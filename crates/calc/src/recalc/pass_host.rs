use super::graph::{HashMap, HashSet, Key};
use super::{Evaluator, Host, Workbook, stack_position};
use gridcraft_core::{Array, CellError, CellRef, RangeRef, Value};
use gridcraft_formula::{BinOp, Expr, SheetSel, UnOp};

/// Formulas a formula may calculate on demand one inside the other (each needing one another's
/// value before it is done). Each level takes stack, so a chain deeper than this is suspended and
/// calculated from the top instead (see [`PassHost::calculate`]): long dependency chains calculate
/// whatever order they come in, with bounded stack.
const MAX_NESTED: usize = 64;

/// Formula evaluations iterative calculation may spend on one recalculation (passes × formulas
/// evaluated again), however high Maximum Iterations is.
const MAX_ITERATION_WORK: usize = 10_000_000;

/// Imported dynamic-array extents, indexed by row so direct cell references can find their
/// anchor without walking every dynamic formula on the sheet.
#[derive(Default)]
struct DeclaredSpillRanges {
    by_row: Vec<(CellRef, RangeRef)>,
    prefix_max_end_row: Vec<u32>,
}

impl DeclaredSpillRanges {
    fn new(mut ranges: Vec<(CellRef, RangeRef)>) -> Self {
        ranges.sort_unstable_by_key(|(_, range)| (range.start.row, range.start.col));
        let mut max_end = 0;
        let prefix_max_end_row = ranges
            .iter()
            .map(|(_, range)| {
                max_end = max_end.max(range.end.row);
                max_end
            })
            .collect();
        Self { by_row: ranges, prefix_max_end_row }
    }

    fn anchor_for(&self, cell: CellRef) -> Option<CellRef> {
        let mut i = self.by_row.partition_point(|(_, range)| range.start.row <= cell.row);
        while i > 0 {
            i -= 1;
            if self.prefix_max_end_row.get(i).is_some_and(|&end| end < cell.row) {
                break;
            }
            let (anchor, range) = self.by_row.get(i)?;
            if *anchor != cell && range.contains(cell) {
                return Some(*anchor);
            }
        }
        None
    }
}

pub(super) struct PassHost<'a> {
    wb: &'a Workbook,
    exprs: &'a HashMap<Key, std::sync::Arc<Expr>>,
    pub(super) results: HashMap<Key, Value>,
    pending: HashSet<Key>,
    in_progress: HashSet<Key>,
    /// New spills found during the pass: anchor → array.
    pub(super) spills: HashMap<Key, std::sync::Arc<Array>>,
    /// Imported dynamic-array ranges for anchors that may still be pending this pass.
    declared_spills: HashMap<usize, DeclaredSpillRanges>,
    /// Used range per sheet: the workbook doesn't change during a pass, and working it out walks
    /// every row, so once per sheet rather than once per range read.
    used: HashMap<usize, Option<RangeRef>>,
    rng: &'a mut u64,
    now: f64,
    cycle: bool,
    pub(super) cycles: Vec<Key>,
    depth: usize,
    /// A formula needed at [`MAX_NESTED`] levels deep: the evaluations in progress are abandoned
    /// and it is calculated first.
    suspend: Option<Key>,
    /// Formulas whose evaluation was abandoned for another one, to be calculated again after it.
    /// They all need it, so reading one of them while it is calculated is a circular reference,
    /// as reading a formula in progress is.
    waiting: HashSet<Key>,
    /// The formulas abandoned since the last suspension.
    abandoned: Vec<Key>,
    /// Other formulas read at [`MAX_NESTED`] levels deep by the evaluations being abandoned. They
    /// are calculated along with the suspended one, rather than one per restart (a wide range
    /// read at the limit would restart the abandoned evaluations once per cell in it).
    also: Vec<Key>,
    /// Suspensions so far (tests check that a wide read at the limit needs one, not one per cell).
    #[cfg(test)]
    pub(super) suspensions: usize,
    /// Spilled values looked at by range reads (tests check that a read outside a large spill
    /// looks at none of it).
    #[cfg(test)]
    pub(super) spill_visits: usize,
    /// The formulas in `cycles`.
    cycle_seen: HashSet<Key>,
    /// Iterative calculation: a circular reference reads the cell's previous value instead of
    /// giving `#CIRC!`.
    pub(super) iterate: bool,
    /// Values from the previous iteration; cells not in it read their stored value.
    prev: HashMap<Key, Value>,
    /// Formulas being evaluated, innermost last (kept only when iterating).
    stack: Vec<Key>,
    /// Formulas found on a circular reference (when iterating).
    pub(super) members: HashSet<Key>,
    /// Results that read a previous value, directly or through other formulas.
    pub(super) tainted: HashSet<Key>,
    /// Whether the formula being evaluated has read a previous value.
    taint: bool,
    /// `stack_position()` where the outermost formula being calculated started.
    stack_top: usize,
    /// Whether an evaluation ran past the stack budget since the innermost formula started.
    out_of_stack: bool,
    /// The kept results of the Python cells in the pass: a Python cell isn't evaluated, its
    /// result is laid out (an array spills from the cell, as a formula's does). Each one is in
    /// `pending` until it is laid out, so a formula that reads it first gets its new value.
    python: HashMap<Key, Value>,
    /// Preserve imported caches for formulas whose results depend on source-only behavior, such as
    /// external cube connections or the producer's exact `FORMULATEXT` spelling.
    preserve_imported_formula_cache: bool,
}

impl<'a> PassHost<'a> {
    pub(super) fn new(wb: &'a Workbook, exprs: &'a HashMap<Key, std::sync::Arc<Expr>>, rng: &'a mut u64, now: f64) -> Self {
        let mut declared: HashMap<usize, Vec<(CellRef, RangeRef)>> = HashMap::default();
        for (sheet, sh) in wb.sheets.iter().enumerate() {
            for (anchor, cell) in sh.cells.iter() {
                if let Some(formula) = cell.formula.as_ref()
                    && formula.dynamic
                    && let Some(range) = formula.dynamic_array_range
                    && range.start == anchor
                {
                    declared.entry(sheet).or_default().push((anchor, range));
                }
            }
        }
        let declared_spills = declared.into_iter().map(|(sheet, ranges)| (sheet, DeclaredSpillRanges::new(ranges))).collect();
        PassHost {
            wb,
            exprs,
            results: HashMap::with_capacity_and_hasher(exprs.len(), Default::default()),
            pending: exprs.keys().copied().collect(),
            in_progress: HashSet::default(),
            spills: HashMap::default(),
            declared_spills,
            used: HashMap::default(),
            rng,
            now,
            cycle: false,
            cycles: vec![],
            depth: 0,
            suspend: None,
            waiting: HashSet::default(),
            abandoned: Vec::new(),
            also: Vec::new(),
            #[cfg(test)]
            suspensions: 0,
            #[cfg(test)]
            spill_visits: 0,
            cycle_seen: HashSet::default(),
            iterate: false,
            prev: HashMap::default(),
            stack: Vec::new(),
            members: HashSet::default(),
            tainted: HashSet::default(),
            taint: false,
            stack_top: 0,
            out_of_stack: false,
            python: HashMap::default(),
            preserve_imported_formula_cache: false,
        }
    }

    pub(super) fn with_imported_formula_cache(mut self, preserve: bool) -> Self {
        self.preserve_imported_formula_cache = preserve;
        self
    }

    /// Adds the dirty Python cells of the pass and their kept results: like the formulas, they
    /// are pending until laid out, so every read path calculates them before reading them.
    pub(super) fn with_python(mut self, python: HashMap<Key, Value>) -> Self {
        self.pending.extend(python.keys().copied());
        self.python = python;
        self
    }
}

/// Whether an array result at `k` can't spill: it is in a table, or its area runs off the sheet,
/// overlaps merged cells, holds other cells, or another formula's spill (unless that formula is
/// recalculated in this pass, and so may spill elsewhere now).
fn spill_blocked(host: &PassHost<'_>, (sheet, anchor): Key, a: &Array) -> bool {
    let Some(sh) = host.wb.sheet(sheet) else { return false };
    let end =
        CellRef::new(anchor.row.saturating_add((a.rows as u32).saturating_sub(1)), anchor.col.saturating_add((a.cols as u32).saturating_sub(1)));
    let range = RangeRef::new(anchor, end);
    let own = sh.spill_ranges.get(&anchor);
    let spilled_over = |c: CellRef| {
        !own.is_some_and(|o| o.contains(c))
            && sh.spill_ranges.iter().any(|(o, r)| {
                // A formula or Python cell recalculated in this pass lays its array out again.
                *o != anchor && r.contains(c) && !host.exprs.contains_key(&(sheet, *o)) && !host.python.contains_key(&(sheet, *o))
            })
    };
    end.row >= gridcraft_core::MAX_ROWS
        || end.col >= gridcraft_core::MAX_COLS
        || sh.merges.iter().any(|m| m.intersects(&range))
        || sh.tables.iter().any(|t| t.range.contains(anchor))
        || sh.cells.iter_range(range).any(|(c, cell)| c != anchor && (!cell.value.is_empty() || cell.formula.is_some()))
        || sh.spill.range(range.start..=range.end).any(|(c, _)| range.contains(*c) && spilled_over(*c))
}

/// Whether `arr`, anchored at `anchor`, would spill exactly what the sheet already holds over
/// `range`: the same area, nothing new in the way, and the same values.
pub(super) fn spills_as_before(sheet: &gridcraft_model::Sheet, anchor: CellRef, range: RangeRef, arr: &Array) -> bool {
    let end =
        CellRef::new(anchor.row.saturating_add((arr.rows as u32).saturating_sub(1)), anchor.col.saturating_add((arr.cols as u32).saturating_sub(1)));
    RangeRef::new(anchor, end) == range
        && !sheet.merges.iter().any(|m| m.intersects(&range))
        && !sheet.tables.iter().any(|t| t.range.contains(anchor))
        && range
            .iter()
            .enumerate()
            .all(|(i, c)| c == anchor || (!sheet.cells.has(c) && sheet.spill.get(&c) == Some(arr.data.get(i).unwrap_or(&Value::Empty))))
}

/// The area an array anchored at `anchor` covers.
fn array_area(anchor: CellRef, a: &Array) -> RangeRef {
    let end =
        CellRef::new(anchor.row.saturating_add((a.rows as u32).saturating_sub(1)), anchor.col.saturating_add((a.cols as u32).saturating_sub(1)));
    RangeRef::new(anchor, end)
}

/// The spilled values `sheet` stores inside `range`, passed to `f` until it returns false. Values
/// outside the range are not walked: with fewer rows in the range than spilled values, each row
/// is looked up on its own; otherwise one ordered scan visits each spilled value at most once.
/// Returns how many values were looked at.
fn stored_spill_in<'s>(sheet: &'s gridcraft_model::Sheet, range: RangeRef, f: &mut dyn FnMut(CellRef, &'s Value) -> bool) -> usize {
    let mut seen = 0usize;
    if sheet.spill.is_empty() {
        return 0;
    }
    if (range.height() as usize) < sheet.spill.len() {
        for row in range.start.row..=range.end.row {
            for (c, v) in sheet.spill.range(CellRef::new(row, range.start.col)..=CellRef::new(row, range.end.col)) {
                seen += 1;
                if !f(*c, v) {
                    return seen;
                }
            }
        }
    } else {
        for (c, v) in sheet.spill.range(range.start..=range.end) {
            seen += 1;
            if range.contains(*c) && !f(*c, v) {
                return seen;
            }
        }
    }
    seen
}

impl PassHost<'_> {
    /// Evaluates one formula whose dirty precedents have already been visited in topological
    /// order. This avoids allocating the nested-work stack for every cell in a long, acyclic pass.
    pub(super) fn calculate_ready(&mut self, k: Key) {
        self.compute(k);
    }

    /// Calculates `k` (and the formulas it reads) with bounded stack: when [`Self::compute`] would
    /// go deeper than [`MAX_NESTED`], it suspends what is in progress, the formula it needed is
    /// calculated from here, then the suspended ones again (reading the results kept so far).
    pub(super) fn calculate(&mut self, k: Key) {
        // Formulas to calculate, innermost last, each with the ones abandoned to calculate the
        // next.
        let mut work: Vec<(Key, Vec<Key>)> = vec![(k, Vec::new())];
        while let Some(&(top, _)) = work.last() {
            self.compute(top);
            match self.suspend.take() {
                Some(next) => {
                    #[cfg(test)]
                    {
                        self.suspensions += 1;
                    }
                    let held = std::mem::take(&mut self.abandoned);
                    self.waiting.extend(held.iter().copied());
                    if let Some(entry) = work.last_mut() {
                        entry.1 = held;
                    }
                    // The other formulas read at the limit are calculated after `next`, before the
                    // held evaluations restart. Each has nothing held of its own, so the held ones
                    // are released only when the last of them is done.
                    let mut seen: HashSet<Key> = HashSet::default();
                    seen.insert(next);
                    for s in std::mem::take(&mut self.also) {
                        if seen.insert(s) {
                            work.push((s, Vec::new()));
                        }
                    }
                    work.push((next, Vec::new()));
                }
                None => {
                    work.pop();
                    if let Some(entry) = work.last_mut() {
                        for a in entry.1.drain(..) {
                            self.waiting.remove(&a);
                        }
                    }
                }
            }
        }
    }

    fn compute(&mut self, k: Key) -> Value {
        if let Some(v) = self.results.get(&k) {
            let v = v.clone();
            if self.iterate && self.tainted.contains(&k) {
                self.taint = true;
            }
            return v;
        }
        if let Some(result) = self.python.get(&k).cloned() {
            return self.python_result(k, result);
        }
        let Some(expr) = self.exprs.get(&k) else {
            return self.wb.sheet(k.0).map(|s| s.value(k.1)).unwrap_or_default();
        };
        if self.preserve_imported_formula_cache
            && let Expr::Call(name, _) = expr.as_ref()
            && is_cube_function(name)
            && let Some(cell) = self.wb.sheet(k.0).and_then(|s| s.cell(k.1))
            && cell.formula.as_ref().is_some_and(|formula| formula.legacy)
            && !matches!(&cell.value, Value::Empty)
        {
            let value = cell.value.clone();
            self.pending.remove(&k);
            self.results.insert(k, value.clone());
            return value;
        }
        if self.preserve_imported_formula_cache
            && formula_uses_text(expr)
            && let Some(cell) = self.wb.sheet(k.0).and_then(|s| s.cell(k.1))
            && !matches!(&cell.value, Value::Empty)
        {
            let value = cell.value.clone();
            self.pending.remove(&k);
            self.results.insert(k, value.clone());
            return value;
        }
        let legacy_formula = self.wb.sheet(k.0).and_then(|s| s.cell(k.1)).and_then(|c| c.formula.as_ref()).is_some_and(|f| f.legacy);
        if !legacy_formula && let Some(value) = self.simple_numeric_add(k, expr) {
            self.pending.remove(&k);
            self.results.insert(k, value.clone());
            return value;
        }
        if self.suspend.is_some() {
            // Unwinding to `calculate`: the value is thrown away. A formula read at the limit is
            // calculated with the suspended one, so the evaluations are not restarted for each.
            if self.depth >= MAX_NESTED && !self.in_progress.contains(&k) && !self.waiting.contains(&k) {
                self.also.push(k);
            }
            return Value::Error(CellError::Calc);
        }
        if self.in_progress.contains(&k) || self.waiting.contains(&k) {
            self.cycle = true;
            if self.iterate {
                return self.circular_read(k);
            }
            // Once each, though a suspended evaluation meets it again.
            if self.cycle_seen.insert(k) {
                self.cycles.push(k);
            }
            return Value::Error(CellError::Circ);
        }
        if self.depth >= MAX_NESTED {
            self.suspend = Some(k);
            return Value::Error(CellError::Calc);
        }
        if self.depth == 0 {
            self.stack_top = stack_position();
        }
        self.in_progress.insert(k);
        self.depth += 1;
        let outer_taint = std::mem::replace(&mut self.taint, false);
        if self.iterate {
            self.stack.push(k);
        }
        let expr = if legacy_formula { std::sync::Arc::new(legacy_intersection(expr, false)) } else { std::sync::Arc::clone(expr) };
        let outer_out_of_stack = std::mem::replace(&mut self.out_of_stack, false);
        let v = {
            let mut ev = Evaluator::new(self, k.0, k.1);
            ev.value(&expr)
        };
        let out_of_stack = std::mem::replace(&mut self.out_of_stack, outer_out_of_stack);
        if out_of_stack && self.depth > 1 && self.suspend.is_none() {
            // It ran out of the stack left below the formulas that read it: it is calculated
            // from the top instead, as a formula needed at `MAX_NESTED` levels deep is.
            self.suspend = Some(k);
            self.depth -= 1;
            self.in_progress.remove(&k);
            if self.iterate {
                self.stack.pop();
            }
            self.taint = outer_taint;
            return Value::Error(CellError::Calc);
        }
        if self.suspend.is_some() {
            // Abandoned: `calculate` evaluates this formula again once the one it needs is done.
            self.depth -= 1;
            self.in_progress.remove(&k);
            self.abandoned.push(k);
            if self.iterate {
                self.stack.pop();
            }
            self.taint = outer_taint;
            return Value::Error(CellError::Calc);
        }
        let unavailable_reference = matches!(&v, Value::Error(CellError::Ref));
        let unavailable_name = matches!(&v, Value::Error(CellError::Name)) && formula_uses_unresolved_name(self.wb, k.0, &expr);
        let cached_future_function_error = self.wb.sheet(k.0).and_then(|s| s.cell(k.1)).is_some_and(|cell| {
            matches!(&cell.value, Value::Error(CellError::Name))
                && cell
                    .formula
                    .as_ref()
                    .and_then(|formula| formula.source_text.as_deref())
                    .is_some_and(|source| source.to_ascii_lowercase().contains("_xlfn."))
        });
        let v = if self.preserve_imported_formula_cache
            && ((legacy_formula && (unavailable_reference || unavailable_name)) || cached_future_function_error)
            && let Some(cell) = self.wb.sheet(k.0).and_then(|s| s.cell(k.1))
            && !matches!(&cell.value, Value::Empty)
        {
            // A workbook can retain a cached result after a linked sheet, workbook or defined
            // name becomes unavailable. A future-function prefix with cached #NAME? also records
            // that the producer could not evaluate this formula. Keep either cache on initial
            // load; later recalculation uses the evaluator normally.
            cell.value.clone()
        } else {
            v
        };
        // A legacy array formula fills the range it was entered in.
        let legacy = self.wb.sheet(k.0).and_then(|s| s.cell(k.1)).and_then(|c| c.formula.as_ref()).and_then(|f| f.array);
        let v = match legacy {
            Some(range) => fit_to_range(v, range),
            None => v,
        };
        self.depth -= 1;
        self.in_progress.remove(&k);
        self.pending.remove(&k);
        if self.iterate {
            self.stack.pop();
            if self.taint {
                self.tainted.insert(k);
            } else {
                self.tainted.remove(&k);
            }
        }
        self.taint |= outer_taint;
        // A blank cell shows as 0 in a formula's result, inside an array as well (`=A1:A3`,
        // FILTER or SORT of a range with blanks). GROUPBY and PIVOTBY lay out blank cells
        // of their own, which stay blank.
        let keep_blanks = matches!(&*expr, Expr::Call(n, _) if matches!(n.as_str(), "GROUPBY" | "PIVOTBY"));
        let v = match v {
            Value::Array(a) => {
                let a = if keep_blanks || !a.data.iter().any(|x| matches!(x, Value::Empty)) {
                    a
                } else {
                    let data = a.data.iter().map(|x| if matches!(x, Value::Empty) { Value::Number(0.0) } else { x.clone() }).collect();
                    Array::new(a.rows, a.cols, data).map(std::sync::Arc::new).unwrap_or(a)
                };
                // A dynamic-array formula anchors a spill range even while its result is one
                // value -- a FILTER matching one row, a SORT or UNIQUE over one item -- so `C1#`
                // is the 1 x 1 range and `ROWS(C1#)` is 1, as in Excel (#1491). A formula that
                // returns a scalar never reaches this arm, so it does not become an anchor.
                self.spills.insert(k, a.clone());
                a.data.first().cloned().unwrap_or_default()
            }
            Value::Empty => Value::Number(0.0),
            v => v,
        };
        // An array that can't spill is #SPILL! for the formulas evaluated after it in this pass too.
        let v = match self.spills.get(&k) {
            Some(a) if spill_blocked(self, k, a) => {
                self.spills.remove(&k);
                Value::Error(CellError::Spill)
            }
            _ => v,
        };
        self.results.insert(k, v.clone());
        v
    }

    /// Fast path for the scalar chain/fan-out shape `=A1+1`. It is deliberately narrow: both
    /// operands must be a same-sheet single-cell reference and a numeric literal, and the
    /// precedent must already be available. Every other formula uses the full evaluator.
    fn simple_numeric_add(&self, k: Key, expr: &Expr) -> Option<Value> {
        let Expr::Binary(BinOp::Add, left, right) = expr else { return None };
        let (Expr::Ref(reference), Expr::Number(addend)) = (left.as_ref(), right.as_ref()) else { return None };
        if reference.sheet != SheetSel::Current || !reference.range().is_single() {
            return None;
        }
        let precedent = (k.0, reference.range().start);
        if self.pending.contains(&precedent) {
            return None;
        }
        let value = self.results.get(&precedent).cloned().or_else(|| self.wb.sheet(precedent.0).map(|s| s.value(precedent.1)))?;
        let Value::Number(number) = value else { return None };
        Some(Value::number(number + addend))
    }

    /// A Python cell's kept result as its value: an array spills from the cell unless it is
    /// blocked, malformed or larger than [`gridcraft_model::python::MAX_RESULT_CELLS`] (only a
    /// crafted file holds one), which shows `#SPILL!`.
    fn python_result(&mut self, k: Key, result: Value) -> Value {
        self.pending.remove(&k);
        let v = match result {
            Value::Array(a) => {
                let sane = a.rows >= 1
                    && a.cols >= 1
                    && a.rows.checked_mul(a.cols).is_some_and(|n| n == a.data.len() && n <= gridcraft_model::python::MAX_RESULT_CELLS);
                if sane {
                    self.spills.insert(k, a.clone());
                    a.data.first().cloned().unwrap_or_default()
                } else {
                    Value::Error(CellError::Spill)
                }
            }
            v => v,
        };
        let v = match self.spills.get(&k) {
            Some(a) if spill_blocked(self, k, a) => {
                self.spills.remove(&k);
                Value::Error(CellError::Spill)
            }
            _ => v,
        };
        self.results.insert(k, v.clone());
        v
    }

    /// A formula's previous value for iterative calculation: from the last iteration, else the
    /// value it shows. Blank, and the `#CIRC!` of a loop calculated with iteration off, are 0.
    fn previous(&self, k: Key) -> Value {
        let v = match self.prev.get(&k) {
            Some(v) => v.clone(),
            None => self.wb.sheet(k.0).map(|s| s.value(k.1)).unwrap_or_default(),
        };
        if matches!(v, Value::Empty | Value::Error(CellError::Circ)) { Value::Number(0.0) } else { v }
    }

    /// Reading `k` while it is being evaluated, with iterative calculation on: its previous value.
    /// The formulas around the loop are the ones whose changes decide when iteration stops.
    fn circular_read(&mut self, k: Key) -> Value {
        self.taint = true;
        match self.stack.iter().rposition(|s| *s == k) {
            Some(i) => self.members.extend(self.stack.get(i..).unwrap_or_default().iter().copied()),
            // Too deep to follow: the formula itself is watched.
            None => {
                self.members.insert(k);
            }
        }
        self.previous(k)
    }

    /// Iterative calculation, after a first pass over `order` that met circular references. The
    /// formulas that read a previous value (the loops and what depends on them) are evaluated
    /// again in the same order, each pass starting from the last one's values and reading what it
    /// has already produced (Gauss-Seidel), until no formula on a loop changes by `max_change` or
    /// more, or after `max_iterations` passes in all. Returns the number of passes.
    pub(super) fn iterate_loops(&mut self, order: &[Key], max_iterations: u32, max_change: f64) -> u32 {
        let again: Vec<Key> = order.iter().copied().filter(|k| self.tainted.contains(k)).collect();
        let set: HashSet<Key> = again.iter().copied().collect();
        // Bounds the work whatever Maximum Iterations says.
        let max_passes = u32::try_from(MAX_ITERATION_WORK / again.len().max(1)).unwrap_or(u32::MAX).max(1);
        let mut passes = 1u32;
        while passes < max_iterations.min(max_passes) && !self.converged(max_change) {
            self.prev = again.iter().filter_map(|k| self.results.remove(k).map(|v| (*k, v))).collect();
            self.pending = set.clone();
            self.spills.retain(|a, _| !set.contains(a));
            for k in &again {
                self.calculate(*k);
            }
            passes += 1;
        }
        passes
    }

    /// Whether every formula on a loop changed by less than `max_change` in the last pass (text,
    /// logical and error values: not at all).
    fn converged(&self, max_change: f64) -> bool {
        self.members.iter().all(|k| {
            let Some(new) = self.results.get(k) else { return true };
            match (new, &self.previous(*k)) {
                (Value::Number(a), Value::Number(b)) => {
                    let d = (a - b).abs();
                    d < max_change || d == 0.0
                }
                (new, old) => new == old,
            }
        })
    }
}

fn is_cube_function(name: &str) -> bool {
    matches!(name, "CUBEKPIMEMBER" | "CUBEMEMBER" | "CUBEMEMBERPROPERTY" | "CUBERANKEDMEMBER" | "CUBESET" | "CUBESETCOUNT" | "CUBEVALUE")
}

fn formula_uses_text(expr: &Expr) -> bool {
    let mut found = false;
    expr.walk(&mut |node| {
        if let Expr::Call(name, _) = node {
            found |= name.eq_ignore_ascii_case("FORMULATEXT");
        }
    });
    found
}

fn formula_uses_unresolved_name(wb: &Workbook, sheet: usize, expr: &Expr) -> bool {
    let mut bound = HashSet::default();
    expr.walk(&mut |node| {
        if let Expr::Call(name, args) = node {
            let params = match name.as_str() {
                "LET" => args.len().saturating_sub(1),
                "LAMBDA" => args.len().saturating_sub(1),
                _ => 0,
            };
            for i in (0..params).step_by(if name == "LET" { 2 } else { 1 }) {
                if let Some(Expr::Name(variable)) = args.get(i) {
                    bound.insert(gridcraft_formula::fold_name(variable));
                }
            }
        }
    });

    let mut unresolved = false;
    expr.walk(&mut |node| {
        if let Expr::Name(name) = node {
            let defined = wb.name(name, sheet);
            let is_external = defined.is_some_and(|d| d.formula.trim_start().strip_prefix('=').unwrap_or(&d.formula).trim_start().starts_with('['));
            let is_unknown = if defined.is_some() { is_external } else { gridcraft_functions::lookup(&name.to_ascii_uppercase()).is_none() };
            if !bound.contains(&gridcraft_formula::fold_name(name)) && is_unknown {
                unresolved = true;
            }
        }
    });
    unresolved
}

/// Rewrites array-shaped references in scalar positions to Excel's pre-dynamic-array implicit
/// intersection. References passed to functions that consume ranges keep their array shape.
pub(super) fn legacy_intersection(expr: &Expr, array_context: bool) -> Expr {
    match expr {
        Expr::Ref(r) if !array_context && !r.range().is_single() => Expr::Unary(UnOp::At, Box::new(expr.clone())),
        // A defined name can resolve to an array constant or a multi-cell reference. Older
        // workbooks used the name in a scalar formula and implicitly selected its intersection,
        // just as they did for a reference written directly in the formula.
        Expr::Name(_) if !array_context => Expr::Unary(UnOp::At, Box::new(expr.clone())),
        Expr::Unary(UnOp::Spill, _) if !array_context => Expr::Unary(UnOp::At, Box::new(expr.clone())),
        Expr::Array(rows) => Expr::Array(rows.iter().map(|row| row.iter().map(|e| legacy_intersection(e, array_context)).collect()).collect()),
        Expr::Unary(op, x) => Expr::Unary(*op, Box::new(legacy_intersection(x, array_context))),
        Expr::Binary(op @ (BinOp::Range | BinOp::Union | BinOp::Intersect), a, b) => {
            Expr::Binary(*op, Box::new(legacy_intersection(a, true)), Box::new(legacy_intersection(b, true)))
        }
        Expr::Binary(op, a, b) => Expr::Binary(*op, Box::new(legacy_intersection(a, array_context)), Box::new(legacy_intersection(b, array_context))),
        // These can return a reference or an array even from a scalar cell. Excel's implicit
        // intersection applies to that result (INDEX/OFFSET/INDIRECT) or selects its first row or
        // column number (ROW/COLUMN), so intersect the call result after keeping its input ranges.
        Expr::Call(name, args)
            if !array_context && matches!(name.as_str(), "ROW" | "COLUMN" | "INDEX" | "OFFSET" | "INDIRECT" | "TRANSPOSE" | "T") =>
        {
            let call = Expr::Call(name.clone(), args.iter().enumerate().map(|(i, a)| legacy_intersection(a, legacy_array_arg(name, i))).collect());
            Expr::Unary(UnOp::At, Box::new(call))
        }
        Expr::Call(name, args) if !array_context && legacy_returns_array(name) => {
            let call = Expr::Call(name.clone(), args.iter().enumerate().map(|(i, a)| legacy_intersection(a, legacy_array_arg(name, i))).collect());
            Expr::Unary(UnOp::At, Box::new(call))
        }
        Expr::Call(name, args) => Expr::Call(
            name.clone(),
            args.iter()
                .enumerate()
                .map(|(i, a)| {
                    let consumes_range = legacy_array_arg(name, i);
                    let returns_reference_or_array = matches!(a, Expr::Name(_))
                        || matches!(
                            a,
                            Expr::Call(result, _)
                                if matches!(result.as_str(), "ROW" | "COLUMN" | "INDEX" | "OFFSET" | "INDIRECT" | "TRANSPOSE" | "T")
                                    || legacy_returns_array(result)
                        )
                        || matches!(a, Expr::Unary(UnOp::Spill, _));
                    let nested_array_context =
                        array_context || (name == "SUMPRODUCT" && consumes_range) || (consumes_range && returns_reference_or_array);
                    // Keep a range argument for the consuming function without making every
                    // nested expression an array formula. SUMPRODUCT evaluates expressions
                    // element by element, so its array context continues through its arguments.
                    if consumes_range && matches!(a, Expr::Ref(_)) { a.clone() } else { legacy_intersection(a, nested_array_context) }
                })
                .collect(),
        ),
        Expr::Invoke(c, args) => Expr::Invoke(Box::new(legacy_intersection(c, false)), args.iter().map(|a| legacy_intersection(a, false)).collect()),
        Expr::Paren(x) => Expr::Paren(Box::new(legacy_intersection(x, array_context))),
        _ => expr.clone(),
    }
}

fn legacy_returns_array(name: &str) -> bool {
    matches!(
        name,
        "CHOOSECOLS"
            | "CHOOSEROWS"
            | "DROP"
            | "EXPAND"
            | "FILTER"
            | "GROUPBY"
            | "HSTACK"
            | "MAKEARRAY"
            | "MAP"
            | "PIVOTBY"
            | "RANDARRAY"
            | "SCAN"
            | "SEQUENCE"
            | "SORT"
            | "SORTBY"
            | "TAKE"
            | "TEXTSPLIT"
            | "TOCOL"
            | "TOROW"
            | "TRANSPOSE"
            | "UNIQUE"
            | "VSTACK"
            | "WRAPCOLS"
            | "WRAPROWS"
    )
}

fn legacy_array_arg(name: &str, index: usize) -> bool {
    matches!(
        name,
        "SUM"
            | "AVERAGE"
            | "AVERAGEA"
            | "MIN"
            | "MINA"
            | "MAX"
            | "MAXA"
            | "COUNT"
            | "COUNTA"
            | "COUNTBLANK"
            | "PRODUCT"
            | "SUMSQ"
            | "MEDIAN"
            | "MODE"
            | "MODE.SNGL"
            | "MODE.MULT"
            | "STDEV"
            | "STDEV.S"
            | "STDEV.P"
            | "STDEVP"
            | "STDEVA"
            | "STDEVPA"
            | "VAR"
            | "VAR.S"
            | "VAR.P"
            | "VARP"
            | "VARA"
            | "VARPA"
            | "AVEDEV"
            | "DEVSQ"
            | "GEOMEAN"
            | "HARMEAN"
            | "KURT"
            | "SKEW"
            | "SKEW.P"
            | "AND"
            | "OR"
            | "XOR"
            | "SUMPRODUCT"
            | "SUMX2MY2"
            | "SUMX2PY2"
            | "SUMXMY2"
            | "CORREL"
            | "COVAR"
            | "COVARIANCE.P"
            | "COVARIANCE.S"
            | "PEARSON"
            | "RSQ"
            | "SLOPE"
            | "INTERCEPT"
            | "STEYX"
            | "ROWS"
            | "COLUMNS"
            | "AREAS"
            | "ROW"
            | "COLUMN"
            | "TRANSPOSE"
            | "ISREF"
            | "TYPE"
            | "MMULT"
            | "MINVERSE"
            | "MDETERM"
            | "FREQUENCY"
            | "FILTER"
            | "SORT"
            | "SORTBY"
            | "UNIQUE"
            | "SEQUENCE"
            | "RANDARRAY"
            | "VSTACK"
            | "HSTACK"
            | "TOROW"
            | "TOCOL"
            | "WRAPROWS"
            | "WRAPCOLS"
            | "TAKE"
            | "DROP"
            | "CHOOSEROWS"
            | "CHOOSECOLS"
            | "EXPAND"
            | "GROUPBY"
            | "PIVOTBY"
            | "T"
    ) || match name {
        "INDEX" => index == 0,
        // These functions consume references rather than scalar values. Keep the reference node
        // intact so they can inspect its area and, for CELL/FORMULATEXT, its identity.
        "CELL" => index == 1,
        "FORMULATEXT" | "ISFORMULA" => index == 0,
        "OFFSET" | "SHEET" | "SHEETS" => index == 0,
        "SUBTOTAL" => index > 0,
        "AGGREGATE" => index > 1,
        "WORKDAY" | "NETWORKDAYS" => index == 2,
        "WORKDAY.INTL" | "NETWORKDAYS.INTL" => index == 3,
        "PROB" => index < 2,
        "IRR" | "MIRR" => index == 0,
        "NPV" => index > 0,
        "XIRR" => index < 2,
        "XNPV" => index == 1 || index == 2,
        "F.TEST" | "CHISQ.TEST" | "T.TEST" => index < 2,
        "Z.TEST" | "PERCENTILE" | "PERCENTILE.INC" | "PERCENTILE.EXC" | "PERCENTRANK" | "PERCENTRANK.INC" | "PERCENTRANK.EXC" | "QUARTILE"
        | "QUARTILE.INC" | "QUARTILE.EXC" | "LARGE" | "SMALL" | "TRIMMEAN" => index == 0,
        "RANK" | "RANK.AVG" | "RANK.EQ" => index == 1,
        "FORECAST" | "FORECAST.LINEAR" => index == 1 || index == 2,
        "FORECAST.ETS" | "FORECAST.ETS.CONFINT" => index == 1 || index == 2,
        "FORECAST.ETS.SEASONALITY" | "FORECAST.ETS.STAT" => index == 0 || index == 1,
        "DCOUNT" | "DCOUNTA" | "DAVERAGE" | "DGET" | "DMAX" | "DMIN" | "DPRODUCT" | "DSTDEV" | "DSTDEVP" | "DSUM" | "DVAR" | "DVARP" => {
            index == 0 || index == 2
        }
        "SUMIF" | "AVERAGEIF" => index == 0 || index == 2,
        "COUNTIF" => index == 0,
        "SUMIFS" | "AVERAGEIFS" | "MINIFS" | "MAXIFS" => index == 0 || index % 2 == 1,
        "COUNTIFS" => index.is_multiple_of(2),
        "VLOOKUP" | "HLOOKUP" => index == 1,
        "MATCH" | "XMATCH" => index == 1,
        "LOOKUP" => index > 0,
        "XLOOKUP" => index == 1 || index == 2,
        _ => false,
    }
}

/// A legacy (Ctrl+Shift+Enter) array formula's result fitted to the range it was entered in, as
/// Excel does: a single row or column repeats across the range, a single value fills it, cells
/// past the result show `#N/A`, and a result larger than the range is cut off.
fn fit_to_range(v: Value, range: RangeRef) -> Value {
    if range.count() > crate::eval::MAX_CELLS {
        return Value::Error(CellError::Num);
    }
    let (h, w) = (range.height() as usize, range.width() as usize);
    let Value::Array(a) = v else {
        return if h * w == 1 { v } else { Array::new(h, w, vec![v; h * w]).map(Value::from).unwrap_or(Value::Error(CellError::Value)) };
    };
    if h * w == 1 {
        return a.data.first().cloned().unwrap_or_default();
    }
    let mut data = Vec::with_capacity(h * w);
    for r in 0..h {
        for c in 0..w {
            let (r, c) = (if a.rows == 1 { 0 } else { r }, if a.cols == 1 { 0 } else { c });
            data.push(a.get(r, c).cloned().unwrap_or(Value::Error(CellError::NA)));
        }
    }
    Array::new(h, w, data).map(Value::from).unwrap_or(Value::Error(CellError::Value))
}

impl Host for PassHost<'_> {
    fn workbook(&self) -> &Workbook {
        self.wb
    }
    fn stack_top(&self) -> Option<usize> {
        (self.depth > 1).then_some(self.stack_top)
    }
    fn stack_exhausted(&mut self) {
        self.out_of_stack = true;
    }
    fn spill_range(&mut self, sheet: usize, anchor: CellRef) -> Option<RangeRef> {
        let k = (sheet, anchor);
        if !(self.pending.contains(&k) || self.results.contains_key(&k)) {
            return self.wb.sheet(sheet)?.spill_ranges.get(&anchor).copied();
        }
        // Recalculated in this pass: its new array, unless something blocks it (#SPILL!).
        self.compute(k);
        let arr = self.spills.get(&k)?;
        let end = CellRef::new(
            anchor.row.saturating_add((arr.rows as u32).saturating_sub(1)),
            anchor.col.saturating_add((arr.cols as u32).saturating_sub(1)),
        );
        let range = RangeRef::new(anchor, end);
        let sh = self.wb.sheet(sheet)?;
        let blocked = end.row >= gridcraft_core::MAX_ROWS
            || end.col >= gridcraft_core::MAX_COLS
            || sh.cells.iter_range(range).any(|(c, cell)| c != anchor && (cell.formula.is_some() || !cell.value.is_empty()))
            || sh.merges.iter().any(|m| m.intersects(&range));
        (!blocked).then_some(range)
    }
    fn cell_value(&mut self, sheet: usize, c: CellRef) -> Value {
        let k = (sheet, c);
        if self.pending.contains(&k) || self.results.contains_key(&k) {
            return self.compute(k);
        }
        // A cell covered by a spill computed in this pass.
        for (anchor, arr) in &self.spills {
            if anchor.0 == sheet && c.row >= anchor.1.row && c.col >= anchor.1.col {
                let (dr, dc) = ((c.row - anchor.1.row) as usize, (c.col - anchor.1.col) as usize);
                if dr < arr.rows && dc < arr.cols {
                    if self.iterate && self.tainted.contains(anchor) {
                        self.taint = true;
                    }
                    return arr.get(dr, dc).cloned().unwrap_or_default();
                }
            }
        }
        // A cached spill cell may be a direct reference precedent, not a range read. During a
        // full recalculation, imported spill values have been dropped, so calculate the declared
        // anchor; in a later pass its laid-out spill value is already on the sheet.
        let declared_anchor = self.declared_spills.get(&sheet).and_then(|ranges| ranges.anchor_for(c));
        if let Some(anchor) = declared_anchor {
            let k = (sheet, anchor);
            if self.pending.contains(&k) {
                self.compute(k);
                if let Some(arr) = self.spills.get(&k) {
                    let (dr, dc) = ((c.row - anchor.row) as usize, (c.col - anchor.col) as usize);
                    if dr < arr.rows && dc < arr.cols {
                        if self.iterate && self.tainted.contains(&k) {
                            self.taint = true;
                        }
                        return arr.get(dr, dc).cloned().unwrap_or_default();
                    }
                }
            } else if let Some(value) = self.wb.sheet(sheet).and_then(|sh| sh.spill.get(&c)) {
                if self.iterate && self.tainted.contains(&k) {
                    self.taint = true;
                }
                return value.clone();
            }
        }
        self.wb.sheet(sheet).map(|s| s.value(c)).unwrap_or_default()
    }
    fn range_values(&mut self, sheet: usize, range: RangeRef) -> Vec<Value> {
        let (h, w) = (range.height() as usize, range.width() as usize);
        let mut out = vec![Value::Empty; h * w];
        let Some(sh) = self.wb.sheet(sheet) else { return out };
        // Sparse walk: only stored cells; formula and Python cells that are (or were) dirty go
        // through `compute`, constants are copied straight from the store.
        let mut formulas: Vec<(usize, CellRef)> = Vec::new();
        for (c, cell) in sh.cells.iter_range(range) {
            let i = (c.row - range.start.row) as usize * w + (c.col - range.start.col) as usize;
            if cell.formula.is_some() || cell.py.is_some() {
                formulas.push((i, c));
            } else if let Some(slot) = out.get_mut(i) {
                *slot = cell.value.clone();
            }
        }
        let _seen = stored_spill_in(sh, range, &mut |c, v| {
            let i = (c.row - range.start.row) as usize * w + (c.col - range.start.col) as usize;
            if let Some(slot) = out.get_mut(i)
                && slot.is_empty()
            {
                *slot = v.clone();
            }
            true
        });
        #[cfg(test)]
        {
            self.spill_visits += _seen;
        }
        for (i, c) in formulas {
            let v = self.cell_value(sheet, c);
            if let Some(slot) = out.get_mut(i) {
                *slot = v;
            }
        }
        if !self.spills.is_empty() {
            // Only the part of each array inside the range is walked: a large array beside a small
            // read costs nothing.
            let mut new: Vec<(usize, Value)> = Vec::new();
            for (a, arr) in self.spills.iter().filter(|(a, _)| a.0 == sheet) {
                let area = array_area(a.1, arr);
                if !area.intersects(&range) {
                    continue;
                }
                let (r0, r1) = (area.start.row.max(range.start.row), area.end.row.min(range.end.row));
                let (c0, c1) = (area.start.col.max(range.start.col), area.end.col.min(range.end.col));
                for row in r0..=r1 {
                    for col in c0..=c1 {
                        let c = CellRef::new(row, col);
                        if c == a.1 {
                            continue;
                        }
                        let v = arr.get((row - a.1.row) as usize, (col - a.1.col) as usize).cloned().unwrap_or_default();
                        new.push(((row - range.start.row) as usize * w + (col - range.start.col) as usize, v));
                    }
                }
            }
            #[cfg(test)]
            {
                self.spill_visits += new.len();
            }
            // Iterating: an array spilled by a formula that read a previous value.
            if self.iterate
                && self.spills.iter().any(|(a, arr)| {
                    let end = CellRef::new(
                        a.1.row.saturating_add((arr.rows as u32).saturating_sub(1)),
                        a.1.col.saturating_add((arr.cols as u32).saturating_sub(1)),
                    );
                    a.0 == sheet && self.tainted.contains(a) && RangeRef::new(a.1, end).intersects(&range)
                })
            {
                self.taint = true;
            }
            for (i, v) in new {
                if let Some(slot) = out.get_mut(i) {
                    *slot = v;
                }
            }
        }
        out
    }
    fn visit_range(&mut self, sheet: usize, range: RangeRef, f: &mut dyn FnMut(&Value) -> bool) -> bool {
        let wb = self.wb;
        let Some(sh) = wb.sheet(sheet) else { return false };
        // Formula and Python cells first, in row-major order like `range_values`: reading one
        // calculates it (a Python cell lays out its result) and the pass remembers the value, so
        // the walk below gets the same value again without this method holding any.
        for (c, cell) in sh.cells.iter_range(range) {
            if cell.formula.is_some() || cell.py.is_some() {
                let _ = self.cell_value(sheet, c);
            }
        }
        // Spilled values sit between the stored cells (and the formulas just calculated may have
        // produced some): leave such blocks to `range_values`.
        let arrays = self.spills.iter().any(|(a, arr)| a.0 == sheet && array_area(a.1, arr).intersects(&range));
        let mut stored = false;
        let _seen = stored_spill_in(sh, range, &mut |_, _| {
            stored = true;
            false
        });
        #[cfg(test)]
        {
            self.spill_visits += _seen;
        }
        if arrays || stored {
            return false;
        }
        for (c, cell) in sh.cells.iter_range(range) {
            let go = if cell.formula.is_some() || cell.py.is_some() { f(&self.cell_value(sheet, c)) } else { f(&cell.value) };
            if !go {
                break;
            }
        }
        true
    }
    fn used_range(&mut self, sheet: usize) -> Option<RangeRef> {
        let wb = self.wb;
        *self.used.entry(sheet).or_insert_with(|| wb.sheet(sheet).and_then(|s| s.used_range()))
    }
    fn now_serial(&self) -> f64 {
        self.now
    }
    fn random(&mut self) -> f64 {
        // xorshift64*
        let mut x = *self.rng;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        *self.rng = x;
        (x.wrapping_mul(0x2545_F491_4F6C_DD1D) >> 11) as f64 / (1u64 << 53) as f64
    }
}
