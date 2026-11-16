use super::array::{Acc, Agg, zip2, zip3};
use super::format::same_kind;
use super::special::{ev_shape, resized_sum_range, resizes_sum_range};
use super::{Area, Arg, Array, CellError, Ev, Evaluator, Expr, FnCtx, Lambda, Pipe, Value, compare, err};
use gridcraft_core::{CellRef, letters_to_col};
use gridcraft_formula::{Anchor, RefKind, Reference, SheetSel, UnOp};
use std::sync::Arc;

/// Replaces matching errors in an array with the corresponding fallback value. A scalar fallback
/// repeats; a fallback array broadcasts to the shape of the original value.
fn if_error_array(array: &Array, alternate: Value, catches: impl Fn(CellError) -> bool + Copy) -> Value {
    let data = array
        .data
        .iter()
        .enumerate()
        .map(|(i, item)| {
            if item.as_error().is_some_and(catches) {
                match &alternate {
                    Value::Array(fallback) => fallback.get_broadcast(i / array.cols, i % array.cols),
                    value => value.scalar(),
                }
            } else {
                item.clone()
            }
        })
        .collect();
    Array::new(array.rows, array.cols, data).map(Value::from).unwrap_or(Value::Error(CellError::Value))
}

fn pivot_item_matches(label: &Value, item: &Value) -> bool {
    match (label.scalar(), item.scalar()) {
        (Value::Text(a), Value::Text(b)) => a.eq_ignore_ascii_case(&b),
        (Value::Number(a), Value::Number(b)) => a == b,
        (Value::Bool(a), Value::Bool(b)) => a == b,
        (Value::Empty, Value::Empty) => true,
        _ => false,
    }
}

impl<'h> Evaluator<'h> {
    pub(super) fn call(&mut self, name: &str, args: &[Expr]) -> Ev {
        match name {
            "IF" => self.if_call(args),
            "IFS" => {
                if args.len() < 2 || !args.len().is_multiple_of(2) {
                    return err(CellError::Value);
                }
                for pair in args.chunks(2) {
                    let [c, v] = pair else { break };
                    let cv = self.value(c);
                    match cv.scalar().to_bool() {
                        Ok(true) => return self.eval(v),
                        Ok(false) => {}
                        Err(e) => return err(e),
                    }
                }
                err(CellError::NA)
            }
            "IFERROR" | "IFNA" => self.if_error_call(name, args),
            "CHOOSE" => self.choose_call(args),
            "SWITCH" => self.switch_call(args),
            "ROW" | "COLUMN" => self.row_column_call(name, args),
            "ROWS" | "COLUMNS" => {
                if args.len() != 1 {
                    return err(CellError::Value);
                }
                let is_rows = name == "ROWS";
                match self.eval(&args[0]) {
                    Ev::R(a) => match a.as_slice() {
                        [a] => Ev::V(Value::number(if is_rows { a.range.height() } else { a.range.width() } as f64)),
                        _ => err(CellError::Ref),
                    },
                    Ev::V(Value::Array(arr)) => Ev::V(Value::number(if is_rows { arr.rows } else { arr.cols } as f64)),
                    Ev::V(Value::Error(e)) => err(e),
                    Ev::V(_) => Ev::V(Value::Number(1.0)),
                    Ev::L(_) => err(CellError::Value),
                }
            }
            "AREAS" => match args.first().map(|a| self.eval(a)) {
                Some(Ev::R(a)) => Ev::V(Value::number(a.len() as f64)),
                Some(Ev::V(Value::Error(e))) => err(e),
                _ => err(CellError::Value),
            },
            "ISREF" => Ev::V(Value::Bool(matches!(args.first().map(|a| self.eval(a)), Some(Ev::R(_))))),
            "ISFORMULA" | "FORMULATEXT" => {
                let Some(Ev::R(a)) = args.first().map(|a| self.eval(a)) else { return err(CellError::NA) };
                let Some(a) = a.first() else { return err(CellError::NA) };
                let wb = self.host.workbook();
                let f = wb.sheet(a.sheet).and_then(|s| s.cell(a.range.start)).and_then(|c| c.formula.clone());
                // A formula formatted Hidden on a protected sheet stays hidden from FORMULATEXT too.
                let hidden = wb.sheet(a.sheet).is_some_and(|s| s.is_protected() && wb.styles.get(s.style_id(a.range.start)).protection.hidden);
                if name == "ISFORMULA" {
                    Ev::V(Value::Bool(f.is_some()))
                } else {
                    match f {
                        Some(f) if !hidden => Ev::V(Value::text(formula_text(&f))),
                        _ => err(CellError::NA),
                    }
                }
            }
            "SHEET" | "SHEETS" => self.sheet_call(name, args),
            "OFFSET" => self.offset(args),
            "INDIRECT" => self.indirect(args),
            "INDEX" => self.index(args),
            "XLOOKUP" => self.xlookup(args),
            "CELL" => self.cell_info(args),
            "TRIMRANGE" => self.trimrange(args),
            "SUBTOTAL" | "AGGREGATE" => self.subtotal(name, args),
            "TEXT" => {
                if args.len() != 2 {
                    return err(CellError::Value);
                }
                let v = self.arg_val(args, 0).unwrap_or_default();
                let f = self.arg_val(args, 1).unwrap_or_default();
                let sys = self.host.workbook().date_system;
                let one = |v: &Value, f: &Value| -> Value {
                    if let Value::Error(e) = v {
                        return Value::Error(*e);
                    }
                    let code = match f.to_text() {
                        Ok(c) => c,
                        Err(e) => return Value::Error(e),
                    };
                    match gridcraft_numfmt::text_function(v, &code, sys) {
                        Ok(s) => Value::text(s),
                        Err(e) => Value::Error(e),
                    }
                };
                Ev::V(zip2(&v, &f, one))
            }
            "GETPIVOTDATA" => self.get_pivot_data(args),
            "LET" => self.let_(args),
            "LAMBDA" => {
                if args.is_empty() {
                    return err(CellError::Value);
                }
                let mut params = Vec::new();
                for p in &args[..args.len() - 1] {
                    match p {
                        Expr::Name(n) => params.push(n.trim_start_matches('[').trim_end_matches(']').to_string()),
                        _ => return err(CellError::Value),
                    }
                }
                let Some(body) = args.last() else { return err(CellError::Value) };
                Ev::L(Arc::new(Lambda { params, body: body.clone(), env: self.env.clone() }))
            }
            "ISOMITTED" => {
                let r = matches!(args.first(), Some(Expr::Name(n)) if self.env.iter().rev().find(|(k, _)| gridcraft_formula::same_name(k, n)).is_some_and(|(_, v)| matches!(v, Ev::V(Value::Empty))));
                Ev::V(Value::Bool(r))
            }
            "MAP" | "REDUCE" | "SCAN" | "BYROW" | "BYCOL" | "MAKEARRAY" => self.higher_order(name, args),
            "GROUPBY" | "PIVOTBY" => {
                // The aggregation may be a function given by name (`SUM`): pass it as its name.
                let i = if name == "GROUPBY" { 2 } else { 3 };
                match args.get(i).and_then(|a| self.function_by_name(a)) {
                    Some(f) => {
                        let mut args = args.to_vec();
                        if let Some(a) = args.get_mut(i) {
                            *a = Expr::Text(f.into());
                        }
                        self.builtin(name, &args)
                    }
                    None => self.builtin(name, args),
                }
            }
            "NOW" | "TODAY" | "RAND" | "RANDBETWEEN" | "RANDARRAY" => {
                self.host.note_volatile();
                self.builtin(name, args)
            }
            "RTD" => {
                if !(3..=255).contains(&args.len()) {
                    return err(CellError::Value);
                }
                // GridCraft has no COM automation host. Excel returns #N/A when the requested
                // real-time data server is unavailable; resolve that before topic expressions,
                // which may be names understood only by the server.
                err(CellError::NA)
            }
            _ => self.builtin(name, args),
        }
    }

    fn if_call(&mut self, args: &[Expr]) -> Ev {
        if args.is_empty() || args.len() > 3 {
            return err(CellError::Value);
        }
        let condition = self.arg_val(args, 0).unwrap_or_default();
        if let Value::Array(array) = &condition {
            let when_true = self.arg_val(args, 1).unwrap_or(Value::Bool(true));
            let when_false = if args.len() > 2 { self.arg_val(args, 2).unwrap_or(Value::Bool(false)) } else { Value::Bool(false) };
            return Ev::V(zip3(array, &when_true, &when_false, |condition, when_true, when_false| match condition.to_bool() {
                Ok(true) => when_true.clone(),
                Ok(false) => when_false.clone(),
                Err(error) => Value::Error(error),
            }));
        }
        match condition.to_bool() {
            Ok(true) => match args.get(1) {
                Some(Expr::Missing) => Ev::V(Value::Number(0.0)),
                Some(expression) => self.eval(expression),
                None => Ev::V(Value::Bool(true)),
            },
            Ok(false) => match args.get(2) {
                Some(Expr::Missing) => Ev::V(Value::Number(0.0)),
                Some(expression) => self.eval(expression),
                None => Ev::V(Value::Bool(false)),
            },
            Err(error) => err(error),
        }
    }

    fn if_error_call(&mut self, name: &str, args: &[Expr]) -> Ev {
        if args.len() != 2 {
            return err(CellError::Value);
        }
        let value = self.arg_ev(args, 0).unwrap_or(Ev::V(Value::Empty));
        let na_only = name == "IFNA";
        let catches = |error: CellError| !na_only || error == CellError::NA;
        match &value {
            Ev::V(Value::Error(error)) if catches(*error) => self.eval(&args[1]),
            Ev::V(Value::Array(array)) if array.data.iter().any(|item| item.as_error().is_some_and(catches)) => {
                let alternate = self.arg_val(args, 1).unwrap_or_default();
                Ev::V(if_error_array(array, alternate, catches))
            }
            Ev::R(_) => self.if_error_reference(value.clone(), args, catches),
            _ => value,
        }
    }

    fn if_error_reference(&mut self, value: Ev, args: &[Expr], catches: impl Fn(CellError) -> bool + Copy) -> Ev {
        match self.deref(value.clone()) {
            Value::Error(error) if catches(error) => self.eval(&args[1]),
            Value::Array(ref array) if array.data.iter().any(|item| item.as_error().is_some_and(catches)) => {
                let alternate = self.arg_val(args, 1).unwrap_or_default();
                Ev::V(if_error_array(array, alternate, catches))
            }
            _ => value,
        }
    }

    fn choose_call(&mut self, args: &[Expr]) -> Ev {
        if args.len() < 2 {
            return err(CellError::Value);
        }
        let index = self.value(&args[0]);
        if let Value::Array(_) = index {
            let Some(spec) = gridcraft_functions::lookup("CHOOSE") else { return err(CellError::Name) };
            let mut evaluated = vec![Arg::val(index)];
            for argument in &args[1..] {
                evaluated.push(Arg::val(self.value(argument)));
            }
            let mut context = FnCtx { ev: self, criteria: None, lambda: None };
            return gridcraft_functions::call(spec, &evaluated, &mut context).pipe(Ev::V);
        }
        let index = match index.to_number() {
            Ok(number) => number.trunc() as i64,
            Err(error) => return err(error),
        };
        if index < 1 || index as usize >= args.len() {
            return err(CellError::Value);
        }
        self.eval(&args[index as usize])
    }

    fn switch_call(&mut self, args: &[Expr]) -> Ev {
        if args.len() < 3 {
            return err(CellError::Value);
        }
        let value = self.arg_val(args, 0).unwrap_or_default().scalar();
        if let Value::Error(error) = value {
            return err(error);
        }
        let choices = &args[1..];
        for pair in choices.as_chunks::<2>().0 {
            let (candidate, result) = (&pair[0], &pair[1]);
            let candidate = self.value(candidate).scalar();
            if !candidate.is_error() && compare(&value, &candidate) == std::cmp::Ordering::Equal && same_kind(&value, &candidate) {
                return self.eval(result);
            }
        }
        if let Some(default) = choices.get(choices.len().saturating_sub(1)).filter(|_| choices.len() % 2 == 1) {
            self.eval(default)
        } else {
            err(CellError::NA)
        }
    }

    fn get_pivot_data(&mut self, args: &[Expr]) -> Ev {
        if args.len() < 2 || !(args.len() - 2).is_multiple_of(2) {
            return err(CellError::Value);
        }
        let data_field = match self.value(&args[0]).scalar().to_text() {
            Ok(s) if !s.trim().is_empty() => s,
            Ok(_) => return err(CellError::Ref),
            Err(e) => return err(e),
        };
        let pivot_ref = match self.eval(&args[1]) {
            Ev::R(areas) => match areas.as_slice() {
                [area] => *area,
                _ => return err(CellError::Ref),
            },
            Ev::V(Value::Error(e)) => return err(e),
            _ => return err(CellError::Ref),
        };
        let pivot_cell = pivot_ref.range.start;
        let item = if args.len() > 2 {
            if args.len() > 4 {
                return err(CellError::Ref);
            }
            let field = match self.value(&args[2]).scalar().to_text() {
                Ok(s) => s,
                Err(e) => return err(e),
            };
            Some((field, self.value(&args[3]).scalar()))
        } else {
            None
        };
        let Some(sheet) = self.host.workbook().sheet(pivot_ref.sheet) else { return err(CellError::Ref) };
        let Some(pivot) = sheet.pivots.iter().find(|pt| pt.last_range.is_some_and(|range| range.contains(pivot_cell))) else {
            return err(CellError::Ref);
        };

        // Read the cached report rather than recomputing the pivot. The imported cells already
        // represent its visible result, and this keeps calculation below the engine layer.
        let supported =
            pivot.rows.len() == 1 && pivot.columns.is_empty() && pivot.filters.is_empty() && pivot.values.len() == 1 && !pivot.values_on_rows;
        if !supported || !pivot.values[0].name.eq_ignore_ascii_case(&data_field) {
            return err(CellError::Ref);
        }
        let Some(report) = pivot.last_range else { return err(CellError::Ref) };
        let label_col = pivot.anchor.col;
        let value_col = report.end.col;
        if label_col < report.start.col || label_col > report.end.col || value_col == label_col {
            return err(CellError::Ref);
        }

        if let Some((field, _)) = &item
            && !pivot.rows[0].source_col.eq_ignore_ascii_case(field)
        {
            return err(CellError::Ref);
        }

        for row in report.start.row..=report.end.row {
            let label = sheet.value(CellRef::new(row, label_col)).scalar();
            let matches = match &item {
                Some((_, expected)) => pivot_item_matches(&label, expected),
                None => matches!(&label, Value::Text(text) if text.eq_ignore_ascii_case("Grand Total")),
            };
            if matches {
                return Ev::V(sheet.value(CellRef::new(row, value_col)).scalar());
            }
        }
        err(CellError::Ref)
    }

    fn row_column_call(&mut self, name: &str, args: &[Expr]) -> Ev {
        let is_row = name == "ROW";
        if args.is_empty() || matches!(args.first(), Some(Expr::Missing)) {
            return Ev::V(Value::number(if is_row { self.at.row + 1 } else { self.at.col + 1 } as f64));
        }
        let evaluated = self.eval(&args[0]);
        let areas = match evaluated {
            Ev::R(areas) => areas,
            Ev::V(Value::Error(CellError::Name)) if let Expr::Name(name) = &args[0] => {
                let Some(col) = letters_to_col(name) else { return err(CellError::Name) };
                let reference =
                    Expr::Ref(Reference { sheet: SheetSel::Current, kind: RefKind::Cell(Anchor { row: 0, col, row_abs: false, col_abs: false }) });
                match self.eval(&reference) {
                    Ev::R(areas) => areas,
                    Ev::V(Value::Error(error)) => return err(error),
                    _ => return err(CellError::Ref),
                }
            }
            Ev::V(Value::Error(error)) => return err(error),
            _ => return err(CellError::Value),
        };
        let Some(area) = areas.first() else { return err(CellError::Ref) };
        let range = self.trim_lines(area);
        if is_row {
            let values: Vec<Value> = (range.start.row..=range.end.row).map(|row| Value::number(row as f64 + 1.0)).collect();
            if values.len() == 1 { Ev::V(values.into_iter().next().unwrap_or_default()) } else { Ev::V(Array::column(values).into()) }
        } else {
            let values: Vec<Value> = (range.start.col..=range.end.col).map(|col| Value::number(col as f64 + 1.0)).collect();
            if values.len() == 1 { Ev::V(values.into_iter().next().unwrap_or_default()) } else { Ev::V(Array::row(values).into()) }
        }
    }

    fn sheet_call(&mut self, name: &str, args: &[Expr]) -> Ev {
        let is_sheet = name == "SHEET";
        if args.is_empty() {
            let count = if is_sheet { self.sheet + 1 } else { self.host.workbook().sheets.len() };
            return Ev::V(Value::number(count as f64));
        }
        match self.eval(&args[0]) {
            Ev::R(areas) if is_sheet => areas.first().map_or(err(CellError::Ref), |area| Ev::V(Value::number(area.sheet as f64 + 1.0))),
            Ev::R(areas) => {
                let mut sheets: Vec<usize> = areas.iter().map(|area| area.sheet).collect();
                sheets.dedup();
                Ev::V(Value::number(sheets.len() as f64))
            }
            Ev::V(Value::Text(name)) if is_sheet => {
                self.host.workbook().sheet_index(&name).map_or(err(CellError::NA), |index| Ev::V(Value::number(index as f64 + 1.0)))
            }
            _ => err(CellError::NA),
        }
    }

    pub(super) fn builtin(&mut self, name: &str, args: &[Expr]) -> Ev {
        let Some(spec) = gridcraft_functions::lookup(name) else {
            // A defined name holding a LAMBDA, or a LET-bound lambda.
            return match self.name(name) {
                Ev::L(l) => self.apply_lambda(&l, args),
                Ev::V(Value::Error(x)) => err(x),
                _ => err(CellError::Name),
            };
        };
        if args.len() < spec.min_args || args.len() > spec.max_args {
            return err(CellError::Value);
        }
        if let Some(kind) = Agg::of(spec.name) {
            return self.aggregate(kind, args);
        }
        let mut evaluated = Vec::with_capacity(args.len());
        // SUMIF/AVERAGEIF: the size of the criteria range (argument 1), which the sum range takes.
        let mut criteria_shape = None;
        // Database functions: the criteria range (argument 2), whose formulas are computed criteria.
        let mut criteria = None;
        // GROUPBY/PIVOTBY: the LAMBDA given as their function.
        let mut lambda = None;
        let lambda_at = match name {
            "GROUPBY" => Some(2),
            "PIVOTBY" => Some(3),
            _ => None,
        };
        for (i, a) in args.iter().enumerate() {
            let mut ev = self.eval(a);
            if lambda_at == Some(i)
                && let Ev::L(l) = &ev
            {
                lambda = Some(l.clone());
                ev = Ev::V(Value::Empty);
            }
            if spec.category == gridcraft_functions::Category::Database
                && i == 2
                && let Ev::R(areas) = &ev
                && let [area] = areas.as_slice()
            {
                criteria = Some(*area);
            }
            if resizes_sum_range(name, args.len()) {
                if i == 0 {
                    criteria_shape = ev_shape(&ev);
                } else if i == 2
                    && let (Some((h, w)), Ev::R(areas)) = (criteria_shape, &ev)
                    && let [area] = areas.as_slice()
                {
                    ev = Ev::R(vec![Area { sheet: area.sheet, range: resized_sum_range(area.range, h, w) }]);
                }
            }
            let from_ref = matches!(ev, Ev::R(_));
            let value = match ev {
                Ev::R(areas) if areas.len() > 1 => {
                    // Multi-area references (unions): flatten into one row for aggregates.
                    let mut vals = Vec::new();
                    for ar in &areas {
                        match self.area_value(ar) {
                            Value::Array(a) => vals.extend(a.data.iter().cloned()),
                            v => vals.push(v),
                        }
                    }
                    Value::from(Array::row(vals))
                }
                ev => self.deref(ev),
            };
            // Only an argument left out (`f(a,,b)`) is omitted; one that computes a blank is given.
            let blank_value = !from_ref && value == Value::Empty && lambda_at != Some(i) && !matches!(a, Expr::Missing);
            evaluated.push(Arg { value, from_ref, blank_value });
        }
        // The function may go through every value it is given (a SUM inside each call of a
        // LAMBDA over a large array): the values count against the cell's work.
        let values = evaluated.iter().fold(0u64, |n, a| n.saturating_add(if let Value::Array(x) = &a.value { x.data.len() as u64 } else { 1 }));
        if !self.spend(values) {
            return err(CellError::Calc);
        }
        let database = criteria.is_some();
        let mut ctx = FnCtx { ev: self, criteria, lambda };
        let v = gridcraft_functions::call(spec, &evaluated, &mut ctx);
        // A computed criterion that ran out of work counted as not met: the result leaves
        // records out.
        if database && self.exhausted {
            return err(CellError::Calc);
        }
        Ev::V(v)
    }

    /// Performs aggregation operations without copying its ranges: blocks are folded over the stored
    /// cells, so no array is built and there is no `MAX_CELLS` limit. Arguments are evaluated and read one
    /// after another, as the array path does, so volatile formulas (like `RAND`) see the same order.
    /// Only `SUM`, `COUNT` and `AVG` are supported currently.
    fn aggregate(&mut self, kind: Agg, args: &[Expr]) -> Ev {
        let mut acc = Acc::default();
        let mut first_error = None;
        for a in args {
            let ev = self.eval(a);
            let steps = match ev {
                Ev::R(areas) => areas.iter().map(|area| self.aggregate_area(kind, area, &mut acc)).collect(),
                ev => {
                    let value = self.deref(ev);
                    vec![self.aggregate_value(kind, value, false, &mut acc)]
                }
            };
            if first_error.is_none() {
                first_error = steps.into_iter().find_map(Result::err);
            }
        }
        first_error.unwrap_or_else(|| Ev::V(acc.finish(kind)))
    }

    /// Adds one area to `acc`; `Err` is the result the function ends with.
    fn aggregate_area(&mut self, kind: Agg, a: &Area, acc: &mut Acc) -> Result<(), Ev> {
        if !a.range.is_single() {
            // Adding the block's remembered sum to anything but +0.0 would add in another order.
            // COUNT never reads the sum, so it may reuse every block.
            if (kind == Agg::Count || acc.sum.to_bits() == 0)
                && let Some((sum, count)) = self.host.range_sum(a.sheet, a.range)
            {
                acc.sum = sum;
                acc.count = acc.count.saturating_add(count);
                return Ok(());
            }
            // Folded without building an array, but still walked: the part inside the used
            // range counts against the cell's work.
            let r = self.read_range(a);
            if !self.spend(u64::from(r.height()) * u64::from(r.width())) {
                return Err(err(CellError::Calc));
            }
            let mut error = None;
            let walked = self.host.visit_range(a.sheet, a.range, &mut |v| match acc.add_cell(kind, v) {
                Ok(()) => true,
                Err(e) => {
                    error = Some(e);
                    false
                }
            });
            if walked {
                return error.map_or(Ok(()), |e| Err(err(e)));
            }
        }
        let value = self.area_value(a);
        self.aggregate_value(kind, value, true, acc)
    }

    /// Adds one argument's value by calling `SUM` and `COUNT` on it, so coercion and error rules
    /// stay in one place (`AVERAGE` of an argument is its `SUM` over its `COUNT`).
    fn aggregate_value(&mut self, kind: Agg, value: Value, from_ref: bool, acc: &mut Acc) -> Result<(), Ev> {
        if !from_ref && !self.spend_on(&value) {
            return Err(err(CellError::Calc));
        }
        let (Some(sum), Some(count)) = (gridcraft_functions::lookup("SUM"), gridcraft_functions::lookup("COUNT")) else {
            return Err(err(CellError::Name));
        };
        let args = [Arg { value, from_ref, blank_value: false }];
        if kind != Agg::Count {
            match gridcraft_functions::call(sum, &args, &mut FnCtx { ev: self, criteria: None, lambda: None }) {
                Value::Number(n) => acc.sum += n,
                other => return Err(Ev::V(other)),
            }
        }
        if kind != Agg::Sum {
            match gridcraft_functions::call(count, &args, &mut FnCtx { ev: self, criteria: None, lambda: None }) {
                Value::Number(n) => acc.count = acc.count.saturating_add(n as u64),
                other => return Err(Ev::V(other)),
            }
        }
        Ok(())
    }

    /// A worksheet function given by name where a function is expected (`BYROW(A1:C3,SUM)`,
    /// `GROUPBY(A2:A9,B2:B9,SUM)`): its name, unless a LET/LAMBDA variable or a defined name has
    /// that name.
    pub(super) fn function_by_name(&self, e: &Expr) -> Option<String> {
        let Expr::Name(n) = e else { return None };
        if self.env.iter().any(|(k, _)| gridcraft_formula::same_name(k, n)) || self.host.workbook().name(n, self.sheet).is_some() {
            return None;
        }
        let u = n.to_ascii_uppercase();
        gridcraft_functions::lookup(&u).map(|_| u)
    }
}

fn formula_text(formula: &gridcraft_model::Formula) -> String {
    let source = formula.source_text.as_deref().unwrap_or(&formula.text);
    let display = file_formula_text(source);
    if formula.legacy
        && !contains_xlsx_single(source)
        && let Some(expr) = formula.expr_arc()
    {
        let mut intersected = crate::recalc::formula_text_intersection(&expr);
        if matches!(expr.as_ref(), Expr::Unary(UnOp::Spill, _)) || returns_array(&expr) {
            intersected = Expr::Unary(UnOp::At, Box::new(expr.as_ref().clone()));
        }
        if intersected != *expr {
            return format!("={}", gridcraft_formula::print(&intersected));
        }
    }
    let display = if contains_xlsx_anchorarray(source) { formula_spacing(&display) } else { display };
    format!("={display}")
}

fn returns_array(expr: &Expr) -> bool {
    let Expr::Call(name, _) = expr else { return false };
    matches!(
        name.as_str(),
        "CHOOSECOLS"
            | "CHOOSEROWS"
            | "DROP"
            | "EXPAND"
            | "FILTER"
            | "HSTACK"
            | "RANDARRAY"
            | "SEQUENCE"
            | "SORT"
            | "SORTBY"
            | "TAKE"
            | "TEXTSPLIT"
            | "TOCOL"
            | "TOROW"
            | "UNIQUE"
            | "VSTACK"
            | "WRAPCOLS"
            | "WRAPROWS"
    )
}

fn contains_xlsx_single(source: &str) -> bool {
    source.as_bytes().windows(b"_xlfn.SINGLE".len()).any(|w| w.eq_ignore_ascii_case(b"_xlfn.SINGLE"))
}

fn contains_xlsx_anchorarray(source: &str) -> bool {
    source.as_bytes().windows(b"_xlfn.ANCHORARRAY".len()).any(|w| w.eq_ignore_ascii_case(b"_xlfn.ANCHORARRAY"))
}

/// Converts OOXML-only spellings for spills, implicit intersection, and modern function names
/// while keeping the formula's original whitespace for `FORMULATEXT`.
fn file_formula_text(source: &str) -> String {
    let mut out = String::with_capacity(source.len());
    let mut i = 0;
    while i < source.len() {
        let rest = &source[i..];
        if rest.starts_with('"') {
            let end = quoted_formula_end(source, i);
            out.push_str(&source[i..end]);
            i = end;
            continue;
        }
        if let Some((token, replacement)) =
            [("_xlfn.ANCHORARRAY", "spill"), ("_xlfn.SINGLE", "single")].into_iter().find(|(token, _)| starts_ascii_case_insensitive(rest, token))
        {
            let after = i + token.len();
            let mut open = after;
            while open < source.len() {
                let ch = source[open..].chars().next().unwrap_or(' ');
                if !ch.is_whitespace() {
                    break;
                }
                open += ch.len_utf8();
            }
            if source.as_bytes().get(open) == Some(&b'(')
                && let Some(close) = matching_formula_paren(source, open)
            {
                let inner = file_formula_text(source[open + 1..close].trim());
                if replacement == "spill" {
                    out.push_str(&inner);
                    out.push('#');
                } else {
                    out.push('@');
                    out.push_str(&inner);
                }
                i = close + 1;
                continue;
            }
        }
        if let Some(prefix) = ["_xlfn.", "_xlpm.", "_xlws."].into_iter().find(|prefix| starts_ascii_case_insensitive(rest, prefix)) {
            i += prefix.len();
            continue;
        }
        let ch = rest.chars().next().unwrap_or(' ');
        out.push(ch);
        i += ch.len_utf8();
    }
    out
}

fn starts_ascii_case_insensitive(text: &str, prefix: &str) -> bool {
    text.get(..prefix.len()).is_some_and(|head| head.eq_ignore_ascii_case(prefix))
}

fn matching_formula_paren(text: &str, open: usize) -> Option<usize> {
    let bytes = text.as_bytes();
    let mut depth = 0usize;
    let mut quoted = false;
    let mut i = open;
    while i < bytes.len() {
        match bytes[i] {
            b'"' if quoted && bytes.get(i + 1) == Some(&b'"') => i += 1,
            b'"' => quoted = !quoted,
            b'(' if !quoted => depth += 1,
            b')' if !quoted => {
                depth -= 1;
                if depth == 0 {
                    return Some(i);
                }
            }
            _ => {}
        }
        i += 1;
    }
    None
}

fn quoted_formula_end(text: &str, start: usize) -> usize {
    let bytes = text.as_bytes();
    let mut i = start + 1;
    while i < bytes.len() {
        if bytes[i] == b'"' {
            if bytes.get(i + 1) == Some(&b'"') {
                i += 2;
                continue;
            }
            return i + 1;
        }
        i += 1;
    }
    bytes.len()
}

/// Excel's formula display inserts spaces around operators and after separators when an
/// `_xlfn.ANCHORARRAY` call is rendered as a spill reference. Fill only missing spaces, retaining
/// any spacing already present in the source formula.
fn formula_spacing(text: &str) -> String {
    let bytes = text.as_bytes();
    let mut out = String::with_capacity(text.len() + 16);
    let mut i = 0;
    let mut prev = None;
    while i < bytes.len() {
        if bytes[i] == b'"' {
            let end = quoted_formula_end(text, i);
            out.push_str(&text[i..end]);
            prev = Some(b'"');
            i = end;
            continue;
        }
        let b = bytes[i];
        if b == b',' {
            out.push(',');
            if bytes.get(i + 1).is_some_and(|next| !next.is_ascii_whitespace() && *next != b')') {
                out.push(' ');
            }
            prev = Some(b',');
            i += 1;
            continue;
        }
        let op_len = if matches!(b, b'<' | b'>') && bytes.get(i + 1).is_some_and(|next| matches!(*next, b'=' | b'>')) {
            2
        } else if matches!(b, b'+' | b'-' | b'*' | b'/' | b'^' | b'&' | b'=' | b'<' | b'>') {
            1
        } else {
            0
        };
        if op_len > 0 {
            let unary = matches!(b, b'+' | b'-')
                && prev.is_none_or(|ch| matches!(ch, b'(' | b',' | b'+' | b'-' | b'*' | b'/' | b'^' | b'&' | b'=' | b'<' | b'>'));
            if !unary && !out.ends_with(char::is_whitespace) {
                out.push(' ');
            }
            out.push_str(&text[i..i + op_len]);
            i += op_len;
            if !unary && bytes.get(i).is_some_and(|next| !next.is_ascii_whitespace() && *next != b')') {
                out.push(' ');
            }
            prev = Some(b);
            continue;
        }
        let ch = text[i..].chars().next().unwrap_or(' ');
        out.push(ch);
        if !ch.is_whitespace() {
            prev = (ch.len_utf8() == 1).then_some(ch as u8);
        }
        i += ch.len_utf8();
    }
    out
}

#[cfg(test)]
mod formula_text_tests {
    use super::{file_formula_text, formula_spacing, formula_text};
    use gridcraft_model::Formula;

    #[test]
    fn source_formula_text_keeps_spacing_and_translates_file_spellings() {
        assert_eq!(file_formula_text("F5:F8 * 2"), "F5:F8 * 2");
        assert_eq!(file_formula_text("_xlfn._xlws.SORT(F5:F8 + G5:G8)"), "SORT(F5:F8 + G5:G8)");
        assert_eq!(file_formula_text("_xlfn.LET(_xlpm.x, F5:F7, _xlpm.x*2)"), "LET(x, F5:F7, x*2)");
        assert_eq!(file_formula_text("_xlfn.ANCHORARRAY(INDEX(F5:F14, 3))"), "INDEX(F5:F14, 3)#");
        assert_eq!(file_formula_text("_xlfn.SINGLE(CHOOSE(1, G7:G9 * 2, G7:G9 * 3))"), "@CHOOSE(1, G7:G9 * 2, G7:G9 * 3)");
        assert_eq!(file_formula_text("=\"_xlfn.ANCHORARRAY(H5)\""), "=\"_xlfn.ANCHORARRAY(H5)\"");
        assert_eq!(formula_spacing(&file_formula_text("CHOOSE(1,_xlfn.ANCHORARRAY( H5)+_xlfn.ANCHORARRAY( G5))")), "CHOOSE(1, H5# + G5#)");
    }

    #[test]
    fn legacy_formula_text_shows_implicit_intersection() {
        let mut range_sum = Formula::new("=F74:F76+G74:G76");
        range_sum.source_text = Some("F74:F76+G74:G76".into());
        range_sum.legacy = true;
        assert_eq!(formula_text(&range_sum), "=@F74:F76+@G74:G76");

        let mut spill = Formula::new("=H5#");
        spill.source_text = Some("_xlfn.ANCHORARRAY(H5)".into());
        spill.legacy = true;
        assert_eq!(formula_text(&spill), "=@H5#");

        let mut unique = Formula::new("=UNIQUE(G7:G9)");
        unique.source_text = Some("_xlfn.UNIQUE(G7:G9)".into());
        unique.legacy = true;
        assert_eq!(formula_text(&unique), "=@UNIQUE(G7:G9)");
    }
}
