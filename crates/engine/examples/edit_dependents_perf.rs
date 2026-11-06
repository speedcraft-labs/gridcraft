//! Reproduce the “edit with 100k dependents” journey.
//! Run without an argument for the deterministic synthetic workbook, or with an XLSX path to
//! exercise a real workbook. Setup and the full-recalc oracle are outside the edit measurement.

#![allow(clippy::disallowed_methods)]

use std::{path::Path, time::Instant};

use gridcraft_engine::{Session, calc::Calc};
use serde_json::json;
use sha2::{Digest, Sha256};

fn main() {
    let mut args = std::env::args().skip(1);
    let input_name = args.next().unwrap_or_default();
    let path = if input_name.starts_with("synthetic-") { None } else { args.next().filter(|s| !s.is_empty()) };
    let mut session = Session::new();
    if let Some(path) = path.as_deref() {
        session.execute("file.open", json!({"path": path})).expect("open real workbook");
        // 51710.xlsx uses B2 as a rate input referenced by its formula table. For the larger
        // LibreOffice corpus case, B2 is simply an ordinary edit that still exercises load/recalc.
        session.execute("cell.set", json!({"cell": "B2", "input": "100"})).expect("warm real edit");
    } else {
        build_synthetic(&mut session);
    }

    // Warm the edited cell and establish the exact answer before measuring the same edit again.
    let edit = if path.is_some() { "B2" } else { "A1" };
    let input = if path.is_some() { "101" } else { "2" };
    session.execute("cell.set", json!({"cell": edit, "input": input})).expect("warm edit");
    let t0 = Instant::now();
    session.execute("cell.set", json!({"cell": edit, "input": if path.is_some() { "100" } else { "1" }})).expect("measured edit");
    let elapsed = t0.elapsed().as_nanos() as u64;

    let d = session.doc().expect("document");
    let incremental = values(&d.wb);
    let mut full = (*d.wb).clone();
    let mut oracle = Calc::new();
    oracle.recalc_all(&mut full);
    let recalculated = values(&full);
    assert_eq!(incremental, recalculated, "incremental edit differs from full recalculation");

    let mut hash = Sha256::new();
    for (sheet, cell, value) in incremental {
        hash.update(sheet.to_le_bytes());
        hash.update(cell.row.to_le_bytes());
        hash.update(cell.col.to_le_bytes());
        hash.update(format!("{value:?}").as_bytes());
    }
    println!("CRAFT_JOURNEY_NS={elapsed}");
    print!("CRAFT_OUTPUT_SHA256=");
    for byte in hash.finalize() {
        print!("{byte:02x}");
    }
    println!();
    if let Some(path) = path {
        println!("real workbook: {} ({})", Path::new(&path).file_name().unwrap_or_default().to_string_lossy(), d.calc.last_recalc_cells);
    } else {
        println!("synthetic workbook: 100000 formulas, {} recalculated", d.calc.last_recalc_cells);
    }
}

fn build_synthetic(session: &mut Session) {
    session.new_workbook();
    session.execute("cell.set", json!({"cell": "A1", "input": "1"})).expect("source");
    // 50k direct dependents (fan-out).
    session.execute("cell.set", json!({"cell": "B1", "input": "=$A$1+1"})).expect("fan-out seed");
    session.execute("edit.autoFill", json!({"source": "B1", "target": "B1:B50000"})).expect("fan-out formulas");
    // 50k formulas in a dependency chain.
    session.execute("cell.set", json!({"cell": "C1", "input": "=$A$1+1"})).expect("chain seed");
    session.execute("cell.set", json!({"cell": "C2", "input": "=C1+1"})).expect("chain second cell");
    session.execute("edit.autoFill", json!({"source": "C2", "target": "C2:C50000"})).expect("chain formulas");
}

fn values(wb: &gridcraft_engine::model::Workbook) -> Vec<(usize, gridcraft_engine::core::CellRef, gridcraft_engine::core::Value)> {
    let mut values = Vec::new();
    for (sheet_index, sheet) in wb.sheets.iter().enumerate() {
        values.extend(sheet.cells.iter().map(|(cell, value)| (sheet_index, cell, value.value.clone())));
    }
    values.sort_by_key(|(sheet, cell, _)| (*sheet, cell.row, cell.col));
    values
}
