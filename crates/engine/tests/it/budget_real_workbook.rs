//! Excel-verified recalculation of the public JovialIO Monthly Budget Tracker workbook.

use gridcraft_engine::core::{CellRef, Value};
use gridcraft_engine::{Session, io::base64_encode};
use serde_json::json;

const WORKBOOK: &[u8] = include_bytes!("../data/monthly-budget-tracker.xlsx");
const EXCEL_VALUES: &str = include_str!("../data/monthly-budget-tracker-excel-values.tsv");

fn value(session: &Session, sheet: &str, cell: &str) -> Value {
    let workbook = &session.doc().unwrap().wb;
    let sheet_index = workbook.sheets.iter().position(|candidate| candidate.name == sheet).unwrap();
    workbook.sheet(sheet_index).unwrap().value(CellRef::parse(cell).unwrap())
}

fn assert_excel_number(session: &Session, sheet: &str, cell: &str, expected: f64) {
    let actual = value(session, sheet, cell);
    let Value::Number(actual) = actual else {
        panic!("{sheet}!{cell}: expected {expected}, got {actual:?}");
    };
    assert!((actual - expected).abs() <= 1e-9 * expected.abs().max(1.0), "{sheet}!{cell}: {actual} != {expected}");
}

#[test]
fn public_monthly_budget_tracker_matches_excel_on_open_and_input_edit() {
    let mut session = Session::new();
    session.execute("file.open", json!({"name": "monthly-budget-tracker.xlsx", "base64": base64_encode(WORKBOOK)})).unwrap();

    let mut checked = 0;
    for line in EXCEL_VALUES.lines().filter(|line| !line.is_empty() && !line.starts_with('#')) {
        let (address, expected) = line.split_once('\t').expect("oracle row has an address and value");
        let (sheet, cell) = address.split_once('!').expect("oracle address has a sheet");
        if let Ok(expected) = expected.parse::<f64>() {
            assert_excel_number(&session, sheet, cell, expected);
        } else {
            assert_eq!(value(&session, sheet, cell), Value::from(expected), "{address}");
        }
        checked += 1;
    }
    assert_eq!(checked, 1_825, "the oracle covers every pre-fix differing formula result");

    session.execute("cell.set", json!({"sheet": "Entries", "cell": "E779", "input": "99.99"})).unwrap();
    assert_excel_number(&session, "Dashboard", "B48", 219.99);
    assert_excel_number(&session, "Dashboard", "C5", 3510.834166666667);
    assert_excel_number(&session, "Dashboard", "B58", 45809.0);
    assert_excel_number(&session, "Dashboard", "C47", 600.0);
    assert_excel_number(&session, "Monthly Summary", "AR10", 400.0);
    assert_excel_number(&session, "Monthly Summary", "F10", 1650.0);
}
