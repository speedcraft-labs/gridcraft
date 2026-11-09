//! One GridCraft task against a pinned workbook: open, edit one cell, or save once.
//! Process wall time is measured by craft-journeys from launch through exit.

#![allow(clippy::disallowed_methods)] // native-only benchmark; wasm never runs it

use std::{error::Error, path::Path, time::Instant};

use gridcraft_engine::Session;
use serde_json::json;
use sha2::{Digest, Sha256};

fn hex(bytes: impl AsRef<[u8]>) -> String {
    bytes.as_ref().iter().map(|byte| format!("{byte:02x}")).collect()
}

fn digest(session: &Session) -> Result<String, Box<dyn Error>> {
    let doc = session.doc()?;
    let mut cells = Vec::new();
    for (sheet_index, sheet) in doc.wb.sheets.iter().enumerate() {
        cells.extend(sheet.cells.iter().map(|(cell, value)| (sheet_index, cell, format!("{:?}", value.value))));
    }
    cells.sort_by_key(|(sheet, cell, _)| (*sheet, cell.row, cell.col));
    let mut hash = Sha256::new();
    for (sheet, cell, value) in cells {
        hash.update(sheet.to_le_bytes());
        hash.update(cell.row.to_le_bytes());
        hash.update(cell.col.to_le_bytes());
        hash.update(value.as_bytes());
    }
    Ok(hex(hash.finalize()))
}

fn main() -> Result<(), Box<dyn Error>> {
    let mut args = std::env::args().skip(1);
    let task = args.next().ok_or("task: open|edit|save")?;
    let input_name = args.next().ok_or("input name is required")?;
    let path = args.next().ok_or("workbook path is required")?;
    let cell = args.next().unwrap_or_else(|| "A3".into());
    let value = args.next().unwrap_or_else(|| "Department of Commerce revised".into());
    let output = args.next().unwrap_or_else(|| "/tmp/craft-journeys-gridcraft.xlsx".into());
    if !matches!(task.as_str(), "open" | "edit" | "save") {
        return Err(format!("unknown single task {task:?}").into());
    }

    let mut session = Session::new();
    let started = Instant::now();
    session.execute("file.open", json!({"path": path}))?;
    let open_ns = started.elapsed().as_nanos() as u64;
    let mut task_ns = open_ns;
    if task == "edit" || task == "save" {
        let started = Instant::now();
        session.execute("cell.set", json!({"cell": cell, "input": value}))?;
        task_ns = started.elapsed().as_nanos() as u64;
    }
    if task == "save" {
        let started = Instant::now();
        session.execute("file.saveAs", json!({"path": output}))?;
        task_ns = started.elapsed().as_nanos() as u64;
        if !Path::new(&output).is_file() {
            return Err(format!("save did not create {output}").into());
        }
    }

    println!("CRAFT_JOURNEY_NS={task_ns}");
    println!("CRAFT_OUTPUT_SHA256={}", digest(&session)?);
    println!("GridCraft {task} {input_name}: {}", Path::new(&path).file_name().and_then(|name| name.to_str()).unwrap_or("workbook"));
    Ok(())
}
