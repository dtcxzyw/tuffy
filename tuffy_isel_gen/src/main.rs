//! CLI tool: read isel rules JSON, write generated Rust source.

mod codegen;
mod schema;

use std::fs;
use std::path::PathBuf;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() != 3 {
        eprintln!("Usage: tuffy_isel_gen <input.json> <output.rs>");
        std::process::exit(1);
    }

    let input_path = PathBuf::from(&args[1]);
    let output_path = PathBuf::from(&args[2]);

    let json_str = fs::read_to_string(&input_path)
        .unwrap_or_else(|e| panic!("failed to read {}: {e}", input_path.display()));

    let rules: Vec<schema::IselRule> =
        serde_json::from_str(&json_str).unwrap_or_else(|e| panic!("failed to parse JSON: {e}"));

    let rust_src = codegen::generate(&rules);

    fs::write(&output_path, &rust_src)
        .unwrap_or_else(|e| panic!("failed to write {}: {e}", output_path.display()));

    eprintln!(
        "Generated {} rules -> {}",
        rules.len(),
        output_path.display()
    );
}
