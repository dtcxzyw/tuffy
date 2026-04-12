//! CLI tool: read peephole JSON and write generated Rust matcher source.

use std::fs;
use std::path::PathBuf;

/// Read the exported peephole JSON and write the generated Rust source file.
///
/// # Panics
///
/// Panics if the input JSON cannot be read, parsed, lowered, or written to the
/// output path.
fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() != 3 {
        eprintln!("Usage: tuffy_opt_gen <input.json> <output.rs>");
        std::process::exit(1);
    }

    let input_path = PathBuf::from(&args[1]);
    let output_path = PathBuf::from(&args[2]);

    let json_str = fs::read_to_string(&input_path)
        .unwrap_or_else(|e| panic!("failed to read {}: {e}", input_path.display()));

    let spec = tuffy_opt_gen::load_spec_from_json_str(&json_str)
        .unwrap_or_else(|e| panic!("failed to parse {}: {e}", input_path.display()));

    let rust_src =
        tuffy_opt_gen::generate(&spec).unwrap_or_else(|e| panic!("failed to generate Rust: {e}"));

    fs::write(&output_path, &rust_src)
        .unwrap_or_else(|e| panic!("failed to write {}: {e}", output_path.display()));

    eprintln!(
        "Generated {} peephole rules (format v{}) -> {}",
        spec.rules.len(),
        spec.format_version,
        output_path.display()
    );
}
