//! CLI tool for running tuffy IR files through the interpreter.
//!
//! Usage: tuffy-interp <file.tuffy> [--entry <name>]
//!
//! Parses the IR text file, runs the interpreter starting from the given
//! entry point (default: "main"), and prints captured stdout.

use std::process;

use tuffy_ir::parser::parse_module;
use tuffy_ir_interp::{ExecMode, InterpResult, Interpreter};

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 2 {
        eprintln!("Usage: {} <file.tuffy> [--entry <name>]", args[0]);
        process::exit(1);
    }

    let path = &args[1];
    let entry = args
        .windows(2)
        .find(|w| w[0] == "--entry")
        .map(|w| w[1].as_str())
        .unwrap_or("main");

    let ir_text = std::fs::read_to_string(path).unwrap_or_else(|e| {
        eprintln!("error: cannot read {path}: {e}");
        process::exit(1);
    });

    let module = parse_module(&ir_text).unwrap_or_else(|e| {
        eprintln!("parse error: {e}");
        process::exit(1);
    });

    let mut interp = Interpreter::new(&module, ExecMode::Normal);

    // Find the entry function — search for exact match, then suffix match.
    let func_names: Vec<String> = module
        .functions
        .iter()
        .map(|f| module.symbols.resolve(f.name).to_string())
        .collect();

    let resolved_entry = func_names
        .iter()
        .find(|n| n.as_str() == entry)
        .or_else(|| {
            // Try suffix match (e.g. "main" matches "_RNv...4main")
            func_names.iter().find(|n| {
                // Rust v0 mangling: `4main` suffix means the symbol ends with a 4-char name "main"
                n.ends_with(&format!("{}{}", entry.len(), entry))
            })
        })
        .map(|s| s.as_str())
        .unwrap_or(entry);

    let result = interp.run(resolved_entry);

    // Write captured stdout to actual stdout.
    if !interp.stdout.is_empty() {
        use std::io::Write;
        std::io::stdout().write_all(&interp.stdout).unwrap();
    }

    match result {
        InterpResult::Ok(_) => {}
        InterpResult::Ub(ub) => {
            eprintln!("interpreter UB: {ub}");
            process::exit(2);
        }
        InterpResult::FunctionNotFound(name) => {
            eprintln!("error: function not found: {name}");
            process::exit(1);
        }
        InterpResult::StackOverflow => {
            eprintln!("error: stack overflow");
            process::exit(2);
        }
        InterpResult::StepLimitExceeded => {
            eprintln!("error: step limit exceeded");
            process::exit(2);
        }
    }
}
