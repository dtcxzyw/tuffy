use std::env;
use std::fs;
use std::path::PathBuf;
use std::process::Command;

fn main() {
    println!("cargo:rerun-if-changed=../lean/TuffyLean");
    println!("cargo:rerun-if-changed=../lean/TuffyLean.lean");
    println!("cargo:rerun-if-changed=../lean/lakefile.toml");
    println!("cargo:rerun-if-changed=../lean/lean-toolchain");

    let manifest_dir = PathBuf::from(env::var("CARGO_MANIFEST_DIR").expect("missing manifest dir"));
    let lean_dir = manifest_dir.join("../lean");
    let out_dir = PathBuf::from(env::var("OUT_DIR").expect("missing OUT_DIR"));
    let json_path = out_dir.join("peephole_rules.json");
    let rust_path = out_dir.join("peephole_gen.rs");

    let output = Command::new("lake")
        .args([
            "env",
            "lean",
            "--run",
            "TuffyLean/Export/Json.lean",
            "--kind",
            "peephole",
        ])
        .current_dir(&lean_dir)
        .output()
        .expect("failed to invoke Lean peephole exporter");

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        panic!("Lean peephole exporter failed:\n{stderr}");
    }

    fs::write(&json_path, &output.stdout).expect("failed to write peephole rule JSON");

    let json_str = String::from_utf8(output.stdout).expect("peephole JSON must be utf-8");
    let spec = tuffy_opt_gen::load_spec_from_json_str(&json_str)
        .expect("generated peephole JSON should satisfy the generator schema");
    let rust_src = tuffy_opt_gen::generate(&spec).expect("peephole Rust generation should succeed");
    fs::write(&rust_path, rust_src).expect("failed to write generated peephole Rust");
}
