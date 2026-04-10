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
    let at_use_rust_path = out_dir.join("at_use_gen.rs");
    let facts_json_path = out_dir.join("peephole_facts.json");
    let facts_rust_path = out_dir.join("peephole_facts_gen.rs");
    let manifest_json_path = out_dir.join("cleanup_pass_manifest.json");
    let manifest_rust_path = out_dir.join("cleanup_pass_manifest_gen.rs");

    let build_status = Command::new("lake")
        .args(["build", "TuffyLean.Export.Json"])
        .current_dir(&lean_dir)
        .status()
        .expect("failed to invoke lake build for Lean export modules");

    if !build_status.success() {
        panic!("lake build TuffyLean.Export.Json failed");
    }

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

    let at_use_rust_src =
        tuffy_opt_gen::generate_at_use(&spec).expect("at-use Rust generation should succeed");
    fs::write(&at_use_rust_path, at_use_rust_src).expect("failed to write generated at-use Rust");

    let facts_output = Command::new("lake")
        .args([
            "env",
            "lean",
            "--run",
            "TuffyLean/Export/Json.lean",
            "--kind",
            "peephole_facts",
        ])
        .current_dir(&lean_dir)
        .output()
        .expect("failed to invoke Lean peephole fact exporter");

    if !facts_output.status.success() {
        let stderr = String::from_utf8_lossy(&facts_output.stderr);
        panic!("Lean peephole fact exporter failed:\n{stderr}");
    }

    fs::write(&facts_json_path, &facts_output.stdout).expect("failed to write peephole fact JSON");

    let facts_json_str =
        String::from_utf8(facts_output.stdout).expect("peephole fact JSON must be utf-8");
    let facts_spec = tuffy_opt_gen::load_facts_spec_from_json_str(&facts_json_str)
        .expect("generated peephole fact JSON should satisfy the generator schema");
    let facts_rust_src = tuffy_opt_gen::generate_facts(&facts_spec)
        .expect("peephole fact Rust generation should succeed");
    fs::write(&facts_rust_path, facts_rust_src)
        .expect("failed to write generated peephole fact Rust");

    let manifest_output = Command::new("lake")
        .args([
            "env",
            "lean",
            "--run",
            "TuffyLean/Export/Json.lean",
            "--kind",
            "opt_pass_manifest",
        ])
        .current_dir(&lean_dir)
        .output()
        .expect("failed to invoke Lean cleanup pass manifest exporter");

    if !manifest_output.status.success() {
        let stderr = String::from_utf8_lossy(&manifest_output.stderr);
        panic!("Lean cleanup pass manifest exporter failed:\n{stderr}");
    }

    fs::write(&manifest_json_path, &manifest_output.stdout)
        .expect("failed to write cleanup pass manifest JSON");

    let manifest_json_str = String::from_utf8(manifest_output.stdout)
        .expect("cleanup pass manifest JSON must be utf-8");
    let manifest_spec = tuffy_opt_gen::load_pass_manifest_spec_from_json_str(&manifest_json_str)
        .expect("generated cleanup pass manifest JSON should satisfy the generator schema");
    let manifest_rust_src = tuffy_opt_gen::generate_pass_manifest(&manifest_spec)
        .expect("cleanup pass manifest Rust generation should succeed");
    fs::write(&manifest_rust_path, manifest_rust_src)
        .expect("failed to write generated cleanup pass manifest Rust");
}
