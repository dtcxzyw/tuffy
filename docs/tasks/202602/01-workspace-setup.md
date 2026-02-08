# Cargo Workspace and Crate Skeleton

- Status: Draft
- Created: 2026-02-07
- Completed: N/A
- Parent: docs/tasks/202602/init.md

## Description

Initialize the Cargo workspace with all tuffy crates, configure nightly Rust toolchain, and set up the basic project structure. Each crate should compile (empty lib.rs) and the workspace should build successfully.

Key deliverables:
- `Cargo.toml` workspace root with all member crates
- `rust-toolchain.toml` pinning nightly (required for rustc private APIs)
- Empty `lib.rs` for each crate with appropriate `#![feature(...)]` gates
- Dependency graph between crates matching the design in `docs/initial.md`

## Subtasks

- N/A (leaf task)

## Affected Modules

- `Cargo.toml` — workspace root
- `rust-toolchain.toml` — nightly toolchain
- `tuffy_ir/Cargo.toml` + `src/lib.rs`
- `tuffy_ir_interp/Cargo.toml` + `src/lib.rs`
- `tuffy_opt/Cargo.toml` + `src/lib.rs`
- `tuffy_target/Cargo.toml` + `src/lib.rs`
- `tuffy_target_x86/Cargo.toml` + `src/lib.rs`
- `tuffy_codegen/Cargo.toml` + `src/lib.rs`
- `tuffy_trace/Cargo.toml` + `src/lib.rs`
- `tuffy_tv/Cargo.toml` + `src/lib.rs`
- `rustc_codegen_tuffy/Cargo.toml` + `src/lib.rs`
