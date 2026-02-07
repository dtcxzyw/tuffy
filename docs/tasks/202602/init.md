# Initialize rustc_codegen_tuffy Project Structure

- Status: Draft
- Created: 2026-02-07
- Completed: N/A

## Description

Set up the initial Rust project structure for `rustc_codegen_tuffy`, a production-grade codegen backend for rustc. This includes initializing the Cargo workspace, establishing the crate structure, and configuring the project to build against rustc's codegen interface.

Key goals:
- Initialize Cargo workspace with the `rustc_codegen_tuffy` crate
- Set up the codegen backend entry point implementing `rustc_codegen_ssa::CodegenBackend`
- Configure nightly Rust toolchain (required for rustc private APIs)
- Establish multi-platform target abstraction from the start
- Define the custom IR skeleton (to be detailed in a follow-up RFC)
- Ensure the backend can be loaded by rustc via `-Z codegen-backend`

## Affected Modules

- `rustc_codegen_tuffy/` — new crate: the codegen backend entry point
- `Cargo.toml` — workspace configuration
- `rust-toolchain.toml` — nightly toolchain pinning

## Testing Strategy

Validation and benchmarking will use the following targets (in progressive order):

1. **Internal unit tests** — small test cases for basic codegen correctness (arithmetic, control flow, function calls)
2. **`no_std` programs** — minimal programs to validate the backend without standard library dependencies
3. **serde** — widely used crate with heavy generics and macros, tests monomorphization and trait dispatch
4. **rustc test suite** — rustc's ui tests for broad correctness coverage
5. **ripgrep** — real-world CLI project for end-to-end correctness and performance comparison against LLVM backend
6. **clippy** — later-stage validation target due to tight coupling with rustc internals
