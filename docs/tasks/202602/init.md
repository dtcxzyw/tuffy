# Initialize rustc_codegen_tuffy Project Structure

- Status: Draft
- Created: 2026-02-07
- Completed: N/A
- Parent: N/A

## Description

Set up the initial Rust project structure for `rustc_codegen_tuffy`, a production-grade codegen backend for rustc. This includes initializing the Cargo workspace, establishing the crate structure, implementing the core IR, and configuring the project to build against rustc's codegen interface.

Key goals:
- Initialize Cargo workspace with all tuffy crates
- Implement the core IR (tuffy_ir) based on the IR design RFC
- Set up the codegen backend entry point implementing `rustc_codegen_ssa::CodegenBackend`
- Configure nightly Rust toolchain (required for rustc private APIs)
- Establish multi-platform target abstraction
- Implement a tuffy IR interpreter for testing and validation
- Set up the optimization pipeline infrastructure
- Set up rewrite path tracing infrastructure
- Set up Lean 4 formal verification integration
- Ensure the backend can be loaded by rustc via `-Z codegen-backend`

## Subtasks

- [docs/tasks/202602/01-workspace-setup.md](01-workspace-setup.md) — Cargo workspace and crate skeleton
- [docs/tasks/202602/02-tuffy-ir.md](02-tuffy-ir.md) — Core IR implementation
- [docs/tasks/202602/03-tuffy-ir-interp.md](03-tuffy-ir-interp.md) — IR interpreter
- [docs/tasks/202602/04-tuffy-target.md](04-tuffy-target.md) — Target abstraction layer
- [docs/tasks/202602/05-tuffy-opt.md](05-tuffy-opt.md) — Optimization pipeline infrastructure
- [docs/tasks/202602/06-tuffy-trace.md](06-tuffy-trace.md) — Rewrite path tracing
- [docs/tasks/202602/07-tuffy-tv.md](07-tuffy-tv.md) — Translation validation
- [docs/tasks/202602/08-tuffy-codegen.md](08-tuffy-codegen.md) — Instruction selection and machine code emission
- [docs/tasks/202602/09-rustc-codegen-tuffy.md](09-rustc-codegen-tuffy.md) — Rustc frontend adapter

## Affected Modules

- `tuffy_ir/` — core IR definition
- `tuffy_ir_interp/` — IR interpreter
- `tuffy_opt/` — optimization passes
- `tuffy_target/` — target abstraction
- `tuffy_target_x86/` — x86 backend
- `tuffy_codegen/` — instruction selection, register allocation, emission
- `tuffy_trace/` — rewrite path tracing
- `tuffy_tv/` — translation validation
- `rustc_codegen_tuffy/` — rustc frontend adapter
- `lean/` — Lean 4 formal verification
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
