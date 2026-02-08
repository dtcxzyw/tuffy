# End-to-End Minimal Pipeline

- Status: Completed
- Created: 2026-02-08
- Completed: 2026-02-08
- Parent: docs/tasks/202602/init.md

## Description

Get the minimal end-to-end pipeline working: MIR → tuffy IR → x86-64 machine code. No optimization passes. Target: compile a simple `fn add(a: i32, b: i32) -> i32 { a + b }` to a correct `.o` file.

## Subtasks

- [docs/tasks/202602/e2e-01-ir-minimal.md](e2e-01-ir-minimal.md) — Minimal IR data structures
- [docs/tasks/202602/e2e-02-codegen-backend.md](e2e-02-codegen-backend.md) — CodegenBackend entry point
- [docs/tasks/202602/e2e-03-mir-to-ir.md](e2e-03-mir-to-ir.md) — MIR to tuffy IR translation
- [docs/tasks/202602/e2e-04-isel.md](e2e-04-isel.md) — Minimal instruction selection (x86-64)
- [docs/tasks/202602/e2e-05-emit.md](e2e-05-emit.md) — Machine code emission to object file
- [docs/tasks/202602/e2e-06-test.md](e2e-06-test.md) — End-to-end test harness

## Affected Modules

- `tuffy_ir/`
- `tuffy_target/`
- `tuffy_target_x86/`
- `tuffy_codegen/`
- `rustc_codegen_tuffy/`
