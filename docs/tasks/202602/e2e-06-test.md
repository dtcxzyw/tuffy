# End-to-End Test Harness

- Status: Completed
- Created: 2026-02-08
- Completed: 2026-02-08
- Parent: docs/tasks/202602/e2e-pipeline.md

## Description

Create a test harness that validates the full pipeline: compile a Rust function with tuffy backend, link it, run it, verify output.

Key deliverables:
- Test program: `fn add(a: i32, b: i32) -> i32 { a + b }` compiled with `-Z codegen-backend`
- C driver program that calls the compiled function and checks the result
- Integration test that runs the full pipeline: rustc → tuffy → .o → link → execute → verify
- `objdump` validation: disassembly matches expected x86-64 instructions
- CI-compatible: runs as part of `cargo test`

## Affected Modules

- `rustc_codegen_tuffy/tests/`
- Test fixtures
