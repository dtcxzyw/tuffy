# Run-Pass Tests

- Status: In Progress
- Created: 2026-02-18
- Completed: N/A
- Parent: N/A

## Description

Compile and execute rustc UI tests that contain `fn main()` using the tuffy codegen backend.
Unlike UI tests (compile-only as `--crate-type lib`), run-pass tests build full binaries and execute them.

Test runner script: `rustc_codegen_tuffy/tests/run-pass-tests.sh`
Test source: `scratch/rust/tests/ui/` (shallow clone of rust-lang/rust)

## Current Results (2026-02-25)

| Category | Count | % of non-skipped |
|----------|------:|----:|
| Pass | 4294 | 100.0 |
| Compile fail | 0 | 0.0 |
| Link fail | 0 | 0.0 |
| Run fail | 0 | 0.0 |
| Skip | 13483 | — |
| **Total** | **17777** | |

100% pass rate on non-skipped, non-excluded tests (4294/4294).
782 tests excluded (known failures).

### Changes from 2026-02-18

- Fixed edition handling in test script (parse `//@ edition:` directives)
- Fixed PtrToPtr cast from large stack locals (Box::new double-free)
- Recovered 178 previously excluded tests
- Discovered 116 pre-existing failures hidden by script bug

## Affected Modules

- `rustc_codegen_tuffy/src/mir_to_ir.rs`
- `rustc_codegen_tuffy/src/lib.rs`
- `tuffy_codegen/src/isel.rs`
- `tuffy_codegen/src/encode.rs`
