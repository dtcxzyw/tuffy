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

## Current Results (2026-02-18)

| Category | Count | % of non-skipped |
|----------|------:|----:|
| Pass | 4150 | 81.9 |
| Compile fail | 235 | 4.6 |
| Link fail | 2 | 0.0 |
| Run fail | 678 | 13.4 |
| Skip | 12687 | — |
| **Total** | **17752** | |

81.9% pass rate on non-skipped tests (4150/5065).

## Affected Modules

- `rustc_codegen_tuffy/src/mir_to_ir.rs`
- `rustc_codegen_tuffy/src/lib.rs`
- `tuffy_codegen/src/isel.rs`
- `tuffy_codegen/src/encode.rs`
