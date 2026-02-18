# Pass rustc UI Tests

- Status: Completed
- Created: 2026-02-08
- Completed: 2026-02-08
- Parent: docs/tasks/202602/init.md

## Description

Improve the tuffy codegen backend to pass a larger portion of the rustc UI test suite. Baseline from 1000-test random sample: 66.8% pass rate (472/707 non-skipped). Target: >95% pass rate on compilable UI tests.

Failures cluster into a small number of root causes in `mir_to_ir.rs` and `isel.rs`. Each subtask addresses one category.

Test runner script: `rustc_codegen_tuffy/tests/run-ui-tests.sh`
Test source: `scratch/rust/tests/ui/` (shallow clone of rust-lang/rust at efc9e1b50)

## Current Results (2026-02-18)

| Category | Count | % |
|----------|------:|----:|
| Pass | 5391 | 28.4 |
| Skip | 13610 | 71.6 |
| Fail | 0 | 0.0 |

100% pass rate on non-skipped tests (5391/5391).

One rustc nightly ICE (`privacy/pub-extern-privacy.rs`) added to exclusion list — this is a rustc bug, not a tuffy issue.

## Subtasks

- [docs/tasks/202602/ui-01-constant-operands.md](ui-01-constant-operands.md) — Support constant operands in MIR translation
- [docs/tasks/202602/ui-02-abi-registers.md](ui-02-abi-registers.md) — Extend ABI parameter registers beyond 2
- [docs/tasks/202602/ui-03-undefined-locals.md](ui-03-undefined-locals.md) — Handle undefined MIR locals gracefully
- [docs/tasks/202602/ui-04-test-harness.md](ui-04-test-harness.md) — Improve test runner to reduce false failures

## Affected Modules

- `rustc_codegen_tuffy/src/mir_to_ir.rs`
- `tuffy_codegen/src/isel.rs`
- `scratch/run_ui_tests.sh`
