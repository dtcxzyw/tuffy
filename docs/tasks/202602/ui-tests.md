# Pass rustc UI Tests

- Status: Draft
- Created: 2026-02-08
- Completed: N/A
- Parent: docs/tasks/202602/init.md

## Description

Improve the tuffy codegen backend to pass a larger portion of the rustc UI test suite. Baseline from 1000-test random sample: 66.8% pass rate (472/707 non-skipped). Target: >95% pass rate on compilable UI tests.

Failures cluster into a small number of root causes in `mir_to_ir.rs` and `isel.rs`. Each subtask addresses one category.

Test runner script: `scratch/run_ui_tests.sh`
Test source: `scratch/rust/tests/ui/` (shallow clone of rust-lang/rust at efc9e1b50)

## Subtasks

- [docs/tasks/202602/ui-01-constant-operands.md](ui-01-constant-operands.md) — Support constant operands in MIR translation
- [docs/tasks/202602/ui-02-abi-registers.md](ui-02-abi-registers.md) — Extend ABI parameter registers beyond 2
- [docs/tasks/202602/ui-03-undefined-locals.md](ui-03-undefined-locals.md) — Handle undefined MIR locals gracefully
- [docs/tasks/202602/ui-04-test-harness.md](ui-04-test-harness.md) — Improve test runner to reduce false failures

## Affected Modules

- `rustc_codegen_tuffy/src/mir_to_ir.rs`
- `tuffy_codegen/src/isel.rs`
- `scratch/run_ui_tests.sh`
