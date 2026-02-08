# Extend ABI Parameter Registers Beyond 2

- Status: Draft
- Created: 2026-02-08
- Completed: N/A
- Parent: docs/tasks/202602/ui-tests.md

## Description

The instruction selector panics at `isel.rs:61` when a function has more than 2 parameters. The System V AMD64 ABI passes the first 6 integer arguments in registers: `rdi`, `rsi`, `rdx`, `rcx`, `r8`, `r9`. The current `ABI_ARGS` array only contains `[Rdi, Rsi]`.

This is ~20% of UI test failures.

Key deliverables:
- Extend `ABI_ARGS` to all 6 integer parameter registers
- Add `Rdx`, `Rcx`, `R8`, `R9` to the GPR register enum
- Handle functions with >6 parameters gracefully (skip codegen or use stack)
- Update register encoding for REX-prefixed registers (R8-R9)

## Affected Modules

- `tuffy_codegen/src/isel.rs` — `ABI_ARGS` array, `select_inst` for Param
- `tuffy_target_x86/src/reg.rs` — add R8-R15 registers
- `tuffy_codegen/src/encode.rs` — REX prefix encoding for R8+
