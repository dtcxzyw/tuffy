# Support Constant Operands in MIR Translation

- Status: Completed
- Created: 2026-02-08
- Completed: 2026-02-08
- Parent: docs/tasks/202602/ui-tests.md

## Description

The MIR translator panics at `mir_to_ir.rs:159` when encountering `Operand::Constant`. This is the largest failure category (~40% of UI test failures).

Rust MIR uses `Operand::Constant` for integer literals, bool values, unit `()`, string literals, function pointers, and other compile-time constants. The current `translate_operand` only handles `Copy` and `Move`.

Key deliverables:
- Handle `Operand::Constant` for integer literals (i32, u32, i64, etc.)
- Handle `Operand::Constant` for bool and unit `()`
- Add `const_int` instruction or equivalent to tuffy IR builder
- Skip/ignore unsupported constant types (function pointers, string refs) gracefully instead of panicking

## Affected Modules

- `rustc_codegen_tuffy/src/mir_to_ir.rs` — `translate_operand` function
- `tuffy_ir/src/` — may need `const_int` builder method
