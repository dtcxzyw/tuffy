# MIR to Tuffy IR Translation

- Status: Draft
- Created: 2026-02-08
- Completed: N/A
- Parent: docs/tasks/202602/e2e-pipeline.md

## Description

Implement the actual MIR → tuffy IR translation in the Builder. Minimal subset: enough to translate `fn add(a: i32, b: i32) -> i32 { a + b }`.

Key deliverables:
- Translate MIR basic blocks to tuffy IR basic blocks
- Translate MIR statements: Assign (with Rvalue::BinaryOp)
- Translate MIR terminators: Return
- Translate MIR operands: Copy, Move, Constant
- Translate MIR places: Local variables
- Type translation: i32 → int + assertsext(32)
- Function parameters: map MIR args to tuffy IR values
- mem2reg: promote simple locals to SSA values (reuse rustc_codegen_ssa's SSA analysis)

Not included:
- Control flow (branches, loops)
- Function calls
- Aggregate types
- Drop/unwind

## Affected Modules

- `rustc_codegen_tuffy/src/`
