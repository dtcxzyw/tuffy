# Add BitReverse, FCmp, FRem IR instructions

- Status: Completed
- Created: 2026-02-28
- Completed: 2026-02-28
- Parent: N/A

## Description

Audit of `mir_to_ir` revealed three missing IR operations:
1. `bitreverse` intrinsic is silently skipped (no IR op exists)
2. Float comparisons use a `float_to_orderable` hack converting floats to orderable integers, then using `icmp` — NaN semantics are wrong
3. Float `%` (Rem) falls through to integer `rem` — completely wrong for floats

## Subtasks

- Add `BitReverse` IR instruction (instruction, builder, display, verifier, Lean, codegen)
- Add `FCmp` IR instruction with `FCmpOp` enum (instruction, builder, display, verifier, Lean, codegen, isel)
- Add `FRem` IR instruction (instruction, builder, display, verifier, Lean, codegen)

## Affected Modules

- `tuffy_ir` — new instruction variants, builder methods, display, verifier
- `lean/TuffyLean/IR/Semantics.lean` — formal semantics
- `rustc_codegen_tuffy` — MIR-to-IR translation (intrinsic.rs, rvalue.rs, ctx.rs)
- `tuffy_isel_gen` — isel codegen for FCmp dispatch
