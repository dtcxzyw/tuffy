# Minimal Instruction Selection (x86-64)

- Status: Completed
- Created: 2026-02-08
- Completed: 2026-02-08
- Parent: docs/tasks/202602/e2e-pipeline.md

## Description

Implement minimal instruction selection: lower tuffy IR to x86-64 machine instructions. Only enough to handle the `add` function.

Key deliverables:
- Derive concrete bit widths from assert nodes (assertsext(32) → i32 → 32-bit GPR)
- Lower `add` on int → x86-64 `add` on 32-bit registers
- Lower `ret` → x86-64 `ret`
- System V AMD64 ABI: first two i32 args in %edi, %esi; return in %eax
- Trivial register allocation (no spilling needed for this case)
- Output: list of x86-64 machine instructions with register assignments

Not included:
- Complex register allocation (spilling, coalescing)
- Stack frame setup (not needed for leaf function with no locals)
- Floating point
- Memory operations beyond simple loads/stores

## Affected Modules

- `tuffy_codegen/src/`
- `tuffy_target/src/`
- `tuffy_target_x86/src/`
