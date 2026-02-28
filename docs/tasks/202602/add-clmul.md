# Add Carry-Less Multiplication (clmul) IR Instruction

- Status: Completed
- Created: 2026-02-28
- Completed: 2026-02-28
- Parent: N/A

## Description

Add a carry-less multiplication (`clmul`) instruction to the tuffy IR. Carry-less
multiplication (also known as polynomial multiplication over GF(2)) computes the
product of two integers using XOR instead of addition for accumulating partial
products. This operation is fundamental for cryptographic algorithms (AES-GCM,
CRC computation) and is supported by hardware on modern x86 (PCLMULQDQ) and
ARM (PMULL) processors.

The instruction operates on non-negative integers with infinite precision.
Negative inputs produce poison.

## Subtasks

- Add Lean 4 formal semantics (`evalClmul`)
- Add Rust IR variant `Op::Clmul(Operand, Operand)`
- Add builder, display, verifier support
- Add unit tests
- Update spec documentation

## Affected Modules

- `lean/TuffyLean/IR/Semantics.lean` — formal semantics definition
- `tuffy_ir/src/instruction.rs` — Op enum variant
- `tuffy_ir/src/builder.rs` — builder convenience method
- `tuffy_ir/src/display.rs` — text format output
- `tuffy_ir/src/verifier.rs` — type checking rules
- `tuffy_ir/src/tests.rs` — unit tests
- `docs/spec/instructions.md` — spec documentation
