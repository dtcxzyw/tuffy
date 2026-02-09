# Stack Frame, Load/Store, Aggregate Types

- Status: Completed
- Created: 2026-02-08
- Completed: 2026-02-09
- Parent: docs/tasks/202602/hello-world.md

## Description

The backend has no memory operations. All values live in registers with no stack frame. Real code needs local variables on the stack, pointer dereferencing, and aggregate type handling (structs, tuples, arrays).

Key deliverables:
- Emit function prologue/epilogue (push rbp, sub rsp, pop rbp)
- Allocate stack slots for MIR locals that don't fit in registers
- Translate MIR `Place` projections (field access, deref, index)
- Emit MOV with memory operands (load/store with [rbp+offset] addressing)
- Support `Ref` and `AddressOf` rvalues
- Handle `Aggregate` rvalue (struct/tuple construction)

## Affected Modules

- `rustc_codegen_tuffy/src/mir_to_ir.rs` — Place projections, Ref, Aggregate rvalues
- `tuffy_ir/src/instruction.rs` — Load, Store, StackSlot, PtrAdd ops
- `tuffy_target_x86/src/isel.rs` — PtrAdd lowering, ensure_in_reg, MOV with memory operands, LEA
- `tuffy_target_x86/src/encode.rs` — ModR/M with displacement, SIB byte encoding
