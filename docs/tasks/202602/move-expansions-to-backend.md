# Move frontend expansion code to backend legalization

- Status: Completed
- Created: 2026-02-28
- Completed: 2026-02-28
- Parent: N/A

## Description

`mir_to_ir.rs` contains multiple functions that expand high-level operations into low-level shift/mask/branch sequences during MIR→IR translation. This is the backend's job — the frontend should emit a single semantic IR instruction and let a legalization or lowering pass in the backend expand it.

Expanding in the frontend:
- Prevents mid-end optimizations from reasoning about the high-level operation
- Bloats the IR with implementation details before optimization
- Duplicates logic that the backend must handle anyway for other sources

## Completed

Five new IR opcodes added and wired end-to-end (Lean semantics → IR → frontend → x86 backend):

| Opcode | IR form | x86 lowering |
|--------|---------|--------------|
| `Bswap` | `bswap.N val` | Native BSWAP (4/8 bytes), shift/mask (2 bytes) |
| `RotateLeft` | `rotate_left.N val, amt` | MOV to CL + ROL |
| `RotateRight` | `rotate_right.N val, amt` | MOV to CL + ROR |
| `SaturatingAdd` | `saturating_add.N lhs, rhs` | ADD + CMOV on carry |
| `SaturatingSub` | `saturating_sub.N lhs, rhs` | SUB + CMOV on borrow |

Commits:
- `feat(lean): add bswap, rotate, and saturating arithmetic semantics`
- `feat(tuffy_ir): add bswap, rotate, and saturating arithmetic opcodes`
- `refactor(rustc_codegen_tuffy): emit bswap/rotate/saturating as single IR opcodes`
- `feat(tuffy_target_x86): add isel and encoding for bswap, rotate, saturating ops`

## Deferred

| Function | Reason |
|----------|--------|
| `emit_u128_to_float` / `emit_u64_pair_to_float` | Tied to i128 type legalization |
| `bswap` for i128 | Tied to i128 splitting (uses `builder.bswap` per word already) |
| `float_to_orderable` | Pure integer arithmetic trick, not a semantic operation |

## Affected Modules

- `lean/TuffyLean/IR/Semantics.lean` — formal semantics for 5 new ops
- `tuffy_ir/src/{instruction,builder,display,verifier}.rs` — IR definition
- `rustc_codegen_tuffy/src/mir_to_ir/intrinsic.rs` — emit single opcodes
- `tuffy_target_x86/src/{inst,isel_gen,regalloc_impl,backend,encode}.rs` — x86 backend
