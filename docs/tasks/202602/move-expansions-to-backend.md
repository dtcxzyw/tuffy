# Move frontend expansion code to backend legalization

- Status: Draft
- Created: 2026-02-28
- Completed: N/A
- Parent: N/A

## Description

`mir_to_ir.rs` contains multiple functions that expand high-level operations into low-level shift/mask/branch sequences during MIR→IR translation. This is the backend's job — the frontend should emit a single semantic IR instruction and let a legalization or lowering pass in the backend expand it.

Expanding in the frontend:
- Prevents mid-end optimizations from reasoning about the high-level operation
- Bloats the IR with implementation details before optimization
- Duplicates logic that the backend must handle anyway for other sources

## Functions to remove from mir_to_ir.rs

| Function | Lines | What it expands |
|----------|-------|-----------------|
| `emit_u128_to_float` | 948–1027 | i128/u128 → float via abs/negate/select sequence |
| `emit_u64_pair_to_float` | 1029–1100 | Two-register pair → float conversion |
| `float_to_orderable` | 1102–1120 | Float → orderable int via sign-bit XOR trick |
| `emit_bswap8` | 7569–7585 | 8-byte bswap via shift/mask loop |

## Intrinsic expansions in translate_intrinsic to simplify

| Intrinsic | Lines | Current expansion |
|-----------|-------|-------------------|
| `bswap` (i128) | 7663–7730 | Two-word load, bswap each, store swapped |
| `rotate_left/right` | 7752–7790 | `(x << a) \| (x >> (bits-a))` |
| `saturating_add` | 7923–7944 | Add + select on overflow |
| `saturating_sub` | 7945–7978 | Sub + select on underflow |

## Proposed approach

1. Emit these as single IR instructions (e.g. `bswap`, `rotate`, `saturating_add`, `uitofp`/`sitofp` for i128)
2. Add a backend legalization pass that expands them to machine-level sequences
3. This pairs naturally with the type legalization task — i128 operations and their expansions belong together

## Affected Modules

- `rustc_codegen_tuffy/src/mir_to_ir.rs` — remove expansion functions, emit single IR ops
- `tuffy_ir/` — ensure IR opcodes cover bswap, rotate, saturating arithmetic
- Backend (new legalization pass) — expand to machine sequences
