# Add i128/u128 IR types and type legalization pass

- Status: Completed
- Created: 2026-02-28
- Completed: 2026-02-28
- Parent: N/A

## Description

`mir_to_ir.rs` has ~16 sites with `size > 8` checks that manually split 9-16 byte values into two registers at the MIR→IR boundary. This scatters ABI/lowering concerns throughout the translation layer, making the code fragile and hard to maintain.

The current IR type system has `Type::Int` (infinite precision) but no fixed-width wide integer types. Values wider than 64 bits are handled by ad-hoc two-register splitting during translation.

### Current approach (problematic)

- Parameter passing: `param_size > 8 && param_size <= 16` → emit two `Type::Int` params
- Return values: `ret_size > 8` → split into two registers or use sret
- Assignments, casts, calls: scattered `size > 8` checks with manual hi/lo splitting
- ~16 code sites affected, each duplicating similar logic

### Proposed approach

Follow LLVM's model:

1. **Emit i128/u128 as a single IR value** during MIR→IR translation (e.g. `Type::Int` with an annotation, or a new `Type::WideInt(bits)`)
2. **Mid-end optimizations** work on the full-width type naturally
3. **Type legalization pass** (after optimization, before isel) splits wide integers into machine-width pairs, handling:
   - Parameter splitting (System V AMD64: two registers for 9-16 byte values)
   - Return value splitting
   - Arithmetic lowering (add-with-carry, etc.)

This cleanly separates concerns: translation emits semantic types, legalization handles machine constraints.

## Affected sites in mir_to_ir.rs

| Line(s) | Context |
|----------|---------|
| 136, 145 | Parameter passing: >16 bytes → ptr, 9-16 bytes → two regs |
| 520 | Return value: ret_size > 8 → two-register return |
| 1219-1221 | translate_params: large_struct / two_reg detection |
| 2334 | Assignment: src_size > 8 handling |
| 3295, 3520 | Rvalue translation: size > 8 splitting |
| 3750 | Fat pointer + size > 8 |
| 4197, 4205, 4230, 4267 | Call arguments: multi-register arg passing |
| 6267, 6300 | Cast: src_size > 8 |
| 7672 | Intrinsic: byte_size > 8 |

## Affected Modules

- `tuffy_ir/src/types.rs` — potentially add wide integer type or annotation
- `rustc_codegen_tuffy/src/mir_to_ir.rs` — simplify by emitting single wide values
- New pass (e.g. `tuffy_opt/` or `tuffy_codegen/`) — type legalization before isel
