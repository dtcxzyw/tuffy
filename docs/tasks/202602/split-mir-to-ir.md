# Split mir_to_ir.rs into smaller modules

- Status: Draft
- Created: 2026-02-27
- Completed: N/A
- Parent: N/A

## Description

`rustc_codegen_tuffy/src/mir_to_ir.rs` is 8741 lines — too large to navigate and maintain effectively. It should be split into a module directory (`mir_to_ir/`) with focused submodules.

## Current structure

| Lines | Content |
|-------|---------|
| 1–572 | Entry point `translate_function`, `TranslationResult`, `StaticDataVec` |
| 574–882 | Helper data structures: `LocalMap`, `FatLocalMap`, `StackLocalSet`, `BlockMap` |
| 616–860 | Type utilities: `translate_ty`, `field_offset`, `type_size`, `type_align`, ABI helpers |
| 888–7100 | `TranslationCtx` struct + all methods (bulk of the file) |
| 7102–7568 | Standalone helpers: `translate_int_to_int_cast`, `translate_const`, `translate_scalar`, `translate_const_slice` |
| 7590–8526 | Intrinsic handling: `translate_intrinsic`, `translate_memory_intrinsic`, `detect_intrinsic` |
| 8527–8741 | Call resolution: `CallTarget`, `ResolvedCall`, `resolve_call_target` |

## Proposed split

| Module | Content |
|--------|---------|
| `mir_to_ir/mod.rs` | `translate_function`, `TranslationResult`, re-exports |
| `mir_to_ir/types.rs` | `translate_ty`, `translate_annotation`, `field_offset`, `type_size`, `type_align`, `needs_indirect_return`, `is_signed_int`, `int_bitwidth`, `is_fat_ptr`, `fat_ptr_meta_type` |
| `mir_to_ir/ctx.rs` | `TranslationCtx` struct definition, `LocalMap`, `FatLocalMap`, `StackLocalSet`, `BlockMap`, `extract_param_names` |
| `mir_to_ir/statement.rs` | `translate_statement`, `translate_set_discriminant`, `write_enum_tag` |
| `mir_to_ir/rvalue.rs` | `translate_rvalue`, `translate_operand`, `translate_place_*`, `extract_fat_component` |
| `mir_to_ir/terminator.rs` | `translate_terminator`, `translate_switch_int` |
| `mir_to_ir/call.rs` | `translate_call`, `CallTarget`, `ResolvedCall`, `resolve_call_target` |
| `mir_to_ir/constant.rs` | `translate_const`, `translate_scalar`, `translate_const_slice`, `extract_alloc_relocs`, `translate_int_to_int_cast` |
| `mir_to_ir/intrinsic.rs` | `translate_intrinsic`, `translate_memory_intrinsic`, `detect_intrinsic`, `intrinsic_to_libc`, `emit_bswap8` |

## Affected Modules

- `rustc_codegen_tuffy/src/mir_to_ir.rs` → split into `rustc_codegen_tuffy/src/mir_to_ir/` directory
