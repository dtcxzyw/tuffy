# Rustlantis Fuzz Seeds 0-100

- **Status**: Completed
- **Created**: 2025-03-24
- **Completed**: 2025-03-24

## Task Description

Run rustlantis fuzz seeds 0-100 against the Tuffy codegen backend and fix all
crashes and miscompilations.

## Affected Modules

- `tuffy_codegen/src/legalize.rs` — 128-bit value legalization
- `tuffy_target_x86/src/isel_gen.rs` — instruction selection
- `tuffy_target_x86/src/backend.rs` — register allocation spilling
- `tuffy_target_x86/src/encode.rs` — instruction encoding
- `rustc_codegen_tuffy/src/mir_to_ir/` — MIR-to-IR translation (8 files)

## Summary

Fixed ~36 bugs across three components, resulting in all 101 seeds passing:

### Legalization Pass (`tuffy_codegen`)

- `is_128_bit_int()` incorrectly matched ALL Int types as 128-bit (only
  checked `Type::Int`, not annotation `bit_width`)
- Wide value detection, wide constant guards, and parameter annotations
  for 128-bit values
- Sign-extension `shr` signedness detection from annotation
- ICmp XOR workaround for FLAGS clobbering

### x86 Backend (`tuffy_target_x86`)

- `CmpRR` always used `OpSize::S64` — sub-64-bit signed values loaded with
  zero-extending `movzx` lose sign bit, causing wrong comparison results.
  Fixed to derive size from annotation `bit_width`.
- `SetCC+MovzxB` emitted immediately after `CmpRR` to prevent FLAGS
  clobbering by intervening instructions
- `MovRR2` multi-spill: both destinations assigned to R11, losing one value.
  Fixed with SPILL_REG2 (R10) for the second destination.

### MIR-to-IR Translation (`rustc_codegen_tuffy`)

- Missing int annotations on ~10 instruction types (min/max, BinOp operands,
  intrinsic args, constant aggregates, sign-extension shr)
- `iconst` bit_width hardcoded to 64 instead of `(size_bytes * 8).min(128)`
- IntToInt/IntToFloat casts on >8-byte projected fields: `translate_operand`
  returns Ptr (address) for >8-byte types, but cast handlers called
  `coerce_to_int(Ptr)` which emits `ptrtoaddr` converting the ADDRESS to int
- Float-to-int min/max used unsigned annotations (should be signed)
- BinOp Div/Rem hardcoded `bit_width: 64`
- Two-phase `translate_params` to prevent ABI register clobbering
- `ReprKind`-based SRET/ScalarPair/Scalar ABI classification
- SwitchInt discriminant type and 128-bit constant handling
