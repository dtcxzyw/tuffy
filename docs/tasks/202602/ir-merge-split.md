# Add merge/split IR instructions for wide integer legalization

- Status: Completed
- Created: 2026-02-28
- Completed: 2026-02-28
- Parent: docs/tasks/202602/type-legalization.md

## Description

Add two new IR instructions `merge` and `split` to support composing and decomposing wide integers into machine-width parts. These instructions are essential for legalizing 128-bit integers into pairs of 64-bit registers.

### merge

```
res = merge a, b, width
```

Replace the low `width` bits of `a` with the low `width` bits of `b`, producing a single logical value. For example, `res = merge a, b, 64` means the result has `b`'s low 64 bits as its low half and `a`'s upper bits as its high half.

### split

```
hi, lo = split a, width
```

Split `a` at bit position `width`:
- `lo` = the low `width` bits of `a` (zero-extended to register width)
- `hi` = `a` right-shifted by `width` bits

After splitting, `hi` and `lo` are independent values that can be allocated to separate registers. They only logically compose the original wide value.

### Motivation

During type legalization of i128/u128, wide values must be decomposed into register-sized parts. Currently this is handled by ad-hoc splitting in `mir_to_ir.rs`. With explicit `merge`/`split` instructions, the legalization pass can express these operations cleanly in the IR, enabling mid-end optimizations to reason about them and simplifying the lowering pipeline.

## Affected Modules

- `tuffy_ir/src/inst.rs` — add `Merge` and `Split` instruction variants
- `tuffy_ir/src/display.rs` — pretty-printing for the new instructions
- `tuffy_ir/src/parse.rs` — parsing support (if applicable)
- `tuffy_ir/src/verify.rs` — verification rules for operand types and widths
- `tuffy_ir_interp/` — interpreter support for the new instructions
- `lean/TuffyLean/IR/` — Lean 4 IR definition (source of truth)
