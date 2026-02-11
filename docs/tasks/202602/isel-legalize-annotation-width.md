# Handle non-standard annotation bit-widths in isel

- Status: Completed
- Created: 2026-02-10
- Completed: 2026-02-11
- Parent: N/A

## Description

The x86 instruction selector (`tuffy_target_x86/src/isel.rs`) does not correctly handle
annotations with non-standard bit-widths (i.e., widths that are not 8, 16, 32, or 64).

### Current behavior

Most arithmetic operations (add/sub/mul, bitwise, div, icmp) are unaffected because they
operate at 64-bit width regardless of annotation. The annotation is a semantic constraint
(violation produces poison), not a machine type directive, so 64-bit operations produce
correct results for any sub-64-bit range.

However, **Sext/Zext** only match exact widths 8, 16, 32 and fall through to an incorrect
default for anything else (e.g., u17 → default MovsxD, which is wrong):

```rust
// isel.rs:742-783
match val.annotation {
    Some(Annotation::Signed(8)) | Some(Annotation::Unsigned(8)) => MovsxB,
    Some(Annotation::Signed(16)) | Some(Annotation::Unsigned(16)) => MovsxW,
    Some(Annotation::Signed(32)) | Some(Annotation::Unsigned(32)) => MovsxD,
    _ => MovsxD,  // BUG: wrong for non-standard widths like u17
}
```

### Required fix

Annotations are semantic guarantees on the value range. This means some extend operations
are no-ops depending on the source annotation's signedness:

| Source annotation | Operation | Lowering |
|---|---|---|
| `:u<N>` | zext | no-op (value already in `[0, 2^N-1]`, upper bits are 0) |
| `:u<N>` | sext | `shl reg, (64-N); sar reg, (64-N)` |
| `:s<N>` | sext | no-op (value already in signed range, upper bits are sign-extended) |
| `:s<N>` | zext | `and reg, (1 << N) - 1` |

For standard widths (8/16/32), native movsx/movzx instructions can still be used as an
optimization. For non-standard widths (e.g., 17, 13), the shift/mask sequences above are
required.

Two possible approaches:

1. **Legalization pass before isel**: normalize all non-standard widths to legal machine
   widths (8/16/32/64), inserting explicit mask/shift operations in the IR.
2. **Handle in isel directly**: emit shift/mask sequences for non-standard widths in
   Sext/Zext, use native movsx/movzx for standard widths.

### Note

This is not currently triggered in practice because `rustc_codegen_tuffy` only emits
standard widths from Rust types. But the IR spec allows arbitrary bit-widths in annotations,
so isel must handle them correctly.

## Subtasks

- Decide between legalization pass vs. in-isel handling
- Implement correct Sext/Zext lowering for non-standard bit-widths
- Add tests for non-standard annotation widths (e.g., u17, s13)

## Affected Modules

- `tuffy_target_x86/src/isel.rs` — Sext/Zext instruction selection
