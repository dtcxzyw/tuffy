# Move align parameter from MemCopy/MemMove/MemSet to pointer annotation

- Status: Draft
- Created: 2026-03-07
- Completed: N/A
- Parent: N/A

## Description

### Problem

Currently, `MemCopy`, `MemMove`, and `MemSet` instructions take `align` as an independent parameter:

```rust
MemCopy(Operand, Operand, Operand, u32, Operand)
//                                 ^^^ align parameter
MemMove(Operand, Operand, Operand, u32, Operand)
MemSet(Operand, Operand, Operand, u32, Operand)
```

This design has fundamental issues:

1. **Semantic inconsistency**: The same pointer can have different align values in different call sites, which is logically contradictory. Alignment is an inherent property of the address a pointer points to, not a property of the operation.

2. **Missing from semantics**: The Lean definitions (`evalMemCopy`, `evalMemMove`, `evalMemSet`) do not include align parameters, indicating align is not semantically necessary for correctness.

3. **Type system gap**: Alignment constraints cannot be enforced at the type level.

### Solution

Alignment should be a **pointer annotation**, not an instruction parameter. This treats alignment as what it fundamentally is: a constraint on the pointer's target address.

Extend the `Annotation` enum to include alignment:

```rust
pub enum Annotation {
    Signed(u32),
    Unsigned(u32),
    DontCare(u32),
    Align(u32),  // New: pointer alignment guarantee
}
```

Then remove align parameters from memory operations:

```rust
// Before
MemCopy(dst, src, count, align, mem_token)

// After
MemCopy(dst_with_align_annotation, src_with_align_annotation, count, mem_token)
```

### Benefits

1. **Logical consistency**: A pointer's alignment is declared once and applies everywhere it's used
2. **Type safety**: Alignment becomes part of the type system via annotations
3. **Simpler API**: Memory operations have fewer parameters
4. **Better optimization**: Alignment information propagates naturally through SSA

## Subtasks

1. Extend `Annotation` enum with `Align(u32)` variant
2. Remove `align` parameter from `MemCopy`, `MemMove`, `MemSet` in Rust IR
3. Update instruction display/parsing to handle align annotations on pointer operands
4. Update codegen backend to extract alignment from pointer annotations
5. Update all test cases using these instructions
6. Verify Lean semantics remain consistent (already correct)

## Affected Modules

- `tuffy_ir/src/types.rs` — Add `Align` variant to `Annotation` enum
- `tuffy_ir/src/instruction.rs` — Remove align parameter from memory bulk operations
- `tuffy_ir/src/display.rs` — Update instruction formatting
- `tuffy_ir/src/builder.rs` — Update builder API
- `rustc_codegen_tuffy/` — Update MIR-to-IR translation for memory intrinsics
- `tuffy_target_x86/` — Update instruction selection to extract align from annotations
- Test files using MemCopy/MemMove/MemSet
