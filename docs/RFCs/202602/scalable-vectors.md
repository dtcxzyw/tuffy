# Feature Name: `scalable-vectors`

- Status: Draft
- Created: 2026-02-09
- Completed: N/A

## Summary

Replace the element-count-parameterized vector type `vec<vscale x N x T>` with a
bit-width-parameterized vector type `vec<W>` (fixed) / `vec<vscale x W>` (scalable),
where `W` is the total bit-width of the vector. Element count is derived as
`W / element_bits`, consistent with tuffy's infinite precision integer model where
bit-width is an annotation property, not a type property.

## Motivation

In tuffy IR, integers have infinite precision and bit-width is expressed through
annotations (`:s32`, `:u16`, etc.). Annotations are always droppable — they constrain
but never determine semantics. This creates a tension with the current vector type
design `vec<vscale x N x T>`, which bakes element count into the type:

1. **Element count requires knowing element size.** `vec<1 x 4 x int>` says "4
   integers" but doesn't specify how wide each integer is. The physical vector
   register width is unknown until isel reads annotations. This makes the type
   incomplete without annotations, violating the principle that annotations are
   droppable.

2. **Hardware thinks in bit-widths.** SSE is 128-bit, AVX is 256-bit, AVX-512 is
   512-bit, SVE is `vscale × 128`-bit. The fundamental hardware parameter is total
   register width, not element count.

3. **Google Highway validates this model.** Highway's `ScalableTag<T, N>` computes
   lane count from `N / sizeof(T)`, where `N` is a byte count (bit-width / 8). The
   library is designed around total width as the primary parameter.

A bit-width-parameterized vector type aligns with all three concerns.

## Guide-level explanation

### Vector type syntax

```
vec<128>              -- fixed 128-bit vector
vec<256>              -- fixed 256-bit vector
vec<vscale x 128>     -- scalable vector, vscale × 128 bits
```

The single parameter `W` is the total bit-width. Element count is derived from
context: when operating on 32-bit integers, `vec<128>` has 4 lanes; when operating
on 64-bit floats, it has 2 lanes.

### Element width comes from annotations

Since tuffy IR integers are infinite precision, the element width is determined by
annotations on the vector operands, not by the vector type itself:

```
v0:vec<128> = vec.add v1:vec<128>:s32, v2:vec<128>:s32
    -- 4 lanes of 32-bit signed integers

v3:vec<128> = vec.add v4:vec<128>:u8, v5:vec<128>:u8
    -- 16 lanes of 8-bit unsigned integers
```

Dropping the annotation relaxes the constraint but doesn't change the vector width.
The vector is still 128 bits; the element interpretation is simply unconstrained.

### Scalable vectors

For hardware with runtime-determined vector width (ARM SVE, RISC-V RVV):

```
v0:vec<vscale x 128> = vec.add v1:vec<vscale x 128>:s32, v2:vec<vscale x 128>:s32
```

Here `vscale` is a runtime constant. On a machine with `vscale=4`, this is a 512-bit
vector with 16 lanes of 32-bit integers.

### Fractional vectors

Half-width or quarter-width vectors are expressed naturally as smaller bit-widths:

```
vec<64>               -- half of vec<128>
vec<vscale x 64>      -- half of vec<vscale x 128>
```

No special "fractional vector" mechanism is needed.

## Reference-level explanation

### Type definition

```
VectorType :=
  | Fixed { width : Nat }           -- fixed-width vector
  | Scalable { baseWidth : Nat }    -- vscale × baseWidth
```

### Well-formedness constraints

A vector operation `vec.op v:vec<W>:ann` is well-formed when:

1. **Bit-width is positive**: `W > 0`
2. **Byte-aligned**: `W % 8 == 0`
3. **Divisible by element width**: When an annotation specifies element width `E`,
   `W % E == 0`
4. **Power-of-two lane count**: `W / E` must be a power of two
5. **Scalable base width**: For `vec<vscale x B>`, the same constraints apply to `B`

Constraints 3–4 are checked only when annotations are present. Without annotations,
the vector is a raw bag of bits with no lane structure.

### Interaction with annotations

Annotations on vector values specify per-element constraints:

| Annotation | Meaning on `vec<W>` |
|---|---|
| `:s32` | Each of the `W/32` elements is in `[-2^31, 2^31-1]` |
| `:u8` | Each of the `W/8` elements is in `[0, 255]` |
| (none) | No per-element constraint; raw bit vector |

### Instruction selection

Isel reads the annotation to determine the machine instruction:

| IR | Annotation | x86 (128-bit) | ARM NEON |
|---|---|---|---|
| `vec.add` | `:s32` | `paddd` | `add.4s` |
| `vec.add` | `:u8` | `paddb` | `add.16b` |
| `vec.shr` | `:s32` | `psrad` | `sshr.4s` |
| `vec.shr` | `:u32` | `psrld` | `ushr.4s` |

### Vector operations

All vector operations from the IR design RFC remain unchanged in semantics. The only
change is the type parameter: `vec<vscale x N x T>` becomes `vec<W>` or
`vec<vscale x W>`.

Operations that need element width (e.g., `vec.shr` for signed vs unsigned shift)
read it from operand annotations, exactly as scalar `shr` does today.

### Memory operations

Vector loads and stores specify the vector width:

```
v0:vec<128> = vec.load %ptr, %mask
vec.store %v:vec<128>, %ptr, %mask
```

The byte count transferred is `W / 8`. Element interpretation for scatter/gather
index computation comes from annotations.

## Drawbacks

1. **Annotation-dependent semantics for lane count.** Without an annotation, the
   lane structure is unknown. Operations like `vec.extract %v, %idx` need to know
   the element width to compute the extraction offset. This could be addressed by
   requiring annotations on such operations.

2. **Diverges from LLVM.** LLVM uses `<N x T>` with explicit element count and type.
   Tooling and documentation that references LLVM's model may cause confusion.

## Rationale and alternatives

### Why bit-width over element count?

- **Consistency**: Matches the infinite precision integer model where bit-width is
  an annotation, not a type property.
- **Hardware alignment**: Maps directly to physical register widths.
- **Simplicity**: One parameter instead of two (count + element type).

### Alternative: Keep `vec<vscale x N x T>`

The LLVM-style approach. Rejected because it requires baking element type into the
vector type, which conflicts with tuffy's annotation-based design. It also creates
redundancy: `vec<1 x 4 x int>:s32` encodes "4 elements" in the type and "32-bit" in
the annotation, but `4 × 32 = 128` is the actual hardware parameter.

### Alternative: `vec<N x T>` with `T = b<W>`

Use byte types as elements: `vec<4 x b32>`. This avoids the infinite-precision
problem but introduces a second parameterization axis. Rejected in favor of the
simpler single-parameter model.

## Prior art

- **Google Highway**: `ScalableTag<T, N>` where `N` is a byte count. Lane count is
  `N / sizeof(T)`. Validates the bit-width-first approach.
- **ARM SVE**: Vectors are `vscale × 128` bits. Element width is encoded in
  instructions, not in the register type.
- **RISC-V RVV**: `VLEN` is the register bit-width. `SEW` (selected element width)
  is set per-instruction via `vtype`.
- **LLVM**: `<vscale x N x T>` with explicit element count and type. The most
  widely used model but designed for a typed IR, not an infinite-precision one.

## Unresolved questions

- **Lane-manipulating operations**: `vec.extract`, `vec.insert`, and `vec.shuffle`
  need element width to compute offsets. Should they require annotations, or should
  they take an explicit element-width immediate?
- **Mixed-width operations**: How to express widening/narrowing operations (e.g.,
  multiply 16-bit elements producing 32-bit results)?
- **Mask type**: Should masks be `vec<W>` with 1-bit-per-element (annotation `:u1`),
  or a separate predicate type?

## Future possibilities

- **Tuple types**: `vec<128> × 2` for multi-register operations (ld2/st2 on ARM).
- **Matrix types**: `mat<R x C x W>` for AMX/SME-style matrix operations.
- **Automatic vectorization**: The bit-width model simplifies cost modeling since
  the hardware register width is directly available.
