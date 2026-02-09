# Type System

Tuffy IR has a minimal type system. All aggregate types (structs, enums, arrays) are
decomposed into scalars before entering the IR.

## `int`

Infinite precision integer. No fixed bit width, no signedness. Arithmetic on `int` is
mathematical: `add 3, 5` produces `8` with no possibility of overflow.

Range constraints are expressed via [value annotations](instructions.md#value-annotations) rather than
the type itself. The decision of sign-extension vs zero-extension is deferred to
instruction selection.

## `bool`

Boolean type with two values: `true` and `false`. Distinct from integers — boolean
logic is not conflated with integer arithmetic. Comparison instructions (`icmp`) return
`bool`, and control flow instructions (`brif`, `select`) require `bool` conditions.

To convert between `bool` and `int`, use `bool_to_int` (true → 1, false → 0). The
reverse conversion uses `icmp.ne val, 0`.

## `byte(N)`

Raw memory data of N bytes. Distinct from integers. The byte type preserves pointer
fragments and supports per-byte poison tracking. Loads and stores operate on byte types.

*Note: `byte` is defined in the type system but not yet used by any implemented
instructions. Memory operations currently use `int` directly.*

## `ptr(AS)`

Pointer with address space AS. Address space 0 is the default. Pointers carry provenance
(allocation ID + offset). Different address spaces may have different pointer sizes and
semantics.

## `float`

IEEE 754 floating point type. Variants: `bf16` (bfloat16), `f16` (half), `f32` (single),
`f64` (double). Floating point operations (`fadd`, `fsub`, etc.) operate on float-typed
values. The result type of a float operation matches the operand float width.
