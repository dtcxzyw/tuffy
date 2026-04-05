# Type System

Tuffy IR has a minimal type system supporting scalar types and aggregate types (structs, arrays).
Aggregate types flow through the IR as single values; ABI-specific decomposition is handled by
the backend legalize pass.

## `unit`

Zero-sized unit type. Represents Rust's `()`. Used as the result type for terminators
and other instructions that do not produce a meaningful value.

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

To convert `bool` to `int`, use `select cond, 1, 0`. To convert `int` to `bool`, use
`icmp.ne val, 0`.

## `byte(N)`

Raw memory data of N bytes. Distinct from integers. The byte type preserves pointer
fragments and supports per-byte poison tracking. Loads and stores operate on byte types.

*Note: `byte` is defined in the type system but not yet used by any implemented
instructions. Memory operations currently use `int` directly.*

## `ptr(AS)`

Pointer with address space AS. Address space 0 is the default. Pointers carry provenance
(allocation ID + offset). Different address spaces may have different pointer sizes and
semantics.

## `mem`

Abstract memory state token for Memory SSA. Memory tokens flow through the function as
regular SSA values, making memory dependencies explicit. The entry block receives the
initial memory state as a block parameter of type `mem`; `ret` carries the final `mem`
token as an operand.

Memory-producing operations (`store`, `call`, `fence`, atomics) consume a `mem` token
and produce a new one. Plain `load` consumes a `mem` token but does not produce one.
At CFG join points, memory versions merge via regular block parameters of type `mem`.

## `float`

IEEE 754 floating point type. Variants: `bf16` (bfloat16), `f16` (half), `f32` (single),
`f64` (double), `f128` (quadruple). Floating point operations (`fadd`, `fsub`, etc.) operate
on float-typed values. The result type of a float operation matches the operand float width.

## `vec(VT)`

Vector type parameterized by total bit-width. Variants: `vec<N>` (fixed-width, e.g., 128 for SSE),
`vec<vscale x N>` (scalable, e.g., SVE, RVV). Element count is derived from the bit-width and
element size.

## `struct{T0, T1, ...}`

Struct type with field types. Represents a heterogeneous aggregate with indexed fields.
Struct values flow through the IR as single SSA values. Field access uses `extractvalue` and
`insertvalue` instructions with index paths.

**Padding must be explicitly represented** in the struct type. Padding fields are typically
represented as `[byte(N); M]` (array of N-byte chunks) or `byte(N)` for individual padding bytes.

Example: `struct{int, [byte(8); 1], bool}` is a struct with an int field, 8 bytes of padding,
and a bool field. The padding is explicit and must be accounted for in field indices.

The backend legalize pass expands struct values into register-sized pieces according to the
target ABI (e.g., System V AMD64 ABI rules for struct passing and return).

## `[T; N]`

Array type with element type T and count N. Represents a homogeneous aggregate with N elements
of type T. Array values flow through the IR as single SSA values. Element access uses
`extractvalue` and `insertvalue` instructions with index paths.

Example: `[int; 10]` is an array of 10 integers.

The backend legalize pass expands array values into register-sized pieces according to the
target ABI.
