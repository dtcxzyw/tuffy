# Tuffy IR Language Reference

This document is the reference manual for the Tuffy IR, the intermediate representation
used by the tuffy compiler. It describes the type system, instruction set, control flow
structure, and textual format of the IR.

> **Status**: This spec describes the currently implemented IR. Features described in
> the [IR Design RFC](RFCs/202602/ir-design.md) but not yet implemented are noted as
> *planned*.
>
> **Source of truth**: The formal definitions in Lean 4 (`lean/TuffyLean/IR/`) are
> authoritative. This spec is a human-readable description that must conform to the
> Lean definitions. When in doubt, consult the Lean code.

## Introduction

Tuffy IR is a typed, SSA-based intermediate representation organized around a
hierarchical control flow graph with SESE (Single Entry, Single Exit) regions.

Key design principles:

- **Infinite precision integers** — no fixed bit widths; range constraints via assert nodes
- **Block arguments** instead of PHI nodes (Cranelift/MLIR style)
- **Hierarchical CFG** — loops and structured control flow are explicit SESE regions
- **Poison-only UB model** — no `undef`; only `poison`
- **Single data structure** — one IR across all compilation stages

## Table of Contents

- [Type System](#type-system)
- [Values](#values)
- [Functions](#functions)
- [Regions](#regions)
- [Basic Blocks](#basic-blocks)
- [Instructions](#instructions)
  - [Constants](#constants)
  - [Arithmetic](#arithmetic)
  - [Floating Point Arithmetic](#floating-point-arithmetic)
  - [Comparison](#comparison)
  - [Value Annotations](#value-annotations)
  - [Memory Operations](#memory-operations)
  - [Atomic Operations](#atomic-operations)
  - [Type Conversion](#type-conversion)
  - [Pointer Operations](#pointer-operations)
  - [Function Calls](#function-calls)
  - [Terminators](#terminators)
- [Text Format](#text-format)
- [Planned Features](#planned-features)

## Type System

Tuffy IR has a minimal type system. All aggregate types (structs, enums, arrays) are
decomposed into scalars before entering the IR.

### `int`

Infinite precision integer. No fixed bit width, no signedness. Arithmetic on `int` is
mathematical: `add 3, 5` produces `8` with no possibility of overflow.

Range constraints are expressed via [value annotations](#value-annotations) rather than
the type itself. The decision of sign-extension vs zero-extension is deferred to
instruction selection.

### `byte(N)`

Raw memory data of N bytes. Distinct from integers. The byte type preserves pointer
fragments and supports per-byte poison tracking. Loads and stores operate on byte types.

*Note: `byte` is defined in the type system but not yet used by any implemented
instructions. Memory operations currently use `int` directly.*

### `ptr(AS)`

Pointer with address space AS. Address space 0 is the default. Pointers carry provenance
(allocation ID + offset). Different address spaces may have different pointer sizes and
semantics.

### `float`

IEEE 754 floating point type. Variants: `bf16` (bfloat16), `f16` (half), `f32` (single),
`f64` (double). Floating point operations (`fadd`, `fsub`, etc.) operate on float-typed
values. The result type of a float operation matches the operand float width.

## Values

A value in tuffy IR is one of four kinds, as defined in Lean (`TuffyLean.IR.Value`):

| Kind | Description |
|------|-------------|
| `int(v)` | An infinite precision integer with mathematical value `v` |
| `bytes(bs)` | A sequence of [abstract bytes](#abstract-bytes) |
| `ptr(p)` | A pointer with provenance (allocation ID + offset) |
| `poison` | A poison value — the result of undefined behavior |

### Abstract Bytes

Each byte in memory is represented as an abstract byte (`TuffyLean.IR.AbstractByte`):

| State | Description |
|-------|-------------|
| `bits(val)` | A concrete byte value (0–255) |
| `ptrFragment(allocId, index)` | The `index`-th byte of a pointer to allocation `allocId` |
| `uninit` | Uninitialized memory (a distinct abstract state, not "random bits") |
| `poison` | A poisoned byte |

### Pointers and Provenance

A pointer consists of an allocation ID and an integer offset
(`TuffyLean.IR.Pointer`). The allocation ID tracks which allocation the pointer
belongs to, enabling provenance-based alias analysis.

## Functions

A function is the top-level unit of compilation. It has a name, typed parameters,
an optional return type, and a body organized as a hierarchical CFG.

```
func @name(param_types...) -> ret_type {
  ...
}
```

- **Name**: prefixed with `@` in text format.
- **Parameters**: a list of types. Parameter values are created via `param` instructions.
- **Return type**: optional. Functions with no return type return `void`.
- **Body**: blocks and nested regions directly inside the function braces. The implicit
  top-level `function` region is not written in the text format.

## Regions

The CFG is organized as a tree of SESE (Single Entry, Single Exit) regions. Each
region contains an ordered sequence of basic blocks and child regions.

### Region Kinds

| Kind | Description |
|------|-------------|
| `function` | Top-level function region. Every function has exactly one. |
| `loop` | Loop region. The entry block is the loop header. Backedges use `continue`. |
| `plain` | Generic SESE region for structured control flow. |

### Nesting and Implicit Capture

Regions nest to form a tree. Values defined in an outer region are visible in inner
regions via implicit capture (VPlan style). There is no explicit capture list — the
live-in set is computed on demand.

```
func @example(int) -> int {
  bb0:
    v0 = iconst 10       // v0 defined in function body

  region loop {
    bb1(v1: int):
      v2 = add v1, v0    // v0 captured implicitly from outer scope
      ...
  }
}
```

### Loop Regions

A loop region's entry block is the loop header. The `continue` terminator transfers
control back to the loop header, passing new values for the header's block arguments.
Exiting a loop is done by branching to a block outside the loop region.

## Basic Blocks

A basic block is a straight-line sequence of instructions with no internal control flow.
Blocks are named `bb0`, `bb1`, etc. in text format.

### Block Arguments

Tuffy IR uses block arguments instead of PHI nodes to represent values that merge at
control flow join points. Block arguments are declared in the block header and receive
values from predecessor branches:

```
bb0:
  v0 = iconst 1
  br bb1(v0)

bb1(v1: int):       // v1 is a block argument
  ret v1
```

Each branch instruction (`br`, `brif`, `continue`) passes values to the target block's
arguments. The number and types of passed values must match the target block's argument
list.

### Instruction Ordering

Instructions within a block execute sequentially. The last instruction in a block must
be a terminator (`ret`, `br`, `brif`, `continue`, `region_yield`).

## Instructions

Every instruction produces a value (named `vN` in text format) and has a result type.
Terminators are not separated from regular instructions — they are simply the last
instruction in a block by convention.

### Constants

#### `iconst`

```
vN = iconst <immediate>
```

Produces an integer constant. The immediate is a signed 64-bit value in the Rust
implementation, but semantically represents a mathematical integer.

**Semantics**: `Value.int(immediate)`

#### `param`

```
vN = param <index>
```

References a function parameter by index (0-based). This is not a true constant but
creates a named value for the parameter within the instruction stream.

### Arithmetic

All integer arithmetic operates on mathematical integers with infinite precision.
There is no overflow. The formal semantics are defined in `TuffyLean.IR.Semantics`.

#### `add`

```
vN = add vA, vB
```

Integer addition. **Semantics**: `evalAdd(a, b) = a + b`

#### `sub`

```
vN = sub vA, vB
```

Integer subtraction. **Semantics**: `evalSub(a, b) = a - b`

#### `mul`

```
vN = mul vA, vB
```

Integer multiplication. **Semantics**: `evalMul(a, b) = a * b`

#### `div`

```
vN = div vA, vB
```

Integer division. Produces `poison` if `vB` is zero. Signedness is a property of
operand annotations, not the operation itself — in the infinite precision integer
model, signed and unsigned division are mathematically identical.
**Semantics**: `evalDiv(a, b) = if b = 0 then poison else a / b`

#### `rem`

```
vN = rem vA, vB
```

Integer remainder. Produces `poison` if `vB` is zero. Signedness is a property of
operand annotations, not the operation itself.
**Semantics**: `evalRem(a, b) = if b = 0 then poison else a % b`

#### `and`

```
vN = and vA, vB
```

Bitwise AND on infinite precision two's complement integers.
**Semantics**: `evalAnd(a, b) = Int.land a b`

#### `or`

```
vN = or vA, vB
```

Bitwise OR on infinite precision two's complement integers.
**Semantics**: `evalOr(a, b) = Int.lor a b`

#### `xor`

```
vN = xor vA, vB
```

Bitwise XOR on infinite precision two's complement integers.
**Semantics**: `evalXor(a, b) = Int.xor a b`

#### `shl`

```
vN = shl vA, vB
```

Left shift. Produces `poison` if the shift amount `vB` is negative.
**Semantics**: `evalShl(a, b) = if b < 0 then poison else a <<< b`

#### `shr`

```
vN = shr vA, vB
```

Right shift. Produces `poison` if the shift amount `vB` is negative.
Signedness is a property of operand annotations, not the operation.
In infinite precision, logical and arithmetic right shift are identical.
**Semantics**: `evalShr(a, b) = if b < 0 then poison else a >>> b`

### Floating Point Arithmetic

Floating point operations operate on values of `float` type (`bf16`, `f16`, `f32`, `f64`).
The formal semantics use Lean 4's native `Float` type (IEEE 754 binary64) as a placeholder
model. The formal float model will be refined when full NaN payload and denormal semantics
are decided.

#### Rewrite flags

Binary floating-point arithmetic instructions (`fadd`, `fsub`, `fmul`, `fdiv`) may carry
optional **rewrite flags** that grant the optimizer permission to apply algebraic
transformations. These flags do not change the instruction's operational semantics — they
only widen the set of legal rewrites.

| Flag | Meaning |
|---|---|
| `reassoc` | Allow associativity / commutativity reordering |
| `contract` | Allow contraction (e.g., `a*b+c → fma(a,b,c)`) |

Flags appear between the opcode and the operands:

```
vN = fadd reassoc contract vA, vB
```

When no flags are present the instruction follows strict IEEE 754 semantics.
Mirrors `TuffyLean.IR.FpRewriteFlags`.

#### `fadd`

```
vN = fadd [flags] vA, vB
```

Floating point addition. **Semantics**: `evalFAdd(a, b) = a + b`

#### `fsub`

```
vN = fsub [flags] vA, vB
```

Floating point subtraction. **Semantics**: `evalFSub(a, b) = a - b`

#### `fmul`

```
vN = fmul [flags] vA, vB
```

Floating point multiplication. **Semantics**: `evalFMul(a, b) = a * b`

#### `fdiv`

```
vN = fdiv [flags] vA, vB
```

Floating point division. **Semantics**: `evalFDiv(a, b) = a / b`

#### `fneg`

```
vN = fneg vA
```

Floating point negation. **Semantics**: `evalFNeg(a) = -a`

#### `fabs`

```
vN = fabs vA
```

Floating point absolute value. **Semantics**: `evalFAbs(a) = Float.abs a`

#### `copysign`

```
vN = copysign vMag, vSign
```

Produce a value with the magnitude of `vMag` and the sign bit of `vSign`.
**Semantics**: `evalCopySign(mag, sign) = if sign < 0 then -(abs mag) else abs mag`

### Comparison

#### `icmp`

```
vN = icmp.<pred> vA, vB
```

Integer comparison. Returns an `int` value: 1 if the comparison is true, 0 otherwise.

Predicates:

| Predicate | Description |
|-----------|-------------|
| `eq` | Equal |
| `ne` | Not equal |
| `lt` | Less than (signedness from annotation) |
| `le` | Less than or equal (signedness from annotation) |
| `gt` | Greater than (signedness from annotation) |
| `ge` | Greater than or equal (signedness from annotation) |

### Value Annotations

Range constraints and bit-level facts are encoded as annotations on value definitions
(result-side) and use edges (use-side), rather than as standalone instructions. See
[RFC: at-use-annotations](RFCs/202602/at-use-annotations.md) for the full design.

#### Annotation types

| Annotation | Meaning |
|---|---|
| `:s<N>` | Value is in signed N-bit range `[-2^(N-1), 2^(N-1)-1]` |
| `:u<N>` | Value is in unsigned N-bit range `[0, 2^N-1]` |
| `:known(<ternary>)` | Per-bit four-state constraint |
| `:nofpclass(<classes>)` | Float value must not belong to the listed FP classes |
| (none) | No constraint; unconstrained `int` |

Annotations are composable: `:s32:known(...)` applies both constraints simultaneously.

#### Known bits encoding

Each bit in a `known` annotation is one of four states:

| Symbol | Meaning |
|---|---|
| `0` | Bit is known to be 0 |
| `1` | Bit is known to be 1 |
| `?` | Unknown — bit is demanded but value not determined |
| `x` | Don't-care — bit is not demanded |

#### nofpclass

Constrains which IEEE 754 floating-point value classes a float value may belong to.
If the value falls into an excluded class, the result is `poison`. This is separate
from integer annotations (`:s<N>`, `:u<N>`) and mirrors LLVM's `nofpclass` attribute.

The 10 individual FP classes (mirroring LLVM's `FPClassTest`):

| Class | Description |
|---|---|
| `snan` | Signaling NaN |
| `qnan` | Quiet NaN |
| `ninf` | Negative infinity |
| `nnorm` | Negative normal |
| `nsub` | Negative subnormal |
| `nzero` | Negative zero |
| `pzero` | Positive zero |
| `psub` | Positive subnormal |
| `pnorm` | Positive normal |
| `pinf` | Positive infinity |

Convenience groups:

| Group | Expands to |
|---|---|
| `nan` | `snan qnan` |
| `inf` | `ninf pinf` |
| `zero` | `nzero pzero` |

Syntax:

```
v0:nofpclass(nan inf) = fadd v1, v2   // result must not be NaN or ±Inf
v1 = fsub v0:nofpclass(nzero), v2     // use-side: v0 must not be -0.0
```

Mirrors `TuffyLean.IR.FpClassMask`.

#### Result-side annotations

Declared on the value produced by an instruction. Violation causes the instruction
to produce `poison`.

```
v0:s32 = add v1, v2    // if true result outside [-2^31, 2^31-1], v0 is poison
```

#### Use-side annotations

Declared on an operand of a consuming instruction. Violation causes the consuming
instruction to produce `poison`. May be stronger than the result-side annotation.

```
v1 = foo v0:u8          // if v0 is outside [0, 255], foo produces poison
```

#### Function signature annotations

Function signatures carry annotations as ABI-level contracts:

```
func @add_i32(int:s32, int:s32) -> int:s32 { ... }
```

Parameter annotations are caller guarantees; return annotations are callee guarantees.

### Memory Operations

#### `load`

```
vN = load vPtr, <size>
```

Load `size` bytes from the address pointed to by `vPtr`. Returns a `bytes` value
(`List AbstractByte`). Memory access operates at the byte level only — the result
is raw bytes with no type interpretation. To obtain a typed value (integer, float),
use `bytecast` as a separate step.

**Semantics**: `evalLoad(mem, addr, size) = bytes [mem[addr], mem[addr+1], ..., mem[addr+size-1]]`

#### `store`

```
store vVal, vPtr
```

Store a `bytes` value (`List AbstractByte`) to the address pointed to by `vPtr`.
The operand `vVal` must be a bytes value. Does not produce a meaningful result value.

**Semantics**: `evalStore(mem, addr, bs) = mem[addr..addr+len(bs)] := bs`

#### `stack_slot`

```
vN = stack_slot <bytes>
```

Allocate `bytes` bytes on the stack. Returns a `ptr(0)` to the allocated memory.

### Atomic Operations

Atomic operations provide thread-safe memory access with explicit memory ordering
constraints. The formal semantics in Lean define sequential-only behavior; a formal
concurrency model (e.g., based on C11) is TBD.

#### Enumerations

**MemoryOrdering** — memory ordering constraints for atomic operations:

| Ordering | Description |
|----------|-------------|
| `relaxed` | No ordering constraints |
| `acquire` | Subsequent reads see writes from the releasing thread |
| `release` | Prior writes are visible to the acquiring thread |
| `acqrel` | Combined acquire + release |
| `seqcst` | Sequentially consistent total order |

**AtomicRmwOp** — read-modify-write operation kinds:

| Op | Description |
|----|-------------|
| `xchg` | Exchange (swap) |
| `add` | Integer addition |
| `sub` | Integer subtraction |
| `and` | Bitwise AND |
| `or` | Bitwise OR |
| `xor` | Bitwise XOR |

#### `load.atomic`

```
vN = load.atomic.<ordering> vPtr
```

Atomic load from pointer `vPtr` with the specified memory ordering.
**Semantics**: Sequentially equivalent to `evalLoad`.

#### `store.atomic`

```
store.atomic.<ordering> vVal, vPtr
```

Atomic store of `vVal` to pointer `vPtr` with the specified memory ordering.
Does not produce a meaningful result value.
**Semantics**: Sequentially equivalent to `evalStore`.

#### `rmw`

```
vN = rmw.<op>.<ordering> vPtr, vVal
```

Atomic read-modify-write. Atomically reads the value at `vPtr`, applies `<op>`
with `vVal`, writes the result back, and returns the original value.

#### `cmpxchg`

```
vN = cmpxchg.<success_ord>.<failure_ord> vPtr, vExpected, vDesired
```

Atomic compare-and-exchange. Atomically compares the value at `vPtr` with
`vExpected`; if equal, writes `vDesired`. Returns the old value regardless of
success. The caller uses `icmp` to determine whether the exchange succeeded.
`<success_ord>` applies on successful exchange; `<failure_ord>` applies on failure.

#### `fence`

```
fence.<ordering>
```

Memory fence. Establishes ordering constraints without accessing memory.
Does not produce a meaningful result value.

### Type Conversion

#### `bitcast`

```
vN = bitcast vA
```

Reinterpret the bits of `vA` as a different type. The result type is determined by
the instruction's type annotation.

#### `sext`

```
vN = sext vA, <bits>
```

Sign-extend `vA` to `bits` bits. Used during lowering to make bit widths explicit
for instruction selection.

#### `zext`

```
vN = zext vA, <bits>
```

Zero-extend `vA` to `bits` bits. Used during lowering to make bit widths explicit
for instruction selection.

#### `bytecast`

```
vN = bytecast vA
```

Convert between byte types and typed values. The source and target types determine
the conversion direction.

**`byte(N) → int`**: Interprets the bytes as a little-endian integer. The low
`N*8` bits of the result are determined by the byte contents; high bits are
**unspecified**. The caller must apply `zext` (zero-extend) or `sext`
(sign-extend) to obtain a fully determined value. `N` must be a multiple of 8
bits (i.e., the byte count is the type parameter directly).

**`byte(N) → float`**: Requires exact size match: `byte(4) → f32`,
`byte(8) → f64`. Size mismatch is ill-formed.

**`int → byte(N)`**: Truncates the integer to `N` bytes (little-endian).

**AbstractByte handling**: Each byte in the input is resolved independently:
- `bits(val)` → decoded as a concrete byte
- `poison` → the entire result is `poison`
- `uninit` → the entire result is `poison`
- `ptrFragment(allocId, index)` → ptrtoint semantics (extracts address byte)

### Pointer Operations

Pointer operations manipulate pointers with explicit provenance tracking. The formal
semantics are defined in `TuffyLean.IR.Semantics`.

#### `ptradd`

```
vN = ptradd vPtr, vOffset
```

Pointer addition. Offsets the pointer `vPtr` by `vOffset` bytes. The result preserves
the provenance of the base pointer.
**Semantics**: `evalPtrAdd(base, offset) = ptr { allocId = base.allocId, offset = base.offset + offset }`

#### `ptrdiff`

```
vN = ptrdiff vA, vB
```

Pointer difference. Computes the byte offset between two pointers. Both pointers must
belong to the same allocation; otherwise the result is `poison`.
**Semantics**: `evalPtrDiff(a, b) = if a.allocId = b.allocId then a.offset - b.offset else poison`

#### `ptrtoint`

```
vN = ptrtoint vPtr
```

Convert a pointer to an integer. The provenance is captured — the resulting integer
retains knowledge that it came from a pointer.
**Semantics**: `evalPtrToInt(p) = p.offset`

#### `ptrtoaddr`

```
vN = ptrtoaddr vPtr
```

Extract the address from a pointer, discarding provenance. Returns a plain integer
with no provenance information.
**Semantics**: `evalPtrToAddr(p) = p.offset`

#### `inttoptr`

```
vN = inttoptr vAddr
```

Create a pointer from an integer address. The resulting pointer has no valid
provenance (wildcard provenance).
**Semantics**: `evalIntToPtr(addr, allocId) = ptr { allocId, offset = addr }`

### Function Calls

#### `call`

```
vN = call vCallee(vArg0, vArg1, ...)
```

Call the function pointed to by `vCallee` with the given arguments. The result type
is the return type of the callee.

### Terminators

Terminators are instructions that end a basic block by transferring control flow.
By convention, they are the last instruction in a block.

#### `ret`

```
ret vA
ret
```

Return from the function. Optionally returns a value. A function with a return type
must return a value; a void function uses bare `ret`.

#### `br`

```
br bbN(vA, vB, ...)
br bbN
```

Unconditional branch to block `bbN`, passing values as block arguments.
If the target block has no arguments, the argument list is omitted.

#### `brif`

```
brif vCond, bbThen(args...), bbElse(args...)
brif vCond, bbThen, bbElse
```

Conditional branch. If `vCond` is nonzero, branches to `bbThen`; otherwise branches
to `bbElse`. Each target may receive block arguments.

#### `continue`

```
continue vA, vB, ...
continue
```

Loop backedge. Transfers control back to the entry block of the enclosing `loop`
region, passing values as the header block's arguments. Only valid inside a `loop`
region.

#### `region_yield`

```
region_yield vA, vB, ...
region_yield
```

Exit the enclosing region, yielding values to the parent region. Used for structured
control flow where a region produces result values.

#### `unreachable`

```
unreachable
```

Indicates that control flow should never reach this point. If executed, the behavior
is undefined (the optimizer may assume this path is dead).

#### `trap`

```
trap
```

Unconditionally abort execution. Used for runtime checks such as failed assertions
(e.g., division-by-zero guards). Unlike `unreachable`, reaching a `trap` is not UB —
it is a well-defined program abort.

## Text Format

Tuffy IR uses a Cranelift-inspired text format for human-readable output.

### Naming Conventions

| Entity | Format | Example |
|--------|--------|---------|
| Functions | `@name` | `@add`, `@factorial` |
| Values | `vN` | `v0`, `v1`, `v2` |
| Blocks | `bbN` | `bb0`, `bb1` |
| Regions | `region <kind>` | `region loop`, `region plain` |

Values are numbered sequentially (v0, v1, v2, ...) in region tree order. Within each
block, block arguments are numbered before instruction results.

### Grammar

```
function     ::= 'func' '@' name '(' param_list ')' ('->' type annotation)? '{' body '}'
param_list   ::= (type annotation (',' type annotation)*)?
body         ::= (block | region)*
region       ::= 'region' region_kind '{' region_body '}'
region_kind  ::= 'loop' | 'plain'
region_body  ::= (block | region)*
block        ::= block_header instruction*
block_header ::= 'bb' N block_args? ':'
block_args   ::= '(' block_arg (',' block_arg)* ')'
block_arg    ::= value ':' type
instruction  ::= (value annotation '=')? opcode operands
operand      ::= value annotation
annotation   ::= (':' range_ann)*
range_ann    ::= 's' N | 'u' N | 'known' '(' ternary ')'
ternary      ::= [01?x_]+
value        ::= 'v' N
type         ::= 'int' | 'byte' | 'ptr'
```

### Complete Example

A factorial function demonstrating nested regions, block arguments, and control flow:

```
func @factorial(int:s32) -> int:s32 {
  bb0:
    v0:s32 = param 0
    v1 = iconst 1
    v2 = iconst 1
    br bb1(v2, v1)

  region loop {
    bb1(v4: int, v5: int):
      v6 = icmp.le v5:s32, v0:s32
      brif v6, bb2, bb3

    bb2:
      v8 = mul v4, v5
      v9 = sub v5, v1
      continue v8, v9
  }

  bb3:
    ret v4:s32
}
```

## Planned Features

The following features are described in the [IR Design RFC](RFCs/202602/ir-design.md) but
are not yet implemented in the Rust codebase.

### Floating Point Semantics

The IR adopts IEEE 754-2008 as the floating-point semantics standard. Basic
operations (`fadd`, `fsub`, `fmul`, `fdiv`, `fneg`, `fabs`, `copysign`) are
implemented. Per-instruction rewrite flags (`reassoc`, `contract`) and float
value class constraints (`nofpclass`) are defined. Full NaN payload and denormal
semantics are still under discussion — the current Lean model uses Lean 4's
native `Float` type (IEEE 754 binary64) as a placeholder.

### Scalable Vector Types

Vector types parameterized by total bit-width, not element count. Element count is
derived: `count = total_bits / element_bits`. Scalable vectors use
`vscale × base_width`, where `vscale` is a runtime constant determined by hardware
(cf. SVE, RVV). Well-formedness: `total_bits % element_bits == 0` and lane count
must be a power of two. See the [scalable vector RFC](RFCs/202602/) (planned).

### Byte Type Operations

`bytecast` semantics are specified in [Type Conversion](#type-conversion). The Lean
formal definition and Rust implementation are not yet complete.

### Memory SSA

Memory dependencies encoded directly into the IR as memory version tokens on load/store
operations, enabling progressive refinement as alias analysis improves.

### Atomic Operations

Atomic operations (`load.atomic`, `store.atomic`, `rmw`, `cmpxchg`, `fence`) are
implemented with `MemoryOrdering` and `AtomicRmwOp` enumerations. See
[Atomic Operations](#atomic-operations). The formal concurrency model is TBD — current
Lean semantics define sequential behavior only.

### Control Flow Structuralization

Translation from rustc MIR to tuffy IR with automatic structuralization of loops and
branches into SESE regions. Irreducible control flow remains as flat CFG within a region.
