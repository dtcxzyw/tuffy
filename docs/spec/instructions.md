# Instructions

Every instruction produces a value (named `vN` in text format) and has a result type.
Terminators are not separated from regular instructions — they are simply the last
instruction in a block by convention.

## Constants

### `iconst`

```
vN = iconst <immediate>
```

Produces an integer constant. The immediate is a signed 64-bit value in the Rust
implementation, but semantically represents a mathematical integer.

**Semantics**: `Value.int(immediate)`

### `param`

```
vN = param <index>
```

References a function parameter by index (0-based). This is not a true constant but
creates a named value for the parameter within the instruction stream.

## Arithmetic

All integer arithmetic operates on mathematical integers with infinite precision.
There is no overflow. The formal semantics are defined in `TuffyLean.IR.Semantics`.

### `add`

```
vN = add vA, vB
```

Integer addition. **Semantics**: `evalAdd(a, b) = a + b`

### `sub`

```
vN = sub vA, vB
```

Integer subtraction. **Semantics**: `evalSub(a, b) = a - b`

### `mul`

```
vN = mul vA, vB
```

Integer multiplication. **Semantics**: `evalMul(a, b) = a * b`

### `div`

```
vN = div vA, vB
```

Integer division. Produces `poison` if `vB` is zero. Signedness is a property of
operand annotations, not the operation itself — in the infinite precision integer
model, signed and unsigned division are mathematically identical.
**Semantics**: `evalDiv(a, b) = if b = 0 then poison else a / b`

### `rem`

```
vN = rem vA, vB
```

Integer remainder. Produces `poison` if `vB` is zero. Signedness is a property of
operand annotations, not the operation itself.
**Semantics**: `evalRem(a, b) = if b = 0 then poison else a % b`

### `and`

```
vN = and vA, vB
```

Bitwise AND on infinite precision two's complement integers.
**Semantics**: `evalAnd(a, b) = Int.land a b`

### `or`

```
vN = or vA, vB
```

Bitwise OR on infinite precision two's complement integers.
**Semantics**: `evalOr(a, b) = Int.lor a b`

### `xor`

```
vN = xor vA, vB
```

Bitwise XOR on infinite precision two's complement integers.
**Semantics**: `evalXor(a, b) = Int.xor a b`

### `shl`

```
vN = shl vA, vB
```

Left shift. Produces `poison` if the shift amount `vB` is negative.
**Semantics**: `evalShl(a, b) = if b < 0 then poison else a <<< b`

### `shr`

```
vN = shr vA, vB
```

Right shift. Produces `poison` if the shift amount `vB` is negative.
Signedness is a property of operand annotations, not the operation.
In infinite precision, logical and arithmetic right shift are identical.
**Semantics**: `evalShr(a, b) = if b < 0 then poison else a >>> b`

### `count_ones`

```
vN = count_ones vA
```

Population count: returns the number of set bits in the binary representation
of `vA`. Produces `poison` if `vA` is negative.
**Semantics**: `evalCountOnes(a) = if a < 0 then poison else popcount(a)`

## Floating Point Arithmetic

Floating point operations operate on values of `float` type (`bf16`, `f16`, `f32`, `f64`).
The formal semantics use Lean 4's native `Float` type (IEEE 754 binary64) as a placeholder
model. The formal float model will be refined when full NaN payload and denormal semantics
are decided.

### Rewrite flags

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

### `fadd`

```
vN = fadd [flags] vA, vB
```

Floating point addition. **Semantics**: `evalFAdd(a, b) = a + b`

### `fsub`

```
vN = fsub [flags] vA, vB
```

Floating point subtraction. **Semantics**: `evalFSub(a, b) = a - b`

### `fmul`

```
vN = fmul [flags] vA, vB
```

Floating point multiplication. **Semantics**: `evalFMul(a, b) = a * b`

### `fdiv`

```
vN = fdiv [flags] vA, vB
```

Floating point division. **Semantics**: `evalFDiv(a, b) = a / b`

### `fneg`

```
vN = fneg vA
```

Floating point negation. **Semantics**: `evalFNeg(a) = -a`

### `fabs`

```
vN = fabs vA
```

Floating point absolute value. **Semantics**: `evalFAbs(a) = Float.abs a`

### `copysign`

```
vN = copysign vMag, vSign
```

Produce a value with the magnitude of `vMag` and the sign bit of `vSign`.
**Semantics**: `evalCopySign(mag, sign) = if sign < 0 then -(abs mag) else abs mag`

## Comparison

### `icmp`

```
vN = icmp.<pred> vA, vB
```

Integer comparison. Returns a `bool` value: `true` if the comparison holds, `false`
otherwise.

Predicates:

| Predicate | Description |
|-----------|-------------|
| `eq` | Equal |
| `ne` | Not equal |
| `lt` | Less than (signedness from annotation) |
| `le` | Less than or equal (signedness from annotation) |
| `gt` | Greater than (signedness from annotation) |
| `ge` | Greater than or equal (signedness from annotation) |

**Semantics**: `evalICmp(op, a, b) = bool(op(a, b))`

### `select`

```
vN = select vCond, vTrue, vFalse
```

Conditional select. If `vCond` is `true`, produces `vTrue`; otherwise produces `vFalse`.
The condition must be of type `bool`. The result type matches the type of `vTrue`/`vFalse`.

**Semantics**: `evalSelect(cond, tv, fv) = if cond then tv else fv`

### `bool_to_int`

```
vN = bool_to_int vA
```

Convert a `bool` to an `int`: `true` → 1, `false` → 0.

**Semantics**: `evalBoolToInt(b) = if b then 1 else 0`

## Value Annotations

Range constraints and bit-level facts are encoded as annotations on value definitions
(result-side) and use edges (use-side), rather than as standalone instructions. See
[RFC: at-use-annotations](../RFCs/202602/at-use-annotations.md) for the full design.

### Annotation types

| Annotation | Meaning |
|---|---|
| `:s<N>` | Value is in signed N-bit range `[-2^(N-1), 2^(N-1)-1]` |
| `:u<N>` | Value is in unsigned N-bit range `[0, 2^N-1]` |
| `:known(<ternary>)` | Per-bit four-state constraint |
| `:nofpclass(<classes>)` | Float value must not belong to the listed FP classes |
| (none) | No constraint; unconstrained `int` |

Annotations are composable: `:s32:known(...)` applies both constraints simultaneously.

### Known bits encoding

Each bit in a `known` annotation is one of four states:

| Symbol | Meaning |
|---|---|
| `0` | Bit is known to be 0 |
| `1` | Bit is known to be 1 |
| `?` | Unknown — bit is demanded but value not determined |
| `x` | Don't-care — bit is not demanded |

### nofpclass

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

### Result-side annotations

Declared on the value produced by an instruction. Violation causes the instruction
to produce `poison`.

```
v0:s32 = add v1, v2    // if true result outside [-2^31, 2^31-1], v0 is poison
```

### Use-side annotations

Declared on an operand of a consuming instruction. Violation causes the consuming
instruction to produce `poison`. May be stronger than the result-side annotation.

```
v1 = foo v0:u8          // if v0 is outside [0, 255], foo produces poison
```

### Function signature annotations

Function signatures carry annotations as ABI-level contracts:

```
func @add_i32(int:s32, int:s32) -> int:s32 { ... }
```

Parameter annotations are caller guarantees; return annotations are callee guarantees.

## Memory Operations

### `load`

```
vN = load vPtr, <size>
```

Load `size` bytes from the address pointed to by `vPtr`. Returns a `bytes` value
(`List AbstractByte`). Memory access operates at the byte level only — the result
is raw bytes with no type interpretation. To obtain a typed value (integer, float),
use `bytecast` as a separate step.

**Semantics**: `evalLoad(mem, addr, size) = bytes [mem[addr], mem[addr+1], ..., mem[addr+size-1]]`

### `store`

```
store vVal, vPtr
```

Store a `bytes` value (`List AbstractByte`) to the address pointed to by `vPtr`.
The operand `vVal` must be a bytes value. Does not produce a meaningful result value.

**Semantics**: `evalStore(mem, addr, bs) = mem[addr..addr+len(bs)] := bs`

### `stack_slot`

```
vN = stack_slot <bytes>
```

Allocate `bytes` bytes on the stack. Returns a `ptr(0)` to the allocated memory.

## Atomic Operations

Atomic operations provide thread-safe memory access with explicit memory ordering
constraints. The formal semantics in Lean define sequential-only behavior; a formal
concurrency model (e.g., based on C11) is TBD.

### Enumerations

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

### `load.atomic`

```
vN = load.atomic.<ordering> vPtr
```

Atomic load from pointer `vPtr` with the specified memory ordering.
**Semantics**: Sequentially equivalent to `evalLoad`.

### `store.atomic`

```
store.atomic.<ordering> vVal, vPtr
```

Atomic store of `vVal` to pointer `vPtr` with the specified memory ordering.
Does not produce a meaningful result value.
**Semantics**: Sequentially equivalent to `evalStore`.

### `rmw`

```
vN = rmw.<op>.<ordering> vPtr, vVal
```

Atomic read-modify-write. Atomically reads the value at `vPtr`, applies `<op>`
with `vVal`, writes the result back, and returns the original value.

### `cmpxchg`

```
vN = cmpxchg.<success_ord>.<failure_ord> vPtr, vExpected, vDesired
```

Atomic compare-and-exchange. Atomically compares the value at `vPtr` with
`vExpected`; if equal, writes `vDesired`. Returns the old value regardless of
success. The caller uses `icmp` to determine whether the exchange succeeded.
`<success_ord>` applies on successful exchange; `<failure_ord>` applies on failure.

### `fence`

```
fence.<ordering>
```

Memory fence. Establishes ordering constraints without accessing memory.
Does not produce a meaningful result value.

## Type Conversion

### `bitcast`

```
vN = bitcast vA
```

Reinterpret the bits of `vA` as a different type. The result type is determined by
the instruction's type annotation.

### `sext`

```
vN = sext vA, <bits>
```

Sign-extend `vA` to `bits` bits. Used during lowering to make bit widths explicit
for instruction selection.

### `zext`

```
vN = zext vA, <bits>
```

Zero-extend `vA` to `bits` bits. Used during lowering to make bit widths explicit
for instruction selection.

### `bytecast`

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

## Pointer Operations

Pointer operations manipulate pointers with explicit provenance tracking. The formal
semantics are defined in `TuffyLean.IR.Semantics`.

### `ptradd`

```
vN = ptradd vPtr, vOffset
```

Pointer addition. Offsets the pointer `vPtr` by `vOffset` bytes. The result preserves
the provenance of the base pointer.
**Semantics**: `evalPtrAdd(base, offset) = ptr { allocId = base.allocId, offset = base.offset + offset }`

### `ptrdiff`

```
vN = ptrdiff vA, vB
```

Pointer difference. Computes the byte offset between two pointers. Both pointers must
belong to the same allocation; otherwise the result is `poison`.
**Semantics**: `evalPtrDiff(a, b) = if a.allocId = b.allocId then a.offset - b.offset else poison`

### `ptrtoint`

```
vN = ptrtoint vPtr
```

Convert a pointer to an integer. The provenance is captured — the resulting integer
retains knowledge that it came from a pointer.
**Semantics**: `evalPtrToInt(p) = p.offset`

### `ptrtoaddr`

```
vN = ptrtoaddr vPtr
```

Extract the address from a pointer, discarding provenance. Returns a plain integer
with no provenance information.
**Semantics**: `evalPtrToAddr(p) = p.offset`

### `inttoptr`

```
vN = inttoptr vAddr
```

Create a pointer from an integer address. The resulting pointer has no valid
provenance (wildcard provenance).
**Semantics**: `evalIntToPtr(addr, allocId) = ptr { allocId, offset = addr }`

## Function Calls

### `call`

```
vN = call vCallee(vArg0, vArg1, ...)
```

Call the function pointed to by `vCallee` with the given arguments. The result type
is the return type of the callee.

## Terminators

Terminators are instructions that end a basic block by transferring control flow.
By convention, they are the last instruction in a block.

### `ret`

```
ret vA
ret
```

Return from the function. Optionally returns a value. A function with a return type
must return a value; a void function uses bare `ret`.

### `br`

```
br bbN(vA, vB, ...)
br bbN
```

Unconditional branch to block `bbN`, passing values as block arguments.
If the target block has no arguments, the argument list is omitted.

### `brif`

```
brif vCond, bbThen(args...), bbElse(args...)
brif vCond, bbThen, bbElse
```

Conditional branch. The condition `vCond` must be of type `bool`. If `true`, branches
to `bbThen`; otherwise branches to `bbElse`. Each target may receive block arguments.

### `continue`

```
continue vA, vB, ...
continue
```

Loop backedge. Transfers control back to the entry block of the enclosing `loop`
region, passing values as the header block's arguments. Only valid inside a `loop`
region.

### `region_yield`

```
region_yield vA, vB, ...
region_yield
```

Exit the enclosing region, yielding values to the parent region. Used for structured
control flow where a region produces result values.

### `unreachable`

```
unreachable
```

Indicates that control flow should never reach this point. If executed, the behavior
is undefined (the optimizer may assume this path is dead).

### `trap`

```
trap
```

Unconditionally abort execution. Used for runtime checks such as failed assertions
(e.g., division-by-zero guards). Unlike `unreachable`, reaching a `trap` is not UB —
it is a well-defined program abort.
