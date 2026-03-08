# Instructions

Every instruction produces a value (named `vN` in text format) and has a result type.
Terminators are not separated from regular instructions — they are simply the last
instruction in a block by convention.

## Constants

### `iconst`

```
vN = iconst <immediate>
```

Produces an integer constant. The immediate is an arbitrary-precision integer,
matching the Lean spec's `Int` type.

**Semantics**: `Value.int(immediate)`

### `param`

```
vN = param <index>
vN = param %name
```

References a function parameter by index (0-based) or by name. When source-level
parameter names are available, the named form `param %name` is used in the text
format. The internal representation always uses the numeric ABI index. This is not
a true constant but creates a named value for the parameter within the instruction
stream.

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

### `clz`

```
vN = clz.<width> vA
```

Count leading zeros in an n-bit representation. Returns the number of consecutive
zero bits starting from the most significant bit. Produces `poison` if `width` is 0.
**Semantics**: `evalCountLeadingZeros(a, width) = if width = 0 then poison else clzN(width, a mod 2^width)`

### `ctz`

```
vN = ctz vA
```

Count trailing zeros: returns the number of consecutive zero bits starting from
the least significant bit. Produces `poison` if `vA` is zero or negative.
**Semantics**: `evalCountTrailingZeros(a) = if a ≤ 0 then poison else ctz(a)`

### `bswap`

```
vN = bswap.<bytes> vA
```

Byte-swap: reverses the byte order of the low `bytes` bytes. Produces `poison`
if `bytes` is 0.
**Semantics**: `evalBswap(a, bytes) = if bytes = 0 then poison else byteswap(a mod 2^(8*bytes))`

### `bitreverse`

```
vN = bitreverse.<bits> vA
```

Bit-reverse: reverses the bit order of the low `bits` bits. Produces `poison`
if `bits` is 0.
**Semantics**: `evalBitReverse(a, bits) = if bits = 0 then poison else bitreverse(a mod 2^bits)`

### `rotl`

```
vN = rotl.<width> vA, vAmt
```

Rotate left by `vAmt` positions in a `width`-bit field. Produces `poison` if
`width` is 0.
**Semantics**: `evalRotateLeft(a, amt, width) = if width = 0 then poison else rotate_left(a mod 2^width, amt mod width)`

### `rotr`

```
vN = rotr.<width> vA, vAmt
```

Rotate right by `vAmt` positions in a `width`-bit field. Produces `poison` if
`width` is 0.
**Semantics**: `evalRotateRight(a, amt, width) = if width = 0 then poison else rotate_right(a mod 2^width, amt mod width)`

### `merge`

```
vN = merge.<width> vA, vB
```

Replace the low `width` bits of `vA` with the low `width` bits of `vB`, producing a
single integer. Produces `poison` if `width` is 0.
**Semantics**: `evalMerge(a, b, width) = if width = 0 then poison else (a with low width bits cleared) | (b AND (2^width - 1))`

### `split`

```
vHi, vLo = split.<width> vA
```

Decompose `vA` at bit position `width`. Produces two results:
- `vLo` = the low `width` bits of `vA` (zero-extended)
- `vHi` = `vA` right-shifted by `width` bits

Produces `poison` if `width` is 0. This is a multi-result instruction.
**Semantics**: `evalSplitHi(a, width) = a >>> width`, `evalSplitLo(a, width) = a mod 2^width`

### `clmul`

```
vN = clmul vA, vB
```

Carry-less multiplication (polynomial multiplication over GF(2)). Multiplies `vA`
and `vB` using XOR instead of addition for accumulating partial products. Produces
`poison` if either operand is negative.
**Semantics**: `evalClmul(a, b) = if a < 0 ∨ b < 0 then poison else clmulNat(a, b)`

### `uadd_sat`

```
vN = uadd_sat.<width> vA, vB
```

Unsigned saturating addition in `width` bits. Clamps result to `[0, 2^width-1]`.
Produces `poison` if `width` is 0.
**Semantics**: `evalSaturatingAdd(a, b, width) = if width = 0 then poison else min(a + b, 2^width - 1)`

### `usub_sat`

```
vN = usub_sat.<width> vA, vB
```

Unsigned saturating subtraction in `width` bits. Clamps result to `[0, 2^width-1]`.
Produces `poison` if `width` is 0.
**Semantics**: `evalSaturatingSub(a, b, width) = if width = 0 then poison else max(a - b, 0)`

### `sadd_sat`

```
vN = sadd_sat.<width> vA, vB
```

Signed saturating addition in `width` bits. Clamps result to `[-2^(width-1), 2^(width-1)-1]`.
Produces `poison` if `width` is 0.
**Semantics**: `evalSignedSaturatingAdd(a, b, width) = if width = 0 then poison else clamp(a + b, -2^(width-1), 2^(width-1)-1)`

### `ssub_sat`

```
vN = ssub_sat.<width> vA, vB
```

Signed saturating subtraction in `width` bits. Clamps result to `[-2^(width-1), 2^(width-1)-1]`.
Produces `poison` if `width` is 0.
**Semantics**: `evalSignedSaturatingSub(a, b, width) = if width = 0 then poison else clamp(a - b, -2^(width-1), 2^(width-1)-1)`

### `sadd_overflow`

```
vSum, vOverflow = sadd_overflow.<width> vA, vB
```

Signed addition with overflow detection in `width` bits. Returns two results:
the wrapped sum and a boolean overflow flag. Produces `poison` if `width` is 0.
**Semantics**: `evalSAddOverflow(a, b, width) = (wrapped_sum, overflow_flag)`

### `uadd_overflow`

```
vSum, vOverflow = uadd_overflow.<width> vA, vB
```

Unsigned addition with overflow detection in `width` bits. Returns two results:
the wrapped sum and a boolean overflow flag. Produces `poison` if `width` is 0.
**Semantics**: `evalUAddOverflow(a, b, width) = (wrapped_sum, overflow_flag)`

### `ssub_overflow`

```
vDiff, vOverflow = ssub_overflow.<width> vA, vB
```

Signed subtraction with overflow detection in `width` bits. Returns two results:
the wrapped difference and a boolean overflow flag. Produces `poison` if `width` is 0.
**Semantics**: `evalSSubOverflow(a, b, width) = (wrapped_diff, overflow_flag)`

### `usub_overflow`

```
vDiff, vOverflow = usub_overflow.<width> vA, vB
```

Unsigned subtraction with overflow detection in `width` bits. Returns two results:
the wrapped difference and a boolean overflow flag. Produces `poison` if `width` is 0.
**Semantics**: `evalUSubOverflow(a, b, width) = (wrapped_diff, overflow_flag)`

### `smul_overflow`

```
vProd, vOverflow = smul_overflow.<width> vA, vB
```

Signed multiplication with overflow detection in `width` bits. Returns two results:
the wrapped product and a boolean overflow flag. Produces `poison` if `width` is 0.
**Semantics**: `evalSMulOverflow(a, b, width) = (wrapped_prod, overflow_flag)`

### `umul_overflow`

```
vProd, vOverflow = umul_overflow.<width> vA, vB
```

Unsigned multiplication with overflow detection in `width` bits. Returns two results:
the wrapped product and a boolean overflow flag. Produces `poison` if `width` is 0.
**Semantics**: `evalUMulOverflow(a, b, width) = (wrapped_prod, overflow_flag)`

### `min`

```
vN = min vA, vB
```

Integer minimum. Returns the smaller of two integers.
**Semantics**: `evalMin(a, b) = if a ≤ b then a else b`

### `max`

```
vN = max vA, vB
```

Integer maximum. Returns the larger of two integers.
**Semantics**: `evalMax(a, b) = if a ≥ b then a else b`

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

### `fminnum`

```
vN = fminnum vA, vB
```

IEEE 754-2008 minNum operation. NaN-suppressing: if one operand is qNaN and the other is numeric, returns the numeric value. **Semantics**: `evalFMinNum(a, b)`

### `fmaxnum`

```
vN = fmaxnum vA, vB
```

IEEE 754-2008 maxNum operation. NaN-suppressing: if one operand is qNaN and the other is numeric, returns the numeric value. **Semantics**: `evalFMaxNum(a, b)`

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

### `frem`

```
vN = frem vA, vB
```

Floating point remainder (IEEE 754 fmod). Computes the remainder of `vA / vB`
with truncation toward zero.
**Semantics**: `evalFRem(a, b) = a - trunc(a/b) * b`

### `fcmp`

```
vN = fcmp.<pred> vA, vB
```

Floating point comparison. Returns a `bool` value: `true` if the comparison holds,
`false` otherwise.

Predicates:

| Predicate | Description |
|-----------|-------------|
| `false` | Always false |
| `oeq` | Ordered equal |
| `ogt` | Ordered greater than |
| `oge` | Ordered greater than or equal |
| `olt` | Ordered less than |
| `ole` | Ordered less than or equal |
| `one` | Ordered not equal |
| `ord` | Ordered (neither operand is NaN) |
| `uno` | Unordered (either operand is NaN) |
| `ueq` | Unordered or equal |
| `ugt` | Unordered or greater than |
| `uge` | Unordered or greater than or equal |
| `ult` | Unordered or less than |
| `ule` | Unordered or less than or equal |
| `une` | Unordered or not equal |
| `true` | Always true |

Ordered predicates return `false` if either operand is NaN. Unordered predicates
return `true` if either operand is NaN.

**Semantics**: `evalFCmp(op, a, b) = bool(op(a, b))`

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

All memory operations participate in Memory SSA. Operations that modify memory state
consume a `mem` token and produce a new one. Plain loads consume a `mem` token but do
not produce one. See [types.md](types.md#mem) for details on the `mem` type.

### `load`

```
vN = load vPtr, vMem -> <type>
```

Load a value of the specified type from the address pointed to by `vPtr`. Takes a `mem` token as input
(MemoryUse). Returns a data value only — does not produce a new `mem` token.

The loaded type must be one of: `int`, `float` (any variant), `vec` (any variant), or `byte(N)`.
Array and struct types are not supported — use `byte(N)` and convert explicitly instead.

**Semantics**: `evalLoad(mem, addr, ty) = value of type ty loaded from mem[addr..]`

### `store`

```
vN = store vVal, vPtr, vMem
```

Store a value to the address pointed to by `vPtr`. Takes a `mem` token as input
(MemoryDef) and produces a new `mem` token as its result.

The stored value type must be one of: `int`, `float` (any variant), `vec` (any variant), or `byte(N)`.
Array and struct types are not supported — convert to `byte(N)` explicitly before storing.

**Semantics**: `evalStore(mem, addr, val) = mem with val written at addr`

### `stack_slot`

```
vN = stack_slot <bytes>
```

Allocate `bytes` bytes on the stack. Returns a `ptr(0)` to the allocated memory.

### `memcpy`

```
vN = memcpy vDst, vSrc, vCount, align=<N>, vMem
```

Copy `vCount` bytes from `vSrc` to `vDst`. The source and destination regions must
not overlap (non-overlapping memcpy semantics). `align` is the minimum alignment hint
for both pointers (must be a power of two). Takes a `mem` token as input (MemoryDef)
and produces a new `mem` token.

**Semantics**: `evalMemCopy(mem, dst, src, count) = evalStore(mem, dst, readBytes(mem, src, count))`

### `memmove`

```
vN = memmove vDst, vSrc, vCount, align=<N>, vMem
```

Copy `vCount` bytes from `vSrc` to `vDst`. Unlike `memcpy`, overlapping regions are
handled correctly: all source bytes are read before any destination bytes are written.
`align` is the minimum alignment hint for both pointers. Takes a `mem` token as input
(MemoryDef) and produces a new `mem` token.

**Semantics**: `evalMemMove(mem, dst, src, count) = evalStore(mem, dst, readBytes(mem, src, count))`
(bytes are captured from `mem` before the store, making overlap safe)

### `memset`

```
vN = memset vDst, vVal, vCount, align=<N>, vMem
```

Fill `vCount` bytes at `vDst` with the byte value `vVal` (low 8 bits). `align` is
the minimum alignment hint for the destination pointer. Takes a `mem` token as input
(MemoryDef) and produces a new `mem` token.

**Semantics**: `evalMemSet(mem, dst, val, count) = evalStore(mem, dst, replicate(count, val & 0xFF))`

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
vM, vN = load.atomic.<ordering> vPtr, vMem
```

Atomic load from pointer `vPtr` with the specified memory ordering. Takes a `mem`
token as input (MemoryDef) and produces two results: a new `mem` token and the
loaded data value.

### `store.atomic`

```
vN = store.atomic.<ordering> vVal, vPtr, vMem
```

Atomic store of `vVal` to pointer `vPtr` with the specified memory ordering.
Takes a `mem` token as input (MemoryDef) and produces a new `mem` token.

### `rmw`

```
vM, vN = rmw.<op>.<ordering> vPtr, vVal, vMem
```

Atomic read-modify-write. Atomically reads the value at `vPtr`, applies `<op>`
with `vVal`, writes the result back. Takes a `mem` token as input (MemoryDef) and
produces two results: a new `mem` token and the original value.

### `cmpxchg`

```
vM, vN = cmpxchg.<success_ord>.<failure_ord> vPtr, vExpected, vDesired, vMem
```

Atomic compare-and-exchange. Atomically compares the value at `vPtr` with
`vExpected`; if equal, writes `vDesired`. Takes a `mem` token as input (MemoryDef)
and produces two results: a new `mem` token and the old value. The caller uses
`icmp` to determine whether the exchange succeeded.
`<success_ord>` applies on successful exchange; `<failure_ord>` applies on failure.

### `fence`

```
vN = fence.<ordering> vMem
```

Memory fence. Establishes ordering constraints without accessing memory.
Takes a `mem` token as input (MemoryDef) and produces a new `mem` token.

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

### `symbol_addr`

```
vN = symbol_addr @name
```

Load the address of a named symbol (function or static data). The `@name` refers
to an entry in the module's symbol table. The result type is `ptr`.

This instruction makes function calls and static data references self-contained
in the IR — the callee of a `call` is a value produced by `symbol_addr` rather
than a side-channel mapping.

**Semantics**: Produces a pointer to the symbol identified by `@name`.

### `call`

```
vM = call vCallee(vArg0, vArg1, ...), vMem
vM, vN = call vCallee(vArg0, vArg1, ...), vMem -> <ret_type>
```

Call the function pointed to by `vCallee` with the given arguments. Takes a `mem`
token as input (MemoryDef). For void calls, produces a single `mem` token result.
For non-void calls, produces two results: a new `mem` token and the return value.

## Terminators

Terminators are instructions that end a basic block by transferring control flow.
By convention, they are the last instruction in a block.

### `ret`

```
ret vA, vMem
ret vMem
```

Return from the function. Takes a `mem` token as the final memory state operand.
Optionally returns a data value. A function with a return type must return a value;
a void function uses `ret vMem` with only the mem token.

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
