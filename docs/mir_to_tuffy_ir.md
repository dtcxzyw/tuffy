# MIR to Tuffy IR Translation

This document describes how Rust MIR (Mid-level Intermediate Representation) operations are translated to Tuffy IR instructions in the `rustc_codegen_tuffy` backend.

## Operands

MIR operands represent values used in operations. There are three kinds:

| MIR Operand | Translation |
|-------------|-------------|
| `Copy(place)` | Read value from place (may generate `load` if stack-allocated) |
| `Move(place)` | Read value from place (same as Copy at IR level) |
| `Constant(const)` | Translate to `iconst`, `bconst`, or `symbol_addr` |

**Copy vs Move**: The distinction between `Copy` and `Move` is enforced by MIR's borrow checker. At the IR level, both translate to reading the value from the place. For register-allocated locals, this is a direct value reference. For stack-allocated locals, this generates a `load` instruction.

**Constants**: Constant operands are translated based on their type:
- Integer/bool literals → `iconst` / `bconst`
- Function pointers → `symbol_addr`
- Static references → `symbol_addr` + optional offset

## Binary Operations

### Integer Arithmetic

| MIR BinOp | Tuffy IR | Result Annotation | Extension |
|-----------|----------|-------------------|-----------|
| `Add` | `add` | `:dontcare(N)` | `sext` (signed) / `zext` (unsigned) |
| `Sub` | `sub` | `:dontcare(N)` | `sext` (signed) / `zext` (unsigned) |
| `Mul` | `mul` | `:dontcare(N)` | `sext` (signed) / `zext` (unsigned) |
| `Div` | `div` | `:sN` / `:uN` | None |
| `Rem` | `rem` | `:sN` / `:uN` | None |
| `AddUnchecked` | `add` | `:sN` / `:uN` | None |
| `SubUnchecked` | `sub` | `:sN` / `:uN` | None |
| `MulUnchecked` | `mul` | `:sN` / `:uN` | None |

**Wrapping arithmetic** (`Add`, `Sub`, `Mul`): The IR instruction produces a result with `:dontcare(N)` annotation, then `sext` (for signed types) or `zext` (for unsigned types) is inserted to correctly interpret the low N bits. This prevents high bits from 64-bit operations bleeding through for sub-64-bit types.

**Unchecked arithmetic**: MIR guarantees no overflow, so the result uses `:sN` or `:uN` annotation directly without extension. The optimizer can assume the result is in range.

### Floating Point Arithmetic

| MIR BinOp | Tuffy IR |
|-----------|----------|
| `Add` | `fadd` |
| `Sub` | `fsub` |
| `Mul` | `fmul` |
| `Div` | `fdiv` |
| `Rem` | `frem` |

**Note**: Floating point operations do not use annotations or extensions.

### Overflow Detection

| MIR BinOp | Tuffy IR (Signed) | Tuffy IR (Unsigned) |
|-----------|-------------------|---------------------|
| `AddWithOverflow` | `sadd_overflow` | `uadd_overflow` |
| `SubWithOverflow` | `ssub_overflow` | `usub_overflow` |
| `MulWithOverflow` | `smul_overflow` | `umul_overflow` |

These return two values: the wrapped result and a boolean overflow flag.

### Bitwise Operations

| MIR BinOp | Tuffy IR | Result Annotation | Notes |
|-----------|----------|-------------------|-------|
| `BitAnd` | `and` | `:sN` / `:uN` | Direct passthrough |
| `BitOr` | `or` | `:sN` / `:uN` | Direct passthrough |
| `BitXor` | `xor` | `:sN` / `:uN` | Direct passthrough |
| `Shl` | `shl` | `:sN` / `:uN` | Shift amount masked to `% bit_width` |
| `ShlUnchecked` | `shl` | `:sN` / `:uN` | Shift amount masked to `% bit_width` |
| `Shr` | `shr` | `:sN` / `:uN` | Shift amount masked to `% bit_width` |
| `ShrUnchecked` | `shr` | `:sN` / `:uN` | Shift amount masked to `% bit_width` |

**Note**: Bitwise operations use the result annotation directly without extension. Shift operations mask the shift amount to `value & (bit_width - 1)` to match Rust semantics.

### Comparison Operations

| MIR BinOp | Tuffy IR (Integer) | Tuffy IR (Float) |
|-----------|-------------------|------------------|
| `Eq` | `icmp.eq` | `fcmp.oeq` |
| `Ne` | `icmp.ne` | `fcmp.one` |
| `Lt` | `icmp.lt` | `fcmp.olt` |
| `Le` | `icmp.le` | `fcmp.ole` |
| `Gt` | `icmp.gt` | `fcmp.ogt` |
| `Ge` | `icmp.ge` | `fcmp.oge` |
| `Cmp` | Special handling* | N/A |

**Note**: `Cmp` (three-way comparison) is lowered to a sequence of comparisons and selects that produce -1, 0, or 1.

### Pointer Operations

| MIR BinOp | Tuffy IR |
|-----------|----------|
| `Offset` | `ptradd` |

## Unary Operations

| MIR UnOp | Tuffy IR |
|----------|----------|
| `Not` | `xor v, -1` |
| `Neg` | `sub 0, v` (int) / `fneg v` (float) |

**Note**: Bitwise NOT is currently emulated using XOR with -1. A dedicated `not` instruction may be added in the future.

## Intrinsics

### Bit Manipulation

| MIR Intrinsic | Tuffy IR |
|---------------|----------|
| `ctpop` | `count_ones` |
| `ctlz` / `ctlz_nonzero` | `clz` |
| `cttz` / `cttz_nonzero` | `ctz` |
| `bswap` | `bswap` |
| `bitreverse` | `bitreverse` |
| `rotate_left` | `rotl` |
| `rotate_right` | `rotr` |

### Memory Operations

| MIR Intrinsic | Tuffy IR |
|---------------|----------|
| `copy_nonoverlapping` | `memcpy` |
| `write_bytes` | `memset` |
| `size_of` | `iconst` (compile-time constant) |
| `align_of` | `iconst` (compile-time constant) |

### Floating Point

| MIR Intrinsic | Tuffy IR |
|---------------|----------|
| `fabsf32` / `fabsf64` | `fabs` |
| `copysignf32` / `copysignf64` | `copysign` |
| `floorf32` / `floorf64` | External call |
| `ceilf32` / `ceilf64` | External call |
| `truncf32` / `truncf64` | External call |
| `sqrtf32` / `sqrtf64` | External call |

**Note**: Transcendental functions (floor, ceil, sqrt, etc.) are not yet implemented as IR instructions and are lowered to external function calls.

### Atomic Operations

| MIR Intrinsic | Tuffy IR |
|---------------|----------|
| `atomic_load` | `load.atomic` |
| `atomic_store` | `store.atomic` |
| `atomic_xchg` | `rmw.xchg` |
| `atomic_xadd` | `rmw.add` |
| `atomic_xsub` | `rmw.sub` |
| `atomic_and` | `rmw.and` |
| `atomic_or` | `rmw.or` |
| `atomic_xor` | `rmw.xor` |
| `atomic_cxchg` / `atomic_cxchgweak` | `cmpxchg` |
| `atomic_fence` | `fence` |

### Other Intrinsics

| MIR Intrinsic | Translation |
|---------------|-------------|
| `black_box` | Identity (no optimization barrier in IR) |
| `assume` | No-op |
| `is_val_statically_known` | `bconst false` |
| `assert_inhabited` | No-op (compile-time check) |
| `assert_zero_valid` | No-op (compile-time check) |

## Terminators

| MIR Terminator | Tuffy IR |
|----------------|----------|
| `Return` | `ret` |
| `Goto` | `br` |
| `SwitchInt` | Lowered to `brif` tree |
| `Call` | `call` |
| `Unreachable` | `unreachable` |
| `Drop` | Call to drop glue + `br` |
| `Assert` | `brif` + `trap` on failure |

**Note**: `SwitchInt` (multi-way branch) is lowered to a binary decision tree using nested `brif` instructions.

## Type Conversions

| MIR Cast | Tuffy IR |
|----------|----------|
| Integer extension (signed) | `sext` |
| Integer extension (unsigned) | `zext` |
| Integer truncation | Annotation change |
| Float to int | `bitcast` + annotation |
| Int to float | `bitcast` |
| Pointer to int | `ptrtoint` |
| Int to pointer | `inttoptr` |

## Not Yet Implemented

The following MIR operations are not yet translated to Tuffy IR:

- **Aggregate construction**: `Rvalue::Aggregate` (tuples, structs, enums)
- **Discriminant operations**: `Rvalue::Discriminant`, `StatementKind::SetDiscriminant`
- **Tail calls**: `TerminatorKind::TailCall`
- **Coroutines**: `Yield`, `CoroutineDrop`
- **Inline assembly**: `InlineAsm`
- **Unwind operations**: `UnwindResume`, `UnwindTerminate`

These operations either require additional IR support or are Rust-specific features that don't map cleanly to a low-level IR.
