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
| `Ne` | `icmp.ne` | `fcmp.une` |
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

## Statements

MIR statements represent actions within a basic block.

| MIR Statement | Translation |
|---------------|-------------|
| `Assign(place, rvalue)` | Translate rvalue, store result to place |
| `StorageLive(local)` | No-op (ignored) |
| `StorageDead(local)` | No-op (ignored) |
| `SetDiscriminant { place, variant }` | `store` tag value to discriminant field |
| `Nop` | No-op |
| `Intrinsic(intrinsic)` | See Intrinsics section |

**StorageLive/StorageDead**: These are lifetime markers used by MIR for stack slot reuse and borrow checking. At the IR level, they are ignored since Tuffy IR uses explicit stack slots and does not perform lifetime-based optimizations.

**SetDiscriminant**: Writes the discriminant (tag) value for an enum variant. For single-variant enums, this is a no-op. For multi-variant enums:
- Computes the tag value based on the variant index and tag encoding (Direct or Niche)
- Calculates the address of the discriminant field (base + offset)
- Emits a `store` instruction to write the tag value

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
| `InlineAsm` | Pattern-based translation (see below) |
| `UnwindResume` | `call _Unwind_Resume` + `unreachable` |
| `UnwindTerminate` | `call panic_cannot_unwind` + `trap` |

**SwitchInt**: Multi-way branch lowered to a binary decision tree using nested `brif` instructions.

**InlineAsm**: Inline assembly is handled via pattern recognition, not general-purpose execution. The `select_unpredictable` pattern (`cmovnz`/`cmovne` + `cmovz`/`cmove`) is translated to `icmp` + `select`. Other patterns use identity copies or zero-initialization of outputs.

**UnwindResume**: Loads the exception pointer from the landing-pad slot, calls `_Unwind_Resume` to resume stack unwinding, then emits `unreachable`.

**UnwindTerminate**: Resolves and calls `core::panicking::panic_cannot_unwind`, then emits `trap` as a safety backstop.

## Type Conversions

| MIR Cast | Tuffy IR |
|----------|----------|
| Integer extension (signed) | `sext` |
| Integer extension (unsigned) | `zext` |
| Integer truncation | Annotation change |
| Float to signed int | `fp_to_si` (saturating) |
| Float to unsigned int | `fp_to_ui` (saturating) |
| Signed int to float | `si_to_fp` |
| Unsigned int to float | `ui_to_fp` |
| Float to float (widen/narrow) | `fp_convert` |
| Pointer to int | `ptrtoint` |
| Int to pointer | `inttoptr` |
| FnPtr to ptr | `symbol_addr` |
| Ptr to ptr | Bitwise move |
| Transmute | Via temporary `stack_slot` + `store`/`load` |

**Float to int**: Follows Rust's saturating semantics — NaN converts to 0, out-of-range values clamp to the target type's MIN/MAX. For 128-bit targets, converts to 64-bit first then extends.

**Int to float**: Narrow integers (< 64 bits) are sign/zero-extended before conversion to ensure correct results.

**Transmute**: Reinterprets bit patterns via a temporary stack slot. Stores the source value, then loads it as the target type.

## Aggregate Construction

`Rvalue::Aggregate` constructs tuples, structs, closures, and enums.

**Strategy**: Allocates a `stack_slot` with the aggregate's size, then stores each field at its computed offset via `ptradd` + `store`.

- **Tuples/Structs**: Direct field-by-field storage at layout-computed offsets.
- **Enums**: After storing variant fields, writes the discriminant via `write_enum_tag()` (a `store` to the tag field using Direct or Niche encoding).
- **Closures/Coroutines**: Stores captured variables; initializes the state discriminant to 0.
- **Fat pointers within aggregates**: Stores data pointer at offset 0 and metadata at offset +8.

## Discriminant Reads

`Rvalue::Discriminant` reads an enum's discriminant value.

Three cases based on enum layout:

- **Single variant** (`Variants::Single`): Returns a constant (`iconst` of the discriminant value).
- **Direct tag** (`TagEncoding::Direct`): Loads the tag field via `ptradd` (if offset ≠ 0) + `load`.
- **Niche encoding** (`TagEncoding::Niche`): Loads the niche field, then decodes via arithmetic (`sub` for relative index, `icmp` for range check, `select` for final discriminant). Option-like enums (1 niche variant at offset 0) use a simplified `icmp.eq` + `select`.

## Not Yet Implemented

The following MIR operations are not yet translated to Tuffy IR:

- **Tail calls**: `TerminatorKind::TailCall`
- **Coroutines**: `Yield`, `CoroutineDrop`

These operations either require additional IR support or are Rust-specific features that don't map cleanly to a low-level IR.
