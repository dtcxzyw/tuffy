# tuffy_ir

Core intermediate representation for the Tuffy compiler.

The Lean 4 definitions in `lean/TuffyLean/IR/` are the **source of truth**. This crate is the Rust implementation that must conform to those definitions.

## Type System

All types are defined in `types.rs`:

- `Int` — infinite-precision integer (no fixed bitwidth). Signedness is expressed through annotations, not the type itself.
- `Bool` — distinct boolean type (not an integer alias).
- `Unit` — zero-sized type for Rust's `()`.
- `Byte(n)` — raw memory data of `n` bytes with per-byte poison tracking.
- `Ptr(as)` — pointer with address space.
- `Float(ft)` — IEEE 754 floating point (`BF16`, `F16`, `F32`, `F64`, `F128`).
- `Vec(vt)` — vector type parameterized by total bit-width (fixed or scalable).
- `Mem` — abstract memory state token for MemSSA.

## Annotations

Annotations (`Annotation`) constrain value ranges at definition or use sites:

- `Signed(n)` — value in `[-2^(n-1), 2^(n-1)-1]`
- `Unsigned(n)` — value in `[0, 2^n-1]`

Violation at a definition site produces poison. Violation at a use site causes the consuming instruction to produce poison. This design separates bitwidth from the type system — `Int` is always infinite-precision, and finite-width semantics are expressed through annotations.

## Hierarchical CFG

The CFG is organized as a tree of SESE (Single Entry, Single Exit) regions (`function.rs`):

- `Region` — contains an ordered sequence of `CfgNode`s (blocks or nested regions).
- `RegionKind` — `Function` (top-level), `Loop` (backedge via `Continue`), or `Plain`.
- `BasicBlock` — holds a range of instructions. Block arguments replace PHI nodes.
- Cross-region value references use implicit capture (VPlan style).

## Value References

All references are `u32` indices into arenas (`value.rs`), enabling arena-based storage and serialization:

- `ValueRef` — tagged index: bit 31 distinguishes block args from instruction results; bit 30 distinguishes primary from secondary results.
- `BlockRef`, `RegionRef`, `InstRef` — typed indices into their respective arenas.

## Instructions

Instructions are defined in `instruction.rs` as the `Op` enum. Categories include:

- **Arithmetic**: `Add`, `Sub`, `Mul`, `Div`, `Rem`, `Min`, `Max`, saturating ops
- **Bitwise**: `And`, `Or`, `Xor`, `Shl`, `Shr`, rotates, `CountOnes`, `CountLeadingZeros`, `CountTrailingZeros`, `Bswap`
- **Comparison**: `ICmp` with predicates (`Eq`, `Ne`, `Lt`, `Le`, `Gt`, `Ge`)
- **Select**: `Select`, `BoolToInt`, `IntToBool`
- **Memory**: `Load`, `Store`, `StackSlot` (with MemSSA tokens)
- **Atomics**: `LoadAtomic`, `StoreAtomic`, `AtomicRmw`, `AtomicCmpXchg`, `Fence`
- **Floating point**: `FAdd`, `FSub`, `FMul`, `FDiv`, `FNeg`, `FAbs`, `CopySign`
- **Pointer**: `PtrAdd`, `PtrDiff`, `PtrToInt`, `PtrToAddr`, `IntToPtr`
- **Type conversion**: `Bitcast`, `Sext`, `Zext`, `FpToSi`, `FpToUi`, `SiToFp`, `UiToFp`, `FpConvert`
- **Control flow**: `Ret` (with optional secondary return operand), `Br`, `BrIf`, `Continue`, `RegionYield`, `Unreachable`, `Trap`
- **Other**: `Const` (arbitrary-precision), `BConst`, `Param`, `Call` (with optional cleanup label), `CallRet2`, `SymbolAddr`

Every instruction carries an `Origin` for debug info / provenance tracking.

## Module Structure

`Module` (`module.rs`) is the top-level container:

- Owns a `SymbolTable` (interned symbol names → `SymbolId`).
- Contains `Vec<Function>` and `Vec<StaticData>`.

## Key Modules

| Module         | Purpose                                      |
|----------------|----------------------------------------------|
| `builder.rs`   | Builder API for constructing IR (origin-mandatory) |
| `display.rs`   | Human-readable IR printer                    |
| `verifier.rs`  | Structural integrity and type-safety checks  |
| `types.rs`     | Type system and annotation definitions       |
| `instruction.rs` | Instruction / opcode definitions           |
| `function.rs`  | Function, BasicBlock, Region definitions     |
| `module.rs`    | Module and SymbolTable                       |
| `value.rs`     | Opaque arena-index handles                   |
