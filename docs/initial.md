# Initial Design Discussion

- Created: 2026-02-07

## Background

Tuffy is an experimental optimizing compiler written in Rust with LLM assistance. This document records the initial design discussion and key decisions made before implementation begins.

## Long-term Vision

Tuffy aims to be a production-grade, language-agnostic optimizing compiler backend:

- **Multi-language backend** — Serve as a codegen backend for multiple programming languages, not just Rust
- **Custom IR** — Design and implement a custom intermediate representation with optimization passes
- **Multi-platform** — Support multiple target architectures from the ground up
- **Balanced optimization** — Pursue both fast compilation and competitive runtime performance
- **Formal verification** — Provide formal correctness guarantees for optimization passes

## Short-term Milestone

The first milestone is `rustc_codegen_tuffy`, a codegen backend for rustc as an alternative to LLVM.

### Key Design Decisions

1. **Target platform**: Multi-platform architecture from the start, with x86-64 as the initial implementation target
2. **Optimization direction**: Balance between compilation speed and runtime performance (not exclusively pursuing either)
3. **IR design**: Custom IR — build our own intermediate representation, perform optimizations on it, then lower to machine code (rather than translating directly from rustc MIR)
4. **IR interpreter**: Implement a tuffy IR interpreter for testing and validation, similar to Miri

### IR Design

**Structure:**
- Single data structure for all stages — no separate SDAG/MIR like LLVM. Different stages have different normalization (legalization) constraints on the same IR, progressively lowering toward machine code.

**UB model (following Alive2):**
- Only `poison` — no `undef`. Simplifies semantics and avoids the well-known undef/poison confusion in LLVM.
- Uninitialized memory is allowed at the memory level, but values are either concrete or poison.

**Byte type (`b<N>`):**
- Introduced from the start, based on the LLVM byte type RFC. Represents raw memory data distinct from integers, with per-byte poison tracking. Enables sound memcpy lowering and load merging.

**Integer type:**
- A single `int` type with infinite precision — no fixed bitwidth (no i8/i32/i64).
- No overflow: arithmetic operations are mathematical (e.g., add is true addition).
- Range constraints via assert nodes: e.g., `assertsext(val, 32)` constrains a value to the 32-bit signed range, producing poison if violated.
- `zext`/`sext`/`trunc` instructions are eliminated from the IR.
- Bitwise operations (and/or/xor/shift) are also defined on infinite precision integers.

**At-use bit-level analysis (encoded in IR):**
- Each use edge carries bit-level annotations: which bits are demanded, and which bits are known to be 0 or 1.
- UB constraints (from assert nodes, memory operations, ABI boundaries) propagate backward through the IR, refining known bits on upstream values.
- This is analogous to LLVM's `KnownBits` and `DemandedBits` analyses, but promoted to first-class IR constructs rather than side analyses.
- Follows the "analysis is also a transformation" principle: analysis results are encoded directly into the IR, not stored in external tables.
- Instruction selection in the final stage derives concrete machine types from these at-use annotations.

**Representation form:**
- Hierarchical CFG with nested SESE regions. Loops and branches are explicitly represented as regions, not inferred from CFG back-edges.
- Region internals use traditional SSA basic blocks with fixed instruction ordering.
- Translation from rustc MIR requires control flow structuralization to recover nested regions from the flat CFG.
- Enables early loop optimizations (vectorization, LICM, unrolling) by preserving loop structure in the IR.
- Inspired by LLVM VPlan's hierarchical CFG and recipe-based transformation model.

**Memory model:**
- Abstract pointer model: pointer = allocation ID + offset, preserving full provenance.
- Two ptr-to-int instructions with distinct semantics:
  - `ptrtoint`: converts pointer to integer, capturing provenance. `inttoptr(ptrtoint(p))` is a safe roundtrip.
  - `ptrtoaddr`: extracts only the address portion, discarding provenance.
- Four-state byte representation: `Bits(u8) | PtrFragment(Pointer, n) | Uninit | Poison`. Each byte in memory is one of these states.
- Uninitialized memory (`Uninit`) is a distinct abstract state, not "random bits". Any operation on uninit values is UB (produces poison).
- Poison can exist at the byte level in memory, aligned with the per-byte poison tracking of the byte type.

### Testing Strategy

Validation and benchmarking will use the following targets (in progressive order):

1. **Internal unit tests** — small test cases for basic codegen correctness (arithmetic, control flow, function calls)
2. **`no_std` programs** — minimal programs to validate the backend without standard library dependencies
3. **serde** — widely used crate with heavy generics and macros, tests monomorphization and trait dispatch
4. **rustc test suite** — rustc's ui tests for broad correctness coverage
5. **ripgrep** — real-world CLI project for end-to-end correctness and performance comparison against LLVM backend
6. **clippy** — later-stage validation target due to tight coupling with rustc internals

## Notes

- Self-hosting is not a separate goal since tuffy is written in Rust — once the backend can compile Rust, self-hosting follows naturally
- JIT support and outperforming LLVM are not current goals but may be revisited later

## Target Abstraction

- Triple-based target identification, following LLVM's convention.
- TargetLowering design follows LLVM's approach (legal types, operation lowering, register classes).
- **Sub-method override via command-line**: individual TargetLowering properties (pointer size, legal integer widths, max vector width, etc.) can be overridden via `--target-override key=value` flags. This enables testing IR-level passes against specific target properties without implementing a full architecture backend.
- Cost model: deferred, not yet designed.

## IR Memory Layout

- **Encapsulation**: memory layout is an implementation detail, hidden behind a stable API. The rest of the compiler operates on opaque handles, not raw pointers. Layout can be changed without affecting pass code.
- **Arena + index**: IR nodes are allocated in arenas. References are `u32` indices (opaque handles), not pointers. Reduces reference size and enables serialization.
- **Contiguous instruction storage**: instructions within the same basic block are stored contiguously in the arena. Iterating a BB's instructions is a linear memory scan, not pointer chasing.
- **Tombstone + periodic compaction**: deleted instructions are marked as tombstones. Periodic compaction restores contiguity.
- **No SOA**: struct-of-arrays layout rejected; standard AOS with contiguous storage is sufficient.
