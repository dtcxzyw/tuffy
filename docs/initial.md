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
- Signedness and minimum required bitwidth are derived at use sites.
- `zext`/`sext`/`trunc` instructions are eliminated from the IR.
- Bitwise operations (and/or/xor/shift) are also defined on infinite precision integers.
- Instruction selection in the final stage derives concrete machine types from at-use analysis.

**Representation form (under discussion):**
- Candidates: SSA CFG, Sea of Nodes, E-graph, RVSDG
- E-graph and Sea of Nodes may be better fits given the infinite precision integer model and formal verification goals

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
