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
