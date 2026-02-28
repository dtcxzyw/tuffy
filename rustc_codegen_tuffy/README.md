# rustc_codegen_tuffy

Rustc codegen backend that translates MIR into tuffy IR.

## Overview

This crate implements `CodegenBackend` from `rustc_codegen_ssa`, plugging Tuffy into the Rust compiler as an alternative code generation backend. It is built as a `dylib` and loaded at runtime:

```
rustc +nightly -Z codegen-backend=path/to/librustc_codegen_tuffy.so input.rs
```

This crate is **not** part of the Cargo workspace — it has its own `Cargo.toml` and `target/` directory.

## Architecture

### `lib.rs` — Backend Entry Point

Implements `CodegenBackend` for `TuffyCodegenBackend`:

- Iterates over `MonoItem`s (functions, statics, global ASM).
- Translates each function's MIR into tuffy IR via `mir_to_ir`.
- Delegates to `CodegenSession` for machine code generation and object file emission.
- Handles allocator shim generation and entry point synthesis.

### `mir_to_ir/` — MIR-to-IR Translation

The core translation layer, organized into submodules by concern:

| Module           | Purpose                                              |
|------------------|------------------------------------------------------|
| `mod.rs`         | Top-level function translation and block traversal   |
| `ctx.rs`         | Translation context (value maps, type caches, state) |
| `types.rs`       | Rust type → tuffy IR type mapping                    |
| `rvalue.rs`      | Rvalue translation (binops, unops, casts, aggregates)|
| `statement.rs`   | Statement translation (assign, storage, intrinsics)  |
| `terminator.rs`  | Terminator translation (return, branch, switch, call)|
| `call.rs`        | Function call ABI handling and argument passing      |
| `constant.rs`    | Constant evaluation and literal translation          |
| `intrinsic.rs`   | Rust intrinsic function lowering                     |

## Boundary Rule

This crate is the **sole boundary** between rustc and the Tuffy compiler infrastructure. All Rust-specific semantics, ABI conventions, MIR quirks, and language-level workarounds must be fully resolved here before emitting tuffy IR.

The downstream crates (`tuffy_ir`, `tuffy_opt`, `tuffy_target`, `tuffy_target_x86`, `tuffy_codegen`, etc.) are language-agnostic. They must never contain Rust-specific logic, special cases, or workarounds. If a Rust construct cannot be directly expressed in tuffy IR, this crate is responsible for lowering it into a valid IR representation.

## Key Design Decisions

- Uses `tuffy_codegen::AbiMetadataBox` to communicate ABI details (secondary returns, wide returns) to the backend without target coupling.
- Handles i128/u128 types through annotation-based legalization rather than type splitting at the IR level.
- Supports `dump-ir` via `-C llvm-args=dump-ir` for debugging IR output.

## Dependencies

- `tuffy_ir` — IR definitions
- `tuffy_target` — backend trait
- `tuffy_codegen` — target-dispatching facade
- `num-bigint` — arbitrary-precision integer constants
- `rustc_*` — rustc internal crates (via `#![feature(rustc_private)]`)
