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
- **load/store i128**: emits a single `load.16` / `store.16` IR instruction; the backend legalize pass splits it into two 8-byte operations.
- **load/store struct**: emits a single `load` / `store` with struct type; the backend legalize pass expands into per-word operations based on ABI rules.
- **function parameters**: struct parameters are represented as single IR values with struct type; the backend legalize pass splits them into multiple register-sized parameters according to the target ABI.
- Supports `dump-ir` via `-C llvm-args=dump-ir` for debugging IR output.

## Translation Conventions

When translating MIR constructs to tuffy IR, follow these principles:

- **Reference LLVM IR semantics** when uncertain about translation strategy. LLVM IR provides a well-documented, battle-tested model for lowering high-level constructs.
- **No special-case handling for specific examples.** Translation logic must be general and correct for all valid inputs, not tailored to pass particular test cases.
- Emit IR that accurately represents the semantics of the source construct, not IR that happens to work for a specific input.

## Testing

### Codegen Tests

Codegen tests verify MIR-to-IR translation correctness using CHECK annotations:

```rust
// compile-flags: -C opt-level=0
// CHECK: func @add(%a: int:s32, %b: int:s32) -> int:s32
// CHECK: v3:s32 = add v1:s32, v2:s32

pub fn add(a: i32, b: i32) -> i32 { a + b }
```

Run with: `tests/run-codegen-tests.sh`

CHECK lines use exact string matching (not regex). Each CHECK line must appear in the generated IR output.

### Test Requirements

When modifying MIR-to-IR translation modules in `mir_to_ir/`, add corresponding regression tests to `tests/codegen/`:

- Organize tests by module: changes to `intrinsic.rs` → tests in `tests/codegen/intrinsic/`
- Keep test cases minimal and focused on the specific behavior being tested
- Use meaningful names for all identifiers (functions, variables, types)
- Each test must include CHECK annotations verifying the expected IR output

After modifying `mir_to_ir/` modules, run `tests/run-codegen-tests.sh` to ensure no regressions. If tests fail, determine whether to update CHECK lines (if the new IR is correct) or fix the implementation (if the change introduced a bug).

## Error Policy

Unsupported MIR constructs (rvalue kinds, statement kinds, terminator kinds, intrinsics, place projections) must **not** be silently skipped or marked as unreachable. Instead:

- Use `trap()` to emit a runtime trap instruction for unsupported terminators and unhandled cases (e.g., `InlineAsm` without targets, `Resume`, `Yield`, etc.)
- Use `unimplemented!()` with a descriptive message for unsupported operations that should never occur in valid MIR
- When an error is hit, the correct response is to add a concrete implementation for that construct — not to suppress the error

## Dependencies

- `tuffy_ir` — IR definitions
- `tuffy_target` — backend trait
- `tuffy_codegen` — target-dispatching facade
- `num-bigint` — arbitrary-precision integer constants
- `rustc_*` — rustc internal crates (via `#![feature(rustc_private)]`)
