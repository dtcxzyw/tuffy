# Build Commands

## Development Environment

Development uses VS Code dev containers built on `mcr.microsoft.com/devcontainers/rust:latest`. The container includes cmake, ninja-build, gdb/gdbserver, and mounts the workspace at `/tuffy`. Cargo cache is persisted via a Docker volume.

To open the dev container, use the VS Code "Reopen in Container" command.

## Workspace (Cargo)

```
cargo build              # Debug build
cargo build --release    # Release build
cargo run                # Run debug build
cargo test               # Run all tests
cargo test <test_name>   # Run a single test
cargo clippy             # Lint
cargo fmt                # Format code
```

## rustc_codegen_tuffy (codegen backend)

`rustc_codegen_tuffy/` is **not** part of the Cargo workspace. It has its own `Cargo.toml` (crate-type `dylib`) and its own `target/` directory. Build it separately:

```
cargo build --manifest-path rustc_codegen_tuffy/Cargo.toml
```

The resulting `.so` is at `rustc_codegen_tuffy/target/debug/librustc_codegen_tuffy.so`. Use it with rustc:

```
rustc +nightly -Z codegen-backend=rustc_codegen_tuffy/target/debug/librustc_codegen_tuffy.so \
    -C llvm-args=dump-ir -o out input.rs
```

`cargo build` / `cargo test` / `cargo clippy` at the workspace root do **not** touch this crate.

Before running UI tests (`run-ui-tests.sh`), always update the Rust nightly toolchain (`rustup update nightly`) and rebuild the codegen backend. The UI test suite is pulled from upstream rust-lang/rust and may use features only available in the latest nightly.

## Lean 4 (formal verification)

```
cd lean && lake build    # Build Lean project
cd lean && lake clean    # Clean build artifacts
```

Lean 4 is managed via elan (toolchain manager). The Lean project is under `lean/` with Mathlib dependency.

`lean/TuffyLean/README.md` defines module-level conventions for the Lean codebase (directory roles and isel export conventions). Treat it as the canonical guide when modifying files under `lean/TuffyLean/`.
