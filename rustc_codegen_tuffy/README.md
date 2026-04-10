# rustc_codegen_tuffy

Rustc codegen backend that translates MIR into tuffy IR.

## Overview

This crate implements `CodegenBackend` from `rustc_codegen_ssa`, plugging Tuffy into the Rust compiler as an alternative code generation backend. It is built as a `dylib` and loaded at runtime:

```
rustc +nightly -Z codegen-backend=path/to/librustc_codegen_tuffy.so input.rs
```

This crate is **not** part of the Cargo workspace — it has its own `Cargo.toml` and `target/` directory.

## Architecture

### Backend Shell

Top-level backend responsibilities are split across small modules:

| Module            | Purpose                                                   |
|-------------------|-----------------------------------------------------------|
| `lib.rs`          | Thin `CodegenBackend` facade and rustc entry point        |
| `driver/aot.rs`   | AOT crate codegen pipeline, CGU iteration, inline fixpoint|
| `config.rs`       | Backend option parsing and target feature reporting       |
| `allocator.rs`    | Allocator shim emission                                   |
| `main_shim.rs`    | C `main` / `lang_start` shim emission                     |
| `rust_try.rs`     | `__rust_try` unwind helper emission                       |
| `static_data.rs`  | Static allocation relocation lowering helpers             |

### `mir_to_ir/` — MIR-to-IR Translation

The core translation layer, organized into submodules by concern:

| Module             | Purpose                                              |
|--------------------|------------------------------------------------------|
| `mod.rs`           | Top-level function translation and block traversal   |
| `ctx.rs`           | Translation context (value maps, type caches, state) |
| `types.rs`         | Rust type → tuffy IR type mapping                    |
| `local_analysis.rs`| Stack promotion pre-scan and local variable analysis |
| `place.rs`         | MIR Place → IR address/value translation             |
| `operand.rs`       | MIR Operand → IR value translation                   |
| `fat_ptr.rs`       | Fat pointer metadata extraction and handling         |
| `discriminant.rs`  | Enum discriminant read/write operations              |
| `rvalue.rs`        | Rvalue translation (binops, unops, casts, aggregates)|
| `statement.rs`     | Statement translation (assign, storage, intrinsics)  |
| `terminator.rs`    | Terminator translation (return, branch, switch, call)|
| `call.rs`          | Function call ABI handling and argument passing      |
| `constant.rs`      | Constant evaluation and literal translation          |
| `intrinsic.rs`     | Scalar intrinsic function lowering                   |
| `simd.rs`          | SIMD intrinsic lowering                              |

### Optimization Hook

After MIR-to-IR translation succeeds, the backend batches all translated functions for one emitted
object into a shared tuffy IR module and runs `tuffy_opt::optimize_module` on that batch before
handing functions to `tuffy_codegen`, but only when rustc codegen optimization is enabled
(`-C opt-level` other than `0`). Regular CGU objects and the later `inline_shims` object are
optimized as separate module batches. This keeps debug-style builds close to raw translation while
allowing optimized builds to benefit from module-level inlining plus the existing cleanup pipeline.

`dump-ir` continues to print the post-translation, pre-optimization IR so the existing codegen
tests remain focused on MIR lowering rather than backend-local optimization effects. When
`dump-module=` is enabled, the written module dump now appends a post-optimization module snapshot
for each batched object. The `dump-ir` stream remains the stable pre-optimization artifact used by
existing codegen checks.

## Boundary Rule

This crate is the **sole boundary** between rustc and the Tuffy compiler infrastructure. All Rust-specific semantics, ABI conventions, MIR quirks, and language-level workarounds must be fully resolved here before emitting tuffy IR.

The downstream crates (`tuffy_ir`, `tuffy_opt`, `tuffy_target`, `tuffy_target_x86`, `tuffy_codegen`, etc.) are language-agnostic. They must never contain Rust-specific logic, special cases, or workarounds. If a Rust construct cannot be directly expressed in tuffy IR, this crate is responsible for lowering it into a valid IR representation.

## Key Design Decisions

- Keeps MIR lowering semantic: machine ABI details such as secondary return
  registers are represented explicitly in IR (`call_ret2`, secondary `ret`
  operand, call cleanup labels) or derived later by the backend.
- Handles i128/u128 types through annotation-based legalization rather than type splitting at the IR level.
- **wide integer load/store**: emits a single wide `load` / `store` IR instruction; the backend legalize pass lowers it into legal-width operations.
- **carrying_mul_add**: emits dedicated `scarrying_mul_add` / `ucarrying_mul_add` IR ops; the backend legalize pass lowers them into legal-width arithmetic.
- **load/store struct**: emits a single `load` / `store` with struct type; the backend legalize pass expands into per-word operations based on ABI rules.
- **function parameters**: struct parameters are represented as single IR values with struct type; the backend legalize pass splits them into multiple register-sized parameters according to the target ABI.
- Supports `dump-ir` via `-C llvm-args=dump-ir` for debugging IR output.

## Translation Conventions

When translating MIR constructs to tuffy IR, follow these principles:

- **MIR semantics are defined by [`rustc_middle::mir::syntax`](https://github.com/rust-lang/rust/blob/main/compiler/rustc_middle/src/mir/syntax.rs).** This is the authoritative source for MIR construct definitions and their intended behavior. When uncertain about MIR semantics, consult the rustc source code first, then reference existing backends (miri, LLVM, Cranelift) for translation strategies.
- **Reference LLVM IR semantics** when uncertain about translation strategy. LLVM IR provides a well-documented, battle-tested model for lowering high-level constructs.
- **When comparing MIR-to-IR translation with other backends, disable their optimization passes.** Use `-C opt-level=0` and `-C llvm-args=-disable-llvm-optzns` for LLVM to ensure fair comparison of MIR translation output without backend-specific optimizations obscuring the translation logic.
- **No special-case handling for specific examples.** Translation logic must be general and correct for all valid inputs, not tailored to pass particular test cases.
- Emit IR that accurately represents the semantics of the source construct, not IR that happens to work for a specific input.

## Testing

### Codegen Tests

Codegen tests verify MIR-to-IR translation correctness using CHECK annotations:

```rust
// compile-flags: -C opt-level=0
// CHECK: func @add(%a: int:s32, %b: int:s32) -> int:s32
// CHECK:     v3:s32 = add v1:s32, v2:s32

pub fn add(a: i32, b: i32) -> i32 { a + b }
```

Run with: `tests/run-codegen-tests.sh`

To automatically generate or update CHECK lines: `tests/update-codegen-test.sh <test.rs>`

**IMPORTANT:** When modifying tests under `tests/codegen/`, always use `update-codegen-test.sh` to regenerate CHECK lines. Do not write CHECK lines manually — the script ensures they match the actual IR output format and indentation.

CHECK lines use exact string matching (not regex), including indentation. Each CHECK line must appear in order in the generated IR output.

**Compile flags:** Unless testing specific behaviors (e.g., debug assertion codegen, debug symbols), use `-Zmir-opt-level=3 -C debug-assertions=off` as the standard compile flags for codegen tests. This ensures tests verify optimized MIR translation.

### Smoke Tests

Basic sanity check that verifies the backend can compile and execute a simple program:

```bash
tests/run-tests.sh
```

Compiles and runs `tests/fixtures/hello.rs`, verifying that `println!("Hello, world!")` produces correct output.

## Debug Info

`-C debuginfo` now emits embedded DWARF into the generated object files.
Source locations are derived from MIR `SourceInfo`, attached to IR instruction
origins, preserved through legalization, and lowered into x86 machine-code line
records plus best-effort parameter/local variable locations.

### UI Tests

Runs rustc UI tests from `rust-lang/rust` against the tuffy backend:

```bash
tests/run-ui-tests.sh [options] [rust-src-dir]
```

Options:
- `--fail-fast`: Stop at first failure
- `--shuffle`: Randomize test order (default: sorted)
- `--filter PATTERN`: Only run tests matching pattern

Requires `scratch/rust/tests/ui/` (sparse clone of rust-lang/rust at pinned version). Tests are compiled as libraries (`--crate-type lib`) to verify MIR translation without linking. Tests with error annotations (`//~`) or unsupported directives are automatically skipped.

Setup:
```bash
git clone --filter=blob:none --sparse -b 1.93.1 https://github.com/rust-lang/rust.git scratch/rust
cd scratch/rust && git sparse-checkout set tests/ui
```

### Run-Pass Tests

Runs executable tests from rustc UI test suite (compile, link, and execute):

```bash
tests/run-pass-tests.sh [options] [rust-src-dir]
```

Options:
- `--fail-fast`: Stop at first failure

Filters UI tests for those with `fn main()` and no error annotations, then compiles as binaries and executes them. Distinguishes between compile failures, link failures, and runtime failures. Uses the same `scratch/rust/tests/ui/` directory as UI tests.

### Doctest Tests

Extracts and compiles doctests from Rust standard library source:

```bash
tests/run-doctest.sh [library-dir] [--run]
```

Arguments:
- `library-dir`: Path to `scratch/rust/library` (default: `../../scratch/rust/library`)
- `--run`: Execute compiled binaries (default: compile-only)

Extracts code blocks from doc comments, wraps them in `fn main()` if needed, and compiles with tuffy backend. Requires a full clone of rust-lang/rust (not sparse).

### Test Requirements

When modifying MIR-to-IR translation modules in `mir_to_ir/`, add corresponding regression tests to `tests/codegen/`:

- Organize tests by module: changes to `intrinsic.rs` → tests in `tests/codegen/intrinsic/`
- Keep test cases minimal and focused on the specific behavior being tested
- Use meaningful names for all identifiers (functions, variables, types)
- Each test must include CHECK annotations verifying the expected IR output

After modifying `mir_to_ir/` modules, run `tests/run-codegen-tests.sh` to ensure no regressions. If tests fail, determine whether to update CHECK lines (if the new IR is correct) or fix the implementation (if the change introduced a bug).

### Differential Testing with Rustlantis

[Rustlantis](https://github.com/cbeuw/rustlantis) generates random, UB-free, deterministic custom MIR programs and compares execution output across compiler backends. Any output mismatch indicates a codegen bug.

**Setup:**

```bash
git clone https://github.com/cbeuw/rustlantis.git /tmp/rustlantis
cd /tmp/rustlantis
git apply /tuffy/rustc_codegen_tuffy/rustlantis/patch/tuffy-backend.patch
cp /tuffy/rustc_codegen_tuffy/rustlantis/patch/config.toml .
cp /tuffy/rustc_codegen_tuffy/rustlantis/patch/fuzz.py .
cargo build --release
```

**Running:**

```bash
python3 fuzz.py <start_seed> <end_seed> [jobs]
```

The script supports parallel execution. The optional `jobs` parameter controls concurrency (defaults to `nproc`):

```bash
python3 fuzz.py 0 1000        # Use all CPU cores
python3 fuzz.py 0 1000 8      # Use 8 parallel jobs
```

**Tips:**

- Adjust `config.toml` to generate smaller inputs when debugging (fewer basic blocks, functions, args)
- Use `minimise.py` to reduce reproducers: copy failing program to `repro.rs`, run `python3 minimise.py`
  - Note: `minimise.py` comments out MIR code rather than deleting lines, so line numbers remain stable. The minimization is still effective.
- Always minimize reproducers before reading them — raw generated programs contain noise

## Error Policy

Unsupported MIR constructs (rvalue kinds, statement kinds, terminator kinds, intrinsics, place projections) must **not** be silently skipped or marked as unreachable. Instead:

- Use `trap()` to emit a runtime trap instruction for unsupported terminators and unhandled cases (e.g., `InlineAsm` without targets, `Resume`, `Yield`, etc.)
- Use `unimplemented!()` with a descriptive message for unsupported operations that should never occur in valid MIR
- When an error is hit, the correct response is to add a concrete implementation for that construct — not to suppress the error

## Dependencies

- `tuffy_ir` — IR definitions
- `tuffy_opt` — Lean-owned peephole optimizer run before backend codegen
- `tuffy_target` — backend trait
- `tuffy_codegen` — target-dispatching facade
- `num-bigint` — arbitrary-precision integer constants
- `rustc_*` — rustc internal crates (via `#![feature(rustc_private)]`)

## References

- [MIR to Tuffy IR Translation](../docs/mir_to_tuffy_ir.md) — Complete mapping of MIR operations to Tuffy IR instructions
- [MIR (Mid-level IR)](https://rustc-dev-guide.rust-lang.org/mir/index.html)
- [Lowering MIR](https://rustc-dev-guide.rust-lang.org/backend/lowering-mir.html)
- [Backend Agnostic Codegen](https://rustc-dev-guide.rust-lang.org/backend/backend-agnostic.html)
