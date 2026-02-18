# Rust Doctest Support

- Status: In Progress
- Created: 2026-02-08
- Completed: N/A
- Parent: N/A

## Description

Compile and run Rust stdlib doctests with tuffy as the codegen backend.

Doctests are extracted from `library/` source doc comments, wrapped in `fn main()`,
and compiled with `rustc -Z codegen-backend=tuffy`.

## Current Results (2026-02-18)

Extracted 4025 doctests from `scratch/rust/library/`.

| Category | Count | % |
|----------|------:|----:|
| Pass (compiled) | 2863 | 71.1 |
| Skip (rustc errors) | 990 | 24.6 |
| Link fail (tuffy) | 166 | 4.1 |
| Other | 6 | 0.1 |

### Top linker failure causes

- 38 — `llvm.x86.sse2.pause` (spin_loop intrinsic not implemented)
- ~74 — hashbrown `RawIterRange` (HashMap generic monomorphization)
- 4 — `llvm.x86.sse42.pcmpistri128` (SSE4.2 intrinsic)
- ~8 — static/thread-local symbols not emitted
- ~3 — `conjure_zst` missing

## Subtasks

- [x] Write doctest extraction and compilation script (`tests/run-doctest.sh`)
- [ ] Fix `llvm.x86.sse2.pause` — emit `pause` instruction for spin_loop hint
- [ ] Fix hashbrown `RawIterRange` monomorphization failures
- [ ] Fix duplicate `__rust_alloc` symbol emission
- [ ] Fix static/thread-local variable codegen
- [ ] Add `--run` mode validation (execute compiled doctests)

## Affected Modules

- `rustc_codegen_tuffy/tests/run-doctest.sh` — doctest extraction and compilation script
- `rustc_codegen_tuffy/src/mir_to_ir.rs` — codegen fixes for missing intrinsics/symbols
