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

Extracted 4026 doctests from `scratch/rust/library/`.

| Category | Count | % |
|----------|------:|----:|
| Pass (compiled) | 2986 | 74.2 |
| Skip (rustc errors) | 996 | 24.7 |
| Link fail (tuffy) | 43 | 1.1 |
| Other | 1 | 0.0 |

### Top linker failure causes

- ~17 — `<&T as Debug>::fmt` trait impl methods from vtables in inline functions
- ~26 — static/thread-local symbols not emitted

## Subtasks

- [x] Write doctest extraction and compilation script (`tests/run-doctest.sh`)
- [x] Fix `llvm.x86.sse2.pause` — skip LLVM intrinsic calls
- [x] Fix hashbrown `RawIterRange` — compile #[inline] functions via fixpoint loop
- [ ] Fix `<&T as Debug>::fmt` vtable references from inline functions
- [ ] Fix static/thread-local variable codegen
- [ ] Add `--run` mode validation (execute compiled doctests)

## Affected Modules

- `rustc_codegen_tuffy/tests/run-doctest.sh` — doctest extraction and compilation script
- `rustc_codegen_tuffy/src/mir_to_ir.rs` — codegen fixes for missing intrinsics/symbols
