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
| Pass (compiled) | 3010 | 74.8 |
| Skip (rustc errors) | 990 | 24.6 |
| Link fail (tuffy) | 25 | 0.6 |

### Top linker failure causes

- ~21 — `<&T as Debug>::fmt` trait impl methods from vtables in inline functions
- ~2 — `drop_in_place` for complex types (vtable-related)
- ~2 — miscellaneous (stdarch ARM tests, keyword_docs)

## Subtasks

- [x] Write doctest extraction and compilation script (`tests/run-doctest.sh`)
- [x] Fix `llvm.x86.sse2.pause` — skip LLVM intrinsic calls
- [x] Fix hashbrown `RawIterRange` — compile #[inline] functions via fixpoint loop
- [ ] Fix `<&T as Debug>::fmt` vtable references from inline functions
- [x] Fix static variable codegen (emit MonoItem::Static + weak allocator shims)
- [ ] Add `--run` mode validation (execute compiled doctests)

## Affected Modules

- `rustc_codegen_tuffy/tests/run-doctest.sh` — doctest extraction and compilation script
- `rustc_codegen_tuffy/src/mir_to_ir.rs` — codegen fixes for missing intrinsics/symbols
