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
| Pass (compiled) | 3029 | 75.3 |
| Skip (rustc errors) | 990 | 24.6 |
| Link fail (tuffy) | 0 | 0.0 |
| Other (extraction bugs, ARM, rustc parse) | 6 | 0.1 |

### Non-tuffy failures

- 3 — extraction bugs (prose/grammar extracted as Rust code)
- 2 — stdarch ARM-specific tests (not applicable on x86)
- 1 — rustc edition parse error (anonymous parameters)

## Subtasks

- [x] Write doctest extraction and compilation script (`tests/run-doctest.sh`)
- [x] Fix `llvm.x86.sse2.pause` — skip LLVM intrinsic calls
- [x] Fix hashbrown `RawIterRange` — compile #[inline] functions via fixpoint loop
- [x] Fix `<&T as Debug>::fmt` vtable references from inline functions
- [x] Fix static variable codegen (emit MonoItem::Static + weak allocator shims)
- [x] Fix `drop_in_place` discovery (add drop instances to referenced_instances)
- [x] Fix function pointer instance tracking (ReifyFnPointer + GlobalAlloc::Function constants)
- [x] Fix allocator shim symbol collision with fixpoint loop stubs
- [ ] Add `--run` mode validation (execute compiled doctests)

## Affected Modules

- `rustc_codegen_tuffy/tests/run-doctest.sh` — doctest extraction and compilation script
- `rustc_codegen_tuffy/src/mir_to_ir.rs` — codegen fixes for missing intrinsics/symbols
