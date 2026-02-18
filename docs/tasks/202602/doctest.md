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
| Pass (compiled) | 3028 | 75.2 |
| Skip (rustc errors) | 990 | 24.6 |
| Link fail (tuffy) | 1 | 0.0 |
| Other (extraction bugs, ARM, rustc parse) | 6 | 0.1 |

### Remaining linker failures

- 1 — `alloc_src_slice_3`: complex sort monomorphization (`partition_lomuto_branchless_cyclic` with `(String, u32)`) not compiled

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
- [ ] Add `--run` mode validation (execute compiled doctests)

## Affected Modules

- `rustc_codegen_tuffy/tests/run-doctest.sh` — doctest extraction and compilation script
- `rustc_codegen_tuffy/src/mir_to_ir.rs` — codegen fixes for missing intrinsics/symbols
