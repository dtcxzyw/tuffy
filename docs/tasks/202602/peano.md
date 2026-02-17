# Peano: Compile and Run survive-peano-lesson-queue with Tuffy

- Status: Completed
- Created: 2026-02-17
- Completed: 2026-02-17
- Parent: N/A

## Description

Make tuffy capable of compiling and correctly running `survive-peano-lesson-queue.rs`, a CertiCoq-generated Rust program that exercises recursive enums, heap allocation (Box), pattern matching, and indirect function calls extensively.

### Success Criteria

- [x] `survive-peano-lesson-queue` runs to completion without segfaults
- [x] Exit code 0, output "2001"

## Completed Fixes

1. **Aggregate self-copy corruption** — When `Rvalue::Aggregate` reuses the destination stack slot directly (`val == slot`), the assignment handler's word-by-word copy stored the slot address into itself instead of the actual field values. This corrupted `Layout` structs, causing `Box::new` to pass garbage alignment to `__rust_alloc`. Fixed by skipping the copy when `val == slot`.

2. **Vtable offset double-counting metadata entries** — rustc's `InstanceKind::Virtual(_, idx)` already includes the 3 metadata entries (drop_in_place, size, align), so the byte offset is `idx * 8`. The previous formula `(3 + idx) * 8` double-counted the header, causing virtual calls through `&dyn Fn` trait objects to load a function pointer from past the end of the vtable. The loaded value 0x8 (the align field of an adjacent vtable) was used as a call target, causing SIGSEGV.

## Affected Modules

- `rustc_codegen_tuffy/src/mir_to_ir.rs` — Aggregate assignment handler, vtable offset calculation
