# Peano: Compile and Run survive-peano-lesson-queue with Tuffy

- Status: In Progress
- Created: 2026-02-17
- Completed: N/A
- Parent: N/A

## Description

Make tuffy capable of compiling and correctly running `survive-peano-lesson-queue.rs`, a CertiCoq-generated Rust program that exercises recursive enums, heap allocation (Box), pattern matching, and indirect function calls extensively.

### Current Status

The test compiles and links successfully but crashes at runtime with SIGSEGV at address 0x8 in `CertiCoq_Benchmarks_lib_Binom_unzip`.

### Known Bug

The crash occurs in `Binom_unzip(%self: ptr, %t: ptr, %cont: ptr, ptr) -> ptr`. The second parameter `%t` holds value 0x8 (an invalid pointer) instead of a valid heap pointer. The function dereferences `%t` to check an enum discriminant, then attempts an indirect call through the loaded value, jumping to address 0x8.

GDB backtrace: `main -> binom -> delete_max -> delete_max_aux -> heap_delete_max -> unzip -> CRASH`.

### Investigation Notes

- The value 0x8 looks like it could be a discriminant or size value being passed where a pointer is expected
- This may be related to enum variant layout, aggregate construction, or how tagged union fields are extracted
- The Aggregate self-copy bug (fix #20 in bitflags.md) was found during this investigation but did not fix the peano crash

### Success Criteria

- [ ] `survive-peano-lesson-queue` runs to completion without segfaults
- [ ] Exit code 0

## Affected Modules

- `rustc_codegen_tuffy/src/mir_to_ir.rs` — MIR translation, enum handling, indirect calls
