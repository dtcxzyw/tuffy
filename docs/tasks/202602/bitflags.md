# Bitflags: Compile and Run bitflags Crate with Tuffy

- Status: Completed
- Created: 2026-02-12
- Completed: 2026-02-15
- Parent: N/A

## Description

Make tuffy capable of compiling and correctly running a Rust binary that uses the `bitflags` crate (v2.10.0) with full `Debug` formatting support. This is the next milestone after the hello-world task.

### Current Status

Phase 1 (basic `println!("{:?}", flags)`) is complete — `Flags(A | B | C)` prints correctly and the binary exits cleanly.

Phase 2 (run `cargo test` for bitflags) is complete. All 37/37 compile-pass tests pass.

### Success Criteria

- [x] `println!("{:?}", flags)` prints the correct Debug representation (e.g. `Flags(A | B | C)`)
- [x] The bitflags debug-format binary runs to completion without segfaults
- [x] All 37 bitflags compile-pass tests pass

## Completed Fixes

1. **Small enum assignment bug** — Changed threshold from `bytes > 8` to `bytes > 0` in the assignment handler so stack-allocated enums with `bytes <= 8` get their data loaded instead of storing the pointer itself.

2. **Sub-word load/store encoding** — `bytes_to_opsize` in isel.rs only mapped 4→S32 and everything else→S64. Added 1→S8, 2→S16 mappings. Updated `encode_mov_rm` to emit `movzbl` (0x0F 0xB6) for S8 and `movzwl` (0x0F 0xB7) for S16. Updated `encode_mov_mr` to emit opcode 0x88 for S8 stores (with REX for registers ≥4) and 0x66 prefix for S16 stores. Updated `encode_mov_mi` to emit 0xC6 with 1-byte immediate for S8 and 0x66+0xC7 with 2-byte immediate for S16.

3. **Return terminator stack slot load size** — The return terminator always loaded 8 bytes from stack slots regardless of the actual return type size. Fixed to load `size.min(8)` bytes with the correct IR type.

4. **Missing intrinsics and stubs** — Implemented stub emission for unhandled intrinsics, `drop_in_place`, and `precondition_check` calls. Fixed `FnOnce` null function pointer crash.

5. **Debug eprintln cleanup** — Removed all temporary debug `eprintln!` statements from the codegen pipeline.

6. **Indirect constant pointer dereference bug** — `ConstValue::Indirect` for reference/pointer types (e.g. `&[Flag<TestFlags>]`) returned `symbol_addr` pointing to the fat pointer data instead of loading the actual data pointer. This caused `InternalBitFlags::all()` to index into the 16-byte slice header instead of the array data, producing wrong flag values. Fixed by loading the pointer value from the emitted static data for `Ref`/`RawPtr` types.

7. **SETcc REX prefix bug** — `encode_setcc` only emitted a REX prefix for r8-r15 registers, but not for RSP/RBP/RSI/RDI (encodings 4-7). Without REX, byte operations on these encodings access legacy high-byte registers (AH/CH/DH/BH) instead of the low-byte registers (SPL/BPL/SIL/DIL), causing BoolToInt to produce garbage values.

8. **Cross-block value flow for call terminators** — The multi-BB assignment detection only scanned `StatementKind::Assign` in MIR statements, missing `TerminatorKind::Call` destinations. Locals assigned by intrinsic/function calls in one block but used in another were not promoted to stack slots, causing stale SSA values.

9. **Intrinsic result stack-slot store** — When `translate_intrinsic` sets a result via `locals.set()`, it overwrites the stack slot pointer with the raw value. Added logic to save the slot pointer before the intrinsic call and emit a store afterward.

10. **Pointer coercion for ptrdiff/arith_offset** — `NonNull<T>` and similar `#[repr(transparent)]` pointer wrappers are loaded as `Int` type. Added `ensure_ptr` coercion (inttoptr) in `ptr_offset_from` and `arith_offset` intrinsic handlers to satisfy the `ptrdiff` verifier check.

11. **size_of / min_align_of intrinsics** — Added inline handlers for `size_of`, `min_align_of`, and `pref_align_of` intrinsics.

12. **DivRem pseudo-instruction** — Replaced separate Idiv/Div instructions with a single DivRem pseudo-instruction that encapsulates the full x86 division sequence, hiding implicit RAX/RDX usage from the register allocator.

13. **needs_self_deref for type parameters** — Excluded `ty::Param` from the blanket-impl reference-stripping check, preventing false self-deref for `impl<I: Iterator> IntoIterator for I`.

14. **needs_self_deref for inherent methods** — Restricted the reference-stripping check to trait methods only (where `args[0]` is Self). For inherent methods like `<[T]>::iter`, `args[0]` is the element type T, not Self — checking `T=&str` incorrectly triggered deref.

15. **Projected destination store scalar pointers** — Only do word-by-word copy for multi-word data (`bytes > 8`). Scalar pointer values (≤8 bytes) are stored directly instead of being treated as source addresses to load from.

16. **Aggregate handler double-deref** — Added `stack_slot_size` check so the load-from-val path only fires when val is actually a stack slot address, not an already-loaded pointer value from `translate_operand`.

17. **Aggregate handler constant fat pointers** — Extract the length component from `Slice`/`Indirect` constants used as fat pointer fields in struct construction (e.g. `MyIter { items: Self::ITEMS, .. }`), preventing word-by-word copy from the data pointer.

18. **Assignment handler constant fat pointers** — Same fix for stack local assignments: store `(data_ptr, len)` directly for `&str` literals and `&[T]` associated constants instead of copying bytes from the data pointer address.

19. **Intrinsic fallthrough to libc** — Check `intrinsic_to_libc` before treating unhandled intrinsics as no-ops, so `compare_bytes` correctly maps to `memcmp` instead of being silently dropped. This fixed string equality comparisons.

## Open Issues

### P2 — Nice to Have

2. **Process MIR blocks in reverse post-order** — Currently blocks are processed in declaration order. Reverse post-order would ensure dominators are visited before their dominated blocks.

3. **Add `.eh_frame` entries for tuffy-compiled functions** — Currently tuffy-emitted object files lack `.eh_frame` sections, which means stack unwinding won't work through tuffy-compiled frames.

## Affected Modules

- `rustc_codegen_tuffy/src/mir_to_ir.rs` — MIR translation, assignment handler, return terminator, place-to-value loading
- `tuffy_target_x86/src/isel.rs` — Instruction selection, `bytes_to_opsize`
- `tuffy_target_x86/src/encode.rs` — Sub-word load/store/immediate encoding
- `tuffy_target_x86/src/emit.rs` — `.eh_frame` generation (future)
