# Bitflags: Compile and Run bitflags Crate with Tuffy

- Status: In Progress
- Created: 2026-02-12
- Completed: N/A
- Parent: N/A

## Description

Make tuffy capable of compiling and correctly running a Rust binary that uses the `bitflags` crate (v2.10.0) with full `Debug` formatting support. This is the next milestone after the hello-world task.

### Current Status

Phase 1 (basic `println!("{:?}", flags)`) is complete — `Flags(A | B | C)` prints correctly and the binary exits cleanly.

Phase 2 (run `cargo test` for bitflags) is in progress. The test binary links successfully but crashes with SIGABRT during `TestFlags::all()` assertion. Multiple sub-word codegen bugs have been fixed, but one critical issue remains.

### Success Criteria

- [x] `println!("{:?}", flags)` prints the correct Debug representation (e.g. `Flags(A | B | C)`)
- [x] The bitflags debug-format binary runs to completion without segfaults
- [ ] `cargo test` for bitflags passes (or most tests pass)

## Completed Fixes

1. **Small enum assignment bug** — Changed threshold from `bytes > 8` to `bytes > 0` in the assignment handler so stack-allocated enums with `bytes <= 8` get their data loaded instead of storing the pointer itself.

2. **Sub-word load/store encoding** — `bytes_to_opsize` in isel.rs only mapped 4→S32 and everything else→S64. Added 1→S8, 2→S16 mappings. Updated `encode_mov_rm` to emit `movzbl` (0x0F 0xB6) for S8 and `movzwl` (0x0F 0xB7) for S16. Updated `encode_mov_mr` to emit opcode 0x88 for S8 stores (with REX for registers ≥4) and 0x66 prefix for S16 stores. Updated `encode_mov_mi` to emit 0xC6 with 1-byte immediate for S8 and 0x66+0xC7 with 2-byte immediate for S16.

3. **Return terminator stack slot load size** — The return terminator always loaded 8 bytes from stack slots regardless of the actual return type size. Fixed to load `size.min(8)` bytes with the correct IR type.

4. **Missing intrinsics and stubs** — Implemented stub emission for unhandled intrinsics, `drop_in_place`, and `precondition_check` calls. Fixed `FnOnce` null function pointer crash.

5. **Debug eprintln cleanup** — Removed all temporary debug `eprintln!` statements from the codegen pipeline.

## Open Issues

### P0 — Blocking

1. **`Flag::value()` returns pointer instead of loaded value** — In the bitflags crate, `Flag<TestFlags>::value(&self) -> TestFlags` emits IR that returns `-> ptr` with just `ptradd` (no load), while standalone test cases with the identical pattern correctly emit `-> int` with `ptradd` + `load.1`. The IR dump confirms the load instruction is entirely missing. Root cause is likely in how `translate_place_to_value` or the assignment handler interacts with generic monomorphization of `Flag<B>` where `B = TestFlags`. This causes `TestFlags::all()` to fail its assertion because it compares an address against an expected bitmask value.

### P2 — Nice to Have

2. **Process MIR blocks in reverse post-order** — Currently blocks are processed in declaration order. Reverse post-order would ensure dominators are visited before their dominated blocks.

3. **Add `.eh_frame` entries for tuffy-compiled functions** — Currently tuffy-emitted object files lack `.eh_frame` sections, which means stack unwinding won't work through tuffy-compiled frames.

## Affected Modules

- `rustc_codegen_tuffy/src/mir_to_ir.rs` — MIR translation, assignment handler, return terminator, place-to-value loading
- `tuffy_target_x86/src/isel.rs` — Instruction selection, `bytes_to_opsize`
- `tuffy_target_x86/src/encode.rs` — Sub-word load/store/immediate encoding
- `tuffy_target_x86/src/emit.rs` — `.eh_frame` generation (future)
