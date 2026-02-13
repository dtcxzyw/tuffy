# Bitflags: Compile and Run bitflags Crate with Debug Formatting

- Status: Completed
- Created: 2026-02-12
- Completed: 2026-02-13
- Parent: N/A

## Description

Make tuffy capable of compiling and correctly running a Rust binary that uses the `bitflags` crate (v2.10.0) with full `Debug` formatting support. This is the next milestone after the hello-world task.

Basic bitwise operations (`|`, `&`, `contains()`) already work correctly after fixing call return value tracking and spurious fat_locals injection. The remaining blocker is `println!("{:?}", flags)` which segfaults due to incorrect `fmt::Arguments` / `fmt::Argument` struct construction or passing.

### Current Status

- All success criteria met: `println!("{:?}", e3)` prints `Flags(A | B | C)` and the binary exits cleanly
- Root cause: when assigning a stack-allocated enum (Ptr value) to a stack local with `bytes <= 8`, the assignment handler stored the pointer itself instead of loading the pointed-to data. Fixed by changing the threshold from `bytes > 8` to `bytes > 0` in both the direct-local and projected-destination assignment paths in `mir_to_ir.rs`.

### Success Criteria

- `println!("{:?}", flags)` prints the correct Debug representation (e.g. `Flags(A | B | C)`)
- The bitflags test binary runs to completion without segfaults

## Subtasks

### P0 — Blocking

1. **Fix fmt::Arguments construction segfault** — The 48-byte `Arguments` struct (3 fat pointers: pieces, fmt, args) is not being constructed or passed correctly. The `fmt::Argument` array's function pointer field gets corrupted with the flags value. Investigate whether `Arguments::new` (tuffy-compiled) correctly preserves the Argument data, or whether the issue is in how the struct is passed through the `_print` call chain. Use GDB watchpoints on the memory location that should contain the fmt function pointer to find the exact corruption point.

### P1 — Important

2. **Clean up debug eprintln statements** — Remove temporary `eprintln!` debug output scattered throughout `mir_to_ir.rs` and `isel.rs` (e.g. `[isel-ensure]`, `[isel-load]`, `[tuffy-call]` prefixed messages). These were added during debugging and should be removed before the next milestone.

3. **Fix `<fn() as FnOnce<()>>::call_once` codegen** — This function's codegen is currently broken. It is needed for trait object dispatch and closures.

### P2 — Nice to Have

4. **Process MIR blocks in reverse post-order** — Currently blocks are processed in declaration order. Reverse post-order would ensure dominators are visited before their dominated blocks, improving correctness for complex control flow.

5. **Add `.eh_frame` entries for tuffy-compiled functions** — Currently tuffy-emitted object files lack `.eh_frame` sections, which means stack unwinding (panics, backtraces) won't work through tuffy-compiled frames.

## Affected Modules

- `rustc_codegen_tuffy/src/mir_to_ir.rs` — fmt::Arguments struct construction, fat pointer handling, debug cleanup
- `tuffy_target_x86/src/isel.rs` — Debug cleanup, potential fixes for struct passing
- `tuffy_target_x86/src/emit.rs` — `.eh_frame` generation
- `tuffy_target_x86/src/encode.rs` — Potential new instruction encodings for struct ops
