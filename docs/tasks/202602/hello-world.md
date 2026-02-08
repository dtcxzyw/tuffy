# Hello World: Produce Working Executables with std

- Status: In Progress
- Created: 2026-02-08
- Completed: N/A
- Parent: N/A

## Description

Make tuffy capable of compiling and linking a complete Rust binary that uses the standard library:

```rust
fn main() {
    println!("Hello, world!");
}
```

This requires closing the gap from "compiles simple arithmetic as `--crate-type lib`" to "produces a working executable linked against std". The current backend only handles Param, Add, Sub, Mul, Const, and Ret on i32/u32 with no function calls, no memory operations, no control flow, and no linker integration.

### Success Criteria

- `rustc -Z codegen-backend=... hello.rs && ./hello` prints "Hello, world!"
- The binary links against the system's standard library (std, libc)
- `cargo build` works for a trivial Cargo project with tuffy as the backend

## Subtasks

- [hw-01-control-flow.md](hw-01-control-flow.md) — Translate MIR control flow (SwitchInt, branches, basic blocks)
- [hw-02-function-calls.md](hw-02-function-calls.md) — Support function calls (Call terminator, ABI, relocations)
- [hw-03-memory.md](hw-03-memory.md) — Stack frame, load/store, aggregate types
- [hw-04-types.md](hw-04-types.md) — Expand type support (i8–i64, pointers, bool, unit, references)
- [hw-05-linking.md](hw-05-linking.md) — Implement CodegenBackend::link(), invoke system linker
- [hw-06-std.md](hw-06-std.md) — Standard library integration (allocator, panic, lang items)

## Affected Modules

- `rustc_codegen_tuffy/src/lib.rs` — link() implementation, entry point handling
- `rustc_codegen_tuffy/src/mir_to_ir.rs` — MIR translation expansion
- `tuffy_ir/src/instruction.rs` — New IR operations (Call, Branch, Load, Store, etc.)
- `tuffy_codegen/src/isel.rs` — Instruction selection for new ops
- `tuffy_codegen/src/encode.rs` — New x86 instruction encodings
- `tuffy_codegen/src/emit.rs` — Relocations, multiple symbols per object
