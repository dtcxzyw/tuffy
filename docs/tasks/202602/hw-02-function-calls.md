# Support Function Calls

- Status: Completed
- Created: 2026-02-08
- Completed: 2026-02-08
- Parent: docs/tasks/202602/hello-world.md

## Description

The backend currently cannot emit function calls. Any non-trivial Rust code (including `println!`) requires calling other functions. This is the single largest gap blocking executable output.

Key deliverables:
- Translate MIR `Call` terminator to tuffy IR
- Emit x86-64 CALL instruction (direct and indirect)
- Generate relocations in ELF objects for external symbol references
- Implement caller-saved register preservation (System V AMD64 ABI)
- Set up proper stack frame (push rbp / mov rsp,rbp / pop rbp)
- Handle return values from called functions
- Support calling functions with >6 arguments (stack passing)

## Affected Modules

- `rustc_codegen_tuffy/src/mir_to_ir.rs` — translate Call terminator, resolve callee
- `tuffy_ir/src/instruction.rs` — add Call operation
- `tuffy_codegen/src/isel.rs` — select CALL, handle caller-saved regs, stack args
- `tuffy_codegen/src/encode.rs` — encode CALL rel32, PUSH, POP, stack frame
- `tuffy_codegen/src/emit.rs` — emit relocations for external symbols
