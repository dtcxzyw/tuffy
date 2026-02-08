# Translate MIR Control Flow

- Status: In Progress
- Created: 2026-02-08
- Completed: N/A
- Parent: docs/tasks/202602/hello-world.md

## Description

The current MIR translator only handles `Return` and `Goto` terminators, and processes a single basic block linearly. Real Rust code requires branching (`SwitchInt`), multiple basic blocks, and loops.

Key deliverables:
- Translate all MIR basic blocks (not just the entry block)
- Support `SwitchInt` terminator (used for `if`, `match`, loops)
- Emit conditional and unconditional jumps in isel/encode
- Handle block ordering and label resolution (forward/backward jumps)
- Support `Assert` terminator (used for overflow checks, bounds checks)

## Affected Modules

- `rustc_codegen_tuffy/src/mir_to_ir.rs` — translate all basic blocks, SwitchInt, Assert
- `tuffy_ir/src/instruction.rs` — add Branch, CondBranch, ICmp operations
- `tuffy_codegen/src/isel.rs` — select CMP, Jcc, JMP instructions
- `tuffy_codegen/src/encode.rs` — encode conditional jumps, label patching
