# Expand Type Support

- Status: In Progress
- Created: 2026-02-08
- Completed: N/A
- Parent: docs/tasks/202602/hello-world.md

## Description

The MIR translator only handles i32/u32. Standard library code uses the full range of Rust types. Without broader type support, most MIR functions are skipped.

Key deliverables:
- Support all integer types: i8, i16, i32, i64, u8, u16, u32, u64, isize, usize
- Support bool, char, unit `()`
- Support raw pointers and references (as i64/usize in IR)
- Support tuples and simple structs (via layout computation)
- Translate MIR `Cast` rvalue (IntToInt, PtrToPtr, etc.)
- Handle `Len`, `Discriminant`, `NullaryOp` rvalues

## Affected Modules

- `rustc_codegen_tuffy/src/mir_to_ir.rs` — type mapping, Cast, wider rvalue coverage
- `tuffy_ir/src/types.rs` — add I8, I16, I64, Ptr types
- `tuffy_codegen/src/isel.rs` — operand size selection based on type
- `tuffy_codegen/src/encode.rs` — 8/16/64-bit instruction variants, REX.W
