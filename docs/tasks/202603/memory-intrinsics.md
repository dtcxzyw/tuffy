# Introduce memcpy/memset/memmove Intrinsics

- Status: Completed
- Created: 2026-03-05
- Completed: 2026-03-05
- Parent: N/A

## Description

Add support for memory operation intrinsics (memcpy, memset, memmove) to the compiler. These are fundamental operations for efficient memory manipulation and are commonly used by higher-level languages.

The implementation should:
- Define IR representations for these intrinsics
- Implement code generation to lower them to target-specific instructions
- Integrate with rustc_codegen_tuffy to recognize and translate Rust's memory intrinsics

## Subtasks

- Define intrinsic representations in tuffy_ir
- Implement codegen lowering in tuffy_codegen
- Add rustc integration in rustc_codegen_tuffy
- Add target-specific instruction selection (x86_64)
- Add regression tests

## Affected Modules

- `tuffy_ir` - add intrinsic IR nodes for memory operations
- `tuffy_codegen` - implement lowering logic for intrinsics
- `rustc_codegen_tuffy` - translate rustc intrinsics to tuffy IR
- `tuffy_target_x86` - x86_64 instruction selection for memory ops
