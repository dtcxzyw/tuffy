# Instruction Selection and Machine Code Emission (tuffy_codegen)

- Status: Draft
- Created: 2026-02-07
- Completed: N/A
- Parent: docs/tasks/202602/init.md

## Description

Implement instruction selection, register allocation, and machine code emission based on the IR design RFC (`docs/RFCs/202602/ir-design.md`) machine code lowering section.

Key deliverables:
- Instruction selection: derive concrete types from at-use annotations, choose sext/zext and GPR/FPR
- ABI library: map int parameters/returns to register classes and calling conventions
- Register allocation
- Stack frame layout derived from target triple
- Machine code emission via `object` crate (ELF, Mach-O, COFF)
- Debug info (DWARF) generation
- Unwind table generation

## Subtasks

- N/A (leaf task)

## Affected Modules

- `tuffy_codegen/src/` — instruction selection, regalloc, emission
