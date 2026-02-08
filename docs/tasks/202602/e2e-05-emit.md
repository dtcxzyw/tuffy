# Machine Code Emission to Object File

- Status: Completed
- Created: 2026-02-08
- Completed: 2026-02-08
- Parent: docs/tasks/202602/e2e-pipeline.md

## Description

Encode x86-64 machine instructions into bytes and emit a valid ELF object file using the `object` crate.

Key deliverables:
- x86-64 instruction encoding: `add`, `mov`, `ret` (minimal subset)
- Emit `.text` section with encoded function
- Emit symbol table entry for the function
- Produce valid `.o` file that `ld` or `cc` can link
- Verify with `objdump -d` that disassembly matches expected instructions

Not included:
- Relocations (not needed for simple leaf function)
- Debug info (DWARF)
- Unwind tables
- Mach-O / COFF (ELF only for now)

## Affected Modules

- `tuffy_codegen/src/`
