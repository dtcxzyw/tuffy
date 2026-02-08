# Target Abstraction Layer (tuffy_target)

- Status: Draft
- Created: 2026-02-07
- Completed: N/A
- Parent: docs/tasks/202602/init.md

## Description

Implement the target abstraction layer based on decisions in `docs/initial.md`. Triple-based target identification with trait-based TargetLowering and CLI override mechanism for testing.

Key deliverables:
- TargetLowering trait: legal types, operation lowering, register classes
- Triple-based target identification following LLVM convention
- `--target-override key=value` CLI mechanism for overriding individual properties
- tuffy_target_x86 crate: i386 + x86-64 backend (initial skeleton)

## Subtasks

- N/A (leaf task)

## Affected Modules

- `tuffy_target/src/` — target abstraction traits and override mechanism
- `tuffy_target_x86/src/` — x86 backend implementation
