# Translation Validation (tuffy_tv)

- Status: Draft
- Created: 2026-02-07
- Completed: N/A
- Parent: docs/tasks/202602/init.md

## Description

Implement the translation validation tool based on the verification RFC (`docs/RFCs/202602/verification.md`). Alive2-style SMT-based verifier for quick-checking rewrite rules.

Key deliverables:
- SMT encoding of tuffy IR semantics (infinite precision integers, poison, four-state bytes)
- Automatic verification of simple rewrite rules (bounded bit widths)
- Integration with Lean 4 export: cross-check Lean-verified rules
- CI integration for regression testing
- Missed optimization discovery via candidate enumeration

## Subtasks

- N/A (leaf task)

## Affected Modules

- `tuffy_tv/src/` — SMT encoding, verifier, CI integration
