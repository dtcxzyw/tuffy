# Optimization Pipeline Infrastructure (tuffy_opt)

- Status: Draft
- Created: 2026-02-07
- Completed: N/A
- Parent: docs/tasks/202602/init.md

## Description

Implement the optimization pipeline infrastructure based on the pipeline RFC (`docs/RFCs/202602/pipeline-design.md`).

Key deliverables:
- Pass trait with TransformKind declaration (Equivalence / Refinement)
- Pass manager: registration, scheduling, stage-based iteration
- Dirty bit protocol for on-demand value-level analysis recomputation
- PipelineConfig: serializable configuration with version locking
- Function-level attribute overrides
- Value-level analysis passes: KnownBits, DemandedBits (as transform passes)
- MemSSA refinement pass

## Subtasks

- N/A (leaf task)

## Affected Modules

- `tuffy_opt/src/` — pass manager, pipeline config, analysis passes
