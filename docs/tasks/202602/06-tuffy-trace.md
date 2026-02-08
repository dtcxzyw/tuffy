# Rewrite Path Tracing (tuffy_trace)

- Status: Draft
- Created: 2026-02-07
- Completed: N/A
- Parent: docs/tasks/202602/init.md

## Description

Implement the rewrite path tracing infrastructure based on the rewrite trace RFC (`docs/RFCs/202602/rewrite-trace.md`).

Key deliverables:
- TraceEntry data structure: rule, stage, context, before/after IR, decision
- TraceEmitter integrated into pass infrastructure
- Three verbosity levels: none (zero overhead), decisions, full
- JSON/JSONL serialization
- Replay engine: re-execute optimization sequence from trace, divergence detection
- Conditional compilation for zero overhead when disabled

## Subtasks

- N/A (leaf task)

## Affected Modules

- `tuffy_trace/src/` — trace data structures, emitter, replay engine
