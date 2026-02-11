# Document Annotation signed/unsigned design rationale

- Status: Completed
- Created: 2026-02-10
- Completed: 2026-02-11
- Parent: N/A

## Description

Add documentation explaining why `Annotation` is designed as a binary choice between
`signed(N)` and `unsigned(N)`, rather than allowing both constraints simultaneously.

Key points to document:

1. The intersection of any two range annotations is always expressible as a single annotation:
   - `:s<M>` ∩ `:s<N>` = `:s<min(M,N)>`
   - `:u<M>` ∩ `:u<N>` = `:u<min(M,N)>`
   - `:s<M>` ∩ `:u<N>` = `:u<min(M-1, N)>`
2. Therefore, supporting both simultaneously adds no expressive power.
3. The planned `KnownBits` extension (per-bit four-state constraint) is the correct
   generalization for constraints that range annotations cannot express.

The rationale should be added to the at-use annotations RFC (`docs/RFCs/202602/at-use-annotations.md`)
or as a dedicated section in the IR spec, whichever is more appropriate.

## Subtasks

- Add a "Why signed/unsigned is a binary choice" section to the at-use annotations RFC

## Affected Modules

- `docs/RFCs/202602/at-use-annotations.md` — add design rationale section
