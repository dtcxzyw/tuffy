# Implement At-Use Annotations

- Status: Completed
- Created: 2026-02-08
- Completed: 2026-02-08
- Parent: N/A

## Description

Replace standalone `assert_sext`/`assert_zext` instructions with at-use annotations
on value definitions (result-side) and use edges (use-side), as specified in
[RFC: at-use-annotations](../../RFCs/202602/at-use-annotations.md).

Additionally, elide the implicit top-level `region function` in the text format.

This task follows the [IR Modification SOP](../../SOPs/ir-change.md).

## Subtasks

Following the SOP checklist order:

- [x] **SOP Step 4: Update spec and RFC docs** — Update `docs/spec.md` and
  `docs/RFCs/202602/ir-design.md` to reflect the new annotation design
- [x] **SOP Step 1: Lean 4 formal definitions** — Add `Annotation` and `FloatType`
  to `Types.lean`; replace `assertSext`/`assertZext` with `checkSignedRange`/
  `checkUnsignedRange`/`applyAnnotation` in `Semantics.lean`
- [x] **SOP Step 2: Rust `tuffy_ir`** — Remove `AssertSext`/`AssertZext` opcodes;
  add `Annotation`, `FloatType`, `Operand` types; add `result_annotation` to
  `Instruction`; add `param_annotations`/`ret_annotation` to `Function`; update
  `builder.rs` API; update `display.rs` to emit annotation syntax and elide
  top-level `region function`
- [x] **SOP Step 3: Downstream crates** — Update `tuffy_codegen` isel and tests,
  `rustc_codegen_tuffy` MIR translation
- [x] **SOP Step 5: Tests** — Update unit tests, codegen tests, e2e tests,
  UI tests (4913 pass / 0 fail)

## Affected Modules

- `lean/TuffyLean/IR/Types.lean` — Add annotation type definition
- `lean/TuffyLean/IR/Semantics.lean` — Remove assertSext/assertZext; add annotation semantics
- `tuffy_ir/src/instruction.rs` — Remove AssertSext/AssertZext opcodes
- `tuffy_ir/src/value.rs` — Add per-use annotation storage
- `tuffy_ir/src/types.rs` — Add Annotation/KnownBits types
- `tuffy_ir/src/builder.rs` — Update API to accept annotations
- `tuffy_ir/src/display.rs` — Emit annotation syntax; elide top-level region
- `tuffy_ir/src/function.rs` — Remove top-level region wrapper requirement
- `tuffy_ir_interp/src/lib.rs` — Update evaluation for annotation semantics
- `tuffy_codegen/src/isel.rs` — Read annotations for type determination
- `docs/spec.md` — Replace assert nodes with annotations; update examples
- `docs/RFCs/202602/ir-design.md` — Update to match new design
