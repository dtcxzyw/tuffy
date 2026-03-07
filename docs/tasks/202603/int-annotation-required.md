# Task: Make Int Type Annotations Required and Restructure Annotation Format

- Status: Pending
- Created: 2026-03-07
- Completed: N/A
- Parent: N/A

## Description

Restructure the IR type system to require annotations on all Int type values and change the annotation representation format. This is necessary for the legalize pass to work correctly.

## Current State

Currently, annotations on Int types are optional:
- Type: `Type::Int`
- Annotation: `Option<Annotation>` where `Annotation` is an enum with variants `Signed(u32)`, `Unsigned(u32)`, `DontCare(u32)`, `Align(u32)`
- Display format: `int:s32`, `int:u64`, `int:i32`, or just `int` (no annotation)

## Target State

All Int type values must have annotations, and the annotation format should be restructured:
- Type: `Type::Int(IntAnnotation)` where `IntAnnotation` contains:
  - `bit_width: u32`
  - `signedness: IntSignedness` (enum with variants `DontCare`, `Signed`, `Unsigned`)
- Display format: `int:s32`, `int:u64`, `int:i32` (annotation always present)
- Remove `Option<Annotation>` from instruction results for Int types

For Ptr types, annotations will be handled separately:
- Type: `Type::Ptr(Option<PtrAnnotation>)` where `PtrAnnotation` contains alignment information
- Or keep using `result_annotation: Option<Annotation>` where `Annotation::Align(u32)` is the only remaining variant
- Display format: `ptr:align8` or just `ptr` (alignment optional)
- Decision: Choose between embedding annotation in type vs. keeping separate annotation field

## Subtasks

- Define IntAnnotation and IntSignedness types in tuffy_ir
- Refactor Type::Int to include IntAnnotation
- Update instruction result annotation handling
- Update IR display format
- Update IR builder APIs
- Update MIR to IR translation in rustc_codegen_tuffy
- Update optimization passes in tuffy_opt
- Update code generation in tuffy_codegen
- Regenerate all codegen test check lines

## Affected Modules

- `tuffy_ir/src/types.rs` - Type and Annotation definitions
- `tuffy_ir/src/instruction.rs` - Instruction result annotations
- `tuffy_ir/src/display.rs` - Display format for types and annotations
- `tuffy_ir/src/builder.rs` - IR builder APIs
- `rustc_codegen_tuffy/src/mir_to_ir/` - MIR to IR translation
- `tuffy_opt/` - Optimization passes that work with Int types
- `tuffy_codegen/` - Code generation that uses Int type information
- `rustc_codegen_tuffy/tests/codegen/` - All codegen test check lines

## Implementation Steps

1. **Define new IntAnnotation structure:**
   - Create `IntAnnotation` struct with `bit_width` and `signedness` fields
   - Create `IntSignedness` enum with `DontCare`, `Signed`, `Unsigned` variants
   - Update `Type::Int` to `Type::Int(IntAnnotation)`

2. **Update Annotation enum:**
   - Remove `Signed`, `Unsigned`, `DontCare` variants from `Annotation`
   - Keep `Align` for pointer annotations
   - Consider whether `Annotation` is still needed or if it should be pointer-specific

3. **Update instruction result annotations:**
   - Remove `result_annotation: Option<Annotation>` for Int-typed instructions
   - Type information is now fully contained in `inst.ty`

4. **Update display format:**
   - Modify `fmt_type` to always display Int with its annotation
   - Update `fmt_val_typed` to not show separate annotation for Int types
   - Format: `v1: int:s32` (type contains annotation)

5. **Update IR builder:**
   - Modify builder methods to require IntAnnotation when creating Int values
   - Update all call sites to provide bit width and signedness

6. **Update MIR to IR translation:**
   - Extract bit width and signedness from MIR types
   - Create IntAnnotation for all Int values during translation

7. **Update optimization passes:**
   - Ensure all passes that create or transform Int values provide proper annotations
   - Update pattern matching to work with new Type::Int(IntAnnotation) structure

8. **Update codegen:**
   - Modify code generation to extract bit width and signedness from IntAnnotation
   - Update all uses of Int type information

9. **Update tests:**
   - Regenerate all codegen test check lines with new format
   - Update unit tests in tuffy_ir to use new annotation structure

## Validation

- All existing tests must pass with new annotation structure
- Verify legalize pass works correctly with required annotations
- Check that all Int values in generated IR have proper annotations
- Ensure display format is consistent and readable

## Notes

- This is a breaking change to the IR structure
- All code that creates or manipulates Int types must be updated
- The change makes the type system more explicit and prevents missing annotation bugs
- Consider whether other types (Float, Ptr) should follow similar patterns
