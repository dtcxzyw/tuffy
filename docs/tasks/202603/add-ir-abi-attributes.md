# Add IR ABI Attributes (sret/byval)

**Status**: Pending
**Created**: 2026-03-07
**Completed**: -

## Task Description

Add ABI attribute support to tuffy IR to properly handle target-specific calling conventions without hardcoding ABI rules in the frontend.

Currently, `rustc_codegen_tuffy` hardcodes x86-64 SysV ABI rules (e.g., `size > 16` for SRET/indirect parameters), violating the architecture boundary principle. This prevents supporting other targets (ARM64, RISC-V) with different ABI rules.

## Motivation

**Current problems**:
- Frontend hardcodes x86-64 ABI thresholds (16 bytes for SRET, indirect params)
- Cannot support multiple targets with different ABI rules
- Violates separation of concerns (frontend knows backend details)

**LLVM's approach**:
- Uses IR attributes (`sret`, `byval`, `inreg`) to mark ABI semantics
- Frontend queries target ABI and generates attributed IR
- Backend lowers attributes according to target calling convention

## Proposed Solution

Add function parameter/return attributes to tuffy IR, similar to LLVM:

```rust
// IR syntax
func @foo(%ret: ptr sret, %arg: ptr byval) -> void

// IR representation
pub enum ParamAttr {
    Sret,      // Structured return pointer
    Byval,     // Pass by value through pointer
    Inreg,     // Pass in register (hint)
}

pub struct Param {
    pub ty: Type,
    pub attrs: Vec<ParamAttr>,
}
```

## Implementation Steps

1. **Add attribute types to tuffy_ir**
   - Define `ParamAttr` and `ReturnAttr` enums
   - Add attribute fields to `Function` signature
   - Update IR parser/printer to handle attributes

2. **Update rustc_codegen_tuffy to query ABI**
   - Remove hardcoded `size > 16` checks
   - Query backend for ABI classification
   - Generate IR with appropriate attributes

3. **Update backends to respect attributes**
   - Modify `tuffy_target_x86` to handle `sret`/`byval`
   - Implement attribute lowering in instruction selection
   - Update calling convention handling

4. **Remove AbiMetadataBox workaround**
   - Migrate existing metadata users to attributes
   - Clean up temporary ABI tracking code

5. **Add tests**
   - Test SRET functions (>16 byte returns)
   - Test byval parameters (>16 byte params)
   - Test i128 return values (two-register returns)

## Affected Modules

- `tuffy_ir` - Add attribute definitions
- `rustc_codegen_tuffy` - Remove hardcoded ABI, query backend
- `tuffy_target` - Define ABI query interface
- `tuffy_target_x86` - Implement attribute lowering
- `tuffy_codegen` - Update compilation pipeline

## References

- LLVM IR attributes: https://llvm.org/docs/LangRef.html#parameter-attributes
- x86-64 SysV ABI: https://gitlab.com/x86-psABIs/x86-64-ABI
- Current analysis: `/tmp/i128_special_cases_analysis.md`
