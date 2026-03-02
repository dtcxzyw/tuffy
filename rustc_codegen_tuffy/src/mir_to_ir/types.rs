//! Type translation utilities for MIR → IR conversion.

use rustc_middle::mir::{self, Operand};
use rustc_middle::ty::{self, TyCtxt};

use tuffy_ir::types::{Annotation, Type};

/// Returns true if the type is i128 or u128.
pub(super) fn is_i128_or_u128(ty: ty::Ty<'_>) -> bool {
    matches!(
        ty.kind(),
        ty::Int(ty::IntTy::I128) | ty::Uint(ty::UintTy::U128)
    )
}

pub(super) fn translate_ty<'tcx>(tcx: TyCtxt<'tcx>, ty: ty::Ty<'tcx>) -> Option<Type> {
    match ty.kind() {
        ty::Bool => Some(Type::Bool),
        ty::Int(ty::IntTy::I8) | ty::Uint(ty::UintTy::U8) => Some(Type::Int),
        ty::Int(ty::IntTy::I16) | ty::Uint(ty::UintTy::U16) => Some(Type::Int),
        ty::Int(ty::IntTy::I32) | ty::Uint(ty::UintTy::U32) | ty::Char => Some(Type::Int),
        ty::Int(ty::IntTy::I64)
        | ty::Uint(ty::UintTy::U64)
        | ty::Int(ty::IntTy::I128)
        | ty::Uint(ty::UintTy::U128)
        | ty::Int(ty::IntTy::Isize)
        | ty::Uint(ty::UintTy::Usize) => Some(Type::Int),
        ty::RawPtr(..) | ty::Ref(..) | ty::FnPtr(..) => Some(Type::Ptr(0)),
        ty::Tuple(fields) if fields.is_empty() => Some(Type::Unit),
        ty::FnDef(..) => Some(Type::Int),
        ty::Never => Some(Type::Int),
        ty::Float(..) => Some(Type::Int),
        ty::Adt(..) | ty::Tuple(..) => {
            // Try to construct Struct type for aggregates
            if let Some(field_types) = struct_field_types(tcx, ty) {
                if !field_types.is_empty() {
                    return Some(Type::Struct(field_types));
                }
            }
            Some(Type::Int)
        }
        ty::Array(..) | ty::Slice(..) | ty::Str => Some(Type::Int),
        // Closure / coroutine-closure structs that capture variables are
        // laid out like regular structs — treat them as Int so they are
        // not skipped as "untranslatable" in call argument handling.
        ty::Closure(..) | ty::CoroutineClosure(..) => Some(Type::Int),
        _ => None,
    }
}

pub(super) fn translate_annotation(ty: ty::Ty<'_>) -> Option<Annotation> {
    match ty.kind() {
        ty::Bool => None,
        ty::Int(ty::IntTy::I8) => Some(Annotation::Signed(8)),
        ty::Uint(ty::UintTy::U8) => Some(Annotation::Unsigned(8)),
        ty::Int(ty::IntTy::I16) => Some(Annotation::Signed(16)),
        ty::Uint(ty::UintTy::U16) => Some(Annotation::Unsigned(16)),
        ty::Int(ty::IntTy::I32) | ty::Char => Some(Annotation::Signed(32)),
        ty::Uint(ty::UintTy::U32) => Some(Annotation::Unsigned(32)),
        ty::Int(ty::IntTy::I64) | ty::Int(ty::IntTy::Isize) => Some(Annotation::Signed(64)),
        ty::Uint(ty::UintTy::U64) | ty::Uint(ty::UintTy::Usize) => Some(Annotation::Unsigned(64)),
        ty::Int(ty::IntTy::I128) => Some(Annotation::Signed(128)),
        ty::Uint(ty::UintTy::U128) => Some(Annotation::Unsigned(128)),
        ty::RawPtr(..) | ty::Ref(..) | ty::FnPtr(..) => None,
        _ => None,
    }
}

/// Extract the type annotation from a MIR operand.
pub(super) fn operand_annotation<'tcx>(
    operand: &Operand<'tcx>,
    mir: &mir::Body<'tcx>,
) -> Option<Annotation> {
    let ty = match operand {
        Operand::Copy(place) | Operand::Move(place) => mir.local_decls[place.local].ty,
        Operand::Constant(c) => c.ty(),
        _ => return None,
    };
    translate_annotation(ty)
}

/// Query the byte offset of field `field_idx` within type `ty`.
pub(super) fn field_offset<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: ty::Ty<'tcx>,
    field_idx: usize,
) -> Option<u64> {
    let typing_env = ty::TypingEnv::fully_monomorphized();
    let layout = tcx.layout_of(typing_env.as_query_input(ty)).ok()?;
    if field_idx >= layout.fields.count() {
        return None;
    }
    Some(layout.fields.offset(field_idx).bytes())
}

/// Query the byte offset of field `field_idx` within a specific enum variant.
pub(super) fn variant_field_offset<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: ty::Ty<'tcx>,
    variant_idx: rustc_abi::VariantIdx,
    field_idx: usize,
) -> Option<u64> {
    let typing_env = ty::TypingEnv::fully_monomorphized();
    let layout = tcx.layout_of(typing_env.as_query_input(ty)).ok()?;
    match &layout.variants {
        rustc_abi::Variants::Multiple { variants, .. } => {
            let variant_layout = &variants[variant_idx];
            if field_idx >= variant_layout.fields.count() {
                return None;
            }
            Some(variant_layout.fields.offset(field_idx).bytes())
        }
        rustc_abi::Variants::Single { .. } => {
            // Single-variant enum — field offsets are the same as the
            // top-level layout.
            if field_idx >= layout.fields.count() {
                return None;
            }
            Some(layout.fields.offset(field_idx).bytes())
        }
        rustc_abi::Variants::Empty => None,
    }
}

/// Query the total byte size of type `ty`.
pub(super) fn type_size<'tcx>(tcx: TyCtxt<'tcx>, ty: ty::Ty<'tcx>) -> Option<u64> {
    let typing_env = ty::TypingEnv::fully_monomorphized();
    let layout = tcx.layout_of(typing_env.as_query_input(ty)).ok()?;
    Some(layout.size.bytes())
}

/// Query the alignment of type `ty` in bytes.
#[allow(dead_code)]
pub(super) fn type_align<'tcx>(tcx: TyCtxt<'tcx>, ty: ty::Ty<'tcx>) -> Option<u64> {
    let typing_env = ty::TypingEnv::fully_monomorphized();
    let layout = tcx.layout_of(typing_env.as_query_input(ty)).ok()?;
    Some(layout.align.abi.bytes())
}

/// Check if a type is a signed integer type.
pub(super) fn is_signed_int(ty: ty::Ty<'_>) -> bool {
    matches!(ty.kind(), ty::Int(_))
}

/// Get the bitwidth of an integer type (for cast operations).
pub(super) fn int_bitwidth(ty: ty::Ty<'_>) -> Option<u32> {
    match ty.kind() {
        ty::Bool => Some(8),
        ty::Int(ty::IntTy::I8) | ty::Uint(ty::UintTy::U8) => Some(8),
        ty::Int(ty::IntTy::I16) | ty::Uint(ty::UintTy::U16) => Some(16),
        ty::Int(ty::IntTy::I32) | ty::Uint(ty::UintTy::U32) | ty::Char => Some(32),
        ty::Int(ty::IntTy::I64)
        | ty::Uint(ty::UintTy::U64)
        | ty::Int(ty::IntTy::Isize)
        | ty::Uint(ty::UintTy::Usize) => Some(64),
        ty::Int(ty::IntTy::I128) | ty::Uint(ty::UintTy::U128) => Some(128),
        _ => None,
    }
}

/// Check if a type is a fat pointer (e.g., &str, &[T], &dyn Trait) that uses two registers at ABI level.
pub(super) fn is_fat_ptr<'tcx>(tcx: TyCtxt<'tcx>, ty: ty::Ty<'tcx>) -> bool {
    match ty.kind() {
        ty::Ref(_, inner, _) | ty::RawPtr(inner, _) => {
            let typing_env = ty::TypingEnv::fully_monomorphized();
            let tail = tcx.struct_tail_for_codegen(*inner, typing_env);
            matches!(tail.kind(), ty::Str | ty::Slice(..) | ty::Dynamic(..))
        }
        _ => false,
    }
}

/// Compute field types for a struct/tuple, including padding fields.
/// Returns Vec<Type> where padding is represented as Type::Byte(N).
/// Returns None if the type is not a struct/tuple or layout computation fails.
pub(super) fn struct_field_types<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: ty::Ty<'tcx>,
) -> Option<Vec<Type>> {
    let typing_env = ty::TypingEnv::fully_monomorphized();
    let layout = tcx.layout_of(typing_env.as_query_input(ty)).ok()?;

    let field_count = layout.fields.count();
    if field_count == 0 {
        return Some(Vec::new());
    }

    let mut result = Vec::new();
    let mut current_offset = 0u64;

    for field_idx in 0..field_count {
        let field_offset = layout.fields.offset(field_idx).bytes();

        // Insert padding if there's a gap
        if field_offset > current_offset {
            let padding_size = (field_offset - current_offset) as u32;
            result.push(Type::Byte(padding_size));
            current_offset = field_offset;
        }

        // Get the field type from the MIR
        let field_ty = match ty.kind() {
            ty::Adt(def, args) => {
                // Only decompose single-variant ADTs (structs/single-variant enums).
                // Multi-variant enums have layout fields (e.g. discriminant) that
                // don't correspond to variant fields.
                if def.variants().len() != 1 {
                    return None;
                }
                let variant = &def.variants()[rustc_abi::VariantIdx::from_u32(0)];
                if field_idx >= variant.fields.len() {
                    return None;
                }
                variant.fields[rustc_abi::FieldIdx::from_usize(field_idx)]
                    .ty(tcx, args)
            }
            ty::Tuple(fields) => {
                if field_idx < fields.len() {
                    fields[field_idx]
                } else {
                    return None;
                }
            }
            _ => return None,
        };

        // Translate the field type
        if let Some(ir_ty) = translate_ty(tcx, field_ty) {
            result.push(ir_ty);
            // Update offset to after this field
            if let Ok(field_layout) = tcx.layout_of(typing_env.as_query_input(field_ty)) {
                current_offset = field_offset + field_layout.size.bytes();
            }
        } else {
            return None;
        }
    }

    // Add trailing padding if needed
    let total_size = layout.size.bytes();
    if current_offset < total_size {
        let trailing_padding = (total_size - current_offset) as u32;
        result.push(Type::Byte(trailing_padding));
    }

    Some(result)
}
