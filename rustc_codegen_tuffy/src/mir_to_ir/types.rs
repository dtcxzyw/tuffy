//! Type translation utilities for MIR → IR conversion.

use rustc_abi::BackendRepr;
use rustc_middle::mir::{self, Operand};
use rustc_middle::ty::{self, TyCtxt};

use tuffy_ir::types::{Annotation, FloatType, Type};

/// Coarse-grained ABI representation of a Rust type, mirroring BackendRepr.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum ReprKind {
    /// Zero-sized type — no data to pass or return.
    Zst,
    /// Single register (int, float, pointer, i128/u128).
    Scalar,
    /// Two registers (fat pointer: data ptr + length/vtable).
    ScalarPair,
    /// Passed via memory pointer (large structs, arrays, etc.).
    Memory,
}


pub(super) fn repr_kind<'tcx>(tcx: TyCtxt<'tcx>, ty: ty::Ty<'tcx>) -> ReprKind {
    let typing_env = ty::TypingEnv::fully_monomorphized();
    let Ok(layout) = tcx.layout_of(typing_env.as_query_input(ty)) else {
        return ReprKind::Memory;
    };
    if layout.is_zst() {
        return ReprKind::Zst;
    }
    match layout.backend_repr {
        BackendRepr::Scalar(_) => ReprKind::Scalar,
        BackendRepr::ScalarPair(_, _) => ReprKind::ScalarPair,
        _ => ReprKind::Memory,
    }
}


pub(super) fn translate_ty<'tcx>(_tcx: TyCtxt<'tcx>, ty: ty::Ty<'tcx>) -> Option<Type> {
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
        ty::Float(ty::FloatTy::F16) => Some(Type::Float(FloatType::F16)),
        ty::Float(ty::FloatTy::F32) => Some(Type::Float(FloatType::F32)),
        ty::Float(ty::FloatTy::F64) => Some(Type::Float(FloatType::F64)),
        ty::Float(ty::FloatTy::F128) => Some(Type::Int), // f128 not yet supported
        ty::Adt(..) | ty::Tuple(..) => Some(Type::Int),
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

/// Return true if the type contains any float fields (recursively).
/// Used to decide whether a composite value passed by value should be
/// annotated as u128 for two-slot ABI handling.
pub(super) fn ty_contains_float<'tcx>(tcx: TyCtxt<'tcx>, ty: ty::Ty<'tcx>) -> bool {
    match ty.kind() {
        ty::Float(_) => true,
        ty::Array(elem, _) => ty_contains_float(tcx, *elem),
        ty::Tuple(fields) => fields.iter().any(|f| ty_contains_float(tcx, f)),
        ty::Adt(def, args) => {
            let typing_env = ty::TypingEnv::fully_monomorphized();
            def.variants().iter().any(|v| {
                v.fields.iter().any(|f| {
                    let fty = f.ty(tcx, args);
                    let fty = tcx.normalize_erasing_regions(typing_env, fty);
                    ty_contains_float(tcx, fty)
                })
            })
        }
        _ => false,
    }
}
