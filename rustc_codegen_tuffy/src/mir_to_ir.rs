//! MIR → tuffy IR translation.
//!
//! Translates rustc MIR into tuffy IR, supporting basic arithmetic,
//! control flow (branches, SwitchInt), and comparison operations.

use std::collections::HashMap;

use rustc_middle::mir::{
    self, BasicBlock, BinOp, CastKind, Operand, Place, PlaceElem, Rvalue, StatementKind,
    TerminatorKind,
};
use rustc_middle::ty::{self, Instance, TyCtxt, TypeVisitableExt};

use tuffy_codegen::{AbiMetadataBox, CodegenSession};
use tuffy_ir::builder::Builder;
use tuffy_ir::function::{Function, RegionKind};
use tuffy_ir::instruction::{ICmpOp, Operand as IrOperand, Origin};
use tuffy_ir::types::{Annotation, Type};
use tuffy_ir::value::{BlockRef, ValueRef};

/// Result of MIR → IR translation.
pub struct TranslationResult {
    pub func: Function,
    /// Maps IR instruction index → callee symbol name for Call instructions.
    pub call_targets: HashMap<u32, String>,
    /// Maps IR instruction index → static data symbol name (for address loads).
    pub static_refs: HashMap<u32, String>,
    /// Static data blobs to emit in .rodata.
    pub static_data: Vec<(String, Vec<u8>)>,
    /// Target-specific ABI metadata (e.g., secondary return register info).
    pub abi_metadata: AbiMetadataBox,
}

/// Translate a single MIR function instance to tuffy IR.
pub fn translate_function<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: Instance<'tcx>,
    session: &CodegenSession,
) -> Option<TranslationResult> {
    let inst_ty = instance.ty(tcx, ty::TypingEnv::fully_monomorphized());
    if !inst_ty.is_fn() {
        return None;
    }

    // Skip partially substituted polymorphic instances — the symbol mangler
    // will panic if generic parameters are still present.
    if instance.args.has_non_region_param() {
        return None;
    }

    let mir = tcx.instance_mir(instance.def);
    let name = tcx.symbol_name(instance).name.to_string();
    let sig = inst_ty.fn_sig(tcx);
    let sig = tcx.instantiate_bound_regions_with_erased(sig);
    let sig = tcx
        .try_normalize_erasing_regions(ty::TypingEnv::fully_monomorphized(), sig)
        .ok()?;

    let params: Vec<Type> = sig
        .inputs()
        .iter()
        .filter_map(|ty| translate_ty(*ty))
        .collect();
    let param_anns: Vec<Option<Annotation>> = sig
        .inputs()
        .iter()
        .filter_map(|ty| translate_ty(*ty).map(|_| translate_annotation(*ty)))
        .collect();
    let ret_ty = translate_ty(sig.output());
    let ret_ann = translate_annotation(sig.output());

    let mut func = Function::new(&name, params, param_anns, ret_ty, ret_ann);
    let mut builder = Builder::new(&mut func);
    let mut locals = LocalMap::new(mir.local_decls.len());
    let mut fat_locals = FatLocalMap::new();
    let mut stack_locals = StackLocalSet::new(mir.local_decls.len());
    let mut call_targets: HashMap<u32, String> = HashMap::new();
    let mut static_refs: HashMap<u32, String> = HashMap::new();
    let mut static_data: Vec<(String, Vec<u8>)> = Vec::new();
    let mut abi_metadata = session.new_metadata();

    // Detect whether this function returns a large struct via sret.
    let ret_mir_ty = sig.output();
    let use_sret = needs_indirect_return(tcx, ret_mir_ty);
    // Will hold the original sret pointer passed by the caller (callee side).
    let mut sret_ptr: Option<ValueRef> = None;

    let root = builder.create_region(RegionKind::Function);
    builder.enter_region(root);

    // Create IR blocks for all MIR basic blocks upfront so branches can
    // reference target blocks before they are translated.
    let mut block_map = BlockMap::new(mir.basic_blocks.len());
    for (bb, _) in mir.basic_blocks.iter_enumerated() {
        let ir_block = builder.create_block();
        block_map.set(bb, ir_block);
    }

    // Emit params into the entry block.
    let entry = block_map.get(BasicBlock::from_u32(0));
    builder.switch_to_block(entry);
    translate_params(
        tcx,
        mir,
        &mut builder,
        &mut locals,
        &mut fat_locals,
        &mut stack_locals,
        &mut sret_ptr,
        use_sret,
    );

    // Translate each basic block.
    for (bb, bb_data) in mir.basic_blocks.iter_enumerated() {
        let ir_block = block_map.get(bb);
        builder.switch_to_block(ir_block);

        for stmt in &bb_data.statements {
            translate_statement(
                tcx,
                stmt,
                mir,
                &mut builder,
                &mut locals,
                &mut fat_locals,
                &mut stack_locals,
                &mut static_refs,
                &mut static_data,
            );
        }
        if let Some(ref term) = bb_data.terminator {
            translate_terminator(
                tcx,
                term,
                mir,
                &mut builder,
                &mut locals,
                &mut fat_locals,
                &mut stack_locals,
                &block_map,
                &mut call_targets,
                &mut static_refs,
                &mut static_data,
                &mut abi_metadata,
                sret_ptr,
                use_sret,
            );
        }
    }

    builder.exit_region();

    Some(TranslationResult {
        func,
        call_targets,
        static_refs,
        static_data,
        abi_metadata,
    })
}

struct LocalMap {
    values: Vec<Option<ValueRef>>,
}

impl LocalMap {
    fn new(count: usize) -> Self {
        Self {
            values: vec![None; count],
        }
    }

    fn set(&mut self, local: mir::Local, val: ValueRef) {
        self.values[local.as_usize()] = Some(val);
    }

    fn get(&self, local: mir::Local) -> Option<ValueRef> {
        self.values[local.as_usize()]
    }
}

/// Tracks the "high" component of fat pointer locals (e.g., length for &str).
struct FatLocalMap {
    /// Maps MIR local index → high ValueRef (e.g., slice length).
    values: HashMap<usize, ValueRef>,
}

impl FatLocalMap {
    fn new() -> Self {
        Self {
            values: HashMap::new(),
        }
    }

    fn set(&mut self, local: mir::Local, val: ValueRef) {
        self.values.insert(local.as_usize(), val);
    }

    fn get(&self, local: mir::Local) -> Option<ValueRef> {
        self.values.get(&local.as_usize()).copied()
    }
}

fn translate_ty(ty: ty::Ty<'_>) -> Option<Type> {
    match ty.kind() {
        ty::Int(ty::IntTy::I8) | ty::Uint(ty::UintTy::U8) | ty::Bool => Some(Type::Byte(1)),
        ty::Int(ty::IntTy::I16) | ty::Uint(ty::UintTy::U16) => Some(Type::Int),
        ty::Int(ty::IntTy::I32) | ty::Uint(ty::UintTy::U32) | ty::Char => Some(Type::Int),
        ty::Int(ty::IntTy::I64)
        | ty::Uint(ty::UintTy::U64)
        | ty::Int(ty::IntTy::I128)
        | ty::Uint(ty::UintTy::U128)
        | ty::Int(ty::IntTy::Isize)
        | ty::Uint(ty::UintTy::Usize) => Some(Type::Int),
        ty::RawPtr(..) | ty::Ref(..) | ty::FnPtr(..) => Some(Type::Ptr(0)),
        ty::Tuple(fields) if fields.is_empty() => Some(Type::Int),
        ty::FnDef(..) => Some(Type::Int),
        ty::Never => Some(Type::Int),
        ty::Adt(..) | ty::Tuple(..) | ty::Array(..) | ty::Slice(..) | ty::Str => Some(Type::Int),
        _ => None,
    }
}

fn translate_annotation(ty: ty::Ty<'_>) -> Option<Annotation> {
    match ty.kind() {
        ty::Bool => Some(Annotation::Unsigned(8)),
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
        ty::RawPtr(..) | ty::Ref(..) | ty::FnPtr(..) => Some(Annotation::Unsigned(64)),
        _ => None,
    }
}

/// Extract the type annotation from a MIR operand.
fn operand_annotation<'tcx>(operand: &Operand<'tcx>, mir: &mir::Body<'tcx>) -> Option<Annotation> {
    let ty = match operand {
        Operand::Copy(place) | Operand::Move(place) => mir.local_decls[place.local].ty,
        Operand::Constant(c) => c.ty(),
        _ => return None,
    };
    translate_annotation(ty)
}

/// Query the byte offset of field `field_idx` within type `ty`.
fn field_offset<'tcx>(tcx: TyCtxt<'tcx>, ty: ty::Ty<'tcx>, field_idx: usize) -> Option<u64> {
    let typing_env = ty::TypingEnv::fully_monomorphized();
    let layout = tcx.layout_of(typing_env.as_query_input(ty)).ok()?;
    if field_idx >= layout.fields.count() {
        return None;
    }
    Some(layout.fields.offset(field_idx).bytes())
}

/// Query the total byte size of type `ty`.
fn type_size<'tcx>(tcx: TyCtxt<'tcx>, ty: ty::Ty<'tcx>) -> Option<u64> {
    let typing_env = ty::TypingEnv::fully_monomorphized();
    let layout = tcx.layout_of(typing_env.as_query_input(ty)).ok()?;
    Some(layout.size.bytes())
}

/// Query the alignment of type `ty` in bytes.
fn type_align<'tcx>(tcx: TyCtxt<'tcx>, ty: ty::Ty<'tcx>) -> Option<u64> {
    let typing_env = ty::TypingEnv::fully_monomorphized();
    let layout = tcx.layout_of(typing_env.as_query_input(ty)).ok()?;
    Some(layout.align.abi.bytes())
}

/// Check if a type needs indirect return (sret) per System V AMD64 ABI.
/// Types larger than 16 bytes are returned via a hidden pointer parameter.
fn needs_indirect_return<'tcx>(tcx: TyCtxt<'tcx>, ty: ty::Ty<'tcx>) -> bool {
    if ty.is_unit() || ty.is_never() {
        return false;
    }
    type_size(tcx, ty).is_some_and(|size| size > 16)
}

/// Check if a type is a signed integer type.
fn is_signed_int(ty: ty::Ty<'_>) -> bool {
    matches!(ty.kind(), ty::Int(_))
}

/// Get the bitwidth of an integer type (for cast operations).
fn int_bitwidth(ty: ty::Ty<'_>) -> Option<u32> {
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

/// Tracks which MIR locals hold stack slot addresses (aggregate/spilled values)
/// rather than scalar values in registers.
struct StackLocalSet {
    is_stack: Vec<bool>,
}

impl StackLocalSet {
    fn new(count: usize) -> Self {
        Self {
            is_stack: vec![false; count],
        }
    }

    fn mark(&mut self, local: mir::Local) {
        self.is_stack[local.as_usize()] = true;
    }

    fn is_stack(&self, local: mir::Local) -> bool {
        self.is_stack[local.as_usize()]
    }
}

#[allow(clippy::too_many_arguments)]
fn translate_params<'tcx>(
    tcx: TyCtxt<'tcx>,
    mir: &mir::Body<'tcx>,
    builder: &mut Builder<'_>,
    locals: &mut LocalMap,
    fat_locals: &mut FatLocalMap,
    stack_locals: &mut StackLocalSet,
    sret_ptr: &mut Option<ValueRef>,
    use_sret: bool,
) {
    let mut abi_idx: u32 = 0;

    // If the function returns a large struct, the caller passes a hidden
    // pointer as the first argument (sret). We consume it here and use it
    // as the storage for local _0.
    if use_sret {
        let ret_ty = mir.local_decls[mir::Local::from_usize(0)].ty;
        let size = type_size(tcx, ret_ty).unwrap_or(8);
        let hidden = builder.param(abi_idx, Type::Ptr(0), None, Origin::synthetic());
        abi_idx += 1;

        // Allocate a local stack slot for _0 so MIR stores go somewhere real.
        let slot = builder.stack_slot(size as u32, Origin::synthetic());
        locals.set(mir::Local::from_usize(0), slot);
        stack_locals.mark(mir::Local::from_usize(0));

        // Remember the caller-provided sret pointer for the Return terminator.
        *sret_ptr = Some(hidden);
    }

    for i in 0..mir.arg_count {
        let local = mir::Local::from_usize(i + 1);
        let ty = mir.local_decls[local].ty;
        let ann = translate_annotation(ty);
        let val = builder.param(abi_idx, Type::Int, ann, Origin::synthetic());
        locals.set(local, val);
        abi_idx += 1;

        // Fat pointer types (&str, &[T]) occupy two ABI registers (ptr + metadata).
        if is_fat_ptr(ty) {
            let meta_val = builder.param(abi_idx, Type::Int, None, Origin::synthetic());
            fat_locals.set(local, meta_val);
            abi_idx += 1;
        }
    }
}

/// Check if a type is a fat pointer (e.g., &str, &[T]) that uses two registers at ABI level.
fn is_fat_ptr(ty: ty::Ty<'_>) -> bool {
    match ty.kind() {
        ty::Ref(_, inner, _) | ty::RawPtr(inner, _) => {
            matches!(inner.kind(), ty::Str | ty::Slice(..))
        }
        _ => false,
    }
}

/// Map from MIR BasicBlock to IR BlockRef.
struct BlockMap {
    blocks: Vec<Option<BlockRef>>,
}

impl BlockMap {
    fn new(count: usize) -> Self {
        Self {
            blocks: vec![None; count],
        }
    }

    fn set(&mut self, bb: BasicBlock, block: BlockRef) {
        self.blocks[bb.as_usize()] = Some(block);
    }

    fn get(&self, bb: BasicBlock) -> BlockRef {
        self.blocks[bb.as_usize()].expect("block not mapped")
    }
}

/// Compute the address of a Place (base + projections).
///
/// Walks the projection chain and returns a ValueRef representing the pointer
/// to the final memory location. For locals with no projections that are
/// stack-allocated, returns the local's value directly (which is already a pointer).
fn translate_place_to_addr<'tcx>(
    tcx: TyCtxt<'tcx>,
    place: &Place<'tcx>,
    mir: &mir::Body<'tcx>,
    builder: &mut Builder<'_>,
    locals: &LocalMap,
    stack_locals: &StackLocalSet,
) -> Option<ValueRef> {
    let mut addr = locals.get(place.local)?;
    let mut cur_ty = mir.local_decls[place.local].ty;

    // If the base local is not stack-allocated and has projections starting
    // with something other than Deref, we need to spill it first.
    // But for now, we handle each projection element in sequence.

    for elem in place.projection.iter() {
        match elem {
            PlaceElem::Deref => {
                // The current value is a pointer; load through it to get the
                // pointee address. But since we want the *address* of the
                // deref'd location, the current value IS the address.
                // If the local is stack-allocated, addr is already a pointer
                // to the slot; we need to load the actual pointer value from it.
                if !place.projection.len() == 1 || !stack_locals.is_stack(place.local) {
                    // addr already holds the pointer value — it IS the address
                    // of the deref'd location. Nothing to do.
                }
                // Update cur_ty to the pointee type.
                cur_ty = match cur_ty.kind() {
                    ty::Ref(_, inner, _) | ty::RawPtr(inner, _) => *inner,
                    _ => return None,
                };
            }
            PlaceElem::Field(field_idx, field_ty) => {
                let offset = field_offset(tcx, cur_ty, field_idx.as_usize())?;
                if offset != 0 {
                    let off_val = builder.iconst(offset as i64, Origin::synthetic());
                    addr = builder.ptradd(addr.into(), off_val.into(), 0, Origin::synthetic());
                }
                cur_ty = field_ty;
            }
            PlaceElem::Index(local) => {
                let idx_val = locals.get(local)?;
                let elem_size = type_size(
                    tcx,
                    match cur_ty.kind() {
                        ty::Array(elem_ty, _) => *elem_ty,
                        ty::Slice(elem_ty) => *elem_ty,
                        _ => return None,
                    },
                )?;
                let size_val = builder.iconst(elem_size as i64, Origin::synthetic());
                let byte_offset =
                    builder.mul(idx_val.into(), size_val.into(), None, Origin::synthetic());
                addr = builder.ptradd(addr.into(), byte_offset.into(), 0, Origin::synthetic());
                cur_ty = match cur_ty.kind() {
                    ty::Array(elem_ty, _) | ty::Slice(elem_ty) => *elem_ty,
                    _ => return None,
                };
            }
            PlaceElem::Downcast(_, _) => {
                // Downcast doesn't change the address, only the type interpretation.
                // We keep the same address and update cur_ty via the variant.
            }
            PlaceElem::ConstantIndex {
                offset, from_end, ..
            } => {
                let elem_ty = match cur_ty.kind() {
                    ty::Array(elem_ty, _) | ty::Slice(elem_ty) => *elem_ty,
                    _ => return None,
                };
                let elem_size = type_size(tcx, elem_ty)?;
                if !from_end {
                    let byte_off = offset * elem_size;
                    if byte_off != 0 {
                        let off_val = builder.iconst(byte_off as i64, Origin::synthetic());
                        addr = builder.ptradd(addr.into(), off_val.into(), 0, Origin::synthetic());
                    }
                }
                // from_end case would need array length; skip for now.
                cur_ty = elem_ty;
            }
            _ => {
                // OpaqueCast, Subslice, UnwrapUnsafeBinder — not yet handled.
                return None;
            }
        }
    }
    Some(addr)
}

/// Read the value at a Place (base + projections).
///
/// If the place has no projections, returns the local's value directly.
/// If it has projections, computes the address and emits a Load.
fn translate_place_to_value<'tcx>(
    tcx: TyCtxt<'tcx>,
    place: &Place<'tcx>,
    mir: &mir::Body<'tcx>,
    builder: &mut Builder<'_>,
    locals: &LocalMap,
    stack_locals: &StackLocalSet,
) -> Option<ValueRef> {
    if place.projection.is_empty() {
        return locals.get(place.local);
    }
    // Non-stack scalar with Field(0) projection (e.g., CheckedOp tuple `.0`):
    // the local already holds the scalar value, no load needed.
    if !stack_locals.is_stack(place.local)
        && place.projection.len() == 1
        && matches!(place.projection[0], PlaceElem::Field(idx, _) if idx.as_usize() == 0)
    {
        return locals.get(place.local);
    }
    let addr = translate_place_to_addr(tcx, place, mir, builder, locals, stack_locals)?;
    Some(builder.load(addr.into(), Type::Int, None, Origin::synthetic()))
}

#[allow(clippy::too_many_arguments)]
fn translate_statement<'tcx>(
    tcx: TyCtxt<'tcx>,
    stmt: &mir::Statement<'tcx>,
    mir: &mir::Body<'tcx>,
    builder: &mut Builder<'_>,
    locals: &mut LocalMap,
    fat_locals: &mut FatLocalMap,
    stack_locals: &mut StackLocalSet,
    static_refs: &mut HashMap<u32, String>,
    static_data: &mut Vec<(String, Vec<u8>)>,
) {
    match &stmt.kind {
        StatementKind::Assign(box (place, rvalue)) => {
            if let Some(val) = translate_rvalue(
                tcx,
                rvalue,
                place,
                mir,
                builder,
                locals,
                fat_locals,
                stack_locals,
                static_refs,
                static_data,
            ) {
                if place.projection.is_empty() {
                    locals.set(place.local, val);
                } else {
                    // Projected destination: compute address and emit Store.
                    if let Some(addr) =
                        translate_place_to_addr(tcx, place, mir, builder, locals, stack_locals)
                    {
                        builder.store(val.into(), addr.into(), Origin::synthetic());
                    }
                }
            }
            // Check if the rvalue produces a fat pointer (e.g., &str from ConstValue::Slice).
            if let Some(fat_val) = extract_fat_component(
                tcx,
                rvalue,
                mir,
                builder,
                locals,
                fat_locals,
                stack_locals,
                static_refs,
                static_data,
            ) {
                fat_locals.set(place.local, fat_val);
            }
        }
        StatementKind::StorageLive(_) | StatementKind::StorageDead(_) | StatementKind::Nop => {}
        _ => {}
    }
}

/// Extract the "high" component of a fat pointer rvalue.
///
/// Handles: ConstValue::Slice, Use/Cast of fat locals, and multi-field Aggregate.
#[allow(clippy::too_many_arguments)]
fn extract_fat_component<'tcx>(
    tcx: TyCtxt<'tcx>,
    rvalue: &Rvalue<'tcx>,
    mir: &mir::Body<'tcx>,
    builder: &mut Builder<'_>,
    locals: &mut LocalMap,
    fat_locals: &FatLocalMap,
    stack_locals: &StackLocalSet,
    static_refs: &mut HashMap<u32, String>,
    static_data: &mut Vec<(String, Vec<u8>)>,
) -> Option<ValueRef> {
    match rvalue {
        // Constant slice: extract the length metadata.
        Rvalue::Use(Operand::Constant(c)) => {
            if let mir::Const::Val(mir::ConstValue::Slice { alloc_id: _, meta }, _) = c.const_ {
                Some(builder.iconst(meta as i64, Origin::synthetic()))
            } else {
                None
            }
        }
        // Use of a fat local: propagate the fat component.
        Rvalue::Use(Operand::Copy(place) | Operand::Move(place)) => fat_locals.get(place.local),
        // Cast (Transmute, PtrToPtr, etc.) of a fat local: propagate.
        Rvalue::Cast(_, Operand::Copy(place) | Operand::Move(place), _) => {
            fat_locals.get(place.local)
        }
        Rvalue::Cast(..) => None,
        // Multi-field Aggregate: second field becomes the fat component.
        Rvalue::Aggregate(_, operands) if operands.len() >= 2 => {
            let second_op = operands.iter().nth(1).unwrap();
            translate_operand(
                tcx,
                second_op,
                mir,
                builder,
                locals,
                stack_locals,
                static_refs,
                static_data,
            )
        }
        _ => None,
    }
}

#[allow(clippy::too_many_arguments)]
fn translate_terminator<'tcx>(
    tcx: TyCtxt<'tcx>,
    term: &mir::Terminator<'tcx>,
    mir: &mir::Body<'tcx>,
    builder: &mut Builder<'_>,
    locals: &mut LocalMap,
    fat_locals: &mut FatLocalMap,
    stack_locals: &mut StackLocalSet,
    block_map: &BlockMap,
    call_targets: &mut HashMap<u32, String>,
    static_refs: &mut HashMap<u32, String>,
    static_data: &mut Vec<(String, Vec<u8>)>,
    abi_metadata: &mut AbiMetadataBox,
    sret_ptr: Option<ValueRef>,
    use_sret: bool,
) {
    match &term.kind {
        TerminatorKind::Return => {
            let ret_local = mir::Local::from_usize(0);

            if use_sret {
                // Large struct return: copy _0's data to the caller's sret pointer,
                // then return the sret pointer in RAX.
                let sret = sret_ptr.expect("sret_ptr must be set when use_sret is true");
                let src = locals.get(ret_local).expect("return local _0 must be set");
                let ret_ty = mir.local_decls[ret_local].ty;
                let size = type_size(tcx, ret_ty).unwrap_or(8);

                // Word-by-word copy from local _0's stack slot to sret pointer.
                let num_words = size.div_ceil(8);
                for i in 0..num_words {
                    let byte_off = i * 8;
                    let load_addr = if byte_off == 0 {
                        src
                    } else {
                        let off = builder.iconst(byte_off as i64, Origin::synthetic());
                        builder.ptradd(src.into(), off.into(), 0, Origin::synthetic())
                    };
                    let word = builder.load(load_addr.into(), Type::Int, None, Origin::synthetic());
                    let store_addr = if byte_off == 0 {
                        sret
                    } else {
                        let off = builder.iconst(byte_off as i64, Origin::synthetic());
                        builder.ptradd(sret.into(), off.into(), 0, Origin::synthetic())
                    };
                    builder.store(word.into(), store_addr.into(), Origin::synthetic());
                }

                // Return the sret pointer in RAX (System V convention).
                builder.ret(Some(sret.into()), Origin::synthetic());
            } else if stack_locals.is_stack(ret_local) {
                // Stack-allocated return (e.g., 16-byte struct built via Aggregate).
                // Load the actual data from the stack slot instead of returning
                // the slot address (which would be a dangling pointer).
                let slot = locals.get(ret_local).expect("return local _0 must be set");
                let ret_ty = mir.local_decls[ret_local].ty;
                let size = type_size(tcx, ret_ty).unwrap_or(8);

                // First 8 bytes → RAX.
                let word0 = builder.load(slot.into(), Type::Int, None, Origin::synthetic());

                if size > 8 {
                    // Second 8 bytes → secondary return register.
                    let off = builder.iconst(8, Origin::synthetic());
                    let addr1 = builder.ptradd(slot.into(), off.into(), 0, Origin::synthetic());
                    let word1 = builder.load(addr1.into(), Type::Int, None, Origin::synthetic());
                    let dummy = builder.iconst(0, Origin::synthetic());
                    abi_metadata.mark_secondary_return_move(dummy.index(), word1.index());
                }

                builder.ret(Some(word0.into()), Origin::synthetic());
            } else {
                // Normal scalar return.
                if let Some(fat_val) = fat_locals.get(ret_local) {
                    let dummy = builder.iconst(0, Origin::synthetic());
                    abi_metadata.mark_secondary_return_move(dummy.index(), fat_val.index());
                }
                let val = locals.values[ret_local.as_usize()];
                builder.ret(val.map(|v| v.into()), Origin::synthetic());
            }
        }
        TerminatorKind::Goto { target } => {
            let target_block = block_map.get(*target);
            builder.br(target_block, vec![], Origin::synthetic());
        }
        TerminatorKind::SwitchInt { discr, targets } => {
            translate_switch_int(
                tcx,
                discr,
                targets,
                mir,
                builder,
                locals,
                stack_locals,
                block_map,
                static_refs,
                static_data,
            );
        }
        TerminatorKind::Assert {
            cond,
            expected,
            target,
            ..
        } => {
            // Assert: if cond != expected, panic. For now, just branch to
            // the success target unconditionally (we'll add panic support later).
            let _ = (cond, expected);
            let target_block = block_map.get(*target);
            builder.br(target_block, vec![], Origin::synthetic());
        }
        TerminatorKind::Unreachable => {
            builder.unreachable(Origin::synthetic());
        }
        TerminatorKind::Drop { target, .. } => {
            // Skip drop glue for now — just branch to the target.
            let target_block = block_map.get(*target);
            builder.br(target_block, vec![], Origin::synthetic());
        }
        TerminatorKind::FalseEdge { real_target, .. } => {
            let target_block = block_map.get(*real_target);
            builder.br(target_block, vec![], Origin::synthetic());
        }
        TerminatorKind::FalseUnwind { real_target, .. } => {
            let target_block = block_map.get(*real_target);
            builder.br(target_block, vec![], Origin::synthetic());
        }
        TerminatorKind::Call {
            func,
            args,
            destination,
            target,
            ..
        } => {
            // Resolve callee symbol name from the function operand's type.
            let callee_sym = resolve_call_symbol(tcx, func);

            // Check if the callee returns a large struct (needs sret on caller side).
            let dest_ty = mir.local_decls[destination.local].ty;
            let dest_size = type_size(tcx, dest_ty);
            let callee_sret = needs_indirect_return(tcx, dest_ty);

            // Translate arguments to IR operands, decomposing fat pointers.
            let mut ir_args: Vec<tuffy_ir::instruction::Operand> = Vec::new();

            // If callee uses sret, allocate a stack slot and prepend as first arg.
            let sret_slot = if callee_sret {
                let size = type_size(tcx, dest_ty).unwrap_or(8);
                let slot = builder.stack_slot(size as u32, Origin::synthetic());
                ir_args.push(slot.into());
                Some(slot)
            } else {
                None
            };

            for arg in args {
                if let Some(v) = translate_operand(
                    tcx,
                    &arg.node,
                    mir,
                    builder,
                    locals,
                    stack_locals,
                    static_refs,
                    static_data,
                ) {
                    // Check if this argument is a stack-allocated local that
                    // should be decomposed into register-sized words (≤16 bytes).
                    let decomposed = if let Operand::Copy(place) | Operand::Move(place) = &arg.node
                    {
                        if place.projection.is_empty() && stack_locals.is_stack(place.local) {
                            let arg_ty = mir.local_decls[place.local].ty;
                            let arg_size = type_size(tcx, arg_ty).unwrap_or(0);
                            if arg_size > 0 && arg_size <= 16 {
                                // Load word(s) from the stack slot and pass in registers.
                                let word0 =
                                    builder.load(v.into(), Type::Int, None, Origin::synthetic());
                                ir_args.push(word0.into());
                                if arg_size > 8 {
                                    let off = builder.iconst(8, Origin::synthetic());
                                    let addr1 = builder.ptradd(
                                        v.into(),
                                        off.into(),
                                        0,
                                        Origin::synthetic(),
                                    );
                                    let word1 = builder.load(
                                        addr1.into(),
                                        Type::Int,
                                        None,
                                        Origin::synthetic(),
                                    );
                                    ir_args.push(word1.into());
                                }
                                true
                            } else {
                                false
                            }
                        } else {
                            false
                        }
                    } else {
                        false
                    };

                    if !decomposed {
                        ir_args.push(v.into());
                        // If this arg is a Copy/Move of a fat local, also pass the high part.
                        if let Operand::Copy(place) | Operand::Move(place) = &arg.node
                            && let Some(fat_v) = fat_locals.get(place.local)
                        {
                            ir_args.push(fat_v.into());
                        }
                        // If this arg is a constant slice, the length was emitted
                        // right after the pointer. Check if it's in the constant.
                        if let Operand::Constant(c) = &arg.node
                            && let mir::Const::Val(mir::ConstValue::Slice { meta, .. }, _) =
                                c.const_
                        {
                            let len_val = builder.iconst(meta as i64, Origin::synthetic());
                            ir_args.push(len_val.into());
                        }
                    }
                }
            }

            // Emit a Call IR instruction. The callee operand is a dummy const
            // (the actual symbol is tracked in call_targets).
            let callee_val = builder.iconst(0, Origin::synthetic());
            let call_vref = builder.call(
                callee_val.into(),
                ir_args,
                Type::Int,
                None,
                Origin::synthetic(),
            );

            // Record the mapping from instruction index to symbol name.
            if let Some(sym) = callee_sym {
                call_targets.insert(call_vref.index(), sym);
            }

            if callee_sret {
                // For sret calls, the result is in the stack slot we allocated.
                // The destination local becomes a pointer to that slot.
                let slot = sret_slot.unwrap();
                locals.set(destination.local, slot);
                stack_locals.mark(destination.local);
                // No RDX capture needed for sret calls.
            } else if dest_size.unwrap_or(0) > 8 {
                // Two-register return (9-16 bytes): RAX has first word,
                // RDX has second word. Reconstruct into a stack slot so
                // downstream code gets a valid pointer to the struct.
                let size = dest_size.unwrap();
                let slot = builder.stack_slot(size as u32, Origin::synthetic());
                builder.store(call_vref.into(), slot.into(), Origin::synthetic());

                let rdx_val = builder.iconst(0, Origin::synthetic());
                abi_metadata.mark_secondary_return_capture(rdx_val.index());
                let off = builder.iconst(8, Origin::synthetic());
                let addr1 = builder.ptradd(slot.into(), off.into(), 0, Origin::synthetic());
                builder.store(rdx_val.into(), addr1.into(), Origin::synthetic());

                locals.set(destination.local, slot);
                stack_locals.mark(destination.local);
            } else {
                // Scalar return (≤ 8 bytes): store directly.
                locals.set(destination.local, call_vref);

                // Capture secondary return register for fat pointer returns (e.g., &str).
                let rdx_val = builder.iconst(0, Origin::synthetic());
                abi_metadata.mark_secondary_return_capture(rdx_val.index());
                fat_locals.set(destination.local, rdx_val);
            }

            // Branch to the continuation block if present.
            if let Some(target_bb) = target {
                let target_block = block_map.get(*target_bb);
                builder.br(target_block, vec![], Origin::synthetic());
            }
        }
        _ => {}
    }
}

#[allow(clippy::too_many_arguments)]
fn translate_switch_int<'tcx>(
    tcx: TyCtxt<'tcx>,
    discr: &Operand<'tcx>,
    targets: &mir::SwitchTargets,
    mir: &mir::Body<'tcx>,
    builder: &mut Builder<'_>,
    locals: &mut LocalMap,
    stack_locals: &StackLocalSet,
    block_map: &BlockMap,
    static_refs: &mut HashMap<u32, String>,
    static_data: &mut Vec<(String, Vec<u8>)>,
) {
    let discr_val = match translate_operand(
        tcx,
        discr,
        mir,
        builder,
        locals,
        stack_locals,
        static_refs,
        static_data,
    ) {
        Some(v) => v,
        None => return,
    };

    let all_targets: Vec<_> = targets.iter().collect();
    let otherwise = targets.otherwise();

    if all_targets.len() == 1 {
        // Two-way branch: compare discriminant with the single value.
        let (test_val, target_bb) = all_targets[0];
        let const_val = builder.iconst(test_val as i64, Origin::synthetic());
        let cmp = builder.icmp(
            ICmpOp::Eq,
            discr_val.into(),
            const_val.into(),
            Origin::synthetic(),
        );
        let then_block = block_map.get(target_bb);
        let else_block = block_map.get(otherwise);
        builder.brif(
            cmp.into(),
            then_block,
            vec![],
            else_block,
            vec![],
            Origin::synthetic(),
        );
    } else {
        // Multi-way: chain of brif comparisons, fallthrough to otherwise.
        for (test_val, target_bb) in &all_targets {
            let const_val = builder.iconst(*test_val as i64, Origin::synthetic());
            let cmp = builder.icmp(
                ICmpOp::Eq,
                discr_val.into(),
                const_val.into(),
                Origin::synthetic(),
            );
            let then_block = block_map.get(*target_bb);
            let otherwise_block = block_map.get(otherwise);
            builder.brif(
                cmp.into(),
                then_block,
                vec![],
                otherwise_block,
                vec![],
                Origin::synthetic(),
            );
        }
        // Final fallthrough to otherwise.
        let otherwise_block = block_map.get(otherwise);
        builder.br(otherwise_block, vec![], Origin::synthetic());
    }
}

#[allow(clippy::too_many_arguments)]
fn translate_rvalue<'tcx>(
    tcx: TyCtxt<'tcx>,
    rvalue: &Rvalue<'tcx>,
    dest_place: &Place<'tcx>,
    mir: &mir::Body<'tcx>,
    builder: &mut Builder<'_>,
    locals: &mut LocalMap,
    fat_locals: &mut FatLocalMap,
    stack_locals: &mut StackLocalSet,
    static_refs: &mut HashMap<u32, String>,
    static_data: &mut Vec<(String, Vec<u8>)>,
) -> Option<ValueRef> {
    match rvalue {
        Rvalue::BinaryOp(op, box (lhs, rhs)) => {
            let l = translate_operand(
                tcx,
                lhs,
                mir,
                builder,
                locals,
                stack_locals,
                static_refs,
                static_data,
            )?;
            let r = translate_operand(
                tcx,
                rhs,
                mir,
                builder,
                locals,
                stack_locals,
                static_refs,
                static_data,
            )?;
            let l_ann = operand_annotation(lhs, mir);
            let r_ann = operand_annotation(rhs, mir);
            let l_op = IrOperand {
                value: l,
                annotation: l_ann,
            };
            let r_op = IrOperand {
                value: r,
                annotation: r_ann,
            };
            // For arithmetic/bitwise ops the result type matches the operand type.
            let res_ann = l_ann;
            let val = match op {
                BinOp::Add | BinOp::AddWithOverflow => {
                    builder.add(l_op, r_op, res_ann, Origin::synthetic())
                }
                BinOp::Sub | BinOp::SubWithOverflow => {
                    builder.sub(l_op, r_op, res_ann, Origin::synthetic())
                }
                BinOp::Mul | BinOp::MulWithOverflow => {
                    builder.mul(l_op, r_op, res_ann, Origin::synthetic())
                }
                BinOp::Eq => builder.icmp(ICmpOp::Eq, l_op, r_op, Origin::synthetic()),
                BinOp::Ne => builder.icmp(ICmpOp::Ne, l_op, r_op, Origin::synthetic()),
                BinOp::Lt => builder.icmp(ICmpOp::Slt, l_op, r_op, Origin::synthetic()),
                BinOp::Le => builder.icmp(ICmpOp::Sle, l_op, r_op, Origin::synthetic()),
                BinOp::Gt => builder.icmp(ICmpOp::Sgt, l_op, r_op, Origin::synthetic()),
                BinOp::Ge => builder.icmp(ICmpOp::Sge, l_op, r_op, Origin::synthetic()),
                BinOp::Shl | BinOp::ShlUnchecked => {
                    builder.shl(l_op, r_op, res_ann, Origin::synthetic())
                }
                BinOp::BitOr => builder.or(l_op, r_op, res_ann, Origin::synthetic()),
                BinOp::BitAnd => builder.and(l_op, r_op, res_ann, Origin::synthetic()),
                BinOp::BitXor => builder.xor(l_op, r_op, res_ann, Origin::synthetic()),
                BinOp::Shr | BinOp::ShrUnchecked => {
                    let lhs_ty = match lhs {
                        Operand::Copy(p) | Operand::Move(p) => mir.local_decls[p.local].ty,
                        Operand::Constant(c) => c.ty(),
                        _ => return None,
                    };
                    if is_signed_int(lhs_ty) {
                        builder.ashr(l_op, r_op, res_ann, Origin::synthetic())
                    } else {
                        builder.lshr(l_op, r_op, res_ann, Origin::synthetic())
                    }
                }
                BinOp::Div => {
                    let lhs_ty = match lhs {
                        Operand::Copy(p) | Operand::Move(p) => mir.local_decls[p.local].ty,
                        Operand::Constant(c) => c.ty(),
                        _ => return None,
                    };
                    if is_signed_int(lhs_ty) {
                        builder.sdiv(l_op, r_op, res_ann, Origin::synthetic())
                    } else {
                        builder.udiv(l_op, r_op, res_ann, Origin::synthetic())
                    }
                }
                BinOp::Rem => {
                    let lhs_ty = match lhs {
                        Operand::Copy(p) | Operand::Move(p) => mir.local_decls[p.local].ty,
                        Operand::Constant(c) => c.ty(),
                        _ => return None,
                    };
                    if is_signed_int(lhs_ty) {
                        builder.srem(l_op, r_op, res_ann, Origin::synthetic())
                    } else {
                        builder.urem(l_op, r_op, res_ann, Origin::synthetic())
                    }
                }
                _ => return None,
            };
            Some(val)
        }
        Rvalue::Use(operand) => translate_operand(
            tcx,
            operand,
            mir,
            builder,
            locals,
            stack_locals,
            static_refs,
            static_data,
        ),
        Rvalue::Cast(kind, operand, target_ty) => {
            let val = translate_operand(
                tcx,
                operand,
                mir,
                builder,
                locals,
                stack_locals,
                static_refs,
                static_data,
            )?;
            match kind {
                CastKind::IntToInt => {
                    let src_ty = match operand {
                        Operand::Copy(p) | Operand::Move(p) => mir.local_decls[p.local].ty,
                        Operand::Constant(c) => c.ty(),
                        _ => return Some(val),
                    };
                    translate_int_to_int_cast(src_ty, *target_ty, val, builder)
                }
                // Pointer casts and transmutes are bitwise moves.
                _ => Some(val),
            }
        }
        Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) => {
            if !place.projection.is_empty() {
                // Place has projections: compute address of the projected location.
                translate_place_to_addr(tcx, place, mir, builder, locals, stack_locals)
            } else if stack_locals.is_stack(place.local) {
                // Local is stack-allocated: its value is already the address.
                locals.get(place.local)
            } else {
                // Scalar local: spill to stack slot, return address.
                if let Some(val) = locals.get(place.local) {
                    let slot = builder.stack_slot(8, Origin::synthetic());
                    builder.store(val.into(), slot.into(), Origin::synthetic());
                    Some(slot)
                } else {
                    None
                }
            }
        }
        Rvalue::Aggregate(kind, operands) => {
            if operands.is_empty() {
                return Some(builder.iconst(0, Origin::synthetic()));
            }
            // Determine the aggregate type for layout queries.
            let agg_ty = match kind.as_ref() {
                mir::AggregateKind::Tuple => mir.local_decls[dest_place.local].ty,
                mir::AggregateKind::Adt(def_id, variant_idx, args, _, _) => {
                    let adt_def = tcx.adt_def(*def_id);
                    if adt_def.is_enum() {
                        // For enums, use the destination local's type.
                        mir.local_decls[dest_place.local].ty
                    } else {
                        let _ = variant_idx;
                        ty::Ty::new_adt(tcx, adt_def, args)
                    }
                }
                _ => mir.local_decls[dest_place.local].ty,
            };
            let total_size = type_size(tcx, agg_ty).unwrap_or(8 * operands.len() as u64);
            if total_size == 0 {
                return Some(builder.iconst(0, Origin::synthetic()));
            }
            let slot = builder.stack_slot(total_size as u32, Origin::synthetic());
            for (i, op) in operands.iter().enumerate() {
                if let Some(val) = translate_operand(
                    tcx,
                    op,
                    mir,
                    builder,
                    locals,
                    stack_locals,
                    static_refs,
                    static_data,
                ) {
                    let offset = field_offset(tcx, agg_ty, i).unwrap_or(i as u64 * 8);
                    if offset == 0 {
                        builder.store(val.into(), slot.into(), Origin::synthetic());
                    } else {
                        let off_val = builder.iconst(offset as i64, Origin::synthetic());
                        let addr =
                            builder.ptradd(slot.into(), off_val.into(), 0, Origin::synthetic());
                        builder.store(val.into(), addr.into(), Origin::synthetic());
                    }
                }
            }
            // Mark the destination local as stack-allocated.
            if dest_place.projection.is_empty() {
                stack_locals.mark(dest_place.local);
            }
            Some(slot)
        }
        Rvalue::UnaryOp(mir::UnOp::PtrMetadata, Operand::Copy(place) | Operand::Move(place)) => {
            // Extract metadata (e.g., slice length) from a fat pointer.
            fat_locals.get(place.local)
        }
        Rvalue::UnaryOp(mir::UnOp::PtrMetadata, _) => None,
        Rvalue::UnaryOp(mir::UnOp::Neg, operand) => {
            let v = translate_operand(
                tcx,
                operand,
                mir,
                builder,
                locals,
                stack_locals,
                static_refs,
                static_data,
            )?;
            let zero = builder.iconst(0, Origin::synthetic());
            Some(builder.sub(zero.into(), v.into(), None, Origin::synthetic()))
        }
        Rvalue::UnaryOp(mir::UnOp::Not, operand) => {
            let v = translate_operand(
                tcx,
                operand,
                mir,
                builder,
                locals,
                stack_locals,
                static_refs,
                static_data,
            )?;
            let ones = builder.iconst(-1, Origin::synthetic());
            Some(builder.xor(v.into(), ones.into(), None, Origin::synthetic()))
        }
        Rvalue::Discriminant(place) => locals.get(place.local),
        _ => None,
    }
}

/// Translate an IntToInt cast between integer types.
///
/// - Widening signed: sign-extend via shl+ashr
/// - Widening unsigned / narrowing: mask via and
/// - Same width: pass through (reinterpretation)
fn translate_int_to_int_cast(
    src_ty: ty::Ty<'_>,
    target_ty: ty::Ty<'_>,
    val: ValueRef,
    builder: &mut Builder<'_>,
) -> Option<ValueRef> {
    let src_bits = int_bitwidth(src_ty)?;
    let dst_bits = int_bitwidth(target_ty)?;

    if src_bits == dst_bits {
        // Same width: reinterpretation only.
        return Some(val);
    }

    if dst_bits > src_bits {
        // Widening cast.
        if is_signed_int(src_ty) {
            // Sign-extend: shl by (64 - src_bits), then ashr by (64 - src_bits).
            let shift_amt = 64 - src_bits;
            let shift_val = builder.iconst(shift_amt as i64, Origin::synthetic());
            let shifted = builder.shl(val.into(), shift_val.into(), None, Origin::synthetic());
            let shift_val2 = builder.iconst(shift_amt as i64, Origin::synthetic());
            Some(builder.ashr(shifted.into(), shift_val2.into(), None, Origin::synthetic()))
        } else {
            // Zero-extend: mask off high bits.
            let mask = if src_bits >= 64 {
                return Some(val);
            } else {
                (1i64 << src_bits) - 1
            };
            let mask_val = builder.iconst(mask, Origin::synthetic());
            Some(builder.and(val.into(), mask_val.into(), None, Origin::synthetic()))
        }
    } else {
        // Narrowing cast: mask to target width.
        let mask = if dst_bits >= 64 {
            return Some(val);
        } else {
            (1i64 << dst_bits) - 1
        };
        let mask_val = builder.iconst(mask, Origin::synthetic());
        Some(builder.and(val.into(), mask_val.into(), None, Origin::synthetic()))
    }
}

#[allow(clippy::too_many_arguments)]
fn translate_operand<'tcx>(
    tcx: TyCtxt<'tcx>,
    operand: &Operand<'tcx>,
    mir: &mir::Body<'tcx>,
    builder: &mut Builder<'_>,
    locals: &mut LocalMap,
    stack_locals: &StackLocalSet,
    static_refs: &mut HashMap<u32, String>,
    static_data: &mut Vec<(String, Vec<u8>)>,
) -> Option<ValueRef> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => {
            if place.projection.is_empty() {
                locals.get(place.local)
            } else {
                translate_place_to_value(tcx, place, mir, builder, locals, stack_locals)
            }
        }
        Operand::Constant(constant) => {
            translate_const(tcx, constant, builder, static_refs, static_data)
        }
        _ => None,
    }
}

fn translate_const<'tcx>(
    tcx: TyCtxt<'tcx>,
    constant: &mir::ConstOperand<'tcx>,
    builder: &mut Builder<'_>,
    static_refs: &mut HashMap<u32, String>,
    static_data: &mut Vec<(String, Vec<u8>)>,
) -> Option<ValueRef> {
    let mir::Const::Val(val, ty) = constant.const_ else {
        return None;
    };
    match val {
        mir::ConstValue::Scalar(scalar) => translate_scalar(scalar, ty, builder),
        mir::ConstValue::ZeroSized => Some(builder.iconst(0, Origin::synthetic())),
        mir::ConstValue::Slice { alloc_id, meta } => {
            translate_const_slice(tcx, alloc_id, meta, builder, static_refs, static_data)
        }
        _ => None,
    }
}

fn translate_scalar(
    scalar: mir::interpret::Scalar,
    ty: ty::Ty<'_>,
    builder: &mut Builder<'_>,
) -> Option<ValueRef> {
    let mir::interpret::Scalar::Int(int) = scalar else {
        return None;
    };
    let bits = int.to_bits(int.size());
    match ty.kind() {
        ty::Int(_) => {
            let val = bits as i128 as i64;
            Some(builder.iconst(val, Origin::synthetic()))
        }
        ty::Uint(_) => {
            let val = bits as i64;
            Some(builder.iconst(val, Origin::synthetic()))
        }
        ty::Bool => {
            let val = if bits != 0 { 1 } else { 0 };
            Some(builder.iconst(val, Origin::synthetic()))
        }
        _ => None,
    }
}

/// Translate a ConstValue::Slice (e.g., a string literal `&str`).
///
/// Emits the data bytes to .rodata and returns an IR constant whose index
/// is recorded in `static_refs` so that isel emits a RIP-relative LEA.
fn translate_const_slice<'tcx>(
    tcx: TyCtxt<'tcx>,
    alloc_id: rustc_middle::mir::interpret::AllocId,
    meta: u64,
    builder: &mut Builder<'_>,
    static_refs: &mut HashMap<u32, String>,
    static_data: &mut Vec<(String, Vec<u8>)>,
) -> Option<ValueRef> {
    let alloc = tcx.global_alloc(alloc_id).unwrap_memory();
    let alloc = alloc.inner();
    let bytes: Vec<u8> = alloc
        .inspect_with_uninit_and_ptr_outside_interpreter(0..alloc.len())
        .to_vec();

    // Create a unique symbol name for this data blob.
    let sym = format!(".Lstr.{}", static_data.len());
    static_data.push((sym.clone(), bytes));

    // Emit a dummy constant whose index we record as a static ref.
    // Isel will emit LEA rip-relative for this value.
    let ptr_val = builder.iconst(0, Origin::synthetic());
    static_refs.insert(ptr_val.index(), sym);

    // Emit the length as a separate constant.
    let len_val = builder.iconst(meta as i64, Origin::synthetic());

    // Store both components. The "value" of this slice is the pointer;
    // the length is stored as the next local via the fat_locals mechanism.
    // For now, we return the pointer and rely on the caller to handle
    // the fat pointer decomposition.
    //
    // We use a convention: for a &str local, we store the pointer in
    // locals[local] and the length in fat_locals[local].
    let _ = len_val;

    // Return pointer; the caller must also retrieve the length.
    Some(ptr_val)
}

/// Resolve the callee symbol name from a Call terminator's function operand.
fn resolve_call_symbol<'tcx>(tcx: TyCtxt<'tcx>, func_op: &Operand<'tcx>) -> Option<String> {
    let ty = match func_op {
        Operand::Constant(c) => c.ty(),
        Operand::Copy(place) | Operand::Move(place) => {
            // Indirect call through a local — we can't resolve statically.
            let _ = place;
            return None;
        }
        _ => return None,
    };
    match ty.kind() {
        ty::FnDef(def_id, args) => {
            // Skip if the callee's generic args contain unresolved parameters —
            // Instance::try_resolve will panic during normalization.
            if args.has_non_region_param() {
                return None;
            }
            let instance =
                Instance::try_resolve(tcx, ty::TypingEnv::fully_monomorphized(), *def_id, args)
                    .ok()
                    .flatten()?;
            if instance.args.has_non_region_param() {
                return None;
            }
            Some(tcx.symbol_name(instance).name.to_string())
        }
        _ => None,
    }
}
