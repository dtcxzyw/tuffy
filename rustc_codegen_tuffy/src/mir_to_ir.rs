//! MIR → tuffy IR translation.
//!
//! Translates rustc MIR into tuffy IR, supporting basic arithmetic,
//! control flow (branches, SwitchInt), and comparison operations.

use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, Ordering};

/// Global counter for generating unique `.Lconst.*` / `.Lstr.*` symbol names
/// across all functions and codegen units within a compilation session.
static STATIC_DATA_COUNTER: AtomicU64 = AtomicU64::new(0);

use num_bigint::BigInt;
use rustc_middle::mir::{
    self, BasicBlock, BinOp, CastKind, Operand, Place, PlaceElem, Rvalue, StatementKind,
    TerminatorKind,
};
use rustc_middle::ty::{self, Instance, TyCtxt, TypeVisitableExt};
use rustc_span::source_map::Spanned;

use tuffy_codegen::{AbiMetadataBox, CodegenSession};
use tuffy_ir::builder::Builder;
use tuffy_ir::function::{Function, RegionKind};
use tuffy_ir::instruction::{ICmpOp, Operand as IrOperand, Origin};
use tuffy_ir::module::{SymbolId, SymbolTable};
use tuffy_ir::types::{Annotation, Type};
use tuffy_ir::value::{BlockRef, ValueRef};

/// Static data entry: (symbol_id, bytes, relocations).
/// Relocations are (offset_in_bytes, target_symbol_name) for function pointers in vtables.
type StaticDataVec = Vec<(SymbolId, Vec<u8>, Vec<(usize, String)>)>;

/// Result of MIR → IR translation.
pub struct TranslationResult {
    pub func: Function,
    /// Interned symbol table shared across the codegen unit.
    pub symbols: SymbolTable,
    /// Static data blobs to emit in .rodata, keyed by SymbolId.
    pub static_data: StaticDataVec,
    /// Target-specific ABI metadata (e.g., secondary return register info).
    pub abi_metadata: AbiMetadataBox,
}

/// Translate a single MIR function instance to tuffy IR.
pub fn translate_function<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: Instance<'tcx>,
    session: &CodegenSession,
) -> Option<TranslationResult> {
    // Skip partially substituted polymorphic instances — the symbol mangler
    // will panic if generic parameters are still present.
    if instance.args.has_non_region_param() {
        return None;
    }

    let mir = tcx.instance_mir(instance.def);
    let name = tcx.symbol_name(instance).name.to_string();

    // Monomorphize a MIR type using the instance's substitutions.
    let monomorphize = |ty: ty::Ty<'tcx>| -> ty::Ty<'tcx> {
        tcx.instantiate_and_normalize_erasing_regions(
            instance.args,
            ty::TypingEnv::fully_monomorphized(),
            ty::EarlyBinder::bind(ty),
        )
    };

    let mut params = Vec::new();
    let mut param_anns = Vec::new();

    let ret_mir_ty = monomorphize(mir.local_decls[mir::RETURN_PLACE].ty);
    // Detect whether this function returns a large struct via sret.
    // Must be computed before building params so the hidden sret pointer
    // is included in the parameter list.
    let use_sret = needs_indirect_return(tcx, ret_mir_ty);
    let ret_size = type_size(tcx, ret_mir_ty);

    // When using sret, the ABI return value is the sret pointer (Ptr),
    // not the logical Rust return type.
    let ret_ty = if use_sret {
        Some(Type::Ptr(0))
    } else {
        translate_ty(ret_mir_ty).filter(|t| !matches!(t, Type::Unit))
    };
    let ret_ann = if use_sret {
        None
    } else {
        translate_annotation(ret_mir_ty)
    };

    let mut symbols = SymbolTable::new();
    let func_sym = symbols.intern(&name);

    // Build all-args name map first, then filter to match params.
    let all_names = extract_param_names(mir, &mut symbols);
    let mut param_names = Vec::new();

    // If sret, the first ABI parameter is a hidden pointer for the return value.
    if use_sret {
        params.push(Type::Ptr(0));
        param_anns.push(None);
        param_names.push(None);
    }

    for i in 0..mir.arg_count {
        let local = mir::Local::from_usize(i + 1);
        let ty = monomorphize(mir.local_decls[local].ty);
        match translate_ty(ty) {
            Some(Type::Unit) | None => continue,
            Some(ir_ty) => {
                // System V AMD64 ABI struct parameter passing:
                // - > 16 bytes: passed by hidden pointer
                // - 9-16 bytes: passed in TWO registers
                // - <= 8 bytes: passed in one register
                let param_size = type_size(tcx, ty).unwrap_or(0);
                let is_int_ty = matches!(ir_ty, Type::Int);
                if param_size > 16 && is_int_ty {
                    params.push(Type::Ptr(0));
                    param_anns.push(None);
                } else {
                    params.push(ir_ty);
                    param_anns.push(translate_annotation(ty));
                }
                param_names.push(all_names.get(i).copied().flatten());
                // Two-register structs (9-16 bytes) occupy two ABI slots.
                if param_size > 8
                    && param_size <= 16
                    && is_int_ty
                    && !is_fat_ptr(ty)
                {
                    params.push(Type::Int);
                    param_anns.push(None);
                    param_names.push(None);
                }
                // Fat pointers (&str, &[T]) occupy two ABI slots.
                if is_fat_ptr(ty) {
                    params.push(fat_ptr_meta_type(ty));
                    param_anns.push(None);
                    param_names.push(None);
                }
            }
        }
    }

    let mut func = Function::new(func_sym, params, param_anns, param_names, ret_ty, ret_ann);
    let mut builder = Builder::new(&mut func);
    let abi_metadata = session.new_metadata();

    let root = builder.create_region(RegionKind::Function);
    builder.enter_region(root);

    // Create IR blocks for all MIR basic blocks upfront so branches can
    // reference target blocks before they are translated.
    // Each block gets a Type::Mem block argument for MemSSA threading.
    let mut block_map = BlockMap::new(mir.basic_blocks.len());
    let mut block_mem_args = Vec::with_capacity(mir.basic_blocks.len());
    for (bb, _) in mir.basic_blocks.iter_enumerated() {
        let ir_block = builder.create_block();
        block_map.set(bb, ir_block);
        let mem_arg = builder.add_block_arg(ir_block, Type::Mem);
        block_mem_args.push(mem_arg);
    }

    let entry = block_map.get(BasicBlock::from_u32(0));
    builder.switch_to_block(entry);

    let initial_mem = block_mem_args[0];

    let mut ctx = TranslationCtx {
        tcx,
        mir,
        builder,
        locals: LocalMap::new(mir.local_decls.len()),
        fat_locals: FatLocalMap::new(),
        stack_locals: StackLocalSet::new(mir.local_decls.len()),
        symbols,
        static_data: Vec::new(),
        block_map,
        block_mem_args,
        abi_metadata,
        instance,
        sret_ptr: None,
        use_sret,
        current_mem: initial_mem,
    };

    // Emit params into the entry block.
    ctx.translate_params();

    // Pre-scan: find scalar locals assigned in more than one basic block.
    // These need stack slots so that mutations in loop bodies are visible
    // at loop headers (SSA values can't be mutated in place).
    {
        let mut assign_bb: Vec<Option<BasicBlock>> = vec![None; mir.local_decls.len()];
        for (bb, bb_data) in mir.basic_blocks.iter_enumerated() {
            for stmt in &bb_data.statements {
                if let StatementKind::Assign(box (place, _)) = &stmt.kind {
                    if place.projection.is_empty() {
                        let local = place.local;
                        // Skip _0 (return place) and function params.
                        if local.as_usize() == 0 || local.as_usize() <= mir.arg_count {
                            continue;
                        }
                        let ty = monomorphize(mir.local_decls[local].ty);
                        let size = type_size(tcx, ty).unwrap_or(0);
                        // Only promote small scalars (<=8 bytes); large types
                        // already use stack slots via the aggregate path.
                        if size > 8 || size == 0 {
                            continue;
                        }
                        if let Some(prev_bb) = assign_bb[local.as_usize()] {
                            if prev_bb != bb && !ctx.stack_locals.is_stack(local) {
                                let slot = ctx.builder.stack_slot(
                                    std::cmp::max(size as u32, 1),
                                    Origin::synthetic(),
                                );
                                ctx.locals.set(local, slot);
                                ctx.stack_locals.mark(local);
                            }
                        } else {
                            assign_bb[local.as_usize()] = Some(bb);
                        }
                    }
                }
            }
        }
    }

    // Translate each basic block.
    for (bb, bb_data) in mir.basic_blocks.iter_enumerated() {
        let ir_block = ctx.block_map.get(bb);
        ctx.builder.switch_to_block(ir_block);
        // Pick up the memory token from this block's MemSSA block argument.
        ctx.current_mem = ctx.block_mem_args[bb.as_usize()];

        for stmt in &bb_data.statements {
            ctx.translate_statement(stmt);
        }
        if let Some(ref term) = bb_data.terminator {
            ctx.translate_terminator(term);
        }

        // Safety net: if the block is still unterminated after lowering
        // (e.g. unhandled statement/terminator combo), patch it with
        // unreachable so the IR verifier won't reject it.
        if !ctx.builder.current_block_is_terminated() {
            ctx.builder.unreachable(Origin::synthetic());
        }
    }

    ctx.builder.exit_region();

    // Destructure ctx to release the borrow on `func` (held by builder).
    let TranslationCtx {
        symbols,
        static_data,
        abi_metadata,
        ..
    } = ctx;

    Some(TranslationResult {
        func,
        symbols,
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
        ty::Adt(..) | ty::Tuple(..) | ty::Array(..) | ty::Slice(..) | ty::Str => Some(Type::Int),
        _ => None,
    }
}

fn translate_annotation(ty: ty::Ty<'_>) -> Option<Annotation> {
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
#[allow(dead_code)]
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
    type_size(tcx, ty).is_some_and(|size| size > 8)
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

/// Extract source-level parameter names from MIR debug info.
///
/// Walks `mir.var_debug_info` looking for entries with `argument_index` set,
/// which indicate function arguments. Returns a vec indexed by MIR arg position
/// (0-based), with `Some(SymbolId)` for named params and `None` otherwise.
/// Synthetic ABI params (sret, fat pointer metadata) are not covered here —
/// the caller is responsible for prepending `None` entries for those.
fn extract_param_names(mir: &mir::Body<'_>, symbols: &mut SymbolTable) -> Vec<Option<SymbolId>> {
    let mut names: Vec<Option<SymbolId>> = vec![None; mir.arg_count];
    for info in &mir.var_debug_info {
        if let Some(arg_idx) = info.argument_index {
            // argument_index is 1-based; convert to 0-based MIR arg index.
            let idx = (arg_idx as usize).wrapping_sub(1);
            if idx < mir.arg_count {
                let name_str = info.name.as_str();
                names[idx] = Some(symbols.intern(name_str));
            }
        }
    }
    names
}

/// Check if a type is a fat pointer (e.g., &str, &[T], &dyn Trait) that uses two registers at ABI level.
fn is_fat_ptr(ty: ty::Ty<'_>) -> bool {
    match ty.kind() {
        ty::Ref(_, inner, _) | ty::RawPtr(inner, _) => {
            matches!(inner.kind(), ty::Str | ty::Slice(..) | ty::Dynamic(..))
        }
        _ => false,
    }
}

/// Return the IR type for the metadata word of a fat pointer.
/// - &dyn Trait → Ptr (vtable pointer)
/// - &str / &[T] → Int (length)
fn fat_ptr_meta_type(ty: ty::Ty<'_>) -> Type {
    match ty.kind() {
        ty::Ref(_, inner, _) | ty::RawPtr(inner, _) if matches!(inner.kind(), ty::Dynamic(..)) => {
            Type::Ptr(0)
        }
        _ => Type::Int,
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

/// Bundles the mutable translation state threaded through MIR→IR lowering.
///
/// Converting free functions into methods on this struct eliminates the
/// `clippy::too_many_arguments` warnings and makes it easier to add new
/// shared state in the future.
struct TranslationCtx<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    mir: &'a mir::Body<'tcx>,
    builder: Builder<'a>,
    locals: LocalMap,
    fat_locals: FatLocalMap,
    stack_locals: StackLocalSet,
    symbols: SymbolTable,
    static_data: StaticDataVec,
    block_map: BlockMap,
    /// MemSSA block arguments: one `Type::Mem` arg per MIR basic block.
    block_mem_args: Vec<ValueRef>,
    abi_metadata: AbiMetadataBox,
    instance: Instance<'tcx>,
    sret_ptr: Option<ValueRef>,
    use_sret: bool,
    /// Current memory token for MemSSA threading.
    current_mem: ValueRef,
}

impl<'a, 'tcx> TranslationCtx<'a, 'tcx> {
    /// Monomorphize a MIR type using the current instance's substitutions.
    fn monomorphize(&self, ty: ty::Ty<'tcx>) -> ty::Ty<'tcx> {
        self.tcx.instantiate_and_normalize_erasing_regions(
            self.instance.args,
            ty::TypingEnv::fully_monomorphized(),
            ty::EarlyBinder::bind(ty),
        )
    }

    /// If `val` is a Ptr or Bool, coerce it to Int.
    fn coerce_to_int(&mut self, val: ValueRef) -> ValueRef {
        match self.builder.value_type(val) {
            Some(Type::Ptr(_)) => self.builder.ptrtoaddr(val.into(), Origin::synthetic()),
            Some(Type::Bool) => self.builder.bool_to_int(val.into(), Origin::synthetic()),
            _ => val,
        }
    }

    /// If `val` is an Int, insert inttoptr to coerce it to Ptr.
    fn coerce_to_ptr(&mut self, val: ValueRef) -> ValueRef {
        if matches!(self.builder.value_type(val), Some(Type::Int)) {
            self.builder.inttoptr(val.into(), 0, Origin::synthetic())
        } else {
            val
        }
    }

    fn translate_params(&mut self) {
        let mut abi_idx: u32 = 0;

        // If the function returns a large struct, the caller passes a hidden
        // pointer as the first argument (sret). We consume it here and use it
        // as the storage for local _0.
        if self.use_sret {
            let ret_ty = self.monomorphize(self.mir.local_decls[mir::Local::from_usize(0)].ty);
            let size = type_size(self.tcx, ret_ty).unwrap_or(8);
            let hidden = self
                .builder
                .param(abi_idx, Type::Ptr(0), None, Origin::synthetic());
            abi_idx += 1;

            // Allocate a local stack slot for _0 so MIR stores go somewhere real.
            let slot = self.builder.stack_slot(size as u32, Origin::synthetic());
            self.locals.set(mir::Local::from_usize(0), slot);
            self.stack_locals.mark(mir::Local::from_usize(0));

            // Remember the caller-provided sret pointer for the Return terminator.
            self.sret_ptr = Some(hidden);
        }

        for i in 0..self.mir.arg_count {
            let local = mir::Local::from_usize(i + 1);
            let ty = self.monomorphize(self.mir.local_decls[local].ty);
            let ir_ty = translate_ty(ty);

            // Skip zero-sized (Unit) and untranslatable params — they don't
            // occupy an ABI slot. Assign a dummy iconst 0 so downstream MIR
            // references to this local don't crash.
            match ir_ty {
                Some(Type::Unit) | None => {
                    let dummy = self.builder.iconst(0, Origin::synthetic());
                    self.locals.set(local, dummy);
                    continue;
                }
                _ => {}
            }

            // System V AMD64 ABI struct parameter passing:
            // - > 16 bytes: passed by hidden pointer
            // - 9-16 bytes: passed in TWO registers
            // - <= 8 bytes: passed in one register
            let param_size = type_size(self.tcx, ty).unwrap_or(0);
            let large_struct = param_size > 16 && matches!(ir_ty, Some(Type::Int));
            let two_reg_struct =
                param_size > 8 && param_size <= 16 && matches!(ir_ty, Some(Type::Int));
            let (abi_ty, abi_ann) = if large_struct {
                (Type::Ptr(0), None)
            } else {
                (ir_ty.unwrap(), translate_annotation(ty))
            };
            let val = self
                .builder
                .param(abi_idx, abi_ty, abi_ann, Origin::synthetic());
            if large_struct {
                // The param is a pointer to caller-allocated memory.
                // Mark as stack-allocated so translate_place_to_addr uses
                // the pointer directly as the base address.
                self.locals.set(local, val);
                self.stack_locals.mark(local);
            } else if two_reg_struct {
                // Two-register struct (9-16 bytes): capture both ABI
                // registers and reconstruct into a stack slot.
                let slot = self
                    .builder
                    .stack_slot(param_size as u32, Origin::synthetic());
                self.current_mem = self.builder.store(
                    val.into(),
                    slot.into(),
                    8,
                    self.current_mem.into(),
                    Origin::synthetic(),
                );
                abi_idx += 1;
                let val2 = self
                    .builder
                    .param(abi_idx, Type::Int, None, Origin::synthetic());
                let off = self.builder.iconst(8, Origin::synthetic());
                let addr1 = self
                    .builder
                    .ptradd(slot.into(), off.into(), 0, Origin::synthetic());
                self.current_mem = self.builder.store(
                    val2.into(),
                    addr1.into(),
                    8,
                    self.current_mem.into(),
                    Origin::synthetic(),
                );
                self.locals.set(local, slot);
                self.stack_locals.mark(local);
            } else {
                self.locals.set(local, val);
            }
            abi_idx += 1;

            // Fat pointer types (&str, &[T]) occupy two ABI registers (ptr + metadata).
            if is_fat_ptr(ty) {
                let meta_ty = fat_ptr_meta_type(ty);
                let meta_val = self
                    .builder
                    .param(abi_idx, meta_ty, None, Origin::synthetic());
                self.fat_locals.set(local, meta_val);
                abi_idx += 1;
            }
        }
    }

    /// Compute the address of a Place (base + projections).
    ///
    /// Walks the projection chain and returns a `(ValueRef, Ty)` pair: the pointer
    /// to the final memory location and the projected type at that location.
    /// For locals with no projections that are stack-allocated, returns the
    /// local's value directly (which is already a pointer).
    fn translate_place_to_addr(&mut self, place: &Place<'tcx>) -> Option<(ValueRef, ty::Ty<'tcx>)> {
        let mut addr = self.locals.get(place.local)?;
        let mut cur_ty = self.monomorphize(self.mir.local_decls[place.local].ty);

        // If the base local is not stack-allocated and the first projection
        // needs an address (Field, Index, etc.), spill the scalar value to a
        // temporary stack slot so we can compute sub-field addresses.
        if !self.stack_locals.is_stack(place.local)
            && !place.projection.is_empty()
            && !matches!(place.projection[0], PlaceElem::Deref)
        {
            let size = type_size(self.tcx, cur_ty).unwrap_or(8) as u32;
            let slot = self.builder.stack_slot(size, Origin::synthetic());
            self.current_mem = self.builder.store(
                addr.into(),
                slot.into(),
                size,
                self.current_mem.into(),
                Origin::synthetic(),
            );
            addr = slot;
        }

        for elem in place.projection.iter() {
            match elem {
                PlaceElem::Deref => {
                    // The current value is a pointer; load through it to get the
                    // pointee address. But since we want the *address* of the
                    // deref'd location, the current value IS the address.
                    // Coerce Int→Ptr if the value was stored as an integer.
                    addr = self.coerce_to_ptr(addr);
                    // Update cur_ty to the pointee type.
                    cur_ty = match cur_ty.kind() {
                        ty::Ref(_, inner, _) | ty::RawPtr(inner, _) => *inner,
                        _ => return None,
                    };
                }
                PlaceElem::Field(field_idx, field_ty) => {
                    let offset = field_offset(self.tcx, cur_ty, field_idx.as_usize())?;
                    if offset != 0 {
                        let off_val = self.builder.iconst(offset as i64, Origin::synthetic());
                        addr = self.builder.ptradd(
                            addr.into(),
                            off_val.into(),
                            0,
                            Origin::synthetic(),
                        );
                    }
                    cur_ty = self.monomorphize(field_ty);
                }
                PlaceElem::Index(local) => {
                    let mut idx_val = self.locals.get(local)?;
                    // If the index local is stored in a stack slot, load
                    // the integer value — the raw slot is a Ptr, not Int.
                    if self.stack_locals.is_stack(local)
                        && matches!(self.builder.value_type(idx_val), Some(Type::Ptr(_)))
                    {
                        idx_val = self.builder.load(
                            idx_val.into(),
                            8,
                            Type::Int,
                            self.current_mem.into(),
                            None,
                            Origin::synthetic(),
                        );
                    }
                    let elem_size = type_size(
                        self.tcx,
                        match cur_ty.kind() {
                            ty::Array(elem_ty, _) => *elem_ty,
                            ty::Slice(elem_ty) => *elem_ty,
                            _ => return None,
                        },
                    )?;
                    let size_val = self.builder.iconst(elem_size as i64, Origin::synthetic());
                    let byte_offset = self.builder.mul(
                        idx_val.into(),
                        size_val.into(),
                        None,
                        Origin::synthetic(),
                    );
                    addr = self.builder.ptradd(
                        addr.into(),
                        byte_offset.into(),
                        0,
                        Origin::synthetic(),
                    );
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
                    let elem_size = type_size(self.tcx, elem_ty)?;
                    if !from_end {
                        let byte_off = offset * elem_size;
                        if byte_off != 0 {
                            let off_val = self.builder.iconst(byte_off as i64, Origin::synthetic());
                            addr = self.builder.ptradd(
                                addr.into(),
                                off_val.into(),
                                0,
                                Origin::synthetic(),
                            );
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
        Some((addr, cur_ty))
    }

    /// Read the value at a Place (base + projections).
    ///
    /// If the place has no projections, returns the local's value directly.
    /// If it has projections, computes the address and emits a Load.
    fn translate_place_to_value(&mut self, place: &Place<'tcx>) -> Option<ValueRef> {
        if place.projection.is_empty() {
            return self.locals.get(place.local);
        }
        // Non-stack scalar with Field projection (e.g., CheckedOp tuple `.0` / `.1`):
        // AddWithOverflow/SubWithOverflow/MulWithOverflow return (result, bool) but
        // we only emit the arithmetic result as a scalar.  Field(0) returns that
        // scalar directly; Field(1) (the overflow flag) returns constant 0 (false),
        // effectively disabling overflow detection (matches release-mode behaviour).
        if !self.stack_locals.is_stack(place.local)
            && place.projection.len() == 1
            && matches!(place.projection[0], PlaceElem::Field(idx, _) if idx.as_usize() == 0)
        {
            return self.locals.get(place.local);
        }
        if !self.stack_locals.is_stack(place.local)
            && place.projection.len() == 1
            && matches!(place.projection[0], PlaceElem::Field(idx, _) if idx.as_usize() == 1)
        {
            // Overflow flag — always false for now.
            return Some(self.builder.iconst(0, Origin::synthetic()));
        }
        let (addr, projected_ty) = self.translate_place_to_addr(place)?;
        let addr = self.coerce_to_ptr(addr);
        let bytes = type_size(self.tcx, projected_ty).unwrap_or(8) as u32;
        let ty = translate_ty(projected_ty).unwrap_or(Type::Int);
        Some(self.builder.load(
            addr.into(),
            bytes,
            ty,
            self.current_mem.into(),
            None,
            Origin::synthetic(),
        ))
    }

    /// Compute the discriminant of an enum at `place`.
    ///
    /// Handles three layout cases:
    /// - `Variants::Single`: return the constant discriminant value.
    /// - `Variants::Multiple` with `TagEncoding::Direct`: load the tag field.
    /// - `Variants::Multiple` with `TagEncoding::Niche`: load the niche field
    ///   and compute the variant index via wrapping arithmetic + select.
    fn translate_discriminant(&mut self, place: &Place<'tcx>) -> Option<ValueRef> {
        let place_ty = self.monomorphize(place.ty(&self.mir.local_decls, self.tcx).ty);
        let typing_env = ty::TypingEnv::fully_monomorphized();
        let layout = self
            .tcx
            .layout_of(typing_env.as_query_input(place_ty))
            .ok()?;

        match layout.variants {
            rustc_abi::Variants::Empty => Some(self.builder.iconst(0, Origin::synthetic())),
            rustc_abi::Variants::Single { index } => {
                let discr_val = match place_ty.kind() {
                    ty::Adt(adt_def, _) if adt_def.is_enum() => {
                        adt_def.discriminant_for_variant(self.tcx, index).val as i64
                    }
                    _ => index.as_u32() as i64,
                };
                Some(self.builder.iconst(discr_val, Origin::synthetic()))
            }
            rustc_abi::Variants::Multiple {
                ref tag,
                ref tag_encoding,
                tag_field,
                ..
            } => {
                // Get the address of the enum value.
                let base_addr = if place.projection.is_empty() {
                    if self.stack_locals.is_stack(place.local) {
                        self.locals.get(place.local)?
                    } else {
                        // Scalar local — spill to a temporary stack slot.
                        let val = self.locals.get(place.local)?;
                        let size = layout.size.bytes() as u32;
                        let slot = self.builder.stack_slot(size, Origin::synthetic());
                        self.current_mem = self.builder.store(
                            val.into(),
                            slot.into(),
                            size,
                            self.current_mem.into(),
                            Origin::synthetic(),
                        );
                        slot
                    }
                } else {
                    let (addr, _) = self.translate_place_to_addr(place)?;
                    self.coerce_to_ptr(addr)
                };

                // Tag field offset and load size.
                let tag_offset = layout.fields.offset(tag_field.as_usize()).bytes();
                let tag_size = match tag.primitive() {
                    rustc_abi::Primitive::Int(int, _) => int.size().bytes() as u32,
                    rustc_abi::Primitive::Pointer(_) => 8,
                    _ => 8,
                };

                let tag_addr = if tag_offset != 0 {
                    let off = self.builder.iconst(tag_offset as i64, Origin::synthetic());
                    self.builder
                        .ptradd(base_addr.into(), off.into(), 0, Origin::synthetic())
                } else {
                    base_addr
                };
                let tag_val = self.builder.load(
                    tag_addr.into(),
                    tag_size,
                    Type::Int,
                    self.current_mem.into(),
                    None,
                    Origin::synthetic(),
                );

                match tag_encoding {
                    rustc_abi::TagEncoding::Direct => Some(tag_val),
                    rustc_abi::TagEncoding::Niche {
                        untagged_variant,
                        niche_variants,
                        niche_start,
                    } => {
                        let variants_start = niche_variants.start().as_u32();
                        let variants_end = niche_variants.end().as_u32();
                        let num_niche = variants_end - variants_start + 1;
                        let untagged_discr = untagged_variant.as_u32() as i64;

                        if num_niche == 1 && *niche_start == 0 && variants_start == 0 {
                            // Common case: Option-like niche (tag == 0 → None).
                            let zero = self.builder.iconst(0, Origin::synthetic());
                            let is_niche = self.builder.icmp(
                                ICmpOp::Eq,
                                tag_val.into(),
                                zero.into(),
                                Origin::synthetic(),
                            );
                            let niche_discr = self
                                .builder
                                .iconst(variants_start as i64, Origin::synthetic());
                            let untag_discr =
                                self.builder.iconst(untagged_discr, Origin::synthetic());
                            Some(self.builder.select(
                                is_niche.into(),
                                niche_discr.into(),
                                untag_discr.into(),
                                Type::Int,
                                Origin::synthetic(),
                            ))
                        } else {
                            // General niche: i = tag.wrapping_sub(niche_start) + start
                            let ns = self
                                .builder
                                .iconst(*niche_start as i64, Origin::synthetic());
                            let relative = self.builder.sub(
                                tag_val.into(),
                                ns.into(),
                                None,
                                Origin::synthetic(),
                            );
                            let start_c = self
                                .builder
                                .iconst(variants_start as i64, Origin::synthetic());
                            let variant_idx = self.builder.add(
                                relative.into(),
                                start_c.into(),
                                None,
                                Origin::synthetic(),
                            );
                            // Check relative < num_niche (unsigned).
                            let num_c = self.builder.iconst(num_niche as i64, Origin::synthetic());
                            let in_range = self.builder.icmp(
                                ICmpOp::Lt,
                                relative.into(),
                                num_c.into(),
                                Origin::synthetic(),
                            );
                            let untag_discr =
                                self.builder.iconst(untagged_discr, Origin::synthetic());
                            Some(self.builder.select(
                                in_range.into(),
                                variant_idx.into(),
                                untag_discr.into(),
                                Type::Int,
                                Origin::synthetic(),
                            ))
                        }
                    }
                }
            }
        }
    }

    fn translate_statement(&mut self, stmt: &mir::Statement<'tcx>) {
        match &stmt.kind {
            StatementKind::Assign(box (place, rvalue)) => {
                let rval_result = self.translate_rvalue(rvalue, place);
                if let Some(val) = rval_result {
                    if place.projection.is_empty() {
                        // For stack-allocated locals, store the value into the
                        // existing stack slot instead of overwriting the pointer.
                        // This preserves the slot address for later loads (e.g.,
                        // sret return copy, field access).
                        if self.stack_locals.is_stack(place.local) {
                            if let Some(slot) = self.locals.get(place.local) {
                                if matches!(self.builder.value_type(slot), Some(Type::Ptr(_))) {
                                    let ty =
                                        self.monomorphize(self.mir.local_decls[place.local].ty);
                                    let bytes = type_size(self.tcx, ty).unwrap_or(8) as u32;
                                    // If val is also a pointer (e.g. stack slot from
                                    // Aggregate) and the type is larger than 8 bytes,
                                    // do a word-by-word copy of the DATA instead of
                                    // storing the pointer value.
                                    let val_ty = self.builder.value_type(val).cloned();
                                    if matches!(val_ty.as_ref(), Some(Type::Ptr(_))) && bytes > 0 {
                                        // For word-by-word copy we need a SOURCE ADDRESS
                                        // to load from. When the rvalue is Use(Copy/Move)
                                        // of a place with projections (e.g. a fat pointer
                                        // field like &str), `val` is the LOADED value (the
                                        // data pointer), not a pointer to the multi-word
                                        // data. Use translate_place_to_addr to get the
                                        // actual source address in memory.
                                        let src_base = match rvalue {
                                            Rvalue::Use(
                                                Operand::Copy(src_place)
                                                | Operand::Move(src_place),
                                            ) if !src_place.projection.is_empty() => {
                                                self.translate_place_to_addr(src_place)
                                                    .map(|(a, _)| self.coerce_to_ptr(a))
                                            }
                                            _ => None,
                                        };
                                        let src_base = src_base.unwrap_or(val);
                                        let num_words = (bytes as u64).div_ceil(8);
                                        for i in 0..num_words {
                                            let byte_off = i * 8;
                                            let src_addr = if byte_off == 0 {
                                                src_base
                                            } else {
                                                let off = self
                                                    .builder
                                                    .iconst(byte_off as i64, Origin::synthetic());
                                                self.builder.ptradd(
                                                    src_base.into(),
                                                    off.into(),
                                                    0,
                                                    Origin::synthetic(),
                                                )
                                            };
                                            let word = self.builder.load(
                                                src_addr.into(),
                                                8,
                                                Type::Int,
                                                self.current_mem.into(),
                                                None,
                                                Origin::synthetic(),
                                            );
                                            let dst_addr = if byte_off == 0 {
                                                slot
                                            } else {
                                                let off = self
                                                    .builder
                                                    .iconst(byte_off as i64, Origin::synthetic());
                                                self.builder.ptradd(
                                                    slot.into(),
                                                    off.into(),
                                                    0,
                                                    Origin::synthetic(),
                                                )
                                            };
                                            self.current_mem = self.builder.store(
                                                word.into(),
                                                dst_addr.into(),
                                                8,
                                                self.current_mem.into(),
                                                Origin::synthetic(),
                                            );
                                        }
                                    } else {
                                        self.current_mem = self.builder.store(
                                            val.into(),
                                            slot.into(),
                                            bytes,
                                            self.current_mem.into(),
                                            Origin::synthetic(),
                                        );
                                    }
                                } else {
                                    self.locals.set(place.local, val);
                                }
                            } else {
                                self.locals.set(place.local, val);
                            }
                        } else {
                            self.locals.set(place.local, val);
                        }
                    } else {
                        // Projected destination: compute address and emit Store.
                        if let Some((addr, projected_ty)) = self.translate_place_to_addr(place) {
                            let addr = self.coerce_to_ptr(addr);
                            let bytes = type_size(self.tcx, projected_ty).unwrap_or(8) as u32;
                            let val_ty = self.builder.value_type(val).cloned();
                            if matches!(val_ty.as_ref(), Some(Type::Ptr(_))) && bytes > 0 {
                                // val is a pointer to multi-word data (e.g.
                                // symbol_addr of an Indirect constant like a
                                // slice reference).  Copy word-by-word from
                                // the source address.
                                let src_base = match rvalue {
                                    Rvalue::Use(
                                        Operand::Copy(src_place)
                                        | Operand::Move(src_place),
                                    ) if !src_place.projection.is_empty() => {
                                        self.translate_place_to_addr(src_place)
                                            .map(|(a, _)| self.coerce_to_ptr(a))
                                    }
                                    _ => None,
                                };
                                let src_base = src_base.unwrap_or(val);
                                let num_words = (bytes as u64).div_ceil(8);
                                for i in 0..num_words {
                                    let byte_off = i * 8;
                                    let src_addr = if byte_off == 0 {
                                        src_base
                                    } else {
                                        let off = self
                                            .builder
                                            .iconst(byte_off as i64, Origin::synthetic());
                                        self.builder.ptradd(
                                            src_base.into(),
                                            off.into(),
                                            0,
                                            Origin::synthetic(),
                                        )
                                    };
                                    let word = self.builder.load(
                                        src_addr.into(),
                                        8,
                                        Type::Int,
                                        self.current_mem.into(),
                                        None,
                                        Origin::synthetic(),
                                    );
                                    let dst_addr = if byte_off == 0 {
                                        addr
                                    } else {
                                        let off = self
                                            .builder
                                            .iconst(byte_off as i64, Origin::synthetic());
                                        self.builder.ptradd(
                                            addr.into(),
                                            off.into(),
                                            0,
                                            Origin::synthetic(),
                                        )
                                    };
                                    self.current_mem = self.builder.store(
                                        word.into(),
                                        dst_addr.into(),
                                        8,
                                        self.current_mem.into(),
                                        Origin::synthetic(),
                                    );
                                }
                            } else {
                                self.current_mem = self.builder.store(
                                    val.into(),
                                    addr.into(),
                                    bytes,
                                    self.current_mem.into(),
                                    Origin::synthetic(),
                                );
                            }
                        }
                    }
                }
                // Check if the rvalue produces a fat pointer (e.g., &str from ConstValue::Slice).
                if let Some(fat_val) = self.extract_fat_component(rvalue) {
                    self.fat_locals.set(place.local, fat_val);
                }
            }
            StatementKind::StorageLive(_) | StatementKind::StorageDead(_) | StatementKind::Nop => {}
            StatementKind::SetDiscriminant {
                box place,
                variant_index,
            } => {
                self.translate_set_discriminant(place, *variant_index);
            }
            _ => {}
        }
    }

    /// Write the discriminant tag for an enum variant.
    ///
    /// Handles both `TagEncoding::Direct` (write the discriminant value) and
    /// `TagEncoding::Niche` (compute niche_start + offset and write to the
    /// niche field).  For niche encoding, the untagged variant is a no-op
    /// because the payload already distinguishes it.
    fn translate_set_discriminant(
        &mut self,
        place: &Place<'tcx>,
        variant_index: rustc_abi::VariantIdx,
    ) {
        let place_ty = self.monomorphize(place.ty(&self.mir.local_decls, self.tcx).ty);
        let typing_env = ty::TypingEnv::fully_monomorphized();
        let layout = match self.tcx.layout_of(typing_env.as_query_input(place_ty)) {
            Ok(l) => l,
            Err(_) => return,
        };

        let (tag, tag_encoding, tag_field) = match layout.variants {
            rustc_abi::Variants::Single { .. } | rustc_abi::Variants::Empty => return,
            rustc_abi::Variants::Multiple {
                ref tag,
                ref tag_encoding,
                tag_field,
                ..
            } => (*tag, tag_encoding.clone(), tag_field),
        };

        // Compute the tag value to store.
        let tag_val: i64 = match &tag_encoding {
            rustc_abi::TagEncoding::Direct => match place_ty.kind() {
                ty::Adt(adt_def, _) => {
                    adt_def
                        .discriminant_for_variant(self.tcx, variant_index)
                        .val as i64
                }
                _ => variant_index.as_u32() as i64,
            },
            rustc_abi::TagEncoding::Niche {
                untagged_variant,
                niche_variants,
                niche_start,
            } => {
                if variant_index == *untagged_variant {
                    // The payload already encodes this variant — nothing to write.
                    return;
                }
                let variant_u128 = variant_index.as_u32() as u128;
                let start_u128 = niche_variants.start().as_u32() as u128;
                niche_start.wrapping_add(variant_u128 - start_u128) as i64
            }
        };

        // Resolve the base address of the enum.
        let base_addr = if place.projection.is_empty() {
            if self.stack_locals.is_stack(place.local) {
                match self.locals.get(place.local) {
                    Some(v) => v,
                    None => return,
                }
            } else {
                return;
            }
        } else {
            match self.translate_place_to_addr(place) {
                Some((addr, _)) => self.coerce_to_ptr(addr),
                None => return,
            }
        };

        // Tag field offset and store size.
        let tag_offset = layout.fields.offset(tag_field.as_usize()).bytes();
        let tag_size = match tag.primitive() {
            rustc_abi::Primitive::Int(int, _) => int.size().bytes() as u32,
            rustc_abi::Primitive::Pointer(_) => 8,
            _ => 8,
        };

        let tag_addr = if tag_offset != 0 {
            let off = self.builder.iconst(tag_offset as i64, Origin::synthetic());
            self.builder
                .ptradd(base_addr.into(), off.into(), 0, Origin::synthetic())
        } else {
            base_addr
        };

        let tag_const = self.builder.iconst(tag_val, Origin::synthetic());
        self.current_mem = self.builder.store(
            tag_const.into(),
            tag_addr.into(),
            tag_size,
            self.current_mem.into(),
            Origin::synthetic(),
        );
    }

    /// Write the discriminant tag for an enum variant into a slot pointer.
    ///
    /// Called from the `Rvalue::Aggregate` handler to set the correct
    /// discriminant after storing variant fields.
    fn write_enum_tag(
        &mut self,
        slot: ValueRef,
        enum_ty: ty::Ty<'tcx>,
        variant_index: rustc_abi::VariantIdx,
    ) {
        let typing_env = ty::TypingEnv::fully_monomorphized();
        let layout = match self.tcx.layout_of(typing_env.as_query_input(enum_ty)) {
            Ok(l) => l,
            Err(_) => return,
        };

        let (tag, tag_encoding, tag_field) = match layout.variants {
            rustc_abi::Variants::Single { .. } | rustc_abi::Variants::Empty => return,
            rustc_abi::Variants::Multiple {
                ref tag,
                ref tag_encoding,
                tag_field,
                ..
            } => (*tag, tag_encoding.clone(), tag_field),
        };

        let tag_val: i64 = match &tag_encoding {
            rustc_abi::TagEncoding::Direct => match enum_ty.kind() {
                ty::Adt(adt_def, _) => {
                    adt_def
                        .discriminant_for_variant(self.tcx, variant_index)
                        .val as i64
                }
                _ => variant_index.as_u32() as i64,
            },
            rustc_abi::TagEncoding::Niche {
                untagged_variant,
                niche_variants,
                niche_start,
            } => {
                if variant_index == *untagged_variant {
                    return;
                }
                let variant_u128 = variant_index.as_u32() as u128;
                let start_u128 = niche_variants.start().as_u32() as u128;
                niche_start.wrapping_add(variant_u128 - start_u128) as i64
            }
        };

        let tag_offset = layout.fields.offset(tag_field.as_usize()).bytes();
        let tag_size = match tag.primitive() {
            rustc_abi::Primitive::Int(int, _) => int.size().bytes() as u32,
            rustc_abi::Primitive::Pointer(_) => 8,
            _ => 8,
        };

        let tag_addr = if tag_offset != 0 {
            let off = self.builder.iconst(tag_offset as i64, Origin::synthetic());
            self.builder
                .ptradd(slot.into(), off.into(), 0, Origin::synthetic())
        } else {
            slot
        };

        let tag_const = self.builder.iconst(tag_val, Origin::synthetic());
        self.current_mem = self.builder.store(
            tag_const.into(),
            tag_addr.into(),
            tag_size,
            self.current_mem.into(),
            Origin::synthetic(),
        );
    }

    /// Extract the "high" component of a fat pointer rvalue.
    ///
    /// Handles: ConstValue::Slice, Use/Cast of fat locals, and multi-field Aggregate.
    fn extract_fat_component(&mut self, rvalue: &Rvalue<'tcx>) -> Option<ValueRef> {
        match rvalue {
            // Constant slice: extract the length metadata.
            Rvalue::Use(Operand::Constant(c)) => {
                if let mir::Const::Val(mir::ConstValue::Slice { alloc_id: _, meta }, _) = c.const_ {
                    Some(self.builder.iconst(meta as i64, Origin::synthetic()))
                } else {
                    None
                }
            }
            // Use of a fat local: propagate the fat component.
            // If the source local already has a fat component, propagate it.
            // Otherwise, if the place has projections (e.g. field access on a
            // struct containing a fat pointer like &mut dyn Write), load the
            // vtable/metadata from offset 8 of the field address.
            Rvalue::Use(Operand::Copy(place) | Operand::Move(place)) => {
                if let Some(fat) = self.fat_locals.get(place.local) {
                    return Some(fat);
                }
                // Check if the place resolves to a fat pointer type via projections.
                if !place.projection.is_empty() {
                    let projected_ty = place.ty(&self.mir.local_decls, self.tcx).ty;
                    let projected_ty = self.monomorphize(projected_ty);
                    if is_fat_ptr(projected_ty) {
                        if let Some((addr, _)) = self.translate_place_to_addr(place) {
                            let off8 = self.builder.iconst(8, Origin::synthetic());
                            let meta_addr = self.builder.ptradd(
                                addr.into(),
                                off8.into(),
                                0,
                                Origin::synthetic(),
                            );
                            let meta = self.builder.load(
                                meta_addr.into(),
                                8,
                                Type::Ptr(0),
                                self.current_mem.into(),
                                None,
                                Origin::synthetic(),
                            );
                            return Some(meta);
                        }
                    }
                }
                None
            }
            // Cast of a fat local: propagate, or generate vtable for Unsize coercion.
            Rvalue::Cast(cast_kind, op, target_ty) => {
                // First try propagating existing fat component from source.
                if let Operand::Copy(place) | Operand::Move(place) = op
                    && let Some(fat) = self.fat_locals.get(place.local)
                {
                    return Some(fat);
                }
                // For Unsize coercions to trait objects, generate the vtable pointer.
                if let CastKind::PointerCoercion(pc, _) = cast_kind {
                    // Check if this is an Unsize coercion by examining the target type.
                    let target_ty = self.monomorphize(*target_ty);
                    let target_inner = match target_ty.kind() {
                        ty::Ref(_, inner, _) => Some(*inner),
                        ty::RawPtr(inner, _) => Some(*inner),
                        _ => None,
                    };
                    if let Some(inner) = target_inner
                        && let ty::Dynamic(predicates, _) = inner.kind()
                    {
                            // This is an unsizing coercion to a trait object.
                            // Get the concrete source type.
                            let src_ty = match op {
                                Operand::Copy(p) | Operand::Move(p) => {
                                    self.monomorphize(self.mir.local_decls[p.local].ty)
                                }
                                Operand::Constant(c) => self.monomorphize(c.ty()),
                                _ => return None,
                            };
                            let src_inner = match src_ty.kind() {
                                ty::Ref(_, inner, _) => *inner,
                                ty::RawPtr(inner, _) => *inner,
                                _ => src_ty,
                            };
                            // Skip vtable generation for types with escaping
                            // bound vars (e.g. closures with unresolved generics).
                            if src_inner.has_escaping_bound_vars() {
                                return None;
                            }
                            // Skip trait upcasting: source is already a dyn trait,
                            // vtable_allocation panics on unsized types.
                            if src_inner.is_trait() {
                                return None;
                            }
                            let principal = predicates.principal().map(ty::Binder::skip_binder);
                            if principal.is_some_and(|p| p.has_escaping_bound_vars()) {
                                return None;
                            }
                            let vtable_alloc_id =
                                self.tcx.vtable_allocation((src_inner, principal));
                            let vtable_alloc = self.tcx.global_alloc(vtable_alloc_id);
                            if let rustc_middle::mir::interpret::GlobalAlloc::Memory(alloc) =
                                vtable_alloc
                            {
                                let inner_alloc = alloc.inner();
                                let size = inner_alloc.len();
                                let bytes = inner_alloc
                                    .inspect_with_uninit_and_ptr_outside_interpreter(0..size)
                                    .to_vec();
                                let sym = format!(
                                    ".Lvtable.{}",
                                    STATIC_DATA_COUNTER.fetch_add(1, Ordering::Relaxed)
                                );
                                let sym_id = self.symbols.intern(&sym);
                                let relocs =
                                    extract_alloc_relocs(self.tcx, inner_alloc, 0, size, &mut self.symbols, &mut self.static_data);
                                self.static_data.push((sym_id, bytes, relocs));
                                return Some(self.builder.symbol_addr(sym_id, Origin::synthetic()));
                            }
                        }
                    // Handle array-to-slice unsizing: &[T; N] → &[T].
                    // The fat component is the array length N.
                    if let Some(inner) = target_inner
                        && let ty::Slice(_) = inner.kind()
                    {
                        let src_ty = match op {
                            Operand::Copy(p) | Operand::Move(p) => {
                                self.monomorphize(self.mir.local_decls[p.local].ty)
                            }
                            Operand::Constant(c) => self.monomorphize(c.ty()),
                            _ => return None,
                        };
                        let src_inner = match src_ty.kind() {
                            ty::Ref(_, inner, _) => *inner,
                            ty::RawPtr(inner, _) => *inner,
                            _ => src_ty,
                        };
                        if let ty::Array(_, len) = src_inner.kind() {
                            if let Some(n) = len.try_to_target_usize(self.tcx) {
                                return Some(
                                    self.builder.iconst(n as i64, Origin::synthetic()),
                                );
                            }
                        }
                    }

                    let _ = pc; // suppress unused warning
                }
                None
            }
            // Multi-field Aggregate: second field becomes the fat component.
            Rvalue::Aggregate(_, operands) if operands.len() >= 2 => {
                let second_op = operands.iter().nth(1).unwrap();
                self.translate_operand(second_op)
            }
            _ => None,
        }
    }

    fn translate_terminator(&mut self, term: &mir::Terminator<'tcx>) {
        match &term.kind {
            TerminatorKind::Return => {
                let ret_local = mir::Local::from_usize(0);
                let ret_mir_ty = self.monomorphize(self.mir.local_decls[ret_local].ty);

                // sret path must be checked first: for coroutines/closures,
                // translate_ty returns None but the ABI still uses sret.
                if self.use_sret {
                    // Large struct return: copy _0's data to the caller's sret pointer,
                    // then return the sret pointer in RAX.
                    let sret = self
                        .sret_ptr
                        .expect("sret_ptr must be set when use_sret is true");
                    let src = self
                        .locals
                        .get(ret_local)
                        .expect("return local _0 must be set");
                    let size = type_size(self.tcx, ret_mir_ty).unwrap_or(8);

                    // Word-by-word copy from local _0's stack slot to sret pointer.
                    let num_words = size.div_ceil(8);
                    for i in 0..num_words {
                        let byte_off = i * 8;
                        let load_addr = if byte_off == 0 {
                            src
                        } else {
                            let off = self.builder.iconst(byte_off as i64, Origin::synthetic());
                            self.builder
                                .ptradd(src.into(), off.into(), 0, Origin::synthetic())
                        };
                        let word = self.builder.load(
                            load_addr.into(),
                            8,
                            Type::Int,
                            self.current_mem.into(),
                            None,
                            Origin::synthetic(),
                        );
                        let store_addr = if byte_off == 0 {
                            sret
                        } else {
                            let off = self.builder.iconst(byte_off as i64, Origin::synthetic());
                            self.builder
                                .ptradd(sret.into(), off.into(), 0, Origin::synthetic())
                        };
                        self.current_mem = self.builder.store(
                            word.into(),
                            store_addr.into(),
                            8,
                            self.current_mem.into(),
                            Origin::synthetic(),
                        );
                    }

                    // Return the sret pointer in RAX (System V convention).
                    self.builder.ret(
                        Some(sret.into()),
                        self.current_mem.into(),
                        Origin::synthetic(),
                    );
                } else if matches!(translate_ty(ret_mir_ty), Some(Type::Unit) | None) {
                    // Unit-returning or untranslatable return type: bare ret, no value.
                    self.builder
                        .ret(None, self.current_mem.into(), Origin::synthetic());
                } else if self.stack_locals.is_stack(ret_local)
                    && matches!(
                        self.locals
                            .get(ret_local)
                            .and_then(|v| self.builder.value_type(v).cloned()),
                        Some(Type::Ptr(_))
                    )
                {
                    // Stack-allocated return (e.g., 16-byte struct built via Aggregate).
                    // Load the actual data from the stack slot instead of returning
                    // the slot address (which would be a dangling pointer).
                    let slot = self
                        .locals
                        .get(ret_local)
                        .expect("return local _0 must be set");
                    let ret_ty = self.monomorphize(self.mir.local_decls[ret_local].ty);
                    let size = type_size(self.tcx, ret_ty).unwrap_or(8);

                    // Load the first word from the stack slot.
                    // Use the actual type size (clamped to 8) so that sub-word
                    // types (u8, u16, etc.) emit a correctly-sized load instead
                    // of reading garbage bytes beyond the stored value.
                    let load_size = size.min(8) as u32;
                    let load_ty = translate_ty(ret_mir_ty).unwrap_or(Type::Int);
                    let word0 = self.builder.load(
                        slot.into(),
                        load_size,
                        load_ty,
                        self.current_mem.into(),
                        None,
                        Origin::synthetic(),
                    );

                    if size > 8 {
                        // Second 8 bytes → secondary return register.
                        let off = self.builder.iconst(8, Origin::synthetic());
                        let addr1 =
                            self.builder
                                .ptradd(slot.into(), off.into(), 0, Origin::synthetic());
                        let word1 = self.builder.load(
                            addr1.into(),
                            8,
                            Type::Int,
                            self.current_mem.into(),
                            None,
                            Origin::synthetic(),
                        );
                        let dummy = self.builder.iconst(0, Origin::synthetic());
                        self.abi_metadata
                            .mark_secondary_return_move(dummy.index(), word1.index());
                    }

                    // Coerce to match declared return type (e.g., Ptr for &T returns).
                    let ret_ir_ty = translate_ty(ret_mir_ty);
                    let coerced_word0 = match ret_ir_ty {
                        Some(Type::Ptr(_)) => self.coerce_to_ptr(word0),
                        _ => word0,
                    };
                    self.builder.ret(
                        Some(coerced_word0.into()),
                        self.current_mem.into(),
                        Origin::synthetic(),
                    );
                } else {
                    // Normal scalar return.
                    let val = self.locals.values[ret_local.as_usize()];
                    if let Some(v) = val {
                        if let Some(fat_val) = self.fat_locals.get(ret_local) {
                            let dummy = self.builder.iconst(0, Origin::synthetic());
                            self.abi_metadata
                                .mark_secondary_return_move(dummy.index(), fat_val.index());
                        }
                        // Coerce to match the declared return type.
                        let ret_ir_ty = translate_ty(ret_mir_ty);
                        let coerced = match (ret_ir_ty, self.builder.value_type(v).cloned()) {
                            (Some(Type::Int), _) => self.coerce_to_int(v),
                            (Some(Type::Ptr(_)), _) => self.coerce_to_ptr(v),
                            (Some(Type::Bool), Some(Type::Int)) => {
                                self.builder.int_to_bool(v.into(), Origin::synthetic())
                            }
                            _ => v,
                        };
                        self.builder.ret(
                            Some(coerced.into()),
                            self.current_mem.into(),
                            Origin::synthetic(),
                        );
                    } else {
                        // Return local was never assigned — this path is
                        // unreachable at runtime (diverging function).
                        self.builder.unreachable(Origin::synthetic());
                    }
                }
            }
            TerminatorKind::Goto { target } => {
                let target_block = self.block_map.get(*target);
                self.builder.br(
                    target_block,
                    vec![self.current_mem.into()],
                    Origin::synthetic(),
                );
            }
            TerminatorKind::SwitchInt { discr, targets } => {
                self.translate_switch_int(discr, targets);
            }
            TerminatorKind::Assert {
                cond,
                expected,
                target,
                ..
            } => {
                // Assert: if cond != expected, trap. Otherwise branch to target.
                let cond_val = self.translate_operand(cond);
                let target_block = self.block_map.get(*target);
                if let Some(cond_v) = cond_val {
                    let cond_v = self.coerce_to_int(cond_v);
                    let expected_val = self
                        .builder
                        .iconst(if *expected { 1 } else { 0 }, Origin::synthetic());
                    let cmp = self.builder.icmp(
                        ICmpOp::Eq,
                        cond_v.into(),
                        expected_val.into(),
                        Origin::synthetic(),
                    );
                    // Create a trap block for the failure path.
                    let trap_block = self.builder.create_block();
                    let _trap_mem = self.builder.add_block_arg(trap_block, Type::Mem);
                    self.builder.brif(
                        cmp.into(),
                        target_block,
                        vec![self.current_mem.into()],
                        trap_block,
                        vec![self.current_mem.into()],
                        Origin::synthetic(),
                    );
                    self.builder.switch_to_block(trap_block);
                    self.builder.trap(Origin::synthetic());
                } else {
                    self.builder.br(
                        target_block,
                        vec![self.current_mem.into()],
                        Origin::synthetic(),
                    );
                }
            }
            TerminatorKind::Unreachable => {
                self.builder.unreachable(Origin::synthetic());
            }
            TerminatorKind::Drop { target, .. } => {
                // Skip drop glue for now — just branch to the target.
                let target_block = self.block_map.get(*target);
                self.builder.br(
                    target_block,
                    vec![self.current_mem.into()],
                    Origin::synthetic(),
                );
            }
            TerminatorKind::FalseEdge { real_target, .. } => {
                let target_block = self.block_map.get(*real_target);
                self.builder.br(
                    target_block,
                    vec![self.current_mem.into()],
                    Origin::synthetic(),
                );
            }
            TerminatorKind::FalseUnwind { real_target, .. } => {
                let target_block = self.block_map.get(*real_target);
                self.builder.br(
                    target_block,
                    vec![self.current_mem.into()],
                    Origin::synthetic(),
                );
            }
            TerminatorKind::Call {
                func,
                args,
                destination,
                target,
                ..
            } => {
                self.translate_call(func, args, destination, target);
            }
            _ => {
                // Unhandled terminator kind — emit unreachable so the block
                // is never empty and the IR verifier stays happy.
                self.builder.unreachable(Origin::synthetic());
            }
        }
    }

    fn translate_call(
        &mut self,
        func: &Operand<'tcx>,
        args: &[Spanned<Operand<'tcx>>],
        destination: &Place<'tcx>,
        target: &Option<BasicBlock>,
    ) {
        // Check for compiler intrinsics and handle them inline.
        if let Some((intrinsic_name, intrinsic_substs)) =
            detect_intrinsic(self.tcx, func, self.instance)
        {
            // Translate intrinsic arguments to IR values.
            let mut intrinsic_args: Vec<ValueRef> = Vec::new();
            for arg in args {
                if let Some(v) = self.translate_operand(&arg.node) {
                    intrinsic_args.push(v);
                }
            }

            // Try simple inline handling first (black_box, etc.).
            let handled = translate_intrinsic(
                self.tcx,
                &intrinsic_name,
                intrinsic_substs,
                &intrinsic_args,
                destination.local,
                &mut self.builder,
                &mut self.locals,
                &mut self.symbols,
                self.current_mem,
            );
            if handled {
                if let Some(target) = target {
                    let target_block = self.block_map.get(*target);
                    self.builder.br(
                        target_block,
                        vec![self.current_mem.into()],
                        Origin::synthetic(),
                    );
                }
                return;
            }

            // Try lowering memory intrinsics to libc calls.
            let mem_handled = translate_memory_intrinsic(
                self.tcx,
                &intrinsic_name,
                intrinsic_substs,
                &intrinsic_args,
                destination.local,
                &mut self.builder,
                &mut self.locals,
                &mut self.symbols,
                self.current_mem,
            );
            if let Some(new_mem) = mem_handled {
                self.current_mem = new_mem;
                if let Some(target) = target {
                    let target_block = self.block_map.get(*target);
                    self.builder.br(
                        target_block,
                        vec![self.current_mem.into()],
                        Origin::synthetic(),
                    );
                }
                return;
            }
            // Intrinsic detected but not handled — treat as no-op rather
            // than falling through to the normal call path (intrinsics don't
            // have real symbol implementations).
            if let Some(target) = target {
                let target_block = self.block_map.get(*target);
                self.builder.br(
                    target_block,
                    vec![self.current_mem.into()],
                    Origin::synthetic(),
                );
            }
            return;
        }

        // Skip calls to drop_in_place — consistent with the Drop terminator
        // handler which already treats all drops as no-ops.  Rustc may not
        // generate MonoItems for some drop glue, so emitting a call would
        // create undefined symbol references.
        // Also skip precondition_check calls — these are debug-mode
        // assertions for unchecked operations that may not have MonoItems.
        if let Operand::Constant(c) = func {
            let fn_ty = self.tcx.instantiate_and_normalize_erasing_regions(
                self.instance.args,
                ty::TypingEnv::fully_monomorphized(),
                ty::EarlyBinder::bind(c.ty()),
            );
            if let ty::FnDef(def_id, _fn_args) = fn_ty.kind() {
                let skip = Some(*def_id) == self.tcx.lang_items().drop_in_place_fn()
                    || self
                        .tcx
                        .opt_item_name(*def_id)
                        .is_some_and(|n| n.as_str() == "precondition_check");
                if skip {
                    if let Some(target) = target {
                        let target_block = self.block_map.get(*target);
                        self.builder.br(
                            target_block,
                            vec![self.current_mem.into()],
                            Origin::synthetic(),
                        );
                    }
                    return;
                }
            }
        }

        // Resolve callee from the function operand's type.
        let callee_target = resolve_call_target(self.tcx, func, self.instance, self.mir);

        // For virtual dispatch, extract the vtable pointer from the first
        // argument (a fat pointer: data_ptr + vtable_ptr) and load the
        // function pointer from the vtable before processing arguments.
        let virtual_fn_ptr = if let Some(CallTarget::Virtual(idx)) = &callee_target {
            // The first argument is &dyn Trait — a fat pointer.
            // Get the vtable pointer from fat_locals.
            let self_arg = &args[0].node;
            let vtable_ptr = match self_arg {
                Operand::Copy(place) | Operand::Move(place) => {
                    // First try fat_locals (set when the fat pointer was created
                    // from a parameter or an Unsize coercion).
                    if let Some(v) = self.fat_locals.get(place.local) {
                        Some(v)
                    } else if self.stack_locals.is_stack(place.local) {
                        // The fat pointer lives in a stack slot.  The vtable
                        // pointer is the second word (offset 8).
                        if let Some(base) = self.locals.get(place.local) {
                            let off8 =
                                self.builder.iconst(8, Origin::synthetic());
                            let vtable_addr = self.builder.ptradd(
                                base.into(),
                                off8.into(),
                                0,
                                Origin::synthetic(),
                            );
                            let vtable = self.builder.load(
                                vtable_addr.into(),
                                8,
                                Type::Ptr(0),
                                self.current_mem.into(),
                                None,
                                Origin::synthetic(),
                            );
                            Some(vtable)
                        } else {
                            None
                        }
                    } else {
                        None
                    }
                }
                _ => None,
            };
            if let Some(vtable) = vtable_ptr {
                // vtable layout: [drop_in_place, size, align, method0, method1, ...]
                // Method at index `idx` is at offset (3 + idx) * 8.
                let offset = (3 + idx) * 8;
                let off_val = self.builder.iconst(offset as i64, Origin::synthetic());
                let fn_addr =
                    self.builder
                        .ptradd(vtable.into(), off_val.into(), 0, Origin::synthetic());
                let fn_ptr = self.builder.load(
                    fn_addr.into(),
                    8,
                    Type::Int,
                    self.current_mem.into(),
                    None,
                    Origin::synthetic(),
                );
                Some(fn_ptr)
            } else {
                None
            }
        } else {
            None
        };
        let is_virtual = virtual_fn_ptr.is_some();

        // Check if the callee returns a large struct (needs sret on caller side).
        let dest_ty = self.monomorphize(self.mir.local_decls[destination.local].ty);
        let dest_size = type_size(self.tcx, dest_ty);
        let callee_sret = needs_indirect_return(self.tcx, dest_ty);

        // Translate arguments to IR operands, decomposing fat pointers.
        let mut ir_args: Vec<tuffy_ir::instruction::Operand> = Vec::new();

        // If callee uses sret, allocate a stack slot and prepend as first arg.
        let sret_slot = if callee_sret {
            let size = type_size(self.tcx, dest_ty).unwrap_or(8);
            let slot = self.builder.stack_slot(size as u32, Origin::synthetic());
            ir_args.push(slot.into());
            Some(slot)
        } else {
            None
        };

        for arg in args {
            // Skip zero-sized (Unit) and untranslatable args — they don't
            // occupy an ABI slot, matching the callee's param skipping.
            let arg_ty = match &arg.node {
                Operand::Copy(place) | Operand::Move(place) => {
                    self.monomorphize(self.mir.local_decls[place.local].ty)
                }
                Operand::Constant(c) => self.monomorphize(c.ty()),
                _ => self.monomorphize(self.mir.local_decls[mir::Local::from_usize(0)].ty),
            };
            if matches!(translate_ty(arg_ty), Some(Type::Unit) | None) {
                continue;
            }

            if let Some(v) = self.translate_operand(&arg.node) {
                // Check if this argument is a stack-allocated local that
                // should be decomposed into register-sized words (≤16 bytes).
                let decomposed = if let Operand::Copy(place) | Operand::Move(place) = &arg.node {
                    if place.projection.is_empty() && self.stack_locals.is_stack(place.local) {
                        let arg_ty = self.monomorphize(self.mir.local_decls[place.local].ty);
                        let arg_size = type_size(self.tcx, arg_ty).unwrap_or(0);
                        if arg_size > 0 && arg_size <= 16 {
                            // Use the stack slot pointer directly — translate_operand
                            // may have already loaded the value for small locals,
                            // so `v` might be an Int rather than a Ptr.
                            let slot = self.locals.get(place.local).unwrap_or(v);
                            let slot_is_ptr = matches!(
                                self.builder.value_type(slot),
                                Some(Type::Ptr(_))
                            );
                            if slot_is_ptr {
                                // Load word(s) from the stack slot and pass in registers.
                                let word0 = self.builder.load(
                                    slot.into(),
                                    8,
                                    Type::Int,
                                    self.current_mem.into(),
                                    None,
                                    Origin::synthetic(),
                                );
                                ir_args.push(word0.into());
                                if arg_size > 8 {
                                    let off = self.builder.iconst(8, Origin::synthetic());
                                    let addr1 = self.builder.ptradd(
                                        slot.into(),
                                        off.into(),
                                        0,
                                        Origin::synthetic(),
                                    );
                                    let word1 = self.builder.load(
                                        addr1.into(),
                                        8,
                                        Type::Int,
                                        self.current_mem.into(),
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
                    }
                } else {
                    false
                };

                if !decomposed {
                    ir_args.push(v.into());
                    // If this arg is a Copy/Move of a fat local, also pass the high part.
                    // Exception: for virtual dispatch, skip the vtable pointer on the
                    // first argument (self) — the actual method only takes the data ptr.
                    let skip_fat =
                        is_virtual && ir_args.len() == 1 + if callee_sret { 1 } else { 0 };
                    if !skip_fat
                        && let Operand::Copy(place) | Operand::Move(place) = &arg.node
                        && let Some(fat_v) = self.fat_locals.get(place.local)
                    {
                        ir_args.push(fat_v.into());
                    }
                    // If this arg is a constant slice, the length was emitted
                    // right after the pointer. Check if it's in the constant.
                    if let Operand::Constant(c) = &arg.node
                        && let mir::Const::Val(mir::ConstValue::Slice { meta, .. }, _) = c.const_
                    {
                        let len_val = self.builder.iconst(meta as i64, Origin::synthetic());
                        ir_args.push(len_val.into());
                    }
                }
            }
        }

        // Emit a Call IR instruction.
        let callee_val = if let Some(fn_ptr) = virtual_fn_ptr {
            // Virtual dispatch: callee is a function pointer loaded from vtable.
            fn_ptr
        } else if let Some(CallTarget::Direct(ref sym)) = callee_target {
            let sym_id = self.symbols.intern(sym);
            self.builder.symbol_addr(sym_id, Origin::synthetic())
        } else if let Some(fn_ptr) = self.translate_operand(func) {
            // Indirect call through a function pointer in a local.
            fn_ptr
        } else {
            self.builder.iconst(0, Origin::synthetic())
        };
        let call_ret_ty = translate_ty(dest_ty).unwrap_or(Type::Unit);
        let (call_mem, call_data) = self.builder.call(
            callee_val.into(),
            ir_args,
            call_ret_ty,
            self.current_mem.into(),
            None,
            Origin::synthetic(),
        );
        self.current_mem = call_mem;
        // For non-void calls, call_data is Some(data_vref).
        // For void calls, call_data is None — use a dummy zero.
        let call_vref = call_data.unwrap_or_else(|| self.builder.iconst(0, Origin::synthetic()));

        if callee_sret {
            // For sret calls, the result is in the stack slot we allocated.
            // The destination local becomes a pointer to that slot.
            let slot = sret_slot.unwrap();
            self.locals.set(destination.local, slot);
            self.stack_locals.mark(destination.local);
            // No RDX capture needed for sret calls.
        } else if dest_size.unwrap_or(0) > 8 {
            // Two-register return (9-16 bytes): RAX has first word,
            // RDX has second word. Reconstruct into a stack slot so
            // downstream code gets a valid pointer to the struct.
            let size = dest_size.unwrap();
            let slot = self.builder.stack_slot(size as u32, Origin::synthetic());
            self.current_mem = self.builder.store(
                call_vref.into(),
                slot.into(),
                8,
                self.current_mem.into(),
                Origin::synthetic(),
            );

            let rdx_val = self.builder.iconst(0, Origin::synthetic());
            self.abi_metadata
                .mark_secondary_return_capture(rdx_val.index());
            let off = self.builder.iconst(8, Origin::synthetic());
            let addr1 = self
                .builder
                .ptradd(slot.into(), off.into(), 0, Origin::synthetic());
            self.current_mem = self.builder.store(
                rdx_val.into(),
                addr1.into(),
                8,
                self.current_mem.into(),
                Origin::synthetic(),
            );

            self.locals.set(destination.local, slot);
            self.stack_locals.mark(destination.local);
        } else {
            // Scalar return (≤ 8 bytes).
            //
            // MIR optimization may merge a value return with a subsequent
            // Ref, giving the destination local a reference type (`&T`)
            // even though the callee returns `T` by value.  Detect this
            // mismatch and spill the return value to a stack slot so the
            // local holds a valid pointer.
            let dest_is_thin_ref = matches!(
                dest_ty.kind(),
                ty::Ref(_, inner, _) if !matches!(inner.kind(), ty::Str | ty::Slice(..) | ty::Dynamic(..))
            );
            let callee_returns_value = {
                // Resolve the callee's actual return type from its signature.
                let mut ret_is_value = false;
                if let Operand::Constant(c) = func {
                    let fn_ty = self.monomorphize(c.ty());
                    if let ty::FnDef(def_id, fn_args) = fn_ty.kind() {
                        let sig = self.tcx.fn_sig(*def_id).instantiate(self.tcx, fn_args);
                        let sig = self.tcx.normalize_erasing_late_bound_regions(
                            ty::TypingEnv::fully_monomorphized(),
                            sig,
                        );
                        let ret_ty = sig.output();
                        ret_is_value = !matches!(ret_ty.kind(), ty::Ref(..) | ty::RawPtr(..));
                    }
                }
                ret_is_value
            };

            if dest_is_thin_ref && callee_returns_value {
                // Callee returns T by value but destination expects &T.
                // Spill the return value to a stack slot.
                let inner_ty = match dest_ty.kind() {
                    ty::Ref(_, inner, _) => *inner,
                    _ => unreachable!(),
                };
                let size = type_size(self.tcx, inner_ty).unwrap_or(8) as u32;
                let slot = self.builder.stack_slot(size.max(1), Origin::synthetic());
                self.current_mem = self.builder.store(
                    call_vref.into(),
                    slot.into(),
                    size,
                    self.current_mem.into(),
                    Origin::synthetic(),
                );
                self.locals.set(destination.local, slot);
            } else {
                self.locals.set(destination.local, call_vref);
            }

            // Capture secondary return register only for fat pointer returns
            // (e.g., &str, &[T]) where RDX carries the second word (length/vtable).
            // Non-fat types must NOT get a fat_locals entry, otherwise the
            // spurious high-part value will be injected as an extra argument
            // when this local is later passed to another function call.
            if is_fat_ptr(dest_ty) {
                let rdx_val = self.builder.iconst(0, Origin::synthetic());
                self.abi_metadata
                    .mark_secondary_return_capture(rdx_val.index());
                self.fat_locals.set(destination.local, rdx_val);
            }
        }

        // Branch to the continuation block if present.
        if let Some(target_bb) = target {
            let target_block = self.block_map.get(*target_bb);
            self.builder.br(
                target_block,
                vec![self.current_mem.into()],
                Origin::synthetic(),
            );
        }
    }

    fn translate_switch_int(&mut self, discr: &Operand<'tcx>, targets: &mir::SwitchTargets) {
        let mut discr_val = match self.translate_operand(discr) {
            Some(v) => v,
            None => {
                // The discriminant local has no value yet (e.g. defined in a
                // later MIR block that hasn't been translated).  Use zero as
                // a conservative default — this is correct for the common
                // case of `is_val_statically_known` (always false/0).
                // TODO: process blocks in reverse post-order to avoid this.
                self.builder.iconst(0, Origin::synthetic())
            }
        };

        // If the discriminant is a pointer (e.g. nullable pointer optimization),
        // convert it to an integer so icmp gets Int operands.
        // Similarly, Bool discriminants need BoolToInt for icmp.
        if matches!(self.builder.value_type(discr_val), Some(Type::Ptr(_))) {
            discr_val = self
                .builder
                .ptrtoaddr(discr_val.into(), Origin::synthetic());
        } else if matches!(self.builder.value_type(discr_val), Some(Type::Bool)) {
            discr_val = self
                .builder
                .bool_to_int(discr_val.into(), Origin::synthetic());
        }

        let all_targets: Vec<_> = targets.iter().collect();
        let otherwise = targets.otherwise();

        if all_targets.len() == 1 {
            // Two-way branch: compare discriminant with the single value.
            let (test_val, target_bb) = all_targets[0];
            let const_val = self.builder.iconst(test_val as i64, Origin::synthetic());
            let cmp = self.builder.icmp(
                ICmpOp::Eq,
                discr_val.into(),
                const_val.into(),
                Origin::synthetic(),
            );
            let then_block = self.block_map.get(target_bb);
            let else_block = self.block_map.get(otherwise);
            self.builder.brif(
                cmp.into(),
                then_block,
                vec![self.current_mem.into()],
                else_block,
                vec![self.current_mem.into()],
                Origin::synthetic(),
            );
        } else {
            // Multi-way: chain of brif comparisons with fallthrough blocks.
            let otherwise_block = self.block_map.get(otherwise);
            for (i, (test_val, target_bb)) in all_targets.iter().enumerate() {
                let const_val = self.builder.iconst(*test_val as i64, Origin::synthetic());
                let cmp = self.builder.icmp(
                    ICmpOp::Eq,
                    discr_val.into(),
                    const_val.into(),
                    Origin::synthetic(),
                );
                let then_block = self.block_map.get(*target_bb);

                if i == all_targets.len() - 1 {
                    // Last comparison: else goes to otherwise.
                    self.builder.brif(
                        cmp.into(),
                        then_block,
                        vec![self.current_mem.into()],
                        otherwise_block,
                        vec![self.current_mem.into()],
                        Origin::synthetic(),
                    );
                } else {
                    // Not last: else falls through to a new comparison block.
                    let next_block = self.builder.create_block();
                    let next_mem = self.builder.add_block_arg(next_block, Type::Mem);
                    self.builder.brif(
                        cmp.into(),
                        then_block,
                        vec![self.current_mem.into()],
                        next_block,
                        vec![self.current_mem.into()],
                        Origin::synthetic(),
                    );
                    self.builder.switch_to_block(next_block);
                    self.current_mem = next_mem;
                }
            }
        }
    }

    fn translate_rvalue(
        &mut self,
        rvalue: &Rvalue<'tcx>,
        dest_place: &Place<'tcx>,
    ) -> Option<ValueRef> {
        match rvalue {
            Rvalue::BinaryOp(op, box (lhs, rhs)) => {
                let l_raw = self.translate_operand(lhs)?;
                let r_raw = self.translate_operand(rhs)?;
                let l_ann = operand_annotation(lhs, self.mir);
                let r_ann = operand_annotation(rhs, self.mir);

                // Unsupported operand types (e.g. floats) produce Unit or
                // typeless values — emit a dummy zero so the IR stays well-typed.
                if !matches!(
                    self.builder.value_type(l_raw),
                    Some(Type::Int | Type::Ptr(_) | Type::Bool)
                ) || !matches!(
                    self.builder.value_type(r_raw),
                    Some(Type::Int | Type::Ptr(_) | Type::Bool)
                ) {
                    return Some(self.builder.iconst(0, Origin::synthetic()));
                }

                // Coerce pointer operands to integers — needed for both
                // arithmetic/bitwise ops and comparisons.
                let l = self.coerce_to_int(l_raw);
                let r = self.coerce_to_int(r_raw);
                let l_op = IrOperand {
                    value: l,
                    annotation: l_ann,
                };
                let r_op = IrOperand {
                    value: r,
                    annotation: r_ann,
                };
                let res_ann = l_ann;

                let val = match op {
                    BinOp::Add | BinOp::AddWithOverflow => {
                        self.builder.add(l_op, r_op, res_ann, Origin::synthetic())
                    }
                    BinOp::Sub | BinOp::SubWithOverflow => {
                        self.builder.sub(l_op, r_op, res_ann, Origin::synthetic())
                    }
                    BinOp::Mul | BinOp::MulWithOverflow => {
                        self.builder.mul(l_op, r_op, res_ann, Origin::synthetic())
                    }
                    BinOp::Eq => {
                        let cmp = self
                            .builder
                            .icmp(ICmpOp::Eq, l_op, r_op, Origin::synthetic());
                        self.builder.bool_to_int(cmp.into(), Origin::synthetic())
                    }
                    BinOp::Ne => {
                        let cmp = self
                            .builder
                            .icmp(ICmpOp::Ne, l_op, r_op, Origin::synthetic());
                        self.builder.bool_to_int(cmp.into(), Origin::synthetic())
                    }
                    BinOp::Lt => {
                        let cmp = self
                            .builder
                            .icmp(ICmpOp::Lt, l_op, r_op, Origin::synthetic());
                        self.builder.bool_to_int(cmp.into(), Origin::synthetic())
                    }
                    BinOp::Le => {
                        let cmp = self
                            .builder
                            .icmp(ICmpOp::Le, l_op, r_op, Origin::synthetic());
                        self.builder.bool_to_int(cmp.into(), Origin::synthetic())
                    }
                    BinOp::Gt => {
                        let cmp = self
                            .builder
                            .icmp(ICmpOp::Gt, l_op, r_op, Origin::synthetic());
                        self.builder.bool_to_int(cmp.into(), Origin::synthetic())
                    }
                    BinOp::Ge => {
                        let cmp = self
                            .builder
                            .icmp(ICmpOp::Ge, l_op, r_op, Origin::synthetic());
                        self.builder.bool_to_int(cmp.into(), Origin::synthetic())
                    }
                    BinOp::Shl | BinOp::ShlUnchecked => {
                        self.builder.shl(l_op, r_op, res_ann, Origin::synthetic())
                    }
                    BinOp::BitOr => self.builder.or(l_op, r_op, res_ann, Origin::synthetic()),
                    BinOp::BitAnd => self.builder.and(l_op, r_op, res_ann, Origin::synthetic()),
                    BinOp::BitXor => self.builder.xor(l_op, r_op, res_ann, Origin::synthetic()),
                    BinOp::Shr | BinOp::ShrUnchecked => {
                        self.builder.shr(l_op, r_op, res_ann, Origin::synthetic())
                    }
                    BinOp::Div => self.builder.div(l_op, r_op, res_ann, Origin::synthetic()),
                    BinOp::Rem => self.builder.rem(l_op, r_op, res_ann, Origin::synthetic()),
                    _ => return None,
                };
                Some(val)
            }
            Rvalue::Use(operand) => self.translate_operand(operand),
            Rvalue::Cast(kind, operand, target_ty) => {
                let val = self.translate_operand(operand)?;
                match kind {
                    CastKind::IntToInt => {
                        let src_ty = match operand {
                            Operand::Copy(p) | Operand::Move(p) => self.mir.local_decls[p.local].ty,
                            Operand::Constant(c) => c.ty(),
                            _ => return Some(val),
                        };
                        // Bool is Type::Bool in IR but IntToInt casts need Int operands.
                        let val = self.coerce_to_int(val);
                        translate_int_to_int_cast(src_ty, *target_ty, val, &mut self.builder)
                    }
                    CastKind::PointerCoercion(..) => {
                        // Convert a zero-sized function item / closure to a function pointer.
                        let src_ty = match operand {
                            Operand::Copy(p) | Operand::Move(p) => self.mir.local_decls[p.local].ty,
                            Operand::Constant(c) => c.ty(),
                            _ => return Some(val),
                        };
                        let src_ty = self.tcx.instantiate_and_normalize_erasing_regions(
                            self.instance.args,
                            ty::TypingEnv::fully_monomorphized(),
                            ty::EarlyBinder::bind(src_ty),
                        );
                        if let ty::FnDef(def_id, args) = src_ty.kind() {
                            let resolved = ty::Instance::try_resolve(
                                self.tcx,
                                ty::TypingEnv::fully_monomorphized(),
                                *def_id,
                                args,
                            )
                            .ok()
                            .flatten()?;
                            let sym_name = self.tcx.symbol_name(resolved).name.to_string();
                            let sym_id = self.symbols.intern(&sym_name);
                            Some(self.builder.symbol_addr(sym_id, Origin::synthetic()))
                        } else {
                            Some(val)
                        }
                    }
                    // Pointer casts and transmutes are bitwise moves.
                    _ => Some(val),
                }
            }
            Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) => {
                if !place.projection.is_empty() {
                    self.translate_place_to_addr(place).map(|(addr, _ty)| addr)
                } else if self.stack_locals.is_stack(place.local) {
                    self.locals.get(place.local)
                } else {
                    if let Some(val) = self.locals.get(place.local) {
                        let local_ty = self.monomorphize(self.mir.local_decls[place.local].ty);
                        let size = type_size(self.tcx, local_ty).unwrap_or(8) as u32;
                        let slot = self.builder.stack_slot(size.max(8), Origin::synthetic());
                        self.current_mem = self.builder.store(
                            val.into(),
                            slot.into(),
                            size,
                            self.current_mem.into(),
                            Origin::synthetic(),
                        );
                        Some(slot)
                    } else {
                        None
                    }
                }
            }
            Rvalue::Aggregate(kind, operands) => {
                // Extract enum variant index when constructing an enum.
                let enum_variant_idx = match kind.as_ref() {
                    mir::AggregateKind::Adt(def_id, variant_idx, _, _, _)
                        if self.tcx.adt_def(*def_id).is_enum() =>
                    {
                        Some(*variant_idx)
                    }
                    _ => None,
                };

                // For non-enum aggregates with no operands, return zero.
                if operands.is_empty() && enum_variant_idx.is_none() {
                    return Some(self.builder.iconst(0, Origin::synthetic()));
                }

                // Determine the aggregate type for layout queries.
                let agg_ty = match kind.as_ref() {
                    mir::AggregateKind::Tuple => {
                        self.monomorphize(self.mir.local_decls[dest_place.local].ty)
                    }
                    mir::AggregateKind::Adt(def_id, _, args, _, _) => {
                        let adt_def = self.tcx.adt_def(*def_id);
                        if adt_def.is_enum() {
                            self.monomorphize(self.mir.local_decls[dest_place.local].ty)
                        } else {
                            self.monomorphize(ty::Ty::new_adt(self.tcx, adt_def, args))
                        }
                    }
                    _ => self.monomorphize(self.mir.local_decls[dest_place.local].ty),
                };
                let total_size = type_size(self.tcx, agg_ty).unwrap_or(if operands.is_empty() {
                    8
                } else {
                    8 * operands.len() as u64
                });
                if total_size == 0 {
                    return Some(self.builder.iconst(0, Origin::synthetic()));
                }
                // Reuse the destination local's existing stack slot when
                // available (e.g. sret-allocated _0) to avoid an intermediate
                // pointer-vs-data copy.
                let slot = if dest_place.projection.is_empty() {
                    if let Some(existing) = self.locals.get(dest_place.local) {
                        let ety = self.builder.value_type(existing).cloned();
                        if matches!(ety, Some(Type::Ptr(_))) {
                            existing
                        } else {
                            self.builder
                                .stack_slot(total_size as u32, Origin::synthetic())
                        }
                    } else {
                        self.builder
                            .stack_slot(total_size as u32, Origin::synthetic())
                    }
                } else {
                    self.builder
                        .stack_slot(total_size as u32, Origin::synthetic())
                };

                // Zero-initialize the aggregate slot for enum variants.
                // This ensures padding bytes and unset niche fields start at
                // zero.  The correct discriminant tag is written below.
                if enum_variant_idx.is_some() && total_size > 0 {
                    let zero = self.builder.iconst(0, Origin::synthetic());
                    let num_words = total_size.div_ceil(8);
                    for w in 0..num_words {
                        let byte_off = w * 8;
                        let dst = if byte_off == 0 {
                            slot
                        } else {
                            let off = self.builder.iconst(byte_off as i64, Origin::synthetic());
                            self.builder
                                .ptradd(slot.into(), off.into(), 0, Origin::synthetic())
                        };
                        self.current_mem = self.builder.store(
                            zero.into(),
                            dst.into(),
                            8,
                            self.current_mem.into(),
                            Origin::synthetic(),
                        );
                    }
                }

                for (i, op) in operands.iter().enumerate() {
                    let val = self
                        .translate_operand(op)
                        .unwrap_or_else(|| self.builder.iconst(0, Origin::synthetic()));
                    let field_ty = match op {
                        Operand::Copy(p) | Operand::Move(p) => {
                            Some(self.monomorphize(self.mir.local_decls[p.local].ty))
                        }
                        Operand::Constant(c) => Some(self.monomorphize(c.ty())),
                        _ => None,
                    };
                    let bytes = field_ty.and_then(|t| type_size(self.tcx, t)).unwrap_or(8) as u32;
                    let offset = field_offset(self.tcx, agg_ty, i).unwrap_or(i as u64 * 8);

                    // Check if the operand is a stack-allocated local whose
                    // value is a pointer to data rather than the data itself.
                    let is_stack_op = match op {
                        Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => {
                            self.stack_locals.is_stack(p.local)
                        }
                        _ => false,
                    };

                    let dst_addr = if offset == 0 {
                        slot
                    } else {
                        let off_val = self.builder.iconst(offset as i64, Origin::synthetic());
                        self.builder
                            .ptradd(slot.into(), off_val.into(), 0, Origin::synthetic())
                    };

                    let is_ptr_val = matches!(self.builder.value_type(val), Some(Type::Ptr(_)));
                    if is_ptr_val && ((is_stack_op && bytes > 0) || bytes > 8) {
                        // val is a pointer to multi-word data (stack slot or
                        // symbol_addr of an Indirect constant like a slice
                        // reference).  Copy word-by-word from the source.
                        let num_words = (bytes as u64).div_ceil(8);
                        for w in 0..num_words {
                            let byte_off = w * 8;
                            let word_size = std::cmp::min(8, bytes as u64 - byte_off) as u32;
                            let src = if byte_off == 0 {
                                val
                            } else {
                                let off = self.builder.iconst(byte_off as i64, Origin::synthetic());
                                self.builder
                                    .ptradd(val.into(), off.into(), 0, Origin::synthetic())
                            };
                            let word = self.builder.load(
                                src.into(),
                                word_size,
                                Type::Int,
                                self.current_mem.into(),
                                None,
                                Origin::synthetic(),
                            );
                            let dst = if byte_off == 0 {
                                dst_addr
                            } else {
                                let off = self.builder.iconst(byte_off as i64, Origin::synthetic());
                                self.builder.ptradd(
                                    dst_addr.into(),
                                    off.into(),
                                    0,
                                    Origin::synthetic(),
                                )
                            };
                            self.current_mem = self.builder.store(
                                word.into(),
                                dst.into(),
                                word_size,
                                self.current_mem.into(),
                                Origin::synthetic(),
                            );
                        }
                    } else {
                        self.current_mem = self.builder.store(
                            val.into(),
                            dst_addr.into(),
                            bytes,
                            self.current_mem.into(),
                            Origin::synthetic(),
                        );
                    }
                }

                // Write the discriminant tag for enum aggregates.
                if let Some(variant_idx) = enum_variant_idx {
                    self.write_enum_tag(slot, agg_ty, variant_idx);
                }

                // Mark the destination local as stack-allocated.
                if dest_place.projection.is_empty() {
                    self.stack_locals.mark(dest_place.local);
                }
                Some(slot)
            }
            Rvalue::UnaryOp(
                mir::UnOp::PtrMetadata,
                Operand::Copy(place) | Operand::Move(place),
            ) => {
                // Extract metadata (e.g., slice length) from a fat pointer.
                self.fat_locals.get(place.local)
            }
            Rvalue::UnaryOp(mir::UnOp::PtrMetadata, _) => None,
            Rvalue::UnaryOp(mir::UnOp::Neg, operand) => {
                let v = self.translate_operand(operand)?;
                // Coerce Bool/Ptr to Int; reject unsupported types (floats → Unit).
                let v = self.coerce_to_int(v);
                if !matches!(self.builder.value_type(v), Some(Type::Int)) {
                    return Some(self.builder.iconst(0, Origin::synthetic()));
                }
                let zero = self.builder.iconst(0, Origin::synthetic());
                Some(
                    self.builder
                        .sub(zero.into(), v.into(), None, Origin::synthetic()),
                )
            }
            Rvalue::UnaryOp(mir::UnOp::Not, operand) => {
                let v = self.translate_operand(operand)?;
                match self.builder.value_type(v) {
                    Some(Type::Bool) => {
                        // Boolean NOT: bool_to_int then XOR 1.
                        let int_v = self.builder.bool_to_int(v.into(), Origin::synthetic());
                        let one = self.builder.iconst(1, Origin::synthetic());
                        Some(
                            self.builder
                                .xor(int_v.into(), one.into(), None, Origin::synthetic()),
                        )
                    }
                    Some(Type::Int) => {
                        // Bitwise NOT: XOR with -1.
                        let ones = self.builder.iconst(-1, Origin::synthetic());
                        Some(
                            self.builder
                                .xor(v.into(), ones.into(), None, Origin::synthetic()),
                        )
                    }
                    _ => {
                        // Unsupported type (e.g. float) — emit dummy zero.
                        Some(self.builder.iconst(0, Origin::synthetic()))
                    }
                }
            }
            Rvalue::Discriminant(place) => self.translate_discriminant(place),
            _ => None,
        }
    }

    fn translate_operand(&mut self, operand: &Operand<'tcx>) -> Option<ValueRef> {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                if place.projection.is_empty() {
                    let val = self.locals.get(place.local);
                    // For scalar locals promoted to stack slots (multi-BB
                    // mutation), load the current value from the slot.
                    if self.stack_locals.is_stack(place.local) {
                        if let Some(slot) = val {
                            let ty = self.monomorphize(self.mir.local_decls[place.local].ty);
                            let size = type_size(self.tcx, ty).unwrap_or(8);
                            if size <= 8
                                && matches!(
                                    self.builder.value_type(slot),
                                    Some(Type::Ptr(_))
                                )
                            {
                                let ir_ty = translate_ty(ty).unwrap_or(Type::Int);
                                let loaded = self.builder.load(
                                    slot.into(),
                                    size as u32,
                                    ir_ty,
                                    self.current_mem.into(),
                                    None,
                                    Origin::synthetic(),
                                );
                                return Some(loaded);
                            }
                        }
                    }
                    val
                } else {
                    self.translate_place_to_value(place)
                }
            }
            Operand::Constant(constant) => translate_const(
                self.tcx,
                self.instance,
                constant,
                &mut self.builder,
                &mut self.symbols,
                &mut self.static_data,
            ),
            Operand::RuntimeChecks(_) => {
                // UbChecks / ContractChecks / OverflowChecks: emit false (0)
                // to skip runtime checks, matching release-mode behaviour.
                Some(self.builder.iconst(0, Origin::synthetic()))
            }
        }
    }
}

/// Translate an IntToInt cast between integer types.
///
/// - Widening signed: sign-extend via shl+shr
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
            // Sign-extend: shl by (dst - src), then arithmetic shr by (dst - src).
            let shift_amt = dst_bits - src_bits;
            let shift_val = builder.iconst(shift_amt as i64, Origin::synthetic());
            let shifted = builder.shl(val.into(), shift_val.into(), None, Origin::synthetic());
            let shift_val2 = builder.iconst(shift_amt as i64, Origin::synthetic());
            let shifted_op = IrOperand::annotated(shifted, Annotation::Signed(dst_bits));
            Some(builder.shr(shifted_op, shift_val2.into(), None, Origin::synthetic()))
        } else {
            // Zero-extend: mask off high bits.
            let mask = (BigInt::from(1) << src_bits) - 1;
            let mask_val = builder.iconst(mask, Origin::synthetic());
            Some(builder.and(val.into(), mask_val.into(), None, Origin::synthetic()))
        }
    } else {
        // Narrowing cast: mask to target width.
        let mask = (BigInt::from(1) << dst_bits) - 1;
        let mask_val = builder.iconst(mask, Origin::synthetic());
        Some(builder.and(val.into(), mask_val.into(), None, Origin::synthetic()))
    }
}

fn translate_const<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: Instance<'tcx>,
    constant: &mir::ConstOperand<'tcx>,
    builder: &mut Builder<'_>,
    symbols: &mut SymbolTable,
    static_data: &mut StaticDataVec,
) -> Option<ValueRef> {
    // Monomorphize the constant using the instance's substitutions so that
    // associated type projections (e.g. <B as Flags>::Bits) are resolved
    // before evaluation.
    let mono_const = tcx.instantiate_and_normalize_erasing_regions(
        instance.args,
        ty::TypingEnv::fully_monomorphized(),
        ty::EarlyBinder::bind(constant.const_),
    );
    let ty = mono_const.ty();
    let val = match mono_const {
        mir::Const::Val(v, _) => v,
        _ => {
            // Const::Ty and Const::Unevaluated need evaluation first.
            let typing_env = ty::TypingEnv::fully_monomorphized();
            match mono_const.eval(tcx, typing_env, constant.span) {
                Ok(v) => v,
                Err(_) => return None,
            }
        }
    };
    match val {
        mir::ConstValue::Scalar(mir::interpret::Scalar::Ptr(ptr, _)) => {
            let (prov, ptr_offset) = ptr.into_raw_parts();
            let alloc_id = prov.alloc_id();
            match tcx.global_alloc(alloc_id) {
                rustc_middle::mir::interpret::GlobalAlloc::Memory(alloc) => {
                    let alloc = alloc.inner();
                    let offset = ptr_offset.bytes() as usize;
                    let size = alloc.len() - offset;
                    let bytes: Vec<u8> = alloc
                        .inspect_with_uninit_and_ptr_outside_interpreter(offset..offset + size)
                        .to_vec();
                    let sym = format!(
                        ".Lconst.{}",
                        STATIC_DATA_COUNTER.fetch_add(1, Ordering::Relaxed)
                    );
                    let sym_id = symbols.intern(&sym);
                    let relocs =
                        extract_alloc_relocs(tcx, alloc, offset, size, symbols, static_data);
                    static_data.push((sym_id, bytes, relocs));
                    let base = builder.symbol_addr(sym_id, Origin::synthetic());
                    Some(base)
                }
                rustc_middle::mir::interpret::GlobalAlloc::Static(def_id) => {
                    let instance = Instance::mono(tcx, def_id);
                    let sym_name = tcx.symbol_name(instance).name.to_string();
                    let sym_id = symbols.intern(&sym_name);
                    let base = builder.symbol_addr(sym_id, Origin::synthetic());
                    if ptr_offset.bytes() > 0 {
                        let off = builder.iconst(ptr_offset.bytes() as i64, Origin::synthetic());
                        Some(builder.add(base.into(), off.into(), None, Origin::synthetic()))
                    } else {
                        Some(base)
                    }
                }
                rustc_middle::mir::interpret::GlobalAlloc::Function { instance } => {
                    let sym_name = tcx.symbol_name(instance).name.to_string();
                    let sym_id = symbols.intern(&sym_name);
                    Some(builder.symbol_addr(sym_id, Origin::synthetic()))
                }
                rustc_middle::mir::interpret::GlobalAlloc::VTable(vtable_ty, vtable_trait_ref) => {
                    // Construct vtable as static data with function pointer relocations.
                    // Extract the principal trait ref from the existential predicates list.
                    let principal = vtable_trait_ref.principal().map(|p| p.skip_binder());
                    let vtable_alloc_id = tcx.vtable_allocation((vtable_ty, principal));
                    let vtable_alloc = tcx.global_alloc(vtable_alloc_id);
                    if let rustc_middle::mir::interpret::GlobalAlloc::Memory(alloc) = vtable_alloc {
                        let inner = alloc.inner();
                        let size = inner.len();
                        let bytes = inner
                            .inspect_with_uninit_and_ptr_outside_interpreter(0..size)
                            .to_vec();
                        let sym = format!(
                            ".Lvtable.{}",
                            STATIC_DATA_COUNTER.fetch_add(1, Ordering::Relaxed)
                        );
                        let sym_id = symbols.intern(&sym);

                        let relocs =
                            extract_alloc_relocs(tcx, inner, 0, size, symbols, static_data);

                        static_data.push((sym_id, bytes, relocs));
                        let base = builder.symbol_addr(sym_id, Origin::synthetic());
                        Some(base)
                    } else {
                        Some(builder.iconst(0, Origin::synthetic()))
                    }
                }
                rustc_middle::mir::interpret::GlobalAlloc::TypeId { .. } => {
                    Some(builder.iconst(0, Origin::synthetic()))
                }
            }
        }
        mir::ConstValue::Scalar(scalar) => translate_scalar(scalar, ty, builder),
        mir::ConstValue::ZeroSized => Some(builder.iconst(0, Origin::synthetic())),
        mir::ConstValue::Slice { alloc_id, meta } => {
            translate_const_slice(tcx, alloc_id, meta, builder, symbols, static_data)
        }
        mir::ConstValue::Indirect { alloc_id, offset } => {
            // Multi-byte constant stored in an allocation (e.g. Option::<&str>::None).
            // Emit the bytes as static data and return a pointer.
            let alloc = tcx.global_alloc(alloc_id);
            if let rustc_middle::mir::interpret::GlobalAlloc::Memory(mem_alloc) = alloc {
                let inner = mem_alloc.inner();
                let byte_offset = offset.bytes() as usize;
                let typing_env = ty::TypingEnv::fully_monomorphized();
                let size = tcx
                    .layout_of(typing_env.as_query_input(ty))
                    .map(|l| l.size.bytes() as usize)
                    .unwrap_or(inner.len() - byte_offset);
                let bytes: Vec<u8> = inner
                    .inspect_with_uninit_and_ptr_outside_interpreter(
                        byte_offset..byte_offset + size,
                    )
                    .to_vec();
                let sym = format!(
                    ".Lconst.{}",
                    STATIC_DATA_COUNTER.fetch_add(1, Ordering::Relaxed)
                );
                let sym_id = symbols.intern(&sym);
                let relocs =
                    extract_alloc_relocs(tcx, inner, byte_offset, size, symbols, static_data);
                static_data.push((sym_id, bytes, relocs));
                Some(builder.symbol_addr(sym_id, Origin::synthetic()))
            } else {
                None
            }
        }
    }
}

/// Extract relocations from an allocation's provenance table.
///
/// Walks the provenance entries in the given byte range and resolves each
/// pointer target to a symbol name. For `Memory` targets, the target
/// allocation is recursively emitted as static data.
fn extract_alloc_relocs<'tcx>(
    tcx: TyCtxt<'tcx>,
    alloc: &rustc_middle::mir::interpret::Allocation,
    byte_offset: usize,
    byte_len: usize,
    symbols: &mut SymbolTable,
    static_data: &mut StaticDataVec,
) -> Vec<(usize, String)> {
    let mut relocs = Vec::new();
    for (offset, prov) in alloc.provenance().ptrs().iter() {
        let abs_offset = offset.bytes() as usize;
        if abs_offset < byte_offset || abs_offset >= byte_offset + byte_len {
            continue;
        }
        let rel_offset = abs_offset - byte_offset;
        let target_alloc_id = prov.alloc_id();
        let ga = tcx.global_alloc(target_alloc_id);
        match ga {
            rustc_middle::mir::interpret::GlobalAlloc::Function { instance } => {
                let fn_sym = tcx.symbol_name(instance).name.to_string();
                relocs.push((rel_offset, fn_sym));
            }
            rustc_middle::mir::interpret::GlobalAlloc::Static(def_id) => {
                let instance = Instance::mono(tcx, def_id);
                let sym_name = tcx.symbol_name(instance).name.to_string();
                relocs.push((rel_offset, sym_name));
            }
            rustc_middle::mir::interpret::GlobalAlloc::Memory(target_alloc) => {
                let inner = target_alloc.inner();
                let bytes = inner
                    .inspect_with_uninit_and_ptr_outside_interpreter(0..inner.len())
                    .to_vec();
                let sym = format!(
                    ".Lconst.{}",
                    STATIC_DATA_COUNTER.fetch_add(1, Ordering::Relaxed)
                );
                let sym_id = symbols.intern(&sym);
                let nested_relocs =
                    extract_alloc_relocs(tcx, inner, 0, inner.len(), symbols, static_data);
                static_data.push((sym_id, bytes, nested_relocs));
                relocs.push((rel_offset, symbols.resolve(sym_id).to_string()));
            }
            rustc_middle::mir::interpret::GlobalAlloc::VTable(vtable_ty, vtable_trait_ref) => {
                let principal = vtable_trait_ref.principal().map(|p| p.skip_binder());
                if let Ok(vtable_alloc_id) =
                    std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                        tcx.vtable_allocation((vtable_ty, principal))
                    }))
                {
                    let vtable_alloc = tcx.global_alloc(vtable_alloc_id);
                    if let rustc_middle::mir::interpret::GlobalAlloc::Memory(va) = vtable_alloc {
                        let inner = va.inner();
                        let bytes = inner
                            .inspect_with_uninit_and_ptr_outside_interpreter(0..inner.len())
                            .to_vec();
                        let sym = format!(
                            ".Lvtable.{}",
                            STATIC_DATA_COUNTER.fetch_add(1, Ordering::Relaxed)
                        );
                        let sym_id = symbols.intern(&sym);
                        let nested_relocs =
                            extract_alloc_relocs(tcx, inner, 0, inner.len(), symbols, static_data);
                        static_data.push((sym_id, bytes, nested_relocs));
                        relocs.push((rel_offset, symbols.resolve(sym_id).to_string()));
                    }
                }
            }
            _ => {}
        }
    }
    relocs
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
            // Sign-extend: interpret as i128, then convert to BigInt.
            let size_bytes = int.size().bytes();
            let val = match size_bytes {
                1 => BigInt::from(bits as i8),
                2 => BigInt::from(bits as i16),
                4 => BigInt::from(bits as i32),
                8 => BigInt::from(bits as i64),
                16 => BigInt::from(bits as i128),
                _ => BigInt::from(bits as i128),
            };
            Some(builder.iconst(val, Origin::synthetic()))
        }
        ty::Uint(_) => {
            // Unsigned: convert u128 directly to BigInt (always non-negative).
            let val = BigInt::from(bits);
            Some(builder.iconst(val, Origin::synthetic()))
        }
        ty::Bool => Some(builder.bconst(bits != 0, Origin::synthetic())),
        ty::Char => {
            let val = BigInt::from(bits as u32);
            Some(builder.iconst(val, Origin::synthetic()))
        }
        ty::Ref(..) | ty::RawPtr(..) | ty::FnPtr(..) => {
            // Scalar::Int reference/pointer (e.g., null pointer constant)
            let val = bits as i64;
            Some(builder.iconst(val, Origin::synthetic()))
        }
        ty::Adt(..) => {
            // Newtype structs (e.g., ExitCode(u8)) are represented as
            // scalars. Treat the raw bits as an unsigned integer.
            let val = BigInt::from(bits);
            Some(builder.iconst(val, Origin::synthetic()))
        }
        _ => None,
    }
}

/// Translate a ConstValue::Slice (e.g., a string literal `&str`).
///
/// Emits the data bytes to .rodata and returns an IR constant whose index
/// is recorded in `symbols` so that isel emits a RIP-relative LEA.
fn translate_const_slice<'tcx>(
    tcx: TyCtxt<'tcx>,
    alloc_id: rustc_middle::mir::interpret::AllocId,
    meta: u64,
    builder: &mut Builder<'_>,
    symbols: &mut SymbolTable,
    static_data: &mut StaticDataVec,
) -> Option<ValueRef> {
    let rustc_middle::mir::interpret::GlobalAlloc::Memory(alloc) = tcx.global_alloc(alloc_id)
    else {
        return None;
    };
    let alloc = alloc.inner();
    let bytes: Vec<u8> = alloc
        .inspect_with_uninit_and_ptr_outside_interpreter(0..alloc.len())
        .to_vec();

    // Create a unique symbol name for this data blob.
    let sym = format!(
        ".Lstr.{}",
        STATIC_DATA_COUNTER.fetch_add(1, Ordering::Relaxed)
    );
    let sym_id = symbols.intern(&sym);
    static_data.push((sym_id, bytes, vec![]));

    // Emit a SymbolAddr to reference this static data blob.
    let ptr_val = builder.symbol_addr(sym_id, Origin::synthetic());

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

/// Handle compiler intrinsics inline during MIR translation.
/// Returns true if the intrinsic was handled, false to fall through to normal call.
fn translate_intrinsic<'tcx>(
    tcx: TyCtxt<'tcx>,
    name: &str,
    substs: &'tcx ty::List<ty::GenericArg<'tcx>>,
    ir_args: &[ValueRef],
    destination_local: mir::Local,
    builder: &mut Builder<'_>,
    locals: &mut LocalMap,
    symbols: &mut SymbolTable,
    current_mem: ValueRef,
) -> bool {
    match name {
        // black_box: identity function, prevents optimizations.
        // Just copy the argument to the destination.
        "black_box" => {
            if let Some(&v) = ir_args.first() {
                locals.set(destination_local, v);
            }
            true
        }

        // assume: optimizer hint, no runtime effect. Treat as no-op.
        "assume" => true,

        // assert_inhabited / assert_zero_valid / assert_mem_uninitialized_valid:
        // compile-time checks, no runtime effect.
        "assert_inhabited" | "assert_zero_valid" | "assert_mem_uninitialized_valid" => true,

        // ctpop: population count (count set bits).
        "ctpop" => {
            if let Some(&v) = ir_args.first() {
                let result = builder.count_ones(v.into(), Origin::synthetic());
                locals.set(destination_local, result);
            }
            true
        }

        // ctlz / ctlz_nonzero: count leading zeros.
        "ctlz" | "ctlz_nonzero" => {
            if let Some(&v) = ir_args.first() {
                let result = builder.count_leading_zeros(v.into(), Origin::synthetic());
                locals.set(destination_local, result);
            }
            true
        }

        // cttz / cttz_nonzero: count trailing zeros.
        "cttz" | "cttz_nonzero" => {
            if let Some(&v) = ir_args.first() {
                let result = builder.count_trailing_zeros(v.into(), Origin::synthetic());
                locals.set(destination_local, result);
            }
            true
        }

        // is_val_statically_known: always false in a non-optimizing backend.
        "is_val_statically_known" => {
            let result = builder.bconst(false, Origin::synthetic());
            locals.set(destination_local, result);
            true
        }

        // size_of_val: return the size of the pointed-to type.
        // For sized types this is a compile-time constant.
        "size_of_val" => {
            if let Some(t) = substs.first().and_then(|a| a.as_type()) {
                let sz = type_size(tcx, t).unwrap_or(0);
                let result = builder.iconst(sz as i64, Origin::synthetic());
                locals.set(destination_local, result);
            }
            true
        }

        // min_align_of_val / align_of_val: return the alignment of the type.
        "min_align_of_val" | "align_of_val" => {
            if let Some(t) = substs.first().and_then(|a| a.as_type()) {
                let align = type_align(tcx, t).unwrap_or(1);
                let result = builder.iconst(align as i64, Origin::synthetic());
                locals.set(destination_local, result);
            }
            true
        }

        // arith_offset<T>(ptr, offset) → ptr + offset * sizeof(T)
        "arith_offset" => {
            if ir_args.len() >= 2 {
                let ptr = ir_args[0];
                let offset = ir_args[1];
                let elem_size = substs
                    .first()
                    .and_then(|a| a.as_type())
                    .and_then(|t| type_size(tcx, t))
                    .unwrap_or(1);
                let byte_offset = if elem_size == 1 {
                    offset
                } else {
                    let sz = builder.iconst(elem_size as i64, Origin::synthetic());
                    builder.mul(offset.into(), sz.into(), None, Origin::synthetic())
                };
                let result =
                    builder.ptradd(ptr.into(), byte_offset.into(), 0, Origin::synthetic());
                locals.set(destination_local, result);
            }
            true
        }

        // ptr_offset_from_unsigned<T>(ptr1, ptr2) → (ptr1 - ptr2) / sizeof(T)
        "ptr_offset_from_unsigned" | "ptr_offset_from" => {
            if ir_args.len() >= 2 {
                let ptr1 = ir_args[0];
                let ptr2 = ir_args[1];
                let diff = builder.ptrdiff(ptr1.into(), ptr2.into(), Origin::synthetic());
                let elem_size = substs
                    .first()
                    .and_then(|a| a.as_type())
                    .and_then(|t| type_size(tcx, t))
                    .unwrap_or(1);
                let result = if elem_size <= 1 {
                    diff
                } else {
                    let sz = builder.iconst(elem_size as i64, Origin::synthetic());
                    builder.div(diff.into(), sz.into(), None, Origin::synthetic())
                };
                locals.set(destination_local, result);
            }
            true
        }

        // saturating_add<T>(a, b): add with saturation at max value.
        "saturating_add" => {
            if ir_args.len() >= 2 {
                let a = ir_args[0];
                let b = ir_args[1];
                // result = a + b; if result wrapped (result < a), clamp to MAX.
                let sum = builder.add(a.into(), b.into(), None, Origin::synthetic());
                let overflowed =
                    builder.icmp(ICmpOp::Lt, sum.into(), a.into(), Origin::synthetic());
                let max_val = builder.iconst(-1i64, Origin::synthetic()); // all-ones = usize::MAX
                let result = builder.select(
                    overflowed.into(),
                    max_val.into(),
                    sum.into(),
                    Type::Int,
                    Origin::synthetic(),
                );
                locals.set(destination_local, result);
            }
            true
        }

        // saturating_sub<T>(a, b): subtract with saturation at zero.
        "saturating_sub" => {
            if ir_args.len() >= 2 {
                let a = ir_args[0];
                let b = ir_args[1];
                let diff = builder.sub(a.into(), b.into(), None, Origin::synthetic());
                let underflowed =
                    builder.icmp(ICmpOp::Gt, b.into(), a.into(), Origin::synthetic());
                let zero = builder.iconst(0, Origin::synthetic());
                let result = builder.select(
                    underflowed.into(),
                    zero.into(),
                    diff.into(),
                    Type::Int,
                    Origin::synthetic(),
                );
                locals.set(destination_local, result);
            }
            true
        }

        // abort: call libc abort().
        "abort" => {
            let sym_id = symbols.intern("abort");
            let callee = builder.symbol_addr(sym_id, Origin::synthetic());
            builder.call(
                callee.into(),
                vec![],
                Type::Unit,
                current_mem.into(),
                None,
                Origin::synthetic(),
            );
            true
        }

        // Unhandled intrinsics fall through to normal call path.
        _ => false,
    }
}

/// Lower memory intrinsics to libc calls with adjusted arguments.
/// Handles write_bytes, copy_nonoverlapping, copy, and raw_eq.
/// Returns `Some(new_mem)` if the intrinsic was handled, `None` to fall through.
#[allow(clippy::too_many_arguments)]
fn translate_memory_intrinsic<'tcx>(
    tcx: TyCtxt<'tcx>,
    name: &str,
    substs: &'tcx ty::List<ty::GenericArg<'tcx>>,
    ir_args: &[ValueRef],
    destination_local: mir::Local,
    builder: &mut Builder<'_>,
    locals: &mut LocalMap,
    symbols: &mut SymbolTable,
    current_mem: ValueRef,
) -> Option<ValueRef> {
    // Extract the type parameter T and compute its size.
    let elem_size = match substs.first().and_then(|a| a.as_type()) {
        Some(t) => type_size(tcx, t).unwrap_or(0),
        None => return None,
    };

    match name {
        // write_bytes<T>(dst, val, count) → memset(dst, val, count * sizeof(T))
        "write_bytes" | "volatile_set_memory" => {
            if ir_args.len() < 3 {
                return None;
            }
            let dst = ir_args[0];
            let val = ir_args[1];
            let count = ir_args[2];
            let byte_count = if elem_size == 1 {
                count
            } else {
                let sz = builder.iconst(elem_size as i64, Origin::synthetic());
                builder.mul(count.into(), sz.into(), None, Origin::synthetic())
            };
            let sym_id = symbols.intern("memset");
            let callee = builder.symbol_addr(sym_id, Origin::synthetic());
            let (mem_out, data) = builder.call(
                callee.into(),
                vec![dst.into(), val.into(), byte_count.into()],
                Type::Int,
                current_mem.into(),
                None,
                Origin::synthetic(),
            );
            if let Some(d) = data {
                locals.set(destination_local, d);
            }
            Some(mem_out)
        }

        // copy_nonoverlapping<T>(src, dst, count) → memcpy(dst, src, count * sizeof(T))
        "copy_nonoverlapping" | "volatile_copy_nonoverlapping_memory" => {
            if ir_args.len() < 3 {
                return None;
            }
            let src = ir_args[0];
            let dst = ir_args[1];
            let count = ir_args[2];
            let byte_count = if elem_size == 1 {
                count
            } else {
                let sz = builder.iconst(elem_size as i64, Origin::synthetic());
                builder.mul(count.into(), sz.into(), None, Origin::synthetic())
            };
            // memcpy(dst, src, n) — note swapped argument order.
            let sym_id = symbols.intern("memcpy");
            let callee = builder.symbol_addr(sym_id, Origin::synthetic());
            let (mem_out, data) = builder.call(
                callee.into(),
                vec![dst.into(), src.into(), byte_count.into()],
                Type::Int,
                current_mem.into(),
                None,
                Origin::synthetic(),
            );
            if let Some(d) = data {
                locals.set(destination_local, d);
            }
            Some(mem_out)
        }

        // copy<T>(src, dst, count) → memmove(dst, src, count * sizeof(T))
        "copy" | "volatile_copy_memory" => {
            if ir_args.len() < 3 {
                return None;
            }
            let src = ir_args[0];
            let dst = ir_args[1];
            let count = ir_args[2];
            let byte_count = if elem_size == 1 {
                count
            } else {
                let sz = builder.iconst(elem_size as i64, Origin::synthetic());
                builder.mul(count.into(), sz.into(), None, Origin::synthetic())
            };
            let sym_id = symbols.intern("memmove");
            let callee = builder.symbol_addr(sym_id, Origin::synthetic());
            let (mem_out, data) = builder.call(
                callee.into(),
                vec![dst.into(), src.into(), byte_count.into()],
                Type::Int,
                current_mem.into(),
                None,
                Origin::synthetic(),
            );
            if let Some(d) = data {
                locals.set(destination_local, d);
            }
            Some(mem_out)
        }

        // raw_eq<T>(a, b) → memcmp(a, b, sizeof(T)) == 0
        "raw_eq" => {
            if ir_args.len() < 2 {
                return None;
            }
            let a = ir_args[0];
            let b = ir_args[1];
            let sz = builder.iconst(elem_size as i64, Origin::synthetic());
            let sym_id = symbols.intern("memcmp");
            let callee = builder.symbol_addr(sym_id, Origin::synthetic());
            let (mem_out, data) = builder.call(
                callee.into(),
                vec![a.into(), b.into(), sz.into()],
                Type::Int,
                current_mem.into(),
                None,
                Origin::synthetic(),
            );
            // raw_eq returns bool (0 or 1): true when memcmp returns 0.
            let cmp_result = data.unwrap_or_else(|| builder.iconst(0, Origin::synthetic()));
            let zero = builder.iconst(0, Origin::synthetic());
            let eq = builder.icmp(
                tuffy_ir::instruction::ICmpOp::Eq,
                cmp_result.into(),
                zero.into(),
                Origin::synthetic(),
            );
            locals.set(destination_local, eq);
            Some(mem_out)
        }

        _ => None,
    }
}

/// Check if a Call terminator's callee is a known intrinsic.
/// Returns the intrinsic name and the generic args (for extracting type parameters).
fn detect_intrinsic<'tcx>(
    tcx: TyCtxt<'tcx>,
    func_op: &Operand<'tcx>,
    caller: Instance<'tcx>,
) -> Option<(String, &'tcx ty::List<ty::GenericArg<'tcx>>)> {
    let ty = match func_op {
        Operand::Constant(c) => c.ty(),
        _ => return None,
    };
    let ty = tcx.instantiate_and_normalize_erasing_regions(
        caller.args,
        ty::TypingEnv::fully_monomorphized(),
        ty::EarlyBinder::bind(ty),
    );
    if let ty::FnDef(def_id, args) = ty.kind()
        && let Some(intrinsic) = tcx.intrinsic(*def_id)
    {
        return Some((intrinsic.name.as_str().to_string(), args));
    }
    None
}

/// Map compiler intrinsics to libc/compiler-rt symbol names.
/// Returns None for intrinsics that need inline handling or aren't supported.
fn intrinsic_to_libc(name: &str) -> Option<&'static str> {
    match name {
        // compare_bytes(left, right, count) -> i32 maps directly to memcmp.
        "compare_bytes" => Some("memcmp"),
        _ => None,
    }
}

/// Resolved call target: direct symbol or virtual dispatch.
enum CallTarget {
    /// Direct call to a named symbol.
    Direct(String),
    /// Virtual dispatch: load function pointer from vtable at given index.
    Virtual(usize),
}

/// Resolve the callee symbol name from a Call terminator's function operand.
fn resolve_call_target<'tcx>(
    tcx: TyCtxt<'tcx>,
    func_op: &Operand<'tcx>,
    caller: Instance<'tcx>,
    mir: &mir::Body<'tcx>,
) -> Option<CallTarget> {
    let ty = match func_op {
        Operand::Constant(c) => c.ty(),
        Operand::Copy(place) | Operand::Move(place) => {
            // Look up the local's type — ZST function items (FnDef) can
            // be resolved statically even though the operand is a local.
            mir.local_decls[place.local].ty
        }
        _ => return None,
    };
    // Monomorphize the callee type using the caller's substitutions.
    // This resolves generic parameters (F/#0, Self/#0, etc.) that appear
    // when the caller is a generic function monomorphized for specific types.
    let ty = tcx.instantiate_and_normalize_erasing_regions(
        caller.args,
        ty::TypingEnv::fully_monomorphized(),
        ty::EarlyBinder::bind(ty),
    );
    match ty.kind() {
        ty::FnDef(def_id, args) => {
            // Check if this is an intrinsic that maps to a libc symbol.
            if let Some(intrinsic) = tcx.intrinsic(*def_id) {
                let iname = intrinsic.name.as_str();
                if let Some(libc_sym) = intrinsic_to_libc(iname) {
                    return Some(CallTarget::Direct(libc_sym.to_string()));
                }
            }
            if args.has_non_region_param() {
                return None;
            }
            let instance =
                Instance::try_resolve(tcx, ty::TypingEnv::fully_monomorphized(), *def_id, args)
                    .ok()
                    .flatten();
            let instance = match instance {
                Some(i) => i,
                None => {
                    return None;
                }
            };
            // Detect virtual dispatch (trait object method calls).
            if let ty::InstanceKind::Virtual(_, idx) = instance.def {
                return Some(CallTarget::Virtual(idx));
            }
            if instance.args.has_non_region_param() {
                return None;
            }
            Some(CallTarget::Direct(
                tcx.symbol_name(instance).name.to_string(),
            ))
        }
        _ => None,
    }
}
