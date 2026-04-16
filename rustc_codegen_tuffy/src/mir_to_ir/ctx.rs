use std::collections::{HashMap, HashSet};

use rustc_middle::mir::{self, BasicBlock};
use rustc_middle::ty::{self, Instance, TyCtxt};
use tuffy_ir::builder::Builder;
use tuffy_ir::debug::{
    DebugBinding, DebugSource, DebugValue, DebugVariable, DebugVariableKind, FunctionDebugInfo,
    SourceLocation,
};
use tuffy_ir::instruction::{Operand, Origin};
use tuffy_ir::module::{SymbolId, SymbolTable};
use tuffy_ir::types::{Annotation, IntAnnotation, IntSignedness, Type};
use tuffy_ir::value::{BlockRef, ValueRef};

use super::StaticDataVec;
use super::constant::extract_alloc_relocs;
use super::types::*;

/// Stores the current SSA value for each MIR local.
pub(super) struct LocalMap {
    /// Slots indexed by `mir::Local::as_usize()`.
    pub(super) values: Vec<Option<ValueRef>>,
}

impl LocalMap {
    /// Creates an empty local map sized for the current MIR body.
    pub(super) fn new(count: usize) -> Self {
        Self {
            values: vec![None; count],
        }
    }

    /// Records the current SSA value for `local`.
    pub(super) fn set(&mut self, local: mir::Local, val: ValueRef) {
        self.values[local.as_usize()] = Some(val);
    }

    /// Returns the current SSA value for `local`, if one has been assigned.
    pub(super) fn get(&self, local: mir::Local) -> Option<ValueRef> {
        self.values[local.as_usize()]
    }

    /// Clears any tracked value for `local`.
    pub(super) fn clear(&mut self, local: mir::Local) {
        self.values[local.as_usize()] = None;
    }
}

/// Tracks the "high" component of fat pointer locals (e.g., length for &str).
pub(super) struct FatLocalMap {
    /// Maps MIR local index → high ValueRef (e.g., slice length).
    values: HashMap<usize, ValueRef>,
}

impl FatLocalMap {
    /// Creates an empty fat-pointer metadata map.
    pub(super) fn new() -> Self {
        Self {
            values: HashMap::new(),
        }
    }

    /// Records the metadata component for `local`.
    pub(super) fn set(&mut self, local: mir::Local, val: ValueRef) {
        self.values.insert(local.as_usize(), val);
    }

    /// Returns the metadata component cached for `local`.
    pub(super) fn get(&self, local: mir::Local) -> Option<ValueRef> {
        self.values.get(&local.as_usize()).copied()
    }

    /// Clears any cached metadata for `local`.
    pub(super) fn clear(&mut self, local: mir::Local) {
        self.values.remove(&local.as_usize());
    }
}

/// Cached components of a direct `split_at_mut{,_unchecked}` result.
#[derive(Clone, Copy)]
pub(super) struct SplitPairLocal {
    /// Left slice data pointer.
    pub(super) left_ptr: ValueRef,
    /// Left slice length.
    pub(super) left_len: ValueRef,
    /// Right slice data pointer.
    pub(super) right_ptr: ValueRef,
    /// Right slice length.
    pub(super) right_len: ValueRef,
}

impl SplitPairLocal {
    /// Returns the `(data_ptr, len)` pair for one tuple field.
    pub(super) fn field(self, idx: usize) -> Option<(ValueRef, ValueRef)> {
        match idx {
            0 => Some((self.left_ptr, self.left_len)),
            1 => Some((self.right_ptr, self.right_len)),
            _ => None,
        }
    }
}

/// Tracks tuple locals caching two fat-pointer fields in SSA.
pub(super) struct SplitPairLocalMap {
    /// Slots indexed by `mir::Local::as_usize()`.
    values: Vec<Option<SplitPairLocal>>,
}

impl SplitPairLocalMap {
    /// Creates an empty split-pair map sized for the current MIR body.
    pub(super) fn new(count: usize) -> Self {
        Self {
            values: vec![None; count],
        }
    }

    /// Records the cached split result for `local`.
    pub(super) fn set(&mut self, local: mir::Local, val: SplitPairLocal) {
        self.values[local.as_usize()] = Some(val);
    }

    /// Returns the cached split result for `local`, if present.
    pub(super) fn get(&self, local: mir::Local) -> Option<SplitPairLocal> {
        self.values[local.as_usize()]
    }

    /// Clears any cached split result for `local`.
    pub(super) fn clear(&mut self, local: mir::Local) {
        self.values[local.as_usize()] = None;
    }
}

/// Maps `*WithOverflow` destination locals to their overflow-flag `ValueRef`
/// (the secondary result of the multi-result IR instruction).
/// Field(1) access on a `(T, bool)` checked-op local consults this map.
pub(super) struct OverflowLocalMap {
    /// Maps MIR local indices to overflow flag values.
    values: HashMap<usize, ValueRef>,
}

impl OverflowLocalMap {
    /// Creates an empty overflow-flag map.
    pub(super) fn new() -> Self {
        Self {
            values: HashMap::new(),
        }
    }

    /// Records the overflow flag value associated with `local`.
    pub(super) fn set(&mut self, local: mir::Local, overflow: ValueRef) {
        self.values.insert(local.as_usize(), overflow);
    }

    /// Returns the cached overflow flag value for `local`.
    pub(super) fn get(&self, local: mir::Local) -> Option<ValueRef> {
        self.values.get(&local.as_usize()).copied()
    }
}

/// Cached `Option<T>` state for simple scalar payload locals.
#[derive(Clone, Copy)]
pub(super) struct OptionScalarLocal {
    /// Cached discriminant for the enum value.
    pub(super) discriminant: ValueRef,
    /// Variant whose field-0 projection maps to `payload`.
    pub(super) payload_variant: rustc_abi::VariantIdx,
    /// Payload value when the option is `Some`.
    pub(super) payload: ValueRef,
}

/// Tracks simple scalar `Option<T>` locals kept in SSA.
pub(super) struct OptionScalarLocalMap {
    /// Slots indexed by `mir::Local::as_usize()`.
    values: Vec<Option<OptionScalarLocal>>,
}

impl OptionScalarLocalMap {
    /// Creates an empty option-scalar map sized for the current MIR body.
    pub(super) fn new(count: usize) -> Self {
        Self {
            values: vec![None; count],
        }
    }

    /// Records the current `Option<T>` state for `local`.
    pub(super) fn set(&mut self, local: mir::Local, value: OptionScalarLocal) {
        self.values[local.as_usize()] = Some(value);
    }

    /// Returns the current `Option<T>` state for `local`, if present.
    pub(super) fn get(&self, local: mir::Local) -> Option<OptionScalarLocal> {
        self.values[local.as_usize()]
    }

    /// Clears any cached `Option<T>` state for `local`.
    pub(super) fn clear(&mut self, local: mir::Local) {
        self.values[local.as_usize()] = None;
    }
}

/// Tracks which MIR locals hold stack slot addresses (aggregate/spilled values)
/// rather than scalar values in registers.
pub(super) struct StackLocalSet {
    /// Marks whether each MIR local currently lives in a stack slot.
    is_stack: Vec<bool>,
}

impl StackLocalSet {
    /// Creates an empty stack-local set sized for the current MIR body.
    pub(super) fn new(count: usize) -> Self {
        Self {
            is_stack: vec![false; count],
        }
    }

    /// Marks `local` as being represented by a stack slot address.
    pub(super) fn mark(&mut self, local: mir::Local) {
        self.is_stack[local.as_usize()] = true;
    }

    /// Returns whether `local` is currently represented by a stack slot.
    pub(super) fn is_stack(&self, local: mir::Local) -> bool {
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
pub(super) fn extract_param_names(
    mir: &mir::Body<'_>,
    symbols: &mut SymbolTable,
) -> Vec<Option<SymbolId>> {
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

/// Map from MIR BasicBlock to IR BlockRef.
pub(super) struct BlockMap {
    /// Slots indexed by `BasicBlock::as_usize()`.
    blocks: Vec<Option<BlockRef>>,
}

impl BlockMap {
    /// Creates an empty block map sized for the current MIR body.
    pub(super) fn new(count: usize) -> Self {
        Self {
            blocks: vec![None; count],
        }
    }

    /// Records the IR block that corresponds to `bb`.
    pub(super) fn set(&mut self, bb: BasicBlock, block: BlockRef) {
        self.blocks[bb.as_usize()] = Some(block);
    }

    /// Returns the IR block previously assigned to `bb`.
    pub(super) fn get(&self, bb: BasicBlock) -> BlockRef {
        self.blocks[bb.as_usize()].expect("block not mapped")
    }
}

/// Bundles the mutable translation state threaded through MIR→IR lowering.
///
/// Converting free functions into methods on this struct eliminates the
/// `clippy::too_many_arguments` warnings and makes it easier to add new
/// shared state in the future.
pub(super) struct TranslationCtx<'a, 'tcx> {
    /// rustc type context for the function being translated.
    pub(super) tcx: TyCtxt<'tcx>,
    /// MIR body currently being lowered.
    pub(super) mir: &'a mir::Body<'tcx>,
    /// Tuffy IR builder for the current function.
    pub(super) builder: Builder<'a>,
    /// Current SSA values for MIR locals.
    pub(super) locals: LocalMap,
    /// Cached metadata words for fat-pointer locals.
    pub(super) fat_locals: FatLocalMap,
    /// Cached tuple locals holding two fat-pointer fields.
    pub(super) split_pair_locals: SplitPairLocalMap,
    /// Tracks which locals currently live in stack slots.
    pub(super) stack_locals: StackLocalSet,
    /// Maps `*WithOverflow` destination locals to the overflow-flag ValueRef
    /// (secondary result of the IR instruction). Used by Field(1) access.
    pub(super) overflow_locals: OverflowLocalMap,
    /// Cached simple scalar `Option<T>` locals.
    pub(super) option_scalar_locals: OptionScalarLocalMap,
    /// Per-function symbol table used during lowering.
    pub(super) symbols: SymbolTable,
    /// Static data emitted while lowering this function.
    pub(super) static_data: StaticDataVec,
    /// MIR basic-block to IR basic-block mapping.
    pub(super) block_map: BlockMap,
    /// MemSSA block arguments: one `Type::Mem` arg per MIR basic block.
    pub(super) block_mem_args: Vec<Option<ValueRef>>,
    /// Maximum legal integer width, in bits, for the target backend.
    pub(super) target_max_int_width: u32,
    /// Maximum number of direct integer ABI parts supported by the target.
    pub(super) target_max_abi_int_parts: u32,
    /// Resolved rustc instance currently being translated.
    pub(super) instance: Instance<'tcx>,
    /// Current memory token for MemSSA threading.
    pub(super) current_mem: ValueRef,
    /// Metadata extracted from Cast-to-fat-pointer assignments
    /// (e.g. `NonNull<[T]> as *const [T]` in `into_vec`).
    /// Only consulted by PtrMetadata — does NOT propagate through
    /// Use/Copy chains like fat_locals does.
    pub(super) cast_fat_meta: FatLocalMap,
    /// Instances referenced by direct calls, for on-demand compilation.
    pub(super) referenced_instances: Vec<Instance<'tcx>>,
    /// Counter for generating unique static data symbol names within a CGU.
    pub(super) data_counter: &'a mut u64,
    /// Cache mapping rustc vtable AllocId → emitted symbol name, shared across
    /// all functions in the CGU to ensure vtable deduplication.
    pub(super) vtable_cache: &'a mut super::VtableCache,
    /// Cache mapping rustc memory AllocId → emitted symbol name, shared across
    /// all functions in the CGU so that identical allocations get the same address.
    pub(super) alloc_cache: &'a mut super::AllocCache,
    /// Content-based dedup cache, shared across all functions in the CGU.
    /// Catches identical allocations with different AllocIds (e.g., const
    /// promotions duplicated by inlining).
    pub(super) content_cache: &'a mut super::ContentCache,
    /// SRET pointer for functions returning values larger than the target's
    /// direct integer-register ABI capacity.
    /// When set, param indices are shifted by 1 (param 0 = hidden SRET ptr).
    pub(super) sret_ptr: Option<ValueRef>,
    /// Symbol names that should be emitted as weak undefined references
    /// (e.g. from `#[linkage = "extern_weak"]` statics).
    pub(super) weak_undefined_symbols: HashSet<String>,
    /// For `#[track_caller]` functions, the implicit `&Location` parameter.
    /// Used by the `caller_location` intrinsic to return the caller's location.
    pub(super) caller_location_param: Option<ValueRef>,
    /// Stack slot for the exception pointer during stack unwinding.
    /// Allocated lazily when the first `UnwindAction::Cleanup` is encountered.
    pub(super) exc_ptr_slot: Option<ValueRef>,
    /// Landing-pad wrapper blocks to emit after the main translation loop.
    /// Each entry is `(wrapper_ir_block, cleanup_mir_bb)`.
    pub(super) landing_pad_wrappers: Vec<(tuffy_ir::value::BlockRef, BasicBlock)>,
    /// Stable source ids used by IR origins.
    pub(super) debug_sources: HashMap<(u32, u32, u32), u32>,
    /// Per-function debug side metadata.
    pub(super) function_debug: FunctionDebugInfo,
}

impl<'a, 'tcx> TranslationCtx<'a, 'tcx> {
    /// Converts a rustc span into a Tuffy debug source location.
    fn source_location_from_span(&self, span: rustc_span::Span) -> SourceLocation {
        let loc = self.tcx.sess.source_map().lookup_char_pos(span.lo());
        SourceLocation {
            file: loc.file.name.prefer_remapped_unconditionally().to_string(),
            line: loc.line as u32,
            column: (loc.col.0 + 1) as u32,
        }
    }

    /// Interns a source location for one MIR source-info record and returns its id.
    pub(super) fn record_source(&mut self, source_info: mir::SourceInfo) -> u32 {
        let key = (
            source_info.span.lo().0,
            source_info.span.hi().0,
            source_info.scope.as_u32(),
        );
        if let Some(&existing) = self.debug_sources.get(&key) {
            return existing;
        }
        let source = DebugSource {
            location: self.source_location_from_span(source_info.span),
        };
        let id = self.function_debug.sources.len() as u32;
        self.function_debug.sources.push(source);
        self.debug_sources.insert(key, id);
        id
    }

    /// Attaches `source_info` to instructions emitted after `start_index`.
    pub(super) fn stamp_new_insts_with_source(
        &mut self,
        start_index: u32,
        source_info: mir::SourceInfo,
    ) {
        let end_index = self.builder.next_inst_index();
        if start_index >= end_index {
            return;
        }
        let source = self.record_source(source_info);
        self.builder
            .set_inst_origins(start_index, end_index, Origin::from_source(source));
    }

    /// Collects debuginfo variable and binding records from the MIR body.
    pub(super) fn collect_debug_variables(&mut self) {
        use rustc_middle::mir::VarDebugInfoContents;

        for info in &self.mir.var_debug_info {
            if info.composite.is_some() {
                continue;
            }

            let variable = self.function_debug.variables.len() as u32;
            self.function_debug.variables.push(DebugVariable {
                name: info.name.as_str().to_string(),
                kind: if info.argument_index.is_some() {
                    DebugVariableKind::Parameter
                } else {
                    DebugVariableKind::Local
                },
                declaration: Some(self.source_location_from_span(info.source_info.span)),
            });

            let value = match &info.value {
                VarDebugInfoContents::Place(place) if place.projection.is_empty() => {
                    self.locals.get(place.local).map(DebugValue::IrValue)
                }
                _ => None,
            };
            let Some(value) = value else {
                continue;
            };
            let source = self.record_source(info.source_info);
            self.function_debug.bindings.push(DebugBinding {
                source,
                variable,
                value,
            });
        }
    }

    /// Returns the target's legal integer-part size in bytes.
    pub(super) fn target_part_bytes(&self) -> u64 {
        (self.target_max_int_width / 8) as u64
    }

    /// Returns the total direct integer ABI capacity in bytes.
    pub(super) fn target_direct_abi_bytes(&self) -> u64 {
        self.target_part_bytes() * self.target_max_abi_int_parts as u64
    }

    /// Returns the total direct integer ABI capacity in bits.
    pub(super) fn target_direct_abi_bits(&self) -> u32 {
        self.target_max_int_width * self.target_max_abi_int_parts
    }

    /// Allocates the next unique static-data id within the current codegen unit.
    pub(super) fn next_data_id(&mut self) -> u64 {
        let id = *self.data_counter;
        *self.data_counter += 1;
        id
    }

    /// Emit a vtable (or reuse a previously emitted one) and return the symbol_addr ValueRef.
    /// Uses `vtable_cache` keyed by the rustc AllocId to deduplicate.
    pub(super) fn emit_vtable(
        &mut self,
        vtable_alloc_id: rustc_middle::mir::interpret::AllocId,
    ) -> Option<ValueRef> {
        if let Some(existing_name) = self.vtable_cache.get(&vtable_alloc_id) {
            let sym_id = self.symbols.intern(existing_name);
            return Some(self.builder.symbol_addr(sym_id, Origin::synthetic()).raw());
        }

        let vtable_alloc = self.tcx.global_alloc(vtable_alloc_id);
        if let rustc_middle::mir::interpret::GlobalAlloc::Memory(alloc) = vtable_alloc {
            let inner_alloc = alloc.inner();
            let size = inner_alloc.len();
            let bytes = inner_alloc
                .inspect_with_uninit_and_ptr_outside_interpreter(0..size)
                .to_vec();
            let sym = format!(".Lvtable.{}", self.next_data_id());
            self.vtable_cache.insert(vtable_alloc_id, sym.clone());
            let sym_id = self.symbols.intern(&sym);
            let relocs = extract_alloc_relocs(
                self.tcx,
                inner_alloc,
                0,
                size,
                &mut self.symbols,
                &mut self.static_data,
                &mut self.referenced_instances,
                self.data_counter,
                self.vtable_cache,
                self.alloc_cache,
                self.content_cache,
            );
            self.static_data
                .push((sym_id, bytes, relocs, inner_alloc.align.bytes()));
            Some(self.builder.symbol_addr(sym_id, Origin::synthetic()).raw())
        } else {
            None
        }
    }

    /// Get the target pointer width in bits.
    fn ptr_width(&self) -> u32 {
        self.tcx.data_layout.pointer_size().bits() as u32
    }

    /// Monomorphize a MIR type using the current instance's substitutions.
    pub(super) fn monomorphize(&self, ty: ty::Ty<'tcx>) -> ty::Ty<'tcx> {
        self.tcx.instantiate_and_normalize_erasing_regions(
            self.instance.args,
            ty::TypingEnv::fully_monomorphized(),
            ty::EarlyBinder::bind(ty),
        )
    }

    /// Get the monomorphized type of an operand.
    pub(super) fn operand_ty_mono(&self, operand: &mir::Operand<'tcx>) -> Option<ty::Ty<'tcx>> {
        let ty = operand_ty(operand, self.mir)?;
        Some(self.monomorphize(ty))
    }

    /// Spill a scalar local to a new stack slot of the given byte size.
    ///
    /// Creates a slot of `max(size, 1)` bytes, optionally stores the current
    /// value of `local` into it (if already assigned), then updates the local
    /// to point at the slot and marks it as stack-allocated.
    pub(super) fn promote_local_to_stack(&mut self, local: mir::Local, size: u64, align: u32) {
        let slot_size = (size as u32).max(1);
        let slot = self
            .builder
            .stack_slot(slot_size, align, Origin::synthetic());
        if let Some(old_val) = self.locals.get(local) {
            let is_fat = self.fat_locals.get(local).is_some();
            if is_fat && slot_size == 16 {
                // Fat pointer: store data pointer (8 bytes) then metadata (8 bytes).
                self.current_mem = self
                    .builder
                    .store(
                        old_val.into(),
                        slot.into(),
                        8,
                        self.current_mem.into(),
                        Origin::synthetic(),
                    )
                    .raw();
                if let Some(meta) = self.fat_locals.get(local) {
                    let off8 =
                        self.builder
                            .iconst(8, 64, IntSignedness::DontCare, Origin::synthetic());
                    let hi_addr =
                        self.builder
                            .ptradd(slot.into(), off8.into(), 0, Origin::synthetic());
                    self.current_mem = self
                        .builder
                        .store(
                            meta.into(),
                            hi_addr.into(),
                            8,
                            self.current_mem.into(),
                            Origin::synthetic(),
                        )
                        .raw();
                }
            } else {
                self.current_mem = self
                    .builder
                    .store(
                        old_val.into(),
                        slot.into(),
                        slot_size,
                        self.current_mem.into(),
                        Origin::synthetic(),
                    )
                    .raw();
            }
        }
        self.locals.set(local, slot);
        self.stack_locals.mark(local);
    }

    /// If `val` is a Ptr or Bool, coerce it to Int.
    pub(super) fn coerce_to_int(&mut self, val: ValueRef) -> ValueRef {
        let ptr_width = self.ptr_width();
        let vtype = self.builder.value_type(val).cloned();
        match vtype.as_ref() {
            Some(Type::Ptr(_)) => self
                .builder
                .ptrtoaddr(val.into(), ptr_width, Origin::synthetic())
                .raw(),
            Some(Type::Bool) => {
                let one =
                    self.builder
                        .iconst(1, ptr_width, IntSignedness::Unsigned, Origin::synthetic());
                let zero =
                    self.builder
                        .iconst(0, ptr_width, IntSignedness::Unsigned, Origin::synthetic());
                self.builder.select(
                    val.into(),
                    one.into(),
                    zero.into(),
                    Type::Int,
                    Some(Annotation::Int(IntAnnotation {
                        bit_width: ptr_width,
                        signedness: IntSignedness::Unsigned,
                    })),
                    Origin::synthetic(),
                )
            }
            _ => val,
        }
    }

    /// If `val` is an Int, insert inttoptr to coerce it to Ptr.
    pub(super) fn coerce_to_ptr(&mut self, val: ValueRef) -> ValueRef {
        match self.builder.value_type(val) {
            Some(Type::Int) => self
                .builder
                .inttoptr(val.into(), 0, Origin::synthetic())
                .raw(),
            _ => val,
        }
    }

    /// Create a static `&Location` for a `#[track_caller]` call site.
    ///
    /// Builds two data blobs in `.rodata`:
    ///   1. The file-name string bytes.
    ///   2. A 24-byte `Location` struct: `{ file_ptr, file_len, line, col }`.
    ///
    /// Returns a `symbol_addr` pointing to the Location blob.
    pub(super) fn make_caller_location(&mut self, source_info: mir::SourceInfo) -> ValueRef {
        let tcx = self.tcx;
        let span = source_info.span;
        let loc = tcx.sess.source_map().lookup_char_pos(span.lo());
        let file_name = loc.file.name.prefer_remapped_unconditionally().to_string();
        let line = loc.line as u32;
        let col = (loc.col.0 + 1) as u32; // 1-based column

        // 1. Emit the file-name string as a data blob.
        let file_bytes = file_name.as_bytes().to_vec();
        let file_len = file_bytes.len() as u64;
        let file_sym_name = format!(".Lloc_file.{}", self.next_data_id());
        let file_sym_id = self.symbols.intern(&file_sym_name);
        self.static_data.push((file_sym_id, file_bytes, vec![], 1));

        // 2. Build the 24-byte Location struct.
        //    Layout: file_ptr(8) + file_len(8) + line(4) + col(4)
        let mut loc_bytes = vec![0u8; 24];
        // file_ptr at offset 0 — filled by relocation
        loc_bytes[8..16].copy_from_slice(&file_len.to_le_bytes());
        loc_bytes[16..20].copy_from_slice(&line.to_le_bytes());
        loc_bytes[20..24].copy_from_slice(&col.to_le_bytes());

        let loc_sym_name = format!(".Lloc.{}", self.next_data_id());
        let loc_sym_id = self.symbols.intern(&loc_sym_name);
        let file_sym_str = self.symbols.resolve(file_sym_id).to_string();
        self.static_data
            .push((loc_sym_id, loc_bytes, vec![(0, file_sym_str)], 8));

        self.builder
            .symbol_addr(loc_sym_id, Origin::synthetic())
            .raw()
    }

    /// Receives ABI parameters and maps them into MIR locals.
    pub(super) fn translate_params(&mut self) {
        // Two-phase param receiving: emit ALL param instructions first,
        // THEN do stores/mem_copy.  mem_copy lowers to a memcpy call that
        // clobbers caller-saved registers (RSI, RDI, …).  If a later
        // param instruction appears after a mem_copy, the ABI register
        // it reads may already be destroyed.

        // When SRET is active, param 0 is the hidden return pointer.
        // Real MIR params start at index 1.
        let mut param_idx: u32 = if self.sret_ptr.is_some() { 1 } else { 0 };

        // Deferred store/copy actions executed after all params are received.
        enum Deferred {
            /// mem_copy from pointer param to local stack slot.
            LargeCopy {
                ptr: ValueRef,
                slot: ValueRef,
                sz: u64,
            },
            /// Two-register aggregate → store lo and hi halves.
            TwoReg {
                lo: ValueRef,
                hi: ValueRef,
                slot: ValueRef,
                hi_bytes: u64,
            },
            /// One-register aggregate → store value.
            OneReg {
                val: ValueRef,
                slot: ValueRef,
                sz: u64,
            },
        }
        let mut deferred: Vec<Deferred> = Vec::new();
        let part_bytes = self.target_part_bytes();
        let direct_abi_bytes = self.target_direct_abi_bytes();

        // --- Phase 1: receive all param values ---
        for i in 0..self.mir.arg_count {
            let local = mir::Local::from_usize(i + 1);
            let ty = self.monomorphize(self.mir.local_decls[local].ty);
            let ir_ty = translate_ty(self.tcx, ty);

            let sz = type_size(self.tcx, ty).unwrap_or(0);

            // Skip zero-sized (Unit) and untranslatable params — they don't
            // occupy a runtime slot. Assign a dummy value so downstream MIR
            // references to this local remain valid.
            if matches!(ir_ty, Some(Type::Unit)) || sz == 0 {
                let dummy =
                    self.builder
                        .iconst(0, 64, IntSignedness::DontCare, Origin::synthetic());
                self.locals.set(local, dummy.raw());
                continue;
            }

            // Non-zero-sized aggregate with no direct IR type (arrays,
            // tuples, ADTs).  Receive register(s) and reconstruct on stack.
            if ir_ty.is_none() {
                let prk = repr_kind(self.tcx, ty);
                if matches!(prk, ReprKind::ScalarPair | ReprKind::Scalar)
                    && sz > part_bytes
                    && sz <= direct_abi_bytes
                {
                    // Aggregate fits in the target's direct integer-register ABI path.
                    let lo = self.builder.param(
                        param_idx,
                        Type::Int,
                        int_annotation_for_bytes(part_bytes as u32),
                        Origin::synthetic(),
                    );
                    param_idx += 1;
                    let hi = self.builder.param(
                        param_idx,
                        Type::Int,
                        int_annotation_for_bytes((sz - part_bytes) as u32),
                        Origin::synthetic(),
                    );
                    param_idx += 1;
                    let ty_align = type_align(self.tcx, ty).unwrap_or(8) as u32;
                    let local_slot =
                        self.builder
                            .stack_slot(sz as u32, ty_align, Origin::synthetic());
                    deferred.push(Deferred::TwoReg {
                        lo,
                        hi,
                        slot: local_slot,
                        hi_bytes: sz - part_bytes,
                    });
                    self.locals.set(local, local_slot);
                    self.stack_locals.mark(local);
                } else if sz > part_bytes {
                    // Larger memory aggregates are passed indirectly.
                    let ptr =
                        self.builder
                            .param(param_idx, Type::Ptr(0), None, Origin::synthetic());
                    param_idx += 1;
                    let local_slot = self.builder.stack_slot(
                        sz as u32,
                        type_align(self.tcx, ty).unwrap_or(8) as u32,
                        Origin::synthetic(),
                    );
                    deferred.push(Deferred::LargeCopy {
                        ptr,
                        slot: local_slot,
                        sz,
                    });
                    self.locals.set(local, local_slot);
                    self.stack_locals.mark(local);
                } else {
                    // 1–8 byte aggregate: passed in one register
                    let val = self.builder.param(
                        param_idx,
                        Type::Int,
                        int_annotation_for_bytes(sz as u32),
                        Origin::synthetic(),
                    );
                    param_idx += 1;
                    let local_slot = self.builder.stack_slot(
                        sz as u32,
                        type_align(self.tcx, ty).unwrap_or(8) as u32,
                        Origin::synthetic(),
                    );
                    deferred.push(Deferred::OneReg {
                        val,
                        slot: local_slot,
                        sz,
                    });
                    self.locals.set(local, local_slot);
                    self.stack_locals.mark(local);
                }
                continue;
            }

            if is_fat_ptr(self.tcx, ty) {
                // Fat pointer params (&str, &[T], &dyn Trait) occupy two
                // register-sized slots: data pointer + metadata.
                let data_ptr = self.builder.param(
                    param_idx,
                    ir_ty.expect("checked above"),
                    None,
                    Origin::synthetic(),
                );
                param_idx += 1;

                // Determine metadata type: Int for slices/str, Ptr for trait objects
                let (meta_ty, meta_ann) = match ty.kind() {
                    ty::TyKind::Ref(_, pointee, _) | ty::TyKind::RawPtr(pointee, _) => {
                        let tail = self.tcx.struct_tail_for_codegen(
                            *pointee,
                            ty::TypingEnv::fully_monomorphized(),
                        );
                        match tail.kind() {
                            ty::TyKind::Dynamic(..) => (Type::Ptr(0), None),
                            _ => (Type::Int, int_annotation_for_bytes(part_bytes as u32)),
                        }
                    }
                    _ => (Type::Int, int_annotation_for_bytes(part_bytes as u32)),
                };

                let metadata =
                    self.builder
                        .param(param_idx, meta_ty, meta_ann, Origin::synthetic());
                param_idx += 1;
                self.locals.set(local, data_ptr);
                self.fat_locals.set(local, metadata);
            } else {
                let ir_ty_val = ir_ty.expect("checked above");
                let sz = type_size(self.tcx, ty).unwrap_or(0);
                let is_large = sz > direct_abi_bytes;

                if is_large {
                    // Large parameter: receive pointer from caller
                    let ptr =
                        self.builder
                            .param(param_idx, Type::Ptr(0), None, Origin::synthetic());

                    // Allocate local stack space
                    let local_slot = self.builder.stack_slot(
                        sz as u32,
                        type_align(self.tcx, ty).unwrap_or(8) as u32,
                        Origin::synthetic(),
                    );
                    deferred.push(Deferred::LargeCopy {
                        ptr,
                        slot: local_slot,
                        sz,
                    });

                    // Use the local slot, not the parameter pointer
                    self.locals.set(local, local_slot);
                    self.stack_locals.mark(local);
                } else {
                    // Small parameter: passed directly
                    let val = self.builder.param(
                        param_idx,
                        ir_ty_val,
                        translate_annotation(ty),
                        Origin::synthetic(),
                    );
                    self.locals.set(local, val);
                }

                param_idx += 1;
            }
        }

        // --- Phase 1b: receive implicit #[track_caller] &Location param ---
        if self.instance.def.requires_caller_location(self.tcx) {
            let loc_param = self
                .builder
                .param(param_idx, Type::Ptr(0), None, Origin::synthetic());
            self.caller_location_param = Some(loc_param);
        }

        // --- Phase 2: emit stores and mem_copy after all params are received ---
        for action in deferred {
            match action {
                Deferred::LargeCopy { ptr, slot, sz } => {
                    let size_val = self.builder.iconst(
                        sz as i64,
                        64,
                        IntSignedness::DontCare,
                        Origin::synthetic(),
                    );
                    let align = 8;
                    let slot_annotated = Operand::annotated(slot, Annotation::Align(align));
                    let ptr_annotated = Operand::annotated(ptr, Annotation::Align(align));
                    let new_mem = self.builder.mem_copy(
                        slot_annotated.into(),
                        ptr_annotated.into(),
                        size_val.into(),
                        self.current_mem.into(),
                        Origin::synthetic(),
                    );
                    self.current_mem = new_mem.raw();
                }
                Deferred::TwoReg {
                    lo,
                    hi,
                    slot,
                    hi_bytes,
                } => {
                    self.current_mem = self
                        .builder
                        .store(
                            lo.into(),
                            slot.into(),
                            8,
                            self.current_mem.into(),
                            Origin::synthetic(),
                        )
                        .raw();
                    let off =
                        self.builder
                            .iconst(8i64, 64, IntSignedness::DontCare, Origin::synthetic());
                    let hi_addr =
                        self.builder
                            .ptradd(slot.into(), off.into(), 0, Origin::synthetic());
                    self.current_mem = self
                        .builder
                        .store(
                            hi.into(),
                            hi_addr.into(),
                            hi_bytes as u32,
                            self.current_mem.into(),
                            Origin::synthetic(),
                        )
                        .raw();
                }
                Deferred::OneReg { val, slot, sz } => {
                    self.current_mem = self
                        .builder
                        .store(
                            val.into(),
                            slot.into(),
                            sz as u32,
                            self.current_mem.into(),
                            Origin::synthetic(),
                        )
                        .raw();
                }
            }
        }
    }
}
