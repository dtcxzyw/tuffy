use std::collections::HashMap;

use rustc_middle::mir::{self, BasicBlock};
use rustc_middle::ty::{self, Instance, TyCtxt};
use tuffy_codegen::AbiMetadataBox;
use tuffy_ir::builder::Builder;
use tuffy_ir::instruction::Origin;
use tuffy_ir::module::{SymbolId, SymbolTable};
use tuffy_ir::types::Type;
use tuffy_ir::value::{BlockRef, ValueRef};

use super::StaticDataVec;
use super::types::*;

pub(super) struct LocalMap {
    pub(super) values: Vec<Option<ValueRef>>,
}

impl LocalMap {
    pub(super) fn new(count: usize) -> Self {
        Self {
            values: vec![None; count],
        }
    }

    pub(super) fn set(&mut self, local: mir::Local, val: ValueRef) {
        self.values[local.as_usize()] = Some(val);
    }

    pub(super) fn get(&self, local: mir::Local) -> Option<ValueRef> {
        self.values[local.as_usize()]
    }
}

/// Tracks the "high" component of fat pointer locals (e.g., length for &str).
pub(super) struct FatLocalMap {
    /// Maps MIR local index → high ValueRef (e.g., slice length).
    values: HashMap<usize, ValueRef>,
}

impl FatLocalMap {
    pub(super) fn new() -> Self {
        Self {
            values: HashMap::new(),
        }
    }

    pub(super) fn set(&mut self, local: mir::Local, val: ValueRef) {
        self.values.insert(local.as_usize(), val);
    }

    pub(super) fn get(&self, local: mir::Local) -> Option<ValueRef> {
        self.values.get(&local.as_usize()).copied()
    }
}

/// Tracks which MIR locals hold stack slot addresses (aggregate/spilled values)
/// rather than scalar values in registers.
pub(super) struct StackLocalSet {
    is_stack: Vec<bool>,
}

impl StackLocalSet {
    pub(super) fn new(count: usize) -> Self {
        Self {
            is_stack: vec![false; count],
        }
    }

    pub(super) fn mark(&mut self, local: mir::Local) {
        self.is_stack[local.as_usize()] = true;
    }

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
    blocks: Vec<Option<BlockRef>>,
}

impl BlockMap {
    pub(super) fn new(count: usize) -> Self {
        Self {
            blocks: vec![None; count],
        }
    }

    pub(super) fn set(&mut self, bb: BasicBlock, block: BlockRef) {
        self.blocks[bb.as_usize()] = Some(block);
    }

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
    pub(super) tcx: TyCtxt<'tcx>,
    pub(super) mir: &'a mir::Body<'tcx>,
    pub(super) builder: Builder<'a>,
    pub(super) locals: LocalMap,
    pub(super) fat_locals: FatLocalMap,
    pub(super) stack_locals: StackLocalSet,
    pub(super) symbols: SymbolTable,
    pub(super) static_data: StaticDataVec,
    pub(super) block_map: BlockMap,
    /// MemSSA block arguments: one `Type::Mem` arg per MIR basic block.
    pub(super) block_mem_args: Vec<ValueRef>,
    pub(super) abi_metadata: AbiMetadataBox,
    pub(super) instance: Instance<'tcx>,
    pub(super) sret_ptr: Option<ValueRef>,
    pub(super) use_sret: bool,
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
}

impl<'a, 'tcx> TranslationCtx<'a, 'tcx> {
    pub(super) fn next_data_id(&mut self) -> u64 {
        let id = *self.data_counter;
        *self.data_counter += 1;
        id
    }

    /// Monomorphize a MIR type using the current instance's substitutions.
    pub(super) fn monomorphize(&self, ty: ty::Ty<'tcx>) -> ty::Ty<'tcx> {
        self.tcx.instantiate_and_normalize_erasing_regions(
            self.instance.args,
            ty::TypingEnv::fully_monomorphized(),
            ty::EarlyBinder::bind(ty),
        )
    }

    /// If `val` is a Ptr or Bool, coerce it to Int.
    pub(super) fn coerce_to_int(&mut self, val: ValueRef) -> ValueRef {
        match self.builder.value_type(val) {
            Some(Type::Ptr(_)) => self.builder.ptrtoaddr(val.into(), Origin::synthetic()),
            Some(Type::Bool) => self.builder.bool_to_int(val.into(), Origin::synthetic()),
            _ => val,
        }
    }

    /// If `val` is an Int, insert inttoptr to coerce it to Ptr.
    pub(super) fn coerce_to_ptr(&mut self, val: ValueRef) -> ValueRef {

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
        self.static_data.push((file_sym_id, file_bytes, vec![]));

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
            .push((loc_sym_id, loc_bytes, vec![(0, file_sym_str)]));

        self.builder.symbol_addr(loc_sym_id, Origin::synthetic())
    }

    pub(super) fn translate_params(&mut self) {
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
            // Skip zero-sized ADTs (e.g. Global allocator) — they
            // don't occupy an ABI slot.
            if param_size == 0 {
                let dummy = self.builder.iconst(0, Origin::synthetic());
                self.locals.set(local, dummy);
                continue;
            }
            let large_struct = param_size > 16 && matches!(ir_ty, Some(Type::Int));
            let two_reg_struct = param_size > 8
                && param_size <= 16
                && matches!(ir_ty, Some(Type::Int))
                && !is_i128_or_u128(ty);
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
            if is_fat_ptr(self.tcx, ty) {
                let meta_ty = fat_ptr_meta_type(self.tcx, ty);
                let meta_val = self
                    .builder
                    .param(abi_idx, meta_ty, None, Origin::synthetic());
                self.fat_locals.set(local, meta_val);
                abi_idx += 1;
            }
        }
    }
}
