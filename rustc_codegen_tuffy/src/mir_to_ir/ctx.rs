use std::collections::HashMap;

use rustc_middle::mir::{self, BasicBlock};
use rustc_middle::ty::{self, Instance, TyCtxt};
use tuffy_codegen::AbiMetadataBox;
use tuffy_ir::builder::Builder;
use tuffy_ir::instruction::Origin;
use tuffy_ir::module::{SymbolId, SymbolTable};
use tuffy_ir::types::{Annotation, Type};
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
    /// SRET pointer for functions returning large structs (>16 bytes).
    /// When set, param indices are shifted by 1 (param 0 = hidden SRET ptr).
    pub(super) sret_ptr: Option<ValueRef>,
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
        match self.builder.value_type(val) {
            Some(Type::Int) => self.builder.inttoptr(val.into(), 0, Origin::synthetic()),
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
        // When SRET is active, param 0 is the hidden return pointer.
        // Real MIR params start at index 1.
        let mut param_idx: u32 = if self.sret_ptr.is_some() { 1 } else { 0 };

        for i in 0..self.mir.arg_count {
            let local = mir::Local::from_usize(i + 1);
            let ty = self.monomorphize(self.mir.local_decls[local].ty);
            let ir_ty = translate_ty(self.tcx, ty);

            // Skip zero-sized (Unit) and untranslatable params — they don't
            // occupy a runtime slot. Assign a dummy value so downstream MIR
            // references to this local remain valid.
            match ir_ty {
                Some(Type::Unit) | None => {
                    let dummy = self.builder.iconst(0, Origin::synthetic());
                    self.locals.set(local, dummy);
                    continue;
                }
                _ => {}
            }

            // Zero-sized ADTs also do not occupy a runtime slot.
            if type_size(self.tcx, ty).unwrap_or(0) == 0 {
                let dummy = self.builder.iconst(0, Origin::synthetic());
                self.locals.set(local, dummy);
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
                let metadata = self.builder.param(
                    param_idx,
                    Type::Int,
                    None,
                    Origin::synthetic(),
                );
                param_idx += 1;
                self.locals.set(local, data_ptr);
                self.fat_locals.set(local, metadata);
            } else {
                let ir_ty_val = ir_ty.expect("checked above");
                let sz = type_size(self.tcx, ty).unwrap_or(0);

                // For >16 byte parameters, the caller passes a pointer per x86-64 ABI.
                // The parameter receives this pointer, so create it as Ptr type.
                let (param_ty, is_indirect) = if sz > 16 {
                    (Type::Ptr(0), true)
                } else {
                    (ir_ty_val, false)
                };

                // For composite types of 9–16 bytes that contain no floats
                // and passed as an integer, annotate the parameter as
                // Unsigned(128) so the legalizer treats it as a two-slot
                // (lo, hi) value — matching the caller's ABI which passes
                // such values in two registers.
                let base_ann = translate_annotation(ty);
                let ann = if !is_indirect && base_ann.is_none() && param_ty == Type::Int {
                    if sz > 8 && sz <= 16 && !ty_contains_float(self.tcx, ty) {
                        Some(Annotation::Unsigned(128))
                    } else {
                        None
                    }
                } else {
                    base_ann
                };

                let val = self.builder.param(
                    param_idx,
                    param_ty,
                    ann,
                    Origin::synthetic(),
                );
                self.locals.set(local, val);

                // Mark >16 byte parameters as stack locals so element access
                // knows to dereference the pointer.
                if is_indirect {
                    self.stack_locals.mark(local);
                }

                param_idx += 1;
            }
        }
    }
}
