use std::collections::HashMap;
use std::sync::atomic::Ordering;

use num_bigint::BigInt;
use rustc_middle::mir::{self, BasicBlock};
use rustc_middle::ty::{self, Instance, TyCtxt};
use tuffy_codegen::AbiMetadataBox;
use tuffy_ir::builder::Builder;
use tuffy_ir::instruction::{Operand as IrOperand, Origin};
use tuffy_ir::module::{SymbolId, SymbolTable};
use tuffy_ir::types::{Annotation, FloatType, FpRewriteFlags, Type};
use tuffy_ir::value::{BlockRef, ValueRef};

use super::types::*;
use super::StaticDataVec;
use super::STATIC_DATA_COUNTER;

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
pub(super) fn extract_param_names(mir: &mir::Body<'_>, symbols: &mut SymbolTable) -> Vec<Option<SymbolId>> {
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
}

impl<'a, 'tcx> TranslationCtx<'a, 'tcx> {
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
        if matches!(self.builder.value_type(val), Some(Type::Int)) {
            self.builder.inttoptr(val.into(), 0, Origin::synthetic())
        } else {
            val
        }
    }

    /// Convert a 128-bit integer (split into two 64-bit words) to a float.
    ///
    /// `lo` and `hi` are the lower and upper 64-bit halves.  `signed` indicates
    /// whether the original type was i128 (vs u128).  The result is a float
    /// value (Type::Float) — caller must bitcast back to Int if needed.
    pub(super) fn emit_u128_to_float(
        &mut self,
        lo: ValueRef,
        hi: ValueRef,
        signed: bool,
        ft: FloatType,
    ) -> ValueRef {
        if signed {
            // i128 → float: compute abs value, convert as unsigned, apply sign.
            //
            // IMPORTANT: int_to_bool stores a condition code (FLAGS) that gets
            // clobbered by subsequent int_to_bool calls.  We must recompute
            // the Bool immediately before each select that consumes it.
            let c63 = self.builder.iconst(63i64, Origin::synthetic());
            let sign_bit = self.builder.shr(
                hi.into(), c63.into(),
                Some(Annotation::Unsigned(64)), Origin::synthetic(),
            );

            // Negate 128-bit: neg_lo = 0 - lo, neg_hi = 0 - hi - (lo != 0)
            let zero = self.builder.iconst(0i64, Origin::synthetic());
            let neg_lo = self.builder.sub(
                zero.into(), lo.into(), None, Origin::synthetic(),
            );
            let lo_nz = self.builder.int_to_bool(lo.into(), Origin::synthetic());
            let borrow = self.builder.bool_to_int(lo_nz.into(), Origin::synthetic());
            let neg_hi_tmp = self.builder.sub(
                zero.into(), hi.into(), None, Origin::synthetic(),
            );
            let neg_hi = self.builder.sub(
                neg_hi_tmp.into(), borrow.into(), None, Origin::synthetic(),
            );

            // Select abs value — recompute Bool fresh before each select
            let is_neg1 = self.builder.int_to_bool(
                sign_bit.into(), Origin::synthetic(),
            );
            let abs_lo = self.builder.select(
                is_neg1.into(), neg_lo.into(), lo.into(),
                Type::Int, Origin::synthetic(),
            );
            let is_neg2 = self.builder.int_to_bool(
                sign_bit.into(), Origin::synthetic(),
            );
            let abs_hi = self.builder.select(
                is_neg2.into(), neg_hi.into(), hi.into(),
                Type::Int, Origin::synthetic(),
            );

            // Convert absolute value as unsigned
            let abs_f = self.emit_u64_pair_to_float(abs_lo, abs_hi, ft);

            // Apply sign via XOR — pure integer arithmetic, no select needed.
            let abs_bits = self.builder.bitcast(
                abs_f.into(), Type::Int, None, Origin::synthetic(),
            );
            let sign_bit_pos: i64 = match ft {
                FloatType::F64 => 63,
                FloatType::F32 => 31,
                _ => 63,
            };
            let pos_c = self.builder.iconst(sign_bit_pos, Origin::synthetic());
            let sign_mask = self.builder.shl(
                sign_bit.into(), pos_c.into(), None, Origin::synthetic(),
            );
            let result_bits = self.builder.xor(
                abs_bits.into(), sign_mask.into(), None, Origin::synthetic(),
            );
            self.builder.bitcast(
                result_bits.into(), Type::Float(ft), None, Origin::synthetic(),
            )
        } else {
            self.emit_u64_pair_to_float(lo, hi, ft)
        }
    }

    /// Convert an unsigned 128-bit value (two u64 words) to float.
    ///
    /// Each half is converted via si_to_fp (the only x86 instruction available)
    /// with a 2^64 correction when the high bit is set, then combined as
    /// `hi_f * 2^64 + lo_f`.
    pub(super) fn emit_u64_pair_to_float(
        &mut self,
        lo: ValueRef,
        hi: ValueRef,
        ft: FloatType,
    ) -> ValueRef {
        let flags = FpRewriteFlags::default();

        // 2^64 as a float constant (bit pattern in integer domain)
        let pow2_64_bits: i64 = match ft {
            FloatType::F64 => 0x43F0000000000000u64 as i64,
            FloatType::F32 => 0x5F800000i64,
            _ => 0x43F0000000000000u64 as i64,
        };
        let pow2_64_int = self.builder.iconst(pow2_64_bits, Origin::synthetic());
        let zero_int = self.builder.iconst(0i64, Origin::synthetic());
        let c63 = self.builder.iconst(63i64, Origin::synthetic());

        // lo: si_to_fp + correction if high bit set
        let lo_f = self.builder.si_to_fp(lo.into(), ft, Origin::synthetic());
        let lo_sign = self.builder.shr(
            lo.into(), c63.into(),
            Some(Annotation::Unsigned(64)), Origin::synthetic(),
        );
        let lo_hi_bit = self.builder.int_to_bool(lo_sign.into(), Origin::synthetic());
        // Select correction in Int domain, then bitcast to Float
        let lo_corr_int = self.builder.select(
            lo_hi_bit.into(), pow2_64_int.into(), zero_int.into(),
            Type::Int, Origin::synthetic(),
        );
        let lo_corr_f = self.builder.bitcast(
            lo_corr_int.into(), Type::Float(ft), None, Origin::synthetic(),
        );
        let lo_corrected = self.builder.fadd(
            lo_f.into(), lo_corr_f.into(), flags,
            Type::Float(ft), Origin::synthetic(),
        );

        // hi: si_to_fp + correction if high bit set
        let hi_f = self.builder.si_to_fp(hi.into(), ft, Origin::synthetic());
        let hi_sign = self.builder.shr(
            hi.into(), c63.into(),
            Some(Annotation::Unsigned(64)), Origin::synthetic(),
        );
        let hi_hi_bit = self.builder.int_to_bool(hi_sign.into(), Origin::synthetic());
        let hi_corr_int = self.builder.select(
            hi_hi_bit.into(), pow2_64_int.into(), zero_int.into(),
            Type::Int, Origin::synthetic(),
        );
        let hi_corr_f = self.builder.bitcast(
            hi_corr_int.into(), Type::Float(ft), None, Origin::synthetic(),
        );
        let hi_corrected = self.builder.fadd(
            hi_f.into(), hi_corr_f.into(), flags,
            Type::Float(ft), Origin::synthetic(),
        );

        // result = hi_f * 2^64 + lo_f
        let pow2_64_f = self.builder.bitcast(
            pow2_64_int.into(), Type::Float(ft), None, Origin::synthetic(),
        );
        let hi_scaled = self.builder.fmul(
            hi_corrected.into(), pow2_64_f.into(),
            flags, Type::Float(ft), Origin::synthetic(),
        );
        self.builder.fadd(
            hi_scaled.into(), lo_corrected.into(),
            flags, Type::Float(ft), Origin::synthetic(),
        )
    }

    /// Transform an IEEE 754 float bit-pattern so unsigned integer comparison
    /// gives correct float ordering (works for both positive and negative).
    pub(super) fn float_to_orderable(&mut self, val: ValueRef) -> IrOperand {
        let sixty3 = self.builder.iconst(63i64, Origin::synthetic());
        let mask = self.builder.shr(
            IrOperand::annotated(val, Annotation::Signed(64)),
            sixty3.into(),
            None,
            Origin::synthetic(),
        );
        let sign_bit = self
            .builder
            .iconst(BigInt::from(0x8000_0000_0000_0000u64), Origin::synthetic());
        let flip = self
            .builder
            .or(mask.into(), sign_bit.into(), None, Origin::synthetic());
        let result = self
            .builder
            .xor(val.into(), flip.into(), None, Origin::synthetic());
        result.into()
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
        let file_sym_name = format!(
            ".Lloc_file.{}",
            STATIC_DATA_COUNTER.fetch_add(1, Ordering::Relaxed)
        );
        let file_sym_id = self.symbols.intern(&file_sym_name);
        self.static_data.push((file_sym_id, file_bytes, vec![]));

        // 2. Build the 24-byte Location struct.
        //    Layout: file_ptr(8) + file_len(8) + line(4) + col(4)
        let mut loc_bytes = vec![0u8; 24];
        // file_ptr at offset 0 — filled by relocation
        loc_bytes[8..16].copy_from_slice(&file_len.to_le_bytes());
        loc_bytes[16..20].copy_from_slice(&line.to_le_bytes());
        loc_bytes[20..24].copy_from_slice(&col.to_le_bytes());

        let loc_sym_name = format!(
            ".Lloc.{}",
            STATIC_DATA_COUNTER.fetch_add(1, Ordering::Relaxed)
        );
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
