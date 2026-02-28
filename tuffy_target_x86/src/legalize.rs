//! i128/u128 type legalization pass.
//!
//! Splits 128-bit integer operations into pairs of 64-bit operations
//! before instruction selection. Runs as the first stage of the x86
//! backend pipeline.

use std::collections::{HashMap, HashSet};

use num_bigint::BigInt;
use num_traits::{ToPrimitive, Zero};

use tuffy_ir::builder::Builder;
use tuffy_ir::function::{CfgNode, Function};
use tuffy_ir::instruction::{ICmpOp, Op, Operand, Origin};
use tuffy_ir::types::{Annotation, Type};
use tuffy_ir::value::{BlockRef, ValueRef};

use tuffy_target::backend::AbiMetadata;

use crate::backend::X86AbiMetadata;

// ---------------------------------------------------------------------------
// Value mapping
// ---------------------------------------------------------------------------

#[derive(Clone, Copy)]
enum Mapped {
    One(ValueRef),
    Pair(ValueRef, ValueRef),
}

struct VMap(HashMap<u32, Mapped>);

impl VMap {
    fn new() -> Self {
        Self(HashMap::new())
    }
    fn set(&mut self, old: ValueRef, m: Mapped) {
        self.0.insert(old.raw(), m);
    }
    fn get(&self, old: ValueRef) -> Mapped {
        self.0.get(&old.raw()).copied().unwrap_or(Mapped::One(old))
    }
    fn one(&self, old: ValueRef) -> ValueRef {
        match self.get(old) {
            Mapped::One(v) | Mapped::Pair(v, _) => v,
        }
    }
    fn pair(&self, old: ValueRef) -> (ValueRef, ValueRef) {
        match self.get(old) {
            Mapped::Pair(lo, hi) => (lo, hi),
            Mapped::One(v) => (v, v),
        }
    }
    fn remap_op(&self, op: &Operand) -> Operand {
        let v = self.one(op.value);
        match op.annotation {
            Some(a) => Operand::annotated(v, a),
            None => Operand::new(v),
        }
    }
}

// ---------------------------------------------------------------------------
// Detection
// ---------------------------------------------------------------------------

fn is_128(ann: Option<&Annotation>) -> bool {
    matches!(
        ann,
        Some(Annotation::Signed(128) | Annotation::Unsigned(128))
    )
}

fn is_signed_128(ann: Option<&Annotation>) -> bool {
    matches!(ann, Some(Annotation::Signed(128)))
}

fn needs_wide_const(v: &BigInt) -> bool {
    !v.is_zero() && v.to_i64().is_none() && v.to_u64().is_none()
}

fn has_128bit_values(func: &Function) -> bool {
    if func.param_annotations.iter().any(|a| is_128(a.as_ref())) {
        return true;
    }
    if is_128(func.ret_annotation.as_ref()) {
        return true;
    }
    for inst in &func.instructions {
        if is_128(inst.result_annotation.as_ref()) {
            return true;
        }
        match &inst.op {
            Op::Load(_, 16, _) | Op::Store(_, _, 16, _) => return true,
            Op::Sext(_, 128) | Op::Zext(_, 128) => return true,
            Op::Bswap(_, 16) => return true,
            Op::RotateLeft(_, _, 128) | Op::RotateRight(_, _, 128) => return true,
            Op::SaturatingAdd(_, _, 128) | Op::SaturatingSub(_, _, 128) => return true,
            Op::Const(v) if needs_wide_const(v) => return true,
            _ => {}
        }
    }
    false
}

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

pub fn legalize_i128(
    func: &Function,
    metadata: &X86AbiMetadata,
) -> Option<(Function, X86AbiMetadata)> {
    if !has_128bit_values(func) && metadata.wide_return_calls.is_empty() {
        return None;
    }
    let (out, state) = build_new_func(func, metadata);
    Some(run_legalize(func, out, state))
}

// ---------------------------------------------------------------------------
// State (separate from Function so Builder can borrow Function independently)
// ---------------------------------------------------------------------------

struct State {
    meta: X86AbiMetadata,
    /// Original ABI metadata from before legalization, used to transfer
    /// non-128-bit secondary return info (e.g. 16-byte struct returns in
    /// RAX+RDX) that would otherwise be lost when instruction indices change.
    old_meta: X86AbiMetadata,
    vmap: VMap,
    bmap: HashMap<u32, BlockRef>,
    /// Old param index → (new_lo_index, Option<new_hi_index>).
    param_map: Vec<(u32, Option<u32>)>,
    /// Set of old ValueRef raw values that are 128-bit.
    wide: HashSet<u32>,
    /// Old RDX-capture instruction index → new ValueRef created in leg_call.
    /// Used to avoid re-creating the capture in copy_inst.
    rdx_capture_remap: HashMap<u32, ValueRef>,
}

fn o() -> Origin {
    Origin::synthetic()
}

fn build_new_func(old: &Function, old_meta: &X86AbiMetadata) -> (Function, State) {
    let mut params = Vec::new();
    let mut param_anns = Vec::new();
    let mut param_names = Vec::new();
    let mut param_map = Vec::new();

    for (i, ty) in old.params.iter().enumerate() {
        let ann = old.param_annotations.get(i).and_then(|a| a.as_ref());
        let name = old.param_names.get(i).and_then(|n| *n);
        if is_128(ann) {
            let lo_idx = params.len() as u32;
            params.push(Type::Int);
            param_anns.push(Some(Annotation::Unsigned(64)));
            param_names.push(name);
            let hi_idx = params.len() as u32;
            params.push(Type::Int);
            param_anns.push(Some(Annotation::Unsigned(64)));
            param_names.push(None);
            param_map.push((lo_idx, Some(hi_idx)));
        } else {
            let idx = params.len() as u32;
            params.push(ty.clone());
            param_anns.push(old.param_annotations.get(i).cloned().flatten());
            param_names.push(name);
            param_map.push((idx, None));
        }
    }

    let ret_ty = old.ret_ty.clone();
    let ret_ann = if is_128(old.ret_annotation.as_ref()) {
        Some(Annotation::Unsigned(64))
    } else {
        old.ret_annotation
    };

    let wide = collect_wide_values(old, old_meta);
    let out = Function::new(old.name, params, param_anns, param_names, ret_ty, ret_ann);
    let state = State {
        meta: X86AbiMetadata::default(),
        old_meta: old_meta.clone(),
        vmap: VMap::new(),
        bmap: HashMap::new(),
        param_map,
        wide,
        rdx_capture_remap: HashMap::new(),
    };
    (out, state)
}

// ---------------------------------------------------------------------------
// Pre-scan: identify 128-bit values in the old function
// ---------------------------------------------------------------------------

fn collect_wide_values(old: &Function, meta: &X86AbiMetadata) -> HashSet<u32> {
    let mut wide = HashSet::new();

    // Mark instructions that produce 128-bit results.
    for (i, inst) in old.instructions.iter().enumerate() {
        let vref = ValueRef::inst_result(i as u32);
        if is_128(inst.result_annotation.as_ref()) {
            wide.insert(vref.raw());
            continue;
        }
        // Calls returning i128/u128 are marked in ABI metadata (the call
        // instruction itself has no result_annotation because its primary
        // result type is Mem).
        if meta.wide_return_calls.contains(&(i as u32)) {
            let sec = ValueRef::inst_secondary_result(i as u32);
            wide.insert(sec.raw());
        }
        match &inst.op {
            Op::Const(v) if needs_wide_const(v) => {
                wide.insert(vref.raw());
            }
            Op::Load(_, 16, _) => {
                wide.insert(vref.raw());
            }
            Op::Sext(_, 128) | Op::Zext(_, 128) => {
                wide.insert(vref.raw());
            }
            Op::Bswap(_, 16) => {
                wide.insert(vref.raw());
            }
            Op::RotateLeft(_, _, 128) | Op::RotateRight(_, _, 128) => {
                wide.insert(vref.raw());
            }
            Op::SaturatingAdd(_, _, 128) | Op::SaturatingSub(_, _, 128) => {
                wide.insert(vref.raw());
            }
            _ => {}
        }
    }

    // Scan branches to find 128-bit block args.
    for inst in &old.instructions {
        let check_args =
            |target: BlockRef, args: &[Operand], wide: &HashSet<u32>, out: &mut HashSet<u32>| {
                let bb = old.block(target);
                for (j, arg) in args.iter().enumerate() {
                    if wide.contains(&arg.value.raw()) {
                        let ba_idx = bb.arg_start + j as u32;
                        out.insert(ValueRef::block_arg(ba_idx).raw());
                    }
                }
            };
        match &inst.op {
            Op::Br(target, args) => {
                let mut new_wide = HashSet::new();
                check_args(*target, args, &wide, &mut new_wide);
                wide.extend(new_wide);
            }
            Op::BrIf(_, then_blk, then_args, else_blk, else_args) => {
                let mut new_wide = HashSet::new();
                check_args(*then_blk, then_args, &wide, &mut new_wide);
                check_args(*else_blk, else_args, &wide, &mut new_wide);
                wide.extend(new_wide);
            }
            _ => {}
        }
    }

    wide
}

fn is_wide(s: &State, v: ValueRef) -> bool {
    s.wide.contains(&v.raw())
}

// ---------------------------------------------------------------------------
// Main legalization loop
// ---------------------------------------------------------------------------

fn run_legalize(old: &Function, mut out: Function, mut s: State) -> (Function, X86AbiMetadata) {
    {
        let mut b = Builder::new(&mut out);
        let old_root = old.root_region;
        let new_root = b.create_region(old.region(old_root).kind);
        b.enter_region(new_root);
        walk_region(old, &mut s, &mut b, old_root);
        b.exit_region();
    }
    (out, s.meta)
}

fn walk_region(
    old: &Function,
    s: &mut State,
    b: &mut Builder,
    old_region: tuffy_ir::value::RegionRef,
) {
    // Phase 1: pre-create all blocks and their args so that forward
    // block references (e.g. brif targets) can be resolved during
    // instruction processing.
    precreate_blocks(old, s, b, old_region);

    // Phase 2: process instructions in each block.
    for child in &old.region(old_region).children {
        match child {
            CfgNode::Block(old_blk) => {
                walk_block_insts(old, s, b, *old_blk);
            }
            CfgNode::Region(old_sub) => {
                let new_sub = b.create_region(old.region(*old_sub).kind);
                b.enter_region(new_sub);
                walk_region(old, s, b, *old_sub);
                b.exit_region();
            }
        }
    }
}

/// Pre-create all blocks (and their args) in a region so that `bmap`
/// is fully populated before any instructions are processed.  This
/// avoids panics on forward block references in `brif`/`br`.
fn precreate_blocks(
    old: &Function,
    s: &mut State,
    b: &mut Builder,
    old_region: tuffy_ir::value::RegionRef,
) {
    for child in &old.region(old_region).children {
        if let CfgNode::Block(old_blk) = child {
            let new_blk = b.create_block();
            s.bmap.insert(old_blk.index(), new_blk);

            // Recreate block args, splitting 128-bit ones.
            let old_bb = old.block(*old_blk);
            for i in 0..old_bb.arg_count {
                let old_ba_idx = old_bb.arg_start + i;
                let old_ba_ref = ValueRef::block_arg(old_ba_idx);
                let ba_ty = old.block_args[old_ba_idx as usize].ty.clone();

                if s.wide.contains(&old_ba_ref.raw()) {
                    let lo = b.add_block_arg(new_blk, Type::Int);
                    let hi = b.add_block_arg(new_blk, Type::Int);
                    s.vmap.set(old_ba_ref, Mapped::Pair(lo, hi));
                } else {
                    let v = b.add_block_arg(new_blk, ba_ty);
                    s.vmap.set(old_ba_ref, Mapped::One(v));
                }
            }
        }
        // Regions are handled recursively in walk_region phase 2.
    }
}

/// Process instructions in a pre-created block.
fn walk_block_insts(old: &Function, s: &mut State, b: &mut Builder, old_blk: BlockRef) {
    let new_blk = s.bmap[&old_blk.index()];
    b.switch_to_block(new_blk);

    for (old_vref, inst) in old.block_insts_with_values(old_blk) {
        legalize_inst(old, s, b, old_vref, inst);
    }
}

// ---------------------------------------------------------------------------
// Instruction dispatch
// ---------------------------------------------------------------------------

#[allow(clippy::too_many_lines)]
fn legalize_inst(
    old: &Function,
    s: &mut State,
    b: &mut Builder,
    old_vref: ValueRef,
    inst: &tuffy_ir::instruction::Instruction,
) {
    let ann = inst.result_annotation.as_ref();
    let wide_result = is_128(ann);

    match &inst.op {
        Op::Param(idx) => {
            let (lo_idx, hi_idx) = s.param_map[*idx as usize];
            if let Some(hi) = hi_idx {
                leg_param(s, b, old_vref, lo_idx, hi);
            } else {
                let ann = old.param_annotations.get(*idx as usize).cloned().flatten();
                let ty = old.params[*idx as usize].clone();
                let v = b.param(lo_idx, ty, ann, o());
                s.vmap.set(old_vref, Mapped::One(v));
            }
        }
        Op::Const(val) if needs_wide_const(val) => {
            leg_wide_const(s, b, old_vref, val);
        }
        Op::Add(a, op_b) if wide_result => {
            leg_add(s, b, old_vref, a, op_b);
        }
        Op::Sub(a, op_b) if wide_result => {
            leg_sub(s, b, old_vref, a, op_b);
        }
        Op::Mul(a, op_b) if wide_result => {
            leg_mul(s, b, old_vref, a, op_b);
        }
        Op::And(a, op_b) if wide_result => {
            leg_bitwise(s, b, old_vref, a, op_b, BitwiseKind::And);
        }
        Op::Or(a, op_b) if wide_result => {
            leg_bitwise(s, b, old_vref, a, op_b, BitwiseKind::Or);
        }
        Op::Xor(a, op_b) if wide_result => {
            leg_bitwise(s, b, old_vref, a, op_b, BitwiseKind::Xor);
        }
        Op::Shl(a, op_b) if wide_result => {
            leg_shl(s, b, old_vref, a, op_b, ann);
        }
        Op::Shr(a, op_b) if wide_result || is_128(a.annotation.as_ref()) => {
            leg_shr(s, b, old_vref, a, op_b, ann);
        }
        Op::ICmp(cmp_op, a, op_b) if is_wide(s, a.value) || is_128(a.annotation.as_ref()) => {
            leg_icmp(s, b, old_vref, *cmp_op, a, op_b);
        }
        Op::Load(ptr, 16, mem) => {
            leg_load_128(s, b, old_vref, ptr, mem);
        }
        Op::Store(val, ptr, 16, mem) => {
            leg_store_128(s, b, old_vref, val, ptr, mem);
        }
        Op::Sext(val, 128) => {
            leg_sext_128(s, b, old_vref, val);
        }
        Op::Zext(val, 128) => {
            leg_zext_128(s, b, old_vref, val);
        }
        Op::Bswap(val, 16) => {
            leg_bswap_128(s, b, old_vref, val);
        }
        Op::Select(cond, tv, fv) if wide_result => {
            leg_select_128(s, b, old_vref, cond, tv, fv);
        }
        Op::BoolToInt(val) if wide_result => {
            leg_bool_to_int_128(s, b, old_vref, val);
        }
        Op::Ret(val, mem) if is_128(old.ret_annotation.as_ref()) => {
            leg_ret(s, b, old_vref, val, mem);
        }
        Op::Call(callee, args, mem) => {
            leg_call(old, s, b, old_vref, inst, callee, args, mem);
        }
        Op::Br(target, args) => {
            leg_br(s, b, old_vref, *target, args);
        }
        Op::BrIf(cond, then_blk, then_args, else_blk, else_args) => {
            leg_brif(
                s, b, old_vref, cond, *then_blk, then_args, *else_blk, else_args,
            );
        }
        Op::Continue(args) => {
            leg_continue(s, b, old_vref, args);
        }
        Op::RegionYield(args) => {
            leg_region_yield(s, b, old_vref, args);
        }
        // Truncation from 128-bit: just use the lo half.
        Op::Sext(val, bits) if is_wide(s, val.value) && *bits < 128 => {
            let lo = s.vmap.one(val.value);
            let v = b.sext(Operand::new(lo), *bits, o());
            s.vmap.set(old_vref, Mapped::One(v));
        }
        Op::Zext(val, bits) if is_wide(s, val.value) && *bits < 128 => {
            let lo = s.vmap.one(val.value);
            let v = b.zext(Operand::new(lo), *bits, o());
            s.vmap.set(old_vref, Mapped::One(v));
        }
        Op::Bitcast(val) if is_wide(s, val.value) => {
            // Truncate to lo half for bitcast from 128-bit.
            let lo = s.vmap.one(val.value);
            let v = b.bitcast(Operand::new(lo), inst.ty.clone(), ann.cloned(), o());
            s.vmap.set(old_vref, Mapped::One(v));
        }
        Op::Store(val, ptr, bytes, mem) if is_wide(s, val.value) => {
            // Store both halves of a 128-bit value to the target address.
            let (lo, hi) = s.vmap.pair(val.value);
            let p = remap_op(s, ptr);
            let m = remap_op(s, mem);
            let m1 = b.store(Operand::new(lo), p.clone(), 8, m, o());
            let off = b.iconst(8i64, o());
            let hi_addr = b.ptradd(p, Operand::new(off), 0, o());
            let m2 = b.store(
                Operand::new(hi),
                Operand::new(hi_addr),
                8,
                Operand::new(m1),
                o(),
            );
            s.vmap.set(old_vref, Mapped::One(m2));
        }
        _ => {
            // Skip instructions already remapped as RDX captures in leg_call.
            if s.rdx_capture_remap.contains_key(&old_vref.index()) {
                return;
            }
            copy_inst(s, b, old_vref, inst);
        }
    }
}

// ---------------------------------------------------------------------------
// Copy non-128-bit instruction with remapped operands
// ---------------------------------------------------------------------------

fn remap_op(s: &State, op: &Operand) -> Operand {
    s.vmap.remap_op(op)
}

fn new_block(s: &State, old: BlockRef) -> BlockRef {
    s.bmap[&old.index()]
}

#[allow(clippy::too_many_lines)]
fn copy_inst(
    s: &mut State,
    b: &mut Builder,
    old_vref: ValueRef,
    inst: &tuffy_ir::instruction::Instruction,
) {
    let ann = inst.result_annotation;
    let v = match &inst.op {
        Op::Param(idx) => b.param(*idx, inst.ty.clone(), ann, o()),
        Op::Const(val) => b.iconst(val.clone(), o()),
        Op::BConst(val) => b.bconst(*val, o()),
        Op::Add(a, op_b) => b.add(remap_op(s, a), remap_op(s, op_b), ann, o()),
        Op::Sub(a, op_b) => b.sub(remap_op(s, a), remap_op(s, op_b), ann, o()),
        Op::Mul(a, op_b) => b.mul(remap_op(s, a), remap_op(s, op_b), ann, o()),
        Op::Div(a, op_b) => b.div(remap_op(s, a), remap_op(s, op_b), ann, o()),
        Op::Rem(a, op_b) => b.rem(remap_op(s, a), remap_op(s, op_b), ann, o()),
        Op::And(a, op_b) => b.and(remap_op(s, a), remap_op(s, op_b), ann, o()),
        Op::Or(a, op_b) => b.or(remap_op(s, a), remap_op(s, op_b), ann, o()),
        Op::Xor(a, op_b) => b.xor(remap_op(s, a), remap_op(s, op_b), ann, o()),
        Op::Shl(a, op_b) => b.shl(remap_op(s, a), remap_op(s, op_b), ann, o()),
        Op::Shr(a, op_b) => b.shr(remap_op(s, a), remap_op(s, op_b), ann, o()),
        Op::Min(a, op_b) => b.min(remap_op(s, a), remap_op(s, op_b), ann, o()),
        Op::Max(a, op_b) => b.max(remap_op(s, a), remap_op(s, op_b), ann, o()),
        Op::CountOnes(a) => b.count_ones(remap_op(s, a), o()),
        Op::CountLeadingZeros(a, bits) => b.count_leading_zeros(remap_op(s, a), *bits, o()),
        Op::CountTrailingZeros(a) => b.count_trailing_zeros(remap_op(s, a), o()),
        Op::Bswap(a, bytes) => b.bswap(remap_op(s, a), *bytes, o()),
        Op::BitReverse(a, bits) => b.bit_reverse(remap_op(s, a), *bits, o()),
        Op::RotateLeft(a, amt, bits) => b.rotate_left(remap_op(s, a), remap_op(s, amt), *bits, o()),
        Op::RotateRight(a, amt, bits) => {
            b.rotate_right(remap_op(s, a), remap_op(s, amt), *bits, o())
        }
        Op::SaturatingAdd(a, op_b, bits) => {
            b.saturating_add(remap_op(s, a), remap_op(s, op_b), *bits, o())
        }
        Op::SaturatingSub(a, op_b, bits) => {
            b.saturating_sub(remap_op(s, a), remap_op(s, op_b), *bits, o())
        }
        Op::ICmp(cmp_op, a, op_b) => b.icmp(*cmp_op, remap_op(s, a), remap_op(s, op_b), o()),
        Op::FCmp(cmp_op, a, op_b) => b.fcmp(*cmp_op, remap_op(s, a), remap_op(s, op_b), o()),
        Op::Select(c, tv, fv) => b.select(
            remap_op(s, c),
            remap_op(s, tv),
            remap_op(s, fv),
            inst.ty.clone(),
            o(),
        ),
        Op::BoolToInt(a) => b.bool_to_int(remap_op(s, a), o()),
        Op::IntToBool(a) => b.int_to_bool(remap_op(s, a), o()),
        Op::Load(ptr, bytes, mem) => b.load(
            remap_op(s, ptr),
            *bytes,
            inst.ty.clone(),
            remap_op(s, mem),
            ann,
            o(),
        ),
        Op::Store(val, ptr, bytes, mem) => b.store(
            remap_op(s, val),
            remap_op(s, ptr),
            *bytes,
            remap_op(s, mem),
            o(),
        ),
        Op::StackSlot(bytes) => b.stack_slot(*bytes, o()),
        Op::SymbolAddr(sym) => b.symbol_addr(*sym, o()),
        Op::Bitcast(a) => b.bitcast(remap_op(s, a), inst.ty.clone(), ann, o()),
        Op::Sext(a, bits) => b.sext(remap_op(s, a), *bits, o()),
        Op::Zext(a, bits) => b.zext(remap_op(s, a), *bits, o()),
        Op::FpToSi(a) => b.fp_to_si(remap_op(s, a), o()),
        Op::FpToUi(a) => b.fp_to_ui(remap_op(s, a), o()),
        Op::SiToFp(a, ft) => b.si_to_fp(remap_op(s, a), *ft, o()),
        Op::UiToFp(a, ft) => b.ui_to_fp(remap_op(s, a), *ft, o()),
        Op::FpConvert(a) => {
            let ft = match &inst.ty {
                Type::Float(ft) => *ft,
                _ => tuffy_ir::types::FloatType::F64,
            };
            b.fp_convert(remap_op(s, a), ft, o())
        }
        Op::PtrAdd(ptr, off) => b.ptradd(remap_op(s, ptr), remap_op(s, off), 0, o()),
        Op::PtrDiff(a, op_b) => b.ptrdiff(remap_op(s, a), remap_op(s, op_b), o()),
        Op::PtrToInt(a) => b.ptrtoint(remap_op(s, a), o()),
        Op::PtrToAddr(a) => b.ptrtoaddr(remap_op(s, a), o()),
        Op::IntToPtr(a) => b.inttoptr(remap_op(s, a), 0, o()),
        Op::Ret(val, mem) => {
            let rv = val.as_ref().map(|v| remap_op(s, v));
            b.ret(rv, remap_op(s, mem), o())
        }
        Op::Unreachable => b.unreachable(o()),
        Op::Trap => b.trap(o()),
        // Branches/calls handled by dedicated leg_* functions; should not reach here.
        Op::Br(..) | Op::BrIf(..) | Op::Call(..) | Op::Continue(..) | Op::RegionYield(..) => {
            unreachable!("branch/call should be handled by dedicated leg_* function")
        }
        // Floating point: pass through with remapped operands.
        Op::FAdd(a, op_b, flags) => b.fadd(
            remap_op(s, a),
            remap_op(s, op_b),
            *flags,
            inst.ty.clone(),
            o(),
        ),
        Op::FSub(a, op_b, flags) => b.fsub(
            remap_op(s, a),
            remap_op(s, op_b),
            *flags,
            inst.ty.clone(),
            o(),
        ),
        Op::FMul(a, op_b, flags) => b.fmul(
            remap_op(s, a),
            remap_op(s, op_b),
            *flags,
            inst.ty.clone(),
            o(),
        ),
        Op::FDiv(a, op_b, flags) => b.fdiv(
            remap_op(s, a),
            remap_op(s, op_b),
            *flags,
            inst.ty.clone(),
            o(),
        ),
        Op::FRem(a, op_b, flags) => b.frem(
            remap_op(s, a),
            remap_op(s, op_b),
            *flags,
            inst.ty.clone(),
            o(),
        ),
        Op::FNeg(a) => b.fneg(remap_op(s, a), inst.ty.clone(), o()),
        Op::FAbs(a) => b.fabs(remap_op(s, a), inst.ty.clone(), o()),
        Op::CopySign(a, op_b) => {
            b.copysign(remap_op(s, a), remap_op(s, op_b), inst.ty.clone(), o())
        }
        // Atomics: pass through.
        Op::LoadAtomic(ptr, ord, mem) => {
            let (primary, secondary) = b.load_atomic(
                remap_op(s, ptr),
                inst.secondary_ty.clone().unwrap_or(Type::Int),
                *ord,
                remap_op(s, mem),
                o(),
            );
            s.vmap.set(old_vref, Mapped::One(primary));
            let old_sec = ValueRef::inst_secondary_result(old_vref.index());
            s.vmap.set(old_sec, Mapped::One(secondary));
            return;
        }
        Op::StoreAtomic(val, ptr, ord, mem) => b.store_atomic(
            remap_op(s, val),
            remap_op(s, ptr),
            *ord,
            remap_op(s, mem),
            o(),
        ),
        Op::AtomicRmw(rmw_op, ptr, val, ord, mem) => {
            let (primary, secondary) = b.atomic_rmw(
                *rmw_op,
                remap_op(s, ptr),
                remap_op(s, val),
                inst.secondary_ty.clone().unwrap_or(Type::Int),
                *ord,
                remap_op(s, mem),
                o(),
            );
            s.vmap.set(old_vref, Mapped::One(primary));
            let old_sec = ValueRef::inst_secondary_result(old_vref.index());
            s.vmap.set(old_sec, Mapped::One(secondary));
            return;
        }
        Op::AtomicCmpXchg(ptr, exp, des, s_ord, f_ord, mem) => {
            let (primary, secondary) = b.atomic_cmpxchg(
                remap_op(s, ptr),
                remap_op(s, exp),
                remap_op(s, des),
                inst.secondary_ty.clone().unwrap_or(Type::Int),
                *s_ord,
                *f_ord,
                remap_op(s, mem),
                o(),
            );
            s.vmap.set(old_vref, Mapped::One(primary));
            let old_sec = ValueRef::inst_secondary_result(old_vref.index());
            s.vmap.set(old_sec, Mapped::One(secondary));
            return;
        }
        Op::Fence(ord, mem) => b.fence(*ord, remap_op(s, mem), o()),
    };
    s.vmap.set(old_vref, Mapped::One(v));
}

// ---------------------------------------------------------------------------
// Bitwise operation kind
// ---------------------------------------------------------------------------

enum BitwiseKind {
    And,
    Or,
    Xor,
}

// ---------------------------------------------------------------------------
// 128-bit parameter
// ---------------------------------------------------------------------------

fn leg_param(s: &mut State, b: &mut Builder, old_vref: ValueRef, lo_idx: u32, hi_idx: u32) {
    let ann64 = Some(Annotation::Unsigned(64));
    let lo = b.param(lo_idx, Type::Int, ann64, o());
    let hi = b.param(hi_idx, Type::Int, ann64, o());
    s.vmap.set(old_vref, Mapped::Pair(lo, hi));
}

// ---------------------------------------------------------------------------
// Wide constant (> 64 bits)
// ---------------------------------------------------------------------------

fn leg_wide_const(s: &mut State, b: &mut Builder, old_vref: ValueRef, val: &BigInt) {
    let mask64: BigInt = (BigInt::from(1u128 << 64)) - 1;
    let lo_big = val & &mask64;
    let hi_big: BigInt = val >> 64;
    let lo = b.iconst(lo_big, o());
    let hi = b.iconst(hi_big, o());
    s.vmap.set(old_vref, Mapped::Pair(lo, hi));
}

// ---------------------------------------------------------------------------
// 128-bit add: lo = add(a_lo, b_lo), carry = icmp.ult(lo, a_lo),
//              hi = add(a_hi, b_hi), hi = add(hi, zext(carry))
// ---------------------------------------------------------------------------

fn leg_add(s: &mut State, b: &mut Builder, old_vref: ValueRef, a: &Operand, op_b: &Operand) {
    let ann64 = Some(Annotation::Unsigned(64));
    let (a_lo, a_hi) = s.vmap.pair(a.value);
    let (b_lo, b_hi) = s.vmap.pair(op_b.value);

    let lo = b.add(
        Operand::annotated(a_lo, Annotation::Unsigned(64)),
        Operand::annotated(b_lo, Annotation::Unsigned(64)),
        ann64,
        o(),
    );
    // carry = lo < a_lo (unsigned)
    let carry = b.icmp(
        ICmpOp::Lt,
        Operand::annotated(lo, Annotation::Unsigned(64)),
        Operand::annotated(a_lo, Annotation::Unsigned(64)),
        o(),
    );
    let carry_int = b.bool_to_int(Operand::new(carry), o());
    let hi_sum = b.add(
        Operand::annotated(a_hi, Annotation::Unsigned(64)),
        Operand::annotated(b_hi, Annotation::Unsigned(64)),
        ann64,
        o(),
    );
    let hi = b.add(
        Operand::annotated(hi_sum, Annotation::Unsigned(64)),
        Operand::annotated(carry_int, Annotation::Unsigned(64)),
        ann64,
        o(),
    );
    s.vmap.set(old_vref, Mapped::Pair(lo, hi));
}

// ---------------------------------------------------------------------------
// 128-bit sub
// ---------------------------------------------------------------------------

fn leg_sub(s: &mut State, b: &mut Builder, old_vref: ValueRef, a: &Operand, op_b: &Operand) {
    let ann64 = Some(Annotation::Unsigned(64));
    let (a_lo, a_hi) = s.vmap.pair(a.value);
    let (b_lo, b_hi) = s.vmap.pair(op_b.value);

    let lo = b.sub(
        Operand::annotated(a_lo, Annotation::Unsigned(64)),
        Operand::annotated(b_lo, Annotation::Unsigned(64)),
        ann64,
        o(),
    );
    let borrow = b.icmp(
        ICmpOp::Gt,
        Operand::annotated(lo, Annotation::Unsigned(64)),
        Operand::annotated(a_lo, Annotation::Unsigned(64)),
        o(),
    );
    let borrow_int = b.bool_to_int(Operand::new(borrow), o());
    let hi_diff = b.sub(
        Operand::annotated(a_hi, Annotation::Unsigned(64)),
        Operand::annotated(b_hi, Annotation::Unsigned(64)),
        ann64,
        o(),
    );
    let hi = b.sub(
        Operand::annotated(hi_diff, Annotation::Unsigned(64)),
        Operand::annotated(borrow_int, Annotation::Unsigned(64)),
        ann64,
        o(),
    );
    s.vmap.set(old_vref, Mapped::Pair(lo, hi));
}

// ---------------------------------------------------------------------------
// 128-bit multiply (schoolbook with 32-bit quarters)
// ---------------------------------------------------------------------------

#[allow(clippy::too_many_lines)]
fn leg_mul(s: &mut State, b: &mut Builder, old_vref: ValueRef, a: &Operand, op_b: &Operand) {
    let ann64 = Some(Annotation::Unsigned(64));
    let (a_lo, a_hi) = s.vmap.pair(a.value);
    let (b_lo, b_hi) = s.vmap.pair(op_b.value);

    let c32 = b.iconst(32i64, o());
    let mask32 = b.iconst(0xFFFF_FFFFi64, o());

    // Split a_lo into 32-bit halves.
    let a0 = b.and(
        Operand::annotated(a_lo, Annotation::Unsigned(64)),
        Operand::new(mask32),
        ann64,
        o(),
    );
    let a1 = b.shr(
        Operand::annotated(a_lo, Annotation::Unsigned(64)),
        Operand::new(c32),
        ann64,
        o(),
    );
    let b0 = b.and(
        Operand::annotated(b_lo, Annotation::Unsigned(64)),
        Operand::new(mask32),
        ann64,
        o(),
    );
    let b1 = b.shr(
        Operand::annotated(b_lo, Annotation::Unsigned(64)),
        Operand::new(c32),
        ann64,
        o(),
    );

    // Partial products (each fits in 64 bits).
    let p0 = b.mul(Operand::new(a0), Operand::new(b0), ann64, o());
    let p1 = b.mul(Operand::new(a0), Operand::new(b1), ann64, o());
    let p2 = b.mul(Operand::new(a1), Operand::new(b0), ann64, o());
    let p3 = b.mul(Operand::new(a1), Operand::new(b1), ann64, o());

    // Accumulate middle column: mid = (p0 >> 32) + p1 + p2
    // This sum can overflow 64 bits, so we track carries.
    let p0_hi = b.shr(
        Operand::annotated(p0, Annotation::Unsigned(64)),
        Operand::new(c32),
        ann64,
        o(),
    );
    let mid1 = b.add(Operand::new(p0_hi), Operand::new(p1), ann64, o());
    let carry1 = b.icmp(
        ICmpOp::Lt,
        Operand::annotated(mid1, Annotation::Unsigned(64)),
        Operand::annotated(p1, Annotation::Unsigned(64)),
        o(),
    );
    let carry1_int = b.bool_to_int(Operand::new(carry1), o());
    let mid = b.add(Operand::new(mid1), Operand::new(p2), ann64, o());
    let carry2 = b.icmp(
        ICmpOp::Lt,
        Operand::annotated(mid, Annotation::Unsigned(64)),
        Operand::annotated(p2, Annotation::Unsigned(64)),
        o(),
    );
    let carry2_int = b.bool_to_int(Operand::new(carry2), o());
    let total_carry = b.add(
        Operand::new(carry1_int),
        Operand::new(carry2_int),
        ann64,
        o(),
    );

    // lo = (mid << 32) | (p0 & 0xFFFFFFFF)
    let mid_shifted = b.shl(Operand::new(mid), Operand::new(c32), ann64, o());
    let p0_lo = b.and(Operand::new(p0), Operand::new(mask32), ann64, o());
    let lo = b.or(Operand::new(mid_shifted), Operand::new(p0_lo), ann64, o());

    // hi = (mid >> 32) + (total_carry << 32) + p3 + a_lo*b_hi + a_hi*b_lo
    let mid_hi = b.shr(
        Operand::annotated(mid, Annotation::Unsigned(64)),
        Operand::new(c32),
        ann64,
        o(),
    );
    let carry_shifted = b.shl(Operand::new(total_carry), Operand::new(c32), ann64, o());
    let hi = b.add(
        Operand::new(mid_hi),
        Operand::new(carry_shifted),
        ann64,
        o(),
    );
    let hi = b.add(Operand::new(hi), Operand::new(p3), ann64, o());
    let cross1 = b.mul(Operand::new(a_lo), Operand::new(b_hi), ann64, o());
    let hi = b.add(Operand::new(hi), Operand::new(cross1), ann64, o());
    let cross2 = b.mul(Operand::new(a_hi), Operand::new(b_lo), ann64, o());
    let hi = b.add(Operand::new(hi), Operand::new(cross2), ann64, o());

    s.vmap.set(old_vref, Mapped::Pair(lo, hi));
}

// ---------------------------------------------------------------------------
// 128-bit bitwise (and/or/xor): independent on each half
// ---------------------------------------------------------------------------

fn leg_bitwise(
    s: &mut State,
    b: &mut Builder,
    old_vref: ValueRef,
    a: &Operand,
    op_b: &Operand,
    kind: BitwiseKind,
) {
    let ann64 = Some(Annotation::Unsigned(64));
    let (a_lo, a_hi) = s.vmap.pair(a.value);
    let (b_lo, b_hi) = s.vmap.pair(op_b.value);
    let (lo, hi) = match kind {
        BitwiseKind::And => (
            b.and(Operand::new(a_lo), Operand::new(b_lo), ann64, o()),
            b.and(Operand::new(a_hi), Operand::new(b_hi), ann64, o()),
        ),
        BitwiseKind::Or => (
            b.or(Operand::new(a_lo), Operand::new(b_lo), ann64, o()),
            b.or(Operand::new(a_hi), Operand::new(b_hi), ann64, o()),
        ),
        BitwiseKind::Xor => (
            b.xor(Operand::new(a_lo), Operand::new(b_lo), ann64, o()),
            b.xor(Operand::new(a_hi), Operand::new(b_hi), ann64, o()),
        ),
    };
    s.vmap.set(old_vref, Mapped::Pair(lo, hi));
}

// ---------------------------------------------------------------------------
// 128-bit left shift: if amt >= 64 → (0, a_lo << (amt-64))
//                     else → (a_lo << amt, (a_hi << amt) | (a_lo >> (64-amt)))
// We use select to pick between the two cases.
// ---------------------------------------------------------------------------

fn leg_shl(
    s: &mut State,
    b: &mut Builder,
    old_vref: ValueRef,
    a: &Operand,
    op_b: &Operand,
    _ann: Option<&Annotation>,
) {
    let ann64 = Some(Annotation::Unsigned(64));
    let (a_lo, a_hi) = s.vmap.pair(a.value);
    let amt = s.vmap.one(op_b.value);

    let c0 = b.iconst(0i64, o());
    let c64 = b.iconst(64i64, o());

    // Small shift path: amt < 64
    let lo_small = b.shl(Operand::new(a_lo), Operand::new(amt), ann64, o());
    let hi_shifted = b.shl(Operand::new(a_hi), Operand::new(amt), ann64, o());
    let comp = b.sub(Operand::new(c64), Operand::new(amt), ann64, o());
    let lo_spill = b.shr(
        Operand::annotated(a_lo, Annotation::Unsigned(64)),
        Operand::new(comp),
        ann64,
        o(),
    );
    // When amt=0, comp=64 and x86 masks 64-bit shifts mod 64, so
    // `a_lo >> 64` becomes `a_lo >> 0 = a_lo` instead of 0.
    // Zero out the spill when amt=0.
    let is_nonzero = b.icmp(
        ICmpOp::Ne,
        Operand::annotated(amt, Annotation::Unsigned(64)),
        Operand::new(c0),
        o(),
    );
    let lo_spill_safe = b.select(
        Operand::new(is_nonzero),
        Operand::new(lo_spill),
        Operand::new(c0),
        Type::Int,
        o(),
    );
    let hi_small = b.or(
        Operand::new(hi_shifted),
        Operand::new(lo_spill_safe),
        ann64,
        o(),
    );

    // Large shift path: amt >= 64
    let amt_minus_64 = b.sub(Operand::new(amt), Operand::new(c64), ann64, o());
    let hi_large = b.shl(Operand::new(a_lo), Operand::new(amt_minus_64), ann64, o());

    // Emit is_large immediately before the selects so no arithmetic
    // instructions clobber FLAGS between the icmp and CMOVcc.
    let is_large = b.icmp(
        ICmpOp::Ge,
        Operand::annotated(amt, Annotation::Unsigned(64)),
        Operand::new(c64),
        o(),
    );

    // Select between paths.
    let lo = b.select(
        Operand::new(is_large),
        Operand::new(c0),
        Operand::new(lo_small),
        Type::Int,
        o(),
    );
    let hi = b.select(
        Operand::new(is_large),
        Operand::new(hi_large),
        Operand::new(hi_small),
        Type::Int,
        o(),
    );

    s.vmap.set(old_vref, Mapped::Pair(lo, hi));
}

// ---------------------------------------------------------------------------
// 128-bit right shift (logical or arithmetic based on annotation)
// ---------------------------------------------------------------------------

fn leg_shr(
    s: &mut State,
    b: &mut Builder,
    old_vref: ValueRef,
    a: &Operand,
    op_b: &Operand,
    _ann: Option<&Annotation>,
) {
    let signed = is_signed_128(a.annotation.as_ref());
    let ann64 = Some(Annotation::Unsigned(64));
    let (a_lo, a_hi) = s.vmap.pair(a.value);
    let amt = s.vmap.one(op_b.value);

    let c0 = b.iconst(0i64, o());
    let c64 = b.iconst(64i64, o());

    // For the hi half, use signed or unsigned shift.
    let hi_ann = if signed {
        Annotation::Signed(64)
    } else {
        Annotation::Unsigned(64)
    };

    // Small shift path: amt < 64
    let hi_small = b.shr(
        Operand::annotated(a_hi, hi_ann),
        Operand::new(amt),
        None,
        o(),
    );
    let lo_shifted = b.shr(
        Operand::annotated(a_lo, Annotation::Unsigned(64)),
        Operand::new(amt),
        ann64,
        o(),
    );
    let comp = b.sub(Operand::new(c64), Operand::new(amt), ann64, o());
    let hi_spill = b.shl(Operand::new(a_hi), Operand::new(comp), ann64, o());
    // When amt=0, comp=64 and x86 masks 64-bit shifts mod 64, so
    // `a_hi << 64` becomes `a_hi << 0 = a_hi` instead of 0.
    // Zero out the spill when amt=0.
    let is_nonzero = b.icmp(
        ICmpOp::Ne,
        Operand::annotated(amt, Annotation::Unsigned(64)),
        Operand::new(c0),
        o(),
    );
    let hi_spill_safe = b.select(
        Operand::new(is_nonzero),
        Operand::new(hi_spill),
        Operand::new(c0),
        Type::Int,
        o(),
    );
    let lo_small = b.or(
        Operand::new(lo_shifted),
        Operand::new(hi_spill_safe),
        ann64,
        o(),
    );

    // Large shift path: amt >= 64
    let amt_minus_64 = b.sub(Operand::new(amt), Operand::new(c64), ann64, o());
    let lo_large = b.shr(
        Operand::annotated(a_hi, hi_ann),
        Operand::new(amt_minus_64),
        None,
        o(),
    );
    // hi_large = 0 for unsigned, sign-fill for signed
    let hi_large = if signed {
        let c63 = b.iconst(63i64, o());
        b.shr(
            Operand::annotated(a_hi, Annotation::Signed(64)),
            Operand::new(c63),
            None,
            o(),
        )
    } else {
        c0
    };

    // Emit is_large immediately before the selects so no arithmetic
    // instructions clobber FLAGS between the icmp and CMOVcc.
    let is_large = b.icmp(
        ICmpOp::Ge,
        Operand::annotated(amt, Annotation::Unsigned(64)),
        Operand::new(c64),
        o(),
    );

    let lo = b.select(
        Operand::new(is_large),
        Operand::new(lo_large),
        Operand::new(lo_small),
        Type::Int,
        o(),
    );
    let hi = b.select(
        Operand::new(is_large),
        Operand::new(hi_large),
        Operand::new(hi_small),
        Type::Int,
        o(),
    );

    s.vmap.set(old_vref, Mapped::Pair(lo, hi));
}

// ---------------------------------------------------------------------------
// 128-bit integer comparison
// Compare hi halves first; if equal, compare lo halves (unsigned).
// For signed comparisons, hi uses signed compare, lo always unsigned.
// ---------------------------------------------------------------------------

fn leg_icmp(
    s: &mut State,
    b: &mut Builder,
    old_vref: ValueRef,
    cmp_op: ICmpOp,
    a: &Operand,
    op_b: &Operand,
) {
    let (a_lo, a_hi) = s.vmap.pair(a.value);
    let (b_lo, b_hi) = s.vmap.pair(op_b.value);
    let signed = is_signed_128(a.annotation.as_ref());

    let hi_ann = if signed {
        Annotation::Signed(64)
    } else {
        Annotation::Unsigned(64)
    };
    let lo_ann = Annotation::Unsigned(64);

    let result = match cmp_op {
        ICmpOp::Eq => {
            let hi_eq = b.icmp(ICmpOp::Eq, Operand::new(a_hi), Operand::new(b_hi), o());
            let lo_eq = b.icmp(ICmpOp::Eq, Operand::new(a_lo), Operand::new(b_lo), o());
            // Convert to int, AND, convert back to bool.
            let hi_int = b.bool_to_int(Operand::new(hi_eq), o());
            let lo_int = b.bool_to_int(Operand::new(lo_eq), o());
            let both = b.and(Operand::new(hi_int), Operand::new(lo_int), None, o());
            b.int_to_bool(Operand::new(both), o())
        }
        ICmpOp::Ne => {
            let hi_ne = b.icmp(ICmpOp::Ne, Operand::new(a_hi), Operand::new(b_hi), o());
            let lo_ne = b.icmp(ICmpOp::Ne, Operand::new(a_lo), Operand::new(b_lo), o());
            let hi_int = b.bool_to_int(Operand::new(hi_ne), o());
            let lo_int = b.bool_to_int(Operand::new(lo_ne), o());
            let either = b.or(Operand::new(hi_int), Operand::new(lo_int), None, o());
            b.int_to_bool(Operand::new(either), o())
        }
        ICmpOp::Lt | ICmpOp::Le | ICmpOp::Gt | ICmpOp::Ge => {
            // hi_cmp = a_hi <cmp> b_hi (signed or unsigned)
            let hi_cmp = b.icmp(
                cmp_op,
                Operand::annotated(a_hi, hi_ann),
                Operand::annotated(b_hi, hi_ann),
                o(),
            );
            let hi_eq = b.icmp(ICmpOp::Eq, Operand::new(a_hi), Operand::new(b_hi), o());
            // lo_cmp always unsigned
            let lo_cmp = b.icmp(
                cmp_op,
                Operand::annotated(a_lo, lo_ann),
                Operand::annotated(b_lo, lo_ann),
                o(),
            );
            // result = hi_eq ? lo_cmp : hi_cmp
            b.select(
                Operand::new(hi_eq),
                Operand::new(lo_cmp),
                Operand::new(hi_cmp),
                Type::Bool,
                o(),
            )
        }
    };
    s.vmap.set(old_vref, Mapped::One(result));
}

// ---------------------------------------------------------------------------
// 128-bit load: two 8-byte loads at offset 0 and 8
// ---------------------------------------------------------------------------

fn leg_load_128(s: &mut State, b: &mut Builder, old_vref: ValueRef, ptr: &Operand, mem: &Operand) {
    let ann64 = Some(Annotation::Unsigned(64));
    let p = s.vmap.one(ptr.value);
    let m = s.vmap.one(mem.value);

    let lo = b.load(Operand::new(p), 8, Type::Int, Operand::new(m), ann64, o());
    let c8 = b.iconst(8i64, o());
    let p_hi = b.ptradd(Operand::new(p), Operand::new(c8), 0, o());
    let hi = b.load(
        Operand::new(p_hi),
        8,
        Type::Int,
        Operand::new(lo),
        ann64,
        o(),
    );
    // The second load's mem output is the final mem token; map the primary
    // result (which was the 16-byte load's mem output) to hi's mem.
    s.vmap.set(old_vref, Mapped::Pair(lo, hi));
}

// ---------------------------------------------------------------------------
// 128-bit store: two 8-byte stores at offset 0 and 8
// ---------------------------------------------------------------------------

fn leg_store_128(
    s: &mut State,
    b: &mut Builder,
    old_vref: ValueRef,
    val: &Operand,
    ptr: &Operand,
    mem: &Operand,
) {
    let (v_lo, v_hi) = s.vmap.pair(val.value);
    let p = s.vmap.one(ptr.value);
    let m = s.vmap.one(mem.value);

    let mem1 = b.store(Operand::new(v_lo), Operand::new(p), 8, Operand::new(m), o());
    let c8 = b.iconst(8i64, o());
    let p_hi = b.ptradd(Operand::new(p), Operand::new(c8), 0, o());
    let mem2 = b.store(
        Operand::new(v_hi),
        Operand::new(p_hi),
        8,
        Operand::new(mem1),
        o(),
    );
    s.vmap.set(old_vref, Mapped::One(mem2));
}

// ---------------------------------------------------------------------------
// Sign-extend to 128: lo = original, hi = arithmetic right shift by 63
// ---------------------------------------------------------------------------

fn leg_sext_128(s: &mut State, b: &mut Builder, old_vref: ValueRef, val: &Operand) {
    let lo = s.vmap.one(val.value);
    let c63 = b.iconst(63i64, o());
    let hi = b.shr(
        Operand::annotated(lo, Annotation::Signed(64)),
        Operand::new(c63),
        None,
        o(),
    );
    s.vmap.set(old_vref, Mapped::Pair(lo, hi));
}

// ---------------------------------------------------------------------------
// Zero-extend to 128: lo = original, hi = 0
// ---------------------------------------------------------------------------

fn leg_zext_128(s: &mut State, b: &mut Builder, old_vref: ValueRef, val: &Operand) {
    let lo = s.vmap.one(val.value);
    let hi = b.iconst(0i64, o());
    s.vmap.set(old_vref, Mapped::Pair(lo, hi));
}

// ---------------------------------------------------------------------------
// 128-bit bswap: bswap each half, then swap the halves
// ---------------------------------------------------------------------------

fn leg_bswap_128(s: &mut State, b: &mut Builder, old_vref: ValueRef, val: &Operand) {
    let (v_lo, v_hi) = s.vmap.pair(val.value);
    let new_lo = b.bswap(Operand::new(v_hi), 8, o());
    let new_hi = b.bswap(Operand::new(v_lo), 8, o());
    s.vmap.set(old_vref, Mapped::Pair(new_lo, new_hi));
}

// ---------------------------------------------------------------------------
// 128-bit select: select on each half independently
// ---------------------------------------------------------------------------

fn leg_select_128(
    s: &mut State,
    b: &mut Builder,
    old_vref: ValueRef,
    cond: &Operand,
    tv: &Operand,
    fv: &Operand,
) {
    let c = s.vmap.one(cond.value);
    let (t_lo, t_hi) = s.vmap.pair(tv.value);
    let (f_lo, f_hi) = s.vmap.pair(fv.value);
    let lo = b.select(
        Operand::new(c),
        Operand::new(t_lo),
        Operand::new(f_lo),
        Type::Int,
        o(),
    );
    let hi = b.select(
        Operand::new(c),
        Operand::new(t_hi),
        Operand::new(f_hi),
        Type::Int,
        o(),
    );
    s.vmap.set(old_vref, Mapped::Pair(lo, hi));
}

// ---------------------------------------------------------------------------
// 128-bit bool_to_int: lo = bool_to_int(val), hi = 0
// ---------------------------------------------------------------------------

fn leg_bool_to_int_128(s: &mut State, b: &mut Builder, old_vref: ValueRef, val: &Operand) {
    let v = s.vmap.one(val.value);
    let lo = b.bool_to_int(Operand::new(v), o());
    let hi = b.iconst(0i64, o());
    s.vmap.set(old_vref, Mapped::Pair(lo, hi));
}

// ---------------------------------------------------------------------------
// 128-bit return: lo → RAX (normal return), hi → RDX (via metadata)
// ---------------------------------------------------------------------------

fn leg_ret(
    s: &mut State,
    b: &mut Builder,
    old_vref: ValueRef,
    val: &Option<Operand>,
    mem: &Operand,
) {
    let m = s.vmap.one(mem.value);
    if let Some(rv) = val {
        // If the return value is wide (Pair mapping), split into (lo, hi).
        // Otherwise the value fits in 64 bits — use it as lo with hi = 0.
        let (lo, hi) = if is_wide(s, rv.value) {
            s.vmap.pair(rv.value)
        } else {
            let lo = s.vmap.one(rv.value);
            let hi = b.iconst(0i64, o());
            (lo, hi)
        };
        // Emit a move for the hi half; record it in metadata so isel
        // knows to place it in RDX.
        let hi_idx = b.iconst(0i64, o()); // placeholder; we overwrite below
        let _ = hi_idx;
        // Actually: emit the ret with lo as the return value.
        // The hi half needs to be communicated via ABI metadata.
        // We emit a dummy instruction that isel will recognize as
        // "move hi into RDX before ret".
        let ret_inst = b.ret(
            Some(Operand::annotated(lo, Annotation::Unsigned(64))),
            Operand::new(m),
            o(),
        );
        // Record that this ret's hi value needs to go to RDX.
        let ret_idx = ret_inst.index();
        s.meta.mark_secondary_return_move(ret_idx, hi.index());
        s.vmap.set(old_vref, Mapped::One(ret_inst));
    } else {
        let v = b.ret(None, Operand::new(m), o());
        s.vmap.set(old_vref, Mapped::One(v));
    }
}

// ---------------------------------------------------------------------------
// Call: split 128-bit args, handle 128-bit returns
// ---------------------------------------------------------------------------

#[allow(clippy::too_many_arguments)]
fn leg_call(
    _old: &Function,
    s: &mut State,
    b: &mut Builder,
    old_vref: ValueRef,
    inst: &tuffy_ir::instruction::Instruction,
    callee: &Operand,
    args: &[Operand],
    mem: &Operand,
) {
    let c = remap_op(s, callee);
    let m = remap_op(s, mem);

    // Split 128-bit arguments into two 64-bit args.
    let mut new_args = Vec::new();
    for arg in args {
        if is_wide(s, arg.value) {
            let (lo, hi) = s.vmap.pair(arg.value);
            new_args.push(Operand::annotated(lo, Annotation::Unsigned(64)));
            new_args.push(Operand::annotated(hi, Annotation::Unsigned(64)));
        } else if is_128(arg.annotation.as_ref()) {
            // The value fits in 64 bits (e.g. a small u128 constant) but
            // the callee expects a 128-bit parameter.  Split into (lo, hi=0).
            let lo = remap_op(s, arg);
            let hi = b.iconst(0i64, o());
            new_args.push(Operand::annotated(lo.value, Annotation::Unsigned(64)));
            new_args.push(Operand::annotated(hi, Annotation::Unsigned(64)));
        } else {
            new_args.push(remap_op(s, arg));
        }
    }

    let wide_ret = is_128(inst.result_annotation.as_ref())
        || s.old_meta.wide_return_calls.contains(&old_vref.index());
    let ret_ty = if wide_ret {
        Type::Int
    } else {
        inst.secondary_ty.clone().unwrap_or(Type::Unit)
    };

    let ann = if wide_ret {
        Some(Annotation::Unsigned(64))
    } else {
        inst.result_annotation
    };

    let (mem_out, data_out) = b.call(c, new_args, ret_ty, m, ann, o());
    s.vmap.set(old_vref, Mapped::One(mem_out));

    if wide_ret {
        if let Some(data) = data_out {
            // The call returns lo in RAX (data). We need to capture RDX for hi.
            let call_idx = mem_out.index();
            s.meta.mark_call_secondary_return(call_idx);

            // Emit a placeholder instruction that isel will recognize as
            // "capture RDX after call". We use an iconst(0) as placeholder
            // and record it in metadata.
            let hi_capture = b.iconst(0i64, o());
            let hi_idx = hi_capture.index();
            s.meta.mark_secondary_return_capture(hi_idx, call_idx);

            s.vmap.set(
                ValueRef::inst_secondary_result(old_vref.index()),
                Mapped::Pair(data, hi_capture),
            );
        }
    } else if let Some(data) = data_out {
        let old_sec = ValueRef::inst_secondary_result(old_vref.index());
        s.vmap.set(old_sec, Mapped::One(data));

        // Transfer secondary return (RDX) metadata for non-wide calls.
        // When legalization runs on a function that has i128 values, calls
        // to functions returning 16-byte structs (e.g. fmt::Arguments) also
        // get new instruction indices.  Without transferring the metadata,
        // isel won't know to capture RDX after the call.
        let old_call_idx = old_vref.index();
        if s.old_meta.call_has_ret2.contains(&old_call_idx) {
            let new_call_idx = mem_out.index();
            s.meta.mark_call_secondary_return(new_call_idx);

            // Create a new RDX capture placeholder (same pattern as codegen).
            let rdx_capture = b.iconst(0i64, o());
            s.meta
                .mark_secondary_return_capture(rdx_capture.index(), new_call_idx);

            // Find the old RDX capture instruction for this call and record
            // the mapping so legalize_inst can remap uses of it.
            for (&old_cap_idx, &old_target_call) in &s.old_meta.rdx_captures {
                if old_target_call == old_call_idx {
                    let old_cap_vref = ValueRef::inst_result(old_cap_idx);
                    s.vmap.set(old_cap_vref, Mapped::One(rdx_capture));
                    s.rdx_capture_remap.insert(old_cap_idx, rdx_capture);
                    break;
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Branch argument remapping: split 128-bit args into lo/hi pairs
// ---------------------------------------------------------------------------

fn remap_branch_args(s: &State, args: &[Operand]) -> Vec<Operand> {
    let mut out = Vec::new();
    for arg in args {
        if is_wide(s, arg.value) {
            let (lo, hi) = s.vmap.pair(arg.value);
            out.push(Operand::new(lo));
            out.push(Operand::new(hi));
        } else {
            out.push(remap_op(s, arg));
        }
    }
    out
}

// ---------------------------------------------------------------------------
// Unconditional branch
// ---------------------------------------------------------------------------

fn leg_br(s: &mut State, b: &mut Builder, old_vref: ValueRef, target: BlockRef, args: &[Operand]) {
    let new_target = new_block(s, target);
    let new_args = remap_branch_args(s, args);
    let v = b.br(new_target, new_args, o());
    s.vmap.set(old_vref, Mapped::One(v));
}

// ---------------------------------------------------------------------------
// Conditional branch
// ---------------------------------------------------------------------------

#[allow(clippy::too_many_arguments)]
fn leg_brif(
    s: &mut State,
    b: &mut Builder,
    old_vref: ValueRef,
    cond: &Operand,
    then_blk: BlockRef,
    then_args: &[Operand],
    else_blk: BlockRef,
    else_args: &[Operand],
) {
    let c = remap_op(s, cond);
    let new_then = new_block(s, then_blk);
    let new_else = new_block(s, else_blk);
    let new_then_args = remap_branch_args(s, then_args);
    let new_else_args = remap_branch_args(s, else_args);
    let v = b.brif(c, new_then, new_then_args, new_else, new_else_args, o());
    s.vmap.set(old_vref, Mapped::One(v));
}

// ---------------------------------------------------------------------------
// Continue (loop backedge)
// ---------------------------------------------------------------------------

fn leg_continue(s: &mut State, b: &mut Builder, old_vref: ValueRef, args: &[Operand]) {
    let new_args = remap_branch_args(s, args);
    let v = b.continue_(new_args, o());
    s.vmap.set(old_vref, Mapped::One(v));
}

// ---------------------------------------------------------------------------
// Region yield
// ---------------------------------------------------------------------------

fn leg_region_yield(s: &mut State, b: &mut Builder, old_vref: ValueRef, args: &[Operand]) {
    let new_args = remap_branch_args(s, args);
    let v = b.region_yield(new_args, o());
    s.vmap.set(old_vref, Mapped::One(v));
}
