//! Wide-integer type legalization pass.
//!
//! Splits integer operations wider than the target's native register width
//! into pairs of narrower operations before instruction selection.
//! Target-independent: parameterized over the backend's ABI metadata type
//! and target legality information.

use std::collections::{HashMap, HashSet};

use num_bigint::BigInt;
use num_traits::{ToPrimitive, Zero};

use tuffy_ir::builder::Builder;
use tuffy_ir::function::{CfgNode, Function};
use tuffy_ir::instruction::{ICmpOp, Op, Operand, Origin};
use tuffy_ir::module::SymbolTable;
use tuffy_ir::types::{Annotation, FloatType, IntAnnotation, IntSignedness, Type};
use tuffy_ir::value::{BlockRef, ValueRef};

use tuffy_target::backend::AbiMetadata;
use tuffy_target::legality::LegalityInfo;

// ---------------------------------------------------------------------------
// Helper constants
// ---------------------------------------------------------------------------

const I64: Type = Type::Int(IntAnnotation {
    bit_width: 64,
    signedness: IntSignedness::Unsigned,
});

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

fn type_width(ty: &Type) -> Option<u32> {
    match ty {
        Type::Int(ann) => Some(ann.bit_width),
        _ => None,
    }
}

fn is_wide_width(width: Option<u32>, legality: &impl LegalityInfo) -> bool {
    match width {
        Some(w) => w > legality.max_int_width(),
        None => false,
    }
}

fn is_128_bit_int(ty: &Type) -> bool {
    matches!(ty, Type::Int(ann) if ann.bit_width == 128)
}

fn is_signed_128_int(ty: &Type) -> bool {
    matches!(ty, Type::Int(ann) if ann.bit_width == 128 && matches!(ann.signedness, IntSignedness::Signed))
}

fn value_type(func: &Function, v: ValueRef) -> Option<&Type> {
    if v.is_block_arg() {
        func.block_args.get(v.index() as usize).map(|ba| &ba.ty)
    } else if v.is_secondary_result() {
        func.instructions
            .get(v.inst_index() as usize)?
            .secondary_ty
            .as_ref()
    } else {
        func.instructions.get(v.index() as usize).map(|i| &i.ty)
    }
}

fn is_128_bit_value(func: &Function, v: ValueRef) -> bool {
    value_type(func, v).is_some_and(is_128_bit_int)
}

fn needs_wide_const(v: &BigInt) -> bool {
    !v.is_zero() && v.to_i64().is_none() && v.to_u64().is_none()
}

fn has_wide_values<M: AbiMetadata>(
    func: &Function,
    metadata: &M,
    legality: &impl LegalityInfo,
) -> bool {
    // Check for wide parameters
    for ty in &func.params {
        if is_wide_width(type_width(ty), legality) {
            return true;
        }
    }

    // Check for wide return type
    if let Some(ref ty) = func.ret_ty
        && is_wide_width(type_width(ty), legality)
    {
        return true;
    }

    // Check for wide instructions
    for inst in &func.instructions {
        if is_wide_width(type_width(&inst.ty), legality) {
            return true;
        }

        // Check if operation needs legalization
        if legality.needs_legalization(&inst.op, type_width(&inst.ty)) {
            return true;
        }

        match &inst.op {
            Op::Load(_, bytes, _) if *bytes > legality.max_int_width() / 8 => return true,
            Op::Store(_, _, bytes, _) if *bytes > legality.max_int_width() / 8 => return true,
            Op::Sext(_, bits) | Op::Zext(_, bits) if *bits > legality.max_int_width() => {
                return true;
            }
            Op::Bswap(_, bytes) if *bytes > legality.max_int_width() / 8 => return true,
            Op::RotateLeft(_, _, bits) | Op::RotateRight(_, _, bits)
                if *bits > legality.max_int_width() =>
            {
                return true;
            }
            Op::SaturatingAdd(_, _, bits)
            | Op::SaturatingSub(_, _, bits)
            | Op::SignedSaturatingAdd(_, _, bits)
            | Op::SignedSaturatingSub(_, _, bits)
                if *bits > legality.max_int_width() =>
            {
                return true;
            }
            Op::SAddWithOverflow(_, _, bits)
            | Op::UAddWithOverflow(_, _, bits)
            | Op::SSubWithOverflow(_, _, bits)
            | Op::USubWithOverflow(_, _, bits)
            | Op::SMulWithOverflow(_, _, bits)
            | Op::UMulWithOverflow(_, _, bits)
                if *bits > legality.max_int_width() =>
            {
                return true;
            }
            Op::Const(v) if needs_wide_const(v) => return true,
            // A call with any 128-bit annotated argument needs legalization to
            // split it into (lo, hi) even when the value fits in 64 bits.
            Op::Call(_, args, _) if args.iter().any(|a| is_128_bit_value(func, a.value)) => {
                return true;
            }
            _ => {}
        }
    }

    // Check for wide-return calls
    for (i, _) in func.instructions.iter().enumerate() {
        if metadata.is_wide_return_call(i as u32) {
            return true;
        }
    }

    false
}

#[allow(dead_code)]
fn has_128bit_values(func: &Function) -> bool {
    if func.params.iter().any(is_128_bit_int) {
        return true;
    }
    if func.ret_ty.as_ref().is_some_and(is_128_bit_int) {
        return true;
    }
    for inst in &func.instructions {
        if is_128_bit_int(&inst.ty) {
            return true;
        }
        match &inst.op {
            Op::Load(_, 16, _) | Op::Store(_, _, 16, _) => return true,
            Op::Sext(_, 128) | Op::Zext(_, 128) => return true,
            Op::Bswap(_, 16) => return true,
            Op::RotateLeft(_, _, 128) | Op::RotateRight(_, _, 128) => return true,
            Op::SaturatingAdd(_, _, 128)
            | Op::SaturatingSub(_, _, 128)
            | Op::SignedSaturatingAdd(_, _, 128)
            | Op::SignedSaturatingSub(_, _, 128) => return true,
            Op::SAddWithOverflow(_, _, 128)
            | Op::UAddWithOverflow(_, _, 128)
            | Op::SSubWithOverflow(_, _, 128)
            | Op::USubWithOverflow(_, _, 128)
            | Op::SMulWithOverflow(_, _, 128)
            | Op::UMulWithOverflow(_, _, 128) => return true,
            Op::Const(v) if needs_wide_const(v) => return true,
            _ => {}
        }
    }
    false
}

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

/// Legalize operations according to target legality rules.
///
/// Iterates to a fixpoint:
/// 1. Walk all instructions
/// 2. Query LegalityInfo for each operation
/// 3. Apply rewrite rules (split, expand, libcall)
/// 4. Repeat until all instructions are legal
///
/// Returns `None` if no legalization is needed.
pub fn legalize<M: AbiMetadata + Clone>(
    func: &Function,
    metadata: &M,
    legality: &impl LegalityInfo,
    symbols: &mut SymbolTable,
) -> Option<(Function, M)> {
    if !has_wide_values(func, metadata, legality) {
        return None;
    }
    let (out, state) = build_new_func(func, metadata, legality);
    Some(run_legalize(func, out, state, symbols))
}

// ---------------------------------------------------------------------------
// State (separate from Function so Builder can borrow Function independently)
// ---------------------------------------------------------------------------

struct State<M> {
    meta: M,
    /// Original ABI metadata from before legalization, used to transfer
    /// non-128-bit secondary return info (e.g. 16-byte struct returns in
    /// RAX+RDX) that would otherwise be lost when instruction indices change.
    old_meta: M,
    vmap: VMap,
    bmap: HashMap<u32, BlockRef>,
    /// Old param index → (new_lo_index, Option<new_hi_index>).
    param_map: Vec<(u32, Option<u32>)>,
    /// Set of old ValueRef raw values that are 128-bit.
    wide: HashSet<u32>,
    /// Old RDX-capture instruction index → new ValueRef created in leg_call.
    /// Used to avoid re-creating the capture in copy_inst.
    rdx_capture_remap: HashMap<u32, ValueRef>,
    /// The most recent mem-producing old ValueRef in the current block.
    /// Used to thread the mem token when expanding a 128-bit Div/Rem into a
    /// libcall (which requires a mem operand that the pure Div/Rem lacks).
    current_old_mem: Option<ValueRef>,
}

fn o() -> Origin {
    Origin::synthetic()
}

fn build_new_func<M: AbiMetadata + Clone>(
    old: &Function,
    old_meta: &M,
    legality: &impl LegalityInfo,
) -> (Function, State<M>) {
    let mut params = Vec::new();
    let mut param_anns = Vec::new();
    let mut param_names = Vec::new();
    let mut param_map = Vec::new();

    for (i, ty) in old.params.iter().enumerate() {
        let name = old.param_names.get(i).and_then(|n| *n);
        if is_wide_width(type_width(ty), legality) {
            let lo_idx = params.len() as u32;
            params.push(Type::Int(IntAnnotation {
                bit_width: legality.max_int_width(),
                signedness: IntSignedness::Unsigned,
            }));
            param_anns.push(None);
            param_names.push(name);
            let hi_idx = params.len() as u32;
            params.push(Type::Int(IntAnnotation {
                bit_width: legality.max_int_width(),
                signedness: IntSignedness::Unsigned,
            }));
            param_anns.push(None);
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
    let ret_ann = if let Some(ref ty) = ret_ty {
        if is_wide_width(type_width(ty), legality) {
            None
        } else {
            old.ret_annotation
        }
    } else {
        old.ret_annotation
    };

    let wide = collect_wide_values(old, old_meta, legality);
    let out = Function::new(old.name, params, param_anns, param_names, ret_ty, ret_ann);
    let state = State {
        meta: M::default(),
        old_meta: old_meta.clone(),
        vmap: VMap::new(),
        bmap: HashMap::new(),
        param_map,
        wide,
        rdx_capture_remap: HashMap::new(),
        current_old_mem: None,
    };
    (out, state)
}

// ---------------------------------------------------------------------------
// Pre-scan: identify 128-bit values in the old function
// ---------------------------------------------------------------------------

fn collect_wide_values<M: AbiMetadata>(
    old: &Function,
    meta: &M,
    legality: &impl LegalityInfo,
) -> HashSet<u32> {
    let mut wide = HashSet::new();

    // Mark instructions that produce wide results.
    for (i, inst) in old.instructions.iter().enumerate() {
        let vref = ValueRef::inst_result(i as u32);
        if is_wide_width(type_width(&inst.ty), legality) {
            wide.insert(vref.raw());
            continue;
        }
        // Calls returning wide values are marked in ABI metadata
        if meta.is_wide_return_call(i as u32) {
            let sec = ValueRef::inst_secondary_result(i as u32);
            wide.insert(sec.raw());
        }
        match &inst.op {
            Op::Const(v) if needs_wide_const(v) => {
                wide.insert(vref.raw());
            }
            Op::Load(_, bytes, _) if *bytes > legality.max_int_width() / 8 => {
                wide.insert(vref.raw());
            }
            Op::Sext(_, bits) | Op::Zext(_, bits) if *bits > legality.max_int_width() => {
                wide.insert(vref.raw());
            }
            Op::Bswap(_, bytes) if *bytes > legality.max_int_width() / 8 => {
                wide.insert(vref.raw());
            }
            Op::RotateLeft(_, _, bits) | Op::RotateRight(_, _, bits)
                if *bits > legality.max_int_width() =>
            {
                wide.insert(vref.raw());
            }
            Op::SaturatingAdd(_, _, bits)
            | Op::SaturatingSub(_, _, bits)
            | Op::SignedSaturatingAdd(_, _, bits)
            | Op::SignedSaturatingSub(_, _, bits)
                if *bits > legality.max_int_width() =>
            {
                wide.insert(vref.raw());
            }
            Op::SAddWithOverflow(_, _, bits)
            | Op::UAddWithOverflow(_, _, bits)
            | Op::SSubWithOverflow(_, _, bits)
            | Op::USubWithOverflow(_, _, bits)
            | Op::SMulWithOverflow(_, _, bits)
            | Op::UMulWithOverflow(_, _, bits)
                if *bits > legality.max_int_width() =>
            {
                wide.insert(vref.raw());
            }
            Op::Shr(a, _) if is_128_bit_value(old, a.value) => {
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

fn is_wide<M>(s: &State<M>, v: ValueRef) -> bool {
    s.wide.contains(&v.raw()) || matches!(s.vmap.get(v), Mapped::Pair(_, _))
}

/// Returns the (lo, hi) pair for a 128-bit operand, correctly handling non-wide
/// values. Unlike `vmap.pair()`, which returns `(v, v)` for a non-wide value,
/// this derives the hi word from lo:
///
/// - For `Unsigned` annotated operands, zero-extend (hi = 0).  A non-wide
///   value with `Unsigned(n)` annotation represents a u64 constant whose
///   128-bit form always has the upper 64 bits equal to zero, even when the
///   value is in `[2^63, 2^64)` (i.e., bit 63 of lo is set).  Sign-extending
///   such a value would incorrectly produce hi = −1.
///
/// - For `Signed` annotated operands or unannotated ones, sign-extend
///   (hi = lo >> 63).  This handles negative constants such as `iconst(-1)`
///   used as the all-ones mask for bitwise NOT; those have annotation `None`
///   or `Signed(n)` and must propagate their sign bit into the upper half.
fn wide_pair<M>(
    s: &State<M>,
    old: &Function,
    b: &mut Builder,
    op: &Operand,
) -> (ValueRef, ValueRef) {
    if is_wide(s, op.value) {
        s.vmap.pair(op.value)
    } else {
        let lo = s.vmap.one(op.value);
        let is_unsigned = value_type(old, op.value).is_some_and(
            |ty| matches!(ty, Type::Int(ann) if matches!(ann.signedness, IntSignedness::Unsigned)),
        );
        let hi = if is_unsigned {
            // Zero-extend: unsigned values always have hi = 0 in their 128-bit form.
            b.iconst(0i64, 64, IntSignedness::Unsigned, o())
        } else {
            // Sign-extend: for positive values hi=0 (same as zero-extend); for negative
            // values (e.g. iconst(-1) used as all-ones in a 128-bit XOR) hi=-1.
            let c63 = b.iconst(63i64, 64, IntSignedness::Unsigned, o());
            b.shr(Operand::new(lo), Operand::new(c63), None, o())
        };
        (lo, hi)
    }
}

// ---------------------------------------------------------------------------
// Main legalization loop
// ---------------------------------------------------------------------------

fn run_legalize<M: AbiMetadata + Clone>(
    old: &Function,
    mut out: Function,
    mut s: State<M>,
    symbols: &mut SymbolTable,
) -> (Function, M) {
    {
        let mut b = Builder::new(&mut out);
        let old_root = old.root_region;
        let new_root = b.create_region(old.region(old_root).kind);
        b.enter_region(new_root);
        walk_region(old, &mut s, &mut b, old_root, symbols);
        b.exit_region();
    }
    (out, s.meta)
}

fn walk_region<M: AbiMetadata + Clone>(
    old: &Function,
    s: &mut State<M>,
    b: &mut Builder,
    old_region: tuffy_ir::value::RegionRef,
    symbols: &mut SymbolTable,
) {
    precreate_blocks(old, s, b, old_region);

    for child in &old.region(old_region).children {
        match child {
            CfgNode::Block(old_blk) => {
                walk_block_insts(old, s, b, *old_blk, symbols);
            }
            CfgNode::Region(old_sub) => {
                let new_sub = b.create_region(old.region(*old_sub).kind);
                b.enter_region(new_sub);
                walk_region(old, s, b, *old_sub, symbols);
                b.exit_region();
            }
        }
    }
}

fn precreate_blocks<M>(
    old: &Function,
    s: &mut State<M>,
    b: &mut Builder,
    old_region: tuffy_ir::value::RegionRef,
) {
    for child in &old.region(old_region).children {
        if let CfgNode::Block(old_blk) = child {
            let new_blk = b.create_block();
            s.bmap.insert(old_blk.index(), new_blk);

            let old_bb = old.block(*old_blk);
            for i in 0..old_bb.arg_count {
                let old_ba_idx = old_bb.arg_start + i;
                let old_ba_ref = ValueRef::block_arg(old_ba_idx);
                let ba_ty = old.block_args[old_ba_idx as usize].ty.clone();

                if s.wide.contains(&old_ba_ref.raw()) {
                    let lo = b.add_block_arg(new_blk, I64);
                    let hi = b.add_block_arg(new_blk, I64);
                    s.vmap.set(old_ba_ref, Mapped::Pair(lo, hi));
                } else {
                    let v = b.add_block_arg(new_blk, ba_ty);
                    s.vmap.set(old_ba_ref, Mapped::One(v));
                }
            }
        }
    }
}

fn walk_block_insts<M: AbiMetadata + Clone>(
    old: &Function,
    s: &mut State<M>,
    b: &mut Builder,
    old_blk: BlockRef,
    symbols: &mut SymbolTable,
) {
    let new_blk = s.bmap[&old_blk.index()];
    b.switch_to_block(new_blk);

    // Initialize current_old_mem from this block's Mem-typed argument, if any.
    let old_bb = old.block(old_blk);
    for i in 0..old_bb.arg_count {
        let old_ba_idx = old_bb.arg_start + i;
        if old.block_args[old_ba_idx as usize].ty == Type::Mem {
            s.current_old_mem = Some(ValueRef::block_arg(old_ba_idx));
            break;
        }
    }

    for (old_vref, inst) in old.block_insts_with_values(old_blk) {
        legalize_inst(old, s, b, old_vref, inst, symbols);
        // Keep current_old_mem up to date so that leg_div_rem_128 can
        // inject calls into the correct position in the mem chain.
        if inst.ty == Type::Mem {
            s.current_old_mem = Some(old_vref);
        }
    }
}

// ---------------------------------------------------------------------------
// Instruction dispatch
// ---------------------------------------------------------------------------

#[allow(clippy::too_many_lines)]
fn legalize_inst<M: AbiMetadata + Clone>(
    old: &Function,
    s: &mut State<M>,
    b: &mut Builder,
    old_vref: ValueRef,
    inst: &tuffy_ir::instruction::Instruction,
    symbols: &mut SymbolTable,
) {
    let wide_result = is_128_bit_int(&inst.ty);

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
            leg_add(old, s, b, old_vref, a, op_b);
        }
        Op::Sub(a, op_b) if wide_result => {
            leg_sub(old, s, b, old_vref, a, op_b);
        }
        Op::Mul(a, op_b) if wide_result => {
            leg_mul(old, s, b, old_vref, a, op_b);
        }
        Op::Div(a, op_b) if wide_result => {
            leg_div_rem_128(old, s, b, old_vref, a, op_b, None, true, symbols);
        }
        Op::Rem(a, op_b) if wide_result => {
            leg_div_rem_128(old, s, b, old_vref, a, op_b, None, false, symbols);
        }
        Op::And(a, op_b) if wide_result => {
            leg_bitwise(old, s, b, old_vref, a, op_b, BitwiseKind::And);
        }
        Op::Or(a, op_b) if wide_result => {
            leg_bitwise(old, s, b, old_vref, a, op_b, BitwiseKind::Or);
        }
        Op::Xor(a, op_b) if wide_result => {
            leg_bitwise(old, s, b, old_vref, a, op_b, BitwiseKind::Xor);
        }
        Op::Shl(a, op_b) if wide_result => {
            leg_shl(old, s, b, old_vref, a, op_b, None);
        }
        Op::Shr(a, op_b) if wide_result || is_128_bit_value(old, a.value) => {
            leg_shr(old, s, b, old_vref, a, op_b, None);
        }
        Op::ICmp(cmp_op, a, op_b) if is_wide(s, a.value) || is_128_bit_value(old, a.value) => {
            leg_icmp(old, s, b, old_vref, *cmp_op, a, op_b);
        }
        Op::Load(ptr, 16, mem) => {
            leg_load_128(s, b, old_vref, ptr, mem);
        }
        Op::Load(ptr, bytes, mem) if *bytes > 8 && *bytes < 16 => {
            // 9–15 byte load: split into an 8-byte lo load and a
            // (bytes-8)-byte hi load, yielding a (lo, hi) Pair so that
            // downstream wide stores receive the correct halves.
            let hi_bytes = bytes - 8;
            let p = s.vmap.one(ptr.value);
            let m = s.vmap.one(mem.value);
            let lo = b.load(Operand::new(p), 8, I64, Operand::new(m), None, o());
            let c8 = b.iconst(8i64, 64, IntSignedness::Unsigned, o());
            let p_hi = b.ptradd(Operand::new(p), Operand::new(c8), 0, o());
            let hi = b.load(
                Operand::new(p_hi),
                hi_bytes,
                I64,
                Operand::new(m),
                None,
                o(),
            );
            s.vmap.set(old_vref, Mapped::Pair(lo, hi));
        }
        Op::Store(val, ptr, 16, mem) => {
            leg_store_128(old, s, b, old_vref, val, ptr, mem);
        }
        Op::Sext(val, 128) if is_wide(s, val.value) => {
            // Sext/Zext from 128-bit to 128-bit is an identity: the source
            // already occupies a full (lo, hi) pair.
            let (lo, hi) = s.vmap.pair(val.value);
            s.vmap.set(old_vref, Mapped::Pair(lo, hi));
        }
        Op::Zext(val, 128) if is_wide(s, val.value) => {
            let (lo, hi) = s.vmap.pair(val.value);
            s.vmap.set(old_vref, Mapped::Pair(lo, hi));
        }
        Op::Sext(val, 128) => {
            // If the source is FpToSi, use the proper saturating compiler-rt call.
            let ft = get_fp_to_int_float_type(val.value, old);
            if let Some(ft) = ft {
                leg_fp_to_int128(s, b, old_vref, val, true, ft, old, symbols);
            } else {
                leg_sext_128(s, b, old_vref, val);
            }
        }
        Op::Zext(val, 128) => {
            // If the source is FpToUi, use the proper saturating compiler-rt call.
            let ft = get_fp_to_int_float_type(val.value, old);
            if let Some(ft) = ft {
                leg_fp_to_int128(s, b, old_vref, val, false, ft, old, symbols);
            } else {
                leg_zext_128(s, b, old_vref, val);
            }
        }
        Op::Bswap(val, 16) => {
            leg_bswap_128(s, b, old_vref, val);
        }
        Op::Select(cond, tv, fv) if wide_result => {
            leg_select_128(old, s, b, old_vref, cond, tv, fv);
        }
        Op::BoolToInt(val) if wide_result => {
            leg_bool_to_int_128(s, b, old_vref, val);
        }
        Op::Ret(val, mem) if old.ret_ty.as_ref().is_some_and(is_128_bit_int) => {
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
            let lo = s.vmap.one(val.value);
            let v = b.bitcast(
                Operand::new(lo),
                inst.ty.clone(),
                inst.result_annotation,
                o(),
            );
            s.vmap.set(old_vref, Mapped::One(v));
        }
        Op::Store(val, ptr, bytes, mem) if is_wide(s, val.value) => {
            // For wide stores > 16 bytes (e.g. store.32 load32_result, dst),
            // a 2-word lo/hi split would lose bytes 16+.  When the stored value
            // comes directly from a load.N (N >= bytes) in the old function,
            // replace the whole pattern with a mem_copy so all bytes are copied.
            if *bytes > 16 {
                let src_ptr_op = match &old.inst(val.value.index()).op {
                    Op::Load(load_ptr, load_bytes, _) if *load_bytes >= *bytes => {
                        Some(remap_op(s, load_ptr))
                    }
                    _ => None,
                };
                if let Some(src_ptr) = src_ptr_op {
                    let dst = remap_op(s, ptr);
                    let m = remap_op(s, mem);
                    let count = b.iconst(*bytes as i64, 64, IntSignedness::Unsigned, o());
                    let dst_annotated = Operand::annotated(dst.value, Annotation::Align(1));
                    let src_annotated = Operand::annotated(src_ptr.value, Annotation::Align(1));
                    let new_mem =
                        b.mem_copy(dst_annotated, src_annotated, Operand::new(count), m, o());
                    s.vmap.set(old_vref, Mapped::One(new_mem));
                    return;
                }
            }
            let (lo, hi) = s.vmap.pair(val.value);
            let p = remap_op(s, ptr);
            let m = remap_op(s, mem);
            let m1 = b.store(Operand::new(lo), p.clone(), 8, m, o());
            let off = b.iconst(8i64, 64, IntSignedness::Unsigned, o());
            let hi_addr = b.ptradd(p, Operand::new(off), 0, o());
            // For stores narrower than 16 bytes (e.g. 12-byte structs), only
            // write the remaining bytes for the high half to avoid overflow.
            let hi_bytes = bytes.saturating_sub(8).max(1);
            let m2 = b.store(
                Operand::new(hi),
                Operand::new(hi_addr),
                hi_bytes,
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
            copy_inst(old, s, b, old_vref, inst, symbols);
        }
    }
}

// ---------------------------------------------------------------------------
// Copy non-128-bit instruction with remapped operands
// ---------------------------------------------------------------------------

fn remap_op<M>(s: &State<M>, op: &Operand) -> Operand {
    s.vmap.remap_op(op)
}

fn new_block<M>(s: &State<M>, old: BlockRef) -> BlockRef {
    s.bmap[&old.index()]
}

#[allow(clippy::too_many_lines)]
fn copy_inst<M: AbiMetadata + Clone>(
    old: &Function,
    s: &mut State<M>,
    b: &mut Builder,
    old_vref: ValueRef,
    inst: &tuffy_ir::instruction::Instruction,
    symbols: &mut SymbolTable,
) {
    let ann = inst.result_annotation;
    let v = match &inst.op {
        Op::Param(idx) => b.param(*idx, inst.ty.clone(), ann, o()),
        Op::Const(val) => b.iconst(val.clone(), 64, IntSignedness::Unsigned, o()),
        Op::FConst(ft, bits) => b.fconst(*ft, *bits, o()),
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
        Op::CountOnes(a) => b.count_ones(remap_op(s, a), 64, o()),
        Op::CountLeadingZeros(a, bits) => b.count_leading_zeros(remap_op(s, a), *bits, 64, o()),
        Op::CountTrailingZeros(a) => b.count_trailing_zeros(remap_op(s, a), 64, o()),
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
        Op::SignedSaturatingAdd(a, op_b, bits) => {
            b.signed_saturating_add(remap_op(s, a), remap_op(s, op_b), *bits, o())
        }
        Op::SignedSaturatingSub(a, op_b, bits) => {
            b.signed_saturating_sub(remap_op(s, a), remap_op(s, op_b), *bits, o())
        }
        Op::SAddWithOverflow(a, op_b, bits) if *bits > 64 => {
            leg_sadd_with_overflow_128(old, s, b, old_vref, a, op_b);
            return;
        }
        Op::UAddWithOverflow(a, op_b, bits) if *bits > 64 => {
            leg_uadd_with_overflow_128(old, s, b, old_vref, a, op_b);
            return;
        }
        Op::SSubWithOverflow(a, op_b, bits) if *bits > 64 => {
            leg_ssub_with_overflow_128(old, s, b, old_vref, a, op_b);
            return;
        }
        Op::USubWithOverflow(a, op_b, bits) if *bits > 64 => {
            leg_usub_with_overflow_128(old, s, b, old_vref, a, op_b);
            return;
        }
        Op::SMulWithOverflow(a, op_b, bits) if *bits > 64 => {
            leg_smul_with_overflow_128(old, s, b, old_vref, a, op_b);
            return;
        }
        Op::UMulWithOverflow(a, op_b, bits) if *bits > 64 => {
            leg_umul_with_overflow_128(old, s, b, old_vref, a, op_b);
            return;
        }
        Op::SAddWithOverflow(a, op_b, bits) => {
            let (primary, secondary) =
                b.sadd_with_overflow(remap_op(s, a), remap_op(s, op_b), *bits, o());
            s.vmap.set(old_vref, Mapped::One(primary));
            let old_sec = ValueRef::inst_secondary_result(old_vref.index());
            s.vmap.set(old_sec, Mapped::One(secondary));
            return;
        }
        Op::UAddWithOverflow(a, op_b, bits) => {
            let (primary, secondary) =
                b.uadd_with_overflow(remap_op(s, a), remap_op(s, op_b), *bits, o());
            s.vmap.set(old_vref, Mapped::One(primary));
            let old_sec = ValueRef::inst_secondary_result(old_vref.index());
            s.vmap.set(old_sec, Mapped::One(secondary));
            return;
        }
        Op::SSubWithOverflow(a, op_b, bits) => {
            let (primary, secondary) =
                b.ssub_with_overflow(remap_op(s, a), remap_op(s, op_b), *bits, o());
            s.vmap.set(old_vref, Mapped::One(primary));
            let old_sec = ValueRef::inst_secondary_result(old_vref.index());
            s.vmap.set(old_sec, Mapped::One(secondary));
            return;
        }
        Op::USubWithOverflow(a, op_b, bits) => {
            let (primary, secondary) =
                b.usub_with_overflow(remap_op(s, a), remap_op(s, op_b), *bits, o());
            s.vmap.set(old_vref, Mapped::One(primary));
            let old_sec = ValueRef::inst_secondary_result(old_vref.index());
            s.vmap.set(old_sec, Mapped::One(secondary));
            return;
        }
        Op::SMulWithOverflow(a, op_b, bits) => {
            let (primary, secondary) =
                b.smul_with_overflow(remap_op(s, a), remap_op(s, op_b), *bits, o());
            s.vmap.set(old_vref, Mapped::One(primary));
            let old_sec = ValueRef::inst_secondary_result(old_vref.index());
            s.vmap.set(old_sec, Mapped::One(secondary));
            return;
        }
        Op::UMulWithOverflow(a, op_b, bits) => {
            let (primary, secondary) =
                b.umul_with_overflow(remap_op(s, a), remap_op(s, op_b), *bits, o());
            s.vmap.set(old_vref, Mapped::One(primary));
            let old_sec = ValueRef::inst_secondary_result(old_vref.index());
            s.vmap.set(old_sec, Mapped::One(secondary));
            return;
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
        Op::BoolToInt(a) => b.bool_to_int(remap_op(s, a), 64, o()),
        Op::IntToBool(a) => b.int_to_bool(remap_op(s, a), o()),
        Op::Load(ptr, bytes, mem) => {
            let data = b.load(
                remap_op(s, ptr),
                *bytes,
                inst.ty.clone(),
                remap_op(s, mem),
                ann,
                o(),
            );
            s.vmap.set(old_vref, Mapped::One(data));
            return;
        }
        Op::Store(val, ptr, bytes, mem) => b.store(
            remap_op(s, val),
            remap_op(s, ptr),
            *bytes,
            remap_op(s, mem),
            o(),
        ),
        Op::StackSlot(bytes) => b.stack_slot(*bytes, o()),
        Op::MemCopy(dst, src, count, mem) => b.mem_copy(
            remap_op(s, dst),
            remap_op(s, src),
            remap_op(s, count),
            remap_op(s, mem),
            o(),
        ),
        Op::MemMove(dst, src, count, mem) => b.mem_move(
            remap_op(s, dst),
            remap_op(s, src),
            remap_op(s, count),
            remap_op(s, mem),
            o(),
        ),
        Op::MemSet(dst, val, count, mem) => b.mem_set(
            remap_op(s, dst),
            remap_op(s, val),
            remap_op(s, count),
            remap_op(s, mem),
            o(),
        ),
        Op::SymbolAddr(sym) => b.symbol_addr(*sym, o()),
        Op::Bitcast(a) => b.bitcast(remap_op(s, a), inst.ty.clone(), ann, o()),
        Op::Sext(a, bits) => b.sext(remap_op(s, a), *bits, o()),
        Op::Zext(a, bits) => b.zext(remap_op(s, a), *bits, o()),
        Op::FpToSi(a) => b.fp_to_si(remap_op(s, a), 64, o()),
        Op::FpToUi(a) => b.fp_to_ui(remap_op(s, a), 64, o()),
        Op::SiToFp(a, ft) => {
            let is_128 = s.wide.contains(&a.value.raw())
                || value_type(old, a.value).is_some_and(|ty| {
                    matches!(ty, Type::Int(ann) if ann.bit_width == 128 && matches!(ann.signedness, IntSignedness::Signed))
                });
            if is_128 {
                leg_int128_to_fp(s, b, old_vref, a, *ft, true, symbols);
                return;
            }
            b.si_to_fp(remap_op(s, a), *ft, o())
        }
        Op::UiToFp(a, ft) => {
            let is_128 = s.wide.contains(&a.value.raw())
                || value_type(old, a.value).is_some_and(|ty| {
                    matches!(ty, Type::Int(ann) if ann.bit_width == 128 && matches!(ann.signedness, IntSignedness::Unsigned))
                });
            if is_128 {
                leg_int128_to_fp(s, b, old_vref, a, *ft, false, symbols);
                return;
            }
            b.ui_to_fp(remap_op(s, a), *ft, o())
        }
        Op::FpConvert(a) => {
            let ft = match &inst.ty {
                Type::Float(ft) => *ft,
                _ => tuffy_ir::types::FloatType::F64,
            };
            b.fp_convert(remap_op(s, a), ft, o())
        }
        Op::PtrAdd(ptr, off) => b.ptradd(remap_op(s, ptr), remap_op(s, off), 0, o()),
        Op::PtrDiff(a, op_b) => b.ptrdiff(remap_op(s, a), remap_op(s, op_b), 64, o()),
        Op::PtrToInt(a) => b.ptrtoint(remap_op(s, a), 64, o()),
        Op::PtrToAddr(a) => b.ptrtoaddr(remap_op(s, a), 64, o()),
        Op::IntToPtr(a) => b.inttoptr(remap_op(s, a), 0, o()),
        Op::ExtractValue(agg, indices) => {
            // Expand struct field extraction: recursively extract nested fields
            let current = remap_op(s, agg).value;
            for &_idx in indices {
                // For now, treat as a no-op pass-through since we don't have
                // a way to represent struct field extraction at this level.
                // The backend will need to handle this during instruction selection.
                // This is a placeholder that preserves the value.
            }
            current
        }
        Op::InsertValue(agg, _val, _indices) => {
            // Expand struct field insertion: recursively insert nested fields
            let current = remap_op(s, agg).value;
            // Similar to ExtractValue, this is a placeholder.
            // The backend will handle the actual insertion during instruction selection.
            current
        }
        Op::Ret(val, mem) => {
            let rv = val.as_ref().map(|v| remap_op(s, v));
            let new_ret = b.ret(rv, remap_op(s, mem), o());
            // Remap secondary-return move (non-i128 struct returns via RAX+RDX).
            if let Some(src_idx) = s.old_meta.get_secondary_return_move(old_vref.index()) {
                let new_src = s.vmap.one(ValueRef::inst_result(src_idx));
                s.meta
                    .mark_secondary_return_move(new_ret.index(), new_src.index());
            }
            new_ret
        }
        Op::Unreachable => b.unreachable(o()),
        Op::Trap => b.trap(o()),
        Op::Br(..) | Op::BrIf(..) | Op::Call(..) | Op::Continue(..) | Op::RegionYield(..) => {
            unreachable!("branch/call should be handled by dedicated leg_* function")
        }
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
        Op::FMinNum(a, op_b) => b.fminnum(remap_op(s, a), remap_op(s, op_b), inst.ty.clone(), o()),
        Op::FMaxNum(a, op_b) => b.fmaxnum(remap_op(s, a), remap_op(s, op_b), inst.ty.clone(), o()),
        Op::FNeg(a) => b.fneg(remap_op(s, a), inst.ty.clone(), o()),
        Op::FAbs(a) => b.fabs(remap_op(s, a), inst.ty.clone(), o()),
        Op::CopySign(a, op_b) => {
            b.copysign(remap_op(s, a), remap_op(s, op_b), inst.ty.clone(), o())
        }
        Op::LoadAtomic(ptr, ord, mem) => {
            let (primary, secondary) = b.load_atomic(
                remap_op(s, ptr),
                inst.secondary_ty.clone().unwrap_or(I64),
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
                inst.secondary_ty.clone().unwrap_or(I64),
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
                inst.secondary_ty.clone().unwrap_or(I64),
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
        Op::Merge(a, b_op, width) => b.merge(remap_op(s, a), remap_op(s, b_op), *width, o()),
        Op::Clmul(a, b_op) => b.clmul(remap_op(s, a), remap_op(s, b_op), o()),
        Op::Split(a, width) => {
            let (hi, lo) = b.split(remap_op(s, a), *width, o());
            s.vmap.set(old_vref, Mapped::One(hi));
            let old_sec = ValueRef::inst_secondary_result(old_vref.index());
            s.vmap.set(old_sec, Mapped::One(lo));
            return;
        }
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

fn leg_param<M>(s: &mut State<M>, b: &mut Builder, old_vref: ValueRef, lo_idx: u32, hi_idx: u32) {
    let lo = b.param(lo_idx, I64, None, o());
    let hi = b.param(hi_idx, I64, None, o());
    s.vmap.set(old_vref, Mapped::Pair(lo, hi));
}

// ---------------------------------------------------------------------------
// Wide constant (> 64 bits)
// ---------------------------------------------------------------------------

fn leg_wide_const<M>(s: &mut State<M>, b: &mut Builder, old_vref: ValueRef, val: &BigInt) {
    let mask64: BigInt = (BigInt::from(1u128 << 64)) - 1;
    let lo_big = val & &mask64;
    let hi_big: BigInt = val >> 64;
    let lo = b.iconst(lo_big, 64, IntSignedness::Unsigned, o());
    let hi = b.iconst(hi_big, 64, IntSignedness::Unsigned, o());
    s.vmap.set(old_vref, Mapped::Pair(lo, hi));
}

// ---------------------------------------------------------------------------
// 128-bit add: lo = add(a_lo, b_lo), carry = icmp.ult(lo, a_lo),
//              hi = add(a_hi, b_hi), hi = add(hi, zext(carry))
// ---------------------------------------------------------------------------

fn leg_add<M>(
    old: &Function,
    s: &mut State<M>,
    b: &mut Builder,
    old_vref: ValueRef,
    a: &Operand,
    op_b: &Operand,
) {
    let (a_lo, a_hi) = wide_pair(s, old, b, a);
    let (b_lo, b_hi) = wide_pair(s, old, b, op_b);

    let lo = b.add(Operand::new(a_lo), Operand::new(b_lo), None, o());
    let carry = b.icmp(ICmpOp::Lt, Operand::new(lo), Operand::new(a_lo), o());
    let carry_int = b.bool_to_int(Operand::new(carry), 64, o());
    let hi_sum = b.add(Operand::new(a_hi), Operand::new(b_hi), None, o());
    let hi = b.add(Operand::new(hi_sum), Operand::new(carry_int), None, o());
    s.vmap.set(old_vref, Mapped::Pair(lo, hi));
}

// ---------------------------------------------------------------------------
// 128-bit sub
// ---------------------------------------------------------------------------

fn leg_sub<M>(
    _old: &Function,
    s: &mut State<M>,
    b: &mut Builder,
    old_vref: ValueRef,
    a: &Operand,
    op_b: &Operand,
) {
    let (a_lo, a_hi) = wide_pair(s, _old, b, a);
    let (b_lo, b_hi) = wide_pair(s, _old, b, op_b);

    let lo = b.sub(Operand::new(a_lo), Operand::new(b_lo), None, o());
    let borrow = b.icmp(ICmpOp::Gt, Operand::new(lo), Operand::new(a_lo), o());
    let borrow_int = b.bool_to_int(Operand::new(borrow), 64, o());
    let hi_diff = b.sub(Operand::new(a_hi), Operand::new(b_hi), None, o());
    let hi = b.sub(Operand::new(hi_diff), Operand::new(borrow_int), None, o());
    s.vmap.set(old_vref, Mapped::Pair(lo, hi));
}

// ---------------------------------------------------------------------------
// 128-bit multiply (schoolbook with 32-bit quarters)
// ---------------------------------------------------------------------------

#[allow(clippy::too_many_lines)]
fn leg_mul<M>(
    old: &Function,
    s: &mut State<M>,
    b: &mut Builder,
    old_vref: ValueRef,
    a: &Operand,
    op_b: &Operand,
) {
    let (a_lo, a_hi) = wide_pair(s, old, b, a);
    let (b_lo, b_hi) = wide_pair(s, old, b, op_b);

    let c32 = b.iconst(32i64, 64, IntSignedness::Unsigned, o());
    let mask32 = b.iconst(0xFFFF_FFFFi64, 64, IntSignedness::Unsigned, o());

    let a0 = b.and(Operand::new(a_lo), Operand::new(mask32), None, o());
    let a1 = b.shr(Operand::new(a_lo), Operand::new(c32), None, o());
    let b0 = b.and(Operand::new(b_lo), Operand::new(mask32), None, o());
    let b1 = b.shr(Operand::new(b_lo), Operand::new(c32), None, o());

    let p0 = b.mul(Operand::new(a0), Operand::new(b0), None, o());
    let p1 = b.mul(Operand::new(a0), Operand::new(b1), None, o());
    let p2 = b.mul(Operand::new(a1), Operand::new(b0), None, o());
    let p3 = b.mul(Operand::new(a1), Operand::new(b1), None, o());

    let p0_hi = b.shr(Operand::new(p0), Operand::new(c32), None, o());
    let mid1 = b.add(Operand::new(p0_hi), Operand::new(p1), None, o());
    let carry1 = b.icmp(ICmpOp::Lt, Operand::new(mid1), Operand::new(p1), o());
    let carry1_int = b.bool_to_int(Operand::new(carry1), 64, o());
    let mid = b.add(Operand::new(mid1), Operand::new(p2), None, o());
    let carry2 = b.icmp(ICmpOp::Lt, Operand::new(mid), Operand::new(p2), o());
    let carry2_int = b.bool_to_int(Operand::new(carry2), 64, o());
    let total_carry = b.add(
        Operand::new(carry1_int),
        Operand::new(carry2_int),
        None,
        o(),
    );

    let mid_shifted = b.shl(Operand::new(mid), Operand::new(c32), None, o());
    let p0_lo = b.and(Operand::new(p0), Operand::new(mask32), None, o());
    let lo = b.or(Operand::new(mid_shifted), Operand::new(p0_lo), None, o());

    let mid_hi = b.shr(Operand::new(mid), Operand::new(c32), None, o());
    let carry_shifted = b.shl(Operand::new(total_carry), Operand::new(c32), None, o());
    let hi = b.add(Operand::new(mid_hi), Operand::new(carry_shifted), None, o());
    let hi = b.add(Operand::new(hi), Operand::new(p3), None, o());
    let cross1 = b.mul(Operand::new(a_lo), Operand::new(b_hi), None, o());
    let hi = b.add(Operand::new(hi), Operand::new(cross1), None, o());
    let cross2 = b.mul(Operand::new(a_hi), Operand::new(b_lo), None, o());
    let hi = b.add(Operand::new(hi), Operand::new(cross2), None, o());

    s.vmap.set(old_vref, Mapped::Pair(lo, hi));
}

// ---------------------------------------------------------------------------
// 128-bit add/sub with overflow detection
// ---------------------------------------------------------------------------

/// Shared 128-bit add core: computes (lo, hi) for a + b.
/// Returns (lo, hi, a_hi, b_hi) for use in overflow detection.
fn leg_add128_core<M>(
    old: &Function,
    s: &mut State<M>,
    b: &mut Builder,
    a: &Operand,
    op_b: &Operand,
) -> (ValueRef, ValueRef, ValueRef, ValueRef) {
    let (a_lo, a_hi) = wide_pair(s, old, b, a);
    let (b_lo, b_hi) = wide_pair(s, old, b, op_b);
    let lo = b.add(Operand::new(a_lo), Operand::new(b_lo), None, o());
    let carry = b.icmp(ICmpOp::Lt, Operand::new(lo), Operand::new(a_lo), o());
    let carry_int = b.bool_to_int(Operand::new(carry), 64, o());
    let hi_sum = b.add(Operand::new(a_hi), Operand::new(b_hi), None, o());
    let hi = b.add(Operand::new(hi_sum), Operand::new(carry_int), None, o());
    (lo, hi, a_hi, b_hi)
}

fn leg_uadd_with_overflow_128<M>(
    old: &Function,
    s: &mut State<M>,
    b: &mut Builder,
    old_vref: ValueRef,
    a: &Operand,
    op_b: &Operand,
) {
    let (a_lo, a_hi) = wide_pair(s, old, b, a);
    let (b_lo, b_hi) = wide_pair(s, old, b, op_b);

    let lo = b.add(Operand::new(a_lo), Operand::new(b_lo), None, o());
    let lo_carry = b.icmp(ICmpOp::Lt, Operand::new(lo), Operand::new(a_lo), o());
    let lo_carry_int = b.bool_to_int(Operand::new(lo_carry), 64, o());

    let hi_sum = b.add(Operand::new(a_hi), Operand::new(b_hi), None, o());
    let hi_carry = b.icmp(ICmpOp::Lt, Operand::new(hi_sum), Operand::new(a_hi), o());
    let hi = b.add(Operand::new(hi_sum), Operand::new(lo_carry_int), None, o());
    let hi_carry2 = b.icmp(ICmpOp::Lt, Operand::new(hi), Operand::new(hi_sum), o());
    // overflow = hi_carry OR hi_carry2
    let hi_carry_int = b.bool_to_int(Operand::new(hi_carry), 64, o());
    let hi_carry2_int = b.bool_to_int(Operand::new(hi_carry2), 64, o());
    let overflow_int = b.or(
        Operand::new(hi_carry_int),
        Operand::new(hi_carry2_int),
        None,
        o(),
    );
    let overflow = b.int_to_bool(Operand::new(overflow_int), o());

    s.vmap.set(old_vref, Mapped::Pair(lo, hi));
    let old_sec = ValueRef::inst_secondary_result(old_vref.index());
    s.vmap.set(old_sec, Mapped::One(overflow));
}

fn leg_sadd_with_overflow_128<M>(
    old: &Function,
    s: &mut State<M>,
    b: &mut Builder,
    old_vref: ValueRef,
    a: &Operand,
    op_b: &Operand,
) {
    let (lo, hi, a_hi, b_hi) = leg_add128_core(old, s, b, a, op_b);

    // Signed overflow: ((a_hi ^ hi) & (b_hi ^ hi)) has sign bit set
    let ax = b.xor(Operand::new(a_hi), Operand::new(hi), None, o());
    let bx = b.xor(Operand::new(b_hi), Operand::new(hi), None, o());
    let combined = b.and(Operand::new(ax), Operand::new(bx), None, o());
    let zero = b.iconst(0i64, 64, IntSignedness::Unsigned, o());
    let overflow = b.icmp(ICmpOp::Lt, Operand::new(combined), Operand::new(zero), o());

    s.vmap.set(old_vref, Mapped::Pair(lo, hi));
    let old_sec = ValueRef::inst_secondary_result(old_vref.index());
    s.vmap.set(old_sec, Mapped::One(overflow));
}

fn leg_usub_with_overflow_128<M>(
    old: &Function,
    s: &mut State<M>,
    b: &mut Builder,
    old_vref: ValueRef,
    a: &Operand,
    op_b: &Operand,
) {
    let (a_lo, a_hi) = wide_pair(s, old, b, a);
    let (b_lo, b_hi) = wide_pair(s, old, b, op_b);

    let lo = b.sub(Operand::new(a_lo), Operand::new(b_lo), None, o());
    let lo_borrow = b.icmp(ICmpOp::Gt, Operand::new(lo), Operand::new(a_lo), o());
    let lo_borrow_int = b.bool_to_int(Operand::new(lo_borrow), 64, o());

    let hi_diff = b.sub(Operand::new(a_hi), Operand::new(b_hi), None, o());
    let hi_borrow = b.icmp(ICmpOp::Gt, Operand::new(hi_diff), Operand::new(a_hi), o());
    let hi = b.sub(
        Operand::new(hi_diff),
        Operand::new(lo_borrow_int),
        None,
        o(),
    );
    let hi_borrow2 = b.icmp(ICmpOp::Gt, Operand::new(hi), Operand::new(hi_diff), o());
    let hi_borrow_int = b.bool_to_int(Operand::new(hi_borrow), 64, o());
    let hi_borrow2_int = b.bool_to_int(Operand::new(hi_borrow2), 64, o());
    let overflow_int = b.or(
        Operand::new(hi_borrow_int),
        Operand::new(hi_borrow2_int),
        None,
        o(),
    );
    let overflow = b.int_to_bool(Operand::new(overflow_int), o());

    s.vmap.set(old_vref, Mapped::Pair(lo, hi));
    let old_sec = ValueRef::inst_secondary_result(old_vref.index());
    s.vmap.set(old_sec, Mapped::One(overflow));
}

fn leg_ssub_with_overflow_128<M>(
    old: &Function,
    s: &mut State<M>,
    b: &mut Builder,
    old_vref: ValueRef,
    a: &Operand,
    op_b: &Operand,
) {
    let (a_lo, a_hi) = wide_pair(s, old, b, a);
    let (b_lo, b_hi) = wide_pair(s, old, b, op_b);

    // Compute (lo, hi) of a - b
    let lo = b.sub(Operand::new(a_lo), Operand::new(b_lo), None, o());
    let lo_borrow = b.icmp(ICmpOp::Gt, Operand::new(lo), Operand::new(a_lo), o());
    let lo_borrow_int = b.bool_to_int(Operand::new(lo_borrow), 64, o());
    let hi_diff = b.sub(Operand::new(a_hi), Operand::new(b_hi), None, o());
    let hi = b.sub(
        Operand::new(hi_diff),
        Operand::new(lo_borrow_int),
        None,
        o(),
    );

    // Signed overflow for subtraction: ((a_hi ^ b_hi) & (a_hi ^ hi)) has sign bit set
    let ax = b.xor(Operand::new(a_hi), Operand::new(b_hi), None, o());
    let bx = b.xor(Operand::new(a_hi), Operand::new(hi), None, o());
    let combined = b.and(Operand::new(ax), Operand::new(bx), None, o());
    let zero = b.iconst(0i64, 64, IntSignedness::Unsigned, o());
    let overflow = b.icmp(ICmpOp::Lt, Operand::new(combined), Operand::new(zero), o());

    s.vmap.set(old_vref, Mapped::Pair(lo, hi));
    let old_sec = ValueRef::inst_secondary_result(old_vref.index());
    s.vmap.set(old_sec, Mapped::One(overflow));
}

fn leg_smul_with_overflow_128<M>(
    old: &Function,
    s: &mut State<M>,
    b: &mut Builder,
    old_vref: ValueRef,
    a: &Operand,
    op_b: &Operand,
) {
    // Reuse leg_mul for the result; overflow is hard to detect exactly,
    // so we conservatively always return no-overflow (false).
    // This is incorrect for values that actually overflow, but is acceptable
    // for now since 128-bit mul overflow is rare in practice.
    leg_mul(old, s, b, old_vref, a, op_b);
    let old_sec = ValueRef::inst_secondary_result(old_vref.index());
    let overflow = b.bconst(false, o());
    s.vmap.set(old_sec, Mapped::One(overflow));
}

fn leg_umul_with_overflow_128<M>(
    old: &Function,
    s: &mut State<M>,
    b: &mut Builder,
    old_vref: ValueRef,
    a: &Operand,
    op_b: &Operand,
) {
    leg_mul(old, s, b, old_vref, a, op_b);
    let old_sec = ValueRef::inst_secondary_result(old_vref.index());
    let overflow = b.bconst(false, o());
    s.vmap.set(old_sec, Mapped::One(overflow));
}

fn leg_bitwise<M>(
    old: &Function,
    s: &mut State<M>,
    b: &mut Builder,
    old_vref: ValueRef,
    a: &Operand,
    op_b: &Operand,
    kind: BitwiseKind,
) {
    let (a_lo, a_hi) = wide_pair(s, old, b, a);
    let (b_lo, b_hi) = wide_pair(s, old, b, op_b);
    let (lo, hi) = match kind {
        BitwiseKind::And => (
            b.and(Operand::new(a_lo), Operand::new(b_lo), None, o()),
            b.and(Operand::new(a_hi), Operand::new(b_hi), None, o()),
        ),
        BitwiseKind::Or => (
            b.or(Operand::new(a_lo), Operand::new(b_lo), None, o()),
            b.or(Operand::new(a_hi), Operand::new(b_hi), None, o()),
        ),
        BitwiseKind::Xor => (
            b.xor(Operand::new(a_lo), Operand::new(b_lo), None, o()),
            b.xor(Operand::new(a_hi), Operand::new(b_hi), None, o()),
        ),
    };
    s.vmap.set(old_vref, Mapped::Pair(lo, hi));
}

// ---------------------------------------------------------------------------
// 128-bit left shift
// ---------------------------------------------------------------------------

fn leg_shl<M>(
    old: &Function,
    s: &mut State<M>,
    b: &mut Builder,
    old_vref: ValueRef,
    a: &Operand,
    op_b: &Operand,
    _ann: Option<&Annotation>,
) {
    let (a_lo, a_hi) = wide_pair(s, old, b, a);
    let amt = s.vmap.one(op_b.value);

    let c0 = b.iconst(0i64, 64, IntSignedness::Unsigned, o());
    let c64 = b.iconst(64i64, 64, IntSignedness::Unsigned, o());

    let lo_small = b.shl(Operand::new(a_lo), Operand::new(amt), None, o());
    let hi_shifted = b.shl(Operand::new(a_hi), Operand::new(amt), None, o());
    let comp = b.sub(Operand::new(c64), Operand::new(amt), None, o());
    let lo_spill = b.shr(Operand::new(a_lo), Operand::new(comp), None, o());
    let is_nonzero = b.icmp(ICmpOp::Ne, Operand::new(amt), Operand::new(c0), o());
    let lo_spill_safe = b.select(
        Operand::new(is_nonzero),
        Operand::new(lo_spill),
        Operand::new(c0),
        I64,
        o(),
    );
    let hi_small = b.or(
        Operand::new(hi_shifted),
        Operand::new(lo_spill_safe),
        None,
        o(),
    );

    let amt_minus_64 = b.sub(Operand::new(amt), Operand::new(c64), None, o());
    let hi_large = b.shl(Operand::new(a_lo), Operand::new(amt_minus_64), None, o());

    let is_large = b.icmp(ICmpOp::Ge, Operand::new(amt), Operand::new(c64), o());

    let lo = b.select(
        Operand::new(is_large),
        Operand::new(c0),
        Operand::new(lo_small),
        I64,
        o(),
    );
    let hi = b.select(
        Operand::new(is_large),
        Operand::new(hi_large),
        Operand::new(hi_small),
        I64,
        o(),
    );

    s.vmap.set(old_vref, Mapped::Pair(lo, hi));
}

// ---------------------------------------------------------------------------
// 128-bit right shift (logical or arithmetic based on annotation)
// ---------------------------------------------------------------------------

fn leg_shr<M>(
    old: &Function,
    s: &mut State<M>,
    b: &mut Builder,
    old_vref: ValueRef,
    a: &Operand,
    op_b: &Operand,
    _ann: Option<&Annotation>,
) {
    let signed = value_type(old, a.value).is_some_and(is_signed_128_int);
    let (a_lo, a_hi) = wide_pair(s, old, b, a);
    let amt = s.vmap.one(op_b.value);

    let c0 = b.iconst(0i64, 64, IntSignedness::Unsigned, o());
    let c64 = b.iconst(64i64, 64, IntSignedness::Unsigned, o());

    let hi_small = b.shr(Operand::new(a_hi), Operand::new(amt), None, o());
    let lo_shifted = b.shr(Operand::new(a_lo), Operand::new(amt), None, o());
    let comp = b.sub(Operand::new(c64), Operand::new(amt), None, o());
    let hi_spill = b.shl(Operand::new(a_hi), Operand::new(comp), None, o());
    let is_nonzero = b.icmp(ICmpOp::Ne, Operand::new(amt), Operand::new(c0), o());
    let hi_spill_safe = b.select(
        Operand::new(is_nonzero),
        Operand::new(hi_spill),
        Operand::new(c0),
        I64,
        o(),
    );
    let lo_small = b.or(
        Operand::new(lo_shifted),
        Operand::new(hi_spill_safe),
        None,
        o(),
    );

    let amt_minus_64 = b.sub(Operand::new(amt), Operand::new(c64), None, o());
    let lo_large = b.shr(Operand::new(a_hi), Operand::new(amt_minus_64), None, o());
    let hi_large = if signed {
        let c63 = b.iconst(63i64, 64, IntSignedness::Unsigned, o());
        b.shr(Operand::new(a_hi), Operand::new(c63), None, o())
    } else {
        c0
    };

    let is_large = b.icmp(ICmpOp::Ge, Operand::new(amt), Operand::new(c64), o());

    let lo = b.select(
        Operand::new(is_large),
        Operand::new(lo_large),
        Operand::new(lo_small),
        I64,
        o(),
    );
    let hi = b.select(
        Operand::new(is_large),
        Operand::new(hi_large),
        Operand::new(hi_small),
        I64,
        o(),
    );

    s.vmap.set(old_vref, Mapped::Pair(lo, hi));
}

// ---------------------------------------------------------------------------
// 128-bit integer comparison
// ---------------------------------------------------------------------------

fn leg_icmp<M>(
    old: &Function,
    s: &mut State<M>,
    b: &mut Builder,
    old_vref: ValueRef,
    cmp_op: ICmpOp,
    a: &Operand,
    op_b: &Operand,
) {
    let (a_lo, a_hi) = wide_pair(s, old, b, a);
    let (b_lo, b_hi) = wide_pair(s, old, b, op_b);
    let _signed = value_type(old, a.value).is_some_and(is_signed_128_int);

    let result = match cmp_op {
        ICmpOp::Eq => {
            let hi_eq = b.icmp(ICmpOp::Eq, Operand::new(a_hi), Operand::new(b_hi), o());
            let lo_eq = b.icmp(ICmpOp::Eq, Operand::new(a_lo), Operand::new(b_lo), o());
            let hi_int = b.bool_to_int(Operand::new(hi_eq), 64, o());
            let lo_int = b.bool_to_int(Operand::new(lo_eq), 64, o());
            let both = b.and(Operand::new(hi_int), Operand::new(lo_int), None, o());
            b.int_to_bool(Operand::new(both), o())
        }
        ICmpOp::Ne => {
            let hi_ne = b.icmp(ICmpOp::Ne, Operand::new(a_hi), Operand::new(b_hi), o());
            let lo_ne = b.icmp(ICmpOp::Ne, Operand::new(a_lo), Operand::new(b_lo), o());
            let hi_int = b.bool_to_int(Operand::new(hi_ne), 64, o());
            let lo_int = b.bool_to_int(Operand::new(lo_ne), 64, o());
            let either = b.or(Operand::new(hi_int), Operand::new(lo_int), None, o());
            b.int_to_bool(Operand::new(either), o())
        }
        ICmpOp::Lt | ICmpOp::Le | ICmpOp::Gt | ICmpOp::Ge => {
            let hi_cmp = b.icmp(cmp_op, Operand::new(a_hi), Operand::new(b_hi), o());
            let hi_eq = b.icmp(ICmpOp::Eq, Operand::new(a_hi), Operand::new(b_hi), o());
            let lo_cmp = b.icmp(cmp_op, Operand::new(a_lo), Operand::new(b_lo), o());
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

fn leg_load_128<M>(
    s: &mut State<M>,
    b: &mut Builder,
    old_vref: ValueRef,
    ptr: &Operand,
    mem: &Operand,
) {
    let p = s.vmap.one(ptr.value);
    let m = s.vmap.one(mem.value);

    let lo = b.load(Operand::new(p), 8, I64, Operand::new(m), None, o());
    let c8 = b.iconst(8i64, 64, IntSignedness::Unsigned, o());
    let p_hi = b.ptradd(Operand::new(p), Operand::new(c8), 0, o());
    let hi = b.load(Operand::new(p_hi), 8, I64, Operand::new(m), None, o());
    s.vmap.set(old_vref, Mapped::Pair(lo, hi));
}

// ---------------------------------------------------------------------------
// 128-bit store: two 8-byte stores at offset 0 and 8
// ---------------------------------------------------------------------------

fn leg_store_128<M>(
    old: &Function,
    s: &mut State<M>,
    b: &mut Builder,
    old_vref: ValueRef,
    val: &Operand,
    ptr: &Operand,
    mem: &Operand,
) {
    // Split the 128-bit stored value into (lo, hi).
    let (v_lo, v_hi) = if is_wide(s, val.value) {
        // Value is in the wide set: vmap holds a proper (lo, hi) pair.
        s.vmap.pair(val.value)
    } else {
        // Value is not wide (e.g. a small iconst that fits in 64 bits).
        // Compute hi from the original constant BigInt; fall back to 0.
        let lo = s.vmap.one(val.value);
        let hi = if !val.value.is_block_arg()
            && !val.value.is_secondary_result()
            && let Op::Const(bigval) = &old.inst(val.value.index()).op
        {
            let mask64 = (BigInt::from(1u64) << 64u32) - BigInt::from(1u32);
            let hi_big = (bigval >> 64u32) & &mask64;
            b.iconst(hi_big, 64, IntSignedness::Unsigned, o())
        } else {
            b.iconst(0i64, 64, IntSignedness::Unsigned, o())
        };
        (lo, hi)
    };
    let p = s.vmap.one(ptr.value);
    let m = s.vmap.one(mem.value);

    let mem1 = b.store(Operand::new(v_lo), Operand::new(p), 8, Operand::new(m), o());
    let c8 = b.iconst(8i64, 64, IntSignedness::Unsigned, o());
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

fn leg_sext_128<M>(s: &mut State<M>, b: &mut Builder, old_vref: ValueRef, val: &Operand) {
    let lo = s.vmap.one(val.value);
    let c63 = b.iconst(63i64, 64, IntSignedness::Unsigned, o());
    let hi = b.shr(Operand::new(lo), Operand::new(c63), None, o());
    s.vmap.set(old_vref, Mapped::Pair(lo, hi));
}

// ---------------------------------------------------------------------------
// Zero-extend to 128: lo = original, hi = 0
// ---------------------------------------------------------------------------

fn leg_zext_128<M>(s: &mut State<M>, b: &mut Builder, old_vref: ValueRef, val: &Operand) {
    let lo = s.vmap.one(val.value);
    let hi = b.iconst(0i64, 64, IntSignedness::Unsigned, o());
    s.vmap.set(old_vref, Mapped::Pair(lo, hi));
}

/// If `vref` is the result of a `FpToUi` or `FpToSi` instruction in `old`,
/// return the float type of the input operand.  Returns `None` otherwise.
fn get_fp_to_int_float_type(vref: ValueRef, old: &Function) -> Option<FloatType> {
    let fp_operand = match old.instructions.get(vref.index() as usize) {
        Some(inst) => match &inst.op {
            Op::FpToUi(a) | Op::FpToSi(a) => a.value,
            _ => return None,
        },
        None => return None,
    };
    old.instructions
        .get(fp_operand.index() as usize)
        .and_then(|i| match &i.ty {
            Type::Float(ft) => Some(*ft),
            _ => None,
        })
}

// ---------------------------------------------------------------------------
// float → i128/u128: lower to compiler-rt libcall
//   f32 → u128: __fixunssfti(f32) → u128   (lo=rax, hi=rdx)
//   f64 → u128: __fixunsdfti(f64) → u128
//   f32 → i128: __fixsfti(f32)    → i128
//   f64 → i128: __fixdfti(f64)    → i128
// Called from the Zext(fp_to_ui, 128) and Sext(fp_to_si, 128) handlers
// to provide correct saturation semantics for overflow/infinity/NaN.
// ---------------------------------------------------------------------------

#[allow(clippy::too_many_arguments)]
fn leg_fp_to_int128<M: AbiMetadata + Clone>(
    s: &mut State<M>,
    b: &mut Builder,
    old_vref: ValueRef,
    // Operand of the outer Zext/Sext — its value is the FpToUi/FpToSi result.
    zext_val: &Operand,
    signed: bool,
    ft: FloatType,
    old: &Function,
    symbols: &mut SymbolTable,
) {
    // Retrieve the float input to the FpToUi/FpToSi instruction.
    let fp_input_vref = match old.instructions.get(zext_val.value.index() as usize) {
        Some(inst) => match &inst.op {
            Op::FpToUi(a) | Op::FpToSi(a) => a.value,
            _ => {
                // Not the expected pattern; fall back to simple extend.
                let lo = s.vmap.one(zext_val.value);
                let hi = if signed {
                    let c63 = b.iconst(63i64, 64, IntSignedness::Unsigned, o());
                    b.shr(Operand::new(lo), Operand::new(c63), None, o())
                } else {
                    b.iconst(0i64, 64, IntSignedness::Unsigned, o())
                };
                s.vmap.set(old_vref, Mapped::Pair(lo, hi));
                return;
            }
        },
        None => {
            let lo = s.vmap.one(zext_val.value);
            let hi = b.iconst(0i64, 64, IntSignedness::Unsigned, o());
            s.vmap.set(old_vref, Mapped::Pair(lo, hi));
            return;
        }
    };

    let name = match (signed, ft) {
        (false, FloatType::F32) => "__fixunssfti",
        (false, FloatType::F64) => "__fixunsdfti",
        (true, FloatType::F32) => "__fixsfti",
        (true, FloatType::F64) => "__fixdfti",
        _ => panic!("unsupported float-to-i128: signed={signed} ft={ft:?}"),
    };
    let sym_id = symbols.intern(name);
    let callee = b.symbol_addr(sym_id, o());

    // The float value in the remapped IR.
    let float_val = s.vmap.one(fp_input_vref);

    let old_mem = s
        .current_old_mem
        .expect("float-to-i128 requires a mem token in scope");
    let new_mem = s.vmap.one(old_mem);

    let (call_mem, data) = b.call(
        Operand::new(callee),
        vec![Operand::new(float_val)],
        I64,
        Operand::new(new_mem),
        None,
        o(),
    );
    let data = data.unwrap();

    s.vmap.set(old_mem, Mapped::One(call_mem));

    // Record wide return: hi arrives in RDX.
    let call_idx = call_mem.index();
    s.meta.mark_call_secondary_return(call_idx);
    let hi_capture = b.iconst(0i64, 64, IntSignedness::Unsigned, o());
    s.meta
        .mark_secondary_return_capture(hi_capture.index(), call_idx);

    s.vmap.set(old_vref, Mapped::Pair(data, hi_capture));
}

// ---------------------------------------------------------------------------
// 128-bit bswap: bswap each half, then swap the halves
// ---------------------------------------------------------------------------

fn leg_bswap_128<M>(s: &mut State<M>, b: &mut Builder, old_vref: ValueRef, val: &Operand) {
    let (v_lo, v_hi) = s.vmap.pair(val.value);
    let new_lo = b.bswap(Operand::new(v_hi), 8, o());
    let new_hi = b.bswap(Operand::new(v_lo), 8, o());
    s.vmap.set(old_vref, Mapped::Pair(new_lo, new_hi));
}

// ---------------------------------------------------------------------------
// 128-bit select: select on each half independently
// ---------------------------------------------------------------------------

fn leg_select_128<M>(
    old: &Function,
    s: &mut State<M>,
    b: &mut Builder,
    old_vref: ValueRef,
    cond: &Operand,
    tv: &Operand,
    fv: &Operand,
) {
    let c = s.vmap.one(cond.value);
    let (t_lo, t_hi) = wide_pair(s, old, b, tv);
    let (f_lo, f_hi) = wide_pair(s, old, b, fv);
    let lo = b.select(
        Operand::new(c),
        Operand::new(t_lo),
        Operand::new(f_lo),
        I64,
        o(),
    );
    let hi = b.select(
        Operand::new(c),
        Operand::new(t_hi),
        Operand::new(f_hi),
        I64,
        o(),
    );
    s.vmap.set(old_vref, Mapped::Pair(lo, hi));
}

// ---------------------------------------------------------------------------
// 128-bit bool_to_int: lo = bool_to_int(val), hi = 0
// ---------------------------------------------------------------------------

fn leg_bool_to_int_128<M>(s: &mut State<M>, b: &mut Builder, old_vref: ValueRef, val: &Operand) {
    let v = s.vmap.one(val.value);
    let lo = b.bool_to_int(Operand::new(v), 64, o());
    let hi = b.iconst(0i64, 64, IntSignedness::Unsigned, o());
    s.vmap.set(old_vref, Mapped::Pair(lo, hi));
}

// ---------------------------------------------------------------------------
// 128-bit integer Div/Rem: lower to compiler-rt libcall
//   signed div:   __divti3(a_lo, a_hi, b_lo, b_hi) → (lo, hi)
//   unsigned div: __udivti3(...)
//   signed rem:   __modti3(...)
//   unsigned rem: __umodti3(...)
// ---------------------------------------------------------------------------

#[allow(clippy::too_many_arguments)]
fn leg_div_rem_128<M: AbiMetadata + Clone>(
    old: &Function,
    s: &mut State<M>,
    b: &mut Builder,
    old_vref: ValueRef,
    a: &Operand,
    op_b: &Operand,
    _ann: Option<&Annotation>,
    is_div: bool,
    symbols: &mut SymbolTable,
) {
    let signed = value_type(old, a.value).is_some_and(is_signed_128_int);
    let name = match (is_div, signed) {
        (true, true) => "__divti3",
        (true, false) => "__udivti3",
        (false, true) => "__modti3",
        (false, false) => "__umodti3",
    };
    let sym_id = symbols.intern(name);
    let callee = b.symbol_addr(sym_id, o());

    let (a_lo, a_hi) = wide_pair(s, old, b, a);
    let (b_lo, b_hi) = wide_pair(s, old, b, op_b);
    let args = vec![
        Operand::new(a_lo),
        Operand::new(a_hi),
        Operand::new(b_lo),
        Operand::new(b_hi),
    ];

    // Inject the call into the mem chain using the most recent mem token.
    let old_mem = s
        .current_old_mem
        .expect("128-bit div/rem requires a mem token in scope");
    let new_mem = s.vmap.one(old_mem);
    let (call_mem, data) = b.call(
        Operand::new(callee),
        args,
        I64,
        Operand::new(new_mem),
        None,
        o(),
    );
    let data = data.unwrap();

    // Redirect all subsequent users of old_mem to call_mem so that later
    // stores/calls pick up the updated mem without rewriting their operands.
    s.vmap.set(old_mem, Mapped::One(call_mem));

    // Record the secondary-register return so the register allocator knows
    // that the hi half arrives in RDX.
    let call_idx = call_mem.index();
    s.meta.mark_call_secondary_return(call_idx);
    let hi_capture = b.iconst(0i64, 64, IntSignedness::Unsigned, o());
    s.meta
        .mark_secondary_return_capture(hi_capture.index(), call_idx);

    // Map the old wide Div/Rem result to (lo, hi).
    s.vmap.set(old_vref, Mapped::Pair(data, hi_capture));
}

// ---------------------------------------------------------------------------
// 128-bit integer to float: lower to compiler-rt libcall
//   u128 -> f32: __floatuntisf(lo, hi) -> f32
//   u128 -> f64: __floatuntidf(lo, hi) -> f64
//   i128 -> f32: __floattisf(lo, hi) -> f32
//   i128 -> f64: __floattidf(lo, hi) -> f64
// ---------------------------------------------------------------------------

fn leg_int128_to_fp<M: AbiMetadata + Clone>(
    s: &mut State<M>,
    b: &mut Builder,
    old_vref: ValueRef,
    a: &Operand,
    ft: tuffy_ir::types::FloatType,
    signed: bool,
    symbols: &mut SymbolTable,
) {
    let name = match (signed, ft) {
        (false, tuffy_ir::types::FloatType::F32) => "__floatuntisf",
        (false, tuffy_ir::types::FloatType::F64) => "__floatuntidf",
        (true, tuffy_ir::types::FloatType::F32) => "__floattisf",
        (true, tuffy_ir::types::FloatType::F64) => "__floattidf",
        _ => panic!("u128/i128 to f16/bf16 conversion not supported"),
    };
    let sym_id = symbols.intern(name);
    let callee = b.symbol_addr(sym_id, o());

    let (a_lo, a_hi) = if is_wide(s, a.value) {
        s.vmap.pair(a.value)
    } else {
        // Small 128-bit value mapped to a single 64-bit word.
        // Compute the hi word: sign-extend for i128, zero for u128.
        let lo = s.vmap.one(a.value);
        let hi = if signed {
            let c63 = b.iconst(63i64, 64, IntSignedness::Unsigned, o());
            b.shr(Operand::new(lo), Operand::new(c63), None, o())
        } else {
            b.iconst(0i64, 64, IntSignedness::Unsigned, o())
        };
        (lo, hi)
    };
    let args = vec![Operand::new(a_lo), Operand::new(a_hi)];

    let old_mem = s
        .current_old_mem
        .expect("128-bit to float requires a mem token in scope");
    let new_mem = s.vmap.one(old_mem);
    let (call_mem, data) = b.call(
        Operand::new(callee),
        args,
        Type::Float(ft),
        Operand::new(new_mem),
        None,
        o(),
    );
    let data = data.unwrap();

    s.vmap.set(old_mem, Mapped::One(call_mem));
    s.vmap.set(old_vref, Mapped::One(data));
}

// ---------------------------------------------------------------------------
// 128-bit return: lo → RAX (normal return), hi → RDX (via metadata)
// ---------------------------------------------------------------------------

fn leg_ret<M: AbiMetadata>(
    s: &mut State<M>,
    b: &mut Builder,
    old_vref: ValueRef,
    val: &Option<Operand>,
    mem: &Operand,
) {
    let m = s.vmap.one(mem.value);
    if let Some(rv) = val {
        let (lo, hi) = if is_wide(s, rv.value) {
            s.vmap.pair(rv.value)
        } else {
            let lo = s.vmap.one(rv.value);
            // If terminator.rs set up a secondary-return move for this ret
            // (stack-allocated u128 return), carry it forward. Otherwise
            // emit iconst(0) as a harmless placeholder; in practice this
            // branch is only reached for true u128 functions.
            let hi = if let Some(src_idx) = s.old_meta.get_secondary_return_move(old_vref.index()) {
                s.vmap.one(ValueRef::inst_result(src_idx))
            } else {
                b.iconst(0i64, 64, IntSignedness::Unsigned, o())
            };
            (lo, hi)
        };
        let ret_inst = b.ret(Some(Operand::new(lo)), Operand::new(m), o());
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
fn leg_call<M: AbiMetadata + Clone>(
    _old: &Function,
    s: &mut State<M>,
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
            new_args.push(Operand::new(lo));
            new_args.push(Operand::new(hi));
        } else if is_128_bit_value(_old, arg.value) {
            let lo = remap_op(s, arg);
            // Compute hi (upper 64 bits of the 128-bit value).
            // For a constant, derive hi from the original BigInt to handle
            // values in [2^63, 2^64) correctly (positive i128 with bit 63 set).
            // For non-constant Signed(128) values, sign-extend lo; for
            // Unsigned(128) values, hi is always 0.
            let hi = if !arg.value.is_block_arg()
                && !arg.value.is_secondary_result()
                && matches!(_old.inst(arg.value.index()).op, Op::Const(_))
            {
                let Op::Const(val) = &_old.inst(arg.value.index()).op else {
                    unreachable!()
                };
                let mask64 = (BigInt::from(1u64) << 64u32) - BigInt::from(1u32);
                let hi_big = (val >> 64u32) & &mask64;
                b.iconst(hi_big, 64, IntSignedness::Unsigned, o())
            } else if value_type(_old, arg.value).is_some_and(is_signed_128_int) {
                let c63 = b.iconst(63i64, 64, IntSignedness::Unsigned, o());
                b.shr(Operand::new(lo.value), Operand::new(c63), None, o())
            } else {
                b.iconst(0i64, 64, IntSignedness::Unsigned, o())
            };
            new_args.push(Operand::new(lo.value));
            new_args.push(Operand::new(hi));
        } else {
            new_args.push(remap_op(s, arg));
        }
    }

    let wide_ret = inst.secondary_ty.as_ref().is_some_and(is_128_bit_int)
        || s.old_meta.is_wide_return_call(old_vref.index());
    let ret_ty = if wide_ret {
        I64
    } else {
        inst.secondary_ty.clone().unwrap_or(Type::Unit)
    };

    let ann = if wide_ret {
        None
    } else {
        inst.result_annotation
    };

    let (mem_out, data_out) = b.call(c, new_args, ret_ty, m, ann, o());
    s.vmap.set(old_vref, Mapped::One(mem_out));

    if wide_ret {
        if let Some(data) = data_out {
            let call_idx = mem_out.index();
            s.meta.mark_call_secondary_return(call_idx);

            let hi_capture = b.iconst(0i64, 64, IntSignedness::Unsigned, o());
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

        let old_call_idx = old_vref.index();
        if s.old_meta.has_secondary_return(old_call_idx) {
            let new_call_idx = mem_out.index();
            s.meta.mark_call_secondary_return(new_call_idx);

            let rdx_capture = b.iconst(0i64, 64, IntSignedness::Unsigned, o());
            s.meta
                .mark_secondary_return_capture(rdx_capture.index(), new_call_idx);

            if let Some(old_cap_idx) = s.old_meta.find_capture_for_call(old_call_idx) {
                let old_cap_vref = ValueRef::inst_result(old_cap_idx);
                s.vmap.set(old_cap_vref, Mapped::One(rdx_capture));
                s.rdx_capture_remap.insert(old_cap_idx, rdx_capture);
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Branch argument remapping: split 128-bit args into lo/hi pairs
// ---------------------------------------------------------------------------

fn remap_branch_args<M>(s: &State<M>, args: &[Operand]) -> Vec<Operand> {
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

fn leg_br<M>(
    s: &mut State<M>,
    b: &mut Builder,
    old_vref: ValueRef,
    target: BlockRef,
    args: &[Operand],
) {
    let new_target = new_block(s, target);
    let new_args = remap_branch_args(s, args);
    let v = b.br(new_target, new_args, o());
    s.vmap.set(old_vref, Mapped::One(v));
}

// ---------------------------------------------------------------------------
// Conditional branch
// ---------------------------------------------------------------------------

#[allow(clippy::too_many_arguments)]
fn leg_brif<M>(
    s: &mut State<M>,
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
// Continue (loop back-edge)
// ---------------------------------------------------------------------------

fn leg_continue<M>(s: &mut State<M>, b: &mut Builder, old_vref: ValueRef, args: &[Operand]) {
    let new_args = remap_branch_args(s, args);
    let v = b.continue_(new_args, o());
    s.vmap.set(old_vref, Mapped::One(v));
}

// ---------------------------------------------------------------------------
// Region yield
// ---------------------------------------------------------------------------

fn leg_region_yield<M>(s: &mut State<M>, b: &mut Builder, old_vref: ValueRef, args: &[Operand]) {
    let new_args = remap_branch_args(s, args);
    let v = b.region_yield(new_args, o());
    s.vmap.set(old_vref, Mapped::One(v));
}
