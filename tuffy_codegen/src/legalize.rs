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
use tuffy_ir::instruction::{FCmpOp, ICmpOp, Op, Operand, Origin};
use tuffy_ir::module::SymbolTable;
use tuffy_ir::typed::IntOperand;
use tuffy_ir::types::{Annotation, FloatType, IntAnnotation, IntSignedness, Type};
use tuffy_ir::value::{BlockRef, ValueRef};

use tuffy_target::backend::AbiMetadata;

// 64-bit unsigned IntAnnotation for legalized operations
const I64: IntAnnotation = IntAnnotation {
    bit_width: 64,
    signedness: IntSignedness::Unsigned,
};

// 64-bit unsigned Type for legalized operations
const I64_TYPE: Type = Type::Int;
use tuffy_target::legality::LegalityInfo;

// ---------------------------------------------------------------------------
// Helper constants
// ---------------------------------------------------------------------------

const SIGNED_64_INT: IntAnnotation = IntAnnotation {
    bit_width: 64,
    signedness: IntSignedness::Signed,
};

const UNSIGNED_64_INT: IntAnnotation = IntAnnotation {
    bit_width: 64,
    signedness: IntSignedness::Unsigned,
};

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
        Type::Int => None,
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
    // This function name is misleading - it's used as a type check only.
    // The actual bit width check happens via annotations elsewhere.
    matches!(ty, Type::Int)
}

fn is_128_bit_int_with_annotation(ty: &Type, ann: &Option<Annotation>) -> bool {
    matches!(ty, Type::Int)
        && ann
            .as_ref()
            .is_some_and(|a| matches!(a, Annotation::Int(ia) if ia.bit_width > 64))
}

/// Check whether an operand annotation indicates a signed integer.
fn is_signed_annotation(ann: Option<&Annotation>) -> bool {
    matches!(
        ann,
        Some(Annotation::Int(IntAnnotation {
            signedness: IntSignedness::Signed,
            ..
        }))
    )
}

fn value_type(func: &Function, v: ValueRef) -> Option<&Type> {
    if v.is_block_arg() {
        func.block_args.get(v.index() as usize).map(|ba| &ba.ty)
    } else if v.is_secondary_result() {
        func.inst_pool
            .get(v.inst_index())?
            .inst
            .secondary_ty
            .as_ref()
    } else {
        func.inst_pool.get(v.index()).map(|n| &n.inst.ty)
    }
}

fn value_annotation(func: &Function, v: ValueRef) -> Option<&Annotation> {
    if v.is_block_arg() || v.is_secondary_result() {
        None
    } else {
        func.inst_pool
            .get(v.index())
            .and_then(|n| n.inst.result_annotation.as_ref())
    }
}

fn is_128_bit_value(func: &Function, v: ValueRef) -> bool {
    let Some(ty) = value_type(func, v) else {
        return false;
    };
    if !matches!(ty, Type::Int) {
        return false;
    }
    let ann = value_annotation(func, v).cloned();
    is_128_bit_int_with_annotation(ty, &ann)
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
    for (ty, ann) in func.params.iter().zip(func.param_annotations.iter()) {
        if is_wide_width(type_width(ty), legality) {
            return true;
        }
        // Check annotation for integer bit width
        if matches!(ty, Type::Int)
            && let Some(Annotation::Int(ia)) = ann
            && ia.bit_width > legality.max_int_width()
        {
            return true;
        }
    }

    // Check for wide return type
    if let Some(ref ty) = func.ret_ty {
        if is_wide_width(type_width(ty), legality) {
            return true;
        }
        // Check annotation for integer bit width
        if matches!(ty, Type::Int)
            && let Some(Annotation::Int(ia)) = &func.ret_annotation
            && ia.bit_width > legality.max_int_width()
        {
            return true;
        }
    }

    // Check for wide instructions
    for (_, inst) in func.inst_pool.iter_insts() {
        if is_wide_width(type_width(&inst.ty), legality) {
            return true;
        }
        // Check primary result annotation
        if matches!(inst.ty, Type::Int)
            && let Some(Annotation::Int(ia)) = &inst.result_annotation
            && ia.bit_width > legality.max_int_width()
        {
            return true;
        }
        // Check secondary result annotation
        if let Some(ref ty) = inst.secondary_ty {
            if is_wide_width(type_width(ty), legality) {
                return true;
            }
            if matches!(ty, Type::Int)
                && let Some(Annotation::Int(ia)) = &inst.secondary_result_annotation
                && ia.bit_width > legality.max_int_width()
            {
                return true;
            }
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
            Op::BitReverse(_, bits) if *bits > legality.max_int_width() => return true,
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
            // FMaxNum/FMinNum always need legalization for IEEE NaN handling
            Op::FMaxNum(..) | Op::FMinNum(..) => return true,
            // A call with any 128-bit annotated argument needs legalization to
            // split it into (lo, hi) even when the value fits in 64 bits.
            Op::Call(_, args, _) if args.iter().any(|a| is_128_bit_value(func, a.value)) => {
                return true;
            }
            _ => {}
        }
    }

    // Check for wide-return calls
    for (i, _) in func.inst_pool.iter_insts() {
        if metadata.is_wide_return_call(i) {
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
    for (_, inst) in func.inst_pool.iter_insts() {
        if is_128_bit_int(&inst.ty) {
            return true;
        }
        match &inst.op {
            Op::Load(_, 16, _) | Op::Store(_, _, 16, _) => return true,
            Op::Sext(_, 128) | Op::Zext(_, 128) => return true,
            Op::Bswap(_, 16) => return true,
            Op::RotateLeft(_, _, 128) | Op::RotateRight(_, _, 128) => return true,
            Op::BitReverse(_, 128) => return true,
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
        let ann = old.param_annotations.get(i).cloned().flatten();
        let param_is_wide =
            is_wide_width(type_width(ty), legality) || is_128_bit_int_with_annotation(ty, &ann);
        if param_is_wide {
            let lo_idx = params.len() as u32;
            params.push(Type::Int);
            param_anns.push(Some(Annotation::Int(IntAnnotation {
                bit_width: legality.max_int_width(),
                signedness: IntSignedness::Unsigned,
            })));
            param_names.push(name);
            let hi_idx = params.len() as u32;
            params.push(Type::Int);
            param_anns.push(Some(Annotation::Int(IntAnnotation {
                bit_width: legality.max_int_width(),
                signedness: IntSignedness::Unsigned,
            })));
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
        if is_wide_width(type_width(ty), legality)
            || is_128_bit_int_with_annotation(ty, &old.ret_annotation)
        {
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
    for (i, inst) in old.inst_pool.iter_insts() {
        let vref = ValueRef::inst_result(i);
        if is_wide_width(type_width(&inst.ty), legality)
            || is_128_bit_int_with_annotation(&inst.ty, &inst.result_annotation)
        {
            wide.insert(vref.raw());
            continue;
        }
        // Calls returning wide values are marked in ABI metadata
        if meta.is_wide_return_call(i) {
            let sec = ValueRef::inst_secondary_result(i);
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
            Op::BitReverse(_, bits) if *bits > legality.max_int_width() => {
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
            Op::Shr(a, _) if is_128_bit_value(old, a.clone().raw().value) => {
                wide.insert(vref.raw());
            }
            _ => {}
        }
    }

    // Scan branches to find 128-bit block args.
    for (_, inst) in old.inst_pool.iter_insts() {
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
        let is_unsigned = value_annotation(old, op.value).is_some_and(
            |ann| matches!(ann, Annotation::Int(ia) if matches!(ia.signedness, IntSignedness::Unsigned)),
        );
        let hi = if is_unsigned {
            // Zero-extend: unsigned values always have hi = 0 in their 128-bit form.
            b.iconst(0i64, 64, IntSignedness::Unsigned, o()).raw()
        } else {
            // Sign-extend: for positive values hi=0 (same as zero-extend); for negative
            // values (e.g. iconst(-1) used as all-ones in a 128-bit XOR) hi=-1.
            let c63 = b.iconst(63i64, 64, IntSignedness::Unsigned, o());
            b.shr(lo.into(), c63.into(), SIGNED_64_INT, o()).raw()
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
                let ba_ann = old.block_args[old_ba_idx as usize].annotation;

                if s.wide.contains(&old_ba_ref.raw()) {
                    let lo = b.add_block_arg(new_blk, I64_TYPE, Some(Annotation::Int(I64)));
                    let hi = b.add_block_arg(new_blk, I64_TYPE, Some(Annotation::Int(I64)));
                    s.vmap.set(old_ba_ref, Mapped::Pair(lo, hi));
                } else {
                    let v = b.add_block_arg(new_blk, ba_ty, ba_ann);
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
    let wide_result = is_wide(s, old_vref);

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
        Op::Const(val) if needs_wide_const(val) || is_wide(s, old_vref) => {
            leg_wide_const(s, b, old_vref, val);
        }
        Op::Add(a, op_b) if wide_result => {
            leg_add(old, s, b, old_vref, &a.clone().raw(), &op_b.clone().raw());
        }
        Op::Sub(a, op_b) if wide_result => {
            leg_sub(old, s, b, old_vref, &a.clone().raw(), &op_b.clone().raw());
        }
        Op::Mul(a, op_b) if wide_result => {
            leg_mul(old, s, b, old_vref, &a.clone().raw(), &op_b.clone().raw());
        }
        Op::Div(a, op_b) if wide_result => {
            leg_div_rem_128(
                old,
                s,
                b,
                old_vref,
                &a.clone().raw(),
                &op_b.clone().raw(),
                None,
                true,
                symbols,
            );
        }
        Op::Rem(a, op_b) if wide_result => {
            leg_div_rem_128(
                old,
                s,
                b,
                old_vref,
                &a.clone().raw(),
                &op_b.clone().raw(),
                None,
                false,
                symbols,
            );
        }
        Op::And(a, op_b) if wide_result => {
            leg_bitwise(
                old,
                s,
                b,
                old_vref,
                &a.clone().raw(),
                &op_b.clone().raw(),
                BitwiseKind::And,
            );
        }
        Op::Or(a, op_b) if wide_result => {
            leg_bitwise(
                old,
                s,
                b,
                old_vref,
                &a.clone().raw(),
                &op_b.clone().raw(),
                BitwiseKind::Or,
            );
        }
        Op::Xor(a, op_b) if wide_result => {
            leg_bitwise(
                old,
                s,
                b,
                old_vref,
                &a.clone().raw(),
                &op_b.clone().raw(),
                BitwiseKind::Xor,
            );
        }
        Op::Shl(a, op_b) if wide_result => {
            leg_shl(
                old,
                s,
                b,
                old_vref,
                &a.clone().raw(),
                &op_b.clone().raw(),
                None,
            );
        }
        Op::Shr(a, op_b) if wide_result || is_128_bit_value(old, a.clone().raw().value) => {
            leg_shr(
                old,
                s,
                b,
                old_vref,
                &a.clone().raw(),
                &op_b.clone().raw(),
                a.clone().raw().annotation.as_ref(),
            );
        }
        Op::RotateLeft(a, amt, bits) if wide_result && *bits > 64 => {
            leg_rotate_128(
                old,
                s,
                b,
                old_vref,
                &a.clone().raw(),
                &amt.clone().raw(),
                true,
            );
        }
        Op::RotateRight(a, amt, bits) if wide_result && *bits > 64 => {
            leg_rotate_128(
                old,
                s,
                b,
                old_vref,
                &a.clone().raw(),
                &amt.clone().raw(),
                false,
            );
        }
        Op::BitReverse(a, bits) if wide_result && *bits > 64 => {
            leg_bit_reverse_128(old, s, b, old_vref, &a.clone().raw());
        }
        Op::ICmp(cmp_op, a, op_b)
            if is_wide(s, a.clone().raw().value)
                || is_128_bit_value(old, a.clone().raw().value) =>
        {
            leg_icmp(
                old,
                s,
                b,
                old_vref,
                *cmp_op,
                &a.clone().raw(),
                &op_b.clone().raw(),
            );
        }
        Op::Load(ptr, 16, mem) => {
            leg_load_128(s, b, old_vref, &ptr.clone().raw(), &mem.clone().raw());
        }
        Op::Load(ptr, bytes, mem) if *bytes > 8 && *bytes < 16 => {
            // 9–15 byte load: split into an 8-byte lo load and a
            // (bytes-8)-byte hi load, yielding a (lo, hi) Pair so that
            // downstream wide stores receive the correct halves.
            let hi_bytes = bytes - 8;
            let p = s.vmap.one(ptr.clone().raw().value);
            let m = s.vmap.one(mem.clone().raw().value);
            let lo = b.load(p.into(), 8, I64_TYPE, m.into(), None, o());
            let c8 = b.iconst(8i64, 64, IntSignedness::Unsigned, o());
            let p_hi = b.ptradd(p.into(), c8.raw().into(), 0, o());
            let hi = b.load(p_hi.into(), hi_bytes, I64_TYPE, m.into(), None, o());
            s.vmap.set(old_vref, Mapped::Pair(lo, hi));
        }
        Op::Store(val, ptr, 16, mem) => {
            leg_store_128(
                old,
                s,
                b,
                old_vref,
                val,
                &ptr.clone().raw(),
                &mem.clone().raw(),
            );
        }
        // 9–15 byte stores where the value comes from a load.N or is a
        // (lo, hi) pair: split into 8-byte lo store + (bytes-8)-byte hi store.
        Op::Store(val, ptr, bytes, mem) if *bytes > 8 && *bytes < 16 => {
            let hi_bytes = bytes - 8;
            let p = remap_op(s, &ptr.clone().raw());
            let m = remap_op(s, &mem.clone().raw());
            if is_wide(s, val.value) {
                let (lo, hi) = s.vmap.pair(val.value);
                let m1 = b.store(Operand::new(lo), p.clone().into(), 8, m.into(), o());
                let c8 = b.iconst(8i64, 64, IntSignedness::Unsigned, o());
                let p_hi = b.ptradd(p.into(), c8.raw().into(), 0, o());
                let m2 = b.store(Operand::new(hi), p_hi.into(), hi_bytes, m1.into(), o());
                s.vmap.set(old_vref, Mapped::One(m2.into()));
            } else {
                // Check if the value is a constant (same fix as >16 path).
                let is_const = matches!(&old.inst(val.value.index()).op, Op::Const(_));
                if is_const {
                    let const_val = match &old.inst(val.value.index()).op {
                        Op::Const(v) => v.clone(),
                        _ => unreachable!(),
                    };
                    let byte_val = if const_val.is_zero() {
                        Some(0u8)
                    } else {
                        let (_, le_bytes) = const_val.to_bytes_le();
                        let first = *le_bytes.first().unwrap_or(&0);
                        if le_bytes.iter().all(|&bb| bb == first) {
                            Some(first)
                        } else {
                            None
                        }
                    };
                    if let Some(bv) = byte_val {
                        let set_val = b.iconst(bv as i64, 8, IntSignedness::Unsigned, o());
                        let count = b.iconst(*bytes as i64, 64, IntSignedness::Unsigned, o());
                        let dst_annotated = Operand::annotated(p.value, Annotation::Align(1));
                        let new_mem = b.mem_set(
                            dst_annotated.into(),
                            set_val.into(),
                            count.into(),
                            m.into(),
                            o(),
                        );
                        s.vmap.set(old_vref, Mapped::One(new_mem.into()));
                    } else {
                        // Non-uniform constant: split into word stores.
                        let (_, le_bytes) = const_val.to_bytes_le();
                        let mut cur_mem = m;
                        let num_words = (*bytes as u64).div_ceil(8);
                        for w in 0..num_words {
                            let off = w * 8;
                            let chunk = std::cmp::min(8, *bytes as u64 - off) as usize;
                            let mut word_bytes = [0u8; 8];
                            for (i, wb) in word_bytes.iter_mut().enumerate().take(chunk) {
                                let idx = off as usize + i;
                                if idx < le_bytes.len() {
                                    *wb = le_bytes[idx];
                                }
                            }
                            let word_val = u64::from_le_bytes(word_bytes);
                            let word = b.iconst(word_val as i64, 64, IntSignedness::Unsigned, o());
                            let dst_w = if w == 0 {
                                p.clone()
                            } else {
                                let off_v = b.iconst(off as i64, 64, IntSignedness::Unsigned, o());
                                Operand::new(b.ptradd(p.clone().into(), off_v.into(), 0, o()).raw())
                            };
                            cur_mem = Operand::new(
                                b.store(
                                    word.into(),
                                    dst_w.into(),
                                    chunk as u32,
                                    cur_mem.into(),
                                    o(),
                                )
                                .raw(),
                            );
                        }
                        s.vmap.set(old_vref, Mapped::One(cur_mem.value));
                    }
                } else {
                    // Value comes from a load — use mem_copy.
                    let src_ptr_op = match &old.inst(val.value.index()).op {
                        Op::Load(load_ptr, load_bytes, _) if *load_bytes >= *bytes => {
                            Some(remap_op(s, &load_ptr.clone().raw()))
                        }
                        _ => None,
                    };
                    if let Some(src_ptr) = src_ptr_op {
                        let count = b.iconst(*bytes as i64, 64, IntSignedness::Unsigned, o());
                        let dst_annotated = Operand::annotated(p.value, Annotation::Align(1));
                        let src_annotated = Operand::annotated(src_ptr.value, Annotation::Align(1));
                        let new_mem = b.mem_copy(
                            dst_annotated.into(),
                            src_annotated.into(),
                            count.into(),
                            m.into(),
                            o(),
                        );
                        s.vmap.set(old_vref, Mapped::One(new_mem.into()));
                    } else {
                        // Treat as a pointer to source data.
                        let src = remap_op(s, val);
                        let count = b.iconst(*bytes as i64, 64, IntSignedness::Unsigned, o());
                        let dst_annotated = Operand::annotated(p.value, Annotation::Align(1));
                        let src_annotated = Operand::annotated(src.value, Annotation::Align(1));
                        let new_mem = b.mem_copy(
                            dst_annotated.into(),
                            src_annotated.into(),
                            count.into(),
                            m.into(),
                            o(),
                        );
                        s.vmap.set(old_vref, Mapped::One(new_mem.into()));
                    }
                }
            }
        }
        Op::Sext(val, 128) if is_wide(s, val.clone().raw().value) => {
            // Sext/Zext from 128-bit to 128-bit is an identity: the source
            // already occupies a full (lo, hi) pair.
            let (lo, hi) = s.vmap.pair(val.clone().raw().value);
            s.vmap.set(old_vref, Mapped::Pair(lo, hi));
        }
        Op::Zext(val, 128) if is_wide(s, val.clone().raw().value) => {
            let (lo, hi) = s.vmap.pair(val.clone().raw().value);
            s.vmap.set(old_vref, Mapped::Pair(lo, hi));
        }
        Op::Sext(val, 128) => {
            // If the source is FpToSi, use the proper saturating compiler-rt call.
            let ft = get_fp_to_int_float_type(val.clone().raw().value, old);
            if let Some(ft) = ft {
                leg_fp_to_int128(s, b, old_vref, &val.clone().raw(), true, ft, old, symbols);
            } else {
                leg_sext_128(s, b, old_vref, &val.clone().raw());
            }
        }
        Op::Zext(val, 128) => {
            // If the source is FpToUi, use the proper saturating compiler-rt call.
            let ft = get_fp_to_int_float_type(val.clone().raw().value, old);
            if let Some(ft) = ft {
                leg_fp_to_int128(s, b, old_vref, &val.clone().raw(), false, ft, old, symbols);
            } else {
                leg_zext_128(s, b, old_vref, &val.clone().raw());
            }
        }
        Op::Bswap(val, 16) => {
            leg_bswap_128(s, b, old_vref, &val.clone().raw());
        }
        // 128-bit signed saturating add/sub: compute wrapping result + overflow,
        // clamp to MIN/MAX on overflow.
        Op::SignedSaturatingAdd(a, op_b, 128) => {
            leg_signed_saturating_addsub_128(
                old,
                s,
                b,
                old_vref,
                &a.clone().raw(),
                &op_b.clone().raw(),
                true,
            );
        }
        Op::SignedSaturatingSub(a, op_b, 128) => {
            leg_signed_saturating_addsub_128(
                old,
                s,
                b,
                old_vref,
                &a.clone().raw(),
                &op_b.clone().raw(),
                false,
            );
        }
        // 128-bit unsigned saturating add/sub.
        Op::SaturatingAdd(a, op_b, 128) => {
            leg_unsigned_saturating_addsub_128(
                old,
                s,
                b,
                old_vref,
                &a.clone().raw(),
                &op_b.clone().raw(),
                true,
            );
        }
        Op::SaturatingSub(a, op_b, 128) => {
            leg_unsigned_saturating_addsub_128(
                old,
                s,
                b,
                old_vref,
                &a.clone().raw(),
                &op_b.clone().raw(),
                false,
            );
        }
        Op::Select(cond, tv, fv) if wide_result => {
            leg_select_128(old, s, b, old_vref, &cond.clone().raw(), tv, fv);
        }
        Op::Ret(val, mem)
            if old
                .ret_ty
                .as_ref()
                .is_some_and(|t| is_128_bit_int_with_annotation(t, &old.ret_annotation)) =>
        {
            leg_ret(s, b, old_vref, val, &mem.clone().raw());
        }
        Op::Call(callee, args, mem) => {
            leg_call(
                old,
                s,
                b,
                old_vref,
                inst,
                &callee.clone().raw(),
                args,
                &mem.clone().raw(),
            );
        }
        Op::Br(target, args) => {
            leg_br(s, b, old_vref, *target, args);
        }
        Op::BrIf(cond, then_blk, then_args, else_blk, else_args) => {
            leg_brif(
                s,
                b,
                old_vref,
                &cond.clone().raw(),
                *then_blk,
                then_args,
                *else_blk,
                else_args,
            );
        }
        Op::Continue(args) => {
            leg_continue(s, b, old_vref, args);
        }
        Op::RegionYield(args) => {
            leg_region_yield(s, b, old_vref, args);
        }
        // Truncation from 128-bit: just use the lo half.
        Op::Sext(val, bits) if is_wide(s, val.clone().raw().value) && *bits < 128 => {
            let lo = s.vmap.one(val.clone().raw().value);
            let v = b.sext(Operand::new(lo).into(), *bits, o()).raw();
            s.vmap.set(old_vref, Mapped::One(v));
        }
        Op::Zext(val, bits) if is_wide(s, val.clone().raw().value) && *bits < 128 => {
            let lo = s.vmap.one(val.clone().raw().value);
            let v = b.zext(Operand::new(lo).into(), *bits, o()).raw();
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
        // Large struct stores (>16 bytes) where the value was NOT split into
        // a wide (lo, hi) pair.  This happens when a load.N (N > 16) result
        // passes through legalization as a single value.  Convert the
        // load→store pair into a mem_copy so all bytes are transferred.
        Op::Store(val, ptr, bytes, mem) if *bytes > 16 && !is_wide(s, val.value) => {
            let src_ptr_op = match &old.inst(val.value.index()).op {
                Op::Load(load_ptr, load_bytes, _) if *load_bytes >= *bytes => {
                    Some(remap_op(s, &load_ptr.clone().raw()))
                }
                _ => None,
            };
            if let Some(src_ptr) = src_ptr_op {
                let dst = remap_op(s, &ptr.clone().raw());
                let m = remap_op(s, &mem.clone().raw());
                let count = b.iconst(*bytes as i64, 64, IntSignedness::Unsigned, o());
                let dst_annotated = Operand::annotated(dst.value, Annotation::Align(1));
                let src_annotated = Operand::annotated(src_ptr.value, Annotation::Align(1));
                let new_mem = b.mem_copy(
                    dst_annotated.into(),
                    src_annotated.into(),
                    count.into(),
                    m.into(),
                    o(),
                );
                s.vmap.set(old_vref, Mapped::One(new_mem.into()));
                return;
            }
            // Check if the value is a constant — we can't use it as a source
            // pointer for mem_copy. Use mem_set for uniform byte patterns
            // (e.g. iconst 0 → memset 0), or split into word stores otherwise.
            let is_const = matches!(&old.inst(val.value.index()).op, Op::Const(_));
            if is_const {
                let const_val = match &old.inst(val.value.index()).op {
                    Op::Const(v) => v.clone(),
                    _ => unreachable!(),
                };
                let dst = remap_op(s, &ptr.clone().raw());
                let m = remap_op(s, &mem.clone().raw());
                // Check if all bytes are the same (common case: zero)
                let byte_val = if const_val.is_zero() {
                    Some(0u8)
                } else {
                    let (_, le_bytes) = const_val.to_bytes_le();
                    let first = *le_bytes.first().unwrap_or(&0);
                    if le_bytes.iter().all(|&b| b == first) {
                        Some(first)
                    } else {
                        None
                    }
                };
                if let Some(bv) = byte_val {
                    // Uniform byte pattern — use memset.
                    let set_val = b.iconst(bv as i64, 8, IntSignedness::Unsigned, o());
                    let count = b.iconst(*bytes as i64, 64, IntSignedness::Unsigned, o());
                    let dst_annotated = Operand::annotated(dst.value, Annotation::Align(1));
                    let new_mem = b.mem_set(
                        dst_annotated.into(),
                        set_val.into(),
                        count.into(),
                        m.into(),
                        o(),
                    );
                    s.vmap.set(old_vref, Mapped::One(new_mem.into()));
                } else {
                    // Non-uniform constant: split into 8-byte word stores.
                    let (_, le_bytes) = const_val.to_bytes_le();
                    let mut cur_mem = m;
                    let num_words = (*bytes as u64).div_ceil(8);
                    for w in 0..num_words {
                        let off = w * 8;
                        let chunk = std::cmp::min(8, *bytes as u64 - off) as usize;
                        let mut word_bytes = [0u8; 8];
                        for (i, wb) in word_bytes.iter_mut().enumerate().take(chunk) {
                            let idx = off as usize + i;
                            if idx < le_bytes.len() {
                                *wb = le_bytes[idx];
                            }
                        }
                        let word_val = u64::from_le_bytes(word_bytes);
                        let word = b.iconst(word_val as i64, 64, IntSignedness::Unsigned, o());
                        let dst_w = if w == 0 {
                            dst.clone()
                        } else {
                            let off_v = b.iconst(off as i64, 64, IntSignedness::Unsigned, o());
                            Operand::new(b.ptradd(dst.clone().into(), off_v.into(), 0, o()).raw())
                        };
                        cur_mem = Operand::new(
                            b.store(word.into(), dst_w.into(), chunk as u32, cur_mem.into(), o())
                                .raw(),
                        );
                    }
                    s.vmap.set(old_vref, Mapped::One(cur_mem.value));
                }
            } else {
                // Not from a load and not a constant — the value is a pointer
                // to the source data (e.g. result of a call returning via SRET,
                // or a stack slot). Convert to mem_copy so the backend can handle it.
                let src = remap_op(s, val);
                let dst = remap_op(s, &ptr.clone().raw());
                let m = remap_op(s, &mem.clone().raw());
                let count = b.iconst(*bytes as i64, 64, IntSignedness::Unsigned, o());
                let dst_annotated = Operand::annotated(dst.value, Annotation::Align(1));
                let src_annotated = Operand::annotated(src.value, Annotation::Align(1));
                let new_mem = b.mem_copy(
                    dst_annotated.into(),
                    src_annotated.into(),
                    count.into(),
                    m.into(),
                    o(),
                );
                s.vmap.set(old_vref, Mapped::One(new_mem.into()));
            }
        }
        Op::Store(val, ptr, bytes, mem) if is_wide(s, val.value) => {
            // For wide stores > 16 bytes (e.g. store.32 load32_result, dst),
            // a 2-word lo/hi split would lose bytes 16+.  When the stored value
            // comes directly from a load.N (N >= bytes) in the old function,
            // replace the whole pattern with a mem_copy so all bytes are copied.
            if *bytes > 16 {
                let src_ptr_op = match &old.inst(val.value.index()).op {
                    Op::Load(load_ptr, load_bytes, _) if *load_bytes >= *bytes => {
                        Some(remap_op(s, &load_ptr.clone().raw()))
                    }
                    _ => None,
                };
                if let Some(src_ptr) = src_ptr_op {
                    let dst = remap_op(s, &ptr.clone().raw());
                    let m = remap_op(s, &mem.clone().raw());
                    let count = b.iconst(*bytes as i64, 64, IntSignedness::Unsigned, o());
                    let dst_annotated = Operand::annotated(dst.value, Annotation::Align(1));
                    let src_annotated = Operand::annotated(src_ptr.value, Annotation::Align(1));
                    let new_mem = b.mem_copy(
                        dst_annotated.into(),
                        src_annotated.into(),
                        count.into(),
                        m.into(),
                        o(),
                    );
                    s.vmap.set(old_vref, Mapped::One(new_mem.into()));
                    return;
                }
            }
            let (lo, hi) = s.vmap.pair(val.value);
            let p = remap_op(s, &ptr.clone().raw());
            let m = remap_op(s, &mem.clone().raw());
            let lo_bytes = (*bytes).min(8);
            let m1 = b.store(Operand::new(lo), p.clone().into(), lo_bytes, m.into(), o());
            let hi_bytes = bytes.saturating_sub(8);
            if hi_bytes > 0 {
                let off = b.iconst(8i64, 64, IntSignedness::Unsigned, o());
                let hi_addr = b.ptradd(p.into(), off.into(), 0, o());
                let m2 = b.store(Operand::new(hi), hi_addr.into(), hi_bytes, m1.into(), o());
                s.vmap.set(old_vref, Mapped::One(m2.into()));
            } else {
                s.vmap.set(old_vref, Mapped::One(m1.into()));
            }
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
    let int_ann = match ann {
        Some(Annotation::Int(ia)) => ia,
        _ => IntAnnotation {
            bit_width: 64,
            signedness: IntSignedness::DontCare,
        },
    };
    let v = match &inst.op {
        Op::Param(idx) => b.param(*idx, inst.ty.clone(), ann, o()),
        Op::Const(val) => b
            .iconst(val.clone(), int_ann.bit_width, int_ann.signedness, o())
            .raw(),
        Op::FConst(value) => b.fconst_value(*value, o()).raw(),
        Op::BConst(val) => b.bconst(*val, o()).raw(),
        Op::Add(a, op_b) => b
            .add(
                remap_op(s, &a.clone().raw()).into(),
                remap_op(s, &op_b.clone().raw()).into(),
                int_ann,
                o(),
            )
            .raw(),
        Op::Sub(a, op_b) => b
            .sub(
                remap_op(s, &a.clone().raw()).into(),
                remap_op(s, &op_b.clone().raw()).into(),
                int_ann,
                o(),
            )
            .raw(),
        Op::Mul(a, op_b) => b
            .mul(
                remap_op(s, &a.clone().raw()).into(),
                remap_op(s, &op_b.clone().raw()).into(),
                int_ann,
                o(),
            )
            .raw(),
        Op::Div(a, op_b) => b
            .div(
                remap_op(s, &a.clone().raw()).into(),
                remap_op(s, &op_b.clone().raw()).into(),
                int_ann,
                o(),
            )
            .raw(),
        Op::Rem(a, op_b) => b
            .rem(
                remap_op(s, &a.clone().raw()).into(),
                remap_op(s, &op_b.clone().raw()).into(),
                int_ann,
                o(),
            )
            .raw(),
        Op::And(a, op_b) => b
            .and(
                remap_op(s, &a.clone().raw()).into(),
                remap_op(s, &op_b.clone().raw()).into(),
                int_ann,
                o(),
            )
            .raw(),
        Op::Or(a, op_b) => b
            .or(
                remap_op(s, &a.clone().raw()).into(),
                remap_op(s, &op_b.clone().raw()).into(),
                int_ann,
                o(),
            )
            .raw(),
        Op::Xor(a, op_b) => b
            .xor(
                remap_op(s, &a.clone().raw()).into(),
                remap_op(s, &op_b.clone().raw()).into(),
                int_ann,
                o(),
            )
            .raw(),
        Op::BAnd(a, op_b) => b
            .band(
                remap_op(s, &a.clone().raw()).into(),
                remap_op(s, &op_b.clone().raw()).into(),
                o(),
            )
            .raw(),
        Op::BOr(a, op_b) => b
            .bor(
                remap_op(s, &a.clone().raw()).into(),
                remap_op(s, &op_b.clone().raw()).into(),
                o(),
            )
            .raw(),
        Op::BXor(a, op_b) => b
            .bxor(
                remap_op(s, &a.clone().raw()).into(),
                remap_op(s, &op_b.clone().raw()).into(),
                o(),
            )
            .raw(),
        Op::Shl(a, op_b) => b
            .shl(
                remap_op(s, &a.clone().raw()).into(),
                remap_op(s, &op_b.clone().raw()).into(),
                int_ann,
                o(),
            )
            .raw(),
        Op::Shr(a, op_b) => b
            .shr(
                remap_op(s, &a.clone().raw()).into(),
                remap_op(s, &op_b.clone().raw()).into(),
                int_ann,
                o(),
            )
            .raw(),
        Op::Min(a, op_b) => b
            .min(
                remap_op(s, &a.clone().raw()).into(),
                remap_op(s, &op_b.clone().raw()).into(),
                int_ann,
                o(),
            )
            .raw(),
        Op::Max(a, op_b) => b
            .max(
                remap_op(s, &a.clone().raw()).into(),
                remap_op(s, &op_b.clone().raw()).into(),
                int_ann,
                o(),
            )
            .raw(),
        Op::CountOnes(a) => {
            let val_vref = a.clone().raw().value;
            if is_wide(s, val_vref) {
                // 128-bit popcount: popcnt64(lo) + popcnt64(hi)
                let (lo, hi) = s.vmap.pair(val_vref);
                let pop_lo = b.count_ones(lo.into(), 64, o());
                let pop_hi = b.count_ones(hi.into(), 64, o());
                b.add(pop_lo.into(), pop_hi.into(), I64, o()).raw()
            } else {
                b.count_ones(remap_op(s, &a.clone().raw()).into(), 64, o())
                    .raw()
            }
        }
        Op::CountLeadingZeros(a, bits) if *bits < 64 => {
            // Sub-64-bit CLZ: lzcnt64(val) - (64 - bits)
            let v = remap_op(s, &a.clone().raw());
            let clz = b.count_leading_zeros(v.into(), 64, 64, o());
            let adjust = b.iconst((64 - bits) as i64, 64, IntSignedness::Unsigned, o());
            b.sub(clz.into(), adjust.into(), I64, o()).raw()
        }
        Op::CountLeadingZeros(a, bits) if *bits == 64 => b
            .count_leading_zeros(remap_op(s, &a.clone().raw()).into(), 64, 64, o())
            .raw(),
        Op::CountLeadingZeros(a, bits) if *bits == 128 => {
            // 128-bit CLZ: hi == 0 ? 64 + clz64(lo) : clz64(hi)
            let val_vref = a.clone().raw().value;
            let (lo, hi) = if is_wide(s, val_vref) {
                s.vmap.pair(val_vref)
            } else {
                let v = s.vmap.one(val_vref);
                (v, b.iconst(0i64, 64, IntSignedness::Unsigned, o()).raw())
            };
            let clz_hi = b.count_leading_zeros(hi.into(), 64, 64, o());
            let clz_lo = b.count_leading_zeros(lo.into(), 64, 64, o());
            let c64 = b.iconst(64i64, 64, IntSignedness::Unsigned, o());
            let lo_adjusted = b.add(clz_lo.into(), c64.into(), I64, o());
            let c0 = b.iconst(0i64, 64, IntSignedness::Unsigned, o());
            let hi_is_zero = b.icmp(ICmpOp::Eq, hi.into(), c0.into(), o());
            b.select(
                hi_is_zero.into(),
                lo_adjusted.into(),
                clz_hi.into(),
                Type::Int,
                Some(Annotation::Int(I64)),
                o(),
            )
        }
        Op::CountLeadingZeros(a, _bits) => b
            .count_leading_zeros(remap_op(s, &a.clone().raw()).into(), 64, 64, o())
            .raw(),
        Op::CountTrailingZeros(a) => {
            let val_vref = a.clone().raw().value;
            if is_wide(s, val_vref) {
                // 128-bit CTZ: lo == 0 ? 64 + tzcnt64(hi) : tzcnt64(lo)
                let (lo, hi) = s.vmap.pair(val_vref);
                let ctz_lo = b.count_trailing_zeros(lo.into(), 64, o());
                let ctz_hi = b.count_trailing_zeros(hi.into(), 64, o());
                let c64 = b.iconst(64i64, 64, IntSignedness::Unsigned, o());
                let hi_adjusted = b.add(ctz_hi.into(), c64.into(), I64, o());
                let c0 = b.iconst(0i64, 64, IntSignedness::Unsigned, o());
                let lo_is_zero = b.icmp(ICmpOp::Eq, lo.into(), c0.into(), o());
                b.select(
                    lo_is_zero.into(),
                    hi_adjusted.into(),
                    ctz_lo.into(),
                    Type::Int,
                    Some(Annotation::Int(I64)),
                    o(),
                )
            } else {
                b.count_trailing_zeros(remap_op(s, &a.clone().raw()).into(), 64, o())
                    .raw()
            }
        }
        Op::Bswap(a, bytes) => b
            .bswap(remap_op(s, &a.clone().raw()).into(), *bytes, o())
            .raw(),
        Op::BitReverse(a, bits) => b
            .bit_reverse(remap_op(s, &a.clone().raw()).into(), *bits, o())
            .raw(),
        Op::RotateLeft(a, amt, bits) => b
            .rotate_left(
                remap_op(s, &a.clone().raw()).into(),
                remap_op(s, &amt.clone().raw()).into(),
                *bits,
                o(),
            )
            .raw(),
        Op::RotateRight(a, amt, bits) => b
            .rotate_right(
                remap_op(s, &a.clone().raw()).into(),
                remap_op(s, &amt.clone().raw()).into(),
                *bits,
                o(),
            )
            .raw(),
        Op::SaturatingAdd(a, op_b, bits) => b
            .saturating_add(
                remap_op(s, &a.clone().raw()).into(),
                remap_op(s, &op_b.clone().raw()).into(),
                *bits,
                o(),
            )
            .raw(),
        Op::SaturatingSub(a, op_b, bits) => b
            .saturating_sub(
                remap_op(s, &a.clone().raw()).into(),
                remap_op(s, &op_b.clone().raw()).into(),
                *bits,
                o(),
            )
            .raw(),
        Op::SignedSaturatingAdd(a, op_b, bits) => b
            .signed_saturating_add(
                remap_op(s, &a.clone().raw()).into(),
                remap_op(s, &op_b.clone().raw()).into(),
                *bits,
                o(),
            )
            .raw(),
        Op::SignedSaturatingSub(a, op_b, bits) => b
            .signed_saturating_sub(
                remap_op(s, &a.clone().raw()).into(),
                remap_op(s, &op_b.clone().raw()).into(),
                *bits,
                o(),
            )
            .raw(),
        Op::SAddWithOverflow(a, op_b, bits) if *bits > 64 => {
            leg_sadd_with_overflow_128(old, s, b, old_vref, &a.clone().raw(), &op_b.clone().raw());
            return;
        }
        Op::UAddWithOverflow(a, op_b, bits) if *bits > 64 => {
            leg_uadd_with_overflow_128(old, s, b, old_vref, &a.clone().raw(), &op_b.clone().raw());
            return;
        }
        Op::SSubWithOverflow(a, op_b, bits) if *bits > 64 => {
            leg_ssub_with_overflow_128(old, s, b, old_vref, &a.clone().raw(), &op_b.clone().raw());
            return;
        }
        Op::USubWithOverflow(a, op_b, bits) if *bits > 64 => {
            leg_usub_with_overflow_128(old, s, b, old_vref, &a.clone().raw(), &op_b.clone().raw());
            return;
        }
        Op::SMulWithOverflow(a, op_b, bits) if *bits > 64 => {
            leg_smul_with_overflow_128(old, s, b, old_vref, &a.clone().raw(), &op_b.clone().raw());
            return;
        }
        Op::UMulWithOverflow(a, op_b, bits) if *bits > 64 => {
            leg_umul_with_overflow_128(old, s, b, old_vref, &a.clone().raw(), &op_b.clone().raw());
            return;
        }
        Op::SAddWithOverflow(a, op_b, bits) => {
            let (primary, secondary) = b.sadd_with_overflow(
                remap_op(s, &a.clone().raw()).into(),
                remap_op(s, &op_b.clone().raw()).into(),
                *bits,
                o(),
            );
            s.vmap.set(old_vref, Mapped::One(primary.into()));
            let old_sec = ValueRef::inst_secondary_result(old_vref.index());
            s.vmap.set(old_sec, Mapped::One(secondary.into()));
            return;
        }
        Op::UAddWithOverflow(a, op_b, bits) => {
            let (primary, secondary) = b.uadd_with_overflow(
                remap_op(s, &a.clone().raw()).into(),
                remap_op(s, &op_b.clone().raw()).into(),
                *bits,
                o(),
            );
            s.vmap.set(old_vref, Mapped::One(primary.into()));
            let old_sec = ValueRef::inst_secondary_result(old_vref.index());
            s.vmap.set(old_sec, Mapped::One(secondary.into()));
            return;
        }
        Op::SSubWithOverflow(a, op_b, bits) => {
            let (primary, secondary) = b.ssub_with_overflow(
                remap_op(s, &a.clone().raw()).into(),
                remap_op(s, &op_b.clone().raw()).into(),
                *bits,
                o(),
            );
            s.vmap.set(old_vref, Mapped::One(primary.into()));
            let old_sec = ValueRef::inst_secondary_result(old_vref.index());
            s.vmap.set(old_sec, Mapped::One(secondary.into()));
            return;
        }
        Op::USubWithOverflow(a, op_b, bits) => {
            let (primary, secondary) = b.usub_with_overflow(
                remap_op(s, &a.clone().raw()).into(),
                remap_op(s, &op_b.clone().raw()).into(),
                *bits,
                o(),
            );
            s.vmap.set(old_vref, Mapped::One(primary.into()));
            let old_sec = ValueRef::inst_secondary_result(old_vref.index());
            s.vmap.set(old_sec, Mapped::One(secondary.into()));
            return;
        }
        Op::SMulWithOverflow(a, op_b, bits) => {
            let (primary, secondary) = b.smul_with_overflow(
                remap_op(s, &a.clone().raw()).into(),
                remap_op(s, &op_b.clone().raw()).into(),
                *bits,
                o(),
            );
            s.vmap.set(old_vref, Mapped::One(primary.into()));
            let old_sec = ValueRef::inst_secondary_result(old_vref.index());
            s.vmap.set(old_sec, Mapped::One(secondary.into()));
            return;
        }
        Op::UMulWithOverflow(a, op_b, bits) => {
            let (primary, secondary) = b.umul_with_overflow(
                remap_op(s, &a.clone().raw()).into(),
                remap_op(s, &op_b.clone().raw()).into(),
                *bits,
                o(),
            );
            s.vmap.set(old_vref, Mapped::One(primary.into()));
            let old_sec = ValueRef::inst_secondary_result(old_vref.index());
            s.vmap.set(old_sec, Mapped::One(secondary.into()));
            return;
        }
        Op::ICmp(cmp_op, a, op_b) => b
            .icmp(
                *cmp_op,
                remap_op(s, &a.clone().raw()).into(),
                remap_op(s, &op_b.clone().raw()).into(),
                o(),
            )
            .raw(),
        Op::FCmp(cmp_op, a, op_b) => b
            .fcmp(
                *cmp_op,
                remap_op(s, &a.clone().raw()).into(),
                remap_op(s, &op_b.clone().raw()).into(),
                o(),
            )
            .raw(),
        Op::Select(c, tv, fv) => b.select(
            remap_op(s, &c.clone().raw()).into(),
            remap_op(s, tv),
            remap_op(s, fv),
            inst.ty.clone(),
            inst.result_annotation,
            o(),
        ),
        Op::Load(ptr, bytes, mem) => {
            let data = b.load(
                remap_op(s, &ptr.clone().raw()).into(),
                *bytes,
                inst.ty.clone(),
                remap_op(s, &mem.clone().raw()).into(),
                ann,
                o(),
            );
            s.vmap.set(old_vref, Mapped::One(data));
            return;
        }
        Op::Store(val, ptr, bytes, mem) => b
            .store(
                remap_op(s, val),
                remap_op(s, &ptr.clone().raw()).into(),
                *bytes,
                remap_op(s, &mem.clone().raw()).into(),
                o(),
            )
            .raw(),
        Op::StackSlot(bytes) => b.stack_slot(*bytes, o()),
        Op::MemCopy(dst, src, count, mem) => b
            .mem_copy(
                remap_op(s, &dst.clone().raw()).into(),
                remap_op(s, &src.clone().raw()).into(),
                remap_op(s, &count.clone().raw()).into(),
                remap_op(s, &mem.clone().raw()).into(),
                o(),
            )
            .raw(),
        Op::MemMove(dst, src, count, mem) => b
            .mem_move(
                remap_op(s, &dst.clone().raw()).into(),
                remap_op(s, &src.clone().raw()).into(),
                remap_op(s, &count.clone().raw()).into(),
                remap_op(s, &mem.clone().raw()).into(),
                o(),
            )
            .raw(),
        Op::MemSet(dst, val, count, mem) => b
            .mem_set(
                remap_op(s, &dst.clone().raw()).into(),
                remap_op(s, val),
                remap_op(s, &count.clone().raw()).into(),
                remap_op(s, &mem.clone().raw()).into(),
                o(),
            )
            .raw(),
        Op::SymbolAddr(sym) => b.symbol_addr(*sym, o()).raw(),
        Op::TlsSymbolAddr(sym) => b.tls_symbol_addr(*sym, o()).raw(),
        Op::Bitcast(a) => b.bitcast(remap_op(s, a), inst.ty.clone(), ann, o()),
        Op::Sext(a, bits) => b
            .sext(remap_op(s, &a.clone().raw()).into(), *bits, o())
            .raw(),
        Op::Zext(a, bits) => b
            .zext(remap_op(s, &a.clone().raw()).into(), *bits, o())
            .raw(),
        Op::FpToSi(a) => b
            .fp_to_si(remap_op(s, &a.clone().raw()).into(), 64, o())
            .raw(),
        Op::FpToUi(a) => b
            .fp_to_ui(remap_op(s, &a.clone().raw()).into(), 64, o())
            .raw(),
        Op::SiToFp(a, ft) => {
            let is_128 = s.wide.contains(&a.clone().raw().value.raw())
                || value_annotation(old, a.clone().raw().value).is_some_and(|ann| {
                    matches!(ann, Annotation::Int(ia) if ia.bit_width == 128 && matches!(ia.signedness, IntSignedness::Signed))
                });
            if is_128 {
                leg_int128_to_fp(s, b, old_vref, &a.clone().raw(), *ft, true, symbols);
                return;
            }
            b.si_to_fp(remap_op(s, &a.clone().raw()).into(), *ft, o())
                .raw()
        }
        Op::UiToFp(a, ft) => {
            let is_128 = s.wide.contains(&a.clone().raw().value.raw())
                || value_annotation(old, a.clone().raw().value).is_some_and(|ann| {
                    matches!(ann, Annotation::Int(ia) if ia.bit_width == 128 && matches!(ia.signedness, IntSignedness::Unsigned))
                });
            if is_128 {
                leg_int128_to_fp(s, b, old_vref, &a.clone().raw(), *ft, false, symbols);
                return;
            }
            b.ui_to_fp(remap_op(s, &a.clone().raw()).into(), *ft, o())
                .raw()
        }
        Op::FpConvert(a) => {
            let ft = match &inst.ty {
                Type::Float(ft) => *ft,
                _ => tuffy_ir::types::FloatType::F64,
            };
            b.fp_convert(remap_op(s, &a.clone().raw()).into(), ft, o())
                .raw()
        }
        Op::PtrAdd(ptr, off) => b
            .ptradd(
                remap_op(s, &ptr.clone().raw()).into(),
                remap_op(s, &off.clone().raw()).into(),
                0,
                o(),
            )
            .raw(),
        Op::PtrDiff(a, op_b) => b
            .ptrdiff(
                remap_op(s, &a.clone().raw()).into(),
                remap_op(s, &op_b.clone().raw()).into(),
                64,
                o(),
            )
            .raw(),
        Op::PtrToInt(a) => b
            .ptrtoint(remap_op(s, &a.clone().raw()).into(), 64, o())
            .raw(),
        Op::PtrToAddr(a) => b
            .ptrtoaddr(remap_op(s, &a.clone().raw()).into(), 64, o())
            .raw(),
        Op::IntToPtr(a) => b
            .inttoptr(remap_op(s, &a.clone().raw()).into(), 0, o())
            .raw(),
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
            let new_ret = b.ret(rv, remap_op(s, &mem.clone().raw()).into(), o());
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
        Op::FAdd(a, op_b, flags) => b
            .fadd(
                remap_op(s, &a.clone().raw()).into(),
                remap_op(s, &op_b.clone().raw()).into(),
                *flags,
                inst.ty.clone(),
                o(),
            )
            .raw(),
        Op::FSub(a, op_b, flags) => b
            .fsub(
                remap_op(s, &a.clone().raw()).into(),
                remap_op(s, &op_b.clone().raw()).into(),
                *flags,
                inst.ty.clone(),
                o(),
            )
            .raw(),
        Op::FMul(a, op_b, flags) => b
            .fmul(
                remap_op(s, &a.clone().raw()).into(),
                remap_op(s, &op_b.clone().raw()).into(),
                *flags,
                inst.ty.clone(),
                o(),
            )
            .raw(),
        Op::FDiv(a, op_b, flags) => b
            .fdiv(
                remap_op(s, &a.clone().raw()).into(),
                remap_op(s, &op_b.clone().raw()).into(),
                *flags,
                inst.ty.clone(),
                o(),
            )
            .raw(),
        Op::FRem(a, op_b, _flags) => {
            let lhs = remap_op(s, &a.clone().raw());
            let rhs = remap_op(s, &op_b.clone().raw());
            let name = match &inst.ty {
                Type::Float(FloatType::F32) => "fmodf",
                _ => "fmod",
            };
            let sym_id = symbols.intern(name);
            let callee = b.symbol_addr(sym_id, o()).raw();
            let old_mem = s
                .current_old_mem
                .expect("FRem legalization requires a mem token in scope");
            let new_mem = s.vmap.one(old_mem);
            let (call_mem, data) = b.call(
                Operand::new(callee).into(),
                vec![Operand::new(lhs.value), Operand::new(rhs.value)],
                inst.ty.clone(),
                Operand::new(new_mem).into(),
                None,
                o(),
            );
            s.vmap.set(old_mem, Mapped::One(call_mem.into()));
            data.unwrap()
        }
        Op::FMinNum(a, op_b) => {
            let lhs: Operand = remap_op(s, &a.clone().raw());
            let rhs: Operand = remap_op(s, &op_b.clone().raw());
            let ty = inst.ty.clone();
            // IEEE 754 minNum: return non-NaN argument if one is NaN
            let b_nan = b.fcmp(FCmpOp::Uno, rhs.clone().into(), rhs.clone().into(), o());
            let a_nan = b.fcmp(FCmpOp::Uno, lhs.clone().into(), lhs.clone().into(), o());
            let cmp = b.fcmp(FCmpOp::OLe, lhs.clone().into(), rhs.clone().into(), o());
            let r1 = b.select(cmp.into(), lhs.clone(), rhs.clone(), ty.clone(), None, o());
            let r2 = b.select(b_nan.into(), lhs.clone(), r1.into(), ty.clone(), None, o());
            b.select(a_nan.into(), rhs.clone(), r2.into(), ty.clone(), None, o())
        }
        Op::FMaxNum(a, op_b) => {
            let lhs: Operand = remap_op(s, &a.clone().raw());
            let rhs: Operand = remap_op(s, &op_b.clone().raw());
            let ty = inst.ty.clone();
            // IEEE 754 maxNum: return non-NaN argument if one is NaN
            let b_nan = b.fcmp(FCmpOp::Uno, rhs.clone().into(), rhs.clone().into(), o());
            let a_nan = b.fcmp(FCmpOp::Uno, lhs.clone().into(), lhs.clone().into(), o());
            let cmp = b.fcmp(FCmpOp::OGe, lhs.clone().into(), rhs.clone().into(), o());
            let r1 = b.select(cmp.into(), lhs.clone(), rhs.clone(), ty.clone(), None, o());
            let r2 = b.select(b_nan.into(), lhs.clone(), r1.into(), ty.clone(), None, o());
            b.select(a_nan.into(), rhs.clone(), r2.into(), ty.clone(), None, o())
        }
        Op::FNeg(a) => b
            .fneg(remap_op(s, &a.clone().raw()).into(), inst.ty.clone(), o())
            .raw(),
        Op::FAbs(a) => b
            .fabs(remap_op(s, &a.clone().raw()).into(), inst.ty.clone(), o())
            .raw(),
        Op::CopySign(a, op_b) => b
            .copysign(
                remap_op(s, &a.clone().raw()).into(),
                remap_op(s, &op_b.clone().raw()).into(),
                inst.ty.clone(),
                o(),
            )
            .raw(),
        Op::LoadAtomic(ptr, ord, mem) => {
            let (primary, secondary) = b.load_atomic(
                remap_op(s, &ptr.clone().raw()).into(),
                inst.secondary_ty.clone().unwrap_or(I64_TYPE),
                *ord,
                remap_op(s, &mem.clone().raw()).into(),
                inst.result_annotation,
                o(),
            );
            s.vmap.set(old_vref, Mapped::One(primary.into()));
            let old_sec = ValueRef::inst_secondary_result(old_vref.index());
            s.vmap.set(old_sec, Mapped::One(secondary));
            return;
        }
        Op::StoreAtomic(val, ptr, ord, mem) => b
            .store_atomic(
                remap_op(s, val),
                remap_op(s, &ptr.clone().raw()).into(),
                *ord,
                remap_op(s, &mem.clone().raw()).into(),
                o(),
            )
            .raw(),
        Op::AtomicRmw(rmw_op, ptr, val, ord, mem) => {
            let (primary, secondary) = b.atomic_rmw(
                *rmw_op,
                remap_op(s, &ptr.clone().raw()).into(),
                remap_op(s, val),
                inst.secondary_ty.clone().unwrap_or(I64_TYPE),
                *ord,
                remap_op(s, &mem.clone().raw()).into(),
                inst.result_annotation,
                o(),
            );
            s.vmap.set(old_vref, Mapped::One(primary.into()));
            let old_sec = ValueRef::inst_secondary_result(old_vref.index());
            s.vmap.set(old_sec, Mapped::One(secondary));
            return;
        }
        Op::AtomicCmpXchg(ptr, exp, des, s_ord, f_ord, mem) => {
            let (primary, secondary) = b.atomic_cmpxchg(
                remap_op(s, &ptr.clone().raw()).into(),
                remap_op(s, exp),
                remap_op(s, des),
                inst.secondary_ty.clone().unwrap_or(I64_TYPE),
                *s_ord,
                *f_ord,
                remap_op(s, &mem.clone().raw()).into(),
                inst.result_annotation,
                o(),
            );
            s.vmap.set(old_vref, Mapped::One(primary.into()));
            let old_sec = ValueRef::inst_secondary_result(old_vref.index());
            s.vmap.set(old_sec, Mapped::One(secondary));
            return;
        }
        Op::Fence(ord, mem) => b
            .fence(*ord, remap_op(s, &mem.clone().raw()).into(), o())
            .raw(),
        Op::Merge(a, b_op, width) => b
            .merge(
                remap_op(s, &a.clone().raw()).into(),
                remap_op(s, &b_op.clone().raw()).into(),
                *width,
                o(),
            )
            .raw(),
        Op::Clmul(a, b_op) => b
            .clmul(
                remap_op(s, &a.clone().raw()).into(),
                remap_op(s, &b_op.clone().raw()).into(),
                o(),
            )
            .raw(),
        Op::Split(a, width) => {
            let (hi, lo) = b.split(remap_op(s, &a.clone().raw()).into(), *width, o());
            s.vmap.set(old_vref, Mapped::One(hi.into()));
            let old_sec = ValueRef::inst_secondary_result(old_vref.index());
            s.vmap.set(old_sec, Mapped::One(lo.into()));
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
    let ann64 = Some(Annotation::Int(IntAnnotation {
        bit_width: 64,
        signedness: IntSignedness::Unsigned,
    }));
    let lo = b.param(lo_idx, I64_TYPE, ann64, o());
    let hi = b.param(hi_idx, I64_TYPE, ann64, o());
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
    s.vmap.set(old_vref, Mapped::Pair(lo.raw(), hi.raw()));
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

    let lo = b.add(a_lo.into(), b_lo.into(), I64, o());
    let carry = b.icmp(ICmpOp::Lt, lo.into(), a_lo.into(), o());
    let one = b.iconst(1, 64, IntSignedness::Unsigned, o());
    let zero = b.iconst(0, 64, IntSignedness::Unsigned, o());
    let carry_int = b.select(
        carry.into(),
        one.into(),
        zero.into(),
        Type::Int,
        Some(Annotation::Int(IntAnnotation {
            bit_width: 64,
            signedness: IntSignedness::Unsigned,
        })),
        o(),
    );
    let hi_sum = b.add(a_hi.into(), b_hi.into(), I64, o());
    let hi = b.add(hi_sum.into(), carry_int.into(), I64, o());
    s.vmap.set(old_vref, Mapped::Pair(lo.raw(), hi.raw()));
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

    let lo = b.sub(a_lo.into(), b_lo.into(), I64, o());
    let borrow = b.icmp(ICmpOp::Gt, lo.into(), a_lo.into(), o());
    let one = b.iconst(1, 64, IntSignedness::Unsigned, o());
    let zero = b.iconst(0, 64, IntSignedness::Unsigned, o());
    let borrow_int = b.select(
        borrow.into(),
        one.into(),
        zero.into(),
        Type::Int,
        Some(Annotation::Int(IntAnnotation {
            bit_width: 64,
            signedness: IntSignedness::Unsigned,
        })),
        o(),
    );
    let hi_diff = b.sub(a_hi.into(), b_hi.into(), I64, o());
    let hi = b.sub(hi_diff.into(), borrow_int.into(), I64, o());
    s.vmap.set(old_vref, Mapped::Pair(lo.raw(), hi.raw()));
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

    let a0 = b.and(a_lo.into(), mask32.into(), I64, o());
    let a1 = b.shr(a_lo.into(), c32.into(), UNSIGNED_64_INT, o());
    let b0 = b.and(b_lo.into(), mask32.into(), I64, o());
    let b1 = b.shr(b_lo.into(), c32.into(), UNSIGNED_64_INT, o());

    let p0 = b.mul(a0.into(), b0.into(), I64, o());
    let p1 = b.mul(a0.into(), b1.into(), I64, o());
    let p2 = b.mul(a1.into(), b0.into(), I64, o());
    let p3 = b.mul(a1.into(), b1.into(), I64, o());

    let p0_hi = b.shr(p0.into(), c32.into(), UNSIGNED_64_INT, o());
    let mid1 = b.add(p0_hi.into(), p1.into(), I64, o());
    let carry1 = b.icmp(ICmpOp::Lt, mid1.into(), p1.into(), o());
    let one = b.iconst(1, 64, IntSignedness::Unsigned, o());
    let zero = b.iconst(0, 64, IntSignedness::Unsigned, o());
    let carry1_int = b.select(
        carry1.into(),
        one.into(),
        zero.into(),
        Type::Int,
        Some(Annotation::Int(IntAnnotation {
            bit_width: 64,
            signedness: IntSignedness::Unsigned,
        })),
        o(),
    );
    let mid = b.add(mid1.into(), p2.into(), I64, o());
    let carry2 = b.icmp(ICmpOp::Lt, mid.into(), p2.into(), o());
    let one = b.iconst(1, 64, IntSignedness::Unsigned, o());
    let zero = b.iconst(0, 64, IntSignedness::Unsigned, o());
    let carry2_int = b.select(
        carry2.into(),
        one.into(),
        zero.into(),
        Type::Int,
        Some(Annotation::Int(IntAnnotation {
            bit_width: 64,
            signedness: IntSignedness::Unsigned,
        })),
        o(),
    );
    let total_carry = b.add(carry1_int.into(), carry2_int.into(), I64, o());

    let mid_shifted = b.shl(mid.into(), c32.into(), UNSIGNED_64_INT, o());
    let p0_lo = b.and(p0.into(), mask32.into(), I64, o());
    let lo = b.or(mid_shifted.into(), p0_lo.into(), I64, o());

    let mid_hi = b.shr(mid.into(), c32.into(), UNSIGNED_64_INT, o());
    let carry_shifted = b.shl(total_carry.into(), c32.into(), UNSIGNED_64_INT, o());
    let hi = b.add(mid_hi.into(), carry_shifted.into(), I64, o());
    let hi = b.add(hi.into(), p3.into(), I64, o());
    let cross1 = b.mul(a_lo.into(), b_hi.into(), I64, o());
    let hi = b.add(hi.into(), cross1.into(), I64, o());
    let cross2 = b.mul(a_hi.into(), b_lo.into(), I64, o());
    let hi = b.add(hi.into(), cross2.into(), I64, o());

    s.vmap.set(old_vref, Mapped::Pair(lo.raw(), hi.raw()));
}

// ---------------------------------------------------------------------------
// Widening 64×64→128 multiply and arithmetic helpers
// ---------------------------------------------------------------------------

/// Compute the full 128-bit unsigned product of two 64-bit values using the
/// schoolbook 32-bit quarter method.  Returns `(lo_64, hi_64)`.
fn widening_mul_u64(b: &mut Builder, x: ValueRef, y: ValueRef) -> (ValueRef, ValueRef) {
    let c32 = b.iconst(32i64, 64, IntSignedness::Unsigned, o());
    let mask32 = b.iconst(0xFFFF_FFFFi64, 64, IntSignedness::Unsigned, o());

    let x0 = b.and(x.into(), mask32.into(), I64, o());
    let x1 = b.shr(x.into(), c32.into(), UNSIGNED_64_INT, o());
    let y0 = b.and(y.into(), mask32.into(), I64, o());
    let y1 = b.shr(y.into(), c32.into(), UNSIGNED_64_INT, o());

    let p0 = b.mul(x0.into(), y0.into(), I64, o());
    let p1 = b.mul(x0.into(), y1.into(), I64, o());
    let p2 = b.mul(x1.into(), y0.into(), I64, o());
    let p3 = b.mul(x1.into(), y1.into(), I64, o());

    let p0_hi = b.shr(p0.into(), c32.into(), UNSIGNED_64_INT, o());
    let mid1 = b.add(p0_hi.into(), p1.into(), I64, o());
    let cmp = b.icmp(ICmpOp::Lt, mid1.into(), p1.into(), o());
    let c1 = bool_to_u64(b, cmp);
    let mid = b.add(mid1.into(), p2.into(), I64, o());
    let cmp = b.icmp(ICmpOp::Lt, mid.into(), p2.into(), o());
    let c2 = bool_to_u64(b, cmp);
    let total_carry = b.add(c1.into(), c2.into(), I64, o());

    let mid_shifted = b.shl(mid.into(), c32.into(), UNSIGNED_64_INT, o());
    let p0_lo = b.and(p0.into(), mask32.into(), I64, o());
    let lo = b.or(mid_shifted.into(), p0_lo.into(), I64, o());

    let mid_hi = b.shr(mid.into(), c32.into(), UNSIGNED_64_INT, o());
    let carry_shifted = b.shl(total_carry.into(), c32.into(), UNSIGNED_64_INT, o());
    let hi = b.add(mid_hi.into(), carry_shifted.into(), I64, o());
    let hi = b.add(hi.into(), p3.into(), I64, o());

    (lo.raw(), hi.raw())
}

/// Convert a boolean value to a u64 integer (0 or 1).
fn bool_to_u64(b: &mut Builder, val: tuffy_ir::typed::BoolValue) -> ValueRef {
    let one = b.iconst(1, 64, IntSignedness::Unsigned, o());
    let zero = b.iconst(0, 64, IntSignedness::Unsigned, o());
    b.select(
        val.into(),
        one.into(),
        zero.into(),
        Type::Int,
        Some(Annotation::Int(I64)),
        o(),
    )
}

/// Add three u64 values, returning `(sum, carry)` where carry fits in 2 bits.
fn add3_u64(b: &mut Builder, x: ValueRef, y: ValueRef, z: ValueRef) -> (ValueRef, ValueRef) {
    let t1 = b.add(x.into(), y.into(), I64, o());
    let cmp = b.icmp(ICmpOp::Lt, t1.into(), y.into(), o());
    let c1 = bool_to_u64(b, cmp);
    let sum = b.add(t1.into(), z.into(), I64, o());
    let cmp = b.icmp(ICmpOp::Lt, sum.into(), z.into(), o());
    let c2 = bool_to_u64(b, cmp);
    let carry = b.add(c1.into(), c2.into(), I64, o());
    (sum.raw(), carry.raw())
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
    let lo = b.add(a_lo.into(), b_lo.into(), I64, o());
    let carry = b.icmp(ICmpOp::Lt, lo.into(), a_lo.into(), o());
    let one = b.iconst(1, 64, IntSignedness::Unsigned, o());
    let zero = b.iconst(0, 64, IntSignedness::Unsigned, o());
    let carry_int = b.select(
        carry.into(),
        one.into(),
        zero.into(),
        Type::Int,
        Some(Annotation::Int(IntAnnotation {
            bit_width: 64,
            signedness: IntSignedness::Unsigned,
        })),
        o(),
    );
    let hi_sum = b.add(a_hi.into(), b_hi.into(), I64, o());
    let hi = b.add(hi_sum.into(), carry_int.into(), I64, o());
    (lo.raw(), hi.raw(), a_hi, b_hi)
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

    let lo = b.add(a_lo.into(), b_lo.into(), I64, o());
    let lo_carry = b.icmp(ICmpOp::Lt, lo.into(), a_lo.into(), o());
    let one = b.iconst(1, 64, IntSignedness::Unsigned, o());
    let zero = b.iconst(0, 64, IntSignedness::Unsigned, o());
    let lo_carry_int = b.select(
        lo_carry.into(),
        one.into(),
        zero.into(),
        Type::Int,
        Some(Annotation::Int(IntAnnotation {
            bit_width: 64,
            signedness: IntSignedness::Unsigned,
        })),
        o(),
    );

    let hi_sum = b.add(a_hi.into(), b_hi.into(), I64, o());
    let hi_carry = b.icmp(ICmpOp::Lt, hi_sum.into(), a_hi.into(), o());
    let hi = b.add(hi_sum.into(), lo_carry_int.into(), I64, o());
    let hi_carry2 = b.icmp(ICmpOp::Lt, hi.into(), hi_sum.into(), o());
    // overflow = hi_carry OR hi_carry2
    let one = b.iconst(1, 64, IntSignedness::Unsigned, o());
    let zero = b.iconst(0, 64, IntSignedness::Unsigned, o());
    let hi_carry_int = b.select(
        hi_carry.into(),
        one.into(),
        zero.into(),
        Type::Int,
        Some(Annotation::Int(IntAnnotation {
            bit_width: 64,
            signedness: IntSignedness::Unsigned,
        })),
        o(),
    );
    let one = b.iconst(1, 64, IntSignedness::Unsigned, o());
    let zero = b.iconst(0, 64, IntSignedness::Unsigned, o());
    let hi_carry2_int = b.select(
        hi_carry2.into(),
        one.into(),
        zero.into(),
        Type::Int,
        Some(Annotation::Int(IntAnnotation {
            bit_width: 64,
            signedness: IntSignedness::Unsigned,
        })),
        o(),
    );
    let overflow_int = b.or(
        Operand::new(hi_carry_int).into(),
        Operand::new(hi_carry2_int).into(),
        I64,
        o(),
    );
    let zero_cmp = b.iconst(0, 64, IntSignedness::DontCare, o());
    let overflow = b.icmp(ICmpOp::Ne, overflow_int.into(), zero_cmp.into(), o());

    s.vmap.set(old_vref, Mapped::Pair(lo.raw(), hi.raw()));
    let old_sec = ValueRef::inst_secondary_result(old_vref.index());
    s.vmap.set(old_sec, Mapped::One(overflow.into()));
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
    let ax = b.xor(Operand::new(a_hi).into(), Operand::new(hi).into(), I64, o());
    let bx = b.xor(Operand::new(b_hi).into(), Operand::new(hi).into(), I64, o());
    let combined = b.and(ax.into(), bx.into(), SIGNED_64_INT, o());
    let zero = b.iconst(0i64, 64, IntSignedness::Signed, o());
    let overflow = b.icmp(
        ICmpOp::Lt,
        Operand::annotated(combined.raw(), Annotation::Int(SIGNED_64_INT)).into(),
        zero.into(),
        o(),
    );

    s.vmap.set(old_vref, Mapped::Pair(lo, hi));
    let old_sec = ValueRef::inst_secondary_result(old_vref.index());
    s.vmap.set(old_sec, Mapped::One(overflow.into()));
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

    let lo = b.sub(a_lo.into(), b_lo.into(), I64, o());
    let lo_borrow = b.icmp(ICmpOp::Gt, lo.into(), a_lo.into(), o());
    let one = b.iconst(1, 64, IntSignedness::Unsigned, o());
    let zero = b.iconst(0, 64, IntSignedness::Unsigned, o());
    let lo_borrow_int = b.select(
        lo_borrow.into(),
        one.into(),
        zero.into(),
        Type::Int,
        Some(Annotation::Int(IntAnnotation {
            bit_width: 64,
            signedness: IntSignedness::Unsigned,
        })),
        o(),
    );

    let hi_diff = b.sub(a_hi.into(), b_hi.into(), I64, o());
    let hi_borrow = b.icmp(ICmpOp::Gt, hi_diff.into(), a_hi.into(), o());
    let hi = b.sub(hi_diff.into(), lo_borrow_int.into(), I64, o());
    let hi_borrow2 = b.icmp(ICmpOp::Gt, hi.into(), hi_diff.into(), o());
    let one = b.iconst(1, 64, IntSignedness::Unsigned, o());
    let zero = b.iconst(0, 64, IntSignedness::Unsigned, o());
    let hi_borrow_int = b.select(
        hi_borrow.into(),
        one.into(),
        zero.into(),
        Type::Int,
        Some(Annotation::Int(IntAnnotation {
            bit_width: 64,
            signedness: IntSignedness::Unsigned,
        })),
        o(),
    );
    let one = b.iconst(1, 64, IntSignedness::Unsigned, o());
    let zero = b.iconst(0, 64, IntSignedness::Unsigned, o());
    let hi_borrow2_int = b.select(
        hi_borrow2.into(),
        one.into(),
        zero.into(),
        Type::Int,
        Some(Annotation::Int(IntAnnotation {
            bit_width: 64,
            signedness: IntSignedness::Unsigned,
        })),
        o(),
    );
    let overflow_int = b.or(
        Operand::new(hi_borrow_int).into(),
        Operand::new(hi_borrow2_int).into(),
        I64,
        o(),
    );
    let zero_cmp = b.iconst(0, 64, IntSignedness::DontCare, o());
    let overflow = b.icmp(ICmpOp::Ne, overflow_int.into(), zero_cmp.into(), o());

    s.vmap.set(old_vref, Mapped::Pair(lo.raw(), hi.raw()));
    let old_sec = ValueRef::inst_secondary_result(old_vref.index());
    s.vmap.set(old_sec, Mapped::One(overflow.into()));
}

/// 128-bit signed saturating add/sub.
/// `is_add == true` → saturating_add, `is_add == false` → saturating_sub.
fn leg_signed_saturating_addsub_128<M>(
    old: &Function,
    s: &mut State<M>,
    b: &mut Builder,
    old_vref: ValueRef,
    a: &Operand,
    op_b: &Operand,
    is_add: bool,
) {
    let (a_lo, a_hi) = wide_pair(s, old, b, a);
    let (b_lo, b_hi) = wide_pair(s, old, b, op_b);

    // Compute 128-bit wrapping result.
    let (lo, hi) = if is_add {
        let lo = b.add(a_lo.into(), b_lo.into(), I64, o());
        let carry = b.icmp(ICmpOp::Lt, lo.into(), a_lo.into(), o());
        let carry_int = bool_to_u64(b, carry);
        let hi_sum = b.add(a_hi.into(), b_hi.into(), I64, o());
        let hi = b.add(hi_sum.into(), carry_int.into(), I64, o());
        (lo.raw(), hi.raw())
    } else {
        let lo = b.sub(a_lo.into(), b_lo.into(), I64, o());
        let borrow = b.icmp(ICmpOp::Gt, lo.into(), a_lo.into(), o());
        let borrow_int = bool_to_u64(b, borrow);
        let hi_diff = b.sub(a_hi.into(), b_hi.into(), I64, o());
        let hi = b.sub(hi_diff.into(), borrow_int.into(), I64, o());
        (lo.raw(), hi.raw())
    };

    // Signed overflow: ((a_hi ^ effective_b_hi) & (a_hi ^ hi)) has sign bit set.
    // For add, effective_b_hi = ~b_hi; for sub, effective_b_hi = b_hi.
    let xor_ab = if is_add {
        // For addition: overflow when signs of a and b are the same but result differs.
        // Use (a_hi ^ b_hi) inverted, which is NOT(a_hi ^ b_hi) = a_hi XNOR b_hi.
        // Overflow = ((a_hi XNOR b_hi) & (a_hi ^ hi)).sign_bit
        // Simplify: not_xor = !(a_hi ^ b_hi); overflow = (not_xor & (a_hi ^ hi)).sign_bit < 0
        let ax = b.xor(
            Operand::new(a_hi).into(),
            Operand::new(b_hi).into(),
            I64,
            o(),
        );
        let not_mask = b.iconst(-1i64, 64, IntSignedness::Unsigned, o());
        b.xor(ax.into(), not_mask.into(), I64, o())
    } else {
        // For subtraction: overflow when signs of a and b differ.
        b.xor(
            Operand::new(a_hi).into(),
            Operand::new(b_hi).into(),
            I64,
            o(),
        )
    };
    let xor_ar = b.xor(Operand::new(a_hi).into(), Operand::new(hi).into(), I64, o());
    let combined = b.and(xor_ab.into(), xor_ar.into(), SIGNED_64_INT, o());
    let zero_s = b.iconst(0i64, 64, IntSignedness::Signed, o());
    let overflow = b.icmp(
        ICmpOp::Lt,
        Operand::annotated(combined.raw(), Annotation::Int(SIGNED_64_INT)).into(),
        zero_s.into(),
        o(),
    );

    // Saturation values: if a_hi < 0 → MIN, else → MAX.
    let a_neg = b.icmp(
        ICmpOp::Lt,
        Operand::annotated(a_hi, Annotation::Int(SIGNED_64_INT)).into(),
        zero_s.into(),
        o(),
    );
    // i128::MIN = (lo=0, hi=0x8000000000000000)
    let min_lo = b.iconst(0i64, 64, IntSignedness::Unsigned, o());
    let min_hi = b.iconst(i64::MIN, 64, IntSignedness::Unsigned, o());
    // i128::MAX = (lo=0xFFFFFFFFFFFFFFFF, hi=0x7FFFFFFFFFFFFFFF)
    let max_lo = b.iconst(-1i64, 64, IntSignedness::Unsigned, o());
    let max_hi = b.iconst(i64::MAX, 64, IntSignedness::Unsigned, o());

    let sat_lo = b.select(
        a_neg.into(),
        min_lo.into(),
        max_lo.into(),
        Type::Int,
        Some(Annotation::Int(I64)),
        o(),
    );
    let sat_hi = b.select(
        a_neg.into(),
        min_hi.into(),
        max_hi.into(),
        Type::Int,
        Some(Annotation::Int(I64)),
        o(),
    );

    // Select between saturated and wrapping result.
    let res_lo = b.select(
        overflow.into(),
        sat_lo.into(),
        Operand::new(lo),
        Type::Int,
        Some(Annotation::Int(I64)),
        o(),
    );
    let res_hi = b.select(
        overflow.into(),
        sat_hi.into(),
        Operand::new(hi),
        Type::Int,
        Some(Annotation::Int(I64)),
        o(),
    );

    s.vmap.set(old_vref, Mapped::Pair(res_lo, res_hi));
}

/// 128-bit unsigned saturating add/sub.
fn leg_unsigned_saturating_addsub_128<M>(
    old: &Function,
    s: &mut State<M>,
    b: &mut Builder,
    old_vref: ValueRef,
    a: &Operand,
    op_b: &Operand,
    is_add: bool,
) {
    let (a_lo, a_hi) = wide_pair(s, old, b, a);
    let (b_lo, b_hi) = wide_pair(s, old, b, op_b);

    if is_add {
        // Unsigned saturating add: clamp to u128::MAX on overflow.
        let lo = b.add(a_lo.into(), b_lo.into(), I64, o());
        let carry = b.icmp(ICmpOp::Lt, lo.into(), a_lo.into(), o());
        let carry_int = bool_to_u64(b, carry);
        let hi_sum = b.add(a_hi.into(), b_hi.into(), I64, o());
        let hi = b.add(hi_sum.into(), carry_int.into(), I64, o());
        // Overflow: hi < a_hi || (hi == a_hi && carry on hi_sum+carry_int)
        let hi_overflow1 = b.icmp(ICmpOp::Lt, hi_sum.into(), a_hi.into(), o());
        let hi_overflow2 = b.icmp(ICmpOp::Lt, hi.into(), hi_sum.into(), o());
        let hi_overflow_a = bool_to_u64(b, hi_overflow1);
        let hi_overflow_b = bool_to_u64(b, hi_overflow2);
        let hi_overflow_sum = b.add(hi_overflow_a.into(), hi_overflow_b.into(), I64, o());
        let zero = b.iconst(0i64, 64, IntSignedness::Unsigned, o());
        let overflow = b.icmp(ICmpOp::Ne, hi_overflow_sum.into(), zero.into(), o());
        let all_ones = b.iconst(-1i64, 64, IntSignedness::Unsigned, o());
        let res_lo = b.select(
            overflow.into(),
            all_ones.into(),
            Operand::new(lo.raw()),
            Type::Int,
            Some(Annotation::Int(I64)),
            o(),
        );
        let res_hi = b.select(
            overflow.into(),
            all_ones.into(),
            Operand::new(hi.raw()),
            Type::Int,
            Some(Annotation::Int(I64)),
            o(),
        );
        s.vmap.set(old_vref, Mapped::Pair(res_lo, res_hi));
    } else {
        // Unsigned saturating sub: clamp to 0 on underflow.
        let lo = b.sub(a_lo.into(), b_lo.into(), I64, o());
        let borrow = b.icmp(ICmpOp::Gt, lo.into(), a_lo.into(), o());
        let borrow_int = bool_to_u64(b, borrow);
        let hi_diff = b.sub(a_hi.into(), b_hi.into(), I64, o());
        let hi = b.sub(hi_diff.into(), borrow_int.into(), I64, o());
        // Underflow: b > a (unsigned 128-bit comparison)
        // b > a iff b_hi > a_hi || (b_hi == a_hi && b_lo > a_lo)
        let hi_gt = b.icmp(
            ICmpOp::Gt,
            Operand::new(b_hi).into(),
            Operand::new(a_hi).into(),
            o(),
        );
        let hi_eq = b.icmp(
            ICmpOp::Eq,
            Operand::new(b_hi).into(),
            Operand::new(a_hi).into(),
            o(),
        );
        let lo_gt = b.icmp(
            ICmpOp::Gt,
            Operand::new(b_lo).into(),
            Operand::new(a_lo).into(),
            o(),
        );
        let lo_gt_int = bool_to_u64(b, lo_gt);
        let hi_eq_int = bool_to_u64(b, hi_eq);
        let eq_and_lo = b.mul(lo_gt_int.into(), hi_eq_int.into(), I64, o());
        let hi_gt_int = bool_to_u64(b, hi_gt);
        let underflow_int = b.add(hi_gt_int.into(), eq_and_lo.into(), I64, o());
        let zero = b.iconst(0i64, 64, IntSignedness::Unsigned, o());
        let underflow = b.icmp(ICmpOp::Ne, underflow_int.into(), zero.into(), o());
        let res_lo = b.select(
            underflow.into(),
            zero.into(),
            Operand::new(lo.raw()),
            Type::Int,
            Some(Annotation::Int(I64)),
            o(),
        );
        let res_hi = b.select(
            underflow.into(),
            zero.into(),
            Operand::new(hi.raw()),
            Type::Int,
            Some(Annotation::Int(I64)),
            o(),
        );
        s.vmap.set(old_vref, Mapped::Pair(res_lo, res_hi));
    }
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
    let lo = b.sub(a_lo.into(), b_lo.into(), I64, o());
    let lo_borrow = b.icmp(ICmpOp::Gt, lo.into(), a_lo.into(), o());
    let one = b.iconst(1, 64, IntSignedness::Unsigned, o());
    let zero = b.iconst(0, 64, IntSignedness::Unsigned, o());
    let lo_borrow_int = b.select(
        lo_borrow.into(),
        one.into(),
        zero.into(),
        Type::Int,
        Some(Annotation::Int(IntAnnotation {
            bit_width: 64,
            signedness: IntSignedness::Unsigned,
        })),
        o(),
    );
    let hi_diff = b.sub(a_hi.into(), b_hi.into(), I64, o());
    let hi = b.sub(hi_diff.into(), lo_borrow_int.into(), I64, o());

    // Signed overflow for subtraction: ((a_hi ^ b_hi) & (a_hi ^ hi)) has sign bit set
    let ax = b.xor(
        Operand::new(a_hi).into(),
        Operand::new(b_hi).into(),
        I64,
        o(),
    );
    let bx = b.xor(Operand::new(a_hi).into(), hi.into(), I64, o());
    let combined = b.and(ax.into(), bx.into(), SIGNED_64_INT, o());
    let zero = b.iconst(0i64, 64, IntSignedness::Signed, o());
    let overflow = b.icmp(
        ICmpOp::Lt,
        Operand::annotated(combined.raw(), Annotation::Int(SIGNED_64_INT)).into(),
        zero.into(),
        o(),
    );

    s.vmap.set(old_vref, Mapped::Pair(lo.raw(), hi.raw()));
    let old_sec = ValueRef::inst_secondary_result(old_vref.index());
    s.vmap.set(old_sec, Mapped::One(overflow.into()));
}

fn leg_smul_with_overflow_128<M>(
    old: &Function,
    s: &mut State<M>,
    b: &mut Builder,
    old_vref: ValueRef,
    a: &Operand,
    op_b: &Operand,
) {
    // Compute the full 256-bit unsigned product, then adjust the high 128
    // bits for signed semantics and check whether they match the sign
    // extension of the low 128-bit result.
    let (a_lo, a_hi) = wide_pair(s, old, b, a);
    let (b_lo, b_hi) = wide_pair(s, old, b, op_b);

    // Four widening 64×64→128 partial products.
    let (ll_lo, ll_hi) = widening_mul_u64(b, a_lo, b_lo);
    let (lh_lo, lh_hi) = widening_mul_u64(b, a_lo, b_hi);
    let (hl_lo, hl_hi) = widening_mul_u64(b, a_hi, b_lo);
    let (hh_lo, hh_hi) = widening_mul_u64(b, a_hi, b_hi);

    // Combine into four 64-bit words of the 256-bit result:
    //   w0 = ll_lo
    //   w1 = ll_hi + lh_lo + hl_lo  (carry → c1)
    //   w2 = lh_hi + hl_hi + hh_lo + c1  (carry → c2)
    //   w3 = hh_hi + c2
    let (w1, c1) = add3_u64(b, ll_hi, lh_lo, hl_lo);
    let (w2_pre, c2_pre) = add3_u64(b, lh_hi, hl_hi, hh_lo);
    let w2_sum = b.add(w2_pre.into(), c1.into(), I64, o());
    let cmp = b.icmp(ICmpOp::Lt, w2_sum.into(), w2_pre.into(), o());
    let w2_carry = bool_to_u64(b, cmp);
    let c2 = b.add(c2_pre.into(), w2_carry.into(), I64, o());
    let w3 = b.add(hh_hi.into(), c2.into(), I64, o());

    // Low 128 bits of the product.
    let prod_lo = ll_lo;
    let prod_hi = w1;

    // Adjust unsigned high 128 bits → signed high 128 bits:
    //   signed_hi = unsigned_hi − (a<0 ? b : 0) − (b<0 ? a : 0)
    let zero = b.iconst(0, 64, IntSignedness::Unsigned, o());
    let c63 = b.iconst(63, 64, IntSignedness::Unsigned, o());

    let a_sign = b.shr(Operand::new(a_hi).into(), c63.into(), UNSIGNED_64_INT, o());
    let a_neg = b.icmp(ICmpOp::Ne, a_sign.into(), zero.into(), o());

    let b_sign = b.shr(Operand::new(b_hi).into(), c63.into(), UNSIGNED_64_INT, o());
    let b_neg = b.icmp(ICmpOp::Ne, b_sign.into(), zero.into(), o());

    let ann64 = Some(Annotation::Int(I64));
    let z = Operand::new(zero.raw());

    let sub_b_lo = b.select(
        a_neg.into(),
        Operand::new(b_lo),
        z.clone(),
        Type::Int,
        ann64,
        o(),
    );
    let sub_b_hi = b.select(
        a_neg.into(),
        Operand::new(b_hi),
        z.clone(),
        Type::Int,
        ann64,
        o(),
    );
    let sub_a_lo = b.select(
        b_neg.into(),
        Operand::new(a_lo),
        z.clone(),
        Type::Int,
        ann64,
        o(),
    );
    let sub_a_hi = b.select(b_neg.into(), Operand::new(a_hi), z, Type::Int, ann64, o());

    // 128-bit sub: (w2_sum, w3) − (sub_b_lo, sub_b_hi)
    let t_lo = b.sub(w2_sum.into(), sub_b_lo.into(), I64, o());
    let cmp = b.icmp(ICmpOp::Lt, w2_sum.into(), sub_b_lo.into(), o());
    let borrow1 = bool_to_u64(b, cmp);
    let t_hi = b.sub(w3.into(), sub_b_hi.into(), I64, o());
    let t_hi = b.sub(t_hi.into(), borrow1.into(), I64, o());

    // 128-bit sub: − (sub_a_lo, sub_a_hi)
    let s_lo = b.sub(t_lo.into(), sub_a_lo.into(), I64, o());
    let cmp = b.icmp(ICmpOp::Lt, t_lo.into(), sub_a_lo.into(), o());
    let borrow2 = bool_to_u64(b, cmp);
    let s_hi = b.sub(t_hi.into(), sub_a_hi.into(), I64, o());
    let s_hi = b.sub(s_hi.into(), borrow2.into(), I64, o());

    // Overflow iff (s_lo, s_hi) ≠ sign-extension of bit 127.
    let sign_ext = b.shr(prod_hi.into(), c63.into(), SIGNED_64_INT, o());
    let ne_lo = b.icmp(ICmpOp::Ne, s_lo.into(), sign_ext.into(), o());
    let ne_hi = b.icmp(ICmpOp::Ne, s_hi.into(), sign_ext.into(), o());
    let ne_lo_int = bool_to_u64(b, ne_lo);
    let ne_hi_int = bool_to_u64(b, ne_hi);
    let overflow_int = b.or(
        Operand::new(ne_lo_int).into(),
        Operand::new(ne_hi_int).into(),
        I64,
        o(),
    );
    let zero_cmp = b.iconst(0, 64, IntSignedness::DontCare, o());
    let overflow = b.icmp(ICmpOp::Ne, overflow_int.into(), zero_cmp.into(), o());

    s.vmap.set(old_vref, Mapped::Pair(prod_lo, prod_hi));
    let old_sec = ValueRef::inst_secondary_result(old_vref.index());
    s.vmap.set(old_sec, Mapped::One(overflow.into()));
}

fn leg_umul_with_overflow_128<M>(
    old: &Function,
    s: &mut State<M>,
    b: &mut Builder,
    old_vref: ValueRef,
    a: &Operand,
    op_b: &Operand,
) {
    // Compute the full 256-bit unsigned product.  Overflow iff the high
    // 128 bits are non-zero.
    let (a_lo, a_hi) = wide_pair(s, old, b, a);
    let (b_lo, b_hi) = wide_pair(s, old, b, op_b);

    let (ll_lo, ll_hi) = widening_mul_u64(b, a_lo, b_lo);
    let (lh_lo, lh_hi) = widening_mul_u64(b, a_lo, b_hi);
    let (hl_lo, hl_hi) = widening_mul_u64(b, a_hi, b_lo);
    let (hh_lo, hh_hi) = widening_mul_u64(b, a_hi, b_hi);

    let (w1, c1) = add3_u64(b, ll_hi, lh_lo, hl_lo);
    let (w2_pre, c2_pre) = add3_u64(b, lh_hi, hl_hi, hh_lo);
    let w2 = b.add(w2_pre.into(), c1.into(), I64, o());
    let cmp = b.icmp(ICmpOp::Lt, w2.into(), w2_pre.into(), o());
    let w2_carry = bool_to_u64(b, cmp);
    let c2 = b.add(c2_pre.into(), w2_carry.into(), I64, o());
    let w3 = b.add(hh_hi.into(), c2.into(), I64, o());

    let prod_lo = ll_lo;
    let prod_hi = w1;

    // Unsigned overflow: high 128 bits non-zero.
    let zero = b.iconst(0, 64, IntSignedness::Unsigned, o());
    let ne_lo = b.icmp(ICmpOp::Ne, w2.into(), zero.into(), o());
    let ne_hi = b.icmp(ICmpOp::Ne, w3.into(), zero.into(), o());
    let ne_lo_int = bool_to_u64(b, ne_lo);
    let ne_hi_int = bool_to_u64(b, ne_hi);
    let overflow_int = b.or(
        Operand::new(ne_lo_int).into(),
        Operand::new(ne_hi_int).into(),
        I64,
        o(),
    );
    let zero_cmp = b.iconst(0, 64, IntSignedness::DontCare, o());
    let overflow = b.icmp(ICmpOp::Ne, overflow_int.into(), zero_cmp.into(), o());

    s.vmap.set(old_vref, Mapped::Pair(prod_lo, prod_hi));
    let old_sec = ValueRef::inst_secondary_result(old_vref.index());
    s.vmap.set(old_sec, Mapped::One(overflow.into()));
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
            b.and(a_lo.into(), b_lo.into(), I64, o()),
            b.and(a_hi.into(), b_hi.into(), I64, o()),
        ),
        BitwiseKind::Or => (
            b.or(a_lo.into(), b_lo.into(), I64, o()),
            b.or(a_hi.into(), b_hi.into(), I64, o()),
        ),
        BitwiseKind::Xor => (
            b.xor(
                Operand::new(a_lo).into(),
                Operand::new(b_lo).into(),
                I64,
                o(),
            ),
            b.xor(
                Operand::new(a_hi).into(),
                Operand::new(b_hi).into(),
                I64,
                o(),
            ),
        ),
    };
    s.vmap.set(old_vref, Mapped::Pair(lo.raw(), hi.raw()));
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

    let lo_small = b.shl(a_lo.into(), amt.into(), UNSIGNED_64_INT, o());
    let hi_shifted = b.shl(a_hi.into(), amt.into(), UNSIGNED_64_INT, o());
    let comp = b.sub(c64.into(), amt.into(), I64, o());
    let lo_spill = b.shr(a_lo.into(), comp.into(), UNSIGNED_64_INT, o());
    let is_nonzero = b.icmp(ICmpOp::Ne, amt.into(), c0.into(), o());
    let lo_spill_safe = b.select(
        is_nonzero.into(),
        lo_spill.into(),
        c0.into(),
        I64_TYPE,
        Some(Annotation::Int(I64)),
        o(),
    );
    let hi_small = b.or(hi_shifted.into(), lo_spill_safe.into(), I64, o());

    let amt_minus_64 = b.sub(amt.into(), c64.into(), I64, o());
    let hi_large = b.shl(a_lo.into(), amt_minus_64.into(), UNSIGNED_64_INT, o());

    let is_large = b.icmp(ICmpOp::Ge, amt.into(), c64.into(), o());

    let lo = b.select(
        is_large.into(),
        c0.into(),
        lo_small.into(),
        I64_TYPE,
        Some(Annotation::Int(I64)),
        o(),
    );
    let hi = b.select(
        is_large.into(),
        hi_large.into(),
        hi_small.into(),
        I64_TYPE,
        Some(Annotation::Int(I64)),
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
    ann: Option<&Annotation>,
) {
    let signed = ann
        .and_then(|a| match a {
            Annotation::Int(ia) => Some(ia.signedness),
            _ => None,
        })
        .is_some_and(|s| matches!(s, IntSignedness::Signed));
    let (a_lo, a_hi) = wide_pair(s, old, b, a);
    let amt = s.vmap.one(op_b.value);

    let c0 = b.iconst(0i64, 64, IntSignedness::Unsigned, o());
    let c64 = b.iconst(64i64, 64, IntSignedness::Unsigned, o());

    let hi_ann = if signed {
        SIGNED_64_INT
    } else {
        UNSIGNED_64_INT
    };
    let hi_small = b.shr(a_hi.into(), amt.into(), hi_ann, o());
    let lo_shifted = b.shr(a_lo.into(), amt.into(), UNSIGNED_64_INT, o());
    let comp = b.sub(c64.into(), amt.into(), I64, o());
    let hi_spill = b.shl(a_hi.into(), comp.into(), UNSIGNED_64_INT, o());
    let is_nonzero = b.icmp(ICmpOp::Ne, amt.into(), c0.into(), o());
    let hi_spill_safe = b.select(
        is_nonzero.into(),
        hi_spill.into(),
        c0.into(),
        I64_TYPE,
        Some(Annotation::Int(I64)),
        o(),
    );
    let lo_small = b.or(lo_shifted.into(), hi_spill_safe.into(), I64, o());

    let amt_minus_64 = b.sub(amt.into(), c64.into(), I64, o());
    let lo_large = b.shr(a_hi.into(), amt_minus_64.into(), hi_ann, o());
    let hi_large = if signed {
        let c63 = b.iconst(63i64, 64, IntSignedness::Unsigned, o());
        b.shr(a_hi.into(), c63.into(), SIGNED_64_INT, o())
    } else {
        c0
    };

    let is_large = b.icmp(ICmpOp::Ge, amt.into(), c64.into(), o());

    let lo = b.select(
        is_large.into(),
        lo_large.into(),
        lo_small.into(),
        I64_TYPE,
        Some(Annotation::Int(I64)),
        o(),
    );
    let hi = b.select(
        is_large.into(),
        hi_large.into(),
        hi_small.into(),
        I64_TYPE,
        Some(Annotation::Int(I64)),
        o(),
    );

    s.vmap.set(old_vref, Mapped::Pair(lo, hi));
}

// ---------------------------------------------------------------------------
// 128-bit rotate (left or right)
// ---------------------------------------------------------------------------

/// Helper: compute 128-bit shl as a (lo, hi) pair without setting vmap.
fn shl_128_pair(
    b: &mut Builder,
    a_lo: ValueRef,
    a_hi: ValueRef,
    amt: ValueRef,
) -> (ValueRef, ValueRef) {
    let c0 = b.iconst(0i64, 64, IntSignedness::Unsigned, o());
    let c64 = b.iconst(64i64, 64, IntSignedness::Unsigned, o());

    let lo_small = b.shl(a_lo.into(), amt.into(), UNSIGNED_64_INT, o());
    let hi_shifted = b.shl(a_hi.into(), amt.into(), UNSIGNED_64_INT, o());
    let comp = b.sub(c64.into(), amt.into(), I64, o());
    let lo_spill = b.shr(a_lo.into(), comp.into(), UNSIGNED_64_INT, o());
    let is_nonzero = b.icmp(ICmpOp::Ne, amt.into(), c0.into(), o());
    let lo_spill_safe = b.select(
        is_nonzero.into(),
        lo_spill.into(),
        c0.into(),
        I64_TYPE,
        Some(Annotation::Int(I64)),
        o(),
    );
    let hi_small = b.or(hi_shifted.into(), lo_spill_safe.into(), I64, o());

    let amt_minus_64 = b.sub(amt.into(), c64.into(), I64, o());
    let hi_large = b.shl(a_lo.into(), amt_minus_64.into(), UNSIGNED_64_INT, o());

    let is_large = b.icmp(ICmpOp::Ge, amt.into(), c64.into(), o());

    let lo = b.select(
        is_large.into(),
        c0.into(),
        lo_small.into(),
        I64_TYPE,
        Some(Annotation::Int(I64)),
        o(),
    );
    let hi = b.select(
        is_large.into(),
        hi_large.into(),
        hi_small.into(),
        I64_TYPE,
        Some(Annotation::Int(I64)),
        o(),
    );

    (lo, hi)
}

/// Helper: compute 128-bit unsigned shr as a (lo, hi) pair without setting vmap.
fn shr_128_pair(
    b: &mut Builder,
    a_lo: ValueRef,
    a_hi: ValueRef,
    amt: ValueRef,
) -> (ValueRef, ValueRef) {
    let c0 = b.iconst(0i64, 64, IntSignedness::Unsigned, o());
    let c64 = b.iconst(64i64, 64, IntSignedness::Unsigned, o());

    let hi_small = b.shr(a_hi.into(), amt.into(), UNSIGNED_64_INT, o());
    let lo_shifted = b.shr(a_lo.into(), amt.into(), UNSIGNED_64_INT, o());
    let comp = b.sub(c64.into(), amt.into(), I64, o());
    let hi_spill = b.shl(a_hi.into(), comp.into(), UNSIGNED_64_INT, o());
    let is_nonzero = b.icmp(ICmpOp::Ne, amt.into(), c0.into(), o());
    let hi_spill_safe = b.select(
        is_nonzero.into(),
        hi_spill.into(),
        c0.into(),
        I64_TYPE,
        Some(Annotation::Int(I64)),
        o(),
    );
    let lo_small = b.or(lo_shifted.into(), hi_spill_safe.into(), I64, o());

    let amt_minus_64 = b.sub(amt.into(), c64.into(), I64, o());
    let lo_large = b.shr(a_hi.into(), amt_minus_64.into(), UNSIGNED_64_INT, o());

    let is_large = b.icmp(ICmpOp::Ge, amt.into(), c64.into(), o());

    let lo = b.select(
        is_large.into(),
        lo_large.into(),
        lo_small.into(),
        I64_TYPE,
        Some(Annotation::Int(I64)),
        o(),
    );
    let hi = b.select(
        is_large.into(),
        c0.into(),
        hi_small.into(),
        I64_TYPE,
        Some(Annotation::Int(I64)),
        o(),
    );

    (lo, hi)
}

fn leg_rotate_128<M>(
    old: &Function,
    s: &mut State<M>,
    b: &mut Builder,
    old_vref: ValueRef,
    a: &Operand,
    amt_op: &Operand,
    is_left: bool,
) {
    let (a_lo, a_hi) = wide_pair(s, old, b, a);
    let n = s.vmap.one(amt_op.value);

    // Mask shift amount to 0..127
    let c127 = b.iconst(127i64, 64, IntSignedness::Unsigned, o());
    let n_mod = b.and(n.into(), c127.into(), I64, o()).raw();

    // Complement: (128 - n_mod) & 127
    // When n_mod == 0, complement becomes 128, masked to 0 → shr by 0 = identity,
    // then shl_result | shr_result = x | x = x, which is correct.
    let c128 = b.iconst(128i64, 64, IntSignedness::Unsigned, o());
    let comp = b.sub(c128.into(), n_mod.into(), I64, o());
    let comp_mod = b.and(comp.into(), c127.into(), I64, o()).raw();

    let (fwd_lo, fwd_hi, bwd_lo, bwd_hi) = if is_left {
        let (shl_lo, shl_hi) = shl_128_pair(b, a_lo, a_hi, n_mod);
        let (shr_lo, shr_hi) = shr_128_pair(b, a_lo, a_hi, comp_mod);
        (shl_lo, shl_hi, shr_lo, shr_hi)
    } else {
        let (shr_lo, shr_hi) = shr_128_pair(b, a_lo, a_hi, n_mod);
        let (shl_lo, shl_hi) = shl_128_pair(b, a_lo, a_hi, comp_mod);
        (shr_lo, shr_hi, shl_lo, shl_hi)
    };

    let lo = b.or(fwd_lo.into(), bwd_lo.into(), I64, o());
    let hi = b.or(fwd_hi.into(), bwd_hi.into(), I64, o());

    s.vmap.set(old_vref, Mapped::Pair(lo.raw(), hi.raw()));
}

// ---------------------------------------------------------------------------
// 128-bit bit reverse
// ---------------------------------------------------------------------------

fn leg_bit_reverse_128<M>(
    old: &Function,
    s: &mut State<M>,
    b: &mut Builder,
    old_vref: ValueRef,
    a: &Operand,
) {
    let (a_lo, a_hi) = wide_pair(s, old, b, a);

    // bit_reverse(128-bit x) = swap(bit_reverse(x_hi), bit_reverse(x_lo))
    // Reverse bits in each half, then swap the halves.
    let rev_lo = b.bit_reverse(a_lo.into(), 64, o());
    let rev_hi = b.bit_reverse(a_hi.into(), 64, o());

    // Swapped: lo of result = reversed hi, hi of result = reversed lo
    s.vmap
        .set(old_vref, Mapped::Pair(rev_hi.raw(), rev_lo.raw()));
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
    let signed = is_signed_annotation(a.annotation.as_ref());

    let result = match cmp_op {
        ICmpOp::Eq => {
            // XOR-based equality: avoids ISel flag-clobbering from back-to-back cmps.
            let hi_diff = b.xor(a_hi.into(), b_hi.into(), I64, o());
            let lo_diff = b.xor(a_lo.into(), b_lo.into(), I64, o());
            let or_diff = b.or(hi_diff.into(), lo_diff.into(), I64, o());
            let zero = b.iconst(0, 64, IntSignedness::DontCare, o());
            b.icmp(ICmpOp::Eq, or_diff.into(), zero.into(), o()).raw()
        }
        ICmpOp::Ne => {
            let hi_diff = b.xor(a_hi.into(), b_hi.into(), I64, o());
            let lo_diff = b.xor(a_lo.into(), b_lo.into(), I64, o());
            let or_diff = b.or(hi_diff.into(), lo_diff.into(), I64, o());
            let zero = b.iconst(0, 64, IntSignedness::DontCare, o());
            b.icmp(ICmpOp::Ne, or_diff.into(), zero.into(), o()).raw()
        }
        ICmpOp::Lt | ICmpOp::Le | ICmpOp::Gt | ICmpOp::Ge => {
            // For signed i128: hi words carry the sign → signed comparison.
            // Lo words are magnitude bits → always unsigned comparison.
            // For unsigned u128: both halves are unsigned (no annotation needed).
            let (hi_a_op, hi_b_op): (IntOperand, IntOperand) = if signed {
                let ann = Annotation::Int(SIGNED_64_INT);
                (
                    Operand::annotated(a_hi, ann).into(),
                    Operand::annotated(b_hi, ann).into(),
                )
            } else {
                (a_hi.into(), b_hi.into())
            };
            let hi_cmp = b.icmp(cmp_op, hi_a_op, hi_b_op, o());
            let hi_eq = b.icmp(ICmpOp::Eq, a_hi.into(), b_hi.into(), o());
            // Lo comparison is always unsigned: the low 64 bits are a
            // non-negative magnitude regardless of the 128-bit signedness.
            let lo_cmp = b.icmp(cmp_op, a_lo.into(), b_lo.into(), o());
            b.select(
                hi_eq.into(),
                lo_cmp.into(),
                hi_cmp.into(),
                Type::Bool,
                None,
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

    let lo = b.load(p.into(), 8, I64_TYPE, m.into(), None, o());
    let c8 = b.iconst(8i64, 64, IntSignedness::Unsigned, o());
    let p_hi = b.ptradd(p.into(), c8.into(), 0, o());
    let hi = b.load(p_hi.into(), 8, I64_TYPE, m.into(), None, o());
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
        (lo, hi.raw())
    };
    let p = s.vmap.one(ptr.value);
    let m = s.vmap.one(mem.value);

    let mem1 = b.store(v_lo.into(), p.into(), 8, m.into(), o());
    let c8 = b.iconst(8i64, 64, IntSignedness::Unsigned, o());
    let p_hi = b.ptradd(p.into(), c8.into(), 0, o());
    let mem2 = b.store(v_hi.into(), p_hi.into(), 8, mem1.into(), o());
    s.vmap.set(old_vref, Mapped::One(mem2.into()));
}

// ---------------------------------------------------------------------------
// Sign-extend to 128: lo = original, hi = arithmetic right shift by 63
// ---------------------------------------------------------------------------

fn leg_sext_128<M>(s: &mut State<M>, b: &mut Builder, old_vref: ValueRef, val: &Operand) {
    let lo = s.vmap.one(val.value);
    let c63 = b.iconst(63i64, 64, IntSignedness::Unsigned, o());
    // Arithmetic shift right: propagate the sign bit of lo into hi.
    // Must pass a Signed annotation so the ISel emits SAR, not SHR.
    let hi = b.shr(lo.into(), c63.into(), SIGNED_64_INT, o());
    s.vmap.set(old_vref, Mapped::Pair(lo, hi.raw()));
}

// ---------------------------------------------------------------------------
// Zero-extend to 128: lo = original, hi = 0
// ---------------------------------------------------------------------------

fn leg_zext_128<M>(s: &mut State<M>, b: &mut Builder, old_vref: ValueRef, val: &Operand) {
    let lo = s.vmap.one(val.value);
    let hi = b.iconst(0i64, 64, IntSignedness::Unsigned, o());
    s.vmap.set(old_vref, Mapped::Pair(lo, hi.raw()));
}

/// If `vref` is the result of a `FpToUi` or `FpToSi` instruction in `old`,
/// return the float type of the input operand.  Returns `None` otherwise.
fn get_fp_to_int_float_type(vref: ValueRef, old: &Function) -> Option<FloatType> {
    let fp_operand = match old.inst_pool.get(vref.index()) {
        Some(node) => match &node.inst.op {
            Op::FpToUi(a) | Op::FpToSi(a) => a.clone().raw().value,
            _ => return None,
        },
        None => return None,
    };
    old.inst_pool
        .get(fp_operand.index())
        .and_then(|n| match &n.inst.ty {
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
    let fp_input_vref = match old.inst_pool.get(zext_val.value.index()) {
        Some(node) => match &node.inst.op {
            Op::FpToUi(a) | Op::FpToSi(a) => a.clone().raw().value,
            _ => {
                // Not the expected pattern; fall back to simple extend.
                let lo = s.vmap.one(zext_val.value);
                let hi = if signed {
                    let c63 = b.iconst(63i64, 64, IntSignedness::Unsigned, o());
                    b.shr(lo.into(), c63.into(), SIGNED_64_INT, o())
                } else {
                    b.iconst(0i64, 64, IntSignedness::Unsigned, o())
                };
                s.vmap.set(old_vref, Mapped::Pair(lo, hi.raw()));
                return;
            }
        },
        None => {
            let lo = s.vmap.one(zext_val.value);
            let hi = b.iconst(0i64, 64, IntSignedness::Unsigned, o());
            s.vmap.set(old_vref, Mapped::Pair(lo, hi.raw()));
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
    let callee = b.symbol_addr(sym_id, o()).raw();

    // The float value in the remapped IR.
    let float_val = s.vmap.one(fp_input_vref);

    let old_mem = s
        .current_old_mem
        .expect("float-to-i128 requires a mem token in scope");
    let new_mem = s.vmap.one(old_mem);

    let (call_mem, data) = b.call(
        Operand::new(callee).into(),
        vec![Operand::new(float_val)],
        I64_TYPE,
        Operand::new(new_mem).into(),
        None,
        o(),
    );
    let data = data.unwrap();

    s.vmap.set(old_mem, Mapped::One(call_mem.into()));

    // Record wide return: hi arrives in RDX.
    let call_idx = call_mem.index();
    s.meta.mark_call_secondary_return(call_idx);
    let hi_capture = b.iconst(0i64, 64, IntSignedness::Unsigned, o());
    s.meta
        .mark_secondary_return_capture(hi_capture.index(), call_idx);

    s.vmap.set(old_vref, Mapped::Pair(data, hi_capture.into()));
}

// ---------------------------------------------------------------------------
// 128-bit bswap: bswap each half, then swap the halves
// ---------------------------------------------------------------------------

fn leg_bswap_128<M>(s: &mut State<M>, b: &mut Builder, old_vref: ValueRef, val: &Operand) {
    let (v_lo, v_hi) = s.vmap.pair(val.value);
    let new_lo = b.bswap(v_hi.into(), 8, o());
    let new_hi = b.bswap(v_lo.into(), 8, o());
    s.vmap
        .set(old_vref, Mapped::Pair(new_lo.raw(), new_hi.raw()));
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
        Operand::new(c).into(),
        Operand::new(t_lo),
        Operand::new(f_lo),
        I64_TYPE,
        Some(Annotation::Int(I64)),
        o(),
    );
    let hi = b.select(
        Operand::new(c).into(),
        Operand::new(t_hi),
        Operand::new(f_hi),
        I64_TYPE,
        Some(Annotation::Int(I64)),
        o(),
    );
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
    let signed = is_signed_annotation(a.annotation.as_ref());
    let name = match (is_div, signed) {
        (true, true) => "__divti3",
        (true, false) => "__udivti3",
        (false, true) => "__modti3",
        (false, false) => "__umodti3",
    };
    let sym_id = symbols.intern(name);
    let callee = b.symbol_addr(sym_id, o()).raw();

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
        Operand::new(callee).into(),
        args,
        I64_TYPE,
        Operand::new(new_mem).into(),
        None,
        o(),
    );
    let data = data.unwrap();

    // Redirect all subsequent users of old_mem to call_mem so that later
    // stores/calls pick up the updated mem without rewriting their operands.
    s.vmap.set(old_mem, Mapped::One(call_mem.into()));

    // Record the secondary-register return so the register allocator knows
    // that the hi half arrives in RDX.
    let call_idx = call_mem.index();
    s.meta.mark_call_secondary_return(call_idx);
    let hi_capture = b.iconst(0i64, 64, IntSignedness::Unsigned, o());
    s.meta
        .mark_secondary_return_capture(hi_capture.index(), call_idx);

    // Map the old wide Div/Rem result to (lo, hi).
    s.vmap.set(old_vref, Mapped::Pair(data, hi_capture.raw()));
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
    let callee = b.symbol_addr(sym_id, o()).raw();

    let (a_lo, a_hi) = if is_wide(s, a.value) {
        s.vmap.pair(a.value)
    } else {
        // Small 128-bit value mapped to a single 64-bit word.
        // Compute the hi word: sign-extend for i128, zero for u128.
        let lo = s.vmap.one(a.value);
        let hi = if signed {
            let c63 = b.iconst(63i64, 64, IntSignedness::Unsigned, o());
            b.shr(lo.into(), c63.into(), SIGNED_64_INT, o())
        } else {
            b.iconst(0i64, 64, IntSignedness::Unsigned, o())
        };
        (lo, hi.raw())
    };
    let args = vec![Operand::new(a_lo), Operand::new(a_hi)];

    let old_mem = s
        .current_old_mem
        .expect("128-bit to float requires a mem token in scope");
    let new_mem = s.vmap.one(old_mem);
    let (call_mem, data) = b.call(
        Operand::new(callee).into(),
        args,
        Type::Float(ft),
        Operand::new(new_mem).into(),
        None,
        o(),
    );
    let data = data.unwrap();

    s.vmap.set(old_mem, Mapped::One(call_mem.into()));
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
                b.iconst(0i64, 64, IntSignedness::Unsigned, o()).raw()
            };
            (lo, hi)
        };
        let ret_inst = b.ret(Some(Operand::new(lo)), Operand::new(m).into(), o());
        let ret_idx = ret_inst.index();
        s.meta.mark_secondary_return_move(ret_idx, hi.index());
        s.vmap.set(old_vref, Mapped::One(ret_inst));
    } else {
        let v = b.ret(None, Operand::new(m).into(), o());
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
            } else if is_signed_annotation(arg.annotation.as_ref()) {
                let c63 = b.iconst(63i64, 64, IntSignedness::Unsigned, o());
                b.shr(
                    Operand::new(lo.value).into(),
                    c63.into(),
                    SIGNED_64_INT,
                    o(),
                )
            } else {
                b.iconst(0i64, 64, IntSignedness::Unsigned, o())
            };
            new_args.push(Operand::new(lo.value));
            new_args.push(Operand::new(hi.raw()));
        } else {
            new_args.push(remap_op(s, arg));
        }
    }

    let wide_ret = is_128_bit_int_with_annotation(
        inst.secondary_ty.as_ref().unwrap_or(&Type::Unit),
        &inst.secondary_result_annotation,
    ) || s.old_meta.is_wide_return_call(old_vref.index());
    let ret_ty = if wide_ret {
        I64_TYPE
    } else {
        inst.secondary_ty.clone().unwrap_or(Type::Unit)
    };

    let ann = if wide_ret {
        None
    } else {
        inst.result_annotation
    };

    let (mem_out, data_out) = b.call(c.into(), new_args, ret_ty, m.into(), ann, o());
    s.vmap.set(old_vref, Mapped::One(mem_out.into()));

    if wide_ret {
        if let Some(data) = data_out {
            let call_idx = mem_out.index();
            s.meta.mark_call_secondary_return(call_idx);

            let hi_capture = b.iconst(0i64, 64, IntSignedness::Unsigned, o());
            let hi_idx = hi_capture.index();
            s.meta.mark_secondary_return_capture(hi_idx, call_idx);

            s.vmap.set(
                ValueRef::inst_secondary_result(old_vref.index()),
                Mapped::Pair(data, hi_capture.into()),
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
                s.vmap.set(old_cap_vref, Mapped::One(rdx_capture.into()));
                s.rdx_capture_remap.insert(old_cap_idx, rdx_capture.into());
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
    let v = b.brif(
        c.into(),
        new_then,
        new_then_args,
        new_else,
        new_else_args,
        o(),
    );
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
