//! Wide-integer type legalization pass.
//!
//! Splits integer operations wider than the target's native register width
//! into pairs of narrower operations before instruction selection.
//! Target-independent apart from the target legality information.
//! Any backend-visible ABI glue is expressed directly in IR (`call_ret2`,
//! secondary `ret` operand), not through a side metadata channel.

use std::collections::{HashMap, HashSet};

use num_bigint::BigInt;
use num_traits::{ToPrimitive, Zero};

use tuffy_ir::builder::Builder;
use tuffy_ir::function::{CfgNode, Function};
use tuffy_ir::instruction::{FCmpOp, ICmpOp, Op, Operand, Origin};
use tuffy_ir::module::SymbolTable;
use tuffy_ir::types::{Annotation, FloatType, IntAnnotation, IntSignedness, Type};
use tuffy_ir::value::{BlockRef, ValueRef};

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

#[derive(Clone)]
enum Mapped {
    One(ValueRef),
    Pair(ValueRef, ValueRef),
    Parts(Vec<ValueRef>),
}

struct VMap(HashMap<u32, Mapped>);

impl VMap {
    fn new() -> Self {
        Self(HashMap::new())
    }
    fn set(&mut self, old: ValueRef, m: Mapped) {
        self.0.insert(old.raw(), m);
    }
    fn set_parts(&mut self, old: ValueRef, parts: Vec<ValueRef>) {
        match parts.as_slice() {
            [v] => self.set(old, Mapped::One(*v)),
            [lo, hi] => self.set(old, Mapped::Pair(*lo, *hi)),
            _ => self.set(old, Mapped::Parts(parts)),
        }
    }
    fn get(&self, old: ValueRef) -> Mapped {
        self.0.get(&old.raw()).cloned().unwrap_or(Mapped::One(old))
    }
    fn one(&self, old: ValueRef) -> ValueRef {
        match self.get(old) {
            Mapped::One(v) | Mapped::Pair(v, _) => v,
            Mapped::Parts(parts) => parts[0],
        }
    }
    fn pair(&self, old: ValueRef) -> (ValueRef, ValueRef) {
        match self.get(old) {
            Mapped::Pair(lo, hi) => (lo, hi),
            Mapped::One(v) => (v, v),
            Mapped::Parts(parts) if parts.len() == 2 => (parts[0], parts[1]),
            Mapped::Parts(parts) => panic!(
                "expected 2-part mapping for value {}, got {} parts",
                old.raw(),
                parts.len()
            ),
        }
    }
    fn parts(&self, old: ValueRef) -> Vec<ValueRef> {
        match self.get(old) {
            Mapped::One(v) => vec![v],
            Mapped::Pair(lo, hi) => vec![lo, hi],
            Mapped::Parts(parts) => parts,
        }
    }
    fn remap_op(&self, op: &Operand) -> Operand {
        let v = self.one(op.value);
        match &op.annotation {
            Some(a) => Operand::annotated(v, a.clone()),
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

fn is_wide_int_with_annotation_limit(
    ty: &Type,
    ann: &Option<Annotation>,
    max_int_width: u32,
) -> bool {
    matches!(ty, Type::Int)
        && ann
            .as_ref()
            .is_some_and(|a| matches!(a, Annotation::Int(ia) if ia.bit_width > max_int_width))
}

fn is_wide_int_value_with_limit(func: &Function, v: ValueRef, max_int_width: u32) -> bool {
    let Some(ty) = value_type(func, v) else {
        return false;
    };
    matches!(ty, Type::Int)
        && int_annotation_bits(value_annotation(func, v)).is_some_and(|bits| bits > max_int_width)
}

fn is_exact_double_width_int_annotation(ann: Option<&Annotation>, part_bits: u32) -> bool {
    int_annotation_bits(ann).is_some_and(|bits| bits == part_bits * 2)
}

fn int_annotation_bits(ann: Option<&Annotation>) -> Option<u32> {
    match ann {
        Some(Annotation::Int(ia)) => Some(ia.bit_width),
        _ => None,
    }
}

fn operand_int_bits(func: &Function, op: &Operand) -> Option<u32> {
    int_annotation_bits(op.annotation.as_ref())
        .or_else(|| value_annotation(func, op.value).and_then(|ann| int_annotation_bits(Some(ann))))
}

fn compiler_rt_int_suffix(bits: u32) -> &'static str {
    match bits {
        16 => "hi",
        32 => "si",
        64 => "di",
        128 => "ti",
        _ => panic!("unsupported compiler-rt integer width: {bits}"),
    }
}

fn compiler_rt_float_suffix(ft: FloatType) -> &'static str {
    match ft {
        FloatType::F32 => "sf",
        FloatType::F64 => "df",
        _ => panic!("unsupported compiler-rt float type: {ft:?}"),
    }
}

fn fp_to_int_double_width_libcall_name(bits: u32, signed: bool, ft: FloatType) -> String {
    let int_suffix = compiler_rt_int_suffix(bits);
    let float_suffix = compiler_rt_float_suffix(ft);
    if signed {
        format!("__fix{float_suffix}{int_suffix}")
    } else {
        format!("__fixuns{float_suffix}{int_suffix}")
    }
}

fn int_to_fp_double_width_libcall_name(bits: u32, signed: bool, ft: FloatType) -> String {
    let int_suffix = compiler_rt_int_suffix(bits);
    let float_suffix = compiler_rt_float_suffix(ft);
    if signed {
        format!("__float{int_suffix}{float_suffix}")
    } else {
        format!("__floatun{int_suffix}{float_suffix}")
    }
}

fn div_rem_double_width_libcall_name(bits: u32, is_div: bool, signed: bool) -> String {
    let int_suffix = compiler_rt_int_suffix(bits);
    match (is_div, signed) {
        (true, true) => format!("__div{int_suffix}3"),
        (true, false) => format!("__udiv{int_suffix}3"),
        (false, true) => format!("__mod{int_suffix}3"),
        (false, false) => format!("__umod{int_suffix}3"),
    }
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

fn needs_wide_const(v: &BigInt) -> bool {
    !v.is_zero() && v.to_i64().is_none() && v.to_u64().is_none()
}

fn has_wide_values(func: &Function, legality: &impl LegalityInfo) -> bool {
    // Check for wide parameters
    for (ty, ann) in func.params.iter().zip(func.param_annotations.iter()) {
        if is_wide_width(type_width(ty), legality) {
            return true;
        }
        if matches!(ty, Type::Float(FloatType::F128)) {
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

    // Check for exact-double-width return type routed through ABI metadata
    if let Some(ref ty) = func.ret_ty {
        if is_wide_width(type_width(ty), legality) {
            return true;
        }
        if matches!(ty, Type::Float(FloatType::F128)) {
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
        if matches!(inst.ty, Type::Float(FloatType::F128)) {
            return true;
        }
        // Check primary result annotation
        if matches!(inst.ty, Type::Int)
            && let Some(Annotation::Int(ia)) = &inst.result_annotation.clone()
            && ia.bit_width > legality.max_int_width()
        {
            return true;
        }
        // Check secondary result annotation
        if let Some(ref ty) = inst.secondary_ty {
            if is_wide_width(type_width(ty), legality) {
                return true;
            }
            if matches!(ty, Type::Float(FloatType::F128)) {
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
            Op::FConst(fc) if fc.float_type() == FloatType::F128 => return true,
            // FMaxNum/FMinNum always need legalization for IEEE NaN handling
            Op::FMaxNum(..) | Op::FMinNum(..) => return true,
            // A call with any wide integer argument needs legalization to
            // split it into legalized parts even when the value fits in one part.
            Op::Call(_, args, _, _)
                if args.iter().any(|a| {
                    a.annotation
                        .as_ref()
                        .and_then(|ann| int_annotation_bits(Some(ann)))
                        .is_some_and(|bits| bits > legality.max_int_width())
                        || is_wide_int_value_with_limit(func, a.value, legality.max_int_width())
                }) =>
            {
                return true;
            }
            Op::SCarryingMulAdd(..) | Op::UCarryingMulAdd(..) => return true,
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
pub fn legalize(
    func: &Function,
    legality: &impl LegalityInfo,
    symbols: &mut SymbolTable,
) -> Option<Function> {
    if !has_wide_values(func, legality) {
        return None;
    }
    let (out, state) = build_new_func(func, legality);
    Some(run_legalize(func, out, state, symbols))
}

// ---------------------------------------------------------------------------
// State (separate from Function so Builder can borrow Function independently)
// ---------------------------------------------------------------------------

struct State {
    vmap: VMap,
    bmap: HashMap<u32, BlockRef>,
    /// Old param index → (new_lo_index, Option<new_hi_index>).
    param_map: Vec<(u32, Option<u32>)>,
    /// Set of old ValueRef raw values that are wider than one legal integer part.
    wide: HashSet<u32>,
    /// The most recent mem-producing old ValueRef in the current block.
    /// Used to thread the mem token when expanding a wide Div/Rem into a
    /// libcall (which requires a mem operand that the pure Div/Rem lacks).
    current_old_mem: Option<ValueRef>,
    part_bits: u32,
    limb_bits: u32,
}

fn o() -> Origin {
    Origin::synthetic()
}

fn build_new_func(old: &Function, legality: &impl LegalityInfo) -> (Function, State) {
    let mut params = Vec::new();
    let mut param_anns = Vec::new();
    let mut param_names = Vec::new();
    let mut param_map = Vec::new();

    for (i, ty) in old.params.iter().enumerate() {
        let name = old.param_names.get(i).and_then(|n| *n);
        let ann = old.param_annotations.get(i).cloned().flatten();
        let param_is_wide = is_wide_width(type_width(ty), legality)
            || is_wide_int_with_annotation_limit(ty, &ann, legality.max_int_width())
            || matches!(ty, Type::Float(FloatType::F128));
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
            || is_wide_int_with_annotation_limit(
                ty,
                &old.ret_annotation.clone(),
                legality.max_int_width(),
            )
            || matches!(ty, Type::Float(FloatType::F128))
        {
            None
        } else {
            old.ret_annotation.clone()
        }
    } else {
        old.ret_annotation.clone()
    };

    let wide = collect_wide_values(old, legality);
    let out = Function::new(old.name, params, param_anns, param_names, ret_ty, ret_ann);
    let state = State {
        vmap: VMap::new(),
        bmap: HashMap::new(),
        param_map,
        wide,
        current_old_mem: None,
        part_bits: legality.max_int_width(),
        limb_bits: (legality.max_int_width() / 2).max(1),
    };
    (out, state)
}

// ---------------------------------------------------------------------------
// Pre-scan: identify wide values in the old function
// ---------------------------------------------------------------------------

fn collect_wide_values(old: &Function, legality: &impl LegalityInfo) -> HashSet<u32> {
    let mut wide = HashSet::new();

    // Mark instructions that produce wide results.
    for (i, inst) in old.inst_pool.iter_insts() {
        let vref = ValueRef::inst_result(i);
        if is_wide_width(type_width(&inst.ty), legality)
            || is_wide_int_with_annotation_limit(
                &inst.ty,
                &inst.result_annotation.clone(),
                legality.max_int_width(),
            )
            || matches!(inst.ty, Type::Float(FloatType::F128))
        {
            wide.insert(vref.raw());
            continue;
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
            Op::SCarryingMulAdd(_, _, _, _, bits) | Op::UCarryingMulAdd(_, _, _, _, bits)
                if *bits > legality.max_int_width() =>
            {
                wide.insert(vref.raw());
                wide.insert(ValueRef::inst_secondary_result(vref.index()).raw());
            }
            Op::Shr(a, _)
                if is_wide_int_value_with_limit(
                    old,
                    a.clone().raw().value,
                    legality.max_int_width(),
                ) =>
            {
                wide.insert(vref.raw());
            }
            Op::FConst(fc) if fc.float_type() == FloatType::F128 => {
                wide.insert(vref.raw());
            }
            _ => {}
        }
    }

    // Scan branches to find wide block args.
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

fn is_wide(s: &State, v: ValueRef) -> bool {
    s.wide.contains(&v.raw()) || matches!(s.vmap.get(v), Mapped::Pair(_, _) | Mapped::Parts(_))
}

/// Returns the low/high legal-part pair for a double-width operand, correctly handling non-wide
/// values. Unlike `vmap.pair()`, which returns `(v, v)` for a non-wide value,
/// this derives the upper part from the low part:
///
/// - For `Unsigned` annotated operands, zero-extend (hi = 0).  A non-wide
///   value with `Unsigned(n)` annotation represents a u64 constant whose
///   double-width form always has the upper part equal to zero, even when the
///   value is in `[2^63, 2^64)` (i.e., bit 63 of lo is set).  Sign-extending
///   such a value would incorrectly produce hi = −1.
///
/// - For `Signed` annotated operands or unannotated ones, sign-extend
///   (hi = lo >> 63).  This handles negative constants such as `iconst(-1)`
///   used as the all-ones mask for bitwise NOT; those have annotation `None`
///   or `Signed(n)` and must propagate their sign bit into the upper half.
fn wide_pair(s: &State, old: &Function, b: &mut Builder, op: &Operand) -> (ValueRef, ValueRef) {
    if is_wide(s, op.value) {
        s.vmap.pair(op.value)
    } else {
        let lo = s.vmap.one(op.value);
        let is_unsigned = value_annotation(old, op.value).is_some_and(
            |ann| matches!(ann, Annotation::Int(ia) if matches!(ia.signedness, IntSignedness::Unsigned)),
        );
        let hi = if is_unsigned {
            // Zero-extend: unsigned values always have hi = 0 in their double-width form.
            b.iconst(0i64, 64, IntSignedness::Unsigned, o()).raw()
        } else {
            // Sign-extend: for positive values hi=0 (same as zero-extend); for negative
            // values (e.g. iconst(-1) used as an all-ones mask) hi=-1.
            let c63 = b.iconst(63i64, 64, IntSignedness::Unsigned, o());
            b.shr(lo.into(), c63.into(), SIGNED_64_INT, o()).raw()
        };
        (lo, hi)
    }
}

// ---------------------------------------------------------------------------
// Main legalization loop
// ---------------------------------------------------------------------------

fn run_legalize(
    old: &Function,
    mut out: Function,
    mut s: State,
    symbols: &mut SymbolTable,
) -> Function {
    {
        let mut b = Builder::new(&mut out);
        let old_root = old.root_region;
        let new_root = b.create_region(old.region(old_root).kind);
        b.enter_region(new_root);
        walk_region(old, &mut s, &mut b, old_root, symbols);
        b.exit_region();
    }
    out
}

fn walk_region(
    old: &Function,
    s: &mut State,
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

            let old_bb = old.block(*old_blk);
            for i in 0..old_bb.arg_count {
                let old_ba_idx = old_bb.arg_start + i;
                let old_ba_ref = ValueRef::block_arg(old_ba_idx);
                let ba_ty = old.block_args[old_ba_idx as usize].ty.clone();
                let ba_ann = old.block_args[old_ba_idx as usize].annotation.clone();

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

fn walk_block_insts(
    old: &Function,
    s: &mut State,
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
        // Keep current_old_mem up to date so that double-width div/rem legalization can
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
fn legalize_inst(
    old: &Function,
    s: &mut State,
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
            leg_wide_const(old, s, b, old_vref, val);
        }
        Op::FConst(fc) if fc.float_type() == FloatType::F128 => {
            let bits = fc.to_bits();
            let lo = b.iconst(BigInt::from(bits as u64), 64, IntSignedness::Unsigned, o());
            let hi = b.iconst(
                BigInt::from((bits >> 64) as u64),
                64,
                IntSignedness::Unsigned,
                o(),
            );
            s.vmap.set(old_vref, Mapped::Pair(lo.raw(), hi.raw()));
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
            let bits = result_bits(s, old, old_vref);
            if bits > s.part_bits * 2 && bits.is_multiple_of(s.limb_bits) {
                leg_div_rem_wide(
                    old,
                    s,
                    b,
                    old_vref,
                    &a.clone().raw(),
                    &op_b.clone().raw(),
                    true,
                );
            } else if bits == s.part_bits * 2 {
                leg_div_rem_double_width(
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
            } else {
                unimplemented!(
                    "wide div legalization for non-limb-aligned widths is not implemented"
                );
            }
        }
        Op::Rem(a, op_b) if wide_result => {
            let bits = result_bits(s, old, old_vref);
            if bits > s.part_bits * 2 && bits.is_multiple_of(s.limb_bits) {
                leg_div_rem_wide(
                    old,
                    s,
                    b,
                    old_vref,
                    &a.clone().raw(),
                    &op_b.clone().raw(),
                    false,
                );
            } else if bits == s.part_bits * 2 {
                leg_div_rem_double_width(
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
            } else {
                unimplemented!(
                    "wide rem legalization for non-limb-aligned widths is not implemented"
                );
            }
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
        Op::Shr(a, op_b)
            if wide_result
                || is_wide_int_value_with_limit(old, a.clone().raw().value, s.part_bits) =>
        {
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
            leg_rotate_wide(
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
            leg_rotate_wide(
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
            leg_bit_reverse_wide(old, s, b, old_vref, &a.clone().raw());
        }
        Op::ICmp(cmp_op, a, op_b)
            if is_wide(s, a.clone().raw().value)
                || is_wide_int_value_with_limit(old, a.clone().raw().value, s.part_bits) =>
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
        Op::Load(ptr, bytes, mem) if *bytes >= 16 => {
            leg_load_wide(
                s,
                b,
                old_vref,
                *bytes,
                &ptr.clone().raw(),
                &mem.clone().raw(),
            );
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
        Op::Store(val, ptr, bytes, mem) if *bytes >= 16 => {
            leg_store_wide(
                old,
                s,
                b,
                old_vref,
                *bytes,
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
        Op::Sext(val, bits) if *bits > s.part_bits && is_wide(s, val.clone().raw().value) => {
            let mut parts = s.vmap.parts(val.clone().raw().value);
            let src_bits = value_annotation(old, val.clone().raw().value)
                .and_then(|ann| int_annotation_bits(Some(ann)))
                .unwrap_or(s.part_bits);
            if *bits == src_bits {
                s.vmap.set_parts(old_vref, parts);
            } else {
                let fill = part_sign_fill(
                    old,
                    b,
                    &val.clone().raw(),
                    *parts.last().expect("wide sext source"),
                    s.part_bits,
                );
                while parts.len() < num_parts64(*bits, s.part_bits) {
                    parts.push(fill);
                }
                s.vmap.set_parts(old_vref, parts);
            }
        }
        Op::Zext(val, bits) if *bits > s.part_bits && is_wide(s, val.clone().raw().value) => {
            let mut parts = s.vmap.parts(val.clone().raw().value);
            if *bits
                == value_annotation(old, val.clone().raw().value)
                    .and_then(|ann| int_annotation_bits(Some(ann)))
                    .unwrap_or(s.part_bits)
            {
                s.vmap.set_parts(old_vref, parts);
            } else {
                let fill = b
                    .iconst(0i64, s.part_bits, IntSignedness::Unsigned, o())
                    .raw();
                while parts.len() < num_parts64(*bits, s.part_bits) {
                    parts.push(fill);
                }
                s.vmap.set_parts(old_vref, parts);
            }
        }
        Op::Sext(val, bits) if *bits > s.part_bits => {
            // If the source is FpToSi, use the proper saturating compiler-rt call.
            let ft = get_fp_to_int_float_type(val.clone().raw().value, old);
            if let Some(ft) = ft {
                if *bits == s.part_bits * 2 {
                    leg_fp_to_int_double_width(
                        s,
                        b,
                        old_vref,
                        &val.clone().raw(),
                        true,
                        ft,
                        old,
                        symbols,
                    );
                } else {
                    leg_fp_to_int_wide(s, b, old_vref, &val.clone().raw(), true, ft, old);
                }
            } else {
                leg_sext_wide(s, b, old_vref, *bits, &val.clone().raw());
            }
        }
        Op::Zext(val, bits) if *bits > s.part_bits => {
            // If the source is FpToUi, use the proper saturating compiler-rt call.
            let ft = get_fp_to_int_float_type(val.clone().raw().value, old);
            if let Some(ft) = ft {
                if *bits == s.part_bits * 2 {
                    leg_fp_to_int_double_width(
                        s,
                        b,
                        old_vref,
                        &val.clone().raw(),
                        false,
                        ft,
                        old,
                        symbols,
                    );
                } else {
                    leg_fp_to_int_wide(s, b, old_vref, &val.clone().raw(), false, ft, old);
                }
            } else {
                leg_zext_wide(s, b, old_vref, *bits, &val.clone().raw());
            }
        }
        Op::Bswap(val, bytes) if *bytes >= 16 => {
            leg_bswap_wide(s, b, old_vref, *bytes, &val.clone().raw());
        }
        Op::SignedSaturatingAdd(a, op_b, bits)
            if *bits > s.part_bits && bits.is_multiple_of(s.limb_bits) =>
        {
            leg_signed_saturating_addsub_wide(
                old,
                s,
                b,
                old_vref,
                &a.clone().raw(),
                &op_b.clone().raw(),
                true,
            );
        }
        Op::SignedSaturatingSub(a, op_b, bits)
            if *bits > s.part_bits && bits.is_multiple_of(s.limb_bits) =>
        {
            leg_signed_saturating_addsub_wide(
                old,
                s,
                b,
                old_vref,
                &a.clone().raw(),
                &op_b.clone().raw(),
                false,
            );
        }
        Op::SaturatingAdd(a, op_b, bits)
            if *bits > s.part_bits && bits.is_multiple_of(s.limb_bits) =>
        {
            leg_unsigned_saturating_addsub_wide(
                old,
                s,
                b,
                old_vref,
                &a.clone().raw(),
                &op_b.clone().raw(),
                true,
            );
        }
        Op::SaturatingSub(a, op_b, bits)
            if *bits > s.part_bits && bits.is_multiple_of(s.limb_bits) =>
        {
            leg_unsigned_saturating_addsub_wide(
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
            leg_select_wide(old, s, b, old_vref, &cond.clone().raw(), tv, fv);
        }
        Op::Ret(val, ret2, mem)
            if old.ret_ty.as_ref().is_some_and(|t| {
                is_wide_int_with_annotation_limit(t, &old.ret_annotation.clone(), s.part_bits)
                    || matches!(t, Type::Float(FloatType::F128))
            }) =>
        {
            leg_ret(s, b, old_vref, val, ret2, &mem.clone().raw());
        }
        Op::Call(callee, args, mem, _) => {
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
        // Truncation from a wide integer: just use the low legalized part.
        Op::Sext(val, bits) if is_wide(s, val.clone().raw().value) && *bits < s.part_bits => {
            let lo = s.vmap.one(val.clone().raw().value);
            let v = b.sext(Operand::new(lo).into(), *bits, o()).raw();
            s.vmap.set(old_vref, Mapped::One(v));
        }
        Op::Zext(val, bits) if is_wide(s, val.clone().raw().value) && *bits < s.part_bits => {
            let lo = s.vmap.one(val.clone().raw().value);
            let v = b.zext(Operand::new(lo).into(), *bits, o()).raw();
            s.vmap.set(old_vref, Mapped::One(v));
        }
        Op::Bitcast(val) if is_wide(s, val.value) => {
            let lo = s.vmap.one(val.value);
            let v = b.bitcast(
                Operand::new(lo),
                inst.ty.clone(),
                inst.result_annotation.clone(),
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
            copy_inst(old, s, b, old_vref, inst, symbols);
        }
    }
}

// ---------------------------------------------------------------------------
// Copy non-wide instruction with remapped operands
// ---------------------------------------------------------------------------

fn remap_op(s: &State, op: &Operand) -> Operand {
    s.vmap.remap_op(op)
}

fn new_block(s: &State, old: BlockRef) -> BlockRef {
    s.bmap[&old.index()]
}

#[allow(clippy::too_many_lines)]
fn copy_inst(
    old: &Function,
    s: &mut State,
    b: &mut Builder,
    old_vref: ValueRef,
    inst: &tuffy_ir::instruction::Instruction,
    symbols: &mut SymbolTable,
) {
    let ann = inst.result_annotation.clone();
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
            let bits = result_bits(s, old, old_vref);
            if is_wide(s, val_vref) && bits > s.part_bits && bits.is_multiple_of(s.limb_bits) {
                let mut total = b.iconst(0i64, 64, IntSignedness::Unsigned, o()).raw();
                for limb in operand_limbs32(old, s, b, &a.clone().raw(), bits) {
                    let cnt = b.count_ones(Operand::new(limb).into(), 64, o());
                    total = b
                        .add(Operand::new(total).into(), cnt.into(), I64, o())
                        .raw();
                }
                total
            } else if is_wide(s, val_vref) {
                // Two-part popcount: popcount(lo) + popcount(hi)
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
        Op::CountLeadingZeros(a, bits) if *bits == s.part_bits * 2 => {
            let (lo, hi) = wide_pair(s, old, b, &a.clone().raw());
            let clz_hi = b.count_leading_zeros(Operand::new(hi).into(), s.part_bits, 64, o());
            let clz_lo = b.count_leading_zeros(Operand::new(lo).into(), s.part_bits, 64, o());
            let part_bits = b.iconst(s.part_bits as i64, 64, IntSignedness::Unsigned, o());
            let zero = b.iconst(0i64, s.part_bits, IntSignedness::Unsigned, o());
            let hi_is_zero = b.icmp(ICmpOp::Eq, Operand::new(hi).into(), zero.into(), o());
            let lo_adjusted = b.add(clz_lo.into(), part_bits.into(), I64, o());
            b.select(
                hi_is_zero.into(),
                lo_adjusted.into(),
                clz_hi.into(),
                I64_TYPE,
                Some(Annotation::Int(I64)),
                o(),
            )
        }
        Op::CountLeadingZeros(a, bits)
            if *bits > s.part_bits && bits.is_multiple_of(s.limb_bits) =>
        {
            let widths = wide_limb_widths(s, *bits);
            let limbs = operand_limbs32(old, s, b, &a.clone().raw(), *bits);
            let zero64 = b.iconst(0i64, 64, IntSignedness::Unsigned, o()).raw();
            let zero32 = b
                .iconst(0i64, s.limb_bits, IntSignedness::Unsigned, o())
                .raw();
            let false_b = b.bconst(false, o());
            let mut total = zero64;
            let mut done = false_b;
            for (limb, limb_bits) in limbs.iter().copied().zip(widths).rev() {
                let limb_bits_val = b.iconst(limb_bits as i64, 64, IntSignedness::Unsigned, o());
                let limb_zero = b.icmp(
                    ICmpOp::Eq,
                    Operand::new(limb).into(),
                    Operand::new(zero32).into(),
                    o(),
                );
                let limb_clz = b
                    .count_leading_zeros(Operand::new(limb).into(), limb_bits, 64, o())
                    .raw();
                let next_zero = b
                    .add(Operand::new(total).into(), limb_bits_val.into(), I64, o())
                    .raw();
                let next_nonzero = b
                    .add(
                        Operand::new(total).into(),
                        Operand::new(limb_clz).into(),
                        I64,
                        o(),
                    )
                    .raw();
                let candidate = b.select(
                    limb_zero.into(),
                    Operand::new(next_zero),
                    Operand::new(next_nonzero),
                    I64_TYPE,
                    Some(Annotation::Int(I64)),
                    o(),
                );
                total = b.select(
                    done.into(),
                    Operand::new(total),
                    Operand::new(candidate),
                    I64_TYPE,
                    Some(Annotation::Int(I64)),
                    o(),
                );
                let limb_nonzero = b.icmp(
                    ICmpOp::Ne,
                    Operand::new(limb).into(),
                    Operand::new(zero32).into(),
                    o(),
                );
                done = b.bor(done.into(), limb_nonzero.into(), o());
            }
            total
        }
        Op::CountLeadingZeros(a, _bits) => b
            .count_leading_zeros(remap_op(s, &a.clone().raw()).into(), 64, 64, o())
            .raw(),
        Op::CountTrailingZeros(a) => {
            let val_vref = a.clone().raw().value;
            let bits = result_bits(s, old, old_vref);
            if is_wide(s, val_vref) && bits == s.part_bits * 2 {
                let (lo, hi) = s.vmap.pair(val_vref);
                let ctz_lo = b.count_trailing_zeros(lo.into(), 64, o());
                let ctz_hi = b.count_trailing_zeros(hi.into(), 64, o());
                let part_bits = b.iconst(s.part_bits as i64, 64, IntSignedness::Unsigned, o());
                let zero = b.iconst(0i64, s.part_bits, IntSignedness::Unsigned, o());
                let lo_is_zero = b.icmp(ICmpOp::Eq, lo.into(), zero.into(), o());
                let hi_adjusted = b.add(ctz_hi.into(), part_bits.into(), I64, o());
                b.select(
                    lo_is_zero.into(),
                    hi_adjusted.into(),
                    ctz_lo.into(),
                    I64_TYPE,
                    Some(Annotation::Int(I64)),
                    o(),
                )
            } else if is_wide(s, val_vref) && bits > s.part_bits && bits.is_multiple_of(s.limb_bits)
            {
                let widths = wide_limb_widths(s, bits);
                let limbs = operand_limbs32(old, s, b, &a.clone().raw(), bits);
                let zero64 = b.iconst(0i64, 64, IntSignedness::Unsigned, o()).raw();
                let zero32 = b
                    .iconst(0i64, s.limb_bits, IntSignedness::Unsigned, o())
                    .raw();
                let false_b = b.bconst(false, o());
                let mut total = zero64;
                let mut done = false_b;
                for (limb, limb_bits) in limbs.iter().copied().zip(widths) {
                    let limb_bits_val =
                        b.iconst(limb_bits as i64, 64, IntSignedness::Unsigned, o());
                    let limb_zero = b.icmp(
                        ICmpOp::Eq,
                        Operand::new(limb).into(),
                        Operand::new(zero32).into(),
                        o(),
                    );
                    let limb_ctz_raw = b
                        .count_trailing_zeros(Operand::new(limb).into(), 64, o())
                        .raw();
                    let limb_ctz = b.select(
                        limb_zero.into(),
                        limb_bits_val.into(),
                        Operand::new(limb_ctz_raw),
                        I64_TYPE,
                        Some(Annotation::Int(I64)),
                        o(),
                    );
                    let next_zero = b
                        .add(Operand::new(total).into(), limb_bits_val.into(), I64, o())
                        .raw();
                    let next_nonzero = b
                        .add(
                            Operand::new(total).into(),
                            Operand::new(limb_ctz).into(),
                            I64,
                            o(),
                        )
                        .raw();
                    let candidate = b.select(
                        limb_zero.into(),
                        Operand::new(next_zero),
                        Operand::new(next_nonzero),
                        I64_TYPE,
                        Some(Annotation::Int(I64)),
                        o(),
                    );
                    total = b.select(
                        done.into(),
                        Operand::new(total),
                        Operand::new(candidate),
                        I64_TYPE,
                        Some(Annotation::Int(I64)),
                        o(),
                    );
                    let limb_nonzero = b.icmp(
                        ICmpOp::Ne,
                        Operand::new(limb).into(),
                        Operand::new(zero32).into(),
                        o(),
                    );
                    done = b.bor(done.into(), limb_nonzero.into(), o());
                }
                total
            } else if is_wide(s, val_vref) {
                // Two-part CTZ: lo == 0 ? part_bits + ctz(hi) : ctz(lo)
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
            leg_sadd_with_overflow_wide(old, s, b, old_vref, &a.clone().raw(), &op_b.clone().raw());
            return;
        }
        Op::UAddWithOverflow(a, op_b, bits) if *bits > 64 => {
            leg_uadd_with_overflow_wide(old, s, b, old_vref, &a.clone().raw(), &op_b.clone().raw());
            return;
        }
        Op::SSubWithOverflow(a, op_b, bits) if *bits > 64 => {
            leg_ssub_with_overflow_wide(old, s, b, old_vref, &a.clone().raw(), &op_b.clone().raw());
            return;
        }
        Op::USubWithOverflow(a, op_b, bits) if *bits > 64 => {
            leg_usub_with_overflow_wide(old, s, b, old_vref, &a.clone().raw(), &op_b.clone().raw());
            return;
        }
        Op::SMulWithOverflow(a, op_b, bits) if *bits > 64 => {
            leg_smul_with_overflow_wide(old, s, b, old_vref, &a.clone().raw(), &op_b.clone().raw());
            return;
        }
        Op::UMulWithOverflow(a, op_b, bits) if *bits > 64 => {
            leg_umul_with_overflow_wide(old, s, b, old_vref, &a.clone().raw(), &op_b.clone().raw());
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
        Op::SCarryingMulAdd(a, op_b, carry, add, bits) => {
            leg_carrying_mul_add_wide(
                old,
                s,
                b,
                old_vref,
                &a.clone().raw(),
                &op_b.clone().raw(),
                &carry.clone().raw(),
                &add.clone().raw(),
                *bits,
                true,
            );
            return;
        }
        Op::UCarryingMulAdd(a, op_b, carry, add, bits) => {
            leg_carrying_mul_add_wide(
                old,
                s,
                b,
                old_vref,
                &a.clone().raw(),
                &op_b.clone().raw(),
                &carry.clone().raw(),
                &add.clone().raw(),
                *bits,
                false,
            );
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
            inst.result_annotation.clone(),
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
        Op::StackSlot(bytes, align) => b.stack_slot(*bytes, *align, o()),
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
            let a = a.clone().raw();
            let src_bits = operand_int_bits(old, &a);
            let is_wide_src =
                s.wide.contains(&a.value.raw()) || src_bits.is_some_and(|bits| bits > s.part_bits);
            if is_wide_src {
                if src_bits.is_some_and(|bits| bits > s.part_bits * 2) {
                    leg_int_to_fp_wide(old, s, b, old_vref, &a, *ft, true);
                } else {
                    leg_int_to_fp_double_width(s, b, old_vref, &a, *ft, true, symbols);
                }
                return;
            }
            b.si_to_fp(remap_op(s, &a).into(), *ft, o()).raw()
        }
        Op::UiToFp(a, ft) => {
            let a = a.clone().raw();
            let src_bits = operand_int_bits(old, &a);
            let is_wide_src =
                s.wide.contains(&a.value.raw()) || src_bits.is_some_and(|bits| bits > s.part_bits);
            if is_wide_src {
                if src_bits.is_some_and(|bits| bits > s.part_bits * 2) {
                    leg_int_to_fp_wide(old, s, b, old_vref, &a, *ft, false);
                } else {
                    leg_int_to_fp_double_width(s, b, old_vref, &a, *ft, false, symbols);
                }
                return;
            }
            b.ui_to_fp(remap_op(s, &a).into(), *ft, o()).raw()
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
        Op::Ret(val, ret2, mem) => {
            let rv = val.as_ref().map(|v| remap_op(s, v));
            let rv2 = ret2.as_ref().map(|v| remap_op(s, v));
            b.ret(rv, rv2, remap_op(s, &mem.clone().raw()).into(), o())
        }
        Op::Unreachable => b.unreachable(o()),
        Op::Trap => b.trap(o()),
        Op::LandingPad => b.landing_pad(o()),
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
                inst.result_annotation.clone(),
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
                inst.result_annotation.clone(),
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
                inst.result_annotation.clone(),
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
        Op::CallRet2(mem) => b.call_ret2(
            remap_op(s, &mem.clone().raw()).into(),
            inst.ty.clone(),
            inst.result_annotation.clone(),
            o(),
        ),
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
// Wide parameter split into legal parts
// ---------------------------------------------------------------------------

fn leg_param(s: &mut State, b: &mut Builder, old_vref: ValueRef, lo_idx: u32, hi_idx: u32) {
    let ann64 = Some(Annotation::Int(IntAnnotation {
        bit_width: 64,
        signedness: IntSignedness::Unsigned,
    }));
    let lo = b.param(lo_idx, I64_TYPE, ann64.clone(), o());
    let hi = b.param(hi_idx, I64_TYPE, ann64, o());
    s.vmap.set(old_vref, Mapped::Pair(lo, hi));
}

// ---------------------------------------------------------------------------
// Wide constant (> 64 bits)
// ---------------------------------------------------------------------------

fn leg_wide_const(
    old: &Function,
    s: &mut State,
    b: &mut Builder,
    old_vref: ValueRef,
    val: &BigInt,
) {
    let bits = value_annotation(old, old_vref)
        .and_then(|ann| int_annotation_bits(Some(ann)))
        .unwrap_or(s.part_bits * 2);
    let parts = const_parts_for_bits(b, val, bits, s.part_bits);
    s.vmap.set_parts(old_vref, parts);
}

fn num_parts64(bits: u32, part_bits: u32) -> usize {
    bits.div_ceil(part_bits) as usize
}

fn num_limbs32(bits: u32, limb_bits: u32) -> usize {
    bits.div_ceil(limb_bits) as usize
}

fn const_parts_for_bits(b: &mut Builder, val: &BigInt, bits: u32, part_bits: u32) -> Vec<ValueRef> {
    let modulus = BigInt::from(1u8) << bits;
    let mut truncated = val % &modulus;
    if truncated.sign() == num_bigint::Sign::Minus {
        truncated += &modulus;
    }
    let mask = (BigInt::from(1u8) << part_bits) - BigInt::from(1u8);
    let mut parts = Vec::with_capacity(num_parts64(bits, part_bits));
    let mut cur = truncated;
    for _ in 0..num_parts64(bits, part_bits) {
        let limb = &cur & &mask;
        let part = b.iconst(limb, part_bits, IntSignedness::Unsigned, o());
        parts.push(part.raw());
        cur >>= part_bits;
    }
    parts
}

fn part_sign_fill(
    old: &Function,
    b: &mut Builder,
    op: &Operand,
    lo: ValueRef,
    part_bits: u32,
) -> ValueRef {
    if is_signed_annotation(
        op.annotation
            .as_ref()
            .or_else(|| value_annotation(old, op.value)),
    ) {
        let shift = b.iconst(
            (part_bits - 1) as i64,
            part_bits,
            IntSignedness::Unsigned,
            o(),
        );
        let signed_part = IntAnnotation {
            bit_width: part_bits,
            signedness: IntSignedness::Signed,
        };
        b.shr(
            Operand::annotated(lo, Annotation::Int(signed_part)).into(),
            shift.into(),
            signed_part,
            o(),
        )
        .raw()
    } else {
        b.iconst(0i64, part_bits, IntSignedness::Unsigned, o())
            .raw()
    }
}

fn operand_parts64(
    old: &Function,
    s: &State,
    b: &mut Builder,
    op: &Operand,
    bits: u32,
) -> Vec<ValueRef> {
    if matches!(s.vmap.get(op.value), Mapped::Parts(_) | Mapped::Pair(_, _)) {
        let mut parts = s.vmap.parts(op.value);
        parts.resize(
            num_parts64(bits, s.part_bits),
            part_sign_fill(old, b, op, parts[parts.len() - 1], s.part_bits),
        );
        return parts;
    }

    if !op.value.is_block_arg()
        && !op.value.is_secondary_result()
        && let Op::Const(val) = &old.inst(op.value.index()).op
    {
        return const_parts_for_bits(b, val, bits, s.part_bits);
    }

    let lo = s.vmap.one(op.value);
    let fill = part_sign_fill(old, b, op, lo, s.part_bits);
    let mut parts = Vec::with_capacity(num_parts64(bits, s.part_bits));
    parts.push(lo);
    while parts.len() < num_parts64(bits, s.part_bits) {
        parts.push(fill);
    }
    parts
}

fn split_parts64_to_limbs32(
    s: &State,
    b: &mut Builder,
    parts: &[ValueRef],
    limb_count: usize,
) -> Vec<ValueRef> {
    let mut limbs = Vec::with_capacity(limb_count);
    let shift = b.iconst(
        s.limb_bits as i64,
        s.part_bits,
        IntSignedness::Unsigned,
        o(),
    );
    let mask = b.iconst(
        (BigInt::from(1u8) << s.limb_bits) - BigInt::from(1u8),
        s.part_bits,
        IntSignedness::Unsigned,
        o(),
    );
    let part_ann = IntAnnotation {
        bit_width: s.part_bits,
        signedness: IntSignedness::Unsigned,
    };
    let limbs_per_part = (s.part_bits / s.limb_bits).max(1);
    for part in parts {
        let mut cur = *part;
        for _ in 0..limbs_per_part {
            if limbs.len() >= limb_count {
                break;
            }
            let lo = b.and(
                Operand::annotated(cur, Annotation::Int(part_ann)).into(),
                mask.raw().into(),
                part_ann,
                o(),
            );
            limbs.push(lo.raw());
            if limbs.len() < limb_count {
                cur = b
                    .shr(
                        Operand::annotated(cur, Annotation::Int(part_ann)).into(),
                        shift.raw().into(),
                        part_ann,
                        o(),
                    )
                    .raw();
            }
        }
    }
    limbs
}

fn limbs32_to_parts64(s: &State, b: &mut Builder, limbs: &[ValueRef]) -> Vec<ValueRef> {
    let limbs_per_part = (s.part_bits / s.limb_bits).max(1) as usize;
    let mut parts = Vec::with_capacity(limbs.len().div_ceil(limbs_per_part));
    let part_ann = IntAnnotation {
        bit_width: s.part_bits,
        signedness: IntSignedness::Unsigned,
    };
    for chunk in limbs.chunks(limbs_per_part) {
        let mut acc = b.zext(
            Operand::annotated(
                chunk[0],
                Annotation::Int(IntAnnotation {
                    bit_width: s.limb_bits,
                    signedness: IntSignedness::Unsigned,
                }),
            )
            .into(),
            s.part_bits,
            o(),
        );
        for (idx, limb) in chunk.iter().copied().enumerate().skip(1) {
            let shift = b.iconst(
                (idx as u32 * s.limb_bits) as i64,
                s.part_bits,
                IntSignedness::Unsigned,
                o(),
            );
            let widened = b.zext(
                Operand::annotated(
                    limb,
                    Annotation::Int(IntAnnotation {
                        bit_width: s.limb_bits,
                        signedness: IntSignedness::Unsigned,
                    }),
                )
                .into(),
                s.part_bits,
                o(),
            );
            let shifted = b.shl(widened.into(), shift.into(), part_ann, o());
            acc = b.or(acc.into(), shifted.into(), part_ann, o());
        }
        parts.push(acc.raw());
    }
    parts
}

fn limb_ann(s: &State) -> IntAnnotation {
    IntAnnotation {
        bit_width: s.limb_bits,
        signedness: IntSignedness::DontCare,
    }
}

fn part_ann(s: &State) -> IntAnnotation {
    IntAnnotation {
        bit_width: s.part_bits,
        signedness: IntSignedness::Unsigned,
    }
}

fn bool_to_u32(s: &State, b: &mut Builder, val: tuffy_ir::typed::BoolValue) -> ValueRef {
    let zero = b.iconst(0i64, s.limb_bits, IntSignedness::Unsigned, o());
    let one = b.iconst(1i64, s.limb_bits, IntSignedness::Unsigned, o());
    b.select(
        val.into(),
        one.into(),
        zero.into(),
        Type::Int,
        Some(Annotation::Int(IntAnnotation {
            bit_width: s.limb_bits,
            signedness: IntSignedness::Unsigned,
        })),
        o(),
    )
}

fn bool_to_part(s: &State, b: &mut Builder, val: tuffy_ir::typed::BoolValue) -> ValueRef {
    let zero = b
        .iconst(0i64, s.part_bits, IntSignedness::Unsigned, o())
        .raw();
    let one = b
        .iconst(1i64, s.part_bits, IntSignedness::Unsigned, o())
        .raw();
    b.select(
        val.into(),
        Operand::annotated(one, Annotation::Int(part_ann(s))),
        Operand::annotated(zero, Annotation::Int(part_ann(s))),
        Type::Int,
        Some(Annotation::Int(part_ann(s))),
        o(),
    )
}

fn add3_u32(
    s: &State,
    b: &mut Builder,
    a: ValueRef,
    b_val: ValueRef,
    carry: ValueRef,
) -> (ValueRef, ValueRef) {
    let ann = limb_ann(s);
    let sum1 = b.add(
        Operand::annotated(a, Annotation::Int(ann)).into(),
        Operand::annotated(b_val, Annotation::Int(ann)).into(),
        ann,
        o(),
    );
    let c1 = b.icmp(
        ICmpOp::Lt,
        sum1.into(),
        Operand::annotated(a, Annotation::Int(ann)).into(),
        o(),
    );
    let sum2 = b.add(
        sum1.into(),
        Operand::annotated(carry, Annotation::Int(ann)).into(),
        ann,
        o(),
    );
    let c2 = b.icmp(ICmpOp::Lt, sum2.into(), sum1.into(), o());
    let c1 = bool_to_u32(s, b, c1);
    let c2 = bool_to_u32(s, b, c2);
    let carry_out = b.add(Operand::new(c1).into(), Operand::new(c2).into(), ann, o());
    (sum2.raw(), carry_out.raw())
}

fn sub2_u32(
    s: &State,
    b: &mut Builder,
    a: ValueRef,
    sub: ValueRef,
    borrow: ValueRef,
) -> (ValueRef, ValueRef) {
    let ann = limb_ann(s);
    let diff1 = b.sub(
        Operand::annotated(a, Annotation::Int(ann)).into(),
        Operand::annotated(sub, Annotation::Int(ann)).into(),
        ann,
        o(),
    );
    let b1 = b.icmp(
        ICmpOp::Gt,
        diff1.into(),
        Operand::annotated(a, Annotation::Int(ann)).into(),
        o(),
    );
    let diff2 = b.sub(
        diff1.into(),
        Operand::annotated(borrow, Annotation::Int(ann)).into(),
        ann,
        o(),
    );
    let b2 = b.icmp(ICmpOp::Gt, diff2.into(), diff1.into(), o());
    let b1 = bool_to_u32(s, b, b1);
    let b2 = bool_to_u32(s, b, b2);
    let borrow_out = b.or(Operand::new(b1).into(), Operand::new(b2).into(), ann, o());
    (diff2.raw(), borrow_out.raw())
}

fn add_into_limbs(
    s: &State,
    b: &mut Builder,
    dst: &mut [ValueRef],
    start: usize,
    src: &[ValueRef],
) {
    let zero = b
        .iconst(0i64, s.limb_bits, IntSignedness::Unsigned, o())
        .raw();
    let mut carry = zero;
    for (idx, slot) in dst.iter_mut().enumerate().skip(start) {
        let addend = src.get(idx - start).copied().unwrap_or(zero);
        let (sum, next_carry) = add3_u32(s, b, *slot, addend, carry);
        *slot = sum;
        carry = next_carry;
    }
}

fn mask_limb_to_width(s: &State, b: &mut Builder, limb: ValueRef, width: u32) -> ValueRef {
    if width >= s.limb_bits {
        return limb;
    }
    let mask = b.iconst(
        (BigInt::from(1u8) << width) - BigInt::from(1u8),
        s.limb_bits,
        IntSignedness::Unsigned,
        o(),
    );
    b.and(
        Operand::annotated(limb, Annotation::Int(limb_ann(s))).into(),
        Operand::annotated(mask.raw(), Annotation::Int(limb_ann(s))).into(),
        limb_ann(s),
        o(),
    )
    .raw()
}

fn normalize_limbs32(s: &State, b: &mut Builder, limbs: &[ValueRef], bits: u32) -> Vec<ValueRef> {
    let widths = wide_limb_widths(s, bits);
    limbs
        .iter()
        .copied()
        .zip(widths)
        .map(|(limb, width)| mask_limb_to_width(s, b, limb, width))
        .collect()
}

fn sub_from_limbs(s: &State, b: &mut Builder, dst: &mut [ValueRef], src: &[ValueRef]) {
    let zero = b
        .iconst(0i64, s.limb_bits, IntSignedness::Unsigned, o())
        .raw();
    let mut borrow = zero;
    for (idx, slot) in dst.iter_mut().enumerate() {
        let sub = src.get(idx).copied().unwrap_or(zero);
        let (diff, next_borrow) = sub2_u32(s, b, *slot, sub, borrow);
        *slot = diff;
        borrow = next_borrow;
    }
}

fn zero_limbs32(s: &State, b: &mut Builder, len: usize) -> Vec<ValueRef> {
    let zero = b
        .iconst(0i64, s.limb_bits, IntSignedness::Unsigned, o())
        .raw();
    vec![zero; len]
}

fn poison_limb32(s: &State, b: &mut Builder) -> ValueRef {
    let zero = b.iconst(0i64, s.limb_bits, IntSignedness::Unsigned, o());
    b.div(
        Operand::annotated(zero.raw(), Annotation::Int(limb_ann(s))).into(),
        Operand::annotated(zero.raw(), Annotation::Int(limb_ann(s))).into(),
        limb_ann(s),
        o(),
    )
    .raw()
}

fn poison_limbs32(s: &State, b: &mut Builder, len: usize) -> Vec<ValueRef> {
    let poison = poison_limb32(s, b);
    vec![poison; len]
}

fn select_limbs32(
    s: &State,
    b: &mut Builder,
    cond: tuffy_ir::typed::BoolValue,
    t: &[ValueRef],
    f: &[ValueRef],
) -> Vec<ValueRef> {
    t.iter()
        .copied()
        .zip(f.iter().copied())
        .map(|(tv, fv)| {
            b.select(
                cond.into(),
                Operand::annotated(tv, Annotation::Int(limb_ann(s))),
                Operand::annotated(fv, Annotation::Int(limb_ann(s))),
                Type::Int,
                Some(Annotation::Int(limb_ann(s))),
                o(),
            )
        })
        .collect()
}

fn limbs32_are_zero(s: &State, b: &mut Builder, limbs: &[ValueRef]) -> tuffy_ir::typed::BoolValue {
    let zero = b
        .iconst(0i64, s.limb_bits, IntSignedness::Unsigned, o())
        .raw();
    let mut eq = b.bconst(true, o());
    for limb in limbs {
        let limb_zero = b.icmp(
            ICmpOp::Eq,
            Operand::annotated(*limb, Annotation::Int(limb_ann(s))).into(),
            Operand::annotated(zero, Annotation::Int(limb_ann(s))).into(),
            o(),
        );
        eq = b.band(eq.into(), limb_zero.into(), o());
    }
    eq
}

fn icmp_unsigned_ge_limbs32(
    s: &State,
    b: &mut Builder,
    lhs: &[ValueRef],
    rhs: &[ValueRef],
) -> tuffy_ir::typed::BoolValue {
    let mut eq = b.bconst(true, o());
    let mut gt = b.bconst(false, o());
    for (l, r) in lhs.iter().copied().zip(rhs.iter().copied()).rev() {
        let limb_gt = b.icmp(
            ICmpOp::Gt,
            Operand::annotated(l, Annotation::Int(limb_ann(s))).into(),
            Operand::annotated(r, Annotation::Int(limb_ann(s))).into(),
            o(),
        );
        let limb_eq = b.icmp(
            ICmpOp::Eq,
            Operand::annotated(l, Annotation::Int(limb_ann(s))).into(),
            Operand::annotated(r, Annotation::Int(limb_ann(s))).into(),
            o(),
        );
        let gt_here = b.band(eq.into(), limb_gt.into(), o());
        gt = b.bor(gt.into(), gt_here.into(), o());
        eq = b.band(eq.into(), limb_eq.into(), o());
    }
    b.bor(gt.into(), eq.into(), o())
}

fn negate_limbs32(s: &State, b: &mut Builder, limbs: &[ValueRef], bits: u32) -> Vec<ValueRef> {
    let zeroes = zero_limbs32(s, b, limbs.len());
    let (neg, _) = sub_limbs32(s, b, &zeroes, limbs);
    normalize_limbs32(s, b, &neg, bits)
}

fn limb_sign_bool(
    s: &State,
    b: &mut Builder,
    v: ValueRef,
    width: u32,
) -> tuffy_ir::typed::BoolValue {
    let zero = b.iconst(0i64, s.limb_bits, IntSignedness::Unsigned, o());
    let shift = b.iconst(
        (width - 1) as i64,
        s.limb_bits,
        IntSignedness::Unsigned,
        o(),
    );
    let sign = b.shr(
        Operand::annotated(v, Annotation::Int(limb_ann(s))).into(),
        shift.into(),
        limb_ann(s),
        o(),
    );
    b.icmp(ICmpOp::Ne, sign.into(), zero.into(), o())
}

fn u32_sign_bool(s: &State, b: &mut Builder, v: ValueRef) -> tuffy_ir::typed::BoolValue {
    limb_sign_bool(s, b, v, s.limb_bits)
}

fn widening_mul_u32(s: &State, b: &mut Builder, x: ValueRef, y: ValueRef) -> (ValueRef, ValueRef) {
    let xw = b.zext(
        Operand::annotated(x, Annotation::Int(limb_ann(s))).into(),
        s.part_bits,
        o(),
    );
    let yw = b.zext(
        Operand::annotated(y, Annotation::Int(limb_ann(s))).into(),
        s.part_bits,
        o(),
    );
    let prod = b.mul(
        xw.into(),
        yw.into(),
        IntAnnotation {
            bit_width: s.part_bits,
            signedness: IntSignedness::Unsigned,
        },
        o(),
    );
    let shift = b.iconst(
        s.limb_bits as i64,
        s.part_bits,
        IntSignedness::Unsigned,
        o(),
    );
    let mask = b.iconst(
        (BigInt::from(1u8) << s.limb_bits) - BigInt::from(1u8),
        s.part_bits,
        IntSignedness::Unsigned,
        o(),
    );
    let part_ann = IntAnnotation {
        bit_width: s.part_bits,
        signedness: IntSignedness::Unsigned,
    };
    let lo = b.and(prod.into(), mask.raw().into(), part_ann, o());
    let hi = b.shr(prod.into(), shift.into(), part_ann, o());
    (lo.raw(), hi.raw())
}

fn result_bits(s: &State, old: &Function, old_vref: ValueRef) -> u32 {
    value_annotation(old, old_vref)
        .and_then(|ann| int_annotation_bits(Some(ann)))
        .unwrap_or(s.part_bits * 2)
}

fn chunk_widths(bits: u32, chunk_bits: u32) -> Vec<u32> {
    let mut remaining = bits;
    let mut widths = Vec::with_capacity(bits.div_ceil(chunk_bits) as usize);
    while remaining > 0 {
        let chunk = remaining.min(chunk_bits);
        widths.push(chunk);
        remaining = remaining.saturating_sub(chunk);
    }
    widths
}

fn wide_limb_widths(s: &State, bits: u32) -> Vec<u32> {
    chunk_widths(bits, s.limb_bits)
}

fn operand_limbs32(
    old: &Function,
    s: &State,
    b: &mut Builder,
    op: &Operand,
    bits: u32,
) -> Vec<ValueRef> {
    let parts = operand_parts64(old, s, b, op, bits);
    split_parts64_to_limbs32(s, b, &parts, num_limbs32(bits, s.limb_bits))
}

fn add_limbs32(
    s: &State,
    b: &mut Builder,
    lhs: &[ValueRef],
    rhs: &[ValueRef],
) -> (Vec<ValueRef>, ValueRef) {
    let zero = b
        .iconst(0i64, s.limb_bits, IntSignedness::Unsigned, o())
        .raw();
    let mut carry = zero;
    let mut out = Vec::with_capacity(lhs.len());
    for (l, r) in lhs.iter().copied().zip(rhs.iter().copied()) {
        let (sum, next_carry) = add3_u32(s, b, l, r, carry);
        out.push(sum);
        carry = next_carry;
    }
    (out, carry)
}

fn sub_limbs32(
    s: &State,
    b: &mut Builder,
    lhs: &[ValueRef],
    rhs: &[ValueRef],
) -> (Vec<ValueRef>, ValueRef) {
    let zero = b
        .iconst(0i64, s.limb_bits, IntSignedness::Unsigned, o())
        .raw();
    let mut borrow = zero;
    let mut out = Vec::with_capacity(lhs.len());
    for (l, r) in lhs.iter().copied().zip(rhs.iter().copied()) {
        let (diff, next_borrow) = sub2_u32(s, b, l, r, borrow);
        out.push(diff);
        borrow = next_borrow;
    }
    (out, borrow)
}

fn nonzero_u32(s: &State, b: &mut Builder, v: ValueRef) -> tuffy_ir::typed::BoolValue {
    let zero = b.iconst(0i64, s.limb_bits, IntSignedness::Unsigned, o());
    b.icmp(ICmpOp::Ne, Operand::new(v).into(), zero.into(), o())
}

fn bool_not(b: &mut Builder, val: tuffy_ir::typed::BoolValue) -> tuffy_ir::typed::BoolValue {
    let t = b.bconst(true, o());
    b.bxor(val.into(), t.into(), o())
}

fn fp_format_params(ft: FloatType) -> Option<(u32, u32, u32, u32)> {
    match ft {
        FloatType::F16 => Some((16, 5, 10, 15)),
        FloatType::BF16 => Some((16, 8, 7, 127)),
        FloatType::F32 => Some((32, 8, 23, 127)),
        FloatType::F64 => Some((64, 11, 52, 1023)),
        FloatType::F128 => None,
    }
}

fn wide_uint_from_small_value(
    s: &State,
    b: &mut Builder,
    val: ValueRef,
    src_bits: u32,
    bits: u32,
) -> Vec<ValueRef> {
    assert!(
        src_bits <= s.part_bits,
        "small-value wide expansion requires source bits <= legal part bits"
    );
    let lo = if src_bits < s.part_bits {
        b.zext(
            Operand::annotated(
                val,
                Annotation::Int(IntAnnotation {
                    bit_width: src_bits,
                    signedness: IntSignedness::Unsigned,
                }),
            )
            .into(),
            s.part_bits,
            o(),
        )
        .raw()
    } else {
        val
    };
    let zero = b
        .iconst(0i64, s.part_bits, IntSignedness::Unsigned, o())
        .raw();
    let parts = std::iter::once(lo)
        .chain(std::iter::repeat_n(
            zero,
            num_parts64(bits, s.part_bits).saturating_sub(1),
        ))
        .collect::<Vec<_>>();
    let limbs = split_parts64_to_limbs32(s, b, &parts, num_limbs32(bits, s.limb_bits));
    normalize_limbs32(s, b, &limbs, bits)
}

fn wide_shift_amount(
    s: &State,
    b: &mut Builder,
    amt: ValueRef,
    bits: u32,
) -> (ValueRef, ValueRef, tuffy_ir::typed::BoolValue) {
    let p_ann = part_ann(s);
    let bits_c = b.iconst(bits as i64, s.part_bits, IntSignedness::Unsigned, o());
    let limb_c = b.iconst(
        s.limb_bits as i64,
        s.part_bits,
        IntSignedness::Unsigned,
        o(),
    );
    let zero = b.iconst(0i64, s.part_bits, IntSignedness::Unsigned, o());
    let amt_op = Operand::annotated(amt, Annotation::Int(p_ann));
    let n_mod = b.rem(amt_op.clone().into(), bits_c.into(), p_ann, o());
    let whole = b.div(n_mod.into(), limb_c.into(), p_ann, o());
    let rem = b.rem(n_mod.into(), limb_c.into(), p_ann, o());
    let rem_zero = b.icmp(ICmpOp::Eq, rem.into(), zero.into(), o());
    (whole.raw(), rem.raw(), rem_zero)
}

fn wide_shl_limbs(
    s: &State,
    b: &mut Builder,
    limbs: &[ValueRef],
    amt: ValueRef,
    bits: u32,
) -> Vec<ValueRef> {
    let limb_count = limbs.len();
    let p_ann = part_ann(s);
    let l_ann = limb_ann(s);
    let zero = b
        .iconst(0i64, s.limb_bits, IntSignedness::Unsigned, o())
        .raw();
    let (whole, rem, rem_zero) = wide_shift_amount(s, b, amt, bits);
    let limb_bits_c = b.iconst(
        s.limb_bits as i64,
        s.part_bits,
        IntSignedness::Unsigned,
        o(),
    );
    let inv_rem = b.sub(limb_bits_c.into(), Operand::new(rem).into(), p_ann, o());

    let mut out = Vec::with_capacity(limb_count);
    for out_idx in 0..limb_count {
        let mut limb_out = zero;
        for whole_idx in 0..limb_count {
            let whole_idx_c = b.iconst(whole_idx as i64, s.part_bits, IntSignedness::Unsigned, o());
            let cond = b.icmp(
                ICmpOp::Eq,
                Operand::new(whole).into(),
                whole_idx_c.into(),
                o(),
            );
            let base = if out_idx >= whole_idx {
                limbs[out_idx - whole_idx]
            } else {
                zero
            };
            let spill = if out_idx > whole_idx {
                limbs[out_idx - whole_idx - 1]
            } else {
                zero
            };
            let base_shift = b.shl(
                Operand::annotated(base, Annotation::Int(l_ann)).into(),
                Operand::new(rem).into(),
                l_ann,
                o(),
            );
            let spill_shift = b.shr(
                Operand::annotated(spill, Annotation::Int(l_ann)).into(),
                inv_rem.into(),
                l_ann,
                o(),
            );
            let merged = b.or(base_shift.into(), spill_shift.into(), l_ann, o());
            let candidate = b.select(
                rem_zero.into(),
                Operand::annotated(base, Annotation::Int(l_ann)),
                Operand::annotated(merged.raw(), Annotation::Int(l_ann)),
                Type::Int,
                Some(Annotation::Int(l_ann)),
                o(),
            );
            limb_out = b.select(
                cond.into(),
                Operand::annotated(candidate, Annotation::Int(l_ann)),
                Operand::annotated(limb_out, Annotation::Int(l_ann)),
                Type::Int,
                Some(Annotation::Int(l_ann)),
                o(),
            );
        }
        out.push(limb_out);
    }
    out
}

fn wide_shr_limbs(
    s: &State,
    b: &mut Builder,
    limbs: &[ValueRef],
    amt: ValueRef,
    bits: u32,
    signed: bool,
) -> Vec<ValueRef> {
    let limb_count = limbs.len();
    let p_ann = part_ann(s);
    let l_ann = limb_ann(s);
    let zero = b
        .iconst(0i64, s.limb_bits, IntSignedness::Unsigned, o())
        .raw();
    let ones = limb_mask_const(s, b, s.limb_bits);
    let sign_fill = if signed {
        let sign = u32_sign_bool(s, b, *limbs.last().expect("wide shr limbs"));
        b.select(
            sign.into(),
            Operand::annotated(ones, Annotation::Int(l_ann)),
            Operand::annotated(zero, Annotation::Int(l_ann)),
            Type::Int,
            Some(Annotation::Int(l_ann)),
            o(),
        )
    } else {
        zero
    };
    let (whole, rem, rem_zero) = wide_shift_amount(s, b, amt, bits);
    let limb_bits_c = b.iconst(
        s.limb_bits as i64,
        s.part_bits,
        IntSignedness::Unsigned,
        o(),
    );
    let inv_rem = b.sub(limb_bits_c.into(), Operand::new(rem).into(), p_ann, o());

    let mut out = Vec::with_capacity(limb_count);
    for out_idx in 0..limb_count {
        let mut limb_out = zero;
        for whole_idx in 0..limb_count {
            let whole_idx_c = b.iconst(whole_idx as i64, s.part_bits, IntSignedness::Unsigned, o());
            let cond = b.icmp(
                ICmpOp::Eq,
                Operand::new(whole).into(),
                whole_idx_c.into(),
                o(),
            );
            let base = if out_idx + whole_idx < limb_count {
                limbs[out_idx + whole_idx]
            } else {
                sign_fill
            };
            let spill = if out_idx + whole_idx + 1 < limb_count {
                limbs[out_idx + whole_idx + 1]
            } else {
                sign_fill
            };
            let shift_ann = if signed {
                IntAnnotation {
                    bit_width: s.limb_bits,
                    signedness: IntSignedness::Signed,
                }
            } else {
                l_ann
            };
            let base_shift = b.shr(
                Operand::annotated(base, Annotation::Int(shift_ann)).into(),
                Operand::new(rem).into(),
                shift_ann,
                o(),
            );
            let spill_shift = b.shl(
                Operand::annotated(spill, Annotation::Int(l_ann)).into(),
                inv_rem.into(),
                l_ann,
                o(),
            );
            let merged = b.or(
                Operand::annotated(base_shift.raw(), Annotation::Int(l_ann)).into(),
                spill_shift.into(),
                l_ann,
                o(),
            );
            let candidate = b.select(
                rem_zero.into(),
                Operand::annotated(base, Annotation::Int(l_ann)),
                Operand::annotated(merged.raw(), Annotation::Int(l_ann)),
                Type::Int,
                Some(Annotation::Int(l_ann)),
                o(),
            );
            limb_out = b.select(
                cond.into(),
                Operand::annotated(candidate, Annotation::Int(l_ann)),
                Operand::annotated(limb_out, Annotation::Int(l_ann)),
                Type::Int,
                Some(Annotation::Int(l_ann)),
                o(),
            );
        }
        out.push(limb_out);
    }
    out
}

#[allow(clippy::too_many_arguments)]
fn full_mul_add_limbs32(
    s: &State,
    b: &mut Builder,
    a_limbs: &[ValueRef],
    b_limbs: &[ValueRef],
    carry_limbs: &[ValueRef],
    add_limbs: &[ValueRef],
    bits: u32,
    signed: bool,
) -> Vec<ValueRef> {
    let limb_count = a_limbs.len();
    let top_width = *wide_limb_widths(s, bits)
        .last()
        .expect("wide mul-add requires at least one limb");
    let zero32 = b
        .iconst(0i64, s.limb_bits, IntSignedness::Unsigned, o())
        .raw();
    let one32 = b
        .iconst(1i64, s.limb_bits, IntSignedness::Unsigned, o())
        .raw();
    let mut full = vec![zero32; limb_count * 2];
    for (i, a_limb) in a_limbs.iter().copied().enumerate() {
        for (j, b_limb) in b_limbs.iter().copied().enumerate() {
            let (prod_lo, prod_hi) = widening_mul_u32(s, b, a_limb, b_limb);
            add_into_limbs(s, b, &mut full, i + j, &[prod_lo, prod_hi]);
        }
    }

    add_into_limbs(s, b, &mut full, 0, carry_limbs);
    add_into_limbs(s, b, &mut full, 0, add_limbs);

    if signed {
        let a_neg = limb_sign_bool(
            s,
            b,
            *a_limbs.last().expect("wide mul-add lhs limbs"),
            top_width,
        );
        let b_neg = limb_sign_bool(
            s,
            b,
            *b_limbs.last().expect("wide mul-add rhs limbs"),
            top_width,
        );
        let carry_neg = limb_sign_bool(
            s,
            b,
            *carry_limbs.last().expect("wide mul-add carry limbs"),
            top_width,
        );
        let add_neg = limb_sign_bool(
            s,
            b,
            *add_limbs.last().expect("wide mul-add add limbs"),
            top_width,
        );

        let mut upper = full[limb_count..].to_vec();

        let select_masked = |this: &mut Builder,
                             cond: tuffy_ir::typed::BoolValue,
                             src: &[ValueRef]|
         -> Vec<ValueRef> {
            src.iter()
                .map(|part| {
                    this.select(
                        cond.into(),
                        Operand::new(*part),
                        Operand::new(zero32),
                        Type::Int,
                        Some(Annotation::Int(limb_ann(s))),
                        o(),
                    )
                })
                .collect()
        };

        let sub_b = select_masked(b, a_neg, b_limbs);
        sub_from_limbs(s, b, &mut upper, &sub_b);

        let sub_a = select_masked(b, b_neg, a_limbs);
        sub_from_limbs(s, b, &mut upper, &sub_a);

        let sub_one_carry = b.select(
            carry_neg.into(),
            Operand::new(one32),
            Operand::new(zero32),
            Type::Int,
            Some(Annotation::Int(limb_ann(s))),
            o(),
        );
        sub_from_limbs(s, b, &mut upper, &[sub_one_carry]);

        let sub_one_add = b.select(
            add_neg.into(),
            Operand::new(one32),
            Operand::new(zero32),
            Type::Int,
            Some(Annotation::Int(limb_ann(s))),
            o(),
        );
        sub_from_limbs(s, b, &mut upper, &[sub_one_add]);

        for (dst, src) in full[limb_count..].iter_mut().zip(upper) {
            *dst = src;
        }
    }

    full
}

fn udivrem_limbs32(
    s: &State,
    b: &mut Builder,
    dividend: &[ValueRef],
    divisor: &[ValueRef],
    bits: u32,
) -> (Vec<ValueRef>, Vec<ValueRef>, tuffy_ir::typed::BoolValue) {
    let limb_count = dividend.len();
    let mut quotient = zero_limbs32(s, b, limb_count);
    let mut remainder = normalize_limbs32(s, b, dividend, bits);
    let divisor = normalize_limbs32(s, b, divisor, bits);
    let divisor_zero = limbs32_are_zero(s, b, &divisor);

    for shift_idx in (0..bits).rev() {
        let shift = b.iconst(shift_idx as i64, s.part_bits, IntSignedness::Unsigned, o());
        let rem_shifted_raw = wide_shr_limbs(s, b, &remainder, shift.raw(), bits, false);
        let rem_shifted = normalize_limbs32(s, b, &rem_shifted_raw, bits);
        let ge = icmp_unsigned_ge_limbs32(s, b, &rem_shifted, &divisor);
        let shifted_div_raw = wide_shl_limbs(s, b, &divisor, shift.raw(), bits);
        let shifted_div = normalize_limbs32(s, b, &shifted_div_raw, bits);
        let (diff, _) = sub_limbs32(s, b, &remainder, &shifted_div);
        let diff = normalize_limbs32(s, b, &diff, bits);
        remainder = select_limbs32(s, b, ge, &diff, &remainder);
        remainder = normalize_limbs32(s, b, &remainder, bits);

        let limb_idx = (shift_idx / s.limb_bits) as usize;
        let bit_idx = shift_idx % s.limb_bits;
        let bit = b.iconst(
            BigInt::from(1u8) << bit_idx,
            s.limb_bits,
            IntSignedness::Unsigned,
            o(),
        );
        let set = b.or(
            Operand::annotated(quotient[limb_idx], Annotation::Int(limb_ann(s))).into(),
            Operand::annotated(bit.raw(), Annotation::Int(limb_ann(s))).into(),
            limb_ann(s),
            o(),
        );
        quotient[limb_idx] = b.select(
            ge.into(),
            Operand::annotated(set.raw(), Annotation::Int(limb_ann(s))),
            Operand::annotated(quotient[limb_idx], Annotation::Int(limb_ann(s))),
            Type::Int,
            Some(Annotation::Int(limb_ann(s))),
            o(),
        );
    }

    (
        normalize_limbs32(s, b, &quotient, bits),
        normalize_limbs32(s, b, &remainder, bits),
        divisor_zero,
    )
}

fn limb_mask_const(s: &State, b: &mut Builder, bits: u32) -> ValueRef {
    let val = (BigInt::from(1u8) << bits) - BigInt::from(1u8);
    b.iconst(val, s.limb_bits, IntSignedness::Unsigned, o())
        .raw()
}

fn signed_sat_limbs32(
    s: &State,
    b: &mut Builder,
    bits: u32,
    negative: tuffy_ir::typed::BoolValue,
) -> Vec<ValueRef> {
    let widths = wide_limb_widths(s, bits);
    let zero = b
        .iconst(0i64, s.limb_bits, IntSignedness::Unsigned, o())
        .raw();
    let ones = limb_mask_const(s, b, s.limb_bits);
    let top_bits = *widths.last().unwrap_or(&s.limb_bits);
    let min_top = b.iconst(
        BigInt::from(1u8) << (top_bits - 1),
        s.limb_bits,
        IntSignedness::Unsigned,
        o(),
    );
    let max_top = b.iconst(
        (BigInt::from(1u8) << (top_bits - 1)) - BigInt::from(1u8),
        s.limb_bits,
        IntSignedness::Unsigned,
        o(),
    );
    let mut out = Vec::with_capacity(widths.len());
    for idx in 0..widths.len() {
        let limb = if idx + 1 == widths.len() {
            b.select(
                negative.into(),
                min_top.raw().into(),
                max_top.raw().into(),
                Type::Int,
                Some(Annotation::Int(limb_ann(s))),
                o(),
            )
        } else {
            b.select(
                negative.into(),
                Operand::new(zero),
                Operand::new(ones),
                Type::Int,
                Some(Annotation::Int(limb_ann(s))),
                o(),
            )
        };
        out.push(limb);
    }
    out
}

fn unsigned_sat_limbs32(s: &State, b: &mut Builder, bits: u32, is_add: bool) -> Vec<ValueRef> {
    let widths = wide_limb_widths(s, bits);
    let zero = b
        .iconst(0i64, s.limb_bits, IntSignedness::Unsigned, o())
        .raw();
    widths
        .into_iter()
        .map(|w| {
            if is_add {
                limb_mask_const(s, b, w)
            } else {
                zero
            }
        })
        .collect()
}

#[allow(clippy::too_many_arguments)]
fn leg_carrying_mul_add_small(
    s: &mut State,
    b: &mut Builder,
    old_vref: ValueRef,
    a: &Operand,
    op_b: &Operand,
    carry: &Operand,
    add: &Operand,
    bits: u32,
    signed: bool,
) {
    let src_ann = IntAnnotation {
        bit_width: bits,
        signedness: if signed {
            IntSignedness::Signed
        } else {
            IntSignedness::Unsigned
        },
    };
    let widen = |this: &mut Builder, op: &Operand| -> ValueRef {
        if signed {
            this.sext(
                Operand::annotated(op.value, Annotation::Int(src_ann)).into(),
                64,
                o(),
            )
            .raw()
        } else {
            this.zext(
                Operand::annotated(op.value, Annotation::Int(src_ann)).into(),
                64,
                o(),
            )
            .raw()
        }
    };

    let a64 = widen(b, a);
    let b64 = widen(b, op_b);
    let carry64 = widen(b, carry);
    let add64 = widen(b, add);
    let full_ann = if signed { SIGNED_64_INT } else { I64 };
    let prod = b.mul(
        Operand::annotated(a64, Annotation::Int(full_ann)).into(),
        Operand::annotated(b64, Annotation::Int(full_ann)).into(),
        full_ann,
        o(),
    );
    let sum = b.add(
        prod.into(),
        Operand::annotated(carry64, Annotation::Int(full_ann)).into(),
        full_ann,
        o(),
    );
    let sum = b.add(
        sum.into(),
        Operand::annotated(add64, Annotation::Int(full_ann)).into(),
        full_ann,
        o(),
    );
    let mask = b.iconst(
        (BigInt::from(1u8) << bits) - BigInt::from(1u8),
        64,
        IntSignedness::Unsigned,
        o(),
    );
    let low = b.and(
        Operand::annotated(sum.raw(), Annotation::Int(I64)).into(),
        mask.into(),
        I64,
        o(),
    );
    let shift = b.iconst(bits as i64, 64, IntSignedness::Unsigned, o());
    let high = if signed {
        b.shr(
            Operand::annotated(sum.raw(), Annotation::Int(SIGNED_64_INT)).into(),
            shift.into(),
            SIGNED_64_INT,
            o(),
        )
    } else {
        b.shr(
            Operand::annotated(sum.raw(), Annotation::Int(I64)).into(),
            shift.into(),
            UNSIGNED_64_INT,
            o(),
        )
    };
    s.vmap.set(old_vref, Mapped::One(low.raw()));
    let old_sec = ValueRef::inst_secondary_result(old_vref.index());
    s.vmap.set(old_sec, Mapped::One(high.raw()));
}

#[allow(clippy::too_many_arguments)]
fn leg_carrying_mul_add_64(
    s: &mut State,
    b: &mut Builder,
    old_vref: ValueRef,
    a: &Operand,
    op_b: &Operand,
    carry: &Operand,
    add: &Operand,
    signed: bool,
) {
    let a_raw = s.vmap.one(a.value);
    let b_raw = s.vmap.one(op_b.value);
    let carry_raw = s.vmap.one(carry.value);
    let add_raw = s.vmap.one(add.value);
    let zero = b.iconst(0, 64, IntSignedness::Unsigned, o()).raw();

    let (mut lo, mut hi) = widening_mul_u64(b, a_raw, b_raw);
    if signed {
        let c63 = b.iconst(63, 64, IntSignedness::Unsigned, o());
        let a_sign = b.shr(
            Operand::annotated(a_raw, Annotation::Int(SIGNED_64_INT)).into(),
            c63.into(),
            SIGNED_64_INT,
            o(),
        );
        let b_sign = b.shr(
            Operand::annotated(b_raw, Annotation::Int(SIGNED_64_INT)).into(),
            c63.into(),
            SIGNED_64_INT,
            o(),
        );
        let a_neg = b.icmp(
            ICmpOp::Ne,
            a_sign.into(),
            Operand::annotated(zero, Annotation::Int(I64)).into(),
            o(),
        );
        let b_neg = b.icmp(
            ICmpOp::Ne,
            b_sign.into(),
            Operand::annotated(zero, Annotation::Int(I64)).into(),
            o(),
        );
        let sub_b = b.select(
            a_neg.into(),
            Operand::annotated(b_raw, Annotation::Int(I64)),
            Operand::annotated(zero, Annotation::Int(I64)),
            Type::Int,
            Some(Annotation::Int(I64)),
            o(),
        );
        hi = b
            .sub(
                Operand::annotated(hi, Annotation::Int(I64)).into(),
                Operand::annotated(sub_b, Annotation::Int(I64)).into(),
                I64,
                o(),
            )
            .raw();
        let sub_a = b.select(
            b_neg.into(),
            Operand::annotated(a_raw, Annotation::Int(I64)),
            Operand::annotated(zero, Annotation::Int(I64)),
            Type::Int,
            Some(Annotation::Int(I64)),
            o(),
        );
        hi = b
            .sub(
                Operand::annotated(hi, Annotation::Int(I64)).into(),
                Operand::annotated(sub_a, Annotation::Int(I64)).into(),
                I64,
                o(),
            )
            .raw();

        let carry_hi = b.shr(
            Operand::annotated(carry_raw, Annotation::Int(SIGNED_64_INT)).into(),
            c63.into(),
            SIGNED_64_INT,
            o(),
        );
        let add_hi = b.shr(
            Operand::annotated(add_raw, Annotation::Int(SIGNED_64_INT)).into(),
            c63.into(),
            SIGNED_64_INT,
            o(),
        );
        (lo, hi) = add_word_pair_u64(b, lo, hi, carry_raw, carry_hi.raw());
        (lo, hi) = add_word_pair_u64(b, lo, hi, add_raw, add_hi.raw());
    } else {
        (lo, hi) = add_word_pair_u64(b, lo, hi, carry_raw, zero);
        (lo, hi) = add_word_pair_u64(b, lo, hi, add_raw, zero);
    }

    s.vmap.set(old_vref, Mapped::One(lo));
    let old_sec = ValueRef::inst_secondary_result(old_vref.index());
    s.vmap.set(old_sec, Mapped::One(hi));
}

#[allow(clippy::too_many_arguments)]
fn leg_carrying_mul_add_128(
    old: &Function,
    s: &mut State,
    b: &mut Builder,
    old_vref: ValueRef,
    a: &Operand,
    op_b: &Operand,
    carry: &Operand,
    add: &Operand,
    signed: bool,
) {
    let (a_lo, a_hi) = wide_pair(s, old, b, a);
    let (b_lo, b_hi) = wide_pair(s, old, b, op_b);
    let (carry_lo, carry_hi) = wide_pair(s, old, b, carry);
    let (add_lo, add_hi) = wide_pair(s, old, b, add);

    let (ll_lo, ll_hi) = widening_mul_u64(b, a_lo, b_lo);
    let (lh_lo, lh_hi) = widening_mul_u64(b, a_lo, b_hi);
    let (hl_lo, hl_hi) = widening_mul_u64(b, a_hi, b_lo);
    let (hh_lo, hh_hi) = widening_mul_u64(b, a_hi, b_hi);

    let (w1, c1) = add3_u64(b, ll_hi, lh_lo, hl_lo);
    let (w2_pre, c2_pre) = add3_u64(b, lh_hi, hl_hi, hh_lo);
    let w2 = b.add(
        Operand::annotated(w2_pre, Annotation::Int(I64)).into(),
        Operand::annotated(c1, Annotation::Int(I64)).into(),
        I64,
        o(),
    );
    let cmp = b.icmp(
        ICmpOp::Lt,
        w2.into(),
        Operand::annotated(w2_pre, Annotation::Int(I64)).into(),
        o(),
    );
    let w2_carry = bool_to_u64(b, cmp);
    let c2 = b.add(
        Operand::annotated(c2_pre, Annotation::Int(I64)).into(),
        Operand::annotated(w2_carry, Annotation::Int(I64)).into(),
        I64,
        o(),
    );
    let w3 = b.add(
        hh_hi.into(),
        Operand::annotated(c2.raw(), Annotation::Int(I64)).into(),
        I64,
        o(),
    );
    let mut full = vec![ll_lo, w1, w2.raw(), w3.raw()];
    add_into_words64(b, &mut full, 0, &[carry_lo, carry_hi]);
    add_into_words64(b, &mut full, 0, &[add_lo, add_hi]);

    if signed {
        let c63 = b.iconst(63, 64, IntSignedness::Unsigned, o());
        let zero = b.iconst(0, 64, IntSignedness::Unsigned, o()).raw();
        let a_sign = b.shr(
            Operand::annotated(a_hi, Annotation::Int(SIGNED_64_INT)).into(),
            c63.into(),
            SIGNED_64_INT,
            o(),
        );
        let b_sign = b.shr(
            Operand::annotated(b_hi, Annotation::Int(SIGNED_64_INT)).into(),
            c63.into(),
            SIGNED_64_INT,
            o(),
        );
        let carry_sign = b.shr(
            Operand::annotated(carry_hi, Annotation::Int(SIGNED_64_INT)).into(),
            c63.into(),
            SIGNED_64_INT,
            o(),
        );
        let add_sign = b.shr(
            Operand::annotated(add_hi, Annotation::Int(SIGNED_64_INT)).into(),
            c63.into(),
            SIGNED_64_INT,
            o(),
        );
        let a_neg = b.icmp(
            ICmpOp::Ne,
            a_sign.into(),
            Operand::annotated(zero, Annotation::Int(I64)).into(),
            o(),
        );
        let b_neg = b.icmp(
            ICmpOp::Ne,
            b_sign.into(),
            Operand::annotated(zero, Annotation::Int(I64)).into(),
            o(),
        );
        let carry_neg = b.icmp(
            ICmpOp::Ne,
            carry_sign.into(),
            Operand::annotated(zero, Annotation::Int(I64)).into(),
            o(),
        );
        let add_neg = b.icmp(
            ICmpOp::Ne,
            add_sign.into(),
            Operand::annotated(zero, Annotation::Int(I64)).into(),
            o(),
        );
        let select_masked =
            |this: &mut Builder, cond: tuffy_ir::typed::BoolValue, lo: ValueRef, hi: ValueRef| {
                [
                    this.select(
                        cond.into(),
                        Operand::annotated(lo, Annotation::Int(I64)),
                        Operand::annotated(zero, Annotation::Int(I64)),
                        Type::Int,
                        Some(Annotation::Int(I64)),
                        o(),
                    ),
                    this.select(
                        cond.into(),
                        Operand::annotated(hi, Annotation::Int(I64)),
                        Operand::annotated(zero, Annotation::Int(I64)),
                        Type::Int,
                        Some(Annotation::Int(I64)),
                        o(),
                    ),
                ]
            };

        let mut upper = vec![full[2], full[3]];
        let sub_b = select_masked(b, a_neg, b_lo, b_hi);
        sub_from_words64(b, &mut upper, &sub_b);
        let sub_a = select_masked(b, b_neg, a_lo, a_hi);
        sub_from_words64(b, &mut upper, &sub_a);
        let one = b.iconst(1, 64, IntSignedness::Unsigned, o()).raw();
        let sub_one_carry = b.select(
            carry_neg.into(),
            Operand::annotated(one, Annotation::Int(I64)),
            Operand::annotated(zero, Annotation::Int(I64)),
            Type::Int,
            Some(Annotation::Int(I64)),
            o(),
        );
        sub_from_words64(b, &mut upper, &[sub_one_carry, zero]);
        let sub_one_add = b.select(
            add_neg.into(),
            Operand::annotated(one, Annotation::Int(I64)),
            Operand::annotated(zero, Annotation::Int(I64)),
            Type::Int,
            Some(Annotation::Int(I64)),
            o(),
        );
        sub_from_words64(b, &mut upper, &[sub_one_add, zero]);
        full[2] = upper[0];
        full[3] = upper[1];
    }

    s.vmap.set(old_vref, Mapped::Pair(full[0], full[1]));
    let old_sec = ValueRef::inst_secondary_result(old_vref.index());
    s.vmap.set(old_sec, Mapped::Pair(full[2], full[3]));
}

#[allow(clippy::too_many_arguments)]
fn leg_carrying_mul_add_wide(
    old: &Function,
    s: &mut State,
    b: &mut Builder,
    old_vref: ValueRef,
    a: &Operand,
    op_b: &Operand,
    carry: &Operand,
    add: &Operand,
    bits: u32,
    signed: bool,
) {
    if bits <= s.limb_bits {
        leg_carrying_mul_add_small(s, b, old_vref, a, op_b, carry, add, bits, signed);
        return;
    }
    if bits == s.part_bits {
        leg_carrying_mul_add_64(s, b, old_vref, a, op_b, carry, add, signed);
        return;
    }
    if bits == s.part_bits * 2 {
        leg_carrying_mul_add_128(old, s, b, old_vref, a, op_b, carry, add, signed);
        return;
    }

    let limb_count = num_limbs32(bits, s.limb_bits);
    let a_limbs = operand_limbs32(old, s, b, a, bits);
    let b_limbs = operand_limbs32(old, s, b, op_b, bits);
    let carry_limbs = operand_limbs32(old, s, b, carry, bits);
    let add_limbs = operand_limbs32(old, s, b, add, bits);
    let full = full_mul_add_limbs32(
        s,
        b,
        &a_limbs,
        &b_limbs,
        &carry_limbs,
        &add_limbs,
        bits,
        signed,
    );

    let low_limbs = normalize_limbs32(s, b, &full[..limb_count], bits);
    let high_limbs = normalize_limbs32(s, b, &full[limb_count..], bits);
    let low_parts = limbs32_to_parts64(s, b, &low_limbs);
    let high_parts = limbs32_to_parts64(s, b, &high_limbs);
    s.vmap.set_parts(old_vref, low_parts);
    let old_sec = ValueRef::inst_secondary_result(old_vref.index());
    s.vmap.set_parts(old_sec, high_parts);
}

// ---------------------------------------------------------------------------
// Double-width add: low part add, carry into high part
// ---------------------------------------------------------------------------

fn leg_add(
    old: &Function,
    s: &mut State,
    b: &mut Builder,
    old_vref: ValueRef,
    a: &Operand,
    op_b: &Operand,
) {
    let bits = int_annotation_bits(value_annotation(old, old_vref)).unwrap_or(s.part_bits * 2);
    if bits > s.part_bits * 2 && bits.is_multiple_of(s.limb_bits) {
        let a_limbs = operand_limbs32(old, s, b, a, bits);
        let b_limbs = operand_limbs32(old, s, b, op_b, bits);
        let (sum, _) = add_limbs32(s, b, &a_limbs, &b_limbs);
        s.vmap.set_parts(old_vref, limbs32_to_parts64(s, b, &sum));
        return;
    }
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
// Double-width sub
// ---------------------------------------------------------------------------

fn leg_sub(
    _old: &Function,
    s: &mut State,
    b: &mut Builder,
    old_vref: ValueRef,
    a: &Operand,
    op_b: &Operand,
) {
    let bits = int_annotation_bits(value_annotation(_old, old_vref)).unwrap_or(s.part_bits * 2);
    if bits > s.part_bits * 2 && bits.is_multiple_of(s.limb_bits) {
        let a_limbs = operand_limbs32(_old, s, b, a, bits);
        let b_limbs = operand_limbs32(_old, s, b, op_b, bits);
        let (diff, _) = sub_limbs32(s, b, &a_limbs, &b_limbs);
        s.vmap.set_parts(old_vref, limbs32_to_parts64(s, b, &diff));
        return;
    }
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
// Double-width multiply
// ---------------------------------------------------------------------------

#[allow(clippy::too_many_lines)]
fn leg_mul(
    old: &Function,
    s: &mut State,
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
// Widening legal-part multiply and arithmetic helpers
// ---------------------------------------------------------------------------

/// Compute the full double-part product of two legal parts using quarter limbs.
fn widening_mul_u64(b: &mut Builder, x: ValueRef, y: ValueRef) -> (ValueRef, ValueRef) {
    let c32 = b.iconst(32i64, 64, IntSignedness::Unsigned, o());
    let mask32 = b.iconst(0xFFFF_FFFFi64, 64, IntSignedness::Unsigned, o());
    let x_op = Operand::annotated(x, Annotation::Int(I64));
    let y_op = Operand::annotated(y, Annotation::Int(I64));

    let x0 = b.and(x_op.clone().into(), mask32.into(), I64, o());
    let x1 = b.shr(x_op.into(), c32.into(), UNSIGNED_64_INT, o());
    let y0 = b.and(y_op.clone().into(), mask32.into(), I64, o());
    let y1 = b.shr(y_op.into(), c32.into(), UNSIGNED_64_INT, o());

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
    let x_op = Operand::annotated(x, Annotation::Int(I64));
    let y_op = Operand::annotated(y, Annotation::Int(I64));
    let z_op = Operand::annotated(z, Annotation::Int(I64));
    let t1 = b.add(x_op.into(), y_op.clone().into(), I64, o());
    let cmp = b.icmp(ICmpOp::Lt, t1.into(), y_op.into(), o());
    let c1 = bool_to_u64(b, cmp);
    let sum = b.add(t1.into(), z_op.clone().into(), I64, o());
    let cmp = b.icmp(ICmpOp::Lt, sum.into(), z_op.into(), o());
    let c2 = bool_to_u64(b, cmp);
    let carry = b.add(c1.into(), c2.into(), I64, o());
    (sum.raw(), carry.raw())
}

fn sub2_u64(b: &mut Builder, x: ValueRef, y: ValueRef, borrow: ValueRef) -> (ValueRef, ValueRef) {
    let x_op = Operand::annotated(x, Annotation::Int(I64));
    let y_op = Operand::annotated(y, Annotation::Int(I64));
    let borrow_op = Operand::annotated(borrow, Annotation::Int(I64));
    let diff1 = b.sub(x_op.into(), y_op.into(), I64, o());
    let cmp = b.icmp(
        ICmpOp::Gt,
        diff1.into(),
        Operand::annotated(x, Annotation::Int(I64)).into(),
        o(),
    );
    let b1 = bool_to_u64(b, cmp);
    let diff2 = b.sub(diff1.into(), borrow_op.into(), I64, o());
    let cmp = b.icmp(ICmpOp::Gt, diff2.into(), diff1.into(), o());
    let b2 = bool_to_u64(b, cmp);
    let borrow_out = b.or(b1.into(), b2.into(), I64, o());
    (diff2.raw(), borrow_out.raw())
}

fn add_word_pair_u64(
    b: &mut Builder,
    lo: ValueRef,
    hi: ValueRef,
    add_lo: ValueRef,
    add_hi: ValueRef,
) -> (ValueRef, ValueRef) {
    let new_lo = b.add(
        Operand::annotated(lo, Annotation::Int(I64)).into(),
        Operand::annotated(add_lo, Annotation::Int(I64)).into(),
        I64,
        o(),
    );
    let carry = b.icmp(
        ICmpOp::Lt,
        new_lo.into(),
        Operand::annotated(lo, Annotation::Int(I64)).into(),
        o(),
    );
    let carry_int = bool_to_u64(b, carry);
    let hi_sum = b.add(
        Operand::annotated(hi, Annotation::Int(I64)).into(),
        Operand::annotated(add_hi, Annotation::Int(I64)).into(),
        I64,
        o(),
    );
    let new_hi = b.add(
        hi_sum.into(),
        Operand::annotated(carry_int, Annotation::Int(I64)).into(),
        I64,
        o(),
    );
    (new_lo.raw(), new_hi.raw())
}

fn add_into_words64(b: &mut Builder, dst: &mut [ValueRef], start: usize, src: &[ValueRef]) {
    let zero = b.iconst(0, 64, IntSignedness::Unsigned, o()).raw();
    let mut carry = zero;
    for (idx, slot) in dst.iter_mut().enumerate().skip(start) {
        let addend = src.get(idx - start).copied().unwrap_or(zero);
        let (sum, next_carry) = add3_u64(b, *slot, addend, carry);
        *slot = sum;
        carry = next_carry;
    }
}

fn sub_from_words64(b: &mut Builder, dst: &mut [ValueRef], src: &[ValueRef]) {
    let zero = b.iconst(0, 64, IntSignedness::Unsigned, o()).raw();
    let mut borrow = zero;
    for (idx, slot) in dst.iter_mut().enumerate() {
        let sub = src.get(idx).copied().unwrap_or(zero);
        let (diff, next_borrow) = sub2_u64(b, *slot, sub, borrow);
        *slot = diff;
        borrow = next_borrow;
    }
}

// ---------------------------------------------------------------------------
// Double-width add/sub with overflow detection
// ---------------------------------------------------------------------------

/// Shared double-width add core: computes (lo, hi) for a + b.
/// Returns (lo, hi, a_hi, b_hi) for use in overflow detection.
fn leg_add128_core(
    old: &Function,
    s: &mut State,
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

fn leg_uadd_with_overflow_wide(
    old: &Function,
    s: &mut State,
    b: &mut Builder,
    old_vref: ValueRef,
    a: &Operand,
    op_b: &Operand,
) {
    let bits = int_annotation_bits(value_annotation(old, old_vref)).unwrap_or(s.part_bits * 2);
    if bits > s.part_bits * 2 && bits.is_multiple_of(s.limb_bits) {
        let a_limbs = operand_limbs32(old, s, b, a, bits);
        let b_limbs = operand_limbs32(old, s, b, op_b, bits);
        let (sum, carry) = add_limbs32(s, b, &a_limbs, &b_limbs);
        let overflow = nonzero_u32(s, b, carry);
        s.vmap.set_parts(old_vref, limbs32_to_parts64(s, b, &sum));
        let old_sec = ValueRef::inst_secondary_result(old_vref.index());
        s.vmap.set(old_sec, Mapped::One(overflow.into()));
        return;
    }
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

fn leg_sadd_with_overflow_wide(
    old: &Function,
    s: &mut State,
    b: &mut Builder,
    old_vref: ValueRef,
    a: &Operand,
    op_b: &Operand,
) {
    let bits = int_annotation_bits(value_annotation(old, old_vref)).unwrap_or(s.part_bits * 2);
    if bits > s.part_bits * 2 && bits.is_multiple_of(s.limb_bits) {
        let a_limbs = operand_limbs32(old, s, b, a, bits);
        let b_limbs = operand_limbs32(old, s, b, op_b, bits);
        let (sum, _) = add_limbs32(s, b, &a_limbs, &b_limbs);
        let top_a = *a_limbs.last().expect("signed add lhs limbs");
        let top_b = *b_limbs.last().expect("signed add rhs limbs");
        let top_r = *sum.last().expect("signed add result limbs");
        let ax = b.xor(
            Operand::new(top_a).into(),
            Operand::new(top_r).into(),
            limb_ann(s),
            o(),
        );
        let bx = b.xor(
            Operand::new(top_b).into(),
            Operand::new(top_r).into(),
            limb_ann(s),
            o(),
        );
        let combined = b.and(ax.into(), bx.into(), limb_ann(s), o());
        let overflow = u32_sign_bool(s, b, combined.raw());
        s.vmap.set_parts(old_vref, limbs32_to_parts64(s, b, &sum));
        let old_sec = ValueRef::inst_secondary_result(old_vref.index());
        s.vmap.set(old_sec, Mapped::One(overflow.into()));
        return;
    }
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

fn leg_usub_with_overflow_wide(
    old: &Function,
    s: &mut State,
    b: &mut Builder,
    old_vref: ValueRef,
    a: &Operand,
    op_b: &Operand,
) {
    let bits = int_annotation_bits(value_annotation(old, old_vref)).unwrap_or(s.part_bits * 2);
    if bits > s.part_bits * 2 && bits.is_multiple_of(s.limb_bits) {
        let a_limbs = operand_limbs32(old, s, b, a, bits);
        let b_limbs = operand_limbs32(old, s, b, op_b, bits);
        let (diff, borrow) = sub_limbs32(s, b, &a_limbs, &b_limbs);
        let overflow = nonzero_u32(s, b, borrow);
        s.vmap.set_parts(old_vref, limbs32_to_parts64(s, b, &diff));
        let old_sec = ValueRef::inst_secondary_result(old_vref.index());
        s.vmap.set(old_sec, Mapped::One(overflow.into()));
        return;
    }
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

/// Double-width signed saturating add/sub.
/// `is_add == true` → saturating_add, `is_add == false` → saturating_sub.
fn leg_signed_saturating_addsub_wide(
    old: &Function,
    s: &mut State,
    b: &mut Builder,
    old_vref: ValueRef,
    a: &Operand,
    op_b: &Operand,
    is_add: bool,
) {
    let bits = result_bits(s, old, old_vref);
    if bits > s.part_bits * 2 && bits.is_multiple_of(s.limb_bits) {
        let a_limbs = operand_limbs32(old, s, b, a, bits);
        let b_limbs = operand_limbs32(old, s, b, op_b, bits);
        let result_limbs = if is_add {
            add_limbs32(s, b, &a_limbs, &b_limbs).0
        } else {
            sub_limbs32(s, b, &a_limbs, &b_limbs).0
        };
        let top_a = *a_limbs.last().expect("signed saturating lhs limbs");
        let top_b = *b_limbs.last().expect("signed saturating rhs limbs");
        let top_r = *result_limbs.last().expect("signed saturating result limbs");
        let overflow = if is_add {
            let ax = b.xor(
                Operand::new(top_a).into(),
                Operand::new(top_r).into(),
                limb_ann(s),
                o(),
            );
            let bx = b.xor(
                Operand::new(top_b).into(),
                Operand::new(top_r).into(),
                limb_ann(s),
                o(),
            );
            let combined = b.and(ax.into(), bx.into(), limb_ann(s), o());
            u32_sign_bool(s, b, combined.raw())
        } else {
            let ax = b.xor(
                Operand::new(top_a).into(),
                Operand::new(top_b).into(),
                limb_ann(s),
                o(),
            );
            let bx = b.xor(
                Operand::new(top_a).into(),
                Operand::new(top_r).into(),
                limb_ann(s),
                o(),
            );
            let combined = b.and(ax.into(), bx.into(), limb_ann(s), o());
            u32_sign_bool(s, b, combined.raw())
        };
        let a_neg = u32_sign_bool(s, b, top_a);
        let sat_limbs = signed_sat_limbs32(s, b, bits, a_neg);
        let out: Vec<ValueRef> = result_limbs
            .iter()
            .copied()
            .zip(sat_limbs)
            .map(|(res, sat)| {
                b.select(
                    overflow.into(),
                    Operand::new(sat),
                    Operand::new(res),
                    Type::Int,
                    Some(Annotation::Int(limb_ann(s))),
                    o(),
                )
            })
            .collect();
        s.vmap.set_parts(old_vref, limbs32_to_parts64(s, b, &out));
        return;
    }
    let (a_lo, a_hi) = wide_pair(s, old, b, a);
    let (b_lo, b_hi) = wide_pair(s, old, b, op_b);

    // Compute the wrapping result in the double-width decomposition.
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
    // Signed minimum = (lo=0, hi=sign-bit only)
    let min_lo = b.iconst(0i64, 64, IntSignedness::Unsigned, o());
    let min_hi = b.iconst(i64::MIN, 64, IntSignedness::Unsigned, o());
    // Signed maximum = (lo=all-ones, hi=sign-bit cleared)
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

/// Double-width unsigned saturating add/sub.
fn leg_unsigned_saturating_addsub_wide(
    old: &Function,
    s: &mut State,
    b: &mut Builder,
    old_vref: ValueRef,
    a: &Operand,
    op_b: &Operand,
    is_add: bool,
) {
    let bits = result_bits(s, old, old_vref);
    if bits > s.part_bits * 2 && bits.is_multiple_of(s.limb_bits) {
        let (result_limbs, overflow) = if is_add {
            let a_limbs = operand_limbs32(old, s, b, a, bits);
            let b_limbs = operand_limbs32(old, s, b, op_b, bits);
            let (sum, carry) = add_limbs32(s, b, &a_limbs, &b_limbs);
            (sum, nonzero_u32(s, b, carry))
        } else {
            let a_limbs = operand_limbs32(old, s, b, a, bits);
            let b_limbs = operand_limbs32(old, s, b, op_b, bits);
            let (diff, borrow) = sub_limbs32(s, b, &a_limbs, &b_limbs);
            (diff, nonzero_u32(s, b, borrow))
        };
        let sat_limbs = unsigned_sat_limbs32(s, b, bits, is_add);
        let out: Vec<ValueRef> = result_limbs
            .iter()
            .copied()
            .zip(sat_limbs)
            .map(|(res, sat)| {
                b.select(
                    overflow.into(),
                    Operand::new(sat),
                    Operand::new(res),
                    Type::Int,
                    Some(Annotation::Int(limb_ann(s))),
                    o(),
                )
            })
            .collect();
        s.vmap.set_parts(old_vref, limbs32_to_parts64(s, b, &out));
        return;
    }
    let (a_lo, a_hi) = wide_pair(s, old, b, a);
    let (b_lo, b_hi) = wide_pair(s, old, b, op_b);

    if is_add {
        // Unsigned saturating add: clamp to the maximum representable value on overflow.
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
        // Underflow: b > a in the unsigned double-width comparison
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

fn leg_ssub_with_overflow_wide(
    old: &Function,
    s: &mut State,
    b: &mut Builder,
    old_vref: ValueRef,
    a: &Operand,
    op_b: &Operand,
) {
    let bits = int_annotation_bits(value_annotation(old, old_vref)).unwrap_or(s.part_bits * 2);
    if bits > s.part_bits * 2 && bits.is_multiple_of(s.limb_bits) {
        let a_limbs = operand_limbs32(old, s, b, a, bits);
        let b_limbs = operand_limbs32(old, s, b, op_b, bits);
        let (diff, _) = sub_limbs32(s, b, &a_limbs, &b_limbs);
        let top_a = *a_limbs.last().expect("signed sub lhs limbs");
        let top_b = *b_limbs.last().expect("signed sub rhs limbs");
        let top_r = *diff.last().expect("signed sub result limbs");
        let ax = b.xor(
            Operand::new(top_a).into(),
            Operand::new(top_b).into(),
            limb_ann(s),
            o(),
        );
        let bx = b.xor(
            Operand::new(top_a).into(),
            Operand::new(top_r).into(),
            limb_ann(s),
            o(),
        );
        let combined = b.and(ax.into(), bx.into(), limb_ann(s), o());
        let overflow = u32_sign_bool(s, b, combined.raw());
        s.vmap.set_parts(old_vref, limbs32_to_parts64(s, b, &diff));
        let old_sec = ValueRef::inst_secondary_result(old_vref.index());
        s.vmap.set(old_sec, Mapped::One(overflow.into()));
        return;
    }
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

fn leg_smul_with_overflow_wide(
    old: &Function,
    s: &mut State,
    b: &mut Builder,
    old_vref: ValueRef,
    a: &Operand,
    op_b: &Operand,
) {
    let bits = int_annotation_bits(value_annotation(old, old_vref)).unwrap_or(s.part_bits * 2);
    if bits > s.part_bits * 2 && bits.is_multiple_of(s.limb_bits) {
        let limb_count = num_limbs32(bits, s.limb_bits);
        let zero = b
            .iconst(0i64, s.limb_bits, IntSignedness::Unsigned, o())
            .raw();
        let ones = limb_mask_const(s, b, s.limb_bits);
        let a_limbs = operand_limbs32(old, s, b, a, bits);
        let b_limbs = operand_limbs32(old, s, b, op_b, bits);
        let zero_vec = vec![zero; limb_count];
        let full = full_mul_add_limbs32(s, b, &a_limbs, &b_limbs, &zero_vec, &zero_vec, bits, true);
        let low = &full[..limb_count];
        let high = &full[limb_count..];
        let sign = u32_sign_bool(s, b, *low.last().expect("signed mul result limbs"));
        let mut overflow_acc = zero;
        for limb in high {
            let expected = b.select(
                sign.into(),
                Operand::new(ones),
                Operand::new(zero),
                Type::Int,
                Some(Annotation::Int(limb_ann(s))),
                o(),
            );
            let neq = b.icmp(ICmpOp::Ne, Operand::new(*limb).into(), expected.into(), o());
            let neq = bool_to_u32(s, b, neq);
            overflow_acc = b
                .or(
                    Operand::new(overflow_acc).into(),
                    Operand::new(neq).into(),
                    limb_ann(s),
                    o(),
                )
                .raw();
        }
        let overflow = nonzero_u32(s, b, overflow_acc);
        s.vmap.set_parts(old_vref, limbs32_to_parts64(s, b, low));
        let old_sec = ValueRef::inst_secondary_result(old_vref.index());
        s.vmap.set(old_sec, Mapped::One(overflow.into()));
        return;
    }
    // Compute the full product, then adjust the upper half for signed semantics
    // and check whether it matches sign extension of the lower half.
    let (a_lo, a_hi) = wide_pair(s, old, b, a);
    let (b_lo, b_hi) = wide_pair(s, old, b, op_b);

    // Four widening legal-part partial products.
    let (ll_lo, ll_hi) = widening_mul_u64(b, a_lo, b_lo);
    let (lh_lo, lh_hi) = widening_mul_u64(b, a_lo, b_hi);
    let (hl_lo, hl_hi) = widening_mul_u64(b, a_hi, b_lo);
    let (hh_lo, hh_hi) = widening_mul_u64(b, a_hi, b_hi);

    // Combine into four equal-width words of the full product:
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

    // Low half of the product.
    let prod_lo = ll_lo;
    let prod_hi = w1;

    // Adjust unsigned upper half → signed upper half:
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
        ann64.clone(),
        o(),
    );
    let sub_b_hi = b.select(
        a_neg.into(),
        Operand::new(b_hi),
        z.clone(),
        Type::Int,
        ann64.clone(),
        o(),
    );
    let sub_a_lo = b.select(
        b_neg.into(),
        Operand::new(a_lo),
        z.clone(),
        Type::Int,
        ann64.clone(),
        o(),
    );
    let sub_a_hi = b.select(
        b_neg.into(),
        Operand::new(a_hi),
        z,
        Type::Int,
        ann64.clone(),
        o(),
    );

    // Subtract the first correction vector from the upper half.
    let t_lo = b.sub(w2_sum.into(), sub_b_lo.into(), I64, o());
    let cmp = b.icmp(ICmpOp::Lt, w2_sum.into(), sub_b_lo.into(), o());
    let borrow1 = bool_to_u64(b, cmp);
    let t_hi = b.sub(w3.into(), sub_b_hi.into(), I64, o());
    let t_hi = b.sub(t_hi.into(), borrow1.into(), I64, o());

    // Subtract the second correction vector from the upper half.
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

fn leg_umul_with_overflow_wide(
    old: &Function,
    s: &mut State,
    b: &mut Builder,
    old_vref: ValueRef,
    a: &Operand,
    op_b: &Operand,
) {
    let bits = int_annotation_bits(value_annotation(old, old_vref)).unwrap_or(s.part_bits * 2);
    if bits > s.part_bits * 2 && bits.is_multiple_of(s.limb_bits) {
        let limb_count = num_limbs32(bits, s.limb_bits);
        let zero = b
            .iconst(0i64, s.limb_bits, IntSignedness::Unsigned, o())
            .raw();
        let a_limbs = operand_limbs32(old, s, b, a, bits);
        let b_limbs = operand_limbs32(old, s, b, op_b, bits);
        let zero_vec = vec![zero; limb_count];
        let full =
            full_mul_add_limbs32(s, b, &a_limbs, &b_limbs, &zero_vec, &zero_vec, bits, false);
        let low = &full[..limb_count];
        let high = &full[limb_count..];
        let mut overflow_acc = zero;
        for limb in high {
            overflow_acc = b
                .or(
                    Operand::new(overflow_acc).into(),
                    Operand::new(*limb).into(),
                    limb_ann(s),
                    o(),
                )
                .raw();
        }
        let overflow = nonzero_u32(s, b, overflow_acc);
        s.vmap.set_parts(old_vref, limbs32_to_parts64(s, b, low));
        let old_sec = ValueRef::inst_secondary_result(old_vref.index());
        s.vmap.set(old_sec, Mapped::One(overflow.into()));
        return;
    }
    // Compute the full 256-bit unsigned product.  Overflow iff the high
    // Overflow iff the upper half is non-zero.
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

    // Unsigned overflow: upper half non-zero.
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

fn leg_bitwise(
    old: &Function,
    s: &mut State,
    b: &mut Builder,
    old_vref: ValueRef,
    a: &Operand,
    op_b: &Operand,
    kind: BitwiseKind,
) {
    let bits = result_bits(s, old, old_vref);
    if bits > s.part_bits && bits.is_multiple_of(s.limb_bits) {
        let a_limbs = operand_limbs32(old, s, b, a, bits);
        let b_limbs = operand_limbs32(old, s, b, op_b, bits);
        let out: Vec<ValueRef> = a_limbs
            .iter()
            .copied()
            .zip(b_limbs.iter().copied())
            .map(|(lhs, rhs)| match kind {
                BitwiseKind::And => b
                    .and(
                        Operand::new(lhs).into(),
                        Operand::new(rhs).into(),
                        limb_ann(s),
                        o(),
                    )
                    .raw(),
                BitwiseKind::Or => b
                    .or(
                        Operand::new(lhs).into(),
                        Operand::new(rhs).into(),
                        limb_ann(s),
                        o(),
                    )
                    .raw(),
                BitwiseKind::Xor => b
                    .xor(
                        Operand::new(lhs).into(),
                        Operand::new(rhs).into(),
                        limb_ann(s),
                        o(),
                    )
                    .raw(),
            })
            .collect();
        s.vmap.set_parts(old_vref, limbs32_to_parts64(s, b, &out));
        return;
    }
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
// Wide left shift
// ---------------------------------------------------------------------------

fn leg_shl(
    old: &Function,
    s: &mut State,
    b: &mut Builder,
    old_vref: ValueRef,
    a: &Operand,
    op_b: &Operand,
    _ann: Option<&Annotation>,
) {
    let bits = result_bits(s, old, old_vref);
    if bits > s.part_bits && bits.is_multiple_of(s.limb_bits) {
        let limbs = operand_limbs32(old, s, b, a, bits);
        let out = wide_shl_limbs(s, b, &limbs, s.vmap.one(op_b.value), bits);
        s.vmap.set_parts(old_vref, limbs32_to_parts64(s, b, &out));
        return;
    }
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
// Wide right shift (logical or arithmetic based on annotation)
// ---------------------------------------------------------------------------

fn leg_shr(
    old: &Function,
    s: &mut State,
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
    let bits = result_bits(s, old, old_vref);
    if bits > s.part_bits && bits.is_multiple_of(s.limb_bits) {
        let limbs = operand_limbs32(old, s, b, a, bits);
        let out = wide_shr_limbs(s, b, &limbs, s.vmap.one(op_b.value), bits, signed);
        s.vmap.set_parts(old_vref, limbs32_to_parts64(s, b, &out));
        return;
    }
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
// Wide rotate (left or right)
// ---------------------------------------------------------------------------

/// Helper: compute a double-width left shift without setting vmap.
fn shl_double_width_pair(
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

/// Helper: compute a double-width unsigned right shift without setting vmap.
fn shr_double_width_pair(
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

fn leg_rotate_wide(
    old: &Function,
    s: &mut State,
    b: &mut Builder,
    old_vref: ValueRef,
    a: &Operand,
    amt_op: &Operand,
    is_left: bool,
) {
    let bits = result_bits(s, old, old_vref);
    if bits > s.part_bits && bits.is_multiple_of(s.limb_bits) {
        let limbs = operand_limbs32(old, s, b, a, bits);
        let amt = s.vmap.one(amt_op.value);
        let left = if is_left {
            wide_shl_limbs(s, b, &limbs, amt, bits)
        } else {
            wide_shr_limbs(s, b, &limbs, amt, bits, false)
        };
        let bits_c = b.iconst(bits as i64, s.part_bits, IntSignedness::Unsigned, o());
        let amt_mod = b.rem(
            Operand::annotated(amt, Annotation::Int(part_ann(s))).into(),
            bits_c.into(),
            part_ann(s),
            o(),
        );
        let comp = b.sub(bits_c.into(), amt_mod.into(), part_ann(s), o());
        let comp = b.rem(comp.into(), bits_c.into(), part_ann(s), o());
        let right = if is_left {
            wide_shr_limbs(s, b, &limbs, comp.raw(), bits, false)
        } else {
            wide_shl_limbs(s, b, &limbs, comp.raw(), bits)
        };
        let out: Vec<ValueRef> = left
            .iter()
            .copied()
            .zip(right.iter().copied())
            .map(|(l, r)| {
                b.or(
                    Operand::annotated(l, Annotation::Int(limb_ann(s))).into(),
                    Operand::annotated(r, Annotation::Int(limb_ann(s))).into(),
                    limb_ann(s),
                    o(),
                )
                .raw()
            })
            .collect();
        s.vmap.set_parts(old_vref, limbs32_to_parts64(s, b, &out));
        return;
    }
    let (a_lo, a_hi) = wide_pair(s, old, b, a);
    let n = s.vmap.one(amt_op.value);

    // Mask shift amount to 0..127
    let c127 = b.iconst(127i64, 64, IntSignedness::Unsigned, o());
    let n_mod = b.and(n.into(), c127.into(), I64, o()).raw();

    // Complement: (bits - n_mod) mod bits
    // When n_mod == 0, the complement becomes 0 and the combined result is the identity.
    // then shl_result | shr_result = x | x = x, which is correct.
    let width_total = b.iconst(
        (s.part_bits * 2) as i64,
        s.part_bits,
        IntSignedness::Unsigned,
        o(),
    );
    let comp = b.sub(width_total.into(), n_mod.into(), part_ann(s), o());
    let comp_mod = b.and(comp.into(), c127.into(), I64, o()).raw();

    let (fwd_lo, fwd_hi, bwd_lo, bwd_hi) = if is_left {
        let (shl_lo, shl_hi) = shl_double_width_pair(b, a_lo, a_hi, n_mod);
        let (shr_lo, shr_hi) = shr_double_width_pair(b, a_lo, a_hi, comp_mod);
        (shl_lo, shl_hi, shr_lo, shr_hi)
    } else {
        let (shr_lo, shr_hi) = shr_double_width_pair(b, a_lo, a_hi, n_mod);
        let (shl_lo, shl_hi) = shl_double_width_pair(b, a_lo, a_hi, comp_mod);
        (shr_lo, shr_hi, shl_lo, shl_hi)
    };

    let lo = b.or(fwd_lo.into(), bwd_lo.into(), I64, o());
    let hi = b.or(fwd_hi.into(), bwd_hi.into(), I64, o());

    s.vmap.set(old_vref, Mapped::Pair(lo.raw(), hi.raw()));
}

// ---------------------------------------------------------------------------
// Wide bit reverse
// ---------------------------------------------------------------------------

fn leg_bit_reverse_wide(
    old: &Function,
    s: &mut State,
    b: &mut Builder,
    old_vref: ValueRef,
    a: &Operand,
) {
    let bits = result_bits(s, old, old_vref);
    if bits > s.part_bits && bits.is_multiple_of(s.limb_bits) {
        let limbs = operand_limbs32(old, s, b, a, bits);
        let rev: Vec<ValueRef> = limbs
            .into_iter()
            .rev()
            .map(|limb| b.bit_reverse(Operand::new(limb).into(), 32, o()).raw())
            .collect();
        s.vmap.set_parts(old_vref, limbs32_to_parts64(s, b, &rev));
        return;
    }
    let (a_lo, a_hi) = wide_pair(s, old, b, a);

    // bit_reverse on a two-part value = swap(bit_reverse(hi), bit_reverse(lo))
    // Reverse bits in each half, then swap the halves.
    let rev_lo = b.bit_reverse(a_lo.into(), 64, o());
    let rev_hi = b.bit_reverse(a_hi.into(), 64, o());

    // Swapped: lo of result = reversed hi, hi of result = reversed lo
    s.vmap
        .set(old_vref, Mapped::Pair(rev_hi.raw(), rev_lo.raw()));
}

// ---------------------------------------------------------------------------
// Two-part integer comparison
// ---------------------------------------------------------------------------

fn leg_icmp(
    old: &Function,
    s: &mut State,
    b: &mut Builder,
    old_vref: ValueRef,
    cmp_op: ICmpOp,
    a: &Operand,
    op_b: &Operand,
) {
    let operand_bits = |op: &Operand| {
        op.annotation
            .as_ref()
            .and_then(|ann| int_annotation_bits(Some(ann)))
            .or_else(|| {
                value_annotation(old, op.value).and_then(|ann| int_annotation_bits(Some(ann)))
            })
            .unwrap_or_else(|| {
                if is_wide(s, op.value) {
                    s.vmap.parts(op.value).len() as u32 * s.part_bits
                } else {
                    s.part_bits
                }
            })
    };
    let bits = operand_bits(a).max(operand_bits(op_b));
    let a_parts = operand_parts64(old, s, b, a, bits);
    let b_parts = operand_parts64(old, s, b, op_b, bits);
    let signed = is_signed_annotation(
        a.annotation
            .as_ref()
            .or_else(|| value_annotation(old, a.value)),
    );
    let unsigned_part = IntAnnotation {
        bit_width: s.part_bits,
        signedness: IntSignedness::Unsigned,
    };
    let signed_part = IntAnnotation {
        bit_width: s.part_bits,
        signedness: IntSignedness::Signed,
    };

    let result = match cmp_op {
        ICmpOp::Eq => {
            let mut or_diff = b
                .iconst(0i64, s.part_bits, IntSignedness::Unsigned, o())
                .raw();
            for (lhs, rhs) in a_parts.iter().copied().zip(b_parts.iter().copied()) {
                let diff = b.xor(
                    Operand::annotated(lhs, Annotation::Int(unsigned_part)).into(),
                    Operand::annotated(rhs, Annotation::Int(unsigned_part)).into(),
                    unsigned_part,
                    o(),
                );
                or_diff = b
                    .or(
                        Operand::annotated(or_diff, Annotation::Int(unsigned_part)).into(),
                        diff.into(),
                        unsigned_part,
                        o(),
                    )
                    .raw();
            }
            let zero = b.iconst(0, s.part_bits, IntSignedness::DontCare, o());
            b.icmp(ICmpOp::Eq, or_diff.into(), zero.into(), o()).raw()
        }
        ICmpOp::Ne => {
            let mut or_diff = b
                .iconst(0i64, s.part_bits, IntSignedness::Unsigned, o())
                .raw();
            for (lhs, rhs) in a_parts.iter().copied().zip(b_parts.iter().copied()) {
                let diff = b.xor(
                    Operand::annotated(lhs, Annotation::Int(unsigned_part)).into(),
                    Operand::annotated(rhs, Annotation::Int(unsigned_part)).into(),
                    unsigned_part,
                    o(),
                );
                or_diff = b
                    .or(
                        Operand::annotated(or_diff, Annotation::Int(unsigned_part)).into(),
                        diff.into(),
                        unsigned_part,
                        o(),
                    )
                    .raw();
            }
            let zero = b.iconst(0, s.part_bits, IntSignedness::DontCare, o());
            b.icmp(ICmpOp::Ne, or_diff.into(), zero.into(), o()).raw()
        }
        ICmpOp::Lt | ICmpOp::Le | ICmpOp::Gt | ICmpOp::Ge => {
            let mut acc = b
                .bconst(matches!(cmp_op, ICmpOp::Le | ICmpOp::Ge), o())
                .raw();
            let mut eq_prefix = b.bconst(true, o()).raw();
            let top_idx = a_parts.len().saturating_sub(1);
            for (idx, (lhs, rhs)) in a_parts
                .iter()
                .copied()
                .zip(b_parts.iter().copied())
                .enumerate()
                .rev()
            {
                let ann = if signed && idx == top_idx {
                    signed_part
                } else {
                    unsigned_part
                };
                let part_cmp = b.icmp(
                    cmp_op,
                    Operand::annotated(lhs, Annotation::Int(ann)).into(),
                    Operand::annotated(rhs, Annotation::Int(ann)).into(),
                    o(),
                );
                let part_eq = b.icmp(
                    ICmpOp::Eq,
                    Operand::annotated(lhs, Annotation::Int(unsigned_part)).into(),
                    Operand::annotated(rhs, Annotation::Int(unsigned_part)).into(),
                    o(),
                );
                let candidate = b.select(
                    part_eq.into(),
                    Operand::new(acc),
                    part_cmp.into(),
                    Type::Bool,
                    None,
                    o(),
                );
                acc = b.select(
                    Operand::new(eq_prefix).into(),
                    Operand::new(candidate),
                    Operand::new(acc),
                    Type::Bool,
                    None,
                    o(),
                );
                eq_prefix = b
                    .band(Operand::new(eq_prefix).into(), part_eq.into(), o())
                    .raw();
            }
            acc
        }
    };
    s.vmap.set(old_vref, Mapped::One(result));
}

// ---------------------------------------------------------------------------
// Wide load
// ---------------------------------------------------------------------------

fn leg_load_wide(
    s: &mut State,
    b: &mut Builder,
    old_vref: ValueRef,
    bytes: u32,
    ptr: &Operand,
    mem: &Operand,
) {
    if bytes > 16 {
        let p = s.vmap.one(ptr.value);
        let m = s.vmap.one(mem.value);
        let mut parts = Vec::with_capacity(bytes.div_ceil(8) as usize);
        for off in (0..bytes).step_by(8) {
            let chunk = (bytes - off).min(8);
            let addr = if off == 0 {
                p
            } else {
                let off_v = b.iconst(off as i64, 64, IntSignedness::Unsigned, o());
                b.ptradd(Operand::new(p).into(), off_v.into(), 0, o()).raw()
            };
            let loaded = b.load(
                Operand::new(addr).into(),
                chunk,
                I64_TYPE,
                Operand::new(m).into(),
                None,
                o(),
            );
            let part = if chunk < 8 {
                b.zext(loaded.into(), 64, o()).raw()
            } else {
                loaded
            };
            parts.push(part);
        }
        s.vmap.set_parts(old_vref, parts);
        return;
    }
    let p = s.vmap.one(ptr.value);
    let m = s.vmap.one(mem.value);

    let lo = b.load(p.into(), 8, I64_TYPE, m.into(), None, o());
    let c8 = b.iconst(8i64, 64, IntSignedness::Unsigned, o());
    let p_hi = b.ptradd(p.into(), c8.into(), 0, o());
    let hi = b.load(p_hi.into(), 8, I64_TYPE, m.into(), None, o());
    s.vmap.set(old_vref, Mapped::Pair(lo, hi));
}

// ---------------------------------------------------------------------------
// Wide store
// ---------------------------------------------------------------------------

#[allow(clippy::too_many_arguments)]
fn leg_store_wide(
    old: &Function,
    s: &mut State,
    b: &mut Builder,
    old_vref: ValueRef,
    bytes: u32,
    val: &Operand,
    ptr: &Operand,
    mem: &Operand,
) {
    if bytes > 16 {
        let parts = if is_wide(s, val.value) {
            s.vmap.parts(val.value)
        } else if !val.value.is_block_arg()
            && !val.value.is_secondary_result()
            && let Op::Const(bigval) = &old.inst(val.value.index()).op
        {
            const_parts_for_bits(b, bigval, bytes * 8, s.part_bits)
        } else {
            vec![s.vmap.one(val.value)]
        };
        let p = s.vmap.one(ptr.value);
        let mut cur_mem = s.vmap.one(mem.value);
        for (i, part) in parts.into_iter().enumerate() {
            let off = (i as u32) * 8;
            if off >= bytes {
                break;
            }
            let chunk = (bytes - off).min(8);
            let addr = if off == 0 {
                p
            } else {
                let off_v = b.iconst(off as i64, 64, IntSignedness::Unsigned, o());
                b.ptradd(Operand::new(p).into(), off_v.into(), 0, o()).raw()
            };
            cur_mem = b
                .store(
                    Operand::new(part),
                    Operand::new(addr).into(),
                    chunk,
                    Operand::new(cur_mem).into(),
                    o(),
                )
                .raw();
        }
        s.vmap.set(old_vref, Mapped::One(cur_mem));
        return;
    }
    // Split the stored wide value into legal parts.
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
// Sign-extend to a wider-than-legal integer
// ---------------------------------------------------------------------------

fn leg_sext_wide(s: &mut State, b: &mut Builder, old_vref: ValueRef, bits: u32, val: &Operand) {
    if bits > s.part_bits {
        let lo = s.vmap.one(val.value);
        let shift = b.iconst(
            (s.part_bits - 1) as i64,
            s.part_bits,
            IntSignedness::Unsigned,
            o(),
        );
        let signed_part = IntAnnotation {
            bit_width: s.part_bits,
            signedness: IntSignedness::Signed,
        };
        let hi = b
            .shr(
                Operand::annotated(lo, Annotation::Int(signed_part)).into(),
                shift.into(),
                signed_part,
                o(),
            )
            .raw();
        let mut parts = vec![lo, hi];
        while parts.len() < num_parts64(bits, s.part_bits) {
            parts.push(hi);
        }
        s.vmap.set_parts(old_vref, parts);
        return;
    }
    let lo = s.vmap.one(val.value);
    let c63 = b.iconst(63i64, 64, IntSignedness::Unsigned, o());
    // Arithmetic shift right: propagate the sign bit of lo into hi.
    // Must pass a Signed annotation so the ISel emits SAR, not SHR.
    let hi = b.shr(lo.into(), c63.into(), SIGNED_64_INT, o());
    s.vmap.set(old_vref, Mapped::Pair(lo, hi.raw()));
}

// ---------------------------------------------------------------------------
// Zero-extend to a wider-than-legal integer
// ---------------------------------------------------------------------------

fn leg_zext_wide(s: &mut State, b: &mut Builder, old_vref: ValueRef, bits: u32, val: &Operand) {
    if bits > s.part_bits {
        let lo = s.vmap.one(val.value);
        let hi = b
            .iconst(0i64, s.part_bits, IntSignedness::Unsigned, o())
            .raw();
        let mut parts = vec![lo];
        while parts.len() < num_parts64(bits, s.part_bits) {
            parts.push(hi);
        }
        s.vmap.set_parts(old_vref, parts);
        return;
    }
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
// float → double-width integer: lower to compiler-rt libcall
//   The exact symbol suffix is chosen from the legalized double-width bits
//   (`si` / `di` / `ti`), e.g. `__fixunsdfdi` or `__fixdfti`.
// Called from the wide Zext(fp_to_ui) and Sext(fp_to_si) handlers
// to provide correct saturation semantics for overflow/infinity/NaN.
// ---------------------------------------------------------------------------

#[allow(clippy::too_many_arguments)]
fn leg_fp_to_int_double_width(
    s: &mut State,
    b: &mut Builder,
    old_vref: ValueRef,
    // Operand of the outer Zext/Sext — its value is the FpToUi/FpToSi result.
    zext_val: &Operand,
    signed: bool,
    ft: FloatType,
    old: &Function,
    symbols: &mut SymbolTable,
) {
    debug_assert_eq!(result_bits(s, old, old_vref), s.part_bits * 2);
    // Retrieve the float input to the FpToUi/FpToSi instruction.
    let fp_input_vref = match old.inst_pool.get(zext_val.value.index()) {
        Some(node) => match &node.inst.op {
            Op::FpToUi(a) | Op::FpToSi(a) => a.clone().raw().value,
            _ => {
                // Not the expected pattern; fall back to simple extend.
                let lo = s.vmap.one(zext_val.value);
                let hi = if signed {
                    let shift = b.iconst(
                        (s.part_bits - 1) as i64,
                        s.part_bits,
                        IntSignedness::Unsigned,
                        o(),
                    );
                    let signed_part = IntAnnotation {
                        bit_width: s.part_bits,
                        signedness: IntSignedness::Signed,
                    };
                    b.shr(
                        Operand::annotated(lo, Annotation::Int(signed_part)).into(),
                        shift.into(),
                        signed_part,
                        o(),
                    )
                } else {
                    b.iconst(0i64, s.part_bits, IntSignedness::Unsigned, o())
                };
                s.vmap.set(old_vref, Mapped::Pair(lo, hi.raw()));
                return;
            }
        },
        None => {
            let lo = s.vmap.one(zext_val.value);
            let hi = b.iconst(0i64, s.part_bits, IntSignedness::Unsigned, o());
            s.vmap.set(old_vref, Mapped::Pair(lo, hi.raw()));
            return;
        }
    };

    let name = fp_to_int_double_width_libcall_name(s.part_bits * 2, signed, ft);
    let sym_id = symbols.intern(&name);
    let callee = b.symbol_addr(sym_id, o()).raw();

    // The float value in the remapped IR.
    let float_val = s.vmap.one(fp_input_vref);

    let old_mem = s
        .current_old_mem
        .expect("float-to-double-width-int requires a mem token in scope");
    let new_mem = s.vmap.one(old_mem);

    let (call_mem, data) = b.call(
        Operand::new(callee).into(),
        vec![Operand::new(float_val)],
        I64_TYPE,
        Operand::new(new_mem).into(),
        None,
        None,
        o(),
    );
    let data = data.unwrap();

    s.vmap.set(old_mem, Mapped::One(call_mem.into()));

    let hi_capture = b.call_ret2(
        Operand::new(call_mem.into()).into(),
        Type::Int,
        Some(Annotation::Int(I64)),
        o(),
    );

    s.vmap.set(old_vref, Mapped::Pair(data, hi_capture));
}

fn leg_fp_to_int_wide(
    s: &mut State,
    b: &mut Builder,
    old_vref: ValueRef,
    zext_val: &Operand,
    signed: bool,
    ft: FloatType,
    old: &Function,
) {
    let bits = result_bits(s, old, old_vref);
    let Some((src_bits, exp_bits, frac_bits, bias)) = fp_format_params(ft) else {
        panic!("unsupported wide float-to-int source type: {ft:?}");
    };

    let fp_input_vref = match old.inst_pool.get(zext_val.value.index()) {
        Some(node) => match &node.inst.op {
            Op::FpToUi(a) | Op::FpToSi(a) => a.clone().raw().value,
            _ => {
                if signed {
                    leg_sext_wide(s, b, old_vref, bits, zext_val);
                } else {
                    leg_zext_wide(s, b, old_vref, bits, zext_val);
                }
                return;
            }
        },
        None => {
            if signed {
                leg_sext_wide(s, b, old_vref, bits, zext_val);
            } else {
                leg_zext_wide(s, b, old_vref, bits, zext_val);
            }
            return;
        }
    };

    let float_val = s.vmap.one(fp_input_vref);
    let src_ann = IntAnnotation {
        bit_width: src_bits,
        signedness: IntSignedness::Unsigned,
    };
    let raw_bits = b.bitcast(
        Operand::new(float_val),
        Type::Int,
        Some(Annotation::Int(src_ann)),
        o(),
    );
    let raw_bits = if src_bits < 64 {
        b.zext(
            Operand::annotated(raw_bits, Annotation::Int(src_ann)).into(),
            64,
            o(),
        )
        .raw()
    } else {
        raw_bits
    };

    let zero64 = b.iconst(0i64, 64, IntSignedness::Unsigned, o()).raw();
    let raw_bits_op = Operand::annotated(raw_bits, Annotation::Int(I64));
    let frac_mask = b.iconst(
        (BigInt::from(1u8) << frac_bits) - BigInt::from(1u8),
        64,
        IntSignedness::Unsigned,
        o(),
    );
    let exp_mask = b.iconst(
        (BigInt::from(1u8) << exp_bits) - BigInt::from(1u8),
        64,
        IntSignedness::Unsigned,
        o(),
    );
    let hidden = b.iconst(
        BigInt::from(1u8) << frac_bits,
        64,
        IntSignedness::Unsigned,
        o(),
    );
    let bias_c = b.iconst(bias as i64, 64, IntSignedness::Unsigned, o());
    let frac_bits_c = b.iconst(frac_bits as i64, 64, IntSignedness::Unsigned, o());
    let sign_shift = b.iconst((src_bits - 1) as i64, 64, IntSignedness::Unsigned, o());

    let frac = b
        .and(raw_bits_op.clone().into(), frac_mask.into(), I64, o())
        .raw();
    let exp_shifted = b
        .shr(raw_bits_op.clone().into(), frac_bits_c.into(), I64, o())
        .raw();
    let exp_raw = b
        .and(
            Operand::annotated(exp_shifted, Annotation::Int(I64)).into(),
            exp_mask.into(),
            I64,
            o(),
        )
        .raw();
    let sign_raw = b.shr(raw_bits_op.into(), sign_shift.into(), I64, o()).raw();
    let sign = b.icmp(
        ICmpOp::Ne,
        Operand::annotated(sign_raw, Annotation::Int(I64)).into(),
        Operand::annotated(zero64, Annotation::Int(I64)).into(),
        o(),
    );

    let exp_zero = b.icmp(
        ICmpOp::Eq,
        Operand::annotated(exp_raw, Annotation::Int(I64)).into(),
        Operand::annotated(zero64, Annotation::Int(I64)).into(),
        o(),
    );
    let exp_all_ones = b.icmp(
        ICmpOp::Eq,
        Operand::annotated(exp_raw, Annotation::Int(I64)).into(),
        exp_mask.into(),
        o(),
    );
    let frac_zero = b.icmp(
        ICmpOp::Eq,
        Operand::annotated(frac, Annotation::Int(I64)).into(),
        Operand::annotated(zero64, Annotation::Int(I64)).into(),
        o(),
    );
    let frac_nonzero = bool_not(b, frac_zero);
    let is_nan = b.band(exp_all_ones.into(), frac_nonzero.into(), o());
    let exp_too_small = b.icmp(
        ICmpOp::Lt,
        Operand::annotated(exp_raw, Annotation::Int(I64)).into(),
        bias_c.into(),
        o(),
    );
    let exp_nonzero = bool_not(b, exp_zero);
    let not_all_ones = bool_not(b, exp_all_ones);
    let normal = b.band(exp_nonzero.into(), not_all_ones.into(), o());

    let sig_base = b.or(
        Operand::annotated(frac, Annotation::Int(I64)).into(),
        hidden.into(),
        I64,
        o(),
    );
    let significand = b.select(
        normal.into(),
        Operand::annotated(sig_base.raw(), Annotation::Int(I64)),
        Operand::annotated(zero64, Annotation::Int(I64)),
        Type::Int,
        Some(Annotation::Int(I64)),
        o(),
    );

    let unbiased_raw = b.sub(
        Operand::annotated(exp_raw, Annotation::Int(I64)).into(),
        bias_c.into(),
        I64,
        o(),
    );
    let small_or_special = b.bor(exp_too_small.into(), exp_all_ones.into(), o());
    let unbiased = b.select(
        small_or_special.into(),
        Operand::annotated(zero64, Annotation::Int(I64)),
        Operand::annotated(unbiased_raw.raw(), Annotation::Int(I64)),
        Type::Int,
        Some(Annotation::Int(I64)),
        o(),
    );
    let exp_ge_frac = b.icmp(
        ICmpOp::Ge,
        Operand::annotated(unbiased, Annotation::Int(I64)).into(),
        frac_bits_c.into(),
        o(),
    );
    let zero_shift = b.iconst(0i64, 64, IntSignedness::Unsigned, o()).raw();
    let shift_left_raw = b.sub(
        Operand::annotated(unbiased, Annotation::Int(I64)).into(),
        frac_bits_c.into(),
        I64,
        o(),
    );
    let shift_left = b.select(
        exp_ge_frac.into(),
        Operand::annotated(shift_left_raw.raw(), Annotation::Int(I64)),
        Operand::annotated(zero_shift, Annotation::Int(I64)),
        Type::Int,
        Some(Annotation::Int(I64)),
        o(),
    );
    let shift_right_raw = b.sub(
        frac_bits_c.into(),
        Operand::annotated(unbiased, Annotation::Int(I64)).into(),
        I64,
        o(),
    );
    let shift_right = b.select(
        exp_ge_frac.into(),
        Operand::annotated(zero_shift, Annotation::Int(I64)),
        Operand::annotated(shift_right_raw.raw(), Annotation::Int(I64)),
        Type::Int,
        Some(Annotation::Int(I64)),
        o(),
    );

    let sig_wide = wide_uint_from_small_value(s, b, significand, 64, bits);
    let left_mag_raw = wide_shl_limbs(s, b, &sig_wide, shift_left, bits);
    let left_mag = normalize_limbs32(s, b, &left_mag_raw, bits);
    let sig_right = b.shr(
        Operand::annotated(significand, Annotation::Int(I64)).into(),
        Operand::annotated(shift_right, Annotation::Int(I64)).into(),
        I64,
        o(),
    );
    let right_mag = wide_uint_from_small_value(s, b, sig_right.raw(), 64, bits);
    let magnitude = select_limbs32(s, b, exp_ge_frac, &left_mag, &right_mag);

    let zero_limbs = zero_limbs32(s, b, num_limbs32(bits, s.limb_bits));
    let result_limbs = if signed {
        let limit = b.iconst((bias + bits - 1) as i64, 64, IntSignedness::Unsigned, o());
        let exp_gt_limit = b.icmp(
            ICmpOp::Gt,
            Operand::annotated(exp_raw, Annotation::Int(I64)).into(),
            limit.into(),
            o(),
        );
        let exp_eq_limit = b.icmp(
            ICmpOp::Eq,
            Operand::annotated(exp_raw, Annotation::Int(I64)).into(),
            limit.into(),
            o(),
        );
        let neg_edge_over = b.band(exp_eq_limit.into(), frac_nonzero.into(), o());
        let exp_gt_or_edge = b.bor(exp_gt_limit.into(), neg_edge_over.into(), o());
        let neg_over = b.band(sign.into(), exp_gt_or_edge.into(), o());
        let not_sign = bool_not(b, sign);
        let pos_eq_over = b.band(not_sign.into(), exp_eq_limit.into(), o());
        let pos_gt_over = b.band(not_sign.into(), exp_gt_limit.into(), o());
        let pos_over = b.bor(pos_eq_over.into(), pos_gt_over.into(), o());
        let overflow = b.bor(pos_over.into(), neg_over.into(), o());
        let neg_mag = negate_limbs32(s, b, &magnitude, bits);
        let signed_mag = select_limbs32(s, b, sign, &neg_mag, &magnitude);
        let sat = signed_sat_limbs32(s, b, bits, sign);
        let saturated = select_limbs32(s, b, overflow, &sat, &signed_mag);
        let zero_cond = b.bor(is_nan.into(), exp_too_small.into(), o());
        select_limbs32(s, b, zero_cond, &zero_limbs, &saturated)
    } else {
        let limit = b.iconst((bias + bits) as i64, 64, IntSignedness::Unsigned, o());
        let exp_over = b.icmp(
            ICmpOp::Ge,
            Operand::annotated(exp_raw, Annotation::Int(I64)).into(),
            limit.into(),
            o(),
        );
        let not_sign = bool_not(b, sign);
        let pos_over = b.band(not_sign.into(), exp_over.into(), o());
        let max = unsigned_sat_limbs32(s, b, bits, true);
        let saturated = select_limbs32(s, b, pos_over, &max, &magnitude);
        let sign_or_small = b.bor(sign.into(), exp_too_small.into(), o());
        let zero_cond = b.bor(is_nan.into(), sign_or_small.into(), o());
        select_limbs32(s, b, zero_cond, &zero_limbs, &saturated)
    };

    s.vmap
        .set_parts(old_vref, limbs32_to_parts64(s, b, &result_limbs));
}

// ---------------------------------------------------------------------------
// Wide bswap
// ---------------------------------------------------------------------------

fn leg_bswap_wide(s: &mut State, b: &mut Builder, old_vref: ValueRef, bytes: u32, val: &Operand) {
    let part_bytes = s.part_bits / 8;
    let limb_bytes = s.limb_bits / 8;
    if bytes > part_bytes && limb_bytes > 0 && bytes.is_multiple_of(limb_bytes) {
        let bits = bytes * 8;
        let limbs = split_parts64_to_limbs32(
            s,
            b,
            &s.vmap.parts(val.value),
            num_limbs32(bits, s.limb_bits),
        );
        let rev: Vec<ValueRef> = limbs
            .into_iter()
            .rev()
            .map(|limb| b.bswap(Operand::new(limb).into(), limb_bytes, o()).raw())
            .collect();
        s.vmap.set_parts(old_vref, limbs32_to_parts64(s, b, &rev));
        return;
    }
    let (v_lo, v_hi) = s.vmap.pair(val.value);
    let new_lo = b.bswap(v_hi.into(), 8, o());
    let new_hi = b.bswap(v_lo.into(), 8, o());
    s.vmap
        .set(old_vref, Mapped::Pair(new_lo.raw(), new_hi.raw()));
}

// ---------------------------------------------------------------------------
// Wide select
// ---------------------------------------------------------------------------

fn leg_select_wide(
    old: &Function,
    s: &mut State,
    b: &mut Builder,
    old_vref: ValueRef,
    cond: &Operand,
    tv: &Operand,
    fv: &Operand,
) {
    let bits = result_bits(s, old, old_vref);
    if bits > s.part_bits && bits.is_multiple_of(s.limb_bits) {
        let c = s.vmap.one(cond.value);
        let t_limbs = operand_limbs32(old, s, b, tv, bits);
        let f_limbs = operand_limbs32(old, s, b, fv, bits);
        let out: Vec<ValueRef> = t_limbs
            .iter()
            .copied()
            .zip(f_limbs.iter().copied())
            .map(|(t, f)| {
                b.select(
                    Operand::new(c).into(),
                    Operand::new(t),
                    Operand::new(f),
                    Type::Int,
                    Some(Annotation::Int(limb_ann(s))),
                    o(),
                )
            })
            .collect();
        s.vmap.set_parts(old_vref, limbs32_to_parts64(s, b, &out));
        return;
    }
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
// Wide integer Div/Rem
// ---------------------------------------------------------------------------

fn leg_div_rem_wide(
    old: &Function,
    s: &mut State,
    b: &mut Builder,
    old_vref: ValueRef,
    a: &Operand,
    op_b: &Operand,
    is_div: bool,
) {
    let bits = result_bits(s, old, old_vref);
    let limb_count = num_limbs32(bits, s.limb_bits);
    let a_limbs_raw = operand_limbs32(old, s, b, a, bits);
    let a_limbs = normalize_limbs32(s, b, &a_limbs_raw, bits);
    let b_limbs_raw = operand_limbs32(old, s, b, op_b, bits);
    let b_limbs = normalize_limbs32(s, b, &b_limbs_raw, bits);
    let signed = is_signed_annotation(a.annotation.as_ref());

    let (result_limbs, div_zero) = if signed {
        let a_neg = u32_sign_bool(s, b, *a_limbs.last().expect("signed wide div lhs limbs"));
        let b_neg = u32_sign_bool(s, b, *b_limbs.last().expect("signed wide div rhs limbs"));
        let neg_a = negate_limbs32(s, b, &a_limbs, bits);
        let neg_b = negate_limbs32(s, b, &b_limbs, bits);
        let abs_a = select_limbs32(s, b, a_neg, &neg_a, &a_limbs);
        let abs_b = select_limbs32(s, b, b_neg, &neg_b, &b_limbs);
        let (quot_mag, rem_mag, div_zero) = udivrem_limbs32(s, b, &abs_a, &abs_b, bits);
        let quot_neg = b.bxor(a_neg.into(), b_neg.into(), o());
        let neg_quot = negate_limbs32(s, b, &quot_mag, bits);
        let quot = select_limbs32(s, b, quot_neg, &neg_quot, &quot_mag);
        let neg_rem = negate_limbs32(s, b, &rem_mag, bits);
        let rem = select_limbs32(s, b, a_neg, &neg_rem, &rem_mag);
        (if is_div { quot } else { rem }, div_zero)
    } else {
        let (quot, rem, div_zero) = udivrem_limbs32(s, b, &a_limbs, &b_limbs, bits);
        (if is_div { quot } else { rem }, div_zero)
    };

    let poison = poison_limbs32(s, b, limb_count);
    let result_limbs = select_limbs32(s, b, div_zero, &poison, &result_limbs);
    s.vmap
        .set_parts(old_vref, limbs32_to_parts64(s, b, &result_limbs));
}

// ---------------------------------------------------------------------------
// Double-width integer Div/Rem: lower to compiler-rt libcall
//   The exact symbol suffix is chosen from the legalized double-width bits
//   (`si` / `di` / `ti`), e.g. `__divdi3` or `__udivti3`.
// ---------------------------------------------------------------------------

#[allow(clippy::too_many_arguments)]
fn leg_div_rem_double_width(
    old: &Function,
    s: &mut State,
    b: &mut Builder,
    old_vref: ValueRef,
    a: &Operand,
    op_b: &Operand,
    _ann: Option<&Annotation>,
    is_div: bool,
    symbols: &mut SymbolTable,
) {
    debug_assert_eq!(result_bits(s, old, old_vref), s.part_bits * 2);
    let signed = is_signed_annotation(a.annotation.as_ref());
    let name = div_rem_double_width_libcall_name(s.part_bits * 2, is_div, signed);
    let sym_id = symbols.intern(&name);
    let callee = b.symbol_addr(sym_id, o()).raw();

    let a_parts = operand_parts64(old, s, b, a, s.part_bits * 2);
    let b_parts = operand_parts64(old, s, b, op_b, s.part_bits * 2);
    let a_lo = a_parts[0];
    let a_hi = a_parts[1];
    let b_lo = b_parts[0];
    let b_hi = b_parts[1];
    let args = vec![
        Operand::new(a_lo),
        Operand::new(a_hi),
        Operand::new(b_lo),
        Operand::new(b_hi),
    ];

    // Inject the call into the mem chain using the most recent mem token.
    let old_mem = s
        .current_old_mem
        .expect("wide div/rem requires a mem token in scope");
    let new_mem = s.vmap.one(old_mem);
    let (call_mem, data) = b.call(
        Operand::new(callee).into(),
        args,
        I64_TYPE,
        Operand::new(new_mem).into(),
        None,
        None,
        o(),
    );
    let data = data.unwrap();

    // Redirect all subsequent users of old_mem to call_mem so that later
    // stores/calls pick up the updated mem without rewriting their operands.
    s.vmap.set(old_mem, Mapped::One(call_mem.into()));

    let hi_capture = b.call_ret2(
        Operand::new(call_mem.into()).into(),
        Type::Int,
        Some(Annotation::Int(I64)),
        o(),
    );

    // Map the old wide Div/Rem result to (lo, hi).
    s.vmap.set(old_vref, Mapped::Pair(data, hi_capture));
}

// ---------------------------------------------------------------------------
// Wide integer to float: lower via target-derived limb rounding
// ---------------------------------------------------------------------------

fn wide_bit_length(s: &State, b: &mut Builder, limbs: &[ValueRef], bits: u32) -> ValueRef {
    let widths = wide_limb_widths(s, bits);
    let zero_part = b
        .iconst(0i64, s.part_bits, IntSignedness::Unsigned, o())
        .raw();
    let zero_limb = b
        .iconst(0i64, s.limb_bits, IntSignedness::Unsigned, o())
        .raw();
    let false_b = b.bconst(false, o());
    let mut clz = zero_part;
    let mut done = false_b;
    for (limb, limb_bits) in limbs.iter().copied().zip(widths).rev() {
        let limb_bits_val = b.iconst(limb_bits as i64, s.part_bits, IntSignedness::Unsigned, o());
        let limb_zero = b.icmp(
            ICmpOp::Eq,
            Operand::annotated(limb, Annotation::Int(limb_ann(s))).into(),
            Operand::annotated(zero_limb, Annotation::Int(limb_ann(s))).into(),
            o(),
        );
        let limb_clz = b
            .count_leading_zeros(
                Operand::annotated(limb, Annotation::Int(limb_ann(s))).into(),
                limb_bits,
                s.part_bits,
                o(),
            )
            .raw();
        let next_zero = b
            .add(
                Operand::annotated(clz, Annotation::Int(part_ann(s))).into(),
                limb_bits_val.into(),
                part_ann(s),
                o(),
            )
            .raw();
        let next_nonzero = b
            .add(
                Operand::annotated(clz, Annotation::Int(part_ann(s))).into(),
                Operand::annotated(limb_clz, Annotation::Int(part_ann(s))).into(),
                part_ann(s),
                o(),
            )
            .raw();
        let candidate = b.select(
            limb_zero.into(),
            Operand::annotated(next_zero, Annotation::Int(part_ann(s))),
            Operand::annotated(next_nonzero, Annotation::Int(part_ann(s))),
            Type::Int,
            Some(Annotation::Int(part_ann(s))),
            o(),
        );
        clz = b.select(
            done.into(),
            Operand::annotated(clz, Annotation::Int(part_ann(s))),
            Operand::annotated(candidate, Annotation::Int(part_ann(s))),
            Type::Int,
            Some(Annotation::Int(part_ann(s))),
            o(),
        );
        let limb_nonzero = b.icmp(
            ICmpOp::Ne,
            Operand::annotated(limb, Annotation::Int(limb_ann(s))).into(),
            Operand::annotated(zero_limb, Annotation::Int(limb_ann(s))).into(),
            o(),
        );
        done = b.bor(done.into(), limb_nonzero.into(), o());
    }
    let bits_c = b.iconst(bits as i64, s.part_bits, IntSignedness::Unsigned, o());
    b.sub(
        bits_c.into(),
        Operand::annotated(clz, Annotation::Int(part_ann(s))).into(),
        part_ann(s),
        o(),
    )
    .raw()
}

fn leg_int_to_fp_wide(
    old: &Function,
    s: &mut State,
    b: &mut Builder,
    old_vref: ValueRef,
    a: &Operand,
    ft: FloatType,
    signed: bool,
) {
    let bits = operand_int_bits(old, a).expect("wide int-to-fp requires integer source bits");
    let Some((src_float_bits, exp_bits, frac_bits, bias)) = fp_format_params(ft) else {
        panic!("unsupported wide int-to-float target type: {ft:?}");
    };

    let raw_limbs = operand_limbs32(old, s, b, a, bits);
    let value_limbs = normalize_limbs32(s, b, &raw_limbs, bits);
    let sign = if signed {
        u32_sign_bool(
            s,
            b,
            *value_limbs
                .last()
                .expect("signed wide int-to-fp source limbs must not be empty"),
        )
    } else {
        b.bconst(false, o())
    };
    let magnitude = if signed {
        let neg = negate_limbs32(s, b, &value_limbs, bits);
        select_limbs32(s, b, sign, &neg, &value_limbs)
    } else {
        value_limbs.clone()
    };
    let is_zero = limbs32_are_zero(s, b, &magnitude);
    let precision = frac_bits + 1;

    let bit_length = wide_bit_length(s, b, &magnitude, bits);
    let precision_c = b.iconst(precision as i64, s.part_bits, IntSignedness::Unsigned, o());
    let zero = b
        .iconst(0i64, s.part_bits, IntSignedness::Unsigned, o())
        .raw();
    let one = b
        .iconst(1i64, s.part_bits, IntSignedness::Unsigned, o())
        .raw();

    let needs_rounding = b.icmp(
        ICmpOp::Gt,
        Operand::annotated(bit_length, Annotation::Int(part_ann(s))).into(),
        precision_c.into(),
        o(),
    );
    let shift_raw = b.sub(
        Operand::annotated(bit_length, Annotation::Int(part_ann(s))).into(),
        precision_c.into(),
        part_ann(s),
        o(),
    );
    let shift = b.select(
        needs_rounding.into(),
        Operand::annotated(shift_raw.raw(), Annotation::Int(part_ann(s))),
        Operand::annotated(zero, Annotation::Int(part_ann(s))),
        Type::Int,
        Some(Annotation::Int(part_ann(s))),
        o(),
    );

    let q_limbs_raw = wide_shr_limbs(s, b, &magnitude, shift, bits, false);
    let q_limbs = normalize_limbs32(s, b, &q_limbs_raw, bits);
    let q_parts = limbs32_to_parts64(s, b, &q_limbs);
    let q = q_parts[0];

    let q_shifted_raw = wide_shl_limbs(s, b, &q_limbs, shift, bits);
    let q_shifted = normalize_limbs32(s, b, &q_shifted_raw, bits);
    let (remainder_raw, _) = sub_limbs32(s, b, &magnitude, &q_shifted);
    let remainder = normalize_limbs32(s, b, &remainder_raw, bits);

    let half_shift_raw = b.sub(
        Operand::annotated(shift, Annotation::Int(part_ann(s))).into(),
        Operand::annotated(one, Annotation::Int(part_ann(s))).into(),
        part_ann(s),
        o(),
    );
    let half_shift = b.select(
        needs_rounding.into(),
        Operand::annotated(half_shift_raw.raw(), Annotation::Int(part_ann(s))),
        Operand::annotated(zero, Annotation::Int(part_ann(s))),
        Type::Int,
        Some(Annotation::Int(part_ann(s))),
        o(),
    );

    let round_slice_raw = wide_shr_limbs(s, b, &remainder, half_shift, bits, false);
    let round_slice = normalize_limbs32(s, b, &round_slice_raw, bits);
    let round_slice_is_zero = limbs32_are_zero(s, b, &round_slice);
    let round_bit = bool_not(b, round_slice_is_zero);
    let round_bit_int = bool_to_part(s, b, round_bit);
    let round_limb = wide_uint_from_small_value(s, b, round_bit_int, s.part_bits, bits);
    let round_contrib_raw = wide_shl_limbs(s, b, &round_limb, half_shift, bits);
    let round_contrib = normalize_limbs32(s, b, &round_contrib_raw, bits);
    let (sticky_raw, _) = sub_limbs32(s, b, &remainder, &round_contrib);
    let sticky_limbs = normalize_limbs32(s, b, &sticky_raw, bits);
    let sticky_is_zero = limbs32_are_zero(s, b, &sticky_limbs);
    let sticky = bool_not(b, sticky_is_zero);

    let one_mask = b
        .iconst(1i64, s.part_bits, IntSignedness::Unsigned, o())
        .raw();
    let q_lsb = b.and(
        Operand::annotated(q, Annotation::Int(part_ann(s))).into(),
        Operand::annotated(one_mask, Annotation::Int(part_ann(s))).into(),
        part_ann(s),
        o(),
    );
    let q_lsb_odd = b.icmp(
        ICmpOp::Ne,
        Operand::annotated(q_lsb.raw(), Annotation::Int(part_ann(s))).into(),
        Operand::annotated(zero, Annotation::Int(part_ann(s))).into(),
        o(),
    );
    let sticky_or_odd = b.bor(sticky.into(), q_lsb_odd.into(), o());
    let round_up = b.band(round_bit.into(), sticky_or_odd.into(), o());
    let round_up_int = bool_to_part(s, b, round_up);
    let q_rounded = b
        .add(
            Operand::annotated(q, Annotation::Int(part_ann(s))).into(),
            Operand::annotated(round_up_int, Annotation::Int(part_ann(s))).into(),
            part_ann(s),
            o(),
        )
        .raw();

    let carry_value = b.iconst(
        BigInt::from(1u8) << precision,
        s.part_bits,
        IntSignedness::Unsigned,
        o(),
    );
    let q_overflow = b.icmp(
        ICmpOp::Eq,
        Operand::annotated(q_rounded, Annotation::Int(part_ann(s))).into(),
        carry_value.into(),
        o(),
    );

    let exponent_bias = b.iconst(bias as i64, s.part_bits, IntSignedness::Unsigned, o());
    let exp_minus_one = b.sub(
        Operand::annotated(bit_length, Annotation::Int(part_ann(s))).into(),
        Operand::annotated(one, Annotation::Int(part_ann(s))).into(),
        part_ann(s),
        o(),
    );
    let q_overflow_int = bool_to_part(s, b, q_overflow);
    let exponent_field = b
        .add(exp_minus_one.into(), exponent_bias.into(), part_ann(s), o())
        .raw();
    let exponent_field = b
        .add(
            Operand::annotated(exponent_field, Annotation::Int(part_ann(s))).into(),
            Operand::annotated(q_overflow_int, Annotation::Int(part_ann(s))).into(),
            part_ann(s),
            o(),
        )
        .raw();

    let inf_field = b.iconst(
        (BigInt::from(1u8) << exp_bits) - BigInt::from(1u8),
        s.part_bits,
        IntSignedness::Unsigned,
        o(),
    );
    let exponent_overflow = b.icmp(
        ICmpOp::Ge,
        Operand::annotated(exponent_field, Annotation::Int(part_ann(s))).into(),
        inf_field.into(),
        o(),
    );

    let frac_mask = b.iconst(
        (BigInt::from(1u8) << frac_bits) - BigInt::from(1u8),
        s.part_bits,
        IntSignedness::Unsigned,
        o(),
    );
    let fraction = b.and(
        Operand::annotated(q_rounded, Annotation::Int(part_ann(s))).into(),
        frac_mask.into(),
        part_ann(s),
        o(),
    );
    let fraction = b.select(
        q_overflow.into(),
        Operand::annotated(zero, Annotation::Int(part_ann(s))),
        Operand::annotated(fraction.raw(), Annotation::Int(part_ann(s))),
        Type::Int,
        Some(Annotation::Int(part_ann(s))),
        o(),
    );

    let frac_shift = b.iconst(frac_bits as i64, s.part_bits, IntSignedness::Unsigned, o());
    let exponent_bits = b
        .shl(
            Operand::annotated(exponent_field, Annotation::Int(part_ann(s))).into(),
            frac_shift.into(),
            part_ann(s),
            o(),
        )
        .raw();
    let finite_bits = b
        .or(
            Operand::annotated(exponent_bits, Annotation::Int(part_ann(s))).into(),
            Operand::annotated(fraction, Annotation::Int(part_ann(s))).into(),
            part_ann(s),
            o(),
        )
        .raw();
    let inf_bits = b
        .shl(inf_field.into(), frac_shift.into(), part_ann(s), o())
        .raw();

    let sign_bit = b.iconst(
        BigInt::from(1u8) << (src_float_bits - 1),
        s.part_bits,
        IntSignedness::Unsigned,
        o(),
    );
    let sign_bits = if signed {
        b.select(
            sign.into(),
            Operand::annotated(sign_bit.raw(), Annotation::Int(part_ann(s))),
            Operand::annotated(zero, Annotation::Int(part_ann(s))),
            Type::Int,
            Some(Annotation::Int(part_ann(s))),
            o(),
        )
    } else {
        zero
    };
    let finite_signed = b
        .or(
            Operand::annotated(finite_bits, Annotation::Int(part_ann(s))).into(),
            Operand::annotated(sign_bits, Annotation::Int(part_ann(s))).into(),
            part_ann(s),
            o(),
        )
        .raw();
    let inf_signed = b
        .or(
            Operand::annotated(inf_bits, Annotation::Int(part_ann(s))).into(),
            Operand::annotated(sign_bits, Annotation::Int(part_ann(s))).into(),
            part_ann(s),
            o(),
        )
        .raw();
    let nonzero_bits = b.select(
        exponent_overflow.into(),
        Operand::annotated(inf_signed, Annotation::Int(part_ann(s))),
        Operand::annotated(finite_signed, Annotation::Int(part_ann(s))),
        Type::Int,
        Some(Annotation::Int(part_ann(s))),
        o(),
    );
    let raw_bits = b.select(
        is_zero.into(),
        Operand::annotated(zero, Annotation::Int(part_ann(s))),
        Operand::annotated(nonzero_bits, Annotation::Int(part_ann(s))),
        Type::Int,
        Some(Annotation::Int(part_ann(s))),
        o(),
    );

    let raw_ann = IntAnnotation {
        bit_width: src_float_bits,
        signedness: IntSignedness::Unsigned,
    };
    let out = b.bitcast(
        Operand::annotated(raw_bits, Annotation::Int(raw_ann)),
        Type::Float(ft),
        None,
        o(),
    );
    s.vmap.set(old_vref, Mapped::One(out));
}

// ---------------------------------------------------------------------------
// Double-width integer to float: lower to compiler-rt libcall
//   The exact symbol suffix is chosen from the legalized double-width bits
//   (`si` / `di` / `ti`), e.g. `__floatdisf` or `__floatuntidf`.
// ---------------------------------------------------------------------------

fn leg_int_to_fp_double_width(
    s: &mut State,
    b: &mut Builder,
    old_vref: ValueRef,
    a: &Operand,
    ft: tuffy_ir::types::FloatType,
    signed: bool,
    symbols: &mut SymbolTable,
) {
    let name = int_to_fp_double_width_libcall_name(s.part_bits * 2, signed, ft);
    let sym_id = symbols.intern(&name);
    let callee = b.symbol_addr(sym_id, o()).raw();

    let (a_lo, a_hi) = if is_wide(s, a.value) {
        let parts = s.vmap.parts(a.value);
        (parts[0], parts[1])
    } else {
        // Small double-width value mapped to a single legal part.
        // Compute the upper part: sign-extend for signed, zero for unsigned.
        let lo = s.vmap.one(a.value);
        let hi = if signed {
            let shift = b.iconst(
                (s.part_bits - 1) as i64,
                s.part_bits,
                IntSignedness::Unsigned,
                o(),
            );
            let signed_part = IntAnnotation {
                bit_width: s.part_bits,
                signedness: IntSignedness::Signed,
            };
            b.shr(
                Operand::annotated(lo, Annotation::Int(signed_part)).into(),
                shift.into(),
                signed_part,
                o(),
            )
        } else {
            b.iconst(0i64, s.part_bits, IntSignedness::Unsigned, o())
        };
        (lo, hi.raw())
    };
    let args = vec![Operand::new(a_lo), Operand::new(a_hi)];

    let old_mem = s
        .current_old_mem
        .expect("wide int-to-float requires a mem token in scope");
    let new_mem = s.vmap.one(old_mem);
    let (call_mem, data) = b.call(
        Operand::new(callee).into(),
        args,
        Type::Float(ft),
        Operand::new(new_mem).into(),
        None,
        None,
        o(),
    );
    let data = data.unwrap();

    s.vmap.set(old_mem, Mapped::One(call_mem.into()));
    s.vmap.set(old_vref, Mapped::One(data));
}

// ---------------------------------------------------------------------------
// Exact double-width return: low part → RAX, second part → RDX (via metadata)
// ---------------------------------------------------------------------------

fn leg_ret(
    s: &mut State,
    b: &mut Builder,
    old_vref: ValueRef,
    val: &Option<Operand>,
    ret2: &Option<Operand>,
    mem: &Operand,
) {
    let m = s.vmap.one(mem.value);
    if let Some(rv) = val {
        let (lo, hi) = if let Some(ret2) = ret2 {
            (s.vmap.one(rv.value), s.vmap.one(ret2.value))
        } else if is_wide(s, rv.value) {
            let parts = s.vmap.parts(rv.value);
            let lo = parts[0];
            let hi = parts.get(1).copied().unwrap_or_else(|| {
                b.iconst(0i64, s.part_bits, IntSignedness::Unsigned, o())
                    .raw()
            });
            (lo, hi)
        } else {
            let lo = s.vmap.one(rv.value);
            let hi = b
                .iconst(0i64, s.part_bits, IntSignedness::Unsigned, o())
                .raw();
            (lo, hi)
        };
        let ret_inst = b.ret(
            Some(Operand::new(lo)),
            Some(Operand::new(hi)),
            Operand::new(m).into(),
            o(),
        );
        s.vmap.set(old_vref, Mapped::One(ret_inst));
    } else {
        let v = b.ret(None, None, Operand::new(m).into(), o());
        s.vmap.set(old_vref, Mapped::One(v));
    }
}

// ---------------------------------------------------------------------------
// Call: split wide integer args, handle double-width returns
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

    // Split wide integer arguments into legalized parts.
    let mut new_args = Vec::new();
    for arg in args {
        if is_wide(s, arg.value) {
            for part in s.vmap.parts(arg.value) {
                new_args.push(Operand::new(part));
            }
        } else if is_wide_int_value_with_limit(_old, arg.value, s.part_bits) {
            for part in operand_parts64(_old, s, b, arg, result_bits(s, _old, arg.value)) {
                new_args.push(Operand::new(part));
            }
        } else {
            new_args.push(remap_op(s, arg));
        }
    }

    let double_width_ret = is_exact_double_width_int_annotation(
        inst.secondary_result_annotation.as_ref(),
        s.part_bits,
    ) || matches!(
        inst.secondary_ty.as_ref(),
        Some(Type::Float(FloatType::F128))
    );
    let ret_ty = if double_width_ret {
        I64_TYPE
    } else {
        inst.secondary_ty.clone().unwrap_or(Type::Unit)
    };

    let ann = if double_width_ret {
        None
    } else {
        inst.result_annotation.clone()
    };

    let cleanup_label = match &inst.op {
        Op::Call(_, _, _, cleanup) => *cleanup,
        _ => None,
    };
    let (mem_out, data_out) = b.call(
        c.into(),
        new_args,
        ret_ty,
        m.into(),
        cleanup_label,
        ann,
        o(),
    );
    s.vmap.set(old_vref, Mapped::One(mem_out.into()));

    if double_width_ret {
        if let Some(data) = data_out {
            let hi_capture = b.call_ret2(
                Operand::new(mem_out.into()).into(),
                Type::Int,
                Some(Annotation::Int(I64)),
                o(),
            );

            s.vmap.set(
                ValueRef::inst_secondary_result(old_vref.index()),
                Mapped::Pair(data, hi_capture),
            );
        }
    } else if let Some(data) = data_out {
        let old_sec = ValueRef::inst_secondary_result(old_vref.index());
        s.vmap.set(old_sec, Mapped::One(data));
    }
}

// ---------------------------------------------------------------------------
// Branch argument remapping: split wide integer args into legalized parts
// ---------------------------------------------------------------------------

fn remap_branch_args(s: &State, args: &[Operand]) -> Vec<Operand> {
    let mut out = Vec::new();
    for arg in args {
        if is_wide(s, arg.value) {
            for part in s.vmap.parts(arg.value) {
                out.push(Operand::new(part));
            }
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

#[cfg(test)]
mod tests {
    use super::*;
    use tuffy_ir::function::RegionKind;
    use tuffy_ir::module::Module;
    use tuffy_ir_interp::{ExecMode, InterpResult, Interpreter, Value};
    use tuffy_target_x86::legality::X86LegalityInfo;

    fn build_carrying_mul_add_func(bits: u32, signed: bool) -> (Function, SymbolTable) {
        let mut symbols = SymbolTable::new();
        let name = symbols.intern("wide_mul_add");
        let sign = if signed {
            IntSignedness::Signed
        } else {
            IntSignedness::Unsigned
        };
        let ann = Annotation::Int(IntAnnotation {
            bit_width: bits,
            signedness: sign,
        });
        let mut func = Function::new(name, vec![], vec![], vec![], None, None);
        let mut b = Builder::new(&mut func);
        let root = b.create_region(RegionKind::Function);
        b.enter_region(root);
        let bb = b.create_block();
        b.switch_to_block(bb);
        let mem0 = b.add_block_arg(bb, Type::Mem, None);

        let lhs = b.iconst(BigInt::from(1u8) << (bits / 2), bits, sign, o());
        let rhs = b.iconst(BigInt::from(1u8) << (bits / 2), bits, sign, o());
        let carry = b.iconst(5i64, bits, sign, o());
        let add = b.iconst(7i64, bits, sign, o());
        if signed {
            let _ = b.s_carrying_mul_add(
                Operand::annotated(lhs.raw(), ann.clone()).into(),
                Operand::annotated(rhs.raw(), ann.clone()).into(),
                Operand::annotated(carry.raw(), ann.clone()).into(),
                Operand::annotated(add.raw(), ann.clone()).into(),
                bits,
                o(),
            );
        } else {
            let _ = b.u_carrying_mul_add(
                Operand::annotated(lhs.raw(), ann.clone()).into(),
                Operand::annotated(rhs.raw(), ann.clone()).into(),
                Operand::annotated(carry.raw(), ann.clone()).into(),
                Operand::annotated(add.raw(), ann.clone()).into(),
                bits,
                o(),
            );
        }
        b.ret(None, None, mem0.into(), o());
        b.exit_region();
        (func, symbols)
    }

    #[allow(clippy::too_many_arguments)]
    fn build_carrying_mul_add_check_func(
        bits: u32,
        signed: bool,
        a: BigInt,
        op_b: BigInt,
        carry: BigInt,
        add: BigInt,
        expected_lo: BigInt,
        expected_hi: BigInt,
    ) -> (Function, SymbolTable) {
        let mut symbols = SymbolTable::new();
        let name = symbols.intern("carrying_mul_add_check");
        let sign = if signed {
            IntSignedness::Signed
        } else {
            IntSignedness::Unsigned
        };
        let ann = Annotation::Int(IntAnnotation {
            bit_width: bits,
            signedness: sign,
        });
        let unsigned_ann = Annotation::Int(IntAnnotation {
            bit_width: bits,
            signedness: IntSignedness::Unsigned,
        });
        let mut func = Function::new(name, vec![], vec![], vec![], Some(Type::Bool), None);
        let mut b = Builder::new(&mut func);
        let root = b.create_region(RegionKind::Function);
        b.enter_region(root);
        let bb = b.create_block();
        b.switch_to_block(bb);
        let mem0 = b.add_block_arg(bb, Type::Mem, None);
        let a = b.iconst(a, bits, sign, o());
        let op_b = b.iconst(op_b, bits, sign, o());
        let carry = b.iconst(carry, bits, sign, o());
        let add = b.iconst(add, bits, sign, o());
        let (lo, hi) = if signed {
            b.s_carrying_mul_add(
                Operand::annotated(a.raw(), ann.clone()).into(),
                Operand::annotated(op_b.raw(), ann.clone()).into(),
                Operand::annotated(carry.raw(), ann.clone()).into(),
                Operand::annotated(add.raw(), ann.clone()).into(),
                bits,
                o(),
            )
        } else {
            b.u_carrying_mul_add(
                Operand::annotated(a.raw(), ann.clone()).into(),
                Operand::annotated(op_b.raw(), ann.clone()).into(),
                Operand::annotated(carry.raw(), ann.clone()).into(),
                Operand::annotated(add.raw(), ann.clone()).into(),
                bits,
                o(),
            )
        };
        let expected_lo = b.iconst(expected_lo, bits, IntSignedness::Unsigned, o());
        let expected_hi = b.iconst(expected_hi, bits, IntSignedness::Unsigned, o());
        let lo_ok = b.icmp(
            ICmpOp::Eq,
            Operand::annotated(lo.raw(), unsigned_ann.clone()).into(),
            Operand::annotated(expected_lo.raw(), unsigned_ann.clone()).into(),
            o(),
        );
        let hi_ok = b.icmp(
            ICmpOp::Eq,
            Operand::annotated(hi.raw(), unsigned_ann.clone()).into(),
            Operand::annotated(expected_hi.raw(), unsigned_ann.clone()).into(),
            o(),
        );
        let ok = b.band(lo_ok.into(), hi_ok.into(), o());
        b.ret(Some(ok.into()), None, mem0.into(), o());
        b.exit_region();
        (func, symbols)
    }

    fn build_add_func(bits: u32) -> (Function, SymbolTable) {
        let mut symbols = SymbolTable::new();
        let name = symbols.intern("wide_add");
        let ann = IntAnnotation {
            bit_width: bits,
            signedness: IntSignedness::Unsigned,
        };
        let mut func = Function::new(name, vec![], vec![], vec![], None, None);
        let mut b = Builder::new(&mut func);
        let root = b.create_region(RegionKind::Function);
        b.enter_region(root);
        let bb = b.create_block();
        b.switch_to_block(bb);
        let mem0 = b.add_block_arg(bb, Type::Mem, None);
        let lhs = b.iconst(
            BigInt::from(1u8) << (bits - 1),
            bits,
            IntSignedness::Unsigned,
            o(),
        );
        let rhs = b.iconst(9i64, bits, IntSignedness::Unsigned, o());
        let _ = b.add(
            Operand::annotated(lhs.raw(), Annotation::Int(ann)).into(),
            Operand::annotated(rhs.raw(), Annotation::Int(ann)).into(),
            IntAnnotation {
                bit_width: bits,
                signedness: IntSignedness::Unsigned,
            },
            o(),
        );
        b.ret(None, None, mem0.into(), o());
        b.exit_region();
        (func, symbols)
    }

    fn build_overflow_func(bits: u32, signed: bool, is_mul: bool) -> (Function, SymbolTable) {
        let mut symbols = SymbolTable::new();
        let name = symbols.intern("wide_overflow");
        let sign = if signed {
            IntSignedness::Signed
        } else {
            IntSignedness::Unsigned
        };
        let ann = Annotation::Int(IntAnnotation {
            bit_width: bits,
            signedness: sign,
        });
        let mut func = Function::new(name, vec![], vec![], vec![], None, None);
        let mut b = Builder::new(&mut func);
        let root = b.create_region(RegionKind::Function);
        b.enter_region(root);
        let bb = b.create_block();
        b.switch_to_block(bb);
        let mem0 = b.add_block_arg(bb, Type::Mem, None);
        let lhs = b.iconst(BigInt::from(1u8) << (bits - 1), bits, sign, o());
        let rhs = b.iconst(2i64, bits, sign, o());
        let _ = match (signed, is_mul) {
            (true, true) => b.smul_with_overflow(
                Operand::annotated(lhs.raw(), ann.clone()).into(),
                Operand::annotated(rhs.raw(), ann.clone()).into(),
                bits,
                o(),
            ),
            (false, true) => b.umul_with_overflow(
                Operand::annotated(lhs.raw(), ann.clone()).into(),
                Operand::annotated(rhs.raw(), ann.clone()).into(),
                bits,
                o(),
            ),
            (true, false) => b.sadd_with_overflow(
                Operand::annotated(lhs.raw(), ann.clone()).into(),
                Operand::annotated(rhs.raw(), ann.clone()).into(),
                bits,
                o(),
            ),
            (false, false) => b.uadd_with_overflow(
                Operand::annotated(lhs.raw(), ann.clone()).into(),
                Operand::annotated(rhs.raw(), ann.clone()).into(),
                bits,
                o(),
            ),
        };
        b.ret(None, None, mem0.into(), o());
        b.exit_region();
        (func, symbols)
    }

    fn build_shift_func(bits: u32, rotate: bool) -> (Function, SymbolTable) {
        let mut symbols = SymbolTable::new();
        let name = symbols.intern("wide_shift");
        let ann = IntAnnotation {
            bit_width: bits,
            signedness: IntSignedness::Unsigned,
        };
        let mut func = Function::new(name, vec![], vec![], vec![], None, None);
        let mut b = Builder::new(&mut func);
        let root = b.create_region(RegionKind::Function);
        b.enter_region(root);
        let bb = b.create_block();
        b.switch_to_block(bb);
        let mem0 = b.add_block_arg(bb, Type::Mem, None);
        let lhs = b.iconst(
            BigInt::parse_bytes(b"123456789abcdef0123456789abcdef0", 16).unwrap(),
            bits,
            IntSignedness::Unsigned,
            o(),
        );
        let amt = b.iconst(17i64, 64, IntSignedness::Unsigned, o());
        let _ = if rotate {
            b.rotate_left(
                Operand::annotated(lhs.raw(), Annotation::Int(ann)).into(),
                amt.into(),
                bits,
                o(),
            )
        } else {
            b.shl(
                Operand::annotated(lhs.raw(), Annotation::Int(ann)).into(),
                amt.into(),
                ann,
                o(),
            )
        };
        b.ret(None, None, mem0.into(), o());
        b.exit_region();
        (func, symbols)
    }

    fn build_divrem_func(bits: u32, is_div: bool, signed: bool) -> (Function, SymbolTable) {
        let mut symbols = SymbolTable::new();
        let name = symbols.intern("wide_divrem");
        let ann = IntAnnotation {
            bit_width: bits,
            signedness: if signed {
                IntSignedness::Signed
            } else {
                IntSignedness::Unsigned
            },
        };
        let mut func = Function::new(name, vec![], vec![], vec![], None, None);
        let mut b = Builder::new(&mut func);
        let root = b.create_region(RegionKind::Function);
        b.enter_region(root);
        let bb = b.create_block();
        b.switch_to_block(bb);
        let mem0 = b.add_block_arg(bb, Type::Mem, None);
        let lhs = b.iconst(
            BigInt::parse_bytes(b"123456789abcdef0123456789abcdef0", 16).unwrap(),
            bits,
            ann.signedness,
            o(),
        );
        let rhs = b.iconst(17i64, bits, ann.signedness, o());
        let _ = if is_div {
            b.div(
                Operand::annotated(lhs.raw(), Annotation::Int(ann)).into(),
                Operand::annotated(rhs.raw(), Annotation::Int(ann)).into(),
                ann,
                o(),
            )
        } else {
            b.rem(
                Operand::annotated(lhs.raw(), Annotation::Int(ann)).into(),
                Operand::annotated(rhs.raw(), Annotation::Int(ann)).into(),
                ann,
                o(),
            )
        };
        b.ret(None, None, mem0.into(), o());
        b.exit_region();
        (func, symbols)
    }

    fn build_int_to_fp_func(bits: u32, signed: bool) -> (Function, SymbolTable) {
        let mut symbols = SymbolTable::new();
        let name = symbols.intern("wide_int_to_fp");
        let ann = IntAnnotation {
            bit_width: bits,
            signedness: if signed {
                IntSignedness::Signed
            } else {
                IntSignedness::Unsigned
            },
        };
        let mut func = Function::new(name, vec![], vec![], vec![], None, None);
        let mut b = Builder::new(&mut func);
        let root = b.create_region(RegionKind::Function);
        b.enter_region(root);
        let bb = b.create_block();
        b.switch_to_block(bb);
        let mem0 = b.add_block_arg(bb, Type::Mem, None);
        let lhs = b.iconst(
            BigInt::parse_bytes(b"123456789abcdef0123456789abcdef0", 16).unwrap(),
            bits,
            ann.signedness,
            o(),
        );
        let _ = if signed {
            b.si_to_fp(
                Operand::annotated(lhs.raw(), Annotation::Int(ann)).into(),
                FloatType::F64,
                o(),
            )
        } else {
            b.ui_to_fp(
                Operand::annotated(lhs.raw(), Annotation::Int(ann)).into(),
                FloatType::F64,
                o(),
            )
        };
        b.ret(None, None, mem0.into(), o());
        b.exit_region();
        (func, symbols)
    }

    fn build_int_to_fp_check_func(
        bits: u32,
        signed: bool,
        value: BigInt,
        expected_bits: u128,
    ) -> (Function, SymbolTable) {
        let mut symbols = SymbolTable::new();
        let name = symbols.intern("wide_int_to_fp_check");
        let ann = IntAnnotation {
            bit_width: bits,
            signedness: if signed {
                IntSignedness::Signed
            } else {
                IntSignedness::Unsigned
            },
        };
        let mut func = Function::new(name, vec![], vec![], vec![], Some(Type::Bool), None);
        let mut b = Builder::new(&mut func);
        let root = b.create_region(RegionKind::Function);
        b.enter_region(root);
        let bb = b.create_block();
        b.switch_to_block(bb);
        let mem0 = b.add_block_arg(bb, Type::Mem, None);
        let lhs = b.iconst(value, bits, ann.signedness, o());
        let actual = if signed {
            b.si_to_fp(
                Operand::annotated(lhs.raw(), Annotation::Int(ann)).into(),
                FloatType::F64,
                o(),
            )
        } else {
            b.ui_to_fp(
                Operand::annotated(lhs.raw(), Annotation::Int(ann)).into(),
                FloatType::F64,
                o(),
            )
        };
        let expected = b.fconst(FloatType::F64, expected_bits, o());
        let ok = b.fcmp(FCmpOp::OEq, actual.into(), expected.into(), o());
        b.ret(Some(ok.into()), None, mem0.into(), o());
        b.exit_region();
        (func, symbols)
    }

    fn build_fp_to_int_func(bits: u32, signed: bool, float_bits: u128) -> (Function, SymbolTable) {
        let mut symbols = SymbolTable::new();
        let name = symbols.intern("wide_fp_to_int");
        let sign = if signed {
            IntSignedness::Signed
        } else {
            IntSignedness::Unsigned
        };
        let ann = Annotation::Int(IntAnnotation {
            bit_width: bits,
            signedness: sign,
        });
        let mut func = Function::new(name, vec![], vec![], vec![], None, None);
        let mut b = Builder::new(&mut func);
        let root = b.create_region(RegionKind::Function);
        b.enter_region(root);
        let bb = b.create_block();
        b.switch_to_block(bb);
        let mem0 = b.add_block_arg(bb, Type::Mem, None);
        let f = b.fconst(FloatType::F64, float_bits, o());
        if signed {
            let raw = b.fp_to_si(f.into(), 64, o());
            let _ = b.sext(raw.into(), bits, o());
        } else {
            let raw = b.fp_to_ui(f.into(), 64, o());
            let _ = b.zext(raw.into(), bits, o());
        }
        b.ret(None, None, mem0.into(), o());
        b.exit_region();
        let _ = ann;
        (func, symbols)
    }

    fn build_fp_to_int_check_func(
        bits: u32,
        signed: bool,
        float_bits: u128,
        expected: BigInt,
    ) -> (Function, SymbolTable) {
        let mut symbols = SymbolTable::new();
        let name = symbols.intern("wide_fp_to_int_check");
        let sign = if signed {
            IntSignedness::Signed
        } else {
            IntSignedness::Unsigned
        };
        let ann = IntAnnotation {
            bit_width: bits,
            signedness: sign,
        };
        let unsigned_ann = IntAnnotation {
            bit_width: bits,
            signedness: IntSignedness::Unsigned,
        };
        let mut func = Function::new(name, vec![], vec![], vec![], Some(Type::Bool), None);
        let mut b = Builder::new(&mut func);
        let root = b.create_region(RegionKind::Function);
        b.enter_region(root);
        let bb = b.create_block();
        b.switch_to_block(bb);
        let mem0 = b.add_block_arg(bb, Type::Mem, None);
        let f = b.fconst(FloatType::F64, float_bits, o());
        let actual = if signed {
            let raw = b.fp_to_si(f.into(), 64, o());
            b.sext(raw.into(), bits, o())
        } else {
            let raw = b.fp_to_ui(f.into(), 64, o());
            b.zext(raw.into(), bits, o())
        };
        let modulus = BigInt::from(1u8) << bits;
        let mut expected_bits = expected % &modulus;
        if expected_bits.sign() == num_bigint::Sign::Minus {
            expected_bits += &modulus;
        }
        let expected = b.iconst(expected_bits, bits, IntSignedness::Unsigned, o());
        let diff = b.xor(
            Operand::annotated(actual.raw(), Annotation::Int(unsigned_ann)).into(),
            Operand::annotated(expected.raw(), Annotation::Int(unsigned_ann)).into(),
            unsigned_ann,
            o(),
        );
        let zero = b.iconst(0i64, bits, IntSignedness::Unsigned, o());
        let ok = b.icmp(
            ICmpOp::Eq,
            Operand::annotated(diff.raw(), Annotation::Int(unsigned_ann)).into(),
            Operand::annotated(zero.raw(), Annotation::Int(unsigned_ann)).into(),
            o(),
        );
        b.ret(Some(ok.into()), None, mem0.into(), o());
        b.exit_region();
        let _ = ann;
        (func, symbols)
    }

    fn build_icmp_func(bits: u32, signed: bool) -> (Function, SymbolTable) {
        let mut symbols = SymbolTable::new();
        let name = symbols.intern("wide_icmp");
        let ann = IntAnnotation {
            bit_width: bits,
            signedness: if signed {
                IntSignedness::Signed
            } else {
                IntSignedness::Unsigned
            },
        };
        let mut func = Function::new(name, vec![], vec![], vec![], None, None);
        let mut b = Builder::new(&mut func);
        let root = b.create_region(RegionKind::Function);
        b.enter_region(root);
        let bb = b.create_block();
        b.switch_to_block(bb);
        let mem0 = b.add_block_arg(bb, Type::Mem, None);
        let lhs = b.iconst(
            BigInt::parse_bytes(b"123456789abcdef0123456789abcdef0", 16).unwrap(),
            bits,
            ann.signedness,
            o(),
        );
        let rhs = b.iconst(
            BigInt::parse_bytes(b"123456789abcdef0123456789abcde00", 16).unwrap(),
            bits,
            ann.signedness,
            o(),
        );
        let _ = b.icmp(
            ICmpOp::Gt,
            Operand::annotated(lhs.raw(), Annotation::Int(ann)).into(),
            Operand::annotated(rhs.raw(), Annotation::Int(ann)).into(),
            o(),
        );
        b.ret(None, None, mem0.into(), o());
        b.exit_region();
        (func, symbols)
    }

    fn build_clz_check_func(bits: u32, value: BigInt, expected: u64) -> (Function, SymbolTable) {
        let mut symbols = SymbolTable::new();
        let name = symbols.intern("wide_clz_check");
        let ann = Annotation::Int(IntAnnotation {
            bit_width: bits,
            signedness: IntSignedness::Unsigned,
        });
        let mut func = Function::new(name, vec![], vec![], vec![], Some(Type::Bool), None);
        let mut b = Builder::new(&mut func);
        let root = b.create_region(RegionKind::Function);
        b.enter_region(root);
        let bb = b.create_block();
        b.switch_to_block(bb);
        let mem0 = b.add_block_arg(bb, Type::Mem, None);
        let val = b.iconst(value, bits, IntSignedness::Unsigned, o());
        let clz = b.count_leading_zeros(
            Operand::annotated(val.raw(), ann.clone()).into(),
            bits,
            64,
            o(),
        );
        let expected = b.iconst(expected as i64, 64, IntSignedness::Unsigned, o());
        let ok = b.icmp(ICmpOp::Eq, clz.into(), expected.into(), o());
        b.ret(Some(ok.into()), None, mem0.into(), o());
        b.exit_region();
        (func, symbols)
    }

    fn assert_legalized_widths(bits: u32, signed: bool) {
        let (func, mut symbols) = build_carrying_mul_add_func(bits, signed);
        let legalized =
            legalize(&func, &X86LegalityInfo, &mut symbols).expect("expected legalization");
        let out = legalized;
        for (_, inst) in out.inst_pool.iter_insts() {
            assert!(
                !matches!(inst.op, Op::SCarryingMulAdd(..) | Op::UCarryingMulAdd(..)),
                "carrying_mul_add op should be fully lowered"
            );
            if let Some(Annotation::Int(ann)) = &inst.result_annotation.clone() {
                assert!(ann.bit_width <= 64, "primary width must be legalized");
            }
            if let Some(Annotation::Int(ann)) = &inst.secondary_result_annotation {
                assert!(ann.bit_width <= 64, "secondary width must be legalized");
            }
        }
    }

    #[test]
    fn legalize_ucarrying_mul_add_widths() {
        for bits in [128, 160, 192, 256] {
            assert_legalized_widths(bits, false);
        }
    }

    #[test]
    fn legalize_scarrying_mul_add_widths() {
        for bits in [128, 160, 192, 256] {
            assert_legalized_widths(bits, true);
        }
    }

    #[test]
    fn legalize_wide_add_160() {
        let (func, mut symbols) = build_add_func(160);
        let legalized =
            legalize(&func, &X86LegalityInfo, &mut symbols).expect("expected legalization");
        for (_, inst) in legalized.inst_pool.iter_insts() {
            if let Some(Annotation::Int(ann)) = &inst.result_annotation.clone() {
                assert!(ann.bit_width <= 64);
            }
        }
    }

    #[test]
    fn legalize_wide_overflow_widths() {
        for (bits, signed, is_mul) in [
            (160, false, false),
            (160, true, false),
            (192, false, true),
            (256, true, true),
        ] {
            let (func, mut symbols) = build_overflow_func(bits, signed, is_mul);
            let legalized = legalize(&func, &X86LegalityInfo, &mut symbols)
                .expect("expected overflow legalization");
            for (_, inst) in legalized.inst_pool.iter_insts() {
                if let Some(Annotation::Int(ann)) = &inst.result_annotation.clone() {
                    assert!(ann.bit_width <= 64);
                }
            }
        }
    }

    #[test]
    fn legalize_wide_shift_and_rotate_widths() {
        for rotate in [false, true] {
            let (func, mut symbols) = build_shift_func(160, rotate);
            let legalized = legalize(&func, &X86LegalityInfo, &mut symbols)
                .expect("expected shift/rotate legalization");
            for (_, inst) in legalized.inst_pool.iter_insts() {
                if let Some(Annotation::Int(ann)) = &inst.result_annotation.clone() {
                    assert!(ann.bit_width <= 64);
                }
            }
        }
    }

    #[test]
    fn legalize_double_width_divrem_paths() {
        for (is_div, signed) in [(true, false), (true, true), (false, false), (false, true)] {
            let (func, mut symbols) = build_divrem_func(128, is_div, signed);
            let legalized = legalize(&func, &X86LegalityInfo, &mut symbols)
                .expect("expected div/rem legalization");
            for (_, inst) in legalized.inst_pool.iter_insts() {
                if let Some(Annotation::Int(ann)) = &inst.result_annotation.clone() {
                    assert!(ann.bit_width <= 64);
                }
            }
        }
    }

    #[test]
    fn legalize_wide_divrem_paths() {
        for (bits, is_div, signed) in [
            (160, true, false),
            (160, false, false),
            (192, true, true),
            (256, false, true),
        ] {
            let (func, mut symbols) = build_divrem_func(bits, is_div, signed);
            let legalized = legalize(&func, &X86LegalityInfo, &mut symbols)
                .expect("expected wide div/rem legalization");
            for (_, inst) in legalized.inst_pool.iter_insts() {
                if let Some(Annotation::Int(ann)) = &inst.result_annotation.clone() {
                    assert!(ann.bit_width <= 64);
                }
            }
        }
    }

    #[test]
    fn legalize_double_width_int_to_fp_paths() {
        for signed in [false, true] {
            let (func, mut symbols) = build_int_to_fp_func(128, signed);
            let legalized = legalize(&func, &X86LegalityInfo, &mut symbols)
                .expect("expected int-to-fp legalization");
            for (_, inst) in legalized.inst_pool.iter_insts() {
                if let Some(Annotation::Int(ann)) = &inst.result_annotation.clone() {
                    assert!(ann.bit_width <= 64);
                }
            }
        }
    }

    #[test]
    fn legalize_wide_int_to_fp_paths() {
        for (bits, signed) in [(160, false), (192, true)] {
            let (func, mut symbols) = build_int_to_fp_func(bits, signed);
            let legalized = legalize(&func, &X86LegalityInfo, &mut symbols)
                .expect("expected wide int-to-fp legalization");
            let saw_helper = legalized.inst_pool.iter_insts().any(|(_, inst)| {
                matches!(inst.op, Op::SymbolAddr(sym) if symbols.resolve(sym).starts_with("__float"))
            });
            assert!(
                !saw_helper,
                "wider-than-double-width int-to-fp should not rely on compiler-rt helpers"
            );
            for (_, inst) in legalized.inst_pool.iter_insts() {
                if let Some(Annotation::Int(ann)) = &inst.result_annotation.clone() {
                    assert!(ann.bit_width <= 64);
                }
            }
        }
    }

    #[test]
    fn legalize_wide_fp_to_int_paths() {
        for signed in [false, true] {
            let bits = 160;
            let f = if signed {
                (-(2f64.powi(120))).to_bits() as u128
            } else {
                (2f64.powi(96)).to_bits() as u128
            };
            let (func, mut symbols) = build_fp_to_int_func(bits, signed, f);
            let legalized = legalize(&func, &X86LegalityInfo, &mut symbols)
                .expect("expected fp-to-int legalization");
            for (_, inst) in legalized.inst_pool.iter_insts() {
                if let Some(Annotation::Int(ann)) = &inst.result_annotation.clone() {
                    assert!(ann.bit_width <= 64);
                }
            }
        }
    }

    #[test]
    fn compiler_rt_double_width_libcall_names_follow_width() {
        assert_eq!(
            div_rem_double_width_libcall_name(64, true, true),
            "__divdi3"
        );
        assert_eq!(
            div_rem_double_width_libcall_name(64, false, false),
            "__umoddi3"
        );
        assert_eq!(
            div_rem_double_width_libcall_name(128, true, false),
            "__udivti3"
        );
        assert_eq!(
            div_rem_double_width_libcall_name(128, false, true),
            "__modti3"
        );

        assert_eq!(
            fp_to_int_double_width_libcall_name(64, false, FloatType::F32),
            "__fixunssfdi"
        );
        assert_eq!(
            fp_to_int_double_width_libcall_name(128, true, FloatType::F64),
            "__fixdfti"
        );

        assert_eq!(
            int_to_fp_double_width_libcall_name(64, true, FloatType::F32),
            "__floatdisf"
        );
        assert_eq!(
            int_to_fp_double_width_libcall_name(128, false, FloatType::F64),
            "__floatuntidf"
        );
    }

    #[test]
    fn legalize_wide_icmp_paths() {
        for signed in [false, true] {
            let (func, mut symbols) = build_icmp_func(160, signed);
            let legalized = legalize(&func, &X86LegalityInfo, &mut symbols)
                .expect("expected icmp legalization");
            for (_, inst) in legalized.inst_pool.iter_insts() {
                if let Some(Annotation::Int(ann)) = &inst.result_annotation.clone() {
                    assert!(ann.bit_width <= 64);
                }
            }
        }
    }

    #[test]
    fn interpret_legalized_smul_overflow_128_regression() {
        let mut symbols = SymbolTable::new();
        let name = symbols.intern("main");
        let ann = Annotation::Int(IntAnnotation {
            bit_width: 128,
            signedness: IntSignedness::Signed,
        });
        let mut func = Function::new(name, vec![], vec![], vec![], Some(Type::Bool), None);
        let mut b = Builder::new(&mut func);
        let root = b.create_region(RegionKind::Function);
        b.enter_region(root);
        let bb = b.create_block();
        b.switch_to_block(bb);
        let mem0 = b.add_block_arg(bb, Type::Mem, None);
        let a = b.iconst(
            BigInt::parse_bytes(b"82651840253265077576806853779406465630", 10).unwrap(),
            128,
            IntSignedness::Signed,
            o(),
        );
        let c = b.iconst(
            BigInt::parse_bytes(b"55120713690567994015539452803646006624", 10).unwrap(),
            128,
            IntSignedness::Signed,
            o(),
        );
        let (prod, ov) = b.smul_with_overflow(
            Operand::annotated(a.raw(), ann.clone()).into(),
            Operand::annotated(c.raw(), ann.clone()).into(),
            128,
            o(),
        );
        let expected = b.iconst(
            BigInt::parse_bytes(b"-122989185482621004698549239146577757888", 10).unwrap(),
            128,
            IntSignedness::Signed,
            o(),
        );
        let prod_ok = b.icmp(
            ICmpOp::Eq,
            Operand::annotated(prod.raw(), ann.clone()).into(),
            Operand::annotated(expected.raw(), ann.clone()).into(),
            o(),
        );
        let result = b.band(prod_ok.into(), ov.into(), o());
        b.ret(Some(result.into()), None, mem0.into(), o());
        b.exit_region();
        let legalized = legalize(&func, &X86LegalityInfo, &mut symbols).expect("legalized");
        let mut module = Module::new("test");
        module.symbols = symbols;
        module.add_function(legalized);
        let mut interp = Interpreter::new(&module, ExecMode::Strict);
        let result = interp.run("main");
        match result {
            InterpResult::Ok(Some(Value::Bool(true))) => {}
            other => panic!("unexpected result: {other}"),
        }
    }

    #[test]
    fn legalize_double_width_int_to_fp_uses_compiler_rt_helpers() {
        for (signed, expected) in [(false, "__floatuntidf"), (true, "__floattidf")] {
            let (func, mut symbols) = build_int_to_fp_func(128, signed);
            let legalized = legalize(&func, &X86LegalityInfo, &mut symbols)
                .expect("expected int-to-fp legalization");
            let saw_helper = legalized.inst_pool.iter_insts().any(|(_, inst)| {
                matches!(inst.op, Op::SymbolAddr(sym) if symbols.resolve(sym) == expected)
            });
            assert!(saw_helper, "expected helper symbol {expected}");
        }
    }

    #[test]
    fn interpret_legalized_double_width_int_to_fp_regressions() {
        for (signed, value, expected_bits) in [
            (
                false,
                BigInt::from(1u8) << 96,
                (2f64.powi(96)).to_bits() as u128,
            ),
            (
                true,
                BigInt::from(-1) * (BigInt::from(1u8) << 120),
                (-(2f64.powi(120))).to_bits() as u128,
            ),
        ] {
            let (func, mut symbols) = build_int_to_fp_check_func(128, signed, value, expected_bits);
            let legalized = legalize(&func, &X86LegalityInfo, &mut symbols).expect("legalized");
            let mut module = Module::new("test");
            module.symbols = symbols;
            module.add_function(legalized);
            let mut interp = Interpreter::new(&module, ExecMode::Strict);
            let result = interp.run("wide_int_to_fp_check");
            match result {
                InterpResult::Ok(Some(Value::Bool(true))) => {}
                other => panic!("unexpected result: {other}"),
            }
        }
    }

    #[test]
    fn interpret_legalized_wide_int_to_fp_regressions() {
        for (bits, signed, value, expected_bits) in [
            (
                160,
                false,
                (BigInt::from(1u8) << 140) + (BigInt::from(1u8) << 87) + BigInt::from(1u8),
                (2f64.powi(140) + 2f64.powi(88)).to_bits() as u128,
            ),
            (
                192,
                true,
                BigInt::from(-1)
                    * ((BigInt::from(1u8) << 140) + (BigInt::from(1u8) << 87) + BigInt::from(1u8)),
                (-(2f64.powi(140) + 2f64.powi(88))).to_bits() as u128,
            ),
        ] {
            let (func, mut symbols) =
                build_int_to_fp_check_func(bits, signed, value, expected_bits);
            let legalized = legalize(&func, &X86LegalityInfo, &mut symbols).expect("legalized");
            let mut module = Module::new("test");
            module.symbols = symbols;
            module.add_function(legalized);
            let mut interp = Interpreter::new(&module, ExecMode::Strict);
            let result = interp.run("wide_int_to_fp_check");
            match result {
                InterpResult::Ok(Some(Value::Bool(true))) => {}
                other => panic!("unexpected result: {other}"),
            }
        }
    }

    #[test]
    fn interpret_legalized_carrying_mul_add_small_and_double_width_regressions() {
        for (bits, signed, a, op_b, carry, add, expected_lo, expected_hi) in [
            (
                8,
                false,
                BigInt::from(255u16),
                BigInt::from(255u16),
                BigInt::from(0u8),
                BigInt::from(0u8),
                BigInt::from(1u8),
                BigInt::from(254u16),
            ),
            (
                64,
                false,
                BigInt::from(u64::MAX),
                BigInt::from(u64::MAX),
                BigInt::from(0u8),
                BigInt::from(0u8),
                BigInt::from(1u8),
                BigInt::parse_bytes(b"18446744073709551614", 10).unwrap(),
            ),
        ] {
            let (func, mut symbols) = build_carrying_mul_add_check_func(
                bits,
                signed,
                a,
                op_b,
                carry,
                add,
                expected_lo,
                expected_hi,
            );
            let legalized = legalize(&func, &X86LegalityInfo, &mut symbols).expect("legalized");
            let mut module = Module::new("test");
            module.symbols = symbols;
            module.add_function(legalized);
            let mut interp = Interpreter::new(&module, ExecMode::Strict);
            let result = interp.run("carrying_mul_add_check");
            match result {
                InterpResult::Ok(Some(Value::Bool(true))) => {}
                other => panic!("unexpected result: {other}"),
            }
        }
    }

    #[test]
    fn interpret_legalized_exact_double_width_clz_regression() {
        let (func, mut symbols) = build_clz_check_func(128, BigInt::from(u128::MAX), 0);
        let legalized = legalize(&func, &X86LegalityInfo, &mut symbols).expect("legalized");
        let mut module = Module::new("test");
        module.symbols = symbols;
        module.add_function(legalized);
        let mut interp = Interpreter::new(&module, ExecMode::Strict);
        let result = interp.run("wide_clz_check");
        match result {
            InterpResult::Ok(Some(Value::Bool(true))) => {}
            other => panic!("unexpected result: {other}"),
        }
    }

    #[test]
    fn interpret_legalized_wide_fp_to_int_regressions() {
        let (func, mut symbols) = build_fp_to_int_check_func(
            160,
            false,
            (2f64.powi(96)).to_bits() as u128,
            BigInt::from(1u8) << 96,
        );
        let legalized = legalize(&func, &X86LegalityInfo, &mut symbols).expect("legalized");
        let mut module = Module::new("test");
        module.symbols = symbols;
        module.add_function(legalized);
        let mut interp = Interpreter::new(&module, ExecMode::Strict);
        let result = interp.run("wide_fp_to_int_check");
        match result {
            InterpResult::Ok(Some(Value::Bool(true))) => {}
            other => panic!("unexpected result: {other}"),
        }
    }
}
