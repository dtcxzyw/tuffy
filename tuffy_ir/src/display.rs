//! Cranelift-style text format for tuffy IR.
//!
//! Output format:
//! ```text
//! func @name(int:s32, int:s32) -> int:s32 {
//!   bb0:
//!     v0:s32 = param 0
//!     v1:s32 = param 1
//!     v2:s32 = add v0:s32, v1:s32
//!     ret v2:s32
//! }
//! ```

use std::collections::HashMap;
use std::fmt;

use crate::function::{CfgNode, Function, RegionKind};
use crate::instruction::{AtomicRmwOp, ICmpOp, Op, Operand};
use crate::module::SymbolTable;
use crate::types::{Annotation, FloatType, FpRewriteFlags, MemoryOrdering, Type, VectorType};
use crate::value::{BlockRef, RegionRef, ValueRef};

/// Display context that tracks value numbering.
struct DisplayCtx<'a> {
    /// Map from ValueRef raw encoding to display number.
    value_names: HashMap<u32, u32>,
    next_value: u32,
    /// Optional symbol table for resolving SymbolId names.
    symbols: Option<&'a SymbolTable>,
}

impl<'a> DisplayCtx<'a> {
    fn new() -> Self {
        Self {
            value_names: HashMap::new(),
            next_value: 0,
            symbols: None,
        }
    }

    fn with_symbols(symbols: &'a SymbolTable) -> Self {
        Self {
            value_names: HashMap::new(),
            next_value: 0,
            symbols: Some(symbols),
        }
    }

    /// Assign the next sequential number to a value.
    fn assign(&mut self, vref: ValueRef) -> u32 {
        let n = self.next_value;
        self.value_names.insert(vref.raw(), n);
        self.next_value += 1;
        n
    }

    /// Get the display number for a value.
    fn name(&self, vref: ValueRef) -> u32 {
        self.value_names[&vref.raw()]
    }

    /// Format a value as "vN".
    fn fmt_val(&self, vref: ValueRef) -> String {
        format!("v{}", self.name(vref))
    }

    /// Format a value with an optional result-side annotation as "vN:s32".
    fn fmt_val_ann(&self, vref: ValueRef, ann: &Option<Annotation>) -> String {
        match ann {
            Some(a) => format!("v{}{}", self.name(vref), fmt_annotation(a)),
            None => format!("v{}", self.name(vref)),
        }
    }

    /// Format an operand (value + optional use-side annotation).
    fn fmt_operand(&self, op: &Operand) -> String {
        match &op.annotation {
            Some(a) => format!("v{}{}", self.name(op.value), fmt_annotation(a)),
            None => format!("v{}", self.name(op.value)),
        }
    }

    /// Format a comma-separated list of operands.
    fn fmt_operands(&self, ops: &[Operand]) -> String {
        ops.iter()
            .map(|o| self.fmt_operand(o))
            .collect::<Vec<_>>()
            .join(", ")
    }
}

fn fmt_type(ty: &Type) -> String {
    match ty {
        Type::Int => "int".to_string(),
        Type::Bool => "bool".to_string(),
        Type::Byte(_) => "byte".to_string(),
        Type::Ptr(_) => "ptr".to_string(),
        Type::Float(ft) => match ft {
            FloatType::BF16 => "bf16".to_string(),
            FloatType::F16 => "f16".to_string(),
            FloatType::F32 => "f32".to_string(),
            FloatType::F64 => "f64".to_string(),
        },
        Type::Vec(vt) => match vt {
            VectorType::Fixed(w) => format!("vec<{w}>"),
            VectorType::Scalable(bw) => format!("vec<vscale x {bw}>"),
        },
    }
}

fn fmt_annotation(ann: &Annotation) -> String {
    match ann {
        Annotation::Signed(n) => format!(":s{n}"),
        Annotation::Unsigned(n) => format!(":u{n}"),
    }
}

fn fmt_icmp_op(op: &ICmpOp) -> &'static str {
    match op {
        ICmpOp::Eq => "eq",
        ICmpOp::Ne => "ne",
        ICmpOp::Lt => "lt",
        ICmpOp::Le => "le",
        ICmpOp::Gt => "gt",
        ICmpOp::Ge => "ge",
    }
}

fn fmt_memory_ordering(ord: &MemoryOrdering) -> &'static str {
    match ord {
        MemoryOrdering::Relaxed => "relaxed",
        MemoryOrdering::Acquire => "acquire",
        MemoryOrdering::Release => "release",
        MemoryOrdering::AcqRel => "acqrel",
        MemoryOrdering::SeqCst => "seqcst",
    }
}

fn fmt_atomic_rmw_op(op: &AtomicRmwOp) -> &'static str {
    match op {
        AtomicRmwOp::Xchg => "xchg",
        AtomicRmwOp::Add => "add",
        AtomicRmwOp::Sub => "sub",
        AtomicRmwOp::And => "and",
        AtomicRmwOp::Or => "or",
        AtomicRmwOp::Xor => "xor",
    }
}

/// Format FP rewrite flags as a suffix string (e.g., " reassoc contract").
fn fmt_fp_rewrite_flags(flags: &FpRewriteFlags) -> String {
    let mut parts = Vec::new();
    if flags.reassoc {
        parts.push("reassoc");
    }
    if flags.contract {
        parts.push("contract");
    }
    if parts.is_empty() {
        String::new()
    } else {
        format!(" {}", parts.join(" "))
    }
}

fn fmt_region_kind(kind: &RegionKind) -> &'static str {
    match kind {
        RegionKind::Function => "function",
        RegionKind::Loop => "loop",
        RegionKind::Plain => "plain",
    }
}

/// First pass: assign display numbers to all values in region tree order.
/// Block args get numbered before instructions within each block.
fn assign_values(func: &Function, region: RegionRef, ctx: &mut DisplayCtx) {
    let reg = &func.regions[region.index() as usize];
    for child in &reg.children {
        match child {
            CfgNode::Block(bref) => {
                let bb = func.block(*bref);
                for i in 0..bb.arg_count {
                    ctx.assign(ValueRef::block_arg(bb.arg_start + i));
                }
                for i in 0..bb.inst_count {
                    ctx.assign(ValueRef::inst_result(bb.inst_start + i));
                }
            }
            CfgNode::Region(rref) => {
                assign_values(func, *rref, ctx);
            }
        }
    }
}

/// Format a single instruction. Returns the formatted string (without leading indent).
fn fmt_inst(
    _func: &Function,
    vref: ValueRef,
    op: &Op,
    result_ann: &Option<Annotation>,
    ctx: &DisplayCtx,
) -> String {
    let v = ctx.fmt_val_ann(vref, result_ann);
    match op {
        Op::Param(idx) => format!("{v} = param {idx}"),
        Op::Add(a, b) => {
            format!("{v} = add {}, {}", ctx.fmt_operand(a), ctx.fmt_operand(b))
        }
        Op::Sub(a, b) => {
            format!("{v} = sub {}, {}", ctx.fmt_operand(a), ctx.fmt_operand(b))
        }
        Op::Mul(a, b) => {
            format!("{v} = mul {}, {}", ctx.fmt_operand(a), ctx.fmt_operand(b))
        }
        Op::Div(a, b) => {
            format!("{v} = div {}, {}", ctx.fmt_operand(a), ctx.fmt_operand(b))
        }
        Op::Rem(a, b) => {
            format!("{v} = rem {}, {}", ctx.fmt_operand(a), ctx.fmt_operand(b))
        }
        Op::And(a, b) => {
            format!("{v} = and {}, {}", ctx.fmt_operand(a), ctx.fmt_operand(b))
        }
        Op::Or(a, b) => {
            format!("{v} = or {}, {}", ctx.fmt_operand(a), ctx.fmt_operand(b))
        }
        Op::Xor(a, b) => {
            format!("{v} = xor {}, {}", ctx.fmt_operand(a), ctx.fmt_operand(b))
        }
        Op::Shl(a, b) => {
            format!("{v} = shl {}, {}", ctx.fmt_operand(a), ctx.fmt_operand(b))
        }
        Op::Shr(a, b) => {
            format!("{v} = shr {}, {}", ctx.fmt_operand(a), ctx.fmt_operand(b))
        }
        Op::FAdd(a, b, flags) => {
            format!(
                "{v} = fadd{} {}, {}",
                fmt_fp_rewrite_flags(flags),
                ctx.fmt_operand(a),
                ctx.fmt_operand(b)
            )
        }
        Op::FSub(a, b, flags) => {
            format!(
                "{v} = fsub{} {}, {}",
                fmt_fp_rewrite_flags(flags),
                ctx.fmt_operand(a),
                ctx.fmt_operand(b)
            )
        }
        Op::FMul(a, b, flags) => {
            format!(
                "{v} = fmul{} {}, {}",
                fmt_fp_rewrite_flags(flags),
                ctx.fmt_operand(a),
                ctx.fmt_operand(b)
            )
        }
        Op::FDiv(a, b, flags) => {
            format!(
                "{v} = fdiv{} {}, {}",
                fmt_fp_rewrite_flags(flags),
                ctx.fmt_operand(a),
                ctx.fmt_operand(b)
            )
        }
        Op::FNeg(a) => format!("{v} = fneg {}", ctx.fmt_operand(a)),
        Op::FAbs(a) => format!("{v} = fabs {}", ctx.fmt_operand(a)),
        Op::CopySign(mag, sign) => {
            format!(
                "{v} = copysign {}, {}",
                ctx.fmt_operand(mag),
                ctx.fmt_operand(sign)
            )
        }
        Op::Const(imm) => format!("{v} = iconst {imm}"),
        Op::ICmp(cmp, a, b) => {
            format!(
                "{v} = icmp.{} {}, {}",
                fmt_icmp_op(cmp),
                ctx.fmt_operand(a),
                ctx.fmt_operand(b)
            )
        }
        Op::Select(cond, tv, fv) => {
            format!(
                "{v} = select {}, {}, {}",
                ctx.fmt_operand(cond),
                ctx.fmt_operand(tv),
                ctx.fmt_operand(fv)
            )
        }
        Op::BoolToInt(val) => {
            format!("{v} = bool_to_int {}", ctx.fmt_operand(val))
        }
        Op::Load(ptr, bytes) => format!("{v} = load.{bytes} {}", ctx.fmt_operand(ptr)),
        Op::Store(val, ptr, bytes) => {
            format!(
                "store.{bytes} {}, {}",
                ctx.fmt_operand(val),
                ctx.fmt_operand(ptr)
            )
        }
        Op::StackSlot(bytes) => format!("{v} = stack_slot {bytes}"),
        Op::LoadAtomic(ptr, ord) => {
            format!(
                "{v} = load.atomic.{} {}",
                fmt_memory_ordering(ord),
                ctx.fmt_operand(ptr)
            )
        }
        Op::StoreAtomic(val, ptr, ord) => {
            format!(
                "store.atomic.{} {}, {}",
                fmt_memory_ordering(ord),
                ctx.fmt_operand(val),
                ctx.fmt_operand(ptr)
            )
        }
        Op::AtomicRmw(rmw_op, ptr, val, ord) => {
            format!(
                "{v} = rmw.{}.{} {}, {}",
                fmt_atomic_rmw_op(rmw_op),
                fmt_memory_ordering(ord),
                ctx.fmt_operand(ptr),
                ctx.fmt_operand(val)
            )
        }
        Op::AtomicCmpXchg(ptr, expected, desired, succ, fail) => {
            format!(
                "{v} = cmpxchg.{}.{} {}, {}, {}",
                fmt_memory_ordering(succ),
                fmt_memory_ordering(fail),
                ctx.fmt_operand(ptr),
                ctx.fmt_operand(expected),
                ctx.fmt_operand(desired)
            )
        }
        Op::Fence(ord) => format!("fence.{}", fmt_memory_ordering(ord)),
        Op::SymbolAddr(sym_id) => {
            let name = match ctx.symbols {
                Some(symbols) => format!("@{}", symbols.resolve(*sym_id)),
                None => format!("${}", sym_id.0),
            };
            format!("{v} = symbol_addr {name}")
        }
        Op::Call(callee, args) => {
            format!(
                "{v} = call {}({})",
                ctx.fmt_operand(callee),
                ctx.fmt_operands(args)
            )
        }
        Op::Bitcast(src) => format!("{v} = bitcast {}", ctx.fmt_operand(src)),
        Op::Sext(src, bits) => format!("{v} = sext {}, {bits}", ctx.fmt_operand(src)),
        Op::Zext(src, bits) => format!("{v} = zext {}, {bits}", ctx.fmt_operand(src)),
        Op::PtrAdd(ptr, offset) => {
            format!(
                "{v} = ptradd {}, {}",
                ctx.fmt_operand(ptr),
                ctx.fmt_operand(offset)
            )
        }
        Op::PtrDiff(a, b) => {
            format!(
                "{v} = ptrdiff {}, {}",
                ctx.fmt_operand(a),
                ctx.fmt_operand(b)
            )
        }
        Op::PtrToInt(ptr) => format!("{v} = ptrtoint {}", ctx.fmt_operand(ptr)),
        Op::PtrToAddr(ptr) => format!("{v} = ptrtoaddr {}", ctx.fmt_operand(ptr)),
        Op::IntToPtr(val) => format!("{v} = inttoptr {}", ctx.fmt_operand(val)),
        Op::Ret(val) => match val {
            Some(o) => format!("ret {}", ctx.fmt_operand(o)),
            None => "ret".to_string(),
        },
        Op::Br(target, args) => {
            if args.is_empty() {
                format!("br bb{}", target.index())
            } else {
                format!("br bb{}({})", target.index(), ctx.fmt_operands(args))
            }
        }
        Op::BrIf(cond, then_bb, then_args, else_bb, else_args) => {
            let cond_s = ctx.fmt_operand(cond);
            let then_s = fmt_branch_target(*then_bb, then_args, ctx);
            let else_s = fmt_branch_target(*else_bb, else_args, ctx);
            format!("brif {cond_s}, {then_s}, {else_s}")
        }
        Op::Continue(vals) => {
            if vals.is_empty() {
                "continue".to_string()
            } else {
                format!("continue {}", ctx.fmt_operands(vals))
            }
        }
        Op::RegionYield(vals) => {
            if vals.is_empty() {
                "region_yield".to_string()
            } else {
                format!("region_yield {}", ctx.fmt_operands(vals))
            }
        }
        Op::CountOnes(val) => {
            format!("{v} = count_ones {}", ctx.fmt_operand(val))
        }
        Op::Unreachable => "unreachable".to_string(),
        Op::Trap => "trap".to_string(),
    }
}

fn fmt_branch_target(block: BlockRef, args: &[Operand], ctx: &DisplayCtx) -> String {
    if args.is_empty() {
        format!("bb{}", block.index())
    } else {
        format!("bb{}({})", block.index(), ctx.fmt_operands(args))
    }
}

/// Format a basic block header: `bb0(v0: int, v1: int):`
fn fmt_block_header(func: &Function, bref: BlockRef, ctx: &DisplayCtx) -> String {
    let bb = func.block(bref);
    if bb.arg_count == 0 {
        format!("bb{}:", bref.index())
    } else {
        let args: Vec<String> = (0..bb.arg_count)
            .map(|i| {
                let vref = ValueRef::block_arg(bb.arg_start + i);
                let ty = &func.block_args[(bb.arg_start + i) as usize].ty;
                format!("{}: {}", ctx.fmt_val(vref), fmt_type(ty))
            })
            .collect();
        format!("bb{}({}):", bref.index(), args.join(", "))
    }
}

/// Write a block's instructions to the formatter.
fn write_block(
    f: &mut fmt::Formatter<'_>,
    func: &Function,
    bref: BlockRef,
    ctx: &DisplayCtx,
    indent: usize,
) -> fmt::Result {
    let pad = " ".repeat(indent);
    writeln!(f, "{pad}{}", fmt_block_header(func, bref, ctx))?;

    let bb = func.block(bref);
    let inst_pad = " ".repeat(indent + 2);
    for i in 0..bb.inst_count {
        let vref = ValueRef::inst_result(bb.inst_start + i);
        let inst = func.inst(bb.inst_start + i);
        writeln!(
            f,
            "{inst_pad}{}",
            fmt_inst(func, vref, &inst.op, &inst.result_annotation, ctx)
        )?;
    }
    Ok(())
}

/// Write a region and its children to the formatter.
fn write_region(
    f: &mut fmt::Formatter<'_>,
    func: &Function,
    rref: RegionRef,
    ctx: &DisplayCtx,
    indent: usize,
) -> fmt::Result {
    let reg = &func.regions[rref.index() as usize];
    let pad = " ".repeat(indent);
    writeln!(f, "{pad}region {} {{", fmt_region_kind(&reg.kind))?;

    let child_indent = indent + 2;
    let mut first = true;
    for child in &reg.children {
        if !first {
            writeln!(f)?;
        }
        first = false;
        match child {
            CfgNode::Block(bref) => {
                write_block(f, func, *bref, ctx, child_indent)?;
            }
            CfgNode::Region(child_rref) => {
                write_region(f, func, *child_rref, ctx, child_indent)?;
            }
        }
    }

    writeln!(f, "{pad}}}")
}

/// Write the children of a region (blocks and nested regions) without the region wrapper.
fn write_region_children(
    f: &mut fmt::Formatter<'_>,
    func: &Function,
    rref: RegionRef,
    ctx: &DisplayCtx,
    indent: usize,
) -> fmt::Result {
    let reg = &func.regions[rref.index() as usize];
    let mut first = true;
    for child in &reg.children {
        if !first {
            writeln!(f)?;
        }
        first = false;
        match child {
            CfgNode::Block(bref) => {
                write_block(f, func, *bref, ctx, indent)?;
            }
            CfgNode::Region(child_rref) => {
                write_region(f, func, *child_rref, ctx, indent)?;
            }
        }
    }
    Ok(())
}

/// Write a function signature and body to the formatter.
fn write_function(f: &mut fmt::Formatter<'_>, func: &Function, ctx: &DisplayCtx) -> fmt::Result {
    // Function signature with annotations
    let params: Vec<String> = func
        .params
        .iter()
        .zip(func.param_annotations.iter())
        .map(|(ty, ann)| {
            let ty_s = fmt_type(ty);
            match ann {
                Some(a) => format!("{ty_s}{}", fmt_annotation(a)),
                None => ty_s.to_string(),
            }
        })
        .collect();
    let name_str = match ctx.symbols {
        Some(symbols) => format!("@{}", symbols.resolve(func.name)),
        None => format!("${}", func.name.0),
    };
    write!(f, "func {}({})", name_str, params.join(", "))?;

    if let Some(ref ret_ty) = func.ret_ty {
        let ret_s = fmt_type(ret_ty);
        match &func.ret_annotation {
            Some(a) => write!(f, " -> {ret_s}{}", fmt_annotation(a))?,
            None => write!(f, " -> {ret_s}")?,
        }
    }
    writeln!(f, " {{")?;

    // Elide top-level region function wrapper; write children directly
    write_region_children(f, func, func.root_region, ctx, 2)?;

    write!(f, "}}")
}

impl fmt::Display for Function {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut ctx = DisplayCtx::new();
        assign_values(self, self.root_region, &mut ctx);
        write_function(f, self, &ctx)
    }
}

/// Wrapper for displaying a `Function` with symbol table context.
pub struct FunctionDisplay<'a> {
    func: &'a Function,
    symbols: &'a SymbolTable,
}

impl fmt::Display for FunctionDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut ctx = DisplayCtx::with_symbols(self.symbols);
        assign_values(self.func, self.func.root_region, &mut ctx);
        write_function(f, self.func, &ctx)
    }
}

impl Function {
    /// Display this function with symbol name resolution.
    pub fn display<'a>(&'a self, symbols: &'a SymbolTable) -> FunctionDisplay<'a> {
        FunctionDisplay {
            func: self,
            symbols,
        }
    }
}

impl fmt::Display for crate::module::Module {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (i, func) in self.functions.iter().enumerate() {
            if i > 0 {
                writeln!(f)?;
                writeln!(f)?;
            }
            let mut ctx = DisplayCtx::with_symbols(&self.symbols);
            assign_values(func, func.root_region, &mut ctx);
            write_function(f, func, &ctx)?;
        }
        Ok(())
    }
}
