//! Cranelift-style text format for tuffy IR.
//!
//! Output format:
//! ```text
//! func @name(int, int) -> int {
//!   region function {
//!     bb0(v0: int, v1: int):
//!       v2 = add v0, v1
//!       ret v2
//!   }
//! }
//! ```

use std::collections::HashMap;
use std::fmt;

use crate::function::{CfgNode, Function, RegionKind};
use crate::instruction::{ICmpOp, Op};
use crate::types::Type;
use crate::value::{BlockRef, RegionRef, ValueRef};

/// Display context that tracks value numbering.
struct DisplayCtx {
    /// Map from ValueRef raw encoding to display number.
    value_names: HashMap<u32, u32>,
    next_value: u32,
}

impl DisplayCtx {
    fn new() -> Self {
        Self {
            value_names: HashMap::new(),
            next_value: 0,
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

    /// Format a comma-separated list of values.
    fn fmt_vals(&self, vrefs: &[ValueRef]) -> String {
        vrefs
            .iter()
            .map(|v| self.fmt_val(*v))
            .collect::<Vec<_>>()
            .join(", ")
    }
}

fn fmt_type(ty: &Type) -> &'static str {
    match ty {
        Type::Int => "int",
        Type::Byte(_) => "byte",
        Type::Ptr(_) => "ptr",
    }
}

fn fmt_icmp_op(op: &ICmpOp) -> &'static str {
    match op {
        ICmpOp::Eq => "eq",
        ICmpOp::Ne => "ne",
        ICmpOp::Slt => "slt",
        ICmpOp::Sle => "sle",
        ICmpOp::Sgt => "sgt",
        ICmpOp::Sge => "sge",
        ICmpOp::Ult => "ult",
        ICmpOp::Ule => "ule",
        ICmpOp::Ugt => "ugt",
        ICmpOp::Uge => "uge",
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
fn fmt_inst(_func: &Function, vref: ValueRef, op: &Op, ctx: &DisplayCtx) -> String {
    let v = ctx.fmt_val(vref);
    match op {
        Op::Param(idx) => format!("{v} = param {idx}"),
        Op::Add(a, b) => format!("{v} = add {}, {}", ctx.fmt_val(*a), ctx.fmt_val(*b)),
        Op::Sub(a, b) => format!("{v} = sub {}, {}", ctx.fmt_val(*a), ctx.fmt_val(*b)),
        Op::Mul(a, b) => format!("{v} = mul {}, {}", ctx.fmt_val(*a), ctx.fmt_val(*b)),
        Op::AssertSext(src, bits) => {
            format!("{v} = assert_sext {}, {bits}", ctx.fmt_val(*src))
        }
        Op::AssertZext(src, bits) => {
            format!("{v} = assert_zext {}, {bits}", ctx.fmt_val(*src))
        }
        Op::Const(imm) => format!("{v} = iconst {imm}"),
        Op::ICmp(cmp, a, b) => {
            format!(
                "{v} = icmp.{} {}, {}",
                fmt_icmp_op(cmp),
                ctx.fmt_val(*a),
                ctx.fmt_val(*b)
            )
        }
        Op::Load(ptr) => format!("{v} = load {}", ctx.fmt_val(*ptr)),
        Op::Store(val, ptr) => {
            format!("store {}, {}", ctx.fmt_val(*val), ctx.fmt_val(*ptr))
        }
        Op::StackSlot(bytes) => format!("{v} = stack_slot {bytes}"),
        Op::Call(callee, args) => {
            format!(
                "{v} = call {}({})",
                ctx.fmt_val(*callee),
                ctx.fmt_vals(args)
            )
        }
        Op::Bitcast(src) => format!("{v} = bitcast {}", ctx.fmt_val(*src)),
        Op::Sext(src, bits) => format!("{v} = sext {}, {bits}", ctx.fmt_val(*src)),
        Op::Zext(src, bits) => format!("{v} = zext {}, {bits}", ctx.fmt_val(*src)),
        Op::Ret(val) => match val {
            Some(v) => format!("ret {}", ctx.fmt_val(*v)),
            None => "ret".to_string(),
        },
        Op::Br(target, args) => {
            if args.is_empty() {
                format!("br bb{}", target.index())
            } else {
                format!("br bb{}({})", target.index(), ctx.fmt_vals(args))
            }
        }
        Op::BrIf(cond, then_bb, then_args, else_bb, else_args) => {
            let cond_s = ctx.fmt_val(*cond);
            let then_s = fmt_branch_target(*then_bb, then_args, ctx);
            let else_s = fmt_branch_target(*else_bb, else_args, ctx);
            format!("brif {cond_s}, {then_s}, {else_s}")
        }
        Op::Continue(vals) => {
            if vals.is_empty() {
                "continue".to_string()
            } else {
                format!("continue {}", ctx.fmt_vals(vals))
            }
        }
        Op::RegionYield(vals) => {
            if vals.is_empty() {
                "region_yield".to_string()
            } else {
                format!("region_yield {}", ctx.fmt_vals(vals))
            }
        }
    }
}

fn fmt_branch_target(block: BlockRef, args: &[ValueRef], ctx: &DisplayCtx) -> String {
    if args.is_empty() {
        format!("bb{}", block.index())
    } else {
        format!("bb{}({})", block.index(), ctx.fmt_vals(args))
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
        writeln!(f, "{inst_pad}{}", fmt_inst(func, vref, &inst.op, ctx))?;
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

impl fmt::Display for Function {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // First pass: assign value numbers
        let mut ctx = DisplayCtx::new();
        assign_values(self, self.root_region, &mut ctx);

        // Function signature
        let params: Vec<&str> = self.params.iter().map(fmt_type).collect();
        write!(f, "func @{}({})", self.name, params.join(", "))?;
        if let Some(ref ret_ty) = self.ret_ty {
            write!(f, " -> {}", fmt_type(ret_ty))?;
        }
        writeln!(f, " {{")?;

        // Root region
        write_region(f, self, self.root_region, &ctx, 2)?;

        write!(f, "}}")
    }
}
