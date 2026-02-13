//! IR verifier: structural integrity and type-safety checks.
//!
//! Collects all errors rather than stopping at the first one.
//! Entry points: `Module::verify()` and `Function::verify()`.

use std::collections::HashSet;
use std::fmt;

use crate::function::{CfgNode, Function, RegionKind};
use crate::instruction::{Instruction, Op, Operand};
use crate::module::{Module, SymbolTable};
use crate::types::{Annotation, MemoryOrdering, Type};
use crate::value::{BlockRef, RegionRef, ValueRef};

// ---------------------------------------------------------------------------
// Error types
// ---------------------------------------------------------------------------

/// Location context for a verification error.
#[derive(Debug, Clone)]
pub enum Location {
    Module,
    Function(String),
    Block(String, u32),
    Instruction(String, u32, u32),
}

impl fmt::Display for Location {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Location::Module => write!(f, "module"),
            Location::Function(name) => write!(f, "func @{name}"),
            Location::Block(name, bi) => write!(f, "func @{name}, bb{bi}"),
            Location::Instruction(name, bi, ii) => {
                write!(f, "func @{name}, bb{bi}, inst {ii}")
            }
        }
    }
}

/// A single verification error.
#[derive(Debug, Clone)]
pub struct VerifyError {
    pub location: Location,
    pub message: String,
}

impl fmt::Display for VerifyError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[{}] {}", self.location, self.message)
    }
}

/// Collected verification results.
#[derive(Debug, Default)]
pub struct VerifyResult {
    pub errors: Vec<VerifyError>,
}

impl VerifyResult {
    pub fn is_ok(&self) -> bool {
        self.errors.is_empty()
    }

    fn error(&mut self, location: Location, message: impl Into<String>) {
        self.errors.push(VerifyError {
            location,
            message: message.into(),
        });
    }
}

impl fmt::Display for VerifyResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_ok() {
            return write!(f, "verification passed");
        }
        writeln!(
            f,
            "verification failed with {} error(s):",
            self.errors.len()
        )?;
        for e in &self.errors {
            writeln!(f, "  {e}")?;
        }
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// Per-function verification context
// ---------------------------------------------------------------------------

struct FuncVerifier<'a> {
    func: &'a Function,
    func_name: String,
    result: &'a mut VerifyResult,
}

impl<'a> FuncVerifier<'a> {
    fn new(func: &'a Function, func_name: String, result: &'a mut VerifyResult) -> Self {
        Self {
            func,
            func_name,
            result,
        }
    }

    fn func_loc(&self) -> Location {
        Location::Function(self.func_name.clone())
    }

    fn block_loc(&self, bi: u32) -> Location {
        Location::Block(self.func_name.clone(), bi)
    }

    fn inst_loc(&self, bi: u32, ii: u32) -> Location {
        Location::Instruction(self.func_name.clone(), bi, ii)
    }

    fn value_type(&self, v: ValueRef) -> Option<&Type> {
        if v.is_block_arg() {
            self.func
                .block_args
                .get(v.index() as usize)
                .map(|ba| &ba.ty)
        } else if v.is_secondary_result() {
            self.func
                .instructions
                .get(v.inst_index() as usize)
                .and_then(|i| i.secondary_ty.as_ref())
        } else {
            self.func
                .instructions
                .get(v.index() as usize)
                .map(|i| &i.ty)
        }
    }

    fn is_valid_value(&self, v: ValueRef) -> bool {
        if v.is_block_arg() {
            (v.index() as usize) < self.func.block_args.len()
        } else {
            (v.index() as usize) < self.func.instructions.len()
        }
    }

    fn is_valid_block(&self, b: BlockRef) -> bool {
        (b.index() as usize) < self.func.blocks.len()
    }

    fn is_valid_region(&self, r: RegionRef) -> bool {
        (r.index() as usize) < self.func.regions.len()
    }

    fn is_terminator(op: &Op) -> bool {
        matches!(
            op,
            Op::Ret(..)
                | Op::Br(_, _)
                | Op::BrIf(..)
                | Op::Continue(_)
                | Op::RegionYield(_)
                | Op::Unreachable
                | Op::Trap
        )
    }

    fn check_operand(&mut self, op: &Operand, loc: &Location) {
        if !self.is_valid_value(op.value) {
            let tag = if op.value.is_block_arg() {
                "block_arg"
            } else {
                "inst_result"
            };
            self.result.error(
                loc.clone(),
                format!("dangling {tag} reference v{}", op.value.index()),
            );
        }
    }

    fn check_operands(&mut self, ops: &[Operand], loc: &Location) {
        for op in ops {
            self.check_operand(op, loc);
        }
    }

    fn expect_type(&mut self, op: &Operand, expected: &Type, ctx: &str, loc: &Location) {
        if let Some(ty) = self.value_type(op.value)
            && ty != expected
        {
            self.result.error(
                loc.clone(),
                format!("{ctx}: expected {expected:?}, got {ty:?}"),
            );
        }
    }

    fn expect_int(&mut self, op: &Operand, ctx: &str, loc: &Location) {
        self.expect_type(op, &Type::Int, ctx, loc);
    }

    fn expect_bool(&mut self, op: &Operand, ctx: &str, loc: &Location) {
        self.expect_type(op, &Type::Bool, ctx, loc);
    }

    fn expect_ptr(&mut self, op: &Operand, ctx: &str, loc: &Location) {
        if let Some(ty) = self.value_type(op.value)
            && !matches!(ty, Type::Ptr(_))
        {
            self.result
                .error(loc.clone(), format!("{ctx}: expected Ptr, got {ty:?}"));
        }
    }

    fn expect_float(&mut self, op: &Operand, ctx: &str, loc: &Location) {
        if let Some(ty) = self.value_type(op.value)
            && !matches!(ty, Type::Float(_))
        {
            self.result
                .error(loc.clone(), format!("{ctx}: expected Float, got {ty:?}"));
        }
    }

    fn expect_mem(&mut self, op: &Operand, ctx: &str, loc: &Location) {
        self.expect_type(op, &Type::Mem, ctx, loc);
    }

    fn expect_same_type(&mut self, a: &Operand, b: &Operand, ctx: &str, loc: &Location) {
        if let (Some(ta), Some(tb)) = (self.value_type(a.value), self.value_type(b.value))
            && ta != tb
        {
            self.result.error(
                loc.clone(),
                format!("{ctx}: type mismatch {ta:?} vs {tb:?}"),
            );
        }
    }

    fn check_branch_target(&mut self, target: BlockRef, args: &[Operand], loc: &Location) {
        if !self.is_valid_block(target) {
            self.result.error(
                loc.clone(),
                format!("branch target bb{} out of bounds", target.index()),
            );
            return;
        }
        let bb = self.func.block(target);
        let expected = bb.arg_count;
        if args.len() as u32 != expected {
            self.result.error(
                loc.clone(),
                format!(
                    "branch to bb{} passes {} args, expected {}",
                    target.index(),
                    args.len(),
                    expected
                ),
            );
        }
        let arg_start = bb.arg_start as usize;
        for (i, op) in args.iter().enumerate() {
            self.check_operand(op, loc);
            if let Some(val_ty) = self.value_type(op.value)
                && let Some(ba) = self.func.block_args.get(arg_start + i)
                && *val_ty != ba.ty
            {
                self.result.error(
                    loc.clone(),
                    format!(
                        "branch to bb{} arg {}: expected {:?}, got {:?}",
                        target.index(),
                        i,
                        ba.ty,
                        val_ty
                    ),
                );
            }
        }
    }

    fn check_annotation(&mut self, ann: &Annotation, ty: &Type, ctx: &str, loc: &Location) {
        match ann {
            Annotation::Signed(_) | Annotation::Unsigned(_) => {
                if *ty != Type::Int {
                    self.result.error(
                        loc.clone(),
                        format!("{ctx}: integer annotation on non-Int type {ty:?}"),
                    );
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Instruction-level type checking
// ---------------------------------------------------------------------------

impl FuncVerifier<'_> {
    fn verify_instruction(&mut self, inst: &Instruction, bi: u32, ii: u32) {
        let loc = self.inst_loc(bi, ii);

        // Check result-side annotation validity.
        if let Some(ref ann) = inst.result_annotation {
            self.check_annotation(ann, &inst.ty, "result annotation", &loc);
        }

        match &inst.op {
            Op::Param(idx) => {
                if *idx as usize >= self.func.params.len() {
                    self.result.error(
                        loc,
                        format!(
                            "param index {} out of bounds ({} params)",
                            idx,
                            self.func.params.len()
                        ),
                    );
                } else if inst.ty != self.func.params[*idx as usize] {
                    self.result.error(
                        loc,
                        format!(
                            "param {} type {:?} != declared {:?}",
                            idx, inst.ty, self.func.params[*idx as usize]
                        ),
                    );
                }
            }

            // Integer binary ops: both Int, result Int.
            Op::Add(a, b)
            | Op::Sub(a, b)
            | Op::Mul(a, b)
            | Op::Div(a, b)
            | Op::Rem(a, b)
            | Op::And(a, b)
            | Op::Or(a, b)
            | Op::Xor(a, b)
            | Op::Shl(a, b)
            | Op::Shr(a, b)
            | Op::Min(a, b)
            | Op::Max(a, b) => {
                self.check_operand(a, &loc);
                self.check_operand(b, &loc);
                self.expect_int(a, "int arith lhs", &loc);
                self.expect_int(b, "int arith rhs", &loc);
                if inst.ty != Type::Int {
                    self.result.error(
                        loc,
                        format!("int arith result must be Int, got {:?}", inst.ty),
                    );
                }
            }

            Op::CountOnes(a) => {
                self.check_operand(a, &loc);
                self.expect_int(a, "count_ones", &loc);
                if inst.ty != Type::Int {
                    self.result.error(
                        loc,
                        format!("count_ones result must be Int, got {:?}", inst.ty),
                    );
                }
            }

            Op::CountLeadingZeros(a, bits) => {
                self.check_operand(a, &loc);
                self.expect_int(a, "count_leading_zeros", &loc);
                if *bits == 0 {
                    self.result
                        .error(loc.clone(), "count_leading_zeros bit width must be > 0");
                }
                if inst.ty != Type::Int {
                    self.result.error(
                        loc,
                        format!("count_leading_zeros result must be Int, got {:?}", inst.ty),
                    );
                }
            }

            Op::CountTrailingZeros(a) => {
                self.check_operand(a, &loc);
                self.expect_int(a, "count_trailing_zeros", &loc);
                if inst.ty != Type::Int {
                    self.result.error(
                        loc,
                        format!("count_trailing_zeros result must be Int, got {:?}", inst.ty),
                    );
                }
            }

            Op::Const(_) => {
                if inst.ty != Type::Int {
                    self.result
                        .error(loc, format!("const result must be Int, got {:?}", inst.ty));
                }
            }

            Op::BConst(_) => {
                if inst.ty != Type::Bool {
                    self.result.error(
                        loc,
                        format!("bconst result must be Bool, got {:?}", inst.ty),
                    );
                }
            }

            Op::ICmp(_, a, b) => {
                self.check_operand(a, &loc);
                self.check_operand(b, &loc);
                self.expect_int(a, "icmp lhs", &loc);
                self.expect_int(b, "icmp rhs", &loc);
                if inst.ty != Type::Bool {
                    self.result
                        .error(loc, format!("icmp result must be Bool, got {:?}", inst.ty));
                }
            }

            Op::Select(cond, tv, fv) => {
                self.check_operand(cond, &loc);
                self.check_operand(tv, &loc);
                self.check_operand(fv, &loc);
                self.expect_bool(cond, "select cond", &loc);
                self.expect_same_type(tv, fv, "select arms", &loc);
            }

            Op::BoolToInt(a) => {
                self.check_operand(a, &loc);
                self.expect_bool(a, "bool_to_int", &loc);
                if inst.ty != Type::Int {
                    self.result.error(
                        loc,
                        format!("bool_to_int result must be Int, got {:?}", inst.ty),
                    );
                }
            }

            Op::IntToBool(a) => {
                self.check_operand(a, &loc);
                self.expect_int(a, "int_to_bool", &loc);
                if inst.ty != Type::Bool {
                    self.result.error(
                        loc,
                        format!("int_to_bool result must be Bool, got {:?}", inst.ty),
                    );
                }
            }

            // Dispatch remaining ops to a separate method.
            _ => self.verify_instruction_rest(inst, &loc),
        }
    }
}

// ---------------------------------------------------------------------------
// Remaining instruction checks (memory, float, pointer, terminators)
// ---------------------------------------------------------------------------

impl FuncVerifier<'_> {
    fn verify_instruction_rest(&mut self, inst: &Instruction, loc: &Location) {
        match &inst.op {
            // -- Memory --
            Op::Load(ptr, _bytes, mem) => {
                self.check_operand(ptr, loc);
                self.check_operand(mem, loc);
                self.expect_ptr(ptr, "load ptr", loc);
                self.expect_mem(mem, "load mem", loc);
            }
            Op::Store(val, ptr, _bytes, mem) => {
                self.check_operand(val, loc);
                self.check_operand(ptr, loc);
                self.check_operand(mem, loc);
                self.expect_ptr(ptr, "store ptr", loc);
                self.expect_mem(mem, "store mem", loc);
                if inst.ty != Type::Mem {
                    self.result.error(
                        loc.clone(),
                        format!("store result must be Mem, got {:?}", inst.ty),
                    );
                }
            }
            Op::StackSlot(_) => {
                if !matches!(inst.ty, Type::Ptr(_)) {
                    self.result.error(
                        loc.clone(),
                        format!("stack_slot result must be Ptr, got {:?}", inst.ty),
                    );
                }
            }

            // -- Atomic memory --
            Op::LoadAtomic(ptr, ord, mem) => {
                self.check_operand(ptr, loc);
                self.check_operand(mem, loc);
                self.expect_ptr(ptr, "load.atomic ptr", loc);
                self.expect_mem(mem, "load.atomic mem", loc);
                self.check_load_ordering(ord, loc);
                if inst.ty != Type::Mem {
                    self.result.error(
                        loc.clone(),
                        format!("load.atomic primary result must be Mem, got {:?}", inst.ty),
                    );
                }
                if inst.secondary_ty.is_none() {
                    self.result
                        .error(loc.clone(), "load.atomic must have a secondary result type");
                }
            }
            Op::StoreAtomic(val, ptr, ord, mem) => {
                self.check_operand(val, loc);
                self.check_operand(ptr, loc);
                self.check_operand(mem, loc);
                self.expect_ptr(ptr, "store.atomic ptr", loc);
                self.expect_mem(mem, "store.atomic mem", loc);
                self.check_store_ordering(ord, loc);
                if inst.ty != Type::Mem {
                    self.result.error(
                        loc.clone(),
                        format!("store.atomic result must be Mem, got {:?}", inst.ty),
                    );
                }
            }
            Op::AtomicRmw(_, ptr, val, _ord, mem) => {
                self.check_operand(ptr, loc);
                self.check_operand(val, loc);
                self.check_operand(mem, loc);
                self.expect_ptr(ptr, "rmw ptr", loc);
                self.expect_mem(mem, "rmw mem", loc);
                if inst.ty != Type::Mem {
                    self.result.error(
                        loc.clone(),
                        format!("rmw primary result must be Mem, got {:?}", inst.ty),
                    );
                }
                if inst.secondary_ty.is_none() {
                    self.result
                        .error(loc.clone(), "rmw must have a secondary result type");
                }
            }
            Op::AtomicCmpXchg(ptr, expected, desired, _succ, fail, mem) => {
                self.check_operand(ptr, loc);
                self.check_operand(expected, loc);
                self.check_operand(desired, loc);
                self.check_operand(mem, loc);
                self.expect_ptr(ptr, "cmpxchg ptr", loc);
                self.expect_mem(mem, "cmpxchg mem", loc);
                self.expect_same_type(expected, desired, "cmpxchg expected/desired", loc);
                if matches!(fail, MemoryOrdering::Release | MemoryOrdering::AcqRel) {
                    self.result.error(
                        loc.clone(),
                        format!("cmpxchg failure ordering cannot be {:?}", fail),
                    );
                }
                if inst.ty != Type::Mem {
                    self.result.error(
                        loc.clone(),
                        format!("cmpxchg primary result must be Mem, got {:?}", inst.ty),
                    );
                }
                if inst.secondary_ty.is_none() {
                    self.result
                        .error(loc.clone(), "cmpxchg must have a secondary result type");
                }
            }
            Op::Fence(ord, mem) => {
                self.check_operand(mem, loc);
                self.expect_mem(mem, "fence mem", loc);
                if matches!(ord, MemoryOrdering::Relaxed) {
                    self.result
                        .error(loc.clone(), "fence cannot use Relaxed ordering");
                }
                if inst.ty != Type::Mem {
                    self.result.error(
                        loc.clone(),
                        format!("fence result must be Mem, got {:?}", inst.ty),
                    );
                }
            }

            _ => self.verify_instruction_final(inst, loc),
        }
    }

    fn check_load_ordering(&mut self, ord: &MemoryOrdering, loc: &Location) {
        if matches!(ord, MemoryOrdering::Release | MemoryOrdering::AcqRel) {
            self.result.error(
                loc.clone(),
                format!("load.atomic cannot use {:?} ordering", ord),
            );
        }
    }

    fn check_store_ordering(&mut self, ord: &MemoryOrdering, loc: &Location) {
        if matches!(ord, MemoryOrdering::Acquire | MemoryOrdering::AcqRel) {
            self.result.error(
                loc.clone(),
                format!("store.atomic cannot use {:?} ordering", ord),
            );
        }
    }
}

// ---------------------------------------------------------------------------
// Float, pointer, call, type-conversion, and terminator checks
// ---------------------------------------------------------------------------

impl FuncVerifier<'_> {
    fn verify_instruction_final(&mut self, inst: &Instruction, loc: &Location) {
        match &inst.op {
            // -- Float binary --
            Op::FAdd(a, b, _) | Op::FSub(a, b, _) | Op::FMul(a, b, _) | Op::FDiv(a, b, _) => {
                self.check_operand(a, loc);
                self.check_operand(b, loc);
                self.expect_float(a, "float arith lhs", loc);
                self.expect_float(b, "float arith rhs", loc);
                if !matches!(inst.ty, Type::Float(_)) {
                    self.result.error(
                        loc.clone(),
                        format!("float arith result must be Float, got {:?}", inst.ty),
                    );
                }
            }
            Op::FNeg(a) | Op::FAbs(a) => {
                self.check_operand(a, loc);
                self.expect_float(a, "float unary", loc);
                if !matches!(inst.ty, Type::Float(_)) {
                    self.result.error(
                        loc.clone(),
                        format!("float unary result must be Float, got {:?}", inst.ty),
                    );
                }
            }
            Op::CopySign(mag, sign) => {
                self.check_operand(mag, loc);
                self.check_operand(sign, loc);
                self.expect_float(mag, "copysign mag", loc);
                self.expect_float(sign, "copysign sign", loc);
                if !matches!(inst.ty, Type::Float(_)) {
                    self.result.error(
                        loc.clone(),
                        format!("copysign result must be Float, got {:?}", inst.ty),
                    );
                }
            }

            // -- Pointer ops --
            Op::PtrAdd(ptr, off) => {
                self.check_operand(ptr, loc);
                self.check_operand(off, loc);
                self.expect_ptr(ptr, "ptradd ptr", loc);
                self.expect_int(off, "ptradd offset", loc);
                if !matches!(inst.ty, Type::Ptr(_)) {
                    self.result.error(
                        loc.clone(),
                        format!("ptradd result must be Ptr, got {:?}", inst.ty),
                    );
                }
            }
            Op::PtrDiff(a, b) => {
                self.check_operand(a, loc);
                self.check_operand(b, loc);
                self.expect_ptr(a, "ptrdiff lhs", loc);
                self.expect_ptr(b, "ptrdiff rhs", loc);
                if inst.ty != Type::Int {
                    self.result.error(
                        loc.clone(),
                        format!("ptrdiff result must be Int, got {:?}", inst.ty),
                    );
                }
            }
            Op::PtrToInt(a) | Op::PtrToAddr(a) => {
                self.check_operand(a, loc);
                self.expect_ptr(a, "ptr-to-int/addr", loc);
                if inst.ty != Type::Int {
                    self.result.error(
                        loc.clone(),
                        format!("ptr-to-int/addr result must be Int, got {:?}", inst.ty),
                    );
                }
            }
            Op::IntToPtr(a) => {
                self.check_operand(a, loc);
                self.expect_int(a, "inttoptr", loc);
                if !matches!(inst.ty, Type::Ptr(_)) {
                    self.result.error(
                        loc.clone(),
                        format!("inttoptr result must be Ptr, got {:?}", inst.ty),
                    );
                }
            }

            // -- Symbol / Call --
            Op::SymbolAddr(_) => {
                if !matches!(inst.ty, Type::Ptr(_)) {
                    self.result.error(
                        loc.clone(),
                        format!("symbol_addr result must be Ptr, got {:?}", inst.ty),
                    );
                }
            }
            Op::Call(callee, args, mem) => {
                self.check_operand(callee, loc);
                self.check_operands(args, loc);
                self.check_operand(mem, loc);
                self.expect_mem(mem, "call mem", loc);
                if inst.ty != Type::Mem {
                    self.result.error(
                        loc.clone(),
                        format!("call primary result must be Mem, got {:?}", inst.ty),
                    );
                }
            }

            // -- Type conversion --
            Op::Bitcast(a) => {
                self.check_operand(a, loc);
            }
            Op::Sext(a, _) | Op::Zext(a, _) => {
                self.check_operand(a, loc);
                if inst.ty != Type::Int {
                    self.result.error(
                        loc.clone(),
                        format!("sext/zext result must be Int, got {:?}", inst.ty),
                    );
                }
            }

            // -- Terminators --
            Op::Ret(val, mem) => {
                self.check_operand(mem, loc);
                self.expect_mem(mem, "ret mem", loc);
                if let Some(op) = val {
                    self.check_operand(op, loc);
                    if let Some(ret_ty) = &self.func.ret_ty {
                        self.expect_type(op, ret_ty, "ret value", loc);
                    }
                } else if self.func.ret_ty.is_some() {
                    self.result.error(
                        loc.clone(),
                        "ret without value but function has return type",
                    );
                }
            }
            Op::Br(target, args) => {
                self.check_branch_target(*target, args, loc);
            }
            Op::BrIf(cond, then_bb, then_args, else_bb, else_args) => {
                self.check_operand(cond, loc);
                self.expect_bool(cond, "brif cond", loc);
                self.check_branch_target(*then_bb, then_args, loc);
                self.check_branch_target(*else_bb, else_args, loc);
            }
            Op::Continue(vals) | Op::RegionYield(vals) => {
                self.check_operands(vals, loc);
            }
            Op::Unreachable | Op::Trap => {}

            // All ops should be covered above; if we reach here it's a bug
            // in the verifier, not the IR.
            #[allow(unreachable_patterns)]
            _ => {}
        }
    }
}

// ---------------------------------------------------------------------------
// Block-level and region-level checks
// ---------------------------------------------------------------------------

impl FuncVerifier<'_> {
    fn verify_blocks(&mut self) {
        for (bi, bb) in self.func.blocks.iter().enumerate() {
            let bi = bi as u32;
            let loc = self.block_loc(bi);

            // Parent region must be valid.
            if !self.is_valid_region(bb.parent_region) {
                self.result.error(
                    loc.clone(),
                    format!("parent region {} out of bounds", bb.parent_region.index()),
                );
            }

            // Instruction range must be in bounds.
            let inst_end = bb.inst_start as usize + bb.inst_count as usize;
            if inst_end > self.func.instructions.len() {
                self.result.error(
                    loc.clone(),
                    format!(
                        "instruction range [{}..{}) exceeds arena size {}",
                        bb.inst_start,
                        inst_end,
                        self.func.instructions.len()
                    ),
                );
                continue;
            }

            // Block arg range must be in bounds.
            let arg_end = bb.arg_start as usize + bb.arg_count as usize;
            if arg_end > self.func.block_args.len() {
                self.result.error(
                    loc.clone(),
                    format!(
                        "block arg range [{}..{}) exceeds arena size {}",
                        bb.arg_start,
                        arg_end,
                        self.func.block_args.len()
                    ),
                );
            }

            // Block must have at least one instruction.
            if bb.inst_count == 0 {
                self.result.error(loc.clone(), "block has no instructions");
                continue;
            }

            // Last instruction must be a terminator.
            let last_idx = bb.inst_start + bb.inst_count - 1;
            let last = &self.func.instructions[last_idx as usize];
            if !Self::is_terminator(&last.op) {
                self.result.error(
                    loc.clone(),
                    format!(
                        "block does not end with a terminator (last op: {:?})",
                        last.op
                    ),
                );
            }

            // Non-last instructions must NOT be terminators.
            for i in 0..bb.inst_count - 1 {
                let idx = (bb.inst_start + i) as usize;
                let inst = &self.func.instructions[idx];
                if Self::is_terminator(&inst.op) {
                    self.result
                        .error(self.inst_loc(bi, i), "terminator in non-terminal position");
                }
            }

            // Verify each instruction.
            for i in 0..bb.inst_count {
                let idx = (bb.inst_start + i) as usize;
                let inst = &self.func.instructions[idx];
                self.verify_instruction(inst, bi, i);
            }
        }
    }

    fn verify_regions(&mut self) {
        if self.func.regions.is_empty() {
            self.result
                .error(self.func_loc(), "function has no regions");
            return;
        }

        // Root region must be valid and of kind Function.
        if !self.is_valid_region(self.func.root_region) {
            self.result.error(
                self.func_loc(),
                format!(
                    "root region {} out of bounds",
                    self.func.root_region.index()
                ),
            );
            return;
        }
        let root = self.func.region(self.func.root_region);
        if root.kind != RegionKind::Function {
            self.result.error(
                self.func_loc(),
                format!("root region must be Function, got {:?}", root.kind),
            );
        }
        if root.parent.is_some() {
            self.result
                .error(self.func_loc(), "root region must have no parent");
        }

        // Validate each region.
        let mut blocks_seen = HashSet::new();
        for (ri, region) in self.func.regions.iter().enumerate() {
            let ri_ref = RegionRef(ri as u32);
            let loc = self.func_loc();

            // Parent must be valid (if present).
            if let Some(parent) = region.parent
                && !self.is_valid_region(parent)
            {
                self.result.error(
                    loc.clone(),
                    format!("region {} parent {} out of bounds", ri, parent.index()),
                );
            }

            // Entry block must be valid.
            if !self.is_valid_block(region.entry_block) {
                self.result.error(
                    loc.clone(),
                    format!(
                        "region {} entry block {} out of bounds",
                        ri,
                        region.entry_block.index()
                    ),
                );
            }

            // Children must reference valid blocks/regions.
            for child in &region.children {
                match child {
                    CfgNode::Block(br) => {
                        if !self.is_valid_block(*br) {
                            self.result.error(
                                loc.clone(),
                                format!("region {} child block {} out of bounds", ri, br.index()),
                            );
                        } else {
                            // Block's parent_region must match.
                            let bb = self.func.block(*br);
                            if bb.parent_region != ri_ref {
                                self.result.error(
                                    loc.clone(),
                                    format!(
                                        "block {} parent_region is {}, expected {}",
                                        br.index(),
                                        bb.parent_region.index(),
                                        ri
                                    ),
                                );
                            }
                            // Each block should appear in exactly one region.
                            if !blocks_seen.insert(br.index()) {
                                self.result.error(
                                    loc.clone(),
                                    format!("block {} appears in multiple regions", br.index()),
                                );
                            }
                        }
                    }
                    CfgNode::Region(rr) => {
                        if !self.is_valid_region(*rr) {
                            self.result.error(
                                loc.clone(),
                                format!("region {} child region {} out of bounds", ri, rr.index()),
                            );
                        }
                    }
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Main entry points
// ---------------------------------------------------------------------------

impl FuncVerifier<'_> {
    fn verify_all(&mut self) {
        // Function-level structural checks.
        if self.func.param_annotations.len() != self.func.params.len() {
            self.result.error(
                self.func_loc(),
                format!(
                    "param_annotations length {} != params length {}",
                    self.func.param_annotations.len(),
                    self.func.params.len()
                ),
            );
        }

        // Check param annotations are valid.
        for (i, ann) in self.func.param_annotations.iter().enumerate() {
            if let Some(a) = ann {
                let loc = self.func_loc();
                self.check_annotation(a, &self.func.params[i], "param annotation", &loc);
            }
        }

        // Check return annotation.
        if let Some(ref ann) = self.func.ret_annotation
            && let Some(ref ret_ty) = self.func.ret_ty
        {
            let loc = self.func_loc();
            self.check_annotation(ann, ret_ty, "return annotation", &loc);
        }

        self.verify_regions();
        self.verify_blocks();
    }
}

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/// Verify a single function.
pub fn verify_function(func: &Function, symbols: &SymbolTable) -> VerifyResult {
    let mut result = VerifyResult::default();
    let name = symbols.resolve(func.name).to_string();
    let mut v = FuncVerifier::new(func, name, &mut result);
    v.verify_all();
    result
}

/// Verify an entire module.
pub fn verify_module(module: &Module) -> VerifyResult {
    let mut result = VerifyResult::default();

    // Check for duplicate function names.
    let mut seen_names = HashSet::new();
    for func in &module.functions {
        let name = module.resolve(func.name);
        if !seen_names.insert(name.to_string()) {
            result.error(Location::Module, format!("duplicate function name @{name}"));
        }
    }

    // Verify each function.
    for func in &module.functions {
        let name = module.resolve(func.name).to_string();
        let mut v = FuncVerifier::new(func, name, &mut result);
        v.verify_all();
    }

    result
}
