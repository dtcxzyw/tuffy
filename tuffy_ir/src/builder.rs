//! Builder API for constructing tuffy IR.
//!
//! Origin is mandatory on every instruction — enforced at compile time.

use num_bigint::BigInt;

use crate::function::{BasicBlock, BlockArg, CfgNode, Function, Region, RegionKind};
use crate::instruction::{AtomicRmwOp, FCmpOp, ICmpOp, Instruction, Op, Operand, Origin};
use crate::module::SymbolId;
use crate::typed::{
    BoolOperand, BoolValue, FloatOperand, FloatValue, IntOperand, IntValue, MemOperand, MemValue,
    PtrOperand, PtrValue,
};
use crate::types::{Annotation, FloatType, FpRewriteFlags, MemoryOrdering, Type};
use crate::value::{BlockRef, RegionRef, ValueRef};

/// Builder for constructing a function's IR.
pub struct Builder<'a> {
    func: &'a mut Function,
    current_block: Option<BlockRef>,
    region_stack: Vec<RegionRef>,
}

impl<'a> Builder<'a> {
    pub fn new(func: &'a mut Function) -> Self {
        Self {
            func,
            current_block: None,
            region_stack: Vec::new(),
        }
    }

    // ── Region management ──

    /// Create a new region and return its reference. Does NOT enter it.
    pub fn create_region(&mut self, kind: RegionKind) -> RegionRef {
        let idx = self.func.regions.len() as u32;
        let parent = self.region_stack.last().copied();
        self.func.regions.push(Region {
            kind,
            parent,
            entry_block: BlockRef(0), // placeholder, set when first block is created
            children: Vec::new(),
        });
        let region_ref = RegionRef(idx);

        // Register as child of parent region
        if let Some(parent_ref) = parent {
            self.func.regions[parent_ref.index() as usize]
                .children
                .push(CfgNode::Region(region_ref));
        }

        region_ref
    }

    /// Enter a region (push onto stack). Subsequent blocks are created in this region.
    pub fn enter_region(&mut self, region: RegionRef) {
        self.region_stack.push(region);
    }

    /// Exit the current region (pop from stack).
    pub fn exit_region(&mut self) {
        self.region_stack.pop();
    }

    fn current_region(&self) -> RegionRef {
        *self.region_stack.last().expect("no active region")
    }

    // ── Block management ──

    /// Create a new basic block in the current region and return its reference.
    pub fn create_block(&mut self) -> BlockRef {
        let idx = self.func.blocks.len() as u32;
        let region = self.current_region();
        self.func.blocks.push(BasicBlock {
            parent_region: region,
            arg_start: self.func.block_args.len() as u32,
            arg_count: 0,
            inst_start: self.func.instructions.len() as u32,
            inst_count: 0,
        });
        let block_ref = BlockRef(idx);

        // Register as child of current region
        let region_idx = region.index() as usize;
        self.func.regions[region_idx]
            .children
            .push(CfgNode::Block(block_ref));

        // If this is the first block in the region, set it as entry
        let is_first = self.func.regions[region_idx]
            .children
            .iter()
            .filter(|c| matches!(c, CfgNode::Block(_)))
            .count()
            == 1;
        if is_first {
            self.func.regions[region_idx].entry_block = block_ref;
        }

        block_ref
    }

    /// Set the current block for subsequent instructions.
    pub fn switch_to_block(&mut self, block: BlockRef) {
        // Update inst_start to current position in instruction arena.
        // This ensures blocks created early but filled later get the right start.
        let bb = &mut self.func.blocks[block.index() as usize];
        if bb.inst_count == 0 {
            bb.inst_start = self.func.instructions.len() as u32;
        }
        self.current_block = Some(block);
    }

    /// Query the IR type of a value produced by an instruction or block argument.
    pub fn value_type(&self, v: ValueRef) -> Option<&Type> {
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

    pub fn value_annotation(&self, v: ValueRef) -> Option<&Annotation> {
        if v.is_block_arg() || v.is_secondary_result() {
            None
        } else {
            self.func
                .instructions
                .get(v.index() as usize)
                .and_then(|i| i.result_annotation.as_ref())
        }
    }

    /// If `v` is a StackSlot instruction, return its size in bytes.
    pub fn stack_slot_size(&self, v: ValueRef) -> Option<u32> {
        if v.is_block_arg() || v.is_secondary_result() {
            return None;
        }
        match self.func.instructions.get(v.index() as usize) {
            Some(inst) => match &inst.op {
                Op::StackSlot(bytes) => Some(*bytes),
                _ => None,
            },
            None => None,
        }
    }

    /// Returns true if `v` is a StackSlot, SymbolAddr, or PtrAdd —
    /// i.e. a pointer that addresses memory rather than being a
    /// pointer-sized *value* (like `NonNull<T>`).
    pub fn is_memory_address(&self, v: ValueRef) -> bool {
        if v.is_block_arg() || v.is_secondary_result() {
            return false;
        }
        matches!(
            self.func.instructions.get(v.index() as usize),
            Some(inst) if matches!(inst.op, Op::StackSlot(_) | Op::SymbolAddr(_) | Op::PtrAdd(..))

        )
    }

    /// Add a block argument and return its ValueRef.
    pub fn add_block_arg(
        &mut self,
        block: BlockRef,
        ty: Type,
        annotation: Option<Annotation>,
    ) -> ValueRef {
        let arg_idx = self.func.block_args.len() as u32;
        self.func.block_args.push(BlockArg { ty, annotation });
        self.func.blocks[block.index() as usize].arg_count += 1;
        ValueRef::block_arg(arg_idx)
    }

    // ── Instruction emission ──

    fn push_inst(
        &mut self,
        op: Op,
        ty: Type,
        secondary_ty: Option<Type>,
        origin: Origin,
        ann: Option<Annotation>,
    ) -> ValueRef {
        let idx = self.func.instructions.len() as u32;
        self.func.instructions.push(Instruction {
            op,
            ty,
            secondary_ty,
            origin,
            result_annotation: ann,
            secondary_result_annotation: None,
        });
        if let Some(bb) = self.current_block {
            self.func.blocks[bb.index() as usize].inst_count += 1;
        }
        ValueRef::inst_result(idx)
    }

    fn push_inst_with_secondary(
        &mut self,
        op: Op,
        ty: Type,
        secondary_ty: Type,
        origin: Origin,
        ann: Option<Annotation>,
        secondary_ann: Option<Annotation>,
    ) -> ValueRef {
        let idx = self.func.instructions.len() as u32;
        self.func.instructions.push(Instruction {
            op,
            ty,
            secondary_ty: Some(secondary_ty),
            origin,
            result_annotation: ann,
            secondary_result_annotation: secondary_ann,
        });
        if let Some(bb) = self.current_block {
            self.func.blocks[bb.index() as usize].inst_count += 1;
        }
        ValueRef::inst_result(idx)
    }

    // ── Existing ops ──

    /// Create a function parameter reference.
    pub fn param(
        &mut self,
        index: u32,
        ty: Type,
        ann: Option<Annotation>,
        origin: Origin,
    ) -> ValueRef {
        self.push_inst(Op::Param(index), ty, None, origin, ann)
    }

    /// Integer addition (typed).
    pub fn add(
        &mut self,
        a: IntOperand,
        b: IntOperand,
        int_ann: crate::types::IntAnnotation,
        origin: Origin,
    ) -> IntValue {
        let res_ann = Some(Annotation::Int(int_ann));
        let v = self.push_inst(Op::Add(a, b), Type::Int, None, origin, res_ann);
        IntValue::new(v, self.func)
    }

    /// Integer subtraction (typed).
    pub fn sub(
        &mut self,
        a: IntOperand,
        b: IntOperand,
        int_ann: crate::types::IntAnnotation,
        origin: Origin,
    ) -> IntValue {
        let res_ann = Some(Annotation::Int(int_ann));
        let v = self.push_inst(Op::Sub(a, b), Type::Int, None, origin, res_ann);
        IntValue::new(v, self.func)
    }

    /// Integer multiplication (typed).
    pub fn mul(
        &mut self,
        a: IntOperand,
        b: IntOperand,
        int_ann: crate::types::IntAnnotation,
        origin: Origin,
    ) -> IntValue {
        let res_ann = Some(Annotation::Int(int_ann));
        let v = self.push_inst(Op::Mul(a, b), Type::Int, None, origin, res_ann);
        IntValue::new(v, self.func)
    }

    /// Integer division (typed).
    pub fn div(
        &mut self,
        a: IntOperand,
        b: IntOperand,
        int_ann: crate::types::IntAnnotation,
        origin: Origin,
    ) -> IntValue {
        let res_ann = Some(Annotation::Int(int_ann));
        let v = self.push_inst(Op::Div(a, b), Type::Int, None, origin, res_ann);
        IntValue::new(v, self.func)
    }

    /// Integer remainder (typed).
    pub fn rem(
        &mut self,
        a: IntOperand,
        b: IntOperand,
        int_ann: crate::types::IntAnnotation,
        origin: Origin,
    ) -> IntValue {
        let res_ann = Some(Annotation::Int(int_ann));
        let v = self.push_inst(Op::Rem(a, b), Type::Int, None, origin, res_ann);
        IntValue::new(v, self.func)
    }

    /// Bitwise AND (typed).
    pub fn and(
        &mut self,
        a: IntOperand,
        b: IntOperand,
        int_ann: crate::types::IntAnnotation,
        origin: Origin,
    ) -> IntValue {
        let res_ann = Some(Annotation::Int(int_ann));
        let v = self.push_inst(Op::And(a, b), Type::Int, None, origin, res_ann);
        IntValue::new(v, self.func)
    }

    /// Bitwise OR (typed).
    pub fn or(
        &mut self,
        a: IntOperand,
        b: IntOperand,
        int_ann: crate::types::IntAnnotation,
        origin: Origin,
    ) -> IntValue {
        let res_ann = Some(Annotation::Int(int_ann));
        let v = self.push_inst(Op::Or(a, b), Type::Int, None, origin, res_ann);
        IntValue::new(v, self.func)
    }

    /// Bitwise XOR (typed).
    pub fn xor(
        &mut self,
        a: IntOperand,
        b: IntOperand,
        int_ann: crate::types::IntAnnotation,
        origin: Origin,
    ) -> IntValue {
        let res_ann = Some(Annotation::Int(int_ann));
        let v = self.push_inst(Op::Xor(a, b), Type::Int, None, origin, res_ann);
        IntValue::new(v, self.func)
    }

    /// Integer constant.
    pub fn iconst(
        &mut self,
        val: impl Into<BigInt>,
        bit_width: u32,
        signedness: crate::types::IntSignedness,
        origin: Origin,
    ) -> IntValue {
        use crate::types::IntAnnotation;
        let ann = Annotation::Int(IntAnnotation {
            bit_width,
            signedness,
        });
        let v = self.push_inst(Op::Const(val.into()), Type::Int, None, origin, Some(ann));
        IntValue::new(v, self.func)
    }

    /// Boolean constant.
    pub fn bconst(&mut self, val: bool, origin: Origin) -> BoolValue {
        let v = self.push_inst(Op::BConst(val), Type::Bool, None, origin, None);
        BoolValue::new(v, self.func)
    }

    /// Float constant.
    pub fn fconst(&mut self, ft: FloatType, bits: u64, origin: Origin) -> FloatValue {
        let v = self.push_inst(Op::FConst(ft, bits), Type::Float(ft), None, origin, None);
        FloatValue::new(v, self.func)
    }

    /// Boolean AND.
    pub fn band(&mut self, a: BoolOperand, b: BoolOperand, origin: Origin) -> BoolValue {
        let v = self.push_inst(Op::BAnd(a, b), Type::Bool, None, origin, None);
        BoolValue::new(v, self.func)
    }

    /// Boolean OR.
    pub fn bor(&mut self, a: BoolOperand, b: BoolOperand, origin: Origin) -> BoolValue {
        let v = self.push_inst(Op::BOr(a, b), Type::Bool, None, origin, None);
        BoolValue::new(v, self.func)
    }

    /// Boolean XOR.
    pub fn bxor(&mut self, a: BoolOperand, b: BoolOperand, origin: Origin) -> BoolValue {
        let v = self.push_inst(Op::BXor(a, b), Type::Bool, None, origin, None);
        BoolValue::new(v, self.func)
    }

    /// Left shift.
    pub fn shl(
        &mut self,
        a: IntOperand,
        b: IntOperand,
        ann: Option<Annotation>,
        origin: Origin,
    ) -> IntValue {
        let v = self.push_inst(Op::Shl(a, b), Type::Int, None, origin, ann);
        IntValue::new(v, self.func)
    }

    /// Right shift.
    pub fn shr(
        &mut self,
        mut a: IntOperand,
        b: IntOperand,
        ann: Option<Annotation>,
        origin: Origin,
    ) -> IntValue {
        if let Some(annotation) = ann {
            a = IntOperand::annotated(IntValue::new(a.raw().value, self.func), annotation);
        }
        let v = self.push_inst(Op::Shr(a, b), Type::Int, None, origin, ann);
        IntValue::new(v, self.func)
    }

    /// Integer comparison.
    pub fn icmp(&mut self, op: ICmpOp, a: IntOperand, b: IntOperand, origin: Origin) -> BoolValue {
        let v = self.push_inst(Op::ICmp(op, a, b), Type::Bool, None, origin, None);
        BoolValue::new(v, self.func)
    }

    /// Float comparison.
    pub fn fcmp(
        &mut self,
        op: FCmpOp,
        a: FloatOperand,
        b: FloatOperand,
        origin: Origin,
    ) -> BoolValue {
        let v = self.push_inst(Op::FCmp(op, a, b), Type::Bool, None, origin, None);
        BoolValue::new(v, self.func)
    }

    /// Load from pointer.
    pub fn load(
        &mut self,
        ptr: PtrOperand,
        bytes: u32,
        ty: Type,
        mem: MemOperand,
        ann: Option<Annotation>,
        origin: Origin,
    ) -> ValueRef {
        self.push_inst(Op::Load(ptr, bytes, mem), ty, None, origin, ann)
    }

    /// Store value to pointer.
    pub fn store(
        &mut self,
        val: Operand,
        ptr: PtrOperand,
        bytes: u32,
        mem: MemOperand,
        origin: Origin,
    ) -> MemValue {
        let v = self.push_inst(
            Op::Store(val, ptr, bytes, mem),
            Type::Mem,
            None,
            origin,
            None,
        );
        MemValue::new(v, self.func)
    }

    /// Integer minimum.
    pub fn min(
        &mut self,
        mut a: Operand,
        b: Operand,
        ann: Option<Annotation>,
        origin: Origin,
    ) -> ValueRef {
        let _ty = self
            .value_type(a.value)
            .and_then(|t| match t {
                Type::Int => Some(Type::Int),
                _ => None,
            })
            .expect("min operand must be Int type");
        if ann.is_some() {
            a.annotation = ann;
        }
        self.push_inst(Op::Min(a.into(), b.into()), Type::Int, None, origin, ann)
    }

    /// Integer maximum.
    pub fn max(
        &mut self,
        mut a: Operand,
        b: Operand,
        ann: Option<Annotation>,
        origin: Origin,
    ) -> ValueRef {
        let _ty = self
            .value_type(a.value)
            .and_then(|t| match t {
                Type::Int => Some(Type::Int),
                _ => None,
            })
            .expect("max operand must be Int type");
        if ann.is_some() {
            a.annotation = ann;
        }
        self.push_inst(Op::Max(a.into(), b.into()), Type::Int, None, origin, ann)
    }

    // ── Floating point arithmetic ──

    /// Floating point addition.
    pub fn fadd(
        &mut self,
        a: Operand,
        b: Operand,
        flags: FpRewriteFlags,
        ty: Type,
        origin: Origin,
    ) -> ValueRef {
        self.push_inst(Op::FAdd(a.into(), b.into(), flags), ty, None, origin, None)
    }

    /// Floating point subtraction.
    pub fn fsub(
        &mut self,
        a: Operand,
        b: Operand,
        flags: FpRewriteFlags,
        ty: Type,
        origin: Origin,
    ) -> ValueRef {
        self.push_inst(Op::FSub(a.into(), b.into(), flags), ty, None, origin, None)
    }

    /// Floating point multiplication.
    pub fn fmul(
        &mut self,
        a: Operand,
        b: Operand,
        flags: FpRewriteFlags,
        ty: Type,
        origin: Origin,
    ) -> ValueRef {
        self.push_inst(Op::FMul(a.into(), b.into(), flags), ty, None, origin, None)
    }

    /// Floating point division.
    pub fn fdiv(
        &mut self,
        a: Operand,
        b: Operand,
        flags: FpRewriteFlags,
        ty: Type,
        origin: Origin,
    ) -> ValueRef {
        self.push_inst(Op::FDiv(a.into(), b.into(), flags), ty, None, origin, None)
    }

    /// Floating point remainder.
    pub fn frem(
        &mut self,
        a: Operand,
        b: Operand,
        flags: FpRewriteFlags,
        ty: Type,
        origin: Origin,
    ) -> ValueRef {
        self.push_inst(Op::FRem(a.into(), b.into(), flags), ty, None, origin, None)
    }

    /// IEEE 754-2008 minNum.
    pub fn fminnum(
        &mut self,
        a: FloatOperand,
        b: FloatOperand,
        ty: Type,
        origin: Origin,
    ) -> FloatValue {
        let v = self.push_inst(Op::FMinNum(a, b), ty, None, origin, None);
        FloatValue::new(v, self.func)
    }

    /// IEEE 754-2008 maxNum.
    pub fn fmaxnum(
        &mut self,
        a: FloatOperand,
        b: FloatOperand,
        ty: Type,
        origin: Origin,
    ) -> FloatValue {
        let v = self.push_inst(Op::FMaxNum(a, b), ty, None, origin, None);
        FloatValue::new(v, self.func)
    }

    /// Copy sign: magnitude from first operand, sign from second.
    pub fn copysign(
        &mut self,
        mag: FloatOperand,
        sign: FloatOperand,
        ty: Type,
        origin: Origin,
    ) -> FloatValue {
        let v = self.push_inst(Op::CopySign(mag, sign), ty, None, origin, None);
        FloatValue::new(v, self.func)
    }

    /// Floating point negation.
    pub fn fneg(&mut self, val: FloatOperand, ty: Type, origin: Origin) -> FloatValue {
        let v = self.push_inst(Op::FNeg(val), ty, None, origin, None);
        FloatValue::new(v, self.func)
    }

    /// Floating point absolute value.
    pub fn fabs(&mut self, val: FloatOperand, ty: Type, origin: Origin) -> FloatValue {
        let v = self.push_inst(Op::FAbs(val), ty, None, origin, None);
        FloatValue::new(v, self.func)
    }

    // ── Comparison ──

    /// Conditional select: if cond then true_val else false_val.
    pub fn select(
        &mut self,
        cond: Operand,
        true_val: Operand,
        false_val: Operand,
        ty: Type,
        ann: Option<Annotation>,
        origin: Origin,
    ) -> ValueRef {
        self.push_inst(
            Op::Select(cond.into(), true_val, false_val),
            ty,
            None,
            origin,
            ann,
        )
    }

    /// Population count: count the number of set bits.
    pub fn count_ones(&mut self, val: IntOperand, result_bits: u32, origin: Origin) -> IntValue {
        use crate::types::{IntAnnotation, IntSignedness};
        let ann = Annotation::Int(IntAnnotation {
            bit_width: result_bits,
            signedness: IntSignedness::Unsigned,
        });
        let v = self.push_inst(Op::CountOnes(val), Type::Int, None, origin, Some(ann));
        IntValue::new(v, self.func)
    }

    /// Count leading zeros after truncating to `bits` width.
    pub fn count_leading_zeros(
        &mut self,
        val: Operand,
        bits: u32,
        result_bits: u32,
        origin: Origin,
    ) -> ValueRef {
        use crate::types::{IntAnnotation, IntSignedness};
        let ann = Annotation::Int(IntAnnotation {
            bit_width: result_bits,
            signedness: IntSignedness::Unsigned,
        });
        self.push_inst(
            Op::CountLeadingZeros(val.into(), bits),
            Type::Int,
            None,
            origin,
            Some(ann),
        )
    }

    /// Count trailing zeros.
    pub fn count_trailing_zeros(
        &mut self,
        val: Operand,
        result_bits: u32,
        origin: Origin,
    ) -> ValueRef {
        use crate::types::{IntAnnotation, IntSignedness};
        let ann = Annotation::Int(IntAnnotation {
            bit_width: result_bits,
            signedness: IntSignedness::Unsigned,
        });
        self.push_inst(
            Op::CountTrailingZeros(val.into()),
            Type::Int,
            None,
            origin,
            Some(ann),
        )
    }

    /// Byte-swap: reverse byte order of the low `bytes` bytes.
    pub fn bswap(&mut self, val: IntOperand, bytes: u32, origin: Origin) -> IntValue {
        let op = val.clone().raw();
        let _ty = self
            .value_type(op.value)
            .filter(|t| matches!(t, Type::Int))
            .expect("bswap operand must be Int type");
        let ann = self.value_annotation(op.value).cloned();
        let v = self.push_inst(Op::Bswap(val, bytes), Type::Int, None, origin, ann);
        IntValue::new(v, self.func)
    }

    /// Bit-reverse: reverse bit order of the low `bits` bits.
    pub fn bit_reverse(&mut self, val: IntOperand, bits: u32, origin: Origin) -> IntValue {
        let op = val.clone().raw();
        let _ty = self
            .value_type(op.value)
            .filter(|t| matches!(t, Type::Int))
            .expect("bit_reverse operand must be Int type");
        let ann = self.value_annotation(op.value).cloned();
        let v = self.push_inst(Op::BitReverse(val, bits), Type::Int, None, origin, ann);
        IntValue::new(v, self.func)
    }

    /// Merge: replace the low `width` bits of `a` with the low `width` bits of `b`.
    pub fn merge(&mut self, a: IntOperand, b: IntOperand, width: u32, origin: Origin) -> IntValue {
        let op_a = a.clone().raw();
        let _op_b = b.clone().raw();
        let _ty = self
            .value_type(op_a.value)
            .and_then(|t| match t {
                Type::Int => Some(Type::Int),
                _ => None,
            })
            .expect("merge operand must be Int type");
        let ann = self.value_annotation(op_a.value).cloned();
        let v = self.push_inst(Op::Merge(a, b, width), Type::Int, None, origin, ann);
        IntValue::new(v, self.func)
    }

    /// Carry-less multiplication (polynomial multiplication over GF(2)).
    pub fn clmul(&mut self, a: IntOperand, b: IntOperand, origin: Origin) -> IntValue {
        let op_a = a.clone().raw();
        let _op_b = b.clone().raw();
        let _ty = self
            .value_type(op_a.value)
            .and_then(|t| match t {
                Type::Int => Some(Type::Int),
                _ => None,
            })
            .expect("clmul operand must be Int type");
        let ann = self.value_annotation(op_a.value).cloned();
        let v = self.push_inst(Op::Clmul(a, b), Type::Int, None, origin, ann);
        IntValue::new(v, self.func)
    }

    /// Split: decompose `a` at bit position `width`. Returns (hi, lo).
    pub fn split(&mut self, a: IntOperand, width: u32, origin: Origin) -> (IntValue, IntValue) {
        let op = a.clone().raw();
        let ty = self
            .value_type(op.value)
            .and_then(|t| match t {
                Type::Int => Some(Type::Int),
                _ => None,
            })
            .expect("split operand must be Int type");
        let primary = self.push_inst(Op::Split(a, width), ty.clone(), Some(ty), origin, None);
        let secondary = ValueRef::inst_secondary_result(primary.index());
        (
            IntValue::new(primary, self.func),
            IntValue::new(secondary, self.func),
        )
    }

    /// Rotate left in an `bits`-bit field.
    pub fn rotate_left(
        &mut self,
        val: Operand,
        amt: Operand,
        bits: u32,
        origin: Origin,
    ) -> ValueRef {
        let _ty = self
            .value_type(val.value)
            .and_then(|t| match t {
                Type::Int => Some(Type::Int),
                _ => None,
            })
            .expect("rotate_left operand must be Int type");
        let ann = self.value_annotation(val.value).cloned();
        self.push_inst(
            Op::RotateLeft(val.into(), amt.into(), bits),
            Type::Int,
            None,
            origin,
            ann,
        )
    }

    /// Rotate right in an `bits`-bit field.
    pub fn rotate_right(
        &mut self,
        val: Operand,
        amt: Operand,
        bits: u32,
        origin: Origin,
    ) -> ValueRef {
        let _ty = self
            .value_type(val.value)
            .and_then(|t| match t {
                Type::Int => Some(Type::Int),
                _ => None,
            })
            .expect("rotate_right operand must be Int type");
        let ann = self.value_annotation(val.value).cloned();
        self.push_inst(
            Op::RotateRight(val.into(), amt.into(), bits),
            Type::Int,
            None,
            origin,
            ann,
        )
    }

    /// Unsigned saturating addition in `bits` bits.
    pub fn saturating_add(
        &mut self,
        a: Operand,
        b: Operand,
        bits: u32,
        origin: Origin,
    ) -> ValueRef {
        use crate::types::{IntAnnotation, IntSignedness};
        let ann = Annotation::Int(IntAnnotation {
            bit_width: bits,
            signedness: IntSignedness::Unsigned,
        });
        self.push_inst(
            Op::SaturatingAdd(a.into(), b.into(), bits),
            Type::Int,
            None,
            origin,
            Some(ann),
        )
    }

    /// Unsigned saturating subtraction in `bits` bits.
    pub fn saturating_sub(
        &mut self,
        a: Operand,
        b: Operand,
        bits: u32,
        origin: Origin,
    ) -> ValueRef {
        use crate::types::{IntAnnotation, IntSignedness};
        let ann = Annotation::Int(IntAnnotation {
            bit_width: bits,
            signedness: IntSignedness::Unsigned,
        });
        self.push_inst(
            Op::SaturatingSub(a.into(), b.into(), bits),
            Type::Int,
            None,
            origin,
            Some(ann),
        )
    }

    /// Signed saturating addition in `bits` bits.
    /// Result is clamped to [-(2^(bits-1)), 2^(bits-1)-1].
    pub fn signed_saturating_add(
        &mut self,
        a: Operand,
        b: Operand,
        bits: u32,
        origin: Origin,
    ) -> ValueRef {
        use crate::types::{IntAnnotation, IntSignedness};
        let ann = Annotation::Int(IntAnnotation {
            bit_width: bits,
            signedness: IntSignedness::Signed,
        });
        self.push_inst(
            Op::SignedSaturatingAdd(a.into(), b.into(), bits),
            Type::Int,
            None,
            origin,
            Some(ann),
        )
    }

    /// Signed saturating subtraction in `bits` bits.
    /// Result is clamped to [-(2^(bits-1)), 2^(bits-1)-1].
    pub fn signed_saturating_sub(
        &mut self,
        a: Operand,
        b: Operand,
        bits: u32,
        origin: Origin,
    ) -> ValueRef {
        use crate::types::{IntAnnotation, IntSignedness};
        let ann = Annotation::Int(IntAnnotation {
            bit_width: bits,
            signedness: IntSignedness::Signed,
        });
        self.push_inst(
            Op::SignedSaturatingSub(a.into(), b.into(), bits),
            Type::Int,
            None,
            origin,
            Some(ann),
        )
    }

    /// Signed addition with overflow detection. Returns (wrapping_sum: Int, overflow: Bool).
    pub fn sadd_with_overflow(
        &mut self,
        a: Operand,
        b: Operand,
        bits: u32,
        origin: Origin,
    ) -> (ValueRef, ValueRef) {
        use crate::types::{IntAnnotation, IntSignedness};
        let ann = Annotation::Int(IntAnnotation {
            bit_width: bits,
            signedness: IntSignedness::Signed,
        });
        let primary = self.push_inst_with_secondary(
            Op::SAddWithOverflow(a.into(), b.into(), bits),
            Type::Int,
            Type::Bool,
            origin,
            Some(ann),
            None,
        );
        let secondary = ValueRef::inst_secondary_result(primary.index());
        (primary, secondary)
    }

    /// Unsigned addition with overflow detection. Returns (wrapping_sum: Int, overflow: Bool).
    pub fn uadd_with_overflow(
        &mut self,
        a: Operand,
        b: Operand,
        bits: u32,
        origin: Origin,
    ) -> (ValueRef, ValueRef) {
        use crate::types::{IntAnnotation, IntSignedness};
        let ann = Annotation::Int(IntAnnotation {
            bit_width: bits,
            signedness: IntSignedness::Unsigned,
        });
        let primary = self.push_inst_with_secondary(
            Op::UAddWithOverflow(a.into(), b.into(), bits),
            Type::Int,
            Type::Bool,
            origin,
            Some(ann),
            None,
        );
        let secondary = ValueRef::inst_secondary_result(primary.index());
        (primary, secondary)
    }

    /// Signed subtraction with overflow detection. Returns (wrapping_diff: Int, overflow: Bool).
    pub fn ssub_with_overflow(
        &mut self,
        a: Operand,
        b: Operand,
        bits: u32,
        origin: Origin,
    ) -> (ValueRef, ValueRef) {
        use crate::types::{IntAnnotation, IntSignedness};
        let ann = Annotation::Int(IntAnnotation {
            bit_width: bits,
            signedness: IntSignedness::Signed,
        });
        let primary = self.push_inst_with_secondary(
            Op::SSubWithOverflow(a.into(), b.into(), bits),
            Type::Int,
            Type::Bool,
            origin,
            Some(ann),
            None,
        );
        let secondary = ValueRef::inst_secondary_result(primary.index());
        (primary, secondary)
    }

    /// Unsigned subtraction with overflow detection. Returns (wrapping_diff: Int, overflow: Bool).
    pub fn usub_with_overflow(
        &mut self,
        a: Operand,
        b: Operand,
        bits: u32,
        origin: Origin,
    ) -> (ValueRef, ValueRef) {
        use crate::types::{IntAnnotation, IntSignedness};
        let ann = Annotation::Int(IntAnnotation {
            bit_width: bits,
            signedness: IntSignedness::Unsigned,
        });
        let primary = self.push_inst_with_secondary(
            Op::USubWithOverflow(a.into(), b.into(), bits),
            Type::Int,
            Type::Bool,
            origin,
            Some(ann),
            None,
        );
        let secondary = ValueRef::inst_secondary_result(primary.index());
        (primary, secondary)
    }

    /// Signed multiplication with overflow detection. Returns (wrapping_product: Int, overflow: Bool).
    pub fn smul_with_overflow(
        &mut self,
        a: Operand,
        b: Operand,
        bits: u32,
        origin: Origin,
    ) -> (ValueRef, ValueRef) {
        use crate::types::{IntAnnotation, IntSignedness};
        let ann = Annotation::Int(IntAnnotation {
            bit_width: bits,
            signedness: IntSignedness::Signed,
        });
        let primary = self.push_inst_with_secondary(
            Op::SMulWithOverflow(a.into(), b.into(), bits),
            Type::Int,
            Type::Bool,
            origin,
            Some(ann),
            None,
        );
        let secondary = ValueRef::inst_secondary_result(primary.index());
        (primary, secondary)
    }

    /// Unsigned multiplication with overflow detection. Returns (wrapping_product: Int, overflow: Bool).
    pub fn umul_with_overflow(
        &mut self,
        a: Operand,
        b: Operand,
        bits: u32,
        origin: Origin,
    ) -> (ValueRef, ValueRef) {
        use crate::types::{IntAnnotation, IntSignedness};
        let ann = Annotation::Int(IntAnnotation {
            bit_width: bits,
            signedness: IntSignedness::Unsigned,
        });
        let primary = self.push_inst_with_secondary(
            Op::UMulWithOverflow(a.into(), b.into(), bits),
            Type::Int,
            Type::Bool,
            origin,
            Some(ann),
            None,
        );
        let secondary = ValueRef::inst_secondary_result(primary.index());
        (primary, secondary)
    }

    // ── Memory ──

    /// Load from pointer. `bytes` is the access width in bytes. Takes mem token input.
    /// Load is a MemoryUse — it does not produce a new mem token.
    /// Allocate stack slot of n bytes.
    pub fn stack_slot(&mut self, bytes: u32, origin: Origin) -> ValueRef {
        self.push_inst(Op::StackSlot(bytes), Type::Ptr(0), None, origin, None)
    }

    /// Memory copy (non-overlapping): memcpy semantics.
    pub fn mem_copy(
        &mut self,
        dst: Operand,
        src: Operand,
        count: Operand,
        mem: Operand,
        origin: Origin,
    ) -> ValueRef {
        self.push_inst(
            Op::MemCopy(dst.into(), src.into(), count.into(), mem.into()),
            Type::Mem,
            None,
            origin,
            None,
        )
    }

    /// Memory move (may overlap): memmove semantics.
    pub fn mem_move(
        &mut self,
        dst: Operand,
        src: Operand,
        count: Operand,
        mem: Operand,
        origin: Origin,
    ) -> ValueRef {
        self.push_inst(
            Op::MemMove(dst.into(), src.into(), count.into(), mem.into()),
            Type::Mem,
            None,
            origin,
            None,
        )
    }

    /// Memory set: memset semantics.
    pub fn mem_set(
        &mut self,
        dst: Operand,
        val: Operand,
        count: Operand,
        mem: Operand,
        origin: Origin,
    ) -> ValueRef {
        self.push_inst(
            Op::MemSet(dst.into(), val, count.into(), mem.into()),
            Type::Mem,
            None,
            origin,
            None,
        )
    }

    // ── Atomic memory operations ──

    /// Atomic load from pointer. Returns (mem_out, data_value).
    pub fn load_atomic(
        &mut self,
        ptr: Operand,
        ty: Type,
        ordering: MemoryOrdering,
        mem: Operand,
        ann: Option<Annotation>,
        origin: Origin,
    ) -> (ValueRef, ValueRef) {
        let primary = self.push_inst_with_secondary(
            Op::LoadAtomic(ptr.into(), ordering, mem.into()),
            Type::Mem,
            ty,
            origin,
            None,
            ann,
        );
        let secondary = ValueRef::inst_secondary_result(primary.index());
        (primary, secondary)
    }

    /// Atomic store value to pointer. Returns mem token.
    pub fn store_atomic(
        &mut self,
        val: Operand,
        ptr: Operand,
        ordering: MemoryOrdering,
        mem: Operand,
        origin: Origin,
    ) -> ValueRef {
        self.push_inst(
            Op::StoreAtomic(val, ptr.into(), ordering, mem.into()),
            Type::Mem,
            None,
            origin,
            None,
        )
    }

    /// Atomic read-modify-write. Returns (mem_out, old_value).
    #[allow(clippy::too_many_arguments)]
    pub fn atomic_rmw(
        &mut self,
        op: AtomicRmwOp,
        ptr: Operand,
        val: Operand,
        ty: Type,
        ordering: MemoryOrdering,
        mem: Operand,
        ann: Option<Annotation>,
        origin: Origin,
    ) -> (ValueRef, ValueRef) {
        let primary = self.push_inst_with_secondary(
            Op::AtomicRmw(op, ptr.into(), val, ordering, mem.into()),
            Type::Mem,
            ty,
            origin,
            None,
            ann,
        );
        let secondary = ValueRef::inst_secondary_result(primary.index());
        (primary, secondary)
    }

    /// Atomic compare-and-exchange. Returns (mem_out, old_value).
    #[allow(clippy::too_many_arguments)]
    pub fn atomic_cmpxchg(
        &mut self,
        ptr: Operand,
        expected: Operand,
        desired: Operand,
        ty: Type,
        success_ord: MemoryOrdering,
        failure_ord: MemoryOrdering,
        mem: Operand,
        ann: Option<Annotation>,
        origin: Origin,
    ) -> (ValueRef, ValueRef) {
        let primary = self.push_inst_with_secondary(
            Op::AtomicCmpXchg(
                ptr.into(),
                expected,
                desired,
                success_ord,
                failure_ord,
                mem.into(),
            ),
            Type::Mem,
            ty,
            origin,
            None,
            ann,
        );
        let secondary = ValueRef::inst_secondary_result(primary.index());
        (primary, secondary)
    }

    /// Memory fence. Returns mem token.
    pub fn fence(&mut self, ordering: MemoryOrdering, mem: MemOperand, origin: Origin) -> MemValue {
        let v = self.push_inst(Op::Fence(ordering, mem), Type::Mem, None, origin, None);
        MemValue::new(v, self.func)
    }

    // ── Symbol ──

    /// Load the address of a symbol (function or static data).
    pub fn symbol_addr(&mut self, sym: SymbolId, origin: Origin) -> PtrValue {
        let v = self.push_inst(Op::SymbolAddr(sym), Type::Ptr(0), None, origin, None);
        PtrValue::new(v, self.func)
    }

    // ── Call ──

    /// Call function with arguments. Takes mem token.
    /// For void calls, returns mem token only.
    /// For non-void calls, returns (mem_out, data_value).
    #[allow(clippy::too_many_arguments)]
    pub fn call(
        &mut self,
        callee: Operand,
        args: Vec<Operand>,
        ret_ty: Type,
        mem: Operand,
        ann: Option<Annotation>,
        origin: Origin,
    ) -> (ValueRef, Option<ValueRef>) {
        if ret_ty == Type::Unit {
            let primary = self.push_inst(
                Op::Call(callee.into(), args, mem.into()),
                Type::Mem,
                None,
                origin,
                None,
            );
            (primary, None)
        } else {
            let primary = self.push_inst_with_secondary(
                Op::Call(callee.into(), args, mem.into()),
                Type::Mem,
                ret_ty,
                origin,
                None,
                ann,
            );
            let secondary = ValueRef::inst_secondary_result(primary.index());
            (primary, Some(secondary))
        }
    }

    // ── Type conversion ──

    /// Bitcast (reinterpret bits).
    pub fn bitcast(
        &mut self,
        val: Operand,
        ty: Type,
        ann: Option<Annotation>,
        origin: Origin,
    ) -> ValueRef {
        self.push_inst(Op::Bitcast(val), ty, None, origin, ann)
    }

    /// Sign-extend to n bits.
    pub fn sext(&mut self, val: IntOperand, bits: u32, origin: Origin) -> IntValue {
        use crate::types::{IntAnnotation, IntSignedness};
        let ann = Annotation::Int(IntAnnotation {
            bit_width: bits,
            signedness: IntSignedness::Signed,
        });
        let v = self.push_inst(Op::Sext(val, bits), Type::Int, None, origin, Some(ann));
        IntValue::new(v, self.func)
    }

    /// Zero-extend to n bits.
    pub fn zext(&mut self, val: IntOperand, bits: u32, origin: Origin) -> IntValue {
        use crate::types::{IntAnnotation, IntSignedness};
        let ann = Annotation::Int(IntAnnotation {
            bit_width: bits,
            signedness: IntSignedness::Unsigned,
        });
        let v = self.push_inst(Op::Zext(val, bits), Type::Int, None, origin, Some(ann));
        IntValue::new(v, self.func)
    }

    /// Float to signed integer (truncation toward zero).
    pub fn fp_to_si(&mut self, val: FloatOperand, bits: u32, origin: Origin) -> IntValue {
        use crate::types::{IntAnnotation, IntSignedness};
        let ann = Annotation::Int(IntAnnotation {
            bit_width: bits,
            signedness: IntSignedness::Signed,
        });
        let v = self.push_inst(Op::FpToSi(val), Type::Int, None, origin, Some(ann));
        IntValue::new(v, self.func)
    }

    /// Float to unsigned integer (truncation toward zero).
    pub fn fp_to_ui(&mut self, val: FloatOperand, bits: u32, origin: Origin) -> IntValue {
        use crate::types::{IntAnnotation, IntSignedness};
        let ann = Annotation::Int(IntAnnotation {
            bit_width: bits,
            signedness: IntSignedness::Unsigned,
        });
        let v = self.push_inst(Op::FpToUi(val), Type::Int, None, origin, Some(ann));
        IntValue::new(v, self.func)
    }

    /// Signed integer to float.
    pub fn si_to_fp(&mut self, val: IntOperand, ft: FloatType, origin: Origin) -> FloatValue {
        let v = self.push_inst(Op::SiToFp(val, ft), Type::Float(ft), None, origin, None);
        FloatValue::new(v, self.func)
    }

    /// Unsigned integer to float.
    pub fn ui_to_fp(&mut self, val: IntOperand, ft: FloatType, origin: Origin) -> FloatValue {
        let v = self.push_inst(Op::UiToFp(val, ft), Type::Float(ft), None, origin, None);
        FloatValue::new(v, self.func)
    }

    /// Float-to-float conversion (widen or narrow).
    pub fn fp_convert(&mut self, val: FloatOperand, ft: FloatType, origin: Origin) -> FloatValue {
        let v = self.push_inst(Op::FpConvert(val), Type::Float(ft), None, origin, None);
        FloatValue::new(v, self.func)
    }

    // ── Pointer operations ──

    /// Pointer addition (preserves provenance).
    pub fn ptradd(
        &mut self,
        ptr: Operand,
        offset: Operand,
        addr_space: u32,
        origin: Origin,
    ) -> ValueRef {
        self.push_inst(
            Op::PtrAdd(ptr.into(), offset.into()),
            Type::Ptr(addr_space),
            None,
            origin,
            None,
        )
    }

    /// Pointer difference (same allocation).
    pub fn ptrdiff(&mut self, a: PtrOperand, b: PtrOperand, bits: u32, origin: Origin) -> IntValue {
        use crate::types::{IntAnnotation, IntSignedness};
        let ann = Annotation::Int(IntAnnotation {
            bit_width: bits,
            signedness: IntSignedness::Signed,
        });
        let v = self.push_inst(Op::PtrDiff(a, b), Type::Int, None, origin, Some(ann));
        IntValue::new(v, self.func)
    }

    /// Pointer to integer with provenance capture.
    pub fn ptrtoint(&mut self, ptr: PtrOperand, bits: u32, origin: Origin) -> IntValue {
        use crate::types::{IntAnnotation, IntSignedness};
        let ann = Annotation::Int(IntAnnotation {
            bit_width: bits,
            signedness: IntSignedness::Unsigned,
        });
        let v = self.push_inst(Op::PtrToInt(ptr), Type::Int, None, origin, Some(ann));
        IntValue::new(v, self.func)
    }

    /// Pointer to address (discard provenance).
    pub fn ptrtoaddr(&mut self, ptr: PtrOperand, bits: u32, origin: Origin) -> IntValue {
        use crate::types::{IntAnnotation, IntSignedness};
        let ann = Annotation::Int(IntAnnotation {
            bit_width: bits,
            signedness: IntSignedness::Unsigned,
        });
        let v = self.push_inst(Op::PtrToAddr(ptr), Type::Int, None, origin, Some(ann));
        IntValue::new(v, self.func)
    }

    /// Integer to pointer (no valid provenance).
    pub fn inttoptr(&mut self, val: IntOperand, addr_space: u32, origin: Origin) -> PtrValue {
        let v = self.push_inst(Op::IntToPtr(val), Type::Ptr(addr_space), None, origin, None);
        PtrValue::new(v, self.func)
    }

    // ── Aggregate operations ──

    /// Extract value from struct/array at indices path.
    pub fn extract_value(
        &mut self,
        agg: Operand,
        indices: Vec<u32>,
        result_ty: Type,
        ann: Option<Annotation>,
        origin: Origin,
    ) -> ValueRef {
        self.push_inst(Op::ExtractValue(agg, indices), result_ty, None, origin, ann)
    }

    /// Insert value into struct/array at indices path.
    pub fn insert_value(
        &mut self,
        agg: Operand,
        val: Operand,
        indices: Vec<u32>,
        ann: Option<Annotation>,
        origin: Origin,
    ) -> ValueRef {
        // Result type is same as agg type
        let agg_ty = self.value_type(agg.value).cloned().unwrap_or(Type::Unit);
        self.push_inst(
            Op::InsertValue(agg, val, indices),
            agg_ty,
            None,
            origin,
            ann,
        )
    }

    // ── Terminators ──

    /// Return from function. Takes mem token output.
    pub fn ret(&mut self, val: Option<Operand>, mem: MemOperand, origin: Origin) -> ValueRef {
        let ty = self.func.ret_ty.clone().unwrap_or(Type::Unit);
        self.push_inst(Op::Ret(val, mem), ty, None, origin, None)
    }

    /// Unconditional branch with block arguments.
    pub fn br(&mut self, target: BlockRef, args: Vec<Operand>, origin: Origin) -> ValueRef {
        self.push_inst(Op::Br(target, args), Type::Unit, None, origin, None)
    }

    /// Conditional branch.
    pub fn brif(
        &mut self,
        cond: Operand,
        then_block: BlockRef,
        then_args: Vec<Operand>,
        else_block: BlockRef,
        else_args: Vec<Operand>,
        origin: Origin,
    ) -> ValueRef {
        self.push_inst(
            Op::BrIf(cond.into(), then_block, then_args, else_block, else_args),
            Type::Unit,
            None,
            origin,
            None,
        )
    }

    /// Loop backedge.
    pub fn continue_(&mut self, values: Vec<Operand>, origin: Origin) -> ValueRef {
        self.push_inst(Op::Continue(values), Type::Unit, None, origin, None)
    }

    /// Exit region with values.
    pub fn region_yield(&mut self, values: Vec<Operand>, origin: Origin) -> ValueRef {
        self.push_inst(Op::RegionYield(values), Type::Unit, None, origin, None)
    }

    /// Unreachable: indicates control flow should never reach this point.
    pub fn unreachable(&mut self, origin: Origin) -> ValueRef {
        self.push_inst(Op::Unreachable, Type::Unit, None, origin, None)
    }

    /// Trap: unconditionally abort execution.
    pub fn trap(&mut self, origin: Origin) -> ValueRef {
        self.push_inst(Op::Trap, Type::Unit, None, origin, None)
    }

    /// Returns `true` if the current block already ends with a terminator.
    pub fn current_block_is_terminated(&self) -> bool {
        let Some(bb_ref) = self.current_block else {
            return false;
        };
        let bb = &self.func.blocks[bb_ref.index() as usize];
        if bb.inst_count == 0 {
            return false;
        }
        let last_idx = (bb.inst_start + bb.inst_count - 1) as usize;
        let last_op = &self.func.instructions[last_idx].op;
        matches!(
            last_op,
            Op::Ret(..)
                | Op::Br(_, _)
                | Op::BrIf(..)
                | Op::Continue(_)
                | Op::RegionYield(_)
                | Op::Unreachable
                | Op::Trap
        )
    }
}
