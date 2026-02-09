//! Builder API for constructing tuffy IR.
//!
//! Origin is mandatory on every instruction — enforced at compile time.

use crate::function::{BasicBlock, BlockArg, CfgNode, Function, Region, RegionKind};
use crate::instruction::{AtomicRmwOp, ICmpOp, Instruction, Op, Operand, Origin};
use crate::types::{Annotation, MemoryOrdering, Type};
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

    /// Add a block argument and return its ValueRef.
    pub fn add_block_arg(&mut self, block: BlockRef, ty: Type) -> ValueRef {
        let arg_idx = self.func.block_args.len() as u32;
        self.func.block_args.push(BlockArg { ty });
        self.func.blocks[block.index() as usize].arg_count += 1;
        ValueRef::block_arg(arg_idx)
    }

    // ── Instruction emission ──

    fn push_inst(&mut self, op: Op, ty: Type, origin: Origin, ann: Option<Annotation>) -> ValueRef {
        let idx = self.func.instructions.len() as u32;
        self.func.instructions.push(Instruction {
            op,
            ty,
            origin,
            result_annotation: ann,
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
        self.push_inst(Op::Param(index), ty, origin, ann)
    }

    /// Integer constant.
    pub fn iconst(&mut self, val: i64, origin: Origin) -> ValueRef {
        self.push_inst(Op::Const(val), Type::Int, origin, None)
    }

    /// Integer addition.
    pub fn add(
        &mut self,
        a: Operand,
        b: Operand,
        ann: Option<Annotation>,
        origin: Origin,
    ) -> ValueRef {
        self.push_inst(Op::Add(a, b), Type::Int, origin, ann)
    }

    /// Integer subtraction.
    pub fn sub(
        &mut self,
        a: Operand,
        b: Operand,
        ann: Option<Annotation>,
        origin: Origin,
    ) -> ValueRef {
        self.push_inst(Op::Sub(a, b), Type::Int, origin, ann)
    }

    /// Integer multiplication.
    pub fn mul(
        &mut self,
        a: Operand,
        b: Operand,
        ann: Option<Annotation>,
        origin: Origin,
    ) -> ValueRef {
        self.push_inst(Op::Mul(a, b), Type::Int, origin, ann)
    }

    /// Signed integer division (poison on division by zero).
    pub fn sdiv(
        &mut self,
        a: Operand,
        b: Operand,
        ann: Option<Annotation>,
        origin: Origin,
    ) -> ValueRef {
        self.push_inst(Op::SDiv(a, b), Type::Int, origin, ann)
    }

    /// Unsigned integer division (poison on division by zero).
    pub fn udiv(
        &mut self,
        a: Operand,
        b: Operand,
        ann: Option<Annotation>,
        origin: Origin,
    ) -> ValueRef {
        self.push_inst(Op::UDiv(a, b), Type::Int, origin, ann)
    }

    pub fn srem(
        &mut self,
        a: Operand,
        b: Operand,
        ann: Option<Annotation>,
        origin: Origin,
    ) -> ValueRef {
        self.push_inst(Op::SRem(a, b), Type::Int, origin, ann)
    }

    pub fn urem(
        &mut self,
        a: Operand,
        b: Operand,
        ann: Option<Annotation>,
        origin: Origin,
    ) -> ValueRef {
        self.push_inst(Op::URem(a, b), Type::Int, origin, ann)
    }

    /// Bitwise AND.
    pub fn and(
        &mut self,
        a: Operand,
        b: Operand,
        ann: Option<Annotation>,
        origin: Origin,
    ) -> ValueRef {
        self.push_inst(Op::And(a, b), Type::Int, origin, ann)
    }

    /// Bitwise OR.
    pub fn or(
        &mut self,
        a: Operand,
        b: Operand,
        ann: Option<Annotation>,
        origin: Origin,
    ) -> ValueRef {
        self.push_inst(Op::Or(a, b), Type::Int, origin, ann)
    }

    /// Bitwise XOR.
    pub fn xor(
        &mut self,
        a: Operand,
        b: Operand,
        ann: Option<Annotation>,
        origin: Origin,
    ) -> ValueRef {
        self.push_inst(Op::Xor(a, b), Type::Int, origin, ann)
    }

    /// Left shift (poison if shift amount is negative).
    pub fn shl(
        &mut self,
        a: Operand,
        b: Operand,
        ann: Option<Annotation>,
        origin: Origin,
    ) -> ValueRef {
        self.push_inst(Op::Shl(a, b), Type::Int, origin, ann)
    }

    /// Logical right shift (poison if shift amount is negative).
    pub fn lshr(
        &mut self,
        a: Operand,
        b: Operand,
        ann: Option<Annotation>,
        origin: Origin,
    ) -> ValueRef {
        self.push_inst(Op::Lshr(a, b), Type::Int, origin, ann)
    }

    /// Arithmetic right shift (poison if shift amount is negative).
    pub fn ashr(
        &mut self,
        a: Operand,
        b: Operand,
        ann: Option<Annotation>,
        origin: Origin,
    ) -> ValueRef {
        self.push_inst(Op::Ashr(a, b), Type::Int, origin, ann)
    }

    // ── Floating point arithmetic ──

    /// Floating point addition.
    pub fn fadd(&mut self, a: Operand, b: Operand, ty: Type, origin: Origin) -> ValueRef {
        self.push_inst(Op::FAdd(a, b), ty, origin, None)
    }

    /// Floating point subtraction.
    pub fn fsub(&mut self, a: Operand, b: Operand, ty: Type, origin: Origin) -> ValueRef {
        self.push_inst(Op::FSub(a, b), ty, origin, None)
    }

    /// Floating point multiplication.
    pub fn fmul(&mut self, a: Operand, b: Operand, ty: Type, origin: Origin) -> ValueRef {
        self.push_inst(Op::FMul(a, b), ty, origin, None)
    }

    /// Floating point division.
    pub fn fdiv(&mut self, a: Operand, b: Operand, ty: Type, origin: Origin) -> ValueRef {
        self.push_inst(Op::FDiv(a, b), ty, origin, None)
    }

    /// Copy sign: magnitude from first operand, sign from second.
    pub fn copysign(&mut self, mag: Operand, sign: Operand, ty: Type, origin: Origin) -> ValueRef {
        self.push_inst(Op::CopySign(mag, sign), ty, origin, None)
    }

    /// Floating point negation.
    pub fn fneg(&mut self, val: Operand, ty: Type, origin: Origin) -> ValueRef {
        self.push_inst(Op::FNeg(val), ty, origin, None)
    }

    /// Floating point absolute value.
    pub fn fabs(&mut self, val: Operand, ty: Type, origin: Origin) -> ValueRef {
        self.push_inst(Op::FAbs(val), ty, origin, None)
    }

    // ── Comparison ──

    /// Integer comparison.
    pub fn icmp(&mut self, op: ICmpOp, a: Operand, b: Operand, origin: Origin) -> ValueRef {
        self.push_inst(Op::ICmp(op, a, b), Type::Int, origin, None)
    }

    // ── Memory ──

    /// Load from pointer.
    pub fn load(
        &mut self,
        ptr: Operand,
        ty: Type,
        ann: Option<Annotation>,
        origin: Origin,
    ) -> ValueRef {
        self.push_inst(Op::Load(ptr), ty, origin, ann)
    }

    /// Store value to pointer.
    pub fn store(&mut self, val: Operand, ptr: Operand, origin: Origin) -> ValueRef {
        self.push_inst(Op::Store(val, ptr), Type::Int, origin, None)
    }

    /// Allocate stack slot of n bytes.
    pub fn stack_slot(&mut self, bytes: u32, origin: Origin) -> ValueRef {
        self.push_inst(Op::StackSlot(bytes), Type::Ptr(0), origin, None)
    }

    // ── Atomic memory operations ──

    /// Atomic load from pointer.
    pub fn load_atomic(
        &mut self,
        ptr: Operand,
        ty: Type,
        ordering: MemoryOrdering,
        origin: Origin,
    ) -> ValueRef {
        self.push_inst(Op::LoadAtomic(ptr, ordering), ty, origin, None)
    }

    /// Atomic store value to pointer.
    pub fn store_atomic(
        &mut self,
        val: Operand,
        ptr: Operand,
        ordering: MemoryOrdering,
        origin: Origin,
    ) -> ValueRef {
        self.push_inst(Op::StoreAtomic(val, ptr, ordering), Type::Int, origin, None)
    }

    /// Atomic read-modify-write.
    pub fn atomic_rmw(
        &mut self,
        op: AtomicRmwOp,
        ptr: Operand,
        val: Operand,
        ty: Type,
        ordering: MemoryOrdering,
        origin: Origin,
    ) -> ValueRef {
        self.push_inst(Op::AtomicRmw(op, ptr, val, ordering), ty, origin, None)
    }

    /// Atomic compare-and-exchange. Returns the old value.
    #[allow(clippy::too_many_arguments)]
    pub fn atomic_cmpxchg(
        &mut self,
        ptr: Operand,
        expected: Operand,
        desired: Operand,
        ty: Type,
        success_ord: MemoryOrdering,
        failure_ord: MemoryOrdering,
        origin: Origin,
    ) -> ValueRef {
        self.push_inst(
            Op::AtomicCmpXchg(ptr, expected, desired, success_ord, failure_ord),
            ty,
            origin,
            None,
        )
    }

    /// Memory fence.
    pub fn fence(&mut self, ordering: MemoryOrdering, origin: Origin) -> ValueRef {
        self.push_inst(Op::Fence(ordering), Type::Int, origin, None)
    }

    // ── Call ──

    /// Call function with arguments.
    pub fn call(
        &mut self,
        callee: Operand,
        args: Vec<Operand>,
        ret_ty: Type,
        ann: Option<Annotation>,
        origin: Origin,
    ) -> ValueRef {
        self.push_inst(Op::Call(callee, args), ret_ty, origin, ann)
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
        self.push_inst(Op::Bitcast(val), ty, origin, ann)
    }

    /// Sign-extend to n bits.
    pub fn sext(&mut self, val: Operand, bits: u32, origin: Origin) -> ValueRef {
        self.push_inst(Op::Sext(val, bits), Type::Int, origin, None)
    }

    /// Zero-extend to n bits.
    pub fn zext(&mut self, val: Operand, bits: u32, origin: Origin) -> ValueRef {
        self.push_inst(Op::Zext(val, bits), Type::Int, origin, None)
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
        self.push_inst(Op::PtrAdd(ptr, offset), Type::Ptr(addr_space), origin, None)
    }

    /// Pointer difference (same allocation).
    pub fn ptrdiff(&mut self, a: Operand, b: Operand, origin: Origin) -> ValueRef {
        self.push_inst(Op::PtrDiff(a, b), Type::Int, origin, None)
    }

    /// Pointer to integer with provenance capture.
    pub fn ptrtoint(&mut self, ptr: Operand, origin: Origin) -> ValueRef {
        self.push_inst(Op::PtrToInt(ptr), Type::Int, origin, None)
    }

    /// Pointer to address (discard provenance).
    pub fn ptrtoaddr(&mut self, ptr: Operand, origin: Origin) -> ValueRef {
        self.push_inst(Op::PtrToAddr(ptr), Type::Int, origin, None)
    }

    /// Integer to pointer (no valid provenance).
    pub fn inttoptr(&mut self, val: Operand, addr_space: u32, origin: Origin) -> ValueRef {
        self.push_inst(Op::IntToPtr(val), Type::Ptr(addr_space), origin, None)
    }

    // ── Terminators ──

    /// Return from function.
    pub fn ret(&mut self, val: Option<Operand>, origin: Origin) -> ValueRef {
        let ty = self.func.ret_ty.clone().unwrap_or(Type::Int);
        self.push_inst(Op::Ret(val), ty, origin, None)
    }

    /// Unconditional branch with block arguments.
    pub fn br(&mut self, target: BlockRef, args: Vec<Operand>, origin: Origin) -> ValueRef {
        self.push_inst(Op::Br(target, args), Type::Int, origin, None)
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
            Op::BrIf(cond, then_block, then_args, else_block, else_args),
            Type::Int,
            origin,
            None,
        )
    }

    /// Loop backedge.
    pub fn continue_(&mut self, values: Vec<Operand>, origin: Origin) -> ValueRef {
        self.push_inst(Op::Continue(values), Type::Int, origin, None)
    }

    /// Exit region with values.
    pub fn region_yield(&mut self, values: Vec<Operand>, origin: Origin) -> ValueRef {
        self.push_inst(Op::RegionYield(values), Type::Int, origin, None)
    }

    /// Unreachable: indicates control flow should never reach this point.
    pub fn unreachable(&mut self, origin: Origin) -> ValueRef {
        self.push_inst(Op::Unreachable, Type::Int, origin, None)
    }

    /// Trap: unconditionally abort execution.
    pub fn trap(&mut self, origin: Origin) -> ValueRef {
        self.push_inst(Op::Trap, Type::Int, origin, None)
    }
}
