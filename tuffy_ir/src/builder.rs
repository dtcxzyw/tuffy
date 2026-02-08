//! Builder API for constructing tuffy IR.
//!
//! Origin is mandatory on every instruction — enforced at compile time.

use crate::function::{BasicBlock, Function};
use crate::instruction::{Instruction, Op, Origin};
use crate::types::Type;
use crate::value::{BlockRef, ValueRef};

/// Builder for constructing a function's IR.
pub struct Builder<'a> {
    func: &'a mut Function,
    current_block: Option<BlockRef>,
}

impl<'a> Builder<'a> {
    pub fn new(func: &'a mut Function) -> Self {
        Self {
            func,
            current_block: None,
        }
    }

    /// Create a new basic block and return its reference.
    pub fn create_block(&mut self) -> BlockRef {
        let idx = self.func.blocks.len() as u32;
        self.func.blocks.push(BasicBlock {
            inst_start: self.func.instructions.len() as u32,
            inst_count: 0,
        });
        BlockRef(idx)
    }

    /// Set the current block for subsequent instructions.
    pub fn switch_to_block(&mut self, block: BlockRef) {
        self.current_block = Some(block);
    }

    fn push_inst(&mut self, inst: Instruction) -> ValueRef {
        let idx = self.func.instructions.len() as u32;
        self.func.instructions.push(inst);
        if let Some(bb) = self.current_block {
            self.func.blocks[bb.0 as usize].inst_count += 1;
        }
        ValueRef(idx)
    }

    /// Create a function parameter reference.
    pub fn param(&mut self, index: u32, ty: Type, origin: Origin) -> ValueRef {
        self.push_inst(Instruction {
            op: Op::Param(index),
            ty,
            origin,
        })
    }

    /// Integer constant.
    pub fn iconst(&mut self, val: i64, origin: Origin) -> ValueRef {
        self.push_inst(Instruction {
            op: Op::Const(val),
            ty: Type::Int,
            origin,
        })
    }

    /// Integer addition.
    pub fn add(&mut self, a: ValueRef, b: ValueRef, origin: Origin) -> ValueRef {
        self.push_inst(Instruction {
            op: Op::Add(a, b),
            ty: Type::Int,
            origin,
        })
    }

    /// Integer subtraction.
    pub fn sub(&mut self, a: ValueRef, b: ValueRef, origin: Origin) -> ValueRef {
        self.push_inst(Instruction {
            op: Op::Sub(a, b),
            ty: Type::Int,
            origin,
        })
    }

    /// Integer multiplication.
    pub fn mul(&mut self, a: ValueRef, b: ValueRef, origin: Origin) -> ValueRef {
        self.push_inst(Instruction {
            op: Op::Mul(a, b),
            ty: Type::Int,
            origin,
        })
    }

    /// Assert signed extension constraint.
    pub fn assert_sext(&mut self, val: ValueRef, bits: u32, origin: Origin) -> ValueRef {
        self.push_inst(Instruction {
            op: Op::AssertSext(val, bits),
            ty: Type::Int,
            origin,
        })
    }

    /// Assert zero extension constraint.
    pub fn assert_zext(&mut self, val: ValueRef, bits: u32, origin: Origin) -> ValueRef {
        self.push_inst(Instruction {
            op: Op::AssertZext(val, bits),
            ty: Type::Int,
            origin,
        })
    }

    /// Return from function.
    pub fn ret(&mut self, val: Option<ValueRef>, origin: Origin) -> ValueRef {
        let ty = self.func.ret_ty.clone().unwrap_or(Type::Int);
        self.push_inst(Instruction {
            op: Op::Ret(val),
            ty,
            origin,
        })
    }
}
