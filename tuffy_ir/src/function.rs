//! Function and basic block definitions with arena storage.

use crate::instruction::Instruction;
use crate::types::Type;
use crate::value::{BlockRef, InstRef};

/// A basic block containing a sequence of instructions.
#[derive(Debug)]
pub struct BasicBlock {
    /// Range into the function's instruction arena.
    pub inst_start: u32,
    pub inst_count: u32,
}

/// A function in the tuffy IR.
#[derive(Debug)]
pub struct Function {
    pub name: String,
    pub params: Vec<Type>,
    pub ret_ty: Option<Type>,
    /// Instruction arena: contiguous storage.
    pub instructions: Vec<Instruction>,
    /// Basic blocks indexing into the instruction arena.
    pub blocks: Vec<BasicBlock>,
}

impl Function {
    pub fn new(name: impl Into<String>, params: Vec<Type>, ret_ty: Option<Type>) -> Self {
        Self {
            name: name.into(),
            params,
            ret_ty,
            instructions: Vec::new(),
            blocks: Vec::new(),
        }
    }

    /// Get an instruction by reference.
    pub fn inst(&self, r: InstRef) -> &Instruction {
        &self.instructions[r.0 as usize]
    }

    /// Get a basic block by reference.
    pub fn block(&self, r: BlockRef) -> &BasicBlock {
        &self.blocks[r.0 as usize]
    }

    /// Iterate instructions in a basic block.
    pub fn block_insts(&self, r: BlockRef) -> &[Instruction] {
        let bb = &self.blocks[r.0 as usize];
        let start = bb.inst_start as usize;
        let end = start + bb.inst_count as usize;
        &self.instructions[start..end]
    }
}
