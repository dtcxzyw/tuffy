//! Function and basic block definitions with hierarchical CFG.
//!
//! The CFG is organized as a tree of SESE (Single Entry, Single Exit) regions.
//! Each region contains an ordered sequence of basic blocks and child regions.
//! Cross-region value references use implicit capture (VPlan style).

use crate::instruction::Instruction;
use crate::module::SymbolId;
use crate::types::{Annotation, Type};
use crate::value::{BlockRef, RegionRef, ValueRef};

/// A block argument (replaces PHI nodes).
#[derive(Debug, Clone)]
pub struct BlockArg {
    pub ty: Type,
}

/// A basic block containing a sequence of instructions.
#[derive(Debug)]
pub struct BasicBlock {
    /// Which region this block belongs to.
    pub parent_region: RegionRef,
    /// Start index into the function's block_args arena.
    pub arg_start: u32,
    /// Number of block arguments.
    pub arg_count: u32,
    /// Range into the function's instruction arena.
    pub inst_start: u32,
    pub inst_count: u32,
}

/// Kind of SESE region.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RegionKind {
    /// Top-level function region.
    Function,
    /// Loop region (backedge via Continue).
    Loop,
    /// Generic SESE region.
    Plain,
}

/// A node in the CFG: either a block or a nested region.
#[derive(Debug, Clone)]
pub enum CfgNode {
    Block(BlockRef),
    Region(RegionRef),
}

/// A SESE region in the hierarchical CFG.
#[derive(Debug)]
pub struct Region {
    pub kind: RegionKind,
    pub parent: Option<RegionRef>,
    pub entry_block: BlockRef,
    /// Ordered sequence of blocks and child regions.
    pub children: Vec<CfgNode>,
}

/// A function in the tuffy IR.
#[derive(Debug)]
pub struct Function {
    pub name: SymbolId,
    pub params: Vec<Type>,
    /// Annotations on function parameters (ABI-level caller guarantees).
    pub param_annotations: Vec<Option<Annotation>>,
    /// Optional source-level names for parameters (for display only).
    /// Indexed by ABI parameter index. `None` means no name available.
    pub param_names: Vec<Option<SymbolId>>,
    pub ret_ty: Option<Type>,
    /// Annotation on the return type (ABI-level callee guarantee).
    pub ret_annotation: Option<Annotation>,
    /// Instruction arena: contiguous storage.
    pub instructions: Vec<Instruction>,
    /// Basic blocks indexing into the instruction arena.
    pub blocks: Vec<BasicBlock>,
    /// Region arena.
    pub regions: Vec<Region>,
    /// Block argument arena.
    pub block_args: Vec<BlockArg>,
    /// Root region (always a Function region).
    pub root_region: RegionRef,
}

impl Function {
    pub fn new(
        name: SymbolId,
        params: Vec<Type>,
        param_annotations: Vec<Option<Annotation>>,
        param_names: Vec<Option<SymbolId>>,
        ret_ty: Option<Type>,
        ret_annotation: Option<Annotation>,
    ) -> Self {
        let param_count = params.len();
        let mut param_anns = param_annotations;
        // Pad with None if caller provided fewer annotations than params.
        param_anns.resize(param_count, None);
        let mut names = param_names;
        names.resize(param_count, None);
        Self {
            name,
            params,
            param_annotations: param_anns,
            param_names: names,
            ret_ty,
            ret_annotation,
            instructions: Vec::new(),
            blocks: Vec::new(),
            regions: Vec::new(),
            block_args: Vec::new(),
            root_region: RegionRef(0),
        }
    }

    /// Get an instruction by index.
    pub fn inst(&self, index: u32) -> &Instruction {
        &self.instructions[index as usize]
    }

    /// Get a basic block by reference.
    pub fn block(&self, r: BlockRef) -> &BasicBlock {
        &self.blocks[r.index() as usize]
    }

    /// Get a region by reference.
    pub fn region(&self, r: RegionRef) -> &Region {
        &self.regions[r.index() as usize]
    }

    /// Iterate instructions in a basic block.
    pub fn block_insts(&self, r: BlockRef) -> &[Instruction] {
        let bb = self.block(r);
        let start = bb.inst_start as usize;
        let end = start + bb.inst_count as usize;
        &self.instructions[start..end]
    }

    /// Reference to the entry block (entry block of root region).
    pub fn entry_block(&self) -> BlockRef {
        self.regions[self.root_region.index() as usize].entry_block
    }

    /// Get block arguments for a block.
    pub fn block_args(&self, r: BlockRef) -> &[BlockArg] {
        let bb = self.block(r);
        let start = bb.arg_start as usize;
        let end = start + bb.arg_count as usize;
        &self.block_args[start..end]
    }

    /// Get ValueRefs for block arguments of a block.
    pub fn block_arg_values(&self, r: BlockRef) -> Vec<ValueRef> {
        let bb = self.block(r);
        (0..bb.arg_count)
            .map(|i| ValueRef::block_arg(bb.arg_start + i))
            .collect()
    }

    /// Iterate (ValueRef, &Instruction) pairs in a basic block.
    pub fn block_insts_with_values(
        &self,
        r: BlockRef,
    ) -> impl Iterator<Item = (ValueRef, &Instruction)> {
        let bb = self.block(r);
        let start = bb.inst_start;
        self.block_insts(r)
            .iter()
            .enumerate()
            .map(move |(i, inst)| (ValueRef::inst_result(start + i as u32), inst))
    }

    /// Get the type of a value (instruction result or block argument).
    /// For secondary results, returns the secondary_ty of the instruction.
    pub fn value_type(&self, v: ValueRef) -> Option<&Type> {
        if v.is_block_arg() {
            self.block_args.get(v.index() as usize).map(|ba| &ba.ty)
        } else if v.is_secondary_result() {
            self.instructions
                .get(v.inst_index() as usize)
                .and_then(|i| i.secondary_ty.as_ref())
        } else {
            self.instructions.get(v.index() as usize).map(|i| &i.ty)
        }
    }
}
