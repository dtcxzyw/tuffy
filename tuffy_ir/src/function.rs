//! Function and basic block definitions with hierarchical CFG.
//!
//! The CFG is organized as a tree of SESE (Single Entry, Single Exit) regions.
//! Each region contains an ordered sequence of basic blocks and child regions.
//! Cross-region value references use implicit capture (VPlan style).
//!
//! Instructions are stored in a pool (`InstPool`) and threaded into per-BB
//! doubly-linked lists, enabling O(1) insertion and removal anywhere.

use crate::instruction::Instruction;
use crate::module::SymbolId;
use crate::pool::{InstNode, InstPool, UseNode, UsePool};
use crate::types::{Annotation, Type};
use crate::value::{BlockRef, RegionRef, ValueRef};

/// A block argument (replaces PHI nodes).
#[derive(Debug, Clone)]
pub struct BlockArg {
    pub ty: Type,
    pub annotation: Option<Annotation>,
    /// Head of the use-list for this block argument.
    pub(crate) use_list_head: Option<u32>,
}

/// A basic block whose instructions form a doubly-linked list in the pool.
#[derive(Debug, Clone)]
pub struct BasicBlock {
    /// Which region this block belongs to.
    pub parent_region: RegionRef,
    /// Start index into the function's block_args arena.
    pub arg_start: u32,
    /// Number of block arguments.
    pub arg_count: u32,
    /// First instruction in this block (`None` if empty).
    pub first_inst: Option<u32>,
    /// Last instruction in this block (`None` if empty).
    pub last_inst: Option<u32>,
    /// Number of instructions in this block.
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
#[derive(Debug, Clone)]
pub struct Region {
    pub kind: RegionKind,
    pub parent: Option<RegionRef>,
    pub entry_block: BlockRef,
    /// Ordered sequence of blocks and child regions.
    pub children: Vec<CfgNode>,
}

/// A function in the tuffy IR.
#[derive(Debug, Clone)]
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
    /// Instruction pool (arena with linked-list threading).
    pub inst_pool: InstPool,
    /// Use-list pool (arena for def-use chain nodes).
    pub use_pool: UsePool,
    /// Basic blocks with linked-list heads into the instruction pool.
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
            inst_pool: InstPool::new(),
            use_pool: UsePool::new(),
            blocks: Vec::new(),
            regions: Vec::new(),
            block_args: Vec::new(),
            root_region: RegionRef(0),
        }
    }

    /// Get an instruction by pool index.
    pub fn inst(&self, index: u32) -> &Instruction {
        self.inst_pool.inst(index)
    }

    /// Get the instruction node (with linked-list metadata) by pool index.
    pub fn inst_node(&self, index: u32) -> &InstNode {
        self.inst_pool
            .get(index)
            .expect("invalid instruction index")
    }

    /// Get a basic block by reference.
    pub fn block(&self, r: BlockRef) -> &BasicBlock {
        &self.blocks[r.index() as usize]
    }

    /// Get a mutable basic block by reference.
    pub fn block_mut(&mut self, r: BlockRef) -> &mut BasicBlock {
        &mut self.blocks[r.index() as usize]
    }

    /// Get a region by reference.
    pub fn region(&self, r: RegionRef) -> &Region {
        &self.regions[r.index() as usize]
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

    /// Iterate instructions in a basic block (follows linked list).
    pub fn block_insts(&self, r: BlockRef) -> BlockInstIter<'_> {
        let bb = self.block(r);
        BlockInstIter {
            pool: &self.inst_pool,
            current: bb.first_inst,
        }
    }

    /// Iterate `(ValueRef, &Instruction)` pairs in a basic block.
    pub fn block_insts_with_values(&self, r: BlockRef) -> BlockInstValueIter<'_> {
        let bb = self.block(r);
        BlockInstValueIter {
            pool: &self.inst_pool,
            current: bb.first_inst,
        }
    }

    /// Get the type of a value (instruction result or block argument).
    pub fn value_type(&self, v: ValueRef) -> Option<&Type> {
        if v.is_block_arg() {
            self.block_args.get(v.index() as usize).map(|ba| &ba.ty)
        } else if v.is_secondary_result() {
            self.inst_pool
                .get(v.inst_index())
                .map(|n| &n.inst)
                .and_then(|i| i.secondary_ty.as_ref())
        } else {
            self.inst_pool.get(v.index()).map(|n| &n.inst.ty)
        }
    }

    // ── Mutation API ──

    /// Append an instruction to the end of a basic block.
    /// Returns the pool index (usable for `ValueRef::inst_result`).
    pub fn append_inst(&mut self, block: BlockRef, inst: Instruction) -> u32 {
        let bb = &self.blocks[block.index() as usize];
        let prev = bb.last_inst;

        let idx = self.inst_pool.alloc(InstNode {
            inst,
            prev,
            next: None,
            parent_block: block,
            use_list_head: None,
            secondary_use_list_head: None,
        });

        // Link previous tail → new node
        if let Some(prev_idx) = prev {
            self.inst_pool.get_mut(prev_idx).unwrap().next = Some(idx);
        }

        let bb = &mut self.blocks[block.index() as usize];
        if bb.first_inst.is_none() {
            bb.first_inst = Some(idx);
        }
        bb.last_inst = Some(idx);
        bb.inst_count += 1;

        // Register uses for the newly appended instruction
        self.register_uses(idx);
        idx
    }

    /// Insert an instruction before `before_idx` in its block.
    pub fn insert_inst_before(&mut self, before_idx: u32, inst: Instruction) -> u32 {
        let before_node = self.inst_pool.get(before_idx).expect("invalid before_idx");
        let block = before_node.parent_block;
        let prev = before_node.prev;

        let idx = self.inst_pool.alloc(InstNode {
            inst,
            prev,
            next: Some(before_idx),
            parent_block: block,
            use_list_head: None,
            secondary_use_list_head: None,
        });

        // Fix prev → new
        if let Some(prev_idx) = prev {
            self.inst_pool.get_mut(prev_idx).unwrap().next = Some(idx);
        } else {
            self.blocks[block.index() as usize].first_inst = Some(idx);
        }
        // Fix before → new
        self.inst_pool.get_mut(before_idx).unwrap().prev = Some(idx);
        self.blocks[block.index() as usize].inst_count += 1;

        // Register uses for the newly inserted instruction
        self.register_uses(idx);
        idx
    }

    /// Insert an instruction after `after_idx` in its block.
    pub fn insert_inst_after(&mut self, after_idx: u32, inst: Instruction) -> u32 {
        let after_node = self.inst_pool.get(after_idx).expect("invalid after_idx");
        let block = after_node.parent_block;
        let next = after_node.next;

        let idx = self.inst_pool.alloc(InstNode {
            inst,
            prev: Some(after_idx),
            next,
            parent_block: block,
            use_list_head: None,
            secondary_use_list_head: None,
        });

        // Fix after → new
        self.inst_pool.get_mut(after_idx).unwrap().next = Some(idx);
        // Fix next → new
        if let Some(next_idx) = next {
            self.inst_pool.get_mut(next_idx).unwrap().prev = Some(idx);
        } else {
            self.blocks[block.index() as usize].last_inst = Some(idx);
        }
        self.blocks[block.index() as usize].inst_count += 1;

        // Register uses for the newly inserted instruction
        self.register_uses(idx);
        idx
    }

    /// Remove an instruction from its block and free the pool slot.
    pub fn remove_inst(&mut self, index: u32) -> Option<Instruction> {
        // Unregister uses before freeing
        self.unregister_uses(index);

        let node = self.inst_pool.free(index)?;
        let block = node.parent_block;
        let bb = &mut self.blocks[block.index() as usize];

        // Unlink from doubly-linked list
        match (node.prev, node.next) {
            (Some(p), Some(n)) => {
                self.inst_pool.get_mut(p).unwrap().next = Some(n);
                self.inst_pool.get_mut(n).unwrap().prev = Some(p);
            }
            (Some(p), None) => {
                self.inst_pool.get_mut(p).unwrap().next = None;
                bb.last_inst = Some(p);
            }
            (None, Some(n)) => {
                self.inst_pool.get_mut(n).unwrap().prev = None;
                bb.first_inst = Some(n);
            }
            (None, None) => {
                bb.first_inst = None;
                bb.last_inst = None;
            }
        }
        bb.inst_count -= 1;
        Some(node.inst)
    }

    // ── Def-Use Chain API ──

    /// Register all value uses for an instruction that was just allocated.
    /// Call this after the instruction is fully linked into its block.
    pub(crate) fn register_uses(&mut self, inst_idx: u32) {
        let refs = self.inst_pool.get(inst_idx).unwrap().inst.op.value_refs();
        for vr in refs {
            let use_node = UseNode {
                user: inst_idx,
                next: None,
                prev: None,
            };
            let use_id = self.use_pool.alloc(use_node);
            self.prepend_use(vr, use_id);
        }
    }

    /// Unregister all value uses for an instruction about to be removed/freed.
    pub(crate) fn unregister_uses(&mut self, inst_idx: u32) {
        let node = match self.inst_pool.get(inst_idx) {
            Some(n) => n,
            None => return,
        };
        let refs = node.inst.op.value_refs();
        for vr in refs {
            self.remove_uses_by(vr, inst_idx);
        }
    }

    /// Prepend a use-list node to the head of a value's use-list.
    fn prepend_use(&mut self, value: ValueRef, use_id: u32) {
        let old_head = self.use_list_head(value);
        // Point the new node's next to the old head
        self.use_pool.get_mut(use_id).unwrap().next = old_head;
        self.use_pool.get_mut(use_id).unwrap().prev = None;
        // Update old head's prev
        if let Some(old) = old_head {
            self.use_pool.get_mut(old).unwrap().prev = Some(use_id);
        }
        // Set new head
        self.set_use_list_head(value, Some(use_id));
    }

    /// Remove all use-list entries for `value` whose `user` equals `inst_idx`.
    fn remove_uses_by(&mut self, value: ValueRef, inst_idx: u32) {
        let mut cur = self.use_list_head(value);
        while let Some(uid) = cur {
            let node = self.use_pool.get(uid).unwrap();
            let next = node.next;
            if node.user == inst_idx {
                self.unlink_use(value, uid);
                self.use_pool.free(uid);
            }
            cur = next;
        }
    }

    /// Unlink a use node from its value's doubly-linked use-list.
    fn unlink_use(&mut self, value: ValueRef, use_id: u32) {
        let node = self.use_pool.get(use_id).unwrap();
        let prev = node.prev;
        let next = node.next;
        match (prev, next) {
            (Some(p), Some(n)) => {
                self.use_pool.get_mut(p).unwrap().next = Some(n);
                self.use_pool.get_mut(n).unwrap().prev = Some(p);
            }
            (Some(p), None) => {
                self.use_pool.get_mut(p).unwrap().next = None;
            }
            (None, Some(n)) => {
                self.use_pool.get_mut(n).unwrap().prev = None;
                self.set_use_list_head(value, Some(n));
            }
            (None, None) => {
                self.set_use_list_head(value, None);
            }
        }
    }

    /// Get the head of the use-list for a value.
    fn use_list_head(&self, value: ValueRef) -> Option<u32> {
        if value.is_block_arg() {
            self.block_args
                .get(value.index() as usize)
                .and_then(|ba| ba.use_list_head)
        } else if value.is_secondary_result() {
            self.inst_pool
                .get(value.inst_index())
                .and_then(|n| n.secondary_use_list_head)
        } else {
            self.inst_pool
                .get(value.index())
                .and_then(|n| n.use_list_head)
        }
    }

    /// Set the head of the use-list for a value.
    fn set_use_list_head(&mut self, value: ValueRef, head: Option<u32>) {
        if value.is_block_arg() {
            if let Some(ba) = self.block_args.get_mut(value.index() as usize) {
                ba.use_list_head = head;
            }
        } else if value.is_secondary_result() {
            if let Some(n) = self.inst_pool.get_mut(value.inst_index()) {
                n.secondary_use_list_head = head;
            }
        } else if let Some(n) = self.inst_pool.get_mut(value.index()) {
            n.use_list_head = head;
        }
    }

    /// Iterate all uses of a value (instruction result or block argument).
    pub fn uses_of(&self, value: ValueRef) -> UseIter<'_> {
        UseIter {
            pool: &self.use_pool,
            current: self.use_list_head(value),
        }
    }

    /// Check whether a value has any uses.
    pub fn has_uses(&self, value: ValueRef) -> bool {
        self.use_list_head(value).is_some()
    }

    /// Count the number of uses of a value.
    pub fn use_count(&self, value: ValueRef) -> usize {
        self.uses_of(value).count()
    }

    /// Replace all uses of `old` with `new`. Updates operands in-place and
    /// moves use-list entries from `old` to `new`.
    pub fn replace_all_uses(&mut self, old: ValueRef, new: ValueRef) {
        // Collect all user instructions (to avoid borrow issues)
        let users: Vec<u32> = self.uses_of(old).map(|u| u.user).collect();

        for inst_idx in &users {
            // Rewrite operands in the instruction
            if let Some(node) = self.inst_pool.get_mut(*inst_idx) {
                node.inst.op.replace_value(old, new);
            }
        }

        // Move the entire use-list from old to new
        let old_head = self.use_list_head(old);
        if old_head.is_none() {
            return;
        }

        // Find the tail of old's use-list
        let mut tail = old_head.unwrap();
        loop {
            let node = self.use_pool.get(tail).unwrap();
            match node.next {
                Some(n) => tail = n,
                None => break,
            }
        }

        // Splice old's list onto the front of new's list
        let new_head = self.use_list_head(new);
        self.use_pool.get_mut(tail).unwrap().next = new_head;
        if let Some(nh) = new_head {
            self.use_pool.get_mut(nh).unwrap().prev = Some(tail);
        }
        self.set_use_list_head(new, old_head);
        self.set_use_list_head(old, None);
    }

    /// Rebuild all def-use chains from scratch. Call this after bulk
    /// modifications that bypass the incremental API (e.g., after parsing).
    pub fn rebuild_use_lists(&mut self) {
        // Clear all use-list heads
        for ba in &mut self.block_args {
            ba.use_list_head = None;
        }
        for node in self.inst_pool.iter_mut() {
            node.use_list_head = None;
            node.secondary_use_list_head = None;
        }
        self.use_pool = UsePool::new();

        // Re-register uses for every instruction
        let indices: Vec<u32> = self.inst_pool.iter_insts().map(|(idx, _)| idx).collect();
        for idx in indices {
            self.register_uses(idx);
        }
    }
}

/// Iterator over instructions in a basic block (follows linked list).
pub struct BlockInstIter<'a> {
    pool: &'a InstPool,
    current: Option<u32>,
}

impl<'a> Iterator for BlockInstIter<'a> {
    type Item = &'a Instruction;

    fn next(&mut self) -> Option<Self::Item> {
        let idx = self.current?;
        let node = self.pool.get(idx)?;
        self.current = node.next;
        Some(&node.inst)
    }
}

/// Iterator over `(ValueRef, &Instruction)` pairs in a basic block.
pub struct BlockInstValueIter<'a> {
    pool: &'a InstPool,
    current: Option<u32>,
}

impl<'a> Iterator for BlockInstValueIter<'a> {
    type Item = (ValueRef, &'a Instruction);

    fn next(&mut self) -> Option<Self::Item> {
        let idx = self.current?;
        let node = self.pool.get(idx)?;
        self.current = node.next;
        Some((ValueRef::inst_result(idx), &node.inst))
    }
}

/// Iterator over uses of a value (walks the use-list).
pub struct UseIter<'a> {
    pool: &'a UsePool,
    current: Option<u32>,
}

impl<'a> Iterator for UseIter<'a> {
    type Item = &'a UseNode;

    fn next(&mut self) -> Option<Self::Item> {
        let uid = self.current?;
        let node = self.pool.get(uid)?;
        self.current = node.next;
        Some(node)
    }
}
