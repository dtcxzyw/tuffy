//! Instruction pool with linked-list threading for per-BB instruction ordering.
//!
//! Instructions are stored in an arena (`Vec<Option<InstNode>>`) and accessed by
//! `u32` index. Each instruction carries prev/next pointers for its basic block's
//! doubly-linked list. Deleted slots are recycled via a free list.

use crate::instruction::Instruction;
use crate::value::BlockRef;

/// A node in the instruction pool: instruction data plus linked-list metadata.
#[derive(Debug, Clone)]
pub struct InstNode {
    /// Instruction payload stored in this node.
    pub inst: Instruction,
    /// Previous instruction in the same basic block (`None` if first).
    pub prev: Option<u32>,
    /// Next instruction in the same basic block (`None` if last).
    pub next: Option<u32>,
    /// The basic block this instruction belongs to.
    pub parent_block: BlockRef,
    /// Head of the use-list for the primary result of this instruction.
    pub use_list_head: Option<u32>,
    /// Head of the use-list for the secondary result (if any).
    pub secondary_use_list_head: Option<u32>,
    /// Use-node ids for each operand used by this instruction, in operand order.
    pub operand_use_ids: Vec<u32>,
}

/// Arena for instructions with O(1) alloc/free and linked-list threading.
///
/// Indices are stable: removing an instruction recycles its slot via a free list
/// but never invalidates other indices.
#[derive(Debug, Clone)]
pub struct InstPool {
    /// Storage for live and vacant instruction slots.
    nodes: Vec<Option<InstNode>>,
    /// Free-list of vacant instruction indices.
    free_list: Vec<u32>,
    /// Number of live instructions currently stored.
    live_count: u32,
}

impl InstPool {
    /// Create an empty instruction pool.
    pub fn new() -> Self {
        Self {
            nodes: Vec::new(),
            free_list: Vec::new(),
            live_count: 0,
        }
    }

    /// Allocate a new instruction node, returning its pool index.
    pub fn alloc(&mut self, node: InstNode) -> u32 {
        self.live_count += 1;
        if let Some(idx) = self.free_list.pop() {
            self.nodes[idx as usize] = Some(node);
            idx
        } else {
            let idx = self.nodes.len() as u32;
            self.nodes.push(Some(node));
            idx
        }
    }

    /// Remove an instruction from the pool. Returns the node if it existed.
    /// The slot is added to the free list for reuse.
    pub fn free(&mut self, index: u32) -> Option<InstNode> {
        let node = self.nodes.get_mut(index as usize)?.take();
        if node.is_some() {
            self.free_list.push(index);
            self.live_count -= 1;
        }
        node
    }

    /// Get a reference to an instruction node by index.
    pub fn get(&self, index: u32) -> Option<&InstNode> {
        self.nodes.get(index as usize)?.as_ref()
    }

    /// Get a mutable reference to an instruction node by index.
    pub fn get_mut(&mut self, index: u32) -> Option<&mut InstNode> {
        self.nodes.get_mut(index as usize)?.as_mut()
    }

    /// Get the instruction at `index`, panicking if the slot is empty.
    ///
    /// # Panics
    ///
    /// Panics if `index` does not refer to a live instruction slot.
    pub fn inst(&self, index: u32) -> &Instruction {
        &self.get(index).expect("invalid instruction index").inst
    }

    /// Get a mutable reference to the instruction at `index`.
    ///
    /// # Panics
    ///
    /// Panics if `index` does not refer to a live instruction slot.
    pub fn inst_mut(&mut self, index: u32) -> &mut Instruction {
        &mut self.get_mut(index).expect("invalid instruction index").inst
    }

    /// Number of live (non-deleted) instructions.
    pub fn live_count(&self) -> u32 {
        self.live_count
    }

    /// Total backing array length (including deleted slots).
    pub fn next_index(&self) -> u32 {
        self.nodes.len() as u32
    }

    /// Iterate all live `(index, &InstNode)` pairs in allocation order.
    pub fn iter(&self) -> impl Iterator<Item = (u32, &InstNode)> {
        self.nodes
            .iter()
            .enumerate()
            .filter_map(|(i, slot)| slot.as_ref().map(|node| (i as u32, node)))
    }

    /// Iterate all live `(index, &Instruction)` pairs in allocation order.
    pub fn iter_insts(&self) -> impl Iterator<Item = (u32, &Instruction)> {
        self.iter().map(|(i, node)| (i, &node.inst))
    }

    /// Iterate all live `&mut InstNode` in allocation order.
    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut InstNode> {
        self.nodes.iter_mut().filter_map(|slot| slot.as_mut())
    }
}

impl Default for InstPool {
    fn default() -> Self {
        Self::new()
    }
}

// ── Use-list pool ──

/// A node in a def-use chain. Each node represents one use of a value by
/// an instruction operand. Uses for the same value form a doubly-linked list.
#[derive(Debug, Clone)]
pub struct UseNode {
    /// The value referenced by this use edge.
    pub value: crate::value::ValueRef,
    /// The instruction that contains this use.
    pub user: u32,
    /// Operand slot within `user` that references `value`.
    pub operand_index: u32,
    /// Next use of the same value (`None` if tail).
    pub next: Option<u32>,
    /// Previous use of the same value (`None` if head).
    pub prev: Option<u32>,
}

/// Pool-based arena for use-list nodes with free-list recycling.
#[derive(Debug, Clone)]
pub struct UsePool {
    /// Storage for live and vacant use-node slots.
    nodes: Vec<Option<UseNode>>,
    /// Free-list of vacant use-node indices.
    free_list: Vec<u32>,
}

impl UsePool {
    /// Create an empty use-node pool.
    pub fn new() -> Self {
        Self {
            nodes: Vec::new(),
            free_list: Vec::new(),
        }
    }

    /// Allocate a new use node, returning its index.
    pub fn alloc(&mut self, node: UseNode) -> u32 {
        if let Some(idx) = self.free_list.pop() {
            self.nodes[idx as usize] = Some(node);
            idx
        } else {
            let idx = self.nodes.len() as u32;
            self.nodes.push(Some(node));
            idx
        }
    }

    /// Remove a use node, returning it. Slot is recycled.
    pub fn free(&mut self, index: u32) -> Option<UseNode> {
        let node = self.nodes.get_mut(index as usize)?.take();
        if node.is_some() {
            self.free_list.push(index);
        }
        node
    }

    /// Get a reference to a use node by index.
    pub fn get(&self, index: u32) -> Option<&UseNode> {
        self.nodes.get(index as usize)?.as_ref()
    }

    /// Get a mutable reference to a use node by index.
    pub fn get_mut(&mut self, index: u32) -> Option<&mut UseNode> {
        self.nodes.get_mut(index as usize)?.as_mut()
    }
}

impl Default for UsePool {
    fn default() -> Self {
        Self::new()
    }
}
