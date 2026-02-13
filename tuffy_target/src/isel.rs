//! Target-independent instruction selection building blocks.
//!
//! These data structures are shared across all backends. Each backend composes
//! them into its own `IselCtx` and lowering logic.

use tuffy_ir::value::ValueRef;
use tuffy_regalloc::{PReg, VReg};

/// Map from IR value to virtual register.
pub struct VRegMap {
    /// Instruction result values.
    map: Vec<Option<VReg>>,
    /// Block argument values (separate namespace).
    block_arg_map: Vec<Option<VReg>>,
}

impl VRegMap {
    pub fn new(inst_capacity: usize, block_arg_capacity: usize) -> Self {
        Self {
            map: vec![None; inst_capacity],
            block_arg_map: vec![None; block_arg_capacity],
        }
    }

    pub fn assign(&mut self, val: ValueRef, vreg: VReg) {
        if val.is_block_arg() {
            self.block_arg_map[val.index() as usize] = Some(vreg);
        } else {
            self.map[val.index() as usize] = Some(vreg);
        }
    }

    pub fn get(&self, val: ValueRef) -> Option<VReg> {
        if val.is_block_arg() {
            *self.block_arg_map.get(val.index() as usize)?
        } else {
            *self.map.get(val.index() as usize)?
        }
    }
}

/// Tracks stack slot allocations (offset from frame pointer).
pub struct StackMap {
    /// Maps IR value index → offset from frame pointer (negative).
    slots: Vec<Option<i32>>,
    /// Block argument stack slots (separate namespace).
    block_arg_slots: Vec<Option<i32>>,
    /// Current stack frame size (grows downward).
    pub frame_size: i32,
}

impl StackMap {
    pub fn new(inst_capacity: usize, block_arg_capacity: usize) -> Self {
        Self {
            slots: vec![None; inst_capacity],
            block_arg_slots: vec![None; block_arg_capacity],
            frame_size: 0,
        }
    }

    pub fn alloc(&mut self, val: ValueRef, bytes: u32) -> i32 {
        self.frame_size += bytes as i32;
        // Align to natural alignment (at least 8 bytes for pointers).
        let align = std::cmp::max(bytes as i32, 8);
        self.frame_size = (self.frame_size + align - 1) & !(align - 1);
        let offset = -self.frame_size;
        if val.is_block_arg() {
            self.block_arg_slots[val.index() as usize] = Some(offset);
        } else {
            self.slots[val.index() as usize] = Some(offset);
        }
        offset
    }

    pub fn get(&self, val: ValueRef) -> Option<i32> {
        if val.is_block_arg() {
            *self.block_arg_slots.get(val.index() as usize)?
        } else {
            *self.slots.get(val.index() as usize)?
        }
    }
}

/// Tracks comparison results so conditional branches can emit fused jumps.
///
/// Generic over the condition code type (`CC`), which is target-specific.
pub struct CmpMap<CC: Copy> {
    map: Vec<Option<CC>>,
}

impl<CC: Copy> CmpMap<CC> {
    pub fn new(capacity: usize) -> Self {
        Self {
            map: vec![None; capacity],
        }
    }

    pub fn set(&mut self, val: ValueRef, cc: CC) {
        self.map[val.index() as usize] = Some(cc);
    }

    pub fn get(&self, val: ValueRef) -> Option<CC> {
        self.map[val.index() as usize]
    }
}

/// Sequential virtual register allocator.
pub struct VRegAlloc {
    pub next: u32,
    /// Fixed physical register constraint per VReg (indexed by VReg.0).
    /// None means the allocator is free to choose.
    pub constraints: Vec<Option<PReg>>,
}

impl VRegAlloc {
    pub fn new() -> Self {
        Self {
            next: 0,
            constraints: Vec::new(),
        }
    }

    /// Allocate a fresh virtual register with no constraint.
    pub fn alloc(&mut self) -> VReg {
        let vreg = VReg(self.next);
        self.next += 1;
        self.constraints.push(None);
        vreg
    }

    /// Allocate a fresh virtual register constrained to a physical register.
    pub fn alloc_fixed(&mut self, preg: PReg) -> VReg {
        let vreg = VReg(self.next);
        self.next += 1;
        self.constraints.push(Some(preg));
        vreg
    }
}

impl Default for VRegAlloc {
    fn default() -> Self {
        Self::new()
    }
}

/// Result of instruction selection for a single function.
///
/// Generic over the instruction type (`I`), which is target-specific.
pub struct IselResult<I> {
    pub name: String,
    pub insts: Vec<I>,
    /// Number of virtual registers allocated.
    pub vreg_count: u32,
    /// Fixed physical register constraint per VReg (indexed by VReg.0).
    /// None means the allocator is free to choose.
    pub constraints: Vec<Option<PReg>>,
    /// Stack frame size from StackSlot operations only (not spills).
    pub isel_frame_size: i32,
    /// Whether the function contains any call instructions.
    pub has_calls: bool,
}
