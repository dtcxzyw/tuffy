//! Target-independent instruction selection building blocks.
//!
//! These data structures are shared across all backends. Each backend composes
//! them into its own `IselCtx` and lowering logic.

use tuffy_ir::value::ValueRef;
use tuffy_regalloc::{PReg, VReg};

/// Register slots keyed by IR value index.
type RegSlots = Vec<Option<VReg>>;
/// Stack slots keyed by IR value index as `(offset, alignment)`.
type StackSlots = Vec<Option<(i32, u32)>>;

/// Location hints for IR values after instruction selection.
pub struct SelectedValueLocations {
    /// Primary instruction-result registers.
    primary_regs: Vec<Option<VReg>>,
    /// Secondary instruction-result registers.
    secondary_regs: Vec<Option<VReg>>,
    /// Block-argument registers.
    block_arg_regs: Vec<Option<VReg>>,
    /// Instruction-result stack slots.
    stack_slots: Vec<Option<(i32, u32)>>,
    /// Block-argument stack slots.
    block_arg_stack_slots: Vec<Option<(i32, u32)>>,
}

impl SelectedValueLocations {
    /// Look up the assigned virtual register for a value.
    pub fn reg(&self, value: ValueRef) -> Option<VReg> {
        if value.is_block_arg() {
            *self.block_arg_regs.get(value.index() as usize)?
        } else if value.is_secondary_result() {
            *self.secondary_regs.get(value.index() as usize)?
        } else {
            *self.primary_regs.get(value.index() as usize)?
        }
    }

    /// Look up the assigned stack slot for a value.
    pub fn stack_slot(&self, value: ValueRef) -> Option<(i32, u32)> {
        if value.is_block_arg() {
            *self.block_arg_stack_slots.get(value.index() as usize)?
        } else {
            *self.stack_slots.get(value.index() as usize)?
        }
    }
}

/// Map from IR value to virtual register.
pub struct VRegMap {
    /// Primary instruction result values.
    map: Vec<Option<VReg>>,
    /// Secondary instruction result values (same instruction index as primary,
    /// but tagged with SECONDARY_BIT in ValueRef). Stored separately to avoid
    /// aliasing: both primary and secondary have the same `val.index()`, so
    /// using a single array would cause secondary assignments to overwrite the
    /// primary entry.
    secondary_map: Vec<Option<VReg>>,
    /// Block argument values (separate namespace).
    block_arg_map: Vec<Option<VReg>>,
}

impl VRegMap {
    /// Create empty register maps sized for instruction and block-argument arenas.
    pub fn new(inst_capacity: usize, block_arg_capacity: usize) -> Self {
        Self {
            map: vec![None; inst_capacity],
            secondary_map: vec![None; inst_capacity],
            block_arg_map: vec![None; block_arg_capacity],
        }
    }

    /// Record the virtual register assigned to a value.
    pub fn assign(&mut self, val: ValueRef, vreg: VReg) {
        if val.is_block_arg() {
            self.block_arg_map[val.index() as usize] = Some(vreg);
        } else if val.is_secondary_result() {
            self.secondary_map[val.index() as usize] = Some(vreg);
        } else {
            self.map[val.index() as usize] = Some(vreg);
        }
    }

    /// Look up the virtual register assigned to a value.
    pub fn get(&self, val: ValueRef) -> Option<VReg> {
        if val.is_block_arg() {
            *self.block_arg_map.get(val.index() as usize)?
        } else if val.is_secondary_result() {
            *self.secondary_map.get(val.index() as usize)?
        } else {
            *self.map.get(val.index() as usize)?
        }
    }

    /// Split the map into its internal storage vectors.
    fn into_parts(self) -> (RegSlots, RegSlots, RegSlots) {
        (self.map, self.secondary_map, self.block_arg_map)
    }
}

/// Tracks stack slot allocations (offset from frame pointer).
pub struct StackMap {
    /// Maps IR value index → (offset from frame pointer, alignment).
    slots: Vec<Option<(i32, u32)>>,
    /// Block argument stack slots (separate namespace).
    block_arg_slots: Vec<Option<(i32, u32)>>,
    /// Current stack frame size (grows downward).
    pub frame_size: i32,
}

impl StackMap {
    /// Create empty stack-slot maps sized for instruction and block-argument arenas.
    pub fn new(inst_capacity: usize, block_arg_capacity: usize) -> Self {
        Self {
            slots: vec![None; inst_capacity],
            block_arg_slots: vec![None; block_arg_capacity],
            frame_size: 0,
        }
    }

    /// Allocate a stack slot for a value and return its frame-pointer offset.
    pub fn alloc(&mut self, val: ValueRef, bytes: u32, align: u32) -> i32 {
        // Explicit alignment from the caller (the actual type alignment).
        // When 0, default to 8 (natural register size).
        let stored_align = if align > 0 {
            std::cmp::max(align, 8) as i32
        } else {
            8
        };
        // For frame layout padding, use at least max(bytes, 8) to keep
        // the historical over-alignment for naturally-sized slots.
        let padding_align = std::cmp::max(stored_align, std::cmp::max(bytes as i32, 8));
        // Reserve at least 1 byte so ZST allocations still advance
        // frame_size (offset 0 conflicts with saved rbp).
        let actual_bytes = std::cmp::max(bytes as i32, 1);

        let offset;
        if stored_align > 16 {
            // High-alignment slot (align > 16, exceeding ABI stack alignment).
            // RBP is only 16-aligned, so RBP-relative addresses aren't
            // guaranteed to be stored_align-aligned.  We use LEA + AND:
            //   lea dst, [rbp + offset]
            //   and dst, -align        ; round DOWN to aligned boundary
            //
            // The AND can shift at most (align-1) bytes downward, so we
            // reserve (align-1) extra bytes BELOW the data region.
            //
            // Layout in frame (growing downward from RBP):
            //   [RBP - old_frame ... RBP - old_frame - actual_bytes]  ← data
            //   [RBP - old_frame - actual_bytes ... -frame_size]      ← padding
            //
            // The LEA offset points to the TOP of the data region.
            // After AND, the address is within the (data + padding) range.
            offset = -(self.frame_size + actual_bytes);
            let extra_padding = stored_align - 1;
            self.frame_size += actual_bytes + extra_padding;
            self.frame_size = (self.frame_size + padding_align - 1) & !(padding_align - 1);
        } else {
            // Normal slot: placed at the bottom, no AND needed.
            self.frame_size += actual_bytes;
            self.frame_size = (self.frame_size + padding_align - 1) & !(padding_align - 1);
            offset = -self.frame_size;
        }

        let slot = (offset, stored_align as u32);
        if val.is_block_arg() {
            self.block_arg_slots[val.index() as usize] = Some(slot);
        } else {
            self.slots[val.index() as usize] = Some(slot);
        }
        offset
    }

    /// Get the offset for a stack slot.
    pub fn get(&self, val: ValueRef) -> Option<i32> {
        if val.is_block_arg() {
            self.block_arg_slots
                .get(val.index() as usize)?
                .map(|(o, _)| o)
        } else {
            self.slots.get(val.index() as usize)?.map(|(o, _)| o)
        }
    }

    /// Get the (offset, alignment) for a stack slot.
    pub fn get_with_align(&self, val: ValueRef) -> Option<(i32, u32)> {
        if val.is_block_arg() {
            *self.block_arg_slots.get(val.index() as usize)?
        } else {
            *self.slots.get(val.index() as usize)?
        }
    }

    /// Split the stack map into its internal storage vectors.
    fn into_parts(self) -> (StackSlots, StackSlots) {
        (self.slots, self.block_arg_slots)
    }
}

/// Tracks comparison results so conditional branches can emit fused jumps.
///
/// Generic over the condition code type (`CC`), which is target-specific.
pub struct CmpMap<CC: Copy> {
    /// Condition-code slots keyed by value index.
    map: Vec<Option<CC>>,
}

impl<CC: Copy> CmpMap<CC> {
    /// Create an empty comparison map.
    pub fn new(capacity: usize) -> Self {
        Self {
            map: vec![None; capacity],
        }
    }

    /// Record the condition code assigned to a value.
    pub fn set(&mut self, val: ValueRef, cc: CC) {
        self.map[val.index() as usize] = Some(cc);
    }

    /// Look up the condition code assigned to a value.
    pub fn get(&self, val: ValueRef) -> Option<CC> {
        self.map[val.index() as usize]
    }
}

/// Sequential virtual register allocator.
pub struct VRegAlloc {
    /// Next virtual-register number to allocate.
    pub next: u32,
    /// Fixed physical register constraint per VReg (indexed by VReg.0).
    /// None means the allocator is free to choose.
    pub constraints: Vec<Option<PReg>>,
    /// Register class per VReg (indexed by VReg.0).
    pub vreg_classes: Vec<u8>,
}

impl VRegAlloc {
    /// Create a fresh virtual-register allocator.
    pub fn new() -> Self {
        Self {
            next: 0,
            constraints: Vec::new(),
            vreg_classes: Vec::new(),
        }
    }

    /// Allocate a fresh virtual register with no constraint (GPR class).
    pub fn alloc(&mut self) -> VReg {
        let vreg = VReg(self.next);
        self.next += 1;
        self.constraints.push(None);
        self.vreg_classes.push(0);
        vreg
    }

    /// Allocate a fresh virtual register with specified class.
    pub fn alloc_class(&mut self, class: u8) -> VReg {
        let vreg = VReg(self.next);
        self.next += 1;
        self.constraints.push(None);
        self.vreg_classes.push(class);
        vreg
    }

    /// Allocate a fresh virtual register constrained to a physical register.
    pub fn alloc_fixed(&mut self, preg: PReg) -> VReg {
        let vreg = VReg(self.next);
        self.next += 1;
        self.constraints.push(Some(preg));
        self.vreg_classes.push(preg.0 >> 5);
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
    /// Function name for diagnostics and downstream consumers.
    pub name: String,
    /// Selected machine instructions.
    pub insts: Vec<I>,
    /// Optional origin source id for each machine instruction.
    pub inst_sources: Vec<Option<u32>>,
    /// Register and stack-slot locations for selected IR values.
    pub value_locations: SelectedValueLocations,
    /// Number of virtual registers allocated.
    pub vreg_count: u32,
    /// Fixed physical register constraint per VReg (indexed by VReg.0).
    /// None means the allocator is free to choose.
    pub constraints: Vec<Option<PReg>>,
    /// Register class per VReg (indexed by VReg.0).
    pub vreg_classes: Vec<u8>,
    /// Stack frame size from StackSlot operations only (not spills).
    pub isel_frame_size: i32,
    /// Whether the function contains any call instructions.
    pub has_calls: bool,
}

impl SelectedValueLocations {
    /// Construct value-location tables from the temporary selection maps.
    pub fn from_maps(regs: VRegMap, stack: StackMap) -> Self {
        let (primary_regs, secondary_regs, block_arg_regs) = regs.into_parts();
        let (stack_slots, block_arg_stack_slots) = stack.into_parts();
        Self {
            primary_regs,
            secondary_regs,
            block_arg_regs,
            stack_slots,
            block_arg_stack_slots,
        }
    }
}
