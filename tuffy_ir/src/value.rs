//! Opaque handles for IR entities.
//!
//! All references into the IR are u32 indices, not pointers.
//! This enables arena-based storage and serialization.
//!
//! ValueRef encoding:
//! - Bit 31 = 1:              block argument (lower 30 bits = block_args arena index)
//! - Bit 31 = 0, Bit 30 = 0:  primary instruction result (lower 30 bits = instruction index)
//! - Bit 31 = 0, Bit 30 = 1:  secondary instruction result (lower 30 bits = instruction index)

/// Reference to a value (instruction result or block argument).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ValueRef(pub(crate) u32);

const BLOCK_ARG_BIT: u32 = 1 << 31;
const SECONDARY_BIT: u32 = 1 << 30;
const TAG_MASK: u32 = BLOCK_ARG_BIT | SECONDARY_BIT;

impl ValueRef {
    /// Create a ValueRef for a primary instruction result.
    pub fn inst_result(index: u32) -> Self {
        debug_assert!(index & TAG_MASK == 0, "index too large");
        Self(index)
    }

    /// Create a ValueRef for a secondary instruction result (multi-result ops).
    pub fn inst_secondary_result(index: u32) -> Self {
        debug_assert!(index & TAG_MASK == 0, "index too large");
        Self(index | SECONDARY_BIT)
    }

    /// Create a ValueRef for a block argument.
    pub fn block_arg(index: u32) -> Self {
        debug_assert!(index & TAG_MASK == 0, "index too large");
        Self(index | BLOCK_ARG_BIT)
    }

    /// True if this refers to a block argument.
    pub fn is_block_arg(self) -> bool {
        self.0 & BLOCK_ARG_BIT != 0
    }

    /// True if this refers to a secondary instruction result.
    pub fn is_secondary_result(self) -> bool {
        !self.is_block_arg() && (self.0 & SECONDARY_BIT != 0)
    }

    /// Raw index (without any tag bits).
    pub fn index(self) -> u32 {
        self.0 & !TAG_MASK
    }

    /// Instruction arena index (masking both tag bits). Only valid for instruction results.
    pub fn inst_index(self) -> u32 {
        debug_assert!(!self.is_block_arg(), "inst_index called on block arg");
        self.0 & !TAG_MASK
    }

    /// Raw encoded value (with tag bits).
    pub fn raw(self) -> u32 {
        self.0
    }
}

/// Reference to an instruction in the arena.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct InstRef(pub(crate) u32);

impl InstRef {
    /// Raw index into the instruction arena.
    pub fn index(self) -> u32 {
        self.0
    }
}

/// Reference to a basic block.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct BlockRef(pub(crate) u32);

impl BlockRef {
    /// Raw index into the block arena.
    pub fn index(self) -> u32 {
        self.0
    }
}

/// Reference to a region.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct RegionRef(pub(crate) u32);

impl RegionRef {
    /// Raw index into the region arena.
    pub fn index(self) -> u32 {
        self.0
    }
}
