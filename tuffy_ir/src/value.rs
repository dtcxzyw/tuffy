//! Opaque handles for IR entities.
//!
//! All references into the IR are u32 indices, not pointers.
//! This enables arena-based storage and serialization.
//!
//! ValueRef encoding:
//! - Bit 31 = 0: instruction result, lower 31 bits = index into instruction arena
//! - Bit 31 = 1: block argument, lower 31 bits = index into block_args arena

/// Reference to a value (instruction result or block argument).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ValueRef(pub(crate) u32);

const BLOCK_ARG_BIT: u32 = 1 << 31;

impl ValueRef {
    /// Create a ValueRef for an instruction result.
    pub fn inst_result(index: u32) -> Self {
        debug_assert!(index & BLOCK_ARG_BIT == 0, "index too large");
        Self(index)
    }

    /// Create a ValueRef for a block argument.
    pub fn block_arg(index: u32) -> Self {
        debug_assert!(index & BLOCK_ARG_BIT == 0, "index too large");
        Self(index | BLOCK_ARG_BIT)
    }

    /// True if this refers to a block argument.
    pub fn is_block_arg(self) -> bool {
        self.0 & BLOCK_ARG_BIT != 0
    }

    /// Raw index (without the tag bit).
    pub fn index(self) -> u32 {
        self.0 & !BLOCK_ARG_BIT
    }

    /// Raw encoded value (with tag bit).
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
