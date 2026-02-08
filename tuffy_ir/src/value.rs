//! Opaque handles for IR entities.
//!
//! All references into the IR are u32 indices, not pointers.
//! This enables arena-based storage and serialization.

/// Reference to a value (instruction result or function parameter).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ValueRef(pub(crate) u32);

impl ValueRef {
    /// Raw index into the instruction arena.
    pub fn index(self) -> u32 {
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
