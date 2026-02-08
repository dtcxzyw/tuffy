//! Opaque handles for IR entities.
//!
//! All references into the IR are u32 indices, not pointers.
//! This enables arena-based storage and serialization.

/// Reference to a value (instruction result or function parameter).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ValueRef(pub(crate) u32);

/// Reference to an instruction in the arena.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct InstRef(pub(crate) u32);

/// Reference to a basic block.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct BlockRef(pub(crate) u32);
