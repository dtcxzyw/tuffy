//! Target-agnostic register allocator.
//!
//! Provides a linear scan register allocator that operates on virtual registers
//! and rewrites them to physical registers. Backends implement the [`RegAllocInst`]
//! and [`RegAllocTarget`] traits to integrate with the allocator.

pub mod allocator;
pub mod liveness;

use std::fmt;

/// A virtual register produced by instruction selection.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct VReg(pub u32);

impl fmt::Display for VReg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "v{}", self.0)
    }
}

/// A physical register, target-agnostic representation.
/// The `hw` field holds the hardware encoding (e.g. 0..15 for x86-64 GPRs).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct PReg(pub u8);

impl fmt::Display for PReg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "p{}", self.0)
    }
}
