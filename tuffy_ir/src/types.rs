//! Type system for tuffy IR.
//!
//! Minimal subset for the first end-to-end test:
//! - `int`: infinite precision integer
//! - `Byte(n)`: raw memory data of n bytes
//! - `Ptr`: pointer with address space

/// A type in the tuffy IR.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type {
    /// Infinite precision integer. No fixed bitwidth.
    Int,
    /// Raw memory data of `n` bytes. Per-byte poison tracking.
    Byte(u32),
    /// Pointer with address space.
    Ptr(u32),
}
