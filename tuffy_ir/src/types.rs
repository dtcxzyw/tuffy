//! Type system for tuffy IR.
//!
//! Types:
//! - `int`: infinite precision integer
//! - `Byte(n)`: raw memory data of n bytes
//! - `Ptr(as)`: pointer with address space
//! - `Float(ft)`: floating point type

/// Floating point type variants.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FloatType {
    /// Brain floating point (bfloat16).
    BF16,
    /// IEEE 754 half precision.
    F16,
    /// IEEE 754 single precision.
    F32,
    /// IEEE 754 double precision.
    F64,
}

/// A type in the tuffy IR.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type {
    /// Infinite precision integer. No fixed bitwidth.
    Int,
    /// Raw memory data of `n` bytes. Per-byte poison tracking.
    Byte(u32),
    /// Pointer with address space.
    Ptr(u32),
    /// Floating point type.
    Float(FloatType),
}

/// Memory ordering for atomic operations.
///
/// Mirrors `TuffyLean.IR.MemoryOrdering`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum MemoryOrdering {
    /// No ordering constraints.
    Relaxed,
    /// Acquire: reads after this load see writes from the releasing thread.
    Acquire,
    /// Release: writes before this store are visible to the acquiring thread.
    Release,
    /// Acquire + Release combined.
    AcqRel,
    /// Sequentially consistent: total order across all seqcst operations.
    SeqCst,
}

/// Range annotation on a value definition (result-side) or use edge (use-side).
///
/// Result-side violation: the defining instruction produces poison.
/// Use-side violation: the consuming instruction produces poison.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Annotation {
    /// `:s<N>` — value must be in signed N-bit range `[-2^(N-1), 2^(N-1)-1]`.
    Signed(u32),
    /// `:u<N>` — value must be in unsigned N-bit range `[0, 2^N-1]`.
    Unsigned(u32),
}
