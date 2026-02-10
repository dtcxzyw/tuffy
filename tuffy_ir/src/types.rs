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

/// Vector type parameterized by total bit-width.
///
/// Element count is derived: `count = width / element_bits`.
/// Mirrors `TuffyLean.IR.VectorType`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum VectorType {
    /// Fixed-width vector (e.g., 128 for SSE, 256 for AVX).
    Fixed(u32),
    /// Scalable vector: `vscale × base_width` bits (e.g., SVE, RVV).
    Scalable(u32),
}

impl VectorType {
    /// Get the base width in bits.
    pub fn base_width(&self) -> u32 {
        match self {
            VectorType::Fixed(w) | VectorType::Scalable(w) => *w,
        }
    }

    /// Compute lane count given element bit-width.
    pub fn lane_count(&self, elem_bits: u32) -> u32 {
        self.base_width() / elem_bits
    }
}

/// A type in the tuffy IR.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type {
    /// Infinite precision integer. No fixed bitwidth.
    Int,
    /// Boolean (true/false). Distinct from integers.
    Bool,
    /// Zero-sized unit type. Represents Rust's `()`.
    Unit,
    /// Raw memory data of `n` bytes. Per-byte poison tracking.
    Byte(u32),
    /// Pointer with address space.
    Ptr(u32),
    /// Floating point type.
    Float(FloatType),
    /// Vector type parameterized by total bit-width.
    Vec(VectorType),
}

/// Bitmask of excluded IEEE 754 floating-point value classes.
///
/// Each flag being `true` means that class is excluded — the value must NOT
/// belong to that class. Violation produces poison (like integer annotations).
/// Mirrors `TuffyLean.IR.FpClassMask`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct FpClassMask {
    pub snan: bool,
    pub qnan: bool,
    pub ninf: bool,
    pub nnorm: bool,
    pub nsub: bool,
    pub nzero: bool,
    pub pzero: bool,
    pub psub: bool,
    pub pnorm: bool,
    pub pinf: bool,
}

impl FpClassMask {
    /// No classes excluded.
    pub const NONE: Self = Self {
        snan: false,
        qnan: false,
        ninf: false,
        nnorm: false,
        nsub: false,
        nzero: false,
        pzero: false,
        psub: false,
        pnorm: false,
        pinf: false,
    };

    /// Exclude all NaN (snan + qnan).
    pub const NAN: Self = Self {
        snan: true,
        qnan: true,
        ..Self::NONE
    };

    /// Exclude all infinity (ninf + pinf).
    pub const INF: Self = Self {
        ninf: true,
        pinf: true,
        ..Self::NONE
    };

    /// Exclude NaN and infinity.
    pub const NAN_INF: Self = Self {
        snan: true,
        qnan: true,
        ninf: true,
        pinf: true,
        ..Self::NONE
    };
}

/// Rewrite flags for floating-point instructions.
///
/// These are optimization permissions, not value constraints.
/// They do not affect operational semantics — only which rewrites are legal.
/// Mirrors `TuffyLean.IR.FpRewriteFlags`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct FpRewriteFlags {
    /// Allow associativity/commutativity reordering.
    pub reassoc: bool,
    /// Allow contraction (e.g., fma fusion).
    pub contract: bool,
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
