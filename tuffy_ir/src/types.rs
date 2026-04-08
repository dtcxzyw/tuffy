//! Type system for tuffy IR.
//!
//! Types:
//! - `int`: infinite precision integer
//! - `Byte(n)`: raw memory data of n bytes
//! - `Ptr(as)`: pointer with address space
//! - `Float(ft)`: floating point type

use num_bigint::BigUint;

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
    /// IEEE 754 quadruple precision.
    F128,
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

/// Integer signedness for type annotations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum IntSignedness {
    /// Only low N bits meaningful, high bits undef.
    DontCare,
    /// Value must be in signed N-bit range.
    Signed,
    /// Value must be in unsigned N-bit range.
    Unsigned,
}

/// Integer type annotation with bit width and signedness.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct IntAnnotation {
    pub bit_width: u32,
    pub signedness: IntSignedness,
}

/// Per-bit four-state annotation.
///
/// `ones`, `zeros`, and `demanded` are all finite masks over the low bits of an
/// infinite-precision integer value. Bits not present in `demanded` are treated
/// as don't-care (`x` in the text format).
#[derive(Debug, Clone, PartialEq, Eq, Hash, Default)]
pub struct KnownBits {
    pub ones: BigUint,
    pub zeros: BigUint,
    pub demanded: BigUint,
}

impl KnownBits {
    /// Parse a `known(...)` ternary payload.
    ///
    /// The rightmost character is bit 0. `_` separators are ignored.
    pub fn from_ternary_str(input: &str) -> Result<Self, String> {
        let mut ones = BigUint::default();
        let mut zeros = BigUint::default();
        let mut demanded = BigUint::default();
        let mut bit = 0usize;

        for ch in input.chars().rev() {
            match ch {
                '_' => continue,
                '1' => {
                    let mask = BigUint::from(1u8) << bit;
                    ones |= &mask;
                    demanded |= mask;
                    bit += 1;
                }
                '0' => {
                    let mask = BigUint::from(1u8) << bit;
                    zeros |= &mask;
                    demanded |= mask;
                    bit += 1;
                }
                '?' => {
                    demanded |= BigUint::from(1u8) << bit;
                    bit += 1;
                }
                'x' | 'X' => {
                    bit += 1;
                }
                other => {
                    return Err(format!("invalid known bits character `{other}`"));
                }
            }
        }

        let known = Self {
            ones,
            zeros,
            demanded,
        };
        if known.is_well_formed() {
            Ok(known)
        } else {
            Err("known bits masks are inconsistent".to_string())
        }
    }

    /// Format this known-bits mask as the payload of `known(...)`.
    pub fn to_ternary_string(&self) -> String {
        let width = self.highest_relevant_bit().unwrap_or(0) + 1;
        let mut out = String::with_capacity(width.max(1));
        for bit in (0..width).rev() {
            let mask = BigUint::from(1u8) << bit;
            let is_demanded = (&self.demanded & &mask) != BigUint::default();
            let is_one = (&self.ones & &mask) != BigUint::default();
            let is_zero = (&self.zeros & &mask) != BigUint::default();
            let ch = match (is_demanded, is_one, is_zero) {
                (_, true, false) => '1',
                (_, false, true) => '0',
                (true, false, false) => '?',
                (false, false, false) => 'x',
                _ => '?',
            };
            out.push(ch);
        }
        if out.is_empty() {
            out.push('x');
        }
        out
    }

    /// Check the representation invariant.
    pub fn is_well_formed(&self) -> bool {
        let overlap = &self.ones & &self.zeros;
        let known = &self.ones | &self.zeros;
        overlap == BigUint::default() && (&known & &self.demanded) == known
    }

    /// Return the highest bit used by any mask.
    pub fn highest_relevant_bit(&self) -> Option<usize> {
        let combined = (&self.ones | &self.zeros) | &self.demanded;
        let bits = combined.bits();
        if bits == 0 {
            None
        } else {
            Some(bits as usize - 1)
        }
    }
}

/// A type in the tuffy IR.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type {
    /// Infinite precision integer. Use result_annotation for bit width/signedness.
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
    /// Abstract memory state token for MemSSA.
    Mem,
    /// Struct type with field types.
    Struct(Vec<Type>),
    /// Array type with element type and count.
    Array(Box<Type>, u32),
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

/// Annotation for pointer alignment hints.
///
/// Result-side violation: the defining instruction produces poison.
/// Use-side violation: the consuming instruction produces poison.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Annotation {
    /// `:align<N>` — pointer alignment in bytes.
    Align(u32),
    /// Integer refinement: narrows bit width and/or signedness at use site.
    Int(IntAnnotation),
    /// `:known(<ternary>)` — per-bit four-state constraint on integer values.
    KnownBits(KnownBits),
    /// C ABI byval: the pointer argument actually references a struct that
    /// the callee expects *on the stack* (SysV MEMORY-class parameter).
    /// The ISel must copy `size` bytes from the pointed-to memory onto the
    /// call frame instead of passing the pointer in a register.
    Byval(u32),
}
