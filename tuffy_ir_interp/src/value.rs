//! Interpreter value representation.
//!
//! Values follow the Lean specification in `lean/TuffyLean/IR/Types.lean`:
//! - Infinite-precision integers (`num_bigint::BigInt`)
//! - Booleans
//! - IEEE 754 floats (via `rustc_apfloat`)
//! - Pointers with provenance tracking
//! - Four-state abstract bytes
//! - Poison (deferred UB marker)

use std::fmt;

use num_bigint::BigInt;
use tuffy_ir::instruction::FloatConst;
use tuffy_ir::types::FloatType;

/// Allocation identifier for provenance tracking.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct AllocId(pub u64);

/// A pointer with provenance: allocation ID + byte offset.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Pointer {
    /// Referenced allocation id.
    pub alloc_id: AllocId,
    /// Byte offset within the allocation.
    pub offset: i64,
}

/// Four-state abstract byte for memory modelling.
///
/// Mirrors `TuffyLean.IR.AbstractByte`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AbstractByte {
    /// A concrete byte value.
    Bits(u8),
    /// Part of a stored pointer (alloc_id, pointer offset, fragment index).
    PtrFragment(AllocId, i64, usize),
    /// Uninitialized memory.
    Uninit,
    /// Poison byte.
    Poison,
}

/// Runtime values for the interpreter.
#[derive(Debug, Clone)]
pub enum Value {
    /// Infinite-precision integer.
    Int(BigInt),
    /// Boolean.
    Bool(bool),
    /// IEEE 754 floating point stored as raw bits + type.
    Float(FloatConst),
    /// Pointer with provenance.
    Ptr(Pointer),
    /// Raw byte sequence (for Byte(n) typed values).
    Bytes(Vec<AbstractByte>),
    /// Poison value — deferred undefined behavior.
    Poison,
    /// Unit value (zero-sized).
    Unit,
    /// Aggregate value (structs, arrays).
    Aggregate(Vec<Value>),
    /// Memory token (operationally a no-op in sequential execution).
    Mem,
}

impl Value {
    /// Returns true if this value is poison.
    pub fn is_poison(&self) -> bool {
        matches!(self, Value::Poison)
    }

    /// Extract as integer, or None if poison/wrong type.
    pub fn as_int(&self) -> Option<&BigInt> {
        match self {
            Value::Int(n) => Some(n),
            _ => None,
        }
    }

    /// Extract as bool, or None.
    pub fn as_bool(&self) -> Option<bool> {
        match self {
            Value::Bool(b) => Some(*b),
            // MIR-to-IR may pass int values where bool is expected
            // (e.g., `xor` result used as a Select condition).
            Value::Int(n) => Some(n.sign() != num_bigint::Sign::NoSign),
            _ => None,
        }
    }

    /// Extract as pointer, or None.
    pub fn as_ptr(&self) -> Option<&Pointer> {
        match self {
            Value::Ptr(p) => Some(p),
            _ => None,
        }
    }

    /// Extract as float, or None.
    pub fn as_float(&self) -> Option<&FloatConst> {
        match self {
            Value::Float(f) => Some(f),
            _ => None,
        }
    }

    /// Convert an integer value to its BigInt representation, consuming self.
    pub fn into_int(self) -> Option<BigInt> {
        match self {
            Value::Int(n) => Some(n),
            _ => None,
        }
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Int(n) => write!(f, "{n}"),
            Value::Bool(b) => write!(f, "{b}"),
            Value::Float(fc) => write!(f, "{:?}", fc),
            Value::Ptr(p) => write!(f, "ptr(alloc{}, offset {})", p.alloc_id.0, p.offset),
            Value::Bytes(bs) => write!(f, "bytes[{}]", bs.len()),
            Value::Poison => write!(f, "poison"),
            Value::Unit => write!(f, "()"),
            Value::Aggregate(vs) => {
                write!(f, "(")?;
                for (i, v) in vs.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{v}")?;
                }
                write!(f, ")")
            }
            Value::Mem => write!(f, "mem"),
        }
    }
}

impl fmt::Display for AbstractByte {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            AbstractByte::Bits(b) => write!(f, "{b:#04x}"),
            AbstractByte::PtrFragment(id, off, idx) => {
                write!(f, "ptr_frag(alloc{}+{off}, {idx})", id.0)
            }
            AbstractByte::Uninit => write!(f, "uninit"),
            AbstractByte::Poison => write!(f, "poison"),
        }
    }
}

/// Encode an integer as little-endian abstract bytes.
pub fn int_to_le_bytes(val: &BigInt, byte_count: usize) -> Vec<AbstractByte> {
    use num_bigint::Sign;
    let (sign, mut digits) = val.to_bytes_le();
    digits.resize(byte_count, 0);
    if sign == Sign::Minus {
        // Two's complement for negative numbers: invert + 1
        let abs_bytes = val.magnitude().to_bytes_le();
        let mut carry = true;
        digits = vec![0u8; byte_count];
        for i in 0..byte_count {
            let b = if i < abs_bytes.len() { abs_bytes[i] } else { 0 };
            let inverted = !b;
            let (sum, c) = inverted.overflowing_add(if carry { 1 } else { 0 });
            digits[i] = sum;
            carry = c;
        }
    }
    digits.into_iter().map(AbstractByte::Bits).collect()
}

/// Decode little-endian abstract bytes to an integer.
/// Returns None if any byte is not Bits.
pub fn le_bytes_to_int(bytes: &[AbstractByte], signed: bool) -> Option<BigInt> {
    let mut raw = Vec::with_capacity(bytes.len());
    for b in bytes {
        match b {
            AbstractByte::Bits(v) => raw.push(*v),
            // Treat Uninit/Poison as 0 — codegen may load across padding.
            AbstractByte::Uninit | AbstractByte::Poison => raw.push(0),
            _ => return None,
        }
    }
    let val = BigInt::from_bytes_le(num_bigint::Sign::Plus, &raw);
    if signed && !raw.is_empty() {
        let n_bits = raw.len() * 8;
        let sign_bit = BigInt::from(1) << (n_bits - 1);
        if val >= sign_bit {
            let modulus = BigInt::from(1) << n_bits;
            Some(val - modulus)
        } else {
            Some(val)
        }
    } else {
        Some(val)
    }
}

/// Encode a float constant as little-endian abstract bytes.
pub fn float_to_le_bytes(fc: &FloatConst) -> Vec<AbstractByte> {
    let bits = fc.to_bits();
    let byte_count = match fc.float_type() {
        FloatType::BF16 | FloatType::F16 => 2,
        FloatType::F32 => 4,
        FloatType::F64 => 8,
        FloatType::F128 => 16,
    };
    (0..byte_count)
        .map(|i| AbstractByte::Bits(((bits >> (i * 8)) & 0xff) as u8))
        .collect()
}

/// Encode a pointer as little-endian abstract bytes (8 bytes, pointer-sized).
pub fn ptr_to_le_bytes(ptr: &Pointer) -> Vec<AbstractByte> {
    (0..8)
        .map(|i| AbstractByte::PtrFragment(ptr.alloc_id, ptr.offset, i))
        .collect()
}
