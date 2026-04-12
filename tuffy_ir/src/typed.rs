//! Type-safe wrappers for IR values and operands.
//!
//! Provides zero-cost newtype wrappers with runtime type checking at construction.

use crate::function::Function;
use crate::instruction::Operand;
use crate::types::{Annotation, Type};
use crate::value::ValueRef;

// ── Value Wrappers ──

/// Type-checked wrapper for integer SSA values.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct IntValue(ValueRef);

/// Type-checked wrapper for boolean SSA values.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BoolValue(ValueRef);

/// Type-checked wrapper for floating-point SSA values.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FloatValue(ValueRef);

/// Type-checked wrapper for pointer SSA values.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PtrValue(ValueRef);

/// Type-checked wrapper for memory-token SSA values.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MemValue(ValueRef);

/// Type-checked wrapper for unit-typed SSA values.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct UnitValue(ValueRef);

/// Type-checked wrapper for byte-array SSA values.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ByteValue(ValueRef);

// ── Operand Wrappers ──

/// Type-checked wrapper for integer operands.
#[derive(Debug, Clone)]
pub struct IntOperand(pub(crate) Operand);

/// Type-checked wrapper for boolean operands.
#[derive(Debug, Clone)]
pub struct BoolOperand(pub(crate) Operand);

/// Type-checked wrapper for floating-point operands.
#[derive(Debug, Clone)]
pub struct FloatOperand(pub(crate) Operand);

/// Type-checked wrapper for pointer operands.
#[derive(Debug, Clone)]
pub struct PtrOperand(pub(crate) Operand);

/// Type-checked wrapper for memory-token operands.
#[derive(Debug, Clone)]
pub struct MemOperand(pub(crate) Operand);

/// Type-checked wrapper for unit operands.
#[derive(Debug, Clone)]
pub struct UnitOperand(pub(crate) Operand);

/// Type-checked wrapper for byte-array operands.
#[derive(Debug, Clone)]
pub struct ByteOperand(pub(crate) Operand);

// ── Value Wrapper Implementations ──

impl IntValue {
    /// Create an integer value wrapper from a raw value reference.
    ///
    /// # Panics
    ///
    /// Panics if `v` does not have IR type `int`.
    pub fn new(v: ValueRef, func: &Function) -> Self {
        assert!(
            matches!(func.value_type(v), Some(Type::Int)),
            "expected Int type, got {:?}",
            func.value_type(v)
        );
        Self(v)
    }

    /// Return the wrapped raw value reference.
    pub fn raw(self) -> ValueRef {
        self.0
    }

    /// Return whether the value is the secondary result of a multi-result instruction.
    pub fn is_secondary_result(self) -> bool {
        self.0.is_secondary_result()
    }

    /// Return the underlying value index.
    pub fn index(self) -> u32 {
        self.0.index()
    }
}

impl BoolValue {
    /// Create a boolean value wrapper from a raw value reference.
    ///
    /// # Panics
    ///
    /// Panics if `v` does not have IR type `bool`.
    pub fn new(v: ValueRef, func: &Function) -> Self {
        assert!(
            matches!(func.value_type(v), Some(Type::Bool)),
            "expected Bool type, got {:?}",
            func.value_type(v)
        );
        Self(v)
    }

    /// Return the wrapped raw value reference.
    pub fn raw(self) -> ValueRef {
        self.0
    }

    /// Return whether the value is the secondary result of a multi-result instruction.
    pub fn is_secondary_result(self) -> bool {
        self.0.is_secondary_result()
    }

    /// Return the underlying value index.
    pub fn index(self) -> u32 {
        self.0.index()
    }
}

impl FloatValue {
    /// Create a floating-point value wrapper from a raw value reference.
    ///
    /// # Panics
    ///
    /// Panics if `v` does not have a floating-point IR type.
    pub fn new(v: ValueRef, func: &Function) -> Self {
        assert!(
            matches!(func.value_type(v), Some(Type::Float(_))),
            "expected Float type, got {:?}",
            func.value_type(v)
        );
        Self(v)
    }

    /// Return the wrapped raw value reference.
    pub fn raw(self) -> ValueRef {
        self.0
    }

    /// Return whether the value is the secondary result of a multi-result instruction.
    pub fn is_secondary_result(self) -> bool {
        self.0.is_secondary_result()
    }

    /// Return the underlying value index.
    pub fn index(self) -> u32 {
        self.0.index()
    }
}

impl PtrValue {
    /// Create a pointer value wrapper from a raw value reference.
    ///
    /// # Panics
    ///
    /// Panics if `v` does not have a pointer IR type.
    pub fn new(v: ValueRef, func: &Function) -> Self {
        assert!(
            matches!(func.value_type(v), Some(Type::Ptr(_))),
            "expected Ptr type, got {:?}",
            func.value_type(v)
        );
        Self(v)
    }

    /// Return the wrapped raw value reference.
    pub fn raw(self) -> ValueRef {
        self.0
    }

    /// Return whether the value is the secondary result of a multi-result instruction.
    pub fn is_secondary_result(self) -> bool {
        self.0.is_secondary_result()
    }

    /// Return the underlying value index.
    pub fn index(self) -> u32 {
        self.0.index()
    }
}

impl MemValue {
    /// Create a memory-token value wrapper from a raw value reference.
    ///
    /// # Panics
    ///
    /// Panics if `v` does not have IR type `mem`.
    pub fn new(v: ValueRef, func: &Function) -> Self {
        assert!(
            matches!(func.value_type(v), Some(Type::Mem)),
            "expected Mem type, got {:?}",
            func.value_type(v)
        );
        Self(v)
    }

    /// Return the wrapped raw value reference.
    pub fn raw(self) -> ValueRef {
        self.0
    }

    /// Return whether the value is the secondary result of a multi-result instruction.
    pub fn is_secondary_result(self) -> bool {
        self.0.is_secondary_result()
    }

    /// Return the underlying value index.
    pub fn index(self) -> u32 {
        self.0.index()
    }
}

impl UnitValue {
    /// Create a unit value wrapper from a raw value reference.
    ///
    /// # Panics
    ///
    /// Panics if `v` does not have IR type `unit`.
    pub fn new(v: ValueRef, func: &Function) -> Self {
        assert!(
            matches!(func.value_type(v), Some(Type::Unit)),
            "expected Unit type, got {:?}",
            func.value_type(v)
        );
        Self(v)
    }

    /// Return the wrapped raw value reference.
    pub fn raw(self) -> ValueRef {
        self.0
    }

    /// Return whether the value is the secondary result of a multi-result instruction.
    pub fn is_secondary_result(self) -> bool {
        self.0.is_secondary_result()
    }

    /// Return the underlying value index.
    pub fn index(self) -> u32 {
        self.0.index()
    }
}

impl ByteValue {
    /// Create a byte-array value wrapper from a raw value reference.
    ///
    /// # Panics
    ///
    /// Panics if `v` does not have IR type `byte`.
    pub fn new(v: ValueRef, func: &Function) -> Self {
        assert!(
            matches!(func.value_type(v), Some(Type::Byte(_))),
            "expected Byte type, got {:?}",
            func.value_type(v)
        );
        Self(v)
    }

    /// Return the wrapped raw value reference.
    pub fn raw(self) -> ValueRef {
        self.0
    }

    /// Return whether the value is the secondary result of a multi-result instruction.
    pub fn is_secondary_result(self) -> bool {
        self.0.is_secondary_result()
    }

    /// Return the underlying value index.
    pub fn index(self) -> u32 {
        self.0.index()
    }
}

// ── Operand Wrapper Implementations ──

impl IntOperand {
    /// Create an integer operand wrapper from a raw operand.
    ///
    /// # Panics
    ///
    /// Panics if `op.value` does not have IR type `int`.
    pub fn new(op: Operand, func: &Function) -> Self {
        assert!(
            matches!(func.value_type(op.value), Some(Type::Int)),
            "expected Int type, got {:?}",
            func.value_type(op.value)
        );
        Self(op)
    }

    /// Create an unannotated integer operand from a typed integer value.
    pub fn from_value(v: IntValue) -> Self {
        Self(Operand::new(v.0))
    }

    /// Create an annotated integer operand from a typed integer value.
    pub fn annotated(v: IntValue, ann: Annotation) -> Self {
        Self(Operand::annotated(v.0, ann))
    }

    /// Return the wrapped raw operand.
    pub fn raw(self) -> Operand {
        self.0
    }
}

impl From<Operand> for IntOperand {
    fn from(op: Operand) -> Self {
        Self(op)
    }
}

impl From<IntValue> for IntOperand {
    fn from(v: IntValue) -> Self {
        Self(Operand::new(v.0))
    }
}

impl BoolOperand {
    /// Create a boolean operand wrapper from a raw operand.
    ///
    /// # Panics
    ///
    /// Panics if `op.value` does not have IR type `bool`.
    pub fn new(op: Operand, func: &Function) -> Self {
        assert!(
            matches!(func.value_type(op.value), Some(Type::Bool)),
            "expected Bool type, got {:?}",
            func.value_type(op.value)
        );
        Self(op)
    }

    /// Create an unannotated boolean operand from a typed boolean value.
    pub fn from_value(v: BoolValue) -> Self {
        Self(Operand::new(v.0))
    }

    /// Create an annotated boolean operand from a typed boolean value.
    pub fn annotated(v: BoolValue, ann: Annotation) -> Self {
        Self(Operand::annotated(v.0, ann))
    }

    /// Return the wrapped raw operand.
    pub fn raw(self) -> Operand {
        self.0
    }
}

impl From<Operand> for BoolOperand {
    fn from(op: Operand) -> Self {
        Self(op)
    }
}

impl From<BoolValue> for BoolOperand {
    fn from(v: BoolValue) -> Self {
        Self(Operand::new(v.0))
    }
}

impl FloatOperand {
    /// Create a floating-point operand wrapper from a raw operand.
    ///
    /// # Panics
    ///
    /// Panics if `op.value` does not have a floating-point IR type.
    pub fn new(op: Operand, func: &Function) -> Self {
        assert!(
            matches!(func.value_type(op.value), Some(Type::Float(_))),
            "expected Float type, got {:?}",
            func.value_type(op.value)
        );
        Self(op)
    }

    /// Create an unannotated floating-point operand from a typed value.
    pub fn from_value(v: FloatValue) -> Self {
        Self(Operand::new(v.0))
    }

    /// Create an annotated floating-point operand from a typed value.
    pub fn annotated(v: FloatValue, ann: Annotation) -> Self {
        Self(Operand::annotated(v.0, ann))
    }

    /// Return the wrapped raw operand.
    pub fn raw(self) -> Operand {
        self.0
    }
}

impl From<Operand> for FloatOperand {
    fn from(op: Operand) -> Self {
        Self(op)
    }
}

impl From<FloatValue> for FloatOperand {
    fn from(v: FloatValue) -> Self {
        Self(Operand::new(v.0))
    }
}

impl PtrOperand {
    /// Create a pointer operand wrapper from a raw operand.
    ///
    /// # Panics
    ///
    /// Panics if `op.value` does not have a pointer IR type.
    pub fn new(op: Operand, func: &Function) -> Self {
        assert!(
            matches!(func.value_type(op.value), Some(Type::Ptr(_))),
            "expected Ptr type, got {:?}",
            func.value_type(op.value)
        );
        Self(op)
    }

    /// Create an unannotated pointer operand from a typed value.
    pub fn from_value(v: PtrValue) -> Self {
        Self(Operand::new(v.0))
    }

    /// Create an annotated pointer operand from a typed value.
    pub fn annotated(v: PtrValue, ann: Annotation) -> Self {
        Self(Operand::annotated(v.0, ann))
    }

    /// Return the wrapped raw operand.
    pub fn raw(self) -> Operand {
        self.0
    }
}

impl From<Operand> for PtrOperand {
    fn from(op: Operand) -> Self {
        Self(op)
    }
}

impl MemOperand {
    /// Create a memory-token operand wrapper from a raw operand.
    ///
    /// # Panics
    ///
    /// Panics if `op.value` does not have IR type `mem`.
    pub fn new(op: Operand, func: &Function) -> Self {
        assert!(
            matches!(func.value_type(op.value), Some(Type::Mem)),
            "expected Mem type, got {:?}",
            func.value_type(op.value)
        );
        Self(op)
    }

    /// Create an unannotated memory-token operand from a typed value.
    pub fn from_value(v: MemValue) -> Self {
        Self(Operand::new(v.0))
    }

    /// Create an annotated memory-token operand from a typed value.
    pub fn annotated(v: MemValue, ann: Annotation) -> Self {
        Self(Operand::annotated(v.0, ann))
    }

    /// Return the wrapped raw operand.
    pub fn raw(self) -> Operand {
        self.0
    }
}

impl From<Operand> for MemOperand {
    fn from(op: Operand) -> Self {
        Self(op)
    }
}

impl UnitOperand {
    /// Create a unit operand wrapper from a raw operand.
    ///
    /// # Panics
    ///
    /// Panics if `op.value` does not have IR type `unit`.
    pub fn new(op: Operand, func: &Function) -> Self {
        assert!(
            matches!(func.value_type(op.value), Some(Type::Unit)),
            "expected Unit type, got {:?}",
            func.value_type(op.value)
        );
        Self(op)
    }

    /// Create an unannotated unit operand from a typed value.
    pub fn from_value(v: UnitValue) -> Self {
        Self(Operand::new(v.0))
    }

    /// Create an annotated unit operand from a typed value.
    pub fn annotated(v: UnitValue, ann: Annotation) -> Self {
        Self(Operand::annotated(v.0, ann))
    }

    /// Return the wrapped raw operand.
    pub fn raw(self) -> Operand {
        self.0
    }
}

impl ByteOperand {
    /// Create a byte-array operand wrapper from a raw operand.
    ///
    /// # Panics
    ///
    /// Panics if `op.value` does not have IR type `byte`.
    pub fn new(op: Operand, func: &Function) -> Self {
        assert!(
            matches!(func.value_type(op.value), Some(Type::Byte(_))),
            "expected Byte type, got {:?}",
            func.value_type(op.value)
        );
        Self(op)
    }

    /// Create an unannotated byte-array operand from a typed value.
    pub fn from_value(v: ByteValue) -> Self {
        Self(Operand::new(v.0))
    }

    /// Create an annotated byte-array operand from a typed value.
    pub fn annotated(v: ByteValue, ann: Annotation) -> Self {
        Self(Operand::annotated(v.0, ann))
    }

    /// Return the wrapped raw operand.
    pub fn raw(self) -> Operand {
        self.0
    }
}

// Conversions from typed values to Operand
impl From<IntValue> for Operand {
    fn from(v: IntValue) -> Self {
        Operand::new(v.0)
    }
}

impl From<BoolValue> for Operand {
    fn from(v: BoolValue) -> Self {
        Operand::new(v.0)
    }
}

impl From<FloatValue> for Operand {
    fn from(v: FloatValue) -> Self {
        Operand::new(v.0)
    }
}

impl From<PtrValue> for Operand {
    fn from(v: PtrValue) -> Self {
        Operand::new(v.0)
    }
}

impl From<MemValue> for Operand {
    fn from(v: MemValue) -> Self {
        Operand::new(v.0)
    }
}

// Conversions from ValueRef to typed operands
impl From<ValueRef> for IntOperand {
    fn from(v: ValueRef) -> Self {
        Self(Operand::new(v))
    }
}

impl From<ValueRef> for BoolOperand {
    fn from(v: ValueRef) -> Self {
        Self(Operand::new(v))
    }
}

impl From<ValueRef> for FloatOperand {
    fn from(v: ValueRef) -> Self {
        Self(Operand::new(v))
    }
}

impl From<ValueRef> for PtrOperand {
    fn from(v: ValueRef) -> Self {
        Self(Operand::new(v))
    }
}

impl From<ValueRef> for MemOperand {
    fn from(v: ValueRef) -> Self {
        Self(Operand::new(v))
    }
}

// Additional conversions from typed values to typed operands
impl From<PtrValue> for PtrOperand {
    fn from(v: PtrValue) -> Self {
        Self(Operand::new(v.0))
    }
}

impl From<MemValue> for MemOperand {
    fn from(v: MemValue) -> Self {
        Self(Operand::new(v.0))
    }
}

impl From<UnitValue> for UnitOperand {
    fn from(v: UnitValue) -> Self {
        Self(Operand::new(v.0))
    }
}

impl From<ByteValue> for ByteOperand {
    fn from(v: ByteValue) -> Self {
        Self(Operand::new(v.0))
    }
}

// Conversions from typed operands to Operand
impl From<IntOperand> for Operand {
    fn from(op: IntOperand) -> Self {
        op.0
    }
}

impl From<BoolOperand> for Operand {
    fn from(op: BoolOperand) -> Self {
        op.0
    }
}

impl From<FloatOperand> for Operand {
    fn from(op: FloatOperand) -> Self {
        op.0
    }
}

impl From<PtrOperand> for Operand {
    fn from(op: PtrOperand) -> Self {
        op.0
    }
}

impl From<MemOperand> for Operand {
    fn from(op: MemOperand) -> Self {
        op.0
    }
}

impl From<UnitOperand> for Operand {
    fn from(op: UnitOperand) -> Self {
        op.0
    }
}

impl From<ByteOperand> for Operand {
    fn from(op: ByteOperand) -> Self {
        op.0
    }
}

// Conversions from typed values to ValueRef
impl From<IntValue> for ValueRef {
    fn from(v: IntValue) -> Self {
        v.0
    }
}

impl From<BoolValue> for ValueRef {
    fn from(v: BoolValue) -> Self {
        v.0
    }
}

impl From<FloatValue> for ValueRef {
    fn from(v: FloatValue) -> Self {
        v.0
    }
}

impl From<PtrValue> for ValueRef {
    fn from(v: PtrValue) -> Self {
        v.0
    }
}

impl From<MemValue> for ValueRef {
    fn from(v: MemValue) -> Self {
        v.0
    }
}

impl From<UnitValue> for ValueRef {
    fn from(v: UnitValue) -> Self {
        v.0
    }
}

impl From<ByteValue> for ValueRef {
    fn from(v: ByteValue) -> Self {
        v.0
    }
}
