//! Type-safe wrappers for IR values and operands.
//!
//! Provides zero-cost newtype wrappers with runtime type checking at construction.

use crate::function::Function;
use crate::instruction::Operand;
use crate::types::{Annotation, Type};
use crate::value::ValueRef;

// ── Value Wrappers ──

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct IntValue(ValueRef);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BoolValue(ValueRef);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FloatValue(ValueRef);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PtrValue(ValueRef);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MemValue(ValueRef);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct UnitValue(ValueRef);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ByteValue(ValueRef);

// ── Operand Wrappers ──

#[derive(Debug, Clone)]
pub struct IntOperand(Operand);

#[derive(Debug, Clone)]
pub struct BoolOperand(Operand);

#[derive(Debug, Clone)]
pub struct FloatOperand(Operand);

#[derive(Debug, Clone)]
pub struct PtrOperand(Operand);

#[derive(Debug, Clone)]
pub struct MemOperand(Operand);

#[derive(Debug, Clone)]
pub struct UnitOperand(Operand);

#[derive(Debug, Clone)]
pub struct ByteOperand(Operand);

// ── Value Wrapper Implementations ──

impl IntValue {
    pub fn new(v: ValueRef, func: &Function) -> Self {
        assert!(
            matches!(func.value_type(v), Some(Type::Int)),
            "expected Int type, got {:?}",
            func.value_type(v)
        );
        Self(v)
    }

    pub fn raw(self) -> ValueRef {
        self.0
    }

    pub fn is_secondary_result(self) -> bool {
        self.0.is_secondary_result()
    }
}

impl BoolValue {
    pub fn new(v: ValueRef, func: &Function) -> Self {
        assert!(
            matches!(func.value_type(v), Some(Type::Bool)),
            "expected Bool type, got {:?}",
            func.value_type(v)
        );
        Self(v)
    }

    pub fn raw(self) -> ValueRef {
        self.0
    }

    pub fn is_secondary_result(self) -> bool {
        self.0.is_secondary_result()
    }
}

impl FloatValue {
    pub fn new(v: ValueRef, func: &Function) -> Self {
        assert!(
            matches!(func.value_type(v), Some(Type::Float(_))),
            "expected Float type, got {:?}",
            func.value_type(v)
        );
        Self(v)
    }

    pub fn raw(self) -> ValueRef {
        self.0
    }

    pub fn is_secondary_result(self) -> bool {
        self.0.is_secondary_result()
    }
}

impl PtrValue {
    pub fn new(v: ValueRef, func: &Function) -> Self {
        assert!(
            matches!(func.value_type(v), Some(Type::Ptr(_))),
            "expected Ptr type, got {:?}",
            func.value_type(v)
        );
        Self(v)
    }

    pub fn raw(self) -> ValueRef {
        self.0
    }

    pub fn is_secondary_result(self) -> bool {
        self.0.is_secondary_result()
    }
}

impl MemValue {
    pub fn new(v: ValueRef, func: &Function) -> Self {
        assert!(
            matches!(func.value_type(v), Some(Type::Mem)),
            "expected Mem type, got {:?}",
            func.value_type(v)
        );
        Self(v)
    }

    pub fn raw(self) -> ValueRef {
        self.0
    }

    pub fn is_secondary_result(self) -> bool {
        self.0.is_secondary_result()
    }
}

impl UnitValue {
    pub fn new(v: ValueRef, func: &Function) -> Self {
        assert!(
            matches!(func.value_type(v), Some(Type::Unit)),
            "expected Unit type, got {:?}",
            func.value_type(v)
        );
        Self(v)
    }

    pub fn raw(self) -> ValueRef {
        self.0
    }

    pub fn is_secondary_result(self) -> bool {
        self.0.is_secondary_result()
    }
}

impl ByteValue {
    pub fn new(v: ValueRef, func: &Function) -> Self {
        assert!(
            matches!(func.value_type(v), Some(Type::Byte(_))),
            "expected Byte type, got {:?}",
            func.value_type(v)
        );
        Self(v)
    }

    pub fn raw(self) -> ValueRef {
        self.0
    }

    pub fn is_secondary_result(self) -> bool {
        self.0.is_secondary_result()
    }
}

// ── Operand Wrapper Implementations ──

impl IntOperand {
    pub fn new(op: Operand, func: &Function) -> Self {
        assert!(
            matches!(func.value_type(op.value), Some(Type::Int)),
            "expected Int type, got {:?}",
            func.value_type(op.value)
        );
        Self(op)
    }

    pub fn from_value(v: IntValue) -> Self {
        Self(Operand::new(v.0))
    }

    pub fn annotated(v: IntValue, ann: Annotation) -> Self {
        Self(Operand::annotated(v.0, ann))
    }

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
    pub fn new(op: Operand, func: &Function) -> Self {
        assert!(
            matches!(func.value_type(op.value), Some(Type::Bool)),
            "expected Bool type, got {:?}",
            func.value_type(op.value)
        );
        Self(op)
    }

    pub fn from_value(v: BoolValue) -> Self {
        Self(Operand::new(v.0))
    }

    pub fn annotated(v: BoolValue, ann: Annotation) -> Self {
        Self(Operand::annotated(v.0, ann))
    }

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
    pub fn new(op: Operand, func: &Function) -> Self {
        assert!(
            matches!(func.value_type(op.value), Some(Type::Float(_))),
            "expected Float type, got {:?}",
            func.value_type(op.value)
        );
        Self(op)
    }

    pub fn from_value(v: FloatValue) -> Self {
        Self(Operand::new(v.0))
    }

    pub fn annotated(v: FloatValue, ann: Annotation) -> Self {
        Self(Operand::annotated(v.0, ann))
    }

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
    pub fn new(op: Operand, func: &Function) -> Self {
        assert!(
            matches!(func.value_type(op.value), Some(Type::Ptr(_))),
            "expected Ptr type, got {:?}",
            func.value_type(op.value)
        );
        Self(op)
    }

    pub fn from_value(v: PtrValue) -> Self {
        Self(Operand::new(v.0))
    }

    pub fn annotated(v: PtrValue, ann: Annotation) -> Self {
        Self(Operand::annotated(v.0, ann))
    }

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
    pub fn new(op: Operand, func: &Function) -> Self {
        assert!(
            matches!(func.value_type(op.value), Some(Type::Mem)),
            "expected Mem type, got {:?}",
            func.value_type(op.value)
        );
        Self(op)
    }

    pub fn from_value(v: MemValue) -> Self {
        Self(Operand::new(v.0))
    }

    pub fn annotated(v: MemValue, ann: Annotation) -> Self {
        Self(Operand::annotated(v.0, ann))
    }

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
    pub fn new(op: Operand, func: &Function) -> Self {
        assert!(
            matches!(func.value_type(op.value), Some(Type::Unit)),
            "expected Unit type, got {:?}",
            func.value_type(op.value)
        );
        Self(op)
    }

    pub fn from_value(v: UnitValue) -> Self {
        Self(Operand::new(v.0))
    }

    pub fn annotated(v: UnitValue, ann: Annotation) -> Self {
        Self(Operand::annotated(v.0, ann))
    }

    pub fn raw(self) -> Operand {
        self.0
    }
}

impl ByteOperand {
    pub fn new(op: Operand, func: &Function) -> Self {
        assert!(
            matches!(func.value_type(op.value), Some(Type::Byte(_))),
            "expected Byte type, got {:?}",
            func.value_type(op.value)
        );
        Self(op)
    }

    pub fn from_value(v: ByteValue) -> Self {
        Self(Operand::new(v.0))
    }

    pub fn annotated(v: ByteValue, ann: Annotation) -> Self {
        Self(Operand::annotated(v.0, ann))
    }

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
