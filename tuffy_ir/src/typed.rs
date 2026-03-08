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
