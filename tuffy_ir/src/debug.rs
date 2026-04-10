use crate::value::ValueRef;

/// A source location used for debug info emission.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SourceLocation {
    pub file: String,
    pub line: u32,
    pub column: u32,
}

/// One original source-bearing operation referenced by IR `Origin`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DebugSource {
    pub location: SourceLocation,
}

/// The kind of source-level variable being described.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DebugVariableKind {
    Parameter,
    Local,
}

/// One source-level variable or parameter.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DebugVariable {
    pub name: String,
    pub kind: DebugVariableKind,
    pub declaration: Option<SourceLocation>,
}

/// The IR value currently carrying a variable's contents.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DebugValue {
    IrValue(ValueRef),
}

/// A source point where a variable becomes associated with a new IR value.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DebugBinding {
    pub source: u32,
    pub variable: u32,
    pub value: DebugValue,
}

/// Per-function debug metadata that survives optimization and lowering.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct FunctionDebugInfo {
    pub declaration: Option<SourceLocation>,
    pub sources: Vec<DebugSource>,
    pub variables: Vec<DebugVariable>,
    pub bindings: Vec<DebugBinding>,
}

impl FunctionDebugInfo {
    pub fn has_debuginfo(&self) -> bool {
        !self.sources.is_empty() || !self.variables.is_empty()
    }
}
