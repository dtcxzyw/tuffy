//! Debug-info side tables attached to functions.

use crate::value::ValueRef;

/// A source location used for debug info emission.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SourceLocation {
    /// Source file path or logical file name.
    pub file: String,
    /// 1-based source line number.
    pub line: u32,
    /// 1-based source column number.
    pub column: u32,
}

/// One original source-bearing operation referenced by IR `Origin`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DebugSource {
    /// Source location represented by this debug source entry.
    pub location: SourceLocation,
}

/// The kind of source-level variable being described.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum DebugVariableKind {
    /// Function parameter.
    Parameter,
    /// Local source variable.
    Local,
}

/// One source-level variable or parameter.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DebugVariable {
    /// User-visible source variable name.
    pub name: String,
    /// Whether the variable is a parameter or a local.
    pub kind: DebugVariableKind,
    /// Optional declaration site of the variable.
    pub declaration: Option<SourceLocation>,
}

/// The IR value currently carrying a variable's contents.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DebugValue {
    /// The variable currently resides in an IR SSA value.
    IrValue(ValueRef),
}

/// A source point where a variable becomes associated with a new IR value.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DebugBinding {
    /// Index into [`FunctionDebugInfo::sources`] naming the source point.
    pub source: u32,
    /// Index into [`FunctionDebugInfo::variables`] naming the source variable.
    pub variable: u32,
    /// IR value currently bound to the source variable.
    pub value: DebugValue,
}

/// Per-function debug metadata that survives optimization and lowering.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct FunctionDebugInfo {
    /// Optional declaration site of the function itself.
    pub declaration: Option<SourceLocation>,
    /// Source locations referenced by debug bindings.
    pub sources: Vec<DebugSource>,
    /// Source-level variables known for the function.
    pub variables: Vec<DebugVariable>,
    /// Value-to-variable bindings recorded for debug emission.
    pub bindings: Vec<DebugBinding>,
}

impl FunctionDebugInfo {
    /// Return whether this function carries any meaningful debug metadata.
    pub fn has_debuginfo(&self) -> bool {
        !self.sources.is_empty() || !self.variables.is_empty()
    }
}
