//! JSON schema types matching the Lean export format.

use std::collections::HashMap;

use serde::Deserialize;

/// Top-level instruction-selection specification exported from Lean.
#[derive(Debug, Deserialize)]
pub struct IselSpec {
    /// Schema format version expected by the generator.
    pub format_version: u32,
    /// Target name the rules were generated for.
    pub target: String,
    /// Shared metadata used while lowering rule payloads into Rust.
    pub metadata: IselMetadata,
    /// Instruction-selection rules to emit into the generated matcher.
    pub rules: Vec<IselRule>,
}

/// Metadata shared by every generated rule.
#[derive(Debug, Deserialize)]
pub struct IselMetadata {
    /// Rust imports copied verbatim into the generated source file.
    pub imports: Vec<String>,
    /// Named lookup tables referenced by emitted fields.
    pub maps: IselMaps,
}

/// Named metadata maps used by rule emission.
#[derive(Debug, Deserialize)]
pub struct IselMaps {
    /// Mapping from serialized fixed-register keys to backend preg expressions.
    pub fixed_regs: HashMap<String, String>,
    /// Mapping from serialized size keys to backend `OpSize` expressions.
    pub size: HashMap<String, String>,
    /// Mapping from serialized condition-code keys to backend condition expressions.
    pub cc: HashMap<String, String>,
}

/// A single instruction-selection rule.
#[derive(Debug, Deserialize)]
pub struct IselRule {
    /// Stable rule name used for generated helper function names and diagnostics.
    pub name: String,
    /// The IR shape this rule matches.
    pub pattern: IrPattern,
    /// Machine instructions emitted when the pattern matches.
    pub emit: Vec<EmitInst>,
    /// How the generated selector reports the produced result.
    pub result: ResultKind,
    /// Whether the rule derives its compare flags from the matched `icmp` opcode.
    #[serde(default)]
    pub icmp_cc_from_op: bool,
}

/// IR-side pattern that dispatches to a generated rule.
#[derive(Debug, Deserialize)]
#[serde(tag = "kind")]
pub enum IrPattern {
    /// Match a binary IR opcode and bind both operands.
    #[serde(rename = "binop")]
    Binop {
        /// IR opcode name, for example `Add` or `PtrDiff`.
        op: String,
        /// Pattern for the left-hand operand.
        lhs: OperandPat,
        /// Pattern for the right-hand operand.
        rhs: OperandPat,
    },
    /// Match a unary IR opcode and bind its single operand.
    #[serde(rename = "unop")]
    Unop {
        /// IR opcode name, for example `CountOnes`.
        op: String,
        /// Pattern for the input operand.
        val: OperandPat,
    },
    /// Match an integer comparison and bind both compared operands.
    #[serde(rename = "icmp")]
    Icmp {
        /// Pattern for the left-hand operand.
        lhs: OperandPat,
        /// Pattern for the right-hand operand.
        rhs: OperandPat,
    },
}

/// Operand-level constraints captured by a pattern.
#[derive(Debug, Deserialize)]
pub struct OperandPat {
    /// Name of the generated `VReg` parameter bound to this operand.
    pub reg: String,
    /// Annotation guard the operand must satisfy.
    pub ann: AnnGuard,
}

/// Annotation predicate applied to a matched operand.
#[derive(Debug, Deserialize, Clone, Copy, PartialEq, Eq)]
#[serde(rename_all = "lowercase")]
pub enum AnnGuard {
    /// Accept any annotation, including no annotation.
    Any,
    /// Require a signed integer annotation.
    Signed,
    /// Require an unsigned integer annotation.
    Unsigned,
}

/// Result form produced by a generated rule helper.
#[derive(Debug, Deserialize)]
#[serde(tag = "kind")]
pub enum ResultKind {
    /// Assign the named emitted register to the matched IR value.
    #[serde(rename = "reg")]
    Reg {
        /// Name of the emitted register binding that becomes the rule result.
        name: String,
    },
    /// Record compare flags instead of assigning a register result.
    #[serde(rename = "cmp_flags")]
    CmpFlags,
    /// Emit instructions without producing a value result.
    #[serde(rename = "none")]
    None,
}

/// Reference to a register binding used by an emitted machine instruction.
#[derive(Debug, Deserialize)]
pub struct RegRef {
    /// How the generator should resolve the reference.
    pub kind: RegRefKind,
    /// Logical binding name within the rule.
    pub name: String,
    /// Optional fixed-register key used by `FreshFixed`.
    #[serde(default)]
    pub reg: Option<String>,
}

/// Strategy used to resolve a register reference during emission.
#[derive(Debug, Deserialize, Clone, Copy, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum RegRefKind {
    /// Reuse a named operand or previously-created temporary binding.
    Named,
    /// Allocate a fresh unconstrained virtual register.
    Fresh,
    /// Allocate a fresh virtual register constrained to a fixed physical register.
    FreshFixed,
}

/// A machine instruction emitted by a rule.
#[derive(Debug, Deserialize)]
pub struct EmitInst {
    /// Rust constructor name for the target machine-instruction variant.
    pub rust_ctor: String,
    /// Named fields to populate on the emitted constructor.
    pub fields: Vec<EmitField>,
}

/// Encoded source for an emitted operand-size field.
#[derive(Debug, Deserialize)]
#[serde(untagged)]
pub enum OpSizeValue {
    /// Use a fixed metadata key looked up in `metadata.maps.size`.
    Fixed(String),
    /// Derive the size from an operand annotation.
    FromAnnotation {
        /// Serialized discriminator currently expected to be `from_annotation`.
        kind: String,
        /// Operand binding whose annotation drives the emitted size.
        reg: String,
    },
}

/// One field assignment in an emitted machine instruction.
#[derive(Debug, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum EmitField {
    /// Populate a register-valued field from a rule binding.
    Reg {
        /// Struct field name in the emitted Rust constructor.
        name: String,
        /// Register binding to materialize for this field.
        #[serde(rename = "ref")]
        reg_ref: RegRef,
    },
    /// Populate an `OpSize` field.
    Size {
        /// Struct field name in the emitted Rust constructor.
        name: String,
        /// Size source to encode for this field.
        value: OpSizeValue,
    },
    /// Populate a condition-code field.
    Cc {
        /// Struct field name in the emitted Rust constructor.
        name: String,
        /// Metadata key to resolve through `metadata.maps.cc`.
        value: String,
    },
    /// Populate a field with a literal Rust expression.
    Literal {
        /// Struct field name in the emitted Rust constructor.
        name: String,
        /// Literal Rust expression copied into the generated output.
        value: String,
    },
}
