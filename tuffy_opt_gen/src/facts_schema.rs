//! JSON schema matching the Lean-exported peephole fact transfer set.

use serde::Deserialize;

use crate::GenerateError;

/// Top-level peephole fact-transfer specification exported from Lean.
#[derive(Debug, Deserialize)]
pub struct FactSpec {
    /// Schema format version expected by the generator.
    pub format_version: u32,
    /// Schema kind discriminator.
    pub kind: String,
    /// Default transfer functions used when no opcode-specific rule matches.
    pub defaults: FactDefaults,
    /// Forward rules keyed by result kind and opcode.
    #[serde(default)]
    pub result_rules: Vec<ResultFactRule>,
    /// Backward rules keyed by opcode.
    #[serde(default)]
    pub inst_rules: Vec<InstFactRule>,
}

/// Default transfer functions used by the generated runtime.
#[derive(Debug, Deserialize)]
pub struct FactDefaults {
    /// Default known-bits forward transfer.
    pub known_bits_forward: KnownBitsForwardKind,
    /// Default int-annotation forward transfer.
    pub int_annotation_forward: IntAnnotationForwardKind,
    /// Default known-bits backward transfer.
    pub known_bits_backward: KnownBitsBackwardKind,
    /// Default int-annotation backward transfer.
    pub int_annotation_backward: IntAnnotationBackwardKind,
}

/// Opcode-specific forward rule for one instruction result.
#[derive(Debug, Deserialize)]
pub struct ResultFactRule {
    /// Opcode handled by this rule.
    pub op: String,
    /// Result slot described by the rule.
    pub result: FactResult,
    /// Known-bits forward transfer to apply.
    pub known_bits_forward: KnownBitsForwardKind,
    /// Int-annotation forward transfer to apply.
    pub int_annotation_forward: IntAnnotationForwardKind,
    /// Lean theorem or definition that justifies the transfer rule.
    pub proof_ref: String,
}

/// Opcode-specific backward rule for an instruction.
#[derive(Debug, Deserialize)]
pub struct InstFactRule {
    /// Opcode handled by this rule.
    pub op: String,
    /// Known-bits backward transfer to apply.
    pub known_bits_backward: KnownBitsBackwardKind,
    /// Int-annotation backward transfer to apply.
    pub int_annotation_backward: IntAnnotationBackwardKind,
    /// Lean theorem or definition that justifies the transfer rule.
    pub proof_ref: String,
}

/// Result slot selected by a forward fact rule.
#[derive(Debug, Clone, Copy, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum FactResult {
    /// The rule targets the primary result.
    Primary,
    /// The rule targets the secondary result.
    Secondary,
}

/// Known-bits forward transfer function.
#[derive(Debug, Clone, Copy, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum KnownBitsForwardKind {
    /// Produce no opcode-specific known-bits information.
    Unknown,
    /// Derive facts from a constant result.
    Const,
    /// Merge facts from a `select`.
    Select,
    /// Derive facts from a bitwise `and`.
    BitAnd,
    /// Derive facts from a bitwise `or`.
    BitOr,
    /// Derive facts from a bitwise `xor`.
    BitXor,
    /// Derive facts from a shift-left.
    Shl,
    /// Derive facts from a shift-right.
    Shr,
    /// Derive facts from a `merge`.
    Merge,
    /// Derive facts for the high result of `split`.
    SplitHi,
    /// Derive facts for the low result of `split`.
    SplitLo,
}

/// Int-annotation forward transfer function.
#[derive(Debug, Clone, Copy, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum IntAnnotationForwardKind {
    /// Produce no opcode-specific annotation.
    Unknown,
    /// Derive an annotation from a constant result.
    Const,
    /// Merge annotations from a `select`.
    Select,
    /// Derive annotations from a bitwise `and`.
    BitAnd,
    /// Derive annotations from a bitwise `or`.
    BitOr,
    /// Derive annotations from a bitwise `xor`.
    BitXor,
    /// Derive annotations for the low result of `split`.
    SplitLo,
}

/// Known-bits backward transfer function.
#[derive(Debug, Clone, Copy, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum KnownBitsBackwardKind {
    /// Produce no backward update.
    None,
    /// Push known bits backward through a `select`.
    Select,
    /// Push known bits backward through a bitwise `and`.
    BitAnd,
    /// Push known bits backward through a bitwise `or`.
    BitOr,
    /// Push known bits backward through a bitwise `xor`.
    BitXor,
    /// Push known bits backward through a shift-left.
    Shl,
    /// Push known bits backward through a shift-right.
    Shr,
    /// Push known bits backward through a `merge`.
    Merge,
    /// Push known bits backward through a `split`.
    Split,
}

/// Int-annotation backward transfer function.
#[derive(Debug, Clone, Copy, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum IntAnnotationBackwardKind {
    /// Produce no backward annotation update.
    None,
    /// Push annotations backward through a `select`.
    Select,
    /// Push annotations backward through a `split`.
    Split,
}

/// Validate a decoded fact-transfer specification.
///
/// # Errors
///
/// Returns an error if the schema version or kind is not supported.
pub fn validate_spec(spec: &FactSpec) -> Result<(), GenerateError> {
    if spec.format_version != 1 {
        return Err(GenerateError::UnsupportedFactsFormatVersion(
            spec.format_version,
        ));
    }
    if spec.kind != "peephole_facts" {
        return Err(GenerateError::UnsupportedFactsKind(spec.kind.clone()));
    }
    Ok(())
}
