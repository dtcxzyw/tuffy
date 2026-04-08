//! JSON schema matching the Lean-exported peephole fact transfer set.

use serde::Deserialize;

use crate::GenerateError;

#[derive(Debug, Deserialize)]
pub struct FactSpec {
    pub format_version: u32,
    pub kind: String,
    pub defaults: FactDefaults,
    #[serde(default)]
    pub result_rules: Vec<ResultFactRule>,
    #[serde(default)]
    pub inst_rules: Vec<InstFactRule>,
}

#[derive(Debug, Deserialize)]
pub struct FactDefaults {
    pub known_bits_forward: KnownBitsForwardKind,
    pub int_annotation_forward: IntAnnotationForwardKind,
    pub known_bits_backward: KnownBitsBackwardKind,
    pub int_annotation_backward: IntAnnotationBackwardKind,
}

#[derive(Debug, Deserialize)]
pub struct ResultFactRule {
    pub op: String,
    pub result: FactResult,
    pub known_bits_forward: KnownBitsForwardKind,
    pub int_annotation_forward: IntAnnotationForwardKind,
    pub proof_ref: String,
}

#[derive(Debug, Deserialize)]
pub struct InstFactRule {
    pub op: String,
    pub known_bits_backward: KnownBitsBackwardKind,
    pub int_annotation_backward: IntAnnotationBackwardKind,
    pub proof_ref: String,
}

#[derive(Debug, Clone, Copy, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum FactResult {
    Primary,
    Secondary,
}

#[derive(Debug, Clone, Copy, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum KnownBitsForwardKind {
    Unknown,
    Const,
    Select,
    BitAnd,
    BitOr,
    BitXor,
    Shl,
    Shr,
    Merge,
    SplitHi,
    SplitLo,
}

#[derive(Debug, Clone, Copy, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum IntAnnotationForwardKind {
    Unknown,
    Const,
    Select,
    BitAnd,
    BitOr,
    BitXor,
    SplitLo,
}

#[derive(Debug, Clone, Copy, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum KnownBitsBackwardKind {
    None,
    Select,
    BitAnd,
    BitOr,
    BitXor,
    Shl,
    Shr,
    Merge,
    Split,
}

#[derive(Debug, Clone, Copy, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum IntAnnotationBackwardKind {
    None,
    Select,
    Split,
}

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
