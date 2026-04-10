//! JSON schema matching the Lean-exported at-use analysis spec.

use serde::Deserialize;

use crate::GenerateError;

#[derive(Debug, Deserialize)]
pub struct AtUseSpec {
    pub format_version: u32,
    pub kind: String,
    #[serde(default)]
    pub forward_rules: Vec<ForwardRule>,
    #[serde(default)]
    pub transforms: Vec<Transform>,
}

#[derive(Debug, Deserialize)]
pub struct ForwardRule {
    pub op: String,
    pub known_bits_forward: KnownBitsForwardKind,
    pub summary_forward: SummaryForwardKind,
    pub proof_ref: String,
}

#[derive(Debug, Deserialize)]
pub struct Transform {
    pub name: String,
    pub kind: TransformKind,
    pub proof_ref: String,
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
}

#[derive(Debug, Clone, Copy, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum SummaryForwardKind {
    Unknown,
    Const,
    Select,
    BitAnd,
    BitOr,
    BitXor,
}

#[derive(Debug, Clone, Copy, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum TransformKind {
    FoldIcmp,
    FoldBrIf,
    StrengthenOperand,
    StrengthenResult,
}

pub fn validate_spec(spec: &AtUseSpec) -> Result<(), GenerateError> {
    if spec.format_version != 1 {
        return Err(GenerateError::UnsupportedAtUseFormatVersion(
            spec.format_version,
        ));
    }
    if spec.kind != "at_use" {
        return Err(GenerateError::UnsupportedAtUseKind(spec.kind.clone()));
    }
    Ok(())
}
