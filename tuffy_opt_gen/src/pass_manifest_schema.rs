//! JSON schema matching the Lean-exported optimizer cleanup pass manifest.

use serde::Deserialize;

use crate::GenerateError;

/// Top-level cleanup-pass manifest exported from Lean.
#[derive(Debug, Deserialize)]
pub struct OptPassManifestSpec {
    /// Schema format version expected by the generator.
    pub format_version: u32,
    /// Schema kind discriminator.
    pub kind: String,
    /// Cleanup families that run per function.
    #[serde(default)]
    pub local_families: Vec<OptPassFamily>,
    /// Cleanup families that run per module.
    #[serde(default)]
    pub module_families: Vec<OptPassFamily>,
}

/// One cleanup-pass family entry in the generated manifest.
#[derive(Debug, Deserialize)]
pub struct OptPassFamily {
    /// User-visible family name.
    pub name: String,
    /// Runtime dispatcher key used to invoke the family.
    pub runner: String,
    /// Whether the family is Lean-verified or legacy handwritten logic.
    pub verification: CleanupPassVerification,
    /// Optional Lean source path that produced the family.
    #[serde(default)]
    pub lean_source: Option<String>,
}

/// Verification status attached to a cleanup-pass family.
#[derive(Debug, Clone, Copy, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum CleanupPassVerification {
    /// The family is backed by a Lean proof.
    Verified,
    /// The family is still legacy handwritten logic.
    Legacy,
}

/// Validate a decoded cleanup-pass manifest.
///
/// # Errors
///
/// Returns an error if the schema version or kind is not supported.
pub fn validate_spec(spec: &OptPassManifestSpec) -> Result<(), GenerateError> {
    if spec.format_version != 1 {
        return Err(GenerateError::UnsupportedPassManifestFormatVersion(
            spec.format_version,
        ));
    }
    if spec.kind != "opt_pass_manifest" {
        return Err(GenerateError::UnsupportedPassManifestKind(
            spec.kind.clone(),
        ));
    }
    Ok(())
}
