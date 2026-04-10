//! JSON schema matching the Lean-exported optimizer cleanup pass manifest.

use serde::Deserialize;

use crate::GenerateError;

#[derive(Debug, Deserialize)]
pub struct OptPassManifestSpec {
    pub format_version: u32,
    pub kind: String,
    #[serde(default)]
    pub local_families: Vec<OptPassFamily>,
    #[serde(default)]
    pub module_families: Vec<OptPassFamily>,
}

#[derive(Debug, Deserialize)]
pub struct OptPassFamily {
    pub name: String,
    pub runner: String,
    pub verification: CleanupPassVerification,
    #[serde(default)]
    pub lean_source: Option<String>,
}

#[derive(Debug, Clone, Copy, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum CleanupPassVerification {
    Verified,
    Legacy,
}

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
