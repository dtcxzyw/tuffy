//! Generate Rust peephole matcher code from Lean-exported JSON rules.

mod codegen;
mod schema;

use std::fmt;

pub use codegen::generate;
pub use schema::PeepholeSpec;

#[derive(Debug)]
pub enum GenerateError {
    Json(serde_json::Error),
    UnsupportedFormatVersion(u32),
    UnsupportedKind(String),
    UnsupportedTransformKind(String),
    UnsupportedSideConditions {
        rule: String,
        conditions: Vec<String>,
    },
    MissingReplacementBinding {
        rule: String,
        binding: String,
    },
    InvalidIntConstant(String),
}

impl fmt::Display for GenerateError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            GenerateError::Json(err) => write!(f, "failed to parse peephole JSON: {err}"),
            GenerateError::UnsupportedFormatVersion(version) => {
                write!(f, "unsupported peephole format version: {version}")
            }
            GenerateError::UnsupportedKind(kind) => {
                write!(f, "unsupported peephole kind: {kind}")
            }
            GenerateError::UnsupportedTransformKind(kind) => {
                write!(f, "unsupported transform kind: {kind}")
            }
            GenerateError::UnsupportedSideConditions { rule, conditions } => {
                write!(
                    f,
                    "rule `{rule}` uses unsupported side conditions: {}",
                    conditions.join(", ")
                )
            }
            GenerateError::MissingReplacementBinding { rule, binding } => {
                write!(
                    f,
                    "rule `{rule}` references missing replacement binding `{binding}`"
                )
            }
            GenerateError::InvalidIntConstant(value) => {
                write!(f, "invalid integer constant in peephole rule: {value}")
            }
        }
    }
}

impl std::error::Error for GenerateError {}

impl From<serde_json::Error> for GenerateError {
    fn from(value: serde_json::Error) -> Self {
        Self::Json(value)
    }
}

pub fn load_spec_from_json_str(json: &str) -> Result<PeepholeSpec, GenerateError> {
    let spec: PeepholeSpec = serde_json::from_str(json)?;
    schema::validate_spec(&spec)?;
    Ok(spec)
}

#[cfg(test)]
mod tests {
    use super::{GenerateError, generate, load_spec_from_json_str};

    const SAMPLE_JSON: &str = r#"{
  "format_version": 1,
  "kind": "peephole",
  "rules": [
    {
      "name": "brif_icmp_eq_select_bool_to_int_one",
      "transform_kind": "equivalence",
      "proof_ref": "TuffyLean.Rewrites.icmp_eq_select_bool_to_int_one",
      "side_conditions": [],
      "rewrite": {
        "kind": "brif",
        "condition": {
          "kind": "inst",
          "op": "icmp_eq",
          "args": [
            {
              "kind": "inst",
              "op": "select",
              "args": [
                { "kind": "capture", "name": "b", "ty": "bool" },
                { "kind": "int_const", "value": "1" },
                { "kind": "int_const", "value": "0" }
              ]
            },
            { "kind": "int_const", "value": "1" }
          ]
        },
        "replacement": { "kind": "binding", "name": "b" },
        "invert": false
      }
    }
  ]
}"#;

    #[test]
    fn parses_and_generates_dispatch_code() {
        let spec = load_spec_from_json_str(SAMPLE_JSON).expect("sample JSON should parse");
        let rust = generate(&spec).expect("sample JSON should generate Rust");

        assert!(rust.contains("pub(super) const GENERATED_RULE_COUNT: usize = 1;"));
        assert!(rust.contains("fn try_apply_brif_icmp_eq_select_bool_to_int_one"));
        assert!(rust.contains("Op::Select(cond, t, e)"));
        assert!(rust.contains("apply_brif_rewrite"));
    }

    #[test]
    fn rejects_unsupported_side_conditions() {
        let json = SAMPLE_JSON.replace(
            "\"side_conditions\": []",
            "\"side_conditions\": [\"single_use\"]",
        );
        let err = load_spec_from_json_str(&json).expect_err("side conditions should be rejected");
        assert!(matches!(
            err,
            GenerateError::UnsupportedSideConditions { .. }
        ));
    }
}
