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
    UnsupportedRootRewrite { rule: String, message: String },
    UnsupportedPattern(String),
    MissingReplacementBinding { rule: String, binding: String },
    MissingSideConditionBinding { rule: String, binding: String },
    IllTypedSideCondition { rule: String, message: String },
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
            GenerateError::UnsupportedRootRewrite { rule, message } => {
                write!(f, "rule `{rule}` uses unsupported root rewrite: {message}")
            }
            GenerateError::UnsupportedPattern(msg) => {
                write!(f, "unsupported peephole pattern: {msg}")
            }
            GenerateError::MissingReplacementBinding { rule, binding } => {
                write!(
                    f,
                    "rule `{rule}` references missing replacement binding `{binding}`"
                )
            }
            GenerateError::MissingSideConditionBinding { rule, binding } => {
                write!(
                    f,
                    "rule `{rule}` references missing side-condition binding `{binding}`"
                )
            }
            GenerateError::IllTypedSideCondition { rule, message } => {
                write!(
                    f,
                    "rule `{rule}` uses an ill-typed side condition: {message}"
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
  "format_version": 3,
  "kind": "peephole",
  "rules": [
    {
      "name": "brif_icmp_eq_select_bool_to_int_is_one",
      "transform_kind": "equivalence",
      "proof_ref": "TuffyLean.Rewrites.icmp_eq_select_bool_to_int_is_one",
      "side_conditions": [
        {
          "kind": "int_predicate",
          "binding": "cmp_const",
          "predicate": "is_one"
        }
      ],
      "rewrite": {
        "match_root": {
          "kind": "terminator",
          "op": "brif",
          "operands": [
            {
              "kind": "inst",
              "op": "icmp",
              "attrs": [{ "kind": "icmp_pred", "value": "eq" }],
              "args": [
                {
                  "kind": "inst",
                  "op": "select",
                  "attrs": [],
                  "args": [
                    { "kind": "capture", "name": "b", "ty": "bool" },
                    { "kind": "int_const", "value": "1" },
                    { "kind": "int_const", "value": "0" }
                  ]
                },
                { "kind": "int_const_binding", "name": "cmp_const" }
              ]
            }
          ],
          "successor_count": 2
        },
        "replacement": {
          "kind": "terminator",
          "op": "brif",
          "operands": [{ "kind": "binding", "name": "b" }],
          "successors": [0, 1]
        }
      }
    }
  ]
}"#;

    const CONST_FOLD_JSON: &str = r#"{
  "format_version": 3,
  "kind": "peephole",
  "rules": [
    {
      "name": "const_fold_add",
      "transform_kind": "equivalence",
      "proof_ref": "TuffyLean.Rewrites.constFoldValue_sound",
      "side_conditions": [],
      "rewrite": {
        "match_root": {
          "kind": "const_fold",
          "op": "add",
          "attrs": []
        },
        "replacement": {
          "kind": "const_fold"
        }
      }
    }
  ]
}"#;

    #[test]
    fn parses_and_generates_dispatch_code() {
        let spec = load_spec_from_json_str(SAMPLE_JSON).expect("sample JSON should parse");
        let rust = generate(&spec).expect("sample JSON should generate Rust");

        assert!(rust.contains("pub(super) const GENERATED_RULE_COUNT: usize = 1;"));
        assert!(rust.contains("fn try_apply_brif_icmp_eq_select_bool_to_int_is_one"));
        assert!(rust.contains("Op::Select(cond, t, e)"));
        assert!(rust.contains("apply_terminator_root_rewrite"));
        assert!(rust.contains("TerminatorOpcode::BrIf"));
        assert!(rust.contains("bound_int_constant(func, bind_cmp_const?)"));
    }

    #[test]
    fn parses_and_generates_const_fold_dispatch_code() {
        let spec = load_spec_from_json_str(CONST_FOLD_JSON).expect("const-fold JSON should parse");
        let rust = generate(&spec).expect("const-fold JSON should generate Rust");

        assert!(rust.contains("fn try_apply_const_fold_add"));
        assert!(rust.contains("try_fold_constant_root(func, root_idx, ConstFoldKind::Add)"));
        assert!(rust.contains("fold_match.replacement"));
    }

    #[test]
    fn rejects_missing_side_condition_binding() {
        let json = SAMPLE_JSON.replace("\"binding\": \"cmp_const\"", "\"binding\": \"missing\"");
        let err =
            load_spec_from_json_str(&json).expect_err("missing side-condition binding should fail");
        assert!(matches!(
            err,
            GenerateError::MissingSideConditionBinding { .. }
        ));
    }

    #[test]
    fn rejects_ill_typed_side_condition_binding() {
        let json = SAMPLE_JSON.replace(
            "{ \"kind\": \"int_const_binding\", \"name\": \"cmp_const\" }",
            "{ \"kind\": \"capture\", \"name\": \"cmp_const\", \"ty\": \"int\" }",
        );
        let err = load_spec_from_json_str(&json)
            .expect_err("non-const side-condition binding should fail");
        assert!(matches!(err, GenerateError::IllTypedSideCondition { .. }));
    }
}
