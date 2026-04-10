//! Generate Rust peephole matcher code from Lean-exported JSON rules.

mod at_use_codegen;
mod codegen;
mod facts_codegen;
mod facts_schema;
mod pass_manifest_codegen;
mod pass_manifest_schema;
mod schema;

use std::fmt;

pub use at_use_codegen::generate as generate_at_use;
pub use codegen::generate;
pub use facts_codegen::generate as generate_facts;
pub use facts_schema::FactSpec;
pub use pass_manifest_codegen::generate as generate_pass_manifest;
pub use pass_manifest_schema::OptPassManifestSpec;
pub use schema::PeepholeSpec;

#[derive(Debug)]
pub enum GenerateError {
    Json(serde_json::Error),
    UnsupportedFormatVersion(u32),
    UnsupportedFactsFormatVersion(u32),
    UnsupportedKind(String),
    UnsupportedFactsKind(String),
    UnsupportedPassManifestFormatVersion(u32),
    UnsupportedPassManifestKind(String),
    UnsupportedTransformKind(String),
    UnsupportedRootRewrite { rule: String, message: String },
    UnsupportedPattern(String),
    UnsupportedFactsRule(String),
    UnsupportedPassFamilyRunner(String),
    IllTypedReplacement { rule: String, message: String },
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
            GenerateError::UnsupportedFactsFormatVersion(version) => {
                write!(f, "unsupported peephole facts format version: {version}")
            }
            GenerateError::UnsupportedKind(kind) => {
                write!(f, "unsupported peephole kind: {kind}")
            }
            GenerateError::UnsupportedFactsKind(kind) => {
                write!(f, "unsupported peephole facts kind: {kind}")
            }
            GenerateError::UnsupportedPassManifestFormatVersion(version) => {
                write!(
                    f,
                    "unsupported optimizer pass manifest format version: {version}"
                )
            }
            GenerateError::UnsupportedPassManifestKind(kind) => {
                write!(f, "unsupported optimizer pass manifest kind: {kind}")
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
            GenerateError::UnsupportedFactsRule(msg) => {
                write!(f, "unsupported peephole fact rule: {msg}")
            }
            GenerateError::UnsupportedPassFamilyRunner(runner) => {
                write!(f, "unsupported optimizer pass family runner: {runner}")
            }
            GenerateError::IllTypedReplacement { rule, message } => {
                write!(f, "rule `{rule}` uses an ill-typed replacement: {message}")
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

pub fn load_facts_spec_from_json_str(json: &str) -> Result<FactSpec, GenerateError> {
    let spec: FactSpec = serde_json::from_str(json)?;
    facts_schema::validate_spec(&spec)?;
    Ok(spec)
}

pub fn load_pass_manifest_spec_from_json_str(
    json: &str,
) -> Result<OptPassManifestSpec, GenerateError> {
    let spec: OptPassManifestSpec = serde_json::from_str(json)?;
    pass_manifest_schema::validate_spec(&spec)?;
    Ok(spec)
}

#[cfg(test)]
mod tests {
    use super::{
        GenerateError, generate, generate_at_use, generate_facts, generate_pass_manifest,
        load_facts_spec_from_json_str, load_pass_manifest_spec_from_json_str,
        load_spec_from_json_str,
    };

    const SAMPLE_JSON: &str = r#"{
  "format_version": 4,
  "kind": "peephole",
  "rules": [
    {
      "name": "icmp_eq_select_bool_to_int_is_zero",
      "transform_kind": "equivalence",
      "proof_ref": "TuffyLean.Rewrites.icmp_eq_select_bool_to_int_is_zero",
      "side_conditions": [
        {
          "kind": "int_predicate",
          "binding": "cmp_const",
          "predicate": "is_one"
        }
      ],
      "rewrite": {
        "match_root": {
          "kind": "value",
          "root": {
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
        },
        "replacement": {
          "kind": "value",
          "value": {
            "kind": "bool_not",
            "value": { "kind": "binding", "name": "b" }
          }
        }
      }
    }
  ]
}"#;

    const CONST_FOLD_JSON: &str = r#"{
  "format_version": 4,
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

    const FACT_JSON: &str = r#"{
  "format_version": 4,
  "kind": "peephole",
  "rules": [
    {
      "name": "and_best_int_annotation_u1_lowbit_one",
      "transform_kind": "equivalence",
      "proof_ref": "TuffyLean.Rewrites.and_u1_lowbit_one_identity",
      "side_conditions": [
        {
          "kind": "best_int_annotation",
          "binding": "x",
          "annotation": { "kind": "unsigned", "bits": 1 }
        },
        {
          "kind": "known_one",
          "binding": "mask",
          "bit": 0
        }
      ],
      "rewrite": {
        "match_root": {
          "kind": "value",
          "root": {
            "kind": "inst",
            "op": "and",
            "attrs": [],
            "args": [
              { "kind": "capture", "name": "x", "ty": "int" },
              { "kind": "capture", "name": "mask", "ty": "int" }
            ]
          }
        },
        "replacement": {
          "kind": "value",
          "value": { "kind": "binding", "name": "x" }
        }
      }
    }
  ]
}"#;

    const FACT_TRANSFER_JSON: &str = r#"{
  "format_version": 1,
  "kind": "peephole_facts",
  "defaults": {
    "known_bits_forward": "unknown",
    "int_annotation_forward": "unknown",
    "known_bits_backward": "none",
    "int_annotation_backward": "none"
  },
  "result_rules": [
    {
      "op": "and",
      "result": "primary",
      "known_bits_forward": "bit_and",
      "int_annotation_forward": "bit_and",
      "proof_ref": "TuffyLean.Rewrites.Facts.knownBitsForward_bitAnd_sound"
    }
  ],
  "inst_rules": [
    {
      "op": "and",
      "known_bits_backward": "bit_and",
      "int_annotation_backward": "none",
      "proof_ref": "TuffyLean.Rewrites.Facts.knownBitsBackward_bitAnd_sound"
    }
  ]
}"#;

    const CANONICAL_BRIF_JSON: &str = r#"{
  "format_version": 4,
  "kind": "peephole",
  "rules": [
    {
      "name": "canonicalize_brif_intified_bool_compare",
      "transform_kind": "equivalence",
      "proof_ref": "TuffyLean.Rewrites.canonicalize_brif_intified_bool_compare_sound",
      "side_conditions": [],
      "rewrite": {
        "match_root": {
          "kind": "canonical_brif",
          "binding": "cond",
          "mode": "intified_bool_compare"
        },
        "replacement": {
          "kind": "terminator",
          "op": "brif",
          "operands": [{ "kind": "binding", "name": "cond" }],
          "successors": [0, 1]
        }
      }
    }
  ]
}"#;

    const PASS_MANIFEST_JSON: &str = r#"{
  "format_version": 1,
  "kind": "opt_pass_manifest",
  "local_families": [
    {
      "name": "peephole",
      "runner": "peephole",
      "verification": "verified",
      "lean_source": "TuffyLean.Rewrites.Basic"
    }
  ],
  "module_families": [
    {
      "name": "bulk_memory",
      "runner": "bulk_memory",
      "verification": "legacy"
    }
  ]
}"#;

    const AT_USE_JSON: &str = r#"{
  "format_version": 4,
  "kind": "peephole",
  "rules": [],
  "at_use_forward_rules": [
    {
      "op": "and",
      "known_bits_forward": "bit_and",
      "summary_forward": "bit_and",
      "proof_ref": "TuffyLean.Rewrites.Facts.resultFact_bitAnd_optimal"
    }
  ],
  "at_use_transforms": [
    {
      "name": "at_use_fold_icmp",
      "kind": "fold_icmp",
      "proof_ref": "TuffyLean.Rewrites.AtUse.foldICmp_sound"
    }
  ]
}"#;

    #[test]
    fn parses_and_generates_dispatch_code() {
        let spec = load_spec_from_json_str(SAMPLE_JSON).expect("sample JSON should parse");
        let rust = generate(&spec).expect("sample JSON should generate Rust");

        assert!(rust.contains("pub(super) const GENERATED_RULE_COUNT: usize = 1;"));
        assert!(rust.contains("fn try_apply_icmp_eq_select_bool_to_int_is_zero"));
        assert!(rust.contains("Op::Select(cond, t, e)"));
        assert!(rust.contains("ValueRewrite::Expr"));
        assert!(rust.contains("ReplacementExpr::BoolNot"));
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
    fn parses_and_generates_canonical_brif_code() {
        let spec =
            load_spec_from_json_str(CANONICAL_BRIF_JSON).expect("canonical brif JSON should parse");
        let rust = generate(&spec).expect("canonical brif JSON should generate Rust");

        assert!(rust.contains("try_match_canonical_brif"));
        assert!(rust.contains("CanonicalBrIfMode::IntifiedBoolCompare"));
        assert!(rust.contains("canonical_match.invert"));
    }

    #[test]
    fn parses_and_generates_fact_side_conditions() {
        let spec = load_spec_from_json_str(FACT_JSON).expect("fact JSON should parse");
        let rust = generate(&spec).expect("fact JSON should generate Rust");

        assert!(rust.contains("best_int_annotation_matches"));
        assert!(rust.contains("known_one(func, fact_cache, bind_mask?, 0)"));
        assert!(rust.contains("IntSignedness::Unsigned"));
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

    #[test]
    fn rejects_ill_typed_bool_not_replacement() {
        let json = SAMPLE_JSON.replace(
            "{ \"kind\": \"binding\", \"name\": \"b\" }",
            "{ \"kind\": \"binding\", \"name\": \"cmp_const\" }",
        );
        let err =
            load_spec_from_json_str(&json).expect_err("bool_not over int binding should fail");
        assert!(matches!(err, GenerateError::IllTypedReplacement { .. }));
    }

    #[test]
    fn parses_and_generates_fact_transfer_code() {
        let spec =
            load_facts_spec_from_json_str(FACT_TRANSFER_JSON).expect("fact transfer JSON parses");
        let rust = generate_facts(&spec).expect("fact transfer JSON generates Rust");

        assert!(rust.contains("generated_forward_int_facts"));
        assert!(rust.contains("forward_bitand"));
        assert!(rust.contains("generated_backward_int_facts"));
        assert!(rust.contains("backward_bitand"));
    }

    #[test]
    fn parses_and_generates_cleanup_pass_manifest() {
        let spec = load_pass_manifest_spec_from_json_str(PASS_MANIFEST_JSON)
            .expect("cleanup pass manifest parses");
        let rust = generate_pass_manifest(&spec).expect("cleanup pass manifest generates Rust");

        assert!(rust.contains("GENERATED_LOCAL_CLEANUP_PASS_COUNT: usize = 1;"));
        assert!(rust.contains("GENERATED_MODULE_CLEANUP_PASS_COUNT: usize = 1;"));
        assert!(rust.contains("run_generated_local_cleanup_passes"));
        assert!(rust.contains("crate::peephole::optimize_function(func)"));
        assert!(rust.contains("crate::bulk_memory::optimize_module(module, changed_functions)"));
    }

    #[test]
    fn parses_and_generates_at_use_code() {
        let spec = load_spec_from_json_str(AT_USE_JSON).expect("peephole JSON parses");
        let rust = generate_at_use(&spec).expect("at-use code generates from peephole JSON");

        assert!(rust.contains("generated_forward_at_use_facts"));
        assert!(rust.contains("GENERATED_AT_USE_TRANSFORMS"));
        assert!(rust.contains("AtUseTransformKind::FoldIcmp"));
    }
}
