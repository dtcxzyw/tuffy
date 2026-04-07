//! JSON schema matching the Lean-exported peephole rule set.

use num_bigint::BigInt;
use serde::Deserialize;

use crate::GenerateError;

#[derive(Debug, Deserialize)]
pub struct PeepholeSpec {
    pub format_version: u32,
    pub kind: String,
    pub rules: Vec<PeepholeRule>,
}

#[derive(Debug, Deserialize)]
pub struct PeepholeRule {
    pub name: String,
    pub transform_kind: String,
    pub proof_ref: String,
    #[serde(default)]
    pub side_conditions: Vec<String>,
    pub rewrite: RewriteBody,
}

#[derive(Debug, Deserialize)]
pub struct RewriteBody {
    pub match_root: MatchRoot,
    pub replacement: RootReplacement,
}

#[derive(Debug, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum MatchRoot {
    Value {
        root: Pattern,
    },
    Terminator {
        op: String,
        operands: Vec<Pattern>,
        successor_count: usize,
    },
}

#[derive(Debug, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum RootReplacement {
    Value {
        value: Replacement,
    },
    Terminator {
        op: String,
        operands: Vec<Replacement>,
        successors: Vec<usize>,
    },
}

#[derive(Debug, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum Replacement {
    Binding { name: String },
}

impl Replacement {
    pub fn binding_name(&self) -> &str {
        match self {
            Replacement::Binding { name } => name,
        }
    }
}

#[derive(Debug, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum Pattern {
    Capture {
        name: String,
        #[serde(default)]
        ty: Option<ValueType>,
    },
    Bind {
        name: String,
        pattern: Box<Pattern>,
    },
    IntConst {
        value: String,
    },
    IntConstBinding {
        name: String,
    },
    Inst {
        op: String,
        #[serde(default)]
        attrs: Vec<PatternAttr>,
        args: Vec<Pattern>,
    },
}

impl Pattern {
    pub fn collect_bindings<'a>(&'a self, out: &mut Vec<&'a str>) {
        match self {
            Pattern::Capture { name, .. }
            | Pattern::Bind { name, .. }
            | Pattern::IntConstBinding { name } => {
                if !out.contains(&name.as_str()) {
                    out.push(name);
                }
                if let Pattern::Bind { pattern, .. } = self {
                    pattern.collect_bindings(out);
                }
            }
            Pattern::IntConst { .. } => {}
            Pattern::Inst { args, .. } => {
                for arg in args {
                    arg.collect_bindings(out);
                }
            }
        }
    }
}

#[derive(Debug, Clone, Copy, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum ValueType {
    Int,
    Bool,
}

#[derive(Debug, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum PatternAttr {
    IcmpPred { value: String },
}

pub fn validate_spec(spec: &PeepholeSpec) -> Result<(), GenerateError> {
    if spec.format_version != 1 {
        return Err(GenerateError::UnsupportedFormatVersion(spec.format_version));
    }
    if spec.kind != "peephole" {
        return Err(GenerateError::UnsupportedKind(spec.kind.clone()));
    }

    for rule in &spec.rules {
        if rule.transform_kind != "equivalence" {
            return Err(GenerateError::UnsupportedTransformKind(
                rule.transform_kind.clone(),
            ));
        }
        if !rule.side_conditions.is_empty() {
            return Err(GenerateError::UnsupportedSideConditions {
                rule: rule.name.clone(),
                conditions: rule.side_conditions.clone(),
            });
        }

        let mut bindings = Vec::new();
        match (&rule.rewrite.match_root, &rule.rewrite.replacement) {
            (MatchRoot::Value { root }, RootReplacement::Value { value: replacement }) => {
                root.collect_bindings(&mut bindings);
                if !bindings.contains(&replacement.binding_name()) {
                    return Err(GenerateError::MissingReplacementBinding {
                        rule: rule.name.clone(),
                        binding: replacement.binding_name().to_string(),
                    });
                }
                validate_pattern(root)?;
            }
            (
                MatchRoot::Terminator {
                    op,
                    operands,
                    successor_count,
                },
                RootReplacement::Terminator {
                    op: replacement_op,
                    operands: replacement_operands,
                    successors,
                },
            ) => {
                for operand in operands {
                    operand.collect_bindings(&mut bindings);
                    validate_pattern(operand)?;
                }
                for replacement in replacement_operands {
                    if !bindings.contains(&replacement.binding_name()) {
                        return Err(GenerateError::MissingReplacementBinding {
                            rule: rule.name.clone(),
                            binding: replacement.binding_name().to_string(),
                        });
                    }
                }
                if op != replacement_op {
                    return Err(GenerateError::UnsupportedRootRewrite {
                        rule: rule.name.clone(),
                        message: format!(
                            "terminator root op `{op}` cannot be replaced with `{replacement_op}`"
                        ),
                    });
                }
                for successor in successors {
                    if *successor >= *successor_count {
                        return Err(GenerateError::UnsupportedRootRewrite {
                            rule: rule.name.clone(),
                            message: format!(
                                "replacement successor index {successor} is out of range for {successor_count} matched successors"
                            ),
                        });
                    }
                }
            }
            (MatchRoot::Value { .. }, RootReplacement::Terminator { .. })
            | (MatchRoot::Terminator { .. }, RootReplacement::Value { .. }) => {
                return Err(GenerateError::UnsupportedRootRewrite {
                    rule: rule.name.clone(),
                    message: "root kind and replacement kind must match".to_string(),
                });
            }
        }
    }

    Ok(())
}

fn validate_pattern(pattern: &Pattern) -> Result<(), GenerateError> {
    match pattern {
        Pattern::Capture { .. } | Pattern::IntConstBinding { .. } => Ok(()),
        Pattern::Bind { pattern, .. } => validate_pattern(pattern),
        Pattern::IntConst { value } => {
            let _: BigInt = value
                .parse()
                .map_err(|_| GenerateError::InvalidIntConstant(value.clone()))?;
            Ok(())
        }
        Pattern::Inst { args, .. } => {
            for arg in args {
                validate_pattern(arg)?;
            }
            Ok(())
        }
    }
}
