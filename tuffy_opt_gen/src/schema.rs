//! JSON schema matching the Lean-exported peephole rule set.

use std::collections::BTreeMap;

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
    pub side_conditions: Vec<SideCondition>,
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
    ConstFold {
        op: String,
        #[serde(default)]
        attrs: Vec<PatternAttr>,
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
    ConstFold,
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

#[derive(Debug, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum SideCondition {
    IntPredicate {
        binding: String,
        predicate: IntPredicate,
    },
    AllOf {
        conditions: Vec<SideCondition>,
    },
    AnyOf {
        conditions: Vec<SideCondition>,
    },
    Not {
        condition: Box<SideCondition>,
    },
}

#[derive(Debug, Clone, Copy, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum IntPredicate {
    #[serde(rename = "is_zero")]
    Zero,
    #[serde(rename = "is_one")]
    One,
    #[serde(rename = "is_odd")]
    Odd,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum BindingKind {
    Value,
    IntConst,
}

pub fn validate_spec(spec: &PeepholeSpec) -> Result<(), GenerateError> {
    if spec.format_version != 3 {
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

        let mut bindings = Vec::new();
        let mut binding_kinds = BTreeMap::new();
        match (&rule.rewrite.match_root, &rule.rewrite.replacement) {
            (MatchRoot::Value { root }, RootReplacement::Value { value: replacement }) => {
                root.collect_bindings(&mut bindings);
                root.collect_binding_kinds(&mut binding_kinds);
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
                    operand.collect_binding_kinds(&mut binding_kinds);
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
            (MatchRoot::ConstFold { op, attrs }, RootReplacement::ConstFold) => {
                if !rule.side_conditions.is_empty() {
                    return Err(GenerateError::UnsupportedRootRewrite {
                        rule: rule.name.clone(),
                        message: "const-fold roots do not support side conditions".to_string(),
                    });
                }
                validate_const_fold(op, attrs, &rule.name)?;
            }
            (MatchRoot::Value { .. }, RootReplacement::Terminator { .. })
            | (MatchRoot::Value { .. }, RootReplacement::ConstFold)
            | (MatchRoot::Terminator { .. }, RootReplacement::Value { .. })
            | (MatchRoot::Terminator { .. }, RootReplacement::ConstFold)
            | (MatchRoot::ConstFold { .. }, RootReplacement::Value { .. })
            | (MatchRoot::ConstFold { .. }, RootReplacement::Terminator { .. }) => {
                return Err(GenerateError::UnsupportedRootRewrite {
                    rule: rule.name.clone(),
                    message: "root kind and replacement kind must match".to_string(),
                });
            }
        }

        for side_condition in &rule.side_conditions {
            validate_side_condition(side_condition, &binding_kinds, &rule.name)?;
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

impl Pattern {
    fn collect_binding_kinds(&self, out: &mut BTreeMap<String, BindingKind>) {
        match self {
            Pattern::Capture { name, .. } | Pattern::Bind { name, .. } => {
                register_binding_kind(out, name, BindingKind::Value);
                if let Pattern::Bind { pattern, .. } = self {
                    pattern.collect_binding_kinds(out);
                }
            }
            Pattern::IntConstBinding { name } => {
                register_binding_kind(out, name, BindingKind::IntConst);
            }
            Pattern::IntConst { .. } => {}
            Pattern::Inst { args, .. } => {
                for arg in args {
                    arg.collect_binding_kinds(out);
                }
            }
        }
    }
}

fn register_binding_kind(out: &mut BTreeMap<String, BindingKind>, name: &str, kind: BindingKind) {
    match out.get_mut(name) {
        Some(existing) => {
            if kind == BindingKind::IntConst {
                *existing = BindingKind::IntConst;
            }
        }
        None => {
            out.insert(name.to_string(), kind);
        }
    }
}

fn validate_side_condition(
    condition: &SideCondition,
    binding_kinds: &BTreeMap<String, BindingKind>,
    rule: &str,
) -> Result<(), GenerateError> {
    match condition {
        SideCondition::IntPredicate {
            binding,
            predicate: _,
        } => match binding_kinds.get(binding) {
            Some(BindingKind::IntConst) => Ok(()),
            Some(BindingKind::Value) => Err(GenerateError::IllTypedSideCondition {
                rule: rule.to_string(),
                message: format!(
                    "side condition binding `{binding}` must come from `int_const_binding`"
                ),
            }),
            None => Err(GenerateError::MissingSideConditionBinding {
                rule: rule.to_string(),
                binding: binding.clone(),
            }),
        },
        SideCondition::AllOf { conditions } | SideCondition::AnyOf { conditions } => {
            for condition in conditions {
                validate_side_condition(condition, binding_kinds, rule)?;
            }
            Ok(())
        }
        SideCondition::Not { condition } => validate_side_condition(condition, binding_kinds, rule),
    }
}

fn validate_const_fold(op: &str, attrs: &[PatternAttr], rule: &str) -> Result<(), GenerateError> {
    match op {
        "add"
        | "sub"
        | "mul"
        | "div"
        | "rem"
        | "and"
        | "or"
        | "xor"
        | "band"
        | "bor"
        | "bxor"
        | "shl"
        | "shr"
        | "min"
        | "max"
        | "count_ones"
        | "count_leading_zeros"
        | "count_trailing_zeros"
        | "bswap"
        | "bit_reverse"
        | "rotate_left"
        | "rotate_right"
        | "select"
            if attrs.is_empty() =>
        {
            Ok(())
        }
        "icmp" => match attrs {
            [PatternAttr::IcmpPred { value }]
                if matches!(value.as_str(), "eq" | "ne" | "lt" | "le" | "gt" | "ge") =>
            {
                Ok(())
            }
            [PatternAttr::IcmpPred { value }] => Err(GenerateError::UnsupportedPattern(format!(
                "unsupported const-fold icmp predicate `{value}`"
            ))),
            [] => Err(GenerateError::UnsupportedRootRewrite {
                rule: rule.to_string(),
                message: "const-fold icmp requires a predicate attribute".to_string(),
            }),
            _ => Err(GenerateError::UnsupportedRootRewrite {
                rule: rule.to_string(),
                message: "const-fold icmp uses unsupported attribute set".to_string(),
            }),
        },
        _ if attrs.is_empty() => Err(GenerateError::UnsupportedPattern(format!(
            "unsupported const-fold op `{op}`"
        ))),
        _ => Err(GenerateError::UnsupportedRootRewrite {
            rule: rule.to_string(),
            message: format!("const-fold op `{op}` uses unsupported attributes"),
        }),
    }
}
