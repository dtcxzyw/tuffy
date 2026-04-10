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
    #[serde(default)]
    pub at_use_forward_rules: Vec<AtUseForwardRule>,
    #[serde(default)]
    pub at_use_transforms: Vec<AtUseTransform>,
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
pub struct AtUseForwardRule {
    pub op: String,
    pub known_bits_forward: AtUseKnownBitsForwardKind,
    pub summary_forward: AtUseSummaryForwardKind,
    pub proof_ref: String,
}

#[derive(Debug, Deserialize)]
pub struct AtUseTransform {
    pub name: String,
    pub kind: AtUseTransformKind,
    pub proof_ref: String,
}

#[derive(Debug, Clone, Copy, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum AtUseKnownBitsForwardKind {
    Unknown,
    Const,
    Select,
    BitAnd,
    BitOr,
    BitXor,
}

#[derive(Debug, Clone, Copy, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum AtUseSummaryForwardKind {
    Unknown,
    Const,
    Select,
    BitAnd,
    BitOr,
    BitXor,
}

#[derive(Debug, Clone, Copy, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum AtUseTransformKind {
    FoldIcmp,
    FoldBrIf,
    StrengthenOperand,
    StrengthenResult,
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
    #[serde(rename = "canonical_brif")]
    CanonicalBrIf {
        binding: String,
        mode: CanonicalBrIfMode,
    },
    ConstFold {
        op: String,
        #[serde(default)]
        attrs: Vec<PatternAttr>,
    },
}

#[derive(Debug, Clone, Copy, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum CanonicalBrIfMode {
    BoolXorConst,
    IntifiedBoolCompare,
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
    BoolConst { value: bool },
    BoolNot { value: Box<Replacement> },
}

impl Replacement {
    fn collect_bindings<'a>(&'a self, out: &mut Vec<&'a str>) {
        match self {
            Replacement::Binding { name } => {
                if !out.contains(&name.as_str()) {
                    out.push(name);
                }
            }
            Replacement::BoolConst { .. } => {}
            Replacement::BoolNot { value } => value.collect_bindings(out),
        }
    }

    pub fn binding_name(&self) -> Option<&str> {
        match self {
            Replacement::Binding { name } => Some(name),
            Replacement::BoolConst { .. } | Replacement::BoolNot { .. } => None,
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

    fn inferred_value_type(&self) -> Option<ValueType> {
        match self {
            Pattern::Capture { ty, .. } => *ty,
            Pattern::Bind { pattern, .. } => pattern.inferred_value_type(),
            Pattern::IntConst { .. } | Pattern::IntConstBinding { .. } => Some(ValueType::Int),
            Pattern::Inst { op, args, .. } => match op.as_str() {
                "and" | "xor" => Some(ValueType::Int),
                "icmp" => Some(ValueType::Bool),
                "select" => {
                    if args.len() != 3 {
                        return None;
                    }
                    let true_ty = args[1].inferred_value_type()?;
                    let false_ty = args[2].inferred_value_type()?;
                    if true_ty == false_ty {
                        Some(true_ty)
                    } else {
                        None
                    }
                }
                _ => None,
            },
        }
    }

    fn collect_binding_kinds(&self, out: &mut BTreeMap<String, BindingKind>) {
        match self {
            Pattern::Capture { name, ty } => {
                register_binding_kind(out, name, BindingKind::from_value_type(*ty));
            }
            Pattern::Bind { name, pattern } => {
                register_binding_kind(
                    out,
                    name,
                    BindingKind::from_value_type(pattern.inferred_value_type()),
                );
                pattern.collect_binding_kinds(out);
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

#[derive(Debug, Clone, Copy, Deserialize, PartialEq, Eq)]
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
    BestIntAnnotation {
        binding: String,
        annotation: IntAnnotationSpec,
    },
    KnownOne {
        binding: String,
        bit: u32,
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

#[derive(Debug, Clone, Copy, Deserialize, PartialEq, Eq)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum IntAnnotationSpec {
    Signed { bits: u32 },
    Unsigned { bits: u32 },
    DontCare { bits: u32 },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum BindingKind {
    UnknownValue,
    IntValue,
    BoolValue,
    IntConst,
}

impl BindingKind {
    fn from_value_type(ty: Option<ValueType>) -> Self {
        match ty {
            Some(ValueType::Int) => Self::IntValue,
            Some(ValueType::Bool) => Self::BoolValue,
            None => Self::UnknownValue,
        }
    }

    fn value_type(self) -> Option<ValueType> {
        match self {
            BindingKind::UnknownValue => None,
            BindingKind::IntValue | BindingKind::IntConst => Some(ValueType::Int),
            BindingKind::BoolValue => Some(ValueType::Bool),
        }
    }
}

pub fn validate_spec(spec: &PeepholeSpec) -> Result<(), GenerateError> {
    if spec.format_version != 4 {
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
                validate_pattern(root)?;
                validate_value_replacement(
                    root,
                    replacement,
                    &bindings,
                    &binding_kinds,
                    &rule.name,
                )?;
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
                    validate_terminator_replacement_operand(replacement, &bindings, &rule.name)?;
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
            (
                MatchRoot::CanonicalBrIf { binding, .. },
                RootReplacement::Terminator {
                    op,
                    operands,
                    successors,
                },
            ) => {
                bindings.push(binding.as_str());
                register_binding_kind(&mut binding_kinds, binding, BindingKind::BoolValue);
                if op != "brif" {
                    return Err(GenerateError::UnsupportedRootRewrite {
                        rule: rule.name.clone(),
                        message: format!(
                            "canonical brif root cannot be replaced with terminator op `{op}`"
                        ),
                    });
                }
                if operands.len() != 1 {
                    return Err(GenerateError::UnsupportedRootRewrite {
                        rule: rule.name.clone(),
                        message: "canonical brif replacement expects exactly one operand"
                            .to_string(),
                    });
                }
                validate_terminator_replacement_operand(&operands[0], &bindings, &rule.name)?;
                if successors.len() != 2
                    || !successors
                        .iter()
                        .all(|successor| *successor == 0 || *successor == 1)
                {
                    return Err(GenerateError::UnsupportedRootRewrite {
                        rule: rule.name.clone(),
                        message:
                            "canonical brif replacement expects two successor indices in {0, 1}"
                                .to_string(),
                    });
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
            | (MatchRoot::CanonicalBrIf { .. }, RootReplacement::Value { .. })
            | (MatchRoot::CanonicalBrIf { .. }, RootReplacement::ConstFold)
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

fn register_binding_kind(out: &mut BTreeMap<String, BindingKind>, name: &str, kind: BindingKind) {
    match out.get_mut(name) {
        Some(existing) => match (*existing, kind) {
            (BindingKind::UnknownValue, new_kind) if new_kind != BindingKind::UnknownValue => {
                *existing = new_kind;
            }
            (_, BindingKind::IntConst) => {
                *existing = BindingKind::IntConst;
            }
            _ => {}
        },
        None => {
            out.insert(name.to_string(), kind);
        }
    }
}

fn validate_value_replacement(
    root: &Pattern,
    replacement: &Replacement,
    bindings: &[&str],
    binding_kinds: &BTreeMap<String, BindingKind>,
    rule: &str,
) -> Result<(), GenerateError> {
    validate_replacement_bindings(replacement, bindings, rule)?;
    let root_ty = root.inferred_value_type();
    let replacement_ty = replacement_value_type(replacement, binding_kinds, rule)?;
    if let (Some(root_ty), Some(replacement_ty)) = (root_ty, replacement_ty)
        && root_ty != replacement_ty
    {
        return Err(GenerateError::IllTypedReplacement {
            rule: rule.to_string(),
            message: format!(
                "value-root replacement has type {:?}, but the matched root has type {:?}",
                replacement_ty, root_ty
            ),
        });
    }
    Ok(())
}

fn validate_terminator_replacement_operand(
    replacement: &Replacement,
    bindings: &[&str],
    rule: &str,
) -> Result<(), GenerateError> {
    let Some(binding) = replacement.binding_name() else {
        return Err(GenerateError::UnsupportedRootRewrite {
            rule: rule.to_string(),
            message: "terminator replacements only support direct binding operands".to_string(),
        });
    };
    if !bindings.contains(&binding) {
        return Err(GenerateError::MissingReplacementBinding {
            rule: rule.to_string(),
            binding: binding.to_string(),
        });
    }
    Ok(())
}

fn validate_replacement_bindings(
    replacement: &Replacement,
    bindings: &[&str],
    rule: &str,
) -> Result<(), GenerateError> {
    let mut replacement_bindings = Vec::new();
    replacement.collect_bindings(&mut replacement_bindings);
    for binding in replacement_bindings {
        if !bindings.contains(&binding) {
            return Err(GenerateError::MissingReplacementBinding {
                rule: rule.to_string(),
                binding: binding.to_string(),
            });
        }
    }
    Ok(())
}

fn replacement_value_type(
    replacement: &Replacement,
    binding_kinds: &BTreeMap<String, BindingKind>,
    rule: &str,
) -> Result<Option<ValueType>, GenerateError> {
    match replacement {
        Replacement::Binding { name } => {
            Ok(binding_kinds.get(name).and_then(|kind| kind.value_type()))
        }
        Replacement::BoolConst { .. } => Ok(Some(ValueType::Bool)),
        Replacement::BoolNot { value } => {
            let value_ty = replacement_value_type(value, binding_kinds, rule)?;
            match value_ty {
                Some(ValueType::Bool) => Ok(Some(ValueType::Bool)),
                Some(ValueType::Int) => Err(GenerateError::IllTypedReplacement {
                    rule: rule.to_string(),
                    message: "bool_not expects a Bool replacement operand".to_string(),
                }),
                None => Err(GenerateError::IllTypedReplacement {
                    rule: rule.to_string(),
                    message: "bool_not operand type could not be inferred".to_string(),
                }),
            }
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
            Some(BindingKind::IntValue)
            | Some(BindingKind::BoolValue)
            | Some(BindingKind::UnknownValue) => Err(GenerateError::IllTypedSideCondition {
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
        SideCondition::BestIntAnnotation {
            binding,
            annotation,
        } => {
            if annotation.bits() == 0 {
                return Err(GenerateError::IllTypedSideCondition {
                    rule: rule.to_string(),
                    message: format!(
                        "side condition binding `{binding}` uses a zero-width integer annotation"
                    ),
                });
            }
            match binding_kinds.get(binding) {
                Some(BindingKind::IntValue) | Some(BindingKind::IntConst) => Ok(()),
                Some(BindingKind::BoolValue) | Some(BindingKind::UnknownValue) => {
                    Err(GenerateError::IllTypedSideCondition {
                        rule: rule.to_string(),
                        message: format!("side condition binding `{binding}` must be an Int value"),
                    })
                }
                None => Err(GenerateError::MissingSideConditionBinding {
                    rule: rule.to_string(),
                    binding: binding.clone(),
                }),
            }
        }
        SideCondition::KnownOne { binding, bit: _ } => match binding_kinds.get(binding) {
            Some(BindingKind::IntValue) | Some(BindingKind::IntConst) => Ok(()),
            Some(BindingKind::BoolValue) | Some(BindingKind::UnknownValue) => {
                Err(GenerateError::IllTypedSideCondition {
                    rule: rule.to_string(),
                    message: format!("side condition binding `{binding}` must be an Int value"),
                })
            }
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

impl IntAnnotationSpec {
    fn bits(self) -> u32 {
        match self {
            IntAnnotationSpec::Signed { bits }
            | IntAnnotationSpec::Unsigned { bits }
            | IntAnnotationSpec::DontCare { bits } => bits,
        }
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
