//! JSON schema matching the Lean-exported peephole rule set.

use std::collections::BTreeMap;

use num_bigint::BigInt;
use serde::Deserialize;

use crate::GenerateError;

/// Top-level peephole optimization specification exported from Lean.
#[derive(Debug, Deserialize)]
pub struct PeepholeSpec {
    /// Schema format version expected by the generator.
    pub format_version: u32,
    /// Schema kind discriminator.
    pub kind: String,
    /// Local peephole rewrite rules.
    pub rules: Vec<PeepholeRule>,
    /// Forward at-use fact-transfer rules.
    #[serde(default)]
    pub at_use_forward_rules: Vec<AtUseForwardRule>,
    /// Context-sensitive transforms driven by at-use facts.
    #[serde(default)]
    pub at_use_transforms: Vec<AtUseTransform>,
}

/// One peephole rewrite rule.
#[derive(Debug, Deserialize)]
pub struct PeepholeRule {
    /// Stable rule name used for diagnostics and generated helper names.
    pub name: String,
    /// Proof/categorization tag for the transform family.
    pub transform_kind: String,
    /// Lean theorem or definition that justifies the transform.
    pub proof_ref: String,
    /// Extra predicates that must hold before the rewrite can fire.
    #[serde(default)]
    pub side_conditions: Vec<SideCondition>,
    /// Match and replacement payload for the rule.
    pub rewrite: RewriteBody,
}

/// A forward at-use fact-transfer rule.
#[derive(Debug, Deserialize)]
pub struct AtUseForwardRule {
    /// Opcode handled by this rule.
    pub op: String,
    /// Known-bits transfer function applied to the result.
    pub known_bits_forward: AtUseKnownBitsForwardKind,
    /// Summary transfer function applied to the result.
    pub summary_forward: AtUseSummaryForwardKind,
    /// Lean theorem or definition that justifies the transfer rule.
    pub proof_ref: String,
}

/// A generated transform driven by at-use facts.
#[derive(Debug, Deserialize)]
pub struct AtUseTransform {
    /// Stable transform name used for diagnostics.
    pub name: String,
    /// Runtime transform kind to invoke.
    pub kind: AtUseTransformKind,
    /// Lean theorem or definition that justifies the transform.
    pub proof_ref: String,
}

/// Known-bits transfer function used by an at-use forward rule.
#[derive(Debug, Clone, Copy, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum AtUseKnownBitsForwardKind {
    /// Produce no additional known-bits information.
    Unknown,
    /// Derive facts from a constant result.
    Const,
    /// Merge facts from a `select`.
    Select,
    /// Derive facts from a bitwise `and`.
    BitAnd,
    /// Derive facts from a bitwise `or`.
    BitOr,
    /// Derive facts from a bitwise `xor`.
    BitXor,
}

/// Summary transfer function used by an at-use forward rule.
#[derive(Debug, Clone, Copy, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum AtUseSummaryForwardKind {
    /// Produce no additional summary information.
    Unknown,
    /// Derive summary facts from a constant result.
    Const,
    /// Merge summary facts from a `select`.
    Select,
    /// Derive summary facts from a bitwise `and`.
    BitAnd,
    /// Derive summary facts from a bitwise `or`.
    BitOr,
    /// Derive summary facts from a bitwise `xor`.
    BitXor,
}

/// Runtime transform kind selected by an at-use descriptor.
#[derive(Debug, Clone, Copy, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum AtUseTransformKind {
    /// Fold an `icmp` based on at-use information.
    FoldIcmp,
    /// Fold a `brif` based on at-use information.
    FoldBrIf,
    /// Strengthen operand annotations.
    StrengthenOperand,
    /// Strengthen result annotations.
    StrengthenResult,
}

/// Match and replacement payload for a peephole rule.
#[derive(Debug, Deserialize)]
pub struct RewriteBody {
    /// Root shape that must match before the rule can fire.
    pub match_root: MatchRoot,
    /// Replacement emitted after a successful match.
    pub replacement: RootReplacement,
}

/// Root shape that anchors a peephole rewrite.
#[derive(Debug, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum MatchRoot {
    /// Match a value-producing instruction tree.
    Value {
        /// Root pattern of the matched value tree.
        root: Pattern,
    },
    /// Match a terminator instruction with explicit operands and successor arity.
    Terminator {
        /// Terminator opcode name.
        op: String,
        /// Operand patterns matched against the terminator operands.
        operands: Vec<Pattern>,
        /// Number of successors the matched terminator must expose.
        successor_count: usize,
    },
    /// Match a canonical `brif` form recognized by the runtime.
    #[serde(rename = "canonical_brif")]
    CanonicalBrIf {
        /// Binding that receives the canonicalized branch condition.
        binding: String,
        /// Canonicalization mode used while matching the branch.
        mode: CanonicalBrIfMode,
    },
    /// Match a root that is eligible for const-folding.
    ConstFold {
        /// Opcode to const-fold.
        op: String,
        /// Attributes that further constrain the root opcode.
        #[serde(default)]
        attrs: Vec<PatternAttr>,
    },
}

/// Canonical form expected when matching a `brif` root.
#[derive(Debug, Clone, Copy, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum CanonicalBrIfMode {
    /// Match `bool xor const` canonicalization.
    BoolXorConst,
    /// Match compares whose boolean result has been intified.
    IntifiedBoolCompare,
}

/// Replacement emitted for a matched root.
#[derive(Debug, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum RootReplacement {
    /// Replace a value root with a new value expression.
    Value {
        /// Replacement value expression.
        value: Replacement,
    },
    /// Replace a terminator root with a new terminator payload.
    Terminator {
        /// Replacement terminator opcode.
        op: String,
        /// Replacement operands.
        operands: Vec<Replacement>,
        /// Successor remapping expressed as indices into the matched successors.
        successors: Vec<usize>,
    },
    /// Replace a const-fold root with the runtime const-fold result.
    ConstFold,
}

/// Replacement expression used inside a root replacement.
#[derive(Debug, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum Replacement {
    /// Reuse a previously bound value.
    Binding {
        /// Binding name to reuse.
        name: String,
    },
    /// Materialize an integer constant.
    IntConst {
        /// Decimal string form of the constant.
        value: String,
    },
    /// Materialize a boolean constant.
    BoolConst {
        /// Boolean literal to materialize.
        value: bool,
    },
    /// Materialize the shift amount `log2(binding)` for a matched positive power-of-two constant.
    Pow2ShiftAmount {
        /// Binding name assigned to the matched integer constant.
        name: String,
    },
    /// Materialize an instruction tree inside the replacement expression.
    Inst {
        /// Lowercase opcode name.
        op: String,
        /// Nested replacement operands.
        args: Vec<Replacement>,
    },
    /// Materialize the logical negation of another replacement expression.
    BoolNot {
        /// Nested replacement expression to negate.
        value: Box<Replacement>,
    },
}

impl Replacement {
    /// Collect every binding name referenced by this replacement expression.
    fn collect_bindings<'a>(&'a self, out: &mut Vec<&'a str>) {
        match self {
            Replacement::Binding { name } => {
                if !out.contains(&name.as_str()) {
                    out.push(name);
                }
            }
            Replacement::IntConst { .. } | Replacement::BoolConst { .. } => {}
            Replacement::Pow2ShiftAmount { name } => {
                if !out.contains(&name.as_str()) {
                    out.push(name);
                }
            }
            Replacement::Inst { args, .. } => {
                for arg in args {
                    arg.collect_bindings(out);
                }
            }
            Replacement::BoolNot { value } => value.collect_bindings(out),
        }
    }

    /// Return the binding name for direct binding replacements.
    pub fn binding_name(&self) -> Option<&str> {
        match self {
            Replacement::Binding { name } => Some(name),
            Replacement::IntConst { .. }
            | Replacement::BoolConst { .. }
            | Replacement::Pow2ShiftAmount { .. }
            | Replacement::Inst { .. }
            | Replacement::BoolNot { .. } => None,
        }
    }
}

/// Value-pattern shape used while matching a rewrite root.
#[derive(Debug, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum Pattern {
    /// Capture any value and optionally constrain its type.
    Capture {
        /// Binding name assigned to the captured value.
        name: String,
        /// Optional value type required for the capture.
        #[serde(default)]
        ty: Option<ValueType>,
    },
    /// Bind a nested pattern to a name for later reuse.
    Bind {
        /// Binding name assigned to the nested pattern result.
        name: String,
        /// Nested pattern to match.
        pattern: Box<Pattern>,
    },
    /// Match a literal integer constant.
    IntConst {
        /// Decimal string form of the constant.
        value: String,
    },
    /// Match an integer constant and bind its literal value.
    IntConstBinding {
        /// Binding name assigned to the matched integer constant.
        name: String,
    },
    /// Match an instruction by opcode, attributes, and operand patterns.
    Inst {
        /// Lowercase opcode name.
        op: String,
        /// Additional attributes constraining the instruction.
        #[serde(default)]
        attrs: Vec<PatternAttr>,
        /// Operand patterns matched against the instruction operands.
        args: Vec<Pattern>,
    },
}

impl Pattern {
    /// Collect every binding introduced by this pattern tree.
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

    /// Infer the value type produced by this pattern when possible.
    fn inferred_value_type(&self) -> Option<ValueType> {
        match self {
            Pattern::Capture { ty, .. } => *ty,
            Pattern::Bind { pattern, .. } => pattern.inferred_value_type(),
            Pattern::IntConst { .. } | Pattern::IntConstBinding { .. } => Some(ValueType::Int),
            Pattern::Inst { op, args, .. } => match op.as_str() {
                "and" | "div" | "rem" | "xor" => Some(ValueType::Int),
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

    /// Record the binding kinds implied by this pattern tree.
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

/// Coarse value type used during schema validation.
#[derive(Debug, Clone, Copy, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "lowercase")]
pub enum ValueType {
    /// Integer value.
    Int,
    /// Boolean value.
    Bool,
}

/// Attribute attached to a pattern-matched instruction.
#[derive(Debug, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum PatternAttr {
    /// Integer-compare predicate attached to an `icmp`.
    IcmpPred {
        /// Predicate name encoded in the exported schema.
        value: String,
    },
}

/// Additional predicate that must hold before a rewrite can fire.
#[derive(Debug, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum SideCondition {
    /// Apply an integer predicate to a bound integer constant.
    IntPredicate {
        /// Binding to inspect.
        binding: String,
        /// Predicate that must hold for the binding.
        predicate: IntPredicate,
    },
    /// Require a bound value to have a best-known integer annotation.
    BestIntAnnotation {
        /// Binding to inspect.
        binding: String,
        /// Required annotation.
        annotation: IntAnnotationSpec,
    },
    /// Require a known-one bit on a bound integer value.
    KnownOne {
        /// Binding to inspect.
        binding: String,
        /// Bit index that must be known one.
        bit: u32,
    },
    /// Require a bound integer value to be known non-negative.
    ValueNonNegative {
        /// Binding to inspect.
        binding: String,
    },
    /// Require every nested condition to hold.
    AllOf {
        /// Nested conditions combined with logical `and`.
        conditions: Vec<SideCondition>,
    },
    /// Require at least one nested condition to hold.
    AnyOf {
        /// Nested conditions combined with logical `or`.
        conditions: Vec<SideCondition>,
    },
    /// Negate a nested condition.
    Not {
        /// Nested condition to negate.
        condition: Box<SideCondition>,
    },
}

/// Integer-constant predicate supported by side conditions.
#[derive(Debug, Clone, Copy, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum IntPredicate {
    #[serde(rename = "is_zero")]
    /// Match the integer literal zero.
    Zero,
    #[serde(rename = "is_one")]
    /// Match the integer literal one.
    One,
    #[serde(rename = "is_odd")]
    /// Match an odd integer literal.
    Odd,
    #[serde(rename = "is_positive_power_of_two")]
    /// Match a positive power-of-two integer literal.
    PositivePowerOfTwo,
}

/// Integer annotation constraint used by side conditions.
#[derive(Debug, Clone, Copy, Deserialize, PartialEq, Eq)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum IntAnnotationSpec {
    /// Require a signed integer annotation with the given bit width.
    Signed {
        /// Bit width carried by the annotation.
        bits: u32,
    },
    /// Require an unsigned integer annotation with the given bit width.
    Unsigned {
        /// Bit width carried by the annotation.
        bits: u32,
    },
    /// Require any signedness as long as the bit width matches.
    DontCare {
        /// Bit width carried by the annotation.
        bits: u32,
    },
}

/// Internal classification used while validating binding types.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum BindingKind {
    /// Binding type is unknown.
    UnknownValue,
    /// Binding is known to hold an integer value.
    IntValue,
    /// Binding is known to hold a boolean value.
    BoolValue,
    /// Binding is an integer constant literal.
    IntConst,
}

impl BindingKind {
    /// Derive a binding kind from an optional value type.
    fn from_value_type(ty: Option<ValueType>) -> Self {
        match ty {
            Some(ValueType::Int) => Self::IntValue,
            Some(ValueType::Bool) => Self::BoolValue,
            None => Self::UnknownValue,
        }
    }

    /// Recover the public-facing value type, if known.
    fn value_type(self) -> Option<ValueType> {
        match self {
            BindingKind::UnknownValue => None,
            BindingKind::IntValue | BindingKind::IntConst => Some(ValueType::Int),
            BindingKind::BoolValue => Some(ValueType::Bool),
        }
    }
}

/// Validate a decoded peephole specification before code generation.
///
/// # Errors
///
/// Returns an error if the schema version, root shape, replacement, or side
/// conditions are unsupported or ill-typed.
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

/// Validate that a pattern uses only supported constructs.
///
/// # Errors
///
/// Returns an error if the pattern contains an invalid integer literal.
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

/// Merge binding-kind information for a binding name discovered in a pattern.
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

/// Validate a value replacement against the matched root and binding set.
///
/// # Errors
///
/// Returns an error if the replacement references missing bindings or has an
/// incompatible inferred type.
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

/// Validate one terminator replacement operand.
///
/// # Errors
///
/// Returns an error if the operand is not a direct binding or references a
/// binding outside the matched root.
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

/// Ensure that every binding referenced by a replacement was matched.
///
/// # Errors
///
/// Returns an error if the replacement refers to an unknown binding.
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

/// Infer the value type produced by a replacement expression.
///
/// # Errors
///
/// Returns an error if the replacement is internally ill-typed.
fn replacement_value_type(
    replacement: &Replacement,
    binding_kinds: &BTreeMap<String, BindingKind>,
    rule: &str,
) -> Result<Option<ValueType>, GenerateError> {
    match replacement {
        Replacement::Binding { name } => {
            Ok(binding_kinds.get(name).and_then(|kind| kind.value_type()))
        }
        Replacement::IntConst { value } => {
            let _: BigInt = value
                .parse()
                .map_err(|_| GenerateError::InvalidIntConstant(value.clone()))?;
            Ok(Some(ValueType::Int))
        }
        Replacement::BoolConst { .. } => Ok(Some(ValueType::Bool)),
        Replacement::Pow2ShiftAmount { name } => match binding_kinds.get(name) {
            Some(BindingKind::IntConst) => Ok(Some(ValueType::Int)),
            Some(BindingKind::IntValue)
            | Some(BindingKind::BoolValue)
            | Some(BindingKind::UnknownValue) => Err(GenerateError::IllTypedReplacement {
                rule: rule.to_string(),
                message: format!(
                    "pow2_shift_amount expects `{name}` to come from `int_const_binding`"
                ),
            }),
            None => Err(GenerateError::MissingReplacementBinding {
                rule: rule.to_string(),
                binding: name.clone(),
            }),
        },
        Replacement::Inst { op, args } => {
            let expected_arity = match op.as_str() {
                "shr" => 2,
                other => {
                    return Err(GenerateError::UnsupportedRootRewrite {
                        rule: rule.to_string(),
                        message: format!("unsupported replacement inst op `{other}`"),
                    });
                }
            };
            if args.len() != expected_arity {
                return Err(GenerateError::IllTypedReplacement {
                    rule: rule.to_string(),
                    message: format!(
                        "replacement inst `{op}` expects {expected_arity} operands, got {}",
                        args.len()
                    ),
                });
            }
            for arg in args {
                match replacement_value_type(arg, binding_kinds, rule)? {
                    Some(ValueType::Int) => {}
                    Some(ValueType::Bool) => {
                        return Err(GenerateError::IllTypedReplacement {
                            rule: rule.to_string(),
                            message: format!("replacement inst `{op}` expects Int operands"),
                        });
                    }
                    None => {
                        return Err(GenerateError::IllTypedReplacement {
                            rule: rule.to_string(),
                            message: format!(
                                "replacement inst `{op}` operand type could not be inferred"
                            ),
                        });
                    }
                }
            }
            Ok(Some(ValueType::Int))
        }
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

/// Validate a side condition against the binding kinds inferred from the root.
///
/// # Errors
///
/// Returns an error if the side condition references unknown bindings or is
/// not well-typed for the matched values.
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
        SideCondition::ValueNonNegative { binding } => match binding_kinds.get(binding) {
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
    /// Return the annotation bit width regardless of signedness.
    fn bits(self) -> u32 {
        match self {
            IntAnnotationSpec::Signed { bits }
            | IntAnnotationSpec::Unsigned { bits }
            | IntAnnotationSpec::DontCare { bits } => bits,
        }
    }
}

/// Validate a const-fold root against the operations supported by the runtime.
///
/// # Errors
///
/// Returns an error if the opcode or attribute set is not supported.
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
