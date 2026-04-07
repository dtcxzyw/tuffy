use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fmt;

use num_bigint::BigInt;
use tuffy_ir::function::Function;
use tuffy_ir::instruction::{ICmpOp, Instruction, Op, Origin};
use tuffy_ir::module::Module;
use tuffy_ir::typed::{BoolOperand, BoolValue};
use tuffy_ir::types::Type;
use tuffy_ir::value::{BlockRef, ValueRef};

const DEFAULT_RULES_JSON: &str = include_str!(concat!(env!("OUT_DIR"), "/peephole_rules.json"));
const MAX_ITERATIONS: usize = 32;

#[derive(Debug)]
pub enum PeepholeLoadError {
    Json(serde_json::Error),
    UnsupportedFormatVersion(u32),
    UnsupportedKind(String),
    InvalidIntConstant(String),
}

impl fmt::Display for PeepholeLoadError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PeepholeLoadError::Json(err) => write!(f, "failed to parse peephole rule JSON: {err}"),
            PeepholeLoadError::UnsupportedFormatVersion(version) => {
                write!(f, "unsupported peephole rule format version: {version}")
            }
            PeepholeLoadError::UnsupportedKind(kind) => {
                write!(f, "unsupported peephole rule kind: {kind}")
            }
            PeepholeLoadError::InvalidIntConstant(value) => {
                write!(f, "invalid peephole integer constant: {value}")
            }
        }
    }
}

impl std::error::Error for PeepholeLoadError {}

impl From<serde_json::Error> for PeepholeLoadError {
    fn from(value: serde_json::Error) -> Self {
        Self::Json(value)
    }
}

#[derive(Debug, Clone)]
pub struct PeepholeRuleSet {
    rules: Vec<PeepholeRule>,
}

impl PeepholeRuleSet {
    pub fn from_json_str(json: &str) -> Result<Self, PeepholeLoadError> {
        let spec: raw::PeepholeSpec = serde_json::from_str(json)?;
        if spec.format_version != 1 {
            return Err(PeepholeLoadError::UnsupportedFormatVersion(
                spec.format_version,
            ));
        }
        if spec.kind != "peephole" {
            return Err(PeepholeLoadError::UnsupportedKind(spec.kind));
        }

        let rules = spec
            .rules
            .into_iter()
            .map(PeepholeRule::from_raw)
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Self { rules })
    }

    pub fn rules(&self) -> &[PeepholeRule] {
        &self.rules
    }
}

pub fn default_rule_set() -> PeepholeRuleSet {
    PeepholeRuleSet::from_json_str(DEFAULT_RULES_JSON)
        .expect("default peephole rules should be valid")
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct PeepholeStats {
    pub iterations: usize,
    pub rewrites: usize,
    pub per_rule: BTreeMap<String, usize>,
}

impl PeepholeStats {
    fn record(&mut self, rule_name: &str) {
        self.rewrites += 1;
        *self.per_rule.entry(rule_name.to_string()).or_default() += 1;
    }

    fn merge(&mut self, other: PeepholeStats) {
        self.iterations += other.iterations;
        self.rewrites += other.rewrites;
        for (name, count) in other.per_rule {
            *self.per_rule.entry(name).or_default() += count;
        }
    }
}

pub fn optimize_module(module: &mut Module, rules: &PeepholeRuleSet) -> PeepholeStats {
    let mut total = PeepholeStats::default();
    for func in &mut module.functions {
        total.merge(optimize_function(func, rules));
    }
    total
}

pub fn optimize_function(func: &mut Function, rules: &PeepholeRuleSet) -> PeepholeStats {
    let mut stats = PeepholeStats::default();
    let mut iterations = 0;

    while iterations < MAX_ITERATIONS {
        iterations += 1;
        let mut changed = false;
        let candidates: Vec<u32> = func.inst_pool.iter_insts().map(|(idx, _)| idx).collect();

        'candidate: for idx in candidates {
            if func.inst_pool.get(idx).is_none() {
                continue;
            }
            for rule in &rules.rules {
                if let Some(matched) = match_rule(func, idx, rule) {
                    apply_rule(func, idx, rule, matched);
                    stats.record(&rule.name);
                    changed = true;
                    break 'candidate;
                }
            }
        }

        if !changed {
            break;
        }
    }

    stats.iterations = iterations;
    stats
}

#[derive(Debug, Clone)]
pub struct PeepholeRule {
    pub name: String,
    pub proof_ref: String,
    rewrite: Rewrite,
}

impl PeepholeRule {
    fn from_raw(raw: raw::PeepholeRule) -> Result<Self, PeepholeLoadError> {
        let rewrite = Rewrite::from_raw(raw.rewrite)?;
        Ok(Self {
            name: raw.name,
            proof_ref: raw.proof_ref,
            rewrite,
        })
    }
}

#[derive(Debug, Clone)]
enum Rewrite {
    Value {
        root: Pattern,
        replacement_binding: String,
    },
    BrIf {
        condition: Pattern,
        replacement_binding: String,
        invert: bool,
    },
}

impl Rewrite {
    fn from_raw(raw: raw::Rewrite) -> Result<Self, PeepholeLoadError> {
        match raw {
            raw::Rewrite::Value { root, replacement } => Ok(Self::Value {
                root: Pattern::from_raw(root)?,
                replacement_binding: replacement.binding_name(),
            }),
            raw::Rewrite::Brif {
                condition,
                replacement,
                invert,
            } => Ok(Self::BrIf {
                condition: Pattern::from_raw(condition)?,
                replacement_binding: replacement.binding_name(),
                invert,
            }),
        }
    }
}

#[derive(Debug, Clone)]
enum Pattern {
    Capture { name: String, ty: Option<BoundType> },
    Bind { name: String, pattern: Box<Pattern> },
    IntConst { value: BigInt },
    IntConstBinding { name: String },
    Inst { op: PatternOp, args: Vec<Pattern> },
}

impl Pattern {
    fn from_raw(raw: raw::Pattern) -> Result<Self, PeepholeLoadError> {
        match raw {
            raw::Pattern::Capture { name, ty } => Ok(Self::Capture {
                name,
                ty: ty.map(BoundType::from_raw),
            }),
            raw::Pattern::Bind { name, pattern } => Ok(Self::Bind {
                name,
                pattern: Box::new(Self::from_raw(*pattern)?),
            }),
            raw::Pattern::IntConst { value } => Ok(Self::IntConst {
                value: parse_big_int(&value)?,
            }),
            raw::Pattern::IntConstBinding { name } => Ok(Self::IntConstBinding { name }),
            raw::Pattern::Inst { op, args } => Ok(Self::Inst {
                op: PatternOp::from_raw(op),
                args: args
                    .into_iter()
                    .map(Self::from_raw)
                    .collect::<Result<Vec<_>, _>>()?,
            }),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum BoundType {
    Int,
    Bool,
}

impl BoundType {
    fn from_raw(raw: raw::ValueType) -> Self {
        match raw {
            raw::ValueType::Int => Self::Int,
            raw::ValueType::Bool => Self::Bool,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PatternOp {
    Select,
    And,
    Xor,
    IcmpEq,
}

impl PatternOp {
    fn from_raw(raw: raw::PatternOp) -> Self {
        match raw {
            raw::PatternOp::Select => Self::Select,
            raw::PatternOp::And => Self::And,
            raw::PatternOp::Xor => Self::Xor,
            raw::PatternOp::IcmpEq => Self::IcmpEq,
        }
    }

    fn is_commutative(self) -> bool {
        matches!(self, Self::And | Self::Xor | Self::IcmpEq)
    }
}

#[derive(Clone, Debug, Default)]
struct MatchState {
    bindings: HashMap<String, ValueRef>,
    matched_insts: BTreeSet<u32>,
}

#[derive(Debug)]
struct RuleMatch {
    bindings: HashMap<String, ValueRef>,
    matched_insts: BTreeSet<u32>,
}

fn parse_big_int(value: &str) -> Result<BigInt, PeepholeLoadError> {
    value
        .parse()
        .map_err(|_| PeepholeLoadError::InvalidIntConstant(value.to_string()))
}

fn match_rule(func: &Function, root_idx: u32, rule: &PeepholeRule) -> Option<RuleMatch> {
    match &rule.rewrite {
        Rewrite::Value { root, .. } => {
            let root_block = func.inst_node(root_idx).parent_block;
            let root_value = ValueRef::inst_result(root_idx);
            let mut state = MatchState::default();
            if match_pattern(func, root_block, root_value, root, &mut state) {
                Some(RuleMatch {
                    bindings: state.bindings,
                    matched_insts: state.matched_insts,
                })
            } else {
                None
            }
        }
        Rewrite::BrIf { condition, .. } => {
            let node = func.inst_pool.get(root_idx)?;
            let root_block = node.parent_block;
            let cond_value = match &node.inst.op {
                Op::BrIf(cond, _, _, _, _) => cond.clone().raw().value,
                _ => return None,
            };
            let mut state = MatchState::default();
            if match_pattern(func, root_block, cond_value, condition, &mut state) {
                Some(RuleMatch {
                    bindings: state.bindings,
                    matched_insts: state.matched_insts,
                })
            } else {
                None
            }
        }
    }
}

fn match_pattern(
    func: &Function,
    root_block: BlockRef,
    value: ValueRef,
    pattern: &Pattern,
    state: &mut MatchState,
) -> bool {
    match pattern {
        Pattern::Capture { name, ty } => {
            if let Some(ty) = ty
                && !value_matches_type(func, value, *ty)
            {
                return false;
            }
            bind_value(state, name, value)
        }
        Pattern::Bind { name, pattern } => {
            if !bind_value(state, name, value) {
                return false;
            }
            match_pattern(func, root_block, value, pattern, state)
        }
        Pattern::IntConst { value: expected } => {
            let Some(inst_idx) = primary_inst_index(value) else {
                return false;
            };
            let Some(node) = func.inst_pool.get(inst_idx) else {
                return false;
            };
            if node.parent_block != root_block {
                return false;
            }
            match &node.inst.op {
                Op::Const(actual) if actual == expected => {
                    state.matched_insts.insert(inst_idx);
                    true
                }
                _ => false,
            }
        }
        Pattern::IntConstBinding { name } => {
            let Some(inst_idx) = primary_inst_index(value) else {
                return false;
            };
            let Some(node) = func.inst_pool.get(inst_idx) else {
                return false;
            };
            if node.parent_block != root_block {
                return false;
            }
            match &node.inst.op {
                Op::Const(_) => {
                    if !bind_value(state, name, value) {
                        return false;
                    }
                    state.matched_insts.insert(inst_idx);
                    true
                }
                _ => false,
            }
        }
        Pattern::Inst { op, args } => {
            let Some(inst_idx) = primary_inst_index(value) else {
                return false;
            };
            let Some(node) = func.inst_pool.get(inst_idx) else {
                return false;
            };
            if node.parent_block != root_block {
                return false;
            }
            let Some(operands) = inst_operands(&node.inst, *op) else {
                return false;
            };
            if operands.len() != args.len() {
                return false;
            }

            let mut branch = state.clone();
            branch.matched_insts.insert(inst_idx);
            if match_operands(func, root_block, &operands, args, &mut branch) {
                *state = branch;
                return true;
            }

            if op.is_commutative() && operands.len() == 2 {
                let swapped = [operands[1], operands[0]];
                let mut branch = state.clone();
                branch.matched_insts.insert(inst_idx);
                if match_operands(func, root_block, &swapped, args, &mut branch) {
                    *state = branch;
                    return true;
                }
            }

            false
        }
    }
}

fn match_operands(
    func: &Function,
    root_block: BlockRef,
    values: &[ValueRef],
    patterns: &[Pattern],
    state: &mut MatchState,
) -> bool {
    if values.len() != patterns.len() {
        return false;
    }
    for (value, pattern) in values.iter().zip(patterns) {
        if !match_pattern(func, root_block, *value, pattern, state) {
            return false;
        }
    }
    true
}

fn bind_value(state: &mut MatchState, name: &str, value: ValueRef) -> bool {
    match state.bindings.get(name) {
        Some(existing) => *existing == value,
        None => {
            state.bindings.insert(name.to_string(), value);
            true
        }
    }
}

fn value_matches_type(func: &Function, value: ValueRef, ty: BoundType) -> bool {
    matches!(
        (ty, func.value_type(value)),
        (BoundType::Int, Some(Type::Int)) | (BoundType::Bool, Some(Type::Bool))
    )
}

fn primary_inst_index(value: ValueRef) -> Option<u32> {
    if value.is_block_arg() || value.is_secondary_result() {
        None
    } else {
        Some(value.index())
    }
}

fn inst_operands(inst: &Instruction, op: PatternOp) -> Option<Vec<ValueRef>> {
    match (op, &inst.op) {
        (PatternOp::Select, Op::Select(cond, t, e)) => {
            Some(vec![cond.clone().raw().value, t.value, e.value])
        }
        (PatternOp::And, Op::And(a, b)) => Some(vec![a.clone().raw().value, b.clone().raw().value]),
        (PatternOp::Xor, Op::Xor(a, b)) => Some(vec![a.clone().raw().value, b.clone().raw().value]),
        (PatternOp::IcmpEq, Op::ICmp(ICmpOp::Eq, a, b)) => {
            Some(vec![a.clone().raw().value, b.clone().raw().value])
        }
        _ => None,
    }
}

fn apply_rule(func: &mut Function, root_idx: u32, rule: &PeepholeRule, matched: RuleMatch) {
    match &rule.rewrite {
        Rewrite::Value {
            replacement_binding,
            ..
        } => {
            let replacement = matched.bindings[replacement_binding];
            let root_value = ValueRef::inst_result(root_idx);
            if replacement == root_value {
                return;
            }
            func.replace_all_uses(root_value, replacement);
            func.remove_inst(root_idx);
            cleanup_dead_instructions(func, &matched.matched_insts);
        }
        Rewrite::BrIf {
            replacement_binding,
            invert,
            ..
        } => {
            let replacement = matched.bindings[replacement_binding];
            let old_inst = func.inst(root_idx).clone();
            let mut new_inst = old_inst.clone();
            new_inst.origin = merged_origin(func, root_idx, &matched.matched_insts);
            new_inst.op = rewrite_brif_op(func, old_inst.op, replacement, *invert);
            let _new_idx = func.insert_inst_before(root_idx, new_inst);
            func.remove_inst(root_idx);
            cleanup_dead_instructions(func, &matched.matched_insts);
        }
    }
}

fn rewrite_brif_op(func: &Function, op: Op, replacement: ValueRef, invert: bool) -> Op {
    let replacement = BoolOperand::from_value(BoolValue::new(replacement, func));
    match op {
        Op::BrIf(_, then_block, then_args, else_block, else_args) => {
            if invert {
                Op::BrIf(replacement, else_block, else_args, then_block, then_args)
            } else {
                Op::BrIf(replacement, then_block, then_args, else_block, else_args)
            }
        }
        other => panic!("expected brif terminator, got {other:?}"),
    }
}

fn merged_origin(func: &Function, root_idx: u32, matched_insts: &BTreeSet<u32>) -> Origin {
    let mut seen = BTreeSet::new();
    let mut sources = Vec::new();
    for idx in std::iter::once(root_idx).chain(matched_insts.iter().copied()) {
        if let Some(node) = func.inst_pool.get(idx) {
            for source in &node.inst.origin.sources {
                if seen.insert(*source) {
                    sources.push(*source);
                }
            }
        }
    }
    Origin { sources }
}

fn cleanup_dead_instructions(func: &mut Function, matched_insts: &BTreeSet<u32>) {
    loop {
        let mut changed = false;
        for idx in matched_insts.iter().copied().collect::<Vec<_>>() {
            let Some(inst) = func.inst_pool.get(idx) else {
                continue;
            };
            if !instruction_results_unused(func, idx, inst.inst.secondary_ty.is_some()) {
                continue;
            }
            func.remove_inst(idx);
            changed = true;
        }
        if !changed {
            break;
        }
    }
}

fn instruction_results_unused(func: &Function, idx: u32, has_secondary_result: bool) -> bool {
    if func.has_uses(ValueRef::inst_result(idx)) {
        return false;
    }
    if has_secondary_result && func.has_uses(ValueRef::inst_secondary_result(idx)) {
        return false;
    }
    true
}

mod raw {
    use serde::Deserialize;

    #[derive(Debug, Deserialize)]
    pub(super) struct PeepholeSpec {
        pub format_version: u32,
        pub kind: String,
        pub rules: Vec<PeepholeRule>,
    }

    #[derive(Debug, Deserialize)]
    pub(super) struct PeepholeRule {
        pub name: String,
        pub proof_ref: String,
        pub rewrite: Rewrite,
    }

    #[derive(Debug, Deserialize)]
    #[serde(tag = "kind", rename_all = "snake_case")]
    pub(super) enum Rewrite {
        Value {
            root: Pattern,
            replacement: Replacement,
        },
        Brif {
            condition: Pattern,
            replacement: Replacement,
            invert: bool,
        },
    }

    #[derive(Debug, Deserialize)]
    #[serde(tag = "kind", rename_all = "snake_case")]
    pub(super) enum Replacement {
        Binding { name: String },
    }

    impl Replacement {
        pub(super) fn binding_name(self) -> String {
            match self {
                Replacement::Binding { name } => name,
            }
        }
    }

    #[derive(Debug, Deserialize)]
    #[serde(tag = "kind", rename_all = "snake_case")]
    pub(super) enum Pattern {
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
            op: PatternOp,
            args: Vec<Pattern>,
        },
    }

    #[derive(Debug, Clone, Copy, Deserialize)]
    #[serde(rename_all = "snake_case")]
    pub(super) enum PatternOp {
        Select,
        And,
        Xor,
        IcmpEq,
    }

    #[derive(Debug, Clone, Copy, Deserialize)]
    #[serde(rename_all = "lowercase")]
    pub(super) enum ValueType {
        Int,
        Bool,
    }
}
