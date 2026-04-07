use std::collections::{BTreeMap, BTreeSet};

use num_bigint::BigInt;
use tuffy_ir::function::Function;
use tuffy_ir::instruction::{ICmpOp, Op, Operand, Origin};
use tuffy_ir::module::Module;
use tuffy_ir::typed::{BoolOperand, BoolValue};
use tuffy_ir::types::Type;
use tuffy_ir::value::BlockRef;
use tuffy_ir::value::ValueRef;

const MAX_ITERATIONS: usize = 32;

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

pub fn generated_rule_count() -> usize {
    GENERATED_RULE_COUNT
}

pub fn optimize_module(module: &mut Module) -> PeepholeStats {
    let mut total = PeepholeStats::default();
    for func in &mut module.functions {
        total.merge(optimize_function(func));
    }
    total
}

pub fn optimize_function(func: &mut Function) -> PeepholeStats {
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
            if try_apply_generated_rule(func, idx, &mut stats) {
                changed = true;
                break 'candidate;
            }
        }

        if !changed {
            break;
        }
    }

    stats.iterations = iterations;
    stats
}

fn bind_value_slot(slot: &mut Option<ValueRef>, value: ValueRef) -> bool {
    match slot {
        Some(existing) => *existing == value,
        None => {
            *slot = Some(value);
            true
        }
    }
}

fn primary_inst_index(value: ValueRef) -> Option<u32> {
    if value.is_block_arg() || value.is_secondary_result() {
        None
    } else {
        Some(value.index())
    }
}

#[allow(dead_code)]
fn parse_decimal_bigint(value: &str) -> BigInt {
    value
        .parse()
        .unwrap_or_else(|_| panic!("invalid generated bigint literal: {value}"))
}

#[derive(Clone, Copy)]
enum TerminatorOpcode {
    BrIf,
}

struct ReplacementTerminator {
    opcode: TerminatorOpcode,
    operands: Vec<ValueRef>,
    successors: Vec<usize>,
}

#[derive(Clone)]
struct MatchedSuccessor {
    block: BlockRef,
    args: Vec<Operand>,
}

fn apply_value_root_rewrite(
    func: &mut Function,
    root_idx: u32,
    replacement: ValueRef,
    matched_insts: &BTreeSet<u32>,
) {
    let root_value = ValueRef::inst_result(root_idx);
    if replacement == root_value {
        return;
    }
    func.replace_all_uses(root_value, replacement);
    func.remove_inst(root_idx);
    cleanup_dead_instructions(func, matched_insts);
}

fn apply_terminator_root_rewrite(
    func: &mut Function,
    root_idx: u32,
    replacement: ReplacementTerminator,
    matched_insts: &BTreeSet<u32>,
) {
    let old_inst = func.inst(root_idx).clone();
    let mut new_inst = old_inst.clone();
    new_inst.origin = merged_origin(func, root_idx, matched_insts);
    new_inst.op = build_terminator_op(func, &old_inst.op, replacement);
    func.insert_inst_before(root_idx, new_inst);
    func.remove_inst(root_idx);
    cleanup_dead_instructions(func, matched_insts);
}

fn build_terminator_op(func: &Function, root_op: &Op, replacement: ReplacementTerminator) -> Op {
    let matched_successors = extract_matched_successors(root_op);

    match replacement.opcode {
        TerminatorOpcode::BrIf => {
            assert_eq!(
                replacement.operands.len(),
                1,
                "brif replacement expects one condition operand"
            );
            assert_eq!(
                replacement.successors.len(),
                2,
                "brif replacement expects two successor mappings"
            );

            let cond = BoolOperand::from_value(BoolValue::new(replacement.operands[0], func));
            let then_succ = &matched_successors[replacement.successors[0]];
            let else_succ = &matched_successors[replacement.successors[1]];
            Op::BrIf(
                cond,
                then_succ.block,
                then_succ.args.clone(),
                else_succ.block,
                else_succ.args.clone(),
            )
        }
    }
}

fn extract_matched_successors(root_op: &Op) -> Vec<MatchedSuccessor> {
    match root_op {
        Op::BrIf(_, then_block, then_args, else_block, else_args) => vec![
            MatchedSuccessor {
                block: *then_block,
                args: then_args.clone(),
            },
            MatchedSuccessor {
                block: *else_block,
                args: else_args.clone(),
            },
        ],
        other => panic!("unsupported matched terminator root: {other:?}"),
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

include!(concat!(env!("OUT_DIR"), "/peephole_gen.rs"));
