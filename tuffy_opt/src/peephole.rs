use std::collections::{BTreeMap, BTreeSet};

use num_bigint::BigInt;
use tuffy_ir::function::Function;
use tuffy_ir::instruction::{ICmpOp, Op, Origin};
use tuffy_ir::module::Module;
use tuffy_ir::typed::{BoolOperand, BoolValue};
use tuffy_ir::types::Type;
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

fn apply_value_rewrite(
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

fn apply_brif_rewrite(
    func: &mut Function,
    root_idx: u32,
    replacement: ValueRef,
    invert: bool,
    matched_insts: &BTreeSet<u32>,
) {
    let old_inst = func.inst(root_idx).clone();
    let mut new_inst = old_inst.clone();
    new_inst.origin = merged_origin(func, root_idx, matched_insts);
    new_inst.op = rewrite_brif_op(func, old_inst.op, replacement, invert);
    func.insert_inst_before(root_idx, new_inst);
    func.remove_inst(root_idx);
    cleanup_dead_instructions(func, matched_insts);
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

include!(concat!(env!("OUT_DIR"), "/peephole_gen.rs"));
