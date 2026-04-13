use std::fmt::Write;

use tuffy_ir::instruction::{Instruction, Op, Operand, Origin};
use tuffy_ir::parser::parse_module;
use tuffy_ir::types::Type;
use tuffy_ir::value::ValueRef;
use tuffy_ir::verifier::verify_module;

use crate::cfg::collect_block_refs;
use crate::{
    generated_cleanup_pass_count, generated_legacy_cleanup_pass_count, generated_rule_count,
    generated_verified_cleanup_pass_count, optimize_module,
};

fn optimize(input: &str) -> (String, crate::PeepholeStats) {
    let mut module = parse_module(input).unwrap_or_else(|e| panic!("parse error: {e}"));
    let stats = optimize_module(&mut module);
    let verify = verify_module(&module);
    assert!(verify.is_ok(), "optimized module should verify: {verify}");
    (format!("{module}"), stats)
}

fn normalize_ir(ir: &str) -> String {
    ir.lines()
        .map(str::trim_end)
        .filter(|line| !line.trim().is_empty())
        .collect::<Vec<_>>()
        .join("\n")
}

#[test]
fn loads_default_rule_set() {
    assert_eq!(generated_rule_count(), 40);
}

#[test]
fn loads_generated_cleanup_manifest() {
    assert_eq!(generated_cleanup_pass_count(), 5);
    assert_eq!(generated_verified_cleanup_pass_count(), 1);
    assert_eq!(generated_legacy_cleanup_pass_count(), 4);
}

#[test]
fn skips_expensive_peephole_fixpoint_for_large_functions() {
    let mut input = String::from(
        r#"func @large_fixpoint_guard(int:s32) -> int:s32 {
  bb0(v0: mem):
    v1: int:s32 = param 0
    v2: int:s32 = iconst 0
"#,
    );
    let mut prev = 1u32;
    let zero = 2u32;
    for next in 3..1105u32 {
        writeln!(&mut input, "    v{next}: int:s32 = add v{prev}, v{zero}")
            .expect("string write should succeed");
        prev = next;
    }
    writeln!(&mut input, "    ret v{prev}, v0").expect("string write should succeed");
    input.push_str("}\n");

    let (output, stats) = optimize(&input);
    assert_eq!(
        stats.rewrites, 0,
        "large functions should skip the expensive local fixpoint:\n{output}"
    );
    assert!(
        output.contains(" = add "),
        "large function should remain largely untranslated by peepholes:\n{output}"
    );
}

#[test]
fn collapses_branch_on_select_eq_one() {
    let input = r#"
func @branch_eq_one() {
  bb0:
    v0: bool = bconst true
    v1: int = iconst 1
    v2: int = iconst 0
    v3: int = select v0, v1, v2
    v4: int = iconst 1
    v5: bool = icmp.eq v3, v4
    brif v5, bb1, bb2
  bb1:
    trap
  bb2:
    trap
}
"#;
    let (output, stats) = optimize(input);
    let expected = r#"func @branch_eq_one() {
  bb0:
    br bb1
  bb1:
    trap
  bb2:
    trap
}"#;
    assert_eq!(normalize_ir(&output), normalize_ir(expected));
    assert!(stats.rewrites > 0);
}

#[test]
fn collapses_branch_on_select_eq_zero() {
    let input = r#"
func @branch_eq_zero() {
  bb0:
    v0: bool = bconst false
    v1: int = iconst 1
    v2: int = iconst 0
    v3: int = select v0, v1, v2
    v4: int = iconst 0
    v5: bool = icmp.eq v3, v4
    brif v5, bb1, bb2
  bb1:
    trap
  bb2:
    trap
}
"#;
    let (output, stats) = optimize(input);
    let expected = r#"func @branch_eq_zero() {
  bb0:
    br bb1
  bb1:
    trap
  bb2:
    trap
}"#;
    assert_eq!(normalize_ir(&output), normalize_ir(expected));
    assert!(stats.rewrites > 0);
}

#[test]
fn combines_mask_cleanup_with_branch_collapse() {
    let input = r#"
func @branch_and_mask() {
  bb0:
    v0: bool = bconst true
    v1: int = iconst 1
    v2: int = iconst 0
    v3: int = select v0, v1, v2
    v4: int = iconst 255
    v5: int = and v3, v4
    v6: int = iconst 0
    v7: bool = icmp.eq v5, v6
    brif v7, bb1, bb2
  bb1:
    trap
  bb2:
    trap
}
"#;
    let (output, stats) = optimize(input);
    let expected = r#"func @branch_and_mask() {
  bb0:
    br bb2
  bb1:
    trap
  bb2:
    trap
}"#;
    assert_eq!(normalize_ir(&output), normalize_ir(expected));
    assert!(stats.rewrites > 0);
}

#[test]
fn canonicalizes_brif_from_cmp_select_mask_compare_zero() {
    let input = r#"
func @branch_cmp_mask(int:s32, int:s32) {
  bb0:
    v0: int:s32 = param 0
    v1: int:s32 = param 1
    v2: bool = icmp.le v0, v1
    v3: int:s32 = iconst 1
    v4: int:s32 = iconst 0
    v5: int:s32 = select v2, v3, v4
    v6: int:s32 = iconst 255
    v7: int:s32 = and v5, v6
    v8: int:s32 = iconst 0
    v9: bool = icmp.eq v7, v8
    brif v9, bb1, bb2
  bb1:
    trap
  bb2:
    trap
}
"#;
    let (output, stats) = optimize(input);
    let expected = r#"func @branch_cmp_mask(int:s32, int:s32) {
  bb0:
    v0: int:s32 = param 0
    v1: int:s32 = param 1
    v2: bool = icmp.le v0, v1
    brif v2, bb2, bb1
  bb1:
    trap
  bb2:
    trap
}"#;
    assert_eq!(normalize_ir(&output), normalize_ir(expected));
    assert_eq!(stats.per_rule["canonicalize_brif_intified_bool_compare"], 1);
}

#[test]
fn generalizes_mask_cleanup_to_non_255_odd_masks() {
    let input = r#"
func @branch_and_mask_three(bool) {
  bb0:
    v0: bool = param 0
    v1: int:s32 = iconst 1
    v2: int:s32 = iconst 0
    v3: int:s32 = select v0, v1, v2
    v4: int:s32 = iconst 3
    v5: int:s32 = and v3, v4
    v6: int:s32 = add v5, v1
    unreachable
}
"#;
    let (output, stats) = optimize(input);
    let expected = r#"func @branch_and_mask_three(bool) {
  bb0:
    v0: bool = param 0
    v1: int:u1 = iconst 1
    v2: int:u1 = iconst 0
    v3: int:u1 = select v0, v1, v2
    v4: int:u2 = add v3, v1
    unreachable
}"#;
    assert_eq!(normalize_ir(&output), normalize_ir(expected));
    assert_eq!(stats.per_rule["and_best_int_annotation_u1_lowbit_one"], 1);
}

#[test]
fn does_not_rewrite_even_masks() {
    let input = r#"
func @branch_and_mask_two(bool) {
  bb0:
    v0: bool = param 0
    v1: int:s32 = iconst 1
    v2: int:s32 = iconst 0
    v3: int:s32 = select v0, v1, v2
    v4: int:s32 = iconst 2
    v5: int:s32 = and v3, v4
    v6: int:s32 = add v5, v1
    unreachable
}
"#;
    let (output, stats) = optimize(input);
    let expected = r#"func @branch_and_mask_two(bool) {
  bb0:
    v0: bool = param 0
    v1: int:u1 = iconst 1
    v2: int:u1 = iconst 0
    v3: int:u1 = select v0, v1, v2
    v4: int:u2 = iconst 2
    v5: int:u2 = and v3, v4
    v6: int:u2 = add v5, v1
    unreachable
}"#;
    assert_eq!(normalize_ir(&output), normalize_ir(expected));
    assert_eq!(
        stats
            .per_rule
            .get("and_best_int_annotation_u1_lowbit_one")
            .copied()
            .unwrap_or(0),
        0
    );
}

#[test]
fn collapses_xor_inversion_ladder() {
    let input = r#"
func @branch_xor_invert() {
  bb0:
    v0: bool = bconst true
    v1: int = iconst 1
    v2: int = iconst 0
    v3: int = select v0, v1, v2
    v4: int = iconst 1
    v5: int = xor v3, v4
    v6: int = iconst 1
    v7: bool = icmp.eq v5, v6
    brif v7, bb1, bb2
  bb1:
    trap
  bb2:
    trap
}
"#;
    let (output, stats) = optimize(input);
    let expected = r#"func @branch_xor_invert() {
  bb0:
    br bb2
  bb1:
    trap
  bb2:
    trap
}"#;
    assert_eq!(normalize_ir(&output), normalize_ir(expected));
    assert!(stats.rewrites > 0);
}

#[test]
fn keeps_shared_select_alive_when_only_mask_is_removed() {
    let input = r#"
func @mask_value(bool) {
  bb0:
    v0: bool = param 0
    v1: int:s32 = iconst 1
    v2: int:s32 = iconst 0
    v3: int:s32 = select v0, v1, v2
    v4: int:s32 = iconst 255
    v5: int:s32 = and v3, v4
    v6: int:s32 = add v5, v1
    unreachable
}
"#;
    let (output, stats) = optimize(input);
    let expected = r#"func @mask_value(bool) {
  bb0:
    v0: bool = param 0
    v1: int:u1 = iconst 1
    v2: int:u1 = iconst 0
    v3: int:u1 = select v0, v1, v2
    v4: int:u2 = add v3, v1
    unreachable
}"#;
    assert_eq!(normalize_ir(&output), normalize_ir(expected));
    assert_eq!(stats.per_rule["and_best_int_annotation_u1_lowbit_one"], 1);
}

#[test]
fn promotes_single_stack_slot_to_ssa() {
    let input = r#"
func @mem2reg_single(int:s32) -> int:s32 {
  bb0(v0: mem):
    v1: ptr = stack_slot 4
    v2: int:s32 = param 0
    v3: mem = store.4 v2, v1, v0
    v4: int:s32 = load.4 v1, v3
    ret v4, v3
}
"#;
    let (output, stats) = optimize(input);
    let expected = r#"func @mem2reg_single(int:s32) -> int:s32 {
  bb0(v0: mem):
    v1: int:s32 = param 0
    ret v1, v0
}"#;
    assert_eq!(normalize_ir(&output), normalize_ir(expected));
    assert_eq!(stats.promoted_slots, 1);
    assert_eq!(stats.promoted_slices, 1);
    assert_eq!(stats.promoted_loads, 1);
    assert_eq!(stats.eliminated_stores, 1);
}

#[test]
fn promotes_stack_slot_across_branch_merge() {
    let input = r#"
func @mem2reg_branch(bool, int:s32, int:s32) -> int:s32 {
  bb0(v0: mem):
    v1: ptr = stack_slot 4
    v2: bool = param 0
    v3: int:s32 = param 1
    v4: int:s32 = param 2
    brif v2, bb1, bb2
  bb1:
    v5: mem = store.4 v3, v1, v0
    br bb3(v5)
  bb2:
    v6: mem = store.4 v4, v1, v0
    br bb3(v6)
  bb3(v7: mem):
    v8: int:s32 = load.4 v1, v7
    ret v8, v7
}
"#;
    let (output, stats) = optimize(input);
    let expected = r#"func @mem2reg_branch(bool, int:s32, int:s32) -> int:s32 {
  bb0(v0: mem):
    v1: bool = param 0
    v2: int:s32 = param 1
    v3: int:s32 = param 2
    brif v1, bb1, bb2
  bb1:
    br bb3(v0, v2)
  bb2:
    br bb3(v0, v3)
  bb3(v7: mem, v8: int:s32):
    ret v8:s32, v7
}"#;
    assert_eq!(normalize_ir(&output), normalize_ir(expected));
    assert_eq!(stats.promoted_slots, 1);
    assert_eq!(stats.promoted_slices, 1);
    assert_eq!(stats.promoted_loads, 1);
    assert_eq!(stats.eliminated_stores, 2);
}

#[test]
fn scalar_replaces_non_overlapping_stack_slices() {
    let input = r#"
func @sroa_split(int:s32, int:s32) -> int:s32 {
  bb0(v0: mem):
    v1: ptr = stack_slot 8
    v2: int:s32 = param 0
    v3: int:s32 = param 1
    v4: int:s64 = iconst 4
    v5: ptr = ptradd v1, v4
    v6: mem = store.4 v2, v1, v0
    v7: mem = store.4 v3, v5, v6
    v8: int:s32 = load.4 v1, v7
    v9: int:s32 = load.4 v5, v7
    v10: int:s32 = add v8, v9
    ret v10, v7
}
"#;
    let (output, stats) = optimize(input);
    assert!(
        !output.contains("stack_slot"),
        "slot should be removed:\n{output}"
    );
    assert!(
        !output.contains("ptradd"),
        "dead address calc should be removed:\n{output}"
    );
    assert!(
        !output.contains("store.4"),
        "stores should be removed:\n{output}"
    );
    assert!(
        !output.contains("load.4"),
        "loads should be removed:\n{output}"
    );
    assert_eq!(stats.promoted_slots, 1);
    assert_eq!(stats.promoted_slices, 2);
    assert_eq!(stats.promoted_loads, 2);
    assert_eq!(stats.eliminated_stores, 2);
}

#[test]
fn promotes_stack_slot_through_loop_region() {
    let input = r#"
func @mem2reg_loop(int:s32) -> int:s32 {
  bb0(v0: mem):
    v1: ptr = stack_slot 4
    v2: int:s32 = param 0
    v3: int:s32 = iconst 0
    v4: int:s32 = iconst 1
    v5: mem = store.4 v3, v1, v0
    br bb1(v5, v2)

  region loop {
    bb1(v6: mem, v7: int:s32):
      v8: bool = icmp.gt v7, v3
      brif v8, bb2, bb3(v6)

    bb2:
      v9: int:s32 = load.4 v1, v6
      v10: int:s32 = add v9, v4
      v11: mem = store.4 v10, v1, v6
      v12: int:s32 = sub v7, v4
      continue v11, v12
  }

  bb3(v13: mem):
    v14: int:s32 = load.4 v1, v13
    ret v14, v13
}
"#;
    let (output, stats) = optimize(input);
    assert!(
        !output.contains("stack_slot"),
        "loop promotion should remove slot:\n{output}"
    );
    assert!(
        !output.contains("store.4"),
        "loop promotion should remove stores:\n{output}"
    );
    assert!(
        !output.contains("load.4"),
        "loop promotion should remove loads:\n{output}"
    );
    assert!(
        output.contains("continue"),
        "loop structure should remain:\n{output}"
    );
    assert_eq!(stats.promoted_slots, 1);
    assert_eq!(stats.promoted_slices, 1);
    assert_eq!(stats.promoted_loads, 2);
    assert_eq!(stats.eliminated_stores, 2);
}

#[test]
fn does_not_promote_slot_passed_to_external_call() {
    let input = r#"
func @call_escape(int:s32) -> int:s32 {
  bb0(v0: mem):
    v1: ptr = stack_slot 4
    v2: int:s32 = param 0
    v3: mem = store.4 v2, v1, v0
    v4: ptr = symbol_addr @extern_sink
    v5: mem = call v4(v1), v3
    v6: int:s32 = load.4 v1, v5
    ret v6, v5
}
"#;
    let (output, stats) = optimize(input);
    assert!(
        output.contains("stack_slot"),
        "escaped slot must stay in memory:\n{output}"
    );
    assert!(
        output.contains("store.4"),
        "escaped slot store must remain:\n{output}"
    );
    assert!(
        output.contains("load.4"),
        "escaped slot load must remain:\n{output}"
    );
    assert_eq!(stats.promoted_slots, 0);
}

#[test]
fn still_promotes_local_slot_around_external_unrelated_call() {
    let input = r#"
func @call_unrelated(int:s32) -> int:s32 {
  bb0(v0: mem):
    v1: ptr = stack_slot 4
    v2: int:s32 = param 0
    v3: mem = store.4 v2, v1, v0
    v4: ptr = symbol_addr @extern_sink
    v5: mem = call v4(v2), v3
    v6: int:s32 = load.4 v1, v5
    ret v6, v5
}
"#;
    let (output, stats) = optimize(input);
    assert!(
        !output.contains("stack_slot"),
        "local slot should still promote:\n{output}"
    );
    assert!(
        !output.contains("store.4"),
        "promoted store should vanish:\n{output}"
    );
    assert!(
        !output.contains("load.4"),
        "promoted load should vanish:\n{output}"
    );
    assert!(
        output.contains("call"),
        "unrelated call should remain:\n{output}"
    );
    assert_eq!(stats.promoted_slots, 1);
}

#[test]
fn range_folds_branch_in_refined_successor() {
    let input = r#"
func @range_refine(int:u64) {
  bb0(v0: mem):
    v1: int:u64 = param 0
    v2: int:u64 = iconst 10
    v3: bool = icmp.lt v1, v2
    brif v3, bb1(v0), bb2(v0)
  bb1(v4: mem):
    v5: int:u64 = iconst 12
    v6: bool = icmp.lt v1, v5
    brif v6, bb3(v4), bb4(v4)
  bb2(v7: mem):
    ret v7
  bb3(v8: mem):
    ret v8
  bb4(v9: mem):
    trap
}
"#;
    let (output, stats) = optimize(input);
    let expected = r#"func @range_refine(int:u64) {
  bb0(v0: mem):
    v1: int:u64 = param 0
    v2: int:u4 = iconst 10
    v3: bool = icmp.lt v1, v2
    brif v3, bb1(v0), bb2(v0)
  bb1(v5: mem):
    v6: int:u4 = iconst 12
    br bb3(v5)
  bb2(v8: mem):
    ret v8
  bb3(v10: mem):
    ret v10
  bb4(v12: mem):
    trap
}"#;
    assert_eq!(normalize_ir(&output), normalize_ir(expected));
    assert!(stats.rewrites > 0);
}

#[test]
fn range_folds_branch_in_pointer_heavy_function() {
    let input = r#"
func @ptr_heavy_range_refine(ptr, int:u64) {
  bb0(v0: mem):
    v1: ptr = param 0
    v2: int:u64 = param 1
    v3: int:u64 = ptrtoaddr v1
    v4: int:u64 = iconst 10
    v5: bool = icmp.lt v2, v4
    brif v5, bb1(v0), bb2(v0)
  bb1(v6: mem):
    v7: int:u64 = iconst 12
    v8: bool = icmp.lt v2, v7
    brif v8, bb3(v6), bb4(v6)
  bb2(v9: mem):
    ret v9
  bb3(v10: mem):
    ret v10
  bb4(v11: mem):
    trap
}
"#;
    let (output, stats) = optimize(input);
    assert!(
        stats.rewrites > 0,
        "pointer-heavy branch should fold:\n{output}"
    );
    assert!(
        output.contains("ptrtoaddr"),
        "pointer op should remain unrelated:\n{output}"
    );
    assert!(
        output.contains("br bb3"),
        "refined integer branch should fold in pointer-heavy function:\n{output}"
    );
}

#[test]
fn range_folds_add_bound() {
    let input = r#"
func @range_add_u4(int:u4) {
  bb0(v0: mem):
    v1: int:u4 = param 0
    v2: int:u1 = iconst 1
    v3: int:u64 = add v1, v2
    v4: int:u5 = iconst 16
    v5: bool = icmp.le v3, v4
    brif v5, bb1(v0), bb2(v0)
  bb1(v6: mem):
    ret v6
  bb2(v7: mem):
    trap
}
"#;
    let (output, stats) = optimize(input);
    assert!(stats.rewrites > 0, "add-based range should fold:\n{output}");
    assert!(
        !output.contains("brif"),
        "branch should fold away:\n{output}"
    );
}

#[test]
fn range_folds_sub_bound() {
    let input = r#"
func @range_sub_u4(int:u4) {
  bb0(v0: mem):
    v1: int:u4 = param 0
    v2: int:u1 = iconst 1
    v3: int:s64 = sub v1, v2
    v4: int:s5 = iconst 14
    v5: bool = icmp.le v3, v4
    brif v5, bb1(v0), bb2(v0)
  bb1(v6: mem):
    ret v6
  bb2(v7: mem):
    trap
}
"#;
    let (output, stats) = optimize(input);
    assert!(stats.rewrites > 0, "sub-based range should fold:\n{output}");
    assert!(
        !output.contains("brif"),
        "branch should fold away:\n{output}"
    );
}

#[test]
fn range_folds_shr_bound() {
    let input = r#"
func @range_shr_u4(int:u4) {
  bb0(v0: mem):
    v1: int:u4 = param 0
    v2: int:u1 = iconst 1
    v3: int:u64 = shr v1, v2
    v4: int:u4 = iconst 8
    v5: bool = icmp.lt v3, v4
    brif v5, bb1(v0), bb2(v0)
  bb1(v6: mem):
    ret v6
  bb2(v7: mem):
    trap
}
"#;
    let (output, stats) = optimize(input);
    assert!(stats.rewrites > 0, "shr-based range should fold:\n{output}");
    assert!(
        !output.contains("brif"),
        "branch should fold away:\n{output}"
    );
}

#[test]
fn range_folds_zext_bound() {
    let input = r#"
func @range_zext_u8(int:u8) {
  bb0(v0: mem):
    v1: int:u8 = param 0
    v2: int:u64 = zext v1, 8
    v3: int:u9 = iconst 256
    v4: bool = icmp.lt v2, v3
    brif v4, bb1(v0), bb2(v0)
  bb1(v5: mem):
    ret v5
  bb2(v6: mem):
    trap
}
"#;
    let (output, stats) = optimize(input);
    assert!(
        stats.rewrites > 0,
        "zext-based range should fold:\n{output}"
    );
    assert!(
        !output.contains("brif"),
        "branch should fold away:\n{output}"
    );
}

#[test]
fn at_use_annotates_refined_branch_argument() {
    let input = r#"
func @annotates_branch_edge_arg(int:u64) {
  bb0(v0: mem):
    v1: int:u64 = param 0
    v2: int:u64 = iconst 10
    v3: bool = icmp.lt v1, v2
    brif v3, bb1(v0, v1), bb2(v0, v1)
  bb1(v4: mem, v5: int:u64):
    ret v4
  bb2(v6: mem, v7: int:u64):
    ret v6
}
"#;
    let (output, stats) = optimize(input);
    let expected = r#"func @annotates_branch_edge_arg(int:u64) {
  bb0(v0: mem):
    v1: int:u64 = param 0
    v2: int:u4 = iconst 10
    v3: bool = icmp.lt v1, v2
    brif v3, bb1(v0, v1:u4), bb2(v0, v1)
  bb1(v5: mem, v6: int:u64):
    ret v5
  bb2(v8: mem, v9: int:u64):
    ret v8
}"#;
    assert_eq!(normalize_ir(&output), normalize_ir(expected));
    assert!(stats.per_rule["at_use_strengthen_operand"] > 0);
}

#[test]
fn range_folds_branch_inside_loop_region() {
    let input = r#"
func @range_loop_region() {
  bb0(v0: mem):
    v1: int:u64 = iconst 0
    br bb1(v0, v1)

  region loop {
    bb1(v2: mem, v3: int:u64):
      v4: int:u64 = iconst 10
      v5: bool = icmp.lt v3, v4
      brif v5, bb2(v2, v3), bb4(v2)

    bb2(v6: mem, v7: int:u64):
      v8: int:u64 = iconst 12
      v9: bool = icmp.lt v7, v8
      brif v9, bb3(v6, v7), bb5(v6)

    bb3(v10: mem, v11: int:u64):
      v12: int:u64 = iconst 1
      v13: int:u64 = add v11, v12
      continue v10, v13
  }

  bb4(v14: mem):
    ret v14

  bb5(v15: mem):
    trap
}
"#;
    let (output, stats) = optimize(input);
    assert!(
        output.contains("continue"),
        "loop structure should remain:\n{output}"
    );
    assert!(
        output.contains("br bb3"),
        "refined loop branch should fold to direct branch:\n{output}"
    );
    assert!(stats.rewrites > 0);
}

#[test]
fn cfg_threads_forwarding_block() {
    let input = r#"
func @thread_forward() {
  bb0(v0: mem):
    v1: bool = bconst true
    brif v1, bb1(v0), bb2(v0)
  bb1(v3: mem):
    br bb3(v3)
  bb2(v4: mem):
    ret v4
  bb3(v5: mem):
    ret v5
}
"#;
    let (output, stats) = optimize(input);
    let expected = r#"func @thread_forward() {
  bb0(v0: mem):
    br bb3(v0)
  bb1(v2: mem):
    br bb3(v2)
  bb2(v4: mem):
    ret v4
  bb3(v6: mem):
    ret v6
}"#;
    assert_eq!(normalize_ir(&output), normalize_ir(expected));
    assert!(stats.rewrites > 0);
}

#[test]
fn cfg_threads_forwarding_block_args() {
    let input = r#"
func @thread_forward_args(int:s32) -> int:s32 {
  bb0(v0: mem):
    v1: int:s32 = param 0
    br bb1(v0, v1)
  bb1(v2: mem, v3: int:s32):
    br bb2(v2, v3)
  bb2(v4: mem, v5: int:s32):
    ret v5, v4
}
"#;
    let (output, stats) = optimize(input);
    let expected = r#"func @thread_forward_args(int:s32) -> int:s32 {
  bb0(v0: mem):
    v1: int:s32 = param 0
    br bb2(v0, v1)
  bb1(v3: mem, v4: int:s32):
    br bb2(v3, v4:s32)
  bb2(v6: mem, v7: int:s32):
    ret v7:s32, v6
}"#;
    assert_eq!(normalize_ir(&output), normalize_ir(expected));
    assert!(stats.rewrites > 0);
}

#[test]
fn cfg_collapses_same_target_brif_after_threading() {
    let input = r#"
func @collapse_same_target(bool) {
  bb0(v0: mem):
    v1: bool = param 0
    brif v1, bb1(v0), bb2(v0)
  bb1(v3: mem):
    br bb3(v3)
  bb2(v4: mem):
    br bb3(v4)
  bb3(v5: mem):
    ret v5
}
"#;
    let (output, stats) = optimize(input);
    let expected = r#"func @collapse_same_target(bool) {
  bb0(v0: mem):
    v1: bool = param 0
    br bb3(v0)
  bb1(v3: mem):
    br bb3(v3)
  bb2(v5: mem):
    br bb3(v5)
  bb3(v7: mem):
    ret v7
}"#;
    assert_eq!(normalize_ir(&output), normalize_ir(expected));
    assert!(stats.rewrites > 0);
}

#[test]
fn cfg_removes_unreachable_after_constant_branch() {
    let input = r#"
func @remove_unreachable() {
  bb0(v0: mem):
    v1: bool = bconst true
    brif v1, bb1(v0), bb2(v0)
  bb1(v3: mem):
    ret v3
  bb2(v4: mem):
    trap
}
"#;
    let (output, stats) = optimize(input);
    let expected = r#"func @remove_unreachable() {
  bb0(v0: mem):
    br bb1(v0)
  bb1(v2: mem):
    ret v2
  bb2(v4: mem):
    trap
}"#;
    assert_eq!(normalize_ir(&output), normalize_ir(expected));
    assert!(stats.rewrites > 0);
}

#[test]
fn inlines_direct_same_module_call() {
    let input = r#"
func @id(int:s32) -> int:s32 {
  bb0(v0: mem):
    v1: int:s32 = param 0
    ret v1, v0
}

func @caller(int:s32) -> int:s32 {
  bb0(v0: mem):
    v1: int:s32 = param 0
    v2: ptr = symbol_addr @id
    v3: mem, v4: int:s32 = call v2(v1), v0 -> int:s32
    ret v4, v3
}
"#;
    let (output, stats) = optimize(input);
    assert!(
        !output.contains(" = call "),
        "direct same-module calls should inline:\n{output}"
    );
    assert_eq!(stats.inlined_calls, 1);
}

#[test]
fn inlines_transitive_same_module_chain() {
    let input = r#"
func @leaf(int:s32) -> int:s32 {
  bb0(v0: mem):
    v1: int:s32 = param 0
    v2: int:s32 = iconst 1
    v3: int:s32 = add v1, v2
    ret v3, v0
}

func @mid(int:s32) -> int:s32 {
  bb0(v0: mem):
    v1: int:s32 = param 0
    v2: ptr = symbol_addr @leaf
    v3: mem, v4: int:s32 = call v2(v1), v0 -> int:s32
    ret v4, v3
}

func @top(int:s32) -> int:s32 {
  bb0(v0: mem):
    v1: int:s32 = param 0
    v2: ptr = symbol_addr @mid
    v3: mem, v4: int:s32 = call v2(v1), v0 -> int:s32
    ret v4, v3
}
"#;
    let (output, stats) = optimize(input);
    assert!(
        !output.contains(" = call "),
        "small acyclic call chains should inline transitively:\n{output}"
    );
    assert_eq!(stats.inlined_calls, 2);
}

#[test]
fn inlines_single_caller_medium_leaf() {
    let input = r#"
func @medium_leaf(int:s32) -> int:s32 {
  bb0(v0: mem):
    v1: int:s32 = param 0
    v2: int:s32 = iconst 1
    v3: int:s32 = add v1, v2
    v4: int:s32 = iconst 2
    v5: int:s32 = add v3, v4
    v6: int:s32 = iconst 3
    v7: int:s32 = add v5, v6
    v8: int:s32 = iconst 4
    v9: int:s32 = add v7, v8
    v10: int:s32 = iconst 5
    v11: int:s32 = add v9, v10
    v12: int:s32 = iconst 6
    v13: int:s32 = add v11, v12
    v14: int:s32 = iconst 7
    v15: int:s32 = add v13, v14
    v16: int:s32 = iconst 8
    v17: int:s32 = add v15, v16
    v18: int:s32 = iconst 9
    v19: int:s32 = add v17, v18
    v20: int:s32 = iconst 10
    v21: int:s32 = add v19, v20
    v22: int:s32 = iconst 11
    v23: int:s32 = add v21, v22
    v24: int:s32 = iconst 12
    v25: int:s32 = add v23, v24
    ret v25, v0
}

func @caller(int:s32) -> int:s32 {
  bb0(v0: mem):
    v1: int:s32 = param 0
    v2: ptr = symbol_addr @medium_leaf
    v3: mem, v4: int:s32 = call v2(v1), v0 -> int:s32
    ret v4, v3
}
"#;
    let (output, stats) = optimize(input);
    assert!(
        !output.contains(" = call "),
        "single-caller medium leaf should inline:\n{output}"
    );
    assert_eq!(stats.inlined_calls, 1);
}

#[test]
fn inlines_single_caller_large_leaf() {
    let input = r#"
func @large_leaf(int:s32) -> int:s32 {
  bb0(v0: mem):
    v1: int:s32 = param 0
    v2: int:s32 = iconst 1
    v3: int:s32 = add v1, v2
    v4: int:s32 = iconst 2
    v5: int:s32 = add v3, v4
    v6: int:s32 = iconst 3
    v7: int:s32 = add v5, v6
    v8: int:s32 = iconst 4
    v9: int:s32 = add v7, v8
    v10: int:s32 = iconst 5
    v11: int:s32 = add v9, v10
    v12: int:s32 = iconst 6
    v13: int:s32 = add v11, v12
    v14: int:s32 = iconst 7
    v15: int:s32 = add v13, v14
    v16: int:s32 = iconst 8
    v17: int:s32 = add v15, v16
    v18: int:s32 = iconst 9
    v19: int:s32 = add v17, v18
    v20: int:s32 = iconst 10
    v21: int:s32 = add v19, v20
    v22: int:s32 = iconst 11
    v23: int:s32 = add v21, v22
    v24: int:s32 = iconst 12
    v25: int:s32 = add v23, v24
    v26: int:s32 = iconst 13
    v27: int:s32 = add v25, v26
    v28: int:s32 = iconst 14
    v29: int:s32 = add v27, v28
    v30: int:s32 = iconst 15
    v31: int:s32 = add v29, v30
    v32: int:s32 = iconst 16
    v33: int:s32 = add v31, v32
    v34: int:s32 = iconst 17
    v35: int:s32 = add v33, v34
    v36: int:s32 = iconst 18
    v37: int:s32 = add v35, v36
    v38: int:s32 = iconst 19
    v39: int:s32 = add v37, v38
    v40: int:s32 = iconst 20
    v41: int:s32 = add v39, v40
    v42: int:s32 = iconst 21
    v43: int:s32 = add v41, v42
    v44: int:s32 = iconst 22
    v45: int:s32 = add v43, v44
    v46: int:s32 = iconst 23
    v47: int:s32 = add v45, v46
    v48: int:s32 = iconst 24
    v49: int:s32 = add v47, v48
    v50: int:s32 = iconst 25
    v51: int:s32 = add v49, v50
    ret v51, v0
}

func @caller(int:s32) -> int:s32 {
  bb0(v0: mem):
    v1: int:s32 = param 0
    v2: ptr = symbol_addr @large_leaf
    v3: mem, v4: int:s32 = call v2(v1), v0 -> int:s32
    ret v4, v3
}
"#;
    let (output, stats) = optimize(input);
    assert!(
        !output.contains(" = call "),
        "single-caller large leaf should inline:\n{output}"
    );
    assert_eq!(stats.inlined_calls, 1);
}

#[test]
fn inlines_single_caller_large_simple_cfg() {
    let input = r#"
func @large_cfg_helper(int:s32) -> int:s32 {
  bb0(v0: mem):
    v1: int:s32 = param 0
    v2: int:s32 = iconst 1
    v3: int:s32 = add v1, v2
    v4: int:s32 = iconst 2
    v5: int:s32 = add v3, v4
    v6: int:s32 = iconst 3
    v7: int:s32 = add v5, v6
    v8: int:s32 = iconst 4
    v9: int:s32 = add v7, v8
    v10: int:s32 = iconst 5
    v11: int:s32 = add v9, v10
    v12: int:s32 = iconst 6
    v13: int:s32 = add v11, v12
    v14: int:s32 = iconst 7
    v15: int:s32 = add v13, v14
    v16: int:s32 = iconst 8
    v17: int:s32 = add v15, v16
    v18: int:s32 = iconst 9
    v19: int:s32 = add v17, v18
    v20: int:s32 = iconst 10
    v21: int:s32 = add v19, v20
    v22: int:s32 = iconst 11
    v23: int:s32 = add v21, v22
    v24: int:s32 = iconst 12
    v25: int:s32 = add v23, v24
    v26: int:s32 = iconst 13
    v27: int:s32 = add v25, v26
    v28: int:s32 = iconst 14
    v29: int:s32 = add v27, v28
    v30: int:s32 = iconst 15
    v31: int:s32 = add v29, v30
    v32: int:s32 = iconst 16
    v33: int:s32 = add v31, v32
    v34: int:s32 = iconst 17
    v35: int:s32 = add v33, v34
    v36: int:s32 = iconst 18
    v37: int:s32 = add v35, v36
    v38: int:s32 = iconst 19
    v39: int:s32 = add v37, v38
    v40: int:s32 = iconst 20
    v41: int:s32 = add v39, v40
    v42: int:s32 = iconst 21
    v43: int:s32 = add v41, v42
    v44: int:s32 = iconst 22
    v45: int:s32 = add v43, v44
    v46: int:s32 = iconst 23
    v47: int:s32 = add v45, v46
    v48: int:s32 = iconst 24
    v49: int:s32 = add v47, v48
    v50: int:s32 = iconst 25
    v51: int:s32 = add v49, v50
    v52: int:s32 = iconst 0
    v53: bool = icmp.lt v51, v52
    brif v53, bb1(v0, v51), bb2(v0, v51)
  bb1(v54: mem, v55: int:s32):
    ret v55, v54
  bb2(v56: mem, v57: int:s32):
    v58: int:s32 = iconst 99
    v59: int:s32 = add v57, v58
    ret v59, v56
}

func @caller(int:s32) -> int:s32 {
  bb0(v0: mem):
    v1: int:s32 = param 0
    v2: ptr = symbol_addr @large_cfg_helper
    v3: mem, v4: int:s32 = call v2(v1), v0 -> int:s32
    ret v4, v3
}
"#;
    let (output, stats) = optimize(input);
    assert!(
        !output.contains(" = call "),
        "single-caller simple CFG helper should inline:\n{output}"
    );
    assert_eq!(stats.inlined_calls, 1);
}

#[test]
fn inlines_two_callsite_memory_wrapper() {
    let input = r#"
func @memory_helper(ptr, ptr, int:s32) -> int:s32 {
  bb0(v0: mem):
    v1: ptr = param 0
    v2: ptr = param 1
    v3: int:s32 = param 2
    v4: int:s32 = load.4 v1, v0
    v5: int:s32 = add v4, v3
    v6: mem = store.4 v5, v2, v0
    v7: int:s32 = load.4 v2, v6
    v8: int:s32 = add v7, v3
    v9: int:s32 = add v8, v3
    v10: int:s32 = add v9, v3
    v11: int:s32 = add v10, v3
    v12: int:s32 = add v11, v3
    v13: int:s32 = add v12, v3
    v14: int:s32 = add v13, v3
    v15: int:s32 = add v14, v3
    v16: int:s32 = add v15, v3
    v17: bool = icmp.gt v16, v3
    brif v17, bb1(v6, v16), bb2(v6, v16)
  bb1(v18: mem, v19: int:s32):
    ret v19, v18
  bb2(v20: mem, v21: int:s32):
    v22: int:s32 = sub v21, v3
    ret v22, v20
}

func @caller_a(ptr, ptr, int:s32) -> int:s32 {
  bb0(v0: mem):
    v1: ptr = param 0
    v2: ptr = param 1
    v3: int:s32 = param 2
    v4: ptr = symbol_addr @memory_helper
    v5: mem, v6: int:s32 = call v4(v1, v2, v3), v0 -> int:s32
    ret v6, v5
}

func @caller_b(ptr, ptr, int:s32) -> int:s32 {
  bb0(v0: mem):
    v1: ptr = param 0
    v2: ptr = param 1
    v3: int:s32 = param 2
    v4: ptr = symbol_addr @memory_helper
    v5: mem, v6: int:s32 = call v4(v2, v1, v3), v0 -> int:s32
    ret v6, v5
}
"#;
    let (output, stats) = optimize(input);
    assert!(
        !output.contains(" = call "),
        "two-callsite memory wrapper should inline:\n{output}"
    );
    assert_eq!(stats.inlined_calls, 2);
}

#[test]
fn does_not_inline_recursive_cycle() {
    let input = r#"
func @a(int:s32) -> int:s32 {
  bb0(v0: mem):
    v1: int:s32 = param 0
    v2: ptr = symbol_addr @b
    v3: mem, v4: int:s32 = call v2(v1), v0 -> int:s32
    ret v4, v3
}

func @b(int:s32) -> int:s32 {
  bb0(v0: mem):
    v1: int:s32 = param 0
    v2: ptr = symbol_addr @a
    v3: mem, v4: int:s32 = call v2(v1), v0 -> int:s32
    ret v4, v3
}
"#;
    let (output, stats) = optimize(input);
    assert!(
        output.contains(" = call "),
        "recursive SCCs must not inline:\n{output}"
    );
    assert_eq!(stats.inlined_calls, 0);
}

#[test]
fn inlines_call_ret2_uses() {
    let input = r#"
func @pair(int:s32) -> int:s32 {
  bb0(v0: mem):
    v1: int:s32 = param 0
    v2: int:s32 = iconst 7
    ret v1, v2, v0
}

func @caller(int:s32) -> int:s32 {
  bb0(v0: mem):
    v1: int:s32 = param 0
    v2: ptr = symbol_addr @pair
    v3: mem, v4: int:s32 = call v2(v1), v0 -> int:s32
    v5: int:s32 = call_ret2 v3
    v6: int:s32 = add v4, v5
    ret v6, v3
}
"#;
    let (output, stats) = optimize(input);
    assert!(
        !output.contains(" = call "),
        "inlined call sites should not leave call instructions behind:\n{output}"
    );
    assert!(
        !output.contains("call_ret2"),
        "call_ret2 users should rewrite to the inlined secondary return value:\n{output}"
    );
    assert_eq!(stats.inlined_calls, 1);
}

#[test]
fn skips_inlining_when_argument_types_do_not_match() {
    let input = r#"
func @as_ref(ptr, int:i64) -> ptr {
  bb0(v0: mem):
    v1: ptr = param 0
    v2: int:i64 = param 1
    ret v1, v2, v0
}

func @caller(ptr) -> int:i64 {
  bb0(v0: mem):
    v1: ptr = param 0
    v2: int:i64 = load.8 v1, v0
    v3: int:i64 = iconst 8
    v4: ptr = ptradd v1, v3
    v5: int:i64 = load.8 v4, v0
    v6: ptr = symbol_addr @as_ref
    v7: mem, v8: ptr = call v6(v2, v5), v0 -> ptr
    v9: int:i64 = call_ret2 v7
    ret v9, v7
}
"#;
    let (output, stats) = optimize(input);
    assert!(
        output.contains(" = call "),
        "mismatched local call signatures must not inline:\n{output}"
    );
    assert_eq!(stats.inlined_calls, 0);
}

#[test]
fn inlines_region_aware_callee() {
    let input = r#"
func @loop_region(int:s32) -> int:s32 {
  bb0(v0: mem):
    v1: int:s32 = param 0
    br bb1(v1)

  region loop {
    bb1(v2: int:s32):
      v3: int:s32 = iconst 0
      v4: bool = icmp.eq v2, v3
      brif v4, bb2, bb3
    bb2:
      continue v1
    bb3:
      region_yield v2
  }

  bb4:
    ret v1, v0
}

func @caller(int:s32) -> int:s32 {
  bb0(v0: mem):
    v1: int:s32 = param 0
    v2: ptr = symbol_addr @loop_region
    v3: mem, v4: int:s32 = call v2(v1), v0 -> int:s32
    ret v4, v3
}
"#;
    let (output, stats) = optimize(input);
    assert!(
        !output.contains(" = call "),
        "region-aware callees should inline:\n{output}"
    );
    assert!(
        output.contains("region loop"),
        "the cloned callee region structure should remain in the caller:\n{output}"
    );
    assert_eq!(stats.inlined_calls, 1);
}

#[test]
fn inlining_remaps_cleanup_labels_to_cloned_landing_pad_blocks() {
    let input = r#"
func @sink() {
  bb0(v0: mem):
    ret v0
}

func @helper(int:s32) -> int:s32 {
  bb0(v0: mem):
    v1: int:s32 = param 0
    ret v1, v0
}

func @caller(int:s32) -> int:s32 {
  bb0(v0: mem):
    v1: int:s32 = param 0
    v2: ptr = symbol_addr @helper
    v3: mem, v4: int:s32 = call v2(v1), v0 -> int:s32
    v5: ptr = symbol_addr @sink
    v6: mem = call v5(), v3
    ret v4, v6
  bb1(v7: mem):
    v8: ptr = symbol_addr @sink
    v9: int:s32 = iconst 0
    ret v9, v7
}
"#;
    let mut module = parse_module(input).unwrap_or_else(|e| panic!("parse error: {e}"));

    let caller_idx = module
        .functions
        .iter()
        .position(|func| module.symbols.resolve(func.name) == "caller")
        .expect("caller function");
    {
        let caller = &mut module.functions[caller_idx];
        let cleanup_block = collect_block_refs(caller)[1];
        let cleanup_head = caller
            .block(cleanup_block)
            .first_inst
            .expect("caller cleanup block should not be empty");
        caller.inst_pool.inst_mut(cleanup_head).op = Op::LandingPad;
        let mut caller_calls = 0;
        for node in caller.inst_pool.iter_mut() {
            if let Op::Call(_, _, _, cleanup_label) = &mut node.inst.op {
                caller_calls += 1;
                if caller_calls == 2 {
                    *cleanup_label = Some(cleanup_block.index());
                }
            }
        }
        assert_eq!(caller_calls, 2, "caller should have exactly two calls");
    }

    let stats = optimize_module(&mut module);
    let verify = verify_module(&module);
    assert!(verify.is_ok(), "optimized module should verify: {verify}");
    assert_eq!(stats.inlined_calls, 1);

    let caller = module
        .functions
        .iter()
        .find(|func| module.symbols.resolve(func.name) == "caller")
        .expect("optimized caller function");
    let cleanup_labels = caller
        .inst_pool
        .iter_insts()
        .filter_map(|(_, inst)| match &inst.op {
            Op::Call(_, _, _, Some(cleanup_label)) => Some(*cleanup_label),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(
        cleanup_labels.len(),
        1,
        "inlined caller should retain the cleanup-labeled sink call:\n{module}"
    );
    for cleanup_label in cleanup_labels {
        let cleanup_block = collect_block_refs(caller)
            .into_iter()
            .find(|block| block.index() == cleanup_label)
            .expect("cleanup label should name an existing block");
        let first_inst = caller
            .block(cleanup_block)
            .first_inst
            .expect("cleanup block should contain landing_pad");
        assert!(
            matches!(caller.inst(first_inst).op, Op::LandingPad),
            "cleanup label must target a landing-pad wrapper block:\n{module}"
        );
    }
}

#[test]
fn promotes_whole_aggregate_stack_slot() {
    let input = r#"
func @aggregate_slot(struct{int, bool}) -> struct{int, bool} {
  bb0(v0: mem):
    v1: ptr = stack_slot 9
    v2: struct{int, bool} = param 0
    v3: mem = store.9 v2, v1, v0
    v4: struct{int, bool} = load.9 v1, v3
    ret v4, v3
}
"#;
    let (output, stats) = optimize(input);
    assert!(
        !output.contains("stack_slot"),
        "aggregate slot should promote:\n{output}"
    );
    assert!(
        !output.contains("store.9"),
        "aggregate store should vanish:\n{output}"
    );
    assert!(
        !output.contains("load.9"),
        "aggregate load should vanish:\n{output}"
    );
    assert_eq!(stats.promoted_slots, 1);
    assert_eq!(stats.promoted_slices, 1);
    assert_eq!(stats.promoted_loads, 1);
    assert_eq!(stats.eliminated_stores, 1);
}

#[test]
fn does_not_promote_atomic_slot() {
    let input = r#"
func @atomic_escape(int:s32) -> int:s32 {
  bb0(v0: mem):
    v1: ptr = stack_slot 4
    v2: int:s32 = param 0
    v3: mem = store.atomic.release v2, v1, v0
    v4: mem, v5: int:s32 = load.atomic.acquire v1, v3
    ret v5, v4
}
"#;
    let (output, stats) = optimize(input);
    assert!(
        output.contains("stack_slot"),
        "atomic slot must remain in memory:\n{output}"
    );
    assert!(
        output.contains("store.atomic"),
        "atomic store must remain:\n{output}"
    );
    assert!(
        output.contains("load.atomic"),
        "atomic load must remain:\n{output}"
    );
    assert_eq!(stats.promoted_slots, 0);
}

#[test]
fn does_not_promote_slot_with_memset() {
    let input = r#"
func @bulk_escape() -> int:s32 {
  bb0(v0: mem):
    v1: ptr = stack_slot 4
    v2: int:s32 = iconst 0
    v3: int:s64 = iconst 4
    v4: mem = memset v1, v2, v3, v0
    v5: int:s32 = load.4 v1, v4
    ret v5, v4
}
"#;
    let (output, stats) = optimize(input);
    assert!(
        output.contains("stack_slot"),
        "bulk-memory slot must remain:\n{output}"
    );
    assert!(output.contains("memset"), "memset must remain:\n{output}");
    assert!(output.contains("load.4"), "load must remain:\n{output}");
    assert_eq!(stats.promoted_slots, 0);
}

#[test]
fn does_not_promote_slot_with_memcopy() {
    let input = r#"
func @bulk_copy(int:s32) -> int:s32 {
  bb0(v0: mem):
    v1: ptr = stack_slot 4
    v2: ptr = stack_slot 4
    v3: int:s32 = param 0
    v4: mem = store.4 v3, v2, v0
    v5: int:s64 = iconst 4
    v6: mem = memcopy v1, v2, v5, v4
    v7: int:s32 = load.4 v1, v6
    ret v7, v6
}
"#;
    let (output, stats) = optimize(input);
    assert!(
        output.contains("memcopy"),
        "memcopy slot must remain:\n{output}"
    );
    assert!(
        output.contains("stack_slot"),
        "memcopy addresses must remain:\n{output}"
    );
    assert_eq!(stats.promoted_slots, 0);
}

#[test]
fn forms_bulk_memcopy_from_static_symbol() {
    let input = r#"
data @blob = "\x01\x02\x03\x04\x05\x06\x07\x08\x11\x12\x13\x14\x15\x16\x17\x18\x21\x22\x23\x24\x25\x26\x27\x28\x31\x32\x33\x34\x35\x36\x37\x38"

func @copy_init() {
  bb0(v0: mem):
    v1: ptr = stack_slot 32
    v2: ptr = symbol_addr @blob
    v3: int:i64 = load.8 v2, v0
    v4: mem = store.8 v3, v1, v0
    v5: int:i64 = iconst 8
    v6: ptr = ptradd v2, v5
    v7: int:i64 = load.8 v6, v4
    v8: ptr = ptradd v1, v5
    v9: mem = store.8 v7, v8, v4
    v10: int:i64 = iconst 16
    v11: ptr = ptradd v2, v10
    v12: int:i64 = load.8 v11, v9
    v13: ptr = ptradd v1, v10
    v14: mem = store.8 v12, v13, v9
    v15: int:i64 = iconst 24
    v16: ptr = ptradd v2, v15
    v17: int:i64 = load.8 v16, v14
    v18: ptr = ptradd v1, v15
    v19: mem = store.8 v17, v18, v14
    v20: ptr = symbol_addr @extern_sink
    v21: mem = call v20(v1), v19
    ret v21
}
"#;
    let (output, stats) = optimize(input);
    assert!(output.contains("memcopy"), "expected memcopy:\n{output}");
    assert!(
        !output.contains("store.8"),
        "store chain should be gone:\n{output}"
    );
    assert_eq!(stats.per_rule["form_bulk_memcopy"], 1);
}

#[test]
fn forms_bulk_memset_from_zero_static_symbol() {
    let input = r#"
data @zeros = "\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00"

func @zero_init() {
  bb0(v0: mem):
    v1: ptr = stack_slot 32
    v2: ptr = symbol_addr @zeros
    v3: int:i64 = load.8 v2, v0
    v4: mem = store.8 v3, v1, v0
    v5: int:i64 = iconst 8
    v6: ptr = ptradd v2, v5
    v7: int:i64 = load.8 v6, v4
    v8: ptr = ptradd v1, v5
    v9: mem = store.8 v7, v8, v4
    v10: int:i64 = iconst 16
    v11: ptr = ptradd v2, v10
    v12: int:i64 = load.8 v11, v9
    v13: ptr = ptradd v1, v10
    v14: mem = store.8 v12, v13, v9
    v15: int:i64 = iconst 24
    v16: ptr = ptradd v2, v15
    v17: int:i64 = load.8 v16, v14
    v18: ptr = ptradd v1, v15
    v19: mem = store.8 v17, v18, v14
    v20: ptr = symbol_addr @extern_sink
    v21: mem = call v20(v1), v19
    ret v21
}
"#;
    let (output, stats) = optimize(input);
    assert!(output.contains("memset"), "expected memset:\n{output}");
    assert!(
        !output.contains("store.8"),
        "store chain should be gone:\n{output}"
    );
    assert_eq!(stats.per_rule["form_bulk_memset_zero"], 1);
}

#[test]
fn forms_bulk_memset_from_repeated_zero_static_symbol_block() {
    let input = r#"
data @zeros16 = "\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00"

func @zero_repeat_init() {
  bb0(v0: mem):
    v1: ptr = stack_slot 32
    v2: ptr = symbol_addr @zeros16
    v3: int:i64 = load.8 v2, v0
    v4: mem = store.8 v3, v1, v0
    v5: int:i64 = iconst 8
    v6: ptr = ptradd v2, v5
    v7: int:i64 = load.8 v6, v4
    v8: ptr = ptradd v1, v5
    v9: mem = store.8 v7, v8, v4
    v10: int:i64 = iconst 16
    v11: ptr = ptradd v1, v10
    v12: int:i64 = load.8 v2, v9
    v13: mem = store.8 v12, v11, v9
    v14: int:i64 = iconst 24
    v15: ptr = ptradd v1, v14
    v16: int:i64 = load.8 v6, v13
    v17: mem = store.8 v16, v15, v13
    v18: ptr = symbol_addr @extern_sink
    v19: mem = call v18(v1), v17
    ret v19
}
"#;
    let (output, stats) = optimize(input);
    assert!(output.contains("memset"), "expected memset:\n{output}");
    assert!(
        !output.contains("store.8"),
        "store chain should be gone:\n{output}"
    );
    assert_eq!(stats.per_rule["form_bulk_memset_zero"], 1);
}

#[test]
fn forms_scalar_swap_from_memcpy_memmove_chain() {
    let input = r#"
func @swap4(ptr, ptr) {
  bb0(v0: mem):
    v1: ptr = param 0
    v2: ptr = param 1
    v3: ptr = stack_slot 4 align 4
    v4: int:i32 = iconst 0
    v5: mem = store.4 v4, v3, v0
    v6: ptr = symbol_addr @memcpy
    v7: int:i64 = iconst 1
    v8: int:i64 = iconst 4
    v9: int:u64 = mul v7, v8
    v10: mem, v11: int:u64 = call v6(v3, v1, v9), v5 -> int:u64
    v12: mem = memmove v1:align4, v2:align4, v9, v10
    v13: ptr = symbol_addr @memcpy
    v14: mem, v15: int:u64 = call v13(v2, v3, v9), v12 -> int:u64
    ret v14
}
"#;
    let (output, stats) = optimize(input);
    assert!(
        !output.contains("memmove"),
        "swap chain should remove memmove:\n{output}"
    );
    assert!(
        !output.contains("symbol_addr @memcpy"),
        "swap chain should remove memcpy calls:\n{output}"
    );
    assert!(
        output.contains("load.4") && output.contains("store.4"),
        "swap chain should become scalar load/store ops:\n{output}"
    );
    assert_eq!(stats.per_rule["form_scalar_swap"], 1);
}

#[test]
fn forms_scalar_swap_eight_byte_chain() {
    let input = r#"
func @swap8(ptr, ptr) {
  bb0(v0: mem):
    v1: ptr = param 0
    v2: ptr = param 1
    v3: ptr = stack_slot 8 align 8
    v4: int:i64 = iconst 0
    v5: mem = store.8 v4, v3, v0
    v6: ptr = symbol_addr @memcpy
    v7: int:u64 = iconst 8
    v8: mem, v9: int:u64 = call v6(v3, v1, v7), v5 -> int:u64
    v10: mem = memmove v1:align8, v2:align8, v7, v8
    v11: ptr = symbol_addr @memcpy
    v12: mem, v13: int:u64 = call v11(v2, v3, v7), v10 -> int:u64
    ret v12
}
"#;
    let (output, stats) = optimize(input);
    assert!(
        !output.contains("memmove"),
        "swap chain should remove memmove:\n{output}"
    );
    assert!(
        !output.contains("symbol_addr @memcpy"),
        "swap chain should remove memcpy calls:\n{output}"
    );
    assert!(
        output.contains("load.8") && output.contains("store.8"),
        "swap chain should become scalar load/store ops:\n{output}"
    );
    assert_eq!(stats.per_rule["form_scalar_swap"], 1);
}

#[test]
fn forms_scalar_swap_with_dynamic_ptradd_operands() {
    let input = r#"
func @swap8_dynamic(ptr, ptr, int:u64, int:u64) {
  bb0(v0: mem):
    v1: ptr = param 0
    v2: ptr = param 1
    v3: int:u64 = param 2
    v4: int:u64 = param 3
    v5: int:u1 = iconst 3
    v6: int:i64 = shl v3, v5
    v7: ptr = ptradd v1, v6
    v8: int:i64 = shl v4, v5
    v9: ptr = ptradd v2, v8
    v10: ptr = stack_slot 8 align 8
    v11: int:i64 = iconst 0
    v12: mem = store.8 v11, v10, v0
    v13: ptr = symbol_addr @memcpy
    v14: int:u64 = iconst 8
    v15: mem, v16: int:u64 = call v13(v10, v7, v14), v12 -> int:u64
    v17: mem = memmove v7:align8, v9:align8, v14, v15
    v18: ptr = symbol_addr @memcpy
    v19: mem, v20: int:u64 = call v18(v9, v10, v14), v17 -> int:u64
    ret v19
}
"#;
    let (output, stats) = optimize(input);
    assert!(
        !output.contains("memmove"),
        "dynamic swap chain should remove memmove:\n{output}"
    );
    assert!(
        !output.contains("symbol_addr @memcpy"),
        "dynamic swap chain should remove memcpy calls:\n{output}"
    );
    assert!(
        output.contains("load.8") && output.contains("store.8"),
        "dynamic swap chain should become scalar load/store ops:\n{output}"
    );
    assert_eq!(stats.per_rule["form_scalar_swap"], 1);
}

#[test]
fn forms_scalar_swap_with_single_base_dynamic_ptradd_operands() {
    let input = r#"
func @swap8_single_base(ptr, int:u64, int:u64) {
  bb0(v0: mem):
    v1: ptr = param 0
    v2: int:u64 = param 1
    v3: int:u64 = param 2
    v4: int:u1 = iconst 3
    v5: int:i64 = shl v2, v4
    v6: ptr = ptradd v1, v5
    v7: int:i64 = shl v3, v4
    v8: ptr = ptradd v1, v7
    v9: ptr = stack_slot 8 align 8
    v10: ptr = symbol_addr @.tmp_zero
    v11: int:i64 = load.8 v10, v0
    v12: mem = store.8 v11, v9, v0
    v13: ptr = symbol_addr @memcpy
    v14: int:u64 = iconst 8
    v15: mem, v16: int:u64 = call v13(v9, v6, v14), v12 -> int:u64
    v17: mem = memmove v6:align8, v8:align8, v14, v15
    v18: ptr = symbol_addr @memcpy
    v19: mem, v20: int:u64 = call v18(v8, v9, v14), v17 -> int:u64
    ret v19
}
data @.tmp_zero = "\0\0\0\0\0\0\0\0"
"#;
    let (output, stats) = optimize(input);
    assert!(
        !output.contains("memmove"),
        "single-base dynamic swap chain should remove memmove:\n{output}"
    );
    assert!(
        !output.contains("symbol_addr @memcpy"),
        "single-base dynamic swap chain should remove memcpy calls:\n{output}"
    );
    assert!(
        output.contains("load.8") && output.contains("store.8"),
        "single-base dynamic swap chain should become scalar load/store ops:\n{output}"
    );
    assert_eq!(stats.per_rule["form_scalar_swap"], 1);
}

#[test]
fn forms_scalar_swap_from_partition_like_chain() {
    let input = r#"
func @partition_like_swap(ptr, ptr) {
  bb0(v0: mem):
    v1: ptr = param 0
    v2: ptr = param 1
    v4: ptr = stack_slot 8 align 8
    v5: ptr = symbol_addr @.zero8
    v6: int:i64 = load.8 v5, v0
    v7: mem = store.8 v6, v4, v0
    v8: int:u4 = iconst 8
    v9: ptr = symbol_addr @memcpy
    v10: mem, v11: int:u64 = call v9(v4, v1:align8, v8), v7 -> int:u64
    v12: mem = memmove v1:align8, v2:align8, v8, v10
    v13: ptr = symbol_addr @memcpy
    v14: mem, v15: int:u64 = call v13(v2, v4, v8), v12 -> int:u64
    ret v14
}
data @.zero8 = "\0\0\0\0\0\0\0\0"
"#;
    let (output, stats) = optimize(input);
    assert!(
        !output.contains("memmove"),
        "partition-like swap chain should remove memmove:\n{output}"
    );
    assert!(
        !output.contains("symbol_addr @memcpy"),
        "partition-like swap chain should remove memcpy calls:\n{output}"
    );
    assert!(
        output.contains("load.8") && output.contains("store.8"),
        "partition-like swap chain should become scalar load/store ops:\n{output}"
    );
    assert_eq!(stats.per_rule["form_scalar_swap"], 1);
}

#[test]
fn forms_scalar_swap_from_partition_like_dynamic_chain() {
    let input = r#"
func @partition_like_dynamic_swap(ptr, int:u64, int:u64) {
  bb0(v0: mem):
    v1: ptr = param 0
    v2: int:u64 = param 1
    v3: int:u64 = param 2
    v4: int:u2 = iconst 3
    v5: int:i64 = shl v2, v4
    v6: ptr = ptradd v1, v5
    v7: int:i64 = shl v3, v4
    v8: ptr = ptradd v1, v7
    v9: ptr = stack_slot 8 align 8
    v10: ptr = symbol_addr @.zero8
    v11: int:i64 = load.8 v10, v0
    v12: mem = store.8 v11, v9, v0
    v13: int:u4 = iconst 8
    v14: ptr = symbol_addr @memcpy
    v15: mem, v16: int:u64 = call v14(v9, v6:align8, v13), v12 -> int:u64
    v17: mem = memmove v6:align8, v8:align8, v13, v15
    v18: ptr = symbol_addr @memcpy
    v19: mem, v20: int:u64 = call v18(v8, v9, v13), v17 -> int:u64
    ret v19
}
data @.zero8 = "\0\0\0\0\0\0\0\0"
"#;
    let (output, stats) = optimize(input);
    assert!(
        !output.contains("memmove"),
        "dynamic partition-like swap chain should remove memmove:\n{output}"
    );
    assert!(
        !output.contains("symbol_addr @memcpy"),
        "dynamic partition-like swap chain should remove memcpy calls:\n{output}"
    );
    assert!(
        output.contains("load.8") && output.contains("store.8"),
        "dynamic partition-like swap chain should become scalar load/store ops:\n{output}"
    );
    assert_eq!(stats.per_rule["form_scalar_swap"], 1);
}

#[test]
fn skips_promotion_when_call_has_cleanup_label() {
    let input = r#"
func @sink() {
  bb0(v0: mem):
    ret v0
}

func @cleanup_skip(int:s32) -> int:s32 {
  bb0(v0: mem):
    v1: ptr = stack_slot 4
    v2: int:s32 = param 0
    v3: mem = store.4 v2, v1, v0
    v4: ptr = symbol_addr @sink
    v5: mem = call v4(), v3
    v6: int:s32 = load.4 v1, v5
    ret v6, v5
  bb1(v7: mem):
    ret v2, v7
}
"#;
    let mut module = parse_module(input).unwrap_or_else(|e| panic!("parse error: {e}"));
    let func_idx = module
        .functions
        .iter()
        .position(|func| module.symbols.resolve(func.name) == "cleanup_skip")
        .expect("cleanup_skip function");
    let func = &mut module.functions[func_idx];
    for node in func.inst_pool.iter_mut() {
        if let Op::Call(_, _, _, cleanup_label) = &mut node.inst.op {
            *cleanup_label = Some(1);
        }
    }
    let stats = optimize_module(&mut module);
    let verify = verify_module(&module);
    assert!(verify.is_ok(), "optimized module should verify: {verify}");
    let output = format!("{module}");
    assert!(
        output.contains("stack_slot"),
        "cleanup calls should disable promotion:\n{output}"
    );
    assert_eq!(stats.promoted_slots, 0);
}

#[test]
fn simplifies_icmp_value_roots_without_branch_matching() {
    let input = r#"
func @icmp_value_root(bool) {
  bb0:
    v0: bool = param 0
    v1: int = iconst 1
    v2: int = iconst 0
    v3: int = select v0, v1, v2
    v4: int = iconst 1
    v5: bool = icmp.eq v3, v4
    v6: bool = bxor v5, v0
    unreachable
}
"#;
    let (output, stats) = optimize(input);
    let expected = r#"func @icmp_value_root(bool) {
  bb0:
    v0: bool = param 0
    v1: bool = bxor v0, v0
    unreachable
}"#;
    assert_eq!(normalize_ir(&output), normalize_ir(expected));
    assert_eq!(stats.per_rule["icmp_eq_select_bool_to_int_is_one"], 1);
}

#[test]
fn generalizes_mask_cleanup_to_best_u1_annotation() {
    let input = r#"
func @mask_i1(int:i1) {
  bb0:
    v0: int:i1 = param 0
    v1: int:u8 = iconst 255
    v2: int:i1 = and v0, v1
    v3: int:i1 = add v2, v0
    unreachable
}
"#;
    let (output, stats) = optimize(input);
    let expected = r#"func @mask_i1(int:i1) {
  bb0:
    v0: int:i1 = param 0
    v1: int:i1 = add v0, v0
    unreachable
}"#;
    assert_eq!(normalize_ir(&output), normalize_ir(expected));
    assert_eq!(stats.per_rule["and_best_int_annotation_u1_lowbit_one"], 1);
}

#[test]
fn does_not_rewrite_signed_one_bit_values() {
    let input = r#"
func @mask_s1(int:s1) {
  bb0:
    v0: int:s1 = param 0
    v1: int:u1 = iconst 1
    v2: int:s1 = and v0, v1
    v3: int:s1 = add v2, v0
    unreachable
}
"#;
    let (output, stats) = optimize(input);
    let expected = r#"func @mask_s1(int:s1) {
  bb0:
    v0: int:s1 = param 0
    v1: int:u1 = iconst 1
    v2: int:u1 = and v0, v1
    v3: int:s1 = add v2, v0
    unreachable
}"#;
    assert_eq!(normalize_ir(&output), normalize_ir(expected));
    assert_eq!(
        stats
            .per_rule
            .get("and_best_int_annotation_u1_lowbit_one")
            .copied()
            .unwrap_or(0),
        0
    );
}

#[test]
fn folds_integer_constant_chains() {
    let input = r#"
func @fold_integer_chain() {
  bb0:
    v0: int:s32 = iconst 2
    v1: int:s32 = iconst 3
    v2: int:s32 = add v0, v1
    v3: int:s32 = iconst 4
    v4: int:s32 = mul v2, v3
    unreachable
}
"#;
    let (output, stats) = optimize(input);
    let expected = r#"func @fold_integer_chain() {
  bb0:
    v0: int:u5 = iconst 20
    unreachable
}"#;
    assert_eq!(normalize_ir(&output), normalize_ir(expected));
    assert!(
        stats.rewrites >= 2,
        "integer chain should still fold through the generated rewrite stack:\n{output}"
    );
}

#[test]
fn folds_select_with_constant_condition() {
    let input = r#"
func @fold_select(int:s32) {
  bb0:
    v0: bool = bconst true
    v1: int:s32 = iconst 7
    v2: int:s32 = param 0
    v3: int:s32 = select v0, v1, v2
    unreachable
}
"#;
    let (output, stats) = optimize(input);
    let expected = r#"func @fold_select(int:s32) {
  bb0:
    v0: int:s32 = param 0
    v1: int:u3 = iconst 7
    unreachable
}"#;
    assert_eq!(normalize_ir(&output), normalize_ir(expected));
    assert_eq!(stats.per_rule["const_fold_select"], 1);
}

#[test]
fn folds_annotated_results() {
    let input = r#"
func @fold_annotated_add() {
  bb0:
    v0: int:u8 = iconst 255
    v1: int:u8 = iconst 2
    v2: int:u8 = add v0, v1
    unreachable
}
"#;
    let (output, stats) = optimize(input);
    let expected = r#"func @fold_annotated_add() {
  bb0:
    v0: int:u1 = iconst 1
    unreachable
}"#;
    assert_eq!(normalize_ir(&output), normalize_ir(expected));
    assert_eq!(stats.per_rule["const_fold_add"], 1);
}

#[test]
fn at_use_narrows_result_annotations() {
    let input = r#"
func @narrow_and_result(int:u64) {
  bb0(v0: mem):
    v1: int:u64 = param 0
    v2: int:u64 = iconst 255
    v3: int:u64 = and v1, v2
    ret v3, v0
}
"#;
    let (output, stats) = optimize(input);
    let expected = r#"func @narrow_and_result(int:u64) {
  bb0(v0: mem):
    v1: int:u64 = param 0
    v2: int:u8 = iconst 255
    v3: int:u8 = and v1, v2
    ret v3, v0
}"#;
    assert_eq!(normalize_ir(&output), normalize_ir(expected));
    assert_eq!(stats.per_rule["at_use_strengthen_result"], 2);
}

#[test]
fn folds_width_sensitive_bit_ops() {
    let input = r#"
func @fold_bit_ops() {
  bb0:
    v0: int:s32 = iconst 3
    v1: int:s32 = count_leading_zeros.8 v0
    v2: int:s32 = iconst 129
    v3: int:s32 = iconst 1
    v4: int:s32 = rotate_left.8 v2, v3
    v5: int:s32 = add v1, v4
    unreachable
}
"#;
    let (output, stats) = optimize(input);
    let expected = r#"func @fold_bit_ops() {
  bb0:
    v0: int:u4 = iconst 9
    unreachable
}"#;
    assert_eq!(normalize_ir(&output), normalize_ir(expected));
    assert_eq!(stats.per_rule["const_fold_count_leading_zeros"], 1);
    assert_eq!(stats.per_rule["const_fold_rotate_left"], 1);
    assert_eq!(stats.per_rule["const_fold_add"], 1);
}

#[test]
fn skips_poisoning_constant_folds() {
    let input = r#"
func @skip_div_zero() {
  bb0:
    v0: int:s32 = iconst 1
    v1: int:s32 = iconst 0
    v2: int:s32 = div v0, v1
    unreachable
}
"#;
    let (output, stats) = optimize(input);
    let expected = r#"func @skip_div_zero() {
  bb0:
    v0: int:u1 = iconst 1
    v1: int:u1 = iconst 0
    v2: int:s32 = div v0, v1
    unreachable
}"#;
    assert_eq!(normalize_ir(&output), normalize_ir(expected));
    assert_eq!(
        stats.per_rule.get("const_fold_div").copied().unwrap_or(0),
        0
    );
}

#[test]
fn rewrites_div_by_one_identity() {
    let input = r#"
func @div_by_one_identity(int:u64) -> int:u64 {
  bb0(v10: mem):
    v0: int:u64 = param 0
    v1: int:u64 = iconst 1
    v2: int:u64 = div v0, v1
    ret v2, v10
}
"#;
    let (output, stats) = optimize(input);
    assert!(
        !output.contains(" = div "),
        "division by one should be eliminated:\n{output}"
    );
    assert!(
        output.contains("ret v"),
        "optimized function should still return the parameter:\n{output}"
    );
    assert_eq!(stats.per_rule["div_by_one_identity"], 1);
}

#[test]
fn rewrites_rem_by_one_to_zero() {
    let input = r#"
func @rem_by_one_zero(int:u64) -> int:u64 {
  bb0(v10: mem):
    v0: int:u64 = param 0
    v1: int:u64 = iconst 1
    v2: int:u64 = rem v0, v1
    ret v2, v10
}
"#;
    let (output, stats) = optimize(input);
    assert!(
        !output.contains(" = rem "),
        "remainder by one should be eliminated:\n{output}"
    );
    assert!(
        output.contains("iconst 0"),
        "replacement should materialize zero:\n{output}"
    );
    assert_eq!(stats.per_rule["rem_by_one_zero"], 1);
}

#[test]
fn rewrites_nonnegative_power_of_two_div_to_shr() {
    let input = r#"
func @div_pow2_to_shr(int:u64) -> int:u64 {
  bb0(v10: mem):
    v0: int:u64 = param 0
    v1: int:u64 = iconst 8
    v2: int:u64 = div v0, v1
    ret v2, v10
}
"#;
    let (output, stats) = optimize(input);
    assert!(
        !output.contains(" = div "),
        "power-of-two division should be eliminated:\n{output}"
    );
    assert!(
        output.contains(" = shr "),
        "replacement should materialize a shift:\n{output}"
    );
    assert!(
        output.contains("iconst 3"),
        "replacement should materialize the shift amount:\n{output}"
    );
    assert_eq!(stats.per_rule["div_nonnegative_power_of_two_to_shr"], 1);
}

#[test]
fn rewrites_mul_power_of_two_to_shl_right() {
    let input = r#"
func @mul_pow2_to_shl_right(int:u64) -> int:u64 {
  bb0(v10: mem):
    v0: int:u64 = param 0
    v1: int:u4 = iconst 8
    v2: int:u64 = mul v0, v1
    ret v2, v10
}
"#;
    let (output, stats) = optimize(input);
    assert!(
        !output.contains(" = mul "),
        "power-of-two multiply should be eliminated:\n{output}"
    );
    assert!(
        output.contains(" = shl "),
        "replacement should materialize a shift:\n{output}"
    );
    assert!(
        output.contains("iconst 3"),
        "replacement should materialize the shift amount:\n{output}"
    );
    assert_eq!(stats.per_rule["mul_power_of_two_to_shl_right"], 1);
}

#[test]
fn rewrites_mul_power_of_two_to_shl_left() {
    let input = r#"
func @mul_pow2_to_shl_left(int:u64) -> int:u64 {
  bb0(v10: mem):
    v0: int:u64 = param 0
    v1: int:u4 = iconst 8
    v2: int:u64 = mul v1, v0
    ret v2, v10
}
"#;
    let (output, stats) = optimize(input);
    assert!(
        !output.contains(" = mul "),
        "power-of-two multiply should be eliminated:\n{output}"
    );
    assert!(
        output.contains(" = shl "),
        "replacement should materialize a shift:\n{output}"
    );
    assert!(
        output.contains("iconst 3"),
        "replacement should materialize the shift amount:\n{output}"
    );
    assert!(
        stats.rewrites > 0,
        "power-of-two multiply should be rewritten:\n{output}"
    );
}

#[test]
fn promotion_preserves_unreachable_block_link_order() {
    let input = r#"
func @promotion_unreachable_order() {
  bb0(v0: mem):
    v1: ptr = stack_slot 4
    v2: int:s32 = iconst 1
    v3: mem = store.4 v2, v1, v0
    v4: int:s32 = load.4 v1, v3
    ret v3

  bb1(v5: mem):
    br bb2(v5)

  bb2(v6: mem):
    ret v6

  bb3(v7: mem):
    ret v7
}
"#;
    let mut module = parse_module(input).unwrap_or_else(|e| panic!("parse error: {e}"));
    let func = &mut module.functions[0];
    let blocks = collect_block_refs(func);
    let unreachable = blocks[1];
    let then_block = blocks[2];
    let else_block = blocks[3];
    let mem_arg = func.block_arg_values(unreachable)[0];
    let branch_idx = func.block(unreachable).last_inst.unwrap();
    let cond_idx = func.insert_inst_before(
        branch_idx,
        Instruction {
            op: Op::BConst(true),
            ty: Type::Bool,
            secondary_ty: None,
            origin: Origin::synthetic(),
            result_annotation: None,
            secondary_result_annotation: None,
        },
    );
    func.inst_pool
        .get_mut(branch_idx)
        .expect("branch exists")
        .inst
        .op = Op::BrIf(
        ValueRef::inst_result(cond_idx).into(),
        then_block,
        vec![Operand::new(mem_arg)],
        else_block,
        vec![Operand::new(mem_arg)],
    );
    func.rebuild_use_lists();

    let stats = optimize_module(&mut module);
    let verify = verify_module(&module);
    assert!(verify.is_ok(), "optimized module should verify: {verify}");
    assert_eq!(stats.promoted_slots, 1);
}
