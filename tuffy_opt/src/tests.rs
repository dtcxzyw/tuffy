use tuffy_ir::instruction::Op;
use tuffy_ir::parser::parse_module;
use tuffy_ir::verifier::verify_module;

use crate::{generated_rule_count, optimize_module};

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
    assert_eq!(generated_rule_count(), 33);
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
    v0: bool = bconst true
    brif v0, bb1, bb2
  bb1:
    trap
  bb2:
    trap
}"#;
    assert_eq!(normalize_ir(&output), normalize_ir(expected));
    assert_eq!(stats.per_rule["icmp_eq_select_bool_to_int_is_one"], 1);
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
    v0: bool = bconst true
    brif v0, bb1, bb2
  bb1:
    trap
  bb2:
    trap
}"#;
    assert_eq!(normalize_ir(&output), normalize_ir(expected));
    assert_eq!(stats.per_rule["icmp_eq_select_bool_to_int_is_zero"], 1);
    assert_eq!(stats.per_rule["const_fold_bxor"], 1);
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
    v0: bool = bconst false
    brif v0, bb1, bb2
  bb1:
    trap
  bb2:
    trap
}"#;
    assert_eq!(normalize_ir(&output), normalize_ir(expected));
    assert_eq!(stats.per_rule["and_best_int_annotation_u1_lowbit_one"], 1);
    assert_eq!(stats.per_rule["icmp_eq_select_bool_to_int_is_zero"], 1);
    assert_eq!(stats.per_rule["const_fold_bxor"], 1);
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
    v1: int:s32 = iconst 1
    v2: int:s32 = iconst 0
    v3: int:s32 = select v0, v1, v2
    v4: int:s32 = add v3, v1
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
    assert_eq!(normalize_ir(&output), normalize_ir(input));
    assert_eq!(stats.rewrites, 0);
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
    v0: bool = bconst false
    brif v0, bb1, bb2
  bb1:
    trap
  bb2:
    trap
}"#;
    assert_eq!(normalize_ir(&output), normalize_ir(expected));
    assert_eq!(
        stats.per_rule["icmp_eq_xor_select_bool_to_int_is_one_is_one"],
        1
    );
    assert_eq!(stats.per_rule["const_fold_bxor"], 1);
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
    v1: int:s32 = iconst 1
    v2: int:s32 = iconst 0
    v3: int:s32 = select v0, v1, v2
    v4: int:s32 = add v3, v1
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
    ret v8, v7
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
fn does_not_promote_slot_passed_to_call() {
    let input = r#"
func @sink(ptr) {
  bb0(v0: mem):
    ret v0
}

func @call_escape(int:s32) -> int:s32 {
  bb0(v0: mem):
    v1: ptr = stack_slot 4
    v2: int:s32 = param 0
    v3: mem = store.4 v2, v1, v0
    v4: ptr = symbol_addr @sink
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
fn still_promotes_local_slot_around_unrelated_call() {
    let input = r#"
func @sink(int:s32) {
  bb0(v0: mem):
    ret v0
}

func @call_unrelated(int:s32) -> int:s32 {
  bb0(v0: mem):
    v1: ptr = stack_slot 4
    v2: int:s32 = param 0
    v3: mem = store.4 v2, v1, v0
    v4: ptr = symbol_addr @sink
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
    assert_eq!(normalize_ir(&output), normalize_ir(input));
    assert_eq!(stats.rewrites, 0);
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
    v0: int:s32 = iconst 20
    unreachable
}"#;
    assert_eq!(normalize_ir(&output), normalize_ir(expected));
    assert_eq!(stats.per_rule["const_fold_add"], 1);
    assert_eq!(stats.per_rule["const_fold_mul"], 1);
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
    v1: int:s32 = iconst 7
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
    v0: int:u8 = iconst 1
    unreachable
}"#;
    assert_eq!(normalize_ir(&output), normalize_ir(expected));
    assert_eq!(stats.per_rule["const_fold_add"], 1);
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
    v0: int:s32 = iconst 9
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
    assert_eq!(normalize_ir(&output), normalize_ir(input));
    assert_eq!(stats.rewrites, 0);
}
