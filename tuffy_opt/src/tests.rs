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
    assert_eq!(stats.per_rule["brif_icmp_eq_select_bool_to_int_is_one"], 1);
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
    v0: bool = bconst false
    brif v0, bb2, bb1
  bb1:
    trap
  bb2:
    trap
}"#;
    assert_eq!(normalize_ir(&output), normalize_ir(expected));
    assert_eq!(stats.per_rule["brif_icmp_eq_select_bool_to_int_is_zero"], 1);
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
    v0: bool = bconst true
    brif v0, bb2, bb1
  bb1:
    trap
  bb2:
    trap
}"#;
    assert_eq!(normalize_ir(&output), normalize_ir(expected));
    assert_eq!(stats.per_rule["and_select_bool_to_int_odd_mask"], 1);
    assert_eq!(stats.per_rule["brif_icmp_eq_select_bool_to_int_is_zero"], 1);
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
    assert_eq!(stats.per_rule["and_select_bool_to_int_odd_mask"], 1);
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
    v0: bool = bconst true
    brif v0, bb2, bb1
  bb1:
    trap
  bb2:
    trap
}"#;
    assert_eq!(normalize_ir(&output), normalize_ir(expected));
    assert_eq!(
        stats.per_rule["brif_icmp_eq_xor_select_bool_to_int_is_one_is_one"],
        1
    );
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
    assert_eq!(stats.per_rule["and_select_bool_to_int_odd_mask"], 1);
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
