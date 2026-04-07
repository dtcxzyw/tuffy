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
    assert_eq!(generated_rule_count(), 4);
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
    assert_eq!(stats.per_rule["brif_icmp_eq_select_bool_to_int_one"], 1);
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
    assert_eq!(stats.per_rule["brif_icmp_eq_select_bool_to_int_zero"], 1);
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
    assert_eq!(stats.per_rule["and_select_bool_to_int_mask_255"], 1);
    assert_eq!(stats.per_rule["brif_icmp_eq_select_bool_to_int_zero"], 1);
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
        stats.per_rule["brif_icmp_eq_xor_select_bool_to_int_one_one"],
        1
    );
}

#[test]
fn keeps_shared_select_alive_when_only_mask_is_removed() {
    let input = r#"
func @mask_value() {
  bb0:
    v0: bool = bconst true
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
    let expected = r#"func @mask_value() {
  bb0:
    v0: bool = bconst true
    v1: int:s32 = iconst 1
    v2: int:s32 = iconst 0
    v3: int:s32 = select v0, v1, v2
    v4: int:s32 = add v3, v1
    unreachable
}"#;
    assert_eq!(normalize_ir(&output), normalize_ir(expected));
    assert_eq!(stats.per_rule["and_select_bool_to_int_mask_255"], 1);
}
