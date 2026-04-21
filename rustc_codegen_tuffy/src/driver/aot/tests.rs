use rustc_hir::attrs::Linkage;

use super::batch::{is_local_linkage, is_weak_linkage, optimize_ir_batch, verify_ir_batch};
use super::{IrModuleBatch, format_post_opt_module_dump, merge_translation_result};
use crate::mir_to_ir::TranslationResult;
use tuffy_ir::instruction::Op;
use tuffy_ir::parser::parse_module;

fn parse_result(input: &str) -> TranslationResult<'static> {
    let mut module = parse_module(input).unwrap_or_else(|e| panic!("parse error: {e}"));
    let func = module
        .functions
        .pop()
        .expect("module should contain one function");
    TranslationResult {
        func,
        symbols: module.symbols,
        static_data: vec![],
        referenced_instances: vec![],
        weak_undefined_symbols: Default::default(),
    }
}

fn merge_results(results: Vec<TranslationResult<'static>>) -> IrModuleBatch {
    let mut batch = IrModuleBatch::new("test");
    for result in results {
        merge_translation_result(&mut batch, result, false, false);
    }
    batch
}

#[test]
fn optimize_ir_batch_runs_module_tuffy_opt_when_enabled() {
    let callee = parse_result(
        r#"
func @id(int:s32) -> int:s32 {
  bb0(v0: mem):
v1: int:s32 = param 0
ret v1, v0
}
"#,
    );
    let caller = parse_result(
        r#"
func @caller(int:s32) -> int:s32 {
  bb0(v0: mem):
v1: int:s32 = param 0
v2: ptr = symbol_addr @id
v3: mem, v4: int:s32 = call v2(v1), v0 -> int:s32
ret v4, v3
}
"#,
    );

    let mut batch = merge_results(vec![callee, caller]);
    let stats = optimize_ir_batch(&mut batch, true)
        .expect("optimization should verify")
        .expect("optimization should run");
    assert_eq!(stats.inlined_calls, 1);
    let printed = format!("{}", batch.module);
    assert!(
        !printed.contains(" = call "),
        "expected inlining:\n{printed}"
    );
}

#[test]
fn optimize_ir_batch_skips_when_disabled() {
    let callee = parse_result(
        r#"
func @id(int:s32) -> int:s32 {
  bb0(v0: mem):
v1: int:s32 = param 0
ret v1, v0
}
"#,
    );
    let caller = parse_result(
        r#"
func @caller(int:s32) -> int:s32 {
  bb0(v0: mem):
v1: int:s32 = param 0
v2: ptr = symbol_addr @id
v3: mem, v4: int:s32 = call v2(v1), v0 -> int:s32
ret v4, v3
}
"#,
    );

    let mut batch = merge_results(vec![callee, caller]);
    let stats = optimize_ir_batch(&mut batch, false).expect("skip should succeed");
    assert!(stats.is_none(), "optimization should be skipped");
    let printed = format!("{}", batch.module);
    assert!(
        printed.contains(" = call "),
        "call should remain:\n{printed}"
    );
}

#[test]
fn merge_translation_result_remaps_symbols_and_static_data() {
    let mut result = parse_result(
        r#"
func @caller() {
  bb0(v0: mem):
v1: ptr = symbol_addr @callee
ret v0
}
"#,
    );
    let blob = result.symbols.intern("blob");
    result
        .static_data
        .push((blob, vec![1, 2, 3, 4], vec![(0, "callee".to_string())], 8));
    result
        .weak_undefined_symbols
        .insert("extern_weak_sym".to_string());

    let mut batch = IrModuleBatch::new("merged");
    merge_translation_result(&mut batch, result, true, false);

    assert!(verify_ir_batch(&batch, "merged batch should verify").is_ok());
    assert_eq!(
        batch.module.resolve(batch.module.functions[0].name),
        "caller"
    );
    let call_target = batch.module.functions[0]
        .inst_pool
        .iter_insts()
        .find_map(|(_, inst)| match &inst.op {
            Op::SymbolAddr(symbol) => Some(*symbol),
            _ => None,
        })
        .expect("caller should contain a symbol_addr");
    assert_eq!(batch.module.resolve(call_target), "callee");
    assert_eq!(
        batch.module.resolve(batch.module.static_data[0].name),
        "blob"
    );
    assert_eq!(
        batch
            .module
            .resolve(batch.module.static_data[0].relocations[0].symbol),
        "callee"
    );
    assert_eq!(batch.target_static_data[0].name, "blob");
    assert_eq!(batch.target_static_data[0].align, 8);
    assert!(batch.weak_undefined_symbols.contains("extern_weak_sym"));
    assert!(batch.function_meta[0].weak);
    assert!(!batch.function_meta[0].local);
}

#[test]
fn format_post_opt_module_dump_includes_module_display() {
    let batch = merge_results(vec![parse_result(
        r#"
func @only() {
  bb0(v0: mem):
ret v0
}
"#,
    )]);
    let dump = format_post_opt_module_dump(&batch.module);
    assert!(dump.contains("; post-opt module test"));
    assert!(dump.contains("func @only()"));
}

#[test]
fn internal_linkage_is_not_treated_as_weak() {
    assert!(!is_weak_linkage(Linkage::Internal));
    assert!(is_weak_linkage(Linkage::WeakAny));
    assert!(is_weak_linkage(Linkage::WeakODR));
}

#[test]
fn internal_linkage_is_treated_as_local() {
    assert!(is_local_linkage(Linkage::Internal));
    assert!(!is_local_linkage(Linkage::External));
    assert!(!is_local_linkage(Linkage::WeakODR));
}
