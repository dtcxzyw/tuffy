use std::fs;

use rustc_codegen_ssa::{CompiledModule, ModuleKind};
use rustc_middle::ty::TyCtxt;
use tuffy_codegen::CodegenSession;

/// Generate the allocator shim module if the crate needs one.
///
/// The allocator shim provides `__rust_alloc` etc. that forward to the
/// default allocator (`__rdl_alloc` etc.). This is required for binary
/// crates that use the standard library.
pub(crate) fn generate_allocator_module(
    tcx: TyCtxt<'_>,
    session: &CodegenSession,
) -> Option<CompiledModule> {
    let dominated_by_std = tcx
        .crates(())
        .iter()
        .any(|&cnum| tcx.crate_name(cnum).as_str() == "std");
    if !dominated_by_std {
        return None;
    }

    let mangle =
        |name: &str| -> String { rustc_symbol_mangling::mangle_internal_symbol(tcx, name) };

    let alloc_pairs_raw = [
        ("__rust_alloc", "__rdl_alloc"),
        ("__rust_dealloc", "__rdl_dealloc"),
        ("__rust_realloc", "__rdl_realloc"),
        ("__rust_alloc_zeroed", "__rdl_alloc_zeroed"),
    ];

    let mangled_pairs: Vec<(String, String)> = alloc_pairs_raw
        .iter()
        .map(|(exported, target)| (mangle(exported), mangle(target)))
        .collect();
    let pairs_ref: Vec<(&str, &str)> = mangled_pairs
        .iter()
        .map(|(exported, target)| (exported.as_str(), target.as_str()))
        .collect();

    let shim_marker = mangle("__rust_no_alloc_shim_is_unstable_v2");
    let mut funcs = session.generate_allocator_stubs(&pairs_ref, &shim_marker);
    for func in &mut funcs {
        func.weak = true;
    }

    let object_data = session.emit_object(&funcs, &[]);
    let tmp = tcx.output_filenames(()).temp_path_for_cgu(
        rustc_session::config::OutputType::Object,
        "allocator_shim",
        tcx.sess.invocation_temp.as_deref(),
    );
    fs::write(&tmp, &object_data).expect("failed to write allocator shim");

    Some(CompiledModule {
        name: "allocator_shim".to_string(),
        kind: ModuleKind::Allocator,
        object: Some(tmp),
        dwarf_object: None,
        bytecode: None,
        assembly: None,
        llvm_ir: None,
        links_from_incr_cache: vec![],
    })
}
