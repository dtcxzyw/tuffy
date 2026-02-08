//! rustc_codegen_tuffy: Rustc codegen backend using tuffy IR.
//!
//! This crate implements `CodegenBackend` from `rustc_codegen_ssa`,
//! translating rustc MIR into tuffy IR for optimization and code generation.
//!
//! Build with: `rustc -Z codegen-backend=path/to/librustc_codegen_tuffy.so`

#![feature(rustc_private)]
#![feature(box_patterns)]

extern crate rustc_driver;
extern crate rustc_codegen_ssa;
extern crate rustc_data_structures;
extern crate rustc_middle;
extern crate rustc_session;

mod mir_to_ir;

use std::any::Any;
use std::fs;

use rustc_codegen_ssa::traits::CodegenBackend;
use rustc_codegen_ssa::{CodegenResults, CompiledModule, CrateInfo, ModuleKind};
use rustc_data_structures::fx::FxIndexMap;
use rustc_middle::dep_graph::{WorkProduct, WorkProductId};
use rustc_middle::mir::mono::MonoItem;
use rustc_middle::ty::TyCtxt;
use rustc_session::config::OutputFilenames;
use rustc_session::Session;

pub struct TuffyCodegenBackend;

impl CodegenBackend for TuffyCodegenBackend {
    fn name(&self) -> &'static str {
        "tuffy"
    }

    fn codegen_crate<'tcx>(&self, tcx: TyCtxt<'tcx>) -> Box<dyn Any> {
        let cgus = tcx.collect_and_partition_mono_items(()).codegen_units;
        let mut modules = Vec::new();

        for cgu in cgus {
            let cgu_name = cgu.name().to_string();
            let mono_items = cgu.items_in_deterministic_order(tcx);

            let mut compiled_funcs: Vec<tuffy_codegen::emit::CompiledFunction> = Vec::new();

            for (mono_item, _item_data) in &mono_items {
                if let MonoItem::Fn(instance) = mono_item {
                    if let Some(result) = mir_to_ir::translate_function(tcx, *instance) {
                        if let Some(isel_result) =
                            tuffy_codegen::isel::isel(&result.func, &result.call_targets)
                        {
                            let enc =
                                tuffy_codegen::encode::encode_function(&isel_result.insts);
                            compiled_funcs.push(tuffy_codegen::emit::CompiledFunction {
                                name: isel_result.name,
                                code: enc.code,
                                relocations: enc.relocations,
                            });
                        }
                    }
                }
            }

            if !compiled_funcs.is_empty() {
                let object_data = tuffy_codegen::emit::emit_elf_multi(&compiled_funcs);
                let tmp = tcx.output_filenames(()).temp_path_for_cgu(
                    rustc_session::config::OutputType::Object,
                    &cgu_name,
                    tcx.sess.invocation_temp.as_deref(),
                );
                fs::write(&tmp, &object_data).expect("failed to write object file");

                modules.push(CompiledModule {
                    name: cgu_name,
                    kind: ModuleKind::Regular,
                    object: Some(tmp),
                    dwarf_object: None,
                    bytecode: None,
                    assembly: None,
                    llvm_ir: None,
                    links_from_incr_cache: vec![],
                });
            }
        }

        // Generate allocator shim if needed.
        let allocator_module = generate_allocator_module(tcx);

        Box::new(CodegenResults {
            modules,
            allocator_module,
            crate_info: CrateInfo::new(tcx, "none".to_string()),
        })
    }

    fn join_codegen(
        &self,
        ongoing_codegen: Box<dyn Any>,
        _sess: &Session,
        _outputs: &OutputFilenames,
    ) -> (CodegenResults, FxIndexMap<WorkProductId, WorkProduct>) {
        let codegen_results = *ongoing_codegen
            .downcast::<CodegenResults>()
            .expect("expected CodegenResults");
        (codegen_results, FxIndexMap::default())
    }

    // `link` uses the default implementation from CodegenBackend,
    // which delegates to ArArchiveBuilderBuilder.
}

/// Entry point called by rustc to create the backend.
#[unsafe(no_mangle)]
pub fn __rustc_codegen_backend() -> Box<dyn CodegenBackend> {
    Box::new(TuffyCodegenBackend)
}

/// Generate the allocator shim module if the crate needs one.
///
/// The allocator shim provides `__rust_alloc` etc. that forward to the
/// default allocator (`__rdl_alloc` etc.). This is required for binary
/// crates that use the standard library.
fn generate_allocator_module(tcx: TyCtxt<'_>) -> Option<CompiledModule> {
    // Only generate allocator shim for binary crates.
    let dominated_by_std = tcx
        .crates(())
        .iter()
        .any(|&cnum| tcx.crate_name(cnum).as_str() == "std");
    if !dominated_by_std {
        return None;
    }

    // Generate forwarding stubs: each __rust_alloc* calls __rdl_alloc*.
    // These are simple jmp instructions (tail calls).
    let alloc_pairs = [
        ("__rust_alloc", "__rdl_alloc"),
        ("__rust_dealloc", "__rdl_dealloc"),
        ("__rust_realloc", "__rdl_realloc"),
        ("__rust_alloc_zeroed", "__rdl_alloc_zeroed"),
        ("__rust_alloc_error_handler", "__rdl_oom"),
    ];

    let mut funcs = Vec::new();
    for (export_name, target_name) in &alloc_pairs {
        // Emit a JMP rel32 to the target (will be resolved by linker).
        let code = vec![0xe9, 0x00, 0x00, 0x00, 0x00]; // jmp rel32
        let relocations = vec![tuffy_codegen::encode::Relocation {
            offset: 1,
            symbol: target_name.to_string(),
        }];
        funcs.push(tuffy_codegen::emit::CompiledFunction {
            name: export_name.to_string(),
            code,
            relocations,
        });
    }

    let object_data = tuffy_codegen::emit::emit_elf_multi(&funcs);
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
