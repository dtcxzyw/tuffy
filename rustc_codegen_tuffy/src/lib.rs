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

            let mut object_data: Vec<u8> = Vec::new();
            let mut has_functions = false;

            for (mono_item, _item_data) in &mono_items {
                if let MonoItem::Fn(instance) = mono_item {
                    if let Some(result) = mir_to_ir::translate_function(tcx, *instance) {
                        if let Some(isel_result) = tuffy_codegen::isel::isel(&result.func, &result.call_targets) {
                            let enc =
                                tuffy_codegen::encode::encode_function(&isel_result.insts);
                            object_data = tuffy_codegen::emit::emit_elf(
                                &isel_result.name,
                                &enc.code,
                                &enc.relocations,
                            );
                            has_functions = true;
                        }
                    }
                }
            }

            if has_functions {
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

        Box::new(CodegenResults {
            modules,
            allocator_module: None,
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
