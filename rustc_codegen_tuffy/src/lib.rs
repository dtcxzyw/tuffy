//! rustc_codegen_tuffy: Rustc codegen backend using tuffy IR.
//!
//! This crate implements `CodegenBackend` from `rustc_codegen_ssa`,
//! translating rustc MIR into tuffy IR for optimization and code generation.
//!
//! Build with: `rustc -Z codegen-backend=path/to/librustc_codegen_tuffy.so`

#![feature(rustc_private)]
#![feature(box_patterns)]

extern crate rustc_abi;
extern crate rustc_codegen_ssa;
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_middle;
extern crate rustc_session;
extern crate rustc_span;
extern crate rustc_symbol_mangling;

mod mir_to_ir;

use std::any::Any;
use std::fs;

use rustc_codegen_ssa::traits::CodegenBackend;
use rustc_codegen_ssa::{CodegenResults, CompiledModule, CrateInfo, ModuleKind, TargetConfig};
use rustc_data_structures::fx::FxIndexMap;
use rustc_middle::dep_graph::{WorkProduct, WorkProductId};
use rustc_middle::mir::mono::MonoItem;
use rustc_middle::ty::TyCtxt;
use rustc_session::Session;
use rustc_session::config::OutputFilenames;
use rustc_span::Symbol;
use tuffy_codegen::CodegenSession;
use tuffy_target::types::{CompiledFunction, StaticData};

pub struct TuffyCodegenBackend;

impl CodegenBackend for TuffyCodegenBackend {
    fn name(&self) -> &'static str {
        "tuffy"
    }

    fn target_config(&self, sess: &Session) -> TargetConfig {
        // Report baseline target features for the current target.
        // For x86-64-v1: x87, sse, sse2, fxsr are mandatory.
        let features: Vec<Symbol> = sess
            .target
            .rust_target_features()
            .iter()
            .filter(|(feature, _, _)| matches!(*feature, "x87" | "sse" | "sse2" | "fxsr"))
            .flat_map(|(feature, _, _)| {
                sess.target
                    .implied_target_features(feature)
                    .into_iter()
                    .map(Symbol::intern)
            })
            .collect();

        TargetConfig {
            target_features: features.clone(),
            unstable_target_features: features,
            has_reliable_f16: false,
            has_reliable_f16_math: false,
            has_reliable_f128: false,
            has_reliable_f128_math: false,
        }
    }

    fn codegen_crate<'tcx>(&self, tcx: TyCtxt<'tcx>) -> Box<dyn Any> {
        let target_triple = tcx.sess.target.llvm_target.as_ref();
        let session = CodegenSession::new(target_triple);
        let dump_ir = tcx.sess.opts.cg.llvm_args.iter().any(|a| a == "dump-ir");
        let cgus = tcx.collect_and_partition_mono_items(()).codegen_units;
        let mut modules = Vec::new();

        for cgu in cgus {
            let cgu_name = cgu.name().to_string();
            let mono_items = cgu.items_in_deterministic_order(tcx);

            let mut compiled_funcs: Vec<CompiledFunction> = Vec::new();
            let mut all_static_data: Vec<StaticData> = Vec::new();

            for (mono_item, item_data) in &mono_items {
                if let MonoItem::Fn(instance) = mono_item {
                    // Skip lang_start — tuffy can't compile the trait object
                    // construction it requires. We emit a hand-crafted version
                    // in generate_entry_point instead.
                    if Some(instance.def_id()) == tcx.lang_items().start_fn() {
                        continue;
                    }
                    let result_opt = mir_to_ir::translate_function(tcx, *instance, &session);
                    if result_opt.is_none() {
                        let name = tcx.symbol_name(*instance);
                        eprintln!("[tuffy] MIR translation failed for: {name}");
                    }
                    if let Some(result) = result_opt {
                        if dump_ir {
                            for (sym_id, data, _relocs) in &result.static_data {
                                let name = result.symbols.resolve(*sym_id);
                                eprintln!(
                                    "{}",
                                    tuffy_ir::display::StaticDataDisplay { name, data }
                                );
                            }
                            eprintln!("{}", result.func.display(&result.symbols));
                        }

                        let vr = tuffy_ir::verifier::verify_function(&result.func, &result.symbols);
                        if !vr.is_ok() {
                            let func_name = result.symbols.resolve(result.func.name);
                            panic!("IR verification failed for {func_name}:\n{vr}");
                        }

                        for (sym_id, data, relocs) in &result.static_data {
                            all_static_data.push(StaticData {
                                name: result.symbols.resolve(*sym_id).to_string(),
                                data: data.clone(),
                                relocations: relocs.iter().map(|(offset, sym)| {
                                    tuffy_target::reloc::Relocation {
                                        offset: *offset,
                                        symbol: sym.clone(),
                                        kind: tuffy_target::reloc::RelocKind::Abs64,
                                    }
                                }).collect(),
                            });
                        }

                        if let Some(mut cf) = session.compile_function(
                            &result.func,
                            &result.symbols,
                            &result.abi_metadata,
                        ) {
                            use rustc_hir::attrs::Linkage;
                            cf.weak = matches!(
                                item_data.linkage,
                                Linkage::Internal
                                    | Linkage::LinkOnceODR
                                    | Linkage::WeakODR
                                    | Linkage::LinkOnceAny
                                    | Linkage::WeakAny
                            );
                            compiled_funcs.push(cf);
                        }
                    }
                }
            }

            if !compiled_funcs.is_empty() {
                let object_data = session.emit_object(&compiled_funcs, &all_static_data);
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
        let allocator_module = generate_allocator_module(tcx, &session);

        // Generate C `main` entry point if this is a binary crate.
        if let Some(entry_module) = generate_entry_point(tcx, &session) {
            modules.push(entry_module);
        }

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
fn generate_allocator_module(tcx: TyCtxt<'_>, session: &CodegenSession) -> Option<CompiledModule> {
    // Only generate allocator shim for binary crates.
    let dominated_by_std = tcx
        .crates(())
        .iter()
        .any(|&cnum| tcx.crate_name(cnum).as_str() == "std");
    if !dominated_by_std {
        return None;
    }

    // Use rustc's symbol mangling to get correct v0-mangled names.
    let mangle =
        |name: &str| -> String { rustc_symbol_mangling::mangle_internal_symbol(tcx, name) };

    // Generate forwarding stubs: each __rust_alloc* calls __rdl_alloc*.
    let alloc_pairs_raw = [
        ("__rust_alloc", "__rdl_alloc"),
        ("__rust_dealloc", "__rdl_dealloc"),
        ("__rust_realloc", "__rdl_realloc"),
        ("__rust_alloc_zeroed", "__rdl_alloc_zeroed"),
    ];

    let mangled_pairs: Vec<(String, String)> = alloc_pairs_raw
        .iter()
        .map(|(e, t)| (mangle(e), mangle(t)))
        .collect();
    let pairs_ref: Vec<(&str, &str)> = mangled_pairs
        .iter()
        .map(|(e, t)| (e.as_str(), t.as_str()))
        .collect();

    let shim_marker = mangle("__rust_no_alloc_shim_is_unstable_v2");
    let funcs = session.generate_allocator_stubs(&pairs_ref, &shim_marker);

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

/// Generate the C `main` entry point and a hand-crafted `lang_start`.
///
/// The C runtime calls `main(argc, argv)`. This wrapper forwards to
/// `std::rt::lang_start(rust_main, argc, argv, sigpipe=0)`.
///
/// We also emit a hand-crafted `lang_start` because tuffy cannot yet
/// compile the real `lang_start` (it constructs a `&dyn Fn() -> i32`
/// trait object, which requires vtable support). Our simplified version
/// calls the user's main directly and returns 0.
fn generate_entry_point(tcx: TyCtxt<'_>, session: &CodegenSession) -> Option<CompiledModule> {
    use rustc_middle::ty::{self, Instance};

    let (entry_def_id, _) = tcx.entry_fn(())?;

    // Resolve the user's main function symbol.
    let main_instance = Instance::mono(tcx, entry_def_id);
    let main_sym = tcx.symbol_name(main_instance).name.to_string();

    // Resolve the lang_start function symbol.
    let start_def_id = tcx.lang_items().start_fn()?;
    let main_ret_ty = tcx
        .fn_sig(entry_def_id)
        .instantiate_identity()
        .output()
        .skip_binder();
    let start_instance = Instance::try_resolve(
        tcx,
        ty::TypingEnv::fully_monomorphized(),
        start_def_id,
        tcx.mk_args(&[main_ret_ty.into()]),
    )
    .ok()
    .flatten()?;
    let start_sym = tcx.symbol_name(start_instance).name.to_string();

    let funcs = session.generate_entry_point(&main_sym, &start_sym);
    let object_data = session.emit_object(&funcs, &[]);

    let tmp = tcx.output_filenames(()).temp_path_for_cgu(
        rustc_session::config::OutputType::Object,
        "entry_point",
        tcx.sess.invocation_temp.as_deref(),
    );
    fs::write(&tmp, &object_data).expect("failed to write entry point");

    Some(CompiledModule {
        name: "entry_point".to_string(),
        kind: ModuleKind::Regular,
        object: Some(tmp),
        dwarf_object: None,
        bytecode: None,
        assembly: None,
        llvm_ir: None,
        links_from_incr_cache: vec![],
    })
}
