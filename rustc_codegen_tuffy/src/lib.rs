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
extern crate rustc_symbol_mangling;

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

        // Generate C `main` entry point if this is a binary crate.
        if let Some(entry_module) = generate_entry_point(tcx) {
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
fn generate_allocator_module(tcx: TyCtxt<'_>) -> Option<CompiledModule> {
    // Only generate allocator shim for binary crates.
    let dominated_by_std = tcx
        .crates(())
        .iter()
        .any(|&cnum| tcx.crate_name(cnum).as_str() == "std");
    if !dominated_by_std {
        return None;
    }

    // Use rustc's symbol mangling to get correct v0-mangled names.
    let mangle = |name: &str| -> String {
        rustc_symbol_mangling::mangle_internal_symbol(tcx, name)
    };

    // Generate forwarding stubs: each __rust_alloc* calls __rdl_alloc*.
    let alloc_pairs = [
        ("__rust_alloc", "__rdl_alloc"),
        ("__rust_dealloc", "__rdl_dealloc"),
        ("__rust_realloc", "__rdl_realloc"),
        ("__rust_alloc_zeroed", "__rdl_alloc_zeroed"),
    ];

    let mut funcs = Vec::new();
    for (export_name, target_name) in &alloc_pairs {
        let mangled_export = mangle(export_name);
        let mangled_target = mangle(target_name);
        // Emit a JMP rel32 to the target (will be resolved by linker).
        let code = vec![0xe9, 0x00, 0x00, 0x00, 0x00]; // jmp rel32
        let relocations = vec![tuffy_codegen::encode::Relocation {
            offset: 1,
            symbol: mangled_target,
        }];
        funcs.push(tuffy_codegen::emit::CompiledFunction {
            name: mangled_export,
            code,
            relocations,
        });
    }

    // Add the no_alloc_shim marker symbol (a single zero byte).
    let shim_marker = mangle("__rust_no_alloc_shim_is_unstable_v2");
    funcs.push(tuffy_codegen::emit::CompiledFunction {
        name: shim_marker,
        code: vec![0x00],
        relocations: vec![],
    });

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

/// Generate the C `main` entry point that calls `lang_start`.
///
/// The C runtime calls `main(argc, argv)`. This wrapper forwards to
/// `std::rt::lang_start(rust_main, argc, argv, sigpipe=0)`.
fn generate_entry_point(tcx: TyCtxt<'_>) -> Option<CompiledModule> {
    use rustc_middle::ty::{self, Instance};

    let (entry_def_id, _) = tcx.entry_fn(())?;

    // Resolve the user's main function symbol.
    let main_instance = Instance::mono(tcx, entry_def_id);
    let main_sym = tcx.symbol_name(main_instance).name.to_string();

    // Resolve the lang_start function symbol.
    let start_def_id = tcx.lang_items().start_fn()?;
    let main_ret_ty = tcx.fn_sig(entry_def_id)
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

    // Generate x86-64 machine code for a minimal entry point:
    //   main(argc: i32 [edi], argv: **u8 [rsi]) -> i32
    //     call rust_main        ; call user's main directly
    //     xor eax, eax          ; return 0
    //     ret
    //
    // This bypasses lang_start/lang_start_internal for now.
    // Full std runtime init will be added later.
    let code = vec![
        0xe8, 0x00, 0x00, 0x00, 0x00, // call rust_main
        0x31, 0xc0, // xor eax, eax
        0xc3, // ret
    ];

    let relocations = vec![
        tuffy_codegen::encode::Relocation {
            offset: 1,
            symbol: main_sym,
        },
    ];

    let funcs = vec![tuffy_codegen::emit::CompiledFunction {
        name: "main".to_string(),
        code,
        relocations,
    }];

    let object_data = tuffy_codegen::emit::emit_elf_multi(&funcs);
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
