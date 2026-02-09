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

            let mut compiled_funcs: Vec<tuffy_target_x86::emit::CompiledFunction> = Vec::new();

            let mut all_static_data: Vec<tuffy_target_x86::emit::StaticData> = Vec::new();

            for (mono_item, _item_data) in &mono_items {
                if let MonoItem::Fn(instance) = mono_item {
                    // Skip lang_start — tuffy can't compile the trait object
                    // construction it requires. We emit a hand-crafted version
                    // in generate_entry_point instead.
                    if Some(instance.def_id()) == tcx.lang_items().start_fn() {
                        continue;
                    }
                    if let Some(result) = mir_to_ir::translate_function(tcx, *instance) {
                        // Collect static data from this function.
                        for (sym, data) in &result.static_data {
                            all_static_data.push(tuffy_target_x86::emit::StaticData {
                                name: sym.clone(),
                                data: data.clone(),
                            });
                        }

                        if let Some(isel_result) = tuffy_target_x86::isel::isel(
                            &result.func,
                            &result.call_targets,
                            &result.static_refs,
                            &result.rdx_captures,
                            &result.rdx_moves,
                        ) {
                            let enc =
                                tuffy_target_x86::encode::encode_function(&isel_result.insts);
                            compiled_funcs.push(tuffy_target_x86::emit::CompiledFunction {
                                name: isel_result.name,
                                code: enc.code,
                                relocations: enc.relocations,
                            });
                        }
                    }
                }
            }

            if !compiled_funcs.is_empty() {
                let object_data = tuffy_target_x86::emit::emit_elf_with_data(
                    &compiled_funcs,
                    &all_static_data,
                );
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
        let relocations = vec![tuffy_target::reloc::Relocation {
            offset: 1,
            symbol: mangled_target,
            kind: tuffy_target::reloc::RelocKind::Call,
        }];
        funcs.push(tuffy_target_x86::emit::CompiledFunction {
            name: mangled_export,
            code,
            relocations,
        });
    }

    // Add the no_alloc_shim marker symbol as a trivial function (just `ret`).
    // The allocator calls this to verify the shim is linked.
    let shim_marker = mangle("__rust_no_alloc_shim_is_unstable_v2");
    funcs.push(tuffy_target_x86::emit::CompiledFunction {
        name: shim_marker,
        code: vec![0xc3], // ret
        relocations: vec![],
    });

    let object_data = tuffy_target_x86::emit::emit_elf_multi(&funcs);

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

    // --- C `main` entry point ---
    //
    //   main(argc: i32 [edi], argv: **u8 [rsi]) -> i64
    //     push   rbp                ; align stack to 16 bytes
    //     movsxd rax, edi           ; sign-extend argc (i32 -> i64)
    //     mov    rdx, rsi           ; argv -> 3rd arg
    //     mov    rsi, rax           ; argc -> 2nd arg
    //     lea    rdi, [rip+disp32]  ; user main fn ptr -> 1st arg (PcRel reloc)
    //     xor    ecx, ecx           ; sigpipe=0 -> 4th arg
    //     call   lang_start         ; call reloc
    //     pop    rbp                ; restore stack
    //     ret
    let main_code = vec![
        0x55,                                       // push rbp
        0x48, 0x63, 0xc7,                           // movsxd rax, edi
        0x48, 0x89, 0xf2,                           // mov rdx, rsi
        0x48, 0x89, 0xc6,                           // mov rsi, rax
        0x48, 0x8d, 0x3d, 0x00, 0x00, 0x00, 0x00,  // lea rdi, [rip+0]
        0x31, 0xc9,                                 // xor ecx, ecx
        0xe8, 0x00, 0x00, 0x00, 0x00,               // call lang_start
        0x5d,                                       // pop rbp
        0xc3,                                       // ret
    ];
    let main_relocs = vec![
        tuffy_target::reloc::Relocation {
            offset: 13,
            symbol: main_sym,
            kind: tuffy_target::reloc::RelocKind::PcRel,
        },
        tuffy_target::reloc::Relocation {
            offset: 20,
            symbol: start_sym.clone(),
            kind: tuffy_target::reloc::RelocKind::Call,
        },
    ];

    // --- Hand-crafted `lang_start` ---
    //
    // Simplified version that calls the user's main fn pointer directly
    // and returns 0, bypassing trait object construction.
    //
    //   lang_start(main: fn() [rdi], argc [rsi], argv [rdx], sigpipe [rcx]) -> isize
    //     push   rbp
    //     mov    rbp, rsp
    //     call   rdi           ; call user's main
    //     xor    eax, eax      ; return 0
    //     pop    rbp
    //     ret
    let start_code = vec![
        0x55,                   // push rbp
        0x48, 0x89, 0xe5,      // mov rbp, rsp
        0xff, 0xd7,             // call rdi
        0x31, 0xc0,             // xor eax, eax
        0x5d,                   // pop rbp
        0xc3,                   // ret
    ];

    let funcs = vec![
        tuffy_target_x86::emit::CompiledFunction {
            name: "main".to_string(),
            code: main_code,
            relocations: main_relocs,
        },
        tuffy_target_x86::emit::CompiledFunction {
            name: start_sym,
            code: start_code,
            relocations: vec![],
        },
    ];

    let object_data = tuffy_target_x86::emit::emit_elf_multi(&funcs);
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
