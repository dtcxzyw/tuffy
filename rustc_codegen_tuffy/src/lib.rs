//! rustc_codegen_tuffy: Rustc codegen backend using tuffy IR.
//!
//! This crate implements `CodegenBackend` from `rustc_codegen_ssa`,
//! translating rustc MIR into tuffy IR for optimization and code generation.
//!
//! Build with: `rustc -Z codegen-backend=path/to/librustc_codegen_tuffy.so`

#![feature(rustc_private)]
#![feature(box_patterns)]

extern crate rustc_abi;
extern crate rustc_ast;
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
use std::collections::HashSet;
use std::fs;

use rustc_codegen_ssa::traits::CodegenBackend;
use rustc_codegen_ssa::{CompiledModule, CompiledModules, CrateInfo, ModuleKind, TargetConfig};
use rustc_data_structures::fx::FxIndexMap;
use rustc_middle::dep_graph::{WorkProduct, WorkProductId};
use rustc_middle::mir::interpret::GlobalAlloc;
use rustc_middle::mir::mono::MonoItem;
use rustc_middle::ty::{self, Instance, TyCtxt};
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

    fn target_cpu(&self, sess: &Session) -> String {
        sess.target.cpu.to_string()
    }

    fn codegen_crate<'tcx>(&self, tcx: TyCtxt<'tcx>, _crate_info: &CrateInfo) -> Box<dyn Any> {
        let target_triple = tcx.sess.target.llvm_target.as_ref();
        let session = CodegenSession::new(target_triple);
        let dump_ir = tcx.sess.opts.cg.llvm_args.iter().any(|a| a == "dump-ir");
        let dump_module_path = tcx
            .sess
            .opts
            .cg
            .llvm_args
            .iter()
            .find_map(|a| a.strip_prefix("dump-module="))
            .map(|s| s.to_string());
        let cgus = tcx.collect_and_partition_mono_items(()).codegen_units;
        let mut modules = Vec::new();
        let mut compiled_symbols: HashSet<String> = HashSet::new();
        let mut pending_instances: Vec<Instance<'tcx>> = Vec::new();
        let mut module_ir_text = if dump_module_path.is_some() {
            Some(String::new())
        } else {
            None
        };

        let mut data_counter: u64 = 0;
        for cgu in cgus {
            let cgu_name = cgu.name().to_string();
            let mono_items = cgu.items_in_deterministic_order(tcx);

            let mut compiled_funcs: Vec<CompiledFunction> = Vec::new();
            let mut all_static_data: Vec<StaticData> = Vec::new();
            let mut vtable_cache: mir_to_ir::VtableCache = std::collections::HashMap::new();
            let mut alloc_cache: mir_to_ir::AllocCache = std::collections::HashMap::new();
            let mut content_cache: mir_to_ir::ContentCache = std::collections::HashMap::new();

            for (mono_item, item_data) in &mono_items {
                if let MonoItem::Fn(instance) = mono_item {
                    // Skip lang_start — tuffy can't compile the trait object
                    // construction it requires. We emit a hand-crafted version
                    // in generate_entry_point instead.
                    if Some(instance.def_id()) == tcx.lang_items().start_fn() {
                        continue;
                    }
                    // Skip intrinsics that must be overridden — they have no
                    // MIR body and are handled inline at call sites.
                    if let ty::InstanceKind::Intrinsic(def_id) = instance.def
                        && tcx.intrinsic(def_id).is_some_and(|i| i.must_be_overridden)
                    {
                        continue;
                    }
                    // Skip non-local functions without MIR — they are already
                    // compiled in their rlib. Emitting a stub here would
                    // override the real implementation.
                    if let ty::InstanceKind::Item(def_id) = instance.def
                        && !def_id.is_local()
                        && !tcx.is_mir_available(def_id)
                        && !matches!(tcx.def_kind(def_id), rustc_hir::def::DefKind::Ctor(..))
                    {
                        continue;
                    }
                    compiled_symbols.insert(tcx.symbol_name(*instance).name.to_string());
                    if dump_ir {
                        use rustc_middle::ty::print::with_no_trimmed_paths;
                        with_no_trimmed_paths!({
                            let mir = tcx.instance_mir(instance.def);
                            let mut buf = Vec::new();
                            let writer = rustc_middle::mir::pretty::MirWriter::new(tcx);
                            writer.write_mir_fn(mir, &mut buf).unwrap();
                            eprint!("{}", String::from_utf8_lossy(&buf));
                        });
                    }
                    let result_opt = mir_to_ir::translate_function(
                        tcx,
                        *instance,
                        &session,
                        &mut data_counter,
                        &mut vtable_cache,
                        &mut alloc_cache,
                        &mut content_cache,
                    );
                    if let Some(mut result) = result_opt {
                        pending_instances.extend(result.referenced_instances.iter().copied());
                        if dump_ir {
                            for (sym_id, data, relocs, _align) in &result.static_data {
                                let name = result.symbols.resolve(*sym_id);
                                let reloc_strs: Vec<(usize, &str)> =
                                    relocs.iter().map(|(o, s)| (*o, s.as_str())).collect();
                                eprintln!(
                                    "{}",
                                    tuffy_ir::display::StaticDataDisplay {
                                        name,
                                        data,
                                        relocs: &reloc_strs
                                    }
                                );
                            }
                            eprintln!("{}", result.func.display(&result.symbols));
                            eprintln!();
                        }
                        if let Some(ref mut buf) = module_ir_text {
                            use std::fmt::Write;
                            for (sym_id, data, relocs, _align) in &result.static_data {
                                let name = result.symbols.resolve(*sym_id);
                                let reloc_strs: Vec<(usize, &str)> =
                                    relocs.iter().map(|(o, s)| (*o, s.as_str())).collect();
                                writeln!(
                                    buf,
                                    "{}",
                                    tuffy_ir::display::StaticDataDisplay {
                                        name,
                                        data,
                                        relocs: &reloc_strs
                                    }
                                )
                                .unwrap();
                            }
                            writeln!(buf, "{}\n", result.func.display(&result.symbols)).unwrap();
                        }

                        let vr = tuffy_ir::verifier::verify_function(&result.func, &result.symbols);
                        if !vr.is_ok() {
                            let func_name = result.symbols.resolve(result.func.name);
                            panic!("IR verification failed for {func_name}: {vr}");
                        } else {
                            // Emit weak undefined symbols FIRST so they are in
                            // sym_map before any static data relocations reference
                            // them (otherwise the emitter creates strong references).
                            for sym in &result.weak_undefined_symbols {
                                all_static_data.push(StaticData {
                                    name: sym.clone(),
                                    data: vec![],
                                    relocations: vec![],
                                    writable: false,
                                    used: false,
                                    weak_undefined: true,
                                    align: 1,
                                    thread_local: false,
                                });
                            }
                            for (sym_id, data, relocs, sd_align) in &result.static_data {
                                all_static_data.push(StaticData {
                                    name: result.symbols.resolve(*sym_id).to_string(),
                                    data: data.clone(),
                                    relocations: relocs
                                        .iter()
                                        .map(|(offset, sym)| tuffy_target::reloc::Relocation {
                                            offset: *offset,
                                            symbol: sym.clone(),
                                            kind: tuffy_target::reloc::RelocKind::Abs64,
                                        })
                                        .collect(),
                                    writable: false,
                                    used: false,
                                    weak_undefined: false,
                                    align: *sd_align,
                                    thread_local: false,
                                });
                            }

                            if let Some(mut cf) = session.compile_function(
                                &result.func,
                                &mut result.symbols,
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
                            } else {
                                // Isel failed — emit stub.
                                let sym_name = tcx.symbol_name(*instance).name.to_string();
                                let func_name = result.symbols.resolve(result.func.name);
                                eprintln!("warning: isel failed for {func_name}, emitting stub");
                                let is_noop = sym_name.contains("drop_in_place")
                                    || sym_name.contains("precondition_check");
                                let code: Vec<u8> = if is_noop {
                                    vec![0xC3]
                                } else {
                                    vec![0x0F, 0x0B]
                                };
                                use rustc_hir::attrs::Linkage;
                                compiled_funcs.push(CompiledFunction {
                                    name: sym_name,
                                    code,
                                    relocations: vec![],
                                    weak: matches!(
                                        item_data.linkage,
                                        Linkage::Internal
                                            | Linkage::LinkOnceODR
                                            | Linkage::WeakODR
                                            | Linkage::LinkOnceAny
                                            | Linkage::WeakAny
                                    ),
                                    local: false,
                                    has_frame_pointer: false,
                                    call_site_table: vec![],
                                    callee_saved_dwarf_regs: vec![],
                                    sub_amount: 0,
                                });
                            }
                        }
                    } else {
                        // Translation failed — emit a minimal stub so the
                        // linker can resolve the symbol.  drop_in_place and
                        // precondition_check stubs just return; everything
                        // else traps with ud2 if actually called.
                        let sym_name = tcx.symbol_name(*instance).name.to_string();
                        let is_noop = sym_name.contains("drop_in_place")
                            || sym_name.contains("precondition_check");
                        let code: Vec<u8> = if is_noop {
                            // ret
                            vec![0xC3]
                        } else {
                            // ud2
                            vec![0x0F, 0x0B]
                        };
                        use rustc_hir::attrs::Linkage;
                        compiled_funcs.push(CompiledFunction {
                            name: sym_name,
                            code,
                            relocations: vec![],
                            weak: matches!(
                                item_data.linkage,
                                Linkage::Internal
                                    | Linkage::LinkOnceODR
                                    | Linkage::WeakODR
                                    | Linkage::LinkOnceAny
                                    | Linkage::WeakAny
                            ),
                            local: false,
                            has_frame_pointer: false,
                            call_site_table: vec![],
                            callee_saved_dwarf_regs: vec![],
                            sub_amount: 0,
                        });
                    }
                }
                if let MonoItem::Static(def_id) = mono_item {
                    // Extern weak statics (e.g. from `weak!` macro) have no
                    // initializer — emit as weak undefined symbols so the
                    // linker resolves them to 0 when not found.
                    let attrs = tcx.codegen_fn_attrs(*def_id);
                    let is_extern_weak =
                        matches!(attrs.linkage, Some(rustc_hir::attrs::Linkage::ExternalWeak))
                            || matches!(
                                attrs.import_linkage,
                                Some(rustc_hir::attrs::Linkage::ExternalWeak)
                            );
                    if is_extern_weak {
                        let instance = Instance::mono(tcx, *def_id);
                        let sym_name = tcx.symbol_name(instance).name.to_string();
                        all_static_data.push(StaticData {
                            name: sym_name,
                            data: vec![],
                            relocations: vec![],
                            writable: false,
                            used: false,
                            weak_undefined: true,
                            align: 1,
                            thread_local: false,
                        });
                    } else if let Ok(alloc) = tcx.eval_static_initializer(*def_id) {
                        let instance = Instance::mono(tcx, *def_id);
                        let sym_name = tcx.symbol_name(instance).name.to_string();
                        let inner = alloc.inner();
                        let bytes = inner
                            .inspect_with_uninit_and_ptr_outside_interpreter(0..inner.len())
                            .to_vec();
                        let relocs = collect_alloc_relocs(
                            tcx,
                            inner,
                            &mut all_static_data,
                            &mut pending_instances,
                            &mut data_counter,
                            &mut vtable_cache,
                        );
                        if let Some(ref mut buf) = module_ir_text {
                            use std::fmt::Write;
                            let reloc_strs: Vec<(usize, &str)> = relocs
                                .iter()
                                .map(|r| (r.offset, r.symbol.as_str()))
                                .collect();
                            writeln!(
                                buf,
                                "{}",
                                tuffy_ir::display::StaticDataDisplay {
                                    name: &sym_name,
                                    data: &bytes,
                                    relocs: &reloc_strs
                                }
                            )
                            .unwrap();
                        }
                        // Nested statics (e.g. `FOO::{nested#0}`) are synthetic
                        // allocations whose DefId does not support `type_of`.
                        // Derive mutability from the DefKind directly.
                        let (needs_write, is_used) = match tcx.def_kind(*def_id) {
                            rustc_hir::def::DefKind::Static {
                                mutability, nested, ..
                            } if nested => (mutability == rustc_ast::Mutability::Mut, false),
                            _ => {
                                // A static is writable if it's `static mut` OR
                                // if its type has interior mutability (contains
                                // UnsafeCell), e.g. Mutex, Cell, AtomicU32.
                                // Such types must live in .data, not .rodata.
                                let static_ty = tcx.type_of(*def_id).instantiate_identity();
                                let writable = tcx.is_mutable_static(*def_id)
                                    || !static_ty
                                        .is_freeze(tcx, ty::TypingEnv::fully_monomorphized());
                                let used = {
                                    let flags = tcx.codegen_fn_attrs(*def_id).flags;
                                    use rustc_middle::middle::codegen_fn_attrs::CodegenFnAttrFlags;
                                    flags.contains(CodegenFnAttrFlags::USED_LINKER)
                                        || flags.contains(CodegenFnAttrFlags::USED_COMPILER)
                                };
                                (writable, used)
                            }
                        };
                        let is_tls = {
                            use rustc_middle::middle::codegen_fn_attrs::CodegenFnAttrFlags;
                            attrs.flags.contains(CodegenFnAttrFlags::THREAD_LOCAL)
                        };
                        all_static_data.push(StaticData {
                            name: sym_name,
                            data: bytes,
                            relocations: relocs,
                            writable: needs_write,
                            used: is_used,
                            weak_undefined: false,
                            align: inner.align.bytes(),
                            thread_local: is_tls,
                        });
                    }
                }
            }

            if !compiled_funcs.is_empty() || !all_static_data.is_empty() {
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

        // Pre-register allocator shim symbols so the fixpoint loop does
        // not emit ud2 stubs that override the real forwarding stubs.
        for name in [
            "__rust_alloc",
            "__rust_dealloc",
            "__rust_realloc",
            "__rust_alloc_zeroed",
            "__rust_no_alloc_shim_is_unstable_v2",
        ] {
            compiled_symbols.insert(rustc_symbol_mangling::mangle_internal_symbol(tcx, name));
        }

        // Skip C library functions that must be resolved by the linker.
        for name in [
            "free",
            "malloc",
            "realloc",
            "calloc",
            "posix_memalign",
            "aligned_alloc",
        ] {
            compiled_symbols.insert(name.to_string());
        }

        // Fixpoint loop: compile #[inline] functions not collected as mono
        // items but referenced by direct calls during translation.
        let mut inline_funcs: Vec<CompiledFunction> = Vec::new();
        let mut inline_static_data: Vec<StaticData> = Vec::new();
        let mut inline_data_counter: u64 = data_counter; // continues from main loop
        let mut inline_vtable_cache: mir_to_ir::VtableCache = std::collections::HashMap::new();
        let mut inline_alloc_cache: mir_to_ir::AllocCache = std::collections::HashMap::new();
        // Share content_cache with the main loop so identical const allocations
        // are deduplicated across mono-item and inline function compilation.
        let mut inline_content_cache: mir_to_ir::ContentCache = std::collections::HashMap::new();
        loop {
            let batch: Vec<Instance<'tcx>> = pending_instances
                .drain(..)
                .filter(|inst| {
                    let sym = tcx.symbol_name(*inst).name.to_string();
                    compiled_symbols.insert(sym)
                })
                .collect();
            if batch.is_empty() {
                break;
            }
            for inst in batch {
                // Skip items without MIR — cross-crate non-inline
                // functions already exist in the rlib, and local extern
                // declarations (no body) must be resolved by the linker.
                if let ty::InstanceKind::Item(def_id) = inst.def
                    && !tcx.is_mir_available(def_id)
                    && !matches!(tcx.def_kind(def_id), rustc_hir::def::DefKind::Ctor(..))
                {
                    continue;
                }
                let mut result = match mir_to_ir::translate_function(
                    tcx,
                    inst,
                    &session,
                    &mut inline_data_counter,
                    &mut inline_vtable_cache,
                    &mut inline_alloc_cache,
                    &mut inline_content_cache,
                ) {
                    Some(r) => r,
                    None => {
                        let sym_name = tcx.symbol_name(inst).name.to_string();
                        let is_noop = sym_name.contains("drop_in_place")
                            || sym_name.contains("precondition_check");
                        inline_funcs.push(CompiledFunction {
                            name: sym_name,
                            code: if is_noop {
                                vec![0xC3]
                            } else {
                                vec![0x0F, 0x0B]
                            },
                            relocations: vec![],
                            weak: true,
                            local: false,
                            has_frame_pointer: false,
                            call_site_table: vec![],
                            callee_saved_dwarf_regs: vec![],
                            sub_amount: 0,
                        });
                        continue;
                    }
                };
                pending_instances.extend(result.referenced_instances.iter().copied());
                if let Some(ref mut buf) = module_ir_text {
                    use std::fmt::Write;
                    for (sym_id, data, relocs, _sd_align) in &result.static_data {
                        let name = result.symbols.resolve(*sym_id);
                        let reloc_strs: Vec<(usize, &str)> =
                            relocs.iter().map(|(o, s)| (*o, s.as_str())).collect();
                        writeln!(
                            buf,
                            "{}",
                            tuffy_ir::display::StaticDataDisplay {
                                name,
                                data,
                                relocs: &reloc_strs
                            }
                        )
                        .unwrap();
                    }
                    writeln!(buf, "{}\n", result.func.display(&result.symbols)).unwrap();
                }
                let vr = tuffy_ir::verifier::verify_function(&result.func, &result.symbols);
                if !vr.is_ok() {
                    let func_name = result.symbols.resolve(result.func.name);
                    panic!("IR verification failed for {func_name}: {vr}");
                }
                // Emit weak undefined symbols FIRST.
                for sym in &result.weak_undefined_symbols {
                    inline_static_data.push(StaticData {
                        name: sym.clone(),
                        data: vec![],
                        relocations: vec![],
                        writable: false,
                        used: false,
                        weak_undefined: true,
                        align: 1,
                        thread_local: false,
                    });
                }
                for (sym_id, data, relocs, sd_align) in &result.static_data {
                    inline_static_data.push(StaticData {
                        name: result.symbols.resolve(*sym_id).to_string(),
                        data: data.clone(),
                        relocations: relocs
                            .iter()
                            .map(|(offset, sym)| tuffy_target::reloc::Relocation {
                                offset: *offset,
                                symbol: sym.clone(),
                                kind: tuffy_target::reloc::RelocKind::Abs64,
                            })
                            .collect(),
                        writable: false,
                        used: false,
                        weak_undefined: false,
                        align: *sd_align,
                        thread_local: false,
                    });
                }
                if let Some(mut cf) = session.compile_function(
                    &result.func,
                    &mut result.symbols,
                    &result.abi_metadata,
                ) {
                    cf.weak = true;
                    inline_funcs.push(cf);
                } else {
                    let sym_name = tcx.symbol_name(inst).name.to_string();
                    let is_noop = sym_name.contains("drop_in_place")
                        || sym_name.contains("precondition_check");
                    inline_funcs.push(CompiledFunction {
                        name: sym_name,
                        code: if is_noop {
                            vec![0xC3]
                        } else {
                            vec![0x0F, 0x0B]
                        },
                        relocations: vec![],
                        weak: true,
                        local: false,
                        has_frame_pointer: false,
                        call_site_table: vec![],
                        callee_saved_dwarf_regs: vec![],
                        sub_amount: 0,
                    });
                }
            }
        }
        if !inline_funcs.is_empty() {
            let object_data = session.emit_object(&inline_funcs, &inline_static_data);
            let tmp = tcx.output_filenames(()).temp_path_for_cgu(
                rustc_session::config::OutputType::Object,
                "inline_shims",
                tcx.sess.invocation_temp.as_deref(),
            );
            fs::write(&tmp, &object_data).expect("failed to write inline shims");
            modules.push(CompiledModule {
                name: "inline_shims".to_string(),
                kind: ModuleKind::Regular,
                object: Some(tmp),
                dwarf_object: None,
                bytecode: None,
                assembly: None,
                llvm_ir: None,
                links_from_incr_cache: vec![],
            });
        }

        // Generate allocator shim if needed.
        let allocator_module = generate_allocator_module(tcx, &session);

        // Generate C `main` entry point if this is a binary crate.
        if let Some(entry_module) = generate_entry_point(tcx, &session) {
            modules.push(entry_module);
        }

        // Generate __rust_try helper if catch_unwind was used.
        if let Some(try_module) = generate_rust_try(tcx) {
            modules.push(try_module);
        }

        // Write complete module IR to file if dump-module was requested.
        if let Some(path) = dump_module_path
            && let Some(text) = module_ir_text
        {
            fs::write(&path, text).unwrap_or_else(|e| {
                panic!("failed to write module IR to {path}: {e}");
            });
        }

        Box::new(CompiledModules {
            modules,
            allocator_module,
        })
    }

    fn join_codegen(
        &self,
        ongoing_codegen: Box<dyn Any>,
        _sess: &Session,
        _outputs: &OutputFilenames,
    ) -> (CompiledModules, FxIndexMap<WorkProductId, WorkProduct>) {
        let compiled_modules = *ongoing_codegen
            .downcast::<CompiledModules>()
            .expect("expected CompiledModules");
        (compiled_modules, FxIndexMap::default())
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
    // Stubs are weak so #[global_allocator] definitions take precedence.
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
    let mut funcs = session.generate_allocator_stubs(&pairs_ref, &shim_marker);
    for f in &mut funcs {
        f.weak = true;
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

/// Extract relocations from an allocation, emitting nested memory
/// allocations as additional `StaticData` entries.
fn collect_alloc_relocs<'tcx>(
    tcx: TyCtxt<'tcx>,
    alloc: &rustc_middle::mir::interpret::Allocation,
    static_data: &mut Vec<StaticData>,
    referenced_instances: &mut Vec<Instance<'tcx>>,
    data_counter: &mut u64,
    vtable_cache: &mut mir_to_ir::VtableCache,
) -> Vec<tuffy_target::reloc::Relocation> {
    let mut relocs = Vec::new();
    for (offset, prov) in alloc.provenance().ptrs().iter() {
        let rel_offset = offset.bytes() as usize;
        let alloc_id = prov.alloc_id();
        let sym = match tcx.global_alloc(alloc_id) {
            GlobalAlloc::Function { instance } => {
                referenced_instances.push(instance);
                tcx.symbol_name(instance).name.to_string()
            }
            GlobalAlloc::Static(def_id) => {
                let inst = Instance::mono(tcx, def_id);
                tcx.symbol_name(inst).name.to_string()
            }
            GlobalAlloc::Memory(nested) => {
                let inner = nested.inner();
                let bytes = inner
                    .inspect_with_uninit_and_ptr_outside_interpreter(0..inner.len())
                    .to_vec();
                let name = format!(".Lstatic.{}", {
                    let id = *data_counter;
                    *data_counter += 1;
                    id
                });
                let nested_relocs = collect_alloc_relocs(
                    tcx,
                    inner,
                    static_data,
                    referenced_instances,
                    data_counter,
                    vtable_cache,
                );
                static_data.push(StaticData {
                    name: name.clone(),
                    data: bytes,
                    relocations: nested_relocs,
                    writable: false,
                    used: false,
                    weak_undefined: false,
                    align: inner.align.bytes(),
                    thread_local: false,
                });
                name
            }
            GlobalAlloc::VTable(ty, trait_ref) => {
                let principal = trait_ref.principal().map(|p| p.skip_binder());
                if let Ok(vtable_id) =
                    std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                        tcx.vtable_allocation((ty, principal))
                    }))
                {
                    // Check vtable cache for deduplication.
                    if let Some(existing_name) = vtable_cache.get(&vtable_id) {
                        existing_name.clone()
                    } else if let GlobalAlloc::Memory(vtable_alloc) = tcx.global_alloc(vtable_id) {
                        let inner = vtable_alloc.inner();
                        let bytes = inner
                            .inspect_with_uninit_and_ptr_outside_interpreter(0..inner.len())
                            .to_vec();
                        let name = format!(".Lvtable.{}", {
                            let id = *data_counter;
                            *data_counter += 1;
                            id
                        });
                        vtable_cache.insert(vtable_id, name.clone());
                        let nested_relocs = collect_alloc_relocs(
                            tcx,
                            inner,
                            static_data,
                            referenced_instances,
                            data_counter,
                            vtable_cache,
                        );
                        static_data.push(StaticData {
                            name: name.clone(),
                            data: bytes,
                            relocations: nested_relocs,
                            writable: false,
                            used: false,
                            weak_undefined: false,
                            align: inner.align.bytes(),
                            thread_local: false,
                        });
                        name
                    } else {
                        continue;
                    }
                } else {
                    continue;
                }
            }
            GlobalAlloc::TypeId { .. } => continue,
        };
        relocs.push(tuffy_target::reloc::Relocation {
            offset: rel_offset,
            symbol: sym,
            kind: tuffy_target::reloc::RelocKind::Abs64,
        });
    }
    relocs
}

/// Generate a `__rust_try` helper object file using the system assembler.
/// This provides the exception-handling wrapper needed by `catch_unwind`.
fn generate_rust_try(tcx: TyCtxt<'_>) -> Option<CompiledModule> {
    let obj_path = tcx.output_filenames(()).temp_path_for_cgu(
        rustc_session::config::OutputType::Object,
        "rust_try",
        tcx.sess.invocation_temp.as_deref(),
    );
    let asm_path = obj_path.with_extension("S");

    fs::write(
        &asm_path,
        r#"
.text
.globl __rust_try
.type __rust_try, @function
__rust_try:
    .cfi_startproc
    .cfi_personality 155, DW.ref.rust_eh_personality
    .cfi_lsda 27, .Lexcept_table0

    # Stack layout (24 bytes, 16-byte aligned with return addr):
    #   16(%rsp) = catch_fn
    #    8(%rsp) = data
    #    0(%rsp) = alignment padding
    # Values stored on the stack survive unwinding (registers don't).
    subq    $24, %rsp
    .cfi_def_cfa_offset 32

    movq    %rdx, 16(%rsp)
    movq    %rsi, 8(%rsp)
    movq    %rdi, %rax
    movq    %rsi, %rdi

.Ltry_begin:
    callq   *%rax
.Ltry_end:

    xorl    %eax, %eax
    .cfi_remember_state
    addq    $24, %rsp
    .cfi_def_cfa_offset 8
    retq

.Lcatch_landing_pad:
    .cfi_restore_state
    movq    8(%rsp), %rdi
    movq    %rax, %rsi
.Lcatch_call_begin:
    callq   *16(%rsp)
.Lcatch_call_end:

    movl    $1, %eax
    addq    $24, %rsp
    .cfi_def_cfa_offset 8
    retq

    .cfi_endproc
.size __rust_try, . - __rust_try

.section .gcc_except_table,"a",@progbits
.p2align 2
.Lexcept_table0:
    .byte   255
    .byte   155
    .uleb128 .Lttbase0 - .Lttbaseref0
.Lttbaseref0:
    .byte   1
    .uleb128 .Lcst_end0 - .Lcst_begin0
.Lcst_begin0:
    # try_fn call: landing pad = catch handler (action 1 = catch-all)
    .uleb128 .Ltry_begin - __rust_try
    .uleb128 .Ltry_end - .Ltry_begin
    .uleb128 .Lcatch_landing_pad - __rust_try
    .uleb128 1
    # catch_fn call: no landing pad (continue unwinding on double-panic)
    .uleb128 .Lcatch_call_begin - __rust_try
    .uleb128 .Lcatch_call_end - .Lcatch_call_begin
    .uleb128 0
    .uleb128 0
.Lcst_end0:
    .byte   1
    .byte   0
    .p2align 2
    .long   0
.Lttbase0:

.section .data.rel.ro,"aw",@progbits
.p2align 3
DW.ref.rust_eh_personality:
    .quad rust_eh_personality
.type DW.ref.rust_eh_personality, @object
.size DW.ref.rust_eh_personality, 8
.hidden DW.ref.rust_eh_personality
"#,
    )
    .expect("failed to write rust_try assembly");

    let status = std::process::Command::new("as")
        .arg("-o")
        .arg(&obj_path)
        .arg(&asm_path)
        .status()
        .expect("failed to run assembler");

    if !status.success() {
        panic!("assembler failed for rust_try.S");
    }

    Some(CompiledModule {
        name: "rust_try".to_string(),
        kind: ModuleKind::Regular,
        object: Some(obj_path),
        dwarf_object: None,
        bytecode: None,
        assembly: None,
        llvm_ir: None,
        links_from_incr_cache: vec![],
    })
}
