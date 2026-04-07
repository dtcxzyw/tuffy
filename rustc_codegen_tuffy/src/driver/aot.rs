use std::any::Any;
use std::collections::HashSet;
use std::fmt::Write;
use std::fs;

use rustc_codegen_ssa::{CompiledModule, CompiledModules, CrateInfo, ModuleKind};
use rustc_data_structures::fx::FxIndexMap;
use rustc_hir::attrs::Linkage;
use rustc_middle::dep_graph::{WorkProduct, WorkProductId};
use rustc_middle::mir::mono::MonoItem;
use rustc_middle::ty::{self, Instance, TyCtxt};
use tuffy_codegen::CodegenSession;
use tuffy_target::reloc::{RelocKind, Relocation};
use tuffy_target::types::{CompiledFunction, StaticData};

use crate::allocator;
use crate::config::BackendOptions;
use crate::main_shim;
use crate::mir_to_ir;
use crate::rust_try;
use crate::static_data::collect_alloc_relocs;

struct OngoingCodegen {
    compiled_modules: CompiledModules,
}

struct AotCodegen<'tcx> {
    tcx: TyCtxt<'tcx>,
    session: CodegenSession,
    config: BackendOptions,
    modules: Vec<CompiledModule>,
    compiled_symbols: HashSet<String>,
    pending_instances: Vec<Instance<'tcx>>,
    module_ir_text: Option<String>,
    data_counter: u64,
}

#[derive(Default)]
struct TranslationCaches {
    vtable_cache: mir_to_ir::VtableCache,
    alloc_cache: mir_to_ir::AllocCache,
    content_cache: mir_to_ir::ContentCache,
}

#[derive(Default)]
struct ObjectArtifacts {
    functions: Vec<CompiledFunction>,
    static_data: Vec<StaticData>,
}

pub(crate) fn codegen_crate<'tcx>(tcx: TyCtxt<'tcx>, _crate_info: &CrateInfo) -> Box<dyn Any> {
    let config = BackendOptions::from_session(tcx.sess);
    let session = CodegenSession::new(tcx.sess.target.llvm_target.as_ref());
    let compiled_modules = AotCodegen::new(tcx, session, config).run();
    Box::new(OngoingCodegen { compiled_modules })
}

pub(crate) fn join_codegen(
    ongoing_codegen: Box<dyn Any>,
) -> (CompiledModules, FxIndexMap<WorkProductId, WorkProduct>) {
    let ongoing_codegen = *ongoing_codegen
        .downcast::<OngoingCodegen>()
        .expect("expected OngoingCodegen");
    (
        ongoing_codegen.compiled_modules,
        FxIndexMap::<WorkProductId, WorkProduct>::default(),
    )
}

impl<'tcx> AotCodegen<'tcx> {
    fn new(tcx: TyCtxt<'tcx>, session: CodegenSession, config: BackendOptions) -> Self {
        let module_ir_text = config.dump_module_path.as_ref().map(|_| String::new());
        Self {
            tcx,
            session,
            config,
            modules: Vec::new(),
            compiled_symbols: HashSet::new(),
            pending_instances: Vec::new(),
            module_ir_text,
            data_counter: 0,
        }
    }

    fn run(mut self) -> CompiledModules {
        let cgus = self.tcx.collect_and_partition_mono_items(()).codegen_units;
        for cgu in cgus {
            let cgu_name = cgu.name().to_string();
            let mono_items = cgu.items_in_deterministic_order(self.tcx);

            let mut artifacts = ObjectArtifacts::default();
            let mut caches = TranslationCaches::default();

            for (mono_item, item_data) in &mono_items {
                match mono_item {
                    MonoItem::Fn(instance) => self.codegen_fn_item(
                        *instance,
                        is_weak_linkage(item_data.linkage),
                        &mut artifacts,
                        &mut caches,
                    ),
                    MonoItem::Static(def_id) => {
                        self.codegen_static_item(*def_id, &mut artifacts, &mut caches)
                    }
                    MonoItem::GlobalAsm(_) => {}
                }
            }

            if !artifacts.functions.is_empty() || !artifacts.static_data.is_empty() {
                self.modules.push(self.emit_module(
                    &cgu_name,
                    ModuleKind::Regular,
                    &artifacts.functions,
                    &artifacts.static_data,
                ));
            }
        }

        self.pre_register_known_symbols();
        self.codegen_inline_instances();

        let allocator_module = allocator::generate_allocator_module(self.tcx, &self.session);

        if let Some(entry_module) = main_shim::generate_entry_point(self.tcx, &self.session) {
            self.modules.push(entry_module);
        }

        if let Some(try_module) = rust_try::generate_rust_try(self.tcx) {
            self.modules.push(try_module);
        }

        self.write_module_dump();

        CompiledModules {
            modules: self.modules,
            allocator_module,
        }
    }

    fn codegen_fn_item(
        &mut self,
        instance: Instance<'tcx>,
        weak: bool,
        artifacts: &mut ObjectArtifacts,
        caches: &mut TranslationCaches,
    ) {
        if Some(instance.def_id()) == self.tcx.lang_items().start_fn() {
            return;
        }
        if let ty::InstanceKind::Intrinsic(def_id) = instance.def
            && self
                .tcx
                .intrinsic(def_id)
                .is_some_and(|intrinsic| intrinsic.must_be_overridden)
        {
            return;
        }
        if let ty::InstanceKind::Item(def_id) = instance.def
            && !def_id.is_local()
            && !self.tcx.is_mir_available(def_id)
            && !matches!(self.tcx.def_kind(def_id), rustc_hir::def::DefKind::Ctor(..))
        {
            return;
        }

        self.compiled_symbols
            .insert(self.tcx.symbol_name(instance).name.to_string());
        self.compile_instance(instance, weak, true, artifacts, caches);
    }

    fn codegen_static_item(
        &mut self,
        def_id: rustc_hir::def_id::DefId,
        artifacts: &mut ObjectArtifacts,
        caches: &mut TranslationCaches,
    ) {
        let attrs = self.tcx.codegen_fn_attrs(def_id);
        let is_extern_weak = matches!(attrs.linkage, Some(Linkage::ExternalWeak))
            || matches!(attrs.import_linkage, Some(Linkage::ExternalWeak));
        if is_extern_weak {
            let instance = Instance::mono(self.tcx, def_id);
            let sym_name = self.tcx.symbol_name(instance).name.to_string();
            artifacts.static_data.push(StaticData {
                name: sym_name,
                data: vec![],
                relocations: vec![],
                writable: false,
                used: false,
                weak_undefined: true,
                align: 1,
                thread_local: false,
            });
            return;
        }

        let Ok(alloc) = self.tcx.eval_static_initializer(def_id) else {
            return;
        };

        let instance = Instance::mono(self.tcx, def_id);
        let sym_name = self.tcx.symbol_name(instance).name.to_string();
        let inner = alloc.inner();
        let bytes = inner
            .inspect_with_uninit_and_ptr_outside_interpreter(0..inner.len())
            .to_vec();
        let relocs = collect_alloc_relocs(
            self.tcx,
            inner,
            &mut artifacts.static_data,
            &mut self.pending_instances,
            &mut self.data_counter,
            &mut caches.vtable_cache,
        );
        self.append_static_dump(&sym_name, &bytes, &relocs);

        let (writable, used) = match self.tcx.def_kind(def_id) {
            rustc_hir::def::DefKind::Static {
                mutability, nested, ..
            } if nested => (mutability == rustc_ast::Mutability::Mut, false),
            _ => {
                let static_ty = self.tcx.type_of(def_id).instantiate_identity();
                let writable = self.tcx.is_mutable_static(def_id)
                    || !static_ty.is_freeze(self.tcx, ty::TypingEnv::fully_monomorphized());
                let flags = self.tcx.codegen_fn_attrs(def_id).flags;
                use rustc_middle::middle::codegen_fn_attrs::CodegenFnAttrFlags;
                let used = flags.contains(CodegenFnAttrFlags::USED_LINKER)
                    || flags.contains(CodegenFnAttrFlags::USED_COMPILER);
                (writable, used)
            }
        };
        let thread_local = {
            use rustc_middle::middle::codegen_fn_attrs::CodegenFnAttrFlags;
            attrs.flags.contains(CodegenFnAttrFlags::THREAD_LOCAL)
        };

        artifacts.static_data.push(StaticData {
            name: sym_name,
            data: bytes,
            relocations: relocs,
            writable,
            used,
            weak_undefined: false,
            align: inner.align.bytes(),
            thread_local,
        });
    }

    fn compile_instance(
        &mut self,
        instance: Instance<'tcx>,
        weak: bool,
        dump_mir: bool,
        artifacts: &mut ObjectArtifacts,
        caches: &mut TranslationCaches,
    ) {
        if self.config.dump_ir && dump_mir {
            self.dump_mir(instance);
        }

        let result = mir_to_ir::translate_function(
            self.tcx,
            instance,
            &self.session,
            &mut self.data_counter,
            &mut caches.vtable_cache,
            &mut caches.alloc_cache,
            &mut caches.content_cache,
        );

        let Some(mut result) = result else {
            artifacts.functions.push(make_stub(
                self.tcx.symbol_name(instance).name.to_string(),
                weak,
            ));
            return;
        };

        self.pending_instances
            .extend(result.referenced_instances.iter().copied());
        self.append_translation_dump(&result);
        verify_translation_result(&result);
        append_translation_static_data(&mut artifacts.static_data, &result);

        if let Some(mut compiled) = self
            .session
            .compile_function(&result.func, &mut result.symbols)
        {
            compiled.weak = weak;
            artifacts.functions.push(compiled);
            return;
        }

        let sym_name = self.tcx.symbol_name(instance).name.to_string();
        let func_name = result.symbols.resolve(result.func.name);
        eprintln!("warning: isel failed for {func_name}, emitting stub");
        artifacts.functions.push(make_stub(sym_name, weak));
    }

    fn codegen_inline_instances(&mut self) {
        let mut artifacts = ObjectArtifacts::default();
        let mut caches = TranslationCaches::default();

        loop {
            let batch: Vec<Instance<'tcx>> = self
                .pending_instances
                .drain(..)
                .filter(|instance| {
                    let symbol = self.tcx.symbol_name(*instance).name.to_string();
                    self.compiled_symbols.insert(symbol)
                })
                .collect();
            if batch.is_empty() {
                break;
            }

            for instance in batch {
                if let ty::InstanceKind::Item(def_id) = instance.def
                    && !self.tcx.is_mir_available(def_id)
                    && !matches!(self.tcx.def_kind(def_id), rustc_hir::def::DefKind::Ctor(..))
                {
                    continue;
                }
                self.compile_instance(instance, true, false, &mut artifacts, &mut caches);
            }
        }

        if !artifacts.functions.is_empty() {
            self.modules.push(self.emit_module(
                "inline_shims",
                ModuleKind::Regular,
                &artifacts.functions,
                &artifacts.static_data,
            ));
        }
    }

    fn pre_register_known_symbols(&mut self) {
        for name in [
            "__rust_alloc",
            "__rust_dealloc",
            "__rust_realloc",
            "__rust_alloc_zeroed",
            "__rust_no_alloc_shim_is_unstable_v2",
        ] {
            self.compiled_symbols
                .insert(rustc_symbol_mangling::mangle_internal_symbol(
                    self.tcx, name,
                ));
        }

        for name in [
            "free",
            "malloc",
            "realloc",
            "calloc",
            "posix_memalign",
            "aligned_alloc",
        ] {
            self.compiled_symbols.insert(name.to_string());
        }
    }

    fn emit_module(
        &self,
        name: &str,
        kind: ModuleKind,
        functions: &[CompiledFunction],
        static_data: &[StaticData],
    ) -> CompiledModule {
        let object_data = self.session.emit_object(functions, static_data);
        let tmp = self.tcx.output_filenames(()).temp_path_for_cgu(
            rustc_session::config::OutputType::Object,
            name,
            self.tcx.sess.invocation_temp.as_deref(),
        );
        fs::write(&tmp, &object_data).expect("failed to write object file");

        CompiledModule {
            name: name.to_string(),
            kind,
            object: Some(tmp),
            dwarf_object: None,
            bytecode: None,
            assembly: None,
            llvm_ir: None,
            links_from_incr_cache: vec![],
        }
    }

    fn dump_mir(&self, instance: Instance<'tcx>) {
        use rustc_middle::ty::print::with_no_trimmed_paths;

        with_no_trimmed_paths!({
            let mir = self.tcx.instance_mir(instance.def);
            let mut buf = Vec::new();
            let writer = rustc_middle::mir::pretty::MirWriter::new(self.tcx);
            writer.write_mir_fn(mir, &mut buf).unwrap();
            eprint!("{}", String::from_utf8_lossy(&buf));
        });
    }

    fn append_translation_dump(&mut self, result: &mir_to_ir::TranslationResult<'tcx>) {
        if self.config.dump_ir {
            for (sym_id, data, relocs, _align) in &result.static_data {
                let name = result.symbols.resolve(*sym_id);
                let reloc_strs: Vec<(usize, &str)> = relocs
                    .iter()
                    .map(|(offset, sym)| (*offset, sym.as_str()))
                    .collect();
                eprintln!(
                    "{}",
                    tuffy_ir::display::StaticDataDisplay {
                        name,
                        data,
                        relocs: &reloc_strs,
                    }
                );
            }
            eprintln!("{}", result.func.display(&result.symbols));
            eprintln!();
        }

        if let Some(buf) = &mut self.module_ir_text {
            for (sym_id, data, relocs, _align) in &result.static_data {
                let name = result.symbols.resolve(*sym_id);
                let reloc_strs: Vec<(usize, &str)> = relocs
                    .iter()
                    .map(|(offset, sym)| (*offset, sym.as_str()))
                    .collect();
                writeln!(
                    buf,
                    "{}",
                    tuffy_ir::display::StaticDataDisplay {
                        name,
                        data,
                        relocs: &reloc_strs,
                    }
                )
                .unwrap();
            }
            writeln!(buf, "{}\n", result.func.display(&result.symbols)).unwrap();
        }
    }

    fn append_static_dump(&mut self, name: &str, data: &[u8], relocs: &[Relocation]) {
        let Some(buf) = &mut self.module_ir_text else {
            return;
        };

        let reloc_strs: Vec<(usize, &str)> = relocs
            .iter()
            .map(|reloc| (reloc.offset, reloc.symbol.as_str()))
            .collect();
        writeln!(
            buf,
            "{}",
            tuffy_ir::display::StaticDataDisplay {
                name,
                data,
                relocs: &reloc_strs,
            }
        )
        .unwrap();
    }

    fn write_module_dump(&self) {
        let Some(path) = &self.config.dump_module_path else {
            return;
        };
        let Some(text) = &self.module_ir_text else {
            return;
        };
        fs::write(path, text)
            .unwrap_or_else(|err| panic!("failed to write module IR to {}: {err}", path.display()));
    }
}

fn verify_translation_result(result: &mir_to_ir::TranslationResult<'_>) {
    let verification = tuffy_ir::verifier::verify_function(&result.func, &result.symbols);
    if !verification.is_ok() {
        let func_name = result.symbols.resolve(result.func.name);
        panic!("IR verification failed for {func_name}: {verification}");
    }
}

fn append_translation_static_data(
    all_static_data: &mut Vec<StaticData>,
    result: &mir_to_ir::TranslationResult<'_>,
) {
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

    for (sym_id, data, relocs, align) in &result.static_data {
        all_static_data.push(StaticData {
            name: result.symbols.resolve(*sym_id).to_string(),
            data: data.clone(),
            relocations: relocs
                .iter()
                .map(|(offset, symbol)| Relocation {
                    offset: *offset,
                    symbol: symbol.clone(),
                    kind: RelocKind::Abs64,
                })
                .collect(),
            writable: false,
            used: false,
            weak_undefined: false,
            align: *align,
            thread_local: false,
        });
    }
}

fn is_weak_linkage(linkage: Linkage) -> bool {
    matches!(
        linkage,
        Linkage::Internal
            | Linkage::LinkOnceODR
            | Linkage::WeakODR
            | Linkage::LinkOnceAny
            | Linkage::WeakAny
    )
}

fn make_stub(name: String, weak: bool) -> CompiledFunction {
    let code = if is_noop_stub(&name) {
        vec![0xC3]
    } else {
        vec![0x0F, 0x0B]
    };

    CompiledFunction {
        name,
        code,
        relocations: vec![],
        weak,
        local: false,
        has_frame_pointer: false,
        call_site_table: vec![],
        callee_saved_dwarf_regs: vec![],
        sub_amount: 0,
    }
}

fn is_noop_stub(name: &str) -> bool {
    name.contains("drop_in_place") || name.contains("precondition_check")
}
