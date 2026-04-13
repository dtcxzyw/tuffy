use std::any::Any;
use std::collections::HashSet;
use std::fmt::Write;
use std::fs;
use std::time::Instant;

use rustc_codegen_ssa::{CompiledModule, CompiledModules, CrateInfo, ModuleKind};
use rustc_data_structures::fx::FxIndexMap;
use rustc_hir::attrs::Linkage;
use rustc_middle::dep_graph::{WorkProduct, WorkProductId};
use rustc_middle::mir::mono::MonoItem;
use rustc_middle::ty::{self, Instance, TyCtxt, TypeVisitableExt};
use tuffy_codegen::CodegenSession;
use tuffy_ir::instruction::Op;
use tuffy_ir::module::{
    Module as IrModule, StaticData as IrStaticData, StaticRelocation, SymbolId,
};
use tuffy_opt::PeepholeStats;
use tuffy_target::reloc::{RelocKind, Relocation};
use tuffy_target::types::{CompiledFunction, StaticData};

use crate::allocator;
use crate::config::BackendOptions;
use crate::main_shim;
use crate::mir_to_ir;
use crate::rust_try;
use crate::static_data::collect_alloc_relocs;

/// IR batch optimization, verification, and object-artifact helpers.
mod batch;
/// MIR/IR dump helpers used by backend debugging flags.
mod dump;
/// Symbol remapping helpers for merging per-function translation results.
mod merge;
#[cfg(test)]
mod tests;

use batch::{format_post_opt_module_dump, is_weak_linkage, verify_translation_result};
use merge::merge_translation_result;

/// Opaque payload handed back to rustc between codegen and join.
struct OngoingCodegen {
    /// Object modules compiled during the AOT pipeline.
    compiled_modules: CompiledModules,
}

/// Stateful AOT driver for one rustc codegen invocation.
struct AotCodegen<'tcx> {
    /// rustc type context for the crate being compiled.
    tcx: TyCtxt<'tcx>,
    /// Tuffy machine-code emission session for the target triple.
    session: CodegenSession,
    /// Backend-local options derived from rustc flags.
    config: BackendOptions,
    /// Object modules emitted so far.
    modules: Vec<CompiledModule>,
    /// Symbol names already queued or emitted, used to deduplicate inline shims.
    compiled_symbols: HashSet<String>,
    /// Additional instances discovered during translation that need on-demand codegen.
    pending_instances: Vec<Instance<'tcx>>,
    /// Optional buffer for `dump-module=` output.
    module_ir_text: Option<String>,
    /// Counter used to generate unique static data names.
    data_counter: u64,
}

#[derive(Default)]
/// Shared translation caches reused across functions in one codegen batch.
struct TranslationCaches {
    /// Deduplicates emitted vtables by rustc allocation id.
    vtable_cache: mir_to_ir::VtableCache,
    /// Deduplicates emitted const allocations by rustc allocation id.
    alloc_cache: mir_to_ir::AllocCache,
    /// Deduplicates emitted const allocations by byte content.
    content_cache: mir_to_ir::ContentCache,
}

#[derive(Default)]
/// Accumulates target artifacts for one object file.
struct ObjectArtifacts {
    /// Compiled functions destined for the object file.
    functions: Vec<CompiledFunction>,
    /// Static data records destined for the object file.
    static_data: Vec<StaticData>,
}

/// Per-function metadata that must survive IR batching.
struct PendingFunction {
    /// Whether the compiled function should be emitted with weak linkage.
    weak: bool,
}

/// One batch of IR and static data that is optimized and verified together.
struct IrModuleBatch {
    /// Tuffy IR module under construction.
    module: IrModule,
    /// Per-function metadata kept in module order.
    function_meta: Vec<PendingFunction>,
    /// Target-facing static data emitted alongside the module.
    target_static_data: Vec<StaticData>,
    /// Symbols that must remain weak undefined in the final object.
    weak_undefined_symbols: HashSet<String>,
}

impl IrModuleBatch {
    /// Creates an empty IR batch with the given module name.
    fn new(name: impl Into<String>) -> Self {
        Self {
            module: IrModule::new(name),
            function_meta: Vec::new(),
            target_static_data: Vec::new(),
            weak_undefined_symbols: HashSet::new(),
        }
    }

    /// Returns whether the batch contains no functions or static payloads.
    fn is_empty(&self) -> bool {
        self.module.functions.is_empty()
            && self.target_static_data.is_empty()
            && self.weak_undefined_symbols.is_empty()
    }
}

/// Runs the ahead-of-time codegen pipeline for the current crate.
pub(crate) fn codegen_crate<'tcx>(tcx: TyCtxt<'tcx>, _crate_info: &CrateInfo) -> Box<dyn Any> {
    let config = BackendOptions::from_session(tcx.sess);
    let session = CodegenSession::new(tcx.sess.target.llvm_target.as_ref());
    let compiled_modules = AotCodegen::new(tcx, session, config).run();
    Box::new(OngoingCodegen { compiled_modules })
}

/// Extracts the compiled module list from rustc's opaque codegen payload.
///
/// # Panics
///
/// Panics if `ongoing_codegen` was not produced by [`codegen_crate`].
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
    /// Creates a fresh AOT driver for one rustc session.
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

    /// Lowers every codegen unit in the crate and returns the compiled modules.
    fn run(mut self) -> CompiledModules {
        let cgus = self.tcx.collect_and_partition_mono_items(()).codegen_units;
        for cgu in cgus {
            let cgu_name = cgu.name().to_string();
            let mono_items = cgu.items_in_deterministic_order(self.tcx);

            let mut artifacts = ObjectArtifacts::default();
            let mut ir_batch = IrModuleBatch::new(cgu_name.clone());
            let mut caches = TranslationCaches::default();

            for (mono_item, item_data) in &mono_items {
                match mono_item {
                    MonoItem::Fn(instance) => self.codegen_fn_item(
                        *instance,
                        is_weak_linkage(item_data.linkage),
                        &mut ir_batch,
                        &mut caches,
                    ),
                    MonoItem::Static(def_id) => {
                        self.codegen_static_item(*def_id, &mut artifacts, &mut caches)
                    }
                    MonoItem::GlobalAsm(_) => {}
                }
            }

            self.finish_ir_batch(&mut ir_batch, &mut artifacts);
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

    /// Translates one mono-item function into the current IR batch.
    fn codegen_fn_item(
        &mut self,
        instance: Instance<'tcx>,
        weak: bool,
        batch: &mut IrModuleBatch,
        caches: &mut TranslationCaches,
    ) {
        if Some(instance.def_id()) == self.tcx.lang_items().start_fn() {
            return;
        }
        if !self.should_codegen_instance(instance) {
            return;
        }

        self.compiled_symbols
            .insert(self.tcx.symbol_name(instance).name.to_string());
        self.translate_instance_into_batch(instance, weak, true, batch, caches);
    }

    /// Lowers one static item into target static-data records.
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

    /// Translates one resolved instance and merges its IR into `batch`.
    fn translate_instance_into_batch(
        &mut self,
        instance: Instance<'tcx>,
        weak: bool,
        dump_mir: bool,
        batch: &mut IrModuleBatch,
        caches: &mut TranslationCaches,
    ) {
        if !self.should_codegen_instance(instance) {
            self.fatal_instance(
                instance,
                "internal error: attempted to compile a non-codegenable instance",
            );
        }

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

        let Some(result) = result else {
            self.fatal_instance(
                instance,
                "MIR-to-IR translation unexpectedly skipped a codegenable instance",
            );
        };

        self.pending_instances
            .extend(result.referenced_instances.iter().copied());
        self.append_translation_dump(&result);
        if let Err(err) = verify_translation_result(&result) {
            self.fatal_instance(instance, &err);
        }
        merge_translation_result(batch, result, weak);
    }

    /// Emits any inline shim instances discovered during earlier translation.
    fn codegen_inline_instances(&mut self) {
        let mut artifacts = ObjectArtifacts::default();
        let mut ir_batch = IrModuleBatch::new("inline_shims");
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
                if !self.should_codegen_instance(instance) {
                    continue;
                }
                self.translate_instance_into_batch(
                    instance,
                    true,
                    false,
                    &mut ir_batch,
                    &mut caches,
                );
            }
        }

        self.finish_ir_batch(&mut ir_batch, &mut artifacts);
        if !artifacts.functions.is_empty() {
            self.modules.push(self.emit_module(
                "inline_shims",
                ModuleKind::Regular,
                &artifacts.functions,
                &artifacts.static_data,
            ));
        }
    }

    /// Seeds the dedup set with runtime symbols emitted outside normal MIR lowering.
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

    /// Emits one object file from compiled functions and static data.
    ///
    /// # Panics
    ///
    /// Panics if the backend cannot write the temporary object file.
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
    /// Returns whether this instance has enough MIR and substitutions for codegen.
    fn should_codegen_instance(&self, instance: Instance<'tcx>) -> bool {
        if instance.args.has_non_region_param() {
            return false;
        }
        if let ty::InstanceKind::Intrinsic(def_id) = instance.def
            && self
                .tcx
                .intrinsic(def_id)
                .is_some_and(|intrinsic| intrinsic.must_be_overridden)
        {
            return false;
        }
        if let ty::InstanceKind::Item(def_id) = instance.def
            && !self.tcx.is_mir_available(def_id)
            && !matches!(self.tcx.def_kind(def_id), rustc_hir::def::DefKind::Ctor(..))
        {
            return false;
        }
        true
    }

    /// Aborts compilation with an error tied to a specific instance symbol.
    fn fatal_instance(&self, instance: Instance<'tcx>, message: &str) -> ! {
        let symbol = self.tcx.symbol_name(instance).name;
        self.tcx.dcx().fatal(format!(
            "rustc_codegen_tuffy failed for {symbol}: {message}"
        ));
    }

    /// Aborts compilation with an error tied to an arbitrary symbol name.
    fn fatal_symbol(&self, symbol: &str, message: &str) -> ! {
        self.tcx.dcx().fatal(format!(
            "rustc_codegen_tuffy failed for {symbol}: {message}"
        ));
    }
}
