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

struct PendingFunction {
    weak: bool,
}

struct IrModuleBatch {
    module: IrModule,
    function_meta: Vec<PendingFunction>,
    target_static_data: Vec<StaticData>,
    weak_undefined_symbols: HashSet<String>,
}

impl IrModuleBatch {
    fn new(name: impl Into<String>) -> Self {
        Self {
            module: IrModule::new(name),
            function_meta: Vec::new(),
            target_static_data: Vec::new(),
            weak_undefined_symbols: HashSet::new(),
        }
    }

    fn is_empty(&self) -> bool {
        self.module.functions.is_empty()
            && self.target_static_data.is_empty()
            && self.weak_undefined_symbols.is_empty()
    }
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

    fn append_optimized_module_dump(&mut self, batch: &IrModuleBatch) {
        if let Some(buf) = &mut self.module_ir_text {
            buf.push_str(&format_post_opt_module_dump(&batch.module));
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

    fn fatal_instance(&self, instance: Instance<'tcx>, message: &str) -> ! {
        let symbol = self.tcx.symbol_name(instance).name;
        self.tcx.dcx().fatal(format!(
            "rustc_codegen_tuffy failed for {symbol}: {message}"
        ));
    }

    fn fatal_symbol(&self, symbol: &str, message: &str) -> ! {
        self.tcx.dcx().fatal(format!(
            "rustc_codegen_tuffy failed for {symbol}: {message}"
        ));
    }

    fn finish_ir_batch(&mut self, batch: &mut IrModuleBatch, artifacts: &mut ObjectArtifacts) {
        if batch.is_empty() {
            return;
        }

        let module_name = batch.module.name.clone();
        let function_count = batch.module.functions.len();
        let total_inst_count = batch
            .module
            .functions
            .iter()
            .map(|func| func.inst_pool.iter_insts().count())
            .sum::<usize>();

        let optimize_start = Instant::now();
        if let Err(err) = optimize_ir_batch(batch, self.config.run_tuffy_opt) {
            self.fatal_symbol(&batch.module.name, &err);
        }
        let optimize_elapsed = optimize_start.elapsed();
        if self.config.run_tuffy_opt {
            self.append_optimized_module_dump(batch);
        }
        let verify_start = Instant::now();
        if let Err(err) = verify_ir_batch(batch, "IR verification failed") {
            self.fatal_symbol(&batch.module.name, &err);
        }
        let verify_elapsed = verify_start.elapsed();

        if self.config.trace_timings {
            eprintln!(
                "[tuffy-timing] module={module_name} phase=optimize functions={function_count} insts={total_inst_count} elapsed_ms={}",
                optimize_elapsed.as_millis()
            );
            eprintln!(
                "[tuffy-timing] module={module_name} phase=verify elapsed_ms={}",
                verify_elapsed.as_millis()
            );
        }

        append_ir_batch_static_data(&mut artifacts.static_data, batch);

        let functions = &batch.module.functions;
        let symbols = &mut batch.module.symbols;
        for (idx, meta) in batch.function_meta.iter().enumerate() {
            let func = &functions[idx];
            let func_name = symbols.resolve(func.name).to_string();
            let codegen_func = self.config.strip_debug_for_codegen(func);
            let compile_start = Instant::now();
            let compiled = self
                .session
                .compile_function(&codegen_func, symbols)
                .unwrap_or_else(|err| self.fatal_symbol(&func_name, &err));
            if self.config.trace_timings {
                let inst_count = func.inst_pool.iter_insts().count();
                eprintln!(
                    "[tuffy-timing] module={module_name} function={func_name} phase=codegen insts={inst_count} elapsed_ms={}",
                    compile_start.elapsed().as_millis()
                );
            }
            artifacts.functions.push(CompiledFunction {
                weak: meta.weak,
                ..compiled
            });
        }
    }
}

fn verify_translation_result(result: &mir_to_ir::TranslationResult<'_>) -> Result<(), String> {
    let verification = tuffy_ir::verifier::verify_function(&result.func, &result.symbols);
    if !verification.is_ok() {
        let func_name = result.symbols.resolve(result.func.name);
        return Err(format!(
            "IR verification failed for {func_name}: {verification}"
        ));
    }
    Ok(())
}

fn optimize_ir_batch(
    batch: &mut IrModuleBatch,
    enabled: bool,
) -> Result<Option<PeepholeStats>, String> {
    if !enabled {
        return Ok(None);
    }

    let stats = tuffy_opt::optimize_module(&mut batch.module);
    verify_ir_batch(batch, "optimized IR verification failed")?;
    Ok(Some(stats))
}

fn verify_ir_batch(batch: &IrModuleBatch, context: &str) -> Result<(), String> {
    let verification = tuffy_ir::verifier::verify_module(&batch.module);
    if !verification.is_ok() {
        return Err(format!(
            "{context} for module {}: {verification}",
            batch.module.name
        ));
    }
    Ok(())
}

fn merge_translation_result(
    batch: &mut IrModuleBatch,
    mut result: mir_to_ir::TranslationResult<'_>,
    weak: bool,
) {
    let symbol_remap = build_symbol_remap(&result.symbols, &mut batch.module);
    remap_function_symbols(&mut result.func, &symbol_remap);
    batch.module.functions.push(result.func);

    for (name, data, relocs, _align) in &result.static_data {
        let remapped_relocs = relocs
            .iter()
            .map(|(offset, symbol)| StaticRelocation {
                offset: *offset,
                symbol: batch.module.intern(symbol),
            })
            .collect();
        batch.module.static_data.push(IrStaticData {
            name: remap_symbol_id(*name, &symbol_remap),
            data: data.clone(),
            relocations: remapped_relocs,
        });
    }

    for (name, data, relocs, align) in result.static_data {
        let remapped_name = remap_symbol_id(name, &symbol_remap);
        batch.target_static_data.push(StaticData {
            name: batch.module.resolve(remapped_name).to_string(),
            data,
            relocations: relocs
                .into_iter()
                .map(|(offset, symbol)| Relocation {
                    offset,
                    symbol,
                    kind: RelocKind::Abs64,
                })
                .collect(),
            writable: false,
            used: false,
            weak_undefined: false,
            align,
            thread_local: false,
        });
    }

    batch
        .weak_undefined_symbols
        .extend(result.weak_undefined_symbols.drain());
    batch.function_meta.push(PendingFunction { weak });
}

fn build_symbol_remap(
    source: &tuffy_ir::module::SymbolTable,
    module: &mut IrModule,
) -> Vec<SymbolId> {
    (0..source.len())
        .map(|idx| module.intern(source.resolve(SymbolId(idx as u32))))
        .collect()
}

fn remap_symbol_id(symbol: SymbolId, remap: &[SymbolId]) -> SymbolId {
    remap[symbol.0 as usize]
}

fn remap_function_symbols(func: &mut tuffy_ir::function::Function, remap: &[SymbolId]) {
    func.name = remap_symbol_id(func.name, remap);
    for symbol in func.param_names.iter_mut().flatten() {
        *symbol = remap_symbol_id(*symbol, remap);
    }
    for node in func.inst_pool.iter_mut() {
        match &mut node.inst.op {
            Op::SymbolAddr(symbol) | Op::TlsSymbolAddr(symbol) => {
                *symbol = remap_symbol_id(*symbol, remap);
            }
            _ => {}
        }
    }
}

fn append_ir_batch_static_data(all_static_data: &mut Vec<StaticData>, batch: &IrModuleBatch) {
    let mut weak_undefined_symbols = batch
        .weak_undefined_symbols
        .iter()
        .cloned()
        .collect::<Vec<_>>();
    weak_undefined_symbols.sort();
    for sym in weak_undefined_symbols {
        all_static_data.push(StaticData {
            name: sym,
            data: vec![],
            relocations: vec![],
            writable: false,
            used: false,
            weak_undefined: true,
            align: 1,
            thread_local: false,
        });
    }

    for sd in &batch.target_static_data {
        all_static_data.push(StaticData {
            name: sd.name.clone(),
            data: sd.data.clone(),
            relocations: sd
                .relocations
                .iter()
                .map(|reloc| Relocation {
                    offset: reloc.offset,
                    symbol: reloc.symbol.clone(),
                    kind: reloc.kind,
                })
                .collect(),
            writable: sd.writable,
            used: sd.used,
            weak_undefined: sd.weak_undefined,
            align: sd.align,
            thread_local: sd.thread_local,
        });
    }
}

fn format_post_opt_module_dump(module: &IrModule) -> String {
    format!("; post-opt module {}\n{}\n\n", module.name, module)
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

#[cfg(test)]
mod tests {
    use super::{
        IrModuleBatch, format_post_opt_module_dump, merge_translation_result, optimize_ir_batch,
        verify_ir_batch,
    };
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
            merge_translation_result(&mut batch, result, false);
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
        merge_translation_result(&mut batch, result, true);

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
}
