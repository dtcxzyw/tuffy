use super::*;

impl<'tcx> AotCodegen<'tcx> {
    /// Optimizes, verifies, and machine-code compiles the current IR batch.
    pub(super) fn finish_ir_batch(
        &mut self,
        batch: &mut IrModuleBatch,
        artifacts: &mut ObjectArtifacts,
    ) {
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
            self.write_module_dump();
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

/// Verifies a freshly translated function before it is merged into a module batch.
///
/// # Errors
///
/// Returns an error string when the translated function fails Tuffy IR verification.
pub(super) fn verify_translation_result(
    result: &mir_to_ir::TranslationResult<'_>,
) -> Result<(), String> {
    let verification = tuffy_ir::verifier::verify_function(&result.func, &result.symbols);
    if !verification.is_ok() {
        let func_name = result.symbols.resolve(result.func.name);
        return Err(format!(
            "IR verification failed for {func_name}: {verification}"
        ));
    }
    Ok(())
}

/// Runs `tuffy_opt` on `batch` when enabled and re-verifies the optimized IR.
///
/// # Errors
///
/// Returns an error string if optimization leaves the batch in an invalid IR state.
pub(super) fn optimize_ir_batch(
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

/// Verifies a whole IR batch and annotates failures with the provided context.
///
/// # Errors
///
/// Returns an error string when module verification fails.
pub(super) fn verify_ir_batch(batch: &IrModuleBatch, context: &str) -> Result<(), String> {
    let verification = tuffy_ir::verifier::verify_module(&batch.module);
    if !verification.is_ok() {
        return Err(format!(
            "{context} for module {}: {verification}",
            batch.module.name
        ));
    }
    Ok(())
}

/// Appends weak undefined and translated static data from `batch` into the object payload list.
pub(super) fn append_ir_batch_static_data(
    all_static_data: &mut Vec<StaticData>,
    batch: &IrModuleBatch,
) {
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

/// Formats the post-optimization snapshot appended to `dump-module=` output.
pub(super) fn format_post_opt_module_dump(module: &IrModule) -> String {
    format!("; post-opt module {}\n{}\n\n", module.name, module)
}

/// Returns whether rustc linkage should be treated as weak by the backend.
pub(super) fn is_weak_linkage(linkage: Linkage) -> bool {
    matches!(
        linkage,
        Linkage::LinkOnceODR | Linkage::WeakODR | Linkage::LinkOnceAny | Linkage::WeakAny
    )
}
