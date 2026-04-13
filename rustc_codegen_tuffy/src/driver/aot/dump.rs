use super::*;

impl<'tcx> AotCodegen<'tcx> {
    /// Prints the MIR body for `instance` when `dump-ir` is enabled.
    pub(super) fn dump_mir(&self, instance: Instance<'tcx>) {
        use rustc_middle::ty::print::with_no_trimmed_paths;

        with_no_trimmed_paths!({
            let mir = self.tcx.instance_mir(instance.def);
            let mut buf = Vec::new();
            let writer = rustc_middle::mir::pretty::MirWriter::new(self.tcx);
            writer.write_mir_fn(mir, &mut buf).unwrap();
            eprint!("{}", String::from_utf8_lossy(&buf));
        });
    }

    /// Appends one translation result to the configured IR dump streams.
    ///
    /// # Panics
    ///
    /// Panics if formatting into the in-memory dump buffer fails.
    pub(super) fn append_translation_dump(&mut self, result: &mir_to_ir::TranslationResult<'tcx>) {
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

    /// Appends the post-optimization module snapshot to the module dump buffer.
    pub(super) fn append_optimized_module_dump(&mut self, batch: &IrModuleBatch) {
        if let Some(buf) = &mut self.module_ir_text {
            buf.push_str(&format_post_opt_module_dump(&batch.module));
        }
    }

    /// Appends one static-data record to the module dump buffer.
    ///
    /// # Panics
    ///
    /// Panics if formatting into the in-memory dump buffer fails.
    pub(super) fn append_static_dump(&mut self, name: &str, data: &[u8], relocs: &[Relocation]) {
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

    /// Writes the accumulated module dump to disk when `dump-module=` was requested.
    ///
    /// # Panics
    ///
    /// Panics if the configured dump path cannot be written.
    pub(super) fn write_module_dump(&self) {
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
