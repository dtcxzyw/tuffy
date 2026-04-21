use super::*;

/// Merges one function-level translation result into the current module batch.
pub(super) fn merge_translation_result(
    batch: &mut IrModuleBatch,
    mut result: mir_to_ir::TranslationResult<'_>,
    weak: bool,
    local: bool,
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
    batch.function_meta.push(PendingFunction { weak, local });
}

/// Builds a symbol-id remap from a per-function symbol table into `module`.
fn build_symbol_remap(
    source: &tuffy_ir::module::SymbolTable,
    module: &mut IrModule,
) -> Vec<SymbolId> {
    (0..source.len())
        .map(|idx| module.intern(source.resolve(SymbolId(idx as u32))))
        .collect()
}

/// Remaps a symbol id through the batch-level symbol table mapping.
fn remap_symbol_id(symbol: SymbolId, remap: &[SymbolId]) -> SymbolId {
    remap[symbol.0 as usize]
}

/// Rewrites symbol references inside one function to use batch-level symbol ids.
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
