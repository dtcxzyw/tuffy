//! ELF object file emission using the `object` crate.

use std::collections::HashMap;

use object::write::{Object, Relocation as ObjRelocation, Symbol, SymbolId, SymbolSection};
use object::{
    Architecture, BinaryFormat, Endianness, RelocationEncoding, RelocationFlags, RelocationKind,
    SymbolFlags, SymbolKind, SymbolScope,
};

use tuffy_target::reloc::{RelocKind, Relocation};
pub use tuffy_target::types::{CompiledFunction, StaticData};

/// Emit a single function as an ELF object file.
pub fn emit_elf(name: &str, code: &[u8], relocations: &[Relocation]) -> Vec<u8> {
    emit_elf_multi(&[CompiledFunction {
        name: name.to_string(),
        code: code.to_vec(),
        relocations: relocations.to_vec(),
    }])
}

/// Emit multiple functions as a single ELF object file.
pub fn emit_elf_multi(functions: &[CompiledFunction]) -> Vec<u8> {
    emit_elf_with_data(functions, &[])
}

/// Emit multiple functions and static data as a single ELF object file.
pub fn emit_elf_with_data(functions: &[CompiledFunction], statics: &[StaticData]) -> Vec<u8> {
    let mut obj = Object::new(BinaryFormat::Elf, Architecture::X86_64, Endianness::Little);
    let text = obj.section_id(object::write::StandardSection::Text);

    // Track symbol name → SymbolId so relocations can reference local data
    // symbols defined in this same object file.
    let mut sym_map: HashMap<String, SymbolId> = HashMap::new();

    // Emit static data: plain data in .rodata, data with relocations in .data.rel.ro.
    if !statics.is_empty() {
        let rodata = obj.section_id(object::write::StandardSection::ReadOnlyData);
        let data_rel_ro = obj.section_id(object::write::StandardSection::ReadOnlyDataWithRel);
        for sd in statics {
            let section = if sd.relocations.is_empty() {
                rodata
            } else {
                data_rel_ro
            };
            let offset = obj.append_section_data(section, &sd.data, 8);
            // .L-prefixed symbols are file-local data blobs — use STB_LOCAL
            // so they don't collide with identically-named symbols in other
            // object files (e.g. across crate boundaries).
            let scope = if sd.name.starts_with(".L") {
                SymbolScope::Compilation
            } else {
                SymbolScope::Linkage
            };
            let sid = obj.add_symbol(Symbol {
                name: sd.name.as_bytes().to_vec(),
                value: offset,
                size: sd.data.len() as u64,
                kind: SymbolKind::Data,
                scope,
                weak: false,
                section: SymbolSection::Section(section),
                flags: SymbolFlags::None,
            });
            sym_map.insert(sd.name.clone(), sid);

            // Add relocations for function pointers within static data (e.g. vtables).
            for reloc in &sd.relocations {
                let target_sid = if let Some(&existing) = sym_map.get(&reloc.symbol) {
                    existing
                } else {
                    let s = obj.add_symbol(Symbol {
                        name: reloc.symbol.as_bytes().to_vec(),
                        value: 0,
                        size: 0,
                        kind: SymbolKind::Text,
                        scope: SymbolScope::Unknown,
                        weak: false,
                        section: SymbolSection::Undefined,
                        flags: SymbolFlags::None,
                    });
                    sym_map.insert(reloc.symbol.clone(), s);
                    s
                };
                let (reloc_kind, reloc_encoding, reloc_size, addend) = match reloc.kind {
                    RelocKind::Abs64 => {
                        (RelocationKind::Absolute, RelocationEncoding::Generic, 64, 0)
                    }
                    RelocKind::Call => (
                        RelocationKind::PltRelative,
                        RelocationEncoding::X86Branch,
                        32,
                        -4,
                    ),
                    RelocKind::PcRel => (
                        RelocationKind::Relative,
                        RelocationEncoding::Generic,
                        32,
                        -4,
                    ),
                };
                obj.add_relocation(
                    section,
                    ObjRelocation {
                        offset: offset + reloc.offset as u64,
                        symbol: target_sid,
                        addend,
                        flags: RelocationFlags::Generic {
                            kind: reloc_kind,
                            encoding: reloc_encoding,
                            size: reloc_size,
                        },
                    },
                )
                .expect("failed to add static data relocation");
            }
        }
    }

    for func in functions {
        let code_offset = obj.append_section_data(text, &func.code, 16);

        let func_sid = obj.add_symbol(Symbol {
            name: func.name.as_bytes().to_vec(),
            value: code_offset,
            size: func.code.len() as u64,
            kind: SymbolKind::Text,
            scope: SymbolScope::Linkage,
            weak: false,
            section: SymbolSection::Section(text),
            flags: SymbolFlags::None,
        });
        sym_map.insert(func.name.clone(), func_sid);

        for reloc in &func.relocations {
            // Reuse the symbol ID if the target is already defined in this
            // object file (e.g. a .Lconst or .Lstr data blob, or another
            // function). Otherwise create an undefined external reference.
            let sym_id = if let Some(&existing) = sym_map.get(&reloc.symbol) {
                existing
            } else {
                let sid = obj.add_symbol(Symbol {
                    name: reloc.symbol.as_bytes().to_vec(),
                    value: 0,
                    size: 0,
                    kind: SymbolKind::Text,
                    scope: SymbolScope::Unknown,
                    weak: false,
                    section: SymbolSection::Undefined,
                    flags: SymbolFlags::None,
                });
                sym_map.insert(reloc.symbol.clone(), sid);
                sid
            };

            let (reloc_kind, reloc_encoding, reloc_size, addend) = match reloc.kind {
                RelocKind::Call => (
                    RelocationKind::PltRelative,
                    RelocationEncoding::X86Branch,
                    32,
                    -4,
                ),
                RelocKind::PcRel => (
                    RelocationKind::Relative,
                    RelocationEncoding::Generic,
                    32,
                    -4,
                ),
                RelocKind::Abs64 => (RelocationKind::Absolute, RelocationEncoding::Generic, 64, 0),
            };
            obj.add_relocation(
                text,
                ObjRelocation {
                    offset: code_offset + reloc.offset as u64,
                    symbol: sym_id,
                    addend,
                    flags: RelocationFlags::Generic {
                        kind: reloc_kind,
                        encoding: reloc_encoding,
                        size: reloc_size,
                    },
                },
            )
            .expect("failed to add relocation");
        }
    }

    let mut buf = Vec::new();
    obj.emit(&mut buf).expect("failed to emit ELF object");
    buf
}
