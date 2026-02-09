//! ELF object file emission using the `object` crate.

use object::write::{Object, Relocation as ObjRelocation, Symbol, SymbolSection};
use object::{
    Architecture, BinaryFormat, Endianness, RelocationEncoding, RelocationFlags, RelocationKind,
    SymbolFlags, SymbolKind, SymbolScope,
};

use crate::encode::{RelocKind, Relocation};

/// A compiled function ready for ELF emission.
pub struct CompiledFunction {
    pub name: String,
    pub code: Vec<u8>,
    pub relocations: Vec<Relocation>,
}

/// A static data blob to be placed in .rodata.
pub struct StaticData {
    pub name: String,
    pub data: Vec<u8>,
}

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

    // Emit static data in .rodata section.
    if !statics.is_empty() {
        let rodata = obj.section_id(object::write::StandardSection::ReadOnlyData);
        for sd in statics {
            let offset = obj.append_section_data(rodata, &sd.data, 1);
            obj.add_symbol(Symbol {
                name: sd.name.as_bytes().to_vec(),
                value: offset,
                size: sd.data.len() as u64,
                kind: SymbolKind::Data,
                scope: SymbolScope::Linkage,
                weak: false,
                section: SymbolSection::Section(rodata),
                flags: SymbolFlags::None,
            });
        }
    }

    for func in functions {
        let code_offset = obj.append_section_data(text, &func.code, 16);

        obj.add_symbol(Symbol {
            name: func.name.as_bytes().to_vec(),
            value: code_offset,
            size: func.code.len() as u64,
            kind: SymbolKind::Text,
            scope: SymbolScope::Dynamic,
            weak: false,
            section: SymbolSection::Section(text),
            flags: SymbolFlags::None,
        });

        for reloc in &func.relocations {
            let sym_id = obj.add_symbol(Symbol {
                name: reloc.symbol.as_bytes().to_vec(),
                value: 0,
                size: 0,
                kind: SymbolKind::Text,
                scope: SymbolScope::Unknown,
                weak: false,
                section: SymbolSection::Undefined,
                flags: SymbolFlags::None,
            });

            let (reloc_kind, reloc_encoding) = match reloc.kind {
                RelocKind::Call => (RelocationKind::PltRelative, RelocationEncoding::X86Branch),
                RelocKind::PcRel => (RelocationKind::Relative, RelocationEncoding::Generic),
            };
            obj.add_relocation(
                text,
                ObjRelocation {
                    offset: code_offset + reloc.offset as u64,
                    symbol: sym_id,
                    addend: -4,
                    flags: RelocationFlags::Generic {
                        kind: reloc_kind,
                        encoding: reloc_encoding,
                        size: 32,
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
