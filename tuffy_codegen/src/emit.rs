//! ELF object file emission using the `object` crate.

use object::write::{Object, Relocation as ObjRelocation, Symbol, SymbolSection};
use object::{
    Architecture, BinaryFormat, Endianness, RelocationEncoding, RelocationFlags, RelocationKind,
    SymbolFlags, SymbolKind, SymbolScope,
};

use crate::encode::Relocation;

/// A compiled function ready for ELF emission.
pub struct CompiledFunction {
    pub name: String,
    pub code: Vec<u8>,
    pub relocations: Vec<Relocation>,
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
    let mut obj = Object::new(BinaryFormat::Elf, Architecture::X86_64, Endianness::Little);
    let text = obj.section_id(object::write::StandardSection::Text);

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

            obj.add_relocation(
                text,
                ObjRelocation {
                    offset: code_offset + reloc.offset as u64,
                    symbol: sym_id,
                    addend: -4,
                    flags: RelocationFlags::Generic {
                        kind: RelocationKind::PltRelative,
                        encoding: RelocationEncoding::X86Branch,
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
