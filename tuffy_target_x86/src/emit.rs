//! ELF object file emission using the `object` crate.

use std::collections::HashMap;
use std::path::Path;

use gimli::write::{
    Address, AttributeValue, Dwarf, EndianVec, Expression, LineProgram, LineString, Location,
    LocationList, RelocateWriter, Relocation as DwarfRelocation,
    RelocationTarget as DwarfRelocationTarget, Sections,
};
use gimli::{Encoding, Format, LineEncoding, Register, SectionId as DwarfSectionId};
use object::write::{
    Comdat, Object, Relocation as ObjRelocation, SectionId, Symbol, SymbolId, SymbolSection,
};
use object::{
    Architecture, BinaryFormat, ComdatKind, Endianness, RelocationEncoding, RelocationFlags,
    RelocationKind, SectionFlags, SectionKind, SymbolFlags, SymbolKind, SymbolScope,
};

use tuffy_target::reloc::{RelocKind, Relocation};
pub use tuffy_target::types::{
    CompiledDebugInfo, CompiledFunction, DebugLocation, DebugVariableRange, StaticData,
};

/// Emit a single function as an ELF object file.
pub fn emit_elf(name: &str, code: &[u8], relocations: &[Relocation]) -> Vec<u8> {
    emit_elf_multi(&[CompiledFunction {
        name: name.to_string(),
        code: code.to_vec(),
        relocations: relocations.to_vec(),
        debug: None,
        weak: false,
        local: false,
        has_frame_pointer: false,
        call_site_table: vec![],
        callee_saved_dwarf_regs: vec![],
        sub_amount: 0,
    }])
}

/// Emit multiple functions as a single ELF object file.
pub fn emit_elf_multi(functions: &[CompiledFunction]) -> Vec<u8> {
    emit_elf_with_data(functions, &[])
}

// ELF section flags needed for COMDAT group member sections.
/// ELF `SHF_ALLOC`.
const SHF_ALLOC: u64 = 0x2;
/// ELF `SHF_EXECINSTR`.
const SHF_EXECINSTR: u64 = 0x4;
/// ELF `SHF_GROUP`.
const SHF_GROUP: u64 = 0x200;

/// Override a section's ELF flags. Used to set SHF_GROUP on COMDAT member
/// sections, which the `object` crate does not do automatically.
fn set_shf_group(obj: &mut Object, section: SectionId, flags: u64) {
    obj.section_mut(section).flags = SectionFlags::Elf { sh_flags: flags };
}

/// Emit multiple functions and static data as a single ELF object file.
///
/// # Panics
///
/// Panics if object-file or DWARF emission encounters internally inconsistent
/// relocation or debug data.
pub fn emit_elf_with_data(functions: &[CompiledFunction], statics: &[StaticData]) -> Vec<u8> {
    let mut obj = Object::new(BinaryFormat::Elf, Architecture::X86_64, Endianness::Little);
    let text = obj.section_id(object::write::StandardSection::Text);

    // Track symbol name → SymbolId so relocations can reference local data
    // symbols defined in this same object file.
    let mut sym_map: HashMap<String, SymbolId> = HashMap::new();

    // Emit static data into appropriate sections based on mutability and relocations.
    if !statics.is_empty() {
        let rodata = obj.section_id(object::write::StandardSection::ReadOnlyData);
        let data_rel_ro = obj.section_id(object::write::StandardSection::ReadOnlyDataWithRel);
        let data_rw = obj.section_id(object::write::StandardSection::Data);
        for sd in statics {
            // Weak undefined symbols (e.g. `#[linkage = "extern_weak"]`) have
            // no data and no section — just a weak undefined ELF symbol.
            if sd.weak_undefined {
                let sid = obj.add_symbol(Symbol {
                    name: sd.name.as_bytes().to_vec(),
                    value: 0,
                    size: 0,
                    kind: SymbolKind::Data,
                    scope: SymbolScope::Unknown,
                    weak: true,
                    section: SymbolSection::Undefined,
                    flags: SymbolFlags::None,
                });
                sym_map.insert(sd.name.clone(), sid);
                continue;
            }
            let section = if sd.thread_local {
                // Thread-local statics go in .tdata (SHF_TLS | SHF_WRITE | SHF_ALLOC).
                obj.section_id(object::write::StandardSection::Tls)
            } else if sd.used {
                // #[used] statics must survive linker GC (e.g. proc_macro_decls).
                // Place in a per-symbol section with SHF_GNU_RETAIN so --gc-sections
                // keeps it even without incoming references.
                let sec_name = if sd.writable {
                    format!(".data.{}", sd.name)
                } else if sd.relocations.is_empty() {
                    format!(".rodata.{}", sd.name)
                } else {
                    format!(".data.rel.ro.{}", sd.name)
                };
                let kind = if sd.writable {
                    SectionKind::Data
                } else if sd.relocations.is_empty() {
                    SectionKind::ReadOnlyData
                } else {
                    SectionKind::ReadOnlyDataWithRel
                };
                let sec_id = obj.add_section(vec![], sec_name.into_bytes(), kind);
                // SHF_GNU_RETAIN = 0x00200000 prevents linker GC.
                // We must also set the proper ELF base flags (SHF_ALLOC, SHF_WRITE)
                // because overriding SectionFlags::Elf replaces the kind-derived defaults.
                let shf_alloc: u64 = 0x2;
                let shf_write: u64 = 0x1;
                let shf_gnu_retain: u64 = 0x0020_0000;
                let base = if sd.writable || !sd.relocations.is_empty() {
                    shf_alloc | shf_write
                } else {
                    shf_alloc
                };
                obj.section_mut(sec_id).flags = SectionFlags::Elf {
                    sh_flags: base | shf_gnu_retain,
                };
                sec_id
            } else if sd.writable {
                data_rw
            } else if sd.relocations.is_empty() {
                rodata
            } else {
                data_rel_ro
            };
            let offset = obj.append_section_data(section, &sd.data, sd.align.max(1));

            let scope = if sd.name.starts_with(".L") {
                SymbolScope::Compilation
            } else if sd.used {
                // #[used] statics (e.g. proc_macro_decls) must be visible in the
                // dynamic symbol table so dlsym can find them in proc-macro .so files.
                SymbolScope::Dynamic
            } else {
                SymbolScope::Linkage
            };
            let sid = obj.add_symbol(Symbol {
                name: sd.name.as_bytes().to_vec(),
                value: offset,
                size: sd.data.len() as u64,
                kind: if sd.thread_local {
                    SymbolKind::Tls
                } else {
                    SymbolKind::Data
                },
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
                let flags = match reloc.kind {
                    RelocKind::Abs64 => RelocationFlags::Generic {
                        kind: RelocationKind::Absolute,
                        encoding: RelocationEncoding::Generic,
                        size: 64,
                    },
                    RelocKind::Call => RelocationFlags::Generic {
                        kind: RelocationKind::PltRelative,
                        encoding: RelocationEncoding::X86Branch,
                        size: 32,
                    },
                    RelocKind::PcRel => RelocationFlags::Generic {
                        kind: RelocationKind::Relative,
                        encoding: RelocationEncoding::Generic,
                        size: 32,
                    },
                    RelocKind::TlsGotTpOff => RelocationFlags::Elf {
                        r_type: object::elf::R_X86_64_GOTTPOFF,
                    },
                };
                let addend = match reloc.kind {
                    RelocKind::Abs64 => {
                        // Read existing bytes at reloc site as the addend.
                        // CTFE stores the byte offset within the target allocation
                        // in the pointer bytes; RELA format ignores the bytes and
                        // uses only S+A, so we must capture the offset here.
                        let off = reloc.offset;
                        if off + 8 <= sd.data.len() {
                            i64::from_le_bytes(sd.data[off..off + 8].try_into().unwrap())
                        } else {
                            0
                        }
                    }
                    _ => -4,
                };
                obj.add_relocation(
                    section,
                    ObjRelocation {
                        offset: offset + reloc.offset as u64,
                        symbol: target_sid,
                        addend,
                        flags,
                    },
                )
                .expect("failed to add static data relocation");
            }
        }
    }

    // Pass 1: Emit all function code and create symbols. This must happen
    // before processing relocations so that local (STB_LOCAL) symbols are
    // already in sym_map when another function in the same object file
    // references them.
    //
    // Weak functions (generic/monomorphized) get their own `.text.func_name`
    // section so they can be placed in COMDAT groups. This lets the linker
    // discard duplicate copies along with their FDEs and LSDAs, preventing
    // overlapping .eh_frame entries that confuse the unwinder.
    let mut code_offsets: Vec<u64> = Vec::with_capacity(functions.len());
    let mut func_text_sections: Vec<SectionId> = Vec::with_capacity(functions.len());
    for func in functions {
        let section = if func.weak {
            let sec_name = format!(".text.{}", func.name);
            let sid = obj.add_section(vec![], sec_name.into_bytes(), SectionKind::Text);
            // SHF_GROUP is required by the ELF spec for COMDAT member sections
            // but the `object` crate doesn't set it automatically.
            set_shf_group(&mut obj, sid, SHF_ALLOC | SHF_EXECINSTR | SHF_GROUP);
            sid
        } else {
            text
        };
        let code_offset = obj.append_section_data(section, &func.code, 16);
        code_offsets.push(code_offset);
        func_text_sections.push(section);

        let func_sid = obj.add_symbol(Symbol {
            name: func.name.as_bytes().to_vec(),
            value: code_offset,
            size: func.code.len() as u64,
            kind: SymbolKind::Text,
            scope: if func.local {
                SymbolScope::Compilation
            } else {
                SymbolScope::Linkage
            },
            weak: func.weak,
            section: SymbolSection::Section(section),
            flags: SymbolFlags::None,
        });
        sym_map.insert(func.name.clone(), func_sid);
    }

    // Pass 2: Add relocations now that all symbols are defined.
    for (i, (func, &code_offset)) in functions.iter().zip(code_offsets.iter()).enumerate() {
        let section = func_text_sections[i];
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

            let flags = match reloc.kind {
                RelocKind::Call => RelocationFlags::Generic {
                    kind: RelocationKind::PltRelative,
                    encoding: RelocationEncoding::X86Branch,
                    size: 32,
                },
                RelocKind::PcRel => RelocationFlags::Generic {
                    kind: RelocationKind::Relative,
                    encoding: RelocationEncoding::Generic,
                    size: 32,
                },
                RelocKind::Abs64 => RelocationFlags::Generic {
                    kind: RelocationKind::Absolute,
                    encoding: RelocationEncoding::Generic,
                    size: 64,
                },
                RelocKind::TlsGotTpOff => RelocationFlags::Elf {
                    r_type: object::elf::R_X86_64_GOTTPOFF,
                },
            };
            let addend = match reloc.kind {
                RelocKind::Abs64 => 0,
                _ => -4,
            };
            obj.add_relocation(
                section,
                ObjRelocation {
                    offset: code_offset + reloc.offset as u64,
                    symbol: sym_id,
                    addend,
                    flags,
                },
            )
            .expect("failed to add relocation");
        }
    }

    emit_dwarf(&mut obj, functions, &sym_map);

    // Generate .eh_frame unwind information so that libunwind can traverse
    // tuffy-compiled frames (required for panic unwinding / catch_unwind).
    emit_eh_frame(
        &mut obj,
        functions,
        &mut sym_map,
        &func_text_sections,
        &code_offsets,
    );

    let mut buf = Vec::new();
    obj.emit(&mut buf).expect("failed to emit ELF object");
    buf
}

#[derive(Debug, Clone)]
/// Writable DWARF section plus its pending relocations.
struct DwarfSectionWriter {
    /// Encoded DWARF bytes.
    writer: EndianVec<gimli::LittleEndian>,
    /// Relocations targeting this DWARF section.
    relocations: Vec<DwarfRelocation>,
}

impl DwarfSectionWriter {
    /// Borrow the encoded bytes accumulated for this section.
    fn slice(&self) -> &[u8] {
        self.writer.slice()
    }
}

impl Default for DwarfSectionWriter {
    fn default() -> Self {
        Self {
            writer: EndianVec::new(gimli::LittleEndian),
            relocations: Vec::new(),
        }
    }
}

impl RelocateWriter for DwarfSectionWriter {
    type Writer = EndianVec<gimli::LittleEndian>;

    fn writer(&self) -> &Self::Writer {
        &self.writer
    }

    fn writer_mut(&mut self) -> &mut Self::Writer {
        &mut self.writer
    }

    fn relocate(&mut self, relocation: DwarfRelocation) {
        self.relocations.push(relocation);
    }
}

/// Split a source path into directory and file name components for DWARF.
fn split_source_path(path: &str) -> (String, String) {
    let source_path = Path::new(path);
    let file = source_path
        .file_name()
        .map(|name| name.to_string_lossy().into_owned())
        .unwrap_or_else(|| path.to_string());
    let dir = source_path
        .parent()
        .map(|parent| parent.to_string_lossy().into_owned())
        .filter(|parent| !parent.is_empty())
        .unwrap_or_else(|| ".".to_string());
    (dir, file)
}

/// Build a DWARF expression describing one variable location.
fn debug_expr(location: &DebugLocation) -> Expression {
    let mut expr = Expression::new();
    match location {
        DebugLocation::Register(reg) => expr.op_reg(Register(*reg)),
        DebugLocation::FrameOffset(offset) => expr.op_fbreg(i64::from(*offset)),
    }
    expr
}

/// Build a DWARF location list for one variable that moves across machine ranges.
fn debug_location_list(symbol_index: usize, ranges: &[DebugVariableRange]) -> Option<LocationList> {
    let mut locations = Vec::new();
    for range in ranges {
        if range.start >= range.end {
            continue;
        }
        locations.push(Location::StartLength {
            begin: Address::Symbol {
                symbol: symbol_index,
                addend: i64::from(range.start),
            },
            length: u64::from(range.end - range.start),
            data: debug_expr(&range.location),
        });
    }
    (!locations.is_empty()).then_some(LocationList(locations))
}

/// Build the DWARF frame-base expression used for stack-relative locations.
fn frame_base_expr() -> Expression {
    let mut expr = Expression::new();
    expr.op(gimli::DW_OP_call_frame_cfa);
    expr
}

/// Ensure that a source file is present in the line program and return its id.
fn ensure_file_id(
    program: &mut LineProgram,
    file_ids: &mut HashMap<String, gimli::write::FileId>,
    working_dir: &str,
    path: &str,
) -> gimli::write::FileId {
    if let Some(&file_id) = file_ids.get(path) {
        return file_id;
    }

    let file_path = Path::new(path);
    let file_name = file_path
        .file_name()
        .map(|name| name.to_string_lossy().into_owned())
        .unwrap_or_else(|| path.to_string());
    let directory = file_path
        .parent()
        .map(|parent| parent.to_string_lossy().into_owned())
        .filter(|parent| !parent.is_empty())
        .unwrap_or_else(|| working_dir.to_string());
    let dir_id = if directory == working_dir {
        program.default_directory()
    } else {
        program.add_directory(LineString::String(directory.as_bytes().to_vec()))
    };
    let file_id = program.add_file(
        LineString::String(file_name.as_bytes().to_vec()),
        dir_id,
        None,
    );
    file_ids.insert(path.to_string(), file_id);
    file_id
}

/// Build a DWARF compilation unit for one compiled function.
fn build_dwarf_unit(
    encoding: Encoding,
    line_encoding: LineEncoding,
    func: &CompiledFunction,
    debug: &CompiledDebugInfo,
    symbol_index: usize,
) -> Option<gimli::write::Unit> {
    let declaration = debug.function.declaration.as_ref().or_else(|| {
        debug
            .function
            .sources
            .first()
            .map(|source| &source.location)
    })?;
    let (working_dir, source_file) = split_source_path(&declaration.file);
    let mut program = LineProgram::new(
        encoding,
        line_encoding,
        LineString::String(working_dir.as_bytes().to_vec()),
        None,
        LineString::String(source_file.as_bytes().to_vec()),
        None,
    );
    let mut file_ids = HashMap::new();
    let decl_file_id = ensure_file_id(&mut program, &mut file_ids, &working_dir, &declaration.file);

    program.begin_sequence(Some(Address::Symbol {
        symbol: symbol_index,
        addend: 0,
    }));
    let mut marked_prologue_end = false;
    for line in &debug.lines {
        let Some(source) = debug.function.sources.get(line.source as usize) else {
            continue;
        };
        let file_id = ensure_file_id(
            &mut program,
            &mut file_ids,
            &working_dir,
            &source.location.file,
        );
        let row = program.row();
        row.address_offset = u64::from(line.offset);
        row.file = file_id;
        row.line = u64::from(source.location.line);
        row.column = u64::from(source.location.column);
        if !marked_prologue_end {
            row.prologue_end = true;
            marked_prologue_end = true;
        }
        program.generate_row();
    }
    program.end_sequence(func.code.len() as u64);

    let mut unit = gimli::write::Unit::new(encoding, program);
    let root = unit.root();
    {
        let root_entry = unit.get_mut(root);
        root_entry.set(
            gimli::DW_AT_name,
            AttributeValue::String(source_file.as_bytes().to_vec()),
        );
        root_entry.set(
            gimli::DW_AT_comp_dir,
            AttributeValue::String(working_dir.as_bytes().to_vec()),
        );
        root_entry.set(
            gimli::DW_AT_producer,
            AttributeValue::String(b"rustc_codegen_tuffy".to_vec()),
        );
        root_entry.set(
            gimli::DW_AT_language,
            AttributeValue::Language(gimli::DW_LANG_Rust),
        );
        root_entry.set(
            gimli::DW_AT_low_pc,
            AttributeValue::Address(Address::Symbol {
                symbol: symbol_index,
                addend: 0,
            }),
        );
        root_entry.set(
            gimli::DW_AT_high_pc,
            AttributeValue::Udata(func.code.len() as u64),
        );
    }

    let subprogram = unit.add(root, gimli::DW_TAG_subprogram);
    {
        let entry = unit.get_mut(subprogram);
        entry.set(
            gimli::DW_AT_name,
            AttributeValue::String(func.name.as_bytes().to_vec()),
        );
        entry.set(
            gimli::DW_AT_low_pc,
            AttributeValue::Address(Address::Symbol {
                symbol: symbol_index,
                addend: 0,
            }),
        );
        entry.set(
            gimli::DW_AT_high_pc,
            AttributeValue::Udata(func.code.len() as u64),
        );
        entry.set(
            gimli::DW_AT_decl_file,
            AttributeValue::FileIndex(Some(decl_file_id)),
        );
        entry.set(
            gimli::DW_AT_decl_line,
            AttributeValue::Udata(u64::from(declaration.line)),
        );
        entry.set(
            gimli::DW_AT_decl_column,
            AttributeValue::Udata(u64::from(declaration.column)),
        );
        entry.set(gimli::DW_AT_external, AttributeValue::Flag(!func.local));
        entry.set(
            gimli::DW_AT_frame_base,
            AttributeValue::Exprloc(frame_base_expr()),
        );
    }

    for compiled in &debug.variables {
        let Some(variable) = debug.function.variables.get(compiled.variable as usize) else {
            continue;
        };
        let tag = match variable.kind {
            tuffy_ir::debug::DebugVariableKind::Parameter => gimli::DW_TAG_formal_parameter,
            tuffy_ir::debug::DebugVariableKind::Local => gimli::DW_TAG_variable,
        };
        let decl_attrs = variable.declaration.as_ref().map(|decl| {
            let file_id = ensure_file_id(
                &mut unit.line_program,
                &mut file_ids,
                &working_dir,
                &decl.file,
            );
            (file_id, decl.line, decl.column)
        });
        let location_attr = match compiled.ranges.as_slice() {
            [
                DebugVariableRange {
                    start,
                    end,
                    location,
                },
            ] if *start == 0 && *end == func.code.len() as u32 => {
                AttributeValue::Exprloc(debug_expr(location))
            }
            ranges => {
                let loc_list = debug_location_list(symbol_index, ranges)?;
                let loc_id = unit.locations.add(loc_list);
                AttributeValue::LocationListRef(loc_id)
            }
        };
        let entry_id = unit.add(subprogram, tag);
        let entry = unit.get_mut(entry_id);
        entry.set(
            gimli::DW_AT_name,
            AttributeValue::String(variable.name.as_bytes().to_vec()),
        );
        if let Some((file_id, line, column)) = decl_attrs {
            entry.set(
                gimli::DW_AT_decl_file,
                AttributeValue::FileIndex(Some(file_id)),
            );
            entry.set(
                gimli::DW_AT_decl_line,
                AttributeValue::Udata(u64::from(line)),
            );
            entry.set(
                gimli::DW_AT_decl_column,
                AttributeValue::Udata(u64::from(column)),
            );
        }
        entry.set(gimli::DW_AT_location, location_attr);
    }

    Some(unit)
}

/// Emit DWARF sections for the compiled functions that carry debug info.
fn emit_dwarf(
    obj: &mut Object,
    functions: &[CompiledFunction],
    sym_map: &HashMap<String, SymbolId>,
) {
    if !functions.iter().any(|func| func.debug.is_some()) {
        return;
    }

    let encoding = Encoding {
        format: Format::Dwarf32,
        version: 5,
        address_size: 8,
    };
    let line_encoding = LineEncoding::default();
    let mut dwarf = Dwarf::new();
    let mut symbol_ids = Vec::new();

    for func in functions {
        let Some(debug) = &func.debug else {
            continue;
        };
        let Some(&symbol_id) = sym_map.get(&func.name) else {
            continue;
        };
        let symbol_index = symbol_ids.len();
        symbol_ids.push(symbol_id);
        if let Some(unit) = build_dwarf_unit(encoding, line_encoding, func, debug, symbol_index) {
            dwarf.units.add(unit);
        }
    }

    if symbol_ids.is_empty() {
        return;
    }

    let mut sections = Sections::new(DwarfSectionWriter::default());
    dwarf
        .write(&mut sections)
        .expect("failed to build DWARF sections");

    let mut section_map = HashMap::new();
    sections
        .for_each(|id, section| -> Result<(), ()> {
            if section.slice().is_empty() {
                return Ok(());
            }
            let kind = match id {
                DwarfSectionId::DebugStr | DwarfSectionId::DebugLineStr => SectionKind::DebugString,
                _ => SectionKind::Debug,
            };
            let sid = obj.add_section(vec![], id.name().as_bytes().to_vec(), kind);
            obj.set_section_data(sid, section.slice().to_vec(), 1);
            section_map.insert(id, sid);
            Ok(())
        })
        .expect("failed to add DWARF sections");

    sections
        .for_each(|id, section| -> Result<(), ()> {
            let Some(&section_id) = section_map.get(&id) else {
                return Ok(());
            };
            for reloc in &section.relocations {
                let target = match reloc.target {
                    DwarfRelocationTarget::Symbol(index) => symbol_ids[index],
                    DwarfRelocationTarget::Section(section_kind) => {
                        obj.section_symbol(section_map[&section_kind])
                    }
                };
                obj.add_relocation(
                    section_id,
                    ObjRelocation {
                        offset: reloc.offset as u64,
                        symbol: target,
                        addend: reloc.addend,
                        flags: RelocationFlags::Generic {
                            kind: RelocationKind::Absolute,
                            encoding: RelocationEncoding::Generic,
                            size: reloc.size * 8,
                        },
                    },
                )
                .expect("failed to add DWARF relocation");
            }
            Ok(())
        })
        .expect("failed to wire DWARF relocations");
}

// ── .eh_frame generation ─────────────────────────────────────────────────────

/// DWARF register numbers for x86-64.
/// DWARF register number for `%rbp`.
const DW_REG_RBP: u8 = 6;
/// DWARF register number for `%rsp`.
const DW_REG_RSP: u8 = 7;
/// DWARF register number for the return address (`%rip`).
const DW_REG_RA: u8 = 16; // return address (rip)

/// Pointer size for x86-64.
const PTR_SIZE: usize = 8;

/// Encode a DWARF unsigned LEB128 value.
fn uleb128(buf: &mut Vec<u8>, mut val: u64) {
    loop {
        let byte = (val & 0x7f) as u8;
        val >>= 7;
        if val == 0 {
            buf.push(byte);
            return;
        }
        buf.push(byte | 0x80);
    }
}

/// Encode a DWARF signed LEB128 value.
fn sleb128(buf: &mut Vec<u8>, mut val: i64) {
    loop {
        let byte = (val & 0x7f) as u8;
        val >>= 7;
        let done = (val == 0 && byte & 0x40 == 0) || (val == -1 && byte & 0x40 != 0);
        if done {
            buf.push(byte);
            return;
        }
        buf.push(byte | 0x80);
    }
}

/// Pad `buf` with DW_CFA_nop (0x00) so its length is a multiple of `align`.
fn pad_to(buf: &mut Vec<u8>, start: usize, align: usize) {
    let len = buf.len() - start;
    let padded = (len + align - 1) & !(align - 1);
    buf.resize(start + padded, 0x00);
}

/// Build a "zR" CIE (no personality, no LSDA) for x86-64.
/// Returns the byte offset within `eh` where the CIE length field starts.
fn emit_cie_zr(eh: &mut Vec<u8>) -> usize {
    let cie_start = eh.len();
    eh.extend_from_slice(&[0; 4]); // placeholder for length

    let content_start = eh.len();
    eh.extend_from_slice(&0u32.to_ne_bytes()); // CIE id = 0
    eh.push(1); // version
    eh.extend_from_slice(b"zR\0"); // augmentation: sized + FDE encoding
    uleb128(eh, 1); // code alignment factor
    sleb128(eh, -8); // data alignment factor
    uleb128(eh, DW_REG_RA as u64); // return address register

    // Augmentation data
    uleb128(eh, 1); // augmentation data length
    eh.push(0x1b); // FDE pointer encoding: DW_EH_PE_pcrel | DW_EH_PE_sdata4

    // Initial instructions: CFA = RSP + 8, RA at CFA - 8
    emit_cie_initial_instructions(eh);

    pad_to(eh, content_start, PTR_SIZE);

    // Patch length field
    let content_len = (eh.len() - content_start) as u32;
    eh[cie_start..cie_start + 4].copy_from_slice(&content_len.to_ne_bytes());

    cie_start
}

/// Build a "zPLR" CIE (personality + LSDA + FDE encoding) for x86-64.
/// Returns `(cie_start, personality_ptr_offset)` — the CIE start offset
/// and the offset of the personality pointer field that needs a relocation.
fn emit_cie_zplr(eh: &mut Vec<u8>) -> (usize, usize) {
    let cie_start = eh.len();
    eh.extend_from_slice(&[0; 4]); // placeholder for length

    let content_start = eh.len();
    eh.extend_from_slice(&0u32.to_ne_bytes()); // CIE id = 0
    eh.push(1); // version
    eh.extend_from_slice(b"zPLR\0"); // augmentation: personality + LSDA + FDE encoding
    uleb128(eh, 1); // code alignment factor
    sleb128(eh, -8); // data alignment factor
    uleb128(eh, DW_REG_RA as u64); // return address register

    // Augmentation data: personality_enc(1) + personality_ptr(4) + lsda_enc(1) + fde_enc(1) = 7
    uleb128(eh, 7); // augmentation data length

    // P: personality function encoding + pointer
    // DW_EH_PE_indirect | DW_EH_PE_pcrel | DW_EH_PE_sdata4 = 0x9b
    eh.push(0x9b);
    let personality_ptr_offset = eh.len();
    eh.extend_from_slice(&0i32.to_ne_bytes()); // placeholder, needs relocation

    // L: LSDA pointer encoding in FDEs
    // DW_EH_PE_pcrel | DW_EH_PE_sdata4 = 0x1b
    eh.push(0x1b);

    // R: FDE pointer encoding
    // DW_EH_PE_pcrel | DW_EH_PE_sdata4 = 0x1b
    eh.push(0x1b);

    // Initial instructions: CFA = RSP + 8, RA at CFA - 8
    emit_cie_initial_instructions(eh);

    pad_to(eh, content_start, PTR_SIZE);

    // Patch length field
    let content_len = (eh.len() - content_start) as u32;
    eh[cie_start..cie_start + 4].copy_from_slice(&content_len.to_ne_bytes());

    (cie_start, personality_ptr_offset)
}

/// Emit the initial CFA instructions shared by all CIE variants.
fn emit_cie_initial_instructions(eh: &mut Vec<u8>) {
    eh.push(0x0c); // DW_CFA_def_cfa
    uleb128(eh, DW_REG_RSP as u64);
    uleb128(eh, 8);
    eh.push(0x80 | DW_REG_RA); // DW_CFA_offset(RA, 1) → RA at CFA - 8
    uleb128(eh, 1); // factored offset: 1 * 8 = 8
}

/// Build an FDE for one function and append it to `eh`.
///
/// When `has_lsda` is true the CIE uses "zPLR" augmentation and each FDE
/// carries a 4-byte LSDA pointer in its augmentation data.
///
/// Returns `(fde_start, initial_location_offset, lsda_ptr_offset)`.
/// `lsda_ptr_offset` is `Some` only when `has_lsda` is true.
fn emit_fde(
    eh: &mut Vec<u8>,
    cie_start: usize,
    code_len: u32,
    has_frame_pointer: bool,
    has_lsda: bool,
    callee_saved_dwarf_regs: &[u8],
    sub_amount: i32,
) -> (usize, usize, Option<usize>) {
    let fde_start = eh.len();
    eh.extend_from_slice(&[0; 4]); // placeholder for length

    let content_start = eh.len();

    // CIE pointer: offset from *this field* back to the CIE start.
    let cie_ptr = (content_start - cie_start) as u32;
    eh.extend_from_slice(&cie_ptr.to_ne_bytes());

    // initial_location (pc-relative, patched by relocation)
    let initial_loc_offset = eh.len();
    eh.extend_from_slice(&0i32.to_ne_bytes());

    // address_range
    eh.extend_from_slice(&code_len.to_ne_bytes());

    // Augmentation data
    let lsda_ptr_offset = if has_lsda {
        uleb128(eh, 4); // augmentation data length: 4 bytes for sdata4 LSDA pointer
        let off = eh.len();
        eh.extend_from_slice(&0i32.to_ne_bytes()); // placeholder LSDA pointer
        Some(off)
    } else {
        uleb128(eh, 0); // no augmentation data
        None
    };

    if has_frame_pointer {
        // After push rbp (+1 byte):
        //   CFA = RSP + 16, RBP saved at CFA - 16
        eh.push(0x40 | 1); // DW_CFA_advance_loc(1)
        eh.push(0x0e); // DW_CFA_def_cfa_offset
        uleb128(eh, 16);
        eh.push(0x80 | DW_REG_RBP); // DW_CFA_offset(RBP, 2) → RBP at CFA - 16
        uleb128(eh, 2);

        // After mov rbp, rsp (+3 bytes, total offset 4):
        //   CFA = RBP + 16
        eh.push(0x40 | 3); // DW_CFA_advance_loc(3)
        eh.push(0x0d); // DW_CFA_def_cfa_register
        uleb128(eh, DW_REG_RBP as u64);

        // Callee-saved register pushes happen after `sub $sub_amount, %rsp`.
        // Prologue: push rbp(1) | mov rsp,rbp(3) | sub $N,rsp(7) | push reg0 | push reg1 ...
        // sub $imm32 is always 7 bytes (Sub_rm64_imm32 encoding).
        // push reg is 1 byte for regs 0-7 (no REX), 2 bytes for regs 8-15 (REX.B).
        //
        // Frame layout (CFA = RBP + 16):
        //   [RBP - sub_amount - 8*(i+1)] = callee_saved[i]
        //   => CFA offset = 16 + sub_amount + 8*(i+1)
        if !callee_saved_dwarf_regs.is_empty() {
            // Advance past the sub instruction (7 bytes) and first push.
            let sub_size: u32 = 7;
            for (i, &dwarf_reg) in callee_saved_dwarf_regs.iter().enumerate() {
                let delta = if i == 0 {
                    sub_size + push_size(dwarf_reg) as u32
                } else {
                    push_size(dwarf_reg) as u32
                };
                emit_advance_loc(eh, delta);
                let factored = (sub_amount as u64 + 8 * (i as u64 + 1) + 16) / 8;
                eh.push(0x80 | dwarf_reg); // DW_CFA_offset(reg, N)
                uleb128(eh, factored);
            }
        }
    }

    pad_to(eh, content_start, PTR_SIZE);

    // Patch length field
    let content_len = (eh.len() - content_start) as u32;
    eh[fde_start..fde_start + 4].copy_from_slice(&content_len.to_ne_bytes());

    (fde_start, initial_loc_offset, lsda_ptr_offset)
}

/// Byte size of a `push` instruction for a register with the given DWARF number.
fn push_size(dwarf_reg: u8) -> u8 {
    if dwarf_reg >= 8 { 2 } else { 1 } // REX prefix needed for extended registers
}

/// Emit a DW_CFA_advance_loc of the appropriate size.
fn emit_advance_loc(eh: &mut Vec<u8>, delta: u32) {
    if delta <= 0x3f {
        eh.push(0x40 | delta as u8);
    } else if delta <= 0xff {
        eh.push(0x02); // DW_CFA_advance_loc1
        eh.push(delta as u8);
    } else {
        eh.push(0x03); // DW_CFA_advance_loc2
        eh.extend_from_slice(&(delta as u16).to_ne_bytes());
    }
}

/// Build an LSDA (Language-Specific Data Area) for one function.
/// Returns the bytes to be placed in `.gcc_except_table`.
fn build_lsda(entries: &[tuffy_target::types::CallSiteEntry]) -> Vec<u8> {
    let mut lsda = Vec::new();

    // Header
    lsda.push(0xff); // LPStart encoding = DW_EH_PE_omit (use function start)
    lsda.push(0xff); // TType encoding = DW_EH_PE_omit (no type table)

    // Call-site table encoding = DW_EH_PE_uleb128
    lsda.push(0x01);

    // Build call-site table body first to measure its length.
    let mut cs_table = Vec::new();
    for e in entries {
        uleb128(&mut cs_table, e.call_start as u64);
        uleb128(&mut cs_table, e.call_length as u64);
        uleb128(&mut cs_table, e.landing_pad as u64);
        uleb128(&mut cs_table, 0); // action = 0 (cleanup only)
    }

    uleb128(&mut lsda, cs_table.len() as u64); // call-site table length
    lsda.extend_from_slice(&cs_table);

    lsda
}

/// Emit `DW.ref.rust_eh_personality` in `.data.rel.ro`.
///
/// This is an indirect pointer: a hidden weak 8-byte object containing
/// the address of `rust_eh_personality`, referenced from the CIE.
fn emit_personality_ref(obj: &mut Object, sym_map: &mut HashMap<String, SymbolId>) -> SymbolId {
    let section = obj.section_id(object::write::StandardSection::ReadOnlyDataWithRel);
    let data = [0u8; 8];
    let offset = obj.append_section_data(section, &data, 8);

    let dw_ref_sid = obj.add_symbol(Symbol {
        name: b"DW.ref.rust_eh_personality".to_vec(),
        value: offset,
        size: 8,
        kind: SymbolKind::Data,
        scope: SymbolScope::Linkage,
        weak: true,
        section: SymbolSection::Section(section),
        flags: SymbolFlags::Elf {
            st_info: (object::elf::STB_WEAK << 4) | object::elf::STT_OBJECT,
            st_other: object::elf::STV_HIDDEN,
        },
    });
    sym_map.insert("DW.ref.rust_eh_personality".to_string(), dw_ref_sid);

    // The 8 bytes hold a R_X86_64_64 relocation to rust_eh_personality.
    let personality_sid = if let Some(&sid) = sym_map.get("rust_eh_personality") {
        sid
    } else {
        let sid = obj.add_symbol(Symbol {
            name: b"rust_eh_personality".to_vec(),
            value: 0,
            size: 0,
            kind: SymbolKind::Text,
            scope: SymbolScope::Unknown,
            weak: false,
            section: SymbolSection::Undefined,
            flags: SymbolFlags::None,
        });
        sym_map.insert("rust_eh_personality".to_string(), sid);
        sid
    };

    obj.add_relocation(
        section,
        ObjRelocation {
            offset,
            symbol: personality_sid,
            addend: 0,
            flags: RelocationFlags::Generic {
                kind: RelocationKind::Absolute,
                encoding: RelocationEncoding::Generic,
                size: 64,
            },
        },
    )
    .expect("failed to add DW.ref.rust_eh_personality relocation");

    dw_ref_sid
}

/// Generate `.eh_frame` (and optionally `.gcc_except_table`) for all
/// functions in the object file.
///
/// Weak (generic/monomorphized) functions get per-function `.text.func_name`
/// and `.gcc_except_table.func_name` sections placed in COMDAT groups.
/// The shared `.eh_frame` section is NOT in any COMDAT group; instead,
/// FDE initial_location relocations use **section symbols** so the linker
/// can determine FDE liveness: when a COMDAT group is discarded the
/// section symbol dies, causing the linker to discard the FDE and skip
/// its LSDA relocation.  This matches GCC/LLVM's approach.
fn emit_eh_frame(
    obj: &mut Object,
    functions: &[CompiledFunction],
    sym_map: &mut HashMap<String, SymbolId>,
    func_text_sections: &[SectionId],
    code_offsets: &[u64],
) {
    if functions.is_empty() {
        return;
    }

    let needs_personality = functions.iter().any(|f| !f.call_site_table.is_empty());

    // ── Personality reference ────────────────────────────────────────────
    let personality_ref_sid = if needs_personality {
        Some(emit_personality_ref(obj, sym_map))
    } else {
        None
    };

    struct EhReloc {
        offset_in_section: usize,
        symbol: SymbolId,
        addend: i64,
    }

    let pcrel_32_flags = RelocationFlags::Generic {
        kind: RelocationKind::Relative,
        encoding: RelocationEncoding::Generic,
        size: 32,
    };

    // ── Per-function .gcc_except_table for weak functions (COMDAT) ───────
    // Each weak function with LSDA gets its own section in the COMDAT group.
    let mut per_func_except: Vec<Option<SectionId>> = vec![None; functions.len()];
    for (i, func) in functions.iter().enumerate() {
        if !func.weak || func.call_site_table.is_empty() {
            continue;
        }
        let lsda = build_lsda(&func.call_site_table);
        let sec_name = format!(".gcc_except_table.{}", func.name);
        let sid = obj.add_section(vec![], sec_name.into_bytes(), SectionKind::ReadOnlyData);
        set_shf_group(obj, sid, SHF_ALLOC | SHF_GROUP);
        obj.set_section_data(sid, lsda, 4);
        per_func_except[i] = Some(sid);
    }

    // Create COMDAT groups: .text.func_name [+ .gcc_except_table.func_name]
    for (i, func) in functions.iter().enumerate() {
        if !func.weak {
            continue;
        }
        let mut comdat_sections = vec![func_text_sections[i]];
        if let Some(except_sid) = per_func_except[i] {
            comdat_sections.push(except_sid);
        }
        if let Some(&func_sid) = sym_map.get(&func.name) {
            obj.add_comdat(Comdat {
                kind: ComdatKind::Any,
                symbol: func_sid,
                sections: comdat_sections,
            });
        }
    }

    // ── Shared .gcc_except_table for non-weak functions ─────────────────
    let mut shared_except_data = Vec::new();
    let mut shared_lsda_offsets: Vec<Option<usize>> = vec![None; functions.len()];
    for (i, func) in functions.iter().enumerate() {
        if func.weak || func.call_site_table.is_empty() {
            continue;
        }
        shared_lsda_offsets[i] = Some(shared_except_data.len());
        shared_except_data.extend_from_slice(&build_lsda(&func.call_site_table));
    }
    let shared_except_section = if !shared_except_data.is_empty() {
        let sid = obj.add_section(
            vec![],
            b".gcc_except_table".to_vec(),
            SectionKind::ReadOnlyData,
        );
        obj.set_section_data(sid, shared_except_data, 4);
        Some(sid)
    } else {
        None
    };

    // ── Single shared .eh_frame for ALL functions ───────────────────────
    // FDE initial_location uses SECTION symbols so the linker can detect
    // dead FDEs when their COMDAT text section is discarded.
    let mut eh = Vec::new();
    let zr_cie_start = emit_cie_zr(&mut eh);

    let zplr_cie = if needs_personality {
        let (start, pers_off) = emit_cie_zplr(&mut eh);
        Some((start, pers_off))
    } else {
        None
    };

    let mut eh_relocs: Vec<EhReloc> = Vec::new();
    if let (Some((_, pers_off)), Some(pers_sid)) = (zplr_cie, personality_ref_sid) {
        eh_relocs.push(EhReloc {
            offset_in_section: pers_off,
            symbol: pers_sid,
            addend: 0,
        });
    }

    for (i, func) in functions.iter().enumerate() {
        let func_has_cleanup = !func.call_site_table.is_empty();
        let (cie_start, has_lsda) = if func_has_cleanup {
            (zplr_cie.unwrap().0, true)
        } else {
            (zr_cie_start, false)
        };

        let (_, initial_loc_offset, lsda_ptr_offset) = emit_fde(
            &mut eh,
            cie_start,
            func.code.len() as u32,
            func.has_frame_pointer,
            has_lsda,
            &func.callee_saved_dwarf_regs,
            func.sub_amount,
        );

        // Use SECTION symbol + offset for initial_location so the linker
        // can determine FDE liveness when COMDAT groups are discarded.
        let text_section = func_text_sections[i];
        let section_sym = obj.section_symbol(text_section);
        eh_relocs.push(EhReloc {
            offset_in_section: initial_loc_offset,
            symbol: section_sym,
            addend: code_offsets[i] as i64,
        });

        // LSDA pointer relocation
        if let Some(lsda_off) = lsda_ptr_offset {
            if func.weak {
                // Weak: per-function .gcc_except_table section (in COMDAT group)
                if let Some(except_sid) = per_func_except[i] {
                    let lsda_sym = obj.section_symbol(except_sid);
                    eh_relocs.push(EhReloc {
                        offset_in_section: lsda_off,
                        symbol: lsda_sym,
                        addend: 0,
                    });
                }
            } else {
                // Non-weak: shared .gcc_except_table + offset
                if let (Some(Some(offset)), Some(except_sid)) =
                    (shared_lsda_offsets.get(i), shared_except_section)
                {
                    let lsda_sym = obj.section_symbol(except_sid);
                    eh_relocs.push(EhReloc {
                        offset_in_section: lsda_off,
                        symbol: lsda_sym,
                        addend: *offset as i64,
                    });
                }
            }
        }
    }

    eh.extend_from_slice(&0u32.to_ne_bytes()); // terminator

    let eh_section = obj.add_section(vec![], b".eh_frame".to_vec(), SectionKind::ReadOnlyData);
    obj.set_section_data(eh_section, eh, PTR_SIZE as u64);
    for reloc in eh_relocs {
        obj.add_relocation(
            eh_section,
            ObjRelocation {
                offset: reloc.offset_in_section as u64,
                symbol: reloc.symbol,
                addend: reloc.addend,
                flags: pcrel_32_flags,
            },
        )
        .expect("failed to add .eh_frame relocation");
    }
}
