//! ELF object file emission using the `object` crate.

use std::collections::HashMap;

use object::write::{Object, Relocation as ObjRelocation, Symbol, SymbolId, SymbolSection};
use object::{
    Architecture, BinaryFormat, Endianness, RelocationEncoding, RelocationFlags, RelocationKind,
    SectionFlags, SectionKind, SymbolFlags, SymbolKind, SymbolScope,
};

use tuffy_target::reloc::{RelocKind, Relocation};
pub use tuffy_target::types::{CompiledFunction, StaticData};

/// Emit a single function as an ELF object file.
pub fn emit_elf(name: &str, code: &[u8], relocations: &[Relocation]) -> Vec<u8> {
    emit_elf_multi(&[CompiledFunction {
        name: name.to_string(),
        code: code.to_vec(),
        relocations: relocations.to_vec(),
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

/// Emit multiple functions and static data as a single ELF object file.
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
    let mut code_offsets: Vec<u64> = Vec::with_capacity(functions.len());
    for func in functions {
        let code_offset = obj.append_section_data(text, &func.code, 16);
        code_offsets.push(code_offset);

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
            section: SymbolSection::Section(text),
            flags: SymbolFlags::None,
        });
        sym_map.insert(func.name.clone(), func_sid);
    }

    // Pass 2: Add relocations now that all symbols are defined.
    for (func, &code_offset) in functions.iter().zip(code_offsets.iter()) {
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
                text,
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

    // Generate .eh_frame unwind information so that libunwind can traverse
    // tuffy-compiled frames (required for panic unwinding / catch_unwind).
    emit_eh_frame(&mut obj, functions, &mut sym_map);

    let mut buf = Vec::new();
    obj.emit(&mut buf).expect("failed to emit ELF object");
    buf
}

// ── .eh_frame generation ─────────────────────────────────────────────────────

/// DWARF register numbers for x86-64.
const DW_REG_RBP: u8 = 6;
const DW_REG_RSP: u8 = 7;
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
fn emit_eh_frame(
    obj: &mut Object,
    functions: &[CompiledFunction],
    sym_map: &mut HashMap<String, SymbolId>,
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

    // ── .gcc_except_table (LSDAs) ───────────────────────────────────────
    // Build LSDA bytes for each function with cleanup entries.
    // lsda_info[i] = Some((offset_in_section, lsda_bytes_len)) or None.
    let mut except_table_data = Vec::new();
    let mut lsda_info: Vec<Option<usize>> = Vec::with_capacity(functions.len());
    for func in functions {
        if func.call_site_table.is_empty() {
            lsda_info.push(None);
        } else {
            let offset = except_table_data.len();
            let lsda = build_lsda(&func.call_site_table);
            except_table_data.extend_from_slice(&lsda);
            lsda_info.push(Some(offset));
        }
    }

    let except_section_id = if !except_table_data.is_empty() {
        let sid = obj.add_section(
            vec![],
            b".gcc_except_table".to_vec(),
            SectionKind::ReadOnlyData,
        );
        obj.set_section_data(sid, except_table_data, 4);
        Some(sid)
    } else {
        None
    };

    // ── .eh_frame ───────────────────────────────────────────────────────
    // Two CIEs: "zR" for functions without cleanup, "zPLR" for functions
    // with cleanup. Each FDE references the appropriate CIE so the
    // personality function is only invoked for frames that actually have
    // LSDA data.
    let mut eh = Vec::new();

    let zr_cie_start = emit_cie_zr(&mut eh);

    // Emit "zPLR" CIE only when at least one function needs it.
    let zplr_cie = if needs_personality {
        let (start, pers_off) = emit_cie_zplr(&mut eh);
        Some((start, pers_off))
    } else {
        None
    };

    struct EhReloc {
        offset_in_section: usize,
        symbol: SymbolId,
        addend: i64,
    }
    let mut eh_relocs: Vec<EhReloc> = Vec::new();

    // CIE personality pointer relocation
    if let (Some((_, pers_off)), Some(pers_sid)) = (zplr_cie, personality_ref_sid) {
        eh_relocs.push(EhReloc {
            offset_in_section: pers_off,
            symbol: pers_sid,
            addend: 0,
        });
    }

    // Emit FDE for each function
    for (i, func) in functions.iter().enumerate() {
        let func_has_cleanup = !func.call_site_table.is_empty();
        let (cie_start, has_lsda) = if func_has_cleanup {
            // Must have zPLR CIE when function has cleanup
            (zplr_cie.unwrap().0, true)
        } else {
            // Use simple "zR" CIE — no personality invoked for this frame
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

        // initial_location relocation → function symbol
        if let Some(&sym_id) = sym_map.get(&func.name) {
            eh_relocs.push(EhReloc {
                offset_in_section: initial_loc_offset,
                symbol: sym_id,
                addend: 0,
            });
        }

        // LSDA pointer relocation → .gcc_except_table + offset
        if let (Some(lsda_off), Some(Some(lsda_offset_in_section))) =
            (lsda_ptr_offset, lsda_info.get(i))
            && let Some(except_sid) = except_section_id
        {
            let section_sym = obj.section_symbol(except_sid);
            eh_relocs.push(EhReloc {
                offset_in_section: lsda_off,
                symbol: section_sym,
                addend: *lsda_offset_in_section as i64,
            });
        }
    }

    // Terminator: zero-length entry
    eh.extend_from_slice(&0u32.to_ne_bytes());

    // Add .eh_frame section
    let eh_section_id = obj.add_section(vec![], b".eh_frame".to_vec(), SectionKind::ReadOnlyData);
    obj.set_section_data(eh_section_id, eh, PTR_SIZE as u64);

    // Add relocations
    for reloc in eh_relocs {
        obj.add_relocation(
            eh_section_id,
            ObjRelocation {
                offset: reloc.offset_in_section as u64,
                symbol: reloc.symbol,
                addend: reloc.addend,
                flags: RelocationFlags::Generic {
                    kind: RelocationKind::Relative,
                    encoding: RelocationEncoding::Generic,
                    size: 32,
                },
            },
        )
        .expect("failed to add .eh_frame relocation");
    }
}
