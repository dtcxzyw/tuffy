//! X86-64 backend implementation.

use std::collections::HashMap;

use tuffy_ir::function::Function;
use tuffy_target::backend::{AbiMetadata, Backend};
use tuffy_target::reloc::{RelocKind, Relocation};
use tuffy_target::types::{CompiledFunction, StaticData};

use crate::emit::emit_elf_with_data;
use crate::encode::encode_function;
use crate::isel;

/// X86-64 ABI metadata tracking secondary return register (RDX) usage.
#[derive(Default)]
pub struct X86AbiMetadata {
    /// Maps IR instruction index → () for values that capture RDX
    /// from the preceding call.
    pub rdx_captures: HashMap<u32, ()>,
    /// Maps IR instruction index → source value index for explicit
    /// RDX moves before return.
    pub rdx_moves: HashMap<u32, u32>,
}

impl AbiMetadata for X86AbiMetadata {
    fn mark_secondary_return_capture(&mut self, inst_idx: u32) {
        self.rdx_captures.insert(inst_idx, ());
    }

    fn mark_secondary_return_move(&mut self, inst_idx: u32, source_idx: u32) {
        self.rdx_moves.insert(inst_idx, source_idx);
    }
}

/// X86-64 code generation backend.
pub struct X86Backend;

impl Backend for X86Backend {
    type Metadata = X86AbiMetadata;

    fn compile_function(
        &self,
        func: &Function,
        call_targets: &HashMap<u32, String>,
        static_refs: &HashMap<u32, String>,
        metadata: &X86AbiMetadata,
    ) -> Option<CompiledFunction> {
        let isel_result = isel::isel(
            func,
            call_targets,
            static_refs,
            &metadata.rdx_captures,
            &metadata.rdx_moves,
        )?;
        let enc = encode_function(&isel_result.insts);
        Some(CompiledFunction {
            name: isel_result.name,
            code: enc.code,
            relocations: enc.relocations,
        })
    }

    fn emit_object(&self, functions: &[CompiledFunction], statics: &[StaticData]) -> Vec<u8> {
        emit_elf_with_data(functions, statics)
    }

    fn generate_allocator_stubs(
        &self,
        pairs: &[(&str, &str)],
        shim_marker: &str,
    ) -> Vec<CompiledFunction> {
        let mut funcs = Vec::new();
        for (export_name, target_name) in pairs {
            // JMP rel32 to the target (resolved by linker).
            let code = vec![0xe9, 0x00, 0x00, 0x00, 0x00];
            let relocations = vec![Relocation {
                offset: 1,
                symbol: target_name.to_string(),
                kind: RelocKind::Call,
            }];
            funcs.push(CompiledFunction {
                name: export_name.to_string(),
                code,
                relocations,
            });
        }
        // Shim marker: trivial `ret` function.
        funcs.push(CompiledFunction {
            name: shim_marker.to_string(),
            code: vec![0xc3],
            relocations: vec![],
        });
        funcs
    }

    fn generate_entry_point(&self, main_sym: &str, start_sym: &str) -> Vec<CompiledFunction> {
        // C `main` entry point:
        //   push   rbp
        //   movsxd rax, edi           ; sign-extend argc
        //   mov    rdx, rsi           ; argv -> 3rd arg
        //   mov    rsi, rax           ; argc -> 2nd arg
        //   lea    rdi, [rip+disp32]  ; user main fn ptr -> 1st arg
        //   xor    ecx, ecx           ; sigpipe=0 -> 4th arg
        //   call   lang_start
        //   pop    rbp
        //   ret
        let main_code = vec![
            0x55, // push rbp
            0x48, 0x63, 0xc7, // movsxd rax, edi
            0x48, 0x89, 0xf2, // mov rdx, rsi
            0x48, 0x89, 0xc6, // mov rsi, rax
            0x48, 0x8d, 0x3d, 0x00, 0x00, 0x00, 0x00, // lea rdi, [rip+0]
            0x31, 0xc9, // xor ecx, ecx
            0xe8, 0x00, 0x00, 0x00, 0x00, // call lang_start
            0x5d, // pop rbp
            0xc3, // ret
        ];
        let main_relocs = vec![
            Relocation {
                offset: 13,
                symbol: main_sym.to_string(),
                kind: RelocKind::PcRel,
            },
            Relocation {
                offset: 20,
                symbol: start_sym.to_string(),
                kind: RelocKind::Call,
            },
        ];

        // Hand-crafted `lang_start`:
        //   push   rbp
        //   mov    rbp, rsp
        //   call   rdi           ; call user's main
        //   xor    eax, eax      ; return 0
        //   pop    rbp
        //   ret
        let start_code = vec![
            0x55, // push rbp
            0x48, 0x89, 0xe5, // mov rbp, rsp
            0xff, 0xd7, // call rdi
            0x31, 0xc0, // xor eax, eax
            0x5d, // pop rbp
            0xc3, // ret
        ];

        vec![
            CompiledFunction {
                name: "main".to_string(),
                code: main_code,
                relocations: main_relocs,
            },
            CompiledFunction {
                name: start_sym.to_string(),
                code: start_code,
                relocations: vec![],
            },
        ]
    }
}
