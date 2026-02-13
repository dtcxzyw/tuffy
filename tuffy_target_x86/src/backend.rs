//! X86-64 backend implementation.

use std::collections::HashMap;

use tuffy_ir::function::Function;
use tuffy_ir::module::SymbolTable;
use tuffy_regalloc::{OpKind, PReg, RegAllocInst};
use tuffy_target::backend::{AbiMetadata, Backend};
use tuffy_target::reloc::{RelocKind, Relocation};
use tuffy_target::types::{CompiledFunction, StaticData};

use crate::emit::emit_elf_with_data;
use crate::encode::encode_function;
use crate::frame::insert_prologue_epilogue;
use tuffy_regalloc::allocator::AllocResult;

use crate::inst::{MInst, OpSize, PInst, VInst};
use crate::isel;
use crate::reg::Gpr;

/// Registers available for allocation.
/// Caller-saved registers are listed first (preferred for short-lived values),
/// followed by callee-saved registers (used for values live across calls).
/// R11 is reserved as the spill temp register.
const ALLOC_REGS: [PReg; 13] = [
    PReg(0),  // Rax
    PReg(1),  // Rcx
    PReg(2),  // Rdx
    PReg(8),  // R8
    PReg(9),  // R9
    PReg(10), // R10
    PReg(6),  // Rsi
    PReg(7),  // Rdi
    // Callee-saved registers (for values live across calls).
    PReg(3),  // Rbx
    PReg(12), // R12
    PReg(13), // R13
    PReg(14), // R14
    PReg(15), // R15
];

/// Register reserved for spill loads/stores. Must NOT be in ALLOC_REGS.
const SPILL_REG: PReg = PReg(11); // R11

/// Callee-saved registers that must be preserved across function calls.
const CALLEE_SAVED_REGS: [PReg; 5] = [
    PReg(3),  // Rbx
    PReg(12), // R12
    PReg(13), // R13
    PReg(14), // R14
    PReg(15), // R15
];

/// X86-64 ABI metadata tracking secondary return register (RDX) usage.
#[derive(Default)]
pub struct X86AbiMetadata {
    pub rdx_captures: HashMap<u32, ()>,
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

/// Rewrite a VReg instruction to a Gpr instruction using the assignment map.
fn rewrite_inst(inst: &VInst, assignments: &[PReg]) -> PInst {
    let r = |vreg: &tuffy_regalloc::VReg| -> Gpr { Gpr::from_preg(assignments[vreg.0 as usize]) };
    match inst {
        MInst::MovRR { size, dst, src } => MInst::MovRR {
            size: *size,
            dst: r(dst),
            src: r(src),
        },
        MInst::MovRI { size, dst, imm } => MInst::MovRI {
            size: *size,
            dst: r(dst),
            imm: *imm,
        },
        MInst::AddRR { size, dst, src } => MInst::AddRR {
            size: *size,
            dst: r(dst),
            src: r(src),
        },
        MInst::SubRR { size, dst, src } => MInst::SubRR {
            size: *size,
            dst: r(dst),
            src: r(src),
        },
        MInst::ImulRR { size, dst, src } => MInst::ImulRR {
            size: *size,
            dst: r(dst),
            src: r(src),
        },
        MInst::Ret => MInst::Ret,
        MInst::Label { id } => MInst::Label { id: *id },
        MInst::Jmp { target } => MInst::Jmp { target: *target },
        MInst::Jcc { cc, target } => MInst::Jcc {
            cc: *cc,
            target: *target,
        },
        MInst::CmpRR { size, src1, src2 } => MInst::CmpRR {
            size: *size,
            src1: r(src1),
            src2: r(src2),
        },
        MInst::CmpRI { size, src, imm } => MInst::CmpRI {
            size: *size,
            src: r(src),
            imm: *imm,
        },
        MInst::TestRR { size, src1, src2 } => MInst::TestRR {
            size: *size,
            src1: r(src1),
            src2: r(src2),
        },
        MInst::CallSym { name, ret } => MInst::CallSym {
            name: name.clone(),
            ret: ret.map(|v| r(&v)),
        },
        MInst::CallReg { callee, ret } => MInst::CallReg {
            callee: r(callee),
            ret: ret.map(|v| r(&v)),
        },
        MInst::Push { reg } => MInst::Push { reg: r(reg) },
        MInst::Pop { reg } => MInst::Pop { reg: r(reg) },
        MInst::SubSPI { imm } => MInst::SubSPI { imm: *imm },
        MInst::AddSPI { imm } => MInst::AddSPI { imm: *imm },
        MInst::MovRM {
            size,
            dst,
            base,
            offset,
        } => MInst::MovRM {
            size: *size,
            dst: r(dst),
            base: r(base),
            offset: *offset,
        },
        MInst::MovMR {
            size,
            base,
            offset,
            src,
        } => MInst::MovMR {
            size: *size,
            base: r(base),
            offset: *offset,
            src: r(src),
        },
        MInst::Lea { dst, base, offset } => MInst::Lea {
            dst: r(dst),
            base: r(base),
            offset: *offset,
        },
        MInst::MovRI64 { dst, imm } => MInst::MovRI64 {
            dst: r(dst),
            imm: *imm,
        },
        MInst::MovMI {
            size,
            base,
            offset,
            imm,
        } => MInst::MovMI {
            size: *size,
            base: r(base),
            offset: *offset,
            imm: *imm,
        },
        MInst::LeaSymbol { dst, symbol } => MInst::LeaSymbol {
            dst: r(dst),
            symbol: symbol.clone(),
        },
        MInst::OrRR { size, dst, src } => MInst::OrRR {
            size: *size,
            dst: r(dst),
            src: r(src),
        },
        MInst::AndRR { size, dst, src } => MInst::AndRR {
            size: *size,
            dst: r(dst),
            src: r(src),
        },
        MInst::XorRR { size, dst, src } => MInst::XorRR {
            size: *size,
            dst: r(dst),
            src: r(src),
        },
        MInst::ShlRCL { size, dst } => MInst::ShlRCL {
            size: *size,
            dst: r(dst),
        },
        MInst::ShrRCL { size, dst } => MInst::ShrRCL {
            size: *size,
            dst: r(dst),
        },
        MInst::SarRCL { size, dst } => MInst::SarRCL {
            size: *size,
            dst: r(dst),
        },
        MInst::ShlImm { size, dst, imm } => MInst::ShlImm {
            size: *size,
            dst: r(dst),
            imm: *imm,
        },
        MInst::SarImm { size, dst, imm } => MInst::SarImm {
            size: *size,
            dst: r(dst),
            imm: *imm,
        },
        MInst::AndRI { size, dst, imm } => MInst::AndRI {
            size: *size,
            dst: r(dst),
            imm: *imm,
        },
        MInst::CMOVcc { size, cc, dst, src } => MInst::CMOVcc {
            size: *size,
            cc: *cc,
            dst: r(dst),
            src: r(src),
        },
        MInst::SetCC { cc, dst } => MInst::SetCC {
            cc: *cc,
            dst: r(dst),
        },
        MInst::MovzxB { dst, src } => MInst::MovzxB {
            dst: r(dst),
            src: r(src),
        },
        MInst::MovzxW { dst, src } => MInst::MovzxW {
            dst: r(dst),
            src: r(src),
        },
        MInst::MovsxB { dst, src } => MInst::MovsxB {
            dst: r(dst),
            src: r(src),
        },
        MInst::MovsxW { dst, src } => MInst::MovsxW {
            dst: r(dst),
            src: r(src),
        },
        MInst::MovsxD { dst, src } => MInst::MovsxD {
            dst: r(dst),
            src: r(src),
        },
        MInst::Cqo => MInst::Cqo,
        MInst::Idiv { size, src } => MInst::Idiv {
            size: *size,
            src: r(src),
        },
        MInst::Div { size, src } => MInst::Div {
            size: *size,
            src: r(src),
        },
        MInst::Popcnt { dst, src } => MInst::Popcnt {
            dst: r(dst),
            src: r(src),
        },
        MInst::Lzcnt { dst, src } => MInst::Lzcnt {
            dst: r(dst),
            src: r(src),
        },
        MInst::Tzcnt { dst, src } => MInst::Tzcnt {
            dst: r(dst),
            src: r(src),
        },
        MInst::Ud2 => MInst::Ud2,
    }
}

/// Rewrite VReg instructions to Gpr instructions, inserting spill loads/stores
/// for any VRegs that were spilled to stack slots by the register allocator.
///
/// Spilled VRegs are assigned to `SPILL_REG` (R11) by the allocator. This
/// function inserts:
/// - `MovRM` (load from stack → R11) before instructions that USE a spilled VReg
/// - `MovMR` (store R11 → stack) after instructions that DEF a spilled VReg
///
/// Spill slot N lives at `[RBP - isel_frame_size - (N+1)*8]`.
fn rewrite_with_spills(
    insts: &[VInst],
    alloc_result: &AllocResult,
    isel_frame_size: i32,
) -> Vec<PInst> {
    let mut out = Vec::with_capacity(insts.len() * 2);
    let mut ops_buf = Vec::new();

    for inst in insts {
        ops_buf.clear();
        inst.reg_operands(&mut ops_buf);

        // Collect spill loads (Use/UseDef) and stores (Def/UseDef).
        let mut loads: Vec<i32> = Vec::new();
        let mut stores: Vec<i32> = Vec::new();

        for op in &ops_buf {
            if let Some(&slot) = alloc_result.spill_map.get(&op.vreg.0) {
                let offset = -(isel_frame_size + (slot as i32 + 1) * 8);
                match op.kind {
                    OpKind::Use => loads.push(offset),
                    OpKind::Def => stores.push(offset),
                    OpKind::UseDef => {
                        loads.push(offset);
                        stores.push(offset);
                    }
                }
            }
        }

        // Emit spill loads before the instruction.
        for &offset in &loads {
            out.push(MInst::MovRM {
                size: OpSize::S64,
                dst: Gpr::R11,
                base: Gpr::Rbp,
                offset,
            });
        }

        // Rewrite the instruction (spilled vregs map to R11 via assignments).
        out.push(rewrite_inst(inst, &alloc_result.assignments));

        // Emit spill stores after the instruction.
        for &offset in &stores {
            out.push(MInst::MovMR {
                size: OpSize::S64,
                base: Gpr::Rbp,
                offset,
                src: Gpr::R11,
            });
        }
    }

    out
}

/// Run regalloc + rewrite + prologue/epilogue on an IselResult.
/// Public for use in tests.
pub fn lower_isel_result(isel_result: &isel::IselResult) -> Vec<PInst> {
    let alloc_result = tuffy_regalloc::allocator::allocate(
        &isel_result.insts,
        isel_result.vreg_count,
        &isel_result.constraints,
        &ALLOC_REGS,
        &CALLEE_SAVED_REGS,
        SPILL_REG,
    );
    let pinsts = rewrite_with_spills(
        &isel_result.insts,
        &alloc_result,
        isel_result.isel_frame_size,
    );
    insert_prologue_epilogue(
        pinsts,
        isel_result.isel_frame_size,
        alloc_result.spill_slots,
        isel_result.has_calls,
        &alloc_result.used_callee_saved,
    )
}

/// X86-64 code generation backend.
pub struct X86Backend;

impl Backend for X86Backend {
    type Metadata = X86AbiMetadata;

    fn compile_function(
        &self,
        func: &Function,
        symbols: &SymbolTable,
        metadata: &X86AbiMetadata,
    ) -> Option<CompiledFunction> {
        // 1. Instruction selection → MInst<VReg>
        let isel_result =
            match isel::isel(func, symbols, &metadata.rdx_captures, &metadata.rdx_moves) {
                Some(r) => r,
                None => {
                    let name = symbols.resolve(func.name);
                    eprintln!("[tuffy] isel failed for: {name}");
                    return None;
                }
            };

        // 2. Register allocation → VReg assignments
        let alloc_result = tuffy_regalloc::allocator::allocate(
            &isel_result.insts,
            isel_result.vreg_count,
            &isel_result.constraints,
            &ALLOC_REGS,
            &CALLEE_SAVED_REGS,
            SPILL_REG,
        );

        // 3. Rewrite VReg → Gpr, inserting spill loads/stores
        let pinsts = rewrite_with_spills(
            &isel_result.insts,
            &alloc_result,
            isel_result.isel_frame_size,
        );

        // 4. Insert prologue/epilogue
        let final_insts = insert_prologue_epilogue(
            pinsts,
            isel_result.isel_frame_size,
            alloc_result.spill_slots,
            isel_result.has_calls,
            &alloc_result.used_callee_saved,
        );

        // 5. Encode to machine code
        let enc = encode_function(&final_insts);
        Some(CompiledFunction {
            name: isel_result.name,
            code: enc.code,
            relocations: enc.relocations,
            weak: false,
            local: false,
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
                weak: false,
                local: false,
            });
        }
        funcs.push(CompiledFunction {
            name: shim_marker.to_string(),
            code: vec![0xc3],
            relocations: vec![],
            weak: false,
            local: false,
        });
        funcs
    }

    fn generate_entry_point(&self, main_sym: &str, start_sym: &str) -> Vec<CompiledFunction> {
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
                weak: false,
                local: false,
            },
            CompiledFunction {
                name: start_sym.to_string(),
                code: start_code,
                relocations: vec![],
                weak: false,
                local: false,
            },
        ]
    }
}
