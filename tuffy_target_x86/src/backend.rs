//! X86-64 backend implementation.

use std::collections::HashSet;

use tuffy_ir::debug::DebugValue;
use tuffy_ir::function::Function;
use tuffy_ir::module::SymbolTable;
use tuffy_ir::value::ValueRef;
use tuffy_regalloc::{OpKind, PReg, RegAllocInst};
use tuffy_target::backend::Backend;
use tuffy_target::regbank::{RegBank, preg_reg_num};
use tuffy_target::reloc::{RelocKind, Relocation};
use tuffy_target::types::{
    CompiledDebugInfo, CompiledDebugVariable, CompiledFunction, DebugLineRecord, DebugLocation,
    DebugVariableRange, StaticData,
};

use crate::emit::emit_elf_with_data;
use crate::encode::encode_function;
use crate::frame::insert_prologue_epilogue;
use crate::reg::X86RegBank;
use tuffy_regalloc::allocator::AllocResult;
use tuffy_target::isel::IselResult;

use crate::inst::{MInst, OpSize, PInst, VInst};
use crate::isel;
use crate::reg::Gpr;

/// Registers available for allocation.
/// Caller-saved registers are listed first (preferred for short-lived values),
/// followed by callee-saved registers (used for values live across calls).
/// R11 is reserved as the spill temp register.
/// XMM registers (class 1) are also included for floating-point operations.
const ALLOC_REGS: [PReg; 28] = [
    // GPRs (class 0)
    PReg(0), // Rax
    PReg(1), // Rcx
    PReg(2), // Rdx
    PReg(8), // R8
    PReg(9), // R9
    PReg(6), // Rsi
    PReg(7), // Rdi
    // Callee-saved GPRs (for values live across calls).
    PReg(3),  // Rbx
    PReg(12), // R12
    PReg(13), // R13
    PReg(14), // R14
    PReg(15), // R15
    // XMM registers (class 1) - all caller-saved on x86-64 System V ABI
    PReg(32), // XMM0
    PReg(33), // XMM1
    PReg(34), // XMM2
    PReg(35), // XMM3
    PReg(36), // XMM4
    PReg(37), // XMM5
    PReg(38), // XMM6
    PReg(39), // XMM7
    PReg(40), // XMM8
    PReg(41), // XMM9
    PReg(42), // XMM10
    PReg(43), // XMM11
    PReg(44), // XMM12
    PReg(45), // XMM13
    PReg(46), // XMM14
    PReg(47), // XMM15
];

/// Primary register reserved for spill loads/stores. Must NOT be in ALLOC_REGS.
const SPILL_REG: PReg = PReg(11); // R11

/// Secondary spill register, used when an instruction has multiple spilled
/// operands (e.g. `and dst, src` where both dst and src are spilled).
/// Must NOT be in ALLOC_REGS.
const SPILL_REG2: PReg = PReg(10); // R10

/// Callee-saved registers that must be preserved across function calls.
const CALLEE_SAVED_REGS: [PReg; 5] = [
    PReg(3),  // Rbx
    PReg(12), // R12
    PReg(13), // R13
    PReg(14), // R14
    PReg(15), // R15
];

/// Map a physical register number (PReg index) to its x86-64 DWARF register number.
fn preg_to_dwarf(p: PReg) -> u8 {
    match p.0 {
        0 => 0,          // Rax
        1 => 2,          // Rcx
        2 => 1,          // Rdx
        3 => 3,          // Rbx
        4 => 7,          // Rsp
        5 => 6,          // Rbp
        6 => 4,          // Rsi
        7 => 5,          // Rdi
        n @ 8..=15 => n, // R8–R15
        _ => panic!("preg_to_dwarf: unexpected PReg({})", p.0),
    }
}

/// Resolve a selected IR value to a compiled debug location.
fn debug_location_for_value(
    value: ValueRef,
    isel_result: &IselResult<VInst>,
    alloc_result: &AllocResult,
) -> Option<DebugLocation> {
    if let Some((offset, _align)) = isel_result.value_locations.stack_slot(value) {
        return Some(DebugLocation::FrameOffset(offset));
    }

    let vreg = isel_result.value_locations.reg(value)?;
    if let Some(&slot) = alloc_result.spill_map.get(&vreg.0) {
        let offset = -(isel_result.isel_frame_size + (slot as i32 + 1) * 8);
        return Some(DebugLocation::FrameOffset(offset));
    }

    let preg = *alloc_result.assignments.get(vreg.0 as usize)?;
    Some(DebugLocation::Register(preg_to_dwarf(preg) as u16))
}

/// Build compiled debug info for one lowered function when source data exists.
fn build_compiled_debug_info(
    func: &Function,
    isel_result: &IselResult<VInst>,
    alloc_result: &AllocResult,
    line_records: &[DebugLineRecord],
    code_len: u32,
) -> Option<CompiledDebugInfo> {
    if !func.debug.has_debuginfo() || line_records.is_empty() {
        return None;
    }

    let mut source_offsets = std::collections::HashMap::new();
    for record in line_records {
        source_offsets.entry(record.source).or_insert(record.offset);
    }

    let mut variables = Vec::new();
    for variable in 0..func.debug.variables.len() as u32 {
        let mut bindings: Vec<_> = func
            .debug
            .bindings
            .iter()
            .filter(|binding| binding.variable == variable)
            .collect();
        if bindings.is_empty() {
            continue;
        }
        bindings.sort_by_key(|binding| source_offsets.get(&binding.source).copied().unwrap_or(0));

        let mut ranges: Vec<DebugVariableRange> = Vec::new();
        for (index, binding) in bindings.iter().enumerate() {
            let DebugValue::IrValue(value) = binding.value;
            let Some(location) = debug_location_for_value(value, isel_result, alloc_result) else {
                continue;
            };
            let start = source_offsets.get(&binding.source).copied().unwrap_or(0);
            let end = bindings
                .iter()
                .skip(index + 1)
                .find_map(|next| source_offsets.get(&next.source).copied())
                .unwrap_or(code_len);
            if start >= end {
                continue;
            }
            if let Some(last) = ranges.last_mut()
                && last.end == start
                && last.location == location
            {
                last.end = end;
                continue;
            }
            ranges.push(DebugVariableRange {
                start,
                end,
                location,
            });
        }

        if !ranges.is_empty() {
            variables.push(CompiledDebugVariable { variable, ranges });
        }
    }

    Some(CompiledDebugInfo {
        function: func.debug.clone(),
        lines: line_records.to_vec(),
        variables,
    })
}

/// Rewrite a VReg instruction to a Gpr instruction using the assignment map.
fn rewrite_inst(inst: &VInst, assignments: &[PReg]) -> PInst {
    let r = |vreg: &tuffy_regalloc::VReg| -> Gpr {
        let preg = assignments[vreg.0 as usize];
        // PInst stores all physical registers in the `Gpr` slot, and the encoder
        // interprets some of them as XMM registers based on the instruction kind.
        // Strip the register-class bits here so XMM0..XMM15 map to indices 0..15.
        Gpr::from_preg(PReg(preg_reg_num(preg)))
    };
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
        MInst::AdcRR { size, dst, src } => MInst::AdcRR {
            size: *size,
            dst: r(dst),
            src: r(src),
        },
        MInst::SbbRR { size, dst, src } => MInst::SbbRR {
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
        MInst::CallSym {
            name,
            ret,
            ret2,
            cleanup_label,
        } => MInst::CallSym {
            name: name.clone(),
            ret: ret.map(|v| r(&v)),
            ret2: ret2.map(|v| r(&v)),
            cleanup_label: *cleanup_label,
        },
        MInst::CallReg {
            callee,
            ret,
            ret2,
            cleanup_label,
        } => MInst::CallReg {
            callee: r(callee),
            ret: ret.map(|v| r(&v)),
            ret2: ret2.map(|v| r(&v)),
            cleanup_label: *cleanup_label,
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
        MInst::LeaIndexed {
            dst,
            base,
            index,
            scale,
            offset,
        } => MInst::LeaIndexed {
            dst: r(dst),
            base: r(base),
            index: r(index),
            scale: *scale,
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
        MInst::TlsLeaSymbol { dst, symbol } => MInst::TlsLeaSymbol {
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
        MInst::ShrImm { size, dst, imm } => MInst::ShrImm {
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
        MInst::DivRem {
            dst,
            lhs,
            rhs,
            signed,
            rem,
        } => MInst::DivRem {
            dst: r(dst),
            lhs: r(lhs),
            rhs: r(rhs),
            signed: *signed,
            rem: *rem,
        },
        MInst::UMulOverflow {
            dst,
            overflow,
            lhs,
            rhs,
        } => MInst::UMulOverflow {
            dst: r(dst),
            overflow: r(overflow),
            lhs: r(lhs),
            rhs: r(rhs),
        },
        MInst::Popcnt { size, dst, src } => MInst::Popcnt {
            size: *size,
            dst: r(dst),
            src: r(src),
        },
        MInst::Lzcnt { size, dst, src } => MInst::Lzcnt {
            size: *size,
            dst: r(dst),
            src: r(src),
        },
        MInst::Tzcnt { size, dst, src } => MInst::Tzcnt {
            size: *size,
            dst: r(dst),
            src: r(src),
        },
        MInst::Bswap { size, dst } => MInst::Bswap {
            size: *size,
            dst: r(dst),
        },
        MInst::RolRCL { size, dst } => MInst::RolRCL {
            size: *size,
            dst: r(dst),
        },
        MInst::RorRCL { size, dst } => MInst::RorRCL {
            size: *size,
            dst: r(dst),
        },
        MInst::MovRR2 {
            dst1,
            src1,
            dst2,
            src2,
        } => MInst::MovRR2 {
            dst1: r(dst1),
            src1: r(src1),
            dst2: r(dst2),
            src2: r(src2),
        },
        MInst::Ud2 => MInst::Ud2,
        MInst::LandingPadCapture { dst } => MInst::LandingPadCapture { dst: r(dst) },
        MInst::FpBinOp {
            op,
            dst,
            lhs,
            rhs,
            double,
        } => MInst::FpBinOp {
            op: *op,
            dst: r(dst),
            lhs: r(lhs),
            rhs: r(rhs),
            double: *double,
        },
        MInst::CvtFpToInt { dst, src, double } => MInst::CvtFpToInt {
            dst: r(dst),
            src: r(src),
            double: *double,
        },
        MInst::CvtIntToFp { dst, src, double } => MInst::CvtIntToFp {
            dst: r(dst),
            src: r(src),
            double: *double,
        },
        MInst::MoveXmmToGpr { dst, src, double } => MInst::MoveXmmToGpr {
            dst: r(dst),
            src: r(src),
            double: *double,
        },
        MInst::GprToXmm { dst, src, double } => MInst::GprToXmm {
            dst: r(dst),
            src: r(src),
            double: *double,
        },
        MInst::CvtFpToFp {
            dst,
            src,
            src_double,
        } => MInst::CvtFpToFp {
            dst: r(dst),
            src: r(src),
            src_double: *src_double,
        },
        MInst::FpCmp {
            dst,
            lhs,
            rhs,
            tmp,
            kind,
            double,
        } => MInst::FpCmp {
            dst: r(dst),
            lhs: r(lhs),
            rhs: r(rhs),
            tmp: r(tmp),
            kind: *kind,
            double: *double,
        },
        MInst::AtomicRmw {
            op,
            size,
            dst,
            base,
            val,
        } => MInst::AtomicRmw {
            op: *op,
            size: *size,
            dst: r(dst),
            base: r(base),
            val: r(val),
        },
        MInst::AtomicCmpXchg {
            size,
            dst,
            base,
            expected,
            desired,
        } => MInst::AtomicCmpXchg {
            size: *size,
            dst: r(dst),
            base: r(base),
            expected: r(expected),
            desired: r(desired),
        },
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
/// When an instruction has multiple spilled operands (e.g. `and dst, src` where
/// both are spilled), the secondary spill register R10 is used for the Use
/// operand to avoid clobbering the UseDef operand's value in R11.
///
/// Spill slot N lives at `[RBP - isel_frame_size - (N+1)*8]`.
fn rewrite_with_spills(
    insts: &[VInst],
    inst_sources: &[Option<u32>],
    alloc_result: &AllocResult,
    isel_frame_size: i32,
) -> (Vec<PInst>, Vec<Option<u32>>) {
    let mut out = Vec::with_capacity(insts.len() * 2);
    let mut out_sources = Vec::with_capacity(insts.len() * 2);
    let mut ops_buf = Vec::new();
    let spill_gpr2 = Gpr::from_preg(SPILL_REG2);

    for (inst, &source) in insts.iter().zip(inst_sources.iter()) {
        ops_buf.clear();
        inst.reg_operands(&mut ops_buf);

        // Collect spilled operands with their details.
        struct SpilledOp {
            vreg_idx: u32,
            kind: OpKind,
            offset: i32,
        }
        let mut spilled: Vec<SpilledOp> = Vec::new();

        for op in &ops_buf {
            if let Some(&slot) = alloc_result.spill_map.get(&op.vreg.0) {
                let offset = -(isel_frame_size + (slot as i32 + 1) * 8);
                spilled.push(SpilledOp {
                    vreg_idx: op.vreg.0,
                    kind: op.kind,
                    offset,
                });
            }
        }

        if spilled.len() <= 1 {
            // Simple case: at most one spilled operand — use R11 only.
            for sp in &spilled {
                if matches!(sp.kind, OpKind::Use | OpKind::UseDef) {
                    out.push(MInst::MovRM {
                        size: OpSize::S64,
                        dst: Gpr::R11,
                        base: Gpr::Rbp,
                        offset: sp.offset,
                    });
                    out_sources.push(source);
                }
            }

            out.push(rewrite_inst(inst, &alloc_result.assignments));
            out_sources.push(source);

            for sp in &spilled {
                if matches!(sp.kind, OpKind::Def | OpKind::UseDef) {
                    out.push(MInst::MovMR {
                        size: OpSize::S64,
                        base: Gpr::Rbp,
                        offset: sp.offset,
                        src: Gpr::R11,
                    });
                    out_sources.push(source);
                }
            }
        } else {
            // Multiple spilled operands: use R10 for some operands and R11
            // for the others to avoid clobbering.
            //
            // Constraints:
            //  - Two spilled Defs MUST get different registers (the pseudo-
            //    instruction writes to both sequentially).
            //  - Two spilled Uses SHOULD get different registers (both are
            //    loaded before the instruction; the second load would
            //    clobber the first if they share R11).
            //  - A Use and a Def MAY share a register when the encoding
            //    consumes Uses before writing Defs (e.g. UMulOverflow).
            let spilled_uses: Vec<&SpilledOp> = spilled
                .iter()
                .filter(|sp| matches!(sp.kind, OpKind::Use))
                .collect();
            let spilled_defs: Vec<&SpilledOp> = spilled
                .iter()
                .filter(|sp| matches!(sp.kind, OpKind::Def | OpKind::UseDef))
                .collect();

            let mut r10_set: HashSet<u32> = HashSet::new();

            if spilled_defs.len() >= 2 {
                // Multiple Defs: assign R10 to the second Def.
                r10_set.insert(spilled_defs[1].vreg_idx);
                // If there are also 2+ spilled Uses, pair one Use with
                // the R10 Def to keep the Uses on separate registers.
                if spilled_uses.len() >= 2 {
                    r10_set.insert(spilled_uses[0].vreg_idx);
                }
            } else if let Some(sp) = spilled_uses.first() {
                // At most 1 Def: assign R10 to one Use (original behavior).
                r10_set.insert(sp.vreg_idx);
            }

            // Emit loads: Use/UseDef → R10 if in set, R11 otherwise.
            for sp in &spilled {
                if matches!(sp.kind, OpKind::Use | OpKind::UseDef) {
                    let is_r10 = r10_set.contains(&sp.vreg_idx) && matches!(sp.kind, OpKind::Use);
                    let dst_gpr = if is_r10 { spill_gpr2 } else { Gpr::R11 };
                    out.push(MInst::MovRM {
                        size: OpSize::S64,
                        dst: dst_gpr,
                        base: Gpr::Rbp,
                        offset: sp.offset,
                    });
                    out_sources.push(source);
                }
            }

            // Rewrite the instruction with R10 overrides for all designated operands.
            if !r10_set.is_empty() {
                let mut overrides = alloc_result.assignments.to_vec();
                for &vi in &r10_set {
                    overrides[vi as usize] = SPILL_REG2;
                }
                out.push(rewrite_inst(inst, &overrides));
                out_sources.push(source);
            } else {
                out.push(rewrite_inst(inst, &alloc_result.assignments));
                out_sources.push(source);
            }

            // Emit stores for Def/UseDef operands.
            for sp in &spilled {
                if matches!(sp.kind, OpKind::Def | OpKind::UseDef) {
                    let src_gpr = if r10_set.contains(&sp.vreg_idx) {
                        spill_gpr2
                    } else {
                        Gpr::R11
                    };
                    out.push(MInst::MovMR {
                        size: OpSize::S64,
                        base: Gpr::Rbp,
                        offset: sp.offset,
                        src: src_gpr,
                    });
                    out_sources.push(source);
                }
            }
        }
    }

    (out, out_sources)
}

/// Run regalloc + rewrite + prologue/epilogue on an IselResult.
/// Public for use in tests.
pub fn lower_isel_result(isel_result: &IselResult<VInst>) -> Vec<PInst> {
    let alloc_result = tuffy_regalloc::allocator::allocate(
        &isel_result.insts,
        isel_result.vreg_count,
        &isel_result.constraints,
        &isel_result.vreg_classes,
        &ALLOC_REGS,
        &CALLEE_SAVED_REGS,
        SPILL_REG,
        X86RegBank::aliases,
    );
    let (pinsts, pinst_sources) = rewrite_with_spills(
        &isel_result.insts,
        &isel_result.inst_sources,
        &alloc_result,
        isel_result.isel_frame_size,
    );
    let (pinsts, pinst_sources) = insert_prologue_epilogue(
        pinsts,
        pinst_sources,
        isel_result.isel_frame_size,
        alloc_result.spill_slots,
        isel_result.has_calls,
        &alloc_result.used_callee_saved,
    );
    remove_fallthrough_jumps(pinsts, pinst_sources).0
}

/// X86-64 code generation backend.
pub struct X86Backend;

impl Backend for X86Backend {
    fn compile_function(
        &self,
        func: &Function,
        symbols: &SymbolTable,
    ) -> Result<CompiledFunction, String> {
        // 1. Instruction selection → MInst<VReg>
        let isel_result = isel::isel(func, symbols)?;

        // 2. Register allocation → VReg assignments
        let alloc_result = tuffy_regalloc::allocator::allocate(
            &isel_result.insts,
            isel_result.vreg_count,
            &isel_result.constraints,
            &isel_result.vreg_classes,
            &ALLOC_REGS,
            &CALLEE_SAVED_REGS,
            SPILL_REG,
            X86RegBank::aliases,
        );

        // 3. Rewrite VReg → Gpr, inserting spill loads/stores
        let (pinsts, pinst_sources) = rewrite_with_spills(
            &isel_result.insts,
            &isel_result.inst_sources,
            &alloc_result,
            isel_result.isel_frame_size,
        );

        // 4. Insert prologue/epilogue
        let (final_insts, final_sources) = insert_prologue_epilogue(
            pinsts,
            pinst_sources,
            isel_result.isel_frame_size,
            alloc_result.spill_slots,
            isel_result.has_calls,
            &alloc_result.used_callee_saved,
        );
        let (final_insts, final_sources) = remove_fallthrough_jumps(final_insts, final_sources);

        // 5. Encode to machine code
        let enc = encode_function(&final_insts, &final_sources);
        let total_frame = isel_result.isel_frame_size + (alloc_result.spill_slots as i32) * 8;
        let has_frame_pointer =
            total_frame > 0 || isel_result.has_calls || !alloc_result.used_callee_saved.is_empty();

        // Compute sub_amount for FDE generation (same logic as frame.rs)
        let callee_save_bytes = alloc_result.used_callee_saved.len() as i32 * 8;
        let padding = if isel_result.has_calls { 8 } else { 0 };
        let total_needed = total_frame + callee_save_bytes + padding;
        let aligned_total = (total_needed + 15) & !15;
        let sub_amount = aligned_total - callee_save_bytes;

        let callee_saved_dwarf_regs: Vec<u8> = alloc_result
            .used_callee_saved
            .iter()
            .map(|p| preg_to_dwarf(*p))
            .collect();
        let debug = build_compiled_debug_info(
            func,
            &isel_result,
            &alloc_result,
            &enc.line_records,
            enc.code.len() as u32,
        );

        Ok(CompiledFunction {
            name: isel_result.name,
            code: enc.code,
            relocations: enc.relocations,
            debug,
            weak: false,
            local: false,
            has_frame_pointer,
            call_site_table: enc.call_site_table,
            callee_saved_dwarf_regs,
            sub_amount,
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
                debug: None,
                weak: false,
                local: false,
                has_frame_pointer: false,
                call_site_table: vec![],
                callee_saved_dwarf_regs: vec![],
                sub_amount: 0,
            });
        }
        funcs.push(CompiledFunction {
            name: shim_marker.to_string(),
            code: vec![0xc3],
            relocations: vec![],
            debug: None,
            weak: false,
            local: false,
            has_frame_pointer: false,
            call_site_table: vec![],
            callee_saved_dwarf_regs: vec![],
            sub_amount: 0,
        });
        funcs
    }

    fn generate_entry_point(&self, main_sym: &str, start_sym: &str) -> Vec<CompiledFunction> {
        let main_code = vec![
            0x55, // push rbp
            0x48, 0x89, 0xe5, // mov rbp, rsp
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
                offset: 16,
                symbol: main_sym.to_string(),
                kind: RelocKind::PcRel,
            },
            Relocation {
                offset: 23,
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
                debug: None,
                weak: false,
                local: false,
                has_frame_pointer: true,
                call_site_table: vec![],
                callee_saved_dwarf_regs: vec![],
                sub_amount: 0,
            },
            CompiledFunction {
                name: start_sym.to_string(),
                code: start_code,
                relocations: vec![],
                debug: None,
                weak: false,
                local: false,
                has_frame_pointer: true,
                call_site_table: vec![],
                callee_saved_dwarf_regs: vec![],
                sub_amount: 0,
            },
        ]
    }
}

/// Remove unconditional jumps whose target label is already the next emitted block.
fn remove_fallthrough_jumps(
    insts: Vec<PInst>,
    inst_sources: Vec<Option<u32>>,
) -> (Vec<PInst>, Vec<Option<u32>>) {
    let original_insts = insts;
    let mut out = Vec::with_capacity(original_insts.len());
    let mut out_sources = Vec::with_capacity(inst_sources.len());

    for (idx, (inst, source)) in original_insts.iter().cloned().zip(inst_sources).enumerate() {
        let keep = match &inst {
            MInst::Jmp { target } => !jump_falls_through(&original_insts, idx, *target),
            _ => true,
        };
        if keep {
            out.push(inst);
            out_sources.push(source);
        }
    }

    (out, out_sources)
}

/// Return whether a jump target is already reached by falling through to following labels.
fn jump_falls_through(insts: &[PInst], idx: usize, target: u32) -> bool {
    insts
        .iter()
        .skip(idx + 1)
        .take_while(|inst| matches!(inst, MInst::Label { .. }))
        .any(|inst| matches!(inst, MInst::Label { id } if *id == target))
}
