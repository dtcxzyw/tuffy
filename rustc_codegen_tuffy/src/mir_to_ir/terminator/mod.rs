//! Terminator translation for MIR → IR conversion.

use rustc_hir::LangItem;
use rustc_middle::mir::{self, AssertKind, InlineAsmOperand, Operand, TerminatorKind};
use rustc_middle::ty::{self, Instance, TypeVisitableExt, TypingEnv};

use num_bigint::BigInt;
use tuffy_ir::instruction::{ICmpOp, Origin};
use tuffy_ir::types::{Annotation, IntAnnotation, IntSignedness, Type};
use tuffy_ir::value::ValueRef;

use super::ctx::TranslationCtx;
use super::types::*;

/// Shared 64-bit unsigned annotation used for synthesized integer terminator values.
const I64: IntAnnotation = IntAnnotation {
    bit_width: 64,
    signedness: IntSignedness::Unsigned,
};

/// Drop terminator lowering, including drop glue calls.
mod drop_;
/// Inline assembly pattern lowering for recognized standard-library uses.
mod inline_asm;
/// Assert panic helper lowering.
mod panic;
/// Return terminator lowering, including SRET conventions.
mod return_;
/// `SwitchInt` lowering helpers.
mod switch;

impl<'a, 'tcx> TranslationCtx<'a, 'tcx> {
    /// Lowers one MIR terminator into Tuffy IR control flow.
    pub(super) fn translate_terminator(&mut self, term: &mir::Terminator<'tcx>) {
        match &term.kind {
            TerminatorKind::Return => {
                self.translate_return();
            }
            TerminatorKind::Goto { target } => {
                let target_block = self.block_map.get(*target);
                self.builder.br(
                    target_block,
                    vec![self.current_mem.into()],
                    Origin::synthetic(),
                );
            }
            TerminatorKind::SwitchInt { discr, targets } => {
                self.translate_switch_int(discr, targets);
            }
            TerminatorKind::Assert {
                cond,
                expected,
                msg,
                target,
                ..
            } => {
                let cond_val = self.translate_operand(cond);
                let target_block = self.block_map.get(*target);
                if let Some(cond_v) = cond_val {
                    let cond_v = self.coerce_to_int(cond_v);
                    let expected_val = self.builder.iconst(
                        if *expected { 1 } else { 0 },
                        64,
                        IntSignedness::DontCare,
                        Origin::synthetic(),
                    );
                    let cmp = self.builder.icmp(
                        ICmpOp::Eq,
                        cond_v.into(),
                        expected_val.into(),
                        Origin::synthetic(),
                    );
                    let panic_block = self.builder.create_block();
                    let panic_mem = self.builder.add_block_arg(panic_block, Type::Mem, None);
                    self.builder.brif(
                        cmp.into(),
                        target_block,
                        vec![self.current_mem.into()],
                        panic_block,
                        vec![self.current_mem.into()],
                        Origin::synthetic(),
                    );

                    // Build the panic call in the failure block.
                    self.builder.switch_to_block(panic_block);
                    self.current_mem = panic_mem;
                    self.emit_assert_panic(msg, term.source_info);
                } else {
                    self.builder.br(
                        target_block,
                        vec![self.current_mem.into()],
                        Origin::synthetic(),
                    );
                }
            }
            TerminatorKind::Unreachable => {
                self.builder.unreachable(Origin::synthetic());
            }
            TerminatorKind::Drop {
                place,
                target,
                unwind,
                ..
            } => {
                self.translate_drop(place, *target, unwind);
            }
            TerminatorKind::FalseEdge { real_target, .. } => {
                let target_block = self.block_map.get(*real_target);
                self.builder.br(
                    target_block,
                    vec![self.current_mem.into()],
                    Origin::synthetic(),
                );
            }
            TerminatorKind::FalseUnwind { real_target, .. } => {
                let target_block = self.block_map.get(*real_target);
                self.builder.br(
                    target_block,
                    vec![self.current_mem.into()],
                    Origin::synthetic(),
                );
            }
            TerminatorKind::Call {
                func,
                args,
                destination,
                target,
                unwind,
                ..
            } => {
                let cleanup_bb = match unwind {
                    mir::UnwindAction::Cleanup(cleanup_bb) => Some(*cleanup_bb),
                    _ => None,
                };
                self.translate_call(
                    func,
                    args,
                    destination,
                    target,
                    cleanup_bb,
                    term.source_info,
                );
            }
            TerminatorKind::InlineAsm {
                template,
                operands,
                targets,
                ..
            } => {
                self.translate_inline_asm(template, operands, targets);
            }
            TerminatorKind::UnwindResume => {
                // Resume unwinding: load the exception pointer from the
                // stack slot (stored by the landing-pad wrapper) and call
                // `_Unwind_Resume(exc_ptr)` to continue stack unwinding.
                if let Some(exc_slot) = self.exc_ptr_slot {
                    let exc_ptr = self.builder.load(
                        exc_slot.into(),
                        8,
                        Type::Ptr(0),
                        self.current_mem.into(),
                        None,
                        Origin::synthetic(),
                    );
                    let resume_sym = self.symbols.intern("_Unwind_Resume");
                    let resume_addr = self.builder.symbol_addr(resume_sym, Origin::synthetic());
                    let (_, _) = self.builder.call(
                        resume_addr.into(),
                        vec![exc_ptr.into()],
                        Type::Unit,
                        self.current_mem.into(),
                        None,
                        None,
                        Origin::synthetic(),
                    );
                }
                self.builder.unreachable(Origin::synthetic());
            }
            TerminatorKind::UnwindTerminate(_) => {
                // Terminate on double-panic: call core::panicking::panic_cannot_unwind.
                let def_id = self
                    .tcx
                    .require_lang_item(LangItem::PanicCannotUnwind, term.source_info.span);
                if let Some(instance) = Instance::try_resolve(
                    self.tcx,
                    TypingEnv::fully_monomorphized(),
                    def_id,
                    ty::List::empty(),
                )
                .ok()
                .flatten()
                {
                    let sym_name = self.tcx.symbol_name(instance).name.to_string();
                    let sym_id = self.symbols.intern(&sym_name);
                    let callee = self.builder.symbol_addr(sym_id, Origin::synthetic()).raw();
                    let (_, _) = self.builder.call(
                        callee.into(),
                        vec![],
                        Type::Unit,
                        self.current_mem.into(),
                        None,
                        None,
                        Origin::synthetic(),
                    );
                }
                self.builder.trap(Origin::synthetic());
            }
            _ => {
                // For any unhandled terminator (including Resume, Yield, etc.),
                // treat as a trap since we don't support exception handling
                // or async/generator constructs yet.
                self.builder.trap(Origin::synthetic());
            }
        }
    }

    /// Create a landing-pad wrapper block for a call with unwind cleanup.
    ///
    /// The wrapper captures the exception pointer from the unwinder,
    /// stores it to the shared `exc_ptr_slot`, and branches to the
    /// actual MIR cleanup block.
    pub(super) fn setup_cleanup_landing_pad(&mut self, cleanup_bb: mir::BasicBlock) -> u32 {
        // Create the wrapper IR block (no block args — entered by unwinder).
        let wrapper_block = self.builder.create_block();

        // Defer wrapper block population to after the main translation loop.
        self.landing_pad_wrappers.push((wrapper_block, cleanup_bb));
        wrapper_block.index()
    }
}
