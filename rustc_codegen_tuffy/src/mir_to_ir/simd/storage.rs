//! SIMD temporary stack materialization helpers.

use super::*;

impl<'a, 'tcx> TranslationCtx<'a, 'tcx> {
    /// Ensure a SIMD value is on the stack.
    pub(crate) fn ensure_simd_on_stack(&mut self, val: ValueRef, size: u32) -> ValueRef {
        macro_rules! o {
            () => {
                Origin::synthetic()
            };
        }
        if matches!(self.builder.value_type(val), Some(Type::Ptr(_))) {
            val
        } else {
            let store_size = if size <= 8 { 8 } else { size };
            let slot = self.builder.stack_slot(store_size, 0, o!());
            self.current_mem = self
                .builder
                .store(
                    val.into(),
                    slot.into(),
                    store_size.min(8),
                    self.current_mem.into(),
                    o!(),
                )
                .raw();
            slot
        }
    }

    /// Load the result from a stack slot as Int if the SIMD type fits in
    /// a register (≤8 bytes), otherwise leave as a stack pointer.
    pub(crate) fn simd_result_from_stack(&mut self, slot: ValueRef, size: u32) -> ValueRef {
        macro_rules! o {
            () => {
                Origin::synthetic()
            };
        }
        if size <= 8 {
            let u64_opt = Some(Annotation::Int(IntAnnotation {
                bit_width: 64,
                signedness: IntSignedness::Unsigned,
            }));
            self.builder.load(
                slot.into(),
                8,
                Type::Int,
                self.current_mem.into(),
                u64_opt.clone(),
                o!(),
            )
        } else {
            slot
        }
    }
}
