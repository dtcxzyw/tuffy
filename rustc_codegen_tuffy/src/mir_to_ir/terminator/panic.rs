use super::*;

impl<'a, 'tcx> TranslationCtx<'a, 'tcx> {
    /// Emits the backend panic call for a failed MIR assert.
    pub(super) fn emit_assert_panic(
        &mut self,
        msg: &AssertKind<Operand<'tcx>>,
        source_info: mir::SourceInfo,
    ) {
        let tcx = self.tcx;
        let location = self.make_caller_location(source_info);

        // Determine the lang item and build arguments.
        let (lang_item, args) = match msg {
            AssertKind::BoundsCheck { len, index } => {
                let mut call_args: Vec<tuffy_ir::instruction::Operand> = Vec::with_capacity(3);
                if let Some(idx) = self.translate_operand(index) {
                    let idx = self.coerce_to_int(idx);
                    call_args.push(idx.into());
                }
                if let Some(len_v) = self.translate_operand(len) {
                    let len_v = self.coerce_to_int(len_v);
                    call_args.push(len_v.into());
                }
                call_args.push(location.into());
                (LangItem::PanicBoundsCheck, call_args)
            }
            AssertKind::MisalignedPointerDereference { required, found } => {
                let mut call_args: Vec<tuffy_ir::instruction::Operand> = Vec::with_capacity(3);
                if let Some(req) = self.translate_operand(required) {
                    let req = self.coerce_to_int(req);
                    call_args.push(req.into());
                }
                if let Some(fnd) = self.translate_operand(found) {
                    let fnd = self.coerce_to_int(fnd);
                    call_args.push(fnd.into());
                }
                call_args.push(location.into());
                (LangItem::PanicMisalignedPointerDereference, call_args)
            }
            _ => {
                // All other assert kinds use panic_const_* functions
                // which take only the implicit #[track_caller] location.
                (msg.panic_function(), vec![location.into()])
            }
        };

        // Resolve the lang item to a function Instance and get its symbol.
        let def_id = tcx.require_lang_item(lang_item, source_info.span);
        if let Some(instance) = Instance::try_resolve(
            tcx,
            TypingEnv::fully_monomorphized(),
            def_id,
            ty::List::empty(),
        )
        .ok()
        .flatten()
        {
            let sym_name = tcx.symbol_name(instance).name.to_string();
            let sym_id = self.symbols.intern(&sym_name);
            let callee = self.builder.symbol_addr(sym_id, Origin::synthetic()).raw();

            let (call_mem, _call_data) = self.builder.call(
                callee.into(),
                args,
                Type::Unit,
                self.current_mem.into(),
                None,
                None,
                Origin::synthetic(),
            );
            self.current_mem = call_mem.raw();
        }

        // The panic function diverges, so terminate with unreachable.
        self.builder.trap(Origin::synthetic());
    }
}
