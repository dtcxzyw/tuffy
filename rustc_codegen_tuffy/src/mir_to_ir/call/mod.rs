//! Call translation for MIR → IR conversion.

use rustc_middle::mir::{self, BasicBlock, Operand, Place};
use rustc_middle::ty::{self, Instance, TyCtxt, TypeVisitableExt};
use rustc_span::Spanned;

use tuffy_ir::instruction::{Operand as IrOperand, Origin};
use tuffy_ir::types::{Annotation, IntAnnotation, IntSignedness, Type};
use tuffy_ir::value::ValueRef;

use super::ctx::TranslationCtx;
use super::intrinsic::intrinsic_to_libc;
use super::types::*;

/// Resolved call target: direct symbol or virtual dispatch.
pub(super) enum CallTarget {
    /// Direct call to a named symbol.
    Direct(String),
    /// Virtual dispatch: load function pointer from vtable at given index.
    Virtual(usize),
}

/// Result of resolving a call target, including caller-location metadata.
pub(super) struct ResolvedCall<'tcx> {
    /// Resolved direct or virtual callee target, if codegen can determine one.
    pub(super) target: Option<CallTarget>,
    /// True if the callee has `#[track_caller]` and expects an implicit
    /// `&Location` as the last ABI argument.
    pub(super) requires_caller_location: bool,
    /// True when `Instance::try_resolve` resolved through a blanket impl
    /// that strips a reference level from Self (e.g. `<&mut Formatter as
    /// Write>::write_fmt` → `<Formatter as Write>::write_fmt`).  The MIR
    /// passes `&mut &mut Formatter` but the resolved callee expects
    /// `&mut Formatter`, so the first argument needs a dereference.
    pub(super) needs_self_deref: bool,
    /// The resolved Instance, if available. Used to compile `#[inline]`
    /// functions not collected as mono items.
    pub(super) resolved_instance: Option<Instance<'tcx>>,
    /// True when the call goes through Fn::call / FnMut::call_mut /
    /// FnOnce::call_once and resolves to a closure body.  The caller
    /// passes args as a single tuple but the closure body expects
    /// individual parameters — the tuple must be spread at the call site.
    pub(super) needs_tuple_spread: bool,
}

/// Call lowering and ABI/result handling.
mod emit;
/// Inline compiler-intrinsic call handling.
mod intrinsic;
/// Callee resolution and dispatch-shape analysis.
mod resolve;

use resolve::resolve_call_target;
