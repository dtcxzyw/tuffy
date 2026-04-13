use std::path::PathBuf;

use rustc_codegen_ssa::TargetConfig;
use rustc_session::Session;
use rustc_session::config::{DebugInfo, InstrumentCoverage, Lto, OptLevel};
use rustc_span::Symbol;
use tuffy_ir::debug::FunctionDebugInfo;

#[derive(Clone, Debug)]
/// Backend options derived from the active rustc session.
pub(crate) struct BackendOptions {
    /// Whether to print each translated function as Tuffy IR.
    pub dump_ir: bool,
    /// Optional output path for the concatenated module dump.
    pub dump_module_path: Option<PathBuf>,
    /// Whether to run `tuffy_opt` on emitted IR batches.
    pub run_tuffy_opt: bool,
    /// Whether to print backend timing diagnostics to stderr.
    pub trace_timings: bool,
    /// Requested rustc debuginfo level.
    pub debuginfo: DebugInfo,
}

impl BackendOptions {
    /// Builds backend options from the current rustc session.
    pub(crate) fn from_session(sess: &Session) -> Self {
        let dump_ir = sess.opts.cg.llvm_args.iter().any(|arg| arg == "dump-ir");
        let dump_module_path = sess
            .opts
            .cg
            .llvm_args
            .iter()
            .find_map(|arg| arg.strip_prefix("dump-module="))
            .map(PathBuf::from);
        let run_tuffy_opt = should_run_tuffy_opt(sess.opts.optimize);
        let trace_timings = std::env::var_os("TUFFY_TRACE_TIMINGS").is_some();
        let debuginfo = sess.opts.cg.debuginfo;

        Self {
            dump_ir,
            dump_module_path,
            run_tuffy_opt,
            trace_timings,
            debuginfo,
        }
    }

    /// Returns whether the backend should emit any debug records.
    pub(crate) fn emit_debuginfo(&self) -> bool {
        self.debuginfo != DebugInfo::None
    }

    /// Returns whether variable-level debug bindings should be preserved.
    pub(crate) fn retain_variable_debuginfo(&self) -> bool {
        matches!(self.debuginfo, DebugInfo::Limited | DebugInfo::Full)
    }

    /// Clones `func` and removes debug payloads that the selected mode does not keep.
    pub(crate) fn strip_debug_for_codegen(
        &self,
        func: &tuffy_ir::function::Function,
    ) -> tuffy_ir::function::Function {
        if self.emit_debuginfo() && self.retain_variable_debuginfo() {
            return func.clone();
        }
        let mut stripped = func.clone();
        if !self.emit_debuginfo() {
            stripped.debug = FunctionDebugInfo::default();
        } else {
            stripped.debug.variables.clear();
            stripped.debug.bindings.clear();
        }
        stripped
    }
}

/// Returns whether module-level Tuffy optimization should run at this opt level.
fn should_run_tuffy_opt(opt_level: OptLevel) -> bool {
    !matches!(opt_level, OptLevel::No)
}

/// Validates rustc options that this backend supports before codegen starts.
pub(crate) fn init(sess: &Session) {
    match sess.lto() {
        Lto::No | Lto::ThinLocal => {}
        Lto::Thin | Lto::Fat => sess
            .dcx()
            .warn("LTO is not supported by rustc_codegen_tuffy. You may get a linker error."),
    }

    if sess.opts.cg.instrument_coverage() != InstrumentCoverage::No {
        sess.dcx()
            .fatal("`-Cinstrument-coverage` is not supported by rustc_codegen_tuffy");
    }
}

/// Builds the rustc target feature view exposed by this backend.
pub(crate) fn target_config(sess: &Session) -> TargetConfig {
    let features: Vec<Symbol> = sess
        .target
        .rust_target_features()
        .iter()
        .filter(|(feature, _, _)| matches!(*feature, "x87" | "sse" | "sse2" | "fxsr"))
        .flat_map(|(feature, _, _)| {
            sess.target
                .implied_target_features(feature)
                .into_iter()
                .map(Symbol::intern)
        })
        .collect();

    TargetConfig {
        target_features: features.clone(),
        unstable_target_features: features,
        has_reliable_f16: false,
        has_reliable_f16_math: false,
        has_reliable_f128: false,
        has_reliable_f128_math: false,
    }
}

#[cfg(test)]
mod tests {
    use super::should_run_tuffy_opt;
    use rustc_session::config::OptLevel;

    #[test]
    fn enables_tuffy_opt_for_non_o0_levels() {
        assert!(!should_run_tuffy_opt(OptLevel::No));
        assert!(should_run_tuffy_opt(OptLevel::Less));
        assert!(should_run_tuffy_opt(OptLevel::More));
        assert!(should_run_tuffy_opt(OptLevel::Aggressive));
        assert!(should_run_tuffy_opt(OptLevel::Size));
        assert!(should_run_tuffy_opt(OptLevel::SizeMin));
    }
}
