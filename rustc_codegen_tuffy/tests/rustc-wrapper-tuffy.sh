#!/bin/bash
# RUSTC_WRAPPER script for selective tuffy backend injection.
#
# Cargo's RUSTC_WRAPPER calling convention: $1 is the path to rustc,
# remaining args are passed directly to rustc.
#
# Injects -Z codegen-backend=$TUFFY_BACKEND only when:
#   - The crate being compiled is named $TUFFY_CRATE (default: "bitflags")
#   - The crate-type is not "proc-macro"
#   - TUFFY_BACKEND is set
#
# All other crates (dependencies, dev-deps, proc-macros) use the default backend.

RUSTC="$1"
shift

crate_name=""
is_proc_macro=0
prev=""
for arg in "$@"; do
    [[ "$prev" == "--crate-name" ]] && crate_name="$arg"
    [[ "$arg" == "proc-macro" || "$arg" == "--crate-type=proc-macro" ]] && is_proc_macro=1
    prev="$arg"
done

if [[ "$crate_name" == "${TUFFY_CRATE:-bitflags}" && "$is_proc_macro" -eq 0 && -n "${TUFFY_BACKEND:-}" ]]; then
    exec "$RUSTC" "$@" -Z "codegen-backend=$TUFFY_BACKEND"
else
    exec "$RUSTC" "$@"
fi
