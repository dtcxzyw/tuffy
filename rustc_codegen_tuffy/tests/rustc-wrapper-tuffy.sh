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
#   - If TUFFY_SRC_DIR is set, the source file must be under that directory
#     (prevents applying tuffy to same-named crates from the cargo registry
#     when they are compiled as host dependencies for proc-macros)
#
# All other crates (dependencies, dev-deps, proc-macros) use the default backend.

RUSTC="$1"
shift

crate_name=""
is_proc_macro=0
src_file=""
prev=""
for arg in "$@"; do
    [[ "$prev" == "--crate-name" ]] && crate_name="$arg"
    [[ "$arg" == "proc-macro" || "$arg" == "--crate-type=proc-macro" ]] && is_proc_macro=1
    # The source file is the .rs argument (not preceded by a flag expecting a value)
    [[ "$arg" == *.rs && "$prev" != "--edition" && "$prev" != "--crate-name" && "$prev" != "-C" ]] && src_file="$arg"
    prev="$arg"
done

use_tuffy=0
if [[ "$crate_name" == "${TUFFY_CRATE:-bitflags}" && "$is_proc_macro" -eq 0 && -n "${TUFFY_BACKEND:-}" ]]; then
    if [[ -z "${TUFFY_SRC_DIR:-}" ]]; then
        use_tuffy=1
    elif [[ "$src_file" == "${TUFFY_SRC_DIR}"/* ]]; then
        use_tuffy=1
    fi
fi

if [[ "$use_tuffy" -eq 1 ]]; then
    exec "$RUSTC" "$@" -Z "codegen-backend=$TUFFY_BACKEND"
else
    exec "$RUSTC" "$@"
fi
