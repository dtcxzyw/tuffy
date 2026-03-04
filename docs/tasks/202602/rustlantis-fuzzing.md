# Rustlantis Differential Fuzzing for rustc_codegen_tuffy

- Status: In Progress
- Created: 2026-02-27
- Completed: N/A


- Parent: N/A

## Description

Use [Rustlantis](https://github.com/cbeuw/rustlantis) to differential-test `rustc_codegen_tuffy` against the LLVM backend. Rustlantis generates random, UB-free, deterministic custom MIR programs and compares execution output across compiler backends. Any output mismatch indicates a bug in the backend under test.

### Setup

Rustlantis is cloned to `/tmp/rustlantis`. A patch adding the `Tuffy` backend type, a `config.toml`, and a standalone `fuzz.sh` script are stored in `rustc_codegen_tuffy/rustlantis/patch/`.

To set up from a fresh clone:

```bash
git clone https://github.com/cbeuw/rustlantis.git /tmp/rustlantis
cd /tmp/rustlantis
git apply /tuffy/rustc_codegen_tuffy/rustlantis/patch/tuffy-backend.patch
cp /tuffy/rustc_codegen_tuffy/rustlantis/patch/config.toml .
cp /tuffy/rustc_codegen_tuffy/rustlantis/patch/fuzz.sh .
cargo build --release
```

### Running

Two approaches are available:

1. Built-in difftest framework: `./fuzz-one.sh <seed>`
2. Standalone script: `./fuzz.sh <start_seed> <end_seed> [jobs]`

The standalone script supports parallel execution. The optional `jobs` parameter controls concurrency (defaults to `nproc`). Examples:

```bash
./fuzz.sh 0 1000        # Use all CPU cores
./fuzz.sh 0 1000 8      # Use 8 parallel jobs
```

Both compare tuffy output against LLVM with `-Zmir-opt-level=3`.

Hints:
- Adjust `config.toml` to generate smaller inputs (fewer basic blocks, functions, args, etc.) when debugging — smaller programs are much easier to minimize and reason about. The shipped config already uses reduced values compared to upstream defaults.
- Use `minimise.py` to reduce a reproducer: copy the failing program to `repro.rs` in the rustlantis directory, then run `python3 minimise.py`. It iteratively comments out or replaces MIR statements with `Return()`, keeping only lines needed to reproduce the bug. Output goes to `minimised.rs`.
- Always minimize reproducers before reading them. Raw generated programs contain a lot of noise; minimised versions isolate the root cause much faster.

## Results (2026-02-28)

### Run 1 (pre-fix baseline)

Seeds 0–1000:

| Category | Count | % of total |
|----------|------:|-----:|
| Pass | 396 | 39.6 |
| Crash (compile fail) | 602 | 60.2 |
| Mismatch (wrong code) | 3 | 0.3 |

### Run 2 (after bswap + u128 + legalization fixes)

Seeds 0–1000:

| Category | Count | % of total |
|----------|------:|-----:|
| Pass | 721 | 72.0 |
| Crash (compile fail) | 0 | 0.0 |
| Mismatch (runtime crash) | 263 | 26.3 |
| Mismatch (wrong code) | 17 | 1.7 |

Compile crashes eliminated entirely. 325 previously-crashing seeds now
pass. The remaining 280 mismatches are mostly runtime crashes (segfaults)
with 17 silent wrong-code bugs producing different hash output.

### Mismatches

All 3 mismatches fixed:

| Seed | Root cause | Fix |
|------|-----------|-----|
| 792 | 2-byte bswap isel extracted wrong byte (shl 56 + sar 56 sign-extended low byte instead of extracting high byte) | Replace with and 0xFF00 + sar 8 |
| 881 | Same bswap bug as seed 792 | Same fix |
| 721 | Three u128 codegen bugs: (1) switch constants truncated to i64, (2) switch discriminant compared address instead of loaded value, (3) unary NOT applied to address instead of loaded value | Load u128 values from pointers; use BigInt for switch constants; pre-create blocks in legalization |

### Run 3 (after 1-tuple spreading fix)

Seeds 0–10:

| Category | Count | % of total |
|----------|------:|-----:|
| Pass | 11 | 100.0 |
| Crash | 0 | 0.0 |
| Mismatch | 0 | 0.0 |

Seed 3 was previously crashing at runtime due to a codegen bug in 1-tuple argument
spreading (see fix below). After the fix, all 11 seeds pass.

| Seed | Root cause | Fix |
|------|-----------|-----|
| 3 | 1-tuple spread skipped: `FnOnce::call_once` passes args as `(&T,)` 1-tuple; codegen skipped spreading for 1-tuples, passing the stack address (`&&T`) instead of loading and passing the value (`&T`) | Change spreading threshold from `>= 2` to `>= 1` non-ZST fields in `call.rs` |

### Run 4 (2026-03-03)

Seeds 0–100 (parallel execution with 48 jobs):

| Category | Count | % of total |
|----------|------:|-----:|
| Pass | 100 | 99.0 |
| Crash | 0 | 0.0 |
| Mismatch | 1 | 1.0 |

Seed 61 mismatch fixed. Root cause: when MIR optimization converts tuple arguments to constants (e.g., `Move(_1)` → `const (42_i32,)`), `translate_operand` returns a pointer to the constant data. For small aggregates (≤8 bytes) passed by value, the pointer was being passed directly instead of loading the value first. This caused the callee to receive a pointer address instead of the tuple value, producing different hash output.

| Seed | Root cause | Fix |
|------|-----------|-----|
| 61 | Constant tuple arguments (≤8 bytes) passed as pointers instead of values in optimized MIR | Load value from constant address before passing as argument in `call.rs` |

### Run 5 (2026-03-04)

Seeds 0–1000 (parallel execution with 48 jobs):

| Category | Count | % of total |
|----------|------:|-----:|
| Pass | 992 | 99.2 |
| Crash | 0 | 0.0 |
| Mismatch (wrong code) | 8 | 0.8 |
| Mismatch (runtime crash) | 1 | 0.1 |

Pass rate improved from 72% (Run 2) to 99.2%. All compilation crashes eliminated. 9 mismatches remain:

Mismatching seeds: 266, 347, 391, 490, 669, 731, 922, 944, 993

- Seed 347: runtime crash (core dump)
- Seeds 266, 391, 490, 669, 731, 922, 944, 993: wrong code (different hash output)

### Run 6 (2026-03-04) - u128 to f32 conversion fix

Seed 347 investigation revealed missing u128/i128 to float conversion support. The conversion was failing in isel because legalization splits u128 values into (lo, hi) pairs, but SiToFp/UiToFp weren't being legalized for 128-bit operands.

| Seed | Root cause | Fix |
|------|-----------|-----|
| 347 | u128/i128 to f32/f64 conversions not implemented in legalization | Add leg_int128_to_fp function to emit libcalls to compiler_builtins (__floatuntisf, __floatuntidf, __floattisf, __floattidf) |

After the fix, seed 347 passes with optimizations enabled.

**Important discovery**: Previous fuzzing campaigns (Runs 1-5) used optimized builds (`-Zmir-opt-level=3 -C opt-level=3`), but the fuzz_campaign.sh script uses unoptimized builds (no opt-level flags). Testing with unoptimized builds reveals different bugs.

Seeds 0–100 (unoptimized builds, parallel execution with 48 jobs):

| Category | Count | % of total |
|----------|------:|-----:|
| Pass | 98 | 97.0 |
| Crash | 0 | 0.0 |
| Mismatch | 3 | 3.0 |

Remaining mismatches in unoptimized builds:
- Seed 7: produces different hash (tuffy: 4739852885392749089, llvm: 8704362819882979984)
- Seed 29: exit code 139 (SIGSEGV)
- Seed 52: exit code 132 (SIGILL)

All three seeds pass when compiled with optimizations, indicating bugs specific to unoptimized code generation.

### Run 7 (2026-03-04) - Additional unoptimized build fixes

Fixed two additional issues affecting unoptimized builds:

| Seed | Root cause | Fix |
|------|-----------|-----|
| N/A | Uninitialized float return values caused IR verification failures | Bitcast integer zero to float type when returning uninitialized float values in terminator.rs |
| 52 | u128 to f64 conversion failed in isel despite legalization fix | Check operand annotations in addition to wide set for detecting 128-bit values in legalization |

Seeds 0–100 (unoptimized builds, after fixes):

| Category | Count | % of total |
|----------|------:|-----:|
| Pass | 99 | 98.0 |
| Crash | 0 | 0.0 |
| Mismatch | 2 | 2.0 |

Remaining mismatches in unoptimized builds:
- Seed 7: exit code 139 (SIGSEGV)
- Seed 29: exit code 139 (SIGSEGV)

Both seeds pass when compiled with optimizations. Seed 52 is now fixed.

### Run 8 (2026-03-04) - i128 struct field store fix

Fixed i128/u128 field assignment bug affecting both constants and operations:

| Seed | Root cause | Fix |
|------|-----------|-----|
| 29 (partial) | i128 field stores checked only MIR type size, not actual IR value width. Constants like 42_i128 return iconst (8 bytes) but code did store.16, writing garbage. Operations like i128*i128 produce true 128-bit values but annotation was lost in ValueRef, causing incorrect scalar extension. | Check rvalue type to distinguish true 128-bit operations (BinaryOp/UnaryOp on i128/u128) from constants. Constants use scalar extension path, operations use full-width store for legalization. |

After the fix:
- Simple i128 constant test now produces correct output (42 instead of garbage)
- Seed 29 IR improved from store.8 to store.16 for multiplication, but still crashes at runtime
- Seed 7 now produces output (wrong hash) instead of crashing

The fix resolves the i128 constant assignment issue but seeds 7 and 29 have additional bugs causing runtime failures.

#### Seed 7 Investigation

Seed 7 minimizes to a u128 multiplication being hashed:
```rust
_2 = 127205287323746125276397411379526629301_u128 * 334158389699225244992710105631410377972_u128;
Call(_6 = dump_var(Move(_1), Move(_2), _7, _7), ReturnTo(bb7), UnwindUnreachable())
```

Findings:
- Tuffy produces hash: 799248379550295712
- LLVM produces hash: 370434447370778688
- u128 multiplication works correctly in isolation (verified with standalone test)
- u128 constants are stored correctly (verified with standalone test)
- Issue appears to be in how u128 values are passed to generic functions (impl Hash)
- IR shows u128 passed as single annotated operand, but backend may not handle this correctly

The bug is likely in the legalization or code generation for u128 function arguments.

#### Seed 29 Investigation

Seed 29 minimizes to two assignments to RET.fld1:
```rust
RET.fld1 = 74045951570396969358155043307167018649_i128 * (-84426674019192898531552418757191699584_i128);
Call(RET.fld1 = core::intrinsics::transmute(_3), ReturnTo(bb1), UnwindUnreachable())
```

Findings:
- Crashes with SIGSEGV (exit code 139) at runtime
- IR shows both stores to RET.fld1 at offset 0 instead of correct field offset
- Simple field assignment tests work correctly, so field_offset calculation is fine
- Issue is specific to how Call results are assigned to struct fields
- The Call destination handling may not be calculating field offsets correctly

Both seeds require further investigation into calling conventions and Call destination handling.

- [x] Run initial fuzzing campaign (seeds 0..1000) and triage results
- [x] Classify failures into compile crashes vs output mismatches
- [x] Minimize reproduction cases for each distinct bug
- [x] Fix identified codegen bugs in rustc_codegen_tuffy
- [x] Fix u128/i128 to float conversion (seed 347, seed 52)
- [x] Fix uninitialized float return IR verification
- [x] Fix i128 struct field store bug (partial - constants fixed, seeds 7/29 have additional issues)
- [ ] Fix remaining unoptimized build failures (seeds 7, 29)
- [ ] Increase config complexity as pass rate improves

## Affected Modules

- `rustc_codegen_tuffy` — codegen backend under test
- `tuffy_codegen/src/legalize.rs` — u128 to float conversion legalization
- `rustc_codegen_tuffy/src/mir_to_ir/terminator.rs` — uninitialized float return handling
