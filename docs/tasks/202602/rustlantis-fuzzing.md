# Rustlantis Differential Fuzzing for rustc_codegen_tuffy

- Status: Completed
- Created: 2026-02-27
- Completed: 2026-03-06


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

Use the Python script for fuzzing:

```bash
cd /tmp/rustlantis
python3 /tuffy/rustc_codegen_tuffy/rustlantis/patch/fuzz.py <start_seed> <end_seed> [jobs]
```

The script supports parallel execution. The optional `jobs` parameter controls concurrency (defaults to `nproc`). Examples:

```bash
python3 /tuffy/rustc_codegen_tuffy/rustlantis/patch/fuzz.py 0 1000      # Use all CPU cores
python3 /tuffy/rustc_codegen_tuffy/rustlantis/patch/fuzz.py 0 1000 8    # Use 8 parallel jobs
```

The script uses `-Zmir-opt-level=0` (unoptimized MIR) and `-C opt-level=3` (LLVM optimizations) to compare tuffy output against LLVM.

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
- IR shows both stores to RET.fld1 at offset 0
- **Field offset investigation (2026-03-04)**: Verified that offset 0 is CORRECT. rustc reorders struct fields to minimize padding: fld1 (i128, 16-byte aligned) is placed at offset 0, fld0 (u16) is placed at offset 16. Simple test cases work correctly with this layout.
- The crash is NOT caused by incorrect field offsets
- Issue is likely in i128 multiplication legalization or codegen
- LLVM version works correctly, tuffy version crashes

Both seeds require further investigation. The field offset calculation is working correctly, so the bugs are elsewhere in the codegen pipeline.

### Run 9 (2026-03-05) - u128 wrapping_mul fix

Fixed two bugs causing incorrect u128 `wrapping_mul` results in unoptimized builds (seeds 7 and 29):

| Bug | Root cause | Fix |
|-----|-----------|-----|
| u128 return hi-word always zero | `leg_ret` always emitted `iconst 0` for the hi half of a non-wide 128-bit return, discarding the pre-legalization `rdx_moves` entry | Added `get_secondary_return_move` to `AbiMetadata` trait; implemented in `X86AbiMetadata` using `rdx_moves`; updated `leg_ret` to use the actual hi source |
| u128 wrapping_mul computes wrong cross-terms | Regalloc assigned a class-0 (GPR) vreg to PReg(32) (XMM0, class-1) when all GPRs were occupied. `Gpr::from_preg(PReg(32))` silently maps to Rax via `ALL_GPRS[32 & 0x1F]`, causing two vregs to both rewrite to Rax | In `spill_at` and `handle_fixed`, filter candidate registers by vreg class (`p.0 >> 5 == vreg_class`) so GPR vregs only get assigned GPR physical registers |

Seeds 0–100 (unoptimized builds):

| Category | Count | % of total |
|----------|------:|-----:|
| Pass | 101 | 100.0 |
| Crash | 0 | 0.0 |
| Mismatch | 0 | 0.0 |

All seeds 0–100 now pass in both optimized and unoptimized builds.

- [x] Run initial fuzzing campaign (seeds 0..1000) and triage results
- [x] Classify failures into compile crashes vs output mismatches
- [x] Minimize reproduction cases for each distinct bug
- [x] Fix identified codegen bugs in rustc_codegen_tuffy
- [x] Fix u128/i128 to float conversion (seed 347, seed 52)
- [x] Fix uninitialized float return IR verification
- [x] Fix i128 struct field store bug (partial - constants fixed, seeds 7/29 have additional issues)
- [x] Fix u128 return hi-word and regalloc class-filter bugs (seeds 7, 29)

### Run 10 (2026-03-05) - Float GPR/XMM class fixes and large u128 constant stores

Fixed two remaining bug classes found in seeds 0–1000:

| Bug | Affected Seeds | Root cause | Fix |
|-----|---------------|-----------|-----|
| Float register class mismatch | 168, 489 | Float IR values were allocated to XMM VRegs (class 1). When returned or passed in GPRs, `MovRR` emitted a no-op `mov rax,rax`. Float ops that received GPR values used `xmm_to_iced(src)` mapping GPR index to wrong XMM register. | Added `GprToXmm` pseudo-instruction (mov to `[rsp-8]` + movss/movsd from `[rsp-8]`); all float ops now keep results in GPR class; XMM used only as scratch within ops |
| Large 128-bit constant wide-store | 495, 543, 767, 929 | `val_is_wide` returned `false` for `Rvalue::Use(Operand::Constant(_))`, forcing large 128-bit constants through scalar extension path where hi word was always `iconst(0)` | Evaluate constant and check if bits fit in i64/u64; return `true` (wide path via `leg_wide_const`) only for values exceeding 64-bit range |

Seeds 0–1000 (unoptimized builds):

| Category | Count | % of total |
|----------|------:|-----:|
| Pass | 1001 | 100.0 |
| Crash | 0 | 0.0 |
| Mismatch | 0 | 0.0 |

All 1001 seeds (0–1000) now pass. 0 crashes, 0 mismatches.

### Run 11 (2026-03-04) - i128/u128 to float libcall fix

Seeds 1001–2000 found one mismatch:

| Seed | Root cause | Fix |
|------|-----------|-----|
| 1379 | Two bugs in `__floattidf`/`__floattisf` libcall emission: (1) `select_call` always allocated RAX for the return value, but C ABI returns floats in XMM0; (2) `leg_int128_to_fp` used `vmap.pair` which returns `(v, v)` for small 128-bit values (Mapped::One), so both lo and hi were set to the same value instead of hi being sign-extended/zero | In `select_call`: detect float return type and use `alloc_fixed(PReg(0x20))` (XMM0) + `MoveXmmToGpr` for the return; in `leg_int128_to_fp`: if not wide, compute hi as `SAR(lo, 63)` for i128 or `iconst(0)` for u128 |

Seeds 0–2000 (unoptimized builds):

| Category | Count | % of total |
|----------|------:|-----:|
| Pass | 2001 | 100.0 |
| Crash | 0 | 0.0 |
| Mismatch | 0 | 0.0 |

All 2001 seeds (0–2000) pass. 0 crashes, 0 mismatches.

### Run 12 (2026-03-04) - Struct return legalization and partial store overflow fixes

Seeds 2001–5000 found two bugs:

| Bug | Affected Seeds | Root cause | Fix |
|-----|---------------|-----------|-----|
| Secondary return move dropped by legalization | 2306 | Default `Op::Ret` handler in `legalize.rs` creates a new ret instruction at a new index but does not remap the `secondary_return_move` metadata from old index to new. isel's Ret handler then finds no rdx_moves entry and leaves RDX stale, corrupting the upper half of multi-register struct returns | Added remapping in default `Op::Ret` handler: check `old_meta.get_secondary_return_move(old_vref.index())`, remap the source via vmap, and call `s.meta.mark_secondary_return_move(new_ret.index(), new_src.index())` |
| Non-power-of-2 byte stores overflow into adjacent memory | 2306 | `bytes_to_opsize(3) = S64` caused 3-byte stores (e.g. `[u8;3]` fields) to emit 8-byte MOV instructions, overwriting adjacent stack memory including saved rbp | Added `emit_partial_store` helper in `isel.rs` that splits sizes 3,5,6,7 into multiple standard-size stores (3=2+1, 5=4+1, 6=4+2, 7=4+2+1) |
| Address-taken non-param locals > 16 bytes get no stack slot | 2020 | Address-taken prescan in `mod.rs` had an early-return for `size > 16` that only called `stack_locals.mark()` without allocating a slot. This was intended for large parameters (already passed by pointer), but incorrectly applied to local variables. The `translate_rvalue` RawPtr handler then returned None (no slot address), leaving the destination pointer local uninitialized | Changed `if size > 16` to `if size > 16 && local.as_usize() <= mir.arg_count` so only true parameters use the no-slot path; non-param locals > 16 bytes now get a proper stack slot |

Seeds 0–5000 (unoptimized builds):

| Category | Count | % of total |
|----------|------:|-----:|
| Pass | 5001 | 100.0 |
| Crash | 0 | 0.0 |
| Mismatch | 0 | 0.0 |

All 5001 seeds (0–5000) pass. 0 crashes, 0 mismatches.

### Run 13 (2026-03-05) - i128 call argument legalization fixes (optimized builds)

Seeds 0–1000 with `-Zmir-opt-level=3 -C opt-level=3` (optimized builds) found two bugs:

| Bug | Affected Seeds | Root cause | Fix |
|-----|---------------|-----------|-----|
| `has_wide_values` misses call operand annotations | 391, 669 | `has_wide_values()` in `legalize.rs` did not scan call instruction argument annotations. When an i128/u128 constant fitting in u64 was passed directly to a call with `:s128`/`:u128` annotation, legalization was skipped entirely. isel then passed only one argument in RDI instead of two (lo in RDI, hi in RSI) | Added `Op::Call(_, args, _) if args.iter().any(|a| is_128(a.annotation))` match arm to return true early |
| `leg_call` uses wrong hi for i128 constants | 266, 490, 731, 922, 944, 125, 970 | In the `else if is_128(arg.annotation)` branch of `leg_call`, hi was computed by sign-extending the 64-bit lo value (`lo >> 63`). For positive i128 values in [2^63, 2^64) (e.g. `18236369148602607032_i128`), bit 63 of lo is set but hi should be 0, giving wrong output | For constant arguments, look up the original BigInt via `_old.inst(arg.value.index())` and compute hi as `(val >> 64) & mask64` directly; fall back to sign-extension only for non-constant Signed(128) values |

Seeds 0–1000 (optimized builds, `-Zmir-opt-level=3 -C opt-level=3`):

| Category | Count | % of total |
|----------|------:|-----:|
| Pass | 1001 | 100.0 |
| Crash | 0 | 0.0 |
| Mismatch | 0 | 0.0 |

All 1001 seeds (0–1000) pass. 0 crashes, 0 mismatches.

### Run 14 (2026-03-06) - Extended optimized build fuzzing (seeds 0–10000)

Extended the optimized-build fuzzing campaign to seeds 0–10000. Found and fixed
multiple new bugs in both legalization and MIR-to-IR translation:

**legalize.rs fixes** (commit `b58b3d1`):

| Bug | Affected Seeds | Root cause | Fix |
|-----|---------------|-----------|-----|
| `leg_shr`: non-wide u128 operand produced wrong hi word | 7263 | When legalizing `shr v:u128, amt` where `v` is a small constant (not in the wide set), `vmap.pair(v)` returned `(v, v)`, making hi = lo instead of 0. | Added `wide_pair()` helper that emits hi = 0 for unsigned non-wide values and hi = lo >> 63 for signed. Also fixed `is_wide()` to recognize `Mapped::Pair` entries. |
| `leg_store_128`: non-wide constant stored with wrong hi word | Various | Storing a small 128-bit constant (fitting in u64) computed hi as `(lo, lo)` instead of deriving hi from the BigInt. | Fixed by computing hi from `Op::Const` BigInt when value is not in the wide set. |
| `Sext`/`Zext` for fp-to-int missing compiler-rt saturation | Various | Float-to-i128/u128 conversions going through `Sext(FpToSi, 128)` / `Zext(FpToUi, 128)` did not call the compiler-rt saturation routines (`__fixsfti`, `__fixdfti`, etc.). | Added `get_fp_to_int_float_type()` and `leg_fp_to_int128()` to route these through the correct libcalls. |

**rustc_codegen_tuffy MIR-to-IR fixes** (commit `2b641db`):

| Bug | Affected Seeds | Root cause | Fix |
|-----|---------------|-----------|-----|
| Spill not persisted for projected intrinsic/call destinations | Various | For non-Deref projected destinations (e.g. `_struct.field`), the local slot was restored to the pre-spill value after the call, so subsequent reads returned stale data. | Persist the spill slot for non-Deref projections; only Deref projections restore to the original. |
| Newtype wrapper over u128/i128 passed as pointer | Various | A 16-byte Scalar argument (e.g. `struct Foo(u128)`) was passed by pointer instead of loading lo+hi halves. | Load the two 8-byte halves from the pointer and pass as two integer registers. |
| Negation/NOT of >8-byte integer applied to pointer | Various | For i128/u128 operands, `translate_place_to_value` returns a Ptr; negation and bitwise NOT applied the operation to the pointer address instead of the loaded value. | Load the 128-bit integer from the pointer before applying the operation. |
| 8-byte non-pointer type copied by value instead of memory | Various | Assignment of an 8-byte projected non-pointer type (e.g. `(char, bool)`) passed the source pointer as the value instead of copying bytes from the source address. | Extended the word-by-word copy condition to also cover non-pointer 8-byte types. |
| Bool-typed unreachable return emitted wrong IR type | Various | Default return value for Bool-typed functions fell through to `iconst(0)` (Int), causing IR type mismatches. | Emit `bconst(false)` for Bool return types. |

Seeds 0–10000 (optimized builds, `-Zmir-opt-level=3 -C opt-level=3`):

| Category | Count | % of total |
|----------|------:|-----:|
| Pass | 10001 | 100.0 |
| Crash | 0 | 0.0 |
| Mismatch | 0 | 0.0 |

All 10001 seeds (0–10000) pass. 0 crashes, 0 mismatches.

## Affected Modules

- `rustc_codegen_tuffy` — codegen backend under test
- `tuffy_codegen/src/legalize.rs` — u128 to float conversion legalization; secondary return move remapping; i128 call argument legalization; leg_shr/leg_store_128 non-wide constant hi fixes; fp-to-int128 compiler-rt routing
- `rustc_codegen_tuffy/src/mir_to_ir/terminator.rs` — uninitialized float return handling; Bool return type fix
- `rustc_codegen_tuffy/src/mir_to_ir/mod.rs` — address-taken prescan stack slot allocation
- `rustc_codegen_tuffy/src/mir_to_ir/call.rs` — spill persistence for projected destinations; newtype wrapper u128 argument loading
- `rustc_codegen_tuffy/src/mir_to_ir/rvalue.rs` — negation/NOT of >8-byte integers stored as pointers
- `rustc_codegen_tuffy/src/mir_to_ir/statement.rs` — 8-byte non-pointer type aggregate copy
- `tuffy_target_x86/src/isel.rs` — partial store for non-power-of-2 byte sizes
