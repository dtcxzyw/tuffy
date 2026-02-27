# Rustlantis Differential Fuzzing for rustc_codegen_tuffy

- Status: Draft
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
2. Standalone script: `./fuzz.sh <start_seed> <end_seed>`

Both compare tuffy output against LLVM with `-Zmir-opt-level=0`.

## Subtasks

- Run initial fuzzing campaign (e.g. seeds 1..100) and triage results
- Classify failures into compile crashes vs output mismatches
- Minimize reproduction cases for each distinct bug
- Fix identified codegen bugs in rustc_codegen_tuffy
- Increase config complexity as pass rate improves

## Affected Modules

- `rustc_codegen_tuffy` — codegen backend under test
