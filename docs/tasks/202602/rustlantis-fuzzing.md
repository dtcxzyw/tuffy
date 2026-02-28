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
2. Standalone script: `./fuzz.sh <start_seed> <end_seed>`

Both compare tuffy output against LLVM with `-Zmir-opt-level=0`.

Hints:
- Adjust `config.toml` to generate smaller inputs (fewer basic blocks, functions, args, etc.) when debugging — smaller programs are much easier to minimize and reason about. The shipped config already uses reduced values compared to upstream defaults.
- Use `minimise.py` to reduce a reproducer: copy the failing program to `repro.rs` in the rustlantis directory, then run `python3 minimise.py`. It iteratively comments out or replaces MIR statements with `Return()`, keeping only lines needed to reproduce the bug. Output goes to `minimised.rs`.
- Always minimize reproducers before reading them. Raw generated programs contain a lot of noise; minimised versions isolate the root cause much faster.

## Results (2026-02-28)

Seeds 0–1000:

| Category | Count | % of total |
|----------|------:|-----:|
| Pass | 396 | 39.6 |
| Crash (compile fail) | 602 | 60.2 |
| Mismatch (wrong code) | 3 | 0.3 |

### Mismatches

| Seed | LLVM output | Tuffy output | Category |
|------|-------------|--------------|----------|
| 721 | `hash: 7541581120933061747` | `timeout: the monitored command dumped core` | Runtime crash |
| 792 | `hash: 5746564840755200983` | `hash: 3589671292757105802` | Wrong code |
| 881 | `hash: 11960833139707412614` | `hash: 12179716529323217799` | Wrong code |

## Subtasks

- Run initial fuzzing campaign (e.g. seeds 1..100) and triage results
- Classify failures into compile crashes vs output mismatches
- Minimize reproduction cases for each distinct bug
- Fix identified codegen bugs in rustc_codegen_tuffy
- Increase config complexity as pass rate improves

## Affected Modules

- `rustc_codegen_tuffy` — codegen backend under test
