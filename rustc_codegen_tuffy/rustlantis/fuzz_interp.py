#!/usr/bin/env python3
"""Rustlantis interpreter differential fuzzing script.

Compares LLVM-compiled native execution against tuffy_ir_interp interpretation
of the Tuffy IR dump. Timeouts are treated as skips (the interpreter is ~1000x
slower than native, so some seeds take too long).
"""

import argparse
import os
import subprocess
import sys
from concurrent.futures import ProcessPoolExecutor, as_completed
from pathlib import Path

CODEGEN = "/tuffy/rustc_codegen_tuffy/target/release/librustc_codegen_tuffy.so"
INTERP = "/tuffy/target/release/tuffy-interp"
GENERATE = "/tmp/rustlantis/target/release/generate"

# Interpreter timeout in seconds.  The interpreter runs ~1000x slower than
# native, so generous timeouts are needed for complex seeds.
INTERP_TIMEOUT = 30


def test_seed(args: tuple[int, int]) -> tuple[str, int, str, str]:
    """Test a single seed. Returns (status, seed, expected, actual)."""
    seed, timeout = args
    src = f"/tmp/rl_interp_{seed}.rs"
    llvm_bin = f"/tmp/rl_interp_llvm_{seed}"
    tuffy_bin = f"/tmp/rl_interp_tuffy_{seed}"
    ir = f"/tmp/rl_interp_{seed}.tuffy"

    try:
        # Generate source
        with open(src, "w") as f:
            subprocess.run(
                [GENERATE, str(seed)],
                stdout=f,
                stderr=subprocess.DEVNULL,
                check=True,
                cwd="/tmp/rustlantis",
            )

        # Compile with LLVM and run
        result = subprocess.run(
            ["rustc", "+nightly", src, "-o", llvm_bin],
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )
        if result.returncode != 0:
            return ("SKIP", seed, "", "")

        try:
            r = subprocess.run(
                [llvm_bin], capture_output=True, text=True, timeout=10
            )
            expected = r.stdout.strip()
        except subprocess.TimeoutExpired:
            return ("SKIP", seed, "", "")

        # Compile with Tuffy backend (dump IR)
        result = subprocess.run(
            [
                "rustc",
                "+nightly",
                src,
                f"-Zcodegen-backend={CODEGEN}",
                "-C",
                f"llvm-args=dump-module={ir}",
                "-o",
                tuffy_bin,
            ],
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )
        if result.returncode != 0:
            return ("CRASH", seed, expected, "")

        # Interpret
        try:
            r = subprocess.run(
                [INTERP, ir], capture_output=True, text=True, timeout=timeout
            )
            actual = r.stdout.strip()
            if r.returncode == 2:
                # Step limit exceeded or stack overflow
                return ("TIMEOUT", seed, expected, "")
        except subprocess.TimeoutExpired:
            return ("TIMEOUT", seed, expected, "")

        if expected == actual:
            return ("PASS", seed, expected, actual)
        else:
            return ("MISMATCH", seed, expected, actual)

    except Exception as e:
        return ("ERROR", seed, "", str(e))

    finally:
        for path in [src, llvm_bin, tuffy_bin, ir]:
            Path(path).unlink(missing_ok=True)


def main():
    parser = argparse.ArgumentParser(
        description="Rustlantis interpreter differential fuzzing"
    )
    parser.add_argument("start", type=int, help="Start seed")
    parser.add_argument("end", type=int, help="End seed (inclusive)")
    parser.add_argument("jobs", type=int, nargs="?", help="Number of parallel jobs")
    parser.add_argument(
        "--timeout",
        type=int,
        default=INTERP_TIMEOUT,
        help=f"Interpreter timeout in seconds (default: {INTERP_TIMEOUT})",
    )
    args = parser.parse_args()

    timeout = args.timeout

    jobs = (
        args.jobs
        if args.jobs
        else int(
            subprocess.run(
                ["nproc"], capture_output=True, text=True
            ).stdout.strip()
        )
    )

    # Check prerequisites
    for path, name in [
        (CODEGEN, "codegen backend"),
        (INTERP, "interpreter"),
        (GENERATE, "rustlantis generator"),
    ]:
        if not Path(path).exists():
            print(f"Error: {name} not found at {path}", file=sys.stderr)
            sys.exit(1)

    # Clean up stale files
    for pattern in ["rl_interp_*.rs", "rl_interp_llvm_*", "rl_interp_tuffy_*", "rl_interp_*.tuffy"]:
        subprocess.run(f"rm -f /tmp/{pattern}", shell=True, stderr=subprocess.DEVNULL)

    seeds = range(args.start, args.end + 1)
    results: dict[str, list] = {
        "PASS": [],
        "MISMATCH": [],
        "CRASH": [],
        "TIMEOUT": [],
        "SKIP": [],
        "ERROR": [],
    }

    with ProcessPoolExecutor(max_workers=jobs) as executor:
        futures = {
            executor.submit(test_seed, (seed, timeout)): seed for seed in seeds
        }
        done = 0
        for future in as_completed(futures):
            status, seed, expected, actual = future.result()
            results[status].append((seed, expected, actual))
            done += 1
            if done % 100 == 0:
                print(
                    f"Progress: {done}/{len(seeds)} "
                    f"({len(results['PASS'])} pass, "
                    f"{len(results['MISMATCH'])} fail, "
                    f"{len(results['TIMEOUT'])} timeout)",
                    file=sys.stderr,
                    flush=True,
                )

    # Print mismatches
    for seed, expected, actual in sorted(results["MISMATCH"]):
        print(f"MISMATCH({seed}):")
        print(f"  expected: {expected}")
        print(f"  actual:   {actual}")

    # Print errors
    for seed, _, msg in sorted(results["ERROR"]):
        print(f"ERROR({seed}): {msg}")

    # Print summary
    print()
    print(
        f"Results: PASS={len(results['PASS'])} FAIL={len(results['MISMATCH'])} "
        f"CRASH={len(results['CRASH'])} TIMEOUT={len(results['TIMEOUT'])} "
        f"SKIP={len(results['SKIP'])} "
        f"(seeds {args.start}..{args.end}, {jobs} jobs)"
    )

    # Exit with failure if any mismatches
    if results["MISMATCH"]:
        sys.exit(1)


if __name__ == "__main__":
    main()
