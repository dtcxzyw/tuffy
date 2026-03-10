#!/usr/bin/env python3
"""Rustlantis differential fuzzing script with parallel execution."""

import argparse
import subprocess
import sys
from concurrent.futures import ProcessPoolExecutor, as_completed
from pathlib import Path

CODEGEN = "/tuffy/rustc_codegen_tuffy/target/release/librustc_codegen_tuffy.so"
GENERATE = "/tmp/rustlantis/target/release/generate"


def test_seed(seed: int) -> tuple[str, int, str, str]:
    """Test a single seed. Returns (status, seed, llvm_out, tuffy_out)."""
    src = f"/tmp/rl_fuzz_{seed}.rs"
    llvm_bin = f"/tmp/rl_llvm_{seed}"
    tuffy_bin = f"/tmp/rl_tuffy_{seed}"

    try:
        # Generate source
        with open(src, "w") as f:
            subprocess.run([GENERATE, str(seed)], stdout=f, stderr=subprocess.DEVNULL, check=True)

        # Compile with LLVM
        result = subprocess.run(
            ["rustc", "+nightly", "-Zmir-opt-level=0", "-C", "debug-assertions=off",
             "-C", "opt-level=3", "-o", llvm_bin, src],
            stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL
        )
        if result.returncode != 0:
            return ("SKIP", seed, "", "")

        # Compile with Tuffy
        result = subprocess.run(
            ["rustc", "+nightly", "-Zmir-opt-level=0", "-C", "debug-assertions=off",
             "-C", "opt-level=3", f"-Zcodegen-backend={CODEGEN}", "-o", tuffy_bin, src],
            stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL
        )
        if result.returncode != 0:
            return ("CRASH", seed, "", "")

        # Run both binaries
        llvm_result = subprocess.run([llvm_bin], capture_output=True, text=True, timeout=5)
        tuffy_result = subprocess.run([tuffy_bin], capture_output=True, text=True, timeout=5)

        llvm_out = llvm_result.stdout + llvm_result.stderr
        tuffy_out = tuffy_result.stdout + tuffy_result.stderr

        if llvm_out == tuffy_out:
            return ("PASS", seed, llvm_out, tuffy_out)
        else:
            return ("MISMATCH", seed, llvm_out, tuffy_out)

    finally:
        # Cleanup
        Path(src).unlink(missing_ok=True)
        Path(llvm_bin).unlink(missing_ok=True)
        Path(tuffy_bin).unlink(missing_ok=True)


def main():
    parser = argparse.ArgumentParser(description="Rustlantis differential fuzzing")
    parser.add_argument("start", type=int, help="Start seed")
    parser.add_argument("end", type=int, help="End seed (inclusive)")
    parser.add_argument("jobs", type=int, nargs="?", help="Number of parallel jobs")
    args = parser.parse_args()

    jobs = args.jobs if args.jobs else subprocess.run(["nproc"], capture_output=True, text=True).stdout.strip()
    jobs = int(jobs)

    # Build generate binary
    print("Building generate binary...", file=sys.stderr)
    subprocess.run(["cargo", "build", "--release", "--bin", "generate"],
                   cwd="/tmp/rustlantis", stderr=subprocess.DEVNULL, check=True)

    # Clean up stale files
    for pattern in ["rl_fuzz_*.rs", "rl_llvm_*", "rl_tuffy_*"]:
        subprocess.run(f"rm -f /tmp/{pattern}", shell=True, stderr=subprocess.DEVNULL)

    # Run tests in parallel
    seeds = range(args.start, args.end + 1)
    results = {"PASS": [], "MISMATCH": [], "CRASH": [], "SKIP": []}

    with ProcessPoolExecutor(max_workers=jobs) as executor:
        futures = {executor.submit(test_seed, seed): seed for seed in seeds}
        for future in as_completed(futures):
            status, seed, llvm_out, tuffy_out = future.result()
            results[status].append((seed, llvm_out, tuffy_out))

    # Print mismatches
    for seed, llvm_out, tuffy_out in sorted(results["MISMATCH"]):
        print(f"MISMATCH({seed}):")
        print(f"  LLVM:  {llvm_out.strip()}")
        print(f"  TUFFY: {tuffy_out.strip()}")

    # Print summary
    print()
    print(f"Results: PASS={len(results['PASS'])} FAIL={len(results['MISMATCH'])} "
          f"CRASH={len(results['CRASH'])} (seeds {args.start}..{args.end}, {jobs} jobs)")


if __name__ == "__main__":
    main()
