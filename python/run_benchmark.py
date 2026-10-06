#!/usr/bin/env python3
"""Run the fixed packing benchmark with equal wall-clock budgets and seeds."""

import argparse
import json
import math
import subprocess
import time
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--problems", type=Path, default=ROOT / "benchmarks/problems.json")
    parser.add_argument("--seconds", type=float, default=30.0)
    parser.add_argument("--seeds", type=int, default=5)
    parser.add_argument("--results", type=Path, default=ROOT / "benchmarks/results.json")
    parser.add_argument("--certificates", type=Path, default=ROOT / "benchmarks/certificates")
    parser.add_argument("--baseline", type=Path)
    args = parser.parse_args()

    if args.seconds <= 0 or args.seeds <= 0:
        parser.error("--seconds and --seeds must be positive")

    problems = json.loads(args.problems.read_text())
    args.certificates.mkdir(parents=True, exist_ok=True)
    args.results.parent.mkdir(parents=True, exist_ok=True)
    run_results = args.results.parent / "results"
    run_results.mkdir(parents=True, exist_ok=True)
    subprocess.run(["lake", "build", "timed_packer"], cwd=ROOT, check=True)
    executable = ROOT / ".lake" / "build" / "bin" / "timed_packer"
    records = []
    milliseconds = round(args.seconds * 1000)

    for problem in problems:
        for seed in range(args.seeds):
            certificate = args.certificates / f"{problem['name']}_seed_{seed}.json"
            result = run_results / f"{problem['name']}_seed_{seed}.json"
            command = [
                str(executable), problem["name"], str(problem["n"]),
                str(problem["nsi"]), str(problem["nsc"]), str(milliseconds), str(seed),
                str(certificate), str(result),
            ]
            timeout = max(args.seconds, 0.1) + 60.0
            started = time.monotonic()
            if result.exists():
                result.unlink()
            try:
                subprocess.run(command, cwd=ROOT, check=True, timeout=timeout)
            except subprocess.TimeoutExpired:
                try:
                    timed_out_result = json.loads(result.read_text())
                except (FileNotFoundError, json.JSONDecodeError):
                    timed_out_result = None
                if not timed_out_result or not (
                    timed_out_result.get("valid")
                    and timed_out_result.get("best_objective") is not None
                ):
                    result.write_text(json.dumps({
                        "problem": problem["name"],
                        "seed": seed,
                        "time_limit_ms": milliseconds,
                        "elapsed_ms": round((time.monotonic() - started) * 1000),
                        "attempts": 0,
                        "best_objective": None,
                        "best_seed": None,
                        "time_to_best_ms": None,
                        "valid": False,
                        "timed_out": True,
                        "curve": [],
                        "certificate": None,
                    }, indent=2) + "\n")
            records.append(json.loads(result.read_text()))

    output = {
        "time_limit_seconds": args.seconds,
        "seed_count": args.seeds,
        "problems_file": str(args.problems.relative_to(ROOT)),
        "runs": records,
    }
    args.results.write_text(json.dumps(output, indent=2) + "\n")
    if args.baseline:
        args.baseline.write_text(json.dumps(output, indent=2) + "\n")
    values = [
        run["best_objective"]
        for run in records
        if run["valid"] and run["best_objective"] is not None
    ]
    total = math.fsum(values) if values else None
    suffix = f" ({len(values)}/{len(records)} valid)"
    value = "unavailable" if total is None else f"{total:.8g}"
    print(f"value: {value}{suffix}")


if __name__ == "__main__":
    main()