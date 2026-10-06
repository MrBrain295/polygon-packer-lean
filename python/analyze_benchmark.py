#!/usr/bin/env python3
"""Print per-problem summary statistics for benchmark results."""

import argparse
import json
import math
import statistics
from pathlib import Path


def total_objective(data):
    values = [
        run["best_objective"]
        for run in data["runs"]
        if run["valid"] and run["best_objective"] is not None
    ]
    if len(values) != len(data["runs"]):
        return None
    return math.fsum(values)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("results", type=Path, default=Path("benchmarks/results.json"), nargs="?")
    parser.add_argument("--baseline", type=Path)
    args = parser.parse_args()
    data = json.loads(args.results.read_text())
    grouped = {}
    for run in data["runs"]:
        if run["valid"] and run["best_objective"] is not None:
            grouped.setdefault(run["problem"], []).append(run["best_objective"])
    print("problem\tbest\tmean\tmedian\tworst")
    for problem, values in grouped.items():
        print(problem, *(f"{value:.8g}" for value in (
            min(values), statistics.mean(values), statistics.median(values), max(values))), sep="\t")

    result_total = total_objective(data)
    print("total", "unavailable" if result_total is None else f"{result_total:.8g}", sep="\t")
    if args.baseline:
        baseline_total = total_objective(json.loads(args.baseline.read_text()))
        if result_total is None or baseline_total is None:
            print("winner\tunavailable")
        elif result_total < baseline_total:
            print("winner\tresults")
        elif baseline_total < result_total:
            print("winner\tbaseline")
        else:
            print("winner\ttie")


if __name__ == "__main__":
    main()