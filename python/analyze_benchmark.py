#!/usr/bin/env python3
"""Print per-problem summary statistics for benchmark results."""

import argparse
import json
import statistics
from pathlib import Path


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("results", type=Path, default=Path("benchmarks/results.json"), nargs="?")
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


if __name__ == "__main__":
    main()