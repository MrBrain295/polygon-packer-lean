# Time-based benchmark

`problems.json` is the fixed benchmark suite. The solver is given the same
problem, seed, and wall-clock budget for every run; iteration counts are only
reported as diagnostics and are not a performance metric.

Run the normal benchmark and save a baseline with:

```sh
python3 python/run_benchmark.py --seconds 30 --seeds 5 --baseline benchmarks/baseline.json
```

Use `--seconds 5` for a quick run or `--seconds 300` for a long run. Results
are written to `benchmarks/results.json`, individual run records to
`benchmarks/results/`, and checked certificates to `benchmarks/certificates/`.

Each run records its best-objective improvement curve, exact validity, time to
the best completed candidate, and the certificate used for judging the result.
Summarize final valid objectives with:

```sh
python3 python/analyze_benchmark.py benchmarks/results.json
```