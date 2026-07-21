# Comparative benchmarks

`run.sh [iterations]` builds optimized Haskell and Rust executables, executes
the same parameterized forward-chaining workloads, and refuses to accept a
timing pair unless both implementations emit the same semantic FNV-1a digest.
Each line records the implementation, workload, parameters, iterations,
elapsed milliseconds, and digest.

Run from the repository root:

```sh
sh benchmarks/run.sh 100
```

These are wall-clock microbenchmarks, not claims about language-wide speed.
Run on an otherwise idle machine and retain the full output when publishing a
comparison.
