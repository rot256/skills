---
name: rust-performance
description: Performance-guided Rust optimization using benchmarks, sampling profilers, and agent-readable profiling artifacts. Use when optimizing Rust throughput, latency, CPU time, allocations, code size, compile/runtime hot paths, Criterion benchmarks, hyperfine measurements, Linux perf, macOS xctrace/Instruments, samply, flamegraphs, heap profilers, cargo-bloat, cargo-llvm-lines, or cargo-asm.
---

# Rust Performance

Do performance work as a measurement-guided loop. Do not make speculative rewrites before establishing a workload, a baseline, and profiler evidence.

## Core Workflow

1. Define the workload, metric, and success threshold.
   - Prefer a real production-like workload, a focused Criterion benchmark, or a command measured with `hyperfine`.
   - Record enough context to reproduce results: command, git state, CPU/OS, feature flags, profile, input size, and relevant environment variables.

2. Run correctness checks first.
   - Run the repo's tests for the touched area before profiling.
   - If no test covers the hot path, add or identify a small invariant check before changing behavior.

3. Measure the baseline.
   - Use Criterion for library/function-level benchmarks.
   - Use `hyperfine` for end-to-end command timing.
   - Save machine-readable output: Criterion JSON or `target/criterion/**/estimates.json`, and `hyperfine --export-json` / `--export-markdown`.

4. Profile before editing.
   - Prefer sampling profilers for CPU work.
   - Prefer `flambe` for Rust CPU sampling reports when available. It wraps `perf` on Linux and `xctrace` on macOS, emits folded stacks plus agent-readable text summaries, and can preserve raw profiler artifacts with `--keep-raw`.
   - Preserve text or structured profiling artifacts: `flambe` summaries/text flamegraphs/folded stacks, `perf report --stdio`, folded stacks, `xctrace` XML, `samply` profiles with symbols, or profiler JSON.
   - Do not use SVG flamegraph scraping for performance analysis. If only SVG output is available, stop and ask the user to install or enable tooling that emits text or structured profiler data. SVG flamegraphs are human-facing companion artifacts only.

5. Optimize one hypothesis at a time.
   - Tie every change to a measured hot path.
   - Keep edits narrow enough that before/after measurements explain the result.
   - Avoid unsafe code unless the bottleneck is proven, the invariant is documented, and tests cover the boundary.

6. Re-run correctness, benchmarks, and the relevant profiler.
   - Compare against the original baseline, not only against the previous experiment.
   - If measurements are noisy, increase runtime/sample count, reduce background load, pin the workload if practical, or state the uncertainty.

7. Report the outcome.
   - Include commands run, artifacts inspected, before/after numbers, percent change, correctness checks, and remaining bottlenecks.
   - Say when a result is inconclusive.

## flambe

Use `flambe` as the preferred Rust sampling wrapper on Linux and macOS when the task needs CPU profiler evidence. It uses Linux `perf` on Linux and `xcrun xctrace` on macOS. Install it from the GitHub repository when it is missing:

```bash
cargo install --git https://github.com/rot256/flambe flambe
```

Recommended capture/reporting flow for a built command:

```bash
cargo build --release
flambe capture --keep-raw -o stacks.folded -- <command> <args>
flambe summary -i stacks.folded -o flambe-summary.txt --top 30 --max-stacks 50
flambe render -i stacks.folded -o flambe.txt
```

On Linux, pass `perf` sampling options through `flambe capture` when needed:

```bash
flambe capture --freq 997 --event cycles --keep-raw -o stacks.folded -- <command> <args>
```

On macOS, pass a time limit to `xctrace` through `flambe capture`:

```bash
flambe capture --time-limit 10s --keep-raw -o stacks.folded -- <command> <args>
```

Use `flambe-summary.txt`, `flambe.txt`, `stacks.folded`, and the kept raw artifacts as the primary profiler evidence. Keep the broader workflow intact: `flambe` replaces the capture/export/collapse/reporting mechanics, not correctness checks, timing baselines, hypothesis discipline, or before/after comparison.

## Linux

Use Linux `perf` through `flambe` by default. If `flambe` is missing, install it from `https://github.com/rot256/flambe`. If `perf`, folded-stack tooling, or benchmark tooling is missing, stop and ask the user to install the missing tools instead of falling back to weak evidence.

Recommended baseline tools:

```bash
cargo test
cargo bench --bench <bench_name> -- --warm-up-time 3 --measurement-time 10
hyperfine --warmup 3 --runs 20 --export-json before.json '<command>'
```

Recommended CPU sampling flow:

```bash
cargo build --release
flambe capture --keep-raw -o stacks.folded -- <command> <args>
flambe summary -i stacks.folded -o flambe-summary.txt --top 30 --max-stacks 50
flambe render -i stacks.folded -o flambe.txt
```

Manual fallback:

```bash
perf record -F 997 --call-graph dwarf -o perf.data -- <command>
perf report --stdio -i perf.data > perf-report.txt
perf script -i perf.data > perf-script.txt
inferno-collapse-perf perf-script.txt > stacks.folded
inferno-flamegraph stacks.folded > flamegraph.svg
```

Use `flambe-summary.txt`, `flambe.txt`, `stacks.folded`, and any kept `.flambe/` raw artifacts as the primary evidence. For the manual fallback, use `perf-report.txt`, `perf-script.txt`, and `stacks.folded` as the primary evidence. Keep `flamegraph.svg` only as a visual companion for humans.

For Criterion benchmarks, profile the benchmark's stable profiling mode:

```bash
CARGO_PROFILE_BENCH_DEBUG=true cargo bench --bench <bench_name> -- --bench '<filter>' --profile-time 10
flambe capture --keep-raw -o stacks.folded -- target/release/deps/<bench_binary> --bench '<filter>' --profile-time 10
flambe summary -i stacks.folded -o flambe-summary.txt --top 30 --max-stacks 50
```

Manual fallback:

```bash
perf record -F 997 --call-graph dwarf -o perf.data -- target/release/deps/<bench_binary> --bench '<filter>' --profile-time 10
```

Use non-sampling tools only when sampling points at that class of problem:

- Allocation pressure: use `heaptrack`, Valgrind Massif/DHAT, allocator statistics, or a small `dhat`-instrumented binary when code changes are acceptable.
- Binary size or compile/codegen bloat: use `cargo bloat --release`, `cargo llvm-lines --release`, and `cargo asm`.
- Tight-loop codegen: inspect only the proven hot function with `cargo asm --release --lib <path::function> --asm --simplify --no-color`.

## macOS

Use `xcrun xctrace` Time Profiler through `flambe` as the default agent-readable sampling path. If `flambe` is missing, install it from `https://github.com/rot256/flambe`. If Xcode Command Line Tools, `xctrace`, `samply`, or benchmark tooling is missing or broken, stop and ask the user to install or enable the missing tool. Do not substitute SVG parsing.

Recommended baseline tools:

```bash
cargo test
cargo bench --bench <bench_name> -- --warm-up-time 3 --measurement-time 10
hyperfine --warmup 3 --runs 20 --export-json before.json --export-markdown before.md '<command>'
```

Recommended Time Profiler flow:

```bash
cargo build --release
flambe capture --time-limit 10s --keep-raw -o stacks.folded -- <command> <args>
flambe summary -i stacks.folded -o flambe-summary.txt --top 30 --max-stacks 50
flambe render -i stacks.folded -o flambe.txt
```

Manual fallback:

```bash
xcrun xctrace record \
  --template 'Time Profiler' \
  --time-limit 10s \
  --output profile.trace \
  --target-stdout - \
  --launch -- <command> <args>

xcrun xctrace export \
  --input profile.trace \
  --toc \
  --output profile-toc.xml

xcrun xctrace export \
  --input profile.trace \
  --xpath '/trace-toc/run[@number="1"]/data/table[@schema="time-profile"]' \
  --output time-profile.xml
```

Use `flambe-summary.txt`, `flambe.txt`, `stacks.folded`, `.flambe/time-profile.xml`, and `.flambe/profile.trace` as the primary sampling evidence. For the manual fallback, use `time-profile.xml` as the primary sampling evidence. It contains symbolicated backtraces, weights, thread state, and process metadata when symbols are available.

Use `samply` when it is a better fit for interactive inspection or archived profiles:

```bash
samply record --save-only --no-open -o profile.json.gz -- <command> <args>
samply record --save-only --no-open --unstable-presymbolicate -o profile.json.gz -- <command> <args>
```

If a `samply` profile is not symbolicated enough for agent analysis, ask for symbol sidecar data or switch to `xctrace` XML export.

Use `cargo flamegraph` only when the user explicitly wants a visual flamegraph or when generating a human companion artifact:

```bash
CARGO_PROFILE_BENCH_DEBUG=true cargo flamegraph --bench <bench_name> -- --bench '<filter>' --profile-time 10
```

Do not parse the SVG as the agent's evidence source.

Use allocation tools only after sampling indicates allocation pressure:

```bash
xcrun xctrace record \
  --template 'Allocations' \
  --time-limit 10s \
  --output allocations.trace \
  --target-stdout - \
  --launch -- <command> <args>

xcrun xctrace export \
  --input allocations.trace \
  --toc \
  --output allocations-toc.xml
```

For Rust-specific allocation attribution, add a temporary `dhat` binary or feature when code instrumentation is acceptable. Save `dhat-heap.json` and summarize total bytes, allocation count, and the hot stack frames.

Use static/codegen tools as second-line diagnostics:

```bash
cargo bloat --release -n 30
cargo llvm-lines --release
cargo asm --release --lib <path::function> --asm --simplify --no-color
```

Only use these after profiling identifies code size, monomorphization, inlining, or tight-loop codegen as plausible bottlenecks.

## Optimization Tactics

Choose tactics based on profiler evidence:

- Allocation hot path: remove repeated `format!`, `to_string`, `collect`, `clone`, `Box`, `Arc`, `Vec` growth, or temporary buffers; preallocate only when the size is justified.
- CPU hot loop: reduce work, improve data layout, avoid redundant parsing/hashing/formatting, batch operations, and keep branches predictable.
- Synchronization hot path: reduce lock scope, avoid unnecessary atomics, shard contention, or batch cross-thread communication.
- Async/service latency: combine sampling with tracing spans and queue/lock metrics; CPU profiles alone may not explain waits.
- Codegen issue: inspect the smallest hot function with assembly/LLVM tools; avoid broad rewrites based only on intuition.

Always verify the optimized code still matches the original semantics. For transformations that replace library behavior with manual logic, add direct equivalence tests against the original behavior.
