# Verifier-budget tooling

The zk.golf verifier runs one job at a time with a 20-minute limit per job
(build, statement comparison, export, kernel re-check).  These scripts keep the
submission inside that budget.

* `dce.lean` — run with `lake env lean tools/dce.lean` in the project; writes
  `dce_ranges.txt` (declaration ranges of every Solution module, and the ranges
  reached by the constant closure of the five exported theorems).
* `../dce.py RANGES SRC OUT [extra]` — deletes unreachable declarations from the
  flattened package, drops modules that keep nothing, hoists their imports.
* `kclosure2.lean` — per-module touched-constant report.
* `kprof.lean` — `lake env lean --run tools/kprof.lean <Module> [ms]` replays a
  module's constants one by one through the kernel and prints the slow ones.

## Pipeline

`../prune_pipeline.sh <scratch dir>` runs the whole thing: stage 1 computes the
closure in the full project (`dce.lean`, iterated with the textual seeds that
`dce.py` emits until nothing new is kept), builds the pruned package in the
isolated project `projs/dce-test` (which shares `.lake/packages` with the main
project) and applies `fixup.py` for identifiers that only ever appeared in
unused `simp`/`rw` lists; stage 2 repeats the closure inside the pruned build.
`START=fix1` / `START=fix2` resume at the build/fixup loops.

Result for the 244,094 submission (8cd30848): 190 files / 7.1 MB pruned to
156 files / 2.7 MB; local cold build 8m49s with 1612 s of serial compile work;
the verifier finished the job in about 10 minutes (limit 20).
