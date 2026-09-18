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
