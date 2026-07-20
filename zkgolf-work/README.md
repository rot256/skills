# zkGolf continuous-improvement loop

Autonomous loop that uses **Aristotle** (Harmonic ATP) to optimize [zk.golf](https://zk.golf)
Lean-4 circuit-golf submissions and auto-submits verified improvements.

## Durability model
Only this **tooling** is committed. All runtime state (`projs/`, `records/`, `targets.json`,
`prompts/`, `state_*.json`, `env.local`) is **gitignored and regenerable from the zk.golf +
Aristotle APIs**. Container restarts wipe the runtime; recover with the steps below.

## Recover after a restart
```bash
cd zkgolf-work
# 1. keys (NOT committed) — from the loop prompt:
cat > env.local <<'EOF'
export ZKGOLF_KEY=<zkgolf cmp_ key>
export ARISTOTLE_API_KEY=<aristotle arstl_ key>
EOF
# 2. rebuild runtime from APIs:
bash bootstrap.sh
# 3. recover job tracking from live Aristotle jobs:
source env.local && uv run --with aristotlelib python3 reconstruct_state.py
# 4. arm the watcher (via the harness Monitor tool):
#    cd zkgolf-work && source env.local && python3 notify_watch.py
```

## How it works
- `bootstrap.sh` — clone challenge repo, build per-challenge project dirs (pruned, `clean`
  pinned to the exact SHA `041c6e7e` so Aristotle builds Lean 4.28 / Mathlib 4.28), seed each
  `Solution/` from the current **valid** best record (must contain `computableWitness`, which the
  grandfathered leaderboard records omit), regenerate prompts + targets.
- `tick.py` — one idempotent pass: refresh each Aristotle job; on completion download output,
  gate (no `sorry`/`admit`/`native_decide`; all required theorems incl **`computableWitness`**
  present; score strictly below the true best = `challenges.best_score`), auto-submit to zk.golf;
  auto-refill so ≥1 job per (challenge, big/small) stays in flight; poll pending submissions.
- `check_records.py` — when a competitor beats a target, re-seed from the new valid record.
- `notify_watch.py` — runs `check_records` + `tick` on a loop, emitting `NOTIFY:` lines.

## Key facts learned
- The per-challenge leaderboard API is sorted **worst-first**; true best = `challenges.best_score`.
- `computableWitness` is a **required** theorem; leaderboard records set before the requirement
  omit it and can't be rebuilt — seed only from records that contain it (baseline otherwise).
- Local validation is possible via `gh-proxy.com` (mirrors the egress-blocked Lean toolchain +
  leantar + ProofWidgets); Mathlib olean cache is reachable directly.
