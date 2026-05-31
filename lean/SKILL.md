---
name: lean
description: Writing, proving, and debugging Lean 4 + Mathlib. Use when proving theorems, filling `sorry`s, formalizing math, fixing broken proofs, or setting up a Lean project. Covers the cached-Mathlib setup and a plan-first proving workflow.
---

# Lean 4

Lean 4 theorem proving with Mathlib. Two rules dominate everything below:

1. **Never compile Mathlib from source.** Always use the cached build (see below). A cold Mathlib build is ~1h+ of CPU; the cache is minutes.
2. **Plan before proving.** Write a human-readable proof first, decompose into Lean steps, make a todo list, then prove. Do not jump straight into tactics.

## Cached Mathlib (mandatory)

Mathlib ships precompiled `.olean` artifacts via its build cache. Fetch them; never let Lake recompile Mathlib.

For a project that depends on Mathlib (has it in `lakefile.toml`/`lakefile.lean` + `lake-manifest.json`):

```bash
lake exe cache get      # downloads prebuilt Mathlib oleans matching the pinned rev
lake build              # builds ONLY your code against cached Mathlib
```

Key points:

- Run `lake exe cache get` after every clone, after `lake update`, or whenever the Mathlib rev in `lake-manifest.json` changes. If `lake build` starts compiling `Mathlib.*` files, the cache was stale or missing — stop it and re-run `lake exe cache get`.
- The cache is keyed to the **exact** Mathlib commit and the matching `lean-toolchain`. Do not bump the toolchain independently of Mathlib; mismatches force a full recompile.
- A new **git worktree** starts without a `.lake/` dir (it's gitignored and per-checkout), so the Mathlib oleans aren't there. Run `lake exe cache get` again inside the worktree before building, or it will recompile Mathlib from source.
- Starting fresh: `lake new my_proj math` (or `lake +leanprover/lean4:vX.Y.0 new my_proj math`) scaffolds a Mathlib-dependent project. Then `cd my_proj && lake exe cache get`.
- `lake exe cache get!` (with `!`) force-redownloads if local oleans are corrupted.
- A partial/aborted `cache get` can leave you compiling. Re-run it to completion before `lake build`.

For the full setup recipe, toolchain pinning, and troubleshooting see [references/setup.md](references/setup.md).

## Proving workflow (plan-first)

When asked to prove something, fill a `sorry`, or fix a proof, do NOT start writing tactics immediately. Follow these stages:

### 1. Human-readable proof

Write a natural-language proof for your own consumption — the mathematical argument, the way you'd explain it on paper. Identify:

- The actual claim (restate it precisely; check the Lean statement matches the intended math).
- The key idea / strategy (induction? case split? existing Mathlib lemma? algebraic manipulation?).
- The non-obvious steps where the real work is.

This guides the high-level strategy and surfaces dead ends before you spend tactic effort.

When the task is to *prove* an existing statement, treat the declaration header (name, binders, type) as immutable — change only the proof body. Altering the statement to make it provable is a silent way to prove the wrong thing. If the statement looks wrong or unprovable as written, stop and flag it rather than quietly editing it.

### 2. Decompose into Lean steps

Break the paper proof into concrete obligations that must be implemented in Lean:

- Each lemma or intermediate `have` that needs proving.
- Each rewrite / simp / induction step.
- Any auxiliary definitions or helper lemmas.
- Existing Mathlib lemmas to locate (name the concept; you'll search for the exact lemma).

Prefer many small `have` steps over one monolithic tactic block — they localize failures and stay debuggable.

### 3. Todo list

Turn the decomposition into an explicit todo list (use the available todo/task tool), one item per step. This makes the proof's progress visible and ensures nothing is dropped.

### 4. Prove

Work the todo list. For each step:

- Use `sorry` as a placeholder for not-yet-proven steps so the file still elaborates and you can typecheck the *structure* before filling details. Track every `sorry` — none may remain at the end.
- After each step, recompile (see Iterating) and check the goal state.
- When a step is more than routine `simp`/`decide`/`rewrite`, search Mathlib for an existing lemma before hand-rolling it. See [references/tactics.md](references/tactics.md) for finding lemmas (`exact?`, `apply?`, `rw?`, `loogle`, `#leansearch`) and the core tactic toolbox.

## Iterating on proofs

Fast feedback beats full builds:

- **Lean LSP feedback** is the primary signal — per-line goal state (`⊢ ...`) and diagnostics, not full rebuilds. Strongly prefer it for iterative work: sub-second vs 30s+ `lake build`.
  - A generic LSP tool (`hover`, `goToDefinition`, `documentSymbol`) gives types and navigation but NOT proof goal state.
  - For goal state + diagnostics, use a Lean-aware MCP server, `lean-lsp-mcp`: register once with `claude mcp add lean-lsp -s project uvx lean-lsp-mcp` (run in the project root), then query goal-state/diagnostics at the line you just edited. It also exposes premise search (LeanSearch, Loogle, Lean Hammer, Lean State Search) and `lean_run_code`. If it isn't installed and the task is proof-heavy, offer to add it.
- **Build one module:** `lake build My.Module.Path` (dotted module target) checks just that module against cached deps.
- **Check one file:** `lake env lean path/to/File.lean` (or `lake lean ...`) — runs Lean with the project's Mathlib search path set up. Do NOT invoke raw `lean File.lean`; without Lake's environment the Mathlib imports won't resolve.
- **`#check`, `#eval`, `example`** for quick local experiments without touching the main statement.
- Keep `set_option maxHeartbeats` reasonable; if a tactic times out, the proof is usually wrong or needs decomposition, not more heartbeats.

Never claim a proof is done while a `sorry`, `admit`, or `axiom`-shaped escape hatch remains, or while `lake build` reports errors. Caveat: **`lake build` still succeeds when the file contains `sorry`** — it only emits a "declaration uses 'sorry'" *warning*. So a green build is not proof of completeness. Treat any sorry/admit warning as failure: build with `lake build --wfail` (warnings fail the build) for a clean signal, or read the diagnostics and confirm none mention `sorry`. "Proved" means it compiles with zero errors and zero sorry warnings. Verify end-to-end before reporting success.
