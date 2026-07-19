ENVIRONMENT (already fixed — do not touch): the dependency pins are correct and reproducible — clean is pinned to the exact commit 041c6e7ebc06f5cbfd534c2a19c4120f3de62435 (Lean v4.28.0, Mathlib v4.28.0 = 8f9d9cff). Do NOT run `lake update` or change any dependency; build against the provided lake-manifest.json. The supplied record already fully builds and verifies in this environment.

STARTING POINT (IMPORTANT): `Solution/KeccakF1600/` already contains the CURRENT LEADERBOARD RECORD for this challenge — score = allocations+constraints = 284160 (by bufferhe4d) — and it ALREADY FULLY VERIFIES with no `sorry`. Improve upon THIS record, NOT the baseline. Any solution you return MUST stay fully proved (no `sorry`/`admit`/`native_decide`) AND score STRICTLY BELOW 284160; otherwise it is worthless. Look for structural constraint/allocation savings in the existing `main` and its gadgets. Keep every theorem obligation proved.

You are optimizing a zkGolf circuit in the Clean Lean-4 framework (builds against
`clean` = github Verified-zkEVM/clean, and Mathlib v4.28.0).

TARGET: `Solution/KeccakF1600/` (namespace `Solution.KeccakF1600`). The current baseline scores
`allocations + constraints = 307200`. GOAL: produce a NEW circuit with STRICTLY FEWER
`allocations + constraints`, and FULLY PROVE it. Bigger reductions are much better — be ambitious.

Rewrite `Solution/KeccakF1600/Main.lean` (and its helper files) so `main` implements a cheaper
circuit, set `@[reducible] def allocations` and `def constraints` to the TRUE new cost, and
provide COMPLETE proofs of every obligation. You choose the circuit design AND write all proofs.

HARD REQUIREMENTS (the zkGolf verifier rejects the submission otherwise):
- Do NOT change anything under `Challenge/` — the interface and `Spec` are TRUSTED and fixed.
  Keep the EXACT signatures of `main`, `elaborated`, `soundness`, `completeness`, `mainCost`,
  `isR1CS`, `computableWitness` as declared in `Challenge/Instances/KeccakF1600/Challenge.lean`.
- NO `sorry`, NO `admit`, NO `native_decide`. Avoid `decide`/`simp`-bombs on huge goals.
- The final `#print axioms` of every listed theorem may use ONLY: `propext`, `Quot.sound`,
  `Classical.choice`, and `Challenge.Instances.KeccakF1600.Interface.hCircomPrime`.
- `mainCost` must prove `circuitCost main ⟨allocations, constraints⟩` for your real cost, and
  `isR1CS` must hold: every `assert` is ONE rank-1 row `A*B - C` with `A,B,C` affine (degree ≤ 1).
- Keep the whole project building green under lean4 v4.28.0 / Mathlib v4.28.0. Mathlib is fair game.

If a full rewrite is too large to finish, make the single highest-impact change you can FULLY
prove while keeping the build green — a smaller verified win beats a larger unproved one.

OPTIMIZATION IDEAS to consider (verify each before relying on it):
- theta, rho, pi are linear (XOR of rotations): keep them as FREE linear combinations, charge no constraints.
- chi = a ⊕ ((¬b) & c): ¬b is affine (1-b); encode the AND (b&c) and the XOR each as a single rank-1 row. iota XORs a constant (free).
- Only pay for state-bit booleanity and chi. The baseline is a uniform 153600/153600 — if XOR is free and only chi is charged, the room is large.
- Fold top bits of any range checks; avoid re-decomposing bits that are already boolean-constrained.

Return the complete updated `Solution/KeccakF1600/` Lean files, fully compiling.