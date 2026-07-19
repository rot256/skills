ENVIRONMENT (already fixed — do not touch): the dependency pins are correct and reproducible — clean is pinned to the exact commit 041c6e7ebc06f5cbfd534c2a19c4120f3de62435 (Lean v4.28.0, Mathlib v4.28.0 = 8f9d9cff). Do NOT run `lake update` or change any dependency; build against the provided lake-manifest.json. The supplied record already fully builds and verifies in this environment.

STARTING POINT (IMPORTANT): `Solution/AssertBytes/` already contains the CURRENT LEADERBOARD RECORD for this challenge — score = allocations+constraints = 240 (by mimoo) — and it ALREADY FULLY VERIFIES with no `sorry`. Improve upon THIS record, NOT the baseline. Any solution you return MUST stay fully proved (no `sorry`/`admit`/`native_decide`) AND score STRICTLY BELOW 240; otherwise it is worthless. Look for structural constraint/allocation savings in the existing `main` and its gadgets. Keep every theorem obligation proved.

You are optimizing a zkGolf circuit in the Clean Lean-4 framework (builds against
`clean` = github Verified-zkEVM/clean, and Mathlib v4.28.0).

TARGET: `Solution/AssertBytes/` (namespace `Solution.AssertBytes`). The current baseline scores
`allocations + constraints = 272`. GOAL: produce a NEW circuit with STRICTLY FEWER
`allocations + constraints`, and FULLY PROVE it. Bigger reductions are much better — be ambitious.

Rewrite `Solution/AssertBytes/Main.lean` (and its helper files) so `main` implements a cheaper
circuit, set `@[reducible] def allocations` and `def constraints` to the TRUE new cost, and
provide COMPLETE proofs of every obligation. You choose the circuit design AND write all proofs.

HARD REQUIREMENTS (the zkGolf verifier rejects the submission otherwise):
- Do NOT change anything under `Challenge/` — the interface and `Spec` are TRUSTED and fixed.
  Keep the EXACT signatures of `main`, `elaborated`, `soundness`, `completeness`, `mainCost`,
  `isR1CS`, `computableWitness` as declared in `Challenge/Instances/AssertBytes/Challenge.lean`.
- NO `sorry`, NO `admit`, NO `native_decide`. Avoid `decide`/`simp`-bombs on huge goals.
- The final `#print axioms` of every listed theorem may use ONLY: `propext`, `Quot.sound`,
  `Classical.choice`, and `Challenge.Instances.AssertBytes.Interface.hCircomPrime`.
- `mainCost` must prove `circuitCost main ⟨allocations, constraints⟩` for your real cost, and
  `isR1CS` must hold: every `assert` is ONE rank-1 row `A*B - C` with `A,B,C` affine (degree ≤ 1).
- Keep the whole project building green under lean4 v4.28.0 / Mathlib v4.28.0. Mathlib is fair game.

If a full rewrite is too large to finish, make the single highest-impact change you can FULLY
prove while keeping the build green — a smaller verified win beats a larger unproved one.

OPTIMIZATION IDEAS to consider (verify each before relying on it):
Each element only needs a byte (<256) range check. Baseline uses 8 witnessed bits + 8 booleanity + 1 recomposition per element (8 alloc / 9 constr). Instead witness only the LOW 7 bits b0..b6, boolean-constrain each, then DEFINE the 8th bit as the affine expression h = (x - Σ_{i<7} b_i·2^i)·(128)⁻¹ and boolean-constrain h with the single rank-1 row h·(h-1)=0. This folds the recomposition away: 7 alloc + 8 constr per element ⇒ 112+128 = 240 total. Soundness: h∈{0,1} ⇒ x = Σ b_i·2^i + 128·h ∈ [0,256).

Return the complete updated `Solution/AssertBytes/` Lean files, fully compiling.