STARTING POINT (IMPORTANT): `Solution/Secp256k1ScalarMul/` already contains the CURRENT LEADERBOARD RECORD for this challenge — score = allocations+constraints = 16457480 (by SebastienGllmt) — and it ALREADY FULLY VERIFIES with no `sorry`. Improve upon THIS record, NOT the baseline. Any solution you return MUST stay fully proved (no `sorry`/`admit`/`native_decide`) AND score STRICTLY BELOW 16457480; otherwise it is worthless. Look for structural constraint/allocation savings in the existing `main` and its gadgets. Keep every theorem obligation proved.

You are optimizing a zkGolf circuit in the Clean Lean-4 framework (builds against
`clean` = github Verified-zkEVM/clean, and Mathlib v4.28.0).

TARGET: `Solution/Secp256k1ScalarMul/` (namespace `Solution.Secp256k1ScalarMul`). The current baseline scores
`allocations + constraints = 16462088`. GOAL: produce a NEW circuit with STRICTLY FEWER
`allocations + constraints`, and FULLY PROVE it. Bigger reductions are much better — be ambitious.

Rewrite `Solution/Secp256k1ScalarMul/Main.lean` (and its helper files) so `main` implements a cheaper
circuit, set `@[reducible] def allocations` and `def constraints` to the TRUE new cost, and
provide COMPLETE proofs of every obligation. You choose the circuit design AND write all proofs.

HARD REQUIREMENTS (the zkGolf verifier rejects the submission otherwise):
- Do NOT change anything under `Challenge/` — the interface and `Spec` are TRUSTED and fixed.
  Keep the EXACT signatures of `main`, `elaborated`, `soundness`, `completeness`, `mainCost`,
  `isR1CS`, `computableWitness` as declared in `Challenge/Instances/Secp256k1ScalarMul/Challenge.lean`.
- NO `sorry`, NO `admit`, NO `native_decide`. Avoid `decide`/`simp`-bombs on huge goals.
- The final `#print axioms` of every listed theorem may use ONLY: `propext`, `Quot.sound`,
  `Classical.choice`, and `Challenge.Instances.Secp256k1ScalarMul.Interface.hCircomPrime`.
- `mainCost` must prove `circuitCost main ⟨allocations, constraints⟩` for your real cost, and
  `isR1CS` must hold: every `assert` is ONE rank-1 row `A*B - C` with `A,B,C` affine (degree ≤ 1).
- Keep the whole project building green under lean4 v4.28.0 / Mathlib v4.28.0. Mathlib is fair game.

If a full rewrite is too large to finish, make the single highest-impact change you can FULLY
prove while keeping the build green — a smaller verified win beats a larger unproved one.

OPTIMIZATION IDEAS to consider (verify each before relying on it):
- Variable-base scalar multiplication on secp256k1 over Fp (256-bit). Per-multiply non-native field range checks dominate — minimize them (carry-save + top-bit-fold range checks, fewest limbs).
- Use a windowed double-and-add (e.g. 4-bit windows) to cut point additions; use incomplete/affine addition formulas (fewer field mults) with standard exceptional-case handling; share/batch inversions.
- Represent Fp elements with minimal limbs and prove limb bounds cheaply.

Return the complete updated `Solution/Secp256k1ScalarMul/` Lean files, fully compiling.
