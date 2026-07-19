ENVIRONMENT (already fixed — do not touch): the dependency pins are correct and reproducible — clean is pinned to the exact commit 041c6e7ebc06f5cbfd534c2a19c4120f3de62435 (Lean v4.28.0, Mathlib v4.28.0 = 8f9d9cff). Do NOT run `lake update` or change any dependency; build against the provided lake-manifest.json. The supplied record already fully builds and verifies in this environment.

STARTING POINT: `Solution/Secp256k1ScalarMul/` contains the CURRENT LEADERBOARD RECORD for this
challenge — score = allocations+constraints = 16457480 (by SebastienGllmt) — and it ALREADY FULLY VERIFIES
(no `sorry`). 

GOAL: a SMALL, SAFE, GUARANTEED fully-proved reduction STRICTLY BELOW 16457480. Prioritize CERTAINTY
of a completely-proved result over the size of the win. Make one or a few LOW-RISK, local savings
you can DEFINITELY prove, without restructuring the circuit, e.g.:
- Fold the top bit of a range check into an affine expression (`h = (x - Σlow)·2^-k`, boolean-
  constrain `h`) to remove one witnessed allocation per range check while keeping one rank-1 row.
- Remove a redundant/duplicate constraint or an unnecessary witness allocation.
- Merge two asserts that are provably one rank-1 row; drop a constraint implied by others.
- Reuse an already-computed value instead of re-witnessing it.

HARD REQUIREMENTS: keep everything under `Challenge/` unchanged; keep the EXACT signatures of
`main`, `elaborated`, `soundness`, `completeness`, `mainCost`, `isR1CS`, `computableWitness`; NO
`sorry`/`admit`/`native_decide`; final `#print axioms` uses only propext, Quot.sound,
Classical.choice, and `Challenge.Instances.Secp256k1ScalarMul.Interface.hCircomPrime`. Set `allocations`/
`constraints` to the true new cost and prove `mainCost`/`isR1CS`. Keep the build green (lean4
v4.28.0 / Mathlib v4.28.0). Return the complete updated `Solution/Secp256k1ScalarMul/` files, fully compiling.

A tiny verified win that beats 16457480 is a success — do not overreach and leave anything unproved.