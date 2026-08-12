# Summary of changes for run 4a90e6f7-dc2d-4b85-b7eb-fd7346dd5604
The `sorry` in `Solution/CarrySave/Basic.lean` is gone; the file compiles with zero errors (only three "unused variable" warnings for the `hx`/`hy`/`hz` bounds, which I kept because the statement had to stay unchanged).

**Route that worked: bitwise induction (route 1), peeling the low bit.** The proof is:

- Three private low-bit lemmas — `(a &&& b) % 2 = (a % 2) &&& (b % 2)` and the `|||`/`^^^` analogues — each proved from `Nat.and_one_is_mod` plus distributivity.
- `maj_div_two` and `maj_mod_two`: `maj` commutes with `/ 2` and with `% 2`, via Mathlib's `Nat.and_div_two` / `Nat.or_div_two` / `Nat.xor_div_two` and the lemmas above.
- `maj_single_bit`: the eight-case single-bit full adder, closed by `interval_cases` + `decide`.
- `add_eq_xor_add_two_mul_maj'`: induction on a bit-width bound. At each step both sides split as `2 * (high part) + (low bit)`; the induction hypothesis on `x/2, y/2, z/2` and the single-bit case combine by `omega`.

**The bound was not needed.** I proved the unbounded version `add_eq_xor_add_two_mul_maj' (x y z : ℕ) : x + y + z = (x ^^^ y ^^^ z) + 2 * maj x y z` and derived the requested bounded theorem from it by discarding the hypotheses (internally the induction instantiates the bit-width bound at `x + y + z`, using `n < 2 ^ n`). The original bounded statement and `maj` are untouched, so `add_eq_xor_add_two_mul_maj_32` still typechecks as written.

**Axioms printed:**
- `Solution.CarrySave.add_eq_xor_add_two_mul_maj` depends on axioms: `[propext, Classical.choice, Quot.sound]`
- `Solution.CarrySave.add_eq_xor_add_two_mul_maj_32` depends on axioms: `[propext, Classical.choice, Quot.sound]`
- `Solution.CarrySave.add_eq_xor_add_two_mul_maj'` depends on axioms: `[propext, Classical.choice, Quot.sound]`

No `sorryAx`, no new `axiom`, and no `native_decide` / `bv_decide` anywhere in `Solution/`. One infrastructure note: the `clean` dependency was missing from the package cache, so I fetched it at the pinned commit `041c6e7` to make the build resolve; no project source outside `Solution/CarrySave/Basic.lean` was modified.