# Degree filtration for R1CS row packing

Everything in this directory compiles with `lake build Solution` (zero errors, no `sorry`),
and every result listed below has `#print axioms` equal to
`[propext, Classical.choice, Quot.sound]` (see `AxiomCheck.lean`).

## Setting

* A point of the cube `{0,1}^ι` is a `Finset ι` (the coordinates equal to `1`).
* `coef t S` (`Multilinear.lean`) is the coefficient of `∏ i ∈ S, x i` in the unique
  multilinear polynomial representing `t : Finset ι → F`; `DegLE t d`, `IsAffineOn t`,
  `SuppIn t P`, `DependsOn t P` are phrased in terms of it.
* A single R1CS row is `Row ι F`: `A * B = C` where each slot is
  `(z-coefficient) * z + (affine form in x)`. So `z` may occur **quadratically**.
* **"a single row determines `z`"** is `Row.Pins R t` (`R1CSRow.lean`):

  ```lean
  def Row.Pins (R : Row ι F) (t : Finset ι → F) : Prop :=
    ∃ D : Aff ι F, (∀ x, R.Sat x (t x)) ∧ ∀ x z, R.Sat x z → z = t x ∨ z = D.ev x
  ```

  i.e. completeness plus soundness **up to one affine decoy root**. Unique determination
  is the special case in which the decoy is never used, so proving `¬ R.Pins t` is
  strictly stronger than ruling out unique determination.

## Disjoint blocks: both obligations proved

| statement | file |
| --- | --- |
| `degree_three_never_packs` — two non-affine gadgets on disjoint blocks, `lam ≠ 0`, packed target of degree ≥ 3: no row pins it | `DegreePack.lean` |
| `three_gadgets_never_pack` — three non-affine gadgets on pairwise disjoint blocks, nonzero multipliers: no row pins the sum (any degrees) | `DegreePack.lean` |
| `degree_two_packs_at_most_two` — the same, restated for degree-2 gadgets | `DegreePack.lean` |
| `two_and2_gadgets_pack` — an explicit row pinning `AND2 + lam·AND2`, uniquely, no decoy | `Examples.lean` |
| `and3_never_packs`, `maj_never_packs` — the degree-3 result for AND3 and Maj on disjoint triples | `Examples.lean` |

All of these assume `2 ≠ 0` in the field (the argument genuinely fails in characteristic 2).

Proof outline. `Row.pins_dichotomy` splits on whether `z` occurs quadratically.

* **Decoy-root branch** (`Az * Bz ≠ 0`): the target agrees pointwise with one of two affine
  forms, so `(t − u)(t − v) = 0`. Taking the multilinear coefficient at `S₁ ∪ S₂`, where
  `S₁`, `S₂` are degree-≥2 witnesses in two different blocks, gives `2·c₁·c₂ = 0`
  (`Packing.not_two_affine_branches`). Contradiction.
* **Linear branch**: the row reads `L·t = C₀ − A₀·B₀` with `L` affine and nowhere zero;
  cross-block coefficients force `L` to be a nonzero constant
  (`Packing.linear_normal_form`). Then all degree-≥3 coefficients of the target vanish,
  which settles obligation 1; and the degree-2 coefficients are the entries of the
  symmetric form `σ(p,q) = A₀ p · B₀ q + A₀ q · B₀ p`, which cannot have three nonzero
  diagonal blocks with vanishing cross terms (`hyperbolic_three_blocks`, an elementary
  rank-≤2 obstruction). That settles obligation 2.

## Delimiting results

* `exists_two_nonaffine_triples_packing` (`Examples.lean`): two non-affine gadgets on
  **disjoint** input triples that *do* share a row. So the degree hypothesis in
  `degree_three_never_packs` cannot be dropped.
* `shared_degree_three_packs` (`Shared.lean`): **obligation 1 is false when the input
  triples share variables**, even with the packed target genuinely of degree 3. Over `ℚ`
  the row `(1 + x₁ + x₂) · z = x₀` pins `z` uniquely, because `1 + x₁ + x₂` never vanishes
  on the cube; the pinned value `x₀/(1 + x₁ + x₂)` has multilinear form
  `x₀ − x₀x₁/2 − x₀x₂/2 + x₀x₁x₂/3`, of degree 3, and splits as `f + g` with `f`
  non-affine on `{0,1,2}` and `g` non-affine on `{1,2,3}`.
* `shared_three_degree_two_gadgets_pack` (`Shared.lean`): **obligation 2 is false when the
  blocks share variables** — two of three gadgets can cancel on the shared variables.
* `pinned_target_of_degree_three` (`Shared.lean`): pinpoints the step that fails, namely
  "pinned ⇒ degree ≤ 2"; it needs disjointness, since a nonconstant nowhere-vanishing `L`
  makes `E/L` of high degree.

So the disjoint case is proved, and the shared case is settled negatively rather than left
open.
