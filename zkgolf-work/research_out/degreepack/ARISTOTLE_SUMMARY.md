# Summary of changes for run 098c7cf1-c810-490f-995b-1b8262a6a7ef
Both questions are settled, in `Solution/Research/` (all committed and pushed; `lake build` and `lake build Solution` both compile with zero errors, and `rg` finds no `sorry`/`admit`/`axiom`/`native_decide`/`bv_decide` anywhere in `Solution/`).

## How "a single R1CS row determines z" is formalised

A point of the cube `{0,1}^ι` is a `Finset ι`; `coef t S` (`Multilinear.lean`) is the coefficient of `∏ i ∈ S, x i` in the unique multilinear polynomial for `t`, and `DegLE`, `IsAffineOn`, `DependsOn` are phrased with it. A row (`R1CSRow.lean`) is `A * B = C` with each slot `(z-coefficient)·z + (affine form in x)`, so **z may occur quadratically**. Determination is

```lean
def Row.Pins (R : Row ι F) (t : Finset ι → F) : Prop :=
  ∃ D : Aff ι F, (∀ x, R.Sat x (t x)) ∧ ∀ x z, R.Sat x z → z = t x ∨ z = D.ev x
```

completeness plus soundness **up to one affine decoy root**; unique determination is the case where the decoy is unused, so `¬ R.Pins t` is strictly stronger than ruling out unique determination.

## Proved (disjoint input blocks, field with `2 ≠ 0`)

- `degree_three_never_packs` — two non-affine gadgets on disjoint blocks, `lam ≠ 0`, packed target of multilinear degree ≥ 3: no row pins it. Obligation 1.
- `three_gadgets_never_pack` — three non-affine gadgets on pairwise disjoint blocks, nonzero multipliers: never pinned, whatever their degrees; `degree_two_packs_at_most_two` restates it for degree 2. Obligation 2, upper half.
- `two_and2_gadgets_pack` — an explicit row pinning `AND2 + lam·AND2` uniquely, so the cap 2 is attained: degree 2 packs exactly 2.
- `and3_never_packs`, `maj_never_packs` — the degree-3 result for AND3 and for Maj on disjoint triples.
- Supporting: `Row.pins_dichotomy`, `Packing.not_two_affine_branches`, `Packing.linear_normal_form`, `hyperbolic_three_blocks` (elementary rank-≤2 obstruction), and the multilinear toolkit incl. `coef_inversion`, `not_isAffineOn_iff`.

**The decoy-root case is handled, and it is the first branch of the argument**: `Row.pins_dichotomy` splits on `Az·Bz ≠ 0`; in that branch the target agrees pointwise with one of two affine forms, and the coefficient at `S₁ ∪ S₂` for degree-≥2 witnesses in two different blocks gives `2·c₁·c₂ = 0`, a contradiction (this is where `2 ≠ 0` is genuinely needed). The other branch gives `L·t = C₀ − A₀B₀` with `L` nowhere zero; cross-block coefficients force `L` constant, killing degree ≥ 3 and, via the σ-form, three blocks.

## Shared variables: settled negatively, not left open (`Shared.lean`)

- `shared_degree_three_packs` — **obligation 1 is false for gadgets sharing input variables**, even with the packed target genuinely cubic. Over ℚ the row `(1 + x₁ + x₂)·z = x₀` pins `z` uniquely (no decoy), since `1 + x₁ + x₂` never vanishes on the cube; the pinned value `x₀/(1+x₁+x₂)` has multilinear form `x₀ − x₀x₁/2 − x₀x₂/2 + x₀x₁x₂/3` (coefficient 1/3 on `x₀x₁x₂`) and splits as `f + 1·g` with `f` non-affine on `{0,1,2}` and `g` non-affine on `{1,2,3}`.
- `shared_three_degree_two_gadgets_pack` — **obligation 2 is false for shared blocks**: two of three gadgets cancel on shared variables.
- `pinned_target_of_degree_three` — pinpoints the step that breaks: "pinned ⇒ degree ≤ 2" needs disjointness.

## Also delimiting the disjoint statement

- `exists_two_nonaffine_triples_packing` — two non-affine gadgets on **disjoint** triples that *do* share a row (both of degree 2). So the degree hypothesis in `degree_three_never_packs` cannot be dropped; an unqualified "non-affine degree-3-block gadgets never pack" would be false.

## Axioms

`AxiomCheck.lean` prints, for every result below, exactly `[propext, Classical.choice, Quot.sound]`:
`degree_three_never_packs`, `three_gadgets_never_pack`, `degree_two_packs_at_most_two`, `no_row_pins_of_degree_three`, `no_row_pins_three_blocks`, `and3_never_packs`, `maj_never_packs`, `two_and2_gadgets_pack`, `exists_two_nonaffine_triples_packing`, `Packing.linear_normal_form`, `Packing.not_two_affine_branches`, `coef_inversion`, `not_isAffineOn_iff`, `Row.pins_dichotomy`, `sharedRow_pins`, `pinned_target_of_degree_three`, `shared_degree_three_packs`, `shared_three_degree_two_gadgets_pack`.

`Solution/Research/README.md` records the same scope summary next to the code. Note that `Solution` is not a default lakefile target, so use `lake build Solution` to build this directory; the pre-existing `sorry`s reported by the plain `lake build` are in the `Challenge/` tree and were not touched.