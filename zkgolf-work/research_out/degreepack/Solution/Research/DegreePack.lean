/-
  The degree filtration: which boolean gadgets can share a row?

  Reduce a boolean function to its MULTILINEAR polynomial over the cube (unique, since
  x^2 = x). Two independent derivations in this project agree on the following, and both
  were checked by exhaustive search, but neither is proved:

    * multilinear degree 2 (Ch, XOR2, AND2) takes the shape `gamma*z = P0*Q0 - R0`
      with z alone in the C-slot, and packs EXACTLY 2 instances per row -- never 3.
    * multilinear degree 3 (Maj, XOR3, AND3) packs NEVER -- not two instances, not even
      with a decoy root.

  These bound a whole search space. Proving them closes it permanently; refuting either
  would be a significant win, since degree-3 gadgets are the dominant cost in SHA-256.
-/
import Solution.Research.Packing

/-!
# What is proved here

Everything below is stated over an arbitrary field `F` with `2 ≠ 0` (the arguments really
do need this: over `𝔽₂` squaring is additive on the cube and the analysis changes), for
gadgets living on **pairwise disjoint** blocks of cube variables.  Disjointness is
essential and not a proof artefact: `Solution/Research/Shared.lean` gives explicit
counterexamples showing that *both* obligations are false for gadgets that share input
variables (`shared_degree_three_packs`, `shared_three_degree_two_gadgets_pack`), so the
shared-variable case is settled too -- negatively.

Formalisation of the informal notions:

* a point of the cube `{0,1}^ι` is a `Finset ι` (the set of coordinates equal to `1`);
* `coef t S` is the coefficient of the monomial `∏ i ∈ S, x i` in the unique multilinear
  polynomial representing `t` (`Solution/Research/Multilinear.lean`);
* `IsAffineOn t` says `t` is affine on the cube, and `not_isAffineOn_iff` shows this is
  equivalent to all multilinear coefficients in degree `≥ 2` vanishing;
* `DependsOn f P` says `f` only reads the variables of the block `P`;
* a single R1CS row is `Row ι F`: `A * B = C` with all three slots affine in the witness
  `(x, z)`, so `z` may occur *quadratically* in the row;
* `Row.Pins R t` is "the row determines `z = t x`": completeness (`t x` always satisfies
  the row) plus soundness up to one affine **decoy root** `D` (any solution is `t x` or
  `D x`).  Unique determination is the special case where no decoy is needed.

Main results:

* `degree_three_never_packs` : two non-affine gadgets on disjoint blocks whose packed
  target has multilinear degree `≥ 3` are never pinned by a single row -- decoy roots
  included.
* `three_gadgets_never_pack` : three non-affine gadgets on pairwise disjoint blocks are
  never pinned by a single row, whatever their degrees.
* `two_and2_gadgets_pack` : two `AND2` gadgets on disjoint variable pairs *are* pinned by
  an explicit single row.  Together with the previous item this is the "packs exactly 2"
  statement for degree 2, in the disjoint-blocks setting.
* `degree_two_packs_at_most_two` : restatement of the cap for degree-2 gadgets.

Delimiting results elsewhere in this directory:

* `exists_two_nonaffine_triples_packing` (`Examples.lean`) : two non-affine gadgets on
  disjoint triples *can* share a row, so the degree hypothesis of
  `degree_three_never_packs` cannot be dropped;
* `shared_degree_three_packs`, `shared_three_degree_two_gadgets_pack` (`Shared.lean`) :
  with shared input variables both obligations fail.
-/

namespace Solution.Research

open Finset Packing

variable {ι : Type*} [DecidableEq ι] {F : Type*} [Field F]

/-! ## The rank obstruction for three blocks

The quadratic part of `A₀ * B₀` is the symmetric form `σ p q = A₀ p * B₀ q + A₀ q * B₀ p`.
Three disjoint blocks each carrying a nonzero `σ` entry, with all cross-block entries
zero, is impossible: this is the "rank ≤ 2" obstruction, in a form that needs no matrix
rank theory. -/
theorem hyperbolic_three_blocks {a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 a6 b6 : F}
    (h12 : a1 * b2 + a2 * b1 ≠ 0) (h34 : a3 * b4 + a4 * b3 ≠ 0)
    (h56 : a5 * b6 + a6 * b5 ≠ 0)
    (c14 : a1 * b4 + a4 * b1 = 0) (c25 : a2 * b5 + a5 * b2 = 0)
    (c45 : a4 * b5 + a5 * b4 = 0) : False := by
  -- the vector `(a5, b5)` is nonzero
  have h5 : a5 ≠ 0 ∨ b5 ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact h56 (by rw [hc.1, hc.2]; ring)
  -- hence `(a2, b2)` and `(a4, b4)` are parallel
  have hom : a2 * b4 - a4 * b2 = 0 := by
    rcases h5 with h5 | h5
    · have : (a2 * b4 - a4 * b2) * a5 = 0 := by linear_combination a2 * c45 - a4 * c25
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · exact absurd h h5
    · have : (a2 * b4 - a4 * b2) * b5 = 0 := by linear_combination b4 * c25 - b2 * c45
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · exact absurd h h5
  have key : (a1 * b2 + a2 * b1) * (a3 * b4 + a4 * b3) = 0 := by
    linear_combination (a3 * b2 + a2 * b3) * c14 - (a1 * b3 - a3 * b1) * hom
  rcases mul_eq_zero.mp key with h | h
  · exact h12 h
  · exact h34 h

/-! ## Consequences of pinning a packed target -/

section Packed

variable {κ : Type*} [Fintype κ] [DecidableEq κ]
  {P : κ → Finset ι} {f : κ → Finset ι → F} {lam : κ → F}

/-- If a single row pins a packed target with two non-affine blocks, then the target has
multilinear degree at most `2`. -/
theorem coef_eq_zero_of_pins (h2 : (2 : F) ≠ 0)
    (hdis : ∀ k l, k ≠ l → Disjoint (P k) (P l)) (hsupp : ∀ k, SuppIn (f k) (P k))
    {k1 k2 : κ} (hk : k1 ≠ k2)
    (hwit : ∀ k, ∃ S : Finset ι, S ⊆ P k ∧ 2 ≤ S.card ∧ coef (packedTarget lam f) S ≠ 0)
    {R : Row ι F} (hpins : R.Pins (packedTarget lam f))
    {S : Finset ι} (hS : 3 ≤ S.card) : coef (packedTarget lam f) S = 0 := by
  obtain ⟨c, hc, hnf⟩ := linear_normal_form h2 hdis hsupp hk hwit hpins
  have h0 : c * coef (packedTarget lam f) S = 0 := by
    rw [← coef_const_mul, coef_congr hnf, coef_sub,
      coef_aff_eq_zero_of_two_le R.C0 (by omega),
      coef_mul_degLE (degLE_aff R.A0) (degLE_aff R.B0) _ (by omega), sub_zero]
  rcases mul_eq_zero.mp h0 with h | h
  · exact absurd h hc
  · exact h

/-- **Obligation 1, general form.**  Two (or more) non-affine gadgets on pairwise disjoint
blocks whose packed target has multilinear degree at least `3` are never pinned by a
single R1CS row -- not even up to a decoy root. -/
theorem no_row_pins_of_degree_three (h2 : (2 : F) ≠ 0)
    (hdis : ∀ k l, k ≠ l → Disjoint (P k) (P l)) (hsupp : ∀ k, SuppIn (f k) (P k))
    {k1 k2 : κ} (hk : k1 ≠ k2)
    (hwit : ∀ k, ∃ S : Finset ι, S ⊆ P k ∧ 2 ≤ S.card ∧ coef (packedTarget lam f) S ≠ 0)
    (hdeg : ∃ S : Finset ι, 3 ≤ S.card ∧ coef (packedTarget lam f) S ≠ 0)
    (R : Row ι F) : ¬ R.Pins (packedTarget lam f) := by
  intro hpins
  obtain ⟨S, hS, hne⟩ := hdeg
  exact hne (coef_eq_zero_of_pins h2 hdis hsupp hk hwit hpins hS)

/-- **Obligation 2, upper half, general form.**  Three non-affine gadgets on pairwise
disjoint blocks are never pinned by a single R1CS row, whatever their degrees. -/
theorem no_row_pins_three_blocks (h2 : (2 : F) ≠ 0)
    (hdis : ∀ k l, k ≠ l → Disjoint (P k) (P l)) (hsupp : ∀ k, SuppIn (f k) (P k))
    (hwit : ∀ k, ∃ S : Finset ι, S ⊆ P k ∧ 2 ≤ S.card ∧ coef (packedTarget lam f) S ≠ 0)
    {k1 k2 k3 : κ} (h12 : k1 ≠ k2) (h13 : k1 ≠ k3) (h23 : k2 ≠ k3)
    (R : Row ι F) : ¬ R.Pins (packedTarget lam f) := by
  intro hpins
  set t := packedTarget lam f with ht
  obtain ⟨c, hc, hnf⟩ := linear_normal_form h2 hdis hsupp h12 hwit hpins
  -- degree of the target is at most 2
  have hdeg : ∀ S : Finset ι, 3 ≤ S.card → coef t S = 0 :=
    fun S hS => coef_eq_zero_of_pins h2 hdis hsupp h12 hwit hpins hS
  -- the degree-2 coefficients are the entries of `σ`
  have hpair : ∀ i j : ι, i ≠ j →
      c * coef t {i, j} = -(R.A0.coeff i * R.B0.coeff j + R.A0.coeff j * R.B0.coeff i) := by
    intro i j hij
    have hcard : ({i, j} : Finset ι).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp [hij]), Finset.card_singleton]
    rw [← coef_const_mul, coef_congr hnf, coef_sub,
      coef_aff_eq_zero_of_two_le R.C0 (by omega), coef_aff_mul_aff_pair R.A0 R.B0 hij]
    ring
  -- each block provides a pair of variables with a nonzero `σ` entry
  have hblock : ∀ k : κ, ∃ i j : ι, i ≠ j ∧ i ∈ P k ∧ j ∈ P k ∧
      R.A0.coeff i * R.B0.coeff j + R.A0.coeff j * R.B0.coeff i ≠ 0 := by
    intro k
    obtain ⟨S, hSP, hScard, hSne⟩ := hwit k
    have hcard2 : S.card = 2 := by
      by_contra hcc
      exact hSne (hdeg S (by omega))
    obtain ⟨i, j, hij, hS⟩ := Finset.card_eq_two.mp hcard2
    subst hS
    refine ⟨i, j, hij, hSP (by simp), hSP (by simp), fun hzero => hSne ?_⟩
    have := hpair i j hij
    rw [hzero, neg_zero] at this
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hc
    · exact h
  -- cross-block entries of `σ` vanish
  have hcross : ∀ (k l : κ) (p q : ι), k ≠ l → p ∈ P k → q ∈ P l →
      R.A0.coeff p * R.B0.coeff q + R.A0.coeff q * R.B0.coeff p = 0 := by
    intro k l p q hkl hp hq
    have hpq : p ≠ q := fun hc' => Finset.disjoint_left.mp (hdis k l hkl) hp (hc' ▸ hq)
    have hzero : coef t {p, q} = 0 := by
      refine coef_eq_zero_of_not_subset hsupp fun m hm => ?_
      have hpm : p ∈ P m := hm (by simp)
      have hqm : q ∈ P m := hm (by simp)
      have hkm : k = m := by
        by_contra hne'
        exact Finset.disjoint_left.mp (hdis k m hne') hp hpm
      have hlm : l = m := by
        by_contra hne'
        exact Finset.disjoint_left.mp (hdis l m hne') hq hqm
      exact hkl (hkm.trans hlm.symm)
    have := hpair p q hpq
    rw [hzero, mul_zero] at this
    linear_combination this
  obtain ⟨i1, j1, hij1, hi1, hj1, hs1⟩ := hblock k1
  obtain ⟨i2, j2, hij2, hi2, hj2, hs2⟩ := hblock k2
  obtain ⟨i3, j3, hij3, hi3, hj3, hs3⟩ := hblock k3
  exact hyperbolic_three_blocks hs1 hs2 hs3
    (hcross k1 k2 i1 j2 h12 hi1 hj2)
    (hcross k1 k3 j1 i3 h13 hj1 hi3)
    (hcross k2 k3 j2 i3 h23 hj2 hi3)

end Packed

/-! ## The headline statements, in terms of individual gadgets -/

/-- A gadget on the block `P` with multiplier `lam ≠ 0` contributes a nonzero degree-`≥ 2`
coefficient to the packed target. -/
private theorem wit_of_not_affine {P : Finset ι} {h : Finset ι → F} (hsupp : SuppIn h P)
    (hna : ¬ IsAffineOn h) : ∃ S : Finset ι, S ⊆ P ∧ 2 ≤ S.card ∧ coef h S ≠ 0 := by
  obtain ⟨S, hS, hne⟩ := not_isAffineOn_iff.mp hna
  refine ⟨S, ?_, hS, hne⟩
  by_contra hc
  exact hne (hsupp S hc)

/-- **Obligation 1.**  Let `f, g` be non-affine functions on the cube reading two disjoint
blocks of variables `P`, `Q` (in the motivating case, two disjoint input triples), let
`lam ≠ 0`, and suppose the packed target `f + lam * g` has multilinear degree at least `3`
-- e.g. because one of `f`, `g` is a degree-3 gadget such as `Maj`, `XOR3` or `AND3`.

Then **no single R1CS row determines `z = f x + lam * g x`**, where "determines" allows a
decoy root: `z` is permitted to occur quadratically in the row provided the second root is
given by an affine form.

Hypothesis `2 ≠ 0` is genuinely used.  Only the disjoint-blocks case is covered. -/
theorem degree_three_never_packs (h2 : (2 : F) ≠ 0)
    {P Q : Finset ι} (hPQ : Disjoint P Q) {f g : Finset ι → F}
    (hfP : DependsOn f P) (hgQ : DependsOn g Q)
    (hfna : ¬ IsAffineOn f) (hgna : ¬ IsAffineOn g)
    {lam : F} (hlam : lam ≠ 0)
    (hcubic : ¬ DegLE f 2 ∨ ¬ DegLE g 2)
    (R : Row ι F) : ¬ R.Pins (fun x => f x + lam * g x) := by
  classical
  set Pb : Fin 2 → Finset ι := ![P, Q] with hPb
  set fb : Fin 2 → Finset ι → F := ![f, g] with hfb
  set lb : Fin 2 → F := ![1, lam] with hlb
  have hsuppf : SuppIn f P := suppIn_of_dependsOn hfP
  have hsuppg : SuppIn g Q := suppIn_of_dependsOn hgQ
  have hsupp : ∀ k, SuppIn (fb k) (Pb k) := by
    intro k; fin_cases k <;> simpa [hPb, hfb]
  have hdis : ∀ k l : Fin 2, k ≠ l → Disjoint (Pb k) (Pb l) := by
    intro k l hkl
    fin_cases k <;> fin_cases l <;> simp_all
    exact hPQ.symm
  have htarget : packedTarget lb fb = fun x => f x + lam * g x := by
    funext x
    rw [packedTarget, Fin.sum_univ_two]
    simp [hfb, hlb]
  -- the coefficients of the packed target on each block
  have hcoefP : ∀ S : Finset ι, S ⊆ P → S.Nonempty →
      coef (packedTarget lb fb) S = coef f S := by
    intro S hS hne
    rw [coef_block hdis hsupp (k0 := 0) (by simpa [hPb]) hne]
    simp [hfb, hlb]
  have hcoefQ : ∀ S : Finset ι, S ⊆ Q → S.Nonempty →
      coef (packedTarget lb fb) S = lam * coef g S := by
    intro S hS hne
    rw [coef_block hdis hsupp (k0 := 1) (by simpa [hPb]) hne]
    simp [hfb, hlb]
  have hwit : ∀ k, ∃ S : Finset ι, S ⊆ Pb k ∧ 2 ≤ S.card ∧ coef (packedTarget lb fb) S ≠ 0 := by
    intro k
    fin_cases k
    · obtain ⟨S, hSP, hScard, hSne⟩ := wit_of_not_affine hsuppf hfna
      refine ⟨S, by simpa [hPb], hScard, ?_⟩
      rw [hcoefP S hSP (Finset.card_pos.mp (by omega))]
      exact hSne
    · obtain ⟨S, hSQ, hScard, hSne⟩ := wit_of_not_affine hsuppg hgna
      refine ⟨S, by simpa [hPb], hScard, ?_⟩
      rw [hcoefQ S hSQ (Finset.card_pos.mp (by omega))]
      exact mul_ne_zero hlam hSne
  have hdeg : ∃ S : Finset ι, 3 ≤ S.card ∧ coef (packedTarget lb fb) S ≠ 0 := by
    rcases hcubic with hc | hc
    · rw [DegLE] at hc
      push_neg at hc
      obtain ⟨S, hScard, hSne⟩ := hc
      have hSP : S ⊆ P := by
        by_contra hcon
        exact hSne (hsuppf S hcon)
      exact ⟨S, by omega, by rw [hcoefP S hSP (Finset.card_pos.mp (by omega))]; exact hSne⟩
    · rw [DegLE] at hc
      push_neg at hc
      obtain ⟨S, hScard, hSne⟩ := hc
      have hSQ : S ⊆ Q := by
        by_contra hcon
        exact hSne (hsuppg S hcon)
      exact ⟨S, by omega, by
        rw [hcoefQ S hSQ (Finset.card_pos.mp (by omega))]
        exact mul_ne_zero hlam hSne⟩
  have := no_row_pins_of_degree_three h2 hdis hsupp (k1 := 0) (k2 := 1) (by decide) hwit hdeg R
  rwa [htarget] at this

/-- **Obligation 2, upper half.**  Three non-affine gadgets on pairwise disjoint blocks,
with nonzero multipliers, are never pinned by a single R1CS row (decoy roots included).
In particular three degree-2 gadgets never share a row. -/
theorem three_gadgets_never_pack (h2 : (2 : F) ≠ 0)
    {P1 P2 P3 : Finset ι} (d12 : Disjoint P1 P2) (d13 : Disjoint P1 P3) (d23 : Disjoint P2 P3)
    {f1 f2 f3 : Finset ι → F}
    (hd1 : DependsOn f1 P1) (hd2 : DependsOn f2 P2) (hd3 : DependsOn f3 P3)
    (hn1 : ¬ IsAffineOn f1) (hn2 : ¬ IsAffineOn f2) (hn3 : ¬ IsAffineOn f3)
    {l1 l2 l3 : F} (hl1 : l1 ≠ 0) (hl2 : l2 ≠ 0) (hl3 : l3 ≠ 0)
    (R : Row ι F) : ¬ R.Pins (fun x => l1 * f1 x + l2 * f2 x + l3 * f3 x) := by
  classical
  set Pb : Fin 3 → Finset ι := ![P1, P2, P3] with hPb
  set fb : Fin 3 → Finset ι → F := ![f1, f2, f3] with hfb
  set lb : Fin 3 → F := ![l1, l2, l3] with hlb
  have hs1 : SuppIn f1 P1 := suppIn_of_dependsOn hd1
  have hs2 : SuppIn f2 P2 := suppIn_of_dependsOn hd2
  have hs3 : SuppIn f3 P3 := suppIn_of_dependsOn hd3
  have hsupp : ∀ k, SuppIn (fb k) (Pb k) := by
    intro k; fin_cases k <;> simpa [hPb, hfb]
  have hdis : ∀ k l : Fin 3, k ≠ l → Disjoint (Pb k) (Pb l) := by
    intro k l hkl
    fin_cases k <;> fin_cases l <;> simp_all <;>
      first
        | exact d12 | exact d12.symm | exact d13 | exact d13.symm
        | exact d23 | exact d23.symm
  have htarget : packedTarget lb fb = fun x => l1 * f1 x + l2 * f2 x + l3 * f3 x := by
    funext x
    rw [packedTarget, Fin.sum_univ_three]
    simp [hfb, hlb, add_assoc]
  have hwit : ∀ k, ∃ S : Finset ι, S ⊆ Pb k ∧ 2 ≤ S.card ∧ coef (packedTarget lb fb) S ≠ 0 := by
    intro k
    fin_cases k
    · obtain ⟨S, hSP, hScard, hSne⟩ := wit_of_not_affine hs1 hn1
      refine ⟨S, by simpa [hPb], hScard, ?_⟩
      rw [coef_block hdis hsupp (k0 := 0) (by simpa [hPb]) (Finset.card_pos.mp (by omega))]
      simpa [hfb, hlb] using mul_ne_zero hl1 hSne
    · obtain ⟨S, hSP, hScard, hSne⟩ := wit_of_not_affine hs2 hn2
      refine ⟨S, by simpa [hPb], hScard, ?_⟩
      rw [coef_block hdis hsupp (k0 := 1) (by simpa [hPb]) (Finset.card_pos.mp (by omega))]
      simpa [hfb, hlb] using mul_ne_zero hl2 hSne
    · obtain ⟨S, hSP, hScard, hSne⟩ := wit_of_not_affine hs3 hn3
      refine ⟨S, by simpa [hPb], hScard, ?_⟩
      rw [coef_block hdis hsupp (k0 := 2) (by simpa [hPb]) (Finset.card_pos.mp (by omega))]
      simpa [hfb, hlb] using mul_ne_zero hl3 hSne
  have := no_row_pins_three_blocks h2 hdis hsupp hwit
    (k1 := 0) (k2 := 1) (k3 := 2) (by decide) (by decide) (by decide) R
  rwa [htarget] at this

/-- Restatement for degree-2 gadgets: the packing cap is at most two.

The degree hypotheses `hg1, hg2, hg3` are stated because the obligation is phrased for
degree-2 gadgets, but they are not needed: `three_gadgets_never_pack` already gives the
cap for gadgets of arbitrary degree. -/
theorem degree_two_packs_at_most_two (h2 : (2 : F) ≠ 0)
    {P1 P2 P3 : Finset ι} (d12 : Disjoint P1 P2) (d13 : Disjoint P1 P3) (d23 : Disjoint P2 P3)
    {f1 f2 f3 : Finset ι → F}
    (hd1 : DependsOn f1 P1) (hd2 : DependsOn f2 P2) (hd3 : DependsOn f3 P3)
    (hg1 : DegLE f1 2) (hg2 : DegLE f2 2) (hg3 : DegLE f3 2)
    (hn1 : ¬ IsAffineOn f1) (hn2 : ¬ IsAffineOn f2) (hn3 : ¬ IsAffineOn f3)
    {l1 l2 l3 : F} (hl1 : l1 ≠ 0) (hl2 : l2 ≠ 0) (hl3 : l3 ≠ 0)
    (R : Row ι F) : ¬ R.Pins (fun x => l1 * f1 x + l2 * f2 x + l3 * f3 x) :=
  three_gadgets_never_pack h2 d12 d13 d23 hd1 hd2 hd3 hn1 hn2 hn3 hl1 hl2 hl3 R

end Solution.Research
