/-
  Packing several boolean gadgets, on pairwise disjoint blocks of variables, into one
  R1CS row.

  `packedTarget lam f x = ∑ k, lam k * f k x` is the value a single row would have to
  determine: a linear combination, with nonzero multipliers, of gadget outputs living on
  pairwise disjoint blocks of cube variables.

  The two main results here are the two halves of the case analysis on a hypothetical row:

  * `Packing.not_two_affine_branches` : with two non-affine blocks the target cannot agree
    pointwise with either of two affine forms, which rules out the branch in which `z`
    occurs quadratically (the *decoy root* branch);
  * `Packing.linear_normal_form` : consequently any row that pins the packed target must
    have the shape `c * z = C₀ - A₀ * B₀` with `c` a nonzero constant.
-/
import Solution.Research.R1CSRow

namespace Solution.Research

open Finset

namespace Packing

variable {ι : Type*} [DecidableEq ι] {F : Type*} [Field F]
  {κ : Type*} [Fintype κ] [DecidableEq κ]
  {P : κ → Finset ι} {f : κ → Finset ι → F} {lam : κ → F}

/-- The value that a single row is asked to determine: the `lam`-combination of the
gadget outputs `f k`. -/
def packedTarget (lam : κ → F) (f : κ → Finset ι → F) : Finset ι → F :=
  fun x => ∑ k, lam k * f k x

omit [DecidableEq ι] [DecidableEq κ] in
theorem coef_eq_zero_of_not_subset (hsupp : ∀ k, SuppIn (f k) (P k))
    {S : Finset ι} (hS : ∀ k, ¬ S ⊆ P k) : coef (packedTarget lam f) S = 0 := by
  unfold packedTarget
  rw [coef_sum]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [coef_const_mul, hsupp k S (hS k), mul_zero]

omit [DecidableEq ι] [DecidableEq κ] in
theorem exists_block_of_coef_ne_zero (hsupp : ∀ k, SuppIn (f k) (P k))
    {S : Finset ι} (hS : coef (packedTarget lam f) S ≠ 0) : ∃ k, S ⊆ P k := by
  by_contra hc
  push_neg at hc
  exact hS (coef_eq_zero_of_not_subset hsupp hc)

omit [DecidableEq ι] [DecidableEq κ] in
theorem coef_block (hdis : ∀ k l, k ≠ l → Disjoint (P k) (P l))
    (hsupp : ∀ k, SuppIn (f k) (P k)) {k0 : κ} {S : Finset ι} (hS : S ⊆ P k0)
    (hne : S.Nonempty) : coef (packedTarget lam f) S = lam k0 * coef (f k0) S := by
  unfold packedTarget
  rw [coef_sum, Finset.sum_eq_single k0]
  · rw [coef_const_mul]
  · intro k _ hk
    obtain ⟨i, hi⟩ := hne
    have hnot : ¬ S ⊆ P k := fun hc =>
      Finset.disjoint_left.mp (hdis k0 k (Ne.symm hk)) (hS hi) (hc hi)
    rw [coef_const_mul, hsupp k S hnot, mul_zero]
  · intro h; exact absurd (Finset.mem_univ k0) h

omit [DecidableEq κ] in
/-- The coefficient of `A * (packed target)` at `insert j S`, for `S` a subset of one block
and `j` a variable outside that block. -/
theorem coef_aff_mul_insert (hdis : ∀ k l, k ≠ l → Disjoint (P k) (P l))
    (hsupp : ∀ k, SuppIn (f k) (P k)) (A : Aff ι F) {k0 : κ} {j : ι} {S : Finset ι}
    (hS : S ⊆ P k0) (hcard : 2 ≤ S.card) (hj : j ∉ P k0) :
    coef (fun x => A.ev x * packedTarget lam f x) (insert j S)
      = A.coeff j * (lam k0 * coef (f k0) S) := by
  have hfun : ∀ x, A.ev x * packedTarget lam f x = ∑ k, lam k * (A.ev x * f k x) := by
    intro x
    unfold packedTarget
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [coef_congr hfun, coef_sum, Finset.sum_eq_single k0]
  · rw [coef_const_mul, Solution.Research.coef_aff_mul_insert A (hsupp k0) hS hj]
    ring
  · intro k _ hk
    rw [coef_const_mul,
      coef_aff_mul_block_eq_zero A (hsupp k) (hdis k0 k (Ne.symm hk)) hS hcard
        (Finset.subset_insert j S), mul_zero]
  · intro h; exact absurd (Finset.mem_univ k0) h

/-- **No decoy root.**  With two non-affine blocks, the packed target cannot agree
pointwise with one of two affine forms.  This is what kills the branch where `z` occurs
quadratically in the row. -/
theorem not_two_affine_branches (h2 : (2 : F) ≠ 0)
    (hdis : ∀ k l, k ≠ l → Disjoint (P k) (P l)) (hsupp : ∀ k, SuppIn (f k) (P k))
    {k1 k2 : κ} (hk : k1 ≠ k2) {S1 S2 : Finset ι}
    (hS1 : S1 ⊆ P k1) (hS1c : 2 ≤ S1.card) (hc1 : coef (packedTarget lam f) S1 ≠ 0)
    (hS2 : S2 ⊆ P k2) (hS2c : 2 ≤ S2.card) (hc2 : coef (packedTarget lam f) S2 ≠ 0)
    (u v : Aff ι F) :
    ¬ ∀ x, (packedTarget lam f x - u.ev x) * (packedTarget lam f x - v.ev x) = 0 := by
  intro hbr
  set t := packedTarget lam f with ht
  have hd12 : Disjoint (P k1) (P k2) := hdis k1 k2 hk
  have hdS : Disjoint S1 S2 := Finset.disjoint_of_subset_left hS1
    (Finset.disjoint_of_subset_right hS2 hd12)
  have hS1ne : S1.Nonempty := Finset.card_pos.mp (by omega)
  have hS2ne : S2.Nonempty := Finset.card_pos.mp (by omega)
  have hne : S1 ≠ S2 := by
    intro hc
    obtain ⟨i, hi⟩ := hS1ne
    exact Finset.disjoint_left.mp hdS hi (hc ▸ hi)
  -- the identity `t² = (u+v) t - u v` on the cube
  have hid : ∀ x, t x * t x = (u.add v).ev x * t x - u.ev x * v.ev x := by
    intro x
    have h := hbr x
    rw [Aff.ev_add]
    linear_combination h
  -- compute the degree-`S1 ∪ S2` coefficient of both sides
  have hlhs : coef (fun x => t x * t x) (S1 ∪ S2) = coef t S1 * coef t S2 + coef t S2 * coef t S1 := by
    refine coef_mul_eq_of_pair Finset.subset_union_left Finset.subset_union_right hne rfl ?_
    intro U V hU hV hUV hnot
    by_cases hcU : coef t U = 0
    · rw [hcU, zero_mul]
    by_cases hcV : coef t V = 0
    · rw [hcV, mul_zero]
    exfalso
    obtain ⟨a, ha⟩ := exists_block_of_coef_ne_zero hsupp hcU
    obtain ⟨b, hb⟩ := exists_block_of_coef_ne_zero hsupp hcV
    -- `k1` and `k2` must be among `a` and `b`
    have hmem : ∀ {k : κ} {S : Finset ι}, S ⊆ P k → S.Nonempty → S ⊆ S1 ∪ S2 → k = a ∨ k = b := by
      intro k S hSP hSne hSsub
      obtain ⟨i, hi⟩ := hSne
      have hiUV : i ∈ U ∪ V := hUV ▸ hSsub hi
      rcases Finset.mem_union.mp hiUV with hiU | hiV
      · left
        by_contra hka
        exact Finset.disjoint_left.mp (hdis k a hka) (hSP hi) (ha hiU)
      · right
        by_contra hkb
        exact Finset.disjoint_left.mp (hdis k b hkb) (hSP hi) (hb hiV)
    have h1 := hmem hS1 hS1ne Finset.subset_union_left
    have h2' := hmem hS2 hS2ne Finset.subset_union_right
    rcases h1 with rfl | rfl
    · rcases h2' with rfl | rfl
      · exact hk rfl
      · exact hnot (Or.inl (block_pair_eq hd12 hS1 hS2 ha hb hUV))
    · rcases h2' with rfl | rfl
      · refine hnot (Or.inr ?_)
        have := block_pair_eq (hdis k2 k1 (Ne.symm hk)) hS2 hS1 ha hb
          (by rw [hUV, Finset.union_comm])
        exact ⟨this.1, this.2⟩
      · exact hk rfl
  have hrhs : coef (fun x => (u.add v).ev x * t x - u.ev x * v.ev x) (S1 ∪ S2) = 0 := by
    rw [coef_sub]
    have hA : coef (fun x => (u.add v).ev x * t x) (S1 ∪ S2) = 0 := by
      have hfun : ∀ x, (u.add v).ev x * t x = ∑ k, lam k * ((u.add v).ev x * f k x) := by
        intro x
        rw [ht]
        unfold packedTarget
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
      rw [coef_congr hfun, coef_sum]
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hkk : k = k1
      · subst hkk
        rw [coef_const_mul,
          coef_aff_mul_block_eq_zero _ (hsupp k) (hdis k2 k (Ne.symm hk)) hS2 hS2c
            Finset.subset_union_right, mul_zero]
      · rw [coef_const_mul,
          coef_aff_mul_block_eq_zero _ (hsupp k) (hdis k1 k (Ne.symm hkk)) hS1 hS1c
            Finset.subset_union_left, mul_zero]
    have hB : coef (fun x => u.ev x * v.ev x) (S1 ∪ S2) = 0 := by
      refine coef_mul_degLE (degLE_aff u) (degLE_aff v) _ ?_
      have : (S1 ∪ S2).card = S1.card + S2.card := Finset.card_union_of_disjoint hdS
      omega
    rw [hA, hB, sub_zero]
  rw [coef_congr hid, hrhs] at hlhs
  have : coef t S1 * coef t S2 = 0 := by
    have h2c : (2 : F) * (coef t S1 * coef t S2) = 0 := by linear_combination -hlhs
    rcases mul_eq_zero.mp h2c with h | h
    · exact absurd h h2
    · exact h
  rcases mul_eq_zero.mp this with h | h
  · exact hc1 h
  · exact hc2 h

/-- **Normal form.**  Any single row that pins a packed target with (at least) two
non-affine blocks must be of the shape `c * z = C₀ - A₀ * B₀` with `c ≠ 0` a constant:
`z` cannot occur quadratically, and the multiplier of `z` cannot depend on the variables. -/
theorem linear_normal_form (h2 : (2 : F) ≠ 0)
    (hdis : ∀ k l, k ≠ l → Disjoint (P k) (P l)) (hsupp : ∀ k, SuppIn (f k) (P k))
    {k1 k2 : κ} (hk : k1 ≠ k2)
    (hwit : ∀ k, ∃ S : Finset ι, S ⊆ P k ∧ 2 ≤ S.card ∧ coef (packedTarget lam f) S ≠ 0)
    {R : Row ι F} (hpins : R.Pins (packedTarget lam f)) :
    ∃ c : F, c ≠ 0 ∧
      ∀ x, c * packedTarget lam f x = R.C0.ev x - R.A0.ev x * R.B0.ev x := by
  set t := packedTarget lam f with ht
  obtain ⟨S1, hS1, hS1c, hc1⟩ := hwit k1
  obtain ⟨S2, hS2, hS2c, hc2⟩ := hwit k2
  by_cases hquad : R.Az * R.Bz = 0
  · obtain ⟨L, hLne, hL⟩ := R.linear_shape_of_pins hpins hquad h2
    -- the affine multiplier `L` has no linear part
    have hLcoeff : ∀ j : ι, L.coeff j = 0 := by
      intro j
      -- choose a block not containing `j`
      obtain ⟨k0, S, hS, hSc, hcS, hj⟩ :
          ∃ (k0 : κ) (S : Finset ι), S ⊆ P k0 ∧ 2 ≤ S.card ∧ coef t S ≠ 0 ∧ j ∉ P k0 := by
        by_cases hj1 : j ∈ P k1
        · exact ⟨k2, S2, hS2, hS2c, hc2, fun hc =>
            Finset.disjoint_left.mp (hdis k1 k2 hk) hj1 hc⟩
        · exact ⟨k1, S1, hS1, hS1c, hc1, hj1⟩
      have hjS : j ∉ S := fun hc => hj (hS hc)
      have hcard : 3 ≤ (insert j S).card := by
        rw [Finset.card_insert_of_notMem hjS]
        omega
      have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
      have hmain : coef (fun x => L.ev x * t x) (insert j S) = L.coeff j * coef t S := by
        rw [coef_aff_mul_insert hdis hsupp L hS hSc hj, coef_block hdis hsupp hS hSne]
      have hzero : coef (fun x => L.ev x * t x) (insert j S) = 0 := by
        rw [coef_congr hL]
        rw [coef_sub, coef_aff_eq_zero_of_two_le R.C0 (by omega),
          coef_mul_degLE (degLE_aff R.A0) (degLE_aff R.B0) _ (by omega), sub_zero]
      rw [hmain] at hzero
      rcases mul_eq_zero.mp hzero with h | h
      · exact h
      · exact absurd h hcS
    have hconst : ∀ x, L.ev x = L.const := by
      intro x
      rw [Aff.ev]
      simp [hLcoeff]
    refine ⟨L.const, ?_, fun x => ?_⟩
    · have := hLne ∅
      rwa [hconst ∅] at this
    · rw [← hconst x]
      exact hL x
  · exfalso
    obtain ⟨u, v, huv⟩ := R.two_affine_branches_of_pins hpins hquad h2
    exact not_two_affine_branches h2 hdis hsupp hk hS1 hS1c hc1 hS2 hS2c hc2 u v huv

end Packing

end Solution.Research
