/-
  Concrete instances of the two obligations.

  * `and3_never_packs`, `maj_never_packs` : the degree-3 impossibility applied to two
    `AND3` gadgets, resp. to two `Maj` gadgets, on disjoint input triples.
  * `two_and2_gadgets_pack` : two `AND2` gadgets on disjoint variable pairs *do* share a
    single row, with an explicit row.  This shows the cap of two proved in
    `three_gadgets_never_pack` is attained, i.e. degree 2 packs exactly 2.
-/
import Solution.Research.DegreePack

namespace Solution.Research

open Finset

variable {ι : Type*} [DecidableEq ι] {F : Type*} [Field F]

/-! ## Gadgets built from monomials -/

theorem dependsOn_mono {T P : Finset ι} (h : T ⊆ P) : DependsOn (mono T : Finset ι → F) P := by
  intro x y hxy
  have key : ∀ u v : Finset ι, u ∩ P = v ∩ P → T ⊆ u → T ⊆ v := by
    intro u v huv hu i hi
    have : i ∈ u ∩ P := Finset.mem_inter.mpr ⟨hu hi, h hi⟩
    rw [huv] at this
    exact (Finset.mem_inter.mp this).1
  unfold mono
  by_cases hx : T ⊆ x
  · rw [if_pos hx, if_pos (key x y hxy hx)]
  · rw [if_neg hx, if_neg (fun hc => hx (key y x hxy.symm hc))]

theorem DependsOn.add {f g : Finset ι → F} {P : Finset ι} (hf : DependsOn f P)
    (hg : DependsOn g P) : DependsOn (fun x => f x + g x) P := by
  intro x y hxy
  show f x + g x = f y + g y
  rw [hf x y hxy, hg x y hxy]

theorem DependsOn.sub {f g : Finset ι → F} {P : Finset ι} (hf : DependsOn f P)
    (hg : DependsOn g P) : DependsOn (fun x => f x - g x) P := by
  intro x y hxy
  show f x - g x = f y - g y
  rw [hf x y hxy, hg x y hxy]

theorem DependsOn.const_mul {f : Finset ι → F} {P : Finset ι} (c : F) (hf : DependsOn f P) :
    DependsOn (fun x => c * f x) P := by
  intro x y hxy
  show c * f x = c * f y
  rw [hf x y hxy]

theorem not_isAffineOn_mono {T : Finset ι} (hT : 2 ≤ T.card) :
    ¬ IsAffineOn (mono T : Finset ι → F) := by
  refine not_isAffineOn_iff.mpr ⟨T, hT, ?_⟩
  rw [coef_mono]
  simp

theorem not_degLE_two_mono {T : Finset ι} (hT : 3 ≤ T.card) :
    ¬ DegLE (mono T : Finset ι → F) 2 := by
  intro h
  have := h T (by omega)
  rw [coef_mono] at this
  simp at this

/-- **Two `AND3` gadgets on disjoint input triples never share a row.** -/
theorem and3_never_packs (h2 : (2 : F) ≠ 0) {T1 T2 : Finset ι} (hdis : Disjoint T1 T2)
    (h1 : T1.card = 3) (h2' : T2.card = 3) {lam : F} (hlam : lam ≠ 0) (R : Row ι F) :
    ¬ R.Pins (fun x => (mono T1 : Finset ι → F) x + lam * mono T2 x) :=
  degree_three_never_packs h2 hdis (dependsOn_mono (Finset.Subset.refl T1))
    (dependsOn_mono (Finset.Subset.refl T2))
    (not_isAffineOn_mono (by omega)) (not_isAffineOn_mono (by omega)) hlam
    (Or.inl (not_degLE_two_mono (by omega))) R

/-! ## Majority -/

/-- The majority gadget on three distinct variables, as a function on the cube. -/
def maj (a b c : ι) : Finset ι → F :=
  fun x => if (a ∈ x ∧ b ∈ x) ∨ (b ∈ x ∧ c ∈ x) ∨ (a ∈ x ∧ c ∈ x) then 1 else 0

/-- The multilinear form of majority: `ab + bc + ac - 2abc`. -/
theorem maj_eq (a b c : ι) :
    (maj a b c : Finset ι → F)
      = fun x => mono {a, b} x + mono {b, c} x + mono {a, c} x - 2 * mono {a, b, c} x := by
  funext x
  unfold maj mono
  by_cases ha : a ∈ x <;> by_cases hb : b ∈ x <;> by_cases hc : c ∈ x <;>
    simp [ha, hb, hc, Finset.insert_subset_iff, Finset.singleton_subset_iff]
  ring

theorem dependsOn_maj {a b c : ι} : DependsOn (maj a b c : Finset ι → F) {a, b, c} := by
  rw [maj_eq]
  exact ((((dependsOn_mono (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> simp)).add
    (dependsOn_mono (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> simp))).add
    (dependsOn_mono (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> simp))).sub
    (DependsOn.const_mul 2 (dependsOn_mono (Finset.Subset.refl _))))

theorem coef_maj_top {a b c : ι} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    coef (maj a b c : Finset ι → F) {a, b, c} = -2 := by
  have hne1 : ({a, b, c} : Finset ι) ≠ {a, b} := by
    intro hcon
    have : c ∈ ({a, b} : Finset ι) := by rw [← hcon]; simp
    simp at this
    rcases this with rfl | rfl
    · exact hac rfl
    · exact hbc rfl
  have hne2 : ({a, b, c} : Finset ι) ≠ {b, c} := by
    intro hcon
    have : a ∈ ({b, c} : Finset ι) := by rw [← hcon]; simp
    simp at this
    rcases this with rfl | rfl
    · exact hab rfl
    · exact hac rfl
  have hne3 : ({a, b, c} : Finset ι) ≠ {a, c} := by
    intro hcon
    have : b ∈ ({a, c} : Finset ι) := by rw [← hcon]; simp
    simp at this
    rcases this with rfl | rfl
    · exact hab rfl
    · exact hbc rfl
  rw [maj_eq, coef_sub, coef_add, coef_add, coef_const_mul, coef_mono, coef_mono, coef_mono,
    coef_mono]
  rw [if_neg hne1, if_neg hne2, if_neg hne3, if_pos rfl]
  ring

theorem card_triple {a b c : ι} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ({a, b, c} : Finset ι).card = 3 := by
  rw [Finset.card_insert_of_notMem (by simp [hab, hac]),
    Finset.card_insert_of_notMem (by simp [hbc]), Finset.card_singleton]

theorem not_isAffineOn_maj (h2 : (2 : F) ≠ 0) {a b c : ι} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) : ¬ IsAffineOn (maj a b c : Finset ι → F) := by
  refine not_isAffineOn_iff.mpr ⟨{a, b, c}, by rw [card_triple hab hac hbc]; omega, ?_⟩
  rw [coef_maj_top hab hac hbc]
  intro hcon
  exact h2 (by linear_combination -hcon)

theorem not_degLE_two_maj (h2 : (2 : F) ≠ 0) {a b c : ι} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) : ¬ DegLE (maj a b c : Finset ι → F) 2 := by
  intro h
  have := h {a, b, c} (by rw [card_triple hab hac hbc]; omega)
  rw [coef_maj_top hab hac hbc] at this
  exact h2 (by linear_combination -this)

/-- **Two `Maj` gadgets on disjoint input triples never share a row** -- not even with a
decoy root. -/
theorem maj_never_packs (h2 : (2 : F) ≠ 0) {a1 b1 c1 a2 b2 c2 : ι}
    (hab1 : a1 ≠ b1) (hac1 : a1 ≠ c1) (hbc1 : b1 ≠ c1)
    (hab2 : a2 ≠ b2) (hac2 : a2 ≠ c2) (hbc2 : b2 ≠ c2)
    (hdis : Disjoint ({a1, b1, c1} : Finset ι) {a2, b2, c2})
    {lam : F} (hlam : lam ≠ 0) (R : Row ι F) :
    ¬ R.Pins (fun x => (maj a1 b1 c1 : Finset ι → F) x + lam * maj a2 b2 c2 x) :=
  degree_three_never_packs h2 hdis dependsOn_maj dependsOn_maj
    (not_isAffineOn_maj h2 hab1 hac1 hbc1) (not_isAffineOn_maj h2 hab2 hac2 hbc2) hlam
    (Or.inl (not_degLE_two_maj h2 hab1 hac1 hbc1)) R

/-! ## Two degree-2 gadgets do share a row

Two `AND2` gadgets on disjoint pairs of variables, with an arbitrary multiplier `lam`, are
pinned by one explicit row.  The row needs no decoy: it determines `z` uniquely.

This has two consequences.  It shows the cap of two proved in `three_gadgets_never_pack`
is attained, so degree 2 packs *exactly* two.  And, since an `AND2` gadget reading two of
the three variables of a block is a non-affine function of that block, it **refutes** the
unrestricted form of Obligation 1: two non-affine gadgets on disjoint input triples can
share a row.  A degree hypothesis such as the one in `degree_three_never_packs` is
therefore necessary. -/

/-- An affine coefficient vector supported on (at most) four variables. -/
def packCoeff (i0 i1 i2 i3 : ι) (c0 c1 c2 c3 : F) : ι → F := fun i =>
  (if i = i0 then c0 else 0) + (if i = i1 then c1 else 0) + (if i = i2 then c2 else 0)
    + (if i = i3 then c3 else 0)

theorem sum_packCoeff (i0 i1 i2 i3 : ι) (c0 c1 c2 c3 : F) (x : Finset ι) :
    ∑ i ∈ x, packCoeff i0 i1 i2 i3 c0 c1 c2 c3 i
      = (if i0 ∈ x then c0 else 0) + (if i1 ∈ x then c1 else 0) + (if i2 ∈ x then c2 else 0)
        + (if i3 ∈ x then c3 else 0) := by
  unfold packCoeff
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_ite_eq' x i0 (fun _ => c0), Finset.sum_ite_eq' x i1 (fun _ => c1),
    Finset.sum_ite_eq' x i2 (fun _ => c2), Finset.sum_ite_eq' x i3 (fun _ => c3)]

/-- The explicit row that packs `AND2 i0 i1 + lam * AND2 i2 i3`. -/
def and2PackRow (i0 i1 i2 i3 : ι) (lam : F) : Row ι F where
  Az := 0
  A0 := ⟨0, packCoeff i0 i1 i2 i3 1 (1 / 2) 1 (-(lam / 2))⟩
  Bz := 0
  B0 := ⟨0, packCoeff i0 i1 i2 i3 1 (1 / 2) (-1) (lam / 2)⟩
  Cz := 1
  C0 := ⟨0, packCoeff i0 i1 i2 i3 1 (1 / 4) (-1) (-(lam ^ 2 / 4))⟩

/-- **Two `AND2` gadgets on disjoint variable pairs share a single row.**

The intended reading is that `i0, i1, i2, i3` are four distinct variables; the identity
that proves it holds for arbitrary indices, so no distinctness hypothesis is needed. -/
theorem two_and2_gadgets_pack (h2 : (2 : F) ≠ 0) (i0 i1 i2 i3 : ι) (lam : F) :
    (and2PackRow i0 i1 i2 i3 lam).Pins
      (fun x => (mono {i0, i1} : Finset ι → F) x + lam * mono {i2, i3} x) := by
  have h4 : (4 : F) ≠ 0 := by
    have h : (4 : F) = 2 * 2 := by norm_num
    rw [h]
    exact mul_ne_zero h2 h2
  have key : ∀ x : Finset ι,
      (and2PackRow i0 i1 i2 i3 lam).A0.ev x * (and2PackRow i0 i1 i2 i3 lam).B0.ev x
        - (and2PackRow i0 i1 i2 i3 lam).C0.ev x
        = (mono {i0, i1} : Finset ι → F) x + lam * mono {i2, i3} x := by
    intro x
    simp only [and2PackRow, Aff.ev, sum_packCoeff, mono, zero_add]
    by_cases hm0 : i0 ∈ x <;> by_cases hm1 : i1 ∈ x <;> by_cases hm2 : i2 ∈ x <;>
      by_cases hm3 : i3 ∈ x <;>
      simp [hm0, hm1, hm2, hm3, Finset.insert_subset_iff, Finset.singleton_subset_iff] <;>
      field_simp [h2, h4] <;> ring
  have hsat : ∀ (x : Finset ι) (z : F), (and2PackRow i0 i1 i2 i3 lam).Sat x z ↔
      z = (mono {i0, i1} : Finset ι → F) x + lam * mono {i2, i3} x := by
    intro x z
    rw [Row.Sat]
    have hk := key x
    simp only [and2PackRow] at hk ⊢
    constructor
    · intro h; linear_combination hk - h
    · intro h; linear_combination hk - h
  exact ⟨⟨0, fun _ => 0⟩, fun x => (hsat x _).2 rfl, fun x z hz => Or.inl ((hsat x z).1 hz)⟩

/-- **The unrestricted form of Obligation 1 is false.**  There are two functions `f`, `g`,
non-affine on the cube and reading two *disjoint input triples*, and a nonzero multiplier
`lam`, such that a single R1CS row does determine `z = f x + lam * g x` (here even
uniquely, with no decoy root).  Both gadgets have multilinear degree 2. -/
theorem exists_two_nonaffine_triples_packing (h2 : (2 : F) ≠ 0) :
    ∃ (P Q : Finset (Fin 6)) (f g : Finset (Fin 6) → F) (lam : F) (R : Row (Fin 6) F),
      Disjoint P Q ∧ P.card = 3 ∧ Q.card = 3 ∧ DependsOn f P ∧ DependsOn g Q ∧
      ¬ IsAffineOn f ∧ ¬ IsAffineOn g ∧ lam ≠ 0 ∧
      R.Pins (fun x => f x + lam * g x) := by
  refine ⟨{0, 1, 2}, {3, 4, 5}, mono {0, 1}, mono {3, 4}, 1,
    and2PackRow 0 1 3 4 1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, one_ne_zero, ?_⟩
  · decide
  · decide
  · decide
  · exact dependsOn_mono (by decide)
  · exact dependsOn_mono (by decide)
  · exact not_isAffineOn_mono (by decide)
  · exact not_isAffineOn_mono (by decide)
  · simpa using two_and2_gadgets_pack h2 (0 : Fin 6) 1 3 4 1

end Solution.Research
