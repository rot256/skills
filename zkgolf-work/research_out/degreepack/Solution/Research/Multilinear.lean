/-
  Multilinear coefficients of functions on the Boolean cube.

  A point of the cube `{0,1}^ι` is identified with the finset of coordinates that are `1`,
  so a "function on the cube" is a map `Finset ι → F`.  Every such function is the
  restriction to the cube of a unique multilinear polynomial
  `t = ∑ S, coef t S * ∏ i ∈ S, x i`, and `coef t S` (defined below by Möbius inversion)
  is that unique family of coefficients.

  This file develops exactly the toolkit needed in `DegreePack.lean`:

  * `coef_mono`      : the coefficients of a monomial;
  * `coef_inversion` : `t x = ∑ S ⊆ x, coef t S` (uniqueness / completeness of `coef`);
  * `coef_mul`       : the product rule `coef (f*g) S = ∑_{U ∪ V = S} coef f U * coef g V`;
  * `SuppIn`         : "the multilinear polynomial only uses variables from a block";
  * `DegLE`          : "the multilinear polynomial has degree at most `d`";
  * `Aff`            : affine forms, their coefficients, and `IsAffineOn`.
-/
import Mathlib

namespace Solution.Research

open Finset

variable {ι : Type*} [DecidableEq ι] {F : Type*} [CommRing F]

/-! ## Multilinear coefficients -/

/-- The multilinear coefficient of `t` at the monomial `∏ i ∈ S, x i`, obtained by Möbius
inversion over the subsets of `S`. -/
def coef (t : Finset ι → F) (S : Finset ι) : F :=
  ∑ y ∈ S.powerset, (-1 : F) ^ (S.card - y.card) * t y

/-- The monomial `∏ i ∈ T, x i`, as a function on the cube. -/
def mono (T : Finset ι) : Finset ι → F := fun x => if T ⊆ x then 1 else 0

theorem sum_alt' (U : Finset ι) :
    ∑ y ∈ U.powerset, (-1 : F) ^ y.card = if U = ∅ then 1 else 0 := by
  have h0 := Finset.sum_powerset_neg_one_pow_card (x := U)
  have h1 : ((∑ m ∈ U.powerset, (-1 : ℤ) ^ m.card : ℤ) : F)
      = ((if U = ∅ then 1 else 0 : ℤ) : F) := by rw [h0]
  push_cast at h1
  exact h1

theorem sum_alt (U : Finset ι) :
    ∑ y ∈ U.powerset, (-1 : F) ^ (U.card - y.card) = if U = ∅ then 1 else 0 := by
  have h2 : ∑ y ∈ U.powerset, (-1 : F) ^ (U.card - y.card)
      = (-1 : F) ^ U.card * ∑ y ∈ U.powerset, (-1 : F) ^ y.card := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [Finset.mem_powerset] at hy
    have h : y.card ≤ U.card := Finset.card_le_card hy
    rw [← pow_add, show U.card + y.card = (U.card - y.card) + 2 * y.card by omega, pow_add,
      pow_mul]
    simp
  rw [h2, sum_alt']
  by_cases hU : U = ∅ <;> simp [hU]

theorem sum_powerset_filter_superset {M : Type*} [AddCommMonoid M] {T S : Finset ι} (hTS : T ⊆ S)
    (f : Finset ι → M) :
    ∑ y ∈ S.powerset.filter (fun y => T ⊆ y), f y = ∑ w ∈ (S \ T).powerset, f (w ∪ T) := by
  refine Finset.sum_nbij' (i := fun y => y \ T) (j := fun w => w ∪ T) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_powerset] at ha ⊢
    exact Finset.sdiff_subset_sdiff ha.1 (le_refl T)
  · intro w hw
    simp only [Finset.mem_powerset, Finset.mem_filter] at hw ⊢
    exact ⟨Finset.union_subset (hw.trans Finset.sdiff_subset) hTS, Finset.subset_union_right⟩
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_powerset] at ha
    exact Finset.sdiff_union_of_subset ha.2
  · intro w hw
    simp only [Finset.mem_powerset] at hw
    have : Disjoint w T := Finset.disjoint_of_subset_left hw Finset.sdiff_disjoint
    simp [Finset.union_sdiff_cancel_right this]
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_powerset] at ha
    rw [Finset.sdiff_union_of_subset ha.2]

/-- The alternating sum over the interval `[T, S]` of the subset lattice. -/
theorem alt_sum_interval (T S : Finset ι) :
    ∑ y ∈ S.powerset.filter (fun y => T ⊆ y), (-1 : F) ^ (S.card - y.card)
      = if S = T then 1 else 0 := by
  by_cases hTS : T ⊆ S
  · rw [sum_powerset_filter_superset hTS]
    have hcard : ∀ w ∈ (S \ T).powerset, (-1 : F) ^ (S.card - (w ∪ T).card)
        = (-1 : F) ^ ((S \ T).card - w.card) := by
      intro w hw
      rw [Finset.mem_powerset] at hw
      have hd : Disjoint w T := Finset.disjoint_of_subset_left hw Finset.sdiff_disjoint
      have h1 : (w ∪ T).card = w.card + T.card := Finset.card_union_of_disjoint hd
      have h2 : (S \ T).card + T.card = S.card := Finset.card_sdiff_add_card_eq_card hTS
      have h4 : w.card ≤ (S \ T).card := Finset.card_le_card hw
      rw [h1]
      congr 1
      omega
    rw [Finset.sum_congr rfl hcard, sum_alt]
    by_cases h : S = T
    · simp [h]
    · have hne : S \ T ≠ ∅ := fun hc =>
        h (Finset.Subset.antisymm (Finset.sdiff_eq_empty_iff_subset.mp hc) hTS)
      simp [hne, h]
  · have h1 : S.powerset.filter (fun y => T ⊆ y) = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr fun y hy hc => hTS ?_
      rw [Finset.mem_powerset] at hy
      exact hc.trans hy
    have h2 : S ≠ T := fun hc => hTS (hc ▸ Finset.Subset.refl T)
    simp [h1, h2]

/-- The alternating sum over the interval `[T, S]`, with the sign attached to the lower end. -/
theorem alt_sum_interval' (T S : Finset ι) :
    ∑ y ∈ S.powerset.filter (fun y => T ⊆ y), (-1 : F) ^ (y.card - T.card)
      = if S = T then 1 else 0 := by
  by_cases hTS : T ⊆ S
  · rw [sum_powerset_filter_superset hTS]
    have hcard : ∀ w ∈ (S \ T).powerset, (-1 : F) ^ ((w ∪ T).card - T.card)
        = (-1 : F) ^ w.card := by
      intro w hw
      rw [Finset.mem_powerset] at hw
      have hd : Disjoint w T := Finset.disjoint_of_subset_left hw Finset.sdiff_disjoint
      have h1 : (w ∪ T).card = w.card + T.card := Finset.card_union_of_disjoint hd
      rw [h1]
      congr 1
      omega
    rw [Finset.sum_congr rfl hcard, sum_alt']
    by_cases h : S = T
    · simp [h]
    · have hne : S \ T ≠ ∅ := fun hc =>
        h (Finset.Subset.antisymm (Finset.sdiff_eq_empty_iff_subset.mp hc) hTS)
      simp [hne, h]
  · have h1 : S.powerset.filter (fun y => T ⊆ y) = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr fun y hy hc => hTS ?_
      rw [Finset.mem_powerset] at hy
      exact hc.trans hy
    have h2 : S ≠ T := fun hc => hTS (hc ▸ Finset.Subset.refl T)
    simp [h1, h2]

theorem coef_mono (T S : Finset ι) : coef (mono T : Finset ι → F) S = if S = T then 1 else 0 := by
  unfold coef mono
  rw [← alt_sum_interval (F := F) T S, Finset.sum_filter]
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases h : T ⊆ y <;> simp [h]

/-! ### Linearity -/

omit [DecidableEq ι] in
@[simp] theorem coef_zero (S : Finset ι) : coef (fun _ => (0 : F)) S = 0 := by
  simp [coef]

omit [DecidableEq ι] in
theorem coef_add (f g : Finset ι → F) (S : Finset ι) :
    coef (fun x => f x + g x) S = coef f S + coef g S := by
  simp only [coef, mul_add, Finset.sum_add_distrib]

omit [DecidableEq ι] in
theorem coef_neg (f : Finset ι → F) (S : Finset ι) :
    coef (fun x => -f x) S = -coef f S := by
  simp only [coef, mul_neg, Finset.sum_neg_distrib]

omit [DecidableEq ι] in
theorem coef_sub (f g : Finset ι → F) (S : Finset ι) :
    coef (fun x => f x - g x) S = coef f S - coef g S := by
  simp only [sub_eq_add_neg, coef_add, coef_neg]

omit [DecidableEq ι] in
theorem coef_const_mul (c : F) (f : Finset ι → F) (S : Finset ι) :
    coef (fun x => c * f x) S = c * coef f S := by
  simp only [coef, Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => by ring

omit [DecidableEq ι] in
theorem coef_sum {κ : Type*} (s : Finset κ) (f : κ → Finset ι → F) (S : Finset ι) :
    coef (fun x => ∑ k ∈ s, f k x) S = ∑ k ∈ s, coef (f k) S := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      rw [coef_add, ih]

omit [DecidableEq ι] in
theorem coef_congr {f g : Finset ι → F} (h : ∀ x, f x = g x) (S : Finset ι) :
    coef f S = coef g S := by
  unfold coef; exact Finset.sum_congr rfl fun y _ => by rw [h]

/-! ### Möbius inversion -/

theorem coef_inversion (t : Finset ι → F) (x : Finset ι) :
    t x = ∑ S ∈ x.powerset, coef t S := by
  have step : ∀ S ∈ x.powerset, coef t S
      = ∑ y ∈ x.powerset, if y ⊆ S then (-1 : F) ^ (S.card - y.card) * t y else 0 := by
    intro S hS
    rw [Finset.mem_powerset] at hS
    rw [coef, ← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext y
    simp only [Finset.mem_powerset, Finset.mem_filter]
    exact ⟨fun h => ⟨h.trans hS, h⟩, fun h => h.2⟩
  rw [Finset.sum_congr rfl step, Finset.sum_comm]
  have inner : ∀ y ∈ x.powerset,
      (∑ S ∈ x.powerset, if y ⊆ S then (-1 : F) ^ (S.card - y.card) * t y else 0)
        = if x = y then t y else 0 := by
    intro y _
    rw [← Finset.sum_filter]
    have : ∑ S ∈ x.powerset.filter (fun S => y ⊆ S), (-1 : F) ^ (S.card - y.card) * t y
        = (∑ S ∈ x.powerset.filter (fun S => y ⊆ S), (-1 : F) ^ (S.card - y.card)) * t y := by
      rw [Finset.sum_mul]
    rw [this, alt_sum_interval']
    by_cases h : x = y <;> simp [h]
  rw [Finset.sum_congr rfl inner]
  simp

/-! ### The product rule -/

theorem coef_mul (f g : Finset ι → F) (S : Finset ι) :
    coef (fun x => f x * g x) S
      = ∑ U ∈ S.powerset, ∑ V ∈ S.powerset, if U ∪ V = S then coef f U * coef g V else 0 := by
  have expand : ∀ y ∈ S.powerset, (-1 : F) ^ (S.card - y.card) * (f y * g y)
      = ∑ U ∈ S.powerset, ∑ V ∈ S.powerset,
          (if U ⊆ y then (1 : F) else 0) * (if V ⊆ y then (1 : F) else 0) *
            ((-1 : F) ^ (S.card - y.card) * (coef f U * coef g V)) := by
    intro y hy
    rw [Finset.mem_powerset] at hy
    have hf : f y = ∑ U ∈ S.powerset, (if U ⊆ y then (1 : F) else 0) * coef f U := by
      have e1 : ∀ U ∈ S.powerset, (if U ⊆ y then (1 : F) else 0) * coef f U
          = if U ⊆ y then coef f U else 0 := by
        intro U _; by_cases h : U ⊆ y <;> simp [h]
      rw [Finset.sum_congr rfl e1, ← Finset.sum_filter, coef_inversion f y]
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext U
      simp only [Finset.mem_powerset, Finset.mem_filter]
      exact ⟨fun h => ⟨h.trans hy, h⟩, fun h => h.2⟩
    have hg : g y = ∑ V ∈ S.powerset, (if V ⊆ y then (1 : F) else 0) * coef g V := by
      have e1 : ∀ V ∈ S.powerset, (if V ⊆ y then (1 : F) else 0) * coef g V
          = if V ⊆ y then coef g V else 0 := by
        intro V _; by_cases h : V ⊆ y <;> simp [h]
      rw [Finset.sum_congr rfl e1, ← Finset.sum_filter, coef_inversion g y]
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext V
      simp only [Finset.mem_powerset, Finset.mem_filter]
      exact ⟨fun h => ⟨h.trans hy, h⟩, fun h => h.2⟩
    rw [hf, hg, Finset.sum_mul_sum]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun U _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun V _ => ?_
    ring
  rw [coef, Finset.sum_congr rfl expand, Finset.sum_comm]
  refine Finset.sum_congr rfl fun U _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun V _ => ?_
  have key : ∀ y ∈ S.powerset,
      (if U ⊆ y then (1 : F) else 0) * (if V ⊆ y then (1 : F) else 0) *
        ((-1 : F) ^ (S.card - y.card) * (coef f U * coef g V))
      = (if U ∪ V ⊆ y then (-1 : F) ^ (S.card - y.card) else 0) * (coef f U * coef g V) := by
    intro y _
    by_cases hU : U ⊆ y <;> by_cases hV : V ⊆ y <;>
      simp [hU, hV, Finset.union_subset_iff]
  rw [Finset.sum_congr rfl key, ← Finset.sum_mul, ← Finset.sum_filter,
    alt_sum_interval (U ∪ V) S]
  by_cases h : U ∪ V = S
  · simp [h]
  · have hne : S ≠ U ∪ V := fun hc => h hc.symm
    simp [hne, h]

/-! ## Support and degree -/

/-- `SuppIn t P`: the multilinear polynomial of `t` only involves variables from `P`. -/
def SuppIn (t : Finset ι → F) (P : Finset ι) : Prop := ∀ S, ¬ S ⊆ P → coef t S = 0

/-- `DegLE t d`: the multilinear polynomial of `t` has degree at most `d`. -/
def DegLE (t : Finset ι → F) (d : ℕ) : Prop := ∀ S, d < S.card → coef t S = 0

/-- `t` only depends on the coordinates in `P`. -/
def DependsOn (t : Finset ι → F) (P : Finset ι) : Prop := ∀ x y, x ∩ P = y ∩ P → t x = t y

theorem suppIn_of_dependsOn {t : Finset ι → F} {P : Finset ι} (h : DependsOn t P) :
    SuppIn t P := by
  intro S hS
  obtain ⟨i, hiS, hiP⟩ : ∃ i, i ∈ S ∧ i ∉ P := by
    by_contra hc
    push_neg at hc
    exact hS fun i hi => hc i hi
  have hS' : S = insert i (S.erase i) := (Finset.insert_erase hiS).symm
  have key : coef t S = ∑ y ∈ (S.erase i).powerset,
      ((-1 : F) ^ (S.card - y.card) * t y + (-1 : F) ^ (S.card - (insert i y).card) * t (insert i y))
      := by
    rw [coef]
    nth_rewrite 1 [hS']
    rw [Finset.sum_powerset_insert (Finset.notMem_erase i S), ← Finset.sum_add_distrib]
  rw [key]
  refine Finset.sum_eq_zero fun y hy => ?_
  rw [Finset.mem_powerset] at hy
  have hiy : i ∉ y := fun hc => (Finset.notMem_erase i S) (hy hc)
  have hcard : (insert i y).card = y.card + 1 := by
    rw [Finset.card_insert_of_notMem hiy]
  have hyS : y ⊆ S := hy.trans (Finset.erase_subset i S)
  have hle : y.card < S.card := by
    have h1 : y.card ≤ (S.erase i).card := Finset.card_le_card hy
    have h2 : (S.erase i).card = S.card - 1 := Finset.card_erase_of_mem hiS
    have h3 : 1 ≤ S.card := Finset.card_pos.mpr ⟨i, hiS⟩
    omega
  have hteq : t (insert i y) = t y := by
    refine h _ _ ?_
    ext j
    simp only [Finset.mem_inter, Finset.mem_insert]
    constructor
    · rintro ⟨rfl | hj, hjP⟩
      · exact absurd hjP hiP
      · exact ⟨hj, hjP⟩
    · rintro ⟨hj, hjP⟩
      exact ⟨Or.inr hj, hjP⟩
  rw [hteq, hcard]
  have : S.card - y.card = (S.card - (y.card + 1)) + 1 := by omega
  rw [this, pow_succ]
  ring

theorem coef_mul_suppIn {f g : Finset ι → F} {P Q : Finset ι}
    (hf : SuppIn f P) (hg : SuppIn g Q) : SuppIn (fun x => f x * g x) (P ∪ Q) := by
  intro S hS
  rw [coef_mul]
  refine Finset.sum_eq_zero fun U _ => Finset.sum_eq_zero fun V _ => ?_
  by_cases h : U ∪ V = S
  · rw [if_pos h]
    by_cases hU : U ⊆ P
    · by_cases hV : V ⊆ Q
      · exact absurd (h ▸ Finset.union_subset_union hU hV) hS
      · rw [hg V hV, mul_zero]
    · rw [hf U hU, zero_mul]
  · rw [if_neg h]

theorem coef_mul_degLE {f g : Finset ι → F} {p q : ℕ}
    (hf : DegLE f p) (hg : DegLE g q) : DegLE (fun x => f x * g x) (p + q) := by
  intro S hS
  rw [coef_mul]
  refine Finset.sum_eq_zero fun U hU => Finset.sum_eq_zero fun V hV => ?_
  by_cases h : U ∪ V = S
  · rw [if_pos h]
    have hcard : S.card ≤ U.card + V.card := by
      calc S.card = (U ∪ V).card := by rw [h]
        _ ≤ U.card + V.card := Finset.card_union_le U V
    by_cases hUp : p < U.card
    · rw [hf U hUp, zero_mul]
    · have : q < V.card := by omega
      rw [hg V this, mul_zero]
  · rw [if_neg h]

/-- Two decompositions of the same set along two disjoint blocks agree. -/
theorem block_pair_eq {P Q S T U V : Finset ι} (hPQ : Disjoint P Q)
    (hS : S ⊆ P) (hT : T ⊆ Q) (hUP : U ⊆ P) (hVQ : V ⊆ Q) (h : U ∪ V = S ∪ T) :
    U = S ∧ V = T := by
  have hdisj : ∀ {j : ι}, j ∈ P → j ∉ Q := fun hj => Finset.disjoint_left.mp hPQ hj
  have key : ∀ U V : Finset ι, U ∪ V = S ∪ T → U ⊆ P → V ⊆ Q → U = S ∧ V = T := by
    intro U V h hUP hVQ
    have hUS : U = S := by
      refine Finset.Subset.antisymm (fun j hj => ?_) (fun j hj => ?_)
      · have hj2 : j ∈ S ∪ T := by rw [← h]; exact Finset.mem_union_left V hj
        rcases Finset.mem_union.mp hj2 with hjS | hjT
        · exact hjS
        · exact absurd (hT hjT) (hdisj (hUP hj))
      · have hj2 : j ∈ U ∪ V := by rw [h]; exact Finset.mem_union_left T hj
        rcases Finset.mem_union.mp hj2 with hjU | hjV
        · exact hjU
        · exact absurd (hVQ hjV) (hdisj (hS hj))
    have hVT : V = T := by
      refine Finset.Subset.antisymm (fun j hj => ?_) (fun j hj => ?_)
      · have hj2 : j ∈ S ∪ T := by rw [← h]; exact Finset.mem_union_right U hj
        rcases Finset.mem_union.mp hj2 with hjS | hjT
        · exact absurd (hVQ hj) (hdisj (hS hjS))
        · exact hjT
      · have hj2 : j ∈ U ∪ V := by rw [h]; exact Finset.mem_union_right S hj
        rcases Finset.mem_union.mp hj2 with hjU | hjV
        · exact absurd (hT hj) (hdisj (hUP hjU))
        · exact hjV
    exact ⟨hUS, hVT⟩
  exact key U V h hUP hVQ

/-- On disjoint blocks the coefficients of a product factor. -/
theorem coef_mul_disjoint {f g : Finset ι → F} {P Q S T : Finset ι}
    (hf : SuppIn f P) (hg : SuppIn g Q) (hPQ : Disjoint P Q) (hS : S ⊆ P) (hT : T ⊆ Q) :
    coef (fun x => f x * g x) (S ∪ T) = coef f S * coef g T := by
  have key : ∀ U V : Finset ι, U ∪ V = S ∪ T → U ⊆ P → V ⊆ Q → U = S ∧ V = T :=
    fun U V h hUP hVQ => block_pair_eq hPQ hS hT hUP hVQ h
  rw [coef_mul]
  have hSmem : S ∈ (S ∪ T).powerset := Finset.mem_powerset.mpr Finset.subset_union_left
  have hTmem : T ∈ (S ∪ T).powerset := Finset.mem_powerset.mpr Finset.subset_union_right
  rw [Finset.sum_eq_single S]
  · rw [Finset.sum_eq_single T]
    · rw [if_pos rfl]
    · intro V _ hVT
      by_cases h : S ∪ V = S ∪ T
      · rw [if_pos h]
        by_cases hVQ : V ⊆ Q
        · exact absurd ((key S V h hS hVQ).2) hVT
        · rw [hg V hVQ, mul_zero]
      · rw [if_neg h]
    · intro h; exact absurd hTmem h
  · intro U _ hUS
    refine Finset.sum_eq_zero fun V _ => ?_
    by_cases h : U ∪ V = S ∪ T
    · rw [if_pos h]
      by_cases hUP : U ⊆ P
      · by_cases hVQ : V ⊆ Q
        · exact absurd ((key U V h hUP hVQ).1) hUS
        · rw [hg V hVQ, mul_zero]
      · rw [hf U hUP, zero_mul]
    · rw [if_neg h]
  · intro h; exact absurd hSmem h

/-- If only one pair `(U₀, V₀)` contributes to the product rule, the product rule collapses. -/
theorem coef_mul_eq_of_unique {f g : Finset ι → F} {S U0 V0 : Finset ι}
    (hU0 : U0 ⊆ S) (hV0 : V0 ⊆ S) (hunion : U0 ∪ V0 = S)
    (huniq : ∀ U V : Finset ι, U ⊆ S → V ⊆ S → U ∪ V = S → (U ≠ U0 ∨ V ≠ V0) →
      coef f U * coef g V = 0) :
    coef (fun x => f x * g x) S = coef f U0 * coef g V0 := by
  rw [coef_mul, Finset.sum_eq_single U0]
  · rw [Finset.sum_eq_single V0]
    · rw [if_pos hunion]
    · intro V hV hne
      by_cases h : U0 ∪ V = S
      · rw [if_pos h, huniq U0 V hU0 (Finset.mem_powerset.mp hV) h (Or.inr hne)]
      · rw [if_neg h]
    · intro h; exact absurd (Finset.mem_powerset.mpr hV0) h
  · intro U hU hne
    refine Finset.sum_eq_zero fun V hV => ?_
    by_cases h : U ∪ V = S
    · rw [if_pos h, huniq U V (Finset.mem_powerset.mp hU) (Finset.mem_powerset.mp hV) h (Or.inl hne)]
    · rw [if_neg h]
  · intro h; exact absurd (Finset.mem_powerset.mpr hU0) h

/-- If exactly the two pairs `(U₀, V₀)` and `(V₀, U₀)` contribute to the product rule. -/
theorem coef_mul_eq_of_pair {f g : Finset ι → F} {S U0 V0 : Finset ι}
    (hU0 : U0 ⊆ S) (hV0 : V0 ⊆ S) (hne : U0 ≠ V0) (hunion : U0 ∪ V0 = S)
    (huniq : ∀ U V : Finset ι, U ⊆ S → V ⊆ S → U ∪ V = S →
        ¬ ((U = U0 ∧ V = V0) ∨ (U = V0 ∧ V = U0)) → coef f U * coef g V = 0) :
    coef (fun x => f x * g x) S = coef f U0 * coef g V0 + coef f V0 * coef g U0 := by
  rw [coef_mul]
  have hsub : ({U0, V0} : Finset (Finset ι)) ⊆ S.powerset := by
    intro U hU
    rcases Finset.mem_insert.mp hU with rfl | hU
    · exact Finset.mem_powerset.mpr hU0
    · rw [Finset.mem_singleton] at hU
      exact hU ▸ Finset.mem_powerset.mpr hV0
  rw [← Finset.sum_subset hsub, Finset.sum_pair hne]
  · congr 1
    · rw [Finset.sum_eq_single V0]
      · rw [if_pos hunion]
      · intro V hV hVne
        by_cases h : U0 ∪ V = S
        · rw [if_pos h]
          refine huniq U0 V hU0 (Finset.mem_powerset.mp hV) h ?_
          rintro (⟨-, h2⟩ | ⟨h1, -⟩)
          · exact hVne h2
          · exact hne h1
        · rw [if_neg h]
      · intro h; exact absurd (Finset.mem_powerset.mpr hV0) h
    · rw [Finset.sum_eq_single U0]
      · rw [if_pos (by rw [Finset.union_comm]; exact hunion)]
      · intro V hV hVne
        by_cases h : V0 ∪ V = S
        · rw [if_pos h]
          refine huniq V0 V hV0 (Finset.mem_powerset.mp hV) h ?_
          rintro (⟨h1, -⟩ | ⟨-, h2⟩)
          · exact hne h1.symm
          · exact hVne h2
        · rw [if_neg h]
      · intro h; exact absurd (Finset.mem_powerset.mpr hU0) h
  · intro U hU hUmem
    have hU1 : U ≠ U0 := fun hc => hUmem (by rw [hc]; exact Finset.mem_insert_self _ _)
    have hU2 : U ≠ V0 := fun hc => hUmem (by rw [hc]; simp)
    refine Finset.sum_eq_zero fun V hV => ?_
    by_cases h : U ∪ V = S
    · rw [if_pos h]
      refine huniq U V (Finset.mem_powerset.mp hU) (Finset.mem_powerset.mp hV) h ?_
      rintro (⟨h1, -⟩ | ⟨h1, -⟩)
      · exact hU1 h1
      · exact hU2 h1
    · rw [if_neg h]

/-- If no pair contributes to the product rule, the coefficient vanishes. -/
theorem coef_mul_eq_zero {f g : Finset ι → F} {S : Finset ι}
    (h : ∀ U V : Finset ι, U ⊆ S → V ⊆ S → U ∪ V = S → coef f U * coef g V = 0) :
    coef (fun x => f x * g x) S = 0 := by
  rw [coef_mul]
  refine Finset.sum_eq_zero fun U hU => Finset.sum_eq_zero fun V hV => ?_
  by_cases hUV : U ∪ V = S
  · rw [if_pos hUV, h U V (Finset.mem_powerset.mp hU) (Finset.mem_powerset.mp hV) hUV]
  · rw [if_neg hUV]

/-- A function whose multilinear polynomial lives on `P` only depends on the coordinates
in `P`. -/
theorem dependsOn_of_suppIn {t : Finset ι → F} {P : Finset ι} (h : SuppIn t P) :
    DependsOn t P := by
  have key : ∀ x : Finset ι, t x = ∑ S ∈ (x ∩ P).powerset, coef t S := by
    intro x
    rw [coef_inversion t x]
    have hsplit : ∑ S ∈ x.powerset, coef t S
        = ∑ S ∈ x.powerset.filter (fun S => S ⊆ P), coef t S := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun S _ => ?_
      by_cases hc : S ⊆ P
      · rw [if_pos hc]
      · rw [if_neg hc, h S hc]
    rw [hsplit]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext S
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_inter_iff]
  intro x y hxy
  rw [key x, key y, hxy]

/-! ## Affine forms -/

/-- An affine form in the cube variables. -/
structure Aff (ι : Type*) (F : Type*) where
  const : F
  coeff : ι → F

/-- Evaluation of an affine form at a cube point. -/
def Aff.ev (A : Aff ι F) (x : Finset ι) : F := A.const + ∑ i ∈ x, A.coeff i

/-- A function on the cube is affine if it is given by an affine form. -/
def IsAffineOn (t : Finset ι → F) : Prop := ∃ A : Aff ι F, ∀ x, t x = A.ev x

omit [DecidableEq ι] in
theorem coef_aff_empty (A : Aff ι F) : coef A.ev ∅ = A.const := by
  simp [coef, Aff.ev]

theorem coef_aff_single (A : Aff ι F) (i : ι) : coef A.ev {i} = A.coeff i := by
  have h : ({i} : Finset ι) = insert i ∅ := rfl
  rw [coef, h, Finset.sum_powerset_insert (by simp)]
  simp [Aff.ev]

/-- An affine form has no multilinear coefficient in degree `≥ 2`. -/
theorem coef_aff_eq_zero_of_two_le (A : Aff ι F) {S : Finset ι} (hS : 2 ≤ S.card) :
    coef A.ev S = 0 := by
  have hne : S ≠ ∅ := by
    intro hc; rw [hc] at hS; simp at hS
  have expand : coef A.ev S
      = A.const * (∑ y ∈ S.powerset, (-1 : F) ^ (S.card - y.card))
        + ∑ i ∈ S, A.coeff i *
            (∑ y ∈ S.powerset.filter (fun y => {i} ⊆ y), (-1 : F) ^ (S.card - y.card)) := by
    rw [coef, Finset.mul_sum]
    have step : ∀ y ∈ S.powerset, (-1 : F) ^ (S.card - y.card) * A.ev y
        = (-1 : F) ^ (S.card - y.card) * A.const
          + ∑ i ∈ S, (if i ∈ y then (-1 : F) ^ (S.card - y.card) * A.coeff i else 0) := by
      intro y hy
      rw [Finset.mem_powerset] at hy
      rw [Aff.ev, mul_add, ← Finset.sum_filter]
      congr 1
      rw [Finset.mul_sum]
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext j
      simp only [Finset.mem_filter]
      exact ⟨fun h => ⟨hy h, h⟩, fun h => h.2⟩
    rw [Finset.sum_congr rfl step, Finset.sum_add_distrib]
    congr 1
    · exact Finset.sum_congr rfl fun y _ => by ring
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_congr ?_ fun y _ => by ring
    ext y
    simp only [Finset.mem_filter, Finset.singleton_subset_iff]
  rw [expand, sum_alt, if_neg hne, mul_zero, zero_add]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [alt_sum_interval]
  have : S ≠ {i} := by
    intro hc
    rw [hc] at hS
    simp at hS
  rw [if_neg this, mul_zero]

theorem degLE_aff (A : Aff ι F) : DegLE A.ev 1 :=
  fun _ hS => coef_aff_eq_zero_of_two_le A (by omega)

theorem degLE_one_of_isAffineOn {t : Finset ι → F} (h : IsAffineOn t) : DegLE t 1 := by
  obtain ⟨A, hA⟩ := h
  intro S hS
  rw [coef_congr hA S]
  exact degLE_aff A S hS

theorem isAffineOn_of_degLE_one {t : Finset ι → F} (h : DegLE t 1) : IsAffineOn t := by
  refine ⟨⟨coef t ∅, fun i => coef t {i}⟩, fun x => ?_⟩
  rw [coef_inversion t x, Aff.ev]
  have hsplit : ∑ S ∈ x.powerset, coef t S
      = ∑ S ∈ x.powerset.filter (fun S => S.card ≤ 1), coef t S := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun S _ => ?_
    by_cases hc : S.card ≤ 1
    · rw [if_pos hc]
    · have hlt : 1 < S.card := by omega
      rw [if_neg hc, h S hlt]
  rw [hsplit]
  have hset : x.powerset.filter (fun S => S.card ≤ 1) = insert ∅ (x.image (fun i => ({i} : Finset ι))) := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_insert, Finset.mem_image]
    constructor
    · rintro ⟨hSx, hcard⟩
      rcases Nat.lt_or_ge S.card 1 with hc | hc
      · left
        exact Finset.card_eq_zero.mp (by omega)
      · right
        have hcard1 : S.card = 1 := by omega
        obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hcard1
        subst hi
        exact ⟨i, Finset.singleton_subset_iff.mp hSx, rfl⟩
    · rintro (h1 | h2)
      · subst h1; exact ⟨Finset.empty_subset x, by simp⟩
      · obtain ⟨i, hi, hiS⟩ := h2
        subst hiS
        exact ⟨Finset.singleton_subset_iff.mpr hi, by simp⟩
  rw [hset, Finset.sum_insert, Finset.sum_image]
  · intro i _ j _ hij
    exact Finset.singleton_injective hij
  · simp only [Finset.mem_image]
    rintro ⟨i, _, hi⟩
    exact absurd hi (Finset.singleton_ne_empty i)

/-- Multiplying a block function by an affine form: the coefficient at `insert j S`, for a
variable `j` outside the block and `S` inside it, picks out the coefficient of `j`. -/
theorem coef_aff_mul_insert (A : Aff ι F) {h : Finset ι → F} {P S : Finset ι} {j : ι}
    (hh : SuppIn h P) (hS : S ⊆ P) (hj : j ∉ P) :
    coef (fun x => A.ev x * h x) (insert j S) = A.coeff j * coef h S := by
  have hjS : j ∉ S := fun hc => hj (hS hc)
  have hsub1 : ({j} : Finset ι) ⊆ insert j S := by
    simp [Finset.singleton_subset_iff]
  have hsub2 : S ⊆ insert j S := Finset.subset_insert j S
  have hunion : ({j} : Finset ι) ∪ S = insert j S := by
    ext k; simp [Finset.mem_insert]
  rw [coef_mul_eq_of_unique hsub1 hsub2 hunion, coef_aff_single]
  intro U V hU hV hUV hne
  by_cases hUcard : 2 ≤ U.card
  · rw [coef_aff_eq_zero_of_two_le A hUcard, zero_mul]
  by_cases hVP : V ⊆ P
  · exfalso
    have hjV : j ∉ V := fun hc => hj (hVP hc)
    have hjU : j ∈ U := by
      have : j ∈ U ∪ V := by rw [hUV]; exact Finset.mem_insert_self j S
      rcases Finset.mem_union.mp this with h1 | h1
      · exact h1
      · exact absurd h1 hjV
    have hUj : U = {j} := by
      refine Finset.eq_singleton_iff_unique_mem.mpr ⟨hjU, fun k hk => ?_⟩
      by_contra hkj
      have : 2 ≤ U.card := by
        have hsub : ({j, k} : Finset ι) ⊆ U := by
          intro m hm
          rcases Finset.mem_insert.mp hm with rfl | hm
          · exact hjU
          · rw [Finset.mem_singleton] at hm; exact hm ▸ hk
        have hcard : ({j, k} : Finset ι).card = 2 := by
          rw [Finset.card_insert_of_notMem (by simp [Ne.symm hkj]), Finset.card_singleton]
        exact hcard ▸ Finset.card_le_card hsub
      exact hUcard this
    have hVS : V = S := by
      refine Finset.Subset.antisymm (fun k hk => ?_) (fun k hk => ?_)
      · have hkins : k ∈ insert j S := hUV ▸ Finset.mem_union_right U hk
        rcases Finset.mem_insert.mp hkins with rfl | hk'
        · exact absurd hk hjV
        · exact hk'
      · have hkins : k ∈ U ∪ V := by
          rw [hUV]; exact Finset.mem_insert_of_mem hk
        rcases Finset.mem_union.mp hkins with hk' | hk'
        · rw [hUj, Finset.mem_singleton] at hk'
          exact absurd (hk' ▸ hk) hjS
        · exact hk'
    rcases hne with hne | hne
    · exact hne hUj
    · exact hne hVS
  · rw [hh V hVP, mul_zero]

/-- Multiplying a block function by an affine form: coefficients straddling two disjoint
blocks vanish. -/
theorem coef_aff_mul_block_eq_zero (A : Aff ι F) {h : Finset ι → F} {P Q S T : Finset ι}
    (hh : SuppIn h Q) (hPQ : Disjoint P Q) (hS : S ⊆ P) (hScard : 2 ≤ S.card) (hST : S ⊆ T) :
    coef (fun x => A.ev x * h x) T = 0 := by
  refine coef_mul_eq_zero fun U V hU hV hUV => ?_
  by_cases hUcard : 2 ≤ U.card
  · rw [coef_aff_eq_zero_of_two_le A hUcard, zero_mul]
  by_cases hVQ : V ⊆ Q
  · exfalso
    have hSU : ¬ S ⊆ U := by
      intro hc
      have : S.card ≤ U.card := Finset.card_le_card hc
      omega
    obtain ⟨k, hkS, hkU⟩ : ∃ k, k ∈ S ∧ k ∉ U := by
      by_contra hcon
      push_neg at hcon
      exact hSU fun k hk => hcon k hk
    have hkins : k ∈ U ∪ V := hUV ▸ hST hkS
    rcases Finset.mem_union.mp hkins with hk | hk
    · exact hkU hk
    · exact Finset.disjoint_left.mp hPQ (hS hkS) (hVQ hk)
  · rw [hh V hVQ, mul_zero]

/-- The degree-two coefficients of a product of two affine forms. -/
theorem coef_aff_mul_aff_pair (A B : Aff ι F) {i j : ι} (hij : i ≠ j) :
    coef (fun x => A.ev x * B.ev x) {i, j}
      = A.coeff i * B.coeff j + A.coeff j * B.coeff i := by
  have hji : j ∉ ({i} : Finset ι) := by simp [Ne.symm hij]
  have hij' : i ∉ ({j} : Finset ι) := by simp [hij]
  have hpair : ({i, j} : Finset ι) = insert i {j} := rfl
  have hcard : ({i, j} : Finset ι).card = 2 := by
    rw [hpair, Finset.card_insert_of_notMem hij', Finset.card_singleton]
  rw [coef, hpair, Finset.sum_powerset_insert hij']
  have hsingle : ∀ G : Finset ι → F, ∑ y ∈ ({j} : Finset ι).powerset, G y = G ∅ + G {j} := by
    intro G
    have : ({j} : Finset ι) = insert j ∅ := rfl
    rw [this, Finset.sum_powerset_insert (by simp)]
    simp
  rw [hsingle, hsingle]
  have ev1 : A.ev ∅ = A.const := by simp [Aff.ev]
  have ev2 : A.ev {j} = A.const + A.coeff j := by simp [Aff.ev]
  have ev3 : A.ev (insert i ∅) = A.const + A.coeff i := by simp [Aff.ev]
  have ev4 : A.ev {i, j} = A.const + A.coeff i + A.coeff j := by
    rw [Aff.ev, hpair, Finset.sum_insert hij']
    simp [add_assoc]
  have bv1 : B.ev ∅ = B.const := by simp [Aff.ev]
  have bv2 : B.ev {j} = B.const + B.coeff j := by simp [Aff.ev]
  have bv3 : B.ev (insert i ∅) = B.const + B.coeff i := by simp [Aff.ev]
  have bv4 : B.ev {i, j} = B.const + B.coeff i + B.coeff j := by
    rw [Aff.ev, hpair, Finset.sum_insert hij']
    simp [add_assoc]
  rw [ev1, ev2, ev3, ev4, bv1, bv2, bv3, bv4, hcard]
  norm_num
  ring

theorem isAffineOn_iff_degLE_one {t : Finset ι → F} : IsAffineOn t ↔ DegLE t 1 :=
  ⟨degLE_one_of_isAffineOn, isAffineOn_of_degLE_one⟩

/-- `t` is non-affine on the cube exactly when it has a nonzero multilinear coefficient in
degree at least two. -/
theorem not_isAffineOn_iff {t : Finset ι → F} :
    ¬ IsAffineOn t ↔ ∃ S : Finset ι, 2 ≤ S.card ∧ coef t S ≠ 0 := by
  rw [isAffineOn_iff_degLE_one, DegLE]
  push_neg
  constructor
  · rintro h
    obtain ⟨S, hS, hne⟩ := h
    exact ⟨S, by omega, hne⟩
  · rintro ⟨S, hS, hne⟩
    exact ⟨S, by omega, hne⟩

end Solution.Research
