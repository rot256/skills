/-
  A single R1CS row over the Boolean cube, and what it means for such a row to *determine*
  (to "pin") a value `z` as a function of the cube variables.

  A row is `A * B = C` where `A`, `B`, `C` are affine forms in the witness.  Here the
  witness consists of the cube variables `x : Finset ι` (a point of `{0,1}^ι`) together
  with the single extra variable `z`, so each of `A`, `B`, `C` has the shape
  `(z-coefficient) * z + (affine form in x)`.

  `Row.Pins R t` says that the row is a correct gadget for the target `t`, allowing a
  *decoy root*: the honest value `z = t x` always satisfies the row (completeness), and
  the row admits no solution other than `t x` and the value of one fixed affine decoy
  `D` (soundness up to a decoy).  Note that `z` may occur quadratically in the row: this
  is exactly the decoy-root situation, and it is covered.

  The two lemmas of this file split the analysis by whether `z` really occurs
  quadratically (`Az * Bz ≠ 0`) or not.
-/
import Solution.Research.Multilinear

namespace Solution.Research

open Finset

variable {ι : Type*} [DecidableEq ι] {F : Type*}

/-! ## Affine algebra -/

section AffAlgebra
variable [CommRing F]

/-- The constant affine form. -/
def Aff.ofConst (c : F) : Aff ι F := ⟨c, fun _ => 0⟩

/-- Sum of affine forms. -/
def Aff.add (A B : Aff ι F) : Aff ι F := ⟨A.const + B.const, fun i => A.coeff i + B.coeff i⟩

/-- Difference of affine forms. -/
def Aff.sub (A B : Aff ι F) : Aff ι F := ⟨A.const - B.const, fun i => A.coeff i - B.coeff i⟩

/-- Scaling of an affine form. -/
def Aff.smul (c : F) (A : Aff ι F) : Aff ι F := ⟨c * A.const, fun i => c * A.coeff i⟩

omit [DecidableEq ι] in
@[simp] theorem Aff.ev_ofConst (c : F) (x : Finset ι) : (Aff.ofConst c : Aff ι F).ev x = c := by
  simp [Aff.ofConst, Aff.ev]

omit [DecidableEq ι] in
@[simp] theorem Aff.ev_add (A B : Aff ι F) (x : Finset ι) :
    (A.add B).ev x = A.ev x + B.ev x := by
  simp [Aff.add, Aff.ev, Finset.sum_add_distrib]; ring

omit [DecidableEq ι] in
@[simp] theorem Aff.ev_sub (A B : Aff ι F) (x : Finset ι) :
    (A.sub B).ev x = A.ev x - B.ev x := by
  simp [Aff.sub, Aff.ev, Finset.sum_sub_distrib]; ring

omit [DecidableEq ι] in
@[simp] theorem Aff.ev_smul (c : F) (A : Aff ι F) (x : Finset ι) :
    (Aff.smul c A).ev x = c * A.ev x := by
  simp only [Aff.smul, Aff.ev, Finset.mul_sum, mul_add]

end AffAlgebra

/-! ## Rows -/

/-- A single R1CS row `A * B = C` over the cube variables `x` and one extra variable `z`,
all three slots being affine in `(x, z)`. -/
structure Row (ι : Type*) (F : Type*) where
  /-- coefficient of `z` in the `A` slot -/
  Az : F
  /-- affine part in `x` of the `A` slot -/
  A0 : Aff ι F
  /-- coefficient of `z` in the `B` slot -/
  Bz : F
  /-- affine part in `x` of the `B` slot -/
  B0 : Aff ι F
  /-- coefficient of `z` in the `C` slot -/
  Cz : F
  /-- affine part in `x` of the `C` slot -/
  C0 : Aff ι F

variable [Field F]

/-- The row is satisfied at the cube point `x` with value `z`. -/
def Row.Sat (R : Row ι F) (x : Finset ι) (z : F) : Prop :=
  (R.Az * z + R.A0.ev x) * (R.Bz * z + R.B0.ev x) = R.Cz * z + R.C0.ev x

/-- `R.Pins t`: the single row `R` determines `z = t x` over the cube, up to an affine
decoy root.  Completeness: the honest value always satisfies the row.  Soundness: the only
solutions are the honest value and (possibly) the value of a fixed affine decoy `D`. -/
def Row.Pins (R : Row ι F) (t : Finset ι → F) : Prop :=
  ∃ D : Aff ι F, (∀ x, R.Sat x (t x)) ∧ ∀ x z, R.Sat x z → z = t x ∨ z = D.ev x

/-- In a field with `2 ≠ 0` no two values can exhaust the whole field. -/
theorem not_forall_mem_pair (h2 : (2 : F) ≠ 0) (p q : F) : ¬ ∀ z : F, z = p ∨ z = q := by
  intro h
  have h01 : (0 : F) ≠ 1 := zero_ne_one
  have h0m : (0 : F) ≠ -1 := fun hc => one_ne_zero (α := F) (by linear_combination hc)
  have h1m : (1 : F) ≠ -1 := fun hc => h2 (by linear_combination hc)
  rcases h 0 with h0 | h0 <;> rcases h 1 with h1 | h1 <;> rcases h (-1) with hm | hm <;>
    first
      | exact h01 (h0.trans h1.symm)
      | exact h0m (h0.trans hm.symm)
      | exact h1m (h1.trans hm.symm)

omit [DecidableEq ι] in
/-- **Quadratic branch.**  If `z` genuinely occurs quadratically in the row, then the
target agrees pointwise with one of two affine forms. -/
theorem Row.two_affine_branches_of_pins {R : Row ι F} {t : Finset ι → F}
    (hP : R.Pins t) (hab : R.Az * R.Bz ≠ 0) (h2 : (2 : F) ≠ 0) :
    ∃ u v : Aff ι F, ∀ x, (t x - u.ev x) * (t x - v.ev x) = 0 := by
  obtain ⟨D, hcomp, hsound⟩ := hP
  -- `s` is the sum of the two roots of the quadratic in `z`
  set s : Aff ι F :=
    Aff.smul (R.Az * R.Bz)⁻¹
      ((Aff.ofConst R.Cz).sub ((Aff.smul R.Az R.B0).add (Aff.smul R.Bz R.A0))) with hs_def
  refine ⟨Aff.smul (2 : F)⁻¹ s, s.sub D, fun x => ?_⟩
  have hsx : R.Az * R.Bz * s.ev x + (R.Az * R.B0.ev x + R.Bz * R.A0.ev x - R.Cz) = 0 := by
    rw [hs_def]
    simp only [Aff.ev_smul, Aff.ev_sub, Aff.ev_add, Aff.ev_ofConst]
    rw [← mul_assoc, mul_inv_cancel₀ hab, one_mul]
    ring
  have hroot : R.Sat x (s.ev x - t x) := by
    have hc := hcomp x
    unfold Row.Sat at hc ⊢
    linear_combination hc + (s.ev x - 2 * t x) * hsx
  rcases hsound x _ hroot with h | h
  · refine mul_eq_zero.mpr (Or.inl ?_)
    simp only [Aff.ev_smul]
    have h2' : 2 * t x = s.ev x := by linear_combination -h
    field_simp
    linear_combination h2'
  · refine mul_eq_zero.mpr (Or.inr ?_)
    simp only [Aff.ev_sub]
    linear_combination -h

omit [DecidableEq ι] in
/-- **Linear branch.**  If `z` occurs only linearly in the row, then the target is
determined by a nonvanishing affine form together with a product of two affine forms:
`L * t = C₀ - A₀ * B₀`. -/
theorem Row.linear_shape_of_pins {R : Row ι F} {t : Finset ι → F}
    (hP : R.Pins t) (hab : R.Az * R.Bz = 0) (h2 : (2 : F) ≠ 0) :
    ∃ L : Aff ι F, (∀ x, L.ev x ≠ 0) ∧
      ∀ x, L.ev x * t x = R.C0.ev x - R.A0.ev x * R.B0.ev x := by
  obtain ⟨D, hcomp, hsound⟩ := hP
  -- in either degenerate case the row reads `L x * z + (A₀ B₀ - C₀) = 0`
  have main : ∀ L : Aff ι F,
      (∀ x z, R.Sat x z ↔ L.ev x * z + (R.A0.ev x * R.B0.ev x - R.C0.ev x) = 0) →
      ∃ L : Aff ι F, (∀ x, L.ev x ≠ 0) ∧
        ∀ x, L.ev x * t x = R.C0.ev x - R.A0.ev x * R.B0.ev x := by
    intro L hL
    refine ⟨L, fun x hx => ?_, fun x => ?_⟩
    · -- a vanishing `L` would make the row hold for every `z`
      have h1 : L.ev x * t x + (R.A0.ev x * R.B0.ev x - R.C0.ev x) = 0 :=
        (hL x (t x)).1 (hcomp x)
      rw [hx, zero_mul, zero_add] at h1
      refine not_forall_mem_pair h2 (t x) (D.ev x) fun z => ?_
      refine hsound x z ((hL x z).2 ?_)
      rw [hx, zero_mul, zero_add, h1]
    · have h1 : L.ev x * t x + (R.A0.ev x * R.B0.ev x - R.C0.ev x) = 0 :=
        (hL x (t x)).1 (hcomp x)
      linear_combination h1
  rcases mul_eq_zero.mp hab with hA | hB
  · refine main ((Aff.smul R.Bz R.A0).sub (Aff.ofConst R.Cz)) fun x z => ?_
    unfold Row.Sat
    simp only [Aff.ev_sub, Aff.ev_smul, Aff.ev_ofConst, hA, zero_mul, zero_add]
    constructor
    · intro h; linear_combination h
    · intro h; linear_combination h
  · refine main ((Aff.smul R.Az R.B0).sub (Aff.ofConst R.Cz)) fun x z => ?_
    unfold Row.Sat
    simp only [Aff.ev_sub, Aff.ev_smul, Aff.ev_ofConst, hB, zero_mul, zero_add]
    constructor
    · intro h; linear_combination h
    · intro h; linear_combination h

omit [DecidableEq ι] in
/-- **Structure of a pinned target, with no disjointness assumption.**  Whatever the row,
either `z` occurs quadratically and the target agrees pointwise with one of two affine
forms (the decoy-root branch), or the row has the linear shape `L * t = C₀ - A₀ * B₀` with
`L` a nowhere-vanishing affine form. -/
theorem Row.pins_dichotomy {R : Row ι F} {t : Finset ι → F} (hP : R.Pins t) (h2 : (2 : F) ≠ 0) :
    (∃ u v : Aff ι F, ∀ x, (t x - u.ev x) * (t x - v.ev x) = 0) ∨
      (∃ L : Aff ι F, (∀ x, L.ev x ≠ 0) ∧
        ∀ x, L.ev x * t x = R.C0.ev x - R.A0.ev x * R.B0.ev x) := by
  by_cases h : R.Az * R.Bz = 0
  · exact Or.inr (Row.linear_shape_of_pins hP h h2)
  · exact Or.inl (Row.two_affine_branches_of_pins hP h h2)

end Solution.Research
