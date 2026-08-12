/-
  # Two witnesses, two rows: the complete analysis

  This file assembles the normal forms of `PairRows.lean`, `Hyperbola.lean` and
  `Parabola.lean` into a single statement: *for any two R1CS rows over two witnesses, the
  set of public inputs accepted is either contained in the root set of a nonzero
  polynomial of degree at most `7`, or has finite complement.*

  The case analysis is on the linear parts `ℓ_{A₁} = (A₁.cy, A₁.cz)` and `ℓ_{B₁}` of the
  two factors of the first row:

  * one of them vanishes — the first row is affine in the witnesses (`caseLinear`);
  * they are independent — after renaming the witnesses the first row is `U V = h(x)`
    (`caseHyperbola`);
  * they are parallel and both nonzero — after renaming the witnesses the first row is
    `U (k U + t(x)) = γ₀ U + γ₁ V + s(x)` with `k ≠ 0` (`caseParabolaSolve`,
    `caseParabolaPure`).

  Renaming the witnesses is an invertible affine substitution with constant linear part
  and translations of degree at most one; `pairSol_sub` says it does not change the
  accepted set.
-/
import Solution.Research.Hyperbola
import Solution.Research.Parabola

namespace Solution.Research

open Polynomial

variable {F : Type*} [Field F]

/-! ## Substitutions putting the first row in normal form -/

/-- The old first witness expressed in the new witnesses. -/
def substY (σ : Subst F) (x U V : F) : F := σ.p₀ * U + σ.p₁ * V + σ.Py.eval x

/-- The old second witness expressed in the new witnesses. -/
def substZ (σ : Subst F) (x U V : F) : F := σ.q₀ * U + σ.q₁ * V + σ.Pz.eval x

theorem PAff.sub_ev_expand (L : PAff F) (σ : Subst F) (x U V : F) :
    (L.sub σ).ev x U V = L.cy * substY σ x U V + L.cz * substZ σ x U V + L.c.eval x := by
  rw [PAff.sub_ev]
  simp only [PAff.ev, substY, substZ]

/-- If the linear parts of two affine forms are independent, the witnesses can be renamed
    so that the two forms become the two witnesses. -/
theorem exists_subst_pair (A B : PAff F) (hA : A.c.natDegree ≤ 1) (hB : B.c.natDegree ≤ 1)
    (hdet : A.cy * B.cz - A.cz * B.cy ≠ 0) :
    ∃ σ : Subst F, σ.det ≠ 0 ∧ σ.Py.natDegree ≤ 1 ∧ σ.Pz.natDegree ≤ 1 ∧
      (∀ x U V : F, (A.sub σ).ev x U V = U) ∧ (∀ x U V : F, (B.sub σ).ev x U V = V) := by
  set D : F := A.cy * B.cz - A.cz * B.cy with hD
  refine ⟨⟨B.cz / D, -A.cz / D, -B.cy / D, A.cy / D,
    Polynomial.C (1 / D) * (Polynomial.C A.cz * B.c - Polynomial.C B.cz * A.c),
    Polynomial.C (1 / D) * (Polynomial.C B.cy * A.c - Polynomial.C A.cy * B.c)⟩,
    ?_, ?_, ?_, ?_, ?_⟩
  · show B.cz / D * (A.cy / D) - -A.cz / D * (-B.cy / D) ≠ 0
    have : B.cz / D * (A.cy / D) - -A.cz / D * (-B.cy / D) = 1 / D := by
      field_simp
      ring
    rw [this]
    exact one_div_ne_zero hdet
  · exact deg_C_mul_le (deg_sub_le (deg_C_mul_le hB) (deg_C_mul_le hA))
  · exact deg_C_mul_le (deg_sub_le (deg_C_mul_le hA) (deg_C_mul_le hB))
  · intro x U V
    rw [PAff.sub_ev_expand]
    simp only [substY, substZ, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_C]
    field_simp
    ring
  · intro x U V
    rw [PAff.sub_ev_expand]
    simp only [substY, substZ, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_C]
    field_simp
    ring

/-- If the linear part of an affine form is nonzero, the witnesses can be renamed so that
    the form becomes the first witness. -/
theorem exists_subst_single (A : PAff F) (hA : A.c.natDegree ≤ 1) (h : A.cy ≠ 0 ∨ A.cz ≠ 0) :
    ∃ σ : Subst F, σ.det ≠ 0 ∧ σ.Py.natDegree ≤ 1 ∧ σ.Pz.natDegree ≤ 1 ∧
      ∀ x U V : F, A.cy * substY σ x U V + A.cz * substZ σ x U V = U - A.c.eval x := by
  by_cases h0 : A.cy ≠ 0
  · refine ⟨⟨1 / A.cy, -A.cz / A.cy, 0, 1,
      Polynomial.C (-1 / A.cy) * A.c, 0⟩, ?_, ?_, ?_, ?_⟩
    · show 1 / A.cy * 1 - -A.cz / A.cy * 0 ≠ 0
      simpa using one_div_ne_zero h0
    · exact deg_C_mul_le hA
    · simp
    · intro x U V
      simp only [substY, substZ, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_zero]
      field_simp
      ring
  · push_neg at h0
    have h1 : A.cz ≠ 0 := h.resolve_left (by simpa using h0)
    refine ⟨⟨0, 1, 1 / A.cz, -A.cy / A.cz, 0,
      Polynomial.C (-1 / A.cz) * A.c⟩, ?_, ?_, ?_, ?_⟩
    · show (0 : F) * (-A.cy / A.cz) - 1 * (1 / A.cz) ≠ 0
      simpa using one_div_ne_zero h1
    · simp
    · exact deg_C_mul_le hA
    · intro x U V
      simp only [substY, substZ, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_zero]
      field_simp
      ring

/-- Two proportional nonzero linear forms in two variables differ by a nonzero factor. -/
theorem exists_prop_factor (a0 a1 b0 b1 : F) (hA : a0 ≠ 0 ∨ a1 ≠ 0) (hB : b0 ≠ 0 ∨ b1 ≠ 0)
    (hdet : a0 * b1 - a1 * b0 = 0) : ∃ k : F, k ≠ 0 ∧ b0 = k * a0 ∧ b1 = k * a1 := by
  by_cases h0 : a0 ≠ 0
  · refine ⟨b0 / a0, ?_, by field_simp, ?_⟩
    · intro hk
      have hb0 : b0 = 0 := by
        have := div_eq_zero_iff.1 hk
        exact this.resolve_right h0
      have hb1 : b1 = 0 := by
        have : a0 * b1 = 0 := by linear_combination hdet + a1 * hb0
        exact (mul_eq_zero.1 this).resolve_left h0
      exact absurd (Or.elim hB (fun h => absurd hb0 h) fun h => absurd hb1 h) not_false
    · field_simp
      linear_combination -hdet
  · push_neg at h0
    have h1 : a1 ≠ 0 := hA.resolve_left (by simpa using h0)
    have hb0 : b0 = 0 := by
      have : a1 * b0 = 0 := by linear_combination -hdet + b1 * h0
      exact (mul_eq_zero.1 this).resolve_left h1
    have hb1 : b1 ≠ 0 := hB.resolve_left (by simpa using hb0)
    exact ⟨b1 / a1, div_ne_zero hb1 h1, by rw [hb0, h0]; ring, by field_simp⟩

/-! ## Rewriting the first row -/

/-- Replacing the first row by an equivalent condition. -/
theorem pairSol_eq_of_row1 (A₁ B₁ C₁ A₂ B₂ C₂ : PAff F) (P : F → F → F → Prop)
    (h : ∀ x U V : F, (A₁.ev x U V * B₁.ev x U V = C₁.ev x U V) ↔ P x U V) :
    pairSol A₁ B₁ C₁ A₂ B₂ C₂ =
      {x : F | ∃ U V : F, P x U V ∧ A₂.ev x U V * B₂.ev x U V = C₂.ev x U V} := by
  ext x
  constructor
  · rintro ⟨U, V, h1, h2⟩
    exact ⟨U, V, (h x U V).1 h1, h2⟩
  · rintro ⟨U, V, h1, h2⟩
    exact ⟨U, V, (h x U V).2 h1, h2⟩

/-- Swapping the two factors of the first row. -/
theorem pairSol_swap (A₁ B₁ C₁ A₂ B₂ C₂ : PAff F) :
    pairSol A₁ B₁ C₁ A₂ B₂ C₂ = pairSol B₁ A₁ C₁ A₂ B₂ C₂ := by
  ext x
  constructor <;> rintro ⟨U, V, h1, h2⟩ <;> exact ⟨U, V, by rw [mul_comm]; exact h1, h2⟩

/-! ## The three cases -/

/-- **First row affine.**  If the first factor of the first row has zero linear part, the
    first row is affine in the witnesses. -/
theorem pairSol_smallOrCofinite_of_affine [IsAlgClosed F] (A₁ B₁ C₁ A₂ B₂ C₂ : PAff F)
    (hA₁ : A₁.c.natDegree ≤ 1) (hB₁ : B₁.c.natDegree ≤ 1) (hC₁ : C₁.c.natDegree ≤ 1)
    (hA₂ : A₂.c.natDegree ≤ 1) (hB₂ : B₂.c.natDegree ≤ 1) (hC₂ : C₂.c.natDegree ≤ 1)
    (hy : A₁.cy = 0) (hz : A₁.cz = 0) :
    SmallOrCofinite (pairSol A₁ B₁ C₁ A₂ B₂ C₂) 7 := by
  classical
  set p : F[X] := A₁.c * Polynomial.C B₁.cy - Polynomial.C C₁.cy with hp
  set q : F[X] := A₁.c * Polynomial.C B₁.cz - Polynomial.C C₁.cz with hq
  set r : F[X] := A₁.c * B₁.c - C₁.c with hr
  have hrw : pairSol A₁ B₁ C₁ A₂ B₂ C₂ =
      {x : F | ∃ y z : F, p.eval x * y + q.eval x * z + r.eval x = 0 ∧
        A₂.ev x y z * B₂.ev x y z = C₂.ev x y z} := by
    refine pairSol_eq_of_row1 _ _ _ _ _ _ _ ?_
    intro x U V
    simp only [PAff.ev, hy, hz, hp, hq, hr, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_C]
    constructor <;> intro hh <;> linear_combination hh
  rw [hrw]
  refine caseLinear_smallOrCofinite p q r ?_ ?_ ?_ A₂ B₂ C₂ hA₂ hB₂ hC₂
  · exact deg_sub_le (le_trans (Polynomial.natDegree_mul_le) (by simpa using hA₁)) (deg_C_le _ _)
  · exact deg_sub_le (le_trans (Polynomial.natDegree_mul_le) (by simpa using hA₁)) (deg_C_le _ _)
  · exact deg_sub_le (deg_mul_le hA₁ hB₁) (le_trans hC₁ (by norm_num))

/-- **First row a hyperbola.**  If the linear parts of the two factors of the first row
    are independent, the witnesses can be renamed so that the first row is `U V = h(x)`. -/
theorem pairSol_smallOrCofinite_of_indep [IsAlgClosed F] (A₁ B₁ C₁ A₂ B₂ C₂ : PAff F)
    (hA₁ : A₁.c.natDegree ≤ 1) (hB₁ : B₁.c.natDegree ≤ 1) (hC₁ : C₁.c.natDegree ≤ 1)
    (hA₂ : A₂.c.natDegree ≤ 1) (hB₂ : B₂.c.natDegree ≤ 1) (hC₂ : C₂.c.natDegree ≤ 1)
    (hdet : A₁.cy * B₁.cz - A₁.cz * B₁.cy ≠ 0) :
    SmallOrCofinite (pairSol A₁ B₁ C₁ A₂ B₂ C₂) 7 := by
  classical
  obtain ⟨σ, hσ, hPy, hPz, hAσ, hBσ⟩ := exists_subst_pair A₁ B₁ hA₁ hB₁ hdet
  rw [pairSol_sub A₁ B₁ C₁ A₂ B₂ C₂ σ hσ]
  set g0 : F := (C₁.sub σ).cy with hg0
  set g1 : F := (C₁.sub σ).cz with hg1
  set τ : Subst F := ⟨1, 0, 0, 1, Polynomial.C g1, Polynomial.C g0⟩ with hτ
  have hτdet : τ.det ≠ 0 := by
    show (1 : F) * 1 - 0 * 0 ≠ 0
    simp
  rw [pairSol_sub _ _ _ _ _ _ τ hτdet]
  set h : F[X] := (C₁.sub σ).c + Polynomial.C (g0 * g1) with hh
  have hAτ : ∀ x U V : F, ((A₁.sub σ).sub τ).ev x U V = U + g1 := by
    intro x U V
    rw [PAff.sub_ev, hAσ]
    simp [hτ]
  have hBτ : ∀ x U V : F, ((B₁.sub σ).sub τ).ev x U V = V + g0 := by
    intro x U V
    rw [PAff.sub_ev, hBσ]
    simp [hτ]
  have hCτ : ∀ x U V : F, ((C₁.sub σ).sub τ).ev x U V =
      g0 * (U + g1) + g1 * (V + g0) + (C₁.sub σ).c.eval x := by
    intro x U V
    rw [PAff.sub_ev]
    simp only [PAff.ev, hτ, Polynomial.eval_C, hg0, hg1]
    ring
  have hrw : pairSol ((A₁.sub σ).sub τ) ((B₁.sub σ).sub τ) ((C₁.sub σ).sub τ)
      ((A₂.sub σ).sub τ) ((B₂.sub σ).sub τ) ((C₂.sub σ).sub τ) =
      {x : F | ∃ U V : F, U * V = h.eval x ∧
        ((A₂.sub σ).sub τ).ev x U V * ((B₂.sub σ).sub τ).ev x U V =
          ((C₂.sub σ).sub τ).ev x U V} := by
    refine pairSol_eq_of_row1 _ _ _ _ _ _ _ ?_
    intro x U V
    rw [hAτ, hBτ, hCτ]
    simp only [hh, Polynomial.eval_add, Polynomial.eval_C]
    constructor <;> intro hx <;> linear_combination hx
  rw [hrw]
  have hdh : h.natDegree ≤ 1 :=
    deg_add_le (PAff.sub_deg C₁ σ hC₁ hPy hPz) (deg_C_le _ _)
  refine caseHyperbola_smallOrCofinite h hdh _ _ _ ?_ ?_ ?_ <;>
    exact PAff.sub_deg _ τ (PAff.sub_deg _ σ (by assumption) hPy hPz) (by simp [hτ]) (by simp [hτ])

/-- **First row a parabola.**  If the linear parts of the two factors of the first row are
    parallel and nonzero, the witnesses can be renamed so that the first row is
    `U (k U + t(x)) = γ₀ U + γ₁ V + s(x)` with `k ≠ 0`. -/
theorem pairSol_smallOrCofinite_of_parallel [IsAlgClosed F] (A₁ B₁ C₁ A₂ B₂ C₂ : PAff F)
    (hA₁ : A₁.c.natDegree ≤ 1) (hB₁ : B₁.c.natDegree ≤ 1) (hC₁ : C₁.c.natDegree ≤ 1)
    (hA₂ : A₂.c.natDegree ≤ 1) (hB₂ : B₂.c.natDegree ≤ 1) (hC₂ : C₂.c.natDegree ≤ 1)
    (hAne : A₁.cy ≠ 0 ∨ A₁.cz ≠ 0) (hBne : B₁.cy ≠ 0 ∨ B₁.cz ≠ 0)
    (hdet : A₁.cy * B₁.cz - A₁.cz * B₁.cy = 0) :
    SmallOrCofinite (pairSol A₁ B₁ C₁ A₂ B₂ C₂) 7 := by
  classical
  obtain ⟨k, hk, hk0, hk1⟩ := exists_prop_factor A₁.cy A₁.cz B₁.cy B₁.cz hAne hBne hdet
  obtain ⟨σ, hσ, hPy, hPz, hlin⟩ := exists_subst_single A₁ hA₁ hAne
  rw [pairSol_sub A₁ B₁ C₁ A₂ B₂ C₂ σ hσ]
  set t : F[X] := B₁.c - Polynomial.C k * A₁.c with ht
  set g0 : F := (C₁.sub σ).cy with hg0
  set g1 : F := (C₁.sub σ).cz with hg1
  set s : F[X] := (C₁.sub σ).c with hs
  have hdt : t.natDegree ≤ 1 := deg_sub_le hB₁ (deg_C_mul_le hA₁)
  have hds : s.natDegree ≤ 1 := PAff.sub_deg C₁ σ hC₁ hPy hPz
  have hAσ : ∀ x U V : F, (A₁.sub σ).ev x U V = U := by
    intro x U V
    rw [PAff.sub_ev_expand, hlin]
    ring
  have hBσ : ∀ x U V : F, (B₁.sub σ).ev x U V = k * U + t.eval x := by
    intro x U V
    rw [PAff.sub_ev_expand, hk0, hk1]
    have := hlin x U V
    simp only [ht, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C]
    linear_combination k * this
  have hCσ : ∀ x U V : F, (C₁.sub σ).ev x U V = g0 * U + g1 * V + s.eval x := by
    intro x U V
    simp only [PAff.ev, hg0, hg1, hs]
  have hdA₂ : ((A₂.sub σ)).c.natDegree ≤ 1 := PAff.sub_deg A₂ σ hA₂ hPy hPz
  have hdB₂ : ((B₂.sub σ)).c.natDegree ≤ 1 := PAff.sub_deg B₂ σ hB₂ hPy hPz
  have hdC₂ : ((C₂.sub σ)).c.natDegree ≤ 1 := PAff.sub_deg C₂ σ hC₂ hPy hPz
  by_cases hg1z : g1 ≠ 0
  · have hrw : pairSol (A₁.sub σ) (B₁.sub σ) (C₁.sub σ) (A₂.sub σ) (B₂.sub σ) (C₂.sub σ) =
        {x : F | ∃ U V : F, U * (k * U + t.eval x) = g0 * U + g1 * V + s.eval x ∧
          (A₂.sub σ).ev x U V * (B₂.sub σ).ev x U V = (C₂.sub σ).ev x U V} := by
      refine pairSol_eq_of_row1 _ _ _ _ _ _ _ ?_
      intro x U V
      rw [hAσ, hBσ, hCσ]
    rw [hrw]
    exact caseParabolaSolve_smallOrCofinite k g0 g1 hg1z t s hdt hds _ _ _ hdA₂ hdB₂ hdC₂
  · push_neg at hg1z
    have hrw : pairSol (A₁.sub σ) (B₁.sub σ) (C₁.sub σ) (A₂.sub σ) (B₂.sub σ) (C₂.sub σ) =
        {x : F | ∃ U V : F, U * (k * U + t.eval x) = g0 * U + s.eval x ∧
          (A₂.sub σ).ev x U V * (B₂.sub σ).ev x U V = (C₂.sub σ).ev x U V} := by
      refine pairSol_eq_of_row1 _ _ _ _ _ _ _ ?_
      intro x U V
      rw [hAσ, hBσ, hCσ, hg1z]
      constructor <;> intro hx <;> linear_combination hx
    rw [hrw]
    exact caseParabolaPure_smallOrCofinite k g0 hk t s hdt hds _ _ _ hdA₂ hdB₂ hdC₂

/-! ## The two-witness two-row theorem -/

/-- **Two rows over two witnesses accept a small or cofinite set of public inputs.**
    Every affine form is allowed to depend on the public input with degree at most one,
    and the witnesses are unconstrained otherwise. -/
theorem pairSol_smallOrCofinite [IsAlgClosed F] (A₁ B₁ C₁ A₂ B₂ C₂ : PAff F)
    (hA₁ : A₁.c.natDegree ≤ 1) (hB₁ : B₁.c.natDegree ≤ 1) (hC₁ : C₁.c.natDegree ≤ 1)
    (hA₂ : A₂.c.natDegree ≤ 1) (hB₂ : B₂.c.natDegree ≤ 1) (hC₂ : C₂.c.natDegree ≤ 1) :
    SmallOrCofinite (pairSol A₁ B₁ C₁ A₂ B₂ C₂) 7 := by
  classical
  by_cases hAne : A₁.cy ≠ 0 ∨ A₁.cz ≠ 0
  · by_cases hBne : B₁.cy ≠ 0 ∨ B₁.cz ≠ 0
    · by_cases hdet : A₁.cy * B₁.cz - A₁.cz * B₁.cy = 0
      · exact pairSol_smallOrCofinite_of_parallel A₁ B₁ C₁ A₂ B₂ C₂ hA₁ hB₁ hC₁ hA₂ hB₂ hC₂
          hAne hBne hdet
      · exact pairSol_smallOrCofinite_of_indep A₁ B₁ C₁ A₂ B₂ C₂ hA₁ hB₁ hC₁ hA₂ hB₂ hC₂ hdet
    · push_neg at hBne
      rw [pairSol_swap]
      exact pairSol_smallOrCofinite_of_affine B₁ A₁ C₁ A₂ B₂ C₂ hB₁ hA₁ hC₁ hA₂ hB₂ hC₂
        hBne.1 hBne.2
  · push_neg at hAne
    exact pairSol_smallOrCofinite_of_affine A₁ B₁ C₁ A₂ B₂ C₂ hA₁ hB₁ hC₁ hA₂ hB₂ hC₂
      hAne.1 hAne.2

end Solution.Research
