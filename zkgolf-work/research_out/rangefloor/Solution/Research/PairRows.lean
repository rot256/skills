/-
  # Two witnesses, two rows: the language and the easy cases

  This file sets up the language in which the last open configuration of the score bound
  is analysed: a pair of R1CS rows over two witnesses `y, z`.  After fixing the public
  input `x`, every affine form is affine in `(y, z)` with *constant* witness coefficients
  and a constant term that is a polynomial in `x` of degree at most one.  That is exactly
  the data of `PAff`.

  An invertible affine change of the witnesses, with constant linear part and polynomial
  translations, maps `PAff`s to `PAff`s and does not change the accepted set of `x`
  (`pairSol_sub`).  Using it, the first row may always be put in one of three normal
  forms; the two easy ones — a single row, and a row that is affine in the witnesses —
  are settled here.
-/
import Solution.Research.Elim
import Solution.Research.LowerBound

namespace Solution.Research

open Polynomial

variable {F : Type*} [Field F]

/-! ## Degree bookkeeping -/

theorem deg_add_le {p q : F[X]} {a : ℕ} (hp : p.natDegree ≤ a) (hq : q.natDegree ≤ a) :
    (p + q).natDegree ≤ a := le_trans (Polynomial.natDegree_add_le _ _) (max_le hp hq)

theorem deg_sub_le {p q : F[X]} {a : ℕ} (hp : p.natDegree ≤ a) (hq : q.natDegree ≤ a) :
    (p - q).natDegree ≤ a := le_trans (Polynomial.natDegree_sub_le _ _) (max_le hp hq)

theorem deg_mul_le {p q : F[X]} {a b : ℕ} (hp : p.natDegree ≤ a) (hq : q.natDegree ≤ b) :
    (p * q).natDegree ≤ a + b :=
  le_trans Polynomial.natDegree_mul_le (Nat.add_le_add hp hq)

theorem deg_C_mul_le {t : F} {p : F[X]} {a : ℕ} (hp : p.natDegree ≤ a) :
    (Polynomial.C t * p).natDegree ≤ a :=
  le_trans Polynomial.natDegree_mul_le (by simpa using hp)

theorem deg_C_le (t : F) (a : ℕ) : (Polynomial.C t).natDegree ≤ a := by simp

theorem deg_zero_le (a : ℕ) : (0 : F[X]).natDegree ≤ a := by simp

/-! ## Affine forms in two witnesses -/

/-- An affine form in two witnesses whose constant term depends polynomially on the
    public input. -/
structure PAff (F : Type*) [Field F] where
  /-- coefficient of the first witness -/
  cy : F
  /-- coefficient of the second witness -/
  cz : F
  /-- constant term, a polynomial in the public input -/
  c : F[X]

/-- Value of an affine form at a public input and a witness pair. -/
def PAff.ev (L : PAff F) (x y z : F) : F := L.cy * y + L.cz * z + L.c.eval x

/-- The public inputs accepted by a pair of R1CS rows in two witnesses. -/
def pairSol (A₁ B₁ C₁ A₂ B₂ C₂ : PAff F) : Set F :=
  {x : F | ∃ y z : F, A₁.ev x y z * B₁.ev x y z = C₁.ev x y z ∧
      A₂.ev x y z * B₂.ev x y z = C₂.ev x y z}

/-- The public inputs accepted by a single R1CS row in two witnesses. -/
def rowSol (A B C : PAff F) : Set F :=
  {x : F | ∃ y z : F, A.ev x y z * B.ev x y z = C.ev x y z}

theorem rowSol_comm (A B C : PAff F) : rowSol A B C = rowSol B A C := by
  ext x
  constructor <;> rintro ⟨y, z, h⟩ <;> exact ⟨y, z, by rw [mul_comm]; exact h⟩

/-! ## Invertible affine substitutions of the witnesses -/

/-- An affine substitution of the witness pair with constant linear part. -/
structure Subst (F : Type*) [Field F] where
  /-- coefficient of the new first witness in the old first witness -/
  p₀ : F
  /-- coefficient of the new second witness in the old first witness -/
  p₁ : F
  /-- coefficient of the new first witness in the old second witness -/
  q₀ : F
  /-- coefficient of the new second witness in the old second witness -/
  q₁ : F
  /-- translation of the old first witness -/
  Py : F[X]
  /-- translation of the old second witness -/
  Pz : F[X]

/-- Determinant of the linear part of a substitution. -/
def Subst.det (σ : Subst F) : F := σ.p₀ * σ.q₁ - σ.p₁ * σ.q₀

/-- An affine form read in the new coordinates. -/
noncomputable def PAff.sub (L : PAff F) (σ : Subst F) : PAff F :=
  ⟨L.cy * σ.p₀ + L.cz * σ.q₀, L.cy * σ.p₁ + L.cz * σ.q₁,
    L.c + Polynomial.C L.cy * σ.Py + Polynomial.C L.cz * σ.Pz⟩

theorem PAff.sub_ev (L : PAff F) (σ : Subst F) (x U V : F) :
    (L.sub σ).ev x U V =
      L.ev x (σ.p₀ * U + σ.p₁ * V + σ.Py.eval x) (σ.q₀ * U + σ.q₁ * V + σ.Pz.eval x) := by
  simp only [PAff.sub, PAff.ev, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
  ring

theorem PAff.sub_deg (L : PAff F) (σ : Subst F) (hL : L.c.natDegree ≤ 1)
    (h1 : σ.Py.natDegree ≤ 1) (h2 : σ.Pz.natDegree ≤ 1) : (L.sub σ).c.natDegree ≤ 1 :=
  deg_add_le (deg_add_le hL (deg_C_mul_le h1)) (deg_C_mul_le h2)

/-- Substituting invertibly in the witnesses does not change the accepted set. -/
theorem pairSol_sub (A₁ B₁ C₁ A₂ B₂ C₂ : PAff F) (σ : Subst F) (hσ : σ.det ≠ 0) :
    pairSol A₁ B₁ C₁ A₂ B₂ C₂ =
      pairSol (A₁.sub σ) (B₁.sub σ) (C₁.sub σ) (A₂.sub σ) (B₂.sub σ) (C₂.sub σ) := by
  ext x
  constructor
  · rintro ⟨y, z, e1, e2⟩
    have hy : σ.p₀ * ((σ.q₁ * (y - σ.Py.eval x) - σ.p₁ * (z - σ.Pz.eval x)) / σ.det) +
        σ.p₁ * ((σ.p₀ * (z - σ.Pz.eval x) - σ.q₀ * (y - σ.Py.eval x)) / σ.det) +
        σ.Py.eval x = y := by
      field_simp
      rw [Subst.det]
      ring
    have hz : σ.q₀ * ((σ.q₁ * (y - σ.Py.eval x) - σ.p₁ * (z - σ.Pz.eval x)) / σ.det) +
        σ.q₁ * ((σ.p₀ * (z - σ.Pz.eval x) - σ.q₀ * (y - σ.Py.eval x)) / σ.det) +
        σ.Pz.eval x = z := by
      field_simp
      rw [Subst.det]
      ring
    refine ⟨(σ.q₁ * (y - σ.Py.eval x) - σ.p₁ * (z - σ.Pz.eval x)) / σ.det,
      (σ.p₀ * (z - σ.Pz.eval x) - σ.q₀ * (y - σ.Py.eval x)) / σ.det, ?_, ?_⟩ <;>
      rw [PAff.sub_ev, PAff.sub_ev, PAff.sub_ev, hy, hz] <;> assumption
  · rintro ⟨U, V, e1, e2⟩
    rw [PAff.sub_ev, PAff.sub_ev, PAff.sub_ev] at e1
    rw [PAff.sub_ev, PAff.sub_ev, PAff.sub_ev] at e2
    exact ⟨_, _, e1, e2⟩

/-! ## A single row in two witnesses -/

/-- Two nonzero linear forms on `F ^ 2` are simultaneously nonzero somewhere. -/
theorem exists_pair_dot_ne_zero [Infinite F] (a₀ a₁ b₀ b₁ : F)
    (ha : a₀ ≠ 0 ∨ a₁ ≠ 0) (hb : b₀ ≠ 0 ∨ b₁ ≠ 0) :
    ∃ v₀ v₁ : F, a₀ * v₀ + a₁ * v₁ ≠ 0 ∧ b₀ * v₀ + b₁ * v₁ ≠ 0 := by
  classical
  have hne : ∀ c₀ c₁ : F, (c₀ ≠ 0 ∨ c₁ ≠ 0) →
      (Polynomial.C c₀ + Polynomial.C c₁ * X : F[X]) ≠ 0 := by
    intro c₀ c₁ hc h
    have h0 : (Polynomial.C c₀ + Polynomial.C c₁ * X : F[X]).coeff 0 = c₀ := by simp
    have h1 : (Polynomial.C c₀ + Polynomial.C c₁ * X : F[X]).coeff 1 = c₁ := by simp
    rcases hc with h' | h'
    · exact h' (by rw [← h0, h, Polynomial.coeff_zero])
    · exact h' (by rw [← h1, h, Polynomial.coeff_zero])
  have hP : ((Polynomial.C a₀ + Polynomial.C a₁ * X) *
      (Polynomial.C b₀ + Polynomial.C b₁ * X) : F[X]) ≠ 0 :=
    mul_ne_zero (hne _ _ ha) (hne _ _ hb)
  obtain ⟨s, hs⟩ :=
    ((Set.infinite_univ (α := F)).diff (Polynomial.finite_setOf_isRoot hP)).nonempty
  have hs' : ((Polynomial.C a₀ + Polynomial.C a₁ * X) *
      (Polynomial.C b₀ + Polynomial.C b₁ * X) : F[X]).eval s ≠ 0 := fun h => hs.2 h
  rw [Polynomial.eval_mul] at hs'
  refine ⟨1, s, ?_, ?_⟩
  · intro h
    refine hs' ?_
    have : (Polynomial.C a₀ + Polynomial.C a₁ * X : F[X]).eval s = 0 := by
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      linear_combination h
    rw [this, zero_mul]
  · intro h
    refine hs' ?_
    have : (Polynomial.C b₀ + Polynomial.C b₁ * X : F[X]).eval s = 0 := by
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      linear_combination h
    rw [this, mul_zero]

/-- A single row whose first factor does not involve the witnesses. -/
theorem rowSol_smallOrCofinite_of_left_const [IsAlgClosed F] (A B C : PAff F)
    (hA0 : A.cy = 0) (hA1 : A.cz = 0) (hA : A.c.natDegree ≤ 1) (hB : B.c.natDegree ≤ 1)
    (hC : C.c.natDegree ≤ 1) : SmallOrCofinite (rowSol A B C) 2 := by
  classical
  set p : F[X] := A.c * Polynomial.C B.cy - Polynomial.C C.cy with hp
  set q : F[X] := A.c * Polynomial.C B.cz - Polynomial.C C.cz with hq
  set r : F[X] := A.c * B.c - C.c with hr
  have hmem : ∀ x y z : F, (A.ev x y z * B.ev x y z = C.ev x y z) ↔
      p.eval x * y + q.eval x * z + r.eval x = 0 := by
    intro x y z
    simp only [PAff.ev, hA0, hA1, hp, hq, hr, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_C]
    constructor <;> intro h <;> linear_combination h
  by_cases hp0 : p ≠ 0
  · refine SmallOrCofinite.of_compl_subset_zeroSet hp0 ?_ 2
    intro x hx
    by_contra hne
    exact hx ⟨-(r.eval x) / p.eval x, 0, (hmem x _ _).2 (by field_simp; ring)⟩
  · push_neg at hp0
    by_cases hq0 : q ≠ 0
    · refine SmallOrCofinite.of_compl_subset_zeroSet hq0 ?_ 2
      intro x hx
      by_contra hne
      exact hx ⟨0, -(r.eval x) / q.eval x, (hmem x _ _).2 (by field_simp; ring)⟩
    · push_neg at hq0
      have hset : rowSol A B C = {x : F | r.eval x = 0} := by
        ext x
        constructor
        · rintro ⟨y, z, h⟩
          have := (hmem x y z).1 h
          rw [hp0, hq0] at this
          simpa using this
        · intro hx
          exact ⟨0, 0, (hmem x 0 0).2 (by simpa using hx)⟩
      refine (SmallOrCofinite.zeroSet r).congr_set hset.symm |>.mono ?_
      exact deg_sub_le (by simpa using deg_mul_le hA hB) (le_trans hC (by norm_num))

/-- **A single row in two witnesses.**  Its accepted set has at most two elements or is
    cofinite. -/
theorem rowSol_smallOrCofinite [IsAlgClosed F] (A B C : PAff F)
    (hA : A.c.natDegree ≤ 1) (hB : B.c.natDegree ≤ 1) (hC : C.c.natDegree ≤ 1) :
    SmallOrCofinite (rowSol A B C) 2 := by
  classical
  by_cases hAn : A.cy ≠ 0 ∨ A.cz ≠ 0
  · by_cases hBn : B.cy ≠ 0 ∨ B.cz ≠ 0
    · -- both factors involve the witnesses: every `x` is accepted
      refine SmallOrCofinite.of_compl_finite ?_ 2
      have : rowSol A B C = Set.univ := by
        ext x
        simp only [Set.mem_univ, iff_true, rowSol, Set.mem_setOf_eq]
        obtain ⟨v₀, v₁, hv1, hv2⟩ := exists_pair_dot_ne_zero A.cy A.cz B.cy B.cz hAn hBn
        obtain ⟨t, ht⟩ := exists_quad_root ((A.cy * v₀ + A.cz * v₁) * (B.cy * v₀ + B.cz * v₁))
          (A.c.eval x * (B.cy * v₀ + B.cz * v₁) + B.c.eval x * (A.cy * v₀ + A.cz * v₁) -
            (C.cy * v₀ + C.cz * v₁))
          (A.c.eval x * B.c.eval x - C.c.eval x) (mul_ne_zero hv1 hv2)
        refine ⟨t * v₀, t * v₁, ?_⟩
        simp only [PAff.ev]
        linear_combination ht
      rw [this]
      simp
    · push_neg at hBn
      rw [rowSol_comm]
      exact rowSol_smallOrCofinite_of_left_const B A C hBn.1 hBn.2 hB hA hC
  · push_neg at hAn
    exact rowSol_smallOrCofinite_of_left_const A B C hAn.1 hAn.2 hA hB hC

/-! ## A row that is affine in the witnesses -/

/-- Eliminating the first witness from `P y + Q z + R = 0`: after clearing the
    denominator `P` the row becomes a quadratic in `z`. -/
theorem pair_elim_identity (P Q R ay az a by2 bz b cy cz c y z : F)
    (hy : P * y = -(Q * z) - R) :
    ((az * P - ay * Q) * z + (P * a - ay * R)) * ((bz * P - by2 * Q) * z + (P * b - by2 * R))
      - P * ((cz * P - cy * Q) * z + (P * c - cy * R))
      = P ^ 2 * ((ay * y + az * z + a) * (by2 * y + bz * z + b) - (cy * y + cz * z + c)) := by
  linear_combination (-(ay * (P * (by2 * y + bz * z + b)) + by2 * (P * (ay * y + az * z + a))
    - ay * by2 * (P * y + Q * z + R) - P * cy)) * hy

/-- The main step: with `p ≠ 0` the first witness can be eliminated, and the second
    unknown satisfies a single quadratic whose coefficients are polynomials in `x`. -/
theorem caseLinear_smallOrCofinite_of_ne [IsAlgClosed F] (p q r : F[X]) (hp : p.natDegree ≤ 1)
    (hr : r.natDegree ≤ 2) (hp0 : p ≠ 0) (A B C : PAff F)
    (hA : A.c.natDegree ≤ 1) (hB : B.c.natDegree ≤ 1) (hC : C.c.natDegree ≤ 1) :
    SmallOrCofinite {x : F | ∃ y z : F, p.eval x * y + q.eval x * z + r.eval x = 0 ∧
      A.ev x y z * B.ev x y z = C.ev x y z} 7 := by
  classical
  set T := {x : F | ∃ y z : F, p.eval x * y + q.eval x * z + r.eval x = 0 ∧
      A.ev x y z * B.ev x y z = C.ev x y z} with hT
  set A1 : F[X] := Polynomial.C A.cz * p - Polynomial.C A.cy * q with hA1
  set A0 : F[X] := p * A.c - Polynomial.C A.cy * r with hA0
  set B1 : F[X] := Polynomial.C B.cz * p - Polynomial.C B.cy * q with hB1
  set B0 : F[X] := p * B.c - Polynomial.C B.cy * r with hB0
  set C1 : F[X] := Polynomial.C C.cz * p - Polynomial.C C.cy * q with hC1
  set C0 : F[X] := p * C.c - Polynomial.C C.cy * r with hC0
  set c₀ : F[X] := A0 * B0 - p * C0 with hc₀
  set c₁ : F[X] := A1 * B0 + A0 * B1 - p * C1 with hc₁
  set c₂ : F[X] := A1 * B1 with hc₂
  have hkey : T ∩ {x : F | p.eval x ≠ 0} =
      quintSet ![c₀, c₁, c₂, 0, 0] ∩ {x : F | p.eval x ≠ 0} := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, hT, quintSet]
    constructor
    · rintro ⟨⟨y, z, hlin, hrow⟩, hpx⟩
      refine ⟨⟨z, ?_⟩, hpx⟩
      rw [quintEval_explicit]
      have hy : p.eval x * y = -(q.eval x * z) - r.eval x := by linear_combination hlin
      have hid := pair_elim_identity (p.eval x) (q.eval x) (r.eval x) A.cy A.cz (A.c.eval x)
        B.cy B.cz (B.c.eval x) C.cy C.cz (C.c.eval x) y z hy
      simp only [hc₀, hc₁, hc₂, hA0, hA1, hB0, hB1, hC0, hC1, Polynomial.eval_sub,
        Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_zero]
      simp only [PAff.ev] at hrow
      linear_combination hid + (p.eval x) ^ 2 * hrow
    · rintro ⟨⟨z, hz⟩, hpx⟩
      rw [quintEval_explicit] at hz
      have hy : p.eval x * ((-(q.eval x * z) - r.eval x) / p.eval x) =
          -(q.eval x * z) - r.eval x := by field_simp
      have hid := pair_elim_identity (p.eval x) (q.eval x) (r.eval x) A.cy A.cz (A.c.eval x)
        B.cy B.cz (B.c.eval x) C.cy C.cz (C.c.eval x)
        ((-(q.eval x * z) - r.eval x) / p.eval x) z hy
      simp only [hc₀, hc₁, hc₂, hA0, hA1, hB0, hB1, hC0, hC1, Polynomial.eval_sub,
        Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_zero] at hz
      refine ⟨⟨(-(q.eval x * z) - r.eval x) / p.eval x, z, by linear_combination hy, ?_⟩, hpx⟩
      have hD : (p.eval x) ^ 2 * (A.ev x ((-(q.eval x * z) - r.eval x) / p.eval x) z *
          B.ev x ((-(q.eval x * z) - r.eval x) / p.eval x) z -
          C.ev x ((-(q.eval x * z) - r.eval x) / p.eval x) z) = 0 := by
        simp only [PAff.ev]
        linear_combination hz - hid
      have hDz := (mul_eq_zero.1 hD).resolve_left (pow_ne_zero 2 hpx)
      linear_combination hDz
  have hdeg0 : c₀.natDegree ≤ 4 := by
    refine deg_sub_le ?_ ?_
    · exact deg_mul_le (deg_sub_le (deg_mul_le hp hA) (le_trans (deg_C_mul_le hr) (by norm_num)))
        (deg_sub_le (deg_mul_le hp hB) (le_trans (deg_C_mul_le hr) (by norm_num)))
    · exact le_trans (deg_mul_le hp
        (deg_sub_le (deg_mul_le hp hC) (le_trans (deg_C_mul_le hr) (by norm_num)))) (by norm_num)
  have h1 : SmallOrCofinite (T ∩ {x : F | p.eval x ≠ 0}) 4 := by
    rw [hkey]
    exact (quintSet_smallOrCofinite ![c₀, c₁, c₂, 0, 0] (by simpa using hdeg0)).inter_nonzero hp0
  have h2 : SmallOrCofinite (T ∩ {x : F | p.eval x = 0}) 1 :=
    (SmallOrCofinite.of_subset_zeroSet hp0 (fun x hx => hx.2)).mono hp
  refine ((h1.union h2).congr_set ?_).mono (by norm_num)
  ext x
  by_cases hx : p.eval x = 0 <;> simp [hx]

/-- **Row one affine in the witnesses.**  If the first constraint is
    `p(x) y + q(x) z + r(x) = 0`, one witness can be eliminated and the accepted set is
    small or cofinite. -/
theorem caseLinear_smallOrCofinite [IsAlgClosed F] (p q r : F[X]) (hp : p.natDegree ≤ 1)
    (hq : q.natDegree ≤ 1) (hr : r.natDegree ≤ 2) (A B C : PAff F)
    (hA : A.c.natDegree ≤ 1) (hB : B.c.natDegree ≤ 1) (hC : C.c.natDegree ≤ 1) :
    SmallOrCofinite {x : F | ∃ y z : F, p.eval x * y + q.eval x * z + r.eval x = 0 ∧
      A.ev x y z * B.ev x y z = C.ev x y z} 7 := by
  classical
  by_cases hp0 : p ≠ 0
  · exact caseLinear_smallOrCofinite_of_ne p q r hp hr hp0 A B C hA hB hC
  · push_neg at hp0
    by_cases hq0 : q ≠ 0
    · -- swap the two witnesses
      have hswap : {x : F | ∃ y z : F, p.eval x * y + q.eval x * z + r.eval x = 0 ∧
            A.ev x y z * B.ev x y z = C.ev x y z} =
          {x : F | ∃ y z : F, q.eval x * y + p.eval x * z + r.eval x = 0 ∧
            (⟨A.cz, A.cy, A.c⟩ : PAff F).ev x y z * (⟨B.cz, B.cy, B.c⟩ : PAff F).ev x y z =
              (⟨C.cz, C.cy, C.c⟩ : PAff F).ev x y z} := by
        ext x
        constructor
        · rintro ⟨y, z, hlin, hrow⟩
          refine ⟨z, y, by linear_combination hlin, ?_⟩
          simp only [PAff.ev] at hrow ⊢
          linear_combination hrow
        · rintro ⟨y, z, hlin, hrow⟩
          refine ⟨z, y, by linear_combination hlin, ?_⟩
          simp only [PAff.ev] at hrow ⊢
          linear_combination hrow
      rw [hswap]
      exact caseLinear_smallOrCofinite_of_ne q p r hq hr hq0 _ _ _ hA hB hC
    · push_neg at hq0
      subst hp0
      subst hq0
      by_cases hr0 : r ≠ 0
      · refine (SmallOrCofinite.of_subset_zeroSet hr0 ?_).mono (le_trans hr (by norm_num))
        rintro x ⟨y, z, hlin, -⟩
        simpa using hlin
      · push_neg at hr0
        subst hr0
        have hset : {x : F | ∃ y z : F,
            (0 : F[X]).eval x * y + (0 : F[X]).eval x * z + (0 : F[X]).eval x = 0 ∧
            A.ev x y z * B.ev x y z = C.ev x y z} = rowSol A B C := by
          ext x
          simp [rowSol]
        rw [hset]
        exact (rowSol_smallOrCofinite A B C hA hB hC).mono (by norm_num)

end Solution.Research
