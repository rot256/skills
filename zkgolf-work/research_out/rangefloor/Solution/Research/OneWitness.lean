/-
  # One witness certifies at most two bits

  `LowerBound.one_row_dichotomy` bounds what a single *row* can do, for any number of
  witnesses.  This file bounds what a single *witness* can do, for any number of rows.

  With `m = 1` every row is a quadratic in the single witness `y` whose leading
  coefficient is a **constant** (it is the product of the `y`-coefficients of the two
  affine factors) and whose lower coefficients are polynomials in `x` of degree `≤ 1` and
  `≤ 2`.  Eliminating the `y²` term between two rows therefore produces an honest
  *linear* consequence `b(x) * y + g(x) = 0` with `deg b ≤ 1`, `deg g ≤ 2`.  Either

  * no nonzero such consequence exists — then all the rows are proportional (or trivial)
    and, over an algebraically closed field, every `x` is accepted; or
  * one exists with `b = 0` — then the accepted `x` are roots of the nonzero `g`; or
  * one exists with `b ≠ 0` — then `y` is forced to be `-g(x)/b(x)` and substituting it
    into row `k` produces `P k = α k * g ^ 2 - β k * g * b + γ k * b ^ 2`, of degree `≤ 4`,
    which must vanish on every accepted `x`.  If some `P k ≠ 0` the accepted set lies in
    the roots of a nonzero degree-`≤ 4` polynomial; if all `P k = 0` then every `x` with
    `b(x) ≠ 0` is accepted.

  So the accepted set has at most four elements or omits at most one — in particular it is
  never the eight-element set of a three-bit range.  Consequently a system certifying
  `n ≥ 3` bits needs at least two witnesses, which raises the general score floor to `4`.
-/
import Solution.Research.Model
import Solution.Research.LowerBound

namespace Solution.Research

open Polynomial

variable {F : Type*} [Field F] {r : ℕ}

/-- A set contained in the roots of a nonzero polynomial of degree at most four (hence of
    size at most four). -/
def AtMostFourRoots (S : Set F) : Prop :=
  ∃ p : F[X], p ≠ 0 ∧ p.natDegree ≤ 4 ∧ ∀ x ∈ S, p.eval x = 0

/-- The `x` for which the family of quadratics `α j * y ^ 2 + β j x * y + γ j x` has a
    common root `y`. -/
def quadFamilySolutions (al : Fin r → F) (be ga : Fin r → F[X]) : Set F :=
  {x : F | ∃ y : F, ∀ j, al j * y ^ 2 + (be j).eval x * y + (ga j).eval x = 0}

/-- A set contained in the roots of a nonzero polynomial of degree `≤ 4` cannot contain
    five distinct elements. -/
theorem AtMostFourRoots.not_five {S : Set F} (h : AtMostFourRoots S) (Z : Finset F)
    (hZS : ∀ x ∈ Z, x ∈ S) (hcard : 5 ≤ Z.card) : False := by
  obtain ⟨p, hp0, hdeg, hroots⟩ := h
  exact hp0 (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' p Z
    (fun x hx => hroots x (hZS x hx)) (by omega))

/-- **A single witness certifies at most two bits.**  For any number of rows, the set of
    accepted `x` either lies in the roots of a nonzero polynomial of degree `≤ 4`, or omits
    at most one element of `F`. -/
theorem quad_family_dichotomy [IsAlgClosed F] (al : Fin r → F) (be ga : Fin r → F[X])
    (hbe : ∀ j, (be j).natDegree ≤ 1) (hga : ∀ j, (ga j).natDegree ≤ 2) :
    AtMostFourRoots (quadFamilySolutions al be ga) ∨
      CoAtMostOne (quadFamilySolutions al be ga) := by
  classical
  set S := quadFamilySolutions al be ga with hS
  by_cases hcons : ∃ b g : F[X], (b ≠ 0 ∨ g ≠ 0) ∧ b.natDegree ≤ 1 ∧ g.natDegree ≤ 2 ∧
      ∀ x y : F, (∀ j, al j * y ^ 2 + (be j).eval x * y + (ga j).eval x = 0) →
        b.eval x * y + g.eval x = 0
  · obtain ⟨b, g, hbg, hb1, hg2, hcon⟩ := hcons
    by_cases hb : b = 0
    · -- the consequence is `g(x) = 0`, with `g ≠ 0`
      subst hb
      left
      refine ⟨g, hbg.resolve_left (by simp), by omega, ?_⟩
      rintro x ⟨y, hy⟩
      have := hcon x y hy
      simpa using this
    · -- `y` is forced; substitute it into every row
      set P : Fin r → F[X] := fun k => C (al k) * g ^ 2 - be k * g * b + ga k * b ^ 2 with hP
      have hPdeg : ∀ k, (P k).natDegree ≤ 4 := by
        intro k
        have h1 : (C (al k) * g ^ 2).natDegree ≤ 4 := by
          refine le_trans (natDegree_C_mul_le _ _) ?_
          refine le_trans (natDegree_pow_le) ?_
          have := hga k
          omega
        have h2 : (be k * g * b).natDegree ≤ 4 := by
          refine le_trans (natDegree_mul_le) ?_
          have h3 : (be k * g).natDegree ≤ 3 := by
            refine le_trans (natDegree_mul_le) ?_
            have := hbe k; have := hga k; omega
          have := hb1
          omega
        have h4 : (ga k * b ^ 2).natDegree ≤ 4 := by
          refine le_trans (natDegree_mul_le) ?_
          have h5 : (b ^ 2).natDegree ≤ 2 := le_trans natDegree_pow_le (by omega)
          have := hga k
          omega
        calc (P k).natDegree ≤ max (C (al k) * g ^ 2 - be k * g * b).natDegree
              (ga k * b ^ 2).natDegree := natDegree_add_le _ _
          _ ≤ 4 := by
              refine max_le ?_ h4
              exact le_trans (natDegree_sub_le _ _) (max_le h1 h2)
      have hPzero : ∀ x ∈ S, ∀ k, (P k).eval x = 0 := by
        rintro x ⟨y, hy⟩ k
        have h1 := hcon x y hy
        have h2 := hy k
        simp only [hP, eval_sub, eval_add, eval_mul, eval_pow, eval_C]
        linear_combination (b.eval x) ^ 2 * h2 +
          (al k * (g.eval x - b.eval x * y) - (be k).eval x * b.eval x) * h1
      by_cases hall : ∀ k, P k = 0
      · -- every `x` off the (at most one) root of `b` is accepted
        right
        have hbroot : ∀ x z : F, b.eval x = 0 → b.eval z = 0 → x = z := by
          intro x z hx hz
          by_contra hne
          refine hb (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' b {x, z} ?_ ?_)
          · intro i hi
            simp only [Finset.mem_insert, Finset.mem_singleton] at hi
            rcases hi with rfl | rfl
            · exact hx
            · exact hz
          · rw [Finset.card_insert_of_notMem (by simpa using hne), Finset.card_singleton]
            omega
        refine ⟨if h : ∃ z, b.eval z = 0 then h.choose else 0, fun x hx => ?_⟩
        have hbx : b.eval x ≠ 0 := by
          intro h0
          apply hx
          rw [dif_pos ⟨x, h0⟩]
          exact hbroot x _ h0 (Exists.choose_spec (⟨x, h0⟩ : ∃ z, b.eval z = 0))
        refine ⟨-(g.eval x) / b.eval x, fun k => ?_⟩
        have hk := congrArg (Polynomial.eval x) (hall k)
        simp only [hP, eval_sub, eval_add, eval_mul, eval_pow, eval_C, eval_zero] at hk
        have hy2 : al k * (-(g.eval x) / b.eval x) ^ 2
              + (be k).eval x * (-(g.eval x) / b.eval x) + (ga k).eval x
            = (al k * (g.eval x) ^ 2 - (be k).eval x * (g.eval x) * b.eval x
               + (ga k).eval x * (b.eval x) ^ 2) / (b.eval x) ^ 2 := by
          field_simp
          ring
        rw [hy2, hk, zero_div]
      · left
        obtain ⟨k, hk⟩ := not_forall.mp hall
        exact ⟨P k, hk, hPdeg k, fun x hx => hPzero x hx k⟩
  · -- no nonzero linear consequence: all rows are proportional or trivial
    right
    push_neg at hcons
    have key : ∀ b g : F[X], b.natDegree ≤ 1 → g.natDegree ≤ 2 →
        (∀ x y : F, (∀ j, al j * y ^ 2 + (be j).eval x * y + (ga j).eval x = 0) →
          b.eval x * y + g.eval x = 0) → b = 0 ∧ g = 0 := by
      intro b g hb hg hc
      by_contra hne
      have : b ≠ 0 ∨ g ≠ 0 := by
        by_contra hc2
        push_neg at hc2
        exact hne ⟨hc2.1, hc2.2⟩
      obtain ⟨x, y, hxy, hne2⟩ := hcons b g this hb hg
      exact hne2 (hc x y hxy)
    have hpair : ∀ j k : Fin r,
        C (al j) * be k - C (al k) * be j = 0 ∧ C (al j) * ga k - C (al k) * ga j = 0 := by
      intro j k
      refine key _ _ ?_ ?_ ?_
      · refine le_trans (natDegree_sub_le _ _) (max_le ?_ ?_) <;>
          exact le_trans (natDegree_C_mul_le _ _) (by first | exact hbe k | exact hbe j)
      · refine le_trans (natDegree_sub_le _ _) (max_le ?_ ?_) <;>
          exact le_trans (natDegree_C_mul_le _ _) (by first | exact hga k | exact hga j)
      · intro x y hy
        have hj := hy j
        have hk := hy k
        simp only [eval_sub, eval_mul, eval_C]
        linear_combination al j * hk - al k * hj
    have htriv : ∀ j, al j = 0 → be j = 0 ∧ ga j = 0 := by
      intro j hj
      refine key _ _ (hbe j) (hga j) ?_
      intro x y hy
      have := hy j
      rw [hj] at this
      linear_combination this
    refine ⟨0, fun x _ => ?_⟩
    by_cases hall0 : ∀ j, al j = 0
    · refine ⟨0, fun j => ?_⟩
      obtain ⟨h1, h2⟩ := htriv j (hall0 j)
      simp [hall0 j, h1, h2]
    · obtain ⟨j0, hj0⟩ := not_forall.mp hall0
      obtain ⟨y, hy⟩ := exists_quad_root (al j0) ((be j0).eval x) ((ga j0).eval x) hj0
      refine ⟨y, fun k => ?_⟩
      obtain ⟨hb, hg⟩ := hpair j0 k
      have hbe' : al j0 * (be k).eval x = al k * (be j0).eval x := by
        have := congrArg (Polynomial.eval x) hb
        simp only [eval_sub, eval_mul, eval_C, eval_zero] at this
        linear_combination this
      have hga' : al j0 * (ga k).eval x = al k * (ga j0).eval x := by
        have := congrArg (Polynomial.eval x) hg
        simp only [eval_sub, eval_mul, eval_C, eval_zero] at this
        linear_combination this
      have := mul_left_cancel₀ hj0
        (show al j0 * (al k * y ^ 2 + (be k).eval x * y + (ga k).eval x) = al j0 * 0 by
          rw [mul_zero]
          linear_combination al k * hy + y * hbe' + hga')
      exact this

/-! ## From a one-witness system to a family of quadratics -/

/-- The `y²`-coefficient of a row over one witness: a constant, since both affine factors
    are linear in the witness. -/
def rowAl (R : Row F 1) : F := R.A.cw 0 * R.B.cw 0

/-- The `y`-coefficient of a row over one witness: affine in `x`. -/
noncomputable def rowBe (R : Row F 1) : F[X] :=
  C (R.A.cw 0 * R.B.cx + R.B.cw 0 * R.A.cx) * X
    + C (R.A.cw 0 * R.B.c + R.B.cw 0 * R.A.c - R.C.cw 0)

/-- The witness-free part of a row over one witness: quadratic in `x`. -/
noncomputable def rowGa (R : Row F 1) : F[X] :=
  (C R.A.cx * X + C R.A.c) * (C R.B.cx * X + C R.B.c) - (C R.C.cx * X + C R.C.c)

theorem rowBe_natDegree (R : Row F 1) : (rowBe R).natDegree ≤ 1 := by
  unfold rowBe
  compute_degree

theorem rowGa_natDegree (R : Row F 1) : (rowGa R).natDegree ≤ 2 := by
  unfold rowGa
  compute_degree

theorem row_holds_iff_quad (R : Row F 1) (x : F) (w : Fin 1 → F) :
    R.Holds x w ↔ rowAl R * w 0 ^ 2 + (rowBe R).eval x * w 0 + (rowGa R).eval x = 0 := by
  have key : R.A.eval x w * R.B.eval x w - R.C.eval x w
      = rowAl R * w 0 ^ 2 + (rowBe R).eval x * w 0 + (rowGa R).eval x := by
    simp only [Aff.eval, rowAl, rowBe, rowGa, Finset.univ_unique, Fin.default_eq_zero,
      Finset.sum_singleton, eval_add, eval_sub, eval_mul, eval_C, eval_X]
    ring
  rw [Row.Holds, ← sub_eq_zero, key]

theorem system_solutions_eq (S : System F 1 r) :
    S.solutions = quadFamilySolutions (fun j => rowAl (S.row j)) (fun j => rowBe (S.row j))
      (fun j => rowGa (S.row j)) := by
  ext x
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨w 0, fun j => (row_holds_iff_quad _ _ _).1 (hw j)⟩
  · rintro ⟨y, hy⟩
    exact ⟨fun _ => y, fun j => (row_holds_iff_quad _ x (fun _ => y)).2 (hy j)⟩

/-- **A one-witness system accepts at most four values of `x`, or all but at most one.** -/
theorem one_witness_dichotomy [IsAlgClosed F] (S : System F 1 r) :
    AtMostFourRoots S.solutions ∨ CoAtMostOne S.solutions := by
  rw [system_solutions_eq]
  exact quad_family_dichotomy _ _ _ (fun j => rowBe_natDegree _) (fun j => rowGa_natDegree _)

end Solution.Research
