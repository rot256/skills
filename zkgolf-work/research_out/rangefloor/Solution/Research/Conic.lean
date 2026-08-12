/-
  # A range check that does not witness bits at all

  The score-`3` two-bit range check of `Construction.lean` is still built out of
  booleanity rows.  This file gives a *completely different* score-`3` certifier of the
  two-bit range, to show that the optimality result of `Optimality.lean` really does
  quantify over exotic systems, and that the lower bound is not an artefact of assuming
  a bit decomposition.

  Take the four points `(0,0), (1,1), (2,4), (3,9)` on the parabola `w = x ^ 2` in the
  `(x, w)`-plane.  Two degenerate conics of the pencil through them are

  * the pair of lines `01` and `23` : `(w - x) * (w - 5 * x + 6) = 0`,
  * the pair of lines `02` and `13` : `(w - 2 * x) * (w - 4 * x + 3) = 0`,

  each of which is *exactly* one R1CS row (a product of two affine forms).  Their common
  zeros are precisely the four base points, whose `x`-coordinates are `0, 1, 2, 3`.
  One witness, two rows: score `3`, and the witness `w` takes the values `0, 1, 4, 9`
  — it is not a bit, and no bit is ever allocated.
-/
import Solution.Research.Model

namespace Solution.Research

variable {F : Type*} [Field F]

/-- The row `(w - x) * (w - 5 * x + 6) = 0`. -/
def conicRow₁ (F : Type*) [Field F] : Row F 1 where
  A := { cx := -1, cw := fun _ => 1, c := 0 }
  B := { cx := -5, cw := fun _ => 1, c := 6 }
  C := { cx := 0, cw := 0, c := 0 }

/-- The row `(w - 2 * x) * (w - 4 * x + 3) = 0`. -/
def conicRow₂ (F : Type*) [Field F] : Row F 1 where
  A := { cx := -2, cw := fun _ => 1, c := 0 }
  B := { cx := -4, cw := fun _ => 1, c := 3 }
  C := { cx := 0, cw := 0, c := 0 }

/-- One witness, two rows: score `3`. -/
def conicSystem (F : Type*) [Field F] : System F 1 2 where
  row := ![conicRow₁ F, conicRow₂ F]

theorem conicSystem_score : (conicSystem F).score = 3 := rfl

theorem conicSystem_sat_iff (x : F) :
    (conicSystem F).Sat x ↔ ∃ t : F,
      (t - x) * (t - 5 * x + 6) = 0 ∧ (t - 2 * x) * (t - 4 * x + 3) = 0 := by
  constructor
  · rintro ⟨w, hw⟩
    have h1 := hw 0
    have h2 := hw 1
    simp only [conicSystem, Matrix.cons_val_zero, Matrix.cons_val_one,
      conicRow₁, conicRow₂, Row.Holds, Aff.eval, Finset.univ_unique,
      Fin.default_eq_zero, Finset.sum_singleton, Pi.zero_apply, zero_mul,
      add_zero] at h1 h2
    exact ⟨w 0, by linear_combination h1, by linear_combination h2⟩
  · rintro ⟨t, h1, h2⟩
    refine ⟨fun _ => t, ?_⟩
    intro j
    match j with
    | 0 =>
      simp only [conicSystem, Matrix.cons_val_zero, conicRow₁, Row.Holds, Aff.eval,
        Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, Pi.zero_apply,
        zero_mul, add_zero]
      linear_combination h1
    | 1 =>
      simp only [conicSystem, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        conicRow₂, Row.Holds, Aff.eval, Finset.univ_unique, Fin.default_eq_zero,
        Finset.sum_singleton, Pi.zero_apply, zero_mul, add_zero]
      linear_combination h2

theorem mem_rangeSet_two (x : F) :
    x ∈ RangeSet F 2 ↔ x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    interval_cases k
    · left; norm_num
    · right; left; norm_num
    · right; right; left; norm_num
    · right; right; right; norm_num
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨0, by norm_num, by norm_num⟩
    · exact ⟨1, by norm_num, by norm_num⟩
    · exact ⟨2, by norm_num, by norm_num⟩
    · exact ⟨3, by norm_num, by norm_num⟩

/-- **A bit-free two-bit range check of score `3`.**  Valid over any field in which
    `3 ≠ 0` (in characteristic `3` the two middle base points collide and the system
    becomes unsound). -/
theorem conicSystem_certifies (h3 : (3 : F) ≠ 0) : (conicSystem F).Certifies 2 := by
  intro x
  rw [conicSystem_sat_iff, mem_rangeSet_two]
  constructor
  · rintro ⟨t, h1, h2⟩
    rcases mul_eq_zero.1 h1 with e1 | e1 <;> rcases mul_eq_zero.1 h2 with e2 | e2
    · -- `t = x` and `t = 2 * x`
      left
      linear_combination e1 - e2
    · -- `t = x` and `t = 4 * x - 3`
      right; left
      have : 3 * x = 3 * 1 := by linear_combination e1 - e2
      exact mul_left_cancel₀ h3 this
    · -- `t = 5 * x - 6` and `t = 2 * x`
      right; right; left
      have : 3 * x = 3 * 2 := by linear_combination e2 - e1
      exact mul_left_cancel₀ h3 this
    · -- `t = 5 * x - 6` and `t = 4 * x - 3`
      right; right; right
      linear_combination e2 - e1
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨0, by ring, by ring⟩
    · exact ⟨1, by ring, by ring⟩
    · exact ⟨4, by ring, by ring⟩
    · exact ⟨9, by ring, by ring⟩

end Solution.Research
