/-
  # Two witnesses, two rows: the hyperbola normal form

  When the two affine factors of the first row are independent in the witnesses, the
  witness pair can be renamed so that the first row reads `U * V = h(x)` with `deg h ≤ 1`.
  Then `V = h(x)/U` whenever `U ≠ 0`, and the second row turns into a single quartic in
  `U` whose coefficients are polynomials in `x`; the remaining possibility `U = 0` forces
  `h(x) = 0`.  Both pieces are handled by the engines of `Elim.lean`.
-/
import Solution.Research.PairRows

namespace Solution.Research

open Polynomial

variable {F : Type*} [Field F]

/-- **Row one a hyperbola.**  If the first constraint is `U * V = h(x)` with `deg h ≤ 1`,
    the accepted set is small or cofinite. -/
theorem caseHyperbola_smallOrCofinite [IsAlgClosed F] (h : F[X]) (hh : h.natDegree ≤ 1)
    (A B C : PAff F) (hA : A.c.natDegree ≤ 1) (hB : B.c.natDegree ≤ 1) (hC : C.c.natDegree ≤ 1) :
    SmallOrCofinite {x : F | ∃ U V : F, U * V = h.eval x ∧
      A.ev x U V * B.ev x U V = C.ev x U V} 7 := by
  classical
  set a : F := A.cy * B.cy with ha
  set b : F := A.cy * B.cz + A.cz * B.cy with hb
  set d : F := A.cz * B.cz with hd
  set e : F[X] := Polynomial.C A.cy * B.c + Polynomial.C B.cy * A.c - Polynomial.C C.cy with he
  set f : F[X] := Polynomial.C A.cz * B.c + Polynomial.C B.cz * A.c - Polynomial.C C.cz with hf
  set g : F[X] := A.c * B.c - C.c with hg
  set G : F[X] := g + Polynomial.C b * h with hG
  -- the second row, expanded
  have hrow : ∀ x U V : F, (A.ev x U V * B.ev x U V = C.ev x U V) ↔
      a * U ^ 2 + b * (U * V) + d * V ^ 2 + e.eval x * U + f.eval x * V + g.eval x = 0 := by
    intro x U V
    simp only [PAff.ev, ha, hb, hd, he, hf, hg, Polynomial.eval_sub, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_C]
    constructor <;> intro hh' <;> linear_combination hh'
  -- degrees
  have hde : e.natDegree ≤ 1 := deg_sub_le (deg_add_le (deg_C_mul_le hB) (deg_C_mul_le hA))
    (deg_C_le _ _)
  have hdf : f.natDegree ≤ 1 := deg_sub_le (deg_add_le (deg_C_mul_le hB) (deg_C_mul_le hA))
    (deg_C_le _ _)
  have hdg : g.natDegree ≤ 2 := deg_sub_le (deg_mul_le hA hB) (le_trans hC (by norm_num))
  have hdG : G.natDegree ≤ 2 := deg_add_le hdg (le_trans (deg_C_mul_le hh) (by norm_num))
  -- the two pieces
  set T₁ : Set F := quintSetNz ![Polynomial.C d * h ^ 2, f * h, G, e, Polynomial.C a] with hT₁
  set T₀ : Set F := {x : F | h.eval x = 0} ∩
    quintSet ![G, f, Polynomial.C d, 0, 0] with hT₀
  have hsplit : {x : F | ∃ U V : F, U * V = h.eval x ∧
      A.ev x U V * B.ev x U V = C.ev x U V} = T₁ ∪ T₀ := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_union, hT₁, hT₀, quintSetNz, quintSet,
      Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨U, V, hUV, hr⟩
      rw [hrow] at hr
      by_cases hU : U = 0
      · subst hU
        refine Or.inr ⟨by simpa using hUV.symm, V, ?_⟩
        rw [quintEval_explicit]
        simp only [hG, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
          Polynomial.eval_zero]
        have hh0 : h.eval x = 0 := by simpa using hUV.symm
        rw [hh0]
        linear_combination hr
      · refine Or.inl ⟨U, hU, ?_⟩
        rw [quintEval_explicit]
        simp only [hG, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
          Polynomial.eval_pow]
        linear_combination U ^ 2 * hr -
          (b * U ^ 2 + d * (h.eval x + V * U) + f.eval x * U) * hUV
    · rintro (⟨U, hU, hq⟩ | ⟨hh0, V, hq⟩)
      · rw [quintEval_explicit] at hq
        simp only [hG, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
          Polynomial.eval_pow] at hq
        refine ⟨U, h.eval x / U, by field_simp, ?_⟩
        rw [hrow]
        have hkey : U ^ 2 * (a * U ^ 2 + b * (U * (h.eval x / U)) + d * (h.eval x / U) ^ 2 +
            e.eval x * U + f.eval x * (h.eval x / U) + g.eval x) = 0 := by
          field_simp
          linear_combination hq
        exact (mul_eq_zero.1 hkey).resolve_left (pow_ne_zero 2 hU)
      · rw [quintEval_explicit] at hq
        simp only [hG, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
          Polynomial.eval_zero] at hq
        refine ⟨0, V, by simpa using hh0.symm, ?_⟩
        rw [hrow, hh0] at *
        linear_combination hq
  have hb₁ : SmallOrCofinite T₁ 2 := by
    refine quintSetNz_smallOrCofinite _ ?_
    intro i
    fin_cases i
    · have hh2 : (h ^ 2).natDegree ≤ 2 := by
        rw [Polynomial.natDegree_pow]; omega
      exact deg_C_mul_le hh2
    · exact deg_mul_le hdf hh
    · exact hdG
    · exact le_trans hde (by norm_num)
    · exact deg_C_le _ _
  have hb₀ : SmallOrCofinite T₀ 2 := by
    by_cases hh0 : h = 0
    · have : T₀ = quintSet ![G, f, Polynomial.C d, 0, 0] := by
        rw [hT₀, hh0]
        ext x
        simp
      rw [this]
      exact quintSet_smallOrCofinite _ (by simpa using hdG)
    · refine (SmallOrCofinite.of_subset_zeroSet hh0 ?_).mono (le_trans hh (by norm_num))
      intro x hx
      exact hx.1
  refine ((hb₁.union hb₀).congr_set hsplit.symm).mono (by norm_num)

end Solution.Research
