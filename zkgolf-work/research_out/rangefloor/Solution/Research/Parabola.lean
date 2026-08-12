/-
  # Two witnesses, two rows: the parabola normal forms

  When the two affine factors of the first row are *proportional* in the witnesses, the
  witness pair can be renamed so that the first row reads

      U * (k U + t(x)) = γ₀ U + γ₁ V + s(x),      k ≠ 0,  deg t, deg s ≤ 1.

  Two cases arise.  If `γ₁ ≠ 0` the first row determines `V` as a quadratic in `U`, and
  substituting it into the second row leaves a single quartic in `U` — engine 1 applies.
  If `γ₁ = 0` the first row is an equation in `U` alone; the second row is then a
  quadratic in `V` whose solvability is analysed by hand, and the exceptional branches
  are all governed by explicit polynomials in `x` of degree at most four.
-/
import Solution.Research.PairRows

namespace Solution.Research

open Polynomial

variable {F : Type*} [Field F]

/-- **Row one a parabola, with the second witness present.**  If the first constraint is
    `U * (k U + t(x)) = γ₀ U + γ₁ V + s(x)` with `γ₁ ≠ 0`, the accepted set is small or
    cofinite. -/
theorem caseParabolaSolve_smallOrCofinite [IsAlgClosed F] (k g0 g1 : F) (hg1 : g1 ≠ 0)
    (t s : F[X]) (ht : t.natDegree ≤ 1) (hs : s.natDegree ≤ 1) (A B C : PAff F)
    (hA : A.c.natDegree ≤ 1) (hB : B.c.natDegree ≤ 1) (hC : C.c.natDegree ≤ 1) :
    SmallOrCofinite {x : F | ∃ U V : F, U * (k * U + t.eval x) = g0 * U + g1 * V + s.eval x ∧
      A.ev x U V * B.ev x U V = C.ev x U V} 7 := by
  classical
  set a : F := A.cy * B.cy with ha
  set b : F := A.cy * B.cz + A.cz * B.cy with hb
  set d : F := A.cz * B.cz with hd
  set e : F[X] := Polynomial.C A.cy * B.c + Polynomial.C B.cy * A.c - Polynomial.C C.cy with he
  set f : F[X] := Polynomial.C A.cz * B.c + Polynomial.C B.cz * A.c - Polynomial.C C.cz with hf
  set g : F[X] := A.c * B.c - C.c with hg
  set t' : F[X] := t - Polynomial.C g0 with ht'
  set s' : F[X] := -s with hs'
  have hdt : t'.natDegree ≤ 1 := deg_sub_le ht (deg_C_le _ _)
  have hds : s'.natDegree ≤ 1 := by rw [hs', Polynomial.natDegree_neg]; exact hs
  have hde : e.natDegree ≤ 1 :=
    deg_sub_le (deg_add_le (deg_C_mul_le hB) (deg_C_mul_le hA)) (deg_C_le _ _)
  have hdf : f.natDegree ≤ 1 :=
    deg_sub_le (deg_add_le (deg_C_mul_le hB) (deg_C_mul_le hA)) (deg_C_le _ _)
  have hdg : g.natDegree ≤ 2 := deg_sub_le (deg_mul_le hA hB) (le_trans hC (by norm_num))
  have hrow2 : ∀ x U V : F, (A.ev x U V * B.ev x U V = C.ev x U V) ↔
      a * U ^ 2 + b * (U * V) + d * V ^ 2 + e.eval x * U + f.eval x * V + g.eval x = 0 := by
    intro x U V
    simp only [PAff.ev, ha, hb, hd, he, hf, hg, Polynomial.eval_sub, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_C]
    constructor <;> intro hh <;> linear_combination hh
  have hrow1 : ∀ x U V : F, (U * (k * U + t.eval x) = g0 * U + g1 * V + s.eval x) ↔
      g1 * V = k * U ^ 2 + t'.eval x * U + s'.eval x := by
    intro x U V
    simp only [ht', hs', Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_C]
    constructor <;> intro hh <;> linear_combination -hh
  -- the quartic in `U` obtained by eliminating `V`
  set c₀ : F[X] := Polynomial.C d * s' ^ 2 + Polynomial.C g1 * (f * s') +
    Polynomial.C (g1 ^ 2) * g with hc₀
  set c₁ : F[X] := Polynomial.C (b * g1) * s' + Polynomial.C (2 * d) * (t' * s') +
    Polynomial.C (g1 ^ 2) * e + Polynomial.C g1 * (f * t') with hc₁
  set c₂ : F[X] := Polynomial.C (a * g1 ^ 2) + Polynomial.C (b * g1) * t' +
    Polynomial.C d * t' ^ 2 + Polynomial.C (2 * d * k) * s' + Polynomial.C (g1 * k) * f with hc₂
  set c₃ : F[X] := Polynomial.C (b * g1 * k) + Polynomial.C (2 * d * k) * t' with hc₃
  set c₄ : F[X] := Polynomial.C (d * k ^ 2) with hc₄
  have hkey : {x : F | ∃ U V : F, U * (k * U + t.eval x) = g0 * U + g1 * V + s.eval x ∧
      A.ev x U V * B.ev x U V = C.ev x U V} = quintSet ![c₀, c₁, c₂, c₃, c₄] := by
    ext x
    simp only [Set.mem_setOf_eq, quintSet]
    constructor
    · rintro ⟨U, V, h1, h2⟩
      rw [hrow1] at h1
      rw [hrow2] at h2
      refine ⟨U, ?_⟩
      rw [quintEval_explicit]
      simp only [hc₀, hc₁, hc₂, hc₃, hc₄, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_pow]
      linear_combination g1 ^ 2 * h2 -
        (b * g1 * U + d * (k * U ^ 2 + t'.eval x * U + s'.eval x + g1 * V) + f.eval x * g1) * h1
    · rintro ⟨U, hU⟩
      rw [quintEval_explicit] at hU
      simp only [hc₀, hc₁, hc₂, hc₃, hc₄, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_pow] at hU
      refine ⟨U, (k * U ^ 2 + t'.eval x * U + s'.eval x) / g1, ?_, ?_⟩
      · rw [hrow1]
        field_simp
      · rw [hrow2]
        have hsq : g1 ^ 2 * (a * U ^ 2 +
            b * (U * ((k * U ^ 2 + t'.eval x * U + s'.eval x) / g1)) +
            d * ((k * U ^ 2 + t'.eval x * U + s'.eval x) / g1) ^ 2 + e.eval x * U +
            f.eval x * ((k * U ^ 2 + t'.eval x * U + s'.eval x) / g1) + g.eval x) = 0 := by
          field_simp
          linear_combination hU
        exact (mul_eq_zero.1 hsq).resolve_left (pow_ne_zero 2 hg1)
  rw [hkey]
  have hdc₀ : c₀.natDegree ≤ 2 := by
    refine deg_add_le (deg_add_le ?_ ?_) ?_
    · exact deg_C_mul_le (by rw [Polynomial.natDegree_pow]; omega)
    · exact deg_C_mul_le (deg_mul_le hdf hds)
    · exact deg_C_mul_le hdg
  exact (quintSet_smallOrCofinite ![c₀, c₁, c₂, c₃, c₄] (by simpa using hdc₀)).mono (by norm_num)

/-! ## Scalar identities used in the pure-parabola analysis

  All of the following are identities between elements of the field, obtained after
  evaluating the coefficient polynomials at a fixed public input `x`.  Isolating them
  keeps the case analysis below readable. -/

/-- The second root of a quadratic with a known root. -/
theorem parab_quad_other_root {F : Type*} [Field F] (k t s U1 : F) (hk : k ≠ 0)
    (h : k * U1 ^ 2 + t * U1 + s = 0) :
    k * (-t / k - U1) ^ 2 + t * (-t / k - U1) + s = 0 := by
  field_simp
  linear_combination k * h

/-- If both roots of `k U² + t U + s` are roots of `b U + f` too, then `b t = 2 k f`. -/
theorem parab_both_roots_bad {F : Type*} [Field F] (b f t k U1 : F) (hb : b ≠ 0) (hk : k ≠ 0)
    (h1 : b * U1 + f = 0) (h2 : b * (-t / k - U1) + f = 0) : b * t - 2 * k * f = 0 := by
  have hU : U1 - (-t / k - U1) = 0 := by
    have h3 : b * (U1 - (-t / k - U1)) = 0 := by linear_combination h1 - h2
    exact (mul_eq_zero.1 h3).resolve_left hb
  have h2U : 2 * (k * U1) = -t := by
    field_simp at hU
    linear_combination hU
  linear_combination b * h2U - 2 * k * h1

/-- With the quadratic coefficient in `V` vanishing and `b U + f ≠ 0`, the second row can
    be solved for `V`. -/
theorem parab_solve_V {F : Type*} [Field F] (a b e f g U : F) (h : b * U + f ≠ 0) :
    a * U ^ 2 + b * (U * (-(a * U ^ 2 + e * U + g) / (b * U + f))) +
      (0 : F) * (-(a * U ^ 2 + e * U + g) / (b * U + f)) ^ 2 + e * U +
      f * (-(a * U ^ 2 + e * U + g) / (b * U + f)) + g = 0 := by
  have hc : (b * U + f) * (-(a * U ^ 2 + e * U + g) / (b * U + f)) =
      -(a * U ^ 2 + e * U + g) := by field_simp
  linear_combination hc

/-- The same when also `b = 0` and `f ≠ 0`. -/
theorem parab_solve_V_b0 {F : Type*} [Field F] (a e f g U : F) (hf : f ≠ 0) :
    a * U ^ 2 + (0 : F) * (U * (-(a * U ^ 2 + e * U + g) / f)) +
      (0 : F) * (-(a * U ^ 2 + e * U + g) / f) ^ 2 + e * U +
      f * (-(a * U ^ 2 + e * U + g) / f) + g = 0 := by
  field_simp
  ring

/-- If `b t = 2 k f` and the quadratic has a root on the line `b U + f = 0`, then also
    `b² s = k f²`. -/
theorem parab_bs_of_root {F : Type*} [Field F] (b f t s k U : F) (hb : b ≠ 0)
    (hbt : b * t = 2 * k * f) (hq : k * U ^ 2 + t * U + s = 0) (hU : b * U + f = 0) :
    b ^ 2 * s = k * f ^ 2 := by
  have hUv : U = -f / b := by field_simp; linear_combination hU
  subst hUv
  field_simp at hq
  linear_combination hq + f * hbt

/-- If `b t = 2 k f` and `b² s = k f²` then `b² (k U² + t U + s) = k (b U + f)²`, so every
    root of the quadratic lies on the line `b U + f = 0`. -/
theorem parab_k_sq_zero {F : Type*} [Field F] (b f t s k U : F) (hbt : b * t = 2 * k * f)
    (hbs : b ^ 2 * s = k * f ^ 2) (hq : k * U ^ 2 + t * U + s = 0) :
    k * (b * U + f) ^ 2 = 0 := by
  linear_combination b ^ 2 * hq - b * U * hbt - hbs

/-- On the line `b U + f = 0` the second row forces the vanishing of `a f² - b e f + b² g`. -/
theorem parab_psi_of_row2 {F : Type*} [Field F] (a b e f g U V : F) (hU : b * U + f = 0)
    (h2 : a * U ^ 2 + b * (U * V) + (0 : F) * V ^ 2 + e * U + f * V + g = 0) :
    a * f ^ 2 - b * (e * f) + b ^ 2 * g = 0 := by
  linear_combination b ^ 2 * h2 - (b ^ 2 * V + a * (b * U) - a * f + b * e) * hU

/-- Conversely, `U = -f/b` is a root of the quadratic once `b t = 2 k f`, `b² s = k f²`. -/
theorem parab_row1_at_root {F : Type*} [Field F] (b f t s k : F) (hb : b ≠ 0)
    (hbt : b * t = 2 * k * f) (hbs : b ^ 2 * s = k * f ^ 2) :
    k * (-f / b) ^ 2 + t * (-f / b) + s = 0 := by
  field_simp
  linear_combination -f * hbt + hbs

/-- … and `(U, V) = (-f/b, 0)` satisfies the second row once `a f² - b e f + b² g = 0`. -/
theorem parab_row2_at_root {F : Type*} [Field F] (a b e f g : F) (hb : b ≠ 0)
    (hPsi : a * f ^ 2 - b * (e * f) + b ^ 2 * g = 0) :
    a * (-f / b) ^ 2 + b * ((-f / b) * (0 : F)) + (0 : F) * (0 : F) ^ 2 + e * (-f / b) +
      f * (0 : F) + g = 0 := by
  field_simp
  linear_combination hPsi

/-- Two quadratics in `U` with a common root: the resultant-like polynomial vanishes. -/
theorem parab_Pi_of_roots {F : Type*} [Field F] (a e g k t s U lam mu : F)
    (hlam : lam = a * t - k * e) (hmu : mu = a * s - k * g)
    (hQ : k * U ^ 2 + t * U + s = 0) (hR : a * U ^ 2 + e * U + g = 0) :
    k * mu ^ 2 - t * (mu * lam) + s * lam ^ 2 = 0 := by
  have hlin : lam * U + mu = 0 := by rw [hlam, hmu]; linear_combination a * hQ - k * hR
  linear_combination lam ^ 2 * hQ + (k * (mu - lam * U) - t * lam) * hlin

/-- Conversely, if that polynomial vanishes and `lam ≠ 0`, then `-mu/lam` is a root. -/
theorem parab_root_of_Pi {F : Type*} [Field F] (k t s lam mu : F) (hlam : lam ≠ 0)
    (hPi : k * mu ^ 2 - t * (mu * lam) + s * lam ^ 2 = 0) :
    k * (-mu / lam) ^ 2 + t * (-mu / lam) + s = 0 := by
  field_simp
  linear_combination hPi

/-- A root of the first quadratic on the line `lam U + mu = 0` is a root of the second. -/
theorem parab_R_of_Q {F : Type*} [Field F] (a e g k t s U lam mu : F) (hk : k ≠ 0)
    (hlam : lam = a * t - k * e) (hmu : mu = a * s - k * g) (hlin : lam * U + mu = 0)
    (hQ : k * U ^ 2 + t * U + s = 0) : a * U ^ 2 + e * U + g = 0 := by
  have hkR : k * (a * U ^ 2 + e * U + g) = 0 := by
    rw [hlam, hmu] at hlin; linear_combination a * hQ - hlin
  exact (mul_eq_zero.1 hkR).resolve_left hk

/-- **Row one a parabola in the first witness alone.**  If the first constraint is
    `U * (k U + t(x)) = γ₀ U + s(x)` with `k ≠ 0`, the accepted set is small or
    cofinite. -/
theorem caseParabolaPure_smallOrCofinite [IsAlgClosed F] (k g0 : F) (hk : k ≠ 0)
    (t s : F[X]) (ht : t.natDegree ≤ 1) (hs : s.natDegree ≤ 1) (A B C : PAff F)
    (hA : A.c.natDegree ≤ 1) (hB : B.c.natDegree ≤ 1) (hC : C.c.natDegree ≤ 1) :
    SmallOrCofinite {x : F | ∃ U V : F, U * (k * U + t.eval x) = g0 * U + s.eval x ∧
      A.ev x U V * B.ev x U V = C.ev x U V} 7 := by
  classical
  set a : F := A.cy * B.cy with ha
  set b : F := A.cy * B.cz + A.cz * B.cy with hb
  set d : F := A.cz * B.cz with hd
  set e : F[X] := Polynomial.C A.cy * B.c + Polynomial.C B.cy * A.c - Polynomial.C C.cy with he
  set f : F[X] := Polynomial.C A.cz * B.c + Polynomial.C B.cz * A.c - Polynomial.C C.cz with hf
  set g : F[X] := A.c * B.c - C.c with hg
  set t' : F[X] := t - Polynomial.C g0 with ht'
  set s' : F[X] := -s with hs'
  have hdt : t'.natDegree ≤ 1 := deg_sub_le ht (deg_C_le _ _)
  have hds : s'.natDegree ≤ 1 := by rw [hs', Polynomial.natDegree_neg]; exact hs
  have hde : e.natDegree ≤ 1 :=
    deg_sub_le (deg_add_le (deg_C_mul_le hB) (deg_C_mul_le hA)) (deg_C_le _ _)
  have hdf : f.natDegree ≤ 1 :=
    deg_sub_le (deg_add_le (deg_C_mul_le hB) (deg_C_mul_le hA)) (deg_C_le _ _)
  have hdg : g.natDegree ≤ 2 := deg_sub_le (deg_mul_le hA hB) (le_trans hC (by norm_num))
  have hrow2 : ∀ x U V : F, (A.ev x U V * B.ev x U V = C.ev x U V) ↔
      a * U ^ 2 + b * (U * V) + d * V ^ 2 + e.eval x * U + f.eval x * V + g.eval x = 0 := by
    intro x U V
    simp only [PAff.ev, ha, hb, hd, he, hf, hg, Polynomial.eval_sub, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_C]
    constructor <;> intro hh <;> linear_combination hh
  have hrow1 : ∀ x U : F, (U * (k * U + t.eval x) = g0 * U + s.eval x) ↔
      k * U ^ 2 + t'.eval x * U + s'.eval x = 0 := by
    intro x U
    simp only [ht', hs', Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_C]
    constructor <;> intro hh <;> linear_combination hh
  set T : Set F := {x : F | ∃ U V : F, k * U ^ 2 + t'.eval x * U + s'.eval x = 0 ∧
      a * U ^ 2 + b * (U * V) + d * V ^ 2 + e.eval x * U + f.eval x * V + g.eval x = 0} with hT
  have hTeq : {x : F | ∃ U V : F, U * (k * U + t.eval x) = g0 * U + s.eval x ∧
      A.ev x U V * B.ev x U V = C.ev x U V} = T := by
    ext x
    simp only [Set.mem_setOf_eq, hT]
    constructor
    · rintro ⟨U, V, h1, h2⟩
      exact ⟨U, V, (hrow1 x U).1 h1, (hrow2 x U V).1 h2⟩
    · rintro ⟨U, V, h1, h2⟩
      exact ⟨U, V, (hrow1 x U).2 h1, (hrow2 x U V).2 h2⟩
  rw [hTeq]
  by_cases hd0 : d ≠ 0
  · -- the second row is a genuine quadratic in `V`: every `x` is accepted
    refine SmallOrCofinite.of_compl_finite ?_ 7
    have huniv : T = Set.univ := by
      ext x
      simp only [Set.mem_univ, iff_true, hT, Set.mem_setOf_eq]
      obtain ⟨U, hU⟩ := exists_quad_root k (t'.eval x) (s'.eval x) hk
      obtain ⟨V, hV⟩ := exists_quad_root d (b * U + f.eval x)
        (a * U ^ 2 + e.eval x * U + g.eval x) hd0
      exact ⟨U, V, hU, by linear_combination hV⟩
    rw [huniv]
    simp
  · push_neg at hd0
    by_cases hb0 : b ≠ 0
    · -- `V` occurs linearly, with coefficient `b U + f`
      set L1 : F[X] := Polynomial.C b * t' - Polynomial.C (2 * k) * f with hL1
      set L2 : F[X] := Polynomial.C (b ^ 2) * s' - Polynomial.C k * f ^ 2 with hL2
      have hL1ev : ∀ x : F, L1.eval x = b * t'.eval x - 2 * k * f.eval x := by
        intro x
        simp only [hL1, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C]
      have hL2ev : ∀ x : F, L2.eval x = b ^ 2 * s'.eval x - k * f.eval x ^ 2 := by
        intro x
        simp only [hL2, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
          Polynomial.eval_pow]
      have hsol : ∀ x U : F, k * U ^ 2 + t'.eval x * U + s'.eval x = 0 →
          b * U + f.eval x ≠ 0 → x ∈ T := by
        intro x U hU hbU
        refine ⟨U, -(a * U ^ 2 + e.eval x * U + g.eval x) / (b * U + f.eval x), hU, ?_⟩
        rw [hd0]
        exact parab_solve_V a b (e.eval x) (f.eval x) (g.eval x) U hbU
      by_cases hL10 : L1 ≠ 0
      · refine SmallOrCofinite.of_compl_subset_zeroSet hL10 ?_ 7
        intro x hx
        by_contra hne
        refine hx ?_
        obtain ⟨U1, hU1⟩ := exists_quad_root k (t'.eval x) (s'.eval x) hk
        by_cases hbU1 : b * U1 + f.eval x ≠ 0
        · exact hsol x U1 hU1 hbU1
        · push_neg at hbU1
          have hU2 := parab_quad_other_root k (t'.eval x) (s'.eval x) U1 hk hU1
          by_cases hbU2 : b * (-(t'.eval x) / k - U1) + f.eval x ≠ 0
          · exact hsol x _ hU2 hbU2
          · push_neg at hbU2
            refine absurd ?_ hne
            rw [hL1ev]
            exact parab_both_roots_bad b (f.eval x) (t'.eval x) k U1 hb0 hk hbU1 hbU2
      · push_neg at hL10
        have hbt : ∀ x : F, b * t'.eval x = 2 * k * f.eval x := by
          intro x
          have h0 : L1.eval x = 0 := by rw [hL10]; simp
          rw [hL1ev] at h0
          linear_combination h0
        by_cases hL20 : L2 ≠ 0
        · refine SmallOrCofinite.of_compl_subset_zeroSet hL20 ?_ 7
          intro x hx
          by_contra hne
          refine hx ?_
          obtain ⟨U, hU⟩ := exists_quad_root k (t'.eval x) (s'.eval x) hk
          refine hsol x U hU ?_
          intro hcon
          refine hne ?_
          rw [hL2ev]
          have hbs := parab_bs_of_root b (f.eval x) (t'.eval x) (s'.eval x) k U hb0 (hbt x) hU hcon
          linear_combination hbs
        · push_neg at hL20
          -- the first row forces `U = -f/b`, and the second row becomes a condition on `x`
          have hbs : ∀ x : F, b ^ 2 * s'.eval x = k * f.eval x ^ 2 := by
            intro x
            have h0 : L2.eval x = 0 := by rw [hL20]; simp
            rw [hL2ev] at h0
            linear_combination h0
          set Psi : F[X] := Polynomial.C a * f ^ 2 - Polynomial.C b * (e * f) +
            Polynomial.C (b ^ 2) * g with hPsi
          have hPsiev : ∀ x : F, Psi.eval x =
              a * f.eval x ^ 2 - b * (e.eval x * f.eval x) + b ^ 2 * g.eval x := by
            intro x
            simp only [hPsi, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
              Polynomial.eval_C, Polynomial.eval_pow]
          have hTZ : T = {x : F | Psi.eval x = 0} := by
            ext x
            simp only [hT, Set.mem_setOf_eq]
            constructor
            · rintro ⟨U, V, h1, h2⟩
              have hfac :=
                parab_k_sq_zero b (f.eval x) (t'.eval x) (s'.eval x) k U (hbt x) (hbs x) h1
              have hbU : b * U + f.eval x = 0 := by
                have h3 := (mul_eq_zero.1 hfac).resolve_left hk
                exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h3
              rw [hd0] at h2
              rw [hPsiev]
              exact parab_psi_of_row2 a b (e.eval x) (f.eval x) (g.eval x) U V hbU h2
            · intro hx
              rw [hPsiev] at hx
              refine ⟨-f.eval x / b, 0, ?_, ?_⟩
              · exact parab_row1_at_root b (f.eval x) (t'.eval x) (s'.eval x) k hb0 (hbt x) (hbs x)
              · rw [hd0]
                exact parab_row2_at_root a b (e.eval x) (f.eval x) (g.eval x) hb0 hx
          rw [hTZ]
          refine (SmallOrCofinite.zeroSet Psi).mono ?_
          rw [hPsi]
          have k1 : (Polynomial.C a * f ^ 2).natDegree ≤ 2 :=
            deg_C_mul_le (by rw [Polynomial.natDegree_pow]; omega)
          have k2 : (Polynomial.C b * (e * f)).natDegree ≤ 2 :=
            deg_C_mul_le (deg_mul_le hde hdf)
          have k3 : (Polynomial.C (b ^ 2) * g).natDegree ≤ 2 := deg_C_mul_le hdg
          exact le_trans (deg_add_le (deg_sub_le k1 k2) k3) (by norm_num)
    · push_neg at hb0
      by_cases hf0 : f ≠ 0
      · refine SmallOrCofinite.of_compl_subset_zeroSet hf0 ?_ 7
        intro x hx
        by_contra hne
        refine hx ?_
        obtain ⟨U, hU⟩ := exists_quad_root k (t'.eval x) (s'.eval x) hk
        refine ⟨U, -(a * U ^ 2 + e.eval x * U + g.eval x) / f.eval x, hU, ?_⟩
        rw [hd0, hb0]
        exact parab_solve_V_b0 a (e.eval x) (f.eval x) (g.eval x) U hne
      · push_neg at hf0
        -- the two rows are two quadratics in `U`
        set lam : F[X] := Polynomial.C a * t' - Polynomial.C k * e with hlam
        set mu : F[X] := Polynomial.C a * s' - Polynomial.C k * g with hmu
        have hlamev : ∀ x : F, lam.eval x = a * t'.eval x - k * e.eval x := by
          intro x
          simp only [hlam, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C]
        have hmuev : ∀ x : F, mu.eval x = a * s'.eval x - k * g.eval x := by
          intro x
          simp only [hmu, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C]
        have hdlam : lam.natDegree ≤ 1 := by
          rw [hlam]; exact deg_sub_le (deg_C_mul_le hdt) (deg_C_mul_le hde)
        have hdmu : mu.natDegree ≤ 2 := by
          rw [hmu]
          exact deg_sub_le (le_trans (deg_C_mul_le hds) (by norm_num)) (deg_C_mul_le hdg)
        set R : Set F := {x : F | ∃ U : F, k * U ^ 2 + t'.eval x * U + s'.eval x = 0 ∧
            a * U ^ 2 + e.eval x * U + g.eval x = 0} with hR
        have hTR : T = R := by
          ext x
          simp only [hT, hR, Set.mem_setOf_eq]
          constructor
          · rintro ⟨U, V, h1, h2⟩
            rw [hd0, hb0, hf0] at h2
            exact ⟨U, h1, by simpa using h2⟩
          · rintro ⟨U, h1, h2⟩
            refine ⟨U, 0, h1, ?_⟩
            rw [hd0, hb0, hf0]
            simpa using h2
        rw [hTR]
        by_cases hlam0 : lam ≠ 0
        · set Pi : F[X] := Polynomial.C k * mu ^ 2 - t' * (mu * lam) + s' * lam ^ 2 with hPi
          have hPiev : ∀ x : F, Pi.eval x = k * mu.eval x ^ 2 -
              t'.eval x * (mu.eval x * lam.eval x) + s'.eval x * lam.eval x ^ 2 := by
            intro x
            simp only [hPi, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
              Polynomial.eval_C, Polynomial.eval_pow]
          have hkey : R ∩ {x : F | lam.eval x ≠ 0} =
              {x : F | Pi.eval x = 0} ∩ {x : F | lam.eval x ≠ 0} := by
            ext x
            simp only [hR, Set.mem_inter_iff, Set.mem_setOf_eq]
            constructor
            · rintro ⟨⟨U, hQ, hRr⟩, hlx⟩
              refine ⟨?_, hlx⟩
              rw [hPiev]
              exact parab_Pi_of_roots a (e.eval x) (g.eval x) k (t'.eval x) (s'.eval x) U
                (lam.eval x) (mu.eval x) (hlamev x) (hmuev x) hQ hRr
            · rintro ⟨hPx, hlx⟩
              rw [hPiev] at hPx
              have hroot := parab_root_of_Pi k (t'.eval x) (s'.eval x) (lam.eval x) (mu.eval x)
                hlx hPx
              refine ⟨⟨-mu.eval x / lam.eval x, hroot, ?_⟩, hlx⟩
              refine parab_R_of_Q a (e.eval x) (g.eval x) k (t'.eval x) (s'.eval x) _
                (lam.eval x) (mu.eval x) hk (hlamev x) (hmuev x) ?_ hroot
              field_simp
              ring
          have hdPi : Pi.natDegree ≤ 4 := by
            rw [hPi]
            refine deg_add_le (deg_sub_le ?_ ?_) ?_
            · exact deg_C_mul_le (by rw [Polynomial.natDegree_pow]; omega)
            · exact le_trans (deg_mul_le hdt (deg_mul_le hdmu hdlam)) (by norm_num)
            · exact le_trans (deg_mul_le hds (show (lam ^ 2).natDegree ≤ 2 by
                rw [Polynomial.natDegree_pow]; omega)) (by norm_num)
          have h1 : SmallOrCofinite (R ∩ {x : F | lam.eval x ≠ 0}) 4 := by
            rw [hkey]
            exact ((SmallOrCofinite.zeroSet Pi).mono hdPi).inter_nonzero hlam0
          have h2 : SmallOrCofinite (R ∩ {x : F | lam.eval x = 0}) 1 :=
            (SmallOrCofinite.of_subset_zeroSet hlam0 (fun x hx => hx.2)).mono hdlam
          refine ((h1.union h2).congr_set ?_).mono (by norm_num)
          ext x
          by_cases hx : lam.eval x = 0 <;> simp [hx]
        · push_neg at hlam0
          have hlx : ∀ x : F, lam.eval x = 0 := by
            intro x; rw [hlam0]; simp
          have hTmu : R = {x : F | mu.eval x = 0} := by
            ext x
            simp only [hR, Set.mem_setOf_eq]
            constructor
            · rintro ⟨U, hQ, hRr⟩
              have hlin : lam.eval x * U + mu.eval x = 0 := by
                rw [hlamev x, hmuev x]
                linear_combination a * hQ - k * hRr
              rw [hlx x] at hlin
              linear_combination hlin
            · intro hx
              obtain ⟨U, hU⟩ := exists_quad_root k (t'.eval x) (s'.eval x) hk
              refine ⟨U, hU, ?_⟩
              refine parab_R_of_Q a (e.eval x) (g.eval x) k (t'.eval x) (s'.eval x) U
                (lam.eval x) (mu.eval x) hk (hlamev x) (hmuev x) ?_ hU
              rw [hlx x, hx]
              ring
          rw [hTmu]
          exact (SmallOrCofinite.zeroSet mu).mono (le_trans hdmu (by norm_num))

end Solution.Research
