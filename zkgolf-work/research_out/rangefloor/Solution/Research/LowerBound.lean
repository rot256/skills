/-
  # Lower bounds

  What can a *cheap* system do?  The results here quantify over **arbitrary** systems:
  arbitrary affine forms, arbitrary field-element witnesses, nothing is assumed about
  bits or about how the witnesses are used.

  * `Row.zero_rows_solutions` : with no rows every `x` is accepted.
  * `one_row_dichotomy` : a **single** row, over **any** number of witnesses, accepts
    either at most two values of `x`, or all but at most one value of `x`.  So one row
    can never certify more than one bit, however many witnesses it is given.
  * `zero_witness_dichotomy` : with **no** witnesses, any number of rows accepts either
    at most two values of `x` or all of them.

  Combining these: over an algebraically closed field of characteristic zero, no system
  of score `≤ 2` certifies a `2`-bit range, so the score-`3` construction of
  `Solution.Research.Construction` is optimal for `n = 2`.
-/
import Solution.Research.Model

namespace Solution.Research

open Polynomial

variable {F : Type*} [Field F] {m r : ℕ}

/-- The set `S` has at most two elements. -/
def AtMostTwo (S : Set F) : Prop := ∃ a b : F, S ⊆ {a, b}

/-- The set `S` omits at most one element of `F`. -/
def CoAtMostOne (S : Set F) : Prop := ∃ a : F, ∀ x : F, x ≠ a → x ∈ S

/-! ## Elementary field facts -/

/-- A not-identically-zero quadratic has at most two roots. -/
theorem quad_atMostTwo (a b c : F) (h : ¬(a = 0 ∧ b = 0 ∧ c = 0)) :
    AtMostTwo {x : F | a * x ^ 2 + b * x + c = 0} := by
  classical
  by_cases hS : ∃ x0 : F, a * x0 ^ 2 + b * x0 + c = 0
  · obtain ⟨x0, hx0⟩ := hS
    by_cases ha : a = 0
    · subst ha
      have hb : b ≠ 0 := by
        rintro rfl
        exact h ⟨rfl, rfl, by simpa using hx0⟩
      refine ⟨x0, x0, ?_⟩
      intro x hx
      simp only [Set.mem_setOf_eq, zero_mul, zero_add] at hx
      have hfac : b * (x - x0) = 0 := by linear_combination hx - hx0
      rcases mul_eq_zero.1 hfac with h' | h'
      · exact absurd h' hb
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        left
        linear_combination h'
    · refine ⟨x0, -(b + a * x0) / a, ?_⟩
      intro x hx
      simp only [Set.mem_setOf_eq] at hx
      have key : (x - x0) * (a * (x + x0) + b) = 0 := by linear_combination hx - hx0
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rcases mul_eq_zero.1 key with h' | h'
      · left; linear_combination h'
      · right
        field_simp
        linear_combination h'
  · push_neg at hS
    exact ⟨0, 0, fun x hx => absurd hx (hS x)⟩

/-- A nonzero linear functional on `Fin m → F` is surjective. -/
theorem exists_dot_eq (u : Fin m → F) (hu : u ≠ 0) (t : F) :
    ∃ w : Fin m → F, ∑ i, u i * w i = t := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, u j ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hu (funext hc)
  refine ⟨Pi.single j (t / u j), ?_⟩
  rw [Finset.sum_eq_single j]
  · simp only [Pi.single_eq_same]
    field_simp
  · intro i _ hij
    simp [Ne.symm hij]
  · intro hj'
    simp at hj'

/-- Two nonzero functionals have a common vector on which neither vanishes
    (over an infinite field). -/
theorem exists_dot_ne_zero_two [Infinite F] (u1 u2 : Fin m → F) (h1 : u1 ≠ 0) (h2 : u2 ≠ 0) :
    ∃ v : Fin m → F, (∑ i, u1 i * v i) ≠ 0 ∧ (∑ i, u2 i * v i) ≠ 0 := by
  classical
  obtain ⟨j1, hj1⟩ : ∃ j, u1 j ≠ 0 := by
    by_contra hc; push_neg at hc; exact h1 (funext hc)
  obtain ⟨j2, hj2⟩ : ∃ j, u2 j ≠ 0 := by
    by_contra hc; push_neg at hc; exact h2 (funext hc)
  have dot_single : ∀ (u : Fin m → F) (j : Fin m) (c : F),
      ∑ i, u i * (Pi.single j c : Fin m → F) i = u j * c := by
    intro u j c
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij; simp [Ne.symm hij]
    · intro hj'; simp at hj'
  have dot_add : ∀ (u : Fin m → F) (v v' : Fin m → F),
      ∑ i, u i * (v i + v' i) = (∑ i, u i * v i) + ∑ i, u i * v' i := by
    intro u v v'
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  by_cases hb : u2 j1 = 0
  · -- then `j1 ≠ j2`; use `e_{j1} + c • e_{j2}` for a suitable `c`
    have hcex : ∃ c : F, c ≠ 0 ∧ u1 j1 + c * u1 j2 ≠ 0 := by
      by_cases hz : u1 j2 = 0
      · exact ⟨1, one_ne_zero, by simp [hz, hj1]⟩
      · obtain ⟨c, hc0, hc1⟩ : ∃ c : F, c ≠ 0 ∧ c ≠ -(u1 j1) / u1 j2 := by
          have hne : ({(0 : F), -(u1 j1) / u1 j2} : Set F) ≠ Set.univ := by
            intro hEq
            have hi := Set.infinite_univ (α := F)
            rw [← hEq] at hi
            exact hi (Set.toFinite _)
          obtain ⟨c, hc⟩ := Set.ne_univ_iff_exists_notMem _ |>.mp hne
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hc
          exact ⟨c, hc.1, hc.2⟩
        refine ⟨c, hc0, ?_⟩
        intro hzero
        apply hc1
        field_simp
        linear_combination hzero
    obtain ⟨c, hc0, hc1⟩ := hcex
    refine ⟨fun i => (Pi.single j1 (1 : F) : Fin m → F) i + (Pi.single j2 c : Fin m → F) i, ?_, ?_⟩
    · rw [dot_add, dot_single, dot_single]
      intro hzero
      exact hc1 (by linear_combination hzero)
    · rw [dot_add, dot_single, dot_single]
      simp [hb, mul_ne_zero hj2 hc0]
  · exact ⟨Pi.single j1 1, by simpa [dot_single] using hj1, by simpa [dot_single] using hb⟩

/-- Over an algebraically closed field every quadratic with nonzero leading coefficient
    has a root. -/
theorem exists_quad_root [IsAlgClosed F] (a b c : F) (ha : a ≠ 0) :
    ∃ t : F, a * t ^ 2 + b * t + c = 0 := by
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_root (C a * X ^ 2 + C b * X + C c)
    (by rw [degree_quadratic ha]; decide)
  exact ⟨t, by simpa [IsRoot, eval_add, eval_mul] using ht⟩

/-! ## Analysis of a single row -/

/-- Value of a row's affine forms in terms of the `x`-part and the witness part. -/
theorem Aff.eval_split (L : Aff F m) (x : F) (w : Fin m → F) :
    L.eval x w = (L.cx * x + L.c) + ∑ i, L.cw i * w i := by
  simp [Aff.eval]; ring

/-- The solution set of a single row. -/
def rowSolutions (R : Row F m) : Set F := {x : F | ∃ w, R.Holds x w}

/-- A row in which no witness occurs at all is a univariate quadratic condition. -/
theorem quad_row_dichotomy (R : Row F m) (h1 : R.A.cw = 0) (h2 : R.B.cw = 0) (h3 : R.C.cw = 0) :
    AtMostTwo (rowSolutions R) ∨ rowSolutions R = Set.univ := by
  classical
  have hA : ∀ x w, R.A.eval x w = R.A.cx * x + R.A.c := by
    intro x w; rw [Aff.eval_split]; simp [h1]
  have hB : ∀ x w, R.B.eval x w = R.B.cx * x + R.B.c := by
    intro x w; rw [Aff.eval_split]; simp [h2]
  -- pure quadratic condition on `x`
  have hC : ∀ x w, R.C.eval x w = R.C.cx * x + R.C.c := by
    intro x w; rw [Aff.eval_split]; simp [h3]
  set a := R.A.cx * R.B.cx with hadef
  set b := R.A.cx * R.B.c + R.A.c * R.B.cx - R.C.cx with hbdef
  set c := R.A.c * R.B.c - R.C.c with hcdef
  have hiff : ∀ x : F, x ∈ rowSolutions R ↔ a * x ^ 2 + b * x + c = 0 := by
    intro x
    constructor
    · rintro ⟨w, hw⟩
      rw [Row.Holds, hA, hB, hC] at hw
      simp only [hadef, hbdef, hcdef]
      linear_combination hw
    · intro hx
      refine ⟨0, ?_⟩
      rw [Row.Holds, hA, hB, hC]
      simp only [hadef, hbdef, hcdef] at hx
      linear_combination hx
  by_cases habc : a = 0 ∧ b = 0 ∧ c = 0
  · right
    ext x
    simp only [Set.mem_univ, iff_true]
    rw [hiff]
    simp [habc.1, habc.2.1, habc.2.2]
  · left
    obtain ⟨p, q, hpq⟩ := quad_atMostTwo a b c habc
    exact ⟨p, q, fun x hx => hpq ((hiff x).1 hx)⟩

/-- A row whose two factors both have zero witness part. -/
theorem one_row_both_const (R : Row F m) (h1 : R.A.cw = 0) (h2 : R.B.cw = 0) :
    AtMostTwo (rowSolutions R) ∨ CoAtMostOne (rowSolutions R) := by
  classical
  have hA : ∀ x w, R.A.eval x w = R.A.cx * x + R.A.c := by
    intro x w; rw [Aff.eval_split]; simp [h1]
  have hB : ∀ x w, R.B.eval x w = R.B.cx * x + R.B.c := by
    intro x w; rw [Aff.eval_split]; simp [h2]
  by_cases h3 : R.C.cw = 0
  · rcases quad_row_dichotomy R h1 h2 h3 with h | h
    · exact Or.inl h
    · exact Or.inr ⟨0, fun x _ => by rw [h]; trivial⟩
  · -- the right-hand side has a free witness direction: everything is satisfiable
    right
    refine ⟨0, fun x _ => ?_⟩
    obtain ⟨w, hw⟩ := exists_dot_eq R.C.cw h3
      ((R.A.cx * x + R.A.c) * (R.B.cx * x + R.B.c) - (R.C.cx * x + R.C.c))
    refine ⟨w, ?_⟩
    rw [Row.Holds, hA, hB, Aff.eval_split, hw]
    ring

/-- A row whose left factor has a nonzero witness part and whose right factor does not. -/
theorem one_row_left_only (R : Row F m) (h1 : R.A.cw ≠ 0) (h2 : R.B.cw = 0) :
    AtMostTwo (rowSolutions R) ∨ CoAtMostOne (rowSolutions R) := by
  classical
  have hB : ∀ x w, R.B.eval x w = R.B.cx * x + R.B.c := by
    intro x w; rw [Aff.eval_split]; simp [h2]
  -- with `b(x) := R.B.cx * x + R.B.c`, the row says
  -- `⟨b(x) • A.cw - C.cw, w⟩ = C-part(x) - A-part(x) * b(x)`
  have key : ∀ x : F, (fun i => (R.B.cx * x + R.B.c) * R.A.cw i - R.C.cw i) ≠ 0 →
      x ∈ rowSolutions R := by
    intro x hx
    obtain ⟨w, hw⟩ := exists_dot_eq _ hx
      ((R.C.cx * x + R.C.c) - (R.A.cx * x + R.A.c) * (R.B.cx * x + R.B.c))
    refine ⟨w, ?_⟩
    rw [Row.Holds, hB, Aff.eval_split, Aff.eval_split]
    have hsum : ∑ i, ((R.B.cx * x + R.B.c) * R.A.cw i - R.C.cw i) * w i
        = (R.B.cx * x + R.B.c) * (∑ i, R.A.cw i * w i) - ∑ i, R.C.cw i * w i := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hsum] at hw
    linear_combination hw
  obtain ⟨j, hj⟩ : ∃ j, R.A.cw j ≠ 0 := by
    by_contra hc; push_neg at hc; exact h1 (funext hc)
  by_cases hbx : R.B.cx = 0
  · -- `b` is the constant `R.B.c`
    by_cases hconst : (fun i => R.B.c * R.A.cw i - R.C.cw i) = 0
    · -- the row degenerates to an affine condition on `x`
      have hiff : ∀ x : F, x ∈ rowSolutions R ↔
          0 * x ^ 2 + (R.A.cx * R.B.c - R.C.cx) * x + (R.A.c * R.B.c - R.C.c) = 0 := by
        intro x
        have hCcw : ∀ w : Fin m → F, ∑ i, R.C.cw i * w i
            = R.B.c * ∑ i, R.A.cw i * w i := by
          intro w
          have : ∀ i, R.C.cw i = R.B.c * R.A.cw i := by
            intro i
            have := congrFun hconst i
            simp only [Pi.zero_apply, sub_eq_zero] at this
            exact this.symm
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by rw [this i]; ring
        constructor
        · rintro ⟨w, hw⟩
          rw [Row.Holds, hB, hbx, Aff.eval_split, Aff.eval_split, hCcw w] at hw
          linear_combination hw
        · intro hx
          refine ⟨0, ?_⟩
          rw [Row.Holds, hB, hbx, Aff.eval_split, Aff.eval_split]
          simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
          linear_combination hx
      by_cases hz : (0 : F) = 0 ∧ (R.A.cx * R.B.c - R.C.cx) = 0 ∧ (R.A.c * R.B.c - R.C.c) = 0
      · right
        refine ⟨0, fun x _ => ?_⟩
        rw [hiff]
        simp [hz.2.1, hz.2.2]
      · left
        obtain ⟨p, q, hpq⟩ := quad_atMostTwo (0 : F) (R.A.cx * R.B.c - R.C.cx)
          (R.A.c * R.B.c - R.C.c) hz
        exact ⟨p, q, fun x hx => hpq ((hiff x).1 hx)⟩
    · -- every `x` is accepted
      right
      refine ⟨0, fun x _ => key x ?_⟩
      simpa [hbx] using hconst
  · -- `b` is a nonconstant affine function: at most one bad `x`
    right
    refine ⟨(R.C.cw j / R.A.cw j - R.B.c) / R.B.cx, fun x hxne => key x ?_⟩
    intro hbad
    apply hxne
    have hjj := congrFun hbad j
    simp only [Pi.zero_apply, sub_eq_zero] at hjj
    have hb : R.B.cx * x + R.B.c = R.C.cw j / R.A.cw j := by
      rw [eq_div_iff hj]
      linear_combination hjj
    rw [eq_div_iff hbx]
    linear_combination hb

/-- **One row can certify at most one bit.**  Whatever the number `m` of witnesses and
    whatever the affine forms, the set of public inputs accepted by a single row either
    has at most two elements, or omits at most one element. -/
theorem one_row_dichotomy [IsAlgClosed F] (R : Row F m) :
    AtMostTwo (rowSolutions R) ∨ CoAtMostOne (rowSolutions R) := by
  classical
  by_cases h1 : R.A.cw = 0
  · by_cases h2 : R.B.cw = 0
    · exact one_row_both_const R h1 h2
    · -- swap the two factors
      have hswap : rowSolutions R = rowSolutions ⟨R.B, R.A, R.C⟩ := by
        ext x
        constructor <;> rintro ⟨w, hw⟩ <;>
          exact ⟨w, by rw [Row.Holds] at hw ⊢; linear_combination hw⟩
      rw [hswap]
      exact one_row_left_only ⟨R.B, R.A, R.C⟩ h2 h1
  · by_cases h2 : R.B.cw = 0
    · exact one_row_left_only R h1 h2
    · -- both factors have a free witness direction: every `x` is accepted
      right
      refine ⟨0, fun x _ => ?_⟩
      obtain ⟨v, hv1, hv2⟩ := exists_dot_ne_zero_two R.A.cw R.B.cw h1 h2
      set p := ∑ i, R.A.cw i * v i with hp
      set q := ∑ i, R.B.cw i * v i with hq
      set e := ∑ i, R.C.cw i * v i with he
      set a := R.A.cx * x + R.A.c with ha
      set b := R.B.cx * x + R.B.c with hb
      set d := R.C.cx * x + R.C.c with hd
      obtain ⟨t, ht⟩ := exists_quad_root (p * q) (a * q + b * p - e) (a * b - d)
        (mul_ne_zero hv1 hv2)
      refine ⟨fun i => t * v i, ?_⟩
      have hscale : ∀ u : Fin m → F, ∑ i, u i * (t * v i) = t * ∑ i, u i * v i := by
        intro u
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [Row.Holds, Aff.eval_split, Aff.eval_split, Aff.eval_split, hscale, hscale, hscale]
      rw [← ha, ← hb, ← hd, ← hp, ← hq, ← he]
      linear_combination ht

/-! ## Systems with no witnesses, and systems with no rows -/

/-- With no rows, every public input is accepted. -/
theorem zero_rows_solutions (S : System F m 0) : S.solutions = Set.univ := by
  ext x
  simp only [Set.mem_univ, iff_true, System.solutions, Set.mem_setOf_eq, System.Sat]
  exact ⟨0, fun j => absurd j.2 (by omega)⟩

/-- A row with no witnesses at all is a univariate quadratic condition on `x`. -/
theorem zero_witness_row (R : Row F 0) :
    AtMostTwo (rowSolutions R) ∨ rowSolutions R = Set.univ :=
  quad_row_dichotomy R (Subsingleton.elim _ _) (Subsingleton.elim _ _) (Subsingleton.elim _ _)

/-- **With no witnesses**, any number of rows accepts at most two values of `x`,
    or all of them. -/
theorem zero_witness_dichotomy (S : System F 0 r) :
    AtMostTwo S.solutions ∨ S.solutions = Set.univ := by
  classical
  by_cases hex : ∃ j, AtMostTwo (rowSolutions (S.row j))
  · obtain ⟨j, a, b, hab⟩ := hex
    refine Or.inl ⟨a, b, fun x hx => hab ?_⟩
    obtain ⟨w, hw⟩ := hx
    exact ⟨w, hw j⟩
  · push_neg at hex
    right
    ext x
    simp only [Set.mem_univ, iff_true, System.solutions, Set.mem_setOf_eq, System.Sat]
    refine ⟨0, fun j => ?_⟩
    have huniv : rowSolutions (S.row j) = Set.univ := by
      rcases zero_witness_row (S.row j) with h | h
      · exact absurd h (hex j)
      · exact h
    have hx : x ∈ rowSolutions (S.row j) := by rw [huniv]; trivial
    obtain ⟨w, hw⟩ := hx
    have hw0 : w = 0 := Subsingleton.elim _ _
    rwa [hw0] at hw

end Solution.Research
