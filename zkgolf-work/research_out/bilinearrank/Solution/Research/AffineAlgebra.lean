/-
  # Algebraic helpers for the one-row analysis

  Coefficient extraction for polynomial identities that hold on an infinite set,
  degeneracy of a vanishing product of linear forms, and the key normal-form lemma:
  *a bilinear map that is affine plus one product of two affine forms has rank ≤ 1*.
-/
import Solution.Research.RankCalculus

namespace Solution.Research

open Module Polynomial

variable {F : Type*} [Field F] {m n p : ℕ}

/-- A polynomial identity of degree `< N` that holds on an infinite set has all
coefficients zero. -/
lemma coeffs_zero_of_eval_zero {N : ℕ} (c : ℕ → F) (S : Set F) (hS : S.Infinite)
    (h : ∀ t ∈ S, ∑ i ∈ Finset.range N, c i * t ^ i = 0) : ∀ i, i < N → c i = 0 := by
  set q : F[X] := ∑ i ∈ Finset.range N, Polynomial.C (c i) * X ^ i with hq
  have hroots : q = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot q (hS.mono ?_)
    intro t ht
    simp only [Set.mem_setOf_eq, Polynomial.IsRoot, hq, Polynomial.eval_finset_sum]
    simpa using h t ht
  intro i hi
  have hco := congrArg (fun r => Polynomial.coeff r i) hroots
  simp only [hq, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_zero] at hco
  simpa [Finset.mem_range.2 hi] using hco

/-- Vector-valued version of `coeffs_zero_of_eval_zero`. -/
lemma vec_coeffs_zero {N : ℕ} (c : ℕ → Vec F p) (S : Set F) (hS : S.Infinite)
    (h : ∀ t ∈ S, ∑ i ∈ Finset.range N, t ^ i • c i = 0) : ∀ i, i < N → c i = 0 := by
  intro i hi
  funext j
  refine coeffs_zero_of_eval_zero (fun k => c k j) S hS (fun t ht => ?_) i hi
  have := congrFun (h t ht) j
  simpa [Finset.sum_apply, mul_comm] using this

/-- The nonzero elements of an infinite field form an infinite set. -/
lemma infinite_ne_zero [Infinite F] : {t : F | t ≠ 0}.Infinite := by
  have h : {t : F | t ≠ 0} = (Set.univ : Set F) \ {0} := by
    ext t; simp
  rw [h]
  exact Set.Infinite.diff Set.infinite_univ (Set.finite_singleton 0)

/-- A vector-valued quadratic in `t` vanishing for all `t ≠ 0` has zero coefficients. -/
lemma quad_coeffs [Infinite F] (c0 c1 c2 : Vec F p)
    (h : ∀ t : F, t ≠ 0 → c0 + t • c1 + (t ^ 2) • c2 = 0) : c0 = 0 ∧ c1 = 0 ∧ c2 = 0 := by
  classical
  set c : ℕ → Vec F p := fun i => if i = 0 then c0 else if i = 1 then c1 else c2 with hc
  have hid : ∀ t ∈ {t : F | t ≠ 0}, ∑ i ∈ Finset.range 3, t ^ i • c i = 0 := by
    intro t ht
    have h1 := h t ht
    simp only [hc, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, one_smul,
      pow_one]
    norm_num
    linear_combination (norm := module) h1
  have hz := vec_coeffs_zero c {t : F | t ≠ 0} infinite_ne_zero hid
  refine ⟨?_, ?_, ?_⟩
  · simpa [hc] using hz 0 (by norm_num)
  · simpa [hc] using hz 1 (by norm_num)
  · simpa [hc] using hz 2 (by norm_num)

/-- If the product of two linear forms vanishes identically, one of them vanishes. -/
lemma linear_forms_mul_eq_zero {M : Type*} [AddCommGroup M] [Module F M]
    (A B : M →ₗ[F] F) (h : ∀ x, A x * B x = 0) : (∀ x, A x = 0) ∨ (∀ x, B x = 0) := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨⟨x₀, hx₀⟩, ⟨x₁, hx₁⟩⟩ := hcon
  have h0 : B x₀ = 0 := by
    rcases mul_eq_zero.1 (h x₀) with h' | h'
    · exact absurd h' hx₀
    · exact h'
  have h1 : A x₁ = 0 := by
    rcases mul_eq_zero.1 (h x₁) with h' | h'
    · exact h'
    · exact absurd h' hx₁
  have hsum := h (x₀ + x₁)
  rw [map_add, map_add, h0, h1] at hsum
  simp only [add_zero, zero_add, mul_eq_zero] at hsum
  rcases hsum with h' | h'
  · exact hx₀ h'
  · exact hx₁ h'

/-- An affine form with a nonzero linear part has a zero. -/
lemma exists_root_of_affine (A : Vec F m →ₗ[F] F) (A' : Vec F n →ₗ[F] F) (a₀ : F)
    (hA : (∃ x, A x ≠ 0) ∨ (∃ y, A' y ≠ 0)) : ∃ x y, A x + A' y + a₀ = 0 := by
  rcases hA with ⟨x₁, hx₁⟩ | ⟨y₁, hy₁⟩
  · refine ⟨(-a₀ / A x₁) • x₁, 0, ?_⟩
    simp only [map_smul, map_zero, smul_eq_mul, add_zero]
    field_simp
    ring
  · refine ⟨0, (-a₀ / A' y₁) • y₁, ?_⟩
    simp only [map_smul, map_zero, smul_eq_mul, zero_add]
    field_simp
    ring

/-- A bilinear map that is a sum of a function of `x`, a function of `y` and a constant
is zero. -/
lemma bilinear_eq_zero_of_split (f : BilMap F m n p) (g : Vec F m → Vec F p)
    (h : Vec F n → Vec F p) (k : Vec F p) (hf : ∀ x y, f x y = g x + h y + k) :
    ∀ x y, f x y = 0 := by
  intro x y
  have e1 := hf x y
  have e2 := hf x 0
  have e3 := hf 0 y
  have e4 := hf 0 0
  have hsplit : f x y = f x 0 + f 0 y - f 0 0 := by rw [e1, e2, e3, e4]; abel
  simpa using hsplit

/-- A bilinear map that is a sum of a function of `x`, a function of `y` and a constant
has rank `0`, hence rank at most `r` for any `r`. -/
lemma hasRankLE_zero_of_split (f : BilMap F m n p) (g : Vec F m → Vec F p)
    (h : Vec F n → Vec F p) (k : Vec F p) (hf : ∀ x y, f x y = g x + h y + k) :
    HasRankLE (fun x y => f x y) 0 :=
  hasRankLE_zero _ (bilinear_eq_zero_of_split f g h k hf)

/-- **Normal form for one product.** A bilinear map that equals an affine map plus one
product of two affine forms (times a fixed vector) has tensor rank at most one. -/
theorem hasRankLE_one_of_affine_product [Infinite F] (f : BilMap F m n p)
    (Zx : Vec F m →ₗ[F] Vec F p) (Zy : Vec F n →ₗ[F] Vec F p) (k : Vec F p)
    (A : Vec F m →ₗ[F] F) (A' : Vec F n →ₗ[F] F) (a₀ : F)
    (B : Vec F m →ₗ[F] F) (B' : Vec F n →ₗ[F] F) (b₀ : F) (w : Vec F p)
    (hf : ∀ x y, f x y = Zx x + Zy y + k + ((A x + A' y + a₀) * (B x + B' y + b₀)) • w) :
    HasRankLE (fun x y => f x y) 1 := by
  classical
  -- expand at `(t • x, y)` and read off the coefficients of the resulting quadratic in `t`
  have coeff : ∀ x y, ((A x * B x) • w = 0) ∧
      (f x y = Zx x + (A x * (B' y + b₀) + (A' y + a₀) * B x) • w) := by
    intro x y
    have hq := quad_coeffs (p := p)
      (Zy y + k + ((A' y + a₀) * (B' y + b₀)) • w)
      (Zx x + (A x * (B' y + b₀) + (A' y + a₀) * B x) • w - f x y)
      ((A x * B x) • w) ?_
    · exact ⟨hq.2.2, by
        have := hq.2.1
        rw [sub_eq_zero] at this
        exact this.symm⟩
    · intro t _
      have h1 := hf (t • x) y
      rw [show f (t • x) y = t • f x y from by rw [map_smul, LinearMap.smul_apply]] at h1
      simp only [map_smul, smul_eq_mul] at h1
      linear_combination (norm := module) -h1
  -- the same expansion in the second argument
  have coeff' : ∀ y, (A' y * B' y) • w = 0 := by
    intro y
    set x : Vec F m := 0 with hx
    have hq := quad_coeffs (p := p)
      (Zx x + k + ((A x + a₀) * (B x + b₀)) • w)
      (Zy y + (A' y * (B x + b₀) + (A x + a₀) * B' y) • w - f x y)
      ((A' y * B' y) • w) ?_
    · exact hq.2.2
    · intro t _
      have h1 := hf x (t • y)
      rw [show f x (t • y) = t • f x y from by rw [map_smul]] at h1
      simp only [map_smul, smul_eq_mul] at h1
      linear_combination (norm := module) -h1
  have hAB : ∀ x, (A x * B x) • w = 0 := fun x => (coeff x 0).1
  have hAB' : ∀ y, (A' y * B' y) • w = 0 := coeff'
  -- the purely bilinear part
  have hmain : ∀ x y, f x y = (A x * B' y + A' y * B x) • w := by
    intro x y
    have h1 := (coeff x y).2
    have h2 := (coeff x 0).2
    have hf0 : f x 0 = 0 := by simp
    rw [hf0] at h2
    simp only [map_zero, zero_add] at h2
    rw [h1]
    rw [show Zx x = -((A x * b₀ + a₀ * B x) • w) from by
      rw [eq_neg_iff_add_eq_zero, ← h2]]
    module
  by_cases hw : w = 0
  · refine (hasRankLE_zero _ ?_).mono (by norm_num)
    intro x y
    rw [hmain x y, hw, smul_zero]
  · obtain ⟨j, hj⟩ : ∃ j, w j ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hw (funext hcon)
    have hABs : ∀ x, A x * B x = 0 := by
      intro x
      have hx := congrFun (hAB x) j
      simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hx
      rcases mul_eq_zero.1 hx with h' | h'
      · exact h'
      · exact absurd h' hj
    have hABs' : ∀ y, A' y * B' y = 0 := by
      intro y
      have hy := congrFun (hAB' y) j
      simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hy
      rcases mul_eq_zero.1 hy with h' | h'
      · exact h'
      · exact absurd h' hj
    rcases linear_forms_mul_eq_zero A B hABs with hA0 | hB0 <;>
      rcases linear_forms_mul_eq_zero A' B' hABs' with hA0' | hB0'
    · refine (hasRankLE_zero _ ?_).mono (by norm_num)
      intro x y
      rw [hmain x y, hA0 x, hA0' y]
      simp
    · -- `A = 0` and `B' = 0`: `f x y = (A' y * B x) • w`
      refine ⟨fun _ => B, fun _ => A', fun _ => w, fun x y => ?_⟩
      simp only [Finset.sum_range_one]
      rw [hmain x y, hA0 x, hB0' y]
      ring_nf
    · -- `B = 0` and `A' = 0`: `f x y = (A x * B' y) • w`
      refine ⟨fun _ => A, fun _ => B', fun _ => w, fun x y => ?_⟩
      simp only [Finset.sum_range_one]
      rw [hmain x y, hB0 x, hA0' y]
      ring_nf
    · refine (hasRankLE_zero _ ?_).mono (by norm_num)
      intro x y
      rw [hmain x y, hB0 x, hB0' y]
      simp

end Solution.Research
