/-
  # One row buys exactly rank one

  Over an infinite field, a *single* R1CS row — with arbitrarily many intermediate
  witnesses, nondeterministically supplied, and with factors that may mix the inputs and
  the witnesses freely — certifies only bilinear maps of tensor rank at most one.

  So at the bottom of the scale the correspondence is exact: nondeterminism and
  intermediate witnesses buy nothing at one row, and a bilinear map of rank ≥ 2 really
  does need ≥ 2 rows.

  The analysis is a case distinction on how the three linear forms `l, mm, nn` that the
  row applies to the witness interact:

  * some witness direction is invisible to the two factors but shifts the right-hand
    side (`nn d = 1`): the row is then just a *definition* of one product, and `f` is
    affine plus one product of affine forms;
  * otherwise `nn` is a combination of `l` and `mm`, and either
    - `l` and `mm` are independent, and then the witness slides along a hyperbola of
      solutions, forcing the output to be affine, hence zero; or
    - one of them is a multiple of the other, and a degree count in a scaling parameter
      forces the output to be affine again, except in the degenerate case where the row
      pins a single product.
-/
import Solution.Research.AffineAlgebra
import Solution.Research.LowerBound

namespace Solution.Research

open Module

variable {F : Type*} [Field F] {m n p : ℕ}

namespace OneRow

/-- **Case: the right-hand side has a free direction.** If some witness direction is
invisible to both factors but shifts the right-hand side, the row is a definition of one
product and `f` is affine plus that product. -/
theorem hasRankLE_one_of_free_rhs [Infinite F] {s : ℕ} (f : BilMap F m n p)
    (l mm nn : Vec F s →ₗ[F] F) (lam : Vec F s →ₗ[F] Vec F p)
    (A : Vec F m →ₗ[F] F) (A' : Vec F n →ₗ[F] F) (a₀ : F)
    (B : Vec F m →ₗ[F] F) (B' : Vec F n →ₗ[F] F) (b₀ : F)
    (C : Vec F m →ₗ[F] F) (C' : Vec F n →ₗ[F] F) (c₀ : F)
    (Zx : Vec F m →ₗ[F] Vec F p) (Zy : Vec F n →ₗ[F] Vec F p) (z₀ : Vec F p)
    (hsound : ∀ x y u, (l u + (A x + A' y + a₀)) * (mm u + (B x + B' y + b₀))
        = nn u + (C x + C' y + c₀) → lam u + (Zx x + Zy y + z₀) = f x y)
    (d : Vec F s) (hl : l d = 0) (hm : mm d = 0) (hn : nn d = 1) :
    HasRankLE (fun x y => f x y) 1 := by
  set w : Vec F p := lam d with hw
  have key : ∀ x y, f x y = (Zx x - (C x) • w) + (Zy y - (C' y) • w) + (z₀ - c₀ • w)
      + ((A x + A' y + a₀) * (B x + B' y + b₀)) • w := by
    intro x y
    set t : F := (A x + A' y + a₀) * (B x + B' y + b₀) - (C x + C' y + c₀) with ht
    have hrow : (l (t • d) + (A x + A' y + a₀)) * (mm (t • d) + (B x + B' y + b₀))
        = nn (t • d) + (C x + C' y + c₀) := by
      simp only [map_smul, hl, hm, hn, smul_eq_mul, mul_zero, mul_one, zero_add, ht]
      ring
    have hout := hsound x y (t • d) hrow
    rw [map_smul] at hout
    rw [← hout, ht]
    module
  exact hasRankLE_one_of_affine_product f (Zx - C.smulRight w) (Zy - C'.smulRight w)
    (z₀ - c₀ • w) A A' a₀ B B' b₀ w (by
      intro x y
      rw [key x y]
      simp only [LinearMap.sub_apply, LinearMap.smulRight_apply])

/-- **Case: the two factors are independent.** Then the witness slides along a whole
hyperbola of solutions, and soundness forces the output to be affine, hence zero. -/
theorem eq_zero_of_independent [Infinite F] {s : ℕ} (f : BilMap F m n p)
    (l mm nn : Vec F s →ₗ[F] F) (lam : Vec F s →ₗ[F] Vec F p)
    (A : Vec F m →ₗ[F] F) (A' : Vec F n →ₗ[F] F) (a₀ : F)
    (B : Vec F m →ₗ[F] F) (B' : Vec F n →ₗ[F] F) (b₀ : F)
    (C : Vec F m →ₗ[F] F) (C' : Vec F n →ₗ[F] F) (c₀ : F)
    (Zx : Vec F m →ₗ[F] Vec F p) (Zy : Vec F n →ₗ[F] Vec F p) (z₀ : Vec F p)
    (hsound : ∀ x y u, (l u + (A x + A' y + a₀)) * (mm u + (B x + B' y + b₀))
        = nn u + (C x + C' y + c₀) → lam u + (Zx x + Zy y + z₀) = f x y)
    (hspan : ∀ d, l d = 0 → mm d = 0 → nn d = 0 → lam d = 0)
    (hdep : ∀ d, l d = 0 → mm d = 0 → nn d = 0)
    (d1 d2 : Vec F s) (h11 : l d1 = 1) (h12 : mm d1 = 0)
    (h21 : l d2 = 0) (h22 : mm d2 = 1) :
    ∀ x y, f x y = 0 := by
  set pp : F := nn d1 with hpp
  set q : F := nn d2 with hq
  set α : Vec F p := lam d1 with hα
  set β : Vec F p := lam d2 with hβ
  have hnn : ∀ u, nn u = pp * l u + q * mm u := by
    intro u
    have hres : nn (u - (l u) • d1 - (mm u) • d2) = 0 := by
      refine hdep _ ?_ ?_
      · simp [map_sub, map_smul, h11, h21]
      · simp [map_sub, map_smul, h12, h22]
    simp only [map_sub, map_smul, smul_eq_mul] at hres
    linear_combination hres
  have hlam : ∀ u, lam u = (l u) • α + (mm u) • β := by
    intro u
    have hres : lam (u - (l u) • d1 - (mm u) • d2) = 0 := by
      refine hspan _ ?_ ?_ ?_
      · simp [map_sub, map_smul, h11, h21]
      · simp [map_sub, map_smul, h12, h22]
      · rw [hnn]
        simp [map_sub, map_smul, h11, h21, h12, h22]
    simp only [map_sub, map_smul] at hres
    rw [← sub_eq_zero, ← hres]
    abel
  -- soundness in terms of the pair of factor values
  have hsound' : ∀ x y (L M : F),
      (L + (A x + A' y + a₀)) * (M + (B x + B' y + b₀)) = (pp * L + q * M) + (C x + C' y + c₀) →
      L • α + M • β + (Zx x + Zy y + z₀) = f x y := by
    intro x y L M hLM
    have hl' : l (L • d1 + M • d2) = L := by simp [map_add, map_smul, h11, h21]
    have hm' : mm (L • d1 + M • d2) = M := by simp [map_add, map_smul, h12, h22]
    have hn' : nn (L • d1 + M • d2) = pp * L + q * M := by rw [hnn, hl', hm']
    have hlm' : lam (L • d1 + M • d2) = L • α + M • β := by rw [hlam, hl', hm']
    have hres := hsound x y (L • d1 + M • d2) (by rw [hl', hm', hn']; exact hLM)
    rw [hlm'] at hres
    exact hres
  -- the value of `f` is forced to be a split (hence zero) function
  have hval : ∀ x y, f x y
      = (pp - (B x + B' y + b₀)) • β + (Zx x + Zy y + z₀) := by
    intro x y
    set a : F := A x + A' y + a₀ with ha
    set b : F := B x + B' y + b₀ with hb
    set c : F := C x + C' y + c₀ with hc
    set W : Vec F p := Zx x + Zy y + z₀ with hW
    set κ : F := c + pp * q - pp * a - q * b with hκ
    have hquad := quad_coeffs (p := p) (κ • β)
        ((q - a) • α + (pp - b) • β + W - f x y) α ?_
    · have hα0 : α = 0 := hquad.2.2
      have h1 : (q - a) • α + (pp - b) • β + W - f x y = 0 := hquad.2.1
      rw [hα0, smul_zero, zero_add] at h1
      linear_combination (norm := module) -h1
    · intro t ht
      have hrow : ((t - a + q) + a) * ((κ / t - b + pp) + b)
          = (pp * (t - a + q) + q * (κ / t - b + pp)) + c := by
        field_simp
        ring
      have hres := hsound' x y (t - a + q) (κ / t - b + pp) hrow
      rw [← sub_eq_zero, ← hres]
      match_scalars <;> field_simp <;> ring
  intro x y
  refine bilinear_eq_zero_of_split f (fun x => (-(B x)) • β + Zx x)
    (fun y => (-(B' y)) • β + Zy y) ((pp - b₀) • β + z₀) ?_ x y
  intro x y
  rw [hval x y]
  module

/-- The top coefficient of a quartic vanishing identically on an infinite field is zero. -/
lemma quartic_top_coeff [Infinite F] (c0 c1 c2 c3 c4 : F)
    (h : ∀ t : F, c0 + c1 * t + c2 * t ^ 2 + c3 * t ^ 3 + c4 * t ^ 4 = 0) : c4 = 0 := by
  classical
  set c : ℕ → F := fun i =>
    if i = 0 then c0 else if i = 1 then c1 else if i = 2 then c2 else if i = 3 then c3 else c4
    with hc
  have hid : ∀ t ∈ (Set.univ : Set F), ∑ i ∈ Finset.range 5, c i * t ^ i = 0 := by
    intro t _
    simp only [hc, Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
    linear_combination h t
  have := coeffs_zero_of_eval_zero c Set.univ Set.infinite_univ hid 4 (by norm_num)
  simpa [hc] using this

/-- The leading coefficient of the row equation, after substituting a quadratic
parametrisation of the witness value. -/
lemma row_top_coeff [Infinite F] (e P Q R A1 a₀ B1 b₀ C1 c₀ p' : F)
    (h : ∀ t : F, ((t ^ 2 * P + t * Q + R) + (t * A1 + a₀))
        * (e * (t ^ 2 * P + t * Q + R) + (t * B1 + b₀))
        = p' * (t ^ 2 * P + t * Q + R) + (t * C1 + c₀)) : e * P ^ 2 = 0 := by
  refine quartic_top_coeff
    (e * R ^ 2 + R * b₀ + e * a₀ * R + a₀ * b₀ - p' * R - c₀)
    (2 * e * Q * R + Q * b₀ + R * B1 + e * (A1 * R + a₀ * Q) + A1 * b₀ + a₀ * B1 - p' * Q - C1)
    (e * (Q ^ 2 + 2 * P * R) + P * b₀ + Q * B1 + e * (A1 * Q + a₀ * P) + A1 * B1 - p' * P)
    (2 * e * P * Q + P * B1 + e * A1 * P) (e * P ^ 2) (fun t => ?_)
  linear_combination h t

/-- **Case: one factor is a scalar multiple of the other.** Then the row is a quadratic
equation in a single scalar unknown, and soundness forces the output to be split, hence
zero. -/
theorem eq_zero_of_scalar_row [Infinite F] (f : BilMap F m n p)
    (e p' : F) (β : Vec F p)
    (A : Vec F m →ₗ[F] F) (A' : Vec F n →ₗ[F] F) (a₀ : F)
    (B : Vec F m →ₗ[F] F) (B' : Vec F n →ₗ[F] F) (b₀ : F)
    (C : Vec F m →ₗ[F] F) (C' : Vec F n →ₗ[F] F) (c₀ : F)
    (Zx : Vec F m →ₗ[F] Vec F p) (Zy : Vec F n →ₗ[F] Vec F p) (z₀ : Vec F p)
    (hsound : ∀ x y (L : F), (L + (A x + A' y + a₀)) * (e * L + (B x + B' y + b₀))
        = p' * L + (C x + C' y + c₀) → L • β + (Zx x + Zy y + z₀) = f x y)
    (hcomp : ∀ x y, ∃ L : F, (L + (A x + A' y + a₀)) * (e * L + (B x + B' y + b₀))
        = p' * L + (C x + C' y + c₀)) :
    ∀ x y, f x y = 0 := by
  classical
  by_cases hβ : β = 0
  · refine bilinear_eq_zero_of_split f (fun x => Zx x) (fun y => Zy y) z₀ (fun x y => ?_)
    obtain ⟨L, hL⟩ := hcomp x y
    have h := hsound x y L hL
    rw [hβ, smul_zero, zero_add] at h
    exact h.symm
  obtain ⟨j, hj⟩ : ∃ j, β j ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hβ (funext hcon)
  -- in both cases we end up knowing that the `j`-th coordinate of `f` vanishes
  have main : (∀ x y, f x y j = 0) → ∀ x y, f x y = 0 := by
    intro hfj
    refine bilinear_eq_zero_of_split f
      (fun x => (-(Zx x j) / β j) • β + Zx x)
      (fun y => (-(Zy y j) / β j) • β + Zy y)
      ((-(z₀ j) / β j) • β + z₀) (fun x y => ?_)
    obtain ⟨L, hL⟩ := hcomp x y
    have h := hsound x y L hL
    have hcoord := congrFun h j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hcoord
    rw [hfj x y] at hcoord
    have hL' : L = (-(Zx x j) / β j) + (-(Zy y j) / β j) + (-(z₀ j) / β j) := by
      field_simp
      linear_combination hcoord
    rw [← h, hL']
    module
  by_cases he : e = 0
  · subst he
    -- the row is affine in `L`; a solution exists and is unique, so its coefficient
    -- never vanishes, which forces the right factor to be constant
    have hne : ∀ x y, B x + B' y + b₀ - p' ≠ 0 := by
      intro x y hzero
      obtain ⟨L₀, hL₀⟩ := hcomp x y
      have hall : ∀ L : F, (L + (A x + A' y + a₀)) * (0 * L + (B x + B' y + b₀))
          = p' * L + (C x + C' y + c₀) := by
        intro L
        linear_combination hL₀ + (L - L₀) * hzero
      have h0 := hsound x y 0 (hall 0)
      have h1 := hsound x y 1 (hall 1)
      refine hβ ?_
      have := h1.trans h0.symm
      linear_combination (norm := module) this
    have hBz : (∀ x, B x = 0) ∧ ∀ y, B' y = 0 := by
      by_contra hcon
      have hex : (∃ x, B x ≠ 0) ∨ (∃ y, B' y ≠ 0) := by
        rw [not_and_or] at hcon
        rcases hcon with h | h
        · exact Or.inl (by push_neg at h; exact h)
        · exact Or.inr (by push_neg at h; exact h)
      obtain ⟨x, y, hxy⟩ := exists_root_of_affine B B' (b₀ - p') hex
      exact hne x y (by linear_combination hxy)
    obtain ⟨hB, hB'⟩ := hBz
    set κ : F := b₀ - p' with hκ
    have hκ0 : κ ≠ 0 := by
      have := hne 0 0
      simpa [hκ] using this
    -- the unique solution is affine and split, hence so is `f`
    refine bilinear_eq_zero_of_split f
      (fun x => (((C x) - (A x) * b₀) / κ) • β + Zx x)
      (fun y => (((C' y) - (A' y) * b₀) / κ) • β + Zy y)
      (((c₀ - a₀ * b₀) / κ) • β + z₀) (fun x y => ?_)
    set L : F := ((C x + C' y + c₀) - (A x + A' y + a₀) * b₀) / κ with hLdef
    have hrow : (L + (A x + A' y + a₀)) * (0 * L + (B x + B' y + b₀))
        = p' * L + (C x + C' y + c₀) := by
      rw [hB, hB', hLdef]
      field_simp [hκ]
      ring
    have h := hsound x y L hrow
    rw [← h, hLdef]
    match_scalars <;> (field_simp; try ring)
  · -- `e ≠ 0`: scale the input and read off the leading coefficient in the scaling
    refine main (fun x y => ?_)
    set Pv : F := f x y j / β j with hPv
    set Qv : F := (-(Zx x j) - Zy y j) / β j with hQv
    have hexp : ∀ t : F, ((t ^ 2 * Pv + t * Qv + (-(z₀ j) / β j)) + (t * (A x + A' y) + a₀))
        * (e * (t ^ 2 * Pv + t * Qv + (-(z₀ j) / β j)) + (t * (B x + B' y) + b₀))
        = p' * (t ^ 2 * Pv + t * Qv + (-(z₀ j) / β j)) + (t * (C x + C' y) + c₀) := by
      intro t
      obtain ⟨L, hL⟩ := hcomp (t • x) (t • y)
      have hsm : ∀ (D : Vec F m →ₗ[F] F) (D' : Vec F n →ₗ[F] F),
          D (t • x) + D' (t • y) = t * (D x + D' y) := by
        intro D D'
        simp [map_smul]
        ring
      have h := hsound (t • x) (t • y) L hL
      have hf2 : f (t • x) (t • y) = (t ^ 2) • f x y := by
        simp only [map_smul, LinearMap.smul_apply, smul_smul, pow_two]
      rw [hf2] at h
      have hcoord := congrFun h j
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_smul] at hcoord
      have hLval : L = t ^ 2 * Pv + t * Qv + (-(z₀ j) / β j) := by
        rw [hPv, hQv]
        field_simp
        linear_combination hcoord
      rw [← hLval]
      simp only [map_smul, smul_eq_mul] at hL ⊢
      linear_combination hL
    have htop := row_top_coeff e Pv Qv (-(z₀ j) / β j) (A x + A' y) a₀ (B x + B' y) b₀
      (C x + C' y) c₀ p' hexp
    have hPv0 : Pv = 0 := by
      rcases mul_eq_zero.1 htop with h | h
      · exact absurd h he
      · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h
    have hdiv : f x y j / β j = 0 := hPv0
    exact (div_eq_zero_iff.1 hdiv).resolve_right hj

/-- Two linear forms with no `(1,0)`-vector are proportional in one of the two
directions. -/
lemma dep_of_no_pair {s : ℕ} (l mm : Vec F s →ₗ[F] F) (h : ¬ ∃ d, l d = 0 ∧ mm d = 1) :
    (∃ e : F, ∀ u, l u = e * mm u) ∨ (∃ e : F, ∀ u, mm u = e * l u) := by
  classical
  by_cases hm : ∀ u, mm u = 0
  · exact Or.inr ⟨0, by intro u; rw [hm u]; ring⟩
  push_neg at hm
  obtain ⟨d₀, hd₀⟩ := hm
  obtain ⟨d, hmd⟩ : ∃ d, mm d = 1 :=
    ⟨(mm d₀)⁻¹ • d₀, by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hd₀]⟩
  have key : ∀ w, mm w = 0 → l w = 0 := by
    intro w hw
    by_contra hlw
    refine h ⟨d - (l d * (l w)⁻¹) • w, ?_, ?_⟩
    · rw [map_sub, map_smul, smul_eq_mul, mul_assoc, inv_mul_cancel₀ hlw, mul_one, sub_self]
    · rw [map_sub, map_smul, hw, smul_zero, sub_zero, hmd]
  refine Or.inl ⟨l d, fun u => ?_⟩
  have hmv : mm (u - (mm u) • d) = 0 := by
    rw [map_sub, map_smul, hmd, smul_eq_mul, mul_one, sub_self]
  have hlv := key _ hmv
  rw [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at hlv
  rw [hlv]
  ring

/-- Completeness plus soundness force the free output map to vanish on witness
directions that no row can see: **nondeterminism smuggles no information**. -/
lemma span_of_row {s : ℕ} (f : BilMap F m n p)
    (l mm nn : Vec F s →ₗ[F] F) (lam : Vec F s →ₗ[F] Vec F p)
    (A : Vec F m →ₗ[F] F) (A' : Vec F n →ₗ[F] F) (a₀ : F)
    (B : Vec F m →ₗ[F] F) (B' : Vec F n →ₗ[F] F) (b₀ : F)
    (C : Vec F m →ₗ[F] F) (C' : Vec F n →ₗ[F] F) (c₀ : F)
    (Zx : Vec F m →ₗ[F] Vec F p) (Zy : Vec F n →ₗ[F] Vec F p) (z₀ : Vec F p)
    (hsound : ∀ x y u, (l u + (A x + A' y + a₀)) * (mm u + (B x + B' y + b₀))
        = nn u + (C x + C' y + c₀) → lam u + (Zx x + Zy y + z₀) = f x y)
    (hcomp : ∀ x y, ∃ u, (l u + (A x + A' y + a₀)) * (mm u + (B x + B' y + b₀))
        = nn u + (C x + C' y + c₀))
    (d : Vec F s) (hl : l d = 0) (hm : mm d = 0) (hn : nn d = 0) : lam d = 0 := by
  obtain ⟨u, hu⟩ := hcomp 0 0
  have hu' : (l (u + d) + (A 0 + A' 0 + a₀)) * (mm (u + d) + (B 0 + B' 0 + b₀))
      = nn (u + d) + (C 0 + C' 0 + c₀) := by
    rw [map_add, map_add, map_add, hl, hm, hn, add_zero, add_zero, add_zero]
    exact hu
  have h1 := hsound 0 0 u hu
  have h2 := hsound 0 0 (u + d) hu'
  rw [map_add] at h2
  have := h2.trans h1.symm
  linear_combination (norm := module) this

/-- **Case: the two factors are proportional.** Reduction of the row to a single scalar
unknown, then `eq_zero_of_scalar_row`. -/
theorem eq_zero_of_dep_row [Infinite F] {s : ℕ} (f : BilMap F m n p)
    (l mm nn : Vec F s →ₗ[F] F) (lam : Vec F s →ₗ[F] Vec F p)
    (A : Vec F m →ₗ[F] F) (A' : Vec F n →ₗ[F] F) (a₀ : F)
    (B : Vec F m →ₗ[F] F) (B' : Vec F n →ₗ[F] F) (b₀ : F)
    (C : Vec F m →ₗ[F] F) (C' : Vec F n →ₗ[F] F) (c₀ : F)
    (Zx : Vec F m →ₗ[F] Vec F p) (Zy : Vec F n →ₗ[F] Vec F p) (z₀ : Vec F p)
    (hsound : ∀ x y u, (l u + (A x + A' y + a₀)) * (mm u + (B x + B' y + b₀))
        = nn u + (C x + C' y + c₀) → lam u + (Zx x + Zy y + z₀) = f x y)
    (hcomp : ∀ x y, ∃ u, (l u + (A x + A' y + a₀)) * (mm u + (B x + B' y + b₀))
        = nn u + (C x + C' y + c₀))
    (hdep : ∀ d, l d = 0 → mm d = 0 → nn d = 0)
    (e : F) (he : ∀ u, mm u = e * l u) :
    ∀ x y, f x y = 0 := by
  classical
  have hspan := span_of_row f l mm nn lam A A' a₀ B B' b₀ C C' c₀ Zx Zy z₀ hsound hcomp
  by_cases hl : ∀ u, l u = 0
  · refine bilinear_eq_zero_of_split f (fun x => Zx x) (fun y => Zy y) z₀ (fun x y => ?_)
    obtain ⟨u, hu⟩ := hcomp x y
    have hm0 : mm u = 0 := by rw [he u, hl u, mul_zero]
    have hlam0 : lam u = 0 := hspan u (hl u) hm0 (hdep u (hl u) hm0)
    have h := hsound x y u hu
    rw [hlam0, zero_add] at h
    exact h.symm
  push_neg at hl
  obtain ⟨d₀, hd₀⟩ := hl
  set d₁ : Vec F s := (l d₀)⁻¹ • d₀ with hd₁
  have hld : l d₁ = 1 := by rw [hd₁, map_smul, smul_eq_mul, inv_mul_cancel₀ hd₀]
  set p' : F := nn d₁ with hp'
  set β : Vec F p := lam d₁ with hβ
  have hres : ∀ u, l (u - (l u) • d₁) = 0 ∧ mm (u - (l u) • d₁) = 0 := by
    intro u
    have h1 : l (u - (l u) • d₁) = 0 := by
      rw [map_sub, map_smul, hld, smul_eq_mul, mul_one, sub_self]
    exact ⟨h1, by rw [he, h1, mul_zero]⟩
  have hnn : ∀ u, nn u = p' * l u := by
    intro u
    have := hdep _ (hres u).1 (hres u).2
    rw [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at this
    rw [this, hp']
    ring
  have hlam : ∀ u, lam u = (l u) • β := by
    intro u
    have := hspan _ (hres u).1 (hres u).2 (hdep _ (hres u).1 (hres u).2)
    rw [map_sub, map_smul, sub_eq_zero] at this
    rw [this, hβ]
  refine eq_zero_of_scalar_row f e p' β A A' a₀ B B' b₀ C C' c₀ Zx Zy z₀ ?_ ?_
  · intro x y L hL
    have hlL : l (L • d₁) = L := by rw [map_smul, hld, smul_eq_mul, mul_one]
    have hrow : (l (L • d₁) + (A x + A' y + a₀)) * (mm (L • d₁) + (B x + B' y + b₀))
        = nn (L • d₁) + (C x + C' y + c₀) := by
      rw [hlL, he, hlL, hnn, hlL]
      exact hL
    have h := hsound x y (L • d₁) hrow
    rw [hlam, hlL] at h
    exact h
  · intro x y
    obtain ⟨u, hu⟩ := hcomp x y
    exact ⟨l u, by rw [← he u, ← hnn u]; exact hu⟩

/-- **One row buys only rank one.** Abstract form: a single R1CS row over an arbitrary
number of nondeterministic intermediate witnesses, whose factors may mix the inputs and
the witnesses arbitrarily, certifies only bilinear maps of tensor rank at most one. -/
theorem hasRankLE_one_of_row [Infinite F] {s : ℕ} (f : BilMap F m n p)
    (l mm nn : Vec F s →ₗ[F] F) (lam : Vec F s →ₗ[F] Vec F p)
    (A : Vec F m →ₗ[F] F) (A' : Vec F n →ₗ[F] F) (a₀ : F)
    (B : Vec F m →ₗ[F] F) (B' : Vec F n →ₗ[F] F) (b₀ : F)
    (C : Vec F m →ₗ[F] F) (C' : Vec F n →ₗ[F] F) (c₀ : F)
    (Zx : Vec F m →ₗ[F] Vec F p) (Zy : Vec F n →ₗ[F] Vec F p) (z₀ : Vec F p)
    (hsound : ∀ x y u, (l u + (A x + A' y + a₀)) * (mm u + (B x + B' y + b₀))
        = nn u + (C x + C' y + c₀) → lam u + (Zx x + Zy y + z₀) = f x y)
    (hcomp : ∀ x y, ∃ u, (l u + (A x + A' y + a₀)) * (mm u + (B x + B' y + b₀))
        = nn u + (C x + C' y + c₀)) :
    HasRankLE (fun x y => f x y) 1 := by
  classical
  by_cases hfree : ∃ d, l d = 0 ∧ mm d = 0 ∧ nn d ≠ 0
  · obtain ⟨d, hl, hm, hn⟩ := hfree
    refine hasRankLE_one_of_free_rhs f l mm nn lam A A' a₀ B B' b₀ C C' c₀ Zx Zy z₀ hsound
      ((nn d)⁻¹ • d) ?_ ?_ ?_
    · rw [map_smul, hl, smul_zero]
    · rw [map_smul, hm, smul_zero]
    · rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hn]
  push_neg at hfree
  have hdep : ∀ d, l d = 0 → mm d = 0 → nn d = 0 := hfree
  have hspan := span_of_row f l mm nn lam A A' a₀ B B' b₀ C C' c₀ Zx Zy z₀ hsound hcomp
  -- in every remaining case `f` is forced to be zero
  suffices h : ∀ x y, f x y = 0 by
    exact (hasRankLE_zero _ h).mono (by norm_num)
  -- the symmetric form of soundness, with the two factors exchanged
  have hsound' : ∀ x y u, (mm u + (B x + B' y + b₀)) * (l u + (A x + A' y + a₀))
      = nn u + (C x + C' y + c₀) → lam u + (Zx x + Zy y + z₀) = f x y := by
    intro x y u hrow
    exact hsound x y u (by rw [mul_comm]; exact hrow)
  have hcomp' : ∀ x y, ∃ u, (mm u + (B x + B' y + b₀)) * (l u + (A x + A' y + a₀))
      = nn u + (C x + C' y + c₀) := by
    intro x y
    obtain ⟨u, hu⟩ := hcomp x y
    exact ⟨u, by rw [mul_comm]; exact hu⟩
  have hdep' : ∀ d, mm d = 0 → l d = 0 → nn d = 0 := fun d h1 h2 => hdep d h2 h1
  by_cases hd1 : ∃ d, l d = 1 ∧ mm d = 0
  · by_cases hd2 : ∃ d, l d = 0 ∧ mm d = 1
    · obtain ⟨d1, h11, h12⟩ := hd1
      obtain ⟨d2, h21, h22⟩ := hd2
      exact eq_zero_of_independent f l mm nn lam A A' a₀ B B' b₀ C C' c₀ Zx Zy z₀ hsound
        hspan hdep d1 d2 h11 h12 h21 h22
    · rcases dep_of_no_pair l mm hd2 with ⟨e, he⟩ | ⟨e, he⟩
      · exact eq_zero_of_dep_row f mm l nn lam B B' b₀ A A' a₀ C C' c₀ Zx Zy z₀
          hsound' hcomp' hdep' e he
      · exact eq_zero_of_dep_row f l mm nn lam A A' a₀ B B' b₀ C C' c₀ Zx Zy z₀
          hsound hcomp hdep e he
  · have hd1' : ¬ ∃ d, mm d = 0 ∧ l d = 1 := fun ⟨d, h1, h2⟩ => hd1 ⟨d, h2, h1⟩
    rcases dep_of_no_pair mm l hd1' with ⟨e, he⟩ | ⟨e, he⟩
    · exact eq_zero_of_dep_row f l mm nn lam A A' a₀ B B' b₀ C C' c₀ Zx Zy z₀
        hsound hcomp hdep e he
    · exact eq_zero_of_dep_row f mm l nn lam B B' b₀ A A' a₀ C C' c₀ Zx Zy z₀
        hsound' hcomp' hdep' e he

end OneRow

namespace R1CS

variable (S : R1CS F m n p)

/-- Decomposition of a witness into its three parts. -/
lemma split_all (x : Vec F m) (y : Vec F n) (u : Vec F S.aux) :
    ((x, y, u) : Wit F m n S.aux) = S.ιx x + S.ιy y + S.ιu u := by
  simp [ιx, ιy, ιu]

end R1CS

/-- **A one-row R1CS certificate forces tensor rank at most one.** The system may use
any number of intermediate witnesses, supplied nondeterministically, and its single row
may multiply arbitrary affine forms of the whole witness. -/
theorem hasRankLE_one_of_rows_le_one [Infinite F] (f : BilMap F m n p) (S : R1CS F m n p)
    (hr : S.rows ≤ 1) (hc : S.Certifies (fun x y => f x y)) :
    HasRankLE (fun x y => f x y) 1 := by
  obtain ⟨hsound, hcomp⟩ := hc
  rcases Nat.lt_or_ge S.rows 1 with h0 | h1
  · have hz : minRows (fun x y => f x y) = 0 :=
      Nat.le_zero.1 (minRows_le ⟨S, by omega, hsound, hcomp⟩)
    exact (hasRankLE_zero _ ((minRows_eq_zero_iff f).1 hz)).mono (by norm_num)
  · have hrows : S.rows = 1 := le_antisymm hr h1
    set k : Fin S.rows := ⟨0, by omega⟩ with hk
    have hall : ∀ k' : Fin S.rows, k' = k := by
      intro k'
      have := k'.isLt
      exact Fin.ext (by omega)
    -- the row, split into the contributions of `x`, `y` and the intermediate witnesses
    have hsplit : ∀ (D : Wit F m n S.aux →ₗ[F] F) (d : F) (x : Vec F m) (y : Vec F n)
        (u : Vec F S.aux), D (x, y, u) + d = D (S.ιu u) + (D (S.ιx x) + D (S.ιy y) + d) := by
      intro D d x y u
      rw [S.split_all x y u, map_add, map_add]
      ring
    refine OneRow.hasRankLE_one_of_row f (S.A k ∘ₗ S.ιu) (S.B k ∘ₗ S.ιu) (S.C k ∘ₗ S.ιu) (S.Z ∘ₗ S.ιu)
      (S.A k ∘ₗ S.ιx) (S.A k ∘ₗ S.ιy) (S.a k)
      (S.B k ∘ₗ S.ιx) (S.B k ∘ₗ S.ιy) (S.b k)
      (S.C k ∘ₗ S.ιx) (S.C k ∘ₗ S.ιy) (S.c k)
      (S.Z ∘ₗ S.ιx) (S.Z ∘ₗ S.ιy) S.z₀ ?_ ?_
    · intro x y u hrow
      simp only [LinearMap.comp_apply] at hrow ⊢
      have hsat : S.Sat (x, y, u) := by
        intro k'
        rw [hall k', hsplit (S.A k) (S.a k), hsplit (S.B k) (S.b k), hsplit (S.C k) (S.c k)]
        exact hrow
      have hout := hsound x y u hsat
      simp only [R1CS.out] at hout
      rw [← hout, S.split_all x y u, map_add, map_add]
      abel
    · intro x y
      obtain ⟨u, hu⟩ := hcomp x y
      refine ⟨u, ?_⟩
      simp only [LinearMap.comp_apply]
      rw [← hsplit (S.A k) (S.a k), ← hsplit (S.B k) (S.b k), ← hsplit (S.C k) (S.c k)]
      exact hu k

/-- **Rank ≤ 1 iff one row.** Over an infinite field, the minimal row count and the
tensor rank agree at the bottom of the scale. -/
theorem tensorRank_le_one_of_minRows_le_one [Infinite F] (f : BilMap F m n p)
    (h : minRows (fun x y => f x y) ≤ 1) : tensorRank (fun x y => f x y) ≤ 1 := by
  obtain ⟨S, hrows, hcert⟩ := hasRowsLE_minRows f
  exact tensorRank_le (hasRankLE_one_of_rows_le_one f S (le_trans hrows h) hcert)


end Solution.Research
