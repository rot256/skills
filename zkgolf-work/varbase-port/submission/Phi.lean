import Solution.Secp256k1ScalarMul.Bridge

namespace Solution.Secp256k1ScalarMul.Phi

open Specs.ShortWeierstrass Specs.Secp256k1


def beta : Fp :=
  0x7ae96a2b657c07106e64479eac3434e99cf0497512f58995c1396c28719501ee

lemma beta_cube : beta ^ 3 = 1 := by decide

lemma beta_ne_zero : beta ≠ 0 := by
  intro h
  have hc := beta_cube
  rw [h] at hc
  norm_num at hc

lemma beta_mul_ne_zero {x : Fp} (hx : x ≠ 0) : beta * x ≠ 0 :=
  mul_ne_zero beta_ne_zero hx

lemma equation_beta {x y : Fp} (h : Bridge.W.Equation x y) :
    Bridge.W.Equation (beta * x) y := by
  rw [WeierstrassCurve.Affine.equation_iff] at h ⊢
  simp only [Bridge.W] at h ⊢
  simp only [zero_mul, zero_add, add_zero] at h ⊢
  rw [mul_pow, beta_cube, one_mul]
  exact h

lemma nonsingular_beta {x y : Fp} (h : Bridge.W.Nonsingular x y) :
    Bridge.W.Nonsingular (beta * x) y :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero Bridge.W_Δ_ne_zero).mp
    (equation_beta h.1)


def pointMap : Bridge.W.Point → Bridge.W.Point
  | .zero => .zero
  | @WeierstrassCurve.Affine.Point.some _ _ _ x y h =>
      .some (nonsingular_beta h)

@[simp] lemma pointMap_zero : pointMap 0 = 0 := rfl

@[simp] lemma pointMap_some {x y : Fp} (h : Bridge.W.Nonsingular x y) :
    pointMap (.some h) = .some (nonsingular_beta h) := rfl

lemma beta_mul_injective : Function.Injective (fun x : Fp => beta * x) := by
  intro x y h
  exact (mul_left_cancel₀ beta_ne_zero h)

lemma beta_sq_mul : beta ^ 2 * beta = 1 := by
  simpa [pow_succ] using beta_cube

lemma beta_mul_sq : beta * beta ^ 2 = 1 := by
  rw [mul_comm]
  exact beta_sq_mul

lemma beta_sq_ne_zero : beta ^ 2 ≠ 0 := pow_ne_zero _ beta_ne_zero

private lemma negY_eq (x y : Fp) : Bridge.W.negY x y = -y := by
  simp [WeierstrassCurve.Affine.negY, Bridge.W]

private lemma slope_beta (x₁ x₂ y₁ y₂ : Fp) :
    Bridge.W.slope (beta * x₁) (beta * x₂) y₁ y₂ =
      beta ^ 2 * Bridge.W.slope x₁ x₂ y₁ y₂ := by
  by_cases hx : x₁ = x₂
  · subst x₂
    by_cases hy : y₁ = -y₂
    · rw [WeierstrassCurve.Affine.slope_of_Y_eq rfl
            (by simpa [WeierstrassCurve.Affine.negY, Bridge.W] using hy),
          WeierstrassCurve.Affine.slope_of_Y_eq rfl
            (by simpa [WeierstrassCurve.Affine.negY, Bridge.W] using hy)]
      ring
    · have hy₁ : y₁ ≠ Bridge.W.negY x₁ y₂ := by
        simpa [WeierstrassCurve.Affine.negY, Bridge.W] using hy
      have hy₂ : y₁ ≠ Bridge.W.negY (beta * x₁) y₂ := by
        simpa [WeierstrassCurve.Affine.negY, Bridge.W] using hy
      rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy₂,
        WeierstrassCurve.Affine.slope_of_Y_ne rfl hy₁]
      simp [WeierstrassCurve.Affine.negY, Bridge.W]
      rw [mul_pow]
      ring
  · have hbx : beta * x₁ ≠ beta * x₂ := fun h => hx (beta_mul_injective h)
    rw [WeierstrassCurve.Affine.slope_of_X_ne hbx,
      WeierstrassCurve.Affine.slope_of_X_ne hx]
    rw [show beta * x₁ - beta * x₂ = beta * (x₁ - x₂) by ring]
    field_simp [beta_ne_zero, sub_ne_zero.mpr hx, beta_cube]
    rw [beta_cube]
    simp

private lemma addX_beta (x₁ x₂ ℓ : Fp) :
    Bridge.W.addX (beta * x₁) (beta * x₂) (beta ^ 2 * ℓ) =
      beta * Bridge.W.addX x₁ x₂ ℓ := by
  simp only [WeierstrassCurve.Affine.addX, Bridge.W]
  rw [mul_pow, show (beta ^ 2) ^ 2 = beta * beta ^ 3 by ring, beta_cube]
  ring

private lemma addY_beta (x₁ x₂ y₁ ℓ : Fp) :
    Bridge.W.addY (beta * x₁) (beta * x₂) y₁ (beta ^ 2 * ℓ) =
      Bridge.W.addY x₁ x₂ y₁ ℓ := by
  have hx := addX_beta x₁ x₂ ℓ
  unfold WeierstrassCurve.Affine.addY WeierstrassCurve.Affine.negY
    WeierstrassCurve.Affine.negAddY
  simp only [Bridge.W, zero_mul, sub_zero]
  change WeierstrassCurve.Affine.addX
      ({ a₁ := (0 : Fp), a₂ := 0, a₃ := 0, a₄ := 0, a₆ := 7 } :
        WeierstrassCurve.Affine Fp) (beta * x₁) (beta * x₂)
        (beta ^ 2 * ℓ) =
      beta * WeierstrassCurve.Affine.addX
        ({ a₁ := (0 : Fp), a₂ := 0, a₃ := 0, a₄ := 0, a₆ := 7 } :
          WeierstrassCurve.Affine Fp) x₁ x₂ ℓ at hx
  rw [hx]
  let A : Fp := WeierstrassCurve.Affine.addX
    ({ a₁ := (0 : Fp), a₂ := 0, a₃ := 0, a₄ := 0, a₆ := 7 } :
      WeierstrassCurve.Affine Fp) x₁ x₂ ℓ
  change -(beta ^ 2 * ℓ * (beta * A - beta * x₁) + y₁) =
    -(ℓ * (A - x₁) + y₁)
  have hs : beta ^ 2 * ℓ * (beta * A - beta * x₁) = ℓ * (A - x₁) := by
    calc
      beta ^ 2 * ℓ * (beta * A - beta * x₁) =
          (beta ^ 2 * beta) * (ℓ * (A - x₁)) := by ring
      _ = ℓ * (A - x₁) := by rw [beta_sq_mul, one_mul]
  rw [hs]

theorem pointMap_add (P Q : Bridge.W.Point) :
    pointMap (P + Q) = pointMap P + pointMap Q := by
  cases P with
  | zero => rfl
  | some h₁ =>
    cases Q with
    | zero => rfl
    | some h₂ =>
      rename_i x₁ y₁ x₂ y₂
      change pointMap ((WeierstrassCurve.Affine.Point.some h₁ : Bridge.W.Point) +
          WeierstrassCurve.Affine.Point.some h₂) =
        WeierstrassCurve.Affine.Point.some (nonsingular_beta h₁) +
          WeierstrassCurve.Affine.Point.some (nonsingular_beta h₂)
      have hneg₁ : Bridge.W.negY x₂ y₂ = -y₂ := negY_eq x₂ y₂
      have hneg₂ : Bridge.W.negY (beta * x₂) y₂ = -y₂ := negY_eq _ y₂
      by_cases hxy : x₁ = x₂ ∧ y₁ = -y₂
      · rw [WeierstrassCurve.Affine.Point.add_of_Y_eq hxy.1 (hneg₁.symm ▸ hxy.2),
          pointMap_zero]
        rw [WeierstrassCurve.Affine.Point.add_of_Y_eq
          (congrArg (beta * ·) hxy.1) (hneg₂.symm ▸ hxy.2)]
      · have hxy' : ¬(beta * x₁ = beta * x₂ ∧ y₁ = -y₂) := by
          intro h
          exact hxy ⟨beta_mul_injective h.1, h.2⟩
        rw [WeierstrassCurve.Affine.Point.add_some (hneg₁ ▸ hxy),
          pointMap_some,
          WeierstrassCurve.Affine.Point.add_some (hneg₂ ▸ hxy')]
        simp only [WeierstrassCurve.Affine.Point.some.injEq]
        rw [slope_beta, addX_beta, addY_beta]
        exact ⟨rfl, rfl⟩


def hom : Bridge.W.Point →+ Bridge.W.Point where
  toFun := pointMap
  map_zero' := rfl
  map_add' := pointMap_add

@[simp] lemma hom_apply (P : Bridge.W.Point) : hom P = pointMap P := rfl

lemma beta_quad : beta ^ 2 + beta + 1 = 0 := by decide

lemma beta_sq_ne_beta : beta ^ 2 ≠ beta := by
  intro h
  have hz : beta * (beta - 1) = 0 := by
    rw [pow_two] at h
    linear_combination h
  rcases mul_eq_zero.mp hz with hb | hb
  · exact beta_ne_zero hb
  · exact (sub_ne_zero.mpr (by decide)) hb

private lemma seven_ne_zero : (7 : Fp) ≠ 0 := by
  have h : ((7 : ℕ) : Fp) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hdvd
    have hle : p ≤ 7 := Nat.le_of_dvd (by norm_num) hdvd
    have hp : 7 < p := by norm_num [p]
    omega
  simpa using h

private lemma y_ne_neg_of_x_zero {y : Fp} (h : Bridge.W.Nonsingular 0 y) :
    y ≠ Bridge.W.negY 0 y := by
  simp only [WeierstrassCurve.Affine.negY, Bridge.W, zero_mul, sub_zero]
  intro hy
  have h2y : (2 : Fp) * y = 0 := by linear_combination hy
  have hy0 : y = 0 := (mul_eq_zero.mp h2y).resolve_left two_ne_zero_fp
  have heq := h.1
  rw [WeierstrassCurve.Affine.equation_iff] at heq
  simp [Bridge.W, hy0] at heq
  exact seven_ne_zero heq.symm


theorem hom_quadratic (P : Bridge.W.Point) : hom (hom P) + hom P + P = 0 := by
  cases P with
  | zero => rfl
  | @some x y h =>
    change
      (WeierstrassCurve.Affine.Point.some (nonsingular_beta (nonsingular_beta h)) :
          Bridge.W.Point) +
          WeierstrassCurve.Affine.Point.some (nonsingular_beta h) +
        WeierstrassCurve.Affine.Point.some h = 0
    by_cases hx : x = 0
    · subst x
      have hy : y ≠ Bridge.W.negY 0 y := y_ne_neg_of_x_zero h
      have hy₁ : y ≠ Bridge.W.negY (beta * 0) y := by simpa using hy
      have hy₂ : y ≠ Bridge.W.negY (beta * (beta * 0)) y := by simpa using hy
      have hs : Bridge.W.slope (beta * (beta * 0)) (beta * (beta * 0)) y y = 0 := by
        rw [WeierstrassCurve.Affine.slope_of_Y_ne (by ring) hy₂]
        simp [Bridge.W, WeierstrassCurve.Affine.negY]
      have hadd :
          (WeierstrassCurve.Affine.Point.some (nonsingular_beta (nonsingular_beta h)) :
              Bridge.W.Point) + WeierstrassCurve.Affine.Point.some (nonsingular_beta h) =
            -WeierstrassCurve.Affine.Point.some h := by
        rw [WeierstrassCurve.Affine.Point.add_of_Y_ne hy₂,
          WeierstrassCurve.Affine.Point.neg_some]
        simp only [WeierstrassCurve.Affine.Point.some.injEq]
        rw [hs]
        simp [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
          WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY, Bridge.W]
      rw [hadd, neg_add_cancel]
    · have hX : beta * (beta * x) ≠ beta * x := by
        intro heq
        have heq' : (beta ^ 2 - beta) * x = 0 := by
          rw [pow_two]
          linear_combination heq
        exact hx ((mul_eq_zero.mp heq').resolve_left (sub_ne_zero.mpr beta_sq_ne_beta))
      have hs : Bridge.W.slope (beta * (beta * x)) (beta * x) y y = 0 := by
        rw [WeierstrassCurve.Affine.slope_of_X_ne hX]
        simp
      have hquadx : beta ^ 2 * x + beta * x + x = 0 := by
        calc
          beta ^ 2 * x + beta * x + x = (beta ^ 2 + beta + 1) * x := by ring
          _ = 0 := by rw [beta_quad, zero_mul]
      have hab : beta ^ 2 * x + beta * x = -x :=
        eq_neg_of_add_eq_zero_left hquadx
      have hxcoord : Bridge.W.addX (beta * (beta * x)) (beta * x) 0 = x := by
        simp only [WeierstrassCurve.Affine.addX, Bridge.W]
        rw [show beta * (beta * x) = beta ^ 2 * x by ring]
        calc
          -(beta ^ 2 * x) - beta * x = -(beta ^ 2 * x + beta * x) := by ring
          _ = x := by rw [hab, neg_neg]
      have hycoord :
          Bridge.W.addY (beta * (beta * x)) (beta * x) y 0 = Bridge.W.negY x y := by
        rw [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY, hxcoord]
        simp
      have hadd :
          (WeierstrassCurve.Affine.Point.some (nonsingular_beta (nonsingular_beta h)) :
              Bridge.W.Point) + WeierstrassCurve.Affine.Point.some (nonsingular_beta h) =
            -WeierstrassCurve.Affine.Point.some h := by
        rw [WeierstrassCurve.Affine.Point.add_of_X_ne hX,
          WeierstrassCurve.Affine.Point.neg_some]
        simp only [WeierstrassCurve.Affine.Point.some.injEq]
        rw [hs]
        exact ⟨hxcoord, hycoord⟩
      rw [hadd, neg_add_cancel]

end Solution.Secp256k1ScalarMul.Phi
