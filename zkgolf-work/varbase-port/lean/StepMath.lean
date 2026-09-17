import Solution.Secp256k1ScalarMul.FusedStepTheorems

/-!
# Value-level group law for the lazy chain step `R' = (R + T) + R`

Pure field-level statements: from the certified relations (chord, unified,
two-slope identity, and the cancellation flags) the outputs decode to the
complete group law.
-/

namespace Solution.Secp256k1ScalarMul.Lazy.StepMath

open Specs.ShortWeierstrass Specs.Secp256k1
open Solution.Secp256k1ScalarMul
open FusedStepTheorems

set_option autoImplicit false

/-- `S = R + T` from the chord and unified relations (the unified relation pins the
tangent when `T = R`; `T = −R` is impossible under the chord). -/
theorem first_add {rx ry tx ty aF : Fp}
    (hR : ry ^ 2 = rx ^ 3 + 7) (hT : ty ^ 2 = tx ^ 3 + 7)
    (hchord : aF * (tx - rx) = ty - ry)
    (huni : aF * (ry + ty) = rx ^ 2 + rx * tx + tx ^ 2) :
    (aF * (rx - (aF * aF - rx - tx)) - ry) ^ 2 = (aF * aF - rx - tx) ^ 3 + 7 ∧
    add curve (.affine ⟨rx, ry⟩) (.affine ⟨tx, ty⟩) =
      .affine ⟨aF * aF - rx - tx, aF * (rx - (aF * aF - rx - tx)) - ry⟩ := by
  have h2ry : ry + ry ≠ 0 := two_y_ne_zero (P := ⟨rx, ry⟩) ((CompleteAdd.onCurve_iff _).mpr hR)
  by_cases hx : rx = tx
  · -- same x: T = R (T = −R contradicts the chord)
    subst hx
    have hy : ty = ry := by
      have := hchord
      rw [sub_self, mul_zero] at this
      linear_combination -this
    subst hy
    have htan : aF * (2 * ty) = 3 * ty ^ 0 * rx ^ 2 := by
      rw [pow_zero, mul_one]
      linear_combination huni
    constructor
    · exact CompleteAdd.tangent_oncurve (x₁ := rx) (y₁ := ty) hR (by linear_combination htan)
        rfl rfl
    · rw [add_self_eq_tangent ⟨rx, ty⟩ ((CompleteAdd.onCurve_iff _).mpr hR),
        CompleteAdd.tangent_eq]
      have hs : (3 * rx ^ 2 + 0) / (2 * ty) = aF := by
        rw [div_eq_iff (by intro h; apply h2ry; linear_combination h)]
        linear_combination -htan
      simp only [Specs.Secp256k1.curve, hs, GroupPoint.affine.injEq, Point.mk.injEq]
      constructor <;> ring
  · have hne : tx - rx ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
    constructor
    · exact CompleteAdd.chord_oncurve (x₁ := rx) (y₁ := ry) (x₂ := tx) (y₂ := ty) hR hT hne
        hchord rfl rfl
    · rw [CompleteAdd.add_affine, if_neg hx, CompleteAdd.chord_eq]
      have hs : (ty - ry) / (tx - rx) = aF := by
        rw [div_eq_iff hne]; exact hchord.symm
      simp only [hs, GroupPoint.affine.injEq, Point.mk.injEq]
      constructor <;> ring

/-- Cancellation `T = −R`: the result is `R`. -/
theorem cancel_core {rx ry : Fp} (hR : ry ^ 2 = rx ^ 3 + 7) :
    add curve (add curve (.affine ⟨rx, ry⟩) (.affine ⟨rx, ry⟩)) (.affine ⟨rx, -ry⟩) =
      .affine ⟨rx, ry⟩ := by
  have hon : OnCurve curve (⟨rx, ry⟩ : Point Fp) := (CompleteAdd.onCurve_iff _).mpr hR
  have h := add_dbl_neg (Bridge.mkPoint ⟨rx, ry⟩ hon)
  rwa [toSpec_neg_mk, toSpec_mk] at h

/-- `S = −R` (same x, opposite y by the chord formula): the result is `𝒪`. -/
theorem second_inf {rx ry xS yS tx ty : Fp} (hR : ry ^ 2 = rx ^ 3 + 7) (hT : ty ^ 2 = tx ^ 3 + 7)
    (hS : add curve (.affine ⟨rx, ry⟩) (.affine ⟨tx, ty⟩) = .affine ⟨xS, yS⟩)
    (hxS : xS = rx) (hyS : yS = -ry) :
    add curve (add curve (.affine ⟨rx, ry⟩) (.affine ⟨rx, ry⟩)) (.affine ⟨tx, ty⟩) =
      .infinity := by
  rw [← add_rot' _ _ ((CompleteAdd.onCurve_iff _).mpr hR) ((CompleteAdd.onCurve_iff _).mpr hT),
    hS, CompleteAdd.add_affine, if_pos hxS, if_pos (by rw [hyS])]

/-- Generic second addition through the two-slope identity. -/
theorem second_add {rx ry xS yS tx ty aF bF : Fp}
    (hR : ry ^ 2 = rx ^ 3 + 7) (hT : ty ^ 2 = tx ^ 3 + 7)
    (hSon : yS ^ 2 = xS ^ 3 + 7)
    (hS : add curve (.affine ⟨rx, ry⟩) (.affine ⟨tx, ty⟩) = .affine ⟨xS, yS⟩)
    (hyS : yS = aF * (rx - xS) - ry)
    (hne : xS ≠ rx)
    (hrel2 : (aF + bF) * (rx - xS) = 2 * ry) :
    (bF * (rx - (bF * bF - xS - rx)) - ry) ^ 2 = (bF * bF - xS - rx) ^ 3 + 7 ∧
    add curve (add curve (.affine ⟨rx, ry⟩) (.affine ⟨rx, ry⟩)) (.affine ⟨tx, ty⟩) =
      .affine ⟨bF * bF - xS - rx, bF * (rx - (bF * bF - xS - rx)) - ry⟩ := by
  have hRon : OnCurve curve (⟨rx, ry⟩ : Point Fp) := (CompleteAdd.onCurve_iff _).mpr hR
  have hTon : OnCurve curve (⟨tx, ty⟩ : Point Fp) := (CompleteAdd.onCurve_iff _).mpr hT
  have hSon' : OnCurve curve (⟨xS, yS⟩ : Point Fp) := (CompleteAdd.onCurve_iff _).mpr hSon
  have hd : xS - rx ≠ 0 := sub_ne_zero.mpr hne
  -- b is the chord slope of (R, S)
  have hb : bF * (xS - rx) = yS - ry := by
    rw [hyS]; linear_combination -hrel2
  constructor
  · exact CompleteAdd.chord_oncurve (x₁ := rx) (y₁ := ry) (x₂ := xS) (y₂ := yS) hR hSon hd hb
      rfl rfl
  · rw [← add_rot' _ _ hRon hTon, hS]
    -- add S R = add R S (commutativity through the bridge)
    have hcomm : add curve (.affine ⟨xS, yS⟩) (.affine ⟨rx, ry⟩) =
        add curve (.affine ⟨rx, ry⟩) (.affine ⟨xS, yS⟩) := by
      rw [← toSpec_mk _ hSon', ← toSpec_mk _ hRon, ← Bridge.bridge_add, ← Bridge.bridge_add,
        add_comm]
    rw [hcomm, CompleteAdd.add_affine, if_neg (Ne.symm hne), CompleteAdd.chord_eq]
    have hs : (yS - ry) / (xS - rx) = bF := by
      rw [div_eq_iff hd]; exact hb.symm
    simp only [hs, GroupPoint.affine.injEq, Point.mk.injEq]
    constructor <;> ring

end Solution.Secp256k1ScalarMul.Lazy.StepMath
