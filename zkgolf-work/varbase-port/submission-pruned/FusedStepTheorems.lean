import Solution.Secp256k1ScalarMul.CompleteAddTheorems
import Solution.Secp256k1ScalarMul.Bridge
import Solution.Secp256k1ScalarMul.ProofBlocker
import Solution.Secp256k1ScalarMul.CancelTheorems
import Solution.Secp256k1ScalarMul.OrderFactsCerts

/-!
# Value-level soundness core for the fused double-add step

`fused_soundness_core` proves that the ELM λ-chain of `FusedStep` computes
`(R + R) + T` under the complete group law, taking all circuit facts in
decoded form.

Structure (R, T finite, not the cancellation case):
* `S := (xS, yS)` with the ghost `yS := λ₁·(R.x − xS) − R.y` equals
  `add R T` — tangent branch when `T.x = R.x` (then `T = R`), chord otherwise.
* If `xS = R.x` then `yS = −R.y`, so `S = −R` and `add S R = 𝒪`; the circuit
  raises exactly the `zOut` flag.  No torsion facts are needed: whenever the
  flag fires, 𝒪 is the correct answer.
* Otherwise the second chord: the slope of `(S, R)` is `−(λ₁ + w)` where
  `w·(xS − R.x) = 2·R.y`, and squaring absorbs the sign:
  `x₄ = (λ₁+w)² − xS − R.x`, `y₄ = (λ₁+w)·(x₄ − R.x) − R.y`.
* `(R+T)+R = (R+R)+T` closes the generic branch through the Mathlib bridge.
-/

namespace Solution.Secp256k1ScalarMul
namespace FusedStepTheorems

open Specs.ShortWeierstrass Specs.Secp256k1
open CompleteAdd

/-- Group-law commutation: `(a+b)+a = (a+a)+b` at the bridge level. -/
lemma add_rot (a b : Bridge.W.Point) :
    add curve (add curve (Bridge.toSpec a) (Bridge.toSpec b)) (Bridge.toSpec a)
      = add curve (add curve (Bridge.toSpec a) (Bridge.toSpec a)) (Bridge.toSpec b) := by
  rw [← Bridge.bridge_add, ← Bridge.bridge_add, ← Bridge.bridge_add, ← Bridge.bridge_add]
  congr 1
  abel

/-- Wrapper for `add_rot` on spec-level points known to be on the curve. -/
lemma add_rot' (G H : GroupPoint Fp)
    (hG : OnCurveOrInfinity curve G) (hH : OnCurveOrInfinity curve H) :
    add curve (add curve G H) G = add curve (add curve G G) H := by
  have ha := Bridge.toSpec_fromSpec G hG
  have hb := Bridge.toSpec_fromSpec H hH
  rw [← ha, ← hb, add_rot]

/-- Cancellation branch: `(b+b) + (−b) = b`. -/
lemma add_dbl_neg (b : Bridge.W.Point) :
    add curve (add curve (Bridge.toSpec b) (Bridge.toSpec b)) (Bridge.toSpec (-b))
      = Bridge.toSpec b := by
  rw [← Bridge.bridge_add, ← Bridge.bridge_add]
  rw [show b + b + -b = b by abel]

/-- `toSpec` of a negated finite bridge point is the y-negated affine point. -/
lemma toSpec_neg_mk (P : Point Fp) (hP : OnCurve curve P) :
    Bridge.toSpec (-(Bridge.mkPoint P hP)) = .affine ⟨P.x, -P.y⟩ := by
  rw [Bridge.mkPoint, WeierstrassCurve.Affine.Point.neg_some]
  simp [Bridge.toSpec, WeierstrassCurve.Affine.negY, Bridge.W]

lemma toSpec_mk (P : Point Fp) (hP : OnCurve curve P) :
    Bridge.toSpec (Bridge.mkPoint P hP) = .affine P := rfl

/-- Nonzero doubled y-coordinate for finite on-curve points. -/
lemma two_y_ne_zero {P : Point Fp} (hP : OnCurve curve P) : P.y + P.y ≠ 0 := by
  intro h
  apply ProofBlocker.noOrderTwo P hP
  have h2 : (2 : Fp) * P.y = 0 := by linear_combination h
  rcases mul_eq_zero.mp h2 with h' | h'
  · exact absurd h' CompleteAdd.two_ne_zero_fp
  · exact h'

/-- The affine double is the tangent point (no order-2 points on secp256k1). -/
lemma add_self_eq_tangent (P : Point Fp) (hP : OnCurve curve P) :
    add curve (.affine P) (.affine P) = .affine (tangent curve P) := by
  rw [show (P : Point Fp) = ⟨P.x, P.y⟩ from rfl, add_affine]
  rw [if_pos rfl, if_neg (fun h : P.y = -P.y => two_y_ne_zero hP (by linear_combination h))]

end FusedStepTheorems
end Solution.Secp256k1ScalarMul
