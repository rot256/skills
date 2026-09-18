import Solution.Secp256k1ScalarMul.GLVFinal
import Solution.Secp256k1ScalarMul.ShortCoeffs

namespace Solution.Secp256k1ScalarMul.FakeGLVSound

open Specs.Secp256k1

private lemma zsmul_eq_zero_of_cast_eq_zero (a : ℤ) (P : Bridge.W.Point)
    (ha : (a : ZMod order) = 0) : a • P = 0 := by
  have hd : (order : ℤ) ∣ a :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp ha
  obtain ⟨t, rfl⟩ := hd
  rw [mul_zsmul, GLVAlgebra.natCast_zsmul_eq_nsmul,
    GLVFinal.order_nsmul_all]

private lemma zsmul_eq_of_cast_eq {a b : ℤ} (P : Bridge.W.Point)
    (h : (a : ZMod order) = (b : ZMod order)) : a • P = b • P := by
  have hz : ((a - b : ℤ) : ZMod order) = 0 := by
    simpa only [Int.cast_sub, sub_eq_zero] using h
  have hs := zsmul_eq_zero_of_cast_eq_zero (a - b) P hz
  rw [sub_zsmul] at hs
  have hs' : a • P - b • P = 0 := by
    simpa only [sub_eq_add_neg] using hs
  exact sub_eq_zero.mp hs'

private lemma phi_eq_lambda_zsmul (P : Bridge.W.Point) :
    Phi.hom P = (GLVAlgebra.lambda : ℤ) • P := by
  calc
    Phi.hom P = GLVAlgebra.lambda • P := GLVFinal.hom_eq_lambda_nsmul P
    _ = (GLVAlgebra.lambda : ℤ) • P :=
      (GLVAlgebra.natCast_zsmul_eq_nsmul GLVAlgebra.lambda P).symm

theorem sound
    (P Q : Bridge.W.Point) (k : ℕ) (u₁ u₂ v₁ v₂ : ℤ)
    (hgroup : u₁ • P + u₂ • Phi.hom P + v₁ • Q + v₂ • Phi.hom Q = 0)
    (hscalar :
      (u₁ : ZMod order) + (GLVAlgebra.lambda : ZMod order) * (u₂ : ZMod order) +
        (k : ZMod order) *
          ((v₁ : ZMod order) + (GLVAlgebra.lambda : ZMod order) * (v₂ : ZMod order)) = 0)
    (hV : (v₁ : ZMod order) +
      (GLVAlgebra.lambda : ZMod order) * (v₂ : ZMod order) ≠ 0) :
    Q = k • P := by
  let U : ℤ := u₁ + u₂ * (GLVAlgebra.lambda : ℤ)
  let V : ℤ := v₁ + v₂ * (GLVAlgebra.lambda : ℤ)
  have hgroup' : U • P + V • Q = 0 := by
    rw [phi_eq_lambda_zsmul, phi_eq_lambda_zsmul] at hgroup
    dsimp [U, V]
    rw [add_zsmul, add_zsmul, mul_zsmul, mul_zsmul]
    simpa only [add_assoc] using hgroup
  have hscalar' : (U : ZMod order) + (k : ZMod order) * (V : ZMod order) = 0 := by
    simpa only [U, V, Int.cast_add, Int.cast_mul, Int.cast_natCast,
      mul_comm] using hscalar
  have hV' : (V : ZMod order) ≠ 0 := by
    simpa only [V, Int.cast_add, Int.cast_mul, mul_comm] using hV
  have hDcast : ((U + V * (k : ℤ) : ℤ) : ZMod order) = 0 := by
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast, mul_comm] using hscalar'
  have hDP := zsmul_eq_zero_of_cast_eq_zero (U + V * (k : ℤ)) P hDcast
  have hDP' : U • P + V • ((k : ℤ) • P) = 0 := by
    simpa only [add_zsmul, mul_zsmul] using hDP
  have hUP : U • P = -(V • ((k : ℤ) • P)) :=
    eq_neg_of_add_eq_zero_left hDP'
  have hVK : V • (Q - k • P) = 0 := by
    rw [← GLVAlgebra.natCast_zsmul_eq_nsmul k P, zsmul_sub]
    calc
      V • Q - V • ((k : ℤ) • P) =
          V • Q + -(V • ((k : ℤ) • P)) := sub_eq_add_neg _ _
      _ = V • Q + U • P := by rw [← hUP]
      _ = U • P + V • Q := add_comm _ _
      _ = 0 := hgroup'
  let r : ℕ := (V : ZMod order).val
  have hr0 : r ≠ 0 := by
    intro hr
    apply hV'
    rw [← ZMod.natCast_zmod_val (V : ZMod order)]
    simp [r, hr]
  have hrlt : r < order := ZMod.val_lt _
  have hrndvd : ¬ order ∣ r := by
    intro hd
    exact hr0 (Nat.eq_zero_of_dvd_of_lt hd hrlt)
  have hcastVr : (V : ZMod order) = ((r : ℕ) : ZMod order) := by
    exact (ZMod.natCast_zmod_val (V : ZMod order)).symm
  have hVr : V • (Q - k • P) = r • (Q - k • P) := by
    calc
      V • (Q - k • P) = (r : ℤ) • (Q - k • P) :=
        zsmul_eq_of_cast_eq (Q - k • P) hcastVr
      _ = r • (Q - k • P) :=
        GLVAlgebra.natCast_zsmul_eq_nsmul r (Q - k • P)
  have hrzero : r • (Q - k • P) = 0 := by rw [← hVr]; exact hVK
  have hdiff : Q - k • P = 0 := by
    apply GLVFinal.nsmul_right_injective_of_not_order_dvd hrndvd
    simpa using hrzero
  exact sub_eq_zero.mp hdiff

theorem complete
    (P : Bridge.W.Point) (k : ℕ) (u₁ u₂ v₁ v₂ : ℤ)
    (hscalar :
      (u₁ : ZMod order) + (GLVAlgebra.lambda : ZMod order) * (u₂ : ZMod order) +
        (k : ZMod order) *
          ((v₁ : ZMod order) + (GLVAlgebra.lambda : ZMod order) * (v₂ : ZMod order)) = 0) :
    u₁ • P + u₂ • Phi.hom P + v₁ • (k • P) + v₂ • Phi.hom (k • P) = 0 := by
  let D : ℤ := u₁ + (GLVAlgebra.lambda : ℤ) * u₂ +
    (k : ℤ) * (v₁ + (GLVAlgebra.lambda : ℤ) * v₂)
  have hDcast : (D : ZMod order) = 0 := by
    simpa only [D, Int.cast_add, Int.cast_mul, Int.cast_natCast] using hscalar
  have hDz : D • P = 0 := zsmul_eq_zero_of_cast_eq_zero D P hDcast
  rw [phi_eq_lambda_zsmul, phi_eq_lambda_zsmul,
    ← GLVAlgebra.natCast_zsmul_eq_nsmul k P]
  calc
    u₁ • P + u₂ • ((GLVAlgebra.lambda : ℤ) • P) +
          v₁ • ((k : ℤ) • P) +
        v₂ • ((GLVAlgebra.lambda : ℤ) • ((k : ℤ) • P)) =
        D • P := by
      simp only [← add_zsmul, ← mul_zsmul]
      congr 1
      dsimp [D]
      ring
    _ = 0 := hDz

end Solution.Secp256k1ScalarMul.FakeGLVSound
