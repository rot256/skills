import Solution.Secp256k1ScalarMul.Bridge
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.BinaryRec
import Solution.Secp256k1ScalarMul.PrimeCertificate
import Solution.Secp256k1ScalarMul.BetaCertificate

namespace Solution.Secp256k1ScalarMul.ProofBlocker

open Specs.ShortWeierstrass Specs.Secp256k1

def pointXY : Bridge.W.Point → Option (Fp × Fp)
  | .zero => none
  | @WeierstrassCurve.Affine.Point.some _ _ _ x y _ => some (x, y)

lemma pointXY_injective : Function.Injective pointXY := by
  intro P Q h
  cases P with
  | zero => cases Q <;> simp [pointXY] at h ⊢
  | some hP =>
      cases Q with
      | zero => simp [pointXY] at h
      | some hQ =>
          simp only [pointXY, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          rfl

instance pointFinite : Finite Bridge.W.Point :=
  Finite.of_injective pointXY pointXY_injective

def pointX : Bridge.W.Point → Option Fp
  | .zero => none
  | @WeierstrassCurve.Affine.Point.some _ _ _ x _ _ => some x

lemma point_eq_or_eq_neg_of_x (P Q : Bridge.W.Point)
    (hX : pointX P = pointX Q) : P = Q ∨ P = -Q := by
  cases P with
  | zero =>
      cases Q with
      | zero => exact Or.inl rfl
      | some hQ => simp [pointX] at hX
  | some hP =>
      cases Q with
      | zero => simp [pointX] at hX
      | @some x2 y2 hQ =>
          rename_i x1 y1
          simp only [pointX, Option.some.injEq] at hX
          subst x2
          have h1 := Bridge.onCurve_of_equation hP.1
          have h2 := Bridge.onCurve_of_equation hQ.1
          rw [onCurve_iff] at h1 h2
          have hy : y1 ^ 2 = y2 ^ 2 := by linear_combination h1 - h2
          rcases sq_eq_sq_iff_eq_or_eq_neg.mp hy with hy | hy
          · left
            subst y2
            rfl
          · right
            rw [WeierstrassCurve.Affine.Point.neg_some]
            simp only [WeierstrassCurve.Affine.negY, Bridge.W]
            subst y1
            apply Bridge.toSpec_injective
            simp [Bridge.toSpec]

theorem point_card_le : Nat.card Bridge.W.Point ≤ 2 * (p + 1) := by
  classical
  letI := Fintype.ofFinite Bridge.W.Point
  have hfiber : ∀ b ∈ (Finset.univ.image pointX),
      (Finset.univ.filter (fun Q : Bridge.W.Point => pointX Q = b)).card ≤ 2 := by
    intro b hb
    obtain ⟨P, -, rfl⟩ := Finset.mem_image.mp hb
    calc
      (Finset.univ.filter (fun Q : Bridge.W.Point => pointX Q = pointX P)).card
          ≤ ({P, -P} : Finset Bridge.W.Point).card := by
            apply Finset.card_le_card
            intro Q hQ
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hQ
            simp only [Finset.mem_insert, Finset.mem_singleton]
            exact point_eq_or_eq_neg_of_x Q P hQ
      _ ≤ 2 := Finset.card_le_two
  calc
    Nat.card Bridge.W.Point = (Finset.univ : Finset Bridge.W.Point).card := by
      rw [Nat.card_eq_fintype_card, Fintype.card]
    _ ≤ 2 * (Finset.univ.image pointX).card :=
      Finset.card_le_mul_card_image Finset.univ 2 hfiber
    _ ≤ 2 * (Finset.univ : Finset (Option Fp)).card := by
      exact Nat.mul_le_mul_left 2 (Finset.card_le_card (Finset.subset_univ _))
    _ = 2 * (p + 1) := by simp [ZMod.card]

lemma negSeven_cubic_character :
    ((-7 : Fp) ^ ((p - 1) / 3)) ≠ 1 := by
  exact CheckFastPow.beta_character_ne_one

lemma seven_ne_zero : (7 : Fp) ≠ 0 := by
  have h : ((7 : ℕ) : Fp) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hdvd
    have hle : p ≤ 7 := Nat.le_of_dvd (by norm_num) hdvd
    have hp : 7 < p := by norm_num [p]
    omega
  simpa using h

set_option maxRecDepth 4096 in
theorem noOrderTwo : NoOrderTwo curve := by
  intro P hP hy
  rw [onCurve_iff] at hP
  have hx3 : P.x ^ 3 = (-7 : Fp) := by
    rw [hy] at hP
    simpa using (eq_neg_of_add_eq_zero_left hP.symm)
  have hx0 : P.x ≠ 0 := by
    intro hx0
    rw [hx0] at hx3
    have hneg : (-7 : Fp) = 0 := by simpa using hx3.symm
    exact seven_ne_zero (neg_eq_zero.mp hneg)
  have hpow := congrArg (fun z : Fp => z ^ ((p - 1) / 3)) hx3
  have hdiv : 3 * ((p - 1) / 3) = p - 1 := by
    norm_num [p]
  have hleft : (P.x ^ 3) ^ ((p - 1) / 3) = 1 := by
    rw [← pow_mul, hdiv]
    exact ZMod.pow_card_sub_one_eq_one hx0
  exact negSeven_cubic_character (hpow.symm.trans hleft)

theorem two_not_dvd_point_card : ¬ 2 ∣ Nat.card Bridge.W.Point := by
  intro htwo
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := exists_prime_addOrderOf_dvd_card' 2 htwo
  have hPspec := addOrderOf_eq_prime_iff.mp hP
  obtain ⟨h2P, hP0⟩ := hPspec
  cases P with
  | zero => exact hP0 rfl
  | @some x y hxy =>
      have hneg : (WeierstrassCurve.Affine.Point.some hxy : Bridge.W.Point) =
          -(WeierstrassCurve.Affine.Point.some hxy : Bridge.W.Point) := by
        apply eq_neg_of_add_eq_zero_left
        simpa [two_nsmul] using h2P
      rw [WeierstrassCurve.Affine.Point.neg_some] at hneg
      have hys : y = -y := by
        simp only [WeierstrassCurve.Affine.Point.some.injEq,
          WeierstrassCurve.Affine.negY, Bridge.W, sub_zero, zero_mul] at hneg
        exact hneg.2
      have hy0 : y = 0 := by
        have hmul : (2 : Fp) * y = 0 := by linear_combination hys
        exact (mul_eq_zero.mp hmul).resolve_left two_ne_zero_fp
      exact noOrderTwo { x := x, y := y } (Bridge.onCurve_of_equation hxy.1) hy0

lemma order_prime : order.Prime := CheckLucas.order_prime

instance orderPrimeFact : Fact order.Prime := ⟨order_prime⟩

lemma G_onCurve : OnCurve curve G := by decide

def gPoint : Bridge.W.Point := Bridge.mkPoint G G_onCurve

lemma gPoint_ne_zero : gPoint ≠ 0 := by
  exact WeierstrassCurve.Affine.Point.some_ne_zero _

lemma addOrderOf_gPoint (horder : order • gPoint = 0) :
    addOrderOf gPoint = order :=
  addOrderOf_eq_prime horder gPoint_ne_zero

lemma order_dvd_point_card (horder : order • gPoint = 0) :
    order ∣ Nat.card Bridge.W.Point := by
  rw [← addOrderOf_gPoint horder]
  exact addOrderOf_dvd_natCard gPoint

theorem point_card_eq_order_of_order_nsmul (horder : order • gPoint = 0) :
    Nat.card Bridge.W.Point = order := by
  obtain ⟨m, hm⟩ := order_dvd_point_card horder
  have hlt : Nat.card Bridge.W.Point < 3 * order := by
    exact lt_of_le_of_lt point_card_le (by norm_num [p, order])
  rw [hm] at hlt
  have hord : 0 < order := by norm_num [order]
  have hm3 : m < 3 := by
    apply (Nat.mul_lt_mul_left hord).mp
    simpa [Nat.mul_comm] using hlt
  have hm0 : m ≠ 0 := by
    intro hmzero
    subst m
    simp at hm
    have hcard : Nat.card Bridge.W.Point ≠ 0 :=
      Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩
    exact hcard hm
  have hm12 : m = 1 ∨ m = 2 := by omega
  rcases hm12 with rfl | rfl
  · simpa using hm
  · exfalso
    apply two_not_dvd_point_card
    rw [hm]
    exact ⟨order, by omega⟩

theorem order_nsmul_all (horder : order • gPoint = 0)
    (Q : Bridge.W.Point) : order • Q = 0 := by
  rw [← point_card_eq_order_of_order_nsmul horder]
  exact card_nsmul_eq_zero'

theorem exists_zsmul_gPoint (horder : order • gPoint = 0)
    (Q : Bridge.W.Point) : ∃ z : ℤ, z • gPoint = Q := by
  apply AddSubgroup.mem_zmultiples_iff.mp
  exact mem_zmultiples_of_prime_card
    (point_card_eq_order_of_order_nsmul horder) gPoint_ne_zero

theorem nsmul_right_injective_of_not_order_dvd
    (horder : order • gPoint = 0) {a : ℕ} (ha : ¬ order ∣ a) :
    Function.Injective (fun Q : Bridge.W.Point ↦ a • Q) := by
  have hcard := point_card_eq_order_of_order_nsmul horder
  have hcop : (Nat.card Bridge.W.Point).Coprime a := by
    rw [hcard]
    exact order_prime.coprime_iff_not_dvd.mpr ha
  exact (Nat.Coprime.nsmul_right_bijective hcop).injective

end Solution.Secp256k1ScalarMul.ProofBlocker
