import Solution.Secp256k1ScalarMul.CompleteAddTheorems
import Solution.Secp256k1ScalarMul.ProofBlocker

namespace Solution.Secp256k1ScalarMul

open Specs.ShortWeierstrass Specs.Secp256k1

lemma same_x_y_eq_or_opp
    {P Q : FlaggedPoint (F circomPrime)}
    (hP : P.Valid) (hQ : Q.Valid)
    (hPf : P.isInf = 0) (hQf : Q.isInf = 0)
    (hx : decodeFe Q.x = decodeFe P.x) :
    decodeFe Q.y = decodeFe P.y ∨ decodeFe P.y + decodeFe Q.y = 0 := by
  have hPc := hP.2.2.2 hPf
  have hQc := hQ.2.2.2 hQf
  rw [onCurve_iff] at hPc hQc
  have hs : (decodeFe Q.y - decodeFe P.y) *
      (decodeFe Q.y + decodeFe P.y) = 0 := by
    rw [mul_add, sub_mul]
    rw [hx] at hQc
    linear_combination hQc - hPc
  rcases mul_eq_zero.mp hs with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (by rw [add_comm]; exact h)

lemma value_mod_base_eq_limb0 (y : Emu (F circomPrime))
    (hy : BigInt.Normalized limbBits y) :
    BigInt.value limbBits y % 2 ^ limbBits = y[0].val := by
  rw [BigInt.value_eq_sum]
  rw [show (∑ k : Fin numLimbs, y[k].val * 2 ^ (limbBits * k.val)) =
      y[0].val + (y[1].val + y[2].val * 2 ^ limbBits +
        y[3].val * 2 ^ (2 * limbBits)) * 2 ^ limbBits by
    simp only [numLimbs, Fin.sum_univ_four, Fin.val_zero, Fin.val_one, limbBits]
    norm_num
    ring]
  rw [Nat.add_mul_mod_self_right]
  exact Nat.mod_eq_of_lt (hy 0)

/-- Opposite nonzero canonical field representatives cannot have equal low
64-bit limbs: their natural representatives sum to the secp256k1 prime, whose
low limb is odd. -/
lemma opposite_y_low_limb_ne
    {y₁ y₂ : Emu (F circomPrime)}
    (hy₁ : Fe.Valid y₁) (hy₂ : Fe.Valid y₂)
    (hopp : decodeFe y₁ + decodeFe y₂ = 0)
    (hy₁0 : decodeFe y₁ ≠ 0) :
    y₁[0] ≠ y₂[0] := by
  intro hlow
  let a := BigInt.value limbBits y₁
  let b := BigInt.value limbBits y₂
  have ha : a < P256 := hy₁.2
  have hb : b < P256 := hy₂.2
  have ha0 : a ≠ 0 := by
    intro h
    apply hy₁0
    simp [decodeFe, a, h]
  have hsum : a + b = P256 := by
    have hz : ((a + b : ℕ) : F P256) = 0 := by
      push_cast
      simpa only [decodeFe, a, b] using hopp
    have hdvd : P256 ∣ a + b := (ZMod.natCast_eq_zero_iff _ _).mp hz
    have hlt : a + b < 2 * P256 := by omega
    rcases hdvd with ⟨k, hk⟩
    have hkpos : 0 < k := by
      by_contra hk0
      have : k = 0 := by omega
      subst k
      simp only [Nat.mul_zero] at hk
      omega
    have hklt : k < 2 := by
      rw [hk] at hlt
      nlinarith [show 0 < P256 by decide]
    have : k = 1 := by omega
    subst k
    simpa [Nat.mul_one] using hk
  have hmod := congrArg (fun x : ℕ => x % 2 ^ limbBits) hsum
  change (a + b) % 2 ^ limbBits = P256 % 2 ^ limbBits at hmod
  rw [Nat.add_mod, value_mod_base_eq_limb0 y₁ hy₁.1,
    value_mod_base_eq_limb0 y₂ hy₂.1] at hmod
  have hv := congrArg ZMod.val hlow
  rw [hv] at hmod
  have hpar := congrArg (fun x : ℕ => x % 2) hmod
  change ((y₂[0].val + y₂[0].val) % 18446744073709551616) % 2 =
    (115792089237316195423570985008687907853269984665640564039457584007908834671663 %
      18446744073709551616) % 2 at hpar
  norm_num [Nat.add_mod] at hpar
  omega

/-- For two finite secp256k1 points with equal x-coordinate, equality of the
least-significant 64-bit y limb already decides equality of the full canonical
y-coordinate. -/
lemma low_y_eq_iff_of_same_x
    {P Q : FlaggedPoint (F circomPrime)}
    (hP : P.Valid) (hQ : Q.Valid)
    (hPf : P.isInf = 0) (hQf : Q.isInf = 0)
    (hx : decodeFe Q.x = decodeFe P.x) :
    P.y[0] = Q.y[0] ↔ decodeFe P.y = decodeFe Q.y := by
  constructor
  · intro hlow
    rcases same_x_y_eq_or_opp hP hQ hPf hQf hx with heq | hopp
    · exact heq.symm
    · have hy0 : decodeFe P.y ≠ 0 := by
        intro h0
        exact ProofBlocker.noOrderTwo _ (hP.2.2.2 hPf) h0
      exact (opposite_y_low_limb_ne hP.2.2.1 hQ.2.2.1 hopp hy0 hlow).elim
  · intro heq
    have hv : P.y = Q.y := by
      apply BigInt.value_inj hP.2.2.1.1 hQ.2.2.1.1
      have hp : BigInt.value limbBits P.y < P256 := hP.2.2.1.2
      have hq : BigInt.value limbBits Q.y < P256 := hQ.2.2.1.2
      have hv := congrArg ZMod.val heq
      simpa only [decodeFe, ZMod.val_natCast_of_lt hp,
        ZMod.val_natCast_of_lt hq] using hv
    exact congrArg (fun y : Emu (F circomPrime) => y[0]) hv

/-- The two-row `CancelLow` flag agrees with `sameX * oppY` on finite points:
same-`x` finite points have equal or opposite `y`, and canonical opposites
already differ in the low 64-bit limb. -/
lemma cancelLow_eq_mul
    {P Q : FlaggedPoint (F circomPrime)}
    (hP : P.Valid) (hQ : Q.Valid) (hPf : P.isInf = 0) (hQf : Q.isInf = 0)
    {sameX cancel : F circomPrime}
    (hsameX : sameX = if decodeFe Q.x = decodeFe P.x then (1 : F circomPrime) else 0)
    (hcancel : cancel = if P.y[0] = Q.y[0] then (0 : F circomPrime) else sameX) :
    cancel = sameX * (if decodeFe P.y + decodeFe Q.y = 0 then (1 : F circomPrime) else 0) := by
  by_cases hx : decodeFe Q.x = decodeFe P.x
  · have hs1 : sameX = 1 := by rw [hsameX, if_pos hx]
    rw [hs1, one_mul]
    rw [hs1] at hcancel
    by_cases hlow : P.y[0] = Q.y[0]
    · have heq : decodeFe P.y = decodeFe Q.y :=
        (low_y_eq_iff_of_same_x hP hQ hPf hQf hx).mp hlow
      have hnot : decodeFe P.y + decodeFe Q.y ≠ 0 := by
        rw [← heq]
        intro htwo
        have hy0 : decodeFe P.y = 0 := by
          have h2 : (2 : Fp) ≠ 0 := by decide
          exact (mul_eq_zero.mp (by simpa [two_mul] using htwo)).resolve_left h2
        exact ProofBlocker.noOrderTwo _ (hP.2.2.2 hPf) hy0
      rw [hcancel, if_pos hlow, if_neg hnot]
    · have hne : decodeFe P.y ≠ decodeFe Q.y := fun h =>
        hlow ((low_y_eq_iff_of_same_x hP hQ hPf hQf hx).mpr h)
      rcases same_x_y_eq_or_opp hP hQ hPf hQf hx with hy | ho
      · exact absurd hy.symm hne
      · rw [hcancel, if_neg hlow, if_pos ho]
  · have hs0 : sameX = 0 := by rw [hsameX, if_neg hx]
    rw [hcancel, hs0, zero_mul, ite_self]

/-- Booleanity of a `CancelLow` output: it is either `0` or a boolean selector. -/
lemma isBool_of_eq_ite_zero {x s : F circomPrime} {c : Prop} [Decidable c]
    (h : x = if c then (0 : F circomPrime) else s) (hs : IsBool s) : IsBool x := by
  rw [h]; split
  · exact Or.inl rfl
  · exact hs

end Solution.Secp256k1ScalarMul
