import Mathlib.FieldTheory.Finite.Basic
import Challenge.Specs.Secp256k1

/-!
# Kernel certificate: secp256k1 has no affine point with `y = 0`

An affine `y = 0` point needs `x ^ 3 = -7` in `𝔽_p`. Since `p ≡ 1 (mod 3)`,
`-7` is a cube iff `(-7) ^ ((p - 1) / 3) = 1`; the fueled binary `powMod`
evaluates that power in the kernel and it is not `1`.
-/

namespace Solution.Secp256k1ScalarMul.OrderFactsCerts

set_option maxRecDepth 100000

def powMod (a m : Nat) : Nat → Nat → Nat
  | 0, _ => 1 % m
  | fuel + 1, e =>
    if e = 0 then 1 % m
    else
      let h := powMod a m fuel (e / 2)
      let sq := h * h % m
      if e % 2 = 1 then sq * (a % m) % m else sq

theorem powMod_correct (a m : Nat) :
    ∀ fuel e, e < 2 ^ fuel → powMod a m fuel e = a ^ e % m := by
  intro fuel
  induction fuel with
  | zero =>
      intro e he
      have : e = 0 := by simpa using he
      subst this; rfl
  | succ f ih =>
      intro e he
      rw [powMod]
      by_cases h0 : e = 0
      · subst h0; simp
      · rw [if_neg h0]
        have hlt : e / 2 < 2 ^ f := by
          have : e < 2 ^ (f + 1) := he
          omega
        have hih := ih (e / 2) hlt
        simp only [hih]
        have hsq : (a ^ (e / 2) % m) * (a ^ (e / 2) % m) % m = a ^ (2 * (e / 2)) % m := by
          rw [← Nat.mul_mod, ← pow_add, two_mul]
        by_cases hpar : e % 2 = 1
        · rw [if_pos hpar, hsq, ← Nat.mul_mod, ← pow_succ]; congr 2; omega
        · rw [if_neg hpar, hsq]; congr 2; omega

private lemma pow_ne_one' {P w e : Nat} (hP1 : 1 < P) (h : w ^ e % P ≠ 1) :
    ((w : Nat) : ZMod P) ^ e ≠ 1 := by
  haveI : Fact (1 < P) := ⟨hP1⟩
  intro hcon
  apply h
  have h1 : ((w ^ e % P : Nat) : ZMod P) = ((w : Nat) : ZMod P) ^ e := by
    rw [ZMod.natCast_mod]; push_cast; ring
  rw [hcon] at h1
  have hlt : w ^ e % P < P := Nat.mod_lt _ (by omega)
  have hv := congrArg ZMod.val h1
  rwa [ZMod.val_cast_of_lt hlt, ZMod.val_one] at hv

/-- Cubic-residue certificate for the secp256k1 base field:
`(p - 7) ^ ((p - 1) / 3) % p ≠ 1`, so `-7` is not a cube in `𝔽_p`. -/
theorem neg7_third_power_ne_one :
    ((0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc28 : ℕ) :
        Specs.Secp256k1.Fp) ^
      (0x55555555555555555555555555555555555555555555555555555554fffffeba : ℕ) ≠ 1 := by
  refine pow_ne_one' (by norm_num [Specs.Secp256k1.p]) ?_
  rw [show Specs.Secp256k1.p
      = 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f from rfl]
  rw [← powMod_correct 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc28
      0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f 256
      0x55555555555555555555555555555555555555555555555555555554fffffeba (by decide)]
  decide

/-- Quadratic non-residue certificate for the secp256k1 base field:
`7 ^ ((p - 1) / 2) % p ≠ 1`. -/
theorem seven_half_power_ne_one :
    ((7 : ℕ) : Specs.Secp256k1.Fp) ^
      (0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffe17 : ℕ) ≠ 1 := by
  refine pow_ne_one' (by norm_num [Specs.Secp256k1.p]) ?_
  rw [show Specs.Secp256k1.p
      = 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f from rfl]
  rw [← powMod_correct 7
      0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f 256
      0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffe17 (by decide)]
  decide

/-- secp256k1 has no affine point with `y = 0`: such a point needs
`x ^ 3 = -7`, and `-7` is not a cube by `neg7_third_power_ne_one`. -/
theorem noOrderTwo_secp :
    Specs.ShortWeierstrass.NoOrderTwo Specs.Secp256k1.curve := by
  intro P hP hy
  rw [Specs.Secp256k1.onCurve_iff, hy] at hP
  have hx3 : P.x ^ 3 = -7 := by linear_combination -hP
  have h7 : ((7 : ℕ) : Specs.Secp256k1.Fp) ≠ 0 := by
    intro h0
    have hv := congrArg ZMod.val h0
    rw [ZMod.val_cast_of_lt (by norm_num [Specs.Secp256k1.p]), ZMod.val_zero] at hv
    omega
  have hx0 : P.x ≠ 0 := by
    intro h0
    rw [h0] at hx3
    apply h7
    push_cast
    linear_combination hx3
  have hpm7 :
      ((0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc28 : ℕ) :
        Specs.Secp256k1.Fp) = -7 := by
    rw [show (0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc28 : ℕ)
        = Specs.Secp256k1.p - 7 from by norm_num [Specs.Secp256k1.p]]
    rw [Nat.cast_sub (by norm_num [Specs.Secp256k1.p])]
    simp
  apply neg7_third_power_ne_one
  rw [hpm7, ← hx3, ← pow_mul]
  rw [show 3 * (0x55555555555555555555555555555555555555555555555555555554fffffeba : ℕ)
      = Specs.Secp256k1.p - 1 from by norm_num [Specs.Secp256k1.p]]
  exact ZMod.pow_card_sub_one_eq_one hx0

/-- secp256k1 has no affine point with `x = 0`: such a point needs
`y ^ 2 = 7`, but `7` is not a quadratic residue. -/
theorem noXZero_secp {P : Specs.ShortWeierstrass.Point Specs.Secp256k1.Fp}
    (hP : Specs.ShortWeierstrass.OnCurve Specs.Secp256k1.curve P) :
    P.x ≠ 0 := by
  intro hx
  rw [Specs.Secp256k1.onCurve_iff, hx] at hP
  have hy2 : P.y ^ 2 = 7 := by linear_combination hP
  have hy2' : P.y ^ 2 = ((7 : ℕ) : Specs.Secp256k1.Fp) := by
    simpa using hy2
  have hy0 : P.y ≠ 0 := by
    intro h0
    have h7 : ((7 : ℕ) : Specs.Secp256k1.Fp) ≠ 0 := by
      intro h70
      have hv := congrArg ZMod.val h70
      rw [ZMod.val_cast_of_lt (by norm_num [Specs.Secp256k1.p]), ZMod.val_zero] at hv
      omega
    apply h7
    rw [← hy2', h0]
    ring
  apply seven_half_power_ne_one
  rw [← hy2', ← pow_mul]
  rw [show 2 * (0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffe17 : ℕ)
      = Specs.Secp256k1.p - 1 from by norm_num [Specs.Secp256k1.p]]
  exact ZMod.pow_card_sub_one_eq_one hy0

end Solution.Secp256k1ScalarMul.OrderFactsCerts
