/-
  The carry-save identity for SHA-256, stated as a proof obligation.

  This is the PRECONDITION for two queued circuit optimisations worth 448 and 240
  score respectively. It is a mathematical statement about natural numbers; it does
  not depend on any circuit machinery, and nothing here needs to be a `Circuit`.

  The identity is the bitwise-parallel 3:2 carry-save adder rule. It has been
  verified numerically on 10^5 random inputs for each of SHA-256's four diffusion
  functions, but it is not proved, and the rewrite cannot land until it is.
-/
import Mathlib

namespace Solution.CarrySave

/-- Bitwise majority on `Nat`, defined via the standard `F_2` identity lifted to
    bit operations: `maj x y z = (x &&& y) ||| (z &&& (x ^^^ y))`. -/
def maj (x y z : ℕ) : ℕ := (x &&& y) ||| (z &&& (x ^^^ y))

private lemma and_mod_two (a b : ℕ) : (a &&& b) % 2 = (a % 2) &&& (b % 2) := by
  simp [← Nat.and_one_is_mod]
  ac_rfl

private lemma or_mod_two (a b : ℕ) : (a ||| b) % 2 = (a % 2) ||| (b % 2) := by
  simp [← Nat.and_one_is_mod, Nat.and_or_distrib_right]

private lemma xor_mod_two (a b : ℕ) : (a ^^^ b) % 2 = (a % 2) ^^^ (b % 2) := by
  simp [← Nat.and_one_is_mod, Nat.and_xor_distrib_right]

/-- `maj` commutes with dividing all its arguments by two (shifting right by one bit). -/
lemma maj_div_two (x y z : ℕ) : maj x y z / 2 = maj (x / 2) (y / 2) (z / 2) := by
  simp [maj, Nat.or_div_two, Nat.and_div_two, Nat.xor_div_two]

/-- `maj` commutes with taking all its arguments mod two (the low bit). -/
lemma maj_mod_two (x y z : ℕ) : maj x y z % 2 = maj (x % 2) (y % 2) (z % 2) := by
  simp only [maj, or_mod_two, and_mod_two, xor_mod_two]

/-- The single-bit full adder: the identity for one-bit inputs, by exhausting the
    eight cases. -/
lemma maj_single_bit (p q r : ℕ) (hp : p < 2) (hq : q < 2) (hr : r < 2) :
    p + q + r = (p ^^^ q ^^^ r) + 2 * maj p q r := by
  interval_cases p <;> interval_cases q <;> interval_cases r <;> decide

/-- **The unbounded identity.** For all naturals, the sum of three numbers equals
    their bitwise XOR plus twice their bitwise majority. No size bound is needed. -/
theorem add_eq_xor_add_two_mul_maj' (x y z : ℕ) :
    x + y + z = (x ^^^ y ^^^ z) + 2 * maj x y z := by
  -- Induct on a bit-width bound, peeling off the low bit at each step.
  suffices h : ∀ n x y z : ℕ, x < 2 ^ n → y < 2 ^ n → z < 2 ^ n →
      x + y + z = (x ^^^ y ^^^ z) + 2 * maj x y z by
    refine h (x + y + z) x y z ?_ ?_ ?_ <;>
      exact lt_of_lt_of_le (Nat.lt_two_pow_self)
        (Nat.pow_le_pow_right (by norm_num) (by omega))
  clear x y z
  intro n
  induction n with
  | zero =>
    intro x y z hx hy hz
    simp only [pow_zero, Nat.lt_one_iff] at hx hy hz
    subst hx; subst hy; subst hz
    decide
  | succ n ih =>
    intro x y z hx hy hz
    rw [pow_succ] at hx hy hz
    have hih : x / 2 + y / 2 + z / 2 =
        ((x / 2) ^^^ (y / 2) ^^^ (z / 2)) + 2 * maj (x / 2) (y / 2) (z / 2) :=
      ih _ _ _ (by omega) (by omega) (by omega)
    have hxor : (x ^^^ y ^^^ z) =
        2 * ((x / 2) ^^^ (y / 2) ^^^ (z / 2)) + ((x % 2) ^^^ (y % 2) ^^^ (z % 2)) := by
      conv_lhs => rw [← Nat.div_add_mod (x ^^^ y ^^^ z) 2]
      rw [Nat.xor_div_two, Nat.xor_div_two, xor_mod_two, xor_mod_two]
    have hmaj : maj x y z = 2 * maj (x / 2) (y / 2) (z / 2) + maj (x % 2) (y % 2) (z % 2) := by
      conv_lhs => rw [← Nat.div_add_mod (maj x y z) 2]
      rw [maj_div_two, maj_mod_two]
    have hbit := maj_single_bit (x % 2) (y % 2) (z % 2) (by omega) (by omega) (by omega)
    omega

/-- **The obligation.** Over the naturals, for inputs below `2 ^ n`, the sum of three
    numbers equals their bitwise XOR plus twice their bitwise majority.

    This is exact over `ℤ` / `ℕ` — there is no modular reduction in the statement.
    The `2 ^ n` bound is supplied because the intended use is `n = 32`; if the proof
    goes through without it, state and prove the unbounded version instead and say so.

    The bound turned out to be unnecessary: this is an immediate consequence of the
    unbounded `add_eq_xor_add_two_mul_maj'`. The hypotheses are kept because they were
    requested in the statement. -/
theorem add_eq_xor_add_two_mul_maj (n : ℕ) (x y z : ℕ)
    (hx : x < 2 ^ n) (hy : y < 2 ^ n) (hz : z < 2 ^ n) :
    x + y + z = (x ^^^ y ^^^ z) + 2 * maj x y z :=
  add_eq_xor_add_two_mul_maj' x y z

/-- The specialisation actually consumed by the circuit rewrite. -/
theorem add_eq_xor_add_two_mul_maj_32 (x y z : ℕ)
    (hx : x < 2 ^ 32) (hy : y < 2 ^ 32) (hz : z < 2 ^ 32) :
    x + y + z = (x ^^^ y ^^^ z) + 2 * maj x y z :=
  add_eq_xor_add_two_mul_maj 32 x y z hx hy hz

end Solution.CarrySave
