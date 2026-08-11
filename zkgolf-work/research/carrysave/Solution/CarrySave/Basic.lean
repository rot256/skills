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

/-- **The obligation.** Over the naturals, for inputs below `2 ^ n`, the sum of three
    numbers equals their bitwise XOR plus twice their bitwise majority.

    This is exact over `ℤ` / `ℕ` — there is no modular reduction in the statement.
    The `2 ^ n` bound is supplied because the intended use is `n = 32`; if the proof
    goes through without it, state and prove the unbounded version instead and say so. -/
theorem add_eq_xor_add_two_mul_maj (n : ℕ) (x y z : ℕ)
    (hx : x < 2 ^ n) (hy : y < 2 ^ n) (hz : z < 2 ^ n) :
    x + y + z = (x ^^^ y ^^^ z) + 2 * maj x y z := by
  sorry

/-- The specialisation actually consumed by the circuit rewrite. -/
theorem add_eq_xor_add_two_mul_maj_32 (x y z : ℕ)
    (hx : x < 2 ^ 32) (hy : y < 2 ^ 32) (hz : z < 2 ^ 32) :
    x + y + z = (x ^^^ y ^^^ z) + 2 * maj x y z :=
  add_eq_xor_add_two_mul_maj 32 x y z hx hy hz

end Solution.CarrySave
