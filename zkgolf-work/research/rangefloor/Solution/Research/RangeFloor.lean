/-
  Does a range check cost at least 2 score per bit?

  In this cost model score = allocations + constraints, each row is exactly one
  product (A·w)(B·w) = (C·w), and affine combinations are FREE. The standard
  n-bit range check witnesses n boolean bits and asserts n booleanity rows plus
  one free affine recomposition, costing ⟨n, n⟩ = 2n score.

  EVERY tree in this project pays that rate, and on RSA it is 81.4% of the entire
  circuit. Beating it, even by a constant factor, would be worth more than every
  structural technique found so far combined. Nobody has proved it is optimal.
-/
import Mathlib

namespace Solution.Research

/-- An R1CS row over a witness vector `w`: `(A ⬝ w) * (B ⬝ w) = C ⬝ w`, with `A`, `B`,
    `C` affine forms. Model them however is most convenient — coefficient vectors over
    `F` with a constant term is the intended reading. -/
structure Row (F : Type*) [Field F] (m : ℕ) where
  A : Fin (m + 1) → F
  B : Fin (m + 1) → F
  C : Fin (m + 1) → F

/-- **The question.** Fix a field `F` of large characteristic and a bound `n`. Suppose a
    system of `r` rows over `m` witnesses, together with the public input `x`, is
    satisfiable exactly when `x < 2 ^ n` (for `x` ranging over the values representable
    in `F`). Is `m + r ≥ 2 * n` forced?

    PROVE IT, or REFUTE IT with an explicit construction. A refutation is far more
    valuable than a proof — it would be the single largest result available here.

    State your own formalisation of "the system is satisfiable exactly when x < 2^n";
    the shape below is a suggestion, not a constraint, and getting the definition right
    is part of the task. -/
theorem range_check_floor : True := by trivial

end Solution.Research
