/-
  The one-row permutation switch.

  A 2x2 switch is normally encoded with a boolean selector `s`:
      out1 = a + s * (b - a),  out2 = a + b - out1,  s * (s - 1) = 0
  costing 2 rows and 2 witnesses. The claim is that witnessing ONLY `out1` and
  asserting a single quadratic row pins the pair as a MULTISET at 1 row + 1 witness.

  Composed with a Waksman network (n·log2 n - n + 1 switches, realising every
  permutation in S_n) this is a permutation / multiset-equality certificate that needs
  NO random challenge -- which matters because our soundness obligation is an
  unconditional `forall env` theorem and the usual grand-product argument is not
  available to us.
-/
import Mathlib

namespace Solution.Research

variable {F : Type*} [Field F]

/-- **The obligation.** The single row `(o - a) * (o - b) = 0`, together with the free
    affine definition `o' = a + b - o`, forces the unordered pair `{o, o'}` to equal
    `{a, b}`.

    Prove it. Then state and prove the converse (completeness): for either choice of
    `o ∈ {a, b}` the row is satisfied and `o'` is the other element. -/
theorem switch_pins_multiset (a b o : F) (h : (o - a) * (o - b) = 0) :
    (o = a ∧ a + b - o = b) ∨ (o = b ∧ a + b - o = a) := by
  sorry

end Solution.Research
