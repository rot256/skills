import Solution.Secp256k1ScalarMul.NegYAffineBase

namespace Solution.Secp256k1ScalarMul
namespace NegYAffine

open Specs.ShortWeierstrass Specs.Secp256k1

lemma boolField_bool (c : Bool) : IsBool (boolField c) := by
  cases c <;> simp [boolField, IsBool]

lemma borrowField_bool (pd y cin : ℕ) : IsBool (borrowField pd y cin) := by
  unfold borrowField
  exact boolField_bool _

lemma borrowField_eq_cast (pd y cin : ℕ) :
    borrowField pd y cin = (borrow pd y cin : F circomPrime) := by
  cases h : borrowFlag pd y cin
  · simp only [borrowField, boolField, borrow, h, Bool.false_eq_true, ↓reduceIte,
      Nat.cast_zero]
  · simp only [borrowField, boolField, borrow, h, ↓reduceIte, Nat.cast_one]

lemma carry0Compute_eq_borrowField (P : Var FlaggedPoint (F circomPrime))
    (env : ProverEnvironment (F circomPrime)) :
    carry0Compute P env =
      borrowField (qNat P env * p0) (yNat P env 0) 0 := by
  rfl

lemma carry0Compute_bool (P : Var FlaggedPoint (F circomPrime))
    (env : ProverEnvironment (F circomPrime)) : IsBool (carry0Compute P env) := by
  rw [carry0Compute_eq_borrowField]
  exact borrowField_bool _ _ _

private lemma nat_sub_val
    {a b : ℕ} (hb : b ≤ a) (hlt : a - b < circomPrime) :
    ((((a : ℕ) : F circomPrime) - ((b : ℕ) : F circomPrime))).val = a - b := by
  rw [← Nat.cast_sub hb, ZMod.val_natCast_of_lt hlt]

lemma borrow_limb_value_lt (pd y cin : ℕ)
    (hpd : pd < radix) (hy : y < radix) (hcin : cin ≤ 1) :
    (((pd : F circomPrime) + (radix : F circomPrime) * (borrow pd y cin : F circomPrime)
        - (y : F circomPrime) - (cin : F circomPrime))).val < radix := by
  by_cases hb : y + cin > pd
  · have hle : y + cin ≤ pd + radix := by omega
    have hdiff : pd + radix - (y + cin) < radix := by omega
    have hprime : pd + radix - (y + cin) < circomPrime :=
      lt_trans hdiff (by decide : radix < circomPrime)
    simp only [borrow, borrowFlag, decide_eq_true_eq, if_pos hb]
    have heq :
        (pd : F circomPrime) + (radix : F circomPrime) * ((1 : ℕ) : F circomPrime)
              - (y : F circomPrime) - (cin : F circomPrime) =
          ((pd + radix : ℕ) : F circomPrime) - ((y + cin : ℕ) : F circomPrime) := by
      push_cast
      ring
    rw [heq, nat_sub_val hle hprime]
    exact hdiff
  · have hle : y + cin ≤ pd := by omega
    have hdiff : pd - (y + cin) < radix := lt_of_le_of_lt (Nat.sub_le _ _) hpd
    have hprime : pd - (y + cin) < circomPrime :=
      lt_trans hdiff (by decide : radix < circomPrime)
    simp only [borrow, borrowFlag, decide_eq_true_eq, if_neg hb]
    have heq :
        (pd : F circomPrime) + (radix : F circomPrime) * ((0 : ℕ) : F circomPrime)
              - (y : F circomPrime) - (cin : F circomPrime) =
          (pd : F circomPrime) - ((y + cin : ℕ) : F circomPrime) := by
      push_cast
      ring
    rw [heq, nat_sub_val hle hprime]
    exact hdiff

end NegYAffine
end Solution.Secp256k1ScalarMul
