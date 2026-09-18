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

lemma c0Nat_eq (P : Var FlaggedPoint (F circomPrime))
    (env : ProverEnvironment (F circomPrime)) :
    c0Nat P env = borrow (qNat P env * p0) (yNat P env 0) 0 := by
  rfl

lemma c1NatFrom_eq (P : FlaggedPoint (F circomPrime)) :
    c1NatFrom P = borrow (qNatFrom P * pHi) (yNatFrom P 1) (c0NatFrom P) := by
  rfl

lemma c1Nat_eq (P : Var FlaggedPoint (F circomPrime))
    (env : ProverEnvironment (F circomPrime)) :
    c1Nat P env = borrow (qNat P env * pHi) (yNat P env 1) (c0Nat P env) := by
  simpa only [c1Nat, qNat, yNat, c0Nat] using c1NatFrom_eq (eval env P)

lemma carry0Compute_eq_borrowField (P : Var FlaggedPoint (F circomPrime))
    (env : ProverEnvironment (F circomPrime)) :
    carry0Compute P env =
      borrowField (qNat P env * p0) (yNat P env 0) 0 := by
  rfl

lemma carry1ComputeFrom_eq_borrowField (P : FlaggedPoint (F circomPrime)) :
    carry1ComputeFrom P =
      borrowField (qNatFrom P * pHi) (yNatFrom P 1) (c0NatFrom P) := by
  rfl

lemma carry1Compute_eq_borrowField (P : Var FlaggedPoint (F circomPrime))
    (env : ProverEnvironment (F circomPrime)) :
    carry1Compute P env =
      borrowField (qNat P env * pHi) (yNat P env 1) (c0Nat P env) := by
  simpa only [carry1Compute, qNat, yNat, c0Nat] using
    carry1ComputeFrom_eq_borrowField (eval env P)

lemma carry2ComputeFrom_eq_borrowField (P : FlaggedPoint (F circomPrime)) :
    carry2ComputeFrom P =
      borrowField (qNatFrom P * pHi) (yNatFrom P 2) (c1NatFrom P) := by
  rfl

lemma carry2Compute_eq_borrowField (P : Var FlaggedPoint (F circomPrime))
    (env : ProverEnvironment (F circomPrime)) :
    carry2Compute P env =
      borrowField (qNat P env * pHi) (yNat P env 2) (c1Nat P env) := by
  simpa only [carry2Compute, qNat, yNat, c1Nat] using
    carry2ComputeFrom_eq_borrowField (eval env P)

lemma carry0Compute_bool (P : Var FlaggedPoint (F circomPrime))
    (env : ProverEnvironment (F circomPrime)) : IsBool (carry0Compute P env) := by
  rw [carry0Compute_eq_borrowField]
  exact borrowField_bool _ _ _

lemma carry1Compute_bool (P : Var FlaggedPoint (F circomPrime))
    (env : ProverEnvironment (F circomPrime)) : IsBool (carry1Compute P env) := by
  rw [carry1Compute_eq_borrowField]
  exact borrowField_bool _ _ _

lemma carry2Compute_bool (P : Var FlaggedPoint (F circomPrime))
    (env : ProverEnvironment (F circomPrime)) : IsBool (carry2Compute P env) := by
  rw [carry2Compute_eq_borrowField]
  exact borrowField_bool _ _ _

lemma borrow_le_one (pd y cin : ℕ) : borrow pd y cin ≤ 1 := by
  cases h : borrowFlag pd y cin <;> simp [borrow, h]

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

lemma last_limb_value_lt (pd y cin : ℕ)
    (hpd : pd < radix) (hle : y + cin ≤ pd) :
    (((pd : F circomPrime) - (y : F circomPrime) - (cin : F circomPrime))).val < radix := by
  have hdiff : pd - (y + cin) < radix := lt_of_le_of_lt (Nat.sub_le _ _) hpd
  have hprime : pd - (y + cin) < circomPrime :=
    lt_trans hdiff (by decide : radix < circomPrime)
  have heq :
      (pd : F circomPrime) - (y : F circomPrime) - (cin : F circomPrime) =
        (pd : F circomPrime) - ((y + cin : ℕ) : F circomPrime) := by
    push_cast
    ring
  rw [heq, nat_sub_val hle hprime]
  exact hdiff

set_option maxRecDepth 10000 in
lemma top_no_borrow (y : Emu (F circomPrime)) (hy : Fe.Valid y) :
    y[3].val +
        borrow pHi y[2].val (borrow pHi y[1].val (borrow p0 y[0].val 0)) ≤ pHi := by
  have h0 := hy.1 (0 : Fin numLimbs)
  have h1 := hy.1 (1 : Fin numLimbs)
  have h2 := hy.1 (2 : Fin numLimbs)
  have h3 := hy.1 (3 : Fin numLimbs)
  have hv := hy.2
  rw [BigInt.value_eq_sum] at hv
  simp only [numLimbs, Fin.sum_univ_four, Fin.getElem_fin] at hv
  norm_num [limbBits, p0, pHi, P256, Specs.Secp256k1.p] at h0 h1 h2 h3 hv ⊢
  simp only [borrow, borrowFlag, decide_eq_true_eq]
  split <;> split <;> split <;> omega

end NegYAffine
end Solution.Secp256k1ScalarMul
