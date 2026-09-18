import Solution.Secp256k1ScalarMul.NegYAffineCompletenessMath

namespace Solution.Secp256k1ScalarMul
namespace NegYAffine

open Specs.ShortWeierstrass Specs.Secp256k1

attribute [local irreducible] carry0Compute
set_option maxRecDepth 10000

private lemma qNat_finite
    (P : Var FlaggedPoint (F circomPrime)) (env : ProverEnvironment (F circomPrime))
    (hi : Expression.eval env.toEnvironment P.isInf = 0) :
    qNat P env = 1 := by
  simp [qNat, qNatFrom, circuit_norm, hi, ZMod.val_one]

private lemma qNat_infinity
    (P : Var FlaggedPoint (F circomPrime)) (env : ProverEnvironment (F circomPrime))
    (hi : Expression.eval env.toEnvironment P.isInf = 1) :
    qNat P env = 0 := by
  simp [qNat, qNatFrom, circuit_norm, hi]

private lemma yNat_eq
    (P : Var FlaggedPoint (F circomPrime)) (env : ProverEnvironment (F circomPrime))
    (y : Emu (F circomPrime))
    (hy : ∀ (i : ℕ) (hip : i < numLimbs),
      Expression.eval env.toEnvironment (P.y[i]'hip) = y[i]'hip)
    (i : Fin numLimbs) : yNat P env i = y[i].val := by
  unfold yNat yNatFrom
  rw [Fin.getElem_fin]
  have hi : (eval env P).y[i.val] = y[i.val] := by
    simpa only [circuit_norm] using hy i.val i.isLt
  exact congrArg ZMod.val hi

private lemma yNat_zero
    (P : Var FlaggedPoint (F circomPrime)) (env : ProverEnvironment (F circomPrime))
    (hy : ∀ (i : ℕ) (hip : i < numLimbs),
      Expression.eval env.toEnvironment (P.y[i]'hip) = 0)
    (i : Fin numLimbs) : yNat P env i = 0 := by
  unfold yNat yNatFrom
  rw [Fin.getElem_fin]
  have hi : (eval env P).y[i.val] = 0 := by
    simpa only [circuit_norm] using hy i.val i.isLt
  rw [hi, ZMod.val_zero]

lemma carry0_finite
    (P : Var FlaggedPoint (F circomPrime)) (env : ProverEnvironment (F circomPrime))
    (y : Emu (F circomPrime))
    (hi : Expression.eval env.toEnvironment P.isInf = 0)
    (hy : ∀ (i : ℕ) (hip : i < numLimbs),
      Expression.eval env.toEnvironment (P.y[i]'hip) = y[i]'hip) :
    carry0Compute P env = (borrow p0 y[0].val 0 : F circomPrime) := by
  have hq := qNat_finite P env hi
  have hy0 := yNat_eq P env y hy (0 : Fin numLimbs)
  rw [carry0Compute_eq_borrowField]
  rw [borrowField_eq_cast, hq, hy0]
  simp only [one_mul]
  rfl

lemma carry0_infinity
    (P : Var FlaggedPoint (F circomPrime)) (env : ProverEnvironment (F circomPrime))
    (hi : Expression.eval env.toEnvironment P.isInf = 1)
    (hy : ∀ (i : ℕ) (hip : i < numLimbs),
      Expression.eval env.toEnvironment (P.y[i]'hip) = 0) :
    carry0Compute P env = 0 := by
  have hq := qNat_infinity P env hi
  have hy0 := yNat_zero P env hy (0 : Fin numLimbs)
  rw [carry0Compute_eq_borrowField]
  rw [borrowField_eq_cast, hq, hy0]
  norm_num [borrow, borrowFlag]

end NegYAffine
end Solution.Secp256k1ScalarMul
