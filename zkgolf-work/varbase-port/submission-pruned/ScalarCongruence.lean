import Solution.Secp256k1ScalarMul.SignedCoeff
import Solution.Secp256k1ScalarMul.DivOrZeroTheorems

namespace Solution.Secp256k1ScalarMul.GLV

set_option maxRecDepth 2000

open Challenge.CostR1CS
open Solution.Secp256k1ScalarMul.Cost

@[reducible] def scalarOrder : ℕ := Specs.Secp256k1.order

@[reducible] def eigenvalue : ℕ :=
  37718080363155996902926221483475020450927657555482586988616620542887997980018

def nConst : Var Emu (F circomPrime) := emuConst scalarOrder

def eigenvalueConst : Var Emu (F circomPrime) := emuConst eigenvalue

lemma scalarOrder_pos : 0 < scalarOrder := by decide
lemma scalarOrder_lt_256 : scalarOrder < 2 ^ (limbBits * numLimbs) := by decide
lemma eigenvalue_lt_order : eigenvalue < scalarOrder := by decide

lemma eval_nConst (env : Environment (F circomPrime)) :
    Vector.map (Expression.eval env) nConst = emuOfNat scalarOrder :=
  DivOrZero.eval_emuConst env scalarOrder

lemma eval_eigenvalueConst (env : Environment (F circomPrime)) :
    Vector.map (Expression.eval env) eigenvalueConst = emuOfNat eigenvalue :=
  DivOrZero.eval_emuConst env eigenvalue

lemma nConst_normalized (env : Environment (F circomPrime)) :
    BigInt.Normalized limbBits (Vector.map (Expression.eval env) nConst) := by
  rw [eval_nConst]
  exact emuOfNat_normalized scalarOrder

lemma nConst_value (env : Environment (F circomPrime)) :
    BigInt.value limbBits (Vector.map (Expression.eval env) nConst) = scalarOrder := by
  rw [eval_nConst]
  exact value_emuOfNat scalarOrder_lt_256

lemma eigenvalueConst_normalized (env : Environment (F circomPrime)) :
    BigInt.Normalized limbBits
      (Vector.map (Expression.eval env) eigenvalueConst) := by
  rw [eval_eigenvalueConst]
  exact emuOfNat_normalized eigenvalue

lemma eigenvalueConst_value (env : Environment (F circomPrime)) :
    BigInt.value limbBits
      (Vector.map (Expression.eval env) eigenvalueConst) = eigenvalue := by
  rw [eval_eigenvalueConst]
  exact value_emuOfNat (lt_trans eigenvalue_lt_order scalarOrder_lt_256)

end Solution.Secp256k1ScalarMul.GLV
