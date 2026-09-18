import Solution.Secp256k1ScalarMul.GLVScalarMulCWHelpers

namespace Solution.Secp256k1ScalarMul

local notation "CF" => F circomPrime
open Challenge.Utils.ComputableWitnessLemmas

namespace GLVScalarMul

attribute [local irreducible] main PointValid.main GLVScalarRelation.main

private noncomputable def cwU2
    (input : Var ScalarMul.Inputs CF) (offset : ℕ) :
    Var GLV.SignedCoeff CF :=
  (coeffVar input offset).u2

private theorem u2Circuit_eq_cwU2
    (input : Var ScalarMul.Inputs CF) (offset : ℕ) :
    u2Circuit input offset = GLV.circuit (cwU2 input offset) := rfl

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
private theorem cwU2_eq_varFromOffset
    (input : Var ScalarMul.Inputs CF) (offset : ℕ) :
    cwU2 input offset =
      (varFromOffset GLV.SignedCoeff (coeffOffset offset + 65) :
        Var GLV.SignedCoeff CF) := by
  simp only [cwU2, coeffVar, coeffCircuit, circuit_norm, GLV.coeffBits,
    List.sum_cons, List.sum_nil, Nat.add_zero, Nat.reduceAdd]

private theorem cwU2_stable
    (input : Var ScalarMul.Inputs CF) (offset : ℕ) :
    ∀ (k : ℕ) (e e' : ProverEnvironment CF),
      shortOffset offset ≤ k → e.AgreesBelow k e' →
      eval e input = eval e' input →
      eval e (cwU2 input offset) = eval e' (cwU2 input offset) := by
  intro k e e' hle h_agree _
  rw [cwU2_eq_varFromOffset]
  have hshort : coeffOffset offset + 260 ≤ k := by
    simpa only [shortOffset] using hle
  exact eval_varFromOffset_of_agreesBelow h_agree (by
    simpa only [show size GLV.SignedCoeff = 65 from rfl] using
      (show coeffOffset offset + 65 + 65 ≤ k by omega))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
theorem structuralU2
    (input : Var ScalarMul.Inputs CF) (offset : ℕ)
    (env env' : ProverEnvironment CF) :
  SCW input env env' (shortOffset offset)
      ((u2Circuit input offset).operations (shortOffset offset)) := by
  rw [u2Circuit_eq_cwU2]
  exact structuralGLV input (cwU2 input offset) (shortOffset offset)
    (cwU2_stable input offset) env env'

end GLVScalarMul
end Solution.Secp256k1ScalarMul
