import Solution.Secp256k1ScalarMul.GLVScalarMulCWHelpers

namespace Solution.Secp256k1ScalarMul

local notation "CF" => F circomPrime
open Challenge.Utils.ComputableWitnessLemmas

namespace GLVScalarMul

attribute [local irreducible] main PointValid.main GLVScalarRelation.main

private noncomputable def cwV1
    (input : Var ScalarMul.Inputs CF) (offset : ℕ) :
    Var GLV.SignedCoeff CF :=
  (coeffVar input offset).v1

private theorem v1Circuit_eq_cwV1
    (input : Var ScalarMul.Inputs CF) (offset : ℕ) :
    v1Circuit input offset = GLV.circuit (cwV1 input offset) := rfl

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
private theorem cwV1_eq_varFromOffset
    (input : Var ScalarMul.Inputs CF) (offset : ℕ) :
    cwV1 input offset =
      (varFromOffset GLV.SignedCoeff (coeffOffset offset + 130) :
        Var GLV.SignedCoeff CF) := by
  simp only [cwV1, coeffVar, coeffCircuit, circuit_norm, GLV.coeffBits,
    List.sum_cons, List.sum_nil, Nat.add_zero, Nat.reduceAdd]

private theorem cwV1_stable
    (input : Var ScalarMul.Inputs CF) (offset : ℕ) :
    ∀ (k : ℕ) (e e' : ProverEnvironment CF),
      shortOffset offset ≤ k → e.AgreesBelow k e' →
      eval e input = eval e' input →
      eval e (cwV1 input offset) = eval e' (cwV1 input offset) := by
  intro k e e' hle h_agree _
  rw [cwV1_eq_varFromOffset]
  have hshort : coeffOffset offset + 260 ≤ k := by
    simpa only [shortOffset] using hle
  exact eval_varFromOffset_of_agreesBelow h_agree (by
    simpa only [show size GLV.SignedCoeff = 65 from rfl] using
      (show coeffOffset offset + 130 + 65 ≤ k by omega))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
theorem structuralV1
    (input : Var ScalarMul.Inputs CF) (offset : ℕ)
    (env env' : ProverEnvironment CF) :
  SCW input env env' (shortOffset offset)
      ((v1Circuit input offset).operations (shortOffset offset)) := by
  rw [v1Circuit_eq_cwV1]
  exact structuralGLV input (cwV1 input offset) (shortOffset offset)
    (cwV1_stable input offset) env env'

end GLVScalarMul
end Solution.Secp256k1ScalarMul
