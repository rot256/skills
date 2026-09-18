import Solution.Secp256k1ScalarMul.GLVScalarMulFinish

namespace Solution.Secp256k1ScalarMul
namespace GLVScalarMul

open Specs.ShortWeierstrass Specs.Secp256k1

set_option maxRecDepth 262144 in
set_option maxHeartbeats 0 in
theorem completeness : Completeness (F circomPrime) main Assumptions := by
  circuit_proof_start_core
  dsimp only [Assumptions, ScalarMul.Assumptions] at h_assumptions
  provable_struct_simp
  simp only [circuit_norm] at h_input
  let input : ScalarMul.Inputs (F circomPrime) :=
    { bits := input_bits, px := input_px, py := input_py }
  let Qv : Var FlaggedPoint (F circomPrime) := varFromOffset FlaggedPoint i₀
  let cv : Var GLV.Coefficients (F circomPrime) :=
    varFromOffset GLV.Coefficients (i₀ + 9 + 1046)
  let output_Q := eval env Qv
  let output_c := eval env cv
  let sV := GLV.ScalarReduce.circuit.output { bits := input_var.bits }
    (i₀ + 9 + 1046 + 260)
  let output_s := eval env sV
  let tV := PatBuildTable.circuit.output
    { P := inputPointVar input_var, Q := Qv
      sign0 := cv.u1.sign, sign1 := cv.u2.sign
      sign2 := cv.v1.sign, sign3 := cv.v2.sign }
    (i₀ + 9 + 1046 + 260 + 0 + 865)
  let output_table := eval env tV
  have hPV : ∀ Q : Var FlaggedPoint (F circomPrime),
      PointValid.circuit.localLength Q = 1046 := fun _ => rfl
  have hSC : ∀ c : Var GLV.SignedCoeff (F circomPrime),
      GLV.circuit.localLength c = 0 := fun _ => rfl
  have hSR : ∀ X : Var GLV.ScalarReduce.Inputs (F circomPrime),
      GLV.ScalarReduce.circuit.localLength X = 0 := fun _ => rfl
  have hRel : ∀ X : Var GLVScalarRelation.Inputs (F circomPrime),
      GLVScalarRelation.circuit.localLength X = 865 := fun _ => rfl
  have hTab : ∀ X : Var GLVBuildTable.Inputs (F circomPrime),
      PatBuildTable.circuit.localLength X = 16366 := patBuildTable_localLength
  have hMSM : ∀ X : Var GLVMSM.Inputs (F circomPrime),
      LazyMSM.circuit.localLength X = 103012 := lazyMSM_localLength
  simp only [main, mainOperations, mainOutput, opChain,
    qCircuit, qVar, pointValidCircuit, coeffCircuit, coeffVar,
    u1Circuit, u2Circuit, v1Circuit, v2Circuit, reduceCircuit, reduceVar,
    relationCircuit, tableCircuit, tableVar, msmCircuit, infinityCircuit,
    pvOffset, coeffOffset, shortOffset, relationOffset, tableOffset, msmOffset, outOffset,
    Circuit.operations, hMSM] at h_env
  rw [Circuit.ConstraintsHold.append_localWitnesses] at h_env
  obtain ⟨hQw, h_env⟩ := h_env
  rw [Circuit.ConstraintsHold.append_localWitnesses] at h_env
  obtain ⟨hpvEnv, h_env⟩ := h_env
  rw [Circuit.ConstraintsHold.append_localWitnesses] at h_env
  obtain ⟨hcw, h_env⟩ := h_env
  rw [Circuit.ConstraintsHold.append_localWitnesses] at h_env
  obtain ⟨hu1Env, h_env⟩ := h_env
  rw [Circuit.ConstraintsHold.append_localWitnesses] at h_env
  obtain ⟨hu2Env, h_env⟩ := h_env
  rw [Circuit.ConstraintsHold.append_localWitnesses] at h_env
  obtain ⟨hv1Env, h_env⟩ := h_env
  rw [Circuit.ConstraintsHold.append_localWitnesses] at h_env
  obtain ⟨hv2Env, h_env⟩ := h_env
  rw [Circuit.ConstraintsHold.append_localWitnesses] at h_env
  obtain ⟨hs, h_env⟩ := h_env
  rw [Circuit.ConstraintsHold.append_localWitnesses] at h_env
  obtain ⟨hrelEnv, h_env⟩ := h_env
  rw [Circuit.ConstraintsHold.append_localWitnesses] at h_env
  obtain ⟨ht, h_env⟩ := h_env
  rw [Circuit.ConstraintsHold.append_localWitnesses] at h_env
  obtain ⟨_, _⟩ := h_env
  simp only [circuit_norm, h_input, hPV, hSC, hSR, hRel, hTab,
    numLimbs, GLV.coeffBits, List.sum_cons, List.sum_nil, Nat.reduceAdd]
    at hQw hcw hs ht
  have hQeq : output_Q = encodePoint (trueResult input) := by
    simpa [output_Q, Qv, resultWitness, input, h_input, circuit_norm] using
      eval_provableWitness (resultWitness input_var) env i₀ hQw
  have hcw' : env.ExtendsVector (toElements (coefficientWitness input_var env))
      (i₀ + 9 + 1046) := by
    intro i
    rw [show i₀ + 9 + 1046 + ↑i = 1046 + (9 + i₀) + ↑i by omega]
    exact hcw i
  have hceq : output_c = coefficientValue input := by
    simpa [output_c, cv, coefficientWitness, input, h_input, circuit_norm] using
      eval_provableWitness (coefficientWitness input_var) env (i₀ + 9 + 1046) hcw'
  have hs' : GLV.ScalarReduce.circuit.Assumptions { bits := input_bits } →
      GLV.ScalarReduce.circuit.Spec { bits := input_bits } output_s := by
    simpa only [output_s, sV, circuit_norm, hPV, hSC, numLimbs,
      GLV.coeffBits, List.sum_cons, List.sum_nil, Nat.reduceAdd] using hs
  have ht' : PatBuildTable.circuit.Assumptions
      { P := eval env (inputPointVar input_var), Q := output_Q
        sign0 := output_c.u1.sign, sign1 := output_c.u2.sign
        sign2 := output_c.v1.sign, sign3 := output_c.v2.sign } →
    PatBuildTable.circuit.Spec
      { P := eval env (inputPointVar input_var), Q := output_Q
        sign0 := output_c.u1.sign, sign1 := output_c.u2.sign
        sign2 := output_c.v1.sign, sign3 := output_c.v2.sign } output_table := by
    simpa only [output_table, tV, output_Q, Qv, output_c, cv,
      circuit_norm, hPV, hSC, hSR, hRel, numLimbs, GLV.coeffBits,
      List.sum_cons, List.sum_nil, Nat.reduceAdd] using ht
  exact finishCompleteness input_var env i₀ input output_Q output_c output_s
    output_table (by rfl) (by rfl) (by rfl) (by rfl)
    h_assumptions
    (by simpa only [input, circuit_norm] using h_input.1)
    (by simpa only [input, circuit_norm] using h_input.2.1)
    (by simpa only [input, circuit_norm] using h_input.2.2)
    hQeq hceq hs' ht'

#check completeness

end GLVScalarMul
end Solution.Secp256k1ScalarMul
