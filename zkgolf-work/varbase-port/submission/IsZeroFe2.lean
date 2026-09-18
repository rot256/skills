import Solution.Secp256k1ScalarMul.Params
import Solution.Secp256k1ScalarMul.IsZeroFe
import Challenge.Utils.ComputableWitnessLemmas
import Clean.Gadgets.IsZeroField

namespace Solution.Secp256k1ScalarMul
namespace IsZeroFe2

def main (x : Var Emu (F circomPrime)) :
    Circuit (F circomPrime) (Expression (F circomPrime)) := do
  let z0 ← subcircuit Gadgets.IsZeroField.circuit x[0]
  let z1 ← subcircuit Gadgets.IsZeroField.circuit x[1]
  let z <== z0 * z1
  return z

instance elaborated : ElaboratedCircuit (F circomPrime) Emu field main := by
  elaborate_circuit

def Assumptions (_ : Emu (F circomPrime)) : Prop := True

def Spec (x : Emu (F circomPrime)) (out : F circomPrime) : Prop :=
  out = if x[0] = 0 ∧ x[1] = 0 then 1 else 0

theorem soundness :
    Soundness (Input := Emu) (Output := field) (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [Gadgets.IsZeroField.circuit, Gadgets.IsZeroField.Assumptions,
    Gadgets.IsZeroField.Spec]
  obtain ⟨hz0, hz1, hz⟩ := h_holds
  have hx : ∀ (i : ℕ) (hi : i < 4), Expression.eval env input_var[i] = input[i] := by
    intro i hi
    rw [← h_input, Vector.getElem_map]
  rw [hx 0 (by omega)] at hz0
  rw [hx 1 (by omega)] at hz1
  rw [hz, hz0, hz1]
  by_cases h0 : input[0] = 0 <;> by_cases h1 : input[1] = 0 <;>
    simp [h0, h1]

theorem completeness :
    Completeness (Input := Emu) (Output := field) (F circomPrime) main Assumptions := by
  circuit_proof_start [Gadgets.IsZeroField.circuit, Gadgets.IsZeroField.Assumptions,
    Gadgets.IsZeroField.Spec]
  obtain ⟨-, -, hz⟩ := h_env
  exact hz

def circuit : FormalCircuit (F circomPrime) Emu field where
  main := main
  elaborated := elaborated
  Assumptions := Assumptions
  Spec := Spec
  soundness := soundness
  completeness := completeness

private lemma input_limb_stable {input : Var Emu (F circomPrime)} {k : ℕ} (hk : k < numLimbs)
    {env env' : ProverEnvironment (F circomPrime)}
    (h : eval env input = eval env' input) :
    eval env input[k] = eval env' input[k] := by
  have hmap := emu_map_eval_eq_of_eval_eq h
  have hget : (input.map (Expression.eval env.toEnvironment))[k] =
      (input.map (Expression.eval env'.toEnvironment))[k] := by rw [hmap]
  simp only [Vector.getElem_map] at hget
  rw [CircuitType.eval_var_field_prover, CircuitType.eval_var_field_prover]
  exact hget

theorem computableWitnesses : circuit.base.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  have hL : ∀ (y : Expression (F circomPrime)) (o : ℕ),
      (subcircuit Gadgets.IsZeroField.circuit y).localLength o = 2 := by
    intro y o
    simp only [circuit_norm, Gadgets.IsZeroField.circuit]
  have hA : ∀ (r : Var field (F circomPrime)) (o : ℕ),
      (HasAssignEq.assignEq (β := field (Expression (F circomPrime))) r).localLength o = 1 := by
    intro r o
    simp only [circuit_norm, HasAssignEq.assignEq]
  unfold main
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.pure_structuralComputableWitnesses_iff,
    hL, hA, and_true]
  refine ⟨?_, ?_, ?_⟩
  · exact Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses
      Gadgets.IsZeroField.circuit input input[0] offset
      (fun _ _ h => input_limb_stable (by decide) h) IsZeroFe.isZeroFieldComputableWitnesses env env'
  · exact Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses
      Gadgets.IsZeroField.circuit input input[1] (offset + 2)
      (fun _ _ h => input_limb_stable (by decide) h) IsZeroFe.isZeroFieldComputableWitnesses env env'
  · refine ⟨?_, ?_, ?_⟩
    · intro h_agree _
      refine congrArg toElements ?_
      have h0 := IsZeroFe.isZeroField_output_eval_stable (base := offset) input[0] h_agree (by omega)
      have h1 := IsZeroFe.isZeroField_output_eval_stable (base := offset + 2) input[1] h_agree (by omega)
      simp only [CircuitType.eval_var_field_prover, Expression.eval, h0, h1]
    · exact IsZeroFe.equalityFieldSubcircuit_flatStructural_any input _ _ _ env env'
    · trivial

theorem computableWitness : ∀ n input,
    ProverEnvironment.OnlyAccessedBelow n
      (fun env : ProverEnvironment (F circomPrime) => eval env input) →
    Circuit.ComputableWitnesses (main input) n :=
  Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnesses_implies
    (circuit := circuit.base) computableWitnesses

lemma eval_output_of_agreesBelow (x : Var Emu (F circomPrime)) {offset k : ℕ}
    {env env' : ProverEnvironment (F circomPrime)}
    (h_agree : env.AgreesBelow k env') (hk : offset + 5 ≤ k) :
    eval env ((main x).output offset) = eval env' ((main x).output offset) := by
  rw [CircuitType.eval_var_field_prover, CircuitType.eval_var_field_prover]
  simp only [main, circuit_norm, Gadgets.IsZeroField.circuit]
  exact h_agree (offset + 4) (by omega)

end IsZeroFe2
end Solution.Secp256k1ScalarMul
