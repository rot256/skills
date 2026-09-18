import Solution.Secp256k1ScalarMul.Theorems
import Solution.Secp256k1ScalarMul.RangeCheck
import Challenge.Utils.ComputableWitnessLemmas

namespace Solution.Secp256k1ScalarMul
open Solution.Secp256k1ScalarMul.Limbs

section
variable {p : ℕ} [Fact p.Prime]
variable {m : ℕ}

namespace Normalize

def main (P : BigIntParams p m) [Fact (p > 2)] (x : Var (BigInt m) (F p)) :
    Circuit (F p) Unit :=
  Circuit.forEach x (fun xi => RangeCheck.circuit P.B P.hB P.hB1 xi)

instance elaborated (P : BigIntParams p m) [Fact (p > 2)] :
    ElaboratedCircuit (F p) (BigInt m) unit (main P) where
  localLength _ := m * (P.B - 1)
  localLength_eq := by
    intro input offset
    simp only [main, circuit_norm, RangeCheck.circuit]
  subcircuitsConsistent := by
    intro input offset
    simp +arith only [main, circuit_norm, RangeCheck.circuit]
  channelsLawful := by
    intro offset
    simp only [main, circuit_norm, RangeCheck.circuit]

def Assumptions (_ : BigInt m (F p)) : Prop := True

def Spec (B : ℕ) (x : BigInt m (F p)) : Prop := BigInt.Normalized B x

def circuit (P : BigIntParams p m) [Fact (p > 2)] : FormalAssertion (F p) (BigInt m) where
  main := main P
  Assumptions := Assumptions
  Spec := Spec P.B
  soundness := by
    circuit_proof_start
    simp_all only [circuit_norm, RangeCheck.circuit, BigInt.Normalized]
    intro i
    rw [← h_input, Vector.getElem_map]
    exact (h_holds i) trivial
  completeness := by
    circuit_proof_start
    simp_all only [circuit_norm, RangeCheck.circuit, BigInt.Normalized]
    intro i
    have := h_spec i
    refine ⟨trivial, ?_⟩
    rwa [← h_input, Vector.getElem_map] at this

theorem computableWitnesses (P : BigIntParams p m) [Fact (p > 2)] :
    (circuit P).ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition input env env')
    ((main P input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.forEach_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_structuralComputableWitnesses_iff]
  intro i
  apply Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_flatStructuralComputableWitnesses
  · intro env₁ env₂ h_input
    have h : (eval env₁ input)[i.val] = (eval env₂ input)[i.val] := by
      simpa only [Fin.getElem_fin] using congrArg (fun x : BigInt m (F p) => x[i]) h_input
    rw [← ProvableType.getElem_eval_fields_prover (env := env₁) input i.val i.isLt,
      ← ProvableType.getElem_eval_fields_prover (env := env₂) input i.val i.isLt] at h
    simpa [CircuitType.eval_expression_prover_to_verifier (M := field),
      CircuitType.eval_expression (M := field), ProvableType.eval, explicit_provable_type] using h
  · exact RangeCheck.computableWitnesses P.B P.hB P.hB1

end Normalize

end

end Solution.Secp256k1ScalarMul
