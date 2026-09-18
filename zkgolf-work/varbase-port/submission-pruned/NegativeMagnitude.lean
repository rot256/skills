import Solution.Secp256k1ScalarMul.Mux
import Solution.Secp256k1ScalarMul.Cost
import Challenge.Utils.ComputableWitnessLemmas

namespace Solution.Secp256k1ScalarMul
namespace NegativeMagnitude

structure Inputs (F : Type) where
  sign : F
  magnitude : F
deriving ProvableStruct

def main (input : Var Inputs (F circomPrime)) :
    Circuit (F circomPrime) (Var field (F circomPrime)) :=
  subcircuit (Mux.circuit (M := field))
    { selector := input.sign, ifTrue := input.magnitude, ifFalse := 0 }

instance elaborated : ElaboratedCircuit (F circomPrime) Inputs field main := by
  elaborate_circuit

def Assumptions (input : Inputs (F circomPrime)) : Prop := IsBool input.sign

def Spec (input : Inputs (F circomPrime)) (out : F circomPrime) : Prop :=
  out = if input.sign = 1 then input.magnitude else 0

theorem soundness : Soundness (Input := Inputs) (Output := field)
    (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [Mux.circuit, Mux.Assumptions, Mux.Spec]
  exact h_holds h_assumptions

theorem completeness : Completeness (Input := Inputs) (Output := field)
    (F circomPrime) main Assumptions := by
  circuit_proof_start [Mux.circuit, Mux.Assumptions, Mux.Spec]
  exact h_assumptions

def circuit : FormalCircuit (F circomPrime) Inputs field where
  main; elaborated; Assumptions; Spec; soundness; completeness

theorem computableWitnesses : circuit.base.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations offset)
  apply Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_structuralComputableWitnesses_iff]
  refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
    (Parent := Inputs) (Mux.circuit (M := field)) _ _ _ ?_ Mux.computableWitnesses env env'
  intro k e e' _ _ hinput
  simpa only [circuit_norm, Inputs.mk.injEq, Mux.Inputs.mk.injEq] using hinput

end NegativeMagnitude

namespace Cost
open Challenge.CostR1CS
attribute [local irreducible] isR1CSRow r1csProducts operationsIsR1CS flatOperationsIsR1CS

def negativeMagnitudeCost : Count := ⟨1, 1⟩

theorem costIs_sub_negativeMagnitude
    (input : Var NegativeMagnitude.Inputs (F circomPrime)) :
    CostIs (subcircuit NegativeMagnitude.circuit input) negativeMagnitudeCost := by
  apply CostIs.subcircuit
  intro n
  simp only [NegativeMagnitude.circuit]
  have h := costIs_sub_mux (M := field)
    ({ selector := input.sign, ifTrue := input.magnitude, ifFalse := 0 } :
      Var (Mux.Inputs field) (F circomPrime)) n
  simpa only [show size field = 1 from rfl, negativeMagnitudeCost] using h

theorem isR1CS_sub_negativeMagnitude
    (input : Var NegativeMagnitude.Inputs (F circomPrime))
    (hs : Affine input.sign) (hm : Affine input.magnitude) :
    IsR1CSCirc (subcircuit NegativeMagnitude.circuit input) := by
  apply IsR1CSCirc.subcircuit
  intro n
  simp only [NegativeMagnitude.circuit]
  unfold NegativeMagnitude.main
  let muxInput : Var (Mux.Inputs field) (F circomPrime) :=
    { selector := input.sign, ifTrue := input.magnitude, ifFalse := 0 }
  have h := isR1CS_sub_mux muxInput hs
    (by simpa [AffineProvable, circuit_norm] using hm)
    (by simpa [AffineProvable, circuit_norm] using (Affine.const (F := F circomPrime) 0))
  exact h n

theorem affine_sub_negativeMagnitude
    (input : Var NegativeMagnitude.Inputs (F circomPrime)) (n : ℕ) :
    Affine ((subcircuit NegativeMagnitude.circuit input).output n) := by
  simp only [circuit_norm, NegativeMagnitude.circuit, NegativeMagnitude.elaborated]
  exact Affine.var _

end Cost
end Solution.Secp256k1ScalarMul
