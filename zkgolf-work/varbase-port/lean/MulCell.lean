import Solution.Secp256k1ScalarMul.Lazy.Relations

/-!
# One rank-1 product cell `v = p · q`

Used for the flag muxes of the certificate contents and the output muxes.
-/

namespace Solution.Secp256k1ScalarMulFixedBase.LazyVar.MulCell

open SmallSquare Challenge.CostR1CS Cost
open Challenge.Utils.ComputableWitnessLemmas

set_option autoImplicit false

structure Inputs (F : Type) where
  p : F
  q : F
deriving ProvableStruct

def main (i : Var Inputs Field) : Circuit Field (Var field Field) := do
  let v ← ProvableType.witness (α := field) fun env =>
    let iv : Inputs Field := eval env i
    iv.p * iv.q
  Circuit.assertZero (v - i.p * i.q)
  return v

instance elaborated : ElaboratedCircuit Field Inputs field main := by
  elaborate_circuit

def Assumptions (_ : Inputs Field) : Prop := True

def Spec (i : Inputs Field) (o : Field) : Prop := o = i.p * i.q

theorem soundness : Soundness Field main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨hp, hq⟩ := h_input
  linear_combination h_holds

theorem completeness : Completeness Field main Assumptions := by
  circuit_proof_start
  obtain ⟨hp, hq⟩ := h_input
  rw [h_env]
  ring

def circuit : FormalCircuit Field Inputs field where
  main := main
  elaborated := elaborated
  Assumptions := Assumptions
  Spec := Spec
  soundness := soundness
  completeness := completeness

theorem costIs_main (i : Var Inputs Field) : CostIs (main i) ⟨1, 1⟩ := by
  rw [show (⟨1, 1⟩ : Count) = ⟨1, 0⟩ + (⟨0, 1⟩ + Count.zero) by decide]
  unfold main
  refine CostIs.bind (CostIs.provableWitness _) fun _ => ?_
  refine CostIs.bind (CostIs.assertZero _) fun _ => ?_
  exact CostIs.pure _

theorem costIs_call (i : Var Inputs Field) : CostIs (subcircuit circuit i) ⟨1, 1⟩ :=
  CostIs.subcircuit (fun n => costIs_main i n)

theorem shape (i : Var Inputs Field) (hp : Affine i.p) (hq : Affine i.q) :
    IsR1CSCirc (main i) := by
  unfold main
  refine IsR1CSCirc.bind_out (IsR1CSCirc.provableWitness _) fun k => ?_
  refine IsR1CSCirc.bind (IsR1CSCirc.assertZero ?_) fun _ => IsR1CSCirc.pure _
  exact isR1CSRow_sub_mul (Affine.var ⟨k⟩) hp hq

theorem shape_call (i : Var Inputs Field) (hp : Affine i.p) (hq : Affine i.q) :
    IsR1CSCirc (subcircuit circuit i) :=
  IsR1CSCirc.subcircuit (fun n => shape i hp hq n)

theorem call_output (i : Var Inputs Field) (n : ℕ) :
    (subcircuit circuit i).output n = varFromOffset field n :=
  (elaborated.output_eq i n).symm

theorem affine_call_output (i : Var Inputs Field) (n : ℕ) :
    Affine ((subcircuit circuit i).output n) := by
  rw [call_output]
  exact Affine.var ⟨n⟩

theorem computableWitnesses : circuit.ComputableWitnesses := by
  intro n input env env'
  change Operations.forAllFlat n (FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations n)
  apply FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  simp only [main, Circuit.bind_structuralComputableWitnesses_iff,
    Circuit.provableWitness_structuralComputableWitnesses_iff,
    Circuit.assertZero_structuralComputableWitnesses_iff,
    Circuit.pure_structuralComputableWitnesses_iff, and_true]
  intro _ hin
  rw [hin]

theorem output_stable (i : Var Inputs Field) (n : ℕ) {k : ℕ}
    {env env' : ProverEnvironment Field} (hag : env.AgreesBelow k env') (hk : n < k) :
    Expression.eval env.toEnvironment ((subcircuit circuit i).output n) =
      Expression.eval env'.toEnvironment ((subcircuit circuit i).output n) := by
  rw [call_output]
  exact hag n hk

end Solution.Secp256k1ScalarMulFixedBase.LazyVar.MulCell
