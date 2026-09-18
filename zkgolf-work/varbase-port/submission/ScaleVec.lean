import Solution.Secp256k1ScalarMul.Params
import Solution.Secp256k1ScalarMul.Cost
import Challenge.Utils.ComputableWitnessLemmas

/-!
# `ScaleVec` — multiply a limb vector by a single field element

`out[k] = a[k] · b`, one rank-1 row per limb.  Used by the deferred mod-`n`
congruence, where a 256-bit value has to be multiplied by a *scalar* (a 64-bit
magnitude, or a sign bit) without any modular reduction: the resulting cells
stay far below the native prime and are consumed additively by the grouped
carry check.

Cost: `⟨numLimbs, numLimbs⟩`.
-/

namespace Solution.Secp256k1ScalarMul
namespace ScaleVec

structure Inputs (F : Type) where
  a : Emu F
  b : F
deriving ProvableStruct

def main (input : Var Inputs (F circomPrime)) :
    Circuit (F circomPrime) (Var Emu (F circomPrime)) := do
  let out ← ProvableType.witness (α := Emu) fun env =>
    let iv : Inputs (F circomPrime) := eval env input
    Vector.ofFn fun k : Fin numLimbs => (iv.a[k.val]'k.isLt) * iv.b
  let constraints := Vector.ofFn fun k : Fin numLimbs =>
    (input.a[k.val]'k.isLt) * input.b - (out[k.val]'k.isLt)
  Circuit.forEach constraints assertZero
  return out

instance elaborated : ElaboratedCircuit (F circomPrime) Inputs Emu main := by
  elaborate_circuit

def Assumptions (_ : Inputs (F circomPrime)) : Prop := True

def Spec (input : Inputs (F circomPrime)) (out : Emu (F circomPrime)) : Prop :=
  ∀ k : Fin numLimbs, (out[k.val]'k.isLt) = (input.a[k.val]'k.isLt) * input.b

theorem soundness : Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨ha, hb⟩ := h_input
  intro k
  have h := h_holds k
  simp only [Vector.getElem_ofFn, Expression.eval] at h
  rw [← ha, ← hb, Vector.getElem_map]
  linear_combination -h

theorem completeness :
    Completeness (Input := Inputs) (Output := Emu) (F circomPrime) main Assumptions := by
  circuit_proof_start
  obtain ⟨ha, hb⟩ := h_input
  intro i
  have henv := h_env i
  simp only [Vector.getElem_ofFn] at henv ⊢
  simp only [Expression.eval, henv, hb]
  ring

def circuit : FormalCircuit (F circomPrime) Inputs Emu where
  main; elaborated; Assumptions; Spec; soundness; completeness

theorem computableWitnesses : circuit.base.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition
      input env env')
    ((main input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  rcases input with ⟨a, b⟩
  unfold main
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.provableWitness_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.forEach_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.assertZero_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.pure_structuralComputableWitnesses_iff,
    and_true]
  and_intros
  · intro _ h_input
    rw [h_input]
  · intro _
    trivial

end ScaleVec

namespace Cost
open Challenge.CostR1CS
attribute [local irreducible] isR1CSRow r1csProducts operationsIsR1CS flatOperationsIsR1CS

theorem costIs_scaleVec (input : Var ScaleVec.Inputs (F circomPrime)) :
    CostIs (ScaleVec.main input) ⟨numLimbs, numLimbs⟩ := by
  unfold ScaleVec.main
  rw [show (⟨numLimbs, numLimbs⟩ : Count)
      = ⟨numLimbs, 0⟩ + (⟨numLimbs * 0, numLimbs * 1⟩ + Count.zero) from by decide]
  refine CostIs.bind (CostIs.provableWitness _) fun out => ?_
  refine CostIs.bind (CostIs.forEach fun a n => CostIs.assertZero _ n) fun _ => ?_
  exact CostIs.pure _

theorem costIs_sub_scaleVec (input : Var ScaleVec.Inputs (F circomPrime)) :
    CostIs (subcircuit ScaleVec.circuit input) ⟨numLimbs, numLimbs⟩ :=
  CostIs.subcircuit (fun n => costIs_scaleVec input n)

theorem isR1CS_scaleVec (input : Var ScaleVec.Inputs (F circomPrime))
    (ha : AffineW input.a) (hb : Affine input.b) :
    IsR1CSCirc (ScaleVec.main input) := by
  unfold ScaleVec.main
  refine IsR1CSCirc.bind_out (IsR1CSCirc.provableWitness _) fun nout => ?_
  refine IsR1CSCirc.bind ?_ fun _ => IsR1CSCirc.pure _
  refine IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) fun i k => ?_
  refine IsR1CSCirc.assertZero ?_ k
  rw [Vector.getElem_ofFn]
  exact isR1CSRow_mul_sub (ha i.val i.isLt) hb
    (affineW_provableWitness_bigInt _ nout i.val i.isLt)

theorem isR1CS_sub_scaleVec (input : Var ScaleVec.Inputs (F circomPrime))
    (ha : AffineW input.a) (hb : Affine input.b) :
    IsR1CSCirc (subcircuit ScaleVec.circuit input) :=
  IsR1CSCirc.subcircuit (fun n => isR1CS_scaleVec input ha hb n)

theorem affineW_sub_scaleVec (input : Var ScaleVec.Inputs (F circomPrime)) (n : ℕ) :
    AffineW ((subcircuit ScaleVec.circuit input).output n) := by
  have h : (subcircuit ScaleVec.circuit input).output n = varFromOffset Emu n := by
    simp only [circuit_norm, subcircuit, ScaleVec.circuit, ScaleVec.elaborated]
  rw [h]
  exact affineW_varFromOffset _ _

end Cost
end Solution.Secp256k1ScalarMul
