import Solution.Secp256k1ScalarMul.GLVStep
import Solution.Secp256k1ScalarMul.CompleteAddIsInf

/-!
# Final joint-MSM step — `GLVStepLast`

Identical to `GLVStep` (double the accumulator, look up the table entry) except
that the concluding complete addition is replaced by `CompleteAddIsInf`, which
computes only the infinity flag of the sum.  This is sound for the *last* step
of the MSM, where the accumulator's coordinates are never consumed — only the
final infinity assertion reads its `isInf` flag.  The output coordinates are
filled with the canonical zero constant.
-/

namespace Solution.Secp256k1ScalarMul
namespace GLVStepLast

open Specs.ShortWeierstrass Specs.Secp256k1

/-- Same inputs as an ordinary `GLVStep`. -/
abbrev Inputs := GLVStep.Inputs

def main (input : Var GLVStep.Inputs (F circomPrime)) :
    Circuit (F circomPrime) (Var FlaggedPoint (F circomPrime)) := do
  let doubled ← subcircuit Double.circuit { P := input.acc }
  let ent ← subcircuit VarLookup.circuit
    { tx := input.tx, ty := input.ty, tinf := input.tinf,
      b3 := input.b3, b2 := input.b2, b1 := input.b1, b0 := input.b0 }
  let flag ← subcircuit CompleteAddIsInf.circuit { P := doubled, Q := ent }
  return { x := zeroConst, y := zeroConst, isInf := flag }

def outputAt (o : ℕ) : Var FlaggedPoint (F circomPrime) :=
  { x := zeroConst,
    y := zeroConst,
    isInf := (var ⟨o + 1749⟩ : Expression (F circomPrime)) }

private def elaboratedNaive :
    ElaboratedCircuit (F circomPrime) GLVStep.Inputs FlaggedPoint main := by
  elaborate_circuit

private lemma output_eq_outputAt (input : Var GLVStep.Inputs (F circomPrime)) (o : ℕ) :
    elaboratedNaive.output input o = outputAt o := by
  simp only [elaboratedNaive, circuit_norm, main, CompleteAddIsInf.output_eq, outputAt]
  norm_num [numLimbs, secpParams, limbBits, GroupedEqXV.widthAllocFrom, vW, vMul, vMulD3,
    wfW, wfMul, wfMulD3]

instance elaborated : ElaboratedCircuit (F circomPrime) GLVStep.Inputs FlaggedPoint main :=
  { elaboratedNaive with
    output := fun _ o => outputAt o
    output_eq := output_eq_outputAt }

def Assumptions (input : GLVStep.Inputs (F circomPrime)) : Prop :=
  GLVStep.Assumptions input

/-- The output's infinity flag is `1` exactly when the doubled accumulator plus
the selected table entry is the point at infinity. -/
def Spec (input : GLVStep.Inputs (F circomPrime)) (out : FlaggedPoint (F circomPrime)) : Prop :=
  ∃ h : GLVStep.nibble input < 16,
    out.isInf =
      if add curve (GLVStep.dbl (decodePoint input.acc))
          (decodePoint (GLVStep.entry input (GLVStep.nibble input) h)) = .infinity
        then 1 else 0

theorem soundness : Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [Double.circuit, Double.Assumptions, Double.Spec,
    VarLookup.circuit, VarLookup.Assumptions, VarLookup.Spec,
    CompleteAddIsInf.circuit, CompleteAddIsInf.Assumptions, CompleteAddIsInf.Spec]
  obtain ⟨hacc, htab, htabCanon, hb3, hb2, hb1, hb0⟩ := h_assumptions
  obtain ⟨hdbl, hlk, hadd⟩ := h_holds
  obtain ⟨hdblv, hdble⟩ := hdbl hacc
  obtain ⟨hnib, hent⟩ := hlk ⟨hb3, hb2, hb1, hb0, htab, htabCanon⟩
  have hentv := htab ⟨_, hnib⟩
  have hflag := hadd ⟨hdblv, hent ▸ hentv⟩
  refine ⟨hnib, ?_⟩
  rw [hent, hdble] at hflag
  exact hflag

theorem completeness : Completeness (F circomPrime) main Assumptions := by
  circuit_proof_start [Double.circuit, Double.Assumptions, Double.Spec,
    VarLookup.circuit, VarLookup.Assumptions, VarLookup.Spec,
    CompleteAddIsInf.circuit, CompleteAddIsInf.Assumptions, CompleteAddIsInf.Spec,
    GLVStep.Assumptions]
  obtain ⟨hacc, htab, htabCanon, hb3, hb2, hb1, hb0⟩ := h_assumptions
  obtain ⟨hdbl, hlk, -⟩ := h_env
  obtain ⟨hdblv, -⟩ := hdbl hacc
  obtain ⟨hnib, hent⟩ := hlk ⟨hb3, hb2, hb1, hb0, htab, htabCanon⟩
  have hentv := htab ⟨_, hnib⟩
  exact ⟨hacc, ⟨hb3, hb2, hb1, hb0, htab, htabCanon⟩, ⟨hdblv, hent ▸ hentv⟩⟩

def circuit : FormalCircuit (F circomPrime) GLVStep.Inputs FlaggedPoint where
  main := main
  elaborated := elaborated
  Assumptions := Assumptions
  Spec := Spec
  soundness := soundness
  completeness := completeness

lemma output_eq (input : Var GLVStep.Inputs (F circomPrime)) (o : ℕ) :
    (subcircuit circuit input).output o = outputAt o := by
  rfl

private lemma cond_completeAdd {e e' : ProverEnvironment (F circomPrime)}
    (P Q : Var FlaggedPoint (F circomPrime))
    (hP : eval e P = eval e' P) (hQ : eval e Q = eval e' Q) :
    eval e ({ P := P, Q := Q } : Var CompleteAdd.Inputs (F circomPrime)) =
      eval e' ({ P := P, Q := Q } : Var CompleteAdd.Inputs (F circomPrime)) := by
  simp only [circuit_norm] at hP hQ ⊢
  rw [CompleteAdd.Inputs.mk.injEq]
  exact ⟨hP, hQ⟩

private lemma double_subOutput_stable
    (input : Var Double.Inputs (F circomPrime)) {offset k : ℕ}
    {env env' : ProverEnvironment (F circomPrime)}
    (h_input : eval env input = eval env' input)
    (h_agree : env.AgreesBelow k env') (hk : offset + 1619 ≤ k) :
    eval env ((subcircuit Double.circuit input).output offset) =
      eval env' ((subcircuit Double.circuit input).output offset) := by
  have h := Double.eval_output_of_agreesBelow input h_input h_agree hk
  rw [Double.elaborated.output_eq input offset] at h
  exact h

theorem computableWitnesses : circuit.base.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition
      input env env')
    ((main input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  obtain ⟨acc, tx, ty, tinf, b3, b2, b1, b0⟩ := input
  have hdbl : ∀ (X : Var Double.Inputs (F circomPrime)) (o : ℕ),
      (subcircuit Double.circuit X).localLength o = 1619 := fun _ _ => rfl
  have hlk : ∀ (X : Var VarLookup.Inputs (F circomPrime)) (o : ℕ),
      (subcircuit VarLookup.circuit X).localLength o = 122 := fun _ _ => rfl
  have hca : ∀ (X : Var CompleteAdd.Inputs (F circomPrime)) (o : ℕ),
      (subcircuit CompleteAddIsInf.circuit X).localLength o = 9 := fun _ _ => rfl
  unfold main
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.pure_structuralComputableWitnesses_iff,
    hdbl, hlk, hca, and_true]
  refine ⟨?_, ?_, ?_⟩
  · refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := GLVStep.Inputs) Double.circuit _ _ _ ?_ Double.computableWitnesses env env'
    intro k e e' _ _ h_in
    simp only [circuit_norm, GLVStep.Inputs.mk.injEq, FlaggedPoint.mk.injEq] at h_in
    obtain ⟨⟨hax, hay, hai'⟩, _, _, _, _, _, _, _⟩ := h_in
    simp only [circuit_norm]
    rw [Double.Inputs.mk.injEq, FlaggedPoint.mk.injEq]
    exact ⟨hax, hay, hai'⟩
  · refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := GLVStep.Inputs) VarLookup.circuit _ _ _ ?_ VarLookup.computableWitnesses env env'
    intro k e e' _ _ h_in
    simp only [circuit_norm, GLVStep.Inputs.mk.injEq, FlaggedPoint.mk.injEq] at h_in
    obtain ⟨_, htx, hty, htinf, hb3', hb2', hb1', hb0'⟩ := h_in
    simp only [circuit_norm]
    rw [VarLookup.Inputs.mk.injEq]
    exact ⟨htx, hty, htinf, hb3', hb2', hb1', hb0'⟩
  · refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := GLVStep.Inputs) CompleteAddIsInf.circuit _ _ _ ?_ CompleteAddIsInf.computableWitnesses env env'
    intro k e e' hle h_agree h_in
    simp only [circuit_norm] at hle
    have hacc_in : eval e ({ P := acc } : Var Double.Inputs (F circomPrime))
        = eval e' ({ P := acc } : Var Double.Inputs (F circomPrime)) := by
      simp only [circuit_norm, GLVStep.Inputs.mk.injEq, FlaggedPoint.mk.injEq,
        Double.Inputs.mk.injEq] at h_in ⊢
      exact h_in.1
    exact cond_completeAdd _ _
      (double_subOutput_stable { P := acc } (offset := offset)
        hacc_in h_agree (by omega))
      (VarLookup.eval_subOutput_of_agreesBelow
        { tx := tx, ty := ty, tinf := tinf,
          b3 := b3, b2 := b2, b1 := b1, b0 := b0 }
        (offset := offset + 1619) h_agree (by omega))

end GLVStepLast
end Solution.Secp256k1ScalarMul
