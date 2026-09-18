import Solution.Secp256k1ScalarMul.GLVStepLast
import Solution.Secp256k1ScalarMul.CompleteAddIsInfLow

namespace Solution.Secp256k1ScalarMul
namespace GLVStepLastLow

open Specs.ShortWeierstrass Specs.Secp256k1

abbrev Inputs := GLVStep.Inputs

def main (input : Var Inputs (F circomPrime)) :
    Circuit (F circomPrime) (Var FlaggedPoint (F circomPrime)) := do
  let doubled ← subcircuit Double.circuit { P := input.acc }
  let ent ← subcircuit VarLookup.circuit
    { tx := input.tx, ty := input.ty, tinf := input.tinf,
      b3 := input.b3, b2 := input.b2, b1 := input.b1, b0 := input.b0 }
  let flag ← subcircuit CompleteAddIsInfLow.circuit { P := doubled, Q := ent }
  return { x := zeroConst, y := zeroConst, isInf := flag }

def outputAt (o : ℕ) : Var FlaggedPoint (F circomPrime) :=
  { x := zeroConst, y := zeroConst,
    isInf := (var ⟨o + 1748⟩ : Expression (F circomPrime)) }

private def elaboratedNaive : ElaboratedCircuit (F circomPrime) Inputs FlaggedPoint main := by
  elaborate_circuit

private lemma output_eq_outputAt (input : Var Inputs (F circomPrime)) (o : ℕ) :
    elaboratedNaive.output input o = outputAt o := by
  simp only [elaboratedNaive, circuit_norm, outputAt]
  norm_num [numLimbs, secpParams, limbBits, GroupedEqXV.widthAllocFrom, vW, vMul, vMulD3,
    wfW, wfMul, wfMulD3]

instance elaborated : ElaboratedCircuit (F circomPrime) Inputs FlaggedPoint main :=
  { elaboratedNaive with
    output := fun _ o => outputAt o
    output_eq := output_eq_outputAt }

def Assumptions (input : Inputs (F circomPrime)) : Prop := GLVStep.Assumptions input

def Spec (input : Inputs (F circomPrime)) (out : FlaggedPoint (F circomPrime)) : Prop :=
  ∃ h : GLVStep.nibble input < 16,
    out.isInf = if add curve (GLVStep.dbl (decodePoint input.acc))
      (decodePoint (GLVStep.entry input (GLVStep.nibble input) h)) = .infinity then 1 else 0

theorem soundness : Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [Double.circuit, Double.Assumptions, Double.Spec,
    VarLookup.circuit, VarLookup.Assumptions, VarLookup.Spec,
    CompleteAddIsInfLow.circuit, CompleteAddIsInfLow.Assumptions, CompleteAddIsInfLow.Spec]
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
    CompleteAddIsInfLow.circuit, CompleteAddIsInfLow.Assumptions, CompleteAddIsInfLow.Spec,
    GLVStep.Assumptions]
  obtain ⟨hacc, htab, htabCanon, hb3, hb2, hb1, hb0⟩ := h_assumptions
  obtain ⟨hdbl, hlk, -⟩ := h_env
  obtain ⟨hdblv, -⟩ := hdbl hacc
  obtain ⟨hnib, hent⟩ := hlk ⟨hb3, hb2, hb1, hb0, htab, htabCanon⟩
  exact ⟨hacc, ⟨hb3, hb2, hb1, hb0, htab, htabCanon⟩, ⟨hdblv, hent ▸ htab ⟨_, hnib⟩⟩⟩

def circuit : FormalCircuit (F circomPrime) Inputs FlaggedPoint where
  main := main; elaborated := elaborated; Assumptions := Assumptions; Spec := Spec
  soundness := soundness; completeness := completeness

lemma output_eq (input : Var Inputs (F circomPrime)) (o : ℕ) :
    (subcircuit circuit input).output o = outputAt o := rfl

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
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations offset)
  apply Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  obtain ⟨acc, tx, ty, tinf, b3, b2, b1, b0⟩ := input
  have hd : ∀ (X : Var Double.Inputs (F circomPrime)) (o : ℕ),
      (subcircuit Double.circuit X).localLength o = 1619 := fun _ _ => rfl
  have hl : ∀ (X : Var VarLookup.Inputs (F circomPrime)) (o : ℕ),
      (subcircuit VarLookup.circuit X).localLength o = 122 := fun _ _ => rfl
  have ha : ∀ (X : Var CompleteAdd.Inputs (F circomPrime)) (o : ℕ),
      (subcircuit CompleteAddIsInfLow.circuit X).localLength o = 8 := fun _ _ => rfl
  unfold main
  simp only [Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.pure_structuralComputableWitnesses_iff,
    hd, hl, ha, and_true]
  refine ⟨?_, ?_, ?_⟩
  · refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) Double.circuit _ _ _ ?_ Double.computableWitnesses env env'
    intro k e e' _ _ h
    simp only [circuit_norm, GLVStep.Inputs.mk.injEq, FlaggedPoint.mk.injEq] at h
    simp only [circuit_norm, Double.Inputs.mk.injEq, FlaggedPoint.mk.injEq]
    exact h.1
  · refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) VarLookup.circuit _ _ _ ?_ VarLookup.computableWitnesses env env'
    intro k e e' _ _ h
    simp only [circuit_norm, GLVStep.Inputs.mk.injEq, FlaggedPoint.mk.injEq] at h
    simpa only [circuit_norm, VarLookup.Inputs.mk.injEq] using h.2
  · refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) CompleteAddIsInfLow.circuit _ _ _ ?_
      CompleteAddIsInfLow.computableWitnesses env env'
    intro k e e' hle h_agree h
    simp only [circuit_norm] at hle
    simp only [circuit_norm, GLVStep.Inputs.mk.injEq, FlaggedPoint.mk.injEq] at h
    simp only [circuit_norm, CompleteAdd.Inputs.mk.injEq]
    have hacc : eval e ({ P := acc } : Var Double.Inputs (F circomPrime)) =
        eval e' ({ P := acc } : Var Double.Inputs (F circomPrime)) := by
      simp only [circuit_norm, Double.Inputs.mk.injEq, FlaggedPoint.mk.injEq]
      exact h.1
    have hdbl := double_subOutput_stable { P := acc } (offset := offset)
      hacc h_agree (by omega)
    refine ⟨by simpa only [circuit_norm] using hdbl, ?_⟩
    have hlk := VarLookup.eval_subOutput_of_agreesBelow
      { tx, ty, tinf, b3, b2, b1, b0 } (offset := offset + 1619) h_agree (by omega)
    simpa only [circuit_norm] using hlk

end GLVStepLastLow
end Solution.Secp256k1ScalarMul

namespace Solution.Secp256k1ScalarMul
namespace Cost

open Challenge.CostR1CS
attribute [local irreducible] isR1CSRow r1csProducts operationsIsR1CS flatOperationsIsR1CS

def completeAddIsInfLowCost : Count := ⟨8, 9⟩

theorem costIs_completeAddIsInfLow (input : Var CompleteAdd.Inputs (F circomPrime)) :
    CostIs (CompleteAddIsInfLow.main input) completeAddIsInfLowCost := by
  rw [show completeAddIsInfLowCost = ⟨3, 4⟩ + (⟨2, 2⟩ +
      (⟨1, 1⟩ + (⟨1, 1⟩ + (⟨1, 1⟩ + Count.zero)))) from by decide]
  unfold CompleteAddIsInfLow.main
  refine CostIs.bind (costIs_sub_eqFe _) fun _ => ?_
  refine CostIs.bind (CostIs.subcircuit fun n => by
    simpa only using costIs_isZeroField (input.P.y[0] - input.Q.y[0]) n) fun _ => ?_
  refine CostIs.bind (costIs_assignEqFieldM _) fun _ => ?_
  refine CostIs.bind (costIs_sub_mux _) fun _ => ?_
  exact costIs_sub_mux _

theorem costIs_sub_completeAddIsInfLow (input : Var CompleteAdd.Inputs (F circomPrime)) :
    CostIs (subcircuit CompleteAddIsInfLow.circuit input) completeAddIsInfLowCost :=
  CostIs.subcircuit fun n => costIs_completeAddIsInfLow input n

theorem isR1CS_completeAddIsInfLow (input : Var CompleteAdd.Inputs (F circomPrime))
    (hP : AffineFP input.P) (hQ : AffineFP input.Q) :
    IsR1CSCirc (CompleteAddIsInfLow.main input) := by
  unfold CompleteAddIsInfLow.main
  refine IsR1CSCirc.bind_out (isR1CS_sub_eqFe _ hQ.1 hP.1) fun nx => ?_
  refine IsR1CSCirc.bind_out (IsR1CSCirc.subcircuit fun n =>
    isR1CS_isZeroField (input.P.y[0] - input.Q.y[0])
      (Affine.sub (hP.2.1 0 (by decide)) (hQ.2.1 0 (by decide))) n) fun ny => ?_
  refine IsR1CSCirc.bind_out (isR1CS_assignEqFieldM _ fun w =>
    isR1CSRow_sub_mul (Affine.var w) (affine_sub_eqFe _ nx)
      (Affine.sub (Affine.const 1) (affine_sub_isZeroField _ ny))) fun nc => ?_
  let cancel := (HasAssignEq.assignEq
    ((subcircuit EqFe.circuit { a := input.Q.x, b := input.P.x }).output nx *
      (((1 : F circomPrime) : Expression (F circomPrime)) -
        (subcircuit Gadgets.IsZeroField.circuit
        (input.P.y[0] - input.Q.y[0])).output ny))).output nc
  let s2in : Var (Mux.Inputs field) (F circomPrime) :=
    { selector := input.Q.isInf, ifTrue := input.P.isInf, ifFalse := cancel }
  have apP : @AffineProvable (F circomPrime) field _ input.P.isInf := by
    intro i hi
    simpa [AffineProvable, circuit_norm, explicit_provable_type] using hP.2.2
  have apQ : @AffineProvable (F circomPrime) field _ input.Q.isInf := by
    intro i hi
    simpa [AffineProvable, circuit_norm, explicit_provable_type] using hQ.2.2
  have apC : @AffineProvable (F circomPrime) field _ cancel := by
    intro i hi
    simpa [AffineProvable, circuit_norm, explicit_provable_type, cancel] using (Affine.var (F := F circomPrime) _)
  refine IsR1CSCirc.bind_out (isR1CS_sub_mux s2in hQ.2.2 apP apC) fun ns => ?_
  let outin : Var (Mux.Inputs field) (F circomPrime) :=
    { selector := input.P.isInf, ifTrue := input.Q.isInf,
      ifFalse := (subcircuit (Mux.circuit (M := field)) s2in).output ns }
  exact isR1CS_sub_mux outin hP.2.2 apQ (affineProvable_sub_mux s2in ns)

theorem isR1CS_sub_completeAddIsInfLow (input : Var CompleteAdd.Inputs (F circomPrime))
    (hP : AffineFP input.P) (hQ : AffineFP input.Q) :
    IsR1CSCirc (subcircuit CompleteAddIsInfLow.circuit input) :=
  IsR1CSCirc.subcircuit fun n => isR1CS_completeAddIsInfLow input hP hQ n

def glvStepLastLowCost : Count := ⟨1749, 1761⟩

theorem costIs_glvStepLastLow (input : Var GLVStep.Inputs (F circomPrime)) :
    CostIs (GLVStepLastLow.main input) glvStepLastLowCost := by
  rw [show glvStepLastLowCost = doubleCost +
      (varLookupCost + (completeAddIsInfLowCost + Count.zero)) from by decide]
  unfold GLVStepLastLow.main
  refine CostIs.bind (costIs_sub_double _) fun _ => ?_
  refine CostIs.bind (costIs_sub_varLookup _) fun _ => ?_
  refine CostIs.bind (costIs_sub_completeAddIsInfLow _) fun _ => ?_
  exact CostIs.pure _

theorem costIs_sub_glvStepLastLow (input : Var GLVStep.Inputs (F circomPrime)) :
    CostIs (subcircuit GLVStepLastLow.circuit input) glvStepLastLowCost :=
  CostIs.subcircuit fun n => costIs_glvStepLastLow input n

theorem isR1CS_glvStepLastLow (input : Var GLVStep.Inputs (F circomPrime))
    (hacc : AffineFP input.acc) (htab : AffineTableV input.tx input.ty input.tinf)
    (hb3 : Affine input.b3) (hb2 : Affine input.b2)
    (hb1 : Affine input.b1) (hb0 : Affine input.b0) :
    IsR1CSCirc (GLVStepLastLow.main input) := by
  unfold GLVStepLastLow.main
  refine IsR1CSCirc.bind_out (isR1CS_sub_double _ hacc) fun _ => ?_
  refine IsR1CSCirc.bind_out (isR1CS_sub_varLookup _ htab hb3 hb2 hb1 hb0) fun _ => ?_
  refine IsR1CSCirc.bind_out (isR1CS_sub_completeAddIsInfLow _
    (affineFP_sub_double _ hacc.2.2 _)
    (AffineFP.of_affineProvable (affineProvable_sub_varLookup _ _))) fun _ => ?_
  exact IsR1CSCirc.pure _

theorem isR1CS_sub_glvStepLastLow (input : Var GLVStep.Inputs (F circomPrime))
    (hacc : AffineFP input.acc) (htab : AffineTableV input.tx input.ty input.tinf)
    (hb3 : Affine input.b3) (hb2 : Affine input.b2)
    (hb1 : Affine input.b1) (hb0 : Affine input.b0) :
    IsR1CSCirc (subcircuit GLVStepLastLow.circuit input) :=
  IsR1CSCirc.subcircuit fun n =>
    isR1CS_glvStepLastLow input hacc htab hb3 hb2 hb1 hb0 n

set_option maxRecDepth 4000 in
theorem affineFP_sub_glvStepLastLow (input : Var GLVStep.Inputs (F circomPrime)) (n : ℕ) :
    AffineFP ((subcircuit GLVStepLastLow.circuit input).output n) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [circuit_norm, subcircuit, GLVStepLastLow.circuit, GLVStepLastLow.elaborated]
  · simpa only [zeroConst] using affineW_emuConst 0
  · simpa only [zeroConst] using affineW_emuConst 0
  · exact Affine.var _

end Cost
end Solution.Secp256k1ScalarMul
