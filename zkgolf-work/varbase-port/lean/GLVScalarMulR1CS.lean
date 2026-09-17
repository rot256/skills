import Solution.Secp256k1ScalarMul.GLVScalarMulTableR1CS

namespace Solution.Secp256k1ScalarMul

local notation "CF" => F circomPrime
open Challenge.Utils.ComputableWitnessLemmas

namespace Cost

open Challenge.CostR1CS

attribute [local irreducible] isR1CSRow r1csProducts operationsIsR1CS flatOperationsIsR1CS

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem isR1CS_glvPrefix
    (input : Var ScalarMul.Inputs CF) (hbits : AffineW input.bits)
    (offset : ℕ) {tail : Operations CF}
    (htail : operationsIsR1CS tail) :
    operationsIsR1CS (glvPrefixOps input offset tail) := by
  let iPV : ℕ := offset + 9
  let iC : ℕ := iPV + 1046
  let iShort : ℕ := iC + 260
  let iRel : ℕ := iShort + 0
  let qC : Circuit CF (Var FlaggedPoint CF) :=
    ProvableType.witness (F := CF) (α := FlaggedPoint)
      (GLVScalarMul.resultWitness input)
  let Q : Var FlaggedPoint CF := qC.output offset
  let pvC : Circuit CF (Var PointValid.Outputs CF) := PointValid.circuit Q
  let cC : Circuit CF (Var GLV.Coefficients CF) :=
    ProvableType.witness (F := CF) (α := GLV.Coefficients)
      (GLVScalarMul.coefficientWitness input)
  let c : Var GLV.Coefficients CF := cC.output iC
  let u1C : Circuit CF Unit := GLV.circuitZ c.u1
  let u2C : Circuit CF Unit := GLV.circuit c.u2
  let v1C : Circuit CF Unit := GLV.circuit c.v1
  let v2C : Circuit CF Unit := GLV.circuit c.v2
  let reduceInput : Var GLV.ScalarReduce.Inputs CF := { bits := input.bits }
  let reduceC : Circuit CF (Var Emu CF) :=
    subcircuit GLV.ScalarReduce.circuit reduceInput
  let s : Var Emu CF := reduceC.output iShort
  let relationInput : Var GLVScalarRelation.Inputs CF :=
    { s, u1 := c.u1, u2 := c.u2, v1 := c.v1, v2 := c.v2 }
  let relationC : Circuit CF Unit := GLVScalarRelation.circuit relationInput
  have hQ : AffineFP Q := by
    simpa only [Q, qC] using affine_resultWitness input offset
  have hc :
      (Affine c.u1.sign ∧ AffineW c.u1.bits) ∧
      (Affine c.u2.sign ∧ AffineW c.u2.bits) ∧
      (Affine c.v1.sign ∧ AffineW c.v1.bits) ∧
      (Affine c.v2.sign ∧ AffineW c.v2.bits) := by
    simpa only [c, cC] using affine_coefficientWitness input iC
  have hs : AffineW s := affineW_sub_scalarReduce reduceInput iShort hbits
  have hq : operationsIsR1CS (qC.operations offset) :=
    (IsR1CSCirc.provableWitness (α := FlaggedPoint)
      (GLVScalarMul.resultWitness input)) offset
  have hpv : operationsIsR1CS (pvC.operations iPV) :=
    (PointValidCost.isR1CS_assertion Q hQ.1 hQ.2.1 hQ.2.2) iPV
  have hcw : operationsIsR1CS (cC.operations iC) :=
    (IsR1CSCirc.provableWitness (α := GLV.Coefficients)
      (GLVScalarMul.coefficientWitness input)) iC
  have hu1 : operationsIsR1CS (u1C.operations iShort) :=
    (IsR1CSCirc.assertion (circuit := GLV.circuitZ) (b := c.u1)
      (fun n => GLV.isR1CS_mainZ c.u1 hc.1.1 hc.1.2 n)) iShort
  have hu2 : operationsIsR1CS (u2C.operations iShort) :=
    (IsR1CSCirc.assertion (circuit := GLV.circuit) (b := c.u2)
      (fun n => GLV.isR1CS_main c.u2 hc.2.1.1 hc.2.1.2 n)) iShort
  have hv1 : operationsIsR1CS (v1C.operations iShort) :=
    (IsR1CSCirc.assertion (circuit := GLV.circuit) (b := c.v1)
      (fun n => GLV.isR1CS_main c.v1 hc.2.2.1.1 hc.2.2.1.2 n)) iShort
  have hv2 : operationsIsR1CS (v2C.operations iShort) :=
    (IsR1CSCirc.assertion (circuit := GLV.circuit) (b := c.v2)
      (fun n => GLV.isR1CS_main c.v2 hc.2.2.2.1 hc.2.2.2.2 n)) iShort
  have hreduce : operationsIsR1CS (reduceC.operations iShort) :=
    (IsR1CSCirc.subcircuit (circuit := GLV.ScalarReduce.circuit)
      (b := reduceInput) (fun n =>
        GLV.ScalarReduce.isR1CS_main reduceInput hbits n)) iShort
  have hrelation : operationsIsR1CS (relationC.operations iRel) :=
    (GLVScalarRelation.isR1CS_assertion relationInput hs
      hc.1.1 hc.1.2 hc.2.1.1 hc.2.1.2
      hc.2.2.1.1 hc.2.2.1.2 hc.2.2.2.1 hc.2.2.2.2) iRel
  have hop : glvPrefixOps input offset tail =
      qC.operations offset ++ pvC.operations iPV ++ cC.operations iC ++
      u1C.operations iShort ++ u2C.operations iShort ++
      v1C.operations iShort ++ v2C.operations iShort ++
      reduceC.operations iShort ++ relationC.operations iRel ++ tail := rfl
  rw [hop]
  have h01 := appendR1CS hq hpv
  have h02 := appendR1CS h01 hcw
  have h03 := appendR1CS h02 hu1
  have h04 := appendR1CS h03 hu2
  have h05 := appendR1CS h04 hv1
  have h06 := appendR1CS h05 hv2
  have h07 := appendR1CS h06 hreduce
  have h08 := appendR1CS h07 hrelation
  exact appendR1CS h08 htail

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem isR1CS_glvTailFrom
    (input : Var ScalarMul.Inputs CF) (hpx : AffineW input.px)
    (hpy : AffineW input.py) (offset : ℕ)
    {head : Operations CF} (hhead : operationsIsR1CS head) :
    operationsIsR1CS (glvTailFromOps input offset head) := by
  let iPV : ℕ := offset + 9
  let iC : ℕ := iPV + 1046
  let iShort : ℕ := iC + 260
  let iRel : ℕ := iShort + 0
  let iTable : ℕ := iRel + 865
  let iMSM : ℕ := iTable + 16366
  let iOut : ℕ := iMSM + 104164
  let qC : Circuit CF (Var FlaggedPoint CF) :=
    ProvableType.witness (F := CF) (α := FlaggedPoint)
      (GLVScalarMul.resultWitness input)
  let Q : Var FlaggedPoint CF := qC.output offset
  let cC : Circuit CF (Var GLV.Coefficients CF) :=
    ProvableType.witness (F := CF) (α := GLV.Coefficients)
      (GLVScalarMul.coefficientWitness input)
  let c : Var GLV.Coefficients CF := cC.output iC
  let tableInput : Var GLVBuildTable.Inputs CF :=
    { P := GLVScalarMul.inputPointVar input, Q
      sign0 := c.u1.sign, sign1 := c.u2.sign
      sign2 := c.v1.sign, sign3 := c.v2.sign }
  let tableC : Circuit CF (Var GLVBuildTable.Table CF) :=
    subcircuit PatBuildTable.circuit tableInput
  let table : Var GLVBuildTable.Table CF := tableC.output iTable
  let msmInput : Var GLVMSM.Inputs CF :=
    { tx := table.tx, ty := table.ty, tinf := table.tinf
      m0 := c.u1.bits, m1 := c.u2.bits
      m2 := c.v1.bits, m3 := c.v2.bits }
  let msmC : Circuit CF (Var unit CF) := LazyMSM.circuit msmInput
  let infC : Circuit CF Unit := pure ()
  have hQ : AffineFP Q := by
    simpa only [Q, qC] using affine_resultWitness input offset
  have hc :
      (Affine c.u1.sign ∧ AffineW c.u1.bits) ∧
      (Affine c.u2.sign ∧ AffineW c.u2.bits) ∧
      (Affine c.v1.sign ∧ AffineW c.v1.bits) ∧
      (Affine c.v2.sign ∧ AffineW c.v2.bits) := by
    simpa only [c, cC] using affine_coefficientWitness input iC
  have hP : AffineFP tableInput.P := by
    dsimp only [tableInput, GLVScalarMul.inputPointVar]
    exact ⟨hpx, hpy, Affine.const 0⟩
  have ht : AffineTableV table.tx table.ty table.tinf :=
    PatBuildTable.affineTable_call tableInput iTable hP hQ
  have hmsm : operationsIsR1CS (msmC.operations iMSM) :=
    (LazyMSM.shape_call msmInput ht
      hc.1.2 hc.2.1.2 hc.2.2.1.2 hc.2.2.2.2) iMSM
  have hinf : operationsIsR1CS (infC.operations iOut) :=
    (IsR1CSCirc.pure ()) iOut
  have hop : glvTailFromOps input offset head =
      head ++ msmC.operations iMSM ++
      infC.operations iOut := rfl
  rw [hop]
  have h01 := appendR1CS hhead hmsm
  exact appendR1CS h01 hinf

set_option maxRecDepth 8192 in
theorem isR1CS_glvScalarMul (input : Var ScalarMul.Inputs (CF))
    (hbits : AffineW input.bits) (hpx : AffineW input.px)
    (hpy : AffineW input.py) : IsR1CSCirc (GLVScalarMul.main input) := by
  intro offset
  rw [glvScalarMul_operations_eq]
  exact isR1CS_glvTailFrom input hpx hpy offset
    (isR1CS_glvPrefix input hbits offset
      (isR1CS_glvTable input hpx hpy offset))

set_option maxRecDepth 8192 in
private theorem affineW_reverse {m : ℕ}
    (v : Var (fields m) CF) (h : AffineW v) : AffineW v.reverse := by
  intro i hi
  rw [Vector.getElem_reverse hi]
  exact h _ (by omega)

attribute [local irreducible] GLVScalarMul.main

set_option maxRecDepth 8192 in
theorem affineOut_glvScalarMul (input : Var ScalarMul.Inputs (CF)) (n : ℕ) :
    AffineW ((GLVScalarMul.main input).output n).x ∧
      AffineW ((GLVScalarMul.main input).output n).y ∧
      Affine ((GLVScalarMul.main input).output n).isInf := by
  let Q : Var FlaggedPoint CF :=
    varFromOffset FlaggedPoint n
  let pv := PointValid.circuit.output Q (n + 9)
  let out := GLVScalarMul.outputFromValidated Q pv
  have hout : (GLVScalarMul.main input).output n = out := by
    simpa only [Q, pv, out] using GLVScalarMul.mainCircuitOutput_eq input n
  have hQ : AffineFP Q := by
    simpa only [Q] using affine_resultWitness input n
  have hpv := PointValidCost.affineOut_circuit Q hQ.1 hQ.2.1 (n + 9)
  have haff : AffineW out.x ∧ AffineW out.y ∧ Affine out.isInf := by
    dsimp only [out, GLVScalarMul.outputFromValidated, pv]
    exact ⟨affineW_reverse _ hpv.1, affineW_reverse _ hpv.2, hQ.2.2⟩
  rw [hout]
  exact haff

theorem affineOut_sub_glvScalarMul
    (input : Var ScalarMul.Inputs (CF)) (n : ℕ) :
  AffineW ((subcircuit GLVScalarMul.circuit input).output n).x ∧
      AffineW ((subcircuit GLVScalarMul.circuit input).output n).y ∧
      Affine ((subcircuit GLVScalarMul.circuit input).output n).isInf := by
  unfold subcircuit
  change
    AffineW (GLVScalarMul.circuit.output input n).x ∧
      AffineW (GLVScalarMul.circuit.output input n).y ∧
      Affine (GLVScalarMul.circuit.output input n).isInf
  unfold GLVScalarMul.circuit FormalCircuitBase.output
  change
    AffineW (ElaboratedCircuit.output GLVScalarMul.main input n).x ∧
      AffineW (ElaboratedCircuit.output GLVScalarMul.main input n).y ∧
      Affine (ElaboratedCircuit.output GLVScalarMul.main input n).isInf
  rw [← GLVScalarMul.elaborated.output_eq input n]
  exact affineOut_glvScalarMul input n

theorem isR1CS_sub_glvScalarMul (input : Var ScalarMul.Inputs (CF))
    (hinput : AffineW input.bits ∧ AffineW input.px ∧ AffineW input.py) :
    IsR1CSCirc (subcircuit GLVScalarMul.circuit input) :=
  IsR1CSCirc.subcircuit fun n =>
    isR1CS_glvScalarMul input hinput.1 hinput.2.1 hinput.2.2 n

end Cost

end Solution.Secp256k1ScalarMul
