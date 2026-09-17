import Solution.Secp256k1ScalarMul.GLVScalarMul
import Solution.Secp256k1ScalarMul.GLVScalarRelationCW
import Solution.Secp256k1ScalarMul.GLVBuildTableCostCW
import Solution.Secp256k1ScalarMul.PointValidCost
import Solution.Secp256k1ScalarMul.GLVMSMCostCW
import Solution.Secp256k1ScalarMul.Lazy.PatBuildTableCost
import Solution.Secp256k1ScalarMul.Lazy.LazyMSMShape
import Challenge.Utils.ComputableWitnessLemmas

namespace Solution.Secp256k1ScalarMul

local notation "CF" => F circomPrime
open Challenge.Utils.ComputableWitnessLemmas

namespace GLVScalarMul

noncomputable def circuit : FormalCircuit (CF)
    ScalarMul.Inputs ScalarMul.Outputs where
  main
  elaborated
  Assumptions
  Spec
  soundness
  completeness

end GLVScalarMul

namespace Cost

open Challenge.CostR1CS

attribute [local irreducible] isR1CSRow r1csProducts operationsIsR1CS flatOperationsIsR1CS

def glvScalarMulCost : Count := ⟨122710, 123688⟩

theorem costIs_glvScalarMul (input : Var ScalarMul.Inputs (CF)) :
    CostIs (GLVScalarMul.main input) glvScalarMulCost := by
  intro offset
  rw [show glvScalarMulCost =
      ⟨9, 0⟩ + (PointValidCost.pointValidCount +
        (⟨260, 0⟩ + (⟨0, 65⟩ + (⟨0, 65⟩ + (⟨0, 65⟩ + (⟨0, 65⟩ +
          (Count.zero + (⟨865, 871⟩ + (PatBuildTable.cost +
            (LazyMSM.cost + Count.zero))))))))))
      from by decide]
  unfold GLVScalarMul.main GLVScalarMul.mainOperations GLVScalarMul.opChain
  simp only [Circuit.operations, Lemmas.operationCount_append,
    GLVScalarMul.qCircuit, GLVScalarMul.qVar, GLVScalarMul.pointValidCircuit,
    GLVScalarMul.coeffCircuit, GLVScalarMul.coeffVar, GLVScalarMul.u1Circuit,
    GLVScalarMul.u2Circuit, GLVScalarMul.v1Circuit, GLVScalarMul.v2Circuit,
    GLVScalarMul.reduceCircuit, GLVScalarMul.reduceVar, GLVScalarMul.relationCircuit,
    GLVScalarMul.tableCircuit, GLVScalarMul.tableVar, GLVScalarMul.msmCircuit,
    GLVScalarMul.infinityCircuit, GLVScalarMul.pvOffset,
    GLVScalarMul.coeffOffset, GLVScalarMul.shortOffset, GLVScalarMul.relationOffset,
    GLVScalarMul.tableOffset, GLVScalarMul.msmOffset, GLVScalarMul.outOffset]
  rw [(CostIs.provableWitness _) offset,
    (PointValidCost.costIs_assertion _) _, (CostIs.provableWitness _) _,
    (CostIs.assertion (circuit := GLV.circuitZ) (b := _)
      (fun o => GLV.costIs_mainZ _ o)) _,
    (CostIs.assertion (circuit := GLV.circuit) (b := _)
      (fun o => GLV.costIs_main _ o)) _,
    (CostIs.assertion (circuit := GLV.circuit) (b := _)
      (fun o => GLV.costIs_main _ o)) _,
    (CostIs.assertion (circuit := GLV.circuit) (b := _)
      (fun o => GLV.costIs_main _ o)) _,
    (CostIs.subcircuit (circuit := GLV.ScalarReduce.circuit) (b := _)
      (fun o => GLV.ScalarReduce.costIs_main _ o)) _,
    (GLVScalarRelation.costIs_assertion _) _,
    (PatBuildTable.costIs_call _) _, (LazyMSM.costIs_call _) _,
    CostIs.pure]
  simp only [show size FlaggedPoint = 9 from rfl,
    show size GLV.Coefficients = 260 from rfl,
    GLVScalarRelation.relationCost, Count.add_assoc, Count.add_zero]

theorem costIs_sub_glvScalarMul (input : Var ScalarMul.Inputs (CF)) :
    CostIs (subcircuit GLVScalarMul.circuit input) glvScalarMulCost :=
  CostIs.subcircuit fun n => costIs_glvScalarMul input n

private theorem affineCoefficients_of_affineProvable
    {c : Var GLV.Coefficients (CF)}
    (h : AffineProvable c) :
    (Affine c.u1.sign ∧ AffineW c.u1.bits) ∧
    (Affine c.u2.sign ∧ AffineW c.u2.bits) ∧
    (Affine c.v1.sign ∧ AffineW c.v1.bits) ∧
    (Affine c.v2.sign ∧ AffineW c.v2.bits) := by
  have hflat : AffineW
      ((#v[c.u1.sign] ++ c.u1.bits) ++
        ((#v[c.u2.sign] ++ c.u2.bits) ++
          ((#v[c.v1.sign] ++ c.v1.bits) ++
            (#v[c.v2.sign] ++ c.v2.bits))) :
        fields ((1 + GLV.coeffBits) + ((1 + GLV.coeffBits) +
          ((1 + GLV.coeffBits) + (1 + GLV.coeffBits))))
          (Expression (CF))) := by
    intro i hi
    simpa [AffineProvable, circuit_norm, explicit_provable_type] using h i hi
  have hu1 := AffineW.left_of_append hflat
  have htail1 := AffineW.right_of_append hflat
  have hu2 := AffineW.left_of_append htail1
  have htail2 := AffineW.right_of_append htail1
  have hv1 := AffineW.left_of_append htail2
  have hv2 := AffineW.right_of_append htail2
  have split : ∀ {c : Var GLV.SignedCoeff (CF)},
      AffineW (#v[c.sign] ++ c.bits : fields (1 + GLV.coeffBits)
        (Expression (CF))) →
      Affine c.sign ∧ AffineW c.bits := by
    intro c hc
    refine ⟨?_, AffineW.right_of_append hc⟩
    simpa using AffineW.left_of_append hc 0 (by decide)
  exact ⟨split hu1, split hu2, split hv1, split hv2⟩

theorem affineW_sub_scalarReduce
    (input : Var GLV.ScalarReduce.Inputs (CF)) (n : ℕ)
    (hbits : AffineW input.bits) :
    AffineW ((subcircuit GLV.ScalarReduce.circuit input).output n) := by
  simpa only [circuit_norm, subcircuit, GLV.ScalarReduce.circuit,
    GLV.ScalarReduce.elaborated] using
    GLV.ScalarReduce.affineW_packBits input.bits hbits

theorem affine_resultWitness
    (input : Var ScalarMul.Inputs CF) (offset : ℕ) :
    AffineFP ((ProvableType.witness (F := CF) (α := FlaggedPoint)
      (GLVScalarMul.resultWitness input)).output offset) := by
  exact AffineFP.of_affineProvable
    (affineProvable_provableWitness (α := FlaggedPoint)
      (GLVScalarMul.resultWitness input) offset)

theorem affine_coefficientWitness
    (input : Var ScalarMul.Inputs CF) (offset : ℕ) :
    let c : Var GLV.Coefficients CF :=
      (ProvableType.witness (F := CF) (α := GLV.Coefficients)
        (GLVScalarMul.coefficientWitness input)).output offset
    (Affine c.u1.sign ∧ AffineW c.u1.bits) ∧
    (Affine c.u2.sign ∧ AffineW c.u2.bits) ∧
    (Affine c.v1.sign ∧ AffineW c.v1.bits) ∧
    (Affine c.v2.sign ∧ AffineW c.v2.bits) := by
  dsimp only
  exact affineCoefficients_of_affineProvable
    (affineProvable_provableWitness (α := GLV.Coefficients)
      (GLVScalarMul.coefficientWitness input) offset)

noncomputable def glvPrefixOps
    (input : Var ScalarMul.Inputs CF) (offset : ℕ)
    (tail : Operations CF) : Operations CF :=
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
  qC.operations offset ++ pvC.operations iPV ++ cC.operations iC ++
    u1C.operations iShort ++ u2C.operations iShort ++
    v1C.operations iShort ++ v2C.operations iShort ++
    reduceC.operations iShort ++ relationC.operations iRel ++ tail

def glvIC (offset : ℕ) : ℕ := offset + 9 + 1046

def glvITable (offset : ℕ) : ℕ :=
  glvIC offset + 260 + 0 + 865

noncomputable def glvTableQ
    (input : Var ScalarMul.Inputs CF) (offset : ℕ) :
    Var FlaggedPoint CF :=
  (ProvableType.witness (F := CF) (α := FlaggedPoint)
    (GLVScalarMul.resultWitness input)).output offset

noncomputable def glvTableCoefficients
    (input : Var ScalarMul.Inputs CF) (offset : ℕ) :
    Var GLV.Coefficients CF :=
  (ProvableType.witness (F := CF) (α := GLV.Coefficients)
    (GLVScalarMul.coefficientWitness input)).output (glvIC offset)

noncomputable def glvTableInput
    (input : Var ScalarMul.Inputs CF) (offset : ℕ) :
    Var GLVBuildTable.Inputs CF :=
  { P := GLVScalarMul.inputPointVar input, Q := glvTableQ input offset
    sign0 := (glvTableCoefficients input offset).u1.sign
    sign1 := (glvTableCoefficients input offset).u2.sign
    sign2 := (glvTableCoefficients input offset).v1.sign
    sign3 := (glvTableCoefficients input offset).v2.sign }

noncomputable def glvTableOps
    (input : Var ScalarMul.Inputs CF) (offset : ℕ) : Operations CF :=
  (subcircuit PatBuildTable.circuit
    (glvTableInput input offset)).operations (glvITable offset)

private noncomputable def glvRawTableInput
    (input : Var ScalarMul.Inputs CF) (offset : ℕ) :
    Var GLVBuildTable.Inputs CF :=
  let Q := (ProvableType.witness (F := CF) (α := FlaggedPoint)
    (GLVScalarMul.resultWitness input)).output offset
  let c := (ProvableType.witness (F := CF) (α := GLV.Coefficients)
    (GLVScalarMul.coefficientWitness input)).output (glvIC offset)
  { P := GLVScalarMul.inputPointVar input, Q
    sign0 := c.u1.sign, sign1 := c.u2.sign
    sign2 := c.v1.sign, sign3 := c.v2.sign }

private def glvRawITable (offset : ℕ) : ℕ :=
  glvITable offset

private noncomputable def glvRawTableOps
    (input : Var ScalarMul.Inputs CF) (offset : ℕ) : Operations CF :=
  (subcircuit PatBuildTable.circuit
    (glvRawTableInput input offset)).operations (glvRawITable offset)

noncomputable def glvTailFromOps
    (input : Var ScalarMul.Inputs CF) (offset : ℕ)
    (head : Operations CF) : Operations CF :=
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
  head ++ msmC.operations iMSM ++ infC.operations iOut

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem glvRawTableInput_eq
    (input : Var ScalarMul.Inputs CF) (offset : ℕ) :
    glvRawTableInput input offset = glvTableInput input offset := rfl

private theorem glvRawITable_eq (offset : ℕ) :
    glvRawITable offset = glvITable offset := rfl

set_option maxRecDepth 8192 in
private theorem glvRawTableOps_eq
    (input : Var ScalarMul.Inputs CF) (offset : ℕ) :
    glvRawTableOps input offset = glvTableOps input offset := by
  unfold glvRawTableOps glvTableOps
  rw [glvRawTableInput_eq, glvRawITable_eq]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem glvScalarMul_operations_raw_eq
    (input : Var ScalarMul.Inputs CF) (offset : ℕ) :
    (GLVScalarMul.main input).operations offset =
      glvTailFromOps input offset
        (glvPrefixOps input offset (glvRawTableOps input offset)) := by
  simp only [GLVScalarMul.main, GLVScalarMul.mainOperations, GLVScalarMul.opChain,
    GLVScalarMul.qCircuit, GLVScalarMul.qVar, GLVScalarMul.pointValidCircuit,
    GLVScalarMul.coeffCircuit, GLVScalarMul.coeffVar, GLVScalarMul.u1Circuit,
    GLVScalarMul.u2Circuit, GLVScalarMul.v1Circuit, GLVScalarMul.v2Circuit,
    GLVScalarMul.reduceCircuit, GLVScalarMul.reduceVar, GLVScalarMul.relationCircuit,
    GLVScalarMul.tableCircuit, GLVScalarMul.tableVar, GLVScalarMul.msmCircuit,
    GLVScalarMul.infinityCircuit, GLVScalarMul.pvOffset,
    GLVScalarMul.coeffOffset, GLVScalarMul.shortOffset, GLVScalarMul.relationOffset,
    GLVScalarMul.tableOffset, GLVScalarMul.msmOffset, GLVScalarMul.outOffset,
    Circuit.operations, glvTailFromOps, glvPrefixOps, glvRawTableOps, glvRawTableInput,
    glvRawITable, glvIC, glvITable]
  simp only [List.append_assoc]

theorem glvScalarMul_operations_eq
    (input : Var ScalarMul.Inputs CF) (offset : ℕ) :
    (GLVScalarMul.main input).operations offset =
      glvTailFromOps input offset
        (glvPrefixOps input offset (glvTableOps input offset)) := by
  rw [glvScalarMul_operations_raw_eq, glvRawTableOps_eq]

theorem appendR1CS {ops₁ ops₂ : Operations CF}
    (h₁ : operationsIsR1CS ops₁) (h₂ : operationsIsR1CS ops₂) :
    operationsIsR1CS (ops₁ ++ ops₂) :=
  (Lemmas.operationsIsR1CS_append ops₁ ops₂).2 ⟨h₁, h₂⟩

theorem isR1CS_tableOpsExact
    (X : Var GLVBuildTable.Inputs CF)
    (hP : AffineFP X.P) (hQ : AffineFP X.Q)
    (hs0 : Affine X.sign0) (hs1 : Affine X.sign1)
    (hs2 : Affine X.sign2) (hs3 : Affine X.sign3) (n : ℕ) :
    operationsIsR1CS
      ((subcircuit PatBuildTable.circuit X).operations n) :=
  (PatBuildTable.isR1CS_call X hP hQ hs0 hs1 hs2 hs3) n


end Cost
end Solution.Secp256k1ScalarMul
