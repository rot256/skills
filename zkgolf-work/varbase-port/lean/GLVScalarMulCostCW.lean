import Solution.Secp256k1ScalarMul.GLVScalarMulCWU1
import Solution.Secp256k1ScalarMul.GLVScalarMulCWU2
import Solution.Secp256k1ScalarMul.GLVScalarMulCWV1
import Solution.Secp256k1ScalarMul.GLVScalarMulCWV2

namespace Solution.Secp256k1ScalarMul

local notation "CF" => F circomPrime
open Challenge.Utils.ComputableWitnessLemmas

namespace GLVScalarMul

attribute [local irreducible] main PointValid.main GLVScalarRelation.main
  PatBuildTable.main PatBuildTable.tableAt LazyMSM.main AssertInfinity.main

private theorem structuralReduce
    (input : Var ScalarMul.Inputs CF) (offset : ℕ)
    (env env' : ProverEnvironment CF) :
    SCW input env env' (shortOffset offset)
      ((reduceCircuit input).operations (shortOffset offset)) := by
  simp only [SCW, reduceCircuit]
  rw [FormalCircuit.subcircuit_structuralComputableWitnesses_iff]
  refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
    (Parent := ScalarMul.Inputs) GLV.ScalarReduce.circuit input
    { bits := input.bits } _ ?_ GLV.ScalarReduce.computableWitnesses env env'
  intro k e e' _ _ h_in
  simpa only [circuit_norm, GLV.ScalarReduce.Inputs.mk.injEq] using
    congrArg (fun x : ScalarMul.Inputs CF => x.bits) h_in

private theorem structuralRelation
    (input : Var ScalarMul.Inputs CF) (offset : ℕ)
    (env env' : ProverEnvironment CF) :
    SCW input env env' (relationOffset offset)
      ((relationCircuit input offset).operations (relationOffset offset)) := by
  simp only [SCW, relationCircuit, reduceVar, reduceCircuit, coeffVar, coeffCircuit]
  rw [FormalAssertion.assertion_structuralComputableWitnesses_iff]
  refine FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
    (Parent := ScalarMul.Inputs) GLVScalarRelation.circuit input
    { s := (subcircuit GLV.ScalarReduce.circuit { bits := input.bits }).output
        (shortOffset offset)
      u1 := ((ProvableType.witness (F := CF) (α := GLV.Coefficients)
        (coefficientWitness input)).output (coeffOffset offset)).u1
      u2 := ((ProvableType.witness (F := CF) (α := GLV.Coefficients)
        (coefficientWitness input)).output (coeffOffset offset)).u2
      v1 := ((ProvableType.witness (F := CF) (α := GLV.Coefficients)
        (coefficientWitness input)).output (coeffOffset offset)).v1
      v2 := ((ProvableType.witness (F := CF) (α := GLV.Coefficients)
        (coefficientWitness input)).output (coeffOffset offset)).v2 }
    (relationOffset offset) ?_ GLVScalarRelation.computableWitnesses env env'
  intro k e e' hle h_agree h_input
  have hs := scalarReduceOutput_stable input.bits (off := shortOffset offset)
    h_agree (by
      simp only [relationOffset] at hle ⊢
      omega) (by
        simpa only [circuit_norm] using
          congrArg (fun x : ScalarMul.Inputs (CF) => x.bits) h_input)
  have hc' := coefficientOutput_stable input (off := coeffOffset offset)
    h_agree (by
      simp only [relationOffset, shortOffset] at hle ⊢
      omega)
  simp only [circuit_norm, GLVScalarRelation.Inputs.mk.injEq] at ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [subcircuit, circuit_norm] using hs
  · simpa only [circuit_norm] using
      congrArg (fun c : GLV.Coefficients (CF) => c.u1) hc'
  · simpa only [circuit_norm] using
      congrArg (fun c : GLV.Coefficients (CF) => c.u2) hc'
  · simpa only [circuit_norm] using
      congrArg (fun c : GLV.Coefficients (CF) => c.v1) hc'
  · simpa only [circuit_norm] using
      congrArg (fun c : GLV.Coefficients (CF) => c.v2) hc'

private theorem structuralTable
    (input : Var ScalarMul.Inputs CF) (offset : ℕ)
    (env env' : ProverEnvironment CF) :
    SCW input env env' (tableOffset offset)
      ((tableCircuit input offset).operations (tableOffset offset)) := by
  simp only [SCW, tableCircuit, qVar, qCircuit, coeffVar, coeffCircuit]
  rw [FormalCircuit.subcircuit_structuralComputableWitnesses_iff]
  refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
    (Parent := ScalarMul.Inputs) PatBuildTable.circuit input
    _ _ ?_ PatBuildTable.computableWitnesses env env'
  intro k e e' hle h_agree h_in
  have hQ := resultOutput_stable input (off := offset) h_agree (by
    simp only [tableOffset, relationOffset, shortOffset, coeffOffset, pvOffset] at hle
    omega)
  have hc' := coefficientOutput_stable input (off := coeffOffset offset)
    h_agree (by
      simp only [tableOffset, relationOffset, shortOffset, coeffOffset, pvOffset] at hle ⊢
      omega)
  simp only [circuit_norm, ScalarMul.Inputs.mk.injEq] at h_in
  simp only [circuit_norm, GLVBuildTable.Inputs.mk.injEq,
    FlaggedPoint.mk.injEq] at ⊢
  refine ⟨⟨?_, ?_, rfl⟩, ?_, ?_, ?_, ?_, ?_⟩
  · exact h_in.2.1
  · exact h_in.2.2
  · simpa only [circuit_norm, FlaggedPoint.mk.injEq] using hQ
  · simpa only [circuit_norm] using
      congrArg (fun c : GLV.Coefficients (CF) => c.u1.sign) hc'
  · simpa only [circuit_norm] using
      congrArg (fun c : GLV.Coefficients (CF) => c.u2.sign) hc'
  · simpa only [circuit_norm] using
      congrArg (fun c : GLV.Coefficients (CF) => c.v1.sign) hc'
  · simpa only [circuit_norm] using
      congrArg (fun c : GLV.Coefficients (CF) => c.v2.sign) hc'

private theorem structuralMSM
    (input : Var ScalarMul.Inputs CF) (offset : ℕ)
    (env env' : ProverEnvironment CF) :
    SCW input env env' (msmOffset offset)
      ((msmCircuit input offset).operations (msmOffset offset)) := by
  simp only [SCW, msmCircuit, tableVar, tableCircuit, qVar, qCircuit,
    coeffVar, coeffCircuit]
  rw [generalSubcircuit_structuralComputableWitnesses_iff]
  refine GeneralFormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
    (Parent := ScalarMul.Inputs) LazyMSM.circuit input
    _ _ ?_ LazyMSM.computableWitnesses env env'
  intro k e e' hle h_agree h_in
  have hc' := coefficientOutput_stable input (off := coeffOffset offset)
    h_agree (by
      simp only [msmOffset, tableOffset, relationOffset, shortOffset, coeffOffset, pvOffset] at hle ⊢
      omega)
  let tableInput : Var GLVBuildTable.Inputs (CF) :=
    { P := inputPointVar input
      Q := (ProvableType.witness (F := CF) (α := FlaggedPoint)
        (resultWitness input)).output offset
      sign0 := ((ProvableType.witness (F := CF) (α := GLV.Coefficients)
        (coefficientWitness input)).output (coeffOffset offset)).u1.sign
      sign1 := ((ProvableType.witness (F := CF) (α := GLV.Coefficients)
        (coefficientWitness input)).output (coeffOffset offset)).u2.sign
      sign2 := ((ProvableType.witness (F := CF) (α := GLV.Coefficients)
        (coefficientWitness input)).output (coeffOffset offset)).v1.sign
      sign3 := ((ProvableType.witness (F := CF) (α := GLV.Coefficients)
        (coefficientWitness input)).output (coeffOffset offset)).v2.sign }
  have ht := PatBuildTable.eval_tableAt_of_agreesBelow tableInput
    (offset := tableOffset offset) h_agree (by
      simpa only [msmOffset] using hle)
  exact msmInput_of_eval_eq
    (PatBuildTable.tableAt tableInput (tableOffset offset))
    ((ProvableType.witness (F := CF) (α := GLV.Coefficients)
      (coefficientWitness input)).output (coeffOffset offset)) ht hc'

set_option maxRecDepth 1000000 in
private theorem structuralInfinity
    (input : Var ScalarMul.Inputs CF) (offset : ℕ)
    (env env' : ProverEnvironment CF) :
  SCW input env env' (outOffset offset)
      ((infinityCircuit input offset).operations (outOffset offset)) := by
  simp only [SCW, infinityCircuit, Circuit.pure_structuralComputableWitnesses_iff]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 400000 in
private theorem structuralComputableWitnesses
    (offset : ℕ) (input : Var ScalarMul.Inputs (CF))
    (env env' : ProverEnvironment (CF)) :
    FormalCircuitBase.Operations.StructuralComputableWitnesses
      input env env' offset ((main input).operations offset) := by
  unfold main
  change SCW input env env' offset (mainOperations input offset)
  unfold mainOperations opChain
  have hInf := structuralInfinity input offset env env'
  have hMsmInf : SCW input env env' (msmOffset offset)
      (((msmCircuit input offset).operations (msmOffset offset)) ++
        ((infinityCircuit input offset).operations (outOffset offset))) := by
    refine appendSCW (structuralMSM input offset env env') ?_
    simpa [msmCircuit_next input offset] using hInf
  have hTableTail : SCW input env env' (tableOffset offset)
      (((tableCircuit input offset).operations (tableOffset offset)) ++
        (((msmCircuit input offset).operations (msmOffset offset)) ++
          ((infinityCircuit input offset).operations (outOffset offset)))) := by
    refine appendSCW (structuralTable input offset env env') ?_
    simpa [tableCircuit_next input offset] using hMsmInf
  have hRelTail : SCW input env env' (relationOffset offset)
      (((relationCircuit input offset).operations (relationOffset offset)) ++
        (((tableCircuit input offset).operations (tableOffset offset)) ++
          (((msmCircuit input offset).operations (msmOffset offset)) ++
            ((infinityCircuit input offset).operations (outOffset offset))))) := by
    refine appendSCW (structuralRelation input offset env env') ?_
    simpa [relationCircuit_next input offset] using hTableTail
  have hReduceTail : SCW input env env' (shortOffset offset)
      (((reduceCircuit input).operations (shortOffset offset)) ++
        (((relationCircuit input offset).operations (relationOffset offset)) ++
          (((tableCircuit input offset).operations (tableOffset offset)) ++
            (((msmCircuit input offset).operations (msmOffset offset)) ++
              ((infinityCircuit input offset).operations (outOffset offset)))))) := by
    refine appendSCW (structuralReduce input offset env env') ?_
    simpa [reduceCircuit_next input offset] using hRelTail
  have hV2Tail : SCW input env env' (shortOffset offset)
      (((v2Circuit input offset).operations (shortOffset offset)) ++
        (((reduceCircuit input).operations (shortOffset offset)) ++
          (((relationCircuit input offset).operations (relationOffset offset)) ++
            (((tableCircuit input offset).operations (tableOffset offset)) ++
              (((msmCircuit input offset).operations (msmOffset offset)) ++
                ((infinityCircuit input offset).operations (outOffset offset))))))) := by
    refine appendSCW (structuralV2 input offset env env') ?_
    simpa [zeroLength_next (v2Circuit_localLength input offset)] using hReduceTail
  have hV1Tail : SCW input env env' (shortOffset offset)
      (((v1Circuit input offset).operations (shortOffset offset)) ++
        (((v2Circuit input offset).operations (shortOffset offset)) ++
          (((reduceCircuit input).operations (shortOffset offset)) ++
            (((relationCircuit input offset).operations (relationOffset offset)) ++
              (((tableCircuit input offset).operations (tableOffset offset)) ++
                (((msmCircuit input offset).operations (msmOffset offset)) ++
                  ((infinityCircuit input offset).operations (outOffset offset)))))))) := by
    refine appendSCW (structuralV1 input offset env env') ?_
    simpa [zeroLength_next (v1Circuit_localLength input offset)] using hV2Tail
  have hU2Tail : SCW input env env' (shortOffset offset)
      (((u2Circuit input offset).operations (shortOffset offset)) ++
        (((v1Circuit input offset).operations (shortOffset offset)) ++
          (((v2Circuit input offset).operations (shortOffset offset)) ++
            (((reduceCircuit input).operations (shortOffset offset)) ++
              (((relationCircuit input offset).operations (relationOffset offset)) ++
                (((tableCircuit input offset).operations (tableOffset offset)) ++
                  (((msmCircuit input offset).operations (msmOffset offset)) ++
                    ((infinityCircuit input offset).operations (outOffset offset))))))))) := by
    refine appendSCW (structuralU2 input offset env env') ?_
    simpa [zeroLength_next (u2Circuit_localLength input offset)] using hV1Tail
  have hU1Tail : SCW input env env' (shortOffset offset)
      (((u1Circuit input offset).operations (shortOffset offset)) ++
        (((u2Circuit input offset).operations (shortOffset offset)) ++
          (((v1Circuit input offset).operations (shortOffset offset)) ++
            (((v2Circuit input offset).operations (shortOffset offset)) ++
              (((reduceCircuit input).operations (shortOffset offset)) ++
                (((relationCircuit input offset).operations (relationOffset offset)) ++
                  (((tableCircuit input offset).operations (tableOffset offset)) ++
                    (((msmCircuit input offset).operations (msmOffset offset)) ++
                      ((infinityCircuit input offset).operations (outOffset offset)))))))))) := by
    refine appendSCW (structuralU1 input offset env env') ?_
    simpa [zeroLength_next (u1Circuit_localLength input offset)] using hU2Tail
  have hCoeffTail : SCW input env env' (coeffOffset offset)
      (((coeffCircuit input).operations (coeffOffset offset)) ++
        (((u1Circuit input offset).operations (shortOffset offset)) ++
          (((u2Circuit input offset).operations (shortOffset offset)) ++
            (((v1Circuit input offset).operations (shortOffset offset)) ++
              (((v2Circuit input offset).operations (shortOffset offset)) ++
                (((reduceCircuit input).operations (shortOffset offset)) ++
                  (((relationCircuit input offset).operations (relationOffset offset)) ++
                    (((tableCircuit input offset).operations (tableOffset offset)) ++
                      (((msmCircuit input offset).operations (msmOffset offset)) ++
                        ((infinityCircuit input offset).operations (outOffset offset))))))))))) := by
    refine appendSCW (structuralCoefficientWitness input offset env env') ?_
    simpa [coeffCircuit_next input offset] using hU1Tail
  have hPVTail : SCW input env env' (pvOffset offset)
      (((pointValidCircuit input offset).operations (pvOffset offset)) ++
        (((coeffCircuit input).operations (coeffOffset offset)) ++
          (((u1Circuit input offset).operations (shortOffset offset)) ++
            (((u2Circuit input offset).operations (shortOffset offset)) ++
              (((v1Circuit input offset).operations (shortOffset offset)) ++
                (((v2Circuit input offset).operations (shortOffset offset)) ++
                  (((reduceCircuit input).operations (shortOffset offset)) ++
                    (((relationCircuit input offset).operations (relationOffset offset)) ++
                      (((tableCircuit input offset).operations (tableOffset offset)) ++
                        (((msmCircuit input offset).operations (msmOffset offset)) ++
                          ((infinityCircuit input offset).operations (outOffset offset)))))))))))) := by
    refine appendSCW (structuralPointValid input offset env env') ?_
    simpa [pointValidCircuit_next input offset] using hCoeffTail
  refine appendSCW (structuralResultWitness input offset env env') ?_
  simpa [qCircuit_next input offset] using hPVTail

theorem computableWitnesses : circuit.base.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (FormalCircuitBase.computableWitnessCondition
      input env env') ((main input).operations offset)
  exact FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
    input env env' (structuralComputableWitnesses offset input env env')

end GLVScalarMul

end Solution.Secp256k1ScalarMul
