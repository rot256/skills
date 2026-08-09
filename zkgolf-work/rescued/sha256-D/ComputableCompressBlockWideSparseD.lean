import Solution.SHA256.CompressBlockWideSparseD
import Solution.SHA256.ComputableCompressBlockWideSparse
import Solution.SHA256.ComputableRoundsW
import Solution.SHA256.ComputableDefer

/-!
Computable-witness contract for the deferred-chain sparse wide-block compressor.

Layout:

* schedule            `offset       .. offset+4185`
* schedule last E62   `offset+4186  .. offset+4243`
* schedule last E63   `offset+4244  .. offset+4301`
* rounds 0..61 (wide) `offset+4302  .. offset+14471`
* tail pair           `offset+14472 .. offset+14802`
* four carry adds     `offset+14803 .. offset+14930`
-/

namespace Solution.SHA256.CompressBlockWideSparseD

open Solution.SHA256
open Challenge.Utils.ComputableWitnessLemmas
open Challenge.Instances.SHA256.Interface (circomPrime)

abbrev wdWords
    (input : Var Inputs (F circomPrime)) (offset : ℕ) :
    Var SHA256Schedule (F circomPrime) :=
  MessageScheduleSparse.circuit46.output input.block offset

abbrev wdE62Input
    (input : Var Inputs (F circomPrime)) (offset : ℕ) :
    Var ScheduleStep.Inputs (F circomPrime) :=
  let words := wdWords input offset
  ⟨words[60], words[55], words[47], words[46]⟩

abbrev wdE63Input
    (input : Var Inputs (F circomPrime)) (offset : ℕ) :
    Var ScheduleStep.Inputs (F circomPrime) :=
  let words := wdWords input offset
  ⟨words[61], words[56], words[48], words[47]⟩

abbrev wdE62
    (input : Var Inputs (F circomPrime)) (offset : ℕ) :
    Var field (F circomPrime) :=
  ScheduleStepLast.circuit.output (wdE62Input input offset) (offset + 4186)

abbrev wdE63
    (input : Var Inputs (F circomPrime)) (offset : ℕ) :
    Var field (F circomPrime) :=
  ScheduleStepLast.circuit.output (wdE63Input input offset) (offset + 4244)

abbrev wdRoundInput
    (input : Var Inputs (F circomPrime)) (offset : ℕ) :
    Var SHA256Rounds63.Inputs (F circomPrime) :=
  ⟨input.state, wdWords input offset⟩

abbrev wdSt62
    (input : Var Inputs (F circomPrime)) (offset : ℕ) :
    Var SHA256State (F circomPrime) :=
  SHA256Rounds63.circuit62_pairedW.output (wdRoundInput input offset) (offset + 4302)

abbrev wdTailInput
    (input : Var Inputs (F circomPrime)) (offset : ℕ) :
    Var TailPairWide.Inputs (F circomPrime) :=
  ⟨wdSt62 input offset, wdE62 input offset, wdE63 input offset,
    input.state[0], input.state[4]⟩

abbrev wdTailOut
    (input : Var Inputs (F circomPrime)) (offset : ℕ) :
    Var TailPairWide.Outputs (F circomPrime) :=
  TailPairWide.circuit.output (wdTailInput input offset) (offset + 14472)

theorem wd_schedule_eval_eq
    (input : Var Inputs (F circomPrime)) (offset : ℕ)
    {env env' : ProverEnvironment (F circomPrime)}
    (hagree : env.AgreesBelow (offset + 4186) env')
    (hinput : eval env input = eval env' input) :
    eval env (wdWords input offset) = eval env' (wdWords input offset) :=
  CompressBlockWideSparse.ws_schedule_eval_eq input offset hagree hinput

theorem wd_roundsOutput_eval_eq
    (input : Var Inputs (F circomPrime)) (offset : ℕ)
    (env env' : ProverEnvironment (F circomPrime))
    (hagree : env.AgreesBelow (offset + 14472) env')
    (hinput : eval env input = eval env' input) :
    eval env.toEnvironment (wdSt62 input offset) =
      eval env'.toEnvironment (wdSt62 input offset) := by
  have hw := wd_schedule_eval_eq input offset
    (ProverEnvironment.agreesBelow_of_le hagree (by omega)) hinput
  have hri := CompressBlockWide.roundsInput_eval_eq input (wdWords input offset)
    env env' hinput hw
  exact SHA256Rounds63.roundsWOutput_eval_eq_of_agreesBelow
    (wdRoundInput input offset) (offset + 4302) env env'
    (ProverEnvironment.agreesBelow_of_le hagree (by omega)) hri

end Solution.SHA256.CompressBlockWideSparseD


namespace Solution.SHA256.CompressBlockWideSparseD

open Solution.SHA256
open Challenge.Utils.ComputableWitnessLemmas
open Challenge.Instances.SHA256.Interface (circomPrime)

section

attribute [local irreducible] main MessageScheduleSparse.circuit46

set_option maxHeartbeats 2000000 in
theorem schedule_flatStructuralD
    (input : Var Inputs (F circomPrime)) (offset : ℕ)
    (env env' : ProverEnvironment (F circomPrime)) :
    FormalCircuitBase.FlatOperation.StructuralComputableWitnesses
      input env env' offset
      ((((MessageScheduleSparse.circuit46 (p := circomPrime)).toSubcircuit
        offset input.block).ops).toFlat) :=
  CompressBlockWideSparse.schedule_flatStructural input offset env env'

end

section

attribute [local irreducible] main ScheduleStepLast.circuit

set_option maxHeartbeats 2000000 in
theorem e62_flatStructuralD
    (input : Var Inputs (F circomPrime)) (offset : ℕ)
    (env env' : ProverEnvironment (F circomPrime)) :
    FormalCircuitBase.FlatOperation.StructuralComputableWitnesses
      input env env' (offset + 4186)
      ((((ScheduleStepLast.circuit (p := circomPrime)).toSubcircuit
        (offset + 4186) (wdE62Input input offset)).ops).toFlat) := by
  refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
    ScheduleStepLast.circuit input (wdE62Input input offset) (offset + 4186)
    ?_ Computable.scheduleStepLast env env'
  intro k e e' hle hagree hinput
  have hw := wd_schedule_eval_eq input offset
    (ProverEnvironment.agreesBelow_of_le hagree (by omega)) hinput
  exact CompressBlockWide.scheduleStepInput_eval_eq (wdWords input offset)
    ⟨60, by norm_num⟩ ⟨55, by norm_num⟩ ⟨47, by norm_num⟩ ⟨46, by norm_num⟩ e e' hw

set_option maxHeartbeats 2000000 in
theorem e63_flatStructuralD
    (input : Var Inputs (F circomPrime)) (offset : ℕ)
    (env env' : ProverEnvironment (F circomPrime)) :
    FormalCircuitBase.FlatOperation.StructuralComputableWitnesses
      input env env' (offset + 4244)
      ((((ScheduleStepLast.circuit (p := circomPrime)).toSubcircuit
        (offset + 4244) (wdE63Input input offset)).ops).toFlat) := by
  refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
    ScheduleStepLast.circuit input (wdE63Input input offset) (offset + 4244)
    ?_ Computable.scheduleStepLast env env'
  intro k e e' hle hagree hinput
  have hw := wd_schedule_eval_eq input offset
    (ProverEnvironment.agreesBelow_of_le hagree (by omega)) hinput
  exact CompressBlockWide.scheduleStepInput_eval_eq (wdWords input offset)
    ⟨61, by norm_num⟩ ⟨56, by norm_num⟩ ⟨48, by norm_num⟩ ⟨47, by norm_num⟩ e e' hw

end

section

attribute [local irreducible] main SHA256Rounds63.circuit62_pairedW

set_option maxHeartbeats 2000000 in
theorem rounds_flatStructuralD
    (input : Var Inputs (F circomPrime)) (offset : ℕ)
    (env env' : ProverEnvironment (F circomPrime)) :
    FormalCircuitBase.FlatOperation.StructuralComputableWitnesses
      input env env' (offset + 4302)
      ((((SHA256Rounds63.circuit62_pairedW (p := circomPrime)).toSubcircuit
        (offset + 4302) (wdRoundInput input offset)).ops).toFlat) := by
  refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
    SHA256Rounds63.circuit62_pairedW input (wdRoundInput input offset)
    (offset + 4302) ?_
      (SHA256Rounds63.computableWitnesses62_pairedW (p := circomPrime)) env env'
  intro k e e' hle hagree hinput
  have hw := wd_schedule_eval_eq input offset
    (ProverEnvironment.agreesBelow_of_le hagree (by omega)) hinput
  exact CompressBlockWide.roundsInput_eval_eq input (wdWords input offset) e e' hinput hw

end

section

attribute [local irreducible] main TailPairWide.circuit

set_option maxHeartbeats 2000000 in
theorem tail_flatStructuralD
    (input : Var Inputs (F circomPrime)) (offset : ℕ)
    (env env' : ProverEnvironment (F circomPrime)) :
    FormalCircuitBase.FlatOperation.StructuralComputableWitnesses
      input env env' (offset + 14472)
      ((((TailPairWide.circuit (p := circomPrime)).toSubcircuit
        (offset + 14472) (wdTailInput input offset)).ops).toFlat) := by
  refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
    TailPairWide.circuit input (wdTailInput input offset) (offset + 14472)
    ?_ (TailPairWide.computableWitnesses (p := circomPrime)) env env'
  intro k e e' hle hagree hinput
  have hagree' : e.AgreesBelow (offset + 14472) e' :=
    ProverEnvironment.agreesBelow_of_le hagree (by omega)
  have hw := wd_schedule_eval_eq input offset
    (ProverEnvironment.agreesBelow_of_le hagree' (by omega)) hinput
  have hi62 := CompressBlockWide.scheduleStepInput_eval_eq (wdWords input offset)
    ⟨60, by norm_num⟩ ⟨55, by norm_num⟩ ⟨47, by norm_num⟩ ⟨46, by norm_num⟩ e e' hw
  have hi63 := CompressBlockWide.scheduleStepInput_eval_eq (wdWords input offset)
    ⟨61, by norm_num⟩ ⟨56, by norm_num⟩ ⟨48, by norm_num⟩ ⟨47, by norm_num⟩ e e' hw
  have he62 := CompressBlockWide.scheduleStepLast_output_eval_eq
    (wdE62Input input offset) (offset + 4186) e e'
    (ProverEnvironment.agreesBelow_of_le hagree' (by omega)) hi62
  have he63 := CompressBlockWide.scheduleStepLast_output_eval_eq
    (wdE63Input input offset) (offset + 4244) e e'
    (ProverEnvironment.agreesBelow_of_le hagree' (by omega)) hi63
  have hround := wd_roundsOutput_eval_eq input offset e e' hagree' hinput
  have hstate := CompressBlockWide.state_eval_eq input hinput
  have hs0 := CompressBlockWide.word_map_eval_eq_of_vector_eval_eq input.state e e'
    hstate 0 (by norm_num)
  have hs4 := CompressBlockWide.word_map_eval_eq_of_vector_eval_eq input.state e e'
    hstate 4 (by norm_num)
  rw [CircuitType.eval_var_field_prover e] at he62 he63
  rw [CircuitType.eval_var_field_prover e'] at he62 he63
  simp only [circuit_norm]
  rw [hround, he62, he63, hs0, hs4]

end

end Solution.SHA256.CompressBlockWideSparseD


namespace Solution.SHA256.CompressBlockWideSparseD

open Solution.SHA256
open Challenge.Utils.ComputableWitnessLemmas
open Challenge.Instances.SHA256.Interface (circomPrime)

section

attribute [local irreducible] main

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem computableWitnesses :
    (circuit (p := circomPrime)).ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations offset)
  apply FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main
  rw [Circuit.bind_structuralComputableWitnesses_iff]
  constructor
  · rw [FormalCircuit.subcircuit_structuralComputableWitnesses_iff]
    exact schedule_flatStructuralD input offset env env'
  · rw [Circuit.bind_structuralComputableWitnesses_iff]
    constructor
    · rw [FormalCircuit.subcircuit_structuralComputableWitnesses_iff]
      exact e62_flatStructuralD input offset env env'
    · rw [Circuit.bind_structuralComputableWitnesses_iff]
      constructor
      · rw [FormalCircuit.subcircuit_structuralComputableWitnesses_iff]
        exact e63_flatStructuralD input offset env env'
      · rw [Circuit.bind_structuralComputableWitnesses_iff]
        constructor
        · rw [FormalCircuit.subcircuit_structuralComputableWitnesses_iff]
          exact rounds_flatStructuralD input offset env env'
        · rw [Circuit.bind_structuralComputableWitnesses_iff]
          constructor
          · rw [FormalCircuit.subcircuit_structuralComputableWitnesses_iff]
            exact tail_flatStructuralD input offset env env'
          · rw [Circuit.bind_structuralComputableWitnesses_iff]
            constructor
            · rw [FormalCircuit.subcircuit_structuralComputableWitnesses_iff]
              exact FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
                CarrySumAdd32.circuit input
                (⟨input.state[1], (wdTailOut input offset).a63⟩ :
                  Var CarrySumAdd32.Inputs (F circomPrime))
                (offset + 14803)
                (by
                  intro k e e' hle hagree hinput
                  have ha := CompressBlockWide.word_map_eval_eq_of_vector_eval_eq input.state e e'
                    (CompressBlockWide.state_eval_eq input hinput) 1 (by norm_num)
                  have hb := CompressBlockWide.tail_a63_eval_eq_of_agreesBelow
                    (wdTailInput input offset) (offset + 14472) e e'
                    (ProverEnvironment.agreesBelow_of_le hagree (by omega))
                  exact CompressBlockWide.carryInput_eval_eq _ _ e e' ha hb)
                CompressBlockWide.carryComputable env env'
            · rw [Circuit.bind_structuralComputableWitnesses_iff]
              constructor
              · rw [FormalCircuit.subcircuit_structuralComputableWitnesses_iff]
                exact FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
                  CarrySumAdd32.circuit input
                  (⟨input.state[2], (wdSt62 input offset)[0]⟩ :
                    Var CarrySumAdd32.Inputs (F circomPrime))
                  (offset + 14835)
                  (by
                    intro k e e' hle hagree hinput
                    have hround := wd_roundsOutput_eval_eq input offset e e'
                      (ProverEnvironment.agreesBelow_of_le hagree (by omega)) hinput
                    have ha := CompressBlockWide.word_map_eval_eq_of_vector_eval_eq input.state
                      e e' (CompressBlockWide.state_eval_eq input hinput) 2 (by norm_num)
                    have hb := CompressBlockWide.word_map_eval_eq_of_verifier_eval_eq
                      (wdSt62 input offset) e e' hround 0 (by norm_num)
                    exact CompressBlockWide.carryInput_eval_eq _ _ e e' ha hb)
                  CompressBlockWide.carryComputable env env'
              · rw [Circuit.bind_structuralComputableWitnesses_iff]
                constructor
                · rw [FormalCircuit.subcircuit_structuralComputableWitnesses_iff]
                  exact FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
                    DeferAdd.circuit input
                    (⟨input.state[3], (wdSt62 input offset)[1]⟩ :
                      Var DeferAdd.Inputs (F circomPrime))
                    (offset + 14867)
                    (by
                      intro k e e' hle hagree hinput
                      have hround := wd_roundsOutput_eval_eq input offset e e'
                        (ProverEnvironment.agreesBelow_of_le hagree (by omega)) hinput
                      have ha := CompressBlockWide.word_map_eval_eq_of_vector_eval_eq input.state
                        e e' (CompressBlockWide.state_eval_eq input hinput) 3 (by norm_num)
                      have hb := CompressBlockWide.word_map_eval_eq_of_verifier_eval_eq
                        (wdSt62 input offset) e e' hround 1 (by norm_num)
                      simp only [circuit_norm]
                      rw [ha, hb])
                    DeferAdd.computableWitnesses env env'
                · rw [Circuit.bind_structuralComputableWitnesses_iff]
                  constructor
                  · rw [FormalCircuit.subcircuit_structuralComputableWitnesses_iff]
                    exact FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
                      CarrySumAdd32.circuit input
                      (⟨input.state[5], (wdTailOut input offset).e63⟩ :
                        Var CarrySumAdd32.Inputs (F circomPrime))
                      (offset + 14867)
                      (by
                        intro k e e' hle hagree hinput
                        have ha := CompressBlockWide.word_map_eval_eq_of_vector_eval_eq input.state
                          e e' (CompressBlockWide.state_eval_eq input hinput) 5 (by norm_num)
                        have hb := CompressBlockWide.tail_e63_eval_eq_of_agreesBelow
                          (wdTailInput input offset) (offset + 14472) e e'
                          (ProverEnvironment.agreesBelow_of_le hagree (by omega))
                        exact CompressBlockWide.carryInput_eval_eq _ _ e e' ha hb)
                      CompressBlockWide.carryComputable env env'
                  · rw [Circuit.bind_structuralComputableWitnesses_iff]
                    constructor
                    · rw [FormalCircuit.subcircuit_structuralComputableWitnesses_iff]
                      exact FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
                        CarrySumAdd32.circuit input
                        (⟨input.state[6], (wdSt62 input offset)[4]⟩ :
                          Var CarrySumAdd32.Inputs (F circomPrime))
                        (offset + 14899)
                        (by
                          intro k e e' hle hagree hinput
                          have hround := wd_roundsOutput_eval_eq input offset e e'
                            (ProverEnvironment.agreesBelow_of_le hagree (by omega)) hinput
                          have ha := CompressBlockWide.word_map_eval_eq_of_vector_eval_eq
                            input.state e e'
                            (CompressBlockWide.state_eval_eq input hinput) 6 (by norm_num)
                          have hb := CompressBlockWide.word_map_eval_eq_of_verifier_eval_eq
                            (wdSt62 input offset) e e' hround 4 (by norm_num)
                          exact CompressBlockWide.carryInput_eval_eq _ _ e e' ha hb)
                        CompressBlockWide.carryComputable env env'
                    · rw [Circuit.bind_structuralComputableWitnesses_iff]
                      constructor
                      · rw [FormalCircuit.subcircuit_structuralComputableWitnesses_iff]
                        exact FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
                          DeferAdd.circuit input
                          (⟨input.state[7], (wdSt62 input offset)[5]⟩ :
                            Var DeferAdd.Inputs (F circomPrime))
                          (offset + 14931)
                          (by
                            intro k e e' hle hagree hinput
                            have hround := wd_roundsOutput_eval_eq input offset e e'
                              (ProverEnvironment.agreesBelow_of_le hagree (by omega)) hinput
                            have ha := CompressBlockWide.word_map_eval_eq_of_vector_eval_eq
                              input.state e e'
                              (CompressBlockWide.state_eval_eq input hinput) 7 (by norm_num)
                            have hb := CompressBlockWide.word_map_eval_eq_of_verifier_eval_eq
                              (wdSt62 input offset) e e' hround 5 (by norm_num)
                            simp only [circuit_norm]
                            rw [ha, hb])
                          DeferAdd.computableWitnesses env env'
                      · rw [Circuit.pure_structuralComputableWitnesses_iff]
                        trivial

end

theorem fromBits_eval_eq_of_map_eq
    (env env' : Environment (F circomPrime)) (v : Var (fields 32) (F circomPrime))
    (h : Vector.map (Expression.eval env) v = Vector.map (Expression.eval env') v) :
    Expression.eval env (fromBitsExpr v) = Expression.eval env' (fromBitsExpr v) := by
  rw [RPShared.fromBitsExpr_eval_sum, RPShared.fromBitsExpr_eval_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  have hi := Vector.ext_iff.mp h i.val i.isLt
  simp only [Vector.getElem_map, Fin.getElem_fin] at hi
  rw [hi]

theorem sparse32_map_eval_eq
    (env env' : Environment (F circomPrime)) (e : Expression (F circomPrime))
    (h : Expression.eval env e = Expression.eval env' e) :
    Vector.map (Expression.eval env) (RPShared.sparse32 e) =
      Vector.map (Expression.eval env') (RPShared.sparse32 e) := by
  have hz : ∀ (e : Environment (F circomPrime)),
      Expression.eval e (0 : Expression (F circomPrime)) = 0 := fun _ => rfl
  simp only [RPShared.sparse32]
  simp [h, hz]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem output_eval_eq_of_agreesBelow
    (input : Var Inputs (F circomPrime)) (offset : Nat)
    (env env' : ProverEnvironment (F circomPrime))
    (hagree : env.AgreesBelow (offset + 14931) env')
    (hinput : eval env input = eval env' input) :
    eval env (circuit.output input offset) =
      eval env' (circuit.output input offset) := by
  have hround := wd_roundsOutput_eval_eq input offset env env'
    (ProverEnvironment.agreesBelow_of_le hagree (by omega)) hinput
  have hstate := CompressBlockWide.state_eval_eq input hinput
  have hs3 := CompressBlockWide.word_map_eval_eq_of_vector_eval_eq input.state env env'
    hstate 3 (by norm_num)
  have hs7 := CompressBlockWide.word_map_eval_eq_of_vector_eval_eq input.state env env'
    hstate 7 (by norm_num)
  have hb1 := CompressBlockWide.word_map_eval_eq_of_verifier_eval_eq (wdSt62 input offset)
    env env' hround 1 (by norm_num)
  have hb5 := CompressBlockWide.word_map_eval_eq_of_verifier_eval_eq (wdSt62 input offset)
    env env' hround 5 (by norm_num)
  have h3 : Expression.eval env.toEnvironment
        (fromBitsExpr input.state[3] + fromBitsExpr ((wdSt62 input offset)[1])) =
      Expression.eval env'.toEnvironment
        (fromBitsExpr input.state[3] + fromBitsExpr ((wdSt62 input offset)[1])) := by
    show _ + _ = _ + _
    rw [fromBits_eval_eq_of_map_eq _ _ _ hs3, fromBits_eval_eq_of_map_eq _ _ _ hb1]
  have h7 : Expression.eval env.toEnvironment
        (fromBitsExpr input.state[7] + fromBitsExpr ((wdSt62 input offset)[5])) =
      Expression.eval env'.toEnvironment
        (fromBitsExpr input.state[7] + fromBitsExpr ((wdSt62 input offset)[5])) := by
    show _ + _ = _ + _
    rw [fromBits_eval_eq_of_map_eq _ _ _ hs7, fromBits_eval_eq_of_map_eq _ _ _ hb5]
  rw [CircuitType.eval_var_prover_to_verifier env (circuit.output input offset),
    CircuitType.eval_var_prover_to_verifier env' (circuit.output input offset)]
  apply Vector.ext
  intro j hj
  rw [← getElem_eval_vector env.toEnvironment (circuit.output input offset) j hj,
    ← getElem_eval_vector env'.toEnvironment (circuit.output input offset) j hj]
  simp only [circuit_norm, circuit, elaborated, ScheduleStepUnchecked.circuit]
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
      j = 5 ∨ j = 6 ∨ j = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  ·
    simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ]
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_map, Vector.getElem_mapRange, Expression.eval]
    exact hagree _ (by omega)
  ·
    simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ]
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_map, Vector.getElem_mapRange, Expression.eval]
    exact hagree _ (by omega)
  ·
    simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ]
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_map, Vector.getElem_mapRange, Expression.eval]
    exact hagree _ (by omega)
  ·
    simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ]
    exact sparse32_map_eval_eq _ _ _ h3
  ·
    simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ]
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_map, Vector.getElem_mapRange, Expression.eval]
    exact hagree _ (by omega)
  ·
    simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ]
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_map, Vector.getElem_mapRange, Expression.eval]
    exact hagree _ (by omega)
  ·
    simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ]
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_map, Vector.getElem_mapRange, Expression.eval]
    exact hagree _ (by omega)
  ·
    simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ]
    exact sparse32_map_eval_eq _ _ _ h7

end Solution.SHA256.CompressBlockWideSparseD
