import Solution.SHA256.CompressBlock5D
import Solution.SHA256.ComputableRoundsW
import Solution.SHA256.ComputableDefer
import Solution.SHA256.ComputableCompressBlockWideSparseD
import Solution.SHA256.ComputableCarry
import Solution.SHA256.ComputableRoundLoops
import Solution.SHA256.ComputableTailPairs
import Challenge.Utils.ComputableWitnessLemmas


namespace Solution.SHA256.CompressBlock5D

open Challenge.Utils.ComputableWitnessLemmas
open Challenge.Instances.SHA256.Interface (circomPrime inputBufferLen)
open Utils.Bits (fieldFromBitsExpr fieldFromBits_eval)

private theorem input_state_eval_eq
    (input : Var Inputs (F circomPrime))
    {env env' : ProverEnvironment (F circomPrime)}
    (hinput : eval env input = eval env' input) :
    eval env.toEnvironment input.state =
      eval env'.toEnvironment input.state := by
  have h := hinput
  rw [CircuitType.eval_expression_prover_to_verifier env input,
    CircuitType.eval_expression_prover_to_verifier env' input] at h
  simpa [circuit_norm] using
    congrArg (fun x : Inputs (F circomPrime) => x.state) h

private theorem input_lenFlags_eval_eq
    (input : Var Inputs (F circomPrime))
    {env env' : ProverEnvironment (F circomPrime)}
    (hinput : eval env input = eval env' input) :
    Vector.map (Expression.eval env.toEnvironment) input.lenFlags =
      Vector.map (Expression.eval env'.toEnvironment) input.lenFlags := by
  have h := hinput
  rw [CircuitType.eval_expression_prover_to_verifier env input,
    CircuitType.eval_expression_prover_to_verifier env' input] at h
  simpa [circuit_norm, CircuitType.eval_var_fields] using
    congrArg (fun x : Inputs (F circomPrime) => x.lenFlags) h

private theorem input_state_word_mem_eval_eq
    (input : Var Inputs (F circomPrime))
    {env env' : ProverEnvironment (F circomPrime)}
    (hinput : eval env input = eval env' input) (j : Fin 8) :
    ∀ a ∈ input.state[j.val]'j.isLt, Expression.eval env.toEnvironment a =
      Expression.eval env'.toEnvironment a := by
  intro a ha
  have hstate := input_state_eval_eq input hinput
  rw [Vector.mem_iff_getElem] at ha
  rcases ha with ⟨i, hi, rfl⟩
  rw [ProvableType.getElem_eval_fields env.toEnvironment
      (input.state[j.val]'j.isLt) i hi,
    ProvableType.getElem_eval_fields env'.toEnvironment
      (input.state[j.val]'j.isLt) i hi,
    getElem_eval_vector env.toEnvironment input.state j.val j.isLt,
    getElem_eval_vector env'.toEnvironment input.state j.val j.isLt]
  exact congrArg
    (fun s : SHA256State (F circomPrime) => (s[j.val]'j.isLt)[i]'hi) hstate

private theorem input_state_word_eval_eq
    (input : Var Inputs (F circomPrime))
    {env env' : ProverEnvironment (F circomPrime)}
    (hinput : eval env input = eval env' input) (j : Fin 8) :
    eval env.toEnvironment (input.state[j.val]'j.isLt) =
      eval env'.toEnvironment (input.state[j.val]'j.isLt) := by
  rw [getElem_eval_vector env.toEnvironment input.state j.val j.isLt,
    getElem_eval_vector env'.toEnvironment input.state j.val j.isLt]
  exact congrArg
    (fun s : SHA256State (F circomPrime) => s[j.val]'j.isLt)
    (input_state_eval_eq input hinput)

private theorem input_state_nat_word_map_eval_eq
    (input : Var Inputs (F circomPrime))
    {env env' : ProverEnvironment (F circomPrime)}
    (hinput : eval env input = eval env' input) (j : ℕ) (hj : j < 8) :
    Vector.map (Expression.eval env.toEnvironment) (input.state[j]'hj) =
      Vector.map (Expression.eval env'.toEnvironment) (input.state[j]'hj) := by
  rw [← CircuitType.eval_var_fields env.toEnvironment,
    ← CircuitType.eval_var_fields env'.toEnvironment,
    getElem_eval_vector env.toEnvironment input.state j hj,
    getElem_eval_vector env'.toEnvironment input.state j hj]
  exact congrArg (fun s : SHA256State (F circomPrime) => s[j]'hj)
    (input_state_eval_eq input hinput)

private theorem input_state_nat_word_eval_eq
    (input : Var Inputs (F circomPrime))
    {env env' : ProverEnvironment (F circomPrime)}
    (hinput : eval env input = eval env' input) (j : ℕ) (hj : j < 8) :
    eval env.toEnvironment (input.state[j]'hj) =
      eval env'.toEnvironment (input.state[j]'hj) := by
  rw [getElem_eval_vector env.toEnvironment input.state j hj,
    getElem_eval_vector env'.toEnvironment input.state j hj]
  exact congrArg (fun s : SHA256State (F circomPrime) => s[j]'hj)
    (input_state_eval_eq input hinput)

private theorem block5ScheduleWord_map_eval_eq
    (env env' : Environment (F circomPrime))
    (flags : Var (fields inputBufferLen) (F circomPrime))
    (hflags : Vector.map (Expression.eval env) flags =
      Vector.map (Expression.eval env') flags) (k : Fin 64) :
    Vector.map (Expression.eval env) (block5ScheduleWord flags k) =
      Vector.map (Expression.eval env') (block5ScheduleWord flags k) := by
  apply Vector.ext
  intro v hv
  rw [Vector.getElem_map, Vector.getElem_map, block5ScheduleWord,
    Vector.getElem_ofFn, eval_finFoldl_add, eval_finFoldl_add]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Expression.eval]
  have hi := Vector.ext_iff.mp hflags (248 + i.val) (by
    have := i.isLt
    simp only [inputBufferLen]
    omega)
  have hi' : Expression.eval env
        (flags[248 + i.val]'(by
          have := i.isLt
          simp only [inputBufferLen]
          omega)) =
      Expression.eval env'
        (flags[248 + i.val]'(by
          have := i.isLt
          simp only [inputBufferLen]
          omega)) := by
    simpa only [Vector.getElem_map] using hi
  rw [hi']

private theorem block5Schedule_eval_eq
    (env env' : Environment (F circomPrime))
    (flags : Var (fields inputBufferLen) (F circomPrime))
    (hflags : Vector.map (Expression.eval env) flags =
      Vector.map (Expression.eval env') flags) :
    eval env (block5Schedule flags) = eval env' (block5Schedule flags) := by
  apply Vector.ext
  intro k hk
  rw [← getElem_eval_vector env (block5Schedule flags) k hk,
    ← getElem_eval_vector env' (block5Schedule flags) k hk,
    CircuitType.eval_var_fields, CircuitType.eval_var_fields]
  simpa only [block5Schedule, Vector.getElem_ofFn] using
    block5ScheduleWord_map_eval_eq env env'
      flags hflags ⟨k, hk⟩

private theorem block5ScheduleWordWide_eval_eq
    (env env' : ProverEnvironment (F circomPrime))
    (flags : Var (fields inputBufferLen) (F circomPrime))
    (hflags : Vector.map (Expression.eval env.toEnvironment) flags =
      Vector.map (Expression.eval env'.toEnvironment) flags) (k : Fin 64) :
    Expression.eval env.toEnvironment
        (fieldFromBitsExpr (block5ScheduleWord flags k)) =
      Expression.eval env'.toEnvironment
        (fieldFromBitsExpr (block5ScheduleWord flags k)) := by
  have hword :
      Vector.map (Expression.eval env.toEnvironment)
          (block5ScheduleWord flags k) =
        Vector.map (Expression.eval env'.toEnvironment)
          (block5ScheduleWord flags k) :=
    block5ScheduleWord_map_eval_eq env.toEnvironment env'.toEnvironment
      flags hflags k
  show Expression.eval env.toEnvironment
      (fromBitsExpr (block5ScheduleWord flags k)) =
    Expression.eval env'.toEnvironment
      (fromBitsExpr (block5ScheduleWord flags k))
  rw [RPShared.fromBitsExpr_eval_sum, RPShared.fromBitsExpr_eval_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hi := Vector.ext_iff.mp hword i.val i.isLt
  simp only [Vector.getElem_map, Fin.getElem_fin] at hi
  rw [hi]

private theorem roundsInput_eval_eq
    (input : Var Inputs (F circomPrime))
    (env env' : ProverEnvironment (F circomPrime))
    (hinput : eval env input = eval env' input) :
    eval env
        (⟨input.state, block5Schedule input.lenFlags⟩ :
          Var SHA256Rounds63.Inputs (F circomPrime)) =
      eval env'
        (⟨input.state, block5Schedule input.lenFlags⟩ :
          Var SHA256Rounds63.Inputs (F circomPrime)) := by
  simp only [circuit_norm]
  have hs := input_state_eval_eq input hinput
  have hw := block5Schedule_eval_eq env.toEnvironment env'.toEnvironment
    input.lenFlags (input_lenFlags_eval_eq input hinput)
  rw [hs, hw]

private theorem roundsOutput_eval_eq_of_agreesBelow
    (input : Var Inputs (F circomPrime)) (offset : ℕ)
    (env env' : ProverEnvironment (F circomPrime))
    (hagree : env.AgreesBelow (offset + 10170) env')
    (hinput : eval env input = eval env' input) :
    eval env.toEnvironment
        (SHA256Rounds63.circuit62_pairedW.output
          ⟨input.state, block5Schedule input.lenFlags⟩ offset) =
      eval env'.toEnvironment
        (SHA256Rounds63.circuit62_pairedW.output
          ⟨input.state, block5Schedule input.lenFlags⟩ offset) := by
  exact SHA256Rounds63.roundsWOutput_eval_eq_of_agreesBelow
    (⟨input.state, block5Schedule input.lenFlags⟩ :
      Var SHA256Rounds63.Inputs (F circomPrime)) offset env env' hagree
    (roundsInput_eval_eq input env env' hinput)

private theorem roundsOutput_word_mem_eval_eq
    (input : Var Inputs (F circomPrime)) (offset : ℕ)
    (env env' : ProverEnvironment (F circomPrime))
    (hagree : env.AgreesBelow (offset + 10170) env')
    (hinput : eval env input = eval env' input) (j : Fin 8) :
    ∀ a ∈ (SHA256Rounds63.circuit62_pairedW.output
        ⟨input.state, block5Schedule input.lenFlags⟩ offset)[j.val]'j.isLt,
      Expression.eval env.toEnvironment a =
        Expression.eval env'.toEnvironment a := by
  intro a ha
  have hstate := roundsOutput_eval_eq_of_agreesBelow input offset env env'
    hagree hinput
  rw [Vector.mem_iff_getElem] at ha
  rcases ha with ⟨i, hi, rfl⟩
  rw [ProvableType.getElem_eval_fields env.toEnvironment
      ((SHA256Rounds63.circuit62_pairedW.output
        ⟨input.state, block5Schedule input.lenFlags⟩ offset)[j.val]'j.isLt) i hi,
    ProvableType.getElem_eval_fields env'.toEnvironment
      ((SHA256Rounds63.circuit62_pairedW.output
        ⟨input.state, block5Schedule input.lenFlags⟩ offset)[j.val]'j.isLt) i hi,
    getElem_eval_vector env.toEnvironment
      (SHA256Rounds63.circuit62_pairedW.output
        ⟨input.state, block5Schedule input.lenFlags⟩ offset) j.val j.isLt,
    getElem_eval_vector env'.toEnvironment
      (SHA256Rounds63.circuit62_pairedW.output
        ⟨input.state, block5Schedule input.lenFlags⟩ offset) j.val j.isLt]
  exact congrArg
    (fun s : SHA256State (F circomPrime) => (s[j.val]'j.isLt)[i]'hi) hstate

private theorem roundsOutput_word_eval_eq
    (input : Var Inputs (F circomPrime)) (offset : ℕ)
    (env env' : ProverEnvironment (F circomPrime))
    (hagree : env.AgreesBelow (offset + 10170) env')
    (hinput : eval env input = eval env' input) (j : Fin 8) :
    eval env.toEnvironment
        ((SHA256Rounds63.circuit62_pairedW.output
          ⟨input.state, block5Schedule input.lenFlags⟩ offset)[j.val]'j.isLt) =
      eval env'.toEnvironment
        ((SHA256Rounds63.circuit62_pairedW.output
          ⟨input.state, block5Schedule input.lenFlags⟩ offset)[j.val]'j.isLt) := by
  rw [getElem_eval_vector env.toEnvironment
      (SHA256Rounds63.circuit62_pairedW.output
        ⟨input.state, block5Schedule input.lenFlags⟩ offset) j.val j.isLt,
    getElem_eval_vector env'.toEnvironment
      (SHA256Rounds63.circuit62_pairedW.output
        ⟨input.state, block5Schedule input.lenFlags⟩ offset) j.val j.isLt]
  exact congrArg
    (fun s : SHA256State (F circomPrime) => s[j.val]'j.isLt)
    (roundsOutput_eval_eq_of_agreesBelow input offset env env' hagree hinput)

private theorem roundsOutput_nat_word_eval_eq
    (input : Var Inputs (F circomPrime)) (offset : ℕ)
    (env env' : ProverEnvironment (F circomPrime))
    (hagree : env.AgreesBelow (offset + 10170) env')
    (hinput : eval env input = eval env' input) (j : ℕ) (hj : j < 8) :
    eval env.toEnvironment
        ((SHA256Rounds63.circuit62_pairedW.output
          ⟨input.state, block5Schedule input.lenFlags⟩ offset)[j]'hj) =
      eval env'.toEnvironment
        ((SHA256Rounds63.circuit62_pairedW.output
          ⟨input.state, block5Schedule input.lenFlags⟩ offset)[j]'hj) := by
  rw [getElem_eval_vector env.toEnvironment
      (SHA256Rounds63.circuit62_pairedW.output
        ⟨input.state, block5Schedule input.lenFlags⟩ offset) j hj,
    getElem_eval_vector env'.toEnvironment
      (SHA256Rounds63.circuit62_pairedW.output
        ⟨input.state, block5Schedule input.lenFlags⟩ offset) j hj]
  exact congrArg (fun s : SHA256State (F circomPrime) => s[j]'hj)
    (roundsOutput_eval_eq_of_agreesBelow input offset env env' hagree hinput)

private theorem tail_a63_mem_eval_eq
    (tailInput : Var TailPairTight.Inputs (F circomPrime)) (offset : ℕ)
    (env env' : ProverEnvironment (F circomPrime))
    (hagree : env.AgreesBelow (offset + 329) env') :
    ∀ a ∈ (TailPairTight.circuit.output tailInput offset).a63,
      Expression.eval env.toEnvironment a =
        Expression.eval env'.toEnvironment a := by
  intro a ha
  have ha' : a ∈ (varFromOffset (fields 32) (offset + 96) :
      Var (fields 32) (F circomPrime)) := by
    simpa only [circuit_norm, TailPairTight.circuit,
      TailPairTight.elaborated,
      show offset + 32 + 32 + 32 = offset + 96 by omega] using ha
  exact eval_mem_varFromOffset_fields_of_agreesBelow hagree (by omega) a ha'

private theorem tail_e63_mem_eval_eq
    (tailInput : Var TailPairTight.Inputs (F circomPrime)) (offset : ℕ)
    (env env' : ProverEnvironment (F circomPrime))
    (hagree : env.AgreesBelow (offset + 329) env') :
    ∀ a ∈ (TailPairTight.circuit.output tailInput offset).e63,
      Expression.eval env.toEnvironment a =
        Expression.eval env'.toEnvironment a := by
  intro a ha
  have ha' : a ∈ (varFromOffset (fields 32) (offset + 64) :
      Var (fields 32) (F circomPrime)) := by
    simpa only [circuit_norm, TailPairTight.circuit,
      TailPairTight.elaborated,
      show offset + 32 + 32 = offset + 64 by omega] using ha
  exact eval_mem_varFromOffset_fields_of_agreesBelow hagree (by omega) a ha'

private theorem tail_a63_eval_eq
    (tailInput : Var TailPairTight.Inputs (F circomPrime)) (offset : ℕ)
    (env env' : ProverEnvironment (F circomPrime))
    (hagree : env.AgreesBelow (offset + 329) env') :
    eval env.toEnvironment
        (TailPairTight.circuit.output tailInput offset).a63 =
      eval env'.toEnvironment
        (TailPairTight.circuit.output tailInput offset).a63 := by
  apply Vector.ext
  intro i hi
  rw [← ProvableType.getElem_eval_fields env.toEnvironment
      (TailPairTight.circuit.output tailInput offset).a63 i hi,
    ← ProvableType.getElem_eval_fields env'.toEnvironment
      (TailPairTight.circuit.output tailInput offset).a63 i hi]
  exact tail_a63_mem_eval_eq tailInput offset env env' hagree _
    (Vector.getElem_mem hi)

private theorem tail_e63_eval_eq
    (tailInput : Var TailPairTight.Inputs (F circomPrime)) (offset : ℕ)
    (env env' : ProverEnvironment (F circomPrime))
    (hagree : env.AgreesBelow (offset + 329) env') :
    eval env.toEnvironment
        (TailPairTight.circuit.output tailInput offset).e63 =
      eval env'.toEnvironment
        (TailPairTight.circuit.output tailInput offset).e63 := by
  apply Vector.ext
  intro i hi
  rw [← ProvableType.getElem_eval_fields env.toEnvironment
      (TailPairTight.circuit.output tailInput offset).e63 i hi,
    ← ProvableType.getElem_eval_fields env'.toEnvironment
      (TailPairTight.circuit.output tailInput offset).e63 i hi]
  exact tail_e63_mem_eval_eq tailInput offset env env' hagree _
    (Vector.getElem_mem hi)

private theorem tailInput_eval_eq
    (input : Var Inputs (F circomPrime)) (offset : ℕ)
    (env env' : ProverEnvironment (F circomPrime))
    (hagree : env.AgreesBelow (offset + 10170) env')
    (hinput : eval env input = eval env' input) :
    let sched := block5Schedule input.lenFlags
    let st62 := SHA256Rounds63.circuit62_pairedW.output
      ⟨input.state, sched⟩ offset
    eval env
        (⟨st62, fieldFromBitsExpr sched[62], fieldFromBitsExpr sched[63],
          input.state[0], input.state[4]⟩ :
          Var TailPairTight.Inputs (F circomPrime)) =
      eval env'
        (⟨st62, fieldFromBitsExpr sched[62], fieldFromBitsExpr sched[63],
          input.state[0], input.state[4]⟩ :
          Var TailPairTight.Inputs (F circomPrime)) := by
  dsimp only
  simp only [circuit_norm]
  have hst := roundsOutput_eval_eq_of_agreesBelow input offset env env'
    hagree hinput
  have hw0 := block5ScheduleWordWide_eval_eq env env' input.lenFlags
    (input_lenFlags_eval_eq input hinput) ⟨62, by norm_num⟩
  have hw1 := block5ScheduleWordWide_eval_eq env env' input.lenFlags
    (input_lenFlags_eval_eq input hinput) ⟨63, by norm_num⟩
  have hs0 := input_state_nat_word_map_eval_eq input hinput 0 (by norm_num)
  have hs4 := input_state_nat_word_map_eval_eq input hinput 4 (by norm_num)
  have h62 : (block5Schedule input.lenFlags)[62]'(by norm_num) =
      block5ScheduleWord input.lenFlags ⟨62, by norm_num⟩ := by
    rw [block5Schedule, Vector.getElem_ofFn]
  have h63 : (block5Schedule input.lenFlags)[63]'(by norm_num) =
      block5ScheduleWord input.lenFlags ⟨63, by norm_num⟩ := by
    rw [block5Schedule, Vector.getElem_ofFn]
  rw [h62, h63, hst, hw0, hw1, hs0, hs4]

private theorem carryInput_eval_eq
    (a b : Var (fields 32) (F circomPrime))
    (env env' : ProverEnvironment (F circomPrime))
    (ha : eval env.toEnvironment a = eval env'.toEnvironment a)
    (hb : eval env.toEnvironment b = eval env'.toEnvironment b) :
    eval env (⟨a, b⟩ : Var CarrySumAdd32.Inputs (F circomPrime)) =
      eval env' (⟨a, b⟩ : Var CarrySumAdd32.Inputs (F circomPrime)) := by
  simp only [circuit_norm]
  rw [CircuitType.eval_var_fields, CircuitType.eval_var_fields] at ha hb
  rw [ha, hb]

private theorem deferInput_eval_eq
    (a b : Var (fields 32) (F circomPrime))
    (env env' : ProverEnvironment (F circomPrime))
    (ha : eval env.toEnvironment a = eval env'.toEnvironment a)
    (hb : eval env.toEnvironment b = eval env'.toEnvironment b) :
    eval env (⟨a, b⟩ : Var DeferAdd.Inputs (F circomPrime)) =
      eval env' (⟨a, b⟩ : Var DeferAdd.Inputs (F circomPrime)) := by
  simp only [circuit_norm]
  rw [CircuitType.eval_var_fields, CircuitType.eval_var_fields] at ha hb
  rw [ha, hb]

private theorem roundsOutput_nat_word_map_eval_eq
    (input : Var Inputs (F circomPrime)) (offset : ℕ)
    (env env' : ProverEnvironment (F circomPrime))
    (hagree : env.AgreesBelow (offset + 10170) env')
    (hinput : eval env input = eval env' input) (j : ℕ) (hj : j < 8) :
    Vector.map (Expression.eval env.toEnvironment)
        ((SHA256Rounds63.circuit62_pairedW.output
          ⟨input.state, block5Schedule input.lenFlags⟩ offset)[j]'hj) =
      Vector.map (Expression.eval env'.toEnvironment)
        ((SHA256Rounds63.circuit62_pairedW.output
          ⟨input.state, block5Schedule input.lenFlags⟩ offset)[j]'hj) := by
  rw [← CircuitType.eval_var_fields env.toEnvironment,
    ← CircuitType.eval_var_fields env'.toEnvironment]
  exact roundsOutput_nat_word_eval_eq input offset env env' hagree hinput j hj

private abbrev roundsInputVar (input : Var Inputs (F circomPrime)) :
    Var SHA256Rounds63.Inputs (F circomPrime) :=
  ⟨input.state, block5Schedule input.lenFlags⟩

private abbrev st62Var (input : Var Inputs (F circomPrime)) (offset : ℕ) :
    Var SHA256State (F circomPrime) :=
  SHA256Rounds63.circuit62_pairedW.output (roundsInputVar input) offset

private abbrev tightInputVar
    (input : Var Inputs (F circomPrime)) (offset : ℕ) :
    Var TailPairTight.Inputs (F circomPrime) :=
  let sched := block5Schedule input.lenFlags
  ⟨st62Var input offset, fieldFromBitsExpr sched[62],
    fieldFromBitsExpr sched[63], input.state[0], input.state[4]⟩

private abbrev tightOutputVar
    (input : Var Inputs (F circomPrime)) (offset : ℕ) :
    Var TailPairTight.Outputs (F circomPrime) :=
  TailPairTight.circuit.output (tightInputVar input offset) (offset + 10170)


attribute [local irreducible] SHA256Rounds63.circuit62_pairedW

private theorem rounds_flatStructural
    (input : Var Inputs (F circomPrime)) (offset : ℕ)
    (env env' : ProverEnvironment (F circomPrime)) :
    FormalCircuitBase.FlatOperation.StructuralComputableWitnesses
      input env env' offset
      (((SHA256Rounds63.circuit62_pairedW
        (p := circomPrime)).toSubcircuit
        offset (roundsInputVar input)).ops.toFlat) := by
  refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses
    (SHA256Rounds63.circuit62_pairedW (p := circomPrime)) input
    (roundsInputVar input) offset ?_ ?_ env env'
  · intro e e' hinput
    exact roundsInput_eval_eq input e e' hinput
  · exact SHA256Rounds63.computableWitnesses62_pairedW (p := circomPrime)

attribute [local irreducible] main

set_option maxHeartbeats 2000000 in
theorem computableWitnesses : circuit.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations offset)
  apply FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main
  simp only [
    Circuit.bind_structuralComputableWitnesses_iff,
    FormalCircuit.subcircuit_structuralComputableWitnesses_iff,
    Circuit.pure_structuralComputableWitnesses_iff,
    and_true]
  and_intros
  · exact rounds_flatStructural input offset env env'
  · simpa only [circuit_norm,
        SHA256Rounds63.circuit62_pairedW_localLength_eq] using
      (FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
        TailPairTight.circuit input (tightInputVar input offset)
        (offset + 10170)
        (by
          intro k env env' hle hagree hinput
          exact tailInput_eval_eq input offset env env'
            (ProverEnvironment.agreesBelow_of_le hagree hle) hinput)
        TailPairTight.computableWitnesses env env')
  · simpa only [circuit_norm,
        SHA256Rounds63.circuit62_pairedW_localLength_eq,
        TailPairTight.circuit, TailPairTight.elaborated] using
      (FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
        CarrySumAdd32.circuit input
        ⟨input.state[1], (tightOutputVar input offset).a63⟩
        (offset + 10499)
        (by
          intro k env env' hle hagree hinput
          exact carryInput_eval_eq _ _ env env'
            (input_state_nat_word_eval_eq input hinput 1 (by norm_num))
            (tail_a63_eval_eq (tightInputVar input offset) (offset + 10170)
              env env' (ProverEnvironment.agreesBelow_of_le hagree (by omega))))
        CarrySumAdd32.computableWitnesses env env')
  · simpa only [circuit_norm,
        SHA256Rounds63.circuit62_pairedW_localLength_eq,
        TailPairTight.circuit, TailPairTight.elaborated,
        CarrySumAdd32.circuit, CarrySumAdd32.elaborated] using
      (FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
        CarrySumAdd32.circuit input
        ⟨input.state[2], (st62Var input offset)[0]⟩
        (offset + 10531)
        (by
          intro k env env' hle hagree hinput
          exact carryInput_eval_eq _ _ env env'
            (input_state_nat_word_eval_eq input hinput 2 (by norm_num))
            (roundsOutput_nat_word_eval_eq input offset env env'
              (ProverEnvironment.agreesBelow_of_le hagree (by omega))
              hinput 0 (by norm_num)))
        CarrySumAdd32.computableWitnesses env env')
  · simpa only [circuit_norm,
        SHA256Rounds63.circuit62_pairedW_localLength_eq,
        TailPairTight.circuit, TailPairTight.elaborated,
        CarrySumAdd32.circuit, CarrySumAdd32.elaborated,
        DeferAdd.circuit, DeferAdd.elaborated] using
      (FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
        DeferAdd.circuit input
        ⟨input.state[3], (st62Var input offset)[1]⟩
        (offset + 10563)
        (by
          intro k env env' hle hagree hinput
          exact deferInput_eval_eq _ _ env env'
            (input_state_nat_word_eval_eq input hinput 3 (by norm_num))
            (roundsOutput_nat_word_eval_eq input offset env env'
              (ProverEnvironment.agreesBelow_of_le hagree (by omega))
              hinput 1 (by norm_num)))
        DeferAdd.computableWitnesses env env')
  · simpa only [circuit_norm,
        SHA256Rounds63.circuit62_pairedW_localLength_eq,
        TailPairTight.circuit, TailPairTight.elaborated,
        CarrySumAdd32.circuit, CarrySumAdd32.elaborated] using
      (FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
        CarrySumAdd32.circuit input
        ⟨input.state[5], (tightOutputVar input offset).e63⟩
        (offset + 10563)
        (by
          intro k env env' hle hagree hinput
          exact carryInput_eval_eq _ _ env env'
            (input_state_nat_word_eval_eq input hinput 5 (by norm_num))
            (tail_e63_eval_eq (tightInputVar input offset) (offset + 10170)
              env env' (ProverEnvironment.agreesBelow_of_le hagree (by omega))))
        CarrySumAdd32.computableWitnesses env env')
  · simpa only [circuit_norm,
        SHA256Rounds63.circuit62_pairedW_localLength_eq,
        TailPairTight.circuit, TailPairTight.elaborated,
        CarrySumAdd32.circuit, CarrySumAdd32.elaborated] using
      (FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
        CarrySumAdd32.circuit input
        ⟨input.state[6], (st62Var input offset)[4]⟩
        (offset + 10595)
        (by
          intro k env env' hle hagree hinput
          exact carryInput_eval_eq _ _ env env'
            (input_state_nat_word_eval_eq input hinput 6 (by norm_num))
            (roundsOutput_nat_word_eval_eq input offset env env'
              (ProverEnvironment.agreesBelow_of_le hagree (by omega))
              hinput 4 (by norm_num)))
        CarrySumAdd32.computableWitnesses env env')
  · simpa only [circuit_norm,
        SHA256Rounds63.circuit62_pairedW_localLength_eq,
        TailPairTight.circuit, TailPairTight.elaborated,
        CarrySumAdd32.circuit, CarrySumAdd32.elaborated,
        DeferAdd.circuit, DeferAdd.elaborated] using
      (FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
        DeferAdd.circuit input
        ⟨input.state[7], (st62Var input offset)[5]⟩
        (offset + 10627)
        (by
          intro k env env' hle hagree hinput
          exact deferInput_eval_eq _ _ env env'
            (input_state_nat_word_eval_eq input hinput 7 (by norm_num))
            (roundsOutput_nat_word_eval_eq input offset env env'
              (ProverEnvironment.agreesBelow_of_le hagree (by omega))
              hinput 5 (by norm_num)))
        DeferAdd.computableWitnesses env env')
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem output_eval_eq_of_agreesBelow
    (input : Var Inputs (F circomPrime)) (offset : ℕ)
    (env env' : ProverEnvironment (F circomPrime))
    (hagree : env.AgreesBelow (offset + 10627) env')
    (hinput : eval env input = eval env' input) :
    eval env (circuit.output input offset) =
      eval env' (circuit.output input offset) := by
  have hagree' : env.AgreesBelow (offset + 10170) env' :=
    ProverEnvironment.agreesBelow_of_le hagree (by omega)
  have hs3 := input_state_nat_word_map_eval_eq input hinput 3 (by norm_num)
  have hs7 := input_state_nat_word_map_eval_eq input hinput 7 (by norm_num)
  have hb1 := roundsOutput_nat_word_map_eval_eq input offset env env' hagree' hinput 1 (by norm_num)
  have hb5 := roundsOutput_nat_word_map_eval_eq input offset env env' hagree' hinput 5 (by norm_num)
  have h3 : Expression.eval env.toEnvironment
        (fromBitsExpr input.state[3] + fromBitsExpr ((st62Var input offset)[1])) =
      Expression.eval env'.toEnvironment
        (fromBitsExpr input.state[3] + fromBitsExpr ((st62Var input offset)[1])) := by
    show _ + _ = _ + _
    rw [CompressBlockWideSparseD.fromBits_eval_eq_of_map_eq _ _ _ hs3,
      CompressBlockWideSparseD.fromBits_eval_eq_of_map_eq _ _ _ hb1]
  have h7 : Expression.eval env.toEnvironment
        (fromBitsExpr input.state[7] + fromBitsExpr ((st62Var input offset)[5])) =
      Expression.eval env'.toEnvironment
        (fromBitsExpr input.state[7] + fromBitsExpr ((st62Var input offset)[5])) := by
    show _ + _ = _ + _
    rw [CompressBlockWideSparseD.fromBits_eval_eq_of_map_eq _ _ _ hs7,
      CompressBlockWideSparseD.fromBits_eval_eq_of_map_eq _ _ _ hb5]
  rw [CircuitType.eval_var_prover_to_verifier env (circuit.output input offset),
    CircuitType.eval_var_prover_to_verifier env' (circuit.output input offset)]
  apply Vector.ext
  intro j hj
  rw [← getElem_eval_vector env.toEnvironment (circuit.output input offset) j hj,
    ← getElem_eval_vector env'.toEnvironment (circuit.output input offset) j hj]
  simp only [circuit_norm, circuit, elaborated]
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
    exact CompressBlockWideSparseD.sparse32_map_eval_eq _ _ _ h3
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
    exact CompressBlockWideSparseD.sparse32_map_eval_eq _ _ _ h7

end Solution.SHA256.CompressBlock5D
