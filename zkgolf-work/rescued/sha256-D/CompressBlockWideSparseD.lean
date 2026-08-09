import Solution.SHA256.SHA256RoundsW
import Solution.SHA256.MessageScheduleSparse
import Solution.SHA256.CompressBlockWide
import Solution.SHA256.CarrySumAdd32
import Solution.SHA256.Round63DM
import Solution.SHA256.ScheduleStepLast
import Solution.SHA256.TailPairWide
import Solution.SHA256.Sparse32
import Solution.SHA256.DeferredSpec
import Challenge.Specs.SHA256

section
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2^35)] [Fact (p > 2^37)] [Fact (p > 2^76)] [Fact (p > 2^120)] [Fact (p > 2^77)]

namespace Solution.SHA256

namespace CompressBlockWideSparseD

abbrev Inputs := CompressBlockWide.Inputs

def main (input : Var Inputs (F p)) : Circuit (F p) (Var SHA256State (F p)) := do
  let w ← MessageScheduleSparse.circuit46 input.block
  let E62 ← ScheduleStepLast.circuit ⟨w[60], w[55], w[47], w[46]⟩
  let E63 ← ScheduleStepLast.circuit ⟨w[61], w[56], w[48], w[47]⟩
  let st62 ← SHA256Rounds63.circuit62_pairedW ⟨input.state, w⟩
  let o ← TailPairWide.circuit ⟨st62, E62, E63, input.state[0], input.state[4]⟩
  let r1 ← CarrySumAdd32.circuit ⟨input.state[1], o.a63⟩
  let r2 ← CarrySumAdd32.circuit ⟨input.state[2], st62[0]⟩
  let r3 ← DeferAdd.circuit ⟨input.state[3], st62[1]⟩
  let r5 ← CarrySumAdd32.circuit ⟨input.state[5], o.e63⟩
  let r6 ← CarrySumAdd32.circuit ⟨input.state[6], st62[4]⟩
  let r7 ← DeferAdd.circuit ⟨input.state[7], st62[5]⟩
  return #v[o.out0, r1, r2, r3, o.out4, r5, r6, r7]

instance elaborated : ElaboratedCircuit (F p) Inputs SHA256State main := by
  elaborate_circuit

def Assumptions (input : Inputs (F p)) : Prop :=
  (∀ i : Fin 8, i.val ≠ 3 → i.val ≠ 7 → Normalized input.state[i]) ∧
  RPShared.Numeric5W input.state[3] ∧ RPShared.Numeric5W input.state[7] ∧
  MessageScheduleSparse.Assumptions input.block

def Spec (input : Inputs (F p)) (out : SHA256State (F p)) : Prop :=
  out.map valueBits =
    Deferred.compressBlockD (input.state.map valueBits) (input.block.map valueBits)
  ∧ ∀ i : Fin 8, i.val ≠ 3 → i.val ≠ 7 → Normalized out[i]

set_option maxHeartbeats 4000000 in
theorem soundness : Soundness (F p) main Assumptions Spec := by
  circuit_proof_start [ScheduleStepLast.Spec, ScheduleStepLast.Assumptions,
    MessageScheduleSparse.Spec, MessageScheduleSparse.Assumptions,
    SHA256Rounds63.Spec62, SHA256Rounds63.Assumptions62PairedW,
    DeferAdd.circuit, DeferAdd.Spec, DeferAdd.Assumptions,
    TailPairWide.Spec, TailPairWide.Assumptions,
    CarrySumAdd32.circuit, CarrySumAdd32.Spec, CarrySumAdd32.Assumptions]
  obtain ⟨h_state_norm, h_q3, h_q7, h_block_norm⟩ := h_assumptions
  obtain ⟨h_input_state, h_input_block⟩ := h_input
  obtain ⟨h_sched, h_E62, h_E63, h_st62, h_o, h_a1, h_a2, h_a3, h_a5, h_a6, h_a7⟩ := h_holds
  have red : ∀ (m : ℕ) (V : ProvableVector (fields 32) m (Expression (F p))) (k : ℕ) (hk : k < m),
      (eval env V)[k]'hk = Vector.map (Expression.eval env) (V[k]'hk) := by
    intro m V k hk
    rw [← getElem_eval_vector env V k hk, CircuitType.eval_var_fields]
  have h_eval : ∀ (i : ℕ) (hi : i < 8),
      Vector.map (Expression.eval env) (input_var_state[i]'hi) = input_state[i]'hi := by
    intro i hi
    rw [← red 8 input_var_state i hi, h_input_state]
  have h_sched_full : MessageScheduleSparse.Spec input_block (eval env (MessageScheduleSparse.circuit46.output input_var_block i₀)) := h_sched h_block_norm
  have hval : ∀ (j : ℕ) (hj : j < 62),
      valueBits (Vector.map (Expression.eval env)
        ((MessageScheduleSparse.circuit46.output input_var_block i₀)[j]'(by omega))) =
        (Specs.SHA256.messageSchedule (Vector.map valueBits input_block))[j]'(by omega) := by
    intro j hj
    rw [← red 64 (MessageScheduleSparse.circuit46.output input_var_block i₀) j (by omega)]
    exact h_sched_full.1 ⟨j, by omega⟩
  have hnorm : ∀ (j : ℕ) (hj : j < 62), 1 ≤ j →
      Normalized (Vector.map (Expression.eval env)
        ((MessageScheduleSparse.circuit46.output input_var_block i₀)[j]'(by omega))) := by
    intro j hj hj1
    rw [← red 64 (MessageScheduleSparse.circuit46.output input_var_block i₀) j (by omega)]
    simpa only [Fin.val_mk, Nat.sub_add_cancel hj1] using
      h_sched_full.2.2 ⟨j - 1, by omega⟩
  obtain ⟨hE62_val, hE62_bound⟩ := h_E62
    ⟨hnorm 60 (by norm_num) (by norm_num), hnorm 55 (by norm_num) (by norm_num),
      hnorm 47 (by norm_num) (by norm_num), hnorm 46 (by norm_num) (by norm_num)⟩
  obtain ⟨hE63_val, hE63_bound⟩ := h_E63
    ⟨hnorm 61 (by norm_num) (by norm_num), hnorm 56 (by norm_num) (by norm_num),
      hnorm 48 (by norm_num) (by norm_num), hnorm 47 (by norm_num) (by norm_num)⟩
  obtain ⟨hst62_val, hst62_norm⟩ := h_st62 ⟨h_state_norm, h_q3, h_q7,
    h_sched_full.2.1,
    fun i hi1 _ => by
      simpa only [Fin.val_mk, Nat.sub_add_cancel hi1] using
        h_sched_full.2.2 ⟨i.val - 1, by omega⟩⟩
  have hcong : SHA256Rounds.valStateAfterRound (Vector.map valueBits input_state)
        (Vector.map valueBits (eval env (MessageScheduleSparse.circuit46.output input_var_block i₀))) 62 =
      SHA256Rounds.valStateAfterRound (Vector.map valueBits input_state)
        (Specs.SHA256.messageSchedule (Vector.map valueBits input_block)) 62 := by
    apply SHA256Rounds.valStateAfterRound_congr _ _ _ 62 (by norm_num)
    intro j hj hlt
    rw [Vector.getElem_map]
    exact h_sched_full.1 ⟨j, by omega⟩
  rw [hcong] at hst62_val
  have hs0n : Normalized (Vector.map (Expression.eval env) input_var_state[0]) := by
    rw [h_eval 0 (by norm_num)]; exact h_state_norm 0 (by norm_num) (by norm_num)
  have hs4n : Normalized (Vector.map (Expression.eval env) input_var_state[4]) := by
    rw [h_eval 4 (by norm_num)]; exact h_state_norm 4 (by norm_num) (by norm_num)
  obtain ⟨ha63_val, he63_val, ho_v0, ho_v4, ho_n0, ho_n4, ha63_norm, he63_norm⟩ :=
    h_o ⟨hst62_norm, hs0n, hs4n, hE62_bound, hE63_bound⟩
  rw [TailPairWide.specSt63_eq, hst62_val, hE62_val, hval 60 (by norm_num), hval 55 (by norm_num),
    hval 47 (by norm_num), hval 46 (by norm_num),
    ← MessageSchedule.messageSchedule_getElem_62 (Vector.map valueBits input_block)] at ha63_val he63_val
  rw [TailPairWide.specSt64_eq, hst62_val, hE62_val, hval 60 (by norm_num), hval 55 (by norm_num),
    hval 47 (by norm_num), hval 46 (by norm_num),
    ← MessageSchedule.messageSchedule_getElem_62 (Vector.map valueBits input_block),
    hE63_val, hval 61 (by norm_num), hval 56 (by norm_num),
    hval 48 (by norm_num), hval 47 (by norm_num),
    ← MessageSchedule.messageSchedule_getElem_63 (Vector.map valueBits input_block),
    ← SHA256Rounds.sha256Compress_split_last2 (Vector.map valueBits input_state)
      (Specs.SHA256.messageSchedule (Vector.map valueBits input_block))] at ho_v0 ho_v4
  simp only [h_eval 0 (by norm_num)] at ho_v0
  simp only [h_eval 4 (by norm_num)] at ho_v4
  obtain ⟨ha1_val, ha1_norm⟩ := h_a1 ⟨by rw [h_eval 1 (by norm_num)]; exact h_state_norm 1 (by norm_num) (by norm_num), ha63_norm⟩
  obtain ⟨ha2_val, ha2_norm⟩ := h_a2 ⟨by rw [h_eval 2 (by norm_num)]; exact h_state_norm 2 (by norm_num) (by norm_num),
    by rw [← CircuitType.eval_var_fields, getElem_eval_vector]; exact hst62_norm ⟨0, by norm_num⟩⟩
  have ha3_val := h_a3 ⟨by rw [h_eval 3 (by norm_num)]; exact h_q3.bound,
    valueBits_lt_two_pow _ (by
      rw [← CircuitType.eval_var_fields, getElem_eval_vector]
      exact hst62_norm ⟨1, by norm_num⟩)⟩
  obtain ⟨ha5_val, ha5_norm⟩ := h_a5 ⟨by rw [h_eval 5 (by norm_num)]; exact h_state_norm 5 (by norm_num) (by norm_num), he63_norm⟩
  obtain ⟨ha6_val, ha6_norm⟩ := h_a6 ⟨by rw [h_eval 6 (by norm_num)]; exact h_state_norm 6 (by norm_num) (by norm_num),
    by rw [← CircuitType.eval_var_fields, getElem_eval_vector]; exact hst62_norm ⟨4, by norm_num⟩⟩
  have ha7_val := h_a7 ⟨by rw [h_eval 7 (by norm_num)]; exact h_q7.bound,
    valueBits_lt_two_pow _ (by
      rw [← CircuitType.eval_var_fields, getElem_eval_vector]
      exact hst62_norm ⟨5, by norm_num⟩)⟩
  simp only [h_eval 1 (by norm_num)] at ha1_val
  simp only [h_eval 2 (by norm_num)] at ha2_val
  simp only [h_eval 3 (by norm_num)] at ha3_val
  simp only [h_eval 5 (by norm_num)] at ha5_val
  simp only [h_eval 6 (by norm_num)] at ha6_val
  simp only [h_eval 7 (by norm_num)] at ha7_val
  have hL46 : ∀ (b : SHA256Block (Expression (F p))),
      (MessageScheduleSparse.circuit46).localLength b = 4186 := fun b => by
    simp only [circuit_norm, MessageScheduleSparse.circuit46,
      MessageScheduleSparse.elaborated46,
      ScheduleStepUnchecked.circuit]
  have hL58 : ∀ (b : ScheduleStep.Inputs (Expression (F p))),
      ScheduleStepLast.circuit.localLength b = 58 := fun b => by
    simp only [circuit_norm, ScheduleStepLast.circuit, ScheduleStepLast.elaborated]
  have hL62 : ∀ (b : SHA256Rounds63.Inputs (Expression (F p))),
      SHA256Rounds63.circuit62_pairedW.localLength b = 10170 := fun b => by
    simp only [circuit_norm, SHA256Rounds63.circuit62_pairedW,
      SHA256Rounds63.elaborated62_pairedW]
  have hL331 : ∀ (b : TailPairWide.Inputs (Expression (F p))),
      TailPairWide.circuit.localLength b = 331 := fun b => by
    simp only [circuit_norm, TailPairWide.circuit, TailPairWide.elaborated]
  have hTPo0 : ∀ (a : TailPairWide.Inputs (Expression (F p))) (n : ℕ),
      (TailPairWide.circuit.output a n).out0 = Vector.mapRange 32 (fun i => var { index := n + 128 + 32 + 32 + 32 + i }) := fun a n => by
    simp only [circuit_norm, TailPairWide.circuit, TailPairWide.elaborated]
  have hTPo4 : ∀ (a : TailPairWide.Inputs (Expression (F p))) (n : ℕ),
      (TailPairWide.circuit.output a n).out4 = Vector.mapRange 32 (fun i => var { index := n + 128 + 32 + 32 + i }) := fun a n => by
    simp only [circuit_norm, TailPairWide.circuit, TailPairWide.elaborated]
  have hTPa63 : ∀ (a : TailPairWide.Inputs (Expression (F p))) (n : ℕ),
      (TailPairWide.circuit.output a n).a63 = Vector.mapRange 32 (fun i => var { index := n + 32 + 32 + 32 + i }) := fun a n => by
    simp only [circuit_norm, TailPairWide.circuit, TailPairWide.elaborated]
  have hTPe63 : ∀ (a : TailPairWide.Inputs (Expression (F p))) (n : ℕ),
      (TailPairWide.circuit.output a n).e63 = Vector.mapRange 32 (fun i => var { index := n + 32 + 32 + i }) := fun a n => by
    simp only [circuit_norm, TailPairWide.circuit, TailPairWide.elaborated]
  have hAdd32o : ∀ (a : CarrySumAdd32.Inputs (Expression (F p))) (n : ℕ),
      CarrySumAdd32.circuit.output a n = Vector.mapRange 32 (fun i => var { index := n + i }) := fun a n => by
    simp only [circuit_norm, CarrySumAdd32.circuit, CarrySumAdd32.elaborated]
  simp only [hL46, hL58, hL62, hL331, hTPo0, hTPo4, hTPa63, hTPe63, hAdd32o] at ho_v0 ho_v4 ha63_val he63_val ha1_val ha2_val ha3_val ha5_val ha6_val ha7_val ho_n0 ho_n4 ha63_norm he63_norm ha1_norm ha2_norm ha5_norm ha6_norm
  simp only [← CircuitType.eval_var_fields] at ho_v0 ho_v4 ha63_val he63_val ha1_val ha2_val ha3_val ha5_val ha6_val ha7_val
  rw [ha63_val] at ha1_val
  rw [he63_val] at ha5_val
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · apply Vector.ext
    intro i hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [Deferred.compressBlockD_getElem_ne _ _ 0 (by norm_num) (by norm_num) (by norm_num),
        SHA256Rounds.compressBlock_getElem _ _ 0 (by norm_num)]
      simp only [Vector.getElem_map, ← getElem_eval_vector,
        Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
      exact ho_v0
    · rw [Deferred.compressBlockD_getElem_ne _ _ 1 (by norm_num) (by norm_num) (by norm_num),
        SHA256Rounds.compressBlock_getElem _ _ 1 (by norm_num),
        SHA256Rounds.sha256Compress_split_last2, Round63DM.sha256Round_eq, Round63DM.vec8_getElem1]
      simp only [Vector.getElem_map, ← getElem_eval_vector,
        Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ, _root_.add32]
      exact ha1_val
    · rw [Deferred.compressBlockD_getElem_ne _ _ 2 (by norm_num) (by norm_num) (by norm_num),
        SHA256Rounds.compressBlock_getElem _ _ 2 (by norm_num),
        SHA256Rounds.sha256Compress_split_last2, Round63DM.sha256Round_eq, Round63DM.vec8_getElem2,
        Round63DM.sha256Round_eq, Round63DM.vec8_getElem1, ← hst62_val]
      simp only [Vector.getElem_map, ← getElem_eval_vector,
        Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ, _root_.add32]
      exact ha2_val
    · rw [Deferred.compressBlockD_getElem_eq _ _ 3 (by norm_num) (by norm_num),
        SHA256Rounds.sha256Compress_split_last2, Round63DM.sha256Round_eq, Round63DM.vec8_getElem3,
        Round63DM.sha256Round_eq, Round63DM.vec8_getElem2, ← hst62_val]
      simp only [Vector.getElem_map, ← getElem_eval_vector,
        Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ, _root_.add32]
      exact ha3_val
    · rw [Deferred.compressBlockD_getElem_ne _ _ 4 (by norm_num) (by norm_num) (by norm_num),
        SHA256Rounds.compressBlock_getElem _ _ 4 (by norm_num)]
      simp only [Vector.getElem_map, ← getElem_eval_vector,
        Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
      exact ho_v4
    · rw [Deferred.compressBlockD_getElem_ne _ _ 5 (by norm_num) (by norm_num) (by norm_num),
        SHA256Rounds.compressBlock_getElem _ _ 5 (by norm_num),
        SHA256Rounds.sha256Compress_split_last2, Round63DM.sha256Round_eq, Round63DM.vec8_getElem5]
      simp only [Vector.getElem_map, ← getElem_eval_vector,
        Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ, _root_.add32]
      exact ha5_val
    · rw [Deferred.compressBlockD_getElem_ne _ _ 6 (by norm_num) (by norm_num) (by norm_num),
        SHA256Rounds.compressBlock_getElem _ _ 6 (by norm_num),
        SHA256Rounds.sha256Compress_split_last2, Round63DM.sha256Round_eq, Round63DM.vec8_getElem6,
        Round63DM.sha256Round_eq, Round63DM.vec8_getElem5, ← hst62_val]
      simp only [Vector.getElem_map, ← getElem_eval_vector,
        Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ, _root_.add32]
      exact ha6_val
    · rw [Deferred.compressBlockD_getElem_eq _ _ 7 (by norm_num) (by norm_num),
        SHA256Rounds.sha256Compress_split_last2, Round63DM.sha256Round_eq, Round63DM.vec8_getElem7,
        Round63DM.sha256Round_eq, Round63DM.vec8_getElem6, ← hst62_val]
      simp only [Vector.getElem_map, ← getElem_eval_vector,
        Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ, _root_.add32]
      exact ha7_val
  · intro i hi3 hi7
    obtain ⟨i, hi⟩ := i
    simp only [Fin.val_mk] at hi3 hi7 ⊢
    rw [red 8 _ i hi]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 4 ∨ i = 5 ∨ i = 6) with
      rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ]
    · exact ho_n0
    · exact ha1_norm
    · exact ha2_norm
    · exact ho_n4
    · exact ha5_norm
    · exact ha6_norm
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl

set_option maxHeartbeats 4000000 in
theorem completeness : Completeness (F p) main Assumptions := by
  circuit_proof_start [ScheduleStepLast.Spec, ScheduleStepLast.Assumptions,
    MessageScheduleSparse.Spec, MessageScheduleSparse.Assumptions,
    SHA256Rounds63.Spec62, SHA256Rounds63.Assumptions62PairedW,
    DeferAdd.circuit, DeferAdd.Spec, DeferAdd.Assumptions,
    TailPairWide.Spec, TailPairWide.Assumptions,
    CarrySumAdd32.circuit, CarrySumAdd32.Spec, CarrySumAdd32.Assumptions]
  obtain ⟨h_state_norm, h_q3, h_q7, h_block_norm⟩ := h_assumptions
  obtain ⟨h_input_state, h_input_block⟩ := h_input
  obtain ⟨h_sched_impl, h_E62_impl, h_E63_impl, h_st62_impl, h_o_impl, _⟩ := h_env
  have red : ∀ (m : ℕ) (V : ProvableVector (fields 32) m (Expression (F p))) (k : ℕ) (hk : k < m),
      (eval env.toEnvironment V)[k]'hk = Vector.map (Expression.eval env.toEnvironment) (V[k]'hk) := by
    intro m V k hk
    rw [← getElem_eval_vector env.toEnvironment V k hk, CircuitType.eval_var_fields]
  have h_eval : ∀ (i : ℕ) (hi : i < 8),
      Vector.map (Expression.eval env.toEnvironment) (input_var_state[i]'hi) = input_state[i]'hi := by
    intro i hi
    rw [← red 8 input_var_state i hi, h_input_state]
  have h_sched_full : MessageScheduleSparse.Spec input_block
      (eval env.toEnvironment (MessageScheduleSparse.circuit46.output input_var_block i₀)) :=
    h_sched_impl h_block_norm
  have hnorm : ∀ (j : ℕ) (hj : j < 62), 1 ≤ j →
      Normalized (Vector.map (Expression.eval env.toEnvironment)
        ((MessageScheduleSparse.circuit46.output input_var_block i₀)[j]'(by omega))) := by
    intro j hj hj1
    rw [← red 64 (MessageScheduleSparse.circuit46.output input_var_block i₀) j (by omega)]
    simpa only [Fin.val_mk, Nat.sub_add_cancel hj1] using
      h_sched_full.2.2 ⟨j - 1, by omega⟩
  obtain ⟨_, hE62_bound⟩ := h_E62_impl
    ⟨hnorm 60 (by norm_num) (by norm_num), hnorm 55 (by norm_num) (by norm_num),
      hnorm 47 (by norm_num) (by norm_num), hnorm 46 (by norm_num) (by norm_num)⟩
  obtain ⟨_, hE63_bound⟩ := h_E63_impl
    ⟨hnorm 61 (by norm_num) (by norm_num), hnorm 56 (by norm_num) (by norm_num),
      hnorm 48 (by norm_num) (by norm_num), hnorm 47 (by norm_num) (by norm_num)⟩
  obtain ⟨_, hst62_norm⟩ := h_st62_impl ⟨h_state_norm, h_q3, h_q7,
    h_sched_full.2.1,
    fun i hi1 _ => by
      simpa only [Fin.val_mk, Nat.sub_add_cancel hi1] using
        h_sched_full.2.2 ⟨i.val - 1, by omega⟩⟩
  have hs0n : Normalized (Vector.map (Expression.eval env.toEnvironment) input_var_state[0]) := by
    rw [h_eval 0 (by norm_num)]; exact h_state_norm 0 (by norm_num) (by norm_num)
  have hs4n : Normalized (Vector.map (Expression.eval env.toEnvironment) input_var_state[4]) := by
    rw [h_eval 4 (by norm_num)]; exact h_state_norm 4 (by norm_num) (by norm_num)
  obtain ⟨_, _, _, _, _, _, ha63_norm, he63_norm⟩ :=
    h_o_impl ⟨hst62_norm, hs0n, hs4n, hE62_bound, hE63_bound⟩
  refine ⟨h_block_norm,
    ⟨hnorm 60 (by norm_num) (by norm_num), hnorm 55 (by norm_num) (by norm_num),
      hnorm 47 (by norm_num) (by norm_num), hnorm 46 (by norm_num) (by norm_num)⟩,
    ⟨hnorm 61 (by norm_num) (by norm_num), hnorm 56 (by norm_num) (by norm_num),
      hnorm 48 (by norm_num) (by norm_num), hnorm 47 (by norm_num) (by norm_num)⟩,
    ⟨h_state_norm, h_q3, h_q7, h_sched_full.2.1,
      fun i hi1 _ => by
        simpa only [Fin.val_mk, Nat.sub_add_cancel hi1] using
          h_sched_full.2.2 ⟨i.val - 1, by omega⟩⟩,
    ⟨hst62_norm, hs0n, hs4n, hE62_bound, hE63_bound⟩,
    ⟨by rw [h_eval 1 (by norm_num)]; exact h_state_norm 1 (by norm_num) (by norm_num), ha63_norm⟩,
    ⟨by rw [h_eval 2 (by norm_num)]; exact h_state_norm 2 (by norm_num) (by norm_num),
      by rw [← CircuitType.eval_var_fields, getElem_eval_vector]; exact hst62_norm ⟨0, by norm_num⟩⟩,
    ⟨by rw [h_eval 3 (by norm_num)]; exact h_q3.bound,
      valueBits_lt_two_pow _ (by
        rw [← CircuitType.eval_var_fields, getElem_eval_vector]
        exact hst62_norm ⟨1, by norm_num⟩)⟩,
    ⟨by rw [h_eval 5 (by norm_num)]; exact h_state_norm 5 (by norm_num) (by norm_num), he63_norm⟩,
    ⟨by rw [h_eval 6 (by norm_num)]; exact h_state_norm 6 (by norm_num) (by norm_num),
      by rw [← CircuitType.eval_var_fields, getElem_eval_vector]; exact hst62_norm ⟨4, by norm_num⟩⟩,
    ⟨by rw [h_eval 7 (by norm_num)]; exact h_q7.bound,
      valueBits_lt_two_pow _ (by
        rw [← CircuitType.eval_var_fields, getElem_eval_vector]
        exact hst62_norm ⟨5, by norm_num⟩)⟩⟩

def circuit : FormalCircuit (F p) Inputs SHA256State := {
  main, elaborated, Assumptions, Spec, soundness
  completeness := by simp only [completeness]
}

end CompressBlockWideSparseD
end Solution.SHA256
end
