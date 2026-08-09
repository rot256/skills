import Solution.SHA256.SHA256Rounds1
import Solution.SHA256.MessageScheduleSparse
import Solution.SHA256.CarrySumAdd32
import Solution.SHA256.Round62Wide
import Solution.SHA256.Round63DMWide
import Solution.SHA256.ScheduleStepLast
import Solution.SHA256.TailPairWide
import Solution.SHA256.Sparse32
import Solution.SHA256.DeferredSpec
import Challenge.Specs.SHA256

section
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2^35)] [Fact (p > 2^37)] [Fact (p > 2^76)] [Fact (p > 2^120)] [Fact (p > 2^77)]

namespace Solution.SHA256

namespace CompressBlock1SparseD

def main (input : Var SHA256Block (F p)) : Circuit (F p) (Var SHA256State (F p)) := do
  let w ← MessageScheduleSparse.circuit46 input
  let E62 ← ScheduleStepLast.circuit ⟨w[60], w[55], w[47], w[46]⟩
  let E63 ← ScheduleStepLast.circuit ⟨w[61], w[56], w[48], w[47]⟩
  let st62 ← SHA256Rounds.circuit62_block1_paired_sparse w
  let o ← TailPairWide.circuit
    ⟨st62, E62, E63, constWord32 Round0Block1.h0_0, constWord32 Round0Block1.h0_4⟩
  let r1 ← CarrySumAddOddConst32.circuit Round0Block1.h0_1 Round0Block1.h0_1_lt (by norm_num [Round0Block1.h0_1]) ⟨o.a63⟩
  let r2 ← CarrySumAddMod4Const32.circuit Round0Block1.h0_2 Round0Block1.h0_2_lt (by norm_num [Round0Block1.h0_2]) ⟨st62[0]⟩
  let r3 ← DeferAddConst.circuit Round0Block1.h0_3 Round0Block1.h0_3_lt ⟨st62[1]⟩
  let r5 ← CarrySumAddMod8Const32.circuit Round0Block1.h0_5 Round0Block1.h0_5_lt (by norm_num [Round0Block1.h0_5]) ⟨o.e63⟩
  let r6 ← CarrySumAddOddConst32.circuit Round0Block1.h0_6 Round0Block1.h0_6_lt (by norm_num [Round0Block1.h0_6]) ⟨st62[4]⟩
  let r7 ← DeferAddConst.circuit Round0Block1.h0_7 Round0Block1.h0_7_lt ⟨st62[5]⟩
  return #v[o.out0, r1, r2, r3, o.out4, r5, r6, r7]

instance elaborated : ElaboratedCircuit (F p) SHA256Block SHA256State main := by
  elaborate_circuit

def Assumptions (input : SHA256Block (F p)) : Prop :=
  MessageScheduleSparse.Assumptions input

def Spec (input : SHA256Block (F p)) (out : SHA256State (F p)) : Prop :=
  out.map valueBits =
    Deferred.compressBlockD Specs.SHA256.H0 (input.map valueBits)
  ∧ ∀ i : Fin 8, i.val ≠ 3 → i.val ≠ 7 → Normalized out[i]

set_option maxHeartbeats 4000000 in
theorem soundness : Soundness (F p) main Assumptions Spec := by
  circuit_proof_start [ScheduleStepLast.Spec, ScheduleStepLast.Assumptions,
    MessageScheduleSparse.Spec, MessageScheduleSparse.Assumptions,
    SHA256Rounds.Spec62_block1, SHA256Rounds.Assumptions62_block1Sparse,
    TailPairWide.Spec, TailPairWide.Assumptions,
    CarrySumAddOddConst32.circuit, CarrySumAddOddConst32.Spec, CarrySumAddOddConst32.Assumptions,
    CarrySumAddMod4Const32.circuit, CarrySumAddMod4Const32.Spec, CarrySumAddMod4Const32.Assumptions,
    CarrySumAddMod8Const32.circuit, CarrySumAddMod8Const32.Spec, CarrySumAddMod8Const32.Assumptions,
    DeferAddConst.circuit, DeferAddConst.Spec, DeferAddConst.Assumptions]
  obtain ⟨h_sched, h_E62, h_E63, h_st62, h_o, h_a1, h_a2, h_a3, h_a5, h_a6, h_a7⟩ := h_holds
  -- H0 constant helpers
  have hnorm_h0 : ∀ (m : ℕ),
      Normalized (Vector.map (Expression.eval env) (constWord32 (p:=p) m)) :=
    fun m => SHA256Rounds.normalized_constWord32 env m
  -- message-schedule spec (sparse: W0 numeric, W1.. normalized)
  have h_sched_full : MessageScheduleSparse.Spec input
      (eval env (MessageScheduleSparse.circuit46.output input_var i₀)) := h_sched h_assumptions
  have red : ∀ (m : ℕ) (V : ProvableVector (fields 32) m (Expression (F p))) (k : ℕ) (hk : k < m),
      (eval env V)[k]'hk = Vector.map (Expression.eval env) (V[k]'hk) := by
    intro m V k hk
    rw [← getElem_eval_vector env V k hk, CircuitType.eval_var_fields]
  have hval : ∀ (j : ℕ) (hj : j < 62),
      valueBits (Vector.map (Expression.eval env)
        ((MessageScheduleSparse.circuit46.output input_var i₀)[j]'(by omega))) =
        (Specs.SHA256.messageSchedule (Vector.map valueBits input))[j]'(by omega) := by
    intro j hj
    rw [← red 64 (MessageScheduleSparse.circuit46.output input_var i₀) j (by omega)]
    exact h_sched_full.1 ⟨j, by omega⟩
  have hnorm : ∀ (j : ℕ) (hj : j < 62), 1 ≤ j →
      Normalized (Vector.map (Expression.eval env)
        ((MessageScheduleSparse.circuit46.output input_var i₀)[j]'(by omega))) := by
    intro j hj hj1
    rw [← red 64 (MessageScheduleSparse.circuit46.output input_var i₀) j (by omega)]
    simpa only [Fin.val_mk, Nat.sub_add_cancel hj1] using
      h_sched_full.2.2 ⟨j - 1, by omega⟩
  obtain ⟨hE62_val, hE62_bound⟩ := h_E62 ⟨hnorm 60 (by norm_num) (by norm_num), hnorm 55 (by norm_num) (by norm_num),
    hnorm 47 (by norm_num) (by norm_num), hnorm 46 (by norm_num) (by norm_num)⟩
  obtain ⟨hE63_val, hE63_bound⟩ := h_E63 ⟨hnorm 61 (by norm_num) (by norm_num), hnorm 56 (by norm_num) (by norm_num),
    hnorm 48 (by norm_num) (by norm_num), hnorm 47 (by norm_num) (by norm_num)⟩
  -- circuit62_block1: state H0, schedule w
  obtain ⟨hst62_val, hst62_norm⟩ := h_st62 ⟨h_sched_full.2.1,
    fun i hi1 _ => by
      simpa only [Fin.val_mk, Nat.sub_add_cancel hi1] using
        h_sched_full.2.2 ⟨i.val - 1, by omega⟩⟩
  have hcong : SHA256Rounds.valStateAfterRound Specs.SHA256.H0
        (Vector.map valueBits (eval env (MessageScheduleSparse.circuit46.output input_var i₀))) 62 =
      SHA256Rounds.valStateAfterRound Specs.SHA256.H0
        (Specs.SHA256.messageSchedule (Vector.map valueBits input)) 62 := by
    apply SHA256Rounds.valStateAfterRound_congr _ _ _ 62 (by norm_num)
    intro j hj hlt
    rw [Vector.getElem_map]
    exact h_sched_full.1 ⟨j, by omega⟩
  rw [hcong] at hst62_val
  obtain ⟨ha63_val, he63_val, ho_v0, ho_v4, ho_n0, ho_n4, ha63_norm, he63_norm⟩ :=
    h_o ⟨hst62_norm, hnorm_h0 _, hnorm_h0 _, hE62_bound, hE63_bound⟩
  rw [TailPairWide.specSt63_eq, hst62_val, hE62_val, hval 60 (by norm_num), hval 55 (by norm_num),
    hval 47 (by norm_num), hval 46 (by norm_num),
    ← MessageSchedule.messageSchedule_getElem_62 (Vector.map valueBits input)] at ha63_val he63_val
  rw [TailPairWide.specSt64_eq, hst62_val, hE62_val, hval 60 (by norm_num), hval 55 (by norm_num),
    hval 47 (by norm_num), hval 46 (by norm_num),
    ← MessageSchedule.messageSchedule_getElem_62 (Vector.map valueBits input),
    hE63_val, hval 61 (by norm_num), hval 56 (by norm_num),
    hval 48 (by norm_num), hval 47 (by norm_num),
    ← MessageSchedule.messageSchedule_getElem_63 (Vector.map valueBits input),
    ← SHA256Rounds.sha256Compress_split_last2 Specs.SHA256.H0
      (Specs.SHA256.messageSchedule (Vector.map valueBits input))] at ho_v0 ho_v4
  rw [SHA256Rounds.valueBits_constWord32_of_lt env Round0Block1.h0_0_lt, Round0Block1.h0_0_eq] at ho_v0
  rw [SHA256Rounds.valueBits_constWord32_of_lt env Round0Block1.h0_4_lt, Round0Block1.h0_4_eq] at ho_v4
  obtain ⟨ha1_val, ha1_norm⟩ := h_a1 ha63_norm
  obtain ⟨ha2_val, ha2_norm⟩ := h_a2
    (by rw [← CircuitType.eval_var_fields, getElem_eval_vector]; exact hst62_norm ⟨0, by norm_num⟩)
  have ha3_val := h_a3
    (by rw [← CircuitType.eval_var_fields, getElem_eval_vector]; exact hst62_norm ⟨1, by norm_num⟩)
  obtain ⟨ha5_val, ha5_norm⟩ := h_a5 he63_norm
  obtain ⟨ha6_val, ha6_norm⟩ := h_a6
    (by rw [← CircuitType.eval_var_fields, getElem_eval_vector]; exact hst62_norm ⟨4, by norm_num⟩)
  have ha7_val := h_a7
    (by rw [← CircuitType.eval_var_fields, getElem_eval_vector]; exact hst62_norm ⟨5, by norm_num⟩)
  simp only [Nat.mod_eq_of_lt Round0Block1.h0_1_lt, Round0Block1.h0_1_eq] at ha1_val
  simp only [Nat.mod_eq_of_lt Round0Block1.h0_2_lt, Round0Block1.h0_2_eq] at ha2_val
  simp only [Round0Block1.h0_3_eq] at ha3_val
  simp only [Nat.mod_eq_of_lt Round0Block1.h0_5_lt, Round0Block1.h0_5_eq] at ha5_val
  simp only [Nat.mod_eq_of_lt Round0Block1.h0_6_lt, Round0Block1.h0_6_eq] at ha6_val
  simp only [Round0Block1.h0_7_eq] at ha7_val
  have hL46 : ∀ (b : SHA256Block (Expression (F p))),
      (MessageScheduleSparse.circuit46).localLength b = 4186 := fun b => by
    simp only [circuit_norm, MessageScheduleSparse.circuit46, MessageScheduleSparse.elaborated46,
      ScheduleStepUnchecked.circuit]
  have hL58 : ∀ (b : ScheduleStep.Inputs (Expression (F p))),
      ScheduleStepLast.circuit.localLength b = 58 := fun b => by
    simp only [circuit_norm, ScheduleStepLast.circuit, ScheduleStepLast.elaborated]
  have hL62 : ∀ (b : SHA256Schedule (Expression (F p))),
      SHA256Rounds.circuit62_block1_paired_sparse.localLength b = 10031 := fun b => by
    simp only [circuit_norm, SHA256Rounds.circuit62_block1_paired_sparse,
      SHA256Rounds.elaborated62_block1_paired_sparse]
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
  simp only [hL46, hL58, hL62, hL331, hTPo0, hTPo4, hTPa63, hTPe63] at ho_v0 ho_v4 ha63_val he63_val ha1_val ha2_val ha3_val ha5_val ha6_val ha7_val ho_n0 ho_n4 ha63_norm he63_norm ha1_norm ha2_norm ha5_norm ha6_norm
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
    SHA256Rounds.Spec62_block1, SHA256Rounds.Assumptions62_block1Sparse,
    TailPairWide.Spec, TailPairWide.Assumptions,
    CarrySumAddOddConst32.circuit, CarrySumAddOddConst32.Spec, CarrySumAddOddConst32.Assumptions,
    CarrySumAddMod4Const32.circuit, CarrySumAddMod4Const32.Spec, CarrySumAddMod4Const32.Assumptions,
    CarrySumAddMod8Const32.circuit, CarrySumAddMod8Const32.Spec, CarrySumAddMod8Const32.Assumptions,
    DeferAddConst.circuit, DeferAddConst.Spec, DeferAddConst.Assumptions]
  obtain ⟨h_sched_impl, h_E62_impl, h_E63_impl, h_st62_impl, h_o_impl, _⟩ := h_env
  have hnorm_h0 : ∀ (m : ℕ),
      Normalized (Vector.map (Expression.eval env.toEnvironment) (constWord32 (p:=p) m)) :=
    fun m => SHA256Rounds.normalized_constWord32 env.toEnvironment m
  have h_sched_full : MessageScheduleSparse.Spec input
      (eval env.toEnvironment (MessageScheduleSparse.circuit46.output input_var i₀)) :=
    h_sched_impl h_assumptions
  have red : ∀ (m : ℕ) (V : ProvableVector (fields 32) m (Expression (F p))) (k : ℕ) (hk : k < m),
      (eval env.toEnvironment V)[k]'hk = Vector.map (Expression.eval env.toEnvironment) (V[k]'hk) := by
    intro m V k hk
    rw [← getElem_eval_vector env.toEnvironment V k hk, CircuitType.eval_var_fields]
  have hnorm : ∀ (j : ℕ) (hj : j < 62), 1 ≤ j →
      Normalized (Vector.map (Expression.eval env.toEnvironment)
        ((MessageScheduleSparse.circuit46.output input_var i₀)[j]'(by omega))) := by
    intro j hj hj1
    rw [← red 64 (MessageScheduleSparse.circuit46.output input_var i₀) j (by omega)]
    simpa only [Fin.val_mk, Nat.sub_add_cancel hj1] using
      h_sched_full.2.2 ⟨j - 1, by omega⟩
  obtain ⟨_, hE62_bound⟩ := h_E62_impl ⟨hnorm 60 (by norm_num) (by norm_num), hnorm 55 (by norm_num) (by norm_num),
    hnorm 47 (by norm_num) (by norm_num), hnorm 46 (by norm_num) (by norm_num)⟩
  obtain ⟨_, hE63_bound⟩ := h_E63_impl ⟨hnorm 61 (by norm_num) (by norm_num), hnorm 56 (by norm_num) (by norm_num),
    hnorm 48 (by norm_num) (by norm_num), hnorm 47 (by norm_num) (by norm_num)⟩
  obtain ⟨_, hst62_norm⟩ := h_st62_impl ⟨h_sched_full.2.1,
    fun i hi1 _ => by
      simpa only [Fin.val_mk, Nat.sub_add_cancel hi1] using
        h_sched_full.2.2 ⟨i.val - 1, by omega⟩⟩
  obtain ⟨_, _, _, _, _, _, ha63_norm, he63_norm⟩ :=
    h_o_impl ⟨hst62_norm, hnorm_h0 _, hnorm_h0 _, hE62_bound, hE63_bound⟩
  refine ⟨h_assumptions,
    ⟨hnorm 60 (by norm_num) (by norm_num), hnorm 55 (by norm_num) (by norm_num), hnorm 47 (by norm_num) (by norm_num), hnorm 46 (by norm_num) (by norm_num)⟩,
    ⟨hnorm 61 (by norm_num) (by norm_num), hnorm 56 (by norm_num) (by norm_num), hnorm 48 (by norm_num) (by norm_num), hnorm 47 (by norm_num) (by norm_num)⟩,
    ⟨h_sched_full.2.1,
      fun i hi1 _ => by
        simpa only [Fin.val_mk, Nat.sub_add_cancel hi1] using
          h_sched_full.2.2 ⟨i.val - 1, by omega⟩⟩,
    ⟨hst62_norm, hnorm_h0 _, hnorm_h0 _, hE62_bound, hE63_bound⟩,
    ha63_norm,
    (by rw [← CircuitType.eval_var_fields, getElem_eval_vector]; exact hst62_norm ⟨0, by norm_num⟩),
    (by rw [← CircuitType.eval_var_fields, getElem_eval_vector]; exact hst62_norm ⟨1, by norm_num⟩),
    he63_norm,
    (by rw [← CircuitType.eval_var_fields, getElem_eval_vector]; exact hst62_norm ⟨4, by norm_num⟩),
    (by rw [← CircuitType.eval_var_fields, getElem_eval_vector]; exact hst62_norm ⟨5, by norm_num⟩)⟩

def circuit : FormalCircuit (F p) SHA256Block SHA256State := {
  main, elaborated, Assumptions, Spec, soundness
  completeness := by simp only [completeness]
}

end CompressBlock1SparseD
end Solution.SHA256
end
