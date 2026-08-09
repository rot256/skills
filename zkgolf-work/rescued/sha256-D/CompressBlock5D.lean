import Solution.SHA256.SHA256RoundsW
import Solution.SHA256.MainTheorems
import Solution.SHA256.TailPairWide
import Solution.SHA256.TailPairTight
import Solution.SHA256.CarrySumAdd32
import Solution.SHA256.Sparse32
import Solution.SHA256.DeferredSpec
import Challenge.Specs.SHA256

namespace Solution.SHA256

open Challenge.Instances.SHA256.Interface (inputBufferLen circomPrime)
open Utils.Bits (fieldFromBitsExpr)

namespace CompressBlock5D

structure Inputs (F : Type) where
  messageLen : F
  lenFlags : fields inputBufferLen F
  state : SHA256State F
deriving ProvableStruct

def main (input : Var Inputs (F circomPrime)) :
    Circuit (F circomPrime) (Var SHA256State (F circomPrime)) := do
  let sched := block5Schedule input.lenFlags
  let st62 ← SHA256Rounds63.circuit62_pairedW ⟨input.state, sched⟩
  let o ← TailPairTight.circuit ⟨st62, fieldFromBitsExpr sched[62], fieldFromBitsExpr sched[63],
    input.state[0], input.state[4]⟩
  let r1 ← CarrySumAdd32.circuit ⟨input.state[1], o.a63⟩
  let r2 ← CarrySumAdd32.circuit ⟨input.state[2], st62[0]⟩
  let r3 ← DeferAdd.circuit ⟨input.state[3], st62[1]⟩
  let r5 ← CarrySumAdd32.circuit ⟨input.state[5], o.e63⟩
  let r6 ← CarrySumAdd32.circuit ⟨input.state[6], st62[4]⟩
  let r7 ← DeferAdd.circuit ⟨input.state[7], st62[5]⟩
  return #v[o.out0, r1, r2, r3, o.out4, r5, r6, r7]

instance elaborated : ElaboratedCircuit (F circomPrime) Inputs SHA256State main := by
  elaborate_circuit

def Assumptions (input : Inputs (F circomPrime)) : Prop :=
  input.messageLen.val < inputBufferLen ∧
  OneHotAt input.lenFlags input.messageLen.val ∧
  (∀ i : Fin 8, i.val ≠ 3 → i.val ≠ 7 → Normalized input.state[i]) ∧
  RPShared.Numeric5W input.state[3] ∧ RPShared.Numeric5W input.state[7]

def Spec (input : Inputs (F circomPrime)) (out : SHA256State (F circomPrime)) : Prop :=
  out.map valueBits =
    Deferred.compressBlockD (input.state.map valueBits)
      (block5SpecBlock input.messageLen.val)
  ∧ ∀ i : Fin 8, i.val ≠ 3 → i.val ≠ 7 → Normalized out[i]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem soundness : Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [SHA256Rounds63.Spec62, SHA256Rounds63.Assumptions62PairedW,
    TailPairTight.Spec, TailPairTight.Assumptions,
    CarrySumAdd32.circuit, CarrySumAdd32.Spec, CarrySumAdd32.Assumptions,
    DeferAdd.circuit, DeferAdd.Spec, DeferAdd.Assumptions]
  all_goals try exact Or.inl rfl
  obtain ⟨h_len, h_onehot, h_state_norm, h_q3, h_q7⟩ := h_assumptions
  obtain ⟨h_msgLen_eq, h_flags_eq, h_state_eq⟩ := h_input
  obtain ⟨h_st62, h_o, h_a1, h_a2, h_a3, h_a5, h_a6, h_a7⟩ := h_holds
  set ℓ := input_messageLen.val with hℓ
  have h_onehot' : OneHotAt (Vector.map (Expression.eval env) input_var_lenFlags) ℓ := by
    rw [h_flags_eq]; exact h_onehot
  have red : ∀ (m : ℕ) (V : ProvableVector (fields 32) m (Expression (F circomPrime))) (k : ℕ) (hk : k < m),
      (eval env V)[k]'hk = Vector.map (Expression.eval env) (V[k]'hk) := by
    intro m V k hk
    rw [← getElem_eval_vector env V k hk, CircuitType.eval_var_fields]
  have h_eval : ∀ (i : ℕ) (hi : i < 8),
      Vector.map (Expression.eval env) (input_var_state[i]'hi) = input_state[i]'hi := by
    intro i hi
    rw [← red 8 input_var_state i hi, h_state_eq]
  have h_sched_map : Vector.map valueBits (eval env (block5Schedule input_var_lenFlags)) =
      Specs.SHA256.messageSchedule (block5SpecBlock ℓ) := by
    have h := block5Schedule_value env input_var_lenFlags (Vector.replicate inputBufferLen 0) ℓ h_len h_onehot'
    rwa [← block5SpecBlock_eq_specBlock (Vector.replicate inputBufferLen 0) ℓ] at h
  have hval : ∀ (j : ℕ) (hj : j < 64),
      valueBits (Vector.map (Expression.eval env) ((block5Schedule input_var_lenFlags)[j]'hj)) =
        (Specs.SHA256.messageSchedule (block5SpecBlock ℓ))[j]'hj := by
    intro j hj
    rw [← red 64 (block5Schedule input_var_lenFlags) j hj, ← h_sched_map, Vector.getElem_map]
  have hnorm : ∀ (j : ℕ) (hj : j < 64),
      Normalized (Vector.map (Expression.eval env) ((block5Schedule input_var_lenFlags)[j]'hj)) := by
    intro j hj
    have h := block5Schedule_normalized env input_var_lenFlags ℓ h_len h_onehot' j hj
    rwa [CircuitType.eval_var_fields] at h
  -- wide words (rounds 62/63 schedule words), directly from the reduced bits
  have hw0 : (Expression.eval env (fieldFromBitsExpr ((block5Schedule input_var_lenFlags)[62]'(by norm_num)))).val =
      (Specs.SHA256.messageSchedule (block5SpecBlock ℓ))[62]'(by norm_num) := by
    rw [Add32.fromBitsExpr_val_eq env _ _ rfl (hnorm 62 (by norm_num)) (by norm_num [circomPrime])]
    exact hval 62 (by norm_num)
  have hw1 : (Expression.eval env (fieldFromBitsExpr ((block5Schedule input_var_lenFlags)[63]'(by norm_num)))).val =
      (Specs.SHA256.messageSchedule (block5SpecBlock ℓ))[63]'(by norm_num) := by
    rw [Add32.fromBitsExpr_val_eq env _ _ rfl (hnorm 63 (by norm_num)) (by norm_num [circomPrime])]
    exact hval 63 (by norm_num)
  have hw0_lt : (Specs.SHA256.messageSchedule (block5SpecBlock ℓ))[62]'(by norm_num) < 2^32 := by
    rw [← hval 62 (by norm_num)]; exact valueBits_lt_two_pow _ (hnorm 62 (by norm_num))
  have hw1_lt : (Specs.SHA256.messageSchedule (block5SpecBlock ℓ))[63]'(by norm_num) < 2^32 := by
    rw [← hval 63 (by norm_num)]; exact valueBits_lt_two_pow _ (hnorm 63 (by norm_num))
  have hw0_bound : (Expression.eval env (fieldFromBitsExpr ((block5Schedule input_var_lenFlags)[62]'(by norm_num)))).val < 2^32 := by
    rw [hw0]; exact hw0_lt
  have hw1_bound : (Expression.eval env (fieldFromBitsExpr ((block5Schedule input_var_lenFlags)[63]'(by norm_num)))).val < 2^32 := by
    rw [hw1]; exact hw1_lt
  have hw0_mod : (Expression.eval env (fieldFromBitsExpr ((block5Schedule input_var_lenFlags)[62]'(by norm_num)))).val % 2^32 =
      (Specs.SHA256.messageSchedule (block5SpecBlock ℓ))[62]'(by norm_num) := by
    rw [hw0]; exact Nat.mod_eq_of_lt hw0_lt
  have hw1_mod : (Expression.eval env (fieldFromBitsExpr ((block5Schedule input_var_lenFlags)[63]'(by norm_num)))).val % 2^32 =
      (Specs.SHA256.messageSchedule (block5SpecBlock ℓ))[63]'(by norm_num) := by
    rw [hw1]; exact Nat.mod_eq_of_lt hw1_lt
  -- rounds 0..61 (paired)
  obtain ⟨hst62_val, hst62_norm⟩ := h_st62 ⟨h_state_norm, h_q3, h_q7,
    (by
      have h := hnorm 0 (by norm_num)
      rw [← red 64 (block5Schedule input_var_lenFlags) 0 (by norm_num)] at h
      exact h.numeric32),
    fun i _ hi => by
    have h := hnorm i.val i.isLt
    rw [← red 64 (block5Schedule input_var_lenFlags) i.val i.isLt] at h
    exact h⟩
  rw [h_sched_map] at hst62_val
  have hs0n : Normalized (Vector.map (Expression.eval env) input_var_state[0]) := by
    rw [h_eval 0 (by norm_num)]; exact h_state_norm 0 (by norm_num) (by norm_num)
  have hs4n : Normalized (Vector.map (Expression.eval env) input_var_state[4]) := by
    rw [h_eval 4 (by norm_num)]; exact h_state_norm 4 (by norm_num) (by norm_num)
  obtain ⟨ha63_val, he63_val, ho_v0, ho_v4, ho_n0, ho_n4, ha63_norm, he63_norm⟩ :=
    h_o ⟨hst62_norm, hs0n, hs4n, hw0_bound, hw1_bound⟩
  rw [TailPairTight.specSt63_eq, hst62_val, hw0_mod] at ha63_val he63_val
  rw [TailPairTight.specSt64_eq, hst62_val, hw0_mod, hw1_mod,
    ← SHA256Rounds.sha256Compress_split_last2 (Vector.map valueBits input_state)
      (Specs.SHA256.messageSchedule (block5SpecBlock ℓ))] at ho_v0 ho_v4
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
  have hL62 : ∀ (b : SHA256Rounds63.Inputs (Expression (F circomPrime))),
      SHA256Rounds63.circuit62_pairedW.localLength b = 10170 := fun b => by
    simp only [circuit_norm, SHA256Rounds63.circuit62_pairedW,
      SHA256Rounds63.elaborated62_pairedW]
  have hL331 : ∀ (b : TailPairTight.Inputs (Expression (F circomPrime))),
      TailPairTight.circuit.localLength b = 329 := fun b => by
    simp only [circuit_norm, TailPairTight.circuit, TailPairTight.elaborated]
  have hTPo0 : ∀ (a : TailPairTight.Inputs (Expression (F circomPrime))) (n : ℕ),
      (TailPairTight.circuit.output a n).out0 = Vector.mapRange 32 (fun i => var { index := n + 128 + 32 + 32 + 32 + i }) := fun a n => by
    simp only [circuit_norm, TailPairTight.circuit, TailPairTight.elaborated]
  have hTPo4 : ∀ (a : TailPairTight.Inputs (Expression (F circomPrime))) (n : ℕ),
      (TailPairTight.circuit.output a n).out4 = Vector.mapRange 32 (fun i => var { index := n + 128 + 32 + 32 + i }) := fun a n => by
    simp only [circuit_norm, TailPairTight.circuit, TailPairTight.elaborated]
  have hTPa63 : ∀ (a : TailPairTight.Inputs (Expression (F circomPrime))) (n : ℕ),
      (TailPairTight.circuit.output a n).a63 = Vector.mapRange 32 (fun i => var { index := n + 32 + 32 + 32 + i }) := fun a n => by
    simp only [circuit_norm, TailPairTight.circuit, TailPairTight.elaborated]
  have hTPe63 : ∀ (a : TailPairTight.Inputs (Expression (F circomPrime))) (n : ℕ),
      (TailPairTight.circuit.output a n).e63 = Vector.mapRange 32 (fun i => var { index := n + 32 + 32 + i }) := fun a n => by
    simp only [circuit_norm, TailPairTight.circuit, TailPairTight.elaborated]
  have hAdd32o : ∀ (a : CarrySumAdd32.Inputs (Expression (F circomPrime))) (n : ℕ),
      CarrySumAdd32.circuit.output a n = Vector.mapRange 32 (fun i => var { index := n + i }) := fun a n => by
    simp only [circuit_norm, CarrySumAdd32.circuit, CarrySumAdd32.elaborated]
  simp only [hL62, hL331, hTPo0, hTPo4, hTPa63, hTPe63, hAdd32o] at ho_v0 ho_v4 ha63_val he63_val ha1_val ha2_val ha3_val ha5_val ha6_val ha7_val ho_n0 ho_n4 ha63_norm he63_norm ha1_norm ha2_norm ha5_norm ha6_norm
  simp only [← CircuitType.eval_var_fields] at ho_v0 ho_v4 ha63_val he63_val ha1_val ha2_val ha3_val ha5_val ha6_val ha7_val
  rw [ha63_val] at ha1_val
  rw [he63_val] at ha5_val
  refine ⟨⟨?_, ?_⟩, ?_⟩
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
  · repeat' first | exact Or.inl rfl | refine ⟨?_, ?_⟩

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem completeness : Completeness (F circomPrime) main Assumptions := by
  circuit_proof_start [SHA256Rounds63.Spec62, SHA256Rounds63.Assumptions62PairedW,
    TailPairTight.Spec, TailPairTight.Assumptions,
    CarrySumAdd32.circuit, CarrySumAdd32.Spec, CarrySumAdd32.Assumptions,
    DeferAdd.circuit, DeferAdd.Spec, DeferAdd.Assumptions]
  obtain ⟨h_len, h_onehot, h_state_norm, h_q3, h_q7⟩ := h_assumptions
  obtain ⟨h_msgLen_eq, h_flags_eq, h_state_eq⟩ := h_input
  obtain ⟨h_st62_impl, h_o_impl, _⟩ := h_env
  set ℓ := input_messageLen.val with hℓ
  have h_onehot' : OneHotAt (Vector.map (Expression.eval env.toEnvironment) input_var_lenFlags) ℓ := by
    rw [h_flags_eq]; exact h_onehot
  have red : ∀ (m : ℕ) (V : ProvableVector (fields 32) m (Expression (F circomPrime))) (k : ℕ) (hk : k < m),
      (eval env.toEnvironment V)[k]'hk = Vector.map (Expression.eval env.toEnvironment) (V[k]'hk) := by
    intro m V k hk
    rw [← getElem_eval_vector env.toEnvironment V k hk, CircuitType.eval_var_fields]
  have h_eval : ∀ (i : ℕ) (hi : i < 8),
      Vector.map (Expression.eval env.toEnvironment) (input_var_state[i]'hi) = input_state[i]'hi := by
    intro i hi
    rw [← red 8 input_var_state i hi, h_state_eq]
  have hnorm : ∀ (j : ℕ) (hj : j < 64),
      Normalized (Vector.map (Expression.eval env.toEnvironment) ((block5Schedule input_var_lenFlags)[j]'hj)) := by
    intro j hj
    have h := block5Schedule_normalized env.toEnvironment input_var_lenFlags ℓ h_len h_onehot' j hj
    rwa [CircuitType.eval_var_fields] at h
  have hw0_bound : (Expression.eval env.toEnvironment (fieldFromBitsExpr ((block5Schedule input_var_lenFlags)[62]'(by norm_num)))).val < 2^32 := by
    rw [Add32.fromBitsExpr_val_eq env.toEnvironment _ _ rfl (hnorm 62 (by norm_num)) (by norm_num [circomPrime])]
    exact valueBits_lt_two_pow _ (hnorm 62 (by norm_num))
  have hw1_bound : (Expression.eval env.toEnvironment (fieldFromBitsExpr ((block5Schedule input_var_lenFlags)[63]'(by norm_num)))).val < 2^32 := by
    rw [Add32.fromBitsExpr_val_eq env.toEnvironment _ _ rfl (hnorm 63 (by norm_num)) (by norm_num [circomPrime])]
    exact valueBits_lt_two_pow _ (hnorm 63 (by norm_num))
  obtain ⟨_, hst62_norm⟩ := h_st62_impl ⟨h_state_norm, h_q3, h_q7,
    (by
      have h := hnorm 0 (by norm_num)
      rw [← red 64 (block5Schedule input_var_lenFlags) 0 (by norm_num)] at h
      exact h.numeric32),
    fun i _ hi => by
    have h := hnorm i.val i.isLt
    rw [← red 64 (block5Schedule input_var_lenFlags) i.val i.isLt] at h
    exact h⟩
  have hs0n : Normalized (Vector.map (Expression.eval env.toEnvironment) input_var_state[0]) := by
    rw [h_eval 0 (by norm_num)]; exact h_state_norm 0 (by norm_num) (by norm_num)
  have hs4n : Normalized (Vector.map (Expression.eval env.toEnvironment) input_var_state[4]) := by
    rw [h_eval 4 (by norm_num)]; exact h_state_norm 4 (by norm_num) (by norm_num)
  obtain ⟨_, _, _, _, _, _, ha63_norm, he63_norm⟩ :=
    h_o_impl ⟨hst62_norm, hs0n, hs4n, hw0_bound, hw1_bound⟩
  refine ⟨⟨h_state_norm, h_q3, h_q7,
      (by
        have h := hnorm 0 (by norm_num)
        rw [← red 64 (block5Schedule input_var_lenFlags) 0 (by norm_num)] at h
        exact h.numeric32),
      fun i _ hi => by
      have h := hnorm i.val i.isLt
      rw [← red 64 (block5Schedule input_var_lenFlags) i.val i.isLt] at h
      exact h⟩,
    ⟨hst62_norm, hs0n, hs4n, hw0_bound, hw1_bound⟩,
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

def circuit : FormalCircuit (F circomPrime) Inputs SHA256State := {
  main, elaborated, Assumptions, Spec, soundness
  completeness := by simp only [completeness]
}

end CompressBlock5D
end Solution.SHA256
