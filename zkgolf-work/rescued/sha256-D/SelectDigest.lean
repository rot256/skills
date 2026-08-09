import Solution.SHA256.PaddingTheorems
import Solution.SHA256.BitwiseOps


section
variable {p : ℕ} [Fact p.Prime] [h_large : Fact (p > 2^33)]

namespace Solution.SHA256
namespace SelectDigest


lemma stateForLen_map {α β : Type} (f : α → β)
    (v : Vector α paddedBlocksLen) (len : ℕ) :
    stateForLen (v.map f) len = f (stateForLen v len) := by
  unfold stateForLen
  split <;> simp [Vector.getElem_map]

lemma stateForLen_mem {α : Type} (v : Vector α paddedBlocksLen) (len : ℕ) :
    ∃ k : Fin paddedBlocksLen, stateForLen v len = v[k] := by
  unfold stateForLen
  split
  · exact ⟨⟨0, by norm_num⟩, rfl⟩
  · exact ⟨⟨1, by norm_num⟩, rfl⟩
  · exact ⟨⟨2, by norm_num⟩, rfl⟩
  · exact ⟨⟨3, by norm_num⟩, rfl⟩
  · exact ⟨⟨4, by norm_num⟩, rfl⟩

omit h_large in
lemma valueBits_lt (w : Vector (F p) 32) (h : Normalized w) :
    valueBits w < 2^32 := by
  unfold valueBits
  have hle : ∀ i : Fin 32, w[i].val ≤ 1 := by
    intro i
    rcases h i with hw | hw <;> rw [hw]
    · simp [ZMod.val_zero]
    · simp [ZMod.val_one]
  have := sum_bool_lt_two_pow 32 (fun i : Fin 32 => w[i].val) hle
  simpa using this

lemma val_fieldFromBits (w : Vector (F p) 32) (h : Normalized w) :
    (Utils.Bits.fieldFromBits w).val = valueBits w := by
  have hsum : Utils.Bits.fromBits (w.map ZMod.val) = valueBits w := by
    unfold Utils.Bits.fromBits valueBits
    rw [Fin.foldl_to_sum 32 (fun i : Fin 32 => (w.map ZMod.val)[i.val] * 2 ^ i.val)]
    apply Finset.sum_congr rfl
    intro i _
    rw [Vector.getElem_map]
    rfl
  have hcast : Utils.Bits.fieldFromBits w = ((valueBits w : ℕ) : F p) := by
    unfold Utils.Bits.fieldFromBits
    rw [hsum]
  rw [hcast]
  have hlt : valueBits w < p := by
    have h32 : (2:ℕ)^32 < 2^33 := by norm_num
    exact lt_trans (lt_trans (valueBits_lt w h) h32) h_large.out
  exact ZMod.val_natCast_of_lt hlt

end SelectDigest
end Solution.SHA256
end


section
variable {p : ℕ} [Fact p.Prime] [h_large : Fact (p > 2^33)]

namespace Solution.SHA256
namespace SelectDigest

open Challenge.Instances.SHA256.Interface (inputBufferLen)

structure Inputs (F : Type) where
  messageLen : F
  lenFlags : fields inputBufferLen F
  s1 : SHA256State F
  s2 : SHA256State F
  s3 : SHA256State F
  s4 : SHA256State F
  s5 : SHA256State F
deriving ProvableStruct

def statesVec {F : Type} (input : Inputs F) : Vector (SHA256State F) paddedBlocksLen :=
  #v[input.s1, input.s2, input.s3, input.s4, input.s5]

def groupFlagSum (lenFlags : Var (fields inputBufferLen) (F p))
    (g : Fin paddedBlocksLen) : Expression (F p) :=
  Fin.foldl inputBufferLen
    (fun acc len =>
      acc + (if numBlocksForLen len.val = g.val + 1 then lenFlags[len] else 0))
    0

def main (input : Var Inputs (F p)) : Circuit (F p) (Var (fields 8) (F p)) := do
  let digest ← witnessVector 8 fun env =>
    Vector.ofFn fun (w : Fin 8) =>
      env (fromBitsExpr (stateForLen (statesVec input) (env input.messageLen).val)[w])
  Circuit.forEach (Vector.finRange paddedBlocksLen) fun g =>
    Circuit.forEach (Vector.finRange 8) fun w =>
      assertZero (groupFlagSum input.lenFlags g *
        (fromBitsExpr (statesVec input)[g][w] - digest[w]))
  return digest

def Assumptions (input : Inputs (F p)) : Prop :=
  input.messageLen.val < inputBufferLen ∧
  OneHotAt input.lenFlags input.messageLen.val ∧
  (∀ k : Fin paddedBlocksLen, ∀ i : Fin 8, Normalized (statesVec input)[k][i])

def Spec (input : Inputs (F p)) (out : fields 8 (F p)) : Prop :=
  ∀ w : Fin 8, out[w].val = valueBits ((stateForLen (statesVec input) input.messageLen.val)[w])

@[reducible] instance elaborated : ElaboratedCircuit (F p) Inputs (fields 8) main := by
  elaborate_circuit


omit h_large in
lemma eval_groupFlagSum (env : Environment (F p))
    (lenFlags : Var (fields inputBufferLen) (F p)) (flags : Vector (F p) inputBufferLen)
    (hf : Vector.map (Expression.eval env) lenFlags = flags)
    (ℓ : ℕ) (hℓ : ℓ < inputBufferLen) (hone : OneHotAt flags ℓ) (g : Fin paddedBlocksLen) :
    Expression.eval env (groupFlagSum lenFlags g)
      = if numBlocksForLen ℓ = g.val + 1 then 1 else 0 := by
  rw [groupFlagSum, eval_finFoldl_add]
  have hterm : ∀ len : Fin inputBufferLen,
      Expression.eval env
          (if numBlocksForLen len.val = g.val + 1 then lenFlags[len] else 0)
        = if len = (⟨ℓ, hℓ⟩ : Fin inputBufferLen)
            then (if numBlocksForLen ℓ = g.val + 1 then 1 else 0) else 0 := by
    intro len
    have hfl : Expression.eval env lenFlags[len] = flags[len] := by
      rw [← hf]; simp [Vector.getElem_map]
    have hval := hone len
    by_cases hlen : len = (⟨ℓ, hℓ⟩ : Fin inputBufferLen)
    · subst hlen
      rw [if_pos rfl]
      rw [if_pos rfl] at hval
      by_cases hg : numBlocksForLen ℓ = g.val + 1
      · rw [if_pos hg, if_pos (by simpa using hg), hfl, hval]
      · rw [if_neg hg, if_neg (by simpa using hg)]
        rfl
    · rw [if_neg hlen]
      have hne : ¬ len.val = ℓ := by
        intro hc; exact hlen (Fin.ext hc)
      rw [if_neg hne] at hval
      split
      · rw [hfl, hval]
      · rfl
  rw [Finset.sum_congr rfl fun len _ => hterm len]
  rw [Finset.sum_ite_eq' Finset.univ (⟨ℓ, hℓ⟩ : Fin inputBufferLen)]
  rw [if_pos (Finset.mem_univ _)]

theorem soundness : Soundness (F p) main Assumptions Spec := by
  circuit_proof_start
  intro w
  obtain ⟨h_len, h_onehot, h_norm⟩ := h_assumptions
  obtain ⟨h_msg, h_flags, h_s1, h_s2, h_s3, h_s4, h_s5⟩ := h_input
  set varRec : Inputs (Expression (F p)) :=
    { messageLen := input_var_messageLen, lenFlags := input_var_lenFlags,
      s1 := input_var_s1, s2 := input_var_s2, s3 := input_var_s3,
      s4 := input_var_s4, s5 := input_var_s5 } with hvarRec
  set valRec : Inputs (F p) :=
    { messageLen := input_messageLen, lenFlags := input_lenFlags,
      s1 := input_s1, s2 := input_s2, s3 := input_s3, s4 := input_s4, s5 := input_s5 } with hvalRec
  set ℓ := ZMod.val input_messageLen with hℓ
  have hpos := numBlocksForLen_pos ℓ
  have hle := numBlocksForLen_le (le_of_lt h_len)
  -- The assert at ℓ's candidate group pins the digest word to the selected word:
  -- its group flag sum evaluates to `1` by one-hotness.
  set g : Fin paddedBlocksLen := ⟨numBlocksForLen ℓ - 1, by omega⟩ with hg
  have h0 := h_holds g w
  have hsum : Expression.eval env (groupFlagSum input_var_lenFlags g) = 1 := by
    rw [eval_groupFlagSum env input_var_lenFlags input_lenFlags h_flags ℓ h_len h_onehot g,
      if_pos (show numBlocksForLen ℓ = numBlocksForLen ℓ - 1 + 1 by omega)]
  rw [hsum, one_mul] at h0
  rw [← add_neg_eq_zero.mp h0]
  -- each state variable evaluates (componentwise) to its value
  have estate : ∀ (sv : SHA256State (Expression (F p))) (s : SHA256State (F p)),
      eval env sv = s → sv.map (Vector.map (Expression.eval env)) = s := by
    intro sv s h
    rw [← h, eval_vector]
    apply Vector.ext
    intro i hi
    rw [Vector.getElem_map, Vector.getElem_map, CircuitType.eval_var_fields]
  have e1 := estate _ _ h_s1
  have e2 := estate _ _ h_s2
  have e3 := estate _ _ h_s3
  have e4 := estate _ _ h_s4
  have e5 := estate _ _ h_s5
  -- Bridge: candidate `g`'s word at the variable level evaluates to the value level.
  have hword : ((statesVec varRec)[g.val]'g.isLt)[w.val].map (Expression.eval env) =
      ((statesVec valRec)[g.val]'g.isLt)[w.val] := by
    have hsv : (statesVec varRec).map (fun st => st.map (Vector.map (Expression.eval env)))
        = statesVec valRec := by
      simp only [statesVec, hvarRec, hvalRec, Vector.map_mk, List.map_toArray, List.map_cons,
        List.map_nil, e1, e2, e3, e4, e5]
    have h1 := congrArg
      (fun v : Vector (SHA256State (F p)) paddedBlocksLen => v[g.val]'g.isLt) hsv
    simp only [Vector.getElem_map] at h1
    have h2 := congrArg (fun st : SHA256State (F p) => st[w.val]'w.isLt) h1
    simp only [Vector.getElem_map] at h2
    exact h2
  simp only [fromBitsExpr, Utils.Bits.fieldFromBits_eval, hword]
  -- The spec's `stateForLen` picks exactly candidate `g`.
  rw [stateForLen_eq _ _ (le_of_lt h_len)]
  exact val_fieldFromBits _ (h_norm g w)

omit h_large in
theorem completeness : Completeness (F p) main Assumptions := by
  circuit_proof_start
  obtain ⟨h_len, h_onehot, h_norm⟩ := h_assumptions
  obtain ⟨h_msg, h_flags, h_s1, h_s2, h_s3, h_s4, h_s5⟩ := h_input
  intro g w
  set varRec : Inputs (Expression (F p)) :=
    { messageLen := input_var_messageLen, lenFlags := input_var_lenFlags,
      s1 := input_var_s1, s2 := input_var_s2, s3 := input_var_s3,
      s4 := input_var_s4, s5 := input_var_s5 } with hvarRec
  by_cases hcase : numBlocksForLen (ZMod.val input_messageLen) = g.val + 1
  · -- the digest witness equals candidate `g`'s word: the second factor vanishes
    have hpos := numBlocksForLen_pos (ZMod.val input_messageLen)
    have hidx : numBlocksForLen (ZMod.val input_messageLen) - 1 = g.val := by omega
    have hsel : stateForLen (statesVec varRec) (ZMod.val input_messageLen)
        = (statesVec varRec)[g.val]'g.isLt := by
      rw [stateForLen_eq _ _ (le_of_lt h_len)]
      simp only [hidx]
    have hd := h_env w
    simp only [Vector.getElem_ofFn, hsel] at hd
    rw [hd]
    simp only [Fin.eta]
    ring
  · -- off the true candidate the group flag sum is zero: the first factor vanishes
    have hzero : Expression.eval env.toEnvironment
        (groupFlagSum input_var_lenFlags g) = 0 := by
      rw [eval_groupFlagSum env.toEnvironment input_var_lenFlags input_lenFlags h_flags
        (ZMod.val input_messageLen) h_len h_onehot g, if_neg hcase]
    rw [hzero, zero_mul]

def circuit : FormalCircuit (F p) Inputs (fields 8) where
  main; elaborated; Assumptions; Spec; soundness; completeness

lemma circuit_Assumptions_eq : (circuit (p := p)).Assumptions = Assumptions := rfl

lemma circuit_Spec_eq : (circuit (p := p)).Spec = Spec := rfl

lemma circuit_output_eq (input : Var Inputs (F p)) (n : ℕ) :
    (circuit (p := p)).output input n = Vector.mapRange 8 fun i => var { index := n + i } := rfl

end SelectDigest
end Solution.SHA256
end
