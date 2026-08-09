import Solution.SHA256.SelectDigest
import Solution.SHA256.FusedAdders
import Solution.SHA256.CarrySumAdd32
import Solution.SHA256.SHA256RoundPair
import Solution.SHA256.Sparse32

/-!
# Digest selection with two deferred state words

State words 3 and 7 arrive **unreduced** (they are the raw Merkle–Damgård sums, below
`6 * 2^32`).  The selector therefore reduces those two words here — once for the whole
hash instead of once per block, which is what makes the deferral profitable.
-/

section
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2^35)] [Fact (p > 2^76)] [Fact (p > 2^120)]

namespace Solution.SHA256
namespace SelectDigestD

open Challenge.Instances.SHA256.Interface (inputBufferLen)
open SelectDigest (statesVec groupFlagSum eval_groupFlagSum stateForLen_map stateForLen_mem
  valueBits_lt val_fieldFromBits)

abbrev Inputs := SelectDigest.Inputs

/-- the six words that arrive already reduced -/
def idx6 : Fin 6 → Fin 8
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 4
  | 4 => 5
  | 5 => 6

/-- the value each deferred word must be reduced against -/
def dvec (input : Var Inputs (F p)) (d6 : Var (fields 6) (F p))
    (b3 b7 : Var (fields 32) (F p)) (c3 c7 : Var (fields 3) (F p)) :
    Var (fields 8) (F p) :=
  #v[d6[0], d6[1], d6[2],
     fromBitsExpr b3 + ((2^32 : F p) : Expression (F p)) * RPShared.carryE c3,
     d6[3], d6[4], d6[5],
     fromBitsExpr b7 + ((2^32 : F p) : Expression (F p)) * RPShared.carryE c7]

def selWord (input : Inputs (F p)) (w : Fin 8) : ℕ :=
  valueBits ((stateForLen (statesVec input) input.messageLen.val)[w.val]'w.isLt)

def main (input : Var Inputs (F p)) : Circuit (F p) (Var (fields 8) (F p)) := do
  let d6 ← witnessVector 6 fun env =>
    Vector.ofFn fun (j : Fin 6) =>
      env (fromBitsExpr (stateForLen (statesVec input) (env input.messageLen).val)[(idx6 j).val])
  let b3 ← witnessVector 32 fun env =>
    RPShared.witBits (selWord (eval env input) 3)
  let b7 ← witnessVector 32 fun env =>
    RPShared.witBits (selWord (eval env input) 7)
  let c3 ← witnessVector 3 fun env =>
    Vector.ofFn fun (j : Fin 3) =>
      (((selWord (eval env input) 3) / 2^32 / 2^j.val % 2 : ℕ) : F p)
  let c7 ← witnessVector 3 fun env =>
    Vector.ofFn fun (j : Fin 3) =>
      (((selWord (eval env input) 7) / 2^32 / 2^j.val % 2 : ℕ) : F p)
  BoolVec32.circuit b3
  BoolVec32.circuit b7
  Circuit.forEach (Vector.finRange 3) fun i => assertZero (c3[i] * (c3[i] - 1))
  Circuit.forEach (Vector.finRange 3) fun i => assertZero (c7[i] * (c7[i] - 1))
  Circuit.forEach (Vector.finRange paddedBlocksLen) fun g =>
    Circuit.forEach (Vector.finRange 8) fun w =>
      assertZero (groupFlagSum input.lenFlags g *
        (fromBitsExpr (statesVec input)[g][w] - (dvec input d6 b3 b7 c3 c7)[w]))
  return #v[d6[0], d6[1], d6[2], fromBitsExpr b3, d6[3], d6[4], d6[5], fromBitsExpr b7]

def Assumptions (input : Inputs (F p)) : Prop :=
  input.messageLen.val < inputBufferLen ∧
  OneHotAt input.lenFlags input.messageLen.val ∧
  (∀ k : Fin paddedBlocksLen, ∀ i : Fin 8, i.val ≠ 3 → i.val ≠ 7 →
    Normalized (statesVec input)[k][i]) ∧
  (∀ k : Fin paddedBlocksLen, valueBits (statesVec input)[k][3] < 6 * 2^32) ∧
  (∀ k : Fin paddedBlocksLen, valueBits (statesVec input)[k][7] < 6 * 2^32)

def Spec (input : Inputs (F p)) (out : fields 8 (F p)) : Prop :=
  ∀ w : Fin 8, out[w].val =
    valueBits ((stateForLen (statesVec input) input.messageLen.val)[w]) % 2^32

@[reducible] instance elaborated : ElaboratedCircuit (F p) Inputs (fields 8) main := by
  elaborate_circuit

lemma reduce_of_field_eq {A B C : ℕ} (hA : A < 6 * 2^32) (hB : B < 2^32) (hC : C ≤ 7)
    (h : ((A : ℕ) : F p) = ((B + 2^32 * C : ℕ) : F p)) : B = A % 2^32 := by
  have hp : (2:ℕ)^35 < p := Fact.out
  have e32 : (2:ℕ)^32 = 4294967296 := by norm_num
  have e35 : (2:ℕ)^35 = 34359738368 := by norm_num
  have hAp : A < p := by rw [e32] at hA; rw [e35] at hp; omega
  have hBp : B + 2^32 * C < p := by rw [e32] at hB ⊢; rw [e35] at hp; omega
  have := congrArg ZMod.val h
  rw [ZMod.val_natCast_of_lt hAp, ZMod.val_natCast_of_lt hBp] at this
  rw [e32] at hB this ⊢
  omega

lemma fieldFromBits_cast (w : Vector (F p) 32) :
    Utils.Bits.fieldFromBits w = ((valueBits w : ℕ) : F p) := by
  have hsum : Utils.Bits.fromBits (w.map ZMod.val) = valueBits w := by
    unfold Utils.Bits.fromBits valueBits
    rw [Fin.foldl_to_sum 32 (fun i : Fin 32 => (w.map ZMod.val)[i.val] * 2 ^ i.val)]
    apply Finset.sum_congr rfl
    intro i _
    rw [Vector.getElem_map]
    rfl
  unfold Utils.Bits.fieldFromBits
  rw [hsum]

set_option maxHeartbeats 4000000 in
theorem soundness : Soundness (F p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨h_len, h_onehot, h_norm, hbd3, hbd7⟩ := h_assumptions
  obtain ⟨h_msg, h_flags, h_s1, h_s2, h_s3, h_s4, h_s5⟩ := h_input
  obtain ⟨c_b3, c_b7, c_c3, c_c7, c_rows⟩ := h_holds
  refine ⟨?_, Or.inl rfl, Or.inl rfl⟩
  intro w
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
  set g : Fin paddedBlocksLen := ⟨numBlocksForLen ℓ - 1, by omega⟩ with hg
  have hsum : Expression.eval env (groupFlagSum input_var_lenFlags g) = 1 := by
    rw [eval_groupFlagSum env input_var_lenFlags input_lenFlags h_flags ℓ h_len h_onehot g,
      if_pos (show numBlocksForLen ℓ = numBlocksForLen ℓ - 1 + 1 by omega)]
  -- state bridging
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
  have hword : ∀ (u : Fin 8), ((statesVec varRec)[g.val]'g.isLt)[u.val].map (Expression.eval env) =
      ((statesVec valRec)[g.val]'g.isLt)[u.val] := by
    intro u
    have hsv : (statesVec varRec).map (fun st => st.map (Vector.map (Expression.eval env)))
        = statesVec valRec := by
      simp only [statesVec, hvarRec, hvalRec, Vector.map_mk, List.map_toArray, List.map_cons,
        List.map_nil, e1, e2, e3, e4, e5]
    have h1 := congrArg
      (fun v : Vector (SHA256State (F p)) paddedBlocksLen => v[g.val]'g.isLt) hsv
    simp only [Vector.getElem_map] at h1
    have h2 := congrArg (fun st : SHA256State (F p) => st[u.val]'u.isLt) h1
    simp only [Vector.getElem_map] at h2
    exact h2
  -- the row for word `u`
  have hrow : ∀ (u : Fin 8),
      ((valueBits (((statesVec valRec)[g.val]'g.isLt)[u.val]) : ℕ) : F p)
        = Expression.eval env ((dvec varRec
            (Vector.mapRange 6 fun i => var { index := i₀ + i })
            (Vector.mapRange 32 fun i => var { index := i₀ + 6 + i })
            (Vector.mapRange 32 fun i => var { index := i₀ + 6 + 32 + i })
            (Vector.mapRange 3 fun i => var { index := i₀ + 6 + 32 + 32 + i })
            (Vector.mapRange 3 fun i => var { index := i₀ + 6 + 32 + 32 + 3 + i }))[u.val]) := by
    intro u
    have h0 := c_rows g u
    simp only [hsum, one_mul] at h0
    have := add_neg_eq_zero.mp h0
    rw [← this]
    simp only [fromBitsExpr, Utils.Bits.fieldFromBits_eval, hword u, fieldFromBits_cast]
  -- carry values
  obtain ⟨hC3, hC3le⟩ := RPShared.carry_facts env (i₀ + 6 + 32 + 32) c_c3
  obtain ⟨hC7, hC7le⟩ := RPShared.carry_facts env (i₀ + 6 + 32 + 32 + 3) c_c7
  set C3 : ℕ := (env.get (i₀ + 6 + 32 + 32 + 0)).val + 2 * (env.get (i₀ + 6 + 32 + 32 + 1)).val
    + 4 * (env.get (i₀ + 6 + 32 + 32 + 2)).val with hC3def
  set C7 : ℕ := (env.get (i₀ + 6 + 32 + 32 + 3 + 0)).val + 2 * (env.get (i₀ + 6 + 32 + 32 + 3 + 1)).val
    + 4 * (env.get (i₀ + 6 + 32 + 32 + 3 + 2)).val with hC7def
  have hb3n : Normalized (Vector.map (Expression.eval env)
      (Vector.mapRange 32 fun i => var { index := i₀ + 6 + i })) := c_b3 trivial
  have hb7n : Normalized (Vector.map (Expression.eval env)
      (Vector.mapRange 32 fun i => var { index := i₀ + 6 + 32 + i })) := c_b7 trivial
  rw [stateForLen_eq _ _ (le_of_lt h_len)]
  have hgidx : (statesVec valRec)[numBlocksForLen ℓ - 1]'(by omega)
      = (statesVec valRec)[g.val]'g.isLt := rfl
  rw [hgidx]
  -- case on the word
  obtain ⟨wv, hwv⟩ := w
  have hcases : wv = 0 ∨ wv = 1 ∨ wv = 2 ∨ wv = 3 ∨ wv = 4 ∨ wv = 5 ∨ wv = 6 ∨ wv = 7 := by omega
  have hplain : ∀ (u : Fin 8) (j : ℕ),
      u.val ≠ 3 → u.val ≠ 7 →
      Expression.eval env ((dvec varRec
          (Vector.mapRange 6 fun i => var { index := i₀ + i })
          (Vector.mapRange 32 fun i => var { index := i₀ + 6 + i })
          (Vector.mapRange 32 fun i => var { index := i₀ + 6 + 32 + i })
          (Vector.mapRange 3 fun i => var { index := i₀ + 6 + 32 + 32 + i })
          (Vector.mapRange 3 fun i => var { index := i₀ + 6 + 32 + 32 + 3 + i }))[u.val])
        = env.get (i₀ + j) →
      ZMod.val (env.get (i₀ + j))
        = valueBits (((statesVec valRec)[g.val]'g.isLt)[u.val]) % 2^32 := by
    intro u j hu3 hu7 hd
    rw [← hd, ← hrow u]
    have hn := h_norm g u hu3 hu7
    have hlt : valueBits (((statesVec valRec)[g.val]'g.isLt)[u.val]) < 2^32 :=
      valueBits_lt_two_pow _ hn
    have hp : (2:ℕ)^35 < p := Fact.out
    have e32 : (2:ℕ)^32 = 4294967296 := by norm_num
    have e35 : (2:ℕ)^35 = 34359738368 := by norm_num
    rw [ZMod.val_natCast_of_lt (by rw [e32] at hlt; rw [e35] at hp; omega),
      Nat.mod_eq_of_lt hlt]
  have hdef : ∀ (u : Fin 8) (B : Var (fields 32) (F p)) (C : ℕ),
      Expression.eval env ((dvec varRec
          (Vector.mapRange 6 fun i => var { index := i₀ + i })
          (Vector.mapRange 32 fun i => var { index := i₀ + 6 + i })
          (Vector.mapRange 32 fun i => var { index := i₀ + 6 + 32 + i })
          (Vector.mapRange 3 fun i => var { index := i₀ + 6 + 32 + 32 + i })
          (Vector.mapRange 3 fun i => var { index := i₀ + 6 + 32 + 32 + 3 + i }))[u.val])
        = Expression.eval env (fromBitsExpr B) + ((2^32 : F p)) * (C : F p) →
      Normalized (Vector.map (Expression.eval env) B) →
      C ≤ 7 →
      valueBits (((statesVec valRec)[g.val]'g.isLt)[u.val]) < 6 * 2^32 →
      ZMod.val (Expression.eval env (fromBitsExpr B))
        = valueBits (((statesVec valRec)[g.val]'g.isLt)[u.val]) % 2^32 := by
    intro u B C hd hBn hCle hAlt
    have hBval : Expression.eval env (fromBitsExpr B)
        = ((valueBits (Vector.map (Expression.eval env) B) : ℕ) : F p) := by
      simp only [fromBitsExpr, Utils.Bits.fieldFromBits_eval, fieldFromBits_cast]
    have hBlt : valueBits (Vector.map (Expression.eval env) B) < 2^32 :=
      valueBits_lt_two_pow _ hBn
    have hfield := hrow u
    rw [hd, hBval] at hfield
    have hcast : ((valueBits (Vector.map (Expression.eval env) B) + 2^32 * C : ℕ) : F p)
        = ((valueBits (Vector.map (Expression.eval env) B) : ℕ) : F p) + (2^32 : F p) * (C : F p) := by
      push_cast; ring
    rw [← hcast] at hfield
    have hred := reduce_of_field_eq hAlt hBlt hCle hfield
    rw [hBval]
    have hp : (2:ℕ)^35 < p := Fact.out
    have e32 : (2:ℕ)^32 = 4294967296 := by norm_num
    have e35 : (2:ℕ)^35 = 34359738368 := by norm_num
    rw [ZMod.val_natCast_of_lt (by rw [e32] at hBlt; rw [e35] at hp; omega)]
    exact hred
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hplain ⟨0, by norm_num⟩ 0 (by norm_num) (by norm_num) rfl
  · exact hplain ⟨1, by norm_num⟩ 1 (by norm_num) (by norm_num) rfl
  · exact hplain ⟨2, by norm_num⟩ 2 (by norm_num) (by norm_num) rfl
  · refine hdef ⟨3, by norm_num⟩ _ C3 ?_ hb3n hC3le (hbd3 g)
    show Expression.eval env (fromBitsExpr (Vector.mapRange 32 fun i => var { index := i₀ + 6 + i }))
        + (2^32 : F p) *
          Expression.eval env
            (RPShared.carryE (Vector.mapRange 3 fun i => var { index := i₀ + 6 + 32 + 32 + i })) = _
    rw [hC3]
  · exact hplain ⟨4, by norm_num⟩ 3 (by norm_num) (by norm_num) rfl
  · exact hplain ⟨5, by norm_num⟩ 4 (by norm_num) (by norm_num) rfl
  · exact hplain ⟨6, by norm_num⟩ 5 (by norm_num) (by norm_num) rfl
  · refine hdef ⟨7, by norm_num⟩ _ C7 ?_ hb7n hC7le (hbd7 g)
    show Expression.eval env (fromBitsExpr (Vector.mapRange 32 fun i => var { index := i₀ + 6 + 32 + i }))
        + (2^32 : F p) *
          Expression.eval env
            (RPShared.carryE (Vector.mapRange 3 fun i => var { index := i₀ + 6 + 32 + 32 + 3 + i })) = _
    rw [hC7]

set_option maxHeartbeats 4000000 in
theorem completeness : Completeness (F p) main Assumptions := by
  circuit_proof_start
  obtain ⟨h_len, h_onehot, h_norm, hbd3, hbd7⟩ := h_assumptions
  obtain ⟨h_msg, h_flags, h_s1, h_s2, h_s3, h_s4, h_s5⟩ := h_input
  obtain ⟨e_d6, e_b3, e_b7, e_c3, e_c7, -⟩ := h_env
  set varRec : Inputs (Expression (F p)) :=
    { messageLen := input_var_messageLen, lenFlags := input_var_lenFlags,
      s1 := input_var_s1, s2 := input_var_s2, s3 := input_var_s3,
      s4 := input_var_s4, s5 := input_var_s5 } with hvarRec
  set valRec : Inputs (F p) :=
    { messageLen := input_messageLen, lenFlags := input_lenFlags,
      s1 := input_s1, s2 := input_s2, s3 := input_s3, s4 := input_s4, s5 := input_s5 } with hvalRec
  set ℓ := ZMod.val input_messageLen with hℓ
  have hml : ZMod.val valRec.messageLen = ℓ := rfl
  have hword : ∀ (k : Fin paddedBlocksLen) (u : Fin 8),
      ((statesVec varRec)[k.val]'k.isLt)[u.val].map (Expression.eval env.toEnvironment) =
        ((statesVec valRec)[k.val]'k.isLt)[u.val] := by
    intro k u
    have estate : ∀ (sv : SHA256State (Expression (F p))) (s : SHA256State (F p)),
        eval env.toEnvironment sv = s → sv.map (Vector.map (Expression.eval env.toEnvironment)) = s := by
      intro sv s h
      rw [← h, eval_vector]
      apply Vector.ext
      intro i hi
      rw [Vector.getElem_map, Vector.getElem_map, CircuitType.eval_var_fields]
    have hsv : (statesVec varRec).map (fun st => st.map (Vector.map (Expression.eval env.toEnvironment)))
        = statesVec valRec := by
      simp only [statesVec, hvarRec, hvalRec, Vector.map_mk, List.map_toArray, List.map_cons,
        List.map_nil, estate _ _ h_s1, estate _ _ h_s2, estate _ _ h_s3, estate _ _ h_s4,
        estate _ _ h_s5]
    have h1 := congrArg
      (fun v : Vector (SHA256State (F p)) paddedBlocksLen => v[k.val]'k.isLt) hsv
    simp only [Vector.getElem_map] at h1
    have h2 := congrArg (fun st : SHA256State (F p) => st[u.val]'u.isLt) h1
    simp only [Vector.getElem_map] at h2
    exact h2
  -- the witnessed bit vectors
  have hb3 : Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange 32 fun i => var { index := i₀ + 6 + i })
      = RPShared.witBits (selWord valRec 3) := by
    apply Vector.ext
    intro i hi
    rw [Vector.getElem_map, Vector.getElem_mapRange]
    exact e_b3 ⟨i, hi⟩
  have hb7 : Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange 32 fun i => var { index := i₀ + 6 + 32 + i })
      = RPShared.witBits (selWord valRec 7) := by
    apply Vector.ext
    intro i hi
    rw [Vector.getElem_map, Vector.getElem_mapRange]
    exact e_b7 ⟨i, hi⟩
  have hcarry : ∀ (A : ℕ) (O : ℕ), A < 6 * 2^32 →
      (∀ i : Fin 3, env.get (O + i.val) = ((A / 2^32 / 2^i.val % 2 : ℕ) : F p)) →
      Expression.eval env.toEnvironment
          (RPShared.carryE (Vector.mapRange 3 fun i => var { index := O + i }))
        = ((A / 2^32 : ℕ) : F p) := by
    intro A O hA hc
    refine RPShared.carry_recompose env.toEnvironment O A ?_ hc
    have e32 : (2:ℕ)^32 = 4294967296 := by norm_num
    rw [e32] at hA ⊢
    omega
  refine ⟨⟨trivial, ?_⟩, ⟨trivial, ?_⟩, ?_, ?_, ?_⟩
  · rw [hb3]; exact SHA256RoundPair.witBits_normalized _
  · rw [hb7]; exact SHA256RoundPair.witBits_normalized _
  · intro i
    have h := e_c3 i
    rw [show (Vector.ofFn fun j : Fin 3 =>
        ((selWord valRec 3 / 2^32 / 2^j.val % 2 : ℕ) : F p))[i.val] =
        ((selWord valRec 3 / 2^32 / 2^i.val % 2 : ℕ) : F p) from by
      rw [Vector.getElem_ofFn]] at h
    rw [h]
    rcases Nat.mod_two_eq_zero_or_one (selWord valRec 3 / 2^32 / 2^i.val) with h0 | h0 <;>
      rw [h0] <;> push_cast <;> ring
  · intro i
    have h := e_c7 i
    rw [show (Vector.ofFn fun j : Fin 3 =>
        ((selWord valRec 7 / 2^32 / 2^j.val % 2 : ℕ) : F p))[i.val] =
        ((selWord valRec 7 / 2^32 / 2^i.val % 2 : ℕ) : F p) from by
      rw [Vector.getElem_ofFn]] at h
    rw [h]
    rcases Nat.mod_two_eq_zero_or_one (selWord valRec 7 / 2^32 / 2^i.val) with h0 | h0 <;>
      rw [h0] <;> push_cast <;> ring
  · intro gg w
    by_cases hcase : numBlocksForLen ℓ = gg.val + 1
    · -- the active group
      have hpos := numBlocksForLen_pos ℓ
      have hidx : numBlocksForLen ℓ - 1 = gg.val := by omega
      have hsel : stateForLen (statesVec varRec) ℓ = (statesVec varRec)[gg.val]'gg.isLt := by
        rw [stateForLen_eq _ _ (le_of_lt h_len)]
        simp only [hidx]
      have hselv : stateForLen (statesVec valRec) ℓ = (statesVec valRec)[gg.val]'gg.isLt := by
        rw [stateForLen_eq _ _ (le_of_lt h_len)]
        simp only [hidx]
      have hd : ∀ (u : Fin 8),
          Expression.eval env.toEnvironment
              (fromBitsExpr (statesVec varRec)[gg.val][u.val])
            = Expression.eval env.toEnvironment
              ((dvec varRec
                (Vector.mapRange 6 fun i => var { index := i₀ + i })
                (Vector.mapRange 32 fun i => var { index := i₀ + 6 + i })
                (Vector.mapRange 32 fun i => var { index := i₀ + 6 + 32 + i })
                (Vector.mapRange 3 fun i => var { index := i₀ + 6 + 32 + 32 + i })
                (Vector.mapRange 3 fun i => var { index := i₀ + 6 + 32 + 32 + 3 + i }))[u.val]) := by
        intro u
        obtain ⟨uv, huv⟩ := u
        have hcases : uv = 0 ∨ uv = 1 ∨ uv = 2 ∨ uv = 3 ∨ uv = 4 ∨ uv = 5 ∨ uv = 6 ∨ uv = 7 := by
          omega
        have hd6 : ∀ (j : Fin 6), env.get (i₀ + j.val)
            = Expression.eval env.toEnvironment
                (fromBitsExpr (stateForLen (statesVec varRec) ℓ)[(idx6 j).val]) := by
          intro j
          have h := e_d6 j
          rw [Vector.getElem_ofFn] at h
          exact h
        have hsp : ∀ (A : ℕ) (B : Var (fields 32) (F p)) (O : ℕ),
            A < 6 * 2^32 →
            Vector.map (Expression.eval env.toEnvironment) B = RPShared.witBits A →
            (∀ i : Fin 3, env.get (O + i.val) = ((A / 2^32 / 2^i.val % 2 : ℕ) : F p)) →
            Expression.eval env.toEnvironment (fromBitsExpr B)
              + (2^32 : F p) * Expression.eval env.toEnvironment
                  (RPShared.carryE (Vector.mapRange 3 fun i => var { index := O + i }))
              = ((A : ℕ) : F p) := by
          intro A B O hA hB hc
          rw [hcarry A O hA hc]
          have : Expression.eval env.toEnvironment (fromBitsExpr B)
              = ((A % 2^32 : ℕ) : F p) := by
            simp only [fromBitsExpr, Utils.Bits.fieldFromBits_eval, fieldFromBits_cast, hB,
              SHA256RoundPair.valueBits_witBits]
          rw [this]
          have hnat : A % 2^32 + 2^32 * (A / 2^32) = A := by omega
          have := congrArg (Nat.cast (R := F p)) hnat
          push_cast at this ⊢
          linear_combination this
        rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · rw [← hsel]; exact (hd6 0).symm
        · rw [← hsel]; exact (hd6 1).symm
        · rw [← hsel]; exact (hd6 2).symm
        · show _ = Expression.eval env.toEnvironment (fromBitsExpr
              (Vector.mapRange 32 fun i => var { index := i₀ + 6 + i }))
              + (2^32 : F p) * Expression.eval env.toEnvironment
                (RPShared.carryE (Vector.mapRange 3 fun i => var { index := i₀ + 6 + 32 + 32 + i }))
          rw [hsp (selWord valRec 3) _ (i₀ + 6 + 32 + 32)
            (by simpa only [selWord, hml, hselv] using hbd3 gg) hb3
            (fun i => by
              have h := e_c3 i
              rw [Vector.getElem_ofFn] at h
              exact h)]
          simp only [selWord, hml, hselv, fromBitsExpr, Utils.Bits.fieldFromBits_eval,
            fieldFromBits_cast, hword gg ⟨3, by norm_num⟩]
          rfl
        · rw [← hsel]; exact (hd6 3).symm
        · rw [← hsel]; exact (hd6 4).symm
        · rw [← hsel]; exact (hd6 5).symm
        · show _ = Expression.eval env.toEnvironment (fromBitsExpr
              (Vector.mapRange 32 fun i => var { index := i₀ + 6 + 32 + i }))
              + (2^32 : F p) * Expression.eval env.toEnvironment
                (RPShared.carryE (Vector.mapRange 3 fun i =>
                  var { index := i₀ + 6 + 32 + 32 + 3 + i }))
          rw [hsp (selWord valRec 7) _ (i₀ + 6 + 32 + 32 + 3)
            (by simpa only [selWord, hml, hselv] using hbd7 gg) hb7
            (fun i => by
              have h := e_c7 i
              rw [Vector.getElem_ofFn] at h
              exact h)]
          simp only [selWord, hml, hselv, fromBitsExpr, Utils.Bits.fieldFromBits_eval,
            fieldFromBits_cast, hword gg ⟨7, by norm_num⟩]
          rfl
      rw [hd w]
      ring
    · have hzero : Expression.eval env.toEnvironment (groupFlagSum input_var_lenFlags gg) = 0 := by
        rw [eval_groupFlagSum env.toEnvironment input_var_lenFlags input_lenFlags h_flags
          ℓ h_len h_onehot gg, if_neg hcase]
      rw [hzero, zero_mul]

def circuit : FormalCircuit (F p) Inputs (fields 8) where
  main; elaborated; Assumptions; Spec; soundness; completeness

lemma circuit_Assumptions_eq : (circuit (p := p)).Assumptions = Assumptions := rfl

lemma circuit_Spec_eq : (circuit (p := p)).Spec = Spec := rfl

end SelectDigestD
end Solution.SHA256
end
