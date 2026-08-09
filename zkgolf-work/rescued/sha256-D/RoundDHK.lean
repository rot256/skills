
import Solution.SHA256.SHA256Round
import Solution.SHA256.SHA256RoundsTheorems
import Solution.SHA256.SHA256Rounds
import Challenge.Specs.SHA256

section
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2^35)]

namespace Solution.SHA256


namespace RoundDHK

structure Params where
  dC : ℕ
  hC : ℕ
  kC : ℕ
  hd : dC < 2^32
  hh : hC < 2^32
  hk : kC < 2^32

def dhkC (P : Params) : ℕ := (P.dC + P.hC + P.kC) % 2^32

lemma dhkC_lt (P : Params) : dhkC P < 2^32 := Nat.mod_lt _ (by norm_num)

lemma mod_dhk (P : Params) (s c wv : ℕ) :
    (dhkC P + s + c + wv) % 2^32 =
      _root_.add32 P.dC
        (_root_.add32 (_root_.add32 (_root_.add32 (_root_.add32 P.hC s) c) P.kC) wv) := by
  unfold dhkC _root_.add32
  omega

def stateWithDH (s : Vector ℕ 8) (dC hC : ℕ) : Vector ℕ 8 :=
  #v[s[0], s[1], s[2], dC, s[4], s[5], s[6], hC]

structure Inputs (F : Type) where
  state : SHA256State F
  w : fields 32 F
deriving ProvableStruct

def main (P : Params) (input : Var Inputs (F p)) :
    Circuit (F p) (Var SHA256State (F p)) := do
  let a := input.state[0]; let b := input.state[1]; let c := input.state[2]
  let e := input.state[4]; let f := input.state[5]; let g := input.state[6]
  let sig1 ← UpperSigma1.circuit e
  let ch   ← Ch32.circuit ⟨e, f, g⟩
  let sig0 ← UpperSigma0.circuit a
  let maj  ← Maj32.circuit ⟨a, b, c⟩
  let new_e ← AddMany.circuit2 (by norm_num) #v[constWord32 (dhkC P), sig1, ch, input.w]
  let new_a ← AddMany.circuit2c (by norm_num)
    #v[new_e, sig0, maj, not32 (constWord32 P.dC)]
  return #v[new_a, a, b, c, new_e, e, f, g]

def Assumptions (input : Inputs (F p)) : Prop :=
  (∀ i : Fin 8, Normalized input.state[i]) ∧ Normalized input.w

def Spec (P : Params) (input : Inputs (F p)) (out : SHA256State (F p)) : Prop :=
  out.map valueBits =
    Specs.SHA256.sha256Round
      (stateWithDH (Vector.map valueBits input.state) P.dC P.hC)
      P.kC (valueBits input.w)
  ∧ ∀ i : Fin 8, Normalized out[i]

instance elaborated (P : Params) : ElaboratedCircuit (F p) Inputs SHA256State (main P) := by
  elaborate_circuit

set_option maxHeartbeats 4000000 in
theorem soundness (P : Params) : Soundness (F p) (main P) Assumptions (Spec P) := by
  circuit_proof_start [main, UpperSigma1.circuit, UpperSigma0.circuit,
    Ch32.circuit, Maj32.circuit, AddMany.circuit2, AddMany.circuit2c]
  obtain ⟨h_state_norm, h_w_norm⟩ := h_assumptions
  obtain ⟨h_input_state, h_input_w⟩ := h_input
  have h_eval : ∀ (i : ℕ) (hi : i < 8),
      Vector.map (Expression.eval env) (input_var_state[i]'hi) = input_state[i]'hi := by
    intro i hi
    have h := getElem_eval_vector env input_var_state i hi
    rw [h_input_state] at h
    rw [← CircuitType.eval_var_fields env (input_var_state[i]'hi)]
    exact h
  simp only [UpperSigma1.Assumptions, UpperSigma0.Assumptions, Ch32.Assumptions,
    Maj32.Assumptions, UpperSigma1.Spec, UpperSigma0.Spec, Ch32.Spec, Maj32.Spec,
    AddMany.Assumptions, AddMany.Spec, AddMany.Spec2c, and_imp] at h_holds
  obtain ⟨c_sig1, c_ch, c_sig0, c_maj, c_newe, c_newa⟩ := h_holds
  have s_sig1 := c_sig1 (by rw [h_eval 4 (by omega)]; exact h_state_norm 4)
  have s_ch := c_ch (by rw [h_eval 4 (by omega)]; exact h_state_norm 4)
    (by rw [h_eval 5 (by omega)]; exact h_state_norm 5) (by rw [h_eval 6 (by omega)]; exact h_state_norm 6)
  have s_sig0 := c_sig0 (by rw [h_eval 0 (by omega)]; exact h_state_norm 0)
  have s_maj := c_maj (by rw [h_eval 0 (by omega)]; exact h_state_norm 0)
    (by rw [h_eval 1 (by omega)]; exact h_state_norm 1) (by rw [h_eval 2 (by omega)]; exact h_state_norm 2)
  have red : ∀ (m : ℕ) (V : ProvableVector (fields 32) m (Expression (F p))) (k : ℕ) (hk : k < m),
      (eval env V)[k]'hk = Vector.map (Expression.eval env) (V[k]'hk) := by
    intro m V k hk
    rw [← getElem_eval_vector env V k hk, CircuitType.eval_var_fields]
  have s_newe := c_newe (by
    intro i
    fin_cases i <;>
      (rw [Fin.getElem_fin, red];
        simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
          List.getElem_cons_succ])
    · exact SHA256Rounds.normalized_constWord32 env _
    · exact s_sig1.2
    · exact s_ch.2
    · rw [h_input_w]; exact h_w_norm)
  have s_newa := c_newa (by
    intro i
    fin_cases i <;>
      (rw [Fin.getElem_fin, red];
        simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
          List.getElem_cons_succ])
    · exact s_newe.2
    · exact s_sig0.2
    · exact s_maj.2
    · rw [SHA256Round.not32_eval env (constWord32 P.dC)]
      exact SHA256Round.normalized_not _ (SHA256Rounds.normalized_constWord32 env _))
  clear c_sig1 c_ch c_sig0 c_maj c_newe c_newa
  -- two's-complement reassociation (as in `SHA256Round.soundness`)
  have modc : ∀ dv t1 y5 y6 : ℕ, dv < 2^32 →
      (_root_.add32 dv t1 + y5 + y6 + (2^32 - 1 - dv) + 1) % 2 ^ 32 =
        _root_.add32 t1 (_root_.add32 y5 y6) := by
    intro dv t1 y5 y6 hdv; unfold _root_.add32; omega
  -- new_e in the spec's nested `add32` shape
  have v_newe : valueBits (Vector.map (Expression.eval env)
        (Vector.mapRange 32 fun i ↦ var { index := i₀ + 32 + 32 + 32 + 32 + i })) =
      _root_.add32 P.dC
        (_root_.add32 (_root_.add32 (_root_.add32 (_root_.add32 P.hC
            (Specs.SHA256.upperSigma1 (valueBits (input_state[4]'(by norm_num)))))
            (Specs.SHA256.Ch (valueBits (input_state[4]'(by norm_num)))
              (valueBits (input_state[5]'(by norm_num))) (valueBits (input_state[6]'(by norm_num)))))
            P.kC) (valueBits input_w)) := by
    rw [s_newe.1, Fin.sum_univ_four]
    simp only [Fin.getElem_fin, red,
      show ((0:Fin 4):ℕ)=0 from rfl, show ((1:Fin 4):ℕ)=1 from rfl, show ((2:Fin 4):ℕ)=2 from rfl,
      show ((3:Fin 4):ℕ)=3 from rfl,
      Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
    rw [SHA256Rounds.valueBits_constWord32_of_lt env (dhkC_lt P),
      s_sig1.1, s_ch.1, h_eval 4 (by norm_num), h_eval 5 (by norm_num), h_eval 6 (by norm_num),
      h_input_w]
    exact mod_dhk P _ _ _
  -- new_a in the spec's nested `add32` shape
  have v_newa : valueBits (Vector.map (Expression.eval env)
        (Vector.mapRange 32 fun i ↦ var { index := i₀ + 32 + 32 + 32 + 32 + 33 + i })) =
      _root_.add32
        (_root_.add32 (_root_.add32 (_root_.add32 (_root_.add32 P.hC
            (Specs.SHA256.upperSigma1 (valueBits (input_state[4]'(by norm_num)))))
            (Specs.SHA256.Ch (valueBits (input_state[4]'(by norm_num)))
              (valueBits (input_state[5]'(by norm_num))) (valueBits (input_state[6]'(by norm_num)))))
            P.kC) (valueBits input_w))
        (_root_.add32 (Specs.SHA256.upperSigma0 (valueBits (input_state[0]'(by norm_num))))
            (Specs.SHA256.Maj (valueBits (input_state[0]'(by norm_num)))
              (valueBits (input_state[1]'(by norm_num))) (valueBits (input_state[2]'(by norm_num))))) := by
    rw [s_newa.1, Fin.sum_univ_four]
    simp only [Fin.getElem_fin, red,
      show ((0:Fin 4):ℕ)=0 from rfl, show ((1:Fin 4):ℕ)=1 from rfl, show ((2:Fin 4):ℕ)=2 from rfl,
      show ((3:Fin 4):ℕ)=3 from rfl,
      Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
    rw [v_newe, s_sig0.1, s_maj.1, h_eval 0 (by norm_num), h_eval 1 (by norm_num),
      h_eval 2 (by norm_num),
      SHA256Round.not32_eval env (constWord32 P.dC),
      SHA256Round.valueBits_not (Vector.map (Expression.eval env) (constWord32 (p:=p) P.dC))
        (SHA256Rounds.normalized_constWord32 env _),
      SHA256Rounds.valueBits_constWord32_of_lt env P.hd]
    exact modc _ _ _ _ P.hd
  have e : ∀ (i : ℕ) (hi : i < 8),
      valueBits (Vector.map (Expression.eval env) (input_var_state[i]'hi)) = valueBits (input_state[i]'hi) :=
    fun i hi => congrArg valueBits (h_eval i hi)
  refine ⟨?_, ?_⟩
  · simp only [eval_vector, Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil,
      circuit_norm]
    rw [show stateWithDH (Vector.map valueBits input_state) P.dC P.hC =
        #v[valueBits (input_state[0]'(by norm_num)), valueBits (input_state[1]'(by norm_num)),
           valueBits (input_state[2]'(by norm_num)), P.dC,
           valueBits (input_state[4]'(by norm_num)), valueBits (input_state[5]'(by norm_num)),
           valueBits (input_state[6]'(by norm_num)), P.hC] from by
      simp only [stateWithDH, Vector.getElem_map]]
    rw [SHA256Rounds.sha256Round_literal]
    obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩ :=
      SHA256Rounds.vec8_get (valueBits (input_state[0]'(by norm_num)))
        (valueBits (input_state[1]'(by norm_num))) (valueBits (input_state[2]'(by norm_num)))
        P.dC (valueBits (input_state[4]'(by norm_num))) (valueBits (input_state[5]'(by norm_num)))
        (valueBits (input_state[6]'(by norm_num))) P.hC
    simp only [g0, g1, g2, g3, g4, g5, g6, g7]
    rw [v_newa, v_newe, e 0 (by norm_num), e 1 (by norm_num), e 2 (by norm_num),
      e 4 (by norm_num), e 5 (by norm_num), e 6 (by norm_num)]
  · intro i
    fin_cases i <;>
      (rw [red];
        simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
          List.getElem_cons_succ])
    · exact s_newa.2
    · rw [h_eval 0 (by norm_num)]; exact h_state_norm 0
    · rw [h_eval 1 (by norm_num)]; exact h_state_norm 1
    · rw [h_eval 2 (by norm_num)]; exact h_state_norm 2
    · exact s_newe.2
    · rw [h_eval 4 (by norm_num)]; exact h_state_norm 4
    · rw [h_eval 5 (by norm_num)]; exact h_state_norm 5
    · rw [h_eval 6 (by norm_num)]; exact h_state_norm 6

set_option maxHeartbeats 4000000 in
theorem completeness (P : Params) : Completeness (F p) (main P) Assumptions := by
  circuit_proof_start [main, UpperSigma1.circuit, UpperSigma0.circuit,
    Ch32.circuit, Maj32.circuit, AddMany.circuit2, AddMany.circuit2c]
  obtain ⟨h_state_norm, h_w_norm⟩ := h_assumptions
  obtain ⟨h_input_state, h_input_w⟩ := h_input
  have h_eval : ∀ (i : ℕ) (hi : i < 8),
      Vector.map (Expression.eval env.toEnvironment) (input_var_state[i]'hi) = input_state[i]'hi := by
    intro i hi
    have h := getElem_eval_vector env.toEnvironment input_var_state i hi
    rw [h_input_state] at h
    rw [← CircuitType.eval_var_fields env.toEnvironment (input_var_state[i]'hi)]
    exact h
  simp only [UpperSigma1.Assumptions, UpperSigma0.Assumptions, Ch32.Assumptions,
    Maj32.Assumptions, UpperSigma1.Spec, UpperSigma0.Spec, Ch32.Spec, Maj32.Spec,
    AddMany.Assumptions, AddMany.Spec, AddMany.Spec2c, and_imp] at h_env ⊢
  obtain ⟨e_sig1, e_ch, e_sig0, e_maj, e_newe, -⟩ := h_env
  have red : ∀ (m : ℕ) (V : ProvableVector (fields 32) m (Expression (F p))) (k : ℕ) (hk : k < m),
      (eval env.toEnvironment V)[k]'hk = Vector.map (Expression.eval env.toEnvironment) (V[k]'hk) := by
    intro m V k hk
    rw [← getElem_eval_vector env.toEnvironment V k hk, CircuitType.eval_var_fields]
  have n0 : Normalized (Vector.map (Expression.eval env.toEnvironment) input_var_state[0]) := by
    rw [h_eval 0 (by norm_num)]; exact h_state_norm 0
  have n1 : Normalized (Vector.map (Expression.eval env.toEnvironment) input_var_state[1]) := by
    rw [h_eval 1 (by norm_num)]; exact h_state_norm 1
  have n2 : Normalized (Vector.map (Expression.eval env.toEnvironment) input_var_state[2]) := by
    rw [h_eval 2 (by norm_num)]; exact h_state_norm 2
  have n4 : Normalized (Vector.map (Expression.eval env.toEnvironment) input_var_state[4]) := by
    rw [h_eval 4 (by norm_num)]; exact h_state_norm 4
  have n5 : Normalized (Vector.map (Expression.eval env.toEnvironment) input_var_state[5]) := by
    rw [h_eval 5 (by norm_num)]; exact h_state_norm 5
  have n6 : Normalized (Vector.map (Expression.eval env.toEnvironment) input_var_state[6]) := by
    rw [h_eval 6 (by norm_num)]; exact h_state_norm 6
  have s_sig1 := e_sig1 n4
  have s_ch := e_ch n4 n5 n6
  have s_sig0 := e_sig0 n0
  have s_maj := e_maj n0 n1 n2
  have s_newe := e_newe (by
    intro i
    fin_cases i <;>
      (rw [Fin.getElem_fin, red];
        simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
          List.getElem_cons_succ])
    · exact SHA256Rounds.normalized_constWord32 env.toEnvironment _
    · exact s_sig1.2
    · exact s_ch.2
    · rw [h_input_w]; exact h_w_norm)
  refine ⟨n4, ⟨n4, n5, n6⟩, n0, ⟨n0, n1, n2⟩, ?_, ?_⟩
  · intro i
    fin_cases i <;>
      (rw [Fin.getElem_fin, red];
        simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
          List.getElem_cons_succ])
    · exact SHA256Rounds.normalized_constWord32 env.toEnvironment _
    · exact s_sig1.2
    · exact s_ch.2
    · rw [h_input_w]; exact h_w_norm
  · intro i
    fin_cases i <;>
      (rw [Fin.getElem_fin, red];
        simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
          List.getElem_cons_succ])
    · exact s_newe.2
    · exact s_sig0.2
    · exact s_maj.2
    · rw [SHA256Round.not32_eval env.toEnvironment (constWord32 P.dC)]
      exact SHA256Round.normalized_not _ (SHA256Rounds.normalized_constWord32 env.toEnvironment _)

def circuit (P : Params) : FormalCircuit (F p) Inputs SHA256State where
  main := main P
  elaborated := elaborated P
  Assumptions := Assumptions
  Spec := Spec P
  soundness := soundness P
  completeness := completeness P


def params2 : Params :=
  ⟨0xbb67ae85, 0x9b05688c, 0xb5c0fbcf, by norm_num, by norm_num, by norm_num⟩

def params3 : Params :=
  ⟨0x6a09e667, 0x510e527f, 0xe9b5dba5, by norm_num, by norm_num, by norm_num⟩

lemma params2_dC_eq : params2.dC = Specs.SHA256.H0[1] := by decide
lemma params2_hC_eq : params2.hC = Specs.SHA256.H0[5] := by decide
lemma params2_kC_eq : params2.kC = (Specs.SHA256.K[2]).toNat := by decide
lemma params3_dC_eq : params3.dC = Specs.SHA256.H0[0] := by decide
lemma params3_hC_eq : params3.hC = Specs.SHA256.H0[4] := by decide
lemma params3_kC_eq : params3.kC = (Specs.SHA256.K[3]).toNat := by decide

end RoundDHK
end Solution.SHA256
end
