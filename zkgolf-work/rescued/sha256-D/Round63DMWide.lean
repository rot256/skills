import Solution.SHA256.AddManyWide
import Solution.SHA256.Round63DM
import Challenge.Specs.SHA256
import Challenge.Utils.CostR1CS
import Challenge.Instances.SHA256.Interface

section
variable {p : ℕ} [Fact p.Prime]

namespace Solution.SHA256

variable [Fact (p > 2^35)] [Fact (p > 2^37)]


namespace Round63DMWide

structure Inputs (F : Type) where
  state : SHA256State F
  wide : field F
  s0 : fields 32 F
  s4 : fields 32 F
deriving ProvableStruct

structure Outputs (F : Type) where
  out0 : fields 32 F
  out4 : fields 32 F
deriving ProvableStruct

def main (input : Var Inputs (F p)) : Circuit (F p) (Var Outputs (F p)) := do
  let a := input.state[0]; let b := input.state[1]; let c := input.state[2]
  let d := input.state[3]; let e := input.state[4]; let f := input.state[5]
  let g := input.state[6]; let h := input.state[7]
  let sig1 ← UpperSigma1.circuit e
  let ch   ← Ch32.circuit ⟨e, f, g⟩
  let sig0 ← UpperSigma0.circuit a
  let maj  ← Maj32.circuit ⟨a, b, c⟩
  let k63 := constWord32 (p := p) Round63DM.k63Nat
  -- out4 = s4 + d + h + Σ₁(e) + Ch(e,f,g) + K₆₃ + wide   (mod 2^32)
  let out4 ← subcircuit (AddManyWide.circuit (by norm_num : 6 ≤ 7))
    ⟨#v[input.s4, d, h, sig1, ch, k63], input.wide⟩
  -- out0 = s0 + h + Σ₁(e) + Ch(e,f,g) + K₆₃ + Σ₀(a) + Maj(a,b,c) + wide (mod 2^32)
  let out0 ← subcircuit (AddManyWide.circuit (by norm_num : 7 ≤ 7))
    ⟨#v[input.s0, h, sig1, ch, k63, sig0, maj], input.wide⟩
  return ⟨out0, out4⟩

def Assumptions (input : Inputs (F p)) : Prop :=
  (∀ i : Fin 8, Normalized input.state[i]) ∧ Normalized input.s0 ∧ Normalized input.s4 ∧
    input.wide.val < 2^34

def Spec (input : Inputs (F p)) (out : Outputs (F p)) : Prop :=
  (valueBits out.out0 = _root_.add32 (valueBits input.s0)
    ((Specs.SHA256.sha256Round (input.state.map valueBits)
      (Specs.SHA256.K[63].toNat) (input.wide.val % 2^32))[0]))
  ∧ (valueBits out.out4 = _root_.add32 (valueBits input.s4)
    ((Specs.SHA256.sha256Round (input.state.map valueBits)
      (Specs.SHA256.K[63].toNat) (input.wide.val % 2^32))[4]))
  ∧ Normalized out.out0 ∧ Normalized out.out4

instance elaborated : ElaboratedCircuit (F p) Inputs Outputs main := by
  elaborate_circuit

set_option maxHeartbeats 4000000 in
theorem soundness : Soundness (F p) main Assumptions Spec := by
  circuit_proof_start [UpperSigma1.circuit, UpperSigma0.circuit,
    Ch32.circuit, Maj32.circuit, AddManyWide.circuit]
  obtain ⟨h_state_norm, h_s0_norm, h_s4_norm, h_wide_lt⟩ := h_assumptions
  obtain ⟨h_input_state, -, h_input_s0, h_input_s4⟩ := h_input
  have h_eval : ∀ (i : ℕ) (hi : i < 8),
      Vector.map (Expression.eval env) (input_var_state[i]'hi) = input_state[i]'hi := by
    intro i hi
    have h := getElem_eval_vector env input_var_state i hi
    rw [h_input_state] at h
    rw [← CircuitType.eval_var_fields env (input_var_state[i]'hi)]
    exact h
  simp only [UpperSigma1.Assumptions, UpperSigma0.Assumptions, Ch32.Assumptions,
    Maj32.Assumptions, UpperSigma1.Spec, UpperSigma0.Spec, Ch32.Spec, Maj32.Spec,
    AddManyWide.Assumptions, AddManyWide.Spec, and_imp] at h_holds
  obtain ⟨c_sig1, c_ch, c_sig0, c_maj, c_out4, c_out0⟩ := h_holds
  have s_sig1 := c_sig1 (by rw [h_eval 4 (by omega)]; exact h_state_norm 4)
  have s_ch := c_ch (by rw [h_eval 4 (by omega)]; exact h_state_norm 4)
    (by rw [h_eval 5 (by omega)]; exact h_state_norm 5)
    (by rw [h_eval 6 (by omega)]; exact h_state_norm 6)
  have s_sig0 := c_sig0 (by rw [h_eval 0 (by omega)]; exact h_state_norm 0)
  have s_maj := c_maj (by rw [h_eval 0 (by omega)]; exact h_state_norm 0)
    (by rw [h_eval 1 (by omega)]; exact h_state_norm 1)
    (by rw [h_eval 2 (by omega)]; exact h_state_norm 2)
  have red : ∀ (m : ℕ) (V : ProvableVector (fields 32) m (Expression (F p))) (k : ℕ) (hk : k < m),
      (eval env V)[k]'hk = Vector.map (Expression.eval env) (V[k]'hk) := by
    intro m V k hk
    rw [← getElem_eval_vector env V k hk, CircuitType.eval_var_fields]
  have s_out4 := c_out4 (by
    intro i
    fin_cases i <;>
      (rw [Fin.getElem_fin, red];
        simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
          List.getElem_cons_succ])
    · rw [h_input_s4]; exact h_s4_norm
    · rw [h_eval 3 (by omega)]; exact h_state_norm 3
    · rw [h_eval 7 (by omega)]; exact h_state_norm 7
    · exact s_sig1.2
    · exact s_ch.2
    · exact SHA256Rounds.normalized_constWord32 env _) h_wide_lt
  have s_out0 := c_out0 (by
    intro i
    fin_cases i <;>
      (rw [Fin.getElem_fin, red];
        simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
          List.getElem_cons_succ])
    · rw [h_input_s0]; exact h_s0_norm
    · rw [h_eval 7 (by omega)]; exact h_state_norm 7
    · exact s_sig1.2
    · exact s_ch.2
    · exact SHA256Rounds.normalized_constWord32 env _
    · exact s_sig0.2
    · exact s_maj.2) h_wide_lt
  -- The large subcircuit-constraint hypotheses are fully consumed.
  clear c_sig1 c_ch c_sig0 c_maj c_out4 c_out0
  -- Reassociate the flat modular sums (with the wide addend reduced) into the
  -- spec's nested `add32` shape (pure ℕ): the `% 2^32` on the wide value is
  -- absorbed because `add32` reduces at each step.
  have mod7w : ∀ x0 x1 x2 x3 x4 x5 W : ℕ,
      (x0 + x1 + x2 + x3 + x4 + x5 + W) % 2 ^ 32 =
        _root_.add32 x0 (_root_.add32 x1
          (_root_.add32 (_root_.add32 (_root_.add32 (_root_.add32 x2 x3) x4) x5) (W % 2^32))) := by
    intro x0 x1 x2 x3 x4 x5 W; unfold _root_.add32; omega
  have mod8w : ∀ x0 x1 x2 x3 x4 x5 x6 W : ℕ,
      (x0 + x1 + x2 + x3 + x4 + x5 + x6 + W) % 2 ^ 32 =
        _root_.add32 x0 (_root_.add32
          (_root_.add32 (_root_.add32 (_root_.add32 (_root_.add32 x1 x2) x3) x4) (W % 2^32))
          (_root_.add32 x5 x6)) := by
    intro x0 x1 x2 x3 x4 x5 x6 W; unfold _root_.add32; omega
  obtain ⟨v4, n_out4⟩ := s_out4
  obtain ⟨v0, n_out0⟩ := s_out0
  rw [Fin.sum_univ_six] at v4
  simp only [Fin.getElem_fin, red,
    show ((0:Fin 6):ℕ)=0 from rfl, show ((1:Fin 6):ℕ)=1 from rfl, show ((2:Fin 6):ℕ)=2 from rfl,
    show ((3:Fin 6):ℕ)=3 from rfl, show ((4:Fin 6):ℕ)=4 from rfl, show ((5:Fin 6):ℕ)=5 from rfl,
    Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ] at v4
  rw [s_sig1.1, s_ch.1,
    SHA256Rounds.valueBits_constWord32_of_lt env Round63DM.k63Nat_lt, Round63DM.k63Nat_eq,
    h_eval 3 (by norm_num), h_eval 4 (by norm_num), h_eval 5 (by norm_num),
    h_eval 6 (by norm_num), h_eval 7 (by norm_num), h_input_s4] at v4
  rw [Fin.sum_univ_seven] at v0
  simp only [Fin.getElem_fin, red,
    show ((0:Fin 7):ℕ)=0 from rfl, show ((1:Fin 7):ℕ)=1 from rfl, show ((2:Fin 7):ℕ)=2 from rfl,
    show ((3:Fin 7):ℕ)=3 from rfl, show ((4:Fin 7):ℕ)=4 from rfl, show ((5:Fin 7):ℕ)=5 from rfl,
    show ((6:Fin 7):ℕ)=6 from rfl,
    Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ] at v0
  rw [s_sig1.1, s_ch.1, s_sig0.1, s_maj.1,
    SHA256Rounds.valueBits_constWord32_of_lt env Round63DM.k63Nat_lt, Round63DM.k63Nat_eq,
    h_eval 0 (by norm_num), h_eval 1 (by norm_num), h_eval 2 (by norm_num),
    h_eval 4 (by norm_num), h_eval 5 (by norm_num), h_eval 6 (by norm_num),
    h_eval 7 (by norm_num), h_input_s0] at v0
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [v0, Round63DM.sha256Round_eq, Round63DM.vec8_getElem0]
    simp only [Vector.getElem_map]
    exact mod8w _ _ _ _ _ _ _ _
  · rw [v4, Round63DM.sha256Round_eq, Round63DM.vec8_getElem4]
    simp only [Vector.getElem_map]
    exact mod7w _ _ _ _ _ _ _
  · exact n_out0
  · exact n_out4

set_option maxHeartbeats 4000000 in
theorem completeness : Completeness (F p) main Assumptions := by
  circuit_proof_start [UpperSigma1.circuit, UpperSigma0.circuit,
    Ch32.circuit, Maj32.circuit, AddManyWide.circuit]
  obtain ⟨h_state_norm, h_s0_norm, h_s4_norm, h_wide_lt⟩ := h_assumptions
  obtain ⟨h_input_state, -, h_input_s0, h_input_s4⟩ := h_input
  have h_eval : ∀ (i : ℕ) (hi : i < 8),
      Vector.map (Expression.eval env.toEnvironment) (input_var_state[i]'hi) = input_state[i]'hi := by
    intro i hi
    have h := getElem_eval_vector env.toEnvironment input_var_state i hi
    rw [h_input_state] at h
    rw [← CircuitType.eval_var_fields env.toEnvironment (input_var_state[i]'hi)]
    exact h
  simp only [UpperSigma1.Assumptions, UpperSigma0.Assumptions, Ch32.Assumptions,
    Maj32.Assumptions, UpperSigma1.Spec, UpperSigma0.Spec, Ch32.Spec, Maj32.Spec,
    AddManyWide.Assumptions, AddManyWide.Spec, and_imp] at h_env ⊢
  obtain ⟨e_sig1, e_ch, e_sig0, e_maj, -, -⟩ := h_env
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
  refine ⟨n4, ⟨n4, n5, n6⟩, n0, ⟨n0, n1, n2⟩, ⟨?_, h_wide_lt⟩, ⟨?_, h_wide_lt⟩⟩
  · intro i
    fin_cases i <;>
      (rw [Fin.getElem_fin, red];
        simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
          List.getElem_cons_succ])
    · rw [h_input_s4]; exact h_s4_norm
    · rw [h_eval 3 (by norm_num)]; exact h_state_norm 3
    · rw [h_eval 7 (by norm_num)]; exact h_state_norm 7
    · exact s_sig1.2
    · exact s_ch.2
    · exact SHA256Rounds.normalized_constWord32 _ _
  · intro i
    fin_cases i <;>
      (rw [Fin.getElem_fin, red];
        simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
          List.getElem_cons_succ])
    · rw [h_input_s0]; exact h_s0_norm
    · rw [h_eval 7 (by norm_num)]; exact h_state_norm 7
    · exact s_sig1.2
    · exact s_ch.2
    · exact SHA256Rounds.normalized_constWord32 _ _
    · exact s_sig0.2
    · exact s_maj.2

def circuit : FormalCircuit (F p) Inputs Outputs where
  main; elaborated; Assumptions; Spec; soundness; completeness


section CostLemmas
open Challenge.Instances.SHA256.Interface
open Challenge.CostR1CS

theorem costIs_sub_addManyWide {n : ℕ} (hn : n ≤ 7)
    (b : Var (AddManyWide.Inputs n) (F circomPrime)) :
    CostIs (subcircuit (AddManyWide.circuit hn) b) ⟨35, 36⟩ :=
  CostIs.subcircuit (AddManyWide.costIs_addManyWide hn b.words b.wide)

theorem costIs_main (input : Var Inputs (F circomPrime)) :
    CostIs (main input) ⟨198, 200⟩ :=
  CostIs.bind (Round63DM.costIs_sub_upperSigma1 _) fun _ =>
  CostIs.bind (Round63DM.costIs_sub_ch32 _) fun _ =>
  CostIs.bind (Round63DM.costIs_sub_upperSigma0 _) fun _ =>
  CostIs.bind (Round63DM.costIs_sub_maj32 _) fun _ =>
  CostIs.bind (costIs_sub_addManyWide _ _) fun _ =>
  CostIs.bind (costIs_sub_addManyWide _ _) fun _ => CostIs.pure _

end CostLemmas

end Round63DMWide
end Solution.SHA256
end
