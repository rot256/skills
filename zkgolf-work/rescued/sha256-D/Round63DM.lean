import Solution.SHA256.AddMany
import Solution.SHA256.Ch32
import Solution.SHA256.Maj32
import Solution.SHA256.UpperSigma0
import Solution.SHA256.UpperSigma1
import Solution.SHA256.SHA256RoundsTheorems
import Challenge.Specs.SHA256
import Challenge.Utils.CostR1CS
import Challenge.Instances.SHA256.Interface

section
variable {p : ℕ} [Fact p.Prime]

namespace Solution.SHA256

variable [Fact (p > 2^35)]


namespace Round63DM

structure Inputs (F : Type) where
  state : SHA256State F
  w : fields 32 F
  s0 : fields 32 F
  s4 : fields 32 F
deriving ProvableStruct

structure Outputs (F : Type) where
  out0 : fields 32 F
  out4 : fields 32 F
deriving ProvableStruct

def k63Nat : ℕ := 0xc67178f2

lemma k63Nat_eq : k63Nat = Specs.SHA256.K[63].toNat := by decide

lemma k63Nat_lt : k63Nat < 2^32 := by norm_num [k63Nat]

def main (input : Var Inputs (F p)) : Circuit (F p) (Var Outputs (F p)) := do
  let a := input.state[0]; let b := input.state[1]; let c := input.state[2]
  let d := input.state[3]; let e := input.state[4]; let f := input.state[5]
  let g := input.state[6]; let h := input.state[7]
  let sig1 ← UpperSigma1.circuit e
  let ch   ← Ch32.circuit ⟨e, f, g⟩
  let sig0 ← UpperSigma0.circuit a
  let maj  ← Maj32.circuit ⟨a, b, c⟩
  let k63 := constWord32 (p := p) k63Nat
  -- out4 = s4 + new_e = s4 + d + h + Σ₁(e) + Ch(e,f,g) + K₆₃ + w   (mod 2^32)
  let out4 ← AddMany.circuit (by norm_num) #v[input.s4, d, h, sig1, ch, k63, input.w]
  -- out0 = s0 + new_a = s0 + t1 + t2
  --      = s0 + h + Σ₁(e) + Ch(e,f,g) + K₆₃ + w + Σ₀(a) + Maj(a,b,c)   (mod 2^32)
  let out0 ← AddMany.circuit (by norm_num) #v[input.s0, h, sig1, ch, k63, input.w, sig0, maj]
  return ⟨out0, out4⟩

def Assumptions (input : Inputs (F p)) : Prop :=
  (∀ i : Fin 8, Normalized input.state[i]) ∧ Normalized input.w ∧
    Normalized input.s0 ∧ Normalized input.s4

def Spec (input : Inputs (F p)) (out : Outputs (F p)) : Prop :=
  (valueBits out.out0 = _root_.add32 (valueBits input.s0)
    ((Specs.SHA256.sha256Round (input.state.map valueBits)
      (Specs.SHA256.K[63].toNat) (valueBits input.w))[0]))
  ∧ (valueBits out.out4 = _root_.add32 (valueBits input.s4)
    ((Specs.SHA256.sha256Round (input.state.map valueBits)
      (Specs.SHA256.K[63].toNat) (valueBits input.w))[4]))
  ∧ Normalized out.out0 ∧ Normalized out.out4

instance elaborated : ElaboratedCircuit (F p) Inputs Outputs main := by
  elaborate_circuit


lemma sha256Round_eq (s : Vector ℕ 8) (k w : ℕ) :
    Specs.SHA256.sha256Round s k w =
      #v[_root_.add32
           (_root_.add32 (_root_.add32 (_root_.add32 (_root_.add32 s[7]
             (Specs.SHA256.upperSigma1 s[4])) (Specs.SHA256.Ch s[4] s[5] s[6])) k) w)
           (_root_.add32 (Specs.SHA256.upperSigma0 s[0]) (Specs.SHA256.Maj s[0] s[1] s[2])),
         s[0], s[1], s[2],
         _root_.add32 s[3]
           (_root_.add32 (_root_.add32 (_root_.add32 (_root_.add32 s[7]
             (Specs.SHA256.upperSigma1 s[4])) (Specs.SHA256.Ch s[4] s[5] s[6])) k) w),
         s[4], s[5], s[6]] := rfl

lemma vec8_getElem0 (x0 x1 x2 x3 x4 x5 x6 x7 : ℕ) :
    (#v[x0, x1, x2, x3, x4, x5, x6, x7] : Vector ℕ 8)[0] = x0 := rfl

lemma vec8_getElem4 (x0 x1 x2 x3 x4 x5 x6 x7 : ℕ) :
    (#v[x0, x1, x2, x3, x4, x5, x6, x7] : Vector ℕ 8)[4] = x4 := rfl

lemma vec8_getElem1 (x0 x1 x2 x3 x4 x5 x6 x7 : ℕ) :
    (#v[x0, x1, x2, x3, x4, x5, x6, x7] : Vector ℕ 8)[1] = x1 := rfl

lemma vec8_getElem2 (x0 x1 x2 x3 x4 x5 x6 x7 : ℕ) :
    (#v[x0, x1, x2, x3, x4, x5, x6, x7] : Vector ℕ 8)[2] = x2 := rfl

lemma vec8_getElem3 (x0 x1 x2 x3 x4 x5 x6 x7 : ℕ) :
    (#v[x0, x1, x2, x3, x4, x5, x6, x7] : Vector ℕ 8)[3] = x3 := rfl

lemma vec8_getElem5 (x0 x1 x2 x3 x4 x5 x6 x7 : ℕ) :
    (#v[x0, x1, x2, x3, x4, x5, x6, x7] : Vector ℕ 8)[5] = x5 := rfl

lemma vec8_getElem6 (x0 x1 x2 x3 x4 x5 x6 x7 : ℕ) :
    (#v[x0, x1, x2, x3, x4, x5, x6, x7] : Vector ℕ 8)[6] = x6 := rfl

lemma vec8_getElem7 (x0 x1 x2 x3 x4 x5 x6 x7 : ℕ) :
    (#v[x0, x1, x2, x3, x4, x5, x6, x7] : Vector ℕ 8)[7] = x7 := rfl

set_option maxHeartbeats 4000000 in
theorem soundness : Soundness (F p) main Assumptions Spec := by
  circuit_proof_start [UpperSigma1.circuit, UpperSigma0.circuit,
    Ch32.circuit, Maj32.circuit, AddMany.circuit]
  obtain ⟨h_state_norm, h_w_norm, h_s0_norm, h_s4_norm⟩ := h_assumptions
  obtain ⟨h_input_state, h_input_w, h_input_s0, h_input_s4⟩ := h_input
  have h_eval : ∀ (i : ℕ) (hi : i < 8),
      Vector.map (Expression.eval env) (input_var_state[i]'hi) = input_state[i]'hi := by
    intro i hi
    have h := getElem_eval_vector env input_var_state i hi
    rw [h_input_state] at h
    rw [← CircuitType.eval_var_fields env (input_var_state[i]'hi)]
    exact h
  simp only [UpperSigma1.Assumptions, UpperSigma0.Assumptions, Ch32.Assumptions,
    Maj32.Assumptions, UpperSigma1.Spec, UpperSigma0.Spec, Ch32.Spec, Maj32.Spec,
    AddMany.Assumptions, AddMany.Spec, and_imp] at h_holds
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
    · exact SHA256Rounds.normalized_constWord32 env _
    · rw [h_input_w]; exact h_w_norm)
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
    · rw [h_input_w]; exact h_w_norm
    · exact s_sig0.2
    · exact s_maj.2)
  -- The large subcircuit-constraint hypotheses are fully consumed.
  clear c_sig1 c_ch c_sig0 c_maj c_out4 c_out0
  -- Reassociate the flat modular sums into the spec's nested `add32` shape (pure ℕ).
  have mod7 : ∀ x0 x1 x2 x3 x4 x5 x6 : ℕ,
      (x0 + x1 + x2 + x3 + x4 + x5 + x6) % 2 ^ 32 =
        _root_.add32 x0 (_root_.add32 x1
          (_root_.add32 (_root_.add32 (_root_.add32 (_root_.add32 x2 x3) x4) x5) x6)) := by
    intro x0 x1 x2 x3 x4 x5 x6; unfold _root_.add32; omega
  have mod8 : ∀ x0 x1 x2 x3 x4 x5 x6 x7 : ℕ,
      (x0 + x1 + x2 + x3 + x4 + x5 + x6 + x7) % 2 ^ 32 =
        _root_.add32 x0 (_root_.add32
          (_root_.add32 (_root_.add32 (_root_.add32 (_root_.add32 x1 x2) x3) x4) x5)
          (_root_.add32 x6 x7)) := by
    intro x0 x1 x2 x3 x4 x5 x6 x7; unfold _root_.add32; omega
  obtain ⟨v4, n_out4⟩ := s_out4
  obtain ⟨v0, n_out0⟩ := s_out0
  rw [Fin.sum_univ_seven] at v4
  simp only [Fin.getElem_fin, red,
    show ((0:Fin 7):ℕ)=0 from rfl, show ((1:Fin 7):ℕ)=1 from rfl, show ((2:Fin 7):ℕ)=2 from rfl,
    show ((3:Fin 7):ℕ)=3 from rfl, show ((4:Fin 7):ℕ)=4 from rfl, show ((5:Fin 7):ℕ)=5 from rfl,
    show ((6:Fin 7):ℕ)=6 from rfl,
    Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ] at v4
  rw [s_sig1.1, s_ch.1,
    SHA256Rounds.valueBits_constWord32_of_lt env k63Nat_lt, k63Nat_eq,
    h_eval 3 (by norm_num), h_eval 4 (by norm_num), h_eval 5 (by norm_num),
    h_eval 6 (by norm_num), h_eval 7 (by norm_num), h_input_w, h_input_s4] at v4
  rw [Fin.sum_univ_eight] at v0
  simp only [Fin.getElem_fin, red,
    show ((0:Fin 8):ℕ)=0 from rfl, show ((1:Fin 8):ℕ)=1 from rfl, show ((2:Fin 8):ℕ)=2 from rfl,
    show ((3:Fin 8):ℕ)=3 from rfl, show ((4:Fin 8):ℕ)=4 from rfl, show ((5:Fin 8):ℕ)=5 from rfl,
    show ((6:Fin 8):ℕ)=6 from rfl, show ((7:Fin 8):ℕ)=7 from rfl,
    Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ] at v0
  rw [s_sig1.1, s_ch.1, s_sig0.1, s_maj.1,
    SHA256Rounds.valueBits_constWord32_of_lt env k63Nat_lt, k63Nat_eq,
    h_eval 0 (by norm_num), h_eval 1 (by norm_num), h_eval 2 (by norm_num),
    h_eval 4 (by norm_num), h_eval 5 (by norm_num), h_eval 6 (by norm_num),
    h_eval 7 (by norm_num), h_input_w, h_input_s0] at v0
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [v0, sha256Round_eq, vec8_getElem0]
    simp only [Vector.getElem_map]
    exact mod8 _ _ _ _ _ _ _ _
  · rw [v4, sha256Round_eq, vec8_getElem4]
    simp only [Vector.getElem_map]
    exact mod7 _ _ _ _ _ _ _
  · exact n_out0
  · exact n_out4

set_option maxHeartbeats 4000000 in
theorem completeness : Completeness (F p) main Assumptions := by
  circuit_proof_start [UpperSigma1.circuit, UpperSigma0.circuit,
    Ch32.circuit, Maj32.circuit, AddMany.circuit]
  obtain ⟨h_state_norm, h_w_norm, h_s0_norm, h_s4_norm⟩ := h_assumptions
  obtain ⟨h_input_state, h_input_w, h_input_s0, h_input_s4⟩ := h_input
  have h_eval : ∀ (i : ℕ) (hi : i < 8),
      Vector.map (Expression.eval env.toEnvironment) (input_var_state[i]'hi) = input_state[i]'hi := by
    intro i hi
    have h := getElem_eval_vector env.toEnvironment input_var_state i hi
    rw [h_input_state] at h
    rw [← CircuitType.eval_var_fields env.toEnvironment (input_var_state[i]'hi)]
    exact h
  simp only [UpperSigma1.Assumptions, UpperSigma0.Assumptions, Ch32.Assumptions,
    Maj32.Assumptions, UpperSigma1.Spec, UpperSigma0.Spec, Ch32.Spec, Maj32.Spec,
    AddMany.Assumptions, AddMany.Spec, and_imp] at h_env ⊢
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
  refine ⟨n4, ⟨n4, n5, n6⟩, n0, ⟨n0, n1, n2⟩, ?_, ?_⟩
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
    · rw [h_input_w]; exact h_w_norm
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
    · rw [h_input_w]; exact h_w_norm
    · exact s_sig0.2
    · exact s_maj.2

def circuit : FormalCircuit (F p) Inputs Outputs where
  main; elaborated; Assumptions; Spec; soundness; completeness


section CostLemmas
open Challenge.Instances.SHA256.Interface
open Challenge.CostR1CS

instance factCircomPrimeLarge : Fact (circomPrime > 2^35) := ⟨by
  norm_num [circomPrime]⟩

theorem costIs_xor3 (a b c : Var (fields 32) (F circomPrime)) :
    CostIs (Xor3.xor3 a b c) ⟨32, 32⟩ :=
  CostIs.bind (CostIs.witnessVector 32 _) fun z =>
    CostIs.bind (CostIs.forEach fun _ => CostIs.assertZero _) fun _ => CostIs.pure z

theorem costIs_ch32 (e f g : Var (fields 32) (F circomPrime)) :
    CostIs (Ch32.ch32 e f g) ⟨32, 32⟩ :=
  CostIs.bind (CostIs.witnessVector 32 _) fun z =>
    CostIs.bind (CostIs.forEach fun _ => CostIs.assertZero _) fun _ => CostIs.pure z

theorem costIs_maj32 (a b c : Var (fields 32) (F circomPrime)) :
    CostIs (Maj32.maj32 a b c) ⟨32, 32⟩ :=
  CostIs.bind (CostIs.witnessVector 32 _) fun z =>
    CostIs.bind (CostIs.forEach fun _ => CostIs.assertZero _) fun _ => CostIs.pure z

theorem costIs_addMany {n : ℕ} (words : Var (ProvableVector (fields 32) n) (F circomPrime)) :
    CostIs (AddMany.addMany words) ⟨34, 35⟩ :=
  CostIs.bind (CostIs.witnessVector 32 _) fun z =>
  CostIs.bind (CostIs.witnessVector 2 _) fun _ =>
  CostIs.bind (CostIs.forEach fun _ => CostIs.assertZero _) fun _ =>
  CostIs.bind (CostIs.forEach fun _ => CostIs.assertZero _) fun _ =>
  CostIs.bind (CostIs.assertZero _) fun _ => CostIs.pure z

theorem costIs_sub_upperSigma1 (b : Var (fields 32) (F circomPrime)) :
    CostIs (subcircuit UpperSigma1.circuit b) ⟨32, 32⟩ :=
  CostIs.subcircuit (CostIs.subcircuit (costIs_xor3 _ _ _))

theorem costIs_sub_upperSigma0 (b : Var (fields 32) (F circomPrime)) :
    CostIs (subcircuit UpperSigma0.circuit b) ⟨32, 32⟩ :=
  CostIs.subcircuit (CostIs.subcircuit (costIs_xor3 _ _ _))

theorem costIs_sub_ch32 (b : Var Ch32.Inputs (F circomPrime)) :
    CostIs (subcircuit Ch32.circuit b) ⟨32, 32⟩ :=
  CostIs.subcircuit (costIs_ch32 _ _ _)

theorem costIs_sub_maj32 (b : Var Maj32.Inputs (F circomPrime)) :
    CostIs (subcircuit Maj32.circuit b) ⟨32, 32⟩ :=
  CostIs.subcircuit (costIs_maj32 _ _ _)

theorem costIs_sub_addMany {n : ℕ} (hn : n ≤ 8)
    (b : Var (ProvableVector (fields 32) n) (F circomPrime)) :
    CostIs (subcircuit (AddMany.circuit hn) b) ⟨34, 35⟩ :=
  CostIs.subcircuit (costIs_addMany b)

theorem costIs_main (input : Var Inputs (F circomPrime)) :
    CostIs (main input) ⟨196, 198⟩ :=
  CostIs.bind (costIs_sub_upperSigma1 _) fun _ =>
  CostIs.bind (costIs_sub_ch32 _) fun _ =>
  CostIs.bind (costIs_sub_upperSigma0 _) fun _ =>
  CostIs.bind (costIs_sub_maj32 _) fun _ =>
  CostIs.bind (costIs_sub_addMany _ _) fun _ =>
  CostIs.bind (costIs_sub_addMany _ _) fun _ => CostIs.pure _

end CostLemmas

end Round63DM
end Solution.SHA256
end
