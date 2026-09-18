import Solution.Secp256k1ScalarMul.CompleteAddIsInf
import Solution.Secp256k1ScalarMul.CancelTheorems
import Solution.Secp256k1ScalarMul.IsZeroFe

/-!
# Lower-cost final infinity flag

For finite on-curve points with equal x-coordinate, the y-coordinates are equal
or opposite.  Since the secp256k1 prime has odd low 64-bit limb, these two cases
are distinguished by equality of only the least-significant y limb.  Thus the
final MSM addition needs one `IsZeroField` instead of a full four-limb `EqFe`.
-/

namespace Solution.Secp256k1ScalarMul
namespace CompleteAddIsInfLow

open Specs.ShortWeierstrass Specs.Secp256k1

abbrev Inputs := CompleteAdd.Inputs

def main (input : Var Inputs (F circomPrime)) :
    Circuit (F circomPrime) (Expression (F circomPrime)) := do
  let { P, Q } := input
  let sameX ← subcircuit EqFe.circuit { a := Q.x, b := P.x }
  let sameY0 ← subcircuit Gadgets.IsZeroField.circuit (P.y[0] - Q.y[0])
  let cancel <== sameX * (1 - sameY0)
  let s2 ← subcircuit (Mux.circuit (M := field))
    { selector := Q.isInf, ifTrue := P.isInf, ifFalse := cancel }
  subcircuit (Mux.circuit (M := field))
    { selector := P.isInf, ifTrue := Q.isInf, ifFalse := s2 }

instance elaborated : ElaboratedCircuit (F circomPrime) Inputs field main := by
  elaborate_circuit

def Assumptions (input : Inputs (F circomPrime)) : Prop :=
  input.P.Valid ∧ input.Q.Valid

def Spec (input : Inputs (F circomPrime)) (out : F circomPrime) : Prop :=
  out = if add curve (decodePoint input.P) (decodePoint input.Q) = .infinity
    then 1 else 0

set_option maxHeartbeats 1000000 in
theorem soundness :
    Soundness (Input := Inputs) (Output := field)
      (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [EqFe.circuit, EqFe.Assumptions, EqFe.Spec,
    Gadgets.IsZeroField.circuit, Gadgets.IsZeroField.Assumptions,
    Gadgets.IsZeroField.Spec, Mux.circuit, Mux.Assumptions, Mux.Spec]
  obtain ⟨hsameX, hsameY0, hcancel, hs2, hout⟩ := h_holds
  obtain ⟨hP, hQ⟩ := h_assumptions
  have hsx := EqFe.flag_eq_decode_eq hQ.2.1 hP.2.1 hsameX
  have hPib : IsBool input_P_isInf := hP.1
  have hQib : IsBool input_Q_isInf := hQ.1
  have h01 : (0 : F circomPrime) ≠ 1 := zero_ne_one
  have hInfAff : ∀ p : Point Fp, (GroupPoint.affine p ≠ GroupPoint.infinity) := by
    intro p h; cases h
  have hout' := hout hPib
  have hs2' := hs2 hQib
  rw [hout', hs2', hcancel, hsx]
  rcases hPib with hP0 | hP1 <;> rcases hQib with hQ0 | hQ1
  · rw [hP0, hQ0, if_neg h01, if_neg h01,
      CompleteAdd.decodePoint_of_finite rfl, CompleteAdd.decodePoint_of_finite rfl,
      CompleteAdd.add_affine]
    by_cases hx : decodeFe input_P_x = decodeFe input_Q_x
    · rw [if_pos hx, if_pos hx.symm]
      have hlow : input_P_y[0] = input_Q_y[0] ↔
          decodeFe input_P_y = decodeFe input_Q_y :=
        low_y_eq_iff_of_same_x hP hQ hP0 hQ0 hx.symm
      have hPy0 : Expression.eval env input_var_P_y[0] = input_P_y[0] := by
        simpa only [Vector.getElem_map] using congrArg (fun y : Emu (F circomPrime) => y[0]) h_input.1.2.1
      have hQy0 : Expression.eval env input_var_Q_y[0] = input_Q_y[0] := by
        simpa only [Vector.getElem_map] using congrArg (fun y : Emu (F circomPrime) => y[0]) h_input.2.2.1
      rw [hPy0, hQy0] at hsameY0
      have hsameY0' : env.get (i₀ + 3 + 1) =
          if decodeFe input_P_y = decodeFe input_Q_y then 1 else 0 := by
        rw [hsameY0]
        by_cases h : input_P_y[0] = input_Q_y[0]
        · have hz : input_P_y[0] + -input_Q_y[0] = 0 := by
            rw [h]; ring
          rw [if_pos hz, if_pos (hlow.mp h)]
        · have hz : input_P_y[0] + -input_Q_y[0] ≠ 0 := by
            intro hz; apply h; linear_combination hz
          rw [if_neg hz, if_neg (fun heq => h (hlow.mpr heq))]
      rw [hsameY0']
      by_cases hy : decodeFe input_P_y = decodeFe input_Q_y
      · rw [if_pos hy]
        have hnopp : decodeFe input_P_y ≠ -decodeFe input_Q_y := by
          intro ho
          have hPzero : decodeFe input_P_y = 0 := by
            have h2 : (2 : Fp) * decodeFe input_P_y = 0 := by
              linear_combination ho + hy
            exact (mul_eq_zero.mp h2).resolve_left CompleteAdd.two_ne_zero_fp
          exact ProofBlocker.noOrderTwo _ (hP.2.2.2 hP0) hPzero
        rw [if_neg hnopp, if_neg (hInfAff _)]
        norm_num
      · rw [if_neg hy]
        rcases same_x_y_eq_or_opp hP hQ hP0 hQ0 hx.symm with heq | hopp
        · exact (hy heq.symm).elim
        · rw [if_pos (eq_neg_of_add_eq_zero_left hopp)]
          norm_num
    · rw [if_neg hx, if_neg (fun h => hx h.symm), zero_mul, if_neg (hInfAff _)]
  · rw [hP0, hQ1, if_neg h01, if_pos rfl,
      CompleteAdd.decodePoint_of_finite rfl, CompleteAdd.decodePoint_of_isInf rfl,
      CompleteAdd.add_inf_right, if_neg (hInfAff _)]
  · rw [hP1, if_pos rfl, hQ0,
      CompleteAdd.decodePoint_of_isInf rfl, CompleteAdd.add_inf_left,
      CompleteAdd.decodePoint_of_finite rfl, if_neg (hInfAff _)]
  · rw [hP1, if_pos rfl, hQ1,
      CompleteAdd.decodePoint_of_isInf rfl, CompleteAdd.add_inf_left,
      CompleteAdd.decodePoint_of_isInf rfl, if_pos rfl]

theorem completeness :
    Completeness (Input := Inputs) (Output := field)
      (F circomPrime) main Assumptions := by
  circuit_proof_start [EqFe.circuit, EqFe.Assumptions, EqFe.Spec,
    Gadgets.IsZeroField.circuit, Gadgets.IsZeroField.Assumptions,
    Gadgets.IsZeroField.Spec, Mux.circuit, Mux.Assumptions, Mux.Spec]
  exact ⟨h_env.2.2.1, h_assumptions.2.1, h_assumptions.1.1⟩

def circuit : FormalCircuit (F circomPrime) Inputs field where
  main := main
  elaborated := elaborated
  Assumptions := Assumptions
  Spec := Spec
  soundness := soundness
  completeness := completeness

private lemma y0diff_stable {e e' : ProverEnvironment (F circomPrime)}
    {P Q : Var FlaggedPoint (F circomPrime)}
    (h : eval e (⟨P, Q⟩ : Var Inputs (F circomPrime)) =
      eval e' (⟨P, Q⟩ : Var Inputs (F circomPrime))) :
    eval e (P.y[0] - Q.y[0]) = eval e' (P.y[0] - Q.y[0]) := by
  simp only [circuit_norm, CompleteAdd.Inputs.mk.injEq, FlaggedPoint.mk.injEq] at h
  rw [CircuitType.eval_var_field_prover, CircuitType.eval_var_field_prover]
  simp only [Expression.eval]
  have hP := congrArg (fun v : Emu (F circomPrime) => v[0]) h.1.2.1
  have hQ := congrArg (fun v : Emu (F circomPrime) => v[0]) h.2.2.1
  simp only [Vector.getElem_map] at hP hQ
  rw [hP, hQ]

open Challenge.Utils.ComputableWitnessLemmas in
theorem computableWitnesses : circuit.base.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations offset)
  apply FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  obtain ⟨P, Q⟩ := input
  have heq : ∀ (X : Var EqFe.Inputs (F circomPrime)) (o : ℕ),
      (subcircuit EqFe.circuit X).localLength o = 3 := fun _ _ => rfl
  have hiz : ∀ (x : Expression (F circomPrime)) (o : ℕ),
      (subcircuit Gadgets.IsZeroField.circuit x).localLength o = 2 := fun _ _ => rfl
  have hmx : ∀ (X : Var (Mux.Inputs field) (F circomPrime)) (o : ℕ),
      (subcircuit (Mux.circuit (M := field)) X).localLength o = 1 := fun _ _ => rfl
  unfold main
  simp only [Circuit.bind_structuralComputableWitnesses_iff,
    FormalCircuit.subcircuit_structuralComputableWitnesses_iff,
    heq, hiz, hmx]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) EqFe.circuit _ _ _ ?_ EqFe.computableWitnesses env env'
    intro k e e' _ _ h_in
    simp only [circuit_norm, CompleteAdd.Inputs.mk.injEq, FlaggedPoint.mk.injEq] at h_in
    simp only [circuit_norm, EqFe.Inputs.mk.injEq]
    exact ⟨h_in.2.1, h_in.1.1⟩
  · exact FormalCircuit.subcircuit_flatStructuralComputableWitnesses
      (Parent := Inputs) Gadgets.IsZeroField.circuit
      (⟨P, Q⟩ : Var Inputs (F circomPrime)) (P.y[0] - Q.y[0]) (offset + 3)
      (fun _ _ h => y0diff_stable h) IsZeroFe.isZeroFieldComputableWitnesses env env'
  · refine ⟨?_, ?_, trivial⟩
    · intro h_agree _
      simp only [circuit_norm, subcircuit, EqFe.circuit, EqFe.elaborated,
        Gadgets.IsZeroField.circuit, Gadgets.IsZeroField.elaborated,
        Expression.eval]
      rw [h_agree (offset + 2) (by omega), h_agree (offset + 4) (by omega)]
    · exact IsZeroFe.equalityFieldSubcircuit_flatStructural_any
        (Parent := Inputs) (⟨P, Q⟩ : Var Inputs (F circomPrime)) _ _ _ env env'
  · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) (Mux.circuit (M := field)) _ _ _ ?_
      (Mux.computableWitnesses (M := field)) env env'
    intro k e e' hle h_agree h_in
    simp only [circuit_norm, HasAssignEq.assignEq] at hle
    simp only [circuit_norm, CompleteAdd.Inputs.mk.injEq, FlaggedPoint.mk.injEq] at h_in
    simp only [circuit_norm, Mux.Inputs.mk.injEq]
    exact ⟨h_in.2.2.2, h_in.1.2.2, h_agree (offset + 5) (by omega)⟩
  · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) (Mux.circuit (M := field)) _ _ _ ?_
      (Mux.computableWitnesses (M := field)) env env'
    intro k e e' hle h_agree h_in
    simp only [circuit_norm, HasAssignEq.assignEq] at hle
    simp only [circuit_norm, CompleteAdd.Inputs.mk.injEq, FlaggedPoint.mk.injEq] at h_in
    simp only [circuit_norm, Mux.Inputs.mk.injEq]
    exact ⟨h_in.1.2.2, h_in.2.2.2, h_agree (offset + 6) (by omega)⟩

end CompleteAddIsInfLow
end Solution.Secp256k1ScalarMul
