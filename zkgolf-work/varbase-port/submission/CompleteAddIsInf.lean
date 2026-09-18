import Solution.Secp256k1ScalarMul.CompleteAdd
import Solution.Secp256k1ScalarMul.ProofBlocker
import Solution.Secp256k1ScalarMul.EqFe
import Solution.Secp256k1ScalarMul.Mux
import Challenge.Utils.ComputableWitnessLemmas

/-!
# Infinity flag of a complete addition — `CompleteAddIsInf`

This gadget computes *only* the `isInf` flag of the complete point addition
`P + Q`, i.e. it decides whether `add curve (decodePoint P) (decodePoint Q)`
is the point at infinity.  It is the exceptional-case detector of
`CompleteAdd.main` (the two `EqFe` flags, cancellation test, and `isInf` muxes) with the
affine coordinate computation (`DivOrZeroF3`, two `MulModSub2*`, the
denominator mux and the coordinate parts of the point muxes) removed.

It is used only for the *final* step of the joint MSM, where the accumulator's
coordinates are never consumed — only its infinity flag is asserted.  Dropping
the coordinate computation there saves the bulk of one complete addition.
-/

namespace Solution.Secp256k1ScalarMul
namespace CompleteAddIsInf

open Specs.ShortWeierstrass Specs.Secp256k1

/-- Compute the infinity flag of `P + Q`.

`sameX`/`sameY` are equality flags. Since secp256k1 has no affine 2-torsion,
`cancel = sameX·(1-sameY)` is exactly the finite cancellation case
`P + (−P) = 𝒪`, and the two muxes fold in the `P = 𝒪`/`Q = 𝒪` cases exactly
as in `CompleteAdd.main`. -/
def main (input : Var CompleteAdd.Inputs (F circomPrime)) :
    Circuit (F circomPrime) (Expression (F circomPrime)) := do
  let { P, Q } := input
  let sameX ← subcircuit EqFe.circuit { a := Q.x, b := P.x }
  let sameY ← subcircuit EqFe.circuit { a := P.y, b := Q.y }
  let cancel <== sameX * (1 - sameY)
  let s2 ← subcircuit (Mux.circuit (M := field))
    { selector := Q.isInf, ifTrue := P.isInf, ifFalse := cancel }
  let out ← subcircuit (Mux.circuit (M := field))
    { selector := P.isInf, ifTrue := Q.isInf, ifFalse := s2 }
  return out

instance elaborated : ElaboratedCircuit (F circomPrime) CompleteAdd.Inputs field main := by
  elaborate_circuit

def Assumptions (input : CompleteAdd.Inputs (F circomPrime)) : Prop :=
  input.P.Valid ∧ input.Q.Valid

/-- The output flag is `1` exactly when the complete sum is the point at
infinity, and `0` otherwise. -/
def Spec (input : CompleteAdd.Inputs (F circomPrime)) (out : F circomPrime) : Prop :=
  out = if add curve (decodePoint input.P) (decodePoint input.Q) = .infinity
    then 1 else 0

theorem soundness :
    Soundness (Input := CompleteAdd.Inputs) (Output := field)
      (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [EqFe.circuit, EqFe.Assumptions, EqFe.Spec,
    Mux.circuit, Mux.Assumptions, Mux.Spec]
  obtain ⟨hsameX, hsameY, hcancel, hs2, hout⟩ := h_holds
  obtain ⟨hP, hQ⟩ := h_assumptions
  have hsx := EqFe.flag_eq_decode_eq hQ.2.1 hP.2.1 hsameX
  have hsy := EqFe.flag_eq_decode_eq hP.2.2.1 hQ.2.2.1 hsameY
  have hout' := hout hP.1
  have hs2' := hs2 hQ.1
  have h01 : (0 : F circomPrime) ≠ 1 := zero_ne_one
  have hInfAff : ∀ p : Point Fp, (GroupPoint.affine p ≠ GroupPoint.infinity) := by
    intro p h; cases h
  have hPib : IsBool input_P_isInf := hP.1
  have hQib : IsBool input_Q_isInf := hQ.1
  rw [hout', hs2', hcancel, hsx, hsy]
  rcases hPib with hP0 | hP1 <;> rcases hQib with hQ0 | hQ1
  · rw [hP0, hQ0, if_neg h01, if_neg h01,
      CompleteAdd.decodePoint_of_finite rfl, CompleteAdd.decodePoint_of_finite rfl,
      CompleteAdd.add_affine]
    by_cases hx : decodeFe input_P_x = decodeFe input_Q_x
    · rw [if_pos hx]
      by_cases hy : decodeFe input_P_y = -decodeFe input_Q_y
      · rw [if_pos hy, if_pos rfl, if_pos hx.symm,
          if_neg (by
            intro heq
            apply ProofBlocker.noOrderTwo _ (hP.2.2.2 hP0)
            dsimp only at heq ⊢
            have hself : decodeFe input_P_y = -decodeFe input_P_y :=
              hy.trans (congrArg Neg.neg heq.symm)
            have h2 : (2 : Fp) * decodeFe input_P_y = 0 := by
              linear_combination hself
            exact (mul_eq_zero.mp h2).resolve_left CompleteAdd.two_ne_zero_fp)]
        norm_num
      · have hpOn := (CompleteAdd.onCurve_iff _).mp (hP.2.2.2 hP0)
        have hqOn := (CompleteAdd.onCurve_iff _).mp (hQ.2.2.2 hQ0)
        have hsq : decodeFe input_P_y ^ 2 = decodeFe input_Q_y ^ 2 := by
          rw [hpOn, hqOn, hx]
        have heqY : decodeFe input_P_y = decodeFe input_Q_y := by
          rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
          · exact h
          · exact (hy h).elim
        rw [if_neg hy, if_neg (hInfAff _), if_pos hx.symm, if_pos heqY]
        ring
    · rw [if_neg hx, if_neg (hInfAff _), if_neg (fun h => hx h.symm), zero_mul]
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
    Completeness (Input := CompleteAdd.Inputs) (Output := field)
      (F circomPrime) main Assumptions := by
  circuit_proof_start [EqFe.circuit, EqFe.Assumptions, EqFe.Spec,
    Mux.circuit, Mux.Assumptions, Mux.Spec]
  exact ⟨h_env.2.2.1, h_assumptions.2.1, h_assumptions.1.1⟩

private lemma assignEq_output_eval_stable (r : Var field (F circomPrime)) {base k : ℕ}
    {env env' : ProverEnvironment (F circomPrime)}
    (h_agree : env.AgreesBelow k env') (hk : base < k) :
    Expression.eval env.toEnvironment
        ((HasAssignEq.assignEq (β := field (Expression (F circomPrime))) r).output base) =
      Expression.eval env'.toEnvironment
        ((HasAssignEq.assignEq (β := field (Expression (F circomPrime))) r).output base) := by
  simp only [circuit_norm, HasAssignEq.assignEq]
  exact h_agree base hk

private lemma mulStable {e e' : ProverEnvironment (F circomPrime)}
    (a b : Expression (F circomPrime))
    (ha : Expression.eval e.toEnvironment a = Expression.eval e'.toEnvironment a)
    (hb : Expression.eval e.toEnvironment b = Expression.eval e'.toEnvironment b) :
    Expression.eval e.toEnvironment (a * b) = Expression.eval e'.toEnvironment (a * b) := by
  change Expression.eval e.toEnvironment (Expression.mul a b)
    = Expression.eval e'.toEnvironment (Expression.mul a b)
  rw [eval_mul, eval_mul, ha, hb]

private lemma expression_stable_of_field_eval_eq
    {env env' : ProverEnvironment (F circomPrime)}
    {x : Expression (F circomPrime)}
    (h : eval env x = eval env' x) :
    Expression.eval env.toEnvironment x = Expression.eval env'.toEnvironment x := by
  rw [CircuitType.eval_expression_prover_to_verifier (M := field),
    CircuitType.eval_expression_prover_to_verifier (M := field)] at h
  rw [CircuitType.eval_var_field, CircuitType.eval_var_field] at h
  exact h

private theorem toFlat_append (a b : Operations (F circomPrime)) :
    (a ++ b).toFlat = a.toFlat ++ b.toFlat := by
  induction a with
  | nil => rfl
  | cons x rest ih => cases x <;> simp [Operations.toFlat, ih, List.append_assoc]

private theorem toFlat_flatten (L : List (Operations (F circomPrime))) :
    Operations.toFlat L.flatten = (L.map Operations.toFlat).flatten := by
  induction L with
  | nil => rfl
  | cons a rest ih =>
    rw [List.flatten_cons, toFlat_append, ih, List.map_cons, List.flatten_cons]

private theorem flatStructural_of_no_witness
    {Parent : TypeMap} [CircuitType Parent]
    (parentInput : Var Parent (F circomPrime))
    (env env' : ProverEnvironment (F circomPrime)) :
    ∀ (ops : List (FlatOperation (F circomPrime))) (offset : ℕ),
      (∀ x ∈ ops, match x with | .witness _ _ => False | _ => True) →
      Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.FlatOperation.StructuralComputableWitnesses
        parentInput env env' offset ops := by
  intro ops
  induction ops with
  | nil => intro offset _; trivial
  | cons x rest ih =>
    intro offset h
    have h_rest : ∀ y ∈ rest, match y with | .witness _ _ => False | _ => True :=
      fun y hy => h y (List.mem_cons_of_mem _ hy)
    cases x with
    | witness m c => exact absurd (h _ (List.mem_cons_self ..)) (by simp)
    | assert e => exact ih offset h_rest
    | lookup l => exact ih offset h_rest
    | interact i => exact ih offset h_rest

def circuit : FormalCircuit (F circomPrime) CompleteAdd.Inputs field where
  main := main
  elaborated := elaborated
  Assumptions := Assumptions
  Spec := Spec
  soundness := soundness
  completeness := completeness

lemma output_eq (input : Var CompleteAdd.Inputs (F circomPrime)) (o : ℕ) :
    circuit.output input o = (var ⟨o + 8⟩ : Expression (F circomPrime)) := by
  show elaborated.output input o = _
  simp only [circuit_norm]

open Challenge.Utils.ComputableWitnessLemmas in
theorem computableWitnesses : circuit.base.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  obtain ⟨P, Q⟩ := input
  have hiszD : ∀ (x : Var EqFe.Inputs (F circomPrime)) (o : ℕ),
      (subcircuit EqFe.circuit x).localLength o = 3 := fun _ _ => rfl
  have hmxF : ∀ (X : Var (Mux.Inputs field) (F circomPrime)) (o : ℕ),
      (subcircuit (Mux.circuit (M := field)) X).localLength o = 1 := fun _ _ => rfl
  let sameX : Var field (F circomPrime) :=
    (subcircuit EqFe.circuit { a := Q.x, b := P.x }).output offset
  let sameY : Var field (F circomPrime) :=
    (subcircuit EqFe.circuit { a := P.y, b := Q.y }).output (offset + 3)
  let cancel : Var field (F circomPrime) :=
    (HasAssignEq.assignEq (sameX * (1 - sameY))).output (offset + 3 + 3)
  unfold main
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.pure_structuralComputableWitnesses_iff,
    hiszD, hmxF, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := CompleteAdd.Inputs) EqFe.circuit _ _ _ ?_ EqFe.computableWitnesses env env'
    intro k e e' hle h_agree h_in
    simp only [circuit_norm, CompleteAdd.Inputs.mk.injEq, FlaggedPoint.mk.injEq] at h_in
    obtain ⟨⟨hPx, _, _⟩, hQx, _, _⟩ := h_in
    simp only [circuit_norm]; rw [EqFe.Inputs.mk.injEq]
    exact ⟨hQx, hPx⟩
  · refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := CompleteAdd.Inputs) EqFe.circuit _ _ _ ?_ EqFe.computableWitnesses env env'
    intro k e e' hle h_agree h_in
    simp only [circuit_norm, CompleteAdd.Inputs.mk.injEq, FlaggedPoint.mk.injEq] at h_in
    obtain ⟨⟨_, hPy, _⟩, _, hQy, _⟩ := h_in
    simp only [circuit_norm]; rw [EqFe.Inputs.mk.injEq]
    exact ⟨hPy, hQy⟩
  · simp only [HasAssignEq.assignEq,
      Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
      Challenge.Utils.ComputableWitnessLemmas.Circuit.provableWitness_structuralComputableWitnesses_iff,
      Challenge.Utils.ComputableWitnessLemmas.Circuit.pure_structuralComputableWitnesses_iff,
      and_true]
    refine ⟨?_, ?_⟩
    · intro h_agree _h_in
      rw [CircuitType.eval_expression_prover_to_verifier (M := field),
        CircuitType.eval_expression_prover_to_verifier (M := field),
        CircuitType.eval_var_field, CircuitType.eval_var_field]
      exact mulStable _ _
        (expression_stable_of_field_eval_eq
          (EqFe.eval_output_of_agreesBelow { a := Q.x, b := P.x }
            (offset := offset) h_agree (by omega)))
        (by
          simp only [circuit_norm, subcircuit, EqFe.circuit, EqFe.elaborated,
            Expression.eval]
          rw [h_agree _ (by omega)])
    · simp only [HasAssertEq.assert_eq, assertEquals,
        Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_structuralComputableWitnesses_iff]
      apply flatStructural_of_no_witness
      simp only [Gadgets.Equality.circuit, Gadgets.Equality.main]
      intro x hx
      rw [Circuit.forEach.operations_eq, toFlat_flatten, List.map_ofFn, List.mem_flatten] at hx
      obtain ⟨l, hl, hxl⟩ := hx
      rw [List.mem_ofFn] at hl
      obtain ⟨i, rfl⟩ := hl
      simp only [Function.comp, Circuit.assertZero, circuit_norm, Operations.toFlat,
        List.mem_cons, List.not_mem_nil, or_false] at hxl
      subst hxl
      trivial
  · refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := CompleteAdd.Inputs) (Mux.circuit (M := field)) _ _ _ ?_
      (Mux.computableWitnesses (M := field)) env env'
    intro k e e' hle h_agree h_in
    simp only [circuit_norm] at hle
    simp only [circuit_norm, CompleteAdd.Inputs.mk.injEq, FlaggedPoint.mk.injEq] at h_in
    obtain ⟨⟨_, _, hPi⟩, _, _, hQi⟩ := h_in
    simp only [circuit_norm]; rw [Mux.Inputs.mk.injEq]
    refine ⟨hQi, hPi, ?_⟩
    exact assignEq_output_eval_stable (sameX * (1 - sameY))
      (base := offset + 3 + 3) h_agree (by omega)
  · refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := CompleteAdd.Inputs) (Mux.circuit (M := field)) _ _ _ ?_
      (Mux.computableWitnesses (M := field)) env env'
    intro k e e' hle h_agree h_in
    simp only [circuit_norm] at hle
    simp only [circuit_norm, CompleteAdd.Inputs.mk.injEq, FlaggedPoint.mk.injEq] at h_in
    obtain ⟨⟨_, _, hPi⟩, _, _, hQi⟩ := h_in
    simp only [circuit_norm]; rw [Mux.Inputs.mk.injEq]
    refine ⟨hPi, hQi, ?_⟩
    exact expression_stable_of_field_eval_eq
      (Mux.eval_output_of_agreesBelow (M := field)
        { selector := Q.isInf, ifTrue := P.isInf, ifFalse := cancel }
        (offset := offset + 3 + 3 + 1) h_agree (by omega))

end CompleteAddIsInf
end Solution.Secp256k1ScalarMul
