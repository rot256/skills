import Solution.Secp256k1ScalarMul.Params
import Solution.Secp256k1ScalarMul.IsZeroFeTheorems
import Challenge.Utils.ComputableWitnessLemmas
import Clean.Gadgets.IsZeroField

namespace Solution.Secp256k1ScalarMul
namespace IsZeroFe

private def xInvCompute (input : Expression (F circomPrime))
    (env : ProverEnvironment (F circomPrime)) : F circomPrime :=
  if Expression.eval env.toEnvironment input = 0 then 0
  else (Expression.eval env.toEnvironment input)⁻¹

private def xInvCircuit (input : Expression (F circomPrime)) :
    Circuit (F circomPrime) (Expression (F circomPrime)) :=
  witnessField (xInvCompute input)

private def isZeroFieldMain (input : Expression (F circomPrime)) :
    Circuit (F circomPrime) (Expression (F circomPrime)) := do
  let xInv ← xInvCircuit input
  let isZero <== 1 - input * xInv
  isZero * input === 0
  return isZero

private lemma expression_stable_of_field_eval_eq
    {env env' : ProverEnvironment (F circomPrime)}
    {x : Expression (F circomPrime)}
    (h : eval env x = eval env' x) :
    Expression.eval env.toEnvironment x = Expression.eval env'.toEnvironment x := by
  rw [CircuitType.eval_expression_prover_to_verifier (M := field),
    CircuitType.eval_expression_prover_to_verifier (M := field)] at h
  rw [CircuitType.eval_var_field, CircuitType.eval_var_field] at h
  exact h

private lemma xInvCompute_stable
    {env env' : ProverEnvironment (F circomPrime)}
    {input : Expression (F circomPrime)}
    (h : eval env input = eval env' input) :
    xInvCompute input env = xInvCompute input env' := by
  have hx := expression_stable_of_field_eval_eq h
  simp [xInvCompute, hx]

private theorem toFlat_append (a b : Operations (F circomPrime)) :
    (a ++ b).toFlat = a.toFlat ++ b.toFlat := by
  induction a using Operations.induct with
  | empty => simp [Operations.toFlat]
  | witness _ _ _ ih | assert _ _ ih | lookup _ _ ih | interact _ _ ih =>
    simp [Operations.toFlat, ih]
  | subcircuit s _ ih => simp [Operations.toFlat, ih, List.append_assoc]

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
    | assert e =>
      exact ih offset h_rest
    | lookup l =>
      exact ih offset h_rest
    | interact i =>
      exact ih offset h_rest

theorem equalityFieldSubcircuit_flatStructural_any
    {Parent : TypeMap} [CircuitType Parent] {M : TypeMap} [ProvableType M]
    (parentInput : Var Parent (F circomPrime))
    (pair : ProvablePair M M (Expression (F circomPrime)))
    (subOffset structuralOffset : ℕ)
    (env env' : ProverEnvironment (F circomPrime)) :
      Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.FlatOperation.StructuralComputableWitnesses
        parentInput env env' structuralOffset
        ((Gadgets.Equality.circuit (F := F circomPrime) M).toSubcircuit subOffset pair).ops.toFlat := by
  apply flatStructural_of_no_witness
  unfold FormalAssertion.toSubcircuit Gadgets.Equality.circuit
  rw [Operations.toNested_toFlat]
  rcases pair with ⟨lhs, rhs⟩
  simp only [Gadgets.Equality.main]
  intro x hx
  rw [Circuit.forEach.operations_eq, toFlat_flatten, List.map_ofFn, List.mem_flatten] at hx
  obtain ⟨l, hl, hxl⟩ := hx
  rw [List.mem_ofFn] at hl
  obtain ⟨i, rfl⟩ := hl
  simp only [Function.comp, Circuit.assertZero, circuit_norm, Operations.toFlat,
    List.mem_cons, List.not_mem_nil, or_false] at hxl
  subst hxl
  trivial

theorem isZeroFieldComputableWitnesses :
    (Gadgets.IsZeroField.circuit (F := F circomPrime)).ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition input env env')
    (((Gadgets.IsZeroField.circuit (F := F circomPrime)).main input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  change
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.StructuralComputableWitnesses
      input env env' offset ((isZeroFieldMain input).operations offset)
  unfold isZeroFieldMain
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.pure_structuralComputableWitnesses_iff,
    and_true]
  and_intros
  · intro _ h_input
    apply Vector.ext
    intro i hi
    have hi0 : i = 0 := by omega
    subst i
    simpa using xInvCompute_stable h_input
  · trivial
  · intro h_agree h_input
    apply Vector.ext
    intro i hi
    have hi0 : i = 0 := by omega
    subst i
    have hx := expression_stable_of_field_eval_eq h_input
    have hxInvRaw : Expression.eval env.toEnvironment
          (((witnessField fun env : ProverEnvironment (F circomPrime) =>
            if Expression.eval env.toEnvironment input = 0 then 0
            else (Expression.eval env.toEnvironment input)⁻¹) :
              Circuit (F circomPrime) (Expression (F circomPrime))).output offset) =
        Expression.eval env'.toEnvironment
          (((witnessField fun env : ProverEnvironment (F circomPrime) =>
            if Expression.eval env.toEnvironment input = 0 then 0
            else (Expression.eval env.toEnvironment input)⁻¹) :
              Circuit (F circomPrime) (Expression (F circomPrime))).output offset) := by
      simp [Circuit.witnessField, Circuit.output]
      apply h_agree
      change offset < offset + 1
      omega
    have hscalar :
        1 + -1 * (Expression.eval env.toEnvironment input *
            Expression.eval env.toEnvironment
              (((witnessField fun env : ProverEnvironment (F circomPrime) =>
                if Expression.eval env.toEnvironment input = 0 then 0
                else (Expression.eval env.toEnvironment input)⁻¹) :
                  Circuit (F circomPrime) (Expression (F circomPrime))).output offset)) =
          1 + -1 * (Expression.eval env'.toEnvironment input *
            Expression.eval env'.toEnvironment
              (((witnessField fun env : ProverEnvironment (F circomPrime) =>
                if Expression.eval env.toEnvironment input = 0 then 0
                else (Expression.eval env.toEnvironment input)⁻¹) :
                  Circuit (F circomPrime) (Expression (F circomPrime))).output offset)) := by
      rw [hx, hxInvRaw]
    change
      1 + -1 * (Expression.eval env.toEnvironment input *
        Expression.eval env.toEnvironment
          (((witnessField fun env : ProverEnvironment (F circomPrime) =>
            if Expression.eval env.toEnvironment input = 0 then 0
            else (Expression.eval env.toEnvironment input)⁻¹) :
              Circuit (F circomPrime) (Expression (F circomPrime))).output offset)) =
      1 + -1 * (Expression.eval env'.toEnvironment input *
        Expression.eval env'.toEnvironment
          (((witnessField fun env : ProverEnvironment (F circomPrime) =>
            if Expression.eval env.toEnvironment input = 0 then 0
            else (Expression.eval env.toEnvironment input)⁻¹) :
              Circuit (F circomPrime) (Expression (F circomPrime))).output offset))
    exact hscalar
  ·
    exact equalityFieldSubcircuit_flatStructural_any input _ _ _ env env'
  · trivial
  ·
    exact equalityFieldSubcircuit_flatStructural_any input _ _ _ env env'
  · trivial

lemma isZeroField_output_eval_stable (x : Expression (F circomPrime)) {base k : ℕ}
    {env env' : ProverEnvironment (F circomPrime)}
    (h_agree : env.AgreesBelow k env') (hk : base + 1 < k) :
    Expression.eval env.toEnvironment ((subcircuit Gadgets.IsZeroField.circuit x).output base) =
      Expression.eval env'.toEnvironment ((subcircuit Gadgets.IsZeroField.circuit x).output base) := by
  simp only [circuit_norm, Gadgets.IsZeroField.circuit]
  exact h_agree (base + 1) hk

lemma assignEq_output_eval_stable (r : Var field (F circomPrime)) {base k : ℕ}
    {env env' : ProverEnvironment (F circomPrime)}
    (h_agree : env.AgreesBelow k env') (hk : base < k) :
    Expression.eval env.toEnvironment
        ((HasAssignEq.assignEq (β := field (Expression (F circomPrime))) r).output base) =
      Expression.eval env'.toEnvironment
        ((HasAssignEq.assignEq (β := field (Expression (F circomPrime))) r).output base) := by
  simp only [circuit_norm, HasAssignEq.assignEq]
  exact h_agree base hk

end IsZeroFe
end Solution.Secp256k1ScalarMul
