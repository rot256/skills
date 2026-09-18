import Solution.Secp256k1ScalarMul.NegYAffine
import Challenge.Utils.ComputableWitnessLemmas

namespace Solution.Secp256k1ScalarMul
namespace NegYAffine

open Challenge.Utils.ComputableWitnessLemmas

attribute [local irreducible] RangeCheck.circuit

private lemma carry0Compute_stable (P : Var FlaggedPoint (F circomPrime))
    (env env' : ProverEnvironment (F circomPrime))
    (h : eval env P = eval env' P) :
    carry0Compute P env = carry0Compute P env' := by
  unfold carry0Compute
  rw [h]

private lemma inv1Compute_stable (P : Var FlaggedPoint (F circomPrime))
    (env env' : ProverEnvironment (F circomPrime))
    (h : eval env P = eval env' P) :
    inv1Compute P env = inv1Compute P env' := by
  unfold inv1Compute
  rw [h]

private lemma zc1Compute_stable (P : Var FlaggedPoint (F circomPrime))
    (env env' : ProverEnvironment (F circomPrime))
    (h : eval env P = eval env' P) :
    zc1Compute P env = zc1Compute P env' := by
  unfold zc1Compute
  rw [h]

private lemma inv2Compute_stable (P : Var FlaggedPoint (F circomPrime))
    (env env' : ProverEnvironment (F circomPrime))
    (h : eval env P = eval env' P) :
    inv2Compute P env = inv2Compute P env' := by
  unfold inv2Compute
  rw [h]

private lemma zc2Compute_stable (P : Var FlaggedPoint (F circomPrime))
    (env env' : ProverEnvironment (F circomPrime))
    (h : eval env P = eval env' P) :
    zc2Compute P env = zc2Compute P env' := by
  unfold zc2Compute
  rw [h]

theorem computableWitnesses : circuit.base.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations offset)
  apply FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  have hw : ∀ (f : ProverEnvironment (F circomPrime) → F circomPrime) (o : ℕ),
      (witnessField f).localLength o = 1 := by
    intro f o
    simp [circuit_norm]
  have ha : ∀ (e : Expression (F circomPrime)) (o : ℕ),
      (assertZero e).localLength o = 0 := by
    intro e o
    simp [circuit_norm]
  unfold main
  simp only [Circuit.bind_structuralComputableWitnesses_iff,
    Circuit.witnessField_structuralComputableWitnesses_iff,
    Circuit.assertZero_structuralComputableWitnesses_iff,
    FormalAssertion.assertion_structuralComputableWitnesses_iff,
    Circuit.pure_structuralComputableWitnesses_iff, and_true, hw, ha]
  refine ⟨?_, ?_, ?_, ?_, ?_, trivial, trivial, trivial, trivial, trivial, ?_⟩
  · intro _ h
    exact carry0Compute_stable input env env' h
  · intro _ h
    exact inv1Compute_stable input env env' h
  · intro _ h
    exact zc1Compute_stable input env env' h
  · intro _ h
    exact inv2Compute_stable input env env' h
  · intro _ h
    exact zc2Compute_stable input env env' h
  · exact FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
      (Parent := FlaggedPoint)
      (RangeCheck.circuit secpParams.B secpParams.hB secpParams.hB1) _ _ _
      (by
        intro k e e' hle h_agree hinput
        have hy : eval e input.y = eval e' input.y := by
          simpa only [circuit_norm] using
            congrArg (fun z : FlaggedPoint (F circomPrime) => z.y) hinput
        have hi : Expression.eval e.toEnvironment input.isInf =
            Expression.eval e'.toEnvironment input.isInf := by
          simpa only [circuit_norm] using
            congrArg (fun z : FlaggedPoint (F circomPrime) => z.isInf) hinput
        have hc0 := h_agree offset (by omega)
        simp only [result, qExpr, circuit_norm, Vector.getElem_mk,
          List.getElem_toArray, List.getElem_cons_zero,
          Expression.eval, MulMod.bigInt_getElem_eval_eq hy, hi, hc0])
      (RangeCheck.computableWitnesses secpParams.B secpParams.hB secpParams.hB1) env env'

lemma eval_output_of_agreesBelow (P : Var FlaggedPoint (F circomPrime))
    {offset k : ℕ} {env env' : ProverEnvironment (F circomPrime)}
    (h_input : eval env P = eval env' P)
    (h_agree : env.AgreesBelow k env') (hk : offset + 5 ≤ k) :
    eval env ((main P).output offset) = eval env' ((main P).output offset) := by
  have hc0 := h_agree offset (by omega)
  have hc1 := h_agree (offset + 1 + 1) (by omega)
  have hc2 := h_agree (offset + 1 + 1 + 1 + 1) (by omega)
  simp only [circuit_norm, FlaggedPoint.mk.injEq] at h_input
  have hy0 : Expression.eval env.toEnvironment P.y[0] =
      Expression.eval env'.toEnvironment P.y[0] := by
    simpa only [Vector.getElem_map] using
      congrArg (fun y : Emu (F circomPrime) => y[0]) h_input.2.1
  have hy1 : Expression.eval env.toEnvironment P.y[1] =
      Expression.eval env'.toEnvironment P.y[1] := by
    simpa only [Vector.getElem_map] using
      congrArg (fun y : Emu (F circomPrime) => y[1]) h_input.2.1
  have hy2 : Expression.eval env.toEnvironment P.y[2] =
      Expression.eval env'.toEnvironment P.y[2] := by
    simpa only [Vector.getElem_map] using
      congrArg (fun y : Emu (F circomPrime) => y[2]) h_input.2.1
  have hy3 : Expression.eval env.toEnvironment P.y[3] =
      Expression.eval env'.toEnvironment P.y[3] := by
    simpa only [Vector.getElem_map] using
      congrArg (fun y : Emu (F circomPrime) => y[3]) h_input.2.1
  apply Vector.ext
  intro i hi
  interval_cases i <;>
    simp only [main, result, qExpr, circuit_norm, Vector.getElem_mk,
      List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ,
      Expression.eval, h_input.2.2, hy0, hy1, hy2, hy3, hc0, hc1, hc2]

end NegYAffine
end Solution.Secp256k1ScalarMul
