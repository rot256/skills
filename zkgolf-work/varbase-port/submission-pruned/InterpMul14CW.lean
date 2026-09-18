import Solution.Secp256k1ScalarMul.MulMod
import Solution.Secp256k1ScalarMul.InterpMul14

/-!
# Structural computable-witness support for the fourteen-point multiply

`InterpMul14` provides the soundness / completeness side of the sparse
fourteen-point interpolated multiply.  This file adds the two structural
lemmas the enclosing certificates need for their `computableWitnesses`
proofs, mirroring `interpolatedMul_structuralComputableWitnesses` and
`interpolatedMul_output_stable`.
-/

namespace Solution.Secp256k1ScalarMul

section
variable {p : ℕ} [Fact p.Prime]

namespace MulMod

lemma interpolatedMul14_structuralComputableWitnesses
    {Parent : TypeMap} [CircuitType Parent] (parentInput : Var Parent (F p))
    (a b : Var (BigInt 8) (F p)) (offset : ℕ)
    (hinput : ∀ (k : ℕ) (env env' : ProverEnvironment (F p)),
      offset ≤ k →
      env.AgreesBelow k env' →
      eval env parentInput = eval env' parentInput →
        eval env a = eval env' a ∧ eval env b = eval env' b) :
    ∀ env env',
      Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.StructuralComputableWitnesses
        parentInput env env' offset ((interpolatedMul14 a b).operations offset) := by
  intro env env'
  unfold interpolatedMul14
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.provableWitness_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.forEach_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.assertZero_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.pure_structuralComputableWitnesses_iff,
    and_true]
  constructor
  · intro h_agree h_parent
    obtain ⟨ha, hb⟩ := hinput offset env env' (Nat.le_refl offset) h_agree h_parent
    apply Vector.ext
    intro t ht
    simp only [Vector.getElem_ofFn]
    exact bigIntMulNoReduce_coeff_stable env.toEnvironment env'.toEnvironment a b
      (fun i hi => bigInt_getElem_eval_eq ha i hi)
      (fun i hi => bigInt_getElem_eval_eq hb i hi) ⟨t, by omega⟩
  · intro _
    trivial

lemma interpolatedMul14_output_stable
    (off : ℕ) (a b : Var (BigInt 8) (F p))
    {k : ℕ} {env env' : ProverEnvironment (F p)}
    (h_agree : env.AgreesBelow k env') (hk : off + 14 ≤ k) :
    Vector.map (Expression.eval env.toEnvironment) (interpolatedMul14 a b off).1
      = Vector.map (Expression.eval env'.toEnvironment) (interpolatedMul14 a b off).1 := by
  rw [interpolatedMul14_output off a b]
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_map, zVec14, pushZero14]
  by_cases h14 : i < 14
  · rw [Vector.getElem_push_lt h14, Vector.getElem_mapRange]
    simp only [Expression.eval]
    exact h_agree (off + i) (by omega)
  · have hi14 : i = 14 := by omega
    subst hi14
    rw [Vector.getElem_push_eq]
    rfl

end MulMod
end

end Solution.Secp256k1ScalarMul
