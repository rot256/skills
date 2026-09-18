import Solution.Secp256k1ScalarMul.IsZeroFe2

/-!
# `CancelLow` — the two-row cancellation detector

For two canonical field representatives `y₁`, `y₂` and a boolean flag `sameX`,
this gadget produces

  `cancel = if y₁[0] = y₂[0] then 0 else sameX`

in **one witness and two rows**, by witnessing the inverse of the low-limb
difference:

```
  yDiffInv ← witness
  cancel  <== yDiff * yDiffInv
  assertZero (yDiff * (sameX - cancel))
```

When the low limbs differ the second row pins `cancel = sameX`; when they agree
the first row pins `cancel = 0`.  Callers combine this with the fact that two
finite same-`x` secp256k1 points have equal or opposite `y`, and that canonical
opposites differ already in the low 64-bit limb (`CancelTheorems`), so the flag
is exactly `sameX ∧ oppositeY` — at four fewer allocations and four fewer rows
than a full value-level opposite-`y` test followed by an `AND`.
-/

namespace Solution.Secp256k1ScalarMul
namespace CancelLow

structure Inputs (F : Type) where
  sameX : F
  y1 : Emu F
  y2 : Emu F
deriving ProvableStruct

/-- Witness generator for the low-limb difference inverse: zero unless the
flag is set and the difference is nonzero. -/
def yDiffInvCompute (input : Var Inputs (F circomPrime))
    (env : ProverEnvironment (F circomPrime)) : F circomPrime :=
  let d := Expression.eval env.toEnvironment (input.y1[0] - input.y2[0])
  if Expression.eval env.toEnvironment input.sameX = 1 then
    (if d = 0 then 0 else d⁻¹)
  else 0

def main (input : Var Inputs (F circomPrime)) :
    Circuit (F circomPrime) (Expression (F circomPrime)) := do
  let { sameX, y1, y2 } := input
  let yDiff := y1[0] - y2[0]
  let yDiffInv ← witnessField (yDiffInvCompute input)
  let cancel <== yDiff * yDiffInv
  assertZero (yDiff * (sameX - cancel))
  return cancel

instance elaborated : ElaboratedCircuit (F circomPrime) Inputs field main := by
  elaborate_circuit

def Assumptions (input : Inputs (F circomPrime)) : Prop := IsBool input.sameX

def Spec (input : Inputs (F circomPrime)) (out : F circomPrime) : Prop :=
  out = if input.y1[0] = input.y2[0] then 0 else input.sameX

theorem soundness :
    Soundness (Input := Inputs) (Output := field) (F circomPrime) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨hc, hassert⟩ := h_holds
  obtain ⟨hsx, hy1, hy2⟩ := h_input
  have h1 : Expression.eval env (input_var_y1[0]) = input_y1[0] := by
    have h := congrArg (fun v : Emu (F circomPrime) => v[0]) hy1
    simpa only [Vector.getElem_map] using h
  have h2 : Expression.eval env (input_var_y2[0]) = input_y2[0] := by
    have h := congrArg (fun v : Emu (F circomPrime) => v[0]) hy2
    simpa only [Vector.getElem_map] using h
  simp only [h1, h2] at hc hassert
  by_cases hd : input_y1[0] + -input_y2[0] = 0
  · have heq : input_y1[0] = input_y2[0] := by linear_combination hd
    rw [if_pos heq, hc, hd, zero_mul]
  · have hne : ¬ (input_y1[0] = input_y2[0]) := fun h => hd (by rw [h]; ring)
    rw [if_neg hne]
    have h := (mul_eq_zero.mp hassert).resolve_left hd
    linear_combination -h

theorem completeness :
    Completeness (Input := Inputs) (Output := field) (F circomPrime) main Assumptions := by
  circuit_proof_start
  obtain ⟨e1, e2⟩ := h_env
  refine ⟨e2, ?_⟩
  obtain ⟨hsx, hy1, hy2⟩ := h_input
  rw [e2, e1]
  simp only [yDiffInvCompute, Expression.eval, hsx, neg_one_mul]
  rcases h_assumptions with h0 | h1
  · rw [h0, if_neg zero_ne_one]
    ring
  · rw [h1, if_pos rfl]
    by_cases hd : Expression.eval env.toEnvironment (input_var_y1[0])
        + -Expression.eval env.toEnvironment (input_var_y2[0]) = 0
    · rw [hd]; ring
    · rw [if_neg hd, mul_inv_cancel₀ hd]; ring

def circuit : FormalCircuit (F circomPrime) Inputs field where
  main; elaborated; Assumptions; Spec; soundness; completeness

set_option maxRecDepth 4096 in
theorem computableWitnesses : circuit.base.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition
      input env env')
    ((main input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  obtain ⟨sameX, y1, y2⟩ := input
  have hL : ∀ (c : ProverEnvironment (F circomPrime) → F circomPrime) (o : ℕ),
      (witnessField c).localLength o = 1 := by
    intro c o
    unfold Circuit.witnessField
    change ((var <$> witnessVar c).localLength o) = 1
    rw [Circuit.map_localLength_eq]
    simp [Circuit.witnessVar, Circuit.localLength, Operations.localLength]
  have hA : ∀ (r : Var field (F circomPrime)) (o : ℕ),
      (HasAssignEq.assignEq (β := field (Expression (F circomPrime))) r).localLength o = 1 := by
    intro r o
    simp only [circuit_norm, HasAssignEq.assignEq]
  have hcells : ∀ (e e' : ProverEnvironment (F circomPrime)),
      eval e (⟨sameX, y1, y2⟩ : Var Inputs (F circomPrime)) =
        eval e' (⟨sameX, y1, y2⟩ : Var Inputs (F circomPrime)) →
      Expression.eval e.toEnvironment sameX = Expression.eval e'.toEnvironment sameX ∧
      Expression.eval e.toEnvironment (y1[0]) = Expression.eval e'.toEnvironment (y1[0]) ∧
      Expression.eval e.toEnvironment (y2[0]) = Expression.eval e'.toEnvironment (y2[0]) := by
    intro e e' hinput
    simp only [circuit_norm, Inputs.mk.injEq] at hinput
    obtain ⟨hs, h1, h2⟩ := hinput
    refine ⟨hs, ?_, ?_⟩
    · have h := congrArg (fun v : Emu (F circomPrime) => v[0]) h1
      simpa only [Vector.getElem_map] using h
    · have h := congrArg (fun v : Emu (F circomPrime) => v[0]) h2
      simpa only [Vector.getElem_map] using h
  unfold main
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.witnessField_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.assertZero_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.pure_structuralComputableWitnesses_iff,
    hL, hA, and_true]
  refine ⟨?_, ?_⟩
  -- 1. yDiffInv ← witnessField (input-only)
  · intro _ hin
    obtain ⟨hs, h1, h2⟩ := hcells env env' hin
    simp only [yDiffInvCompute, Expression.eval, hs, h1, h2]
  -- 2. cancel <== yDiff * yDiffInv (reads the inverse cell)
  · refine ⟨?_, ?_, ?_⟩
    · intro h_agree hin
      refine congrArg (fun x => (#v[x] : Vector (F circomPrime) 1)) ?_
      obtain ⟨hs, h1, h2⟩ := hcells env env' hin
      simp only [circuit_norm, HasAssignEq.assignEq, Circuit.witnessField,
        subcircuit] at h_agree ⊢
      have hg0 : env.get offset = env'.get offset := h_agree offset (by omega)
      try simp only [Expression.eval, hg0, h1, h2]
      try rfl
    · exact IsZeroFe.equalityFieldSubcircuit_flatStructural_any
        (Parent := Inputs) (⟨sameX, y1, y2⟩ : Var Inputs (F circomPrime)) _ _ _ env env'
    · trivial

theorem computableWitness : ∀ n input,
    ProverEnvironment.OnlyAccessedBelow n
      (fun env : ProverEnvironment (F circomPrime) => eval env input) →
    Circuit.ComputableWitnesses (main input) n :=
  Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnesses_implies
    (circuit := circuit.base) computableWitnesses

lemma eval_output_of_agreesBelow (input : Var Inputs (F circomPrime)) {offset k : ℕ}
    {env env' : ProverEnvironment (F circomPrime)}
    (h_agree : env.AgreesBelow k env') (hk : offset + 2 ≤ k) :
    Expression.eval env.toEnvironment (circuit.output input offset) =
      Expression.eval env'.toEnvironment (circuit.output input offset) := by
  obtain ⟨_, _, _⟩ := input
  simp only [circuit, circuit_norm, Expression.eval, main, HasAssignEq.assignEq,
    Circuit.witnessField] at ⊢
  exact h_agree (offset + 1) (by omega)

end CancelLow
end Solution.Secp256k1ScalarMul
