import Solution.Secp256k1ScalarMul.Cost
import Solution.Secp256k1ScalarMul.IsZeroFeSum
import Challenge.Utils.ComputableWitnessLemmas

/-!
# Zero test of an emulated field element, output allocated first

`IsZeroFeSum` tests whether the four limbs of an `Emu` all vanish, but it
delegates to `Gadgets.IsZeroField`, which allocates the inverse hint *before*
the boolean answer.  This file provides the same functionality with the two
cells swapped, so that the answer occupies the *first* of the two allocated
cells.  That makes it possible to append the flag to a block of previously
allocated coordinates and still read the result back as a single contiguous
`varFromOffset`.

Cost is identical: two allocations and two constraints.
-/

namespace Solution.Secp256k1ScalarMul
namespace IsZeroFeSumR

/-- The limb sum of the input, as an affine expression. -/
def sumE (x : Var Emu (F circomPrime)) : Expression (F circomPrime) :=
  x[0] + x[1] + x[2] + x[3]

def main (x : Var Emu (F circomPrime)) :
    Circuit (F circomPrime) (Expression (F circomPrime)) := do
  let s := sumE x
  let z ← witnessField fun env => if s.eval env = 0 then 1 else 0
  let zInv ← witnessField fun env => if s.eval env = 0 then 0 else (s.eval env)⁻¹
  assertZero (z - 1 + s * zInv)
  assertZero (z * s)
  return z

instance elaborated : ElaboratedCircuit (F circomPrime) Emu field main := by
  elaborate_circuit

def Assumptions (_ : Emu (F circomPrime)) : Prop := True

/-- The sum of the four limbs, as a field element.  Kept as a named function so
that the specification does not get decomposed by the caller's normalization. -/
def limbSum (x : Emu (F circomPrime)) : F circomPrime := x[0] + x[1] + x[2] + x[3]

def Spec (x : Emu (F circomPrime)) (out : F circomPrime) : Prop :=
  out = if limbSum x = 0 then 1 else 0

set_option maxRecDepth 8192 in
theorem soundness :
    Soundness (Input := Emu) (Output := field) (F circomPrime) main Assumptions Spec := by
  circuit_proof_start
  have hx : ∀ (i : ℕ) (hi : i < 4), Expression.eval env input_var[i] = input[i] := by
    intro i hi
    rw [← h_input, Vector.getElem_map]
  obtain ⟨h1, h2⟩ := h_holds
  simp only [sumE, Expression.eval, hx 0 (by omega), hx 1 (by omega), hx 2 (by omega),
    hx 3 (by omega)] at h1 h2
  simp only [limbSum]
  set s : F circomPrime := input[0] + input[1] + input[2] + input[3] with hs
  set z : F circomPrime := env.get i₀ with hz
  by_cases h : s = 0
  · rw [if_pos h]
    rw [h] at h1
    linear_combination h1
  · rw [if_neg h]
    exact (mul_eq_zero.mp h2).resolve_right h

theorem completeness :
    Completeness (Input := Emu) (Output := field) (F circomPrime) main Assumptions := by
  circuit_proof_start
  have hx : ∀ (i : ℕ) (hi : i < 4), Expression.eval env input_var[i] = input[i] := by
    intro i hi
    rw [← h_input, Vector.getElem_map]
  obtain ⟨e1, e2⟩ := h_env
  simp only [sumE, Expression.eval] at e1 e2 ⊢
  by_cases h : Expression.eval env input_var[0] + Expression.eval env input_var[1] +
      Expression.eval env input_var[2] + Expression.eval env input_var[3] = 0
  · rw [if_pos h] at e1 e2
    rw [e1, e2, h]; constructor <;> ring
  · rw [if_neg h] at e1 e2
    rw [e1, e2]
    refine ⟨?_, by ring⟩
    field_simp
    norm_num

def circuit : FormalCircuit (F circomPrime) Emu field where
  main := main
  elaborated := elaborated
  Assumptions := Assumptions
  Spec := Spec
  soundness := soundness
  completeness := completeness

private lemma input_sum_stable {input : Var Emu (F circomPrime)}
    {env env' : ProverEnvironment (F circomPrime)}
    (h : eval env input = eval env' input) :
    Expression.eval env.toEnvironment (sumE input)
      = Expression.eval env'.toEnvironment (sumE input) := by
  have hmap := emu_map_eval_eq_of_eval_eq h
  have hget : ∀ k (hk : k < 4),
      (input.map (Expression.eval env.toEnvironment))[k]'(by simpa using hk)
        = (input.map (Expression.eval env'.toEnvironment))[k]'(by simpa using hk) := by
    intro k hk; rw [hmap]
  have h0 := hget 0 (by omega)
  have h1 := hget 1 (by omega)
  have h2 := hget 2 (by omega)
  have h3 := hget 3 (by omega)
  simp only [Vector.getElem_map] at h0 h1 h2 h3
  simp only [sumE, Expression.eval]
  rw [h0, h1, h2, h3]

theorem computableWitnesses : circuit.base.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.witnessField_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.assertZero_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.pure_structuralComputableWitnesses_iff,
    and_true]
  constructor
  · intro _ hinput
    rw [input_sum_stable hinput]
  · intro _ hinput
    rw [input_sum_stable hinput]

theorem computableWitness : ∀ n input,
    ProverEnvironment.OnlyAccessedBelow n
      (fun env : ProverEnvironment (F circomPrime) => eval env input) →
    Circuit.ComputableWitnesses (main input) n :=
  Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnesses_implies
    (circuit := circuit.base) computableWitnesses

lemma eval_output_of_agreesBelow (x : Var Emu (F circomPrime)) {offset k : ℕ}
    {env env' : ProverEnvironment (F circomPrime)}
    (h_agree : env.AgreesBelow k env') (hk : offset + 1 ≤ k) :
    eval env ((main x).output offset) = eval env' ((main x).output offset) := by
  rw [CircuitType.eval_var_field_prover, CircuitType.eval_var_field_prover]
  simp only [main, circuit_norm]
  exact h_agree offset (by omega)

end IsZeroFeSumR

namespace Cost
open Challenge.CostR1CS
attribute [local irreducible] isR1CSRow r1csProducts operationsIsR1CS flatOperationsIsR1CS

theorem costIs_isZeroFeSumR (x : Var Emu (F circomPrime)) :
    CostIs (IsZeroFeSumR.main x) ⟨2, 2⟩ := by
  rw [show (⟨2, 2⟩ : Count) = ⟨1, 0⟩ + (⟨1, 0⟩ + (⟨0, 1⟩ + (⟨0, 1⟩ + Count.zero))) from by decide]
  unfold IsZeroFeSumR.main
  refine CostIs.bind (CostIs.witnessField _) fun _ => ?_
  refine CostIs.bind (CostIs.witnessField _) fun _ => ?_
  refine CostIs.bind (CostIs.assertZero _) fun _ => ?_
  exact CostIs.bind (CostIs.assertZero _) fun _ => CostIs.pure _

theorem costIs_sub_isZeroFeSumR (x : Var Emu (F circomPrime)) :
    CostIs (subcircuit IsZeroFeSumR.circuit x) ⟨2, 2⟩ :=
  CostIs.subcircuit (fun n => costIs_isZeroFeSumR x n)

theorem affine_sumE {x : Var Emu (F circomPrime)} (hx : AffineW x) :
    Affine (IsZeroFeSumR.sumE x) :=
  Affine.add (Affine.add (Affine.add (hx 0 (by decide)) (hx 1 (by decide)))
    (hx 2 (by decide))) (hx 3 (by decide))

theorem isR1CS_isZeroFeSumR (x : Var Emu (F circomPrime)) (hx : AffineW x) :
    IsR1CSCirc (IsZeroFeSumR.main x) := by
  unfold IsZeroFeSumR.main
  refine IsR1CSCirc.bind_out (IsR1CSCirc.witnessField _) fun n => ?_
  refine IsR1CSCirc.bind_out (IsR1CSCirc.witnessField _) fun m => ?_
  refine IsR1CSCirc.bind (IsR1CSCirc.assertZero ?_) fun _ => ?_
  · exact isR1CSRow_add_mul
      (Affine.sub (Affine.var _) (Affine.const (F := F circomPrime) 1))
      (affine_sumE hx) (Affine.var _)
  refine IsR1CSCirc.bind (IsR1CSCirc.assertZero ?_) fun _ => IsR1CSCirc.pure _
  exact isR1CSRow_mul (Affine.var _) (affine_sumE hx)

theorem isR1CS_sub_isZeroFeSumR (x : Var Emu (F circomPrime)) (hx : AffineW x) :
    IsR1CSCirc (subcircuit IsZeroFeSumR.circuit x) :=
  IsR1CSCirc.subcircuit (fun n => isR1CS_isZeroFeSumR x hx n)

theorem affine_sub_isZeroFeSumR (x : Var Emu (F circomPrime)) (n : ℕ) :
    Affine ((subcircuit IsZeroFeSumR.circuit x).output n) := by
  simp only [circuit_norm, subcircuit, IsZeroFeSumR.circuit, IsZeroFeSumR.elaborated]
  exact Affine.var _

end Cost
end Solution.Secp256k1ScalarMul
