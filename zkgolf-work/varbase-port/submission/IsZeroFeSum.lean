import Solution.Secp256k1ScalarMul.Params
import Solution.Secp256k1ScalarMul.IsZeroFe
import Solution.Secp256k1ScalarMul.IsZeroFeTheorems
import Challenge.Utils.ComputableWitnessLemmas
import Clean.Gadgets.IsZeroField

namespace Solution.Secp256k1ScalarMul
namespace IsZeroFeSum

def main (x : Var Emu (F circomPrime)) :
    Circuit (F circomPrime) (Expression (F circomPrime)) := do
  let z ← subcircuit Gadgets.IsZeroField.circuit (x[0] + x[1] + x[2] + x[3])
  return z

instance elaborated : ElaboratedCircuit (F circomPrime) Emu field main := by
  elaborate_circuit

def Assumptions (x : Emu (F circomPrime)) : Prop :=
  ∀ i : Fin numLimbs, (x[i.val]'i.isLt).val < 3 * 2 ^ limbBits

theorem sum_field_eq_zero_iff_value (x : Emu (F circomPrime))
    (hbound : ∀ i : Fin numLimbs, (x[i.val]'i.isLt).val < 3 * 2 ^ limbBits) :
    (x[0] + x[1] + x[2] + x[3] : F circomPrime) = 0 ↔ BigInt.value limbBits x = 0 := by
  rw [BigInt.value_eq_zero_iff]
  have hb0 : (x[0]).val < 3 * 2 ^ limbBits := hbound 0
  have hb1 : (x[1]).val < 3 * 2 ^ limbBits := hbound 1
  have hb2 : (x[2]).val < 3 * 2 ^ limbBits := hbound 2
  have hb3 : (x[3]).val < 3 * 2 ^ limbBits := hbound 3
  constructor
  · intro hsum
    set S : ℕ := (x[0]).val + (x[1]).val + (x[2]).val + (x[3]).val with hS
    have hScast : ((S : ℕ) : F circomPrime) = x[0] + x[1] + x[2] + x[3] := by
      rw [hS]; push_cast; rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val,
        ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    have hcast : ((S : ℕ) : F circomPrime) = 0 := by rw [hScast]; exact hsum
    have hdvd : circomPrime ∣ S := (ZMod.natCast_eq_zero_iff _ _).mp hcast
    have hbig : 4 * (3 * 2 ^ limbBits) < circomPrime := by decide
    have hSlt : S < circomPrime := by rw [hS]; omega
    have hS0 : S = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hSlt
    have hv0 : (x[0]).val = 0 := by rw [hS] at hS0; omega
    have hv1 : (x[1]).val = 0 := by rw [hS] at hS0; omega
    have hv2 : (x[2]).val = 0 := by rw [hS] at hS0; omega
    have hv3 : (x[3]).val = 0 := by rw [hS] at hS0; omega
    have hx0 : x[0] = 0 := (ZMod.val_eq_zero _).mp hv0
    have hx1 : x[1] = 0 := (ZMod.val_eq_zero _).mp hv1
    have hx2 : x[2] = 0 := (ZMod.val_eq_zero _).mp hv2
    have hx3 : x[3] = 0 := (ZMod.val_eq_zero _).mp hv3
    intro i
    fin_cases i
    · simpa using hx0
    · simpa using hx1
    · simpa using hx2
    · simpa using hx3
  · intro hall
    have hx0 : x[0] = (0 : F circomPrime) := by simpa using hall 0
    have hx1 : x[1] = (0 : F circomPrime) := by simpa using hall 1
    have hx2 : x[2] = (0 : F circomPrime) := by simpa using hall 2
    have hx3 : x[3] = (0 : F circomPrime) := by simpa using hall 3
    rw [hx0, hx1, hx2, hx3]; ring

def Spec (x : Emu (F circomPrime)) (out : F circomPrime) : Prop :=
  out = if BigInt.value limbBits x = 0 then 1 else 0

theorem soundness :
    Soundness (Input := Emu) (Output := field) (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [Gadgets.IsZeroField.circuit, Gadgets.IsZeroField.Assumptions,
    Gadgets.IsZeroField.Spec]
  have hx : ∀ (i : ℕ) (hi : i < 4), Expression.eval env input_var[i] = input[i] := by
    intro i hi
    rw [← h_input, Vector.getElem_map]
  have e0 : Expression.eval env input_var[0] = input[0] := hx 0 (by omega)
  have e1 : Expression.eval env input_var[1] = input[1] := hx 1 (by omega)
  have e2 : Expression.eval env input_var[2] = input[2] := hx 2 (by omega)
  have e3 : Expression.eval env input_var[3] = input[3] := hx 3 (by omega)
  simp only [e0, e1, e2, e3, sum_field_eq_zero_iff_value input h_assumptions] at h_holds
  exact h_holds

theorem completeness :
    Completeness (Input := Emu) (Output := field) (F circomPrime) main Assumptions := by
  circuit_proof_start [Gadgets.IsZeroField.circuit, Gadgets.IsZeroField.Assumptions,
    Gadgets.IsZeroField.Spec]

def circuit : FormalCircuit (F circomPrime) Emu field where
  main := main
  elaborated := elaborated
  Assumptions := Assumptions
  Spec := Spec
  soundness := soundness
  completeness := completeness

private lemma input_limb_stable {input : Var Emu (F circomPrime)} {k : ℕ} (hk : k < numLimbs)
    {env env' : ProverEnvironment (F circomPrime)}
    (h : eval env input = eval env' input) :
    eval env input[k] = eval env' input[k] := by
  have hmap := emu_map_eval_eq_of_eval_eq h
  have hget : (input.map (Expression.eval env.toEnvironment))[k] =
      (input.map (Expression.eval env'.toEnvironment))[k] := by rw [hmap]
  simp only [Vector.getElem_map] at hget
  rw [CircuitType.eval_var_field_prover, CircuitType.eval_var_field_prover]
  exact hget

private lemma input_sum_stable {input : Var Emu (F circomPrime)}
    {env env' : ProverEnvironment (F circomPrime)}
    (h : eval env input = eval env' input) :
    eval env (input[0] + input[1] + input[2] + input[3] : Var field (F circomPrime))
      = eval env' (input[0] + input[1] + input[2] + input[3] : Var field (F circomPrime)) := by
  have h0 := input_limb_stable (input := input) (k := 0) (by decide) h
  have h1 := input_limb_stable (input := input) (k := 1) (by decide) h
  have h2 := input_limb_stable (input := input) (k := 2) (by decide) h
  have h3 := input_limb_stable (input := input) (k := 3) (by decide) h
  rw [CircuitType.eval_var_field_prover, CircuitType.eval_var_field_prover]
  rw [CircuitType.eval_var_field_prover, CircuitType.eval_var_field_prover] at h0 h1 h2 h3
  simp only [Expression.eval]
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
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.pure_structuralComputableWitnesses_iff,
    and_true]
  exact Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses
    Gadgets.IsZeroField.circuit input (input[0] + input[1] + input[2] + input[3]) offset
    (fun _ _ h => input_sum_stable h) IsZeroFe.isZeroFieldComputableWitnesses env env'

theorem computableWitness : ∀ n input,
    ProverEnvironment.OnlyAccessedBelow n
      (fun env : ProverEnvironment (F circomPrime) => eval env input) →
    Circuit.ComputableWitnesses (main input) n :=
  Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnesses_implies
    (circuit := circuit.base) computableWitnesses

lemma eval_output_of_agreesBelow (x : Var Emu (F circomPrime)) {offset k : ℕ}
    {env env' : ProverEnvironment (F circomPrime)}
    (h_agree : env.AgreesBelow k env') (hk : offset + 2 ≤ k) :
    eval env ((main x).output offset) = eval env' ((main x).output offset) := by
  rw [CircuitType.eval_var_field_prover, CircuitType.eval_var_field_prover]
  simp only [main, circuit_norm, Gadgets.IsZeroField.circuit]
  exact h_agree (offset + 1) (by omega)

end IsZeroFeSum
end Solution.Secp256k1ScalarMul
