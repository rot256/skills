import Clean.Circuit
import Clean.Utils.Bits
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Challenge.Utils.ComputableWitnessLemmas



namespace Solution.Secp256k1ScalarMul
namespace RangeCheck

open Utils.Bits

section
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2)]


def main (n : ℕ) (x : Expression (F p)) : Circuit (F p) Unit := do
  let bits ← witnessVector (n - 1) (fun env => fieldToBits (n - 1) (x.eval env))
  Circuit.forEach bits (fun b => assertZero (b * (b - 1)))
  let top := (((2 ^ (n - 1) : ℕ) : F p)⁻¹ : F p) * (x - fieldFromBitsExpr bits)
  assertZero (top * (top - 1))

instance elaborated (n : ℕ) : ElaboratedCircuit (F p) field unit (main n) := by
  elaborate_circuit

def Assumptions (_x : F p) : Prop := True

def Spec (n : ℕ) (x : F p) : Prop := x.val < 2 ^ n

private theorem pow_pred_lt {n : ℕ} (hn : 2 ^ n < p) :
    2 ^ (n - 1) < p := by
  exact lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le n 1)) hn

private theorem pow_pred_ne_zero {n : ℕ} (hn : 2 ^ n < p) :
    (((2 ^ (n - 1) : ℕ) : F p) ≠ 0) := by
  intro h
  have hval : (((2 ^ (n - 1) : ℕ) : F p).val) = 2 ^ (n - 1) :=
    ZMod.val_natCast_of_lt (pow_pred_lt hn)
  rw [h, ZMod.val_zero] at hval
  have hpos : 0 < 2 ^ (n - 1) := Nat.two_pow_pos _
  omega

private theorem two_mul_pow_pred {n : ℕ} (hpos : 1 ≤ n) :
    2 * 2 ^ (n - 1) = 2 ^ n := by
  rw [Nat.mul_comm, ← Nat.pow_succ]
  congr 1
  omega

theorem soundness (n : ℕ) (hn : 2 ^ n < p) (hpos : 1 ≤ n) :
    FormalAssertion.Soundness (Input := field) (F p) (main n) Assumptions (Spec n) := by
  circuit_proof_start [main, Spec]
  obtain ⟨h_bool, h_eq⟩ := h_holds
  set bit_vars : Vector (Expression (F p)) (n - 1) :=
    Vector.mapRange (n - 1) (fun i => var ⟨i₀ + i⟩) with hbv
  have hval : ∀ (i : ℕ) (hi : i < n - 1), (bit_vars.map env)[i] = env.get (i₀ + i) := by
    intro i hi
    simp only [hbv, Vector.getElem_map, Vector.getElem_mapRange]
    rfl
  have h_bits : ∀ (i : ℕ) (hi : i < n - 1),
      (bit_vars.map env)[i] = 0 ∨ (bit_vars.map env)[i] = 1 := by
    intro i hi
    rw [hval i hi]
    rcases mul_eq_zero.mp (h_bool ⟨i, hi⟩) with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (add_neg_eq_zero.mp h1)
  have hE : Expression.eval env (fieldFromBitsExpr bit_vars)
      = fieldFromBits (bit_vars.map env) := fieldFromBits_eval bit_vars
  set L : F p := fieldFromBits (bit_vars.map env) with hL
  have hLlt : L.val < 2 ^ (n - 1) := fieldFromBits_lt _ h_bits
  rw [hE] at h_eq
  have hbase := pow_pred_ne_zero hn
  rcases mul_eq_zero.mp h_eq with h | h
  · have hin : input = L := by
      rcases mul_eq_zero.mp h with h0 | h0
      · exact absurd h0 (inv_ne_zero hbase)
      · linear_combination h0
    rw [hin]
    exact lt_of_lt_of_le hLlt (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le n 1))
  · have hin : input = L + ((2 ^ (n - 1) : ℕ) : F p) := by
      have h1 : (((2 ^ (n - 1) : ℕ) : F p)⁻¹ : F p) * (input + -L) = 1 := by
        linear_combination h
      have h2 : ((2 ^ (n - 1) : ℕ) : F p) *
          ((((2 ^ (n - 1) : ℕ) : F p)⁻¹ : F p) * (input + -L))
          = ((2 ^ (n - 1) : ℕ) : F p) := by
        rw [h1, mul_one]
      rw [← mul_assoc, mul_inv_cancel₀ hbase, one_mul] at h2
      linear_combination h2
    have hsum_lt : L.val + 2 ^ (n - 1) < 2 ^ n := by
      rw [← two_mul_pow_pred hpos]
      omega
    have hcast : input = ((L.val + 2 ^ (n - 1) : ℕ) : F p) := by
      rw [hin]
      push_cast
      rw [ZMod.natCast_zmod_val]
    rw [hcast, ZMod.val_cast_of_lt (lt_trans hsum_lt hn)]
    exact hsum_lt

theorem completeness (n : ℕ) (hn : 2 ^ n < p) (hpos : 1 ≤ n) :
    FormalAssertion.Completeness (Input := field) (F p) (main n) Assumptions (Spec n) := by
  circuit_proof_start [main, Spec]
  set bit_vars : Vector (Expression (F p)) (n - 1) :=
    Vector.mapRange (n - 1) (fun i => var ⟨i₀ + i⟩) with hbv
  refine ⟨?_, ?_⟩
  · intro i
    rw [h_env i]
    rcases @fieldToBits_bits p _ (n - 1) input i.val i.isLt with h0 | h1
    · rw [h0]; ring
    · rw [h1]; ring
  · set x : F p := input with hx
    set base : ℕ := 2 ^ (n - 1) with hbaseNat
    have hmap : bit_vars.map env.toEnvironment = fieldToBits (n - 1) x := by
      apply Vector.ext
      intro i hi
      rw [hbv, Vector.getElem_map, Vector.getElem_mapRange]
      simpa using h_env ⟨i, hi⟩
    set v : ℕ := x.val with hv
    have hE0 : Expression.eval env.toEnvironment (fieldFromBitsExpr bit_vars)
        = fieldFromBits (bit_vars.map env.toEnvironment) := fieldFromBits_eval bit_vars
    have hE : Expression.eval env.toEnvironment (fieldFromBitsExpr bit_vars)
        = ((v % base : ℕ) : F p) := by
      rw [hE0, hmap, fieldFromBits_fieldToBits_mod, hbaseNat]
    rw [hE]
    have hbaseF := pow_pred_ne_zero hn
    have hinput : x = ((base * (v / base) + v % base : ℕ) : F p) := by
      rw [show base * (v / base) + v % base = v from Nat.div_add_mod v base, hv,
        ZMod.natCast_zmod_val]
    have htop : (((2 ^ (n - 1) : ℕ) : F p)⁻¹ : F p) *
          (x + -((v % base : ℕ) : F p))
        = ((v / base : ℕ) : F p) := by
      rw [hinput]
      have hbaseF' : ((base : F p) ≠ 0) := by
        rw [hbaseNat]
        exact hbaseF
      change ((base : F p)⁻¹ : F p) *
          (((base * (v / base) + v % base : ℕ) : F p) + -((v % base : ℕ) : F p))
        = ((v / base : ℕ) : F p)
      push_cast
      field_simp [hbaseF']
      ring
    rw [htop]
    have hq_lt : v / base < 2 := by
      apply Nat.div_lt_of_lt_mul
      rw [hbaseNat, Nat.mul_comm, two_mul_pow_pred hpos]
      rw [hv]
      exact h_spec
    have hq : v / base = 0 ∨ v / base = 1 := by
      rcases Nat.eq_zero_or_pos (v / base) with h0 | hposq
      · exact Or.inl h0
      · exact Or.inr (by omega)
    rcases hq with h | h <;> rw [h] <;> norm_num

def circuit (n : ℕ) (hn : 2 ^ n < p) (hpos : 1 ≤ n) : FormalAssertion (F p) field where
  main := main n
  elaborated := elaborated n
  Assumptions := Assumptions
  Spec := Spec n
  soundness := soundness n hn hpos
  completeness := completeness n hn hpos

theorem computableWitnesses (n : ℕ) (hn : 2 ^ n < p) (hpos : 1 ≤ n) :
    (circuit n hn hpos).ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition input env env')
    ((main n input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.witnessVector_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.forEach_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.assertZero_structuralComputableWitnesses_iff,
    and_true]
  and_intros
  · intro _ h_input
    rw [CircuitType.eval_expression_prover_to_verifier (M := field),
      CircuitType.eval_expression_prover_to_verifier (M := field)] at h_input
    have h_input_expr :
        Expression.eval env.toEnvironment input = Expression.eval env'.toEnvironment input := by
      simpa only [CircuitType.eval_var_field] using h_input
    exact congrArg (fieldToBits (n - 1)) h_input_expr
  · intro _
    trivial

end

end RangeCheck
end Solution.Secp256k1ScalarMul
