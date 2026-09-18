import Clean.Circuit
import Clean.Utils.Bits
import Clean.Gadgets.Boolean
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Challenge.Utils.ComputableWitnessLemmas
import Solution.Secp256k1ScalarMul.Theorems

namespace Solution.Secp256k1ScalarMul
namespace ToBitsAffine

open Utils.Bits

variable {p : ℕ} [Fact p.Prime] [Fact (p > 2)]

def main (w : ℕ) (x : Expression (F p)) : Circuit (F p) (Var (fields (w + 1)) (F p)) := do
  let low ← witnessVector w fun env => fieldToBits w (x.eval env)
  Circuit.forEach low assertBool
  let top := (((2 ^ w : ℕ) : F p)⁻¹ : F p) * (x - fieldFromBitsExpr low)
  assertZero (top * (top - 1))
  return low.push top

instance elaborated (w : ℕ) : ElaboratedCircuit (F p) field (fields (w + 1)) (main w) := by
  elaborate_circuit

private theorem pow_lt {w : ℕ} (hn : 2 ^ (w + 1) < p) : 2 ^ w < p :=
  lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ w)) hn

private theorem pow_ne_zero' {w : ℕ} (hn : 2 ^ (w + 1) < p) :
    (((2 ^ w : ℕ) : F p) ≠ 0) := by
  intro h
  have hval : (((2 ^ w : ℕ) : F p).val) = 2 ^ w :=
    ZMod.val_natCast_of_lt (pow_lt hn)
  rw [h, ZMod.val_zero] at hval
  have hpos : 0 < 2 ^ w := Nat.two_pow_pos _
  omega

theorem fieldFromBits_push {w : ℕ} (low : Vector (F p) w) (top : F p) :
    fieldFromBits (low.push top) = fieldFromBits low + top * ((2 ^ w : ℕ) : F p) := by
  rw [fieldFromBits_succ w (low.push top)]
  have hpop : (low.push top).pop = low := by
    apply Vector.ext; intro i hi
    simp [Vector.getElem_pop', Vector.getElem_push_lt hi]
  rw [hpop, Vector.getElem_push_eq, Nat.cast_pow, Nat.cast_ofNat]

def toBitsAffine (w : ℕ) (hn : 2 ^ (w + 1) < p) : GeneralFormalCircuit (F p) field (fields (w + 1)) where
  main := main w

  ProverAssumptions (x : F p) _ _ := x.val < 2 ^ (w + 1)

  Spec (x : F p) (bits : Vector (F p) (w + 1)) _ :=
    x.val < 2 ^ (w + 1) ∧ bits = fieldToBits (w + 1) x

  soundness := by
    circuit_proof_start
    obtain ⟨h_bool, h_eq⟩ := h_holds
    set low_vars : Vector (Expression (F p)) w := Vector.mapRange w (fun i => var ⟨i₀ + i⟩) with hlv
    set low : Vector (F p) w := low_vars.map env with hlow
    set t : F p := (((2 ^ w : ℕ) : F p)⁻¹ : F p) * (input + -Expression.eval env (fieldFromBitsExpr low_vars)) with ht
    change t * (t + -1) = 0 at h_eq
    have hbase := pow_ne_zero' (w := w) hn
    have hE : Expression.eval env (fieldFromBitsExpr low_vars) = fieldFromBits low :=
      fieldFromBits_eval low_vars
    have h_low_bool : ∀ (i : ℕ) (hi : i < w), low[i] = 0 ∨ low[i] = 1 := by
      intro i hi
      have := h_bool ⟨i, hi⟩
      simp only [IsBool, hlow, hlv, Vector.getElem_map, Vector.getElem_mapRange, Expression.eval] at this ⊢
      exact this
    have h_top_bool : t = 0 ∨ t = 1 := by
      rcases mul_eq_zero.mp h_eq with h | h
      · exact Or.inl h
      · exact Or.inr (by linear_combination h)
    set bits : Vector (F p) (w + 1) := low.push t with hbits
    have h_bits : ∀ (i : ℕ) (hi : i < w + 1), bits[i] = 0 ∨ bits[i] = 1 := by
      intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
      · rw [hbits, Vector.getElem_push_lt hlt]; exact h_low_bool i hlt
      · rw [hbits, Vector.getElem_push_eq]; exact h_top_bool
    have hrecomp : fieldFromBits bits = input := by
      rw [hbits, fieldFromBits_push, ← hE, ht]
      field_simp
      ring
    have hval : input.val < 2 ^ (w + 1) := by
      rw [← hrecomp]; exact fieldFromBits_lt bits h_bits
    have htoBits : fieldToBits (w + 1) input = bits := by
      rw [← hrecomp]; exact fieldToBits_fieldFromBits hn bits h_bits
    refine ⟨hval, ?_⟩
    rw [htoBits, hbits, hlow]
    simp only [circuit_norm, Vector.map_push, hlv, ht, h_input]

  completeness := by
    circuit_proof_start
    set low_vars : Vector (Expression (F p)) w := Vector.mapRange w (fun i => var ⟨i₀ + i⟩) with hlv
    have hbase := pow_ne_zero' (w := w) hn
    refine ⟨?_, ?_⟩
    ·
      intro i
      rw [h_env i]
      rcases fieldToBits_bits (n := w) (x := input) i.val i.isLt with h | h <;>
        rw [h] <;> simp [IsBool]
    ·
      set base : ℕ := 2 ^ w with hbaseNat
      have hmap : low_vars.map env.toEnvironment = fieldToBits w input := by
        apply Vector.ext; intro i hi
        rw [hlv, Vector.getElem_map, Vector.getElem_mapRange]
        simpa using h_env ⟨i, hi⟩
      set v : ℕ := input.val with hv
      have hE0 : Expression.eval env.toEnvironment (fieldFromBitsExpr low_vars)
          = fieldFromBits (low_vars.map env.toEnvironment) := fieldFromBits_eval low_vars
      have hE : Expression.eval env.toEnvironment (fieldFromBitsExpr low_vars)
          = ((v % base : ℕ) : F p) := by
        rw [hE0, hmap, fieldFromBits_fieldToBits_mod, hbaseNat, hv]
      have htop_val : (((2 ^ w : ℕ) : F p)⁻¹ : F p) *
            (input + -Expression.eval env.toEnvironment (fieldFromBitsExpr low_vars))
          = ((v / base : ℕ) : F p) := by
        rw [hE]
        have hbaseF : ((base : F p) ≠ 0) := by rw [hbaseNat]; exact hbase
        have hinput : input = ((base * (v / base) + v % base : ℕ) : F p) := by
          rw [show base * (v / base) + v % base = v from Nat.div_add_mod v base, hv,
            ZMod.natCast_zmod_val]
        change ((base : F p)⁻¹ : F p) * (input + -((v % base : ℕ) : F p))
          = ((v / base : ℕ) : F p)
        rw [hinput]
        push_cast
        field_simp [hbaseF]
        ring
      rw [htop_val]
      have hq_lt : v / base < 2 := by
        apply Nat.div_lt_of_lt_mul
        rw [hbaseNat, ← pow_succ]
        exact h_assumptions
      set q : ℕ := v / base with hq_def
      clear_value q
      rcases (by omega : q = 0 ∨ q = 1) with h | h <;>
        rw [h] <;> norm_num

theorem computableWitnesses (w : ℕ) (hn : 2 ^ (w + 1) < p) :
    (toBitsAffine (p := p) w hn).base.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition input env env')
    (((toBitsAffine (p := p) w hn).main input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold toBitsAffine main
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.witnessVector_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.forEach_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.assertZero_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.pure_structuralComputableWitnesses_iff,
    and_true]
  and_intros
  · intro _ h_input
    rw [CircuitType.eval_expression_prover_to_verifier (M := field),
      CircuitType.eval_expression_prover_to_verifier (M := field)] at h_input
    have h_input_expr :
        Expression.eval env.toEnvironment input = Expression.eval env'.toEnvironment input := by
      simpa only [CircuitType.eval_var_field] using h_input
    exact congrArg (Utils.Bits.fieldToBits w) h_input_expr
  · intro i
    apply Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
    · intro k env env' hk h_agree _
      rw [CircuitType.eval_expression_prover_to_verifier (M := field),
        CircuitType.eval_expression_prover_to_verifier (M := field)]
      rw [show eval env.toEnvironment
            ((witnessVector w fun env =>
                Utils.Bits.fieldToBits w (Expression.eval env.toEnvironment input)).output
          offset)[i.val] =
            env.get (offset + i.val) by
          rw [CircuitType.eval_expression (M := field)]
          simp [Circuit.witnessVector, Circuit.output,
            ProvableType.eval, explicit_provable_type, size, Vector.getElem_mapRange,
            Expression.eval],
        show eval env'.toEnvironment
            ((witnessVector w fun env =>
                Utils.Bits.fieldToBits w (Expression.eval env.toEnvironment input)).output
              offset)[i.val] =
            env'.get (offset + i.val) by
          rw [CircuitType.eval_expression (M := field)]
          simp [Circuit.witnessVector, Circuit.output,
            ProvableType.eval, explicit_provable_type, size, Vector.getElem_mapRange,
            Expression.eval]]
      exact h_agree (offset + i.val) (by
        have hi : i.val < w := i.isLt
        have hbase : offset + w ≤ k := by
          simpa [Circuit.localLength] using hk
        omega)
    · exact assertBoolComputableWitnesses

end ToBitsAffine
end Solution.Secp256k1ScalarMul
