import Solution.Secp256k1ScalarMul.Theorems
import Solution.Secp256k1ScalarMul.Params
import Solution.Secp256k1ScalarMul.RangeCheck
import Challenge.Utils.ComputableWitnessLemmas

/-!
# Re-limbing a 64-bit `Emu` value into eight 32-bit limbs, for free

`Normalize` proves `x_i < 2^64` by a 63-bit affine bit decomposition of each of
the four limbs: `4 · (63 allocations + 64 constraints) = 252/256`.

This gadget proves *the same thing* at *exactly the same cost* while
additionally **returning** the eight 32-bit limbs of `x`: per 64-bit limb it
witnesses the low half (1 allocation), range-checks it to 32 bits (31/32),
defines the high half as the free affine expression `(x_i − lo_i)/2^32`, and
range-checks that to 32 bits (31/32) — `1 + 31 + 31 = 63` allocations and
`32 + 32 = 64` constraints per limb, identical to `Normalize`.

The point of the eight-limb view is the modular-multiplication certificate:
`p = 2^256 − 2^32 − 977` has a *limb-aligned* fold constant in base `2^32`
(`cFold = 977 + 1·2^32`, two tiny digits) whereas in base `2^64` it is a single
33-bit digit.  The fold constant enters the carry width linearly, so a
certificate run on 32-bit limbs needs a 39-bit quotient and a 50-bit carry
instead of 69 and 101 — see `MulModFold32`.
-/

namespace Solution.Secp256k1ScalarMul
namespace Split32

open Solution.Secp256k1ScalarMul.Limbs

/-- Eight 32-bit limbs. -/
@[reducible] def Emu32 : TypeMap := BigInt 8

/-- `2^32` as a field constant. -/
def twoPow32 : F circomPrime := ((2 ^ 32 : ℕ) : F circomPrime)

lemma twoPow32_val : twoPow32.val = 2 ^ 32 :=
  ZMod.val_natCast_of_lt (by decide)

lemma twoPow32_ne_zero : twoPow32 ≠ 0 := by
  intro h
  have := twoPow32_val
  rw [h, ZMod.val_zero] at this
  exact absurd this.symm (by decide)

/-- The low 32 bits of the `i`-th limb, as a prover value. -/
def loCompute (x : Var Emu (F circomPrime)) (i : ℕ) (hi : i < numLimbs)
    (env : ProverEnvironment (F circomPrime)) : F circomPrime :=
  (((Expression.eval env.toEnvironment (x[i]'hi)).val % 2 ^ 32 : ℕ) : F circomPrime)

/-- The high half, as a free affine expression. -/
def hiExpr (x : Var Emu (F circomPrime)) (i : ℕ) (hi : i < numLimbs)
    (lo : Expression (F circomPrime)) : Expression (F circomPrime) :=
  Expression.const (twoPow32⁻¹) * ((x[i]'hi) - lo)

def main (x : Var Emu (F circomPrime)) :
    Circuit (F circomPrime) (Var Emu32 (F circomPrime)) := do
  let l0 ← witnessField (loCompute x 0 (by decide))
  RangeCheck.circuit 32 (by decide) (by decide) l0
  let h0 := hiExpr x 0 (by decide) l0
  RangeCheck.circuit 32 (by decide) (by decide) h0
  let l1 ← witnessField (loCompute x 1 (by decide))
  RangeCheck.circuit 32 (by decide) (by decide) l1
  let h1 := hiExpr x 1 (by decide) l1
  RangeCheck.circuit 32 (by decide) (by decide) h1
  let l2 ← witnessField (loCompute x 2 (by decide))
  RangeCheck.circuit 32 (by decide) (by decide) l2
  let h2 := hiExpr x 2 (by decide) l2
  RangeCheck.circuit 32 (by decide) (by decide) h2
  let l3 ← witnessField (loCompute x 3 (by decide))
  RangeCheck.circuit 32 (by decide) (by decide) l3
  let h3 := hiExpr x 3 (by decide) l3
  RangeCheck.circuit 32 (by decide) (by decide) h3
  return #v[l0, h0, l1, h1, l2, h2, l3, h3]

instance elaborated : ElaboratedCircuit (F circomPrime) Emu Emu32 main := by
  elaborate_circuit

def Assumptions (x : Emu (F circomPrime)) : Prop := BigInt.Normalized limbBits x

def Spec (x : Emu (F circomPrime)) (out : Emu32 (F circomPrime)) : Prop :=
  BigInt.Normalized 32 out ∧ BigInt.value 32 out = BigInt.value limbBits x ∧
    BigInt.Normalized limbBits x


/-! ## Correctness -/

lemma hiExpr_eval (env : Environment (F circomPrime)) (x : Var Emu (F circomPrime))
    (i : ℕ) (hi : i < numLimbs) (lo : Expression (F circomPrime)) :
    Expression.eval env (hiExpr x i hi lo)
      = twoPow32⁻¹ * (Expression.eval env (x[i]'hi) - Expression.eval env lo) := by
  simp [hiExpr, Expression.eval, sub_eq_add_neg]

/-- The defining field identity of the split: it holds unconditionally. -/
lemma split_identity (env : Environment (F circomPrime)) (x : Var Emu (F circomPrime))
    (i : ℕ) (hi : i < numLimbs) (lo : Expression (F circomPrime)) :
    Expression.eval env (x[i]'hi)
      = Expression.eval env lo + twoPow32 * Expression.eval env (hiExpr x i hi lo) := by
  rw [hiExpr_eval, ← mul_assoc, mul_inv_cancel₀ twoPow32_ne_zero, one_mul]
  ring

/-- Natural-number form of the split, given both halves are 32-bit. -/
lemma limb_split {xv lo hi : F circomPrime} (hlo : lo.val < 2 ^ 32) (hhi : hi.val < 2 ^ 32)
    (h : xv = lo + twoPow32 * hi) : xv.val = lo.val + 2 ^ 32 * hi.val := by
  have hb : 2 ^ 32 * hi.val < 2 ^ 64 := by
    have hle : hi.val ≤ 2 ^ 32 - 1 := by omega
    calc 2 ^ 32 * hi.val ≤ 2 ^ 32 * (2 ^ 32 - 1) := Nat.mul_le_mul_left _ hle
      _ < 2 ^ 64 := by norm_num
  have hp : (2 : ℕ) ^ 64 + 2 ^ 32 < circomPrime := by decide
  have hmul : (twoPow32 * hi).val = 2 ^ 32 * hi.val := by
    rw [ZMod.val_mul_of_lt (by rw [twoPow32_val]; omega), twoPow32_val]
  rw [h, ZMod.val_add_of_lt (by rw [hmul]; omega), hmul]

lemma value32_eight (v : Vector (F circomPrime) 8) :
    BigInt.value 32 v = v[0].val + v[1].val * 2 ^ 32 + v[2].val * 2 ^ 64 + v[3].val * 2 ^ 96
      + v[4].val * 2 ^ 128 + v[5].val * 2 ^ 160 + v[6].val * 2 ^ 192 + v[7].val * 2 ^ 224 := by
  rw [BigInt.value_eq_sum]
  simp only [Fin.sum_univ_eight]
  norm_num

lemma value64_four (v : Emu (F circomPrime)) :
    BigInt.value limbBits v = v[0].val + v[1].val * 2 ^ 64 + v[2].val * 2 ^ 128
      + v[3].val * 2 ^ 192 := by
  rw [BigInt.value_eq_sum]
  simp only [Fin.sum_univ_four]
  norm_num

theorem soundness : Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [RangeCheck.circuit, RangeCheck.Assumptions, RangeCheck.Spec]
  simp only [show (32 - 1 : ℕ) = 31 from rfl] at h_holds
  obtain ⟨hl0, hh0, hl1, hh1, hl2, hh2, hl3, hh3⟩ := h_holds
  have hx : ∀ (i : ℕ) (hi : i < numLimbs), Expression.eval env (input_var[i]'hi) = input[i]'hi := by
    intro i hi
    rw [← h_input, Vector.getElem_map]
  have e0 := limb_split hl0 hh0 (split_identity env input_var 0 (by decide)
    (var (F := F circomPrime) { index := i₀ }))
  have e1 := limb_split hl1 hh1 (split_identity env input_var 1 (by decide)
    (var (F := F circomPrime) { index := i₀ + 1 + 31 + 31 }))
  have e2 := limb_split hl2 hh2 (split_identity env input_var 2 (by decide)
    (var (F := F circomPrime) { index := i₀ + 1 + 31 + 31 + 1 + 31 + 31 }))
  have e3 := limb_split hl3 hh3 (split_identity env input_var 3 (by decide)
    (var (F := F circomPrime) { index := i₀ + 1 + 31 + 31 + 1 + 31 + 31 + 1 + 31 + 31 }))
  rw [hx 0 (by decide)] at e0
  rw [hx 1 (by decide)] at e1
  rw [hx 2 (by decide)] at e2
  rw [hx 3 (by decide)] at e3
  refine ⟨?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> simpa using ‹_›
  · rw [value32_eight, value64_four]
    simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ]
    omega
  · intro i
    have hb : (2 : ℕ) ^ limbBits = 2 ^ 64 := rfl
    rw [hb]
    fin_cases i <;> [rw [Fin.getElem_fin, e0]; rw [Fin.getElem_fin, e1];
      rw [Fin.getElem_fin, e2]; rw [Fin.getElem_fin, e3]] <;> omega


lemma hi_of_lo (X : F circomPrime) :
    twoPow32⁻¹ * (X - ((X.val % 2 ^ 32 : ℕ) : F circomPrime))
      = ((X.val / 2 ^ 32 : ℕ) : F circomPrime) := by
  have h1 : ((X.val : ℕ) : F circomPrime)
      = twoPow32 * ((X.val / 2 ^ 32 : ℕ) : F circomPrime)
        + ((X.val % 2 ^ 32 : ℕ) : F circomPrime) := by
    conv_lhs => rw [← Nat.div_add_mod X.val (2 ^ 32)]
    push_cast [twoPow32]
    ring
  rw [ZMod.natCast_zmod_val] at h1
  have h2 : X - ((X.val % 2 ^ 32 : ℕ) : F circomPrime)
      = twoPow32 * ((X.val / 2 ^ 32 : ℕ) : F circomPrime) := by linear_combination h1
  rw [h2, ← mul_assoc, inv_mul_cancel₀ twoPow32_ne_zero, one_mul]

lemma completeness_limb (env : ProverEnvironment (F circomPrime)) (x : Var Emu (F circomPrime))
    (i : ℕ) (hi : i < numLimbs) (idx : ℕ)
    (hval : (Expression.eval env.toEnvironment (x[i]'hi)).val < 2 ^ 64)
    (hg : env.get idx = loCompute x i hi env) :
    (env.get idx).val < 2 ^ 32 ∧
    (Expression.eval env.toEnvironment
      (hiExpr x i hi (var (F := F circomPrime) { index := idx }))).val < 2 ^ 32 := by
  have hp32 : (2 : ℕ) ^ 32 < circomPrime := by decide
  have hlo_val : (env.get idx).val
      = (Expression.eval env.toEnvironment (x[i]'hi)).val % 2 ^ 32 := by
    rw [hg, loCompute]
    exact ZMod.val_natCast_of_lt (by
      have := Nat.mod_lt (Expression.eval env.toEnvironment (x[i]'hi)).val
        (show 0 < 2 ^ 32 by norm_num); omega)
  have hgetE : Expression.eval env.toEnvironment (var (F := F circomPrime) { index := idx })
      = env.get idx := rfl
  have hhi_eq : Expression.eval env.toEnvironment
      (hiExpr x i hi (var (F := F circomPrime) { index := idx }))
      = (((Expression.eval env.toEnvironment (x[i]'hi)).val / 2 ^ 32 : ℕ) : F circomPrime) := by
    rw [hiExpr_eval, hgetE, hg, loCompute]
    exact hi_of_lo _
  refine ⟨by rw [hlo_val]; exact Nat.mod_lt _ (by norm_num), ?_⟩
  rw [hhi_eq, ZMod.val_natCast_of_lt (by omega)]
  omega

theorem completeness : Completeness (F circomPrime) main Assumptions := by
  circuit_proof_start [RangeCheck.circuit, RangeCheck.Assumptions, RangeCheck.Spec]
  simp only [show (32 - 1 : ℕ) = 31 from rfl] at h_env ⊢
  obtain ⟨g0, g1, g2, g3⟩ := h_env
  have hx : ∀ (i : ℕ) (hi : i < numLimbs),
      (Expression.eval env.toEnvironment (input_var[i]'hi)).val < 2 ^ 64 := by
    intro i hi
    have := h_assumptions ⟨i, hi⟩
    rw [Fin.getElem_fin, ← h_input, Vector.getElem_map] at this
    exact this
  have c0 := completeness_limb env input_var 0 (by decide) _ (hx 0 (by decide)) g0
  have c1 := completeness_limb env input_var 1 (by decide) _ (hx 1 (by decide)) g1
  have c2 := completeness_limb env input_var 2 (by decide) _ (hx 2 (by decide)) g2
  have c3 := completeness_limb env input_var 3 (by decide) _ (hx 3 (by decide)) g3
  exact ⟨c0.1, c0.2, c1.1, c1.2, c2.1, c2.2, c3.1, c3.2⟩

def circuit : FormalCircuit (F circomPrime) Emu Emu32 where
  main := main
  elaborated := elaborated
  Assumptions := Assumptions
  Spec := Spec
  soundness := soundness
  completeness := completeness

open Challenge.Utils.ComputableWitnessLemmas in
open MulMod in
set_option maxHeartbeats 2000000 in
theorem computableWitnesses : circuit.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (FormalCircuitBase.computableWitnessCondition input env env') ((main input).operations offset)
  apply FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main
  have hw : ∀ (f : ProverEnvironment (F circomPrime) → F circomPrime) (o : ℕ),
      (witnessField f).localLength o = 1 := by intro f o; simp [circuit_norm]
  have hrc : ∀ (e : Expression (F circomPrime)) (o : ℕ),
      (assertion (RangeCheck.circuit 32 (by decide) (by decide)) e).localLength o = 31 := by
    intro e o; simp [circuit_norm, RangeCheck.circuit]
  have hlo : ∀ (i : ℕ) (hi : i < numLimbs) (e1 e2 : ProverEnvironment (F circomPrime)),
      eval e1 input = eval e2 input → loCompute input i hi e1 = loCompute input i hi e2 := by
    intro i hi e1 e2 h
    unfold loCompute
    rw [bigInt_getElem_eval_eq h i hi]
  have hhi : ∀ (i : ℕ) (hi : i < numLimbs) (idx : ℕ) (e1 e2 : ProverEnvironment (F circomPrime)),
      eval e1 input = eval e2 input →
      Expression.eval e1.toEnvironment (var (F := F circomPrime) { index := idx })
        = Expression.eval e2.toEnvironment (var (F := F circomPrime) { index := idx }) →
      eval e1 (hiExpr input i hi (var (F := F circomPrime) { index := idx }))
        = eval e2 (hiExpr input i hi (var (F := F circomPrime) { index := idx })) := by
    intro i hi idx e1 e2 h hv
    rw [CircuitType.eval_var_field_prover, CircuitType.eval_var_field_prover,
      hiExpr_eval, hiExpr_eval, bigInt_getElem_eval_eq h i hi, hv]
  simp only [
    Circuit.bind_structuralComputableWitnesses_iff,
    Circuit.witnessField_structuralComputableWitnesses_iff,
    FormalAssertion.assertion_structuralComputableWitnesses_iff,
    Circuit.pure_structuralComputableWitnesses_iff, and_true, hw, hrc]
  refine ⟨fun _ h => hlo 0 (by decide) _ _ h, ?_, ?_,
    fun _ h => hlo 1 (by decide) _ _ h, ?_, ?_,
    fun _ h => hlo 2 (by decide) _ _ h, ?_, ?_,
    fun _ h => hlo 3 (by decide) _ _ h, ?_, ?_⟩ <;>
  · first
    | exact FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
        (RangeCheck.circuit 32 (by decide) (by decide)) input _ _
        (by
          intro k e1 e2 hle h_agree _
          simpa [circuit_norm] using h_agree _ (by omega))
        (RangeCheck.computableWitnesses 32 (by decide) (by decide)) env env'
    | exact FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
        (RangeCheck.circuit 32 (by decide) (by decide)) input _ _
        (by
          intro k e1 e2 hle h_agree h_in
          refine hhi _ (by decide) _ _ _ h_in ?_
          exact h_agree _ (by dsimp only; omega))
        (RangeCheck.computableWitnesses 32 (by decide) (by decide)) env env'

theorem computableWitness : ∀ n (input : Var Emu (F circomPrime)),
    ProverEnvironment.OnlyAccessedBelow n
      (fun env : ProverEnvironment (F circomPrime) => eval env input) →
    Circuit.ComputableWitnesses (main input) n :=
  Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnesses_implies
    (circuit := circuit.base) computableWitnesses

end Split32
end Solution.Secp256k1ScalarMul
