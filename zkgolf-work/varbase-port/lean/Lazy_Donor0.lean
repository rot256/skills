import Mathlib.Data.Nat.Size
import Clean.Circuit.Basic
import Clean.Circuit.Loops
import Clean.Gadgets.Bits
import Clean.Gadgets.Equality
import Clean.Utils.Tactics.ProvableStructDeriving
import Challenge.Utils.ComputableWitnessLemmas
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Basic
import Challenge.Specs.Secp256k1
import Challenge.Instances.Secp256k1ScalarMulFixedBase.Interface
import Challenge.Instances.Secp256k1ScalarMul.Interface
import Clean.Gadgets.IsZeroField
import Challenge.Utils.CostR1CS
import Clean.Circuit
import Clean.Utils.Bits
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Clean.Gadgets.Boolean
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Intervals


-- Adapted donor module: Theorems
section DonorFile0_0

namespace Solution.Secp256k1ScalarMulFixedBase.Limbs

def fromLimbs (limbBits : ℕ) (limbs : List ℕ) : ℕ :=
  limbs.foldr (fun limb acc => limb + acc * 2 ^ limbBits) 0

end Solution.Secp256k1ScalarMulFixedBase.Limbs

namespace Solution.Secp256k1ScalarMulFixedBase
open Solution.Secp256k1ScalarMulFixedBase.Limbs

section ComputableWitnessHelpers
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2)]

omit [Fact (p > 2)] in
theorem assertBoolComputableWitnesses :
    (assertBool (p := p)).ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition input env env')
    (((assertBool (p := p)).main input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold assertBool
  simp only [Challenge.Utils.ComputableWitnessLemmas.Circuit.assertZero_structuralComputableWitnesses_iff]

omit [Fact (p > 2)] in
private theorem equalityComputableWitnesses (M : TypeMap) [ProvableType M] :
    (Gadgets.Equality.circuit (F := F p) M).ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition input env env')
    (((Gadgets.Equality.circuit (F := F p) M).main input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold Gadgets.Equality.circuit Gadgets.Equality.main
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.forEach_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.assertZero_structuralComputableWitnesses_iff]
  intro _
  trivial

omit [Fact (p > 2)] in
theorem rangeCheckComputableWitnesses (n : ℕ) (hn : 2 ^ n < p) :
    (Gadgets.ToBits.rangeCheck (p := p) n hn).ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition input env env')
    (((Gadgets.ToBits.rangeCheck (p := p) n hn).main input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold Gadgets.ToBits.rangeCheck
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.pure_structuralComputableWitnesses_iff,
    and_true]
  unfold subcircuitWithAssertion
  simp only [Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.StructuralComputableWitnesses]
  constructor
  · apply Challenge.Utils.ComputableWitnessLemmas.GeneralFormalCircuit.subcircuit_flatStructuralComputableWitnesses
    · intro _ _ h_input
      exact h_input
    · intro offset input env env'
      change Operations.forAllFlat offset
        (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition input env env')
        (((Gadgets.ToBits.toBits (p := p) n hn).main input).operations offset)
      apply
        Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
      unfold Gadgets.ToBits.toBits Gadgets.ToBits.main
      simp only [
        Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
        Challenge.Utils.ComputableWitnessLemmas.Circuit.witnessVector_structuralComputableWitnesses_iff,
        Challenge.Utils.ComputableWitnessLemmas.Circuit.forEach_structuralComputableWitnesses_iff,
        Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_structuralComputableWitnesses_iff,
        Challenge.Utils.ComputableWitnessLemmas.Circuit.pure_structuralComputableWitnesses_iff,
      and_true]
      and_intros
      · intro _ h_input
        rw [CircuitType.eval_expression_prover_to_verifier (M := field),
          CircuitType.eval_expression_prover_to_verifier (M := field)] at h_input
        have h_input_expr :
            Expression.eval env.toEnvironment input = Expression.eval env'.toEnvironment input := by
          simpa only [CircuitType.eval_var_field] using h_input
        exact congrArg (Utils.Bits.fieldToBits n) h_input_expr
      · intro i
        apply Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
        · intro k env env' hk h_agree _
          rw [CircuitType.eval_expression_prover_to_verifier (M := field),
            CircuitType.eval_expression_prover_to_verifier (M := field)]
          rw [show eval env.toEnvironment
                ((witnessVector n fun env =>
                    Utils.Bits.fieldToBits n (Expression.eval env.toEnvironment input)).output
              offset)[i.val] =
                env.get (offset + i.val) by
              rw [CircuitType.eval_expression (M := field)]
              simp [Circuit.witnessVector, Circuit.output,
                ProvableType.eval, explicit_provable_type, size, Vector.getElem_mapRange,
                Expression.eval],
            show eval env'.toEnvironment
                ((witnessVector n fun env =>
                    Utils.Bits.fieldToBits n (Expression.eval env.toEnvironment input)).output
                  offset)[i.val] =
                env'.get (offset + i.val) by
              rw [CircuitType.eval_expression (M := field)]
              simp [Circuit.witnessVector, Circuit.output,
                ProvableType.eval, explicit_provable_type, size, Vector.getElem_mapRange,
                Expression.eval]]
          exact h_agree (offset + i.val) (by
              have hi : i.val < n := i.isLt
              have hbase : offset + n ≤ k := by
                simpa [Circuit.localLength] using hk
              omega)
        · exact assertBoolComputableWitnesses
      · rw [FormalAssertion.toSubcircuit]
        simp only [Operations.toNested_toFlat]
        apply Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
        · intro k env env' hk h_agree h_input
          simp only [circuit_norm]
          apply Prod.ext
          · rw [CircuitType.eval_expression_prover_to_verifier (M := field),
              CircuitType.eval_expression_prover_to_verifier (M := field)] at h_input
            dsimp
            simpa only [CircuitType.eval_var_field] using h_input
          · dsimp
            change Expression.eval env.toEnvironment
                (Utils.Bits.fieldFromBitsExpr (Vector.mapRange n fun i => var { index := offset + i })) =
              Expression.eval env'.toEnvironment
                (Utils.Bits.fieldFromBitsExpr (Vector.mapRange n fun i => var { index := offset + i }))
            change env.toEnvironment
                (Utils.Bits.fieldFromBitsExpr (Vector.mapRange n fun i => var { index := offset + i })) =
              env'.toEnvironment
                (Utils.Bits.fieldFromBitsExpr (Vector.mapRange n fun i => var { index := offset + i }))
            rw [Utils.Bits.fieldFromBits_eval, Utils.Bits.fieldFromBits_eval]
            apply Utils.Bits.fieldFromBits_eq
            intro i
            simp [Vector.getElem_map, Vector.getElem_mapRange, Expression.eval]
            exact h_agree (offset + i.val) (by
              have hi : i.val < n := i.isLt
              have hbase : offset + n ≤ k := by
                have hw :
                    (witnessVector n fun env =>
                      Utils.Bits.fieldToBits n (Expression.eval env.toEnvironment input)).localLength
                      offset = n := by
                  simp [Circuit.witnessVector, Circuit.localLength, Operations.localLength]
                omega
              omega)
        · exact equalityComputableWitnesses id
      · trivial
  · trivial

end ComputableWitnessHelpers

@[reducible] def BigInt (m : ℕ) : TypeMap := fields m

namespace BigInt

section
variable {p : ℕ} [Fact p.Prime] {m : ℕ}

def value (B : ℕ) (x : BigInt m (F p)) : ℕ :=
  Solution.Secp256k1ScalarMulFixedBase.Limbs.fromLimbs B (x.toList.map ZMod.val)

def Normalized (B : ℕ) (x : BigInt m (F p)) : Prop := ∀ i : Fin m, (x[i]).val < 2 ^ B

end

end BigInt

section
variable {p : ℕ} [Fact p.Prime]
variable {m : ℕ}

theorem fromLimbs_injective {B : ℕ} :
    ∀ {l₁ l₂ : List ℕ}, l₁.length = l₂.length →
      (∀ x ∈ l₁, x < 2 ^ B) → (∀ x ∈ l₂, x < 2 ^ B) →
      Solution.Secp256k1ScalarMulFixedBase.Limbs.fromLimbs B l₁ = Solution.Secp256k1ScalarMulFixedBase.Limbs.fromLimbs B l₂ → l₁ = l₂ := by
  intro l₁
  induction l₁ with
  | nil =>
    intro l₂ hlen _ _ _
    exact (List.length_eq_zero_iff.mp hlen.symm).symm
  | cons a t ih =>
    intro l₂ hlen h₁ h₂ hval
    match l₂ with
    | b :: s =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      have ha : a < 2 ^ B := h₁ a (List.mem_cons_self ..)
      have hb : b < 2 ^ B := h₂ b (List.mem_cons_self ..)
      simp only [Solution.Secp256k1ScalarMulFixedBase.Limbs.fromLimbs, List.foldr_cons] at hval ⊢

      have hpow : 0 < 2 ^ B := Nat.two_pow_pos B
      have hmod : a = b := by
        have := congrArg (· % 2 ^ B) hval
        simp only [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ha,
          Nat.mod_eq_of_lt hb] at this
        exact this
      subst hmod
      have hrest : (t.foldr (fun limb acc => limb + acc * 2 ^ B) 0)
          = (s.foldr (fun limb acc => limb + acc * 2 ^ B) 0) := by
        have := congrArg (· / 2 ^ B) hval
        simp only [Nat.add_mul_div_right _ _ hpow,
          Nat.div_eq_of_lt ha, Nat.zero_add] at this
        exact this
      have := ih hlen (fun x hx => h₁ x (List.mem_cons_of_mem _ hx))
        (fun x hx => h₂ x (List.mem_cons_of_mem _ hx)) hrest
      rw [this]

theorem BigInt.value_inj {B : ℕ} {a b : BigInt m (F p)}
    (ha : a.Normalized B) (hb : b.Normalized B)
    (h : a.value B = b.value B) : a = b := by

  have hlists : a.toList.map ZMod.val = b.toList.map ZMod.val := by
    apply fromLimbs_injective (B := B)
    · simp only [List.length_map, Vector.length_toList]
    · intro x hx
      simp only [List.mem_map, Vector.mem_toList_iff] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      obtain ⟨i, hi, rfl⟩ := Vector.getElem_of_mem hy
      exact ha ⟨i, hi⟩
    · intro x hx
      simp only [List.mem_map, Vector.mem_toList_iff] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      obtain ⟨i, hi, rfl⟩ := Vector.getElem_of_mem hy
      exact hb ⟨i, hi⟩
    · exact h

  have : a.toList = b.toList :=
    List.map_injective_iff.mpr (ZMod.val_injective p) hlists
  exact Vector.toList_inj.mp this

theorem fromLimbs_eq_sum {B : ℕ} (l : List ℕ) :
    Solution.Secp256k1ScalarMulFixedBase.Limbs.fromLimbs B l = ∑ i : Fin l.length, l[i] * 2 ^ (B * i.val) := by
  induction l with
  | nil => simp [Solution.Secp256k1ScalarMulFixedBase.Limbs.fromLimbs]
  | cons a t ih =>
    have hrhs : (∑ i : Fin (a :: t).length, (a :: t)[i] * 2 ^ (B * i.val))
        = a + (∑ i : Fin t.length, t[i] * 2 ^ (B * i.val)) * 2 ^ B := by
      show (∑ i : Fin (t.length + 1), (a :: t)[i] * 2 ^ (B * i.val)) = _
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, Nat.mul_zero, pow_zero, Nat.mul_one,
        Fin.val_succ]
      rw [Finset.sum_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      have hidx : (a :: t)[i.succ] = t[i] := by
        simp [List.getElem_cons_succ]
      rw [hidx, Nat.mul_add, Nat.mul_one, pow_add]
      ring
    rw [show Solution.Secp256k1ScalarMulFixedBase.Limbs.fromLimbs B (a :: t)
        = a + Solution.Secp256k1ScalarMulFixedBase.Limbs.fromLimbs B t * 2 ^ B from rfl, ih]
    exact hrhs.symm

omit [Fact (Nat.Prime p)] in

theorem BigInt.value_eq_sum {B : ℕ} (x : BigInt m (F p)) :
    BigInt.value B x = ∑ k : Fin m, (x[k]).val * 2 ^ (B * k.val) := by
  rw [BigInt.value, fromLimbs_eq_sum]
  have hlen : (x.toList.map ZMod.val).length = m := by
    simp [List.length_map, Vector.length_toList]

  rw [← Fin.sum_congr' (fun k : Fin m => (x[k]).val * 2 ^ (B * k.val)) hlen]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Fin.val_cast]
  congr 1
  rw [Fin.getElem_fin, List.getElem_map]
  rfl

theorem sum_lt_pow {B n : ℕ} (f : Fin n → ℕ) (hf : ∀ i, f i < 2 ^ B) :
    ∑ i : Fin n, f i * 2 ^ (B * i.val) < 2 ^ (B * n) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Fin.sum_univ_castSucc]
    have ihk : ∑ i : Fin k, f (Fin.castSucc i) * 2 ^ (B * i.val) < 2 ^ (B * k) :=
      ih (fun i => f (Fin.castSucc i)) (fun i => hf _)
    have hlast : f (Fin.last k) < 2 ^ B := hf _
    have hterm : f (Fin.last k) * 2 ^ (B * k) ≤ (2 ^ B - 1) * 2 ^ (B * k) := by
      apply Nat.mul_le_mul_right
      omega
    have hpow : (2 ^ B - 1) * 2 ^ (B * k) + 2 ^ (B * k) = 2 ^ (B * (k + 1)) := by
      have h1 : 0 < 2 ^ B := Nat.two_pow_pos B
      rw [Nat.mul_add, Nat.mul_one, pow_add, Nat.sub_mul, Nat.one_mul,
        Nat.mul_comm (2 ^ B) (2 ^ (B * k))]
      have hle : 2 ^ (B * k) ≤ 2 ^ (B * k) * 2 ^ B := Nat.le_mul_of_pos_right _ h1
      omega
    have hcs : ∀ i : Fin k, ((Fin.castSucc i : Fin (k+1)) : ℕ) = (i : ℕ) := fun i => rfl
    simp only [Fin.val_last, hcs] at *
    omega

omit [Fact (Nat.Prime p)] in

theorem BigInt.value_lt {B : ℕ} {x : BigInt m (F p)} (h : x.Normalized B) :
    BigInt.value B x < 2 ^ (B * m) := by
  rw [BigInt.value_eq_sum]
  exact sum_lt_pow (fun k => (x[k]).val) h

theorem limb_decomp_mod (B : ℕ) : ∀ (m N : ℕ),
    (∑ i ∈ Finset.range m, (N / 2 ^ (B * i) % 2 ^ B) * 2 ^ (B * i)) = N % 2 ^ (B * m) := by
  intro m
  induction m with
  | zero => intro N; simp [Nat.mod_one]
  | succ n ih =>
    intro N
    rw [Finset.sum_range_succ']
    simp only [Nat.mul_zero, pow_zero, Nat.mul_one, Nat.div_one]
    have htail : (∑ i ∈ Finset.range n, (N / 2 ^ (B * (i + 1)) % 2 ^ B) * 2 ^ (B * (i + 1)))
        = 2 ^ B * ((N / 2 ^ B) % 2 ^ (B * n)) := by
      rw [← ih (N / 2 ^ B), Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      have h1 : N / 2 ^ (B * (i + 1)) = (N / 2 ^ B) / 2 ^ (B * i) := by
        rw [Nat.div_div_eq_div_mul, ← pow_add]; congr 1; ring
      have h2 : (2 : ℕ) ^ (B * (i + 1)) = 2 ^ B * 2 ^ (B * i) := by rw [← pow_add]; congr 1; ring
      rw [h1, h2]; ring
    rw [htail]
    have hsplit : N % 2 ^ (B * (n + 1)) = N % 2 ^ B + 2 ^ B * ((N / 2 ^ B) % 2 ^ (B * n)) := by
      conv_lhs => rw [show B * (n + 1) = B + B * n by ring, pow_add, Nat.mod_mul]
    rw [hsplit]; ring

theorem BigInt.value_mapRange {B : ℕ} (off N : ℕ) (env : Environment (F p))
    (hB : 2 ^ B < p) (hN : N < 2 ^ (B * m))
    (hwit : ∀ i : Fin m, env.get (off + i.val) = ((N / 2 ^ (B * i.val) % 2 ^ B : ℕ) : F p)) :
    BigInt.value B (Vector.map (Expression.eval env)
      (Vector.mapRange m fun i => var (F := F p) { index := off + i })) = N := by
  rw [BigInt.value_eq_sum]
  have hstep : (∑ k : Fin m, ((Vector.map (Expression.eval env)
        (Vector.mapRange m fun i => var (F := F p) { index := off + i }))[k]).val * 2 ^ (B * k.val))
      = ∑ k ∈ Finset.range m, (N / 2 ^ (B * k) % 2 ^ B) * 2 ^ (B * k) := by
    rw [← Fin.sum_univ_eq_sum_range (fun k => (N / 2 ^ (B * k) % 2 ^ B) * 2 ^ (B * k))]
    apply Finset.sum_congr rfl
    intro i _
    have hget : (Vector.map (Expression.eval env)
        (Vector.mapRange m fun j => var (F := F p) { index := off + j }))[i.val] = env.get (off + i.val) := by
      simp [circuit_norm]
    rw [Fin.getElem_fin, hget, hwit i]
    congr 1
    rw [ZMod.val_natCast_of_lt]
    exact lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos B)) (le_of_lt hB)
  rw [hstep, limb_decomp_mod, Nat.mod_eq_of_lt hN]

end

section
variable {p : ℕ} [Fact p.Prime]
variable {m : ℕ} [NeZero m]

def bigIntMulNoReduce (a b : Var (BigInt m) (F p)) :
    Vector (Expression (F p)) (2 * m - 1) :=
  Vector.mapFinRange (2 * m - 1) fun k =>

    (Vector.finRange m).foldl
      (fun acc i =>
        if h : i.val ≤ k.val ∧ k.val - i.val < m then
          acc + a[i.val] * b[k.val - i.val]'(h.2)
        else acc)
      (0 : Expression (F p))

def polyValue (B : ℕ) {k : ℕ} (coeffs : Vector (F p) k) : ℕ :=
  ∑ i : Fin k, (coeffs[i.val]).val * 2 ^ (B * i.val)

lemma vector_foldl_finRange {α : Type*} (n : ℕ) (f : α → Fin n → α) (init : α) :
    Vector.foldl f init (Vector.finRange n) = Fin.foldl n f init := by
  induction n generalizing init with
  | zero => simp [Fin.foldl_zero]
  | succ k ih =>
    rw [Fin.foldl_succ_last, Vector.finRange_succ_last, Vector.foldl_append]
    simp only [Vector.foldl_map]
    rw [ih]
    simp [Vector.foldl]

lemma foldl_dif_add_eq_sum {M : Type*} [AddCommMonoid M] (n : ℕ)
    (P : Fin n → Prop) [DecidablePred P] (g : (i : Fin n) → P i → M) :
    Fin.foldl n (fun acc i => if h : P i then acc + g i h else acc) 0
      = ∑ i : Fin n, if h : P i then g i h else 0 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Fin.foldl_succ_last, Fin.sum_univ_castSucc]
    rw [ih (fun i => P i.castSucc) (fun i h => g i.castSucc h)]
    split <;> simp

def bigIntMulVars (pp : Vector (Expression (F p)) (m * m)) :
    Vector (Expression (F p)) (2 * m - 1) :=
  Vector.mapFinRange (2 * m - 1) fun k =>
    (Vector.finRange m).foldl
      (fun acc i =>
        if h : i.val ≤ k.val ∧ k.val - i.val < m then
          acc + pp[i.val * m + (k.val - i.val)]'(by
            have : i.val * m + (k.val - i.val) < m * m := by
              have hi := i.isLt; have := h.2; calc
                i.val * m + (k.val - i.val) < i.val * m + m := by omega
                _ = (i.val + 1) * m := by ring
                _ ≤ m * m := by apply Nat.mul_le_mul_right; omega
            simpa [Nat.mul_comm] using this)
        else acc)
      (0 : Expression (F p))

omit [NeZero m] in

lemma eval_bigIntMulNoReduce_coeff (env : Environment (F p))
    (a b : Var (BigInt m) (F p)) (k : Fin (2 * m - 1)) :
    Expression.eval env ((bigIntMulNoReduce a b)[k.val])
      = ∑ i : Fin m, if h : i.val ≤ k.val ∧ k.val - i.val < m then
          (Expression.eval env a[i.val]) * (Expression.eval env (b[k.val - i.val]'h.2)) else 0 := by
  simp only [bigIntMulNoReduce, Vector.getElem_mapFinRange]
  rw [vector_foldl_finRange]
  rw [eval_foldl env m
    (fun acc i => if h : i.val ≤ k.val ∧ k.val - i.val < m then
        acc + a[i.val] * b[k.val - i.val]'h.2 else acc) 0
    (by intro e i; by_cases h : i.val ≤ k.val ∧ k.val - i.val < m <;> simp [h, circuit_norm])]
  simp only [apply_dite (Expression.eval env), Expression.eval]
  rw [foldl_dif_add_eq_sum m (fun i : Fin m => i.val ≤ k.val ∧ k.val - i.val < m)
    (fun i h => (Expression.eval env a[i.val]) * (Expression.eval env (b[k.val - i.val]'h.2)))]

omit [NeZero m] in

lemma eval_bigIntMulVars_coeff (env : Environment (F p))
    (pp : Vector (Expression (F p)) (m * m)) (k : Fin (2 * m - 1)) :
    Expression.eval env ((bigIntMulVars pp)[k.val])
      = ∑ i : Fin m, if h : i.val ≤ k.val ∧ k.val - i.val < m then
          (Expression.eval env (pp[i.val * m + (k.val - i.val)]'(by
            have := i.isLt; have := h.2; calc
              i.val * m + (k.val - i.val) < i.val * m + m := by omega
              _ = (i.val + 1) * m := by ring
              _ ≤ m * m := by apply Nat.mul_le_mul_right; omega))) else 0 := by
  simp only [bigIntMulVars, Vector.getElem_mapFinRange]
  rw [vector_foldl_finRange]
  rw [eval_foldl env m
    (fun acc i => if h : i.val ≤ k.val ∧ k.val - i.val < m then
        acc + pp[i.val * m + (k.val - i.val)]'(by
          have hi := i.isLt; have := h.2; calc
            i.val * m + (k.val - i.val) < i.val * m + m := by omega
            _ = (i.val + 1) * m := by ring
            _ ≤ m * m := by apply Nat.mul_le_mul_right; omega) else acc) 0
    (by intro e i; by_cases h : i.val ≤ k.val ∧ k.val - i.val < m <;> simp [h, circuit_norm])]
  simp only [apply_dite (Expression.eval env), Expression.eval]
  rw [foldl_dif_add_eq_sum m (fun i : Fin m => i.val ≤ k.val ∧ k.val - i.val < m)
    (fun i h => Expression.eval env (pp[i.val * m + (k.val - i.val)]'(by
      have hi := i.isLt; have := h.2; calc
        i.val * m + (k.val - i.val) < i.val * m + m := by omega
        _ = (i.val + 1) * m := by ring
        _ ≤ m * m := by apply Nat.mul_le_mul_right; omega)))]

omit [NeZero m] in

lemma map_eval_bigIntMulVars_eq (env : Environment (F p))
    (a b : Var (BigInt m) (F p)) (pp : Vector (Expression (F p)) (m * m))
    (hpp : ∀ (i j : Fin m),
      Expression.eval env (pp[i.val * m + j.val]'(by
        have := i.isLt; have := j.isLt
        calc i.val * m + j.val < i.val * m + m := by omega
          _ = (i.val + 1) * m := by ring
          _ ≤ m * m := by apply Nat.mul_le_mul_right; omega))
        = Expression.eval env a[i.val] * Expression.eval env b[j.val]) :
    Vector.map (Expression.eval env) (bigIntMulVars pp)
      = Vector.map (Expression.eval env) (bigIntMulNoReduce a b) := by
  apply Vector.ext
  intro k hk
  rw [Vector.getElem_map, Vector.getElem_map,
    eval_bigIntMulVars_coeff env pp ⟨k, hk⟩, eval_bigIntMulNoReduce_coeff env a b ⟨k, hk⟩]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : i.val ≤ k ∧ k - i.val < m
  · simp only [dif_pos h]
    have hj : k - i.val < m := h.2
    have := hpp i ⟨k - i.val, hj⟩
    simpa using this
  · simp only [dif_neg h]

lemma val_bigIntMulNoReduce_coeff {B : ℕ} (env : Environment (F p))
    (a b : Var (BigInt m) (F p)) (k : Fin (2 * m - 1))
    (ha : ∀ i : Fin m, (Expression.eval env a[i.val]).val < 2 ^ B)
    (hb : ∀ i : Fin m, (Expression.eval env b[i.val]).val < 2 ^ B)
    (hbound : m * (2 ^ B * 2 ^ B) < p) :
    (Expression.eval env ((bigIntMulNoReduce a b)[k.val])).val
      = ∑ i : Fin m, if h : i.val ≤ k.val ∧ k.val - i.val < m then
          (Expression.eval env a[i.val]).val
            * (Expression.eval env (b[k.val - i.val]'h.2)).val else 0 := by
  set natConv := ∑ i : Fin m, if h : i.val ≤ k.val ∧ k.val - i.val < m then
      (Expression.eval env a[i.val]).val
        * (Expression.eval env (b[k.val - i.val]'h.2)).val else 0 with hnat

  have hlt : natConv < p := by
    have hterm : ∀ i : Fin m, (if h : i.val ≤ k.val ∧ k.val - i.val < m then
        (Expression.eval env a[i.val]).val
          * (Expression.eval env (b[k.val - i.val]'h.2)).val else 0)
        ≤ 2 ^ B * 2 ^ B - 1 := by
      intro i
      by_cases h : i.val ≤ k.val ∧ k.val - i.val < m
      · rw [dif_pos h]
        have h1 := ha i
        have h2 := hb ⟨k.val - i.val, h.2⟩
        have : (Expression.eval env a[i.val]).val
            * (Expression.eval env (b[k.val - i.val]'h.2)).val < 2 ^ B * 2 ^ B :=
          Nat.mul_lt_mul'' h1 h2
        omega
      · rw [dif_neg h]; positivity
    have hcard : natConv ≤ m * (2 ^ B * 2 ^ B - 1) := by
      rw [hnat]
      calc ∑ i : Fin m, _ ≤ ∑ _i : Fin m, (2 ^ B * 2 ^ B - 1) :=
            Finset.sum_le_sum (fun i _ => hterm i)
        _ = m * (2 ^ B * 2 ^ B - 1) := by rw [Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, smul_eq_mul]
    have hpos : 0 < 2 ^ B * 2 ^ B := by positivity
    have hm : 0 < m := Nat.pos_of_neZero m
    have : m * (2 ^ B * 2 ^ B - 1) < m * (2 ^ B * 2 ^ B) :=
      (Nat.mul_lt_mul_left hm).mpr (by omega)
    omega

  have hcast : Expression.eval env ((bigIntMulNoReduce a b)[k.val]) = (natConv : F p) := by
    rw [eval_bigIntMulNoReduce_coeff, hnat, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : i.val ≤ k.val ∧ k.val - i.val < m
    · simp only [dif_pos h]
      rw [Nat.cast_mul, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    · simp only [dif_neg h, Nat.cast_zero]
  rw [hcast, ZMod.val_natCast_of_lt hlt]

lemma val_bigIntMulNoReduce_coeff_lt {B : ℕ} (env : Environment (F p))
    (a b : Var (BigInt m) (F p)) (k : Fin (2 * m - 1))
    (ha : ∀ i : Fin m, (Expression.eval env a[i.val]).val < 2 ^ B)
    (hb : ∀ i : Fin m, (Expression.eval env b[i.val]).val < 2 ^ B)
    (hbound : m * (2 ^ B * 2 ^ B) < p) :
    (Expression.eval env ((bigIntMulNoReduce a b)[k.val])).val < m * 2 ^ (2 * B) := by
  rw [val_bigIntMulNoReduce_coeff env a b k ha hb hbound]
  have hterm : ∀ i : Fin m, (if h : i.val ≤ k.val ∧ k.val - i.val < m then
      (Expression.eval env a[i.val]).val
        * (Expression.eval env (b[k.val - i.val]'h.2)).val else 0)
      ≤ 2 ^ B * 2 ^ B - 1 := by
    intro i
    by_cases h : i.val ≤ k.val ∧ k.val - i.val < m
    · rw [dif_pos h]
      have h1 := ha i
      have h2 := hb ⟨k.val - i.val, h.2⟩
      have : (Expression.eval env a[i.val]).val
          * (Expression.eval env (b[k.val - i.val]'h.2)).val < 2 ^ B * 2 ^ B :=
        Nat.mul_lt_mul'' h1 h2
      omega
    · rw [dif_neg h]; positivity
  have hcard : (∑ i : Fin m, if h : i.val ≤ k.val ∧ k.val - i.val < m then
      (Expression.eval env a[i.val]).val
        * (Expression.eval env (b[k.val - i.val]'h.2)).val else 0)
      ≤ m * (2 ^ B * 2 ^ B - 1) := by
    calc ∑ i : Fin m, _ ≤ ∑ _i : Fin m, (2 ^ B * 2 ^ B - 1) :=
          Finset.sum_le_sum (fun i _ => hterm i)
      _ = m * (2 ^ B * 2 ^ B - 1) := by rw [Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, smul_eq_mul]
  have hpos : 0 < 2 ^ B * 2 ^ B := by positivity
  have hm : 0 < m := Nat.pos_of_neZero m
  have h2B : (2 : ℕ) ^ B * 2 ^ B = 2 ^ (2 * B) := by rw [two_mul, pow_add]
  have hlt2 : m * (2 ^ B * 2 ^ B - 1) < m * (2 ^ B * 2 ^ B) :=
    (Nat.mul_lt_mul_left hm).mpr (by omega)
  rw [h2B] at hcard hlt2
  omega

lemma cauchy_inner_reindex (B m : ℕ) (f g : ℕ → ℕ) (i : ℕ) (hi : i < m) :
    (∑ k ∈ Finset.range (2 * m - 1),
        if i ≤ k ∧ k - i < m then f i * g (k - i) * 2 ^ (B * k) else 0)
      = ∑ j ∈ Finset.range m, f i * g j * 2 ^ (B * (i + j)) := by
  rw [← Finset.sum_filter]
  apply Finset.sum_nbij' (i := fun k => k - i) (j := fun j => i + j)
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
    omega
  · intro j hj
    simp only [Finset.mem_range, Finset.mem_filter] at hj ⊢
    omega
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    omega
  · intro j hj
    simp only [Finset.mem_range] at hj
    omega
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    rw [show i + (k - i) = k by omega]

lemma cauchy_base_pow (B m : ℕ) (f g : ℕ → ℕ) :
    (∑ i ∈ Finset.range m, f i * 2 ^ (B * i))
        * (∑ j ∈ Finset.range m, g j * 2 ^ (B * j))
      = ∑ k ∈ Finset.range (2 * m - 1),
          (∑ i ∈ Finset.range m, if i ≤ k ∧ k - i < m then f i * g (k - i) else 0)
            * 2 ^ (B * k) := by
  rw [Finset.sum_mul_sum]

  have hrhs : (∑ k ∈ Finset.range (2 * m - 1),
        (∑ i ∈ Finset.range m, if i ≤ k ∧ k - i < m then f i * g (k - i) else 0)
          * 2 ^ (B * k))
      = ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m, f i * g j * 2 ^ (B * (i + j)) := by
    have hstep : (∑ k ∈ Finset.range (2 * m - 1),
          (∑ i ∈ Finset.range m, if i ≤ k ∧ k - i < m then f i * g (k - i) else 0)
            * 2 ^ (B * k))
        = ∑ k ∈ Finset.range (2 * m - 1), ∑ i ∈ Finset.range m,
            if i ≤ k ∧ k - i < m then f i * g (k - i) * 2 ^ (B * k) else 0 := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [ite_mul, zero_mul]
    rw [hstep, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    rw [cauchy_inner_reindex B m f g i hi]
  rw [hrhs]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [show B * (i + j) = B * i + B * j by ring, pow_add]
  ring

lemma polyValue_bigIntMulNoReduce {B : ℕ} (env : Environment (F p))
    (a b : Var (BigInt m) (F p))
    (ha : ∀ i : Fin m, (Expression.eval env a[i.val]).val < 2 ^ B)
    (hb : ∀ i : Fin m, (Expression.eval env b[i.val]).val < 2 ^ B)
    (hbound : m * (2 ^ B * 2 ^ B) < p) :
    polyValue B (Vector.map (Expression.eval env) (bigIntMulNoReduce a b))
      = (∑ i : Fin m, (Expression.eval env a[i.val]).val * 2 ^ (B * i.val))
        * (∑ j : Fin m, (Expression.eval env b[j.val]).val * 2 ^ (B * j.val)) := by

  set av : ℕ → ℕ := fun i => if h : i < m then (Expression.eval env a[i]).val else 0 with hav
  set bv : ℕ → ℕ := fun j => if h : j < m then (Expression.eval env b[j]).val else 0 with hbv

  have hAsum : (∑ i : Fin m, (Expression.eval env a[i.val]).val * 2 ^ (B * i.val))
      = ∑ i ∈ Finset.range m, av i * 2 ^ (B * i) := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => av i * 2 ^ (B * i))]
    apply Finset.sum_congr rfl
    intro i _; simp only [hav, dif_pos i.isLt]
  have hBsum : (∑ j : Fin m, (Expression.eval env b[j.val]).val * 2 ^ (B * j.val))
      = ∑ j ∈ Finset.range m, bv j * 2 ^ (B * j) := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => bv j * 2 ^ (B * j))]
    apply Finset.sum_congr rfl
    intro j _; simp only [hbv, dif_pos j.isLt]
  rw [hAsum, hBsum, cauchy_base_pow B m av bv]

  rw [polyValue]
  rw [← Fin.sum_univ_eq_sum_range
    (fun k => (∑ i ∈ Finset.range m, if i ≤ k ∧ k - i < m then av i * bv (k - i) else 0)
      * 2 ^ (B * k))]
  apply Finset.sum_congr rfl
  intro k _
  rw [Vector.getElem_map, val_bigIntMulNoReduce_coeff env a b k ha hb hbound]
  congr 1

  rw [← Fin.sum_univ_eq_sum_range
    (fun i => if i ≤ k.val ∧ k.val - i < m then av i * bv (k.val - i) else 0)]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : i.val ≤ k.val ∧ k.val - i.val < m
  · rw [dif_pos h, if_pos h]
    simp only [hav, hbv, dif_pos i.isLt, dif_pos h.2]
  · rw [dif_neg h, if_neg h]

def evalPartial (B : ℕ) {n : ℕ} (env : ProverEnvironment (F p))
    (x : Var (fields n) (F p)) (k : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (k + 1),
    (if h : j < n then (Expression.eval env.toEnvironment x[j]).val else 0) * 2 ^ (B * j)

lemma partial_div_bound (B m : ℕ) (hB1 : 1 ≤ B) (f : ℕ → ℕ)
    (hf : ∀ j, f j < (m + 1) * 2 ^ (2 * B)) (k : ℕ) :
    (∑ j ∈ Finset.range (k + 1), f j * 2 ^ (B * j)) / 2 ^ (B * (k + 1))
      ≤ (m + 1) * 2 ^ (B + 1) := by

  have hgeo : (∑ j ∈ Finset.range (k + 1), 2 ^ (B * j)) ≤ 2 ^ (B * k + 1) := by
    induction k with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have h1 : (2 : ℕ) ^ (B * n + 1) + 2 ^ (B * (n + 1)) ≤ 2 ^ (B * (n + 1) + 1) := by
        have he : B * n + 1 ≤ B * (n + 1) := by nlinarith
        have h2 : (2 : ℕ) ^ (B * n + 1) ≤ 2 ^ (B * (n + 1)) := Nat.pow_le_pow_right (by norm_num) he
        have : (2 : ℕ) ^ (B * (n + 1)) + 2 ^ (B * (n + 1)) = 2 ^ (B * (n + 1) + 1) := by
          rw [pow_succ]; ring
        omega
      omega
  have hsum_lt : (∑ j ∈ Finset.range (k + 1), f j * 2 ^ (B * j))
      ≤ (m + 1) * 2 ^ (B + 1) * 2 ^ (B * (k + 1)) := by
    calc (∑ j ∈ Finset.range (k + 1), f j * 2 ^ (B * j))
        ≤ ∑ j ∈ Finset.range (k + 1), (m + 1) * 2 ^ (2 * B) * 2 ^ (B * j) := by
          apply Finset.sum_le_sum
          intro j _
          apply Nat.mul_le_mul_right
          have := hf j; omega
      _ = (m + 1) * 2 ^ (2 * B) * ∑ j ∈ Finset.range (k + 1), 2 ^ (B * j) := by
          rw [Finset.mul_sum]
      _ ≤ (m + 1) * 2 ^ (2 * B) * 2 ^ (B * k + 1) := Nat.mul_le_mul_left _ hgeo
      _ = (m + 1) * 2 ^ (B + 1) * 2 ^ (B * (k + 1)) := by
          rw [Nat.mul_assoc, Nat.mul_assoc, ← pow_add, ← pow_add]; congr 2; ring

  exact Nat.div_le_of_le_mul (by rw [Nat.mul_comm]; exact hsum_lt)

lemma partial_mod_stable (B : ℕ) (h : ℕ → ℕ) :
    ∀ N k, k < N →
      (∑ j ∈ Finset.range N, h j * 2 ^ (B * j)) % 2 ^ (B * (k + 1))
        = (∑ j ∈ Finset.range (k + 1), h j * 2 ^ (B * j)) % 2 ^ (B * (k + 1)) := by
  intro N
  induction N with
  | zero => intro k hk; omega
  | succ n ih =>
    intro k hk
    rw [Finset.sum_range_succ]
    rcases Nat.lt_or_ge k n with hlt | hge
    ·
      have hfac : (2 : ℕ) ^ (B * n) = 2 ^ (B * (k + 1)) * 2 ^ (B * (n - k - 1)) := by
        rw [← pow_add]; congr 1
        have : B * (k + 1) + B * (n - k - 1) = B * (k + 1 + (n - k - 1)) := by ring
        rw [this]; congr 1; omega
      rw [hfac, show h n * (2 ^ (B * (k + 1)) * 2 ^ (B * (n - k - 1)))
          = (h n * 2 ^ (B * (n - k - 1))) * 2 ^ (B * (k + 1)) by ring,
        Nat.add_mul_mod_self_right]
      exact ih k hlt
    ·
      have : k = n := by omega
      subst this; rw [Finset.sum_range_succ]

lemma quot_step (B : ℕ) (f : ℕ → ℕ) (k : ℕ) :
    (∑ j ∈ Finset.range (k + 1), f j * 2 ^ (B * j)) / 2 ^ (B * k)
      = f k + (if k = 0 then 0
          else (∑ j ∈ Finset.range k, f j * 2 ^ (B * j)) / 2 ^ (B * k)) := by
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · subst hk0; simp
  · rw [if_neg (by omega : ¬ k = 0)]
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    rw [Finset.sum_range_succ, show n.succ = n + 1 from rfl,
      Nat.add_mul_div_right _ _ (Nat.two_pow_pos (B * (n + 1)))]
    ring

lemma carry_telescope (B : ℕ) (C : ℕ → ℕ) :
    ∀ n : ℕ,
      (∑ k ∈ Finset.range n, (if k = 0 then 0 else C (k - 1)) * 2 ^ (B * k))
        + (if n = 0 then 0 else C (n - 1) * 2 ^ (B * n))
      = ∑ k ∈ Finset.range n, C k * 2 ^ (B * (k + 1)) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    · rw [if_neg (by omega : n + 1 ≠ 0)] at *
      rw [if_neg (by omega : n ≠ 0)] at ih ⊢
      simp only [Nat.add_sub_cancel] at *
      omega

lemma geom_shift (B : ℕ) :
    ∀ n : ℕ,
      2 ^ B * (∑ k ∈ Finset.range n, 2 ^ (B * k))
        = (∑ k ∈ Finset.range n, 2 ^ (B * k)) + 2 ^ (B * n) - 1 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Nat.mul_add, ih]
    have h1 : (2 : ℕ) ^ B * 2 ^ (B * n) = 2 ^ (B * (n + 1)) := by
      rw [← pow_add]; congr 1; ring
    have hge : 1 ≤ 2 ^ (B * n) := Nat.one_le_two_pow
    have hge2 : 1 ≤ ∑ k ∈ Finset.range n, 2 ^ (B * k) + 2 ^ (B * n) := by omega
    rw [h1]; omega

def carryOffset (B : ℕ) : ℕ := (m + 1) * 2 ^ (B + 1)

structure BigIntParams (p m : ℕ) where

  B : ℕ

  W : ℕ

  hB : 2 ^ B < p

  hW : 2 ^ W < p

  hB1 : 1 ≤ B

  hWB : carryOffset (m := m) B * 2 < 2 ^ W

  hWp : (m + 1) * 2 ^ (2 * B) * 3 + 2 ^ W * 2 ^ B + 2 ^ W < p

  hp : 2 ^ (2 * B) * (m + 1) * 4 < p

lemma per_index_lift {B : ℕ} (a cinF b c off : F p) (cinN offN : ℕ)
    (hpB : 2 ^ B < p) (hcin : cinF.val = cinN) (hoff : off.val = offN)
    (hlhs : a.val + cinN + offN * 2 ^ B < p)
    (hrhs : b.val + c.val * 2 ^ B + offN < p)
    (heq : a + cinF + off * (2 ^ B : F p) = b + c * (2 ^ B : F p) + off) :
    a.val + cinN + offN * 2 ^ B = b.val + c.val * 2 ^ B + offN := by
  have hpow_val_cast : ((2 ^ B : ℕ) : F p) = (2 ^ B : F p) := by push_cast; ring
  have hpow_val : (2 ^ B : F p).val = 2 ^ B := by
    rw [← hpow_val_cast, ZMod.val_natCast_of_lt hpB]
  have hoffcast : ((offN : ℕ) : F p) = off := by rw [← hoff, ZMod.natCast_zmod_val]
  have hcincast : ((cinN : ℕ) : F p) = cinF := by rw [← hcin, ZMod.natCast_zmod_val]
  have hacast : ((a.val : ℕ) : F p) = a := ZMod.natCast_zmod_val a
  have hbcast : ((b.val : ℕ) : F p) = b := ZMod.natCast_zmod_val b
  have hccast : ((c.val : ℕ) : F p) = c := ZMod.natCast_zmod_val c

  have hlhs_cast : a + cinF + off * (2 ^ B : F p)
      = ((a.val + cinN + offN * 2 ^ B : ℕ) : F p) := by
    push_cast [hacast, hcincast, hoffcast, hpow_val_cast]; ring
  have hlhs_val : (a + cinF + off * (2 ^ B : F p)).val = a.val + cinN + offN * 2 ^ B := by
    rw [hlhs_cast, ZMod.val_natCast_of_lt hlhs]

  have hrhs_cast : b + c * (2 ^ B : F p) + off
      = ((b.val + c.val * 2 ^ B + offN : ℕ) : F p) := by
    push_cast [hbcast, hccast, hoffcast, hpow_val_cast]; ring
  have hrhs_val : (b + c * (2 ^ B : F p) + off).val = b.val + c.val * 2 ^ B + offN := by
    rw [hrhs_cast, ZMod.val_natCast_of_lt hrhs]
  have := congrArg ZMod.val heq
  rw [hlhs_val, hrhs_val] at this
  exact this

end

section
variable {p : ℕ} [Fact p.Prime]
variable {m : ℕ} [NeZero m]

lemma ripple_carry (B : ℕ) (g : ℕ → ℕ) (hg : ∀ j, g j ≤ 2 * (2 ^ B - 1)) :
    ∀ k : ℕ,
      let P : ℕ → ℕ := fun k => 1 + ∑ j ∈ Finset.range (k + 1), g j * 2 ^ (B * j)
      (P k / 2 ^ (B * k)) ≤ 2 ^ (B + 1) - 1 ∧
      P k / 2 ^ (B * (k + 1)) ≤ 1 := by
  have hBpos : 0 < 2 ^ B := Nat.two_pow_pos B
  have hcarry_bit : (2 ^ (B + 1) - 1) / 2 ^ B ≤ 1 := by
    rw [Nat.div_le_iff_le_mul_add_pred hBpos]
    rw [pow_succ]; omega
  intro k P
  induction k with
  | zero =>
    refine ⟨?_, ?_⟩
    · show P 0 / 2 ^ (B * 0) ≤ _
      have hP0 : P 0 = 1 + g 0 := by
        simp only [P, Finset.sum_range_succ, Finset.sum_range_zero, Nat.mul_zero, pow_zero]; ring
      rw [hP0, Nat.mul_zero, pow_zero, Nat.div_one]
      have := hg 0
      have : 2 * (2 ^ B - 1) + 1 ≤ 2 ^ (B + 1) - 1 := by rw [pow_succ]; omega
      omega
    · show P 0 / 2 ^ (B * (0 + 1)) ≤ 1
      have hP0 : P 0 = 1 + g 0 := by
        simp only [P, Finset.sum_range_succ, Finset.sum_range_zero, Nat.mul_zero, pow_zero]; ring
      rw [hP0, Nat.zero_add, Nat.mul_one]
      have hg0 := hg 0
      have hub : 1 + g 0 ≤ 2 ^ (B + 1) - 1 := by rw [pow_succ]; omega
      calc (1 + g 0) / 2 ^ B ≤ (2 ^ (B + 1) - 1) / 2 ^ B := Nat.div_le_div_right hub
        _ ≤ 1 := hcarry_bit
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih

    have hPsucc : P (n + 1) = P n + g (n + 1) * 2 ^ (B * (n + 1)) := by
      simp only [P, Finset.sum_range_succ]; ring

    have hdiv1 : P (n + 1) / 2 ^ (B * (n + 1)) = P n / 2 ^ (B * (n + 1)) + g (n + 1) := by
      rw [hPsucc, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _)]
    refine ⟨?_, ?_⟩
    ·
      rw [hdiv1]
      have := hg (n + 1)
      have hub : 2 * (2 ^ B - 1) + 1 ≤ 2 ^ (B + 1) - 1 := by rw [pow_succ]; omega
      omega
    ·
      have hdiv2 : P (n + 1) / 2 ^ (B * (n + 1 + 1))
          = (P n / 2 ^ (B * (n + 1)) + g (n + 1)) / 2 ^ B := by
        rw [show B * (n + 1 + 1) = B * (n + 1) + B by ring, pow_add,
          ← Nat.div_div_eq_div_mul, hdiv1]
      rw [hdiv2]
      have := hg (n + 1)
      have hsum : P n / 2 ^ (B * (n + 1)) + g (n + 1) ≤ 2 ^ (B + 1) - 1 := by
        rw [pow_succ]; omega
      calc (P n / 2 ^ (B * (n + 1)) + g (n + 1)) / 2 ^ B
          ≤ (2 ^ (B + 1) - 1) / 2 ^ B := Nat.div_le_div_right hsum
        _ ≤ 1 := hcarry_bit

lemma digit_extract (B : ℕ) (f : ℕ → ℕ) (hf : ∀ j, f j < 2 ^ B) :
    ∀ (m k : ℕ), k < m →
      (∑ j ∈ Finset.range m, f j * 2 ^ (B * j)) / 2 ^ (B * k) % 2 ^ B = f k := by
  intro m
  induction m with
  | zero => intro k hk; omega
  | succ n ih =>
    intro k hk
    rw [Finset.sum_range_succ]
    rcases Nat.lt_or_ge k n with hlt | hge
    ·
      have hfac : (2 : ℕ) ^ (B * n) = 2 ^ (B * k) * 2 ^ B * 2 ^ (B * (n - k - 1)) := by
        rw [← pow_add, ← pow_add]; congr 1
        have hn : B * k + B + B * (n - k - 1) = B * (k + 1 + (n - k - 1)) := by ring
        rw [hn]; congr 1; omega
      rw [hfac, show f n * (2 ^ (B * k) * 2 ^ B * 2 ^ (B * (n - k - 1)))
          = (f n * 2 ^ (B * (n - k - 1)) * 2 ^ B) * 2 ^ (B * k) by ring,
        Nat.add_mul_div_right _ _ (Nat.two_pow_pos (B * k)), Nat.add_mul_mod_self_right]
      exact ih k hlt
    ·
      have hkn : k = n := by omega
      subst hkn
      have hlow : (∑ j ∈ Finset.range k, f j * 2 ^ (B * j)) < 2 ^ (B * k) := by
        rw [← Fin.sum_univ_eq_sum_range (fun j => f j * 2 ^ (B * j)) k]
        exact sum_lt_pow (fun j : Fin k => f j) (fun j => hf _)
      rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos (B * k)),
        Nat.div_eq_of_lt hlow, Nat.zero_add, Nat.mod_eq_of_lt (hf k)]

lemma limb_stable (B : ℕ) (g : ℕ → ℕ) :
    let P : ℕ → ℕ := fun k => 1 + ∑ j ∈ Finset.range (k + 1), g j * 2 ^ (B * j)
    ∀ k k', k ≤ k' → P k' / 2 ^ (B * k) % 2 ^ B = P k / 2 ^ (B * k) % 2 ^ B := by
  intro P k k' hk
  induction k' with
  | zero => simp only [Nat.le_zero] at hk; subst hk; rfl
  | succ n ih =>
    rcases Nat.lt_or_ge k (n + 1) with hlt | hge
    ·
      have hkn : k ≤ n := by omega
      rw [← ih hkn]

      have hPsucc : P (n + 1) = P n + g (n + 1) * 2 ^ (B * (n + 1)) := by
        simp only [P, Finset.sum_range_succ]; ring
      rw [hPsucc]
      have hfac : (2 : ℕ) ^ (B * (n + 1)) = 2 ^ (B * k) * 2 ^ B * 2 ^ (B * (n - k)) := by
        rw [← pow_add, ← pow_add]; congr 1
        have hn : B * k + B + B * (n - k) = B * (k + 1 + (n - k)) := by ring
        rw [hn]; congr 1; omega
      rw [hfac]
      rw [show g (n + 1) * (2 ^ (B * k) * 2 ^ B * 2 ^ (B * (n - k)))
          = (g (n + 1) * 2 ^ (B * (n - k)) * 2 ^ B) * 2 ^ (B * k) by ring]
      rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos (B * k))]
      rw [Nat.add_mul_mod_self_right]
    ·
      have : k = n + 1 := by omega
      subst this; rfl

lemma ripple_eq (B : ℕ) (g : ℕ → ℕ) (k : ℕ) :
    let P : ℕ → ℕ := fun k => 1 + ∑ j ∈ Finset.range (k + 1), g j * 2 ^ (B * j)
    g k + (if k = 0 then 1 else P (k - 1) / 2 ^ (B * k))
      = (P k / 2 ^ (B * k)) % 2 ^ B + (P k / 2 ^ (B * (k + 1))) * 2 ^ B := by
  intro P
  have hkey : P k / 2 ^ (B * k) = g k + (if k = 0 then 1 else P (k - 1) / 2 ^ (B * k)) := by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      simp only [Nat.mul_zero, pow_zero, Nat.div_one, if_pos]
      show P 0 = g 0 + 1
      simp only [P, Finset.sum_range_succ, Finset.sum_range_zero, Nat.mul_zero, pow_zero]; ring
    · rw [if_neg (by omega : ¬ k = 0)]
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      have hPsucc : P (n + 1) = P n + g (n + 1) * 2 ^ (B * (n + 1)) := by
        simp only [P, Finset.sum_range_succ]; ring
      rw [hPsucc, Nat.succ_sub_one,
        Nat.add_mul_div_right _ _ (Nat.two_pow_pos (B * (n + 1)))]
      ring

  have hdiv : P k / 2 ^ (B * (k + 1)) = (P k / 2 ^ (B * k)) / 2 ^ B := by
    rw [show B * (k + 1) = B * k + B by ring, pow_add, Nat.div_div_eq_div_mul]
  rw [hdiv, hkey]
  exact (Nat.mod_add_div' _ _).symm

lemma per_limb_lift {B : ℕ} (a d cin one b c : F p)
    (hpB : 2 ^ B < p)
    (hsum_lt : a.val + d.val + cin.val + one.val < p)
    (hrhs_lt : b.val + c.val * 2 ^ B < p)
    (heq : a + d + cin + one - b - c * (2 ^ B : F p) = 0) :
    a.val + d.val + cin.val + one.val = b.val + c.val * 2 ^ B := by
  have hpow_val_cast : ((2 ^ B : ℕ) : F p) = (2 ^ B : F p) := by push_cast; ring
  have hpow_val : (2 ^ B : F p).val = 2 ^ B := by
    rw [← hpow_val_cast, ZMod.val_natCast_of_lt hpB]
  have heq' : a + d + cin + one = b + c * (2 ^ B : F p) := by
    rw [← sub_eq_zero]; rw [← heq]; ring
  have hlhs : (a + d + cin + one).val = a.val + d.val + cin.val + one.val := by
    have hcast : a + d + cin + one
        = ((a.val + d.val + cin.val + one.val : ℕ) : F p) := by
      push_cast
      rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val,
        ZMod.natCast_zmod_val]
    rw [hcast, ZMod.val_natCast_of_lt hsum_lt]
  have hmul : (c * (2 ^ B : F p)).val = c.val * 2 ^ B := by
    rw [ZMod.val_mul, hpow_val, Nat.mod_eq_of_lt]
    omega
  have hrhs : (b + c * (2 ^ B : F p)).val = b.val + c.val * 2 ^ B := by
    have hcast : b + c * (2 ^ B : F p) = ((b.val + c.val * 2 ^ B : ℕ) : F p) := by
      push_cast
      rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    rw [hcast, ZMod.val_natCast_of_lt hrhs_lt]
  have := congrArg ZMod.val heq'
  rw [hlhs, hrhs] at this
  exact this

end

end Solution.Secp256k1ScalarMulFixedBase

end DonorFile0_0

-- Adapted donor module: MulModTheorems
section DonorFile0_1

namespace Solution.Secp256k1ScalarMulFixedBase
open Solution.Secp256k1ScalarMulFixedBase.Limbs

namespace MulMod

section
variable {p : ℕ} [Fact p.Prime]
variable {m : ℕ} [NeZero m]

omit [NeZero m] in

lemma value_map_eval {B : ℕ} (env : Environment (F p)) (x : Var (BigInt m) (F p)) :
    BigInt.value B (Vector.map (Expression.eval env) x)
      = ∑ k : Fin m, (Expression.eval env x[k.val]).val * 2 ^ (B * k.val) := by
  rw [BigInt.value_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fin.getElem_fin, Vector.getElem_map]

lemma polyValue_mul_eq {B : ℕ} (env : Environment (F p))
    (a b : Var (BigInt m) (F p))
    (ha : ∀ i : Fin m, (Expression.eval env a[i.val]).val < 2 ^ B)
    (hb : ∀ i : Fin m, (Expression.eval env b[i.val]).val < 2 ^ B)
    (hfield : m * (2 ^ B * 2 ^ B) < p) :
    polyValue B (Vector.map (Expression.eval env) (bigIntMulNoReduce a b))
      = BigInt.value B (Vector.map (Expression.eval env) a)
        * BigInt.value B (Vector.map (Expression.eval env) b) := by
  rw [polyValue_bigIntMulNoReduce env a b ha hb hfield, value_map_eval, value_map_eval]

lemma polyValue_Sqn_eq {B : ℕ} (env : Environment (F p))
    (q n : Var (BigInt m) (F p))
    (hq : ∀ i : Fin m, (Expression.eval env q[i.val]).val < 2 ^ B)
    (hn : ∀ i : Fin m, (Expression.eval env n[i.val]).val < 2 ^ B)
    (hfield : m * (2 ^ B * 2 ^ B) < p) :
    polyValue B (Vector.map (Expression.eval env) (bigIntMulNoReduce q n))
      = BigInt.value B (Vector.map (Expression.eval env) q)
        * BigInt.value B (Vector.map (Expression.eval env) n) :=
  polyValue_mul_eq env q n hq hn hfield

lemma remainder_eq {a b q n r : ℕ} (heq : a * b = q * n + r) (hr : r < n) :
    r = a * b % n := by
  rw [heq, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]

def sVec (q n : Var (BigInt m) (F p)) (off : ℕ) :
    Vector (Expression (F p)) (2 * m - 1) :=
  Vector.mapFinRange (2 * m - 1) fun k =>
    if h : k.val < m then (bigIntMulNoReduce q n)[k.val] + var { index := off + k.val }
    else (bigIntMulNoReduce q n)[k.val]

lemma polyValue_sVec_split {B : ℕ} (env : Environment (F p))
    (q n : Var (BigInt m) (F p)) (off : ℕ)
    (hnowrap : ∀ k : Fin (2 * m - 1), k.val < m →
      (Expression.eval env ((bigIntMulNoReduce q n)[k.val])).val
        + (Expression.eval env (var (F := F p) { index := off + k.val })).val < p) :
    polyValue B (Vector.map (Expression.eval env) (sVec q n off))
      = polyValue B (Vector.map (Expression.eval env) (bigIntMulNoReduce q n))
        + BigInt.value B (Vector.map (Expression.eval env)
            (Vector.mapRange m fun i => var (F := F p) { index := off + i })) := by
  rw [polyValue, polyValue, value_map_eval]

  have hS : ∀ k : Fin (2 * m - 1),
      (Vector.map (Expression.eval env) (sVec q n off))[k.val].val
        = (Expression.eval env ((bigIntMulNoReduce q n)[k.val])).val
          + (if h : k.val < m then (Expression.eval env (var (F := F p) { index := off + k.val })).val else 0) := by
    intro k
    rw [Vector.getElem_map]
    simp only [sVec, Vector.getElem_mapFinRange]
    by_cases hk : k.val < m
    · simp only [dif_pos hk]
      rw [show Expression.eval env ((bigIntMulNoReduce q n)[k.val] + var { index := off + k.val })
            = Expression.eval env ((bigIntMulNoReduce q n)[k.val])
              + Expression.eval env (var (F := F p) { index := off + k.val }) from rfl,
        ZMod.val_add_of_lt (hnowrap k hk)]
    · simp only [dif_neg hk, Nat.add_zero]

  simp only [hS]

  rw [show (∑ k : Fin (2 * m - 1),
        ((Expression.eval env ((bigIntMulNoReduce q n)[k.val])).val
          + (if h : k.val < m then (Expression.eval env (var (F := F p) { index := off + k.val })).val else 0))
          * 2 ^ (B * k.val))
      = (∑ k : Fin (2 * m - 1),
          (Expression.eval env ((bigIntMulNoReduce q n)[k.val])).val * 2 ^ (B * k.val))
        + (∑ k : Fin (2 * m - 1),
          (if h : k.val < m then (Expression.eval env (var (F := F p) { index := off + k.val })).val else 0)
            * 2 ^ (B * k.val)) from by
    rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro k _; ring]
  congr 1
  ·
    apply Finset.sum_congr rfl; intro k _; rw [Vector.getElem_map]
  ·

    have hRHS : (∑ k : Fin m, (Expression.eval env (Vector.mapRange m
          fun i => var (F := F p) { index := off + i })[k.val]).val * 2 ^ (B * k.val))
        = ∑ k ∈ Finset.range m,
            (Expression.eval env (var (F := F p) { index := off + k })).val * 2 ^ (B * k) := by
      rw [← Fin.sum_univ_eq_sum_range (fun k => (Expression.eval env (var (F := F p) { index := off + k })).val * 2 ^ (B * k))]
      apply Finset.sum_congr rfl
      intro k _
      congr 2
      simp [circuit_norm]
    rw [hRHS]

    simp only [dite_eq_ite]
    rw [Fin.sum_univ_eq_sum_range (fun k =>
      (if k < m then (Expression.eval env (var (F := F p) { index := off + k })).val else 0) * 2 ^ (B * k))]
    have hext : (∑ k ∈ Finset.range (2 * m - 1),
          (if k < m then (Expression.eval env (var (F := F p) { index := off + k })).val else 0)
            * 2 ^ (B * k))
        = ∑ k ∈ Finset.range m,
          (Expression.eval env (var (F := F p) { index := off + k })).val * 2 ^ (B * k) := by
      rw [← Finset.sum_subset (Finset.range_subset_range.mpr (by have := Nat.pos_of_neZero m; omega : m ≤ 2 * m - 1))
        (f := fun k => (if k < m then (Expression.eval env (var (F := F p) { index := off + k })).val else 0) * 2 ^ (B * k))]
      · apply Finset.sum_congr rfl; intro k hk
        rw [Finset.mem_range] at hk; rw [if_pos hk]
      · intro k _ hk
        rw [Finset.mem_range] at hk; rw [if_neg hk, Nat.zero_mul]
    rw [hext]

lemma coeff_P_bound {B : ℕ} (env : Environment (F p))
    (a b : Var (BigInt m) (F p)) (k : Fin (2 * m - 1))
    (ha : ∀ i : Fin m, (Expression.eval env a[i.val]).val < 2 ^ B)
    (hb : ∀ i : Fin m, (Expression.eval env b[i.val]).val < 2 ^ B)
    (hfield : m * (2 ^ B * 2 ^ B) < p) :
    (Expression.eval env ((bigIntMulNoReduce a b)[k.val])).val < (m + 1) * 2 ^ (2 * B) := by
  have h := val_bigIntMulNoReduce_coeff_lt env a b k ha hb hfield
  have : m * 2 ^ (2 * B) ≤ (m + 1) * 2 ^ (2 * B) := by
    apply Nat.mul_le_mul_right; omega
  omega

lemma coeff_S_bound {B : ℕ} (env : Environment (F p))
    (q n : Var (BigInt m) (F p)) (off : ℕ) (k : Fin (2 * m - 1))
    (hq : ∀ i : Fin m, (Expression.eval env q[i.val]).val < 2 ^ B)
    (hn : ∀ i : Fin m, (Expression.eval env n[i.val]).val < 2 ^ B)
    (hr : ∀ j : ℕ, j < m → (Expression.eval env (var (F := F p) { index := off + j })).val < 2 ^ B)
    (hfield : m * (2 ^ B * 2 ^ B) < p) :
    (Expression.eval env ((sVec q n off)[k.val])).val < (m + 1) * 2 ^ (2 * B) := by
  have hSqn := val_bigIntMulNoReduce_coeff_lt env q n k hq hn hfield
  have hpow : (2 : ℕ) ^ B ≤ 2 ^ (2 * B) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hmm : (m + 1) * 2 ^ (2 * B) = m * 2 ^ (2 * B) + 2 ^ (2 * B) := by ring
  rw [hmm]
  generalize hX : 2 ^ (2 * B) = X at *
  generalize hY : m * X = Y at *
  simp only [sVec, Vector.getElem_mapFinRange]
  by_cases hk : k.val < m
  · rw [dif_pos hk]
    have hr' := hr k.val hk
    have hadd : (Expression.eval env ((bigIntMulNoReduce q n)[k.val])
        + Expression.eval env (var (F := F p) { index := off + k.val })).val
        ≤ (Expression.eval env ((bigIntMulNoReduce q n)[k.val])).val
          + (Expression.eval env (var (F := F p) { index := off + k.val })).val := ZMod.val_add_le _ _
    rw [show Expression.eval env ((bigIntMulNoReduce q n)[k.val] + var { index := off + k.val })
          = Expression.eval env ((bigIntMulNoReduce q n)[k.val])
            + Expression.eval env (var (F := F p) { index := off + k.val }) from rfl]
    omega
  · rw [dif_neg hk]
    omega

lemma witnessedMul_map_eval (env : Environment (F p)) (off : ℕ)
    (a b : Var (BigInt m) (F p))
    (hprod : ∀ t : Fin (m * m),
      Expression.eval env (a[t.val / m]'(Nat.div_lt_of_lt_mul t.isLt))
          * Expression.eval env (b[t.val % m]'(Nat.mod_lt _ (Nat.pos_of_neZero m)))
        = env.get (off + t.val)) :
    Vector.map (Expression.eval env)
        (bigIntMulVars (Vector.mapRange (m * m) fun i => var (F := F p) { index := off + i }))
      = Vector.map (Expression.eval env) (bigIntMulNoReduce a b) := by
  apply map_eval_bigIntMulVars_eq env a b
  intro i j

  have hidx : (Vector.mapRange (m * m) fun i => var (F := F p) { index := off + i })[i.val * m + j.val]'(by
        have := i.isLt; have := j.isLt
        calc i.val * m + j.val < i.val * m + m := by omega
          _ = (i.val + 1) * m := by ring
          _ ≤ m * m := by apply Nat.mul_le_mul_right; omega)
      = var (F := F p) { index := off + (i.val * m + j.val) } := by
    simp [circuit_norm]
  rw [hidx]

  have ht : (i.val * m + j.val) < m * m := by
    have := i.isLt; have := j.isLt
    calc i.val * m + j.val < i.val * m + m := by omega
      _ = (i.val + 1) * m := by ring
      _ ≤ m * m := by apply Nat.mul_le_mul_right; omega
  have hd : (i.val * m + j.val) / m = i.val := by
    rw [Nat.mul_comm, Nat.mul_add_div (Nat.pos_of_neZero m), Nat.div_eq_of_lt j.isLt, Nat.add_zero]
  have hr : (i.val * m + j.val) % m = j.val := by
    rw [Nat.mul_comm, Nat.mul_add_mod]; exact Nat.mod_eq_of_lt j.isLt
  have := hprod ⟨i.val * m + j.val, ht⟩
  simp only [hd, hr] at this
  rw [show Expression.eval env (var (F := F p) { index := off + (i.val * m + j.val) })
        = env.get (off + (i.val * m + j.val)) from rfl, ← this]

omit [NeZero m] in

lemma eqImpl_bridge {B rOff : ℕ} (env : Environment (F p))
    (Pv Pn Qv Qn : Vector (Expression (F p)) (2 * m - 1))
    (hP_get : ∀ k : Fin (2 * m - 1), Expression.eval env Pv[k.val] = Expression.eval env Pn[k.val])
    (hQ_get : ∀ k : Fin (2 * m - 1), Expression.eval env Qv[k.val] = Expression.eval env Qn[k.val])
    (himpl :
      ((∀ k : Fin (2 * m - 1), (Expression.eval env Pv[k.val]).val < (m + 1) * 2 ^ (2 * B)) ∧
        ∀ k : Fin (2 * m - 1),
          (Expression.eval env (if h : k.val < m then Qv[k.val] + var { index := rOff + k.val }
            else Qv[k.val])).val < (m + 1) * 2 ^ (2 * B)) →
        polyValue B (Vector.map (Expression.eval env) Pv) =
          polyValue B (Vector.map (Expression.eval env)
            (Vector.mapFinRange (2 * m - 1) fun k =>
              if h : k.val < m then Qv[k.val] + var { index := rOff + k.val } else Qv[k.val]))) :
    ((∀ k : Fin (2 * m - 1), (Expression.eval env Pn[k.val]).val < (m + 1) * 2 ^ (2 * B)) ∧
      ∀ k : Fin (2 * m - 1),
        (Expression.eval env (if h : k.val < m then Qn[k.val] + var { index := rOff + k.val }
          else Qn[k.val])).val < (m + 1) * 2 ^ (2 * B)) →
      polyValue B (Vector.map (Expression.eval env) Pn) =
        polyValue B (Vector.map (Expression.eval env)
          (Vector.mapFinRange (2 * m - 1) fun k =>
            if h : k.val < m then Qn[k.val] + var { index := rOff + k.val } else Qn[k.val])) := by

  have hS_get : ∀ k : Fin (2 * m - 1),
      Expression.eval env (if h : k.val < m then Qv[k.val] + var (F := F p) { index := rOff + k.val } else Qv[k.val])
        = Expression.eval env (if h : k.val < m then Qn[k.val] + var (F := F p) { index := rOff + k.val } else Qn[k.val]) := by
    intro k
    by_cases hk : k.val < m
    · simp only [dif_pos hk]
      show Expression.eval env Qv[k.val] + Expression.eval env (var (F := F p) { index := rOff + k.val })
        = Expression.eval env Qn[k.val] + Expression.eval env (var (F := F p) { index := rOff + k.val })
      rw [hQ_get k]
    · simp only [dif_neg hk]; exact hQ_get k

  have hSvec : Vector.map (Expression.eval env)
        (Vector.mapFinRange (2 * m - 1) fun k =>
          if h : k.val < m then Qv[k.val] + var (F := F p) { index := rOff + k.val } else Qv[k.val])
      = Vector.map (Expression.eval env)
        (Vector.mapFinRange (2 * m - 1) fun k =>
          if h : k.val < m then Qn[k.val] + var (F := F p) { index := rOff + k.val } else Qn[k.val]) := by
    apply Vector.ext; intro k hk
    rw [Vector.getElem_map, Vector.getElem_map, Vector.getElem_mapFinRange, Vector.getElem_mapFinRange]
    exact hS_get ⟨k, hk⟩
  have hPvec : Vector.map (Expression.eval env) Pv = Vector.map (Expression.eval env) Pn := by
    apply Vector.ext; intro k hk; rw [Vector.getElem_map, Vector.getElem_map]; exact hP_get ⟨k, hk⟩
  intro hbounds
  rw [← hPvec, ← hSvec]
  apply himpl
  refine ⟨fun k => ?_, fun k => ?_⟩
  · rw [hP_get k]; exact hbounds.1 k
  · rw [hS_get k]; exact hbounds.2 k

omit [NeZero m] in

lemma eqConj_bridge {B rOff : ℕ} (env : Environment (F p))
    (Pv Pn Qv Qn : Vector (Expression (F p)) (2 * m - 1))
    (hP_get : ∀ k : Fin (2 * m - 1), Expression.eval env Pv[k.val] = Expression.eval env Pn[k.val])
    (hQ_get : ∀ k : Fin (2 * m - 1), Expression.eval env Qv[k.val] = Expression.eval env Qn[k.val])
    (hconj :
      ((∀ k : Fin (2 * m - 1), (Expression.eval env Pn[k.val]).val < (m + 1) * 2 ^ (2 * B)) ∧
        (∀ k : Fin (2 * m - 1),
          (Expression.eval env (if h : k.val < m then Qn[k.val] + var { index := rOff + k.val }
            else Qn[k.val])).val < (m + 1) * 2 ^ (2 * B))) ∧
        polyValue B (Vector.map (Expression.eval env) Pn) =
          polyValue B (Vector.map (Expression.eval env)
            (Vector.mapFinRange (2 * m - 1) fun k =>
              if h : k.val < m then Qn[k.val] + var { index := rOff + k.val } else Qn[k.val]))) :
    ((∀ k : Fin (2 * m - 1), (Expression.eval env Pv[k.val]).val < (m + 1) * 2 ^ (2 * B)) ∧
      (∀ k : Fin (2 * m - 1),
        (Expression.eval env (if h : k.val < m then Qv[k.val] + var { index := rOff + k.val }
          else Qv[k.val])).val < (m + 1) * 2 ^ (2 * B))) ∧
        polyValue B (Vector.map (Expression.eval env) Pv) =
          polyValue B (Vector.map (Expression.eval env)
            (Vector.mapFinRange (2 * m - 1) fun k =>
              if h : k.val < m then Qv[k.val] + var { index := rOff + k.val } else Qv[k.val])) := by
  have hS_get : ∀ k : Fin (2 * m - 1),
      Expression.eval env (if h : k.val < m then Qv[k.val] + var (F := F p) { index := rOff + k.val } else Qv[k.val])
        = Expression.eval env (if h : k.val < m then Qn[k.val] + var (F := F p) { index := rOff + k.val } else Qn[k.val]) := by
    intro k
    by_cases hk : k.val < m
    · simp only [dif_pos hk]
      show Expression.eval env Qv[k.val] + Expression.eval env (var (F := F p) { index := rOff + k.val })
        = Expression.eval env Qn[k.val] + Expression.eval env (var (F := F p) { index := rOff + k.val })
      rw [hQ_get k]
    · simp only [dif_neg hk]; exact hQ_get k
  have hPvec : Vector.map (Expression.eval env) Pv = Vector.map (Expression.eval env) Pn := by
    apply Vector.ext; intro k hk; rw [Vector.getElem_map, Vector.getElem_map]; exact hP_get ⟨k, hk⟩
  have hSvec : Vector.map (Expression.eval env)
        (Vector.mapFinRange (2 * m - 1) fun k =>
          if h : k.val < m then Qv[k.val] + var (F := F p) { index := rOff + k.val } else Qv[k.val])
      = Vector.map (Expression.eval env)
        (Vector.mapFinRange (2 * m - 1) fun k =>
          if h : k.val < m then Qn[k.val] + var (F := F p) { index := rOff + k.val } else Qn[k.val]) := by
    apply Vector.ext; intro k hk
    rw [Vector.getElem_map, Vector.getElem_map, Vector.getElem_mapFinRange, Vector.getElem_mapFinRange]
    exact hS_get ⟨k, hk⟩
  refine ⟨⟨fun k => ?_, fun k => ?_⟩, ?_⟩
  · rw [hP_get k]; exact hconj.1.1 k
  · rw [hS_get k]; exact hconj.1.2 k
  · rw [hPvec, hSvec]; exact hconj.2

lemma mulMod_soundness_core {B : ℕ} (hp : 2 ^ (2 * B) * (m + 1) * 4 < p)
    (i₀ : ℕ) (env : Environment (F p))
    (input_var : ProvablePair (BigInt m) (ProvablePair (BigInt m) (BigInt m)) (Expression (F p)))
    (input : ProvablePair (BigInt m) (ProvablePair (BigInt m) (BigInt m)) (F p))
    (h_input : (Vector.map (Expression.eval env) input_var.1,
        Vector.map (Expression.eval env) input_var.2.1,
        Vector.map (Expression.eval env) input_var.2.2) = input)
    (ha_norm : BigInt.Normalized B input.1) (hb_norm : BigInt.Normalized B input.2.1)
    (hn_norm : BigInt.Normalized B input.2.2)
    (hq_norm : BigInt.Normalized B (Vector.map (Expression.eval env)
        (Vector.mapRange m fun i ↦ var { index := i₀ + i })))
    (hr_norm : BigInt.Normalized B (Vector.map (Expression.eval env)
        (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })))
    (h_eq_impl :
      ((∀ k : Fin (2 * m - 1),
          (Expression.eval env (bigIntMulNoReduce input_var.1 input_var.2.1)[k.val]).val
            < (m + 1) * 2 ^ (2 * B)) ∧
        ∀ k : Fin (2 * m - 1),
          (Expression.eval env
            (if h : k.val < m then
              (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2)[k.val] +
                var { index := i₀ + m + k.val }
            else (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2)[k.val])).val
            < (m + 1) * 2 ^ (2 * B)) →
        polyValue B (Vector.map (Expression.eval env) (bigIntMulNoReduce input_var.1 input_var.2.1)) =
          polyValue B
            (Vector.map (Expression.eval env)
              (Vector.mapFinRange (2 * m - 1) fun k ↦
                if h : k.val < m then
                  (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2)[k.val] +
                    var { index := i₀ + m + k.val }
                else (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2)[k.val])))
    (h_lt_impl :
      BigInt.Normalized B (Vector.map (Expression.eval env)
          (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })) ∧
        BigInt.Normalized B (Vector.map (Expression.eval env) input_var.2.2) →
        BigInt.value B (Vector.map (Expression.eval env)
            (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })) <
          BigInt.value B (Vector.map (Expression.eval env) input_var.2.2)) :
    BigInt.Normalized B (Vector.map (Expression.eval env)
        (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })) ∧
      BigInt.value B (Vector.map (Expression.eval env)
          (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })) =
        BigInt.value B input.1 * BigInt.value B input.2.1 % BigInt.value B input.2.2 := by

  set qVar := (Vector.mapRange m fun i ↦ var (F := F p) { index := i₀ + i }) with hqVar
  set rVar := (Vector.mapRange m fun i ↦ var (F := F p) { index := i₀ + m + i }) with hrVar
  set qv := (Vector.map (Expression.eval env) qVar : BigInt m (F p)) with hqv
  set rv := (Vector.map (Expression.eval env) rVar : BigInt m (F p)) with hrv

  have ha_lt : ∀ i : Fin m, (Expression.eval env input_var.1[i.val]).val < 2 ^ B := by
    intro i; rw [show Expression.eval env input_var.1[i.val] = input.1[i.val] from by
      rw [← h_input]; simp only [Vector.getElem_map]]; exact ha_norm i
  have hb_lt : ∀ i : Fin m, (Expression.eval env input_var.2.1[i.val]).val < 2 ^ B := by
    intro i; rw [show Expression.eval env input_var.2.1[i.val] = input.2.1[i.val] from by
      rw [← h_input]; simp only [Vector.getElem_map]]; exact hb_norm i
  have hn_lt : ∀ i : Fin m, (Expression.eval env input_var.2.2[i.val]).val < 2 ^ B := by
    intro i; rw [show Expression.eval env input_var.2.2[i.val] = input.2.2[i.val] from by
      rw [← h_input]; simp only [Vector.getElem_map]]; exact hn_norm i
  have hqd_lt : ∀ i : Fin m, (Expression.eval env qVar[i.val]).val < 2 ^ B := by
    intro i; have := hq_norm i; rwa [hqv, Fin.getElem_fin, Vector.getElem_map] at this
  have hrd_lt : ∀ j : ℕ, j < m → (Expression.eval env (var (F := F p) { index := i₀ + m + j })).val < 2 ^ B := by
    intro j hj; have := hr_norm ⟨j, hj⟩
    rwa [hrv, Fin.getElem_fin, Vector.getElem_map, hrVar,
      show (Vector.mapRange m fun i ↦ var (F := F p) { index := i₀ + m + i })[j]
        = var (F := F p) { index := i₀ + m + j } from by simp [circuit_norm]] at this

  have hfield : m * (2 ^ B * 2 ^ B) < p := by
    have h1 : m * (2 ^ B * 2 ^ B) = m * 2 ^ (2 * B) := by rw [two_mul, pow_add]
    rw [h1]
    have h2 : m * 2 ^ (2 * B) ≤ 2 ^ (2 * B) * (m + 1) * 4 := by nlinarith [Nat.two_pow_pos (2 * B)]
    omega

  have hS_eq : (Vector.mapFinRange (2 * m - 1) fun k ↦
        if h : k.val < m then (bigIntMulNoReduce qVar input_var.2.2)[k.val] + var { index := i₀ + m + k.val }
        else (bigIntMulNoReduce qVar input_var.2.2)[k.val])
      = sVec qVar input_var.2.2 (i₀ + m) := by
    rfl

  have h_polyeq := h_eq_impl ⟨fun k => coeff_P_bound env input_var.1 input_var.2.1 k ha_lt hb_lt hfield,
    fun k => by
      have hb := coeff_S_bound env qVar input_var.2.2 (i₀ + m) k hqd_lt hn_lt hrd_lt hfield
      rw [sVec, Vector.getElem_mapFinRange] at hb
      exact hb⟩
  rw [hS_eq] at h_polyeq

  have hP : polyValue B (Vector.map (Expression.eval env) (bigIntMulNoReduce input_var.1 input_var.2.1))
      = BigInt.value B input.1 * BigInt.value B input.2.1 := by
    rw [polyValue_mul_eq env input_var.1 input_var.2.1 ha_lt hb_lt hfield, ← h_input]

  have hSplit := polyValue_sVec_split (B := B) env qVar input_var.2.2 (i₀ + m)
    (fun k hk => by
      have h1 := val_bigIntMulNoReduce_coeff_lt env qVar input_var.2.2 k hqd_lt hn_lt hfield
      have h2 := hrd_lt k.val hk
      have hpow : (2 : ℕ) ^ B ≤ 2 ^ (2 * B) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h3 : m * 2 ^ (2 * B) + 2 ^ (2 * B) ≤ 2 ^ (2 * B) * (m + 1) * 4 := by nlinarith [Nat.two_pow_pos (2 * B)]
      omega)

  have hSqn : polyValue B (Vector.map (Expression.eval env) (bigIntMulNoReduce qVar input_var.2.2))
      = BigInt.value B qv * BigInt.value B input.2.2 := by
    rw [polyValue_Sqn_eq env qVar input_var.2.2 hqd_lt hn_lt hfield, ← h_input]

  have hrval : BigInt.value B (Vector.map (Expression.eval env)
      (Vector.mapRange m fun i => var (F := F p) { index := i₀ + m + i })) = BigInt.value B rv := by
    rw [hrv, hrVar]

  rw [hP] at h_polyeq
  rw [hSplit, hSqn, hrval] at h_polyeq

  have hn_eq : BigInt.value B (Vector.map (Expression.eval env) input_var.2.2) = BigInt.value B input.2.2 := by
    rw [← h_input]
  have hn_norm' : BigInt.Normalized B (Vector.map (Expression.eval env) input_var.2.2) := by
    rw [show (Vector.map (Expression.eval env) input_var.2.2) = input.2.2 from by rw [← h_input]]
    exact hn_norm
  have hr_lt_n : BigInt.value B rv < BigInt.value B input.2.2 := by
    have := h_lt_impl ⟨hr_norm, hn_norm'⟩
    rwa [hn_eq] at this

  refine ⟨hr_norm, ?_⟩
  exact remainder_eq h_polyeq hr_lt_n

lemma mulMod_soundness_core_wm {B : ℕ} (hp : 2 ^ (2 * B) * (m + 1) * 4 < p)
    (i₀ : ℕ) (env : Environment (F p))
    (a b n : Var (BigInt m) (F p))
    (Pv Qv : Vector (Expression (F p)) (2 * m - 1))
    (input : ProvablePair (BigInt m) (ProvablePair (BigInt m) (BigInt m)) (F p))
    (h_input : (Vector.map (Expression.eval env) a,
        Vector.map (Expression.eval env) b,
        Vector.map (Expression.eval env) n) = input)
    (ha_norm : BigInt.Normalized B input.1) (hb_norm : BigInt.Normalized B input.2.1)
    (hn_norm : BigInt.Normalized B input.2.2)
    (hq_norm : BigInt.Normalized B (Vector.map (Expression.eval env)
        (Vector.mapRange m fun i ↦ var { index := i₀ + i })))
    (hr_norm : BigInt.Normalized B (Vector.map (Expression.eval env)
        (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })))
    (heqAB_get : ∀ k : Fin (2 * m - 1),
      Expression.eval env Pv[k.val] = Expression.eval env (bigIntMulNoReduce a b)[k.val])
    (heqQN_get : ∀ k : Fin (2 * m - 1),
      Expression.eval env Qv[k.val]
        = Expression.eval env (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n)[k.val])
    (h_eq_impl :
      ((∀ k : Fin (2 * m - 1), (Expression.eval env Pv[k.val]).val < (m + 1) * 2 ^ (2 * B)) ∧
        ∀ k : Fin (2 * m - 1),
          (Expression.eval env
            (if h : k.val < m then Qv[k.val] + var { index := i₀ + m + k.val } else Qv[k.val])).val
            < (m + 1) * 2 ^ (2 * B)) →
        polyValue B (Vector.map (Expression.eval env) Pv) =
          polyValue B (Vector.map (Expression.eval env)
            (Vector.mapFinRange (2 * m - 1) fun k ↦
              if h : k.val < m then Qv[k.val] + var { index := i₀ + m + k.val } else Qv[k.val])))
    (h_lt_impl :
      BigInt.Normalized B (Vector.map (Expression.eval env)
          (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })) ∧
        BigInt.Normalized B (Vector.map (Expression.eval env) n) →
        BigInt.value B (Vector.map (Expression.eval env)
            (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })) <
          BigInt.value B (Vector.map (Expression.eval env) n)) :
    BigInt.Normalized B (Vector.map (Expression.eval env)
        (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })) ∧
      BigInt.value B (Vector.map (Expression.eval env)
          (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })) =
        BigInt.value B input.1 * BigInt.value B input.2.1 % BigInt.value B input.2.2 := by

  have h_eq_impl' := eqImpl_bridge (rOff := i₀ + m) env Pv (bigIntMulNoReduce a b)
    Qv (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n)
    heqAB_get heqQN_get h_eq_impl

  exact mulMod_soundness_core (B := B) hp i₀ env (a, b, n) input h_input
    ha_norm hb_norm hn_norm hq_norm hr_norm h_eq_impl' h_lt_impl

omit [NeZero m] in

lemma normalized_mapRange {B : ℕ} (off N : ℕ) (env : Environment (F p))
    (hB : 2 ^ B < p)
    (hwit : ∀ i : Fin m, env.get (off + i.val) = ((N / 2 ^ (B * i.val) % 2 ^ B : ℕ) : F p)) :
    BigInt.Normalized B (Vector.map (Expression.eval env)
      (Vector.mapRange m fun i => var (F := F p) { index := off + i })) := by
  intro i
  have hget : (Vector.map (Expression.eval env)
      (Vector.mapRange m fun j => var (F := F p) { index := off + j }))[i.val] = env.get (off + i.val) := by
    simp [circuit_norm]
  rw [Fin.getElem_fin, hget, hwit i, ZMod.val_natCast_of_lt
    (lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos B)) (le_of_lt hB))]
  exact Nat.mod_lt _ (Nat.two_pow_pos B)

lemma mulMod_completeness_core {B : ℕ} (hB : 2 ^ B < p)
    (hp : 2 ^ (2 * B) * (m + 1) * 4 < p)
    (i₀ : ℕ) (env : Environment (F p))
    (input_var : ProvablePair (BigInt m) (ProvablePair (BigInt m) (BigInt m)) (Expression (F p)))
    (input : ProvablePair (BigInt m) (ProvablePair (BigInt m) (BigInt m)) (F p))
    (h_input : (Vector.map (Expression.eval env) input_var.1,
        Vector.map (Expression.eval env) input_var.2.1,
        Vector.map (Expression.eval env) input_var.2.2) = input)
    (ha_norm : BigInt.Normalized B input.1) (hb_norm : BigInt.Normalized B input.2.1)
    (hn_norm : BigInt.Normalized B input.2.2)
    (hab_lt : BigInt.value B input.1 < BigInt.value B input.2.2)
    (hbb_lt : BigInt.value B input.2.1 < BigInt.value B input.2.2)
    (hn_pos : 0 < BigInt.value B input.2.2)
    (hqwit : ∀ i : Fin m, env.get (i₀ + i.val)
      = ((BigInt.value B input.1 * BigInt.value B input.2.1 / BigInt.value B input.2.2
          / 2 ^ (B * i.val) % 2 ^ B : ℕ) : F p))
    (hrwit : ∀ i : Fin m, env.get (i₀ + m + i.val)
      = ((BigInt.value B input.1 * BigInt.value B input.2.1 % BigInt.value B input.2.2
          / 2 ^ (B * i.val) % 2 ^ B : ℕ) : F p)) :
    BigInt.Normalized B (Vector.map (Expression.eval env)
        (Vector.mapRange m fun i ↦ var { index := i₀ + i })) ∧
      BigInt.Normalized B (Vector.map (Expression.eval env)
          (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })) ∧
        (((∀ k : Fin (2 * m - 1),
                (Expression.eval env (bigIntMulNoReduce input_var.1 input_var.2.1)[k.val]).val
                  < (m + 1) * 2 ^ (2 * B)) ∧
              ∀ k : Fin (2 * m - 1),
                (Expression.eval env
                  (if h : k.val < m then
                    (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2)[k.val] +
                      var { index := i₀ + m + k.val }
                  else (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2)[k.val])).val
                  < (m + 1) * 2 ^ (2 * B)) ∧
            polyValue B (Vector.map (Expression.eval env) (bigIntMulNoReduce input_var.1 input_var.2.1)) =
              polyValue B
                (Vector.map (Expression.eval env)
                  (Vector.mapFinRange (2 * m - 1) fun k ↦
                    if h : k.val < m then
                      (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2)[k.val] +
                        var { index := i₀ + m + k.val }
                    else (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2)[k.val]))) ∧
          (BigInt.Normalized B (Vector.map (Expression.eval env)
                (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })) ∧
              BigInt.Normalized B (Vector.map (Expression.eval env) input_var.2.2)) ∧
            BigInt.value B (Vector.map (Expression.eval env)
                (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })) <
              BigInt.value B (Vector.map (Expression.eval env) input_var.2.2) := by

  set a := BigInt.value B input.1 with ha_def
  set b := BigInt.value B input.2.1 with hb_def
  set n := BigInt.value B input.2.2 with hn_def
  set qval := a * b / n with hqval_def
  set rval := a * b % n with hrval_def

  have hmap_a : BigInt.value B (Vector.map (Expression.eval env) input_var.1) = a := by
    rw [ha_def, ← h_input]
  have hmap_b : BigInt.value B (Vector.map (Expression.eval env) input_var.2.1) = b := by
    rw [hb_def, ← h_input]
  have hmap_n : BigInt.value B (Vector.map (Expression.eval env) input_var.2.2) = n := by
    rw [hn_def, ← h_input]
  have hmap_n_norm : BigInt.Normalized B (Vector.map (Expression.eval env) input_var.2.2) := by
    rw [show (Vector.map (Expression.eval env) input_var.2.2) = input.2.2 from by rw [← h_input]]
    exact hn_norm

  have hn_lt : n < 2 ^ (B * m) := BigInt.value_lt hn_norm

  have hq_lt_n : qval < n := by
    rw [hqval_def]
    apply Nat.div_lt_of_lt_mul
    have hab : a * b < n * n := by
      rcases Nat.eq_zero_or_pos b with hb0 | hb0
      · rw [hb0, Nat.mul_zero]; exact Nat.mul_pos hn_pos hn_pos
      · calc a * b < n * b := by
              apply (Nat.mul_lt_mul_right hb0).mpr hab_lt
          _ ≤ n * n := by apply Nat.mul_le_mul_left; omega
    omega
  have hqval_lt : qval < 2 ^ (B * m) := lt_trans hq_lt_n hn_lt
  have hrval_lt : rval < 2 ^ (B * m) := lt_trans (Nat.mod_lt _ hn_pos) hn_lt

  have hqv_val : BigInt.value B (Vector.map (Expression.eval env)
      (Vector.mapRange m fun i ↦ var { index := i₀ + i })) = qval :=
    BigInt.value_mapRange i₀ qval env hB hqval_lt (by intro i; rw [hqwit i])
  have hrv_val : BigInt.value B (Vector.map (Expression.eval env)
      (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })) = rval :=
    BigInt.value_mapRange (i₀ + m) rval env hB hrval_lt (by intro i; rw [hrwit i])

  have hqv_norm : BigInt.Normalized B (Vector.map (Expression.eval env)
      (Vector.mapRange m fun i ↦ var { index := i₀ + i })) :=
    normalized_mapRange i₀ qval env hB (by intro i; rw [hqwit i])
  have hrv_norm : BigInt.Normalized B (Vector.map (Expression.eval env)
      (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })) :=
    normalized_mapRange (i₀ + m) rval env hB (by intro i; rw [hrwit i])

  have ha_lt : ∀ i : Fin m, (Expression.eval env input_var.1[i.val]).val < 2 ^ B := by
    intro i; rw [show Expression.eval env input_var.1[i.val] = input.1[i.val] from by
      rw [← h_input]; simp only [Vector.getElem_map]]; exact ha_norm i
  have hb_lt : ∀ i : Fin m, (Expression.eval env input_var.2.1[i.val]).val < 2 ^ B := by
    intro i; rw [show Expression.eval env input_var.2.1[i.val] = input.2.1[i.val] from by
      rw [← h_input]; simp only [Vector.getElem_map]]; exact hb_norm i
  have hn_lt' : ∀ i : Fin m, (Expression.eval env input_var.2.2[i.val]).val < 2 ^ B := by
    intro i; rw [show Expression.eval env input_var.2.2[i.val] = input.2.2[i.val] from by
      rw [← h_input]; simp only [Vector.getElem_map]]; exact hn_norm i
  have hqd_lt : ∀ i : Fin m, (Expression.eval env (Vector.mapRange m fun j ↦ var (F := F p) { index := i₀ + j })[i.val]).val < 2 ^ B := by
    intro i; have := hqv_norm i; rwa [Fin.getElem_fin, Vector.getElem_map] at this
  have hrd_lt : ∀ j : ℕ, j < m → (Expression.eval env (var (F := F p) { index := i₀ + m + j })).val < 2 ^ B := by
    intro j hj; have := hrv_norm ⟨j, hj⟩
    rwa [Fin.getElem_fin, Vector.getElem_map,
      show (Vector.mapRange m fun i ↦ var (F := F p) { index := i₀ + m + i })[j]
        = var (F := F p) { index := i₀ + m + j } from by simp [circuit_norm]] at this

  have hfield : m * (2 ^ B * 2 ^ B) < p := by
    have h1 : m * (2 ^ B * 2 ^ B) = m * 2 ^ (2 * B) := by rw [two_mul, pow_add]
    rw [h1]
    have h2 : m * 2 ^ (2 * B) ≤ 2 ^ (2 * B) * (m + 1) * 4 := by nlinarith [Nat.two_pow_pos (2 * B)]
    omega

  have hS_eq : (Vector.mapFinRange (2 * m - 1) fun k ↦
        if h : k.val < m then (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2)[k.val]
          + var { index := i₀ + m + k.val }
        else (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2)[k.val])
      = sVec (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2 (i₀ + m) := rfl

  have hP : polyValue B (Vector.map (Expression.eval env) (bigIntMulNoReduce input_var.1 input_var.2.1))
      = a * b := by
    rw [polyValue_mul_eq env input_var.1 input_var.2.1 ha_lt hb_lt hfield, hmap_a, hmap_b]

  have hSplit := polyValue_sVec_split (B := B) env (Vector.mapRange m fun i ↦ var { index := i₀ + i })
    input_var.2.2 (i₀ + m)
    (fun k hk => by
      have h1 := val_bigIntMulNoReduce_coeff_lt env (Vector.mapRange m fun i ↦ var { index := i₀ + i })
        input_var.2.2 k hqd_lt hn_lt' hfield
      have h2 := hrd_lt k.val hk
      have hpow : (2 : ℕ) ^ B ≤ 2 ^ (2 * B) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h3 : m * 2 ^ (2 * B) + 2 ^ (2 * B) ≤ 2 ^ (2 * B) * (m + 1) * 4 := by nlinarith [Nat.two_pow_pos (2 * B)]
      omega)
  have hSqn : polyValue B (Vector.map (Expression.eval env)
      (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2))
      = qval * n := by
    rw [polyValue_Sqn_eq env (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2 hqd_lt hn_lt' hfield,
      hqv_val, hmap_n]
  have hpolyS : polyValue B (Vector.map (Expression.eval env)
      (Vector.mapFinRange (2 * m - 1) fun k ↦
        if h : k.val < m then (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2)[k.val]
          + var { index := i₀ + m + k.val }
        else (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2)[k.val]))
      = a * b := by
    rw [hS_eq, hSplit, hSqn, hrv_val, hqval_def, hrval_def, Nat.div_add_mod']

  refine ⟨hqv_norm, hrv_norm, ⟨⟨?_, ?_⟩, ?_⟩, ⟨hrv_norm, ?_⟩, ?_⟩
  · intro k; exact coeff_P_bound env input_var.1 input_var.2.1 k ha_lt hb_lt hfield
  · intro k
    have hb := coeff_S_bound env (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2 (i₀ + m) k
      hqd_lt hn_lt' hrd_lt hfield
    rw [sVec, Vector.getElem_mapFinRange] at hb
    exact hb
  · rw [hP, hpolyS]
  · exact hmap_n_norm
  · rw [hrv_val, hmap_n, hrval_def]
    exact Nat.mod_lt _ hn_pos

lemma mulMod_completeness_core_wm {B : ℕ} (hB : 2 ^ B < p)
    (hp : 2 ^ (2 * B) * (m + 1) * 4 < p)
    (i₀ : ℕ) (env : Environment (F p))
    (a b n : Var (BigInt m) (F p))
    (Pv Qv : Vector (Expression (F p)) (2 * m - 1))
    (input : ProvablePair (BigInt m) (ProvablePair (BigInt m) (BigInt m)) (F p))
    (h_input : (Vector.map (Expression.eval env) a,
        Vector.map (Expression.eval env) b,
        Vector.map (Expression.eval env) n) = input)
    (ha_norm : BigInt.Normalized B input.1) (hb_norm : BigInt.Normalized B input.2.1)
    (hn_norm : BigInt.Normalized B input.2.2)
    (hab_lt : BigInt.value B input.1 < BigInt.value B input.2.2)
    (hbb_lt : BigInt.value B input.2.1 < BigInt.value B input.2.2)
    (hn_pos : 0 < BigInt.value B input.2.2)
    (hqwit : ∀ i : Fin m, env.get (i₀ + i.val)
      = ((BigInt.value B input.1 * BigInt.value B input.2.1 / BigInt.value B input.2.2
          / 2 ^ (B * i.val) % 2 ^ B : ℕ) : F p))
    (hrwit : ∀ i : Fin m, env.get (i₀ + m + i.val)
      = ((BigInt.value B input.1 * BigInt.value B input.2.1 % BigInt.value B input.2.2
          / 2 ^ (B * i.val) % 2 ^ B : ℕ) : F p))
    (heqAB_get : ∀ k : Fin (2 * m - 1),
      Expression.eval env Pv[k.val] = Expression.eval env (bigIntMulNoReduce a b)[k.val])
    (heqQN_get : ∀ k : Fin (2 * m - 1),
      Expression.eval env Qv[k.val]
        = Expression.eval env (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n)[k.val]) :
    BigInt.Normalized B (Vector.map (Expression.eval env)
        (Vector.mapRange m fun i ↦ var { index := i₀ + i })) ∧
      BigInt.Normalized B (Vector.map (Expression.eval env)
          (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })) ∧
        (((∀ k : Fin (2 * m - 1), (Expression.eval env Pv[k.val]).val < (m + 1) * 2 ^ (2 * B)) ∧
            (∀ k : Fin (2 * m - 1),
              (Expression.eval env
                (if h : k.val < m then Qv[k.val] + var { index := i₀ + m + k.val } else Qv[k.val])).val
                < (m + 1) * 2 ^ (2 * B))) ∧
            polyValue B (Vector.map (Expression.eval env) Pv) =
              polyValue B (Vector.map (Expression.eval env)
                (Vector.mapFinRange (2 * m - 1) fun k ↦
                  if h : k.val < m then Qv[k.val] + var { index := i₀ + m + k.val } else Qv[k.val]))) ∧
          (BigInt.Normalized B (Vector.map (Expression.eval env)
                (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })) ∧
              BigInt.Normalized B (Vector.map (Expression.eval env) n)) ∧
            BigInt.value B (Vector.map (Expression.eval env)
                (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })) <
              BigInt.value B (Vector.map (Expression.eval env) n) := by
  obtain ⟨hqn, hrn, hconj, hlt⟩ :=
    mulMod_completeness_core (B := B) hB hp i₀ env (a, b, n) input h_input
      ha_norm hb_norm hn_norm hab_lt hbb_lt hn_pos hqwit hrwit
  exact ⟨hqn, hrn,
    eqConj_bridge (rOff := i₀ + m) env Pv (bigIntMulNoReduce a b) Qv
      (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n)
      heqAB_get heqQN_get hconj, hlt⟩

end

end MulMod

end Solution.Secp256k1ScalarMulFixedBase

end DonorFile0_1

-- Adapted donor module: Vandermonde
section DonorFile0_2

namespace Solution.Secp256k1ScalarMulFixedBase

open Polynomial

noncomputable def coeffPoly {K : Type*} [CommRing K] {N : ℕ} (coeffs : Fin N → K) : K[X] :=
  ∑ k : Fin N, Polynomial.monomial k.val (coeffs k)

lemma coeffPoly_eval {K : Type*} [CommRing K] {N : ℕ} (coeffs : Fin N → K) (x : K) :
    (coeffPoly coeffs).eval x = ∑ k : Fin N, coeffs k * x ^ k.val := by
  simp only [coeffPoly, eval_finset_sum, eval_monomial]

lemma coeffPoly_natDegree_lt {K : Type*} [CommRing K] {N : ℕ} (hN : 0 < N) (coeffs : Fin N → K) :
    (coeffPoly coeffs).natDegree < N := by
  have hle : (coeffPoly coeffs).natDegree ≤ N - 1 := by
    refine natDegree_sum_le_of_forall_le _ _ (fun k _ => ?_)
    exact (natDegree_monomial_le _).trans (by have := k.isLt; omega)
  omega

lemma coeffPoly_coeff {K : Type*} [CommRing K] {N : ℕ} (coeffs : Fin N → K) (j : Fin N) :
    (coeffPoly coeffs).coeff j.val = coeffs j := by
  simp only [coeffPoly, finset_sum_coeff, coeff_monomial]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    rw [if_neg]
    intro h; exact hb (Fin.ext h)
  · intro h; exact absurd (Finset.mem_univ j) h

lemma cauchy_diag {K : Type*} [CommRing K] {m : ℕ} (hm : 0 < m)
    (a b : Fin m → K) (x : K) :
    (∑ i : Fin m, a i * x ^ i.val) * (∑ j : Fin m, b j * x ^ j.val)
      = ∑ k : Fin (2 * m - 1),
          (∑ i : Fin m, if h : i.val ≤ k.val ∧ k.val - i.val < m then
            a i * b ⟨k.val - i.val, h.2⟩ else 0) * x ^ k.val := by
  rw [Fintype.sum_mul_sum]

  have hL : (∑ i : Fin m, ∑ j : Fin m, a i * x ^ i.val * (b j * x ^ j.val))
      = ∑ i : Fin m, ∑ j : Fin m, (a i * b j) * x ^ (i.val + j.val) := by
    apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _
    rw [pow_add]; ring
  rw [hL]

  have hR : (∑ k : Fin (2 * m - 1),
        (∑ i : Fin m, if h : i.val ≤ k.val ∧ k.val - i.val < m then
          a i * b ⟨k.val - i.val, h.2⟩ else 0) * x ^ k.val)
      = ∑ k : Fin (2 * m - 1), ∑ i : Fin m,
          if h : i.val ≤ k.val ∧ k.val - i.val < m then
            (a i * b ⟨k.val - i.val, h.2⟩) * x ^ k.val else 0 := by
    apply Finset.sum_congr rfl; intro k _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl; intro i _
    by_cases h : i.val ≤ k.val ∧ k.val - i.val < m
    · rw [dif_pos h, dif_pos h]
    · rw [dif_neg h, dif_neg h, zero_mul]
  rw [hR]
  conv_rhs => rw [Finset.sum_comm]

  apply Finset.sum_congr rfl; intro i _

  classical
  have hfilter : (∑ k : Fin (2 * m - 1),
        if h : i.val ≤ k.val ∧ k.val - i.val < m then
          a i * b ⟨k.val - i.val, h.2⟩ * x ^ k.val else 0)
      = ∑ k ∈ (Finset.univ.filter (fun k : Fin (2 * m - 1) => i.val ≤ k.val ∧ k.val - i.val < m)),
          if h : i.val ≤ k.val ∧ k.val - i.val < m then
            a i * b ⟨k.val - i.val, h.2⟩ * x ^ k.val else 0 := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl; intro k _
    by_cases h : i.val ≤ k.val ∧ k.val - i.val < m
    · rw [dif_pos h, if_pos h]
    · rw [dif_neg h, if_neg h]
  rw [hfilter]

  refine Finset.sum_nbij'
    (i := fun (j : Fin m) => (⟨i.val + j.val, by have := i.isLt; have := j.isLt; omega⟩ : Fin (2 * m - 1)))
    (j := fun (k : Fin (2 * m - 1)) => (⟨min (k.val - i.val) (m - 1), by omega⟩ : Fin m))
    ?hi ?hj ?left_inv ?right_inv ?h
  case hi =>
    intro j _; refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    show i.val ≤ i.val + j.val ∧ (i.val + j.val) - i.val < m
    have := j.isLt; omega
  case hj =>
    intro k hk; exact Finset.mem_univ _
  case left_inv =>
    intro j _
    show (⟨min ((i.val + j.val) - i.val) (m - 1), _⟩ : Fin m) = j
    apply Fin.ext; show min ((i.val + j.val) - i.val) (m - 1) = j.val
    have := j.isLt; omega
  case right_inv =>
    intro k hk; obtain ⟨_, hle, hlt⟩ := Finset.mem_filter.mp hk
    show (⟨i.val + min (k.val - i.val) (m - 1), _⟩ : Fin (2 * m - 1)) = k
    apply Fin.ext; show i.val + min (k.val - i.val) (m - 1) = k.val
    omega
  case h =>
    intro j _
    show a i * b j * x ^ (i.val + j.val)
      = (if h : i.val ≤ (i.val + j.val) ∧ (i.val + j.val) - i.val < m then
          a i * b ⟨(i.val + j.val) - i.val, h.2⟩ * x ^ (i.val + j.val) else 0)
    have hguard : i.val ≤ i.val + j.val ∧ (i.val + j.val) - i.val < m := by
      have := j.isLt; omega
    rw [dif_pos hguard]
    have hbj : (⟨(i.val + j.val) - i.val, hguard.2⟩ : Fin m) = j := by
      apply Fin.ext; show (i.val + j.val) - i.val = j.val; omega
    rw [hbj]

lemma interp_uniqueness {K : Type*} [Field K] {N : ℕ}
    (u v : Fin N → K) (f : Fin N → K) (hf : Function.Injective f)
    (heval : ∀ i : Fin N, (∑ k : Fin N, u k * f i ^ k.val) = ∑ k : Fin N, v k * f i ^ k.val) :
    ∀ j : Fin N, u j = v j := by
  intro j
  have hN : 0 < N := Fin.pos_iff_nonempty.mpr ⟨j⟩
  have hpoly : coeffPoly u = coeffPoly v := by
    apply eq_of_natDegree_lt_card_of_eval_eq _ _ hf
    · intro i
      rw [coeffPoly_eval, coeffPoly_eval]; exact heval i
    · rw [Fintype.card_fin]
      exact max_lt (coeffPoly_natDegree_lt hN u) (coeffPoly_natDegree_lt hN v)
  have := congrArg (fun q => Polynomial.coeff q j.val) hpoly
  simpa only [coeffPoly_coeff] using this

end Solution.Secp256k1ScalarMulFixedBase

end DonorFile0_2

-- Adapted donor module: Normalize
section DonorFile0_3

namespace Solution.Secp256k1ScalarMulFixedBase
open Solution.Secp256k1ScalarMulFixedBase.Limbs

section
variable {p : ℕ} [Fact p.Prime]
variable {m : ℕ}

namespace Normalize

def main (P : BigIntParams p m) [Fact (p > 2)] (x : Var (BigInt m) (F p)) :
    Circuit (F p) Unit :=
  Circuit.forEach x (fun xi => Gadgets.ToBits.rangeCheck P.B P.hB xi)

instance elaborated (P : BigIntParams p m) [Fact (p > 2)] :
    ElaboratedCircuit (F p) (BigInt m) unit (main P) where
  localLength _ := m * P.B
  localLength_eq := by
    intro input offset
    simp only [main, circuit_norm, Gadgets.ToBits.rangeCheck]
  subcircuitsConsistent := by
    intro input offset
    simp +arith only [main, circuit_norm, Gadgets.ToBits.rangeCheck]
  channelsLawful := by
    simp only [main, circuit_norm, Gadgets.ToBits.rangeCheck]

def Assumptions (_ : BigInt m (F p)) : Prop := True

def Spec (B : ℕ) (x : BigInt m (F p)) : Prop := BigInt.Normalized B x

def circuit (P : BigIntParams p m) [Fact (p > 2)] : FormalAssertion (F p) (BigInt m) where
  main := main P
  Assumptions := Assumptions
  Spec := Spec P.B
  soundness := by
    circuit_proof_start
    simp_all only [circuit_norm, Gadgets.ToBits.rangeCheck, BigInt.Normalized]
    intro i
    rw [← h_input, Vector.getElem_map]
    exact h_holds i
  completeness := by
    circuit_proof_start
    simp_all only [circuit_norm, Gadgets.ToBits.rangeCheck, BigInt.Normalized]
    intro i
    have := h_spec i
    rwa [← h_input, Vector.getElem_map] at this

theorem computableWitnesses (P : BigIntParams p m) [Fact (p > 2)] :
    (circuit P).ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition input env env')
    ((main P input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.forEach_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_structuralComputableWitnesses_iff]
  intro i
  apply Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_flatStructuralComputableWitnesses
  · intro env₁ env₂ h_input
    have h : (eval env₁ input)[i.val] = (eval env₂ input)[i.val] := by
      simpa only [Fin.getElem_fin] using congrArg (fun x : BigInt m (F p) => x[i]) h_input
    rw [← ProvableType.getElem_eval_fields_prover (env := env₁) input i.val i.isLt,
      ← ProvableType.getElem_eval_fields_prover (env := env₂) input i.val i.isLt] at h
    simpa [CircuitType.eval_expression_prover_to_verifier (M := field),
      CircuitType.eval_expression (M := field), ProvableType.eval, explicit_provable_type] using h
  · exact rangeCheckComputableWitnesses P.B P.hB

theorem computableWitness (P : BigIntParams p m) [Fact (p > 2)] : ∀ n input,
    ProverEnvironment.OnlyAccessedBelow n
      (fun env : ProverEnvironment (F p) => eval env input) →
    Circuit.ComputableWitnesses (main P input) n := by
  exact Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnesses_implies
    (computableWitnesses P)

end Normalize

end

end Solution.Secp256k1ScalarMulFixedBase

end DonorFile0_3

-- Adapted donor module: Equal
section DonorFile0_4

namespace Solution.Secp256k1ScalarMulFixedBase
open Solution.Secp256k1ScalarMulFixedBase.Limbs

section
variable {p : ℕ} [Fact p.Prime]
variable {m : ℕ}

namespace Equal

structure Inputs (m : ℕ) (F : Type) where
  lhs : BigInt m F
  rhs : BigInt m F
deriving ProvableStruct

def main (input : Var (Inputs m) (F p)) : Circuit (F p) Unit :=
  input.lhs === input.rhs

instance elaborated : ElaboratedCircuit (F p) (Inputs m) unit main where
  localLength _ := 0

def Assumptions (B : ℕ) (input : Inputs m (F p)) : Prop :=
  input.lhs.Normalized B ∧ input.rhs.Normalized B

def Spec (B : ℕ) (input : Inputs m (F p)) : Prop :=
  input.lhs.value B = input.rhs.value B

def circuit (P : BigIntParams p m) : FormalAssertion (F p) (Inputs m) where
  main := main
  Assumptions := Assumptions P.B
  Spec := Spec P.B
  soundness := by
    circuit_proof_start
    simp only [← h_input]
    rw [h_holds]
  completeness := by
    circuit_proof_start
    simp only [← h_input] at h_assumptions h_spec
    exact BigInt.value_inj h_assumptions.1 h_assumptions.2 h_spec

end Equal

end

end Solution.Secp256k1ScalarMulFixedBase

end DonorFile0_4

-- Adapted donor module: LessThan
section DonorFile0_5

namespace Solution.Secp256k1ScalarMulFixedBase
open Solution.Secp256k1ScalarMulFixedBase.Limbs

section
variable {p : ℕ} [Fact p.Prime]
variable {m : ℕ} [NeZero m]

namespace LessThan

structure Inputs (m : ℕ) (F : Type) where
  lhs : BigInt m F
  rhs : BigInt m F
deriving ProvableStruct

private def evalValue (B : ℕ) (env : ProverEnvironment (F p))
    (x : Var (BigInt m) (F p)) : ℕ :=
  Solution.Secp256k1ScalarMulFixedBase.Limbs.fromLimbs B ((x.map (Expression.eval env.toEnvironment)).toList.map ZMod.val)

def main (P : BigIntParams p m) [Fact (p > 2)] (input : Var (Inputs m) (F p)) :
    Circuit (F p) Unit := do
  let a := input.lhs
  let b := input.rhs

  let d ← ProvableType.witness (α := BigInt m) fun env =>
    let dval : ℕ := evalValue P.B env b - 1 - evalValue P.B env a
    Vector.ofFn fun k : Fin m => ((dval / 2 ^ (P.B * k.val) % 2 ^ P.B : ℕ) : F p)

  Normalize.circuit P d

  let carry ← witnessVector (m - 1) fun env =>
    let av : ℕ → ℕ := fun j => if h : j < m then (Expression.eval env.toEnvironment a[j]).val else 0
    let dv : ℕ → ℕ := fun j => if h : j < m then (Expression.eval env.toEnvironment d[j]).val else 0
    Vector.ofFn fun k : Fin (m - 1) =>
      (((1 + ∑ j ∈ Finset.range (k.val + 1), (av j + dv j) * 2 ^ (P.B * j))
          / 2 ^ (P.B * (k.val + 1)) : ℕ) : F p)

  Circuit.forEach carry (fun c => assertZero (c * (c - 1)))

  let constraints : Vector (Expression (F p)) m := Vector.mapFinRange m fun k =>
    let carryIn : Expression (F p) :=
      if h : k.val = 0 then 0 else carry[k.val - 1]'(by omega)
    let one : Expression (F p) := if k.val = 0 then 1 else 0
    let carryOut : Expression (F p) :=
      if h : k.val < m - 1 then carry[k.val]'h else 0
    a[k.val] + d[k.val] + carryIn + one - b[k.val] - carryOut * (2 ^ P.B : F p)
  Circuit.forEach constraints assertZero

instance elaborated (P : BigIntParams p m) [Fact (p > 2)] :
    ElaboratedCircuit (F p) (Inputs m) unit (main P) where

  localLength _ := m + m * P.B + (m - 1)
  localLength_eq := by
    intro input offset
    simp only [main, circuit_norm, Normalize.circuit, Normalize.elaborated, Normalize.main,
      Gadgets.ToBits.rangeCheck]
    simp +arith [circuit_norm]
  subcircuitsConsistent := by
    intro input offset
    simp +arith only [main, circuit_norm, Normalize.circuit, Normalize.elaborated, Normalize.main,
      Gadgets.ToBits.rangeCheck]
  channelsLawful := by
    intro offset
    simp only [main, circuit_norm, Normalize.circuit, Normalize.elaborated, Normalize.main,
      Gadgets.ToBits.rangeCheck]

def Assumptions (B : ℕ) (input : Inputs m (F p)) : Prop :=
  input.lhs.Normalized B ∧ input.rhs.Normalized B

def Spec (B : ℕ) (input : Inputs m (F p)) : Prop :=
  input.lhs.value B < input.rhs.value B

def circuit (P : BigIntParams p m) [Fact (p > 2)] :
    FormalAssertion (F p) (Inputs m) where
    main := main P
    Assumptions := Assumptions P.B
    Spec := Spec P.B
    soundness := by
      obtain ⟨B, W, hB, hW, hB1, hWB, hWp, hp⟩ := P
      circuit_proof_start
      simp only [circuit_norm, Normalize.circuit, Normalize.elaborated, Normalize.main,
        Gadgets.ToBits.rangeCheck] at h_holds ⊢
      obtain ⟨h_dnorm, h_cbool, h_lin⟩ := h_holds
      obtain ⟨ha_norm, hb_norm⟩ := h_assumptions
      rcases Nat.eq_zero_or_pos m with hm | hm
      ·

        exact absurd hm (NeZero.ne m)

      set An : ℕ → ℕ := fun k => if h : k < m then (input.lhs[k]'h).val else 0 with hAn
      set Dn : ℕ → ℕ := fun k => (env.get (i₀ + k)).val with hDn
      set Bn : ℕ → ℕ := fun k => if h : k < m then (input.rhs[k]'h).val else 0 with hBn
      set Cn : ℕ → ℕ := fun k =>
        if k < m - 1 then (env.get (i₀ + m + m * B + k)).val else 0 with hCn

      have hAn_lt : ∀ k, k < m → An k < 2 ^ B := by
        intro k hk; simp only [hAn, dif_pos hk]; exact ha_norm ⟨k, hk⟩
      have hBn_lt : ∀ k, k < m → Bn k < 2 ^ B := by
        intro k hk; simp only [hBn, dif_pos hk]; exact hb_norm ⟨k, hk⟩
      have hDn_lt : ∀ k, k < m → Dn k < 2 ^ B := by
        intro k hk
        have hspec := h_dnorm trivial ⟨k, hk⟩
        have heq : (Vector.map (Expression.eval env)
            (Vector.mapRange m fun i => var { index := i₀ + i }))[(⟨k, hk⟩ : Fin m)]
            = env.get (i₀ + k) := by simp [circuit_norm]
        rw [heq] at hspec
        simpa [hDn] using hspec

      have hCn_le : ∀ k, k < m → Cn k ≤ 1 := by
        intro k hk
        simp only [hCn]
        split
        · rename_i hk1
          have hb := h_cbool ⟨k, hk1⟩
          have : IsBool (env.get (i₀ + m + m * B + k)) := by
            rw [IsBool.iff_mul_sub_one]; rw [show env.get (i₀ + m + m * B + k) - 1
              = env.get (i₀ + m + m * B + k) + -1 by ring]; exact hb
          have := IsBool.val_lt_two this
          omega
        · omega

      have hPB1 : 2 ^ (B + 1) < p := by
        have h1 : 2 ^ (B + 1) ≤ 2 ^ (2 * B + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
        have h2 : 2 ^ (2 * B + 2) = 2 ^ (2 * B) * 4 := by rw [pow_add]; ring
        have h3 : 2 ^ (2 * B) * 4 ≤ 2 ^ (2 * B) * (m + 1) * 4 := by
          have : 1 ≤ m + 1 := by omega
          nlinarith [Nat.two_pow_pos (2 * B)]
        omega

      have h_limb : ∀ k : ℕ, (hk : k < m) →
          An k + Dn k + (if k = 0 then 0 else Cn (k - 1)) + (if k = 0 then 1 else 0)
            = Bn k + Cn k * 2 ^ B := by
        intro k hk
        have hlin := h_lin ⟨k, hk⟩

        have ha_e : Expression.eval env input_var.lhs[(⟨k, hk⟩ : Fin m).val] = input.lhs[k]'hk := by
          rw [← h_input]; simp [Vector.getElem_map]
        have hb_e : Expression.eval env input_var.rhs[(⟨k, hk⟩ : Fin m).val] = input.rhs[k]'hk := by
          rw [← h_input]; simp [Vector.getElem_map]
        have hcin_e : Expression.eval env
            (if h : (⟨k, hk⟩ : Fin m).val = 0 then 0
              else var { index := i₀ + m + m * B + ((⟨k, hk⟩ : Fin m).val - 1) })
            = if k = 0 then 0 else env.get (i₀ + m + m * B + (k - 1)) := by
          simp only []
          split <;> simp [circuit_norm]
        have hone_e : Expression.eval env (if (⟨k, hk⟩ : Fin m).val = 0 then 1 else 0)
            = if k = 0 then (1 : F p) else 0 := by
          simp only []; split <;> simp [circuit_norm]
        have hcout_e : Expression.eval env
            (if h : (⟨k, hk⟩ : Fin m).val < m - 1
              then var { index := i₀ + m + m * B + (⟨k, hk⟩ : Fin m).val } else 0)
            = if k < m - 1 then env.get (i₀ + m + m * B + k) else 0 := by
          simp only []
          split <;> simp [circuit_norm]
        simp only [ha_e, hb_e, hcin_e, hone_e, hcout_e] at hlin

        have h3 : (if k = 0 then (0:F p) else env.get (i₀ + m + m * B + (k - 1))).val ≤ 1 := by
          split
          · simp [ZMod.val_zero]
          · rename_i h
            have hkm : k - 1 < m := by omega
            have := hCn_le (k - 1) hkm
            simp only [hCn] at this
            rw [if_pos (by omega)] at this
            exact this
        have h4 : (if k = 0 then (1 : F p) else 0).val ≤ 1 := by
          split
          · simp [ZMod.val_one]
          · simp [ZMod.val_zero]
        have hpw : 2 ^ B + 2 ^ B = 2 ^ (B + 1) := by rw [pow_succ]; ring
        have hsum_lt : (input.lhs[k]'hk).val + (env.get (i₀ + k)).val
            + (if k = 0 then (0:F p) else env.get (i₀ + m + m * B + (k - 1))).val
            + (if k = 0 then (1 : F p) else 0).val < p := by
          have h1 := hAn_lt k hk; have h2 := hDn_lt k hk
          simp only [hAn, hDn, dif_pos hk] at h1 h2
          omega
        have hcout_le : (if k < m - 1 then env.get (i₀ + m + m * B + k) else (0:F p)).val ≤ 1 := by
          split
          · rename_i h1
            have := hCn_le k hk
            simp only [hCn, if_pos h1] at this
            exact this
          · simp
        have hrhs_lt : (input.rhs[k]'hk).val
            + (if k < m - 1 then env.get (i₀ + m + m * B + k) else (0:F p)).val * 2 ^ B < p := by
          have h1 := hBn_lt k hk
          simp only [hBn, dif_pos hk] at h1
          nlinarith [Nat.two_pow_pos B, hcout_le]
        have hlin' : (input.lhs[k]'hk) + env.get (i₀ + k)
            + (if k = 0 then (0:F p) else env.get (i₀ + m + m * B + (k - 1)))
            + (if k = 0 then (1 : F p) else 0) - (input.rhs[k]'hk)
            - (if k < m - 1 then env.get (i₀ + m + m * B + k) else (0:F p)) * (2 ^ B : F p) = 0 := by
          rw [sub_eq_add_neg, sub_eq_add_neg]; exact hlin
        have hlift := per_limb_lift (B := B) (input.lhs[k]'hk) (env.get (i₀ + k))
          (if k = 0 then (0:F p) else env.get (i₀ + m + m * B + (k - 1)))
          (if k = 0 then (1 : F p) else 0) (input.rhs[k]'hk)
          (if k < m - 1 then env.get (i₀ + m + m * B + k) else (0:F p)) hB hsum_lt hrhs_lt hlin'

        have hcin_val : (if k = 0 then (0:F p) else env.get (i₀ + m + m * B + (k - 1))).val
            = if k = 0 then 0 else Cn (k - 1) := by
          split
          · simp
          · rename_i hk0
            simp only [hCn]
            rw [if_pos (by omega)]
        have hone_val : (if k = 0 then (1 : F p) else 0).val = if k = 0 then 1 else 0 := by
          split
          · simp [ZMod.val_one]
          · simp [ZMod.val_zero]
        have hcout_val : (if k < m - 1 then env.get (i₀ + m + m * B + k) else (0:F p)).val
            = Cn k := by
          simp only [hCn]
          split <;> simp
        rw [hcin_val, hone_val, hcout_val] at hlift
        simp only [hAn, hDn, hBn, dif_pos hk]
        omega

      have htop0 : Cn (m - 1) = 0 := by
        simp only [hCn]
        rw [if_neg (lt_irrefl _)]

      have hval_a : BigInt.value B input.lhs = ∑ k ∈ Finset.range m, An k * 2 ^ (B * k) := by
        rw [BigInt.value_eq_sum, ← Fin.sum_univ_eq_sum_range (fun k => An k * 2 ^ (B * k))]
        apply Finset.sum_congr rfl
        intro i _
        simp only [hAn, dif_pos i.isLt, Fin.getElem_fin]
      have hval_b : BigInt.value B input.rhs = ∑ k ∈ Finset.range m, Bn k * 2 ^ (B * k) := by
        rw [BigInt.value_eq_sum, ← Fin.sum_univ_eq_sum_range (fun k => Bn k * 2 ^ (B * k))]
        apply Finset.sum_congr rfl
        intro i _
        simp only [hBn, dif_pos i.isLt, Fin.getElem_fin]

      have hsum_eq : (∑ k ∈ Finset.range m,
            ((An k + Dn k + (if k = 0 then 0 else Cn (k - 1)) + (if k = 0 then 1 else 0)) * 2 ^ (B * k)))
          = ∑ k ∈ Finset.range m, ((Bn k + Cn k * 2 ^ B) * 2 ^ (B * k)) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.mem_range] at hk
        rw [h_limb k hk]

      have hLHS : (∑ k ∈ Finset.range m,
            (An k + Dn k + (if k = 0 then 0 else Cn (k - 1)) + (if k = 0 then 1 else 0)) * 2 ^ (B * k))
          = (∑ k ∈ Finset.range m, An k * 2 ^ (B * k))
            + (∑ k ∈ Finset.range m, Dn k * 2 ^ (B * k))
            + (∑ k ∈ Finset.range m, (if k = 0 then 0 else Cn (k - 1)) * 2 ^ (B * k))
            + (∑ k ∈ Finset.range m, (if k = 0 then 1 else 0) * 2 ^ (B * k)) := by
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _; ring
      have hRHS : (∑ k ∈ Finset.range m, (Bn k + Cn k * 2 ^ B) * 2 ^ (B * k))
          = (∑ k ∈ Finset.range m, Bn k * 2 ^ (B * k))
            + (∑ k ∈ Finset.range m, Cn k * 2 ^ (B * (k + 1))) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _
        rw [Nat.mul_add, Nat.mul_one, pow_add]; ring

      have hone_sum : (∑ k ∈ Finset.range m, (if k = 0 then 1 else 0) * 2 ^ (B * k)) = 1 := by
        rw [Finset.sum_eq_single 0]
        · simp
        · intro k _ hk0; simp [hk0]
        · intro h; exact absurd (Finset.mem_range.mpr hm) h

      have htel := carry_telescope B Cn m
      rw [if_neg (by omega : ¬ (m = 0)), htop0, Nat.zero_mul, Nat.add_zero] at htel

      rw [hLHS, hRHS, hone_sum, htel] at hsum_eq

      rw [hval_a, hval_b]

      have hd_nonneg : 0 ≤ ∑ k ∈ Finset.range m, Dn k * 2 ^ (B * k) := Nat.zero_le _
      omega
    completeness := by
      obtain ⟨B, W, hB, hW, hB1, hWB, hWp, hp⟩ := P
      circuit_proof_start
      simp only [circuit_norm, Normalize.circuit, Normalize.elaborated, Normalize.main,
        Gadgets.ToBits.rangeCheck] at h_env ⊢
      obtain ⟨h_dwit, h_cwit, -⟩ := h_env
      obtain ⟨ha_norm, hb_norm⟩ := h_assumptions

      set An : ℕ → ℕ := fun k => if h : k < m then (input.lhs[k]'h).val else 0 with hAn
      set Bn : ℕ → ℕ := fun k => if h : k < m then (input.rhs[k]'h).val else 0 with hBn

      have hd_val : ∀ i : Fin m, (env.get (i₀ + i.val)).val
          = (evalValue B env input_var.rhs - 1 - evalValue B env input_var.lhs)
              / 2 ^ (B * i.val) % 2 ^ B := by
        intro i
        rw [h_dwit i]
        simp only [Vector.getElem_ofFn]
        rw [ZMod.val_natCast_of_lt]
        exact lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos B)) (le_of_lt hB)

      have heva : evalValue B env input_var.lhs = BigInt.value B input.lhs := by
        rw [evalValue, BigInt.value, ← h_input]
      have hevb : evalValue B env input_var.rhs = BigInt.value B input.rhs := by
        rw [evalValue, BigInt.value, ← h_input]

      set va := BigInt.value B input.lhs with hva
      set vb := BigInt.value B input.rhs with hvb

      set dtot : ℕ := vb - 1 - va with hdtot

      have hva_lt : va < 2 ^ (B * m) := BigInt.value_lt ha_norm
      have hvb_lt : vb < 2 ^ (B * m) := BigInt.value_lt hb_norm

      have hd_val' : ∀ i : Fin m, (env.get (i₀ + i.val)).val = dtot / 2 ^ (B * i.val) % 2 ^ B := by
        intro i; rw [hd_val i, heva, hevb]

      set Dn : ℕ → ℕ := fun k => if h : k < m then (env.get (i₀ + k)).val else 0 with hDn
      have hDn_eq : ∀ k, k < m → Dn k = dtot / 2 ^ (B * k) % 2 ^ B := by
        intro k hk; simp only [hDn, dif_pos hk]; exact hd_val' ⟨k, hk⟩
      have hDn_lt : ∀ k, k < m → Dn k < 2 ^ B := by
        intro k hk; rw [hDn_eq k hk]; exact lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos B)) (le_refl _)
      have hAn_lt : ∀ k, k < m → An k < 2 ^ B := fun k hk => by
        simp only [hAn, dif_pos hk]; exact ha_norm ⟨k, hk⟩
      have hBn_lt : ∀ k, k < m → Bn k < 2 ^ B := fun k hk => by
        simp only [hBn, dif_pos hk]; exact hb_norm ⟨k, hk⟩

      set gfun : ℕ → ℕ := fun k => An k + Dn k with hgfun
      have hgfun_le : ∀ j, gfun j ≤ 2 * (2 ^ B - 1) := by
        intro j
        rcases Nat.lt_or_ge j m with hj | hj
        · have := hAn_lt j hj; have := hDn_lt j hj; simp only [hgfun]; omega
        · simp only [hgfun, hAn, hDn, dif_neg (by omega : ¬ j < m)]; omega
      set P : ℕ → ℕ := fun k => 1 + ∑ j ∈ Finset.range (k + 1), gfun j * 2 ^ (B * j) with hP

      have hdtot_lt : dtot < 2 ^ (B * m) := by rw [hdtot]; omega
      have hadd : va + dtot + 1 = vb := by rw [hdtot]; omega

      have hvd : BigInt.value B (Vector.map (Expression.eval env.toEnvironment)
          (Vector.mapRange m fun i => var { index := i₀ + i })) = dtot := by
        rw [BigInt.value_eq_sum]
        have hstep : (∑ k : Fin m, ((Vector.map (Expression.eval env.toEnvironment)
            (Vector.mapRange m fun i => var { index := i₀ + i }))[k]).val * 2 ^ (B * k.val))
            = ∑ k ∈ Finset.range m, (dtot / 2 ^ (B * k) % 2 ^ B) * 2 ^ (B * k) := by
          rw [← Fin.sum_univ_eq_sum_range (fun k => (dtot / 2 ^ (B * k) % 2 ^ B) * 2 ^ (B * k))]
          apply Finset.sum_congr rfl
          intro i _
          have : (Vector.map (Expression.eval env.toEnvironment)
              (Vector.mapRange m fun j => var { index := i₀ + j }))[i] = env.get (i₀ + i.val) := by
            simp [circuit_norm]
          rw [this, hd_val' i]
        rw [hstep, limb_decomp_mod, Nat.mod_eq_of_lt hdtot_lt]

      have hCn_eq : ∀ k : ℕ, k < m - 1 →
          (env.get (i₀ + m + m * B + k)).val = P k / 2 ^ (B * (k + 1)) := by
        intro k hk

        have hraw : (1 + ∑ x ∈ Finset.range (k + 1),
            ((if h : x < m then (Expression.eval env.toEnvironment input_var.lhs[x]).val else 0) +
              (if h : x < m then (env.get (i₀ + x)).val else 0)) * 2 ^ (B * x)) / 2 ^ (B * (k + 1))
            = P k / 2 ^ (B * (k + 1)) := by
          congr 1
          simp only [hP]
          congr 1
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.mem_range] at hj
          have hjm : j < m := by omega
          congr 1
          simp only [hgfun, hAn, hDn, dif_pos hjm]
          congr 1
          rw [← h_input]; simp [Vector.getElem_map]
        rw [h_cwit ⟨k, hk⟩]
        simp only [Vector.getElem_ofFn]
        rw [ZMod.val_natCast_of_lt, hraw]
        rw [hraw]
        have hbit : P k / 2 ^ (B * (k + 1)) ≤ 1 := (ripple_carry B gfun hgfun_le k).2
        have := hB; have := Nat.two_pow_pos B; omega

      have hm : 0 < m := by
        by_contra h
        have hm0 : m = 0 := by omega
        have h1 : va < 2 ^ (B * m) := hva_lt
        have h2 : vb < 2 ^ (B * m) := hvb_lt
        rw [hm0, Nat.mul_zero, pow_zero] at h1 h2
        omega

      have hsum_an : (∑ j ∈ Finset.range m, An j * 2 ^ (B * j)) = va := by
        rw [hva, BigInt.value_eq_sum, ← Fin.sum_univ_eq_sum_range (fun j => An j * 2 ^ (B * j))]
        apply Finset.sum_congr rfl
        intro i _; simp only [hAn, dif_pos i.isLt, Fin.getElem_fin]
      have hsum_dn : (∑ j ∈ Finset.range m, Dn j * 2 ^ (B * j)) = dtot := by
        rw [← hvd, BigInt.value_eq_sum, ← Fin.sum_univ_eq_sum_range (fun j => Dn j * 2 ^ (B * j))]
        apply Finset.sum_congr rfl
        intro i _
        simp only [hDn, dif_pos i.isLt]
        congr 1
        have : (Vector.map (Expression.eval env.toEnvironment)
            (Vector.mapRange m fun j => var { index := i₀ + j }))[i] = env.get (i₀ + i.val) := by
          simp [circuit_norm]
        rw [this]

      have hPlast : P (m - 1) = vb := by
        simp only [hP]
        rw [show m - 1 + 1 = m by omega]
        simp only [hgfun]
        rw [show (∑ j ∈ Finset.range m, (An j + Dn j) * 2 ^ (B * j))
            = (∑ j ∈ Finset.range m, An j * 2 ^ (B * j))
              + (∑ j ∈ Finset.range m, Dn j * 2 ^ (B * j)) by
          rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro j _; ring]
        rw [hsum_an, hsum_dn]; omega

      have hBn_eq : ∀ k, k < m → Bn k = vb / 2 ^ (B * k) % 2 ^ B := by
        intro k hk
        have hvb_sum : vb = ∑ j ∈ Finset.range m, Bn j * 2 ^ (B * j) := by
          rw [hvb, BigInt.value_eq_sum, ← Fin.sum_univ_eq_sum_range (fun j => Bn j * 2 ^ (B * j))]
          apply Finset.sum_congr rfl
          intro i _; simp only [hBn, dif_pos i.isLt, Fin.getElem_fin]
        rw [hvb_sum]
        exact (digit_extract B Bn (fun j => by
          rcases Nat.lt_or_ge j m with hj | hj
          · exact hBn_lt j hj
          · simp only [hBn, dif_neg (by omega : ¬ j < m)]; exact Nat.two_pow_pos B) m k hk).symm

      have hCn_bit : ∀ k : ℕ, k < m - 1 → IsBool (env.get (i₀ + m + m * B + k)) := by
        intro k hk
        have hle : (env.get (i₀ + m + m * B + k)).val ≤ 1 := by
          rw [hCn_eq k hk]; exact (ripple_carry B gfun hgfun_le k).2
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h0 | h1
        · left; exact (ZMod.val_eq_zero _).mp h0
        · right
          have : env.get (i₀ + m + m * B + k) = ((1 : ℕ) : F p) := by
            rw [← h1, ZMod.natCast_zmod_val]
          simpa using this
      refine ⟨?_, ?_, ?_⟩
      ·
        refine ⟨trivial, ?_⟩
        intro i
        have : (Vector.map (Expression.eval env.toEnvironment)
            (Vector.mapRange m fun j => var { index := i₀ + j }))[i] = env.get (i₀ + i.val) := by
          simp [circuit_norm]
        rw [this]
        have := hDn_lt i.val i.isLt
        simp only [hDn, dif_pos i.isLt] at this
        exact this
      ·
        intro i
        have hbit := hCn_bit i.val i.isLt
        rw [show env.get (i₀ + m + m * B + i.val) + -1
          = env.get (i₀ + m + m * B + i.val) - 1 by ring]
        exact (IsBool.iff_mul_sub_one).mp hbit
      ·
        set Cn : ℕ → ℕ := fun k =>
          if k < m - 1 then (env.get (i₀ + m + m * B + k)).val else 0 with hCn
        have hCnP : ∀ k, k < m - 1 → Cn k = P k / 2 ^ (B * (k + 1)) := fun k hk => by
          simp only [hCn, if_pos hk]; exact hCn_eq k hk

        have hnat : ∀ k, k < m →
            An k + Dn k + (if k = 0 then 0 else Cn (k - 1)) + (if k = 0 then 1 else 0)
              = Bn k + Cn k * 2 ^ B := by
          intro k hk
          have hre : gfun k + (if k = 0 then 1 else P (k - 1) / 2 ^ (B * k))
              = (P k / 2 ^ (B * k)) % 2 ^ B + (P k / 2 ^ (B * (k + 1))) * 2 ^ B := ripple_eq B gfun k

          have hlimb : (P k / 2 ^ (B * k)) % 2 ^ B = Bn k := by
            have h1 : P (m - 1) / 2 ^ (B * k) % 2 ^ B = P k / 2 ^ (B * k) % 2 ^ B :=
              limb_stable B gfun k (m - 1) (by omega)
            rw [hBn_eq k hk, ← hPlast, ← h1]

          have hco : P k / 2 ^ (B * (k + 1)) = Cn k := by
            rcases Nat.lt_or_ge k (m - 1) with hk1 | hk1
            · exact (hCnP k hk1).symm
            · have hkm : k = m - 1 := by omega
              subst hkm
              simp only [hCn]
              rw [if_neg (lt_irrefl _), show m - 1 + 1 = m from by omega, hPlast]
              exact Nat.div_eq_of_lt hvb_lt
          rw [hlimb, hco] at hre
          simp only [hgfun] at hre

          rcases Nat.eq_zero_or_pos k with hk0 | hk0
          · subst hk0
            simp only [↓reduceIte] at hre ⊢
            omega
          · rw [if_neg (by omega : ¬ k = 0), if_neg (by omega : ¬ k = 0)]
            have hcin : P (k - 1) / 2 ^ (B * k) = Cn (k - 1) := by
              rw [hCnP (k - 1) (by omega), show k - 1 + 1 = k from by omega]
            rw [if_neg (by omega : ¬ k = 0), hcin] at hre
            omega

        intro i
        have hk := i.isLt
        have hnatk := hnat i.val hk

        have ha_e : Expression.eval env.toEnvironment input_var.lhs[i.val] = input.lhs[i.val]'hk := by
          rw [← h_input]; simp [Vector.getElem_map]
        have hb_e : Expression.eval env.toEnvironment input_var.rhs[i.val] = input.rhs[i.val]'hk := by
          rw [← h_input]; simp [Vector.getElem_map]
        have hcin_e : Expression.eval env.toEnvironment
            (if h : i.val = 0 then 0 else var { index := i₀ + m + m * B + (i.val - 1) })
            = if i.val = 0 then 0 else env.get (i₀ + m + m * B + (i.val - 1)) := by
          split <;> simp [circuit_norm]
        have hone_e : Expression.eval env.toEnvironment (if i.val = 0 then 1 else 0)
            = if i.val = 0 then (1 : F p) else 0 := by split <;> simp [circuit_norm]
        have hcout_e : Expression.eval env.toEnvironment
            (if h : i.val < m - 1 then var { index := i₀ + m + m * B + i.val } else 0)
            = if i.val < m - 1 then env.get (i₀ + m + m * B + i.val) else 0 := by
          split <;> simp [circuit_norm]
        rw [ha_e, hb_e, hcin_e, hone_e, hcout_e]

        have hAk : ((An i.val : ℕ) : F p) = (input.lhs[i.val]'hk) := by
          simp only [hAn, dif_pos hk]; rw [ZMod.natCast_zmod_val]
        have hDk : ((Dn i.val : ℕ) : F p) = env.get (i₀ + i.val) := by
          simp only [hDn, dif_pos hk]; rw [ZMod.natCast_zmod_val]
        have hBk : ((Bn i.val : ℕ) : F p) = (input.rhs[i.val]'hk) := by
          simp only [hBn, dif_pos hk]; rw [ZMod.natCast_zmod_val]
        have hCk : ((Cn i.val : ℕ) : F p)
            = (if i.val < m - 1 then env.get (i₀ + m + m * B + i.val) else 0) := by
          simp only [hCn]
          split
          · rw [ZMod.natCast_zmod_val]
          · simp

        have hcast_eq : (input.lhs[i.val]'hk) + env.get (i₀ + i.val)
            + (if i.val = 0 then (0:F p) else env.get (i₀ + m + m * B + (i.val - 1)))
            + (if i.val = 0 then (1 : F p) else 0)
            = (input.rhs[i.val]'hk)
              + (if i.val < m - 1 then env.get (i₀ + m + m * B + i.val) else 0)
                * (2 ^ B : F p) := by
          have hcast := congrArg (Nat.cast : ℕ → F p) hnatk
          push_cast at hcast
          rw [hAk, hDk, hBk, hCk] at hcast

          rw [show ((if i.val = 0 then (0:F p) else env.get (i₀ + m + m * B + (i.val - 1))))
                = ((if i.val = 0 then (0:ℕ) else Cn (i.val - 1) : ℕ) : F p) by
              split
              · simp
              · simp only [hCn]; rw [if_pos (by omega), ZMod.natCast_zmod_val],
            show ((if i.val = 0 then (1:F p) else 0))
                = ((if i.val = 0 then (1:ℕ) else 0 : ℕ) : F p) by split <;> simp]
          push_cast
          convert hcast using 2
        rw [hcast_eq]; ring

theorem computableWitnesses (P : BigIntParams p m) [Fact (p > 2)] :
    (circuit P).ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition input env env')
    ((main P input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.provableWitness_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.witnessVector_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.forEach_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.assertZero_structuralComputableWitnesses_iff]
  and_intros
  · intro _ h_input
    have hlhs : evalValue P.B env input.lhs = evalValue P.B env' input.lhs := by
      have h_lhs : eval env input.lhs = eval env' input.lhs := by
        simpa [circuit_norm] using congrArg (fun x : Inputs m (F p) => x.lhs) h_input
      have h_vec :
          input.lhs.map (Expression.eval env.toEnvironment) =
            input.lhs.map (Expression.eval env'.toEnvironment) := by
        simpa [CircuitType.eval_expression_prover_to_verifier, CircuitType.eval_expression,
          ProvableType.eval, explicit_provable_type] using h_lhs
      simp [evalValue, h_vec]
    have hrhs : evalValue P.B env input.rhs = evalValue P.B env' input.rhs := by
      have h_rhs : eval env input.rhs = eval env' input.rhs := by
        simpa [circuit_norm] using congrArg (fun x : Inputs m (F p) => x.rhs) h_input
      have h_vec :
          input.rhs.map (Expression.eval env.toEnvironment) =
            input.rhs.map (Expression.eval env'.toEnvironment) := by
        simpa [CircuitType.eval_expression_prover_to_verifier, CircuitType.eval_expression,
          ProvableType.eval, explicit_provable_type] using h_rhs
      simp [evalValue, h_vec]
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_ofFn, hlhs, hrhs]
  · apply Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
    · intro k env env' hk h_agree _
      apply Vector.ext
      intro i hi
      rw [← ProvableType.getElem_eval_fields_prover (env := env) _ i hi,
        ← ProvableType.getElem_eval_fields_prover (env := env') _ i hi]
      simp only [Circuit.output, ProvableType.witness, ProvableType.varFromOffset_fields,
        Vector.getElem_mapRange, Expression.eval]
      exact h_agree (offset + i) (by
        have hk' : offset + m ≤ k := by
          simpa [ProvableType.witness, Circuit.localLength, size] using hk
        omega)
    · exact Normalize.computableWitnesses P
  · intro h_agree h_input
    ext i
    simp only [Vector.getElem_ofFn]
    apply congrArg (fun n : ℕ => (n : F p))
    apply congrArg (fun s => ((1 + s) / 2 ^ (P.B * (i + 1)) : ℕ))
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    have hjm : j < m := by omega
    simp only [dif_pos hjm]
    have hlhs :
        ZMod.val (Expression.eval env.toEnvironment input.lhs[j]) =
          ZMod.val (Expression.eval env'.toEnvironment input.lhs[j]) := by
      apply congrArg ZMod.val
      have h_lhs : eval env input.lhs = eval env' input.lhs := by
        simpa [circuit_norm] using congrArg (fun x : Inputs m (F p) => x.lhs) h_input
      have h : (eval env input.lhs)[j] = (eval env' input.lhs)[j] := by
        simpa only using congrArg (fun x : BigInt m (F p) => x[j]) h_lhs
      rw [← ProvableType.getElem_eval_fields_prover (env := env) input.lhs j hjm,
        ← ProvableType.getElem_eval_fields_prover (env := env') input.lhs j hjm] at h
      exact h
    have hd :
        ZMod.val
          (Expression.eval env.toEnvironment
            ((ProvableType.witness (α := BigInt m) fun env =>
                    Vector.ofFn fun k : Fin m =>
                      (((evalValue P.B env input.rhs - 1 - evalValue P.B env input.lhs) /
                        2 ^ (P.B * k.val) % 2 ^ P.B : ℕ) : F p)).output
                offset)[j]) =
        ZMod.val
          (Expression.eval env'.toEnvironment
            ((ProvableType.witness (α := BigInt m) fun env =>
                    Vector.ofFn fun k : Fin m =>
                      (((evalValue P.B env input.rhs - 1 - evalValue P.B env input.lhs) /
                        2 ^ (P.B * k.val) % 2 ^ P.B : ℕ) : F p)).output
                offset)[j]) := by
      apply congrArg ZMod.val
      rw [Circuit.output, ProvableType.witness]
      simp only [ProvableType.varFromOffset_fields, Vector.getElem_mapRange, Expression.eval]
      exact h_agree (offset + j) (by
        have hdlen :
            (ProvableType.witness (α := BigInt m) fun env =>
              (Vector.ofFn fun k : Fin m =>
                (((evalValue P.B env input.rhs - 1 - evalValue P.B env input.lhs) /
                  2 ^ (P.B * k.val) % 2 ^ P.B : ℕ) : F p))).localLength offset = m := by
          simp [ProvableType.witness, Circuit.localLength, Operations.localLength, size]
        omega)
    rw [hlhs, hd]
  · intro _
    trivial
  · intro _
    trivial

theorem computableWitness (P : BigIntParams p m) [Fact (p > 2)] : ∀ n input,
    ProverEnvironment.OnlyAccessedBelow n
      (fun env : ProverEnvironment (F p) => eval env input) →
    Circuit.ComputableWitnesses (main P input) n := by
  exact Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnesses_implies
    (computableWitnesses P)

end LessThan

end

end Solution.Secp256k1ScalarMulFixedBase

end DonorFile0_5

-- Adapted donor module: EqViaCarries
section DonorFile0_6

namespace Solution.Secp256k1ScalarMulFixedBase
open Solution.Secp256k1ScalarMulFixedBase.Limbs

section
variable {p : ℕ} [Fact p.Prime]
variable {m : ℕ} [NeZero m]

namespace EqViaCarries

@[reducible] def Coeffs (m : ℕ) : TypeMap := fields (2 * m - 1)

structure Inputs (m : ℕ) (F : Type) where
  lhs : Coeffs m F
  rhs : Coeffs m F
deriving ProvableStruct

def main (P : BigIntParams p m) [Fact (p > 2)] (input : Var (Inputs m) (F p)) :
    Circuit (F p) Unit := do
  let Pc := input.lhs
  let Sc := input.rhs

  let carry ← witnessVector (2 * m - 1) fun env =>
    Vector.ofFn fun k : Fin (2 * m - 1) =>

      ((carryOffset (m := m) P.B + evalPartial P.B env Pc k.val / 2 ^ (P.B * (k.val + 1))
          - evalPartial P.B env Sc k.val / 2 ^ (P.B * (k.val + 1)) : ℕ) : F p)

  Circuit.forEach carry (fun c => Gadgets.ToBits.rangeCheck P.W P.hW c)

  let constraints : Vector (Expression (F p)) (2 * m - 1) :=
    Vector.mapFinRange (2 * m - 1) fun k =>
      let carryIn : Expression (F p) :=
        if h : k.val = 0 then 0 else carry[k.val - 1]'(by omega) - (carryOffset (m := m) P.B : F p)
      Pc[k.val] + carryIn - Sc[k.val]
        - (carry[k.val] - (carryOffset (m := m) P.B : F p)) * (2 ^ P.B : F p)
  Circuit.forEach constraints assertZero

  if h : 2 * m - 1 = 0 then pure () else
    assertZero (carry[2 * m - 1 - 1]'(by omega) - (carryOffset (m := m) P.B : F p))

instance elaborated (P : BigIntParams p m) [Fact (p > 2)] :
    ElaboratedCircuit (F p) (Inputs m) unit (main P) where

  localLength _ := (2 * m - 1) * P.W + (2 * m - 1)
  localLength_eq := by
    intro input offset
    simp only [main, circuit_norm, Gadgets.ToBits.rangeCheck]
    split <;> simp +arith [circuit_norm]
  subcircuitsConsistent := by
    intro input offset
    simp +arith only [main, circuit_norm, Gadgets.ToBits.rangeCheck]
    split <;> simp +arith [circuit_norm]
  channelsLawful := by
    intro offset
    simp only [main, circuit_norm, Gadgets.ToBits.rangeCheck]
    split <;> simp +arith [circuit_norm]

def Assumptions (B : ℕ) (input : Inputs m (F p)) : Prop :=
  (∀ k : Fin (2 * m - 1), (input.lhs[k.val]).val < (m + 1) * 2 ^ (2 * B)) ∧
  (∀ k : Fin (2 * m - 1), (input.rhs[k.val]).val < (m + 1) * 2 ^ (2 * B))

def Spec (B : ℕ) (input : Inputs m (F p)) : Prop :=
  polyValue B input.lhs = polyValue B input.rhs

def circuit (P : BigIntParams p m) [Fact (p > 2)] : FormalAssertion (F p) (Inputs m) where
    main := main P
    Assumptions := Assumptions P.B
    Spec := Spec P.B
    soundness := by
      obtain ⟨B, W, hB, hW, hB1, hWB, hWp, hp⟩ := P
      circuit_proof_start
      simp only [circuit_norm, Gadgets.ToBits.rangeCheck] at h_holds ⊢
      obtain ⟨h_range, h_lin, h_top⟩ := h_holds
      refine ⟨?_, by split <;> simp [circuit_norm]⟩

      have hM : 0 < 2 * m - 1 := by have := Nat.pos_of_neZero m; omega
      set OFFn := carryOffset (m := m) B with hOFFn

      set Pn : ℕ → ℕ := fun k => if h : k < 2 * m - 1 then (input.lhs[k]'h).val else 0 with hPn
      set Sn : ℕ → ℕ := fun k => if h : k < 2 * m - 1 then (input.rhs[k]'h).val else 0 with hSn
      set Cn : ℕ → ℕ := fun k => (env.get (i₀ + k)).val with hCn

      have hCn_lt : ∀ k, k < 2 * m - 1 → Cn k < 2 ^ W := by
        intro k hk; simpa [hCn] using h_range ⟨k, hk⟩
      have hPn_lt : ∀ k, k < 2 * m - 1 → Pn k < (m + 1) * 2 ^ (2 * B) := by
        intro k hk; simp only [hPn, dif_pos hk]; exact h_assumptions.1 ⟨k, hk⟩
      have hSn_lt : ∀ k, k < 2 * m - 1 → Sn k < (m + 1) * 2 ^ (2 * B) := by
        intro k hk; simp only [hSn, dif_pos hk]; exact h_assumptions.2 ⟨k, hk⟩

      have hOFF_eq : OFFn = (m + 1) * 2 ^ (B + 1) := rfl
      have hOFFB_eq : OFFn * 2 ^ B = (m + 1) * 2 ^ (2 * B + 1) := by
        rw [hOFF_eq, Nat.mul_assoc, ← pow_add]; congr 2; ring

      have hpow_le : (m + 1) * 2 ^ (2 * B + 1) ≤ (m + 1) * 2 ^ (2 * B) * 3 := by
        rw [pow_succ]; nlinarith [Nat.two_pow_pos (2 * B)]
      have hOFF_le3 : OFFn ≤ (m + 1) * 2 ^ (2 * B) * 3 := by
        rw [hOFF_eq]
        have h1 : (m + 1) * 2 ^ (B + 1) ≤ (m + 1) * 2 ^ (2 * B + 1) := by
          apply Nat.mul_le_mul_left; apply Nat.pow_le_pow_right (by norm_num); omega
        omega
      have hOFFB_lt : OFFn * 2 ^ B < p := by rw [hOFFB_eq]; omega
      have hpB : 2 ^ B < p := by
        have : 2 ^ B ≤ 2 ^ W * 2 ^ B := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos W)
        omega
      have hOFFn_lt : OFFn < p := by omega
      have hOFFn_cast : (OFFn : F p).val = OFFn := ZMod.val_natCast_of_lt hOFFn_lt

      have hOFFn_le_W : OFFn ≤ 2 ^ W := by
        have : OFFn ≤ OFFn * 2 := Nat.le_mul_of_pos_right _ (by norm_num); omega
      have hXW : (m + 1) * 2 ^ (2 * B) ≤ 2 ^ W * 2 ^ B := by
        have h1 : (m + 1) * 2 ^ (B + 2) ≤ 2 ^ W := by
          have : OFFn * 2 = (m + 1) * 2 ^ (B + 2) := by rw [hOFF_eq, pow_succ]; ring
          omega
        calc (m + 1) * 2 ^ (2 * B) ≤ (m + 1) * 2 ^ (B + 2) * 2 ^ B := by
                rw [Nat.mul_assoc, ← pow_add]
                apply Nat.mul_le_mul_left
                apply Nat.pow_le_pow_right (by norm_num); omega
          _ ≤ 2 ^ W * 2 ^ B := Nat.mul_le_mul_right _ h1

      rw [dif_neg (by omega : ¬ (2 * m - 1 = 0))] at h_top
      simp only [circuit_norm] at h_top
      have hCtop : Cn (2 * m - 1 - 1) = OFFn := by
        have : env.get (i₀ + (2 * m - 1 - 1)) = (OFFn : F p) := by
          rw [← sub_eq_zero]; rw [show env.get (i₀ + (2 * m - 1 - 1)) - (OFFn : F p)
            = env.get (i₀ + (2 * m - 1 - 1)) + -(OFFn : F p) by ring]; exact h_top
        simp only [hCn, this, hOFFn_cast]

      have h_idx : ∀ k, (hk : k < 2 * m - 1) →
          Pn k + (if k = 0 then OFFn else Cn (k - 1)) + OFFn * 2 ^ B
            = Sn k + Cn k * 2 ^ B + OFFn := by
        intro k hk
        have hlin := h_lin ⟨k, hk⟩

        have ha_e : Expression.eval env input_var.lhs[(⟨k, hk⟩ : Fin (2*m-1)).val] = input.lhs[k]'hk := by
          rw [← h_input]; simp [Vector.getElem_map]
        have hb_e : Expression.eval env input_var.rhs[(⟨k, hk⟩ : Fin (2*m-1)).val] = input.rhs[k]'hk := by
          rw [← h_input]; simp [Vector.getElem_map]
        have hcin_e : Expression.eval env
            (if h : (⟨k, hk⟩ : Fin (2*m-1)).val = 0 then 0
              else var { index := i₀ + ((⟨k, hk⟩ : Fin (2*m-1)).val - 1) } - Expression.const (OFFn : F p))
            = if k = 0 then 0 else env.get (i₀ + (k - 1)) - (OFFn : F p) := by
          simp only []
          split <;> simp [circuit_norm, sub_eq_add_neg]
        simp only [ha_e, hb_e, hcin_e] at hlin

        have hfield : (input.lhs[k]'hk) + (if k = 0 then (OFFn : F p) else env.get (i₀ + (k - 1)))
            + (OFFn : F p) * (2 ^ B : F p)
            = (input.rhs[k]'hk) + env.get (i₀ + k) * (2 ^ B : F p) + (OFFn : F p) := by
          rcases Nat.eq_zero_or_pos k with hk0 | hk0
          · subst hk0
            simp only [↓reduceIte] at hlin ⊢
            rw [← sub_eq_zero]
            rw [← hlin]; ring
          · rw [if_neg (by omega : ¬ k = 0)] at hlin ⊢
            rw [← sub_eq_zero]
            rw [← hlin]; ring

        have hcin_val : (if k = 0 then (OFFn : F p) else env.get (i₀ + (k - 1))).val
            = if k = 0 then OFFn else Cn (k - 1) := by
          split
          · exact hOFFn_cast
          · simp [hCn]
        have hcinN_lt : (if k = 0 then OFFn else Cn (k - 1)) < p := by
          split
          · exact hOFFn_lt
          · rename_i hkne
            have := hCn_lt (k - 1) (by omega); omega
        have hcin_le : (if k = 0 then OFFn else Cn (k - 1)) ≤ 2 ^ W := by
          split
          · exact hOFFn_le_W
          · rename_i hkne; have := hCn_lt (k - 1) (by omega); omega
        have hlhs : (input.lhs[k]'hk).val + (if k = 0 then OFFn else Cn (k - 1)) + OFFn * 2 ^ B < p := by
          have hp1 := hPn_lt k hk
          simp only [hPn, dif_pos hk] at hp1
          omega
        have hrhs : (input.rhs[k]'hk).val + (env.get (i₀ + k)).val * 2 ^ B + OFFn < p := by
          have hp2 := hSn_lt k hk
          simp only [hSn, dif_pos hk] at hp2
          have hc : (env.get (i₀ + k)).val < 2 ^ W := h_range ⟨k, hk⟩
          have hcB : (env.get (i₀ + k)).val * 2 ^ B ≤ 2 ^ W * 2 ^ B := by
            apply Nat.mul_le_mul_right; omega
          omega
        have hlift := per_index_lift (B := B) (input.lhs[k]'hk)
          (if k = 0 then (OFFn : F p) else env.get (i₀ + (k - 1)))
          (input.rhs[k]'hk) (env.get (i₀ + k)) (OFFn : F p)
          (if k = 0 then OFFn else Cn (k - 1)) OFFn hpB hcin_val hOFFn_cast hlhs hrhs hfield
        simp only [hPn, hSn, hCn, dif_pos hk] at hlift ⊢
        convert hlift using 2

      have hpv1 : polyValue B input.lhs = ∑ k ∈ Finset.range (2 * m - 1), Pn k * 2 ^ (B * k) := by
        rw [polyValue, ← Fin.sum_univ_eq_sum_range (fun k => Pn k * 2 ^ (B * k))]
        apply Finset.sum_congr rfl
        intro i _; simp only [hPn, dif_pos i.isLt]
      have hpv2 : polyValue B input.rhs = ∑ k ∈ Finset.range (2 * m - 1), Sn k * 2 ^ (B * k) := by
        rw [polyValue, ← Fin.sum_univ_eq_sum_range (fun k => Sn k * 2 ^ (B * k))]
        apply Finset.sum_congr rfl
        intro i _; simp only [hSn, dif_pos i.isLt]
      rw [hpv1, hpv2]

      have hsum : (∑ k ∈ Finset.range (2 * m - 1),
            ((Pn k + (if k = 0 then OFFn else Cn (k - 1))) + OFFn * 2 ^ B) * 2 ^ (B * k))
          = ∑ k ∈ Finset.range (2 * m - 1),
            (Sn k + Cn k * 2 ^ B + OFFn) * 2 ^ (B * k) := by
        apply Finset.sum_congr rfl
        intro k hk; rw [Finset.mem_range] at hk; rw [h_idx k hk]

      set SP := ∑ k ∈ Finset.range (2 * m - 1), Pn k * 2 ^ (B * k) with hSP
      set SS := ∑ k ∈ Finset.range (2 * m - 1), Sn k * 2 ^ (B * k) with hSS
      set SC := ∑ k ∈ Finset.range (2 * m - 1), Cn k * 2 ^ (B * (k + 1)) with hSC

      set SCin' := ∑ k ∈ Finset.range (2 * m - 1),
        (if k = 0 then OFFn else Cn (k - 1)) * 2 ^ (B * k) with hSCin'

      set SCin := ∑ k ∈ Finset.range (2 * m - 1),
        (if k = 0 then 0 else Cn (k - 1)) * 2 ^ (B * k) with hSCin
      set G := ∑ k ∈ Finset.range (2 * m - 1), 2 ^ (B * k) with hG

      have hSCin_rel : SCin' = SCin + OFFn := by
        rw [hSCin', hSCin, show 2 * m - 1 = (2 * m - 2) + 1 from by omega]
        rw [Finset.sum_range_succ' _ (2 * m - 2), Finset.sum_range_succ' _ (2 * m - 2)]
        simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte,
          Nat.mul_zero, pow_zero, Nat.mul_one]
        ring

      have hLHS : (∑ k ∈ Finset.range (2 * m - 1),
            ((Pn k + (if k = 0 then OFFn else Cn (k - 1))) + OFFn * 2 ^ B) * 2 ^ (B * k))
          = SP + SCin' + OFFn * 2 ^ B * G := by
        rw [hSP, hSCin', hG, Finset.mul_sum,
          ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _; ring

      have hRHS : (∑ k ∈ Finset.range (2 * m - 1), (Sn k + Cn k * 2 ^ B + OFFn) * 2 ^ (B * k))
          = SS + SC + OFFn * G := by
        rw [hSS, hSC, hG, Finset.mul_sum,
          ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _
        rw [Nat.mul_add, Nat.mul_one, pow_add]; ring
      rw [hLHS, hRHS] at hsum

      have htel := carry_telescope B Cn (2 * m - 1)
      rw [if_neg (by omega : ¬ (2 * m - 1 = 0)), hCtop] at htel
      rw [← hSCin, ← hSC] at htel

      have hgeo := geom_shift B (2 * m - 1)
      rw [← hG] at hgeo
      set Gtop := 2 ^ (B * (2 * m - 1)) with hGtop
      have hGtop_pos : 1 ≤ Gtop := Nat.one_le_two_pow
      have hG_pos : 1 ≤ G := by
        rw [hG]
        calc 1 = 2 ^ (B * 0) := by simp
          _ ≤ _ := Finset.single_le_sum (f := fun k => 2 ^ (B * k))
              (by intro i _; positivity) (Finset.mem_range.mpr hM)
      have hgeo' : 2 ^ B * G + 1 = G + Gtop := by omega
      have hoff_geo : OFFn * (2 ^ B * G) + OFFn = OFFn * G + OFFn * Gtop := by
        have hc := congrArg (OFFn * ·) hgeo'
        simp only [Nat.mul_add, Nat.mul_one] at hc
        omega
      have hsum' : SP + SCin' + OFFn * (2 ^ B * G) = SS + SC + OFFn * G := by
        rw [← Nat.mul_assoc]; exact hsum
      omega
    completeness := by
      obtain ⟨B, W, hB, hW, hB1, hWB, hWp, hp⟩ := P
      circuit_proof_start
      simp only [circuit_norm, Gadgets.ToBits.rangeCheck] at h_env ⊢
      obtain ⟨h_wit, _, _⟩ := h_env
      have hM : 0 < 2 * m - 1 := by have := Nat.pos_of_neZero m; omega
      set OFFn := carryOffset (m := m) B with hOFFn
      have hOFF_eq : OFFn = (m + 1) * 2 ^ (B + 1) := rfl

      set Pn : ℕ → ℕ := fun k => if h : k < 2 * m - 1 then (input.lhs[k]'h).val else 0 with hPn
      set Sn : ℕ → ℕ := fun k => if h : k < 2 * m - 1 then (input.rhs[k]'h).val else 0 with hSn
      have hPn_lt : ∀ k, Pn k < (m + 1) * 2 ^ (2 * B) := by
        intro k; simp only [hPn]; split
        · rename_i h; exact h_assumptions.1 ⟨k, h⟩
        · positivity
      have hSn_lt : ∀ k, Sn k < (m + 1) * 2 ^ (2 * B) := by
        intro k; simp only [hSn]; split
        · rename_i h; exact h_assumptions.2 ⟨k, h⟩
        · positivity

      set PFn : ℕ → ℕ := fun k => ∑ j ∈ Finset.range (k + 1), Pn j * 2 ^ (B * j) with hPFn
      set PSn : ℕ → ℕ := fun k => ∑ j ∈ Finset.range (k + 1), Sn j * 2 ^ (B * j) with hPSn

      have hPFn_eq : ∀ k, evalPartial B env input_var.lhs k = PFn k := by
        intro k; simp only [evalPartial, hPFn]
        apply Finset.sum_congr rfl
        intro j _; congr 1
        simp only [hPn]; split
        · rename_i h; rw [← h_input]; simp [Vector.getElem_map]
        · rfl
      have hPSn_eq : ∀ k, evalPartial B env input_var.rhs k = PSn k := by
        intro k; simp only [evalPartial, hPSn]
        apply Finset.sum_congr rfl
        intro j _; congr 1
        simp only [hSn]; split
        · rename_i h; rw [← h_input]; simp [Vector.getElem_map]
        · rfl

      set Dk : ℕ → ℕ := fun k => 2 ^ (B * (k + 1)) with hDk
      set Cn : ℕ → ℕ := fun k => OFFn + PFn k / Dk k - PSn k / Dk k with hCn

      have hDk_app : ∀ k, Dk k = 2 ^ (B * (k + 1)) := fun k => rfl
      have hPFn_app : ∀ k, PFn k = ∑ j ∈ Finset.range (k + 1), Pn j * 2 ^ (B * j) := fun k => rfl
      have hPSn_app : ∀ k, PSn k = ∑ j ∈ Finset.range (k + 1), Sn j * 2 ^ (B * j) := fun k => rfl
      have hCn_app : ∀ k, Cn k = OFFn + PFn k / Dk k - PSn k / Dk k := fun k => rfl

      have hwit_eq : ∀ k, k < 2 * m - 1 → env.get (i₀ + k) = (Cn k : F p) := by
        intro k hk
        rw [h_wit ⟨k, hk⟩]
        simp only [Vector.getElem_ofFn, hCn_app, hDk_app, hPFn_eq, hPSn_eq]

      have hPFdiv : ∀ k, PFn k / Dk k ≤ OFFn := by
        intro k; rw [hOFF_eq]; exact partial_div_bound B m hB1 Pn hPn_lt k
      have hPSdiv : ∀ k, PSn k / Dk k ≤ OFFn := by
        intro k; rw [hOFF_eq]; exact partial_div_bound B m hB1 Sn hSn_lt k

      have hrange : ∀ k, Cn k < 2 ^ W := by
        intro k
        have h1 := hPFdiv k
        rw [hCn_app]
        calc OFFn + PFn k / Dk k - PSn k / Dk k ≤ OFFn + PFn k / Dk k := Nat.sub_le _ _
          _ ≤ OFFn + OFFn := by omega
          _ < 2 ^ W := by have := hWB; omega

      have hpB : 2 ^ B < p := by
        have hle : 2 ^ B ≤ 2 ^ W * 2 ^ B := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos W)
        omega
      have hOFFn_lt : OFFn < p := by
        have : OFFn ≤ OFFn * 2 := Nat.le_mul_of_pos_right _ (by norm_num); omega
      have hOFFn_cast : (OFFn : F p).val = OFFn := ZMod.val_natCast_of_lt hOFFn_lt

      have hPFn_top : PFn (2 * m - 2) = polyValue B input.lhs := by
        rw [hPFn_app, polyValue, ← Fin.sum_univ_eq_sum_range (fun j => Pn j * 2 ^ (B * j)),
          show 2 * m - 2 + 1 = 2 * m - 1 from by omega]
        apply Finset.sum_congr rfl (fun i _ => ?_)
        simp only [hPn, dif_pos i.isLt]
      have hPSn_top : PSn (2 * m - 2) = polyValue B input.rhs := by
        rw [hPSn_app, polyValue, ← Fin.sum_univ_eq_sum_range (fun j => Sn j * 2 ^ (B * j)),
          show 2 * m - 2 + 1 = 2 * m - 1 from by omega]
        apply Finset.sum_congr rfl (fun i _ => ?_)
        simp only [hSn, dif_pos i.isLt]
      have hPtop_eq : PFn (2 * m - 2) = PSn (2 * m - 2) := by
        rw [hPFn_top, hPSn_top]; exact h_spec
      have hmod : ∀ k, k < 2 * m - 1 → PFn k % Dk k = PSn k % Dk k := by
        intro k hk
        have e1 : PFn (2 * m - 2) % Dk k = PFn k % Dk k := by
          rw [hPFn_app, hPFn_app, hDk_app, show 2 * m - 2 + 1 = 2 * m - 1 from by omega]
          exact partial_mod_stable B Pn (2 * m - 1) k hk
        have e2 : PSn (2 * m - 2) % Dk k = PSn k % Dk k := by
          rw [hPSn_app, hPSn_app, hDk_app, show 2 * m - 2 + 1 = 2 * m - 1 from by omega]
          exact partial_mod_stable B Sn (2 * m - 1) k hk
        rw [← e1, ← e2, hPtop_eq]

      have hCtop : Cn (2 * m - 2) = OFFn := by
        rw [hCn_app, hPtop_eq]; omega
      have hidx : ∀ k, k < 2 * m - 1 →
          Pn k + (if k = 0 then OFFn else Cn (k - 1)) + OFFn * 2 ^ B
            = Sn k + Cn k * 2 ^ B + OFFn := by
        intro k hk

        set qP := PFn k / 2 ^ (B * k) with hqP_def
        set qS := PSn k / 2 ^ (B * k) with hqS_def
        set rP := PFn k / Dk k with hrP_def
        set rS := PSn k / Dk k with hrS_def

        have hrP_quot : rP = qP / 2 ^ B := by
          rw [hrP_def, hqP_def, hDk_app, show B * (k + 1) = B * k + B by ring, pow_add,
            Nat.div_div_eq_div_mul]
        have hrS_quot : rS = qS / 2 ^ B := by
          rw [hrS_def, hqS_def, hDk_app, show B * (k + 1) = B * k + B by ring, pow_add,
            Nat.div_div_eq_div_mul]

        have hsplitP : qP = rP * 2 ^ B + qP % 2 ^ B := by
          rw [hrP_quot]; exact (Nat.div_add_mod' qP (2 ^ B)).symm
        have hsplitS : qS = rS * 2 ^ B + qS % 2 ^ B := by
          rw [hrS_quot]; exact (Nat.div_add_mod' qS (2 ^ B)).symm

        have hdig : qP % 2 ^ B = qS % 2 ^ B := by
          have hP : qP % 2 ^ B = PFn k % Dk k / 2 ^ (B * k) := by
            rw [hqP_def, hDk_app, show B * (k + 1) = B * k + B by ring, pow_add,
              Nat.mod_mul_right_div_self]
          have hS : qS % 2 ^ B = PSn k % Dk k / 2 ^ (B * k) := by
            rw [hqS_def, hDk_app, show B * (k + 1) = B * k + B by ring, pow_add,
              Nat.mod_mul_right_div_self]
          rw [hP, hS, hmod k hk]

        have hstepP : qP = Pn k + (if k = 0 then 0
            else (∑ j ∈ Finset.range k, Pn j * 2 ^ (B * j)) / 2 ^ (B * k)) := by
          rw [hqP_def, hPFn_app]; exact quot_step B Pn k
        have hstepS : qS = Sn k + (if k = 0 then 0
            else (∑ j ∈ Finset.range k, Sn j * 2 ^ (B * j)) / 2 ^ (B * k)) := by
          rw [hqS_def, hPSn_app]; exact quot_step B Sn k

        have hCnk : Cn k = OFFn + rP - rS := by rw [hCn_app, ← hrP_def, ← hrS_def]
        have hrS_le : rS ≤ OFFn := by rw [hrS_def]; exact hPSdiv k

        rw [hdig] at hsplitP

        clear_value qP qS rP rS

        have hmulCnk : Cn k * 2 ^ B = OFFn * 2 ^ B + rP * 2 ^ B - rS * 2 ^ B := by
          rw [hCnk, Nat.sub_mul, Nat.add_mul]
        rcases Nat.eq_zero_or_pos k with hk0 | hk0
        · subst hk0
          rw [hmulCnk]
          simp only [↓reduceIte] at hstepP hstepS ⊢
          rw [Nat.add_zero] at hstepP hstepS

          have hrPmul : rS * 2 ^ B ≤ rP * 2 ^ B + OFFn * 2 ^ B := by
            have : rS ≤ rP + OFFn := by omega
            calc rS * 2 ^ B ≤ (rP + OFFn) * 2 ^ B := Nat.mul_le_mul_right _ this
              _ = rP * 2 ^ B + OFFn * 2 ^ B := by rw [Nat.add_mul]
          omega
        · rw [if_neg (by omega : ¬ k = 0), hmulCnk]

          have hPFnprev : (∑ j ∈ Finset.range k, Pn j * 2 ^ (B * j)) = PFn (k - 1) := by
            rw [hPFn_app, show k - 1 + 1 = k from by omega]
          have hPSnprev : (∑ j ∈ Finset.range k, Sn j * 2 ^ (B * j)) = PSn (k - 1) := by
            rw [hPSn_app, show k - 1 + 1 = k from by omega]
          rw [if_neg (by omega : ¬ k = 0), hPFnprev] at hstepP
          rw [if_neg (by omega : ¬ k = 0), hPSnprev] at hstepS

          set rP' := PFn (k - 1) / Dk (k - 1) with hrP'_def
          set rS' := PSn (k - 1) / Dk (k - 1) with hrS'_def
          have hprevP : PFn (k - 1) / 2 ^ (B * k) = rP' := by
            rw [hrP'_def, hDk_app, show k - 1 + 1 = k from by omega]
          have hprevS : PSn (k - 1) / 2 ^ (B * k) = rS' := by
            rw [hrS'_def, hDk_app, show k - 1 + 1 = k from by omega]
          rw [hprevP] at hstepP
          rw [hprevS] at hstepS
          have hCnprev : Cn (k - 1) = OFFn + rP' - rS' := hCn_app (k - 1)
          have hrSprev_le : rS' ≤ OFFn := hPSdiv (k - 1)
          rw [hCnprev]
          clear_value rP' rS'
          have hrPmul : rS * 2 ^ B ≤ rP * 2 ^ B + OFFn * 2 ^ B := by
            have : rS ≤ rP + OFFn := by omega
            calc rS * 2 ^ B ≤ (rP + OFFn) * 2 ^ B := Nat.mul_le_mul_right _ this
              _ = rP * 2 ^ B + OFFn * 2 ^ B := by rw [Nat.add_mul]
          omega

      have hCn_val : ∀ k, k < 2 * m - 1 → (env.get (i₀ + k)).val = Cn k := by
        intro k hk
        rw [hwit_eq k hk, ZMod.val_natCast_of_lt (lt_of_lt_of_le (hrange k) (le_of_lt hW))]
      refine ⟨?_, ?_, ?_⟩
      ·
        intro i
        rw [hCn_val i.val i.isLt]; exact hrange i.val
      ·
        intro i
        have hk := i.isLt
        have hnatk := hidx i.val hk

        have ha_e : Expression.eval env.toEnvironment input_var.lhs[i.val] = input.lhs[i.val]'hk := by
          rw [← h_input]; simp [Vector.getElem_map]
        have hb_e : Expression.eval env.toEnvironment input_var.rhs[i.val] = input.rhs[i.val]'hk := by
          rw [← h_input]; simp [Vector.getElem_map]
        have hcin_e : Expression.eval env.toEnvironment
            (if h : i.val = 0 then 0 else var { index := i₀ + (i.val - 1) } - Expression.const (OFFn : F p))
            = if i.val = 0 then 0 else env.get (i₀ + (i.val - 1)) - (OFFn : F p) := by
          split <;> simp [circuit_norm, sub_eq_add_neg]
        rw [ha_e, hb_e, hcin_e]

        have hAk : ((Pn i.val : ℕ) : F p) = (input.lhs[i.val]'hk) := by
          simp only [hPn, dif_pos hk]; rw [ZMod.natCast_zmod_val]
        have hBk : ((Sn i.val : ℕ) : F p) = (input.rhs[i.val]'hk) := by
          simp only [hSn, dif_pos hk]; rw [ZMod.natCast_zmod_val]
        have hCk : ((Cn i.val : ℕ) : F p) = env.get (i₀ + i.val) := by
          rw [hwit_eq i.val hk]
        have hOFFcast : ((OFFn : ℕ) : F p) = (OFFn : F p) := rfl
        have hpow_cast : ((2 ^ B : ℕ) : F p) = (2 ^ B : F p) := by push_cast; ring

        have hcast := congrArg (Nat.cast : ℕ → F p) hnatk
        push_cast [hpow_cast] at hcast
        rw [hAk, hBk, hCk] at hcast
        rcases Nat.eq_zero_or_pos i.val with hi0 | hi0
        · simp only [hi0, ↓reduceIte, add_zero] at hcast ⊢
          rw [← sub_eq_zero] at hcast
          rw [← hcast]; ring
        · simp only [if_neg (by omega : ¬ i.val = 0)] at hcast ⊢
          have hCkprev : ((Cn (i.val - 1) : ℕ) : F p) = env.get (i₀ + (i.val - 1)) := by
            rw [hwit_eq (i.val - 1) (by omega)]
          rw [hCkprev, ← sub_eq_zero] at hcast
          rw [← hcast]; ring
      ·
        rw [dif_neg (by omega : ¬ (2 * m - 1 = 0))]
        simp only [circuit_norm]
        have : env.get (i₀ + (2 * m - 1 - 1)) = (OFFn : F p) := by
          rw [show 2 * m - 1 - 1 = 2 * m - 2 from by omega, hwit_eq (2 * m - 2) (by omega), hCtop]
        rw [this]; ring

end EqViaCarries

end

end Solution.Secp256k1ScalarMulFixedBase

end DonorFile0_6

-- Adapted donor module: MulMod
section DonorFile0_7

namespace Solution.Secp256k1ScalarMulFixedBase
open Solution.Secp256k1ScalarMulFixedBase.Limbs

section
variable {p : ℕ} [Fact p.Prime]
variable {m : ℕ} [NeZero m]

namespace MulMod

structure Inputs (m : ℕ) (F : Type) where
  a : BigInt m F
  b : BigInt m F
  modulus : BigInt m F
deriving ProvableStruct

private def evalValue (B : ℕ) (env : ProverEnvironment (F p))
    (x : Var (BigInt m) (F p)) : ℕ :=
  Solution.Secp256k1ScalarMulFixedBase.Limbs.fromLimbs B ((x.map (Expression.eval env.toEnvironment)).toList.map ZMod.val)

def witnessedMul (a b : Var (BigInt m) (F p)) :
    Circuit (F p) (Vector (Expression (F p)) (2 * m - 1)) := do

  let pp ← ProvableType.witness (α := fields (m * m)) fun env =>
    Vector.ofFn fun t : Fin (m * m) =>
      (Expression.eval env.toEnvironment (a[t.val / m]'(Nat.div_lt_of_lt_mul t.isLt)))
        * (Expression.eval env.toEnvironment (b[t.val % m]'(Nat.mod_lt _ (Nat.pos_of_neZero m))))

  let constraints : Vector (Expression (F p)) (m * m) :=
    Vector.mapFinRange (m * m) fun t =>
      (a[t.val / m]'(Nat.div_lt_of_lt_mul t.isLt))
        * (b[t.val % m]'(Nat.mod_lt _ (Nat.pos_of_neZero m)))
        - pp[t.val]
  Circuit.forEach constraints assertZero
  return bigIntMulVars pp

lemma witnessedMul_output (off : ℕ) (a b : Var (BigInt m) (F p)) :
    (witnessedMul a b off).1
      = bigIntMulVars (Vector.mapRange (m * m) fun i => var (F := F p) { index := off + i }) := by
  simp only [witnessedMul, circuit_norm]

lemma witnessedMul_soundness (off : ℕ) (a b : Var (BigInt m) (F p)) (env : Environment (F p))
    (h : Operations.forAllNoOffset
        { assert := fun e => Expression.eval env e = 0, lookup := fun l => l.Soundness env,
          interact := fun i => i.Guarantees env, subcircuit := fun {_n} s => s.Assumptions env → s.Spec env }
        (witnessedMul a b off).2) :
    ∀ t : Fin (m * m),
      Expression.eval env (a[t.val / m]'(Nat.div_lt_of_lt_mul t.isLt))
          * Expression.eval env (b[t.val % m]'(Nat.mod_lt _ (Nat.pos_of_neZero m)))
        = env.get (off + t.val) := by
  simp only [witnessedMul, circuit_norm] at h
  intro t; have := h t; rw [add_neg_eq_zero] at this; exact this

lemma witnessedMul_eval_bridge (env : Environment (F p)) (off : ℕ) (a b : Var (BigInt m) (F p))
    (h_prod : ∀ t : Fin (m * m),
      Expression.eval env (a[t.val / m]'(Nat.div_lt_of_lt_mul t.isLt))
          * Expression.eval env (b[t.val % m]'(Nat.mod_lt _ (Nat.pos_of_neZero m)))
        = env.get (off + t.val)) :
    ∀ k : Fin (2 * m - 1),
      Expression.eval env (witnessedMul a b off).1[k.val]
        = Expression.eval env (bigIntMulNoReduce a b)[k.val] := by
  intro k
  rw [witnessedMul_output off a b]
  have hvec := witnessedMul_map_eval env off a b h_prod
  have := congrArg (fun v => v[k.val]) hvec
  simpa only [Vector.getElem_map] using this

lemma witnessedMul_requirements (off : ℕ) (a b : Var (BigInt m) (F p)) (env : Environment (F p)) :
    Operations.forAllNoOffset
      { interact := fun i => i.Requirements env,
        subcircuit := fun {_n} s => s.channelsWithRequirements = [] ∨ s.Assumptions env }
      (witnessedMul a b off).2 := by
  simp only [witnessedMul, circuit_norm]

lemma witnessedMul_usesLocalWitnesses (off off' : ℕ) (a b : Var (BigInt m) (F p))
    (penv : ProverEnvironment (F p)) (heq : off' = off)
    (h : penv.UsesLocalWitnessesCompleteness off' (witnessedMul a b off).2) :
    ∀ t : Fin (m * m), penv.toEnvironment.get (off + t.val)
        = Expression.eval penv.toEnvironment (a[t.val / m]'(Nat.div_lt_of_lt_mul t.isLt))
            * Expression.eval penv.toEnvironment (b[t.val % m]'(Nat.mod_lt _ (Nat.pos_of_neZero m))) := by
  subst heq
  simp only [witnessedMul, circuit_norm] at h
  intro t
  have := h t
  simpa only [Vector.getElem_ofFn] using this

lemma witnessedMul_completeness (off : ℕ) (a b : Var (BigInt m) (F p)) (penv : ProverEnvironment (F p))
    (h : ∀ t : Fin (m * m), penv.toEnvironment.get (off + t.val)
        = Expression.eval penv.toEnvironment (a[t.val / m]'(Nat.div_lt_of_lt_mul t.isLt))
            * Expression.eval penv.toEnvironment (b[t.val % m]'(Nat.mod_lt _ (Nat.pos_of_neZero m)))) :
    Operations.forAllNoOffset
      { assert := fun e => Expression.eval penv.toEnvironment e = 0,
        lookup := fun l => l.Completeness penv.toEnvironment,
        interact := fun i => i.Guarantees penv.toEnvironment, subcircuit := fun {_n} s => s.ProverAssumptions penv }
      (witnessedMul a b off).2 := by
  simp only [witnessedMul, circuit_norm]
  intro t; rw [h t]; ring

def main (P : BigIntParams p m) [Fact (p > 2)]
    (input : Var (Inputs m) (F p)) :
    Circuit (F p) (Var (BigInt m) (F p)) := do
  let a := input.a
  let b := input.b
  let n := input.modulus

  let q ← ProvableType.witness (α := BigInt m) fun env =>
    let prod := evalValue P.B env a * evalValue P.B env b
    let qval : ℕ := prod / evalValue P.B env n
    Vector.ofFn fun k : Fin m => ((qval / 2 ^ (P.B * k.val) % 2 ^ P.B : ℕ) : F p)
  let r ← ProvableType.witness (α := BigInt m) fun env =>
    let prod := evalValue P.B env a * evalValue P.B env b
    let rval : ℕ := prod % evalValue P.B env n
    Vector.ofFn fun k : Fin m => ((rval / 2 ^ (P.B * k.val) % 2 ^ P.B : ℕ) : F p)

  Normalize.circuit P q
  Normalize.circuit P r

  let Pc ← witnessedMul a b
  let Sqn ← witnessedMul q n
  let S : Vector (Expression (F p)) (2 * m - 1) := Vector.mapFinRange (2 * m - 1) fun k =>
    if h : k.val < m then Sqn[k.val] + r[k.val]'h else Sqn[k.val]

  EqViaCarries.circuit P { lhs := Pc, rhs := S }

  LessThan.circuit P { lhs := r, rhs := n }

  return r

instance elaborated (P : BigIntParams p m) [Fact (p > 2)] :
    ElaboratedCircuit (F p) (Inputs m) (BigInt m) (main P) where

  localLength _ :=
    m + m + m * P.B + m * P.B + (m * m) + (m * m)
      + ((2 * m - 1) * P.W + (2 * m - 1)) + (m + m * P.B + (m - 1))
  output _ i0 := varFromOffset (BigInt m) (i0 + m)
  localLength_eq := by
    intro input offset
    simp only [main, witnessedMul, circuit_norm, Normalize.circuit, Normalize.elaborated,
      Normalize.main, EqViaCarries.circuit, EqViaCarries.elaborated, EqViaCarries.main,
      LessThan.circuit, LessThan.elaborated, LessThan.main, Gadgets.ToBits.rangeCheck]
    omega
  output_eq := by
    intro input offset
    simp only [main, witnessedMul, circuit_norm, Normalize.circuit, Normalize.elaborated,
      Normalize.main, EqViaCarries.circuit, EqViaCarries.elaborated, EqViaCarries.main,
      LessThan.circuit, LessThan.elaborated, LessThan.main, Gadgets.ToBits.rangeCheck]
  subcircuitsConsistent := by
    intro input offset
    simp +arith only [main, witnessedMul, circuit_norm, Normalize.circuit, Normalize.elaborated,
      Normalize.main, EqViaCarries.circuit, EqViaCarries.elaborated, EqViaCarries.main,
      LessThan.circuit, LessThan.elaborated, LessThan.main, Gadgets.ToBits.rangeCheck]
  channelsLawful := by
    intro input offset
    simp only [main, witnessedMul, circuit_norm, Normalize.circuit, Normalize.elaborated,
      Normalize.main, EqViaCarries.circuit, EqViaCarries.elaborated, EqViaCarries.main,
      LessThan.circuit, LessThan.elaborated, LessThan.main, Gadgets.ToBits.rangeCheck]

def Assumptions (B : ℕ) (input : Inputs m (F p)) : Prop :=
  let a := input.a
  let b := input.b
  let n := input.modulus
  a.Normalized B ∧ b.Normalized B ∧ n.Normalized B ∧
    a.value B < n.value B ∧ b.value B < n.value B ∧ 0 < n.value B

def Spec (B : ℕ) (input : Inputs m (F p)) (out : BigInt m (F p)) : Prop :=
  let a := input.a
  let b := input.b
  let n := input.modulus
  out.Normalized B ∧ out.value B = (a.value B * b.value B) % n.value B

def circuit (P : BigIntParams p m) [Fact (p > 2)] :
    FormalCircuit (F p) (Inputs m) (BigInt m) where
    main := main P
    Assumptions := Assumptions P.B
    Spec := Spec P.B
    soundness := by
      obtain ⟨B, W, hB, hW, hB1, hWB, hWp, hp⟩ := P
      circuit_proof_start [Normalize.circuit, Normalize.elaborated, Normalize.main,
        Normalize.Assumptions, Normalize.Spec,
        EqViaCarries.circuit, EqViaCarries.elaborated, EqViaCarries.main,
        EqViaCarries.Assumptions, EqViaCarries.Spec,
        LessThan.circuit, LessThan.elaborated, LessThan.main,
        LessThan.Assumptions, LessThan.Spec]
      obtain ⟨ha_norm, hb_norm, hn_norm, hab_lt, hbb_lt, hn_pos⟩ := h_assumptions
      obtain ⟨hq_norm, hr_norm, hAB_ops, hQN_ops, h_eq_impl, h_lt_impl⟩ := h_holds

      have h_pAB := witnessedMul_soundness (i₀ + m + m + m * B + m * B) input_var.a input_var.b env hAB_ops
      have h_pQN := witnessedMul_soundness
        (i₀ + m + m + m * B + m * B + Operations.localLength
          (witnessedMul input_var.a input_var.b (i₀ + m + m + m * B + m * B)).2)
        (Vector.mapRange m fun i => var { index := i₀ + i }) input_var.modulus env hQN_ops
      refine ⟨?_, witnessedMul_requirements _ _ _ _, witnessedMul_requirements _ _ _ _⟩
      have h_input' : (Vector.map (Expression.eval env) input_var.a,
          Vector.map (Expression.eval env) input_var.b,
          Vector.map (Expression.eval env) input_var.modulus)
            = ((input.a, input.b, input.modulus) :
              ProvablePair (BigInt m) (ProvablePair (BigInt m) (BigInt m)) (F p)) := by
        simp only [← h_input]
      have heqAB_get := witnessedMul_eval_bridge env (i₀ + m + m + m * B + m * B)
        input_var.a input_var.b h_pAB
      have heqQN_get := witnessedMul_eval_bridge env
        (i₀ + m + m + m * B + m * B + Operations.localLength
          (witnessedMul input_var.a input_var.b (i₀ + m + m + m * B + m * B)).2)
        (Vector.mapRange m fun i => var { index := i₀ + i }) input_var.modulus h_pQN
      exact mulMod_soundness_core_wm (B := B) hp i₀ env
        input_var.a input_var.b input_var.modulus
        (witnessedMul input_var.a input_var.b (i₀ + m + m + m * B + m * B)).1
        (witnessedMul (Vector.mapRange m fun i => var { index := i₀ + i }) input_var.modulus
          (i₀ + m + m + m * B + m * B + Operations.localLength
            (witnessedMul input_var.a input_var.b (i₀ + m + m + m * B + m * B)).2)).1
        (input.a, input.b, input.modulus) h_input' ha_norm hb_norm hn_norm hq_norm hr_norm
        heqAB_get heqQN_get h_eq_impl h_lt_impl
    completeness := by
      obtain ⟨B, W, hB, hW, hB1, hWB, hWp, hp⟩ := P
      circuit_proof_start [Normalize.circuit, Normalize.elaborated, Normalize.main,
        Normalize.Assumptions, Normalize.Spec,
        EqViaCarries.circuit, EqViaCarries.elaborated, EqViaCarries.main,
        EqViaCarries.Assumptions, EqViaCarries.Spec,
        LessThan.circuit, LessThan.elaborated, LessThan.main,
        LessThan.Assumptions, LessThan.Spec]
      obtain ⟨ha_norm, hb_norm, hn_norm, hab_lt, hbb_lt, hn_pos⟩ := h_assumptions
      obtain ⟨hq_env, hr_env, hAB_uses, hQN_uses⟩ := h_env
      have h_pvAB := witnessedMul_usesLocalWitnesses (i₀ + m + m + m * B + m * B)
        (i₀ + m + m + m * B + m * B) input_var.a input_var.b env rfl hAB_uses
      have h_pvQN := witnessedMul_usesLocalWitnesses
        (i₀ + m + m + m * B + m * B + Operations.localLength
          (witnessedMul input_var.a input_var.b (i₀ + m + m + m * B + m * B)).2)
        (Operations.localLength (witnessedMul input_var.a input_var.b (i₀ + m + m + m * B + m * B)).2
          + (i₀ + m + m + m * B + m * B))
        (Vector.mapRange m fun i => var { index := i₀ + i }) input_var.modulus env
        (Nat.add_comm _ _) hQN_uses
      have h_pAB : ∀ t : Fin (m * m),
          Expression.eval env.toEnvironment (input_var.a[t.val / m]'(Nat.div_lt_of_lt_mul t.isLt))
              * Expression.eval env.toEnvironment (input_var.b[t.val % m]'(Nat.mod_lt _ (Nat.pos_of_neZero m)))
            = env.toEnvironment.get ((i₀ + m + m + m * B + m * B) + t.val) :=
        fun t => (h_pvAB t).symm
      have h_pQN : ∀ t : Fin (m * m),
          Expression.eval env.toEnvironment
              ((Vector.mapRange m fun i => var { index := i₀ + i })[t.val / m]'(Nat.div_lt_of_lt_mul t.isLt))
              * Expression.eval env.toEnvironment (input_var.modulus[t.val % m]'(Nat.mod_lt _ (Nat.pos_of_neZero m)))
            = env.toEnvironment.get ((i₀ + m + m + m * B + m * B + Operations.localLength
                (witnessedMul input_var.a input_var.b (i₀ + m + m + m * B + m * B)).2) + t.val) :=
        fun t => (h_pvQN t).symm
      have heva : evalValue B env input_var.a = BigInt.value B input.a := by
        rw [evalValue, BigInt.value, ← h_input]
      have hevb : evalValue B env input_var.b = BigInt.value B input.b := by
        rw [evalValue, BigInt.value, ← h_input]
      have hevn : evalValue B env input_var.modulus = BigInt.value B input.modulus := by
        rw [evalValue, BigInt.value, ← h_input]
      have hqwit : ∀ i : Fin m, env.toEnvironment.get (i₀ + i.val)
          = ((BigInt.value B input.a * BigInt.value B input.b / BigInt.value B input.modulus
              / 2 ^ (B * i.val) % 2 ^ B : ℕ) : F p) := by
        intro i; rw [hq_env i, Vector.getElem_ofFn, heva, hevb, hevn]
      have hrwit : ∀ i : Fin m, env.toEnvironment.get (i₀ + m + i.val)
          = ((BigInt.value B input.a * BigInt.value B input.b % BigInt.value B input.modulus
              / 2 ^ (B * i.val) % 2 ^ B : ℕ) : F p) := by
        intro i; rw [hr_env i, Vector.getElem_ofFn, heva, hevb, hevn]
      have h_input' : (Vector.map (Expression.eval env.toEnvironment) input_var.a,
          Vector.map (Expression.eval env.toEnvironment) input_var.b,
          Vector.map (Expression.eval env.toEnvironment) input_var.modulus)
            = ((input.a, input.b, input.modulus) :
              ProvablePair (BigInt m) (ProvablePair (BigInt m) (BigInt m)) (F p)) := by
        simp only [← h_input]
      have heqAB_get := witnessedMul_eval_bridge env.toEnvironment (i₀ + m + m + m * B + m * B)
        input_var.a input_var.b h_pAB
      have heqQN_get := witnessedMul_eval_bridge env.toEnvironment
        (i₀ + m + m + m * B + m * B + Operations.localLength
          (witnessedMul input_var.a input_var.b (i₀ + m + m + m * B + m * B)).2)
        (Vector.mapRange m fun i => var { index := i₀ + i }) input_var.modulus h_pQN
      have core := mulMod_completeness_core_wm (B := B) hB hp i₀ env.toEnvironment
        input_var.a input_var.b input_var.modulus
        (witnessedMul input_var.a input_var.b (i₀ + m + m + m * B + m * B)).1
        (witnessedMul (Vector.mapRange m fun i => var { index := i₀ + i }) input_var.modulus
          (i₀ + m + m + m * B + m * B + Operations.localLength
            (witnessedMul input_var.a input_var.b (i₀ + m + m + m * B + m * B)).2)).1
        (input.a, input.b, input.modulus) h_input' ha_norm hb_norm hn_norm hab_lt hbb_lt hn_pos
        hqwit hrwit heqAB_get heqQN_get

      exact ⟨core.1, core.2.1,
        witnessedMul_completeness (i₀ + m + m + m * B + m * B) input_var.a input_var.b env h_pvAB,
        witnessedMul_completeness _ (Vector.mapRange m fun i => var { index := i₀ + i })
          input_var.modulus env h_pvQN,
        core.2.2⟩

end MulMod

end

end Solution.Secp256k1ScalarMulFixedBase

end DonorFile0_7

-- Adapted donor module: Params
section DonorFile0_8

namespace Solution.Secp256k1ScalarMulFixedBase

@[reducible] def circomPrime : ℕ :=
  Challenge.Instances.Secp256k1ScalarMul.Interface.circomPrime

-- Keep legacy donor I/O declarations available, but field algebra in this
-- variable-base port must use the variable-base verifier's permitted proof.
instance (priority := 2000) : Fact (circomPrime.Prime) :=
  ⟨Challenge.Instances.Secp256k1ScalarMul.Interface.hCircomPrime⟩

instance : Fact (circomPrime > 2) := ⟨by decide⟩

@[reducible] def P256 : ℕ := Specs.Secp256k1.p

@[reducible] def numLimbs : ℕ := 4

@[reducible] def limbBits : ℕ := 64

@[reducible] def bytesPerLimb : ℕ := 8

@[reducible] def coordBytes : ℕ := 32

@[reducible] def Emu : TypeMap := BigInt numLimbs

def secpParams : BigIntParams circomPrime numLimbs where
  B := limbBits
  W := 69
  hB := by decide
  hW := by decide
  hB1 := by decide
  hWB := by decide
  hWp := by decide
  hp := by decide

def limbOfNat (v k : ℕ) : ℕ := v / 2 ^ (limbBits * k) % 2 ^ limbBits

def emuOfNat (v : ℕ) : Emu (F circomPrime) :=
  Vector.ofFn fun k : Fin numLimbs => ((limbOfNat v k.val : ℕ) : F circomPrime)

def emuConst (v : ℕ) : Var Emu (F circomPrime) :=
  Vector.ofFn fun k : Fin numLimbs =>
    (((limbOfNat v k.val : ℕ) : F circomPrime) : Expression (F circomPrime))

def pConst : Var Emu (F circomPrime) := emuConst P256

def zeroConst : Var Emu (F circomPrime) := emuConst 0

def oneConst : Var Emu (F circomPrime) := emuConst 1

def evalEmu (env : ProverEnvironment (F circomPrime))
    (x : Var Emu (F circomPrime)) : ℕ :=
  Limbs.fromLimbs limbBits
    ((x.map (Expression.eval env.toEnvironment)).toList.map ZMod.val)

theorem evalEmu_eq_of_eval_eq {env env' : ProverEnvironment (F circomPrime)}
    {x : Var Emu (F circomPrime)}
    (h : eval env x = eval env' x) :
    evalEmu env x = evalEmu env' x := by
  have hmap :
      x.map (Expression.eval env.toEnvironment) =
        x.map (Expression.eval env'.toEnvironment) := by
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_map]
    have h_i : (eval env x)[i] = (eval env' x)[i] := by
      simpa only using congrArg (fun y : Emu (F circomPrime) => y[i]) h
    rw [← ProvableType.getElem_eval_fields_prover (env := env) x i hi,
      ← ProvableType.getElem_eval_fields_prover (env := env') x i hi] at h_i
    exact h_i
  simp [evalEmu, hmap]

theorem emu_map_eval_eq_of_eval_eq {env env' : ProverEnvironment (F circomPrime)}
    {x : Var Emu (F circomPrime)}
    (h : eval env x = eval env' x) :
    x.map (Expression.eval env.toEnvironment) =
      x.map (Expression.eval env'.toEnvironment) := by
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_map]
  have h_i : (eval env x)[i] = (eval env' x)[i] := by
    simpa only using congrArg (fun y : Emu (F circomPrime) => y[i]) h
  rw [← ProvableType.getElem_eval_fields_prover (env := env) x i hi,
    ← ProvableType.getElem_eval_fields_prover (env := env') x i hi] at h_i
  exact h_i

theorem eval_mem_of_map_eval_eq {m : ℕ} {env env' : ProverEnvironment (F circomPrime)}
    {x : Vector (Expression (F circomPrime)) m}
    (h : x.map (Expression.eval env.toEnvironment) =
      x.map (Expression.eval env'.toEnvironment)) :
    ∀ a ∈ x, Expression.eval env.toEnvironment a = Expression.eval env'.toEnvironment a := by
  intro a ha
  simp only [Vector.mem_iff_getElem] at ha
  rcases ha with ⟨i, hi, rfl⟩
  simpa only [Vector.getElem_map] using congrArg (fun y : Vector (F circomPrime) m => y[i]) h

def decodeFe (x : Emu (F circomPrime)) : Specs.Secp256k1.Fp :=
  ((x.value limbBits : ℕ) : Specs.Secp256k1.Fp)

def Fe.Valid (x : Emu (F circomPrime)) : Prop :=
  x.Normalized limbBits ∧ x.value limbBits < P256

structure FlaggedPoint (F : Type) where
  x : Emu F
  y : Emu F
  isInf : F
deriving ProvableStruct

def decodePoint (P : FlaggedPoint (F circomPrime)) :
    Specs.ShortWeierstrass.GroupPoint Specs.Secp256k1.Fp :=
  if P.isInf = 1 then .infinity
  else .affine { x := decodeFe P.x, y := decodeFe P.y }

def FlaggedPoint.Valid (P : FlaggedPoint (F circomPrime)) : Prop :=
  IsBool P.isInf ∧ Fe.Valid P.x ∧ Fe.Valid P.y ∧
    (P.isInf = 0 →
      Specs.ShortWeierstrass.OnCurve Specs.Secp256k1.curve
        { x := decodeFe P.x, y := decodeFe P.y })

end Solution.Secp256k1ScalarMulFixedBase

end DonorFile0_8

-- Adapted donor module: AddModTheorems
section DonorFile0_9

namespace Solution.Secp256k1ScalarMulFixedBase
open Solution.Secp256k1ScalarMulFixedBase.Limbs

lemma P256_pos : 0 < P256 := by decide

lemma P256_lt : P256 < 2 ^ (limbBits * numLimbs) := by decide

lemma two_pow_limb_lt : 2 ^ limbBits < circomPrime := by decide

lemma limb_add_lt : 2 ^ limbBits + 2 ^ limbBits < circomPrime := by decide

lemma limb_add_le_bound :
    2 ^ limbBits + 2 ^ limbBits ≤ (numLimbs + 1) * 2 ^ (2 * limbBits) := by decide

lemma limbOfNat_lt (v k : ℕ) : limbOfNat v k < 2 ^ limbBits :=
  Nat.mod_lt _ (Nat.two_pow_pos limbBits)

lemma val_limbOfNat (v k : ℕ) :
    ((limbOfNat v k : ℕ) : F circomPrime).val = limbOfNat v k :=
  ZMod.val_natCast_of_lt (lt_trans (limbOfNat_lt v k) two_pow_limb_lt)

lemma emuOfNat_getElem (v k : ℕ) (hk : k < numLimbs) :
    (emuOfNat v)[k]'hk = ((limbOfNat v k : ℕ) : F circomPrime) := by
  simp only [emuOfNat, Vector.getElem_ofFn]

lemma emuOfNat_normalized (v : ℕ) : (emuOfNat v).Normalized limbBits := by
  intro i
  rw [Fin.getElem_fin, emuOfNat_getElem v i.val i.isLt, val_limbOfNat]
  exact limbOfNat_lt v i.val

lemma value_emuOfNat {v : ℕ} (hv : v < 2 ^ (limbBits * numLimbs)) :
    BigInt.value limbBits (emuOfNat v) = v := by
  rw [BigInt.value_eq_sum]
  have hsum : (∑ k : Fin numLimbs, ((emuOfNat v)[k]).val * 2 ^ (limbBits * k.val))
      = ∑ k ∈ Finset.range numLimbs,
          (v / 2 ^ (limbBits * k) % 2 ^ limbBits) * 2 ^ (limbBits * k) := by
    rw [← Fin.sum_univ_eq_sum_range
      (fun k => (v / 2 ^ (limbBits * k) % 2 ^ limbBits) * 2 ^ (limbBits * k))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fin.getElem_fin, emuOfNat_getElem v i.val i.isLt, val_limbOfNat]
    rfl
  rw [hsum, limb_decomp_mod, Nat.mod_eq_of_lt hv]

lemma limb_sum_P256 :
    (∑ k ∈ Finset.range numLimbs, limbOfNat P256 k * 2 ^ (limbBits * k)) = P256 := by
  have h : (∑ k ∈ Finset.range numLimbs, limbOfNat P256 k * 2 ^ (limbBits * k))
      = ∑ k ∈ Finset.range numLimbs,
          (P256 / 2 ^ (limbBits * k) % 2 ^ limbBits) * 2 ^ (limbBits * k) :=
    Finset.sum_congr rfl fun k _ => rfl
  rw [h, limb_decomp_mod, Nat.mod_eq_of_lt P256_lt]

lemma eval_pConst_getElem (env : Environment (F circomPrime)) (k : ℕ) (hk : k < numLimbs) :
    Expression.eval env (pConst[k]'hk) = ((limbOfNat P256 k : ℕ) : F circomPrime) :=
  congrArg (Expression.eval env) (Vector.getElem_ofFn ..)

lemma eval_pConst (env : Environment (F circomPrime)) :
    Vector.map (Expression.eval env) pConst = emuOfNat P256 := by
  apply Vector.ext
  intro k hk
  rw [Vector.getElem_map, eval_pConst_getElem env k hk, emuOfNat_getElem P256 k hk]

lemma pConst_normalized (env : Environment (F circomPrime)) :
    BigInt.Normalized limbBits (Vector.map (Expression.eval env) pConst) := by
  rw [eval_pConst]
  exact emuOfNat_normalized P256

lemma pConst_value (env : Environment (F circomPrime)) :
    BigInt.value limbBits (Vector.map (Expression.eval env) pConst) = P256 := by
  rw [eval_pConst]
  exact value_emuOfNat P256_lt

lemma eval_outVar_getElem (env : Environment (F circomPrime)) (i₀ k : ℕ) (hk : k < numLimbs) :
    (Vector.map (Expression.eval env)
        (Vector.mapRange numLimbs fun i => var (F := F circomPrime) { index := i₀ + i }))[k]'hk
      = env.get (i₀ + k) := by
  simp [circuit_norm]

lemma outVar_val_lt (env : Environment (F circomPrime)) (i₀ : ℕ)
    (h : BigInt.Normalized limbBits (Vector.map (Expression.eval env)
      (Vector.mapRange numLimbs fun i => var { index := i₀ + i }))) :
    ∀ k : ℕ, k < numLimbs → (env.get (i₀ + k)).val < 2 ^ limbBits := by
  intro k hk
  have hval := h ⟨k, hk⟩
  rwa [Fin.getElem_fin, eval_outVar_getElem env i₀ k hk] at hval

lemma value_outVar (B : ℕ) (env : Environment (F circomPrime)) (i₀ : ℕ) :
    BigInt.value B (Vector.map (Expression.eval env)
        (Vector.mapRange numLimbs fun i => var { index := i₀ + i }))
      = ∑ k ∈ Finset.range numLimbs, (env.get (i₀ + k)).val * 2 ^ (B * k) := by
  rw [BigInt.value_eq_sum,
    ← Fin.sum_univ_eq_sum_range (fun k => (env.get (i₀ + k)).val * 2 ^ (B * k))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fin.getElem_fin, eval_outVar_getElem env i₀ i.val i.isLt]

lemma value_eq_range_sum (B : ℕ) (x : Emu (F circomPrime)) :
    BigInt.value B x
      = ∑ k ∈ Finset.range numLimbs,
          (if h : k < numLimbs then (x[k]'h).val else 0) * 2 ^ (B * k) := by
  rw [BigInt.value_eq_sum,
    ← Fin.sum_univ_eq_sum_range
      (fun k => (if h : k < numLimbs then (x[k]'h).val else 0) * 2 ^ (B * k))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dif_pos i.isLt, Fin.getElem_fin]

lemma polyValue_padded (B : ℕ) (env : Environment (F circomPrime))
    (f : (k : Fin (2 * numLimbs - 1)) → k.val < numLimbs → Expression (F circomPrime))
    (c : ℕ → ℕ)
    (hval : ∀ (k : Fin (2 * numLimbs - 1)) (h : k.val < numLimbs),
      (Expression.eval env (f k h)).val = c k.val) :
    polyValue B (Vector.map (Expression.eval env)
        (Vector.mapFinRange (2 * numLimbs - 1) fun k =>
          if h : k.val < numLimbs then f k h else 0))
      = ∑ k ∈ Finset.range numLimbs, c k * 2 ^ (B * k) := by
  have hterm : ∀ k : Fin (2 * numLimbs - 1),
      ((Vector.map (Expression.eval env)
        (Vector.mapFinRange (2 * numLimbs - 1) fun k =>
          if h : k.val < numLimbs then f k h else 0))[k.val]).val * 2 ^ (B * k.val)
      = (if k.val < numLimbs then c k.val else 0) * 2 ^ (B * k.val) := by
    intro k
    rw [Vector.getElem_map, Vector.getElem_mapFinRange]
    by_cases hk : k.val < numLimbs
    · rw [dif_pos hk, if_pos hk, hval ⟨k.val, k.isLt⟩ hk]
    · rw [dif_neg hk, if_neg hk]
      norm_num [circuit_norm]
  rw [polyValue, Finset.sum_congr rfl (fun k _ => hterm k),
    Fin.sum_univ_eq_sum_range (fun k => (if k < numLimbs then c k else 0) * 2 ^ (B * k))]
  rw [← Finset.sum_subset (Finset.range_subset_range.mpr (by decide : numLimbs ≤ 2 * numLimbs - 1))
    (f := fun k => (if k < numLimbs then c k else 0) * 2 ^ (B * k))]
  · exact Finset.sum_congr rfl fun k hk => by rw [if_pos (Finset.mem_range.mp hk)]
  · intro k _ hk
    rw [Finset.mem_range] at hk
    rw [if_neg hk, Nat.zero_mul]

lemma val_add_limb {u v : F circomPrime}
    (hu : u.val < 2 ^ limbBits) (hv : v.val < 2 ^ limbBits) :
    (u + v).val = u.val + v.val :=
  ZMod.val_add_of_lt (by have := limb_add_lt; omega)

lemma bound_add_limb {u v : F circomPrime}
    (hu : u.val < 2 ^ limbBits) (hv : v.val < 2 ^ limbBits) :
    (u + v).val < (numLimbs + 1) * 2 ^ (2 * limbBits) := by
  have h := ZMod.val_add_le u v
  have := limb_add_le_bound
  omega

lemma val_q_mul_limb {qN : ℕ} (hqN : qN ≤ 1) (k : ℕ) :
    (((qN : ℕ) : F circomPrime) * ((limbOfNat P256 k : ℕ) : F circomPrime)).val
      = qN * limbOfNat P256 k := by
  have hq_lt : qN < circomPrime := by
    have := two_pow_limb_lt
    have := Nat.two_pow_pos limbBits
    omega
  rw [ZMod.val_mul_of_lt, ZMod.val_natCast_of_lt hq_lt, val_limbOfNat]
  rw [ZMod.val_natCast_of_lt hq_lt, val_limbOfNat]
  have h1 := limbOfNat_lt P256 k
  have h2 : qN * limbOfNat P256 k ≤ 1 * limbOfNat P256 k :=
    Nat.mul_le_mul_right _ hqN
  have := two_pow_limb_lt
  omega

namespace AddMod

lemma lhs_bounds (env : Environment (F circomPrime))
    (a_var b_var : Var Emu (F circomPrime)) (a b : Emu (F circomPrime))
    (h_input_a : Vector.map (Expression.eval env) a_var = a)
    (h_input_b : Vector.map (Expression.eval env) b_var = b)
    (ha_norm : a.Normalized limbBits) (hb_norm : b.Normalized limbBits) :
    ∀ k : Fin (2 * numLimbs - 1),
      (Expression.eval env
          (if h : k.val < numLimbs then a_var[k.val]'h + b_var[k.val]'h else 0)).val
        < (numLimbs + 1) * 2 ^ (2 * limbBits) := by
  intro k
  by_cases hk : k.val < numLimbs
  · rw [dif_pos hk,
      show Expression.eval env (a_var[k.val]'hk + b_var[k.val]'hk)
        = Expression.eval env (a_var[k.val]'hk) + Expression.eval env (b_var[k.val]'hk) from rfl,
      show Expression.eval env (a_var[k.val]'hk) = a[k.val]'hk from by
        rw [← h_input_a, Vector.getElem_map],
      show Expression.eval env (b_var[k.val]'hk) = b[k.val]'hk from by
        rw [← h_input_b, Vector.getElem_map]]
    exact bound_add_limb (ha_norm ⟨k.val, hk⟩) (hb_norm ⟨k.val, hk⟩)
  · rw [dif_neg hk, show Expression.eval env (0 : Expression (F circomPrime)) = 0 from rfl,
      ZMod.val_zero]
    positivity

lemma rhs_bounds (env : Environment (F circomPrime)) (i₀ : ℕ) (qN : ℕ)
    (hq : env.get (i₀ + numLimbs) = ((qN : ℕ) : F circomPrime)) (hqN : qN ≤ 1)
    (hr : ∀ k : ℕ, k < numLimbs → (env.get (i₀ + k)).val < 2 ^ limbBits) :
    ∀ k : Fin (2 * numLimbs - 1),
      (Expression.eval env
          (if h : k.val < numLimbs
            then var { index := i₀ + numLimbs } * pConst[k.val]'h + var { index := i₀ + k.val }
            else 0)).val
        < (numLimbs + 1) * 2 ^ (2 * limbBits) := by
  intro k
  by_cases hk : k.val < numLimbs
  · rw [dif_pos hk,
      show Expression.eval env
            (var { index := i₀ + numLimbs } * pConst[k.val]'hk + var { index := i₀ + k.val })
          = env.get (i₀ + numLimbs) * Expression.eval env (pConst[k.val]'hk)
            + env.get (i₀ + k.val) from rfl,
      hq, eval_pConst_getElem env k.val hk]
    have h1 := ZMod.val_add_le
      (((qN : ℕ) : F circomPrime) * ((limbOfNat P256 k.val : ℕ) : F circomPrime))
      (env.get (i₀ + k.val))
    rw [val_q_mul_limb hqN k.val] at h1
    have h2 := limbOfNat_lt P256 k.val
    have h3 : qN * limbOfNat P256 k.val ≤ 1 * limbOfNat P256 k.val :=
      Nat.mul_le_mul_right _ hqN
    have h4 := hr k.val hk
    have := limb_add_le_bound
    omega
  · rw [dif_neg hk, show Expression.eval env (0 : Expression (F circomPrime)) = 0 from rfl,
      ZMod.val_zero]
    positivity

lemma polyValue_lhs (env : Environment (F circomPrime))
    (a_var b_var : Var Emu (F circomPrime)) (a b : Emu (F circomPrime))
    (h_input_a : Vector.map (Expression.eval env) a_var = a)
    (h_input_b : Vector.map (Expression.eval env) b_var = b)
    (ha_norm : a.Normalized limbBits) (hb_norm : b.Normalized limbBits) :
    polyValue limbBits (Vector.map (Expression.eval env)
        (Vector.mapFinRange (2 * numLimbs - 1) fun k =>
          if h : k.val < numLimbs then a_var[k.val]'h + b_var[k.val]'h else 0))
      = BigInt.value limbBits a + BigInt.value limbBits b := by
  refine (polyValue_padded limbBits env
      (fun k h => a_var[k.val]'h + b_var[k.val]'h)
      (fun k => (if h : k < numLimbs then (a[k]'h).val else 0)
        + (if h : k < numLimbs then (b[k]'h).val else 0)) ?_).trans ?_
  · intro k hk
    rw [show Expression.eval env (a_var[k.val]'hk + b_var[k.val]'hk)
        = Expression.eval env (a_var[k.val]'hk) + Expression.eval env (b_var[k.val]'hk) from rfl,
      show Expression.eval env (a_var[k.val]'hk) = a[k.val]'hk from by
        rw [← h_input_a, Vector.getElem_map],
      show Expression.eval env (b_var[k.val]'hk) = b[k.val]'hk from by
        rw [← h_input_b, Vector.getElem_map],
      val_add_limb (u := a[k.val]'hk) (v := b[k.val]'hk)
        (ha_norm ⟨k.val, hk⟩) (hb_norm ⟨k.val, hk⟩)]
    simp only [dif_pos hk]
  · rw [value_eq_range_sum limbBits a, value_eq_range_sum limbBits b,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => add_mul _ _ _

lemma polyValue_rhs (env : Environment (F circomPrime)) (i₀ : ℕ) (qN : ℕ)
    (hq : env.get (i₀ + numLimbs) = ((qN : ℕ) : F circomPrime)) (hqN : qN ≤ 1)
    (hr : ∀ k : ℕ, k < numLimbs → (env.get (i₀ + k)).val < 2 ^ limbBits) :
    polyValue limbBits (Vector.map (Expression.eval env)
        (Vector.mapFinRange (2 * numLimbs - 1) fun k =>
          if h : k.val < numLimbs
          then var { index := i₀ + numLimbs } * pConst[k.val]'h + var { index := i₀ + k.val }
          else 0))
      = qN * P256 + BigInt.value limbBits (Vector.map (Expression.eval env)
          (Vector.mapRange numLimbs fun i => var { index := i₀ + i })) := by
  refine (polyValue_padded limbBits env
      (fun k h => var { index := i₀ + numLimbs } * pConst[k.val]'h + var { index := i₀ + k.val })
      (fun k => qN * limbOfNat P256 k + (env.get (i₀ + k)).val) ?_).trans ?_
  · intro k hk
    rw [show Expression.eval env
          (var { index := i₀ + numLimbs } * pConst[k.val]'hk + var { index := i₀ + k.val })
        = env.get (i₀ + numLimbs) * Expression.eval env (pConst[k.val]'hk)
          + env.get (i₀ + k.val) from rfl,
      hq, eval_pConst_getElem env k.val hk,
      ZMod.val_add_of_lt, val_q_mul_limb hqN k.val]

    rw [val_q_mul_limb hqN k.val]
    have h2 := limbOfNat_lt P256 k.val
    have h3 : qN * limbOfNat P256 k.val ≤ 1 * limbOfNat P256 k.val :=
      Nat.mul_le_mul_right _ hqN
    have h4 := hr k.val hk
    have := limb_add_lt
    omega
  · rw [value_outVar limbBits env i₀]
    have hsplit : (∑ k ∈ Finset.range numLimbs,
          (qN * limbOfNat P256 k + (env.get (i₀ + k)).val) * 2 ^ (limbBits * k))
        = (∑ k ∈ Finset.range numLimbs, qN * (limbOfNat P256 k * 2 ^ (limbBits * k)))
          + ∑ k ∈ Finset.range numLimbs, (env.get (i₀ + k)).val * 2 ^ (limbBits * k) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hsplit, ← Finset.mul_sum, limb_sum_P256]

lemma soundness_core (i₀ : ℕ) (env : Environment (F circomPrime))
    (a_var b_var : Var Emu (F circomPrime)) (a b : Emu (F circomPrime))
    (h_input_a : Vector.map (Expression.eval env) a_var = a)
    (h_input_b : Vector.map (Expression.eval env) b_var = b)
    (ha : Fe.Valid a) (hb : Fe.Valid b)
    (hq_bool : env.get (i₀ + numLimbs) * (env.get (i₀ + numLimbs) + -1) = 0)
    (hr_norm : BigInt.Normalized limbBits (Vector.map (Expression.eval env)
        (Vector.mapRange numLimbs fun i => var { index := i₀ + i })))
    (h_lt_impl :
      BigInt.Normalized limbBits (Vector.map (Expression.eval env)
          (Vector.mapRange numLimbs fun i => var { index := i₀ + i })) ∧
        BigInt.Normalized limbBits (Vector.map (Expression.eval env) pConst) →
        BigInt.value limbBits (Vector.map (Expression.eval env)
            (Vector.mapRange numLimbs fun i => var { index := i₀ + i })) <
          BigInt.value limbBits (Vector.map (Expression.eval env) pConst))
    (h_eq_impl :
      ((∀ k : Fin (2 * numLimbs - 1),
          (Expression.eval env
              (if h : k.val < numLimbs then a_var[k.val]'h + b_var[k.val]'h else 0)).val
            < (numLimbs + 1) * 2 ^ (2 * limbBits)) ∧
        ∀ k : Fin (2 * numLimbs - 1),
          (Expression.eval env
              (if h : k.val < numLimbs
                then var { index := i₀ + numLimbs } * pConst[k.val]'h + var { index := i₀ + k.val }
                else 0)).val
            < (numLimbs + 1) * 2 ^ (2 * limbBits)) →
        polyValue limbBits (Vector.map (Expression.eval env)
            (Vector.mapFinRange (2 * numLimbs - 1) fun k =>
              if h : k.val < numLimbs then a_var[k.val]'h + b_var[k.val]'h else 0)) =
          polyValue limbBits (Vector.map (Expression.eval env)
            (Vector.mapFinRange (2 * numLimbs - 1) fun k =>
              if h : k.val < numLimbs
              then var { index := i₀ + numLimbs } * pConst[k.val]'h + var { index := i₀ + k.val }
              else 0))) :
    Fe.Valid (Vector.map (Expression.eval env)
        (Vector.mapRange numLimbs fun i => var { index := i₀ + i })) ∧
      decodeFe (Vector.map (Expression.eval env)
          (Vector.mapRange numLimbs fun i => var { index := i₀ + i }))
        = decodeFe a + decodeFe b := by
  obtain ⟨ha_norm, ha_lt⟩ := ha
  obtain ⟨hb_norm, hb_lt⟩ := hb

  have hq01 : (env.get (i₀ + numLimbs)).val ≤ 1 := by
    rcases mul_eq_zero.mp hq_bool with h | h
    · rw [h, ZMod.val_zero]
      omega
    · rw [add_neg_eq_zero] at h
      rw [h, ZMod.val_one]
  have hq_cast : env.get (i₀ + numLimbs)
      = (((env.get (i₀ + numLimbs)).val : ℕ) : F circomPrime) :=
    (ZMod.natCast_zmod_val _).symm

  have h_polyeq := h_eq_impl
    ⟨lhs_bounds env a_var b_var a b h_input_a h_input_b ha_norm hb_norm,
      rhs_bounds env i₀ _ hq_cast hq01 (outVar_val_lt env i₀ hr_norm)⟩
  rw [polyValue_lhs env a_var b_var a b h_input_a h_input_b ha_norm hb_norm,
    polyValue_rhs env i₀ _ hq_cast hq01 (outVar_val_lt env i₀ hr_norm)] at h_polyeq

  have hr_lt : BigInt.value limbBits (Vector.map (Expression.eval env)
      (Vector.mapRange numLimbs fun i => var { index := i₀ + i })) < P256 := by
    have h := h_lt_impl ⟨hr_norm, pConst_normalized env⟩
    rwa [pConst_value env] at h
  refine ⟨⟨hr_norm, hr_lt⟩, ?_⟩

  have hcast := congrArg (Nat.cast : ℕ → Specs.Secp256k1.Fp) h_polyeq
  push_cast at hcast
  rw [show ((P256 : ℕ) : Specs.Secp256k1.Fp) = 0 from ZMod.natCast_self _,
    mul_zero, zero_add] at hcast
  simp only [decodeFe]
  exact hcast.symm

lemma completeness_core (i₀ : ℕ) (env : Environment (F circomPrime))
    (a_var b_var : Var Emu (F circomPrime)) (a b : Emu (F circomPrime))
    (h_input_a : Vector.map (Expression.eval env) a_var = a)
    (h_input_b : Vector.map (Expression.eval env) b_var = b)
    (ha : Fe.Valid a) (hb : Fe.Valid b)
    (h_wit_r : ∀ i : Fin numLimbs,
      env.get (i₀ + i.val)
        = (emuOfNat ((BigInt.value limbBits a + BigInt.value limbBits b) % P256))[i.val])
    (h_wit_q : env.get (i₀ + numLimbs)
      = (((BigInt.value limbBits a + BigInt.value limbBits b) / P256 : ℕ) : F circomPrime)) :
    env.get (i₀ + numLimbs) * (env.get (i₀ + numLimbs) + -1) = 0 ∧
      BigInt.Normalized limbBits (Vector.map (Expression.eval env)
          (Vector.mapRange numLimbs fun i => var { index := i₀ + i })) ∧
        ((BigInt.Normalized limbBits (Vector.map (Expression.eval env)
              (Vector.mapRange numLimbs fun i => var { index := i₀ + i })) ∧
            BigInt.Normalized limbBits (Vector.map (Expression.eval env) pConst)) ∧
          BigInt.value limbBits (Vector.map (Expression.eval env)
              (Vector.mapRange numLimbs fun i => var { index := i₀ + i })) <
            BigInt.value limbBits (Vector.map (Expression.eval env) pConst)) ∧
        ((∀ k : Fin (2 * numLimbs - 1),
            (Expression.eval env
                (if h : k.val < numLimbs then a_var[k.val]'h + b_var[k.val]'h else 0)).val
              < (numLimbs + 1) * 2 ^ (2 * limbBits)) ∧
          ∀ k : Fin (2 * numLimbs - 1),
            (Expression.eval env
                (if h : k.val < numLimbs
                  then var { index := i₀ + numLimbs } * pConst[k.val]'h + var { index := i₀ + k.val }
                  else 0)).val
              < (numLimbs + 1) * 2 ^ (2 * limbBits)) ∧
          polyValue limbBits (Vector.map (Expression.eval env)
              (Vector.mapFinRange (2 * numLimbs - 1) fun k =>
                if h : k.val < numLimbs then a_var[k.val]'h + b_var[k.val]'h else 0)) =
            polyValue limbBits (Vector.map (Expression.eval env)
              (Vector.mapFinRange (2 * numLimbs - 1) fun k =>
                if h : k.val < numLimbs
                then var { index := i₀ + numLimbs } * pConst[k.val]'h + var { index := i₀ + k.val }
                else 0)) := by
  obtain ⟨ha_norm, ha_lt⟩ := ha
  obtain ⟨hb_norm, hb_lt⟩ := hb
  set va := BigInt.value limbBits a with hva
  set vb := BigInt.value limbBits b with hvb

  have hq2 : (va + vb) / P256 ≤ 1 := by
    have h := (Nat.div_lt_iff_lt_mul P256_pos).mpr (by omega : va + vb < 2 * P256)
    omega
  set qNat := (va + vb) / P256 with hqNat
  set rN := (va + vb) % P256 with hrN
  have hrN_lt : rN < P256 := Nat.mod_lt _ P256_pos
  have hrN_pow : rN < 2 ^ (limbBits * numLimbs) := lt_trans hrN_lt P256_lt

  have hwit : ∀ i : Fin numLimbs, env.get (i₀ + i.val)
      = ((rN / 2 ^ (limbBits * i.val) % 2 ^ limbBits : ℕ) : F circomPrime) := by
    intro i
    rw [h_wit_r i, emuOfNat_getElem _ i.val i.isLt]
    rfl
  have hrv_norm : BigInt.Normalized limbBits (Vector.map (Expression.eval env)
      (Vector.mapRange numLimbs fun i => var { index := i₀ + i })) :=
    MulMod.normalized_mapRange i₀ rN env two_pow_limb_lt hwit
  have hrv_val : BigInt.value limbBits (Vector.map (Expression.eval env)
      (Vector.mapRange numLimbs fun i => var { index := i₀ + i })) = rN :=
    BigInt.value_mapRange i₀ rN env two_pow_limb_lt hrN_pow hwit
  refine ⟨?_, hrv_norm, ⟨⟨hrv_norm, pConst_normalized env⟩, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  ·
    rw [h_wit_q]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hq2 with h | h <;> rw [h] <;> norm_num
  ·
    rw [hrv_val, pConst_value env]
    exact hrN_lt
  · exact lhs_bounds env a_var b_var a b h_input_a h_input_b ha_norm hb_norm
  · exact rhs_bounds env i₀ qNat h_wit_q hq2 (outVar_val_lt env i₀ hrv_norm)
  ·
    rw [polyValue_lhs env a_var b_var a b h_input_a h_input_b ha_norm hb_norm,
      polyValue_rhs env i₀ qNat h_wit_q hq2 (outVar_val_lt env i₀ hrv_norm),
      hrv_val]
    calc va + vb = P256 * qNat + rN := by
          rw [hqNat, hrN]
          exact (Nat.div_add_mod (va + vb) P256).symm
      _ = qNat * P256 + rN := by ring

end AddMod

end Solution.Secp256k1ScalarMulFixedBase

end DonorFile0_9

-- Adapted donor module: AddMod
section DonorFile0_10

namespace Solution.Secp256k1ScalarMulFixedBase
namespace AddMod

structure Inputs (F : Type) where
  a : Emu F
  b : Emu F
deriving ProvableStruct

def main (input : Var Inputs (F circomPrime)) :
    Circuit (F circomPrime) (Var Emu (F circomPrime)) := do
  let { a, b } := input

  let r ← ProvableType.witness (α := Emu) fun env =>
    emuOfNat ((evalEmu env a + evalEmu env b) % P256)
  let q ← ProvableType.witness (α := field) fun env =>
    (((evalEmu env a + evalEmu env b) / P256 : ℕ) : F circomPrime)

  assertZero (q * (q - 1))

  Normalize.circuit secpParams r
  LessThan.circuit secpParams { lhs := r, rhs := pConst }

  let lhs : Vector (Expression (F circomPrime)) (2 * numLimbs - 1) :=
    Vector.mapFinRange (2 * numLimbs - 1) fun k =>
      if h : k.val < numLimbs then a[k.val]'h + b[k.val]'h else 0
  let rhs : Vector (Expression (F circomPrime)) (2 * numLimbs - 1) :=
    Vector.mapFinRange (2 * numLimbs - 1) fun k =>
      if h : k.val < numLimbs then q * pConst[k.val]'h + r[k.val]'h else 0
  EqViaCarries.circuit secpParams { lhs := lhs, rhs := rhs }

  return r

instance elaborated : ElaboratedCircuit (F circomPrime) Inputs Emu main := by
  elaborate_circuit

def Assumptions (input : Inputs (F circomPrime)) : Prop :=
  Fe.Valid input.a ∧ Fe.Valid input.b

def Spec (input : Inputs (F circomPrime)) (out : Emu (F circomPrime)) : Prop :=
  Fe.Valid out ∧ decodeFe out = decodeFe input.a + decodeFe input.b

theorem soundness : Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [Normalize.circuit, Normalize.elaborated, Normalize.main,
    Normalize.Assumptions, Normalize.Spec,
    EqViaCarries.circuit, EqViaCarries.elaborated, EqViaCarries.main,
    EqViaCarries.Assumptions, EqViaCarries.Spec,
    LessThan.circuit, LessThan.elaborated, LessThan.main,
    LessThan.Assumptions, LessThan.Spec]
  obtain ⟨hq_bool, hr_norm, h_lt_impl, h_eq_impl⟩ := h_holds
  exact soundness_core i₀ env input_var_a input_var_b input_a input_b
    h_input.1 h_input.2 h_assumptions.1 h_assumptions.2 hq_bool hr_norm h_lt_impl h_eq_impl

theorem completeness : Completeness (F circomPrime) main Assumptions := by
  circuit_proof_start [Normalize.circuit, Normalize.elaborated, Normalize.main,
    Normalize.Assumptions, Normalize.Spec,
    EqViaCarries.circuit, EqViaCarries.elaborated, EqViaCarries.main,
    EqViaCarries.Assumptions, EqViaCarries.Spec,
    LessThan.circuit, LessThan.elaborated, LessThan.main,
    LessThan.Assumptions, LessThan.Spec]
  have heva : evalEmu env input_var_a = BigInt.value limbBits input_a := by
    rw [evalEmu, BigInt.value, ← h_input.1]
  have hevb : evalEmu env input_var_b = BigInt.value limbBits input_b := by
    rw [evalEmu, BigInt.value, ← h_input.2]
  rw [heva, hevb] at h_env
  exact completeness_core i₀ env.toEnvironment input_var_a input_var_b input_a input_b
    h_input.1 h_input.2 h_assumptions.1 h_assumptions.2 h_env.1 h_env.2

def circuit : FormalCircuit (F circomPrime) Inputs Emu where
  main; elaborated; Assumptions; Spec; soundness; completeness

end AddMod
end Solution.Secp256k1ScalarMulFixedBase

end DonorFile0_10

-- Adapted donor module: SubModTheorems
section DonorFile0_11

namespace Solution.Secp256k1ScalarMulFixedBase
open Solution.Secp256k1ScalarMulFixedBase.Limbs

namespace SubMod

lemma sub_witness_identity {va vb : ℕ} (hva : va < P256) (hvb : vb < P256) :
    (va + P256 - vb) % P256 + vb = va + (if va < vb then 1 else 0) * P256 := by
  by_cases h : va < vb
  · rw [if_pos h, Nat.mod_eq_of_lt (by omega : va + P256 - vb < P256)]
    omega
  · rw [if_neg h, show va + P256 - vb = (va - vb) + P256 from by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : va - vb < P256)]
    omega

lemma lhs_bounds (env : Environment (F circomPrime)) (i₀ : ℕ)
    (b_var : Var Emu (F circomPrime)) (b : Emu (F circomPrime))
    (h_input_b : Vector.map (Expression.eval env) b_var = b)
    (hb_norm : b.Normalized limbBits)
    (hr : ∀ k : ℕ, k < numLimbs → (env.get (i₀ + k)).val < 2 ^ limbBits) :
    ∀ k : Fin (2 * numLimbs - 1),
      (Expression.eval env
          (if h : k.val < numLimbs then var { index := i₀ + k.val } + b_var[k.val]'h else 0)).val
        < (numLimbs + 1) * 2 ^ (2 * limbBits) := by
  intro k
  by_cases hk : k.val < numLimbs
  · rw [dif_pos hk,
      show Expression.eval env (var { index := i₀ + k.val } + b_var[k.val]'hk)
        = env.get (i₀ + k.val) + Expression.eval env (b_var[k.val]'hk) from rfl,
      show Expression.eval env (b_var[k.val]'hk) = b[k.val]'hk from by
        rw [← h_input_b, Vector.getElem_map]]
    exact bound_add_limb (hr k.val hk) (hb_norm ⟨k.val, hk⟩)
  · rw [dif_neg hk, show Expression.eval env (0 : Expression (F circomPrime)) = 0 from rfl,
      ZMod.val_zero]
    positivity

lemma rhs_bounds (env : Environment (F circomPrime)) (i₀ : ℕ)
    (a_var : Var Emu (F circomPrime)) (a : Emu (F circomPrime))
    (h_input_a : Vector.map (Expression.eval env) a_var = a)
    (ha_norm : a.Normalized limbBits) (qN : ℕ)
    (hq : env.get (i₀ + numLimbs) = ((qN : ℕ) : F circomPrime)) (hqN : qN ≤ 1) :
    ∀ k : Fin (2 * numLimbs - 1),
      (Expression.eval env
          (if h : k.val < numLimbs
            then a_var[k.val]'h + var { index := i₀ + numLimbs } * pConst[k.val]'h
            else 0)).val
        < (numLimbs + 1) * 2 ^ (2 * limbBits) := by
  intro k
  by_cases hk : k.val < numLimbs
  · rw [dif_pos hk,
      show Expression.eval env
            (a_var[k.val]'hk + var { index := i₀ + numLimbs } * pConst[k.val]'hk)
          = Expression.eval env (a_var[k.val]'hk)
            + env.get (i₀ + numLimbs) * Expression.eval env (pConst[k.val]'hk) from rfl,
      show Expression.eval env (a_var[k.val]'hk) = a[k.val]'hk from by
        rw [← h_input_a, Vector.getElem_map],
      hq, eval_pConst_getElem env k.val hk]
    have h1 : (a[k.val]'hk).val < 2 ^ limbBits := ha_norm ⟨k.val, hk⟩
    have h2 := ZMod.val_add_le (a[k.val]'hk)
      (((qN : ℕ) : F circomPrime) * ((limbOfNat P256 k.val : ℕ) : F circomPrime))
    rw [val_q_mul_limb hqN k.val] at h2
    have h3 := limbOfNat_lt P256 k.val
    have h4 : qN * limbOfNat P256 k.val ≤ 1 * limbOfNat P256 k.val :=
      Nat.mul_le_mul_right _ hqN
    have := limb_add_le_bound
    omega
  · rw [dif_neg hk, show Expression.eval env (0 : Expression (F circomPrime)) = 0 from rfl,
      ZMod.val_zero]
    positivity

lemma polyValue_lhs (env : Environment (F circomPrime)) (i₀ : ℕ)
    (b_var : Var Emu (F circomPrime)) (b : Emu (F circomPrime))
    (h_input_b : Vector.map (Expression.eval env) b_var = b)
    (hb_norm : b.Normalized limbBits)
    (hr : ∀ k : ℕ, k < numLimbs → (env.get (i₀ + k)).val < 2 ^ limbBits) :
    polyValue limbBits (Vector.map (Expression.eval env)
        (Vector.mapFinRange (2 * numLimbs - 1) fun k =>
          if h : k.val < numLimbs then var { index := i₀ + k.val } + b_var[k.val]'h else 0))
      = BigInt.value limbBits (Vector.map (Expression.eval env)
          (Vector.mapRange numLimbs fun i => var { index := i₀ + i }))
        + BigInt.value limbBits b := by
  refine (polyValue_padded limbBits env
      (fun k h => var { index := i₀ + k.val } + b_var[k.val]'h)
      (fun k => (env.get (i₀ + k)).val
        + (if h : k < numLimbs then (b[k]'h).val else 0)) ?_).trans ?_
  · intro k hk
    rw [show Expression.eval env (var { index := i₀ + k.val } + b_var[k.val]'hk)
        = env.get (i₀ + k.val) + Expression.eval env (b_var[k.val]'hk) from rfl,
      show Expression.eval env (b_var[k.val]'hk) = b[k.val]'hk from by
        rw [← h_input_b, Vector.getElem_map],
      val_add_limb (u := env.get (i₀ + k.val)) (v := b[k.val]'hk)
        (hr k.val hk) (hb_norm ⟨k.val, hk⟩)]
    simp only [dif_pos hk]
  · rw [value_outVar limbBits env i₀, value_eq_range_sum limbBits b,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => add_mul _ _ _

lemma polyValue_rhs (env : Environment (F circomPrime)) (i₀ : ℕ)
    (a_var : Var Emu (F circomPrime)) (a : Emu (F circomPrime))
    (h_input_a : Vector.map (Expression.eval env) a_var = a)
    (ha_norm : a.Normalized limbBits) (qN : ℕ)
    (hq : env.get (i₀ + numLimbs) = ((qN : ℕ) : F circomPrime)) (hqN : qN ≤ 1) :
    polyValue limbBits (Vector.map (Expression.eval env)
        (Vector.mapFinRange (2 * numLimbs - 1) fun k =>
          if h : k.val < numLimbs
          then a_var[k.val]'h + var { index := i₀ + numLimbs } * pConst[k.val]'h
          else 0))
      = BigInt.value limbBits a + qN * P256 := by
  refine (polyValue_padded limbBits env
      (fun k h => a_var[k.val]'h + var { index := i₀ + numLimbs } * pConst[k.val]'h)
      (fun k => (if h : k < numLimbs then (a[k]'h).val else 0)
        + qN * limbOfNat P256 k) ?_).trans ?_
  · intro k hk
    rw [show Expression.eval env
          (a_var[k.val]'hk + var { index := i₀ + numLimbs } * pConst[k.val]'hk)
        = Expression.eval env (a_var[k.val]'hk)
          + env.get (i₀ + numLimbs) * Expression.eval env (pConst[k.val]'hk) from rfl,
      show Expression.eval env (a_var[k.val]'hk) = a[k.val]'hk from by
        rw [← h_input_a, Vector.getElem_map],
      hq, eval_pConst_getElem env k.val hk,
      ZMod.val_add_of_lt, val_q_mul_limb hqN k.val]
    · simp only [dif_pos hk]
    ·
      rw [val_q_mul_limb hqN k.val]
      have h1 : (a[k.val]'hk).val < 2 ^ limbBits := ha_norm ⟨k.val, hk⟩
      have h2 := limbOfNat_lt P256 k.val
      have h3 : qN * limbOfNat P256 k.val ≤ 1 * limbOfNat P256 k.val :=
        Nat.mul_le_mul_right _ hqN
      have := limb_add_lt
      omega
  ·
    rw [value_eq_range_sum limbBits a]
    have hsplit : (∑ k ∈ Finset.range numLimbs,
          ((if h : k < numLimbs then (a[k]'h).val else 0) + qN * limbOfNat P256 k)
            * 2 ^ (limbBits * k))
        = (∑ k ∈ Finset.range numLimbs,
            (if h : k < numLimbs then (a[k]'h).val else 0) * 2 ^ (limbBits * k))
          + ∑ k ∈ Finset.range numLimbs, qN * (limbOfNat P256 k * 2 ^ (limbBits * k)) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hsplit, ← Finset.mul_sum, limb_sum_P256]

lemma soundness_core (i₀ : ℕ) (env : Environment (F circomPrime))
    (a_var b_var : Var Emu (F circomPrime)) (a b : Emu (F circomPrime))
    (h_input_a : Vector.map (Expression.eval env) a_var = a)
    (h_input_b : Vector.map (Expression.eval env) b_var = b)
    (ha : Fe.Valid a) (hb : Fe.Valid b)
    (hq_bool : env.get (i₀ + numLimbs) * (env.get (i₀ + numLimbs) + -1) = 0)
    (hr_norm : BigInt.Normalized limbBits (Vector.map (Expression.eval env)
        (Vector.mapRange numLimbs fun i => var { index := i₀ + i })))
    (h_lt_impl :
      BigInt.Normalized limbBits (Vector.map (Expression.eval env)
          (Vector.mapRange numLimbs fun i => var { index := i₀ + i })) ∧
        BigInt.Normalized limbBits (Vector.map (Expression.eval env) pConst) →
        BigInt.value limbBits (Vector.map (Expression.eval env)
            (Vector.mapRange numLimbs fun i => var { index := i₀ + i })) <
          BigInt.value limbBits (Vector.map (Expression.eval env) pConst))
    (h_eq_impl :
      ((∀ k : Fin (2 * numLimbs - 1),
          (Expression.eval env
              (if h : k.val < numLimbs then var { index := i₀ + k.val } + b_var[k.val]'h
                else 0)).val
            < (numLimbs + 1) * 2 ^ (2 * limbBits)) ∧
        ∀ k : Fin (2 * numLimbs - 1),
          (Expression.eval env
              (if h : k.val < numLimbs
                then a_var[k.val]'h + var { index := i₀ + numLimbs } * pConst[k.val]'h
                else 0)).val
            < (numLimbs + 1) * 2 ^ (2 * limbBits)) →
        polyValue limbBits (Vector.map (Expression.eval env)
            (Vector.mapFinRange (2 * numLimbs - 1) fun k =>
              if h : k.val < numLimbs then var { index := i₀ + k.val } + b_var[k.val]'h
              else 0)) =
          polyValue limbBits (Vector.map (Expression.eval env)
            (Vector.mapFinRange (2 * numLimbs - 1) fun k =>
              if h : k.val < numLimbs
              then a_var[k.val]'h + var { index := i₀ + numLimbs } * pConst[k.val]'h
              else 0))) :
    Fe.Valid (Vector.map (Expression.eval env)
        (Vector.mapRange numLimbs fun i => var { index := i₀ + i })) ∧
      decodeFe (Vector.map (Expression.eval env)
          (Vector.mapRange numLimbs fun i => var { index := i₀ + i }))
        = decodeFe a - decodeFe b := by
  obtain ⟨ha_norm, ha_lt⟩ := ha
  obtain ⟨hb_norm, hb_lt⟩ := hb

  have hq01 : (env.get (i₀ + numLimbs)).val ≤ 1 := by
    rcases mul_eq_zero.mp hq_bool with h | h
    · rw [h, ZMod.val_zero]
      omega
    · rw [add_neg_eq_zero] at h
      rw [h, ZMod.val_one]
  have hq_cast : env.get (i₀ + numLimbs)
      = (((env.get (i₀ + numLimbs)).val : ℕ) : F circomPrime) :=
    (ZMod.natCast_zmod_val _).symm

  have h_polyeq := h_eq_impl
    ⟨lhs_bounds env i₀ b_var b h_input_b hb_norm (outVar_val_lt env i₀ hr_norm),
      rhs_bounds env i₀ a_var a h_input_a ha_norm _ hq_cast hq01⟩
  rw [polyValue_lhs env i₀ b_var b h_input_b hb_norm (outVar_val_lt env i₀ hr_norm),
    polyValue_rhs env i₀ a_var a h_input_a ha_norm _ hq_cast hq01] at h_polyeq

  have hr_lt : BigInt.value limbBits (Vector.map (Expression.eval env)
      (Vector.mapRange numLimbs fun i => var { index := i₀ + i })) < P256 := by
    have h := h_lt_impl ⟨hr_norm, pConst_normalized env⟩
    rwa [pConst_value env] at h
  refine ⟨⟨hr_norm, hr_lt⟩, ?_⟩

  have hcast := congrArg (Nat.cast : ℕ → Specs.Secp256k1.Fp) h_polyeq
  push_cast at hcast
  rw [show ((P256 : ℕ) : Specs.Secp256k1.Fp) = 0 from ZMod.natCast_self _,
    mul_zero, add_zero] at hcast
  simp only [decodeFe]
  exact eq_sub_of_add_eq hcast

lemma completeness_core (i₀ : ℕ) (env : Environment (F circomPrime))
    (a_var b_var : Var Emu (F circomPrime)) (a b : Emu (F circomPrime))
    (h_input_a : Vector.map (Expression.eval env) a_var = a)
    (h_input_b : Vector.map (Expression.eval env) b_var = b)
    (ha : Fe.Valid a) (hb : Fe.Valid b)
    (h_wit_r : ∀ i : Fin numLimbs,
      env.get (i₀ + i.val)
        = (emuOfNat ((BigInt.value limbBits a + P256 - BigInt.value limbBits b) % P256))[i.val])
    (h_wit_q : env.get (i₀ + numLimbs)
      = (((if BigInt.value limbBits a < BigInt.value limbBits b then 1 else 0 : ℕ))
          : F circomPrime)) :
    env.get (i₀ + numLimbs) * (env.get (i₀ + numLimbs) + -1) = 0 ∧
      BigInt.Normalized limbBits (Vector.map (Expression.eval env)
          (Vector.mapRange numLimbs fun i => var { index := i₀ + i })) ∧
        ((BigInt.Normalized limbBits (Vector.map (Expression.eval env)
              (Vector.mapRange numLimbs fun i => var { index := i₀ + i })) ∧
            BigInt.Normalized limbBits (Vector.map (Expression.eval env) pConst)) ∧
          BigInt.value limbBits (Vector.map (Expression.eval env)
              (Vector.mapRange numLimbs fun i => var { index := i₀ + i })) <
            BigInt.value limbBits (Vector.map (Expression.eval env) pConst)) ∧
        ((∀ k : Fin (2 * numLimbs - 1),
            (Expression.eval env
                (if h : k.val < numLimbs then var { index := i₀ + k.val } + b_var[k.val]'h
                  else 0)).val
              < (numLimbs + 1) * 2 ^ (2 * limbBits)) ∧
          ∀ k : Fin (2 * numLimbs - 1),
            (Expression.eval env
                (if h : k.val < numLimbs
                  then a_var[k.val]'h + var { index := i₀ + numLimbs } * pConst[k.val]'h
                  else 0)).val
              < (numLimbs + 1) * 2 ^ (2 * limbBits)) ∧
          polyValue limbBits (Vector.map (Expression.eval env)
              (Vector.mapFinRange (2 * numLimbs - 1) fun k =>
                if h : k.val < numLimbs then var { index := i₀ + k.val } + b_var[k.val]'h
                else 0)) =
            polyValue limbBits (Vector.map (Expression.eval env)
              (Vector.mapFinRange (2 * numLimbs - 1) fun k =>
                if h : k.val < numLimbs
                then a_var[k.val]'h + var { index := i₀ + numLimbs } * pConst[k.val]'h
                else 0)) := by
  obtain ⟨ha_norm, ha_lt⟩ := ha
  obtain ⟨hb_norm, hb_lt⟩ := hb
  set va := BigInt.value limbBits a with hva
  set vb := BigInt.value limbBits b with hvb
  set qNat : ℕ := if va < vb then 1 else 0 with hqNat
  set rN := (va + P256 - vb) % P256 with hrN
  have hqNat_le : qNat ≤ 1 := by
    rw [hqNat]
    split <;> omega
  have hrN_lt : rN < P256 := Nat.mod_lt _ P256_pos
  have hrN_pow : rN < 2 ^ (limbBits * numLimbs) := lt_trans hrN_lt P256_lt

  have hkey : rN + vb = va + qNat * P256 := by
    rw [hrN, hqNat]
    exact sub_witness_identity ha_lt hb_lt

  have hwit : ∀ i : Fin numLimbs, env.get (i₀ + i.val)
      = ((rN / 2 ^ (limbBits * i.val) % 2 ^ limbBits : ℕ) : F circomPrime) := by
    intro i
    rw [h_wit_r i, emuOfNat_getElem _ i.val i.isLt]
    rfl
  have hrv_norm : BigInt.Normalized limbBits (Vector.map (Expression.eval env)
      (Vector.mapRange numLimbs fun i => var { index := i₀ + i })) :=
    MulMod.normalized_mapRange i₀ rN env two_pow_limb_lt hwit
  have hrv_val : BigInt.value limbBits (Vector.map (Expression.eval env)
      (Vector.mapRange numLimbs fun i => var { index := i₀ + i })) = rN :=
    BigInt.value_mapRange i₀ rN env two_pow_limb_lt hrN_pow hwit
  refine ⟨?_, hrv_norm, ⟨⟨hrv_norm, pConst_normalized env⟩, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  ·
    rw [h_wit_q]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hqNat_le with h | h <;> rw [h] <;> norm_num
  ·
    rw [hrv_val, pConst_value env]
    exact hrN_lt
  · exact lhs_bounds env i₀ b_var b h_input_b hb_norm (outVar_val_lt env i₀ hrv_norm)
  · exact rhs_bounds env i₀ a_var a h_input_a ha_norm qNat h_wit_q hqNat_le
  ·
    rw [polyValue_lhs env i₀ b_var b h_input_b hb_norm (outVar_val_lt env i₀ hrv_norm),
      polyValue_rhs env i₀ a_var a h_input_a ha_norm qNat h_wit_q hqNat_le,
      hrv_val]
    exact hkey

end SubMod

end Solution.Secp256k1ScalarMulFixedBase

end DonorFile0_11

-- Adapted donor module: SubMod
section DonorFile0_12

namespace Solution.Secp256k1ScalarMulFixedBase
namespace SubMod

structure Inputs (F : Type) where
  a : Emu F
  b : Emu F
deriving ProvableStruct

def main (input : Var Inputs (F circomPrime)) :
    Circuit (F circomPrime) (Var Emu (F circomPrime)) := do
  let { a, b } := input

  let r ← ProvableType.witness (α := Emu) fun env =>
    emuOfNat ((evalEmu env a + P256 - evalEmu env b) % P256)
  let q ← ProvableType.witness (α := field) fun env =>
    (((if evalEmu env a < evalEmu env b then 1 else 0 : ℕ)) : F circomPrime)

  assertZero (q * (q - 1))

  Normalize.circuit secpParams r
  LessThan.circuit secpParams { lhs := r, rhs := pConst }

  let lhs : Vector (Expression (F circomPrime)) (2 * numLimbs - 1) :=
    Vector.mapFinRange (2 * numLimbs - 1) fun k =>
      if h : k.val < numLimbs then r[k.val]'h + b[k.val]'h else 0
  let rhs : Vector (Expression (F circomPrime)) (2 * numLimbs - 1) :=
    Vector.mapFinRange (2 * numLimbs - 1) fun k =>
      if h : k.val < numLimbs then a[k.val]'h + q * pConst[k.val]'h else 0
  EqViaCarries.circuit secpParams { lhs := lhs, rhs := rhs }

  return r

instance elaborated : ElaboratedCircuit (F circomPrime) Inputs Emu main := by
  elaborate_circuit

def Assumptions (input : Inputs (F circomPrime)) : Prop :=
  Fe.Valid input.a ∧ Fe.Valid input.b

def Spec (input : Inputs (F circomPrime)) (out : Emu (F circomPrime)) : Prop :=
  Fe.Valid out ∧ decodeFe out = decodeFe input.a - decodeFe input.b

theorem soundness : Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [Normalize.circuit, Normalize.elaborated, Normalize.main,
    Normalize.Assumptions, Normalize.Spec,
    EqViaCarries.circuit, EqViaCarries.elaborated, EqViaCarries.main,
    EqViaCarries.Assumptions, EqViaCarries.Spec,
    LessThan.circuit, LessThan.elaborated, LessThan.main,
    LessThan.Assumptions, LessThan.Spec]
  obtain ⟨hq_bool, hr_norm, h_lt_impl, h_eq_impl⟩ := h_holds
  exact soundness_core i₀ env input_var_a input_var_b input_a input_b
    h_input.1 h_input.2 h_assumptions.1 h_assumptions.2 hq_bool hr_norm h_lt_impl h_eq_impl

theorem completeness : Completeness (F circomPrime) main Assumptions := by
  circuit_proof_start [Normalize.circuit, Normalize.elaborated, Normalize.main,
    Normalize.Assumptions, Normalize.Spec,
    EqViaCarries.circuit, EqViaCarries.elaborated, EqViaCarries.main,
    EqViaCarries.Assumptions, EqViaCarries.Spec,
    LessThan.circuit, LessThan.elaborated, LessThan.main,
    LessThan.Assumptions, LessThan.Spec]
  have heva : evalEmu env input_var_a = BigInt.value limbBits input_a := by
    rw [evalEmu, BigInt.value, ← h_input.1]
  have hevb : evalEmu env input_var_b = BigInt.value limbBits input_b := by
    rw [evalEmu, BigInt.value, ← h_input.2]
  rw [heva, hevb] at h_env
  exact completeness_core i₀ env.toEnvironment input_var_a input_var_b input_a input_b
    h_input.1 h_input.2 h_assumptions.1 h_assumptions.2 h_env.1 h_env.2

def circuit : FormalCircuit (F circomPrime) Inputs Emu where
  main; elaborated; Assumptions; Spec; soundness; completeness

end SubMod
end Solution.Secp256k1ScalarMulFixedBase

end DonorFile0_12

-- Adapted donor module: IsZeroFeTheorems
section DonorFile0_13

namespace Solution.Secp256k1ScalarMulFixedBase

section
variable {p : ℕ} [Fact p.Prime] {m : ℕ}

omit [Fact (Nat.Prime p)] in

theorem BigInt.value_eq_zero_iff {B : ℕ} (x : BigInt m (F p)) :
    BigInt.value B x = 0 ↔ ∀ i : Fin m, x[i] = 0 := by
  rw [BigInt.value_eq_sum, Finset.sum_eq_zero_iff]
  constructor
  · intro h i
    have hterm := h i (Finset.mem_univ i)
    have hval : (x[i]).val = 0 := by
      have hpow : 0 < 2 ^ (B * i.val) := Nat.two_pow_pos _
      rcases Nat.mul_eq_zero.mp hterm with h0 | h0
      · exact h0
      · omega
    exact (ZMod.val_eq_zero _).mp hval
  · intro h i _
    rw [h i, ZMod.val_zero, Nat.zero_mul]

end

theorem decodeFe_eq_zero_iff {x : Emu (F circomPrime)} (hx : Fe.Valid x) :
    decodeFe x = 0 ↔ (x[0] = 0 ∧ x[1] = 0 ∧ x[2] = 0 ∧ x[3] = 0) := by
  have hvalue : decodeFe x = 0 ↔ BigInt.value limbBits x = 0 := by
    simp only [decodeFe]
    constructor
    · intro h
      exact Nat.eq_zero_of_dvd_of_lt ((ZMod.natCast_eq_zero_iff _ _).mp h) hx.2
    · intro h
      rw [h, Nat.cast_zero]
  rw [hvalue, BigInt.value_eq_zero_iff]
  constructor
  · intro h
    exact ⟨h 0, h 1, h 2, h 3⟩
  · rintro ⟨h0, h1, h2, h3⟩ ⟨i, hi⟩
    match i, hi with
    | 0, _ => exact h0
    | 1, _ => exact h1
    | 2, _ => exact h2
    | 3, _ => exact h3

end Solution.Secp256k1ScalarMulFixedBase

end DonorFile0_13

-- Adapted donor module: IsZeroFe
section DonorFile0_14

namespace Solution.Secp256k1ScalarMulFixedBase
namespace IsZeroFe

def main (x : Var Emu (F circomPrime)) :
    Circuit (F circomPrime) (Expression (F circomPrime)) := do
  let z0 ← subcircuit Gadgets.IsZeroField.circuit x[0]
  let z1 ← subcircuit Gadgets.IsZeroField.circuit x[1]
  let z2 ← subcircuit Gadgets.IsZeroField.circuit x[2]
  let z3 ← subcircuit Gadgets.IsZeroField.circuit x[3]
  let t01 <== z0 * z1
  let t23 <== z2 * z3
  let z <== t01 * t23
  return z

instance elaborated : ElaboratedCircuit (F circomPrime) Emu field main := by
  elaborate_circuit

def Assumptions (x : Emu (F circomPrime)) : Prop :=
  Fe.Valid x

def Spec (x : Emu (F circomPrime)) (out : F circomPrime) : Prop :=
  out = if decodeFe x = 0 then 1 else 0

theorem soundness :
    Soundness (Input := Emu) (Output := field) (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [Gadgets.IsZeroField.circuit, Gadgets.IsZeroField.Assumptions,
    Gadgets.IsZeroField.Spec]
  obtain ⟨hz0, hz1, hz2, hz3, ht01, ht23, hz⟩ := h_holds
  have hx : ∀ (i : ℕ) (hi : i < 4), Expression.eval env input_var[i] = input[i] := by
    intro i hi
    rw [← h_input, Vector.getElem_map]
  rw [hx 0 (by omega)] at hz0
  rw [hx 1 (by omega)] at hz1
  rw [hx 2 (by omega)] at hz2
  rw [hx 3 (by omega)] at hz3
  rw [hz, ht01, ht23, hz0, hz1, hz2, hz3]
  simp only [decodeFe_eq_zero_iff h_assumptions]
  by_cases h0 : input[0] = 0 <;> by_cases h1 : input[1] = 0 <;>
    by_cases h2 : input[2] = 0 <;> by_cases h3 : input[3] = 0 <;>
    simp [h0, h1, h2, h3]

theorem completeness :
    Completeness (Input := Emu) (Output := field) (F circomPrime) main Assumptions := by
  circuit_proof_start [Gadgets.IsZeroField.circuit, Gadgets.IsZeroField.Assumptions,
    Gadgets.IsZeroField.Spec]
  obtain ⟨-, -, -, -, ht01, ht23, hz⟩ := h_env
  exact ⟨ht01, ht23, hz⟩

def circuit : FormalCircuit (F circomPrime) Emu field where
  main; elaborated; Assumptions; Spec; soundness; completeness

end IsZeroFe
end Solution.Secp256k1ScalarMulFixedBase

namespace Solution.Secp256k1ScalarMulFixedBase
namespace IsZeroFeD

def main (x : Var Emu (F circomPrime)) :
    Circuit (F circomPrime) (Expression (F circomPrime)) := do
  let z0 ← subcircuit Gadgets.IsZeroField.circuit x[0]
  let z1 ← subcircuit Gadgets.IsZeroField.circuit x[1]
  let z2 ← subcircuit Gadgets.IsZeroField.circuit x[2]
  let z3 ← subcircuit Gadgets.IsZeroField.circuit x[3]
  let t01 <== z0 * z1
  let t23 <== z2 * z3
  let z <== t01 * t23
  return z

instance elaborated : ElaboratedCircuit (F circomPrime) Emu field main := by
  elaborate_circuit

def Assumptions (_ : Emu (F circomPrime)) : Prop := True

private lemma value_eq_zero_iff (x : Emu (F circomPrime)) :
    BigInt.value limbBits x = 0 ↔ x[0] = 0 ∧ x[1] = 0 ∧ x[2] = 0 ∧ x[3] = 0 := by
  rw [BigInt.value_eq_sum, Finset.sum_eq_zero_iff]
  constructor
  · intro h
    have key : ∀ i : Fin 4, x[i.val]'i.isLt = 0 := by
      intro i
      have hterm := h i (Finset.mem_univ _)
      rw [Fin.getElem_fin] at hterm
      rcases Nat.mul_eq_zero.mp hterm with hv | hp
      · exact (ZMod.val_eq_zero _).mp hv
      · exact absurd hp (Nat.two_pow_pos _).ne'
    exact ⟨key 0, key 1, key 2, key 3⟩
  · rintro ⟨h0, h1, h2, h3⟩ i _
    rw [Fin.getElem_fin]
    fin_cases i <;> simp [h0, h1, h2, h3]

def Spec (x : Emu (F circomPrime)) (out : F circomPrime) : Prop :=
  out = if BigInt.value limbBits x = 0 then 1 else 0

theorem soundness :
    Soundness (Input := Emu) (Output := field) (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [Gadgets.IsZeroField.circuit, Gadgets.IsZeroField.Assumptions,
    Gadgets.IsZeroField.Spec]
  obtain ⟨hz0, hz1, hz2, hz3, ht01, ht23, hz⟩ := h_holds
  have hx : ∀ (i : ℕ) (hi : i < 4), Expression.eval env input_var[i] = input[i] := by
    intro i hi
    rw [← h_input, Vector.getElem_map]
  rw [hx 0 (by omega)] at hz0
  rw [hx 1 (by omega)] at hz1
  rw [hx 2 (by omega)] at hz2
  rw [hx 3 (by omega)] at hz3
  rw [hz, ht01, ht23, hz0, hz1, hz2, hz3]
  simp only [value_eq_zero_iff]
  by_cases h0 : input[0] = 0 <;> by_cases h1 : input[1] = 0 <;>
    by_cases h2 : input[2] = 0 <;> by_cases h3 : input[3] = 0 <;>
    simp [h0, h1, h2, h3]

theorem completeness :
    Completeness (Input := Emu) (Output := field) (F circomPrime) main Assumptions := by
  circuit_proof_start [Gadgets.IsZeroField.circuit, Gadgets.IsZeroField.Assumptions,
    Gadgets.IsZeroField.Spec]
  obtain ⟨-, -, -, -, ht01, ht23, hz⟩ := h_env
  exact ⟨ht01, ht23, hz⟩

def circuit : FormalCircuit (F circomPrime) Emu field where
  main := main
  elaborated := elaborated
  Assumptions := Assumptions
  Spec := Spec
  soundness := soundness
  completeness := completeness

theorem equalityComputableWitnesses (M : TypeMap) [ProvableType M] :
    (Gadgets.Equality.circuit (F := F circomPrime) M).ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition input env env')
    (((Gadgets.Equality.circuit (F := F circomPrime) M).main input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold Gadgets.Equality.circuit Gadgets.Equality.main
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.forEach_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.assertZero_structuralComputableWitnesses_iff]
  intro _
  trivial

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

theorem computableWitnesses : circuit.base.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  have hL : ∀ (y : Expression (F circomPrime)) (o : ℕ),
      (subcircuit Gadgets.IsZeroField.circuit y).localLength o = 2 := by
    intro y o
    simp only [circuit_norm, Gadgets.IsZeroField.circuit]
  have hA : ∀ (r : Var field (F circomPrime)) (o : ℕ),
      (HasAssignEq.assignEq (β := field (Expression (F circomPrime))) r).localLength o = 1 := by
    intro r o
    simp only [circuit_norm, HasAssignEq.assignEq]
  unfold main
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.pure_structuralComputableWitnesses_iff,
    hL, hA, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩

  · exact Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses
      Gadgets.IsZeroField.circuit input input[0] offset
      (fun _ _ h => input_limb_stable (by decide) h) isZeroFieldComputableWitnesses env env'
  · exact Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses
      Gadgets.IsZeroField.circuit input input[1] (offset + 2)
      (fun _ _ h => input_limb_stable (by decide) h) isZeroFieldComputableWitnesses env env'
  · exact Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses
      Gadgets.IsZeroField.circuit input input[2] (offset + 2 + 2)
      (fun _ _ h => input_limb_stable (by decide) h) isZeroFieldComputableWitnesses env env'
  · exact Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses
      Gadgets.IsZeroField.circuit input input[3] (offset + 2 + 2 + 2)
      (fun _ _ h => input_limb_stable (by decide) h) isZeroFieldComputableWitnesses env env'

  · refine ⟨?_, ?_, ?_⟩
    · intro h_agree _
      refine congrArg toElements ?_
      have h0 := isZeroField_output_eval_stable (base := offset) input[0] h_agree (by omega)
      have h1 := isZeroField_output_eval_stable (base := offset + 2) input[1] h_agree (by omega)
      simp only [CircuitType.eval_var_field_prover, Expression.eval, h0, h1]
    · exact equalityFieldSubcircuit_flatStructural_any input _ _ _ env env'
    · trivial

  · refine ⟨?_, ?_, ?_⟩
    · intro h_agree _
      refine congrArg toElements ?_
      have h2 := isZeroField_output_eval_stable (base := offset + 2 + 2) input[2] h_agree (by omega)
      have h3 := isZeroField_output_eval_stable (base := offset + 2 + 2 + 2) input[3] h_agree (by omega)
      simp only [CircuitType.eval_var_field_prover, Expression.eval, h2, h3]
    · exact equalityFieldSubcircuit_flatStructural_any input _ _ _ env env'
    · trivial

  · refine ⟨?_, ?_, ?_⟩
    · intro h_agree _
      refine congrArg toElements ?_
      have h01 := assignEq_output_eval_stable
        ((subcircuit Gadgets.IsZeroField.circuit input[0]).output offset *
          (subcircuit Gadgets.IsZeroField.circuit input[1]).output (offset + 2))
        (base := offset + 2 + 2 + 2 + 2) h_agree (by omega)
      have h23 := assignEq_output_eval_stable
        ((subcircuit Gadgets.IsZeroField.circuit input[2]).output (offset + 2 + 2) *
          (subcircuit Gadgets.IsZeroField.circuit input[3]).output (offset + 2 + 2 + 2))
        (base := offset + 2 + 2 + 2 + 2 + 1) h_agree (by omega)
      simp only [CircuitType.eval_var_field_prover, Expression.eval, h01, h23]
    · exact equalityFieldSubcircuit_flatStructural_any input _ _ _ env env'
    · trivial

theorem computableWitness : ∀ n input,
    ProverEnvironment.OnlyAccessedBelow n
      (fun env : ProverEnvironment (F circomPrime) => eval env input) →
    Circuit.ComputableWitnesses (main input) n :=
  Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnesses_implies
    (circuit := circuit.base) computableWitnesses

lemma eval_output_of_agreesBelow (x : Var Emu (F circomPrime)) {offset k : ℕ}
    {env env' : ProverEnvironment (F circomPrime)}
    (h_agree : env.AgreesBelow k env') (hk : offset + 11 ≤ k) :
    eval env ((main x).output offset) = eval env' ((main x).output offset) := by
  rw [CircuitType.eval_var_field_prover, CircuitType.eval_var_field_prover]
  simp only [main, circuit_norm, Gadgets.IsZeroField.circuit]
  exact h_agree (offset + 10) (by omega)

end IsZeroFeD
end Solution.Secp256k1ScalarMulFixedBase

end DonorFile0_14

-- Adapted donor module: Mux
section DonorFile0_15

namespace Solution.Secp256k1ScalarMulFixedBase
namespace Mux

section
variable {M : TypeMap} [ProvableType M]

structure Inputs (M : TypeMap) (F : Type) where
  selector : F
  ifTrue : M F
  ifFalse : M F
deriving ProvableStruct

def main (input : Var (Inputs M) (F circomPrime)) :
    Circuit (F circomPrime) (Var M (F circomPrime)) := do
  let { selector, ifTrue, ifFalse } := input
  let t := toElements ifTrue
  let f := toElements ifFalse

  let out ← ProvableType.witness (α := M) fun env =>
    let s := Expression.eval env.toEnvironment selector
    let tv := t.map (Expression.eval env.toEnvironment)
    let fv := f.map (Expression.eval env.toEnvironment)
    fromElements (M := M) (if s = 1 then tv else fv)

  let outE := toElements (M := M) out
  let constraints := Vector.ofFn fun i : Fin (size M) =>
    selector * (t[i] - f[i]) + f[i] - outE[i]
  Circuit.forEach constraints assertZero

  return out

instance elaborated : ElaboratedCircuit (F circomPrime) (Inputs M) M main := by
  elaborate_circuit

def Assumptions (input : Inputs M (F circomPrime)) : Prop :=
  IsBool input.selector

def Spec (input : Inputs M (F circomPrime)) (out : M (F circomPrime)) : Prop :=
  out = if input.selector = 1 then input.ifTrue else input.ifFalse

theorem soundness : Soundness (F circomPrime) main Assumptions (Spec (M := M)) := by
  circuit_proof_start
  rcases input with ⟨selector, ifTrue, ifFalse⟩
  simp only [Inputs.mk.injEq] at h_input
  obtain ⟨h_selector, h_ifTrue, h_ifFalse⟩ := h_input
  simp only at h_assumptions
  rw [ProvableType.ext_iff]
  intro i hi
  have h := h_holds ⟨i, hi⟩
  simp only [Vector.getElem_ofFn, Expression.eval,
    ProvableType.getElem_eval_toElements, h_selector, h_ifTrue, h_ifFalse] at h
  rcases h_assumptions with h0 | h1
  · rw [h0] at h
    rw [h0, if_neg (zero_ne_one (α := F circomPrime))]
    rw [zero_mul, zero_add, neg_one_mul, add_neg_eq_zero] at h
    exact h.symm
  · rw [h1] at h
    rw [h1, if_pos rfl]
    rw [one_mul, neg_one_mul, neg_one_mul, add_neg_eq_zero, neg_add_cancel_right] at h
    exact h.symm

theorem completeness :
    Completeness (Input := Inputs M) (Output := M) (F circomPrime) main Assumptions := by
  circuit_proof_start
  rcases input with ⟨selector, ifTrue, ifFalse⟩
  simp only [Inputs.mk.injEq] at h_input
  obtain ⟨h_selector, h_ifTrue, h_ifFalse⟩ := h_input
  simp only at h_assumptions
  intro i
  have henv := h_env i
  simp only [Vector.getElem_ofFn, Expression.eval, varFromOffset,
    ProvableType.toElements_fromElements, Vector.getElem_mapRange]
  rw [henv, h_selector]
  rcases h_assumptions with h0 | h1
  · rw [h0, if_neg (zero_ne_one (α := F circomPrime)), Vector.getElem_map]
    ring
  · rw [h1, if_pos rfl, Vector.getElem_map]
    ring

def circuit : FormalCircuit (F circomPrime) (Inputs M) M where
  main; elaborated; Assumptions; Spec := Spec (M := M); soundness; completeness

end
end Mux
end Solution.Secp256k1ScalarMulFixedBase

namespace Solution.Secp256k1ScalarMulFixedBase
namespace Mux

section ComputableWitness
variable {M : TypeMap} [ProvableType M]
open Challenge.Utils.ComputableWitnessLemmas

theorem computableWitnesses : (circuit (M := M)).ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations offset)
  apply FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  rcases input with ⟨selector, ifTrue, ifFalse⟩
  unfold main
  simp only [
    Circuit.bind_structuralComputableWitnesses_iff,
    Circuit.provableWitness_structuralComputableWitnesses_iff,
    Circuit.forEach_structuralComputableWitnesses_iff,
    Circuit.assertZero_structuralComputableWitnesses_iff,
    Circuit.pure_structuralComputableWitnesses_iff,
    and_true]
  and_intros
  · intro _ h_input
    have hcomp : eval env (Inputs.mk (M := M) selector ifTrue ifFalse)
        = eval env' (Inputs.mk (M := M) selector ifTrue ifFalse) := h_input
    simp only [circuit_norm, Inputs.mk.injEq] at hcomp
    obtain ⟨hs, ht, hf⟩ := hcomp
    have htv : (toElements ifTrue).map (Expression.eval env.toEnvironment)
        = (toElements ifTrue).map (Expression.eval env'.toEnvironment) := by
      apply Vector.ext
      intro i hi
      simp only [Vector.getElem_map, ProvableType.getElem_eval_toElements]
      exact congrArg (fun x => (toElements (M := M) x)[i]'hi) ht
    have hfv : (toElements ifFalse).map (Expression.eval env.toEnvironment)
        = (toElements ifFalse).map (Expression.eval env'.toEnvironment) := by
      apply Vector.ext
      intro i hi
      simp only [Vector.getElem_map, ProvableType.getElem_eval_toElements]
      exact congrArg (fun x => (toElements (M := M) x)[i]'hi) hf
    simp only [hs, htv, hfv]
  · intro _
    trivial

theorem computableWitness : ∀ n (input : Var (Inputs M) (F circomPrime)),
    ProverEnvironment.OnlyAccessedBelow n
      (fun env : ProverEnvironment (F circomPrime) => eval env input) →
    Circuit.ComputableWitnesses (main input) n := by
  exact FormalCircuitBase.computableWitnesses_implies
    (circuit := (circuit (M := M)).base) computableWitnesses

end ComputableWitness

end Mux
end Solution.Secp256k1ScalarMulFixedBase

end DonorFile0_15

-- Adapted donor module: DivOrZeroTheorems
section DonorFile0_16

namespace Solution.Secp256k1ScalarMulFixedBase
namespace DivOrZero

lemma P256_pos : 0 < P256 := by decide

lemma one_lt_P256 : 1 < P256 := by decide

lemma P256_lt : P256 < 2 ^ (limbBits * numLimbs) := by decide

lemma two_pow_limb_lt : 2 ^ limbBits < circomPrime := by decide

instance : NeZero P256 := ⟨Nat.pos_iff_ne_zero.mp P256_pos⟩

lemma limbOfNat_lt (v k : ℕ) : limbOfNat v k < 2 ^ limbBits :=
  Nat.mod_lt _ (Nat.two_pow_pos limbBits)

lemma val_limbOfNat (v k : ℕ) :
    ((limbOfNat v k : ℕ) : F circomPrime).val = limbOfNat v k :=
  ZMod.val_natCast_of_lt (lt_trans (limbOfNat_lt v k) two_pow_limb_lt)

lemma emuOfNat_getElem (v k : ℕ) (hk : k < numLimbs) :
    (emuOfNat v)[k]'hk = ((limbOfNat v k : ℕ) : F circomPrime) := by
  simp only [emuOfNat, Vector.getElem_ofFn]

lemma emuOfNat_normalized (v : ℕ) : (emuOfNat v).Normalized limbBits := by
  intro i
  rw [Fin.getElem_fin, emuOfNat_getElem v i.val i.isLt, val_limbOfNat]
  exact limbOfNat_lt v i.val

lemma value_emuOfNat {v : ℕ} (hv : v < 2 ^ (limbBits * numLimbs)) :
    BigInt.value limbBits (emuOfNat v) = v := by
  rw [BigInt.value_eq_sum]
  have hsum : (∑ k : Fin numLimbs, ((emuOfNat v)[k]).val * 2 ^ (limbBits * k.val))
      = ∑ k ∈ Finset.range numLimbs,
          (v / 2 ^ (limbBits * k) % 2 ^ limbBits) * 2 ^ (limbBits * k) := by
    rw [← Fin.sum_univ_eq_sum_range
      (fun k => (v / 2 ^ (limbBits * k) % 2 ^ limbBits) * 2 ^ (limbBits * k))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fin.getElem_fin, emuOfNat_getElem v i.val i.isLt, val_limbOfNat]
    rfl
  rw [hsum, limb_decomp_mod, Nat.mod_eq_of_lt hv]

lemma fe_valid_emuOfNat {v : ℕ} (hv : v < P256) : Fe.Valid (emuOfNat v) :=
  ⟨emuOfNat_normalized v, by rw [value_emuOfNat (lt_trans hv P256_lt)]; exact hv⟩

lemma secpParams_B : secpParams.B = limbBits := rfl

lemma eval_emuConst_getElem (env : Environment (F circomPrime)) (v k : ℕ)
    (hk : k < numLimbs) :
    Expression.eval env ((emuConst v)[k]'hk) = ((limbOfNat v k : ℕ) : F circomPrime) := by
  simp only [emuConst]
  rw [Vector.getElem_ofFn]
  rfl

lemma eval_emuConst (env : Environment (F circomPrime)) (v : ℕ) :
    Vector.map (Expression.eval env) (emuConst v) = emuOfNat v := by
  apply Vector.ext
  intro k hk
  rw [Vector.getElem_map, eval_emuConst_getElem env v k hk, emuOfNat_getElem v k hk]

lemma eval_pConst (env : Environment (F circomPrime)) :
    Vector.map (Expression.eval env) pConst = emuOfNat P256 :=
  eval_emuConst env P256

lemma eval_oneConst (env : Environment (F circomPrime)) :
    Vector.map (Expression.eval env) oneConst = emuOfNat 1 :=
  eval_emuConst env 1

lemma eval_zeroConst (env : Environment (F circomPrime)) :
    Vector.map (Expression.eval env) zeroConst = emuOfNat 0 :=
  eval_emuConst env 0

lemma pConst_normalized (env : Environment (F circomPrime)) :
    BigInt.Normalized limbBits (Vector.map (Expression.eval env) pConst) := by
  rw [eval_pConst]
  exact emuOfNat_normalized P256

lemma pConst_value (env : Environment (F circomPrime)) :
    BigInt.value limbBits (Vector.map (Expression.eval env) pConst) = P256 := by
  rw [eval_pConst]
  exact value_emuOfNat P256_lt

lemma value_emuOfNat_one : BigInt.value limbBits (emuOfNat 1) = 1 :=
  value_emuOfNat (by decide)

lemma value_emuOfNat_zero : BigInt.value limbBits (emuOfNat 0) = 0 :=
  value_emuOfNat (by decide)

lemma decodeFe_of_value_eq_zero {x : Emu (F circomPrime)}
    (h : BigInt.value limbBits x = 0) : decodeFe x = 0 := by
  rw [decodeFe, h, Nat.cast_zero]

lemma mul_cast_of_mod_eq {l d n : ℕ} (h : l * d % P256 = n) :
    (l : Specs.Secp256k1.Fp) * (d : Specs.Secp256k1.Fp) = (n : Specs.Secp256k1.Fp) := by
  rw [← h, ZMod.natCast_mod, Nat.cast_mul]

lemma witness_val_den_zero (n : Specs.Secp256k1.Fp) :
    (n * (0 : Specs.Secp256k1.Fp)⁻¹).val = 0 := by
  rw [inv_zero, mul_zero, ZMod.val_zero]

lemma witness_cert_nonzero {nv dv : ℕ} (hnv : nv < P256)
    (hd : (dv : Specs.Secp256k1.Fp) ≠ 0) :
    ((nv : Specs.Secp256k1.Fp) * (dv : Specs.Secp256k1.Fp)⁻¹).val * dv % P256 = nv := by
  have h1 : ((((nv : Specs.Secp256k1.Fp) * (dv : Specs.Secp256k1.Fp)⁻¹).val * dv : ℕ) :
      Specs.Secp256k1.Fp) = (nv : Specs.Secp256k1.Fp) := by
    push_cast [ZMod.natCast_val, ZMod.cast_id]
    rw [mul_assoc, inv_mul_cancel₀ hd, mul_one]
  calc ((nv : Specs.Secp256k1.Fp) * (dv : Specs.Secp256k1.Fp)⁻¹).val * dv % P256
      = ((((nv : Specs.Secp256k1.Fp) * (dv : Specs.Secp256k1.Fp)⁻¹).val * dv : ℕ) :
          Specs.Secp256k1.Fp).val := by rw [ZMod.val_natCast]
    _ = ((nv : Specs.Secp256k1.Fp)).val := by rw [h1]
    _ = nv := by rw [ZMod.val_natCast, Nat.mod_eq_of_lt hnv]

end DivOrZero
end Solution.Secp256k1ScalarMulFixedBase

end DonorFile0_16

-- Adapted donor module: DivOrZero
section DonorFile0_17

namespace Solution.Secp256k1ScalarMulFixedBase
namespace DivOrZero

structure Inputs (F : Type) where
  num : Emu F
  den : Emu F
deriving ProvableStruct

def main (input : Var Inputs (F circomPrime)) :
    Circuit (F circomPrime) (Var Emu (F circomPrime)) := do
  let { num, den } := input

  let z ← subcircuit IsZeroFe.circuit den

  let denSafe ← subcircuit (Mux.circuit (M := Emu))
    { selector := z, ifTrue := oneConst, ifFalse := den }
  let numSafe ← subcircuit (Mux.circuit (M := Emu))
    { selector := z, ifTrue := zeroConst, ifFalse := num }

  let lam ← ProvableType.witness (α := Emu) fun env =>
    let denFp : Specs.Secp256k1.Fp := ((evalEmu env den : ℕ) : Specs.Secp256k1.Fp)
    let numFp : Specs.Secp256k1.Fp := ((evalEmu env num : ℕ) : Specs.Secp256k1.Fp)
    emuOfNat (numFp * denFp⁻¹).val

  Normalize.circuit secpParams lam
  LessThan.circuit secpParams { lhs := lam, rhs := pConst }

  let prod ← subcircuit (MulMod.circuit secpParams)
    { a := lam, b := denSafe, modulus := pConst }
  Equal.circuit secpParams { lhs := prod, rhs := numSafe }

  return lam

instance elaborated : ElaboratedCircuit (F circomPrime) Inputs Emu main := by
  elaborate_circuit

def Assumptions (input : Inputs (F circomPrime)) : Prop :=
  Fe.Valid input.num ∧ Fe.Valid input.den

def Spec (input : Inputs (F circomPrime)) (out : Emu (F circomPrime)) : Prop :=
  Fe.Valid out ∧
    (decodeFe input.den ≠ 0 →
      decodeFe out * decodeFe input.den = decodeFe input.num) ∧
    (decodeFe input.den = 0 → decodeFe out = 0)

theorem soundness : Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [IsZeroFe.circuit, IsZeroFe.Assumptions, IsZeroFe.Spec,
    Mux.circuit, Mux.Assumptions, Mux.Spec,
    MulMod.circuit, MulMod.Assumptions, MulMod.Spec,
    Normalize.circuit, Normalize.Assumptions, Normalize.Spec,
    LessThan.circuit, LessThan.Assumptions, LessThan.Spec,
    Equal.circuit, Equal.Assumptions, Equal.Spec]
  obtain ⟨h_num_valid, h_den_valid⟩ := h_assumptions
  obtain ⟨hz, hden, hnum, hlam_norm, hlt, hmul, heq⟩ := h_holds
  simp only [secpParams_B] at hlam_norm hlt hmul heq
  specialize hz h_den_valid
  have hz_bool : IsBool (env.get (i₀ + 2 + 2 + 2 + 2 + 1 + 1)) := by
    rw [hz]
    split
    · exact IsBool.one
    · exact IsBool.zero
  specialize hden hz_bool
  specialize hnum hz_bool
  have hp_norm := pConst_normalized env
  have hp_val := pConst_value env
  have hlam_lt := hlt ⟨hlam_norm, hp_norm⟩
  rw [hp_val] at hlam_lt
  rw [hp_val] at hmul
  by_cases hd0 : decodeFe input_den = 0
  ·
    rw [if_pos hd0] at hz
    rw [hz, if_pos rfl, eval_oneConst] at hden
    rw [hz, if_pos rfl, eval_zeroConst] at hnum
    rw [hden, value_emuOfNat_one] at hmul
    rw [hnum, value_emuOfNat_zero] at heq
    obtain ⟨hprod_norm, hprod_val⟩ :=
      hmul ⟨hlam_norm, emuOfNat_normalized 1, hp_norm, hlam_lt, one_lt_P256, P256_pos⟩
    have hpn := heq ⟨hprod_norm, emuOfNat_normalized 0⟩
    rw [hpn, mul_one, Nat.mod_eq_of_lt hlam_lt] at hprod_val
    exact ⟨⟨hlam_norm, hlam_lt⟩, fun h => absurd hd0 h,
      fun _ => decodeFe_of_value_eq_zero hprod_val.symm⟩
  ·
    rw [if_neg hd0] at hz
    rw [hz, if_neg (zero_ne_one (α := F circomPrime))] at hden
    rw [hz, if_neg (zero_ne_one (α := F circomPrime))] at hnum
    rw [hden] at hmul
    rw [hnum] at heq
    obtain ⟨hprod_norm, hprod_val⟩ :=
      hmul ⟨hlam_norm, h_den_valid.1, hp_norm, hlam_lt, h_den_valid.2, P256_pos⟩
    have hpn := heq ⟨hprod_norm, h_num_valid.1⟩
    rw [hprod_val] at hpn
    refine ⟨⟨hlam_norm, hlam_lt⟩, fun _ => ?_, fun h => absurd h hd0⟩
    simp only [decodeFe]
    exact mul_cast_of_mod_eq hpn

theorem completeness : Completeness (F circomPrime) main Assumptions := by
  circuit_proof_start [IsZeroFe.circuit, IsZeroFe.Assumptions, IsZeroFe.Spec,
    Mux.circuit, Mux.Assumptions, Mux.Spec,
    MulMod.circuit, MulMod.Assumptions, MulMod.Spec,
    Normalize.circuit, Normalize.Assumptions, Normalize.Spec,
    LessThan.circuit, LessThan.Assumptions, LessThan.Spec,
    Equal.circuit, Equal.Assumptions, Equal.Spec]
  obtain ⟨h_num_valid, h_den_valid⟩ := h_assumptions
  obtain ⟨h_input_num, h_input_den⟩ := h_input
  obtain ⟨hz, hden, hnum, hlam, hmul⟩ := h_env
  simp only [secpParams_B] at hmul ⊢
  specialize hz h_den_valid
  have hz_bool : IsBool (env.get (i₀ + 2 + 2 + 2 + 2 + 1 + 1)) := by
    rw [hz]
    split
    · exact IsBool.one
    · exact IsBool.zero
  specialize hden hz_bool
  specialize hnum hz_bool

  have hev_num : evalEmu env input_var_num = BigInt.value limbBits input_num := by
    rw [evalEmu, BigInt.value, ← h_input_num]
  have hev_den : evalEmu env input_var_den = BigInt.value limbBits input_den := by
    rw [evalEmu, BigInt.value, ← h_input_den]
  have hlam_eval : Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange numLimbs fun i => var { index := i₀ + 11 + numLimbs + numLimbs + i })
      = emuOfNat (ZMod.val (((BigInt.value limbBits input_num : ℕ) : Specs.Secp256k1.Fp)
          * ((BigInt.value limbBits input_den : ℕ) : Specs.Secp256k1.Fp)⁻¹)) := by
    rw [← hev_num, ← hev_den]
    apply Vector.ext
    intro k hk
    have hentry : (Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange numLimbs fun i => var { index := i₀ + 11 + numLimbs + numLimbs + i }))[k]'hk
        = env.get (i₀ + 11 + numLimbs + numLimbs + k) := by
      simp [circuit_norm]
    rw [hentry]
    exact hlam ⟨k, hk⟩
  have hq_lt : ZMod.val (((BigInt.value limbBits input_num : ℕ) : Specs.Secp256k1.Fp)
      * ((BigInt.value limbBits input_den : ℕ) : Specs.Secp256k1.Fp)⁻¹) < P256 :=
    ZMod.val_lt _
  have hlam_norm : BigInt.Normalized limbBits (Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange numLimbs fun i => var { index := i₀ + 11 + numLimbs + numLimbs + i })) := by
    rw [hlam_eval]
    exact emuOfNat_normalized _
  have hlam_val : BigInt.value limbBits (Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange numLimbs fun i => var { index := i₀ + 11 + numLimbs + numLimbs + i }))
      = ZMod.val (((BigInt.value limbBits input_num : ℕ) : Specs.Secp256k1.Fp)
          * ((BigInt.value limbBits input_den : ℕ) : Specs.Secp256k1.Fp)⁻¹) := by
    rw [hlam_eval]
    exact value_emuOfNat (lt_trans hq_lt P256_lt)
  have hp_norm := pConst_normalized env.toEnvironment
  have hp_val := pConst_value env.toEnvironment
  rw [hp_val] at hmul ⊢
  rw [hlam_val] at hmul ⊢
  by_cases hd0 : decodeFe input_den = 0
  ·
    rw [if_pos hd0] at hz
    rw [hz, if_pos rfl, eval_oneConst] at hden
    rw [hz, if_pos rfl, eval_zeroConst] at hnum
    rw [hden, value_emuOfNat_one] at hmul ⊢
    rw [hnum, value_emuOfNat_zero] at *
    have hq0 : ZMod.val (((BigInt.value limbBits input_num : ℕ) : Specs.Secp256k1.Fp)
        * ((BigInt.value limbBits input_den : ℕ) : Specs.Secp256k1.Fp)⁻¹) = 0 := by
      simp only [decodeFe] at hd0
      rw [hd0]
      exact witness_val_den_zero _
    obtain ⟨hprod_norm, hprod_val⟩ :=
      hmul ⟨hlam_norm, emuOfNat_normalized 1, hp_norm, hq_lt, one_lt_P256, P256_pos⟩
    refine ⟨h_den_valid, hz_bool, hz_bool, hlam_norm, ⟨⟨hlam_norm, hp_norm⟩, hq_lt⟩,
      ⟨hlam_norm, emuOfNat_normalized 1, hp_norm, hq_lt, one_lt_P256, P256_pos⟩,
      ⟨hprod_norm, emuOfNat_normalized 0⟩, ?_⟩
    rw [hprod_val, hq0, Nat.zero_mul, Nat.zero_mod]
  ·
    rw [if_neg hd0] at hz
    rw [hz, if_neg (zero_ne_one (α := F circomPrime))] at hden
    rw [hz, if_neg (zero_ne_one (α := F circomPrime))] at hnum
    rw [hden] at hmul ⊢
    rw [hnum] at *
    have hcert : ZMod.val (((BigInt.value limbBits input_num : ℕ) : Specs.Secp256k1.Fp)
        * ((BigInt.value limbBits input_den : ℕ) : Specs.Secp256k1.Fp)⁻¹)
          * BigInt.value limbBits input_den % P256 = BigInt.value limbBits input_num := by
      simp only [decodeFe] at hd0
      exact witness_cert_nonzero h_num_valid.2 hd0
    obtain ⟨hprod_norm, hprod_val⟩ :=
      hmul ⟨hlam_norm, h_den_valid.1, hp_norm, hq_lt, h_den_valid.2, P256_pos⟩
    refine ⟨h_den_valid, hz_bool, hz_bool, hlam_norm, ⟨⟨hlam_norm, hp_norm⟩, hq_lt⟩,
      ⟨hlam_norm, h_den_valid.1, hp_norm, hq_lt, h_den_valid.2, P256_pos⟩,
      ⟨hprod_norm, h_num_valid.1⟩, ?_⟩
    rw [hprod_val, hcert]

def circuit : FormalCircuit (F circomPrime) Inputs Emu where
  main; elaborated; Assumptions; Spec; soundness; completeness

end DivOrZero
end Solution.Secp256k1ScalarMulFixedBase

end DonorFile0_17

-- Adapted donor module: ToBytesTheorems
section DonorFile0_18

namespace Solution.Secp256k1ScalarMulFixedBase
open Solution.Secp256k1ScalarMulFixedBase.Limbs

namespace ToBytes

theorem two_pow_64_lt_circomPrime : (2 : ℕ) ^ 64 < circomPrime := by decide

section
variable {p : ℕ} [Fact p.Prime]

theorem eval_foldl_add (env : Environment (F p)) (n : ℕ)
    (g : Fin n → Expression (F p)) :
    Expression.eval env (Fin.foldl n (fun acc i => acc + g i) 0)
      = ∑ i : Fin n, Expression.eval env (g i) := by
  induction n with
  | zero => simp [Expression.eval]
  | succ k ih =>
    simp [Fin.foldl_succ_last, Fin.sum_univ_castSucc, Expression.eval, ih]

theorem eval_row_iff (env : Environment (F p)) {n : ℕ}
    (g : Fin n → Expression (F p)) (e : Expression (F p)) :
    Expression.eval env (Fin.foldl n (fun acc i => acc + g i) 0 - e) = 0
      ↔ (∑ i : Fin n, Expression.eval env (g i)) = Expression.eval env e := by
  have hsub : Expression.eval env (Fin.foldl n (fun acc i => acc + g i) 0 - e)
      = Expression.eval env (Fin.foldl n (fun acc i => acc + g i) 0)
        - Expression.eval env e := by
    show Expression.eval env (Expression.add _ (Expression.mul (Expression.const (-1)) e)) = _
    simp only [Expression.eval]
    ring
  rw [hsub, sub_eq_zero, eval_foldl_add]

end

theorem byteSum_eq_limb (v k : ℕ) :
    (∑ t ∈ Finset.range 8, v / 2 ^ (8 * (8 * k + t)) % 256 * 2 ^ (8 * t))
      = v / 2 ^ (64 * k) % 2 ^ 64 := by
  have h : ∀ t, v / 2 ^ (8 * (8 * k + t)) = v / 2 ^ (64 * k) / 2 ^ (8 * t) := by
    intro t
    rw [Nat.div_div_eq_div_mul, ← pow_add]
    congr 1
    ring
  calc (∑ t ∈ Finset.range 8, v / 2 ^ (8 * (8 * k + t)) % 256 * 2 ^ (8 * t))
      = ∑ t ∈ Finset.range 8, v / 2 ^ (64 * k) / 2 ^ (8 * t) % 2 ^ 8 * 2 ^ (8 * t) := by
        apply Finset.sum_congr rfl
        intro t _
        rw [h t]
        norm_num
    _ = v / 2 ^ (64 * k) % 2 ^ (8 * 8) := limb_decomp_mod 8 8 (v / 2 ^ (64 * k))
    _ = v / 2 ^ (64 * k) % 2 ^ 64 := by norm_num

theorem sum_regroup (B n : ℕ) (f : ℕ → ℕ) : ∀ m : ℕ,
    (∑ i ∈ Finset.range (m * n), f i * 2 ^ (B * i))
      = ∑ k ∈ Finset.range m,
          (∑ t ∈ Finset.range n, f (n * k + t) * 2 ^ (B * t)) * 2 ^ (B * n * k) := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ← ih, show (m + 1) * n = m * n + n by ring,
      Finset.sum_range_add]
    congr 1
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro t _
    rw [show n * m + t = m * n + t by ring, mul_assoc, ← pow_add]
    congr 2
    ring

theorem value_limb_eq (x : Emu (F circomPrime)) (hx : x.Normalized limbBits)
    (k : Fin numLimbs) :
    x.value limbBits / 2 ^ (64 * k.val) % 2 ^ 64 = (x[k]).val := by
  rw [BigInt.value_eq_sum]
  have hstep : (∑ j : Fin numLimbs, (x[j]).val * 2 ^ (limbBits * j.val))
      = ∑ j ∈ Finset.range numLimbs,
          (if h : j < numLimbs then (x[j]'h).val else 0) * 2 ^ (64 * j) := by
    rw [← Fin.sum_univ_eq_sum_range
      (fun j => (if h : j < numLimbs then (x[j]'h).val else 0) * 2 ^ (64 * j))]
    apply Finset.sum_congr rfl
    intro j _
    rw [dif_pos j.isLt]
    rfl
  rw [hstep, digit_extract 64 (fun j => if h : j < numLimbs then (x[j]'h).val else 0)
    (by
      intro j
      dsimp only
      by_cases h : j < numLimbs
      · rw [dif_pos h]
        exact hx ⟨j, h⟩
      · rw [dif_neg h]
        exact Nat.two_pow_pos 64)
    numLimbs k.val k.isLt, dif_pos k.isLt]
  rw [Fin.getElem_fin]

theorem soundness_core (env : Environment (F circomPrime)) (i₀ : ℕ)
    (input : Emu (F circomPrime))
    (h_bytes : ∀ i : Fin coordBytes, (env.get (i₀ + i.val)).val < 2 ^ 8)
    (h_rows : ∀ k : Fin numLimbs,
      (∑ t : Fin bytesPerLimb,
          env.get (i₀ + (bytesPerLimb * k.val + t.val))
            * ((2 ^ (8 * t.val) : ℕ) : F circomPrime))
        = input[k.val]'k.isLt) :
    Limbs.fromLimbs 8 (List.map ZMod.val
        (Vector.map (Expression.eval env)
          (Vector.mapRange coordBytes fun i =>
            var (F := F circomPrime) { index := i₀ + i })).toList)
      = BigInt.value limbBits input := by

  have hval : Limbs.fromLimbs 8 (List.map ZMod.val
        (Vector.map (Expression.eval env)
          (Vector.mapRange coordBytes fun i =>
            var (F := F circomPrime) { index := i₀ + i })).toList)
      = BigInt.value 8 (Vector.map (Expression.eval env)
          (Vector.mapRange coordBytes fun i =>
            var (F := F circomPrime) { index := i₀ + i })) := rfl
  rw [hval, BigInt.value_eq_sum, BigInt.value_eq_sum]

  have hget : ∀ (i : ℕ) (h : i < coordBytes),
      (Vector.map (Expression.eval env)
        (Vector.mapRange coordBytes fun j =>
          var (F := F circomPrime) { index := i₀ + j }))[i] = env.get (i₀ + i) := by
    intro i h
    simp [circuit_norm]

  have hrow_nat : ∀ k : Fin numLimbs,
      (∑ t ∈ Finset.range 8, (env.get (i₀ + (8 * k.val + t))).val * 2 ^ (8 * t))
        = (input[k.val]'k.isLt).val := by
    intro k
    have hidx : ∀ t : Fin bytesPerLimb, 8 * k.val + t.val < coordBytes := by
      intro t
      have hk := k.isLt
      have ht := t.isLt
      simp only [numLimbs, bytesPerLimb, coordBytes] at hk ht ⊢
      omega

    have hcast : (∑ t : Fin bytesPerLimb,
          env.get (i₀ + (bytesPerLimb * k.val + t.val))
            * ((2 ^ (8 * t.val) : ℕ) : F circomPrime))
        = ((∑ t ∈ Finset.range 8,
            (env.get (i₀ + (8 * k.val + t))).val * 2 ^ (8 * t) : ℕ) : F circomPrime) := by
      rw [← Fin.sum_univ_eq_sum_range
        (fun t => (env.get (i₀ + (8 * k.val + t))).val * 2 ^ (8 * t)) 8, Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro t _
      rw [Nat.cast_mul, ZMod.natCast_zmod_val]

    have hlt : (∑ t ∈ Finset.range 8,
        (env.get (i₀ + (8 * k.val + t))).val * 2 ^ (8 * t)) < 2 ^ 64 := by
      have h := sum_lt_pow (B := 8) (n := 8)
        (fun t : Fin 8 => (env.get (i₀ + (8 * k.val + t.val))).val)
        (fun t => h_bytes ⟨8 * k.val + t.val, hidx t⟩)
      rw [← Fin.sum_univ_eq_sum_range
        (fun t => (env.get (i₀ + (8 * k.val + t))).val * 2 ^ (8 * t)) 8]
      calc (∑ t : Fin 8, (env.get (i₀ + (8 * k.val + t.val))).val * 2 ^ (8 * t.val))
          < 2 ^ (8 * 8) := h
        _ = 2 ^ 64 := by norm_num
    have h := h_rows k
    rw [hcast] at h
    rw [← h, ZMod.val_natCast_of_lt (lt_trans hlt two_pow_64_lt_circomPrime)]

  calc (∑ i : Fin coordBytes,
        ((Vector.map (Expression.eval env)
          (Vector.mapRange coordBytes fun j =>
            var (F := F circomPrime) { index := i₀ + j }))[i]).val * 2 ^ (8 * i.val))
      = ∑ i ∈ Finset.range (4 * 8), (env.get (i₀ + i)).val * 2 ^ (8 * i) := by
        rw [← Fin.sum_univ_eq_sum_range (fun i => (env.get (i₀ + i)).val * 2 ^ (8 * i)) 32]
        apply Finset.sum_congr rfl
        intro i _
        rw [Fin.getElem_fin, hget i.val i.isLt]
    _ = ∑ k ∈ Finset.range 4,
          (∑ t ∈ Finset.range 8, (env.get (i₀ + (8 * k + t))).val * 2 ^ (8 * t))
            * 2 ^ (8 * 8 * k) :=
        sum_regroup 8 8 (fun i => (env.get (i₀ + i)).val) 4
    _ = ∑ k : Fin numLimbs, (input[k]).val * 2 ^ (limbBits * k.val) := by
        rw [← Fin.sum_univ_eq_sum_range (fun k =>
          (∑ t ∈ Finset.range 8, (env.get (i₀ + (8 * k + t))).val * 2 ^ (8 * t))
            * 2 ^ (8 * 8 * k)) 4]
        apply Finset.sum_congr rfl
        intro k _
        rw [hrow_nat k, Fin.getElem_fin]

theorem completeness_core (input : Emu (F circomPrime))
    (h_norm : input.Normalized limbBits) (k : Fin numLimbs)
    (b : Fin bytesPerLimb → F circomPrime)
    (hb : ∀ t : Fin bytesPerLimb,
      b t = ((input.value limbBits / 2 ^ (8 * (bytesPerLimb * k.val + t.val)) % 256 : ℕ)
        : F circomPrime)) :
    (∑ t : Fin bytesPerLimb, b t * ((2 ^ (8 * t.val) : ℕ) : F circomPrime))
      = input[k.val]'k.isLt := by
  have hcast : (∑ t : Fin bytesPerLimb, b t * ((2 ^ (8 * t.val) : ℕ) : F circomPrime))
      = ((∑ t ∈ Finset.range 8,
          input.value limbBits / 2 ^ (8 * (8 * k.val + t)) % 256 * 2 ^ (8 * t) : ℕ)
        : F circomPrime) := by
    rw [← Fin.sum_univ_eq_sum_range
      (fun t => input.value limbBits / 2 ^ (8 * (8 * k.val + t)) % 256 * 2 ^ (8 * t)) 8,
      Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro t _
    rw [hb t]
    push_cast
    ring
  rw [hcast, byteSum_eq_limb, value_limb_eq input h_norm k, ZMod.natCast_zmod_val,
    Fin.getElem_fin]

end ToBytes

end Solution.Secp256k1ScalarMulFixedBase

end DonorFile0_18

-- Adapted donor module: ToBytes
section DonorFile0_19

namespace Solution.Secp256k1ScalarMulFixedBase
namespace ToBytes

def byteOfNat (v i : ℕ) : ℕ := v / 2 ^ (8 * i) % 256

def main (x : Var Emu (F circomPrime)) :
    Circuit (F circomPrime) (Var (fields coordBytes) (F circomPrime)) := do

  let bytes ← ProvableType.witness (α := fields coordBytes) fun env =>
    Vector.ofFn fun i : Fin coordBytes =>
      ((byteOfNat (evalEmu env x) i.val : ℕ) : F circomPrime)

  Circuit.forEach bytes (fun b => Gadgets.ToBits.rangeCheck 8 (by decide) b)

  let constraints := Vector.ofFn fun k : Fin numLimbs =>
    (Fin.foldl bytesPerLimb (fun acc t =>
      acc + bytes[bytesPerLimb * k.val + t.val]'(by
          have hk := k.isLt; have ht := t.isLt
          simp only [numLimbs, bytesPerLimb, coordBytes] at hk ht ⊢
          omega)
        * (((2 ^ (8 * t.val) : ℕ) : F circomPrime) : Expression (F circomPrime)))
      0)
    - x[k.val]'k.isLt
  Circuit.forEach constraints assertZero

  return bytes

instance elaborated : ElaboratedCircuit (F circomPrime) Emu (fields coordBytes) main := by
  elaborate_circuit

def Assumptions (x : Emu (F circomPrime)) : Prop :=
  x.Normalized limbBits

def Spec (x : Emu (F circomPrime)) (out : fields coordBytes (F circomPrime)) : Prop :=
  (∀ i : Fin coordBytes, (out[i]).val < 256) ∧
    Limbs.fromLimbs 8 (out.toList.map ZMod.val) = x.value limbBits

theorem soundness :
    Soundness (Input := Emu) (Output := fields coordBytes) (F circomPrime)
      main Assumptions Spec := by
  circuit_proof_start [Gadgets.ToBits.rangeCheck]
  obtain ⟨h_bytes, h_rows⟩ := h_holds
  refine ⟨fun i => lt_of_lt_of_eq (h_bytes i) (by norm_num), ?_⟩
  apply soundness_core env i₀ input h_bytes
  intro k
  have h := h_rows k
  simp only [Vector.getElem_ofFn] at h
  rw [eval_row_iff] at h
  rw [← h_input, Vector.getElem_map]
  exact h

theorem completeness :
    Completeness (Input := Emu) (Output := fields coordBytes) (F circomPrime)
      main Assumptions := by
  circuit_proof_start [Gadgets.ToBits.rangeCheck]
  obtain ⟨h_wit, -⟩ := h_env

  have hv : evalEmu env input_var = BigInt.value limbBits input := by
    rw [evalEmu, h_input]
    rfl

  have hbyte : ∀ i : Fin coordBytes,
      env.get (i₀ + i.val)
        = ((byteOfNat (BigInt.value limbBits input) i.val : ℕ) : F circomPrime) := by
    intro i
    rw [h_wit i]
    simp only [Vector.getElem_ofFn, hv]

  have hbyte_lt : ∀ v j : ℕ, byteOfNat v j < 2 ^ 8 :=
    fun v j => Nat.mod_lt _ (by norm_num)
  refine ⟨fun i => ?_, fun k => ?_⟩
  ·
    rw [hbyte i, ZMod.val_natCast_of_lt (lt_trans (hbyte_lt _ _)
      (lt_trans (by norm_num) two_pow_64_lt_circomPrime))]
    exact hbyte_lt _ _
  ·
    simp only [Vector.getElem_ofFn]
    rw [eval_row_iff]
    have hx : Expression.eval env.toEnvironment (input_var[k.val]'k.isLt)
        = input[k.val]'k.isLt := by
      rw [← h_input, Vector.getElem_map]
    rw [hx]
    show (∑ t : Fin bytesPerLimb,
        env.get (i₀ + (bytesPerLimb * k.val + t.val))
          * ((2 ^ (8 * t.val) : ℕ) : F circomPrime))
      = input[k.val]'k.isLt
    apply completeness_core input h_assumptions k
    intro t
    have hidx : bytesPerLimb * k.val + t.val < coordBytes := by
      have hk := k.isLt
      have ht := t.isLt
      simp only [numLimbs, bytesPerLimb, coordBytes] at hk ht ⊢
      omega
    rw [hbyte ⟨bytesPerLimb * k.val + t.val, hidx⟩]
    simp only [byteOfNat]

def circuit : FormalCircuit (F circomPrime) Emu (fields coordBytes) where
  main; elaborated; Assumptions; Spec; soundness; completeness

end ToBytes
end Solution.Secp256k1ScalarMulFixedBase

end DonorFile0_19

-- Adapted donor module: Cost
section DonorFile0_20

namespace Solution.Secp256k1ScalarMulFixedBase
namespace Cost

open Challenge.CostR1CS

theorem CostIs.provableWitness {α : TypeMap} [ProvableType α]
    (compute : ProverEnvironment (F circomPrime) → α (F circomPrime)) :
    CostIs (ProvableType.witness (α := α) compute) ⟨size α, 0⟩ := by
  intro n; rfl

theorem IsR1CSCirc.provableWitness {α : TypeMap} [ProvableType α]
    (compute : ProverEnvironment (F circomPrime) → α (F circomPrime)) :
    IsR1CSCirc (ProvableType.witness (α := α) compute) := by
  intro n; trivial

theorem affineProvable_provableWitness {α : TypeMap} [ProvableType α]
    (compute : ProverEnvironment (F circomPrime) → α (F circomPrime)) (n : ℕ) :
    AffineProvable ((ProvableType.witness (α := α) compute).output n) := by
  rw [show ((ProvableType.witness (α := α) compute).output n)
        = varFromOffset α n from rfl]
  exact affineProvable_varFromOffset n

theorem CostIs.subcircuitWithAssertion {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    {circuit : GeneralFormalCircuit (F circomPrime) Input Output}
    {b : Var Input (F circomPrime)} {K : Count}
    (h : ∀ n, operationCount ((circuit.main b).operations n) = K) :
    CostIs (subcircuitWithAssertion circuit b) K := by
  intro n
  show operationCount [Operation.subcircuit (circuit.toSubcircuit n b)] = K
  have hz : operationCount [Operation.subcircuit (circuit.toSubcircuit n b)]
      = nestedCount (circuit.toSubcircuit n b).ops := by
    show nestedCount _ + operationCount ([] : Operations (F circomPrime)) = nestedCount _
    rw [show operationCount ([] : Operations (F circomPrime)) = Count.zero from rfl, Count.add_zero]
  rw [hz]
  show nestedCount (NestedOperations.nested ⟨circuit.name, ((circuit.main b).operations n).toNested⟩) = K
  rw [show nestedCount (NestedOperations.nested ⟨circuit.name, ((circuit.main b).operations n).toNested⟩)
        = nestedListCount ((circuit.main b).operations n).toNested from rfl,
      Lemmas.operationCount_toNested]
  exact h n

theorem IsR1CSCirc.subcircuitWithAssertion {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    {circuit : GeneralFormalCircuit (F circomPrime) Input Output}
    {b : Var Input (F circomPrime)}
    (h : ∀ n, operationsIsR1CS ((circuit.main b).operations n)) :
    IsR1CSCirc (subcircuitWithAssertion circuit b) := by
  intro n
  show operationsIsR1CS [Operation.subcircuit (circuit.toSubcircuit n b)]
  refine ⟨?_, trivial⟩
  show flatOperationsIsR1CS (circuit.toSubcircuit n b).ops.toFlat
  have hofl : (circuit.toSubcircuit n b).ops.toFlat = ((circuit.main b).operations n).toFlat := by
    show (NestedOperations.nested ⟨circuit.name, ((circuit.main b).operations n).toNested⟩).toFlat = _
    rw [Operations.toNested_toFlat]
  rw [hofl]
  exact (Lemmas.operationsIsR1CS_iff_toFlat _).mp (h n)

theorem costIs_toBits (n : ℕ) (x : Expression (F circomPrime)) :
    CostIs (Gadgets.ToBits.main n x) ⟨n, n + 1⟩ := by
  unfold Gadgets.ToBits.main
  have hcount : (⟨n, 0⟩ + (⟨n * 0, n * 1⟩ + (⟨0, 1⟩ + Count.zero)) : Count) = ⟨n, n + 1⟩ := by
    show (⟨_, _⟩ : Count) = _; congr 1; simp [Count.zero]
  rw [← hcount]
  refine CostIs.bind (CostIs.witnessVector (F := F circomPrime) n _) fun bits => ?_
  refine CostIs.bind
    (show CostIs (Circuit.forEach bits (fun input => assertion assertBool input) _) ⟨n * 0, n * 1⟩ from
      CostIs.forEach fun (a : Expression (F circomPrime)) m =>
        (CostIs.assertion (circuit := assertBool) (b := a) (K := ⟨0, 1⟩) (fun k => rfl)) m) fun _ => ?_
  refine CostIs.bind
    (show CostIs (x === Utils.Bits.fieldFromBitsExpr bits) ⟨0, 1⟩ from ?_) fun _ => CostIs.pure _
  show CostIs (Expression.assertEquals x (Utils.Bits.fieldFromBitsExpr bits)) ⟨0, 1⟩
  unfold Expression.assertEquals
  refine CostIs.assertion (K := ⟨0, 1⟩) fun m => ?_
  show operationCount ((Gadgets.Equality.main (M := id) (x, Utils.Bits.fieldFromBitsExpr bits)).operations m) = _
  unfold Gadgets.Equality.main
  simpa using (CostIs.forEach (m := 1) (fun a k => CostIs.assertZero _ k) m)

theorem IsR1CSCirc.forEach_mem {α : Type} {m : ℕ} [Inhabited α] {xs : Vector α m}
    {body : α → Circuit (F circomPrime) Unit}
    {constant : Circuit.ConstantLength body}
    (h : ∀ (i : Fin m) n, operationsIsR1CS ((body xs[i.val]).operations n)) :
    IsR1CSCirc (Circuit.forEach xs body constant) := by
  intro n
  rw [Circuit.forEach.operations_eq]
  exact operationsIsR1CS_flatten_ofFn _ (fun i => h i _)

attribute [local irreducible] isR1CSRow r1csProducts operationsIsR1CS flatOperationsIsR1CS

theorem affine_fieldFromBitsExpr {n : ℕ} (bits : Var (fields n) (F circomPrime))
    (h : AffineW bits) : Affine (Utils.Bits.fieldFromBitsExpr bits) := by
  unfold Utils.Bits.fieldFromBitsExpr
  apply affine_finFoldl'
  · exact Affine.zero
  · intro acc i hacc
    exact Affine.add hacc (Affine.mul_fconst _ (h i.val i.isLt))

theorem isR1CS_toBits (n : ℕ) (x : Expression (F circomPrime)) (hx : Affine x) :
    IsR1CSCirc (Gadgets.ToBits.main n x) := by
  unfold Gadgets.ToBits.main
  refine IsR1CSCirc.bind_out (IsR1CSCirc.witnessVector n _) fun w => ?_
  refine IsR1CSCirc.bind ?_ fun _ => ?_
  · refine IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) fun i k => ?_
    refine (IsR1CSCirc.assertion (circuit := assertBool) fun j => ?_) k
    refine IsR1CSCirc.assertZero ?_ j
    show isR1CSRow (_ * (_ - 1))
    exact isR1CSRow_mul (affineW_witnessVector_output n _ w i.val i.isLt)
      (Affine.sub (affineW_witnessVector_output n _ w i.val i.isLt) (Affine.const 1))
  · show IsR1CSCirc (x === Utils.Bits.fieldFromBitsExpr _)
    show IsR1CSCirc (Expression.assertEquals x (Utils.Bits.fieldFromBitsExpr _))
    unfold Expression.assertEquals
    refine IsR1CSCirc.assertion (circuit := Gadgets.Equality.circuit id) fun k => ?_
    show operationsIsR1CS ((Gadgets.Equality.main (M := id)
      (x, Utils.Bits.fieldFromBitsExpr ((Circuit.witnessVector n _).output w))).operations k)
    unfold Gadgets.Equality.main
    refine (IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) (m := 1) fun i j => ?_) k
    refine IsR1CSCirc.assertZero ?_ j
    simp only [circuit_norm, Vector.getElem_map, Vector.getElem_zip]
    exact isR1CSRow_of_affine (Affine.sub hx
      (affine_fieldFromBitsExpr (Vector.mapRange n fun i => Expression.var { index := w + i })
        (affineW_mapRange_var _)))

theorem costIs_toBits_sub (n : ℕ) (hn : (2 : ℕ) ^ n < circomPrime) (x : Expression (F circomPrime)) :
    CostIs (Gadgets.ToBits.toBits n hn x) ⟨n, n + 1⟩ :=
  CostIs.subcircuitWithAssertion (fun m => costIs_toBits n x m)

theorem isR1CS_toBits_sub (n : ℕ) (hn : (2 : ℕ) ^ n < circomPrime)
    (x : Expression (F circomPrime)) (hx : Affine x) :
    IsR1CSCirc (Gadgets.ToBits.toBits n hn x) :=
  IsR1CSCirc.subcircuitWithAssertion (fun m => isR1CS_toBits n x hx m)

theorem costIs_rangeCheck (n : ℕ) (hn : (2 : ℕ) ^ n < circomPrime) (x : Expression (F circomPrime)) :
    CostIs ((Gadgets.ToBits.rangeCheck n hn).main x) ⟨n, n + 1⟩ := by
  show CostIs (Gadgets.ToBits.toBits n hn x >>= fun _ => pure ()) ⟨n, n + 1⟩
  have := CostIs.bind (costIs_toBits_sub n hn x) (fun _ => CostIs.pure ())
  simpa [Count.add_zero] using this

theorem isR1CS_rangeCheck (n : ℕ) (hn : (2 : ℕ) ^ n < circomPrime)
    (x : Expression (F circomPrime)) (hx : Affine x) :
    IsR1CSCirc ((Gadgets.ToBits.rangeCheck n hn).main x) := by
  show IsR1CSCirc (Gadgets.ToBits.toBits n hn x >>= fun _ => pure ())
  exact IsR1CSCirc.bind (isR1CS_toBits_sub n hn x hx) (fun _ => IsR1CSCirc.pure ())

theorem isR1CS_assertion_rangeCheck (n : ℕ) (hn : (2 : ℕ) ^ n < circomPrime)
    (x : Expression (F circomPrime)) (hx : Affine x) :
    IsR1CSCirc (assertion (Gadgets.ToBits.rangeCheck n hn) x) :=
  IsR1CSCirc.assertion (fun m => isR1CS_rangeCheck n hn x hx m)

variable {m : ℕ}

theorem isR1CS_normalize (P : BigIntParams circomPrime m)
    (x : Var (BigInt m) (F circomPrime)) (hx : AffineW x) :
    IsR1CSCirc (Normalize.main P x) := by
  unfold Normalize.main
  exact IsR1CSCirc.forEach_mem (α := Expression (F circomPrime))
    fun i n => isR1CS_assertion_rangeCheck P.B P.hB x[i.val] (hx i.val i.isLt) n

theorem isR1CS_assertion_normalize (P : BigIntParams circomPrime m)
    (x : Var (BigInt m) (F circomPrime)) (hx : AffineW x) :
    IsR1CSCirc (assertion (Normalize.circuit P) x) :=
  IsR1CSCirc.assertion (fun n => isR1CS_normalize P x hx n)

theorem affineW_provableWitness_bigInt {k : ℕ}
    (compute : ProverEnvironment (F circomPrime) → BigInt k (F circomPrime)) (nd : ℕ) :
    AffineW ((ProvableType.witness (α := BigInt k) compute).output nd :
      Var (BigInt k) (F circomPrime)) := by
  rw [show ((ProvableType.witness (α := BigInt k) compute).output nd : Var (BigInt k) (F circomPrime))
        = varFromOffset (BigInt k) nd from rfl]
  exact affineW_varFromOffset _ _

theorem isR1CS_provableWitness_bigInt {k : ℕ}
    (compute : ProverEnvironment (F circomPrime) → BigInt k (F circomPrime)) :
    IsR1CSCirc (ProvableType.witness (α := BigInt k) compute) :=
  IsR1CSCirc.provableWitness _

theorem isR1CS_witnessVec (k : ℕ) (c : ProverEnvironment (F circomPrime) → Vector (F circomPrime) k) :
    IsR1CSCirc (Circuit.witnessVector k c) := IsR1CSCirc.witnessVector k c

theorem isR1CSRow_mul_sub {A B C : Expression (F circomPrime)}
    (hA : Affine A) (hB : Affine B) (hC : Affine C) : isR1CSRow (A * B - C) := by
  rcases r1csProducts_mul_affine hA hB with h | h
  · exact isR1CSRow_of_r1csProducts (k := 0)
      (by show r1csProducts (A * B + -C) = some 0
          rw [r1csProducts_add, r1csProducts_neg, r1csProducts_of_affine hC, h]) (by omega)
  · exact isR1CSRow_of_r1csProducts (k := 1)
      (by show r1csProducts (A * B + -C) = some 1
          rw [r1csProducts_add, r1csProducts_neg, r1csProducts_of_affine hC, h]) (by omega)

theorem affineW_bigIntMulVars [NeZero m] (pp : Vector (Expression (F circomPrime)) (m * m))
    (hpp : ∀ t (ht : t < m * m), Affine pp[t]) :
    AffineW (bigIntMulVars pp) := by
  intro k hk
  simp only [bigIntMulVars]
  rw [Vector.getElem_mapFinRange, vector_foldl_finRange]
  refine affine_finFoldl' _ _ Affine.zero fun acc i hacc => ?_
  split
  · exact Affine.add hacc (hpp _ _)
  · exact hacc

theorem affineW_witnessedMul_output [NeZero m] (a b : Var (BigInt m) (F circomPrime)) (off : ℕ) :
    AffineW ((MulMod.witnessedMul a b).output off) := by
  rw [show (MulMod.witnessedMul a b).output off
        = bigIntMulVars (Vector.mapRange (m * m) fun i => var (F := F circomPrime) { index := off + i })
      from MulMod.witnessedMul_output off a b]
  refine affineW_bigIntMulVars _ fun t ht => ?_
  rw [Vector.getElem_mapRange]; exact Affine.var _

theorem isR1CS_witnessedMul [NeZero m] (a b : Var (BigInt m) (F circomPrime))
    (ha : AffineW a) (hb : AffineW b) :
    IsR1CSCirc (MulMod.witnessedMul a b) := by
  unfold MulMod.witnessedMul
  refine IsR1CSCirc.bind_out (IsR1CSCirc.provableWitness _) fun npp => ?_
  refine IsR1CSCirc.bind ?_ fun _ => ?_
  · refine IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) fun t k => ?_
    refine IsR1CSCirc.assertZero ?_ k
    rw [Vector.getElem_mapFinRange]
    exact isR1CSRow_mul_sub (ha _ (Nat.div_lt_of_lt_mul t.isLt))
      (hb _ (Nat.mod_lt _ (Nat.pos_of_neZero m)))
      (affineW_provableWitness_bigInt (k := m * m) _ npp t.val t.isLt)
  exact IsR1CSCirc.pure _

theorem count_eq (a c : ℕ) {x : Count} (ha : x.allocations = a) (hc : x.constraints = c) :
    (⟨a, c⟩ : Count) = x := by
  cases x; cases ha; cases hc; rfl

theorem isR1CSRow_mul_add_sub {A B C D : Expression (F circomPrime)}
    (hA : Affine A) (hB : Affine B) (hC : Affine C) (hD : Affine D) :
    isR1CSRow (A * B + C - D) := by
  rcases r1csProducts_mul_affine hA hB with h | h
  · refine isR1CSRow_of_r1csProducts (k := 0) ?_ (by omega)
    show r1csProducts (A * B + C + -D) = some 0
    rw [r1csProducts_add, r1csProducts_add, r1csProducts_neg, h,
        r1csProducts_of_affine hC, r1csProducts_of_affine hD]
  · refine isR1CSRow_of_r1csProducts (k := 1) ?_ (by omega)
    show r1csProducts (A * B + C + -D) = some 1
    rw [r1csProducts_add, r1csProducts_add, r1csProducts_neg, h,
        r1csProducts_of_affine hC, r1csProducts_of_affine hD]

theorem costIs_assertEqField (x y : Expression (F circomPrime)) :
    CostIs (x === y) ⟨0, 1⟩ := by
  show CostIs (Expression.assertEquals x y) ⟨0, 1⟩
  unfold Expression.assertEquals
  refine CostIs.assertion (K := ⟨0, 1⟩) fun m => ?_
  show operationCount ((Gadgets.Equality.main (M := id) (x, y)).operations m) = _
  unfold Gadgets.Equality.main
  simpa using (CostIs.forEach (m := 1) (fun a k => CostIs.assertZero _ k) m)

theorem isR1CS_assertEqField {x y : Expression (F circomPrime)}
    (h : isR1CSRow (x - y)) : IsR1CSCirc (x === y) := by
  show IsR1CSCirc (Expression.assertEquals x y)
  unfold Expression.assertEquals
  refine IsR1CSCirc.assertion (circuit := Gadgets.Equality.circuit id) fun k => ?_
  show operationsIsR1CS ((Gadgets.Equality.main (M := id) (x, y)).operations k)
  unfold Gadgets.Equality.main
  refine (IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) (m := 1) fun i j => ?_) k
  refine IsR1CSCirc.assertZero ?_ j
  simp only [circuit_norm, Vector.getElem_map, Vector.getElem_zip]
  exact h

theorem costIs_assignEqField (rhs : Expression (F circomPrime)) :
    CostIs (HasAssignEq.assignEq (F := F circomPrime) rhs) ⟨1, 1⟩ := by
  rw [show (⟨1, 1⟩ : Count) = ⟨1, 0⟩ + (⟨0, 1⟩ + Count.zero) from by decide]
  exact CostIs.bind (CostIs.witnessField _) fun w =>
    CostIs.bind (costIs_assertEqField _ rhs) fun _ => CostIs.pure _

theorem isR1CS_assignEqField (rhs : Expression (F circomPrime))
    (h : ∀ w : Variable (F circomPrime), isR1CSRow (Expression.var w - rhs)) :
    IsR1CSCirc (HasAssignEq.assignEq (F := F circomPrime) rhs) := by
  refine IsR1CSCirc.bind_out (IsR1CSCirc.witnessField _) fun k => ?_
  exact IsR1CSCirc.bind (isR1CS_assertEqField (h ⟨k⟩)) fun _ => IsR1CSCirc.pure _

theorem affine_assignEq_output (rhs : Expression (F circomPrime)) (n : ℕ) :
    Affine ((HasAssignEq.assignEq (F := F circomPrime) rhs).output n) := Affine.var _

theorem isR1CS_assertEqFieldM {x y : Var field (F circomPrime)}
    (h : isR1CSRow (x - y)) : IsR1CSCirc (x === y) := by
  show IsR1CSCirc (assertEquals (M := field) x y)
  unfold assertEquals
  refine IsR1CSCirc.assertion (circuit := Gadgets.Equality.circuit field) fun k => ?_
  show operationsIsR1CS ((Gadgets.Equality.main (M := field) (x, y)).operations k)
  unfold Gadgets.Equality.main
  refine (IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) (m := 1) fun i j => ?_) k
  refine IsR1CSCirc.assertZero ?_ j
  simp only [circuit_norm, Vector.getElem_map, Vector.getElem_zip]
  exact h

theorem isR1CS_assignEqFieldM (rhs : Var field (F circomPrime))
    (h : ∀ w : Variable (F circomPrime), isR1CSRow (Expression.var w - rhs)) :
    IsR1CSCirc (HasAssignEq.assignEq (β := field (Expression (F circomPrime))) rhs) := by
  refine IsR1CSCirc.bind_out (IsR1CSCirc.provableWitness (α := field) _) fun k => ?_
  exact IsR1CSCirc.bind (isR1CS_assertEqFieldM (h ⟨k⟩)) fun _ => IsR1CSCirc.pure _

theorem affine_assignEqFieldM_output (rhs : Var field (F circomPrime)) (n : ℕ) :
    Affine ((HasAssignEq.assignEq (β := field (Expression (F circomPrime))) rhs).output n) :=
  Affine.var _

theorem costIs_mux {M : TypeMap} [ProvableType M]
    (input : Var (Mux.Inputs M) (F circomPrime)) :
    CostIs (Mux.main input) ⟨size M, size M⟩ := by
  obtain ⟨sel, t, f⟩ := input
  rw [show (⟨size M, size M⟩ : Count)
        = ⟨size M, 0⟩ + (⟨size M * 0, size M * 1⟩ + Count.zero) from
      count_eq _ _ (by simp only [Count.add_allocations, Count.zero]; omega)
        (by simp only [Count.add_constraints, Count.zero]; omega)]
  unfold Mux.main
  refine CostIs.bind (CostIs.provableWitness _) fun out => ?_
  refine CostIs.bind (CostIs.forEach fun a n => CostIs.assertZero _ n) fun _ => ?_
  exact CostIs.pure _

theorem isR1CS_mux {M : TypeMap} [ProvableType M]
    (input : Var (Mux.Inputs M) (F circomPrime))
    (hsel : Affine input.selector)
    (ht : AffineProvable input.ifTrue) (hf : AffineProvable input.ifFalse) :
    IsR1CSCirc (Mux.main input) := by
  obtain ⟨sel, t, f⟩ := input
  unfold Mux.main
  refine IsR1CSCirc.bind_out (IsR1CSCirc.provableWitness _) fun nout => ?_
  refine IsR1CSCirc.bind ?_ fun _ => IsR1CSCirc.pure _
  refine IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) fun i k => ?_
  refine IsR1CSCirc.assertZero ?_ k
  rw [Vector.getElem_ofFn]
  exact isR1CSRow_mul_add_sub hsel
    (Affine.sub (ht i.val i.isLt) (hf i.val i.isLt)) (hf i.val i.isLt)
    (affineProvable_provableWitness _ nout i.val i.isLt)

theorem costIs_sub_mux {M : TypeMap} [ProvableType M]
    (b : Var (Mux.Inputs M) (F circomPrime)) :
    CostIs (subcircuit (Mux.circuit (M := M)) b) ⟨size M, size M⟩ :=
  CostIs.subcircuit (fun n => costIs_mux b n)

theorem isR1CS_sub_mux {M : TypeMap} [ProvableType M]
    (b : Var (Mux.Inputs M) (F circomPrime))
    (hsel : Affine b.selector)
    (ht : AffineProvable b.ifTrue) (hf : AffineProvable b.ifFalse) :
    IsR1CSCirc (subcircuit (Mux.circuit (M := M)) b) :=
  IsR1CSCirc.subcircuit (fun n => isR1CS_mux b hsel ht hf n)

theorem affineProvable_sub_mux {M : TypeMap} [ProvableType M]
    (b : Var (Mux.Inputs M) (F circomPrime)) (n : ℕ) :
    AffineProvable ((subcircuit (Mux.circuit (M := M)) b).output n) := by
  have h : (subcircuit (Mux.circuit (M := M)) b).output n = varFromOffset M n := by
    simp only [circuit_norm, subcircuit, Mux.circuit, Mux.elaborated]
  rw [h]
  exact affineProvable_varFromOffset n

theorem affineW_emuConst (v : ℕ) : AffineW (emuConst v : Var Emu (F circomPrime)) := by
  intro i hi
  unfold emuConst
  rw [Vector.getElem_ofFn]
  exact Affine.const _

theorem affine_provableWitness_field
    (c : ProverEnvironment (F circomPrime) → field (F circomPrime)) (n : ℕ) :
    Affine ((ProvableType.witness (α := field) c).output n) := Affine.var _

def AffineFP (v : Var FlaggedPoint (F circomPrime)) : Prop :=
  AffineW v.x ∧ AffineW v.y ∧ Affine v.isInf

theorem AffineFP.of_affineProvable {v : Var FlaggedPoint (F circomPrime)}
    (h : AffineProvable v) : AffineFP v := by
  have hflat : AffineW
      (v.x ++ (v.y ++ #v[v.isInf]) :
        fields (numLimbs + (numLimbs + 1)) (Expression (F circomPrime))) := by
    intro i hi
    simpa [AffineProvable, circuit_norm, explicit_provable_type] using h i (by exact hi)
  refine ⟨AffineW.left_of_append hflat,
    AffineW.left_of_append (AffineW.right_of_append hflat), ?_⟩
  have h1 := AffineW.right_of_append (AffineW.right_of_append hflat) 0 (by decide)
  simpa using h1

theorem AffineW.append {m n : ℕ}
    {a : fields m (Expression (F circomPrime))} {b : fields n (Expression (F circomPrime))}
    (ha : AffineW a) (hb : AffineW b) :
    AffineW (a ++ b : fields (m + n) (Expression (F circomPrime))) := by
  intro i hi
  rw [Vector.getElem_append]
  split
  · exact ha _ _
  · exact hb _ _

theorem affineW_singleton {e : Expression (F circomPrime)} (he : Affine e) :
    AffineW (#v[e] : fields 1 (Expression (F circomPrime))) := by
  intro i hi
  have h0 : i = 0 := by omega
  subst h0
  simpa using he

theorem AffineFP.affineProvable {v : Var FlaggedPoint (F circomPrime)}
    (h : AffineFP v) : AffineProvable v := by
  obtain ⟨hx, hy, hi⟩ := h
  intro j hj
  simp only [circuit_norm, explicit_provable_type]
  exact AffineW.append hx (AffineW.append hy (affineW_singleton hi)) j hj

theorem IsR1CSCirc.bind_out_inv {α β : Type} {f : Circuit (F circomPrime) α}
    {g : α → Circuit (F circomPrime) β} (P : α → Prop)
    (hf : IsR1CSCirc f)
    (hout : ∀ n, P (f.output n))
    (hg : ∀ a, P a → IsR1CSCirc (g a)) :
    IsR1CSCirc (f >>= g) := by
  intro n
  rw [Circuit.bind_operations_eq, Lemmas.operationsIsR1CS_append]
  exact ⟨hf n, hg _ (hout _) _⟩

open Challenge.Instances.Secp256k1ScalarMulFixedBase in

theorem affineInput_components (input : Var Interface.Input (F circomPrime))
    (hinput : AffineProvable input) :
    AffineW input.bits := by
  have hflat : AffineW
      (input.bits ++ (#v[] : Vector (Expression (F circomPrime)) 0) :
        fields (Interface.scalarBits + 0) (Expression (F circomPrime))) := by
    intro i hi
    simpa [AffineProvable, circuit_norm, explicit_provable_type] using hinput i (by exact hi)
  exact AffineW.left_of_append hflat

open Challenge.Instances.Secp256k1ScalarMulFixedBase in

theorem affineProvable_interfaceOutput {v : Var Interface.Output (F circomPrime)}
    (hx : AffineW v.x) (hy : AffineW v.y) (hi : Affine v.isInf) :
    AffineProvable v := by
  intro j hj
  simp only [circuit_norm, explicit_provable_type]
  exact AffineW.append hx (AffineW.append hy (affineW_singleton hi)) j hj

end Cost

namespace CompactAdd

open Challenge.CostR1CS
open Cost

attribute [local irreducible] isR1CSRow r1csProducts operationsIsR1CS flatOperationsIsR1CS

theorem isR1CSRow_sub_sub_mul {w C A B : Expression (F circomPrime)}
    (hw : Affine w) (hC : Affine C) (hA : Affine A) (hB : Affine B) :
    isR1CSRow (w - (C - A * B)) := by
  rcases r1csProducts_mul_affine hA hB with h | h
  · refine isR1CSRow_of_r1csProducts (k := 0) ?_ (by omega)
    show r1csProducts (w + -(C + -(A * B))) = some 0
    rw [r1csProducts_add, r1csProducts_neg, r1csProducts_add, r1csProducts_neg, h,
        r1csProducts_of_affine hw, r1csProducts_of_affine hC]
  · refine isR1CSRow_of_r1csProducts (k := 1) ?_ (by omega)
    show r1csProducts (w + -(C + -(A * B))) = some 1
    rw [r1csProducts_add, r1csProducts_neg, r1csProducts_add, r1csProducts_neg, h,
        r1csProducts_of_affine hw, r1csProducts_of_affine hC]

theorem isR1CSRow_sub_mul_sub {C A B D : Expression (F circomPrime)}
    (hC : Affine C) (hA : Affine A) (hB : Affine B) (hD : Affine D) :
    isR1CSRow (C - A * B - D) := by
  rcases r1csProducts_mul_affine hA hB with h | h
  · refine isR1CSRow_of_r1csProducts (k := 0) ?_ (by omega)
    show r1csProducts (C + -(A * B) + -D) = some 0
    rw [r1csProducts_add, r1csProducts_add, r1csProducts_neg, r1csProducts_neg, h,
        r1csProducts_of_affine hC, r1csProducts_of_affine hD]
  · refine isR1CSRow_of_r1csProducts (k := 1) ?_ (by omega)
    show r1csProducts (C + -(A * B) + -D) = some 1
    rw [r1csProducts_add, r1csProducts_add, r1csProducts_neg, r1csProducts_neg, h,
        r1csProducts_of_affine hC, r1csProducts_of_affine hD]

theorem isR1CSRow_add_mul_sub {C A B D : Expression (F circomPrime)}
    (hC : Affine C) (hA : Affine A) (hB : Affine B) (hD : Affine D) :
    isR1CSRow (C + A * B - D) := by
  rcases r1csProducts_mul_affine hA hB with h | h
  · refine isR1CSRow_of_r1csProducts (k := 0) ?_ (by omega)
    show r1csProducts (C + A * B + -D) = some 0
    rw [r1csProducts_add, r1csProducts_add, r1csProducts_neg, h,
        r1csProducts_of_affine hC, r1csProducts_of_affine hD]
  · refine isR1CSRow_of_r1csProducts (k := 1) ?_ (by omega)
    show r1csProducts (C + A * B + -D) = some 1
    rw [r1csProducts_add, r1csProducts_add, r1csProducts_neg, h,
        r1csProducts_of_affine hC, r1csProducts_of_affine hD]

end CompactAdd
end Solution.Secp256k1ScalarMulFixedBase

end DonorFile0_20

-- Adapted donor module: EqViaCarriesFlex
section DonorFile0_21

namespace Solution.Secp256k1ScalarMulFixedBase
open Solution.Secp256k1ScalarMulFixedBase.Limbs

section
variable {p : ℕ} [Fact p.Prime]
variable {n : ℕ} [NeZero n]

namespace EqViaCarriesFlex

def boundAt {n : ℕ} (M : Vector ℕ n) (j : ℕ) : ℕ :=
  if h : j < n then M[j] else 0

structure FlexParams (p n : ℕ) where

  B : ℕ

  W : ℕ

  M : Vector ℕ n

  hB : 2 ^ B < p

  hW : 2 ^ W < p

  hB1 : 1 ≤ B

  hW1 : 1 ≤ W

  hcarry : ∀ k : Fin n,
    (∑ j ∈ Finset.range (k.val + 1), boundAt M j * 2 ^ (B * j))
      ≤ 2 ^ (W - 1) * 2 ^ (B * (k.val + 1))

  hlift : ∀ k : Fin n, boundAt M k.val + 2 ^ W + 2 ^ W * 2 ^ B < p

@[reducible] def Coeffs (n : ℕ) : TypeMap := fields n

structure Inputs (n : ℕ) (F : Type) where
  lhs : Coeffs n F
  rhs : Coeffs n F
deriving ProvableStruct

def main (P : FlexParams p n) [Fact (p > 2)] (input : Var (Inputs n) (F p)) :
    Circuit (F p) Unit := do
  let Pc := input.lhs
  let Sc := input.rhs

  let carry ← witnessVector n fun env =>
    Vector.ofFn fun k : Fin n =>
      ((2 ^ (P.W - 1) + evalPartial P.B env Pc k.val / 2 ^ (P.B * (k.val + 1))
          - evalPartial P.B env Sc k.val / 2 ^ (P.B * (k.val + 1)) : ℕ) : F p)

  Circuit.forEach carry (fun c => Gadgets.ToBits.rangeCheck P.W P.hW c)

  let constraints : Vector (Expression (F p)) n :=
    Vector.mapFinRange n fun k =>
      let carryIn : Expression (F p) :=
        if h : k.val = 0 then 0
        else carry[k.val - 1]'(by omega) - ((2 ^ (P.W - 1) : ℕ) : F p)
      Pc[k.val] + carryIn - Sc[k.val]
        - (carry[k.val] - ((2 ^ (P.W - 1) : ℕ) : F p)) * (2 ^ P.B : F p)
  Circuit.forEach constraints assertZero

  if h : n = 0 then pure () else
    assertZero (carry[n - 1]'(by omega) - ((2 ^ (P.W - 1) : ℕ) : F p))

instance elaborated (P : FlexParams p n) [Fact (p > 2)] :
    ElaboratedCircuit (F p) (Inputs n) unit (main P) where
  localLength _ := n * P.W + n
  localLength_eq := by
    intro input offset
    simp only [main, circuit_norm, Gadgets.ToBits.rangeCheck]
    split <;> simp +arith [circuit_norm]
  subcircuitsConsistent := by
    intro input offset
    simp +arith only [main, circuit_norm, Gadgets.ToBits.rangeCheck]
    split <;> simp +arith [circuit_norm]
  channelsLawful := by
    intro offset
    simp only [main, circuit_norm, Gadgets.ToBits.rangeCheck]
    split <;> simp +arith [circuit_norm]

def Assumptions (P : FlexParams p n) (input : Inputs n (F p)) : Prop :=
  (∀ k : Fin n, (input.lhs[k.val]).val < boundAt P.M k.val) ∧
  (∀ k : Fin n, (input.rhs[k.val]).val < boundAt P.M k.val)

def Spec (B : ℕ) (input : Inputs n (F p)) : Prop :=
  polyValue B input.lhs = polyValue B input.rhs

private lemma flex_div_bound (B : ℕ) (Mf f : ℕ → ℕ) (k : ℕ)
    (hf : ∀ j, j ≤ k → f j < Mf j) (OFF : ℕ) (hOFF : 1 ≤ OFF)
    (hsum : (∑ j ∈ Finset.range (k + 1), Mf j * 2 ^ (B * j))
      ≤ OFF * 2 ^ (B * (k + 1))) :
    (∑ j ∈ Finset.range (k + 1), f j * 2 ^ (B * j)) / 2 ^ (B * (k + 1))
      ≤ OFF - 1 := by
  have hlt : (∑ j ∈ Finset.range (k + 1), f j * 2 ^ (B * j))
      < ∑ j ∈ Finset.range (k + 1), Mf j * 2 ^ (B * j) := by
    apply Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.mpr (by omega))
    intro j hj
    rw [Finset.mem_range] at hj
    exact (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).mpr (hf j (by omega))
  have hdiv : (∑ j ∈ Finset.range (k + 1), f j * 2 ^ (B * j)) / 2 ^ (B * (k + 1))
      < OFF := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
    calc (∑ j ∈ Finset.range (k + 1), f j * 2 ^ (B * j))
        < ∑ j ∈ Finset.range (k + 1), Mf j * 2 ^ (B * j) := hlt
      _ ≤ OFF * 2 ^ (B * (k + 1)) := hsum
  omega

def circuit (P : FlexParams p n) [Fact (p > 2)] : FormalAssertion (F p) (Inputs n) where
    main := main P
    Assumptions := Assumptions P
    Spec := Spec P.B
    soundness := by
      obtain ⟨B, W, M, hB, hW, hB1, hW1, hcarry, hlift⟩ := P
      circuit_proof_start
      simp only [circuit_norm, Gadgets.ToBits.rangeCheck] at h_holds ⊢
      obtain ⟨h_range, h_lin, h_top⟩ := h_holds
      refine ⟨?_, by split <;> simp [circuit_norm]⟩
      have hM : 0 < n := Nat.pos_of_neZero n
      set OFFn := 2 ^ (W - 1) with hOFFdef
      clear_value OFFn
      have hOFF2 : OFFn * 2 = 2 ^ W := by
        rw [hOFFdef, ← pow_succ]; congr 1; omega
      have hOFF_pos : 1 ≤ OFFn := hOFFdef ▸ Nat.one_le_two_pow
      clear hOFFdef

      set Pn : ℕ → ℕ := fun k => if h : k < n then (input.lhs[k]'h).val else 0 with hPn
      set Sn : ℕ → ℕ := fun k => if h : k < n then (input.rhs[k]'h).val else 0 with hSn
      set Cn : ℕ → ℕ := fun k => (env.get (i₀ + k)).val with hCn

      have hCn_lt : ∀ k, k < n → Cn k < 2 ^ W := by
        intro k hk; simpa [hCn] using h_range ⟨k, hk⟩
      have hPn_lt : ∀ k, (hk : k < n) → Pn k < boundAt M k := by
        intro k hk; simp only [hPn, dif_pos hk]; exact h_assumptions.1 ⟨k, hk⟩
      have hSn_lt : ∀ k, (hk : k < n) → Sn k < boundAt M k := by
        intro k hk; simp only [hSn, dif_pos hk]; exact h_assumptions.2 ⟨k, hk⟩

      have hOFFn_le_W : OFFn ≤ 2 ^ W := by omega
      have hOFFn_lt : OFFn < p := by omega
      have hpB : 2 ^ B < p := hB
      have hOFFn_cast : (OFFn : F p).val = OFFn := ZMod.val_natCast_of_lt hOFFn_lt

      rw [dif_neg (by omega : ¬ (n = 0))] at h_top
      simp only [circuit_norm] at h_top
      have hCtop : Cn (n - 1) = OFFn := by
        have : env.get (i₀ + (n - 1)) = (OFFn : F p) := by
          rw [← sub_eq_zero]; rw [show env.get (i₀ + (n - 1)) - (OFFn : F p)
            = env.get (i₀ + (n - 1)) + -(OFFn : F p) by ring]; exact h_top
        simp only [hCn, this, hOFFn_cast]

      have h_idx : ∀ k, (hk : k < n) →
          Pn k + (if k = 0 then OFFn else Cn (k - 1)) + OFFn * 2 ^ B
            = Sn k + Cn k * 2 ^ B + OFFn := by
        intro k hk
        have hlin := h_lin ⟨k, hk⟩

        have ha_e : Expression.eval env input_var.lhs[(⟨k, hk⟩ : Fin n).val] = input.lhs[k]'hk := by
          rw [← h_input]; simp [Vector.getElem_map]
        have hb_e : Expression.eval env input_var.rhs[(⟨k, hk⟩ : Fin n).val] = input.rhs[k]'hk := by
          rw [← h_input]; simp [Vector.getElem_map]
        have hcin_e : Expression.eval env
            (if h : (⟨k, hk⟩ : Fin n).val = 0 then 0
              else var { index := i₀ + ((⟨k, hk⟩ : Fin n).val - 1) } - Expression.const (OFFn : F p))
            = if k = 0 then 0 else env.get (i₀ + (k - 1)) - (OFFn : F p) := by
          simp only []
          split <;> simp [circuit_norm, sub_eq_add_neg]
        simp only [ha_e, hb_e, hcin_e] at hlin

        have hfield : (input.lhs[k]'hk) + (if k = 0 then (OFFn : F p) else env.get (i₀ + (k - 1)))
            + (OFFn : F p) * (2 ^ B : F p)
            = (input.rhs[k]'hk) + env.get (i₀ + k) * (2 ^ B : F p) + (OFFn : F p) := by
          rcases Nat.eq_zero_or_pos k with hk0 | hk0
          · subst hk0
            simp only [↓reduceIte] at hlin ⊢
            rw [← sub_eq_zero]
            rw [← hlin]; ring
          · rw [if_neg (by omega : ¬ k = 0)] at hlin ⊢
            rw [← sub_eq_zero]
            rw [← hlin]; ring

        have hcin_val : (if k = 0 then (OFFn : F p) else env.get (i₀ + (k - 1))).val
            = if k = 0 then OFFn else Cn (k - 1) := by
          split
          · exact hOFFn_cast
          · simp [hCn]
        have hcin_le : (if k = 0 then OFFn else Cn (k - 1)) ≤ 2 ^ W := by
          split
          · exact hOFFn_le_W
          · rename_i hkne; have := hCn_lt (k - 1) (by omega); omega
        have hliftk : boundAt M k + 2 ^ W + 2 ^ W * 2 ^ B < p := hlift ⟨k, hk⟩
        have hlhs : (input.lhs[k]'hk).val + (if k = 0 then OFFn else Cn (k - 1)) + OFFn * 2 ^ B < p := by
          have hp1 := hPn_lt k hk
          simp only [hPn, dif_pos hk] at hp1
          have hOB : OFFn * 2 ^ B ≤ 2 ^ W * 2 ^ B :=
            Nat.mul_le_mul_right _ hOFFn_le_W
          generalize OFFn * 2 ^ B = X at hOB ⊢
          generalize 2 ^ W * 2 ^ B = Y at hOB hliftk
          omega
        have hrhs : (input.rhs[k]'hk).val + (env.get (i₀ + k)).val * 2 ^ B + OFFn < p := by
          have hp2 := hSn_lt k hk
          simp only [hSn, dif_pos hk] at hp2
          have hc : (env.get (i₀ + k)).val < 2 ^ W := h_range ⟨k, hk⟩
          have hcB : (env.get (i₀ + k)).val * 2 ^ B ≤ 2 ^ W * 2 ^ B := by
            apply Nat.mul_le_mul_right; omega
          generalize (env.get (i₀ + k)).val * 2 ^ B = Z at hcB ⊢
          generalize 2 ^ W * 2 ^ B = Y at hcB hliftk
          omega
        have hlift' := per_index_lift (B := B) (input.lhs[k]'hk)
          (if k = 0 then (OFFn : F p) else env.get (i₀ + (k - 1)))
          (input.rhs[k]'hk) (env.get (i₀ + k)) (OFFn : F p)
          (if k = 0 then OFFn else Cn (k - 1)) OFFn hpB hcin_val hOFFn_cast hlhs hrhs hfield
        simp only [hPn, hSn, hCn, dif_pos hk] at hlift' ⊢
        convert hlift' using 2

      have hpv1 : polyValue B input.lhs = ∑ k ∈ Finset.range n, Pn k * 2 ^ (B * k) := by
        rw [polyValue, ← Fin.sum_univ_eq_sum_range (fun k => Pn k * 2 ^ (B * k))]
        apply Finset.sum_congr rfl
        intro i _; simp only [hPn, dif_pos i.isLt]
      have hpv2 : polyValue B input.rhs = ∑ k ∈ Finset.range n, Sn k * 2 ^ (B * k) := by
        rw [polyValue, ← Fin.sum_univ_eq_sum_range (fun k => Sn k * 2 ^ (B * k))]
        apply Finset.sum_congr rfl
        intro i _; simp only [hSn, dif_pos i.isLt]
      rw [hpv1, hpv2]

      have hsum : (∑ k ∈ Finset.range n,
            ((Pn k + (if k = 0 then OFFn else Cn (k - 1))) + OFFn * 2 ^ B) * 2 ^ (B * k))
          = ∑ k ∈ Finset.range n,
            (Sn k + Cn k * 2 ^ B + OFFn) * 2 ^ (B * k) := by
        apply Finset.sum_congr rfl
        intro k hk; rw [Finset.mem_range] at hk; rw [h_idx k hk]

      set SP := ∑ k ∈ Finset.range n, Pn k * 2 ^ (B * k) with hSP
      set SS := ∑ k ∈ Finset.range n, Sn k * 2 ^ (B * k) with hSS
      set SC := ∑ k ∈ Finset.range n, Cn k * 2 ^ (B * (k + 1)) with hSC
      set SCin' := ∑ k ∈ Finset.range n,
        (if k = 0 then OFFn else Cn (k - 1)) * 2 ^ (B * k) with hSCin'
      set SCin := ∑ k ∈ Finset.range n,
        (if k = 0 then 0 else Cn (k - 1)) * 2 ^ (B * k) with hSCin
      set G := ∑ k ∈ Finset.range n, 2 ^ (B * k) with hG

      have hSCin_rel : SCin' = SCin + OFFn := by
        rw [hSCin', hSCin, show n = (n - 1) + 1 from by omega]
        rw [Finset.sum_range_succ' _ (n - 1), Finset.sum_range_succ' _ (n - 1)]
        simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte,
          Nat.mul_zero, pow_zero, Nat.mul_one]
        ring

      have hLHS : (∑ k ∈ Finset.range n,
            ((Pn k + (if k = 0 then OFFn else Cn (k - 1))) + OFFn * 2 ^ B) * 2 ^ (B * k))
          = SP + SCin' + OFFn * 2 ^ B * G := by
        rw [hSP, hSCin', hG, Finset.mul_sum,
          ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _; ring

      have hRHS : (∑ k ∈ Finset.range n, (Sn k + Cn k * 2 ^ B + OFFn) * 2 ^ (B * k))
          = SS + SC + OFFn * G := by
        rw [hSS, hSC, hG, Finset.mul_sum,
          ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _
        rw [Nat.mul_add, Nat.mul_one, pow_add]; ring
      rw [hLHS, hRHS] at hsum

      have htel := carry_telescope B Cn n
      rw [if_neg (by omega : ¬ (n = 0)), hCtop] at htel
      rw [← hSCin, ← hSC] at htel

      have hgeo := geom_shift B n
      rw [← hG] at hgeo
      set Gtop := 2 ^ (B * n) with hGtop
      have hGtop_pos : 1 ≤ Gtop := Nat.one_le_two_pow
      have hG_pos : 1 ≤ G := by
        rw [hG]
        calc 1 = 2 ^ (B * 0) := by simp
          _ ≤ _ := Finset.single_le_sum (f := fun k => 2 ^ (B * k))
              (by intro i _; positivity) (Finset.mem_range.mpr hM)
      have hgeo' : 2 ^ B * G + 1 = G + Gtop := by omega
      have hoff_geo : OFFn * (2 ^ B * G) + OFFn = OFFn * G + OFFn * Gtop := by
        have hc := congrArg (OFFn * ·) hgeo'
        simp only [Nat.mul_add, Nat.mul_one] at hc
        omega
      have hsum' : SP + SCin' + OFFn * (2 ^ B * G) = SS + SC + OFFn * G := by
        rw [← Nat.mul_assoc]; exact hsum
      omega
    completeness := by
      obtain ⟨B, W, M, hB, hW, hB1, hW1, hcarry, hlift⟩ := P
      circuit_proof_start
      simp only [circuit_norm, Gadgets.ToBits.rangeCheck] at h_env ⊢
      obtain ⟨h_wit, _, _⟩ := h_env
      have hM : 0 < n := Nat.pos_of_neZero n
      set OFFn := 2 ^ (W - 1) with hOFFdef
      clear_value OFFn
      have h2OFF : OFFn * 2 = 2 ^ W := by
        rw [hOFFdef, ← pow_succ]; congr 1; omega
      have hOFFn_pos : 1 ≤ OFFn := hOFFdef ▸ Nat.one_le_two_pow
      clear hOFFdef

      set Pn : ℕ → ℕ := fun k => if h : k < n then (input.lhs[k]'h).val else 0 with hPn
      set Sn : ℕ → ℕ := fun k => if h : k < n then (input.rhs[k]'h).val else 0 with hSn
      have hPn_lt : ∀ k, k < n → Pn k < boundAt M k := by
        intro k hk; simp only [hPn, dif_pos hk]; exact h_assumptions.1 ⟨k, hk⟩
      have hSn_lt : ∀ k, k < n → Sn k < boundAt M k := by
        intro k hk; simp only [hSn, dif_pos hk]; exact h_assumptions.2 ⟨k, hk⟩

      set PFn : ℕ → ℕ := fun k => ∑ j ∈ Finset.range (k + 1), Pn j * 2 ^ (B * j) with hPFn
      set PSn : ℕ → ℕ := fun k => ∑ j ∈ Finset.range (k + 1), Sn j * 2 ^ (B * j) with hPSn

      have hPFn_eq : ∀ k, evalPartial B env input_var.lhs k = PFn k := by
        intro k; simp only [evalPartial, hPFn]
        apply Finset.sum_congr rfl
        intro j _; congr 1
        simp only [hPn]; split
        · rename_i h; rw [← h_input]; simp [Vector.getElem_map]
        · rfl
      have hPSn_eq : ∀ k, evalPartial B env input_var.rhs k = PSn k := by
        intro k; simp only [evalPartial, hPSn]
        apply Finset.sum_congr rfl
        intro j _; congr 1
        simp only [hSn]; split
        · rename_i h; rw [← h_input]; simp [Vector.getElem_map]
        · rfl

      set Dk : ℕ → ℕ := fun k => 2 ^ (B * (k + 1)) with hDk
      set Cn : ℕ → ℕ := fun k => OFFn + PFn k / Dk k - PSn k / Dk k with hCn

      have hDk_app : ∀ k, Dk k = 2 ^ (B * (k + 1)) := fun k => rfl
      have hPFn_app : ∀ k, PFn k = ∑ j ∈ Finset.range (k + 1), Pn j * 2 ^ (B * j) := fun k => rfl
      have hPSn_app : ∀ k, PSn k = ∑ j ∈ Finset.range (k + 1), Sn j * 2 ^ (B * j) := fun k => rfl
      have hCn_app : ∀ k, Cn k = OFFn + PFn k / Dk k - PSn k / Dk k := fun k => rfl

      have hwit_eq : ∀ k, k < n → env.get (i₀ + k) = (Cn k : F p) := by
        intro k hk
        rw [h_wit ⟨k, hk⟩]
        simp only [Vector.getElem_ofFn, hCn_app, hDk_app, hPFn_eq, hPSn_eq]

      have hMbound : ∀ k, (hk : k < n) →
          (∑ j ∈ Finset.range (k + 1), boundAt M j * 2 ^ (B * j))
            ≤ OFFn * 2 ^ (B * (k + 1)) := by
        intro k hk; exact hcarry ⟨k, hk⟩
      have hPFdiv : ∀ k, (hk : k < n) → PFn k / Dk k ≤ OFFn - 1 := by
        intro k hk
        rw [hPFn_app, hDk_app]
        exact flex_div_bound B (boundAt M) Pn k
          (fun j hj => hPn_lt j (by omega)) OFFn hOFFn_pos (hMbound k hk)
      have hPSdiv : ∀ k, (hk : k < n) → PSn k / Dk k ≤ OFFn - 1 := by
        intro k hk
        rw [hPSn_app, hDk_app]
        exact flex_div_bound B (boundAt M) Sn k
          (fun j hj => hSn_lt j (by omega)) OFFn hOFFn_pos (hMbound k hk)

      have hrange : ∀ k, (hk : k < n) → Cn k < 2 ^ W := by
        intro k hk
        have h1 := hPFdiv k hk
        rw [hCn_app]
        calc OFFn + PFn k / Dk k - PSn k / Dk k
            ≤ OFFn + PFn k / Dk k := Nat.sub_le _ _
          _ ≤ OFFn + (OFFn - 1) := by omega
          _ < 2 ^ W := by omega
      have hpB : 2 ^ B < p := hB
      have hOFFn_lt : OFFn < p := by
        have h1 : OFFn ≤ 2 ^ W := by omega
        omega
      have hOFFn_cast : (OFFn : F p).val = OFFn := ZMod.val_natCast_of_lt hOFFn_lt

      have hPFn_top : PFn (n - 1) = polyValue B input.lhs := by
        rw [hPFn_app, polyValue, ← Fin.sum_univ_eq_sum_range (fun j => Pn j * 2 ^ (B * j)),
          show n - 1 + 1 = n from by omega]
        apply Finset.sum_congr rfl (fun i _ => ?_)
        simp only [hPn, dif_pos i.isLt]
      have hPSn_top : PSn (n - 1) = polyValue B input.rhs := by
        rw [hPSn_app, polyValue, ← Fin.sum_univ_eq_sum_range (fun j => Sn j * 2 ^ (B * j)),
          show n - 1 + 1 = n from by omega]
        apply Finset.sum_congr rfl (fun i _ => ?_)
        simp only [hSn, dif_pos i.isLt]
      have hPtop_eq : PFn (n - 1) = PSn (n - 1) := by
        rw [hPFn_top, hPSn_top]; exact h_spec
      have hmod : ∀ k, k < n → PFn k % Dk k = PSn k % Dk k := by
        intro k hk
        have e1 : PFn (n - 1) % Dk k = PFn k % Dk k := by
          rw [hPFn_app, hPFn_app, hDk_app, show n - 1 + 1 = n from by omega]
          exact partial_mod_stable B Pn n k hk
        have e2 : PSn (n - 1) % Dk k = PSn k % Dk k := by
          rw [hPSn_app, hPSn_app, hDk_app, show n - 1 + 1 = n from by omega]
          exact partial_mod_stable B Sn n k hk
        rw [← e1, ← e2, hPtop_eq]

      have hCtop : Cn (n - 1) = OFFn := by
        rw [hCn_app, hPtop_eq]; omega

      have hidx : ∀ k, k < n →
          Pn k + (if k = 0 then OFFn else Cn (k - 1)) + OFFn * 2 ^ B
            = Sn k + Cn k * 2 ^ B + OFFn := by
        intro k hk

        set qP := PFn k / 2 ^ (B * k) with hqP_def
        set qS := PSn k / 2 ^ (B * k) with hqS_def
        set rP := PFn k / Dk k with hrP_def
        set rS := PSn k / Dk k with hrS_def
        have hrP_quot : rP = qP / 2 ^ B := by
          rw [hrP_def, hqP_def, hDk_app, show B * (k + 1) = B * k + B by ring, pow_add,
            Nat.div_div_eq_div_mul]
        have hrS_quot : rS = qS / 2 ^ B := by
          rw [hrS_def, hqS_def, hDk_app, show B * (k + 1) = B * k + B by ring, pow_add,
            Nat.div_div_eq_div_mul]
        have hsplitP : qP = rP * 2 ^ B + qP % 2 ^ B := by
          rw [hrP_quot]; exact (Nat.div_add_mod' qP (2 ^ B)).symm
        have hsplitS : qS = rS * 2 ^ B + qS % 2 ^ B := by
          rw [hrS_quot]; exact (Nat.div_add_mod' qS (2 ^ B)).symm
        have hdig : qP % 2 ^ B = qS % 2 ^ B := by
          have hP : qP % 2 ^ B = PFn k % Dk k / 2 ^ (B * k) := by
            rw [hqP_def, hDk_app, show B * (k + 1) = B * k + B by ring, pow_add,
              Nat.mod_mul_right_div_self]
          have hS : qS % 2 ^ B = PSn k % Dk k / 2 ^ (B * k) := by
            rw [hqS_def, hDk_app, show B * (k + 1) = B * k + B by ring, pow_add,
              Nat.mod_mul_right_div_self]
          rw [hP, hS, hmod k hk]
        have hstepP : qP = Pn k + (if k = 0 then 0
            else (∑ j ∈ Finset.range k, Pn j * 2 ^ (B * j)) / 2 ^ (B * k)) := by
          rw [hqP_def, hPFn_app]; exact quot_step B Pn k
        have hstepS : qS = Sn k + (if k = 0 then 0
            else (∑ j ∈ Finset.range k, Sn j * 2 ^ (B * j)) / 2 ^ (B * k)) := by
          rw [hqS_def, hPSn_app]; exact quot_step B Sn k
        have hCnk : Cn k = OFFn + rP - rS := by rw [hCn_app, ← hrP_def, ← hrS_def]
        have hrS_le : rS ≤ OFFn := by
          rw [hrS_def]; have := hPSdiv k hk; omega
        rw [hdig] at hsplitP
        clear_value qP qS rP rS
        have hmulCnk : Cn k * 2 ^ B = OFFn * 2 ^ B + rP * 2 ^ B - rS * 2 ^ B := by
          rw [hCnk, Nat.sub_mul, Nat.add_mul]
        rcases Nat.eq_zero_or_pos k with hk0 | hk0
        · subst hk0
          rw [hmulCnk]
          simp only [↓reduceIte] at hstepP hstepS ⊢
          rw [Nat.add_zero] at hstepP hstepS
          have hrPmul : rS * 2 ^ B ≤ rP * 2 ^ B + OFFn * 2 ^ B := by
            have : rS ≤ rP + OFFn := by omega
            calc rS * 2 ^ B ≤ (rP + OFFn) * 2 ^ B := Nat.mul_le_mul_right _ this
              _ = rP * 2 ^ B + OFFn * 2 ^ B := by rw [Nat.add_mul]
          omega
        · rw [if_neg (by omega : ¬ k = 0), hmulCnk]
          have hPFnprev : (∑ j ∈ Finset.range k, Pn j * 2 ^ (B * j)) = PFn (k - 1) := by
            rw [hPFn_app, show k - 1 + 1 = k from by omega]
          have hPSnprev : (∑ j ∈ Finset.range k, Sn j * 2 ^ (B * j)) = PSn (k - 1) := by
            rw [hPSn_app, show k - 1 + 1 = k from by omega]
          rw [if_neg (by omega : ¬ k = 0), hPFnprev] at hstepP
          rw [if_neg (by omega : ¬ k = 0), hPSnprev] at hstepS
          set rP' := PFn (k - 1) / Dk (k - 1) with hrP'_def
          set rS' := PSn (k - 1) / Dk (k - 1) with hrS'_def
          have hprevP : PFn (k - 1) / 2 ^ (B * k) = rP' := by
            rw [hrP'_def, hDk_app, show k - 1 + 1 = k from by omega]
          have hprevS : PSn (k - 1) / 2 ^ (B * k) = rS' := by
            rw [hrS'_def, hDk_app, show k - 1 + 1 = k from by omega]
          rw [hprevP] at hstepP
          rw [hprevS] at hstepS
          have hCnprev : Cn (k - 1) = OFFn + rP' - rS' := hCn_app (k - 1)
          have hrSprev_le : rS' ≤ OFFn := by
            rw [hrS'_def]; have := hPSdiv (k - 1) (by omega); omega
          rw [hCnprev]
          clear_value rP' rS'
          have hrPmul : rS * 2 ^ B ≤ rP * 2 ^ B + OFFn * 2 ^ B := by
            have : rS ≤ rP + OFFn := by omega
            calc rS * 2 ^ B ≤ (rP + OFFn) * 2 ^ B := Nat.mul_le_mul_right _ this
              _ = rP * 2 ^ B + OFFn * 2 ^ B := by rw [Nat.add_mul]
          omega

      have hCn_val : ∀ k, (hk : k < n) → (env.get (i₀ + k)).val = Cn k := by
        intro k hk
        rw [hwit_eq k hk, ZMod.val_natCast_of_lt (lt_of_lt_of_le (hrange k hk) (le_of_lt hW))]
      refine ⟨?_, ?_, ?_⟩
      ·
        intro i
        rw [hCn_val i.val i.isLt]; exact hrange i.val i.isLt
      ·
        intro i
        have hk := i.isLt
        have hnatk := hidx i.val hk
        have ha_e : Expression.eval env.toEnvironment input_var.lhs[i.val] = input.lhs[i.val]'hk := by
          rw [← h_input]; simp [Vector.getElem_map]
        have hb_e : Expression.eval env.toEnvironment input_var.rhs[i.val] = input.rhs[i.val]'hk := by
          rw [← h_input]; simp [Vector.getElem_map]
        have hcin_e : Expression.eval env.toEnvironment
            (if h : i.val = 0 then 0 else var { index := i₀ + (i.val - 1) } - Expression.const (OFFn : F p))
            = if i.val = 0 then 0 else env.get (i₀ + (i.val - 1)) - (OFFn : F p) := by
          split <;> simp [circuit_norm, sub_eq_add_neg]
        rw [ha_e, hb_e, hcin_e]
        have hAk : ((Pn i.val : ℕ) : F p) = (input.lhs[i.val]'hk) := by
          simp only [hPn, dif_pos hk]; rw [ZMod.natCast_zmod_val]
        have hBk : ((Sn i.val : ℕ) : F p) = (input.rhs[i.val]'hk) := by
          simp only [hSn, dif_pos hk]; rw [ZMod.natCast_zmod_val]
        have hCk : ((Cn i.val : ℕ) : F p) = env.get (i₀ + i.val) := by
          rw [hwit_eq i.val hk]
        have hpow_cast : ((2 ^ B : ℕ) : F p) = (2 ^ B : F p) := by push_cast; ring
        have hcast := congrArg (Nat.cast : ℕ → F p) hnatk
        push_cast [hpow_cast] at hcast
        rw [hAk, hBk, hCk] at hcast
        rcases Nat.eq_zero_or_pos i.val with hi0 | hi0
        · simp only [hi0, ↓reduceIte, add_zero] at hcast ⊢
          rw [← sub_eq_zero] at hcast
          rw [← hcast]; ring
        · simp only [if_neg (by omega : ¬ i.val = 0)] at hcast ⊢
          have hCkprev : ((Cn (i.val - 1) : ℕ) : F p) = env.get (i₀ + (i.val - 1)) := by
            rw [hwit_eq (i.val - 1) (by omega)]
          rw [hCkprev, ← sub_eq_zero] at hcast
          rw [← hcast]; ring
      ·
        rw [dif_neg (by omega : ¬ (n = 0))]
        simp only [circuit_norm]
        have : env.get (i₀ + (n - 1)) = (OFFn : F p) := by
          rw [hwit_eq (n - 1) (by omega), hCtop]
        rw [this]; ring

end EqViaCarriesFlex

end

namespace Cost

open Challenge.CostR1CS
open EqViaCarriesFlex (FlexParams)

variable {n : ℕ}

end Cost

end Solution.Secp256k1ScalarMulFixedBase

namespace Solution.Secp256k1ScalarMulFixedBase
namespace EqViaCarriesFlex

section ComputableWitness
variable {p : ℕ} [Fact p.Prime] {n : ℕ} [NeZero n]
open Challenge.Utils.ComputableWitnessLemmas

theorem evalPartial_stable {Input : TypeMap} [ProvableType Input]
    {input : Var Input (F p)} {env env' : ProverEnvironment (F p)}
    {m : ℕ} (x : Var (fields m) (F p)) (B k : ℕ)
    (hx : ∀ j (hj : j < m),
      Expression.eval env.toEnvironment (x[j]'hj)
        = Expression.eval env'.toEnvironment (x[j]'hj)) :
    evalPartial B env x k = evalPartial B env' x k := by
  simp only [evalPartial]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  by_cases hj : j < m
  · simp only [dif_pos hj]
    exact congrArg ZMod.val (hx j hj)
  · simp only [dif_neg hj]

theorem inputs_field_eq {input : Var (Inputs n) (F p)}
    {env env' : ProverEnvironment (F p)}
    (h_input : eval env input = eval env' input) :
    (∀ j (hj : j < n),
      Expression.eval env.toEnvironment (input.lhs[j]'hj)
        = Expression.eval env'.toEnvironment (input.lhs[j]'hj)) ∧
    (∀ j (hj : j < n),
      Expression.eval env.toEnvironment (input.rhs[j]'hj)
        = Expression.eval env'.toEnvironment (input.rhs[j]'hj)) := by
  constructor
  · intro j hj
    simpa [circuit_norm, CircuitType.eval_expression_prover_to_verifier,
      CircuitType.eval_expression, ProvableType.eval, explicit_provable_type,
      Vector.getElem_map] using
        congrArg (fun x : Inputs n (F p) => x.lhs[j]'hj) h_input
  · intro j hj
    simpa [circuit_norm, CircuitType.eval_expression_prover_to_verifier,
      CircuitType.eval_expression, ProvableType.eval, explicit_provable_type,
      Vector.getElem_map] using
        congrArg (fun x : Inputs n (F p) => x.rhs[j]'hj) h_input

theorem computableWitnesses (P : FlexParams p n) [Fact (p > 2)] :
    (circuit P).ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (FormalCircuitBase.computableWitnessCondition input env env')
    ((main P input).operations offset)
  apply FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main
  simp only [
    Circuit.bind_structuralComputableWitnesses_iff,
    Circuit.witnessVector_structuralComputableWitnesses_iff,
    Circuit.forEach_structuralComputableWitnesses_iff,
    FormalAssertion.assertion_structuralComputableWitnesses_iff,
    Circuit.assertZero_structuralComputableWitnesses_iff]
  and_intros
  · intro _ h_input
    obtain ⟨hlhs, hrhs⟩ := inputs_field_eq h_input
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_ofFn]
    rw [evalPartial_stable (input := input) input.lhs P.B i hlhs,
      evalPartial_stable (input := input) input.rhs P.B i hrhs]
  · intro i
    apply FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
    · intro k env env' hk h_agree _
      rw [CircuitType.eval_expression_prover_to_verifier (M := field),
        CircuitType.eval_expression_prover_to_verifier (M := field)]
      rw [show eval env.toEnvironment
              ((witnessVector n fun env =>
                Vector.ofFn fun k : Fin n =>
                  ((2 ^ (P.W - 1) + evalPartial P.B env input.lhs k.val / 2 ^ (P.B * (k.val + 1))
                      - evalPartial P.B env input.rhs k.val / 2 ^ (P.B * (k.val + 1)) : ℕ) :
                    F p)).output offset)[i.val] =
            env.get (offset + i.val) by
          rw [CircuitType.eval_expression (M := field)]
          simp [Circuit.witnessVector, Circuit.output, ProvableType.eval,
            explicit_provable_type, size, Vector.getElem_mapRange, Expression.eval],
        show eval env'.toEnvironment
              ((witnessVector n fun env =>
                Vector.ofFn fun k : Fin n =>
                  ((2 ^ (P.W - 1) + evalPartial P.B env input.lhs k.val / 2 ^ (P.B * (k.val + 1))
                      - evalPartial P.B env input.rhs k.val / 2 ^ (P.B * (k.val + 1)) : ℕ) :
                    F p)).output offset)[i.val] =
            env'.get (offset + i.val) by
          rw [CircuitType.eval_expression (M := field)]
          simp [Circuit.witnessVector, Circuit.output, ProvableType.eval,
            explicit_provable_type, size, Vector.getElem_mapRange, Expression.eval]]
      exact h_agree (offset + i.val) (by
        have hbase : offset + n + i.val * P.W ≤ k := by
          simpa [Circuit.localLength, Gadgets.ToBits.rangeCheck] using hk
        omega)
    · exact rangeCheckComputableWitnesses P.W P.hW
  · intro _
    trivial
  · split <;> trivial

theorem computableWitness (P : FlexParams p n) [Fact (p > 2)] : ∀ m input,
    ProverEnvironment.OnlyAccessedBelow m
      (fun env : ProverEnvironment (F p) => eval env input) →
    Circuit.ComputableWitnesses (main P input) m := by
  exact FormalCircuitBase.computableWitnesses_implies (computableWitnesses P)

end ComputableWitness

end EqViaCarriesFlex

end Solution.Secp256k1ScalarMulFixedBase

end DonorFile0_21

-- Adapted donor module: RangeCheck
section DonorFile0_22

namespace Solution.Secp256k1ScalarMulFixedBase
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
end Solution.Secp256k1ScalarMulFixedBase

end DonorFile0_22
