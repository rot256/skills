import Solution.Secp256k1ScalarMul.IsZeroFe



namespace Solution.Secp256k1ScalarMul
namespace EqFe

structure Inputs (F : Type) where
  a : Emu F
  b : Emu F
deriving ProvableStruct

def B64 : ℕ := 18446744073709551616

def packLoExpr (a b : Var Emu (F circomPrime)) : Expression (F circomPrime) :=
  a[0] - b[0] +
    (((B64 : F circomPrime) : Expression (F circomPrime)) * (a[1] - b[1]))

def packHiExpr (a b : Var Emu (F circomPrime)) : Expression (F circomPrime) :=
  a[2] - b[2] +
    (((B64 : F circomPrime) : Expression (F circomPrime)) * (a[3] - b[3]))

/-- The prover-chosen fold addend.  It is the high pack when the low pack
already vanishes and `0` otherwise, so that `dLo + v` vanishes *exactly* when
both packs do.  A *constant* coefficient on `dHi` cannot work here — by
Minkowski's theorem the two 129-bit pack ranges always admit a nonzero
collision modulo `circomPrime` — which is why the addend is witnessed.  It is
pinned to `{0, dHi}` by the single row `v * (v - dHi) = 0`; that is all the
soundness argument needs, since on the branch where both packs vanish the row
forces `v = 0`, and on every other branch one of the two `z · pack = 0` rows
already forces the flag to zero regardless of `v`. -/
def vCompute (input : Var Inputs (F circomPrime))
    (env : ProverEnvironment (F circomPrime)) : F circomPrime :=
  if Expression.eval env.toEnvironment (packLoExpr input.a input.b) = 0 then
    Expression.eval env.toEnvironment (packHiExpr input.a input.b)
  else 0

/-- The folded element `dLo + v`. -/
def uCompute (input : Var Inputs (F circomPrime))
    (env : ProverEnvironment (F circomPrime)) : F circomPrime :=
  Expression.eval env.toEnvironment (packLoExpr input.a input.b) + vCompute input env

def uInvCompute (input : Var Inputs (F circomPrime))
    (env : ProverEnvironment (F circomPrime)) : F circomPrime :=
  if uCompute input env = 0 then 0 else (uCompute input env)⁻¹

/-- Equality flag of two canonical field elements in `3` witnesses / `4` rows.

Rather than running an `IsZero` on each 128-bit half and multiplying the two
flags (`5/5`), the prover folds the two halves into a single element `u` and a
single `IsZero` runs on `u`; the two `z·pack = 0` rows keep the flag sound.
The fold addend `v` is witnessed directly and pinned by one quadratic row,
rather than being materialised as a product of a witnessed selector bit and
`dHi`, which saves one allocation. -/
def main (input : Var Inputs (F circomPrime)) :
    Circuit (F circomPrime) (Expression (F circomPrime)) := do
  let dLo := packLoExpr input.a input.b
  let dHi := packHiExpr input.a input.b
  let v ← witnessField (vCompute input)
  assertZero (v * (v - dHi))
  let uInv ← witnessField (uInvCompute input)
  let z <== 1 - (dLo + v) * uInv
  assertZero (z * dLo)
  assertZero (z * dHi)
  return z

instance elaborated : ElaboratedCircuit (F circomPrime) Inputs field main := by
  elaborate_circuit

def Assumptions (_ : Inputs (F circomPrime)) : Prop := True

def packLoF (a b : Emu (F circomPrime)) : F circomPrime :=
  a[0] - b[0] + (B64 : F circomPrime) * (a[1] - b[1])

def packHiF (a b : Emu (F circomPrime)) : F circomPrime :=
  a[2] - b[2] + (B64 : F circomPrime) * (a[3] - b[3])

def Spec (input : Inputs (F circomPrime)) (out : F circomPrime) : Prop :=
  out = if packLoF input.a input.b = 0 ∧ packHiF input.a input.b = 0
    then 1 else 0

/-- Evaluation of the two packs, given the input evaluation. -/
private lemma eval_packs {env : Environment (F circomPrime)}
    {input_var_a input_var_b : Emu (Expression (F circomPrime))}
    {input_a input_b : Emu (F circomPrime)}
    (ha : Vector.map (Expression.eval env) input_var_a = input_a)
    (hb : Vector.map (Expression.eval env) input_var_b = input_b) :
    Expression.eval env (packLoExpr input_var_a input_var_b) = packLoF input_a input_b ∧
      Expression.eval env (packHiExpr input_var_a input_var_b) = packHiF input_a input_b := by
  have hA : ∀ (i : ℕ) (hi : i < 4),
      Expression.eval env (input_var_a[i]'hi) = input_a[i]'hi := by
    intro i hi
    rw [← ha, Vector.getElem_map]
  have hB : ∀ (i : ℕ) (hi : i < 4),
      Expression.eval env (input_var_b[i]'hi) = input_b[i]'hi := by
    intro i hi
    rw [← hb, Vector.getElem_map]
  constructor
  · simp only [packLoExpr, packLoF, Expression.eval]
    rw [hA 0 (by omega), hA 1 (by omega), hB 0 (by omega), hB 1 (by omega)]
    ring
  · simp only [packHiExpr, packHiF, Expression.eval]
    rw [hA 2 (by omega), hA 3 (by omega), hB 2 (by omega), hB 3 (by omega)]
    ring

theorem soundness :
    Soundness (Input := Inputs) (Output := field) (F circomPrime) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨hv, hz, h3, h4⟩ := h_holds
  obtain ⟨ha, hb⟩ := h_input
  obtain ⟨hlo, hhi⟩ := eval_packs ha hb
  rw [hlo] at hz h3
  rw [hhi] at hv h4
  dsimp only [Spec]
  by_cases h0 : packLoF input_a input_b = 0
  · by_cases h1 : packHiF input_a input_b = 0
    · rw [if_pos ⟨h0, h1⟩]
      rw [h1] at hv
      simp only [neg_zero, add_zero] at hv
      rw [h0, mul_self_eq_zero.mp hv] at hz
      simpa using hz
    · rw [if_neg (fun h => h1 h.2)]
      exact (mul_eq_zero.mp h4).resolve_right h1
  · rw [if_neg (fun h => h0 h.1)]
    exact (mul_eq_zero.mp h3).resolve_right h0

private lemma uCompute_eq_zero_iff (input : Var Inputs (F circomPrime))
    (env : ProverEnvironment (F circomPrime)) :
    uCompute input env = 0 ↔
      (Expression.eval env.toEnvironment (packLoExpr input.a input.b) = 0 ∧
        Expression.eval env.toEnvironment (packHiExpr input.a input.b) = 0) := by
  simp only [uCompute, vCompute]
  by_cases h : Expression.eval env.toEnvironment (packLoExpr input.a input.b) = 0
  · rw [if_pos h, h]
    simp
  · rw [if_neg h]
    simp only [add_zero]
    exact ⟨fun hc => absurd hc h, fun hc => absurd hc.1 h⟩

private lemma one_sub_uu_inv (input : Var Inputs (F circomPrime))
    (env : ProverEnvironment (F circomPrime)) :
    1 + -(uCompute input env * uInvCompute input env)
      = if uCompute input env = 0 then 1 else 0 := by
  simp only [uInvCompute]
  by_cases h : uCompute input env = 0
  · rw [if_pos h, if_pos h, h]; ring
  · rw [if_neg h, if_neg h, mul_inv_cancel₀ h]; ring

theorem completeness :
    Completeness (Input := Inputs) (Output := field) (F circomPrime) main Assumptions := by
  circuit_proof_start
  obtain ⟨hv, hinv, hz⟩ := h_env
  have hu : Expression.eval env.toEnvironment (packLoExpr input_var_a input_var_b)
        + env.get i₀
      = uCompute { a := input_var_a, b := input_var_b } env := by
    rw [hv]
    simp only [uCompute]
  have hvrow : env.get i₀ *
      (env.get i₀ + -Expression.eval env.toEnvironment (packHiExpr input_var_a input_var_b))
        = 0 := by
    rw [hv]
    simp only [vCompute]
    by_cases h : Expression.eval env.toEnvironment (packLoExpr input_var_a input_var_b) = 0
    · rw [if_pos h]; ring
    · rw [if_neg h]; ring
  refine ⟨hvrow, hz, ?_, ?_⟩ <;>
    rw [hz, hu, hinv, one_sub_uu_inv] <;>
    by_cases h : uCompute { a := input_var_a, b := input_var_b } env = 0
  · rw [if_pos h, ((uCompute_eq_zero_iff _ env).mp h).1, mul_zero]
  · rw [if_neg h, zero_mul]
  · rw [if_pos h, ((uCompute_eq_zero_iff _ env).mp h).2, mul_zero]
  · rw [if_neg h, zero_mul]

private lemma witnessField_output_stable
    (c : ProverEnvironment (F circomPrime) → F circomPrime) (o k : ℕ)
    {env env' : ProverEnvironment (F circomPrime)}
    (h_agree : env.AgreesBelow k env') (hk : o < k) :
    Expression.eval env.toEnvironment ((witnessField c).output o) =
      Expression.eval env'.toEnvironment ((witnessField c).output o) := by
  simp only [Circuit.witnessField, Circuit.output, circuit_norm, Expression.eval]
  exact h_agree o hk

private lemma assignEq_output_stable (r : Expression (F circomPrime)) (o k : ℕ)
    {env env' : ProverEnvironment (F circomPrime)}
    (h_agree : env.AgreesBelow k env') (hk : o < k) :
    Expression.eval env.toEnvironment ((HasAssignEq.assignEq r).output o) =
      Expression.eval env'.toEnvironment ((HasAssignEq.assignEq r).output o) := by
  simp only [HasAssignEq.assignEq, circuit_norm, Expression.eval]
  exact h_agree o hk

private theorem assignEq_structural {Parent : TypeMap} [CircuitType Parent]
    (parentInput : Var Parent (F circomPrime))
    (rhs : Expression (F circomPrime)) (o : ℕ)
    (env env' : ProverEnvironment (F circomPrime))
    (hrhs : env.AgreesBelow o env' →
      eval env parentInput = eval env' parentInput →
      Expression.eval env.toEnvironment rhs = Expression.eval env'.toEnvironment rhs) :
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.StructuralComputableWitnesses
      parentInput env env' o ((HasAssignEq.assignEq rhs).operations o) := by
  unfold HasAssignEq.assignEq instHasAssignEqExpression
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.witnessField_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.pure_structuralComputableWitnesses_iff,
    and_true]
  refine ⟨hrhs, ?_, ?_⟩
  · exact IsZeroFe.equalityFieldSubcircuit_flatStructural_any parentInput _ _ _ env env'
  · trivial

private lemma eqfe_assertZero_localLength_zero (e : Expression (F circomPrime)) (offset : ℕ) :
    (assertZero e).localLength offset = 0 := rfl

private lemma eqfe_witnessField_localLength_one
    (compute : ProverEnvironment (F circomPrime) → F circomPrime) (offset : ℕ) :
    (witnessField compute).localLength offset = 1 := by
  unfold Circuit.witnessField
  change ((var <$> witnessVar compute).localLength offset) = 1
  rw [Circuit.map_localLength_eq]
  simp [Circuit.witnessVar, Circuit.localLength, Operations.localLength]

def circuit : FormalCircuit (F circomPrime) Inputs field where
  main; elaborated; Assumptions; Spec; soundness; completeness

theorem computableWitnesses : circuit.base.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  obtain ⟨a, b⟩ := input
  have hcells : ∀ (e e' : ProverEnvironment (F circomPrime)),
      eval e (⟨a, b⟩ : Var Inputs (F circomPrime)) =
        eval e' (⟨a, b⟩ : Var Inputs (F circomPrime)) →
      (∀ (i : ℕ) (hi : i < numLimbs),
        Expression.eval e.toEnvironment (a[i]'hi) =
          Expression.eval e'.toEnvironment (a[i]'hi)) ∧
      (∀ (i : ℕ) (hi : i < numLimbs),
        Expression.eval e.toEnvironment (b[i]'hi) =
          Expression.eval e'.toEnvironment (b[i]'hi)) := by
    intro e e' hinput
    simp only [circuit_norm, Inputs.mk.injEq] at hinput
    obtain ⟨ha, hb⟩ := hinput
    constructor
    · intro i hi
      have h := congrArg (fun v : Emu (F circomPrime) => v[i]'hi) ha
      simpa only [Vector.getElem_map] using h
    · intro i hi
      have h := congrArg (fun v : Emu (F circomPrime) => v[i]'hi) hb
      simpa only [Vector.getElem_map] using h
  have stableLo : ∀ (e e' : ProverEnvironment (F circomPrime)),
      eval e (⟨a, b⟩ : Var Inputs (F circomPrime)) =
        eval e' (⟨a, b⟩ : Var Inputs (F circomPrime)) →
      Expression.eval e.toEnvironment (packLoExpr a b) =
        Expression.eval e'.toEnvironment (packLoExpr a b) := by
    intro e e' hinput
    obtain ⟨hcA, hcB⟩ := hcells e e' hinput
    simp only [packLoExpr, Expression.eval]
    rw [hcA 0 (by decide), hcB 0 (by decide),
      hcA 1 (by decide), hcB 1 (by decide)]
  have stableHi : ∀ (e e' : ProverEnvironment (F circomPrime)),
      eval e (⟨a, b⟩ : Var Inputs (F circomPrime)) =
        eval e' (⟨a, b⟩ : Var Inputs (F circomPrime)) →
      Expression.eval e.toEnvironment (packHiExpr a b) =
        Expression.eval e'.toEnvironment (packHiExpr a b) := by
    intro e e' hinput
    obtain ⟨hcA, hcB⟩ := hcells e e' hinput
    simp only [packHiExpr, Expression.eval]
    rw [hcA 2 (by decide), hcB 2 (by decide),
      hcA 3 (by decide), hcB 3 (by decide)]
  unfold main
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.witnessField_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.assertZero_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.pure_structuralComputableWitnesses_iff,
    eqfe_witnessField_localLength_one, eqfe_assertZero_localLength_zero, and_true]
  refine ⟨?_, trivial, ?_, ?_⟩
  · intro _ h_input
    simp only [vCompute, stableLo env env' h_input, stableHi env env' h_input]
  · intro _ h_input
    simp only [uInvCompute, uCompute, vCompute,
      stableLo env env' h_input, stableHi env env' h_input]
  · refine assignEq_structural _ _ _ env env' ?_
    intro h_agree h_input
    simp only [Expression.eval]
    rw [witnessField_output_stable _ _ _ h_agree (by omega),
      witnessField_output_stable _ _ _ h_agree (by omega), stableLo env env' h_input]

theorem computableWitness : ∀ n input,
    ProverEnvironment.OnlyAccessedBelow n
      (fun env : ProverEnvironment (F circomPrime) => eval env input) →
    Circuit.ComputableWitnesses (main input) n :=
  Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnesses_implies
    (circuit := circuit.base) computableWitnesses

lemma eval_output_of_agreesBelow (x : Var Inputs (F circomPrime)) {offset k : ℕ}
    {env env' : ProverEnvironment (F circomPrime)}
    (h_agree : env.AgreesBelow k env') (hk : offset + 3 ≤ k) :
    eval env ((main x).output offset) = eval env' ((main x).output offset) := by
  rw [CircuitType.eval_var_field_prover, CircuitType.eval_var_field_prover]
  simp only [main, circuit_norm]
  exact h_agree (offset + 2) (by omega)



def loN (x : Emu (F circomPrime)) : ℕ := x[0].val + B64 * x[1].val

def hiN (x : Emu (F circomPrime)) : ℕ := x[2].val + B64 * x[3].val

lemma packLoF_eq_cast (a b : Emu (F circomPrime)) :
    packLoF a b = (loN a : F circomPrime) - (loN b : F circomPrime) := by
  simp only [packLoF, loN]
  push_cast [ZMod.natCast_zmod_val]
  rw [ZMod.natCast_zmod_val a[0], ZMod.natCast_zmod_val b[0],
    ZMod.natCast_zmod_val a[1], ZMod.natCast_zmod_val b[1]]
  ring

lemma packHiF_eq_cast (a b : Emu (F circomPrime)) :
    packHiF a b = (hiN a : F circomPrime) - (hiN b : F circomPrime) := by
  simp only [packHiF, hiN]
  push_cast [ZMod.natCast_zmod_val]
  rw [ZMod.natCast_zmod_val a[2], ZMod.natCast_zmod_val b[2],
    ZMod.natCast_zmod_val a[3], ZMod.natCast_zmod_val b[3]]
  ring

lemma loN_lt (x : Emu (F circomPrime)) (hx : x.Normalized limbBits) :
    loN x < B64 * B64 := by
  have h0 := hx 0
  have h1 := hx 1
  norm_num [limbBits] at h0 h1
  simp only [loN, B64]
  omega

lemma hiN_lt (x : Emu (F circomPrime)) (hx : x.Normalized limbBits) :
    hiN x < B64 * B64 := by
  have h2 := hx 2
  have h3 := hx 3
  norm_num [limbBits] at h2 h3
  simp only [hiN, B64]
  omega

lemma packLoF_zero_iff (a b : Emu (F circomPrime)) (ha : a.Normalized limbBits)
    (hb : b.Normalized limbBits) :
    packLoF a b = 0 ↔ loN a = loN b := by
  rw [packLoF_eq_cast, sub_eq_zero]
  have hpp : B64 * B64 < circomPrime := by decide
  constructor
  · intro h
    have hv := congrArg ZMod.val h
    rwa [ZMod.val_natCast_of_lt (lt_trans (loN_lt a ha) hpp),
      ZMod.val_natCast_of_lt (lt_trans (loN_lt b hb) hpp)] at hv
  · intro h
    rw [h]

lemma packHiF_zero_iff (a b : Emu (F circomPrime)) (ha : a.Normalized limbBits)
    (hb : b.Normalized limbBits) :
    packHiF a b = 0 ↔ hiN a = hiN b := by
  rw [packHiF_eq_cast, sub_eq_zero]
  have hpp : B64 * B64 < circomPrime := by decide
  constructor
  · intro h
    have hv := congrArg ZMod.val h
    rwa [ZMod.val_natCast_of_lt (lt_trans (hiN_lt a ha) hpp),
      ZMod.val_natCast_of_lt (lt_trans (hiN_lt b hb) hpp)] at hv
  · intro h
    rw [h]

lemma value_eq_chunks (x : Emu (F circomPrime)) :
    BigInt.value limbBits x = loN x + B64 * B64 * hiN x := by
  rw [BigInt.value_eq_sum]
  simp only [numLimbs, Fin.sum_univ_four]
  norm_num [loN, hiN, B64, limbBits]
  ring

lemma chunks_eq_iff_value_eq (a b : Emu (F circomPrime))
    (ha : a.Normalized limbBits) (hb : b.Normalized limbBits) :
    loN a = loN b ∧ hiN a = hiN b ↔
      BigInt.value limbBits a = BigInt.value limbBits b := by
  have hla := loN_lt a ha
  have hlb := loN_lt b hb
  rw [value_eq_chunks, value_eq_chunks]
  simp only [B64] at hla hlb ⊢
  omega

theorem flag_eq_decode_eq {a b : Emu (F circomPrime)} {out : F circomPrime}
    (ha : Fe.Valid a) (hb : Fe.Valid b) (hout : Spec { a, b } out) :
    out = if decodeFe a = decodeFe b then 1 else 0 := by
  have hdec : decodeFe a = decodeFe b ↔
      BigInt.value limbBits a = BigInt.value limbBits b := by
    simp only [decodeFe]
    constructor
    · intro h
      have hv := congrArg ZMod.val h
      rwa [ZMod.val_natCast_of_lt ha.2, ZMod.val_natCast_of_lt hb.2] at hv
    · intro h
      rw [h]
  dsimp [Spec] at hout
  rw [hout]
  refine if_congr ?_ rfl rfl
  rw [packLoF_zero_iff a b ha.1 hb.1, packHiF_zero_iff a b ha.1 hb.1,
    chunks_eq_iff_value_eq a b ha.1 hb.1, hdec]

end EqFe
end Solution.Secp256k1ScalarMul
