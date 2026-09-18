import Solution.Secp256k1ScalarMul.MulModVariantsCost
import Solution.Secp256k1ScalarMul.Cost
import Challenge.Utils.ComputableWitnessLemmas

/-!
# `MulModLooseQ`: loose modular multiplication with a *short* quotient

`MulModLoose` witnesses the quotient `q = a·b / n` as a full `numLimbs`-limb
`BigInt` and range-checks all four limbs (252 allocations / 256 constraints).
Every call site in the scalar-side GLV relation multiplies by a value below
`2^limbBits`, so the honest quotient satisfies `q < 2^65`: only the low limb
needs a full range check, the second limb is a *boolean*, and the top two limbs
are asserted zero.  That replaces the 256/256 quotient normalization by
63/64 + 0/1 + 0/1 + 0/1 = 63/67, i.e. 189 allocations and 189 constraints less
per site, with no change to the certificate or to the specification.
-/

namespace Solution.Secp256k1ScalarMul
namespace MulModLooseQ

open MulMod
open Solution.Secp256k1ScalarMul.Limbs

def main (input : Var (MulMod.Inputs numLimbs) (F circomPrime)) :
    Circuit (F circomPrime) (Var Emu (F circomPrime)) := do
  let a := input.a
  let b := input.b
  let n := input.modulus
  let q ← ProvableType.witness (α := Emu) fun env =>
    let prod := evalEmu env a * evalEmu env b
    let qval : ℕ := prod / evalEmu env n
    Vector.ofFn fun k : Fin numLimbs =>
      ((qval / 2 ^ (limbBits * k.val) % 2 ^ limbBits : ℕ) : F circomPrime)
  let r ← ProvableType.witness (α := Emu) fun env =>
    let prod := evalEmu env a * evalEmu env b
    let rval : ℕ := prod % evalEmu env n
    Vector.ofFn fun k : Fin numLimbs =>
      ((rval / 2 ^ (limbBits * k.val) % 2 ^ limbBits : ℕ) : F circomPrime)
  RangeCheck.circuit secpParams.B secpParams.hB secpParams.hB1 q[0]
  assertZero (q[1] * (q[1] - 1))
  assertZero q[2]
  assertZero q[3]
  Normalize.circuit secpParams r
  let Pc ← interpolatedMul a b
  let Sqn : Vector (Expression (F circomPrime)) (2 * numLimbs - 1) := bigIntMulNoReduce q n
  let S : Vector (Expression (F circomPrime)) (2 * numLimbs - 1) :=
    Vector.mapFinRange (2 * numLimbs - 1) fun k =>
      if h : k.val < numLimbs then Sqn[k.val] + r[k.val]'h else Sqn[k.val]
  GroupedEqXV.circuit secpParams.B gfMul posOfMul 5 vMul vMul hgvMul secpParams.hB1
    { lhs := Pc, rhs := S }
  return r

instance elaborated :
    ElaboratedCircuit (F circomPrime) (MulMod.Inputs numLimbs) Emu main := by
  elaborate_circuit

def Assumptions (input : MulMod.Inputs numLimbs (F circomPrime)) : Prop :=
  input.a.Normalized limbBits ∧ input.b.Normalized limbBits ∧
    input.modulus.Normalized limbBits ∧
    input.a.value limbBits < input.modulus.value limbBits ∧
    0 < input.modulus.value limbBits ∧
    input.a.value limbBits * input.b.value limbBits
      < 2 ^ 65 * input.modulus.value limbBits

def Spec (input : MulMod.Inputs numLimbs (F circomPrime)) (out : Emu (F circomPrime)) :
    Prop :=
  out.Normalized limbBits ∧
    out.value limbBits % input.modulus.value limbBits
      = (input.a.value limbBits * input.b.value limbBits) % input.modulus.value limbBits

theorem soundness : Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [Normalize.circuit, Normalize.elaborated, Normalize.main,
    Normalize.Assumptions, Normalize.Spec,
    RangeCheck.circuit, RangeCheck.Assumptions, RangeCheck.Spec,
    GroupedEqXV.circuit, GroupedEqXV.elaborated,
    GroupedEqXV.Assumptions, GroupedEqX.Spec]
  obtain ⟨ha_norm, hb_norm, hn_norm, hab_lt, hn_pos, hbound⟩ := h_assumptions
  obtain ⟨hq0, hq1, hq2, hq3, hr_norm, hAB_ops, h_eq_impl⟩ := h_holds
  simp only [hNfMul] at h_eq_impl
  have hq_norm : BigInt.Normalized secpParams.B (Vector.map (Expression.eval env)
      (Vector.mapRange numLimbs fun i => var (F := F circomPrime) { index := i₀ + i })) := by
    intro i
    have hval : (Vector.map (Expression.eval env)
        (Vector.mapRange numLimbs fun i => var (F := F circomPrime) { index := i₀ + i }))[i.val]
        = env.get (i₀ + i.val) := by
      simp [circuit_norm]
    rw [Fin.getElem_fin, hval]
    have h1 : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 := by
      have := i.isLt; simp only [numLimbs] at this; omega
    rcases h1 with h | h | h | h <;> rw [h]
    · exact hq0
    · have : env.get (i₀ + 1) = 0 ∨ env.get (i₀ + 1) = 1 := by
        rcases mul_eq_zero.mp hq1 with h' | h'
        · exact Or.inl h'
        · exact Or.inr (by linear_combination h')
      rcases this with h' | h' <;> rw [h']
      · simp [secpParams]
      · rw [ZMod.val_one]
        exact Nat.one_lt_two_pow (by decide)
    · rw [hq2]; simp [secpParams]
    · rw [hq3]; simp [secpParams]
  have hbridge : ∀ (V : Vector (Expression (F circomPrime)) (2 * numLimbs - 1))
      (k : Fin (2 * numLimbs - 1)),
      (Vector.map (Expression.eval env) V)[k.val] = Expression.eval env V[k.val] :=
    fun V k => Vector.getElem_map _ _
  have hpm : 2 * numLimbs - 1 < circomPrime := by decide
  set OFF := i₀ + numLimbs + numLimbs + (secpParams.B - 1) + numLimbs * (secpParams.B - 1) with hOFF
  have h_pAB := interpolatedMul_soundness OFF input_var.a input_var.b env hAB_ops
  refine ⟨?_, interpolatedMul_requirements _ _ _ _⟩
  have h_input' : (Vector.map (Expression.eval env) input_var.a,
      Vector.map (Expression.eval env) input_var.b,
      Vector.map (Expression.eval env) input_var.modulus)
        = ((input.a, input.b, input.modulus) :
          ProvablePair (BigInt numLimbs) (ProvablePair (BigInt numLimbs) (BigInt numLimbs))
            (F circomPrime)) := by
    simp only [← h_input]
  have heqAB_get := interpolatedMul_eval_bridge env OFF input_var.a input_var.b hpm h_pAB
  exact MulMod.mulMod_soundness_core_loose_wm (B := secpParams.B) secpParams.hp i₀ env
    input_var.a input_var.b input_var.modulus
    (interpolatedMul input_var.a input_var.b OFF).1
    (bigIntMulNoReduce (Vector.mapRange numLimbs fun i => var { index := i₀ + i })
      input_var.modulus)
    (input.a, input.b, input.modulus) h_input' ha_norm hb_norm hn_norm hq_norm hr_norm
    heqAB_get (fun _ => rfl)
    (fun hb => h_eq_impl
      ⟨fun k => lt_of_eq_of_lt (congrArg ZMod.val (Vector.getElem_map _ _)) (hb.1 k),
       fun k => lt_of_eq_of_lt (congrArg ZMod.val (Eq.trans (Vector.getElem_map _ _)
         (congrArg (Expression.eval env) (Vector.getElem_mapFinRange _ _)))) (hb.2 k)⟩)

theorem completeness : Completeness (F circomPrime) main Assumptions := by
  circuit_proof_start [Normalize.circuit, Normalize.elaborated, Normalize.main,
    Normalize.Assumptions, Normalize.Spec,
    RangeCheck.circuit, RangeCheck.Assumptions, RangeCheck.Spec,
    GroupedEqXV.circuit, GroupedEqXV.elaborated,
    GroupedEqXV.Assumptions, GroupedEqX.Spec]
  obtain ⟨ha_norm, hb_norm, hn_norm, hab_lt, hn_pos, hbound⟩ := h_assumptions
  obtain ⟨hq_env, hr_env, hAB_uses⟩ := h_env
  set OFF := i₀ + numLimbs + numLimbs + (secpParams.B - 1) + numLimbs * (secpParams.B - 1)
    with hOFF
  have h_pvAB := interpolatedMul_usesLocalWitnesses OFF OFF input_var.a input_var.b env rfl hAB_uses
  have heva : evalEmu env input_var.a = BigInt.value limbBits input.a := by
    rw [evalEmu, BigInt.value, ← h_input]
  have hevb : evalEmu env input_var.b = BigInt.value limbBits input.b := by
    rw [evalEmu, BigInt.value, ← h_input]
  have hevn : evalEmu env input_var.modulus = BigInt.value limbBits input.modulus := by
    rw [evalEmu, BigInt.value, ← h_input]
  have hqwit : ∀ i : Fin numLimbs, env.toEnvironment.get (i₀ + i.val)
      = ((BigInt.value limbBits input.a * BigInt.value limbBits input.b
          / BigInt.value limbBits input.modulus
          / 2 ^ (limbBits * i.val) % 2 ^ limbBits : ℕ) : F circomPrime) := by
    intro i; rw [hq_env i, Vector.getElem_ofFn, heva, hevb, hevn]
  have hrwit : ∀ i : Fin numLimbs, env.toEnvironment.get (i₀ + numLimbs + i.val)
      = ((BigInt.value limbBits input.a * BigInt.value limbBits input.b
          % BigInt.value limbBits input.modulus
          / 2 ^ (limbBits * i.val) % 2 ^ limbBits : ℕ) : F circomPrime) := by
    intro i; rw [hr_env i, Vector.getElem_ofFn, heva, hevb, hevn]
  have h_input' : (Vector.map (Expression.eval env.toEnvironment) input_var.a,
      Vector.map (Expression.eval env.toEnvironment) input_var.b,
      Vector.map (Expression.eval env.toEnvironment) input_var.modulus)
        = ((input.a, input.b, input.modulus) :
          ProvablePair (BigInt numLimbs) (ProvablePair (BigInt numLimbs) (BigInt numLimbs))
            (F circomPrime)) := by
    simp only [← h_input]
  have heqAB_get := interpolatedMul_eval_bridge_uses env.toEnvironment OFF
    input_var.a input_var.b h_pvAB
  have core := MulMod.mulMod_completeness_core_wideb_wm (B := secpParams.B) secpParams.hB
    secpParams.hp i₀ env.toEnvironment
    input_var.a input_var.b input_var.modulus
    (interpolatedMul input_var.a input_var.b OFF).1
    (bigIntMulNoReduce (Vector.mapRange numLimbs fun i => var { index := i₀ + i })
      input_var.modulus)
    (input.a, input.b, input.modulus) h_input' ha_norm hb_norm hn_norm hab_lt hn_pos
    hqwit hrwit heqAB_get (fun _ => rfl)
  -- the honest quotient is below `2^65`
  set QV : ℕ := BigInt.value limbBits input.a * BigInt.value limbBits input.b
      / BigInt.value limbBits input.modulus with hQVdef
  have hQV : QV < 2 ^ 65 :=
    Nat.div_lt_of_lt_mul (hbound.trans_le (le_of_eq (Nat.mul_comm _ _)))
  have hpow64 : (2 : ℕ) ^ limbBits = 18446744073709551616 := by norm_num [limbBits]
  have hQVnum : QV < 36893488147419103232 := by
    have h65 : (2 : ℕ) ^ 65 = 36893488147419103232 := by norm_num
    omega
  have hq0 : env.toEnvironment.get i₀ = ((QV % 2 ^ limbBits : ℕ) : F circomPrime) := by
    have := hqwit ⟨0, by decide⟩
    simpa [hQVdef] using this
  have hq1 : env.toEnvironment.get (i₀ + 1)
      = ((QV / 2 ^ limbBits % 2 ^ limbBits : ℕ) : F circomPrime) := by
    have := hqwit ⟨1, by decide⟩
    simpa [hQVdef] using this
  have hq2 : env.toEnvironment.get (i₀ + 2)
      = ((QV / 2 ^ (limbBits * 2) % 2 ^ limbBits : ℕ) : F circomPrime) := by
    have := hqwit ⟨2, by decide⟩
    simpa [hQVdef] using this
  have hq3 : env.toEnvironment.get (i₀ + 3)
      = ((QV / 2 ^ (limbBits * 3) % 2 ^ limbBits : ℕ) : F circomPrime) := by
    have := hqwit ⟨3, by decide⟩
    simpa [hQVdef] using this
  refine ⟨?_, ?_, ?_, ?_, core.2.1,
    interpolatedMul_completeness OFF input_var.a input_var.b env h_pvAB, ?_⟩
  · rw [hq0, ZMod.val_natCast_of_lt]
    · exact Nat.mod_lt _ (Nat.two_pow_pos limbBits)
    · exact lt_trans (Nat.mod_lt _ (Nat.two_pow_pos limbBits)) (by decide)
  · have hlt : QV / 2 ^ limbBits < 2 := by
      apply Nat.div_lt_of_lt_mul
      omega
    have hmod : QV / 2 ^ limbBits % 2 ^ limbBits = QV / 2 ^ limbBits :=
      Nat.mod_eq_of_lt (lt_trans hlt (by omega))
    rw [hq1, hmod]
    have hcase : QV / 2 ^ limbBits = 0 ∨ QV / 2 ^ limbBits = 1 := by omega
    rcases hcase with h | h <;> rw [h] <;> norm_num
  · rw [hq2]
    have : QV / 2 ^ (limbBits * 2) = 0 := by
      apply Nat.div_eq_of_lt
      have : (2 : ℕ) ^ 65 ≤ 2 ^ (limbBits * 2) := Nat.pow_le_pow_right (by norm_num) (by norm_num [limbBits])
      omega
    rw [this]
    norm_num
  · rw [hq3]
    have : QV / 2 ^ (limbBits * 3) = 0 := by
      apply Nat.div_eq_of_lt
      have : (2 : ℕ) ^ 65 ≤ 2 ^ (limbBits * 3) := Nat.pow_le_pow_right (by norm_num) (by norm_num [limbBits])
      omega
    rw [this]
    norm_num
  · refine ⟨⟨fun k => ?_, fun k => ?_⟩, core.2.2.1.2⟩
    · rw [hNfMul]
      exact lt_of_eq_of_lt (congrArg ZMod.val (Vector.getElem_map _ _)) (core.2.2.1.1.1 k)
    · rw [hNfMul]
      exact lt_of_eq_of_lt (congrArg ZMod.val (Eq.trans (Vector.getElem_map _ _)
        (congrArg (Expression.eval env.toEnvironment) (Vector.getElem_mapFinRange _ _))))
        (core.2.2.1.1.2 k)

def circuit : FormalCircuit (F circomPrime) (MulMod.Inputs numLimbs) Emu where
  main
  elaborated
  Assumptions
  Spec
  soundness
  completeness

attribute [local irreducible] interpolatedMul Normalize.circuit GroupedEqXV.circuit
  RangeCheck.circuit

theorem computableWitnesses : circuit.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition
      input env env')
    ((main input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main
  let qc : Circuit (F circomPrime) (Var Emu (F circomPrime)) :=
    ProvableType.witness (α := Emu) fun env =>
      let prod := evalEmu env input.a * evalEmu env input.b
      let qval : ℕ := prod / evalEmu env input.modulus
      Vector.ofFn fun k : Fin numLimbs =>
        ((qval / 2 ^ (limbBits * k.val) % 2 ^ limbBits : ℕ) : F circomPrime)
  let q := qc.output offset
  let rOff := offset + qc.localLength offset
  let rc : Circuit (F circomPrime) (Var Emu (F circomPrime)) :=
    ProvableType.witness (α := Emu) fun env =>
      let prod := evalEmu env input.a * evalEmu env input.b
      let rval : ℕ := prod % evalEmu env input.modulus
      Vector.ofFn fun k : Fin numLimbs =>
        ((rval / 2 ^ (limbBits * k.val) % 2 ^ limbBits : ℕ) : F circomPrime)
  let r := rc.output rOff
  let rcOff := rOff + rc.localLength rOff
  let rgc : Circuit (F circomPrime) Unit :=
    assertion (RangeCheck.circuit secpParams.B secpParams.hB secpParams.hB1) q[0]
  let nrOff := rcOff + rgc.localLength rcOff
  let nrc : Circuit (F circomPrime) Unit := assertion (Normalize.circuit secpParams) r
  let pcOff := nrOff + nrc.localLength nrOff
  let pcv := (interpolatedMul input.a input.b).output pcOff
  let eqOff := pcOff + (interpolatedMul input.a input.b).localLength pcOff
  let Sqn : Vector (Expression (F circomPrime)) (2 * numLimbs - 1) :=
    bigIntMulNoReduce q input.modulus
  let Sv : Vector (Expression (F circomPrime)) (2 * numLimbs - 1) :=
    Vector.mapFinRange (2 * numLimbs - 1) fun k =>
      if h : k.val < numLimbs then Sqn[k.val] + r[k.val]'h else Sqn[k.val]
  have h_qlen : qc.localLength offset = numLimbs := by
    simp [qc, ProvableType.witness, Circuit.localLength, Operations.localLength, size]
  have h_rlen : rc.localLength rOff = numLimbs := by
    simp [rc, ProvableType.witness, Circuit.localLength, Operations.localLength, size]
  have h_pclen : (interpolatedMul input.a input.b).localLength pcOff = 2 * numLimbs - 1 :=
    interpolatedMul_localLength pcOff input.a input.b
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.provableWitness_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.assertZero_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.pure_structuralComputableWitnesses_iff,
    and_true, true_and]
  and_intros
  · intro _ h_input
    have ha : evalEmu env input.a = evalEmu env' input.a :=
      evalEmu_eq_of_eval_eq (by
        simpa [circuit_norm] using
          congrArg (fun x : MulMod.Inputs numLimbs (F circomPrime) => x.a) h_input)
    have hb : evalEmu env input.b = evalEmu env' input.b :=
      evalEmu_eq_of_eval_eq (by
        simpa [circuit_norm] using
          congrArg (fun x : MulMod.Inputs numLimbs (F circomPrime) => x.b) h_input)
    have hn : evalEmu env input.modulus = evalEmu env' input.modulus :=
      evalEmu_eq_of_eval_eq (by
        simpa [circuit_norm] using
          congrArg (fun x : MulMod.Inputs numLimbs (F circomPrime) => x.modulus) h_input)
    simp only [ha, hb, hn]
  · intro _ h_input
    have ha : evalEmu env input.a = evalEmu env' input.a :=
      evalEmu_eq_of_eval_eq (by
        simpa [circuit_norm] using
          congrArg (fun x : MulMod.Inputs numLimbs (F circomPrime) => x.a) h_input)
    have hb : evalEmu env input.b = evalEmu env' input.b :=
      evalEmu_eq_of_eval_eq (by
        simpa [circuit_norm] using
          congrArg (fun x : MulMod.Inputs numLimbs (F circomPrime) => x.b) h_input)
    have hn : evalEmu env input.modulus = evalEmu env' input.modulus :=
      evalEmu_eq_of_eval_eq (by
        simpa [circuit_norm] using
          congrArg (fun x : MulMod.Inputs numLimbs (F circomPrime) => x.modulus) h_input)
    simp only [ha, hb, hn]
  · exact Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
      (RangeCheck.circuit secpParams.B secpParams.hB secpParams.hB1) input q[0] rcOff
      (by
        intro k env₁ env₂ hle h_agree _
        have hk : offset + numLimbs ≤ k := by
          dsimp only [rcOff, rOff] at hle
          rw [h_qlen] at hle
          omega
        have hq_vec : eval env₁ q = eval env₂ q :=
          MulMod.bigIntWitnessOutput_stable _ h_agree hk
        have := MulMod.bigInt_getElem_eval_eq hq_vec 0 (by decide)
        simpa [circuit_norm] using this)
      (RangeCheck.computableWitnesses secpParams.B secpParams.hB secpParams.hB1) env env'
  · exact Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
      (Normalize.circuit secpParams) input r nrOff
      (by
        intro k env₁ env₂ hle h_agree _
        have hk : rOff + numLimbs ≤ k := by
          dsimp only [nrOff, rcOff] at hle
          rw [h_rlen] at hle
          omega
        exact MulMod.bigIntWitnessOutput_stable _ h_agree hk)
      (Normalize.computableWitnesses secpParams) env env'
  · exact interpolatedMul_structuralComputableWitnesses input input.a input.b pcOff
      (by
        intro k env₁ env₂ _ _ h_input
        have ha : eval env₁ input.a = eval env₂ input.a := by
          simpa [circuit_norm] using
            congrArg (fun x : MulMod.Inputs numLimbs (F circomPrime) => x.a) h_input
        have hb : eval env₁ input.b = eval env₂ input.b := by
          simpa [circuit_norm] using
            congrArg (fun x : MulMod.Inputs numLimbs (F circomPrime) => x.b) h_input
        exact ⟨ha, hb⟩)
      env env'
  · exact Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
      (GroupedEqXV.circuit secpParams.B gfMul posOfMul 5 vMul vMul hgvMul secpParams.hB1)
      input { lhs := pcv, rhs := Sv } eqOff
      (by
        intro k env₁ env₂ hle h_agree h_input
        have hk_pc : pcOff + (2 * numLimbs - 1) ≤ k := by
          dsimp only [eqOff] at hle
          rw [h_pclen] at hle
          omega
        have hk_q : offset + numLimbs ≤ k := by
          dsimp only [eqOff, pcOff, nrOff, rcOff, rOff] at hle
          rw [h_qlen] at hle
          omega
        have hk_r : rOff + numLimbs ≤ k := by
          dsimp only [eqOff, pcOff, nrOff, rcOff] at hle
          rw [h_rlen] at hle
          omega
        have hPc : Vector.map (Expression.eval env₁.toEnvironment) pcv
            = Vector.map (Expression.eval env₂.toEnvironment) pcv :=
          interpolatedMul_output_stable pcOff input.a input.b h_agree hk_pc
        have hq_vec : eval env₁ q = eval env₂ q :=
          MulMod.bigIntWitnessOutput_stable _ h_agree hk_q
        have hr_vec : eval env₁ r = eval env₂ r :=
          MulMod.bigIntWitnessOutput_stable _ h_agree hk_r
        have hn : eval env₁ input.modulus = eval env₂ input.modulus := by
          simpa [circuit_norm] using
            congrArg (fun x : MulMod.Inputs numLimbs (F circomPrime) => x.modulus) h_input
        have hr_map : r.map (Expression.eval env₁.toEnvironment)
            = r.map (Expression.eval env₂.toEnvironment) :=
          MulMod.bigInt_map_eval_eq_of_eval_eq hr_vec
        have hS : Vector.map (Expression.eval env₁.toEnvironment) Sv
            = Vector.map (Expression.eval env₂.toEnvironment) Sv := by
          apply Vector.ext
          intro i hi
          have hsq_i : Expression.eval env₁.toEnvironment Sqn[i]
              = Expression.eval env₂.toEnvironment Sqn[i] :=
            MulMod.bigIntMulNoReduce_coeff_stable env₁.toEnvironment env₂.toEnvironment q
              input.modulus
              (fun j hj => MulMod.bigInt_getElem_eval_eq hq_vec j hj)
              (fun j hj => MulMod.bigInt_getElem_eval_eq hn j hj) ⟨i, hi⟩
          simp only [Vector.getElem_map, Sv, Vector.getElem_mapFinRange]
          split
          · rename_i hlt
            have hr_i : Expression.eval env₁.toEnvironment (r[i]'hlt)
                = Expression.eval env₂.toEnvironment (r[i]'hlt) := by
              have := congrArg (fun v : Vector (F circomPrime) numLimbs => v[i]'hlt) hr_map
              simpa only [Vector.getElem_map] using this
            simp only [Expression.eval, hsq_i, hr_i]
          · exact hsq_i
        simp only [circuit_norm]
        rw [hPc, hS])
      (GroupedEqXV.computableWitnesses secpParams.B gfMul posOfMul 5 vMul vMul hgvMul
        secpParams.hB1) env env'

end MulModLooseQ

namespace Cost

open Challenge.CostR1CS

attribute [local irreducible] isR1CSRow r1csProducts operationsIsR1CS flatOperationsIsR1CS

def mulModLooseQCount : Count :=
  ⟨numLimbs, 0⟩ + (⟨numLimbs, 0⟩ + (⟨secpParams.B - 1, secpParams.B⟩ + (⟨0, 1⟩ + (⟨0, 1⟩ +
    (⟨0, 1⟩ + (⟨numLimbs * (secpParams.B - 1), numLimbs * secpParams.B⟩ +
      (⟨2 * numLimbs - 1, 2 * numLimbs - 1⟩ +
        (⟨GroupedEqXV.widthAllocFrom vMul.Wf 3 0,
          GroupedEqXV.widthConsFrom vMul.Wf 3 0 + 1⟩ + Count.zero))))))))

theorem costIs_mulModLooseQ (input : Var (MulMod.Inputs numLimbs) (F circomPrime)) :
    CostIs (MulModLooseQ.main input) mulModLooseQCount := by
  unfold MulModLooseQ.main mulModLooseQCount
  refine CostIs.bind (CostIs.provableWitness _) fun q => ?_
  refine CostIs.bind (CostIs.provableWitness _) fun r => ?_
  refine CostIs.bind (costIs_assertion_implicitRangeCheck _ _ _ _) fun _ => ?_
  refine CostIs.bind (CostIs.assertZero _) fun _ => ?_
  refine CostIs.bind (CostIs.assertZero _) fun _ => ?_
  refine CostIs.bind (CostIs.assertZero _) fun _ => ?_
  refine CostIs.bind (costIs_assertion_normalize secpParams _) fun _ => ?_
  refine CostIs.bind (costIs_interpolatedMul _ _) fun Pc => ?_
  refine CostIs.bind
    (costIs_assertion_groupedEqXV secpParams.B gfMul posOfMul 5 vMul vMul hgvMul
      secpParams.hB1 _) fun _ => ?_
  exact CostIs.pure _

theorem costIs_sub_mulModLooseQ (b : Var (MulMod.Inputs numLimbs) (F circomPrime)) :
    CostIs (subcircuit MulModLooseQ.circuit b) mulModLooseQCount :=
  CostIs.subcircuit fun n => costIs_mulModLooseQ b n

private lemma affine_sVec_elem
    (q r nv : Var Emu (F circomPrime))
    (hq : AffineW q) (hr : AffineW r)
    (hnd : ∀ j (hj : j < numLimbs), degree nv[j] = 0)
    (i : ℕ) (hi : i < 2 * numLimbs - 1) :
    Affine ((Vector.mapFinRange (2 * numLimbs - 1) fun k : Fin (2 * numLimbs - 1) =>
        if h : k.val < numLimbs then (bigIntMulNoReduce q nv)[k.val] + r[k.val]'h
        else (bigIntMulNoReduce q nv)[k.val])[i]'hi) := by
  rw [Vector.getElem_mapFinRange]
  split
  · exact Affine.add (affineW_bigIntMulNoReduce _ _ hq hnd i hi) (hr i (by assumption))
  · exact affineW_bigIntMulNoReduce _ _ hq hnd i hi

theorem isR1CS_mulModLooseQ (input : Var (MulMod.Inputs numLimbs) (F circomPrime))
    (ha : AffineW input.a) (hb : AffineW input.b) (hn : AffineW input.modulus)
    (hnd : ∀ j (hj : j < numLimbs), degree input.modulus[j] = 0) :
    IsR1CSCirc (MulModLooseQ.main input) := by
  unfold MulModLooseQ.main
  refine IsR1CSCirc.bind_out (isR1CS_provableWitness_bigInt _) fun nq => ?_
  refine IsR1CSCirc.bind_out (isR1CS_provableWitness_bigInt _) fun nr => ?_
  refine IsR1CSCirc.bind (isR1CS_assertion_implicitRangeCheck _ _ _ _
    (affineW_provableWitness_bigInt _ nq 0 (by decide))) fun _ => ?_
  refine IsR1CSCirc.bind (IsR1CSCirc.assertZero
    (isR1CSRow_mul (affineW_provableWitness_bigInt _ nq 1 (by decide))
      (Affine.sub (affineW_provableWitness_bigInt _ nq 1 (by decide)) (Affine.const _))))
    fun _ => ?_
  refine IsR1CSCirc.bind (IsR1CSCirc.assertZero
    (isR1CSRow_of_affine (affineW_provableWitness_bigInt _ nq 2 (by decide)))) fun _ => ?_
  refine IsR1CSCirc.bind (IsR1CSCirc.assertZero
    (isR1CSRow_of_affine (affineW_provableWitness_bigInt _ nq 3 (by decide)))) fun _ => ?_
  refine IsR1CSCirc.bind
    (isR1CS_assertion_normalize secpParams _ (affineW_provableWitness_bigInt _ nr)) fun _ => ?_
  refine IsR1CSCirc.bind_out (isR1CS_interpolatedMul _ _ ha hb) fun nPc => ?_
  refine IsR1CSCirc.bind
    (isR1CS_assertion_groupedEqXV secpParams.B gfMul posOfMul 5 vMul vMul hgvMul
      secpParams.hB1 _ ?_ ?_) fun _ => ?_
  · exact affineW_interpolatedMul_output input.a input.b _
  · intro i hi
    exact affine_sVec_elem _ _ _ (affineW_provableWitness_bigInt _ nq)
      (affineW_provableWitness_bigInt _ nr) hnd i (by omega)
  exact IsR1CSCirc.pure _

theorem isR1CS_sub_mulModLooseQ (b : Var (MulMod.Inputs numLimbs) (F circomPrime))
    (ha : AffineW b.a) (hb : AffineW b.b) (hn : AffineW b.modulus)
    (hnd : ∀ j (hj : j < numLimbs), degree b.modulus[j] = 0) :
    IsR1CSCirc (subcircuit MulModLooseQ.circuit b) :=
  IsR1CSCirc.subcircuit fun n => isR1CS_mulModLooseQ b ha hb hn hnd n

theorem affineW_sub_mulModLooseQ (b : Var (MulMod.Inputs numLimbs) (F circomPrime)) (n : ℕ) :
    AffineW ((subcircuit MulModLooseQ.circuit b).output n) := by
  have h : ((subcircuit MulModLooseQ.circuit b).output n)
      = varFromOffset (BigInt numLimbs) (n + numLimbs) := by
    simp only [circuit_norm, subcircuit, MulModLooseQ.circuit, MulModLooseQ.elaborated]
  rw [h]
  exact affineW_varFromOffset _ _

end Cost
end Solution.Secp256k1ScalarMul
