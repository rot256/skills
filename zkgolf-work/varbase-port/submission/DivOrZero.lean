import Solution.Secp256k1ScalarMul.IsZeroFe
import Solution.Secp256k1ScalarMul.Mux
import Solution.Secp256k1ScalarMul.DivOrZeroTheorems
import Solution.Secp256k1ScalarMul.CompleteAddTheorems
import Solution.Secp256k1ScalarMul.AddMod
import Challenge.Utils.ComputableWitnessLemmas



namespace Solution.Secp256k1ScalarMul
namespace DivOrZero


structure Inputs (F : Type) where
  num : Emu F
  den : Emu F
deriving ProvableStruct

def main (input : Var Inputs (F circomPrime)) :
    Circuit (F circomPrime) (Var Emu (F circomPrime)) := do
  let { num, den } := input

  -- boolean zero flag of the denominator
  let z ← subcircuit IsZeroFe.circuit den

  -- guarded denominator/numerator: (1, 0) in the degenerate case
  let denSafe ← subcircuit (Mux.circuit (M := Emu))
    { selector := z, ifTrue := oneConst, ifFalse := den }
  let numSafe ← subcircuit (Mux.circuit (M := Emu))
    { selector := z, ifTrue := zeroConst, ifFalse := num }

  -- witness the quotient λ = num · den⁻¹ mod P256 (0 when den = 0)
  let lam ← ProvableType.witness (α := Emu) fun env =>
    let denFp : Specs.Secp256k1.Fp := ((evalEmu env den : ℕ) : Specs.Secp256k1.Fp)
    let numFp : Specs.Secp256k1.Fp := ((evalEmu env num : ℕ) : Specs.Secp256k1.Fp)
    emuOfNat (numFp * denFp⁻¹).val

  -- λ is normalized and canonical
  Normalize.circuit secpParams lam
  LessThan.circuit secpParams { lhs := lam, rhs := pConst }

  -- certify λ · denSafe ≡ numSafe (mod P256): the mux'd numerator limbs stand
  -- directly in the integer certificate (no remainder witness, no `Equal`)
  MulModTarget.circuit secpParams gfMul posOfMul 5 vMul vMul hgvMul hNfMul hNfMul
    { a := lam, b := denSafe, modulus := pConst, target := numSafe }

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
    MulModTarget.circuit, MulModTarget.Assumptions, MulModTarget.Spec,
    Normalize.circuit, Normalize.Assumptions, Normalize.Spec,
    LessThan.circuit, LessThan.Assumptions, LessThan.Spec]
  obtain ⟨h_num_valid, h_den_valid⟩ := h_assumptions
  obtain ⟨hz, hden, hnum, hlam_norm, hlt, hmul⟩ := h_holds
  simp only [secpParams_B] at hlam_norm hlt hmul
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
  · -- zero denominator: `λ · 1 ≡ 0` forces `λ = 0`
    rw [if_pos hd0] at hz
    rw [hz, if_pos rfl, eval_oneConst] at hden
    rw [hz, if_pos rfl, eval_zeroConst] at hnum
    rw [hden, value_emuOfNat_one] at hmul
    rw [hnum] at hmul
    have hspec := hmul ⟨hlam_norm, emuOfNat_normalized 1, hp_norm, emuOfNat_normalized 0,
      hlam_lt, one_lt_P256, by rw [value_emuOfNat_zero]; exact P256_pos, P256_pos⟩
    rw [value_emuOfNat_zero, mul_one, Nat.mod_eq_of_lt hlam_lt] at hspec
    exact ⟨⟨hlam_norm, hlam_lt⟩, fun h => absurd hd0 h,
      fun _ => decodeFe_of_value_eq_zero hspec.symm⟩
  · -- nonzero denominator: the target certificate gives `λ · den ≡ num (mod P256)`
    rw [if_neg hd0] at hz
    rw [hz, if_neg (zero_ne_one (α := F circomPrime))] at hden
    rw [hz, if_neg (zero_ne_one (α := F circomPrime))] at hnum
    rw [hden] at hmul
    rw [hnum] at hmul
    have hspec := hmul ⟨hlam_norm, h_den_valid.1, hp_norm, h_num_valid.1,
      hlam_lt, h_den_valid.2, h_num_valid.2, P256_pos⟩
    refine ⟨⟨hlam_norm, hlam_lt⟩, fun _ => ?_, fun h => absurd h hd0⟩
    simp only [decodeFe]
    exact mul_cast_of_mod_eq hspec.symm

theorem completeness : Completeness (F circomPrime) main Assumptions := by
  circuit_proof_start [IsZeroFe.circuit, IsZeroFe.Assumptions, IsZeroFe.Spec,
    Mux.circuit, Mux.Assumptions, Mux.Spec,
    MulModTarget.circuit, MulModTarget.Assumptions, MulModTarget.Spec,
    Normalize.circuit, Normalize.Assumptions, Normalize.Spec,
    LessThan.circuit, LessThan.Assumptions, LessThan.Spec]
  obtain ⟨h_num_valid, h_den_valid⟩ := h_assumptions
  obtain ⟨h_input_num, h_input_den⟩ := h_input
  obtain ⟨hz, hden, hnum, hlam⟩ := h_env
  simp only [secpParams_B]
  specialize hz h_den_valid
  have hz_bool : IsBool (env.get (i₀ + 2 + 2 + 2 + 2 + 1 + 1)) := by
    rw [hz]
    split
    · exact IsBool.one
    · exact IsBool.zero
  specialize hden hz_bool
  specialize hnum hz_bool
  -- the witnessed λ evaluates to the canonical quotient
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
  rw [hp_val]
  rw [hlam_val]
  by_cases hd0 : decodeFe input_den = 0
  · -- zero denominator: λ = 0 certifies against (1, 0)
    rw [if_pos hd0] at hz
    rw [hz, if_pos rfl, eval_oneConst] at hden
    rw [hz, if_pos rfl, eval_zeroConst] at hnum
    rw [hden, value_emuOfNat_one]
    rw [hnum, value_emuOfNat_zero] at *
    have hq0 : ZMod.val (((BigInt.value limbBits input_num : ℕ) : Specs.Secp256k1.Fp)
        * ((BigInt.value limbBits input_den : ℕ) : Specs.Secp256k1.Fp)⁻¹) = 0 := by
      simp only [decodeFe] at hd0
      rw [hd0]
      exact witness_val_den_zero _
    refine ⟨h_den_valid, hz_bool, hz_bool, hlam_norm, ⟨⟨hlam_norm, hp_norm⟩, hq_lt⟩,
      ⟨⟨hlam_norm, emuOfNat_normalized 1, hp_norm, emuOfNat_normalized 0,
        hq_lt, one_lt_P256, P256_pos, P256_pos⟩, ?_⟩⟩
    rw [hq0, Nat.zero_mul, Nat.zero_mod]
  · -- nonzero denominator: λ · den ≡ num certifies against (den, num)
    rw [if_neg hd0] at hz
    rw [hz, if_neg (zero_ne_one (α := F circomPrime))] at hden
    rw [hz, if_neg (zero_ne_one (α := F circomPrime))] at hnum
    rw [hden]
    rw [hnum] at *
    have hcert : ZMod.val (((BigInt.value limbBits input_num : ℕ) : Specs.Secp256k1.Fp)
        * ((BigInt.value limbBits input_den : ℕ) : Specs.Secp256k1.Fp)⁻¹)
          * BigInt.value limbBits input_den % P256 = BigInt.value limbBits input_num := by
      simp only [decodeFe] at hd0
      exact witness_cert_nonzero h_num_valid.2 hd0
    refine ⟨h_den_valid, hz_bool, hz_bool, hlam_norm, ⟨⟨hlam_norm, hp_norm⟩, hq_lt⟩,
      ⟨⟨hlam_norm, h_den_valid.1, hp_norm, h_num_valid.1,
        hq_lt, h_den_valid.2, h_num_valid.2, P256_pos⟩, ?_⟩⟩
    exact hcert.symm


def circuit : FormalCircuit (F circomPrime) Inputs Emu where
  main; elaborated; Assumptions; Spec; soundness; completeness

end DivOrZero



namespace DivOrZero3
open DivOrZero

def main (input : Var DivOrZero.Inputs (F circomPrime)) :
    Circuit (F circomPrime) (Var Emu (F circomPrime)) := do
  let { num, den } := input

  -- boolean zero flag of the denominator
  let z ← subcircuit IsZeroFe.circuit den

  -- guarded denominator/numerator: (1, 0) in the degenerate case
  let denSafe ← subcircuit (Mux.circuit (M := Emu))
    { selector := z, ifTrue := oneConst, ifFalse := den }
  let numSafe ← subcircuit (Mux.circuit (M := Emu))
    { selector := z, ifTrue := zeroConst, ifFalse := num }

  -- witness the quotient λ = num · den⁻¹ mod P256 (0 when den = 0)
  let lam ← ProvableType.witness (α := Emu) fun env =>
    let denFp : Specs.Secp256k1.Fp := ((evalEmu env den : ℕ) : Specs.Secp256k1.Fp)
    let numFp : Specs.Secp256k1.Fp := ((evalEmu env num : ℕ) : Specs.Secp256k1.Fp)
    emuOfNat (numFp * denFp⁻¹).val

  -- λ is normalized and canonical
  Normalize.circuit secpParams lam
  LessThan.circuit secpParams { lhs := lam, rhs := pConst }

  -- certify λ·denSafe + 3p = q·p + numSafe: the unreduced mux'd numerator
  -- limbs stand directly in the offset certificate
  MulModTarget3.circuit secpParams gfMul posOfMul 5 vMul vMul hgvMul hNfMul hNfMul
    threePLimbs (by decide)
    { a := lam, b := denSafe, modulus := pConst, target := numSafe }

  return lam

instance elaborated : ElaboratedCircuit (F circomPrime) DivOrZero.Inputs Emu main := by
  elaborate_circuit


def Assumptions (input : DivOrZero.Inputs (F circomPrime)) : Prop :=
  (∀ i : Fin numLimbs, (input.num[i.val]).val < 3 * 2 ^ limbBits) ∧
    BigInt.value limbBits input.num < 3 * P256 ∧
    Fe.Valid input.den


def Spec (input : DivOrZero.Inputs (F circomPrime)) (out : Emu (F circomPrime)) : Prop :=
  Fe.Valid out ∧
    (decodeFe input.den ≠ 0 →
      decodeFe out * decodeFe input.den = decodeFe input.num) ∧
    (decodeFe input.den = 0 → decodeFe out = 0)

theorem soundness : Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [IsZeroFe.circuit, IsZeroFe.Assumptions, IsZeroFe.Spec,
    Mux.circuit, Mux.Assumptions, Mux.Spec,
    MulModTarget3.circuit, MulModTarget3.Assumptions, MulModTarget3.Spec,
    Normalize.circuit, Normalize.Assumptions, Normalize.Spec,
    LessThan.circuit, LessThan.Assumptions, LessThan.Spec]
  obtain ⟨h_num_limb, h_num_val, h_den_valid⟩ := h_assumptions
  obtain ⟨hz, hden, hnum, hlam_norm, hlt, hmul⟩ := h_holds
  simp only [secpParams_B] at hlam_norm hlt hmul
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
  · -- zero denominator: `0 ≡ λ·1` forces `λ = 0`
    rw [if_pos hd0] at hz
    rw [hz, if_pos rfl, eval_oneConst] at hden
    rw [hz, if_pos rfl, eval_zeroConst] at hnum
    rw [hden, value_emuOfNat_one] at hmul
    rw [hnum] at hmul
    have hznum : ∀ i : Fin numLimbs,
        (env.get (i₀ + 11 + numLimbs + i.val)).val < 3 * 2 ^ limbBits := by
      intro i
      have hentry : (Vector.map (Expression.eval env)
          (Vector.mapRange numLimbs fun j => var { index := i₀ + 11 + numLimbs + j }))[i.val]'i.isLt
          = env.get (i₀ + 11 + numLimbs + i.val) := by
        simp [circuit_norm]
      have hcell : env.get (i₀ + 11 + numLimbs + i.val)
          = (emuOfNat 0 : Emu (F circomPrime))[i.val]'i.isLt := by
        rw [← hentry, hnum]
      rw [hcell]
      have h : ((emuOfNat 0 : Emu (F circomPrime))[i.val]'i.isLt).val < 2 ^ limbBits :=
        emuOfNat_normalized 0 i
      omega
    have hspec := hmul ⟨hlam_norm, emuOfNat_normalized 1, hp_norm,
      hznum,
      hlam_lt, one_lt_P256,
      (by rw [value_emuOfNat_zero]; have := P256_pos; omega),
      P256_pos, (by decide),
      CompleteAdd.threePLimbs_limb_lt, CompleteAdd.polyValue_threePLimbs⟩
    rw [value_emuOfNat_zero, mul_one, Nat.zero_mod] at hspec
    have hlam0 : BigInt.value limbBits (Vector.map (Expression.eval env)
        (Vector.mapRange numLimbs fun i => var { index := i₀ + 11 + numLimbs + numLimbs + i }))
        = 0 := by
      have := hspec.symm
      rwa [Nat.mod_eq_of_lt hlam_lt] at this
    exact ⟨⟨hlam_norm, hlam_lt⟩, fun h => absurd hd0 h,
      fun _ => decodeFe_of_value_eq_zero hlam0⟩
  · -- nonzero denominator: the offset certificate gives `λ·den ≡ num (mod P256)`
    rw [if_neg hd0] at hz
    rw [hz, if_neg (zero_ne_one (α := F circomPrime))] at hden
    rw [hz, if_neg (zero_ne_one (α := F circomPrime))] at hnum
    rw [hden] at hmul
    rw [hnum] at hmul
    have hnnum : ∀ i : Fin numLimbs,
        (env.get (i₀ + 11 + numLimbs + i.val)).val < 3 * 2 ^ limbBits := by
      intro i
      have hentry : (Vector.map (Expression.eval env)
          (Vector.mapRange numLimbs fun j => var { index := i₀ + 11 + numLimbs + j }))[i.val]'i.isLt
          = env.get (i₀ + 11 + numLimbs + i.val) := by
        simp [circuit_norm]
      have hcell : env.get (i₀ + 11 + numLimbs + i.val) = input_num[i.val]'i.isLt := by
        rw [← hentry, hnum]
      rw [hcell]
      exact h_num_limb i
    have hspec := hmul ⟨hlam_norm, h_den_valid.1, hp_norm,
      hnnum,
      hlam_lt, h_den_valid.2, h_num_val, P256_pos, (by decide),
      CompleteAdd.threePLimbs_limb_lt, CompleteAdd.polyValue_threePLimbs⟩
    refine ⟨⟨hlam_norm, hlam_lt⟩, fun _ => ?_, fun h => absurd h hd0⟩
    simp only [decodeFe]
    exact mul_cast_of_mod_eq3 hspec

theorem completeness : Completeness (F circomPrime) main Assumptions := by
  circuit_proof_start [IsZeroFe.circuit, IsZeroFe.Assumptions, IsZeroFe.Spec,
    Mux.circuit, Mux.Assumptions, Mux.Spec,
    MulModTarget3.circuit, MulModTarget3.Assumptions, MulModTarget3.Spec,
    Normalize.circuit, Normalize.Assumptions, Normalize.Spec,
    LessThan.circuit, LessThan.Assumptions, LessThan.Spec]
  obtain ⟨h_num_limb, h_num_val, h_den_valid⟩ := h_assumptions
  obtain ⟨h_input_num, h_input_den⟩ := h_input
  obtain ⟨hz, hden, hnum, hlam⟩ := h_env
  simp only [secpParams_B]
  specialize hz h_den_valid
  have hz_bool : IsBool (env.get (i₀ + 2 + 2 + 2 + 2 + 1 + 1)) := by
    rw [hz]
    split
    · exact IsBool.one
    · exact IsBool.zero
  specialize hden hz_bool
  specialize hnum hz_bool
  -- the witnessed λ evaluates to the canonical quotient
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
  rw [hp_val]
  rw [hlam_val]
  by_cases hd0 : decodeFe input_den = 0
  · -- zero denominator: λ = 0 certifies against (1, 0)
    rw [if_pos hd0] at hz
    rw [hz, if_pos rfl, eval_oneConst] at hden
    rw [hz, if_pos rfl, eval_zeroConst] at hnum
    have hznum : ∀ i : Fin numLimbs,
        (env.toEnvironment.get (i₀ + 11 + numLimbs + i.val)).val < 3 * 2 ^ limbBits := by
      intro i
      have hentry : (Vector.map (Expression.eval env.toEnvironment)
          (Vector.mapRange numLimbs fun j => var { index := i₀ + 11 + numLimbs + j }))[i.val]'i.isLt
          = env.toEnvironment.get (i₀ + 11 + numLimbs + i.val) := by
        simp [circuit_norm]
      have hcell : env.toEnvironment.get (i₀ + 11 + numLimbs + i.val)
          = (emuOfNat 0 : Emu (F circomPrime))[i.val]'i.isLt := by
        rw [← hentry, hnum]
      rw [hcell]
      have h : ((emuOfNat 0 : Emu (F circomPrime))[i.val]'i.isLt).val < 2 ^ limbBits :=
        emuOfNat_normalized 0 i
      omega
    rw [hden, value_emuOfNat_one]
    rw [hnum] at *
    have hq0 : ZMod.val (((BigInt.value limbBits input_num : ℕ) : Specs.Secp256k1.Fp)
        * ((BigInt.value limbBits input_den : ℕ) : Specs.Secp256k1.Fp)⁻¹) = 0 := by
      simp only [decodeFe] at hd0
      rw [hd0]
      exact witness_val_den_zero _
    refine ⟨h_den_valid, hz_bool, hz_bool, hlam_norm, ⟨⟨hlam_norm, hp_norm⟩, hq_lt⟩,
      ⟨⟨hlam_norm, emuOfNat_normalized 1, hp_norm,
        hznum,
        hq_lt, one_lt_P256,
        (by rw [value_emuOfNat_zero]; have := P256_pos; omega),
        P256_pos, (by decide),
        CompleteAdd.threePLimbs_limb_lt, CompleteAdd.polyValue_threePLimbs⟩, ?_⟩⟩
    rw [hq0, Nat.zero_mul, Nat.zero_mod, value_emuOfNat_zero, Nat.zero_mod]
  · -- nonzero denominator: λ·den ≡ num certifies against (den, num)
    rw [if_neg hd0] at hz
    rw [hz, if_neg (zero_ne_one (α := F circomPrime))] at hden
    rw [hz, if_neg (zero_ne_one (α := F circomPrime))] at hnum
    have hnnum : ∀ i : Fin numLimbs,
        (env.toEnvironment.get (i₀ + 11 + numLimbs + i.val)).val < 3 * 2 ^ limbBits := by
      intro i
      have hentry : (Vector.map (Expression.eval env.toEnvironment)
          (Vector.mapRange numLimbs fun j =>
            var { index := i₀ + 11 + numLimbs + j }))[i.val]'i.isLt
          = env.toEnvironment.get (i₀ + 11 + numLimbs + i.val) := by
        simp [circuit_norm]
      have hcell : env.toEnvironment.get (i₀ + 11 + numLimbs + i.val)
          = input_num[i.val]'i.isLt := by
        rw [← hentry, hnum]
      rw [hcell]
      exact h_num_limb i
    rw [hden]
    rw [hnum] at *
    have hcert : BigInt.value limbBits input_num % P256
        = ZMod.val (((BigInt.value limbBits input_num : ℕ) : Specs.Secp256k1.Fp)
            * ((BigInt.value limbBits input_den : ℕ) : Specs.Secp256k1.Fp)⁻¹)
          * BigInt.value limbBits input_den % P256 := by
      simp only [decodeFe] at hd0
      exact witness_cert_nonzero3 hd0
    refine ⟨h_den_valid, hz_bool, hz_bool, hlam_norm, ⟨⟨hlam_norm, hp_norm⟩, hq_lt⟩,
      ⟨⟨hlam_norm, h_den_valid.1, hp_norm,
        hnnum,
        hq_lt, h_den_valid.2, h_num_val, P256_pos, (by decide),
        CompleteAdd.threePLimbs_limb_lt, CompleteAdd.polyValue_threePLimbs⟩, ?_⟩⟩
    exact hcert


def circuit : FormalCircuit (F circomPrime) DivOrZero.Inputs Emu where
  main; elaborated; Assumptions; Spec; soundness; completeness

end DivOrZero3
end Solution.Secp256k1ScalarMul



namespace Solution.Secp256k1ScalarMul
namespace DivOrZero3
open DivOrZero AddMod


theorem computableWitnesses : circuit.base.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  obtain ⟨num, den⟩ := input
  have hz : ∀ (o : ℕ), (subcircuit IsZeroFe.circuit den).localLength o = 11 := by
    intro o; simp only [circuit_norm, IsZeroFe.circuit]
  have hmx : ∀ (X : Var (Mux.Inputs Emu) (F circomPrime)) (o : ℕ),
      (subcircuit (Mux.circuit (M := Emu)) X).localLength o = numLimbs := by
    intro X o; simp only [circuit_norm, Mux.circuit]
  have hw : ∀ (c : ProverEnvironment (F circomPrime) → Emu (F circomPrime)) (o : ℕ),
      (ProvableType.witness (α := Emu) c).localLength o = numLimbs := by
    intro c o; simp only [circuit_norm]
  have hsize : size Emu = numLimbs := rfl
  have hnl : ∀ (x : Var Emu (F circomPrime)) (o : ℕ),
      (Normalize.circuit secpParams x).localLength o = numLimbs * (secpParams.B - 1) := fun _ _ => rfl
  have hltl : ∀ (X : Var (LessThan.Inputs numLimbs) (F circomPrime)) (o : ℕ),
      (LessThan.circuit secpParams X).localLength o
        = numLimbs + numLimbs * (secpParams.B - 1) + numLimbs := fun _ _ => rfl
  have hmux_in : ∀ (e e' : ProverEnvironment (F circomPrime))
      (s : Var field (F circomPrime)) (cst f : Var Emu (F circomPrime)),
      Expression.eval e.toEnvironment s = Expression.eval e'.toEnvironment s →
      Vector.map (Expression.eval e.toEnvironment) cst
        = Vector.map (Expression.eval e'.toEnvironment) cst →
      Vector.map (Expression.eval e.toEnvironment) f
        = Vector.map (Expression.eval e'.toEnvironment) f →
      eval e ({ selector := s, ifTrue := cst, ifFalse := f } : Var (Mux.Inputs Emu) (F circomPrime))
        = eval e' ({ selector := s, ifTrue := cst, ifFalse := f } : Var (Mux.Inputs Emu) (F circomPrime)) := by
    intro e e' s cst f hs hcst hf
    simp only [circuit_norm]
    simp only [hs, hcst, hf]
  unfold main
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.provableWitness_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.pure_structuralComputableWitnesses_iff,
    hz, hmx, hw, hnl, hltl, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- z ← IsZeroFe den : input is the raw denominator
    exact Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses
      (Parent := DivOrZero.Inputs) IsZeroFe.circuit _ den offset
      (fun e e' h => by
        have hden := congrArg (fun x : DivOrZero.Inputs (F circomPrime) => x.den) h
        simpa [circuit_norm] using hden)
      IsZeroFe.computableWitnesses env env'
  · -- denSafe ← Mux { z, oneConst, den }
    exact Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := DivOrZero.Inputs) (Mux.circuit (M := Emu)) _
      { selector := (subcircuit IsZeroFe.circuit den).output offset,
        ifTrue := oneConst, ifFalse := den }
      (offset + 11)
      (by
        intro k e e' hle h_agree h_in
        have hsel := IsZeroFe.eval_output_of_agreesBelow den (offset := offset) h_agree (by omega)
        rw [CircuitType.eval_var_field_prover, CircuitType.eval_var_field_prover] at hsel
        have hden := congrArg (fun x : DivOrZero.Inputs (F circomPrime) => x.den) h_in
        have hden' : Vector.map (Expression.eval e.toEnvironment) den
            = Vector.map (Expression.eval e'.toEnvironment) den := by
          simpa [circuit_norm] using hden
        exact hmux_in e e' _ oneConst den hsel (by rw [eval_oneConst, eval_oneConst]) hden')
      (Mux.computableWitnesses (M := Emu)) env env'
  · -- numSafe ← Mux { z, zeroConst, num }
    exact Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := DivOrZero.Inputs) (Mux.circuit (M := Emu)) _
      { selector := (subcircuit IsZeroFe.circuit den).output offset,
        ifTrue := zeroConst, ifFalse := num }
      (offset + 11 + numLimbs)
      (by
        intro k e e' hle h_agree h_in
        have hsel := IsZeroFe.eval_output_of_agreesBelow den (offset := offset) h_agree (by omega)
        rw [CircuitType.eval_var_field_prover, CircuitType.eval_var_field_prover] at hsel
        have hnum := congrArg (fun x : DivOrZero.Inputs (F circomPrime) => x.num) h_in
        have hnum' : Vector.map (Expression.eval e.toEnvironment) num
            = Vector.map (Expression.eval e'.toEnvironment) num := by
          simpa [circuit_norm] using hnum
        exact hmux_in e e' _ zeroConst num hsel (by rw [eval_zeroConst, eval_zeroConst]) hnum')
      (Mux.computableWitnesses (M := Emu)) env env'
  · -- λ witness : reads only the raw input limbs (via evalEmu)
    intro _ h_input
    have hden : evalEmu env den = evalEmu env' den :=
      evalEmu_eq_of_eval_eq (by
        simpa [circuit_norm] using
          congrArg (fun x : DivOrZero.Inputs (F circomPrime) => x.den) h_input)
    have hnum : evalEmu env num = evalEmu env' num :=
      evalEmu_eq_of_eval_eq (by
        simpa [circuit_norm] using
          congrArg (fun x : DivOrZero.Inputs (F circomPrime) => x.num) h_input)
    simp only [hden, hnum]
  · -- Normalize λ
    exact Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
      (Parent := DivOrZero.Inputs) (Normalize.circuit secpParams) _
      ((ProvableType.witness (α := Emu) fun env =>
        let denFp : Specs.Secp256k1.Fp := ((evalEmu env den : ℕ) : Specs.Secp256k1.Fp)
        let numFp : Specs.Secp256k1.Fp := ((evalEmu env num : ℕ) : Specs.Secp256k1.Fp)
        emuOfNat (numFp * denFp⁻¹).val).output (offset + 11 + numLimbs + numLimbs))
      _
      (by
        intro k e e' hle h_agree _
        exact emuWitnessOutput_stable _ h_agree
          (offset := offset + 11 + numLimbs + numLimbs) (by omega))
      (Normalize.computableWitnesses secpParams) env env'
  · -- LessThan { λ, pConst }
    exact Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
      (Parent := DivOrZero.Inputs) (LessThan.circuit secpParams) _
      { lhs := (ProvableType.witness (α := Emu) fun env =>
          let denFp : Specs.Secp256k1.Fp := ((evalEmu env den : ℕ) : Specs.Secp256k1.Fp)
          let numFp : Specs.Secp256k1.Fp := ((evalEmu env num : ℕ) : Specs.Secp256k1.Fp)
          emuOfNat (numFp * denFp⁻¹).val).output (offset + 11 + numLimbs + numLimbs),
        rhs := pConst }
      _
      (by
        intro k e e' hle h_agree _
        have hlam := emuWitnessOutput_stable
          (fun env =>
            let denFp : Specs.Secp256k1.Fp := ((evalEmu env den : ℕ) : Specs.Secp256k1.Fp)
            let numFp : Specs.Secp256k1.Fp := ((evalEmu env num : ℕ) : Specs.Secp256k1.Fp)
            emuOfNat (numFp * denFp⁻¹).val)
          h_agree (offset := offset + 11 + numLimbs + numLimbs) (k := k) (by omega)
        simp only [circuit_norm] at hlam ⊢
        simp only [hlam, eval_pConst])
      (LessThan.computableWitnesses secpParams) env env'
  · -- MulModTarget3 { λ, denSafe, pConst, numSafe }
    exact Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
      (Parent := DivOrZero.Inputs)
      (MulModTarget3.circuit secpParams gfMul posOfMul 5 vMul vMul hgvMul hNfMul hNfMul
        threePLimbs (by decide)) _
      { a := (ProvableType.witness (α := Emu) fun env =>
          let denFp : Specs.Secp256k1.Fp := ((evalEmu env den : ℕ) : Specs.Secp256k1.Fp)
          let numFp : Specs.Secp256k1.Fp := ((evalEmu env num : ℕ) : Specs.Secp256k1.Fp)
          emuOfNat (numFp * denFp⁻¹).val).output (offset + 11 + numLimbs + numLimbs),
        b := (subcircuit (Mux.circuit (M := Emu))
          { selector := (subcircuit IsZeroFe.circuit den).output offset,
            ifTrue := oneConst, ifFalse := den }).output (offset + 11),
        modulus := pConst,
        target := (subcircuit (Mux.circuit (M := Emu))
          { selector := (subcircuit IsZeroFe.circuit den).output offset,
            ifTrue := zeroConst, ifFalse := num }).output (offset + 11 + numLimbs) }
      _
      (by
        intro k e e' hle h_agree _
        have hlam := emuWitnessOutput_stable
          (fun env =>
            let denFp : Specs.Secp256k1.Fp := ((evalEmu env den : ℕ) : Specs.Secp256k1.Fp)
            let numFp : Specs.Secp256k1.Fp := ((evalEmu env num : ℕ) : Specs.Secp256k1.Fp)
            emuOfNat (numFp * denFp⁻¹).val)
          h_agree (offset := offset + 11 + numLimbs + numLimbs) (k := k) (by omega)
        have hden := Mux.eval_output_of_agreesBelow (M := Emu)
          { selector := (subcircuit IsZeroFe.circuit den).output offset,
            ifTrue := oneConst, ifFalse := den }
          h_agree (offset := offset + 11) (k := k) (by omega)
        have hnum := Mux.eval_output_of_agreesBelow (M := Emu)
          { selector := (subcircuit IsZeroFe.circuit den).output offset,
            ifTrue := zeroConst, ifFalse := num }
          h_agree (offset := offset + 11 + numLimbs) (k := k) (by omega)
        simp only [circuit_norm]
        congr 1
        · exact emu_map_eval_eq_of_eval_eq hlam
        · exact emu_map_eval_eq_of_eval_eq hden
        · rw [eval_pConst, eval_pConst]
        · exact emu_map_eval_eq_of_eval_eq hnum)
      (MulModTarget3.computableWitnesses secpParams gfMul posOfMul 5 vMul vMul hgvMul
        hNfMul hNfMul threePLimbs (by decide)) env env'

theorem computableWitness : ∀ n input,
    ProverEnvironment.OnlyAccessedBelow n
      (fun env : ProverEnvironment (F circomPrime) => eval env input) →
    Circuit.ComputableWitnesses (main input) n := by
  exact Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnesses_implies
    (circuit := circuit.base) computableWitnesses


lemma eval_output_of_agreesBelow (input : Var DivOrZero.Inputs (F circomPrime)) {offset k : ℕ}
    {env env' : ProverEnvironment (F circomPrime)}
    (h_agree : env.AgreesBelow k env')
    (hk : offset + 11 + numLimbs + numLimbs + numLimbs ≤ k) :
    eval env ((main input).output offset) = eval env' ((main input).output offset) := by
  obtain ⟨num, den⟩ := input
  have hout : (main ⟨num, den⟩).output offset
      = (ProvableType.witness (α := Emu) fun env =>
          let denFp : Specs.Secp256k1.Fp := ((evalEmu env den : ℕ) : Specs.Secp256k1.Fp)
          let numFp : Specs.Secp256k1.Fp := ((evalEmu env num : ℕ) : Specs.Secp256k1.Fp)
          emuOfNat (numFp * denFp⁻¹).val).output (offset + 11 + numLimbs + numLimbs) := rfl
  rw [hout]
  exact emuWitnessOutput_stable _ h_agree (by omega)

end DivOrZero3
end Solution.Secp256k1ScalarMul
