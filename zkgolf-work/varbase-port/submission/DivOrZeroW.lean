import Solution.Secp256k1ScalarMul.DivOrZero
import Solution.Secp256k1ScalarMul.IsZeroFeSum
import Solution.Secp256k1ScalarMul.ParamsW
import Solution.Secp256k1ScalarMul.MulModTargetW



namespace Solution.Secp256k1ScalarMul

namespace DivOrZeroW
open DivOrZero


structure Output (F : Type) where
  lam : Emu F
  isZero : F
deriving ProvableStruct

def main (input : Var DivOrZero.Inputs (F circomPrime)) :
    Circuit (F circomPrime) (Var Output (F circomPrime)) := do
  let { num := x, den } := input

  -- boolean zero flag of the denominator
  let z ← subcircuit IsZeroFeSum.circuit den

  -- guarded denominator/coordinate: (1, 0) in the degenerate case
  let denSafe ← subcircuit (Mux.circuit (M := Emu))
    { selector := z, ifTrue := oneConst, ifFalse := den }
  let xSafe ← subcircuit (Mux.circuit (M := Emu))
    { selector := z, ifTrue := zeroConst, ifFalse := x }

  -- witness the slope λ = 3x² · den⁻¹ mod P256 (0 when den = 0)
  let lam ← ProvableType.witness (α := Emu) fun env =>
    let denFp : Specs.Secp256k1.Fp := ((evalEmu env den : ℕ) : Specs.Secp256k1.Fp)
    let numFp : Specs.Secp256k1.Fp :=
      ((3 * (evalEmu env x * evalEmu env x) : ℕ) : Specs.Secp256k1.Fp)
    emuOfNat (numFp * denFp⁻¹).val

  -- λ is normalized and canonical, using the sparse shape of secp256k1's p.
  ValidP.circuit lam

  -- certify λ·denSafe + 3p² = q·p + 3(xSafe ⊛ xSafe): the square is
  -- interpolated inside the certificate, never reduced
  MulModTargetW.circuit secpParams gfMulD posOfMulD 5 vW vrW hgvW hNfW hNfrW
    threeP2Limbs (by decide) (by decide)
    { a := lam, b := denSafe, modulus := pConst, target := xSafe }

  return { lam, isZero := z }

instance elaborated : ElaboratedCircuit (F circomPrime) DivOrZero.Inputs Output main := by
  elaborate_circuit


def Assumptions (input : DivOrZero.Inputs (F circomPrime)) : Prop :=
  Fe.Valid input.num ∧
    BigInt.Normalized (limbBits + 1) input.den ∧
    BigInt.value limbBits input.den < 2 * P256 ∧
    (BigInt.value limbBits input.den % P256 = 0 → BigInt.value limbBits input.den = 0)


def Spec (input : DivOrZero.Inputs (F circomPrime)) (out : Output (F circomPrime)) : Prop :=
  Fe.Valid out.lam ∧
    (decodeFe input.den ≠ 0 →
      decodeFe out.lam * decodeFe input.den = 3 * (decodeFe input.num * decodeFe input.num)) ∧
    (decodeFe input.den = 0 → decodeFe out.lam = 0) ∧
    out.isZero = if decodeFe input.den = 0 then 1 else 0

theorem soundness : Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [IsZeroFeSum.circuit, IsZeroFeSum.Assumptions, IsZeroFeSum.Spec,
    Mux.circuit, Mux.Assumptions, Mux.Spec,
    MulModTargetW.circuit, MulModTargetW.Assumptions, MulModTargetW.Spec,
    ValidP.circuit, ValidP.main, ValidP.Assumptions, ValidP.Spec]
  obtain ⟨h_x_valid, h_den_limb, h_den_val, h_den_alias⟩ := h_assumptions
  have h_den_bound : IsZeroFeSum.Assumptions input_den := by
    intro i
    have hi := h_den_limb i
    rw [Fin.getElem_fin] at hi
    have hle : 2 ^ (limbBits + 1) ≤ 3 * 2 ^ limbBits := by rw [pow_succ]; omega
    omega
  obtain ⟨hz, hden, hnum, hlam_valid, hmul⟩ := h_holds
  specialize hz h_den_bound
  simp only [secpParams_B] at hmul
  have hlam_norm := hlam_valid.1
  have hd_iff : decodeFe input_den = 0 ↔ BigInt.value limbBits input_den = 0 := by
    constructor
    · intro h
      apply h_den_alias
      have hdvd : (P256 : ℕ) ∣ BigInt.value limbBits input_den := by
        exact (ZMod.natCast_eq_zero_iff _ _).mp (by simpa [decodeFe] using h)
      rcases hdvd with ⟨k, hk⟩
      rw [hk]
      exact Nat.mul_mod_right _ _
    · intro h
      simp [decodeFe, h]
  have hz_bool : IsBool (env.get (i₀ + 1)) := by
    rw [hz]
    split
    · exact IsBool.one
    · exact IsBool.zero
  specialize hden hz_bool
  specialize hnum hz_bool
  have hp_norm := pConst_normalized env
  have hp_val := pConst_value env
  have hlam_lt := hlam_valid.2
  rw [hp_val] at hmul
  by_cases hd0 : decodeFe input_den = 0
  · -- zero denominator: `3·0² ≡ λ·1` forces `λ = 0`
    rw [if_pos (hd_iff.mp hd0)] at hz
    rw [hz, if_pos rfl, eval_oneConst] at hden
    rw [hz, if_pos rfl, eval_zeroConst] at hnum
    rw [hden, value_emuOfNat_one] at hmul
    rw [hnum] at hmul
    have hspec := hmul ⟨hlam_norm,
      (fun i => lt_of_lt_of_le (emuOfNat_normalized 1 i)
        (Nat.pow_le_pow_right (by norm_num) (by omega))), hp_norm,
      emuOfNat_normalized 0,
      hlam_lt, (by have := P256_pos; omega),
      (by rw [value_emuOfNat_zero]; exact P256_pos),
      P256_pos, (by decide),
      threeP2Limbs_limb_lt, polyValue_threeP2Limbs⟩
    simp only [value_emuOfNat_zero, Nat.mul_zero, Nat.zero_mod, mul_one] at hspec
    have hlam0 : BigInt.value limbBits (Vector.map (Expression.eval env)
        (Vector.mapRange numLimbs fun i => var { index := i₀ + 2 + numLimbs + numLimbs + i }))
        = 0 := by
      have := hspec.symm
      rwa [Nat.mod_eq_of_lt hlam_lt] at this
    exact ⟨⟨hlam_norm, hlam_lt⟩, fun h => absurd hd0 h,
      fun _ => decodeFe_of_value_eq_zero hlam0, by simpa [hd0] using hz⟩
  · -- nonzero denominator: the certificate gives `λ·den ≡ 3x² (mod P256)`
    rw [if_neg (fun h => hd0 (hd_iff.mpr h))] at hz
    rw [hz, if_neg (zero_ne_one (α := F circomPrime))] at hden
    rw [hz, if_neg (zero_ne_one (α := F circomPrime))] at hnum
    rw [hden] at hmul
    rw [hnum] at hmul
    have hspec := hmul ⟨hlam_norm, h_den_limb, hp_norm,
      h_x_valid.1,
      hlam_lt, h_den_val, h_x_valid.2, P256_pos, (by decide),
      threeP2Limbs_limb_lt, polyValue_threeP2Limbs⟩
    refine ⟨⟨hlam_norm, hlam_lt⟩, fun _ => ?_, fun h => absurd h hd0, ?_⟩
    simp only [decodeFe]
    rw [mul_cast_of_mod_eq3 hspec]
    push_cast
    ring
    simpa [hd0] using hz

theorem completeness : Completeness (F circomPrime) main Assumptions := by
  circuit_proof_start [IsZeroFeSum.circuit, IsZeroFeSum.Assumptions, IsZeroFeSum.Spec,
    Mux.circuit, Mux.Assumptions, Mux.Spec,
    MulModTargetW.circuit, MulModTargetW.Assumptions, MulModTargetW.Spec,
    ValidP.circuit, ValidP.main, ValidP.Assumptions, ValidP.Spec]
  obtain ⟨h_x_valid, h_den_limb, h_den_val, h_den_alias⟩ := h_assumptions
  have h_den_bound : IsZeroFeSum.Assumptions input_den := by
    intro i
    have hi := h_den_limb i
    rw [Fin.getElem_fin] at hi
    have hle : 2 ^ (limbBits + 1) ≤ 3 * 2 ^ limbBits := by rw [pow_succ]; omega
    omega
  obtain ⟨h_input_num, h_input_den⟩ := h_input
  obtain ⟨hz, hden, hnum, hlam⟩ := h_env
  specialize hz h_den_bound
  simp only [secpParams_B]
  have hd_iff : decodeFe input_den = 0 ↔ BigInt.value limbBits input_den = 0 := by
    constructor
    · intro h
      apply h_den_alias
      have hdvd : (P256 : ℕ) ∣ BigInt.value limbBits input_den := by
        exact (ZMod.natCast_eq_zero_iff _ _).mp (by simpa [decodeFe] using h)
      rcases hdvd with ⟨k, hk⟩
      rw [hk]
      exact Nat.mul_mod_right _ _
    · intro h
      simp [decodeFe, h]
  have hz_bool : IsBool (env.get (i₀ + 1)) := by
    rw [hz]
    split
    · exact IsBool.one
    · exact IsBool.zero
  specialize hden hz_bool
  specialize hnum hz_bool
  -- the witnessed λ evaluates to the canonical fused quotient
  have hev_num : evalEmu env input_var_num = BigInt.value limbBits input_num := by
    rw [evalEmu, BigInt.value, ← h_input_num]
  have hev_den : evalEmu env input_var_den = BigInt.value limbBits input_den := by
    rw [evalEmu, BigInt.value, ← h_input_den]
  have hlam_eval : Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange numLimbs fun i => var { index := i₀ + 2 + numLimbs + numLimbs + i })
      = emuOfNat (ZMod.val
          (((3 * (BigInt.value limbBits input_num * BigInt.value limbBits input_num) : ℕ)
              : Specs.Secp256k1.Fp)
            * ((BigInt.value limbBits input_den : ℕ) : Specs.Secp256k1.Fp)⁻¹)) := by
    rw [← hev_num, ← hev_den]
    apply Vector.ext
    intro k hk
    have hentry : (Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange numLimbs fun i => var { index := i₀ + 2 + numLimbs + numLimbs + i }))[k]'hk
        = env.get (i₀ + 2 + numLimbs + numLimbs + k) := by
      simp [circuit_norm]
    rw [hentry]
    exact hlam ⟨k, hk⟩
  have hq_lt : ZMod.val
      (((3 * (BigInt.value limbBits input_num * BigInt.value limbBits input_num) : ℕ)
          : Specs.Secp256k1.Fp)
        * ((BigInt.value limbBits input_den : ℕ) : Specs.Secp256k1.Fp)⁻¹) < P256 :=
    ZMod.val_lt _
  have hlam_norm : BigInt.Normalized limbBits (Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange numLimbs fun i => var { index := i₀ + 2 + numLimbs + numLimbs + i })) := by
    rw [hlam_eval]
    exact emuOfNat_normalized _
  have hlam_val : BigInt.value limbBits (Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange numLimbs fun i => var { index := i₀ + 2 + numLimbs + numLimbs + i }))
      = ZMod.val
          (((3 * (BigInt.value limbBits input_num * BigInt.value limbBits input_num) : ℕ)
              : Specs.Secp256k1.Fp)
            * ((BigInt.value limbBits input_den : ℕ) : Specs.Secp256k1.Fp)⁻¹) := by
    rw [hlam_eval]
    exact value_emuOfNat (lt_trans hq_lt P256_lt)
  have hp_norm := pConst_normalized env.toEnvironment
  have hp_val := pConst_value env.toEnvironment
  rw [hp_val]
  rw [hlam_val]
  by_cases hd0 : decodeFe input_den = 0
  · -- zero denominator: λ = 0 certifies against (1, 0)
    rw [if_pos (hd_iff.mp hd0)] at hz
    rw [hz, if_pos rfl, eval_oneConst] at hden
    rw [hz, if_pos rfl, eval_zeroConst] at hnum
    rw [hden, value_emuOfNat_one]
    rw [hnum] at *
    have hq0 : ZMod.val
        (((3 * (BigInt.value limbBits input_num * BigInt.value limbBits input_num) : ℕ)
            : Specs.Secp256k1.Fp)
          * ((BigInt.value limbBits input_den : ℕ) : Specs.Secp256k1.Fp)⁻¹) = 0 := by
      simp only [decodeFe] at hd0
      rw [hd0]
      exact witness_val_den_zero _
    refine ⟨h_den_bound, hz_bool, hz_bool, ⟨hlam_norm, by rw [hlam_val]; exact hq_lt⟩,
      ⟨⟨hlam_norm, (fun i => lt_of_lt_of_le (emuOfNat_normalized 1 i)
          (Nat.pow_le_pow_right (by norm_num) (by omega))), hp_norm,
        emuOfNat_normalized 0,
        hq_lt, (by have := P256_pos; omega),
        (by rw [value_emuOfNat_zero]; exact P256_pos),
        P256_pos, (by decide),
        threeP2Limbs_limb_lt, polyValue_threeP2Limbs⟩, ?_⟩⟩
    simp only [hq0, Nat.zero_mod, value_emuOfNat_zero, Nat.mul_zero, mul_one]
  · -- nonzero denominator: λ·den ≡ 3x² certifies against (den, x)
    rw [if_neg (fun h => hd0 (hd_iff.mpr h))] at hz
    rw [hz, if_neg (zero_ne_one (α := F circomPrime))] at hden
    rw [hz, if_neg (zero_ne_one (α := F circomPrime))] at hnum
    rw [hden]
    rw [hnum] at *
    have hcert : 3 * (BigInt.value limbBits input_num * BigInt.value limbBits input_num) % P256
        = ZMod.val
            (((3 * (BigInt.value limbBits input_num * BigInt.value limbBits input_num) : ℕ)
                : Specs.Secp256k1.Fp)
              * ((BigInt.value limbBits input_den : ℕ) : Specs.Secp256k1.Fp)⁻¹)
          * BigInt.value limbBits input_den % P256 := by
      simp only [decodeFe] at hd0
      exact witness_cert_nonzero3 hd0
    refine ⟨h_den_bound, hz_bool, hz_bool, ⟨hlam_norm, by rw [hlam_val]; exact hq_lt⟩,
      ⟨⟨hlam_norm, h_den_limb, hp_norm,
        h_x_valid.1,
        hq_lt, h_den_val, h_x_valid.2, P256_pos, (by decide),
        threeP2Limbs_limb_lt, polyValue_threeP2Limbs⟩, ?_⟩⟩
    exact hcert


def circuit : FormalCircuit (F circomPrime) DivOrZero.Inputs Output where
  main; elaborated; Assumptions; Spec; soundness; completeness

end DivOrZeroW
end Solution.Secp256k1ScalarMul



namespace Solution.Secp256k1ScalarMul
namespace DivOrZeroW
open DivOrZero AddMod


theorem computableWitnesses : circuit.base.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  obtain ⟨x, den⟩ := input
  have hz : ∀ (o : ℕ), (subcircuit IsZeroFeSum.circuit den).localLength o = 2 := by
    intro o; simp only [circuit_norm, IsZeroFeSum.circuit]
  have hmx : ∀ (X : Var (Mux.Inputs Emu) (F circomPrime)) (o : ℕ),
      (subcircuit (Mux.circuit (M := Emu)) X).localLength o = numLimbs := by
    intro X o; simp only [circuit_norm, Mux.circuit]
  have hw : ∀ (c : ProverEnvironment (F circomPrime) → Emu (F circomPrime)) (o : ℕ),
      (ProvableType.witness (α := Emu) c).localLength o = numLimbs := by
    intro c o; simp only [circuit_norm]
  have hsize : size Emu = numLimbs := rfl
  have hvp : ∀ (v : Var Emu (F circomPrime)) (o : ℕ),
      (ValidP.circuit v).localLength o = 260 := fun _ _ => rfl
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
    hz, hmx, hw, hvp, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- z ← IsZeroFe den : input is the raw denominator
    exact Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses
      (Parent := DivOrZero.Inputs) IsZeroFeSum.circuit _ den offset
      (fun e e' h => by
        have hden := congrArg (fun v : DivOrZero.Inputs (F circomPrime) => v.den) h
        simpa [circuit_norm] using hden)
      IsZeroFeSum.computableWitnesses env env'
  · -- denSafe ← Mux { z, oneConst, den }
    exact Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := DivOrZero.Inputs) (Mux.circuit (M := Emu)) _
      { selector := (subcircuit IsZeroFeSum.circuit den).output offset,
        ifTrue := oneConst, ifFalse := den }
      (offset + 2)
      (by
        intro k e e' hle h_agree h_in
        have hsel := IsZeroFeSum.eval_output_of_agreesBelow den (offset := offset) h_agree (by omega)
        rw [CircuitType.eval_var_field_prover, CircuitType.eval_var_field_prover] at hsel
        have hden := congrArg (fun v : DivOrZero.Inputs (F circomPrime) => v.den) h_in
        have hden' : Vector.map (Expression.eval e.toEnvironment) den
            = Vector.map (Expression.eval e'.toEnvironment) den := by
          simpa [circuit_norm] using hden
        exact hmux_in e e' _ oneConst den hsel (by rw [eval_oneConst, eval_oneConst]) hden')
      (Mux.computableWitnesses (M := Emu)) env env'
  · -- xSafe ← Mux { z, zeroConst, x }
    exact Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := DivOrZero.Inputs) (Mux.circuit (M := Emu)) _
      { selector := (subcircuit IsZeroFeSum.circuit den).output offset,
        ifTrue := zeroConst, ifFalse := x }
      (offset + 2 + numLimbs)
      (by
        intro k e e' hle h_agree h_in
        have hsel := IsZeroFeSum.eval_output_of_agreesBelow den (offset := offset) h_agree (by omega)
        rw [CircuitType.eval_var_field_prover, CircuitType.eval_var_field_prover] at hsel
        have hx := congrArg (fun v : DivOrZero.Inputs (F circomPrime) => v.num) h_in
        have hx' : Vector.map (Expression.eval e.toEnvironment) x
            = Vector.map (Expression.eval e'.toEnvironment) x := by
          simpa [circuit_norm] using hx
        exact hmux_in e e' _ zeroConst x hsel (by rw [eval_zeroConst, eval_zeroConst]) hx')
      (Mux.computableWitnesses (M := Emu)) env env'
  · -- λ witness : reads only the raw input limbs (via evalEmu)
    intro _ h_input
    have hden : evalEmu env den = evalEmu env' den :=
      evalEmu_eq_of_eval_eq (by
        simpa [circuit_norm] using
          congrArg (fun v : DivOrZero.Inputs (F circomPrime) => v.den) h_input)
    have hx : evalEmu env x = evalEmu env' x :=
      evalEmu_eq_of_eval_eq (by
        simpa [circuit_norm] using
          congrArg (fun v : DivOrZero.Inputs (F circomPrime) => v.num) h_input)
    simp only [hden, hx]
  · -- Sparse canonical validation of λ
    exact Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
      (Parent := DivOrZero.Inputs) ValidP.circuit _
      ((ProvableType.witness (α := Emu) fun env =>
        let denFp : Specs.Secp256k1.Fp := ((evalEmu env den : ℕ) : Specs.Secp256k1.Fp)
        let numFp : Specs.Secp256k1.Fp :=
          ((3 * (evalEmu env x * evalEmu env x) : ℕ) : Specs.Secp256k1.Fp)
        emuOfNat (numFp * denFp⁻¹).val).output (offset + 2 + numLimbs + numLimbs))
      _
      (by
        intro k e e' hle h_agree _
        exact emuWitnessOutput_stable _ h_agree
          (offset := offset + 2 + numLimbs + numLimbs) (by omega))
      ValidP.computableWitnesses env env'
  · -- MulModTargetW { λ, denSafe, pConst, xSafe }
    exact Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
      (Parent := DivOrZero.Inputs)
      (MulModTargetW.circuit secpParams gfMulD posOfMulD 5 vW vrW hgvW hNfW hNfrW
        threeP2Limbs (by decide) (by decide)) _
      { a := (ProvableType.witness (α := Emu) fun env =>
          let denFp : Specs.Secp256k1.Fp := ((evalEmu env den : ℕ) : Specs.Secp256k1.Fp)
          let numFp : Specs.Secp256k1.Fp :=
            ((3 * (evalEmu env x * evalEmu env x) : ℕ) : Specs.Secp256k1.Fp)
          emuOfNat (numFp * denFp⁻¹).val).output (offset + 2 + numLimbs + numLimbs),
        b := (subcircuit (Mux.circuit (M := Emu))
          { selector := (subcircuit IsZeroFeSum.circuit den).output offset,
            ifTrue := oneConst, ifFalse := den }).output (offset + 2),
        modulus := pConst,
        target := (subcircuit (Mux.circuit (M := Emu))
          { selector := (subcircuit IsZeroFeSum.circuit den).output offset,
            ifTrue := zeroConst, ifFalse := x }).output (offset + 2 + numLimbs) }
      _
      (by
        intro k e e' hle h_agree _
        have hlam := emuWitnessOutput_stable
          (fun env =>
            let denFp : Specs.Secp256k1.Fp := ((evalEmu env den : ℕ) : Specs.Secp256k1.Fp)
            let numFp : Specs.Secp256k1.Fp :=
              ((3 * (evalEmu env x * evalEmu env x) : ℕ) : Specs.Secp256k1.Fp)
            emuOfNat (numFp * denFp⁻¹).val)
          h_agree (offset := offset + 2 + numLimbs + numLimbs) (k := k) (by omega)
        have hden := Mux.eval_output_of_agreesBelow (M := Emu)
          { selector := (subcircuit IsZeroFeSum.circuit den).output offset,
            ifTrue := oneConst, ifFalse := den }
          h_agree (offset := offset + 2) (k := k) (by omega)
        have hx := Mux.eval_output_of_agreesBelow (M := Emu)
          { selector := (subcircuit IsZeroFeSum.circuit den).output offset,
            ifTrue := zeroConst, ifFalse := x }
          h_agree (offset := offset + 2 + numLimbs) (k := k) (by omega)
        simp only [circuit_norm]
        congr 1
        · exact emu_map_eval_eq_of_eval_eq hlam
        · exact emu_map_eval_eq_of_eval_eq hden
        · rw [eval_pConst, eval_pConst]
        · exact emu_map_eval_eq_of_eval_eq hx)
      (MulModTargetW.computableWitnesses secpParams gfMulD posOfMulD 5 vW vrW hgvW
        hNfW hNfrW threeP2Limbs (by decide) (by decide)) env env'

theorem computableWitness : ∀ n input,
    ProverEnvironment.OnlyAccessedBelow n
      (fun env : ProverEnvironment (F circomPrime) => eval env input) →
    Circuit.ComputableWitnesses (main input) n := by
  exact Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnesses_implies
    (circuit := circuit.base) computableWitnesses


lemma eval_lam_output_of_agreesBelow (input : Var DivOrZero.Inputs (F circomPrime)) {offset k : ℕ}
    {env env' : ProverEnvironment (F circomPrime)}
    (h_agree : env.AgreesBelow k env')
    (hk : offset + 2 + numLimbs + numLimbs + numLimbs ≤ k) :
    eval env ((main input).output offset).lam = eval env' ((main input).output offset).lam := by
  obtain ⟨x, den⟩ := input
  have hout : ((main ⟨x, den⟩).output offset).lam
      = (ProvableType.witness (α := Emu) fun env =>
          let denFp : Specs.Secp256k1.Fp := ((evalEmu env den : ℕ) : Specs.Secp256k1.Fp)
          let numFp : Specs.Secp256k1.Fp :=
            ((3 * (evalEmu env x * evalEmu env x) : ℕ) : Specs.Secp256k1.Fp)
          emuOfNat (numFp * denFp⁻¹).val).output (offset + 2 + numLimbs + numLimbs) := rfl
  rw [hout]
  exact emuWitnessOutput_stable _ h_agree (by omega)


lemma eval_isZero_output_of_agreesBelow (input : Var DivOrZero.Inputs (F circomPrime))
    {offset k : ℕ} {env env' : ProverEnvironment (F circomPrime)}
    (h_agree : env.AgreesBelow k env') (hk : offset + 2 ≤ k) :
    eval env ((main input).output offset).isZero =
      eval env' ((main input).output offset).isZero := by
  obtain ⟨x, den⟩ := input
  have hout : ((main ⟨x, den⟩).output offset).isZero =
      (subcircuit IsZeroFeSum.circuit den).output offset := rfl
  rw [hout]
  exact IsZeroFeSum.eval_output_of_agreesBelow den h_agree hk

end DivOrZeroW
end Solution.Secp256k1ScalarMul
