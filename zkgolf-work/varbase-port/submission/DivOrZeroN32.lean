import Solution.Secp256k1ScalarMul.DivOrZeroS32
import Solution.Secp256k1ScalarMul.MulModFold32NInv

/-!
# Unconditional division `λ = num / den`, with the quotient in 32-bit limbs

This is `DivOrZeroS32` stripped of its *conditional* numerator **and** of its
zero guard: the caller hands in the numerator directly as a (borrow-biased)
four-limb vector, so the gadget neither materialises a squaring convolution nor
multiplexes a `2m−1`-cell target, and it *assumes* the denominator is not a
multiple of `p`, so no `IsZeroFeSum` flag and no guarded recombination are
needed.  What remains is the eight 32-bit witness limbs of the quotient, their
range check, and the folded certificate `λ·den ≡ num`.

The sole call site (`Slope2`) already feeds a denominator whose integer value
lies in `(p, 3p]` — it is `DivOrZeroS32.denSafeVec` applied to a borrow-biased
difference — and already proves exactly that non-aliasing fact in both its
soundness and its completeness argument, so the zero flag it used to pay for
was provably dead.

Cost `8 + 248/256 + 156/158 = 412/414`, against the wider base-64 division.

The certificate is the *mixed* base-`2^32` fold `MulModFold32N`: the quotient
limbs are already 32-bit (they are range-checked as such by `Normalize`), and
the denominator, a four-limb 64-bit vector, is re-read for free at the even
base-`2^32` positions.  That also removes the zero-padding of the target to
`2m-1` cells, since the mixed fold takes the numerator as an `Emu` directly.
-/

namespace Solution.Secp256k1ScalarMul

namespace DivOrZeroN32
open DivOrZero MulMod MulModTargetD MulModTargetW
open DivOrZeroS32 (Emu32 emu32WitnessOutput_stable polyValue_pad)

/-- Numerator and denominator of an unconditional modular division. -/
structure Inputs (F : Type) where
  num : Emu F
  den : Emu F
deriving ProvableStruct

def main (input : Var Inputs (F circomPrime)) :
    Circuit (F circomPrime) (Var Emu32 (F circomPrime)) := do
  let { num, den } := input

  let lam32 ← ProvableType.witness (α := Emu32) fun env =>
    let denFp : Specs.Secp256k1.Fp := ((evalEmu env den : ℕ) : Specs.Secp256k1.Fp)
    let numFp : Specs.Secp256k1.Fp := ((evalEmu env num : ℕ) : Specs.Secp256k1.Fp)
    Limbs32.emu32OfNat (numFp * denFp⁻¹).val

  Normalize.circuit secpParams32 lam32

  MulModFold32N.circuitInv (2 ^ 32) (3 * 2 ^ 64) (by decide)
    { a := lam32, b := MulModFold32N.expand32 den, target := num }

  return lam32

instance elaborated : ElaboratedCircuit (F circomPrime) Inputs Emu32 main := by
  elaborate_circuit

def Assumptions (input : Inputs (F circomPrime)) : Prop :=
  (∀ i : Fin numLimbs, (input.num[i.val]).val < 3 * 2 ^ limbBits) ∧
    BigInt.value limbBits input.num < 3 * P256 ∧
    (∀ i : Fin numLimbs, (input.den[i.val]).val < 3 * 2 ^ limbBits) ∧
    BigInt.value limbBits input.den < 3 * P256 ∧
    ¬ (BigInt.value limbBits input.den % P256 = 0)

def Spec (input : Inputs (F circomPrime)) (lam32 : Emu32 (F circomPrime)) : Prop :=
  BigInt.Normalized 32 lam32 ∧
    (decodeFe input.den ≠ 0 →
      decodeFe (Limbs32.emuOf32V lam32) * decodeFe input.den = decodeFe input.num)

set_option maxHeartbeats 3200000 in
theorem soundness : Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [MulModFold32N.circuitInv, MulModFold32N.Assumptions, MulModFold32N.Spec,
    Normalize.circuit, Normalize.main, Normalize.Assumptions, Normalize.Spec]
  obtain ⟨h_num_limb, h_num_val, h_den_limb3, h_den_val3, h_den_alias⟩ := h_assumptions
  obtain ⟨h_input_num, h_input_den⟩ := h_input
  obtain ⟨hlam_valid, hmul⟩ := h_holds
  set lam32Var := Vector.mapRange 8 fun i =>
    var (F := F circomPrime) { index := i₀ + i } with hlam32Var
  have hden_limb : ∀ i : Fin numLimbs,
      ((Vector.map (Expression.eval env) input_var_den)[i.val]'i.isLt).val
        < 3 * 2 ^ limbBits := by
    intro i
    rw [h_input_den]
    exact h_den_limb3 i
  have hexp_limb' : ∀ i : Fin 8,
      ((Vector.map (Expression.eval env) (MulModFold32N.expand32 input_var_den))[i.val]).val
        < 3 * 2 ^ 64 := by
    rw [MulModFold32N.eval_expand32]
    exact MulModFold32N.expand32V_lt (by positivity) hden_limb
  have hexp_limb : ∀ i : Fin 8,
      (Expression.eval env ((MulModFold32N.expand32 input_var_den)[i.val])).val < 3 * 2 ^ 64 :=
    fun i => by simpa [Vector.getElem_map] using hexp_limb' i
  have hspec_of := hmul ⟨fun i => by
      simpa [hlam32Var, secpParams32, circuit_norm] using hlam_valid i,
    hexp_limb, MulModFold32N.eval_expand32_odd_zero env input_var_den,
    fun i => by simpa [limbBits] using h_num_limb i,
    by simpa [limbBits] using h_num_val⟩
  have hden_val32 : BigInt.value 32 (Vector.map (Expression.eval env)
        (MulModFold32N.expand32 input_var_den))
      = BigInt.value limbBits input_den := by
    rw [MulModFold32N.eval_expand32, MulModFold32N.value_expand32, h_input_den]
  have hlamval : BigInt.value 32 (Vector.map (Expression.eval env) lam32Var)
      = BigInt.value limbBits
        (Limbs32.emuOf32V (Vector.map (Expression.eval env) lam32Var)) :=
    (Limbs32.value_emuOf32 hlam_valid).symm
  refine ⟨hlam_valid, fun _ => ?_⟩
  have hspec := hspec_of
  rw [hden_val32, hlamval] at hspec
  simp only [decodeFe]
  exact mul_cast_of_mod_eq3 hspec

set_option maxHeartbeats 3200000 in
theorem completeness : Completeness (F circomPrime) main Assumptions := by
  circuit_proof_start [MulModFold32N.circuitInv, MulModFold32N.Assumptions, MulModFold32N.Spec,
    Normalize.circuit, Normalize.main, Normalize.Assumptions, Normalize.Spec]
  obtain ⟨h_num_limb, h_num_val, h_den_limb3, h_den_val3, h_den_alias⟩ := h_assumptions
  obtain ⟨h_input_num, h_input_den⟩ := h_input
  set lam32Var := Vector.mapRange 8 fun i =>
    var (F := F circomPrime) { index := i₀ + i } with hlam32Var
  have hden_limb : ∀ i : Fin numLimbs,
      ((Vector.map (Expression.eval env.toEnvironment) input_var_den)[i.val]'i.isLt).val
        < 3 * 2 ^ limbBits := by
    intro i
    rw [h_input_den]
    exact h_den_limb3 i
  have hexp_limb' : ∀ i : Fin 8,
      ((Vector.map (Expression.eval env.toEnvironment)
          (MulModFold32N.expand32 input_var_den))[i.val]).val < 3 * 2 ^ 64 := by
    rw [MulModFold32N.eval_expand32]
    exact MulModFold32N.expand32V_lt (by positivity) hden_limb
  have hexp_limb : ∀ i : Fin 8,
      (Expression.eval env.toEnvironment
        ((MulModFold32N.expand32 input_var_den)[i.val])).val < 3 * 2 ^ 64 :=
    fun i => by simpa [Vector.getElem_map] using hexp_limb' i
  have hev_num : evalEmu env input_var_num = BigInt.value limbBits input_num := by
    rw [evalEmu, BigInt.value, ← h_input_num]
  have hev_den : evalEmu env input_var_den = BigInt.value limbBits input_den := by
    rw [evalEmu, BigInt.value, ← h_input_den]
  have hlam_eval : Vector.map (Expression.eval env.toEnvironment) lam32Var
      = Limbs32.emu32OfNat (ZMod.val
          (((BigInt.value limbBits input_num : ℕ) : Specs.Secp256k1.Fp)
            * ((BigInt.value limbBits input_den : ℕ) : Specs.Secp256k1.Fp)⁻¹)) := by
    rw [← hev_num, ← hev_den]
    apply Vector.ext
    intro k hk
    have hentry : (Vector.map (Expression.eval env.toEnvironment) lam32Var)[k]'hk
        = env.get (i₀ + k) := by
      rw [hlam32Var, Vector.getElem_map, Vector.getElem_mapRange]; rfl
    rw [hentry]
    exact h_env ⟨k, hk⟩
  have hq_lt : ZMod.val (((BigInt.value limbBits input_num : ℕ) : Specs.Secp256k1.Fp)
        * ((BigInt.value limbBits input_den : ℕ) : Specs.Secp256k1.Fp)⁻¹) < P256 :=
    ZMod.val_lt _
  have hlam32_norm : BigInt.Normalized 32
      (Vector.map (Expression.eval env.toEnvironment) lam32Var) := by
    rw [hlam_eval]; exact Limbs32.emu32OfNat_normalized _
  have hlam_val32 : BigInt.value 32 (Vector.map (Expression.eval env.toEnvironment) lam32Var)
      = ZMod.val (((BigInt.value limbBits input_num : ℕ) : Specs.Secp256k1.Fp)
          * ((BigInt.value limbBits input_den : ℕ) : Specs.Secp256k1.Fp)⁻¹) := by
    rw [← Limbs32.value_emuOf32 hlam32_norm, hlam_eval, Limbs32.emuOf32V_emu32OfNat]
    exact value_emuOfNat (lt_trans hq_lt P256_lt)
  have hden_val32 : BigInt.value 32 (Vector.map (Expression.eval env.toEnvironment)
        (MulModFold32N.expand32 input_var_den))
      = BigInt.value limbBits input_den := by
    rw [MulModFold32N.eval_expand32, MulModFold32N.value_expand32, h_input_den]
  have hdv_ne : ((BigInt.value limbBits input_den : ℕ) : Specs.Secp256k1.Fp) ≠ 0 := by
    intro hc
    rcases (ZMod.natCast_eq_zero_iff _ _).mp hc with ⟨k, hk⟩
    exact h_den_alias (by rw [hk]; exact Nat.mul_mod_right _ _)
  refine ⟨hlam32_norm,
    ⟨⟨fun i => by simpa [hlam32Var, secpParams32, circuit_norm] using hlam32_norm i,
      hexp_limb,
      MulModFold32N.eval_expand32_odd_zero env.toEnvironment input_var_den,
      fun i => by simpa [limbBits] using h_num_limb i,
      by simpa [limbBits] using h_num_val⟩, ?_⟩⟩
  rw [hlam_val32, hden_val32]
  exact witness_cert_nonzero3 hdv_ne

def circuit : FormalCircuit (F circomPrime) Inputs Emu32 where
  main; elaborated; Assumptions; Spec; soundness; completeness

set_option maxHeartbeats 3200000 in
theorem computableWitnesses : circuit.base.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition
      input env env')
    ((main input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  obtain ⟨num, den⟩ := input
  have hw : ∀ (c : ProverEnvironment (F circomPrime) → Emu32 (F circomPrime)) (o : ℕ),
      (ProvableType.witness (α := Emu32) c).localLength o = 8 := by
    intro c o; simp only [circuit_norm]
  have hvp : ∀ (v : Var Emu32 (F circomPrime)) (o : ℕ),
      (Normalize.circuit secpParams32 v).localLength o = 248 := fun _ _ => rfl
  unfold main
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.provableWitness_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.pure_structuralComputableWitnesses_iff,
    hw, hvp, and_true]
  refine ⟨?_, ?_, ?_⟩
  · -- λ witness : reads only the parent inputs
    intro _ h_input
    have hden : evalEmu env den = evalEmu env' den :=
      evalEmu_eq_of_eval_eq (by
        simpa [circuit_norm] using
          congrArg (fun v : Inputs (F circomPrime) => v.den) h_input)
    have hnum : evalEmu env num = evalEmu env' num :=
      evalEmu_eq_of_eval_eq (by
        simpa [circuit_norm] using
          congrArg (fun v : Inputs (F circomPrime) => v.num) h_input)
    simp only [hden, hnum]
  · -- 32-bit limb range checks on λ
    exact Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) (Normalize.circuit secpParams32) _
      ((ProvableType.witness (α := Emu32) fun env =>
        let denFp : Specs.Secp256k1.Fp := ((evalEmu env den : ℕ) : Specs.Secp256k1.Fp)
        let numFp : Specs.Secp256k1.Fp := ((evalEmu env num : ℕ) : Specs.Secp256k1.Fp)
        Limbs32.emu32OfNat (numFp * denFp⁻¹).val).output offset)
      _
      (by
        intro k e e' hle h_agree _
        exact emu32WitnessOutput_stable _ h_agree (offset := offset) (by omega))
      (Normalize.computableWitnesses secpParams32) env env'
  · -- MulModFold32N { λ, expand32 den, num }
    exact Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs)
      (MulModFold32N.circuitInv (2 ^ 32) (3 * 2 ^ 64) (by decide)) _
      { a := (ProvableType.witness (α := Emu32) fun env =>
          let denFp : Specs.Secp256k1.Fp := ((evalEmu env den : ℕ) : Specs.Secp256k1.Fp)
          let numFp : Specs.Secp256k1.Fp := ((evalEmu env num : ℕ) : Specs.Secp256k1.Fp)
          Limbs32.emu32OfNat (numFp * denFp⁻¹).val).output offset,
        b := MulModFold32N.expand32 den,
        target := num }
      _
      (by
        intro k e e' hle h_agree h_in
        have hlam := emu32WitnessOutput_stable
          (fun env =>
            let denFp : Specs.Secp256k1.Fp := ((evalEmu env den : ℕ) : Specs.Secp256k1.Fp)
            let numFp : Specs.Secp256k1.Fp := ((evalEmu env num : ℕ) : Specs.Secp256k1.Fp)
            Limbs32.emu32OfNat (numFp * denFp⁻¹).val)
          h_agree (offset := offset) (k := k) (by omega)
        have hnumMap : Vector.map (Expression.eval e.toEnvironment) num
            = Vector.map (Expression.eval e'.toEnvironment) num := by
          simpa [circuit_norm] using congrArg (fun v : Inputs (F circomPrime) => v.num) h_in
        have hdenMap : Vector.map (Expression.eval e.toEnvironment) den
            = Vector.map (Expression.eval e'.toEnvironment) den := by
          simpa [circuit_norm] using congrArg (fun v : Inputs (F circomPrime) => v.den) h_in
        simp only [circuit_norm]
        rw [MulModFold32N.Inputs.mk.injEq]
        refine ⟨MulMod.bigInt_map_eval_eq_of_eval_eq hlam, ?_, hnumMap⟩
        rw [MulModFold32N.eval_expand32, MulModFold32N.eval_expand32]
        exact congrArg MulModFold32N.expand32V hdenMap)
      (MulModFold32N.computableWitnessesInv (2 ^ 32) (3 * 2 ^ 64) (by decide)) env env'

theorem computableWitness : ∀ n input,
    ProverEnvironment.OnlyAccessedBelow n
      (fun env : ProverEnvironment (F circomPrime) => eval env input) →
    Circuit.ComputableWitnesses (main input) n :=
  Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnesses_implies
    (circuit := circuit.base) computableWitnesses

lemma eval_output_of_agreesBelow (input : Var Inputs (F circomPrime)) {offset k : ℕ}
    {env env' : ProverEnvironment (F circomPrime)}
    (h_agree : env.AgreesBelow k env') (hk : offset + 8 ≤ k) :
    eval env ((main input).output offset) = eval env' ((main input).output offset) := by
  obtain ⟨num, den⟩ := input
  have hout : (main ⟨num, den⟩).output offset
      = (ProvableType.witness (α := Emu32) fun env =>
          let denFp : Specs.Secp256k1.Fp := ((evalEmu env den : ℕ) : Specs.Secp256k1.Fp)
          let numFp : Specs.Secp256k1.Fp := ((evalEmu env num : ℕ) : Specs.Secp256k1.Fp)
          Limbs32.emu32OfNat (numFp * denFp⁻¹).val).output offset := rfl
  rw [hout]
  exact emu32WitnessOutput_stable _ h_agree (by omega)

end DivOrZeroN32
end Solution.Secp256k1ScalarMul
