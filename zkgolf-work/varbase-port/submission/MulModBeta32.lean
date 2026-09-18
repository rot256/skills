import Solution.Secp256k1ScalarMul.ValidPBytes
import Solution.Secp256k1ScalarMul.Bytes32
import Solution.Secp256k1ScalarMul.MulModFold32T
import Solution.Secp256k1ScalarMul.MulModFold32TAInv
import Solution.Secp256k1ScalarMul.AddMod
import Challenge.Utils.ComputableWitnessLemmas

/-!
# `r = β·a (mod p)` — certified by the *inverse* constant in base `2^32`

Multiplying a canonical field element by the compile-time GLV constant `β`
would normally need `a` in the eight-limb 32-bit view in order to run the
certificate in base `2^32`; but `a` is an *input* here (a point coordinate), so
only its four 64-bit limbs are available.

The trick is to certify the equation the other way round.  `β` is invertible
mod `p`, so `r = β·a` is equivalent to `β⁻¹·r = a`, and in that form the two
multiplicands are the freshly witnessed remainder `r` — whose 32-bit limbs come
for free out of the bytes that its canonicality check already allocates — and
the compile-time constant `β⁻¹`.  The input `a` appears only as the certificate
*target*, i.e. as an affine addend, where its 64-bit limbs are all that is
needed.

Cost: 4 witnesses + `ValidPBytes` 260/265 + `MulModFold32TAInv` 77/79 = 341/344,
against 440/443 for the base-`2^64` `MulModSub2`.
-/

namespace Solution.Secp256k1ScalarMul
namespace MulModBeta32

open Specs.ShortWeierstrass Specs.Secp256k1

/-- The GLV endomorphism constant. -/
def betaNat : ℕ :=
  0x7ae96a2b657c07106e64479eac3434e99cf0497512f58995c1396c28719501ee

/-- Its inverse mod `p`. -/
def betaInvNat : ℕ :=
  0x851695d49a83f8ef919bb86153cbcb16630fb68aed0a766a3ec693d68e6afa40

theorem beta_mul_betaInv : betaNat * betaInvNat % P256 = 1 := by decide

theorem betaInv_lt : betaInvNat < 2 ^ 256 := by decide

/-- `β⁻¹` as eight compile-time 32-bit limbs. -/
def betaInvConst32 : Var (BigInt 8) (F circomPrime) :=
  Vector.ofFn fun k : Fin 8 =>
    ((((Limbs32.limbOfNat32 betaInvNat k.val : ℕ) : F circomPrime)) :
      Expression (F circomPrime))

lemma eval_betaInvConst32 (env : Environment (F circomPrime)) :
    Vector.map (Expression.eval env) betaInvConst32 = Limbs32.emu32OfNat betaInvNat := by
  apply Vector.ext
  intro i hi
  simp only [betaInvConst32, Limbs32.emu32OfNat, Vector.getElem_map, Vector.getElem_ofFn]
  rfl

lemma value_emu32OfNat {v : ℕ} (hv : v < 2 ^ 256) :
    BigInt.value 32 (Limbs32.emu32OfNat v) = v := by
  have h64 : BigInt.value limbBits (Limbs32.emuOf32V (Limbs32.emu32OfNat v)) = v := by
    rw [Limbs32.emuOf32V_emu32OfNat]
    exact value_emuOfNat (by simpa [limbBits, numLimbs] using hv)
  rwa [Limbs32.value_emuOf32 (Limbs32.emu32OfNat_normalized v)] at h64

structure Inputs (F : Type) where
  a : Emu F
deriving ProvableStruct

def main (input : Var Inputs (F circomPrime)) :
    Circuit (F circomPrime) (Var Emu (F circomPrime)) := do
  let r ← ProvableType.witness (α := Emu) fun env =>
    emuOfNat ((((betaNat : ℕ) : Specs.Secp256k1.Fp)
      * ((evalEmu env input.a : ℕ) : Specs.Secp256k1.Fp)).val)

  -- canonicality of `r`, which also hands back its bytes and hence its
  -- eight 32-bit limbs at no extra cost
  let bytes ← ValidPBytes.circuit r

  -- `β⁻¹ · r ≡ a (mod p)`
  MulModFold32TA.circuitInv (2 ^ 32) (2 ^ 32) (by decide)
    { a := Bytes32.ofBytes bytes, b := betaInvConst32, target := input.a }

  return r

instance elaborated : ElaboratedCircuit (F circomPrime) Inputs Emu main := by
  elaborate_circuit

def Assumptions (input : Inputs (F circomPrime)) : Prop := Fe.Valid input.a

def Spec (input : Inputs (F circomPrime)) (out : Emu (F circomPrime)) : Prop :=
  Fe.Valid out ∧
    decodeFe out = ((betaNat : ℕ) : Specs.Secp256k1.Fp) * decodeFe input.a

private lemma betaFp_mul_betaInvFp :
    ((betaNat : ℕ) : Specs.Secp256k1.Fp) * ((betaInvNat : ℕ) : Specs.Secp256k1.Fp) = 1 := by
  have h : ((betaNat * betaInvNat : ℕ) : Specs.Secp256k1.Fp) = ((1 : ℕ) : Specs.Secp256k1.Fp) := by
    rw [ZMod.natCast_eq_natCast_iff]
    change betaNat * betaInvNat % P256 = 1 % P256
    rw [beta_mul_betaInv]
    decide
  push_cast at h
  exact h

/-- The certificate congruence, cast into `Fp` and solved for `r`. -/
private lemma spec_of_cert {av rv : ℕ}
    (h : av % P256 = rv * betaInvNat % P256) :
    ((rv : ℕ) : Specs.Secp256k1.Fp)
      = ((betaNat : ℕ) : Specs.Secp256k1.Fp) * ((av : ℕ) : Specs.Secp256k1.Fp) := by
  have hcast : ((av : ℕ) : Specs.Secp256k1.Fp)
      = ((rv * betaInvNat : ℕ) : Specs.Secp256k1.Fp) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mpr h
  push_cast at hcast
  calc ((rv : ℕ) : Specs.Secp256k1.Fp)
      = ((betaNat : ℕ) : Specs.Secp256k1.Fp)
          * (((betaInvNat : ℕ) : Specs.Secp256k1.Fp) * (rv : Specs.Secp256k1.Fp)) := by
        rw [← mul_assoc, betaFp_mul_betaInvFp, one_mul]
    _ = ((betaNat : ℕ) : Specs.Secp256k1.Fp) * ((av : ℕ) : Specs.Secp256k1.Fp) := by
        rw [hcast]; ring

/-- The converse direction, used for completeness. -/
private lemma cert_of_spec {av rv : ℕ}
    (h : ((rv : ℕ) : Specs.Secp256k1.Fp)
      = ((betaNat : ℕ) : Specs.Secp256k1.Fp) * ((av : ℕ) : Specs.Secp256k1.Fp)) :
    av % P256 = rv * betaInvNat % P256 := by
  refine (ZMod.natCast_eq_natCast_iff _ _ _).mp ?_
  push_cast
  rw [h]
  calc ((av : ℕ) : Specs.Secp256k1.Fp)
      = (((betaNat : ℕ) : Specs.Secp256k1.Fp) * ((betaInvNat : ℕ) : Specs.Secp256k1.Fp))
          * ((av : ℕ) : Specs.Secp256k1.Fp) := by rw [betaFp_mul_betaInvFp, one_mul]
    _ = ((betaNat : ℕ) : Specs.Secp256k1.Fp) * ((av : ℕ) : Specs.Secp256k1.Fp)
          * ((betaInvNat : ℕ) : Specs.Secp256k1.Fp) := by ring

set_option maxHeartbeats 1000000 in
theorem soundness : Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [ValidPBytes.circuit, ValidPBytes.Assumptions, ValidPBytes.Spec,
    MulModFold32TA.circuitInv, MulModFold32TA.Assumptions, MulModFold32TA.Spec,
    MulModFold32T.Assumptions, MulModFold32T.Spec]
  obtain ⟨⟨hr_valid, hbspec⟩, hcert⟩ := h_holds
  have hnorm32 := Bytes32.normalized_map_ofBytes hbspec
  have hbetaN : BigInt.Normalized 32 (Vector.map (Expression.eval env) betaInvConst32) := by
    rw [eval_betaInvConst32]
    exact Limbs32.emu32OfNat_normalized _
  have ha3 : ∀ i : Fin numLimbs, (input_a[i.val]'i.isLt).val < 3 * 2 ^ 64 := by
    intro i
    have h := h_assumptions.1 i
    simp only [Fin.getElem_fin, limbBits] at h ⊢
    omega
  have haval : BigInt.value 64 input_a < 3 * P256 := by
    have h := h_assumptions.2
    simp only [limbBits] at h
    omega
  have hc := hcert ⟨fun i => by
      have h := hnorm32 i
      rwa [Fin.getElem_fin, Vector.getElem_map] at h,
    fun i => by
      have h := hbetaN i
      rwa [Fin.getElem_fin, Vector.getElem_map] at h,
    ha3, haval⟩
  rw [Bytes32.eval_ofBytes, Bytes32.value_ofBytesV hbspec.1, hbspec.2,
    eval_betaInvConst32, value_emu32OfNat betaInv_lt] at hc
  refine ⟨hr_valid, ?_⟩
  simp only [decodeFe]
  exact spec_of_cert hc

theorem completeness : Completeness (F circomPrime) main Assumptions := by
  circuit_proof_start [ValidPBytes.circuit, ValidPBytes.ProverAssumptions,
    ValidPBytes.ProverSpec,
    MulModFold32TA.circuitInv, MulModFold32TA.Assumptions, MulModFold32TA.Spec,
    MulModFold32T.Assumptions, MulModFold32T.Spec]
  obtain ⟨hr, hbytesImp⟩ := h_env
  have hev_a : evalEmu env input_var_a = BigInt.value limbBits input_a := by
    rw [evalEmu, BigInt.value, ← h_input]
  set rval : ℕ := (((betaNat : ℕ) : Specs.Secp256k1.Fp)
    * ((BigInt.value limbBits input_a : ℕ) : Specs.Secp256k1.Fp)).val with hrval
  have hr_eval : Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange numLimbs fun i => var { index := i₀ + i }) = emuOfNat rval := by
    apply Vector.ext
    intro k hk
    have hentry : (Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange numLimbs fun i => var { index := i₀ + i }))[k]'hk
        = env.get (i₀ + k) := by
      simp [circuit_norm]
    rw [hentry, hrval, ← hev_a]
    exact hr ⟨k, hk⟩
  have hrlt : rval < P256 := ZMod.val_lt _
  have hr_norm : BigInt.Normalized limbBits (Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange numLimbs fun i => var { index := i₀ + i })) := by
    rw [hr_eval]
    exact emuOfNat_normalized _
  have hr_val : BigInt.value limbBits (Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange numLimbs fun i => var { index := i₀ + i })) = rval := by
    rw [hr_eval]
    exact value_emuOfNat (lt_trans hrlt P256_lt)
  have hr_valid : Fe.Valid (Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange numLimbs fun i => var { index := i₀ + i })) :=
    ⟨hr_norm, by rw [hr_val]; exact hrlt⟩
  have hbspec := (hbytesImp hr_valid).2
  have hnorm32 := Bytes32.normalized_map_ofBytes hbspec
  have hbetaN : BigInt.Normalized 32
      (Vector.map (Expression.eval env.toEnvironment) betaInvConst32) := by
    rw [eval_betaInvConst32]
    exact Limbs32.emu32OfNat_normalized _
  have ha3 : ∀ i : Fin numLimbs, (input_a[i.val]'i.isLt).val < 3 * 2 ^ 64 := by
    intro i
    have h := h_assumptions.1 i
    simp only [Fin.getElem_fin, limbBits] at h ⊢
    omega
  have haval : BigInt.value 64 input_a < 3 * P256 := by
    have h := h_assumptions.2
    simp only [limbBits] at h
    omega
  refine ⟨hr_valid, ⟨fun i => by
      have h := hnorm32 i
      rwa [Fin.getElem_fin, Vector.getElem_map] at h,
    fun i => by
      have h := hbetaN i
      rwa [Fin.getElem_fin, Vector.getElem_map] at h,
    ha3, haval⟩, ?_⟩
  rw [Bytes32.eval_ofBytes, Bytes32.value_ofBytesV hbspec.1, hbspec.2, hr_val,
    eval_betaInvConst32, value_emu32OfNat betaInv_lt]
  apply cert_of_spec
  rw [hrval]
  exact ZMod.natCast_zmod_val _


def circuit : FormalCircuit (F circomPrime) Inputs Emu where
  main; elaborated; Assumptions; Spec; soundness; completeness

open AddMod

private theorem generalSubcircuit_structuralComputableWitnesses_iff
    {Parent Input Output : TypeMap}
    [CircuitType Parent] [ProvableType Input] [ProvableType Output]
    (c : GeneralFormalCircuit (F circomPrime) Input Output)
    (parentInput : Var Parent (F circomPrime))
    (input : Var Input (F circomPrime)) (n : ℕ)
    (env env' : ProverEnvironment (F circomPrime)) :
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.StructuralComputableWitnesses
        parentInput env env' n ((subcircuitWithAssertion c input).operations n) ↔
      Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.FlatOperation.StructuralComputableWitnesses
        parentInput env env' n ((c.toSubcircuit n input).ops.toFlat) := by
  unfold subcircuitWithAssertion
  simp [Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.StructuralComputableWitnesses]

set_option maxHeartbeats 8000000 in
theorem computableWitnesses : circuit.base.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition
      input env env') ((main input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  obtain ⟨a⟩ := input
  have hw : ∀ (c : ProverEnvironment (F circomPrime) → Emu (F circomPrime)) (o : ℕ),
      (ProvableType.witness (α := Emu) c).localLength o = numLimbs := by
    intro c o; simp only [circuit_norm]
  have hvp : ∀ (x : Var Emu (F circomPrime)) (o : ℕ),
      (ValidPBytes.circuit x).localLength o = 260 := fun _ _ => rfl
  let rc : ProverEnvironment (F circomPrime) → Emu (F circomPrime) := fun env =>
    emuOfNat ((((betaNat : ℕ) : Specs.Secp256k1.Fp)
      * ((evalEmu env a : ℕ) : Specs.Secp256k1.Fp)).val)
  let r : Var Emu (F circomPrime) := (ProvableType.witness (α := Emu) rc).output offset
  let bytesv : Var (fields coordBytes) (F circomPrime) :=
    ValidPBytes.circuit.output r (offset + numLimbs)
  unfold main
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.provableWitness_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.pure_structuralComputableWitnesses_iff,
    generalSubcircuit_structuralComputableWitnesses_iff,
    hw, hvp, and_true]
  refine ⟨?_, ?_, ?_⟩
  · -- the remainder witness reads only the input limbs
    intro _ h_input
    have ha : evalEmu env a = evalEmu env' a :=
      evalEmu_eq_of_eval_eq (by
        simpa [circuit_norm] using
          congrArg (fun x : Inputs (F circomPrime) => x.a) h_input)
    simp only [ha]
  · -- canonicality of the remainder
    exact Challenge.Utils.ComputableWitnessLemmas.GeneralFormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) ValidPBytes.circuit _ r _
      (by
        intro k e e' hle h_agree _
        exact emuWitnessOutput_stable rc h_agree (offset := offset) (by omega))
      ValidPBytes.computableWitnesses env env'
  · -- the folded certificate
    refine Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs)
      (MulModFold32TA.circuitInv (2 ^ 32) (2 ^ 32) (by decide))
      ({ a := a } : Var Inputs (F circomPrime))
      { a := Bytes32.ofBytes bytesv, b := betaInvConst32, target := a } _ ?_
      (MulModFold32TA.computableWitnessesInv (2 ^ 32) (2 ^ 32) (by decide)) env env'
    intro k e e' hle h_agree h_input
    have ha : Vector.map (Expression.eval e.toEnvironment) a
        = Vector.map (Expression.eval e'.toEnvironment) a := by
      simpa [circuit_norm] using
        congrArg (fun x : Inputs (F circomPrime) => x.a) h_input
    have hrs : eval e r = eval e' r :=
      emuWitnessOutput_stable rc h_agree (offset := offset) (by omega)
    have hbytes : Vector.map (Expression.eval e.toEnvironment) bytesv
        = Vector.map (Expression.eval e'.toEnvironment) bytesv :=
      ValidPBytes.output_map_eval_eq r (offset + numLimbs) h_agree (by omega)
        (emu_map_eval_eq_of_eval_eq hrs)
    simp only [circuit_norm]
    rw [MulModFold32T.Inputs.mk.injEq]
    exact ⟨Bytes32.ofBytes_map_eval_eq hbytes,
      by rw [eval_betaInvConst32, eval_betaInvConst32], ha⟩

theorem computableWitness : ∀ n input,
    ProverEnvironment.OnlyAccessedBelow n
      (fun env : ProverEnvironment (F circomPrime) => eval env input) →
    Circuit.ComputableWitnesses (main input) n :=
  Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnesses_implies
    (circuit := circuit.base) computableWitnesses

lemma eval_output_of_agreesBelow (input : Var Inputs (F circomPrime)) {offset k : ℕ}
    {env env' : ProverEnvironment (F circomPrime)}
    (h_agree : env.AgreesBelow k env') (hk : offset + numLimbs ≤ k) :
    eval env ((main input).output offset) = eval env' ((main input).output offset) := by
  have hout : (main input).output offset
      = (ProvableType.witness (α := Emu) fun env =>
          emuOfNat ((((betaNat : ℕ) : Specs.Secp256k1.Fp)
            * ((evalEmu env input.a : ℕ) : Specs.Secp256k1.Fp)).val)).output offset := rfl
  rw [hout]
  exact AddMod.emuWitnessOutput_stable _ h_agree hk

end MulModBeta32
end Solution.Secp256k1ScalarMul
