import Solution.Secp256k1ScalarMul.CompleteAddTheorems
import Solution.Secp256k1ScalarMul.AddMod
import Solution.Secp256k1ScalarMul.MulModFold32TInv
import Solution.Secp256k1ScalarMul.Limbs32
import Solution.Secp256k1ScalarMul.Normalize
import Challenge.Utils.ComputableWitnessLemmas

/-!
# `r ≡ a·b (mod p)` on 32-bit operands, with a *non-canonical* remainder

Identical to `MulModSub2F32` with `s1 = s2 = 0`, except that the witnessed
remainder is only proved **normalized** (`Normalize`, 252/256) instead of
canonical (`ValidP`, 260/265).

Canonicality is *uniqueness*, and a remainder that is only ever read as an
operand of another modular certificate never needs to be the canonical
representative — the limb bound is the whole soundness requirement.

Cost: 4 + 252/256 + 93/97 = 349/353, against `MulModSub2F32`s 357/362.
-/

namespace Solution.Secp256k1ScalarMul
namespace MulModSqN32

open Specs.ShortWeierstrass Specs.Secp256k1

structure Inputs (F : Type) where
  a : BigInt 8 F
  b : BigInt 8 F
deriving ProvableStruct

def main (input : Var Inputs (F circomPrime)) :
    Circuit (F circomPrime) (Var Emu (F circomPrime)) := do
  let { a, b } := input

  let r ← ProvableType.witness (α := Emu) fun env =>
    emuOfNat (((BigInt.value 32 (Vector.map (Expression.eval env.toEnvironment) a) : ℕ)
        : Specs.Secp256k1.Fp)
        * ((BigInt.value 32 (Vector.map (Expression.eval env.toEnvironment) b) : ℕ)
          : Specs.Secp256k1.Fp)).val

  Normalize.circuit secpParams r

  MulModFold32T.circuitInv (2 ^ 32) (2 ^ 32) (by decide)
    { a := a, b := b, target := r }

  return r

instance elaborated : ElaboratedCircuit (F circomPrime) Inputs Emu main := by
  elaborate_circuit

def Assumptions (input : Inputs (F circomPrime)) : Prop :=
  BigInt.Normalized 32 input.a ∧ BigInt.Normalized 32 input.b

def Spec (input : Inputs (F circomPrime)) (out : Emu (F circomPrime)) : Prop :=
  BigInt.Normalized limbBits out ∧
    decodeFe out = decodeFe (Limbs32.emuOf32V input.a) * decodeFe (Limbs32.emuOf32V input.b)

private lemma cast_of_target_mod {rv av bv : ℕ} (h : rv % P256 = av * bv % P256) :
    ((rv : ℕ) : Specs.Secp256k1.Fp)
      = ((av : ℕ) : Specs.Secp256k1.Fp) * ((bv : ℕ) : Specs.Secp256k1.Fp) := by
  have hcast : ((rv : ℕ) : Specs.Secp256k1.Fp) = ((av * bv : ℕ) : Specs.Secp256k1.Fp) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mpr h
  push_cast at hcast
  linear_combination hcast

private lemma target_mod_of_witness (A B : ℕ) :
    (ZMod.val (((A : ℕ) : Specs.Secp256k1.Fp) * ((B : ℕ) : Specs.Secp256k1.Fp))) % P256
      = A * B % P256 := by
  simpa using CompleteAdd.witness_cert_sub2 A B 0 0

theorem soundness : Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [Normalize.circuit, Normalize.main, Normalize.Assumptions, Normalize.Spec,
    MulModFold32T.circuitInv, MulModFold32T.Assumptions, MulModFold32T.Spec]
  obtain ⟨ha_valid, hb_valid⟩ := h_assumptions
  obtain ⟨h_input_a, h_input_b⟩ := h_input
  obtain ⟨hr_norm0, hcert⟩ := h_holds
  have hr_norm : BigInt.Normalized limbBits
      (Vector.map (Expression.eval env)
        (Vector.mapRange numLimbs fun i => var (F := F circomPrime) { index := i₀ + i })) :=
    hr_norm0
  have hcell : ∀ i : Fin numLimbs, (env.get (i₀ + i.val)).val < 2 ^ limbBits := by
    intro i
    have h := hr_norm i
    simpa [circuit_norm] using h
  have hr_lt : BigInt.value limbBits
      (Vector.map (Expression.eval env)
        (Vector.mapRange numLimbs fun i => var (F := F circomPrime) { index := i₀ + i }))
      < 3 * P256 := by
    have h := BigInt.value_lt hr_norm
    have h2 : (2 : ℕ) ^ (limbBits * numLimbs) ≤ 3 * P256 := by decide
    omega
  have hspec := hcert ⟨ha_valid, hb_valid, ?_, hr_lt⟩
  · refine ⟨hr_norm, ?_⟩
    rw [Limbs32.decodeFe_emuOf32V ha_valid, Limbs32.decodeFe_emuOf32V hb_valid]
    simp only [decodeFe]
    exact cast_of_target_mod hspec
  · intro i
    have h := hcell i
    simp only [limbBits] at h ⊢
    omega

theorem completeness : Completeness (F circomPrime) main Assumptions := by
  circuit_proof_start [Normalize.circuit, Normalize.main, Normalize.Assumptions, Normalize.Spec,
    MulModFold32T.circuitInv, MulModFold32T.Assumptions, MulModFold32T.Spec]
  obtain ⟨ha_valid, hb_valid⟩ := h_assumptions
  obtain ⟨h_input_a, h_input_b⟩ := h_input
  have hr := h_env
  have hev_a : BigInt.value 32 (Vector.map (Expression.eval env.toEnvironment) input_var_a)
      = BigInt.value 32 input_a := by rw [← h_input_a]
  have hev_b : BigInt.value 32 (Vector.map (Expression.eval env.toEnvironment) input_var_b)
      = BigInt.value 32 input_b := by rw [← h_input_b]
  have hcellEq : ∀ i : Fin numLimbs, env.get (i₀ + i.val)
      = (emuOfNat (ZMod.val (((BigInt.value 32 input_a : ℕ) : Specs.Secp256k1.Fp)
          * ((BigInt.value 32 input_b : ℕ) : Specs.Secp256k1.Fp))))[i.val] := by
    intro i
    simpa [hev_a, hev_b] using hr i
  have hr_eval : Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange numLimbs fun i => var { index := i₀ + i })
      = emuOfNat (ZMod.val (((BigInt.value 32 input_a : ℕ) : Specs.Secp256k1.Fp)
          * ((BigInt.value 32 input_b : ℕ) : Specs.Secp256k1.Fp))) := by
    apply Vector.ext
    intro k hk
    have hentry : (Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange numLimbs fun i => var { index := i₀ + i }))[k]'hk
        = env.get (i₀ + k) := by
      simp [circuit_norm]
    rw [hentry]
    exact hcellEq ⟨k, hk⟩
  have hr_val_lt : ZMod.val (((BigInt.value 32 input_a : ℕ) : Specs.Secp256k1.Fp)
      * ((BigInt.value 32 input_b : ℕ) : Specs.Secp256k1.Fp)) < P256 := ZMod.val_lt _
  have hr_norm : BigInt.Normalized limbBits (Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange numLimbs fun i => var { index := i₀ + i })) := by
    rw [hr_eval]
    exact emuOfNat_normalized _
  have hcell : ∀ i : Fin numLimbs, (env.get (i₀ + i.val)).val < 2 ^ limbBits := by
    intro i
    have h := hr_norm i
    simpa [circuit_norm] using h
  have hr_val : BigInt.value limbBits (Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange numLimbs fun i => var { index := i₀ + i }))
      = ZMod.val (((BigInt.value 32 input_a : ℕ) : Specs.Secp256k1.Fp)
          * ((BigInt.value 32 input_b : ℕ) : Specs.Secp256k1.Fp)) := by
    rw [hr_eval]
    exact value_emuOfNat (lt_trans hr_val_lt P256_lt)
  refine ⟨hr_norm, ⟨ha_valid, hb_valid, ?_, ?_⟩, ?_⟩
  · intro i
    have h := hcell i
    simp only [limbBits] at h ⊢
    omega
  · rw [hr_val]
    have := hr_val_lt
    omega
  · rw [hr_val]
    exact target_mod_of_witness _ _

def circuit : FormalCircuit (F circomPrime) Inputs Emu where
  main; elaborated; Assumptions; Spec; soundness; completeness

open AddMod

theorem computableWitnesses : circuit.base.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition
      input env env')
    ((main input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  obtain ⟨a, b⟩ := input
  have hw : ∀ (c : ProverEnvironment (F circomPrime) → Emu (F circomPrime)) (o : ℕ),
      (ProvableType.witness (α := Emu) c).localLength o = numLimbs := by
    intro c o; simp only [circuit_norm]
  have hnz : ∀ (x : Var Emu (F circomPrime)) (o : ℕ),
      (Normalize.circuit secpParams x).localLength o = 252 := fun _ _ => rfl
  let rc : ProverEnvironment (F circomPrime) → Emu (F circomPrime) := fun env =>
    emuOfNat (((BigInt.value 32 (Vector.map (Expression.eval env.toEnvironment) a) : ℕ)
          : Specs.Secp256k1.Fp)
        * ((BigInt.value 32 (Vector.map (Expression.eval env.toEnvironment) b) : ℕ)
          : Specs.Secp256k1.Fp)).val
  let r : Var Emu (F circomPrime) := (ProvableType.witness (α := Emu) rc).output offset
  unfold main
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.provableWitness_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.pure_structuralComputableWitnesses_iff,
    hw, hnz, and_true]
  have hparent : ∀ (e e' : ProverEnvironment (F circomPrime)),
      eval e (⟨a, b⟩ : Var Inputs (F circomPrime))
        = eval e' (⟨a, b⟩ : Var Inputs (F circomPrime)) →
      Vector.map (Expression.eval e.toEnvironment) a
          = Vector.map (Expression.eval e'.toEnvironment) a ∧
      Vector.map (Expression.eval e.toEnvironment) b
          = Vector.map (Expression.eval e'.toEnvironment) b := by
    intro e e' h_input
    exact ⟨MulMod.bigInt_map_eval_eq_of_eval_eq (by
        simpa [circuit_norm] using congrArg (fun x : Inputs (F circomPrime) => x.a) h_input),
      MulMod.bigInt_map_eval_eq_of_eval_eq (by
        simpa [circuit_norm] using congrArg (fun x : Inputs (F circomPrime) => x.b) h_input)⟩
  refine ⟨?_, ?_, ?_⟩
  · intro _ h_input
    obtain ⟨ha, hb⟩ := hparent env env' h_input
    simp [ha, hb]
  · exact Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) (Normalize.circuit secpParams) _ r _
      (by
        intro k e e' hle h_agree _
        exact emuWitnessOutput_stable rc h_agree (offset := offset) (by omega))
      (Normalize.computableWitnesses secpParams) env env'
  · exact Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs)
      (MulModFold32T.circuitInv (2 ^ 32) (2 ^ 32) (by decide)) _
      { a := a, b := b, target := r } _
      (by
        intro k e e' hle h_agree h_input
        have ha := congrArg (fun x : Inputs (F circomPrime) => x.a) h_input
        have hb := congrArg (fun x : Inputs (F circomPrime) => x.b) h_input
        simp only [circuit_norm] at ha hb
        have hr := emu_map_eval_eq_of_eval_eq
          (emuWitnessOutput_stable rc h_agree (offset := offset) (k := k) (by omega))
        simp only [circuit_norm]
        rw [MulModFold32T.Inputs.mk.injEq]
        exact ⟨ha, hb, hr⟩)
      (MulModFold32T.computableWitnessesInv (2 ^ 32) (2 ^ 32) (by decide)) env env'

lemma eval_output_of_agreesBelow (input : Var Inputs (F circomPrime)) {offset k : ℕ}
    {env env' : ProverEnvironment (F circomPrime)}
    (h_agree : env.AgreesBelow k env') (hk : offset + numLimbs ≤ k) :
    eval env ((main input).output offset) = eval env' ((main input).output offset) := by
  have hout : (main input).output offset
      = (ProvableType.witness (α := Emu) fun env =>
          emuOfNat (((BigInt.value 32
                (Vector.map (Expression.eval env.toEnvironment) input.a) : ℕ)
              : Specs.Secp256k1.Fp)
              * ((BigInt.value 32
                (Vector.map (Expression.eval env.toEnvironment) input.b) : ℕ)
                : Specs.Secp256k1.Fp)).val).output offset := rfl
  rw [hout]
  exact AddMod.emuWitnessOutput_stable _ h_agree hk

theorem computableWitness : ∀ n input,
    ProverEnvironment.OnlyAccessedBelow n
      (fun env : ProverEnvironment (F circomPrime) => eval env input) →
    Circuit.ComputableWitnesses (main input) n :=
  Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnesses_implies
    (circuit := circuit.base) computableWitnesses

end MulModSqN32
end Solution.Secp256k1ScalarMul
