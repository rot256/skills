import Solution.Secp256k1ScalarMul.CompleteAddTheorems
import Solution.Secp256k1ScalarMul.ValidP
import Solution.Secp256k1ScalarMul.AddMod
import Solution.Secp256k1ScalarMul.MulModFold32TInv
import Solution.Secp256k1ScalarMul.Limbs32
import Challenge.Utils.ComputableWitnessLemmas

/-!
# `r = a·b − s1 − s2 (mod p)` with the operands in 32-bit limbs

Identical to `MulModSub2` — witness the canonical remainder, validate it with
`ValidP`, and certify `r + s1 + s2 ≡ a·b` — except that the two operands are
given as eight 32-bit limbs, so the certificate is `MulModFold32T` (93/97)
instead of `MulModFold` (176/178).

Cost: 4 + 260/267 + 93/97 = 357/362, against `MulModSub2`'s 440/445.
Callers get the 32-bit view of a witnessed slope for free out of `DivOrZeroF3`.
-/

namespace Solution.Secp256k1ScalarMul
namespace MulModSub2F32

open Specs.ShortWeierstrass Specs.Secp256k1

structure Inputs (F : Type) where
  a : BigInt 8 F
  b : BigInt 8 F
  s1 : Emu F
  s2 : Emu F
deriving ProvableStruct

def main (input : Var Inputs (F circomPrime)) :
    Circuit (F circomPrime) (Var Emu (F circomPrime)) := do
  let { a, b, s1, s2 } := input

  let r ← ProvableType.witness (α := Emu) fun env =>
    emuOfNat (((BigInt.value 32 (Vector.map (Expression.eval env.toEnvironment) a) : ℕ)
        : Specs.Secp256k1.Fp)
        * ((BigInt.value 32 (Vector.map (Expression.eval env.toEnvironment) b) : ℕ)
          : Specs.Secp256k1.Fp)
        - ((evalEmu env s1 : ℕ) : Specs.Secp256k1.Fp)
        - ((evalEmu env s2 : ℕ) : Specs.Secp256k1.Fp)).val

  ValidP.circuit r

  MulModFold32T.circuitInv (2 ^ 32) (2 ^ 32) (by decide)
    { a := a, b := b,
      target := Vector.ofFn fun k : Fin numLimbs =>
        r[k.val]'k.isLt + s1[k.val]'k.isLt + s2[k.val]'k.isLt }

  return r

instance elaborated : ElaboratedCircuit (F circomPrime) Inputs Emu main := by
  elaborate_circuit

def Assumptions (input : Inputs (F circomPrime)) : Prop :=
  BigInt.Normalized 32 input.a ∧ BigInt.Normalized 32 input.b ∧
    Fe.Valid input.s1 ∧ Fe.Valid input.s2

def Spec (input : Inputs (F circomPrime)) (out : Emu (F circomPrime)) : Prop :=
  Fe.Valid out ∧
    decodeFe out = decodeFe (Limbs32.emuOf32V input.a) * decodeFe (Limbs32.emuOf32V input.b)
      - decodeFe input.s1 - decodeFe input.s2

theorem soundness : Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [ValidP.circuit, ValidP.main, ValidP.Assumptions, ValidP.Spec,
    MulModFold32T.circuitInv, MulModFold32T.Assumptions, MulModFold32T.Spec]
  obtain ⟨ha_valid, hb_valid, hs1_valid, hs2_valid⟩ := h_assumptions
  obtain ⟨h_input_a, h_input_b, h_input_s1, h_input_s2⟩ := h_input
  obtain ⟨hr_valid, hcert⟩ := h_holds
  have hr_norm := hr_valid.1
  have hr_lt := hr_valid.2
  -- limb-level facts about the evaluated inputs
  have hs1_norm : BigInt.Normalized limbBits (Vector.map (Expression.eval env) input_var_s1) := by
    rw [h_input_s1]; exact hs1_valid.1
  have hs2_norm : BigInt.Normalized limbBits (Vector.map (Expression.eval env) input_var_s2) := by
    rw [h_input_s2]; exact hs2_valid.1
  -- the evaluated target is the limb-wise 3-sum of the evaluated vectors
  have ht_eval : Vector.map (Expression.eval env)
      (Vector.ofFn fun k : Fin numLimbs =>
        var (F := F circomPrime) { index := i₀ + k.val }
          + input_var_s1[k.val]'k.isLt + input_var_s2[k.val]'k.isLt)
      = Vector.ofFn (fun k : Fin numLimbs =>
        (Vector.map (Expression.eval env)
          (Vector.mapRange numLimbs fun i => var { index := i₀ + i }))[k.val]
          + (Vector.map (Expression.eval env) input_var_s1)[k.val]
          + (Vector.map (Expression.eval env) input_var_s2)[k.val]) := by
    apply Vector.ext
    intro j hj
    simp [circuit_norm, Vector.getElem_map, Vector.getElem_ofFn, Vector.getElem_mapRange]
  have hspec := hcert ⟨ha_valid, hb_valid, ?_, ?_⟩
  · -- conclude the spec from the congruence
    rw [ht_eval, CompleteAdd.value_sum3 _ _ _ hr_norm hs1_norm hs2_norm,
      h_input_s1, h_input_s2] at hspec
    refine ⟨⟨hr_norm, hr_lt⟩, ?_⟩
    rw [Limbs32.decodeFe_emuOf32V ha_valid, Limbs32.decodeFe_emuOf32V hb_valid]
    simp only [decodeFe]
    exact CompleteAdd.cast_of_target3_mod hspec
  · -- target limbs < 3·2^64
    intro i
    rw [Vector.getElem_ofFn]
    have hu : (Expression.eval env (var (F := F circomPrime) { index := i₀ + i.val })).val
        < 2 ^ limbBits := by
      have h := hr_norm i
      rwa [Fin.getElem_fin, Vector.getElem_map, Vector.getElem_mapRange] at h
    have hv : (Expression.eval env (input_var_s1[i.val]'i.isLt)).val < 2 ^ limbBits := by
      have h := hs1_norm i
      rwa [Fin.getElem_fin, Vector.getElem_map] at h
    have hw : (Expression.eval env (input_var_s2[i.val]'i.isLt)).val < 2 ^ limbBits := by
      have h := hs2_norm i
      rwa [Fin.getElem_fin, Vector.getElem_map] at h
    exact CompleteAdd.limb_sum3_lt hu hv hw
  · -- target value < 3·P256
    rw [ht_eval, CompleteAdd.value_sum3 _ _ _ hr_norm hs1_norm hs2_norm,
      h_input_s1, h_input_s2]
    have h1 : BigInt.value limbBits input_s1 < P256 := hs1_valid.2
    have h2 : BigInt.value limbBits input_s2 < P256 := hs2_valid.2
    omega

theorem completeness : Completeness (F circomPrime) main Assumptions := by
  circuit_proof_start [ValidP.circuit, ValidP.main, ValidP.Assumptions, ValidP.Spec,
    MulModFold32T.circuitInv, MulModFold32T.Assumptions, MulModFold32T.Spec]
  obtain ⟨ha_valid, hb_valid, hs1_valid, hs2_valid⟩ := h_assumptions
  obtain ⟨h_input_a, h_input_b, h_input_s1, h_input_s2⟩ := h_input
  have hr := h_env
  have hev_a : BigInt.value 32 (Vector.map (Expression.eval env.toEnvironment) input_var_a)
      = BigInt.value 32 input_a := by rw [← h_input_a]
  have hev_b : BigInt.value 32 (Vector.map (Expression.eval env.toEnvironment) input_var_b)
      = BigInt.value 32 input_b := by rw [← h_input_b]
  have hev_s1 : evalEmu env input_var_s1 = BigInt.value limbBits input_s1 := by
    rw [evalEmu, BigInt.value, ← h_input_s1]
  have hev_s2 : evalEmu env input_var_s2 = BigInt.value limbBits input_s2 := by
    rw [evalEmu, BigInt.value, ← h_input_s2]
  have hr_eval : Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange numLimbs fun i => var { index := i₀ + i })
      = emuOfNat (ZMod.val (((BigInt.value 32 input_a : ℕ) : Specs.Secp256k1.Fp)
          * ((BigInt.value 32 input_b : ℕ) : Specs.Secp256k1.Fp)
          - ((BigInt.value limbBits input_s1 : ℕ) : Specs.Secp256k1.Fp)
          - ((BigInt.value limbBits input_s2 : ℕ) : Specs.Secp256k1.Fp))) := by
    rw [← hev_s1, ← hev_s2]
    apply Vector.ext
    intro k hk
    have hentry : (Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange numLimbs fun i => var { index := i₀ + i }))[k]'hk
        = env.get (i₀ + k) := by
      simp [circuit_norm]
    rw [hentry]
    simpa using hr ⟨k, hk⟩
  have hr_lt : ZMod.val (((BigInt.value 32 input_a : ℕ) : Specs.Secp256k1.Fp)
      * ((BigInt.value 32 input_b : ℕ) : Specs.Secp256k1.Fp)
      - ((BigInt.value limbBits input_s1 : ℕ) : Specs.Secp256k1.Fp)
      - ((BigInt.value limbBits input_s2 : ℕ) : Specs.Secp256k1.Fp)) < P256 :=
    ZMod.val_lt _
  have hr_norm : BigInt.Normalized limbBits (Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange numLimbs fun i => var { index := i₀ + i })) := by
    rw [hr_eval]
    exact emuOfNat_normalized _
  have hr_val : BigInt.value limbBits (Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange numLimbs fun i => var { index := i₀ + i }))
      = ZMod.val (((BigInt.value 32 input_a : ℕ) : Specs.Secp256k1.Fp)
          * ((BigInt.value 32 input_b : ℕ) : Specs.Secp256k1.Fp)
          - ((BigInt.value limbBits input_s1 : ℕ) : Specs.Secp256k1.Fp)
          - ((BigInt.value limbBits input_s2 : ℕ) : Specs.Secp256k1.Fp)) := by
    rw [hr_eval]
    exact value_emuOfNat (lt_trans hr_lt P256_lt)
  have hs1_norm : BigInt.Normalized limbBits
      (Vector.map (Expression.eval env.toEnvironment) input_var_s1) := by
    rw [h_input_s1]; exact hs1_valid.1
  have hs2_norm : BigInt.Normalized limbBits
      (Vector.map (Expression.eval env.toEnvironment) input_var_s2) := by
    rw [h_input_s2]; exact hs2_valid.1
  have ht_eval : Vector.map (Expression.eval env.toEnvironment)
      (Vector.ofFn fun k : Fin numLimbs =>
        var (F := F circomPrime) { index := i₀ + k.val }
          + input_var_s1[k.val]'k.isLt + input_var_s2[k.val]'k.isLt)
      = Vector.ofFn (fun k : Fin numLimbs =>
        (Vector.map (Expression.eval env.toEnvironment)
          (Vector.mapRange numLimbs fun i => var { index := i₀ + i }))[k.val]
          + (Vector.map (Expression.eval env.toEnvironment) input_var_s1)[k.val]
          + (Vector.map (Expression.eval env.toEnvironment) input_var_s2)[k.val]) := by
    apply Vector.ext
    intro j hj
    simp [circuit_norm, Vector.getElem_map, Vector.getElem_ofFn, Vector.getElem_mapRange]
  refine ⟨⟨hr_norm, by rw [hr_val]; exact hr_lt⟩,
    ⟨ha_valid, hb_valid, ?_, ?_⟩, ?_⟩
  · -- target limbs < 3·2^64
    intro i
    rw [Vector.getElem_ofFn]
    have hu : (Expression.eval env.toEnvironment
        (var (F := F circomPrime) { index := i₀ + i.val })).val < 2 ^ limbBits := by
      have h := hr_norm i
      rwa [Fin.getElem_fin, Vector.getElem_map, Vector.getElem_mapRange] at h
    have hv : (Expression.eval env.toEnvironment (input_var_s1[i.val]'i.isLt)).val
        < 2 ^ limbBits := by
      have h := hs1_norm i
      rwa [Fin.getElem_fin, Vector.getElem_map] at h
    have hw : (Expression.eval env.toEnvironment (input_var_s2[i.val]'i.isLt)).val
        < 2 ^ limbBits := by
      have h := hs2_norm i
      rwa [Fin.getElem_fin, Vector.getElem_map] at h
    exact CompleteAdd.limb_sum3_lt hu hv hw
  · -- target value < 3·P256
    rw [ht_eval, CompleteAdd.value_sum3 _ _ _ hr_norm hs1_norm hs2_norm, hr_val,
      h_input_s1, h_input_s2]
    have h1 : BigInt.value limbBits input_s1 < P256 := hs1_valid.2
    have h2 : BigInt.value limbBits input_s2 < P256 := hs2_valid.2
    omega
  · -- the certificate spec: (r + s1 + s2) ≡ a·b (mod P256)
    rw [ht_eval, CompleteAdd.value_sum3 _ _ _ hr_norm hs1_norm hs2_norm, hr_val,
      h_input_s1, h_input_s2]
    exact CompleteAdd.witness_cert_sub2 _ _ _ _

def circuit : FormalCircuit (F circomPrime) Inputs Emu where
  main; elaborated; Assumptions; Spec; soundness; completeness

open AddMod

theorem computableWitnesses : circuit.base.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  obtain ⟨a, b, s1, s2⟩ := input
  have hw : ∀ (c : ProverEnvironment (F circomPrime) → Emu (F circomPrime)) (o : ℕ),
      (ProvableType.witness (α := Emu) c).localLength o = numLimbs := by
    intro c o; simp only [circuit_norm]
  have hvp : ∀ (x : Var Emu (F circomPrime)) (o : ℕ),
      (ValidP.circuit x).localLength o = 260 := fun _ _ => rfl
  -- the witnessed remainder block
  let rc : ProverEnvironment (F circomPrime) → Emu (F circomPrime) := fun env =>
    emuOfNat (((BigInt.value 32 (Vector.map (Expression.eval env.toEnvironment) a) : ℕ)
          : Specs.Secp256k1.Fp)
        * ((BigInt.value 32 (Vector.map (Expression.eval env.toEnvironment) b) : ℕ)
          : Specs.Secp256k1.Fp)
        - ((evalEmu env s1 : ℕ) : Specs.Secp256k1.Fp)
        - ((evalEmu env s2 : ℕ) : Specs.Secp256k1.Fp)).val
  let r : Var Emu (F circomPrime) := (ProvableType.witness (α := Emu) rc).output offset
  unfold main
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.provableWitness_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.pure_structuralComputableWitnesses_iff,
    hw, hvp, and_true]
  have hparent : ∀ (e e' : ProverEnvironment (F circomPrime)),
      eval e (⟨a, b, s1, s2⟩ : Var Inputs (F circomPrime))
        = eval e' (⟨a, b, s1, s2⟩ : Var Inputs (F circomPrime)) →
      Vector.map (Expression.eval e.toEnvironment) a
          = Vector.map (Expression.eval e'.toEnvironment) a ∧
      Vector.map (Expression.eval e.toEnvironment) b
          = Vector.map (Expression.eval e'.toEnvironment) b ∧
      evalEmu e s1 = evalEmu e' s1 ∧ evalEmu e s2 = evalEmu e' s2 := by
    intro e e' h_input
    exact ⟨MulMod.bigInt_map_eval_eq_of_eval_eq (by
        simpa [circuit_norm] using congrArg (fun x : Inputs (F circomPrime) => x.a) h_input),
      MulMod.bigInt_map_eval_eq_of_eval_eq (by
        simpa [circuit_norm] using congrArg (fun x : Inputs (F circomPrime) => x.b) h_input),
      evalEmu_eq_of_eval_eq (by
        simpa [circuit_norm] using congrArg (fun x : Inputs (F circomPrime) => x.s1) h_input),
      evalEmu_eq_of_eval_eq (by
        simpa [circuit_norm] using congrArg (fun x : Inputs (F circomPrime) => x.s2) h_input)⟩
  refine ⟨?_, ?_, ?_⟩
  · -- the r witness reads only the parent input limbs
    intro _ h_input
    obtain ⟨ha, hb, hs1, hs2⟩ := hparent env env' h_input
    simp [ha, hb, hs1, hs2]
  · -- Sparse canonical validation of r
    exact Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) ValidP.circuit _ r _
      (by
        intro k e e' hle h_agree _
        exact emuWitnessOutput_stable rc h_agree (offset := offset) (by omega))
      ValidP.computableWitnesses env env'
  · -- MulModFold { a, b, r + s1 + s2 }
    exact Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs)
      (MulModFold32T.circuitInv (2 ^ 32) (2 ^ 32) (by decide)) _
      { a := a, b := b,
        target := Vector.ofFn fun k : Fin numLimbs =>
          r[k.val]'k.isLt + s1[k.val]'k.isLt + s2[k.val]'k.isLt }
      _
      (by
        intro k e e' hle h_agree h_input
        have ha := congrArg (fun x : Inputs (F circomPrime) => x.a) h_input
        have hb := congrArg (fun x : Inputs (F circomPrime) => x.b) h_input
        have hs1 := congrArg (fun x : Inputs (F circomPrime) => x.s1) h_input
        have hs2 := congrArg (fun x : Inputs (F circomPrime) => x.s2) h_input
        simp only [circuit_norm] at ha hb hs1 hs2
        have hr := emuWitnessOutput_stable rc h_agree (offset := offset) (k := k) (by omega)
        have hr_cell : ∀ (i : ℕ) (hi : i < numLimbs),
            Expression.eval e.toEnvironment (r[i]'hi) =
              Expression.eval e'.toEnvironment (r[i]'hi) := by
          intro i hi
          have hr_i : (eval e r)[i] = (eval e' r)[i] :=
            congrArg (fun x : Emu (F circomPrime) => x[i]) hr
          rw [← ProvableType.getElem_eval_fields_prover (env := e) r i hi,
            ← ProvableType.getElem_eval_fields_prover (env := e') r i hi] at hr_i
          exact hr_i
        have hcell : ∀ (x : Var Emu (F circomPrime)),
            Vector.map (Expression.eval e.toEnvironment) x
              = Vector.map (Expression.eval e'.toEnvironment) x →
            ∀ (i : ℕ) (hi : i < numLimbs),
            Expression.eval e.toEnvironment (x[i]'hi) =
              Expression.eval e'.toEnvironment (x[i]'hi) := by
          intro x hx i hi
          have := congrArg (fun v : Vector (F circomPrime) numLimbs => v[i]'hi) hx
          simpa only [Vector.getElem_map] using this
        simp only [circuit_norm]
        rw [MulModFold32T.Inputs.mk.injEq]
        refine ⟨ha, hb, ?_⟩
        apply Vector.ext
        intro i hi
        simp only [Vector.getElem_map, Vector.getElem_ofFn]
        simp only [Expression.eval, hr_cell i hi, hcell s1 hs1 i hi, hcell s2 hs2 i hi])
      (MulModFold32T.computableWitnessesInv (2 ^ 32) (2 ^ 32) (by decide)) env env'

lemma eval_output_of_agreesBelow (input : Var Inputs (F circomPrime)) {offset k : ℕ}
    {env env' : ProverEnvironment (F circomPrime)}
    (h_agree : env.AgreesBelow k env') (hk : offset + numLimbs ≤ k) :
    eval env ((main input).output offset) = eval env' ((main input).output offset) := by
  have hout : (main input).output offset
      = (ProvableType.witness (α := Emu) fun env =>
          emuOfNat (((BigInt.value 32 (Vector.map (Expression.eval env.toEnvironment) input.a) : ℕ)
              : Specs.Secp256k1.Fp)
              * ((BigInt.value 32 (Vector.map (Expression.eval env.toEnvironment) input.b) : ℕ)
                : Specs.Secp256k1.Fp)
              - ((evalEmu env input.s1 : ℕ) : Specs.Secp256k1.Fp)
              - ((evalEmu env input.s2 : ℕ) : Specs.Secp256k1.Fp)).val).output offset := rfl
  rw [hout]
  exact AddMod.emuWitnessOutput_stable _ h_agree hk

end MulModSub2F32
end Solution.Secp256k1ScalarMul
