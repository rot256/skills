import Solution.Secp256k1ScalarMul.CompleteAddTheorems
import Solution.Secp256k1ScalarMul.ValidP
import Solution.Secp256k1ScalarMul.AddMod
import Solution.Secp256k1ScalarMul.Params
import Solution.Secp256k1ScalarMul.ParamsFold
import Solution.Secp256k1ScalarMul.GroupedEqXV
import Solution.Secp256k1ScalarMul.MulModTargetW2
import Solution.Secp256k1ScalarMul.InterpMul
import Solution.Secp256k1ScalarMul.RangeCheck
import Solution.Secp256k1ScalarMul.MulModFold32NInv
import Solution.Secp256k1ScalarMul.Limbs32
import Solution.Secp256k1ScalarMul.MulMod
import Solution.Secp256k1ScalarMul.Limbs33
import Challenge.Utils.ComputableWitnessLemmas

/-!
# `r = a·b − s1 − s2 (mod p)` with a widened 32-bit `a` and an unreduced `b`

Identical to `MulModSub2W2` — witness the canonical remainder, validate it with
`ValidP`, and certify `r + s1 + s2 ≡ a·b` — except that the first operand is
given as eight widened 32-bit limbs while the second stays a triply unreduced
four-limb 64-bit vector.  The certificate is then the *mixed* base-`2^32` fold
`MulModFold32N` (163/165) rather than the base-`2^64` `MulModFold` (176/178):
`b` is re-read at the even base-`2^32` positions, which costs nothing.

The quotient-inverted folded certificate saves one allocation and one row
relative to the ordinary `MulModFold32N` endpoint.
-/

namespace Solution.Secp256k1ScalarMul
namespace MulModSub2W32N

open Specs.ShortWeierstrass Specs.Secp256k1

/-- Product-cell cap of the mixed fold: `a` has widened 32-bit limbs and `b`
triply unreduced 64-bit limbs; only the four even positions of the expanded
`b` are nonzero, so a cell is below `4·(2^33−1)·3·2^64 ≤ 3·2^99`. -/
lemma hcapN : 4 * ((2 ^ 32) * (3 * 2 ^ 64)) ≤ 3 * 2 ^ 98 := by
  norm_num

structure Inputs (F : Type) where
  a : BigInt 8 F
  b : Emu F
  s1 : Emu F
  s2 : Emu F
deriving ProvableStruct

def main (input : Var Inputs (F circomPrime)) :
    Circuit (F circomPrime) (Var Emu (F circomPrime)) := do
  let { a, b, s1, s2 } := input

  let r ← ProvableType.witness (α := Emu) fun env =>
    emuOfNat (((BigInt.value 32 (Vector.map (Expression.eval env.toEnvironment) a) : ℕ)
        : Specs.Secp256k1.Fp)
        * ((evalEmu env b : ℕ)
          : Specs.Secp256k1.Fp)
        - ((evalEmu env s1 : ℕ) : Specs.Secp256k1.Fp)
        - ((evalEmu env s2 : ℕ) : Specs.Secp256k1.Fp)).val

  ValidP.circuit r

  MulModFold32N.circuitInv (2 ^ 32) (3 * 2 ^ 64) hcapN
    { a := a, b := MulModFold32N.expand32 b,
      target := Vector.ofFn fun k : Fin numLimbs =>
        r[k.val]'k.isLt + s1[k.val]'k.isLt + s2[k.val]'k.isLt }

  return r

instance elaborated : ElaboratedCircuit (F circomPrime) Inputs Emu main := by
  elaborate_circuit

def Assumptions (input : Inputs (F circomPrime)) : Prop :=
  BigInt.Normalized 32 input.a ∧ (∀ i : Fin numLimbs, (input.b[i.val]).val < 3 * 2 ^ limbBits) ∧
    Fe.Valid input.s1 ∧ Fe.Valid input.s2

def Spec (input : Inputs (F circomPrime)) (out : Emu (F circomPrime)) : Prop :=
  Fe.Valid out ∧
    decodeFe out = decodeFe (Limbs32.emuOf32V input.a) * decodeFe input.b
      - decodeFe input.s1 - decodeFe input.s2

theorem soundness : Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [ValidP.circuit, ValidP.main, ValidP.Assumptions, ValidP.Spec,
    MulModFold32N.circuitInv, MulModFold32N.Assumptions, MulModFold32N.Spec]
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
  have hbv : BigInt.value 32
        (Vector.map (Expression.eval env) (MulModFold32N.expand32 input_var_b))
      = BigInt.value limbBits (Vector.map (Expression.eval env) input_var_b) := by
    rw [MulModFold32N.eval_expand32, MulModFold32N.value_expand32]
  have hexp_limb : ∀ i : Fin 8,
      (Expression.eval env ((MulModFold32N.expand32 input_var_b)[i.val])).val
        < 3 * 2 ^ 64 := by
    have hb' : ∀ j : Fin numLimbs,
        ((Vector.map (Expression.eval env) input_var_b)[j.val]'j.isLt).val
          < 3 * 2 ^ 64 := by
      intro j; rw [h_input_b]; exact hb_valid j
    intro i
    have h := MulModFold32N.expand32V_lt (C := 3 * 2 ^ 64) (by positivity) hb' i
    rw [← MulModFold32N.eval_expand32] at h
    simpa [Vector.getElem_map] using h
  have hspec := hcert ⟨ha_valid, hexp_limb,
    MulModFold32N.eval_expand32_odd_zero env input_var_b, ?_, ?_⟩
  · -- conclude the spec from the congruence
    rw [ht_eval, CompleteAdd.value_sum3 _ _ _ hr_norm hs1_norm hs2_norm,
      h_input_s1, h_input_s2, hbv, h_input_b] at hspec
    refine ⟨⟨hr_norm, hr_lt⟩, ?_⟩
    rw [decodeFe_emuOf32V_33 (fun i => lt_trans (ha_valid i) (by norm_num [widen33]))]
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

set_option maxRecDepth 8000 in
theorem completeness : Completeness (F circomPrime) main Assumptions := by
  circuit_proof_start [ValidP.circuit, ValidP.main, ValidP.Assumptions, ValidP.Spec,
    MulModFold32N.circuitInv, MulModFold32N.Assumptions, MulModFold32N.Spec]
  obtain ⟨ha_valid, hb_valid, hs1_valid, hs2_valid⟩ := h_assumptions
  obtain ⟨h_input_a, h_input_b, h_input_s1, h_input_s2⟩ := h_input
  have hr := h_env
  have hev_a : BigInt.value 32 (Vector.map (Expression.eval env.toEnvironment) input_var_a)
      = BigInt.value 32 input_a := by rw [← h_input_a]
  have hev_b : evalEmu env input_var_b = BigInt.value limbBits input_b := by
    rw [evalEmu, BigInt.value, ← h_input_b]
  have hbv : BigInt.value 32
        (Vector.map (Expression.eval env.toEnvironment) (MulModFold32N.expand32 input_var_b))
      = BigInt.value limbBits (Vector.map (Expression.eval env.toEnvironment) input_var_b) := by
    rw [MulModFold32N.eval_expand32, MulModFold32N.value_expand32]
  have hexp_limb : ∀ i : Fin 8,
      (Expression.eval env.toEnvironment
        ((MulModFold32N.expand32 input_var_b)[i.val])).val < 3 * 2 ^ 64 := by
    have hb' : ∀ j : Fin numLimbs,
        ((Vector.map (Expression.eval env.toEnvironment) input_var_b)[j.val]'j.isLt).val
          < 3 * 2 ^ 64 := by
      intro j; rw [h_input_b]; exact hb_valid j
    intro i
    have h := MulModFold32N.expand32V_lt (C := 3 * 2 ^ 64) (by positivity) hb' i
    rw [← MulModFold32N.eval_expand32] at h
    simpa [Vector.getElem_map] using h
  have hev_s1 : evalEmu env input_var_s1 = BigInt.value limbBits input_s1 := by
    rw [evalEmu, BigInt.value, ← h_input_s1]
  have hev_s2 : evalEmu env input_var_s2 = BigInt.value limbBits input_s2 := by
    rw [evalEmu, BigInt.value, ← h_input_s2]
  have hr_eval : Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange numLimbs fun i => var { index := i₀ + i })
      = emuOfNat (ZMod.val (((BigInt.value 32 input_a : ℕ) : Specs.Secp256k1.Fp)
          * ((BigInt.value limbBits input_b : ℕ) : Specs.Secp256k1.Fp)
          - ((BigInt.value limbBits input_s1 : ℕ) : Specs.Secp256k1.Fp)
          - ((BigInt.value limbBits input_s2 : ℕ) : Specs.Secp256k1.Fp))) := by
    rw [← hev_s1, ← hev_s2, ← hev_b]
    apply Vector.ext
    intro k hk
    have hentry : (Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange numLimbs fun i => var { index := i₀ + i }))[k]'hk
        = env.get (i₀ + k) := by
      simp [circuit_norm]
    rw [hentry]
    simpa using hr ⟨k, hk⟩
  have hr_lt : ZMod.val (((BigInt.value 32 input_a : ℕ) : Specs.Secp256k1.Fp)
      * ((BigInt.value limbBits input_b : ℕ) : Specs.Secp256k1.Fp)
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
          * ((BigInt.value limbBits input_b : ℕ) : Specs.Secp256k1.Fp)
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
    ⟨ha_valid, hexp_limb,
      MulModFold32N.eval_expand32_odd_zero env.toEnvironment input_var_b, ?_, ?_⟩, ?_⟩
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
      h_input_s1, h_input_s2, hbv, h_input_b]
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
        * ((evalEmu env b : ℕ)
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
      evalEmu e b = evalEmu e' b ∧
      evalEmu e s1 = evalEmu e' s1 ∧ evalEmu e s2 = evalEmu e' s2 := by
    intro e e' h_input
    exact ⟨MulMod.bigInt_map_eval_eq_of_eval_eq (by
        simpa [circuit_norm] using congrArg (fun x : Inputs (F circomPrime) => x.a) h_input),
      evalEmu_eq_of_eval_eq (by
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
      (MulModFold32N.circuitInv (2 ^ 32) (3 * 2 ^ 64) hcapN) _
      { a := a, b := MulModFold32N.expand32 b,
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
        rw [MulModFold32N.Inputs.mk.injEq]
        refine ⟨ha, ?_, ?_⟩
        · rw [MulModFold32N.eval_expand32, MulModFold32N.eval_expand32]
          exact congrArg MulModFold32N.expand32V hb
        apply Vector.ext
        intro i hi
        simp only [Vector.getElem_map, Vector.getElem_ofFn]
        simp only [Expression.eval, hr_cell i hi, hcell s1 hs1 i hi, hcell s2 hs2 i hi])
      (MulModFold32N.computableWitnessesInv (2 ^ 32) (3 * 2 ^ 64) hcapN) env env'

lemma eval_output_of_agreesBelow (input : Var Inputs (F circomPrime)) {offset k : ℕ}
    {env env' : ProverEnvironment (F circomPrime)}
    (h_agree : env.AgreesBelow k env') (hk : offset + numLimbs ≤ k) :
    eval env ((main input).output offset) = eval env' ((main input).output offset) := by
  have hout : (main input).output offset
      = (ProvableType.witness (α := Emu) fun env =>
          emuOfNat (((BigInt.value 32 (Vector.map (Expression.eval env.toEnvironment) input.a) : ℕ)
              : Specs.Secp256k1.Fp)
              * ((evalEmu env input.b : ℕ)
                : Specs.Secp256k1.Fp)
              - ((evalEmu env input.s1 : ℕ) : Specs.Secp256k1.Fp)
              - ((evalEmu env input.s2 : ℕ) : Specs.Secp256k1.Fp)).val).output offset := rfl
  rw [hout]
  exact AddMod.emuWitnessOutput_stable _ h_agree hk

end MulModSub2W32N
end Solution.Secp256k1ScalarMul
