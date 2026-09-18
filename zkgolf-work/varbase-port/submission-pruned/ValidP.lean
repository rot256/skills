import Solution.Secp256k1ScalarMul.ValidPMerge
import Solution.Secp256k1ScalarMul.IsZeroFe
import Solution.Secp256k1ScalarMul.ToBitsAffine
import Challenge.Utils.ComputableWitnessLemmas

/-!
# secp256k1-specific canonical field validation

Every field-result gadget used to run `Normalize` and then the generic
`LessThan` gadget against `p`.  That decomposes 256 result bits once and then
allocates another 256-bit difference.  Here the four limb decompositions are
kept in scope and compared with the constant

`p = 2^256 - 2^32 - 977`.

The binary representation of `p` has only six zero positions:
`32, 9, 8, 7, 6, 4`.  Three zero tests summarize the long all-one runs and two
product witnesses carry the equal-prefix state.  The resulting assertion has
264 witnesses and 272 rows, versus 520 witnesses and 529 rows for
`Normalize + LessThan`.
-/

namespace Solution.Secp256k1ScalarMul
namespace ValidP

open Utils.Bits

/-- Sparse comparison against the secp256k1 prime after the four limbs have
already been decomposed into bits. -/
def tail (b0 b1 b2 b3 : Var (fields limbBits) (F circomPrime)) :
    Circuit (F circomPrime) Unit := do
  -- p has ones at every position 255..33.  A zero in this run makes x < p.
  let topDef := deficitSlice b0 33 31 (by decide)
    + deficitSlice b1 0 64 (by decide)
    + deficitSlice b2 0 64 (by decide)
    + deficitSlice b3 0 64 (by decide)
  let topEq ← Gadgets.IsZeroField.circuit topDef

  -- The remaining sparse comparison conditions are nested into two products.
  -- All leaves are boolean, so the final sum can vanish only when every active
  -- forbidden bit/equality flag vanishes.  This replaces five rows by three.
  let midDef := deficitSlice b0 10 22 (by decide)
  let midEq ← Gadgets.IsZeroField.circuit midDef
  let lowDef := deficitSlice b0 0 4 (by decide)
  let lowEq ← Gadgets.IsZeroField.circuit lowDef
  let u <== b0[5] * (b0[4] + lowEq)
  let v <== midEq * (b0[9] + b0[8] + b0[7] + b0[6] + u)
  assertZero (topEq * (b0[32] + v))

/-- Normalize four 64-bit limbs and prove their 256-bit value is below the
secp256k1 base-field prime using its sparse complement. -/
def main (x : Var Emu (F circomPrime)) : Circuit (F circomPrime) Unit := do
  let b0 ← ToBitsAffine.toBitsAffine 63 secpParams.hB x[0]
  let b1 ← ToBitsAffine.toBitsAffine 63 secpParams.hB x[1]
  let b2 ← ToBitsAffine.toBitsAffine 63 secpParams.hB x[2]
  let b3 ← ToBitsAffine.toBitsAffine 63 secpParams.hB x[3]
  tail b0 b1 b2 b3

instance elaborated : ElaboratedCircuit (F circomPrime) Emu unit main := by
  elaborate_circuit

def Assumptions (_x : Emu (F circomPrime)) : Prop := True

def Spec (x : Emu (F circomPrime)) : Prop := Fe.Valid x

set_option maxHeartbeats 2000000 in
theorem soundness :
    FormalAssertion.Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [tail, ToBitsAffine.toBitsAffine, ToBitsAffine.main,
    Gadgets.IsZeroField.circuit,
    Gadgets.IsZeroField.Assumptions, Gadgets.IsZeroField.Spec]
  obtain ⟨⟨hn0, hb0⟩, ⟨hn1, hb1⟩, ⟨hn2, hb2⟩, ⟨hn3, hb3⟩,
    htopEq, hmidEq, hlowEq, hu, hv, hmerged⟩ := h_holds
  have hx : ∀ (i : ℕ) (hi : i < 4), Expression.eval env input_var[i] = input[i] := by
    intro i hi
    rw [← h_input, Vector.getElem_map]
  rw [hx 0 (by omega)] at hn0 hb0
  rw [hx 1 (by omega)] at hn1 hb1
  rw [hx 2 (by omega)] at hn2 hb2
  rw [hx 3 (by omega)] at hn3 hb3
  have hn : BigInt.Normalized limbBits input := by
    intro i
    fin_cases i <;> assumption
  rw [eval_ds (by decide) env _ input[0] hb0,
    eval_ds (by decide) env _ input[1] hb1,
    eval_ds (by decide) env _ input[2] hb2,
    eval_ds (by decide) env _ input[3] hb3] at htopEq
  rw [eval_ds (by decide) env _ input[0] hb0] at hmidEq hlowEq
  simp only [top_count_cast_zero_iff] at htopEq
  change _ = if topDC input = 0 then 1 else 0 at htopEq
  simp only [mid_cast_zero_iff input] at hmidEq
  simp only [low_cast_zero_iff input] at hlowEq
  have hb0val : ∀ (i : ℕ) (hi : i < 63),
      env.get (i₀ + i) = if input[0].val.testBit i then 1 else 0 := by
    exact fun i hi => push_eval_bit env i₀ _ input[0] hb0 i hi
  have hu' : env.get (i₀ + 63 + 63 + 63 + 63 + 2 + 2 + 2) =
      bitField (input[0].val.testBit 5) *
        (bitField (input[0].val.testBit 4) +
          env.get (i₀ + 63 + 63 + 63 + 63 + 2 + 2 + 1)) := by
    rw [bitField, ← hb0val 5 (by omega), bitField, ← hb0val 4 (by omega)]
    exact hu
  have hv' : env.get (i₀ + 63 + 63 + 63 + 63 + 2 + 2 + 2 + 1) =
      env.get (i₀ + 63 + 63 + 63 + 63 + 2 + 1) *
        (bitField (input[0].val.testBit 9) + bitField (input[0].val.testBit 8) +
          bitField (input[0].val.testBit 7) + bitField (input[0].val.testBit 6) +
          env.get (i₀ + 63 + 63 + 63 + 63 + 2 + 2 + 2)) := by
    rw [bitField, ← hb0val 9 (by omega), bitField, ← hb0val 8 (by omega),
      bitField, ← hb0val 7 (by omega), bitField, ← hb0val 6 (by omega)]
    exact hv
  have hmerged' : env.get (i₀ + 63 + 63 + 63 + 63 + 1) *
      (bitField (input[0].val.testBit 32) +
        env.get (i₀ + 63 + 63 + 63 + 63 + 2 + 2 + 2 + 1)) = 0 := by
    rw [bitField, ← hb0val 32 (by omega)]
    exact hmerged
  have hpatt : Pattern input :=
    pattern_of_merged input htopEq hmidEq hlowEq hu' hv' hmerged'
  exact ⟨hn, (pattern_iff_lt input hn).mp hpatt⟩

set_option maxHeartbeats 0 in
theorem completeness :
    FormalAssertion.Completeness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [tail, ToBitsAffine.toBitsAffine, ToBitsAffine.main,
    Gadgets.IsZeroField.circuit,
    Gadgets.IsZeroField.Assumptions, Gadgets.IsZeroField.Spec]
  obtain ⟨hb0gen, hb1gen, hb2gen, hb3gen, htopEq, hmidEq, hlowEq, hu, hv⟩ := h_env
  have hx : ∀ (i : ℕ) (hi : i < 4),
      Expression.eval env.toEnvironment input_var[i] = input[i] := by
    intro i hi
    rw [← h_input, Vector.getElem_map]
  have hn := h_spec.1
  have hn0 : (Expression.eval env.toEnvironment input_var[0]).val < 2 ^ limbBits := by
    rw [hx 0 (by omega)]
    exact hn 0
  have hn1 : (Expression.eval env.toEnvironment input_var[1]).val < 2 ^ limbBits := by
    rw [hx 1 (by omega)]
    exact hn 1
  have hn2 : (Expression.eval env.toEnvironment input_var[2]).val < 2 ^ limbBits := by
    rw [hx 2 (by omega)]
    exact hn 2
  have hn3 : (Expression.eval env.toEnvironment input_var[3]).val < 2 ^ limbBits := by
    rw [hx 3 (by omega)]
    exact hn 3
  obtain ⟨-, hb0⟩ := hb0gen hn0
  obtain ⟨-, hb1⟩ := hb1gen hn1
  obtain ⟨-, hb2⟩ := hb2gen hn2
  obtain ⟨-, hb3⟩ := hb3gen hn3
  rw [hx 0 (by omega)] at hb0
  rw [hx 1 (by omega)] at hb1
  rw [hx 2 (by omega)] at hb2
  rw [hx 3 (by omega)] at hb3
  rw [eval_ds (by decide) env.toEnvironment _ input[0] hb0,
    eval_ds (by decide) env.toEnvironment _ input[1] hb1,
    eval_ds (by decide) env.toEnvironment _ input[2] hb2,
    eval_ds (by decide) env.toEnvironment _ input[3] hb3] at htopEq
  rw [eval_ds (by decide) env.toEnvironment _ input[0] hb0] at hmidEq hlowEq
  simp only [top_count_cast_zero_iff] at htopEq
  change _ = if topDC input = 0 then 1 else 0 at htopEq
  simp only [mid_cast_zero_iff input] at hmidEq
  simp only [low_cast_zero_iff input] at hlowEq
  have hb0val : ∀ (i : ℕ) (hi : i < 63),
      env.get (i₀ + i) = if input[0].val.testBit i then 1 else 0 := by
    exact fun i hi => push_eval_bit env.toEnvironment i₀ _ input[0] hb0 i hi
  have hu' : env.get (i₀ + 63 + 63 + 63 + 63 + 2 + 2 + 2) =
      bitField (input[0].val.testBit 5) *
        (bitField (input[0].val.testBit 4) +
          env.get (i₀ + 63 + 63 + 63 + 63 + 2 + 2 + 1)) := by
    rw [bitField, ← hb0val 5 (by omega), bitField, ← hb0val 4 (by omega)]
    exact hu
  have hv' : env.get (i₀ + 63 + 63 + 63 + 63 + 2 + 2 + 2 + 1) =
      env.get (i₀ + 63 + 63 + 63 + 63 + 2 + 1) *
        (bitField (input[0].val.testBit 9) + bitField (input[0].val.testBit 8) +
          bitField (input[0].val.testBit 7) + bitField (input[0].val.testBit 6) +
          env.get (i₀ + 63 + 63 + 63 + 63 + 2 + 2 + 2)) := by
    rw [bitField, ← hb0val 9 (by omega), bitField, ← hb0val 8 (by omega),
      bitField, ← hb0val 7 (by omega), bitField, ← hb0val 6 (by omega)]
    exact hv
  have hpatt : Pattern input := (pattern_iff_lt input hn).mpr h_spec.2
  have hmerged := merged_of_pattern input htopEq hmidEq hlowEq hu' hv' hpatt
  rw [bitField, ← hb0val 32 (by omega)] at hmerged
  refine ⟨hn0, hn1, hn2, hn3, hu, hv, ?_⟩
  exact hmerged

def circuit : FormalAssertion (F circomPrime) Emu where
  main
  elaborated
  Assumptions
  Spec
  soundness
  completeness

/-! ## Computable witnesses -/

private lemma input_limb_stable {input : Var Emu (F circomPrime)} {i : ℕ} (hi : i < numLimbs)
    {env env' : ProverEnvironment (F circomPrime)}
    (h : eval env input = eval env' input) :
    eval env input[i] = eval env' input[i] := by
  have hmap := emu_map_eval_eq_of_eval_eq h
  have hget : (input.map (Expression.eval env.toEnvironment))[i] =
      (input.map (Expression.eval env'.toEnvironment))[i] := by rw [hmap]
  simp only [Vector.getElem_map] at hget
  rw [CircuitType.eval_var_field_prover, CircuitType.eval_var_field_prover]
  exact hget

private lemma input_limb_stable' {input : Var Emu (F circomPrime)} {i : ℕ} (hi : i < numLimbs)
    {env env' : ProverEnvironment (F circomPrime)}
    (h : eval env input = eval env' input) :
    Expression.eval env.toEnvironment input[i] = Expression.eval env'.toEnvironment input[i] := by
  have hstep := input_limb_stable hi h
  rwa [CircuitType.eval_var_field_prover, CircuitType.eval_var_field_prover] at hstep

/-- The affine top expression of the limb `k` decomposition is stable under
environment agreement below `k`, given the limb input is stable. -/
private lemma top_eval_stable {base k : ℕ} {env env' : ProverEnvironment (F circomPrime)}
    (inp : Expression (F circomPrime))
    (h_agree : env.AgreesBelow k env') (hk : base + 63 ≤ k)
    (hinp : Expression.eval env.toEnvironment inp = Expression.eval env'.toEnvironment inp) :
    Expression.eval env.toEnvironment
        (Expression.const (((2 ^ 63 : ℕ) : F circomPrime)⁻¹) *
          (inp - fieldFromBitsExpr (Vector.mapRange 63 fun i => var { index := base + i }))) =
      Expression.eval env'.toEnvironment
        (Expression.const (((2 ^ 63 : ℕ) : F circomPrime)⁻¹) *
          (inp - fieldFromBitsExpr (Vector.mapRange 63 fun i => var { index := base + i }))) := by
  simp only [Expression.eval, hinp]
  have hmeq : (Vector.mapRange 63 fun i => var { index := base + i }).map env.toEnvironment
      = (Vector.mapRange 63 fun i => var { index := base + i }).map env'.toEnvironment := by
    apply Vector.ext; intro j hj
    simp only [Vector.getElem_map, Vector.getElem_mapRange, Expression.eval]
    exact h_agree (base + j) (by omega)
  have hE1 : Expression.eval env.toEnvironment
      (fieldFromBitsExpr (Vector.mapRange 63 fun i => var { index := base + i })) =
        fieldFromBits ((Vector.mapRange 63 fun i => var { index := base + i }).map env.toEnvironment) :=
    fieldFromBits_eval _
  have hE2 : Expression.eval env'.toEnvironment
      (fieldFromBitsExpr (Vector.mapRange 63 fun i => var { index := base + i })) =
        fieldFromBits ((Vector.mapRange 63 fun i => var { index := base + i }).map env'.toEnvironment) :=
    fieldFromBits_eval _
  rw [hE1, hE2, hmeq]

/-- Stability of a deficit slice over the affine-top vector.  Low cells are
plain witnesses; the top cell (index 63) is the affine residual, whose stability
is supplied by `htop`. -/
private lemma deficitSlice_push_eval_stable {base k start len : ℕ}
    (h : start + len ≤ limbBits) (top : Expression (F circomPrime))
    {env env' : ProverEnvironment (F circomPrime)}
    (h_agree : env.AgreesBelow k env') (hk : base + 63 ≤ k)
    (htop : Expression.eval env.toEnvironment top = Expression.eval env'.toEnvironment top) :
    Expression.eval env.toEnvironment
        (deficitSlice ((Vector.mapRange 63 fun i => var { index := base + i }).push top) start len h) =
      Expression.eval env'.toEnvironment
        (deficitSlice ((Vector.mapRange 63 fun i => var { index := base + i }).push top) start len h) := by
  have h64 : start + len ≤ 64 := h
  unfold deficitSlice
  rw [eval_fold, eval_fold]
  have hcells : ∀ (j : ℕ) (hj : j < 63 + 1),
      Expression.eval env.toEnvironment
        (((Vector.mapRange 63 fun m => var { index := base + m }).push top)[j]'hj) =
      Expression.eval env'.toEnvironment
        (((Vector.mapRange 63 fun m => var { index := base + m }).push top)[j]'hj) := by
    intro j hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
    · simp only [Vector.getElem_push_lt hlt, Vector.getElem_mapRange, Expression.eval]
      rw [h_agree (base + j) (by omega)]
    · simp only [Vector.getElem_push_eq]
      exact htop
  apply Finset.sum_congr rfl
  intro i _
  have hi := i.isLt
  simp only [Expression.eval]
  rw [hcells (start + i.val) (by omega)]

theorem computableWitnesses : circuit.base.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  have hT : ∀ (y : Expression (F circomPrime)) (o : ℕ),
      (subcircuitWithAssertion
        (ToBitsAffine.toBitsAffine 63 secpParams.hB) y).localLength o = 63 := by
    intro y o
    simp [subcircuitWithAssertion, ToBitsAffine.toBitsAffine, ToBitsAffine.main,
      circuit_norm]
  have hZ : ∀ (y : Expression (F circomPrime)) (o : ℕ),
      (subcircuit Gadgets.IsZeroField.circuit y).localLength o = 2 := by
    intro y o
    simp only [circuit_norm, Gadgets.IsZeroField.circuit]
  have hA : ∀ (r : Var field (F circomPrime)) (o : ℕ),
      (HasAssignEq.assignEq (β := field (Expression (F circomPrime))) r).localLength o = 1 := by
    intro r o
    simp only [circuit_norm, HasAssignEq.assignEq]
  have h0 : ∀ (r : Expression (F circomPrime)) (o : ℕ),
      (assertZero r).localLength o = 0 := by
    intro r o
    simp only [circuit_norm]
  let bitsCircuit := ToBitsAffine.toBitsAffine 63 secpParams.hB
  let b0 := (subcircuitWithAssertion bitsCircuit input[0]).output offset
  let b1 := (subcircuitWithAssertion bitsCircuit input[1]).output (offset + 63)
  let b2 := (subcircuitWithAssertion bitsCircuit input[2]).output
    (offset + 63 + 63)
  let b3 := (subcircuitWithAssertion bitsCircuit input[3]).output
    (offset + 63 + 63 + 63)
  let topOff := offset + 63 + 63 + 63 + 63
  let topDef := deficitSlice b0 33 31 (by decide) + deficitSlice b1 0 64 (by decide) +
    deficitSlice b2 0 64 (by decide) + deficitSlice b3 0 64 (by decide)
  let topEq := (subcircuit Gadgets.IsZeroField.circuit topDef).output topOff
  let midOff := topOff + 2
  let midDef := deficitSlice b0 10 22 (by decide)
  let midEq := (subcircuit Gadgets.IsZeroField.circuit midDef).output midOff
  let lowOff := midOff + 2
  let lowDef := deficitSlice b0 0 4 (by decide)
  let lowEq := (subcircuit Gadgets.IsZeroField.circuit lowDef).output lowOff
  let uOff := lowOff + 2
  let uExpr := b0[5] * (b0[4] + lowEq)
  let u := (HasAssignEq.assignEq
    (β := field (Expression (F circomPrime))) uExpr).output uOff
  let vOff := uOff + 1
  let vExpr := midEq * (b0[9] + b0[8] + b0[7] + b0[6] + u)
  unfold main tail
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.assertZero_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.pure_structuralComputableWitnesses_iff,
    subcircuitWithAssertion,
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.StructuralComputableWitnesses,
    hT, hZ, hA, h0, and_true]
  and_intros
  all_goals try trivial
  · exact Challenge.Utils.ComputableWitnessLemmas.GeneralFormalCircuit.subcircuit_flatStructuralComputableWitnesses
      (ToBitsAffine.toBitsAffine 63 secpParams.hB) input input[0] offset
      (fun _ _ hinput => input_limb_stable (by decide) hinput)
      (ToBitsAffine.computableWitnesses 63 secpParams.hB) env env'
  · exact Challenge.Utils.ComputableWitnessLemmas.GeneralFormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (ToBitsAffine.toBitsAffine 63 secpParams.hB) input input[1] (offset + 63)
      (fun _ _ _ _ _ hinput => input_limb_stable (by decide) hinput)
      (ToBitsAffine.computableWitnesses 63 secpParams.hB) env env'
  · exact Challenge.Utils.ComputableWitnessLemmas.GeneralFormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (ToBitsAffine.toBitsAffine 63 secpParams.hB) input input[2] (offset + 63 + 63)
      (fun _ _ _ _ _ hinput => input_limb_stable (by decide) hinput)
      (ToBitsAffine.computableWitnesses 63 secpParams.hB) env env'
  · exact Challenge.Utils.ComputableWitnessLemmas.GeneralFormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (ToBitsAffine.toBitsAffine 63 secpParams.hB) input input[3] (offset + 63 + 63 + 63)
      (fun _ _ _ _ _ hinput => input_limb_stable (by decide) hinput)
      (ToBitsAffine.computableWitnesses 63 secpParams.hB) env env'
  · refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      Gadgets.IsZeroField.circuit input _ _ ?_ IsZeroFe.isZeroFieldComputableWitnesses env env'
    intro k env₁ env₂ hk h_agree hcond
    have hi0 := input_limb_stable' (i := 0) (by decide) hcond
    have hi1 := input_limb_stable' (i := 1) (by decide) hcond
    have hi2 := input_limb_stable' (i := 2) (by decide) hcond
    have hi3 := input_limb_stable' (i := 3) (by decide) hcond
    simp only [circuit_norm, ToBitsAffine.toBitsAffine, ToBitsAffine.main]
    rw [deficitSlice_push_eval_stable (base := offset) (start := 33) (len := 31)
        (by decide) _ h_agree (by omega) (top_eval_stable (base := offset) input[0] h_agree (by omega) hi0),
      deficitSlice_push_eval_stable (base := offset + 63) (start := 0) (len := 64)
        (by decide) _ h_agree (by omega) (top_eval_stable (base := offset + 63) input[1] h_agree (by omega) hi1),
      deficitSlice_push_eval_stable (base := offset + 63 + 63) (start := 0) (len := 64)
        (by decide) _ h_agree (by omega) (top_eval_stable (base := offset + 63 + 63) input[2] h_agree (by omega) hi2),
      deficitSlice_push_eval_stable (base := offset + 63 + 63 + 63)
        (start := 0) (len := 64) (by decide) _ h_agree (by omega)
        (top_eval_stable (base := offset + 63 + 63 + 63) input[3] h_agree (by omega) hi3)]
  · refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      Gadgets.IsZeroField.circuit input _ _ ?_ IsZeroFe.isZeroFieldComputableWitnesses env env'
    intro k env₁ env₂ hk h_agree hcond
    have hi0 := input_limb_stable' (i := 0) (by decide) hcond
    simp only [circuit_norm, ToBitsAffine.toBitsAffine, ToBitsAffine.main]
    rw [deficitSlice_push_eval_stable (base := offset) (start := 10) (len := 22)
      (by decide) _ h_agree (by omega) (top_eval_stable (base := offset) input[0] h_agree (by omega) hi0)]
  · refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      Gadgets.IsZeroField.circuit input _ _ ?_ IsZeroFe.isZeroFieldComputableWitnesses env env'
    intro k env₁ env₂ hk h_agree hcond
    have hi0 := input_limb_stable' (i := 0) (by decide) hcond
    simp only [circuit_norm, ToBitsAffine.toBitsAffine, ToBitsAffine.main]
    rw [deficitSlice_push_eval_stable (base := offset) (start := 0) (len := 4)
      (by decide) _ h_agree (by omega) (top_eval_stable (base := offset) input[0] h_agree (by omega) hi0)]
  · intro h_agree _
    refine congrArg (fun x : F circomPrime => #v[x]) ?_
    have h5 : Expression.eval env.toEnvironment b0[5] =
        Expression.eval env'.toEnvironment b0[5] := by
      dsimp only [b0, bitsCircuit]
      simp only [circuit_norm, ToBitsAffine.toBitsAffine, ToBitsAffine.main,
        Vector.getElem_push_lt, Vector.getElem_mapRange, Expression.eval]
      exact h_agree (offset + 5) (by omega)
    have h4 : Expression.eval env.toEnvironment b0[4] =
        Expression.eval env'.toEnvironment b0[4] := by
      dsimp only [b0, bitsCircuit]
      simp only [circuit_norm, ToBitsAffine.toBitsAffine, ToBitsAffine.main,
        Vector.getElem_push_lt, Vector.getElem_mapRange, Expression.eval]
      exact h_agree (offset + 4) (by omega)
    have hlo := IsZeroFe.isZeroField_output_eval_stable lowDef
      (base := lowOff) h_agree (by omega)
    simpa only [CircuitType.eval_var_field_prover, Expression.eval, uExpr, lowEq,
      lowDef, lowOff, b0, bitsCircuit] using
      congrArg₂ (fun a b : F circomPrime => a * b) h5
        (congrArg₂ (fun a b : F circomPrime => a + b) h4 hlo)
  · exact IsZeroFe.equalityFieldSubcircuit_flatStructural_any input _ _ _ env env'
  · intro h_agree _
    refine congrArg (fun x : F circomPrime => #v[x]) ?_
    have hmid := IsZeroFe.isZeroField_output_eval_stable midDef
      (base := midOff) h_agree (by omega)
    have h9 : Expression.eval env.toEnvironment b0[9] =
        Expression.eval env'.toEnvironment b0[9] := by
      dsimp only [b0, bitsCircuit]
      simp only [circuit_norm, ToBitsAffine.toBitsAffine, Vector.getElem_push_lt,
        Vector.getElem_mapRange, Expression.eval]
      exact h_agree (offset + 9) (by omega)
    have h8 : Expression.eval env.toEnvironment b0[8] =
        Expression.eval env'.toEnvironment b0[8] := by
      dsimp only [b0, bitsCircuit]
      simp only [circuit_norm, ToBitsAffine.toBitsAffine, Vector.getElem_push_lt,
        Vector.getElem_mapRange, Expression.eval]
      exact h_agree (offset + 8) (by omega)
    have h7 : Expression.eval env.toEnvironment b0[7] =
        Expression.eval env'.toEnvironment b0[7] := by
      dsimp only [b0, bitsCircuit]
      simp only [circuit_norm, ToBitsAffine.toBitsAffine, Vector.getElem_push_lt,
        Vector.getElem_mapRange, Expression.eval]
      exact h_agree (offset + 7) (by omega)
    have h6 : Expression.eval env.toEnvironment b0[6] =
        Expression.eval env'.toEnvironment b0[6] := by
      dsimp only [b0, bitsCircuit]
      simp only [circuit_norm, ToBitsAffine.toBitsAffine, Vector.getElem_push_lt,
        Vector.getElem_mapRange, Expression.eval]
      exact h_agree (offset + 6) (by omega)
    have hu := IsZeroFe.assignEq_output_eval_stable uExpr
      (base := uOff) h_agree (by
        simp only [circuit_norm, HasAssignEq.assignEq]
        dsimp only [uOff, lowOff, midOff, topOff]
        omega)
    have h98 := congrArg₂ (fun a b : F circomPrime => a + b) h9 h8
    have h987 := congrArg₂ (fun a b : F circomPrime => a + b) h98 h7
    have h9876 := congrArg₂ (fun a b : F circomPrime => a + b) h987 h6
    have hsum := congrArg₂ (fun a b : F circomPrime => a + b) h9876 hu
    simpa only [Expression.eval] using
      congrArg₂ (fun a b : F circomPrime => a * b) hmid hsum
  · exact IsZeroFe.equalityFieldSubcircuit_flatStructural_any input _ _ _ env env'
  all_goals try trivial

end ValidP
end Solution.Secp256k1ScalarMul
