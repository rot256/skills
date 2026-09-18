import Solution.Secp256k1ScalarMul.SubModTheorems
import Challenge.Utils.ComputableWitnessLemmas
import Solution.Secp256k1ScalarMul.AddMod
import Solution.Secp256k1ScalarMul.ValidP



namespace Solution.Secp256k1ScalarMul
namespace SubMod


structure Inputs (F : Type) where
  a : Emu F
  b : Emu F
deriving ProvableStruct

def main (input : Var Inputs (F circomPrime)) :
    Circuit (F circomPrime) (Var Emu (F circomPrime)) := do
  let { a, b } := input

  -- witness r = (a + P256 - b) % P256 and the borrow bit
  let r ← ProvableType.witness (α := Emu) fun env =>
    emuOfNat ((evalEmu env a + P256 - evalEmu env b) % P256)
  let q ← ProvableType.witness (α := field) fun env =>
    (((if evalEmu env a < evalEmu env b then 1 else 0 : ℕ)) : F circomPrime)

  -- q is boolean
  assertZero (q * (q - 1))

  -- r is normalized and canonical, using the sparse shape of secp256k1's p.
  ValidP.circuit r

  -- r + b = a + q·P256 as integers, limb-coefficient-wise.
  -- Width-5 vector; every coefficient is additive-scale (`< 2^65 + 2`), so the
  -- narrow-carry `EqViaCarriesN` (`eqNParamsAdd`) runs each offset carry at
  -- 3 bits instead of the multiplication width 69.
  let lhs : Vector (Expression (F circomPrime)) (2 * 3 - 1) :=
    Vector.mapFinRange (2 * 3 - 1) fun k =>
      if h : k.val < numLimbs then r[k.val]'h + b[k.val]'h else 0
  let rhs : Vector (Expression (F circomPrime)) (2 * 3 - 1) :=
    Vector.mapFinRange (2 * 3 - 1) fun k =>
      if h : k.val < numLimbs then a[k.val]'h + q * pConst[k.val]'h else 0
  EqViaCarriesN.circuit eqNParamsAdd { lhs := lhs, rhs := rhs }

  return r

instance elaborated : ElaboratedCircuit (F circomPrime) Inputs Emu main := by
  elaborate_circuit


def Assumptions (input : Inputs (F circomPrime)) : Prop :=
  Fe.Valid input.a ∧ Fe.Valid input.b


def Spec (input : Inputs (F circomPrime)) (out : Emu (F circomPrime)) : Prop :=
  Fe.Valid out ∧ decodeFe out = decodeFe input.a - decodeFe input.b

theorem soundness : Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [ValidP.circuit, ValidP.main, ValidP.Assumptions, ValidP.Spec,
    EqViaCarriesN.circuit, EqViaCarriesN.elaborated, EqViaCarriesN.main,
    EqViaCarriesN.Assumptions, EqViaCarriesN.Spec]
  obtain ⟨hq_bool, hr_valid, h_eq_impl⟩ := h_holds
  apply soundness_coreN i₀ env input_var_a input_var_b input_a input_b
    h_input.1 h_input.2 h_assumptions.1 h_assumptions.2 hq_bool hr_valid.1
  · intro _
    rw [pConst_value env]
    exact hr_valid.2
  · exact h_eq_impl

theorem completeness : Completeness (F circomPrime) main Assumptions := by
  circuit_proof_start [ValidP.circuit, ValidP.main, ValidP.Assumptions, ValidP.Spec,
    EqViaCarriesN.circuit, EqViaCarriesN.elaborated, EqViaCarriesN.main,
    EqViaCarriesN.Assumptions, EqViaCarriesN.Spec]
  have heva : evalEmu env input_var_a = BigInt.value limbBits input_a := by
    rw [evalEmu, BigInt.value, ← h_input.1]
  have hevb : evalEmu env input_var_b = BigInt.value limbBits input_b := by
    rw [evalEmu, BigInt.value, ← h_input.2]
  rw [heva, hevb] at h_env
  obtain ⟨hq, hr_norm, hr_lt, h_eq⟩ :=
    completeness_coreN i₀ env.toEnvironment input_var_a input_var_b input_a input_b
      h_input.1 h_input.2 h_assumptions.1 h_assumptions.2 h_env.1 h_env.2
  refine ⟨hq, ⟨hr_norm, ?_⟩, h_eq⟩
  rw [← pConst_value env.toEnvironment]
  exact hr_lt.2


def circuit : FormalCircuit (F circomPrime) Inputs Emu where
  main; elaborated; Assumptions; Spec; soundness; completeness

end SubMod

namespace SubMod3
open SubMod AddMod




structure Inputs (F : Type) where
  a : Emu F
  b : Emu F
  c : Emu F
deriving ProvableStruct

def main (input : Var Inputs (F circomPrime)) :
    Circuit (F circomPrime) (Var Emu (F circomPrime)) := do
  let a := input.a
  let b := input.b
  let c := input.c

  -- witness r = (a + 2·P256 − b − c) % P256, the borrow
  -- q = 2 − (a + 2·P256 − b − c)/P256 ∈ {0,1,2}, and the auxiliary t = q·(q−1)
  let r ← ProvableType.witness (α := Emu) fun env =>
    emuOfNat ((evalEmu env a + 2 * P256 - evalEmu env b - evalEmu env c) % P256)
  let q ← ProvableType.witness (α := field) fun env =>
    (((2 - (evalEmu env a + 2 * P256 - evalEmu env b - evalEmu env c) / P256 : ℕ))
      : F circomPrime)
  let t ← ProvableType.witness (α := field) fun env =>
    (((2 - (evalEmu env a + 2 * P256 - evalEmu env b - evalEmu env c) / P256 : ℕ))
        : F circomPrime)
      * ((((2 - (evalEmu env a + 2 * P256 - evalEmu env b - evalEmu env c) / P256 : ℕ))
          : F circomPrime) - 1)

  -- q ∈ {0,1,2} via t = q·(q−1) and t·(q−2) = 0
  assertZero (q * (q - 1) - t)
  assertZero (t * (q - 2))

  -- r is normalized and canonical, using the sparse shape of secp256k1's p.
  ValidP.circuit r

  -- r + b + c = a + q·P256 as integers, limb-coefficient-wise (3-sum scale).
  let lhs : Vector (Expression (F circomPrime)) (2 * 3 - 1) :=
    Vector.mapFinRange (2 * 3 - 1) fun k =>
      if h : k.val < numLimbs then r[k.val]'h + b[k.val]'h + c[k.val]'h else 0
  let rhs : Vector (Expression (F circomPrime)) (2 * 3 - 1) :=
    Vector.mapFinRange (2 * 3 - 1) fun k =>
      if h : k.val < numLimbs then a[k.val]'h + q * pConst[k.val]'h else 0
  EqViaCarriesN.circuit eqNParams3Add { lhs := lhs, rhs := rhs }

  return r

instance elaborated : ElaboratedCircuit (F circomPrime) Inputs Emu main := by
  elaborate_circuit


def Assumptions (input : Inputs (F circomPrime)) : Prop :=
  Fe.Valid input.a ∧ Fe.Valid input.b ∧ Fe.Valid input.c


def Spec (input : Inputs (F circomPrime)) (out : Emu (F circomPrime)) : Prop :=
  Fe.Valid out ∧ decodeFe out = decodeFe input.a - decodeFe input.b - decodeFe input.c

theorem soundness : Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [ValidP.circuit, ValidP.main, ValidP.Assumptions, ValidP.Spec,
    EqViaCarriesN.circuit, EqViaCarriesN.elaborated, EqViaCarriesN.main,
    EqViaCarriesN.Assumptions, EqViaCarriesN.Spec]
  obtain ⟨h_row1, h_row2, hr_valid, h_eq_impl⟩ := h_holds
  have hq2 : (env.get (i₀ + numLimbs)).val ≤ 2 := q_val_le_two h_row1 h_row2
  apply SubMod.soundness_core3N i₀ env input_var_a input_var_b input_var_c
    input_a input_b input_c
    h_input.1 h_input.2.1 h_input.2.2 h_assumptions.1 h_assumptions.2.1 h_assumptions.2.2
    hq2 hr_valid.1
  · intro _
    rw [pConst_value env]
    exact hr_valid.2
  · exact h_eq_impl

theorem completeness : Completeness (F circomPrime) main Assumptions := by
  circuit_proof_start [ValidP.circuit, ValidP.main, ValidP.Assumptions, ValidP.Spec,
    EqViaCarriesN.circuit, EqViaCarriesN.elaborated, EqViaCarriesN.main,
    EqViaCarriesN.Assumptions, EqViaCarriesN.Spec]
  have heva : evalEmu env input_var_a = BigInt.value limbBits input_a := by
    rw [evalEmu, BigInt.value, ← h_input.1]
  have hevb : evalEmu env input_var_b = BigInt.value limbBits input_b := by
    rw [evalEmu, BigInt.value, ← h_input.2.1]
  have hevc : evalEmu env input_var_c = BigInt.value limbBits input_c := by
    rw [evalEmu, BigInt.value, ← h_input.2.2]
  rw [heva, hevb, hevc] at h_env
  obtain ⟨h_wit_r, h_wit_q, h_wit_t⟩ := h_env
  have hcore := SubMod.completeness_core3N i₀ env.toEnvironment
    input_var_a input_var_b input_var_c input_a input_b input_c
    h_input.1 h_input.2.1 h_input.2.2 h_assumptions.1 h_assumptions.2.1 h_assumptions.2.2
    h_wit_r h_wit_q
  obtain ⟨hq2, hrv_norm, hlt_pair, hbounds, hpoly⟩ := hcore
  refine ⟨?_, ?_, ⟨hrv_norm, ?_⟩, hbounds, hpoly⟩
  · rw [h_wit_q, h_wit_t]
    ring
  · rw [h_wit_q, h_wit_t]
    linear_combination q_row2_of_wit hq2
  · rw [← pConst_value env.toEnvironment]
    exact hlt_pair.2


def circuit : FormalCircuit (F circomPrime) Inputs Emu where
  main; elaborated; Assumptions; Spec; soundness; completeness

end SubMod3
end Solution.Secp256k1ScalarMul



namespace Solution.Secp256k1ScalarMul
namespace SubMod
open AddMod

theorem computableWitnesses : circuit.base.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main
  let rCircuit : Circuit (F circomPrime) (Var Emu (F circomPrime)) :=
    ProvableType.witness (α := Emu) fun env =>
      emuOfNat ((evalEmu env input.a + P256 - evalEmu env input.b) % P256)
  let r := rCircuit.output offset
  let qOffset := offset + rCircuit.localLength offset
  let qCircuit : Circuit (F circomPrime) (Var field (F circomPrime)) :=
    ProvableType.witness (α := field) fun env =>
      (((if evalEmu env input.a < evalEmu env input.b then 1 else 0 : ℕ)) : F circomPrime)
  let q := qCircuit.output qOffset
  let boolOffset := qOffset + qCircuit.localLength qOffset
  let validCircuit : Circuit (F circomPrime) Unit := ValidP.circuit r
  let validOffset := boolOffset + (assertZero (q * (q - 1))).localLength boolOffset
  let lhs : Vector (Expression (F circomPrime)) (2 * 3 - 1) :=
    Vector.mapFinRange (2 * 3 - 1) fun k =>
      if h : k.val < numLimbs then r[k.val]'h + input.b[k.val]'h else 0
  let rhs : Vector (Expression (F circomPrime)) (2 * 3 - 1) :=
    Vector.mapFinRange (2 * 3 - 1) fun k =>
      if h : k.val < numLimbs then input.a[k.val]'h + q * pConst[k.val]'h else 0
  have h_r_len : rCircuit.localLength offset = numLimbs := by
    simp [rCircuit, circuit_norm]
  have h_q_len : qCircuit.localLength qOffset = 1 := by
    simp [qCircuit, circuit_norm]
  have h_bool_len : (assertZero (q * (q - 1))).localLength boolOffset = 0 := by
    simp [circuit_norm]
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.provableWitness_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.assertZero_structuralComputableWitnesses_iff]
  and_intros
  · intro _ h_input
    have ha : evalEmu env input.a = evalEmu env' input.a := by
      apply evalEmu_eq_of_eval_eq
      simpa [circuit_norm] using congrArg (fun x : Inputs (F circomPrime) => x.a) h_input
    have hb : evalEmu env input.b = evalEmu env' input.b := by
      apply evalEmu_eq_of_eval_eq
      simpa [circuit_norm] using congrArg (fun x : Inputs (F circomPrime) => x.b) h_input
    simp [ha, hb]
  · intro _ h_input
    have ha : evalEmu env input.a = evalEmu env' input.a := by
      apply evalEmu_eq_of_eval_eq
      simpa [circuit_norm] using congrArg (fun x : Inputs (F circomPrime) => x.a) h_input
    have hb : evalEmu env input.b = evalEmu env' input.b := by
      apply evalEmu_eq_of_eval_eq
      simpa [circuit_norm] using congrArg (fun x : Inputs (F circomPrime) => x.b) h_input
    simp [ha, hb]
  · trivial
  · exact Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.subcircuit_flatStructuralComputableWitnesses_of_condition
      ValidP.circuit input r validOffset
      (by
        intro k env env' hle h_agree _h_input
        have hk : offset + numLimbs ≤ k := by
          have hle' := hle
          dsimp [validOffset, boolOffset, qOffset] at hle'
          rw [h_r_len] at hle'
          omega
        have hr := emuWitnessOutput_stable
          (offset := offset) (k := k)
          (fun env => emuOfNat ((evalEmu env input.a + P256 - evalEmu env input.b) % P256))
          h_agree hk
        simpa [r, rCircuit] using hr)
      ValidP.computableWitnesses env env'
  · trivial
  · exact Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.subcircuit_flatStructuralComputableWitnesses_of_condition
      (EqViaCarriesN.circuit eqNParamsAdd) input { lhs := lhs, rhs := rhs }
      (validOffset + validCircuit.localLength validOffset)
      (by
        intro k env env' hle h_agree h_input
        simp [circuit_norm]
        have h_input_parts :
            (∀ a ∈ input.a, Expression.eval env.toEnvironment a =
                Expression.eval env'.toEnvironment a) ∧
              ∀ a ∈ input.b, Expression.eval env.toEnvironment a =
                Expression.eval env'.toEnvironment a := by
          simpa [circuit_norm, CircuitType.eval_expression_prover_to_verifier,
            CircuitType.eval_expression, ProvableType.eval, explicit_provable_type] using h_input
        have hr_cell : ∀ (i : ℕ) (hi : i < numLimbs),
            Expression.eval env.toEnvironment (r[i]'hi) =
              Expression.eval env'.toEnvironment (r[i]'hi) := by
          intro i hi
          have hr_vec := emuWitnessOutput_stable
            (offset := offset) (k := k)
            (fun env => emuOfNat ((evalEmu env input.a + P256 - evalEmu env input.b) % P256))
            h_agree (by
              have hbase : offset + numLimbs ≤ validOffset := by
                dsimp [validOffset, boolOffset, qOffset]
                rw [h_r_len]
                omega
              have hvalid_le_k : validOffset ≤ k := by
                have hle' := hle
                omega
              omega)
          have hr_i : (eval env r)[i] = (eval env' r)[i] := by
            exact congrArg (fun x : Emu (F circomPrime) => x[i]) (by
              simpa [r, rCircuit] using hr_vec)
          rw [← ProvableType.getElem_eval_fields_prover (env := env) r i hi,
            ← ProvableType.getElem_eval_fields_prover (env := env') r i hi] at hr_i
          exact hr_i
        constructor
        · have hlhs :
            lhs.map (Expression.eval env.toEnvironment) =
              lhs.map (Expression.eval env'.toEnvironment) := by
            apply Vector.ext
            intro i hi
            simp only [Vector.getElem_map]
            simp only [lhs, Vector.getElem_mapFinRange]
            split
            · rename_i hlt
              have hb : Expression.eval env.toEnvironment input.b[i] =
                  Expression.eval env'.toEnvironment input.b[i] :=
                h_input_parts.2 input.b[i] (by
                  simp only [Vector.mem_iff_getElem]
                  exact ⟨i, by assumption, rfl⟩)
              simp [Expression.eval, hr_cell i hlt, hb]
            · rfl
          simpa [CircuitType.eval_expression_prover_to_verifier,
            CircuitType.eval_expression, ProvableType.eval, explicit_provable_type] using
              eval_mem_of_map_eval_eq hlhs
        · have hrhs :
            rhs.map (Expression.eval env.toEnvironment) =
              rhs.map (Expression.eval env'.toEnvironment) := by
            apply Vector.ext
            intro i hi
            simp only [Vector.getElem_map]
            simp only [rhs, Vector.getElem_mapFinRange]
            split
            · rename_i hlt
              have hq : Expression.eval env.toEnvironment q =
                  Expression.eval env'.toEnvironment q := by
                exact fieldWitnessOutput_stable
                  (offset := qOffset) (k := k)
                  (fun env =>
                    (((if evalEmu env input.a < evalEmu env input.b then 1 else 0 : ℕ))
                      : F circomPrime))
                  h_agree (by
                    have hbase : qOffset + 1 ≤ validOffset := by
                      dsimp [validOffset, boolOffset]
                      rw [h_q_len]
                      omega
                    have hvalid_le_k : validOffset ≤ k := by
                      have hle' := hle
                      omega
                    omega)
              have hp : Expression.eval env.toEnvironment pConst[i] =
                  Expression.eval env'.toEnvironment pConst[i] := by
                rw [pConst, emuConst]
                rw [Vector.getElem_ofFn hlt]
                simp [Expression.eval]
              have ha : Expression.eval env.toEnvironment input.a[i] =
                  Expression.eval env'.toEnvironment input.a[i] :=
                h_input_parts.1 input.a[i] (by
                  simp only [Vector.mem_iff_getElem]
                  exact ⟨i, by assumption, rfl⟩)
              simp [Expression.eval, hq, hp, ha]
            · rfl
          simpa [CircuitType.eval_expression_prover_to_verifier,
            CircuitType.eval_expression, ProvableType.eval, explicit_provable_type] using
              eval_mem_of_map_eval_eq hrhs)
      (EqViaCarriesN.computableWitnesses eqNParamsAdd) env env'
  · trivial
  · trivial

theorem computableWitness : ∀ n input,
    ProverEnvironment.OnlyAccessedBelow n
      (fun env : ProverEnvironment (F circomPrime) => eval env input) →
    Circuit.ComputableWitnesses (main input) n := by
  exact Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnesses_implies
    (circuit := circuit.base) computableWitnesses


lemma eval_output_of_agreesBelow (input : Var Inputs (F circomPrime)) {offset k : ℕ}
    {env env' : ProverEnvironment (F circomPrime)}
    (h_agree : env.AgreesBelow k env') (hk : offset + numLimbs ≤ k) :
    eval env ((main input).output offset) = eval env' ((main input).output offset) := by
  have hout : (main input).output offset
      = (ProvableType.witness (α := Emu) fun env =>
          emuOfNat ((evalEmu env input.a + P256 - evalEmu env input.b) % P256)).output offset := rfl
  rw [hout]
  exact emuWitnessOutput_stable _ h_agree hk

end SubMod
end Solution.Secp256k1ScalarMul

namespace Solution.Secp256k1ScalarMul
namespace SubMod3
open AddMod

theorem computableWitnesses : circuit.base.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main
  let rCircuit : Circuit (F circomPrime) (Var Emu (F circomPrime)) :=
    ProvableType.witness (α := Emu) fun env =>
      emuOfNat ((evalEmu env input.a + 2 * P256 - evalEmu env input.b - evalEmu env input.c) % P256)
  let r := rCircuit.output offset
  let qOffset := offset + rCircuit.localLength offset
  let qCircuit : Circuit (F circomPrime) (Var field (F circomPrime)) :=
    ProvableType.witness (α := field) fun env =>
      (((2 - (evalEmu env input.a + 2 * P256 - evalEmu env input.b - evalEmu env input.c) / P256 : ℕ))
        : F circomPrime)
  let q := qCircuit.output qOffset
  let tOffset := qOffset + qCircuit.localLength qOffset
  let tCircuit : Circuit (F circomPrime) (Var field (F circomPrime)) :=
    ProvableType.witness (α := field) fun env =>
      (((2 - (evalEmu env input.a + 2 * P256 - evalEmu env input.b - evalEmu env input.c) / P256 : ℕ))
          : F circomPrime)
        * ((((2 - (evalEmu env input.a + 2 * P256 - evalEmu env input.b - evalEmu env input.c) / P256 : ℕ))
            : F circomPrime) - 1)
  let t := tCircuit.output tOffset
  let rowOffset := tOffset + tCircuit.localLength tOffset
  let validCircuit : Circuit (F circomPrime) Unit := ValidP.circuit r
  let validOffset := rowOffset
  let lhs : Vector (Expression (F circomPrime)) (2 * 3 - 1) :=
    Vector.mapFinRange (2 * 3 - 1) fun k =>
      if h : k.val < numLimbs then r[k.val]'h + input.b[k.val]'h + input.c[k.val]'h else 0
  let rhs : Vector (Expression (F circomPrime)) (2 * 3 - 1) :=
    Vector.mapFinRange (2 * 3 - 1) fun k =>
      if h : k.val < numLimbs then input.a[k.val]'h + q * pConst[k.val]'h else 0
  have h_r_len : rCircuit.localLength offset = numLimbs := by
    simp [rCircuit, circuit_norm]
  have h_q_len : qCircuit.localLength qOffset = 1 := by
    simp [qCircuit, circuit_norm]
  have h_t_len : tCircuit.localLength tOffset = 1 := by
    simp [tCircuit, circuit_norm]
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.provableWitness_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.assertZero_structuralComputableWitnesses_iff]
  have hparent : ∀ (e e' : ProverEnvironment (F circomPrime)),
      eval e input = eval e' input →
      evalEmu e input.a = evalEmu e' input.a ∧
      evalEmu e input.b = evalEmu e' input.b ∧
      evalEmu e input.c = evalEmu e' input.c := by
    intro e e' h_input
    exact ⟨evalEmu_eq_of_eval_eq (by
        simpa [circuit_norm] using congrArg (fun x : Inputs (F circomPrime) => x.a) h_input),
      evalEmu_eq_of_eval_eq (by
        simpa [circuit_norm] using congrArg (fun x : Inputs (F circomPrime) => x.b) h_input),
      evalEmu_eq_of_eval_eq (by
        simpa [circuit_norm] using congrArg (fun x : Inputs (F circomPrime) => x.c) h_input)⟩
  and_intros
  · intro _ h_input
    obtain ⟨ha, hb, hc⟩ := hparent env env' h_input
    simp [ha, hb, hc]
  · intro _ h_input
    obtain ⟨ha, hb, hc⟩ := hparent env env' h_input
    simp [ha, hb, hc]
  · intro _ h_input
    obtain ⟨ha, hb, hc⟩ := hparent env env' h_input
    simp [ha, hb, hc]
  · trivial
  · trivial
  · exact Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.subcircuit_flatStructuralComputableWitnesses_of_condition
      ValidP.circuit input r validOffset
      (by
        intro k env env' hle h_agree _h_input
        have hk : offset + numLimbs ≤ k := by
          have hle' := hle
          dsimp [validOffset, rowOffset, tOffset, qOffset] at hle'
          rw [h_r_len] at hle'
          omega
        have hr := emuWitnessOutput_stable
          (offset := offset) (k := k)
          (fun env =>
            emuOfNat ((evalEmu env input.a + 2 * P256 - evalEmu env input.b - evalEmu env input.c)
              % P256))
          h_agree hk
        simpa [r, rCircuit] using hr)
      ValidP.computableWitnesses env env'
  · trivial
  · exact Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.subcircuit_flatStructuralComputableWitnesses_of_condition
      (EqViaCarriesN.circuit eqNParams3Add) input { lhs := lhs, rhs := rhs }
      (validOffset + validCircuit.localLength validOffset)
      (by
        intro k env env' hle h_agree h_input
        simp [circuit_norm]
        have h_input_parts :
            (∀ a ∈ input.a, Expression.eval env.toEnvironment a =
                Expression.eval env'.toEnvironment a) ∧
              (∀ a ∈ input.b, Expression.eval env.toEnvironment a =
                Expression.eval env'.toEnvironment a) ∧
              ∀ a ∈ input.c, Expression.eval env.toEnvironment a =
                Expression.eval env'.toEnvironment a := by
          simpa [circuit_norm, CircuitType.eval_expression_prover_to_verifier,
            CircuitType.eval_expression, ProvableType.eval, explicit_provable_type] using h_input
        have hr_cell : ∀ (i : ℕ) (hi : i < numLimbs),
            Expression.eval env.toEnvironment (r[i]'hi) =
              Expression.eval env'.toEnvironment (r[i]'hi) := by
          intro i hi
          have hr_vec := emuWitnessOutput_stable
            (offset := offset) (k := k)
            (fun env =>
              emuOfNat ((evalEmu env input.a + 2 * P256 - evalEmu env input.b - evalEmu env input.c)
                % P256))
            h_agree (by
              have hbase : offset + numLimbs ≤ validOffset := by
                dsimp [validOffset, rowOffset, tOffset, qOffset]
                rw [h_r_len]
                omega
              have hvalid_le_k : validOffset ≤ k := by
                have hle' := hle
                omega
              omega)
          have hr_i : (eval env r)[i] = (eval env' r)[i] := by
            exact congrArg (fun x : Emu (F circomPrime) => x[i]) (by
              simpa [r, rCircuit] using hr_vec)
          rw [← ProvableType.getElem_eval_fields_prover (env := env) r i hi,
            ← ProvableType.getElem_eval_fields_prover (env := env') r i hi] at hr_i
          exact hr_i
        constructor
        · have hlhs :
            lhs.map (Expression.eval env.toEnvironment) =
              lhs.map (Expression.eval env'.toEnvironment) := by
            apply Vector.ext
            intro i hi
            simp only [Vector.getElem_map]
            simp only [lhs, Vector.getElem_mapFinRange]
            split
            · rename_i hlt
              have hb : Expression.eval env.toEnvironment input.b[i] =
                  Expression.eval env'.toEnvironment input.b[i] :=
                h_input_parts.2.1 input.b[i] (by
                  simp only [Vector.mem_iff_getElem]
                  exact ⟨i, by assumption, rfl⟩)
              have hc : Expression.eval env.toEnvironment input.c[i] =
                  Expression.eval env'.toEnvironment input.c[i] :=
                h_input_parts.2.2 input.c[i] (by
                  simp only [Vector.mem_iff_getElem]
                  exact ⟨i, by assumption, rfl⟩)
              simp [Expression.eval, hr_cell i hlt, hb, hc]
            · rfl
          simpa [CircuitType.eval_expression_prover_to_verifier,
            CircuitType.eval_expression, ProvableType.eval, explicit_provable_type] using
              eval_mem_of_map_eval_eq hlhs
        · have hrhs :
            rhs.map (Expression.eval env.toEnvironment) =
              rhs.map (Expression.eval env'.toEnvironment) := by
            apply Vector.ext
            intro i hi
            simp only [Vector.getElem_map]
            simp only [rhs, Vector.getElem_mapFinRange]
            split
            · rename_i hlt
              have hq : Expression.eval env.toEnvironment q =
                  Expression.eval env'.toEnvironment q := by
                exact fieldWitnessOutput_stable
                  (offset := qOffset) (k := k)
                  (fun env =>
                    (((2 - (evalEmu env input.a + 2 * P256 - evalEmu env input.b
                        - evalEmu env input.c) / P256 : ℕ)) : F circomPrime))
                  h_agree (by
                    have hbase : qOffset + 1 ≤ validOffset := by
                      dsimp [validOffset, rowOffset, tOffset]
                      rw [h_q_len]
                      omega
                    have hvalid_le_k : validOffset ≤ k := by
                      have hle' := hle
                      omega
                    omega)
              have hp : Expression.eval env.toEnvironment pConst[i] =
                  Expression.eval env'.toEnvironment pConst[i] := by
                rw [pConst, emuConst]
                rw [Vector.getElem_ofFn hlt]
                simp [Expression.eval]
              have ha : Expression.eval env.toEnvironment input.a[i] =
                  Expression.eval env'.toEnvironment input.a[i] :=
                h_input_parts.1 input.a[i] (by
                  simp only [Vector.mem_iff_getElem]
                  exact ⟨i, by assumption, rfl⟩)
              simp [Expression.eval, hq, hp, ha]
            · rfl
          simpa [CircuitType.eval_expression_prover_to_verifier,
            CircuitType.eval_expression, ProvableType.eval, explicit_provable_type] using
              eval_mem_of_map_eval_eq hrhs)
      (EqViaCarriesN.computableWitnesses eqNParams3Add) env env'
  · trivial
  · trivial


lemma eval_output_of_agreesBelow (input : Var Inputs (F circomPrime)) {offset k : ℕ}
    {env env' : ProverEnvironment (F circomPrime)}
    (h_agree : env.AgreesBelow k env') (hk : offset + numLimbs ≤ k) :
    eval env ((main input).output offset) = eval env' ((main input).output offset) := by
  have hout : (main input).output offset
      = (ProvableType.witness (α := Emu) fun env =>
          emuOfNat ((evalEmu env input.a + 2 * P256 - evalEmu env input.b - evalEmu env input.c)
            % P256)).output offset := rfl
  rw [hout]
  exact emuWitnessOutput_stable _ h_agree hk

end SubMod3
end Solution.Secp256k1ScalarMul
