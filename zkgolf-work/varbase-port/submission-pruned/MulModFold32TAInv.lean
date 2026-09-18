import Solution.Secp256k1ScalarMul.MulModFold32TA
import Solution.Secp256k1ScalarMul.MulModFold32TInv

/-!
# Quotient-inverted `MulModFold32TA`

`MulModFold32TA` is `MulModFold32T` with a compile-time constant second operand,
so its `2m−1` convolution cells are affine forms in `a`'s limbs and are never
witnessed.  Consequently the very same quotient inversion that `MulModFold32T`
uses applies verbatim: the folded quotient is determined over the native field
by an affine expression in the operand and target wires, so it need not be
witnessed, and the native row of the grouped equality is then true by
construction and is dropped.

`⟨78, 80⟩` becomes `⟨77, 79⟩`.  Every arithmetic ingredient is shared with
`MulModFold32T` / `MulModFold32TInv`: the inversion lemmas there are stated for
an *arbitrary* coefficient vector `Pc`, and here it is instantiated with the
constant-operand convolution `bigIntMulNoReduce a b`.
-/

set_option exponentiation.threshold 600

namespace Solution.Secp256k1ScalarMul
namespace MulModFold32TA

open MulMod
open Solution.Secp256k1ScalarMul.Limbs
open MulModFold32T

/-- The (unwitnessed) convolution cells of a constant-operand product. -/
def pcOf (input : Var Inputs (F circomPrime)) : Vector (Expression (F circomPrime)) 15 :=
  bigIntMulNoReduce input.a input.b

def mainInv (input : Var Inputs (F circomPrime)) : Circuit (F circomPrime) Unit := do
  assertion (RangeCheck.circuit qBitsFold32T (by decide) (by decide))
    (qInv (pcOf input) input.target)
  assertion
    (GroupedEqXV.circuitNoTop 32 gfFold32T posOfFold32T 3 vFold32TL vFold32TR
      hgvFold32T (by norm_num))
    { lhs := foldLhs32 (pcOf input),
      rhs := foldRhs32 (qInv (pcOf input) input.target) input.target }

instance elaboratedInv : ElaboratedCircuit (F circomPrime) Inputs unit mainInv where
  -- range check (35) + one carry (42)
  localLength _ := 77
  localLength_eq := by
    intro input offset
    simp only [mainInv, circuit_norm, RangeCheck.circuit,
      GroupedEqXV.circuitNoTop, GroupedEqXV.elaboratedNoTop, vFold32TL, wfFold32T,
      GroupedEqXV.widthAllocFrom, qBitsFold32T]
  subcircuitsConsistent := by
    intro input offset
    simp +arith only [mainInv, circuit_norm, RangeCheck.circuit,
      GroupedEqXV.circuitNoTop, GroupedEqXV.elaboratedNoTop]
  channelsLawful := by
    intro offset
    simp only [mainInv, circuit_norm, RangeCheck.circuit,
      GroupedEqXV.circuitNoTop, GroupedEqXV.elaboratedNoTop]

attribute [local irreducible] RangeCheck.circuit GroupedEqXV.circuitNoTop GroupedEqXV.mainNoTop qInv lhsPolyInv targetPolyInv

set_option maxHeartbeats 8000000 in
theorem soundnessInv (Ca Cb : ℕ) (hcap : 8 * (Ca * Cb) ≤ 2 ^ 67) :
    FormalAssertion.Soundness (F circomPrime) mainInv (Assumptions Ca Cb) Spec := by
  circuit_proof_start [mainInv, pcOf,
    RangeCheck.circuit, RangeCheck.Assumptions, RangeCheck.Spec,
    GroupedEqXV.circuitNoTop, GroupedEqXV.elaboratedNoTop,
    GroupedEqXV.AssumptionsNoTop, GroupedEqXV.Assumptions, GroupedEqX.Spec,
    MulModFold32T.Assumptions, MulModFold32T.Spec]
  obtain ⟨hq_lt, h_eq_impl⟩ := h_holds
  obtain ⟨ha_lt, hb_lt, ht_lt, ht_val⟩ := h_assumptions
  obtain ⟨ha_in, hb_in, ht_in⟩ := h_input
  simp only [vFold32TL, vFold32TR, nfFold32TR] at h_eq_impl
  have ha_lt' : ∀ i : Fin 8,
      (Expression.eval env (input_var_a[i.val]'i.isLt)).val < Ca := by
    intro i
    rw [show Expression.eval env (input_var_a[i.val]'i.isLt) = input_a[i.val] from by
      rw [← ha_in]; simp only [Vector.getElem_map]]
    exact ha_lt i
  have hb_lt' : ∀ i : Fin 8,
      (Expression.eval env (input_var_b[i.val]'i.isLt)).val < Cb := by
    intro i
    rw [show Expression.eval env (input_var_b[i.val]'i.isLt) = input_b[i.val] from by
      rw [← hb_in]; simp only [Vector.getElem_map]]
    exact hb_lt i
  have ht_lt' : ∀ i : Fin numLimbs,
      (Expression.eval env (input_var_target[i.val]'i.isLt)).val < 3 * 2 ^ 64 := by
    intro i
    rw [show Expression.eval env (input_var_target[i.val]'i.isLt) = input_target[i.val] from by
      rw [← ht_in]; simp only [Vector.getElem_map]]
    exact ht_lt i
  have hNbp : 8 * (Ca * Cb) < circomPrime := by
    have h2 : (2 : ℕ) ^ 69 < circomPrime := by decide
    omega
  have hcap64 : Ca * Cb ≤ 2 ^ 64 := by omega
  have hPv : ∀ k : Fin 15,
      (Expression.eval env ((bigIntMulNoReduce input_var_a input_var_b)[k.val])).val
        < triNf k.val := by
    intro k
    rw [coeff_eq_convNat env input_var_a input_var_b ha_lt' hb_lt' hNbp k]
    exact convNat_lt_tri env input_var_a input_var_b ha_lt' hb_lt' hcap64 k
  have hqv : (Expression.eval env
      (qInv (bigIntMulNoReduce input_var_a input_var_b) input_var_target)).val < 2 ^ 37 := by
    have h36 : (Expression.eval env
        (qInv (bigIntMulNoReduce input_var_a input_var_b) input_var_target)).val < 2 ^ 36 :=
      hq_lt
    have : (2 : ℕ) ^ 36 ≤ 2 ^ 37 := by norm_num
    omega
  have heq := h_eq_impl
    ⟨⟨foldLhs32_bound env _ hPv,
      foldRhs32_bound env _ input_var_target hqv ht_lt'⟩,
     qInv_linIdent env (bigIntMulNoReduce input_var_a input_var_b) input_var_target⟩
  rw [foldLhs32_polyValue env _ hPv,
    foldRhs32_polyValue env _ input_var_target hqv ht_lt',
    foldDNatOf_eq env input_var_a input_var_b ha_lt' hb_lt' hNbp _ (fun _ => rfl), ht_in] at heq
  have hid := foldDNat_identity env input_var_a input_var_b ha_lt' hb_lt' hNbp
  rw [ha_in, hb_in] at hid
  exact target_congr hid heq

set_option maxHeartbeats 8000000 in
theorem completenessInv (Ca Cb : ℕ) (hcap : 8 * (Ca * Cb) ≤ 2 ^ 67) :
    FormalAssertion.Completeness (F circomPrime) mainInv (Assumptions Ca Cb) Spec := by
  circuit_proof_start [mainInv, pcOf,
    RangeCheck.circuit, RangeCheck.Assumptions, RangeCheck.Spec,
    GroupedEqXV.circuitNoTop, GroupedEqXV.elaboratedNoTop,
    GroupedEqXV.AssumptionsNoTop, GroupedEqXV.Assumptions, GroupedEqX.Spec,
    MulModFold32T.Assumptions, MulModFold32T.Spec]
  obtain ⟨ha_lt, hb_lt, ht_lt, ht_val⟩ := h_assumptions
  obtain ⟨ha_in, hb_in, ht_in⟩ := h_input
  simp only [vFold32TL, vFold32TR, nfFold32TR]
  have ha_lt' : ∀ i : Fin 8,
      (Expression.eval env.toEnvironment (input_var_a[i.val]'i.isLt)).val < Ca := by
    intro i
    rw [show Expression.eval env.toEnvironment (input_var_a[i.val]'i.isLt) = input_a[i.val] from by
      rw [← ha_in]; simp only [Vector.getElem_map]]
    exact ha_lt i
  have hb_lt' : ∀ i : Fin 8,
      (Expression.eval env.toEnvironment (input_var_b[i.val]'i.isLt)).val < Cb := by
    intro i
    rw [show Expression.eval env.toEnvironment (input_var_b[i.val]'i.isLt) = input_b[i.val] from by
      rw [← hb_in]; simp only [Vector.getElem_map]]
    exact hb_lt i
  have ht_lt' : ∀ i : Fin numLimbs,
      (Expression.eval env.toEnvironment (input_var_target[i.val]'i.isLt)).val < 3 * 2 ^ 64 := by
    intro i
    rw [show Expression.eval env.toEnvironment (input_var_target[i.val]'i.isLt)
        = input_target[i.val] from by rw [← ht_in]; simp only [Vector.getElem_map]]
    exact ht_lt i
  have hNbp : 8 * (Ca * Cb) < circomPrime := by
    have h2 : (2 : ℕ) ^ 69 < circomPrime := by decide
    omega
  have hcap64 : Ca * Cb ≤ 2 ^ 64 := by omega
  have hPv : ∀ k : Fin 15,
      (Expression.eval env.toEnvironment
        ((bigIntMulNoReduce input_var_a input_var_b)[k.val])).val < triNf k.val := by
    intro k
    rw [coeff_eq_convNat env.toEnvironment input_var_a input_var_b ha_lt' hb_lt' hNbp k]
    exact convNat_lt_tri env.toEnvironment input_var_a input_var_b ha_lt' hb_lt' hcap64 k
  set D := foldDNat env.toEnvironment input_var_a input_var_b with hDdef
  set T := BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) input_var_target)
    with hTdef
  have hT3 : T < 3 * P256 := by rw [hTdef, ht_in]; exact ht_val
  have hDge : 3 * P256 ≤ D := foldDNat_ge env.toEnvironment input_var_a input_var_b
  have hDlt : D < 9 * 2 ^ 288 + 2 ^ 266 := foldDNat_lt env.toEnvironment input_var_a input_var_b
    ha_lt' hb_lt' hcap
  have hid := foldDNat_identity env.toEnvironment input_var_a input_var_b ha_lt' hb_lt' hNbp
  rw [ha_in, hb_in] at hid
  have hDmod : D % P256 = T % P256 := by
    rw [foldD_mod hid, hTdef, ht_in]
    exact h_spec.symm
  set q0 := (D - T) / P256 with hq0def
  have hqlt : q0 < 2 ^ 36 := by
    have hdiv : (D - T) / P256 ≤ D / P256 := Nat.div_le_div_right (by omega)
    have hD2 : D / P256 < 2 ^ 36 := by
      apply Nat.div_lt_of_lt_mul
      have hle : 9 * (2 : ℕ) ^ 288 + 2 ^ 266 ≤ 2 ^ 36 * P256 := by decide
      omega
    exact lt_of_le_of_lt hdiv hD2
  have hreconstruct : q0 * P256 + T = D := quot_reconstruct (by omega) hDmod
  have hqIdentity :
      polyValue 32 (Vector.map (Expression.eval env.toEnvironment)
        (foldLhs32 (bigIntMulNoReduce input_var_a input_var_b)))
        = q0 * P256 + BigInt.value 64
          (Vector.map (Expression.eval env.toEnvironment) input_var_target) := by
    rw [foldLhs32_polyValue env.toEnvironment _ hPv,
      foldDNatOf_eq env.toEnvironment input_var_a input_var_b ha_lt' hb_lt' hNbp _
        (fun _ => rfl), ← hTdef]
    exact hreconstruct.symm
  have hqeval := eval_qInv_of_identity env.toEnvironment
    (bigIntMulNoReduce input_var_a input_var_b) input_var_target q0 hqIdentity
  have hqval : (Expression.eval env.toEnvironment
      (qInv (bigIntMulNoReduce input_var_a input_var_b) input_var_target)).val = q0 := by
    rw [hqeval, ZMod.val_natCast_of_lt]
    have hp : (2 : ℕ) ^ 36 < circomPrime := by decide
    omega
  have hqvar : (Expression.eval env.toEnvironment
      (qInv (bigIntMulNoReduce input_var_a input_var_b) input_var_target)).val < 2 ^ 37 := by
    rw [hqval]
    have : (2 : ℕ) ^ 36 ≤ 2 ^ 37 := by norm_num
    omega
  refine ⟨?_, ?_, ?_⟩
  · rw [hqval]; exact hqlt
  · exact ⟨⟨foldLhs32_bound env.toEnvironment _ hPv,
      foldRhs32_bound env.toEnvironment _ input_var_target hqvar ht_lt'⟩,
      qInv_linIdent env.toEnvironment
        (bigIntMulNoReduce input_var_a input_var_b) input_var_target⟩
  · rw [foldLhs32_polyValue env.toEnvironment _ hPv,
      foldRhs32_polyValue env.toEnvironment _ input_var_target hqvar ht_lt',
      foldDNatOf_eq env.toEnvironment input_var_a input_var_b ha_lt' hb_lt' hNbp _
        (fun _ => rfl)]
    show D = (Expression.eval env.toEnvironment
      (qInv (bigIntMulNoReduce input_var_a input_var_b) input_var_target)).val * P256 + T
    rw [hqval]
    exact hreconstruct.symm

def circuitInv (Ca Cb : ℕ) (hcap : 8 * (Ca * Cb) ≤ 2 ^ 67) :
    FormalAssertion (F circomPrime) Inputs where
  main := mainInv
  Assumptions := Assumptions Ca Cb
  Spec := Spec
  soundness := soundnessInv Ca Cb hcap
  completeness := completenessInv Ca Cb hcap

set_option maxHeartbeats 4000000 in
theorem computableWitnessesInv (Ca Cb : ℕ) (hcap : 8 * (Ca * Cb) ≤ 2 ^ 67) :
    (circuitInv Ca Cb hcap).ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition
      input env env') ((mainInv input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold mainInv
  let pcv := pcOf input
  let qv := qInv pcv input.target
  let rcc : Circuit (F circomPrime) Unit :=
    assertion (RangeCheck.circuit qBitsFold32T (by decide) (by decide)) qv
  let eqOff := offset + rcc.localLength offset
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.pure_structuralComputableWitnesses_iff,
    and_true]
  and_intros
  · exact Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
      (RangeCheck.circuit qBitsFold32T (by decide) (by decide)) input qv offset
      (by
        intro k e1 e2 _ _ h_input
        have ha : eval e1 input.a = eval e2 input.a := by
          simpa [circuit_norm] using congrArg (fun x : Inputs (F circomPrime) => x.a) h_input
        have hb : eval e1 input.b = eval e2 input.b := by
          simpa [circuit_norm] using congrArg (fun x : Inputs (F circomPrime) => x.b) h_input
        have ht : eval e1 input.target = eval e2 input.target := by
          simpa [circuit_norm] using congrArg (fun x : Inputs (F circomPrime) => x.target) h_input
        have ha_i : ∀ (i : ℕ) (hi : i < 8),
            Expression.eval e1.toEnvironment (input.a[i]'hi)
              = Expression.eval e2.toEnvironment (input.a[i]'hi) :=
          fun i hi => bigInt_getElem_eval_eq ha i hi
        have hb_i : ∀ (i : ℕ) (hi : i < 8),
            Expression.eval e1.toEnvironment (input.b[i]'hi)
              = Expression.eval e2.toEnvironment (input.b[i]'hi) :=
          fun i hi => bigInt_getElem_eval_eq hb i hi
        have hPc_i : ∀ (i : ℕ) (hi : i < 15),
            Expression.eval e1.toEnvironment (pcv[i]'hi)
              = Expression.eval e2.toEnvironment (pcv[i]'hi) := by
          intro i hi
          exact bigIntMulNoReduce_coeff_stable e1.toEnvironment e2.toEnvironment
            input.a input.b ha_i hb_i ⟨i, hi⟩
        have ht_i : ∀ (i : ℕ) (hi : i < numLimbs),
            Expression.eval e1.toEnvironment (input.target[i]'hi)
              = Expression.eval e2.toEnvironment (input.target[i]'hi) :=
          fun i hi => bigInt_getElem_eval_eq ht i hi
        simpa only [qv, circuit_norm] using qInv_stable pcv input.target hPc_i ht_i)
      (RangeCheck.computableWitnesses qBitsFold32T (by decide) (by decide)) env env'
  · exact Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
      (GroupedEqXV.circuitNoTop 32 gfFold32T posOfFold32T 3 vFold32TL vFold32TR
        hgvFold32T (by norm_num))
      input { lhs := foldLhs32 pcv, rhs := foldRhs32 qv input.target } eqOff
      (by
        intro k e1 e2 _ _ h_input
        have ha : eval e1 input.a = eval e2 input.a := by
          simpa [circuit_norm] using congrArg (fun x : Inputs (F circomPrime) => x.a) h_input
        have hb : eval e1 input.b = eval e2 input.b := by
          simpa [circuit_norm] using congrArg (fun x : Inputs (F circomPrime) => x.b) h_input
        have ht : eval e1 input.target = eval e2 input.target := by
          simpa [circuit_norm] using congrArg (fun x : Inputs (F circomPrime) => x.target) h_input
        have ha_i : ∀ (i : ℕ) (hi : i < 8),
            Expression.eval e1.toEnvironment (input.a[i]'hi)
              = Expression.eval e2.toEnvironment (input.a[i]'hi) :=
          fun i hi => bigInt_getElem_eval_eq ha i hi
        have hb_i : ∀ (i : ℕ) (hi : i < 8),
            Expression.eval e1.toEnvironment (input.b[i]'hi)
              = Expression.eval e2.toEnvironment (input.b[i]'hi) :=
          fun i hi => bigInt_getElem_eval_eq hb i hi
        have hPc_i : ∀ (i : ℕ) (hi : i < 15),
            Expression.eval e1.toEnvironment (pcv[i]'hi)
              = Expression.eval e2.toEnvironment (pcv[i]'hi) := by
          intro i hi
          exact bigIntMulNoReduce_coeff_stable e1.toEnvironment e2.toEnvironment
            input.a input.b ha_i hb_i ⟨i, hi⟩
        have ht_i : ∀ (i : ℕ) (hi : i < numLimbs),
            Expression.eval e1.toEnvironment (input.target[i]'hi)
              = Expression.eval e2.toEnvironment (input.target[i]'hi) :=
          fun i hi => bigInt_getElem_eval_eq ht i hi
        have hq := qInv_stable pcv input.target hPc_i ht_i
        have hL := foldLhs32_stable (E1 := e1.toEnvironment) (E2 := e2.toEnvironment)
          pcv hPc_i
        have hR := foldRhs32_stable (E1 := e1.toEnvironment) (E2 := e2.toEnvironment)
          qv input.target hq ht_i
        simp only [circuit_norm]
        rw [hL, hR])
      (GroupedEqXV.computableWitnessesNoTop 32 gfFold32T posOfFold32T 3
        vFold32TL vFold32TR hgvFold32T (by norm_num))
      env env'

end MulModFold32TA
end Solution.Secp256k1ScalarMul
