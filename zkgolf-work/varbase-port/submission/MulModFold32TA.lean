import Solution.Secp256k1ScalarMul.MulModFold32T

/-!
# Folded modular-multiplication certificate with a **constant** second operand

This is `MulModFold32T` specialised to the case where the second operand `b` is a
compile-time constant vector.  The only difference is that the `2m−1`-cell
convolution is *not witnessed*: when every `b[j]` has degree `0`, each cell of
`bigIntMulNoReduce a b` is already an affine form in `a`'s limbs, so it can be
handed to the grouped equality directly.  That deletes `interpolatedMul`'s
`⟨15, 15⟩` outright, taking the certificate from `⟨93, 95⟩` to `⟨78, 80⟩`.

Everything else — the quotient witness, its 36-bit range check, the fold, the
single grouped carry — is shared verbatim with `MulModFold32T`, and so are all
the arithmetic lemmas.
-/

set_option exponentiation.threshold 600

namespace Solution.Secp256k1ScalarMul
namespace MulModFold32TA

open MulMod
open Solution.Secp256k1ScalarMul.Limbs
open MulModFold32T

/-- Same inputs as `MulModFold32T`; the caller is responsible for supplying a
constant `b` (needed only for the R1CS shape, never for soundness). -/
abbrev Inputs := MulModFold32T.Inputs

def main (input : Var Inputs (F circomPrime)) : Circuit (F circomPrime) Unit := do
  let q ← witnessField fun env =>
    ((qNat env.toEnvironment input : ℕ) : F circomPrime)
  RangeCheck.circuit qBitsFold32T (by decide) (by decide) q
  GroupedEqXV.circuit 32 gfFold32T posOfFold32T 3 vFold32TL vFold32TR hgvFold32T (by norm_num)
    { lhs := foldLhs32 (bigIntMulNoReduce input.a input.b), rhs := foldRhs32 q input.target }

instance elaborated : ElaboratedCircuit (F circomPrime) Inputs unit main where
  -- q (1) + range check (35) + one carry (42)
  localLength _ := 78
  localLength_eq := by
    intro input offset
    simp only [main, circuit_norm, RangeCheck.circuit,
      GroupedEqXV.circuit, GroupedEqXV.elaborated, vFold32TL, wfFold32T,
      GroupedEqXV.widthAllocFrom, qBitsFold32T]
  subcircuitsConsistent := by
    intro input offset
    simp +arith only [main, circuit_norm, RangeCheck.circuit,
      GroupedEqXV.circuit, GroupedEqXV.elaborated]
  channelsLawful := by
    intro offset
    simp only [main, circuit_norm, RangeCheck.circuit,
      GroupedEqXV.circuit, GroupedEqXV.elaborated]

abbrev Assumptions (Ca Cb : ℕ) := MulModFold32T.Assumptions Ca Cb

abbrev Spec := MulModFold32T.Spec

theorem soundness (Ca Cb : ℕ) (hcap : 8 * (Ca * Cb) ≤ 2 ^ 67) :
    FormalAssertion.Soundness (F circomPrime) main (Assumptions Ca Cb) Spec := by
  circuit_proof_start [RangeCheck.circuit, RangeCheck.Assumptions, RangeCheck.Spec,
    GroupedEqXV.circuit, GroupedEqXV.elaborated, GroupedEqXV.Assumptions, GroupedEqX.Spec,
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
  have hqv : (Expression.eval env (var (F := F circomPrime) { index := i₀ })).val < 2 ^ 37 := by
    have h36 : (Expression.eval env (var (F := F circomPrime) { index := i₀ })).val < 2 ^ 36 :=
      hq_lt
    have : (2 : ℕ) ^ 36 ≤ 2 ^ 37 := by norm_num
    omega
  have heq := h_eq_impl
    ⟨foldLhs32_bound env _ hPv,
     foldRhs32_bound env _ input_var_target hqv ht_lt'⟩
  rw [foldLhs32_polyValue env _ hPv,
    foldRhs32_polyValue env _ input_var_target hqv ht_lt',
    foldDNatOf_eq env input_var_a input_var_b ha_lt' hb_lt' hNbp _ (fun _ => rfl), ht_in] at heq
  have hid := foldDNat_identity env input_var_a input_var_b ha_lt' hb_lt' hNbp
  rw [ha_in, hb_in] at hid
  exact target_congr hid heq

theorem completeness (Ca Cb : ℕ) (hcap : 8 * (Ca * Cb) ≤ 2 ^ 67) :
    FormalAssertion.Completeness (F circomPrime) main (Assumptions Ca Cb) Spec := by
  circuit_proof_start [RangeCheck.circuit, RangeCheck.Assumptions, RangeCheck.Spec,
    GroupedEqXV.circuit, GroupedEqXV.elaborated, GroupedEqXV.Assumptions, GroupedEqX.Spec,
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
  have hqdef : qNat env.toEnvironment
      { a := input_var_a, b := input_var_b, target := input_var_target } = (D - T) / P256 := rfl
  have hqlt : (D - T) / P256 < 2 ^ 36 := by
    have hdiv : (D - T) / P256 ≤ D / P256 := Nat.div_le_div_right (by omega)
    have hD2 : D / P256 < 2 ^ 36 := by
      apply Nat.div_lt_of_lt_mul
      have hle : 9 * (2 : ℕ) ^ 288 + 2 ^ 266 ≤ 2 ^ 36 * P256 := by decide
      omega
    omega
  have hqval : (env.get i₀).val = (D - T) / P256 := by
    rw [h_env, hqdef]
    exact ZMod.val_natCast_of_lt (by
      have : (2 : ℕ) ^ 39 < circomPrime := by decide
      omega)
  have hqvar : (Expression.eval env.toEnvironment
      (var (F := F circomPrime) { index := i₀ })).val < 2 ^ 37 := by
    show (env.get i₀).val < 2 ^ 37
    rw [hqval]
    have : (2 : ℕ) ^ 36 ≤ 2 ^ 37 := by norm_num
    omega
  refine ⟨by rw [hqval]; exact hqlt,
    ⟨foldLhs32_bound env.toEnvironment _ hPv,
     foldRhs32_bound env.toEnvironment _ input_var_target hqvar ht_lt'⟩, ?_⟩
  rw [foldLhs32_polyValue env.toEnvironment _ hPv,
    foldRhs32_polyValue env.toEnvironment _ input_var_target hqvar ht_lt',
    foldDNatOf_eq env.toEnvironment input_var_a input_var_b ha_lt' hb_lt' hNbp _ (fun _ => rfl)]
  show D = (Expression.eval env.toEnvironment
    (var (F := F circomPrime) { index := i₀ })).val * P256 + T
  show D = (env.get i₀).val * P256 + T
  rw [hqval]
  exact (quot_reconstruct (by omega) hDmod).symm

def circuit (Ca Cb : ℕ) (hcap : 8 * (Ca * Cb) ≤ 2 ^ 67) :
    FormalAssertion (F circomPrime) Inputs where
  main := main
  Assumptions := Assumptions Ca Cb
  Spec := Spec
  soundness := soundness Ca Cb hcap
  completeness := completeness Ca Cb hcap

attribute [local irreducible] RangeCheck.circuit GroupedEqXV.circuit

theorem computableWitnesses (Ca Cb : ℕ) (hcap : 8 * (Ca * Cb) ≤ 2 ^ 67) :
    (circuit Ca Cb hcap).ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition
      input env env') ((main input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main
  let qc : Circuit (F circomPrime) (Expression (F circomPrime)) :=
    Circuit.witnessField fun e => ((qNat e.toEnvironment input : ℕ) : F circomPrime)
  let qv := qc.output offset
  let rcOff := offset + qc.localLength offset
  let rcc : Circuit (F circomPrime) Unit :=
    assertion (RangeCheck.circuit qBitsFold32T (by decide) (by decide)) qv
  let eqOff := rcOff + rcc.localLength rcOff
  have h_qlen : qc.localLength offset = 1 := by
    simp [qc, circuit_norm]
  have h_qvar : qv = var (F := F circomPrime) { index := offset } := rfl
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.witnessField_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_structuralComputableWitnesses_iff]
  and_intros
  · intro _ h_input
    have ha : eval env input.a = eval env' input.a := by
      simpa [circuit_norm] using congrArg (fun x : Inputs (F circomPrime) => x.a) h_input
    have hb : eval env input.b = eval env' input.b := by
      simpa [circuit_norm] using congrArg (fun x : Inputs (F circomPrime) => x.b) h_input
    have ht : eval env input.target = eval env' input.target := by
      simpa [circuit_norm] using congrArg (fun x : Inputs (F circomPrime) => x.target) h_input
    rw [qNat_stable input ha hb ht]
  · exact Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
      (RangeCheck.circuit qBitsFold32T (by decide) (by decide)) input qv rcOff
      (by
        intro k e1 e2 hle h_agree _
        have hk : offset + 1 ≤ k := by
          dsimp only [rcOff] at hle; rw [h_qlen] at hle; omega
        rw [h_qvar]
        simpa [circuit_norm] using h_agree offset (by omega))
      (RangeCheck.computableWitnesses qBitsFold32T (by decide) (by decide)) env env'
  · exact Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
      (GroupedEqXV.circuit 32 gfFold32T posOfFold32T 3 vFold32TL vFold32TR hgvFold32T (by norm_num))
      input { lhs := foldLhs32 (bigIntMulNoReduce input.a input.b),
              rhs := foldRhs32 qv input.target } eqOff
      (by
        intro k e1 e2 hle h_agree h_input
        have hk_q : offset + 1 ≤ k := by
          dsimp only [eqOff, rcOff] at hle; rw [h_qlen] at hle; omega
        have hq : Expression.eval e1.toEnvironment (var (F := F circomPrime) { index := offset })
            = Expression.eval e2.toEnvironment (var (F := F circomPrime) { index := offset }) :=
          h_agree offset (by omega)
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
            Expression.eval e1.toEnvironment
                ((bigIntMulNoReduce input.a input.b)[i]'hi)
              = Expression.eval e2.toEnvironment
                ((bigIntMulNoReduce input.a input.b)[i]'hi) := by
          intro i hi
          exact bigIntMulNoReduce_coeff_stable e1.toEnvironment e2.toEnvironment
            input.a input.b ha_i hb_i ⟨i, hi⟩
        have ht_i : ∀ (i : ℕ) (hi : i < numLimbs),
            Expression.eval e1.toEnvironment (input.target[i]'hi)
              = Expression.eval e2.toEnvironment (input.target[i]'hi) :=
          fun i hi => bigInt_getElem_eval_eq ht i hi
        have hL := foldLhs32_stable (E1 := e1.toEnvironment) (E2 := e2.toEnvironment)
          (bigIntMulNoReduce input.a input.b) hPc_i
        have hR := foldRhs32_stable (E1 := e1.toEnvironment) (E2 := e2.toEnvironment)
          qv input.target (by rw [h_qvar]; exact hq) ht_i
        simp only [circuit_norm]
        rw [hL, hR])
      (GroupedEqXV.computableWitnesses 32 gfFold32T posOfFold32T 3 vFold32TL vFold32TR hgvFold32T
        (by norm_num))
      env env'

end MulModFold32TA
end Solution.Secp256k1ScalarMul
