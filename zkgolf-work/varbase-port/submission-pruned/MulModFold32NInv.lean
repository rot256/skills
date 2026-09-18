import Solution.Secp256k1ScalarMul.MulModFold32N
import Solution.Secp256k1ScalarMul.GroupedEqXVNoTop

/-!
# Quotient-inverted `MulModFold32N`

The folded quotient is uniquely determined over the native field because the
secp256k1 modulus is a nonzero constant.  Recover it as an affine expression
after the interpolated product has been allocated, retain its range check, and
drop the now-tautological native row of the grouped equality.
-/

set_option exponentiation.threshold 600

namespace Solution.Secp256k1ScalarMul
namespace MulModFold32N

open MulMod
open Solution.Secp256k1ScalarMul.Limbs

/-- Native polynomial of the folded product side. -/
def lhsPolyInv (Pc : Vector (Expression (F circomPrime)) 15) :
    Expression (F circomPrime) :=
  polyEvalExpr (foldLhs32 Pc) ((2 : F circomPrime) ^ 32)

/-- Target embedded in the even 32-bit positions. -/
def targetVecInv (t : Var Emu (F circomPrime)) :
    Vector (Expression (F circomPrime)) 8 :=
  #v[t[0], 0, t[1], 0, t[2], 0, t[3], 0]

/-- Native polynomial of the target. -/
def targetPolyInv (t : Var Emu (F circomPrime)) : Expression (F circomPrime) :=
  polyEvalExpr (targetVecInv t) ((2 : F circomPrime) ^ 32)

/-- The quotient recovered from the native identity. -/
def qInv (Pc : Vector (Expression (F circomPrime)) 15)
    (t : Var Emu (F circomPrime)) : Expression (F circomPrime) :=
  (((P256 : ℕ) : F circomPrime)⁻¹) * (lhsPolyInv Pc - targetPolyInv t)

lemma P256_cast_ne_zero : (((P256 : ℕ) : F circomPrime)) ≠ 0 := by
  norm_num [P256, Specs.Secp256k1.p, circomPrime,
    Challenge.Instances.Secp256k1ScalarMul.Interface.circomPrime]
  decide

lemma eval_targetPolyInv (env : Environment (F circomPrime))
    (t : Var Emu (F circomPrime)) :
    Expression.eval env (targetPolyInv t)
      = ((BigInt.value 64 (Vector.map (Expression.eval env) t) : ℕ) : F circomPrime) := by
  rw [bigIntValue_four]
  simp [targetPolyInv, targetVecInv, polyEvalExpr_eval, Fin.sum_univ_eight,
    Expression.eval]
  norm_num
  rw [ZMod.cast_id circomPrime (Expression.eval env t[0]),
    ZMod.cast_id circomPrime (Expression.eval env t[1]),
    ZMod.cast_id circomPrime (Expression.eval env t[2]),
    ZMod.cast_id circomPrime (Expression.eval env t[3])]

lemma eval_targetPolyInv_expanded (env : Environment (F circomPrime))
    (t : Var Emu (F circomPrime)) :
    Expression.eval env (targetPolyInv t)
      = Expression.eval env t[0]
        + Expression.eval env t[1] * (2 : F circomPrime) ^ 64
        + Expression.eval env t[2] * (2 : F circomPrime) ^ 128
        + Expression.eval env t[3] * (2 : F circomPrime) ^ 192 := by
  simp [targetPolyInv, targetVecInv, polyEvalExpr_eval, Fin.sum_univ_eight,
    Expression.eval]
  norm_num

lemma eval_lhsPolyInv (env : Environment (F circomPrime))
    (Pc : Vector (Expression (F circomPrime)) 15) :
    Expression.eval env (lhsPolyInv Pc)
      = ((polyValue 32 (Vector.map (Expression.eval env) (foldLhs32 Pc)) : ℕ) :
          F circomPrime) := by
  unfold lhsPolyInv
  rw [polyEvalExpr_eval]
  symm
  exact GroupedEqXV.polyValue_eval_cast 32 env (foldLhs32 Pc)
    (Vector.map (Expression.eval env) (foldLhs32 Pc))
    (fun j hj => by simp only [Vector.getElem_map])

/-- Under the honest integer certificate identity, `qInv` evaluates to the
honest quotient. -/
lemma eval_qInv_of_identity (env : Environment (F circomPrime))
    (Pc : Vector (Expression (F circomPrime)) 15) (t : Var Emu (F circomPrime))
    (q0 : ℕ)
    (hid : polyValue 32 (Vector.map (Expression.eval env) (foldLhs32 Pc))
      = q0 * P256 + BigInt.value 64 (Vector.map (Expression.eval env) t)) :
    Expression.eval env (qInv Pc t) = ((q0 : ℕ) : F circomPrime) := by
  have hL := eval_lhsPolyInv env Pc
  have hT := eval_targetPolyInv env t
  have hkey : Expression.eval env (lhsPolyInv Pc)
      - Expression.eval env (targetPolyInv t)
      = ((q0 : ℕ) : F circomPrime) * ((P256 : ℕ) : F circomPrime) := by
    rw [hL, hT, hid]
    push_cast
    ring
  have hinv : (((P256 : ℕ) : F circomPrime))⁻¹
      * ((P256 : ℕ) : F circomPrime) = 1 := inv_mul_cancel₀ P256_cast_ne_zero
  simp only [qInv, Expression.eval]
  linear_combination (((P256 : ℕ) : F circomPrime))⁻¹ * hkey
    + ((q0 : ℕ) : F circomPrime) * hinv

lemma qInv_mul_P256 (env : Environment (F circomPrime))
    (Pc : Vector (Expression (F circomPrime)) 15) (t : Var Emu (F circomPrime)) :
    Expression.eval env (qInv Pc t) * ((P256 : ℕ) : F circomPrime)
      = Expression.eval env (lhsPolyInv Pc) - Expression.eval env (targetPolyInv t) := by
  simp only [qInv, Expression.eval]
  calc
    ((↑P256 : F circomPrime)⁻¹ *
          (Expression.eval env (lhsPolyInv Pc) +
            -1 * Expression.eval env (targetPolyInv t))) * ↑P256
        = (Expression.eval env (lhsPolyInv Pc) - Expression.eval env (targetPolyInv t))
            * ((↑P256 : F circomPrime)⁻¹ * ↑P256) := by ring
    _ = Expression.eval env (lhsPolyInv Pc) - Expression.eval env (targetPolyInv t) := by
      rw [inv_mul_cancel₀ P256_cast_ne_zero, mul_one]

lemma eval_foldRhs32_poly (env : Environment (F circomPrime))
    (q : Expression (F circomPrime)) (t : Var Emu (F circomPrime)) :
    Expression.eval env
        (polyEvalExpr (foldRhs32 q t) ((2 : F circomPrime) ^ 32))
      = Expression.eval env q * ((P256 : ℕ) : F circomPrime)
        + Expression.eval env (targetPolyInv t) := by
  rw [polyEvalExpr_eval]
  simp [Fin.sum_univ_eight, foldRhs32, pElim, Expression.eval]
  have hp := congrArg (fun n : ℕ => (n : F circomPrime)) pNat32_sum
  push_cast at hp
  have ht := eval_targetPolyInv_expanded env t
  norm_num at hp ⊢
  rw [ht]
  linear_combination (Expression.eval env q) * hp

/-- The deleted native row holds identically for the inverted quotient. -/
lemma qInv_linIdent (env : Environment (F circomPrime))
    (Pc : Vector (Expression (F circomPrime)) 15) (t : Var Emu (F circomPrime)) :
    GroupedEqXV.LinIdent 32
      { lhs := Vector.map (Expression.eval env) (foldLhs32 Pc),
        rhs := Vector.map (Expression.eval env) (foldRhs32 (qInv Pc t) t) } := by
  have hQ := qInv_mul_P256 env Pc t
  have hR := eval_foldRhs32_poly env (qInv Pc t) t
  simp only [GroupedEqXV.LinIdent, Vector.getElem_map]
  rw [← polyEvalExpr_eval env (foldLhs32 Pc),
    ← polyEvalExpr_eval env (foldRhs32 (qInv Pc t) t)]
  change Expression.eval env (lhsPolyInv Pc) = _
  rw [hR]
  exact eq_add_of_sub_eq hQ.symm

lemma lhsPolyInv_stable {E1 E2 : Environment (F circomPrime)}
    (Pc : Vector (Expression (F circomPrime)) 15)
    (hPc : ∀ (i : ℕ) (hi : i < 15),
      Expression.eval E1 (Pc[i]'hi) = Expression.eval E2 (Pc[i]'hi)) :
    Expression.eval E1 (lhsPolyInv Pc) = Expression.eval E2 (lhsPolyInv Pc) := by
  have hL := foldLhs32_stable (E1 := E1) (E2 := E2) Pc hPc
  have hLi : ∀ (i : ℕ) (hi : i < 8),
      Expression.eval E1 ((foldLhs32 Pc)[i]'hi)
        = Expression.eval E2 ((foldLhs32 Pc)[i]'hi) := by
    intro i hi
    simpa only [Vector.getElem_map] using
      congrArg (fun v : Vector (F circomPrime) 8 => v[i]'hi) hL
  simp only [lhsPolyInv, polyEvalExpr_eval]
  apply Finset.sum_congr rfl
  intro i _
  rw [hLi i.val i.isLt]

lemma targetPolyInv_stable {E1 E2 : Environment (F circomPrime)}
    (t : Var Emu (F circomPrime))
    (ht : ∀ (i : ℕ) (hi : i < numLimbs),
      Expression.eval E1 (t[i]'hi) = Expression.eval E2 (t[i]'hi)) :
    Expression.eval E1 (targetPolyInv t) = Expression.eval E2 (targetPolyInv t) := by
  rw [eval_targetPolyInv_expanded, eval_targetPolyInv_expanded]
  rw [ht 0 (by decide), ht 1 (by decide), ht 2 (by decide), ht 3 (by decide)]

lemma qInv_stable {E1 E2 : Environment (F circomPrime)}
    (Pc : Vector (Expression (F circomPrime)) 15) (t : Var Emu (F circomPrime))
    (hPc : ∀ (i : ℕ) (hi : i < 15),
      Expression.eval E1 (Pc[i]'hi) = Expression.eval E2 (Pc[i]'hi))
    (ht : ∀ (i : ℕ) (hi : i < numLimbs),
      Expression.eval E1 (t[i]'hi) = Expression.eval E2 (t[i]'hi)) :
    Expression.eval E1 (qInv Pc t) = Expression.eval E2 (qInv Pc t) := by
  simp only [qInv, Expression.eval]
  rw [lhsPolyInv_stable Pc hPc, targetPolyInv_stable t ht]

def mainInv (input : Var Inputs (F circomPrime)) : Circuit (F circomPrime) Unit := do
  let Pc ← interpolatedMul14 input.a input.b
  assertion (RangeCheck.circuit qBitsFold32N (by decide) (by decide))
    (qInv Pc input.target)
  assertion
    (GroupedEqXV.circuitNoTop 32 gfFold32N posOfFold32N 3 vFold32NL vFold32NR
      hgvFold32N (by norm_num))
    { lhs := foldLhs32 Pc, rhs := foldRhs32 (qInv Pc input.target) input.target }

instance elaboratedInv : ElaboratedCircuit (F circomPrime) Inputs unit mainInv where
  localLength _ := 156
  localLength_eq := by
    intro input offset
    simp only [mainInv, interpolatedMul14, circuit_norm, RangeCheck.circuit,
      GroupedEqXV.circuitNoTop, GroupedEqXV.elaboratedNoTop, vFold32NL, wfFold32N,
      GroupedEqXV.widthAllocFrom, qBitsFold32N]
  subcircuitsConsistent := by
    intro input offset
    simp +arith only [mainInv, interpolatedMul14, circuit_norm, RangeCheck.circuit,
      GroupedEqXV.circuitNoTop, GroupedEqXV.elaboratedNoTop]
  channelsLawful := by
    intro offset
    simp only [mainInv, interpolatedMul14, circuit_norm, RangeCheck.circuit,
      GroupedEqXV.circuitNoTop, GroupedEqXV.elaboratedNoTop]

attribute [local irreducible] interpolatedMul14 RangeCheck.circuit GroupedEqXV.circuitNoTop GroupedEqXV.mainNoTop qInv lhsPolyInv targetPolyInv

set_option maxHeartbeats 8000000 in
theorem soundnessInv (Ca Cb : ℕ) (hcap : 4 * (Ca * Cb) ≤ (3 * 2 ^ 98)) :
    FormalAssertion.Soundness (F circomPrime) mainInv (Assumptions Ca Cb) Spec := by
  circuit_proof_start [mainInv,
    RangeCheck.circuit, RangeCheck.Assumptions, RangeCheck.Spec,
    GroupedEqXV.circuitNoTop, GroupedEqXV.elaboratedNoTop,
    GroupedEqXV.AssumptionsNoTop, GroupedEqXV.Assumptions, GroupedEqX.Spec]
  obtain ⟨hAB_ops, hq_lt, h_eq_impl⟩ := h_holds
  obtain ⟨ha_lt, hb_lt, hb_zero, ht_lt, ht_val⟩ := h_assumptions
  obtain ⟨ha_in, hb_in, ht_in⟩ := h_input
  simp only [vFold32NL, vFold32NR, nfFold32NL, nfFold32NR] at h_eq_impl
  have hpm : (14 : ℕ) < circomPrime := by decide
  have hbz' : ∀ i : Fin 8, i.val % 2 = 1 →
      Expression.eval env (input_var_b[i.val]'i.isLt) = 0 := by
    intro i hi
    rw [show Expression.eval env (input_var_b[i.val]'i.isLt) = input_b[i.val] from by
      rw [← hb_in]; simp only [Vector.getElem_map]]
    exact hb_zero i hi
  have hb7 : Expression.eval env (input_var_b[7]'(by decide)) = 0 :=
    hbz' ⟨7, by decide⟩ (by decide)
  have hbridge := interpolatedMul14_eval_bridge env i₀ input_var_a input_var_b hpm hb7
    (interpolatedMul14_soundness i₀ input_var_a input_var_b env hAB_ops)
  have ha_lt' : ∀ i : Fin 8,
      (Expression.eval env (input_var_a[i.val]'i.isLt)).val < Ca := by
    intro i
    have hi := congrArg (fun v : BigInt 8 (F circomPrime) => v[i.val]'i.isLt) ha_in
    simp only [Vector.getElem_map] at hi
    rw [hi]
    exact ha_lt i
  have hb_lt' : ∀ i : Fin 8,
      (Expression.eval env (input_var_b[i.val]'i.isLt)).val < Cb := by
    intro i
    have hi := congrArg (fun v : BigInt 8 (F circomPrime) => v[i.val]'i.isLt) hb_in
    simp only [Vector.getElem_map] at hi
    rw [hi]
    exact hb_lt i
  have ht_lt' : ∀ i : Fin numLimbs,
      (Expression.eval env (input_var_target[i.val]'i.isLt)).val < 3 * 2 ^ 64 := by
    intro i
    have hi := congrArg (fun v : Emu (F circomPrime) => v[i.val]'i.isLt) ht_in
    simp only [Vector.getElem_map] at hi
    rw [hi]
    exact ht_lt i
  have hNbp : 8 * (Ca * Cb) < circomPrime := by
    have h2 : (2 : ℕ) ^ 102 < circomPrime := by decide
    omega
  have hcap97 : Ca * Cb ≤ 3 * 2 ^ 96 := by
    refine Nat.le_of_mul_le_mul_left ?_ (show 0 < 4 by norm_num)
    calc 4 * (Ca * Cb) ≤ 3 * 2 ^ 98 := hcap
      _ = 4 * (3 * 2 ^ 96) := by norm_num
  have hPv : ∀ k : Fin 15,
      (Expression.eval env (interpolatedMul14 input_var_a input_var_b i₀).1[k.val]).val
        < sparseNf k.val := by
    intro k
    rw [hbridge k, coeff_eq_convNat env input_var_a input_var_b ha_lt' hb_lt' hNbp k]
    exact convNat_lt_sparse_tri env input_var_a input_var_b ha_lt' hb_lt' hbz' hcap97 k.val
  have hqv : (Expression.eval env
      (qInv (interpolatedMul14 input_var_a input_var_b i₀).1 input_var_target)).val < 2 ^ 68 :=
    hq_lt
  have heq := h_eq_impl
    ⟨⟨foldLhs32_bound env _ hPv,
       foldRhs32_bound env _ input_var_target hqv ht_lt'⟩,
      qInv_linIdent env (interpolatedMul14 input_var_a input_var_b i₀).1 input_var_target⟩
  rw [foldLhs32_polyValue env _ hPv,
    foldRhs32_polyValue env _ input_var_target hqv ht_lt',
    foldDNatOf_eq env input_var_a input_var_b ha_lt' hb_lt' hNbp _ hbridge, ht_in] at heq
  have hid := foldDNat_identity env input_var_a input_var_b ha_lt' hb_lt' hNbp
  rw [ha_in, hb_in] at hid
  exact ⟨target_congr hid heq, interpolatedMul14_requirements _ _ _ _⟩

set_option maxHeartbeats 8000000 in
theorem completenessInv (Ca Cb : ℕ) (hcap : 4 * (Ca * Cb) ≤ (3 * 2 ^ 98)) :
    FormalAssertion.Completeness (F circomPrime) mainInv (Assumptions Ca Cb) Spec := by
  circuit_proof_start [mainInv,
    RangeCheck.circuit, RangeCheck.Assumptions, RangeCheck.Spec,
    GroupedEqXV.circuitNoTop, GroupedEqXV.elaboratedNoTop,
    GroupedEqXV.AssumptionsNoTop, GroupedEqXV.Assumptions, GroupedEqX.Spec]
  have hAB_uses := h_env
  obtain ⟨ha_lt, hb_lt, hb_zero, ht_lt, ht_val⟩ := h_assumptions
  obtain ⟨ha_in, hb_in, ht_in⟩ := h_input
  simp only [vFold32NL, vFold32NR, nfFold32NL, nfFold32NR]
  have ha_lt' : ∀ i : Fin 8,
      (Expression.eval env.toEnvironment (input_var_a[i.val]'i.isLt)).val < Ca := by
    intro i
    have hi := congrArg (fun v : BigInt 8 (F circomPrime) => v[i.val]'i.isLt) ha_in
    simp only [Vector.getElem_map] at hi
    rw [hi]
    exact ha_lt i
  have hb_lt' : ∀ i : Fin 8,
      (Expression.eval env.toEnvironment (input_var_b[i.val]'i.isLt)).val < Cb := by
    intro i
    have hi := congrArg (fun v : BigInt 8 (F circomPrime) => v[i.val]'i.isLt) hb_in
    simp only [Vector.getElem_map] at hi
    rw [hi]
    exact hb_lt i
  have ht_lt' : ∀ i : Fin numLimbs,
      (Expression.eval env.toEnvironment (input_var_target[i.val]'i.isLt)).val
        < 3 * 2 ^ 64 := by
    intro i
    have hi := congrArg (fun v : Emu (F circomPrime) => v[i.val]'i.isLt) ht_in
    simp only [Vector.getElem_map] at hi
    rw [hi]
    exact ht_lt i
  have hNbp : 8 * (Ca * Cb) < circomPrime := by
    have h2 : (2 : ℕ) ^ 102 < circomPrime := by decide
    omega
  have hbz' : ∀ i : Fin 8, i.val % 2 = 1 →
      Expression.eval env.toEnvironment (input_var_b[i.val]'i.isLt) = 0 := by
    intro i hi
    rw [show Expression.eval env.toEnvironment (input_var_b[i.val]'i.isLt) = input_b[i.val] from by
      rw [← hb_in]; simp only [Vector.getElem_map]]
    exact hb_zero i hi
  have hb7 : Expression.eval env.toEnvironment (input_var_b[7]'(by decide)) = 0 :=
    hbz' ⟨7, by decide⟩ (by decide)
  have h_pvAB := interpolatedMul14_usesLocalWitnesses i₀ i₀ input_var_a input_var_b env rfl hAB_uses
  have hbridge := interpolatedMul14_eval_bridge_uses env.toEnvironment i₀
    input_var_a input_var_b hb7 h_pvAB
  have hcap97 : Ca * Cb ≤ 3 * 2 ^ 96 := by
    refine Nat.le_of_mul_le_mul_left ?_ (show 0 < 4 by norm_num)
    calc 4 * (Ca * Cb) ≤ 3 * 2 ^ 98 := hcap
      _ = 4 * (3 * 2 ^ 96) := by norm_num
  have hPv : ∀ k : Fin 15,
      (Expression.eval env.toEnvironment
        (interpolatedMul14 input_var_a input_var_b i₀).1[k.val]).val < sparseNf k.val := by
    intro k
    rw [hbridge k,
      coeff_eq_convNat env.toEnvironment input_var_a input_var_b ha_lt' hb_lt' hNbp k]
    exact convNat_lt_sparse_tri env.toEnvironment input_var_a input_var_b ha_lt' hb_lt' hbz'
      hcap97 k.val
  set D := foldDNat env.toEnvironment input_var_a input_var_b with hDdef
  set T := BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) input_var_target)
    with hTdef
  have hT3 : T < 3 * P256 := by rw [hTdef, ht_in]; exact ht_val
  have hDge : 3 * P256 ≤ D := foldDNat_ge env.toEnvironment input_var_a input_var_b
  have hDlt : D < 3 * 2 ^ 322 + 2 ^ 299 :=
    foldDNat_lt env.toEnvironment input_var_a input_var_b ha_lt' hb_lt' hbz' hcap
  have hid := foldDNat_identity env.toEnvironment input_var_a input_var_b ha_lt' hb_lt' hNbp
  rw [ha_in, hb_in] at hid
  have hDmod : D % P256 = T % P256 := by
    rw [foldD_mod hid, hTdef, ht_in]
    exact h_spec.symm
  let q0 := (D - T) / P256
  have hqlt : q0 < 2 ^ 68 := by
    have hdiv : (D - T) / P256 ≤ D / P256 := Nat.div_le_div_right (by omega)
    have hD2 : D / P256 < 2 ^ 68 := by
      apply Nat.div_lt_of_lt_mul
      have hle : (3 : ℕ) * 2 ^ 322 + 2 ^ 299 ≤ 2 ^ 68 * P256 := by decide
      omega
    exact lt_of_le_of_lt hdiv hD2
  have hreconstruct : q0 * P256 + T = D := by
    exact quot_reconstruct (by omega) hDmod
  have hqIdentity :
      polyValue 32 (Vector.map (Expression.eval env.toEnvironment)
        (foldLhs32 (interpolatedMul14 input_var_a input_var_b i₀).1))
        = q0 * P256 + BigInt.value 64
          (Vector.map (Expression.eval env.toEnvironment) input_var_target) := by
    rw [foldLhs32_polyValue env.toEnvironment _ hPv,
      foldDNatOf_eq env.toEnvironment input_var_a input_var_b ha_lt' hb_lt' hNbp _ hbridge,
      ← hTdef]
    exact hreconstruct.symm
  have hqeval := eval_qInv_of_identity env.toEnvironment
    (interpolatedMul14 input_var_a input_var_b i₀).1 input_var_target q0 hqIdentity
  have hqval : (Expression.eval env.toEnvironment
      (qInv (interpolatedMul14 input_var_a input_var_b i₀).1 input_var_target)).val = q0 := by
    rw [hqeval, ZMod.val_natCast_of_lt]
    have hp : (2 : ℕ) ^ 72 < circomPrime := by decide
    omega
  have hqvar : (Expression.eval env.toEnvironment
      (qInv (interpolatedMul14 input_var_a input_var_b i₀).1 input_var_target)).val < 2 ^ 68 := by
    rw [hqval]
    exact hqlt
  refine ⟨interpolatedMul14_completeness i₀ input_var_a input_var_b env hb7 h_pvAB,
    ?_, ?_, ?_⟩
  · rw [hqval]
    exact hqlt
  · exact ⟨⟨foldLhs32_bound env.toEnvironment _ hPv,
      foldRhs32_bound env.toEnvironment _ input_var_target hqvar ht_lt'⟩,
      qInv_linIdent env.toEnvironment
        (interpolatedMul14 input_var_a input_var_b i₀).1 input_var_target⟩
  · rw [foldLhs32_polyValue env.toEnvironment _ hPv,
      foldRhs32_polyValue env.toEnvironment _ input_var_target hqvar ht_lt',
      foldDNatOf_eq env.toEnvironment input_var_a input_var_b ha_lt' hb_lt' hNbp _ hbridge]
    show D = (Expression.eval env.toEnvironment
      (qInv (interpolatedMul14 input_var_a input_var_b i₀).1 input_var_target)).val
        * P256 + T
    rw [hqval]
    exact hreconstruct.symm

def circuitInv (Ca Cb : ℕ) (hcap : 4 * (Ca * Cb) ≤ (3 * 2 ^ 98)) :
    FormalAssertion (F circomPrime) Inputs where
  main := mainInv
  Assumptions := Assumptions Ca Cb
  Spec := Spec
  soundness := soundnessInv Ca Cb hcap
  completeness := completenessInv Ca Cb hcap

set_option maxHeartbeats 4000000 in
theorem computableWitnessesInv (Ca Cb : ℕ) (hcap : 4 * (Ca * Cb) ≤ (3 * 2 ^ 98)) :
    (circuitInv Ca Cb hcap).ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition
      input env env') ((mainInv input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold mainInv
  let pcOff := offset
  let pcv := (interpolatedMul14 input.a input.b).output pcOff
  let qv := qInv pcv input.target
  let rcOff := pcOff + (interpolatedMul14 input.a input.b).localLength pcOff
  let rcc : Circuit (F circomPrime) Unit :=
    assertion (RangeCheck.circuit qBitsFold32N (by decide) (by decide)) qv
  let eqOff := rcOff + rcc.localLength rcOff
  have h_pclen : (interpolatedMul14 input.a input.b).localLength pcOff = 14 :=
    interpolatedMul14_localLength pcOff input.a input.b
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.pure_structuralComputableWitnesses_iff,
    and_true]
  and_intros
  · exact interpolatedMul14_structuralComputableWitnesses input input.a input.b pcOff
      (by
        intro k e1 e2 _ _ h_input
        have ha : eval e1 input.a = eval e2 input.a := by
          simpa [circuit_norm] using
            congrArg (fun x : Inputs (F circomPrime) => x.a) h_input
        have hb : eval e1 input.b = eval e2 input.b := by
          simpa [circuit_norm] using
            congrArg (fun x : Inputs (F circomPrime) => x.b) h_input
        exact ⟨ha, hb⟩)
      env env'
  · exact Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
      (RangeCheck.circuit qBitsFold32N (by decide) (by decide)) input qv rcOff
      (by
        intro k e1 e2 hle h_agree h_input
        have hk_pc : pcOff + 14 ≤ k := by
          dsimp only [rcOff] at hle
          rw [h_pclen] at hle
          exact hle
        have hPc : Vector.map (Expression.eval e1.toEnvironment) pcv
            = Vector.map (Expression.eval e2.toEnvironment) pcv :=
          interpolatedMul14_output_stable pcOff input.a input.b h_agree hk_pc
        have hPc_i : ∀ (i : ℕ) (hi : i < 15),
            Expression.eval e1.toEnvironment (pcv[i]'hi)
              = Expression.eval e2.toEnvironment (pcv[i]'hi) := by
          intro i hi
          simpa only [Vector.getElem_map] using
            congrArg (fun v : Vector (F circomPrime) 15 => v[i]'hi) hPc
        have ht : eval e1 input.target = eval e2 input.target := by
          simpa [circuit_norm] using
            congrArg (fun x : Inputs (F circomPrime) => x.target) h_input
        have ht_i : ∀ (i : ℕ) (hi : i < numLimbs),
            Expression.eval e1.toEnvironment (input.target[i]'hi)
              = Expression.eval e2.toEnvironment (input.target[i]'hi) :=
          fun i hi => bigInt_getElem_eval_eq ht i hi
        simpa only [qv, circuit_norm] using qInv_stable pcv input.target hPc_i ht_i)
      (RangeCheck.computableWitnesses qBitsFold32N (by decide) (by decide)) env env'
  · exact Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
      (GroupedEqXV.circuitNoTop 32 gfFold32N posOfFold32N 3 vFold32NL vFold32NR
        hgvFold32N (by norm_num))
      input { lhs := foldLhs32 pcv, rhs := foldRhs32 qv input.target } eqOff
      (by
        intro k e1 e2 hle h_agree h_input
        have hk_pc : pcOff + 14 ≤ k := by
          dsimp only [eqOff, rcOff] at hle
          rw [h_pclen] at hle
          omega
        have hPc : Vector.map (Expression.eval e1.toEnvironment) pcv
            = Vector.map (Expression.eval e2.toEnvironment) pcv :=
          interpolatedMul14_output_stable pcOff input.a input.b h_agree hk_pc
        have hPc_i : ∀ (i : ℕ) (hi : i < 15),
            Expression.eval e1.toEnvironment (pcv[i]'hi)
              = Expression.eval e2.toEnvironment (pcv[i]'hi) := by
          intro i hi
          simpa only [Vector.getElem_map] using
            congrArg (fun v : Vector (F circomPrime) 15 => v[i]'hi) hPc
        have ht : eval e1 input.target = eval e2 input.target := by
          simpa [circuit_norm] using
            congrArg (fun x : Inputs (F circomPrime) => x.target) h_input
        have ht_i : ∀ (i : ℕ) (hi : i < numLimbs),
            Expression.eval e1.toEnvironment (input.target[i]'hi)
              = Expression.eval e2.toEnvironment (input.target[i]'hi) :=
          fun i hi => bigInt_getElem_eval_eq ht i hi
        have hq := qInv_stable pcv input.target hPc_i ht_i
        have hL := foldLhs32_stable
          (E1 := e1.toEnvironment) (E2 := e2.toEnvironment) pcv hPc_i
        have hR := foldRhs32_stable
          (E1 := e1.toEnvironment) (E2 := e2.toEnvironment)
          qv input.target hq ht_i
        simp only [circuit_norm]
        rw [hL, hR])
      (GroupedEqXV.computableWitnessesNoTop 32 gfFold32N posOfFold32N 3
        vFold32NL vFold32NR hgvFold32N (by norm_num))
      env env'

end MulModFold32N
end Solution.Secp256k1ScalarMul
