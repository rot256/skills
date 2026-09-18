import Solution.Secp256k1ScalarMul.MulModFoldT
import Solution.Secp256k1ScalarMul.GroupedEqXVNoTop

/-!
# Quotient-inverted `MulModFoldT`

The folded quotient is uniquely determined over the native field because the
secp256k1 modulus is a nonzero constant.  Recover it as an affine expression
after the CRT product digits have been allocated, retain its range check, and
drop the now-tautological native row of the grouped equality.
-/

set_option exponentiation.threshold 600

namespace Solution.Secp256k1ScalarMul
namespace MulModFoldT

open MulMod
open Solution.Secp256k1ScalarMul.Limbs
open MulModFold

/-- Native polynomial of the folded product side. -/
def lhsPolyInv (d : Vector (Expression (F circomPrime)) numLimbs) :
    Expression (F circomPrime) :=
  polyEvalExpr (foldLhsC d) ((2 : F circomPrime) ^ 64)

/-- Native polynomial of the folded target (the `q = 0` right-hand side). -/
def targetPolyInv (T : Var TVec (F circomPrime)) : Expression (F circomPrime) :=
  polyEvalExpr (foldRhsT 0 T) ((2 : F circomPrime) ^ 64)

/-- The quotient recovered from the native identity. -/
def qInv (d : Vector (Expression (F circomPrime)) numLimbs)
    (T : Var TVec (F circomPrime)) : Expression (F circomPrime) :=
  (((P256 : ℕ) : F circomPrime)⁻¹) * (lhsPolyInv d - targetPolyInv T)

lemma P256_cast_ne_zero : (((P256 : ℕ) : F circomPrime)) ≠ 0 := by
  norm_num [P256, Specs.Secp256k1.p, circomPrime,
    Challenge.Instances.Secp256k1ScalarMul.Interface.circomPrime]
  decide

lemma eval_lhsPolyInv (env : Environment (F circomPrime))
    (d : Vector (Expression (F circomPrime)) numLimbs) :
    Expression.eval env (lhsPolyInv d)
      = ((polyValue 64 (Vector.map (Expression.eval env) (foldLhsC d)) : ℕ) :
          F circomPrime) := by
  unfold lhsPolyInv
  rw [polyEvalExpr_eval]
  symm
  exact GroupedEqXV.polyValue_eval_cast 64 env (foldLhsC d)
    (Vector.map (Expression.eval env) (foldLhsC d))
    (fun j hj => by simp only [Vector.getElem_map])

lemma eval_targetPolyInv (env : Environment (F circomPrime))
    (T : Var TVec (F circomPrime)) :
    Expression.eval env (targetPolyInv T)
      = ((polyValue 64 (Vector.map (Expression.eval env) (foldRhsT 0 T)) : ℕ) :
          F circomPrime) := by
  unfold targetPolyInv
  rw [polyEvalExpr_eval]
  symm
  exact GroupedEqXV.polyValue_eval_cast 64 env (foldRhsT 0 T)
    (Vector.map (Expression.eval env) (foldRhsT 0 T))
    (fun j hj => by simp only [Vector.getElem_map])

lemma eval_targetPolyInv_expanded (env : Environment (F circomPrime))
    (T : Var TVec (F circomPrime)) :
    Expression.eval env (targetPolyInv T)
      = (Expression.eval env T[0]
          + ((cFold : ℕ) : F circomPrime) * Expression.eval env T[4])
        + (Expression.eval env T[1]
          + ((cFold : ℕ) : F circomPrime) * Expression.eval env T[5])
            * (2 : F circomPrime) ^ 64
        + (Expression.eval env T[2]
          + ((cFold : ℕ) : F circomPrime) * Expression.eval env T[6])
            * ((2 : F circomPrime) ^ 64) ^ 2
        + Expression.eval env T[3] * ((2 : F circomPrime) ^ 64) ^ 3 := by
  unfold targetPolyInv
  rw [polyEvalExpr_eval]
  simp [Fin.sum_univ_four, foldRhsT, pElim, cfE, Expression.eval, numLimbs]

/-- The native row that the grouped equality would otherwise assert. -/
lemma eval_foldRhsT_poly (env : Environment (F circomPrime))
    (q : Expression (F circomPrime)) (T : Var TVec (F circomPrime)) :
    Expression.eval env
        (polyEvalExpr (foldRhsT q T) ((2 : F circomPrime) ^ 64))
      = Expression.eval env q * ((P256 : ℕ) : F circomPrime)
        + Expression.eval env (targetPolyInv T) := by
  rw [polyEvalExpr_eval, eval_targetPolyInv_expanded]
  simp [Fin.sum_univ_four, foldRhsT, pElim, cfE, Expression.eval, numLimbs]
  have hp := congrArg (fun n : ℕ => (n : F circomPrime)) pNat_sum
  push_cast at hp
  norm_num at hp ⊢
  linear_combination (Expression.eval env q) * hp

lemma qInv_mul_P256 (env : Environment (F circomPrime))
    (d : Vector (Expression (F circomPrime)) numLimbs) (T : Var TVec (F circomPrime)) :
    Expression.eval env (qInv d T) * ((P256 : ℕ) : F circomPrime)
      = Expression.eval env (lhsPolyInv d) - Expression.eval env (targetPolyInv T) := by
  simp only [qInv, Expression.eval]
  calc
    ((↑P256 : F circomPrime)⁻¹ *
          (Expression.eval env (lhsPolyInv d) +
            -1 * Expression.eval env (targetPolyInv T))) * ↑P256
        = (Expression.eval env (lhsPolyInv d) - Expression.eval env (targetPolyInv T))
            * ((↑P256 : F circomPrime)⁻¹ * ↑P256) := by ring
    _ = Expression.eval env (lhsPolyInv d) - Expression.eval env (targetPolyInv T) := by
      rw [inv_mul_cancel₀ P256_cast_ne_zero, mul_one]

/-- Under the honest integer certificate identity, `qInv` evaluates to the
honest quotient. -/
lemma eval_qInv_of_identity (env : Environment (F circomPrime))
    (d : Vector (Expression (F circomPrime)) numLimbs) (T : Var TVec (F circomPrime))
    (q0 : ℕ)
    (hid : polyValue 64 (Vector.map (Expression.eval env) (foldLhsC d))
      = q0 * P256 + polyValue 64 (Vector.map (Expression.eval env) (foldRhsT 0 T))) :
    Expression.eval env (qInv d T) = ((q0 : ℕ) : F circomPrime) := by
  have hL := eval_lhsPolyInv env d
  have hT := eval_targetPolyInv env T
  have hkey : Expression.eval env (lhsPolyInv d)
      - Expression.eval env (targetPolyInv T)
      = ((q0 : ℕ) : F circomPrime) * ((P256 : ℕ) : F circomPrime) := by
    rw [hL, hT, hid]
    push_cast
    ring
  have hinv : (((P256 : ℕ) : F circomPrime))⁻¹
      * ((P256 : ℕ) : F circomPrime) = 1 := inv_mul_cancel₀ P256_cast_ne_zero
  simp only [qInv, Expression.eval]
  linear_combination (((P256 : ℕ) : F circomPrime))⁻¹ * hkey
    + ((q0 : ℕ) : F circomPrime) * hinv

/-- The deleted native row holds identically for the inverted quotient. -/
lemma qInv_linIdent (env : Environment (F circomPrime))
    (d : Vector (Expression (F circomPrime)) numLimbs) (T : Var TVec (F circomPrime)) :
    GroupedEqXV.LinIdent 64
      { lhs := Vector.map (Expression.eval env) (foldLhsC d),
        rhs := Vector.map (Expression.eval env) (foldRhsT (qInv d T) T) } := by
  have hQ := qInv_mul_P256 env d T
  have hR := eval_foldRhsT_poly env (qInv d T) T
  simp only [GroupedEqXV.LinIdent, Vector.getElem_map]
  rw [← polyEvalExpr_eval env (foldLhsC d),
    ← polyEvalExpr_eval env (foldRhsT (qInv d T) T)]
  change Expression.eval env (lhsPolyInv d) = _
  rw [hR]
  exact eq_add_of_sub_eq hQ.symm

lemma lhsPolyInv_stable {E1 E2 : Environment (F circomPrime)}
    (d : Vector (Expression (F circomPrime)) numLimbs)
    (hd : ∀ (i : ℕ) (hi : i < numLimbs),
      Expression.eval E1 (d[i]'hi) = Expression.eval E2 (d[i]'hi)) :
    Expression.eval E1 (lhsPolyInv d) = Expression.eval E2 (lhsPolyInv d) := by
  have hL := foldLhsC_stable (E1 := E1) (E2 := E2) d hd
  have hLi : ∀ (i : ℕ) (hi : i < numLimbs),
      Expression.eval E1 ((foldLhsC d)[i]'hi)
        = Expression.eval E2 ((foldLhsC d)[i]'hi) := by
    intro i hi
    simpa only [Vector.getElem_map] using
      congrArg (fun v : Vector (F circomPrime) numLimbs => v[i]'hi) hL
  simp only [lhsPolyInv, polyEvalExpr_eval]
  apply Finset.sum_congr rfl
  intro i _
  rw [hLi i.val i.isLt]

lemma targetPolyInv_stable {E1 E2 : Environment (F circomPrime)}
    (T : Var TVec (F circomPrime))
    (ht : ∀ (i : ℕ) (hi : i < 2 * numLimbs - 1),
      Expression.eval E1 (T[i]'hi) = Expression.eval E2 (T[i]'hi)) :
    Expression.eval E1 (targetPolyInv T) = Expression.eval E2 (targetPolyInv T) := by
  rw [eval_targetPolyInv_expanded, eval_targetPolyInv_expanded]
  rw [ht 0 (by decide), ht 1 (by decide), ht 2 (by decide), ht 3 (by decide),
    ht 4 (by decide), ht 5 (by decide), ht 6 (by decide)]

lemma qInv_stable {E1 E2 : Environment (F circomPrime)}
    (d : Vector (Expression (F circomPrime)) numLimbs) (T : Var TVec (F circomPrime))
    (hd : ∀ (i : ℕ) (hi : i < numLimbs),
      Expression.eval E1 (d[i]'hi) = Expression.eval E2 (d[i]'hi))
    (ht : ∀ (i : ℕ) (hi : i < 2 * numLimbs - 1),
      Expression.eval E1 (T[i]'hi) = Expression.eval E2 (T[i]'hi)) :
    Expression.eval E1 (qInv d T) = Expression.eval E2 (qInv d T) := by
  simp only [qInv, Expression.eval]
  rw [lhsPolyInv_stable d hd, targetPolyInv_stable T ht]

def mainInv (input : Var Inputs (F circomPrime)) : Circuit (F circomPrime) Unit := do
  let d ← CrtMul.crtMul input.a input.b
  assertion (RangeCheck.circuit qBitsFoldT (by decide) (by decide))
    (qInv d input.target)
  assertion
    (GroupedEqXV.circuitNoTop 64 gfFold posOfFold 3 vFoldTL vFoldTR hgvFoldT (by norm_num))
    { lhs := foldLhsC d, rhs := foldRhsT (qInv d input.target) input.target }

instance elaboratedInv : ElaboratedCircuit (F circomPrime) Inputs unit mainInv where
  localLength _ := 171
  localLength_eq := by
    intro input offset
    simp only [mainInv, CrtMul.crtMul, circuit_norm, RangeCheck.circuit,
      GroupedEqXV.circuitNoTop, GroupedEqXV.elaboratedNoTop, vFoldTL, wfFoldT,
      GroupedEqXV.widthAllocFrom, qBitsFoldT, numLimbs]
  subcircuitsConsistent := by
    intro input offset
    simp +arith only [mainInv, CrtMul.crtMul, circuit_norm, RangeCheck.circuit,
      GroupedEqXV.circuitNoTop, GroupedEqXV.elaboratedNoTop]
  channelsLawful := by
    intro offset
    simp only [mainInv, CrtMul.crtMul, circuit_norm, RangeCheck.circuit,
      GroupedEqXV.circuitNoTop, GroupedEqXV.elaboratedNoTop]

attribute [local irreducible] CrtMul.crtMul RangeCheck.circuit
  GroupedEqXV.circuitNoTop GroupedEqXV.mainNoTop
  qInv lhsPolyInv targetPolyInv

set_option maxHeartbeats 8000000 in
theorem soundnessInv (Ca Cb Nt Nt5 : ℕ)
    (hcap : numLimbs * (Ca * Cb) ≤ 12 * 2 ^ 128)
    (hcapT : Nt ≤ 12 * 2 ^ 128) (hNt5 : Nt5 ≤ 6 * 2 ^ 128) :
    FormalAssertion.Soundness (F circomPrime) mainInv (Assumptions Ca Cb Nt Nt5) Spec := by
  circuit_proof_start [mainInv, RangeCheck.circuit, RangeCheck.Assumptions, RangeCheck.Spec,
    GroupedEqXV.circuitNoTop, GroupedEqXV.elaboratedNoTop,
    GroupedEqXV.AssumptionsNoTop, GroupedEqXV.Assumptions, GroupedEqX.Spec]
  obtain ⟨hAB_ops, hq_lt, h_eq_impl⟩ := h_holds
  obtain ⟨ha_lt, hb_lt, ht_lt, ht5⟩ := h_assumptions
  obtain ⟨ha_in, hb_in, ht_in⟩ := h_input
  refine ⟨?_, CrtMul.crtMul_requirements _ _ _ _⟩
  simp only [vFoldTL, vFoldTR] at h_eq_impl
  have hd := CrtMul.crtMul_eval_bridge env i₀ input_var_a input_var_b
    (CrtMul.crtMul_soundness i₀ input_var_a input_var_b env hAB_ops)
  have ha_lt' : ∀ i : Fin numLimbs,
      (Expression.eval env (input_var_a[i.val]'i.isLt)).val < Ca := by
    intro i
    rw [show Expression.eval env (input_var_a[i.val]'i.isLt) = input_a[i.val] from by
      rw [← ha_in]; simp only [Vector.getElem_map]]
    exact ha_lt i
  have hb_lt' : ∀ i : Fin numLimbs,
      (Expression.eval env (input_var_b[i.val]'i.isLt)).val < Cb := by
    intro i
    rw [show Expression.eval env (input_var_b[i.val]'i.isLt) = input_b[i.val] from by
      rw [← hb_in]; simp only [Vector.getElem_map]]
    exact hb_lt i
  have ht_lt' : ∀ k : Fin (2 * numLimbs - 1),
      (Expression.eval env (input_var_target[k.val]'k.isLt)).val < Nt := by
    intro k
    rw [show Expression.eval env (input_var_target[k.val]'k.isLt) = input_target[k.val] from by
      rw [← ht_in]; simp only [Vector.getElem_map]]
    exact ht_lt k
  have hNbp : numLimbs * (Ca * Cb) < circomPrime := by
    have h1 : numLimbs * (Ca * Cb) ≤ numLimbs * (Ca * Cb) * (1 + cFold) :=
      Nat.le_mul_of_pos_right _ (by omega)
    have h2 : (2 : ℕ) ^ 166 < circomPrime := by decide
    omega
  have hPv : ∀ k : Fin (2 * numLimbs - 1),
      (Expression.eval env (bigIntMulNoReduce input_var_a input_var_b)[k.val]).val
        < numLimbs * (Ca * Cb) :=
    fun k => MulModTargetW2.val_coeff_lt_gen2 env input_var_a input_var_b k ha_lt' hb_lt' hNbp
  have hqv : (Expression.eval env
      (qInv (CrtMul.crtMul input_var_a input_var_b i₀).1 input_var_target)).val < 2 ^ 69 :=
    hq_lt
  have ht5' : (Expression.eval env (input_var_target[5]'(by decide))).val < Nt5 := by
    rw [show Expression.eval env (input_var_target[5]'(by decide)) = input_target[5] from by
      rw [← ht_in]; simp only [Vector.getElem_map]]
    exact ht5
  have hPv5 : (Expression.eval env (bigIntMulNoReduce input_var_a input_var_b)[5]).val
      < 2 * (Ca * Cb) :=
    coeff5_lt env input_var_a input_var_b ha_lt' hb_lt' hNbp
  have heq := h_eq_impl
    ⟨⟨fun k => by
        rw [foldLhsC_eval_eq env input_var_a input_var_b _ hd k.val k.isLt]
        exact foldLhsT_boundN env _ (numLimbs * (Ca * Cb)) (2 * (Ca * Cb)) hPv hPv5
          (cap_lhsT hcap) (cap_lhsT5 hcap (le_refl _)) k,
      foldRhsT_boundN env _ input_var_target Nt Nt5 hqv ht_lt' ht5' (cap_lhsT hcapT)
        (cap_rhsT5 hcapT hNt5)⟩,
     qInv_linIdent env (CrtMul.crtMul input_var_a input_var_b i₀).1 input_var_target⟩
  rw [foldLhsC_map_eq env input_var_a input_var_b _ hd,
    foldLhsT_polyValue env _ (numLimbs * (Ca * Cb)) hPv (cap_lhsT hcap),
    foldRhsT_polyValue env _ input_var_target Nt hqv ht_lt' (cap_lhsT hcapT),
    foldDNatTOf_eq env input_var_a input_var_b ha_lt' hb_lt' hNbp _ (fun _ => rfl)] at heq
  have hid := foldDNatT_identity env input_var_a input_var_b ha_lt' hb_lt' hNbp
  rw [ha_in, hb_in] at hid
  have hidT := foldRTNat_identity env input_var_target
  rw [ht_in] at hidT
  exact targetT_congr hid hidT heq

set_option maxHeartbeats 8000000 in
theorem completenessInv (Ca Cb Nt Nt5 : ℕ)
    (hcap : numLimbs * (Ca * Cb) ≤ 12 * 2 ^ 128)
    (hcapT : Nt ≤ 12 * 2 ^ 128) (hNt : Nt ≤ 12 * 2 ^ 128) (hNt5 : Nt5 ≤ 6 * 2 ^ 128) :
    FormalAssertion.Completeness (F circomPrime) mainInv (Assumptions Ca Cb Nt Nt5) Spec := by
  circuit_proof_start [mainInv, RangeCheck.circuit, RangeCheck.Assumptions, RangeCheck.Spec,
    GroupedEqXV.circuitNoTop, GroupedEqXV.elaboratedNoTop,
    GroupedEqXV.AssumptionsNoTop, GroupedEqXV.Assumptions, GroupedEqX.Spec]
  have hAB_uses := h_env
  obtain ⟨ha_lt, hb_lt, ht_lt, ht5⟩ := h_assumptions
  obtain ⟨ha_in, hb_in, ht_in⟩ := h_input
  simp only [vFoldTL, vFoldTR]
  have ha_lt' : ∀ i : Fin numLimbs,
      (Expression.eval env.toEnvironment (input_var_a[i.val]'i.isLt)).val < Ca := by
    intro i
    rw [show Expression.eval env.toEnvironment (input_var_a[i.val]'i.isLt) = input_a[i.val] from by
      rw [← ha_in]; simp only [Vector.getElem_map]]
    exact ha_lt i
  have hb_lt' : ∀ i : Fin numLimbs,
      (Expression.eval env.toEnvironment (input_var_b[i.val]'i.isLt)).val < Cb := by
    intro i
    rw [show Expression.eval env.toEnvironment (input_var_b[i.val]'i.isLt) = input_b[i.val] from by
      rw [← hb_in]; simp only [Vector.getElem_map]]
    exact hb_lt i
  have ht_lt' : ∀ k : Fin (2 * numLimbs - 1),
      (Expression.eval env.toEnvironment (input_var_target[k.val]'k.isLt)).val < Nt := by
    intro k
    rw [show Expression.eval env.toEnvironment (input_var_target[k.val]'k.isLt)
        = input_target[k.val] from by rw [← ht_in]; simp only [Vector.getElem_map]]
    exact ht_lt k
  have hNbp : numLimbs * (Ca * Cb) < circomPrime := by
    have h1 : numLimbs * (Ca * Cb) ≤ numLimbs * (Ca * Cb) * (1 + cFold) :=
      Nat.le_mul_of_pos_right _ (by omega)
    have h2 : (2 : ℕ) ^ 166 < circomPrime := by decide
    omega
  have h_pvAB := CrtMul.crtMul_usesLocalWitnesses i₀ i₀ input_var_a input_var_b env rfl hAB_uses
  have hd := CrtMul.crtMul_eval_bridge_uses env.toEnvironment i₀
    input_var_a input_var_b h_pvAB
  have hPv : ∀ k : Fin (2 * numLimbs - 1),
      (Expression.eval env.toEnvironment (bigIntMulNoReduce input_var_a input_var_b)[k.val]).val
        < numLimbs * (Ca * Cb) :=
    fun k => MulModTargetW2.val_coeff_lt_gen2 env.toEnvironment input_var_a input_var_b k
      ha_lt' hb_lt' hNbp
  set D := foldDNatT env.toEnvironment input_var_a input_var_b with hDdef
  set RT := foldRTNat env.toEnvironment input_var_target with hRTdef
  have hDge : kOffT * P256 ≤ D := foldDNatT_ge env.toEnvironment input_var_a input_var_b
  have hRTle : RT ≤ kOffT * P256 :=
    foldRTNat_lt_offset env.toEnvironment input_var_target Nt ht_lt' hNt
  have hDlt : D < 29 * 2 ^ 320 := foldDNatT_lt env.toEnvironment input_var_a input_var_b
    ha_lt' hb_lt' hcap
  have hid := foldDNatT_identity env.toEnvironment input_var_a input_var_b ha_lt' hb_lt' hNbp
  rw [ha_in, hb_in] at hid
  have hidT := foldRTNat_identity env.toEnvironment input_var_target
  rw [ht_in] at hidT
  have hDmod : D % P256 = RT % P256 := foldD_mod_T hid hidT h_spec
  have hqlt : (D - RT) / P256 < 2 ^ 69 := by
    have hp : P256 = 2 ^ 256 - 2 ^ 32 - 977 := by decide
    have hdiv : (D - RT) / P256 ≤ D / P256 := Nat.div_le_div_right (by omega)
    have : D / P256 < 2 ^ 69 := by
      apply Nat.div_lt_of_lt_mul
      calc D < 29 * 2 ^ 320 := hDlt
        _ ≤ 2 ^ 69 * P256 := by rw [hp]; norm_num
    omega
  have hzero : (Expression.eval env.toEnvironment
      (0 : Expression (F circomPrime))).val < 2 ^ 69 := by
    simp only [Expression.eval, ZMod.val_zero]
    norm_num
  have hRTpoly : polyValue 64 (Vector.map (Expression.eval env.toEnvironment)
      (foldRhsT 0 input_var_target)) = RT := by
    rw [foldRhsT_polyValue env.toEnvironment 0 input_var_target Nt hzero ht_lt'
      (cap_lhsT hcapT)]
    have h0 : (Expression.eval env.toEnvironment (0 : Expression (F circomPrime))) = 0 := rfl
    rw [h0, ZMod.val_zero, zero_mul, zero_add]
  have hDpoly : polyValue 64 (Vector.map (Expression.eval env.toEnvironment)
      (foldLhsC (CrtMul.crtMul input_var_a input_var_b i₀).1)) = D := by
    rw [foldLhsC_map_eq env.toEnvironment input_var_a input_var_b _ hd,
      foldLhsT_polyValue env.toEnvironment _ (numLimbs * (Ca * Cb)) hPv (cap_lhsT hcap),
      foldDNatTOf_eq env.toEnvironment input_var_a input_var_b ha_lt' hb_lt' hNbp _
        (fun _ => rfl)]
  have hreconstruct : (D - RT) / P256 * P256 + RT = D :=
    quot_reconstruct (by omega) hDmod
  have hqeval := eval_qInv_of_identity env.toEnvironment
    (CrtMul.crtMul input_var_a input_var_b i₀).1 input_var_target ((D - RT) / P256)
    (by rw [hDpoly, hRTpoly]; exact hreconstruct.symm)
  have hqval : (Expression.eval env.toEnvironment
      (qInv (CrtMul.crtMul input_var_a input_var_b i₀).1 input_var_target)).val
        = (D - RT) / P256 := by
    rw [hqeval, ZMod.val_natCast_of_lt]
    have : (2 : ℕ) ^ 72 < circomPrime := by decide
    omega
  have hqvar : (Expression.eval env.toEnvironment
      (qInv (CrtMul.crtMul input_var_a input_var_b i₀).1 input_var_target)).val < 2 ^ 69 := by
    rw [hqval]; exact hqlt
  have ht5' : (Expression.eval env.toEnvironment
      (input_var_target[5]'(by decide))).val < Nt5 := by
    rw [show Expression.eval env.toEnvironment (input_var_target[5]'(by decide))
        = input_target[5] from by rw [← ht_in]; simp only [Vector.getElem_map]]
    exact ht5
  have hPv5 : (Expression.eval env.toEnvironment
      (bigIntMulNoReduce input_var_a input_var_b)[5]).val < 2 * (Ca * Cb) :=
    coeff5_lt env.toEnvironment input_var_a input_var_b ha_lt' hb_lt' hNbp
  refine ⟨CrtMul.crtMul_completeness i₀ input_var_a input_var_b env h_pvAB,
    by rw [hqval]; exact hqlt,
    ⟨⟨fun k => by
        rw [foldLhsC_eval_eq env.toEnvironment input_var_a input_var_b _ hd k.val k.isLt]
        exact foldLhsT_boundN env.toEnvironment _ (numLimbs * (Ca * Cb)) (2 * (Ca * Cb)) hPv hPv5
          (cap_lhsT hcap) (cap_lhsT5 hcap (le_refl _)) k,
      foldRhsT_boundN env.toEnvironment _ input_var_target Nt Nt5 hqvar ht_lt' ht5'
        (cap_lhsT hcapT) (cap_rhsT5 hcapT hNt5)⟩,
     qInv_linIdent env.toEnvironment
       (CrtMul.crtMul input_var_a input_var_b i₀).1 input_var_target⟩, ?_⟩
  rw [foldLhsC_map_eq env.toEnvironment input_var_a input_var_b _ hd,
    foldLhsT_polyValue env.toEnvironment _ (numLimbs * (Ca * Cb)) hPv (cap_lhsT hcap),
    foldRhsT_polyValue env.toEnvironment _ input_var_target Nt hqvar ht_lt' (cap_lhsT hcapT),
    foldDNatTOf_eq env.toEnvironment input_var_a input_var_b ha_lt' hb_lt' hNbp _ (fun _ => rfl)]
  show D = (Expression.eval env.toEnvironment
    (qInv (CrtMul.crtMul input_var_a input_var_b i₀).1 input_var_target)).val * P256 + RT
  rw [hqval]
  exact hreconstruct.symm

def circuitInv (Ca Cb Nt Nt5 : ℕ)
    (hcap : numLimbs * (Ca * Cb) ≤ 12 * 2 ^ 128)
    (hcapT : Nt ≤ 12 * 2 ^ 128) (hNt : Nt ≤ 12 * 2 ^ 128) (hNt5 : Nt5 ≤ 6 * 2 ^ 128) :
    FormalAssertion (F circomPrime) Inputs where
  main := mainInv
  Assumptions := Assumptions Ca Cb Nt Nt5
  Spec := Spec
  soundness := soundnessInv Ca Cb Nt Nt5 hcap hcapT hNt5
  completeness := completenessInv Ca Cb Nt Nt5 hcap hcapT hNt hNt5

set_option maxHeartbeats 4000000 in
theorem computableWitnessesInv (Ca Cb Nt Nt5 : ℕ)
    (hcap : numLimbs * (Ca * Cb) ≤ 12 * 2 ^ 128)
    (hcapT : Nt ≤ 12 * 2 ^ 128) (hNt : Nt ≤ 12 * 2 ^ 128) (hNt5 : Nt5 ≤ 6 * 2 ^ 128) :
    (circuitInv Ca Cb Nt Nt5 hcap hcapT hNt hNt5).ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition
      input env env') ((mainInv input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold mainInv
  let pcOff := offset
  let pcv := (CrtMul.crtMul input.a input.b).output pcOff
  let qv := qInv pcv input.target
  let rcOff := pcOff + (CrtMul.crtMul input.a input.b).localLength pcOff
  let rcc : Circuit (F circomPrime) Unit :=
    assertion (RangeCheck.circuit qBitsFoldT (by decide) (by decide)) qv
  let eqOff := rcOff + rcc.localLength rcOff
  have h_pclen : (CrtMul.crtMul input.a input.b).localLength pcOff = numLimbs :=
    CrtMul.crtMul_localLength pcOff input.a input.b
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_structuralComputableWitnesses_iff]
  and_intros
  · exact CrtMul.crtMul_structuralComputableWitnesses input input.a input.b pcOff
      (by
        intro k e1 e2 _ _ h_input
        have ha : eval e1 input.a = eval e2 input.a := by
          simpa [circuit_norm] using congrArg (fun x : Inputs (F circomPrime) => x.a) h_input
        have hb : eval e1 input.b = eval e2 input.b := by
          simpa [circuit_norm] using congrArg (fun x : Inputs (F circomPrime) => x.b) h_input
        exact ⟨ha, hb⟩)
      env env'
  · exact Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
      (RangeCheck.circuit qBitsFoldT (by decide) (by decide)) input qv rcOff
      (by
        intro k e1 e2 hle h_agree h_input
        have hk_pc : pcOff + numLimbs ≤ k := by
          dsimp only [rcOff] at hle
          rw [h_pclen] at hle
          exact hle
        have hPc : Vector.map (Expression.eval e1.toEnvironment) pcv
            = Vector.map (Expression.eval e2.toEnvironment) pcv :=
          CrtMul.crtMul_output_stable pcOff input.a input.b h_agree hk_pc
        have hPc_i : ∀ (i : ℕ) (hi : i < numLimbs),
            Expression.eval e1.toEnvironment (pcv[i]'hi)
              = Expression.eval e2.toEnvironment (pcv[i]'hi) := by
          intro i hi
          simpa only [Vector.getElem_map] using
            congrArg (fun v : Vector (F circomPrime) numLimbs => v[i]'hi) hPc
        have ht : eval e1 input.target = eval e2 input.target := by
          simpa [circuit_norm] using
            congrArg (fun x : Inputs (F circomPrime) => x.target) h_input
        have ht_i : ∀ (i : ℕ) (hi : i < 2 * numLimbs - 1),
            Expression.eval e1.toEnvironment (input.target[i]'hi)
              = Expression.eval e2.toEnvironment (input.target[i]'hi) :=
          fun i hi => tvec_getElem_eval_eq ht i hi
        simpa only [qv, circuit_norm] using qInv_stable pcv input.target hPc_i ht_i)
      (RangeCheck.computableWitnesses qBitsFoldT (by decide) (by decide)) env env'
  · exact Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
      (GroupedEqXV.circuitNoTop 64 gfFold posOfFold 3 vFoldTL vFoldTR hgvFoldT (by norm_num))
      input { lhs := foldLhsC pcv, rhs := foldRhsT qv input.target } eqOff
      (by
        intro k e1 e2 hle h_agree h_input
        have hk_pc : pcOff + numLimbs ≤ k := by
          dsimp only [eqOff, rcOff] at hle
          rw [h_pclen] at hle
          omega
        have hPc : Vector.map (Expression.eval e1.toEnvironment) pcv
            = Vector.map (Expression.eval e2.toEnvironment) pcv :=
          CrtMul.crtMul_output_stable pcOff input.a input.b h_agree hk_pc
        have hPc_i : ∀ (i : ℕ) (hi : i < numLimbs),
            Expression.eval e1.toEnvironment (pcv[i]'hi)
              = Expression.eval e2.toEnvironment (pcv[i]'hi) := by
          intro i hi
          simpa only [Vector.getElem_map] using
            congrArg (fun v : Vector (F circomPrime) numLimbs => v[i]'hi) hPc
        have ht : eval e1 input.target = eval e2 input.target := by
          simpa [circuit_norm] using
            congrArg (fun x : Inputs (F circomPrime) => x.target) h_input
        have ht_i : ∀ (i : ℕ) (hi : i < 2 * numLimbs - 1),
            Expression.eval e1.toEnvironment (input.target[i]'hi)
              = Expression.eval e2.toEnvironment (input.target[i]'hi) :=
          fun i hi => tvec_getElem_eval_eq ht i hi
        have hq := qInv_stable pcv input.target hPc_i ht_i
        have hL := foldLhsC_stable
          (E1 := e1.toEnvironment) (E2 := e2.toEnvironment) pcv hPc_i
        have hR := foldRhsT_stable
          (E1 := e1.toEnvironment) (E2 := e2.toEnvironment)
          qv input.target hq ht_i
        simp only [circuit_norm]
        rw [hL, hR])
      (GroupedEqXV.computableWitnessesNoTop 64 gfFold posOfFold 3
        vFoldTL vFoldTR hgvFoldT (by norm_num))
      env env'

end MulModFoldT
end Solution.Secp256k1ScalarMul
