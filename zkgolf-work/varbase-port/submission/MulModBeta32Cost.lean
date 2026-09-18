import Solution.Secp256k1ScalarMul.MulModBeta32
import Solution.Secp256k1ScalarMul.MulModFold32TAInv
import Solution.Secp256k1ScalarMul.PointValidCost
import Solution.Secp256k1ScalarMul.Cost

/-! Cost, R1CS and affinity certificates for `MulModBeta32`. -/

namespace Solution.Secp256k1ScalarMul
namespace Cost

open Challenge.CostR1CS

attribute [local irreducible] isR1CSRow r1csProducts operationsIsR1CS flatOperationsIsR1CS


/-! ## `MulModFold32TA` — the constant-operand fold certificate

Identical to `mulModFold32TCount` minus `interpolatedMul`'s `⟨15, 15⟩`, since a
constant second operand makes the convolution cells affine and they need not be
witnessed. -/

def mulModFold32TACount : Count :=
  ⟨1, 0⟩ + (⟨qBitsFold32T - 1, qBitsFold32T⟩ +
    ⟨GroupedEqXV.widthAllocFrom vFold32TL.Wf (3 - 2) 0,
     GroupedEqXV.widthConsFrom vFold32TL.Wf (3 - 2) 0 + 1⟩)

def mulModFold32TACost : Count := ⟨78, 80⟩

theorem mulModFold32TACount_eq : mulModFold32TACount = mulModFold32TACost := by
  simp only [mulModFold32TACount, mulModFold32TACost, GroupedEqXV.widthAllocFrom,
    GroupedEqXV.widthConsFrom, vFold32TL, wfFold32T]
  rfl

theorem costIs_mulModFold32TA' (input : Var MulModFold32TA.Inputs (F circomPrime)) :
    CostIs (MulModFold32TA.main input) mulModFold32TACount := by
  obtain ⟨a, b, t⟩ := input
  unfold MulModFold32TA.main mulModFold32TACount
  refine CostIs.bind (CostIs.witnessField _) fun q => ?_
  refine CostIs.bind (costIs_assertion_implicitRangeCheck qBitsFold32T (by decide) (by decide) q)
    fun _ => ?_
  exact costIs_assertion_groupedEqXV (L := 8) 32 gfFold32T posOfFold32T 3 vFold32TL vFold32TR
    hgvFold32T (by norm_num) _

theorem costIs_mulModFold32TA (input : Var MulModFold32TA.Inputs (F circomPrime)) :
    CostIs (MulModFold32TA.main input) mulModFold32TACost :=
  mulModFold32TACount_eq ▸ costIs_mulModFold32TA' input

theorem costIs_assertion_mulModFold32TA (Ca Cb : ℕ) (hcap : 8 * (Ca * Cb) ≤ 2 ^ 67)
    (input : Var MulModFold32TA.Inputs (F circomPrime)) :
    CostIs (assertion (MulModFold32TA.circuit Ca Cb hcap) input) mulModFold32TACost :=
  CostIs.assertion (fun n => costIs_mulModFold32TA input n)

theorem isR1CS_mulModFold32TA (input : Var MulModFold32TA.Inputs (F circomPrime))
    (ha : AffineW input.a) (hb : ∀ (j : ℕ) (hj : j < 8), degree (input.b[j]'hj) = 0)
    (ht : AffineW input.target) :
    IsR1CSCirc (MulModFold32TA.main input) := by
  obtain ⟨a, b, t⟩ := input
  unfold MulModFold32TA.main
  refine IsR1CSCirc.bind_out (IsR1CSCirc.witnessField _) fun q => ?_
  refine IsR1CSCirc.bind
    (isR1CS_assertion_implicitRangeCheck qBitsFold32T (by decide) (by decide) _
      (Affine.var _)) fun _ => ?_
  refine isR1CS_assertion_groupedEqXV (L := 8) 32 gfFold32T posOfFold32T 3 vFold32TL vFold32TR
    hgvFold32T (by norm_num) _ ?_ ?_
  · exact affineW_foldLhs32T _ (fun i hi => affineW_bigIntMulNoReduce a b ha hb i hi)
  · exact affineW_foldRhs32T _ t (Affine.var _) ht

theorem isR1CS_assertion_mulModFold32TA (Ca Cb : ℕ) (hcap : 8 * (Ca * Cb) ≤ 2 ^ 67)
    (input : Var MulModFold32TA.Inputs (F circomPrime))
    (ha : AffineW input.a) (hb : ∀ (j : ℕ) (hj : j < 8), degree (input.b[j]'hj) = 0)
    (ht : AffineW input.target) :
    IsR1CSCirc (assertion (MulModFold32TA.circuit Ca Cb hcap) input) :=
  IsR1CSCirc.assertion (fun n => isR1CS_mulModFold32TA input ha hb ht n)

/-! ## Quotient-inverted `MulModFold32TA` -/

def mulModFold32TAInvCount : Count :=
  ⟨qBitsFold32T - 1, qBitsFold32T⟩ +
    ⟨GroupedEqXV.widthAllocFrom vFold32TL.Wf (3 - 2) 0,
     GroupedEqXV.widthConsFrom vFold32TL.Wf (3 - 2) 0⟩

def mulModFold32TAInvCost : Count := ⟨77, 79⟩

theorem mulModFold32TAInvCount_eq : mulModFold32TAInvCount = mulModFold32TAInvCost := by
  simp only [mulModFold32TAInvCount, mulModFold32TAInvCost,
    GroupedEqXV.widthAllocFrom, GroupedEqXV.widthConsFrom, vFold32TL, wfFold32T]
  rfl

theorem costIs_mulModFold32TAInv' (input : Var MulModFold32TA.Inputs (F circomPrime)) :
    CostIs (MulModFold32TA.mainInv input) mulModFold32TAInvCount := by
  obtain ⟨a, b, t⟩ := input
  unfold MulModFold32TA.mainInv mulModFold32TAInvCount
  refine CostIs.bind
    (costIs_assertion_implicitRangeCheck qBitsFold32T (by decide) (by decide) _) fun _ => ?_
  exact costIs_assertion_groupedEqXVNoTop (L := 8) 32 gfFold32T posOfFold32T 3
    vFold32TL vFold32TR hgvFold32T (by norm_num) _

theorem costIs_mulModFold32TAInv (input : Var MulModFold32TA.Inputs (F circomPrime)) :
    CostIs (MulModFold32TA.mainInv input) mulModFold32TAInvCost :=
  mulModFold32TAInvCount_eq ▸ costIs_mulModFold32TAInv' input

theorem costIs_assertion_mulModFold32TAInv (Ca Cb : ℕ)
    (hcap : 8 * (Ca * Cb) ≤ 2 ^ 67)
    (input : Var MulModFold32TA.Inputs (F circomPrime)) :
    CostIs (assertion (MulModFold32TA.circuitInv Ca Cb hcap) input) mulModFold32TAInvCost :=
  CostIs.assertion (fun n => costIs_mulModFold32TAInv input n)

theorem isR1CS_mulModFold32TAInv (input : Var MulModFold32TA.Inputs (F circomPrime))
    (ha : AffineW input.a) (hb : ∀ (j : ℕ) (hj : j < 8), degree (input.b[j]'hj) = 0)
    (ht : AffineW input.target) :
    IsR1CSCirc (MulModFold32TA.mainInv input) := by
  obtain ⟨a, b, t⟩ := input
  unfold MulModFold32TA.mainInv MulModFold32TA.pcOf
  have hPc : ∀ (i : ℕ) (hi : i < 15), Affine ((bigIntMulNoReduce a b)[i]'hi) :=
    fun i hi => affineW_bigIntMulNoReduce a b ha hb i hi
  have hq := affine_qInv (bigIntMulNoReduce a b) hPc t ht
  refine IsR1CSCirc.bind
    (isR1CS_assertion_implicitRangeCheck qBitsFold32T (by decide) (by decide) _ hq) fun _ => ?_
  refine isR1CS_assertion_groupedEqXVNoTop (L := 8) 32 gfFold32T posOfFold32T 3
    vFold32TL vFold32TR hgvFold32T (by norm_num) _ ?_ ?_
  · exact affineW_foldLhs32T _ hPc
  · exact affineW_foldRhs32T _ t hq ht

theorem isR1CS_assertion_mulModFold32TAInv (Ca Cb : ℕ)
    (hcap : 8 * (Ca * Cb) ≤ 2 ^ 67)
    (input : Var MulModFold32TA.Inputs (F circomPrime))
    (ha : AffineW input.a) (hb : ∀ (j : ℕ) (hj : j < 8), degree (input.b[j]'hj) = 0)
    (ht : AffineW input.target) :
    IsR1CSCirc (assertion (MulModFold32TA.circuitInv Ca Cb hcap) input) :=
  IsR1CSCirc.assertion (fun n => isR1CS_mulModFold32TAInv input ha hb ht n)

def mulModBeta32Cost : Count := ⟨341, 344⟩

theorem costIs_mulModBeta32 (input : Var MulModBeta32.Inputs (F circomPrime)) :
    CostIs (MulModBeta32.main input) mulModBeta32Cost := by
  obtain ⟨a⟩ := input
  rw [show mulModBeta32Cost
        = ⟨4, 0⟩ + (⟨260, 265⟩ + (mulModFold32TAInvCost + Count.zero)) from by decide]
  unfold MulModBeta32.main
  refine CostIs.bind (CostIs.provableWitness _) fun r => ?_
  refine CostIs.bind (PointValidCost.costIs_sub_validPBytes _) fun _ => ?_
  refine CostIs.bind (costIs_assertion_mulModFold32TAInv _ _ _ _) fun _ => ?_
  exact CostIs.pure _

theorem costIs_sub_mulModBeta32 (input : Var MulModBeta32.Inputs (F circomPrime)) :
    CostIs (subcircuit MulModBeta32.circuit input) mulModBeta32Cost :=
  CostIs.subcircuit fun n => costIs_mulModBeta32 input n

theorem isR1CS_mulModBeta32 (input : Var MulModBeta32.Inputs (F circomPrime))
    (ha : AffineW input.a) :
    IsR1CSCirc (MulModBeta32.main input) := by
  obtain ⟨a⟩ := input
  unfold MulModBeta32.main
  refine IsR1CSCirc.bind_out (isR1CS_provableWitness_bigInt _) fun nr => ?_
  refine IsR1CSCirc.bind_out
    (PointValidCost.isR1CS_sub_validPBytes _
      (affineW_provableWitness_bigInt _ nr)) fun nb => ?_
  refine IsR1CSCirc.bind
    (isR1CS_assertion_mulModFold32TAInv _ _ _ _
      (Bytes32.affineW_ofBytes
        (PointValidCost.affineW_validPBytes_output _
          (affineW_provableWitness_bigInt _ nr) _))
      (fun i hi => by
        rw [MulModBeta32.betaInvConst32, Vector.getElem_ofFn]; rfl)
      ha)
    fun _ => IsR1CSCirc.pure _

theorem isR1CS_sub_mulModBeta32 (input : Var MulModBeta32.Inputs (F circomPrime))
    (ha : AffineW input.a) :
    IsR1CSCirc (subcircuit MulModBeta32.circuit input) :=
  IsR1CSCirc.subcircuit fun n => isR1CS_mulModBeta32 input ha n

theorem affineW_sub_mulModBeta32 (input : Var MulModBeta32.Inputs (F circomPrime)) (n : ℕ) :
    AffineW ((subcircuit MulModBeta32.circuit input).output n) := by
  simp only [circuit_norm, subcircuit, MulModBeta32.circuit, MulModBeta32.elaborated]
  exact affineW_varFromOffset _ _

end Cost
end Solution.Secp256k1ScalarMul
