import Solution.Secp256k1ScalarMul.GLVScalarMulCostCWBase

namespace Solution.Secp256k1ScalarMul

local notation "CF" => F circomPrime

namespace Cost

open Challenge.CostR1CS

attribute [local irreducible] isR1CSRow r1csProducts operationsIsR1CS flatOperationsIsR1CS

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
theorem isR1CS_glvTable
    (input : Var ScalarMul.Inputs CF)
    (hpx : AffineW input.px) (hpy : AffineW input.py) (offset : ℕ) :
    operationsIsR1CS (glvTableOps input offset) := by
  have hP : AffineFP (glvTableInput input offset).P := by
    dsimp only [glvTableInput, GLVScalarMul.inputPointVar]
    exact ⟨hpx, hpy, Affine.const 0⟩
  have hQ : AffineFP (glvTableInput input offset).Q := by
    simpa only [glvTableInput, glvTableQ] using
      affine_resultWitness input offset
  have hc :
      (Affine (glvTableCoefficients input offset).u1.sign ∧
        AffineW (glvTableCoefficients input offset).u1.bits) ∧
      (Affine (glvTableCoefficients input offset).u2.sign ∧
        AffineW (glvTableCoefficients input offset).u2.bits) ∧
      (Affine (glvTableCoefficients input offset).v1.sign ∧
        AffineW (glvTableCoefficients input offset).v1.bits) ∧
      (Affine (glvTableCoefficients input offset).v2.sign ∧
        AffineW (glvTableCoefficients input offset).v2.bits) := by
    simpa only [glvTableCoefficients] using
      affine_coefficientWitness input (glvIC offset)
  have hs0 : Affine (glvTableInput input offset).sign0 := by
    dsimp only [glvTableInput]
    exact hc.1.1
  have hs1 : Affine (glvTableInput input offset).sign1 := by
    dsimp only [glvTableInput]
    exact hc.2.1.1
  have hs2 : Affine (glvTableInput input offset).sign2 := by
    dsimp only [glvTableInput]
    exact hc.2.2.1.1
  have hs3 : Affine (glvTableInput input offset).sign3 := by
    dsimp only [glvTableInput]
    exact hc.2.2.2.1
  unfold glvTableOps
  exact isR1CS_tableOpsExact (glvTableInput input offset) hP hQ
    hs0 hs1 hs2 hs3 (glvITable offset)

end Cost
end Solution.Secp256k1ScalarMul
