import Solution.Secp256k1ScalarMul.NegYAffine
import Solution.Secp256k1ScalarMul.Cost

namespace Solution.Secp256k1ScalarMul
namespace NegYAffine
namespace CostCert

open Challenge.CostR1CS
open Solution.Secp256k1ScalarMul.Cost
attribute [local irreducible] isR1CSRow r1csProducts operationsIsR1CS flatOperationsIsR1CS

def cost : Count := ⟨68, 69⟩

theorem costIs (P : Var FlaggedPoint (F circomPrime)) :
    CostIs (main P) cost := by
  rw [show cost = ⟨1, 0⟩ + (⟨1, 0⟩ + (⟨1, 0⟩ + (⟨1, 0⟩ + (⟨1, 0⟩ +
      (⟨0, 1⟩ + (⟨0, 1⟩ + (⟨0, 1⟩ + (⟨0, 1⟩ + (⟨0, 1⟩ +
      (⟨63, 64⟩ + Count.zero)))))))))) from by decide]
  unfold main
  refine CostIs.bind (CostIs.witnessField _) fun _ => ?_
  refine CostIs.bind (CostIs.witnessField _) fun _ => ?_
  refine CostIs.bind (CostIs.witnessField _) fun _ => ?_
  refine CostIs.bind (CostIs.witnessField _) fun _ => ?_
  refine CostIs.bind (CostIs.witnessField _) fun _ => ?_
  refine CostIs.bind (CostIs.assertZero _) fun _ => ?_
  refine CostIs.bind (CostIs.assertZero _) fun _ => ?_
  refine CostIs.bind (CostIs.assertZero _) fun _ => ?_
  refine CostIs.bind (CostIs.assertZero _) fun _ => ?_
  refine CostIs.bind (CostIs.assertZero _) fun _ => ?_
  refine CostIs.bind (costIs_assertion_implicitRangeCheck secpParams.B secpParams.hB
    secpParams.hB1 _) fun _ => CostIs.pure _

private lemma affine_result (P : Var FlaggedPoint (F circomPrime))
    (c0 c1 c2 : Expression (F circomPrime)) (hP : AffineFP P)
    (hc0 : Affine c0) (hc1 : Affine c1) (hc2 : Affine c2) :
    AffineW (result P c0 c1 c2) := by
  intro i hi
  interval_cases i
  · exact Affine.sub
      (Affine.add
        (Affine.mul_fconst _ (Affine.sub (Affine.const 1) hP.2.2))
        (Affine.fconst_mul _ hc0))
      (hP.2.1 0 (by decide))
  · exact Affine.sub
      (Affine.sub
        (Affine.add
          (Affine.mul_fconst _ (Affine.sub (Affine.const 1) hP.2.2))
          (Affine.fconst_mul _ hc1))
        (hP.2.1 1 (by decide)))
      hc0
  · exact Affine.sub
      (Affine.sub
        (Affine.add
          (Affine.mul_fconst _ (Affine.sub (Affine.const 1) hP.2.2))
          (Affine.fconst_mul _ hc2))
        (hP.2.1 2 (by decide)))
      hc1
  · exact Affine.sub
      (Affine.sub
        (Affine.mul_fconst _ (Affine.sub (Affine.const 1) hP.2.2))
        (hP.2.1 3 (by decide)))
      hc2

private lemma affine_d1 (P : Var FlaggedPoint (F circomPrime))
    (c0 : Expression (F circomPrime)) (hP : AffineFP P) (hc0 : Affine c0) :
    Affine (d1Expr P c0) :=
  Affine.sub (Affine.add (hP.2.1 1 (by decide)) hc0) (Affine.const _)

private lemma affine_d2 (P : Var FlaggedPoint (F circomPrime))
    (c1 : Expression (F circomPrime)) (hP : AffineFP P) (hc1 : Affine c1) :
    Affine (d2Expr P c1) :=
  Affine.sub (Affine.add (hP.2.1 2 (by decide)) hc1) (Affine.const _)

theorem isR1CS (P : Var FlaggedPoint (F circomPrime)) (hP : AffineFP P) :
    IsR1CSCirc (main P) := by
  unfold main
  refine IsR1CSCirc.bind_out (IsR1CSCirc.witnessField _) fun _ => ?_
  refine IsR1CSCirc.bind_out (IsR1CSCirc.witnessField _) fun _ => ?_
  refine IsR1CSCirc.bind_out (IsR1CSCirc.witnessField _) fun _ => ?_
  refine IsR1CSCirc.bind_out (IsR1CSCirc.witnessField _) fun _ => ?_
  refine IsR1CSCirc.bind_out (IsR1CSCirc.witnessField _) fun _ => ?_
  refine IsR1CSCirc.bind (IsR1CSCirc.assertZero
    (isR1CSRow_mul (Affine.var _) (Affine.sub (Affine.var _) (Affine.const 1)))) fun _ => ?_
  refine IsR1CSCirc.bind (IsR1CSCirc.assertZero
    (isR1CSRow_add_mul (Affine.sub (Affine.var _) (Affine.const 1))
      (affine_d1 P _ hP (Affine.var _)) (Affine.var _))) fun _ => ?_
  refine IsR1CSCirc.bind (IsR1CSCirc.assertZero
    (isR1CSRow_mul (affine_d1 P _ hP (Affine.var _)) (Affine.var _))) fun _ => ?_
  refine IsR1CSCirc.bind (IsR1CSCirc.assertZero
    (isR1CSRow_add_mul (Affine.sub (Affine.var _) (Affine.const 1))
      (affine_d2 P _ hP (Affine.var _)) (Affine.var _))) fun _ => ?_
  refine IsR1CSCirc.bind (IsR1CSCirc.assertZero
    (isR1CSRow_mul (affine_d2 P _ hP (Affine.var _)) (Affine.var _))) fun _ => ?_
  refine IsR1CSCirc.bind (isR1CS_assertion_implicitRangeCheck secpParams.B secpParams.hB
    secpParams.hB1 _ (affine_result P _ _ _ hP (Affine.var _) (Affine.var _) (Affine.var _)
      0 (by decide))) fun _ => IsR1CSCirc.pure _

theorem affineW_output (P : Var FlaggedPoint (F circomPrime)) (n : ℕ)
    (hP : AffineFP P) : AffineW ((main P).output n) := by
  simpa only [main, circuit_norm] using
    (affine_result P _ _ _ hP (Affine.var _) (Affine.var _) (Affine.var _))

end CostCert
end NegYAffine
end Solution.Secp256k1ScalarMul
