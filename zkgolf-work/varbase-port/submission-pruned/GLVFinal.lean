import Solution.Secp256k1ScalarMul.JacobianCert
import Solution.Secp256k1ScalarMul.GLVAlgebra

namespace Solution.Secp256k1ScalarMul.GLVFinal

open Specs.Secp256k1

lemma jacobian_gPoint_eq :
    Bridge.mkPoint G JacobianCert.G_onCurve = ProofBlocker.gPoint := by
  rfl

lemma jacobian_phiPoint_eq' :
    Bridge.mkPoint JacobianCert.PhiG JacobianCert.PhiG_onCurve =
      Phi.hom (Bridge.mkPoint G JacobianCert.G_onCurve) := by
  rfl

lemma latticeA_eq : GLVAlgebra.latticeA = JacobianCert.a := by rfl
lemma latticeB_eq : GLVAlgebra.latticeB = JacobianCert.bAbs := by rfl

theorem short_relation :
    GLVAlgebra.latticeA • ProofBlocker.gPoint =
      GLVAlgebra.latticeB • Phi.hom ProofBlocker.gPoint := by
  rw [latticeA_eq, latticeB_eq, ← jacobian_gPoint_eq, ← jacobian_phiPoint_eq']
  exact JacobianCert.a_smul_G_eq_b_smul_PhiG

theorem order_nsmul_gPoint : order • ProofBlocker.gPoint = 0 :=
  GLVAlgebra.order_nsmul_of_short_relation ProofBlocker.gPoint short_relation

theorem hom_eq_lambda_nsmul (Q : Bridge.W.Point) :
    Phi.hom Q = GLVAlgebra.lambda • Q :=
  GLVAlgebra.hom_eq_lambda_nsmul_all short_relation Q

theorem order_nsmul_all (Q : Bridge.W.Point) : order • Q = 0 :=
  ProofBlocker.order_nsmul_all order_nsmul_gPoint Q

theorem nsmul_right_injective_of_not_order_dvd {a : ℕ} (ha : ¬ order ∣ a) :
    Function.Injective (fun Q : Bridge.W.Point ↦ a • Q) :=
  ProofBlocker.nsmul_right_injective_of_not_order_dvd order_nsmul_gPoint ha

end Solution.Secp256k1ScalarMul.GLVFinal
