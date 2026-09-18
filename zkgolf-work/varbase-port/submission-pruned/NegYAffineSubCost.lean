import Solution.Secp256k1ScalarMul.NegYAffineCost

namespace Solution.Secp256k1ScalarMul
namespace NegYAffine
namespace CostCert

open Challenge.CostR1CS
open Solution.Secp256k1ScalarMul.Cost

theorem costIs_sub (P : Var FlaggedPoint (F circomPrime)) :
    CostIs (subcircuit circuit P) cost :=
  CostIs.subcircuit fun n => costIs P n

theorem isR1CS_sub (P : Var FlaggedPoint (F circomPrime)) (hP : AffineFP P) :
    IsR1CSCirc (subcircuit circuit P) :=
  IsR1CSCirc.subcircuit fun n => isR1CS P hP n

theorem affineW_sub (P : Var FlaggedPoint (F circomPrime)) (n : ℕ)
    (hP : AffineFP P) : AffineW ((subcircuit circuit P).output n) := by
  simpa only [subcircuit, circuit, elaborated] using affineW_output P n hP

end CostCert
end NegYAffine
end Solution.Secp256k1ScalarMul
