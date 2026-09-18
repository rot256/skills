import Solution.Secp256k1ScalarMul.NegYAffineSoundness
import Solution.Secp256k1ScalarMul.NegYAffineCompleteness

/-!
# Affine secp256k1 point negation

For a finite point the circuit returns `p - y`; for the canonical infinity
encoding it returns zero.  Its trusted assumption explicitly includes
`isInf = 1 -> y = 0`, because ordinary `FlaggedPoint.Valid` deliberately does
not canonicalize infinity coordinates.
-/

namespace Solution.Secp256k1ScalarMul
namespace NegYAffine

def circuit : FormalCircuit (F circomPrime) FlaggedPoint Emu where
  main; elaborated; Assumptions; Spec; soundness; completeness

end NegYAffine
end Solution.Secp256k1ScalarMul
