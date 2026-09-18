import Solution.Secp256k1ScalarMul.ToBytes
import Solution.Secp256k1ScalarMul.ScalarMulTheorems

namespace Solution.Secp256k1ScalarMul
namespace ScalarMul

structure Inputs (F : Type) where
  bits : Vector F Specs.Secp256k1.scalarBits
  px : Emu F
  py : Emu F
deriving ProvableStruct

def Assumptions (input : Inputs (F circomPrime)) : Prop :=
  (∀ i : Fin Specs.Secp256k1.scalarBits, IsBool (input.bits[i])) ∧
  Fe.Valid input.px ∧ Fe.Valid input.py ∧
  Specs.ShortWeierstrass.OnCurve Specs.Secp256k1.curve
    { x := decodeFe input.px, y := decodeFe input.py }

def Spec (input : Inputs (F circomPrime)) (out : Outputs (F circomPrime)) : Prop :=
  out.Valid ∧
    Specs.Secp256k1ScalarMul.Spec (input.bits.map ZMod.val)
      { x := decodeFe input.px, y := decodeFe input.py }
      (decodeOutput out)

end ScalarMul
end Solution.Secp256k1ScalarMul
