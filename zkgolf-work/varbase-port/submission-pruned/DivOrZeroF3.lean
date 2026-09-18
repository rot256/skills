import Solution.Secp256k1ScalarMul.IsZeroFe
import Solution.Secp256k1ScalarMul.Mux
import Solution.Secp256k1ScalarMul.DivOrZeroTheorems
import Solution.Secp256k1ScalarMul.CompleteAddTheorems
import Solution.Secp256k1ScalarMul.AddMod
import Solution.Secp256k1ScalarMul.IsZeroFeSum
import Solution.Secp256k1ScalarMul.Params
import Solution.Secp256k1ScalarMul.MulMod
import Solution.Secp256k1ScalarMul.MulModTargetW
import Solution.Secp256k1ScalarMul.MulModFoldTInv

namespace Solution.Secp256k1ScalarMul

namespace DivOrZeroF3
open DivOrZero MulMod MulModTargetD MulModTargetW

/-- The zero-guarded denominator `den + z·e₀`.  When the zero flag `z` is set,
every limb of `den` vanishes, so the vector is the constant `1`; otherwise it is
`den` itself.  Being a pure affine recombination it costs no witness and no row,
which is what a `Mux` here would have charged. -/
def denSafeVec (den : Var Emu (F circomPrime)) (z : Expression (F circomPrime)) :
    Var Emu (F circomPrime) :=
  Vector.ofFn fun k : Fin numLimbs =>
    (den[k.val]'k.isLt) + (if k.val = 0 then z else 0)

/-- `denSafeVec` is affine whenever its inputs are. -/
lemma affineW_denSafeVec {den : Var Emu (F circomPrime)} {z : Expression (F circomPrime)}
    (hd : Challenge.CostR1CS.AffineW den) (hz : Challenge.CostR1CS.Affine z) :
    Challenge.CostR1CS.AffineW (denSafeVec den z) := by
  intro i hi
  rw [denSafeVec, Vector.getElem_ofFn]
  split
  · exact Challenge.CostR1CS.Affine.add (hd i hi) hz
  · exact Challenge.CostR1CS.Affine.add (hd i hi) Challenge.CostR1CS.Affine.zero

end DivOrZeroF3
end Solution.Secp256k1ScalarMul
