import Solution.Secp256k1ScalarMul.MulModFold32T

/-!
# Folded modular-multiplication certificate with a **constant** second operand

This is `MulModFold32T` specialised to the case where the second operand `b` is a
compile-time constant vector.  The only difference is that the `2m−1`-cell
convolution is *not witnessed*: when every `b[j]` has degree `0`, each cell of
`bigIntMulNoReduce a b` is already an affine form in `a`'s limbs, so it can be
handed to the grouped equality directly.  That deletes `interpolatedMul`'s
`⟨15, 15⟩` outright, taking the certificate from `⟨93, 95⟩` to `⟨78, 80⟩`.

Everything else — the quotient witness, its 36-bit range check, the fold, the
single grouped carry — is shared verbatim with `MulModFold32T`, and so are all
the arithmetic lemmas.
-/

set_option exponentiation.threshold 600

namespace Solution.Secp256k1ScalarMul
namespace MulModFold32TA

open MulMod
open Solution.Secp256k1ScalarMul.Limbs
open MulModFold32T

/-- Same inputs as `MulModFold32T`; the caller is responsible for supplying a
constant `b` (needed only for the R1CS shape, never for soundness). -/
abbrev Inputs := MulModFold32T.Inputs

abbrev Assumptions (Ca Cb : ℕ) := MulModFold32T.Assumptions Ca Cb

abbrev Spec := MulModFold32T.Spec

attribute [local irreducible] RangeCheck.circuit GroupedEqXV.circuit

end MulModFold32TA
end Solution.Secp256k1ScalarMul
