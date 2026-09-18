import Solution.Secp256k1ScalarMul.Lazy_Donor2

-- Adapted donor module: FoldWide
section DonorFile3_0

/-!
# Folded (pseudo-Mersenne) quotient layout for the *wide* slope identity

Same idea as `FoldQuot`, but for the two-convolution "wide" site
`lam2 * dtil2 + lam1 * xd + 2^34 * p = q * p + yT2 + yA + c976 * lam1`.

Folding positions `4,5,6` of the *summed* convolution onto `0,1,2` with the
constant `cF = 2 ^ 256 - P256` is again a free affine recombination.  It
shrinks the modular quotient to a single wire below `2 ^ 70` and puts both
sides of the identity on `L = 4` positions.
-/

namespace Solution.Secp256k1ScalarMulFixedBase
namespace FoldWide

open Challenge.CostR1CS
open CompactAdd (cExp)
open Solution.Secp256k1ScalarMulFixedBase.Limbs

/-! ### Affineness -/

/-! ### Environment stability -/

/-! ### Constant-offset bookkeeping -/

/-! ### Coefficient values and bounds -/

/-! ### Polynomial values -/

/-! ### The wide fold bridge -/

end FoldWide
end Solution.Secp256k1ScalarMulFixedBase

end DonorFile3_0

-- Adapted donor module: CrtFold
section DonorFile3_1

/-!
# Bridging the CRT multiply into the existing fold certificates

`FoldQuot.foldLhs` / `FoldWide.foldLhs2` take the seven raw convolution
coefficients and fold them onto four positions.  `CrtMul.crtFoldMul` produces
the four folded coefficients directly, so the certificate's left-hand side
becomes `crtLhs` / `crtLhs2`: the witnessed coefficient plus the constant
offset limb.

The bound and identity lemmas in `FoldQuot` / `FoldWideC1` are already stated
for an *arbitrary* coefficient vector `P` together with a hypothesis
`hP : ∀ k, eval P[k] = eval (bigIntMulNoReduce a b)[k]`, so they can be reused
verbatim with `P := bigIntMulNoReduce a b` (a free expression vector) once the
evaluated `crtLhs` vector has been rewritten into the evaluated `foldLhs`
vector.  That rewrite is exactly what this file provides.
-/

namespace Solution.Secp256k1ScalarMulFixedBase

open Challenge.CostR1CS

namespace CrtMul

/-! ### Environment stability -/

/-! ### Evaluated-vector bridges -/

end CrtMul

end Solution.Secp256k1ScalarMulFixedBase

end DonorFile3_1

-- Adapted donor module: FoldQInv
section DonorFile3_2

/-!
# Certificate inversion for the narrow (CRT-folded) reduction sites

The folded quotient `q` of a narrow certificate is pinned by the very identity
it appears in, and `P256` is a compile-time constant, so instead of witnessing
`q` it can be written directly as the affine expression

  `q = (∑ₖ lhsₖ 2^(64k) - ∑ₖ tailₖ 2^(64k)) * (P256 : F)⁻¹`

over wires that are already allocated.  That saves one allocation per site
while leaving the surviving `RangeCheck` (which already accepts an arbitrary
`Expression`) and the `GroupedFlex` shape untouched.
-/

namespace Solution.Secp256k1ScalarMulFixedBase

open Challenge.CostR1CS
open Solution.Secp256k1ScalarMulFixedBase.Limbs

namespace CrtMul

end CrtMul

end Solution.Secp256k1ScalarMulFixedBase

end DonorFile3_2

-- Adapted donor module: AffineRangeBounds
section DonorFile3_3

/-!
Integer bounds for the shifted certificates. These lemmas deliberately distinguish
honest semantic assignments (completeness) from replacement-range assumptions
(soundness). No old quotient or carry range is assumed in the soundness direction.
-/
namespace Solution.Secp256k1ScalarMulFixedBase.AffineRangeBounds

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

def nativePrime : ℕ := 21888242871839275222246405745257275088548364400416034343698204186575808495617

theorem zero_of_native_zero {z : ℤ}
    (hz : (z : ZMod nativePrime) = 0)
    (hlo : -(nativePrime : ℤ) < z) (hhi : z < nativePrime) : z = 0 := by
  obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd z nativePrime).mp hz
  norm_num [nativePrime] at hk hlo hhi
  omega

namespace Narrow

end Narrow

namespace Wide

end Wide
end Solution.Secp256k1ScalarMulFixedBase.AffineRangeBounds

end DonorFile3_3

-- Adapted donor module: AffineNarrow
section DonorFile3_4

namespace Solution.Secp256k1ScalarMulFixedBase.AffineNarrow

open AffineRangeBounds
open Challenge.CostR1CS Cost

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

lemma range_of_int (n : ℕ) (z : ℤ) (hz : 0 ≤ z ∧ z < 2^n)
    (hn : (2 : ℕ)^n < circomPrime) : (z : F circomPrime).val < 2^n := by
  have hzn : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hz.1
  have hzlt : z.toNat < 2^n := by exact_mod_cast (show (z.toNat : ℤ) < 2^n by omega)
  have hcast := congrArg (fun a : ℤ => (a : F circomPrime)) hzn
  simp only [Int.cast_natCast] at hcast
  rw [← hcast, ZMod.val_natCast_of_lt (lt_trans hzlt hn)]
  exact hzlt

end Solution.Secp256k1ScalarMulFixedBase.AffineNarrow

end DonorFile3_4

-- Adapted donor module: GroupLaw
section DonorFile3_5

namespace Solution.Secp256k1ScalarMulFixedBase.GroupLaw

open Specs.ShortWeierstrass Specs.Secp256k1
open WeierstrassCurve.Affine

noncomputable section

def W : WeierstrassCurve Fp where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := 0
  a₆ := 7

def fromW : Point W → GroupPoint Fp
  | 0 => .infinity
  | @WeierstrassCurve.Affine.Point.some _ _ _ x y _ => .affine ⟨x, y⟩

@[simp] lemma fromW_zero : fromW (0 : Point W) = .infinity := rfl

end

end Solution.Secp256k1ScalarMulFixedBase.GroupLaw

end DonorFile3_5

-- Adapted donor module: TableReflect
section DonorFile3_6

namespace Solution.Secp256k1ScalarMulFixedBase.TableReflect

open Specs.ShortWeierstrass Specs.Secp256k1
open Solution.Secp256k1ScalarMulFixedBase.GroupLaw

set_option maxRecDepth 65536

def cstep (qx : Fp) (p : Point Fp) (s : Fp) : Point Fp :=
  let x3 := s ^ 2 - p.x - qx
  ⟨x3, s * (p.x - x3) - p.y⟩

def cnth (qx : Fp) : Point Fp → List Fp → ℕ → Point Fp
  | p, _, 0 => p
  | p, [], _ + 1 => p
  | p, s :: rest, k + 1 => cnth qx (cstep qx p s) rest k

def dstep (p : Point Fp) (s : Fp) : Point Fp :=
  let x3 := s ^ 2 - 2 * p.x
  ⟨x3, s * (p.x - x3) - p.y⟩

def dnth : Point Fp → List Fp → ℕ → Point Fp
  | p, _, 0 => p
  | p, [], _ + 1 => p
  | p, s :: rest, k + 1 => dnth (dstep p s) rest k

end Solution.Secp256k1ScalarMulFixedBase.TableReflect

end DonorFile3_6
