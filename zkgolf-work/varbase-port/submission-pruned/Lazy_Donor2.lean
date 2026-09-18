import Solution.Secp256k1ScalarMul.Lazy_Donor1

-- Adapted donor module: CanonicalizeTheorems
section DonorFile2_0

namespace Solution.Secp256k1ScalarMulFixedBase
open Solution.Secp256k1ScalarMulFixedBase.Limbs

namespace Canonicalize

lemma eval_cExp (env : Environment (F circomPrime)) (v k : ℕ) :
    Expression.eval env (CompactAdd.cExp v k) = ((limbOfNat v k : ℕ) : F circomPrime) :=
  rfl

end Canonicalize
end Solution.Secp256k1ScalarMulFixedBase

end DonorFile2_0

-- Adapted donor module: CompleteAddTheorems
section DonorFile2_1

namespace Solution.Secp256k1ScalarMulFixedBase
namespace CompleteAdd

lemma P256_lt : P256 < 2 ^ (limbBits * numLimbs) := by decide

lemma two_pow_limb_lt : 2 ^ limbBits < circomPrime := by decide

lemma limbOfNat_lt (v k : ℕ) : limbOfNat v k < 2 ^ limbBits :=
  Nat.mod_lt _ (Nat.two_pow_pos limbBits)

lemma val_limbOfNat (v k : ℕ) :
    ((limbOfNat v k : ℕ) : F circomPrime).val = limbOfNat v k :=
  ZMod.val_natCast_of_lt (lt_trans (limbOfNat_lt v k) two_pow_limb_lt)

lemma emuOfNat_getElem (v k : ℕ) (hk : k < numLimbs) :
    (emuOfNat v)[k]'hk = ((limbOfNat v k : ℕ) : F circomPrime) := by
  simp only [emuOfNat, Vector.getElem_ofFn]

lemma emuOfNat_normalized (v : ℕ) : (emuOfNat v).Normalized limbBits := by
  intro i
  rw [Fin.getElem_fin, emuOfNat_getElem v i.val i.isLt, val_limbOfNat]
  exact limbOfNat_lt v i.val

lemma value_emuOfNat {v : ℕ} (hv : v < 2 ^ (limbBits * numLimbs)) :
    BigInt.value limbBits (emuOfNat v) = v := by
  rw [BigInt.value_eq_sum]
  have hsum : (∑ k : Fin numLimbs, ((emuOfNat v)[k]).val * 2 ^ (limbBits * k.val))
      = ∑ k ∈ Finset.range numLimbs,
          (v / 2 ^ (limbBits * k) % 2 ^ limbBits) * 2 ^ (limbBits * k) := by
    rw [← Fin.sum_univ_eq_sum_range
      (fun k => (v / 2 ^ (limbBits * k) % 2 ^ limbBits) * 2 ^ (limbBits * k))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fin.getElem_fin, emuOfNat_getElem v i.val i.isLt, val_limbOfNat]
    rfl
  rw [hsum, limb_decomp_mod, Nat.mod_eq_of_lt hv]

open Specs.ShortWeierstrass in
lemma add_inf_left (q : GroupPoint Specs.Secp256k1.Fp) :
    add Specs.Secp256k1.curve .infinity q = q := rfl

end CompleteAdd
end Solution.Secp256k1ScalarMulFixedBase

end DonorFile2_1

-- Adapted donor module: PairAddTheorems
section DonorFile2_2

namespace Solution.Secp256k1ScalarMulFixedBase
open Solution.Secp256k1ScalarMulFixedBase.Limbs

namespace PairAdd

open CompactAdd (cExp)
open Canonicalize (eval_cExp)

/-! ### Borrow-pilot: `dtil = xT + twoPBorrowDigit − xA`, fat-limb, no re-limbing

`dtil` is the wire-only analogue of `xd` above, using the non-uniform digit
vector `twoPBorrowDigit` (sum `= 2·P256`) instead of the uniform `2^64 − 1`
(sum `= 2^256 − 1`). Each limb is bounded by `3·2^64` instead of `2^65`
(§BORROW-PILOT, `BorrowFree.lean`). -/

/-! ### §BORROW-ROLLOUT: fat-limb C1 lemmas (`d2 → dtilOf xT2 x1`)

Mirrors of `polyValue_c1_lhs`/`c1_identity`/`c1_fp`/`c1_discharge` with the
`d2`/`d24`/`lp2` machinery deleted: `P2 = lam2 ⊛ dtil2` (fat limbs, coeff
`< 12·2^128`) sits next to `P1 = lam1 ⊛ xd1` (`< 8·2^128`) under the widened
`vWideFat` tent (`21·2^128`). -/

end PairAdd
end Solution.Secp256k1ScalarMulFixedBase

end DonorFile2_2

-- Adapted donor module: PairAddCompleteTheorems
section DonorFile2_3

namespace Solution.Secp256k1ScalarMulFixedBase
open Solution.Secp256k1ScalarMulFixedBase.Limbs
namespace PairAdd
open CompactAdd (cExp)

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

end PairAdd
end Solution.Secp256k1ScalarMulFixedBase

end DonorFile2_3

-- Adapted donor module: FoldQuot
section DonorFile2_4

/-!
# Folded (pseudo-Mersenne) quotient layout

secp256k1's prime satisfies `P256 = 2 ^ 256 - cF` with `cF = 2 ^ 32 + 977`, i.e.
`2 ^ 256 ≡ cF (mod P256)`.  A 4-limb product `a * b` is produced by
`interpolatedMul` as `7` unreduced convolution positions `P 0 … P 6`.  Folding
positions `4, 5, 6` back onto `0, 1, 2` with the *constant* multiplier `cF` is a
free affine recombination that shrinks the value from `< 2^518` to `< 2^323`, so
the modular quotient fits in **one** wire below `2^68` instead of a full 4-limb
BigInt needing a 256-bit range check.

`foldLhs P v` is the folded left-hand side (plus a constant `v`, always a
multiple of `P256` chosen large enough to keep the quotient non-negative) and
`foldRhs q a b c` is `q * P256 + a + b + c`, both living on `L = 4` positions.
-/

namespace Solution.Secp256k1ScalarMulFixedBase
namespace FoldQuot

open CompactAdd (cExp)
open Challenge.CostR1CS
open Solution.Secp256k1ScalarMulFixedBase.Limbs

/-! ### Affineness -/

/-! ### Environment stability (for computable witnesses) -/

/-! ### Constant-offset bookkeeping -/

/-! ### Coefficient bounds -/

/-! ### Splitting a convolution into low part and folded high part -/

/-! ### Polynomial values -/

/-! ### Certificate inversion

The folded quotient `q` is pinned by the very identity it appears in, and
`P256` is a compile-time constant, so `q` can be written directly as an affine
expression over already-allocated wires instead of being witnessed.
-/

lemma natCast_val_F (x : F circomPrime) : ((x.val : ℕ) : F circomPrime) = x :=
  ZMod.natCast_zmod_val x

/-! ### Soundness -/

/-! ### Completeness -/

end FoldQuot
end Solution.Secp256k1ScalarMulFixedBase

end DonorFile2_4

-- Adapted donor module: CrtMul
section DonorFile2_5

/-!
# The CRT (residue-ring) fold multiply

`MulMod.interpolatedMul` pins the full `2m-1 = 7` coefficient convolution of two
4-limb operands at a cost of `⟨7,7⟩`.  But **nothing in this circuit ever reads
those seven coefficients**: every consumer immediately applies `FoldQuot.foldLhs`
(or `FoldWide.foldLhs2`), i.e. reduces the product modulo `X^4 - cF` with
`cF = 2^32 + 977`.

Multiplication in the residue ring `F_r[X]/(X^4 - cF)` has bilinear rank equal to
`2*4 - k` where `k` is the number of distinct irreducible factors of `X^4 - cF`
over the BN254 scalar field.  `cF` is a fourth power there, so `X^4 - cF` splits
completely, `k = 4`, and the rank is `4`.

`crtFoldMul` realises that: it witnesses the **four folded** coefficients
`z_k + cF * z_{k+4}` directly and pins them with one row per fourth root of `cF`,
at a cost of `⟨4,4⟩`.  Each row is a single product of two affine forms, since
the roots are compile-time constants.
-/

namespace Solution.Secp256k1ScalarMulFixedBase

namespace CrtMul

/-! ### Soundness -/

end CrtMul

namespace Cost
open Challenge.CostR1CS

end Cost

end Solution.Secp256k1ScalarMulFixedBase

end DonorFile2_5
