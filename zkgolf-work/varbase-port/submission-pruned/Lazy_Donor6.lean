import Solution.Secp256k1ScalarMul.Lazy_Donor5

-- Adapted donor module: UploadSelectors
section DonorFile6_0

/-! S21: reachable development proofs bundled for the 200-file cap. -/

/- === PackedPoint === -/
section
/-! A selected point retains its four-limb semantic coordinates, while emitted
arithmetic may consume the two affine 128-bit halves of y. The semantic limbs
can be expressions in lookup indicators; they need not be allocated wires. -/
namespace Solution.Secp256k1ScalarMulFixedBase.Packed

open Challenge.CostR1CS Cost
abbrev Field := F circomPrime

structure Point (F : Type) where
  point : Select.AffPoint F
  halves : fields 2 F
deriving ProvableStruct

def pack (y : Emu Field) : fields 2 Field :=
  Vector.ofFn fun i : Fin 2 => y[2*i.val]'(by dsimp [numLimbs]; omega) +
    (2^64 : Field)*y[2*i.val+1]'(by dsimp [numLimbs]; omega)

end Solution.Secp256k1ScalarMulFixedBase.Packed
end

/- === PackedSelect13 === -/
section
namespace Solution.Secp256k1ScalarMulFixedBase.Packed13
open Select13
open Challenge.CostR1CS Cost
set_option maxRecDepth 10000
set_option maxHeartbeats 32000000

def halfCoeff (table : Nat → Nat) (h j : Nat) : Field :=
  ((limbOfNat (table j) (2*h) : Nat) : Field) +
    (2^64 : Field)*((limbOfNat (table j) (2*h+1) : Nat) : Field)

def halfInner (h outer : Nat) (blk : Var (fields 5) Field)
    (h4 : Var (fields 15) Field) (h6 : Var (fields 48) Field) (h7 : Var (fields 64) Field)
    (table : Nat → Nat) : Expression Field :=
  inner (2*h) outer blk h4 h6 h7 table +
    (2^64 : Field)*inner (2*h+1) outer blk h4 h6 h7 table

def halfInnerVal (env : ProverEnvironment Field) (b : Var (fields 13) Field)
    (h outer : Nat) (table : Nat → Nat) : Field :=
  innerVal env b (2*h) outer table + (2^64 : Field)*innerVal env b (2*h+1) outer table

def halfCorr (h o0 o1 : Nat) (blk : Var (fields 5) Field)
    (h4 : Var (fields 15) Field) (h6 : Var (fields 48) Field) (h7 : Var (fields 64) Field)
    (table : Nat → Nat) : Expression Field :=
  (Vector.ofFn fun a : Fin 128 => hot7 blk h4 h6 h7 a.val a.isLt *
    (halfCoeff table h (128*o0+a.val) * halfCoeff table h (128*o1+a.val) : Field)).foldl (·+·) 0

def halfCorrVal (env : ProverEnvironment Field) (b : Var (fields 13) Field)
    (h o0 o1 : Nat) (table : Nat → Nat) : Field :=
  ∑ a : Fin 128, hot7Val env b a.val *
    (halfCoeff table h (128*o0+a.val) * halfCoeff table h (128*o1+a.val))

def halfProdVal (env : ProverEnvironment Field) (b : Var (fields 13) Field)
    (h k : Nat) (table : Nat → Nat) : Field :=
  (hot5Val env b (2*k) + halfInnerVal env b h (2*k+1) table) *
    (hot5Val env b (2*k+1) + halfInnerVal env b h (2*k) table) -
      halfCorrVal env b h (2*k) (2*k+1) table

def halfSelected (h : Nat) (hh : h < 2) (p : Var (fields 32) Field) : Expression Field :=
  (Vector.ofFn fun k : Fin 16 => p[16*h+k.val]'(by have := k.isLt; omega)).foldl (·+·) 0

def halfSelectedVal (env : ProverEnvironment Field) (b : Var (fields 13) Field)
    (h : Nat) (table : Nat → Nat) : Field :=
  ∑ k : Fin 16, halfProdVal env b h k.val table

/-- Proof-only limb selection. No operation emits these products. -/
def ghostSelected (limb : Nat) (blk : Var (fields 5) Field)
    (h4 : Var (fields 15) Field) (h6 : Var (fields 48) Field) (h7 : Var (fields 64) Field)
    (o4 : Var (fields 15) Field) (o5 : Var (fields 16) Field) (table : Nat → Nat) : Expression Field :=
  (Vector.ofFn fun j : Fin 32 => hot5 blk o4 o5 j.val j.isLt *
    inner limb j.val blk h4 h6 h7 table).foldl (·+·) 0

def ghostY (s : Expression Field) (blk : Var (fields 5) Field)
    (h4 : Var (fields 15) Field) (h6 : Var (fields 48) Field) (h7 : Var (fields 64) Field)
    (o4 : Var (fields 15) Field) (o5 : Var (fields 16) Field) (table : Nat → Nat) : Var Emu Field :=
  Vector.ofFn fun i : Fin 4 =>
    let neg := ghostSelected i.val blk h4 h6 h7 o4 o5 (fun j => P256-table j)
    s * (((limbOfNat P256 i.val : Nat) : Field) - (2 : Field)*neg) + neg

def main (xTable yTable : Nat → Nat)
    (b : Var (fields 13) Field) : Circuit Field (Var Packed.Point Field) := do
  let w ← ProvableType.witness (α := fields 12) fun env =>
    Vector.ofFn fun i : Fin 12 => xVal env b i.val (by omega)
  Circuit.forEach (Vector.ofFn fun i : Fin 12 =>
    b[12] * (2 : Field) * b[i.val]'(by omega)
      - (w[i.val]'i.isLt + b[12] + b[i.val]'(by omega) - 1)) assertZero
  let blk ← ProvableType.witness (α := fields 5) fun env =>
    Vector.ofFn fun p : Fin 5 => xVal env b (pairLo p.val) (pairLo_lt p.isLt) *
      xVal env b (pairLo p.val + 1) (pairLo_add_lt p.isLt)
  Circuit.forEach (Vector.ofFn fun p : Fin 5 =>
    xExpr b w (pairLo p.val) (pairLo_lt p.isLt) *
    xExpr b w (pairLo p.val + 1) (pairLo_add_lt p.isLt) - blk[p.val]'p.isLt) assertZero
  let inner4w ← ProvableType.witness (α := fields 9) fun env =>
    Vector.ofFn fun j : Fin 9 => hot4Val env b 0 (j.val % 3 + 4 * (j.val / 3)) (by omega)
  Circuit.forEach (Vector.ofFn fun j : Fin 9 =>
    innerP b w blk 0 (by decide) (j.val % 3) *
    innerP b w blk 1 (by decide) (j.val / 3) - inner4w[j.val]'j.isLt) assertZero
  let inner4 := hot4Vec b w blk 0 (by decide) inner4w
  let inner6w ← ProvableType.witness (α := fields 45) fun env =>
    Vector.ofFn fun j : Fin 45 => hot6Val env b (16 * (j.val / 15) + j.val % 15)
  Circuit.forEach (Vector.ofFn fun j : Fin 45 =>
    hot4 blk inner4 0 (by omega) (j.val % 15) (by omega) *
    innerP b w blk 2 (by decide) (j.val / 15) - inner6w[j.val]'j.isLt) assertZero
  let inner6 := inner6Vec b w blk inner6w
  let inner7w ← ProvableType.witness (α := fields 63) fun env =>
    Vector.ofFn fun j : Fin 63 => hot6Val env b j.val * xVal env b 6 (by omega)
  Circuit.forEach (Vector.ofFn fun j : Fin 63 =>
    hot6 blk inner4 inner6 j.val (by omega) * xExpr b w 6 (by omega) - inner7w[j.val]'j.isLt) assertZero
  let inner7 := inner7Vec b w inner7w
  let outer4w ← ProvableType.witness (α := fields 9) fun env =>
    Vector.ofFn fun j : Fin 9 => hot4Val env b 3 (j.val % 3 + 4 * (j.val / 3)) (by omega)
  Circuit.forEach (Vector.ofFn fun j : Fin 9 =>
    innerP b w blk 3 (by decide) (j.val % 3) *
    innerP b w blk 4 (by decide) (j.val / 3) - outer4w[j.val]'j.isLt) assertZero
  let outer4 := hot4Vec b w blk 3 (by decide) outer4w
  let outer5w ← ProvableType.witness (α := fields 15) fun env =>
    Vector.ofFn fun j : Fin 15 => hot5Val env b (16 + j.val)
  Circuit.forEach (Vector.ofFn fun j : Fin 15 =>
    hot4 blk outer4 3 (by omega) j.val (by omega) *
    xExpr b w 11 (by omega) - outer5w[j.val]'j.isLt) assertZero
  let outer5 := outer5Vec b w outer5w
  let xProd ← ProvableType.witness (α := fields 64) fun env =>
    Vector.ofFn fun k : Fin 64 => outProdVal env b (k.val/16) (k.val % 16) xTable
  Circuit.forEach (Vector.ofFn fun k : Fin 64 =>
    (hot5 blk outer4 outer5 (2 * (k.val % 16)) (by omega) +
        inner (k.val/16) (2 * (k.val % 16) + 1) blk inner4 inner6 inner7 xTable) *
      (hot5 blk outer4 outer5 (2 * (k.val % 16) + 1) (by omega) +
        inner (k.val/16) (2 * (k.val % 16)) blk inner4 inner6 inner7 xTable)
      - (corrC (k.val/16) (2 * (k.val % 16)) (2 * (k.val % 16) + 1)
            blk inner4 inner6 inner7 xTable
          + xProd[k.val]'k.isLt)) assertZero
  let yNeg ← ProvableType.witness (α := fields 32) fun env =>
    Vector.ofFn fun k : Fin 32 => halfProdVal env b (k.val/16) (k.val%16) (fun j => P256-yTable j)
  Circuit.forEach (Vector.ofFn fun k : Fin 32 =>
    (hot5 blk outer4 outer5 (2*(k.val%16)) (by omega) +
      halfInner (k.val/16) (2*(k.val%16)+1) blk inner4 inner6 inner7 (fun j => P256-yTable j)) *
    (hot5 blk outer4 outer5 (2*(k.val%16)+1) (by omega) +
      halfInner (k.val/16) (2*(k.val%16)) blk inner4 inner6 inner7 (fun j => P256-yTable j)) -
    (halfCorr (k.val/16) (2*(k.val%16)) (2*(k.val%16)+1) blk inner4 inner6 inner7 (fun j => P256-yTable j)
      + yNeg[k.val])) assertZero
  let y ← ProvableType.witness (α := fields 2) fun env =>
    Vector.ofFn fun i : Fin 2 =>
      bitVal env b 12 (by decide) *
        (halfCoeff (fun _ => P256) i.val 0 - 2*halfSelectedVal env b i.val (fun j => P256-yTable j)) +
          halfSelectedVal env b i.val (fun j => P256-yTable j)
  Circuit.forEach (Vector.ofFn fun i : Fin 2 =>
    b[12] * ((halfCoeff (fun _ => P256) i.val 0 : Field) -
      (2 : Field)*halfSelected i.val i.isLt yNeg) +
      halfSelected i.val i.isLt yNeg - y[i.val]) assertZero
  return {
    point := {
      x := xSelExpr xTable blk inner4 inner6 inner7 xProd
      y := ghostY b[12] blk inner4 inner6 inner7 outer4 outer5 yTable }
    halves := y }

end Solution.Secp256k1ScalarMulFixedBase.Packed13
end

/- === PositiveTop === -/
section
namespace Solution.Secp256k1ScalarMulFixedBase.PositiveTop

open Select13 Packed13
open Challenge.CostR1CS Cost
set_option maxRecDepth 10000
set_option maxHeartbeats 32000000

end Solution.Secp256k1ScalarMulFixedBase.PositiveTop
end

/- === ElevenSelect === -/
section
namespace Solution.Secp256k1ScalarMulFixedBase.Packed11

open Challenge.CostR1CS Cost
set_option maxRecDepth 10000
set_option maxHeartbeats 32000000

abbrev Field := F circomPrime

end Solution.Secp256k1ScalarMulFixedBase.Packed11
end

end DonorFile6_0

-- Adapted donor module: CollisionFree
section DonorFile6_1

namespace Solution.Secp256k1ScalarMulFixedBase.CollisionFree

open Specs.ShortWeierstrass Specs.Secp256k1
open Solution.Secp256k1ScalarMulFixedBase.GroupLaw

end Solution.Secp256k1ScalarMulFixedBase.CollisionFree

end DonorFile6_1

-- Adapted donor module: Recode
section DonorFile6_2

namespace Solution.Secp256k1ScalarMulFixedBase
namespace Recode

end Recode
end Solution.Secp256k1ScalarMulFixedBase

namespace Solution.Secp256k1ScalarMulFixedBase
namespace Recode

section ComputableWitness
open Challenge.Utils.ComputableWitnessLemmas

end ComputableWitness

end Recode
end Solution.Secp256k1ScalarMulFixedBase

end DonorFile6_2

-- Adapted donor module: RecodeTheorems
section DonorFile6_3

namespace Solution.Secp256k1ScalarMulFixedBase
open Solution.Secp256k1ScalarMulFixedBase.Limbs

namespace Recode

set_option maxHeartbeats 6400000
set_option maxRecDepth 8192

end Recode
end Solution.Secp256k1ScalarMulFixedBase

set_option maxRecDepth 2048
set_option maxHeartbeats 2000000

namespace Solution.Secp256k1ScalarMulFixedBase.Width12.RecodeCircuitBridge

end Solution.Secp256k1ScalarMulFixedBase.Width12.RecodeCircuitBridge

end DonorFile6_3

-- Adapted donor module: CandidateRadix
section DonorFile6_4

namespace Solution.Secp256k1ScalarMulFixedBase.CandidateRadix
open Specs.ShortWeierstrass Specs.Secp256k1

set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

end Solution.Secp256k1ScalarMulFixedBase.CandidateRadix

end DonorFile6_4

-- Adapted donor module: CandidateSemantics
section DonorFile6_5

namespace Solution.Secp256k1ScalarMulFixedBase.CandidateSemantics
open Specs.ShortWeierstrass Specs.Secp256k1

set_option maxHeartbeats 6400000
set_option maxRecDepth 8192

end Solution.Secp256k1ScalarMulFixedBase.CandidateSemantics

end DonorFile6_5

-- Adapted donor module: CompactAddCost
section DonorFile6_6

namespace Solution.Secp256k1ScalarMulFixedBase
namespace CompactAdd

open Challenge.CostR1CS
open Cost

end CompactAdd
end Solution.Secp256k1ScalarMulFixedBase

end DonorFile6_6

-- Adapted donor module: CanonicalizeCost
section DonorFile6_7

namespace Solution.Secp256k1ScalarMulFixedBase
namespace Canonicalize

open Challenge.CostR1CS
open Cost
open CompactAdd (cExp)

attribute [local irreducible] isR1CSRow r1csProducts operationsIsR1CS flatOperationsIsR1CS

end Canonicalize
end Solution.Secp256k1ScalarMulFixedBase

end DonorFile6_7

-- Adapted donor module: Chain
section DonorFile6_8

/-!
Chain extension of the signed-digit comb: the accumulator between incomplete
additions is represented as `(x, lam, T)` — its y-coordinate is never
materialized; the actual point is `(x, impliedY)` with
`impliedY = lam·(T.x − x) − T.y` (chord through the last-added table point).

`ChainStart` = stageA + stageO2 (windows 0,1 seed, A-form slope certificate).
`ChainExt`   = stageC1 (previous table point in the accumulator slot) + stageX
               (x-half of the old stageC2) — one window per application.
`ChainFinish`= stageY (y-half of the old stageC2) — materializes the final y.
-/

namespace Solution.Secp256k1ScalarMulFixedBase
namespace Chain

open CompactAdd (cExp)

syntax "chain_simp" : tactic
macro_rules
  | `(tactic| chain_simp) =>
    `(tactic| simp +arith (maxSteps := 4000000) only
        [stageX, stageY, PairAdd.dtilOf, MulMod.witnessedMul, MulMod.interpolatedMul,
         circuit_norm,
         NormalizeImplicit.circuit, NormalizeImplicit.elaborated,
         EqViaCarriesFlex.circuit, EqViaCarriesFlex.elaborated,
         GroupedFlex.circuit, GroupedFlex.elaborated, GroupedFlex.main,
         gfQuad, posOfQuad, vQuad, wfQuad, hgvQuad,
         gfWide, posOfWide, vWide, wfWide, hgvWide,
         GroupedFlex.widthAllocFrom, GroupedFlex.widthConsFrom,
         secpParams, RangeCheck.circuit, RangeCheck.elaborated, numLimbs, limbBits])

end Chain

namespace ChainStart
open Specs.ShortWeierstrass
open Specs.Secp256k1 (Fp curve)

end ChainStart

namespace ChainExt
open Specs.ShortWeierstrass
open Specs.Secp256k1 (Fp curve)

end ChainExt

namespace ChainFinish
open Specs.ShortWeierstrass
open Specs.Secp256k1 (Fp curve)

end ChainFinish
end Solution.Secp256k1ScalarMulFixedBase

end DonorFile6_8

-- Adapted donor module: PairAddGroupLaw
section DonorFile6_9

namespace Solution.Secp256k1ScalarMulFixedBase
namespace PairAdd

open Specs.ShortWeierstrass
open Specs.Secp256k1 (Fp curve chord_onCurve)

end PairAdd
end Solution.Secp256k1ScalarMulFixedBase

end DonorFile6_9

-- Adapted donor module: ChainGroupLaw
section DonorFile6_10

/-!
Group-law assembly lemmas for the chain representation: the accumulator's
y-coordinate is implied, `yP = lamP·(xTP − xP) − yTP` (chord through the
last-added table point TP).
-/

namespace Solution.Secp256k1ScalarMulFixedBase
namespace Chain

open Specs.ShortWeierstrass
open Specs.Secp256k1 (Fp curve chord_onCurve)

end Chain
end Solution.Secp256k1ScalarMulFixedBase

end DonorFile6_10

-- Adapted donor module: SelectCircuit
section DonorFile6_12a

namespace Solution.Secp256k1ScalarMulFixedBase
namespace CombTableBridge

open Specs.ShortWeierstrass Specs.Secp256k1

end CombTableBridge
end Solution.Secp256k1ScalarMulFixedBase

end DonorFile6_12a

-- Adapted donor module: UploadPart1
section DonorFile6_13

/-! S21: reachable development proofs bundled for the 200-file cap. -/

/- === Sparse32Model === -/
section
/-!
The integer model shared by the sparse radix-`2^32` implementation and its bounds.
Reduction is the single rule `t^8 = t + 977`; evaluating at `t = 2^32`
therefore reduces modulo the secp256k1 base-field modulus.
-/
namespace Solution.Secp256k1ScalarMulFixedBase.Sparse32

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 12000000
set_option exponentiation.threshold 1024

abbrev Words (K : Type*) := Fin 8 → K

def H : ℤ := 2 ^ 32
def m : ℤ := 2 ^ 31
def B64 : ℤ := 2 ^ 64
def R : ℤ := 2 ^ 128
def c : ℤ := 2 ^ 32 + 977
def q : ℤ := 2 ^ 256 - c
def nativePrime : ℕ :=
  21888242871839275222246405745257275088548364400416034343698204186575808495617

/-- Coefficient of output position `k` after reducing the monomial `t^(i+j)` by
`t^8 = t + 977`. Inputs have degree at most seven, so one reduction is enough. -/
def redCoeff (i j k : Fin 8) : ℤ :=
  if i.val + j.val < 8 then
    if i.val + j.val = k.val then 1 else 0
  else
    (if i.val + j.val - 8 = k.val then 977 else 0) +
    (if i.val + j.val - 7 = k.val then 1 else 0)

def sparseMul {K : Type*} [CommRing K] (x y : Words K) (k : Fin 8) : K :=
  ∑ i : Fin 8, ∑ j : Fin 8, (redCoeff i j k : K) * (x i * y j)

def sparseSquare {K : Type*} [CommRing K] (x : Words K) : Words K :=
  sparseMul x x

def eval {K : Type*} [CommRing K] (x : Words K) (r : K) : K :=
  ∑ i : Fin 8, x i * r ^ i.val

def lowHalf {K : Type*} [CommRing K] (x : Words K) : K :=
  x 0 + H * x 1 + H ^ 2 * x 2 + H ^ 3 * x 3

def highHalf {K : Type*} [CommRing K] (x : Words K) : K :=
  x 4 + H * x 5 + H ^ 2 * x 6 + H ^ 3 * x 7

lemma redCoeff_nonneg (i j k : Fin 8) : 0 ≤ redCoeff i j k := by
  simp only [redCoeff]
  split_ifs <;> norm_num

lemma sparseMul_map {K L : Type*} [CommRing K] [CommRing L]
    (f : K →+* L) (x y : Words K) (k : Fin 8) :
    sparseMul (fun i => f (x i)) (fun i => f (y i)) k = f (sparseMul x y k) := by
  simp only [sparseMul, map_sum, map_mul, map_intCast]

/-- The defining sparse multiplication identity over every commutative ring in
which the evaluation point satisfies the sparse modulus. -/
lemma eval_sparseMul {K : Type*} [CommRing K] (x y : Words K) (r : K)
    (hr : r ^ 8 = r + 977) :
    eval (sparseMul x y) r = eval x r * eval y r := by
  simp only [eval, sparseMul, redCoeff, Fin.sum_univ_succ, Fin.sum_univ_zero]
  norm_num [Fin.succ] at hr ⊢
  simp at hr ⊢
  linear_combination
    -(x 1*y 7+x 2*y 6+x 3*y 5+x 4*y 4+x 5*y 3+x 6*y 2+x 7*y 1 +
      r*(x 2*y 7+x 3*y 6+x 4*y 5+x 5*y 4+x 6*y 3+x 7*y 2) +
      r^2*(x 3*y 7+x 4*y 6+x 5*y 5+x 6*y 4+x 7*y 3) +
      r^3*(x 4*y 7+x 5*y 6+x 6*y 5+x 7*y 4) +
      r^4*(x 5*y 7+x 6*y 6+x 7*y 5) +
      r^5*(x 6*y 7+x 7*y 6) + r^6*(x 7*y 7)) * hr

lemma H_square : H ^ 2 = B64 := by norm_num [H, B64]
lemma R_eq_H4 : R = H ^ 4 := by norm_num [R, H]
lemma q_eq_R2_sub_c : q = R ^ 2 - c := by norm_num [q, R, c]

lemma eval_eq_halves (x : Words ℤ) : eval x H = lowHalf x + R * highHalf x := by
  simp only [eval, lowHalf, highHalf, Fin.sum_univ_succ, Fin.sum_univ_zero]
  norm_num [Fin.succ]
  simp
  rw [R_eq_H4]
  ring

/-- Embed four unsigned 64-bit words at sparse32 positions `0,2,4,6`. -/
def embed {K : Type*} [Zero K] (a : Fin 4 → K) (i : Fin 8) : K :=
  if i.val % 2 = 0 then a ⟨i.val / 2, by omega⟩ else 0

lemma eval_embed {K : Type*} [CommRing K] (a : Fin 4 → K) (r : K) :
    eval (embed a) r = ∑ j : Fin 4, a j * (r ^ 2) ^ j.val := by
  simp only [eval, embed, Fin.sum_univ_succ, Fin.sum_univ_zero]
  norm_num [Fin.succ]
  ring

end Solution.Secp256k1ScalarMulFixedBase.Sparse32
end

/- === SmallSquareAlgebra === -/
section
namespace Solution.Secp256k1ScalarMulFixedBase.SmallSquare

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

abbrev Field := F circomPrime
def c : ℕ := 2^32 + 977

def poly {K : Type*} [CommRing K] {m : ℕ} (a : Fin m → K) (r : K) : K :=
  ∑ i : Fin m, a i * r^i.val

end Solution.Secp256k1ScalarMulFixedBase.SmallSquare
end

/- === SmallSquareBounds === -/
section
namespace Solution.Secp256k1ScalarMulFixedBase.SmallSquare
set_option maxHeartbeats 16000000
set_option maxRecDepth 20000
set_option exponentiation.threshold 1024

inductive Layout where | w32 | w16
  deriving DecidableEq

def count : Layout → ℕ | .w32 => 8 | .w16 => 16
def bits : Layout → ℕ | .w32 => 32 | .w16 => 16
def base (l : Layout) : ℤ := 2^(bits l)
def R : ℤ := 2^128
def q : ℤ := 2^256-c

end Solution.Secp256k1ScalarMulFixedBase.SmallSquare
end

/- === SmallNormalize === -/
section
namespace Solution.Secp256k1ScalarMulFixedBase.SmallNormalize
open SmallSquare Utils.Bits
set_option maxHeartbeats 16000000
set_option maxRecDepth 10000

def perWord (l : Layout) : ℕ := count l / 4

lemma word_index (l : Layout) (i : Fin (count l)) : i.val / perWord l < 4 := by
  cases l <;> simp [perWord, count] at * <;> omega

lemma chunk_index (l : Layout) (i : Fin (count l)) (j : Fin (bits l)) :
    bits l*(i.val%perWord l)+j.val < 64 := by
  cases l <;> simp [perWord, count, bits] at * <;> omega

def chunk (l : Layout) (b : Var (fields 64) Field) (i : Fin (count l)) : Expression Field :=
  fieldFromBitsExpr (Vector.ofFn fun j : Fin (bits l) =>
    b[bits l*(i.val%perWord l)+j.val]'(chunk_index l i j))

def outputs (l : Layout) (b0 b1 b2 b3 : Var (fields 64) Field) : Var (fields (count l)) Field :=
  Vector.ofFn fun i => chunk l
    (if i.val/perWord l = 0 then b0 else if i.val/perWord l = 1 then b1
      else if i.val/perWord l = 2 then b2 else b3) i

def digit (l : Layout) (x : Emu Field) (i : Fin (count l)) : ℕ :=
  (x[i.val/perWord l]'(word_index l i)).val / 2^(bits l*(i.val%perWord l)) % 2^(bits l)

def main (l : Layout) (x : Var Emu Field) : Circuit Field (Var (fields (count l)) Field) := do
  let b0 ← ToBitsAffine.toBitsAffine 63 secpParams.hB x[0]
  let b1 ← ToBitsAffine.toBitsAffine 63 secpParams.hB x[1]
  let b2 ← ToBitsAffine.toBitsAffine 63 secpParams.hB x[2]
  let b3 ← ToBitsAffine.toBitsAffine 63 secpParams.hB x[3]
  return outputs l b0 b1 b2 b3

instance elaborated (l : Layout) : ElaboratedCircuit Field Emu (fields (count l)) (main l) := by
  elaborate_circuit

def Assumptions (_ : Emu Field) (_ : ProverData Field) : Prop := True
def ProverAssumptions (x : Emu Field) (_ : ProverData Field) (_ : ProverHint Field) : Prop :=
  BigInt.Normalized 64 x
def Spec (l : Layout) (x : Emu Field) (out : fields (count l) Field) (_ : ProverData Field) : Prop :=
  BigInt.Normalized 64 x ∧ ∀ i, out[i.val] = ((digit l x i : ℕ) : Field)
def ProverSpec (l : Layout) (_ : Emu Field) (_ : fields (count l) Field) (_ : ProverHint Field) : Prop := True

lemma eval_chunk (l : Layout) (env : Environment Field) (b : Var (fields 64) Field)
    (z : Field) (hb : Vector.map (Expression.eval env) b = fieldToBits 64 z)
    (i : Fin (count l)) :
    Expression.eval env (chunk l b i) =
      (((z.val / 2^(bits l*(i.val%perWord l))) % 2^(bits l) : ℕ) : Field) := by
  change env (fieldFromBitsExpr _) = _
  rw [fieldFromBits_eval]
  have hv : Vector.map (Expression.eval env)
      (Vector.ofFn fun j : Fin (bits l) => b[bits l*(i.val%perWord l)+j.val]'(chunk_index l i j)) =
      fieldToBits (bits l) ((z.val / 2^(bits l*(i.val%perWord l)) : ℕ) : Field) := by
    apply Vector.ext
    intro j hj
    have hdlt : z.val / 2^(bits l*(i.val%perWord l)) < circomPrime :=
      lt_of_le_of_lt (Nat.div_le_self _ _) (ZMod.val_lt z)
    have he := congrArg (fun v : Vector Field 64 => v[bits l*(i.val%perWord l)+j]'(chunk_index l i ⟨j,hj⟩)) hb
    simp only [Vector.getElem_map] at he
    simp only [Vector.getElem_map, Vector.getElem_ofFn, he, fieldToBits, toBits,
      Vector.getElem_mapRange, ZMod.val_natCast_of_lt hdlt]
    rw [Nat.testBit_div_two_pow]
    rw [show bits l*(i.val%perWord l)+j = j+bits l*(i.val%perWord l) by omega]
  rw [hv, fieldFromBits_fieldToBits_mod]
  rw [ZMod.val_natCast_of_lt (lt_of_le_of_lt (Nat.div_le_self _ _) (ZMod.val_lt z))]

theorem soundness (l : Layout) :
    GeneralFormalCircuit.Soundness Field (main l) Assumptions (Spec l) := by
  circuit_proof_start [ToBitsAffine.toBitsAffine, ToBitsAffine.main]
  obtain ⟨⟨hn0,hb0⟩,⟨hn1,hb1⟩,⟨hn2,hb2⟩,⟨hn3,hb3⟩⟩ := h_holds
  have hx (i : ℕ) (hi : i < 4) : Expression.eval env input_var[i] = input[i] := by
    rw [← h_input, Vector.getElem_map]
  rw [hx 0 (by decide)] at hn0 hb0
  rw [hx 1 (by decide)] at hn1 hb1
  rw [hx 2 (by decide)] at hn2 hb2
  rw [hx 3 (by decide)] at hn3 hb3
  refine ⟨?_, ?_⟩
  · intro i; fin_cases i <;> assumption
  · intro i
    simp only [outputs, circuit_norm, Vector.getElem_ofFn]
    dsimp only [digit]
    split_ifs with h0 h1 h2
    · simpa only [h0] using eval_chunk l env _ input[0] hb0 i
    · simpa only [h1] using eval_chunk l env _ input[1] hb1 i
    · simpa only [h2] using eval_chunk l env _ input[2] hb2 i
    · have h3 : i.val/perWord l = 3 := by
        cases l <;> simp [perWord, count] at * <;> omega
      simpa only [h3] using eval_chunk l env _ input[3] hb3 i

theorem completeness (l : Layout) :
    GeneralFormalCircuit.Completeness Field (main l) ProverAssumptions (ProverSpec l) := by
  circuit_proof_start [ToBitsAffine.toBitsAffine, ToBitsAffine.main]
  have hx (i : ℕ) (hi : i < 4) : Expression.eval env.toEnvironment input_var[i] = input[i] := by
    rw [← h_input, Vector.getElem_map]
  exact ⟨by rw [hx]; exact h_assumptions 0,
    by rw [hx]; exact h_assumptions 1,
    by rw [hx]; exact h_assumptions 2,
    by rw [hx]; exact h_assumptions 3⟩

def circuit (l : Layout) : GeneralFormalCircuit Field Emu (fields (count l)) where
  main := main l
  Assumptions := Assumptions
  Spec := Spec l
  ProverAssumptions := ProverAssumptions
  ProverSpec := ProverSpec l
  soundness := soundness l
  completeness := completeness l

lemma digit_lt (l : Layout) (x : Emu Field) (i : Fin (count l)) :
    digit l x i < 2^(bits l) := Nat.mod_lt _ (by positivity)

lemma word32 (v : ℕ) (hv : v < 2^64) :
    v = v%2^32 + 2^32*(v/2^32%2^32) := by omega

lemma word16 (v : ℕ) (hv : v < 2^64) :
    v = v%2^16 + 2^16*(v/2^16%2^16) + 2^32*(v/2^32%2^16) + 2^48*(v/2^48%2^16) := by
  have h0 := Nat.mod_add_div v (2^16)
  have h1 := Nat.mod_add_div (v/2^16) (2^16)
  have h2 := Nat.mod_add_div (v/2^32) (2^16)
  norm_num [Nat.div_div_eq_div_mul] at h0 h1 h2
  omega

lemma digit_reconstruct_nat (l : Layout) (x : Emu Field) (hx : BigInt.Normalized 64 x) :
    (∑ i : Fin (count l), digit l x i * (2^(bits l))^i.val) = BigInt.value 64 x := by
  have h0 := hx 0; have h1 := hx 1; have h2 := hx 2; have h3 := hx 3
  cases l
  · have r0 := word32 x[0].val h0; have r1 := word32 x[1].val h1
    have r2 := word32 x[2].val h2; have r3 := word32 x[3].val h3
    simp only [count, bits, perWord, digit, BigInt.value_eq_sum,
      Fin.sum_univ_succ, Fin.sum_univ_zero]
    norm_num [Fin.succ]
    omega
  · have r0 := word16 x[0].val h0; have r1 := word16 x[1].val h1
    have r2 := word16 x[2].val h2; have r3 := word16 x[3].val h3
    simp only [count, bits, perWord, digit, BigInt.value_eq_sum,
      Fin.sum_univ_succ, Fin.sum_univ_zero]
    norm_num [Fin.succ]
    omega

lemma digit_reconstruct (l : Layout) (x : Emu Field) (hx : BigInt.Normalized 64 x) :
    poly (fun i => (digit l x i : ℤ)) (base l) = (BigInt.value 64 x : ℤ) := by
  have h := congrArg (fun n : ℕ => (n : ℤ)) (digit_reconstruct_nat l x hx)
  simpa only [Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, poly, base] using h

end Solution.Secp256k1ScalarMulFixedBase.SmallNormalize
end

/- === SmallNormalizeContract === -/
section
namespace Solution.Secp256k1ScalarMulFixedBase.SmallNormalize
open SmallSquare Challenge.CostR1CS Cost
open Challenge.Utils.ComputableWitnessLemmas
set_option maxHeartbeats 16000000
set_option maxRecDepth 10000

theorem costIs_toBitsAffine (w : ℕ) (x : Expression (F circomPrime)) :
    CostIs (ToBitsAffine.main w x) ⟨w, w + 1⟩ := by
  unfold ToBitsAffine.main
  rw [show (⟨w, w + 1⟩ : Count)
        = ⟨w, 0⟩ + (⟨w * 0, w * 1⟩ + (⟨0, 1⟩ + Count.zero)) from by
      simp only [Count.zero]; congr 1 <;>
        simp only [Count.add_allocations, Count.add_constraints] <;> omega]
  refine CostIs.bind (CostIs.witnessVector (F := F circomPrime) w _) fun bits => ?_
  refine CostIs.bind
    (show CostIs (Circuit.forEach bits (fun input => assertion assertBool input) _) ⟨w * 0, w * 1⟩ from
      CostIs.forEach fun a m =>
        (CostIs.assertion (circuit := assertBool) (b := a) (K := ⟨0, 1⟩) (fun k => rfl)) m) fun _ => ?_
  exact CostIs.bind (CostIs.assertZero _) fun _ => CostIs.pure _

theorem isR1CS_toBitsAffine (w : ℕ) (x : Expression (F circomPrime)) (hx : Affine x) :
    IsR1CSCirc (ToBitsAffine.main w x) := by
  unfold ToBitsAffine.main
  refine IsR1CSCirc.bind_out (IsR1CSCirc.witnessVector w _) fun ww => ?_
  refine IsR1CSCirc.bind ?_ fun _ => ?_
  · refine IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) fun i k => ?_
    refine (IsR1CSCirc.assertion (circuit := assertBool) fun j => ?_) k
    refine IsR1CSCirc.assertZero ?_ j
    show isR1CSRow (_ * (_ - 1))
    exact isR1CSRow_mul (affineW_witnessVector_output w _ ww i.val i.isLt)
      (Affine.sub (affineW_witnessVector_output w _ ww i.val i.isLt) (Affine.const 1))
  · refine IsR1CSCirc.bind (IsR1CSCirc.assertZero ?_) fun _ => IsR1CSCirc.pure _
    let bits : Var (fields w) (F circomPrime) :=
      (Circuit.witnessVector w fun env =>
        Utils.Bits.fieldToBits w (x.eval env)).output ww
    have hbits : Affine (Utils.Bits.fieldFromBitsExpr bits) := by
      change Affine (Utils.Bits.fieldFromBitsExpr
        (Vector.mapRange w fun i => Expression.var { index := ww + i }))
      exact affine_fieldFromBitsExpr _ (affineW_mapRange_var _)
    let c : F circomPrime := (((2 ^ w : ℕ) : F circomPrime)⁻¹ : F circomPrime)
    have htop : Affine (c * (x - Utils.Bits.fieldFromBitsExpr bits)) :=
      Affine.fconst_mul c (Affine.sub hx hbits)
    exact isR1CSRow_mul htop (Affine.sub htop (Affine.const 1))

theorem costIs_toBitsAffine_sub (w : ℕ) (hn : (2 : ℕ) ^ (w + 1) < circomPrime)
    (x : Expression (F circomPrime)) :
    CostIs (ToBitsAffine.toBitsAffine w hn x) ⟨w, w + 1⟩ :=
  CostIs.subcircuitWithAssertion (fun m => costIs_toBitsAffine w x m)

theorem isR1CS_toBitsAffine_sub (w : ℕ) (hn : (2 : ℕ) ^ (w + 1) < circomPrime)
    (x : Expression (F circomPrime)) (hx : Affine x) :
    IsR1CSCirc (ToBitsAffine.toBitsAffine w hn x) :=
  IsR1CSCirc.subcircuitWithAssertion (fun m => isR1CS_toBitsAffine w x hx m)

theorem cost (l : Layout) (x : Var Emu Field) : CostIs (main l x) ⟨252,256⟩ := by
  rw [show (⟨252,256⟩ : Count) = ⟨63,64⟩ + (⟨63,64⟩ + (⟨63,64⟩ + (⟨63,64⟩ + Count.zero))) by decide]
  unfold main
  refine CostIs.bind (costIs_toBitsAffine_sub 63 secpParams.hB _) fun b0 => ?_
  refine CostIs.bind (costIs_toBitsAffine_sub 63 secpParams.hB _) fun b1 => ?_
  refine CostIs.bind (costIs_toBitsAffine_sub 63 secpParams.hB _) fun b2 => ?_
  refine CostIs.bind (costIs_toBitsAffine_sub 63 secpParams.hB _) fun b3 => ?_
  exact CostIs.pure _

theorem shape (l : Layout) (x : Var Emu Field) (hx : AffineW x) : IsR1CSCirc (main l x) := by
  unfold main
  refine IsR1CSCirc.bind (isR1CS_toBitsAffine_sub 63 secpParams.hB _ (hx 0 (by decide))) fun _ => ?_
  refine IsR1CSCirc.bind (isR1CS_toBitsAffine_sub 63 secpParams.hB _ (hx 1 (by decide))) fun _ => ?_
  refine IsR1CSCirc.bind (isR1CS_toBitsAffine_sub 63 secpParams.hB _ (hx 2 (by decide))) fun _ => ?_
  refine IsR1CSCirc.bind (isR1CS_toBitsAffine_sub 63 secpParams.hB _ (hx 3 (by decide))) fun _ => ?_
  exact IsR1CSCirc.pure _

lemma bits_affine (w : ℕ) (x : Expression Field) (hx : Affine x) (n : ℕ) :
    AffineW ((ToBitsAffine.main w x).output n) := by
  simp only [ToBitsAffine.main, circuit_norm]
  intro i hi
  by_cases h : i < w
  · rw [Vector.getElem_push_lt h, Vector.getElem_mapRange]
    exact Affine.var _
  · have he : i = w := by omega
    subst i
    rw [Vector.getElem_push_eq]
    exact Affine.fconst_mul _ (Affine.sub hx (affine_fieldFromBitsExpr _ (affineW_mapRange_var _)))

lemma chunk_affine (l : Layout) (b : Var (fields 64) Field) (hb : AffineW b) (i : Fin (count l)) :
    Affine (chunk l b i) := by
  apply affine_fieldFromBitsExpr
  intro j hj
  rw [Vector.getElem_ofFn]
  exact hb _ (chunk_index l i ⟨j,hj⟩)

lemma outputs_affine (l : Layout) (b0 b1 b2 b3 : Var (fields 64) Field)
    (h0 : AffineW b0) (h1 : AffineW b1) (h2 : AffineW b2) (h3 : AffineW b3) :
    AffineW (outputs l b0 b1 b2 b3) := by
  intro i hi
  rw [outputs, Vector.getElem_ofFn]
  split_ifs <;> apply chunk_affine <;> assumption

lemma affine_output (l : Layout) (x : Var Emu Field) (hx : AffineW x) (n : ℕ) :
    AffineW ((main l x).output n) := by
  simp only [main, circuit_norm, ToBitsAffine.toBitsAffine]
  exact outputs_affine l _ _ _ _
    (bits_affine 63 x[0] (hx 0 (by decide)) n)
    (bits_affine 63 x[1] (hx 1 (by decide)) (n+63))
    (bits_affine 63 x[2] (hx 2 (by decide)) (n+63+63))
    (bits_affine 63 x[3] (hx 3 (by decide)) (n+63+63+63))

lemma input_limb_stable {input : Var Emu (F circomPrime)} {i : ℕ} (hi : i < numLimbs)
    {env env' : ProverEnvironment (F circomPrime)}
    (h : eval env input = eval env' input) :
    eval env input[i] = eval env' input[i] := by
  have hmap := emu_map_eval_eq_of_eval_eq h
  have hget : (input.map (Expression.eval env.toEnvironment))[i] =
      (input.map (Expression.eval env'.toEnvironment))[i] := by rw [hmap]
  simp only [Vector.getElem_map] at hget
  rw [CircuitType.eval_var_field_prover, CircuitType.eval_var_field_prover]
  exact hget

theorem computableWitnesses (l : Layout) : (circuit l).base.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset (FormalCircuitBase.computableWitnessCondition input env env')
    ((main l input).operations offset)
  apply FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  have hT : ∀ (y : Expression Field) (o : ℕ),
      (ToBitsAffine.toBitsAffine 63 secpParams.hB y).localLength o = 63 := by
    intro y o
    simp [subcircuitWithAssertion, ToBitsAffine.toBitsAffine, circuit_norm]
  unfold main
  simp only [Circuit.bind_structuralComputableWitnesses_iff,
    Circuit.pure_structuralComputableWitnesses_iff, hT, and_true]
  refine ⟨?_,?_,?_,?_⟩
  · simp only [subcircuitWithAssertion, FormalCircuitBase.Operations.StructuralComputableWitnesses,
      Circuit.operations, and_true]
    exact GeneralFormalCircuit.subcircuit_flatStructuralComputableWitnesses
      (ToBitsAffine.toBitsAffine 63 secpParams.hB) input input[0] offset
      (fun _ _ hinput => input_limb_stable (by decide) hinput)
      (ToBitsAffine.computableWitnesses 63 secpParams.hB) env env'
  · simp only [subcircuitWithAssertion, FormalCircuitBase.Operations.StructuralComputableWitnesses,
      Circuit.operations, and_true]
    exact GeneralFormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (ToBitsAffine.toBitsAffine 63 secpParams.hB) input input[1] (offset+63)
      (fun _ _ _ _ _ hinput => input_limb_stable (by decide) hinput)
      (ToBitsAffine.computableWitnesses 63 secpParams.hB) env env'
  · simp only [subcircuitWithAssertion, FormalCircuitBase.Operations.StructuralComputableWitnesses,
      Circuit.operations, and_true]
    exact GeneralFormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (ToBitsAffine.toBitsAffine 63 secpParams.hB) input input[2] (offset+63+63)
      (fun _ _ _ _ _ hinput => input_limb_stable (by decide) hinput)
      (ToBitsAffine.computableWitnesses 63 secpParams.hB) env env'
  · simp only [subcircuitWithAssertion, FormalCircuitBase.Operations.StructuralComputableWitnesses,
      Circuit.operations, and_true]
    exact GeneralFormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (ToBitsAffine.toBitsAffine 63 secpParams.hB) input input[3] (offset+63+63+63)
      (fun _ _ _ _ _ hinput => input_limb_stable (by decide) hinput)
      (ToBitsAffine.computableWitnesses 63 secpParams.hB) env env'

end Solution.Secp256k1ScalarMulFixedBase.SmallNormalize
end

/- === SmallCert === -/
section
namespace Solution.Secp256k1ScalarMulFixedBase.SmallCert
open SmallSquare
open Challenge.CostR1CS Cost
set_option maxHeartbeats 16000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024

lemma q_ne : (q : Field) ≠ 0 := by decide
lemma r_ne : (R : Field) ≠ 0 := by decide

lemma native (L H : Field) :
    let k := (q : Field)⁻¹*(L+(R : Field)*H)
    let t := (R : Field)⁻¹*(L-((R-c : ℤ) : Field)*k)
    L-((R-c : ℤ) : Field)*k-(R : Field)*t=0 ∧ H-((R-1 : ℤ) : Field)*k+t=0 := by
  dsimp only
  have hq : (q : Field) = (R : Field)^2-(c : Field) := by
    norm_num [q, R, c]
  constructor
  · field_simp [r_ne, q_ne]
    ring
  · field_simp [r_ne, q_ne]
    rw [hq]
    push_cast
    ring

end Solution.Secp256k1ScalarMulFixedBase.SmallCert
end

/- === SmallSupport === -/
section
namespace Solution.Secp256k1ScalarMulFixedBase
open SmallSquare Challenge.CostR1CS Cost
open Challenge.Utils.ComputableWitnessLemmas
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

namespace SmallNormalize
theorem call_output (l : Layout) (x : Var Emu Field) (n : ℕ) :
    (circuit l x).output n = (main l x).output n :=
  ((elaborated l).output_eq x n).symm
theorem output_stable (l : Layout) (x : Var Emu Field) {n k : ℕ}
    {e e' : ProverEnvironment Field} (hx : eval e x = eval e' x)
    (h : e.AgreesBelow k e') (hk : n+252 ≤ k) :
    eval e ((main l x).output n) = eval e' ((main l x).output n) := by
  have hb (j : ℕ) (hj : j < 4) (o : ℕ) (ho : o+63 ≤ k) :=
    ValidPBytes.toBitsAffine_output_eval_stable 63 x[j]
      (by simpa only [circuit_norm] using input_limb_stable hj hx) h ho
  have hc (b : Var (fields 64) Field)
      (hs : ∀ i (hi : i < 64), Expression.eval e.toEnvironment b[i] =
        Expression.eval e'.toEnvironment b[i]) (i : Fin (count l)) :
      Expression.eval e.toEnvironment (chunk l b i) =
        Expression.eval e'.toEnvironment (chunk l b i) := by
    unfold chunk
    apply ValidPBytes.fieldFromBitsExpr_eval_stable
    intro j hj
    rw [Vector.getElem_ofFn hj]
    exact hs _ (chunk_index l i ⟨j,hj⟩)
  simp only [main,circuit_norm,ToBitsAffine.toBitsAffine]
  apply Vector.ext; intro i hi
  simp only [Vector.getElem_map,outputs,Vector.getElem_ofFn]
  split_ifs
  · exact hc _ (hb 0 (by decide) n (by omega)) ⟨i,hi⟩
  · exact hc _ (hb 1 (by decide) (n+63) (by omega)) ⟨i,hi⟩
  · exact hc _ (hb 2 (by decide) (n+63+63) (by omega)) ⟨i,hi⟩
  · exact hc _ (hb 3 (by decide) (n+63+63+63) (by omega)) ⟨i,hi⟩
end SmallNormalize

end Solution.Secp256k1ScalarMulFixedBase
end

/- === LazyLift === -/
section
namespace Solution.Secp256k1ScalarMulFixedBase.LazyX
open SmallSquare
set_option maxHeartbeats 1000000

def nativeHalf : ℤ := 10944121435919637611123202872628637544274182200208017171849102093287904247808
def lift (x : Field) : ℤ :=
  if (x.val : ℤ) ≤ nativeHalf then x.val else (x.val : ℤ)-circomPrime

lemma cast_lift (x : Field) : ((lift x : ℤ) : Field) = x := by
  unfold lift
  split_ifs
  · simp only [Int.cast_natCast,FoldQuot.natCast_val_F]
  · simp only [Int.cast_sub,Int.cast_natCast,FoldQuot.natCast_val_F]
    have h : (circomPrime : Field) = 0 := by decide
    rw [h,sub_zero]

lemma lift_bounds (x : Field) : -nativeHalf ≤ lift x ∧ lift x ≤ nativeHalf := by
  have h := ZMod.val_lt x
  change x.val < 21888242871839275222246405745257275088548364400416034343698204186575808495617 at h
  unfold lift
  have hp : (circomPrime : ℤ) = 21888242871839275222246405745257275088548364400416034343698204186575808495617 := rfl
  split_ifs <;> simp only [nativeHalf,hp] at * <;> omega

lemma lift_cast (z : ℤ) (hz : -nativeHalf ≤ z ∧ z ≤ nativeHalf) : lift (z : Field) = z := by
  have hb := lift_bounds (z : Field)
  have hzero : (((lift (z : Field)-z : ℤ) : Field)) = 0 := by
    rw [Int.cast_sub,cast_lift,sub_self]
  have he := AffineRangeBounds.zero_of_native_zero hzero
    (by simp only [nativeHalf,AffineRangeBounds.nativePrime] at *; omega)
    (by simp only [nativeHalf,AffineRangeBounds.nativePrime] at *; omega)
  omega

lemma lift_nat (x : Field) (hx : x.val < 2^64) : lift x = (x.val : ℤ) := by
  apply if_pos
  simp only [nativeHalf]
  omega

end Solution.Secp256k1ScalarMulFixedBase.LazyX
end

/- === SmallCertSemantics === -/
section
namespace Solution.Secp256k1ScalarMulFixedBase.SmallCert
open SmallSquare
set_option maxHeartbeats 16000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024

end Solution.Secp256k1ScalarMulFixedBase.SmallCert
end

/- === Sparse32Rep === -/
section
namespace Solution.Secp256k1ScalarMulFixedBase.Sparse32

open SmallSquare

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000

/-- Circuit-facing storage for the eight balanced radix-`2^32` digits. -/
abbrev Digits (K : Type*) := fields 8 K

/-- The offset introduced by subtracting `2^31` from every radix-`2^32` digit. -/
def kappa : ℤ := m * ∑ i : Fin 8, H ^ i.val

def unsignedDigit (raw : Emu Field) (i : Fin 8) : ℕ :=
  SmallNormalize.digit .w32 raw i

def digitZ (raw : Emu Field) (i : Fin 8) : ℤ :=
  (unsignedDigit raw i : ℤ) - m

/-- A raw four-word slope together with its eight balanced native-field digits. -/
def SlopeRep (raw : Emu Field) (a : Digits Field) : Prop :=
  BigInt.Normalized 64 raw ∧
    ∀ i : Fin 8, a[i.val] = ((digitZ raw i : ℤ) : Field)

def digitsZ (a : Digits Field) : Words ℤ := fun i => LazyX.lift a[i.val]

def slopeValueZ (raw : Emu Field) : ℤ :=
  (BigInt.value 64 raw : ℤ) - kappa

def slopeValueFp (raw : Emu Field) : Specs.Secp256k1.Fp :=
  (slopeValueZ raw : Specs.Secp256k1.Fp)

lemma digitZ_bounds (raw : Emu Field) (i : Fin 8) :
    -m ≤ digitZ raw i ∧ digitZ raw i < m := by
  have h := SmallNormalize.digit_lt .w32 raw i
  simp only [digitZ, unsignedDigit, m, bits] at h ⊢
  omega

lemma digitZ_native_bounds (raw : Emu Field) (i : Fin 8) :
    -LazyX.nativeHalf ≤ digitZ raw i ∧ digitZ raw i ≤ LazyX.nativeHalf := by
  have h := digitZ_bounds raw i
  simp only [m, LazyX.nativeHalf] at h ⊢
  omega

lemma SlopeRep.digit_lift {raw : Emu Field} {a : Digits Field}
    (ha : SlopeRep raw a) (i : Fin 8) :
    LazyX.lift a[i.val] = digitZ raw i := by
  rw [ha.2 i]
  exact LazyX.lift_cast _ (digitZ_native_bounds raw i)

lemma SlopeRep.digitsZ_eq {raw : Emu Field} {a : Digits Field}
    (ha : SlopeRep raw a) : digitsZ a = digitZ raw := by
  funext i
  exact ha.digit_lift i

lemma digit_reconstruct (raw : Emu Field) (hraw : BigInt.Normalized 64 raw) :
    eval (digitZ raw) H = slopeValueZ raw := by
  have hr := SmallNormalize.digit_reconstruct .w32 raw hraw
  have hr' : (∑ i : Fin 8, (unsignedDigit raw i : ℤ) * H ^ i.val) =
      (BigInt.value 64 raw : ℤ) := by
    simpa only [SmallSquare.poly, base, bits, unsignedDigit, H] using hr
  simp only [eval, digitZ, unsignedDigit, slopeValueZ, kappa]
  rw [show (∑ i : Fin 8,
      ((SmallNormalize.digit .w32 raw i : ℤ) - m) * H ^ i.val) =
      (∑ i : Fin 8, (SmallNormalize.digit .w32 raw i : ℤ) * H ^ i.val) -
        m * ∑ i : Fin 8, H ^ i.val by
      simp only [sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]]
  rw [show (∑ i : Fin 8,
      (SmallNormalize.digit .w32 raw i : ℤ) * H ^ i.val) =
      (BigInt.value 64 raw : ℤ) by simpa only [unsignedDigit] using hr']

lemma SlopeRep.reconstruct {raw : Emu Field} {a : Digits Field}
    (ha : SlopeRep raw a) : eval (digitsZ a) H = slopeValueZ raw := by
  rw [ha.digitsZ_eq]
  exact digit_reconstruct raw ha.1

lemma SlopeRep.reconstructFp {raw : Emu Field} {a : Digits Field}
    (ha : SlopeRep raw a) :
    eval (fun i => (digitsZ a i : Specs.Secp256k1.Fp))
      (H : Specs.Secp256k1.Fp) = slopeValueFp raw := by
  have h := congrArg (fun z : ℤ => (z : Specs.Secp256k1.Fp)) ha.reconstruct
  simpa only [eval, Int.cast_sum, Int.cast_mul, Int.cast_pow, slopeValueFp] using h

/-- Honest raw words for a curve-field slope.  Adding `kappa` before taking the
canonical representative exactly compensates for balancing every digit. -/
def slopeWitness (s : Specs.Secp256k1.Fp) : Emu Field :=
  emuOfNat (s + (kappa : Specs.Secp256k1.Fp)).val

lemma slopeWitness_normalized (s : Specs.Secp256k1.Fp) :
    BigInt.Normalized 64 (slopeWitness s) :=
  CompleteAdd.emuOfNat_normalized _

lemma slopeWitness_value (s : Specs.Secp256k1.Fp) :
    BigInt.value 64 (slopeWitness s) =
      (s + (kappa : Specs.Secp256k1.Fp)).val := by
  apply CompleteAdd.value_emuOfNat
  exact lt_trans (ZMod.val_lt _) CompleteAdd.P256_lt

lemma slopeWitness_valueFp (s : Specs.Secp256k1.Fp) :
    slopeValueFp (slopeWitness s) = s := by
  simp only [slopeValueFp, slopeValueZ, slopeWitness_value, Int.cast_sub,
    Int.cast_natCast, ZMod.natCast_zmod_val]
  ring

/-- The same balanced digits regrouped into four signed radix-`2^64` words. -/
def wordZ (raw : Emu Field) (j : Fin 4) : ℤ :=
  (raw[j.val].val : ℤ) - m * (1 + H)

end Solution.Secp256k1ScalarMulFixedBase.Sparse32
end

/- === Sparse32Bounds === -/
section
/-! Universal integer envelopes for the sparse32 state and wide relation. -/
namespace Solution.Secp256k1ScalarMulFixedBase.Sparse32

set_option maxHeartbeats 12000000
set_option maxRecDepth 30000
set_option exponentiation.threshold 1024

def wordMax : ℤ := B64 - 1
def nativeHalf : ℤ := (nativePrime : ℤ) / 2

/-- Four 64-bit words embedded at sparse32 positions `0,2,4,6`. -/
def dcap (i : Fin 8) : ℤ := if i.val % 2 = 0 then wordMax else 0

lemma dcap_nonneg (i : Fin 8) : 0 ≤ dcap i := by
  simp only [dcap]
  split_ifs <;> norm_num [wordMax, B64]

lemma embed_bounds (a : Fin 4 → ℤ) (ha : ∀ i, 0 ≤ a i ∧ a i ≤ wordMax)
    (i : Fin 8) : 0 ≤ embed a i ∧ embed a i ≤ dcap i := by
  simp only [embed, dcap]
  split_ifs
  · exact ha _
  · omega

lemma half_interval (f lo hi : Words ℤ)
    (hf : ∀ i, lo i ≤ f i ∧ f i ≤ hi i) :
    (lowHalf lo ≤ lowHalf f ∧ lowHalf f ≤ lowHalf hi) ∧
    (highHalf lo ≤ highHalf f ∧ highHalf f ≤ highHalf hi) := by
  simp only [lowHalf, highHalf, H]
  have h0 := hf 0; have h1 := hf 1; have h2 := hf 2; have h3 := hf 3
  have h4 := hf 4; have h5 := hf 5; have h6 := hf 6; have h7 := hf 7
  norm_num at *
  omega

end Solution.Secp256k1ScalarMulFixedBase.Sparse32
end

/- === PackedState === -/
section
namespace Solution.Secp256k1ScalarMulFixedBase.Packed
open Challenge.CostR1CS Cost

end Solution.Secp256k1ScalarMulFixedBase.Packed
end

/- === Sparse32State === -/
section
/-! Deferred coordinates represented by eight signed radix-`2^32` coefficients.
The four raw slope words encode the balanced slope with a fixed offset; only
the semantic view uses its canonical secp256k1 representative. -/
namespace Solution.Secp256k1ScalarMulFixedBase.SparseX

open SmallSquare Challenge.CostR1CS Cost
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000

abbrev Coeffs (K : Type*) := fields 8 K

def zwords (x : Coeffs Field) : Sparse32.Words ℤ := fun i => LazyX.lift x[i.val]
def emuz (x : Emu Field) : Fin 4 → ℤ := fun i => x[i.val].val

def embedVec (x : Emu Field) : Coeffs Field :=
  Vector.ofFn fun i => Sparse32.embed (fun j => x[j.val]) i
def embedExpr (x : Var Emu Field) : Var (fields 8) Field :=
  Vector.ofFn fun i => Sparse32.embed (fun j => x[j.val]) i

lemma eval_embedExpr (env : Environment Field) (x : Var Emu Field) :
    eval env (embedExpr x) = embedVec (eval env x) := by
  apply Vector.ext
  intro i hi
  simp only [embedExpr, embedVec, Sparse32.embed, circuit_norm, Vector.getElem_ofFn,
    Vector.getElem_map]
  split_ifs <;> simp only [Expression.eval]

lemma affine_embedExpr (x : Var Emu Field) (hx : AffineW x) : AffineW (embedExpr x) := by
  intro i hi
  rw [embedExpr, Vector.getElem_ofFn]
  simp only [Sparse32.embed]
  split_ifs
  · exact hx _ _
  · exact Affine.const _

lemma emuz_bounds (x : Emu Field) (hx : BigInt.Normalized 64 x) (i : Fin 4) :
    0 ≤ emuz x i ∧ emuz x i ≤ Sparse32.wordMax := by
  have hi := hx i
  simp only [Fin.getElem_fin] at hi
  have hz : (x[i.val].val : ℤ) < 2 ^ 64 := by exact_mod_cast hi
  dsimp only [emuz, Sparse32.wordMax, Sparse32.B64]
  exact ⟨Int.natCast_nonneg _, by omega⟩

lemma embed_value (x : Emu Field) :
    Sparse32.eval (Sparse32.embed (emuz x)) Sparse32.H = (BigInt.value 64 x : ℤ) := by
  rw [Sparse32.eval_embed, Sparse32.H_square]
  simp only [emuz, BigInt.value_eq_sum, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Fin.val_zero, Fin.val_succ, Sparse32.B64]
  norm_num only [Fin.succ, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
    Int.reducePow, Int.reduceMul, Fin.val_mk, Fin.getElem_fin, Fin.val_zero]
  try ring

lemma embed_zwords (x : Emu Field) (hx : BigInt.Normalized 64 x) :
    zwords (embedVec x) = Sparse32.embed (emuz x) := by
  funext i
  simp only [zwords, embedVec, Vector.getElem_ofFn, Sparse32.embed]
  split_ifs
  · apply LazyX.lift_nat
    simpa only [Fin.getElem_fin] using hx ⟨i.val / 2, by change i.val / 2 < 4; omega⟩
  · exact LazyX.lift_cast 0 (by norm_num [LazyX.nativeHalf])

lemma eval_sub {K : Type*} [CommRing K] (a b : Sparse32.Words K) (r : K) :
    Sparse32.eval (fun i => a i-b i) r = Sparse32.eval a r-Sparse32.eval b r := by
  simp only [Sparse32.eval, sub_mul, Finset.sum_sub_distrib]

lemma eval_cast (a : Sparse32.Words ℤ) :
    ((Sparse32.eval a Sparse32.H : ℤ) : Specs.Secp256k1.Fp) =
      Sparse32.eval (fun i => (a i : Specs.Secp256k1.Fp)) (Sparse32.H : Specs.Secp256k1.Fp) := by
  simp only [Sparse32.eval, Int.cast_sum, Int.cast_mul, Int.cast_pow]

lemma curve_root : (Sparse32.H : Specs.Secp256k1.Fp)^8 =
    (Sparse32.H : Specs.Secp256k1.Fp) + 977 := by decide

lemma dvd_q_iff (z : ℤ) : Sparse32.q ∣ z ↔ (z : Specs.Secp256k1.Fp) = 0 := by
  have hq : Sparse32.q = (Specs.Secp256k1.p : ℤ) := by decide
  rw [hq]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).symm

end Solution.Secp256k1ScalarMulFixedBase.SparseX
end

/- === Sparse32CertBounds === -/
section
/-!
Two-half quotient/carry certificates for sparse32. Completeness uses the honest
quotient and carry extrema. Soundness deliberately uses the full admitted
power-of-two ranges.
-/
namespace Solution.Secp256k1ScalarMulFixedBase.Sparse32

set_option maxHeartbeats 24000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 1024

end Solution.Secp256k1ScalarMulFixedBase.Sparse32
end

/- === Sparse32Cert === -/
section
namespace Solution.Secp256k1ScalarMulFixedBase.Sparse32Cert
open Sparse32
open Challenge.CostR1CS Cost
open Challenge.Utils.ComputableWitnessLemmas
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

abbrev Field := SmallSquare.Field

end Solution.Secp256k1ScalarMulFixedBase.Sparse32Cert
end

/- === Sparse32Constants === -/
section
namespace Solution.Secp256k1ScalarMulFixedBase.Sparse32
open SmallSquare

def mulLeftTable : Fin 12 → Fin 8 → Field := ![
  ![1, 17830313287178678300075165430871420918623796426666436563442495302091948996803, 16052220995846179155770638562993134065194722560516022159294779337741062486774, 14346482063451528945327715214050469444928178411454331741841682816047614103144, 21339301304752718988215352341228879974107791115026816894980508983458082919256, 15186338500635156823802589253117867895193699858373702849122702488306366487793, 7848266810172406343638849335992843908508025916319356350300949193263573272390, 3653093957930534339083788324908071808261542320956665151843894665890557700170],
  ![1, 0, 17657420889165142708325888127146764367282761903416803545312828205605851228411, 18356882090831635286785840712767081933734099407095191010478024293022790835566, 10481600734669560230218618961743559767969138051662470696140532799013938881337, 6230981028153536343814912205643947668221254812873179125621177324355503183913, 10256945437743364403948523415602339732071568966424142649310528511578796984408, 3879764850311880149921339326947741580094340619195257923777522274992161414605],
  ![1, 1, 14338883243649854931900099441676946938171415650364854537142507074516509169545, 7560782226249230895930992101143082200640297455737807941499563845876303833286, 7597618652866706488059559975468778686119883912199448567334106454640730279302, 19545197686259630769584425011835526484867522661178533023528037373658234903216, 19747686893353283502036851852379302557648826495780892528811278283139174377676, 7396703465303399993044749412035825986096006585324484928114909865918907493329],
  ![1, 2, 11020345598134567155474310756207129509060069397312905528972185943427167110679, 18652925233506101727322549234776357556094859904796459216219307585305625326623, 4713636571063852745900500989193997604270629772736426438527680110267521677267, 10971171472526449973107532072769830212965426109067852577736693236385158126902, 7350185477123927377878774543898990294677719624721608064613823868123743275327, 10913642080294919836168159497123910392097672551453711932452297456845653572053],
  ![1, 0, 10018073864673442513518430073484026915052364810749044824415024641613086976241, 18443463137444866779066660126500063127619097974263312847675577020796344701782, 15784410606773979991823749972685351125196062676659605255511439101045852654842, 18223056516515274334717990367659739894556405069644024368945164689525432597221, 16965470788455150874066627926632497218885138070407302800451239301805957509347, 8551939828350411054356504317129589504189880685789187635552140617389610488130],
  ![1, 1, 21474440737686566566119686761100152170552154870722394296571138700681058268352, 9101717771676344043425626014924868402440946728049569135593927774412259299093, 11846748545714563478781095263231485165223521241828659807721325900255832359206, 15545596348335661340652465938169189744823140709354107496720063473559847191214, 14360361878088857835767571613044854163242655124772572457453716792053904891459, 13674893377703334137155855914267728976786284623614794533653834406831647647985],
  ![1, 2, 11042564738860415396474537703459002337503580530279709425029048573173221064846, 21648215277747096530030997648606948765811159882251859767210482714603982392021, 7909086484655146965738440553777619205250979806997714359931212699465812063570, 12868136180156048346586941508678639595089876349064190624494962257594261785207, 11755252967722564797468515299457211107600172179137842114456194282301852273571, 18797846927056257219955207511405868449382688561440401431755528196273684807840],
  ![1, 0, 0, 12468348012623040825192146294675171179855414518991213012721477000913213348614, 5469452413023980165758398547485993458033653419203165111301006736344888152322, 17800484446806152479040058745194584736630379582817033276702312050334874230801, 13016145140785917587333560187986965254663419332688846560349526174807217460372, 5803444235246449678884773776271872196002600774474923632524646628303478892715],
  ![1, 1, 1, 5549094966479066551317868255815680115428428836234761080724418817823425505752, 10385616989095764052269862852546795798817525340548116239111555507049252274852, 8538598130619381675188984564470540677479527775620087565569406986498940768688, 16677443735959974280366155452151926400331955933363941069443994329925271344250, 6837998636741029673933731546176478756189251051816123891954060238420813365106],
  ![1, 2, 4, 12358285506499888791681540586692556826622055887550738124965396734319906689645, 17577233076791893720776091269470761354108553607672947054927415947236413032564, 9462229081971437051446883052503428393928285398989163276769497998958458487529, 9177960620110058034755278327861381809655965679528095830699592528914059473670, 13953888165030957817669221226485662979459824261348517477453929259542431234386],
  ![1, 3, 9, 11007676760846232324036757542048526224887931272523109801746206563826848404676, 5156057804273093949030678053000615035358373820161623215050383870330561929841, 20571377300862318607813754209293247885976652452924260410302585087713427387324, 12405938665075444072747334560372606571183812971597345187814524958349390344249, 5262869948276958887844837071942149777265956002656070045326049505092524004938],
  ![1, 4, 16, 1497268729518097148383519121883588310226054991151876111066848306344250650845, 16898576915217915181526434693650907019663714778846213406876867649483315957917, 19977799915452751122043192289582724065076264537009344622470464066188038972456, 4473134999016857172095918404428325596367133409155654797090587431655455460370, 2653186858318308106706984827803214238156010676154815939268625161646900172379]
]

def mulOutTable : Fin 8 → Fin 12 → Field := ![
  ![3009020363786216896458374568611060141893793250184664185608781440688144160465, 13765381858198407640340031514569358996472652883634291929338233862241085698201, 7865712452137393909052692866061637064004159559128011738684966779700854774572, 10223762929280807466492487917616158740727941911212269912799517940626167457917, 8430856272019024240033346876081943238979611474193293896048337421321642265609, 16039279450846670264765366268038679263031203875484996626375347097346666413186, 13057220193713645324374608833787743525827587339331643804178743975879306240339, 11184959109084908783131655413616770161029624304147944995563860235763874873182, 17986412997067144103816360423843328684571067582885421910163261791209147832028, 5494495857421627437016525999933894184280654230417266752581705132402578448617, 13667727913035784531631401492058032738487813286834337954749346555529543602367, 10604627834444020736365582297325043791984076705042062356097122886745839207220],
  ![20763318163528416485282803781759334267969259083963103883510227548027075599842, 20784150439010959570079717842719138699478718721853266359439605202403502344678, 11051896548025350671132151645222262544986243275533646447042843937112194052283, 9396609893888425980778584955930502382708825080133305647896972850712887653937, 1820169086954456926169916121270781277814559663257506808204337966134979001020, 21805260996950804886112047857070969257206437531414196457522243097160622032006, 14558870628419427140605546174087557197541935271327093475522110370263755984138, 15568795827481887485036847551173266505028472760752795416235779741256117200263, 8326499666057206697210225481784229327257214685835787359222413371520092884611, 9916399174051076462122364280104386217670628155668134813779484565392709148501, 16548315968763581440851056076678642362068345817927096124614306100463965539385, 2677413709743332810343578448999855580107910755246307612897104555582758028655],
  ![6434623415606853071008492586992891416075761871914933566664072646139679736179, 13320689190564470392362212073941773436401341435389692070468572898716507673762, 8843711682368719366798775840145989766846951918408110478525645968767581750405, 5250351163358370816472636429234319385889235379348036816077785917442596902438, 9090517384392706652038162165768692909870296256668011864760522415948928747230, 3557356299020443516205474354355256724287192457513175730232714842854771538429, 6369350770732485107217815026408387959863687804034793333658886202064388491559, 1021424663818743780452972633972612324797687502041957972787377722298249909112, 4936954360466930970618398450705470081726012527598865993070919776817136198812, 12972419284178063831566653849675581315120806796615767017427913525367524212504, 18978418802283952052917346845371477764544624153507414481953073626304208614940, 18665397342404636553573088469713922357318223899039412392863535390157468702715],
  ![19229605427121741224630892758389346588553330356808123469856926886817807235956, 5375733781974748119754581010671988741221722050486913988775409884693000721410, 13596847191658384929276794242772261551101270388771460275764587579624788602312, 17853073858236225434301617922903548063292311372395206716502810695938853109955, 904508566655371864046504933161860338100784986232563159347496714797460998696, 21738391067805856820281798685892642544027784970849199459753759674752629032889, 9583538129089526838713029302948485069270877973891407906298283986345634119973, 20328158459272913452615943331369780966308439088672847410572644861436305530773, 9022653015741906092430288986595919380916762535766697884220430666010135835260, 3421935650632800574424409022919953683167340892182009590351823595789012378916, 391958195239883984160943878668217325062336587086404009801460109640466585257, 9883053887606291998841630395249646280267225199353372190943590463608756822305],
  ![1094482630573599477792397105700407419257853989404058284635423602694441350631, 11812552563580539467380641787691020637135904015871922739409715091647833746606, 2460071883768605946539550518858963944996350089329253909617203162434981549515, 17182791474050376268396721328744417205309476861162163535712802498910830442081, 5542754535061096805452916767199157496094884150697848547009826516310680000601, 1659165329277325326128402806959088131680990542898291434750548917771742534664, 15283636217136715098456465057521949909859228694037439545324495729061990808447, 20608635429395649209641574768757221872891565146968615563303472689609727260000, 2782315365476459013908439331045942891957061288793950151718193365452123975884, 6391221063015485596103591753122459208303446381320565594552589773313015083990, 5346621138937904042628499989458505308216999913509896873665808998552754407166, 19276966728922619858802827511227241417038060928086165538790940587118921318500],
  ![272498037643020218674345226812193359915470131438840999883331566491177066111, 8726613875229163457270962236432611286793382903784023427178549082752355180523, 4196934139090409659054428348983730130719793720657065044738429159154840547110, 13629240891154556011631242643155335828360968622853137570000645796919402595546, 20155746609755256274018846043611312602880107529384215555564512913463068476646, 12744674399399518937034236341357403123870758844293988528770201950393102535866, 4870440841037809146501774145161396206882172271669795499157334606375655403923, 11219276667624156985002209969218637803569471972918117055099825542145704059751, 19552128467541230185735521170303005117878228675420309373837471564163607529033, 7034432858838620835866288806061389251122120951002539138460489377554751248846, 7372144747000891738151860609571855844712722433378752031928362399088079320105, 21555325696721017884536718930874779974584988345695421837570071160953107010242],
  ![11413604713085643752338683934736272232136690297253810655799679314056898981917, 7167743851288250512555532615068640099545330026962665675689259090555384609766, 21650161889548736573596352821848952704306559528225111899095527324659550908156, 13395434943882333888303343075989999815057975059742574243260150450371427955320, 3417630373722882224829459011080599145329975988577093685031312998622738369706, 9279681875231481040579116938065478152534245102230350952502819404167622497924, 3301468551560914047364666923403679346275214571350807143645512939744197711447, 16534781268290354596905878600092051546906504002942710505811557286004780342107, 20652749394359307681251549556663006155059387766260708906840365359594806776803, 13635872170225389907419325985889331391949373357578987091327176435491880436404, 2824255224606323077889296331977285627297960508073050521643752064839759522625, 8056072975234034030445228676728354314890970193298334781542112451345802861527],
  ![2814903261912687896117973563089438434563768971336393600360879549663780529645, 2667249701441864774715597466903749925142325784117355315150988243443136620236, 14097406720285962376461012306728957814848855181734408906775841319194511632071, 3113845546297041687873905230460679857756322516389954283785445679908021672777, 8282906061533695547767382183578138625059271214495071201940592064454594420750, 16114942622677245490238034960226676443194197079384538322565445401413099237336, 10886040524838653522390806828790177644746801491594873901156202063848633918679, 8478579684960975792490856352125202091067290327913827321575687406561996344890, 21127145852002900402135846721259387077040310576783447898991981943886502658380, 990078023920181607484838683183061232351903470793430715625324732883216183115, 1099550560749971932924531165524555516426294439531929837931789549710485134734, 19768565798575195080631243264416350780544480948004940412630842977911064125472]
]

def squareLeftTable : Fin 9 → Fin 8 → Field := ![
  ![1, 17830313287178678300075165430871420918623796426666436563442495302091948996803, 16052220995846179155770638562993134065194722560516022159294779337741062486774, 14346482063451528945327715214050469444928178411454331741841682816047614103144, 21339301304752718988215352341228879974107791115026816894980508983458082919256, 15186338500635156823802589253117867895193699858373702849122702488306366487793, 7848266810172406343638849335992843908508025916319356350300949193263573272390, 3653093957930534339083788324908071808261542320956665151843894665890557700170],
  ![1, 20228974049081631334033511402522366373992691273890059839613043621031137466184, 14374781948211006769858722630390019861368662176237727410016285972517586360874, 18680571440434028383436593735874787970216604834024101612684901067612695364574, 11897908696387827327994065883967569292307702949983912297023696424158335300320, 18804982677801365332074823193839092791173438371322981674410065641245844536399, 6886942026367442123535966750345212069036617466276684826823958051252771531566, 1939882425155940074960669663473870790047170309597628961888761137496080707303],
  ![1, 20228974049081631334033511402522366373992691273890059839613043621031137466185, 11056244302695718993432933944920202432257315923185778401845964841428244302008, 7884471575851623992581745124250788237122802882666718543706440620466208362294, 9013926614584973585835006897692788210458448810520890168217270079785126698285, 10230956464068184535597930254773396519271341819212301228618721503972767760085, 16377683481977361221624295187122174894613874995633434706324707822813148924834, 5456821040147459918084079748561955196048836275726855966226148728422826786027],
  ![1, 16672304872426199637423831216436700172024077230194691907927159122821889893864, 338164249452459888938697980954416094937106782267650556166687697614500786776, 7252900538192725133012002708523098583823278269716183699942731910003162203073, 17497596655216821110002315644226038032005581358392861363492271035828037872226, 18753095238994128259332669899664685963731143262212664184822923183174594237475, 11044212168904036978432989761885318345740771004116454849276466545623997334601, 15220091350094843138301455031193432296369122543102610989625172401982709491874],
  ![1, 16672304872426199637423831216436700172024077230194691907927159122821889893865, 11794531122465583941539954668570541350436896842241000028322801756682472078887, 19799398044263477619617374342205178947193491423918474331559286850194885296001, 13559934594157404596959660934772172072033039923561915915702157835038017576590, 16075635070814515265267145470174135813997878901922747312597821967209008831468, 8439103258537743940133933448297675290098288058481724506278944035871944716713, 20343044899447766221100806628331571768965526480928217887726866191424746651729],
  ![20359427081012083661403335330743739568231841969456494150700994679073834458167, 0, 7558565483464362632940589252576395378655476508160869545263147541584641387410, 17597461307207582512214244478752884009534933232584103468116004697468033567866, 20495383718964717413730252116642752000056350382003859251773767897623992547511, 10364649059626983037474378068600710601991679854324985465749807019275840121719, 13498591781732913208017255543455458113632284863287742551198852587512859911197, 20359427081012083661403335330743739568231841969456494150700994679073834458167],
  ![0, 0, 5469452413023980165758398547485993458033653419203165111301006736344888152322, 2219177462088778058048683011753699575395930924925347102173846953323539204063, 19841500268708055957140202645941862650585666977947997983988361935998725337093, 123931506415855345915327154265874588262385873056906878186544069245974316106, 13355233908659172754937284649802097122213016661069431937221607591559823545840, 19486494494604516808961800440118118839143996267283062892479255648982924158824],
  ![19625953636414343354081550893686682147742462085512417161291934909095631700380, 17592529254416028164363440835559949878577769326345525292089116529168948714472, 13548624495199209025481696067042463805038247820004994257922630049194360412968, 21712349523847776059695280033894128883629452651647867003693339834552209999734, 21577473028736838426896661386626257640377944704667157545710302151259780285834, 21205222422518621693745968172239532575632738990556632757712073901207413021713, 14106949665870870611454609049095365505308988081188859880963648332702118111048, 6293327195235144833022495082688067853779133450124830220249332826395305889904],
  ![9924630385617517732776604610530474259798186204471015003957460190226704500989, 0, 20577312747721484600522568935339499763145553642125185164094748319055874858260, 14448147004483308007028211666233725282395170750974458873039843733113250477868, 19024835534539653100820712770393741167128962709431300802060695283464702228292, 11549979642885937829248915251847081448948138745287922416698319347657739415956, 3329767718936524668490806867981332214616326031760380866901306652652027992138, 9796924909133419200361563949830961855700678588349459612091611388633838408911]
]

def squareRightTable : Fin 9 → Fin 8 → Field := ![
  ![1, 17830313287178678300075165430871420918623796426666436563442495302091948996803, 16052220995846179155770638562993134065194722560516022159294779337741062486774, 14346482063451528945327715214050469444928178411454331741841682816047614103144, 21339301304752718988215352341228879974107791115026816894980508983458082919256, 15186338500635156823802589253117867895193699858373702849122702488306366487793, 7848266810172406343638849335992843908508025916319356350300949193263573272390, 3653093957930534339083788324908071808261542320956665151843894665890557700170],
  ![0, 1, 18569705226323987445820617059787457659437018147364085335527883055486466436751, 11092143007256870831391557133633275355454562449058651274719743739429321493337, 19004260790036421480087346758982494006699110260953012214891777842202599893582, 13314216658106094425769512806191578816646267848305353897906860049302731719303, 9490741455609919098088328436776962825577257529356749879500749771560377393268, 3516938614991519843123410085088084406001665966129227004337387590926746078724],
  ![1, 3412711160010793239756208163404845855495856713093273801730294430229143517401, 17360166755216292172150276803890546785636307244815558797129140486291727504244, 12675410840970717061547610191420062416037626221350197492489555644388729565652, 7659628628039925287420088368628384062431162691224281351712574817903799598150, 18710274457373161232964772297291577828975325020111226184672853453291933126654, 4727610854679916185770783972704196174269832718834302478286618739168723972207, 391658493656335765581244550581630431649204925442657752612324297688210439727],
  ![0, 1, 11456366873013124052601256687616125255499790059973349472156114059067971292111, 12546497506070752486605371633682080363370213154202290631616554940191723092928, 17950580810779858709203751035803409128575822965585088895908090985785788199981, 19210782703659662228180881315766724938815100040126117471473102970610223089610, 19283133961472982183947349431669632032905881454781304000700681676823755877729, 5122953549352923082799351597138139472596403937825606898101693789442037159855],
  ![1, 10906302493569513227529192371027284132744630826495022426368913199147779527564, 8575480302910039150211364366840981168753520410691570618056947907815168063758, 12995331881596237195610914531368448039535967171329046400738474352943107154050, 10123390380404157164498508061778927967651821381929547608542613271183984027993, 6738269535158989057229895146325270968499499491414622680466173755459936550214, 12400530198155453775057540375382201318916675861410936598647617861122040028471, 16402016655467793372107256597254846521588625113740268656772708231012940912722],
  ![1, 19996486778376624130054605180713007588431283671537008331586509353647865399363, 2839353403306734919870050351099037407963109849584649248266974139595018108431, 3126984894259506657664997487210398316554347351300646929047149528235564439827, 3887014403781132110254231669865210846820998020230520377071853874986309460031, 2245054124292321620299608080487420336431490299192631057636275208102294349058, 18616323682802470961765230279932914596158470250270004141966689012584385759793, 21881476621123478259598997766228695640743399744295753993836786929445635452200],
  ![0, 3752760165567567354579224813502217164834123157234111284803162471837102535943, 1, 21536097175044805265487531682186925234868281583832066576572270698271812107823, 9350232808409650482546354004024632510512421497052231016624977991686506027749, 3134220232766287166229239355284925351155862364088882360227336009658378548865, 6714271699869191991804335816504627210732291422993360450176072523780458926823, 7903453872521963536779936917426348712732220734112420508813874387785762549364],
  ![1, 11801650118729829855139766504299450049243766107098503821778495561366482815816, 2892709161866097273652514356665712412853913461705592722889505885559463800595, 13767805023892767685237028285879575017175876660576761569999667404053415540138, 8997393623482391522203553902406639281470132035855144885178756185471672783481, 3637330111491489497434903252105797957601247089092327302154796485217723899239, 3818163293052047592394938648144968800605718368957932167108138043908972770456, 7685192198745897339501722465777864298274801726437122210872207697711408661658],
  ![1, 15803648794703328643953297473242840535409952870433677586883004133799278088291, 12259248262522969316924309801681141316656059731009470579243701325257613255434, 5819823560402143869491100207432906551957988123710107687736743253479501283284, 8973183139036458334225631339213551187422369992133522983934305842509315415584, 6668408059836993247959823546549136026812980491246459560289759390350955575505, 5125079217283252192919978602020013707681675472177967183417221152494446988945, 20092537407634469576213236635163594067251941268729819665374100093833689074031]
]

def squareOutTable : Fin 8 → Fin 9 → Field := ![
  ![3009020363786216896458374568611060141893793250184664185608781440688144160465, 7255538898303508643455029942111632465500040410465381415981867582727282853022, 9966614367777333793638806552989879712656389953558539237124514395992299435073, 20931455985160421268131162197128680332675899956535602379591846758269320072871, 15639113044740064606926916232651090939290038288593899982904224307971806423517, 2536593524509507005104094753043122756522913005536100970467051251006601747893, 10418096144696064660880583095963852734385354231224006211438652432917064903851, 4324349917590918084718308430442774411603765360496013055315104709881653929064, 419291905087952401869822609855892237267387716774946015005131085700648139265],
  ![20763318163528416485282803781759334267969259083963103883510227548027075599842, 11561902601474311535782984343336910288931359432901419210656766982445769348919, 19344414009085460999744048698614628538625422677104184110681217803652775555281, 17719297247447266969791834854355664035956997801163010749520239403638575097113, 16296057840485413730641104407172032644014568065582762397550487246983548521547, 139962519843974835115833517522722191337966119018626987167124973407068137403, 9445084003401131955644301500272082427082712274125505427557369280489033675891, 20883130718634318256392385023734493852797767749632770105240737560832662835390, 820966752222359461280979569476528623703727751255811450252777306318137794517],
  ![6434623415606853071008492586992891416075761871914933566664072646139679736179, 2610623854635768280843001949062542394213119112116778997637327794131651641373, 5526509164452285353387218598064807500589164332729805021373800598350877830988, 19619280895326761560926075858288847660380862426905211027115587854775185448792, 19017224454145635275461451546532337594021176518215980928652123460868088777218, 13676263932343014679347415999843106063149809751481096227304475142645189500502, 16252524767331922676514991323542539099482898584579954321238304569648928405250, 960929272066334296396813086999250815041693870274438437419902279725205931920, 17472917541914794993970250093639998840434398023532990755746409004994644805296],
  ![19229605427121741224630892758389346588553330356808123469856926886817807235956, 4684093703776978943447724815735210827525546407711572274721177681409652934111, 14937411960030083261086587431090523267066939411237546637344603973680833938060, 18941823729201035260752265269976128518415816138965069551542875334699529407047, 10338194891711480300794927176745712862851083530557136181701336189319915655941, 13264365180123607979370401410641028556295326203088602456065591231854665614758, 12364814204885817663890302173036927622022596653164497388198245112906537814622, 9260938602418534451071260348225829815035843374598052639352679961064025810181, 21422006401189443987511653093540760198663664275298781058339024622514113527708],
  ![1094482630573599477792397105700407419257853989404058284635423602694441350631, 7653224813978903210127196019175431634985647017024935657710598605686327321701, 9567173049560246460070507890037126698893366565947305841041516566417837242585, 16940060291451805552343823193977005283859695877559299743781527894411637756408, 597313209635862007791378886422920449086738987217545183386666976568604848095, 17586640213792659986697225324444469998596717935690022023049394670951870306054, 16146512021573204860673294304327809394871121213336535488484038720720764552234, 12798128709473776744635648758924513666410626077971349170706411667792970646849, 3572876122861860893529584545101772548577021966955274719142350838956998350840],
  ![272498037643020218674345226812193359915470131438840999883331566491177066111, 4469529138099819647876550483749078423579971298513108078468887602123569910840, 4664546033634853905710227483314402157325780846878191698219419852250789827562, 1153206718467882074747208962717614119469556293174983091195952556899011857546, 15882618978353309135308450784872836845084674244931965239793845283656017920818, 9959741028916840552565378401019460096824264444734673856838749513933671087233, 1127773404240119580546234663891514843110923261825322829512218633883509552776, 21159516336654520880226809869546242547173739902645296742191745509908868656894, 669532953152726724026743462077360424486140413112451177795847526961253967073],
  ![11413604713085643752338683934736272232136690297253810655799679314056898981917, 17742064520434032539338673600257047962966555546771946317675728819047450289412, 20325097812880045752208822767650317530361500214514317474346732679010554977625, 4535637964461898119978145727204476146024579554060842721273075937533193952632, 15998780800515277312773242872549756644139435662158251781179645342534558579077, 20027825780372634871753538294375759721659923334536533241472153197636522489727, 4368974393292559259780096096599300244586181926428060577106299710113378206910, 10629273982069567276592121863096820521310404857847125034634597040894925054306, 2928996913674732313046249701139358093110880243046537508027658473117109687016],
  ![2814903261912687896117973563089438434563768971336393600360879549663780529645, 21527736795203972688412230414771454574482894434456970785356598744627456148332, 19878501968024868839050515004093387597747503482241718505712275242545669925084, 18375359172905797223420464971733423652611490051503280913494053172382738656093, 13395646337210319338149818227337717624451905385058449081964035343140519081148, 4770697419559184513142185669727866786105827501258626123215082564795382390396, 15350549356684183294591246199885826809757836659381408440702342280869601712012, 1068579822208091962553382250257842726222439177167036405801607484177823681126, 13156547869477674336276281991107612072901639526063096996553472659330030557836]
]

def mulLeft (row : Fin 12) (i : Fin 8) : Field := mulLeftTable row i
def mulRight (row : Fin 12) (i : Fin 8) : Field := mulLeft row i
def mulOut (k : Fin 8) (row : Fin 12) : Field := mulOutTable k row

def squareLeft (row : Fin 9) (i : Fin 8) : Field := squareLeftTable row i
def squareRight (row : Fin 9) (i : Fin 8) : Field := squareRightTable row i
def squareOut (k : Fin 8) (row : Fin 9) : Field := squareOutTable k row

end Solution.Secp256k1ScalarMulFixedBase.Sparse32
end

/- === Sparse32Algebra === -/
section
/-!
The explicit sparse multiplication maps used by the circuit.  The constants in
`Sparse32Constants` are a fixed CRT decomposition of multiplication in
`Field[t]/(t^8-t-977)`: twelve products suffice for a general product, and nine
products suffice when both inputs are equal.
-/
namespace Solution.Secp256k1ScalarMulFixedBase.Sparse32

open SmallSquare

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000

def linear8 (row : Fin 8 → Field) (a : Words Field) : Field :=
  ∑ i : Fin 8, row i * a i

def mulProducts (a b : Words Field) (row : Fin 12) : Field :=
  linear8 (mulLeft row) a * linear8 (mulRight row) b

def mulMap (a b : Words Field) (k : Fin 8) : Field :=
  ∑ row : Fin 12, mulOut k row * mulProducts a b row

def squareProducts (a : Words Field) (row : Fin 9) : Field :=
  linear8 (squareLeft row) a * linear8 (squareRight row) a

def squareMap (a : Words Field) (k : Fin 8) : Field :=
  ∑ row : Fin 9, squareOut k row * squareProducts a row

private theorem mulCoefficient : ∀ (k i j : Fin 8),
    (∑ row : Fin 12, mulOut k row * (mulLeft row i * mulRight row j)) =
      (redCoeff i j k : Field) := by
  decide

private theorem mul_expand (a b : Words Field) (k : Fin 8) :
    mulMap a b k =
      ∑ i : Fin 8, ∑ j : Fin 8,
        (∑ row : Fin 12, mulOut k row * (mulLeft row i * mulRight row j)) *
          (a i * b j) := by
  unfold mulMap mulProducts linear8
  calc
    (∑ row : Fin 12, mulOut k row *
        ((∑ i : Fin 8, mulLeft row i * a i) *
         (∑ j : Fin 8, mulRight row j * b j))) =
      ∑ row : Fin 12, ∑ j : Fin 8, ∑ i : Fin 8,
        (mulOut k row * (mulLeft row i * mulRight row j)) * (a i * b j) := by
          apply Finset.sum_congr rfl
          intro row _
          simp only [Finset.mul_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j _
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ = ∑ j : Fin 8, ∑ row : Fin 12, ∑ i : Fin 8,
        (mulOut k row * (mulLeft row i * mulRight row j)) * (a i * b j) := by
          rw [Finset.sum_comm]
    _ = ∑ j : Fin 8, ∑ i : Fin 8, ∑ row : Fin 12,
        (mulOut k row * (mulLeft row i * mulRight row j)) * (a i * b j) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.sum_comm]
    _ = ∑ i : Fin 8, ∑ j : Fin 8, ∑ row : Fin 12,
        (mulOut k row * (mulLeft row i * mulRight row j)) * (a i * b j) := by
          rw [Finset.sum_comm]
    _ = _ := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.sum_mul]

theorem mulMap_eq_sparseMul (a b : Words Field) : mulMap a b = sparseMul a b := by
  funext k
  rw [mul_expand]
  simp only [mulCoefficient, sparseMul]

private theorem squareSymCoefficient0 : ∀ (i j : Fin 8),
    (∑ row : Fin 9, squareOut 0 row * (squareLeft row i * squareRight row j)) +
      (∑ row : Fin 9, squareOut 0 row * (squareLeft row j * squareRight row i)) =
    (redCoeff i j 0 : Field) + (redCoeff j i 0 : Field) := by
  decide

private theorem squareSymCoefficient1 : ∀ (i j : Fin 8),
    (∑ row : Fin 9, squareOut 1 row * (squareLeft row i * squareRight row j)) +
      (∑ row : Fin 9, squareOut 1 row * (squareLeft row j * squareRight row i)) =
    (redCoeff i j 1 : Field) + (redCoeff j i 1 : Field) := by
  decide

private theorem squareSymCoefficient2 : ∀ (i j : Fin 8),
    (∑ row : Fin 9, squareOut 2 row * (squareLeft row i * squareRight row j)) +
      (∑ row : Fin 9, squareOut 2 row * (squareLeft row j * squareRight row i)) =
    (redCoeff i j 2 : Field) + (redCoeff j i 2 : Field) := by
  decide

private theorem squareSymCoefficient3 : ∀ (i j : Fin 8),
    (∑ row : Fin 9, squareOut 3 row * (squareLeft row i * squareRight row j)) +
      (∑ row : Fin 9, squareOut 3 row * (squareLeft row j * squareRight row i)) =
    (redCoeff i j 3 : Field) + (redCoeff j i 3 : Field) := by
  decide

private theorem squareSymCoefficient4 : ∀ (i j : Fin 8),
    (∑ row : Fin 9, squareOut 4 row * (squareLeft row i * squareRight row j)) +
      (∑ row : Fin 9, squareOut 4 row * (squareLeft row j * squareRight row i)) =
    (redCoeff i j 4 : Field) + (redCoeff j i 4 : Field) := by
  decide

private theorem squareSymCoefficient5 : ∀ (i j : Fin 8),
    (∑ row : Fin 9, squareOut 5 row * (squareLeft row i * squareRight row j)) +
      (∑ row : Fin 9, squareOut 5 row * (squareLeft row j * squareRight row i)) =
    (redCoeff i j 5 : Field) + (redCoeff j i 5 : Field) := by
  decide

private theorem squareSymCoefficient6 : ∀ (i j : Fin 8),
    (∑ row : Fin 9, squareOut 6 row * (squareLeft row i * squareRight row j)) +
      (∑ row : Fin 9, squareOut 6 row * (squareLeft row j * squareRight row i)) =
    (redCoeff i j 6 : Field) + (redCoeff j i 6 : Field) := by
  decide

private theorem squareSymCoefficient7 : ∀ (i j : Fin 8),
    (∑ row : Fin 9, squareOut 7 row * (squareLeft row i * squareRight row j)) +
      (∑ row : Fin 9, squareOut 7 row * (squareLeft row j * squareRight row i)) =
    (redCoeff i j 7 : Field) + (redCoeff j i 7 : Field) := by
  decide

private theorem squareSymCoefficient (k i j : Fin 8) :
    (∑ row : Fin 9, squareOut k row * (squareLeft row i * squareRight row j)) +
      (∑ row : Fin 9, squareOut k row * (squareLeft row j * squareRight row i)) =
    (redCoeff i j k : Field) + (redCoeff j i k : Field) := by
  fin_cases k
  · exact squareSymCoefficient0 i j
  · exact squareSymCoefficient1 i j
  · exact squareSymCoefficient2 i j
  · exact squareSymCoefficient3 i j
  · exact squareSymCoefficient4 i j
  · exact squareSymCoefficient5 i j
  · exact squareSymCoefficient6 i j
  · exact squareSymCoefficient7 i j

private theorem square_expand (a : Words Field) (k : Fin 8) :
    squareMap a k =
      ∑ i : Fin 8, ∑ j : Fin 8,
        (∑ row : Fin 9, squareOut k row * (squareLeft row i * squareRight row j)) *
          (a i * a j) := by
  unfold squareMap squareProducts linear8
  calc
    (∑ row : Fin 9, squareOut k row *
        ((∑ i : Fin 8, squareLeft row i * a i) *
         (∑ j : Fin 8, squareRight row j * a j))) =
      ∑ row : Fin 9, ∑ j : Fin 8, ∑ i : Fin 8,
        (squareOut k row * (squareLeft row i * squareRight row j)) * (a i * a j) := by
          apply Finset.sum_congr rfl
          intro row _
          simp only [Finset.mul_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j _
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ = ∑ j : Fin 8, ∑ row : Fin 9, ∑ i : Fin 8,
        (squareOut k row * (squareLeft row i * squareRight row j)) * (a i * a j) := by
          rw [Finset.sum_comm]
    _ = ∑ j : Fin 8, ∑ i : Fin 8, ∑ row : Fin 9,
        (squareOut k row * (squareLeft row i * squareRight row j)) * (a i * a j) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.sum_comm]
    _ = ∑ i : Fin 8, ∑ j : Fin 8, ∑ row : Fin 9,
        (squareOut k row * (squareLeft row i * squareRight row j)) * (a i * a j) := by
          rw [Finset.sum_comm]
    _ = _ := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.sum_mul]

private theorem twice_bilinear_sum (coeff : Fin 8 → Fin 8 → Field)
    (a : Words Field) :
    (2 : Field) * (∑ i : Fin 8, ∑ j : Fin 8, coeff i j * (a i * a j)) =
      ∑ i : Fin 8, ∑ j : Fin 8, (coeff i j + coeff j i) * (a i * a j) := by
  let S := ∑ i : Fin 8, ∑ j : Fin 8, coeff i j * (a i * a j)
  have hswap : S =
      ∑ i : Fin 8, ∑ j : Fin 8, coeff j i * (a j * a i) := by
    dsimp only [S]
    rw [Finset.sum_comm]
  calc
    (2 : Field) * S = S + S := by ring
    _ = S + ∑ i : Fin 8, ∑ j : Fin 8, coeff j i * (a j * a i) :=
      congrArg (S + ·) hswap
    _ = _ := by
      dsimp only [S]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem squareMap_eq_sparseSquare (a : Words Field) : squareMap a = sparseSquare a := by
  funext k
  rw [square_expand]
  apply mul_left_cancel₀ (by decide : (2 : Field) ≠ 0)
  rw [twice_bilinear_sum]
  simp_rw [squareSymCoefficient]
  change (∑ i : Fin 8, ∑ j : Fin 8,
      ((redCoeff i j k : Field) + (redCoeff j i k : Field)) * (a i * a j)) =
    (2 : Field) *
      (∑ i : Fin 8, ∑ j : Fin 8, (redCoeff i j k : Field) * (a i * a j))
  rw [twice_bilinear_sum]

end Solution.Secp256k1ScalarMulFixedBase.Sparse32
end

/- === Sparse32Mul === -/
section
namespace Solution.Secp256k1ScalarMulFixedBase.Sparse32Mul

open SmallSquare Sparse32 Challenge.CostR1CS Cost

set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 20000

structure Inputs (K : Type) where
  x : fields 8 K
  y : fields 8 K
deriving ProvableStruct

abbrev Outputs := fields 8

/-- An affine linear form with eight coefficients. -/
def linearExpr (row : Fin 8 → Field) (a : Var (fields 8) Field) : Expression Field :=
  Fin.foldl 8 (fun acc i => acc + row i * a[i.val]) 0

def leftExpr (input : Var Inputs Field) (row : Fin 12) : Expression Field :=
  linearExpr (mulLeft row) input.x

def rightExpr (input : Var Inputs Field) (row : Fin 12) : Expression Field :=
  linearExpr (mulRight row) input.y

def productsValue (input : Inputs Field) : fields 12 Field :=
  Vector.ofFn fun row =>
    mulProducts (fun i => input.x[i.val]) (fun i => input.y[i.val]) row

/-- Free reconstruction of the eight product coefficients from the twelve CRT products. -/
def outputExpr (products : Var (fields 12) Field) : Var Outputs Field :=
  Vector.ofFn fun k =>
    Fin.foldl 12 (fun acc row => acc + mulOut k row * products[row.val]) 0

def outputValue (products : fields 12 Field) : Outputs Field :=
  Vector.ofFn fun k => ∑ row : Fin 12, mulOut k row * products[row.val]

def main (input : Var Inputs Field) : Circuit Field (Var Outputs Field) := do
  let products ← ProvableType.witness (α := fields 12) fun env =>
    productsValue (eval env input)
  Circuit.forEach (Vector.ofFn fun row : Fin 12 =>
    leftExpr input row * rightExpr input row - products[row.val]) assertZero
  return outputExpr products

instance elaborated : ElaboratedCircuit Field Inputs Outputs main := by
  elaborate_circuit

def Assumptions (_ : Inputs Field) : Prop := True

def Spec (input : Inputs Field) (output : Outputs Field) : Prop :=
  output = Vector.ofFn fun k =>
    sparseMul (fun i => input.x[i.val]) (fun i => input.y[i.val]) k

private theorem eval_foldl_linear (env : Environment Field) :
    ∀ {n : ℕ} (coeff : Fin n → Field) (a : Fin n → Expression Field)
      (init : Expression Field),
      Expression.eval env (Fin.foldl n (fun acc i => acc + coeff i * a i) init) =
        Expression.eval env init + ∑ i : Fin n, coeff i * Expression.eval env (a i)
  | 0, _, _, init => by simp
  | n + 1, coeff, a, init => by
      rw [Fin.foldl_succ_last]
      simp only [Expression.eval]
      rw [eval_foldl_linear env (fun i => coeff i.castSucc)
        (fun i => a i.castSucc) init]
      rw [Fin.sum_univ_castSucc]
      ring

lemma eval_linearExpr (env : Environment Field) (row : Fin 8 → Field)
    (a : Var (fields 8) Field) :
    Expression.eval env (linearExpr row a) =
      linear8 row (fun i => Expression.eval env a[i.val]) := by
  rw [linearExpr, linear8, eval_foldl_linear]
  simp only [Expression.eval, zero_add]

lemma eval_leftExpr (env : Environment Field) (input : Var Inputs Field) (row : Fin 12) :
    Expression.eval env (leftExpr input row) =
      linear8 (mulLeft row) (fun i => Expression.eval env input.x[i.val]) :=
  eval_linearExpr env _ _

lemma eval_rightExpr (env : Environment Field) (input : Var Inputs Field) (row : Fin 12) :
    Expression.eval env (rightExpr input row) =
      linear8 (mulRight row) (fun i => Expression.eval env input.y[i.val]) :=
  eval_linearExpr env _ _

lemma eval_outputExpr (env : Environment Field) (products : Var (fields 12) Field) :
    Vector.map (Expression.eval env) (outputExpr products) =
      outputValue (Vector.map (Expression.eval env) products) := by
  apply Vector.ext
  intro k hk
  simp only [outputExpr, outputValue, Vector.getElem_map, Vector.getElem_ofFn]
  rw [eval_foldl_linear]
  simp only [Expression.eval, zero_add, Vector.getElem_map]

lemma outputValue_productsValue (input : Inputs Field) :
    outputValue (productsValue input) = Vector.ofFn fun k =>
      sparseMul (fun i => input.x[i.val]) (fun i => input.y[i.val]) k := by
  apply Vector.ext
  intro k hk
  simp only [outputValue, productsValue, Vector.getElem_ofFn]
  change mulMap (fun i => input.x[i.val]) (fun i => input.y[i.val]) ⟨k, hk⟩ =
    sparseMul (fun i => input.x[i.val]) (fun i => input.y[i.val]) ⟨k, hk⟩
  exact congrFun (mulMap_eq_sparseMul
    (fun i => input.x[i.val]) (fun i => input.y[i.val])) ⟨k, hk⟩

theorem soundness : Soundness Field main Assumptions Spec := by
  circuit_proof_start_core
  simp only [main, circuit_norm, Vector.getElem_ofFn] at h_holds
  have hin : eval env input_var = input := by
    simpa only [circuit_norm] using h_input
  have hx (i : Fin 8) : Expression.eval env input_var.x[i.val] = input.x[i.val] := by
    have h := congrArg (fun v : Inputs Field => v.x[i.val]) hin
    simpa only [circuit_norm] using h
  have hy (i : Fin 8) : Expression.eval env input_var.y[i.val] = input.y[i.val] := by
    have h := congrArg (fun v : Inputs Field => v.y[i.val]) hin
    simpa only [circuit_norm] using h
  have hp (row : Fin 12) : env.get (i₀ + row.val) =
      mulProducts (fun i => input.x[i.val]) (fun i => input.y[i.val]) row := by
    have h := h_holds row
    rw [eval_leftExpr, eval_rightExpr] at h
    simp only [hx, hy, neg_one_mul, add_neg_eq_zero] at h
    simpa only [mulProducts, Fin.eta] using h.symm
  have hpv : Vector.map (Expression.eval env)
      (varFromOffset (fields 12) i₀ : Var (fields 12) Field) = productsValue input := by
    apply Vector.ext
    intro row hr
    simpa only [circuit_norm, productsValue, Vector.getElem_ofFn]
      using hp ⟨row, hr⟩
  constructor
  · simp only [Spec, elaborated, main, circuit_norm]
    exact (eval_outputExpr env _).trans
      ((congrArg outputValue hpv).trans (outputValue_productsValue input))
  · simp only [main, circuit_norm]

theorem completeness : Completeness Field main Assumptions := by
  circuit_proof_start_core
  simp only [main, circuit_norm, Vector.getElem_ofFn] at h_env ⊢
  have hx (i : Fin 8) : Expression.eval env.toEnvironment input_var.x[i.val] = input.x[i.val] := by
    have h := congrArg (fun v : Inputs Field => v.x[i.val]) h_input
    simpa only [circuit_norm] using h
  have hy (i : Fin 8) : Expression.eval env.toEnvironment input_var.y[i.val] = input.y[i.val] := by
    have h := congrArg (fun v : Inputs Field => v.y[i.val]) h_input
    simpa only [circuit_norm] using h
  intro row
  have hp : env.get (i₀ + row.val) =
      mulProducts (fun i => input.x[i.val]) (fun i => input.y[i.val]) row := by
    simpa only [productsValue, Vector.getElem_ofFn, Vector.getElem_map, hx, hy]
      using h_env row
  rw [eval_leftExpr, eval_rightExpr]
  simp only [hx, hy, hp, mulProducts, Fin.eta]
  ring

def circuit : FormalCircuit Field Inputs Outputs where
  main := main
  elaborated := elaborated
  Assumptions := Assumptions
  Spec := Spec
  soundness := soundness
  completeness := completeness

def mulCost : Count := ⟨12, 12⟩

theorem costIs_main (input : Var Inputs Field) : CostIs (main input) mulCost := by
  rw [show mulCost = ⟨12, 0⟩ + (⟨12 * 0, 12 * 1⟩ + Count.zero) from by decide]
  unfold main
  refine CostIs.bind (CostIs.provableWitness _) fun _ => ?_
  refine CostIs.bind (CostIs.forEach fun a k => CostIs.assertZero _ k) fun _ => ?_
  exact CostIs.pure _

theorem costIs_call (input : Var Inputs Field) :
    CostIs (subcircuit circuit input) mulCost :=
  CostIs.subcircuit (fun n => costIs_main input n)

end Solution.Secp256k1ScalarMulFixedBase.Sparse32Mul
end

/- === Sparse32MulContract === -/
section
namespace Solution.Secp256k1ScalarMulFixedBase.Sparse32Mul

open SmallSquare Sparse32 Challenge.CostR1CS Cost
open Challenge.Utils.ComputableWitnessLemmas

set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 20000

def AffineInput (input : Var Inputs Field) : Prop :=
  AffineW input.x ∧ AffineW input.y

private theorem affine_foldl_linear :
    ∀ {n : ℕ} (coeff : Fin n → Field) (a : Fin n → Expression Field)
      (init : Expression Field), Affine init → (∀ i, Affine (a i)) →
      Affine (Fin.foldl n (fun acc i => acc + coeff i * a i) init)
  | 0, _, _, _, hinit, _ => by simpa using hinit
  | n + 1, coeff, a, init, hinit, ha => by
      rw [Fin.foldl_succ_last]
      exact Affine.add
        (affine_foldl_linear (fun i => coeff i.castSucc) (fun i => a i.castSucc)
          init hinit (fun i => ha i.castSucc))
        (Affine.fconst_mul _ (ha (Fin.last n)))

lemma affine_linearExpr (row : Fin 8 → Field) (a : Var (fields 8) Field)
    (ha : AffineW a) : Affine (linearExpr row a) := by
  apply affine_foldl_linear row (fun i => a[i.val]) 0 Affine.zero
  intro i
  exact ha i.val i.isLt

lemma affine_leftExpr (input : Var Inputs Field) (row : Fin 12)
    (hinput : AffineInput input) : Affine (leftExpr input row) :=
  affine_linearExpr _ _ hinput.1

lemma affine_rightExpr (input : Var Inputs Field) (row : Fin 12)
    (hinput : AffineInput input) : Affine (rightExpr input row) :=
  affine_linearExpr _ _ hinput.2

lemma affine_outputExpr (products : Var (fields 12) Field) (hp : AffineW products) :
    AffineW (outputExpr products) := by
  intro k hk
  rw [outputExpr, Vector.getElem_ofFn]
  apply affine_foldl_linear (mulOut ⟨k, hk⟩) (fun row => products[row.val]) 0 Affine.zero
  intro row
  exact hp row.val row.isLt

attribute [local irreducible] isR1CSRow r1csProducts operationsIsR1CS flatOperationsIsR1CS

theorem shape (input : Var Inputs Field) (hinput : AffineInput input) :
    IsR1CSCirc (main input) := by
  unfold main
  refine IsR1CSCirc.bind_out (IsR1CSCirc.provableWitness _) fun nproducts => ?_
  have hp := affineW_provableWitness_bigInt (k := 12)
    (fun env => productsValue (eval env input)) nproducts
  refine IsR1CSCirc.bind ?_ fun _ => IsR1CSCirc.pure _
  refine IsR1CSCirc.forEach_mem (α := Expression Field) fun row k => ?_
  refine IsR1CSCirc.assertZero ?_ k
  rw [Vector.getElem_ofFn]
  exact isR1CSRow_mul_sub (affine_leftExpr input row hinput)
    (affine_rightExpr input row hinput) (hp row.val row.isLt)

theorem output_eq (input : Var Inputs Field) (n : ℕ) :
    (main input).output n = outputExpr (varFromOffset (fields 12) n) := by
  simp only [main, circuit_norm]

theorem call_output (input : Var Inputs Field) (n : ℕ) :
    (subcircuit circuit input).output n = (main input).output n :=
  (elaborated.output_eq input n).symm

theorem structuralCW {Parent : TypeMap} [CircuitType Parent]
    (parentInput : Var Parent Field) (input : Var Inputs Field) (n : ℕ)
    (hin : ∀ (k : ℕ) (env env' : ProverEnvironment Field), n ≤ k →
      env.AgreesBelow k env' → eval env parentInput = eval env' parentInput →
      eval env input = eval env' input)
    (env env' : ProverEnvironment Field) :
    FormalCircuitBase.Operations.StructuralComputableWitnesses
      parentInput env env' n ((main input).operations n) := by
  simp only [main, Circuit.bind_structuralComputableWitnesses_iff,
    Circuit.provableWitness_structuralComputableWitnesses_iff,
    Circuit.forEach_structuralComputableWitnesses_iff,
    Circuit.assertZero_structuralComputableWitnesses_iff,
    Circuit.pure_structuralComputableWitnesses_iff]
  exact ⟨fun hag hp => congrArg productsValue (hin n env env' (by omega) hag hp),
    fun _ => trivial, trivial⟩

theorem computableWitnesses : circuit.ComputableWitnesses := by
  intro n input env env'
  change Operations.forAllFlat n
    (FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations n)
  exact FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
    input env env' (structuralCW input input n (fun _ _ _ _ _ hp => hp) env env')

theorem main_output_stable (input : Var Inputs Field) (n : ℕ) {k : ℕ}
    {env env' : ProverEnvironment Field} (hag : env.AgreesBelow k env')
    (hk : n + 12 ≤ k) :
    eval env ((main input).output n) = eval env' ((main input).output n) := by
  rw [output_eq]
  let products := (varFromOffset (fields 12) n : Var (fields 12) Field)
  have hp : Vector.map (Expression.eval env.toEnvironment) products =
      Vector.map (Expression.eval env'.toEnvironment) products := by
    apply Vector.ext
    intro row hr
    simp only [products, circuit_norm]
    exact hag (n + row) (by omega)
  have ho : Vector.map (Expression.eval env.toEnvironment) (outputExpr products) =
      Vector.map (Expression.eval env'.toEnvironment) (outputExpr products) :=
    (eval_outputExpr env.toEnvironment products).trans
      ((congrArg outputValue hp).trans (eval_outputExpr env'.toEnvironment products).symm)
  apply Vector.ext
  intro j hj
  rw [← ProvableType.getElem_eval_fields_prover,
    ← ProvableType.getElem_eval_fields_prover]
  simpa only [Vector.getElem_map] using congrArg (fun z : fields 8 Field => z[j]) ho

theorem output_stable (input : Var Inputs Field) (n : ℕ) {k : ℕ}
    {env env' : ProverEnvironment Field} (hag : env.AgreesBelow k env')
    (hk : n + 12 ≤ k) :
    eval env ((subcircuit circuit input).output n) =
      eval env' ((subcircuit circuit input).output n) := by
  rw [call_output]
  exact main_output_stable input n hag hk

end Solution.Secp256k1ScalarMulFixedBase.Sparse32Mul
end

/- === Sparse32WideModel === -/
section
namespace Solution.Secp256k1ScalarMulFixedBase.Sparse32Wide

open SmallSquare Sparse32 SparseX Challenge.CostR1CS Cost

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

def productHalfExpr (z : Var (fields 8) Field) (side : Bool) : Expression Field :=
  if side then
    z[4] + (H : Field) * z[5] + (H ^ 2 : Field) * z[6] + (H ^ 3 : Field) * z[7]
  else
    z[0] + (H : Field) * z[1] + (H ^ 2 : Field) * z[2] + (H ^ 3 : Field) * z[3]

lemma eval_productHalfExpr (env : Environment Field) (z : Var (fields 8) Field)
    (side : Bool) :
    Expression.eval env (productHalfExpr z side) =
      (if side then Sparse32.highHalf (fun k => (eval env z)[k.val])
        else Sparse32.lowHalf (fun k => (eval env z)[k.val])) := by
  cases side <;>
    simp only [productHalfExpr, Bool.false_eq_true, ↓reduceIte, Sparse32.lowHalf,
      Sparse32.highHalf, circuit_norm, Expression.eval]

end Solution.Secp256k1ScalarMulFixedBase.Sparse32Wide
end

end DonorFile6_13

-- Adapted donor module: UploadPart2
section DonorFile6_14

/-! Exact Sparse32Square section from accepted fixed-base donor.
Unused fixed-base window tables and step extensions are deliberately excluded. -/

namespace Solution.Secp256k1ScalarMulFixedBase.Sparse32Square

open SmallSquare Sparse32 Challenge.CostR1CS Cost

set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 20000

abbrev Inputs := fields 8
abbrev Outputs := fields 8

/-- An affine linear form with eight coefficients. -/
def linearExpr (row : Fin 8 → Field) (a : Var Inputs Field) : Expression Field :=
  Fin.foldl 8 (fun acc i => acc + row i * a[i.val]) 0

def leftExpr (a : Var Inputs Field) (row : Fin 9) : Expression Field :=
  linearExpr (squareLeft row) a

def rightExpr (a : Var Inputs Field) (row : Fin 9) : Expression Field :=
  linearExpr (squareRight row) a

def productsValue (a : Inputs Field) : fields 9 Field :=
  Vector.ofFn fun row => squareProducts (fun i => a[i.val]) row

/-- Free reconstruction of the eight square coefficients from the nine CRT products. -/
def outputExpr (products : Var (fields 9) Field) : Var Outputs Field :=
  Vector.ofFn fun k =>
    Fin.foldl 9 (fun acc row => acc + squareOut k row * products[row.val]) 0

def outputValue (products : fields 9 Field) : Outputs Field :=
  Vector.ofFn fun k => ∑ row : Fin 9, squareOut k row * products[row.val]

def main (a : Var Inputs Field) : Circuit Field (Var Outputs Field) := do
  let products ← ProvableType.witness (α := fields 9) fun env =>
    productsValue (eval env a)
  Circuit.forEach (Vector.ofFn fun row : Fin 9 =>
    leftExpr a row * rightExpr a row - products[row.val]) assertZero
  return outputExpr products

instance elaborated : ElaboratedCircuit Field Inputs Outputs main := by
  elaborate_circuit

def Assumptions (_ : Inputs Field) : Prop := True

def Spec (a : Inputs Field) (output : Outputs Field) : Prop :=
  output = Vector.ofFn fun k => sparseSquare (fun i => a[i.val]) k

private theorem eval_foldl_linear (env : Environment Field) :
    ∀ {n : ℕ} (coeff : Fin n → Field) (a : Fin n → Expression Field)
      (init : Expression Field),
      Expression.eval env (Fin.foldl n (fun acc i => acc + coeff i * a i) init) =
        Expression.eval env init + ∑ i : Fin n, coeff i * Expression.eval env (a i)
  | 0, _, _, init => by simp
  | n + 1, coeff, a, init => by
      rw [Fin.foldl_succ_last]
      simp only [Expression.eval]
      rw [eval_foldl_linear env (fun i => coeff i.castSucc)
        (fun i => a i.castSucc) init]
      rw [Fin.sum_univ_castSucc]
      ring

lemma eval_linearExpr (env : Environment Field) (row : Fin 8 → Field)
    (a : Var Inputs Field) :
    Expression.eval env (linearExpr row a) =
      linear8 row (fun i => Expression.eval env a[i.val]) := by
  rw [linearExpr, linear8, eval_foldl_linear]
  simp only [Expression.eval, zero_add]

lemma eval_leftExpr (env : Environment Field) (a : Var Inputs Field) (row : Fin 9) :
    Expression.eval env (leftExpr a row) =
      linear8 (squareLeft row) (fun i => Expression.eval env a[i.val]) :=
  eval_linearExpr env _ _

lemma eval_rightExpr (env : Environment Field) (a : Var Inputs Field) (row : Fin 9) :
    Expression.eval env (rightExpr a row) =
      linear8 (squareRight row) (fun i => Expression.eval env a[i.val]) :=
  eval_linearExpr env _ _

lemma eval_outputExpr (env : Environment Field) (products : Var (fields 9) Field) :
    Vector.map (Expression.eval env) (outputExpr products) =
      outputValue (Vector.map (Expression.eval env) products) := by
  apply Vector.ext
  intro k hk
  simp only [outputExpr, outputValue, Vector.getElem_map, Vector.getElem_ofFn]
  rw [eval_foldl_linear]
  simp only [Expression.eval, zero_add, Vector.getElem_map]

lemma outputValue_productsValue (a : Inputs Field) :
    outputValue (productsValue a) =
      Vector.ofFn fun k => sparseSquare (fun i => a[i.val]) k := by
  apply Vector.ext
  intro k hk
  simp only [outputValue, productsValue, Vector.getElem_ofFn]
  change squareMap (fun i => a[i.val]) ⟨k, hk⟩ = sparseSquare (fun i => a[i.val]) ⟨k, hk⟩
  exact congrFun (squareMap_eq_sparseSquare (fun i => a[i.val])) ⟨k, hk⟩

theorem soundness : Soundness Field main Assumptions Spec := by
  circuit_proof_start_core
  simp only [main, circuit_norm, Vector.getElem_ofFn] at h_holds
  have hin : eval env input_var = input := by
    simpa only [circuit_norm] using h_input
  have ha (i : Fin 8) : Expression.eval env input_var[i.val] = input[i.val] := by
    have h := congrArg (fun v : Inputs Field => v[i.val]) hin
    simpa only [circuit_norm] using h
  have hp (row : Fin 9) : env.get (i₀ + row.val) =
      squareProducts (fun i => input[i.val]) row := by
    have h := h_holds row
    rw [eval_leftExpr, eval_rightExpr] at h
    simp only [ha, neg_one_mul, add_neg_eq_zero] at h
    simpa only [squareProducts, Fin.eta] using h.symm
  have hpv : Vector.map (Expression.eval env)
      (varFromOffset (fields 9) i₀ : Var (fields 9) Field) = productsValue input := by
    apply Vector.ext
    intro row hr
    simpa only [circuit_norm, productsValue, Vector.getElem_ofFn]
      using hp ⟨row, hr⟩
  constructor
  · simp only [Spec, elaborated, main, circuit_norm]
    exact (eval_outputExpr env _).trans
      ((congrArg outputValue hpv).trans (outputValue_productsValue input))
  · simp only [main, circuit_norm]

theorem completeness : Completeness Field main Assumptions := by
  circuit_proof_start_core
  simp only [main, circuit_norm, Vector.getElem_ofFn] at h_env ⊢
  have ha (i : Fin 8) : Expression.eval env.toEnvironment input_var[i.val] = input[i.val] := by
    have h := congrArg (fun v : Inputs Field => v[i.val]) h_input
    simpa only [circuit_norm] using h
  intro row
  have hp : env.get (i₀ + row.val) = squareProducts (fun i => input[i.val]) row := by
    simpa only [productsValue, Vector.getElem_ofFn, Vector.getElem_map, ha] using h_env row
  rw [eval_leftExpr, eval_rightExpr]
  simp only [ha, hp, squareProducts, Fin.eta]
  ring

def circuit : FormalCircuit Field Inputs Outputs where
  main := main
  elaborated := elaborated
  Assumptions := Assumptions
  Spec := Spec
  soundness := soundness
  completeness := completeness

def squareCost : Count := ⟨9, 9⟩

theorem costIs_main (a : Var Inputs Field) : CostIs (main a) squareCost := by
  rw [show squareCost = ⟨9, 0⟩ + (⟨9 * 0, 9 * 1⟩ + Count.zero) from by decide]
  unfold main
  refine CostIs.bind (CostIs.provableWitness _) fun _ => ?_
  refine CostIs.bind (CostIs.forEach fun a k => CostIs.assertZero _ k) fun _ => ?_
  exact CostIs.pure _

theorem costIs_call (a : Var Inputs Field) :
    CostIs (subcircuit circuit a) squareCost :=
  CostIs.subcircuit (fun n => costIs_main a n)

end Solution.Secp256k1ScalarMulFixedBase.Sparse32Square

end DonorFile6_14

section DonorFile6_11

namespace Solution.Secp256k1ScalarMulFixedBase.Width12.SelectorBridge

open Select12
open Width12.Tables

end Solution.Secp256k1ScalarMulFixedBase.Width12.SelectorBridge

end DonorFile6_11

-- Adapted donor module: CombTableBridge
section DonorFile6_12

set_option maxRecDepth 2048

namespace Solution.Secp256k1ScalarMulFixedBase.Width12.Bridge

open Specs.ShortWeierstrass Specs.Secp256k1
open Solution.Secp256k1ScalarMulFixedBase.GroupLaw

end Solution.Secp256k1ScalarMulFixedBase.Width12.Bridge

namespace Solution.Secp256k1ScalarMulFixedBase
namespace CombTableBridge

open Specs.ShortWeierstrass Specs.Secp256k1
open Solution.Secp256k1ScalarMulFixedBase.GroupLaw

end CombTableBridge
end Solution.Secp256k1ScalarMulFixedBase

end DonorFile6_12
