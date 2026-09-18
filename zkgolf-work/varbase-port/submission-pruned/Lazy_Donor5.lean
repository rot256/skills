import Solution.Secp256k1ScalarMul.Lazy_Donor4

-- Adapted donor module: OrderFactsCerts
section DonorFile5_0

namespace Solution.Secp256k1ScalarMulFixedBase.OrderFactsCerts

set_option maxRecDepth 100000

end Solution.Secp256k1ScalarMulFixedBase.OrderFactsCerts

end DonorFile5_0

-- Adapted donor module: OrderChainReflect
section DonorFile5_1

namespace Solution.Secp256k1ScalarMulFixedBase.OrderChainReflect

open Specs.ShortWeierstrass Specs.Secp256k1
open Solution.Secp256k1ScalarMulFixedBase.GroupLaw
open Solution.Secp256k1ScalarMulFixedBase.TableReflect

set_option maxRecDepth 65536

def daStep (gx : Fp) (p : Point Fp) (t : Nat × Fp × Fp) : Point Fp :=
  let d := dstep p t.2.1
  if t.1 = 1 then cstep gx d t.2.2 else d

def daChecks (gx gy : Fp) : Point Fp → List (Nat × Fp × Fp) → Bool
  | _, [] => true
  | p, t :: rest =>
      let d := dstep p t.2.1
      (decide (t.1 < 2) && decide (p.y ≠ -p.y) && decide (t.2.1 * (2 * p.y) = 3 * p.x ^ 2))
        && (if t.1 = 1 then
              decide (d.x ≠ gx) && decide (t.2.2 * (gx - d.x) = gy - d.y)
            else true)
        && daChecks gx gy (daStep gx p t) rest

end Solution.Secp256k1ScalarMulFixedBase.OrderChainReflect

end DonorFile5_1

-- Adapted donor module: OrderFactsChain
section DonorFile5_2

namespace Solution.Secp256k1ScalarMulFixedBase.OrderFactsChain

open Specs.ShortWeierstrass Specs.Secp256k1
open Solution.Secp256k1ScalarMulFixedBase.GroupLaw
open Solution.Secp256k1ScalarMulFixedBase.OrderChainReflect
open Solution.Secp256k1ScalarMulFixedBase.TableReflect

set_option maxHeartbeats 4000000
set_option maxRecDepth 65536

end Solution.Secp256k1ScalarMulFixedBase.OrderFactsChain

end DonorFile5_2

-- Adapted donor module: OrderFacts
section DonorFile5_3

namespace Solution.Secp256k1ScalarMulFixedBase.OrderFacts

open Specs.ShortWeierstrass Specs.Secp256k1
open Solution.Secp256k1ScalarMulFixedBase.GroupLaw

noncomputable section

end

end Solution.Secp256k1ScalarMulFixedBase.OrderFacts

end DonorFile5_3

-- Adapted donor module: TableCerts
section DonorFile5_4

set_option maxHeartbeats 8000000
set_option maxRecDepth 65536

namespace Solution.Secp256k1ScalarMulFixedBase.TableCerts

open Specs.ShortWeierstrass Specs.Secp256k1
open Solution.Secp256k1ScalarMulFixedBase.GroupLaw
open Solution.Secp256k1ScalarMulFixedBase.TableReflect
open Solution.Secp256k1ScalarMulFixedBase.Tables

end Solution.Secp256k1ScalarMulFixedBase.TableCerts

end DonorFile5_4

-- Adapted donor module: EvenTableTop
section DonorFile5_5

set_option maxHeartbeats 4000000
set_option maxRecDepth 65536

namespace Solution.Secp256k1ScalarMulFixedBase.EvenTableTop

open Specs.ShortWeierstrass Specs.Secp256k1
open Solution.Secp256k1ScalarMulFixedBase.GroupLaw
open Solution.Secp256k1ScalarMulFixedBase.TableReflect
open Solution.Secp256k1ScalarMulFixedBase.Tables

-- even-parity top-window (4-bit) table constants, generated and validated by
-- scratchpad/gen_eventabletop.py: entry v = (2v - 15) * 2^252 * G - G.

end Solution.Secp256k1ScalarMulFixedBase.EvenTableTop

set_option maxRecDepth 65536

namespace Solution.Secp256k1ScalarMulFixedBase.Width12.Tables

open Specs.ShortWeierstrass Specs.Secp256k1
open Solution.Secp256k1ScalarMulFixedBase.TableReflect

end Solution.Secp256k1ScalarMulFixedBase.Width12.Tables

set_option maxHeartbeats 16000000
set_option maxRecDepth 65536

namespace Solution.Secp256k1ScalarMulFixedBase.Width12.TableCerts

open Specs.ShortWeierstrass Specs.Secp256k1
open Solution.Secp256k1ScalarMulFixedBase.GroupLaw
open Solution.Secp256k1ScalarMulFixedBase.TableReflect
open Solution.Secp256k1ScalarMulFixedBase.Width12.Tables

end Solution.Secp256k1ScalarMulFixedBase.Width12.TableCerts

set_option maxHeartbeats 12000000
set_option maxRecDepth 65536

namespace Solution.Secp256k1ScalarMulFixedBase.Width12.TableYNonzero

open Specs.ShortWeierstrass Specs.Secp256k1
open Solution.Secp256k1ScalarMulFixedBase.TableReflect
open Solution.Secp256k1ScalarMulFixedBase.Width12.Tables

end Solution.Secp256k1ScalarMulFixedBase.Width12.TableYNonzero

end DonorFile5_5

-- Adapted donor module: SelectTop
section DonorFile5_6

namespace Solution.Secp256k1ScalarMulFixedBase
namespace SelectTop

def bitVal (env : ProverEnvironment (F circomPrime))
    (b : Var (fields 4) (F circomPrime)) (t : ℕ) (ht : t < 4) : F circomPrime :=
  Expression.eval env.toEnvironment b[t]

def xVal (env : ProverEnvironment (F circomPrime))
    (b : Var (fields 4) (F circomPrime)) (t : ℕ) (ht : t < 3) : F circomPrime :=
  2 * bitVal env b 3 (by omega) * bitVal env b t (by omega)
    - bitVal env b 3 (by omega) - bitVal env b t (by omega) + 1

def blockVal (env : ProverEnvironment (F circomPrime))
    (b : Var (fields 4) (F circomPrime)) (v : ℕ) : F circomPrime :=
  (if v % 2 = 1 then xVal env b 0 (by omega) else 1 - xVal env b 0 (by omega))
    * (if v / 2 % 2 = 1 then xVal env b 1 (by omega)
       else 1 - xVal env b 1 (by omega))

def mVal (env : ProverEnvironment (F circomPrime))
    (b : Var (fields 4) (F circomPrime)) : ℕ :=
  (bitVal env b 0 (by omega)).val + 2 * (bitVal env b 1 (by omega)).val
    + 4 * (bitVal env b 2 (by omega)).val + 8 * (bitVal env b 3 (by omega)).val

def xExpr (b : Var (fields 4) (F circomPrime))
    (w : Var (fields 3) (F circomPrime)) (t : ℕ) (ht : t < 3) :
    Expression (F circomPrime) :=
  w[t] * (2 : F circomPrime) - b[3] - b[t]'(by omega)
    + ((1 : F circomPrime) : Expression (F circomPrime))

def xCoeff (i : Fin 4) (j : Fin 7) : F circomPrime :=
  ((limbOfNat (Tables.magXNat (28 * 256 + j.val)) i.val : ℕ) : F circomPrime) -
    ((limbOfNat (Tables.magXNat (28 * 256 + 7)) i.val : ℕ) : F circomPrime)

def xBase (i : Fin 4) : F circomPrime :=
  ((limbOfNat (Tables.magXNat (28 * 256 + 7)) i.val : ℕ) : F circomPrime)

def xSelExpr (e : Var (fields 7) (F circomPrime)) :
    Var Emu (F circomPrime) :=
  Vector.ofFn fun i : Fin 4 => Select.weightedSum e (xCoeff i) (xBase i)

/-- The positive-`y` one-hot coefficients (sign bit fixed to `1`). -/
def yCoeff (i : Fin 4) (j : Fin 7) : F circomPrime :=
  ((limbOfNat (Tables.magYNat (28 * 256 + j.val)) i.val : ℕ) : F circomPrime) -
    ((limbOfNat (Tables.magYNat (28 * 256 + 7)) i.val : ℕ) : F circomPrime)

def yBase (i : Fin 4) : F circomPrime :=
  ((limbOfNat (Tables.magYNat (28 * 256 + 7)) i.val : ℕ) : F circomPrime)

def ySelExpr (e : Var (fields 7) (F circomPrime)) :
    Var Emu (F circomPrime) :=
  Vector.ofFn fun i : Fin 4 => Select.weightedSum e (yCoeff i) (yBase i)

attribute [irreducible] ySelExpr

def main (b : Var (fields 4) (F circomPrime)) :
    Circuit (F circomPrime) (Var Select.AffPoint (F circomPrime)) := do

  let w ← ProvableType.witness (α := fields 3) fun env =>
    Vector.ofFn fun t : Fin 3 =>
      bitVal env b 3 (by omega) * bitVal env b t.val (by omega)
  Circuit.forEach (Vector.ofFn fun t : Fin 3 =>
    b[3] * (b[t.val]'(by omega)) - w[t.val]'t.isLt) assertZero

  let blk ← ProvableType.witness (α := fields 1) fun env =>
    Vector.ofFn fun _ : Fin 1 =>
      xVal env b 0 (by omega) * xVal env b 1 (by omega)
  Circuit.forEach (Vector.ofFn fun _ : Fin 1 =>
    xExpr b w 0 (by omega) * xExpr b w 1 (by omega)
      - blk[0]'(by omega)) assertZero

  let e ← ProvableType.witness (α := fields 7) fun env =>
    Vector.ofFn fun v : Fin 7 =>
      blockVal env b (v.val % 4)
        * (if v.val / 4 = 1 then xVal env b 2 (by omega)
           else 1 - xVal env b 2 (by omega))
  Circuit.forEach (Vector.ofFn fun v : Fin 7 =>
    Select.blockExpr (xExpr b w 0 (by omega)) (xExpr b w 1 (by omega)) (blk[0]'(by omega))
        (v.val % 4)
      * (if v.val / 4 = 1 then xExpr b w 2 (by omega)
         else ((1 : F circomPrime) : Expression (F circomPrime)) - xExpr b w 2 (by omega))
      - e[v.val]'v.isLt) assertZero

  return { x := xSelExpr e, y := ySelExpr e }

def Assumptions (b : fields 4 (F circomPrime)) : Prop :=
  (∀ i : Fin 4, IsBool b[i]) ∧ b[3]'(by omega) = 1

end SelectTop
end Solution.Secp256k1ScalarMulFixedBase

/-! ### merged from `TopSelect.lean` (submission file-count cap) -/

namespace Solution.Secp256k1ScalarMulFixedBase
namespace TopSelect

/-- The three nonconstant bits of the top recoded digit, together with the
original scalar parity bit.  The fourth recoded bit is definitionally one in
`Comb`, so carrying it through either old selector only duplicated work. -/
structure Inputs (F : Type) where
  bits : fields 3 F
  selector : F
deriving ProvableStruct

abbrev Field := F circomPrime

/-- The eleven nonlinear monomials of four inputs, in the order used by
`lookupExpr`. -/
def monomialAt (b0 b1 b2 selector : Field) : Nat → Field
  | 0 => b0 * b1
  | 1 => b0 * b2
  | 2 => b0 * selector
  | 3 => b1 * b2
  | 4 => b1 * selector
  | 5 => b2 * selector
  | 6 => b0 * b1 * b2
  | 7 => b0 * b1 * selector
  | 8 => b0 * b2 * selector
  | 9 => b1 * b2 * selector
  | 10 => b0 * b1 * b2 * selector
  | _ => 0

/-- R1CS equations for the eleven monomials.  Higher products are chained
through earlier witnesses, keeping every row bilinear. -/
def constraintAt (input : Var Inputs Field) (w : Var (fields 11) Field) :
    Nat → Expression Field
  | 0 => input.bits[0] * input.bits[1] - w[0]
  | 1 => input.bits[0] * input.bits[2] - w[1]
  | 2 => input.bits[0] * input.selector - w[2]
  | 3 => input.bits[1] * input.bits[2] - w[3]
  | 4 => input.bits[1] * input.selector - w[4]
  | 5 => input.bits[2] * input.selector - w[5]
  | 6 => w[0] * input.bits[2] - w[6]
  | 7 => w[0] * input.selector - w[7]
  | 8 => w[1] * input.selector - w[8]
  | 9 => w[3] * input.selector - w[9]
  | 10 => w[6] * input.selector - w[10]
  | _ => 0

end TopSelect
end Solution.Secp256k1ScalarMulFixedBase

namespace Solution.Secp256k1ScalarMulFixedBase
namespace SelectTop

section ComputableWitness
open Challenge.Utils.ComputableWitnessLemmas

end ComputableWitness

end SelectTop
end Solution.Secp256k1ScalarMulFixedBase

end DonorFile5_6

-- Adapted donor module: SelectBorrow
section DonorFile5_7

/-!
### Schoolbook borrow bits for `P256 - y`

The width-12 selector needs, for every table entry, both the positive `y` limbs
and the limbs of the canonical negation `P256 - y`.  Selecting both costs two
full four-limb lookups.  This file provides the arithmetic that lets the second
lookup be replaced by an affine expression in the first one plus the three
*borrow bits* of the schoolbook subtraction `P256 - y`, which are themselves a
single (scalar) table lookup.
-/

namespace Solution.Secp256k1ScalarMulFixedBase
namespace Borrow

/-!
#### Borrow-free negation

Every entry of the fixed-base tables satisfies `y % 2^64 ≤ P256 % 2^64`, which
is exactly the statement that the schoolbook subtraction `P256 - y` produces no
borrows at all (the three high limbs of `P256` are `2^64 - 1`, so they can never
be the source of a borrow).  That turns the sign delta into the purely affine
expression `limbOfNat P256 i - 2 * limbOfNat (P256 - y) i`, deleting the whole
packed-borrow selection column, its two witnessed bits, and their three
booleanity rows from the width-12 selector.
-/

end Borrow
end Solution.Secp256k1ScalarMulFixedBase

end DonorFile5_7

-- Adapted donor module: BorrowDerived
section DonorFile5_8

/-!
### The packed-borrow linking row is redundant

The width-12 selector delivers the three schoolbook borrow bits of `P256 - y`
as a *single* selected field element `s`, the packed value `Borrow.packedNat y`
(see `SelectBorrow.lean`).  The obvious way to unpack it is to witness three
bits `b0, b1, b2`, assert booleanity of each, and add one further *linking* row
`s = b0 + 2*b1 + 4*b2`.  That costs 3 allocations and 4 constraints.

This file records the observation that makes the linking row — and one of the
three allocations — unnecessary.  Witness only the two high bits `b1, b2` and
*define*

  `b0 := s - 2*b1 - 4*b2`

as a free affine expression.  Then `b0 + 2*b1 + 4*b2 = s` holds as a ring
identity rather than as a constraint, so the three booleanity rows on
`b0, b1, b2` already pin all three bits to the honest borrow bits.

`derived_bits_sound` is the soundness content (the constraints force the honest
values) and `derived_bits_complete` is the completeness content (the honest
values do satisfy the constraints).  Together they say that the 2-allocation /
3-constraint gadget is exactly equivalent to the 3-allocation / 4-constraint
one, which is the entire justification for the cost reduction.
-/

namespace Solution.Secp256k1ScalarMulFixedBase
namespace Borrow

end Borrow
end Solution.Secp256k1ScalarMulFixedBase

end DonorFile5_8

-- Adapted donor module: SelectCost
section DonorFile5_9

namespace Solution.Secp256k1ScalarMulFixedBase
namespace Select

open Challenge.CostR1CS
open Cost
open CompactAdd (isR1CSRow_add_mul_sub)

attribute [local irreducible] isR1CSRow r1csProducts operationsIsR1CS flatOperationsIsR1CS

end Select
end Solution.Secp256k1ScalarMulFixedBase

namespace Solution.Secp256k1ScalarMulFixedBase
namespace Select12

/-- The width-12 selector returns the production affine-point type. -/
abbrev AffPoint := Select.AffPoint

abbrev Field := F circomPrime

def bitVal (env : ProverEnvironment Field) (b : Var (fields 12) Field)
    (i : Nat) (hi : i < 12) : Field := Expression.eval env.toEnvironment b[i]

def xVal (env : ProverEnvironment Field) (b : Var (fields 12) Field)
    (i : Nat) (hi : i < 11) : Field :=
  2 * bitVal env b 11 (by omega) * bitVal env b i (by omega) -
    bitVal env b 11 (by omega) - bitVal env b i (by omega) + 1

/-- The XNOR of the sign bit with magnitude bit `i`.  It is witnessed directly
(pinned by one rank-1 row), so it is a bare wire rather than an affine rewrite of
`b[11] * b[i]`; that keeps the whole selected-x expression free of the input
bits. -/
def xExpr (_b : Var (fields 12) Field) (w : Var (fields 11) Field)
    (i : Nat) (hi : i < 11) : Expression Field :=
  w[i]'hi

/-- Low bit index of a magnitude-bit pair.  Pairs are
`(0,1),(2,3),(4,5),(7,8),(9,10)`; bit 6 is handled as a single-bit extension
of the inner one-hot, which is what makes the 7-bit inner / 4-bit outer split. -/
def pairLo : Nat → Nat
  | 0 => 0
  | 1 => 2
  | 2 => 4
  | 3 => 7
  | 4 => 9
  | _ => 0

lemma pairLo_add_lt {p : Nat} (hp : p < 5) : pairLo p + 1 < 11 := by
  match p, hp with
  | 0, _ => decide
  | 1, _ => decide
  | 2, _ => decide
  | 3, _ => decide
  | 4, _ => decide

lemma pairLo_lt {p : Nat} (hp : p < 5) : pairLo p < 11 :=
  Nat.lt_of_succ_lt (pairLo_add_lt hp)

def pairExpr (x y xy : Expression Field) (v : Nat) : Expression Field :=
  if v = 0 then 1 - x - y + xy else if v = 1 then x - xy else
  if v = 2 then y - xy else xy

def pairVal (env : ProverEnvironment Field) (b : Var (fields 12) Field)
    (p v : Nat) (hp : p < 5) : Field :=
  let x := xVal env b (pairLo p) (pairLo_lt hp)
  let y := xVal env b (pairLo p + 1) (pairLo_add_lt hp)
  (if v % 2 = 1 then x else 1-x) * (if v / 2 % 2 = 1 then y else 1-y)

def hot4Val (env : ProverEnvironment Field) (b : Var (fields 12) Field)
    (basePair v : Nat) (hp : basePair < 4) : Field :=
  pairVal env b basePair (v % 4) (by omega) *
    pairVal env b (basePair + 1) (v / 4) (by omega)

/-- Six-bit inner one-hot value (bits 0..5). -/
def hot6Val (env : ProverEnvironment Field) (b : Var (fields 12) Field)
    (v : Nat) : Field := hot4Val env b 0 (v % 16) (by omega) * pairVal env b 2 (v / 16) (by omega)

/-- One factor of a bit-pair one-hot, as an expression in the input bits. -/
def innerP (b : Var (fields 12) Field) (w : Var (fields 11) Field)
    (blk : Var (fields 5) Field) (p : Nat) (hp : p < 5) (u : Nat) : Expression Field :=
  pairExpr (xExpr b w (pairLo p) (pairLo_lt hp)) (xExpr b w (pairLo p + 1) (pairLo_add_lt hp))
    (blk[p]'hp) u

/-- A `4 x 4` one-hot from only nine products: the last row and the last column
are affine consequences of `sum_c P1 c = 1` and `sum_a P0 a = 1`.  Only the
fifteen cells `v < 15` are produced here; cell `15` is recovered by `hot4`. -/
def hot4gen (P0 P1 : Nat → Expression Field) (h : Var (fields 9) Field) (v : Nat) :
    Expression Field :=
  if ha : v % 4 < 3 then
    (if hc : v / 4 < 3 then h[v % 4 + 3 * (v / 4)]'(by omega)
     else P0 (v % 4) - h[v % 4]'(by omega) - h[v % 4 + 3]'(by omega) - h[v % 4 + 6]'(by omega))
  else
    (if hc : v / 4 < 3 then
      P1 (v / 4) - h[3 * (v / 4)]'(by omega) - h[3 * (v / 4) + 1]'(by omega)
        - h[3 * (v / 4) + 2]'(by omega)
     else 0)

/-- The forty-eight cells of the `c < 3` part of the six-bit one-hot, from
forty-five products: the `a = 15` row is affine. -/
def inner6Vec (b : Var (fields 12) Field) (w : Var (fields 11) Field)
    (blk : Var (fields 5) Field) (h : Var (fields 45) Field) : Var (fields 48) Field :=
  Vector.ofFn fun v : Fin 48 =>
    if hh : v.val % 16 < 15 then h[15 * (v.val / 16) + v.val % 16]'(by have := v.isLt; omega)
    else innerP b w blk 2 (by decide) (v.val / 16)
      - (Vector.ofFn fun a : Fin 15 =>
          h[15 * (v.val / 16) + a.val]'(by have := v.isLt; have := a.isLt; omega)).foldl (·+·) 0

/-- The sixty-four cells of the bit-6 layer, from sixty-three products. -/
def inner7Vec (b : Var (fields 12) Field) (w : Var (fields 11) Field)
    (h : Var (fields 63) Field) : Var (fields 64) Field :=
  Vector.ofFn fun v : Fin 64 =>
    if hk : v.val < 63 then h[v.val]'hk
    else xExpr b w 6 (by decide)
      - (Vector.ofFn fun a : Fin 63 => h[a.val]'a.isLt).foldl (·+·) 0

/-- The sixteenth four-bit one-hot cell is affine-derived. -/
def hot4 (blk : Var (fields 5) Field) (h : Var (fields 15) Field)
    (basePair : Nat) (hbase : basePair < 4) (v : Nat) (hv : v < 16) : Expression Field :=
  if _ : v = 15 then blk[basePair+1]'(by omega) - h[12] - h[13] - h[14]
  else h[v]'(by omega)

/-- Six-bit inner one-hot; its last pair branch is affine-derived. -/
def hot6 (blk : Var (fields 5) Field) (h4 : Var (fields 15) Field)
    (h6 : Var (fields 48) Field) (v : Nat) (_hv : v < 64) : Expression Field :=
  let a := v % 16
  let c := v / 16
  if _ : c < 3 then h6[c*16+a]'(by omega)
  else hot4 blk h4 0 (by omega) a (by omega) - h6[a] - h6[16+a] - h6[32+a]

/-- Seven-bit inner one-hot; the single bit-6 zero branch is affine-derived
from the six-bit cell. -/
def hot7 (blk : Var (fields 5) Field) (h4 : Var (fields 15) Field)
    (h6 : Var (fields 48) Field) (h7 : Var (fields 64) Field)
    (v : Nat) (_hv : v < 128) : Expression Field :=
  let a := v % 64
  if _ : v / 64 = 1 then h7[a]'(by omega)
  else hot6 blk h4 h6 a (by omega) - h7[a]'(by omega)

def inner (limb outer : Nat) (blk : Var (fields 5) Field)
    (h4 : Var (fields 15) Field) (h6 : Var (fields 48) Field) (h7 : Var (fields 64) Field)
    (table : Nat → Nat) : Expression Field :=
  (Vector.ofFn fun a : Fin 128 => hot7 blk h4 h6 h7 a.val a.isLt *
    (((limbOfNat (table (128*outer+a.val)) limb : Nat) : Field))).foldl (·+·) 0

def bitsVal (b : fields 12 Field) : Nat :=
  b[0].val + 2*b[1].val + 4*b[2].val + 8*b[3].val + 16*b[4].val +
  32*b[5].val + 64*b[6].val + 128*b[7].val + 256*b[8].val +
  512*b[9].val + 1024*b[10].val + 2048*b[11].val

/-- Scalar-quantity selection over the same outer one-hot: a single field
element, so the product array is only 15 wide. -/
def selectedE (blk : Var (fields 5) Field)
    (inner4 : Var (fields 15) Field) (inner6 : Var (fields 48) Field)
    (inner7 : Var (fields 64) Field)
    (prod : Var (fields 15) Field) (table : Nat → Nat) : Expression Field :=
  inner 0 15 blk inner4 inner6 inner7 table +
    (Vector.ofFn fun q : Fin 15 => prod[q.val]'q.isLt).foldl (·+·) 0

namespace ChannelsFree

end ChannelsFree

section ComputableWitness
open Challenge.Utils.ComputableWitnessLemmas

end ComputableWitness

end Select12
end Solution.Secp256k1ScalarMulFixedBase

namespace Solution.Secp256k1ScalarMulFixedBase.Select12
open Challenge.CostR1CS
open Cost
open CompactAdd (isR1CSRow_add_mul_sub)

attribute [local irreducible] isR1CSRow r1csProducts operationsIsR1CS flatOperationsIsR1CS

end Solution.Secp256k1ScalarMulFixedBase.Select12

end DonorFile5_9

-- Adapted donor module: SelectTheorems
section DonorFile5_10

namespace Solution.Secp256k1ScalarMulFixedBase
open Solution.Secp256k1ScalarMulFixedBase.Limbs

namespace Select

set_option maxRecDepth 2048
set_option maxHeartbeats 12800000

end Select
end Solution.Secp256k1ScalarMulFixedBase

namespace Solution.Secp256k1ScalarMulFixedBase.Select12

set_option maxRecDepth 4096
set_option maxHeartbeats 32000000

end Solution.Secp256k1ScalarMulFixedBase.Select12

namespace Solution.Secp256k1ScalarMulFixedBase.Select12

set_option maxRecDepth 4096
set_option maxHeartbeats 32000000

end Solution.Secp256k1ScalarMulFixedBase.Select12

namespace Solution.Secp256k1ScalarMulFixedBase.Select12

set_option maxRecDepth 4096
set_option maxHeartbeats 32000000

end Solution.Secp256k1ScalarMulFixedBase.Select12

namespace Solution.Secp256k1ScalarMulFixedBase.Select12

set_option maxRecDepth 4096

end Solution.Secp256k1ScalarMulFixedBase.Select12

namespace Solution.Secp256k1ScalarMulFixedBase.Select12

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

end Solution.Secp256k1ScalarMulFixedBase.Select12

namespace Solution.Secp256k1ScalarMulFixedBase.Select12

set_option maxRecDepth 4096
set_option maxHeartbeats 8000000

section ValueOneHot

/-! Value-level one-hot facts: with Boolean inputs the *witness values* computed
by the selector are the expected indicator functions.  These mirror the
constraint-level facts derived inside `soundness`, and are what the completeness
proof needs in order to discharge the borrow-bit rows. -/

variable {env : ProverEnvironment Field} {b : Var (fields 12) Field} {input : fields 12 Field}

end ValueOneHot

end Solution.Secp256k1ScalarMulFixedBase.Select12

namespace Solution.Secp256k1ScalarMulFixedBase
namespace Select12

end Select12
end Solution.Secp256k1ScalarMulFixedBase

end DonorFile5_10

-- Adapted donor module: SelectTopTheorems
section DonorFile5_11

namespace Solution.Secp256k1ScalarMulFixedBase
open Solution.Secp256k1ScalarMulFixedBase.Limbs

namespace SelectTop

set_option maxRecDepth 2048
set_option maxHeartbeats 1600000

end SelectTop
end Solution.Secp256k1ScalarMulFixedBase

/-! ### merged from `TopSelectTheorems.lean` (submission file-count cap) -/

namespace Solution.Secp256k1ScalarMulFixedBase
namespace TopSelect

set_option maxRecDepth 4096
set_option maxHeartbeats 3200000

end TopSelect
end Solution.Secp256k1ScalarMulFixedBase

end DonorFile5_11

-- Adapted donor module: SelectTopCircuit
section DonorFile5_12

namespace Solution.Secp256k1ScalarMulFixedBase
namespace SelectTop

set_option maxRecDepth 4096

end SelectTop
end Solution.Secp256k1ScalarMulFixedBase

/-! ### merged from `TopSelectCircuit.lean` (submission file-count cap) -/

namespace Solution.Secp256k1ScalarMulFixedBase
namespace TopSelect

end TopSelect
end Solution.Secp256k1ScalarMulFixedBase

end DonorFile5_12

-- Adapted donor module: CWHelpers
section DonorFile5_13

namespace Solution.Secp256k1ScalarMulFixedBase
namespace CWHelpers

open Challenge.Utils.ComputableWitnessLemmas

theorem assertion_structuralComputableWitnesses_of_condition {Parent Input : TypeMap}
    [CircuitType Parent] [ProvableType Input]
    (circuit : FormalAssertion (F circomPrime) Input) (parentInput : Var Parent (F circomPrime))
    (input : Var Input (F circomPrime)) (n : ℕ)
    (hinput : ∀ (k : ℕ) (env env' : ProverEnvironment (F circomPrime)),
      n ≤ k →
      env.AgreesBelow k env' →
      eval env parentInput = eval env' parentInput → eval env input = eval env' input)
    (hcircuit : circuit.ComputableWitnesses) :
    ∀ env env',
      FormalCircuitBase.Operations.StructuralComputableWitnesses
        parentInput env env' n ((assertion circuit input).operations n) := by
  intro env env'
  rw [FormalAssertion.assertion_structuralComputableWitnesses_iff]
  exact FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
    circuit parentInput input n hinput hcircuit env env'

end CWHelpers
end Solution.Secp256k1ScalarMulFixedBase

/-! ### merged from `TopSelectCW.lean` (submission file-count cap) -/

namespace Solution.Secp256k1ScalarMulFixedBase
namespace TopSelect

open Challenge.Utils.ComputableWitnessLemmas

end TopSelect
end Solution.Secp256k1ScalarMulFixedBase

end DonorFile5_13

-- Adapted donor module: Select13Cost
section DonorFile5_14

namespace Solution.Secp256k1ScalarMulFixedBase
namespace Select13

/-- The width-12 selector returns the production affine-point type. -/
abbrev AffPoint := Select.AffPoint

abbrev Field := F circomPrime

def bitVal (env : ProverEnvironment Field) (b : Var (fields 13) Field)
    (i : Nat) (hi : i < 13) : Field := Expression.eval env.toEnvironment b[i]

def xVal (env : ProverEnvironment Field) (b : Var (fields 13) Field)
    (i : Nat) (hi : i < 12) : Field :=
  2 * bitVal env b 12 (by omega) * bitVal env b i (by omega) -
    bitVal env b 12 (by omega) - bitVal env b i (by omega) + 1

/-- The XNOR of the sign bit with magnitude bit `i`.  It is witnessed directly
(pinned by one rank-1 row), so it is a bare wire rather than an affine rewrite of
`b[12] * b[i]`; that keeps the whole selected-x expression free of the input
bits. -/
def xExpr (_b : Var (fields 13) Field) (w : Var (fields 12) Field)
    (i : Nat) (hi : i < 12) : Expression Field :=
  w[i]'hi

/-- Low bit index of a magnitude-bit pair.  Pairs are
`(0,1),(2,3),(4,5),(7,8),(9,10)`; bit 6 is handled as a single-bit extension
of the inner one-hot, which is what makes the 7-bit inner / 4-bit outer split. -/
def pairLo : Nat → Nat
  | 0 => 0
  | 1 => 2
  | 2 => 4
  | 3 => 7
  | 4 => 9
  | _ => 0

lemma pairLo_add_lt {p : Nat} (hp : p < 5) : pairLo p + 1 < 12 := by
  match p, hp with
  | 0, _ => decide
  | 1, _ => decide
  | 2, _ => decide
  | 3, _ => decide
  | 4, _ => decide

lemma pairLo_lt {p : Nat} (hp : p < 5) : pairLo p < 12 :=
  Nat.lt_of_succ_lt (pairLo_add_lt hp)

def pairExpr (x y xy : Expression Field) (v : Nat) : Expression Field :=
  if v = 0 then 1 - x - y + xy else if v = 1 then x - xy else
  if v = 2 then y - xy else xy

def pairVal (env : ProverEnvironment Field) (b : Var (fields 13) Field)
    (p v : Nat) (hp : p < 5) : Field :=
  let x := xVal env b (pairLo p) (pairLo_lt hp)
  let y := xVal env b (pairLo p + 1) (pairLo_add_lt hp)
  (if v % 2 = 1 then x else 1-x) * (if v / 2 % 2 = 1 then y else 1-y)

def hot4Val (env : ProverEnvironment Field) (b : Var (fields 13) Field)
    (basePair v : Nat) (hp : basePair < 4) : Field :=
  pairVal env b basePair (v % 4) (by omega) *
    pairVal env b (basePair + 1) (v / 4) (by omega)

/-- Six-bit inner one-hot value (bits 0..5). -/
def hot6Val (env : ProverEnvironment Field) (b : Var (fields 13) Field)
    (v : Nat) : Field := hot4Val env b 0 (v % 16) (by omega) * pairVal env b 2 (v / 16) (by omega)

/-- Seven-bit inner one-hot value (bits 0..6); the extension multiplies the
six-bit cell by the single bit-6 factor. -/
def hot7Val (env : ProverEnvironment Field) (b : Var (fields 13) Field)
    (v : Nat) : Field := hot6Val env b (v % 64) *
      (if v / 64 = 1 then xVal env b 6 (by omega) else 1 - xVal env b 6 (by omega))

/-- Five-bit outer one-hot value (bits 7..11); the extension multiplies the
four-bit outer cell by the single bit-11 factor. -/
def hot5Val (env : ProverEnvironment Field) (b : Var (fields 13) Field)
    (v : Nat) : Field := hot4Val env b 3 (v % 16) (by omega) *
      (if v / 16 = 1 then xVal env b 11 (by omega) else 1 - xVal env b 11 (by omega))

/-- One factor of a bit-pair one-hot, as an expression in the input bits. -/
def innerP (b : Var (fields 13) Field) (w : Var (fields 12) Field)
    (blk : Var (fields 5) Field) (p : Nat) (hp : p < 5) (u : Nat) : Expression Field :=
  pairExpr (xExpr b w (pairLo p) (pairLo_lt hp)) (xExpr b w (pairLo p + 1) (pairLo_add_lt hp))
    (blk[p]'hp) u

/-- A `4 x 4` one-hot from only nine products: the last row and the last column
are affine consequences of `sum_c P1 c = 1` and `sum_a P0 a = 1`.  Only the
fifteen cells `v < 15` are produced here; cell `15` is recovered by `hot4`. -/
def hot4gen (P0 P1 : Nat → Expression Field) (h : Var (fields 9) Field) (v : Nat) :
    Expression Field :=
  if ha : v % 4 < 3 then
    (if hc : v / 4 < 3 then h[v % 4 + 3 * (v / 4)]'(by omega)
     else P0 (v % 4) - h[v % 4]'(by omega) - h[v % 4 + 3]'(by omega) - h[v % 4 + 6]'(by omega))
  else
    (if hc : v / 4 < 3 then
      P1 (v / 4) - h[3 * (v / 4)]'(by omega) - h[3 * (v / 4) + 1]'(by omega)
        - h[3 * (v / 4) + 2]'(by omega)
     else 0)

/-- The fifteen derived cells of the four-bit one-hot on pairs `p`, `p+1`. -/
def hot4Vec (b : Var (fields 13) Field) (w : Var (fields 12) Field)
    (blk : Var (fields 5) Field) (p : Nat) (hp : p < 4) (h : Var (fields 9) Field) :
    Var (fields 15) Field :=
  Vector.ofFn fun v : Fin 15 =>
    hot4gen (innerP b w blk p (by omega)) (innerP b w blk (p + 1) (by omega)) h v.val

/-- The forty-eight cells of the `c < 3` part of the six-bit one-hot, from
forty-five products: the `a = 15` row is affine. -/
def inner6Vec (b : Var (fields 13) Field) (w : Var (fields 12) Field)
    (blk : Var (fields 5) Field) (h : Var (fields 45) Field) : Var (fields 48) Field :=
  Vector.ofFn fun v : Fin 48 =>
    if hh : v.val % 16 < 15 then h[15 * (v.val / 16) + v.val % 16]'(by have := v.isLt; omega)
    else innerP b w blk 2 (by decide) (v.val / 16)
      - (Vector.ofFn fun a : Fin 15 =>
          h[15 * (v.val / 16) + a.val]'(by have := v.isLt; have := a.isLt; omega)).foldl (·+·) 0

/-- The sixty-four cells of the bit-6 layer, from sixty-three products. -/
def inner7Vec (b : Var (fields 13) Field) (w : Var (fields 12) Field)
    (h : Var (fields 63) Field) : Var (fields 64) Field :=
  Vector.ofFn fun v : Fin 64 =>
    if hk : v.val < 63 then h[v.val]'hk
    else xExpr b w 6 (by decide)
      - (Vector.ofFn fun a : Fin 63 => h[a.val]'a.isLt).foldl (·+·) 0

/-- The sixteen cells of the bit-11 outer layer, from fifteen products. -/
def outer5Vec (b : Var (fields 13) Field) (w : Var (fields 12) Field)
    (h : Var (fields 15) Field) : Var (fields 16) Field :=
  Vector.ofFn fun v : Fin 16 =>
    if hk : v.val < 15 then h[v.val]'hk
    else xExpr b w 11 (by decide)
      - (Vector.ofFn fun a : Fin 15 => h[a.val]'a.isLt).foldl (·+·) 0

/-- The sixteenth four-bit one-hot cell is affine-derived. -/
def hot4 (blk : Var (fields 5) Field) (h : Var (fields 15) Field)
    (basePair : Nat) (hbase : basePair < 4) (v : Nat) (hv : v < 16) : Expression Field :=
  if _ : v = 15 then blk[basePair+1]'(by omega) - h[12] - h[13] - h[14]
  else h[v]'(by omega)

/-- Six-bit inner one-hot; its last pair branch is affine-derived. -/
def hot6 (blk : Var (fields 5) Field) (h4 : Var (fields 15) Field)
    (h6 : Var (fields 48) Field) (v : Nat) (_hv : v < 64) : Expression Field :=
  let a := v % 16
  let c := v / 16
  if _ : c < 3 then h6[c*16+a]'(by omega)
  else hot4 blk h4 0 (by omega) a (by omega) - h6[a] - h6[16+a] - h6[32+a]

/-- Seven-bit inner one-hot; the single bit-6 zero branch is affine-derived
from the six-bit cell. -/
def hot7 (blk : Var (fields 5) Field) (h4 : Var (fields 15) Field)
    (h6 : Var (fields 48) Field) (h7 : Var (fields 64) Field)
    (v : Nat) (_hv : v < 128) : Expression Field :=
  let a := v % 64
  if _ : v / 64 = 1 then h7[a]'(by omega)
  else hot6 blk h4 h6 a (by omega) - h7[a]'(by omega)

/-- Five-bit outer one-hot; the single bit-11 zero branch is affine-derived
from the four-bit outer cell. -/
def hot5 (blk : Var (fields 5) Field) (h4o : Var (fields 15) Field)
    (h5 : Var (fields 16) Field) (v : Nat) (_hv : v < 32) : Expression Field :=
  let a := v % 16
  if _ : v / 16 = 1 then h5[a]'(by omega)
  else hot4 blk h4o 3 (by omega) a (by omega) - h5[a]'(by omega)

def inner (limb outer : Nat) (blk : Var (fields 5) Field)
    (h4 : Var (fields 15) Field) (h6 : Var (fields 48) Field) (h7 : Var (fields 64) Field)
    (table : Nat → Nat) : Expression Field :=
  (Vector.ofFn fun a : Fin 128 => hot7 blk h4 h6 h7 a.val a.isLt *
    (((limbOfNat (table (128*outer+a.val)) limb : Nat) : Field))).foldl (·+·) 0

def innerVal (env : ProverEnvironment Field) (b : Var (fields 13) Field)
    (limb outer : Nat) (table : Nat → Nat) : Field :=
  ∑ a : Fin 128, hot7Val env b a.val *
    (((limbOfNat (table (128*outer+a.val)) limb : Nat) : Field))

/-- The free affine correction produced by pairing two one-hot terms into a
single rank-2 row.  Because the inner one-hot cells are orthogonal idempotents,
`inner o0 * inner o1` collapses to this linear combination of the same cells
with compile-time coefficients. -/
def corrC (limb o0 o1 : Nat) (blk : Var (fields 5) Field)
    (h4 : Var (fields 15) Field) (h6 : Var (fields 48) Field) (h7 : Var (fields 64) Field)
    (table : Nat → Nat) : Expression Field :=
  (Vector.ofFn fun a : Fin 128 => hot7 blk h4 h6 h7 a.val a.isLt *
    ((((limbOfNat (table (128*o0+a.val)) limb : Nat) : Field)) *
      (((limbOfNat (table (128*o1+a.val)) limb : Nat) : Field)))).foldl (·+·) 0

def corrVal (env : ProverEnvironment Field) (b : Var (fields 13) Field)
    (limb o0 o1 : Nat) (table : Nat → Nat) : Field :=
  ∑ a : Fin 128, hot7Val env b a.val *
    ((((limbOfNat (table (128*o0+a.val)) limb : Nat) : Field)) *
      (((limbOfNat (table (128*o1+a.val)) limb : Nat) : Field)))

/-- The value pinned by one rank-2 row of the **single-stage** outer
contraction: it carries two of the *sixteen* outer one-hot terms for one
product.  Because the two outer cells `2k` and `2k+1` differ in exactly one
boolean factor their product vanishes, and because the inner one-hot cells are
orthogonal idempotents the remaining cross term collapses to the free affine
correction `corrVal`. -/
def outProdVal (env : ProverEnvironment Field) (b : Var (fields 13) Field)
    (limb k : Nat) (table : Nat → Nat) : Field :=
  (hot5Val env b (2*k) + innerVal env b limb (2*k+1) table) *
    (hot5Val env b (2*k+1) + innerVal env b limb (2*k) table)
    - corrVal env b limb (2*k) (2*k+1) table

def selected2 (limb : Nat) (hl : limb < 4) (_blk : Var (fields 5) Field)
    (_h4 : Var (fields 15) Field) (_h6 : Var (fields 48) Field) (_h7 : Var (fields 64) Field)
    (pA : Var (fields 64) Field) (_table : Nat → Nat) :
    Expression Field :=
  (Vector.ofFn fun k : Fin 16 =>
    pA[16 * limb + k.val]'(by have := k.isLt; omega)).foldl (·+·) 0

/-- The selected x-coordinate is already affine in the selector witnesses, so
return it directly instead of materializing four redundant output witnesses. -/
def xSelExpr (xTable : Nat → Nat) (blk : Var (fields 5) Field)
    (inner4 : Var (fields 15) Field) (inner6 : Var (fields 48) Field)
    (inner7 : Var (fields 64) Field) (pA : Var (fields 64) Field) :
    Var Emu Field :=
  Vector.ofFn fun i : Fin 4 =>
    selected2 i.val i.isLt blk inner4 inner6 inner7 pA xTable

namespace ChannelsFree

end ChannelsFree

section ComputableWitness
open Challenge.Utils.ComputableWitnessLemmas

end ComputableWitness

end Select13
end Solution.Secp256k1ScalarMulFixedBase

namespace Solution.Secp256k1ScalarMulFixedBase.Select13
open Challenge.CostR1CS
open Cost
open CompactAdd (isR1CSRow_add_mul_sub)

attribute [local irreducible] isR1CSRow r1csProducts operationsIsR1CS flatOperationsIsR1CS

end Solution.Secp256k1ScalarMulFixedBase.Select13

end DonorFile5_14

-- Adapted donor module: SelectTheorems13
section DonorFile5_15

namespace Solution.Secp256k1ScalarMulFixedBase.Select13

set_option maxRecDepth 4096
set_option maxHeartbeats 32000000

end Solution.Secp256k1ScalarMulFixedBase.Select13

namespace Solution.Secp256k1ScalarMulFixedBase.Select13

set_option maxRecDepth 4096
set_option maxHeartbeats 32000000

end Solution.Secp256k1ScalarMulFixedBase.Select13

namespace Solution.Secp256k1ScalarMulFixedBase.Select13

set_option maxRecDepth 4096
set_option maxHeartbeats 32000000

end Solution.Secp256k1ScalarMulFixedBase.Select13

namespace Solution.Secp256k1ScalarMulFixedBase.Select13

set_option maxRecDepth 4096

end Solution.Secp256k1ScalarMulFixedBase.Select13

namespace Solution.Secp256k1ScalarMulFixedBase.Select13

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
end Solution.Secp256k1ScalarMulFixedBase.Select13

namespace Solution.Secp256k1ScalarMulFixedBase.Select13

set_option maxRecDepth 4096
set_option maxHeartbeats 8000000

section ValueOneHot

/-! Value-level one-hot facts: with Boolean inputs the *witness values* computed
by the selector are the expected indicator functions.  These mirror the
constraint-level facts derived inside `soundness`, and are what the completeness
proof needs in order to discharge the borrow-bit rows. -/

variable {env : ProverEnvironment Field} {b : Var (fields 13) Field} {input : fields 13 Field}

end ValueOneHot

end Solution.Secp256k1ScalarMulFixedBase.Select13

namespace Solution.Secp256k1ScalarMulFixedBase
namespace Select13

end Select13
end Solution.Secp256k1ScalarMulFixedBase

end DonorFile5_15
