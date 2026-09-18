import Solution.Secp256k1ScalarMul.Normalize
import Solution.Secp256k1ScalarMul.Params

/-!
# Affine negation of a canonical secp256k1 y-coordinate: circuit definitions

The result limbs are affine expressions.  The only new cells are three radix
borrow bits; four ordinary `Normalize` calls establish their 64-bit bounds.
-/

namespace Solution.Secp256k1ScalarMul
namespace NegYAffine

open Specs.ShortWeierstrass Specs.Secp256k1

def radix : ℕ := 2 ^ limbBits
def p0 : ℕ := 18446744069414583343
def pHi : ℕ := 18446744073709551615

def qExpr (P : Var FlaggedPoint (F circomPrime)) : Expression (F circomPrime) :=
  1 - P.isInf

def borrowFlag (pd y cin : ℕ) : Bool :=
  decide (y + cin > pd)

def borrow (pd y cin : ℕ) : ℕ :=
  if borrowFlag pd y cin then 1 else 0

def boolField (c : Bool) : F circomPrime :=
  if c then 1 else 0

def borrowField (pd y cin : ℕ) : F circomPrime :=
  boolField (borrowFlag pd y cin)

def qNatFrom (P : FlaggedPoint (F circomPrime)) : ℕ := (1 - P.isInf).val

def yNatFrom (P : FlaggedPoint (F circomPrime)) (i : Fin numLimbs) : ℕ := P.y[i].val

def c0NatFrom (P : FlaggedPoint (F circomPrime)) : ℕ :=
  borrow (qNatFrom P * p0) (yNatFrom P 0) 0

def c1NatFrom (P : FlaggedPoint (F circomPrime)) : ℕ :=
  borrow (qNatFrom P * pHi) (yNatFrom P 1) (c0NatFrom P)

def c2NatFrom (P : FlaggedPoint (F circomPrime)) : ℕ :=
  borrow (qNatFrom P * pHi) (yNatFrom P 2) (c1NatFrom P)

def carryNatFrom (P : FlaggedPoint (F circomPrime)) : ℕ → ℕ
  | 0 => c0NatFrom P
  | 1 => c1NatFrom P
  | _ => c2NatFrom P

def carryPdFrom (P : FlaggedPoint (F circomPrime)) (i : ℕ) : ℕ := match i with
  | 0 => qNatFrom P * p0
  | _ => qNatFrom P * pHi

def carryYFrom (P : FlaggedPoint (F circomPrime)) (i : ℕ) : ℕ := match i with
  | 0 => yNatFrom P 0
  | 1 => yNatFrom P 1
  | _ => yNatFrom P 2

def carryCinFrom (P : FlaggedPoint (F circomPrime)) (i : ℕ) : ℕ := match i with
  | 0 => 0
  | 1 => c0NatFrom P
  | _ => c1NatFrom P

def qNat (P : Var FlaggedPoint (F circomPrime))
    (env : ProverEnvironment (F circomPrime)) : ℕ := qNatFrom (eval env P)

def yNat (P : Var FlaggedPoint (F circomPrime))
    (env : ProverEnvironment (F circomPrime)) (i : Fin numLimbs) : ℕ :=
  yNatFrom (eval env P) i

def c0Nat (P : Var FlaggedPoint (F circomPrime))
    (env : ProverEnvironment (F circomPrime)) : ℕ := c0NatFrom (eval env P)

def c1Nat (P : Var FlaggedPoint (F circomPrime))
    (env : ProverEnvironment (F circomPrime)) : ℕ := c1NatFrom (eval env P)

def c2Nat (P : Var FlaggedPoint (F circomPrime))
    (env : ProverEnvironment (F circomPrime)) : ℕ := c2NatFrom (eval env P)

def carryNat (P : Var FlaggedPoint (F circomPrime))
    (env : ProverEnvironment (F circomPrime)) (i : ℕ) : ℕ := carryNatFrom (eval env P) i

def carryPd (P : Var FlaggedPoint (F circomPrime)) (i : ℕ)
    (env : ProverEnvironment (F circomPrime)) : ℕ := carryPdFrom (eval env P) i

def carryY (P : Var FlaggedPoint (F circomPrime)) (i : ℕ)
    (env : ProverEnvironment (F circomPrime)) : ℕ := carryYFrom (eval env P) i

def carryCin (P : Var FlaggedPoint (F circomPrime)) (i : ℕ)
    (env : ProverEnvironment (F circomPrime)) : ℕ := carryCinFrom (eval env P) i

def carryFlag (P : Var FlaggedPoint (F circomPrime)) (i : ℕ)
    (env : ProverEnvironment (F circomPrime)) : Bool :=
  borrowFlag (carryPd P i env) (carryY P i env) (carryCin P i env)

def carryComputeFrom (P : FlaggedPoint (F circomPrime)) (i : ℕ) : F circomPrime :=
  borrowField (carryPdFrom P i) (carryYFrom P i) (carryCinFrom P i)

def carryCompute (P : Var FlaggedPoint (F circomPrime)) (i : ℕ)
    (env : ProverEnvironment (F circomPrime)) : F circomPrime :=
  carryComputeFrom (eval env P) i

def carry0ComputeFrom (P : FlaggedPoint (F circomPrime)) : F circomPrime :=
  borrowField (qNatFrom P * p0) (yNatFrom P 0) 0

def carry1ComputeFrom (P : FlaggedPoint (F circomPrime)) : F circomPrime :=
  borrowField (qNatFrom P * pHi) (yNatFrom P 1) (c0NatFrom P)

def carry2ComputeFrom (P : FlaggedPoint (F circomPrime)) : F circomPrime :=
  borrowField (qNatFrom P * pHi) (yNatFrom P 2) (c1NatFrom P)

def carry0Compute (P : Var FlaggedPoint (F circomPrime))
    (env : ProverEnvironment (F circomPrime)) : F circomPrime :=
  carry0ComputeFrom (eval env P)

def carry1Compute (P : Var FlaggedPoint (F circomPrime))
    (env : ProverEnvironment (F circomPrime)) : F circomPrime :=
  carry1ComputeFrom (eval env P)

def carry2Compute (P : Var FlaggedPoint (F circomPrime))
    (env : ProverEnvironment (F circomPrime)) : F circomPrime :=
  carry2ComputeFrom (eval env P)

/-- The limb-1 borrow indicator, as a field difference.  Because `p1 = 2^64 - 1`,
a borrow out of limb 1 happens exactly when `y[1] + c0 = 2^64`, i.e. exactly when
this difference vanishes. -/
def d1From (P : FlaggedPoint (F circomPrime)) : F circomPrime :=
  P.y[1] + carry0ComputeFrom P - (radix : F circomPrime)

def zc1From (P : FlaggedPoint (F circomPrime)) : F circomPrime :=
  if d1From P = 0 then 1 else 0

def inv1From (P : FlaggedPoint (F circomPrime)) : F circomPrime :=
  if d1From P = 0 then 0 else (d1From P)⁻¹

def d2From (P : FlaggedPoint (F circomPrime)) : F circomPrime :=
  P.y[2] + zc1From P - (radix : F circomPrime)

def zc2From (P : FlaggedPoint (F circomPrime)) : F circomPrime :=
  if d2From P = 0 then 1 else 0

def inv2From (P : FlaggedPoint (F circomPrime)) : F circomPrime :=
  if d2From P = 0 then 0 else (d2From P)⁻¹

def zc1Compute (P : Var FlaggedPoint (F circomPrime))
    (env : ProverEnvironment (F circomPrime)) : F circomPrime :=
  zc1From (eval env P)

def inv1Compute (P : Var FlaggedPoint (F circomPrime))
    (env : ProverEnvironment (F circomPrime)) : F circomPrime :=
  inv1From (eval env P)

def zc2Compute (P : Var FlaggedPoint (F circomPrime))
    (env : ProverEnvironment (F circomPrime)) : F circomPrime :=
  zc2From (eval env P)

def inv2Compute (P : Var FlaggedPoint (F circomPrime))
    (env : ProverEnvironment (F circomPrime)) : F circomPrime :=
  inv2From (eval env P)

/-- `y[1] + c0 - 2^64`, as a circuit expression. -/
def d1Expr (P : Var FlaggedPoint (F circomPrime)) (c0 : Expression (F circomPrime)) :
    Expression (F circomPrime) :=
  P.y[1] + c0 - Expression.const ((radix : ℕ) : F circomPrime)

/-- `y[2] + c1 - 2^64`, as a circuit expression. -/
def d2Expr (P : Var FlaggedPoint (F circomPrime)) (c1 : Expression (F circomPrime)) :
    Expression (F circomPrime) :=
  P.y[2] + c1 - Expression.const ((radix : ℕ) : F circomPrime)

def result (P : Var FlaggedPoint (F circomPrime))
    (c0 c1 c2 : Expression (F circomPrime)) : Var Emu (F circomPrime) :=
  #v[
    qExpr P * (p0 : F circomPrime) + (radix : F circomPrime) * c0 - P.y[0],
    qExpr P * (pHi : F circomPrime) + (radix : F circomPrime) * c1 - P.y[1] - c0,
    qExpr P * (pHi : F circomPrime) + (radix : F circomPrime) * c2 - P.y[2] - c1,
    qExpr P * (pHi : F circomPrime) - P.y[3] - c2]

def main (P : Var FlaggedPoint (F circomPrime)) :
    Circuit (F circomPrime) (Var Emu (F circomPrime)) := do
  let c0 ← witnessField (carry0Compute P)
  let v1 ← witnessField (inv1Compute P)
  let c1 ← witnessField (zc1Compute P)
  let v2 ← witnessField (inv2Compute P)
  let c2 ← witnessField (zc2Compute P)
  assertZero (c0 * (c0 - 1))
  assertZero (c1 - 1 + d1Expr P c0 * v1)
  assertZero (d1Expr P c0 * c1)
  assertZero (c2 - 1 + d2Expr P c1 * v2)
  assertZero (d2Expr P c1 * c2)
  let r := result P c0 c1 c2
  RangeCheck.circuit secpParams.B secpParams.hB secpParams.hB1 r[0]
  return r

instance elaborated : ElaboratedCircuit (F circomPrime) FlaggedPoint Emu main := by
  elaborate_circuit

/-- Validity alone does not canonicalize coordinates of infinity. -/
def Assumptions (P : FlaggedPoint (F circomPrime)) : Prop :=
  P.Valid ∧ (P.isInf = 1 → P.y = emuOfNat 0)

def Spec (P : FlaggedPoint (F circomPrime)) (out : Emu (F circomPrime)) : Prop :=
  Fe.Valid out ∧ decodeFe out = -decodeFe P.y

end NegYAffine
end Solution.Secp256k1ScalarMul
