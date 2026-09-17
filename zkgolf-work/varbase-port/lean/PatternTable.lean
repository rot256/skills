import Solution.Secp256k1ScalarMul.GLVBuildTable

/-!
# Sign-pattern table `E(b) = Σ_j (2 b_j − 1) B_j`

Built from the signed bases `r0..r3` of `GLVBuildTable.Prepare`:
`u± = r0 ± r1`, `v± = r2 ± r3` (four `PhiPairAdd`), the eight entries with
`b_0 = 1` as `u± + (±v±)` (eight `CompleteAdd`), and the remaining eight as
negations (`NegYAffine`).  Entry `t` has bit `j` set iff `+B_j`.
-/

namespace Solution.Secp256k1ScalarMul.PatTable

open Specs.ShortWeierstrass Specs.Secp256k1
open GLVBuildTable

/-- `+P` for a set bit, `−P` for a clear bit. -/
def pickG (b : Bool) (P : GroupPoint Fp) : GroupPoint Fp := if b then P else negGP P

def patPoint (B : Fin 4 → GroupPoint Fp) (t : ℕ) : GroupPoint Fp :=
  add curve (add curve (pickG (bitAt t 0) (B 0)) (pickG (bitAt t 1) (B 1)))
    (add curve (pickG (bitAt t 2) (B 2)) (pickG (bitAt t 3) (B 3)))

/-! ### Circuit -/

def withY (P : Var FlaggedPoint (F circomPrime)) (y : Var Emu (F circomPrime)) :
    Var FlaggedPoint (F circomPrime) :=
  { x := P.x, y := y, isInf := P.isInf }

def withXY (P : Var FlaggedPoint (F circomPrime)) (x y : Var Emu (F circomPrime)) :
    Var FlaggedPoint (F circomPrime) :=
  { x := x, y := y, isInf := P.isInf }

/-- Canonicalise both coordinates of a possibly-infinite point to zero, then negate. -/
def negCanon (P : Var FlaggedPoint (F circomPrime)) :
    Circuit (F circomPrime) (Var FlaggedPoint (F circomPrime) × Var FlaggedPoint (F circomPrime)) := do
  let x ← subcircuit (Mux.circuit (M := Emu)) { selector := P.isInf, ifTrue := zeroConst, ifFalse := P.x }
  let y ← subcircuit (Mux.circuit (M := Emu)) { selector := P.isInf, ifTrue := zeroConst, ifFalse := P.y }
  let ny ← subcircuit NegYAffine.circuit (withXY P x y)
  return (withXY P x y, withXY P x ny)

def main (b : Var Bases (F circomPrime)) : Circuit (F circomPrime) (Var GLVBuildTable.RawTable (F circomPrime)) := do
  let nr1y ← subcircuit NegYAffine.circuit b.r1
  let nr3y ← subcircuit NegYAffine.circuit b.r3
  let up ← subcircuit PhiPairAdd.circuit { P := b.r0, Q := b.r1 }
  let um ← subcircuit PhiPairAdd.circuit { P := b.r0, Q := withY b.r1 nr1y }
  let vp ← subcircuit PhiPairAdd.circuit { P := b.r2, Q := b.r3 }
  let vm ← subcircuit PhiPairAdd.circuit { P := b.r2, Q := withY b.r3 nr3y }
  let (vp', nvp) ← negCanon vp
  let (vm', nvm) ← negCanon vm
  -- entries with `b_0 = 1`: index `1 + 2 b_1 + 4 b_2 + 8 b_3`
  let e15 ← subcircuit CompleteAdd.circuit { P := up, Q := vp' }
  let e7 ← subcircuit CompleteAdd.circuit { P := up, Q := vm' }
  let e11 ← subcircuit CompleteAdd.circuit { P := up, Q := nvm }
  let e3 ← subcircuit CompleteAdd.circuit { P := up, Q := nvp }
  let e13 ← subcircuit CompleteAdd.circuit { P := um, Q := vp' }
  let e5 ← subcircuit CompleteAdd.circuit { P := um, Q := vm' }
  let e9 ← subcircuit CompleteAdd.circuit { P := um, Q := nvm }
  let e1 ← subcircuit CompleteAdd.circuit { P := um, Q := nvp }
  -- the other half by negation
  let (_, e0) ← negCanon e15
  let (_, e8) ← negCanon e7
  let (_, e4) ← negCanon e11
  let (_, e12) ← negCanon e3
  let (_, e2) ← negCanon e13
  let (_, e10) ← negCanon e5
  let (_, e6) ← negCanon e9
  let (_, e14) ← negCanon e1
  return GLVBuildTable.RawTable.mk e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15

instance elaborated : ElaboratedCircuit (F circomPrime) Bases GLVBuildTable.RawTable main := by
  elaborate_circuit

def Assumptions (input : Bases (F circomPrime)) : Prop :=
  (∀ i : Fin 4, (baseEntry input i).Valid) ∧
    input.r0.isInf = 0 ∧ input.r1.isInf = 0 ∧
    decodeFe input.r1.x ≠ decodeFe input.r0.x ∧
    (input.r2.isInf = 1 → input.r2.y = emuOfNat 0) ∧
    (input.r3.isInf = 1 → input.r3.y = emuOfNat 0) ∧
    PhiPairAdd.Assumptions { P := input.r2, Q := input.r3 }

def Spec (input : Bases (F circomPrime)) (out : GLVBuildTable.RawTable (F circomPrime)) : Prop :=
  ∀ i : Fin 16, (rawEntry out i).Valid ∧
    decodePoint (rawEntry out i) =
      patPoint (fun j => decodePoint (baseEntry input j)) i.val ∧
    ((rawEntry out i).isInf = 1 → decodeFe (rawEntry out i).x = 0)

end Solution.Secp256k1ScalarMul.PatTable
