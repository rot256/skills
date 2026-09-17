import Solution.Secp256k1ScalarMul.Lazy.Certs
import Solution.Secp256k1ScalarMul.Lazy.MuxVec
import Solution.Secp256k1ScalarMul.Lazy.StepMath

/-!
# One lazy variable-base chain step: `R' = 2R + T = (R + T) + R`

The accumulator `R` is carried lazily (eight signed radix-`2^32` coefficients
per coordinate, never normalised); the table point `T` is canonical.  Two
slope witnesses with balanced digits (patchgravity's `Sparse32Normalize`,
d59c8bf7), nine sparse products, four zero-row certificates, and boolean
flags for the two cancellation branches.  `T = ∞` is delegated to the global
special-scalar fallback (`sp`); `R = ∞` is handled by an output mux.
-/

namespace Solution.Secp256k1ScalarMulFixedBase.LazyVar.Step

open SmallSquare Sparse32 SparseX Challenge.CostR1CS Cost
open Solution.Secp256k1ScalarMul.Lazy
open Solution.Secp256k1ScalarMulFixedBase.LazyVar
open Specs.ShortWeierstrass Specs.Secp256k1

set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 20000

abbrev FlaggedPoint := Solution.Secp256k1ScalarMul.FlaggedPoint

structure LazyPt (F : Type) where
  x : fields 8 F
  y : fields 8 F
  isInf : F
deriving ProvableStruct

structure Inputs (F : Type) where
  acc : LazyPt F
  t : FlaggedPoint F
  sp : F
deriving ProvableStruct

/-! ### Value-level views -/

def rx (i : Inputs Field) : Fp := valZ (zwords i.acc.x)
def ry (i : Inputs Field) : Fp := valZ (zwords i.acc.y)
def tX (i : Inputs Field) : Fp := decodeFe i.t.x
def tY (i : Inputs Field) : Fp := decodeFe i.t.y

/-- Honest first slope: chord of `(R, T)`, tangent when `T = R`, and `0` on the
branches where no relation is certified. -/
noncomputable def slope1 (i : Inputs Field) : Fp :=
  if i.acc.isInf = 1 then 0
  else if tX i = rx i then (if tY i = -ry i then 0 else 3 * rx i ^ 2 / (2 * ry i))
  else (tY i - ry i) / (tX i - rx i)

def cflagV (i : Inputs Field) : Field :=
  if i.acc.isInf = 0 ∧ rx i = tX i ∧ ry i = -tY i then 1 else 0

noncomputable def xSV (i : Inputs Field) : Fp := slope1 i * slope1 i - rx i - tX i

noncomputable def zflagV (i : Inputs Field) : Field :=
  if i.acc.isInf = 0 ∧ cflagV i = 0 ∧ xSV i = rx i then 1 else 0

/-- Honest second slope from the two-slope identity. -/
noncomputable def slope2 (i : Inputs Field) : Fp :=
  if xSV i = rx i then 0 else 2 * ry i / (rx i - xSV i) - slope1 i

noncomputable def lam1W (i : Inputs Field) : Emu Field := slopeWitness (slope1 i)
noncomputable def lam2W (i : Inputs Field) : Emu Field := slopeWitness (slope2 i)
noncomputable def flagsW (i : Inputs Field) : fields 2 Field := #v[cflagV i, zflagV i]

def zeroVec : Var (fields 8) Field := Vector.ofFn fun _ => (0 : Expression Field)

/-! ### Circuit -/

noncomputable def main (n : ℕ) (hn : n ≤ depth) (i : Var Inputs Field) :
    Circuit Field (Var LazyPt Field) := do
  let lam1 ← ProvableType.witness (α := Emu) fun env => lam1W (eval env i)
  let a ← Sparse32Normalize.circuit lam1
  let lam2 ← ProvableType.witness (α := Emu) fun env => lam2W (eval env i)
  let b ← Sparse32Normalize.circuit lam2
  let fl ← ProvableType.witness (α := fields 2) fun env => flagsW (eval env i)
  let c := fl[0]
  let z := fl[1]
  Circuit.assertZero (c * (1 - c))
  Circuit.assertZero (z * (1 - z))
  Circuit.assertZero (c * z)
  Circuit.assertZero (i.acc.isInf * c)
  Circuit.assertZero (i.acc.isInf * z)
  Circuit.assertZero ((1 - i.sp) * i.t.isInf)
  let g ← subcircuit MulCell.circuit ⟨1 - i.sp, 1 - i.acc.isInf⟩
  let p ← subcircuit Products.circuit ⟨a, b, i.acc.x, i.acc.y, i.t.x, i.t.y⟩
  assertion (Certs.circuit n hn) ⟨a, b, i.acc.x, i.acc.y, i.t.x, i.t.y, p, g, c, z⟩
  let rt ← subcircuit MulCell.circuit ⟨i.acc.isInf, i.t.isInf⟩
  let zrt ← subcircuit MulCell.circuit ⟨z, rt⟩
  let zOut := z + rt - zrt
  let xP := Products.vaddE (Products.vsubE p.sb p.sa) (embedExpr i.t.x)
  let yP := Products.vsubE p.pb i.acc.y
  let xw ← subcircuit MuxVec.circuit ⟨c, xP, i.acc.x⟩
  let xv ← subcircuit MuxVec.circuit ⟨i.acc.isInf, xw, embedExpr i.t.x⟩
  let xo ← subcircuit MuxVec.circuit ⟨zOut, xv, zeroVec⟩
  let yw ← subcircuit MuxVec.circuit ⟨c, yP, i.acc.y⟩
  let yv ← subcircuit MuxVec.circuit ⟨i.acc.isInf, yw, embedExpr i.t.y⟩
  let yo ← subcircuit MuxVec.circuit ⟨zOut, yv, zeroVec⟩
  return { x := xo, y := yo, isInf := zOut }

noncomputable instance elaborated (n : ℕ) (hn : n ≤ depth) :
    ElaboratedCircuit Field Inputs LazyPt (main n hn) := by
  elaborate_circuit

/-! ### Specification -/

def LazyValid (n : ℕ) (P : LazyPt Field) : Prop :=
  IsBool P.isInf ∧ XIn (zwords P.x) ∧ YIn n (zwords P.y) ∧
  (P.isInf = 1 → zwords P.x = (fun _ => 0) ∧ zwords P.y = (fun _ => 0))

def OnCurveLazy (P : LazyPt Field) : Prop :=
  P.isInf = 0 → valZ (zwords P.y) ^ 2 = valZ (zwords P.x) ^ 3 + 7

def TValid (t : FlaggedPoint Field) : Prop :=
  IsBool t.isInf ∧ BigInt.Normalized 64 t.x ∧ BigInt.Normalized 64 t.y ∧
  (t.isInf = 0 → decodeFe t.y ^ 2 = decodeFe t.x ^ 3 + 7)

def decodeL (P : LazyPt Field) : GroupPoint Fp :=
  if P.isInf = 1 then .infinity else .affine ⟨valZ (zwords P.x), valZ (zwords P.y)⟩

def decodeT (t : FlaggedPoint Field) : GroupPoint Fp :=
  if t.isInf = 1 then .infinity else .affine ⟨decodeFe t.x, decodeFe t.y⟩

def Assumptions (n : ℕ) (i : Inputs Field) : Prop :=
  LazyValid n i.acc ∧ OnCurveLazy i.acc ∧ TValid i.t ∧ IsBool i.sp

def Spec (n : ℕ) (i : Inputs Field) (o : LazyPt Field) : Prop :=
  LazyValid (n + 1) o ∧
  (i.sp = 0 → OnCurveLazy o ∧
    decodeL o = add curve (add curve (decodeL i.acc) (decodeL i.acc)) (decodeT i.t))

end Solution.Secp256k1ScalarMulFixedBase.LazyVar.Step
