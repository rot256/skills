import Solution.Secp256k1ScalarMul.Lazy.Certs
import Solution.Secp256k1ScalarMul.Lazy.StepMath

/-!
# Interface of one lazy variable-base chain step `R' = 2R + T`

Types and value-level specification shared by the circuit (`Step`) and its
value-level correctness lemma (`StepValues`).
-/

namespace Solution.Secp256k1ScalarMulFixedBase.LazyVar.Step

open SmallSquare Sparse32 SparseX
open Solution.Secp256k1ScalarMul.Lazy
open Solution.Secp256k1ScalarMulFixedBase.LazyVar
open Specs.ShortWeierstrass Specs.Secp256k1

set_option autoImplicit false

abbrev FlaggedPoint := Solution.Secp256k1ScalarMul.FlaggedPoint

/-- A lazily represented accumulator point: eight signed radix-`2^32`
coefficients per coordinate (never normalised) and an infinity flag. -/
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

def LazyValid (n : ℕ) (P : LazyPt Field) : Prop :=
  IsBool P.isInf ∧ XIn (zwords P.x) ∧ YIn n (zwords P.y)

def OnCurveLazy (P : LazyPt Field) : Prop :=
  P.isInf = 0 → valZ (zwords P.y) ^ 2 = valZ (zwords P.x) ^ 3 + 7

def TValid (t : FlaggedPoint Field) : Prop :=
  IsBool t.isInf ∧ BigInt.Normalized 64 t.x ∧ BigInt.Normalized 64 t.y ∧
  (t.isInf = 0 → decodeFe t.y ^ 2 = decodeFe t.x ^ 3 + 7)

def decodeL (P : LazyPt Field) : GroupPoint Fp :=
  if P.isInf = 1 then .infinity else .affine ⟨valZ (zwords P.x), valZ (zwords P.y)⟩

def decodeT (t : FlaggedPoint Field) : GroupPoint Fp :=
  if t.isInf = 1 then .infinity else .affine ⟨decodeFe t.x, decodeFe t.y⟩

/-- `sp = 0` (ordinary scalar) requires an affine table point; infinite table
entries are only reachable through the special-scalar fallback `sp = 1`. -/
def Assumptions (n : ℕ) (i : Inputs Field) : Prop :=
  LazyValid n i.acc ∧ OnCurveLazy i.acc ∧ TValid i.t ∧ IsBool i.sp ∧ (i.sp = 0 → i.t.isInf = 0)

/-- Output valid at the next depth; with `sp = 0` (ordinary scalar) it is the
group-law result `(R + R) + T`, on the curve. -/
def Spec (n : ℕ) (i : Inputs Field) (o : LazyPt Field) : Prop :=
  LazyValid (n + 1) o ∧
  (i.sp = 0 → OnCurveLazy o ∧
    decodeL o = add curve (add curve (decodeL i.acc) (decodeL i.acc)) (decodeT i.t))

/-! ### Value-level views and honest witnesses -/

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

end Solution.Secp256k1ScalarMulFixedBase.LazyVar.Step
