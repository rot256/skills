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

/-- Output valid at the next depth; with `sp = 0` (ordinary scalar) it is the
group-law result `(R + R) + T`, on the curve. -/
def Spec (n : ℕ) (i : Inputs Field) (o : LazyPt Field) : Prop :=
  LazyValid (n + 1) o ∧
  (i.sp = 0 → OnCurveLazy o ∧
    decodeL o = add curve (add curve (decodeL i.acc) (decodeL i.acc)) (decodeT i.t))

end Solution.Secp256k1ScalarMulFixedBase.LazyVar.Step
