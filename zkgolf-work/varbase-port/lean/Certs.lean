import Solution.Secp256k1ScalarMul.Lazy.Products
import Solution.Secp256k1ScalarMul.Lazy.Cert3
import Solution.Secp256k1ScalarMul.Lazy.MulCell

/-!
# The four certificate slots of one chain step

Contents are selected by boolean flags (`g` gate, `c` cancellation `T = −R`,
`z` second cancellation `S = −R`) at the half/limb level, so each mux is one
product cell.  With `g = 0` every slot certifies `0`.
-/

namespace Solution.Secp256k1ScalarMulFixedBase.LazyVar.Certs

open SmallSquare Sparse32 SparseX Challenge.CostR1CS Cost
open Solution.Secp256k1ScalarMul.Lazy
open Solution.Secp256k1ScalarMulFixedBase.LazyVar

set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 20000

structure Inputs (F : Type) where
  a : fields 8 F
  b : fields 8 F
  x : fields 8 F
  y : fields 8 F
  tx : Emu F
  ty : Emu F
  p : Products.Outputs F
  g : F
  c : F
  z : F
deriving ProvableStruct

/-! ### Word vectors of the slot contents -/

def chordW (i : Var Inputs Field) : Var (fields 8) Field :=
  Products.vaddE (Products.vsubE i.p.pa (embedExpr i.ty)) i.y
def xeq1W (i : Var Inputs Field) : Var (fields 8) Field :=
  Products.vsubE i.x (embedExpr i.tx)
def uniW (i : Var Inputs Field) : Var (fields 8) Field :=
  Products.vsubE i.p.pu (Products.vaddE (Products.vaddE i.p.sx i.p.pxt) i.p.st)
def yeqW (i : Var Inputs Field) : Var (fields 8) Field :=
  Products.vaddE i.y (embedExpr i.ty)
def xSW (i : Var Inputs Field) : Var (fields 8) Field :=
  Products.vsubE (Products.vsubE i.p.sa i.x) (embedExpr i.tx)
def xeq2W (i : Var Inputs Field) : Var (fields 8) Field :=
  Products.vsubE (xSW i) i.x
def rel2W (i : Var Inputs Field) : Var (fields 8) Field :=
  Vector.ofFn fun k => i.p.pab[k.val] - (2 : Field) * i.y[k.val]

def half (w : Var (fields 8) Field) (side : Bool) : Expression Field :=
  Sparse32Wide.productHalfExpr w side

def limb (w : Var (fields 8) Field) (j : Fin 3) : Expression Field :=
  if j.val = 0 then w[0] + (H : Field) * w[1] + (H ^ 2 : Field) * w[2]
  else if j.val = 1 then w[3] + (H : Field) * w[4] + (H ^ 2 : Field) * w[5]
  else w[6] + (H : Field) * w[7]

/-- Gated select at cell level: `g * (A + s * (B − A))`. -/
def cell (s A B : Expression Field) : Var MulCell.Inputs Field := ⟨s, B - A⟩

def main (i : Var Inputs Field) : Circuit Field Unit := do
  -- rel1 slot: chord, or x − T.x under c
  let m1l ← subcircuit MulCell.circuit ⟨i.c, half (xeq1W i) false - half (chordW i) false⟩
  let h1l ← subcircuit MulCell.circuit ⟨i.g, half (chordW i) false + m1l⟩
  let m1h ← subcircuit MulCell.circuit ⟨i.c, half (xeq1W i) true - half (chordW i) true⟩
  let h1h ← subcircuit MulCell.circuit ⟨i.g, half (chordW i) true + m1h⟩
  -- uni slot: unified relation, or y + T.y under c
  let mu0 ← subcircuit MulCell.circuit ⟨i.c, limb (yeqW i) 0 - limb (uniW i) 0⟩
  let l0 ← subcircuit MulCell.circuit ⟨i.g, limb (uniW i) 0 + mu0⟩
  let mu1 ← subcircuit MulCell.circuit ⟨i.c, limb (yeqW i) 1 - limb (uniW i) 1⟩
  let l1 ← subcircuit MulCell.circuit ⟨i.g, limb (uniW i) 1 + mu1⟩
  let mu2 ← subcircuit MulCell.circuit ⟨i.c, limb (yeqW i) 2 - limb (uniW i) 2⟩
  let l2 ← subcircuit MulCell.circuit ⟨i.g, limb (uniW i) 2 + mu2⟩
  -- xeq slot: xS − x under z
  let gz ← subcircuit MulCell.circuit ⟨i.g, i.z⟩
  let hxl ← subcircuit MulCell.circuit ⟨gz, half (xeq2W i) false⟩
  let hxh ← subcircuit MulCell.circuit ⟨gz, half (xeq2W i) true⟩
  -- rel2 slot: two-slope identity, off under c or z
  let m2l ← subcircuit MulCell.circuit ⟨i.c + i.z, half (rel2W i) false⟩
  let h2l ← subcircuit MulCell.circuit ⟨i.g, half (rel2W i) false - m2l⟩
  let m2h ← subcircuit MulCell.circuit ⟨i.c + i.z, half (rel2W i) true⟩
  let h2h ← subcircuit MulCell.circuit ⟨i.g, half (rel2W i) true - m2h⟩
  assertion (Cert.circuit .rel1) #v[h1l, h1h]
  assertion Cert3.circuit #v[l0, l1, l2]
  assertion (Cert.circuit .xeq) #v[hxl, hxh]
  assertion (Cert.circuit .rel2) #v[h2l, h2h]

instance elaborated : ElaboratedCircuit Field Inputs unit main := by
  elaborate_circuit

/-! ### Value-level model -/

def prodInput (i : Inputs Field) : Products.Inputs Field :=
  ⟨i.a, i.b, i.x, i.y, i.tx, i.ty⟩

def Assumptions (n : ℕ) (i : Inputs Field) : Prop :=
  IsBool i.g ∧ IsBool i.c ∧ IsBool i.z ∧ i.c * i.z = 0 ∧
  (i.g = 1 →
    Digits (digitsZ i.a) ∧ Digits (digitsZ i.b) ∧ XIn (zwords i.x) ∧ YIn n (zwords i.y) ∧
    BigInt.Normalized 64 i.tx ∧ BigInt.Normalized 64 i.ty ∧
    Products.Spec (prodInput i) i.p)

def rx (i : Inputs Field) : Fp := valZ (zwords i.x)
def ry (i : Inputs Field) : Fp := valZ (zwords i.y)
def aF (i : Inputs Field) : Fp := valZ (digitsZ i.a)
def bF (i : Inputs Field) : Fp := valZ (digitsZ i.b)
def tX (i : Inputs Field) : Fp := decodeFe i.tx
def tY (i : Inputs Field) : Fp := decodeFe i.ty
def xS (i : Inputs Field) : Fp := aF i * aF i - rx i - tX i

def Spec (i : Inputs Field) : Prop :=
  i.g = 1 →
    (i.c = 0 → aF i * (tX i - rx i) - tY i + ry i = 0 ∧
      aF i * (ry i + tY i) - (rx i * rx i + rx i * tX i + tX i * tX i) = 0) ∧
    (i.c = 1 → rx i - tX i = 0 ∧ ry i + tY i = 0) ∧
    (i.z = 1 → xS i - rx i = 0) ∧
    (i.c = 0 → i.z = 0 → (aF i + bF i) * (rx i - xS i) - 2 * ry i = 0)

end Solution.Secp256k1ScalarMulFixedBase.LazyVar.Certs
