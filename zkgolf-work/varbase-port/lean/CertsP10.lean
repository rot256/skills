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
  gate : F
  cflag : F
  zflag : F
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
  let m1l ← subcircuit MulCell.circuit ⟨i.cflag, half (xeq1W i) false - half (chordW i) false⟩
  let h1l ← subcircuit MulCell.circuit ⟨i.gate, half (chordW i) false + m1l⟩
  let m1h ← subcircuit MulCell.circuit ⟨i.cflag, half (xeq1W i) true - half (chordW i) true⟩
  let h1h ← subcircuit MulCell.circuit ⟨i.gate, half (chordW i) true + m1h⟩
  -- uni slot: unified relation, or y + T.y under c
  let mu0 ← subcircuit MulCell.circuit ⟨i.cflag, limb (yeqW i) 0 - limb (uniW i) 0⟩
  let l0 ← subcircuit MulCell.circuit ⟨i.gate, limb (uniW i) 0 + mu0⟩
  let mu1 ← subcircuit MulCell.circuit ⟨i.cflag, limb (yeqW i) 1 - limb (uniW i) 1⟩
  let l1 ← subcircuit MulCell.circuit ⟨i.gate, limb (uniW i) 1 + mu1⟩
  let mu2 ← subcircuit MulCell.circuit ⟨i.cflag, limb (yeqW i) 2 - limb (uniW i) 2⟩
  let l2 ← subcircuit MulCell.circuit ⟨i.gate, limb (uniW i) 2 + mu2⟩
  -- xeq slot: xS − x under z
  let gz ← subcircuit MulCell.circuit ⟨i.gate, i.zflag⟩
  let hxl ← subcircuit MulCell.circuit ⟨gz, half (xeq2W i) false⟩
  let hxh ← subcircuit MulCell.circuit ⟨gz, half (xeq2W i) true⟩
  -- rel2 slot: two-slope identity, off under c or z
  let m2l ← subcircuit MulCell.circuit ⟨i.cflag + i.zflag, half (rel2W i) false⟩
  let h2l ← subcircuit MulCell.circuit ⟨i.gate, half (rel2W i) false - m2l⟩
  let m2h ← subcircuit MulCell.circuit ⟨i.cflag + i.zflag, half (rel2W i) true⟩
  let h2h ← subcircuit MulCell.circuit ⟨i.gate, half (rel2W i) true - m2h⟩
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
  IsBool i.gate ∧ IsBool i.cflag ∧ IsBool i.zflag ∧ i.cflag * i.zflag = 0 ∧
  (i.gate = 1 →
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
  i.gate = 1 →
    (i.cflag = 0 → aF i * (tX i - rx i) - tY i + ry i = 0 ∧
      aF i * (ry i + tY i) - (rx i * rx i + rx i * tX i + tX i * tX i) = 0) ∧
    (i.cflag = 1 → rx i - tX i = 0 ∧ ry i + tY i = 0) ∧
    (i.zflag = 1 → xS i - rx i = 0) ∧
    (i.cflag = 0 → i.zflag = 0 → (aF i + bF i) * (rx i - xS i) - 2 * ry i = 0)

/-! ### Value-level word vectors and their integer models -/

def chordV (i : Inputs Field) : fields 8 Field := Products.vadd (Products.vsub i.p.pa (embedVec i.ty)) i.y
def xeq1V (i : Inputs Field) : fields 8 Field := Products.vsub i.x (embedVec i.tx)
def uniV (i : Inputs Field) : fields 8 Field := Products.vsub i.p.pu (Products.vadd (Products.vadd i.p.sx i.p.pxt) i.p.st)
def yeqV (i : Inputs Field) : fields 8 Field := Products.vadd i.y (embedVec i.ty)
def xSV (i : Inputs Field) : fields 8 Field := Products.vsub (Products.vsub i.p.sa i.x) (embedVec i.tx)
def xeq2V (i : Inputs Field) : fields 8 Field := Products.vsub (xSV i) i.x
def rel2V (i : Inputs Field) : fields 8 Field :=
  Vector.ofFn fun k => i.p.pab[k.val] - (2 : Field) * i.y[k.val]

def A (i : Inputs Field) : Words ℤ := digitsZ i.a
def B (i : Inputs Field) : Words ℤ := digitsZ i.b
def X (i : Inputs Field) : Words ℤ := zwords i.x
def Y (i : Inputs Field) : Words ℤ := zwords i.y
def TX (i : Inputs Field) : Fin 4 → ℤ := emuz i.tx
def TY (i : Inputs Field) : Fin 4 → ℤ := emuz i.ty

lemma map_chordW (env : Environment Field) (iv : Var Inputs Field) :
    Vector.map (Expression.eval env) (chordW iv) = chordV (eval env iv) := by
  simp only [chordW, chordV, Products.map_vaddE, Products.map_vsubE, Products.map_embedExpr,
    circuit_norm]
lemma map_xeq1W (env : Environment Field) (iv : Var Inputs Field) :
    Vector.map (Expression.eval env) (xeq1W iv) = xeq1V (eval env iv) := by
  simp only [xeq1W, xeq1V, Products.map_vsubE, Products.map_embedExpr, circuit_norm]
lemma map_uniW (env : Environment Field) (iv : Var Inputs Field) :
    Vector.map (Expression.eval env) (uniW iv) = uniV (eval env iv) := by
  simp only [uniW, uniV, Products.map_vaddE, Products.map_vsubE, circuit_norm]
lemma map_yeqW (env : Environment Field) (iv : Var Inputs Field) :
    Vector.map (Expression.eval env) (yeqW iv) = yeqV (eval env iv) := by
  simp only [yeqW, yeqV, Products.map_vaddE, Products.map_embedExpr, circuit_norm]
lemma map_xeq2W (env : Environment Field) (iv : Var Inputs Field) :
    Vector.map (Expression.eval env) (xeq2W iv) = xeq2V (eval env iv) := by
  simp only [xeq2W, xSW, xeq2V, xSV, Products.map_vsubE, Products.map_embedExpr, circuit_norm]
lemma map_rel2W (env : Environment Field) (iv : Var Inputs Field) :
    Vector.map (Expression.eval env) (rel2W iv) = rel2V (eval env iv) := by
  apply Vector.ext
  intro k hk
  simp only [rel2W, rel2V, circuit_norm, Vector.getElem_ofFn, Vector.getElem_map,
    Expression.eval, neg_one_mul, sub_eq_add_neg]

lemma vsub_cast (u v : fields 8 Field) (U V : Words ℤ)
    (hu : ∀ k : Fin 8, u[k.val] = ((U k : ℤ) : Field)) (hv : ∀ k : Fin 8, v[k.val] = ((V k : ℤ) : Field))
    (k : Fin 8) : (Products.vsub u v)[k.val] = ((U k - V k : ℤ) : Field) := by
  simp only [Products.vsub, Vector.getElem_ofFn, hu, hv, Int.cast_sub]
lemma vadd_cast (u v : fields 8 Field) (U V : Words ℤ)
    (hu : ∀ k : Fin 8, u[k.val] = ((U k : ℤ) : Field)) (hv : ∀ k : Fin 8, v[k.val] = ((V k : ℤ) : Field))
    (k : Fin 8) : (Products.vadd u v)[k.val] = ((U k + V k : ℤ) : Field) := by
  simp only [Products.vadd, Vector.getElem_ofFn, hu, hv, Int.cast_add]
lemma mulVec_cast (u v : fields 8 Field) (U V : Words ℤ)
    (hu : ∀ k : Fin 8, u[k.val] = ((U k : ℤ) : Field)) (hv : ∀ k : Fin 8, v[k.val] = ((V k : ℤ) : Field))
    (k : Fin 8) : (Products.mulVec u v)[k.val] = ((sparseMul U V k : ℤ) : Field) := by
  simp only [Products.mulVec, Vector.getElem_ofFn]
  exact sparseMul_cast U V _ _ hu hv k
lemma sqVec_cast (u : fields 8 Field) (U : Words ℤ)
    (hu : ∀ k : Fin 8, u[k.val] = ((U k : ℤ) : Field)) (k : Fin 8) :
    (Products.sqVec u)[k.val] = ((sparseSquare U k : ℤ) : Field) := by
  simp only [Products.sqVec, Vector.getElem_ofFn]
  exact sparseMul_cast U U _ _ hu hu k

section Casts
variable (i : Inputs Field) (hp : Products.Spec (prodInput i) i.p)
include hp

lemma pa_cast (k : Fin 8) :
    i.p.pa[k.val] = ((sparseMul (A i) (fun j => embed (TX i) j - X i j) k : ℤ) : Field) := by
  rw [hp.1]
  exact mulVec_cast _ _ (A i) _ (digitsZ_cast i.a)
    (vsub_cast _ _ (embed (TX i)) (X i) (embedVec_cast i.tx) (zwords_cast i.x)) k

lemma pu_cast (k : Fin 8) :
    i.p.pu[k.val] = ((sparseMul (A i) (fun j => Y i j + embed (TY i) j) k : ℤ) : Field) := by
  rw [hp.2.1]
  exact mulVec_cast _ _ (A i) _ (digitsZ_cast i.a)
    (vadd_cast _ _ (Y i) (embed (TY i)) (zwords_cast i.y) (embedVec_cast i.ty)) k

lemma sx_cast (k : Fin 8) : i.p.sx[k.val] = ((sparseSquare (X i) k : ℤ) : Field) := by
  rw [hp.2.2.1]; exact sqVec_cast _ (X i) (zwords_cast i.x) k

lemma pxt_cast (k : Fin 8) :
    i.p.pxt[k.val] = ((sparseMul (X i) (embed (TX i)) k : ℤ) : Field) := by
  rw [hp.2.2.2.1]; exact mulVec_cast _ _ (X i) _ (zwords_cast i.x) (embedVec_cast i.tx) k

lemma st_cast (k : Fin 8) : i.p.st[k.val] = ((sparseSquare (embed (TX i)) k : ℤ) : Field) := by
  rw [hp.2.2.2.2.1]; exact sqVec_cast _ (embed (TX i)) (embedVec_cast i.tx) k

lemma sa_cast (k : Fin 8) : i.p.sa[k.val] = ((sparseSquare (A i) k : ℤ) : Field) := by
  rw [hp.2.2.2.2.2.1]; exact sqVec_cast _ (A i) (digitsZ_cast i.a) k

lemma xSV_cast (k : Fin 8) : (xSV i)[k.val] = ((xSZ (A i) (X i) (TX i) k : ℤ) : Field) := by
  simp only [xSV, xSZ]
  exact vsub_cast _ _ (fun j => sparseSquare (A i) j - X i j) (embed (TX i))
    (vsub_cast _ _ _ _ (sa_cast i hp) (zwords_cast i.x)) (embedVec_cast i.tx) k

lemma pab_cast (k : Fin 8) :
    i.p.pab[k.val] =
      ((sparseMul (fun j => A i j + B i j) (fun j => X i j - xSZ (A i) (X i) (TX i) j) k : ℤ) : Field) := by
  rw [hp.2.2.2.2.2.2.1]
  refine mulVec_cast _ _ _ _ (vadd_cast _ _ (A i) (B i) (digitsZ_cast i.a) (digitsZ_cast i.b)) ?_ k
  intro j
  simp only [Products.xSVal]
  exact vsub_cast _ _ (X i) _ (zwords_cast i.x) (xSV_cast i hp) j

lemma chordV_cast (k : Fin 8) :
    (chordV i)[k.val] = ((chordZ (A i) (X i) (Y i) (TX i) (TY i) k : ℤ) : Field) := by
  simp only [chordV, chordZ]
  exact vadd_cast _ _ _ (Y i) (vsub_cast _ _ _ (embed (TY i)) (pa_cast i hp) (embedVec_cast i.ty))
    (zwords_cast i.y) k

lemma uniV_cast (k : Fin 8) :
    (uniV i)[k.val] = ((uniZ (A i) (X i) (Y i) (TX i) (TY i) k : ℤ) : Field) := by
  simp only [uniV, uniZ]
  exact vsub_cast _ _ _ _ (pu_cast i hp)
    (vadd_cast _ _ _ _ (vadd_cast _ _ _ _ (sx_cast i hp) (pxt_cast i hp)) (st_cast i hp)) k

lemma xeq2V_cast (k : Fin 8) :
    (xeq2V i)[k.val] = ((xeq2Z (A i) (X i) (TX i) k : ℤ) : Field) := by
  simp only [xeq2V, xeq2Z]
  exact vsub_cast _ _ _ (X i) (xSV_cast i hp) (zwords_cast i.x) k

lemma rel2V_cast (k : Fin 8) :
    (rel2V i)[k.val] = ((rel2Z' (A i) (B i) (X i) (Y i) (TX i) k : ℤ) : Field) := by
  simp only [rel2V, rel2Z', Y, Vector.getElem_ofFn, pab_cast i hp, zwords_cast i.y, Fin.eta]
  push_cast; ring

end Casts

lemma xeq1V_cast (i : Inputs Field) (k : Fin 8) :
    (xeq1V i)[k.val] = ((xeq1Z (X i) (TX i) k : ℤ) : Field) := by
  simp only [xeq1V, xeq1Z]
  exact vsub_cast _ _ (X i) _ (zwords_cast i.x) (embedVec_cast i.tx) k

lemma yeqV_cast (i : Inputs Field) (k : Fin 8) :
    (yeqV i)[k.val] = ((yeqZ (Y i) (TY i) (-1) k : ℤ) : Field) := by
  simp only [yeqV, yeqZ]
  rw [vadd_cast _ _ (Y i) (embed (TY i)) (zwords_cast i.y) (embedVec_cast i.ty) k]
  push_cast; ring

/-! ### Halves and limbs of cast vectors -/

lemma eval_half_cast (env : Environment Field) (w : Var (fields 8) Field) (Z : Words ℤ)
    (hw : ∀ k : Fin 8, (Vector.map (Expression.eval env) w)[k.val] = ((Z k : ℤ) : Field)) :
    Expression.eval env (half w false) = ((lowHalf Z : ℤ) : Field) ∧
    Expression.eval env (half w true) = ((highHalf Z : ℤ) : Field) := by
  have h0 : Expression.eval env w[0] = ((Z 0 : ℤ) : Field) := by
    have := hw 0; simp only [Vector.getElem_map] at this; exact this
  have h1 : Expression.eval env w[1] = ((Z 1 : ℤ) : Field) := by
    have := hw 1; simp only [Vector.getElem_map] at this; exact this
  have h2 : Expression.eval env w[2] = ((Z 2 : ℤ) : Field) := by
    have := hw 2; simp only [Vector.getElem_map] at this; exact this
  have h3 : Expression.eval env w[3] = ((Z 3 : ℤ) : Field) := by
    have := hw 3; simp only [Vector.getElem_map] at this; exact this
  have h4 : Expression.eval env w[4] = ((Z 4 : ℤ) : Field) := by
    have := hw 4; simp only [Vector.getElem_map] at this; exact this
  have h5 : Expression.eval env w[5] = ((Z 5 : ℤ) : Field) := by
    have := hw 5; simp only [Vector.getElem_map] at this; exact this
  have h6 : Expression.eval env w[6] = ((Z 6 : ℤ) : Field) := by
    have := hw 6; simp only [Vector.getElem_map] at this; exact this
  have h7 : Expression.eval env w[7] = ((Z 7 : ℤ) : Field) := by
    have := hw 7; simp only [Vector.getElem_map] at this; exact this
  simp only [half, Sparse32Wide.productHalfExpr, Bool.false_eq_true, ↓reduceIte, circuit_norm,
    Expression.eval, lowHalf, highHalf, h0, h1, h2, h3, h4, h5, h6, h7]
  push_cast
  constructor <;> ring

lemma eval_limb_cast (env : Environment Field) (w : Var (fields 8) Field) (Z : Words ℤ)
    (hw : ∀ k : Fin 8, (Vector.map (Expression.eval env) w)[k.val] = ((Z k : ℤ) : Field)) :
    Expression.eval env (limb w 0) = ((limb0 Z : ℤ) : Field) ∧
    Expression.eval env (limb w 1) = ((limb1 Z : ℤ) : Field) ∧
    Expression.eval env (limb w 2) = ((limb2 Z : ℤ) : Field) := by
  have h0 : Expression.eval env w[0] = ((Z 0 : ℤ) : Field) := by
    have := hw 0; simp only [Vector.getElem_map] at this; exact this
  have h1 : Expression.eval env w[1] = ((Z 1 : ℤ) : Field) := by
    have := hw 1; simp only [Vector.getElem_map] at this; exact this
  have h2 : Expression.eval env w[2] = ((Z 2 : ℤ) : Field) := by
    have := hw 2; simp only [Vector.getElem_map] at this; exact this
  have h3 : Expression.eval env w[3] = ((Z 3 : ℤ) : Field) := by
    have := hw 3; simp only [Vector.getElem_map] at this; exact this
  have h4 : Expression.eval env w[4] = ((Z 4 : ℤ) : Field) := by
    have := hw 4; simp only [Vector.getElem_map] at this; exact this
  have h5 : Expression.eval env w[5] = ((Z 5 : ℤ) : Field) := by
    have := hw 5; simp only [Vector.getElem_map] at this; exact this
  have h6 : Expression.eval env w[6] = ((Z 6 : ℤ) : Field) := by
    have := hw 6; simp only [Vector.getElem_map] at this; exact this
  have h7 : Expression.eval env w[7] = ((Z 7 : ℤ) : Field) := by
    have := hw 7; simp only [Vector.getElem_map] at this; exact this
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [limb, Fin.val_zero, Fin.val_one, Fin.val_two, ↓reduceIte, Nat.one_ne_zero,
      Nat.succ_ne_self, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, Nat.reduceEqDiff] <;>
    simp only [circuit_norm, Expression.eval, limb0, limb1, limb2, h0, h1, h2, h3, h4, h5, h6, h7] <;>
    push_cast <;> ring

/-! ### The certified integer contents -/

/-- Content of the `rel1` slot as an integer vector. -/
def Z1 (i : Inputs Field) : Words ℤ :=
  if i.cflag = 1 then xeq1Z (X i) (TX i) else chordZ (A i) (X i) (Y i) (TX i) (TY i)
def Z2 (i : Inputs Field) : Words ℤ :=
  if i.cflag = 1 then yeqZ (Y i) (TY i) (-1) else uniZ (A i) (X i) (Y i) (TX i) (TY i)
def Z3 (i : Inputs Field) : Words ℤ :=
  if i.zflag = 1 then xeq2Z (A i) (X i) (TX i) else fun _ => 0
def Z4 (i : Inputs Field) : Words ℤ :=
  if i.cflag = 0 ∧ i.zflag = 0 then rel2Z' (A i) (B i) (X i) (Y i) (TX i) else fun _ => 0

lemma Z1_bounds {n : ℕ} (hn : n ≤ depth) (i : Inputs Field) (h : Assumptions n i) (hg : i.gate = 1) :
    ∀ k, slotLo .rel1 k ≤ Z1 i k ∧ Z1 i k ≤ slotHi .rel1 k := by
  obtain ⟨ha, hb, hx, hy, htx, hty, hp⟩ := h.2.2.2.2 hg
  unfold Z1
  split_ifs
  · exact rel1_of_xeq1 hx (emuz_bounds _ htx)
  · exact rel1_of_chord hn ha hx hy (emuz_bounds _ htx) (emuz_bounds _ hty)

lemma Z2_bounds {n : ℕ} (hn : n ≤ depth) (i : Inputs Field) (h : Assumptions n i) (hg : i.gate = 1) :
    ∀ k, uniLo k ≤ Z2 i k ∧ Z2 i k ≤ uniHi k := by
  obtain ⟨ha, hb, hx, hy, htx, hty, hp⟩ := h.2.2.2.2 hg
  unfold Z2
  split_ifs
  · exact uni_of_yeq hn hy (emuz_bounds _ hty)
  · exact uni_bounds hn ha hx hy (emuz_bounds _ htx) (emuz_bounds _ hty)

lemma Z3_bounds {n : ℕ} (i : Inputs Field) (h : Assumptions n i) (hg : i.gate = 1) :
    ∀ k, slotLo .xeq k ≤ Z3 i k ∧ Z3 i k ≤ slotHi .xeq k := by
  obtain ⟨ha, hb, hx, hy, htx, hty, hp⟩ := h.2.2.2.2 hg
  unfold Z3
  split_ifs
  · exact xeq2_bounds ha hx (emuz_bounds _ htx)
  · exact slot_zero .xeq

lemma Z4_bounds {n : ℕ} (hn : n ≤ depth) (i : Inputs Field) (h : Assumptions n i) (hg : i.gate = 1) :
    ∀ k, slotLo .rel2 k ≤ Z4 i k ∧ Z4 i k ≤ slotHi .rel2 k := by
  obtain ⟨ha, hb, hx, hy, htx, hty, hp⟩ := h.2.2.2.2 hg
  unfold Z4
  split_ifs
  · exact rel2_bounds hn ha hb hx hy (emuz_bounds _ htx)
  · exact slot_zero .rel2

/-! ### Soundness -/

lemma Z1_value (i : Inputs Field) (hc : IsBool i.cflag) (h : valZ (Z1 i) = 0) :
    (i.cflag = 0 → aF i * (tX i - rx i) - tY i + ry i = 0) ∧ (i.cflag = 1 → rx i - tX i = 0) := by
  rcases hc with hc | hc
  · refine ⟨fun _ => ?_, fun h1 => absurd (hc.symm.trans h1) zero_ne_one⟩
    simp only [Z1, hc, zero_ne_one, ↓reduceIte, A, X, Y, TX, TY] at h
    rw [chordZ_value] at h
    exact h
  · refine ⟨fun h0 => absurd (hc.symm.trans h0) one_ne_zero, fun _ => ?_⟩
    simp only [Z1, hc, ↓reduceIte, X, TX] at h
    rw [xeq1Z_value] at h
    exact h

lemma Z2_value (i : Inputs Field) (hc : IsBool i.cflag) (h : valZ (Z2 i) = 0) :
    (i.cflag = 0 → aF i * (ry i + tY i) - (rx i * rx i + rx i * tX i + tX i * tX i) = 0) ∧
    (i.cflag = 1 → ry i + tY i = 0) := by
  rcases hc with hc | hc
  · refine ⟨fun _ => ?_, fun h1 => absurd (hc.symm.trans h1) zero_ne_one⟩
    simp only [Z2, hc, zero_ne_one, ↓reduceIte, A, X, Y, TX, TY] at h
    rw [uniZ_value] at h
    exact h
  · refine ⟨fun h0 => absurd (hc.symm.trans h0) one_ne_zero, fun _ => ?_⟩
    simp only [Z2, hc, ↓reduceIte, Y, TY] at h
    rw [yeqZ_value] at h
    push_cast at h
    simp only [ry, tY]
    linear_combination h

lemma Z3_value (i : Inputs Field) (h : valZ (Z3 i) = 0) : i.zflag = 1 → xS i - rx i = 0 := by
  intro hz
  simp only [Z3, hz, ↓reduceIte, A, X, TX] at h
  rw [xeq2Z_value, xSZ_value] at h
  exact h

lemma Z4_value (i : Inputs Field) (h : valZ (Z4 i) = 0) :
    i.cflag = 0 → i.zflag = 0 → (aF i + bF i) * (rx i - xS i) - 2 * ry i = 0 := by
  intro hc hz
  simp only [Z4, hc, hz, and_self, ↓reduceIte, A, B, X, Y, TX] at h
  rw [rel2Z_value, xSZ_value] at h
  exact h

theorem soundness (n : ℕ) (hn : n ≤ depth) :
    FormalAssertion.Soundness Field main (Assumptions n) Spec := by
  circuit_proof_start_core
  subst h_input
  simp only [main, MulCell.circuit, MulCell.Assumptions, MulCell.Spec, Cert.circuit,
    Cert3.circuit, circuit_norm] at h_holds
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17,
    c1, c2, c3, c4⟩ := h_holds
  have hg' : Expression.eval env input_var.gate = (eval env input_var).gate := by
    simp only [circuit_norm]
  have hc' : Expression.eval env input_var.cflag = (eval env input_var).cflag := by
    simp only [circuit_norm]
  have hz' : Expression.eval env input_var.zflag = (eval env input_var).zflag := by
    simp only [circuit_norm]
  rw [hg'] at e2 e4 e6 e8 e10 e11 e15 e17
  rw [hc'] at e1 e3 e5 e7 e9 e14 e16
  rw [hz'] at e11 e14 e16
  refine ⟨?_, by simp only [main, MulCell.circuit, Cert.circuit, Cert3.circuit, circuit_norm]⟩
  unfold Spec
  intro hg
  obtain ⟨hgB, hcB, hzB, hcz, hrest⟩ := h_assumptions
  obtain ⟨ha, hb, hx, hy, htx, hty, hp⟩ := hrest hg
  rw [hg] at e2 e4 e6 e8 e10 e11 e15 e17
  simp only [one_mul] at e2 e4 e6 e8 e10 e11 e15 e17
  -- halves and limbs of the contents
  have hch := eval_half_cast env (chordW input_var) (chordZ (A (eval env input_var)) (X (eval env input_var)) (Y (eval env input_var)) (TX (eval env input_var)) (TY (eval env input_var)))
    (fun k => by rw [map_chordW]; exact chordV_cast (eval env input_var) hp k)
  have hx1 := eval_half_cast env (xeq1W input_var) (xeq1Z (X (eval env input_var)) (TX (eval env input_var)))
    (fun k => by rw [map_xeq1W]; exact xeq1V_cast (eval env input_var) k)
  have hun := eval_limb_cast env (uniW input_var) (uniZ (A (eval env input_var)) (X (eval env input_var)) (Y (eval env input_var)) (TX (eval env input_var)) (TY (eval env input_var)))
    (fun k => by rw [map_uniW]; exact uniV_cast (eval env input_var) hp k)
  have hye := eval_limb_cast env (yeqW input_var) (yeqZ (Y (eval env input_var)) (TY (eval env input_var)) (-1))
    (fun k => by rw [map_yeqW]; exact yeqV_cast (eval env input_var) k)
  have hx2 := eval_half_cast env (xeq2W input_var) (xeq2Z (A (eval env input_var)) (X (eval env input_var)) (TX (eval env input_var)))
    (fun k => by rw [map_xeq2W]; exact xeq2V_cast (eval env input_var) hp k)
  have hr2 := eval_half_cast env (rel2W input_var) (rel2Z' (A (eval env input_var)) (B (eval env input_var)) (X (eval env input_var)) (Y (eval env input_var)) (TX (eval env input_var)))
    (fun k => by rw [map_rel2W]; exact rel2V_cast (eval env input_var) hp k)
  -- slot rel1
  have hs1 : env.get (i₀ + 1) = ((lowHalf (Z1 (eval env input_var)) : ℤ) : Field) ∧
      env.get (i₀ + 1 + 1 + 1) = ((highHalf (Z1 (eval env input_var)) : ℤ) : Field) := by
    rw [e2, e4, e1, e3, hch.1, hch.2, hx1.1, hx1.2]
    rcases hcB with hc | hc <;> simp only [Z1, hc, zero_ne_one, ↓reduceIte] <;> constructor <;> ring
  have hb1 := slot_half_bounds .rel1 (Z1 (eval env input_var)) (Z1_bounds hn (eval env input_var) ⟨hgB, hcB, hzB, hcz, hrest⟩ hg)
  have hm1 := Cert.model .rel1 #v[env.get (i₀ + 1), env.get (i₀ + 1 + 1 + 1)]
    (lowHalf (Z1 (eval env input_var))) (highHalf (Z1 (eval env input_var))) hb1.1 hb1.2 hs1.1 hs1.2
  have hv1 : valZ (Z1 (eval env input_var)) = 0 := by
    rw [← dvd_iff, eval_eq_halves]
    exact hm1.2.mp (c1 hm1.1)
  -- slot uni
  have hs2 : env.get (i₀ + 1 + 1 + 1 + 1 + 1) = ((limb0 (Z2 (eval env input_var)) : ℤ) : Field) ∧
      env.get (i₀ + 1 + 1 + 1 + 1 + 1 + 1 + 1) = ((limb1 (Z2 (eval env input_var)) : ℤ) : Field) ∧
      env.get (i₀ + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) = ((limb2 (Z2 (eval env input_var)) : ℤ) : Field) := by
    rw [e6, e8, e10, e5, e7, e9, hun.1, hun.2.1, hun.2.2, hye.1, hye.2.1, hye.2.2]
    rcases hcB with hc | hc <;> simp only [Z2, hc, zero_ne_one, ↓reduceIte] <;>
      refine ⟨by ring, by ring, by ring⟩
  have hb2 := uni_limb_bounds (Z2 (eval env input_var)) (Z2_bounds hn (eval env input_var) ⟨hgB, hcB, hzB, hcz, hrest⟩ hg)
  have hm2 := Cert3.model #v[env.get (i₀ + 1 + 1 + 1 + 1 + 1), env.get (i₀ + 1 + 1 + 1 + 1 + 1 + 1 + 1),
      env.get (i₀ + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)]
    (limb0 (Z2 (eval env input_var))) (limb1 (Z2 (eval env input_var))) (limb2 (Z2 (eval env input_var))) hb2.1 hb2.2.1 hb2.2.2 hs2.1 hs2.2.1 hs2.2.2
  have hv2 : valZ (Z2 (eval env input_var)) = 0 := by
    rw [← dvd_iff, eval_eq_limbs]
    exact hm2.2.mp (c2 hm2.1)
  -- slot xeq
  have hs3 : env.get (i₀ + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) =
        ((lowHalf (Z3 (eval env input_var)) : ℤ) : Field) ∧
      env.get (i₀ + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) =
        ((highHalf (Z3 (eval env input_var)) : ℤ) : Field) := by
    rw [e12, e13, e11, hx2.1, hx2.2]
    rcases hzB with hz | hz <;> simp only [Z3, hz, zero_ne_one, ↓reduceIte, lowHalf, highHalf] <;>
      push_cast <;> constructor <;> ring
  have hb3 := slot_half_bounds .xeq (Z3 (eval env input_var)) (Z3_bounds (eval env input_var) ⟨hgB, hcB, hzB, hcz, hrest⟩ hg)
  have hm3 := Cert.model .xeq #v[env.get (i₀ + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1),
      env.get (i₀ + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)]
    (lowHalf (Z3 (eval env input_var))) (highHalf (Z3 (eval env input_var))) hb3.1 hb3.2 hs3.1 hs3.2
  have hv3 : valZ (Z3 (eval env input_var)) = 0 := by
    rw [← dvd_iff, eval_eq_halves]
    exact hm3.2.mp (c3 hm3.1)
  -- slot rel2
  have hs4 : env.get (i₀ + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) =
        ((lowHalf (Z4 (eval env input_var)) : ℤ) : Field) ∧
      env.get (i₀ + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) =
        ((highHalf (Z4 (eval env input_var)) : ℤ) : Field) := by
    rw [e15, e17, e14, e16, hr2.1, hr2.2]
    rcases hcB with hc | hc <;> rcases hzB with hz | hz
    · simp only [Z4, hc, hz, and_self, ↓reduceIte]; constructor <;> ring
    · simp only [Z4, hc, hz, one_ne_zero, and_false, ↓reduceIte, lowHalf, highHalf]
      push_cast; constructor <;> ring
    · simp only [Z4, hc, hz, one_ne_zero, false_and, ↓reduceIte, lowHalf, highHalf]
      push_cast; constructor <;> ring
    · exfalso; rw [hc, hz, one_mul] at hcz; exact one_ne_zero hcz
  have hb4 := slot_half_bounds .rel2 (Z4 (eval env input_var)) (Z4_bounds hn (eval env input_var) ⟨hgB, hcB, hzB, hcz, hrest⟩ hg)
  have hm4 := Cert.model .rel2 #v[env.get (i₀ + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1),
      env.get (i₀ + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)]
    (lowHalf (Z4 (eval env input_var))) (highHalf (Z4 (eval env input_var))) hb4.1 hb4.2 hs4.1 hs4.2
  have hv4 : valZ (Z4 (eval env input_var)) = 0 := by
    rw [← dvd_iff, eval_eq_halves]
    exact hm4.2.mp (c4 hm4.1)
  have v1 := Z1_value (eval env input_var) hcB hv1
  have v2 := Z2_value (eval env input_var) hcB hv2
  have v3 := Z3_value (eval env input_var) hv3
  have v4 := Z4_value (eval env input_var) hv4
  exact ⟨fun hc => ⟨v1.1 hc, v2.1 hc⟩, fun hc => ⟨v1.2 hc, v2.2 hc⟩, v3, v4⟩

/-! ### Completeness -/

def G1 (i : Inputs Field) : Words ℤ := if i.gate = 1 then Z1 i else fun _ => 0
def G2 (i : Inputs Field) : Words ℤ := if i.gate = 1 then Z2 i else fun _ => 0
def G3 (i : Inputs Field) : Words ℤ := if i.gate = 1 then Z3 i else fun _ => 0
def G4 (i : Inputs Field) : Words ℤ := if i.gate = 1 then Z4 i else fun _ => 0

lemma G1_bounds {n : ℕ} (hn : n ≤ depth) (i : Inputs Field) (h : Assumptions n i) :
    ∀ k, slotLo .rel1 k ≤ G1 i k ∧ G1 i k ≤ slotHi .rel1 k := by
  unfold G1; split_ifs with hg
  · exact Z1_bounds hn i h hg
  · exact slot_zero .rel1
lemma G2_bounds {n : ℕ} (hn : n ≤ depth) (i : Inputs Field) (h : Assumptions n i) :
    ∀ k, uniLo k ≤ G2 i k ∧ G2 i k ≤ uniHi k := by
  unfold G2; split_ifs with hg
  · exact Z2_bounds hn i h hg
  · exact uni_zero
lemma G3_bounds {n : ℕ} (i : Inputs Field) (h : Assumptions n i) :
    ∀ k, slotLo .xeq k ≤ G3 i k ∧ G3 i k ≤ slotHi .xeq k := by
  unfold G3; split_ifs with hg
  · exact Z3_bounds i h hg
  · exact slot_zero .xeq
lemma G4_bounds {n : ℕ} (hn : n ≤ depth) (i : Inputs Field) (h : Assumptions n i) :
    ∀ k, slotLo .rel2 k ≤ G4 i k ∧ G4 i k ≤ slotHi .rel2 k := by
  unfold G4; split_ifs with hg
  · exact Z4_bounds hn i h hg
  · exact slot_zero .rel2

lemma valZ_zero : valZ (fun _ => (0 : ℤ)) = 0 := by
  simp [valZ, Sparse32.eval]

lemma G1_value (i : Inputs Field) (hc : IsBool i.cflag) (hs : Spec i) : valZ (G1 i) = 0 := by
  unfold G1; split_ifs with hg
  · have hsp := hs hg
    unfold Z1
    rcases hc with hc | hc
    · simp only [hc, zero_ne_one, ↓reduceIte, A, X, Y, TX, TY]
      rw [chordZ_value]; exact (hsp.1 hc).1
    · simp only [hc, ↓reduceIte, X, TX]
      rw [xeq1Z_value]; exact (hsp.2.1 hc).1
  · exact valZ_zero

lemma G2_value (i : Inputs Field) (hc : IsBool i.cflag) (hs : Spec i) : valZ (G2 i) = 0 := by
  unfold G2; split_ifs with hg
  · have hsp := hs hg
    unfold Z2
    rcases hc with hc | hc
    · simp only [hc, zero_ne_one, ↓reduceIte, A, X, Y, TX, TY]
      rw [uniZ_value]; exact (hsp.1 hc).2
    · simp only [hc, ↓reduceIte, Y, TY]
      rw [yeqZ_value]; push_cast
      have := (hsp.2.1 hc).2
      simp only [ry, tY] at this
      linear_combination this
  · exact valZ_zero

lemma G3_value (i : Inputs Field) (hz : IsBool i.zflag) (hs : Spec i) : valZ (G3 i) = 0 := by
  unfold G3; split_ifs with hg
  · have hsp := hs hg
    unfold Z3
    rcases hz with hz | hz
    · simp only [hz, zero_ne_one, ↓reduceIte]; exact valZ_zero
    · simp only [hz, ↓reduceIte, A, X, TX]
      rw [xeq2Z_value, xSZ_value]; exact hsp.2.2.1 hz
  · exact valZ_zero

lemma G4_value (i : Inputs Field) (hs : Spec i) : valZ (G4 i) = 0 := by
  unfold G4; split_ifs with hg
  · have hsp := hs hg
    unfold Z4
    split_ifs with hcz
    · simp only [A, B, X, Y, TX]
      rw [rel2Z_value, xSZ_value]; exact hsp.2.2.2 hcz.1 hcz.2
    · exact valZ_zero
  · exact valZ_zero

theorem completeness (n : ℕ) (hn : n ≤ depth) :
    FormalAssertion.Completeness Field main (Assumptions n) Spec := by
  circuit_proof_start_core
  subst h_input
  simp only [main, MulCell.circuit, MulCell.Assumptions, MulCell.Spec, MulCell.elaborated,
    Cert.circuit, Cert3.circuit, circuit_norm] at h_env ⊢
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17⟩ := h_env
  have hi : eval env.toEnvironment input_var = eval env input_var := by simp only [circuit_norm]
  rw [← hi] at h_assumptions h_spec
  have hg' : Expression.eval env.toEnvironment input_var.gate = (eval env.toEnvironment input_var).gate := by
    simp only [circuit_norm]
  have hc' : Expression.eval env.toEnvironment input_var.cflag = (eval env.toEnvironment input_var).cflag := by
    simp only [circuit_norm]
  have hz' : Expression.eval env.toEnvironment input_var.zflag = (eval env.toEnvironment input_var).zflag := by
    simp only [circuit_norm]
  rw [hg'] at e2 e4 e6 e8 e10 e11 e15 e17
  rw [hc'] at e1 e3 e5 e7 e9 e14 e16
  rw [hz'] at e11 e14 e16
  obtain ⟨hgB, hcB, hzB, hcz, hrest⟩ := h_assumptions
  have hzero_lo : lowHalf (fun _ : Fin 8 => (0 : ℤ)) = 0 := by simp [lowHalf]
  have hzero_hi : highHalf (fun _ : Fin 8 => (0 : ℤ)) = 0 := by simp [highHalf]
  have hzero_l0 : limb0 (fun _ : Fin 8 => (0 : ℤ)) = 0 := by simp [limb0]
  have hzero_l1 : limb1 (fun _ : Fin 8 => (0 : ℤ)) = 0 := by simp [limb1]
  have hzero_l2 : limb2 (fun _ : Fin 8 => (0 : ℤ)) = 0 := by simp [limb2]
  rcases hgB with hg | hg
  · -- gate = 0: every slot certifies zero
    rw [hg] at e2 e4 e6 e8 e10 e11 e15 e17
    simp only [zero_mul] at e2 e4 e6 e8 e10 e11 e15 e17
    rw [e11] at e12 e13
    simp only [zero_mul] at e12 e13
    have hb1 := slot_half_bounds .rel1 (fun _ => 0) (slot_zero .rel1)
    have hb2 := uni_limb_bounds (fun _ => 0) uni_zero
    have hb3 := slot_half_bounds .xeq (fun _ => 0) (slot_zero .xeq)
    have hb4 := slot_half_bounds .rel2 (fun _ => 0) (slot_zero .rel2)
    rw [hzero_lo, hzero_hi] at hb1 hb3 hb4
    rw [hzero_l0, hzero_l1, hzero_l2] at hb2
    have hm1 := Cert.model .rel1 #v[env.get (i₀ + 1), env.get (i₀ + 1 + 1 + 1)] 0 0 hb1.1 hb1.2
      (by rw [e2]; simp) (by rw [e4]; simp)
    have hm2 := Cert3.model #v[env.get (i₀ + 1 + 1 + 1 + 1 + 1),
        env.get (i₀ + 1 + 1 + 1 + 1 + 1 + 1 + 1), env.get (i₀ + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)]
      0 0 0 hb2.1 hb2.2.1 hb2.2.2 (by rw [e6]; simp) (by rw [e8]; simp) (by rw [e10]; simp)
    have hm3 := Cert.model .xeq #v[env.get (i₀ + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1),
        env.get (i₀ + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)] 0 0 hb3.1 hb3.2
      (by rw [e12]; simp) (by rw [e13]; simp)
    have hm4 := Cert.model .rel2 #v[env.get (i₀ + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1),
        env.get (i₀ + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)] 0 0 hb4.1 hb4.2
      (by rw [e15]; simp) (by rw [e17]; simp)
    exact ⟨⟨hm1.1, hm1.2.mpr (by simp)⟩, ⟨hm2.1, hm2.2.mpr (by simp)⟩, ⟨hm3.1, hm3.2.mpr (by simp)⟩,
      ⟨hm4.1, hm4.2.mpr (by simp)⟩⟩
  · -- gate = 1: the honest contents
    obtain ⟨ha, hb, hx, hy, htx, hty, hp⟩ := hrest hg
    sorry
def circuit (n : ℕ) (hn : n ≤ depth) : FormalAssertion Field Inputs where
  main := main
  Assumptions := Assumptions n
  Spec := Spec
  soundness := soundness n hn
  completeness := completeness n hn

end Solution.Secp256k1ScalarMulFixedBase.LazyVar.Certs
