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

def packExpr (y : Var Emu Field) : Var (fields 2) Field :=
  Vector.ofFn fun i : Fin 2 => y[2*i.val]'(by dsimp [numLimbs]; omega) +
    (2^64 : Field)*y[2*i.val+1]'(by dsimp [numLimbs]; omega)

def Consistent (p : Point Field) : Prop := p.halves = pack p.point.y

def AffinePoint (p : Var Point Field) : Prop :=
  AffineW p.point.x ∧ AffineW p.halves

def expand (h : fields 2 Field) : Emu Field :=
  Vector.ofFn fun i : Fin 4 => if i.val = 0 then h[0] else if i.val = 2 then h[1] else 0

def expandExpr (h : Var (fields 2) Field) : Var Emu Field :=
  Vector.ofFn fun i : Fin 4 => if i.val = 0 then h[0] else if i.val = 2 then h[1] else 0

@[simp] theorem eval_expandExpr (env : Environment Field) (h : Var (fields 2) Field) :
    eval env (expandExpr h) = expand (eval env h) := by
  simp only [expandExpr, expand, circuit_norm]
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_map, Vector.getElem_ofFn]
  split_ifs <;> rfl

theorem affine_expandExpr (h : Var (fields 2) Field) (hh : AffineW h) :
    AffineW (expandExpr h) := by
  intro i hi
  rw [expandExpr, Vector.getElem_ofFn]
  split_ifs
  · exact hh 0 (by decide)
  · exact hh 1 (by decide)
  · exact Affine.zero

@[simp] theorem eval_packExpr (env : Environment Field) (y : Var Emu Field) :
    eval env (packExpr y) = pack (eval env y) := by
  simp only [packExpr, pack, circuit_norm]
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_map, Vector.getElem_ofFn, Expression.eval]

theorem affine_packExpr (y : Var Emu Field) (hy : AffineW y) :
    AffineW (packExpr y) := by
  intro i hi
  rw [packExpr, Vector.getElem_ofFn]
  exact Affine.add (hy _ (by dsimp [numLimbs]; omega))
    (Affine.fconst_mul _ (hy _ (by dsimp [numLimbs]; omega)))

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

lemma eval_affineGhost (env : Environment Field) (s neg : Expression Field) (c : Field) :
    Expression.eval env (s * (c - (2 : Field) * neg) + neg) =
      Expression.eval env s * (c - 2 * Expression.eval env neg) + Expression.eval env neg := by
  simp only [circuit_norm]
  ring

lemma ghostY_get_formula (s : Expression Field)
    (blk : Var (fields 5) Field) (h4 : Var (fields 15) Field)
    (h6 : Var (fields 48) Field) (h7 : Var (fields 64) Field)
    (o4 : Var (fields 15) Field) (o5 : Var (fields 16) Field)
    (table : Nat → Nat) (i : Nat) (hi : i < 4) :
    (ghostY s blk h4 h6 h7 o4 o5 table)[i]'hi =
      s * (((limbOfNat P256 i : Nat) : Field) -
        (2 : Field) * ghostSelected i blk h4 h6 h7 o4 o5 (fun j => P256-table j)) +
        ghostSelected i blk h4 h6 h7 o4 o5 (fun j => P256-table j) := by
  rw [ghostY, Vector.getElem_ofFn]

lemma eval_ghostY_formula (env : Environment Field) (s : Expression Field)
    (blk : Var (fields 5) Field) (h4 : Var (fields 15) Field)
    (h6 : Var (fields 48) Field) (h7 : Var (fields 64) Field)
    (o4 : Var (fields 15) Field) (o5 : Var (fields 16) Field)
    (table : Nat → Nat) (i : Nat) (hi : i < 4) :
    Expression.eval env ((ghostY s blk h4 h6 h7 o4 o5 table)[i]'hi) =
      Expression.eval env s * (((limbOfNat P256 i : Nat) : Field) -
        2 * Expression.eval env (ghostSelected i blk h4 h6 h7 o4 o5 (fun j => P256-table j))) +
        Expression.eval env (ghostSelected i blk h4 h6 h7 o4 o5 (fun j => P256-table j)) := by
  rw [ghostY_get_formula]
  exact eval_affineGhost env s
    (ghostSelected i blk h4 h6 h7 o4 o5 (fun j => P256-table j))
    ((limbOfNat P256 i : Nat) : Field)

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

instance elaborated (xt yt : Nat → Nat) :
    ElaboratedCircuit Field (fields 13) Packed.Point (main xt yt) := by
  elaborate_circuit

def Assumptions := Select13.Assumptions

def Spec (xt yt : Nat → Nat) (b : fields 13 Field) (out : Packed.Point Field) : Prop :=
  Select13.Spec xt yt b out.point ∧ Packed.Consistent out

def selectCost : Count := ⟨256,256⟩

theorem costIs_main (xt yt : Nat → Nat) (b : Var (fields 13) Field) :
    CostIs (main xt yt b) selectCost := by
  rw [show selectCost = ⟨12,0⟩ + (⟨0,12⟩ + (⟨5,0⟩ + (⟨0,5⟩ + (⟨9,0⟩ +
    (⟨0,9⟩ + (⟨45,0⟩ + (⟨0,45⟩ + (⟨63,0⟩ + (⟨0,63⟩ + (⟨9,0⟩ + (⟨0,9⟩ +
    (⟨15,0⟩ + (⟨0,15⟩ +
    (⟨64,0⟩ + (⟨0,64⟩ + (⟨32,0⟩ + (⟨0,32⟩ +
    (⟨2,0⟩ + (⟨0,2⟩ + (Count.zero))))))))))))))))))))
    from by decide]
  unfold main
  refine CostIs.bind (CostIs.provableWitness _) fun _ => ?_
  refine CostIs.bind (CostIs.forEach fun a k => CostIs.assertZero a k) fun _ => ?_
  refine CostIs.bind (CostIs.provableWitness _) fun _ => ?_
  refine CostIs.bind (CostIs.forEach fun a k => CostIs.assertZero a k) fun _ => ?_
  refine CostIs.bind (CostIs.provableWitness _) fun _ => ?_
  refine CostIs.bind (CostIs.forEach fun a k => CostIs.assertZero a k) fun _ => ?_
  refine CostIs.bind (CostIs.provableWitness _) fun _ => ?_
  refine CostIs.bind (CostIs.forEach fun a k => CostIs.assertZero a k) fun _ => ?_
  refine CostIs.bind (CostIs.provableWitness _) fun _ => ?_
  refine CostIs.bind (CostIs.forEach fun a k => CostIs.assertZero a k) fun _ => ?_
  refine CostIs.bind (CostIs.provableWitness _) fun _ => ?_
  refine CostIs.bind (CostIs.forEach fun a k => CostIs.assertZero a k) fun _ => ?_
  refine CostIs.bind (CostIs.provableWitness _) fun _ => ?_
  refine CostIs.bind (CostIs.forEach fun a k => CostIs.assertZero a k) fun _ => ?_
  refine CostIs.bind (CostIs.provableWitness _) fun _ => ?_
  refine CostIs.bind (CostIs.forEach fun a k => CostIs.assertZero a k) fun _ => ?_
  refine CostIs.bind (CostIs.provableWitness _) fun _ => ?_
  refine CostIs.bind (CostIs.forEach fun a k => CostIs.assertZero a k) fun _ => ?_
  refine CostIs.bind (CostIs.provableWitness _) fun _ => ?_
  refine CostIs.bind (CostIs.forEach fun a k => CostIs.assertZero a k) fun _ => ?_
  exact CostIs.pure _


end Solution.Secp256k1ScalarMulFixedBase.Packed13
end

/- === PositiveTop === -/
section
namespace Solution.Secp256k1ScalarMulFixedBase.PositiveTop

open Select13 Packed13
open Challenge.CostR1CS Cost
set_option maxRecDepth 10000
set_option maxHeartbeats 32000000

/-- Append the fixed positive sign bit to the twelve magnitude bits. -/
def positiveInput (b : fields 12 Field) : fields 13 Field :=
  Vector.ofFn fun i : Fin 13 => if h : i.val < 12 then b[i.val] else 1

/-- Expression-level version of `positiveInput`. -/
def positiveVar (b : Var (fields 12) Field) : Var (fields 13) Field :=
  Vector.ofFn fun i : Fin 13 => if h : i.val < 12 then b[i.val]'h else 1

@[simp] theorem eval_positiveVar (env : Environment Field) (b : Var (fields 12) Field) :
    eval env (positiveVar b) = positiveInput (eval env b) := by
  apply Vector.ext
  intro i hi
  simp only [circuit_norm]
  rw [positiveVar, Vector.getElem_ofFn]
  unfold positiveInput
  rw [Vector.getElem_ofFn]
  split <;> simp only [circuit_norm]

@[simp] theorem positiveInput_get (b : fields 12 Field) (i : Nat) (hi : i < 12) :
    (positiveInput b)[i]'(by omega) = b[i]'hi := by
  rw [positiveInput, Vector.getElem_ofFn, dif_pos hi]

@[simp] theorem positiveInput_sign (b : fields 12 Field) :
    (positiveInput b)[12] = 1 := by
  rw [positiveInput, Vector.getElem_ofFn]
  change (if h : (12 : Nat) < 12 then b[12]'h else 1) = 1
  rw [dif_neg (by omega)]

@[simp] theorem positiveVar_get (b : Var (fields 12) Field) (i : Nat) (hi : i < 12) :
    (positiveVar b)[i]'(by omega) = b[i]'hi := by
  rw [positiveVar, Vector.getElem_ofFn, dif_pos hi]

@[simp] theorem positiveVar_sign (b : Var (fields 12) Field) :
    (positiveVar b)[12] = 1 := by
  rw [positiveVar, Vector.getElem_ofFn]
  change (if h : (12 : Nat) < 12 then b[12]'h else 1) = 1
  rw [dif_neg (by omega)]

def main (xTable yTable : Nat → Nat)
    (b : Var (fields 12) Field) : Circuit Field (Var Packed.Point Field) := do
  let pb := positiveVar b
  let blk ← ProvableType.witness (α := fields 5) fun env =>
    Vector.ofFn fun p : Fin 5 => xVal env pb (pairLo p.val) (pairLo_lt p.isLt) *
      xVal env pb (pairLo p.val + 1) (pairLo_add_lt p.isLt)
  Circuit.forEach (Vector.ofFn fun p : Fin 5 =>
    xExpr pb b (pairLo p.val) (pairLo_lt p.isLt) *
    xExpr pb b (pairLo p.val + 1) (pairLo_add_lt p.isLt) - blk[p.val]'p.isLt) assertZero
  let inner4w ← ProvableType.witness (α := fields 9) fun env =>
    Vector.ofFn fun j : Fin 9 => hot4Val env pb 0 (j.val % 3 + 4 * (j.val / 3)) (by omega)
  Circuit.forEach (Vector.ofFn fun j : Fin 9 =>
    innerP pb b blk 0 (by decide) (j.val % 3) *
    innerP pb b blk 1 (by decide) (j.val / 3) - inner4w[j.val]'j.isLt) assertZero
  let inner4 := hot4Vec pb b blk 0 (by decide) inner4w
  let inner6w ← ProvableType.witness (α := fields 45) fun env =>
    Vector.ofFn fun j : Fin 45 => hot6Val env pb (16 * (j.val / 15) + j.val % 15)
  Circuit.forEach (Vector.ofFn fun j : Fin 45 =>
    hot4 blk inner4 0 (by omega) (j.val % 15) (by omega) *
    innerP pb b blk 2 (by decide) (j.val / 15) - inner6w[j.val]'j.isLt) assertZero
  let inner6 := inner6Vec pb b blk inner6w
  let inner7w ← ProvableType.witness (α := fields 63) fun env =>
    Vector.ofFn fun j : Fin 63 => hot6Val env pb j.val * xVal env pb 6 (by omega)
  Circuit.forEach (Vector.ofFn fun j : Fin 63 =>
    hot6 blk inner4 inner6 j.val (by omega) * xExpr pb b 6 (by omega) - inner7w[j.val]'j.isLt) assertZero
  let inner7 := inner7Vec pb b inner7w
  let outer4w ← ProvableType.witness (α := fields 9) fun env =>
    Vector.ofFn fun j : Fin 9 => hot4Val env pb 3 (j.val % 3 + 4 * (j.val / 3)) (by omega)
  Circuit.forEach (Vector.ofFn fun j : Fin 9 =>
    innerP pb b blk 3 (by decide) (j.val % 3) *
    innerP pb b blk 4 (by decide) (j.val / 3) - outer4w[j.val]'j.isLt) assertZero
  let outer4 := hot4Vec pb b blk 3 (by decide) outer4w
  let outer5w ← ProvableType.witness (α := fields 15) fun env =>
    Vector.ofFn fun j : Fin 15 => hot5Val env pb (16 + j.val)
  Circuit.forEach (Vector.ofFn fun j : Fin 15 =>
    hot4 blk outer4 3 (by omega) j.val (by omega) *
    xExpr pb b 11 (by omega) - outer5w[j.val]'j.isLt) assertZero
  let outer5 := outer5Vec pb b outer5w
  let xProd ← ProvableType.witness (α := fields 64) fun env =>
    Vector.ofFn fun k : Fin 64 => outProdVal env pb (k.val/16) (k.val % 16) xTable
  Circuit.forEach (Vector.ofFn fun k : Fin 64 =>
    (hot5 blk outer4 outer5 (2 * (k.val % 16)) (by omega) +
        inner (k.val/16) (2 * (k.val % 16) + 1) blk inner4 inner6 inner7 xTable) *
      (hot5 blk outer4 outer5 (2 * (k.val % 16) + 1) (by omega) +
        inner (k.val/16) (2 * (k.val % 16)) blk inner4 inner6 inner7 xTable)
      - (corrC (k.val/16) (2 * (k.val % 16)) (2 * (k.val % 16) + 1)
            blk inner4 inner6 inner7 xTable
          + xProd[k.val]'k.isLt)) assertZero
  let yNeg ← ProvableType.witness (α := fields 32) fun env =>
    Vector.ofFn fun k : Fin 32 => halfProdVal env pb (k.val/16) (k.val%16) (fun j => P256-yTable j)
  Circuit.forEach (Vector.ofFn fun k : Fin 32 =>
    (hot5 blk outer4 outer5 (2*(k.val%16)) (by omega) +
      halfInner (k.val/16) (2*(k.val%16)+1) blk inner4 inner6 inner7 (fun j => P256-yTable j)) *
    (hot5 blk outer4 outer5 (2*(k.val%16)+1) (by omega) +
      halfInner (k.val/16) (2*(k.val%16)) blk inner4 inner6 inner7 (fun j => P256-yTable j)) -
    (halfCorr (k.val/16) (2*(k.val%16)) (2*(k.val%16)+1) blk inner4 inner6 inner7 (fun j => P256-yTable j)
      + yNeg[k.val])) assertZero
  return {
    point := {
      x := xSelExpr xTable blk inner4 inner6 inner7 xProd
      y := ghostY 1 blk inner4 inner6 inner7 outer4 outer5 yTable }
    halves := Vector.ofFn fun i : Fin 2 =>
      (halfCoeff (fun _ => P256) i.val 0 : Field) - halfSelected i.val i.isLt yNeg }

instance elaborated (xt yt : Nat → Nat) :
    ElaboratedCircuit Field (fields 12) Packed.Point (main xt yt) := by
  elaborate_circuit

def Assumptions (b : fields 12 Field) : Prop := ∀ i : Fin 12, IsBool b[i]

def Spec (xt yt : Nat → Nat) (b : fields 12 Field) (out : Packed.Point Field) : Prop :=
  Packed13.Spec xt yt (positiveInput b) out

def selectCost : Count := ⟨242,242⟩

theorem costIs_main (xt yt : Nat → Nat) (b : Var (fields 12) Field) :
    CostIs (main xt yt b) selectCost := by
  rw [show selectCost = ⟨5,0⟩ + (⟨0,5⟩ + (⟨9,0⟩ +
    (⟨0,9⟩ + (⟨45,0⟩ + (⟨0,45⟩ + (⟨63,0⟩ + (⟨0,63⟩ + (⟨9,0⟩ + (⟨0,9⟩ +
    (⟨15,0⟩ + (⟨0,15⟩ + (⟨64,0⟩ + (⟨0,64⟩ + (⟨32,0⟩ + (⟨0,32⟩ +
    Count.zero))))))))))))))) from by decide]
  unfold main
  refine CostIs.bind (CostIs.provableWitness _) fun _ => ?_
  refine CostIs.bind (CostIs.forEach fun a k => CostIs.assertZero a k) fun _ => ?_
  refine CostIs.bind (CostIs.provableWitness _) fun _ => ?_
  refine CostIs.bind (CostIs.forEach fun a k => CostIs.assertZero a k) fun _ => ?_
  refine CostIs.bind (CostIs.provableWitness _) fun _ => ?_
  refine CostIs.bind (CostIs.forEach fun a k => CostIs.assertZero a k) fun _ => ?_
  refine CostIs.bind (CostIs.provableWitness _) fun _ => ?_
  refine CostIs.bind (CostIs.forEach fun a k => CostIs.assertZero a k) fun _ => ?_
  refine CostIs.bind (CostIs.provableWitness _) fun _ => ?_
  refine CostIs.bind (CostIs.forEach fun a k => CostIs.assertZero a k) fun _ => ?_
  refine CostIs.bind (CostIs.provableWitness _) fun _ => ?_
  refine CostIs.bind (CostIs.forEach fun a k => CostIs.assertZero a k) fun _ => ?_
  refine CostIs.bind (CostIs.provableWitness _) fun _ => ?_
  refine CostIs.bind (CostIs.forEach fun a k => CostIs.assertZero a k) fun _ => ?_
  refine CostIs.bind (CostIs.provableWitness _) fun _ => ?_
  refine CostIs.bind (CostIs.forEach fun a k => CostIs.assertZero a k) fun _ => ?_
  exact CostIs.pure _

end Solution.Secp256k1ScalarMulFixedBase.PositiveTop
end

/- === ElevenSelect === -/
section
namespace Solution.Secp256k1ScalarMulFixedBase.Packed11

open Challenge.CostR1CS Cost
set_option maxRecDepth 10000
set_option maxHeartbeats 32000000

abbrev Field := F circomPrime

def bitVal (env : ProverEnvironment Field) (b : Var (fields 11) Field)
    (i : Nat) (hi : i < 11) : Field :=
  Expression.eval env.toEnvironment b[i]

def xVal (env : ProverEnvironment Field) (b : Var (fields 11) Field)
    (i : Nat) (hi : i < 10) : Field :=
  2 * bitVal env b 10 (by omega) * bitVal env b i (by omega) -
    bitVal env b 10 (by omega) - bitVal env b i (by omega) + 1

/-- A witnessed XNOR bit. -/
def xExpr (_b : Var (fields 11) Field) (w : Var (fields 10) Field)
    (i : Nat) (hi : i < 10) : Expression Field :=
  w[i]'hi

/-- Low bit of pair `p`; the five pairs are `(0,1),...,(8,9)`. -/
def pairLo (p : Nat) : Nat := 2 * p

lemma pairLo_add_lt {p : Nat} (hp : p < 5) : pairLo p + 1 < 10 := by
  unfold pairLo
  omega

lemma pairLo_lt {p : Nat} (hp : p < 5) : pairLo p < 10 := by
  have := pairLo_add_lt hp
  omega

def pairExpr (x y xy : Expression Field) (v : Nat) : Expression Field :=
  if v = 0 then 1 - x - y + xy else if v = 1 then x - xy else
  if v = 2 then y - xy else xy

def pairVal (env : ProverEnvironment Field) (b : Var (fields 11) Field)
    (p v : Nat) (hp : p < 5) : Field :=
  let x := xVal env b (pairLo p) (pairLo_lt hp)
  let y := xVal env b (pairLo p + 1) (pairLo_add_lt hp)
  (if v % 2 = 1 then x else 1-x) * (if v / 2 % 2 = 1 then y else 1-y)

def hot4Val (env : ProverEnvironment Field) (b : Var (fields 11) Field)
    (basePair v : Nat) (hp : basePair < 4) : Field :=
  pairVal env b basePair (v % 4) (by omega) *
    pairVal env b (basePair + 1) (v / 4) (by omega)

def hot6Val (env : ProverEnvironment Field) (b : Var (fields 11) Field)
    (v : Nat) : Field :=
  hot4Val env b 0 (v % 16) (by omega) * pairVal env b 2 (v / 16) (by omega)

def innerP (b : Var (fields 11) Field) (w : Var (fields 10) Field)
    (blk : Var (fields 5) Field) (p : Nat) (hp : p < 5) (u : Nat) : Expression Field :=
  pairExpr (xExpr b w (pairLo p) (pairLo_lt hp))
    (xExpr b w (pairLo p + 1) (pairLo_add_lt hp)) (blk[p]'hp) u

def hot4gen (P0 P1 : Nat → Expression Field) (h : Var (fields 9) Field) (v : Nat) :
    Expression Field :=
  if ha : v % 4 < 3 then
    (if hc : v / 4 < 3 then h[v % 4 + 3 * (v / 4)]'(by omega)
     else P0 (v % 4) - h[v % 4]'(by omega) - h[v % 4 + 3]'(by omega) -
       h[v % 4 + 6]'(by omega))
  else
    (if hc : v / 4 < 3 then
      P1 (v / 4) - h[3 * (v / 4)]'(by omega) - h[3 * (v / 4) + 1]'(by omega) -
        h[3 * (v / 4) + 2]'(by omega)
     else 0)

def hot4Vec (b : Var (fields 11) Field) (w : Var (fields 10) Field)
    (blk : Var (fields 5) Field) (p : Nat) (hp : p < 4) (h : Var (fields 9) Field) :
    Var (fields 15) Field :=
  Vector.ofFn fun v : Fin 15 =>
    hot4gen (innerP b w blk p (by omega)) (innerP b w blk (p + 1) (by omega)) h v.val

def inner6Vec (b : Var (fields 11) Field) (w : Var (fields 10) Field)
    (blk : Var (fields 5) Field) (h : Var (fields 45) Field) : Var (fields 48) Field :=
  Vector.ofFn fun v : Fin 48 =>
    if hh : v.val % 16 < 15 then h[15 * (v.val / 16) + v.val % 16]'(by omega)
    else innerP b w blk 2 (by decide) (v.val / 16) -
      (Vector.ofFn fun a : Fin 15 => h[15 * (v.val / 16) + a.val]'(by omega)).foldl (·+·) 0

def hot4 (blk : Var (fields 5) Field) (h : Var (fields 15) Field)
    (basePair : Nat) (hbase : basePair < 4) (v : Nat) (hv : v < 16) : Expression Field :=
  if _ : v = 15 then blk[basePair+1]'(by omega) - h[12] - h[13] - h[14]
  else h[v]'(by omega)

def hot6 (blk : Var (fields 5) Field) (h4 : Var (fields 15) Field)
    (h6 : Var (fields 48) Field) (v : Nat) (_hv : v < 64) : Expression Field :=
  let a := v % 16
  let c := v / 16
  if _ : c < 3 then h6[c*16+a]'(by omega)
  else hot4 blk h4 0 (by omega) a (by omega) - h6[a] - h6[16+a] - h6[32+a]

def inner (limb outer : Nat) (blk : Var (fields 5) Field)
    (h4 : Var (fields 15) Field) (h6 : Var (fields 48) Field)
    (table : Nat → Nat) : Expression Field :=
  (Vector.ofFn fun a : Fin 64 => hot6 blk h4 h6 a.val a.isLt *
    (((limbOfNat (table (64*outer+a.val)) limb : Nat) : Field))).foldl (·+·) 0

def innerVal (env : ProverEnvironment Field) (b : Var (fields 11) Field)
    (limb outer : Nat) (table : Nat → Nat) : Field :=
  ∑ a : Fin 64, hot6Val env b a.val *
    (((limbOfNat (table (64*outer+a.val)) limb : Nat) : Field))

def corrC (limb o0 o1 : Nat) (blk : Var (fields 5) Field)
    (h4 : Var (fields 15) Field) (h6 : Var (fields 48) Field)
    (table : Nat → Nat) : Expression Field :=
  (Vector.ofFn fun a : Fin 64 => hot6 blk h4 h6 a.val a.isLt *
    ((((limbOfNat (table (64*o0+a.val)) limb : Nat) : Field)) *
      (((limbOfNat (table (64*o1+a.val)) limb : Nat) : Field)))).foldl (·+·) 0

def corrVal (env : ProverEnvironment Field) (b : Var (fields 11) Field)
    (limb o0 o1 : Nat) (table : Nat → Nat) : Field :=
  ∑ a : Fin 64, hot6Val env b a.val *
    ((((limbOfNat (table (64*o0+a.val)) limb : Nat) : Field)) *
      (((limbOfNat (table (64*o1+a.val)) limb : Nat) : Field)))

def outProdVal (env : ProverEnvironment Field) (b : Var (fields 11) Field)
    (limb k : Nat) (table : Nat → Nat) : Field :=
  (hot4Val env b 3 (2*k) (by omega) + innerVal env b limb (2*k+1) table) *
    (hot4Val env b 3 (2*k+1) (by omega) + innerVal env b limb (2*k) table) -
      corrVal env b limb (2*k) (2*k+1) table

def selected2 (limb : Nat) (hl : limb < 4) (_blk : Var (fields 5) Field)
    (_h4 : Var (fields 15) Field) (_h6 : Var (fields 48) Field)
    (pA : Var (fields 32) Field) (_table : Nat → Nat) : Expression Field :=
  (Vector.ofFn fun k : Fin 8 => pA[8 * limb + k.val]'(by omega)).foldl (·+·) 0

def selectedVal2 (env : ProverEnvironment Field) (b : Var (fields 11) Field)
    (limb : Nat) (table : Nat → Nat) : Field :=
  ∑ k : Fin 8, outProdVal env b limb k.val table

def xSelExpr (xTable : Nat → Nat) (blk : Var (fields 5) Field)
    (inner4 : Var (fields 15) Field) (inner6 : Var (fields 48) Field)
    (pA : Var (fields 32) Field) : Var Emu Field :=
  Vector.ofFn fun i : Fin 4 => selected2 i.val i.isLt blk inner4 inner6 pA xTable

attribute [irreducible] xSelExpr

@[simp] theorem xSelExpr_get (xTable : Nat → Nat) (blk : Var (fields 5) Field)
    (inner4 : Var (fields 15) Field) (inner6 : Var (fields 48) Field)
    (pA : Var (fields 32) Field) (i : Nat) (hi : i < 4) :
    (xSelExpr xTable blk inner4 inner6 pA)[i]'hi =
      selected2 i hi blk inner4 inner6 pA xTable := by
  unfold xSelExpr
  rw [Vector.getElem_ofFn]

def yDeltaLimb (yTable : Nat → Nat) (idx limb : Nat) : Field :=
  ((limbOfNat (yTable idx) limb : Nat) : Field) -
    ((limbOfNat (P256 - yTable idx) limb : Nat) : Field)

def bitsVal (b : fields 11 Field) : Nat :=
  b[0].val + 2*b[1].val + 4*b[2].val + 8*b[3].val + 16*b[4].val +
  32*b[5].val + 64*b[6].val + 128*b[7].val + 256*b[8].val +
  512*b[9].val + 1024*b[10].val

def magnitudeIndex (b : fields 11 Field) : Nat :=
  if 1024 ≤ bitsVal b then bitsVal b - 1024 else 1023 - bitsVal b

def xNbit (b : fields 11 Field) (i : Nat) (hi : i < 10) : Nat :=
  if b[i].val = b[10].val then 1 else 0

def innerIndex (b : fields 11 Field) : Nat :=
  xNbit b 0 (by omega) + 2*xNbit b 1 (by omega) + 4*xNbit b 2 (by omega) +
  8*xNbit b 3 (by omega) + 16*xNbit b 4 (by omega) + 32*xNbit b 5 (by omega)

def outerIndex (b : fields 11 Field) : Nat :=
  xNbit b 6 (by omega) + 2*xNbit b 7 (by omega) + 4*xNbit b 8 (by omega) +
  8*xNbit b 9 (by omega)

def transformedIndex (b : fields 11 Field) : Nat :=
  innerIndex b + 64 * outerIndex b

lemma xNbit_le (b : fields 11 Field) (i : Nat) (hi : i < 10) : xNbit b i hi ≤ 1 := by
  unfold xNbit
  split <;> omega

lemma innerIndex_lt (b : fields 11 Field) : innerIndex b < 64 := by
  unfold innerIndex
  have h0 := xNbit_le b 0 (by omega); have h1 := xNbit_le b 1 (by omega)
  have h2 := xNbit_le b 2 (by omega); have h3 := xNbit_le b 3 (by omega)
  have h4 := xNbit_le b 4 (by omega); have h5 := xNbit_le b 5 (by omega)
  omega

lemma outerIndex_lt (b : fields 11 Field) : outerIndex b < 16 := by
  unfold outerIndex
  have h6 := xNbit_le b 6 (by omega); have h7 := xNbit_le b 7 (by omega)
  have h8 := xNbit_le b 8 (by omega); have h9 := xNbit_le b 9 (by omega)
  omega

lemma transformedIndex_lt (b : fields 11 Field) : transformedIndex b < 1024 := by
  unfold transformedIndex
  have hi := innerIndex_lt b
  have ho := outerIndex_lt b
  omega

lemma index_split (b : fields 11 Field) :
    64 * outerIndex b + innerIndex b = transformedIndex b := by
  unfold transformedIndex
  omega

def Assumptions (b : fields 11 Field) : Prop := ∀ i : Fin 11, IsBool b[i]

lemma bitsVal_lt_2048 (b : fields 11 Field) (hb : Assumptions b) : bitsVal b < 2048 := by
  have hle : ∀ (j : Nat) (hj : j < 11), b[j].val ≤ 1 := fun j hj =>
    Select.IsBool.val_le_one (hb ⟨j, hj⟩)
  unfold bitsVal
  have h0 := hle 0 (by omega); have h1 := hle 1 (by omega)
  have h2 := hle 2 (by omega); have h3 := hle 3 (by omega)
  have h4 := hle 4 (by omega); have h5 := hle 5 (by omega)
  have h6 := hle 6 (by omega); have h7 := hle 7 (by omega)
  have h8 := hle 8 (by omega); have h9 := hle 9 (by omega)
  have h10 := hle 10 (by omega)
  omega

lemma bitsVal_lt_1024_of_sign_zero (b : fields 11 Field) (hb : Assumptions b)
    (hs : b[10] = 0) : bitsVal b < 1024 := by
  have hle : ∀ (j : Nat) (hj : j < 10), b[j].val ≤ 1 := fun j hj =>
    Select.IsBool.val_le_one (hb ⟨j, by omega⟩)
  have hsval : b[10].val = 0 := by simpa using congrArg ZMod.val hs
  unfold bitsVal
  rw [hsval]
  have h0 := hle 0 (by omega); have h1 := hle 1 (by omega)
  have h2 := hle 2 (by omega); have h3 := hle 3 (by omega)
  have h4 := hle 4 (by omega); have h5 := hle 5 (by omega)
  have h6 := hle 6 (by omega); have h7 := hle 7 (by omega)
  have h8 := hle 8 (by omega); have h9 := hle 9 (by omega)
  omega

lemma bitsVal_ge_1024_of_sign_one (b : fields 11 Field) (_hb : Assumptions b)
    (hs : b[10] = 1) : 1024 ≤ bitsVal b := by
  have hsval : b[10].val = 1 := by simpa using congrArg ZMod.val hs
  unfold bitsVal
  rw [hsval]
  omega

lemma transformedIndex_eq_sign_zero (b : fields 11 Field) (hb : Assumptions b)
    (hs : b[10] = 0) : transformedIndex b = 1023 - bitsVal b := by
  have hle : ∀ (j : Nat) (hj : j < 11), b[j].val ≤ 1 := fun j hj =>
    Select.IsBool.val_le_one (hb ⟨j, hj⟩)
  have hz : ∀ x : Nat, x ≤ 1 → (if x = 0 then 1 else 0) = 1-x := by
    intro x hx; split <;> omega
  have hsval : b[10].val = 0 := by simpa using congrArg ZMod.val hs
  have h0 := hle 0 (by omega); have h1 := hle 1 (by omega)
  have h2 := hle 2 (by omega); have h3 := hle 3 (by omega)
  have h4 := hle 4 (by omega); have h5 := hle 5 (by omega)
  have h6 := hle 6 (by omega); have h7 := hle 7 (by omega)
  have h8 := hle 8 (by omega); have h9 := hle 9 (by omega)
  unfold transformedIndex innerIndex outerIndex xNbit
  rw [hsval]
  rw [hz _ (hle 0 (by omega)), hz _ (hle 1 (by omega)), hz _ (hle 2 (by omega)),
    hz _ (hle 3 (by omega)), hz _ (hle 4 (by omega)), hz _ (hle 5 (by omega)),
    hz _ (hle 6 (by omega)), hz _ (hle 7 (by omega)), hz _ (hle 8 (by omega)),
    hz _ (hle 9 (by omega)), bitsVal, hsval]
  omega

lemma transformedIndex_eq_sign_one (b : fields 11 Field) (hb : Assumptions b)
    (hs : b[10] = 1) : transformedIndex b = bitsVal b - 1024 := by
  have hle : ∀ (j : Nat) (hj : j < 11), b[j].val ≤ 1 := fun j hj =>
    Select.IsBool.val_le_one (hb ⟨j, hj⟩)
  have ho : ∀ x : Nat, x ≤ 1 → (if x = 1 then 1 else 0) = x := by
    intro x hx; split <;> omega
  have hsval : b[10].val = 1 := by simpa using congrArg ZMod.val hs
  unfold transformedIndex innerIndex outerIndex xNbit
  rw [hsval]
  rw [ho _ (hle 0 (by omega)), ho _ (hle 1 (by omega)), ho _ (hle 2 (by omega)),
    ho _ (hle 3 (by omega)), ho _ (hle 4 (by omega)), ho _ (hle 5 (by omega)),
    ho _ (hle 6 (by omega)), ho _ (hle 7 (by omega)), ho _ (hle 8 (by omega)),
    ho _ (hle 9 (by omega)), bitsVal, hsval]
  omega

lemma transformedIndex_eq (b : fields 11 Field) (hb : Assumptions b) :
    transformedIndex b = magnitudeIndex b := by
  rcases hb ⟨10, by omega⟩ with hs | hs
  · rw [transformedIndex_eq_sign_zero b hb hs, magnitudeIndex]
    rw [if_neg (by have := bitsVal_lt_1024_of_sign_zero b hb hs; omega)]
  · rw [transformedIndex_eq_sign_one b hb hs, magnitudeIndex]
    rw [if_pos (bitsVal_ge_1024_of_sign_one b hb hs)]

def halfCoeff (table : Nat → Nat) (h j : Nat) : Field :=
  ((limbOfNat (table j) (2*h) : Nat) : Field) +
    (2^64 : Field)*((limbOfNat (table j) (2*h+1) : Nat) : Field)

def halfInner (h outer : Nat) (blk : Var (fields 5) Field)
    (h4 : Var (fields 15) Field) (h6 : Var (fields 48) Field)
    (table : Nat → Nat) : Expression Field :=
  inner (2*h) outer blk h4 h6 table +
    (2^64 : Field)*inner (2*h+1) outer blk h4 h6 table

def halfInnerVal (env : ProverEnvironment Field) (b : Var (fields 11) Field)
    (h outer : Nat) (table : Nat → Nat) : Field :=
  innerVal env b (2*h) outer table + (2^64 : Field)*innerVal env b (2*h+1) outer table

def halfCorr (h o0 o1 : Nat) (blk : Var (fields 5) Field)
    (h4 : Var (fields 15) Field) (h6 : Var (fields 48) Field)
    (table : Nat → Nat) : Expression Field :=
  (Vector.ofFn fun a : Fin 64 => hot6 blk h4 h6 a.val a.isLt *
    (halfCoeff table h (64*o0+a.val) * halfCoeff table h (64*o1+a.val) : Field)).foldl (·+·) 0

def halfCorrVal (env : ProverEnvironment Field) (b : Var (fields 11) Field)
    (h o0 o1 : Nat) (table : Nat → Nat) : Field :=
  ∑ a : Fin 64, hot6Val env b a.val *
    (halfCoeff table h (64*o0+a.val) * halfCoeff table h (64*o1+a.val))

def halfProdVal (env : ProverEnvironment Field) (b : Var (fields 11) Field)
    (h k : Nat) (table : Nat → Nat) : Field :=
  (hot4Val env b 3 (2*k) (by decide) + halfInnerVal env b h (2*k+1) table) *
    (hot4Val env b 3 (2*k+1) (by decide) + halfInnerVal env b h (2*k) table) -
      halfCorrVal env b h (2*k) (2*k+1) table

def halfSelected (h : Nat) (hh : h < 2) (p : Var (fields 16) Field) : Expression Field :=
  (Vector.ofFn fun k : Fin 8 => p[8*h+k.val]'(by omega)).foldl (·+·) 0

def halfSelectedVal (env : ProverEnvironment Field) (b : Var (fields 11) Field)
    (h : Nat) (table : Nat → Nat) : Field :=
  ∑ k : Fin 8, halfProdVal env b h k.val table

/-- Proof-only y-limb selection; it emits no operation. -/
def ghostSelected (limb : Nat) (blk : Var (fields 5) Field)
    (h4 : Var (fields 15) Field) (h6 : Var (fields 48) Field)
    (o4 : Var (fields 15) Field) (table : Nat → Nat) : Expression Field :=
  (Vector.ofFn fun j : Fin 16 => hot4 blk o4 3 (by decide) j.val j.isLt *
    inner limb j.val blk h4 h6 table).foldl (·+·) 0

def ghostY (s : Expression Field) (blk : Var (fields 5) Field)
    (h4 : Var (fields 15) Field) (h6 : Var (fields 48) Field)
    (o4 : Var (fields 15) Field) (table : Nat → Nat) : Var Emu Field :=
  Vector.ofFn fun i : Fin 4 =>
    let neg := ghostSelected i.val blk h4 h6 o4 (fun j => P256-table j)
    s * (((limbOfNat P256 i.val : Nat) : Field) - (2 : Field)*neg) + neg

def main (xTable yTable : Nat → Nat)
    (b : Var (fields 11) Field) : Circuit Field (Var Packed.Point Field) := do
  let w ← ProvableType.witness (α := fields 10) fun env =>
    Vector.ofFn fun i : Fin 10 => xVal env b i.val i.isLt
  Circuit.forEach (Vector.ofFn fun i : Fin 10 =>
    b[10] * (2 : Field) * b[i.val]'(by omega) -
      (w[i.val]'i.isLt + b[10] + b[i.val]'(by omega) - 1)) assertZero
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
  let outer4w ← ProvableType.witness (α := fields 9) fun env =>
    Vector.ofFn fun j : Fin 9 => hot4Val env b 3 (j.val % 3 + 4 * (j.val / 3)) (by omega)
  Circuit.forEach (Vector.ofFn fun j : Fin 9 =>
    innerP b w blk 3 (by decide) (j.val % 3) *
    innerP b w blk 4 (by decide) (j.val / 3) - outer4w[j.val]'j.isLt) assertZero
  let outer4 := hot4Vec b w blk 3 (by decide) outer4w
  let xProd ← ProvableType.witness (α := fields 32) fun env =>
    Vector.ofFn fun k : Fin 32 => outProdVal env b (k.val/8) (k.val % 8) xTable
  Circuit.forEach (Vector.ofFn fun k : Fin 32 =>
    (hot4 blk outer4 3 (by omega) (2 * (k.val % 8)) (by omega) +
        inner (k.val/8) (2 * (k.val % 8) + 1) blk inner4 inner6 xTable) *
      (hot4 blk outer4 3 (by omega) (2 * (k.val % 8) + 1) (by omega) +
        inner (k.val/8) (2 * (k.val % 8)) blk inner4 inner6 xTable) -
      (corrC (k.val/8) (2 * (k.val % 8)) (2 * (k.val % 8) + 1)
          blk inner4 inner6 xTable + xProd[k.val]'k.isLt)) assertZero
  let yNeg ← ProvableType.witness (α := fields 16) fun env =>
    Vector.ofFn fun k : Fin 16 => halfProdVal env b (k.val/8) (k.val%8) (fun j => P256-yTable j)
  Circuit.forEach (Vector.ofFn fun k : Fin 16 =>
    (hot4 blk outer4 3 (by decide) (2*(k.val%8)) (by omega) +
      halfInner (k.val/8) (2*(k.val%8)+1) blk inner4 inner6 (fun j => P256-yTable j)) *
    (hot4 blk outer4 3 (by decide) (2*(k.val%8)+1) (by omega) +
      halfInner (k.val/8) (2*(k.val%8)) blk inner4 inner6 (fun j => P256-yTable j)) -
    (halfCorr (k.val/8) (2*(k.val%8)) (2*(k.val%8)+1) blk inner4 inner6
      (fun j => P256-yTable j) + yNeg[k.val])) assertZero
  let y ← ProvableType.witness (α := fields 2) fun env =>
    Vector.ofFn fun i : Fin 2 =>
      bitVal env b 10 (by decide) *
        (halfCoeff (fun _ => P256) i.val 0 - 2*halfSelectedVal env b i.val (fun j => P256-yTable j)) +
          halfSelectedVal env b i.val (fun j => P256-yTable j)
  Circuit.forEach (Vector.ofFn fun i : Fin 2 =>
    b[10] * ((halfCoeff (fun _ => P256) i.val 0 : Field) -
      (2 : Field)*halfSelected i.val i.isLt yNeg) +
      halfSelected i.val i.isLt yNeg - y[i.val]) assertZero
  return {
    point := {
      x := xSelExpr xTable blk inner4 inner6 xProd
      y := ghostY b[10] blk inner4 inner6 outer4 yTable }
    halves := y }

def dummyBits : Var (fields 11) Field :=
  Vector.ofFn fun _ : Fin 11 => (0 : Expression Field)

def outXAt (xt : Nat → Nat) (i0 : Nat) : Var Emu Field :=
  xSelExpr xt (varFromOffset (fields 5) (i0 + 10))
    (hot4Vec dummyBits (varFromOffset (fields 10) i0)
      (varFromOffset (fields 5) (i0 + 10)) 0 (by decide)
      (varFromOffset (fields 9) (i0 + 15)))
    (inner6Vec dummyBits (varFromOffset (fields 10) i0)
      (varFromOffset (fields 5) (i0 + 10)) (varFromOffset (fields 45) (i0 + 24)))
    (varFromOffset (fields 32) (i0 + 78))

instance elaborated (xt yt : Nat → Nat) :
    ElaboratedCircuit Field (fields 11) Packed.Point (main xt yt) := by
  elaborate_circuit

def Spec (xt yt : Nat → Nat) (b : fields 11 Field) (out : Packed.Point Field) : Prop :=
  (out.point.x = Vector.ofFn (fun i : Fin 4 =>
      ((limbOfNat (xt (magnitudeIndex b)) i.val : Nat) : Field)) ∧
   out.point.y = Vector.ofFn (fun i : Fin 4 =>
      (b[10].val : Field) *
          (((limbOfNat (yt (magnitudeIndex b)) i.val : Nat) : Field) -
           ((limbOfNat (P256 - yt (magnitudeIndex b)) i.val : Nat) : Field)) +
       ((limbOfNat (P256 - yt (magnitudeIndex b)) i.val : Nat) : Field))) ∧
  Packed.Consistent out

def selectCost : Count := ⟨128,128⟩

theorem costIs_main (xt yt : Nat → Nat) (b : Var (fields 11) Field) :
    CostIs (main xt yt b) selectCost := by
  rw [show selectCost = ⟨10,0⟩ + (⟨0,10⟩ + (⟨5,0⟩ + (⟨0,5⟩ + (⟨9,0⟩ +
    (⟨0,9⟩ + (⟨45,0⟩ + (⟨0,45⟩ + (⟨9,0⟩ + (⟨0,9⟩ +
    (⟨32,0⟩ + (⟨0,32⟩ + (⟨16,0⟩ + (⟨0,16⟩ +
    (⟨2,0⟩ + (⟨0,2⟩ + (Count.zero)))))))))))))))) from by decide]
  unfold main
  refine CostIs.bind (CostIs.provableWitness _) fun _ => ?_
  refine CostIs.bind (CostIs.forEach fun a k => CostIs.assertZero a k) fun _ => ?_
  refine CostIs.bind (CostIs.provableWitness _) fun _ => ?_
  refine CostIs.bind (CostIs.forEach fun a k => CostIs.assertZero a k) fun _ => ?_
  refine CostIs.bind (CostIs.provableWitness _) fun _ => ?_
  refine CostIs.bind (CostIs.forEach fun a k => CostIs.assertZero a k) fun _ => ?_
  refine CostIs.bind (CostIs.provableWitness _) fun _ => ?_
  refine CostIs.bind (CostIs.forEach fun a k => CostIs.assertZero a k) fun _ => ?_
  refine CostIs.bind (CostIs.provableWitness _) fun _ => ?_
  refine CostIs.bind (CostIs.forEach fun a k => CostIs.assertZero a k) fun _ => ?_
  refine CostIs.bind (CostIs.provableWitness _) fun _ => ?_
  refine CostIs.bind (CostIs.forEach fun a k => CostIs.assertZero a k) fun _ => ?_
  refine CostIs.bind (CostIs.provableWitness _) fun _ => ?_
  refine CostIs.bind (CostIs.forEach fun a k => CostIs.assertZero a k) fun _ => ?_
  refine CostIs.bind (CostIs.provableWitness _) fun _ => ?_
  refine CostIs.bind (CostIs.forEach fun a k => CostIs.assertZero a k) fun _ => ?_
  exact CostIs.pure _

end Solution.Secp256k1ScalarMulFixedBase.Packed11
end


end DonorFile6_0

-- Adapted donor module: CollisionFree
section DonorFile6_1

namespace Solution.Secp256k1ScalarMulFixedBase.CollisionFree

open Specs.ShortWeierstrass Specs.Secp256k1
open Solution.Secp256k1ScalarMulFixedBase.GroupLaw
open Solution.Secp256k1ScalarMulFixedBase.OrderFacts

theorem digit_facts (w : ℕ) (hw : 0 < w) (m : ℕ) (hm : m < 2 ^ w) :
    Odd (2 * (m : ℤ) + 1 - 2 ^ w) ∧ |2 * (m : ℤ) + 1 - 2 ^ w| < 2 ^ w := by
  obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
  have hm' : (m : ℤ) < 2 ^ (w' + 1) := by exact_mod_cast hm
  have hp : (0 : ℤ) < 2 ^ (w' + 1) := by positivity
  refine ⟨⟨(m : ℤ) - 2 ^ w', by rw [pow_succ]; ring⟩, ?_⟩
  rw [abs_lt]
  constructor
  · linarith [Int.natCast_nonneg m]
  · linarith

private lemma abs_core {X Y s d : ℤ} (hX : 0 < X)
    (hs : |s| < X) (hd : |d| < Y) :
    |s + d * X| < X * Y ∧ |s - d * X| < X * Y := by
  have h1 : |d * X| = |d| * X := by
    rw [abs_mul, abs_of_nonneg hX.le]
  have h2 : |d| * X ≤ (Y - 1) * X := by
    apply mul_le_mul_of_nonneg_right _ hX.le
    omega
  have h3 : (X - 1) + (Y - 1) * X = X * Y - 1 := by ring
  have hs' : |s| ≤ X - 1 := by omega
  constructor
  · calc |s + d * X| ≤ |s| + |d * X| := abs_add_le _ _
      _ ≤ (X - 1) + (Y - 1) * X := by rw [h1]; linarith
      _ < X * Y := by omega
  · calc |s - d * X| = |s + -(d * X)| := by rw [sub_eq_add_neg]
      _ ≤ |s| + |-(d * X)| := abs_add_le _ _
      _ = |s| + |d * X| := by rw [abs_neg]
      _ ≤ (X - 1) + (Y - 1) * X := by rw [h1]; linarith
      _ < X * Y := by omega

private lemma two_pow_split (w t : ℕ) :
    (2 : ℤ) ^ (w * (t + 2)) = 2 ^ (w * (t + 1)) * 2 ^ w := by
  rw [show w * (t + 2) = w * (t + 1) + w by ring, pow_add]

theorem sum_step (w t : ℕ) (hw : 0 < w) {s d : ℤ}
    (hs : Odd s) (hsb : |s| < 2 ^ (w * (t + 1)))
    (hd : Odd d) (hdb : |d| < 2 ^ w) :
    Odd (s + d * 2 ^ (w * (t + 1))) ∧
      |s + d * 2 ^ (w * (t + 1))| < 2 ^ (w * (t + 2)) := by
  have hK : w * (t + 1) ≠ 0 := by positivity
  have heven : Even (d * 2 ^ (w * (t + 1))) :=
    (Int.even_pow.mpr ⟨even_two, hK⟩).mul_left d
  have hcore := (abs_core (by positivity) hsb hdb).1
  rw [← two_pow_split w t] at hcore
  exact ⟨hs.add_even heven, hcore⟩

theorem site_int_facts (w t : ℕ) (hw : 0 < w)
    (hsafe : (2 : ℤ) ^ (w * (t + 2)) ≤ ((order : ℕ) : ℤ))
    {s d : ℤ} (hs : Odd s) (hsb : |s| < 2 ^ (w * (t + 1)))
    (hd : Odd d) (hdb : |d| < 2 ^ w) :
    s ≠ d * 2 ^ (w * (t + 1)) ∧
    s + d * 2 ^ (w * (t + 1)) ≠ 0 ∧
    |s - d * 2 ^ (w * (t + 1))| < ((order : ℕ) : ℤ) ∧
    |s + d * 2 ^ (w * (t + 1))| < ((order : ℕ) : ℤ) ∧
    d * 2 ^ (w * (t + 1)) ≠ 0 ∧
    |d * 2 ^ (w * (t + 1))| < ((order : ℕ) : ℤ) ∧
    s ≠ 0 ∧ |s| < ((order : ℕ) : ℤ) := by
  have hK : w * (t + 1) ≠ 0 := by positivity
  have hp : (0 : ℤ) < 2 ^ (w * (t + 1)) := by positivity
  have heven : Even (d * 2 ^ (w * (t + 1))) :=
    (Int.even_pow.mpr ⟨even_two, hK⟩).mul_left d
  have hd0 : d ≠ 0 := by rintro rfl; simp at hd
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  have hcore := abs_core hp hsb hdb
  rw [← two_pow_split w t] at hcore
  have hDabs : |d * 2 ^ (w * (t + 1))| = |d| * 2 ^ (w * (t + 1)) := by
    rw [abs_mul, abs_of_nonneg hp.le]
  have hDlt : |d * 2 ^ (w * (t + 1))| < 2 ^ (w * (t + 2)) := by
    rw [hDabs, two_pow_split w t, mul_comm (|d|)]
    have h2w : (0 : ℤ) < 2 ^ w := by positivity
    exact mul_lt_mul_of_pos_left hdb hp
  refine ⟨?_, ?_, by omega, by omega, mul_ne_zero hd0 (by positivity), by omega,
    hs0, ?_⟩
  · rintro rfl
    exact (Int.not_odd_iff_even.mpr heven) hs
  · intro hc
    have hodd : Odd (s + d * 2 ^ (w * (t + 1))) := hs.add_even heven
    rw [hc] at hodd
    simp at hodd
  · have h1 : (2 : ℤ) ^ (w * (t + 1)) ≤ 2 ^ (w * (t + 2)) :=
      pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left w (by omega))
    omega

theorem site_xcoord_ne (w t : ℕ) (hw : 0 < w)
    (hsafe : (2 : ℤ) ^ (w * (t + 2)) ≤ ((order : ℕ) : ℤ))
    {s d : ℤ} (hs : Odd s) (hsb : |s| < 2 ^ (w * (t + 1)))
    (hd : Odd d) (hdb : |d| < 2 ^ w)
    {PA PT : Point Fp}
    (hA : zsmul s (.affine G) = .affine PA)
    (hT : zsmul (d * 2 ^ (w * (t + 1))) (.affine G) = .affine PT) :
    PA.x ≠ PT.x := by
  obtain ⟨hne, hsum0, hsub, hsum, -, -, -, -⟩ :=
    site_int_facts w t hw hsafe hs hsb hd hdb
  have hocA : OnCurve curve PA := by
    have h := zsmul_onCurveOrInfinity hGoc s
    rw [hA] at h; exact h
  have hocT : OnCurve curve PT := by
    have h := zsmul_onCurveOrInfinity hGoc (d * 2 ^ (w * (t + 1)))
    rw [hT] at h; exact h
  have h1 : GroupPoint.affine PA ≠ .affine PT := by
    rw [← hA, ← hT]
    exact zsmul_inj _ _ hne hsub
  have h2 : GroupPoint.affine PA ≠ specNeg (.affine PT) := by
    rw [← hA, ← hT]
    exact zsmul_ne_neg _ _ hsum0 hsum
  exact x_ne_of_ne hocA hocT h1 h2

theorem add_eq_chord {P Q : Point Fp} (hx : P.x ≠ Q.x) :
    add curve (.affine P) (.affine Q) = .affine (chord P Q) := by
  rcases P with ⟨px, py⟩
  rcases Q with ⟨qx, qy⟩
  show (if px = qx then if py = -qy then GroupPoint.infinity
      else .affine (tangent curve ⟨px, py⟩) else .affine (chord ⟨px, py⟩ ⟨qx, qy⟩))
      = .affine (chord ⟨px, py⟩ ⟨qx, qy⟩)
  rw [if_neg hx]

end Solution.Secp256k1ScalarMulFixedBase.CollisionFree

end DonorFile6_1

-- Adapted donor module: Recode
section DonorFile6_2

namespace Solution.Secp256k1ScalarMulFixedBase
namespace Recode

def derivedDigits (bits : Var (fields 256) (F circomPrime)) :
    Var (fields 256) (F circomPrime) :=
  Vector.ofFn fun c : Fin 256 =>
    if h : c.val < 255 then bits[254 - c.val]'(by omega) else 1

def main (bits : Var (fields 256) (F circomPrime)) :
    Circuit (F circomPrime) (Var (fields 256) (F circomPrime)) :=
  pure (derivedDigits bits)

instance elaborated :
    ElaboratedCircuit (F circomPrime) (fields 256) (fields 256) main where

  localLength _ := 0
  output input _ := derivedDigits input
  localLength_eq := by
    intro input offset
    rfl
  output_eq := by
    intro input offset
    rfl
  subcircuitsConsistent := by
    intro input offset
    rw [main, Circuit.pure_operations_eq]
    trivial
  channelsLawful := by
    intro input offset
    rw [main, Circuit.pure_operations_eq]
    exact Operations.channelsLawful_nil

def windowVal (out : fields 256 (F circomPrime)) (i : ℕ) : ℕ :=
  if h : i < 28 then
    (out[9 * i]'(by omega)).val + 2 * (out[9 * i + 1]'(by omega)).val
      + 4 * (out[9 * i + 2]'(by omega)).val + 8 * (out[9 * i + 3]'(by omega)).val
      + 16 * (out[9 * i + 4]'(by omega)).val + 32 * (out[9 * i + 5]'(by omega)).val
      + 64 * (out[9 * i + 6]'(by omega)).val + 128 * (out[9 * i + 7]'(by omega)).val
      + 256 * (out[9 * i + 8]'(by omega)).val
  else if i = 28 then
    (out[252]'(by omega)).val + 2 * (out[253]'(by omega)).val
      + 4 * (out[254]'(by omega)).val + 8 * (out[255]'(by omega)).val
  else 0

def digitVal (out : fields 256 (F circomPrime)) (i : ℕ) : ℤ :=
  2 * (windowVal out i : ℤ) + 1 - (if i < 28 then 512 else 16)

def Assumptions (bits : fields 256 (F circomPrime)) : Prop :=
  ∀ i : Fin 256, IsBool bits[i]

def Spec (bits : fields 256 (F circomPrime))
    (out : fields 256 (F circomPrime)) : Prop :=
  (∀ c : Fin 256, IsBool out[c]) ∧
  ∑ i ∈ Finset.range 29, digitVal out i * 2 ^ (9 * i)
    = (Specs.ShortWeierstrass.scalarOfBits (bits.map ZMod.val) : ℤ)
      + 1 - (bits[255]'(by omega)).val

end Recode
end Solution.Secp256k1ScalarMulFixedBase

namespace Solution.Secp256k1ScalarMulFixedBase
namespace Recode

section ComputableWitness
open Challenge.Utils.ComputableWitnessLemmas

set_option maxHeartbeats 1600000 in
theorem structuralCW {Parent : TypeMap} [CircuitType Parent]
    (parentInput : Var Parent (F circomPrime))
    (bits : Var (fields 256) (F circomPrime)) (n : ℕ)
    (hb : ∀ (k : ℕ) (env env' : ProverEnvironment (F circomPrime)), n ≤ k →
      env.AgreesBelow k env' → eval env parentInput = eval env' parentInput →
      ∀ (j : ℕ) (hj : j < 256),
        Expression.eval env.toEnvironment (bits[j]'hj)
          = Expression.eval env'.toEnvironment (bits[j]'hj))
    (env env' : ProverEnvironment (F circomPrime)) :
    FormalCircuitBase.Operations.StructuralComputableWitnesses
      parentInput env env' n ((main bits).operations n) := by
  rw [main, Circuit.pure_structuralComputableWitnesses_iff]
  trivial

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

lemma foldl_bin (l : List ℕ) (a : ℕ) :
    l.foldl (fun acc b => 2 * acc + b) a
      = a * 2 ^ l.length + ∑ j ∈ Finset.range l.length, l[j]! * 2 ^ (l.length - 1 - j) := by
  induction l generalizing a with
  | nil => simp
  | cons hd tl ih =>
    rw [List.foldl_cons, ih (2 * a + hd), List.length_cons]
    simp only [Nat.add_sub_cancel]
    rw [Finset.sum_range_succ' (fun j => (hd :: tl)[j]! * 2 ^ (tl.length - j)) tl.length]
    simp only [List.getElem!_cons_succ, List.getElem!_cons_zero, Nat.sub_zero]
    rw [show (∑ j ∈ Finset.range tl.length, tl[j]! * 2 ^ (tl.length - 1 - j))
        = ∑ j ∈ Finset.range tl.length, tl[j]! * 2 ^ (tl.length - (j + 1)) from
      Finset.sum_congr rfl (fun j _ => by rw [Nat.sub_sub, Nat.add_comm])]
    rw [pow_succ]
    ring

lemma scalarOfBits_eq_sum (v : Vector ℕ 256) :
    Specs.ShortWeierstrass.scalarOfBits v
      = ∑ j ∈ Finset.range 256, v[j]! * 2 ^ (255 - j) := by
  have hfold : Specs.ShortWeierstrass.scalarOfBits v
      = v.toList.foldl (fun acc b => 2 * acc + b) 0 := by
    rw [Specs.ShortWeierstrass.scalarOfBits]
    rcases v with ⟨xs, hxs⟩
    simp [Vector.foldl_mk, Array.foldl_toList, Vector.toList]
  have hlen : v.toList.length = 256 := by simp
  rw [hfold, foldl_bin, hlen, Nat.zero_mul, Nat.zero_add]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  congr 1
  rw [getElem!_pos v.toList j (by rw [hlen]; exact hj),
    Vector.getElem_toList, getElem!_pos]

lemma sum_range_block9 (n : ℕ) (h : ℕ → ℕ) :
    (∑ j ∈ Finset.range (9 * n), h j)
      = ∑ i ∈ Finset.range n, ∑ t ∈ Finset.range 9, h (9 * i + t) := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [show 9 * (m + 1) = 9 * m + 9 from by ring, Finset.sum_range_add,
      Finset.sum_range_succ _ m, ih]

lemma scalarOfBits_grouped9 (v : Vector ℕ 256) :
    Specs.ShortWeierstrass.scalarOfBits v
      = (∑ i ∈ Finset.range 28,
          (∑ t ∈ Finset.range 9, v[255 - (9 * i + t)]! * 2 ^ t) * 2 ^ (9 * i))
        + (∑ t ∈ Finset.range 4, v[255 - (252 + t)]! * 2 ^ t) * 2 ^ (9 * 28) := by
  rw [scalarOfBits_eq_sum]
  have hreflect : (∑ j ∈ Finset.range 256, v[j]! * 2 ^ (255 - j))
      = ∑ j ∈ Finset.range 256, v[255 - j]! * 2 ^ j := by
    rw [← Finset.sum_range_reflect (fun j => v[255 - j]! * 2 ^ j) 256]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    congr 2
    omega
  have hsplit : (∑ j ∈ Finset.range 256, v[255 - j]! * 2 ^ j)
      = (∑ j ∈ Finset.range 252, v[255 - j]! * 2 ^ j)
        + ∑ t ∈ Finset.range 4, v[255 - (252 + t)]! * 2 ^ (252 + t) := by
    exact Finset.sum_range_add (fun j => v[255 - j]! * 2 ^ j) 252 4
  have hblock := sum_range_block9 28 (fun j => v[255 - j]! * 2 ^ j)
  rw [show 9 * 28 = 252 from rfl] at hblock
  have h1 : (∑ i ∈ Finset.range 28, ∑ t ∈ Finset.range 9, v[255 - (9 * i + t)]! * 2 ^ (9 * i + t))
      = ∑ i ∈ Finset.range 28,
          (∑ t ∈ Finset.range 9, v[255 - (9 * i + t)]! * 2 ^ t) * 2 ^ (9 * i) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [Finset.mem_range] at hi ht
    rw [pow_add, show 9 * i + t = t + 9 * i from by ring]
    ring
  have h2 : (∑ t ∈ Finset.range 4, v[255 - (252 + t)]! * 2 ^ (252 + t))
      = (∑ t ∈ Finset.range 4, v[255 - (252 + t)]! * 2 ^ t) * 2 ^ (9 * 28) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [Finset.mem_range] at ht
    rw [show (9 : ℕ) * 28 = 252 from rfl, pow_add]
    ring
  rw [hreflect, hsplit, hblock, h1, h2]



lemma IsBool.val_le_one {x : F circomPrime} (h : IsBool x) : x.val ≤ 1 := by
  rcases h with h | h <;> rw [h]
  · rw [ZMod.val_zero]; omega
  · rw [ZMod.val_one]



def gNat (x : fields 256 (F circomPrime)) (i : ℕ) : ℕ :=
  if h : i < 28 then
    (x[255 - 9 * i]'(by omega)).val
      + 2 * (x[254 - 9 * i]'(by omega)).val
      + 4 * (x[253 - 9 * i]'(by omega)).val
      + 8 * (x[252 - 9 * i]'(by omega)).val
      + 16 * (x[251 - 9 * i]'(by omega)).val
      + 32 * (x[250 - 9 * i]'(by omega)).val
      + 64 * (x[249 - 9 * i]'(by omega)).val
      + 128 * (x[248 - 9 * i]'(by omega)).val
      + 256 * (x[247 - 9 * i]'(by omega)).val
  else
    (x[3]'(by omega)).val
      + 2 * (x[2]'(by omega)).val
      + 4 * (x[1]'(by omega)).val
      + 8 * (x[0]'(by omega)).val


lemma gNat_eq_sum (x : fields 256 (F circomPrime)) (i : ℕ) (hi : i < 28) :
    gNat x i = ∑ t ∈ Finset.range 9, (Vector.map ZMod.val x)[255 - (9 * i + t)]! * 2 ^ t := by
  have hmap : ∀ j : ℕ, j < 256 → (hj : j < 256) →
      (Vector.map ZMod.val x)[j]! = (x[j]'hj).val := by
    intro j hj hj'
    rw [getElem!_pos _ j (by simpa using hj), Vector.getElem_map]
    rfl
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [show 255 - (9 * i + 0) = 255 - 9 * i from by omega,
    show 255 - (9 * i + 1) = 254 - 9 * i from by omega,
    show 255 - (9 * i + 2) = 253 - 9 * i from by omega,
    show 255 - (9 * i + 3) = 252 - 9 * i from by omega,
    show 255 - (9 * i + 4) = 251 - 9 * i from by omega,
    show 255 - (9 * i + 5) = 250 - 9 * i from by omega,
    show 255 - (9 * i + 6) = 249 - 9 * i from by omega,
    show 255 - (9 * i + 7) = 248 - 9 * i from by omega,
    show 255 - (9 * i + 8) = 247 - 9 * i from by omega,
    hmap (255 - 9 * i) (by omega) (by omega),
    hmap (254 - 9 * i) (by omega) (by omega),
    hmap (253 - 9 * i) (by omega) (by omega),
    hmap (252 - 9 * i) (by omega) (by omega),
    hmap (251 - 9 * i) (by omega) (by omega),
    hmap (250 - 9 * i) (by omega) (by omega),
    hmap (249 - 9 * i) (by omega) (by omega),
    hmap (248 - 9 * i) (by omega) (by omega),
    hmap (247 - 9 * i) (by omega) (by omega),
    gNat, dif_pos hi]
  ring

lemma gNat_eq_sum_top (x : fields 256 (F circomPrime)) :
    gNat x 28 = ∑ t ∈ Finset.range 4, (Vector.map ZMod.val x)[255 - (252 + t)]! * 2 ^ t := by
  have hmap : ∀ j : ℕ, j < 256 → (hj : j < 256) →
      (Vector.map ZMod.val x)[j]! = (x[j]'hj).val := by
    intro j hj hj'
    rw [getElem!_pos _ j (by simpa using hj), Vector.getElem_map]
    rfl
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [show 255 - (252 + 0) = 3 from by omega,
    show 255 - (252 + 1) = 2 from by omega,
    show 255 - (252 + 2) = 1 from by omega,
    show 255 - (252 + 3) = 0 from by omega,
    hmap 3 (by omega) (by omega), hmap 2 (by omega) (by omega),
    hmap 1 (by omega) (by omega), hmap 0 (by omega) (by omega),
    gNat, dif_neg (by omega : ¬ (28 : ℕ) < 28)]
  ring

lemma scalar_eq_gNat_sum (x : fields 256 (F circomPrime)) :
    Specs.ShortWeierstrass.scalarOfBits (Vector.map ZMod.val x)
      = ∑ i ∈ Finset.range 29, gNat x i * 2 ^ (9 * i) := by
  rw [scalarOfBits_grouped9,
    show (∑ i ∈ Finset.range 29, gNat x i * 2 ^ (9 * i))
      = (∑ i ∈ Finset.range 28, gNat x i * 2 ^ (9 * i)) + gNat x 28 * 2 ^ (9 * 28)
    from Finset.sum_range_succ _ 28]
  have h1 : (∑ i ∈ Finset.range 28,
        (∑ t ∈ Finset.range 9, (Vector.map ZMod.val x)[255 - (9 * i + t)]! * 2 ^ t)
          * 2 ^ (9 * i))
      = ∑ i ∈ Finset.range 28, gNat x i * 2 ^ (9 * i) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [gNat_eq_sum x i hi]
  rw [h1, gNat_eq_sum_top]



def boothCarry (x : fields 256 (F circomPrime)) (i : ℕ) : ℕ :=
  (x[255 - 9 * i]'(by omega)).val

/-- Evaluation of the affine recode output. -/
lemma eval_derivedDigits (env : Environment (F circomPrime))
    (input_var : Var (fields 256) (F circomPrime))
    (input : fields 256 (F circomPrime))
    (h_input : Vector.map (Expression.eval env) input_var = input)
    (c : ℕ) (hc : c < 256) :
    Expression.eval env ((derivedDigits input_var)[c]'hc) =
      if c < 255 then input[254 - c]'(by omega) else 1 := by
  rw [derivedDigits, Vector.getElem_ofFn]
  split
  · rw [← h_input, Vector.getElem_map]
  · rfl

/-- One ordinary 9-bit Booth window advances the complement carry. -/
lemma booth_step (out x : fields 256 (F circomPrime))
    (hx : ∀ c : Fin 256, IsBool x[c])
    (hout : ∀ c (hc : c < 256), out[c]'hc =
      if c < 255 then x[254 - c]'(by omega) else 1)
    (i : ℕ) (hi : i < 28) :
    digitVal out i = (gNat x i : ℤ) + (1 - (boothCarry x i : ℤ))
      - (1 - (boothCarry x (i + 1) : ℤ)) * 2 ^ 9 := by
  simp only [digitVal, windowVal, dif_pos hi, gNat, boothCarry]
  rw [hout (9 * i) (by omega), hout (9 * i + 1) (by omega),
    hout (9 * i + 2) (by omega), hout (9 * i + 3) (by omega),
    hout (9 * i + 4) (by omega), hout (9 * i + 5) (by omega),
    hout (9 * i + 6) (by omega), hout (9 * i + 7) (by omega),
    hout (9 * i + 8) (by omega)]
  simp only [if_pos (by omega : 9 * i < 255), if_pos (by omega : 9 * i + 1 < 255),
    if_pos (by omega : 9 * i + 2 < 255), if_pos (by omega : 9 * i + 3 < 255),
    if_pos (by omega : 9 * i + 4 < 255), if_pos (by omega : 9 * i + 5 < 255),
    if_pos (by omega : 9 * i + 6 < 255), if_pos (by omega : 9 * i + 7 < 255),
    if_pos (by omega : 9 * i + 8 < 255), if_pos hi]
  simp only [show 254 - (9 * i + 1) = 253 - 9 * i by omega,
    show 254 - (9 * i + 2) = 252 - 9 * i by omega,
    show 254 - (9 * i + 3) = 251 - 9 * i by omega,
    show 254 - (9 * i + 4) = 250 - 9 * i by omega,
    show 254 - (9 * i + 5) = 249 - 9 * i by omega,
    show 254 - (9 * i + 6) = 248 - 9 * i by omega,
    show 254 - (9 * i + 7) = 247 - 9 * i by omega,
    show 254 - (9 * i + 8) = 246 - 9 * i by omega,
    show 255 - 9 * (i + 1) = 246 - 9 * i by omega]
  push_cast
  ring

/-- The four-bit top window consumes the final carry. -/
lemma booth_top (out x : fields 256 (F circomPrime))
    (hx : ∀ c : Fin 256, IsBool x[c])
    (hout : ∀ c (hc : c < 256), out[c]'hc =
      if c < 255 then x[254 - c]'(by omega) else 1) :
    digitVal out 28 = (gNat x 28 : ℤ) + (1 - (boothCarry x 28 : ℤ)) := by
  simp only [digitVal, windowVal, dif_neg (by omega : ¬ (28 : ℕ) < 28), if_pos rfl,
    gNat, boothCarry]
  rw [hout 252 (by omega), hout 253 (by omega), hout 254 (by omega), hout 255 (by omega)]
  simp only [if_pos (by omega : 252 < 255), if_pos (by omega : 253 < 255),
    if_pos (by omega : 254 < 255), if_neg (by omega : ¬ 255 < 255), if_pos (by omega : 28 < 29),
    if_neg (by omega : ¬ 28 < 28)]
  push_cast
  have honeN : ZMod.val (1 : F circomPrime) = 1 := ZMod.val_one'
  rw [honeN]
  ring

/-- Explicit carry invariant after `n` ordinary Booth windows. -/
lemma booth_partial (out x : fields 256 (F circomPrime))
    (hx : ∀ c : Fin 256, IsBool x[c])
    (hout : ∀ c (hc : c < 256), out[c]'hc =
      if c < 255 then x[254 - c]'(by omega) else 1) :
    ∀ n ≤ 28,
    (∑ i ∈ Finset.range n, digitVal out i * 2 ^ (9 * i)) =
      (∑ i ∈ Finset.range n, (gNat x i : ℤ) * 2 ^ (9 * i))
        + 1 - boothCarry x 0
        - (1 - (boothCarry x n : ℤ)) * 2 ^ (9 * n) := by
  intro n hn
  induction n with
  | zero =>
      simp [boothCarry]
  | succ n ih =>
      have hn' : n ≤ 28 := by omega
      have hlt : n < 28 := by omega
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih hn', booth_step out x hx hout n hlt]
      rw [show (2 : ℤ) ^ (9 * (n + 1)) = 2 ^ (9 * n) * 2 ^ 9 by ring]
      ring

lemma cast_sum_pow (f : ℕ → ℕ) (n : ℕ) :
    ((∑ k ∈ Finset.range n, f k * 2 ^ (9 * k) : ℕ) : ℤ)
      = ∑ k ∈ Finset.range n, (f k : ℤ) * 2 ^ (9 * k) := by
  rw [Nat.cast_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  push_cast
  ring

lemma derived_digit_identity (out x : fields 256 (F circomPrime))
    (hx : ∀ c : Fin 256, IsBool x[c])
    (hout : ∀ c (hc : c < 256), out[c]'hc =
      if c < 255 then x[254 - c]'(by omega) else 1) :
    (∑ i ∈ Finset.range 29, digitVal out i * 2 ^ (9 * i)) =
      (Specs.ShortWeierstrass.scalarOfBits (Vector.map ZMod.val x) : ℤ)
        + 1 - (x[255]'(by omega)).val := by
  rw [scalar_eq_gNat_sum x, cast_sum_pow (gNat x) 29]
  rw [show (∑ i ∈ Finset.range 29, digitVal out i * 2 ^ (9 * i)) =
      (∑ i ∈ Finset.range 28, digitVal out i * 2 ^ (9 * i)) +
        digitVal out 28 * 2 ^ (9 * 28) by rw [Finset.sum_range_succ]]
  rw [show (∑ i ∈ Finset.range 29, (gNat x i : ℤ) * 2 ^ (9 * i)) =
      (∑ i ∈ Finset.range 28, (gNat x i : ℤ) * 2 ^ (9 * i)) +
        (gNat x 28 : ℤ) * 2 ^ (9 * 28) by rw [Finset.sum_range_succ]]
  rw [booth_partial out x hx hout 28 (by omega), booth_top out x hx hout]
  simp only [boothCarry]
  ring

theorem soundness : Soundness (F circomPrime) main Assumptions Spec := by
  intro i₀ env input_var input h_input h_assumptions h_holds
  have h_input' : Vector.map (Expression.eval env) input_var = input := by
    rw [← CircuitType.eval_var_fields]
    exact h_input
  let out := Vector.map (Expression.eval env) (derivedDigits input_var)
  have hevalout : eval env (ElaboratedCircuit.output main input_var i₀) = out := by
    rw [CircuitType.eval_var_fields]
    rfl
  have hout : ∀ c (hc : c < 256), out[c]'hc =
      if c < 255 then input[254 - c]'(by omega) else 1 := by
    intro c hc
    simp only [out, Vector.getElem_map]
    exact eval_derivedDigits env input_var input h_input' c hc
  rw [hevalout]
  refine ⟨⟨?_, derived_digit_identity out input h_assumptions hout⟩, ?_⟩
  · intro c
    rw [Fin.getElem_fin]
    rw [hout c.val c.isLt]
    split
    · exact h_assumptions ⟨254 - c.val, by omega⟩
    · exact Or.inr rfl
  · rw [main, Circuit.pure_operations_eq]
    trivial

theorem completeness : Completeness (F circomPrime) main Assumptions := by
  intro n env input_var h_local input h_input h_assumptions
  rw [main, Circuit.pure_operations_eq]
  trivial

end Recode
end Solution.Secp256k1ScalarMulFixedBase



set_option maxRecDepth 2048
set_option maxHeartbeats 2000000




namespace Solution.Secp256k1ScalarMulFixedBase.Width12.RecodeCircuitBridge

def windowVal (out : fields 256 (F circomPrime)) (i : ℕ) : ℕ :=
  if h : i < 21 then
    (out[12 * i]'(by omega)).val + 2 * (out[12 * i + 1]'(by omega)).val
      + 4 * (out[12 * i + 2]'(by omega)).val
      + 8 * (out[12 * i + 3]'(by omega)).val
      + 16 * (out[12 * i + 4]'(by omega)).val
      + 32 * (out[12 * i + 5]'(by omega)).val
      + 64 * (out[12 * i + 6]'(by omega)).val
      + 128 * (out[12 * i + 7]'(by omega)).val
      + 256 * (out[12 * i + 8]'(by omega)).val
      + 512 * (out[12 * i + 9]'(by omega)).val
      + 1024 * (out[12 * i + 10]'(by omega)).val
      + 2048 * (out[12 * i + 11]'(by omega)).val
  else if i = 21 then
    (out[252]'(by omega)).val + 2 * (out[253]'(by omega)).val
      + 4 * (out[254]'(by omega)).val + 8 * (out[255]'(by omega)).val
  else 0

def digitVal (out : fields 256 (F circomPrime)) (i : ℕ) : ℤ :=
  2 * (windowVal out i : ℤ) + 1 - (if i < 21 then 4096 else 16)

lemma regular_window_eq (out : fields 256 (F circomPrime)) (i : ℕ) (hi : i < 21) :
    windowVal out i = Select12.bitsVal
      (Vector.ofFn fun t : Fin 12 => out[12 * i + t.val]'(by omega)) := by
  rw [windowVal, dif_pos hi, Select12.bitsVal]
  rfl

lemma top_window_eq (out : fields 256 (F circomPrime)) :
    windowVal out 21 = SelectTop.bitsVal
      (Vector.ofFn fun t : Fin 4 => out[252 + t.val]'(by omega)) := by
  rw [windowVal, dif_neg (by omega : ¬ (21 : ℕ) < 21), if_pos rfl,
    SelectTop.bitsVal]
  rfl

set_option maxHeartbeats 6400000 in
set_option maxRecDepth 16384 in
/-- The width-12 and width-9 Booth layouts are finite regroupings of the same
256 little-endian recode witness. -/
theorem digit_sum_eq_recode (out : fields 256 (F circomPrime)) :
    (∑ i ∈ Finset.range 22, digitVal out i * 2 ^ (12 * i)) =
      ∑ i ∈ Finset.range 29, Recode.digitVal out i * 2 ^ (9 * i) := by
  simp only [digitVal, windowVal, Recode.digitVal, Recode.windowVal]
  norm_num [Finset.sum_range_succ]
  push_cast
  ring

end Solution.Secp256k1ScalarMulFixedBase.Width12.RecodeCircuitBridge

end DonorFile6_3

-- Adapted donor module: CandidateRadix
section DonorFile6_4

namespace Solution.Secp256k1ScalarMulFixedBase.CandidateRadix
open Specs.ShortWeierstrass Specs.Secp256k1

set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

def bit (db : fields 256 (F circomPrime)) (i : ℕ) : ℕ :=
  if h : i < 256 then (db[i]'h).val else 0

def low (db : fields 256 (F circomPrime)) (e : ℕ) : ℕ :=
  ∑ i ∈ Finset.range e, bit db i * 2 ^ i

def window (db : fields 256 (F circomPrime)) (e w : ℕ) : ℕ :=
  ∑ i ∈ Finset.range w, bit db (e+i) * 2 ^ i

def signed (db : fields 256 (F circomPrime)) (e : ℕ) : ℤ :=
  2 * (low db e : ℤ) + 1 - 2 ^ e

def digit (db : fields 256 (F circomPrime)) (e w : ℕ) : ℤ :=
  2 * (window db e w : ℤ) + 1 - 2 ^ w

theorem low_add (db : fields 256 (F circomPrime)) (e w : ℕ) :
    low db (e+w) = low db e + window db e w * 2 ^ e := by
  rw [low, Finset.sum_range_add]
  congr 1
  rw [window, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [pow_add]
  ring

theorem signed_add (db : fields 256 (F circomPrime)) (e w : ℕ) :
    signed db (e+w) = signed db e + digit db e w * 2 ^ e := by
  simp only [signed, digit, low_add, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [pow_add]
  ring

theorem bit_le (db : fields 256 (F circomPrime))
    (hb : ∀ i : Fin 256, IsBool db[i]) (i : ℕ) : bit db i ≤ 1 := by
  unfold bit
  split
  · exact Select.IsBool.val_le_one (hb ⟨i,by omega⟩)
  · omega

theorem low_lt (db : fields 256 (F circomPrime))
    (hb : ∀ i : Fin 256, IsBool db[i]) (e : ℕ) : low db e < 2 ^ e := by
  induction e with
  | zero => simp [low]
  | succ e ih =>
    have h := Nat.mul_le_mul_right (2 ^ e) (bit_le db hb e)
    rw [low, Finset.sum_range_succ, pow_succ]
    change low db e + bit db e * 2 ^ e < 2 ^ e * 2
    omega

theorem signed_odd (db : fields 256 (F circomPrime)) (e : ℕ) (he : 0 < e) :
    Odd (signed db e) := by
  obtain ⟨e,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : e ≠ 0)
  refine ⟨(low db (e+1) : ℤ) - 2 ^ e, ?_⟩
  rw [signed, pow_succ]
  ring

theorem signed_bound (db : fields 256 (F circomPrime))
    (hb : ∀ i : Fin 256, IsBool db[i]) (e : ℕ) : |signed db e| < 2 ^ e := by
  have h : (low db e : ℤ) < 2 ^ e := by exact_mod_cast low_lt db hb e
  have hz : 0 ≤ (low db e : ℤ) := by positivity
  rw [signed, abs_lt]
  constructor <;> omega

theorem window12 (db : fields 256 (F circomPrime)) (e : ℕ) (he : e+12 ≤ 256) :
    window db e 12 = Select12.bitsVal (Vector.ofFn fun i : Fin 12 => db[e+i.val]'(by omega)) := by
  simp (disch := omega) only [window, bit, dif_pos, Select12.bitsVal,
    Finset.sum_range_succ, Finset.sum_range_zero, Vector.getElem_ofFn]
  norm_num
  omega

theorem window13 (db : fields 256 (F circomPrime)) (e : ℕ) (he : e+13 ≤ 256) :
    window db e 13 = Select13.bitsVal (Vector.ofFn fun i : Fin 13 => db[e+i.val]'(by omega)) := by
  simp (disch := omega) only [window, bit, dif_pos, Select13.bitsVal,
    Finset.sum_range_succ, Finset.sum_range_zero, Vector.getElem_ofFn]
  norm_num
  omega

theorem recode_regular (db : fields 256 (F circomPrime)) (i : ℕ) (hi : i < 28) :
    Recode.digitVal db i = digit db (9*i) 9 := by
  simp (disch := omega) only [Recode.digitVal, Recode.windowVal, digit, window,
    bit, dif_pos, if_pos hi, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  push_cast
  omega

theorem recode_top (db : fields 256 (F circomPrime)) :
    Recode.digitVal db 28 = digit db 252 4 := by
  simp [Recode.digitVal, Recode.windowVal, digit, window, bit, Finset.sum_range_succ]
  <;> push_cast <;> ring

theorem recode_prefix (db : fields 256 (F circomPrime)) (n : ℕ) (hn : n ≤ 28) :
    (∑ i ∈ Finset.range n, Recode.digitVal db i * 2 ^ (9*i)) = signed db (9*n) := by
  induction n with
  | zero => simp [signed,low]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih (by omega), recode_regular db n (by omega)]
    rw [show 9 * (n+1) = 9*n+9 from by omega, signed_add]

theorem recode_total (db : fields 256 (F circomPrime)) :
    (∑ i ∈ Finset.range 29, Recode.digitVal db i * 2 ^ (9*i)) = signed db 256 := by
  rw [show 29 = 28+1 from rfl, Finset.sum_range_succ, recode_prefix db 28 (by omega), recode_top]
  exact (signed_add db 252 4).symm

theorem recode_scalar (bits db : fields 256 (F circomPrime)) (hr : Recode.Spec bits db) :
    signed db 256 = (scalarOfBits (bits.map ZMod.val) : ℤ) + 1 - bits[255].val := by
  rw [← recode_total]
  exact hr.2

end Solution.Secp256k1ScalarMulFixedBase.CandidateRadix

end DonorFile6_4

-- Adapted donor module: CandidateSemantics
section DonorFile6_5

namespace Solution.Secp256k1ScalarMulFixedBase.CandidateSemantics
open Specs.ShortWeierstrass Specs.Secp256k1
open Solution.Secp256k1ScalarMulFixedBase.CandidateRadix

set_option maxHeartbeats 6400000
set_option maxRecDepth 8192

def slice {α : Type} (db : Vector α 256) (e w : ℕ) (he : e+w ≤ 256) : Vector α w :=
  Vector.ofFn fun i : Fin w => db[e+i.val]'(by omega)

theorem slice_bool (db : fields 256 (F circomPrime))
    (hb : ∀ i : Fin 256, IsBool db[i]) (e w : ℕ) (he : e+w ≤ 256) :
    ∀ i : Fin w, IsBool (slice db e w he)[i] := by
  intro i
  simpa only [slice,Fin.getElem_fin,Vector.getElem_ofFn] using hb ⟨e+i.val,by omega⟩

theorem digit12_eq (db : fields 256 (F circomPrime)) (e : ℕ) (he : e+12 ≤ 256) :
    digit db e 12 = 2 * (Select12.bitsVal (slice db e 12 he) : ℤ) + 1 - 4096 := by
  rw [digit,window12 db e he]
  rfl

theorem digit13_eq (db : fields 256 (F circomPrime)) (e : ℕ) (he : e+13 ≤ 256) :
    digit db e 13 = 2 * (Select13.bitsVal (slice db e 13 he) : ℤ) + 1 - 8192 := by
  rw [digit,window13 db e he]
  rfl

theorem signed_zero (db : fields 256 (F circomPrime)) : signed db 0 = 0 := by
  simp [signed,low]

theorem first_digit (db : fields 256 (F circomPrime)) (w : ℕ) :
    digit db 0 w = signed db w := by
  simpa only [Nat.zero_add,signed_zero,pow_zero,mul_one,zero_add] using
    (signed_add db 0 w).symm

end Solution.Secp256k1ScalarMulFixedBase.CandidateSemantics

end DonorFile6_5

-- Adapted donor module: CompactAddCost
section DonorFile6_6

namespace Solution.Secp256k1ScalarMulFixedBase
namespace CompactAdd

open Challenge.CostR1CS
open Cost

theorem costIs_linFlexG (input : Var (EqViaCarriesFlex.Inputs 5) (F circomPrime)) :
    CostIs (assertion (GroupedFlex.circuit 64 gfLin posOfLin 3 vLin vLin hgvLin (by norm_num))
      input) ⟨3, 5⟩ :=
  Cost.costIs_assertion_groupedEqXV 64 gfLin posOfLin 3 vLin vLin hgvLin (by norm_num) input

end CompactAdd
end Solution.Secp256k1ScalarMulFixedBase

end DonorFile6_6

-- Adapted donor module: CanonicalizeCost
section DonorFile6_7

namespace Solution.Secp256k1ScalarMulFixedBase
namespace Canonicalize

open Challenge.CostR1CS
open Cost
open CompactAdd (cExp degree_cExp affine_cExp costIs_linFlexG)

attribute [local irreducible] isR1CSRow r1csProducts operationsIsR1CS flatOperationsIsR1CS

private theorem costIs_toBitsAffine (w : ℕ) (x : Expression (F circomPrime)) :
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

private theorem isR1CS_toBitsAffine (w : ℕ) (x : Expression (F circomPrime)) (hx : Affine x) :
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

private theorem costIs_toBitsAffine_sub (w : ℕ) (hn : (2 : ℕ) ^ (w + 1) < circomPrime)
    (x : Expression (F circomPrime)) :
    CostIs (ToBitsAffine.toBitsAffine w hn x) ⟨w, w + 1⟩ :=
  CostIs.subcircuitWithAssertion (fun m => costIs_toBitsAffine w x m)

private theorem isR1CS_toBitsAffine_sub (w : ℕ) (hn : (2 : ℕ) ^ (w + 1) < circomPrime)
    (x : Expression (F circomPrime)) (hx : Affine x) :
    IsR1CSCirc (ToBitsAffine.toBitsAffine w hn x) :=
  IsR1CSCirc.subcircuitWithAssertion (fun m => isR1CS_toBitsAffine w x hx m)

private theorem costIs_isZeroField (x : Expression (F circomPrime)) :
    CostIs (Gadgets.IsZeroField.main x) ⟨2, 2⟩ := by
  rw [show (⟨2, 2⟩ : Count) = ⟨1, 0⟩ + (⟨1, 1⟩ + (⟨0, 1⟩ + Count.zero)) from by decide]
  unfold Gadgets.IsZeroField.main
  refine CostIs.bind (CostIs.witnessField (F := F circomPrime) _) fun _ => ?_
  refine CostIs.bind (costIs_assignEqField _) fun _ => ?_
  exact CostIs.bind (costIs_assertEqField _ _) fun _ => CostIs.pure _

private theorem isR1CS_isZeroField (x : Expression (F circomPrime)) (hx : Affine x) :
    IsR1CSCirc (Gadgets.IsZeroField.main x) := by
  unfold Gadgets.IsZeroField.main
  refine IsR1CSCirc.bind_out (IsR1CSCirc.witnessField _) fun nxInv => ?_
  refine IsR1CSCirc.bind_out (isR1CS_assignEqField _ fun w =>
    CompactAdd.isR1CSRow_sub_sub_mul (Affine.var w) (Affine.const 1) hx (Affine.var _)) fun nisZero => ?_
  refine IsR1CSCirc.bind (isR1CS_assertEqField
    (isR1CSRow_mul_sub (affine_assignEq_output _ nisZero) hx Affine.zero)) fun _ =>
      IsR1CSCirc.pure _

private theorem costIs_sub_isZeroField (x : Expression (F circomPrime)) :
    CostIs (subcircuit Gadgets.IsZeroField.circuit x) ⟨2, 2⟩ :=
  CostIs.subcircuit (fun n => costIs_isZeroField x n)

private theorem isR1CS_sub_isZeroField (x : Expression (F circomPrime)) (hx : Affine x) :
    IsR1CSCirc (subcircuit Gadgets.IsZeroField.circuit x) :=
  IsR1CSCirc.subcircuit (fun n => isR1CS_isZeroField x hx n)

private theorem affine_sub_isZeroField (x : Expression (F circomPrime)) (n : ℕ) :
    Affine ((subcircuit Gadgets.IsZeroField.circuit x).output n) := by
  simp only [circuit_norm, subcircuit, Gadgets.IsZeroField.circuit,
    Gadgets.IsZeroField.elaborated]
  exact Affine.var _

private theorem affineW_push_top {w : ℕ} (base : ℕ) (top : Expression (F circomPrime))
    (htop : Affine top) :
    AffineW ((Vector.mapRange w fun i => Expression.var { index := base + i }).push top) := by
  intro i hi
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
  · rw [Vector.getElem_push_lt hlt, Vector.getElem_mapRange]; exact Affine.var _
  · rw [Vector.getElem_push_eq]; exact htop

private theorem costIs_validP (x : Var Emu (F circomPrime)) :
    CostIs (ValidP.main x) (⟨256, 260⟩ : Count) := by
  rw [show (⟨256, 260⟩ : Count) =
      ⟨63, 64⟩ + (⟨63, 64⟩ + (⟨63, 64⟩ + (⟨63, 64⟩ +
      (⟨1, 0⟩ + (⟨0, 1⟩ + (⟨1, 0⟩ + (⟨0, 1⟩ +
      (⟨1, 0⟩ + (⟨0, 1⟩ + (⟨1, 0⟩ + (⟨0, 1⟩ + Count.zero)))))))))))
      from by decide]
  unfold ValidP.main ValidP.tail
  refine CostIs.bind (costIs_toBitsAffine_sub 63 secpParams.hB _) fun b0 => ?_
  refine CostIs.bind (costIs_toBitsAffine_sub 63 secpParams.hB _) fun b1 => ?_
  refine CostIs.bind (costIs_toBitsAffine_sub 63 secpParams.hB _) fun b2 => ?_
  refine CostIs.bind (costIs_toBitsAffine_sub 63 secpParams.hB _) fun b3 => ?_
  refine CostIs.bind (CostIs.witnessField (F := F circomPrime) _) fun u1 => ?_
  refine CostIs.bind (CostIs.assertZero _) fun _ => ?_
  refine CostIs.bind (CostIs.witnessField (F := F circomPrime) _) fun u2 => ?_
  refine CostIs.bind (CostIs.assertZero _) fun _ => ?_
  refine CostIs.bind (CostIs.witnessField (F := F circomPrime) _) fun u3 => ?_
  refine CostIs.bind (CostIs.assertZero _) fun _ => ?_
  refine CostIs.bind (CostIs.witnessField (F := F circomPrime) _) fun u4 => ?_
  exact CostIs.bind (CostIs.assertZero _) fun _ => CostIs.pure _

theorem costIs_validPBytes (x : Var Emu (F circomPrime)) :
    CostIs (ValidPBytes.main x) ⟨256, 260⟩ := by
  simpa only [ValidPBytes.main, ValidP.main, Circuit.operations] using
    costIs_validP x

theorem costIs_sub_validPBytes (x : Var Emu (F circomPrime)) :
    CostIs (ValidPBytes.circuit x) ⟨256, 260⟩ :=
  CostIs.subcircuitWithAssertion (fun n => costIs_validPBytes x n)

private theorem affine_deficitSlice {n : ℕ} (bits : Var (fields n) (F circomPrime))
    (hbits : AffineW bits) (start len : ℕ) (h : start + len ≤ n) :
    Affine (ValidP.deficitSlice bits start len h) := by
  unfold ValidP.deficitSlice
  apply affine_finFoldl'
  · exact Affine.zero
  · intro acc i hacc
    exact Affine.add hacc
      (Affine.sub (Affine.const 1) (hbits (start + i.val) (by omega)))

private theorem isR1CS_validPTail (b0 b1 b2 b3 : Var (fields limbBits) (F circomPrime))
    (hb0 : AffineW b0) (hb1 : AffineW b1) (hb2 : AffineW b2) (hb3 : AffineW b3) :
    IsR1CSCirc (ValidP.tail b0 b1 b2 b3) := by
  unfold ValidP.tail
  have htopDef : Affine (ValidP.deficitSlice b0 33 31 (by decide) +
      ValidP.deficitSlice b1 0 64 (by decide) +
      ValidP.deficitSlice b2 0 64 (by decide) +
      ValidP.deficitSlice b3 0 64 (by decide)) :=
    Affine.add (Affine.add (Affine.add
      (affine_deficitSlice _ hb0 33 31 (by decide))
      (affine_deficitSlice _ hb1 0 64 (by decide)))
      (affine_deficitSlice _ hb2 0 64 (by decide)))
      (affine_deficitSlice _ hb3 0 64 (by decide))
  have hsDef := Affine.add htopDef (affine_deficitSlice b0 hb0 10 22 (by decide))
  have htDef := Affine.add hsDef (Affine.sub (Affine.const 1) (hb0 5 (by decide)))
  have huDef := Affine.add htDef (affine_deficitSlice b0 hb0 0 4 (by decide))
  refine IsR1CSCirc.bind_out (IsR1CSCirc.witnessField _) fun u1 => ?_
  refine IsR1CSCirc.bind (IsR1CSCirc.assertZero
    (isR1CSRow_sub_mul (hb0 32 (by decide)) htopDef (Affine.var _))) fun _ => ?_
  refine IsR1CSCirc.bind_out (IsR1CSCirc.witnessField _) fun u2 => ?_
  refine IsR1CSCirc.bind (IsR1CSCirc.assertZero
    (isR1CSRow_sub_mul (Affine.add (Affine.add (Affine.add
        (hb0 9 (by decide)) (hb0 8 (by decide))) (hb0 7 (by decide))) (hb0 6 (by decide)))
      hsDef (Affine.var _))) fun _ => ?_
  refine IsR1CSCirc.bind_out (IsR1CSCirc.witnessField _) fun u3 => ?_
  refine IsR1CSCirc.bind (IsR1CSCirc.assertZero
    (isR1CSRow_sub_mul (hb0 4 (by decide)) htDef (Affine.var _))) fun _ => ?_
  refine IsR1CSCirc.bind_out (IsR1CSCirc.witnessField _) fun u4 => ?_
  exact IsR1CSCirc.bind (IsR1CSCirc.assertZero
    (isR1CSRow_mul_sub huDef (Affine.var _) (Affine.const 1))) fun _ => IsR1CSCirc.pure _

private theorem isR1CS_validP (x : Var Emu (F circomPrime)) (hx : AffineW x) :
    IsR1CSCirc (ValidP.main x) := by
  unfold ValidP.main
  refine IsR1CSCirc.bind_out
    (isR1CS_toBitsAffine_sub 63 secpParams.hB _ (hx 0 (by decide))) fun n0 => ?_
  refine IsR1CSCirc.bind_out
    (isR1CS_toBitsAffine_sub 63 secpParams.hB _ (hx 1 (by decide))) fun n1 => ?_
  refine IsR1CSCirc.bind_out
    (isR1CS_toBitsAffine_sub 63 secpParams.hB _ (hx 2 (by decide))) fun n2 => ?_
  refine IsR1CSCirc.bind_out
    (isR1CS_toBitsAffine_sub 63 secpParams.hB _ (hx 3 (by decide))) fun n3 => ?_
  exact isR1CS_validPTail _ _ _ _
    (affineW_push_top _ _ (Affine.fconst_mul _
      (Affine.sub (hx 0 (by decide)) (affine_fieldFromBitsExpr _ (affineW_mapRange_var _)))))
    (affineW_push_top _ _ (Affine.fconst_mul _
      (Affine.sub (hx 1 (by decide)) (affine_fieldFromBitsExpr _ (affineW_mapRange_var _)))))
    (affineW_push_top _ _ (Affine.fconst_mul _
      (Affine.sub (hx 2 (by decide)) (affine_fieldFromBitsExpr _ (affineW_mapRange_var _)))))
    (affineW_push_top _ _ (Affine.fconst_mul _
      (Affine.sub (hx 3 (by decide)) (affine_fieldFromBitsExpr _ (affineW_mapRange_var _)))))

theorem isR1CS_validPBytes (x : Var Emu (F circomPrime)) (hx : AffineW x) :
    IsR1CSCirc (ValidPBytes.main x) := by
  simpa only [ValidPBytes.main, ValidP.main, Circuit.operations] using
    isR1CS_validP x hx

theorem isR1CS_sub_validPBytes (x : Var Emu (F circomPrime))
    (hx : AffineW x) :
    IsR1CSCirc (ValidPBytes.circuit x) :=
  IsR1CSCirc.subcircuitWithAssertion (fun n => isR1CS_validPBytes x hx n)

private theorem affine_byteFromBits
    (b0 b1 b2 b3 : Var (fields limbBits) (F circomPrime))
    (hb0 : AffineW b0) (hb1 : AffineW b1)
    (hb2 : AffineW b2) (hb3 : AffineW b3)
    (t : Fin coordBytes) :
    Affine (ValidPBytes.byteFromBits b0 b1 b2 b3 t) := by
  unfold ValidPBytes.byteFromBits
  refine affine_finFoldl' _ _ Affine.zero fun acc j hacc => ?_
  apply Affine.add hacc
  apply Affine.mul_deg0
  · split_ifs
    · apply hb0
    · apply hb1
    · apply hb2
    · apply hb3
  · exact degree_const _

theorem affineW_validPBytes_output
    (x : Var Emu (F circomPrime)) (hx : AffineW x) (n : ℕ) :
    AffineW (ValidPBytes.circuit.output x n) := by
  simp only [ValidPBytes.circuit, circuit_norm, ValidPBytes.elaborated]
  intro i hi
  rw [Vector.getElem_ofFn]
  apply affine_byteFromBits
  · exact affineW_push_top _ _
      (Affine.fconst_mul _
        (Affine.sub (hx 0 (by decide))
          (affine_fieldFromBitsExpr _ (affineW_mapRange_var _))))
  · exact affineW_push_top _ _
      (Affine.fconst_mul _
        (Affine.sub (hx 1 (by decide))
          (affine_fieldFromBitsExpr _ (affineW_mapRange_var _))))
  · exact affineW_push_top _ _
      (Affine.fconst_mul _
        (Affine.sub (hx 2 (by decide))
          (affine_fieldFromBitsExpr _ (affineW_mapRange_var _))))
  · exact affineW_push_top _ _
      (Affine.fconst_mul _
        (Affine.sub (hx 3 (by decide))
          (affine_fieldFromBitsExpr _ (affineW_mapRange_var _))))

private theorem affine_emuPoly {a : Var Emu (F circomPrime)} (ha : AffineW a) :
    Affine (emuPoly a) :=
  Affine.add (Affine.add (Affine.add (ha 0 (by decide))
    (Affine.fconst_mul _ (ha 1 (by decide))))
    (Affine.fconst_mul _ (ha 2 (by decide))))
    (Affine.fconst_mul _ (ha 3 (by decide)))

private theorem affine_bExpr {x r : Var Emu (F circomPrime)}
    (hx : AffineW x) (hr : AffineW r) : Affine (bExpr x r) :=
  Affine.fconst_mul _ (Affine.sub (affine_emuPoly hx) (affine_emuPoly hr))

def canonicalizeCost : Count := ⟨260, 262⟩

theorem costIs_main (x : Var Emu (F circomPrime)) :
    CostIs (main x) canonicalizeCost := by
  rw [show canonicalizeCost =
    ⟨4, 0⟩ + (⟨0, 1⟩ + (⟨256, 260⟩ +
        (⟨GroupedFlex.widthAllocFrom vCanonicalL.Wf (3 - 2) 0,
          GroupedFlex.widthConsFrom vCanonicalL.Wf (3 - 2) 0⟩ + Count.zero))) from by decide]
  unfold main
  refine CostIs.bind (CostIs.provableWitness _) fun r => ?_
  refine CostIs.bind (CostIs.assertZero _) fun _ => ?_
  refine CostIs.bind (costIs_sub_validPBytes _) fun validBytes => ?_
  refine CostIs.bind
    (Cost.costIs_assertion_groupedNoTop 64 gfLin posOfLin 3
      vCanonicalL vCanonicalR hgvCanonical (by norm_num) _) fun _ => ?_
  exact CostIs.pure _

theorem isR1CS_main (x : Var Emu (F circomPrime)) (hx : AffineW x) :
    IsR1CSCirc (main x) := by
  unfold main
  refine IsR1CSCirc.bind_out (IsR1CSCirc.provableWitness _) fun nr => ?_
  let r : Var Emu (F circomPrime) :=
    (ProvableType.witness (α := Emu) fun env => emuOfNat (evalEmu env x % P256)).output nr
  have hr : AffineW r := (affineProvable_provableWitness _ nr).affineW
  have hb : Affine (bExpr x r) := affine_bExpr hx hr
  refine IsR1CSCirc.bind (IsR1CSCirc.assertZero (isR1CSRow_mul hb
    (Affine.sub hb (Affine.const 1)))) fun _ => ?_
  refine IsR1CSCirc.bind_out (isR1CS_sub_validPBytes r hr) fun nv => ?_
  refine IsR1CSCirc.bind
    (Cost.isR1CS_assertion_groupedNoTop 64 gfLin posOfLin 3
      vCanonicalL vCanonicalR hgvCanonical (by norm_num) _ ?_ ?_) fun _ =>
      IsR1CSCirc.pure _
  ·
    intro k hk
    rw [Vector.getElem_mapFinRange]
    split
    · refine Affine.add (hr _ (by assumption))
        (Affine.mul_deg0 hb (degree_cExp _ _))
    · exact Affine.zero
  ·
    intro k hk
    rw [Vector.getElem_mapFinRange]
    split
    · exact hx _ (by assumption)
    · exact Affine.zero

theorem affineW_output (x : Var Emu (F circomPrime)) (n : ℕ) :
    AffineW ((main x).output n) := by
  rw [elaborated.output_eq]
  simp only [circuit_norm]
  intro i hi
  rw [Vector.getElem_ofFn]
  apply affine_byteFromBits <;>
    exact affineW_push_top _ _
      (Affine.fconst_mul _
        (Affine.sub (Affine.var _)
          (affine_fieldFromBitsExpr _ (affineW_mapRange_var _))))

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

open PairAdd (dtilOf x2W x2Quot y32W y32Quot stageA stageO2 stageC1)
open CompactAdd (cExp qpCoeff c976 cK)

/-- Fold state: accumulator x, last chord slope, last table point. -/
structure ChainState (F : Type) where
  x : Emu F
  lam : Emu F
  T : Select.AffPoint F
deriving ProvableStruct

/-- Output of one chain-extension step. -/
structure ChainXL (F : Type) where
  x : Emu F
  lam : Emu F
deriving ProvableStruct

structure StartInputs (F : Type) where
  A : Select.AffPoint F
  T : Select.AffPoint F
deriving ProvableStruct

structure ExtInputs (F : Type) where
  x : Emu F
  lam : Emu F
  TP : Select.AffPoint F
  T : Select.AffPoint F
deriving ProvableStruct

/-- x-half of the old `PairAdd.stageC2`: witnesses `x' = lam² − xPrev − xT (mod p)`
with its quotient, and certifies via `gfQuad`. -/
def stageX (xPrev xT lam2 : Var Emu (F circomPrime)) :
    Circuit (F circomPrime) (Var Emu (F circomPrime)) := do
  let x2 ← ProvableType.witness (α := Emu) fun env =>
    emuOfNat (x2W env xPrev xT lam2)
  NormalizeImplicit.circuit secpParams x2
  let q6 ← ProvableType.witness (α := Emu) fun env =>
    emuOfNat (x2Quot env xPrev xT lam2 % 2 ^ 256)
  let q6t ← ProvableType.witness (α := field) fun env =>
    ((x2Quot env xPrev xT lam2 / 2 ^ 256 : ℕ) : F circomPrime)
  NormalizeImplicit.circuit secpParams q6
  assertion (RangeCheck.circuit 1 (by decide) (by decide)) q6t
  let convLL ← MulMod.interpolatedMul lam2 lam2
  GroupedFlex.circuit 64 gfQuad posOfQuad 5 vQuad vQuad hgvQuad (by norm_num) {
    lhs := Vector.mapFinRange 9 fun k =>
      (if h : k.val < 7 then convLL[k.val] else 0)
        + (if k.val < 5 then cExp (4 * P256) k.val else 0)
    rhs := Vector.mapFinRange 9 fun k =>
      qpCoeff q6 q6t k.val
        + (if h : k.val < 4 then x2[k.val] + xPrev[k.val] + xT[k.val] else 0) }
  return x2

/-- y-half of the old `PairAdd.stageC2`: witnesses
`y = lam·(xT − x) − yT (mod p)` and certifies via `gfWide`. -/
def stageY (x xT yT lam : Var Emu (F circomPrime)) :
    Circuit (F circomPrime) (Var Emu (F circomPrime)) := do
  let xd2 : Var Emu (F circomPrime) :=
    Vector.ofFn fun i : Fin 4 =>
      xT[i.val]'i.isLt
        + (((2 ^ 64 - 1 : ℕ) : F circomPrime) : Expression (F circomPrime))
        - x[i.val]'i.isLt
  let y3 ← ProvableType.witness (α := Emu) fun env =>
    emuOfNat (y32W env xT yT lam x)
  NormalizeImplicit.circuit secpParams y3
  let q7 ← ProvableType.witness (α := Emu) fun env =>
    emuOfNat (y32Quot env xT yT lam x % 2 ^ 256)
  let q7t ← ProvableType.witness (α := field) fun env =>
    ((y32Quot env xT yT lam x / 2 ^ 256 : ℕ) : F circomPrime)
  NormalizeImplicit.circuit secpParams q7
  assertion (RangeCheck.circuit 2 (by decide) (by decide)) q7t
  let convLX2 ← MulMod.interpolatedMul lam xd2
  GroupedFlex.circuit 64 gfWide posOfWide 6 vWide vWide hgvWide (by norm_num) {
    lhs := Vector.mapFinRange 10 fun k =>
      (if h : k.val < 7 then convLX2[k.val] else 0)
        + (if k.val < 5 then cExp (2 ^ 35 * P256) k.val else 0)
    rhs := Vector.mapFinRange 10 fun k =>
      qpCoeff q7 q7t k.val
        + (if h : k.val < 4 then
            y3[k.val] + yT[k.val]
              + ((c976 : ℕ) : F circomPrime) * (lam[k.val]'h) else 0) }
  return y3

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

lemma stageX_localLength (xPrev xT lam2 : Var Emu (F circomPrime)) (n : ℕ) :
    Operations.localLength (stageX xPrev xT lam2 n).2 = 721 := by chain_simp

lemma stageX_output (xPrev xT lam2 : Var Emu (F circomPrime)) (n : ℕ) :
    (stageX xPrev xT lam2 n).1 = varFromOffset Emu n := by chain_simp

lemma stageX_subcircuitsConsistent (xPrev xT lam2 : Var Emu (F circomPrime)) (n : ℕ) :
    Operations.forAll n { subcircuit := fun offset {m} _ => m = offset }
      (stageX xPrev xT lam2 n).2 := by chain_simp

lemma stageX_chanG (xPrev xT lam2 : Var Emu (F circomPrime)) (n : ℕ) :
    Operations.subcircuitChannelsWithGuarantees (stageX xPrev xT lam2 n).2 = [] := by
  chain_simp

lemma stageX_chanR (xPrev xT lam2 : Var Emu (F circomPrime)) (n : ℕ) :
    Operations.subcircuitChannelsWithRequirements (stageX xPrev xT lam2 n).2 = [] := by
  chain_simp

lemma stageX_shallow (xPrev xT lam2 : Var Emu (F circomPrime)) (n : ℕ) :
    Operations.shallowChannels (stageX xPrev xT lam2 n).2 = [] := by chain_simp

lemma stageX_guar (xPrev xT lam2 : Var Emu (F circomPrime)) (n : ℕ)
    (env : Environment (F circomPrime)) :
    Operations.forAllNoOffset { interact := fun i => i.Guarantees env }
      (stageX xPrev xT lam2 n).2 := by chain_simp

lemma stageX_req (xPrev xT lam2 : Var Emu (F circomPrime)) (n : ℕ)
    (env : Environment (F circomPrime)) :
    Operations.forAllNoOffset { interact := fun i => i.Requirements env }
      (stageX xPrev xT lam2 n).2 := by chain_simp

lemma stageX_subLawful (xPrev xT lam2 : Var Emu (F circomPrime)) (n : ℕ) :
    Operations.forAllNoOffset { subcircuit := fun {m} s => s.ChannelsLawful }
      (stageX xPrev xT lam2 n).2 := by chain_simp

lemma stageY_localLength (x xT yT lam : Var Emu (F circomPrime)) (n : ℕ) :
    Operations.localLength (stageY x xT yT lam n).2 = 730 := by chain_simp

lemma stageY_output (x xT yT lam : Var Emu (F circomPrime)) (n : ℕ) :
    (stageY x xT yT lam n).1 = varFromOffset Emu n := by chain_simp

lemma stageY_subcircuitsConsistent (x xT yT lam : Var Emu (F circomPrime)) (n : ℕ) :
    Operations.forAll n { subcircuit := fun offset {m} _ => m = offset }
      (stageY x xT yT lam n).2 := by chain_simp

lemma stageY_chanG (x xT yT lam : Var Emu (F circomPrime)) (n : ℕ) :
    Operations.subcircuitChannelsWithGuarantees (stageY x xT yT lam n).2 = [] := by
  chain_simp

lemma stageY_chanR (x xT yT lam : Var Emu (F circomPrime)) (n : ℕ) :
    Operations.subcircuitChannelsWithRequirements (stageY x xT yT lam n).2 = [] := by
  chain_simp

lemma stageY_shallow (x xT yT lam : Var Emu (F circomPrime)) (n : ℕ) :
    Operations.shallowChannels (stageY x xT yT lam n).2 = [] := by chain_simp

lemma stageY_guar (x xT yT lam : Var Emu (F circomPrime)) (n : ℕ)
    (env : Environment (F circomPrime)) :
    Operations.forAllNoOffset { interact := fun i => i.Guarantees env }
      (stageY x xT yT lam n).2 := by chain_simp

lemma stageY_req (x xT yT lam : Var Emu (F circomPrime)) (n : ℕ)
    (env : Environment (F circomPrime)) :
    Operations.forAllNoOffset { interact := fun i => i.Requirements env }
      (stageY x xT yT lam n).2 := by chain_simp

lemma stageY_subLawful (x xT yT lam : Var Emu (F circomPrime)) (n : ℕ) :
    Operations.forAllNoOffset { subcircuit := fun {m} s => s.ChannelsLawful }
      (stageY x xT yT lam n).2 := by chain_simp

/-- Implied accumulator y-coordinate of a chain state (value level). -/
noncomputable def impliedY (x lam : Emu (F circomPrime))
    (T : Select.AffPoint (F circomPrime)) : Specs.Secp256k1.Fp :=
  decodeFe lam * (decodeFe T.x - decodeFe x) - decodeFe T.y

end Chain

namespace ChainStart
open Chain
open Specs.ShortWeierstrass
open Specs.Secp256k1 (Fp curve)

def main (input : Var StartInputs (F circomPrime)) :
    Circuit (F circomPrime) (Var ChainXL (F circomPrime)) := do
  let { A, T } := input
  let lam1 ← PairAdd.stageA A.x A.y T.x T.y
  let x1 ← PairAdd.stageO2 A.x A.y T.x T.y lam1
  return { x := x1, lam := lam1 }

set_option maxHeartbeats 8000000 in
instance elaborated : ElaboratedCircuit (F circomPrime) StartInputs ChainXL main where
  localLength _ := 1446
  output _ i0 := { x := varFromOffset Emu (i0 + 725), lam := varFromOffset Emu i0 }
  localLength_eq := by
    intro input offset
    simp +arith only [main, circuit_norm,
      PairAdd.stageA_localLength, PairAdd.stageA_output,
      PairAdd.stageO2_localLength, PairAdd.stageO2_output]
  output_eq := by
    intro input offset
    simp +arith only [main, circuit_norm,
      PairAdd.stageA_localLength, PairAdd.stageA_output,
      PairAdd.stageO2_localLength, PairAdd.stageO2_output]
  subcircuitsConsistent := by
    intro input offset
    simp +arith only [main, circuit_norm, Operations.forAll_append,
      PairAdd.stageA_localLength, PairAdd.stageA_output,
      PairAdd.stageO2_localLength, PairAdd.stageO2_output,
      PairAdd.stageA_subcircuitsConsistent, PairAdd.stageO2_subcircuitsConsistent]
  channelsLawful := by
    intro input offset
    simp +arith only [main, circuit_norm,
      PairAdd.stageA_localLength, PairAdd.stageA_output,
      PairAdd.stageO2_localLength, PairAdd.stageO2_output,
      PairAdd.stageA_chanG, PairAdd.stageO2_chanG,
      PairAdd.stageA_chanR, PairAdd.stageO2_chanR,
      PairAdd.stageA_shallow, PairAdd.stageO2_shallow,
      PairAdd.stageA_guar, PairAdd.stageO2_guar,
      PairAdd.stageA_req, PairAdd.stageO2_req,
      PairAdd.stageA_subLawful, PairAdd.stageO2_subLawful,
      List.nil_subset, List.not_mem_nil, List.append_nil, List.nil_append]

def Assumptions (input : StartInputs (F circomPrime)) : Prop :=
  IncompleteAdd.NormAff input.A ∧ CompactAdd.TValid input.T ∧
  decodeFe input.A.x ≠ decodeFe input.T.x

noncomputable def Spec (input : StartInputs (F circomPrime))
    (out : ChainXL (F circomPrime)) : Prop :=
  BigInt.Normalized 64 out.x ∧ BigInt.Normalized 64 out.lam ∧
  GroupPoint.affine
      (⟨decodeFe out.x, impliedY out.x out.lam input.T⟩ : Point Fp)
    = Specs.ShortWeierstrass.add curve
        (.affine ⟨decodeFe input.A.x, decodeFe input.A.y⟩)
        (.affine ⟨decodeFe input.T.x, decodeFe input.T.y⟩)

end ChainStart

namespace ChainExt
open Chain
open Specs.ShortWeierstrass
open Specs.Secp256k1 (Fp curve)

def main (input : Var ExtInputs (F circomPrime)) :
    Circuit (F circomPrime) (Var ChainXL (F circomPrime)) := do
  let { x, lam, TP, T } := input
  let lam' ← PairAdd.stageC1 TP.x TP.y x lam T.x T.y
  let x' ← Chain.stageX x T.x lam'
  return { x := x', lam := lam' }

set_option maxHeartbeats 8000000 in
instance elaborated : ElaboratedCircuit (F circomPrime) ExtInputs ChainXL main where
  localLength _ := 1462
  output _ i0 := { x := varFromOffset Emu (i0 + 741), lam := varFromOffset Emu i0 }
  localLength_eq := by
    intro input offset
    simp +arith only [main, circuit_norm,
      PairAdd.stageC1_localLength, PairAdd.stageC1_output,
      Chain.stageX_localLength, Chain.stageX_output]
  output_eq := by
    intro input offset
    simp +arith only [main, circuit_norm,
      PairAdd.stageC1_localLength, PairAdd.stageC1_output,
      Chain.stageX_localLength, Chain.stageX_output]
  subcircuitsConsistent := by
    intro input offset
    simp +arith only [main, circuit_norm, Operations.forAll_append,
      PairAdd.stageC1_localLength, PairAdd.stageC1_output,
      Chain.stageX_localLength, Chain.stageX_output,
      PairAdd.stageC1_subcircuitsConsistent, Chain.stageX_subcircuitsConsistent]
  channelsLawful := by
    intro input offset
    simp +arith only [main, circuit_norm,
      PairAdd.stageC1_localLength, PairAdd.stageC1_output,
      Chain.stageX_localLength, Chain.stageX_output,
      PairAdd.stageC1_chanG, Chain.stageX_chanG,
      PairAdd.stageC1_chanR, Chain.stageX_chanR,
      PairAdd.stageC1_shallow, Chain.stageX_shallow,
      PairAdd.stageC1_guar, Chain.stageX_guar,
      PairAdd.stageC1_req, Chain.stageX_req,
      PairAdd.stageC1_subLawful, Chain.stageX_subLawful,
      List.nil_subset, List.not_mem_nil, List.append_nil, List.nil_append]

noncomputable def Assumptions (input : ExtInputs (F circomPrime)) : Prop :=
  BigInt.Normalized 64 input.x ∧ BigInt.Normalized 64 input.lam ∧
  CompactAdd.TValid input.TP ∧ CompactAdd.TValid input.T ∧
  OnCurve curve ⟨decodeFe input.x, impliedY input.x input.lam input.TP⟩ ∧
  decodeFe input.x ≠ decodeFe input.T.x

noncomputable def Spec (input : ExtInputs (F circomPrime))
    (out : ChainXL (F circomPrime)) : Prop :=
  BigInt.Normalized 64 out.x ∧ BigInt.Normalized 64 out.lam ∧
  GroupPoint.affine
      (⟨decodeFe out.x, impliedY out.x out.lam input.T⟩ : Point Fp)
    = Specs.ShortWeierstrass.add curve
        (.affine ⟨decodeFe input.x, impliedY input.x input.lam input.TP⟩)
        (.affine ⟨decodeFe input.T.x, decodeFe input.T.y⟩)

end ChainExt

namespace ChainFinish
open Chain
open Specs.ShortWeierstrass
open Specs.Secp256k1 (Fp curve)

def main (input : Var ChainState (F circomPrime)) :
    Circuit (F circomPrime) (Var Emu (F circomPrime)) := do
  let { x, lam, T } := input
  Chain.stageY x T.x T.y lam

set_option maxHeartbeats 8000000 in
instance elaborated : ElaboratedCircuit (F circomPrime) ChainState Emu main where
  localLength _ := 730
  output _ i0 := varFromOffset Emu i0
  localLength_eq := by
    intro input offset
    simp +arith only [main, circuit_norm,
      Chain.stageY_localLength, Chain.stageY_output]
  output_eq := by
    intro input offset
    simp +arith only [main, circuit_norm,
      Chain.stageY_localLength, Chain.stageY_output]
  subcircuitsConsistent := by
    intro input offset
    simp +arith only [main, circuit_norm, Operations.forAll_append,
      Chain.stageY_localLength, Chain.stageY_output,
      Chain.stageY_subcircuitsConsistent]
  channelsLawful := by
    intro input offset
    simp +arith only [main, circuit_norm,
      Chain.stageY_localLength, Chain.stageY_output,
      Chain.stageY_chanG, Chain.stageY_chanR, Chain.stageY_shallow,
      Chain.stageY_guar, Chain.stageY_req, Chain.stageY_subLawful,
      List.nil_subset, List.not_mem_nil, List.append_nil, List.nil_append]

def Assumptions (input : ChainState (F circomPrime)) : Prop :=
  BigInt.Normalized 64 input.x ∧ BigInt.Normalized 64 input.lam ∧
  CompactAdd.TValid input.T

noncomputable def Spec (input : ChainState (F circomPrime))
    (out : Emu (F circomPrime)) : Prop :=
  BigInt.Normalized 64 out ∧
  decodeFe out = impliedY input.x input.lam input.T

end ChainFinish
end Solution.Secp256k1ScalarMulFixedBase

end DonorFile6_8

-- Adapted donor module: PairAddGroupLaw
section DonorFile6_9

namespace Solution.Secp256k1ScalarMulFixedBase
namespace PairAdd

open Specs.ShortWeierstrass
open Specs.Secp256k1 (Fp curve chord_onCurve)

theorem add_eq_chord {P Q : Point Fp} (hx : P.x ≠ Q.x) :
    add curve (.affine P) (.affine Q) = .affine (chord P Q) := by
  rcases P with ⟨px, py⟩
  rcases Q with ⟨qx, qy⟩
  show (if px = qx then if py = -qy then GroupPoint.infinity
      else .affine (tangent curve ⟨px, py⟩) else .affine (chord ⟨px, py⟩ ⟨qx, qy⟩))
      = .affine (chord ⟨px, py⟩ ⟨qx, qy⟩)
  rw [if_neg hx]

theorem chord_pins (P Q : Point Fp) (lam x3 y3 : Fp)
    (hne : P.x ≠ Q.x)
    (hslope : lam * (Q.x - P.x) = Q.y - P.y)
    (hx3 : x3 = lam ^ 2 - P.x - Q.x)
    (hy3 : y3 = lam * (P.x - x3) - P.y) :
    (⟨x3, y3⟩ : Point Fp) = chord P Q := by
  have hd : Q.x - P.x ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hlam : lam = (Q.y - P.y) / (Q.x - P.x) := by rw [eq_div_iff hd]; exact hslope
  subst hx3
  subst hy3
  dsimp only [chord]
  rw [hlam]

theorem open_half_pins
    (xA yA xT1 yT1 lam1 x1 : Fp)
    (hocA : OnCurve curve ⟨xA, yA⟩)
    (hocT1 : OnCurve curve ⟨xT1, yT1⟩)
    (hne1 : xA ≠ xT1)
    (hA2 : lam1 * (xT1 - xA) = yT1 - yA)
    (hO2 : x1 = lam1 ^ 2 - xA - xT1) :
    x1 = (chord ⟨xA, yA⟩ ⟨xT1, yT1⟩).x
      ∧ lam1 * (xA - x1) - yA = (chord ⟨xA, yA⟩ ⟨xT1, yT1⟩).y
      ∧ OnCurve curve (⟨x1, lam1 * (xA - x1) - yA⟩ : Point Fp) := by
  have hpt : (⟨x1, lam1 * (xA - x1) - yA⟩ : Point Fp) = chord ⟨xA, yA⟩ ⟨xT1, yT1⟩ :=
    chord_pins ⟨xA, yA⟩ ⟨xT1, yT1⟩ lam1 x1 (lam1 * (xA - x1) - yA) hne1 hA2 hO2 rfl
  refine ⟨congrArg Point.x hpt, congrArg Point.y hpt, ?_⟩
  rw [hpt]
  exact chord_onCurve hocA hocT1 hne1

theorem pairadd_chord_assembly
    (xA yA xT1 yT1 xT2 yT2 lam1 x1 lam2 x2 y3 : Fp)
    (hocA : OnCurve curve ⟨xA, yA⟩)
    (hocT1 : OnCurve curve ⟨xT1, yT1⟩)
    (hocT2 : OnCurve curve ⟨xT2, yT2⟩)
    (hne1 : xA ≠ xT1)
    (hA2 : lam1 * (xT1 - xA) = yT1 - yA)
    (hO2 : x1 = lam1 ^ 2 - xA - xT1)
    (hne2 : (chord ⟨xA, yA⟩ ⟨xT1, yT1⟩).x ≠ xT2)
    (hC1 : lam2 * (xT2 - x1) + lam1 * (xA - x1) = yT2 + yA)
    (hC2a : x2 = lam2 ^ 2 - x1 - xT2)
    (hC2b : y3 = lam2 * (xT2 - x2) - yT2) :
    GroupPoint.affine (⟨x2, y3⟩ : Point Fp)
      = add curve
          (add curve (.affine ⟨xA, yA⟩) (.affine ⟨xT1, yT1⟩))
          (.affine ⟨xT2, yT2⟩)
      ∧ OnCurve curve (⟨x2, y3⟩ : Point Fp) := by

  have hMpt : (⟨x1, lam1 * (xA - x1) - yA⟩ : Point Fp) = chord ⟨xA, yA⟩ ⟨xT1, yT1⟩ :=
    chord_pins ⟨xA, yA⟩ ⟨xT1, yT1⟩ lam1 x1 (lam1 * (xA - x1) - yA) hne1 hA2 hO2 rfl
  have hMx : (chord ⟨xA, yA⟩ ⟨xT1, yT1⟩).x = x1 := (congrArg Point.x hMpt).symm
  have hMy : (chord ⟨xA, yA⟩ ⟨xT1, yT1⟩).y = lam1 * (xA - x1) - yA :=
    (congrArg Point.y hMpt).symm
  have hoc1 : OnCurve curve (chord ⟨xA, yA⟩ ⟨xT1, yT1⟩) := chord_onCurve hocA hocT1 hne1

  have hslope2 : lam2 * (xT2 - x1) = yT2 - (lam1 * (xA - x1) - yA) := by
    linear_combination hC1
  have hy3eq : y3 = lam2 * (x1 - x2) - (lam1 * (xA - x1) - yA) := by
    linear_combination hC2b + hslope2

  have hOuterPt : (⟨x2, y3⟩ : Point Fp)
      = chord (chord ⟨xA, yA⟩ ⟨xT1, yT1⟩) ⟨xT2, yT2⟩ := by
    apply chord_pins (chord ⟨xA, yA⟩ ⟨xT1, yT1⟩) ⟨xT2, yT2⟩ lam2 x2 y3
    · exact hne2
    · show lam2 * (xT2 - (chord ⟨xA, yA⟩ ⟨xT1, yT1⟩).x)
          = yT2 - (chord ⟨xA, yA⟩ ⟨xT1, yT1⟩).y
      rw [hMx, hMy]; linear_combination hC1
    · show x2 = lam2 ^ 2 - (chord ⟨xA, yA⟩ ⟨xT1, yT1⟩).x - xT2
      rw [hMx]; exact hC2a
    · show y3 = lam2 * ((chord ⟨xA, yA⟩ ⟨xT1, yT1⟩).x - x2)
          - (chord ⟨xA, yA⟩ ⟨xT1, yT1⟩).y
      rw [hMx, hMy]; exact hy3eq
  refine ⟨?_, ?_⟩
  · rw [add_eq_chord (P := (⟨xA, yA⟩ : Point Fp)) (Q := ⟨xT1, yT1⟩) hne1,
        add_eq_chord (P := chord ⟨xA, yA⟩ ⟨xT1, yT1⟩) (Q := ⟨xT2, yT2⟩) hne2,
        ← hOuterPt]
  · rw [hOuterPt]
    exact chord_onCurve hoc1 hocT2 hne2

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
open PairAdd (add_eq_chord chord_pins open_half_pins)

/-- Seed assembly: from the A-form slope and x certificates for `A + T`,
the pair `(x₁, lam₁)` represents `A + T` with implied y through `T`. -/
theorem chainstart_assembly
    (xA yA xT yT lam1 x1 : Fp)
    (hocA : OnCurve curve ⟨xA, yA⟩)
    (hocT : OnCurve curve ⟨xT, yT⟩)
    (hne : xA ≠ xT)
    (hA2 : lam1 * (xT - xA) = yT - yA)
    (hO2 : x1 = lam1 ^ 2 - xA - xT) :
    GroupPoint.affine (⟨x1, lam1 * (xT - x1) - yT⟩ : Point Fp)
      = add curve (.affine ⟨xA, yA⟩) (.affine ⟨xT, yT⟩)
      ∧ OnCurve curve (⟨x1, lam1 * (xT - x1) - yT⟩ : Point Fp) := by
  have hyT : lam1 * (xT - x1) - yT = lam1 * (xA - x1) - yA := by
    linear_combination hA2
  have hpt : (⟨x1, lam1 * (xT - x1) - yT⟩ : Point Fp) = chord ⟨xA, yA⟩ ⟨xT, yT⟩ := by
    rw [show (⟨x1, lam1 * (xT - x1) - yT⟩ : Point Fp)
        = (⟨x1, lam1 * (xA - x1) - yA⟩ : Point Fp) from by rw [hyT]]
    exact chord_pins ⟨xA, yA⟩ ⟨xT, yT⟩ lam1 x1 _ hne hA2 hO2 rfl
  refine ⟨?_, ?_⟩
  · rw [add_eq_chord hne, hpt]
  · rw [hpt]; exact chord_onCurve hocA hocT hne

/-- Chain-step assembly: the accumulator is `(xP, lamP, TP)` with implied
y `yP = lamP·(xTP − xP) − yTP`; the T-form slope certificate
`lam'·(xT − xP) + lamP·(xTP − xP) = yT + yTP` and the x certificate pin the
next state `(x', lam', T)` to represent `P + T`. -/
theorem chainstep_assembly
    (xP lamP xTP yTP xT yT lam' x' : Fp)
    (hocP : OnCurve curve ⟨xP, lamP * (xTP - xP) - yTP⟩)
    (hocT : OnCurve curve ⟨xT, yT⟩)
    (hne : xP ≠ xT)
    (hC1 : lam' * (xT - xP) + lamP * (xTP - xP) = yT + yTP)
    (hC2a : x' = lam' ^ 2 - xP - xT) :
    GroupPoint.affine (⟨x', lam' * (xT - x') - yT⟩ : Point Fp)
      = add curve (.affine ⟨xP, lamP * (xTP - xP) - yTP⟩) (.affine ⟨xT, yT⟩)
      ∧ OnCurve curve (⟨x', lam' * (xT - x') - yT⟩ : Point Fp) := by
  have hslope : lam' * (xT - xP) = yT - (lamP * (xTP - xP) - yTP) := by
    linear_combination hC1
  have hy' : lam' * (xT - x') - yT
      = lam' * (xP - x') - (lamP * (xTP - xP) - yTP) := by
    linear_combination hslope
  have hpt : (⟨x', lam' * (xT - x') - yT⟩ : Point Fp)
      = chord ⟨xP, lamP * (xTP - xP) - yTP⟩ ⟨xT, yT⟩ := by
    rw [show (⟨x', lam' * (xT - x') - yT⟩ : Point Fp)
        = (⟨x', lam' * (xP - x') - (lamP * (xTP - xP) - yTP)⟩ : Point Fp) from by rw [hy']]
    exact chord_pins ⟨xP, lamP * (xTP - xP) - yTP⟩ ⟨xT, yT⟩ lam' x' _ hne hslope hC2a rfl
  refine ⟨?_, ?_⟩
  · rw [add_eq_chord hne, hpt]
  · rw [hpt]; exact chord_onCurve hocP hocT hne

end Chain
end Solution.Secp256k1ScalarMulFixedBase

end DonorFile6_10

-- Adapted donor module: SelectCircuit
section DonorFile6_11




namespace Solution.Secp256k1ScalarMulFixedBase.Width12.SelectorBridge

open Select12
open Width12.Tables

/-- Concrete real-data selector specification.  The sign bit chooses positive y
when it is one and `P256-y` when it is zero, while x is unchanged. -/
def RealSpec (win : Fin 8) (b : fields 12 Select12.Field)
    (out : Select12.AffPoint Select12.Field) : Prop :=
  Select12.Spec
    (fun j => magXNat (win.val * magnitudes + j))
    (fun j => magYNat (win.val * magnitudes + j)) b out

/-- The zero sign branch returns the certified negative y coordinate. -/
theorem realSpec_sign_zero (win : Fin 8) (b : fields 12 Select12.Field)
    (out : Select12.AffPoint Select12.Field) (hs : b[11] = 0)
    (hout : RealSpec win b out) :
    out.y = Vector.ofFn (fun i : Fin 4 =>
      ((limbOfNat (P256 - magYNat (win.val * magnitudes + Select12.magnitudeIndex b))
        i.val : Nat) : Select12.Field)) := by
  rcases hout with ⟨_, hy⟩
  rw [hy]
  apply Vector.ext
  intro i hi
  rw [Vector.getElem_ofFn, Vector.getElem_ofFn]
  have hsval : b[11].val = 0 := by simpa using congrArg ZMod.val hs
  rw [hsval]
  ring

/-- The one sign branch returns the certified positive y coordinate. -/
theorem realSpec_sign_one (win : Fin 8) (b : fields 12 Select12.Field)
    (out : Select12.AffPoint Select12.Field) (hs : b[11] = 1)
    (hout : RealSpec win b out) :
    out.y = Vector.ofFn (fun i : Fin 4 =>
      ((limbOfNat (magYNat (win.val * magnitudes + Select12.magnitudeIndex b))
        i.val : Nat) : Select12.Field)) := by
  rcases hout with ⟨_, hy⟩
  rw [hy]
  apply Vector.ext
  intro i hi
  rw [Vector.getElem_ofFn, Vector.getElem_ofFn]
  have hsval : b[11].val = 1 := by simpa using congrArg ZMod.val hs
  rw [hsval]
  ring

end Solution.Secp256k1ScalarMulFixedBase.Width12.SelectorBridge

end DonorFile6_11

-- Adapted donor module: CombTableBridge
section DonorFile6_12


set_option maxRecDepth 2048

namespace Solution.Secp256k1ScalarMulFixedBase.Width12.Bridge

open Specs.ShortWeierstrass Specs.Secp256k1
open Solution.Secp256k1ScalarMulFixedBase.GroupLaw

/-- Width-12 safety for abstract `CollisionFree` sites `t ≤ 18`.  In that
API the added scalar has exponent `12 * (t+1)`, so this range does not include
the production caller's last extension, which uses `t = 19`. -/
theorem safe_w12 {t : ℕ} (ht : t ≤ 18) :
    (2 : ℤ) ^ (12 * (t + 2)) ≤ ((order : ℕ) : ℤ) := by
  have h1 : (2 : ℤ) ^ (12 * (t + 2)) ≤ 2 ^ 240 :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have h2 : (2 : ℤ) ^ 240 ≤ ((order : ℕ) : ℤ) := by norm_num [order]
  linarith

/-- Safety bound in the production `ChainExt` convention.  Extension `k`
adds regular window `k+2`, hence instantiates `CollisionFree` at site
`t = k+1`; its post-step bound has exponent `12 * (k+3)`. -/
theorem safe_w12_chain_ext (k : Fin 19) :
    (2 : ℤ) ^ (12 * (k.val + 3)) ≤ ((order : ℕ) : ℤ) := by
  have h1 : (2 : ℤ) ^ (12 * (k.val + 3)) ≤ 2 ^ 252 :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have h2 : (2 : ℤ) ^ 252 ≤ ((order : ℕ) : ℤ) := by norm_num [order]
  linarith

/-- X-coordinate noncollision in the exact shape needed by the future
width-12 `CombFoldStep` extension call. -/
theorem site_xcoord_ne_w12_chain_ext (k : Fin 19)
    {s d : ℤ} (hs : Odd s) (hsb : |s| < 2 ^ (12 * (k.val + 2)))
    (hd : Odd d) (hdb : |d| < 2 ^ 12)
    {PA PT : Point Fp}
    (hA : zsmul s (.affine G) = .affine PA)
    (hT : zsmul (d * 2 ^ (12 * (k.val + 2))) (.affine G) = .affine PT) :
    PA.x ≠ PT.x := by
  apply CollisionFree.site_xcoord_ne 12 (k.val + 1) (by norm_num)
    (by simpa [Nat.add_assoc] using safe_w12_chain_ext k) hs
    (by simpa [Nat.add_assoc] using hsb) hd hdb
  · exact hA
  · simpa [Nat.add_assoc] using hT

/-- Legacy abstract-site wrapper, retained for compatibility. -/
theorem site_xcoord_ne_w12 {t : ℕ} (ht : t ≤ 18)
    {s d : ℤ} (hs : Odd s) (hsb : |s| < 2 ^ (12 * (t + 1)))
    (hd : Odd d) (hdb : |d| < 2 ^ 12)
    {PA PT : Point Fp}
    (hA : zsmul s (.affine G) = .affine PA)
    (hT : zsmul (d * 2 ^ (12 * (t + 1))) (.affine G) = .affine PT) :
    PA.x ≠ PT.x :=
  CollisionFree.site_xcoord_ne 12 t (by norm_num) (safe_w12 ht) hs hsb hd hdb hA hT

end Solution.Secp256k1ScalarMulFixedBase.Width12.Bridge



namespace Solution.Secp256k1ScalarMulFixedBase
namespace CombTableBridge

open Specs.ShortWeierstrass Specs.Secp256k1
open Solution.Secp256k1ScalarMulFixedBase.GroupLaw
open Solution.Secp256k1ScalarMulFixedBase.OrderFacts

lemma magXNat_lt {win j : ℕ} (hw : win ≤ 28) (hj : j < 256) :
    Tables.magXNat (win * 256 + j) < P256 := by
  haveI : NeZero P256 := ⟨hPrime.ne_zero⟩
  unfold Tables.magXNat
  exact ZMod.val_lt _


lemma magYNat_bnd_top {j : ℕ} (hj : j < 8) :
    0 < Tables.magYNat (28 * 256 + j) ∧ Tables.magYNat (28 * 256 + j) < P256 := by
  haveI : NeZero P256 := ⟨hPrime.ne_zero⟩
  have hdiv : (28 * 256 + j) / 256 = 28 := by omega
  have hmod : (28 * 256 + j) % 256 = j := by omega
  refine ⟨?_, ?_⟩
  · unfold Tables.magYNat
    rw [hdiv, hmod]
    have hne := TableCerts.magY_ne_zero_top ⟨j, hj⟩
    exact Nat.pos_of_ne_zero fun hz => hne ((ZMod.val_eq_zero _).mp hz)
  · unfold Tables.magYNat
    exact ZMod.val_lt _

lemma zsmul_neg {P : GroupPoint Fp} (h : OnCurveOrInfinity curve P) (n : ℤ) :
    zsmul (-n) P = specNeg (zsmul n P) := by
  rw [zsmul_eq h (-n), zsmul_eq h n, neg_zsmul, fromW_neg]

lemma decodeFe_emuOfNat {v : ℕ} (hv : v < P256) :
    decodeFe (emuOfNat v) = ((v : ℕ) : Fp) := by
  rw [decodeFe, CompleteAdd.value_emuOfNat (lt_trans hv P256_lt)]


lemma bitsValTop_lt (b : fields 4 (F circomPrime)) (hb : ∀ i : Fin 4, IsBool b[i]) :
    SelectTop.bitsVal b < 16 := by
  have hle : ∀ (j : ℕ) (hj : j < 4), (b[j]'hj).val ≤ 1 := fun j hj =>
    Select.IsBool.val_le_one (hb ⟨j, hj⟩)
  have h0 := hle 0 (by omega)
  have h1 := hle 1 (by omega)
  have h2 := hle 2 (by omega)
  have h3 := hle 3 (by omega)
  rw [SelectTop.bitsVal]
  omega


theorem selectTop_decodes_zsmul (b : fields 4 (F circomPrime))
    (hb : ∀ i : Fin 4, IsBool b[i]) (out : Select.AffPoint (F circomPrime))
    (hspec : SelectTop.Spec b out) :
    CompactAdd.TValid out ∧
      zsmul ((2 * (SelectTop.bitsVal b : ℤ) + 1 - 16) * 2 ^ (9 * 28)) (.affine G)
        = .affine { x := decodeFe out.x, y := decodeFe out.y } := by
  obtain ⟨hx, hy⟩ := hspec
  set m := SelectTop.bitsVal b with hm
  have hm16 : m < 16 := bitsValTop_lt b hb
  by_cases hc : 8 ≤ m
  ·
    have hjlt : m - 8 < 8 := by omega
    have hmx := magXNat_lt (le_refl 28) (by omega : m - 8 < 256)
    obtain ⟨hmy0, hmy⟩ := magYNat_bnd_top hjlt
    have hsx : SelectTop.sigXNat m = Tables.magXNat (28 * 256 + (m - 8)) := by
      rw [SelectTop.sigXNat, if_pos hc]
    have hsy : SelectTop.sigYNat m = Tables.magYNat (28 * 256 + (m - 8)) := by
      rw [SelectTop.sigYNat, if_pos hc]
    have hdx : decodeFe out.x = ((Tables.magXNat (28 * 256 + (m - 8)) : ℕ) : Fp) := by
      rw [hx, hsx, decodeFe_emuOfNat hmx]
    have hdy : decodeFe out.y = ((Tables.magYNat (28 * 256 + (m - 8)) : ℕ) : Fp) := by
      rw [hy, hsy, decodeFe_emuOfNat hmy]
    have hcert' : zsmul ((2 * ((m - 8 : ℕ) : ℤ) + 1) * 2 ^ (9 * 28)) (.affine G)
        = .affine ⟨((Tables.magXNat (28 * 256 + (m - 8)) : ℕ) : Fp),
                   ((Tables.magYNat (28 * 256 + (m - 8)) : ℕ) : Fp)⟩ :=
      TableCerts.tableCertTop ⟨m - 8, hjlt⟩
    have hscal : (2 * (m : ℤ) + 1 - 16) * 2 ^ (9 * 28)
        = (2 * ((m - 8 : ℕ) : ℤ) + 1) * 2 ^ (9 * 28) := by
      have hjc : ((m - 8 : ℕ) : ℤ) = (m : ℤ) - 8 := by omega
      rw [hjc]; ring
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · rw [hx, hsx]; exact CompleteAdd.fe_valid_emuOfNat hmx
    · rw [hy, hsy]; exact CompleteAdd.fe_valid_emuOfNat hmy
    · rw [hdx, hdy]
      have hoc := zsmul_onCurveOrInfinity hGoc ((2 * ((m - 8 : ℕ) : ℤ) + 1) * 2 ^ (9 * 28))
      rw [hcert'] at hoc
      exact hoc
    · rw [hdx, hdy, hscal]; exact hcert'
  ·
    push_neg at hc
    have hjlt : 7 - m < 8 := by omega
    have hmx := magXNat_lt (le_refl 28) (by omega : 7 - m < 256)
    obtain ⟨hmy0, hmy⟩ := magYNat_bnd_top hjlt
    have hsx : SelectTop.sigXNat m = Tables.magXNat (28 * 256 + (7 - m)) := by
      rw [SelectTop.sigXNat, if_neg (by omega)]
    have hsy : SelectTop.sigYNat m = P256 - Tables.magYNat (28 * 256 + (7 - m)) := by
      rw [SelectTop.sigYNat, if_neg (by omega)]
    have hdx : decodeFe out.x = ((Tables.magXNat (28 * 256 + (7 - m)) : ℕ) : Fp) := by
      rw [hx, hsx, decodeFe_emuOfNat hmx]
    have hdy : decodeFe out.y = -((Tables.magYNat (28 * 256 + (7 - m)) : ℕ) : Fp) := by
      rw [hy, hsy, decodeFe_emuOfNat (Nat.sub_lt P256_pos hmy0),
        Nat.cast_sub (le_of_lt hmy),
        show ((P256 : ℕ) : Fp) = 0 from ZMod.natCast_self _, zero_sub]
    have hcert' : zsmul ((2 * ((7 - m : ℕ) : ℤ) + 1) * 2 ^ (9 * 28)) (.affine G)
        = .affine ⟨((Tables.magXNat (28 * 256 + (7 - m)) : ℕ) : Fp),
                   ((Tables.magYNat (28 * 256 + (7 - m)) : ℕ) : Fp)⟩ :=
      TableCerts.tableCertTop ⟨7 - m, hjlt⟩
    have hscal : (2 * (m : ℤ) + 1 - 16) * 2 ^ (9 * 28)
        = -((2 * ((7 - m : ℕ) : ℤ) + 1) * 2 ^ (9 * 28)) := by
      have hjc : ((7 - m : ℕ) : ℤ) = 7 - (m : ℤ) := by omega
      rw [hjc]; ring
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · rw [hx, hsx]; exact CompleteAdd.fe_valid_emuOfNat hmx
    · rw [hy, hsy]; exact CompleteAdd.fe_valid_emuOfNat (Nat.sub_lt P256_pos hmy0)
    · rw [hdx, hdy]
      have hoc := zsmul_onCurveOrInfinity hGoc ((2 * ((7 - m : ℕ) : ℤ) + 1) * 2 ^ (9 * 28))
      rw [hcert'] at hoc
      have hcurve : OnCurve curve
          ⟨((Tables.magXNat (28 * 256 + (7 - m)) : ℕ) : Fp),
           ((Tables.magYNat (28 * 256 + (7 - m)) : ℕ) : Fp)⟩ := hoc
      rw [onCurve_iff] at hcurve
      rw [onCurve_iff]
      linear_combination hcurve
    · rw [hdx, hdy, hscal, zsmul_neg hGoc, hcert']
      rfl


lemma bitsVal12_lt (b : fields 12 (F circomPrime))
    (hb : Select12.Assumptions b) : Select12.bitsVal b < 4096 := by
  have hle : ∀ (j : ℕ) (hj : j < 12), (b[j]'hj).val ≤ 1 := fun j hj =>
    Select.IsBool.val_le_one (hb ⟨j, hj⟩)
  have h0 := hle 0 (by omega); have h1 := hle 1 (by omega)
  have h2 := hle 2 (by omega); have h3 := hle 3 (by omega)
  have h4 := hle 4 (by omega); have h5 := hle 5 (by omega)
  have h6 := hle 6 (by omega); have h7 := hle 7 (by omega)
  have h8 := hle 8 (by omega); have h9 := hle 9 (by omega)
  have h10 := hle 10 (by omega); have h11 := hle 11 (by omega)
  rw [Select12.bitsVal]
  omega

lemma digit12_odd_bound (b : fields 12 (F circomPrime))
    (hb : Select12.Assumptions b) :
    Odd (2 * (Select12.bitsVal b : ℤ) + 1 - 4096) ∧
      |2 * (Select12.bitsVal b : ℤ) + 1 - 4096| < 4096 := by
  have h := CollisionFree.digit_facts 12 (by norm_num) (Select12.bitsVal b)
    (bitsVal12_lt b hb)
  norm_num at h ⊢
  exact h

lemma select12_spec_exact (win : Fin 8) (b : fields 12 (F circomPrime))
    (out : Select.AffPoint (F circomPrime)) (hb : Select12.Assumptions b)
    (hspec : Width12.SelectorBridge.RealSpec win b out) :
    out.x = emuOfNat (Width12.Tables.magXNat
      (win.val * Width12.Tables.magnitudes + Select12.magnitudeIndex b)) ∧
    out.y = if b[11] = 1 then
        emuOfNat (Width12.Tables.magYNat
          (win.val * Width12.Tables.magnitudes + Select12.magnitudeIndex b))
      else emuOfNat (P256 - Width12.Tables.magYNat
        (win.val * Width12.Tables.magnitudes + Select12.magnitudeIndex b)) := by
  constructor
  · rw [hspec.1]
    apply Vector.ext
    intro i hi
    rw [Vector.getElem_ofFn, emuOfNat_getElem]
  · rcases hb ⟨11, by omega⟩ with hzero | hone
    · have hz : b[11] = 0 := by simpa only using hzero
      have hne : b[11] ≠ 1 := by
        rw [hz]
        exact zero_ne_one
      rw [if_neg hne]
      rw [Width12.SelectorBridge.realSpec_sign_zero win b out hz hspec]
      apply Vector.ext
      intro i hi
      rw [Vector.getElem_ofFn, emuOfNat_getElem]
    · have ho : b[11] = 1 := by simpa only using hone
      rw [if_pos ho]
      rw [Width12.SelectorBridge.realSpec_sign_one win b out ho hspec]
      apply Vector.ext
      intro i hi
      rw [Vector.getElem_ofFn, emuOfNat_getElem]

theorem select12_decodes_zsmul (win : Fin 8) (b : fields 12 (F circomPrime))
    (hb : Select12.Assumptions b) (out : Select.AffPoint (F circomPrime))
    (hspec : Width12.SelectorBridge.RealSpec win b out) :
    CompactAdd.TValid out ∧
      zsmul ((2 * (Select12.bitsVal b : ℤ) + 1 - 4096) * 2 ^ (12 * win.val))
        (.affine G) = .affine { x := decodeFe out.x, y := decodeFe out.y } := by
  let d : ℤ := 2 * (Select12.bitsVal b : ℤ) + 1 - 4096
  let j : ℕ := Select12.magnitudeIndex b
  have hj : j < 2048 := by
    dsimp [j]
    rw [← Select12.transformedIndex_eq b hb]
    exact Select12.transformedIndex_lt b
  have hcoords := Width12.TableCerts.coordinates_lt win ⟨j, hj⟩
  have hspec' := select12_spec_exact win b out hb hspec
  have hcert := Width12.TableCerts.tableCert win ⟨j, hj⟩
  have hcert' :
      zsmul ((2 * (j : ℤ) + 1) * 2 ^ (12 * win.val)) (.affine G) =
        .affine (Width12.Tables.magPt win.val j) := by
    simpa only [Width12.Tables.Gpt] using hcert
  have hlookup := Width12.TableCerts.lookup_semantics win ⟨j, hj⟩
  have hyne := Width12.TableYNonzero.magY_ne_zero win ⟨j, hj⟩
  have hynatpos : 0 < Width12.Tables.magYNat
      (win.val * Width12.Tables.magnitudes + j) := by
    apply Nat.pos_of_ne_zero
    intro hz
    apply hyne
    have hy := congrArg Prod.snd hlookup
    rw [hz] at hy
    simpa using hy.symm
  rcases hb ⟨11, by omega⟩ with hzero | hone
  · have hz : b[11] = 0 := by simpa only using hzero
    have hne : b[11] ≠ 1 := by
      rw [hz]
      exact zero_ne_one
    have hbits : Select12.bitsVal b < 2048 := by
      have hv : b[11].val = 0 := by rw [hz]; rfl
      have hle : ∀ (k : ℕ) (hk : k < 12), (b[k]'hk).val ≤ 1 := fun k hk =>
        Select.IsBool.val_le_one (hb ⟨k, hk⟩)
      have h0 := hle 0 (by omega); have h1 := hle 1 (by omega)
      have h2 := hle 2 (by omega); have h3 := hle 3 (by omega)
      have h4 := hle 4 (by omega); have h5 := hle 5 (by omega)
      have h6 := hle 6 (by omega); have h7 := hle 7 (by omega)
      have h8 := hle 8 (by omega); have h9 := hle 9 (by omega)
      have h10 := hle 10 (by omega)
      rw [Select12.bitsVal, hv]
      omega
    have hjval : j = 2047 - Select12.bitsVal b := by
      simp [j, Select12.magnitudeIndex, show ¬ 2048 ≤ Select12.bitsVal b by omega]
    have hd : d = -(2 * (j : ℤ) + 1) := by
      dsimp [d]
      rw [hjval]
      push_cast
      omega
    have hdx : decodeFe out.x = (Width12.Tables.magPt win.val j).x := by
      rw [hspec'.1, decodeFe_emuOfNat hcoords.1]
      exact congrArg Prod.fst hlookup
    have hdy : decodeFe out.y = -(Width12.Tables.magPt win.val j).y := by
      rw [hspec'.2, if_neg hne,
        decodeFe_emuOfNat (Nat.sub_lt P256_pos hynatpos)]
      rw [Nat.cast_sub (le_of_lt hcoords.2), ZMod.natCast_self, zero_sub]
      exact congrArg Neg.neg (congrArg Prod.snd hlookup)
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · rw [hspec'.1]; exact CompleteAdd.fe_valid_emuOfNat hcoords.1
    · rw [hspec'.2, if_neg hne]
      exact CompleteAdd.fe_valid_emuOfNat (Nat.sub_lt P256_pos
        hynatpos)
    · rw [hdx, hdy]
      have hoc := Width12.TableCerts.tableOnCurve win ⟨j, hj⟩
      rw [onCurve_iff] at hoc ⊢
      linear_combination hoc
    · rw [hdx, hdy]
      change zsmul (d * 2 ^ (12 * win.val)) (.affine G) = _
      rw [hd]
      have hcoef : -(2 * (j : ℤ) + 1) * 2 ^ (12 * win.val) =
          -((2 * (j : ℤ) + 1) * 2 ^ (12 * win.val)) := by ring
      rw [hcoef, zsmul_neg hGoc, hcert']
      rfl
  · have ho : b[11] = 1 := by simpa only using hone
    have hbits : 2048 ≤ Select12.bitsVal b := by
      have hv : b[11].val = 1 := by rw [ho]; rfl
      rw [Select12.bitsVal, hv]
      omega
    have hjval : j = Select12.bitsVal b - 2048 := by
      simp [j, Select12.magnitudeIndex, hbits]
    have hd : d = 2 * (j : ℤ) + 1 := by
      dsimp [d]
      rw [hjval]
      push_cast
      omega
    have hdx : decodeFe out.x = (Width12.Tables.magPt win.val j).x := by
      rw [hspec'.1, decodeFe_emuOfNat hcoords.1]
      exact congrArg Prod.fst hlookup
    have hdy : decodeFe out.y = (Width12.Tables.magPt win.val j).y := by
      rw [hspec'.2, if_pos ho, decodeFe_emuOfNat hcoords.2]
      exact congrArg Prod.snd hlookup
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · rw [hspec'.1]; exact CompleteAdd.fe_valid_emuOfNat hcoords.1
    · rw [hspec'.2, if_pos ho]; exact CompleteAdd.fe_valid_emuOfNat hcoords.2
    · rw [hdx, hdy]; exact Width12.TableCerts.tableOnCurve win ⟨j, hj⟩
    · rw [hdx, hdy]
      change zsmul (d * 2 ^ (12 * win.val)) (.affine G) = _
      rw [hd, hcert']

theorem seed12_invariant (b : fields 12 (F circomPrime))
    (hb : Select12.Assumptions b) (out : Select.AffPoint (F circomPrime))
    (hspec : Width12.SelectorBridge.RealSpec ⟨0, by omega⟩ b out) :
    CompactAdd.TValid out ∧
      zsmul (2 * (Select12.bitsVal b : ℤ) + 1 - 4096) (.affine G)
        = .affine { x := decodeFe out.x, y := decodeFe out.y } ∧
      Odd (2 * (Select12.bitsVal b : ℤ) + 1 - 4096) ∧
      |2 * (Select12.bitsVal b : ℤ) + 1 - 4096| < 2 ^ 12 := by
  obtain ⟨htv, heq⟩ := select12_decodes_zsmul ⟨0, by omega⟩ b hb out hspec
  obtain ⟨hodd, hbnd⟩ := digit12_odd_bound b hb
  refine ⟨htv, ?_, hodd, ?_⟩
  · simpa using heq
  · norm_num at hbnd ⊢
    exact hbnd

end CombTableBridge
end Solution.Secp256k1ScalarMulFixedBase

end DonorFile6_12

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

lemma H_sparse_relation : H ^ 8 = H + 977 + q := by
  norm_num [H, q, c]

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

def weight (m : ℕ) (i j k : Fin m) : ℕ :=
  if k.val = (i.val+j.val)%m then (if i.val+j.val < m then 1 else c) else 0

def coeff {K : Type*} [CommRing K] {m : ℕ} (a : Fin m → K) (k : Fin m) : K :=
  ∑ i : Fin m, ∑ j : Fin m, (weight m i j k : K) * (a i * a j)

def poly {K : Type*} [CommRing K] {m : ℕ} (a : Fin m → K) (r : K) : K :=
  ∑ i : Fin m, a i * r^i.val

lemma weight_eval {K : Type*} [CommRing K] {m : ℕ} (hm : 0 < m)
    (i j : Fin m) (r : K) (hr : r^m = (c : K)) :
    (∑ k : Fin m, (weight m i j k : K) * r^k.val) = r^i.val * r^j.val := by
  let k : Fin m := ⟨(i.val+j.val)%m, Nat.mod_lt _ hm⟩
  rw [Finset.sum_eq_single k]
  · have hk : k.val = (i.val+j.val)%m := rfl
    simp only [weight, hk, ↓reduceIte]
    rw [← pow_add]
    by_cases h : i.val+j.val < m
    · simp [h, Nat.mod_eq_of_lt h]
    · have hij : i.val+j.val-m < m := by omega
      have he : (i.val+j.val)%m = i.val+j.val-m := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt hij]
      rw [if_neg h, he]
      have hs : i.val+j.val = m+(i.val+j.val-m) := by omega
      conv_rhs => rw [hs, pow_add, hr]
  · intro l _ hne
    have hl : l.val ≠ (i.val+j.val)%m := by
      intro he
      exact hne (Fin.ext he)
    simp [weight, hl]
  · simp

theorem poly_coeff {K : Type*} [CommRing K] {m : ℕ} (hm : 0 < m)
    (a : Fin m → K) (r : K) (hr : r^m = (c : K)) :
    poly (coeff a) r = (poly a r)^2 := by
  unfold poly coeff
  simp_rw [Finset.sum_mul]
  have hs : (∑ k : Fin m, ∑ i : Fin m, ∑ j : Fin m,
      (weight m i j k : K)*(a i*a j)*r^k.val) =
      ∑ i : Fin m, ∑ j : Fin m, ∑ k : Fin m,
        (weight m i j k : K)*(a i*a j)*r^k.val := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    exact Finset.sum_comm
  rw [hs]
  simp_rw [show ∀ i j k : Fin m,
    (weight m i j k : K)*(a i*a j)*r^k.val =
      ((weight m i j k : K)*r^k.val)*(a i*a j) by intros; ring]
  simp_rw [← Finset.sum_mul, weight_eval hm _ _ r hr]
  rw [pow_two, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem coeff_nonneg {m : ℕ} (a : Fin m → ℤ) (ha : ∀ i, 0 ≤ a i) (k : Fin m) :
    0 ≤ coeff a k := by
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (Int.natCast_nonneg _) (mul_nonneg (ha i) (ha j))

theorem coeff_le {m : ℕ} (a : Fin m → ℤ) (D : ℤ)
    (ha : ∀ i, 0 ≤ a i ∧ a i ≤ D) (k : Fin m) :
    coeff a k ≤ ((∑ i : Fin m, ∑ j : Fin m, weight m i j k : ℕ) : ℤ)*D^2 := by
  have hterm (i j : Fin m) :
      (weight m i j k : ℤ)*(a i*a j) ≤ (weight m i j k : ℤ)*D^2 := by
    apply mul_le_mul_of_nonneg_left _ (Int.natCast_nonneg _)
    rw [pow_two]
    exact mul_le_mul (ha i).2 (ha j).2 (ha j).1 (le_trans (ha i).1 (ha i).2)
  calc
    coeff a k ≤ ∑ i : Fin m, ∑ j : Fin m, (weight m i j k : ℤ)*D^2 :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
    _ = _ := by simp only [Nat.cast_sum, Finset.sum_mul]

theorem coeff_cast {K : Type*} [CommRing K] {m : ℕ} (a : Fin m → ℤ) (k : Fin m) :
    ((coeff a k : ℤ) : K) = coeff (fun i => (a i : K)) k := by
  simp only [coeff, Int.cast_sum, Int.cast_mul, Int.cast_natCast]

theorem poly_cast {K : Type*} [CommRing K] {m : ℕ} (a : Fin m → ℤ) (r : ℤ) :
    ((poly a r : ℤ) : K) = poly (fun i => (a i : K)) (r : K) := by
  simp only [poly, Int.cast_sum, Int.cast_mul, Int.cast_pow]

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
def cap (l : Layout) (i : Fin (count l)) : ℤ :=
  ((i.val+1+c*(count l-1-i.val) : ℕ) : ℤ)*(base l-1)^2
def R : ℤ := 2^128
def q : ℤ := 2^256-c

def halfPoly {K : Type*} [CommRing K] (l : Layout)
    (a : Fin (count l) → K) (side : Bool) : K :=
  ∑ i : Fin (count l/2),
    a ⟨i.val + (if side then count l/2 else 0), by cases l <;> cases side <;> simp [count] at * <;> omega⟩ *
      ((base l : ℤ) : K)^i.val

lemma weights_sum (l : Layout) (k : Fin (count l)) :
    (∑ i : Fin (count l), ∑ j : Fin (count l), weight (count l) i j k) =
      k.val+1+c*(count l-1-k.val) := by
  cases l <;> revert k <;> decide

lemma coeff_bounds (l : Layout) (a : Fin (count l) → ℤ)
    (ha : ∀ i, 0 ≤ a i ∧ a i < base l) (k : Fin (count l)) :
    0 ≤ coeff a k ∧ coeff a k ≤ cap l k := by
  refine ⟨coeff_nonneg a (fun i => (ha i).1) k, ?_⟩
  have h := coeff_le a (base l-1) (fun i => ⟨(ha i).1, by have := (ha i).2; omega⟩) k
  simpa only [weights_sum, cap] using h

lemma halfPoly_bounds (l : Layout) (a : Fin (count l) → ℤ)
    (ha : ∀ i, 0 ≤ a i ∧ a i < base l) (side : Bool) :
    0 ≤ halfPoly l (coeff a) side ∧
      halfPoly l (coeff a) side ≤ halfPoly l (cap l) side := by
  have hb : 0 ≤ base l := by cases l <;> norm_num [base, bits]
  constructor
  · apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (coeff_bounds l a ha _).1 (pow_nonneg hb _)
  · apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_right (coeff_bounds l a ha _).2 (pow_nonneg hb _)

lemma poly_halves (l : Layout) (a : Fin (count l) → ℤ) :
    poly a (base l) = halfPoly l a false + R*halfPoly l a true := by
  cases l <;> simp only [poly, halfPoly, count, base, bits, R, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ, Bool.false_eq_true,
    ↓reduceIte, Nat.reduceDiv, Nat.add_zero] <;> norm_num [Fin.succ] <;> ring

def loMin : Layout → ℤ | .w32 => -680564733841876926926749214880716296001 | .w16 => -680564733841876926926749214880716296001
def loMax : Layout → ℤ | .w32 => 25108412654556622383113918038080286487207698814510492027764 | .w16 => 766237714400183632796033881497451617087423522003757564
def hiMin : Layout → ℤ | .w32 => 340282366920938463463374607431768211458 | .w16 => 340282366920938463463374607431768211458
def hiMax : Layout → ℤ | .w32 => 13153515066732586910985349980772878607498229058423 | .w16 => 1461858777286281119958628182901764705894322412223
def qbits : Layout → ℕ | .w32 => 36 | .w16 => 33
def tbits : Layout → ℕ | .w32 => 67 | .w16 => 51
def offset : Layout → ℤ | .w32 => 38654706637 | .w16 => 4296016837

lemma bounds (l : Layout) (a : Fin (count l) → ℤ)
    (ha : ∀ i, 0 ≤ a i ∧ a i < base l) (tl th : ℤ)
    (htl : 0 ≤ tl ∧ tl ≤ 3*(R-1)) (hth : 0 ≤ th ∧ th ≤ 3*(R-1)) :
    (loMin l ≤ halfPoly l (coeff a) false + (4*q)%R-tl ∧
      halfPoly l (coeff a) false + (4*q)%R-tl ≤ loMax l) ∧
    (hiMin l ≤ halfPoly l (coeff a) true + (4*q)/R-th ∧
      halfPoly l (coeff a) true + (4*q)/R-th ≤ hiMax l) := by
  have hl := halfPoly_bounds l a ha false
  have hh := halfPoly_bounds l a ha true
  cases l <;> simp only [halfPoly, count, Nat.reduceDiv] at hl hh ⊢ <;>
    norm_num [halfPoly, cap, count, base, bits, R, q, c, loMin, loMax, hiMin, hiMax,
      Fin.sum_univ_succ] at hl hh htl hth ⊢ <;> omega

lemma certificate_complete (l : Layout) (L H k : ℤ)
    (hL : loMin l ≤ L ∧ L ≤ loMax l) (hH : hiMin l ≤ H ∧ H ≤ hiMax l)
    (he : L+R*H=q*k) :
    (0 ≤ k ∧ k < 2^(qbits l)) ∧
    (0 ≤ (R-1)*k-H+offset l ∧ (R-1)*k-H+offset l < 2^(tbits l)) := by
  cases l <;> norm_num [loMin, loMax, hiMin, hiMax, R, q, c, qbits, tbits, offset] at * <;> omega

lemma certificate_sound (l : Layout) (L H k v : ℤ)
    (hL : loMin l ≤ L ∧ L ≤ loMax l) (hH : hiMin l ≤ H ∧ H ≤ hiMax l)
    (hk : 0 ≤ k ∧ k < 2^(qbits l)) (hv : 0 ≤ v ∧ v < 2^(tbits l))
    (h0 : ((L-(R-c)*k-R*(v-offset l) : ℤ) : ZMod AffineRangeBounds.nativePrime) = 0)
    (h1 : ((H-(R-1)*k+(v-offset l) : ℤ) : ZMod AffineRangeBounds.nativePrime) = 0) :
    L+R*H=q*k := by
  have he0 : L-(R-c)*k-R*(v-offset l)=0 := by
    apply AffineRangeBounds.zero_of_native_zero h0
    all_goals cases l <;>
      norm_num [loMin, loMax, hiMin, hiMax, R, c, qbits, tbits, offset,
        AffineRangeBounds.nativePrime] at * <;> omega
  have he1 : H-(R-1)*k+(v-offset l)=0 := by
    apply AffineRangeBounds.zero_of_native_zero h1
    all_goals cases l <;>
      norm_num [loMin, loMax, hiMin, hiMax, R, c, qbits, tbits, offset,
        AffineRangeBounds.nativePrime] at * <;> omega
  have hq : q=R^2-c := by norm_num [q,R,c]
  rw [hq]
  linear_combination he0+R*he1

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

lemma digit_cast_val (l : Layout) (x : Emu Field) (i : Fin (count l)) :
    (((digit l x i : ℕ) : Field)).val = digit l x i := by
  apply ZMod.val_natCast_of_lt
  apply lt_trans (digit_lt l x i)
  cases l <;> decide

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
  simp only [main, circuit_norm, ToBitsAffine.toBitsAffine, ToBitsAffine.main_localLength]
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

def halfZ (v : Emu Field) (side : Bool) : ℤ :=
  if side then (v[2].val : ℤ) + 2^64*v[3].val else (v[0].val : ℤ) + 2^64*v[1].val
lemma half_bounds (v : Emu Field) (hv : BigInt.Normalized 64 v) (side : Bool) :
    0 ≤ halfZ v side ∧ halfZ v side ≤ R-1 := by
  have h0 : (v[0].val : ℤ) < 2^64 := by exact_mod_cast hv 0
  have h1 : (v[1].val : ℤ) < 2^64 := by exact_mod_cast hv 1
  have h2 : (v[2].val : ℤ) < 2^64 := by exact_mod_cast hv 2
  have h3 : (v[3].val : ℤ) < 2^64 := by exact_mod_cast hv 3
  cases side <;> simp only [halfZ, Bool.false_eq_true, ↓reduceIte] <;> norm_num only [R, Int.reducePow] <;> omega
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
  simp only [main,circuit_norm,ToBitsAffine.toBitsAffine,ToBitsAffine.main_localLength]
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

lemma value_halves (v : Emu Field) :
    halfZ v false+R*halfZ v true = (BigInt.value 64 v : ℤ) := by
  simp only [halfZ, Bool.false_eq_true, ↓reduceIte, BigInt.value_eq_sum,
    Fin.sum_univ_succ, Fin.sum_univ_zero, R]
  norm_num [Fin.succ]
  ring

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

def balancedDigits (raw : Emu Field) : Digits Field :=
  Vector.ofFn fun i => ((digitZ raw i : ℤ) : Field)

/-- A raw four-word slope together with its eight balanced native-field digits. -/
def SlopeRep (raw : Emu Field) (a : Digits Field) : Prop :=
  BigInt.Normalized 64 raw ∧
    ∀ i : Fin 8, a[i.val] = ((digitZ raw i : ℤ) : Field)

def digitsZ (a : Digits Field) : Words ℤ := fun i => LazyX.lift a[i.val]

def slopeValueZ (raw : Emu Field) : ℤ :=
  (BigInt.value 64 raw : ℤ) - kappa

def slopeValueFp (raw : Emu Field) : Specs.Secp256k1.Fp :=
  (slopeValueZ raw : Specs.Secp256k1.Fp)

def canonicalSlope (raw : Emu Field) : Emu Field :=
  emuOfNat (slopeValueFp raw).val

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

lemma balancedDigits_get (raw : Emu Field) (i : Fin 8) :
    (balancedDigits raw)[i.val] = ((digitZ raw i : ℤ) : Field) := by
  simp only [balancedDigits, Vector.getElem_ofFn]

lemma balancedDigits_rep (raw : Emu Field) (hraw : BigInt.Normalized 64 raw) :
    SlopeRep raw (balancedDigits raw) := by
  exact ⟨hraw, balancedDigits_get raw⟩

lemma SlopeRep.digit_cast {raw : Emu Field} {a : Digits Field}
    (ha : SlopeRep raw a) (i : Fin 8) :
    a[i.val] = ((digitZ raw i : ℤ) : Field) := ha.2 i

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

lemma canonicalSlope_normalized (raw : Emu Field) :
    BigInt.Normalized 64 (canonicalSlope raw) :=
  CompleteAdd.emuOfNat_normalized _

lemma canonicalSlope_decode (raw : Emu Field) :
    decodeFe (canonicalSlope raw) = slopeValueFp raw := by
  rw [canonicalSlope,
    CombTableBridge.decodeFe_emuOfNat (ZMod.val_lt (slopeValueFp raw))]
  exact ZMod.natCast_zmod_val _

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

lemma slopeWitness_rep (s : Specs.Secp256k1.Fp) :
    SlopeRep (slopeWitness s) (balancedDigits (slopeWitness s)) :=
  balancedDigits_rep _ (slopeWitness_normalized s)

lemma slopeWitness_canonical_decode (s : Specs.Secp256k1.Fp) :
    decodeFe (canonicalSlope (slopeWitness s)) = s := by
  rw [canonicalSlope_decode, slopeWitness_valueFp]

/-- The same balanced digits regrouped into four signed radix-`2^64` words. -/
def wordZ (raw : Emu Field) (j : Fin 4) : ℤ :=
  (raw[j.val].val : ℤ) - m * (1 + H)

def words64 (raw : Emu Field) : fields 4 Field :=
  Vector.ofFn fun j => ((wordZ raw j : ℤ) : Field)

def words64Z (w : fields 4 Field) : Fin 4 → ℤ := fun j => LazyX.lift w[j.val]

lemma wordZ_bounds (raw : Emu Field) (hraw : BigInt.Normalized 64 raw) (j : Fin 4) :
    -(m * (1 + H)) ≤ wordZ raw j ∧ wordZ raw j < m * (1 + H) := by
  have hj := hraw j
  simp only [Fin.getElem_fin] at hj
  simp only [wordZ, m, H]
  omega

lemma wordZ_native_bounds (raw : Emu Field) (hraw : BigInt.Normalized 64 raw)
    (j : Fin 4) :
    -LazyX.nativeHalf ≤ wordZ raw j ∧ wordZ raw j ≤ LazyX.nativeHalf := by
  have hj := wordZ_bounds raw hraw j
  simp only [m, H, LazyX.nativeHalf] at hj ⊢
  omega

lemma words64_lift (raw : Emu Field) (hraw : BigInt.Normalized 64 raw) (j : Fin 4) :
    LazyX.lift (words64 raw)[j.val] = wordZ raw j := by
  rw [words64, Vector.getElem_ofFn]
  exact LazyX.lift_cast _ (wordZ_native_bounds raw hraw j)

lemma words64Z_eq (raw : Emu Field) (hraw : BigInt.Normalized 64 raw) :
    words64Z (words64 raw) = wordZ raw := by
  funext j
  exact words64_lift raw hraw j

set_option maxHeartbeats 300000 in
lemma unsignedDigit_regroup (raw : Emu Field) (hraw : BigInt.Normalized 64 raw)
    (j : Fin 4) :
    (raw[j.val].val : ℤ) =
      (unsignedDigit raw ⟨2 * j.val, by omega⟩ : ℤ) +
        H * (unsignedDigit raw ⟨2 * j.val + 1, by omega⟩ : ℤ) := by
  have hj := SmallNormalize.word32 raw[j.val].val (by
    simpa only [Fin.getElem_fin] using hraw j)
  have hjz := congrArg (fun n : ℕ => (n : ℤ)) hj
  fin_cases j <;>
    simp only [unsignedDigit, SmallNormalize.digit, SmallNormalize.perWord,
      count, bits, H] at hjz ⊢ <;>
    norm_num at hjz ⊢ <;>
    exact hjz

lemma wordZ_regroup (raw : Emu Field) (hraw : BigInt.Normalized 64 raw) (j : Fin 4) :
    wordZ raw j =
      digitZ raw ⟨2 * j.val, by omega⟩ +
        H * digitZ raw ⟨2 * j.val + 1, by omega⟩ := by
  rw [wordZ, digitZ, digitZ, unsignedDigit_regroup raw hraw j]
  ring

lemma eval_words64 (raw : Emu Field) (hraw : BigInt.Normalized 64 raw) :
    (∑ j : Fin 4, wordZ raw j * (H ^ 2) ^ j.val) = slopeValueZ raw := by
  rw [← digit_reconstruct raw hraw]
  simp_rw [wordZ_regroup raw hraw]
  simp only [eval, Fin.sum_univ_succ, Fin.sum_univ_zero]
  norm_num [Fin.succ]
  ring

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

def squareLoTerm (i j : Fin 8) : ℤ := if i = j then 0 else -m * (m-1)
def squareHiTerm (_i _j : Fin 8) : ℤ := m * m

def SLO (k : Fin 8) : ℤ :=
  ∑ i : Fin 8, ∑ j : Fin 8, redCoeff i j k * squareLoTerm i j
def SHI (k : Fin 8) : ℤ :=
  ∑ i : Fin 8, ∑ j : Fin 8, redCoeff i j k * squareHiTerm i j

/-- State bounds before the first addition and after each update. -/
def stateBounds : ℕ → Words ℤ × Words ℤ
  | 0 => (fun _ => 0, dcap)
  | n+1 =>
      let p := stateBounds n
      (fun i => SLO i - p.2 i - dcap i, fun i => SHI i - p.1 i)

def lower (n : ℕ) : Words ℤ := (stateBounds n).1
def upper (n : ℕ) : Words ℤ := (stateBounds n).2

lemma state_step (n : ℕ) (i : Fin 8) :
    lower (n+1) i = SLO i-upper n i-dcap i ∧
    upper (n+1) i = SHI i-lower n i := ⟨rfl, rfl⟩

lemma dcap_nonneg (i : Fin 8) : 0 ≤ dcap i := by
  simp only [dcap]
  split_ifs <;> norm_num [wordMax, B64]

lemma embed_bounds (a : Fin 4 → ℤ) (ha : ∀ i, 0 ≤ a i ∧ a i ≤ wordMax)
    (i : Fin 8) : 0 ≤ embed a i ∧ embed a i ≤ dcap i := by
  simp only [embed, dcap]
  split_ifs
  · exact ha _
  · omega

private lemma balanced_square_bounds {a : ℤ} (ha : -m ≤ a ∧ a ≤ m-1) :
    0 ≤ a*a ∧ a*a ≤ m*m := by
  have hm : 0 ≤ m-a := by omega
  have hp : 0 ≤ m+a := by omega
  constructor
  · exact mul_self_nonneg a
  · nlinarith [mul_nonneg hm hp]

private lemma balanced_product_bounds {a b : ℤ}
    (ha : -m ≤ a ∧ a ≤ m-1) (hb : -m ≤ b ∧ b ≤ m-1) :
    -m*(m-1) ≤ a*b ∧ a*b ≤ m*m := by
  have hm : 0 ≤ m := by norm_num [m]
  have hu : 0 ≤ m-1 := by norm_num [m]
  by_cases ha0 : 0 ≤ a
  · by_cases hb0 : 0 ≤ b
    · have h1 := mul_nonneg (show 0 ≤ m-1-a by omega) hb0
      have h2 := mul_nonneg hu (show 0 ≤ m-1-b by omega)
      constructor <;> nlinarith
    · have hbneg : b ≤ 0 := by omega
      have h1 := mul_nonneg (show 0 ≤ m-1-a by omega) (show 0 ≤ -b by omega)
      have h2 := mul_nonneg hu (show 0 ≤ m+b by omega)
      constructor <;> nlinarith
  · have haneg : a ≤ 0 := by omega
    by_cases hb0 : 0 ≤ b
    · have h1 := mul_nonneg (show 0 ≤ m+a by omega) hb0
      have h2 := mul_nonneg (show 0 ≤ -a by omega) (show 0 ≤ m-1-b by omega)
      constructor <;> nlinarith
    · have hbneg : b ≤ 0 := by omega
      have h1 := mul_nonneg (show 0 ≤ m+a by omega) (show 0 ≤ -b by omega)
      have h2 := mul_nonneg hm (show 0 ≤ m+b by omega)
      constructor <;> nlinarith

lemma square_term_bounds (a : Words ℤ) (ha : ∀ i, -m ≤ a i ∧ a i ≤ m-1)
    (i j : Fin 8) :
    squareLoTerm i j ≤ a i*a j ∧ a i*a j ≤ squareHiTerm i j := by
  by_cases h : i = j
  · subst j
    simpa only [squareLoTerm, squareHiTerm, if_pos] using balanced_square_bounds (ha i)
  · simpa only [squareLoTerm, squareHiTerm, if_neg h] using
      balanced_product_bounds (ha i) (ha j)

lemma sparseSquare_bounds (a : Words ℤ) (ha : ∀ i, -m ≤ a i ∧ a i ≤ m-1)
    (k : Fin 8) : SLO k ≤ sparseSquare a k ∧ sparseSquare a k ≤ SHI k := by
  have ht (i j : Fin 8) := square_term_bounds a ha i j
  have hw (i j : Fin 8) : 0 ≤ redCoeff i j k := redCoeff_nonneg i j k
  constructor
  · exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_left (ht i j).1 (hw i j)
  · exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_left (ht i j).2 (hw i j)

alias square_bounds := sparseSquare_bounds

lemma update_bounds (n : ℕ) (a x : Words ℤ) (T : Fin 4 → ℤ)
    (ha : ∀ i, -m ≤ a i ∧ a i ≤ m-1)
    (hx : ∀ i, lower n i ≤ x i ∧ x i ≤ upper n i)
    (hT : ∀ i, 0 ≤ T i ∧ T i ≤ wordMax) (k : Fin 8) :
    lower (n+1) k ≤ sparseSquare a k-x k-embed T k ∧
      sparseSquare a k-x k-embed T k ≤ upper (n+1) k := by
  have hs := sparseSquare_bounds a ha k
  have ht := embed_bounds T hT k
  rw [(state_step n k).1, (state_step n k).2]
  have := hx k
  omega

/-- Minimum of all four products at the corners of
`[-m,m-1] × [l,u]`. -/
def rectLo (l u : ℤ) : ℤ :=
  min ((-m)*l) (min ((-m)*u) (min ((m-1)*l) ((m-1)*u)))

/-- Maximum of all four products at the corners of
`[-m,m-1] × [l,u]`. -/
def rectHi (l u : ℤ) : ℤ :=
  max ((-m)*l) (max ((-m)*u) (max ((m-1)*l) ((m-1)*u)))

private lemma rectLo_le_left (l u z : ℤ) (h : (-m)*l ≤ z) : rectLo l u ≤ z :=
  (min_le_left _ _).trans h
private lemma rectLo_le_right (l u z : ℤ) (h : (m-1)*u ≤ z) : rectLo l u ≤ z :=
  (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans h))
private lemma rectLo_le_negUpper (l u z : ℤ) (h : (-m)*u ≤ z) : rectLo l u ≤ z :=
  (min_le_right _ _).trans ((min_le_left _ _).trans h)
private lemma rectLo_le_posLower (l u z : ℤ) (h : (m-1)*l ≤ z) : rectLo l u ≤ z :=
  (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_left _ _).trans h))

private lemma le_rectHi_left (l u z : ℤ) (h : z ≤ (-m)*l) : z ≤ rectHi l u :=
  h.trans (le_max_left _ _)
private lemma le_rectHi_right (l u z : ℤ) (h : z ≤ (m-1)*u) : z ≤ rectHi l u := by
  calc
    z ≤ (m-1)*u := h
    _ ≤ max ((m-1)*l) ((m-1)*u) := le_max_right _ _
    _ ≤ max ((-m)*u) (max ((m-1)*l) ((m-1)*u)) := le_max_right _ _
    _ ≤ rectHi l u := le_max_right _ _
private lemma le_rectHi_negUpper (l u z : ℤ) (h : z ≤ (-m)*u) : z ≤ rectHi l u := by
  calc
    z ≤ (-m)*u := h
    _ ≤ max ((-m)*u) (max ((m-1)*l) ((m-1)*u)) := le_max_left _ _
    _ ≤ rectHi l u := le_max_right _ _
private lemma le_rectHi_posLower (l u z : ℤ) (h : z ≤ (m-1)*l) : z ≤ rectHi l u := by
  calc
    z ≤ (m-1)*l := h
    _ ≤ max ((m-1)*l) ((m-1)*u) := le_max_left _ _
    _ ≤ max ((-m)*u) (max ((m-1)*l) ((m-1)*u)) := le_max_right _ _
    _ ≤ rectHi l u := le_max_right _ _

/-- Bilinear extrema occur at rectangle corners. The proof uses the sign of each
factor and does not assume the slope is nonnegative. -/
lemma balanced_rect_bounds {a x l u : ℤ}
    (ha : -m ≤ a ∧ a ≤ m-1) (hx : l ≤ x ∧ x ≤ u)
    (hl : l ≤ 0) (hu : 0 ≤ u) : rectLo l u ≤ a*x ∧ a*x ≤ rectHi l u := by
  have hm : 0 ≤ m := by norm_num [m]
  have hp : 0 ≤ m-1 := by norm_num [m]
  by_cases ha0 : 0 ≤ a
  · by_cases hx0 : 0 ≤ x
    · constructor
      · apply rectLo_le_negUpper
        have : (-m)*u ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by omega) hu
        exact this.trans (mul_nonneg ha0 hx0)
      · apply le_rectHi_right
        calc
          a*x ≤ (m-1)*x := mul_le_mul_of_nonneg_right ha.2 hx0
          _ ≤ (m-1)*u := mul_le_mul_of_nonneg_left hx.2 hp
    · have hxneg : x ≤ 0 := by omega
      constructor
      · apply rectLo_le_posLower
        calc
          (m-1)*l ≤ a*l := mul_le_mul_of_nonpos_right ha.2 hl
          _ ≤ a*x := mul_le_mul_of_nonneg_left hx.1 ha0
      · apply le_rectHi_left
        have hax : a*x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha0 hxneg
        have hc : 0 ≤ (-m)*l := mul_nonneg_of_nonpos_of_nonpos (by omega) hl
        exact hax.trans hc
  · have haneg : a ≤ 0 := by omega
    by_cases hx0 : 0 ≤ x
    · constructor
      · apply rectLo_le_negUpper
        calc
          (-m)*u ≤ a*u := mul_le_mul_of_nonneg_right ha.1 hu
          _ ≤ a*x := mul_le_mul_of_nonpos_left hx.2 haneg
      · apply le_rectHi_right
        have hax : a*x ≤ 0 := mul_nonpos_of_nonpos_of_nonneg haneg hx0
        have hc : 0 ≤ (m-1)*u := mul_nonneg hp hu
        exact hax.trans hc
    · have hxneg : x ≤ 0 := by omega
      constructor
      · apply rectLo_le_negUpper
        have hc : (-m)*u ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by omega) hu
        exact hc.trans (mul_nonneg_of_nonpos_of_nonpos haneg hxneg)
      · apply le_rectHi_left
        calc
          a*x ≤ (-m)*x := mul_le_mul_of_nonpos_right ha.1 hxneg
          _ ≤ (-m)*l := mul_le_mul_of_nonpos_left hx.1 (by omega)

def wideTermLo (n : ℕ) (j : Fin 8) : ℤ :=
  rectLo (-upper n j) (dcap j-lower n j)
def wideTermHi (n : ℕ) (j : Fin 8) : ℤ :=
  rectHi (-upper n j) (dcap j-lower n j)

def productLower (n : ℕ) (k : Fin 8) : ℤ :=
  ∑ i : Fin 8, ∑ j : Fin 8, redCoeff i j k * wideTermLo n j
def productUpper (n : ℕ) (k : Fin 8) : ℤ :=
  ∑ i : Fin 8, ∑ j : Fin 8, redCoeff i j k * wideTermHi n j
def wideLower (n : ℕ) (k : Fin 8) : ℤ := 2 * productLower n k
def wideUpper (n : ℕ) (k : Fin 8) : ℤ := 2 * productUpper n k

def wideCoeff (a b x : Words ℤ) (A T : Fin 4 → ℤ) : Words ℤ :=
  fun k => sparseMul a (fun j => embed A j-x j) k +
    sparseMul b (fun j => embed T j-x j) k

lemma state_signs : ∀ n : Fin 23, ∀ i : Fin 8,
    lower n.val i ≤ 0 ∧ 0 ≤ upper n.val i := by decide

lemma product_bounds (n : Fin 23) (a x : Words ℤ) (A : Fin 4 → ℤ)
    (ha : ∀ i, -m ≤ a i ∧ a i ≤ m-1)
    (hx : ∀ i, lower n.val i ≤ x i ∧ x i ≤ upper n.val i)
    (hA : ∀ i, 0 ≤ A i ∧ A i ≤ wordMax) (k : Fin 8) :
    productLower n.val k ≤ sparseMul a (fun j => embed A j-x j) k ∧
      sparseMul a (fun j => embed A j-x j) k ≤ productUpper n.val k := by
  have ht (i j : Fin 8) :
      wideTermLo n.val j ≤ a i*(embed A j-x j) ∧
      a i*(embed A j-x j) ≤ wideTermHi n.val j := by
    apply balanced_rect_bounds (ha i)
    · have he := embed_bounds A hA j
      have hs := hx j
      omega
    · have hs := (state_signs n j).2
      omega
    · have he := embed_bounds A hA j
      have hs := (state_signs n j).1
      omega
  have hw (i j : Fin 8) : 0 ≤ redCoeff i j k := redCoeff_nonneg i j k
  constructor
  · exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_left (ht i j).1 (hw i j)
  · exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_left (ht i j).2 (hw i j)

lemma wide_bounds (n : Fin 23) (a b x : Words ℤ) (A T : Fin 4 → ℤ)
    (ha : ∀ i, -m ≤ a i ∧ a i ≤ m-1)
    (hb : ∀ i, -m ≤ b i ∧ b i ≤ m-1)
    (hx : ∀ i, lower n.val i ≤ x i ∧ x i ≤ upper n.val i)
    (hA : ∀ i, 0 ≤ A i ∧ A i ≤ wordMax)
    (hT : ∀ i, 0 ≤ T i ∧ T i ≤ wordMax) (k : Fin 8) :
    wideLower n.val k ≤ wideCoeff a b x A T k ∧
      wideCoeff a b x A T k ≤ wideUpper n.val k := by
  have ha' := product_bounds n a x A ha hx hA k
  have hb' := product_bounds n b x T hb hx hT k
  simp only [wideLower, wideUpper, wideCoeff]
  omega

lemma half_interval (f lo hi : Words ℤ)
    (hf : ∀ i, lo i ≤ f i ∧ f i ≤ hi i) :
    (lowHalf lo ≤ lowHalf f ∧ lowHalf f ≤ lowHalf hi) ∧
    (highHalf lo ≤ highHalf f ∧ highHalf f ≤ highHalf hi) := by
  simp only [lowHalf, highHalf, H]
  have h0 := hf 0; have h1 := hf 1; have h2 := hf 2; have h3 := hf 3
  have h4 := hf 4; have h5 := hf 5; have h6 := hf 6; have h7 := hf 7
  norm_num at *
  omega

/-- Every state coefficient through depth 22 has a unique centered native lift. -/
lemma state_centered : ∀ n : Fin 23, ∀ i : Fin 8,
    -nativeHalf < lower n.val i ∧ upper n.val i < nativeHalf := by decide

lemma bounds_centered (n : ℕ) (hn : n ≤ 22) (i : Fin 8) :
    -nativeHalf < lower n i ∧ upper n i < nativeHalf := by
  exact state_centered ⟨n, by omega⟩ i

/-- Every depth-1 through depth-21 wide coefficient has a unique centered lift. -/
lemma wide_centered : ∀ d : Fin 21, ∀ i : Fin 8,
    -nativeHalf < wideLower (d.val+1) i ∧ wideUpper (d.val+1) i < nativeHalf := by decide

/-- Coefficient caps for the two signed 64-bit endpoint products. -/
def endpointCap (i : Fin 4) : ℤ :=
  (i.val+1+c*(3-i.val)) * (m*(H+1)) * wordMax

def endpointSlopeMax : ℤ := m*(H+1)

def endpointWeight (i j k : Fin 4) : ℤ :=
  if i.val+j.val < 4 then (if i.val+j.val=k.val then 1 else 0)
  else if i.val+j.val-4=k.val then c else 0

def endpointCoeff (a b : Fin 4 → ℤ) (k : Fin 4) : ℤ :=
  ∑ i : Fin 4, ∑ j : Fin 4, endpointWeight i j k*(a i*b j)

def endpointLow (z : Fin 4 → ℤ) : ℤ := z 0+B64*z 1
def endpointHigh (z : Fin 4 → ℤ) : ℤ := z 2+B64*z 3

def endpointLowCap : ℤ := endpointCap 0+B64*endpointCap 1
def endpointHighCap : ℤ := endpointCap 2+B64*endpointCap 3

lemma endpointCap_nonneg (i : Fin 4) : 0 ≤ endpointCap i := by
  fin_cases i <;> norm_num [endpointCap, c, m, H, wordMax, B64]

private lemma endpointWeight_nonneg (i j k : Fin 4) : 0 ≤ endpointWeight i j k := by
  simp only [endpointWeight]
  split_ifs <;> norm_num [c]

private lemma endpointWeight_sum (k : Fin 4) :
    (∑ i : Fin 4, ∑ j : Fin 4, endpointWeight i j k) =
      k.val+1+c*(3-k.val) := by
  fin_cases k <;> decide

lemma endpointCoeff_bounds (a b : Fin 4 → ℤ)
    (ha : ∀ i, -endpointSlopeMax ≤ a i ∧ a i ≤ endpointSlopeMax)
    (hb : ∀ i, -wordMax ≤ b i ∧ b i ≤ wordMax) (k : Fin 4) :
    -endpointCap k ≤ endpointCoeff a b k ∧ endpointCoeff a b k ≤ endpointCap k := by
  have hM : 0 ≤ endpointSlopeMax := by norm_num [endpointSlopeMax, m, H]
  have hD : 0 ≤ wordMax := by norm_num [wordMax, B64]
  have ht (i j : Fin 4) :
      -(endpointSlopeMax*wordMax) ≤ a i*b j ∧
        a i*b j ≤ endpointSlopeMax*wordMax := by
    have hai : |a i| ≤ endpointSlopeMax := (abs_le).2 (ha i)
    have hbj : |b j| ≤ wordMax := (abs_le).2 (hb j)
    have hp : |a i*b j| ≤ endpointSlopeMax*wordMax := by
      rw [abs_mul]
      exact mul_le_mul hai hbj (abs_nonneg _) hM
    exact (abs_le).1 hp
  have hw (i j : Fin 4) := endpointWeight_nonneg i j k
  have hcap : endpointCap k =
      ∑ i : Fin 4, ∑ j : Fin 4,
        endpointWeight i j k*(endpointSlopeMax*wordMax) := by
    fin_cases k <;> decide
  constructor
  · rw [hcap, endpointCoeff]
    calc
      -(∑ i : Fin 4, ∑ j : Fin 4,
          endpointWeight i j k*(endpointSlopeMax*wordMax)) =
          ∑ i : Fin 4, ∑ j : Fin 4,
            -(endpointWeight i j k*(endpointSlopeMax*wordMax)) := by simp
      _ ≤ ∑ i : Fin 4, ∑ j : Fin 4, endpointWeight i j k*(a i*b j) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
          have h := mul_le_mul_of_nonneg_left (ht i j).1 (hw i j)
          simpa only [mul_neg] using h
  · rw [hcap, endpointCoeff]
    exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_left (ht i j).2 (hw i j)

lemma endpoint_half_interval (z : Fin 4 → ℤ)
    (hz : ∀ i, -endpointCap i ≤ z i ∧ z i ≤ endpointCap i) :
    (-endpointLowCap ≤ endpointLow z ∧ endpointLow z ≤ endpointLowCap) ∧
    (-endpointHighCap ≤ endpointHigh z ∧ endpointHigh z ≤ endpointHighCap) := by
  have h0 := hz 0; have h1 := hz 1; have h2 := hz 2; have h3 := hz 3
  norm_num [endpointLowCap, endpointHighCap, endpointLow, endpointHigh, B64]
  omega

end Solution.Secp256k1ScalarMulFixedBase.Sparse32
end

/- === PackedState === -/
section
namespace Solution.Secp256k1ScalarMulFixedBase.Packed
open Challenge.CostR1CS Cost

structure State (F : Type) where
  x : Emu F
  lam : Emu F
  T : Point F
deriving ProvableStruct

def state (s : State Field) : Chain.ChainState Field := { x := s.x, lam := s.lam, T := s.T.point }
def stateExpr (s : Var State Field) : Var Chain.ChainState Field := { x := s.x, lam := s.lam, T := s.T.point }
@[simp] theorem eval_stateExpr (env : Environment Field) (s : Var State Field) :
    eval env (stateExpr s) = state (eval env s) := by simp only [stateExpr,state,circuit_norm]

def AffineState (s : Var State Field) : Prop := AffineW s.x ∧ AffineW s.lam ∧ AffinePoint s.T

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
def XBound (n : ℕ) (x : Coeffs Field) : Prop :=
  ∀ i, Sparse32.lower n i ≤ zwords x i ∧ zwords x i ≤ Sparse32.upper n i

def valueZ (x : Coeffs Field) : ℤ := Sparse32.eval (zwords x) Sparse32.H
def valueFp (x : Coeffs Field) : Specs.Secp256k1.Fp := (valueZ x : Specs.Secp256k1.Fp)
def canonical (x : Coeffs Field) : Emu Field := emuOfNat (valueFp x).val

lemma canonical_normalized (x : Coeffs Field) : BigInt.Normalized 64 (canonical x) :=
  CompleteAdd.emuOfNat_normalized _

lemma canonical_decode (x : Coeffs Field) : decodeFe (canonical x) = valueFp x := by
  rw [canonical, CombTableBridge.decodeFe_emuOfNat (ZMod.val_lt (valueFp x))]
  exact ZMod.natCast_zmod_val _

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

lemma embed_bound (x : Emu Field) (hx : BigInt.Normalized 64 x) : XBound 0 (embedVec x) := by
  rw [XBound, embed_zwords x hx]
  intro i
  exact Sparse32.embed_bounds (emuz x) (emuz_bounds x hx) i

lemma embed_decode (x : Emu Field) (hx : BigInt.Normalized 64 x) :
    valueFp (embedVec x) = decodeFe x := by
  unfold valueFp valueZ
  rw [embed_zwords x hx, embed_value]
  rfl

def squareVec (a : Coeffs Field) : Coeffs Field :=
  Vector.ofFn fun k => Sparse32.sparseSquare (fun i => a[i.val]) k

def update (s x : Coeffs Field) (T : Emu Field) : Coeffs Field :=
  Vector.ofFn fun k => s[k.val] - x[k.val] - (embedVec T)[k.val]
def updateExpr (s x : Var (fields 8) Field) (T : Var Emu Field) : Var (fields 8) Field :=
  Vector.ofFn fun k => s[k.val] - x[k.val] - (embedExpr T)[k.val]

lemma eval_updateExpr (env : Environment Field) (s x : Var (fields 8) Field)
    (T : Var Emu Field) :
    eval env (updateExpr s x T) = update (eval env s) (eval env x) (eval env T) := by
  have ht := eval_embedExpr env T
  apply Vector.ext
  intro i hi
  have hti := congrArg (fun v : fields 8 Field => v[i]) ht
  simp only [circuit_norm, Vector.getElem_map] at hti
  simp only [updateExpr, update, circuit_norm, Vector.getElem_ofFn, Expression.eval,
    hti, neg_one_mul, sub_eq_add_neg]

lemma affine_update (s x : Var (fields 8) Field) (T : Var Emu Field)
    (hs : AffineW s) (hx : AffineW x) (ht : AffineW T) : AffineW (updateExpr s x T) := by
  intro i hi
  rw [updateExpr, Vector.getElem_ofFn]
  exact Affine.sub (Affine.sub (hs i hi) (hx i hi)) (affine_embedExpr T ht i hi)

lemma square_cast (a : Coeffs Field) (k : Fin 8) :
    (squareVec a)[k.val] = ((Sparse32.sparseSquare (Sparse32.digitsZ a) k : ℤ) : Field) := by
  rw [squareVec, Vector.getElem_ofFn]
  simpa only [Sparse32.sparseSquare, Int.coe_castRingHom, Sparse32.digitsZ,
    LazyX.cast_lift, Fin.eta] using
    Sparse32.sparseMul_map (Int.castRingHom Field) (Sparse32.digitsZ a) (Sparse32.digitsZ a) k

lemma slope_digits (raw : Emu Field) (a : Coeffs Field) (ha : Sparse32.SlopeRep raw a) :
    ∀ i, -Sparse32.m ≤ Sparse32.digitsZ a i ∧ Sparse32.digitsZ a i ≤ Sparse32.m - 1 := by
  intro i
  rw [ha.digitsZ_eq]
  have h := Sparse32.digitZ_bounds raw i
  omega

lemma update_model (n : Fin 22) (s a x : Coeffs Field) (T raw : Emu Field)
    (hx : XBound n.val x) (ha : Sparse32.SlopeRep raw a) (hT : BigInt.Normalized 64 T)
    (hs : s = squareVec a) :
    XBound (n.val + 1) (update s x T) ∧
    zwords (update s x T) =
      (fun k => Sparse32.sparseSquare (Sparse32.digitsZ a) k - zwords x k - Sparse32.embed (emuz T) k) := by
  have hb (i : Fin 8) := Sparse32.update_bounds n.val (Sparse32.digitsZ a) (zwords x)
    (emuz T) (slope_digits raw a ha) hx (emuz_bounds T hT) i
  have he (k : Fin 8) : (update s x T)[k.val] =
      ((Sparse32.sparseSquare (Sparse32.digitsZ a) k-zwords x k-Sparse32.embed (emuz T) k : ℤ) : Field) := by
    subst s
    rw [update, Vector.getElem_ofFn, square_cast]
    simp only [Int.cast_sub, zwords, LazyX.cast_lift, Sparse32.embed, embedVec,
      Vector.getElem_ofFn, emuz, Int.cast_natCast, FoldQuot.natCast_val_F]
    split_ifs <;> simp only [Int.cast_zero, Int.cast_natCast, FoldQuot.natCast_val_F]
  have hz (k : Fin 8) : zwords (update s x T) k =
      Sparse32.sparseSquare (Sparse32.digitsZ a) k-zwords x k-Sparse32.embed (emuz T) k := by
    change LazyX.lift ((update s x T)[k.val]) = _
    rw [he]
    apply LazyX.lift_cast
    have hl := Sparse32.bounds_centered (n.val+1) (by omega) k
    have hk := hb k
    change -LazyX.nativeHalf ≤ _ ∧ _ ≤ LazyX.nativeHalf
    change -LazyX.nativeHalf < Sparse32.lower (n.val+1) k ∧
      Sparse32.upper (n.val+1) k < LazyX.nativeHalf at hl
    omega
  refine ⟨?_, funext hz⟩
  intro i
  rw [hz]
  exact hb i

lemma eval_sub {K : Type*} [CommRing K] (a b : Sparse32.Words K) (r : K) :
    Sparse32.eval (fun i => a i-b i) r = Sparse32.eval a r-Sparse32.eval b r := by
  simp only [Sparse32.eval, sub_mul, Finset.sum_sub_distrib]

lemma eval_cast (a : Sparse32.Words ℤ) :
    ((Sparse32.eval a Sparse32.H : ℤ) : Specs.Secp256k1.Fp) =
      Sparse32.eval (fun i => (a i : Specs.Secp256k1.Fp)) (Sparse32.H : Specs.Secp256k1.Fp) := by
  simp only [Sparse32.eval, Int.cast_sum, Int.cast_mul, Int.cast_pow]

lemma curve_root : (Sparse32.H : Specs.Secp256k1.Fp)^8 =
    (Sparse32.H : Specs.Secp256k1.Fp) + 977 := by decide

lemma update_semantics (n : Fin 22) (s a x : Coeffs Field) (T raw : Emu Field)
    (hx : XBound n.val x) (ha : Sparse32.SlopeRep raw a) (hT : BigInt.Normalized 64 T)
    (hs : s = squareVec a) :
    XBound (n.val+1) (update s x T) ∧
    valueFp (update s x T) = Sparse32.slopeValueFp raw^2-valueFp x-decodeFe T := by
  have hm := update_model n s a x T raw hx ha hT hs
  refine ⟨hm.1, ?_⟩
  unfold valueFp valueZ
  rw [hm.2, eval_sub, eval_sub, embed_value]
  push_cast
  rw [eval_cast]
  have hcast := Sparse32.sparseMul_map (Int.castRingHom Specs.Secp256k1.Fp)
    (Sparse32.digitsZ a) (Sparse32.digitsZ a)
  simp only [Int.coe_castRingHom] at hcast
  simp only [Sparse32.sparseSquare, ← hcast]
  rw [Sparse32.eval_sparseMul _ _ _ curve_root, ha.reconstructFp]
  simp only [pow_two, decodeFe, limbBits, Int.cast_natCast]

lemma dvd_q_iff (z : ℤ) : Sparse32.q ∣ z ↔ (z : Specs.Secp256k1.Fp) = 0 := by
  have hq : Sparse32.q = (Specs.Secp256k1.p : ℤ) := by decide
  rw [hq]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).symm

structure XL (F : Type) where
  x : fields 8 F
  lam : Emu F
  small : fields 8 F
deriving ProvableStruct

structure State (F : Type) where
  x : fields 8 F
  lam : Emu F
  small : fields 8 F
  T : Packed.Point F
deriving ProvableStruct

def xl (s : XL Field) : Chain.ChainXL Field :=
  ⟨canonical s.x, Sparse32.canonicalSlope s.lam⟩
def state (s : State Field) : Chain.ChainState Field :=
  ⟨canonical s.x, Sparse32.canonicalSlope s.lam, s.T.point⟩
def Bounded (n : ℕ) (s : XL Field) : Prop := XBound n s.x ∧ Sparse32.SlopeRep s.lam s.small
def AffineXL (s : Var XL Field) : Prop := AffineW s.x ∧ AffineW s.lam ∧ AffineW s.small
def AffineState (s : Var State Field) : Prop :=
  AffineW s.x ∧ AffineW s.lam ∧ AffineW s.small ∧ Packed.AffinePoint s.T

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

inductive CertLayout where
  | start
  | wide (d : Fin 21)
  | finalX
  | finalY
  deriving DecidableEq

def loMin : CertLayout → ℤ
  | .start => -endpointLowCap-(R-1)
  | .wide d => lowHalf (wideLower (d.val+1))-2*(R-1)
  | .finalX => lowHalf (fun i => lower 22 i-dcap i)
  | .finalY => -endpointLowCap-2*(R-1)

def loMax : CertLayout → ℤ
  | .start => endpointLowCap+(R-1)
  | .wide d => lowHalf (wideUpper (d.val+1))
  | .finalX => lowHalf (upper 22)
  | .finalY => endpointLowCap

def hiMin : CertLayout → ℤ
  | .start => -endpointHighCap-(R-1)
  | .wide d => highHalf (wideLower (d.val+1))-2*(R-1)
  | .finalX => highHalf (fun i => lower 22 i-dcap i)
  | .finalY => -endpointHighCap-2*(R-1)

def hiMax : CertLayout → ℤ
  | .start => endpointHighCap+(R-1)
  | .wide d => highHalf (wideUpper (d.val+1))
  | .finalX => highHalf (upper 22)
  | .finalY => endpointHighCap

def qbits : CertLayout → ℕ
  | .start | .finalY => 67
  | .finalX => 39
  | .wide d =>
      if d.val = 0 then 78 else if d.val = 1 then 79 else
      if d.val ≤ 4 then 80 else if d.val ≤ 9 then 81 else
      if d.val ≤ 19 then 82 else 83

def tbits : CertLayout → ℕ
  | .start | .finalY => 98
  | .finalX => 48
  | .wide d =>
      if d.val = 0 then 86 else if d.val ≤ 2 then 87 else
      if d.val ≤ 5 then 88 else if d.val ≤ 12 then 89 else 90

private def wideKmin : Fin 21 → ℤ := ![
  -126493935780483616180577, -235071471440430863991965,
  -361491620135168842866721, -470069155904545414940007,
  -596489304489854069552866, -705066840368659965888049,
  -831486988844539296239010, -940064524832774516836091,
  -1066484673199224522925155, -1175062209296889067784133,
  -1301482357553909749611299, -1410059893761003618732175,
  -1536480041908594976297444, -1645057578225118169680217,
  -1771477726263280202983588, -1880055262689232720628259,
  -2006475410617965429669733, -2115052947153347271576301,
  -2241473094972650656355877, -2350050631617461822524343,
  -2476470779327335883042022]

private def wideKmax : Fin 21 → ℤ := ![
  126493935839386945180166, 235071471440430863991963,
  361491620303501496128208, 470069155904545414940005,
  596489304767616047076250, 705066840368659965888047,
  831486989231730598024292, 940064524832774516836089,
  1066484673695845148972334, 1175062209296889067784131,
  1301482358159959699920376, 1410059893761003618732173,
  1536480042624074250868418, 1645057578225118169680215,
  1771477727088188801816460, 1880055262689232720628257,
  2006475411552303352764502, 2115052947153347271576299,
  2241473096016417903712544, 2350050631617461822524341,
  2476470780480532454660586]

private def wideTmin : Fin 21 → ℤ := ![
  -26845140820029072521387083, -44904540174066108561356443,
  -71713488461430104419219246, -89772887836251163666670995,
  -116581836102831136317051409, -134641235498436218771985546,
  -161450183744232168214883572, -179509583160621273877300098,
  -206318531385633200112715735, -224377930822806328982614649,
  -251186879027034232010547898, -269246278484991384087929201,
  -296055226668435263908380061, -314114626147176439193243752,
  -340923574309836295806212224, -358982973809361494298558304,
  -385791921951237327704044387, -403851321471546549403872855,
  -430660269592638359601876550, -448719669133731604509187407,
  -475528617234039391499708713]

private def wideTmax : Fin 21 → ℤ := ![
  26845140832412008701393861, 44904540174066108561356443,
  71713488494487634482446514, 89772887836251163666670995,
  116581836156563260263499169, 134641235498436218771985546,
  161450183818638886044551822, 179509583160621273877300098,
  206318531480714511825604477, 224377930822806328982614649,
  251186879142790137606657130, 269246278484991384087929201,
  296055226804865763387709785, 314114626147176439193243752,
  340923574466941389168762438, 358982973809361494298558304,
  385791922129017014949815093, 403851321471546549403872855,
  430660269791092640730867746, 448719669133731604509187407,
  475528617453168266511920401]

def kmin : CertLayout → ℤ
  | .start => -36893488158156521961
  | .wide d => wideKmin d
  | .finalX => -200789723789
  | .finalY => -36893488158156521962

private def kmax : CertLayout → ℤ
  | .start => 36893488158156521961
  | .wide d => wideKmax d
  | .finalX => 200789723789
  | .finalY => 36893488158156521960

def tmin : CertLayout → ℤ
  | .start | .finalY => -79228180610520278115977003986
  | .wide d => wideTmin d
  | .finalX => -92717606507802

private def tmax : CertLayout → ℤ
  | .start | .finalY => 79228180610520278115977003986
  | .wide d => wideTmax d
  | .finalX => 92717606507802

private lemma honest_parameter_bounds : ∀ l : CertLayout,
    q*(kmin l-1) < loMin l+R*hiMin l ∧
    loMax l+R*hiMax l < q*(kmax l+1) ∧
    kmax l-kmin l < 2^(qbits l) ∧
    R*(tmin l-1) < loMin l-(R-c)*kmax l ∧
    loMax l-(R-c)*kmin l < R*(tmax l+1) ∧
    tmax l-tmin l < 2^(tbits l) := by
  intro l
  cases l with
  | start => decide
  | finalX => decide
  | finalY => decide
  | wide d => fin_cases d <;> decide

lemma bit_schedule :
    qbits .start=67 ∧ tbits .start=98 ∧
    qbits .finalX=39 ∧ tbits .finalX=48 ∧
    qbits .finalY=67 ∧ tbits .finalY=98 ∧
    (∀ d : Fin 21, 78 ≤ qbits (.wide d) ∧ qbits (.wide d) ≤ 83 ∧
      86 ≤ tbits (.wide d) ∧ tbits (.wide d) ≤ 90) := by
  constructor
  · decide
  constructor
  · decide
  constructor
  · decide
  constructor
  · decide
  constructor
  · decide
  constructor
  · decide
  intro d
  fin_cases d <;> decide

lemma certificate_complete (l : CertLayout) (L U k : ℤ)
    (hL : loMin l ≤ L ∧ L ≤ loMax l)
    (hU : hiMin l ≤ U ∧ U ≤ hiMax l)
    (he : L+R*U=q*k) :
    (0 ≤ k-kmin l ∧ k-kmin l < 2^(qbits l)) ∧
    (0 ≤ (R-1)*k-U-tmin l ∧
      (R-1)*k-U-tmin l < 2^(tbits l)) := by
  have hp := honest_parameter_bounds l
  norm_num [q, R, c] at hp he ⊢
  omega

def residualLo (l : CertLayout) (L kr vr : ℤ) : ℤ :=
  L-(R-c)*(kr+kmin l)-R*(vr+tmin l)

def residualHi (l : CertLayout) (U kr vr : ℤ) : ℤ :=
  U-(R-1)*(kr+kmin l)+(vr+tmin l)

private lemma admitted_extrema : ∀ l : CertLayout,
    -(2^227 : ℤ) < loMin l-(R-c)*(kmin l+2^(qbits l)-1)-
        R*(tmin l+2^(tbits l)-1) ∧
    loMax l-(R-c)*kmin l-R*tmin l < 2^227 ∧
    -(2^227 : ℤ) < hiMin l-(R-1)*(kmin l+2^(qbits l)-1)+tmin l ∧
    hiMax l-(R-1)*kmin l+(tmin l+2^(tbits l)-1) < 2^227 := by
  intro l
  cases l with
  | start => decide
  | finalX => decide
  | finalY => decide
  | wide d => fin_cases d <;> decide

/-- The largest admitted residual envelope is strictly below 227 bits. -/
lemma certificate_residual_bounds (l : CertLayout) (L U kr vr : ℤ)
    (hL : loMin l ≤ L ∧ L ≤ loMax l)
    (hU : hiMin l ≤ U ∧ U ≤ hiMax l)
    (hk : 0 ≤ kr ∧ kr < 2^(qbits l))
    (hv : 0 ≤ vr ∧ vr < 2^(tbits l)) :
    (-(2^227 : ℤ) < residualLo l L kr vr ∧ residualLo l L kr vr < 2^227) ∧
    (-(2^227 : ℤ) < residualHi l U kr vr ∧ residualHi l U kr vr < 2^227) := by
  have he := admitted_extrema l
  simp only [residualLo, residualHi]
  norm_num [R, c] at he ⊢
  omega

lemma certificate_no_wrap (l : CertLayout) (L U kr vr : ℤ)
    (hL : loMin l ≤ L ∧ L ≤ loMax l)
    (hU : hiMin l ≤ U ∧ U ≤ hiMax l)
    (hk : 0 ≤ kr ∧ kr < 2^(qbits l))
    (hv : 0 ≤ vr ∧ vr < 2^(tbits l)) :
    (-(nativePrime : ℤ) < residualLo l L kr vr ∧
      residualLo l L kr vr < nativePrime) ∧
    (-(nativePrime : ℤ) < residualHi l U kr vr ∧
      residualHi l U kr vr < nativePrime) := by
  have h := certificate_residual_bounds l L U kr vr hL hU hk hv
  norm_num [nativePrime] at h ⊢
  omega

lemma endpoints_centered (l : CertLayout) :
    -nativeHalf < loMin l ∧ loMax l < nativeHalf ∧
      -nativeHalf < hiMin l ∧ hiMax l < nativeHalf := by
  cases l with
  | start => decide
  | finalX => decide
  | finalY => decide
  | wide d => fin_cases d <;> decide

lemma certificate_sound (l : CertLayout) (L U kr vr : ℤ)
    (hL : loMin l ≤ L ∧ L ≤ loMax l)
    (hU : hiMin l ≤ U ∧ U ≤ hiMax l)
    (hk : 0 ≤ kr ∧ kr < 2^(qbits l))
    (hv : 0 ≤ vr ∧ vr < 2^(tbits l))
    (h0 : ((residualLo l L kr vr : ℤ) : ZMod nativePrime)=0)
    (h1 : ((residualHi l U kr vr : ℤ) : ZMod nativePrime)=0) :
    L+R*U=q*(kr+kmin l) := by
  have hb := certificate_no_wrap l L U kr vr hL hU hk hv
  have he0 : residualLo l L kr vr=0 :=
    AffineRangeBounds.zero_of_native_zero h0 hb.1.1 hb.1.2
  have he1 : residualHi l U kr vr=0 :=
    AffineRangeBounds.zero_of_native_zero h1 hb.2.1 hb.2.2
  rw [q_eq_R2_sub_c]
  simp only [residualLo, residualHi] at he0 he1
  linear_combination he0+R*he1

lemma wide_half_bounds (d : Fin 21) (z : Words ℤ)
    (hz : ∀ i, wideLower (d.val+1) i ≤ z i ∧ z i ≤ wideUpper (d.val+1) i) :
    (loMin (.wide d) ≤ lowHalf z-2*(R-1) ∧
      lowHalf z-2*(R-1) ≤ loMax (.wide d)) ∧
    (hiMin (.wide d) ≤ highHalf z-2*(R-1) ∧
      highHalf z-2*(R-1) ≤ hiMax (.wide d)) := by
  have h := half_interval z (wideLower (d.val+1)) (wideUpper (d.val+1)) hz
  have hR : 1 ≤ R := by norm_num [R]
  simp only [loMin, loMax, hiMin, hiMax]
  omega

lemma finalX_half_bounds (z : Words ℤ)
    (hz : ∀ i, lower 22 i-dcap i ≤ z i ∧ z i ≤ upper 22 i) :
    (loMin .finalX ≤ lowHalf z ∧ lowHalf z ≤ loMax .finalX) ∧
    (hiMin .finalX ≤ highHalf z ∧ highHalf z ≤ hiMax .finalX) := by
  simpa only [loMin, loMax, hiMin, hiMax] using
    half_interval z (fun i => lower 22 i-dcap i) (upper 22) hz

lemma start_half_bounds (z : Fin 4 → ℤ)
    (hz : ∀ i, -endpointCap i ≤ z i ∧ z i ≤ endpointCap i)
    (tl th : ℤ) (htl : -(R-1) ≤ tl ∧ tl ≤ R-1)
    (hth : -(R-1) ≤ th ∧ th ≤ R-1) :
    (loMin .start ≤ endpointLow z+tl ∧ endpointLow z+tl ≤ loMax .start) ∧
    (hiMin .start ≤ endpointHigh z+th ∧ endpointHigh z+th ≤ hiMax .start) := by
  have h := endpoint_half_interval z hz
  have hR : 1 ≤ R := by norm_num [R]
  simp only [loMin, loMax, hiMin, hiMax]
  omega

lemma finalY_half_bounds (z : Fin 4 → ℤ)
    (hz : ∀ i, -endpointCap i ≤ z i ∧ z i ≤ endpointCap i)
    (tl th : ℤ) (htl : 0 ≤ tl ∧ tl ≤ 2*(R-1))
    (hth : 0 ≤ th ∧ th ≤ 2*(R-1)) :
    (loMin .finalY ≤ endpointLow z-tl ∧ endpointLow z-tl ≤ loMax .finalY) ∧
    (hiMin .finalY ≤ endpointHigh z-th ∧ endpointHigh z-th ≤ hiMax .finalY) := by
  have h := endpoint_half_interval z hz
  have hR : 1 ≤ R := by norm_num [R]
  simp only [loMin, loMax, hiMin, hiMax]
  omega

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

private lemma qbits_valid (l : CertLayout) : 2 ^ qbits l < circomPrime := by
  cases l with
  | start => norm_num [qbits, Challenge.Instances.Secp256k1ScalarMul.Interface.circomPrime]
  | finalX => norm_num [qbits, Challenge.Instances.Secp256k1ScalarMul.Interface.circomPrime]
  | finalY => norm_num [qbits, Challenge.Instances.Secp256k1ScalarMul.Interface.circomPrime]
  | wide d => fin_cases d <;>
      norm_num [qbits, Challenge.Instances.Secp256k1ScalarMul.Interface.circomPrime]

private lemma qbits_pos (l : CertLayout) : 1 ≤ qbits l := by
  cases l with
  | start => norm_num [qbits]
  | finalX => norm_num [qbits]
  | finalY => norm_num [qbits]
  | wide d => fin_cases d <;> norm_num [qbits]

private lemma tbits_valid (l : CertLayout) : 2 ^ tbits l < circomPrime := by
  cases l with
  | start => norm_num [tbits, Challenge.Instances.Secp256k1ScalarMul.Interface.circomPrime]
  | finalX => norm_num [tbits, Challenge.Instances.Secp256k1ScalarMul.Interface.circomPrime]
  | finalY => norm_num [tbits, Challenge.Instances.Secp256k1ScalarMul.Interface.circomPrime]
  | wide d => fin_cases d <;>
      norm_num [tbits, Challenge.Instances.Secp256k1ScalarMul.Interface.circomPrime]

private lemma tbits_pos (l : CertLayout) : 1 ≤ tbits l := by
  cases l with
  | start => norm_num [tbits]
  | finalX => norm_num [tbits]
  | finalY => norm_num [tbits]
  | wide d => fin_cases d <;> norm_num [tbits]

def Assumptions (l : CertLayout) (i : fields 2 Field) : Prop :=
  (loMin l ≤ LazyX.lift (i[0]'(by decide)) ∧ LazyX.lift (i[0]'(by decide)) ≤ loMax l) ∧
  (hiMin l ≤ LazyX.lift (i[1]'(by decide)) ∧ LazyX.lift (i[1]'(by decide)) ≤ hiMax l)

def Spec (i : fields 2 Field) : Prop :=
  q ∣ LazyX.lift (i[0]'(by decide)) + R * LazyX.lift (i[1]'(by decide))

def rawQ (i : fields 2 Field) : Field :=
  (q : Field)⁻¹ * ((i[0]'(by decide)) + (R : Field) * (i[1]'(by decide)))
def qValue (l : CertLayout) (i : fields 2 Field) : Field := rawQ i - (kmin l : Field)
def vValue (l : CertLayout) (i : fields 2 Field) : Field :=
  (R : Field)⁻¹ * ((i[0]'(by decide)) - ((R-c : ℤ) : Field) * rawQ i) - (tmin l : Field)

def rawQExpr (i : Var (fields 2) Field) : Expression Field :=
  (q : Field)⁻¹ * ((i[0]'(by decide)) + (R : Field) * (i[1]'(by decide)))
def qExpr (l : CertLayout) (i : Var (fields 2) Field) : Expression Field :=
  rawQExpr i - (kmin l : Field)
def vExpr (l : CertLayout) (i : Var (fields 2) Field) : Expression Field :=
  (R : Field)⁻¹ * ((i[0]'(by decide)) - ((R-c : ℤ) : Field) * rawQExpr i) -
    (tmin l : Field)

def main (l : CertLayout) (i : Var (fields 2) Field) : Circuit Field Unit := do
  assertion (RangeCheck.circuit (qbits l) (qbits_valid l) (qbits_pos l)) (qExpr l i)
  assertion (RangeCheck.circuit (tbits l) (tbits_valid l) (tbits_pos l)) (vExpr l i)

instance elaborated (l : CertLayout) : ElaboratedCircuit Field (fields 2) unit (main l) := by
  elaborate_circuit

lemma values_sound (l : CertLayout) (i : fields 2 Field) (h : Assumptions l i)
    (hk : (qValue l i).val < 2 ^ qbits l) (hv : (vValue l i).val < 2 ^ tbits l) :
    Spec i := by
  have hn :
      (i[0]'(by decide)) - ((R-c : ℤ) : Field) * rawQ i -
          (R : Field) * ((R : Field)⁻¹ *
            ((i[0]'(by decide)) - ((R-c : ℤ) : Field) * rawQ i)) = 0 ∧
        (i[1]'(by decide)) - ((R-1 : ℤ) : Field) * rawQ i +
          (R : Field)⁻¹ *
            ((i[0]'(by decide)) - ((R-c : ℤ) : Field) * rawQ i) = 0 := by
    simpa only [rawQ, Sparse32.q, Sparse32.R, Sparse32.c,
      SmallSquare.q, SmallSquare.R, SmallSquare.c] using
        SmallCert.native (i[0]'(by decide)) (i[1]'(by decide))
  simp only [rawQ] at hn
  have h0 :
      ((LazyX.lift (i[0]'(by decide)) - (R-c) * ((qValue l i).val + kmin l) -
        R * ((vValue l i).val + tmin l) : ℤ) : Field) = 0 := by
    push_cast
    simp only [LazyX.cast_lift, FoldQuot.natCast_val_F, qValue, vValue, rawQ]
    push_cast at hn ⊢
    linear_combination hn.1
  have h1 :
      ((LazyX.lift (i[1]'(by decide)) - (R-1) * ((qValue l i).val + kmin l) +
        ((vValue l i).val + tmin l) : ℤ) : Field) = 0 := by
    push_cast
    simp only [LazyX.cast_lift, FoldQuot.natCast_val_F, qValue, vValue, rawQ]
    push_cast at hn ⊢
    linear_combination hn.2
  have he := certificate_sound l
    (LazyX.lift (i[0]'(by decide))) (LazyX.lift (i[1]'(by decide)))
    (qValue l i).val (vValue l i).val h.1 h.2
    ⟨by omega, by exact_mod_cast hk⟩ ⟨by omega, by exact_mod_cast hv⟩ h0 h1
  exact ⟨(qValue l i).val + kmin l, he⟩

lemma values_complete (l : CertLayout) (i : fields 2 Field) (h : Assumptions l i)
    (hs : Spec i) :
    (qValue l i).val < 2 ^ qbits l ∧ (vValue l i).val < 2 ^ tbits l := by
  obtain ⟨k, hk⟩ := hs
  have hb := certificate_complete l
    (LazyX.lift (i[0]'(by decide))) (LazyX.lift (i[1]'(by decide))) k h.1 h.2 hk
  have he := congrArg (fun z : ℤ => (z : Field)) hk
  push_cast at he
  simp only [LazyX.cast_lift] at he
  have hq : rawQ i = (k : Field) := by
    unfold rawQ
    rw [he, ← mul_assoc]
    have hqn : (q : Field) ≠ 0 := by decide
    rw [inv_mul_cancel₀ hqn, one_mul]
  have hqv : qValue l i = ((k-kmin l : ℤ) : Field) := by
    simp only [qValue, hq, Int.cast_sub]
  have hn := (SmallCert.native (i[0]'(by decide)) (i[1]'(by decide))).2
  change (i[1]'(by decide)) - ((R-1 : ℤ) : Field) * rawQ i +
    (R : Field)⁻¹ * ((i[0]'(by decide)) - ((R-c : ℤ) : Field) * rawQ i) = 0 at hn
  rw [hq] at hn
  have hvv :
      vValue l i = (((R-1)*k-LazyX.lift (i[1]'(by decide))-tmin l : ℤ) : Field) := by
    unfold vValue
    rw [hq]
    push_cast at hn ⊢
    rw [LazyX.cast_lift]
    linear_combination hn
  constructor
  · rw [hqv]
    exact AffineNarrow.range_of_int _ _ hb.1 (qbits_valid l)
  · rw [hvv]
    exact AffineNarrow.range_of_int _ _ hb.2 (tbits_valid l)

lemma eval_expr (l : CertLayout) (env : Environment Field) (i : Var (fields 2) Field) :
    Expression.eval env (qExpr l i) = qValue l (eval env i) ∧
    Expression.eval env (vExpr l i) = vValue l (eval env i) := by
  simp only [qExpr, vExpr, rawQExpr, qValue, vValue, rawQ, Expression.eval,
    circuit_norm, neg_one_mul, sub_eq_add_neg, and_self]

theorem soundness (l : CertLayout) :
    FormalAssertion.Soundness Field (main l) (Assumptions l) Spec := by
  circuit_proof_start_core
  have he := eval_expr l env input_var
  rw [h_input] at he
  simp only [main, circuit_norm, RangeCheck.circuit, RangeCheck.Assumptions,
    RangeCheck.Spec] at h_holds ⊢
  exact values_sound l input h_assumptions
    (by simpa only [he.1] using h_holds.1) (by simpa only [he.2] using h_holds.2)

theorem completeness (l : CertLayout) :
    FormalAssertion.Completeness Field (main l) (Assumptions l) Spec := by
  circuit_proof_start_core
  have he := eval_expr l env.toEnvironment input_var
  have hi : eval env.toEnvironment input_var = input := by
    simpa only [circuit_norm] using h_input
  rw [hi] at he
  have hv := values_complete l input h_assumptions h_spec
  simp only [main, circuit_norm, RangeCheck.circuit, RangeCheck.Assumptions, RangeCheck.Spec]
  exact ⟨by simpa only [he.1] using hv.1, by simpa only [he.2] using hv.2⟩

def circuit (l : CertLayout) : FormalAssertion Field (fields 2) where
  main := main l
  Assumptions := Assumptions l
  Spec := Spec
  soundness := soundness l
  completeness := completeness l

theorem cost (l : CertLayout) (i : Var (fields 2) Field) :
    CostIs (main l i) ⟨qbits l+tbits l-2, qbits l+tbits l⟩ := by
  rw [show (⟨qbits l+tbits l-2, qbits l+tbits l⟩ : Count) =
    ⟨qbits l-1, qbits l⟩ + ⟨tbits l-1, tbits l⟩ by
      cases l with
      | start => norm_num [qbits, tbits] <;> decide
      | finalX => norm_num [qbits, tbits] <;> decide
      | finalY => norm_num [qbits, tbits] <;> decide
      | wide d => fin_cases d <;> norm_num [qbits, tbits] <;> decide]
  unfold main
  refine CostIs.bind (costIs_assertion_implicitRangeCheck _ _ _ _) fun _ => ?_
  exact costIs_assertion_implicitRangeCheck _ _ _ _

lemma affine_expr (l : CertLayout) (i : Var (fields 2) Field) (hi : AffineW i) :
    Affine (qExpr l i) ∧ Affine (vExpr l i) := by
  have hq : Affine (rawQExpr i) :=
    Affine.fconst_mul _
      (Affine.add (hi _ (by decide)) (Affine.fconst_mul _ (hi _ (by decide))))
  exact ⟨Affine.sub hq (Affine.const _),
    Affine.sub
      (Affine.fconst_mul _ (Affine.sub (hi _ (by decide)) (Affine.fconst_mul _ hq)))
      (Affine.const _)⟩

theorem shape (l : CertLayout) (i : Var (fields 2) Field) (hi : AffineW i) :
    IsR1CSCirc (main l i) := by
  have h := affine_expr l i hi
  unfold main
  refine IsR1CSCirc.bind (isR1CS_assertion_implicitRangeCheck _ _ _ _ h.1) fun _ => ?_
  exact isR1CS_assertion_implicitRangeCheck _ _ _ _ h.2

lemma expr_stable (l : CertLayout) (i : Var (fields 2) Field)
    {e e' : ProverEnvironment Field} (h : eval e i = eval e' i) :
    eval e (qExpr l i) = eval e' (qExpr l i) ∧
      eval e (vExpr l i) = eval e' (vExpr l i) := by
  have h' : eval e.toEnvironment i = eval e'.toEnvironment i := by
    simpa only [circuit_norm] using h
  simpa only [circuit_norm, (eval_expr l e.toEnvironment i).1,
    (eval_expr l e'.toEnvironment i).1, (eval_expr l e.toEnvironment i).2,
    (eval_expr l e'.toEnvironment i).2, h']

theorem computableWitnesses (l : CertLayout) : (circuit l).ComputableWitnesses := by
  intro n input env env'
  change Operations.forAllFlat n (FormalCircuitBase.computableWitnessCondition input env env')
    ((main l input).operations n)
  apply FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  simp only [main, Circuit.bind_structuralComputableWitnesses_iff]
  constructor
  · exact CWHelpers.assertion_structuralComputableWitnesses_of_condition
      (RangeCheck.circuit (qbits l) (qbits_valid l) (qbits_pos l))
      input _ _ (fun _ _ _ _ _ h => (expr_stable l input h).1)
      (RangeCheck.computableWitnesses _ _ _) env env'
  · exact CWHelpers.assertion_structuralComputableWitnesses_of_condition
      (RangeCheck.circuit (tbits l) (tbits_valid l) (tbits_pos l))
      input _ _ (fun _ _ _ _ _ h => (expr_stable l input h).2)
      (RangeCheck.computableWitnesses _ _ _) env env'

lemma model (l : CertLayout) (i : fields 2 Field) (L H : ℤ)
    (hL : loMin l ≤ L ∧ L ≤ loMax l)
    (hH : hiMin l ≤ H ∧ H ≤ hiMax l)
    (hl : (i[0]'(by decide)) = (L : Field))
    (hh : (i[1]'(by decide)) = (H : Field)) :
    Assumptions l i ∧ (Spec i ↔ q ∣ L+R*H) := by
  have he := endpoints_centered l
  have hhalf : Sparse32.nativeHalf = LazyX.nativeHalf := by
    norm_num [Sparse32.nativeHalf, Sparse32.nativePrime, LazyX.nativeHalf]
  have hlift : LazyX.lift (i[0]'(by decide)) = L := by
    rw [hl]
    apply LazyX.lift_cast
    rw [← hhalf]
    omega
  have hlifth : LazyX.lift (i[1]'(by decide)) = H := by
    rw [hh]
    apply LazyX.lift_cast
    rw [← hhalf]
    omega
  simp only [Assumptions, Spec, hlift, hlifth]
  exact ⟨⟨hL, hH⟩, trivial⟩

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

theorem circuitCount_main (input : Var Inputs Field) :
    circuitCount (main input) = mulCost :=
  circuitCount_eq_of_CostIs (costIs_main input)

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

theorem localLength_eq (input : Var Inputs Field) (n : ℕ) :
    (main input).localLength n = 12 := by
  simp only [main, circuit_norm]

theorem output_eq (input : Var Inputs Field) (n : ℕ) :
    (main input).output n = outputExpr (varFromOffset (fields 12) n) := by
  simp only [main, circuit_norm]

theorem call_output (input : Var Inputs Field) (n : ℕ) :
    (subcircuit circuit input).output n = (main input).output n :=
  (elaborated.output_eq input n).symm

theorem affine_output (input : Var Inputs Field) (n : ℕ) :
    AffineW ((main input).output n) := by
  rw [output_eq]
  exact affine_outputExpr _ (affineW_mapRange_var _)

theorem affine_call_output (input : Var Inputs Field) (n : ℕ) :
    AffineW ((subcircuit circuit input).output n) := by
  rw [call_output]
  exact affine_output input n

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

structure Inputs (F : Type) where
  a : fields 8 F
  b : fields 8 F
  x : fields 8 F
  A : Packed.Point F
  T : Packed.Point F
deriving ProvableStruct

def DigitBound (a : fields 8 Field) : Prop :=
  ∀ k : Fin 8, -m ≤ Sparse32.digitsZ a k ∧ Sparse32.digitsZ a k ≤ m - 1

def Assumptions (d : Fin 21) (i : Inputs Field) : Prop :=
  XBound (d.val + 1) i.x ∧ DigitBound i.a ∧ DigitBound i.b ∧
  BigInt.Normalized 64 i.A.point.x ∧ BigInt.Normalized 64 i.A.point.y ∧
  BigInt.Normalized 64 i.T.point.x ∧ BigInt.Normalized 64 i.T.point.y ∧
  Packed.Consistent i.A ∧ Packed.Consistent i.T

def evalCurve (a : fields 8 Field) : Specs.Secp256k1.Fp :=
  Sparse32.eval (fun k => (Sparse32.digitsZ a k : Specs.Secp256k1.Fp))
    (Sparse32.H : Specs.Secp256k1.Fp)

def Spec (i : Inputs Field) : Prop :=
  evalCurve i.a * (decodeFe i.A.point.x - valueFp i.x) +
    evalCurve i.b * (decodeFe i.T.point.x - valueFp i.x) =
      decodeFe i.A.point.y + decodeFe i.T.point.y

def difference (x : fields 8 Field) (u : Emu Field) : fields 8 Field :=
  Vector.ofFn fun k => (embedVec u)[k.val] - x[k.val]

def differenceExpr (x : Var (fields 8) Field) (u : Var Emu Field) :
    Var (fields 8) Field :=
  Vector.ofFn fun k => (embedExpr u)[k.val] - x[k.val]

def mulInput (a x : fields 8 Field) (u : Emu Field) : Sparse32Mul.Inputs Field :=
  ⟨a, difference x u⟩

def mulExpr (a x : Var (fields 8) Field) (u : Var Emu Field) :
    Var Sparse32Mul.Inputs Field :=
  ⟨a, differenceExpr x u⟩

lemma eval_differenceExpr (env : Environment Field) (x : Var (fields 8) Field)
    (u : Var Emu Field) :
    eval env (differenceExpr x u) = difference (eval env x) (eval env u) := by
  have hu := eval_embedExpr env u
  apply Vector.ext
  intro k hk
  have huk := congrArg (fun v : fields 8 Field => v[k]) hu
  simp only [circuit_norm, Vector.getElem_map] at huk
  simp only [differenceExpr, difference, circuit_norm, Vector.getElem_ofFn,
    Expression.eval, huk, neg_one_mul, sub_eq_add_neg]

lemma eval_mulExpr (env : Environment Field) (a x : Var (fields 8) Field)
    (u : Var Emu Field) :
    eval env (mulExpr a x u) = mulInput (eval env a) (eval env x) (eval env u) := by
  simp only [mulExpr, mulInput, circuit_norm]
  congr 1
  simpa only [circuit_norm] using eval_differenceExpr env x u

def productVec (a x : fields 8 Field) (u : Emu Field) : fields 8 Field :=
  Vector.ofFn fun k => Sparse32.sparseMul (fun j => a[j.val])
    (fun j => (difference x u)[j.val]) k

lemma mulSpec_iff (a x : fields 8 Field) (u : Emu Field) (z : fields 8 Field) :
    Sparse32Mul.Spec (mulInput a x u) z ↔ z = productVec a x u := by
  rfl

def coeffZ (i : Inputs Field) : Sparse32.Words ℤ :=
  Sparse32.wideCoeff (Sparse32.digitsZ i.a) (Sparse32.digitsZ i.b)
    (zwords i.x) (emuz i.A.point.x) (emuz i.T.point.x)

def coeffHalf (z : Sparse32.Words ℤ) (side : Bool) : ℤ :=
  if side then Sparse32.highHalf z else Sparse32.lowHalf z

def halfZ (i : Inputs Field) (side : Bool) : ℤ :=
  coeffHalf (coeffZ i) side - SmallCert.halfZ i.A.point.y side -
    SmallCert.halfZ i.T.point.y side

def halves (i : Inputs Field) : fields 2 Field :=
  Vector.ofFn fun k => ((halfZ i (decide (k.val = 1)) : ℤ) : Field)

def productHalfExpr (z : Var (fields 8) Field) (side : Bool) : Expression Field :=
  if side then
    z[4] + (H : Field) * z[5] + (H ^ 2 : Field) * z[6] + (H ^ 3 : Field) * z[7]
  else
    z[0] + (H : Field) * z[1] + (H ^ 2 : Field) * z[2] + (H ^ 3 : Field) * z[3]

def halvesExpr (i : Var Inputs Field) (za zb : Var (fields 8) Field) :
    Var (fields 2) Field :=
  Vector.ofFn fun k =>
    productHalfExpr za (decide (k.val = 1)) +
      productHalfExpr zb (decide (k.val = 1)) -
      i.A.halves[k.val] - i.T.halves[k.val]

lemma product_cast (a x : fields 8 Field) (u : Emu Field) (k : Fin 8) :
    (productVec a x u)[k.val] =
      ((Sparse32.sparseMul (Sparse32.digitsZ a)
        (fun j => Sparse32.embed (emuz u) j - zwords x j) k : ℤ) : Field) := by
  rw [productVec, Vector.getElem_ofFn]
  change Sparse32.sparseMul (fun j => a[j.val])
    (fun j => (difference x u)[j.val]) k = _
  calc
    _ = Sparse32.sparseMul
        (fun j => ((Sparse32.digitsZ a j : ℤ) : Field))
        (fun j => ((Sparse32.embed (emuz u) j - zwords x j : ℤ) : Field)) k := by
      congr 1
      · funext j
        simp only [Sparse32.digitsZ, LazyX.cast_lift]
      · funext j
        simp only [difference, embedVec, Vector.getElem_ofFn, Int.cast_sub, zwords,
          LazyX.cast_lift, Sparse32.embed, emuz]
        split_ifs <;>
          simp only [Int.cast_zero, Int.cast_natCast, FoldQuot.natCast_val_F]
    _ = _ := Sparse32.sparseMul_map (Int.castRingHom Field)
      (Sparse32.digitsZ a) (fun j => Sparse32.embed (emuz u) j - zwords x j) k

lemma packed_half (p : Packed.Point Field) (hp : Packed.Consistent p) (k : Fin 2) :
    p.halves[k.val] = ((SmallCert.halfZ p.point.y (decide (k.val = 1)) : ℤ) : Field) := by
  rw [hp]
  fin_cases k <;>
    simp only [Packed.pack, SmallCert.halfZ, Vector.getElem_ofFn, Fin.val_mk,
      Nat.reduceMul, Nat.reduceAdd, Nat.reduceEqDiff, decide_true, decide_false,
      Bool.false_eq_true, ↓reduceIte, Int.cast_add, Int.cast_mul, Int.cast_pow,
      Int.cast_ofNat, Int.cast_natCast, Nat.cast_ofNat, FoldQuot.natCast_val_F]

lemma eval_productHalfExpr (env : Environment Field) (z : Var (fields 8) Field)
    (side : Bool) :
    Expression.eval env (productHalfExpr z side) =
      (if side then Sparse32.highHalf (fun k => (eval env z)[k.val])
        else Sparse32.lowHalf (fun k => (eval env z)[k.val])) := by
  cases side <;>
    simp only [productHalfExpr, Bool.false_eq_true, ↓reduceIte, Sparse32.lowHalf,
      Sparse32.highHalf, circuit_norm, Expression.eval]

lemma eval_halves (d : Fin 21) (env : Environment Field) (iv : Var Inputs Field)
    (za zb : Var (fields 8) Field) (i : Inputs Field) (hi : eval env iv = i)
    (h : Assumptions d i)
    (hza : eval env za = productVec i.a i.x i.A.point.x)
    (hzb : eval env zb = productVec i.b i.x i.T.point.x) :
    eval env (halvesExpr iv za zb) = halves i := by
  have hA : eval env iv.A.halves = i.A.halves := by
    simpa only [circuit_norm] using congrArg (fun v : Inputs Field => v.A.halves) hi
  have hT : eval env iv.T.halves = i.T.halves := by
    simpa only [circuit_norm] using congrArg (fun v : Inputs Field => v.T.halves) hi
  have hz (k : Fin 8) :
      (eval env za)[k.val] + (eval env zb)[k.val] = ((coeffZ i k : ℤ) : Field) := by
    rw [hza, hzb, product_cast, product_cast]
    simp only [coeffZ, Sparse32.wideCoeff, Int.cast_add]
  have hh (side : Bool) :
      Expression.eval env (productHalfExpr za side + productHalfExpr zb side) =
        ((coeffHalf (coeffZ i) side : ℤ) : Field) := by
    simp only [Expression.eval, eval_productHalfExpr]
    cases side
    · simp only [coeffHalf, Bool.false_eq_true, ↓reduceIte, Sparse32.lowHalf,
        Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
      linear_combination hz 0 + (H : Field) * hz 1 +
        (H ^ 2 : Field) * hz 2 + (H ^ 3 : Field) * hz 3
    · simp only [coeffHalf, ↓reduceIte, Sparse32.highHalf, Int.cast_add,
        Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
      linear_combination hz 4 + (H : Field) * hz 5 +
        (H ^ 2 : Field) * hz 6 + (H ^ 3 : Field) * hz 7
  apply Vector.ext
  intro k hk
  have hAk := congrArg (fun v : fields 2 Field => v[k]) hA
  have hTk := congrArg (fun v : fields 2 Field => v[k]) hT
  simp only [circuit_norm, Vector.getElem_map] at hAk hTk
  simp only [halvesExpr, halves, circuit_norm, Vector.getElem_ofFn, Expression.eval,
    hAk, hTk, packed_half i.A h.2.2.2.2.2.2.2.1 ⟨k, hk⟩,
    packed_half i.T h.2.2.2.2.2.2.2.2 ⟨k, hk⟩, halfZ,
    Int.cast_sub, Int.cast_add, Int.cast_neg, neg_one_mul, sub_eq_add_neg]
  have hhs := hh (decide (k = 1))
  simp only [Expression.eval] at hhs
  linear_combination hhs

lemma half_bounds (d : Fin 21) (i : Inputs Field) (h : Assumptions d i) :
    (Sparse32.loMin (.wide d) ≤ halfZ i false ∧
      halfZ i false ≤ Sparse32.loMax (.wide d)) ∧
    (Sparse32.hiMin (.wide d) ≤ halfZ i true ∧
      halfZ i true ≤ Sparse32.hiMax (.wide d)) := by
  rcases h with ⟨hx, ha, hb, hAx, hAy, hTx, hTy, hAc, hTc⟩
  have hw := Sparse32.wide_bounds ⟨d.val + 1, by omega⟩
    (Sparse32.digitsZ i.a) (Sparse32.digitsZ i.b) (zwords i.x)
    (emuz i.A.point.x) (emuz i.T.point.x) ha hb hx
    (emuz_bounds _ hAx) (emuz_bounds _ hTx)
  have hh := Sparse32.half_interval (coeffZ i)
    (Sparse32.wideLower (d.val + 1)) (Sparse32.wideUpper (d.val + 1)) hw
  have ha0 := SmallCert.half_bounds i.A.point.y hAy false
  have ha1 := SmallCert.half_bounds i.A.point.y hAy true
  have ht0 := SmallCert.half_bounds i.T.point.y hTy false
  have ht1 := SmallCert.half_bounds i.T.point.y hTy true
  simp only [Sparse32.loMin, Sparse32.loMax, Sparse32.hiMin, Sparse32.hiMax,
    halfZ, coeffHalf, Bool.false_eq_true, ↓reduceIte] at *
  norm_num [Sparse32.R, SmallSquare.R] at *
  omega

lemma eval_add {K : Type*} [CommRing K] (a b : Sparse32.Words K) (r : K) :
    Sparse32.eval (fun i => a i + b i) r = Sparse32.eval a r + Sparse32.eval b r := by
  simp only [Sparse32.eval, add_mul, Finset.sum_add_distrib]

lemma product_semantics (a x : fields 8 Field) (u : Emu Field) :
    ((Sparse32.eval
      (Sparse32.sparseMul (Sparse32.digitsZ a)
        (fun j => Sparse32.embed (emuz u) j - zwords x j)) H : ℤ) :
        Specs.Secp256k1.Fp) =
      evalCurve a * (decodeFe u - valueFp x) := by
  rw [SparseX.eval_cast]
  have hm :
      (fun k => ((Sparse32.sparseMul (Sparse32.digitsZ a)
        (fun j => Sparse32.embed (emuz u) j - zwords x j) k : ℤ) :
          Specs.Secp256k1.Fp)) =
      Sparse32.sparseMul
        (fun k => (Sparse32.digitsZ a k : Specs.Secp256k1.Fp))
        (fun j => ((Sparse32.embed (emuz u) j - zwords x j : ℤ) :
          Specs.Secp256k1.Fp)) := by
    funext k
    exact (Sparse32.sparseMul_map (Int.castRingHom Specs.Secp256k1.Fp)
      (Sparse32.digitsZ a) (fun j => Sparse32.embed (emuz u) j - zwords x j) k).symm
  rw [hm]
  rw [Sparse32.eval_sparseMul _ _ _ SparseX.curve_root]
  unfold evalCurve
  congr 1
  simp only [Int.cast_sub]
  rw [SparseX.eval_sub]
  rw [← SparseX.eval_cast (Sparse32.embed (emuz u)), SparseX.embed_value]
  rw [← SparseX.eval_cast (zwords x)]
  rfl

lemma model (d : Fin 21) (i : Inputs Field) (h : Assumptions d i) :
    Sparse32Cert.Assumptions (.wide d) (halves i) ∧
      (Sparse32Cert.Spec (halves i) ↔ Spec i) := by
  have hb := half_bounds d i h
  have hm := Sparse32Cert.model (.wide d) (halves i) (halfZ i false) (halfZ i true)
    hb.1 hb.2
    (by simp only [halves, Vector.getElem_ofFn, Fin.val_zero, Nat.reduceEqDiff,
      decide_false])
    (by simp only [halves, Vector.getElem_ofFn, Fin.val_one, decide_true])
  refine ⟨hm.1, hm.2.trans ?_⟩
  have he : halfZ i false + Sparse32.R * halfZ i true =
      Sparse32.eval (coeffZ i) H - (BigInt.value 64 i.A.point.y : ℤ) -
        (BigInt.value 64 i.T.point.y : ℤ) := by
    rw [Sparse32.eval_eq_halves, ← SmallCert.value_halves i.A.point.y,
      ← SmallCert.value_halves i.T.point.y]
    unfold halfZ coeffHalf
    simp only [Bool.false_eq_true, ↓reduceIte]
    norm_num [Sparse32.R, SmallSquare.R]
    ring
  rw [he, SparseX.dvd_q_iff]
  have hc : ((Sparse32.eval (coeffZ i) H : ℤ) : Specs.Secp256k1.Fp) =
      evalCurve i.a * (decodeFe i.A.point.x - valueFp i.x) +
        evalCurve i.b * (decodeFe i.T.point.x - valueFp i.x) := by
    unfold coeffZ Sparse32.wideCoeff
    rw [eval_add]
    push_cast
    rw [product_semantics, product_semantics]
  push_cast
  rw [hc]
  change (_ - decodeFe i.A.point.y - decodeFe i.T.point.y = 0) ↔ Spec i
  unfold Spec
  constructor <;> intro heq <;> linear_combination heq

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

theorem circuitCount_main (a : Var Inputs Field) :
    circuitCount (main a) = squareCost :=
  circuitCount_eq_of_CostIs (costIs_main a)

end Solution.Secp256k1ScalarMulFixedBase.Sparse32Square

end DonorFile6_14
