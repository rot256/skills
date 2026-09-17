import Solution.Secp256k1ScalarMul.Lazy.StepOutput
import Solution.Secp256k1ScalarMul.Lazy.CertsShape
import Solution.Secp256k1ScalarMul.Lazy.ProductsShape

/-! R1CS shape of one chain step. -/

namespace Solution.Secp256k1ScalarMulFixedBase.LazyVar.Step

open SmallSquare Sparse32 SparseX Challenge.CostR1CS Cost
open Solution.Secp256k1ScalarMul.Lazy
open Solution.Secp256k1ScalarMulFixedBase.LazyVar

set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 20000

attribute [local irreducible] isR1CSRow r1csProducts operationsIsR1CS flatOperationsIsR1CS

def AffineLazy (P : Var LazyPt Field) : Prop := AffineW P.x ∧ AffineW P.y ∧ Affine P.isInf

def AffineInput (i : Var Inputs Field) : Prop :=
  AffineLazy i.acc ∧ AffineW i.t.x ∧ AffineW i.t.y ∧ Affine i.t.isInf ∧ Affine i.sp

def AffineProducts (p : Var Products.Outputs Field) : Prop :=
  AffineW p.pa ∧ AffineW p.pu ∧ AffineW p.sx ∧ AffineW p.pxt ∧ AffineW p.st ∧ AffineW p.sa ∧
  AffineW p.pab ∧ AffineW p.sb ∧ AffineW p.pb

lemma affineW_zeroVec : AffineW zeroVec := by
  intro k hk
  rw [zeroVec, Vector.getElem_ofFn]
  exact Affine.zero (F := Field)

lemma affineLazy_outputAt (n : ℕ) : AffineLazy (outputAt n) :=
  ⟨affineW_varFromOffset 8 _, affineW_varFromOffset 8 _,
    Affine.sub (Affine.add (Affine.var _) (Affine.var _)) (Affine.var _)⟩

theorem shape (n : ℕ) (hn : n + 1 ≤ depth) (i : Var Inputs Field) (hi : AffineInput i) :
    IsR1CSCirc (main n hn i) := by
  obtain ⟨⟨hax, hay, hai⟩, htx, hty, hti, hsp⟩ := hi
  have hetx := affine_embedExpr i.t.x htx
  have hety := affine_embedExpr i.t.y hty
  have h1sp : Affine (1 - i.sp) := Affine.sub (Affine.const 1) hsp
  have h1ai : Affine (1 - i.acc.isInf) := Affine.sub (Affine.const 1) hai
  dsimp only [main]
  refine IsR1CSCirc.bind_out (IsR1CSCirc.provableWitness _) fun nl1 => ?_
  have hl1 := affineW_provableWitness_bigInt (k := 4) (fun env => lam1W (eval env i)) nl1
  refine IsR1CSCirc.bind_out_inv AffineW
    (IsR1CSCirc.subcircuitWithAssertion (Sparse32Normalize.shape _ hl1))
    (fun na => by rw [Sparse32Normalize.call_output]; exact Sparse32Normalize.affine_output _ hl1 na)
    fun a ha => ?_
  refine IsR1CSCirc.bind_out (IsR1CSCirc.provableWitness _) fun nl2 => ?_
  have hl2 := affineW_provableWitness_bigInt (k := 4) (fun env => lam2W (eval env i)) nl2
  refine IsR1CSCirc.bind_out_inv AffineW
    (IsR1CSCirc.subcircuitWithAssertion (Sparse32Normalize.shape _ hl2))
    (fun nb => by rw [Sparse32Normalize.call_output]; exact Sparse32Normalize.affine_output _ hl2 nb)
    fun b hb => ?_
  refine IsR1CSCirc.bind_out (IsR1CSCirc.provableWitness _) fun nfl => ?_
  have hfl : AffineW ((ProvableType.witness (α := fields 2) fun env => flagsW (eval env i)).output nfl :
      Var (fields 2) Field) := by
    rw [show ((ProvableType.witness (α := fields 2) fun env => flagsW (eval env i)).output nfl :
        Var (fields 2) Field) = varFromOffset (fields 2) nfl from rfl]
    exact affineW_varFromOffset _ _
  have hc := hfl 0 (by decide)
  have hz := hfl 1 (by decide)
  refine IsR1CSCirc.bind (IsR1CSCirc.assertZero (isR1CSRow_mul hc (Affine.sub (Affine.const 1) hc)))
    fun _ => ?_
  refine IsR1CSCirc.bind (IsR1CSCirc.assertZero (isR1CSRow_mul hz (Affine.sub (Affine.const 1) hz)))
    fun _ => ?_
  refine IsR1CSCirc.bind (IsR1CSCirc.assertZero (isR1CSRow_mul hc hz)) fun _ => ?_
  refine IsR1CSCirc.bind (IsR1CSCirc.assertZero (isR1CSRow_mul hai hc)) fun _ => ?_
  refine IsR1CSCirc.bind (IsR1CSCirc.assertZero (isR1CSRow_mul hai hz)) fun _ => ?_
  refine IsR1CSCirc.bind (IsR1CSCirc.assertZero (isR1CSRow_mul h1sp hti)) fun _ => ?_
  refine IsR1CSCirc.bind_out_inv Affine
    (MulCell.shape_call ⟨1 - i.sp, 1 - i.acc.isInf⟩ h1sp h1ai)
    (MulCell.affine_call_output _) fun g hg => ?_
  refine IsR1CSCirc.bind_out_inv AffineProducts
    (Products.shape_call ⟨a, b, i.acc.x, i.acc.y, i.t.x, i.t.y⟩ ⟨ha, hb, hax, hay, htx, hty⟩)
    (fun np => Products.affine_call_output _ np) fun p hp => ?_
  obtain ⟨hpa, hpu, hsx, hpxt, hst, hsa, hpab, hsb, hpb⟩ := hp
  refine IsR1CSCirc.bind (Certs.shape_call n (Nat.le_of_succ_le hn)
    ⟨a, b, i.acc.x, i.acc.y, i.t.x, i.t.y, p, g, _, _⟩
    ⟨ha, hb, hax, hay, htx, hty, hpa, hpu, hsx, hpxt, hst, hsa, hpab, hsb, hpb, hg, hc, hz⟩)
    fun _ => ?_
  refine IsR1CSCirc.bind_out_inv Affine
    (MulCell.shape_call ⟨i.acc.isInf, i.t.isInf⟩ hai hti)
    (MulCell.affine_call_output _) fun rt hrt => ?_
  refine IsR1CSCirc.bind_out_inv Affine
    (MulCell.shape_call ⟨_, rt⟩ hz hrt)
    (MulCell.affine_call_output _) fun zrt hzrt => ?_
  have hzo : Affine (_ + rt - zrt) := Affine.sub (Affine.add hz hrt) hzrt
  have hxP : AffineW (Products.vaddE (Products.vsubE p.sb p.sa) (embedExpr i.t.x)) :=
    Products.affine_vaddE _ _ (Products.affine_vsubE _ _ hsb hsa) hetx
  have hyP : AffineW (Products.vsubE p.pb i.acc.y) := Products.affine_vsubE _ _ hpb hay
  refine IsR1CSCirc.bind_out_inv AffineW
    (MuxVec.shape_call ⟨_, Products.vaddE (Products.vsubE p.sb p.sa) (embedExpr i.t.x), i.acc.x⟩ hc hxP hax)
    (MuxVec.affine_call_output _) fun xw hxw => ?_
  refine IsR1CSCirc.bind_out_inv AffineW
    (MuxVec.shape_call ⟨i.acc.isInf, xw, embedExpr i.t.x⟩ hai hxw hetx)
    (MuxVec.affine_call_output _) fun xv hxv => ?_
  refine IsR1CSCirc.bind_out_inv AffineW
    (MuxVec.shape_call ⟨_ + rt - zrt, xv, zeroVec⟩ hzo hxv affineW_zeroVec)
    (MuxVec.affine_call_output _) fun xo hxo => ?_
  refine IsR1CSCirc.bind_out_inv AffineW
    (MuxVec.shape_call ⟨_, Products.vsubE p.pb i.acc.y, i.acc.y⟩ hc hyP hay)
    (MuxVec.affine_call_output _) fun yw hyw => ?_
  refine IsR1CSCirc.bind_out_inv AffineW
    (MuxVec.shape_call ⟨i.acc.isInf, yw, embedExpr i.t.y⟩ hai hyw hety)
    (MuxVec.affine_call_output _) fun yv hyv => ?_
  refine IsR1CSCirc.bind_out_inv AffineW
    (MuxVec.shape_call ⟨_ + rt - zrt, yv, zeroVec⟩ hzo hyv affineW_zeroVec)
    (MuxVec.affine_call_output _) fun yo hyo => ?_
  exact IsR1CSCirc.pure _

theorem shape_call (n : ℕ) (hn : n + 1 ≤ depth) (i : Var Inputs Field) (hi : AffineInput i) :
    IsR1CSCirc (subcircuitWithAssertion (circuit n hn) i) :=
  IsR1CSCirc.subcircuitWithAssertion (fun k => shape n hn i hi k)

end Solution.Secp256k1ScalarMulFixedBase.LazyVar.Step
