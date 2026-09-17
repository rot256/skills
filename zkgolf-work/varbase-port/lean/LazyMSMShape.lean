import Solution.Secp256k1ScalarMul.Lazy.LazyMSMCost
import Solution.Secp256k1ScalarMul.Lazy.StepShape

/-! R1CS shape of the lazy chain. -/

namespace Solution.Secp256k1ScalarMul.LazyMSM

open Specs.ShortWeierstrass Specs.Secp256k1
open Solution.Secp256k1ScalarMulFixedBase.SparseX
open Solution.Secp256k1ScalarMulFixedBase.LazyVar
open Solution.Secp256k1ScalarMul.Lazy
open Challenge.CostR1CS Cost
open Solution.Secp256k1ScalarMulFixedBase.Cost (IsR1CSCirc.bind_out_inv)

set_option maxHeartbeats 16000000
set_option maxRecDepth 20000

attribute [local irreducible] isR1CSRow r1csProducts operationsIsR1CS flatOperationsIsR1CS

lemma affine_foldl_add (n : ℕ) (f : Fin n → Expression (F circomPrime)) (e : Expression (F circomPrime))
    (he : Affine e) (hf : ∀ i, Affine (f i)) :
    Affine (Fin.foldl n (fun acc i => acc + f i) e) := by
  induction n generalizing e with
  | zero => simpa only [Fin.foldl_zero] using he
  | succ n ih =>
      rw [Fin.foldl_succ]
      exact ih (fun i => f i.succ) (e + f 0) (Affine.add he (hf 0)) (fun i => hf _)

lemma affine_unitDefect (m : Var (fields GLVMSM.coeffBits) (F circomPrime)) (hm : AffineW m) :
    Affine (unitDefect m) := by
  unfold unitDefect
  exact Affine.add (Affine.sub (Affine.const 1) (hm 0 (by simp only [GLVMSM.coeffBits]; omega)))
    (affine_foldl_add 63 _ 0 Affine.zero (fun i => hm _ _))

lemma affineLazy_seed (input : Var Inputs (F circomPrime))
    (htab : AffineTableV input.tx input.ty input.tinf) : Step.AffineLazy (seed input) :=
  ⟨affine_embedExpr _ (htab.1 15 (by norm_num)), affine_embedExpr _ (htab.2.1 15 (by norm_num)),
    htab.2.2 15 (by norm_num)⟩

theorem shape (input : Var Inputs (F circomPrime))
    (htab : AffineTableV input.tx input.ty input.tinf)
    (hm0 : AffineW input.m0) (hm1 : AffineW input.m1)
    (hm2 : AffineW input.m2) (hm3 : AffineW input.m3) :
    IsR1CSCirc (main input) := by
  have hsp : Affine (spE input) := htab.2.2 15 (by norm_num)
  have htx : AffineW (embedExpr input.tx[15]) := affine_embedExpr _ (htab.1 15 (by norm_num))
  have hty : AffineW (embedExpr input.ty[15]) := affine_embedExpr _ (htab.2.1 15 (by norm_num))
  have h1sp : Affine (1 - spE input) := Affine.sub (Affine.const 1) hsp
  dsimp only [main]
  refine IsR1CSCirc.bind_out_inv Step.AffineLazy
    (IsR1CSCirc.foldlRange_inv Step.AffineLazy (affineLazy_seed input htab)
      (fun s k hs => ?_) (fun s k n _ => ?_))
    (fun n => ?_) fun acc hacc => ?_
  · unfold stepBody
    refine IsR1CSCirc.bind_out_inv AffineFP
      (isR1CS_sub_varLookup (lkInput input k) htab
        (hm3 _ (bitIdx_lt k)) (hm2 _ (bitIdx_lt k)) (hm1 _ (bitIdx_lt k)) (hm0 _ (bitIdx_lt k)))
      (fun n => affineFP_sub_varLookup _ n) fun t ht =>
      Step.shape_call _ _ _ ⟨hs, ht.1, ht.2.1, ht.2.2, hsp⟩
  · rw [stepBody_output]
    exact Step.affineLazy_outputAt _
  · have hl : ∀ (i : Fin 64), Operations.localLength (stepBody input default i 0).2 = 1622 :=
      fun i => stepBody_localLength' input default i 0
    simp only [circuit_norm, stepBody_output', hl, fin_foldl_eq_accL]
    exact Step.affineLazy_outputAt _
  obtain ⟨hax, hay, hai⟩ := hacc
  have hex : AffineW (Products.vsubE acc.x (embedExpr input.tx[15])) :=
    Products.affine_vsubE _ _ hax htx
  have hey : AffineW (Products.vsubE acc.y (embedExpr input.ty[15])) :=
    Products.affine_vsubE _ _ hay hty
  refine IsR1CSCirc.bind (IsR1CSCirc.assertZero (isR1CSRow_mul h1sp (Affine.sub hai hsp))) fun _ => ?_
  refine IsR1CSCirc.bind_out_inv Affine
    (MulCell.shape_call ⟨(1 : Expression (F circomPrime)) - spE input, Certs.half (Products.vsubE acc.x (embedExpr input.tx[15])) false⟩
      h1sp (Certs.affine_half _ hex false))
    (MulCell.affine_call_output _) fun hxl hhxl => ?_
  refine IsR1CSCirc.bind_out_inv Affine
    (MulCell.shape_call ⟨(1 : Expression (F circomPrime)) - spE input, Certs.half (Products.vsubE acc.x (embedExpr input.tx[15])) true⟩
      h1sp (Certs.affine_half _ hex true))
    (MulCell.affine_call_output _) fun hxh hhxh => ?_
  refine IsR1CSCirc.bind (IsR1CSCirc.assertion (Cert.shape .rel1 _ (Certs.affineW_pair hhxl hhxh)))
    fun _ => ?_
  refine IsR1CSCirc.bind_out_inv Affine
    (MulCell.shape_call ⟨(1 : Expression (F circomPrime)) - spE input, Certs.half (Products.vsubE acc.y (embedExpr input.ty[15])) false⟩
      h1sp (Certs.affine_half _ hey false))
    (MulCell.affine_call_output _) fun hyl hhyl => ?_
  refine IsR1CSCirc.bind_out_inv Affine
    (MulCell.shape_call ⟨(1 : Expression (F circomPrime)) - spE input, Certs.half (Products.vsubE acc.y (embedExpr input.ty[15])) true⟩
      h1sp (Certs.affine_half _ hey true))
    (MulCell.affine_call_output _) fun hyh hhyh => ?_
  refine IsR1CSCirc.bind (IsR1CSCirc.assertion (Cert.shape .fin _ (Certs.affineW_pair hhyl hhyh)))
    fun _ => ?_
  refine IsR1CSCirc.bind (IsR1CSCirc.assertZero (isR1CSRow_mul hsp (affine_unitDefect _ hm0))) fun _ => ?_
  refine IsR1CSCirc.bind (IsR1CSCirc.assertZero (isR1CSRow_mul hsp (affine_unitDefect _ hm1))) fun _ => ?_
  refine IsR1CSCirc.bind (IsR1CSCirc.assertZero (isR1CSRow_mul hsp (affine_unitDefect _ hm2))) fun _ => ?_
  exact IsR1CSCirc.assertZero (isR1CSRow_mul hsp (affine_unitDefect _ hm3))

theorem shape_call (input : Var Inputs (F circomPrime))
    (htab : AffineTableV input.tx input.ty input.tinf)
    (hm0 : AffineW input.m0) (hm1 : AffineW input.m1)
    (hm2 : AffineW input.m2) (hm3 : AffineW input.m3) :
    IsR1CSCirc (subcircuitWithAssertion circuit input) :=
  IsR1CSCirc.subcircuitWithAssertion (fun n => shape input htab hm0 hm1 hm2 hm3 n)

end Solution.Secp256k1ScalarMul.LazyMSM
