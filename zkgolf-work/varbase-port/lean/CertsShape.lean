import Solution.Secp256k1ScalarMul.Lazy.CertsCost

/-! R1CS shape of the certificate-slot assertion. -/

namespace Solution.Secp256k1ScalarMulFixedBase.LazyVar.Certs

open SmallSquare Sparse32 SparseX Challenge.CostR1CS Cost
open Solution.Secp256k1ScalarMul.Lazy
open Solution.Secp256k1ScalarMulFixedBase.LazyVar

set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 20000

/-! ### Shape -/

attribute [local irreducible] isR1CSRow r1csProducts operationsIsR1CS flatOperationsIsR1CS

def AffineInput (i : Var Inputs Field) : Prop :=
  AffineW i.a ∧ AffineW i.b ∧ AffineW i.x ∧ AffineW i.y ∧ AffineW i.tx ∧ AffineW i.ty ∧
  AffineW i.p.pa ∧ AffineW i.p.pu ∧ AffineW i.p.sx ∧ AffineW i.p.pxt ∧ AffineW i.p.st ∧
  AffineW i.p.sa ∧ AffineW i.p.pab ∧ AffineW i.p.sb ∧ AffineW i.p.pb ∧
  Affine i.gate ∧ Affine i.cflag ∧ Affine i.zflag

lemma affineW_pair {a b : Expression Field} (ha : Affine a) (hb : Affine b) :
    AffineW (#v[a, b] : Var (fields 2) Field) := by
  intro k hk
  match k, hk with
  | 0, _ => exact ha
  | 1, _ => exact hb

lemma affineW_triple {a b c : Expression Field} (ha : Affine a) (hb : Affine b) (hc : Affine c) :
    AffineW (#v[a, b, c] : Var (fields 3) Field) := by
  intro k hk
  match k, hk with
  | 0, _ => exact ha
  | 1, _ => exact hb
  | 2, _ => exact hc

lemma affine_half (w : Var (fields 8) Field) (hw : AffineW w) (side : Bool) :
    Affine (half w side) :=
  Sparse32Wide.affine_productHalfExpr w hw side

lemma affine_limb (w : Var (fields 8) Field) (hw : AffineW w) (j : Fin 3) :
    Affine (limb w j) := by
  unfold limb
  split_ifs
  · exact Affine.add (Affine.add (hw _ _) (Affine.fconst_mul _ (hw _ _))) (Affine.fconst_mul _ (hw _ _))
  · exact Affine.add (Affine.add (hw _ _) (Affine.fconst_mul _ (hw _ _))) (Affine.fconst_mul _ (hw _ _))
  · exact Affine.add (hw _ _) (Affine.fconst_mul _ (hw _ _))

lemma affine_rel2W (i : Var Inputs Field) (hp : AffineW i.p.pab) (hy : AffineW i.y) :
    AffineW (rel2W i) := by
  intro k hk
  rw [rel2W, Vector.getElem_ofFn]
  exact Affine.sub (hp _ _) (Affine.fconst_mul _ (hy _ _))

theorem shape (i : Var Inputs Field) (hi : AffineInput i) : IsR1CSCirc (main i) := by
  obtain ⟨ha, hb, hx, hy, htx, hty, hpa, hpu, hsx, hpxt, hst, hsa, hpab, hsb, hpb, hg, hc, hz⟩ := hi
  have hetx := affine_embedExpr i.tx htx
  have hety := affine_embedExpr i.ty hty
  have hchord : AffineW (chordW i) :=
    Products.affine_vaddE _ _ (Products.affine_vsubE _ _ hpa hety) hy
  have hxeq1 : AffineW (xeq1W i) := Products.affine_vsubE _ _ hx hetx
  have huni : AffineW (uniW i) :=
    Products.affine_vsubE _ _ hpu (Products.affine_vaddE _ _ (Products.affine_vaddE _ _ hsx hpxt) hst)
  have hyeq : AffineW (yeqW i) := Products.affine_vaddE _ _ hy hety
  have hxeq2 : AffineW (xeq2W i) :=
    Products.affine_vsubE _ _ (Products.affine_vsubE _ _ (Products.affine_vsubE _ _ hsa hx) hetx) hx
  have hrel2 : AffineW (rel2W i) := affine_rel2W i hpab hy
  have hcz : Affine (i.cflag + i.zflag) := Affine.add hc hz
  unfold main
  refine IsR1CSCirc.bind_out_inv Affine (MulCell.shape_call _ hc
    (Affine.sub (affine_half _ hxeq1 _) (affine_half _ hchord _)))
    (MulCell.affine_call_output _) fun m1l hm1l => ?_
  refine IsR1CSCirc.bind_out_inv Affine (MulCell.shape_call _ hg
    (Affine.add (affine_half _ hchord _) hm1l))
    (MulCell.affine_call_output _) fun h1l hh1l => ?_
  refine IsR1CSCirc.bind_out_inv Affine (MulCell.shape_call _ hc
    (Affine.sub (affine_half _ hxeq1 _) (affine_half _ hchord _)))
    (MulCell.affine_call_output _) fun m1h hm1h => ?_
  refine IsR1CSCirc.bind_out_inv Affine (MulCell.shape_call _ hg
    (Affine.add (affine_half _ hchord _) hm1h))
    (MulCell.affine_call_output _) fun h1h hh1h => ?_
  refine IsR1CSCirc.bind_out_inv Affine (MulCell.shape_call _ hc
    (Affine.sub (affine_limb _ hyeq _) (affine_limb _ huni _)))
    (MulCell.affine_call_output _) fun mu0 hmu0 => ?_
  refine IsR1CSCirc.bind_out_inv Affine (MulCell.shape_call _ hg
    (Affine.add (affine_limb _ huni _) hmu0))
    (MulCell.affine_call_output _) fun l0 hl0 => ?_
  refine IsR1CSCirc.bind_out_inv Affine (MulCell.shape_call _ hc
    (Affine.sub (affine_limb _ hyeq _) (affine_limb _ huni _)))
    (MulCell.affine_call_output _) fun mu1 hmu1 => ?_
  refine IsR1CSCirc.bind_out_inv Affine (MulCell.shape_call _ hg
    (Affine.add (affine_limb _ huni _) hmu1))
    (MulCell.affine_call_output _) fun l1 hl1 => ?_
  refine IsR1CSCirc.bind_out_inv Affine (MulCell.shape_call _ hc
    (Affine.sub (affine_limb _ hyeq _) (affine_limb _ huni _)))
    (MulCell.affine_call_output _) fun mu2 hmu2 => ?_
  refine IsR1CSCirc.bind_out_inv Affine (MulCell.shape_call _ hg
    (Affine.add (affine_limb _ huni _) hmu2))
    (MulCell.affine_call_output _) fun l2 hl2 => ?_
  refine IsR1CSCirc.bind_out_inv Affine (MulCell.shape_call _ hg hz)
    (MulCell.affine_call_output _) fun gz hgz => ?_
  refine IsR1CSCirc.bind_out_inv Affine
    (MulCell.shape_call ⟨gz, half (xeq2W i) false⟩ hgz (affine_half _ hxeq2 false))
    (MulCell.affine_call_output _) fun hxl hhxl => ?_
  refine IsR1CSCirc.bind_out_inv Affine
    (MulCell.shape_call ⟨gz, half (xeq2W i) true⟩ hgz (affine_half _ hxeq2 true))
    (MulCell.affine_call_output _) fun hxh hhxh => ?_
  refine IsR1CSCirc.bind_out_inv Affine
    (MulCell.shape_call ⟨i.cflag + i.zflag, half (rel2W i) false⟩ hcz (affine_half _ hrel2 false))
    (MulCell.affine_call_output _) fun m2l hm2l => ?_
  refine IsR1CSCirc.bind_out_inv Affine
    (MulCell.shape_call ⟨i.gate, half (rel2W i) false - m2l⟩ hg
      (Affine.sub (affine_half _ hrel2 false) hm2l))
    (MulCell.affine_call_output _) fun h2l hh2l => ?_
  refine IsR1CSCirc.bind_out_inv Affine
    (MulCell.shape_call ⟨i.cflag + i.zflag, half (rel2W i) true⟩ hcz (affine_half _ hrel2 true))
    (MulCell.affine_call_output _) fun m2h hm2h => ?_
  refine IsR1CSCirc.bind_out_inv Affine
    (MulCell.shape_call ⟨i.gate, half (rel2W i) true - m2h⟩ hg
      (Affine.sub (affine_half _ hrel2 true) hm2h))
    (MulCell.affine_call_output _) fun h2h hh2h => ?_
  refine IsR1CSCirc.bind (IsR1CSCirc.assertion (Cert.shape .rel1 _
    (affineW_pair hh1l hh1h))) fun _ => ?_
  refine IsR1CSCirc.bind (IsR1CSCirc.assertion (Cert3.shape _
    (affineW_triple hl0 hl1 hl2))) fun _ => ?_
  refine IsR1CSCirc.bind (IsR1CSCirc.assertion (Cert.shape .xeq _
    (affineW_pair hhxl hhxh))) fun _ => ?_
  exact IsR1CSCirc.assertion (Cert.shape .rel2 _ (affineW_pair hh2l hh2h))

theorem shape_call (n : ℕ) (hn : n ≤ depth) (i : Var Inputs Field) (hi : AffineInput i) :
    IsR1CSCirc (assertion (circuit n hn) i) :=
  IsR1CSCirc.assertion (fun n => shape i hi n)

end Solution.Secp256k1ScalarMulFixedBase.LazyVar.Certs
