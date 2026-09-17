import Solution.Secp256k1ScalarMul.Lazy.Certs

/-! Cost, R1CS shape and local length of the certificate-slot assertion. -/

namespace Solution.Secp256k1ScalarMulFixedBase.LazyVar.Certs

open SmallSquare Sparse32 SparseX Challenge.CostR1CS Cost
open Solution.Secp256k1ScalarMul.Lazy
open Solution.Secp256k1ScalarMulFixedBase.LazyVar

set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 20000

/-- 17 product cells and the four certificates. -/
def certsCost : Count := ⟨839, 848⟩

theorem cost (i : Var Inputs Field) : CostIs (main i) certsCost := by
  rw [show certsCost = ⟨1, 1⟩ + (⟨1, 1⟩ + (⟨1, 1⟩ + (⟨1, 1⟩ + (⟨1, 1⟩ + (⟨1, 1⟩ + (⟨1, 1⟩ +
    (⟨1, 1⟩ + (⟨1, 1⟩ + (⟨1, 1⟩ + (⟨1, 1⟩ + (⟨1, 1⟩ + (⟨1, 1⟩ + (⟨1, 1⟩ + (⟨1, 1⟩ + (⟨1, 1⟩ +
    (⟨1, 1⟩ + (⟨qbits .rel1 + tbits .rel1 - 2, qbits .rel1 + tbits .rel1⟩ + (Cert3.cost3 +
    (⟨qbits .xeq + tbits .xeq - 2, qbits .xeq + tbits .xeq⟩ +
    (⟨qbits .rel2 + tbits .rel2 - 2, qbits .rel2 + tbits .rel2⟩ + Count.zero)))))))))))))))))))) by
    decide]
  unfold main
  refine CostIs.bind (MulCell.costIs_call _) fun _ => ?_
  refine CostIs.bind (MulCell.costIs_call _) fun _ => ?_
  refine CostIs.bind (MulCell.costIs_call _) fun _ => ?_
  refine CostIs.bind (MulCell.costIs_call _) fun _ => ?_
  refine CostIs.bind (MulCell.costIs_call _) fun _ => ?_
  refine CostIs.bind (MulCell.costIs_call _) fun _ => ?_
  refine CostIs.bind (MulCell.costIs_call _) fun _ => ?_
  refine CostIs.bind (MulCell.costIs_call _) fun _ => ?_
  refine CostIs.bind (MulCell.costIs_call _) fun _ => ?_
  refine CostIs.bind (MulCell.costIs_call _) fun _ => ?_
  refine CostIs.bind (MulCell.costIs_call _) fun _ => ?_
  refine CostIs.bind (MulCell.costIs_call _) fun _ => ?_
  refine CostIs.bind (MulCell.costIs_call _) fun _ => ?_
  refine CostIs.bind (MulCell.costIs_call _) fun _ => ?_
  refine CostIs.bind (MulCell.costIs_call _) fun _ => ?_
  refine CostIs.bind (MulCell.costIs_call _) fun _ => ?_
  refine CostIs.bind (MulCell.costIs_call _) fun _ => ?_
  refine CostIs.bind (CostIs.assertion (Cert.cost .rel1 _)) fun _ => ?_
  refine CostIs.bind (CostIs.assertion (Cert3.cost _)) fun _ => ?_
  refine CostIs.bind (CostIs.assertion (Cert.cost .xeq _)) fun _ => ?_
  exact CostIs.assertion (Cert.cost .rel2 _)

theorem costIs_call (n : ℕ) (hn : n ≤ depth) (i : Var Inputs Field) : CostIs (assertion (circuit n hn) i) certsCost :=
  CostIs.assertion (fun n => cost i n)

lemma localLength (i : Var Inputs Field) (n : ℕ) : (main i).localLength n = 839 := by
  simp only [main, MulCell.circuit, MulCell.elaborated, Cert.circuit, Cert3.circuit,
    RangeCheck.circuit, circuit_norm]
  decide

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
  unfold main
  refine IsR1CSCirc.bind_out (MulCell.shape_call _ hc
    (Affine.sub (affine_half _ hxeq1 _) (affine_half _ hchord _))) fun m1l => ?_
  have hm1l := MulCell.affine_call_output _ m1l
  refine IsR1CSCirc.bind_out (MulCell.shape_call _ hg
    (Affine.add (affine_half _ hchord _) hm1l)) fun h1l => ?_
  have hh1l := MulCell.affine_call_output _ h1l
  refine IsR1CSCirc.bind_out (MulCell.shape_call _ hc
    (Affine.sub (affine_half _ hxeq1 _) (affine_half _ hchord _))) fun m1h => ?_
  have hm1h := MulCell.affine_call_output _ m1h
  refine IsR1CSCirc.bind_out (MulCell.shape_call _ hg
    (Affine.add (affine_half _ hchord _) hm1h)) fun h1h => ?_
  have hh1h := MulCell.affine_call_output _ h1h
  refine IsR1CSCirc.bind_out (MulCell.shape_call _ hc
    (Affine.sub (affine_limb _ hyeq _) (affine_limb _ huni _))) fun mu0 => ?_
  have hmu0 := MulCell.affine_call_output _ mu0
  refine IsR1CSCirc.bind_out (MulCell.shape_call _ hg
    (Affine.add (affine_limb _ huni _) hmu0)) fun l0 => ?_
  have hl0 := MulCell.affine_call_output _ l0
  refine IsR1CSCirc.bind_out (MulCell.shape_call _ hc
    (Affine.sub (affine_limb _ hyeq _) (affine_limb _ huni _))) fun mu1 => ?_
  have hmu1 := MulCell.affine_call_output _ mu1
  refine IsR1CSCirc.bind_out (MulCell.shape_call _ hg
    (Affine.add (affine_limb _ huni _) hmu1)) fun l1 => ?_
  have hl1 := MulCell.affine_call_output _ l1
  refine IsR1CSCirc.bind_out (MulCell.shape_call _ hc
    (Affine.sub (affine_limb _ hyeq _) (affine_limb _ huni _))) fun mu2 => ?_
  have hmu2 := MulCell.affine_call_output _ mu2
  refine IsR1CSCirc.bind_out (MulCell.shape_call _ hg
    (Affine.add (affine_limb _ huni _) hmu2)) fun l2 => ?_
  have hl2 := MulCell.affine_call_output _ l2
  refine IsR1CSCirc.bind_out (MulCell.shape_call _ hg hz) fun gz => ?_
  have hgz := MulCell.affine_call_output _ gz
  refine IsR1CSCirc.bind_out (MulCell.shape_call _ hgz (affine_half _ hxeq2 _)) fun hxl => ?_
  have hhxl := MulCell.affine_call_output _ hxl
  refine IsR1CSCirc.bind_out (MulCell.shape_call _ hgz (affine_half _ hxeq2 _)) fun hxh => ?_
  have hhxh := MulCell.affine_call_output _ hxh
  refine IsR1CSCirc.bind_out (MulCell.shape_call _ (Affine.add hc hz)
    (affine_half _ hrel2 _)) fun m2l => ?_
  have hm2l := MulCell.affine_call_output _ m2l
  refine IsR1CSCirc.bind_out (MulCell.shape_call _ hg
    (Affine.sub (affine_half _ hrel2 _) hm2l)) fun h2l => ?_
  have hh2l := MulCell.affine_call_output _ h2l
  refine IsR1CSCirc.bind_out (MulCell.shape_call _ (Affine.add hc hz)
    (affine_half _ hrel2 _)) fun m2h => ?_
  have hm2h := MulCell.affine_call_output _ m2h
  refine IsR1CSCirc.bind_out (MulCell.shape_call _ hg
    (Affine.sub (affine_half _ hrel2 _) hm2h)) fun h2h => ?_
  have hh2h := MulCell.affine_call_output _ h2h
  refine IsR1CSCirc.bind (IsR1CSCirc.assertion (Cert.shape .rel1 _ ?_)) fun _ => ?_
  · exact affineW_pair hh1l hh1h
  refine IsR1CSCirc.bind (IsR1CSCirc.assertion (Cert3.shape _ ?_)) fun _ => ?_
  · exact affineW_triple hl0 hl1 hl2
  refine IsR1CSCirc.bind (IsR1CSCirc.assertion (Cert.shape .xeq _ ?_)) fun _ => ?_
  · exact affineW_pair hhxl hhxh
  exact IsR1CSCirc.assertion (Cert.shape .rel2 _ (affineW_pair hh2l hh2h))

theorem shape_call (n : ℕ) (hn : n ≤ depth) (i : Var Inputs Field) (hi : AffineInput i) :
    IsR1CSCirc (assertion (circuit n hn) i) :=
  IsR1CSCirc.assertion (fun n => shape i hi n)

end Solution.Secp256k1ScalarMulFixedBase.LazyVar.Certs
