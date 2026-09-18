import Solution.Secp256k1ScalarMul.Lazy.Certs
import Solution.Secp256k1ScalarMul.Lazy_Donor7

/-! ## merged from `Lazy/CertsCost.lean` -/
section
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

end Solution.Secp256k1ScalarMulFixedBase.LazyVar.Certs
end

/-! ## merged from `Lazy/CertsShape.lean` -/
section
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
  AffineW i.p.pa ∧ AffineW i.p.pu ∧ AffineW i.p.qxt ∧
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
  obtain ⟨ha, hb, hx, hy, htx, hty, hpa, hpu, hqxt, hsa, hpab, hsb, hpb, hg, hc, hz⟩ := hi
  have hetx := affine_embedExpr i.tx htx
  have hety := affine_embedExpr i.ty hty
  have hchord : AffineW (chordW i) :=
    Products.affine_vaddE _ _ (Products.affine_vsubE _ _ hpa hety) hy
  have hxeq1 : AffineW (xeq1W i) := Products.affine_vsubE _ _ hx hetx
  have huni : AffineW (uniW i) :=
    Products.affine_vsubE _ _ hpu hqxt
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
end

/-! ## merged from `Lazy/CertsCW.lean` -/
section
/-! Computable witnesses of the certificate-slot assertion. -/

namespace Solution.Secp256k1ScalarMulFixedBase.LazyVar.Certs

open SmallSquare Sparse32 SparseX
open Solution.Secp256k1ScalarMul.Lazy
open Solution.Secp256k1ScalarMulFixedBase.LazyVar
open Challenge.Utils.ComputableWitnessLemmas

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

/-- Native value of a half of an evaluated word vector. -/
def halfN (w : fields 8 Field) (side : Bool) : Field :=
  if side then Sparse32.highHalf (fun k => w[k.val]) else Sparse32.lowHalf (fun k => w[k.val])

def limbN (w : fields 8 Field) (j : Fin 3) : Field :=
  if j.val = 0 then w[0] + (H : Field) * w[1] + (H ^ 2 : Field) * w[2]
  else if j.val = 1 then w[3] + (H : Field) * w[4] + (H ^ 2 : Field) * w[5]
  else w[6] + (H : Field) * w[7]

lemma eval_half (env : Environment Field) (w : Var (fields 8) Field) (side : Bool) :
    Expression.eval env (half w side) = halfN (Vector.map (Expression.eval env) w) side := by
  rw [half, Sparse32Wide.eval_productHalfExpr]
  simp only [halfN, circuit_norm, Vector.getElem_map]

lemma eval_limb (env : Environment Field) (w : Var (fields 8) Field) (j : Fin 3) :
    Expression.eval env (limb w j) = limbN (Vector.map (Expression.eval env) w) j := by
  fin_cases j <;>
    simp only [limb, limbN, circuit_norm, Expression.eval, Fin.isValue, Fin.val_zero,
      Fin.val_one, Fin.val_two, Nat.one_ne_zero, Nat.succ_ne_self, OfNat.ofNat_ne_zero,
      OfNat.ofNat_ne_one, Nat.reduceEqDiff, ↓reduceIte, Vector.getElem_map]

lemma payload_stable (i : Var Inputs Field) {e e' : ProverEnvironment Field}
    (h : eval e i = eval e' i) :
    Vector.map (Expression.eval e.toEnvironment) (chordW i) =
      Vector.map (Expression.eval e'.toEnvironment) (chordW i) ∧
    Vector.map (Expression.eval e.toEnvironment) (xeq1W i) =
      Vector.map (Expression.eval e'.toEnvironment) (xeq1W i) ∧
    Vector.map (Expression.eval e.toEnvironment) (uniW i) =
      Vector.map (Expression.eval e'.toEnvironment) (uniW i) ∧
    Vector.map (Expression.eval e.toEnvironment) (yeqW i) =
      Vector.map (Expression.eval e'.toEnvironment) (yeqW i) ∧
    Vector.map (Expression.eval e.toEnvironment) (xeq2W i) =
      Vector.map (Expression.eval e'.toEnvironment) (xeq2W i) ∧
    Vector.map (Expression.eval e.toEnvironment) (rel2W i) =
      Vector.map (Expression.eval e'.toEnvironment) (rel2W i) ∧
    Expression.eval e.toEnvironment i.gate = Expression.eval e'.toEnvironment i.gate ∧
    Expression.eval e.toEnvironment i.cflag = Expression.eval e'.toEnvironment i.cflag ∧
    Expression.eval e.toEnvironment i.zflag = Expression.eval e'.toEnvironment i.zflag := by
  have hi : eval e.toEnvironment i = eval e'.toEnvironment i := by
    simpa only [circuit_norm] using h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 := map_chordW e.toEnvironment i
    have h2 := map_chordW e'.toEnvironment i
    rw [h1, h2, hi]
  · have h1 := map_xeq1W e.toEnvironment i
    have h2 := map_xeq1W e'.toEnvironment i
    rw [h1, h2, hi]
  · have h1 := map_uniW e.toEnvironment i
    have h2 := map_uniW e'.toEnvironment i
    rw [h1, h2, hi]
  · have h1 := map_yeqW e.toEnvironment i
    have h2 := map_yeqW e'.toEnvironment i
    rw [h1, h2, hi]
  · have h1 := map_xeq2W e.toEnvironment i
    have h2 := map_xeq2W e'.toEnvironment i
    rw [h1, h2, hi]
  · have h1 := map_rel2W e.toEnvironment i
    have h2 := map_rel2W e'.toEnvironment i
    rw [h1, h2, hi]
  · simpa only [circuit_norm] using congrArg Inputs.gate hi
  · simpa only [circuit_norm] using congrArg Inputs.cflag hi
  · simpa only [circuit_norm] using congrArg Inputs.zflag hi

lemma mulCell_localLength (i : Var MulCell.Inputs Field) (o : ℕ) :
    (subcircuit MulCell.circuit i).localLength o = 1 := by
  simp only [MulCell.circuit, MulCell.elaborated, circuit_norm]

theorem computableWitnesses (n : ℕ) (hn : n ≤ depth) : (circuit n hn).ComputableWitnesses := by
  intro o input env env'
  change Operations.forAllFlat o (FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations o)
  apply FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  simp only [main, Circuit.bind_structuralComputableWitnesses_iff,
    mulCell_localLength, MulCell.call_output]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (rw [FormalCircuit.subcircuit_structuralComputableWitnesses_iff]
       apply FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
       rotate_left
       exact MulCell.computableWitnesses)
    | (rw [FormalAssertion.assertion_structuralComputableWitnesses_iff]
       apply FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
       rotate_left
       first | exact Cert.computableWitnesses _ | exact Cert3.computableWitnesses)
  all_goals
    intro k e e' hk hag hp
    have he := payload_stable input hp
    have hag' : ∀ j, j < k → e.get j = e'.get j := hag
    simp only [Cert.circuit, Cert3.circuit, Cert.elaborated, Cert3.elaborated, circuit_norm] at hk
    simp only [circuit_norm, MulCell.Inputs.mk.injEq, eval_half, eval_limb,
      he.1, he.2.1, he.2.2.1, he.2.2.2.1, he.2.2.2.2.1, he.2.2.2.2.2.1,
      he.2.2.2.2.2.2.1, he.2.2.2.2.2.2.2.1, he.2.2.2.2.2.2.2.2]
    all_goals simp (disch := omega) only [hag']

end Solution.Secp256k1ScalarMulFixedBase.LazyVar.Certs
end
