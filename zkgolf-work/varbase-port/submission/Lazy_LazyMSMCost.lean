import Solution.Secp256k1ScalarMul.Lazy_LazyMSMFold
import Solution.Secp256k1ScalarMul.VarLookupCW
import Solution.Secp256k1ScalarMul.Lazy_StepCost
import Solution.Secp256k1ScalarMul.Lazy_StepCW

/-! ## merged from `Lazy/LazyMSMCost.lean` -/
section
/-! The lazy chain as a `GeneralFormalCircuit`, its cost and its local length. -/

namespace Solution.Secp256k1ScalarMul.LazyMSM

open Specs.ShortWeierstrass Specs.Secp256k1
open Solution.Secp256k1ScalarMulFixedBase.SparseX
open Solution.Secp256k1ScalarMulFixedBase.LazyVar
open Solution.Secp256k1ScalarMul.Lazy
open Challenge.CostR1CS Cost

set_option maxHeartbeats 4000000

noncomputable def circuit : GeneralFormalCircuit (F circomPrime) Inputs unit where
  main := main
  Assumptions := fun i _ => Assumptions i
  Spec := fun i _ _ => Spec i
  ProverAssumptions := fun i _ _ => ProverAssumptions i
  ProverSpec := fun _ _ _ => True
  soundness := soundness
  completeness := completeness

/-- `64 · 1622 + 4 + 176 + 176` allocations, `64 · 1635 + 1 + 4 + 178 + 178 + 4` rows. -/
def cost : Count := ⟨104164, 105005⟩

lemma stepBody_cost (input : Var Inputs (F circomPrime)) (acc : Var LazyPt (F circomPrime))
    (k : Fin 64) : CostIs (stepBody input acc k) ⟨1622, 1635⟩ := by
  rw [show (⟨1622, 1635⟩ : Count) = varLookupCost + Step.stepCost from by decide]
  unfold stepBody
  exact CostIs.bind (costIs_sub_varLookup _) fun t => Step.costIs_call _ _ _

theorem costIs_main (input : Var Inputs (F circomPrime)) : CostIs (main input) cost := by
  rw [show cost = ⟨64 * 1622, 64 * 1635⟩ + (⟨0, 1⟩ + (⟨1, 1⟩ + (⟨1, 1⟩ +
    (⟨qbits .rel1 + tbits .rel1 - 2, qbits .rel1 + tbits .rel1⟩ + (⟨1, 1⟩ + (⟨1, 1⟩ +
    (⟨qbits .fin + tbits .fin - 2, qbits .fin + tbits .fin⟩ + (⟨0, 1⟩ + (⟨0, 1⟩ + (⟨0, 1⟩ +
    ⟨0, 1⟩)))))))))) from by decide]
  dsimp only [main]
  refine CostIs.bind (CostIs.foldlRange fun acc k n => stepBody_cost input acc k n) fun _ => ?_
  refine CostIs.bind (CostIs.assertZero _) fun _ => ?_
  refine CostIs.bind (MulCell.costIs_call _) fun _ => ?_
  refine CostIs.bind (MulCell.costIs_call _) fun _ => ?_
  refine CostIs.bind (CostIs.assertion (Cert.cost .rel1 _)) fun _ => ?_
  refine CostIs.bind (MulCell.costIs_call _) fun _ => ?_
  refine CostIs.bind (MulCell.costIs_call _) fun _ => ?_
  refine CostIs.bind (CostIs.assertion (Cert.cost .fin _)) fun _ => ?_
  refine CostIs.bind (CostIs.assertZero _) fun _ => ?_
  refine CostIs.bind (CostIs.assertZero _) fun _ => ?_
  refine CostIs.bind (CostIs.assertZero _) fun _ => ?_
  exact CostIs.assertZero _

theorem costIs_call (input : Var Inputs (F circomPrime)) :
    CostIs (subcircuitWithAssertion circuit input) cost :=
  CostIs.subcircuitWithAssertion (fun n => costIs_main input n)

lemma localLength (input : Var Inputs (F circomPrime)) (n : ℕ) :
    (main input).localLength n = 104164 := by
  simp +arith only [main, circuit_norm, stepBody_localLength', dif_pos True.intro, MulCell.circuit,
    MulCell.elaborated, Cert.circuit, Cert.elaborated, RangeCheck.circuit, qbits, tbits,
    Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul]

lemma circuit_localLength (input : Var Inputs (F circomPrime)) :
    circuit.localLength input = 104164 := by
  rw [show circuit.localLength input = (main input).localLength 0 from
    (elaborated.localLength_eq input 0).symm]
  exact localLength input 0

end Solution.Secp256k1ScalarMul.LazyMSM
end

/-! ## merged from `Lazy/LazyMSMShape.lean` -/
section
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
end

/-! ## merged from `Lazy/LazyMSMCW.lean` -/
section
/-! Computable witnesses of the lazy chain. -/

namespace Solution.Secp256k1ScalarMul.LazyMSM

open Specs.ShortWeierstrass Specs.Secp256k1
open Solution.Secp256k1ScalarMulFixedBase.SparseX
open Solution.Secp256k1ScalarMulFixedBase.LazyVar
open Solution.Secp256k1ScalarMul.Lazy
open Challenge.Utils.ComputableWitnessLemmas

set_option maxHeartbeats 16000000
set_option maxRecDepth 20000

abbrev PE := ProverEnvironment (F circomPrime)

lemma input_parts (i : Var Inputs (F circomPrime)) {e e' : PE} (h : eval e i = eval e' i) :
    Vector.map (eval e.toEnvironment) i.tx = Vector.map (eval e'.toEnvironment) i.tx ∧
    Vector.map (eval e.toEnvironment) i.ty = Vector.map (eval e'.toEnvironment) i.ty ∧
    Vector.map (Expression.eval e.toEnvironment) i.tinf =
        Vector.map (Expression.eval e'.toEnvironment) i.tinf ∧
    Vector.map (Expression.eval e.toEnvironment) i.m0 =
        Vector.map (Expression.eval e'.toEnvironment) i.m0 ∧
    Vector.map (Expression.eval e.toEnvironment) i.m1 =
        Vector.map (Expression.eval e'.toEnvironment) i.m1 ∧
    Vector.map (Expression.eval e.toEnvironment) i.m2 =
        Vector.map (Expression.eval e'.toEnvironment) i.m2 ∧
    Vector.map (Expression.eval e.toEnvironment) i.m3 =
        Vector.map (Expression.eval e'.toEnvironment) i.m3 := by
  have hi : eval e.toEnvironment i = eval e'.toEnvironment i := by
    simpa only [circuit_norm] using h
  simpa only [circuit_norm, GLVMSM.Inputs.mk.injEq, eval_vector] using hi

lemma vec_component {m : ℕ} {α : Type} (f g : Expression (F circomPrime) → α)
    (v : Vector (Expression (F circomPrime)) m)
    (h : Vector.map f v = Vector.map g v) (j : ℕ) (hj : j < m) : f v[j] = g v[j] := by
  have := Vector.ext_iff.mp h j hj
  simpa only [Vector.getElem_map] using this

lemma vecvec_component {m : ℕ} {α β : Type} (f g : β → α) (v : Vector β m)
    (h : Vector.map f v = Vector.map g v) (j : ℕ) (hj : j < m) : f v[j] = g v[j] := by
  have := Vector.ext_iff.mp h j hj
  simpa only [Vector.getElem_map] using this

lemma stepBody_localLength'' (input : Var Inputs (F circomPrime)) (acc : Var LazyPt (F circomPrime))
    (k : Fin 64) : (stepBody input acc k).localLength = 1622 :=
  stepBody_localLength input acc k 0

lemma mulCell_localLength (i : Var MulCell.Inputs (F circomPrime)) (o : ℕ) :
    (subcircuit MulCell.circuit i).localLength o = 1 := by
  simp only [MulCell.circuit, MulCell.elaborated, circuit_norm]

lemma cert_localLength (l : VarLayout) (x : Var (fields 2) (F circomPrime)) (o : ℕ) :
    (assertion (Cert.circuit l) x).localLength o = qbits l - 1 + (tbits l - 1) := by
  simp only [Cert.circuit, Cert.elaborated, circuit_norm]

lemma mapRange_var_stable (m n : ℕ) {k : ℕ} {e e' : PE}
    (hag : e.AgreesBelow k e') (hk : n + m ≤ k) :
    Vector.map (Expression.eval e.toEnvironment) (Vector.mapRange m fun i => var { index := n + i }) =
      Vector.map (Expression.eval e'.toEnvironment) (Vector.mapRange m fun i => var { index := n + i }) := by
  apply Vector.ext
  intro j hj
  simp only [Vector.getElem_map, Vector.getElem_mapRange, Expression.eval]
  exact hag (n + j) (by omega)

lemma mulCell_output' (i : Var MulCell.Inputs (F circomPrime)) (n : ℕ) :
    MulCell.circuit.output i n = varFromOffset field n := MulCell.call_output i n

lemma map_embedExpr' (env : Environment (F circomPrime)) (x : Var Emu (F circomPrime)) :
    Vector.map (Expression.eval env) (embedExpr x) = embedVec (Vector.map (Expression.eval env) x) :=
  Products.map_embedExpr env x

lemma map_vsubE' (env : Environment (F circomPrime)) (u v : Var (fields 8) (F circomPrime)) :
    Vector.map (Expression.eval env) (Products.vsubE u v) =
      Products.vsub (Vector.map (Expression.eval env) u) (Vector.map (Expression.eval env) v) :=
  Products.map_vsubE env u v

lemma eval_half' (env : Environment (F circomPrime)) (w : Var (fields 8) (F circomPrime)) (side : Bool) :
    Expression.eval env (Certs.half w side) = Certs.halfN (Vector.map (Expression.eval env) w) side :=
  Certs.eval_half env w side

lemma mulCell_localLength' (i : Var MulCell.Inputs (F circomPrime)) :
    @FormalCircuitBase.localLength (F circomPrime) _ MulCell.Inputs field _ _
      (@FormalCircuit.base (F circomPrime) _ MulCell.Inputs field _ _ MulCell.circuit) i = 1 := rfl

lemma mulCell_output'' (i : Var MulCell.Inputs (F circomPrime)) (n : ℕ) :
    @FormalCircuitBase.output (F circomPrime) _ MulCell.Inputs field _ _
      (@FormalCircuit.base (F circomPrime) _ MulCell.Inputs field _ _ MulCell.circuit) i n =
      varFromOffset field n := MulCell.call_output i n

lemma cert_localLength' (l : VarLayout) (x : Var (fields 2) (F circomPrime)) :
    @FormalCircuitBase.localLength (F circomPrime) _ (fields 2) unit _ _
      (@FormalAssertion.base (F circomPrime) (fields 2) _ _ (Cert.circuit l)) x =
      qbits l - 1 + (tbits l - 1) := cert_localLength l x 0

lemma foldlAcc_eq_accL' (input : Var Inputs (F circomPrime)) (i₀ : ℕ) (i : Fin 64) :
    Circuit.FoldlM.foldlAcc (β := Var LazyPt (F circomPrime)) i₀ (Vector.finRange 64)
      (stepBody input) (seed input) i = accL input i₀ i.val :=
  foldlAcc_eq_accL input i₀ i

lemma fin_foldl_eq_accL' (input : Var Inputs (F circomPrime)) (i₀ : ℕ) :
    Fin.foldl 64 (fun (_ : Var LazyPt (F circomPrime)) (i : Fin 64) =>
      Step.outputAt (i₀ + i.val * 1622 + 122)) (seed input) = accL input i₀ 64 :=
  fin_foldl_ignore_acc 63 (fun v => Step.outputAt (i₀ + v * 1622 + 122)) (seed input)

theorem structuralComputableWitnesses (o : ℕ) (input : Var Inputs (F circomPrime))
    (env env' : PE) :
    FormalCircuitBase.Operations.StructuralComputableWitnesses input env env' o
      ((main input).operations o) := by
  have h64 : (0 : ℕ) < 64 := by norm_num
  simp only [main, Circuit.bind_structuralComputableWitnesses_iff,
    Circuit.foldlRange_structuralComputableWitnesses_iff,
    Circuit.assertZero_structuralComputableWitnesses_iff,
    Circuit.foldlRange.localLength_eq, Circuit.foldlRange.output_eq, dif_pos h64,
    stepBody_localLength'', stepBody_output, fin_foldl_eq_accL, fin_foldl_eq_accL',
    mulCell_localLength, cert_localLength, qbits, tbits, true_and, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the fold
    intro i
    rcases i with ⟨iv, hiv⟩
    simp only [stepBody, Circuit.bind_structuralComputableWitnesses_iff,
      GLVMSM.varLookup_localLength, foldlAcc_eq_accL, foldlAcc_eq_accL', Fin.val_mk]
    refine ⟨?_, ?_⟩
    · rw [FormalCircuit.subcircuit_structuralComputableWitnesses_iff]
      apply FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      rotate_left
      · exact VarLookup.computableWitnesses
      intro k e e' hk hag hi
      obtain ⟨htx, hty, htinf, hm0, hm1, hm2, hm3⟩ := input_parts input hi
      simp only [lkInput, circuit_norm, VarLookup.Inputs.mk.injEq, eval_vector, htx, hty, htinf,
        true_and]
      exact ⟨vec_component _ _ _ hm3 _ _, vec_component _ _ _ hm2 _ _,
        vec_component _ _ _ hm1 _ _, vec_component _ _ _ hm0 _ _⟩
    · simp only [subcircuitWithAssertion, FormalCircuitBase.Operations.StructuralComputableWitnesses,
        Circuit.operations, and_true]
      apply GeneralFormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      rotate_left
      · exact Step.computableWitnesses _ _
      intro k e e' hk hag hi
      obtain ⟨htx, hty, htinf, hm0, hm1, hm2, hm3⟩ := input_parts input hi
      have hag' : ∀ j, j < k → e.get j = e'.get j := hag
      have hmap : ∀ m j, j + m ≤ k →
          Vector.map (Expression.eval e.toEnvironment) (Vector.mapRange m fun i => var { index := j + i }) =
          Vector.map (Expression.eval e'.toEnvironment) (Vector.mapRange m fun i => var { index := j + i }) :=
        fun m j h => mapRange_var_stable m j hag h
      have h15x := vecvec_component _ _ _ htx 15 (by norm_num)
      have h15y := vecvec_component _ _ _ hty 15 (by norm_num)
      have h15i := vec_component _ _ _ htinf 15 (by norm_num)
      simp only [circuit_norm, GLVMSM.varLookup_localLength, Fin.val_mk] at hk h15x h15y h15i
      simp only [GLVMSM.varLookup_output, spE, Step.outputAt, circuit_norm,
        Step.Inputs.mk.injEq, Step.LazyPt.mk.injEq,
        Solution.Secp256k1ScalarMul.FlaggedPoint.mk.injEq, map_embedExpr', h15x, h15y, h15i]
      cases iv with
      | zero =>
          simp only [accL, seed, circuit_norm, map_embedExpr', h15x, h15y, h15i, and_self,
            true_and]
          first | done | (simp (disch := (try simp only [numLimbs]); omega) only [hag', hmap, and_self, true_and]; done)
      | succ j =>
          simp only [accL_succ, Step.outputAt, circuit_norm, and_self, true_and]
          first | done | (simp (disch := (try simp only [numLimbs]); omega) only [hag', hmap, and_self, true_and]; done)
  all_goals first
    | (rw [FormalAssertion.assertion_structuralComputableWitnesses_iff]
       apply FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
       rotate_left
       exact Cert.computableWitnesses _)
    | (rw [FormalCircuit.subcircuit_structuralComputableWitnesses_iff]
       apply FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
       rotate_left
       exact MulCell.computableWitnesses)
  all_goals
    intro k e e' hk hag hi
    obtain ⟨htx, hty, htinf, hm0, hm1, hm2, hm3⟩ := input_parts input hi
    have hag' : ∀ j, j < k → e.get j = e'.get j := hag
    have hmap : ∀ m j, j + m ≤ k →
        Vector.map (Expression.eval e.toEnvironment) (Vector.mapRange m fun i => var { index := j + i }) =
        Vector.map (Expression.eval e'.toEnvironment) (Vector.mapRange m fun i => var { index := j + i }) :=
      fun m j h => mapRange_var_stable m j hag h
    have h15x := vecvec_component _ _ _ htx 15 (by norm_num)
    have h15y := vecvec_component _ _ _ hty 15 (by norm_num)
    have h15i := vec_component _ _ _ htinf 15 (by norm_num)
    simp only [circuit_norm, Cert.circuit, Cert.elaborated, qbits, tbits, mulCell_localLength'] at hk
    try simp only [circuit_norm] at h15x h15y h15i
    have hax := hmap 8 (o + 63 * 1622 + 122 + 1468) (by omega)
    have hay := hmap 8 (o + 63 * 1622 + 122 + 1492) (by omega)
    simp only [circuit_norm, accL_succ, Step.outputAt, spE,
      MulCell.call_output, mulCell_output', mulCell_output'', mulCell_localLength',
      cert_localLength', qbits, tbits,
      MulCell.Inputs.mk.injEq, eval_half', h15i, true_and, and_true]
    first
      | done
      | (rw [Products.map_vsubE, Products.map_vsubE, Products.map_embedExpr, Products.map_embedExpr]
         first | rw [hax, h15x] | rw [hay, h15y])
      | (simp (disch := omega) only [hag', and_self, true_and]; done)
      | (congr 1 <;> exact hag' _ (by omega))

attribute [local irreducible] main in
theorem computableWitnesses : circuit.base.ComputableWitnesses := by
  intro o input env env'
  change Operations.forAllFlat o (FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations o)
  exact FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses input env env'
    (structuralComputableWitnesses o input env env')

end Solution.Secp256k1ScalarMul.LazyMSM
end
