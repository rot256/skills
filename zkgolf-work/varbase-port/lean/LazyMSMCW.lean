import Solution.Secp256k1ScalarMul.Lazy.LazyMSMShape
import Solution.Secp256k1ScalarMul.Lazy.StepCW
import Solution.Secp256k1ScalarMul.VarLookupCW

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
    Vector.map (fun v => Vector.map (Expression.eval e.toEnvironment) v) i.tx =
        Vector.map (fun v => Vector.map (Expression.eval e'.toEnvironment) v) i.tx ∧
    Vector.map (fun v => Vector.map (Expression.eval e.toEnvironment) v) i.ty =
        Vector.map (fun v => Vector.map (Expression.eval e'.toEnvironment) v) i.ty ∧
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
    (k : Fin 64) : (stepBody input acc k).localLength = 1622 := by
  funext n; exact stepBody_localLength input acc k n

lemma mulCell_localLength (i : Var MulCell.Inputs (F circomPrime)) (o : ℕ) :
    (subcircuit MulCell.circuit i).localLength o = 1 := by
  simp only [MulCell.circuit, MulCell.elaborated, circuit_norm]

lemma cert_localLength (l : VarLayout) (x : Var (fields 2) (F circomPrime)) (o : ℕ) :
    (assertion (Cert.circuit l) x).localLength o = qbits l + tbits l - 2 := by
  simp +arith only [Cert.circuit, Cert.elaborated, RangeCheck.circuit, circuit_norm]

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

theorem computableWitnesses : circuit.base.ComputableWitnesses := by
  intro o input env env'
  change Operations.forAllFlat o (FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations o)
  apply FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  simp only [main, Circuit.bind_structuralComputableWitnesses_iff,
    Circuit.foldlRange_structuralComputableWitnesses_iff,
    Circuit.assertZero_structuralComputableWitnesses_iff,
    stepBody_localLength'', mulCell_localLength, cert_localLength, true_and, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the fold
    intro i
    simp only [stepBody, Circuit.bind_structuralComputableWitnesses_iff,
      GLVMSM.varLookup_localLength, foldlAcc_eq_accL]
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
      simp only [circuit_norm] at hk
      simp only [GLVMSM.varLookup_output, spE, seed, Step.outputAt, circuit_norm,
        Step.Inputs.mk.injEq, Step.LazyPt.mk.injEq,
        Solution.Secp256k1ScalarMul.FlaggedPoint.mk.injEq, Products.map_embedExpr, h15x, h15y, h15i]
      rcases i with ⟨iv, hiv⟩
      cases iv with
      | zero =>
          simp only [accL, seed, circuit_norm, Products.map_embedExpr, h15x, h15y, h15i, and_self,
            true_and]
          simp (disch := omega) only [hag', hmap, and_self, true_and]
      | succ j =>
          simp only [accL_succ, Step.outputAt, circuit_norm, and_self, true_and]
          simp (disch := omega) only [hag', hmap, and_self, true_and]
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
    simp only [circuit_norm, dif_pos (show (0:ℕ) < 64 by norm_num)] at hk
    simp only [circuit_norm, dif_pos (show (0:ℕ) < 64 by norm_num), stepBody_output',
      stepBody_localLength', fin_foldl_eq_accL, accL_succ, Step.outputAt, spE,
      MulCell.call_output, mulCell_output', MulCell.Inputs.mk.injEq, Certs.eval_half,
      Products.map_vsubE, Products.map_embedExpr, h15x, h15y, h15i, true_and, and_true]
    simp (disch := omega) only [hag', hmap, and_self, true_and]

end Solution.Secp256k1ScalarMul.LazyMSM
