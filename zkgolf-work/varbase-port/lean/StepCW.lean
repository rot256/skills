import Solution.Secp256k1ScalarMul.Lazy.StepOutput
import Solution.Secp256k1ScalarMul.Lazy.CertsCost
import Solution.Secp256k1ScalarMul.Lazy.CertsCW
import Solution.Secp256k1ScalarMul.Lazy.ProductsCW
import Solution.Secp256k1ScalarMul.Lazy.MuxVecCW
import Solution.Secp256k1ScalarMul.Lazy.NormalizeCW

/-! Computable witnesses of one chain step. -/

namespace Solution.Secp256k1ScalarMulFixedBase.LazyVar.Step

open SmallSquare Sparse32 SparseX
open Solution.Secp256k1ScalarMul.Lazy
open Solution.Secp256k1ScalarMulFixedBase.LazyVar
open Challenge.Utils.ComputableWitnessLemmas

set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 20000

lemma input_parts (i : Var Inputs Field) {e e' : ProverEnvironment Field}
    (h : eval e i = eval e' i) :
    Vector.map (Expression.eval e.toEnvironment) i.acc.x =
        Vector.map (Expression.eval e'.toEnvironment) i.acc.x ∧
    Vector.map (Expression.eval e.toEnvironment) i.acc.y =
        Vector.map (Expression.eval e'.toEnvironment) i.acc.y ∧
    Expression.eval e.toEnvironment i.acc.isInf = Expression.eval e'.toEnvironment i.acc.isInf ∧
    Vector.map (Expression.eval e.toEnvironment) i.t.x =
        Vector.map (Expression.eval e'.toEnvironment) i.t.x ∧
    Vector.map (Expression.eval e.toEnvironment) i.t.y =
        Vector.map (Expression.eval e'.toEnvironment) i.t.y ∧
    Expression.eval e.toEnvironment i.t.isInf = Expression.eval e'.toEnvironment i.t.isInf ∧
    Expression.eval e.toEnvironment i.sp = Expression.eval e'.toEnvironment i.sp := by
  have hi : eval e.toEnvironment i = eval e'.toEnvironment i := by
    simpa only [circuit_norm] using h
  simp only [circuit_norm, Inputs.mk.injEq, LazyPt.mk.injEq,
    Solution.Secp256k1ScalarMul.FlaggedPoint.mk.injEq] at hi
  exact ⟨hi.1.1, hi.1.2.1, hi.1.2.2, hi.2.1.1, hi.2.1.2.1, hi.2.1.2.2, hi.2.2⟩

lemma normalize_localLength (raw : Var Emu Field) (k : ℕ) :
    (Sparse32Normalize.circuit raw).localLength k = 252 := by
  simp only [Sparse32Normalize.circuit, Sparse32Normalize.elaborated, circuit_norm]

lemma products_localLength (x : Var Products.Inputs Field) (k : ℕ) :
    (subcircuit Products.circuit x).localLength k = 96 := by
  simp only [Products.circuit, Products.elaborated, circuit_norm]

lemma certs_localLength (n : ℕ) (hn : n ≤ depth) (x : Var Certs.Inputs Field) (k : ℕ) :
    (assertion (Certs.circuit n hn) x).localLength k = 839 := by
  simp only [Certs.circuit, Certs.elaborated, Certs.main, MulCell.circuit, MulCell.elaborated,
    Cert.circuit, Cert3.circuit, RangeCheck.circuit, circuit_norm]

lemma mux_localLength (x : Var MuxVec.Inputs Field) (k : ℕ) :
    (subcircuit MuxVec.circuit x).localLength k = 8 := by
  simp only [MuxVec.circuit, MuxVec.elaborated, circuit_norm]

lemma fl_component (o : ℕ) (j : ℕ) (hj : j < 2) (i : Var Inputs Field)
    {k : ℕ} {e e' : ProverEnvironment Field} (hag : e.AgreesBelow k e') (hk : o + 2 ≤ k) :
    Expression.eval e.toEnvironment
        (((ProvableType.witness (α := fields 2) fun env => flagsW (eval env i)).output o :
          Var (fields 2) Field)[j]'hj) =
      Expression.eval e'.toEnvironment
        (((ProvableType.witness (α := fields 2) fun env => flagsW (eval env i)).output o :
          Var (fields 2) Field)[j]'hj) := by
  have h := CWHelpers.fieldsWitnessOutput_stable (fun env => flagsW (eval env i)) hag hk
  have h' := congrArg (fun v : fields 2 Field => v[j]'hj) h
  simpa only [circuit_norm, Vector.getElem_map] using h'

theorem computableWitnesses (n : ℕ) (hn : n + 1 ≤ depth) : (circuit n hn).base.ComputableWitnesses := by
  intro o input env env'
  change Operations.forAllFlat o (FormalCircuitBase.computableWitnessCondition input env env')
    ((main n hn input).operations o)
  apply FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  simp only [main, Circuit.bind_structuralComputableWitnesses_iff,
    Circuit.provableWitness_structuralComputableWitnesses_iff,
    Circuit.assertZero_structuralComputableWitnesses_iff,
    Circuit.pure_structuralComputableWitnesses_iff,
    normalize_localLength, Certs.mulCell_localLength, products_localLength, certs_localLength,
    mux_localLength, add_zero, true_and, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (intro _ hi; rw [hi])
    | (intro hi; rw [hi])
    | (simp only [subcircuitWithAssertion, FormalCircuitBase.Operations.StructuralComputableWitnesses,
         Circuit.operations, and_true]
       apply GeneralFormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
       rotate_left
       exact Sparse32Normalize.computableWitnesses)
    | (rw [FormalAssertion.assertion_structuralComputableWitnesses_iff]
       apply FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
       rotate_left
       exact Certs.computableWitnesses n (Nat.le_of_succ_le hn))
    | (rw [FormalCircuit.subcircuit_structuralComputableWitnesses_iff]
       apply FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
       rotate_left
       first | exact MulCell.computableWitnesses | exact Products.computableWitnesses
             | exact MuxVec.computableWitnesses)
  all_goals
    intro k e e' hk hag hi
    simp only [circuit_norm, numLimbs, List.sum_cons, List.sum_nil, Nat.reduceAdd] at hk
    obtain ⟨hax, hay, hai, htx, hty, hti, hsp⟩ := input_parts input hi
    have hl1 := CWHelpers.emuWitnessOutput_stable (fun env => lam1W (eval env input)) hag
      (by simp only [numLimbs]; omega)
    have hl2 := CWHelpers.emuWitnessOutput_stable (fun env => lam2W (eval env input)) hag
      (by simp only [numLimbs]; omega)
    have ha := Sparse32Normalize.call_output_stable _ hl1 hag (by omega)
    have hb := Sparse32Normalize.call_output_stable _ hl2 hag (by omega)
    have hc := fl_component (o + 4 + 252 + 4 + 252) 0 (by decide) input hag (by omega)
    have hz := fl_component (o + 4 + 252 + 4 + 252) 1 (by decide) input hag (by omega)
    have hg := MulCell.output_stable _ (o + 4 + 252 + 4 + 252 + 2) hag (by omega)
    have hp := Products.call_output_stable _ (o + 4 + 252 + 4 + 252 + 2 + 1) hag (by omega)
    have hrt := MulCell.output_stable _ (o + 4 + 252 + 4 + 252 + 2 + 1 + 96 + 839) hag (by omega)
    have hzrt := MulCell.output_stable _ (o + 4 + 252 + 4 + 252 + 2 + 1 + 96 + 839 + 1) hag (by omega)
    have hxw := MuxVec.call_output_stable _ (o + 4 + 252 + 4 + 252 + 2 + 1 + 96 + 839 + 1 + 1) hag
      (by omega)
    have hxv := MuxVec.call_output_stable _ (o + 4 + 252 + 4 + 252 + 2 + 1 + 96 + 839 + 1 + 1 + 8) hag
      (by omega)
    have hyw := MuxVec.call_output_stable _
      (o + 4 + 252 + 4 + 252 + 2 + 1 + 96 + 839 + 1 + 1 + 8 + 8 + 8) hag (by omega)
    have hyv := MuxVec.call_output_stable _
      (o + 4 + 252 + 4 + 252 + 2 + 1 + 96 + 839 + 1 + 1 + 8 + 8 + 8 + 8) hag (by omega)
    simp only [circuit_norm, Vector.getElem_map] at hl1 hl2 ha hb hg hp hrt hzrt hxw hxv hyw hyv
    simp only [circuit_norm, Inputs.mk.injEq, LazyPt.mk.injEq,
      Solution.Secp256k1ScalarMul.FlaggedPoint.mk.injEq, MulCell.Inputs.mk.injEq,
      Products.Inputs.mk.injEq, Certs.Inputs.mk.injEq, MuxVec.Inputs.mk.injEq,
      Products.map_vaddE, Products.map_vsubE, Products.map_embedExpr,
      hax, hay, hai, htx, hty, hti, hsp, hl1, hl2, ha, hb, hc, hz, hg, hp, hrt, hzrt,
      hxw, hxv, hyw, hyv, and_self]

end Solution.Secp256k1ScalarMulFixedBase.LazyVar.Step
