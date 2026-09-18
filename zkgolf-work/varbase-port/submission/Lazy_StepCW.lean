import Solution.Secp256k1ScalarMul.Lazy_StepCost
import Solution.Secp256k1ScalarMul.Lazy_CertsCost
import Solution.Secp256k1ScalarMul.Lazy_ProductsShape

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
  simp +arith only [Certs.circuit, Certs.elaborated, Certs.main, MulCell.circuit, MulCell.elaborated,
    Cert.circuit, Cert3.circuit, RangeCheck.circuit, circuit_norm, Secp256k1ScalarMul.Lazy.qbits,
    Secp256k1ScalarMul.Lazy.tbits, ukbits, ut0bits, ut1bits, Nat.reduceAdd, Nat.reduceSub]

lemma mux_localLength (x : Var MuxVec.Inputs Field) (k : ℕ) :
    (subcircuit MuxVec.circuit x).localLength k = 8 := by
  simp only [MuxVec.circuit, MuxVec.elaborated, circuit_norm]

lemma mapRange_var_stable (m n : ℕ) {k : ℕ} {e e' : ProverEnvironment Field}
    (hag : e.AgreesBelow k e') (hk : n + m ≤ k) :
    Vector.map (Expression.eval e.toEnvironment) (Vector.mapRange m fun i => var { index := n + i }) =
      Vector.map (Expression.eval e'.toEnvironment) (Vector.mapRange m fun i => var { index := n + i }) := by
  apply Vector.ext
  intro j hj
  simp only [Vector.getElem_map, Vector.getElem_mapRange, Expression.eval]
  exact hag (n + j) (by omega)

lemma mulCell_output' (i : Var MulCell.Inputs Field) (n : ℕ) :
    MulCell.circuit.output i n = varFromOffset field n := MulCell.call_output i n

lemma mux_output' (i : Var MuxVec.Inputs Field) (n : ℕ) :
    MuxVec.circuit.output i n = varFromOffset (fields 8) n := MuxVec.call_output i n

lemma map_eval_zeroVec (env : Environment Field) :
    Vector.map (Expression.eval env) zeroVec = Vector.ofFn (fun _ => (0 : Field)) := by
  apply Vector.ext
  intro j hj
  simp only [zeroVec, Vector.getElem_map, Vector.getElem_ofFn, Expression.eval]

abbrev lam1V (o : ℕ) : Var Emu Field := Vector.mapRange numLimbs fun i => var { index := o + i }
abbrev lam2V (o : ℕ) : Var Emu Field :=
  Vector.mapRange numLimbs fun i => var { index := o + numLimbs + 252 + i }
abbrev aV (o : ℕ) : Var (fields 8) Field := Sparse32Normalize.circuit.output (lam1V o) (o + numLimbs)
abbrev bV (o : ℕ) : Var (fields 8) Field :=
  Sparse32Normalize.circuit.output (lam2V o) (o + numLimbs + 252 + numLimbs)

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
    mux_localLength, true_and, and_true]
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
    simp only [circuit_norm, numLimbs] at hk
    obtain ⟨hax, hay, hai, htx, hty, hti, hsp⟩ := input_parts input hi
    have hag' : ∀ j, j < k → e.get j = e'.get j := hag
    have hmap : ∀ m j, j + m ≤ k →
        Vector.map (Expression.eval e.toEnvironment) (Vector.mapRange m fun i => var { index := j + i }) =
        Vector.map (Expression.eval e'.toEnvironment) (Vector.mapRange m fun i => var { index := j + i }) :=
      fun m j h => mapRange_var_stable m j hag h
    have ha : o + numLimbs + 252 ≤ k →
        Vector.map (Expression.eval e.toEnvironment) (aV o) =
        Vector.map (Expression.eval e'.toEnvironment) (aV o) := fun h => by
      have hl := hmap numLimbs o (by simp only [numLimbs] at h ⊢; omega)
      have := Sparse32Normalize.call_output_stable (n := o + numLimbs) (lam1V o)
        (by simpa only [circuit_norm] using hl) hag h
      simpa only [circuit_norm] using this
    have hb : o + numLimbs + 252 + numLimbs + 252 ≤ k →
        Vector.map (Expression.eval e.toEnvironment) (bV o) =
        Vector.map (Expression.eval e'.toEnvironment) (bV o) := fun h => by
      have hl := hmap numLimbs (o + numLimbs + 252) (by simp only [numLimbs] at h ⊢; omega)
      have := Sparse32Normalize.call_output_stable (n := o + numLimbs + 252 + numLimbs) (lam2V o)
        (by simpa only [circuit_norm] using hl) hag h
      simpa only [circuit_norm] using this
    have hp : o + numLimbs + 252 + numLimbs + 252 + 2 + 1 + 96 ≤ k →
        eval e ((subcircuit Products.circuit
          ⟨aV o, bV o, input.acc.x, input.acc.y, input.t.x, input.t.y⟩).output
          (o + numLimbs + 252 + numLimbs + 252 + 2 + 1)) =
        eval e' ((subcircuit Products.circuit
          ⟨aV o, bV o, input.acc.x, input.acc.y, input.t.x, input.t.y⟩).output
          (o + numLimbs + 252 + numLimbs + 252 + 2 + 1)) :=
      fun h => Products.call_output_stable _ _ hag h
    simp only [circuit_norm, MulCell.call_output, MuxVec.call_output, mulCell_output', mux_output',
      Inputs.mk.injEq,
      LazyPt.mk.injEq, Solution.Secp256k1ScalarMul.FlaggedPoint.mk.injEq, MulCell.Inputs.mk.injEq,
      Products.Inputs.mk.injEq, Certs.Inputs.mk.injEq, MuxVec.Inputs.mk.injEq,
      Products.Outputs.mk.injEq, Products.map_vaddE, Products.map_vsubE, Products.map_embedExpr,
      hax, hay, hai, htx, hty, hti, hsp, map_eval_zeroVec, and_self, true_and, and_true]
  all_goals first
    | done
    | (simp (disch := simp only [numLimbs]; omega) only [hag', hmap, ha, hb, and_self, true_and]
       done)
    | (have hp' := hp (by simp only [numLimbs]; omega)
       simp only [circuit_norm, Products.Outputs.mk.injEq] at hp'
       simp (disch := simp only [numLimbs]; omega) only [hag', hmap, ha, hb, hp'.1, hp'.2.1,
         hp'.2.2.1, hp'.2.2.2.1, hp'.2.2.2.2.1, hp'.2.2.2.2.2.1, hp'.2.2.2.2.2.2.1,
         hp'.2.2.2.2.2.2.2.1, hp'.2.2.2.2.2.2.2.2, and_self, true_and]
       done)

end Solution.Secp256k1ScalarMulFixedBase.LazyVar.Step
