import Solution.Secp256k1ScalarMul.GLVBuildTable
import Solution.Secp256k1ScalarMul.Cost
import Solution.Secp256k1ScalarMul.MulModBeta32Cost
import Solution.Secp256k1ScalarMul.NegYAffineSubCost
import Solution.Secp256k1ScalarMul.NegYAffineCW
import Challenge.Utils.ComputableWitnessLemmas

namespace Solution.Secp256k1ScalarMul

local notation "CF" => F circomPrime
local notation "PE" => ProverEnvironment CF
local notation "VI" => Var GLVBuildTable.Inputs CF
local notation "VP" => Var FlaggedPoint CF
open Challenge.Utils.ComputableWitnessLemmas

namespace Cost

open Challenge.CostR1CS

attribute [local irreducible] isR1CSRow r1csProducts operationsIsR1CS flatOperationsIsR1CS

def glvPrepareCost : Count := ⟨830, 838⟩

theorem costIs_glvPrepare
    (input : VI) :
    CostIs (GLVBuildTable.Prepare.main input) glvPrepareCost := by
  rw [show glvPrepareCost =
      mulModBeta32Cost +
      (mulModBeta32Cost +
      (NegYAffine.CostCert.cost + (NegYAffine.CostCert.cost +
      (⟨4, 4⟩ + (⟨4, 4⟩ + (⟨4, 4⟩ + Count.zero))))))
    from by decide]
  unfold GLVBuildTable.Prepare.main
  refine CostIs.bind (costIs_sub_mulModBeta32 _) fun _ => ?_
  refine CostIs.bind (costIs_sub_mulModBeta32 _) fun _ => ?_
  refine CostIs.bind (NegYAffine.CostCert.costIs_sub _) fun _ => ?_
  refine CostIs.bind (NegYAffine.CostCert.costIs_sub _) fun _ => ?_
  refine CostIs.bind (costIs_sub_mux _) fun _ => ?_
  refine CostIs.bind (costIs_sub_mux _) fun _ => ?_
  refine CostIs.bind (costIs_sub_mux _) fun _ => ?_
  exact CostIs.pure _

theorem costIs_sub_glvPrepare
    (input : VI) :
    CostIs (subcircuit GLVBuildTable.Prepare.circuit input) glvPrepareCost :=
  CostIs.subcircuit fun n => costIs_glvPrepare input n

private theorem isR1CS_glvPrepare
    (input : VI)
    (hP : AffineFP input.P) (hQ : AffineFP input.Q)
    (_hs0 : Affine input.sign0) (hs1 : Affine input.sign1)
    (hs2 : Affine input.sign2) (hs3 : Affine input.sign3) :
    IsR1CSCirc (GLVBuildTable.Prepare.main input) := by
  unfold GLVBuildTable.Prepare.main
  refine IsR1CSCirc.bind_out
    (isR1CS_sub_mulModBeta32 _ hP.1)
    fun npx => ?_
  refine IsR1CSCirc.bind_out
    (isR1CS_sub_mulModBeta32 _ hQ.1)
    fun nqx => ?_
  refine IsR1CSCirc.bind_out
    (NegYAffine.CostCert.isR1CS_sub input.P hP) fun npy => ?_
  refine IsR1CSCirc.bind_out
    (NegYAffine.CostCert.isR1CS_sub input.Q hQ) fun nqy => ?_
  have hphiP : AffineFP
      ({ x := (subcircuit MulModBeta32.circuit { a := input.P.x }).output npx,
         y := input.P.y, isInf := input.P.isInf } :
        VP) :=
    ⟨affineW_sub_mulModBeta32 _ _, hP.2.1, hP.2.2⟩
  have hphiQ : AffineFP
      ({ x := (subcircuit MulModBeta32.circuit { a := input.Q.x }).output nqx,
         y := input.Q.y, isInf := input.Q.isInf } :
        VP) :=
    ⟨affineW_sub_mulModBeta32 _ _, hQ.2.1, hQ.2.2⟩
  have hnP : AffineFP
      ({ x := input.P.x,
         y := (subcircuit NegYAffine.circuit input.P).output npy,
         isInf := input.P.isInf } : VP) :=
    ⟨hP.1, NegYAffine.CostCert.affineW_sub input.P _ hP, hP.2.2⟩
  have hnQ : AffineFP
      ({ x := input.Q.x,
         y := (subcircuit NegYAffine.circuit input.Q).output nqy,
         isInf := input.Q.isInf } : VP) :=
    ⟨hQ.1, NegYAffine.CostCert.affineW_sub input.Q _ hQ, hQ.2.2⟩
  have hnphiP : AffineFP
      ({ x := (subcircuit MulModBeta32.circuit { a := input.P.x }).output npx,
         y := (subcircuit NegYAffine.circuit input.P).output npy,
         isInf := input.P.isInf } : VP) :=
    ⟨affineW_sub_mulModBeta32 _ _, NegYAffine.CostCert.affineW_sub input.P _ hP,
      hP.2.2⟩
  have hnphiQ : AffineFP
      ({ x := (subcircuit MulModBeta32.circuit { a := input.Q.x }).output nqx,
         y := (subcircuit NegYAffine.circuit input.Q).output nqy,
         isInf := input.Q.isInf } : VP) :=
    ⟨affineW_sub_mulModBeta32 _ _, NegYAffine.CostCert.affineW_sub input.Q _ hQ,
      hQ.2.2⟩
  refine IsR1CSCirc.bind_out
    (isR1CS_sub_mux _ hs1 (NegYAffine.CostCert.affineW_sub input.P npy hP).affineProvable
      hP.2.1.affineProvable) fun _ => ?_
  refine IsR1CSCirc.bind_out
    (isR1CS_sub_mux _ hs2 (NegYAffine.CostCert.affineW_sub input.Q nqy hQ).affineProvable
      hQ.2.1.affineProvable) fun _ => ?_
  refine IsR1CSCirc.bind_out
    (isR1CS_sub_mux _ hs3 (NegYAffine.CostCert.affineW_sub input.Q nqy hQ).affineProvable
      hQ.2.1.affineProvable) fun _ => ?_
  exact IsR1CSCirc.pure _

theorem isR1CS_sub_glvPrepare
    (input : VI)
    (hP : AffineFP input.P) (hQ : AffineFP input.Q)
    (hs0 : Affine input.sign0) (hs1 : Affine input.sign1)
    (hs2 : Affine input.sign2) (hs3 : Affine input.sign3) :
    IsR1CSCirc (subcircuit GLVBuildTable.Prepare.circuit input) :=
  IsR1CSCirc.subcircuit fun n =>
    isR1CS_glvPrepare input hP hQ hs0 hs1 hs2 hs3 n

def baseEntryV (b : Var GLVBuildTable.Bases (CF)) :
    Fin 4 → VP
  | ⟨0, _⟩ => b.r0
  | ⟨1, _⟩ => b.r1
  | ⟨2, _⟩ => b.r2
  | ⟨3, _⟩ => b.r3

def rawEntryV (t : Var GLVBuildTable.RawTable (CF)) :
    Fin 16 → VP
  | ⟨0, _⟩ => t.t0 | ⟨1, _⟩ => t.t1 | ⟨2, _⟩ => t.t2 | ⟨3, _⟩ => t.t3
  | ⟨4, _⟩ => t.t4 | ⟨5, _⟩ => t.t5 | ⟨6, _⟩ => t.t6 | ⟨7, _⟩ => t.t7
  | ⟨8, _⟩ => t.t8 | ⟨9, _⟩ => t.t9 | ⟨10, _⟩ => t.t10 | ⟨11, _⟩ => t.t11
  | ⟨12, _⟩ => t.t12 | ⟨13, _⟩ => t.t13 | ⟨14, _⟩ => t.t14 | _ => t.t15

lemma affineTable_pack
    (raw : Var GLVBuildTable.RawTable (CF))
    (hr : ∀ i : Fin 16, AffineFP (rawEntryV raw i)) :
    AffineTableV (GLVBuildTable.Pack.pack raw).tx
      (GLVBuildTable.Pack.pack raw).ty (GLVBuildTable.Pack.pack raw).tinf := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    have h := (hr ⟨i, hi⟩).1
    interval_cases i <;>
      simpa only [GLVBuildTable.Pack.pack, rawEntryV, Vector.getElem_ofFn] using h
  · intro i hi
    have h := (hr ⟨i, hi⟩).2.1
    interval_cases i <;>
      simpa only [GLVBuildTable.Pack.pack, rawEntryV, Vector.getElem_ofFn] using h
  · intro i hi
    have h := (hr ⟨i, hi⟩).2.2
    interval_cases i <;>
      simpa only [GLVBuildTable.Pack.pack, rawEntryV, Vector.getElem_ofFn] using h

set_option maxRecDepth 8192 in
theorem affineBases_sub_glvPrepare
    (input : VI) (n : ℕ) (hP : AffineFP input.P) (hQ : AffineFP input.Q) :
    ∀ i : Fin 4, AffineFP (baseEntryV
      ((subcircuit GLVBuildTable.Prepare.circuit input).output n) i) := by
  intro i
  fin_cases i <;> simp only [circuit_norm, subcircuit,
    GLVBuildTable.Prepare.circuit, GLVBuildTable.Prepare.elaborated, baseEntryV]
  · exact ⟨hP.1, hP.2.1, hP.2.2⟩
  · exact ⟨affineW_mapRange_var _, affineW_mapRange_var _, hP.2.2⟩
  · exact ⟨hQ.1, affineW_mapRange_var _, hQ.2.2⟩
  · exact ⟨affineW_mapRange_var _, affineW_mapRange_var _, hQ.2.2⟩

end Cost

namespace GLVBuildTable

private lemma eval_varFromOffset_of_agreesBelow
    {A : TypeMap} [ProvableType A] {off k : ℕ}
    {env env' : PE}
    (h_agree : env.AgreesBelow k env') (hk : off + size A ≤ k) :
    eval env (varFromOffset A off : Var A (CF)) =
      eval env' (varFromOffset A off : Var A (CF)) := by
  rw [CircuitType.eval_expression_prover_to_verifier (M := A),
    CircuitType.eval_expression_prover_to_verifier (M := A), ProvableType.ext_iff]
  intro i hi
  rw [← ProvableType.getElem_eval_toElements
      (varFromOffset A off : Var A (CF)) i hi,
    ← ProvableType.getElem_eval_toElements
      (varFromOffset A off : Var A (CF)) i hi]
  simp only [varFromOffset, ProvableType.toElements_fromElements,
    Vector.getElem_mapRange, Expression.eval]
  exact h_agree (off + i) (by omega)

namespace Prepare

private lemma negY_output_stable
    (X : VP) {off k : ℕ}
    {e e' : PE}
    (hX : eval e X = eval e' X)
    (h_agree : e.AgreesBelow k e') (hk : off + 68 ≤ k) :
    eval e ((subcircuit NegYAffine.circuit X).output off) =
      eval e' ((subcircuit NegYAffine.circuit X).output off) := by
  simpa only [circuit_norm, subcircuit, NegYAffine.circuit,
    NegYAffine.elaborated] using
    (NegYAffine.eval_output_of_agreesBelow X hX h_agree (by omega))

set_option maxHeartbeats 4000000 in
private theorem structuralComputableWitnesses
    (offset : ℕ) (input : VI)
    (env env' : PE) :
    FormalCircuitBase.Operations.StructuralComputableWitnesses
      input env env' offset ((main input).operations offset) := by
  obtain ⟨P, Q, s0, s1, s2, s3⟩ := input
  have hmm : ∀ (X : Var MulModBeta32.Inputs (CF)) (o : ℕ),
      (subcircuit MulModBeta32.circuit X).localLength o = 341 := fun _ _ => rfl
  have hneg : ∀ (X : VP) (o : ℕ),
      (subcircuit NegYAffine.circuit X).localLength o = 68 := fun _ _ => rfl
  have hmux : ∀ (X : Var (Mux.Inputs Emu) (CF)) (o : ℕ),
      (subcircuit (Mux.circuit (M := Emu)) X).localLength o = 4 :=
    fun _ _ => rfl
  unfold main
  simp only [
    Circuit.bind_structuralComputableWitnesses_iff,
    FormalCircuit.subcircuit_structuralComputableWitnesses_iff,
    Circuit.pure_structuralComputableWitnesses_iff,
    hmm, hneg, hmux, and_true]
  have parts : ∀ {e e' : PE},
      eval e (⟨P, Q, s0, s1, s2, s3⟩ : VI) =
        eval e' (⟨P, Q, s0, s1, s2, s3⟩ : VI) →
      (eval e P = eval e' P) ∧ (eval e Q = eval e' Q) ∧
      Expression.eval e.toEnvironment s0 = Expression.eval e'.toEnvironment s0 ∧
      Expression.eval e.toEnvironment s1 = Expression.eval e'.toEnvironment s1 ∧
      Expression.eval e.toEnvironment s2 = Expression.eval e'.toEnvironment s2 ∧
      Expression.eval e.toEnvironment s3 = Expression.eval e'.toEnvironment s3 := by
    intro e e' h
    simpa only [circuit_norm, Inputs.mk.injEq] using h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) MulModBeta32.circuit _ _ _ ?_
      MulModBeta32.computableWitnesses env env'
    intro k e e' _ _ h_in
    have hp := (parts h_in).1
    simp only [circuit_norm, FlaggedPoint.mk.injEq] at hp ⊢
    rw [MulModBeta32.Inputs.mk.injEq]
    exact hp.1
  · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) MulModBeta32.circuit _ _ _ ?_
      MulModBeta32.computableWitnesses env env'
    intro k e e' _ _ h_in
    have hq := (parts h_in).2.1
    simp only [circuit_norm, FlaggedPoint.mk.injEq] at hq ⊢
    rw [MulModBeta32.Inputs.mk.injEq]
    exact hq.1
  · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) NegYAffine.circuit _ _ _ ?_
      NegYAffine.computableWitnesses env env'
    intro k e e' _ _ h_in
    have hp := (parts h_in).1
    exact (parts h_in).1
  · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) NegYAffine.circuit _ _ _ ?_
      NegYAffine.computableWitnesses env env'
    intro k e e' _ _ h_in
    have hq := (parts h_in).2.1
    exact (parts h_in).2.1
  all_goals
    refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) (Mux.circuit (M := Emu)) _ _ _ ?_
      (Mux.computableWitnesses (M := Emu)) env env'
  · intro k e e' hle h_agree h_in
    obtain ⟨hp, hq, hs0, hs1, hs2, hs3⟩ := parts h_in
    have hp_eq : eval e P = eval e' P := hp
    simp only [circuit_norm, FlaggedPoint.mk.injEq] at hp hq ⊢
    rw [Mux.Inputs.mk.injEq]
    exact ⟨hs1, emu_map_eval_eq_of_eval_eq
      (negY_output_stable _ hp_eq h_agree (by omega)), hp.2.1⟩
  · intro k e e' hle h_agree h_in
    obtain ⟨hp, hq, hs0, hs1, hs2, hs3⟩ := parts h_in
    have hq_eq : eval e Q = eval e' Q := hq
    simp only [circuit_norm, FlaggedPoint.mk.injEq] at hp hq ⊢
    rw [Mux.Inputs.mk.injEq]
    exact ⟨hs2, emu_map_eval_eq_of_eval_eq
      (negY_output_stable _ hq_eq h_agree (by omega)), hq.2.1⟩
  · intro k e e' hle h_agree h_in
    obtain ⟨hp, hq, hs0, hs1, hs2, hs3⟩ := parts h_in
    have hq_eq : eval e Q = eval e' Q := hq
    simp only [circuit_norm, FlaggedPoint.mk.injEq] at hp hq ⊢
    rw [Mux.Inputs.mk.injEq]
    exact ⟨hs3, emu_map_eval_eq_of_eval_eq
      (negY_output_stable _ hq_eq h_agree (by omega)), hq.2.1⟩

theorem computableWitnesses : circuit.base.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (FormalCircuitBase.computableWitnessCondition
      input env env') ((main input).operations offset)
  exact FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
    input env env' (structuralComputableWitnesses offset input env env')

end Prepare

namespace Subset

end Subset

lemma prepare_subOutput_of_agreesBelow
    (input : VI) {offset k : ℕ}
    {env env' : PE}
    (h_input : eval env input = eval env' input)
    (h_agree : env.AgreesBelow k env') (hk : offset + 830 ≤ k) :
    eval env ((subcircuit Prepare.circuit input).output offset) =
      eval env' ((subcircuit Prepare.circuit input).output offset) := by
  simp only [circuit_norm, subcircuit, Prepare.circuit, Prepare.elaborated]
  rw [Bases.mk.injEq]
  have hp := congrArg Inputs.P h_input
  have hq := congrArg Inputs.Q h_input
  simp only [circuit_norm, FlaggedPoint.mk.injEq] at hp hq
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [FlaggedPoint.mk.injEq]
    exact ⟨hp.1, hp.2.1, hp.2.2⟩
  · rw [FlaggedPoint.mk.injEq]
    exact ⟨emu_map_eval_eq_of_eval_eq (eval_varFromOffset_of_agreesBelow
        (A := Emu) (off := offset) h_agree (by simp only [size, numLimbs]; omega)),
      emu_map_eval_eq_of_eval_eq (eval_varFromOffset_of_agreesBelow
        (A := Emu) (off := offset + 818) h_agree (by simp only [size, numLimbs]; omega)), hp.2.2⟩
  · rw [FlaggedPoint.mk.injEq]
    exact ⟨hq.1, emu_map_eval_eq_of_eval_eq (eval_varFromOffset_of_agreesBelow
      (A := Emu) (off := offset + 822) h_agree (by simp only [size, numLimbs]; omega)), hq.2.2⟩
  · rw [FlaggedPoint.mk.injEq]
    exact ⟨emu_map_eval_eq_of_eval_eq (eval_varFromOffset_of_agreesBelow
        (A := Emu) (off := offset + 341) h_agree (by simp only [size, numLimbs]; omega)),
      emu_map_eval_eq_of_eval_eq (eval_varFromOffset_of_agreesBelow
        (A := Emu) (off := offset + 826) h_agree (by simp only [size, numLimbs]; omega)), hq.2.2⟩

set_option maxRecDepth 262144

end GLVBuildTable
end Solution.Secp256k1ScalarMul
