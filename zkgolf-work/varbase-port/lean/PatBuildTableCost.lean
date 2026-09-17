import Solution.Secp256k1ScalarMul.Lazy.PatBuildTable
import Solution.Secp256k1ScalarMul.Lazy.PatternTableCost
import Solution.Secp256k1ScalarMul.Lazy.PatternTableCW

/-! Cost, R1CS shape, output affinity and computable witnesses of the
sign-pattern table assembly. -/

namespace Solution.Secp256k1ScalarMul.PatBuildTable

open Specs.ShortWeierstrass Specs.Secp256k1
open GLVBuildTable
open Challenge.CostR1CS Cost
open Challenge.Utils.ComputableWitnessLemmas

set_option maxHeartbeats 16000000
set_option maxRecDepth 65536

abbrev CF := F circomPrime
abbrev PE := ProverEnvironment (F circomPrime)
abbrev VI := Var Inputs (F circomPrime)

/-! ### Cost -/

/-- `830 + 4 + 4 + 15528` allocations. -/
def cost : Count := ⟨16366, 16490⟩

theorem costIs_main (input : VI) : CostIs (main input) cost := by
  rw [show cost = glvPrepareCost + (⟨4, 4⟩ + (⟨4, 4⟩ + (PatTable.cost + Count.zero))) from by decide]
  unfold main
  refine CostIs.bind (costIs_sub_glvPrepare _) fun _ => ?_
  refine CostIs.bind (costIs_sub_mux _) fun _ => ?_
  refine CostIs.bind (costIs_sub_mux _) fun _ => ?_
  refine CostIs.bind (PatTable.costIs_call _) fun _ => ?_
  exact CostIs.pure _

theorem costIs_call (input : VI) : CostIs (subcircuit circuit input) cost :=
  CostIs.subcircuit fun n => costIs_main input n

/-! ### Shape -/

lemma affineBases_canon (b : Var Bases CF) (y2 y3 : Var Emu CF)
    (hb : ∀ i : Fin 4, AffineFP (baseEntryV b i)) (h2 : AffineW y2) (h3 : AffineW y3) :
    ∀ i : Fin 4, AffineFP (baseEntryV (canonBases b y2 y3) i) := by
  intro i
  fin_cases i
  · exact hb 0
  · exact hb 1
  · exact ⟨(hb 2).1, h2, (hb 2).2.2⟩
  · exact ⟨(hb 3).1, h3, (hb 3).2.2⟩

theorem isR1CS_main (input : VI)
    (hP : AffineFP input.P) (hQ : AffineFP input.Q)
    (hs0 : Affine input.sign0) (hs1 : Affine input.sign1)
    (hs2 : Affine input.sign2) (hs3 : Affine input.sign3) :
    IsR1CSCirc (main input) := by
  have hz0 : AffineProvable (zeroConst : Var Emu CF) := by
    simpa only [zeroConst] using (affineW_emuConst 0).affineProvable
  unfold main
  refine IsR1CSCirc.bind_out (isR1CS_sub_glvPrepare input hP hQ hs0 hs1 hs2 hs3) fun nb => ?_
  have hb := affineBases_sub_glvPrepare input nb hP hQ
  have hb2 : AffineFP ((subcircuit Prepare.circuit input).output nb).r2 := hb 2
  have hb3 : AffineFP ((subcircuit Prepare.circuit input).output nb).r3 := hb 3
  refine IsR1CSCirc.bind_out (isR1CS_sub_mux _ hb2.2.2 hz0 hb2.2.1.affineProvable) fun n2 => ?_
  have hy2 := (affineProvable_sub_mux (M := Emu)
    (canonYInput ((subcircuit Prepare.circuit input).output nb).r2) n2).affineW
  refine IsR1CSCirc.bind_out (isR1CS_sub_mux _ hb3.2.2 hz0 hb3.2.1.affineProvable) fun n3 => ?_
  have hy3 := (affineProvable_sub_mux (M := Emu)
    (canonYInput ((subcircuit Prepare.circuit input).output nb).r3) n3).affineW
  refine IsR1CSCirc.bind_out (PatTable.isR1CS_call _ (affineBases_canon _ _ _ hb hy2 hy3)) fun _ => ?_
  exact IsR1CSCirc.pure _

theorem isR1CS_call (input : VI)
    (hP : AffineFP input.P) (hQ : AffineFP input.Q)
    (hs0 : Affine input.sign0) (hs1 : Affine input.sign1)
    (hs2 : Affine input.sign2) (hs3 : Affine input.sign3) :
    IsR1CSCirc (subcircuit circuit input) :=
  IsR1CSCirc.subcircuit fun n => isR1CS_main input hP hQ hs0 hs1 hs2 hs3 n

theorem affineTable_call (input : VI) (n : ℕ) (hP : AffineFP input.P) (hQ : AffineFP input.Q) :
    AffineTableV
      ((subcircuit circuit input).output n).tx
      ((subcircuit circuit input).output n).ty
      ((subcircuit circuit input).output n).tinf := by
  have hb := affineBases_sub_glvPrepare input n hP hQ
  have hcb := affineBases_canon (basesAt input n) (varFromOffset Emu (n + 830))
    (varFromOffset Emu (n + 830 + 4)) hb (affineW_varFromOffset _ _) (affineW_varFromOffset _ _)
  have hr := PatTable.affine_call_output (canonBasesAt input n) hcb (n + 830 + 4 + 4)
  simpa only [subcircuit, circuit, elaborated, tableAt, rawAt] using
    affineTable_pack (rawAt input n) hr

/-! ### Output stability -/

lemma rawEntry_eval (e : PE) (t : Var GLVBuildTable.RawTable CF) (i : Fin 16) :
    rawEntry (eval e t) i = eval e (rawEntryV t i) := by
  fin_cases i <;> simp only [rawEntry, rawEntryV, circuit_norm]

lemma pack_eval_congr (raw : Var GLVBuildTable.RawTable CF) {e e' : PE}
    (h : ∀ i : Fin 16, eval e (rawEntryV raw i) = eval e' (rawEntryV raw i)) :
    eval e (Pack.pack raw) = eval e' (Pack.pack raw) := by
  have hentry (i : Fin 16) :
      entry (eval e (Pack.pack raw)) i.val i.isLt = entry (eval e' (Pack.pack raw)) i.val i.isLt := by
    have h1 := Pack.eval_pack_entry_whole e.toEnvironment raw i
    have h2 := Pack.eval_pack_entry_whole e'.toEnvironment raw i
    have h3 := rawEntry_eval e raw i
    have h4 := rawEntry_eval e' raw i
    simp only [circuit_norm] at h1 h2 h3 h4 ⊢
    rw [h1, h2, h3, h4, h i]
  simp only [circuit_norm]
  rw [Table.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · apply Vector.ext
    intro i hi
    have h := hentry ⟨i, hi⟩
    simp only [entry, FlaggedPoint.mk.injEq] at h
    simpa only [circuit_norm] using h.1
  · apply Vector.ext
    intro i hi
    have h := hentry ⟨i, hi⟩
    simp only [entry, FlaggedPoint.mk.injEq] at h
    simpa only [circuit_norm] using h.2.1
  · apply Vector.ext
    intro i hi
    have h := hentry ⟨i, hi⟩
    simp only [entry, FlaggedPoint.mk.injEq] at h
    simpa only [circuit_norm] using h.2.2

lemma eval_tableAt_of_agreesBelow (input : VI) {offset k : ℕ} {env env' : PE}
    (h_agree : env.AgreesBelow k env') (hk : offset + 16366 ≤ k) :
    eval env (tableAt input offset) = eval env' (tableAt input offset) := by
  unfold tableAt rawAt
  apply pack_eval_congr
  exact PatTable.call_output_stable _ _ h_agree (by omega)

lemma eval_output_of_agreesBelow (input : VI) {offset k : ℕ} {env env' : PE}
    (h_agree : env.AgreesBelow k env') (hk : offset + 16366 ≤ k) :
    eval env ((subcircuit circuit input).output offset) =
      eval env' ((subcircuit circuit input).output offset) :=
  eval_tableAt_of_agreesBelow input h_agree hk

/-! ### Computable witnesses -/

lemma canonBases_stable {e e' : PE} (b : Var Bases CF) (y2 y3 : Var Emu CF)
    (hb : eval e b = eval e' b) (h2 : eval e y2 = eval e' y2) (h3 : eval e y3 = eval e' y3) :
    eval e (canonBases b y2 y3) = eval e' (canonBases b y2 y3) := by
  simp only [circuit_norm, Bases.mk.injEq, FlaggedPoint.mk.injEq] at hb
  simp only [canonBases, PatTable.withY, circuit_norm, Bases.mk.injEq, FlaggedPoint.mk.injEq]
  exact ⟨hb.1, hb.2.1, ⟨hb.2.2.1.1, by simpa only [circuit_norm] using h2, hb.2.2.1.2.2⟩,
    ⟨hb.2.2.2.1, by simpa only [circuit_norm] using h3, hb.2.2.2.2.2⟩⟩

theorem structuralComputableWitnesses (offset : ℕ) (input : VI) (env env' : PE) :
    FormalCircuitBase.Operations.StructuralComputableWitnesses input env env' offset
      ((main input).operations offset) := by
  have hp : ∀ (X : VI) (o : ℕ), (subcircuit Prepare.circuit X).localLength o = 830 := fun _ _ => rfl
  have hmux : ∀ (X : Var (Mux.Inputs Emu) CF) (o : ℕ),
      (subcircuit (Mux.circuit (M := Emu)) X).localLength o = 4 := fun _ _ => rfl
  have ht : ∀ (X : Var Bases CF) (o : ℕ), (subcircuit PatTable.circuit X).localLength o = 15528 :=
    fun _ _ => rfl
  unfold main
  simp only [Circuit.bind_structuralComputableWitnesses_iff,
    FormalCircuit.subcircuit_structuralComputableWitnesses_iff,
    Circuit.pure_structuralComputableWitnesses_iff, hp, hmux, ht, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) Prepare.circuit _ _ _ (fun _ _ _ _ _ h_in => h_in)
      Prepare.computableWitnesses env env'
  · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) (Mux.circuit (M := Emu)) _ _ _ ?_ (Mux.computableWitnesses (M := Emu)) env env'
    intro k e e' hle h_agree h_in
    have hb := prepare_subOutput_of_agreesBelow input (offset := offset) h_in h_agree (by omega)
    obtain ⟨hx, hy, hi⟩ := PatTable.point_parts _ (PatTable.bases_parts _ hb).2.2.1
    exact PatTable.cond_muxEmu _ _ _ hi PatTable.zeroConst_emu_stable hy
  · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) (Mux.circuit (M := Emu)) _ _ _ ?_ (Mux.computableWitnesses (M := Emu)) env env'
    intro k e e' hle h_agree h_in
    have hb := prepare_subOutput_of_agreesBelow input (offset := offset) h_in h_agree (by omega)
    obtain ⟨hx, hy, hi⟩ := PatTable.point_parts _ (PatTable.bases_parts _ hb).2.2.2
    exact PatTable.cond_muxEmu _ _ _ hi PatTable.zeroConst_emu_stable hy
  · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) PatTable.circuit _ _ _ ?_ PatTable.computableWitnesses env env'
    intro k e e' hle h_agree h_in
    have hb := prepare_subOutput_of_agreesBelow input (offset := offset) h_in h_agree (by omega)
    exact canonBases_stable _ _ _ hb
      (PatTable.muxEmu_output_stable _ h_agree (by omega))
      (PatTable.muxEmu_output_stable _ h_agree (by omega))

theorem computableWitnesses : circuit.base.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (FormalCircuitBase.computableWitnessCondition input env env') ((main input).operations offset)
  exact FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
    input env env' (structuralComputableWitnesses offset input env env')

end Solution.Secp256k1ScalarMul.PatBuildTable
