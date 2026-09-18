import Solution.Secp256k1ScalarMul.Lazy.PatternTable
import Solution.Secp256k1ScalarMul.Lazy.PatternTableCost

/-! ## merged from `Lazy/PatBuildTable.lean` -/
section
/-!
# Sign-pattern table from the input point and the verified result

`Prepare` builds the four signed bases, two muxes canonicalise the
`y`-coordinates of the (possibly infinite) `Q`-bases to zero, then `PatTable`
computes the sixteen sign-pattern entries `E(b) = Σ_j (2 b_j − 1) B_j`, packed
into the coordinate-vector table consumed by the lazy chain.
-/

namespace Solution.Secp256k1ScalarMul.PatBuildTable

open Specs.ShortWeierstrass Specs.Secp256k1
open GLVBuildTable

def canonYInput (P : Var FlaggedPoint (F circomPrime)) : Var (Mux.Inputs Emu) (F circomPrime) :=
  { selector := P.isInf, ifTrue := zeroConst, ifFalse := P.y }

def canonBases (b : Var Bases (F circomPrime)) (y2 y3 : Var Emu (F circomPrime)) :
    Var Bases (F circomPrime) :=
  { r0 := b.r0, r1 := b.r1, r2 := PatTable.withY b.r2 y2, r3 := PatTable.withY b.r3 y3 }

def main (input : Var Inputs (F circomPrime)) :
    Circuit (F circomPrime) (Var Table (F circomPrime)) := do
  let bases ← subcircuit Prepare.circuit input
  let y2 ← subcircuit (Mux.circuit (M := Emu)) (canonYInput bases.r2)
  let y3 ← subcircuit (Mux.circuit (M := Emu)) (canonYInput bases.r3)
  let raw ← subcircuit PatTable.circuit (canonBases bases y2 y3)
  return Pack.pack raw

def basesAt (input : Var Inputs (F circomPrime)) (offset : ℕ) : Var Bases (F circomPrime) :=
  Prepare.circuit.output input offset

def canonBasesAt (input : Var Inputs (F circomPrime)) (offset : ℕ) : Var Bases (F circomPrime) :=
  canonBases (basesAt input offset) (varFromOffset Emu (offset + 830))
    (varFromOffset Emu (offset + 830 + 4))

def rawAt (input : Var Inputs (F circomPrime)) (offset : ℕ) : Var GLVBuildTable.RawTable (F circomPrime) :=
  PatTable.circuit.output (canonBasesAt input offset) (offset + 830 + 4 + 4)

def tableAt (input : Var Inputs (F circomPrime)) (offset : ℕ) : Var Table (F circomPrime) :=
  Pack.pack (rawAt input offset)

def totalLength (_input : Var Inputs (F circomPrime)) : ℕ := 16366

set_option maxRecDepth 8192 in
lemma patTable_localLength (b : Var Bases (F circomPrime)) :
    PatTable.circuit.localLength b = 15528 := rfl

lemma mux_output (i : Var (Mux.Inputs Emu) (F circomPrime)) (n : ℕ) :
    (Mux.circuit (M := Emu)).output i n = varFromOffset Emu n := rfl

lemma mux_localLength (i : Var (Mux.Inputs Emu) (F circomPrime)) :
    (Mux.circuit (M := Emu)).localLength i = 4 := rfl

instance elaborated : ElaboratedCircuit (F circomPrime) Inputs Table main where
  localLength := totalLength
  localLength_eq input offset := by
    simp only [main, totalLength, circuit_norm, Prepare.localLength, mux_localLength,
      patTable_localLength]
  output := tableAt
  output_eq input offset := by
    simp only [main, tableAt, rawAt, canonBasesAt, basesAt, canonBases, circuit_norm,
      Prepare.localLength, mux_localLength, mux_output]

def Assumptions (input : Inputs (F circomPrime)) : Prop := GLVBuildTable.Assumptions input

def Spec (input : Inputs (F circomPrime)) (out : Table (F circomPrime)) : Prop :=
  ∀ i : Fin 16, (entry out i.val i.isLt).Valid ∧
    decodePoint (entry out i.val i.isLt) = PatTable.patPoint (signedBase input) i.val ∧
    ((entry out i.val i.isLt).isInf = 1 → decodeFe (entry out i.val i.isLt).x = 0)

/-- Canonicalising the `y`-coordinate of a point (zero when infinite). -/
lemma canonY_spec {P : FlaggedPoint (F circomPrime)} {Y : Emu (F circomPrime)} (hP : P.Valid)
    (hY : Y = if P.isInf = 1 then emuOfNat 0 else P.y) :
    (valueFP P.x Y P.isInf).Valid ∧ decodePoint (valueFP P.x Y P.isInf) = decodePoint P ∧
      (P.isInf = 1 → Y = emuOfNat 0) := by
  have hz : Fe.Valid (emuOfNat 0 : Emu (F circomPrime)) :=
    CompleteAdd.fe_valid_emuOfNat CompleteAdd.P256_pos
  by_cases hi : P.isInf = 1
  · rw [if_pos hi] at hY
    subst hY
    refine ⟨⟨hP.1, hP.2.1, hz, fun h0 => absurd (h0.symm.trans hi) zero_ne_one⟩, ?_, fun _ => rfl⟩
    simp only [decodePoint, valueFP, hi, if_true]
  · rw [if_neg hi] at hY
    subst hY
    rw [PatTable.valueFP_eta]
    exact ⟨hP, rfl, fun h => absurd h hi⟩

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
theorem soundness : Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start_core
  subst input
  dsimp only [Assumptions] at h_assumptions
  simp only [main, circuit_norm] at h_holds
  obtain ⟨hp0, hm2, hm3, ht0⟩ := h_holds
  have hp' : Prepare.Spec (eval env input_var) (eval env (basesAt input_var i₀)) := by
    simpa only [basesAt, circuit_norm] using hp0 (by simpa only [circuit_norm] using h_assumptions.1)
  have hsub : Subset.Assumptions (eval env (basesAt input_var i₀)) :=
    subsetAssumptions_of_prepare_spec hp'
      (by simpa only [circuit_norm] using h_assumptions.2.1)
      (by simpa only [circuit_norm] using h_assumptions.2.2.1)
      (by simpa only [circuit_norm] using h_assumptions.1.2.1)
      (by simpa only [circuit_norm] using h_assumptions.2.2.2)
  have hV2 : (eval env (basesAt input_var i₀)).r2.Valid := hsub.1 2
  have hV3 : (eval env (basesAt input_var i₀)).r3.Valid := hsub.1 3
  have hy2 : eval env (varFromOffset Emu (i₀ + 830) : Var Emu (F circomPrime)) =
      if (eval env (basesAt input_var i₀)).r2.isInf = 1 then emuOfNat 0
      else (eval env (basesAt input_var i₀)).r2.y := by
    have h := hm2 (by simpa only [canonYInput, basesAt, circuit_norm] using hV2.1)
    simpa only [canonYInput, basesAt, zeroConst, CompleteAdd.eval_emuConst, circuit_norm,
      Prepare.localLength, mux_output, Mux.circuit, Mux.Spec] using h
  have hy3 : eval env (varFromOffset Emu (i₀ + 830 + 4) : Var Emu (F circomPrime)) =
      if (eval env (basesAt input_var i₀)).r3.isInf = 1 then emuOfNat 0
      else (eval env (basesAt input_var i₀)).r3.y := by
    have h := hm3 (by simpa only [canonYInput, basesAt, circuit_norm] using hV3.1)
    simpa only [canonYInput, basesAt, zeroConst, CompleteAdd.eval_emuConst, circuit_norm,
      Prepare.localLength, mux_localLength, mux_output, Mux.circuit, Mux.Spec] using h
  obtain ⟨hV2', hd2, hc2⟩ := canonY_spec hV2 hy2
  obtain ⟨hV3', hd3, hc3⟩ := canonY_spec hV3 hy3
  have hcb : eval env (canonBasesAt input_var i₀) =
      { r0 := (eval env (basesAt input_var i₀)).r0, r1 := (eval env (basesAt input_var i₀)).r1,
        r2 := valueFP (eval env (basesAt input_var i₀)).r2.x
          (eval env (varFromOffset Emu (i₀ + 830) : Var Emu (F circomPrime)))
          (eval env (basesAt input_var i₀)).r2.isInf,
        r3 := valueFP (eval env (basesAt input_var i₀)).r3.x
          (eval env (varFromOffset Emu (i₀ + 830 + 4) : Var Emu (F circomPrime)))
          (eval env (basesAt input_var i₀)).r3.isInf } := by
    simp only [canonBasesAt, canonBases, PatTable.withY, basesAt, valueFP, circuit_norm]
  have hpat : PatTable.Assumptions (eval env (canonBasesAt input_var i₀)) := by
    rw [hcb]
    refine ⟨?_, ?_, ?_, ?_, hc2, hc3, ?_⟩
    · intro j
      fin_cases j
      · exact hsub.1 0
      · exact hsub.1 1
      · exact hV2'
      · exact hV3'
    · exact hsub.2.1.2.2.1
    · exact hsub.2.1.2.2.2.1
    · exact hsub.2.1.2.2.2.2
    · obtain ⟨-, -, hcase⟩ := hsub.2.2.1
      refine ⟨hV2', hV3', ?_⟩
      rcases hcase with ⟨h2, h3, hx⟩ | ⟨h2, h3, hy⟩
      · exact Or.inl ⟨h2, h3, hx⟩
      · refine Or.inr ⟨h2, h3, ?_⟩
        show decodeFe (eval env (varFromOffset Emu (i₀ + 830 + 4) : Var Emu (F circomPrime))) =
          decodeFe (eval env (varFromOffset Emu (i₀ + 830) : Var Emu (F circomPrime)))
        rw [hc3 h3, hc2 h2]
  have ht : PatTable.Spec (eval env (canonBasesAt input_var i₀)) (eval env (rawAt input_var i₀)) := by
    have h := ht0 (by
      simpa only [canonBasesAt, basesAt, circuit_norm, Prepare.localLength, mux_localLength,
        mux_output] using hpat)
    simpa only [rawAt, canonBasesAt, basesAt, circuit_norm, Prepare.localLength, mux_localLength,
      mux_output] using h
  have hbase : (fun j => decodePoint (baseEntry (eval env (canonBasesAt input_var i₀)) j)) =
      signedBase (eval env input_var) := by
    funext j
    rw [hcb]
    fin_cases j
    · exact (hp'.1 0).2
    · exact (hp'.1 1).2
    · exact hd2.trans (hp'.1 2).2
    · exact hd3.trans (hp'.1 3).2
  dsimp only [elaborated, ElaboratedCircuit.output, Spec, tableAt]
  constructor
  · intro i
    rw [Pack.eval_pack_entry_whole]
    have hi := ht i
    rw [hbase] at hi
    exact hi
  · simp only [main, circuit_norm]
    refine ⟨Or.inr ?_, Or.inr ?_, Or.inr ?_, Or.inr ?_⟩
    · simpa only [circuit_norm] using h_assumptions.1
    · simpa only [canonYInput, basesAt, circuit_norm] using hV2.1
    · simpa only [canonYInput, basesAt, circuit_norm] using hV3.1
    · simpa only [canonBasesAt, basesAt, circuit_norm, Prepare.localLength, mux_localLength,
        mux_output] using hpat

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
theorem completeness : Completeness (F circomPrime) main Assumptions := by
  circuit_proof_start_core
  subst input
  dsimp only [Assumptions] at h_assumptions
  simp only [main, circuit_norm] at h_env ⊢
  obtain ⟨hp0, hm2, hm3, -⟩ := h_env
  have hp' : Prepare.Spec (eval env input_var) (eval env (basesAt input_var i₀)) := by
    simpa only [basesAt, circuit_norm] using hp0 (by simpa only [circuit_norm] using h_assumptions.1)
  have hsub : Subset.Assumptions (eval env (basesAt input_var i₀)) :=
    subsetAssumptions_of_prepare_spec hp'
      (by simpa only [circuit_norm] using h_assumptions.2.1)
      (by simpa only [circuit_norm] using h_assumptions.2.2.1)
      (by simpa only [circuit_norm] using h_assumptions.1.2.1)
      (by simpa only [circuit_norm] using h_assumptions.2.2.2)
  have hV2 : (eval env (basesAt input_var i₀)).r2.Valid := hsub.1 2
  have hV3 : (eval env (basesAt input_var i₀)).r3.Valid := hsub.1 3
  have hy2 : eval env (varFromOffset Emu (i₀ + 830) : Var Emu (F circomPrime)) =
      if (eval env (basesAt input_var i₀)).r2.isInf = 1 then emuOfNat 0
      else (eval env (basesAt input_var i₀)).r2.y := by
    have h := hm2 (by simpa only [canonYInput, basesAt, circuit_norm] using hV2.1)
    simpa only [canonYInput, basesAt, zeroConst, CompleteAdd.eval_emuConst, circuit_norm,
      Prepare.localLength, mux_output, Mux.circuit, Mux.Spec] using h
  have hy3 : eval env (varFromOffset Emu (i₀ + 830 + 4) : Var Emu (F circomPrime)) =
      if (eval env (basesAt input_var i₀)).r3.isInf = 1 then emuOfNat 0
      else (eval env (basesAt input_var i₀)).r3.y := by
    have h := hm3 (by simpa only [canonYInput, basesAt, circuit_norm] using hV3.1)
    simpa only [canonYInput, basesAt, zeroConst, CompleteAdd.eval_emuConst, circuit_norm,
      Prepare.localLength, mux_localLength, mux_output, Mux.circuit, Mux.Spec] using h
  obtain ⟨hV2', hd2, hc2⟩ := canonY_spec hV2 hy2
  obtain ⟨hV3', hd3, hc3⟩ := canonY_spec hV3 hy3
  have hcb : eval env (canonBasesAt input_var i₀) =
      { r0 := (eval env (basesAt input_var i₀)).r0, r1 := (eval env (basesAt input_var i₀)).r1,
        r2 := valueFP (eval env (basesAt input_var i₀)).r2.x
          (eval env (varFromOffset Emu (i₀ + 830) : Var Emu (F circomPrime)))
          (eval env (basesAt input_var i₀)).r2.isInf,
        r3 := valueFP (eval env (basesAt input_var i₀)).r3.x
          (eval env (varFromOffset Emu (i₀ + 830 + 4) : Var Emu (F circomPrime)))
          (eval env (basesAt input_var i₀)).r3.isInf } := by
    simp only [canonBasesAt, canonBases, PatTable.withY, basesAt, valueFP, circuit_norm]
  have hpat : PatTable.Assumptions (eval env (canonBasesAt input_var i₀)) := by
    rw [hcb]
    refine ⟨?_, ?_, ?_, ?_, hc2, hc3, ?_⟩
    · intro j
      fin_cases j
      · exact hsub.1 0
      · exact hsub.1 1
      · exact hV2'
      · exact hV3'
    · exact hsub.2.1.2.2.1
    · exact hsub.2.1.2.2.2.1
    · exact hsub.2.1.2.2.2.2
    · obtain ⟨-, -, hcase⟩ := hsub.2.2.1
      refine ⟨hV2', hV3', ?_⟩
      rcases hcase with ⟨h2, h3, hx⟩ | ⟨h2, h3, hy⟩
      · exact Or.inl ⟨h2, h3, hx⟩
      · refine Or.inr ⟨h2, h3, ?_⟩
        show decodeFe (eval env (varFromOffset Emu (i₀ + 830 + 4) : Var Emu (F circomPrime))) =
          decodeFe (eval env (varFromOffset Emu (i₀ + 830) : Var Emu (F circomPrime)))
        rw [hc3 h3, hc2 h2]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [circuit_norm] using h_assumptions.1
  · simpa only [canonYInput, basesAt, circuit_norm] using hV2.1
  · simpa only [canonYInput, basesAt, circuit_norm] using hV3.1
  · simpa only [canonBasesAt, basesAt, circuit_norm, Prepare.localLength, mux_localLength,
      mux_output] using hpat

def circuit : FormalCircuit (F circomPrime) Inputs Table where
  main; elaborated; Assumptions; Spec; soundness; completeness

set_option maxRecDepth 8192 in
lemma localLength (input : Var Inputs (F circomPrime)) :
    circuit.localLength input = 16366 := rfl

end Solution.Secp256k1ScalarMul.PatBuildTable
end

/-! ## merged from `Lazy/PatBuildTableCost.lean` -/
section
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
    calc entry (eval e (Pack.pack raw)) i.val i.isLt = rawEntry (eval e raw) i := by
          simpa only [circuit_norm] using Pack.eval_pack_entry_whole e.toEnvironment raw i
      _ = eval e (rawEntryV raw i) := rawEntry_eval e raw i
      _ = eval e' (rawEntryV raw i) := h i
      _ = rawEntry (eval e' raw) i := (rawEntry_eval e' raw i).symm
      _ = entry (eval e' (Pack.pack raw)) i.val i.isLt := by
          simpa only [circuit_norm] using (Pack.eval_pack_entry_whole e'.toEnvironment raw i).symm
  simp only [circuit_norm]
  rw [GLVBuildTable.Table.mk.injEq]
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
end
