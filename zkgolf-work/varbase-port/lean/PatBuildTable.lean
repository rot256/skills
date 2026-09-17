import Solution.Secp256k1ScalarMul.Lazy.PatternTable

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
