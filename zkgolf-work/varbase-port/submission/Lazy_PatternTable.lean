import Solution.Secp256k1ScalarMul.GLVBuildTable
import Solution.Secp256k1ScalarMul.Lazy_ChainAlgebra

/-!
# Sign-pattern table `E(b) = Σ_j (2 b_j − 1) B_j`

Built from the signed bases `r0..r3` of `GLVBuildTable.Prepare`:
`u± = r0 ± r1`, `v± = r2 ± r3` (four `PhiPairAdd`), the eight entries with
`b_0 = 1` as `u± + (±v±)` (eight `CompleteAdd`), and the remaining eight as
negations (`NegYAffine`).  Entry `t` has bit `j` set iff `+B_j`.
-/

namespace Solution.Secp256k1ScalarMul.PatTable

open Specs.ShortWeierstrass Specs.Secp256k1
open GLVBuildTable

/-- `+P` for a set bit, `−P` for a clear bit. -/
def pickG (b : Bool) (P : GroupPoint Fp) : GroupPoint Fp := if b then P else negGP P

def patPoint (B : Fin 4 → GroupPoint Fp) (t : ℕ) : GroupPoint Fp :=
  add curve (add curve (pickG (bitAt t 0) (B 0)) (pickG (bitAt t 1) (B 1)))
    (add curve (pickG (bitAt t 2) (B 2)) (pickG (bitAt t 3) (B 3)))

/-! ### Circuit -/

def withY (P : Var FlaggedPoint (F circomPrime)) (y : Var Emu (F circomPrime)) :
    Var FlaggedPoint (F circomPrime) :=
  { x := P.x, y := y, isInf := P.isInf }

def withXY (P : Var FlaggedPoint (F circomPrime)) (x y : Var Emu (F circomPrime)) :
    Var FlaggedPoint (F circomPrime) :=
  { x := x, y := y, isInf := P.isInf }

/-- Canonicalise both coordinates of a possibly-infinite point to zero, then negate. -/
def negCanon (P : Var FlaggedPoint (F circomPrime)) :
    Circuit (F circomPrime) (Var FlaggedPoint (F circomPrime) × Var FlaggedPoint (F circomPrime)) := do
  let x ← subcircuit (Mux.circuit (M := Emu)) { selector := P.isInf, ifTrue := zeroConst, ifFalse := P.x }
  let y ← subcircuit (Mux.circuit (M := Emu)) { selector := P.isInf, ifTrue := zeroConst, ifFalse := P.y }
  let ny ← subcircuit NegYAffine.circuit (withXY P x y)
  return (withXY P x y, withXY P x ny)

def main (b : Var Bases (F circomPrime)) : Circuit (F circomPrime) (Var GLVBuildTable.RawTable (F circomPrime)) := do
  let nr1y ← subcircuit NegYAffine.circuit b.r1
  let nr3y ← subcircuit NegYAffine.circuit b.r3
  let up ← subcircuit PhiPairAdd.circuit { P := b.r0, Q := b.r1 }
  let um ← subcircuit PhiPairAdd.circuit { P := b.r0, Q := withY b.r1 nr1y }
  let vp ← subcircuit PhiPairAdd.circuit { P := b.r2, Q := b.r3 }
  let vm ← subcircuit PhiPairAdd.circuit { P := b.r2, Q := withY b.r3 nr3y }
  let (vp', nvp) ← negCanon vp
  let (vm', nvm) ← negCanon vm
  -- entries with `b_0 = 1`: index `1 + 2 b_1 + 4 b_2 + 8 b_3`
  let e15 ← subcircuit CompleteAdd.circuit { P := up, Q := vp' }
  let e7 ← subcircuit CompleteAdd.circuit { P := up, Q := vm' }
  let e11 ← subcircuit CompleteAdd.circuit { P := up, Q := nvm }
  let e3 ← subcircuit CompleteAdd.circuit { P := up, Q := nvp }
  let e13 ← subcircuit CompleteAdd.circuit { P := um, Q := vp' }
  let e5 ← subcircuit CompleteAdd.circuit { P := um, Q := vm' }
  let e9 ← subcircuit CompleteAdd.circuit { P := um, Q := nvm }
  let e1 ← subcircuit CompleteAdd.circuit { P := um, Q := nvp }
  -- the other half by negation
  let (_, e0) ← negCanon e15
  let (_, e8) ← negCanon e7
  let (_, e4) ← negCanon e11
  let (_, e12) ← negCanon e3
  let (_, e2) ← negCanon e13
  let (_, e10) ← negCanon e5
  let (_, e6) ← negCanon e9
  let (_, e14) ← negCanon e1
  return GLVBuildTable.RawTable.mk e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15

instance elaborated : ElaboratedCircuit (F circomPrime) Bases GLVBuildTable.RawTable main := by
  elaborate_circuit

def Assumptions (input : Bases (F circomPrime)) : Prop :=
  (∀ i : Fin 4, (baseEntry input i).Valid) ∧
    input.r0.isInf = 0 ∧ input.r1.isInf = 0 ∧
    decodeFe input.r1.x ≠ decodeFe input.r0.x ∧
    (input.r2.isInf = 1 → input.r2.y = emuOfNat 0) ∧
    (input.r3.isInf = 1 → input.r3.y = emuOfNat 0) ∧
    PhiPairAdd.Assumptions { P := input.r2, Q := input.r3 }

def Spec (input : Bases (F circomPrime)) (out : GLVBuildTable.RawTable (F circomPrime)) : Prop :=
  ∀ i : Fin 16, (rawEntry out i).Valid ∧
    decodePoint (rawEntry out i) =
      patPoint (fun j => decodePoint (baseEntry input j)) i.val ∧
    ((rawEntry out i).isInf = 1 → decodeFe (rawEntry out i).x = 0)


/-! ### Value-level helpers -/

lemma pickG_toSpec (b : Bool) (P : Bridge.W.Point) :
    pickG b (Bridge.toSpec P) = Bridge.toSpec (LazyChain.pickS b P) := by
  cases b <;> simp [pickG, LazyChain.pickS, GLVVerifierTheorems.toSpec_neg]

lemma patPoint_toSpec (B : Fin 4 → Bridge.W.Point) (t : ℕ) :
    patPoint (fun i => Bridge.toSpec (B i)) t = Bridge.toSpec (LazyChain.patW B t) := by
  unfold patPoint LazyChain.patW
  simp only [bitAt]
  rw [pickG_toSpec, pickG_toSpec, pickG_toSpec, pickG_toSpec]
  rw [← Bridge.bridge_add, ← Bridge.bridge_add, ← Bridge.bridge_add]

lemma negW_patW (W : Fin 4 → Bridge.W.Point) (t : Fin 16) :
    -(LazyChain.patW W t.val) = LazyChain.patW W (15 - t.val) := by
  fin_cases t <;> simp [LazyChain.patW, LazyChain.pickS] <;> abel

lemma decodePoint_ocoi {P : FlaggedPoint (F circomPrime)} (hP : P.Valid) :
    OnCurveOrInfinity curve (decodePoint P) := by
  rcases hP.1 with h0 | h1
  · rw [CompleteAdd.decodePoint_of_finite h0]; exact hP.2.2.2 h0
  · rw [CompleteAdd.decodePoint_of_isInf h1]; trivial

lemma negGP_patPoint (B : Fin 4 → GroupPoint Fp) (hB : ∀ j, OnCurveOrInfinity curve (B j))
    (t : Fin 16) : negGP (patPoint B t.val) = patPoint B (15 - t.val) := by
  have hBeq : B = fun j => Bridge.toSpec (Bridge.fromSpec (B j) (hB j)) := by
    funext j; rw [Bridge.toSpec_fromSpec]
  rw [hBeq, patPoint_toSpec, patPoint_toSpec, ← GLVVerifierTheorems.toSpec_neg, negW_patW]

lemma negGP_add {a b : GroupPoint Fp} (ha : OnCurveOrInfinity curve a)
    (hb : OnCurveOrInfinity curve b) :
    negGP (add curve a b) = add curve (negGP a) (negGP b) := by
  rw [← Bridge.toSpec_fromSpec a ha, ← Bridge.toSpec_fromSpec b hb, ← Bridge.bridge_add,
    ← GLVVerifierTheorems.toSpec_neg, ← GLVVerifierTheorems.toSpec_neg,
    ← GLVVerifierTheorems.toSpec_neg, ← Bridge.bridge_add, neg_add]

lemma negGP_negGP (a : GroupPoint Fp) : negGP (negGP a) = a := by
  cases a with
  | infinity => rfl
  | affine P => simp [negGP]

lemma negGP_ocoi {a : GroupPoint Fp} (ha : OnCurveOrInfinity curve a) :
    OnCurveOrInfinity curve (negGP a) := by
  cases a with
  | infinity => trivial
  | affine P =>
      simp only [negGP, OnCurveOrInfinity, CompleteAdd.onCurve_iff] at ha ⊢
      rw [neg_sq]; exact ha

lemma finite_of_decode_affine {P : FlaggedPoint (F circomPrime)} (hP : P.Valid)
    (h : ∃ Q : Point Fp, decodePoint P = .affine Q) : P.isInf = 0 := by
  obtain ⟨Q, h⟩ := h
  rcases hP.1 with h0 | h1
  · exact h0
  · rw [CompleteAdd.decodePoint_of_isInf h1] at h; cases h

lemma add_affine_ne {a b : Point Fp} (h : b.x ≠ a.x) :
    ∃ c : Point Fp, add curve (.affine a) (.affine b) = .affine c := by
  refine ⟨chord a b, ?_⟩
  simp only [add, if_neg (Ne.symm h)]

lemma decode_zero : decodeFe (emuOfNat 0 : Emu (F circomPrime)) = 0 := by
  rw [decodeFe, CompleteAdd.value_emuOfNat (by positivity), Nat.cast_zero]

lemma valueFP_eta (P : FlaggedPoint (F circomPrime)) : valueFP P.x P.y P.isInf = P := by
  cases P; rfl

/-- Canonicalising the coordinates of a point (zero when infinite). -/
lemma canon_spec {P : FlaggedPoint (F circomPrime)} {X Y : Emu (F circomPrime)} (hP : P.Valid)
    (hX : X = if P.isInf = 1 then emuOfNat 0 else P.x)
    (hY : Y = if P.isInf = 1 then emuOfNat 0 else P.y) :
    (valueFP X Y P.isInf).Valid ∧ decodePoint (valueFP X Y P.isInf) = decodePoint P ∧
    (P.isInf = 1 → decodeFe X = 0) ∧ (P.isInf = 1 → Y = emuOfNat 0) := by
  have hz : Fe.Valid (emuOfNat 0 : Emu (F circomPrime)) := CompleteAdd.fe_valid_emuOfNat CompleteAdd.P256_pos
  by_cases hi : P.isInf = 1
  · rw [if_pos hi] at hX hY
    subst hX; subst hY
    refine ⟨⟨hP.1, hz, hz, fun h0 => absurd (h0.symm.trans hi) zero_ne_one⟩, ?_, fun _ => decode_zero,
      fun _ => rfl⟩
    simp only [decodePoint, valueFP, hi, if_true]
  · rw [if_neg hi] at hX hY
    subst hX; subst hY
    rw [valueFP_eta]
    exact ⟨hP, rfl, fun h => absurd h hi, fun h => absurd h hi⟩

/-! ### Soundness -/

set_option maxRecDepth 65536 in
set_option maxHeartbeats 16000000 in
theorem soundness : Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [negCanon, withY, withXY, PhiPairAdd.circuit, PhiPairAdd.Assumptions,
    PhiPairAdd.Spec, CompleteAdd.circuit, CompleteAdd.Assumptions, CompleteAdd.Spec,
    NegYAffine.circuit, NegYAffine.Assumptions, NegYAffine.Spec,
    Mux.circuit, Mux.Assumptions, Mux.Spec]
  obtain ⟨hn1, hn3, hup, hum, hvp, hvm, hvpx, hvpy, hnvp, hvmx, hvmy, hnvm,
    h15, h7, h11, h3, h13, h5, h9, h1,
    h0x, h0y, h0, h8x, h8y, h8, h4x, h4y, h4, h12x, h12y, h12,
    h2x, h2y, h2, h10x, h10y, h10, h6x, h6y, h6, h14x, h14y, h14⟩ := h_holds
  obtain ⟨hV, h0f, h1f, hne, h2c, h3c, hpp⟩ := h_assumptions
  have hV0 : ({ x := input_r0_x, y := input_r0_y, isInf := input_r0_isInf } :
    FlaggedPoint (F circomPrime)).Valid := hV 0
  have hV1 : ({ x := input_r1_x, y := input_r1_y, isInf := input_r1_isInf } :
    FlaggedPoint (F circomPrime)).Valid := hV 1
  have hV2 : ({ x := input_r2_x, y := input_r2_y, isInf := input_r2_isInf } :
    FlaggedPoint (F circomPrime)).Valid := hV 2
  have hV3 : ({ x := input_r3_x, y := input_r3_y, isInf := input_r3_isInf } :
    FlaggedPoint (F circomPrime)).Valid := hV 3
  -- negations of r1, r3
  obtain ⟨hn1v, hn1e⟩ := hn1 ⟨hV1, fun h => absurd (h1f.symm.trans h) zero_ne_one⟩
  obtain ⟨hn3v, hn3e⟩ := hn3 ⟨hV3, h3c⟩
  have hnr1 := neg_valueFP hV1 hn1v hn1e
  have hnr3 := neg_valueFP hV3 hn3v hn3e
  simp only [valueFP] at hnr1 hnr3
  -- the four pair additions
  obtain ⟨hupv, hupd⟩ := hup ⟨hV0, hV1, Or.inl ⟨h0f, h1f, hne⟩⟩
  obtain ⟨humv, humd⟩ := hum ⟨hV0, hnr1.1, Or.inl ⟨h0f, h1f, hne⟩⟩
  obtain ⟨hvpv, hvpd⟩ := hvp hpp
  obtain ⟨hvmv, hvmd⟩ := hvm ⟨hV2, hnr3.1, by
    rcases hpp.2.2 with ⟨h2, h3, hx⟩ | ⟨h2, h3, hy⟩
    · exact Or.inl ⟨h2, h3, hx⟩
    · refine Or.inr ⟨h2, h3, ?_⟩
      show decodeFe _ = decodeFe input_r2_y
      rw [hn3e, h3c h3, h2c h2, decode_zero, neg_zero]⟩
  -- canonicalise `v±` and negate
  have hvpx' := hvpx hvpv.1
  have hvpy' := hvpy hvpv.1
  simp only [zeroConst, CompleteAdd.eval_emuConst] at hvpx' hvpy'
  have hcvp := canon_spec hvpv hvpx' hvpy'
  obtain ⟨hnvpv, hnvpe⟩ := hnvp ⟨hcvp.1, hcvp.2.2.2⟩
  have hnvp' := neg_valueFP hcvp.1 hnvpv hnvpe
  have hvmx' := hvmx hvmv.1
  have hvmy' := hvmy hvmv.1
  simp only [zeroConst, CompleteAdd.eval_emuConst] at hvmx' hvmy'
  have hcvm := canon_spec hvmv hvmx' hvmy'
  obtain ⟨hnvmv, hnvme⟩ := hnvm ⟨hcvm.1, hcvm.2.2.2⟩
  have hnvm' := neg_valueFP hcvm.1 hnvmv hnvme
  simp only [valueFP] at hcvp hnvp' hcvm hnvm'
  -- `u±` are affine
  have hupf := finite_of_decode_affine hupv ⟨_, by
    rw [hupd, CompleteAdd.decodePoint_of_finite h0f, CompleteAdd.decodePoint_of_finite h1f]
    exact (add_affine_ne hne).choose_spec⟩
  have humf := finite_of_decode_affine humv ⟨_, by
    rw [humd, hnr1.2, CompleteAdd.decodePoint_of_finite h0f, CompleteAdd.decodePoint_of_finite h1f]
    simp only [negGP]
    exact (add_affine_ne (a := { x := decodeFe input_r0_x, y := decodeFe input_r0_y })
      (b := { x := decodeFe input_r1_x, y := -decodeFe input_r1_y }) hne).choose_spec⟩
  -- the eight additions
  obtain ⟨h15v, h15d, h15c⟩ := h15 ⟨hupv, hcvp.1, hupf, hcvp.2.2.1⟩
  obtain ⟨h7v, h7d, h7c⟩ := h7 ⟨hupv, hcvm.1, hupf, hcvm.2.2.1⟩
  obtain ⟨h11v, h11d, h11c⟩ := h11 ⟨hupv, hnvm'.1, hupf, hcvm.2.2.1⟩
  obtain ⟨h3v, h3d, h3c'⟩ := h3 ⟨hupv, hnvp'.1, hupf, hcvp.2.2.1⟩
  obtain ⟨h13v, h13d, h13c⟩ := h13 ⟨humv, hcvp.1, humf, hcvp.2.2.1⟩
  obtain ⟨h5v, h5d, h5c⟩ := h5 ⟨humv, hcvm.1, humf, hcvm.2.2.1⟩
  obtain ⟨h9v, h9d, h9c⟩ := h9 ⟨humv, hnvm'.1, humf, hcvm.2.2.1⟩
  obtain ⟨h1v, h1d, h1c⟩ := h1 ⟨humv, hnvp'.1, humf, hcvp.2.2.1⟩
  -- the eight negations
  have hn0x := h0x h15v.1; have hn0y := h0y h15v.1
  simp only [zeroConst, CompleteAdd.eval_emuConst] at hn0x hn0y
  have hc0 := canon_spec h15v hn0x hn0y
  obtain ⟨hn0v, hn0e⟩ := h0 ⟨hc0.1, hc0.2.2.2⟩
  have he0 := neg_valueFP hc0.1 hn0v hn0e
  have hn8x := h8x h7v.1; have hn8y := h8y h7v.1
  simp only [zeroConst, CompleteAdd.eval_emuConst] at hn8x hn8y
  have hc8 := canon_spec h7v hn8x hn8y
  obtain ⟨hn8v, hn8e⟩ := h8 ⟨hc8.1, hc8.2.2.2⟩
  have he8 := neg_valueFP hc8.1 hn8v hn8e
  have hn4x := h4x h11v.1; have hn4y := h4y h11v.1
  simp only [zeroConst, CompleteAdd.eval_emuConst] at hn4x hn4y
  have hc4 := canon_spec h11v hn4x hn4y
  obtain ⟨hn4v, hn4e⟩ := h4 ⟨hc4.1, hc4.2.2.2⟩
  have he4 := neg_valueFP hc4.1 hn4v hn4e
  have hn12x := h12x h3v.1; have hn12y := h12y h3v.1
  simp only [zeroConst, CompleteAdd.eval_emuConst] at hn12x hn12y
  have hc12 := canon_spec h3v hn12x hn12y
  obtain ⟨hn12v, hn12e⟩ := h12 ⟨hc12.1, hc12.2.2.2⟩
  have he12 := neg_valueFP hc12.1 hn12v hn12e
  have hn2x := h2x h13v.1; have hn2y := h2y h13v.1
  simp only [zeroConst, CompleteAdd.eval_emuConst] at hn2x hn2y
  have hc2 := canon_spec h13v hn2x hn2y
  obtain ⟨hn2v, hn2e⟩ := h2 ⟨hc2.1, hc2.2.2.2⟩
  have he2 := neg_valueFP hc2.1 hn2v hn2e
  have hn10x := h10x h5v.1; have hn10y := h10y h5v.1
  simp only [zeroConst, CompleteAdd.eval_emuConst] at hn10x hn10y
  have hc10 := canon_spec h5v hn10x hn10y
  obtain ⟨hn10v, hn10e⟩ := h10 ⟨hc10.1, hc10.2.2.2⟩
  have he10 := neg_valueFP hc10.1 hn10v hn10e
  have hn6x := h6x h9v.1; have hn6y := h6y h9v.1
  simp only [zeroConst, CompleteAdd.eval_emuConst] at hn6x hn6y
  have hc6 := canon_spec h9v hn6x hn6y
  obtain ⟨hn6v, hn6e⟩ := h6 ⟨hc6.1, hc6.2.2.2⟩
  have he6 := neg_valueFP hc6.1 hn6v hn6e
  have hn14x := h14x h1v.1; have hn14y := h14y h1v.1
  simp only [zeroConst, CompleteAdd.eval_emuConst] at hn14x hn14y
  have hc14 := canon_spec h1v hn14x hn14y
  obtain ⟨hn14v, hn14e⟩ := h14 ⟨hc14.1, hc14.2.2.2⟩
  have he14 := neg_valueFP hc14.1 hn14v hn14e
  simp only [valueFP] at hc0 he0 hc8 he8 hc4 he4 hc12 he12 hc2 he2 hc10 he10 hc6 he6 hc14 he14
  -- decoded values of the base points
  have hB : ∀ j, OnCurveOrInfinity curve (decodePoint (baseEntry
      { r0 := { x := input_r0_x, y := input_r0_y, isInf := input_r0_isInf },
        r1 := { x := input_r1_x, y := input_r1_y, isInf := input_r1_isInf },
        r2 := { x := input_r2_x, y := input_r2_y, isInf := input_r2_isInf },
        r3 := { x := input_r3_x, y := input_r3_y, isInf := input_r3_isInf } } j)) :=
    fun j => decodePoint_ocoi (hV j)
  have hB0 := hB 0; have hB1 := hB 1; have hB2 := hB 2; have hB3 := hB 3
  simp only [baseEntry] at hB0 hB1 hB2 hB3
  -- the eight direct entries, in pattern form
  have e15 := h15d
  rw [hupd, hcvp.2.1, hvpd] at e15
  have e7 := h7d
  rw [hupd, hcvm.2.1, hvmd, hnr3.2] at e7
  have e11 := h11d
  rw [hupd, hnvm'.2, hcvm.2.1, hvmd, hnr3.2, negGP_add hB2 (negGP_ocoi hB3), negGP_negGP] at e11
  have e3 := h3d
  rw [hupd, hnvp'.2, hcvp.2.1, hvpd, negGP_add hB2 hB3] at e3
  have e13 := h13d
  rw [humd, hnr1.2, hcvp.2.1, hvpd] at e13
  have e5 := h5d
  rw [humd, hnr1.2, hcvm.2.1, hvmd, hnr3.2] at e5
  have e9 := h9d
  rw [humd, hnr1.2, hnvm'.2, hcvm.2.1, hvmd, hnr3.2, negGP_add hB2 (negGP_ocoi hB3), negGP_negGP] at e9
  have e1 := h1d
  rw [humd, hnr1.2, hnvp'.2, hcvp.2.1, hvpd, negGP_add hB2 hB3] at e1
  -- assemble
  intro i
  fin_cases i
  · refine ⟨he0.1, ?_, hc0.2.2.1⟩
    try simp only [rawEntry]
    rw [he0.2, hc0.2.1, e15]
    have h := negGP_patPoint _ hB 15
    simp [rawEntry, patPoint, bitAt, pickG, baseEntry] at h ⊢
    exact h
  · refine ⟨h1v, ?_, h1c⟩
    try simp only [rawEntry]
    rw [e1]
    simp [rawEntry, patPoint, bitAt, pickG, baseEntry]
  · refine ⟨he2.1, ?_, hc2.2.2.1⟩
    try simp only [rawEntry]
    rw [he2.2, hc2.2.1, e13]
    have h := negGP_patPoint _ hB 13
    simp [rawEntry, patPoint, bitAt, pickG, baseEntry] at h ⊢
    exact h
  · refine ⟨h3v, ?_, h3c'⟩
    try simp only [rawEntry]
    rw [e3]
    simp [rawEntry, patPoint, bitAt, pickG, baseEntry]
  · refine ⟨he4.1, ?_, hc4.2.2.1⟩
    try simp only [rawEntry]
    rw [he4.2, hc4.2.1, e11]
    have h := negGP_patPoint _ hB 11
    simp [rawEntry, patPoint, bitAt, pickG, baseEntry] at h ⊢
    exact h
  · refine ⟨h5v, ?_, h5c⟩
    try simp only [rawEntry]
    rw [e5]
    simp [rawEntry, patPoint, bitAt, pickG, baseEntry]
  · refine ⟨he6.1, ?_, hc6.2.2.1⟩
    try simp only [rawEntry]
    rw [he6.2, hc6.2.1, e9]
    have h := negGP_patPoint _ hB 9
    simp [rawEntry, patPoint, bitAt, pickG, baseEntry] at h ⊢
    exact h
  · refine ⟨h7v, ?_, h7c⟩
    try simp only [rawEntry]
    rw [e7]
    simp [rawEntry, patPoint, bitAt, pickG, baseEntry]
  · refine ⟨he8.1, ?_, hc8.2.2.1⟩
    try simp only [rawEntry]
    rw [he8.2, hc8.2.1, e7]
    have h := negGP_patPoint _ hB 7
    simp [rawEntry, patPoint, bitAt, pickG, baseEntry] at h ⊢
    exact h
  · refine ⟨h9v, ?_, h9c⟩
    try simp only [rawEntry]
    rw [e9]
    simp [rawEntry, patPoint, bitAt, pickG, baseEntry]
  · refine ⟨he10.1, ?_, hc10.2.2.1⟩
    try simp only [rawEntry]
    rw [he10.2, hc10.2.1, e5]
    have h := negGP_patPoint _ hB 5
    simp [rawEntry, patPoint, bitAt, pickG, baseEntry] at h ⊢
    exact h
  · refine ⟨h11v, ?_, h11c⟩
    try simp only [rawEntry]
    rw [e11]
    simp [rawEntry, patPoint, bitAt, pickG, baseEntry]
  · refine ⟨he12.1, ?_, hc12.2.2.1⟩
    try simp only [rawEntry]
    rw [he12.2, hc12.2.1, e3]
    have h := negGP_patPoint _ hB 3
    simp [rawEntry, patPoint, bitAt, pickG, baseEntry] at h ⊢
    exact h
  · refine ⟨h13v, ?_, h13c⟩
    try simp only [rawEntry]
    rw [e13]
    simp [rawEntry, patPoint, bitAt, pickG, baseEntry]
  · refine ⟨he14.1, ?_, hc14.2.2.1⟩
    try simp only [rawEntry]
    rw [he14.2, hc14.2.1, e1]
    have h := negGP_patPoint _ hB 1
    simp [rawEntry, patPoint, bitAt, pickG, baseEntry] at h ⊢
    exact h
  · refine ⟨h15v, ?_, h15c⟩
    try simp only [rawEntry]
    rw [e15]
    simp [rawEntry, patPoint, bitAt, pickG, baseEntry]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 16000000 in
theorem completeness : Completeness (F circomPrime) main Assumptions := by
  circuit_proof_start [negCanon, withY, withXY, PhiPairAdd.circuit, PhiPairAdd.Assumptions,
    PhiPairAdd.Spec, CompleteAdd.circuit, CompleteAdd.Assumptions, CompleteAdd.Spec,
    NegYAffine.circuit, NegYAffine.Assumptions, NegYAffine.Spec,
    Mux.circuit, Mux.Assumptions, Mux.Spec]
  obtain ⟨hn1, hn3, hup, hum, hvp, hvm, hvpx, hvpy, hnvp, hvmx, hvmy, hnvm,
    h15, h7, h11, h3, h13, h5, h9, h1,
    h0x, h0y, h0, h8x, h8y, h8, h4x, h4y, h4, h12x, h12y, h12,
    h2x, h2y, h2, h10x, h10y, h10, h6x, h6y, h6, h14x, h14y, h14⟩ := h_env
  obtain ⟨hV, h0f, h1f, hne, h2c, h3c, hpp⟩ := h_assumptions
  have hV0 : ({ x := input_r0_x, y := input_r0_y, isInf := input_r0_isInf } :
    FlaggedPoint (F circomPrime)).Valid := hV 0
  have hV1 : ({ x := input_r1_x, y := input_r1_y, isInf := input_r1_isInf } :
    FlaggedPoint (F circomPrime)).Valid := hV 1
  have hV2 : ({ x := input_r2_x, y := input_r2_y, isInf := input_r2_isInf } :
    FlaggedPoint (F circomPrime)).Valid := hV 2
  have hV3 : ({ x := input_r3_x, y := input_r3_y, isInf := input_r3_isInf } :
    FlaggedPoint (F circomPrime)).Valid := hV 3
  -- negations of r1, r3
  obtain ⟨hn1v, hn1e⟩ := hn1 ⟨hV1, fun h => absurd (h1f.symm.trans h) zero_ne_one⟩
  obtain ⟨hn3v, hn3e⟩ := hn3 ⟨hV3, h3c⟩
  have hnr1 := neg_valueFP hV1 hn1v hn1e
  have hnr3 := neg_valueFP hV3 hn3v hn3e
  simp only [valueFP] at hnr1 hnr3
  -- the four pair additions
  obtain ⟨hupv, hupd⟩ := hup ⟨hV0, hV1, Or.inl ⟨h0f, h1f, hne⟩⟩
  obtain ⟨humv, humd⟩ := hum ⟨hV0, hnr1.1, Or.inl ⟨h0f, h1f, hne⟩⟩
  obtain ⟨hvpv, hvpd⟩ := hvp hpp
  obtain ⟨hvmv, hvmd⟩ := hvm ⟨hV2, hnr3.1, by
    rcases hpp.2.2 with ⟨h2, h3, hx⟩ | ⟨h2, h3, hy⟩
    · exact Or.inl ⟨h2, h3, hx⟩
    · refine Or.inr ⟨h2, h3, ?_⟩
      show decodeFe _ = decodeFe input_r2_y
      rw [hn3e, h3c h3, h2c h2, decode_zero, neg_zero]⟩
  -- canonicalise `v±` and negate
  have hvpx' := hvpx hvpv.1
  have hvpy' := hvpy hvpv.1
  simp only [zeroConst, CompleteAdd.eval_emuConst] at hvpx' hvpy'
  have hcvp := canon_spec hvpv hvpx' hvpy'
  obtain ⟨hnvpv, hnvpe⟩ := hnvp ⟨hcvp.1, hcvp.2.2.2⟩
  have hnvp' := neg_valueFP hcvp.1 hnvpv hnvpe
  have hvmx' := hvmx hvmv.1
  have hvmy' := hvmy hvmv.1
  simp only [zeroConst, CompleteAdd.eval_emuConst] at hvmx' hvmy'
  have hcvm := canon_spec hvmv hvmx' hvmy'
  obtain ⟨hnvmv, hnvme⟩ := hnvm ⟨hcvm.1, hcvm.2.2.2⟩
  have hnvm' := neg_valueFP hcvm.1 hnvmv hnvme
  simp only [valueFP] at hcvp hnvp' hcvm hnvm'
  -- `u±` are affine
  have hupf := finite_of_decode_affine hupv ⟨_, by
    rw [hupd, CompleteAdd.decodePoint_of_finite h0f, CompleteAdd.decodePoint_of_finite h1f]
    exact (add_affine_ne hne).choose_spec⟩
  have humf := finite_of_decode_affine humv ⟨_, by
    rw [humd, hnr1.2, CompleteAdd.decodePoint_of_finite h0f, CompleteAdd.decodePoint_of_finite h1f]
    simp only [negGP]
    exact (add_affine_ne (a := { x := decodeFe input_r0_x, y := decodeFe input_r0_y })
      (b := { x := decodeFe input_r1_x, y := -decodeFe input_r1_y }) hne).choose_spec⟩
  -- the eight additions
  obtain ⟨h15v, h15d, h15c⟩ := h15 ⟨hupv, hcvp.1, hupf, hcvp.2.2.1⟩
  obtain ⟨h7v, h7d, h7c⟩ := h7 ⟨hupv, hcvm.1, hupf, hcvm.2.2.1⟩
  obtain ⟨h11v, h11d, h11c⟩ := h11 ⟨hupv, hnvm'.1, hupf, hcvm.2.2.1⟩
  obtain ⟨h3v, h3d, h3c'⟩ := h3 ⟨hupv, hnvp'.1, hupf, hcvp.2.2.1⟩
  obtain ⟨h13v, h13d, h13c⟩ := h13 ⟨humv, hcvp.1, humf, hcvp.2.2.1⟩
  obtain ⟨h5v, h5d, h5c⟩ := h5 ⟨humv, hcvm.1, humf, hcvm.2.2.1⟩
  obtain ⟨h9v, h9d, h9c⟩ := h9 ⟨humv, hnvm'.1, humf, hcvm.2.2.1⟩
  obtain ⟨h1v, h1d, h1c⟩ := h1 ⟨humv, hnvp'.1, humf, hcvp.2.2.1⟩
  -- the eight negations
  have hn0x := h0x h15v.1; have hn0y := h0y h15v.1
  simp only [zeroConst, CompleteAdd.eval_emuConst] at hn0x hn0y
  have hc0 := canon_spec h15v hn0x hn0y
  obtain ⟨hn0v, hn0e⟩ := h0 ⟨hc0.1, hc0.2.2.2⟩
  have he0 := neg_valueFP hc0.1 hn0v hn0e
  have hn8x := h8x h7v.1; have hn8y := h8y h7v.1
  simp only [zeroConst, CompleteAdd.eval_emuConst] at hn8x hn8y
  have hc8 := canon_spec h7v hn8x hn8y
  obtain ⟨hn8v, hn8e⟩ := h8 ⟨hc8.1, hc8.2.2.2⟩
  have he8 := neg_valueFP hc8.1 hn8v hn8e
  have hn4x := h4x h11v.1; have hn4y := h4y h11v.1
  simp only [zeroConst, CompleteAdd.eval_emuConst] at hn4x hn4y
  have hc4 := canon_spec h11v hn4x hn4y
  obtain ⟨hn4v, hn4e⟩ := h4 ⟨hc4.1, hc4.2.2.2⟩
  have he4 := neg_valueFP hc4.1 hn4v hn4e
  have hn12x := h12x h3v.1; have hn12y := h12y h3v.1
  simp only [zeroConst, CompleteAdd.eval_emuConst] at hn12x hn12y
  have hc12 := canon_spec h3v hn12x hn12y
  obtain ⟨hn12v, hn12e⟩ := h12 ⟨hc12.1, hc12.2.2.2⟩
  have he12 := neg_valueFP hc12.1 hn12v hn12e
  have hn2x := h2x h13v.1; have hn2y := h2y h13v.1
  simp only [zeroConst, CompleteAdd.eval_emuConst] at hn2x hn2y
  have hc2 := canon_spec h13v hn2x hn2y
  obtain ⟨hn2v, hn2e⟩ := h2 ⟨hc2.1, hc2.2.2.2⟩
  have he2 := neg_valueFP hc2.1 hn2v hn2e
  have hn10x := h10x h5v.1; have hn10y := h10y h5v.1
  simp only [zeroConst, CompleteAdd.eval_emuConst] at hn10x hn10y
  have hc10 := canon_spec h5v hn10x hn10y
  obtain ⟨hn10v, hn10e⟩ := h10 ⟨hc10.1, hc10.2.2.2⟩
  have he10 := neg_valueFP hc10.1 hn10v hn10e
  have hn6x := h6x h9v.1; have hn6y := h6y h9v.1
  simp only [zeroConst, CompleteAdd.eval_emuConst] at hn6x hn6y
  have hc6 := canon_spec h9v hn6x hn6y
  obtain ⟨hn6v, hn6e⟩ := h6 ⟨hc6.1, hc6.2.2.2⟩
  have he6 := neg_valueFP hc6.1 hn6v hn6e
  have hn14x := h14x h1v.1; have hn14y := h14y h1v.1
  simp only [zeroConst, CompleteAdd.eval_emuConst] at hn14x hn14y
  have hc14 := canon_spec h1v hn14x hn14y
  obtain ⟨hn14v, hn14e⟩ := h14 ⟨hc14.1, hc14.2.2.2⟩
  have he14 := neg_valueFP hc14.1 hn14v hn14e
  exact ⟨⟨hV1, fun h => absurd (h1f.symm.trans h) zero_ne_one⟩, ⟨hV3, h3c⟩,
    ⟨hV0, hV1, Or.inl ⟨h0f, h1f, hne⟩⟩, ⟨hV0, hnr1.1, Or.inl ⟨h0f, h1f, hne⟩⟩, hpp,
    ⟨hV2, hnr3.1, by
      rcases hpp.2.2 with ⟨h2, h3, hx⟩ | ⟨h2, h3, hy⟩
      · exact Or.inl ⟨h2, h3, hx⟩
      · refine Or.inr ⟨h2, h3, ?_⟩
        show decodeFe _ = decodeFe input_r2_y
        rw [hn3e, h3c h3, h2c h2, decode_zero, neg_zero]⟩,
    hvpv.1, hvpv.1, ⟨hcvp.1, hcvp.2.2.2⟩, hvmv.1, hvmv.1, ⟨hcvm.1, hcvm.2.2.2⟩,
    ⟨hupv, hcvp.1, hupf, hcvp.2.2.1⟩, ⟨hupv, hcvm.1, hupf, hcvm.2.2.1⟩,
    ⟨hupv, hnvm'.1, hupf, hcvm.2.2.1⟩, ⟨hupv, hnvp'.1, hupf, hcvp.2.2.1⟩,
    ⟨humv, hcvp.1, humf, hcvp.2.2.1⟩, ⟨humv, hcvm.1, humf, hcvm.2.2.1⟩,
    ⟨humv, hnvm'.1, humf, hcvm.2.2.1⟩, ⟨humv, hnvp'.1, humf, hcvp.2.2.1⟩,
    h15v.1, h15v.1, ⟨hc0.1, hc0.2.2.2⟩, h7v.1, h7v.1, ⟨hc8.1, hc8.2.2.2⟩,
    h11v.1, h11v.1, ⟨hc4.1, hc4.2.2.2⟩, h3v.1, h3v.1, ⟨hc12.1, hc12.2.2.2⟩,
    h13v.1, h13v.1, ⟨hc2.1, hc2.2.2.2⟩, h5v.1, h5v.1, ⟨hc10.1, hc10.2.2.2⟩,
    h9v.1, h9v.1, ⟨hc6.1, hc6.2.2.2⟩, h1v.1, h1v.1, ⟨hc14.1, hc14.2.2.2⟩⟩

def circuit : FormalCircuit (F circomPrime) Bases GLVBuildTable.RawTable where
  main; elaborated; Assumptions; Spec; soundness; completeness

end Solution.Secp256k1ScalarMul.PatTable
