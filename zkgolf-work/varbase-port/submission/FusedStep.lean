import Solution.Secp256k1ScalarMul.SlopeXS
import Solution.Secp256k1ScalarMul.Slope2
import Solution.Secp256k1ScalarMul.FinishXY
import Solution.Secp256k1ScalarMul.FusedStepTheorems
import Challenge.Utils.ComputableWitnessLemmas

/-!
# Fused double-add step (Eisenträger–Lauter–Montgomery)

Computes `2·R + T` as `(R + T) + R` through a shared λ-chain that never
materializes the y-coordinate of the intermediate `S = R + T`:

  λ₁ = chord/tangent slope of (R, T)          (SlopeXS)
  x_S = λ₁² − R.x − T.x                       (SlopeXS)
  w  = 2·R.y / (x_S − R.x)   or tangent       (Slope2)
  A  = λ₁ + w                or w             (Slope2)
  x₄ = A² − x_S' − R.x, y₄ = A·(±(x₄−R.x)) − R.y   (FinishXY)

Exception handling (proved in `FusedStepTheorems.fused_soundness_core`):
`R = 𝒪` and `T = −R` by output muxes, `T = 𝒪` by re-routing `x_S := R.x`
into the stage-2 tangent branch, `T = R` by the stage-1 tangent branch, and
the chord-path collision `x_S = R.x` (⇔ `S = −R` ⇔ result `𝒪`) by the
`zOut` flag.  Compared to the separate `Double` + `CompleteAdd`, one full
multiply-subtract certificate is saved per step.
-/

namespace Solution.Secp256k1ScalarMul
namespace FusedStep

open Specs.ShortWeierstrass Specs.Secp256k1
open CompleteAdd

structure Inputs (F : Type) where
  acc : FlaggedPoint F
  t : FlaggedPoint F
deriving ProvableStruct

def main (input : Var Inputs (F circomPrime)) :
    Circuit (F circomPrime) (Var FlaggedPoint (F circomPrime)) := do
  let R := input.acc
  let T := input.t

  let s1 ← subcircuit SlopeXS.circuit
    { rx := R.x, ry := R.y, tx := T.x, ty := T.y, tIsInf := T.isInf }
  let s2 ← subcircuit Slope2.circuit
    { rx := R.x, ry := R.y, tIsInf := T.isInf, lam1 := s1.lam1, xS := s1.xS,
      lam32 := s1.lam32 }
  let s3 ← subcircuit FinishXY.circuit
    { rx := R.x, ry := R.y, tIsInf := T.isInf, mulA := s2.mulA, xSe := s2.xSe,
      mulA32 := s2.mulA32 }

  -- cancellation `T = -R`; `SlopeXS` computes this selector directly.
  let cancel := s1.oppY1
  -- `tsel - T.isInf = sameX2 * (1 - T.isInf)` because `tsel` is their
  -- boolean OR.  Reusing this affine expression avoids one assigned witness
  -- and one constraint per scalar step.
  let zOut := s2.tsel - T.isInf

  -- `cancel` gated by `R` being finite; the *x*-coordinate then needs a single
  -- mux, because `cancel = 1` forces `T.x = R.x` (equal canonical limbs), so
  -- `T.x` is the right answer on both exceptional branches.
  let cancelG <== cancel * (1 - R.isInf)
  let m2y ← subcircuit (Mux.circuit (M := Emu))
    { selector := cancel, ifTrue := R.y, ifFalse := s3.y4 }
  let outX ← subcircuit (Mux.circuit (M := Emu))
    { selector := R.isInf + cancelG, ifTrue := T.x, ifFalse := s3.x4 }
  let outY ← subcircuit (Mux.circuit (M := Emu))
    { selector := R.isInf, ifTrue := T.y, ifFalse := m2y }
  -- The two exceptional contributions fuse into a *single* row.  Writing
  -- `a = R.isInf`, `t = T.isInf`, `c = cancelG` and `s = s2.tsel`, we have
  -- `(s - t + a) * (1 - a - c + t) = a*t + (1 - a - c)*(s - t)`
  -- as soon as `a² = a`, `t² = t`, `a*c = 0` and `s*t = t`, all four of which
  -- hold on any satisfying assignment.  This saves one witness and one
  -- constraint per scalar step.
  let outI <== (zOut + R.isInf) * (1 - R.isInf - cancelG + T.isInf)
  return { x := outX, y := outY, isInf := outI }

instance elaborated : ElaboratedCircuit (F circomPrime) Inputs FlaggedPoint main := by
  elaborate_circuit

def Assumptions (input : Inputs (F circomPrime)) : Prop :=
  input.acc.Valid ∧ input.t.Valid ∧
    (input.t.isInf = 1 → decodeFe input.t.x = 0)

def Spec (input : Inputs (F circomPrime)) (out : FlaggedPoint (F circomPrime)) : Prop :=
  out.Valid ∧
    decodePoint out =
      add curve (add curve (decodePoint input.acc) (decodePoint input.acc))
        (decodePoint input.t)

/-- `IsBool (1 − b)` for boolean `b`. -/
private lemma isBool_one_sub {b : F circomPrime} (hb : IsBool b) : IsBool (1 - b) := by
  rcases hb with h | h <;> rw [h]
  · exact Or.inr (by ring)
  · exact Or.inl (by ring)

private lemma isBool_mul_one_sub {x a b : F circomPrime}
    (ha : IsBool a) (hb : IsBool b) (h : x = a * (1 + -b)) : IsBool x := by
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rw [h, ha, hb] <;>
    simp [IsBool]

/-- The gated OR `a + b·(1−a)` of two booleans is boolean. -/
private lemma isBool_or_of_gate {a b g : F circomPrime} (ha : IsBool a) (hb : IsBool b)
    (hg : g = b * (1 + -a)) : IsBool (a + g) := by
  rcases ha with h1 | h1 <;> rcases hb with h2 | h2 <;> rw [hg, h1, h2] <;> simp [IsBool]

private lemma isBool_cancel_direct {x sameX y0 y1 : F circomPrime}
    (h : x = if sameX = 1 then if y0 = y1 then 0 else 1 else 0) : IsBool x := by
  rw [h]
  split
  · split <;> simp [IsBool]
  · simp [IsBool]

theorem soundness : Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [SlopeXS.circuit, SlopeXS.Assumptions, SlopeXS.Spec,
    Slope2.circuit, Slope2.Assumptions, Slope2.Spec,
    FinishXY.circuit, FinishXY.Assumptions, FinishXY.Spec,
    Mux.circuit, Mux.Assumptions, Mux.Spec]
  obtain ⟨hs1, hs2, hs3, hcgE, hm2y, houtXm, houtYm, hoiE⟩ := h_holds
  have hRv := h_assumptions.1
  have hTv := h_assumptions.2.1
  have hTcanon := h_assumptions.2.2
  have hRx : Fe.Valid input_acc_x := hRv.2.1
  have hRy : Fe.Valid input_acc_y := hRv.2.2.1
  have hTx : Fe.Valid input_t_x := hTv.2.1
  have hTy : Fe.Valid input_t_y := hTv.2.2.1
  have htib : IsBool input_t_isInf := hTv.1
  have hRib : IsBool input_acc_isInf := hRv.1
  obtain ⟨⟨hIRx, hIRy, hIRi⟩, hITx, hITy, hITi⟩ := h_input
  -- sub-circuit specs
  obtain ⟨hsameX1, hcancel, hsel1, hlam1v, hlam1, hxSv, hxS, hlam32v, hlam1eq⟩ :=
    hs1 ⟨hRx, hRy, hTx, hTy, htib⟩
  obtain ⟨hxSev, hxSed, hsameX2, htsel, hwv, hw, hmulAv, hmulAd, hA32v, hmulAeq⟩ :=
    hs2 ⟨hRx, hRy, htib, hlam1v, hxSv, hlam32v, hlam1eq⟩
  obtain ⟨hx4v, hx4, hy4v, hy4⟩ := hs3 ⟨hRx, hRy, htib, hmulAv, hxSev, hA32v, hmulAeq⟩
  -- flag booleans
  have hsx1b : IsBool _ := isBool_of_eq_ite hsameX1
  have hsx2b : IsBool _ := isBool_of_eq_ite hsameX2
  have hcb := isBool_cancel_direct hcancel
  -- instantiate the value-level core with the ghost decoded quantities
  refine FusedStepTheorems.fused_soundness_core
    (R := { x := input_acc_x, y := input_acc_y, isInf := input_acc_isInf })
    (T := { x := input_t_x, y := input_t_y, isInf := input_t_isInf })
    hRv hTv hsameX1 hsel1 rfl hlam1 hxS hxSed hsameX2 htsel rfl hw hmulAd
    hx4v (by rw [hx4]) rfl hy4v hy4 hcancel
    hTcanon
    hcgE ?_ ?_ ?_
  · exact houtXm (isBool_or_of_gate hRib (by convert hcb using 2) hcgE)
  · rw [houtYm hRib, hm2y (by convert hcb using 2)]
  · rcases hRib with hb | hb <;> rcases htib with hb' | hb' <;>
      rw [hoiE, htsel, hcgE, hb, hb'] <;> ring

theorem completeness : Completeness (F circomPrime) main Assumptions := by
  circuit_proof_start [SlopeXS.circuit, SlopeXS.Assumptions, SlopeXS.Spec,
    Slope2.circuit, Slope2.Assumptions, Slope2.Spec,
    FinishXY.circuit, FinishXY.Assumptions, FinishXY.Spec,
    Mux.circuit, Mux.Assumptions, Mux.Spec]
  obtain ⟨hs1, hs2, hs3, hcgE, hm2y, houtXm, houtYm, hoiE⟩ := h_env
  have hRv := h_assumptions.1
  have hTv := h_assumptions.2.1
  have hRx : Fe.Valid input_acc_x := hRv.2.1
  have hRy : Fe.Valid input_acc_y := hRv.2.2.1
  have hTx : Fe.Valid input_t_x := hTv.2.1
  have hTy : Fe.Valid input_t_y := hTv.2.2.1
  have htib : IsBool input_t_isInf := hTv.1
  have hRib : IsBool input_acc_isInf := hRv.1
  obtain ⟨hsameX1, hcancel, hsel1, hlam1v, hlam1, hxSv, hxS, hlam32v, hlam1eq⟩ :=
    hs1 ⟨hRx, hRy, hTx, hTy, htib⟩
  obtain ⟨hxSev, hxSed, hsameX2, htsel, hwv, hw, hmulAv, hmulAd, hA32v, hmulAeq⟩ :=
    hs2 ⟨hRx, hRy, htib, hlam1v, hxSv, hlam32v, hlam1eq⟩
  have hsx1b : IsBool _ := isBool_of_eq_ite hsameX1
  have hcb := isBool_cancel_direct hcancel
  exact ⟨⟨hRx, hRy, hTx, hTy, htib⟩, ⟨hRx, hRy, htib, hlam1v, hxSv, hlam32v, hlam1eq⟩,
    ⟨hRx, hRy, htib, hmulAv, hxSev, hA32v, hmulAeq⟩, hcgE, (by convert hcb using 2),
    isBool_or_of_gate hRib (by convert hcb using 2) hcgE, hRib, hoiE⟩

def circuit : FormalCircuit (F circomPrime) Inputs FlaggedPoint where
  main; elaborated; Assumptions; Spec; soundness; completeness

def outputAt (n : ℕ) : Var FlaggedPoint (F circomPrime) :=
  varFromOffset FlaggedPoint (n + 2018)

/-- Componentwise expansion of a `FlaggedPoint` variable block: four limb cells
for `x`, four for `y`, then the flag. -/
lemma varFromOffset_flaggedPoint (m : ℕ) :
    (varFromOffset FlaggedPoint m : Var FlaggedPoint (F circomPrime))
      = { x := varFromOffset Emu m, y := varFromOffset Emu (m + 4),
          isInf := var ⟨m + 8⟩ } := by
  simp only [ProvableStruct.varFromOffset_eq_varFromOffset, ProvableStruct.varFromOffset,
    ProvableStruct.varFromOffset.go, ProvableStruct.fromComponents,
    ProvableType.varFromOffset_field]
  rfl

lemma output_eq_outputAt (input : Var Inputs (F circomPrime)) (n : ℕ) :
    circuit.output input n = outputAt n := by
  show elaborated.output input n = _
  simp only [elaborated, outputAt, varFromOffset_flaggedPoint, numLimbs,
    show secpParams32.B = 32 from rfl]

end FusedStep
end Solution.Secp256k1ScalarMul
