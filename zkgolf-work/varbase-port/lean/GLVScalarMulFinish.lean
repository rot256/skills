import Solution.Secp256k1ScalarMul.GLVScalarMulHonest

namespace Solution.Secp256k1ScalarMul
namespace GLVScalarMul

open Specs.ShortWeierstrass Specs.Secp256k1

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem finishCompleteness
    (input_var : Var ScalarMul.Inputs (F circomPrime))
    (env : ProverEnvironment (F circomPrime)) (i₀ : ℕ)
    (input : ScalarMul.Inputs (F circomPrime))
    (output_Q : FlaggedPoint (F circomPrime))
    (output_c : GLV.Coefficients (F circomPrime))
    (output_s : Emu (F circomPrime))
    (output_table : GLVBuildTable.Table (F circomPrime))
    (hQActual : output_Q = eval env
      (varFromOffset FlaggedPoint i₀ : Var FlaggedPoint (F circomPrime)))
    (hcActual : output_c = eval env
      (varFromOffset GLV.Coefficients (i₀ + 9 + 1046) :
        Var GLV.Coefficients (F circomPrime)))
    (hsActual : output_s = eval env
      (GLV.ScalarReduce.circuit.output { bits := input_var.bits }
        (i₀ + 9 + 1046 + 260)))
    (htActual : output_table = eval env
      (PatBuildTable.circuit.output
        { P := inputPointVar input_var
          Q := varFromOffset FlaggedPoint i₀
          sign0 := (varFromOffset GLV.Coefficients (i₀ + 9 + 1046)).u1.sign
          sign1 := (varFromOffset GLV.Coefficients (i₀ + 9 + 1046)).u2.sign
          sign2 := (varFromOffset GLV.Coefficients (i₀ + 9 + 1046)).v1.sign
          sign3 := (varFromOffset GLV.Coefficients (i₀ + 9 + 1046)).v2.sign }
        (i₀ + 9 + 1046 + 260 + 0 + 865)))
    (hass : ScalarMul.Assumptions input)
    (hbitsIn : eval env input_var.bits = input.bits)
    (hpxIn : eval env input_var.px = input.px)
    (hpyIn : eval env input_var.py = input.py)
    (hQeq : output_Q = encodePoint (trueResult input))
    (hceq : output_c = coefficientValue input)
    (hs' : GLV.ScalarReduce.circuit.Assumptions { bits := input.bits } →
      GLV.ScalarReduce.circuit.Spec { bits := input.bits } output_s)
    (ht' : PatBuildTable.circuit.Assumptions
        { P := eval env (inputPointVar input_var), Q := output_Q
          sign0 := output_c.u1.sign, sign1 := output_c.u2.sign
          sign2 := output_c.v1.sign, sign3 := output_c.v2.sign } →
      PatBuildTable.circuit.Spec
        { P := eval env (inputPointVar input_var), Q := output_Q
          sign0 := output_c.u1.sign, sign1 := output_c.u2.sign
          sign2 := output_c.v1.sign, sign3 := output_c.v2.sign } output_table) :
    ConstraintsHold.Completeness env ((main input_var).operations i₀) := by
  have hsSpec := hs' hass.1
  obtain ⟨hQspecRaw, hc', hrRaw⟩ := honestAlgebra input hass
    output_Q output_c output_s hQeq hceq hsSpec
  have hPeq : eval env (inputPointVar input_var) = inputPoint input := by
    simp only [inputPointVar, inputPoint, circuit_norm]
    rw [FlaggedPoint.mk.injEq]
    constructor
    · simpa only [circuit_norm] using hpxIn
    constructor
    · simpa only [circuit_norm] using hpyIn
    · rfl
  have hPvalid' : (eval env (inputPointVar input_var)).Valid := by
    rw [hPeq]
    exact inputPoint_valid hass
  have hQvalid' : output_Q.Valid := hQspecRaw.1
  have hPfinRaw : (eval env (inputPointVar input_var)).isInf = 0 := by
    rw [hPeq]
    rfl
  have hPxneRaw : decodeFe (eval env (inputPointVar input_var)).x ≠ 0 := by
    rw [hPeq]
    exact OrderFactsCerts.noXZero_secp
      (P := { x := decodeFe input.px, y := decodeFe input.py }) hass.2.2.2
  have htAssRaw : PatBuildTable.Assumptions
      { P := eval env (inputPointVar input_var), Q := output_Q
        sign0 := output_c.u1.sign, sign1 := output_c.u2.sign
        sign2 := output_c.v1.sign, sign3 := output_c.v2.sign } :=
    ⟨⟨hPvalid', hQvalid', hc'.1.1, hc'.2.1.1, hc'.2.2.1.1, hc'.2.2.2.1,
      (fun hinf => (zero_ne_one (hPfinRaw.symm.trans hinf)).elim),
      (fun hinf => (hQspecRaw.2 hinf).2)⟩,
      hPfinRaw, hPxneRaw, hQspecRaw.2⟩
  have htRaw := ht' htAssRaw
  have htSpec : PatBuildTable.Spec
      { P := inputPoint input, Q := encodePoint (trueResult input)
        sign0 := (coefficientValue input).u1.sign
        sign1 := (coefficientValue input).u2.sign
        sign2 := (coefficientValue input).v1.sign
        sign3 := (coefficientValue input).v2.sign } output_table := by
    let rawBI : GLVBuildTable.Inputs (F circomPrime) :=
      { P := eval env (inputPointVar input_var), Q := output_Q
        sign0 := output_c.u1.sign, sign1 := output_c.u2.sign
        sign2 := output_c.v1.sign, sign3 := output_c.v2.sign }
    let targetBI : GLVBuildTable.Inputs (F circomPrime) :=
      { P := inputPoint input, Q := encodePoint (trueResult input)
        sign0 := (coefficientValue input).u1.sign
        sign1 := (coefficientValue input).u2.sign
        sign2 := (coefficientValue input).v1.sign
        sign3 := (coefficientValue input).v2.sign }
    have hBuildInput : rawBI = targetBI := by
      dsimp only [rawBI, targetBI]
      rw [hPeq, hQeq, hceq]
    exact patBuildTableSpec_changeInput htRaw hBuildInput
  have hmRaw := honestLazy input hass output_table htSpec
  have hmAssRaw : LazyMSM.ProverAssumptions
      { tx := output_table.tx, ty := output_table.ty, tinf := output_table.tinf
        m0 := output_c.u1.bits, m1 := output_c.u2.bits
        m2 := output_c.v1.bits, m3 := output_c.v2.bits } := by
    simpa only [GLVVerifierTheorems.msmInput, hceq] using hmRaw
  have hsAssRaw :
      GLV.ScalarReduce.Assumptions { bits := eval env input_var.bits } := by
    simpa only [hbitsIn] using hass.1
  apply mainConstraints (env := env) (i₀ := i₀) (input_var := input_var)
  · rw [← hQActual]
    exact hQspecRaw
  · rw [← hcActual]
    exact hc'
  · exact hsAssRaw
  · rw [← hsActual, ← hcActual]
    exact hrRaw
  · rw [← hQActual, ← hcActual]
    exact htAssRaw
  · rw [← htActual, ← hcActual]
    exact hmAssRaw

end GLVScalarMul
end Solution.Secp256k1ScalarMul
