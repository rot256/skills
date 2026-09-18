import Solution.Secp256k1ScalarMul.GLVScalarMulBase

namespace Solution.Secp256k1ScalarMul
namespace GLVScalarMul

open Specs.ShortWeierstrass Specs.Secp256k1

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem honestAlgebra
    (input : ScalarMul.Inputs (F circomPrime))
    (hass : ScalarMul.Assumptions input)
    (output_Q : FlaggedPoint (F circomPrime))
    (output_c : GLV.Coefficients (F circomPrime))
    (output_s : Emu (F circomPrime))
    (hQeq : output_Q = encodePoint (trueResult input))
    (hceq : output_c = coefficientValue input)
    (hsSpec : GLV.ScalarReduce.Spec { bits := input.bits } output_s) :
    PointValid.Spec output_Q ∧
      (GLV.ValidZ output_c.u1 ∧ GLV.Valid output_c.u2 ∧
        GLV.Valid output_c.v1 ∧ GLV.Valid output_c.v2) ∧
      (GLVScalarRelation.Assumptions
          { s := output_s, u1 := output_c.u1, u2 := output_c.u2
            v1 := output_c.v1, v2 := output_c.v2 } ∧
        GLVScalarRelation.Spec
          { s := output_s, u1 := output_c.u1, u2 := output_c.u2
            v1 := output_c.v1, v2 := output_c.v2 }) := by
  let d := decompositionValue input
  have hc : GLV.Valid (coefficientValue input).u1 ∧
      GLV.Valid (coefficientValue input).u2 ∧
      GLV.Valid (coefficientValue input).v1 ∧
      GLV.Valid (coefficientValue input).v2 := by
    exact CoeffWitness.ofDecomposition_valid d
  have hbits : IsBitArray (input.bits.map ZMod.val) := by
    intro i
    simp only [Vector.getElem_map, Fin.getElem_fin]
    exact IsBool.val_lt_two (hass.1 i)
  have htrue : OnCurveOrInfinity curve (trueResult input) := by
    let P0 : Point Fp := { x := decodeFe input.px, y := decodeFe input.py }
    rw [show trueResult input = Bridge.toSpec
      (GLV.ScalarReduce.scalarValue { bits := input.bits } •
        Bridge.mkPoint P0 hass.2.2.2) from by
          unfold trueResult GLV.ScalarReduce.scalarValue
          exact Bridge.scalarMul_eq_smul (input.bits.map ZMod.val) hbits P0
            hass.2.2.2]
    exact Bridge.toSpec_onCurveOrInfinity _
  have hQvalid := encodePoint_valid htrue
  have hscalar :
      (GLV.signedValue (coefficientValue input).u1 : ZMod order) +
          (GLVAlgebra.lambda : ZMod order) *
            GLV.signedValue (coefficientValue input).u2 +
        (GLV.ScalarReduce.scalarValue { bits := input.bits } : ZMod order) *
          ((GLV.signedValue (coefficientValue input).v1 : ZMod order) +
            (GLVAlgebra.lambda : ZMod order) *
              GLV.signedValue (coefficientValue input).v2) = 0 := by
    have hd := CoeffWitness.ofDecomposition_relation d
    simpa only [coefficientValue, d,
      GLVVerifierTheorems.lambdaZ_eq_lambda] using hd
  have hrRel : GLVScalarRelation.Relation
      { s := output_s
        u1 := (coefficientValue input).u1
        u2 := (coefficientValue input).u2
        v1 := (coefficientValue input).v1
        v2 := (coefficientValue input).v2 } := by
    apply GLVVerifierTheorems.relation_of_fakeScalar hsSpec hscalar
  have hrNonzero : GLVScalarRelation.VNonzero
      { s := output_s
        u1 := (coefficientValue input).u1
        u2 := (coefficientValue input).u2
        v1 := (coefficientValue input).v1
        v2 := (coefficientValue input).v2 } := by
    exact CoeffWitness.ofDecomposition_v_nonzero d
  have hQspecRaw : PointValid.Spec output_Q := by
    rw [hQeq]
    exact hQvalid
  have hc' : GLV.Valid output_c.u1 ∧ GLV.Valid output_c.u2 ∧
      GLV.Valid output_c.v1 ∧ GLV.Valid output_c.v2 := by
    rw [hceq]
    exact hc
  have hrRelRaw : GLVScalarRelation.Relation
      { s := output_s, u1 := output_c.u1, u2 := output_c.u2
        v1 := output_c.v1, v2 := output_c.v2 } := by
    rw [hceq]
    exact hrRel
  have hrNonzeroRaw : GLVScalarRelation.VNonzero
      { s := output_s, u1 := output_c.u1, u2 := output_c.u2
        v1 := output_c.v1, v2 := output_c.v2 } := by
    rw [hceq]
    exact hrNonzero
  have hc'Z : GLV.ValidZ output_c.u1 ∧ GLV.Valid output_c.u2 ∧
      GLV.Valid output_c.v1 ∧ GLV.Valid output_c.v2 :=
    ⟨⟨by rw [hceq]; exact CoeffWitness.ofDecomposition_u1_sign d, hc'.1.2⟩,
      hc'.2.1, hc'.2.2.1, hc'.2.2.2⟩
  exact ⟨hQspecRaw, hc'Z,
    ⟨⟨hsSpec.1, hc'.1, hc'.2.1, hc'.2.2.1, hc'.2.2.2⟩,
      ⟨hrRelRaw, hrNonzeroRaw⟩⟩⟩

end GLVScalarMul
end Solution.Secp256k1ScalarMul
