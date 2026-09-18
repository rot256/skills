import Solution.Secp256k1ScalarMul.GLVBuildTable
import Solution.Secp256k1ScalarMul.GLVMSMTheorems
import Solution.Secp256k1ScalarMul.FakeGLVSound
import Solution.Secp256k1ScalarMul.GLVScalarRelation

namespace Solution.Secp256k1ScalarMul.GLVVerifierTheorems

open Specs.ShortWeierstrass Specs.Secp256k1

lemma toSpec_neg (P : Bridge.W.Point) :
    Bridge.toSpec (-P) = GLVBuildTable.negGP (Bridge.toSpec P) := by
  cases P with
  | zero => rfl
  | @some x y h =>
      rw [WeierstrassCurve.Affine.Point.neg_some]
      simp only [Bridge.toSpec_some, GLVBuildTable.negGP]
      simp [WeierstrassCurve.Affine.negY, Bridge.W]

lemma toSpec_phi (P : Bridge.W.Point) :
    Bridge.toSpec (Phi.hom P) = GLVBuildTable.phiGP (Bridge.toSpec P) := by
  cases P <;> rfl

def signedW (s : F circomPrime) (P : Bridge.W.Point) : Bridge.W.Point :=
  if s = 1 then -P else P

lemma toSpec_signedW (s : F circomPrime) (P : Bridge.W.Point) :
    Bridge.toSpec (signedW s P) =
      GLVBuildTable.signedGP s (Bridge.toSpec P) := by
  by_cases hs : s = 1
  · simp [signedW, GLVBuildTable.signedGP, hs, toSpec_neg]
  · simp [signedW, GLVBuildTable.signedGP, hs]

def basesW (input : GLVBuildTable.Inputs (F circomPrime))
    (P Q : Bridge.W.Point) : Fin 4 → Bridge.W.Point
  | ⟨0, _⟩ => signedW input.sign0 P
  | ⟨1, _⟩ => signedW input.sign1 (Phi.hom P)
  | ⟨2, _⟩ => signedW input.sign2 Q
  | ⟨3, _⟩ => signedW input.sign3 (Phi.hom Q)

lemma signedBase_eq (input : GLVBuildTable.Inputs (F circomPrime))
    (P Q : Bridge.W.Point)
    (hP : decodePoint input.P = Bridge.toSpec P)
    (hQ : decodePoint input.Q = Bridge.toSpec Q) (i : Fin 4) :
    GLVBuildTable.signedBase input i = Bridge.toSpec (basesW input P Q i) := by
  fin_cases i
  · simp [GLVBuildTable.signedBase, basesW, hP, toSpec_signedW]
  · simp only [GLVBuildTable.signedBase, basesW]
    rw [hP, toSpec_signedW]
    exact congrArg (GLVBuildTable.signedGP input.sign1) (toSpec_phi P).symm
  · simp [GLVBuildTable.signedBase, basesW, hQ, toSpec_signedW]
  · simp only [GLVBuildTable.signedBase, basesW]
    rw [hQ, toSpec_signedW]
    exact congrArg (GLVBuildTable.signedGP input.sign3) (toSpec_phi Q).symm

lemma pick_toSpec (b : Bool) (P : Bridge.W.Point) :
    GLVBuildTable.pick b (Bridge.toSpec P) =
      Bridge.toSpec (GLVMSMTheorems.pickW b P) := by
  cases b <;> simp [GLVBuildTable.pick, GLVMSMTheorems.pickW]

lemma subsetPoint_toSpec (B : Fin 4 → Bridge.W.Point) (t : ℕ) :
    GLVBuildTable.subsetPoint (fun i => Bridge.toSpec (B i)) t =
      Bridge.toSpec (GLVMSMTheorems.subsetW B t) := by
  unfold GLVBuildTable.subsetPoint GLVMSMTheorems.subsetW
  rw [pick_toSpec, pick_toSpec, pick_toSpec, pick_toSpec]
  rw [← Bridge.bridge_add, ← Bridge.bridge_add, ← Bridge.bridge_add]
  rfl

theorem tableFor_of_spec
    (buildInput : GLVBuildTable.Inputs (F circomPrime))
    (table : GLVBuildTable.Table (F circomPrime))
    (P Q : Bridge.W.Point)
    (m0 m1 m2 m3 : Vector (F circomPrime) GLV.coeffBits)
    (hP : decodePoint buildInput.P = Bridge.toSpec P)
    (hQ : decodePoint buildInput.Q = Bridge.toSpec Q)
    (hspec : GLVBuildTable.Spec buildInput table) :
    GLVMSMTheorems.TableFor
      { tx := table.tx, ty := table.ty, tinf := table.tinf
        m0, m1, m2, m3 }
      (basesW buildInput P Q) := by
  intro i
  change decodePoint (GLVBuildTable.entry table i.val i.isLt) =
    Bridge.toSpec (GLVMSMTheorems.subsetW (basesW buildInput P Q) i.val)
  rw [(hspec i).2.1]
  unfold GLVBuildTable.tablePoint
  rw [show GLVBuildTable.signedBase buildInput =
      fun j => Bridge.toSpec (basesW buildInput P Q j) from by
        funext j
        exact signedBase_eq buildInput P Q hP hQ j]
  exact subsetPoint_toSpec _ _

def msmInput (table : GLVBuildTable.Table (F circomPrime))
    (c : GLV.Coefficients (F circomPrime)) : GLVMSM.Inputs (F circomPrime) :=
  { tx := table.tx, ty := table.ty, tinf := table.tinf
    m0 := c.u1.bits, m1 := c.u2.bits, m2 := c.v1.bits, m3 := c.v2.bits }

theorem msmAssumptions
    {buildInput : GLVBuildTable.Inputs (F circomPrime)}
    {table : GLVBuildTable.Table (F circomPrime)}
    {c : GLV.Coefficients (F circomPrime)}
    (ht : GLVBuildTable.Spec buildInput table)
    (hc : GLV.Valid c.u1 ∧ GLV.Valid c.u2 ∧
      GLV.Valid c.v1 ∧ GLV.Valid c.v2) :
    GLVMSM.Assumptions (msmInput table c) := by
  refine ⟨fun i => (ht i).1, ?_, hc.1.2, hc.2.1.2, hc.2.2.1.2, hc.2.2.2.2⟩
  intro i
  simpa only [msmInput, GLVMSM.tableEntry, GLVBuildTable.entry, circuit_norm] using (ht i).2.2

theorem tableFor
    {buildInput : GLVBuildTable.Inputs (F circomPrime)}
    {table : GLVBuildTable.Table (F circomPrime)}
    {c : GLV.Coefficients (F circomPrime)}
    (P Q : Bridge.W.Point)
    (hP : decodePoint buildInput.P = Bridge.toSpec P)
    (hQ : decodePoint buildInput.Q = Bridge.toSpec Q)
    (ht : GLVBuildTable.Spec buildInput table) :
    GLVMSMTheorems.TableFor (msmInput table c) (basesW buildInput P Q) := by
  exact tableFor_of_spec buildInput table P Q c.u1.bits c.u2.bits
    c.v1.bits c.v2.bits hP hQ ht

theorem magnitude_smul_signedW (c : GLV.SignedCoeff (F circomPrime))
    (hc : GLV.Valid c) (P : Bridge.W.Point) :
    GLV.magnitude c • signedW c.sign P = GLV.signedValue c • P := by
  rcases hc.1 with hs | hs
  · simp only [signedW, GLV.signedValue, hs, zero_ne_one, if_false]
    exact (GLVAlgebra.natCast_zsmul_eq_nsmul (GLV.magnitude c) P).symm
  · simp only [signedW, GLV.signedValue, hs, if_pos]
    rw [neg_nsmul]
    exact (GLVAlgebra.neg_natCast_zsmul_eq_neg_nsmul (GLV.magnitude c) P).symm

theorem linComb_eq_signed
    (buildInput : GLVBuildTable.Inputs (F circomPrime))
    (c : GLV.Coefficients (F circomPrime))
    (P Q : Bridge.W.Point)
    (hc : GLV.Valid c.u1 ∧ GLV.Valid c.u2 ∧
      GLV.Valid c.v1 ∧ GLV.Valid c.v2)
    (hs0 : buildInput.sign0 = c.u1.sign)
    (hs1 : buildInput.sign1 = c.u2.sign)
    (hs2 : buildInput.sign2 = c.v1.sign)
    (hs3 : buildInput.sign3 = c.v2.sign) :
    GLVMSMTheorems.linComb (basesW buildInput P Q)
        (GLV.magnitude c.u1) (GLV.magnitude c.u2)
        (GLV.magnitude c.v1) (GLV.magnitude c.v2) =
      GLV.signedValue c.u1 • P + GLV.signedValue c.u2 • Phi.hom P +
        GLV.signedValue c.v1 • Q + GLV.signedValue c.v2 • Phi.hom Q := by
  unfold GLVMSMTheorems.linComb
  simp only [basesW]
  rw [hs0, hs1, hs2, hs3]
  rw [magnitude_smul_signedW c.u1 hc.1,
    magnitude_smul_signedW c.u2 hc.2.1,
    magnitude_smul_signedW c.v1 hc.2.2.1,
    magnitude_smul_signedW c.v2 hc.2.2.2]
  simp only [add_assoc]

theorem specAcc_eq_signed
    {buildInput : GLVBuildTable.Inputs (F circomPrime)}
    {table : GLVBuildTable.Table (F circomPrime)}
    {c : GLV.Coefficients (F circomPrime)}
    (P Q : Bridge.W.Point)
    (hP : decodePoint buildInput.P = Bridge.toSpec P)
    (hQ : decodePoint buildInput.Q = Bridge.toSpec Q)
    (ht : GLVBuildTable.Spec buildInput table)
    (hc : GLV.Valid c.u1 ∧ GLV.Valid c.u2 ∧
      GLV.Valid c.v1 ∧ GLV.Valid c.v2)
    (hs0 : buildInput.sign0 = c.u1.sign)
    (hs1 : buildInput.sign1 = c.u2.sign)
    (hs2 : buildInput.sign2 = c.v1.sign)
    (hs3 : buildInput.sign3 = c.v2.sign) :
    GLVMSM.specAcc (msmInput table c) GLVMSM.coeffBits =
      Bridge.toSpec
        (GLV.signedValue c.u1 • P + GLV.signedValue c.u2 • Phi.hom P +
          GLV.signedValue c.v1 • Q + GLV.signedValue c.v2 • Phi.hom Q) := by
  have ha := msmAssumptions ht hc
  have htable := tableFor (c := c) P Q hP hQ ht
  rw [GLVMSMTheorems.specAcc_final_eq
    (msmInput table c) (basesW buildInput P Q) ha htable]
  simp only [msmInput]
  rw [GLVMSMTheorems.scalarOfBits_coeff_eq_magnitude hc.1,
    GLVMSMTheorems.scalarOfBits_coeff_eq_magnitude hc.2.1,
    GLVMSMTheorems.scalarOfBits_coeff_eq_magnitude hc.2.2.1,
    GLVMSMTheorems.scalarOfBits_coeff_eq_magnitude hc.2.2.2,
    linComb_eq_signed buildInput c P Q hc hs0 hs1 hs2 hs3]

theorem groupRelation_of_msm
    {buildInput : GLVBuildTable.Inputs (F circomPrime)}
    {table : GLVBuildTable.Table (F circomPrime)}
    {c : GLV.Coefficients (F circomPrime)}
    {acc : FlaggedPoint (F circomPrime)}
    (P Q : Bridge.W.Point)
    (hP : decodePoint buildInput.P = Bridge.toSpec P)
    (hQ : decodePoint buildInput.Q = Bridge.toSpec Q)
    (ht : GLVBuildTable.Spec buildInput table)
    (hc : GLV.Valid c.u1 ∧ GLV.Valid c.u2 ∧
      GLV.Valid c.v1 ∧ GLV.Valid c.v2)
    (hs0 : buildInput.sign0 = c.u1.sign)
    (hs1 : buildInput.sign1 = c.u2.sign)
    (hs2 : buildInput.sign2 = c.v1.sign)
    (hs3 : buildInput.sign3 = c.v2.sign)
    (hm : GLVMSM.Spec (msmInput table c) acc)
    (hinf : acc.isInf = 1) :
    GLV.signedValue c.u1 • P + GLV.signedValue c.u2 • Phi.hom P +
      GLV.signedValue c.v1 • Q + GLV.signedValue c.v2 • Phi.hom Q = 0 := by
  have ha := msmAssumptions ht hc
  have htable := tableFor (c := c) P Q hP hQ ht
  have hfinal := GLVMSMTheorems.specAcc_final_eq
    (msmInput table c) (basesW buildInput P Q) ha htable
  simp only [msmInput] at hfinal
  have hif :
      (if GLVMSM.specAcc (msmInput table c) GLVMSM.coeffBits = .infinity
        then (1 : F circomPrime) else 0) = 1 := by
    rw [← hm, hinf]
  have hzero : GLVMSM.specAcc (msmInput table c) GLVMSM.coeffBits = .infinity := by
    by_cases h : GLVMSM.specAcc (msmInput table c) GLVMSM.coeffBits = .infinity
    · exact h
    · have hz : (0 : F circomPrime) = 1 := by
        simpa [h] using hif
      exact False.elim (zero_ne_one hz)
  simp only [msmInput] at hzero
  have himage : Bridge.toSpec
      (GLVMSMTheorems.linComb (basesW buildInput P Q)
        (GLV.magnitude c.u1) (GLV.magnitude c.u2)
        (GLV.magnitude c.v1) (GLV.magnitude c.v2)) = Bridge.toSpec 0 := by
    rw [← GLVMSMTheorems.scalarOfBits_coeff_eq_magnitude hc.1,
      ← GLVMSMTheorems.scalarOfBits_coeff_eq_magnitude hc.2.1,
      ← GLVMSMTheorems.scalarOfBits_coeff_eq_magnitude hc.2.2.1,
      ← GLVMSMTheorems.scalarOfBits_coeff_eq_magnitude hc.2.2.2,
      ← hfinal, hzero]
    rfl
  have hlin : GLVMSMTheorems.linComb (basesW buildInput P Q)
        (GLV.magnitude c.u1) (GLV.magnitude c.u2)
        (GLV.magnitude c.v1) (GLV.magnitude c.v2) = 0 :=
    Bridge.toSpec_injective himage
  rw [linComb_eq_signed buildInput c P Q hc hs0 hs1 hs2 hs3] at hlin
  exact hlin

lemma signedValue_natAbs (c : GLV.SignedCoeff (F circomPrime))
    (_hc : GLV.Valid c) :
    (GLV.signedValue c).natAbs = GLV.magnitude c := by
  have h (m : ℕ) :
      (if c.sign = 1 then -(m : ℤ) else (m : ℤ)).natAbs = m := by
    split <;> simp only [Int.natAbs_neg, Int.natAbs_natCast]
  exact h (GLV.magnitude c)

lemma signedResidue_eq_signedValue (c : GLV.SignedCoeff (F circomPrime)) :
    GLVScalarRelation.signedResidue c =
      (GLV.signedValue c : ZMod order) := by
  unfold GLVScalarRelation.signedResidue GLV.signedValue
  split <;> simp

lemma eigenvalue_eq_lambda : GLV.eigenvalue = GLVAlgebra.lambda := by rfl

lemma lambdaZ_eq_lambda : ShortCoeffs.lambdaZ = (GLVAlgebra.lambda : ℤ) := by rfl

theorem shortCombination_nonzero
    (v1 v2 : GLV.SignedCoeff (F circomPrime))
    (h1 : GLV.Valid v1) (h2 : GLV.Valid v2)
    (hnz : GLV.magnitude v1 ≠ 0 ∨ GLV.magnitude v2 ≠ 0) :
    (GLV.signedValue v1 : ZMod order) +
        (GLVAlgebra.lambda : ZMod order) * GLV.signedValue v2 ≠ 0 := by
  intro hz
  have hb1 : (GLV.signedValue v1).natAbs < ShortCoeffs.coeffBound := by
    rw [signedValue_natAbs v1 h1]
    simpa only [ShortCoeffs.coeffBound, GLV.coeffBits] using GLV.magnitude_lt h1
  have hb2 : (GLV.signedValue v2).natAbs < ShortCoeffs.coeffBound := by
    rw [signedValue_natAbs v2 h2]
    simpa only [ShortCoeffs.coeffBound, GLV.coeffBits] using GLV.magnitude_lt h2
  have hk := ShortCoeffs.short_kernel hb1 hb2
    (by simpa only [lambdaZ_eq_lambda] using hz)
  have hm1 : GLV.magnitude v1 = 0 := by
    rw [← signedValue_natAbs v1 h1, hk.1]
    rfl
  have hm2 : GLV.magnitude v2 = 0 := by
    rw [← signedValue_natAbs v2 h2, hk.2]
    rfl
  rcases hnz with hnz | hnz
  · exact hnz hm1
  · exact hnz hm2

lemma scalarResidue_of_reduce
    {bits : Vector (F circomPrime) Specs.Secp256k1.scalarBits}
    {s : Emu (F circomPrime)}
    (hs : GLV.ScalarReduce.Spec { bits := bits } s) :
    GLVScalarRelation.scalarResidue s =
      (GLV.ScalarReduce.scalarValue { bits := bits } : ZMod order) := by
  unfold GLVScalarRelation.scalarResidue
  rw [← ZMod.natCast_mod (BigInt.value limbBits s) order,
    ← ZMod.natCast_mod (GLV.ScalarReduce.scalarValue { bits := bits }) order,
    hs.2]

theorem fakeScalarRelation
    {bits : Vector (F circomPrime) Specs.Secp256k1.scalarBits}
    {s : Emu (F circomPrime)}
    {c : GLV.Coefficients (F circomPrime)}
    (hs : GLV.ScalarReduce.Spec { bits := bits } s)
    (hr : GLVScalarRelation.Relation
      { s, u1 := c.u1, u2 := c.u2, v1 := c.v1, v2 := c.v2 }) :
    (GLV.signedValue c.u1 : ZMod order) +
        (GLVAlgebra.lambda : ZMod order) * GLV.signedValue c.u2 +
      (GLV.ScalarReduce.scalarValue { bits := bits } : ZMod order) *
        ((GLV.signedValue c.v1 : ZMod order) +
          (GLVAlgebra.lambda : ZMod order) * GLV.signedValue c.v2) = 0 := by
  have hs' := scalarResidue_of_reduce hs
  unfold GLVScalarRelation.Relation at hr
  rw [signedResidue_eq_signedValue, signedResidue_eq_signedValue,
    signedResidue_eq_signedValue, signedResidue_eq_signedValue,
    hs', eigenvalue_eq_lambda] at hr
  linear_combination hr

theorem relation_of_fakeScalar
    {bits : Vector (F circomPrime) Specs.Secp256k1.scalarBits}
    {s : Emu (F circomPrime)}
    {c : GLV.Coefficients (F circomPrime)}
    (hs : GLV.ScalarReduce.Spec { bits := bits } s)
    (hr :
      (GLV.signedValue c.u1 : ZMod order) +
          (GLVAlgebra.lambda : ZMod order) * GLV.signedValue c.u2 +
        (GLV.ScalarReduce.scalarValue { bits := bits } : ZMod order) *
          ((GLV.signedValue c.v1 : ZMod order) +
            (GLVAlgebra.lambda : ZMod order) * GLV.signedValue c.v2) = 0) :
    GLVScalarRelation.Relation
      { s, u1 := c.u1, u2 := c.u2, v1 := c.v1, v2 := c.v2 } := by
  have hs' := scalarResidue_of_reduce hs
  unfold GLVScalarRelation.Relation
  rw [signedResidue_eq_signedValue, signedResidue_eq_signedValue,
    signedResidue_eq_signedValue, signedResidue_eq_signedValue,
    hs', eigenvalue_eq_lambda]
  linear_combination hr

end Solution.Secp256k1ScalarMul.GLVVerifierTheorems
