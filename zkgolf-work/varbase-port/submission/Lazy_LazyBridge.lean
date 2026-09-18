import Solution.Secp256k1ScalarMul.Lazy_PatBuildTable
import Solution.Secp256k1ScalarMul.Lazy_LazyMSMCost
import Solution.Secp256k1ScalarMul.Lazy_SpecialScalar
import Solution.Secp256k1ScalarMul.GLVVerifierTheorems
import Solution.Secp256k1ScalarMul.FakeGLVSound

/-!
# Bridging the lazy chain to the fake-GLV verifier

Soundness: a satisfied lazy chain over the sign-pattern table of the signed
bases forces the signed linear combination `u₁ P + u₂ φP + v₁ Q + v₂ φQ = 0`,
either through the chain (`sp = 0`) or through the vanishing all-plus entry
with unit coefficients (`sp = 1`).

Completeness: with the special-scalar decomposition, the honest prover always
satisfies the chain's prover assumptions.
-/

namespace Solution.Secp256k1ScalarMul.LazyBridge

open Specs.ShortWeierstrass Specs.Secp256k1
open GLVVerifierTheorems

/-! ### Table facts -/

theorem msmAssumptions
    {buildInput : GLVBuildTable.Inputs (F circomPrime)}
    {table : GLVBuildTable.Table (F circomPrime)}
    {c : GLV.Coefficients (F circomPrime)}
    (ht : PatBuildTable.Spec buildInput table)
    (hc : GLV.Valid c.u1 ∧ GLV.Valid c.u2 ∧ GLV.Valid c.v1 ∧ GLV.Valid c.v2) :
    GLVMSM.Assumptions (msmInput table c) := by
  refine ⟨fun i => (ht i).1, ?_, hc.1.2, hc.2.1.2, hc.2.2.1.2, hc.2.2.2.2⟩
  intro i
  simpa only [msmInput, GLVMSM.tableEntry, GLVBuildTable.entry, circuit_norm] using (ht i).2.2

theorem patTableFor
    {buildInput : GLVBuildTable.Inputs (F circomPrime)}
    {table : GLVBuildTable.Table (F circomPrime)}
    {c : GLV.Coefficients (F circomPrime)}
    (P Q : Bridge.W.Point)
    (hP : decodePoint buildInput.P = Bridge.toSpec P)
    (hQ : decodePoint buildInput.Q = Bridge.toSpec Q)
    (ht : PatBuildTable.Spec buildInput table) :
    LazyChain.PatTableFor (msmInput table c) (basesW buildInput P Q) := by
  intro i
  change decodePoint (GLVBuildTable.entry table i.val i.isLt) =
    Bridge.toSpec (LazyChain.patW (basesW buildInput P Q) i.val)
  rw [(ht i).2.1]
  rw [show GLVBuildTable.signedBase buildInput =
      fun j => Bridge.toSpec (basesW buildInput P Q j) from
        funext (signedBase_eq buildInput P Q hP hQ)]
  exact PatTable.patPoint_toSpec _ _

lemma entry15_inf_of_tinf
    {table : GLVBuildTable.Table (F circomPrime)} {c : GLV.Coefficients (F circomPrime)}
    (h : table.tinf[15] = 1) :
    decodePoint (GLVMSM.tableEntry (msmInput table c) 15 (by norm_num)) = .infinity :=
  CompleteAdd.decodePoint_of_isInf h

/-- The infinity flag of a valid entry that decodes to infinity is set. -/
lemma tinf_of_decode_inf {P : FlaggedPoint (F circomPrime)} (hP : P.Valid)
    (h : decodePoint P = .infinity) : P.isInf = 1 := by
  rcases hP.1 with h0 | h1
  · rw [CompleteAdd.decodePoint_of_finite h0] at h
    cases h
  · exact h1

/-! ### Magnitudes of unit coefficients -/

lemma magnitude_of_unitBits {c : GLV.SignedCoeff (F circomPrime)} (hc : GLV.Valid c)
    (hu : LazyMSM.UnitBits c.bits) : GLV.magnitude c = 1 := by
  rw [GLVMSMTheorems.magnitude_eq_fromBits hc, Utils.Bits.fromBits]
  rw [show (fun (acc : ℕ) (i : Fin GLV.coeffBits) => acc + (c.bits.map ZMod.val)[i.val] * 2 ^ i.val) =
      fun acc i => acc + (fun i : Fin GLV.coeffBits => (c.bits.map ZMod.val)[i.val] * 2 ^ i.val) i from rfl]
  rw [Fin.foldl_to_sum]
  rw [Finset.sum_eq_single (0 : Fin GLV.coeffBits)]
  · simp only [Fin.val_zero, Vector.getElem_map, pow_zero, mul_one]
    have h0 : c.bits[(0 : ℕ)] = 1 := hu.1
    have h0' := congrArg ZMod.val h0
    rw [LazyChain.val_one] at h0'
    exact h0'
  · intro b _ hb
    have hb' : 1 ≤ b.val := Nat.pos_of_ne_zero (fun h => hb (Fin.ext h))
    have hz : c.bits[b.val] = 0 := hu.2 b hb'
    have hz' : c.bits[b.val].val = 0 := by rw [hz]; exact ZMod.val_zero
    simp only [Vector.getElem_map]
    exact (by rw [hz', zero_mul] : c.bits[b.val].val * 2 ^ b.val = 0)
  · intro h
    exact absurd (Finset.mem_univ _) h

/-! ### Soundness: the group relation -/

lemma linComb_ones (B : Fin 4 → Bridge.W.Point) :
    GLVMSMTheorems.linComb B 1 1 1 1 = LazyChain.patW B 15 := by
  simp [GLVMSMTheorems.linComb, LazyChain.patW, LazyChain.pickS]

theorem groupRelation_of_lazy
    {buildInput : GLVBuildTable.Inputs (F circomPrime)}
    {table : GLVBuildTable.Table (F circomPrime)}
    {c : GLV.Coefficients (F circomPrime)}
    (P Q : Bridge.W.Point)
    (hP : decodePoint buildInput.P = Bridge.toSpec P)
    (hQ : decodePoint buildInput.Q = Bridge.toSpec Q)
    (ht : PatBuildTable.Spec buildInput table)
    (hc : GLV.Valid c.u1 ∧ GLV.Valid c.u2 ∧ GLV.Valid c.v1 ∧ GLV.Valid c.v2)
    (hs0 : buildInput.sign0 = c.u1.sign)
    (hs1 : buildInput.sign1 = c.u2.sign)
    (hs2 : buildInput.sign2 = c.v1.sign)
    (hs3 : buildInput.sign3 = c.v2.sign)
    (hm : LazyMSM.Spec (msmInput table c)) :
    GLV.signedValue c.u1 • P + GLV.signedValue c.u2 • Phi.hom P +
      GLV.signedValue c.v1 • Q + GLV.signedValue c.v2 • Phi.hom Q = 0 := by
  have ha := msmAssumptions ht hc
  have htable := patTableFor (c := c) P Q hP hQ ht
  rw [← linComb_eq_signed buildInput c P Q hc hs0 hs1 hs2 hs3]
  have hV15 := (ht ⟨15, by norm_num⟩).1
  rcases hV15.1 with h15 | h15
  · have hchain := hm.1 h15
    rw [LazyChain.chainAcc_final _ _ ha htable, htable ⟨15, by norm_num⟩] at hchain
    have h := Bridge.toSpec_injective hchain
    have hz := LazyChain.linComb_eq_zero_of_chain _ _ _ _ _ h
    simp only [msmInput] at hz
    rwa [GLVMSMTheorems.scalarOfBits_coeff_eq_magnitude hc.1,
      GLVMSMTheorems.scalarOfBits_coeff_eq_magnitude hc.2.1,
      GLVMSMTheorems.scalarOfBits_coeff_eq_magnitude hc.2.2.1,
      GLVMSMTheorems.scalarOfBits_coeff_eq_magnitude hc.2.2.2] at hz
  · obtain ⟨hu0, hu1, hu2, hu3⟩ := hm.2 h15
    have hinf := entry15_inf_of_tinf (c := c) h15
    rw [htable ⟨15, by norm_num⟩] at hinf
    have hpat : LazyChain.patW (basesW buildInput P Q) 15 = 0 :=
      Bridge.toSpec_injective (hinf.trans Bridge.toSpec_zero.symm)
    rw [magnitude_of_unitBits hc.1 hu0, magnitude_of_unitBits hc.2.1 hu1,
      magnitude_of_unitBits hc.2.2.1 hu2, magnitude_of_unitBits hc.2.2.2 hu3, linComb_ones]
    exact hpat

/-! ### Completeness: the honest prover -/

/-- Sign of a sign flag as an integer. -/
def sgnOf (s : F circomPrime) : ℤ := if s = 1 then -1 else 1

lemma signedW_eq_sgn (s : F circomPrime) (P : Bridge.W.Point) :
    signedW s P = sgnOf s • P := by
  by_cases h : s = 1 <;> simp [signedW, sgnOf, h]

lemma sgnOf_isSign (s : F circomPrime) : SpecialScalar.IsSign (sgnOf s) := by
  by_cases h : s = 1 <;> simp [sgnOf, h, SpecialScalar.IsSign]

lemma signedValue_eq_sgn (c : GLV.SignedCoeff (F circomPrime)) :
    GLV.signedValue c = sgnOf c.sign * (GLV.magnitude c : ℤ) := by
  by_cases h : c.sign = 1 <;> simp [GLV.signedValue, sgnOf, h]

/-- The signed bases of `(P, k P)` are the GLV bases with the flag signs. -/
lemma basesW_eq_glvBases (buildInput : GLVBuildTable.Inputs (F circomPrime))
    (P : Bridge.W.Point) (k : ℕ) :
    basesW buildInput P (k • P) =
      LazyChain.glvBases P k
        (fun j => sgnOf (match j with
          | ⟨0, _⟩ => buildInput.sign0 | ⟨1, _⟩ => buildInput.sign1
          | ⟨2, _⟩ => buildInput.sign2 | _ => buildInput.sign3)) := by
  funext j
  fin_cases j <;> simp only [basesW, LazyChain.glvBases, signedW_eq_sgn]

/-- A scalar vanishing modulo the order kills every point. -/
lemma zsmul_eq_zero_of_cast_eq_zero (a : ℤ) (P : Bridge.W.Point)
    (h : (a : ZMod order) = 0) : a • P = 0 := by
  obtain ⟨q, hq⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd a order).mp h
  rw [hq, mul_comm, mul_zsmul, GLVAlgebra.natCast_zsmul_eq_nsmul, GLVFinal.order_nsmul_all]
  first | exact zsmul_zero q | simp

/-- The sign pattern selected by `t` on the flag signs. -/
def patternOf (σ : Fin 4 → ℤ) (t : ℕ) : Fin 4 → ℤ :=
  fun j => LazyChain.sgn (decide (t / 2 ^ j.val % 2 = 1)) * σ j

lemma patScalar_eq_pattern (σ : Fin 4 → ℤ) (k : ℕ) (t : ℕ) :
    (LazyChain.patScalar σ k t : ZMod order) =
      (patternOf σ t 0 : ZMod order) + (ShortCoeffs.lambdaZ : ZMod order) * patternOf σ t 1 +
        (k : ZMod order) * ((patternOf σ t 2 : ZMod order) +
          (ShortCoeffs.lambdaZ : ZMod order) * patternOf σ t 3) := by
  simp only [LazyChain.patScalar, patternOf, lambdaZ_eq_lambda, Fin.val_zero, Fin.val_one,
    Fin.val_two, show ((3 : Fin 4) : ℕ) = 3 from rfl]
  push_cast
  ring

lemma patternOf_isSign (σ : Fin 4 → ℤ) (hσ : ∀ j, SpecialScalar.IsSign (σ j)) (t : ℕ) (j : Fin 4) :
    SpecialScalar.IsSign (patternOf σ t j) := by
  unfold patternOf LazyChain.sgn
  rcases hσ j with h | h <;> split <;> simp [SpecialScalar.IsSign, h]

/-- A vanishing pattern entry of the honest bases makes the scalar special. -/
theorem isSpecial_of_entry_zero (P : Bridge.W.Point) (hP : P ≠ 0) (k : ℕ)
    (σ : Fin 4 → ℤ) (hσ : ∀ j, SpecialScalar.IsSign (σ j)) (t : ℕ)
    (h : LazyChain.patW (LazyChain.glvBases P k σ) t = 0) :
    SpecialScalar.IsSpecial (k : ZMod order) := by
  have hz := LazyChain.patScalar_cast_eq_zero P hP k σ t h
  rw [patScalar_eq_pattern] at hz
  exact SpecialScalar.isSpecial_of_pattern _ (patternOf σ t) (patternOf_isSign σ hσ t) hz

lemma patW_15_eq_zero (P : Bridge.W.Point) (k : ℕ) (σ : Fin 4 → ℤ)
    (hrel : SpecialScalar.Relation (k : ZMod order) σ) :
    LazyChain.patW (LazyChain.glvBases P k σ) 15 = 0 := by
  rw [LazyChain.patW_bases]
  apply zsmul_eq_zero_of_cast_eq_zero
  rw [patScalar_eq_pattern]
  have : patternOf σ 15 = σ := by
    funext j; fin_cases j <;> simp [patternOf, LazyChain.sgn]
  rw [this]
  exact hrel

/-- Unit-magnitude coefficients have unit bit patterns. -/
lemma unitBits_of_natAbs_one (z : ℤ) (hz : z.natAbs = 1) :
    LazyMSM.UnitBits (CoeffWitness.ofInt z).bits := by
  refine ⟨?_, ?_⟩
  · show (CoeffWitness.magnitudeBits z)[(0 : ℕ)] = 1
    simp [CoeffWitness.magnitudeBits, Utils.Bits.toBits, Vector.getElem_map,
      Vector.getElem_mapRange, hz]
  · intro i hi
    show (CoeffWitness.magnitudeBits z)[i.val] = 0
    have : ¬ Nat.testBit 1 i.val := by
      rw [show (1 : ℕ) = 2 ^ 0 from rfl, Nat.testBit_two_pow]
      simp only [decide_eq_true_eq]
      omega
    simp [CoeffWitness.magnitudeBits, Utils.Bits.toBits, Vector.getElem_map,
      Vector.getElem_mapRange, hz, this]

lemma sgnOf_signBit (z : ℤ) (hz : SpecialScalar.IsSign z) : sgnOf (CoeffWitness.signBit z) = z := by
  rcases hz with rfl | rfl <;> simp [CoeffWitness.signBit, sgnOf]

/-- The honest prover (special-scalar decomposition) satisfies the chain's
prover assumptions. -/
theorem honestProverAssumptions (P : Bridge.W.Point) (hP : P ≠ 0) (k : ℕ)
    {buildInput : GLVBuildTable.Inputs (F circomPrime)}
    {table : GLVBuildTable.Table (F circomPrime)}
    (hPd : decodePoint buildInput.P = Bridge.toSpec P)
    (hQd : decodePoint buildInput.Q = Bridge.toSpec (k • P))
    (hs0 : buildInput.sign0 =
      (CoeffWitness.ofDecomposition (SpecialScalar.decomposition (k : ZMod order))).u1.sign)
    (hs1 : buildInput.sign1 =
      (CoeffWitness.ofDecomposition (SpecialScalar.decomposition (k : ZMod order))).u2.sign)
    (hs2 : buildInput.sign2 =
      (CoeffWitness.ofDecomposition (SpecialScalar.decomposition (k : ZMod order))).v1.sign)
    (hs3 : buildInput.sign3 =
      (CoeffWitness.ofDecomposition (SpecialScalar.decomposition (k : ZMod order))).v2.sign)
    (ht : PatBuildTable.Spec buildInput table) :
    LazyMSM.ProverAssumptions
      (msmInput table (CoeffWitness.ofDecomposition (SpecialScalar.decomposition (k : ZMod order)))) := by
  set d := SpecialScalar.decomposition (k : ZMod order) with hd
  set c := CoeffWitness.ofDecomposition d with hcdef
  have hc := CoeffWitness.ofDecomposition_valid d
  have ha := msmAssumptions ht hc
  have htable := patTableFor (c := c) P (k • P) hPd hQd ht
  set σ : Fin 4 → ℤ := fun j => sgnOf (match j with
    | ⟨0, _⟩ => buildInput.sign0 | ⟨1, _⟩ => buildInput.sign1
    | ⟨2, _⟩ => buildInput.sign2 | _ => buildInput.sign3) with hσ
  have hB : basesW buildInput P (k • P) = LazyChain.glvBases P k σ := basesW_eq_glvBases buildInput P k
  have hσs : ∀ j, SpecialScalar.IsSign (σ j) := fun j => sgnOf_isSign _
  have hscalar :
      (GLV.signedValue c.u1 : ZMod order) +
          (GLVAlgebra.lambda : ZMod order) * GLV.signedValue c.u2 +
        (k : ZMod order) *
          ((GLV.signedValue c.v1 : ZMod order) +
            (GLVAlgebra.lambda : ZMod order) * GLV.signedValue c.v2) = 0 := by
    simpa only [c, lambdaZ_eq_lambda] using CoeffWitness.ofDecomposition_relation d
  have hgroup := FakeGLVSound.complete P k _ _ _ _ hscalar
  have hchain : LazyChain.chainAcc (msmInput table c) GLVMSM.coeffBits =
      decodePoint (GLVMSM.tableEntry (msmInput table c) 15 (by norm_num)) := by
    rw [LazyChain.chainAcc_final _ _ ha htable, htable ⟨15, by norm_num⟩]
    apply congrArg Bridge.toSpec
    rw [LazyChain.oddComb_eq_two_linComb]
    simp only [msmInput]
    rw [GLVMSMTheorems.scalarOfBits_coeff_eq_magnitude hc.1,
      GLVMSMTheorems.scalarOfBits_coeff_eq_magnitude hc.2.1,
      GLVMSMTheorems.scalarOfBits_coeff_eq_magnitude hc.2.2.1,
      GLVMSMTheorems.scalarOfBits_coeff_eq_magnitude hc.2.2.2,
      linComb_eq_signed buildInput c P (k • P) hc hs0 hs1 hs2 hs3, hgroup]
    simp
  -- the signs of the flags are the coefficients when the scalar is special
  have hσd : SpecialScalar.IsSpecial (k : ZMod order) →
      σ 0 = d.u₁ ∧ σ 1 = d.u₂ ∧ σ 2 = d.v₁ ∧ σ 3 = d.v₂ := by
    intro hsp
    have hd' := SpecialScalar.decomposition_special _ hsp
    obtain ⟨h0, h1, h2, h3⟩ := SpecialScalar.specialDecomposition_signs _ hsp
    rw [← hd'] at h0 h1 h2 h3
    refine ⟨?_, ?_, ?_, ?_⟩
    · show sgnOf buildInput.sign0 = d.u₁
      rw [hs0]; exact sgnOf_signBit _ h0
    · show sgnOf buildInput.sign1 = d.u₂
      rw [hs1]; exact sgnOf_signBit _ h1
    · show sgnOf buildInput.sign2 = d.v₁
      rw [hs2]; exact sgnOf_signBit _ h2
    · show sgnOf buildInput.sign3 = d.v₂
      rw [hs3]; exact sgnOf_signBit _ h3
  refine ⟨ha, ?_, fun _ => hchain, ?_⟩
  · intro h15 i
    by_contra hne
    have hV := (ht i).1
    have hi1 : table.tinf[i] = 1 := by
      rcases hV.1 with h0 | h1
      · exact absurd h0 hne
      · exact h1
    have hinf : decodePoint (GLVMSM.tableEntry (msmInput table c) i.val i.isLt) = .infinity :=
      CompleteAdd.decodePoint_of_isInf hi1
    rw [htable i, hB] at hinf
    have hpat0 : LazyChain.patW (LazyChain.glvBases P k σ) i.val = 0 :=
      Bridge.toSpec_injective (hinf.trans Bridge.toSpec_zero.symm)
    have hsp := isSpecial_of_entry_zero P hP k σ hσs i.val hpat0
    obtain ⟨e0, e1, e2, e3⟩ := hσd hsp
    have hrel : SpecialScalar.Relation (k : ZMod order) σ := by
      unfold SpecialScalar.Relation
      rw [e0, e1, e2, e3]
      exact d.relation
    have h15z := patW_15_eq_zero P k σ hrel
    have hinf15 : decodePoint (GLVMSM.tableEntry (msmInput table c) 15 (by norm_num)) = .infinity := by
      rw [htable ⟨15, by norm_num⟩, hB, h15z, Bridge.toSpec_zero]
    have h15one := tinf_of_decode_inf (ht ⟨15, by norm_num⟩).1 hinf15
    exact absurd (h15.symm.trans h15one) zero_ne_one
  · intro h15
    have hinf := entry15_inf_of_tinf (c := c) h15
    rw [htable ⟨15, by norm_num⟩, hB] at hinf
    have hpat0 : LazyChain.patW (LazyChain.glvBases P k σ) 15 = 0 :=
      Bridge.toSpec_injective (hinf.trans Bridge.toSpec_zero.symm)
    have hsp := isSpecial_of_entry_zero P hP k σ hσs 15 hpat0
    have hd' := SpecialScalar.decomposition_special _ hsp
    obtain ⟨h0, h1, h2, h3⟩ := SpecialScalar.specialDecomposition_signs _ hsp
    rw [← hd'] at h0 h1 h2 h3
    exact ⟨unitBits_of_natAbs_one _ (SpecialScalar.isSign_natAbs h0),
      unitBits_of_natAbs_one _ (SpecialScalar.isSign_natAbs h1),
      unitBits_of_natAbs_one _ (SpecialScalar.isSign_natAbs h2),
      unitBits_of_natAbs_one _ (SpecialScalar.isSign_natAbs h3)⟩

end Solution.Secp256k1ScalarMul.LazyBridge
