import Solution.Secp256k1ScalarMul.Lazy.PatternTable
import Solution.Secp256k1ScalarMul.GLVBuildTableCostCW
import Solution.Secp256k1ScalarMul.NegYAffineCost
import Solution.Secp256k1ScalarMul.NegYAffineSubCost

/-! Cost, local length and R1CS shape of the sign-pattern table. -/

namespace Solution.Secp256k1ScalarMul.PatTable

open Specs.ShortWeierstrass Specs.Secp256k1
open GLVBuildTable
open Challenge.CostR1CS Cost

set_option maxHeartbeats 16000000
set_option maxRecDepth 20000

/-- `2·68 + 4·1188 + 10·(8 + 68) + 8·1235` allocations. -/
def cost : Count := ⟨15528, 15644⟩

abbrev VP := Var FlaggedPoint (F circomPrime)

theorem negY_costIs_sub (P : VP) : CostIs (subcircuit NegYAffine.circuit P) NegYAffine.CostCert.cost :=
  NegYAffine.CostCert.costIs_sub P

theorem costIs_negCanon (P : VP) :
    CostIs (negCanon P) (⟨4, 4⟩ + (⟨4, 4⟩ + (NegYAffine.CostCert.cost + Count.zero))) := by
  unfold negCanon
  refine CostIs.bind (costIs_sub_mux _) fun _ => ?_
  refine CostIs.bind (costIs_sub_mux _) fun _ => ?_
  refine CostIs.bind (NegYAffine.CostCert.costIs_sub _) fun _ => ?_
  exact CostIs.pure _

def negCanonCost : Count := ⟨4, 4⟩ + (⟨4, 4⟩ + (NegYAffine.CostCert.cost + Count.zero))

theorem costIs_negCanon' (P : VP) : CostIs (negCanon P) negCanonCost := costIs_negCanon P

theorem costIs_main (b : Var Bases (F circomPrime)) : CostIs (main b) cost := by
  rw [show cost = NegYAffine.CostCert.cost + (NegYAffine.CostCert.cost + (phiPairAddCost +
    (phiPairAddCost + (phiPairAddCost + (phiPairAddCost + (negCanonCost + (negCanonCost +
    (completeAddCost + (completeAddCost + (completeAddCost + (completeAddCost + (completeAddCost +
    (completeAddCost + (completeAddCost + (completeAddCost + (negCanonCost + (negCanonCost +
    (negCanonCost + (negCanonCost + (negCanonCost + (negCanonCost + (negCanonCost + (negCanonCost +
    Count.zero))))))))))))))))))))))) from by decide]
  unfold main
  refine CostIs.bind (NegYAffine.CostCert.costIs_sub _) fun _ => ?_
  refine CostIs.bind (NegYAffine.CostCert.costIs_sub _) fun _ => ?_
  refine CostIs.bind (costIs_sub_phiPairAdd _) fun _ => ?_
  refine CostIs.bind (costIs_sub_phiPairAdd _) fun _ => ?_
  refine CostIs.bind (costIs_sub_phiPairAdd _) fun _ => ?_
  refine CostIs.bind (costIs_sub_phiPairAdd _) fun _ => ?_
  refine CostIs.bind (costIs_negCanon' _) fun _ => ?_
  refine CostIs.bind (costIs_negCanon' _) fun _ => ?_
  refine CostIs.bind (costIs_sub_completeAdd _) fun _ => ?_
  refine CostIs.bind (costIs_sub_completeAdd _) fun _ => ?_
  refine CostIs.bind (costIs_sub_completeAdd _) fun _ => ?_
  refine CostIs.bind (costIs_sub_completeAdd _) fun _ => ?_
  refine CostIs.bind (costIs_sub_completeAdd _) fun _ => ?_
  refine CostIs.bind (costIs_sub_completeAdd _) fun _ => ?_
  refine CostIs.bind (costIs_sub_completeAdd _) fun _ => ?_
  refine CostIs.bind (costIs_sub_completeAdd _) fun _ => ?_
  refine CostIs.bind (costIs_negCanon' _) fun _ => ?_
  refine CostIs.bind (costIs_negCanon' _) fun _ => ?_
  refine CostIs.bind (costIs_negCanon' _) fun _ => ?_
  refine CostIs.bind (costIs_negCanon' _) fun _ => ?_
  refine CostIs.bind (costIs_negCanon' _) fun _ => ?_
  refine CostIs.bind (costIs_negCanon' _) fun _ => ?_
  refine CostIs.bind (costIs_negCanon' _) fun _ => ?_
  refine CostIs.bind (costIs_negCanon' _) fun _ => ?_
  exact CostIs.pure _

theorem costIs_call (b : Var Bases (F circomPrime)) : CostIs (subcircuit circuit b) cost :=
  CostIs.subcircuit fun n => costIs_main b n

set_option maxRecDepth 8192 in
lemma circuit_localLength (b : Var Bases (F circomPrime)) : circuit.localLength b = 15528 := rfl

/-! ### Shape -/

theorem negY_isR1CS_sub (P : VP) (hP : AffineFP P) :
    IsR1CSCirc (subcircuit NegYAffine.circuit P) :=
  IsR1CSCirc.subcircuit fun n => NegYAffine.CostCert.isR1CS P hP n

theorem negY_affineW_sub (P : VP) (hP : AffineFP P) (n : ℕ) :
    AffineW ((subcircuit NegYAffine.circuit P).output n) := by
  rw [show (subcircuit NegYAffine.circuit P).output n = (NegYAffine.main P).output n from
    (NegYAffine.elaborated.output_eq P n).symm]
  exact NegYAffine.CostCert.affineW_output P n hP

lemma affineFP_withY (P : VP) (y : Var Emu (F circomPrime)) (hP : AffineFP P) (hy : AffineW y) :
    AffineFP (withY P y) := ⟨hP.1, hy, hP.2.2⟩

lemma affineFP_withXY (P : VP) (x y : Var Emu (F circomPrime)) (hP : AffineFP P)
    (hx : AffineW x) (hy : AffineW y) : AffineFP (withXY P x y) := ⟨hx, hy, hP.2.2⟩

theorem isR1CS_negCanon (P : VP) (hP : AffineFP P) :
    IsR1CSCirc (negCanon P) := by
  have hz0 : AffineProvable (zeroConst : Var Emu (F circomPrime)) := by
    simpa only [zeroConst] using (affineW_emuConst 0).affineProvable
  unfold negCanon
  refine IsR1CSCirc.bind_out (isR1CS_sub_mux _ hP.2.2 hz0 hP.1.affineProvable) fun nx => ?_
  have hx := (affineProvable_sub_mux (M := Emu)
    { selector := P.isInf, ifTrue := zeroConst, ifFalse := P.x } nx).affineW
  refine IsR1CSCirc.bind_out (isR1CS_sub_mux _ hP.2.2 hz0 hP.2.1.affineProvable) fun ny => ?_
  have hy := (affineProvable_sub_mux (M := Emu)
    { selector := P.isInf, ifTrue := zeroConst, ifFalse := P.y } ny).affineW
  refine IsR1CSCirc.bind_out (negY_isR1CS_sub _ (affineFP_withXY P _ _ hP hx hy)) fun nn => ?_
  exact IsR1CSCirc.pure _

theorem affineFP_negCanon (P : VP) (hP : AffineFP P) (n : ℕ) :
    AffineFP ((negCanon P).output n).1 ∧ AffineFP ((negCanon P).output n).2 := by
  have hz0 : AffineProvable (zeroConst : Var Emu (F circomPrime)) := by
    simpa only [zeroConst] using (affineW_emuConst 0).affineProvable
  have hx := (affineProvable_sub_mux (M := Emu)
    { selector := P.isInf, ifTrue := zeroConst, ifFalse := P.x } n).affineW
  have hy := (affineProvable_sub_mux (M := Emu)
    { selector := P.isInf, ifTrue := zeroConst, ifFalse := P.y } (n + 4)).affineW
  simp only [negCanon, circuit_norm]
  refine ⟨⟨?_, ?_, hP.2.2⟩, ⟨?_, ?_, hP.2.2⟩⟩
  · exact hx
  · exact hy
  · exact hx
  · exact negY_affineW_sub _ (affineFP_withXY P _ _ hP hx hy) _

end Solution.Secp256k1ScalarMul.PatTable

namespace Solution.Secp256k1ScalarMul.PatTable

open Specs.ShortWeierstrass Specs.Secp256k1
open GLVBuildTable
open Challenge.CostR1CS Cost

set_option maxHeartbeats 16000000
set_option maxRecDepth 65536

/-! ### Full shape -/

theorem affineFP_bases (b : Var Bases (F circomPrime)) (hb : ∀ i : Fin 4, AffineFP (baseEntryV b i)) :
    AffineFP b.r0 ∧ AffineFP b.r1 ∧ AffineFP b.r2 ∧ AffineFP b.r3 :=
  ⟨hb 0, hb 1, hb 2, hb 3⟩

theorem isR1CS_main (b : Var Bases (F circomPrime)) (hb : ∀ i : Fin 4, AffineFP (baseEntryV b i)) :
    IsR1CSCirc (main b) := by
  obtain ⟨h0, h1, h2, h3⟩ := affineFP_bases b hb
  unfold main
  refine Solution.Secp256k1ScalarMulFixedBase.Cost.IsR1CSCirc.bind_out_inv AffineW
    (negY_isR1CS_sub _ h1) (fun n => negY_affineW_sub _ h1 n) fun nr1y hn1 => ?_
  refine Solution.Secp256k1ScalarMulFixedBase.Cost.IsR1CSCirc.bind_out_inv AffineW
    (negY_isR1CS_sub _ h3) (fun n => negY_affineW_sub _ h3 n) fun nr3y hn3 => ?_
  refine Solution.Secp256k1ScalarMulFixedBase.Cost.IsR1CSCirc.bind_out_inv AffineFP
    (isR1CS_sub_phiPairAdd _ h0 h1) (fun n => affineFP_sub_phiPairAdd _ n h0) fun up hup => ?_
  refine Solution.Secp256k1ScalarMulFixedBase.Cost.IsR1CSCirc.bind_out_inv AffineFP
    (isR1CS_sub_phiPairAdd _ h0 (affineFP_withY _ _ h1 hn1)) (fun n => affineFP_sub_phiPairAdd _ n h0)
    fun um hum => ?_
  refine Solution.Secp256k1ScalarMulFixedBase.Cost.IsR1CSCirc.bind_out_inv AffineFP
    (isR1CS_sub_phiPairAdd _ h2 h3) (fun n => affineFP_sub_phiPairAdd _ n h2) fun vp hvp => ?_
  refine Solution.Secp256k1ScalarMulFixedBase.Cost.IsR1CSCirc.bind_out_inv AffineFP
    (isR1CS_sub_phiPairAdd _ h2 (affineFP_withY _ _ h3 hn3)) (fun n => affineFP_sub_phiPairAdd _ n h2)
    fun vm hvm => ?_
  refine Solution.Secp256k1ScalarMulFixedBase.Cost.IsR1CSCirc.bind_out_inv
    (fun p : VP × VP => AffineFP p.1 ∧ AffineFP p.2)
    (isR1CS_negCanon _ hvp) (fun n => affineFP_negCanon _ hvp n) fun vpp hvpp => ?_
  obtain ⟨hvp', hnvp⟩ := hvpp
  refine Solution.Secp256k1ScalarMulFixedBase.Cost.IsR1CSCirc.bind_out_inv
    (fun p : VP × VP => AffineFP p.1 ∧ AffineFP p.2)
    (isR1CS_negCanon _ hvm) (fun n => affineFP_negCanon _ hvm n) fun vmp hvmp => ?_
  obtain ⟨hvm', hnvm⟩ := hvmp
  refine Solution.Secp256k1ScalarMulFixedBase.Cost.IsR1CSCirc.bind_out_inv AffineFP
    (isR1CS_sub_completeAdd _ hup hvp') (fun n => affineFP_sub_completeAdd _ n) fun e15 h15 => ?_
  refine Solution.Secp256k1ScalarMulFixedBase.Cost.IsR1CSCirc.bind_out_inv AffineFP
    (isR1CS_sub_completeAdd _ hup hvm') (fun n => affineFP_sub_completeAdd _ n) fun e7 h7 => ?_
  refine Solution.Secp256k1ScalarMulFixedBase.Cost.IsR1CSCirc.bind_out_inv AffineFP
    (isR1CS_sub_completeAdd _ hup hnvm) (fun n => affineFP_sub_completeAdd _ n) fun e11 h11 => ?_
  refine Solution.Secp256k1ScalarMulFixedBase.Cost.IsR1CSCirc.bind_out_inv AffineFP
    (isR1CS_sub_completeAdd _ hup hnvp) (fun n => affineFP_sub_completeAdd _ n) fun e3 h3' => ?_
  refine Solution.Secp256k1ScalarMulFixedBase.Cost.IsR1CSCirc.bind_out_inv AffineFP
    (isR1CS_sub_completeAdd _ hum hvp') (fun n => affineFP_sub_completeAdd _ n) fun e13 h13 => ?_
  refine Solution.Secp256k1ScalarMulFixedBase.Cost.IsR1CSCirc.bind_out_inv AffineFP
    (isR1CS_sub_completeAdd _ hum hvm') (fun n => affineFP_sub_completeAdd _ n) fun e5 h5 => ?_
  refine Solution.Secp256k1ScalarMulFixedBase.Cost.IsR1CSCirc.bind_out_inv AffineFP
    (isR1CS_sub_completeAdd _ hum hnvm) (fun n => affineFP_sub_completeAdd _ n) fun e9 h9 => ?_
  refine Solution.Secp256k1ScalarMulFixedBase.Cost.IsR1CSCirc.bind_out_inv AffineFP
    (isR1CS_sub_completeAdd _ hum hnvp) (fun n => affineFP_sub_completeAdd _ n) fun e1 h1' => ?_
  refine IsR1CSCirc.bind_out (isR1CS_negCanon _ h15) fun _ => ?_
  refine IsR1CSCirc.bind_out (isR1CS_negCanon _ h7) fun _ => ?_
  refine IsR1CSCirc.bind_out (isR1CS_negCanon _ h11) fun _ => ?_
  refine IsR1CSCirc.bind_out (isR1CS_negCanon _ h3') fun _ => ?_
  refine IsR1CSCirc.bind_out (isR1CS_negCanon _ h13) fun _ => ?_
  refine IsR1CSCirc.bind_out (isR1CS_negCanon _ h5) fun _ => ?_
  refine IsR1CSCirc.bind_out (isR1CS_negCanon _ h9) fun _ => ?_
  refine IsR1CSCirc.bind_out (isR1CS_negCanon _ h1') fun _ => ?_
  exact IsR1CSCirc.pure _

theorem isR1CS_call (b : Var Bases (F circomPrime)) (hb : ∀ i : Fin 4, AffineFP (baseEntryV b i)) :
    IsR1CSCirc (subcircuit circuit b) :=
  IsR1CSCirc.subcircuit fun n => isR1CS_main b hb n

/-- Every raw entry of the output is an affine point. -/
theorem affine_output (b : Var Bases (F circomPrime)) (hb : ∀ i : Fin 4, AffineFP (baseEntryV b i))
    (n : ℕ) : ∀ i : Fin 16, AffineFP (rawEntryV ((main b).output n) i) := by
  obtain ⟨h0, h1, h2, h3⟩ := affineFP_bases b hb
  simp only [main, negCanon, Circuit.bind_output_eq, Circuit.pure_output_eq]
  intro i
  fin_cases i <;> simp only [rawEntryV]
  all_goals first
    | exact affineFP_sub_completeAdd _ _
    | exact affineFP_withXY _ _ _ (affineFP_sub_completeAdd _ _) (affineProvable_sub_mux _ _).affineW
        (negY_affineW_sub _ (affineFP_withXY _ _ _ (affineFP_sub_completeAdd _ _)
          (affineProvable_sub_mux _ _).affineW (affineProvable_sub_mux _ _).affineW) _)

theorem affine_call_output (b : Var Bases (F circomPrime))
    (hb : ∀ i : Fin 4, AffineFP (baseEntryV b i)) (n : ℕ) :
    ∀ i : Fin 16, AffineFP (rawEntryV ((subcircuit circuit b).output n) i) := by
  rw [show (subcircuit circuit b).output n = (main b).output n from
    (elaborated.output_eq b n).symm]
  exact affine_output b hb n

end Solution.Secp256k1ScalarMul.PatTable
