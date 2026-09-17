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
