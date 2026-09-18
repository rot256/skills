import Solution.Secp256k1ScalarMul.Lazy.PatternTable
import Solution.Secp256k1ScalarMul.GLVBuildTableCostCW
import Solution.Secp256k1ScalarMul.NegYAffineCost
import Solution.Secp256k1ScalarMul.NegYAffineSubCost
import Solution.Secp256k1ScalarMul.Lazy_Donor7
import Solution.Secp256k1ScalarMul.NegYAffineCW

/-! ## merged from `Lazy/PatternTableCost.lean` -/
section
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
open Solution.Secp256k1ScalarMulFixedBase.Cost (IsR1CSCirc.bind_out_inv)

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
  refine IsR1CSCirc.bind_out_inv AffineW
    (negY_isR1CS_sub _ h1) (fun n => negY_affineW_sub _ h1 n) fun nr1y hn1 => ?_
  refine IsR1CSCirc.bind_out_inv AffineW
    (negY_isR1CS_sub _ h3) (fun n => negY_affineW_sub _ h3 n) fun nr3y hn3 => ?_
  refine IsR1CSCirc.bind_out_inv AffineFP
    (isR1CS_sub_phiPairAdd _ h0 h1) (fun n => affineFP_sub_phiPairAdd _ n h0) fun up hup => ?_
  refine IsR1CSCirc.bind_out_inv AffineFP
    (isR1CS_sub_phiPairAdd _ h0 (affineFP_withY _ _ h1 hn1)) (fun n => affineFP_sub_phiPairAdd _ n h0)
    fun um hum => ?_
  refine IsR1CSCirc.bind_out_inv AffineFP
    (isR1CS_sub_phiPairAdd _ h2 h3) (fun n => affineFP_sub_phiPairAdd _ n h2) fun vp hvp => ?_
  refine IsR1CSCirc.bind_out_inv AffineFP
    (isR1CS_sub_phiPairAdd _ h2 (affineFP_withY _ _ h3 hn3)) (fun n => affineFP_sub_phiPairAdd _ n h2)
    fun vm hvm => ?_
  refine IsR1CSCirc.bind_out_inv
    (fun p : VP × VP => AffineFP p.1 ∧ AffineFP p.2)
    (isR1CS_negCanon _ hvp) (fun n => affineFP_negCanon _ hvp n) fun vpp hvpp => ?_
  obtain ⟨hvp', hnvp⟩ := hvpp
  refine IsR1CSCirc.bind_out_inv
    (fun p : VP × VP => AffineFP p.1 ∧ AffineFP p.2)
    (isR1CS_negCanon _ hvm) (fun n => affineFP_negCanon _ hvm n) fun vmp hvmp => ?_
  obtain ⟨hvm', hnvm⟩ := hvmp
  refine IsR1CSCirc.bind_out_inv AffineFP
    (isR1CS_sub_completeAdd _ hup hvp') (fun n => affineFP_sub_completeAdd _ n) fun e15 h15 => ?_
  refine IsR1CSCirc.bind_out_inv AffineFP
    (isR1CS_sub_completeAdd _ hup hvm') (fun n => affineFP_sub_completeAdd _ n) fun e7 h7 => ?_
  refine IsR1CSCirc.bind_out_inv AffineFP
    (isR1CS_sub_completeAdd _ hup hnvm) (fun n => affineFP_sub_completeAdd _ n) fun e11 h11 => ?_
  refine IsR1CSCirc.bind_out_inv AffineFP
    (isR1CS_sub_completeAdd _ hup hnvp) (fun n => affineFP_sub_completeAdd _ n) fun e3 h3' => ?_
  refine IsR1CSCirc.bind_out_inv AffineFP
    (isR1CS_sub_completeAdd _ hum hvp') (fun n => affineFP_sub_completeAdd _ n) fun e13 h13 => ?_
  refine IsR1CSCirc.bind_out_inv AffineFP
    (isR1CS_sub_completeAdd _ hum hvm') (fun n => affineFP_sub_completeAdd _ n) fun e5 h5 => ?_
  refine IsR1CSCirc.bind_out_inv AffineFP
    (isR1CS_sub_completeAdd _ hum hnvm) (fun n => affineFP_sub_completeAdd _ n) fun e9 h9 => ?_
  refine IsR1CSCirc.bind_out_inv AffineFP
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

/-- Output invariants along a circuit, without computing the output. -/
def OutInv {α : Type} (P : α → Prop) (c : Circuit (F circomPrime) α) : Prop := ∀ n, P (c.output n)

lemma OutInv.bind {α β : Type} {P : α → Prop} {Q : β → Prop} {f : Circuit (F circomPrime) α}
    {g : α → Circuit (F circomPrime) β} (hf : OutInv P f) (hg : ∀ a, P a → OutInv Q (g a)) :
    OutInv Q (f >>= g) := fun n => by
  rw [Circuit.bind_output_eq]
  exact hg _ (hf n) _

lemma OutInv.pure {α : Type} {P : α → Prop} {a : α} (h : P a) :
    OutInv P (pure a : Circuit (F circomPrime) α) := fun n => by
  rw [Circuit.pure_output_eq]
  exact h

theorem affine_output_inv (b : Var Bases (F circomPrime)) (hb : ∀ i : Fin 4, AffineFP (baseEntryV b i)) :
    OutInv (fun t => ∀ i : Fin 16, AffineFP (rawEntryV t i)) (main b) := by
  obtain ⟨h0, h1, h2, h3⟩ := affineFP_bases b hb
  unfold main
  refine OutInv.bind (P := AffineW) (fun n => negY_affineW_sub _ h1 n) fun nr1y hn1 => ?_
  refine OutInv.bind (P := AffineW) (fun n => negY_affineW_sub _ h3 n) fun nr3y hn3 => ?_
  refine OutInv.bind (P := AffineFP) (fun n => affineFP_sub_phiPairAdd _ n h0) fun up hup => ?_
  refine OutInv.bind (P := AffineFP) (fun n => affineFP_sub_phiPairAdd _ n h0) fun um hum => ?_
  refine OutInv.bind (P := AffineFP) (fun n => affineFP_sub_phiPairAdd _ n h2) fun vp hvp => ?_
  refine OutInv.bind (P := AffineFP) (fun n => affineFP_sub_phiPairAdd _ n h2) fun vm hvm => ?_
  refine OutInv.bind (P := fun p : VP × VP => AffineFP p.1 ∧ AffineFP p.2)
    (fun n => affineFP_negCanon _ hvp n) fun vpp hvpp => ?_
  obtain ⟨hvp', hnvp⟩ := hvpp
  refine OutInv.bind (P := fun p : VP × VP => AffineFP p.1 ∧ AffineFP p.2)
    (fun n => affineFP_negCanon _ hvm n) fun vmp hvmp => ?_
  obtain ⟨hvm', hnvm⟩ := hvmp
  refine OutInv.bind (P := AffineFP) (fun n => affineFP_sub_completeAdd _ n) fun e15 h15 => ?_
  refine OutInv.bind (P := AffineFP) (fun n => affineFP_sub_completeAdd _ n) fun e7 h7 => ?_
  refine OutInv.bind (P := AffineFP) (fun n => affineFP_sub_completeAdd _ n) fun e11 h11 => ?_
  refine OutInv.bind (P := AffineFP) (fun n => affineFP_sub_completeAdd _ n) fun e3 h3' => ?_
  refine OutInv.bind (P := AffineFP) (fun n => affineFP_sub_completeAdd _ n) fun e13 h13 => ?_
  refine OutInv.bind (P := AffineFP) (fun n => affineFP_sub_completeAdd _ n) fun e5 h5 => ?_
  refine OutInv.bind (P := AffineFP) (fun n => affineFP_sub_completeAdd _ n) fun e9 h9 => ?_
  refine OutInv.bind (P := AffineFP) (fun n => affineFP_sub_completeAdd _ n) fun e1 h1' => ?_
  refine OutInv.bind (P := fun p : VP × VP => AffineFP p.1 ∧ AffineFP p.2)
    (fun n => affineFP_negCanon _ h15 n) fun p0 hp0 => ?_
  refine OutInv.bind (P := fun p : VP × VP => AffineFP p.1 ∧ AffineFP p.2)
    (fun n => affineFP_negCanon _ h7 n) fun p8 hp8 => ?_
  refine OutInv.bind (P := fun p : VP × VP => AffineFP p.1 ∧ AffineFP p.2)
    (fun n => affineFP_negCanon _ h11 n) fun p4 hp4 => ?_
  refine OutInv.bind (P := fun p : VP × VP => AffineFP p.1 ∧ AffineFP p.2)
    (fun n => affineFP_negCanon _ h3' n) fun p12 hp12 => ?_
  refine OutInv.bind (P := fun p : VP × VP => AffineFP p.1 ∧ AffineFP p.2)
    (fun n => affineFP_negCanon _ h13 n) fun p2 hp2 => ?_
  refine OutInv.bind (P := fun p : VP × VP => AffineFP p.1 ∧ AffineFP p.2)
    (fun n => affineFP_negCanon _ h5 n) fun p10 hp10 => ?_
  refine OutInv.bind (P := fun p : VP × VP => AffineFP p.1 ∧ AffineFP p.2)
    (fun n => affineFP_negCanon _ h9 n) fun p6 hp6 => ?_
  refine OutInv.bind (P := fun p : VP × VP => AffineFP p.1 ∧ AffineFP p.2)
    (fun n => affineFP_negCanon _ h1' n) fun p14 hp14 => ?_
  apply OutInv.pure
  intro i
  fin_cases i <;> simp only [rawEntryV]
  · exact hp0.2
  · exact h1'
  · exact hp2.2
  · exact h3'
  · exact hp4.2
  · exact h5
  · exact hp6.2
  · exact h7
  · exact hp8.2
  · exact h9
  · exact hp10.2
  · exact h11
  · exact hp12.2
  · exact h13
  · exact hp14.2
  · exact h15

/-- Every raw entry of the output is an affine point. -/
theorem affine_output (b : Var Bases (F circomPrime)) (hb : ∀ i : Fin 4, AffineFP (baseEntryV b i))
    (n : ℕ) : ∀ i : Fin 16, AffineFP (rawEntryV ((main b).output n) i) :=
  affine_output_inv b hb n

theorem affine_call_output (b : Var Bases (F circomPrime))
    (hb : ∀ i : Fin 4, AffineFP (baseEntryV b i)) (n : ℕ) :
    ∀ i : Fin 16, AffineFP (rawEntryV ((subcircuit circuit b).output n) i) := by
  rw [show (subcircuit circuit b).output n = (main b).output n from
    (elaborated.output_eq b n).symm]
  exact affine_output b hb n

end Solution.Secp256k1ScalarMul.PatTable
end

/-! ## merged from `Lazy/PatternTableCW.lean` -/
section
/-! Computable witnesses of the sign-pattern table. -/

namespace Solution.Secp256k1ScalarMul.PatTable

open Specs.ShortWeierstrass Specs.Secp256k1
open GLVBuildTable
open Challenge.Utils.ComputableWitnessLemmas

set_option maxHeartbeats 16000000
set_option maxRecDepth 20000

abbrev CF := F circomPrime
abbrev PE := ProverEnvironment (F circomPrime)

/-! ### Stability of the building blocks -/

lemma completeAdd_output_stable (X : Var CompleteAdd.Inputs CF) {off k : ℕ} {e e' : PE}
    (h_agree : e.AgreesBelow k e') (hk : off + 1235 ≤ k) :
    eval e ((subcircuit CompleteAdd.circuit X).output off) =
      eval e' ((subcircuit CompleteAdd.circuit X).output off) := by
  have h := CompleteAdd.eval_output_of_agreesBelow X h_agree hk
  rw [CompleteAdd.elaborated.output_eq X off] at h
  exact h

lemma phiPairAdd_output_stable (X : Var PhiPairAdd.Inputs CF) {off k : ℕ} {e e' : PE}
    (h_input : eval e X = eval e' X) (h_agree : e.AgreesBelow k e') (hk : off + 1188 ≤ k) :
    eval e ((subcircuit PhiPairAdd.circuit X).output off) =
      eval e' ((subcircuit PhiPairAdd.circuit X).output off) := by
  have h := PhiPairAdd.eval_output_of_agreesBelow X h_input h_agree hk
  rw [PhiPairAdd.elaborated.output_eq X off] at h
  exact h

lemma muxEmu_output_stable (X : Var (Mux.Inputs Emu) CF) {off k : ℕ} {e e' : PE}
    (h_agree : e.AgreesBelow k e') (hk : off + 4 ≤ k) :
    eval e ((subcircuit (Mux.circuit (M := Emu)) X).output off) =
      eval e' ((subcircuit (Mux.circuit (M := Emu)) X).output off) := by
  have h := Mux.eval_output_of_agreesBelow (M := Emu) X (offset := off) h_agree (by
    simp only [size, numLimbs]
    omega)
  exact h

lemma negY_output_stable (X : VP) {off k : ℕ} {e e' : PE}
    (hX : eval e X = eval e' X) (h_agree : e.AgreesBelow k e') (hk : off + 68 ≤ k) :
    eval e ((subcircuit NegYAffine.circuit X).output off) =
      eval e' ((subcircuit NegYAffine.circuit X).output off) := by
  simpa only [circuit_norm, subcircuit, NegYAffine.circuit, NegYAffine.elaborated] using
    (NegYAffine.eval_output_of_agreesBelow X hX h_agree (by omega))

lemma cond_completeAdd {e e' : PE} (P Q : VP)
    (hP : eval e P = eval e' P) (hQ : eval e Q = eval e' Q) :
    eval e ({ P := P, Q := Q } : Var CompleteAdd.Inputs CF) =
      eval e' ({ P := P, Q := Q } : Var CompleteAdd.Inputs CF) := by
  simp only [circuit_norm] at hP hQ ⊢
  rw [CompleteAdd.Inputs.mk.injEq]
  exact ⟨hP, hQ⟩

lemma cond_phiPairAdd {e e' : PE} (P Q : VP)
    (hP : eval e P = eval e' P) (hQ : eval e Q = eval e' Q) :
    eval e ({ P := P, Q := Q } : Var PhiPairAdd.Inputs CF) =
      eval e' ({ P := P, Q := Q } : Var PhiPairAdd.Inputs CF) := by
  simp only [circuit_norm] at hP hQ ⊢
  rw [PhiPairAdd.Inputs.mk.injEq]
  exact ⟨hP, hQ⟩

lemma point_parts {e e' : PE} (P : VP) (hP : eval e P = eval e' P) :
    eval e P.x = eval e' P.x ∧ eval e P.y = eval e' P.y ∧
    Expression.eval e.toEnvironment P.isInf = Expression.eval e'.toEnvironment P.isInf := by
  simp only [circuit_norm, FlaggedPoint.mk.injEq] at hP
  exact ⟨by simpa only [circuit_norm] using hP.1, by simpa only [circuit_norm] using hP.2.1,
    by simpa only [circuit_norm] using hP.2.2⟩

lemma zeroConst_emu_stable {e e' : PE} :
    eval e (zeroConst : Var Emu CF) = eval e' (zeroConst : Var Emu CF) := by
  rw [CircuitType.eval_var_fields_prover, CircuitType.eval_var_fields_prover]
  rw [DivOrZero.eval_zeroConst, DivOrZero.eval_zeroConst]

lemma cond_muxEmu {e e' : PE} (s : Expression CF) (t f : Var Emu CF)
    (hs : Expression.eval e.toEnvironment s = Expression.eval e'.toEnvironment s)
    (ht : eval e t = eval e' t) (hf : eval e f = eval e' f) :
    eval e ({ selector := s, ifTrue := t, ifFalse := f } : Var (Mux.Inputs Emu) CF) =
      eval e' ({ selector := s, ifTrue := t, ifFalse := f } : Var (Mux.Inputs Emu) CF) := by
  simp only [circuit_norm]
  rw [Mux.Inputs.mk.injEq]
  exact ⟨hs, by simpa only [circuit_norm] using ht, by simpa only [circuit_norm] using hf⟩

lemma withY_stable {e e' : PE} (P : VP) (y : Var Emu CF)
    (hP : eval e P = eval e' P) (hy : eval e y = eval e' y) :
    eval e (withY P y) = eval e' (withY P y) := by
  obtain ⟨hx, -, hi⟩ := point_parts P hP
  simp only [withY, circuit_norm, FlaggedPoint.mk.injEq]
  exact ⟨by simpa only [circuit_norm] using hx, by simpa only [circuit_norm] using hy, hi⟩

lemma withXY_stable {e e' : PE} (P : VP) (x y : Var Emu CF)
    (hP : eval e P = eval e' P) (hx : eval e x = eval e' x) (hy : eval e y = eval e' y) :
    eval e (withXY P x y) = eval e' (withXY P x y) := by
  obtain ⟨-, -, hi⟩ := point_parts P hP
  simp only [withXY, circuit_norm, FlaggedPoint.mk.injEq]
  exact ⟨by simpa only [circuit_norm] using hx, by simpa only [circuit_norm] using hy, hi⟩

/-- The canonicalising muxes of `negCanon P` at offset `o`. -/
lemma canon_muxes_stable (P : VP) {o k : ℕ} {e e' : PE}
    (hP : eval e P = eval e' P) (h_agree : e.AgreesBelow k e') (hk : o + 8 ≤ k) :
    eval e ((subcircuit (Mux.circuit (M := Emu))
        { selector := P.isInf, ifTrue := zeroConst, ifFalse := P.x }).output o) =
      eval e' ((subcircuit (Mux.circuit (M := Emu))
        { selector := P.isInf, ifTrue := zeroConst, ifFalse := P.x }).output o) ∧
    eval e ((subcircuit (Mux.circuit (M := Emu))
        { selector := P.isInf, ifTrue := zeroConst, ifFalse := P.y }).output (o + 4)) =
      eval e' ((subcircuit (Mux.circuit (M := Emu))
        { selector := P.isInf, ifTrue := zeroConst, ifFalse := P.y }).output (o + 4)) :=
  ⟨muxEmu_output_stable _ h_agree (by omega), muxEmu_output_stable _ h_agree (by omega)⟩

/-- Both outputs of `negCanon P` placed at offset `o` (mux, mux, negation). -/
lemma negCanon_outputs_stable (P : VP) {o k : ℕ} {e e' : PE}
    (hP : eval e P = eval e' P) (h_agree : e.AgreesBelow k e') (hk : o + 76 ≤ k) :
    eval e (withXY P
        ((subcircuit (Mux.circuit (M := Emu))
          { selector := P.isInf, ifTrue := zeroConst, ifFalse := P.x }).output o)
        ((subcircuit (Mux.circuit (M := Emu))
          { selector := P.isInf, ifTrue := zeroConst, ifFalse := P.y }).output (o + 4))) =
      eval e' (withXY P
        ((subcircuit (Mux.circuit (M := Emu))
          { selector := P.isInf, ifTrue := zeroConst, ifFalse := P.x }).output o)
        ((subcircuit (Mux.circuit (M := Emu))
          { selector := P.isInf, ifTrue := zeroConst, ifFalse := P.y }).output (o + 4))) ∧
    eval e (withXY P
        ((subcircuit (Mux.circuit (M := Emu))
          { selector := P.isInf, ifTrue := zeroConst, ifFalse := P.x }).output o)
        ((subcircuit NegYAffine.circuit (withXY P
          ((subcircuit (Mux.circuit (M := Emu))
            { selector := P.isInf, ifTrue := zeroConst, ifFalse := P.x }).output o)
          ((subcircuit (Mux.circuit (M := Emu))
            { selector := P.isInf, ifTrue := zeroConst, ifFalse := P.y }).output (o + 4)))).output
          (o + 4 + 4))) =
      eval e' (withXY P
        ((subcircuit (Mux.circuit (M := Emu))
          { selector := P.isInf, ifTrue := zeroConst, ifFalse := P.x }).output o)
        ((subcircuit NegYAffine.circuit (withXY P
          ((subcircuit (Mux.circuit (M := Emu))
            { selector := P.isInf, ifTrue := zeroConst, ifFalse := P.x }).output o)
          ((subcircuit (Mux.circuit (M := Emu))
            { selector := P.isInf, ifTrue := zeroConst, ifFalse := P.y }).output (o + 4)))).output
          (o + 4 + 4))) := by
  obtain ⟨hmx, hmy⟩ := canon_muxes_stable (o := o) P hP h_agree (by omega)
  have hc := withXY_stable P _ _ hP hmx hmy
  exact ⟨hc, withXY_stable P _ _ hP hmx (negY_output_stable _ hc h_agree (by omega))⟩

end Solution.Secp256k1ScalarMul.PatTable

namespace Solution.Secp256k1ScalarMul.PatTable

open Specs.ShortWeierstrass Specs.Secp256k1
open GLVBuildTable
open Challenge.Utils.ComputableWitnessLemmas

set_option maxHeartbeats 16000000
set_option maxRecDepth 20000

lemma bases_parts {e e' : PE} (b : Var Bases CF) (h : eval e b = eval e' b) :
    eval e b.r0 = eval e' b.r0 ∧ eval e b.r1 = eval e' b.r1 ∧
    eval e b.r2 = eval e' b.r2 ∧ eval e b.r3 = eval e' b.r3 := by
  simpa only [circuit_norm, Bases.mk.injEq] using h

/-! Compositional structural computable witnesses.  `Stab o a` says that the
expression `a` evaluates identically in any two prover environments that agree
below `o` and agree on the input `b`; `SInvAt` threads it through the binds
without ever unfolding `main`. -/

section SInv
variable (b : Var Bases CF) (env env' : PE)

def Stab (o : ℕ) {M : TypeMap} [ProvableType M] (a : Var M CF) : Prop :=
  ∀ (k : ℕ) (e e' : PE), o ≤ k → e.AgreesBelow k e' → eval e b = eval e' b → eval e a = eval e' a

def SInvAt {α : Type} (o : ℕ) (P : ℕ → α → Prop) (c : Circuit CF α) : Prop :=
  FormalCircuitBase.Operations.StructuralComputableWitnesses b env env' o (c.operations o) ∧
    P (o + c.localLength o) (c.output o)

variable {b env env'}

lemma SInvAt.bind {α β : Type} {o : ℕ} {P : ℕ → α → Prop} {Q : ℕ → β → Prop}
    {f : Circuit CF α} {g : α → Circuit CF β} (hf : SInvAt b env env' o P f)
    (hg : ∀ a, P (o + f.localLength o) a → SInvAt b env env' (o + f.localLength o) Q (g a)) :
    SInvAt b env env' o Q (f >>= g) := by
  obtain ⟨hs, hp⟩ := hf
  obtain ⟨hs', hq⟩ := hg _ hp
  refine ⟨?_, ?_⟩
  · rw [Circuit.bind_structuralComputableWitnesses_iff]
    exact ⟨hs, hs'⟩
  · rw [Circuit.bind_localLength_eq, Circuit.bind_output_eq, ← Nat.add_assoc]
    exact hq

lemma SInvAt.pure {α : Type} {o : ℕ} {P : ℕ → α → Prop} {a : α} (h : P o a) :
    SInvAt b env env' o P (pure a : Circuit CF α) := by
  refine ⟨?_, ?_⟩
  · rw [Circuit.pure_structuralComputableWitnesses_iff]; trivial
  · rw [Circuit.pure_localLength_eq, Circuit.pure_output_eq, Nat.add_zero]; exact h

lemma Stab.mono {o o' : ℕ} {M : TypeMap} [ProvableType M] {a : Var M CF} (h : Stab b o a)
    (hle : o ≤ o') : Stab b o' a := fun k e e' hk => h k e e' (by omega)

lemma stab_of_eq {o : ℕ} {M : TypeMap} [ProvableType M] {a : Var M CF}
    (h : ∀ e e' : PE, eval e b = eval e' b → eval e a = eval e' a) : Stab b o a :=
  fun _ e e' _ _ hb => h e e' hb

lemma stab_pair {o : ℕ} {P Q : VP} (hP : Stab b o P) (hQ : Stab b o Q) :
    Stab b o ({ P := P, Q := Q } : Var CompleteAdd.Inputs CF) :=
  fun k e e' hk hag hb => cond_completeAdd P Q (hP k e e' hk hag hb) (hQ k e e' hk hag hb)

lemma stab_pairPhi {o : ℕ} {P Q : VP} (hP : Stab b o P) (hQ : Stab b o Q) :
    Stab b o ({ P := P, Q := Q } : Var PhiPairAdd.Inputs CF) :=
  fun k e e' hk hag hb => cond_phiPairAdd P Q (hP k e e' hk hag hb) (hQ k e e' hk hag hb)

lemma stab_withY {o : ℕ} {P : VP} {y : Var Emu CF} (hP : Stab b o P) (hy : Stab b o y) :
    Stab b o (withY P y) :=
  fun k e e' hk hag hb => withY_stable P y (hP k e e' hk hag hb) (hy k e e' hk hag hb)

lemma stab_withXY {o : ℕ} {P : VP} {x y : Var Emu CF} (hP : Stab b o P) (hx : Stab b o x)
    (hy : Stab b o y) : Stab b o (withXY P x y) :=
  fun k e e' hk hag hb =>
    withXY_stable P x y (hP k e e' hk hag hb) (hx k e e' hk hag hb) (hy k e e' hk hag hb)

lemma stab_muxInput {o : ℕ} {P : VP} {c : Var Emu CF} (hP : Stab b o P) (hc : Stab b o c) :
    Stab b o ({ selector := P.isInf, ifTrue := zeroConst, ifFalse := c } : Var (Mux.Inputs Emu) CF) :=
  fun k e e' hk hag hb => by
    obtain ⟨-, -, hi⟩ := point_parts P (hP k e e' hk hag hb)
    exact cond_muxEmu _ _ _ hi zeroConst_emu_stable (hc k e e' hk hag hb)

lemma stab_x {o : ℕ} {P : VP} (hP : Stab b o P) : Stab b o (M := Emu) P.x :=
  fun k e e' hk hag hb => (point_parts P (hP k e e' hk hag hb)).1
lemma stab_y {o : ℕ} {P : VP} (hP : Stab b o P) : Stab b o (M := Emu) P.y :=
  fun k e e' hk hag hb => (point_parts P (hP k e e' hk hag hb)).2.1

lemma sinv_completeAdd {o : ℕ} (X : Var CompleteAdd.Inputs CF) (hX : Stab b o X) :
    SInvAt b env env' o (fun o' t => Stab b o' t) (subcircuit CompleteAdd.circuit X) := by
  have hl : (subcircuit CompleteAdd.circuit X).localLength o = 1235 := rfl
  refine ⟨?_, ?_⟩
  · rw [FormalCircuit.subcircuit_structuralComputableWitnesses_iff]
    exact FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Bases) CompleteAdd.circuit b X o (fun k e e' hk hag hb => hX k e e' hk hag hb)
      CompleteAdd.computableWitnesses env env'
  · intro k e e' hk hag _
    exact completeAdd_output_stable X hag (by omega)

lemma sinv_phiPairAdd {o : ℕ} (X : Var PhiPairAdd.Inputs CF) (hX : Stab b o X) :
    SInvAt b env env' o (fun o' t => Stab b o' t) (subcircuit PhiPairAdd.circuit X) := by
  have hl : (subcircuit PhiPairAdd.circuit X).localLength o = 1188 := rfl
  refine ⟨?_, ?_⟩
  · rw [FormalCircuit.subcircuit_structuralComputableWitnesses_iff]
    exact FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Bases) PhiPairAdd.circuit b X o (fun k e e' hk hag hb => hX k e e' hk hag hb)
      PhiPairAdd.computableWitnesses env env'
  · intro k e e' hk hag hb
    exact phiPairAdd_output_stable X (hX k e e' (by omega) hag hb) hag (by omega)

lemma sinv_negY {o : ℕ} (X : VP) (hX : Stab b o X) :
    SInvAt b env env' o (fun o' t => Stab b o' t) (subcircuit NegYAffine.circuit X) := by
  have hl : (subcircuit NegYAffine.circuit X).localLength o = 68 := rfl
  refine ⟨?_, ?_⟩
  · rw [FormalCircuit.subcircuit_structuralComputableWitnesses_iff]
    exact FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Bases) NegYAffine.circuit b X o (fun k e e' hk hag hb => hX k e e' hk hag hb)
      NegYAffine.computableWitnesses env env'
  · intro k e e' hk hag hb
    exact negY_output_stable X (hX k e e' (by omega) hag hb) hag (by omega)

lemma sinv_mux {o : ℕ} (X : Var (Mux.Inputs Emu) CF) (hX : Stab b o X) :
    SInvAt b env env' o (fun o' t => Stab b o' t) (subcircuit (Mux.circuit (M := Emu)) X) := by
  have hl : (subcircuit (Mux.circuit (M := Emu)) X).localLength o = 4 := rfl
  refine ⟨?_, ?_⟩
  · rw [FormalCircuit.subcircuit_structuralComputableWitnesses_iff]
    exact FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Bases) (Mux.circuit (M := Emu)) b X o (fun k e e' hk hag hb => hX k e e' hk hag hb)
      (Mux.computableWitnesses (M := Emu)) env env'
  · intro k e e' hk hag _
    exact muxEmu_output_stable X hag (by omega)

lemma sinv_negCanon {o : ℕ} (P : VP) (hP : Stab b o P) :
    SInvAt b env env' o (fun o' p => Stab b o' p.1 ∧ Stab b o' p.2) (negCanon P) := by
  unfold negCanon
  refine SInvAt.bind (sinv_mux _ (stab_muxInput hP (stab_x hP))) fun x hx => ?_
  refine SInvAt.bind (sinv_mux _ (stab_muxInput (hP.mono (by omega)) (stab_y (hP.mono (by omega)))))
    fun y hy => ?_
  refine SInvAt.bind (sinv_negY _ (stab_withXY (hP.mono (by omega)) (hx.mono (by omega)) hy))
    fun ny hny => ?_
  apply SInvAt.pure
  exact ⟨stab_withXY (hP.mono (by omega)) (hx.mono (by omega)) (hy.mono (by omega)),
    stab_withXY (hP.mono (by omega)) (hx.mono (by omega)) hny⟩

end SInv

theorem structuralComputableWitnesses (offset : ℕ) (b : Var Bases CF) (env env' : PE) :
    FormalCircuitBase.Operations.StructuralComputableWitnesses b env env' offset
      ((main b).operations offset) := by
  have hb : ∀ (o : ℕ) (i : Fin 4), Stab b o (Cost.baseEntryV b i) := fun o i =>
    stab_of_eq (b := b) fun e e' h => by
      obtain ⟨h0, h1, h2, h3⟩ := bases_parts b h
      fin_cases i <;> simp only [Cost.baseEntryV] <;> assumption
  suffices h : SInvAt b env env' offset (fun _ _ => True) (main b) from h.1
  unfold main
  refine SInvAt.bind (sinv_negY _ (hb _ 1)) fun nr1y hn1 => ?_
  refine SInvAt.bind (sinv_negY _ (hb _ 3)) fun nr3y hn3 => ?_
  refine SInvAt.bind (sinv_phiPairAdd _ (stab_pairPhi (hb _ 0) (hb _ 1))) fun up hup => ?_
  refine SInvAt.bind (sinv_phiPairAdd _ (stab_pairPhi (hb _ 0)
    (stab_withY (hb _ 1) (hn1.mono (by omega))))) fun um hum => ?_
  refine SInvAt.bind (sinv_phiPairAdd _ (stab_pairPhi (hb _ 2) (hb _ 3))) fun vp hvp => ?_
  refine SInvAt.bind (sinv_phiPairAdd _ (stab_pairPhi (hb _ 2)
    (stab_withY (hb _ 3) (hn3.mono (by omega))))) fun vm hvm => ?_
  refine SInvAt.bind (sinv_negCanon _ (hvp.mono (by omega))) fun vpp hvpp => ?_
  obtain ⟨hvp', hnvp⟩ := hvpp
  refine SInvAt.bind (sinv_negCanon _ (hvm.mono (by omega))) fun vmp hvmp => ?_
  obtain ⟨hvm', hnvm⟩ := hvmp
  refine SInvAt.bind (sinv_completeAdd _ (stab_pair (hup.mono (by omega)) (hvp'.mono (by omega))))
    fun e15 h15 => ?_
  refine SInvAt.bind (sinv_completeAdd _ (stab_pair (hup.mono (by omega)) (hvm'.mono (by omega))))
    fun e7 h7 => ?_
  refine SInvAt.bind (sinv_completeAdd _ (stab_pair (hup.mono (by omega)) (hnvm.mono (by omega))))
    fun e11 h11 => ?_
  refine SInvAt.bind (sinv_completeAdd _ (stab_pair (hup.mono (by omega)) (hnvp.mono (by omega))))
    fun e3 h3 => ?_
  refine SInvAt.bind (sinv_completeAdd _ (stab_pair (hum.mono (by omega)) (hvp'.mono (by omega))))
    fun e13 h13 => ?_
  refine SInvAt.bind (sinv_completeAdd _ (stab_pair (hum.mono (by omega)) (hvm'.mono (by omega))))
    fun e5 h5 => ?_
  refine SInvAt.bind (sinv_completeAdd _ (stab_pair (hum.mono (by omega)) (hnvm.mono (by omega))))
    fun e9 h9 => ?_
  refine SInvAt.bind (sinv_completeAdd _ (stab_pair (hum.mono (by omega)) (hnvp.mono (by omega))))
    fun e1 h1 => ?_
  refine SInvAt.bind (sinv_negCanon _ (h15.mono (by omega))) fun p0 _ => ?_
  refine SInvAt.bind (sinv_negCanon _ (h7.mono (by omega))) fun p8 _ => ?_
  refine SInvAt.bind (sinv_negCanon _ (h11.mono (by omega))) fun p4 _ => ?_
  refine SInvAt.bind (sinv_negCanon _ (h3.mono (by omega))) fun p12 _ => ?_
  refine SInvAt.bind (sinv_negCanon _ (h13.mono (by omega))) fun p2 _ => ?_
  refine SInvAt.bind (sinv_negCanon _ (h5.mono (by omega))) fun p10 _ => ?_
  refine SInvAt.bind (sinv_negCanon _ (h9.mono (by omega))) fun p6 _ => ?_
  refine SInvAt.bind (sinv_negCanon _ (h1.mono (by omega))) fun p14 _ => ?_
  exact SInvAt.pure trivial

theorem computableWitnesses : circuit.base.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (FormalCircuitBase.computableWitnessCondition input env env') ((main input).operations offset)
  exact FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
    input env env' (structuralComputableWitnesses offset input env env')

/-! ### Output stability -/

/-- Output invariants along a circuit whose local witnesses stay below `k`
(no unfolding of the circuit's output). -/
def EvInv {α : Type} (k : ℕ) (P : α → Prop) (c : Circuit CF α) : Prop :=
  ∀ n, n + c.localLength n ≤ k → P (c.output n)

lemma EvInv.bind {α β : Type} {k : ℕ} {P : α → Prop} {Q : β → Prop} {f : Circuit CF α}
    {g : α → Circuit CF β} (hf : EvInv k P f) (hg : ∀ a, P a → EvInv k Q (g a)) :
    EvInv k Q (f >>= g) := fun n hn => by
  rw [Circuit.bind_localLength_eq] at hn
  rw [Circuit.bind_output_eq]
  exact hg _ (hf n (by omega)) _ (by omega)

lemma EvInv.pure {α : Type} {k : ℕ} {P : α → Prop} {a : α} (h : P a) :
    EvInv k P (pure a : Circuit CF α) := fun n _ => by
  rw [Circuit.pure_output_eq]
  exact h

lemma EvInv.skip {α : Type} {k : ℕ} (c : Circuit CF α) : EvInv k (fun _ => True) c :=
  fun _ _ => trivial

lemma evInv_completeAdd (X : Var CompleteAdd.Inputs CF) {k : ℕ} {e e' : PE}
    (h_agree : e.AgreesBelow k e') :
    EvInv k (fun t => eval e t = eval e' t) (subcircuit CompleteAdd.circuit X) := fun n hn =>
  completeAdd_output_stable X h_agree (by
    have h : (subcircuit CompleteAdd.circuit X).localLength n = 1235 := rfl
    omega)

lemma evInv_negCanon (P : VP) {k : ℕ} {e e' : PE} (hP : eval e P = eval e' P)
    (h_agree : e.AgreesBelow k e') :
    EvInv k (fun p : VP × VP => eval e p.1 = eval e' p.1 ∧ eval e p.2 = eval e' p.2)
      (negCanon P) := by
  unfold negCanon
  refine EvInv.bind (P := fun x => eval e x = eval e' x) (fun n hn =>
    muxEmu_output_stable _ h_agree (by
      have h : (subcircuit (Mux.circuit (M := Emu))
        { selector := P.isInf, ifTrue := zeroConst, ifFalse := P.x }).localLength n = 4 := rfl
      omega)) fun x hx => ?_
  refine EvInv.bind (P := fun y => eval e y = eval e' y) (fun n hn =>
    muxEmu_output_stable _ h_agree (by
      have h : (subcircuit (Mux.circuit (M := Emu))
        { selector := P.isInf, ifTrue := zeroConst, ifFalse := P.y }).localLength n = 4 := rfl
      omega)) fun y hy => ?_
  have hc := withXY_stable P x y hP hx hy
  refine EvInv.bind (P := fun ny => eval e ny = eval e' ny) (fun n hn =>
    negY_output_stable _ hc h_agree (by
      have h : (subcircuit NegYAffine.circuit (withXY P x y)).localLength n = 68 := rfl
      omega)) fun ny hny => ?_
  exact EvInv.pure ⟨hc, withXY_stable P x ny hP hx hny⟩

theorem output_evInv (b : Var Bases CF) {k : ℕ} {e e' : PE} (h_agree : e.AgreesBelow k e') :
    EvInv k (fun t => ∀ i : Fin 16, eval e (Cost.rawEntryV t i) = eval e' (Cost.rawEntryV t i))
      (main b) := by
  unfold main
  refine EvInv.bind (EvInv.skip _) fun nr1y _ => ?_
  refine EvInv.bind (EvInv.skip _) fun nr3y _ => ?_
  refine EvInv.bind (EvInv.skip _) fun up _ => ?_
  refine EvInv.bind (EvInv.skip _) fun um _ => ?_
  refine EvInv.bind (EvInv.skip _) fun vp _ => ?_
  refine EvInv.bind (EvInv.skip _) fun vm _ => ?_
  refine EvInv.bind (EvInv.skip _) fun vpp _ => ?_
  refine EvInv.bind (EvInv.skip _) fun vmp _ => ?_
  refine EvInv.bind (evInv_completeAdd _ h_agree) fun e15 h15 => ?_
  refine EvInv.bind (evInv_completeAdd _ h_agree) fun e7 h7 => ?_
  refine EvInv.bind (evInv_completeAdd _ h_agree) fun e11 h11 => ?_
  refine EvInv.bind (evInv_completeAdd _ h_agree) fun e3 h3 => ?_
  refine EvInv.bind (evInv_completeAdd _ h_agree) fun e13 h13 => ?_
  refine EvInv.bind (evInv_completeAdd _ h_agree) fun e5 h5 => ?_
  refine EvInv.bind (evInv_completeAdd _ h_agree) fun e9 h9 => ?_
  refine EvInv.bind (evInv_completeAdd _ h_agree) fun e1 h1 => ?_
  refine EvInv.bind (evInv_negCanon _ h15 h_agree) fun p0 hp0 => ?_
  refine EvInv.bind (evInv_negCanon _ h7 h_agree) fun p8 hp8 => ?_
  refine EvInv.bind (evInv_negCanon _ h11 h_agree) fun p4 hp4 => ?_
  refine EvInv.bind (evInv_negCanon _ h3 h_agree) fun p12 hp12 => ?_
  refine EvInv.bind (evInv_negCanon _ h13 h_agree) fun p2 hp2 => ?_
  refine EvInv.bind (evInv_negCanon _ h5 h_agree) fun p10 hp10 => ?_
  refine EvInv.bind (evInv_negCanon _ h9 h_agree) fun p6 hp6 => ?_
  refine EvInv.bind (evInv_negCanon _ h1 h_agree) fun p14 hp14 => ?_
  apply EvInv.pure
  intro i
  fin_cases i <;> simp only [Cost.rawEntryV]
  · exact hp0.2
  · exact h1
  · exact hp2.2
  · exact h3
  · exact hp4.2
  · exact h5
  · exact hp6.2
  · exact h7
  · exact hp8.2
  · exact h9
  · exact hp10.2
  · exact h11
  · exact hp12.2
  · exact h13
  · exact hp14.2
  · exact h15

theorem output_stable (b : Var Bases CF) (n : ℕ) {k : ℕ} {e e' : PE}
    (h_agree : e.AgreesBelow k e') (hk : n + 15528 ≤ k) :
    ∀ i : Fin 16, eval e (Cost.rawEntryV ((main b).output n) i) = eval e' (Cost.rawEntryV ((main b).output n) i) := by
  have hlen : (main b).localLength n = 15528 := by
    rw [elaborated.localLength_eq]
    exact circuit_localLength b
  exact output_evInv b h_agree n (by omega)

theorem call_output_stable (b : Var Bases CF) (n : ℕ) {k : ℕ} {e e' : PE}
    (h_agree : e.AgreesBelow k e') (hk : n + 15528 ≤ k) :
    ∀ i : Fin 16, eval e (Cost.rawEntryV ((subcircuit circuit b).output n) i) =
      eval e' (Cost.rawEntryV ((subcircuit circuit b).output n) i) := by
  rw [show (subcircuit circuit b).output n = (main b).output n from (elaborated.output_eq b n).symm]
  exact output_stable b n h_agree hk

end Solution.Secp256k1ScalarMul.PatTable
end
