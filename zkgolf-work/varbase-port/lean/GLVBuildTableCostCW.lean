import Solution.Secp256k1ScalarMul.GLVBuildTable
import Solution.Secp256k1ScalarMul.Cost
import Solution.Secp256k1ScalarMul.MulModBeta32Cost
import Solution.Secp256k1ScalarMul.NegYAffineSubCost
import Solution.Secp256k1ScalarMul.NegYAffineCW
import Challenge.Utils.ComputableWitnessLemmas

namespace Solution.Secp256k1ScalarMul

local notation "CF" => F circomPrime
local notation "PE" => ProverEnvironment CF
local notation "VI" => Var GLVBuildTable.Inputs CF
local notation "VP" => Var FlaggedPoint CF
open Challenge.Utils.ComputableWitnessLemmas

namespace Cost

open Challenge.CostR1CS

attribute [local irreducible] isR1CSRow r1csProducts operationsIsR1CS flatOperationsIsR1CS

def glvPrepareCost : Count := ⟨830, 838⟩
private def glvSubsetCost : Count := ⟨13495, 13592⟩

def glvBuildTableCost : Count := ⟨14325, 14430⟩

theorem costIs_glvPrepare
    (input : VI) :
    CostIs (GLVBuildTable.Prepare.main input) glvPrepareCost := by
  rw [show glvPrepareCost =
      mulModBeta32Cost +
      (mulModBeta32Cost +
      (NegYAffine.CostCert.cost + (NegYAffine.CostCert.cost +
      (⟨4, 4⟩ + (⟨4, 4⟩ + (⟨4, 4⟩ + Count.zero))))))
    from by decide]
  unfold GLVBuildTable.Prepare.main
  refine CostIs.bind (costIs_sub_mulModBeta32 _) fun _ => ?_
  refine CostIs.bind (costIs_sub_mulModBeta32 _) fun _ => ?_
  refine CostIs.bind (NegYAffine.CostCert.costIs_sub _) fun _ => ?_
  refine CostIs.bind (NegYAffine.CostCert.costIs_sub _) fun _ => ?_
  refine CostIs.bind (costIs_sub_mux _) fun _ => ?_
  refine CostIs.bind (costIs_sub_mux _) fun _ => ?_
  refine CostIs.bind (costIs_sub_mux _) fun _ => ?_
  exact CostIs.pure _

theorem costIs_sub_glvPrepare
    (input : VI) :
    CostIs (subcircuit GLVBuildTable.Prepare.circuit input) glvPrepareCost :=
  CostIs.subcircuit fun n => costIs_glvPrepare input n

set_option maxHeartbeats 4000000 in
private theorem costIs_glvSubset
    (input : Var GLVBuildTable.Bases (CF)) :
    CostIs (GLVBuildTable.Subset.main input) glvSubsetCost := by
  rw [show glvSubsetCost =
      phiPairAddCost + (phiPairAddCost + (⟨4, 4⟩ +
        (completeAddCost + (completeAddCost + (completeAddCost +
        (completeAddCost + (completeAddCost + (completeAddCost +
        (completeAddCost + (completeAddCost + (completeAddCost +
        Count.zero)))))))))))
    from by decide]
  unfold GLVBuildTable.Subset.main
  refine CostIs.bind (costIs_sub_phiPairAdd _) fun _ => ?_
  refine CostIs.bind (costIs_sub_phiPairAdd _) fun _ => ?_
  refine CostIs.bind (costIs_sub_mux _) fun _ => ?_
  refine CostIs.bind (costIs_sub_completeAdd _) fun _ => ?_
  refine CostIs.bind (costIs_sub_completeAdd _) fun _ => ?_
  refine CostIs.bind (costIs_sub_completeAdd _) fun _ => ?_
  refine CostIs.bind (costIs_sub_completeAdd _) fun _ => ?_
  refine CostIs.bind (costIs_sub_completeAdd _) fun _ => ?_
  refine CostIs.bind (costIs_sub_completeAdd _) fun _ => ?_
  refine CostIs.bind (costIs_sub_completeAdd _) fun _ => ?_
  refine CostIs.bind (costIs_sub_completeAdd _) fun _ => ?_
  refine CostIs.bind (costIs_sub_completeAdd _) fun _ => ?_
  exact CostIs.pure _

private theorem costIs_sub_glvSubset
    (input : Var GLVBuildTable.Bases (CF)) :
    CostIs (subcircuit GLVBuildTable.Subset.circuit input) glvSubsetCost :=
  CostIs.subcircuit fun n => costIs_glvSubset input n

theorem costIs_glvBuildTable
    (input : VI) :
    CostIs (GLVBuildTable.main input) glvBuildTableCost := by
  rw [show glvBuildTableCost = glvPrepareCost + (glvSubsetCost + Count.zero)
    from by decide]
  unfold GLVBuildTable.main
  refine CostIs.bind (costIs_sub_glvPrepare _) fun _ => ?_
  refine CostIs.bind (costIs_sub_glvSubset _) fun _ => ?_
  exact CostIs.pure _

theorem costIs_sub_glvBuildTable
    (input : VI) :
    CostIs (subcircuit GLVBuildTable.circuit input) glvBuildTableCost :=
  CostIs.subcircuit fun n => costIs_glvBuildTable input n

private theorem isR1CS_glvPrepare
    (input : VI)
    (hP : AffineFP input.P) (hQ : AffineFP input.Q)
    (_hs0 : Affine input.sign0) (hs1 : Affine input.sign1)
    (hs2 : Affine input.sign2) (hs3 : Affine input.sign3) :
    IsR1CSCirc (GLVBuildTable.Prepare.main input) := by
  unfold GLVBuildTable.Prepare.main
  refine IsR1CSCirc.bind_out
    (isR1CS_sub_mulModBeta32 _ hP.1)
    fun npx => ?_
  refine IsR1CSCirc.bind_out
    (isR1CS_sub_mulModBeta32 _ hQ.1)
    fun nqx => ?_
  refine IsR1CSCirc.bind_out
    (NegYAffine.CostCert.isR1CS_sub input.P hP) fun npy => ?_
  refine IsR1CSCirc.bind_out
    (NegYAffine.CostCert.isR1CS_sub input.Q hQ) fun nqy => ?_
  have hphiP : AffineFP
      ({ x := (subcircuit MulModBeta32.circuit { a := input.P.x }).output npx,
         y := input.P.y, isInf := input.P.isInf } :
        VP) :=
    ⟨affineW_sub_mulModBeta32 _ _, hP.2.1, hP.2.2⟩
  have hphiQ : AffineFP
      ({ x := (subcircuit MulModBeta32.circuit { a := input.Q.x }).output nqx,
         y := input.Q.y, isInf := input.Q.isInf } :
        VP) :=
    ⟨affineW_sub_mulModBeta32 _ _, hQ.2.1, hQ.2.2⟩
  have hnP : AffineFP
      ({ x := input.P.x,
         y := (subcircuit NegYAffine.circuit input.P).output npy,
         isInf := input.P.isInf } : VP) :=
    ⟨hP.1, NegYAffine.CostCert.affineW_sub input.P _ hP, hP.2.2⟩
  have hnQ : AffineFP
      ({ x := input.Q.x,
         y := (subcircuit NegYAffine.circuit input.Q).output nqy,
         isInf := input.Q.isInf } : VP) :=
    ⟨hQ.1, NegYAffine.CostCert.affineW_sub input.Q _ hQ, hQ.2.2⟩
  have hnphiP : AffineFP
      ({ x := (subcircuit MulModBeta32.circuit { a := input.P.x }).output npx,
         y := (subcircuit NegYAffine.circuit input.P).output npy,
         isInf := input.P.isInf } : VP) :=
    ⟨affineW_sub_mulModBeta32 _ _, NegYAffine.CostCert.affineW_sub input.P _ hP,
      hP.2.2⟩
  have hnphiQ : AffineFP
      ({ x := (subcircuit MulModBeta32.circuit { a := input.Q.x }).output nqx,
         y := (subcircuit NegYAffine.circuit input.Q).output nqy,
         isInf := input.Q.isInf } : VP) :=
    ⟨affineW_sub_mulModBeta32 _ _, NegYAffine.CostCert.affineW_sub input.Q _ hQ,
      hQ.2.2⟩
  refine IsR1CSCirc.bind_out
    (isR1CS_sub_mux _ hs1 (NegYAffine.CostCert.affineW_sub input.P npy hP).affineProvable
      hP.2.1.affineProvable) fun _ => ?_
  refine IsR1CSCirc.bind_out
    (isR1CS_sub_mux _ hs2 (NegYAffine.CostCert.affineW_sub input.Q nqy hQ).affineProvable
      hQ.2.1.affineProvable) fun _ => ?_
  refine IsR1CSCirc.bind_out
    (isR1CS_sub_mux _ hs3 (NegYAffine.CostCert.affineW_sub input.Q nqy hQ).affineProvable
      hQ.2.1.affineProvable) fun _ => ?_
  exact IsR1CSCirc.pure _

theorem isR1CS_sub_glvPrepare
    (input : VI)
    (hP : AffineFP input.P) (hQ : AffineFP input.Q)
    (hs0 : Affine input.sign0) (hs1 : Affine input.sign1)
    (hs2 : Affine input.sign2) (hs3 : Affine input.sign3) :
    IsR1CSCirc (subcircuit GLVBuildTable.Prepare.circuit input) :=
  IsR1CSCirc.subcircuit fun n =>
    isR1CS_glvPrepare input hP hQ hs0 hs1 hs2 hs3 n

def baseEntryV (b : Var GLVBuildTable.Bases (CF)) :
    Fin 4 → VP
  | ⟨0, _⟩ => b.r0
  | ⟨1, _⟩ => b.r1
  | ⟨2, _⟩ => b.r2
  | ⟨3, _⟩ => b.r3

def rawEntryV (t : Var GLVBuildTable.RawTable (CF)) :
    Fin 16 → VP
  | ⟨0, _⟩ => t.t0 | ⟨1, _⟩ => t.t1 | ⟨2, _⟩ => t.t2 | ⟨3, _⟩ => t.t3
  | ⟨4, _⟩ => t.t4 | ⟨5, _⟩ => t.t5 | ⟨6, _⟩ => t.t6 | ⟨7, _⟩ => t.t7
  | ⟨8, _⟩ => t.t8 | ⟨9, _⟩ => t.t9 | ⟨10, _⟩ => t.t10 | ⟨11, _⟩ => t.t11
  | ⟨12, _⟩ => t.t12 | ⟨13, _⟩ => t.t13 | ⟨14, _⟩ => t.t14 | _ => t.t15

lemma affineTable_pack
    (raw : Var GLVBuildTable.RawTable (CF))
    (hr : ∀ i : Fin 16, AffineFP (rawEntryV raw i)) :
    AffineTableV (GLVBuildTable.Pack.pack raw).tx
      (GLVBuildTable.Pack.pack raw).ty (GLVBuildTable.Pack.pack raw).tinf := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    have h := (hr ⟨i, hi⟩).1
    interval_cases i <;>
      simpa only [GLVBuildTable.Pack.pack, rawEntryV, Vector.getElem_ofFn] using h
  · intro i hi
    have h := (hr ⟨i, hi⟩).2.1
    interval_cases i <;>
      simpa only [GLVBuildTable.Pack.pack, rawEntryV, Vector.getElem_ofFn] using h
  · intro i hi
    have h := (hr ⟨i, hi⟩).2.2
    interval_cases i <;>
      simpa only [GLVBuildTable.Pack.pack, rawEntryV, Vector.getElem_ofFn] using h

private lemma affineFP_withX
    {P : VP} {x : Var Emu (CF)}
    (hx : AffineW x) (hP : AffineFP P) :
    AffineFP ({ x := x, y := P.y, isInf := P.isInf } : VP) :=
  ⟨hx, hP.2.1, hP.2.2⟩

set_option maxRecDepth 8192 in
theorem affineBases_sub_glvPrepare
    (input : VI) (n : ℕ) (hP : AffineFP input.P) (hQ : AffineFP input.Q) :
    ∀ i : Fin 4, AffineFP (baseEntryV
      ((subcircuit GLVBuildTable.Prepare.circuit input).output n) i) := by
  intro i
  fin_cases i <;> simp only [circuit_norm, subcircuit,
    GLVBuildTable.Prepare.circuit, GLVBuildTable.Prepare.elaborated, baseEntryV]
  · exact ⟨hP.1, hP.2.1, hP.2.2⟩
  · exact ⟨affineW_mapRange_var _, affineW_mapRange_var _, hP.2.2⟩
  · exact ⟨hQ.1, affineW_mapRange_var _, hQ.2.2⟩
  · exact ⟨affineW_mapRange_var _, affineW_mapRange_var _, hQ.2.2⟩

private def glvSubsetCanonMuxes
    (input : Var GLVBuildTable.Bases (CF))
    (t3 t12 t5 t9 t6 t10 t7 t11 t13 t14 t15 : VP) :
    Circuit (CF) (Var GLVBuildTable.RawTable (CF)) := do
  let t5x ← subcircuit (Mux.circuit (M := Emu))
    { selector := t5.isInf, ifTrue := zeroConst, ifFalse := t5.x }
  let t6x ← subcircuit (Mux.circuit (M := Emu))
    { selector := t6.isInf, ifTrue := zeroConst, ifFalse := t6.x }
  let t7x ← subcircuit (Mux.circuit (M := Emu))
    { selector := t7.isInf, ifTrue := zeroConst, ifFalse := t7.x }
  let t9x ← subcircuit (Mux.circuit (M := Emu))
    { selector := t9.isInf, ifTrue := zeroConst, ifFalse := t9.x }
  let t10x ← subcircuit (Mux.circuit (M := Emu))
    { selector := t10.isInf, ifTrue := zeroConst, ifFalse := t10.x }
  let t11x ← subcircuit (Mux.circuit (M := Emu))
    { selector := t11.isInf, ifTrue := zeroConst, ifFalse := t11.x }
  let t13x ← subcircuit (Mux.circuit (M := Emu))
    { selector := t13.isInf, ifTrue := zeroConst, ifFalse := t13.x }
  let t14x ← subcircuit (Mux.circuit (M := Emu))
    { selector := t14.isInf, ifTrue := zeroConst, ifFalse := t14.x }
  let t15x ← subcircuit (Mux.circuit (M := Emu))
    { selector := t15.isInf, ifTrue := zeroConst, ifFalse := t15.x }
  let t5 : VP := { x := t5x, y := t5.y, isInf := t5.isInf }
  let t6 : VP := { x := t6x, y := t6.y, isInf := t6.isInf }
  let t7 : VP := { x := t7x, y := t7.y, isInf := t7.isInf }
  let t9 : VP := { x := t9x, y := t9.y, isInf := t9.isInf }
  let t10 : VP := { x := t10x, y := t10.y, isInf := t10.isInf }
  let t11 : VP := { x := t11x, y := t11.y, isInf := t11.isInf }
  let t13 : VP := { x := t13x, y := t13.y, isInf := t13.isInf }
  let t14 : VP := { x := t14x, y := t14.y, isInf := t14.isInf }
  let t15 : VP := { x := t15x, y := t15.y, isInf := t15.isInf }
  return GLVBuildTable.RawTable.mk infConst input.r0 input.r1 t3 input.r2 t5 t6 t7
    input.r3 t9 t10 t11 t12 t13 t14 t15

private theorem isR1CS_glvSubsetCanonMuxes
    (input : Var GLVBuildTable.Bases (CF))
    (t3 t12 t5 t9 t6 t10 t7 t11 t13 t14 t15 : VP)
    (ht5 : AffineFP t5) (ht6 : AffineFP t6)
    (ht7 : AffineFP t7) (ht9 : AffineFP t9) (ht10 : AffineFP t10)
    (ht11 : AffineFP t11) (ht13 : AffineFP t13) (ht14 : AffineFP t14)
    (ht15 : AffineFP t15) :
    IsR1CSCirc
      (glvSubsetCanonMuxes input t3 t12 t5 t9 t6 t10 t7 t11 t13 t14 t15) := by
  have hz : AffineProvable (zeroConst : Var Emu (CF)) := by
    simpa only [zeroConst] using (affineW_emuConst 0).affineProvable
  unfold glvSubsetCanonMuxes
  refine IsR1CSCirc.bind
    (isR1CS_sub_mux _ ht5.2.2 hz ht5.1.affineProvable) fun _ => ?_
  refine IsR1CSCirc.bind
    (isR1CS_sub_mux _ ht6.2.2 hz ht6.1.affineProvable) fun _ => ?_
  refine IsR1CSCirc.bind
    (isR1CS_sub_mux _ ht7.2.2 hz ht7.1.affineProvable) fun _ => ?_
  refine IsR1CSCirc.bind
    (isR1CS_sub_mux _ ht9.2.2 hz ht9.1.affineProvable) fun _ => ?_
  refine IsR1CSCirc.bind
    (isR1CS_sub_mux _ ht10.2.2 hz ht10.1.affineProvable) fun _ => ?_
  refine IsR1CSCirc.bind
    (isR1CS_sub_mux _ ht11.2.2 hz ht11.1.affineProvable) fun _ => ?_
  refine IsR1CSCirc.bind
    (isR1CS_sub_mux _ ht13.2.2 hz ht13.1.affineProvable) fun _ => ?_
  refine IsR1CSCirc.bind
    (isR1CS_sub_mux _ ht14.2.2 hz ht14.1.affineProvable) fun _ => ?_
  refine IsR1CSCirc.bind
    (isR1CS_sub_mux _ ht15.2.2 hz ht15.1.affineProvable) fun _ => ?_
  exact IsR1CSCirc.pure _

set_option maxHeartbeats 8000000 in
private theorem isR1CS_glvSubset
    (input : Var GLVBuildTable.Bases (CF))
    (hbase : ∀ i : Fin 4, AffineFP (baseEntryV input i)) :
    IsR1CSCirc (GLVBuildTable.Subset.main input) := by
  unfold GLVBuildTable.Subset.main
  have h0 := hbase 0; have h1 := hbase 1
  have h2 := hbase 2; have h3 := hbase 3
  refine IsR1CSCirc.bind_out (isR1CS_sub_phiPairAdd _ h0 h1) fun n3 => ?_
  let t3 : VP :=
    (subcircuit PhiPairAdd.circuit { P := input.r0, Q := input.r1 }).output n3
  have ht3 : AffineFP t3 := affineFP_sub_phiPairAdd _ n3 h0
  refine IsR1CSCirc.bind_out (isR1CS_sub_phiPairAdd _ h2 h3) fun n12 => ?_
  let t12r : VP :=
    (subcircuit PhiPairAdd.circuit { P := input.r2, Q := input.r3 }).output n12
  have ht12r : AffineFP t12r := affineFP_sub_phiPairAdd _ n12 h2
  have hz0 : AffineProvable (zeroConst : Var Emu (CF)) := by
    simpa only [zeroConst] using (affineW_emuConst 0).affineProvable
  refine IsR1CSCirc.bind_out
    (isR1CS_sub_mux _ ht12r.2.2 hz0 ht12r.1.affineProvable) fun n12x => ?_
  let t12x : Var Emu (CF) :=
    (subcircuit (Mux.circuit (M := Emu))
      { selector := t12r.isInf, ifTrue := zeroConst, ifFalse := t12r.x }).output n12x
  let t12 : VP := { x := t12x, y := t12r.y, isInf := t12r.isInf }
  have ht12 : AffineFP t12 :=
    affineFP_withX (affineProvable_sub_mux _ n12x).affineW ht12r
  refine IsR1CSCirc.bind_out (isR1CS_sub_completeAdd _ h0 h2) fun n5 => ?_
  let t5 : VP :=
    (subcircuit CompleteAdd.circuit { P := input.r0, Q := input.r2 }).output n5
  have ht5 : AffineFP t5 := affineFP_sub_completeAdd _ n5
  refine IsR1CSCirc.bind_out (isR1CS_sub_completeAdd _ h0 h3) fun n9 => ?_
  let t9 : VP :=
    (subcircuit CompleteAdd.circuit { P := input.r0, Q := input.r3 }).output n9
  have ht9 : AffineFP t9 := affineFP_sub_completeAdd _ n9
  refine IsR1CSCirc.bind_out (isR1CS_sub_completeAdd _ h1 h2) fun n6 => ?_
  let t6 : VP :=
    (subcircuit CompleteAdd.circuit { P := input.r1, Q := input.r2 }).output n6
  have ht6 : AffineFP t6 := affineFP_sub_completeAdd _ n6
  refine IsR1CSCirc.bind_out (isR1CS_sub_completeAdd _ h1 h3) fun n10 => ?_
  let t10 : VP :=
    (subcircuit CompleteAdd.circuit { P := input.r1, Q := input.r3 }).output n10
  have ht10 : AffineFP t10 := affineFP_sub_completeAdd _ n10
  refine IsR1CSCirc.bind_out
    (isR1CS_sub_completeAdd _ ht3 h2) fun n7 => ?_
  let t7 : VP :=
    (subcircuit CompleteAdd.circuit { P := t3, Q := input.r2 }).output n7
  have ht7 : AffineFP t7 := affineFP_sub_completeAdd _ n7
  refine IsR1CSCirc.bind_out
    (isR1CS_sub_completeAdd _ ht3 h3) fun n11 => ?_
  let t11 : VP :=
    (subcircuit CompleteAdd.circuit { P := t3, Q := input.r3 }).output n11
  have ht11 : AffineFP t11 := affineFP_sub_completeAdd _ n11
  refine IsR1CSCirc.bind_out
    (isR1CS_sub_completeAdd _ h0 ht12) fun n13 => ?_
  let t13 : VP :=
    (subcircuit CompleteAdd.circuit { P := input.r0, Q := t12 }).output n13
  have ht13 : AffineFP t13 := affineFP_sub_completeAdd _ n13
  refine IsR1CSCirc.bind_out
    (isR1CS_sub_completeAdd _ h1 ht12) fun n14 => ?_
  let t14 : VP :=
    (subcircuit CompleteAdd.circuit { P := input.r1, Q := t12 }).output n14
  have ht14 : AffineFP t14 := affineFP_sub_completeAdd _ n14
  refine IsR1CSCirc.bind_out
    (isR1CS_sub_completeAdd _ ht3 ht12) fun n15 => ?_
  let t15 : VP :=
    (subcircuit CompleteAdd.circuit { P := t3, Q := t12 }).output n15
  have ht15 : AffineFP t15 := affineFP_sub_completeAdd _ n15
  exact IsR1CSCirc.pure _

private theorem isR1CS_sub_glvSubset
    (input : Var GLVBuildTable.Bases (CF))
    (hbase : ∀ i : Fin 4, AffineFP (baseEntryV input i)) :
    IsR1CSCirc (subcircuit GLVBuildTable.Subset.circuit input) :=
  IsR1CSCirc.subcircuit fun n => isR1CS_glvSubset input hbase n

theorem isR1CS_glvBuildTable
    (input : VI)
    (hP : AffineFP input.P) (hQ : AffineFP input.Q)
    (hs0 : Affine input.sign0) (hs1 : Affine input.sign1)
    (hs2 : Affine input.sign2) (hs3 : Affine input.sign3) :
    IsR1CSCirc (GLVBuildTable.main input) := by
  unfold GLVBuildTable.main
  refine IsR1CSCirc.bind_out
    (isR1CS_sub_glvPrepare input hP hQ hs0 hs1 hs2 hs3) fun nb => ?_
  refine IsR1CSCirc.bind_out
    (isR1CS_sub_glvSubset _ (affineBases_sub_glvPrepare input nb hP hQ)) fun _ => ?_
  exact IsR1CSCirc.pure _

theorem isR1CS_sub_glvBuildTable
    (input : VI)
    (hP : AffineFP input.P) (hQ : AffineFP input.Q)
    (hs0 : Affine input.sign0) (hs1 : Affine input.sign1)
    (hs2 : Affine input.sign2) (hs3 : Affine input.sign3) :
    IsR1CSCirc (subcircuit GLVBuildTable.circuit input) :=
  IsR1CSCirc.subcircuit fun n =>
    isR1CS_glvBuildTable input hP hQ hs0 hs1 hs2 hs3 n

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
theorem affineTable_sub_glvBuildTable
    (input : VI) (n : ℕ) (hP : AffineFP input.P) (hQ : AffineFP input.Q) :
    AffineTableV
      ((subcircuit GLVBuildTable.circuit input).output n).tx
      ((subcircuit GLVBuildTable.circuit input).output n).ty
      ((subcircuit GLVBuildTable.circuit input).output n).tinf := by
  have hb := affineBases_sub_glvPrepare input n hP hQ
  have hb0 := hb 0; have hb1 := hb 1
  have hb2 := hb 2; have hb3 := hb 3
  simp only [baseEntryV, circuit_norm] at hb0 hb1 hb2 hb3
  let dummy : Var CompleteAdd.Inputs (CF) :=
    { P := infConst, Q := infConst }
  let phiInput : Var PhiPairAdd.Inputs (CF) :=
    { P := (GLVBuildTable.basesAt input n).r0,
      Q := (GLVBuildTable.basesAt input n).r1 }
  let phiQInput : Var PhiPairAdd.Inputs (CF) :=
    { P := (GLVBuildTable.basesAt input n).r2,
      Q := (GLVBuildTable.basesAt input n).r3 }
  have hr : ∀ i : Fin 16,
      AffineFP (rawEntryV (GLVBuildTable.rawAt input n) i) := by
    intro i
    fin_cases i
    · exact affineFP_infConst
    · exact hb0
    · exact hb1
    · exact affineFP_sub_phiPairAdd phiInput _ hb0
    · exact hb2
    · exact affineFP_sub_completeAdd dummy _
    · exact affineFP_sub_completeAdd dummy _
    · exact affineFP_sub_completeAdd dummy _
    · exact hb3
    · exact affineFP_sub_completeAdd dummy _
    · exact affineFP_sub_completeAdd dummy _
    · exact affineFP_sub_completeAdd dummy _
    · exact affineFP_withX (affineW_varFromOffset _ _)
        (affineFP_sub_phiPairAdd phiQInput _ hb2)
    · exact affineFP_sub_completeAdd dummy _
    · exact affineFP_sub_completeAdd dummy _
    · exact affineFP_sub_completeAdd dummy _
  simpa only [subcircuit, GLVBuildTable.circuit, GLVBuildTable.elaborated,
    GLVBuildTable.tableAt] using
    affineTable_pack (GLVBuildTable.rawAt input n) hr

end Cost

namespace GLVBuildTable

private lemma eval_varFromOffset_of_agreesBelow
    {A : TypeMap} [ProvableType A] {off k : ℕ}
    {env env' : PE}
    (h_agree : env.AgreesBelow k env') (hk : off + size A ≤ k) :
    eval env (varFromOffset A off : Var A (CF)) =
      eval env' (varFromOffset A off : Var A (CF)) := by
  rw [CircuitType.eval_expression_prover_to_verifier (M := A),
    CircuitType.eval_expression_prover_to_verifier (M := A), ProvableType.ext_iff]
  intro i hi
  rw [← ProvableType.getElem_eval_toElements
      (varFromOffset A off : Var A (CF)) i hi,
    ← ProvableType.getElem_eval_toElements
      (varFromOffset A off : Var A (CF)) i hi]
  simp only [varFromOffset, ProvableType.toElements_fromElements,
    Vector.getElem_mapRange, Expression.eval]
  exact h_agree (off + i) (by omega)

private lemma cond_completeAdd {e e' : PE}
    (P Q : VP)
    (hP : eval e P = eval e' P) (hQ : eval e Q = eval e' Q) :
    eval e ({ P := P, Q := Q } : Var CompleteAdd.Inputs (CF)) =
      eval e' ({ P := P, Q := Q } : Var CompleteAdd.Inputs (CF)) := by
  simp only [circuit_norm] at hP hQ ⊢
  rw [CompleteAdd.Inputs.mk.injEq]
  exact ⟨hP, hQ⟩

private lemma cond_phiPairAdd {e e' : PE}
    (P Q : VP)
    (hP : eval e P = eval e' P) (hQ : eval e Q = eval e' Q) :
    eval e ({ P := P, Q := Q } : Var PhiPairAdd.Inputs (CF)) =
      eval e' ({ P := P, Q := Q } : Var PhiPairAdd.Inputs (CF)) := by
  simp only [circuit_norm] at hP hQ ⊢
  rw [PhiPairAdd.Inputs.mk.injEq]
  exact ⟨hP, hQ⟩

private lemma point_x_stable {e e' : PE}
    (P : VP) (hP : eval e P = eval e' P) :
    eval e P.x = eval e' P.x := by
  simp only [circuit_norm, FlaggedPoint.mk.injEq] at hP
  simpa only [circuit_norm] using hP.1

private lemma point_isInf_stable {e e' : PE}
    (P : VP) (hP : eval e P = eval e' P) :
    Expression.eval e.toEnvironment P.isInf =
      Expression.eval e'.toEnvironment P.isInf := by
  simp only [circuit_norm, FlaggedPoint.mk.injEq] at hP
  simpa only [circuit_norm] using hP.2.2

private lemma zeroConst_emu_stable {e e' : PE} :
    eval e (zeroConst : Var Emu (CF)) =
      eval e' (zeroConst : Var Emu (CF)) := by
  rw [CircuitType.eval_var_fields_prover, CircuitType.eval_var_fields_prover]
  rw [DivOrZero.eval_zeroConst, DivOrZero.eval_zeroConst]

private lemma cond_muxEmu {e e' : PE}
    (s : Expression (CF)) (t f : Var Emu (CF))
    (hs : Expression.eval e.toEnvironment s =
      Expression.eval e'.toEnvironment s)
    (ht : eval e t = eval e' t) (hf : eval e f = eval e' f) :
    eval e ({ selector := s, ifTrue := t, ifFalse := f } :
      Var (Mux.Inputs Emu) (CF)) =
    eval e' ({ selector := s, ifTrue := t, ifFalse := f } :
      Var (Mux.Inputs Emu) (CF)) := by
  simp only [circuit_norm]
  rw [Mux.Inputs.mk.injEq]
  exact ⟨hs, by simpa only [circuit_norm] using ht,
    by simpa only [circuit_norm] using hf⟩

namespace Prepare

private lemma negY_output_stable
    (X : VP) {off k : ℕ}
    {e e' : PE}
    (hX : eval e X = eval e' X)
    (h_agree : e.AgreesBelow k e') (hk : off + 68 ≤ k) :
    eval e ((subcircuit NegYAffine.circuit X).output off) =
      eval e' ((subcircuit NegYAffine.circuit X).output off) := by
  simpa only [circuit_norm, subcircuit, NegYAffine.circuit,
    NegYAffine.elaborated] using
    (NegYAffine.eval_output_of_agreesBelow X hX h_agree (by omega))

set_option maxHeartbeats 4000000 in
private theorem structuralComputableWitnesses
    (offset : ℕ) (input : VI)
    (env env' : PE) :
    FormalCircuitBase.Operations.StructuralComputableWitnesses
      input env env' offset ((main input).operations offset) := by
  obtain ⟨P, Q, s0, s1, s2, s3⟩ := input
  have hmm : ∀ (X : Var MulModBeta32.Inputs (CF)) (o : ℕ),
      (subcircuit MulModBeta32.circuit X).localLength o = 341 := fun _ _ => rfl
  have hneg : ∀ (X : VP) (o : ℕ),
      (subcircuit NegYAffine.circuit X).localLength o = 68 := fun _ _ => rfl
  have hmux : ∀ (X : Var (Mux.Inputs Emu) (CF)) (o : ℕ),
      (subcircuit (Mux.circuit (M := Emu)) X).localLength o = 4 :=
    fun _ _ => rfl
  unfold main
  simp only [
    Circuit.bind_structuralComputableWitnesses_iff,
    FormalCircuit.subcircuit_structuralComputableWitnesses_iff,
    Circuit.pure_structuralComputableWitnesses_iff,
    hmm, hneg, hmux, and_true]
  have parts : ∀ {e e' : PE},
      eval e (⟨P, Q, s0, s1, s2, s3⟩ : VI) =
        eval e' (⟨P, Q, s0, s1, s2, s3⟩ : VI) →
      (eval e P = eval e' P) ∧ (eval e Q = eval e' Q) ∧
      Expression.eval e.toEnvironment s0 = Expression.eval e'.toEnvironment s0 ∧
      Expression.eval e.toEnvironment s1 = Expression.eval e'.toEnvironment s1 ∧
      Expression.eval e.toEnvironment s2 = Expression.eval e'.toEnvironment s2 ∧
      Expression.eval e.toEnvironment s3 = Expression.eval e'.toEnvironment s3 := by
    intro e e' h
    simpa only [circuit_norm, Inputs.mk.injEq] using h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) MulModBeta32.circuit _ _ _ ?_
      MulModBeta32.computableWitnesses env env'
    intro k e e' _ _ h_in
    have hp := (parts h_in).1
    simp only [circuit_norm, FlaggedPoint.mk.injEq] at hp ⊢
    rw [MulModBeta32.Inputs.mk.injEq]
    exact hp.1
  · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) MulModBeta32.circuit _ _ _ ?_
      MulModBeta32.computableWitnesses env env'
    intro k e e' _ _ h_in
    have hq := (parts h_in).2.1
    simp only [circuit_norm, FlaggedPoint.mk.injEq] at hq ⊢
    rw [MulModBeta32.Inputs.mk.injEq]
    exact hq.1
  · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) NegYAffine.circuit _ _ _ ?_
      NegYAffine.computableWitnesses env env'
    intro k e e' _ _ h_in
    have hp := (parts h_in).1
    exact (parts h_in).1
  · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) NegYAffine.circuit _ _ _ ?_
      NegYAffine.computableWitnesses env env'
    intro k e e' _ _ h_in
    have hq := (parts h_in).2.1
    exact (parts h_in).2.1
  all_goals
    refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) (Mux.circuit (M := Emu)) _ _ _ ?_
      (Mux.computableWitnesses (M := Emu)) env env'
  · intro k e e' hle h_agree h_in
    obtain ⟨hp, hq, hs0, hs1, hs2, hs3⟩ := parts h_in
    have hp_eq : eval e P = eval e' P := hp
    simp only [circuit_norm, FlaggedPoint.mk.injEq] at hp hq ⊢
    rw [Mux.Inputs.mk.injEq]
    exact ⟨hs1, emu_map_eval_eq_of_eval_eq
      (negY_output_stable _ hp_eq h_agree (by omega)), hp.2.1⟩
  · intro k e e' hle h_agree h_in
    obtain ⟨hp, hq, hs0, hs1, hs2, hs3⟩ := parts h_in
    have hq_eq : eval e Q = eval e' Q := hq
    simp only [circuit_norm, FlaggedPoint.mk.injEq] at hp hq ⊢
    rw [Mux.Inputs.mk.injEq]
    exact ⟨hs2, emu_map_eval_eq_of_eval_eq
      (negY_output_stable _ hq_eq h_agree (by omega)), hq.2.1⟩
  · intro k e e' hle h_agree h_in
    obtain ⟨hp, hq, hs0, hs1, hs2, hs3⟩ := parts h_in
    have hq_eq : eval e Q = eval e' Q := hq
    simp only [circuit_norm, FlaggedPoint.mk.injEq] at hp hq ⊢
    rw [Mux.Inputs.mk.injEq]
    exact ⟨hs3, emu_map_eval_eq_of_eval_eq
      (negY_output_stable _ hq_eq h_agree (by omega)), hq.2.1⟩

theorem computableWitnesses : circuit.base.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (FormalCircuitBase.computableWitnessCondition
      input env env') ((main input).operations offset)
  exact FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
    input env env' (structuralComputableWitnesses offset input env env')

end Prepare

namespace Subset

private lemma completeAdd_output_stable
    (X : Var CompleteAdd.Inputs (CF)) {off k : ℕ}
    {e e' : PE}
    (h_agree : e.AgreesBelow k e') (hk : off + 1235 ≤ k) :
    eval e ((subcircuit CompleteAdd.circuit X).output off) =
      eval e' ((subcircuit CompleteAdd.circuit X).output off) := by
  have h := CompleteAdd.eval_output_of_agreesBelow X h_agree hk
  rw [CompleteAdd.elaborated.output_eq X off] at h
  exact h

private lemma phiPairAdd_output_stable
    (X : Var PhiPairAdd.Inputs (CF)) {off k : ℕ}
    {e e' : PE}
    (h_input : eval e X = eval e' X)
    (h_agree : e.AgreesBelow k e') (hk : off + 1188 ≤ k) :
    eval e ((subcircuit PhiPairAdd.circuit X).output off) =
      eval e' ((subcircuit PhiPairAdd.circuit X).output off) := by
  have h := PhiPairAdd.eval_output_of_agreesBelow X h_input h_agree hk
  rw [PhiPairAdd.elaborated.output_eq X off] at h
  exact h

private lemma muxEmu_output_stable
    (X : Var (Mux.Inputs Emu) (CF)) {off k : ℕ}
    {e e' : PE}
    (h_agree : e.AgreesBelow k e') (hk : off + 4 ≤ k) :
    eval e ((subcircuit (Mux.circuit (M := Emu)) X).output off) =
      eval e' ((subcircuit (Mux.circuit (M := Emu)) X).output off) := by
  have h := Mux.eval_output_of_agreesBelow (M := Emu) X (offset := off) h_agree (by
    simp only [size, numLimbs]
    omega)
  exact h

private lemma canonPoint_stable {e e' : PE} {P : VP} {xv : Var Emu (CF)}
    (hP : eval e P = eval e' P) (hx : eval e xv = eval e' xv) :
    eval e ({ x := xv, y := P.y, isInf := P.isInf } : VP) =
      eval e' ({ x := xv, y := P.y, isInf := P.isInf } : VP) := by
  simp only [circuit_norm, FlaggedPoint.mk.injEq] at hP ⊢
  refine ⟨?_, hP.2.1, hP.2.2⟩
  simpa only [circuit_norm] using hx

private theorem structuralComputableWitnesses
    (offset : ℕ) (input : Var Bases (CF))
    (env env' : PE) :
    FormalCircuitBase.Operations.StructuralComputableWitnesses
      input env env' offset ((main input).operations offset) := by
  obtain ⟨r0, r1, r2, r3⟩ := input
  have hpa : ∀ (X : Var PhiPairAdd.Inputs (CF)) (o : ℕ),
      (subcircuit PhiPairAdd.circuit X).localLength o = 1188 := fun _ _ => rfl
  have hca : ∀ (X : Var CompleteAdd.Inputs (CF)) (o : ℕ),
      (subcircuit CompleteAdd.circuit X).localLength o = 1235 := fun _ _ => rfl
  have hmux : ∀ (X : Var (Mux.Inputs Emu) (CF)) (o : ℕ),
      (subcircuit (Mux.circuit (M := Emu)) X).localLength o = 4 :=
    fun _ _ => rfl
  unfold main
  simp only [
    Circuit.bind_structuralComputableWitnesses_iff,
    FormalCircuit.subcircuit_structuralComputableWitnesses_iff,
    Circuit.pure_structuralComputableWitnesses_iff,
    hpa, hca, hmux, and_true]
  have parts : ∀ {e e' : PE},
      eval e (⟨r0, r1, r2, r3⟩ : Var Bases (CF)) =
        eval e' (⟨r0, r1, r2, r3⟩ : Var Bases (CF)) →
      eval e r0 = eval e' r0 ∧ eval e r1 = eval e' r1 ∧
      eval e r2 = eval e' r2 ∧ eval e r3 = eval e' r3 := by
    intro e e' h
    simpa only [circuit_norm, Bases.mk.injEq] using h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- 1. t3 = phiPairAdd r0 r1
  · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Bases) PhiPairAdd.circuit _ _ _ ?_
      PhiPairAdd.computableWitnesses env env'
    intro k e e' _ _ h_in
    exact cond_phiPairAdd r0 r1 (parts h_in).1 (parts h_in).2.1
  -- 2. t12 = phiPairAdd r2 r3
  · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Bases) PhiPairAdd.circuit _ _ _ ?_
      PhiPairAdd.computableWitnesses env env'
    intro k e e' _ _ h_in
    exact cond_phiPairAdd r2 r3 (parts h_in).2.2.1 (parts h_in).2.2.2
  -- 3. t12x mux
  · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Bases) (Mux.circuit (M := Emu)) _ _ _ ?_
      (Mux.computableWitnesses (M := Emu)) env env'
    intro k e e' hle h_agree h_in
    simp only [circuit_norm] at hle
    have hp := phiPairAdd_output_stable (off := offset + 1188) _
      (cond_phiPairAdd r2 r3 (parts h_in).2.2.1 (parts h_in).2.2.2)
      h_agree (by omega)
    exact cond_muxEmu _ zeroConst _
      (point_isInf_stable _ hp) zeroConst_emu_stable (point_x_stable _ hp)
  -- 4. t5 = completeAdd r0 r2
  · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Bases) CompleteAdd.circuit _ _ _ ?_
      CompleteAdd.computableWitnesses env env'
    intro k e e' _ _ h_in
    exact cond_completeAdd r0 r2 (parts h_in).1 (parts h_in).2.2.1
  -- 5. t9 = completeAdd r0 r3
  · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Bases) CompleteAdd.circuit _ _ _ ?_
      CompleteAdd.computableWitnesses env env'
    intro k e e' _ _ h_in
    exact cond_completeAdd r0 r3 (parts h_in).1 (parts h_in).2.2.2
  -- 6. t6 = completeAdd r1 r2
  · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Bases) CompleteAdd.circuit _ _ _ ?_
      CompleteAdd.computableWitnesses env env'
    intro k e e' _ _ h_in
    exact cond_completeAdd r1 r2 (parts h_in).2.1 (parts h_in).2.2.1
  -- 7. t10 = completeAdd r1 r3
  · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Bases) CompleteAdd.circuit _ _ _ ?_
      CompleteAdd.computableWitnesses env env'
    intro k e e' _ _ h_in
    exact cond_completeAdd r1 r3 (parts h_in).2.1 (parts h_in).2.2.2
  -- 8. t7 = completeAdd t3 r2
  · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Bases) CompleteAdd.circuit _ _ _ ?_
      CompleteAdd.computableWitnesses env env'
    intro k e e' hle h_agree h_in
    simp only [circuit_norm] at hle
    exact cond_completeAdd _ r2
      (phiPairAdd_output_stable _ (cond_phiPairAdd r0 r1 (parts h_in).1 (parts h_in).2.1)
        h_agree (by omega)) (parts h_in).2.2.1
  -- 9. t11 = completeAdd t3 r3
  · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Bases) CompleteAdd.circuit _ _ _ ?_
      CompleteAdd.computableWitnesses env env'
    intro k e e' hle h_agree h_in
    simp only [circuit_norm] at hle
    exact cond_completeAdd _ r3
      (phiPairAdd_output_stable _ (cond_phiPairAdd r0 r1 (parts h_in).1 (parts h_in).2.1)
        h_agree (by omega)) (parts h_in).2.2.2
  -- 10. t13 = completeAdd r0 t12canon
  · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Bases) CompleteAdd.circuit _ _ _ ?_
      CompleteAdd.computableWitnesses env env'
    intro k e e' hle h_agree h_in
    simp only [circuit_norm] at hle
    have hp := phiPairAdd_output_stable (off := offset + 1188) _
      (cond_phiPairAdd r2 r3 (parts h_in).2.2.1 (parts h_in).2.2.2)
      h_agree (by omega)
    exact cond_completeAdd r0 _ (parts h_in).1
      (canonPoint_stable hp
        (muxEmu_output_stable (off := offset + 1188 + 1188) _ h_agree (by omega)))
  -- 11. t14 = completeAdd r1 t12canon
  · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Bases) CompleteAdd.circuit _ _ _ ?_
      CompleteAdd.computableWitnesses env env'
    intro k e e' hle h_agree h_in
    simp only [circuit_norm] at hle
    have hp := phiPairAdd_output_stable (off := offset + 1188) _
      (cond_phiPairAdd r2 r3 (parts h_in).2.2.1 (parts h_in).2.2.2)
      h_agree (by omega)
    exact cond_completeAdd r1 _ (parts h_in).2.1
      (canonPoint_stable hp
        (muxEmu_output_stable (off := offset + 1188 + 1188) _ h_agree (by omega)))
  -- 12. t15 = completeAdd t3 t12canon
  · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Bases) CompleteAdd.circuit _ _ _ ?_
      CompleteAdd.computableWitnesses env env'
    intro k e e' hle h_agree h_in
    simp only [circuit_norm] at hle
    have hp := phiPairAdd_output_stable (off := offset + 1188) _
      (cond_phiPairAdd r2 r3 (parts h_in).2.2.1 (parts h_in).2.2.2)
      h_agree (by omega)
    exact cond_completeAdd _ _
      (phiPairAdd_output_stable _ (cond_phiPairAdd r0 r1 (parts h_in).1 (parts h_in).2.1)
        h_agree (by omega))
      (canonPoint_stable hp
        (muxEmu_output_stable (off := offset + 1188 + 1188) _ h_agree (by omega)))

theorem computableWitnesses : circuit.base.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (FormalCircuitBase.computableWitnessCondition
      input env env') ((main input).operations offset)
  exact FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
    input env env' (structuralComputableWitnesses offset input env env')

end Subset

lemma prepare_subOutput_of_agreesBelow
    (input : VI) {offset k : ℕ}
    {env env' : PE}
    (h_input : eval env input = eval env' input)
    (h_agree : env.AgreesBelow k env') (hk : offset + 830 ≤ k) :
    eval env ((subcircuit Prepare.circuit input).output offset) =
      eval env' ((subcircuit Prepare.circuit input).output offset) := by
  simp only [circuit_norm, subcircuit, Prepare.circuit, Prepare.elaborated]
  rw [Bases.mk.injEq]
  have hp := congrArg Inputs.P h_input
  have hq := congrArg Inputs.Q h_input
  simp only [circuit_norm, FlaggedPoint.mk.injEq] at hp hq
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [FlaggedPoint.mk.injEq]
    exact ⟨hp.1, hp.2.1, hp.2.2⟩
  · rw [FlaggedPoint.mk.injEq]
    exact ⟨emu_map_eval_eq_of_eval_eq (eval_varFromOffset_of_agreesBelow
        (A := Emu) (off := offset) h_agree (by simp only [size, numLimbs]; omega)),
      emu_map_eval_eq_of_eval_eq (eval_varFromOffset_of_agreesBelow
        (A := Emu) (off := offset + 818) h_agree (by simp only [size, numLimbs]; omega)), hp.2.2⟩
  · rw [FlaggedPoint.mk.injEq]
    exact ⟨hq.1, emu_map_eval_eq_of_eval_eq (eval_varFromOffset_of_agreesBelow
      (A := Emu) (off := offset + 822) h_agree (by simp only [size, numLimbs]; omega)), hq.2.2⟩
  · rw [FlaggedPoint.mk.injEq]
    exact ⟨emu_map_eval_eq_of_eval_eq (eval_varFromOffset_of_agreesBelow
        (A := Emu) (off := offset + 341) h_agree (by simp only [size, numLimbs]; omega)),
      emu_map_eval_eq_of_eval_eq (eval_varFromOffset_of_agreesBelow
        (A := Emu) (off := offset + 826) h_agree (by simp only [size, numLimbs]; omega)), hq.2.2⟩

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
private theorem structuralComputableWitnesses
    (offset : ℕ) (input : VI)
    (env env' : PE) :
    FormalCircuitBase.Operations.StructuralComputableWitnesses
      input env env' offset ((main input).operations offset) := by
  have hp : ∀ (X : VI) (o : ℕ),
      (subcircuit Prepare.circuit X).localLength o = 830 := fun _ _ => rfl
  have hs : ∀ (X : Var Bases (CF)) (o : ℕ),
      (subcircuit Subset.circuit X).localLength o = 13495 := fun _ _ => rfl
  unfold main
  simp only [
    Circuit.bind_structuralComputableWitnesses_iff,
    FormalCircuit.subcircuit_structuralComputableWitnesses_iff,
    Circuit.pure_structuralComputableWitnesses_iff,
    hp, hs, and_true]
  refine ⟨?_, ?_⟩
  · exact FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) Prepare.circuit _ _ _
      (fun _ _ _ _ _ h_in => h_in) Prepare.computableWitnesses env env'
  · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) Subset.circuit _ _ _ ?_ Subset.computableWitnesses env env'
    intro k e e' hle h_agree _
    simp only [circuit_norm] at hle
    exact prepare_subOutput_of_agreesBelow input (by assumption) h_agree (by omega)

theorem computableWitnesses : circuit.base.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (FormalCircuitBase.computableWitnessCondition
      input env env') ((main input).operations offset)
  exact FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
    input env env' (structuralComputableWitnesses offset input env env')

private def rawV (t : Var RawTable (CF)) : Fin 16 → VP
  | ⟨0, _⟩ => t.t0 | ⟨1, _⟩ => t.t1 | ⟨2, _⟩ => t.t2 | ⟨3, _⟩ => t.t3
  | ⟨4, _⟩ => t.t4 | ⟨5, _⟩ => t.t5 | ⟨6, _⟩ => t.t6 | ⟨7, _⟩ => t.t7
  | ⟨8, _⟩ => t.t8 | ⟨9, _⟩ => t.t9 | ⟨10, _⟩ => t.t10 | ⟨11, _⟩ => t.t11
  | ⟨12, _⟩ => t.t12 | ⟨13, _⟩ => t.t13 | ⟨14, _⟩ => t.t14 | _ => t.t15

private lemma raw_eval (e : PE)
    (t : Var RawTable (CF)) (i : Fin 16) :
    rawEntry (eval e t) i = eval e (rawV t i) := by
  fin_cases i <;> simp only [rawEntry, rawV, circuit_norm]

private lemma rawV15_eq (t : Var RawTable (CF)) :
    rawV t 15 = t.t15 := by
  unfold rawV
  rfl

private lemma rawV15Stable_of_eq
    (t : Var RawTable (CF)) (v : VP)
    {env env' : PE} (ht : t.t15 = v)
    (hv : eval env v = eval env' v) :
    eval env (rawV t 15) = eval env' (rawV t 15) := by
  calc
    eval env (rawV t 15) = eval env t.t15 := congrArg (eval env) (rawV15_eq t)
    _ = eval env v := congrArg (eval env) ht
    _ = eval env' v := hv
    _ = eval env' t.t15 := congrArg (eval env') ht.symm
    _ = eval env' (rawV t 15) := congrArg (eval env') (rawV15_eq t).symm

private def caOutputAt (off : Nat) : VP :=
  { x := varFromOffset Emu (off + 1227),
    y := varFromOffset Emu (off + 1231),
    isInf := var ⟨off + 4⟩ }

private def phiOutputAt (input : Var Bases (CF)) (off : Nat) : VP :=
  (subcircuit PhiPairAdd.circuit { P := input.r0, Q := input.r1 }).output off

private def phiQOutputAt (input : Var Bases (CF)) (off : Nat) : VP :=
  (subcircuit PhiPairAdd.circuit { P := input.r2, Q := input.r3 }).output off

private def ca15OutputAt (off : Nat) : VP :=
  caOutputAt (off + 1188 + 1188 + 4 + 1235 + 1235 + 1235 + 1235 +
    1235 + 1235 + 1235 + 1235)

private def muxOutputAt (off : Nat) : Var Emu (CF) :=
  varFromOffset Emu off

private def canonXAt (P : VP) (off : Nat) : VP :=
  { x := muxOutputAt off, y := P.y, isInf := P.isInf }

attribute [local irreducible] ca15OutputAt muxOutputAt canonXAt

private def subsetOutputAt (input : Var Bases (CF)) (off : Nat) :
    Var RawTable (CF) :=
  let t3 := phiOutputAt input off
  let t12Raw := phiQOutputAt input (off + 1188)
  let t5Raw := caOutputAt (off + 1188 + 1188 + 4)
  let t9Raw := caOutputAt (off + 1188 + 1188 + 4 + 1235)
  let t6Raw := caOutputAt (off + 1188 + 1188 + 4 + 1235 + 1235)
  let t10Raw := caOutputAt (off + 1188 + 1188 + 4 + 1235 + 1235 + 1235)
  let t7Raw := caOutputAt (off + 1188 + 1188 + 4 + 1235 + 1235 + 1235 + 1235)
  let t11Raw := caOutputAt (off + 1188 + 1188 + 4 + 1235 + 1235 + 1235 + 1235 + 1235)
  let t13Raw := caOutputAt (off + 1188 + 1188 + 4 + 1235 + 1235 + 1235 + 1235 + 1235 + 1235)
  let t14Raw := caOutputAt (off + 1188 + 1188 + 4 + 1235 + 1235 + 1235 + 1235 + 1235 + 1235 + 1235)
  let t15Raw := ca15OutputAt off
  RawTable.mk infConst input.r0 input.r1 t3
    input.r2
    t5Raw
    t6Raw
    t7Raw
    input.r3
    t9Raw
    t10Raw
    t11Raw
    (canonXAt t12Raw (off + 2376))
    t13Raw
    t14Raw
    t15Raw

private def compactRawAt (input : VI) (off : Nat) :
    Var RawTable (CF) :=
  subsetOutputAt (basesAt input off) (off + 830)

private def compactEntryLow (input : VI) (off : Nat) :
    Fin 15 → VP
  | ⟨0, _⟩ => infConst
  | ⟨1, _⟩ => (basesAt input off).r0
  | ⟨2, _⟩ => (basesAt input off).r1
  | ⟨3, _⟩ => phiOutputAt (basesAt input off) (off + 830)
  | ⟨4, _⟩ => (basesAt input off).r2
  | ⟨5, _⟩ => caOutputAt (off + 830 + 1188 + 1188 + 4)
  | ⟨6, _⟩ => caOutputAt (off + 830 + 1188 + 1188 + 4 + 1235 + 1235)
  | ⟨7, _⟩ => caOutputAt (off + 830 + 1188 + 1188 + 4 + 1235 + 1235 + 1235 + 1235)
  | ⟨8, _⟩ => (basesAt input off).r3
  | ⟨9, _⟩ => caOutputAt (off + 830 + 1188 + 1188 + 4 + 1235)
  | ⟨10, _⟩ => caOutputAt (off + 830 + 1188 + 1188 + 4 + 1235 + 1235 + 1235)
  | ⟨11, _⟩ => caOutputAt (off + 830 + 1188 + 1188 + 4 + 1235 + 1235 + 1235 + 1235 + 1235)
  | ⟨12, _⟩ => canonXAt (phiQOutputAt (basesAt input off) (off + 830 + 1188)) (off + 830 + 2376)
  | ⟨13, _⟩ => caOutputAt (off + 830 + 1188 + 1188 + 4 + 1235 + 1235 + 1235 + 1235 + 1235 + 1235)
  | _ => caOutputAt (off + 830 + 1188 + 1188 + 4 + 1235 + 1235 + 1235 + 1235 + 1235 + 1235 + 1235)

private def compactEntryAt (input : VI) (off : Nat)
    (i : Fin 16) : VP :=
  Fin.lastCases
    (ca15OutputAt (off + 830))
    (compactEntryLow input off) i

attribute [local irreducible] compactRawAt rawV compactEntryLow compactEntryAt

private lemma compactRawAt_t15_eq (input : VI) (off : Nat) :
    (compactRawAt input off).t15 =
      ca15OutputAt (off + 830) := by
  unfold compactRawAt
  simp only [subsetOutputAt]

set_option maxRecDepth 262144
private lemma caOutputAt_stable {off k : Nat}
    {env env' : PE}
    (h_agree : env.AgreesBelow k env') (hk : off + 1235 ≤ k) :
    eval env (caOutputAt off) = eval env' (caOutputAt off) := by
  unfold caOutputAt
  simp only [circuit_norm]
  rw [FlaggedPoint.mk.injEq]
  refine ⟨?_, ?_, h_agree (off + 4) (by omega)⟩
  · simpa only [circuit_norm] using
      eval_varFromOffset_of_agreesBelow (A := Emu) (off := off + 1227) h_agree
        (by rw [show size Emu = 4 from rfl]; omega)
  · simpa only [circuit_norm] using
      eval_varFromOffset_of_agreesBelow (A := Emu) (off := off + 1231) h_agree
        (by rw [show size Emu = 4 from rfl]; omega)

private lemma ca15OutputAt_stable {off k : Nat}
    {env env' : PE}
    (h_agree : env.AgreesBelow k env') (hk : off + 13495 ≤ k) :
    eval env (ca15OutputAt off) = eval env' (ca15OutputAt off) := by
  unfold ca15OutputAt
  exact caOutputAt_stable h_agree (by omega)

set_option maxRecDepth 4194304 in
private lemma compactEntryAt_eq (input : VI) (off : Nat)
    (i : Fin 16) :
    compactEntryAt input off i = rawV (compactRawAt input off) i := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · calc
      compactEntryAt input off (Fin.last 15) =
          ca15OutputAt (off + 830) := by
        simp only [compactEntryAt, Fin.lastCases_last]
      _ = (compactRawAt input off).t15 := (compactRawAt_t15_eq input off).symm
      _ = rawV (compactRawAt input off) (Fin.last 15) := by
        simpa only using (rawV15_eq (compactRawAt input off)).symm
  · simp only [compactEntryAt, Fin.lastCases_castSucc]
    fin_cases j <;> simp only [Fin.castSucc_mk] <;>
      unfold compactEntryLow compactRawAt rawV <;>
      simp only [subsetOutputAt]

private lemma muxOutputAt_stable {off k : Nat}
    {env env' : PE}
    (h_agree : env.AgreesBelow k env') (hk : off + 4 ≤ k) :
    eval env (muxOutputAt off) = eval env' (muxOutputAt off) := by
  unfold muxOutputAt
  exact eval_varFromOffset_of_agreesBelow (A := Emu) h_agree
    (by rw [show size Emu = 4 from rfl]; omega)

private lemma canonXAt_stable
    {P : VP} {xoff : Nat} {env env' : PE}
    (hx : eval env (muxOutputAt xoff) = eval env' (muxOutputAt xoff))
    (hP : eval env P = eval env' P) :
    eval env (canonXAt P xoff) =
      eval env' (canonXAt P xoff) := by
  unfold canonXAt
  simp only [circuit_norm] at hP ⊢
  rw [FlaggedPoint.mk.injEq] at hP ⊢
  exact ⟨by simpa only [circuit_norm] using hx, hP.2.1, hP.2.2⟩

private lemma compactStable0 (input : VI) (offset : Nat)
    {env env' : PE} :
    eval env (compactEntryLow input offset 0) =
      eval env' (compactEntryLow input offset 0) := by
  unfold compactEntryLow
  simp only [subsetOutputAt, circuit_norm, infConst]
  rw [FlaggedPoint.mk.injEq]
  refine ⟨?_, ?_, rfl⟩ <;>
    rw [DivOrZero.eval_zeroConst, DivOrZero.eval_zeroConst]

private lemma compactStable1 (input : VI) (offset : Nat)
    {env env' : PE}
    (hb : eval env (basesAt input offset) = eval env' (basesAt input offset)) :
    eval env (compactEntryLow input offset 1) =
      eval env' (compactEntryLow input offset 1) := by
  unfold compactEntryLow
  simp only [subsetOutputAt]
  simpa only [circuit_norm] using congrArg Bases.r0 hb

private lemma compactStable2 (input : VI) (offset : Nat)
    {env env' : PE}
    (hb : eval env (basesAt input offset) = eval env' (basesAt input offset)) :
    eval env (compactEntryLow input offset 2) =
      eval env' (compactEntryLow input offset 2) := by
  unfold compactEntryLow
  simp only [subsetOutputAt]
  simpa only [circuit_norm] using congrArg Bases.r1 hb

private lemma compactStable4 (input : VI) (offset : Nat)
    {env env' : PE}
    (hb : eval env (basesAt input offset) = eval env' (basesAt input offset)) :
    eval env (compactEntryLow input offset 4) =
      eval env' (compactEntryLow input offset 4) := by
  unfold compactEntryLow
  simp only [subsetOutputAt]
  simpa only [circuit_norm] using congrArg Bases.r2 hb

private lemma compactStable8 (input : VI) (offset : Nat)
    {env env' : PE}
    (hb : eval env (basesAt input offset) = eval env' (basesAt input offset)) :
    eval env (compactEntryLow input offset 8) =
      eval env' (compactEntryLow input offset 8) := by
  unfold compactEntryLow
  simp only [subsetOutputAt]
  simpa only [circuit_norm] using congrArg Bases.r3 hb

private lemma compactStable3 (input : VI) {offset k : Nat}
    {env env' : PE}
    (hb : eval env (basesAt input offset) = eval env' (basesAt input offset))
    (h_agree : env.AgreesBelow k env') (hk : offset + 14325 ≤ k) :
    eval env (compactEntryLow input offset 3) =
      eval env' (compactEntryLow input offset 3) := by
  unfold compactEntryLow
  simp only [subsetOutputAt]
  have hb0 : eval env (basesAt input offset).r0 =
      eval env' (basesAt input offset).r0 := by
    simpa only [circuit_norm] using congrArg Bases.r0 hb
  have hb1 : eval env (basesAt input offset).r1 =
      eval env' (basesAt input offset).r1 := by
    simpa only [circuit_norm] using congrArg Bases.r1 hb
  exact Subset.phiPairAdd_output_stable _
    (cond_phiPairAdd (basesAt input offset).r0 (basesAt input offset).r1 hb0 hb1)
    h_agree (by omega)

private lemma compactStable5 (input : VI) {offset k : Nat}
    {env env' : PE}
    (h_agree : env.AgreesBelow k env') (hk : offset + 14325 ≤ k) :
    eval env (compactEntryLow input offset 5) =
      eval env' (compactEntryLow input offset 5) := by
  unfold compactEntryLow
  simp only [subsetOutputAt]
  exact caOutputAt_stable h_agree (by omega)

private lemma compactStable6 (input : VI) {offset k : Nat}
    {env env' : PE}
    (h_agree : env.AgreesBelow k env') (hk : offset + 14325 ≤ k) :
    eval env (compactEntryLow input offset 6) =
      eval env' (compactEntryLow input offset 6) := by
  unfold compactEntryLow
  simp only [subsetOutputAt]
  exact caOutputAt_stable h_agree (by omega)

private lemma compactStable7 (input : VI) {offset k : Nat}
    {env env' : PE}
    (h_agree : env.AgreesBelow k env') (hk : offset + 14325 ≤ k) :
    eval env (compactEntryLow input offset 7) =
      eval env' (compactEntryLow input offset 7) := by
  unfold compactEntryLow
  simp only [subsetOutputAt]
  exact caOutputAt_stable h_agree (by omega)

private lemma compactStable9 (input : VI) {offset k : Nat}
    {env env' : PE}
    (h_agree : env.AgreesBelow k env') (hk : offset + 14325 ≤ k) :
    eval env (compactEntryLow input offset 9) =
      eval env' (compactEntryLow input offset 9) := by
  unfold compactEntryLow
  simp only [subsetOutputAt]
  exact caOutputAt_stable h_agree (by omega)

private lemma compactStable10 (input : VI) {offset k : Nat}
    {env env' : PE}
    (h_agree : env.AgreesBelow k env') (hk : offset + 14325 ≤ k) :
    eval env (compactEntryLow input offset 10) =
      eval env' (compactEntryLow input offset 10) := by
  unfold compactEntryLow
  simp only [subsetOutputAt]
  exact caOutputAt_stable h_agree (by omega)

private lemma compactStable11 (input : VI) {offset k : Nat}
    {env env' : PE}
    (h_agree : env.AgreesBelow k env') (hk : offset + 14325 ≤ k) :
    eval env (compactEntryLow input offset 11) =
      eval env' (compactEntryLow input offset 11) := by
  unfold compactEntryLow
  simp only [subsetOutputAt]
  exact caOutputAt_stable h_agree (by omega)

private lemma compactStable12 (input : VI) {offset k : Nat}
    {env env' : PE}
    (hb : eval env (basesAt input offset) = eval env' (basesAt input offset))
    (h_agree : env.AgreesBelow k env') (hk : offset + 14325 ≤ k) :
    eval env (compactEntryLow input offset 12) =
      eval env' (compactEntryLow input offset 12) := by
  unfold compactEntryLow
  simp only [subsetOutputAt]
  have hb2 : eval env (basesAt input offset).r2 =
      eval env' (basesAt input offset).r2 := by
    simpa only [circuit_norm] using congrArg Bases.r2 hb
  have hb3 : eval env (basesAt input offset).r3 =
      eval env' (basesAt input offset).r3 := by
    simpa only [circuit_norm] using congrArg Bases.r3 hb
  exact canonXAt_stable (muxOutputAt_stable h_agree (by omega))
    (Subset.phiPairAdd_output_stable _
      (cond_phiPairAdd (basesAt input offset).r2 (basesAt input offset).r3 hb2 hb3)
      h_agree (by omega))

private lemma compactStable13 (input : VI) {offset k : Nat}
    {env env' : PE}
    (h_agree : env.AgreesBelow k env') (hk : offset + 14325 ≤ k) :
    eval env (compactEntryLow input offset 13) =
      eval env' (compactEntryLow input offset 13) := by
  unfold compactEntryLow
  simp only [subsetOutputAt]
  exact caOutputAt_stable h_agree (by omega)

private lemma compactStable14 (input : VI) {offset k : Nat}
    {env env' : PE}
    (h_agree : env.AgreesBelow k env') (hk : offset + 14325 ≤ k) :
    eval env (compactEntryLow input offset 14) =
      eval env' (compactEntryLow input offset 14) := by
  unfold compactEntryLow
  simp only [subsetOutputAt]
  exact caOutputAt_stable h_agree (by omega)

set_option maxRecDepth 4194304 in
private lemma eval_compactEntryLow_of_agreesBelow
    (input : VI) {offset k : Nat}
    {env env' : PE} (j : Fin 15)
    (h_input : eval env input = eval env' input)
    (h_agree : env.AgreesBelow k env') (hk : offset + 14325 ≤ k) :
    eval env (compactEntryLow input offset j) =
      eval env' (compactEntryLow input offset j) := by
  have hb : eval env (basesAt input offset) = eval env' (basesAt input offset) :=
    prepare_subOutput_of_agreesBelow input h_input h_agree (by omega)
  fin_cases j
  · exact compactStable0 input offset
  · exact compactStable1 input offset hb
  · exact compactStable2 input offset hb
  · exact compactStable3 input (offset := offset) hb h_agree hk
  · exact compactStable4 input offset hb
  · exact compactStable5 input h_agree hk
  · exact compactStable6 input h_agree hk
  · exact compactStable7 input h_agree hk
  · exact compactStable8 input offset hb
  · exact compactStable9 input h_agree hk
  · exact compactStable10 input h_agree hk
  · exact compactStable11 input h_agree hk
  · exact compactStable12 input hb h_agree hk
  · exact compactStable13 input h_agree hk
  · exact compactStable14 input h_agree hk

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 1048576 in
private lemma subset_circuit_output_eq_outputAt
    (input : Var Bases (CF)) (off : Nat) :
    Subset.circuit.output input off = subsetOutputAt input off := by
  change Subset.elaborated.output input off = _
  unfold subsetOutputAt canonXAt muxOutputAt ca15OutputAt caOutputAt
    phiOutputAt phiQOutputAt
  rfl

set_option maxRecDepth 1048576 in
private lemma tableAt_eq_compact (input : VI) (off : Nat) :
    tableAt input off = Pack.pack (compactRawAt input off) := by
  unfold compactRawAt tableAt rawAt
  simpa only [Prepare.localLength] using congrArg Pack.pack
    (subset_circuit_output_eq_outputAt (basesAt input off)
      (off + Prepare.circuit.localLength input))

attribute [local irreducible] tableAt

def entryV (t : Var Table (CF)) (i : Fin 16) :
    VP :=
  { x := t.tx[i.val]'i.isLt, y := t.ty[i.val]'i.isLt,
    isInf := t.tinf[i.val]'i.isLt }

def tableEntryAt (input : VI) (off : Nat) (i : Fin 16) :
    VP := entryV (tableAt input off) i

attribute [local irreducible] entryV tableEntryAt

private lemma tableEntryAt_eq_compact
    (input : VI) (off : Nat) (i : Fin 16) :
    tableEntryAt input off i =
      entryV (Pack.pack (compactRawAt input off)) i := by
  unfold tableEntryAt
  exact congrArg
    (fun t : Var Table (CF) => entryV t i)
    (tableAt_eq_compact input off)

set_option maxRecDepth 4194304 in
set_option maxHeartbeats 4000000 in
private lemma entryV_pack_rawV (raw : Var RawTable (CF)) (i : Fin 16) :
    entryV (Pack.pack raw) i = rawV raw i := by
  fin_cases i <;> simp [entryV, Pack.pack] <;> unfold rawV <;> rfl

private lemma entryV_pack_t15 (raw : Var RawTable (CF)) :
    entryV (Pack.pack raw) 15 = raw.t15 :=
  (entryV_pack_rawV raw 15).trans (rawV15_eq raw)

set_option maxRecDepth 4194304 in
private lemma canonT15At_eq_tableLast
    (input : VI) (off : Nat) :
    ca15OutputAt (off + 830) =
      tableEntryAt input off (Fin.last 15) := by
  calc
    ca15OutputAt (off + 830) =
        (compactRawAt input off).t15 := (compactRawAt_t15_eq input off).symm
    _ = entryV (Pack.pack (compactRawAt input off)) 15 :=
      (entryV_pack_t15 (compactRawAt input off)).symm
    _ = tableEntryAt input off (Fin.last 15) :=
      (tableEntryAt_eq_compact input off (Fin.last 15)).symm

private lemma evalStable_of_eq
    {a b : VP}
    {env env' : PE}
    (hab : a = b) (hb : eval env b = eval env' b) :
    eval env a = eval env' a := by
  cases hab
  exact hb

private lemma entryStable_of_rawStable
    (input : VI) (offset : Nat) (i : Fin 16)
    {env env' : PE}
    (raw : Var RawTable (CF))
    (hc : tableEntryAt input offset i = entryV (Pack.pack raw) i)
    (hi : eval env (rawV raw i) = eval env' (rawV raw i)) :
    eval env (tableEntryAt input offset i) =
      eval env' (tableEntryAt input offset i) := by
  calc
    eval env (tableEntryAt input offset i) =
        eval env (entryV (Pack.pack raw) i) := congrArg (eval env) hc
    _ = entry (eval env (Pack.pack raw)) i.val i.isLt := by
      simp only [entryV, entry, circuit_norm, ← getElem_eval_vector]
    _ = rawEntry (eval env raw) i := by
      simpa only [circuit_norm] using
        Pack.eval_pack_entry_whole env.toEnvironment raw i
    _ = eval env (rawV raw i) := raw_eval env raw i
    _ = eval env' (rawV raw i) := hi
    _ = rawEntry (eval env' raw) i := (raw_eval env' raw i).symm
    _ = entry (eval env' (Pack.pack raw)) i.val i.isLt := by
      simpa only [circuit_norm] using
        (Pack.eval_pack_entry_whole env'.toEnvironment raw i).symm
    _ = eval env' (entryV (Pack.pack raw) i) := by
      simp only [entryV, entry, circuit_norm, ← getElem_eval_vector]
    _ = eval env' (tableEntryAt input offset i) :=
      congrArg (eval env') hc.symm

private lemma entryAtStable_of_rawStable
    (input : VI) (offset : Nat) (i : Fin 16)
    {env env' : PE}
    (hi : eval env (rawV (compactRawAt input offset) i) =
      eval env' (rawV (compactRawAt input offset) i)) :
    eval env (tableEntryAt input offset i) =
      eval env' (tableEntryAt input offset i) := by
  exact entryStable_of_rawStable input offset i
    (compactRawAt input offset) (tableEntryAt_eq_compact input offset i) hi

private lemma entryStable_of_compactStable
    (input : VI) (offset : Nat) (i : Fin 16)
    {env env' : PE}
    (hi : eval env (compactEntryAt input offset i) =
      eval env' (compactEntryAt input offset i)) :
    eval env (tableEntryAt input offset i) =
      eval env' (tableEntryAt input offset i) := by
  have he := compactEntryAt_eq input offset i
  have hr : eval env (rawV (compactRawAt input offset) i) =
      eval env' (rawV (compactRawAt input offset) i) := by
    calc
      eval env (rawV (compactRawAt input offset) i) =
          eval env (compactEntryAt input offset i) := congrArg (eval env) he.symm
      _ = eval env' (compactEntryAt input offset i) := hi
      _ = eval env' (rawV (compactRawAt input offset) i) := congrArg (eval env') he
  exact entryAtStable_of_rawStable input offset i hr

set_option maxRecDepth 4194304 in
private lemma tableStableLow
    (input : VI) {offset k : Nat}
    {env env' : PE} (j : Fin 15)
    (h_input : eval env input = eval env' input)
    (h_agree : env.AgreesBelow k env') (hk : offset + 14325 ≤ k) :
    eval env (tableEntryAt input offset (Fin.castSucc j)) =
      eval env' (tableEntryAt input offset (Fin.castSucc j)) := by
  apply entryStable_of_compactStable input offset (Fin.castSucc j)
  simpa only [compactEntryAt, Fin.lastCases_castSucc] using
    eval_compactEntryLow_of_agreesBelow input j h_input h_agree hk

private def LowEntriesStable
    (t : Var Table (CF))
    (env env' : PE) : Prop :=
  ∀ j : Fin 15,
    entry (eval env t) (Fin.castSucc j).val (Fin.castSucc j).isLt =
      entry (eval env' t) (Fin.castSucc j).val (Fin.castSucc j).isLt

private def LastEntryStable
    (t : Var Table (CF))
    (env env' : PE) : Prop :=
  entry (eval env t) (Fin.last 15).val (Fin.last 15).isLt =
    entry (eval env' t) (Fin.last 15).val (Fin.last 15).isLt

attribute [local irreducible] LowEntriesStable LastEntryStable

set_option maxRecDepth 4194304 in
private lemma eval_table_of_lowLastStable
    (t : Var Table (CF))
    {env env' : PE}
    (hlow : LowEntriesStable t env env')
    (hlast : LastEntryStable t env env') :
    eval env t = eval env' t := by
  unfold LowEntriesStable at hlow
  unfold LastEntryStable at hlast
  have hentry (i : Fin 16) :
      entry (eval env t) i.val i.isLt = entry (eval env' t) i.val i.isLt :=
    Fin.lastCases hlast (fun j => hlow j) i
  simp only [circuit_norm]
  rw [Table.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · apply Vector.ext
    intro i hi
    have h := hentry ⟨i, hi⟩
    simp only [entry, FlaggedPoint.mk.injEq] at h
    simpa only [circuit_norm] using h.1
  · apply Vector.ext
    intro i hi
    have h := hentry ⟨i, hi⟩
    simp only [entry, FlaggedPoint.mk.injEq] at h
    simpa only [circuit_norm] using h.2.1
  · apply Vector.ext
    intro i hi
    have h := hentry ⟨i, hi⟩
    simp only [entry, FlaggedPoint.mk.injEq] at h
    simpa only [circuit_norm] using h.2.2

private lemma eval_tableEntryAt_eq_entry
    (env : PE)
    (input : VI) (off : Nat) (i : Fin 16) :
    eval env (tableEntryAt input off i) =
      entry (eval env (tableAt input off)) i.val i.isLt := by
  simp only [tableEntryAt, entryV, entry, circuit_norm, ← getElem_eval_vector]

set_option maxRecDepth 4194304 in
private lemma concreteLowEntriesStable
    (input : VI) {offset k : Nat}
    {env env' : PE}
    (h_input : eval env input = eval env' input)
    (h_agree : env.AgreesBelow k env') (hk : offset + 14325 ≤ k) :
    LowEntriesStable (tableAt input offset) env env' := by
  unfold LowEntriesStable
  intro j
  rw [← eval_tableEntryAt_eq_entry env input offset (Fin.castSucc j),
    ← eval_tableEntryAt_eq_entry env' input offset (Fin.castSucc j)]
  exact tableStableLow input j h_input h_agree hk

set_option maxRecDepth 4194304 in
private lemma lastEntryStable_of_tableEntryStable
    (input : VI) (offset : Nat)
    {env env' : PE}
    (h : eval env (tableEntryAt input offset (Fin.last 15)) =
      eval env' (tableEntryAt input offset (Fin.last 15))) :
    LastEntryStable (tableAt input offset) env env' := by
  unfold LastEntryStable
  rw [← eval_tableEntryAt_eq_entry env input offset (Fin.last 15),
    ← eval_tableEntryAt_eq_entry env' input offset (Fin.last 15)]
  exact h

set_option maxRecDepth 4194304 in
private lemma ca15FinalBound {offset k : Nat} (hk : offset + 14325 ≤ k) :
    offset + 830 + 13495 ≤ k := by
  have hn : 830 + 13495 = 14325 := by norm_num
  rw [Nat.add_assoc, hn]
  omega

set_option maxRecDepth 4194304 in
private lemma concreteTableLastStable
    (input : VI) {offset k : Nat}
    {env env' : PE}
    (h_agree : env.AgreesBelow k env') (hk : offset + 14325 ≤ k) :
    eval env (tableEntryAt input offset (Fin.last 15)) =
      eval env' (tableEntryAt input offset (Fin.last 15)) := by
  exact evalStable_of_eq (canonT15At_eq_tableLast input offset).symm
    (ca15OutputAt_stable (off := offset + 830) h_agree (ca15FinalBound hk))

set_option maxRecDepth 4194304 in
private lemma concreteLastEntryStable
    (input : VI) {offset k : Nat}
    {env env' : PE}
    (h_agree : env.AgreesBelow k env') (hk : offset + 14325 ≤ k) :
    LastEntryStable (tableAt input offset) env env' := by
  apply lastEntryStable_of_tableEntryStable input offset
  exact concreteTableLastStable input h_agree hk

set_option maxRecDepth 4194304 in
set_option maxHeartbeats 4000000 in
lemma eval_tableAt_of_agreesBelow
    (input : VI) {offset k : ℕ}
    {env env' : PE}
    (h_input : eval env input = eval env' input)
    (h_agree : env.AgreesBelow k env') (hk : offset + 14325 ≤ k) :
    eval env (tableAt input offset) = eval env' (tableAt input offset) := by
  exact eval_table_of_lowLastStable (tableAt input offset)
    (concreteLowEntriesStable input h_input h_agree hk)
    (concreteLastEntryStable input h_agree hk)

end GLVBuildTable
end Solution.Secp256k1ScalarMul
