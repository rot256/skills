import Solution.Secp256k1ScalarMul.ScalarMul
import Solution.Secp256k1ScalarMul.PointValid
import Solution.Secp256k1ScalarMul.PointOutput
import Solution.Secp256k1ScalarMul.CoeffWitness
import Solution.Secp256k1ScalarMul.GLVScalarRelation
import Solution.Secp256k1ScalarMul.GLVBuildTable
import Solution.Secp256k1ScalarMul.GLVMSM
import Solution.Secp256k1ScalarMul.Lazy.LazyBridge
import Solution.Secp256k1ScalarMul.GLVVerifierTheorems
import Solution.Secp256k1ScalarMul.OrderFactsCerts

namespace Solution.Secp256k1ScalarMul
namespace GLVScalarMul

open Specs.ShortWeierstrass Specs.Secp256k1

def encodePoint : GroupPoint Fp → FlaggedPoint (F circomPrime)
  | .infinity => { x := emuOfNat 0, y := emuOfNat 0, isInf := 1 }
  | .affine P => { x := emuOfNat P.x.val, y := emuOfNat P.y.val, isInf := 0 }

lemma encodePoint_valid {G : GroupPoint Fp}
    (hG : OnCurveOrInfinity curve G) :
    (encodePoint G).Valid ∧
      ((encodePoint G).isInf = 1 →
        (encodePoint G).x = emuOfNat 0 ∧ (encodePoint G).y = emuOfNat 0) := by
  cases G with
  | infinity =>
      simp [encodePoint, FlaggedPoint.Valid,
        CompleteAdd.fe_valid_emuOfNat (by decide : 0 < P256), IsBool.one]
  | affine P =>
      refine ⟨⟨Or.inl rfl,
        CompleteAdd.fe_valid_emuOfNat (ZMod.val_lt P.x),
        CompleteAdd.fe_valid_emuOfNat (ZMod.val_lt P.y), ?_⟩, ?_⟩
      · intro _
        simpa [encodePoint, CompleteAdd.decodeFe_emuOfNat_val] using hG
      · norm_num [encodePoint]

@[simp] theorem decode_encodePoint (G : GroupPoint Fp) :
    decodePoint (encodePoint G) = G := by
  cases G with
  | infinity => simp [encodePoint, decodePoint]
  | affine P =>
      simp [encodePoint, decodePoint, CompleteAdd.decodeFe_emuOfNat_val]

#check decode_encodePoint

def inputPoint (input : ScalarMul.Inputs (F circomPrime)) :
    FlaggedPoint (F circomPrime) :=
  { x := input.px, y := input.py, isInf := 0 }

def inputPointVar (input : Var ScalarMul.Inputs (F circomPrime)) :
    Var FlaggedPoint (F circomPrime) :=
  { x := input.px, y := input.py, isInf := 0 }

lemma inputPoint_valid {input : ScalarMul.Inputs (F circomPrime)}
    (h : ScalarMul.Assumptions input) : (inputPoint input).Valid := by
  exact ⟨Or.inl rfl, h.2.1, h.2.2.1, by simpa [inputPoint] using h.2.2.2⟩

lemma decodePoint_onCurveOrInfinity {P : FlaggedPoint (F circomPrime)}
    (hP : P.Valid) : OnCurveOrInfinity curve (decodePoint P) := by
  rcases hP.1 with h0 | h1
  · rw [decodePoint, if_neg (by
      simpa [h0] using (zero_ne_one : (0 : F circomPrime) ≠ 1))]
    exact hP.2.2.2 h0
  · rw [decodePoint, if_pos h1]
    trivial

@[simp] lemma decode_inputPoint (input : ScalarMul.Inputs (F circomPrime)) :
    decodePoint (inputPoint input) =
      .affine { x := decodeFe input.px, y := decodeFe input.py } := by
  simp [inputPoint, decodePoint]

def trueResult (input : ScalarMul.Inputs (F circomPrime)) : GroupPoint Fp :=
  scalarMul curve (input.bits.map ZMod.val)
    { x := decodeFe input.px, y := decodeFe input.py }

def resultWitness (input : Var ScalarMul.Inputs (F circomPrime))
    (env : ProverEnvironment (F circomPrime)) : FlaggedPoint (F circomPrime) :=
  encodePoint (trueResult (eval env input))

/-- Honest decomposition: the sign pattern for special scalars, a short
decomposition otherwise (see `SpecialScalar.decomposition`). -/
noncomputable def decompositionValue (input : ScalarMul.Inputs (F circomPrime)) :
    ShortCoeffs.Decomposition
      ((GLV.ScalarReduce.scalarValue { bits := input.bits } : ℕ) : ZMod order) :=
  SpecialScalar.decomposition
    ((GLV.ScalarReduce.scalarValue { bits := input.bits } : ℕ) : ZMod order)

noncomputable def coefficientValue (input : ScalarMul.Inputs (F circomPrime)) :
    GLV.Coefficients (F circomPrime) :=
  CoeffWitness.ofDecomposition (decompositionValue input)

noncomputable def coefficientWitness
    (input : Var ScalarMul.Inputs (F circomPrime))
    (env : ProverEnvironment (F circomPrime)) :
    GLV.Coefficients (F circomPrime) :=
  coefficientValue (eval env input)

lemma eval_provableWitness
    {α : TypeMap} [ProvableType α]
    (compute : ProverEnvironment (F circomPrime) → α (F circomPrime))
    (env : ProverEnvironment (F circomPrime)) (offset : ℕ)
    (h : env.ExtendsVector (toElements (compute env)) offset) :
    eval env ((ProvableType.witness (F := F circomPrime) (α := α) compute).output offset) =
      compute env := by
  change eval env (varFromOffset α offset : Var α (F circomPrime)) = compute env
  rw [ProvableType.ext_iff]
  intro i hi
  rw [ProvableType.eval_varFromOffset_prover,
    ProvableType.toElements_fromElements, Vector.getElem_mapRange]
  exact h ⟨i, hi⟩

theorem verifiedPoint_eq_trueResult
    {input : ScalarMul.Inputs (F circomPrime)}
    {Q : FlaggedPoint (F circomPrime)}
    {c : GLV.Coefficients (F circomPrime)}
    {s : Emu (F circomPrime)}
    {table : GLVBuildTable.Table (F circomPrime)}
    (hinput : ScalarMul.Assumptions input)
    (hQ : Q.Valid)
    (hc : GLV.Valid c.u1 ∧ GLV.Valid c.u2 ∧
      GLV.Valid c.v1 ∧ GLV.Valid c.v2)
    (hs : GLV.ScalarReduce.Spec { bits := input.bits } s)
    (hr : GLVScalarRelation.Spec
      { s, u1 := c.u1, u2 := c.u2, v1 := c.v1, v2 := c.v2 })
    (ht : PatBuildTable.Spec
      { P := inputPoint input, Q
        sign0 := c.u1.sign, sign1 := c.u2.sign
        sign2 := c.v1.sign, sign3 := c.v2.sign } table)
    (hm : LazyMSM.Spec (GLVVerifierTheorems.msmInput table c)) :
    decodePoint Q = trueResult input := by
  let P0 : Point Fp := { x := decodeFe input.px, y := decodeFe input.py }
  let PW : Bridge.W.Point := Bridge.mkPoint P0 hinput.2.2.2
  have hQcurve := decodePoint_onCurveOrInfinity hQ
  let QW : Bridge.W.Point := Bridge.fromSpec (decodePoint Q) hQcurve
  have hPd : decodePoint (inputPoint input) = Bridge.toSpec PW := by
    rw [decode_inputPoint]
    exact (Bridge.toSpec_mkPoint P0 hinput.2.2.2).symm
  have hQd : decodePoint Q = Bridge.toSpec QW := by
    exact (Bridge.toSpec_fromSpec (decodePoint Q) hQcurve).symm
  have hgroup := LazyBridge.groupRelation_of_lazy PW QW hPd hQd
    ht hc rfl rfl rfl rfl hm
  have hscalar := GLVVerifierTheorems.fakeScalarRelation hs hr.1
  have hV := GLVVerifierTheorems.shortCombination_nonzero c.v1 c.v2
    hc.2.2.1 hc.2.2.2 hr.2
  have hfake := FakeGLVSound.sound PW QW
    (GLV.ScalarReduce.scalarValue { bits := input.bits })
    (GLV.signedValue c.u1) (GLV.signedValue c.u2)
    (GLV.signedValue c.v1) (GLV.signedValue c.v2)
    hgroup hscalar hV
  have hbits : IsBitArray (input.bits.map ZMod.val) := by
    intro i
    simp only [Vector.getElem_map, Fin.getElem_fin]
    exact IsBool.val_lt_two (hinput.1 i)
  have htrue : trueResult input = Bridge.toSpec
      (GLV.ScalarReduce.scalarValue { bits := input.bits } • PW) := by
    unfold trueResult GLV.ScalarReduce.scalarValue
    exact Bridge.scalarMul_eq_smul (input.bits.map ZMod.val) hbits P0 hinput.2.2.2
  rw [hQd, hfake, ← htrue]

#check verifiedPoint_eq_trueResult

theorem honestLazy
    (input : ScalarMul.Inputs (F circomPrime))
    (hinput : ScalarMul.Assumptions input)
    (table : GLVBuildTable.Table (F circomPrime))
    (ht : PatBuildTable.Spec
      { P := inputPoint input, Q := encodePoint (trueResult input)
        sign0 := (coefficientValue input).u1.sign
        sign1 := (coefficientValue input).u2.sign
        sign2 := (coefficientValue input).v1.sign
        sign3 := (coefficientValue input).v2.sign } table) :
    LazyMSM.ProverAssumptions
      (GLVVerifierTheorems.msmInput table (coefficientValue input)) := by
  let P0 : Point Fp := { x := decodeFe input.px, y := decodeFe input.py }
  let PW : Bridge.W.Point := Bridge.mkPoint P0 hinput.2.2.2
  let k := GLV.ScalarReduce.scalarValue { bits := input.bits }
  have hP0 : PW ≠ 0 := by
    intro h0
    have := Bridge.toSpec_mkPoint P0 hinput.2.2.2
    rw [show Bridge.mkPoint P0 hinput.2.2.2 = PW from rfl, h0, Bridge.toSpec_zero] at this
    cases this
  have hPd : decodePoint (inputPoint input) = Bridge.toSpec PW := by
    rw [decode_inputPoint]
    exact (Bridge.toSpec_mkPoint P0 hinput.2.2.2).symm
  have hbits : IsBitArray (input.bits.map ZMod.val) := by
    intro i
    simp only [Vector.getElem_map, Fin.getElem_fin]
    exact IsBool.val_lt_two (hinput.1 i)
  have hresult : trueResult input = Bridge.toSpec (k • PW) := by
    unfold trueResult k GLV.ScalarReduce.scalarValue
    exact Bridge.scalarMul_eq_smul (input.bits.map ZMod.val) hbits P0 hinput.2.2.2
  have hQd : decodePoint (encodePoint (trueResult input)) =
      Bridge.toSpec (k • PW) := by rw [decode_encodePoint, hresult]
  exact LazyBridge.honestProverAssumptions PW hP0 k hPd hQd rfl rfl rfl rfl ht

#check honestLazy

namespace AssertInfinity

def main (P : Var FlaggedPoint (F circomPrime)) : Circuit (F circomPrime) Unit :=
  assertZero (P.isInf - 1)

instance elaborated :
    ElaboratedCircuit (F circomPrime) FlaggedPoint unit main where
  localLength _ := 0

def Assumptions (_ : FlaggedPoint (F circomPrime)) : Prop := True

def Spec (P : FlaggedPoint (F circomPrime)) : Prop := P.isInf = 1

theorem soundness :
    FormalAssertion.Soundness (F circomPrime) main Assumptions Spec := by
  unfold FormalAssertion.Soundness
  intro offset env input_var input h_input _ h_holds
  subst input
  constructor
  · change (eval env input_var).isInf = 1
    simp only [main, Circuit.operations, ConstraintsHold.Soundness,
      Operations.forAllNoOffset, circuit_norm] at h_holds
    have hx : Expression.eval env input_var.isInf = -(-1) :=
      eq_neg_of_add_eq_zero_left h_holds
    simpa only [circuit_norm, neg_neg] using hx
  · exact ⟨trivial, trivial⟩

theorem completeness :
    FormalAssertion.Completeness (F circomPrime) main Assumptions Spec := by
  unfold FormalAssertion.Completeness
  intro offset env input_var _ input h_input _ h_spec
  subst input
  simp only [main, Circuit.operations, ConstraintsHold.Completeness,
    Operations.forAllNoOffset, circuit_norm]
  simp only [Spec, circuit_norm] at h_spec
  calc
    Expression.eval env.toEnvironment input_var.isInf + -1 = 1 + -1 :=
      congrArg (fun z : F circomPrime => z + -1) h_spec
    _ = 0 := add_neg_cancel 1

def circuit : FormalAssertion (F circomPrime) FlaggedPoint where
  main := main
  elaborated := elaborated
  Assumptions := Assumptions
  Spec := Spec
  soundness := soundness
  completeness := completeness

end AssertInfinity

#check AssertInfinity.circuit

def outputFromValidated (Q : Var FlaggedPoint (F circomPrime))
    (pv : Var PointValid.Outputs (F circomPrime)) :
    Var ScalarMul.Outputs (F circomPrime) :=
  {
    x := pv.x.reverse
    y := pv.y.reverse
    isInf := Q.isInf
  }

def opChain
    (q pv c u1 u2 v1 v2 reduce rel table msm inf : Operations (F circomPrime)) :
    Operations (F circomPrime) :=
  q ++ (pv ++ (c ++ (u1 ++ (u2 ++ (v1 ++ (v2 ++ (reduce ++
    (rel ++ (table ++ (msm ++ inf))))))))))

def pvOffset (i₀ : ℕ) : ℕ := i₀ + 9
def coeffOffset (i₀ : ℕ) : ℕ := pvOffset i₀ + 1046
def shortOffset (i₀ : ℕ) : ℕ := coeffOffset i₀ + 260
def relationOffset (i₀ : ℕ) : ℕ := shortOffset i₀ + 0
def tableOffset (i₀ : ℕ) : ℕ := relationOffset i₀ + 865
def msmOffset (i₀ : ℕ) : ℕ := tableOffset i₀ + 16366
def outOffset (i₀ : ℕ) : ℕ := msmOffset i₀ + 103012

def qCircuit (input : Var ScalarMul.Inputs (F circomPrime)) :
    Circuit (F circomPrime) (Var FlaggedPoint (F circomPrime)) :=
  ProvableType.witness (F := F circomPrime) (α := FlaggedPoint)
    (resultWitness input)

def qVar (input : Var ScalarMul.Inputs (F circomPrime)) (i₀ : ℕ) :
    Var FlaggedPoint (F circomPrime) :=
  (qCircuit input).output i₀

def pointValidCircuit (input : Var ScalarMul.Inputs (F circomPrime)) (i₀ : ℕ) :
    Circuit (F circomPrime) (Var PointValid.Outputs (F circomPrime)) :=
  PointValid.circuit (qVar input i₀)

noncomputable def coeffCircuit (input : Var ScalarMul.Inputs (F circomPrime)) :
    Circuit (F circomPrime) (Var GLV.Coefficients (F circomPrime)) :=
  ProvableType.witness (F := F circomPrime) (α := GLV.Coefficients)
    (coefficientWitness input)

noncomputable def coeffVar (input : Var ScalarMul.Inputs (F circomPrime)) (i₀ : ℕ) :
    Var GLV.Coefficients (F circomPrime) :=
  (coeffCircuit input).output (coeffOffset i₀)

noncomputable def u1Circuit
    (input : Var ScalarMul.Inputs (F circomPrime)) (i₀ : ℕ) :=
  GLV.circuitZ (coeffVar input i₀).u1

noncomputable def u2Circuit
    (input : Var ScalarMul.Inputs (F circomPrime)) (i₀ : ℕ) :=
  GLV.circuit (coeffVar input i₀).u2

noncomputable def v1Circuit
    (input : Var ScalarMul.Inputs (F circomPrime)) (i₀ : ℕ) :=
  GLV.circuit (coeffVar input i₀).v1

noncomputable def v2Circuit
    (input : Var ScalarMul.Inputs (F circomPrime)) (i₀ : ℕ) :=
  GLV.circuit (coeffVar input i₀).v2

def reduceCircuit (input : Var ScalarMul.Inputs (F circomPrime)) :
    Circuit (F circomPrime) (Var Emu (F circomPrime)) :=
  subcircuit GLV.ScalarReduce.circuit { bits := input.bits }

def reduceVar (input : Var ScalarMul.Inputs (F circomPrime)) (i₀ : ℕ) :
    Var Emu (F circomPrime) :=
  (reduceCircuit input).output (shortOffset i₀)

noncomputable def relationCircuit
    (input : Var ScalarMul.Inputs (F circomPrime)) (i₀ : ℕ) :=
  GLVScalarRelation.circuit
    { s := reduceVar input i₀
      u1 := (coeffVar input i₀).u1
      u2 := (coeffVar input i₀).u2
      v1 := (coeffVar input i₀).v1
      v2 := (coeffVar input i₀).v2 }

noncomputable def tableCircuit
    (input : Var ScalarMul.Inputs (F circomPrime)) (i₀ : ℕ) :=
  subcircuit PatBuildTable.circuit
    { P := inputPointVar input
      Q := qVar input i₀
      sign0 := (coeffVar input i₀).u1.sign
      sign1 := (coeffVar input i₀).u2.sign
      sign2 := (coeffVar input i₀).v1.sign
      sign3 := (coeffVar input i₀).v2.sign }

noncomputable def tableVar
    (input : Var ScalarMul.Inputs (F circomPrime)) (i₀ : ℕ) :
    Var GLVBuildTable.Table (F circomPrime) :=
  (tableCircuit input i₀).output (tableOffset i₀)

noncomputable def msmCircuit
    (input : Var ScalarMul.Inputs (F circomPrime)) (i₀ : ℕ) :=
  LazyMSM.circuit
    { tx := (tableVar input i₀).tx
      ty := (tableVar input i₀).ty
      tinf := (tableVar input i₀).tinf
      m0 := (coeffVar input i₀).u1.bits
      m1 := (coeffVar input i₀).u2.bits
      m2 := (coeffVar input i₀).v1.bits
      m3 := (coeffVar input i₀).v2.bits }

noncomputable def infinityCircuit
    (input : Var ScalarMul.Inputs (F circomPrime)) (i₀ : ℕ) :=
  (pure () : Circuit (F circomPrime) Unit)

def mainOutput (input : Var ScalarMul.Inputs (F circomPrime)) (i₀ : ℕ) :
    Var ScalarMul.Outputs (F circomPrime) :=
  outputFromValidated (qVar input i₀)
    ((pointValidCircuit input i₀).output (pvOffset i₀))

noncomputable def mainOperations (input : Var ScalarMul.Inputs (F circomPrime)) (i₀ : ℕ) :
    Operations (F circomPrime) :=
  opChain ((qCircuit input).operations i₀)
    ((pointValidCircuit input i₀).operations (pvOffset i₀))
    ((coeffCircuit input).operations (coeffOffset i₀))
    ((u1Circuit input i₀).operations (shortOffset i₀))
    ((u2Circuit input i₀).operations (shortOffset i₀))
    ((v1Circuit input i₀).operations (shortOffset i₀))
    ((v2Circuit input i₀).operations (shortOffset i₀))
    ((reduceCircuit input).operations (shortOffset i₀))
    ((relationCircuit input i₀).operations (relationOffset i₀))
    ((tableCircuit input i₀).operations (tableOffset i₀))
    ((msmCircuit input i₀).operations (msmOffset i₀))
    ((infinityCircuit input i₀).operations (outOffset i₀))

noncomputable def main (input : Var ScalarMul.Inputs (F circomPrime)) :
    Circuit (F circomPrime) (Var ScalarMul.Outputs (F circomPrime)) := fun i₀ =>
  (mainOutput input i₀, mainOperations input i₀)

private theorem subcircuitsConsistent_append
    {ops ops' : Operations (F circomPrime)} {offset : ℕ}
    (h : ops.SubcircuitsConsistent offset)
    (h' : ops'.SubcircuitsConsistent (ops.localLength + offset)) :
    (ops ++ ops').SubcircuitsConsistent offset := by
  rw [Operations.SubcircuitsConsistent, Operations.forAll_append]
  exact ⟨h, h'⟩

private theorem subcircuitsConsistent_append_eq
    {ops ops' : Operations (F circomPrime)} {offset next : ℕ}
    (hLen : ops.localLength + offset = next)
    (h : ops.SubcircuitsConsistent offset)
    (h' : ops'.SubcircuitsConsistent next) :
    (ops ++ ops').SubcircuitsConsistent offset := by
  apply subcircuitsConsistent_append h
  simpa only [hLen] using h'

private theorem opChain_subcircuitsConsistent
    {q pv c u1 u2 v1 v2 reduce rel table msm inf : Operations (F circomPrime)}
    {offset iPV iC iShort iRel iTable iMSM iOut : ℕ}
    (hqLen : q.localLength + offset = iPV)
    (hpvLen : pv.localLength + iPV = iC)
    (hcLen : c.localLength + iC = iShort)
    (hu1Len : u1.localLength + iShort = iShort)
    (hu2Len : u2.localLength + iShort = iShort)
    (hv1Len : v1.localLength + iShort = iShort)
    (hv2Len : v2.localLength + iShort = iShort)
    (hreduceLen : reduce.localLength + iShort = iRel)
    (hrelLen : rel.localLength + iRel = iTable)
    (htabLen : table.localLength + iTable = iMSM)
    (hmsmLen : msm.localLength + iMSM = iOut)
    (hq : q.SubcircuitsConsistent offset)
    (hpv : pv.SubcircuitsConsistent iPV)
    (hc : c.SubcircuitsConsistent iC)
    (hu1 : u1.SubcircuitsConsistent iShort)
    (hu2 : u2.SubcircuitsConsistent iShort)
    (hv1 : v1.SubcircuitsConsistent iShort)
    (hv2 : v2.SubcircuitsConsistent iShort)
    (hreduce : reduce.SubcircuitsConsistent iShort)
    (hrel : rel.SubcircuitsConsistent iRel)
    (htab : table.SubcircuitsConsistent iTable)
    (hmsm : msm.SubcircuitsConsistent iMSM)
    (hinf : inf.SubcircuitsConsistent iOut) :
    (opChain q pv c u1 u2 v1 v2 reduce rel table msm inf).SubcircuitsConsistent offset := by
  unfold opChain
  refine subcircuitsConsistent_append_eq hqLen hq ?_
  refine subcircuitsConsistent_append_eq hpvLen hpv ?_
  refine subcircuitsConsistent_append_eq hcLen hc ?_
  refine subcircuitsConsistent_append_eq hu1Len hu1 ?_
  refine subcircuitsConsistent_append_eq hu2Len hu2 ?_
  refine subcircuitsConsistent_append_eq hv1Len hv1 ?_
  refine subcircuitsConsistent_append_eq hv2Len hv2 ?_
  refine subcircuitsConsistent_append_eq hreduceLen hreduce ?_
  refine subcircuitsConsistent_append_eq hrelLen hrel ?_
  refine subcircuitsConsistent_append_eq htabLen htab ?_
  exact subcircuitsConsistent_append_eq hmsmLen hmsm hinf

private theorem provableWitness_subcircuitsConsistent
    {α : TypeMap} [ProvableType α]
    (compute : ProverEnvironment (F circomPrime) → α (F circomPrime))
    (offset : ℕ) :
    Operations.SubcircuitsConsistent offset
      ((ProvableType.witness (F := F circomPrime) (α := α) compute).operations offset) := by
  simp only [Circuit.operations, ProvableType.witness,
    Operations.SubcircuitsConsistent, Operations.forAll, true_and]

private theorem formalCircuitCall_subcircuitsConsistent
    {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (circuit : FormalCircuit (F circomPrime) Input Output)
    (input : Var Input (F circomPrime)) (offset : ℕ) :
    ((circuit input).operations offset).SubcircuitsConsistent offset := by
  change ((subcircuit circuit input).operations offset).SubcircuitsConsistent offset
  simp only [Circuit.operations, subcircuit, Operations.SubcircuitsConsistent,
    Operations.forAll, true_and]

private theorem generalFormalCircuitCall_subcircuitsConsistent
    {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (F circomPrime) Input Output)
    (input : Var Input (F circomPrime)) (offset : ℕ) :
    ((circuit input).operations offset).SubcircuitsConsistent offset := by
  change Operations.SubcircuitsConsistent offset
    ((subcircuitWithAssertion circuit input).operations offset)
  simp only [Circuit.operations, subcircuitWithAssertion,
    Operations.SubcircuitsConsistent, Operations.forAll, true_and]

private theorem formalAssertionCall_subcircuitsConsistent
    {Input : TypeMap} [ProvableType Input]
    (circuit : FormalAssertion (F circomPrime) Input)
    (input : Var Input (F circomPrime)) (offset : ℕ) :
    ((circuit input).operations offset).SubcircuitsConsistent offset := by
  change ((assertion circuit input).operations offset).SubcircuitsConsistent offset
  simp only [Circuit.operations, assertion, Operations.SubcircuitsConsistent,
    Operations.forAll, true_and]

private theorem provableWitness_localLength
    {α : TypeMap} [ProvableType α]
    (compute : ProverEnvironment (F circomPrime) → α (F circomPrime))
    (offset : ℕ) :
    Operations.localLength
      ((ProvableType.witness (F := F circomPrime) (α := α) compute).operations offset) =
        size α := by
  rfl

private theorem formalCircuitCall_localLength
    {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (circuit : FormalCircuit (F circomPrime) Input Output)
    (input : Var Input (F circomPrime)) (offset : ℕ) :
    ((circuit input).operations offset).localLength = circuit.localLength input := by
  change ((subcircuit circuit input).operations offset).localLength =
    circuit.localLength input
  rfl

private theorem generalFormalCircuitCall_localLength
    {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (F circomPrime) Input Output)
    (input : Var Input (F circomPrime)) (offset : ℕ) :
    ((circuit input).operations offset).localLength = circuit.localLength input := by
  change ((subcircuitWithAssertion circuit input).operations offset).localLength =
    circuit.localLength input
  rfl

private theorem formalAssertionCall_localLength
    {Input : TypeMap} [ProvableType Input]
    (circuit : FormalAssertion (F circomPrime) Input)
    (input : Var Input (F circomPrime)) (offset : ℕ) :
    ((circuit input).operations offset).localLength = circuit.localLength input := by
  change ((assertion circuit input).operations offset).localLength =
    circuit.localLength input
  rfl

open Challenge.CostR1CS in
private theorem flatOperation_localLength_append
    (xs ys : List (FlatOperation (F circomPrime))) :
    FlatOperation.localLength (xs ++ ys) =
      FlatOperation.localLength xs + FlatOperation.localLength ys := by
  induction xs using FlatOperation.induct with
  | empty => simp only [List.nil_append, FlatOperation.localLength, Nat.zero_add]
  | witness m c ops ih | assert c ops ih | lookup c ops ih | interact c ops ih =>
      simp only [List.cons_append, FlatOperation.localLength, ih, Nat.add_assoc]

open Challenge.CostR1CS in
mutual
  private theorem nestedCount_allocations_eq_localLength
      (op : NestedOperations (F circomPrime)) :
      (nestedCount op).allocations = FlatOperation.localLength op.toFlat := by
    cases op with
    | single op =>
        cases op <;> simp only [nestedCount, NestedOperations.toFlat,
          flatOperationCount, FlatOperation.localLength, Count.add_allocations,
          Count.zero, Nat.add_zero, Nat.add_zero]
    | nested p =>
        cases p with
        | mk _ ops =>
            simpa only [nestedCount, NestedOperations.toFlat] using
              nestedListCount_allocations_eq_localLength ops

  private theorem nestedListCount_allocations_eq_localLength
      (ops : List (NestedOperations (F circomPrime))) :
      (nestedListCount ops).allocations =
        FlatOperation.localLength (ops.flatMap NestedOperations.toFlat) := by
    cases ops with
    | nil => rfl
    | cons op ops =>
        simp only [nestedListCount, Count.add_allocations, List.flatMap_cons,
          flatOperation_localLength_append,
          nestedCount_allocations_eq_localLength op,
          nestedListCount_allocations_eq_localLength ops]
end

open Challenge.CostR1CS in
private theorem operationCount_allocations_eq_localLength
    (ops : Operations (F circomPrime)) :
    (operationCount ops).allocations = ops.localLength := by
  induction ops using Operations.induct with
  | empty => rfl
  | witness m c ops ih =>
      simp only [operationCount, Operations.localLength, Count.add_allocations,
        flatOperationCount, ih]
  | assert e ops ih | lookup e ops ih | interact e ops ih =>
      simp only [operationCount, Operations.localLength, Count.add_allocations,
        flatOperationCount, Count.zero, ih, Nat.zero_add]
  | subcircuit s ops ih =>
      simp only [operationCount, Operations.localLength, Count.add_allocations, ih]
      rw [nestedCount_allocations_eq_localLength s.ops, ← s.localLength_eq]

open Challenge.CostR1CS in
private theorem costIs_localLength
    {α : Type} {c : Circuit (F circomPrime) α} {K : Count}
    (h : CostIs c K) (offset : ℕ) :
    c.localLength offset = K.allocations := by
  change Operations.localLength (c.operations offset) = K.allocations
  rw [← operationCount_allocations_eq_localLength (c.operations offset), h offset]

private theorem glvScalarRelation_localLength
    (input : Var GLVScalarRelation.Inputs (F circomPrime)) :
    GLVScalarRelation.circuit.localLength input = 865 := by
  have h := costIs_localLength (GLVScalarRelation.costIs_main input) 0
  rw [← GLVScalarRelation.circuit.localLength_eq input 0]
  simpa only [GLVScalarRelation.relationCost] using h

theorem patBuildTable_localLength
    (input : Var GLVBuildTable.Inputs (F circomPrime)) :
    PatBuildTable.circuit.localLength input = 16366 :=
  PatBuildTable.localLength input

theorem lazyMSM_localLength
    (input : Var GLVMSM.Inputs (F circomPrime)) :
    LazyMSM.circuit.localLength input = 103012 :=
  LazyMSM.circuit_localLength input

private theorem opChain_localLength
    {q pv c u1 u2 v1 v2 reduce rel table msm inf : Operations (F circomPrime)}
    (hq : q.localLength = 9)
    (hpv : pv.localLength = 1046)
    (hc : c.localLength = 260)
    (hu1 : u1.localLength = 0)
    (hu2 : u2.localLength = 0)
    (hv1 : v1.localLength = 0)
    (hv2 : v2.localLength = 0)
    (hreduce : reduce.localLength = 0)
    (hrel : rel.localLength = 865)
    (htable : table.localLength = 16366)
    (hmsm : msm.localLength = 103012)
    (hinf : inf.localLength = 0) :
    (opChain q pv c u1 u2 v1 v2 reduce rel table msm inf).localLength = 121558 := by
  unfold opChain
  simp only [Operations.append_localLength, hq, hpv, hc, hu1, hu2, hv1, hv2,
    hreduce, hrel, htable, hmsm, hinf]

theorem qCircuit_localLength
    (input : Var ScalarMul.Inputs (F circomPrime)) (offset : ℕ) :
    ((qCircuit input).operations offset).localLength = 9 := by
  simpa only [qCircuit, numLimbs, Nat.reduceAdd] using
    provableWitness_localLength (resultWitness input) offset

theorem pointValidCircuit_localLength
    (input : Var ScalarMul.Inputs (F circomPrime)) (offset : ℕ) :
    ((pointValidCircuit input offset).operations (pvOffset offset)).localLength = 1046 := by
  simpa only [pointValidCircuit] using
    (generalFormalCircuitCall_localLength PointValid.circuit (qVar input offset)
      (pvOffset offset)).trans rfl

theorem coeffCircuit_localLength
    (input : Var ScalarMul.Inputs (F circomPrime)) (offset : ℕ) :
    ((coeffCircuit input).operations (coeffOffset offset)).localLength = 260 := by
  simpa only [coeffCircuit, GLV.coeffBits, Nat.reduceAdd] using
    provableWitness_localLength (coefficientWitness input) (coeffOffset offset)

theorem u1Circuit_localLength
    (input : Var ScalarMul.Inputs (F circomPrime)) (offset : ℕ) :
    ((u1Circuit input offset).operations (shortOffset offset)).localLength = 0 := by
  simpa only [u1Circuit] using
    (formalAssertionCall_localLength GLV.circuitZ (coeffVar input offset).u1
      (shortOffset offset)).trans rfl

theorem u2Circuit_localLength
    (input : Var ScalarMul.Inputs (F circomPrime)) (offset : ℕ) :
    ((u2Circuit input offset).operations (shortOffset offset)).localLength = 0 := by
  simpa only [u2Circuit] using
    (formalAssertionCall_localLength GLV.circuit (coeffVar input offset).u2
      (shortOffset offset)).trans rfl

theorem v1Circuit_localLength
    (input : Var ScalarMul.Inputs (F circomPrime)) (offset : ℕ) :
    ((v1Circuit input offset).operations (shortOffset offset)).localLength = 0 := by
  simpa only [v1Circuit] using
    (formalAssertionCall_localLength GLV.circuit (coeffVar input offset).v1
      (shortOffset offset)).trans rfl

theorem v2Circuit_localLength
    (input : Var ScalarMul.Inputs (F circomPrime)) (offset : ℕ) :
    ((v2Circuit input offset).operations (shortOffset offset)).localLength = 0 := by
  simpa only [v2Circuit] using
    (formalAssertionCall_localLength GLV.circuit (coeffVar input offset).v2
      (shortOffset offset)).trans rfl

theorem reduceCircuit_localLength
    (input : Var ScalarMul.Inputs (F circomPrime)) (offset : ℕ) :
    ((reduceCircuit input).operations (shortOffset offset)).localLength = 0 := by
  simpa only [reduceCircuit] using
    (formalCircuitCall_localLength GLV.ScalarReduce.circuit { bits := input.bits }
      (shortOffset offset)).trans rfl

theorem relationCircuit_localLength
    (input : Var ScalarMul.Inputs (F circomPrime)) (offset : ℕ) :
    ((relationCircuit input offset).operations (relationOffset offset)).localLength = 865 := by
  simpa only [relationCircuit] using
    (formalAssertionCall_localLength GLVScalarRelation.circuit
      { s := reduceVar input offset
        u1 := (coeffVar input offset).u1
        u2 := (coeffVar input offset).u2
        v1 := (coeffVar input offset).v1
        v2 := (coeffVar input offset).v2 } (relationOffset offset)).trans
      (glvScalarRelation_localLength _)

theorem tableCircuit_localLength
    (input : Var ScalarMul.Inputs (F circomPrime)) (offset : ℕ) :
    ((tableCircuit input offset).operations (tableOffset offset)).localLength = 16366 := by
  simpa only [tableCircuit] using
    (formalCircuitCall_localLength PatBuildTable.circuit
      { P := inputPointVar input
        Q := qVar input offset
        sign0 := (coeffVar input offset).u1.sign
        sign1 := (coeffVar input offset).u2.sign
        sign2 := (coeffVar input offset).v1.sign
        sign3 := (coeffVar input offset).v2.sign } (tableOffset offset)).trans
      (patBuildTable_localLength _)

theorem msmCircuit_localLength
    (input : Var ScalarMul.Inputs (F circomPrime)) (offset : ℕ) :
    ((msmCircuit input offset).operations (msmOffset offset)).localLength = 103012 := by
  simpa only [msmCircuit] using
    (generalFormalCircuitCall_localLength LazyMSM.circuit
      { tx := (tableVar input offset).tx
        ty := (tableVar input offset).ty
        tinf := (tableVar input offset).tinf
        m0 := (coeffVar input offset).u1.bits
        m1 := (coeffVar input offset).u2.bits
        m2 := (coeffVar input offset).v1.bits
        m3 := (coeffVar input offset).v2.bits } (msmOffset offset)).trans
      (lazyMSM_localLength _)

theorem infinityCircuit_localLength
    (input : Var ScalarMul.Inputs (F circomPrime)) (offset : ℕ) :
    ((infinityCircuit input offset).operations (outOffset offset)).localLength = 0 := by
  simp only [infinityCircuit, Circuit.pure_operations_eq, Operations.localLength]

private theorem mainOperationsLocalLengthEq
    (input : Var ScalarMul.Inputs (F circomPrime)) (offset : ℕ) :
    (mainOperations input offset).localLength = 121558 := by
  change
    (opChain ((qCircuit input).operations offset)
      ((pointValidCircuit input offset).operations (pvOffset offset))
      ((coeffCircuit input).operations (coeffOffset offset))
      ((u1Circuit input offset).operations (shortOffset offset))
      ((u2Circuit input offset).operations (shortOffset offset))
      ((v1Circuit input offset).operations (shortOffset offset))
      ((v2Circuit input offset).operations (shortOffset offset))
      ((reduceCircuit input).operations (shortOffset offset))
      ((relationCircuit input offset).operations (relationOffset offset))
      ((tableCircuit input offset).operations (tableOffset offset))
      ((msmCircuit input offset).operations (msmOffset offset))
      ((infinityCircuit input offset).operations (outOffset offset))).localLength = 121558
  exact opChain_localLength
    (qCircuit_localLength input offset)
    (pointValidCircuit_localLength input offset)
    (coeffCircuit_localLength input offset)
    (u1Circuit_localLength input offset)
    (u2Circuit_localLength input offset)
    (v1Circuit_localLength input offset)
    (v2Circuit_localLength input offset)
    (reduceCircuit_localLength input offset)
    (relationCircuit_localLength input offset)
    (tableCircuit_localLength input offset)
    (msmCircuit_localLength input offset)
    (infinityCircuit_localLength input offset)

private theorem elaboratedLocalLengthEq
    (input : Var ScalarMul.Inputs (F circomPrime)) (offset : ℕ) :
    (main input).localLength offset = 121558 := by
  change (mainOperations input offset).localLength = 121558
  exact mainOperationsLocalLengthEq input offset

private theorem qCircuit_subcircuitsConsistent
    (input : Var ScalarMul.Inputs (F circomPrime)) (offset : ℕ) :
    ((qCircuit input).operations offset).SubcircuitsConsistent offset := by
  simpa only [qCircuit] using
    provableWitness_subcircuitsConsistent (resultWitness input) offset

private theorem pointValidCircuit_subcircuitsConsistent
    (input : Var ScalarMul.Inputs (F circomPrime)) (offset : ℕ) :
    ((pointValidCircuit input offset).operations (pvOffset offset)).SubcircuitsConsistent
      (pvOffset offset) := by
  simpa only [pointValidCircuit] using
    generalFormalCircuitCall_subcircuitsConsistent PointValid.circuit (qVar input offset)
      (pvOffset offset)

private theorem coeffCircuit_subcircuitsConsistent
    (input : Var ScalarMul.Inputs (F circomPrime)) (offset : ℕ) :
    ((coeffCircuit input).operations (coeffOffset offset)).SubcircuitsConsistent
      (coeffOffset offset) := by
  simpa only [coeffCircuit] using
    provableWitness_subcircuitsConsistent (coefficientWitness input) (coeffOffset offset)

private theorem u1Circuit_subcircuitsConsistent
    (input : Var ScalarMul.Inputs (F circomPrime)) (offset : ℕ) :
    ((u1Circuit input offset).operations (shortOffset offset)).SubcircuitsConsistent
      (shortOffset offset) := by
  simpa only [u1Circuit] using
    formalAssertionCall_subcircuitsConsistent GLV.circuitZ (coeffVar input offset).u1
      (shortOffset offset)

private theorem u2Circuit_subcircuitsConsistent
    (input : Var ScalarMul.Inputs (F circomPrime)) (offset : ℕ) :
    ((u2Circuit input offset).operations (shortOffset offset)).SubcircuitsConsistent
      (shortOffset offset) := by
  simpa only [u2Circuit] using
    formalAssertionCall_subcircuitsConsistent GLV.circuit (coeffVar input offset).u2
      (shortOffset offset)

private theorem v1Circuit_subcircuitsConsistent
    (input : Var ScalarMul.Inputs (F circomPrime)) (offset : ℕ) :
    ((v1Circuit input offset).operations (shortOffset offset)).SubcircuitsConsistent
      (shortOffset offset) := by
  simpa only [v1Circuit] using
    formalAssertionCall_subcircuitsConsistent GLV.circuit (coeffVar input offset).v1
      (shortOffset offset)

private theorem v2Circuit_subcircuitsConsistent
    (input : Var ScalarMul.Inputs (F circomPrime)) (offset : ℕ) :
    ((v2Circuit input offset).operations (shortOffset offset)).SubcircuitsConsistent
      (shortOffset offset) := by
  simpa only [v2Circuit] using
    formalAssertionCall_subcircuitsConsistent GLV.circuit (coeffVar input offset).v2
      (shortOffset offset)

private theorem reduceCircuit_subcircuitsConsistent
    (input : Var ScalarMul.Inputs (F circomPrime)) (offset : ℕ) :
    ((reduceCircuit input).operations (shortOffset offset)).SubcircuitsConsistent
      (shortOffset offset) := by
  simpa only [reduceCircuit] using
    formalCircuitCall_subcircuitsConsistent GLV.ScalarReduce.circuit { bits := input.bits }
      (shortOffset offset)

private theorem relationCircuit_subcircuitsConsistent
    (input : Var ScalarMul.Inputs (F circomPrime)) (offset : ℕ) :
    ((relationCircuit input offset).operations (relationOffset offset)).SubcircuitsConsistent
      (relationOffset offset) := by
  simpa only [relationCircuit] using
    formalAssertionCall_subcircuitsConsistent GLVScalarRelation.circuit
      { s := reduceVar input offset
        u1 := (coeffVar input offset).u1
        u2 := (coeffVar input offset).u2
        v1 := (coeffVar input offset).v1
        v2 := (coeffVar input offset).v2 } (relationOffset offset)

private theorem tableCircuit_subcircuitsConsistent
    (input : Var ScalarMul.Inputs (F circomPrime)) (offset : ℕ) :
    ((tableCircuit input offset).operations (tableOffset offset)).SubcircuitsConsistent
      (tableOffset offset) := by
  simpa only [tableCircuit] using
    formalCircuitCall_subcircuitsConsistent PatBuildTable.circuit
      { P := inputPointVar input
        Q := qVar input offset
        sign0 := (coeffVar input offset).u1.sign
        sign1 := (coeffVar input offset).u2.sign
        sign2 := (coeffVar input offset).v1.sign
        sign3 := (coeffVar input offset).v2.sign } (tableOffset offset)

private theorem msmCircuit_subcircuitsConsistent
    (input : Var ScalarMul.Inputs (F circomPrime)) (offset : ℕ) :
    ((msmCircuit input offset).operations (msmOffset offset)).SubcircuitsConsistent
      (msmOffset offset) := by
  simpa only [msmCircuit] using
    generalFormalCircuitCall_subcircuitsConsistent LazyMSM.circuit
      { tx := (tableVar input offset).tx
        ty := (tableVar input offset).ty
        tinf := (tableVar input offset).tinf
        m0 := (coeffVar input offset).u1.bits
        m1 := (coeffVar input offset).u2.bits
        m2 := (coeffVar input offset).v1.bits
        m3 := (coeffVar input offset).v2.bits } (msmOffset offset)

private theorem infinityCircuit_subcircuitsConsistent
    (input : Var ScalarMul.Inputs (F circomPrime)) (offset : ℕ) :
    ((infinityCircuit input offset).operations (outOffset offset)).SubcircuitsConsistent
      (outOffset offset) := by
  simp only [infinityCircuit, Circuit.pure_operations_eq, Operations.SubcircuitsConsistent,
    Operations.forAll_empty]

theorem qCircuit_next
    (input : Var ScalarMul.Inputs (F circomPrime)) (offset : ℕ) :
    ((qCircuit input).operations offset).localLength + offset = pvOffset offset := by
  rw [qCircuit_localLength]
  simp only [pvOffset]
  omega

theorem pointValidCircuit_next
    (input : Var ScalarMul.Inputs (F circomPrime)) (offset : ℕ) :
    ((pointValidCircuit input offset).operations (pvOffset offset)).localLength +
      pvOffset offset = coeffOffset offset := by
  rw [pointValidCircuit_localLength]
  simp only [pvOffset, coeffOffset]
  omega

theorem coeffCircuit_next
    (input : Var ScalarMul.Inputs (F circomPrime)) (offset : ℕ) :
    ((coeffCircuit input).operations (coeffOffset offset)).localLength +
      coeffOffset offset = shortOffset offset := by
  rw [coeffCircuit_localLength]
  simp only [shortOffset, coeffOffset, pvOffset]
  omega

theorem zeroLength_next
    {ops : Operations (F circomPrime)} {offset : ℕ}
    (h : ops.localLength = 0) : ops.localLength + offset = offset := by
  rw [h]
  omega

theorem reduceCircuit_next
    (input : Var ScalarMul.Inputs (F circomPrime)) (offset : ℕ) :
    ((reduceCircuit input).operations (shortOffset offset)).localLength +
      shortOffset offset = relationOffset offset := by
  rw [reduceCircuit_localLength]
  simp only [relationOffset, shortOffset, coeffOffset, pvOffset]
  omega

theorem relationCircuit_next
    (input : Var ScalarMul.Inputs (F circomPrime)) (offset : ℕ) :
    ((relationCircuit input offset).operations (relationOffset offset)).localLength +
      relationOffset offset = tableOffset offset := by
  rw [relationCircuit_localLength]
  simp only [tableOffset, relationOffset, shortOffset, coeffOffset, pvOffset]
  omega

theorem tableCircuit_next
    (input : Var ScalarMul.Inputs (F circomPrime)) (offset : ℕ) :
    ((tableCircuit input offset).operations (tableOffset offset)).localLength +
      tableOffset offset = msmOffset offset := by
  rw [tableCircuit_localLength]
  simp only [msmOffset, tableOffset, relationOffset, shortOffset, coeffOffset, pvOffset]
  omega

theorem msmCircuit_next
    (input : Var ScalarMul.Inputs (F circomPrime)) (offset : ℕ) :
    ((msmCircuit input offset).operations (msmOffset offset)).localLength +
      msmOffset offset = outOffset offset := by
  rw [msmCircuit_localLength]
  simp only [outOffset, msmOffset, tableOffset, relationOffset, shortOffset, coeffOffset, pvOffset]
  omega

set_option maxRecDepth 10000000 in
private theorem elaboratedSubcircuitsConsistent
    (input : Var ScalarMul.Inputs (F circomPrime)) (offset : ℕ) :
    (mainOperations input offset).SubcircuitsConsistent offset := by
  change
    (opChain ((qCircuit input).operations offset)
      ((pointValidCircuit input offset).operations (pvOffset offset))
      ((coeffCircuit input).operations (coeffOffset offset))
      ((u1Circuit input offset).operations (shortOffset offset))
      ((u2Circuit input offset).operations (shortOffset offset))
      ((v1Circuit input offset).operations (shortOffset offset))
      ((v2Circuit input offset).operations (shortOffset offset))
      ((reduceCircuit input).operations (shortOffset offset))
      ((relationCircuit input offset).operations (relationOffset offset))
      ((tableCircuit input offset).operations (tableOffset offset))
      ((msmCircuit input offset).operations (msmOffset offset))
      ((infinityCircuit input offset).operations (outOffset offset))).SubcircuitsConsistent offset
  exact opChain_subcircuitsConsistent
    (qCircuit_next input offset)
    (pointValidCircuit_next input offset)
    (coeffCircuit_next input offset)
    (zeroLength_next (u1Circuit_localLength input offset))
    (zeroLength_next (u2Circuit_localLength input offset))
    (zeroLength_next (v1Circuit_localLength input offset))
    (zeroLength_next (v2Circuit_localLength input offset))
    (reduceCircuit_next input offset)
    (relationCircuit_next input offset)
    (tableCircuit_next input offset)
    (msmCircuit_next input offset)
    (qCircuit_subcircuitsConsistent input offset)
    (pointValidCircuit_subcircuitsConsistent input offset)
    (coeffCircuit_subcircuitsConsistent input offset)
    (u1Circuit_subcircuitsConsistent input offset)
    (u2Circuit_subcircuitsConsistent input offset)
    (v1Circuit_subcircuitsConsistent input offset)
    (v2Circuit_subcircuitsConsistent input offset)
    (reduceCircuit_subcircuitsConsistent input offset)
    (relationCircuit_subcircuitsConsistent input offset)
    (tableCircuit_subcircuitsConsistent input offset)
    (msmCircuit_subcircuitsConsistent input offset)
    (infinityCircuit_subcircuitsConsistent input offset)

theorem elaboratedChannelsLawful :
    ElaboratedCircuit.ChannelsLawful main [] [] := by
  intro input offset
  have hpvg : PointValid.circuit.channelsWithGuarantees = [] := rfl
  have hpvr : PointValid.circuit.channelsWithRequirements = [] := rfl
  have hcg : GLV.circuit.channelsWithGuarantees = [] := rfl
  have hcr : GLV.circuit.channelsWithRequirements = [] := rfl
  have hcgZ : GLV.circuitZ.channelsWithGuarantees = [] := rfl
  have hcrZ : GLV.circuitZ.channelsWithRequirements = [] := rfl
  have hsrg : GLV.ScalarReduce.circuit.channelsWithGuarantees = [] := rfl
  have hsrr : GLV.ScalarReduce.circuit.channelsWithRequirements = [] := rfl
  have hrelg : GLVScalarRelation.circuit.channelsWithGuarantees = [] := rfl
  have hrelr : GLVScalarRelation.circuit.channelsWithRequirements = [] := rfl
  have htabg : PatBuildTable.circuit.channelsWithGuarantees = [] := rfl
  have htabr : PatBuildTable.circuit.channelsWithRequirements = [] := rfl
  have hmsmg : LazyMSM.circuit.channelsWithGuarantees = [] := rfl
  have hmsmr : LazyMSM.circuit.channelsWithRequirements = [] := rfl
  simp only [main, mainOperations, mainOutput, opChain,
    qCircuit, qVar, pointValidCircuit, coeffCircuit, coeffVar,
    u1Circuit, u2Circuit, v1Circuit, v2Circuit, reduceCircuit, reduceVar,
    relationCircuit, tableCircuit, tableVar, msmCircuit, infinityCircuit,
    pvOffset, coeffOffset, shortOffset, relationOffset, tableOffset, msmOffset, outOffset,
    circuit_norm, seval, hpvg, hpvr, hcg, hcr, hcgZ, hcrZ, hsrg, hsrr,
    hrelg, hrelr, htabg, htabr, hmsmg, hmsmr]

noncomputable instance elaborated :
    ElaboratedCircuit (F circomPrime) ScalarMul.Inputs ScalarMul.Outputs main where
  localLength _ := 121558
  localLength_eq := elaboratedLocalLengthEq
  output _ i₀ :=
    outputFromValidated
      (varFromOffset FlaggedPoint i₀)
      (PointValid.circuit.output (varFromOffset FlaggedPoint i₀) (i₀ + 9))
  output_eq := by
    intro input i₀
    unfold main
    rfl
  subcircuitsConsistent := by
    intro input offset
    change (mainOperations input offset).SubcircuitsConsistent offset
    exact elaboratedSubcircuitsConsistent input offset
  channelsLawful := elaboratedChannelsLawful

def Assumptions := ScalarMul.Assumptions

def Spec := ScalarMul.Spec

lemma patBuildTableSpec_changeInput
    {a b : GLVBuildTable.Inputs (F circomPrime)}
    {out : GLVBuildTable.Table (F circomPrime)}
    (hs : PatBuildTable.Spec a out) (h : a = b) :
    PatBuildTable.Spec b out := by
  rw [← h]
  exact hs

private def MainHolds (env : ProverEnvironment (F circomPrime)) (i₀ : ℕ)
    (input : Var ScalarMul.Inputs (F circomPrime)) : Prop :=
  let Qv : Var FlaggedPoint (F circomPrime) := varFromOffset FlaggedPoint i₀
  let cv : Var GLV.Coefficients (F circomPrime) :=
    varFromOffset GLV.Coefficients (i₀ + 9 + 1046)
  let sV := GLV.ScalarReduce.circuit.output { bits := input.bits }
    (i₀ + 9 + 1046 + 260)
  let tV := PatBuildTable.circuit.output
    { P := inputPointVar input, Q := Qv
      sign0 := cv.u1.sign, sign1 := cv.u2.sign
      sign2 := cv.v1.sign, sign3 := cv.v2.sign }
    (i₀ + 9 + 1046 + 260 + 0 + 865)
  let Q := eval env Qv
  let c := eval env cv
  let s := eval env sV
  let table := eval env tV
  (True ∧ PointValid.Spec Q) ∧
  (True ∧ GLV.ValidZ c.u1) ∧ (True ∧ GLV.Valid c.u2) ∧
  (True ∧ GLV.Valid c.v1) ∧ (True ∧ GLV.Valid c.v2) ∧
  GLV.ScalarReduce.Assumptions { bits := eval env input.bits } ∧
  (GLVScalarRelation.Assumptions
      { s, u1 := c.u1, u2 := c.u2, v1 := c.v1, v2 := c.v2 } ∧
    GLVScalarRelation.Spec
      { s, u1 := c.u1, u2 := c.u2, v1 := c.v1, v2 := c.v2 }) ∧
  PatBuildTable.Assumptions
    { P := eval env (inputPointVar input), Q
      sign0 := c.u1.sign, sign1 := c.u2.sign
      sign2 := c.v1.sign, sign3 := c.v2.sign } ∧
  (LazyMSM.ProverAssumptions
    { tx := table.tx, ty := table.ty, tinf := table.tinf
      m0 := c.u1.bits, m1 := c.u2.bits, m2 := c.v1.bits, m3 := c.v2.bits } ∧ True) ∧
  True

set_option maxRecDepth 65536 in
private theorem mainConstraints_shape
    (env : ProverEnvironment (F circomPrime)) (i₀ : ℕ)
    (input : Var ScalarMul.Inputs (F circomPrime)) :
    ConstraintsHold.Completeness env ((main input).operations i₀) ↔
      MainHolds env i₀ input := by
  have hPV : ∀ Q : Var FlaggedPoint (F circomPrime),
      PointValid.circuit.localLength Q = 1046 := fun _ => rfl
  have hSC : ∀ c : Var GLV.SignedCoeff (F circomPrime),
      GLV.circuit.localLength c = 0 := fun _ => rfl
  have hSCZ : ∀ c : Var GLV.SignedCoeff (F circomPrime),
      GLV.circuitZ.localLength c = 0 := fun _ => rfl
  have hSR : ∀ X : Var GLV.ScalarReduce.Inputs (F circomPrime),
      GLV.ScalarReduce.circuit.localLength X = 0 := fun _ => rfl
  have hRel : ∀ X : Var GLVScalarRelation.Inputs (F circomPrime),
      GLVScalarRelation.circuit.localLength X = 865 := fun _ => rfl
  have hTab : ∀ X : Var GLVBuildTable.Inputs (F circomPrime),
      PatBuildTable.circuit.localLength X = 16366 := patBuildTable_localLength
  have hMSM : ∀ X : Var GLVMSM.Inputs (F circomPrime),
      LazyMSM.circuit.localLength X = 103012 := lazyMSM_localLength
  simp only [MainHolds, main, mainOperations, mainOutput, opChain,
    qCircuit, qVar, pointValidCircuit, coeffCircuit, coeffVar,
    u1Circuit, u2Circuit, v1Circuit, v2Circuit, reduceCircuit, reduceVar,
    relationCircuit, tableCircuit, tableVar, msmCircuit, infinityCircuit,
    pvOffset, coeffOffset, shortOffset, relationOffset, tableOffset, msmOffset, outOffset,
    circuit_norm, hPV, hSC, hSCZ, hSR, hRel, hTab, hMSM,
    numLimbs, GLV.coeffBits, List.sum_cons, List.sum_nil, Nat.reduceAdd]
  simp only [PointValid.circuit, GLV.circuit, GLV.circuitZ, GLV.ScalarReduce.circuit,
    GLVScalarRelation.circuit, PatBuildTable.circuit, LazyMSM.circuit]
  simp only [PointValid.Assumptions, GLV.Assumptions, GLV.Spec, GLV.SpecZ,
    PointValid.ProverAssumptions, PointValid.ProverSpec,
    true_and, and_true]

#check mainConstraints_shape

theorem mainConstraints
    (env : ProverEnvironment (F circomPrime)) (i₀ : ℕ)
    (input_var : Var ScalarMul.Inputs (F circomPrime)) :
    let Qv : Var FlaggedPoint (F circomPrime) := varFromOffset FlaggedPoint i₀
    let cv : Var GLV.Coefficients (F circomPrime) :=
      varFromOffset GLV.Coefficients (i₀ + 9 + 1046)
    let sV := GLV.ScalarReduce.circuit.output { bits := input_var.bits }
      (i₀ + 9 + 1046 + 260)
    let tV := PatBuildTable.circuit.output
      { P := inputPointVar input_var, Q := Qv
        sign0 := cv.u1.sign, sign1 := cv.u2.sign
        sign2 := cv.v1.sign, sign3 := cv.v2.sign }
      (i₀ + 9 + 1046 + 260 + 0 + 865)
    let Q := eval env Qv
    let c := eval env cv
    let s := eval env sV
    let table := eval env tV
    PointValid.Spec Q →
    (GLV.ValidZ c.u1 ∧ GLV.Valid c.u2 ∧
      GLV.Valid c.v1 ∧ GLV.Valid c.v2) →
    GLV.ScalarReduce.Assumptions { bits := eval env input_var.bits } →
    (GLVScalarRelation.Assumptions
        { s, u1 := c.u1, u2 := c.u2, v1 := c.v1, v2 := c.v2 } ∧
      GLVScalarRelation.Spec
        { s, u1 := c.u1, u2 := c.u2, v1 := c.v1, v2 := c.v2 }) →
    PatBuildTable.Assumptions
      { P := eval env (inputPointVar input_var), Q
        sign0 := c.u1.sign, sign1 := c.u2.sign
        sign2 := c.v1.sign, sign3 := c.v2.sign } →
    LazyMSM.ProverAssumptions
      { tx := table.tx, ty := table.ty, tinf := table.tinf
        m0 := c.u1.bits, m1 := c.u2.bits, m2 := c.v1.bits, m3 := c.v2.bits } →
    ConstraintsHold.Completeness env ((main input_var).operations i₀) := by
  dsimp only
  intro hQ hc hs hr ht hm
  rw [mainConstraints_shape]
  simp only [MainHolds]
  exact ⟨⟨trivial, hQ⟩, ⟨trivial, hc.1⟩, ⟨trivial, hc.2.1⟩,
    ⟨trivial, hc.2.2.1⟩, ⟨trivial, hc.2.2.2⟩, hs, hr, ht, ⟨hm, trivial⟩, trivial⟩

#check mainConstraints

lemma requirements_of_channelsLawful_nil
    {ops : Operations (F circomPrime)}
    {env : Environment (F circomPrime)}
    (h : ops.ChannelsLawful [] []) : ops.Requirements env := by
  rw [Operations.requirements_iff_forall_mem]
  constructor
  · have hi := h.2.2.2.1 env
    rw [Operations.inChannelsOrRequirements_iff_forall_mem] at hi
    simpa using hi
  · intro s hs
    left
    rw [List.eq_nil_iff_forall_not_mem]
    intro c hc
    have hsub := h.2.2.1
    rw [Operations.subcircuitChannelsWithRequirements_subset_iff_forall] at hsub
    simpa using hsub s hs c hc

lemma mainOutput_eq
    (input : Var ScalarMul.Inputs (F circomPrime)) (i₀ : ℕ) :
    ElaboratedCircuit.output main input i₀ =
      outputFromValidated
        (varFromOffset FlaggedPoint i₀)
        (PointValid.circuit.output (varFromOffset FlaggedPoint i₀) (i₀ + 9)) := by
  rfl

lemma mainCircuitOutput_eq
    (input : Var ScalarMul.Inputs (F circomPrime)) (i₀ : ℕ) :
    (main input).output i₀ =
      outputFromValidated
        (varFromOffset FlaggedPoint i₀)
        (PointValid.circuit.output (varFromOffset FlaggedPoint i₀) (i₀ + 9)) := by
  exact elaborated.output_eq input i₀

attribute [local irreducible] main PointValid.main GLVScalarRelation.main
  PatBuildTable.main PatBuildTable.tableAt LazyMSM.main AssertInfinity.main

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem soundness : Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start_core
  dsimp only [Assumptions, ScalarMul.Assumptions] at h_assumptions
  provable_struct_simp
  simp only [circuit_norm] at h_input
  have hPV : ∀ Q : Var FlaggedPoint (F circomPrime),
      PointValid.circuit.localLength Q = 1046 := fun _ => rfl
  have hSC : ∀ c : Var GLV.SignedCoeff (F circomPrime),
      GLV.circuit.localLength c = 0 := fun _ => rfl
  have hSCZ : ∀ c : Var GLV.SignedCoeff (F circomPrime),
      GLV.circuitZ.localLength c = 0 := fun _ => rfl
  have hSR : ∀ X : Var GLV.ScalarReduce.Inputs (F circomPrime),
      GLV.ScalarReduce.circuit.localLength X = 0 := fun _ => rfl
  have hRel : ∀ X : Var GLVScalarRelation.Inputs (F circomPrime),
      GLVScalarRelation.circuit.localLength X = 865 := fun _ => rfl
  have hTab : ∀ X : Var GLVBuildTable.Inputs (F circomPrime),
      PatBuildTable.circuit.localLength X = 16366 := patBuildTable_localLength
  have hMSM : ∀ X : Var GLVMSM.Inputs (F circomPrime),
      LazyMSM.circuit.localLength X = 103012 := lazyMSM_localLength
  simp only [main, mainOperations, mainOutput, opChain,
    qCircuit, qVar, pointValidCircuit, coeffCircuit, coeffVar,
    u1Circuit, u2Circuit, v1Circuit, v2Circuit, reduceCircuit, reduceVar,
    relationCircuit, tableCircuit, tableVar, msmCircuit, infinityCircuit,
    pvOffset, coeffOffset, shortOffset, relationOffset, tableOffset, msmOffset, outOffset,
    ConstraintsHold.Soundness, Circuit.operations, hMSM,
    Operations.forAllNoOffset_append, and_assoc] at h_holds
  rcases h_holds with ⟨_, hQcheck, _, hu1check, hu2check, hv1check,
    hv2check, hs, hr, ht, hm, hinf⟩
  simp only [circuit_norm] at hQcheck
  simp only [circuit_norm, h_input] at hu1check hu2check hv1check hv2check
  simp only [circuit_norm, h_input] at hs
  simp only [circuit_norm, h_input] at hr
  simp only [circuit_norm, h_input] at ht
  simp only [circuit_norm, h_input] at hm
  simp only [circuit_norm, h_input] at hinf
  obtain ⟨h_bits_eq, h_px_eq, h_py_eq⟩ := h_input
  have hQspec := hQcheck trivial
  have hu1 := hu1check trivial
  have hu1V := GLV.ValidZ.toValid hu1
  have hu2 := hu2check trivial
  have hv1 := hv1check trivial
  have hv2 := hv2check trivial
  let cv : Var GLV.Coefficients (F circomPrime) :=
    varFromOffset GLV.Coefficients (i₀ + 9 + 1046)
  let c : GLV.Coefficients (F circomPrime) := eval env cv
  have hu1c : GLV.Valid c.u1 := by
    simpa only [c, cv, circuit_norm, GLV.coeffBits, List.sum_cons,
      List.sum_nil, Nat.reduceAdd] using hu1V
  have hu2c : GLV.Valid c.u2 := by
    simpa only [c, cv, circuit_norm, GLV.coeffBits, List.sum_cons,
      List.sum_nil, Nat.reduceAdd] using hu2
  have hv1c : GLV.Valid c.v1 := by
    simpa only [c, cv, circuit_norm, GLV.coeffBits, List.sum_cons,
      List.sum_nil, Nat.reduceAdd] using hv1
  have hv2c : GLV.Valid c.v2 := by
    simpa only [c, cv, circuit_norm, GLV.coeffBits, List.sum_cons,
      List.sum_nil, Nat.reduceAdd] using hv2
  have hc : GLV.Valid c.u1 ∧ GLV.Valid c.u2 ∧
      GLV.Valid c.v1 ∧ GLV.Valid c.v2 := ⟨hu1c, hu2c, hv1c, hv2c⟩
  have hsspec := hs h_assumptions.1
  have hrspec := hr ⟨hsspec.1, hu1V, hu2, hv1, hv2⟩
  have hPvalid :
      (eval env (inputPointVar input_var)).Valid := by
    simpa only [inputPointVar, inputPoint, circuit_norm, h_px_eq, h_py_eq] using
      (inputPoint_valid
        (input := { bits := input_bits, px := input_px, py := input_py })
        h_assumptions)
  have hPfin : (eval env (inputPointVar input_var)).isInf = 0 := by
    simp only [inputPointVar, circuit_norm]
  have hPxne : decodeFe (eval env (inputPointVar input_var)).x ≠ 0 := by
    simpa only [inputPointVar, inputPoint, circuit_norm, h_px_eq, h_py_eq] using
      OrderFactsCerts.noXZero_secp
        (P := { x := decodeFe input_px, y := decodeFe input_py })
        h_assumptions.2.2.2
  have htSpec := ht ⟨⟨by
      simpa only [circuit_norm] using hPvalid,
    hQspec.1.1, hu1.1, hu2.1, hv1.1, hv2.1,
    (fun hinf => by
      have hinf' : (eval env (inputPointVar input_var)).isInf = 1 := by
        simpa only [circuit_norm] using hinf
      exact (zero_ne_one (hPfin.symm.trans hinf')).elim),
    (fun hinf => (hQspec.1.2 hinf).2)⟩,
    by simpa only [circuit_norm] using hPfin,
    by simpa only [circuit_norm] using hPxne,
    by simpa only [circuit_norm] using hQspec.1.2⟩
  have hmSpec := hm ⟨fun i => (htSpec i).1, fun i => (htSpec i).2.2,
    hu1V.2, hu2.2, hv1.2, hv2.2⟩
  simp only [inputPointVar, inputPoint, circuit_norm, h_px_eq, h_py_eq] at htSpec
  let Qv : Var FlaggedPoint (F circomPrime) :=
    varFromOffset FlaggedPoint i₀
  let sV := GLV.ScalarReduce.circuit.output { bits := input_var.bits }
    (i₀ + 9 + 1046 + 260)
  let iTable := i₀ + 9 + 1046 + 260 + 0 + 865
  let tV := PatBuildTable.circuit.output
    { P := inputPointVar input_var, Q := Qv
      sign0 := cv.u1.sign, sign1 := cv.u2.sign
      sign2 := cv.v1.sign, sign3 := cv.v2.sign } iTable
  let iMSM := iTable + 16366
  let mV : Var GLVMSM.Inputs (F circomPrime) :=
    { tx := tV.tx, ty := tV.ty, tinf := tV.tinf
      m0 := cv.u1.bits, m1 := cv.u2.bits
      m2 := cv.v1.bits, m3 := cv.v2.bits }
  have hpoint :
      decodePoint (eval env (varFromOffset FlaggedPoint i₀ :
        Var FlaggedPoint (F circomPrime))) =
        trueResult { bits := input_bits, px := input_px, py := input_py } := by
    apply verifiedPoint_eq_trueResult
      (input := { bits := input_bits, px := input_px, py := input_py })
      (Q := eval env Qv) (c := c) (s := eval env sV)
      (table := eval env tV)
    · exact h_assumptions
    · simpa only [Qv, circuit_norm] using hQspec.1.1
    · exact hc
    · simpa only [sV, circuit_norm] using hsspec
    · simpa only [sV, c, cv, circuit_norm, GLV.coeffBits,
        List.sum_cons, List.sum_nil, Nat.reduceAdd] using hrspec
    · simpa only [tV, iTable, Qv, c, cv, circuit_norm, GLV.coeffBits,
        List.sum_cons, List.sum_nil, Nat.reduceAdd] using htSpec
    · simpa only [GLVVerifierTheorems.msmInput, mV, iMSM,
          tV, iTable, Qv, c, cv, circuit_norm, GLV.coeffBits, List.sum_cons,
          List.sum_nil, Nat.reduceAdd] using hmSpec
  have houtSpec' : PointOutput.Spec
      (eval env (varFromOffset FlaggedPoint i₀ : Var FlaggedPoint (F circomPrime)))
      (eval env (outputFromValidated
        (varFromOffset FlaggedPoint i₀)
        (PointValid.circuit.output
          (varFromOffset FlaggedPoint i₀) (i₀ + 9)))) := by
    simpa only [outputFromValidated, PointOutput.fromBytes,
      PointOutput.reverseBytes, circuit_norm, Vector.map_reverse] using
      PointOutput.spec_of_bytes
        (eval env (varFromOffset FlaggedPoint i₀ :
          Var FlaggedPoint (F circomPrime)))
        (eval env (PointValid.circuit.output
          (varFromOffset FlaggedPoint i₀) (i₀ + 9))).x
        (eval env (PointValid.circuit.output
          (varFromOffset FlaggedPoint i₀) (i₀ + 9))).y
        (by simpa only [PointOutput.Assumptions, PointValid.Spec,
          circuit_norm] using hQspec.1)
        (by simpa only [circuit_norm] using hQspec.2.1)
        (by simpa only [circuit_norm] using hQspec.2.2)
  dsimp only [Spec]
  rw [mainOutput_eq]
  constructor
  · refine ⟨houtSpec'.1, ?_⟩
    unfold Specs.Secp256k1ScalarMul.Spec Specs.ShortWeierstrass.Spec
    rw [houtSpec'.2, hpoint]
    unfold trueResult
    rfl
  · exact requirements_of_channelsLawful_nil
      (elaboratedChannelsLawful input_var i₀)

#check soundness


end GLVScalarMul
end Solution.Secp256k1ScalarMul
