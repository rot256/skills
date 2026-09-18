import Solution.Secp256k1ScalarMul.Cost



namespace Solution.Secp256k1ScalarMul.GLV

set_option maxRecDepth 2000

open Utils.Bits
open Challenge.CostR1CS
open Solution.Secp256k1ScalarMul.Cost


@[reducible] def coeffBits : ℕ := 64


structure SignedCoeff (F : Type) where
  sign : F
  bits : Vector F coeffBits
deriving ProvableStruct


structure Coefficients (F : Type) where
  u1 : SignedCoeff F
  u2 : SignedCoeff F
  v1 : SignedCoeff F
  v2 : SignedCoeff F
deriving ProvableStruct


def lowBits {α : Type} (bits : Vector α coeffBits) : Vector α 64 := bits

lemma lowBits_map {α β : Type} (f : α → β) (bits : Vector α coeffBits) :
    lowBits (bits.map f) = (lowBits bits).map f := rfl

lemma lowBits_eq_self {α : Type} (bits : Vector α coeffBits) :
    lowBits bits = bits := rfl


def magnitude (c : SignedCoeff (F circomPrime)) : ℕ :=
  (fieldFromBits (lowBits c.bits)).val


def signedValue (c : SignedCoeff (F circomPrime)) : ℤ :=
  if c.sign = 1 then -(magnitude c : ℤ) else (magnitude c : ℤ)


def magnitudeVar (c : Var SignedCoeff (F circomPrime)) : Var Emu (F circomPrime) :=
  #v[
    fieldFromBitsExpr (lowBits c.bits),
    0,
    0,
    0
  ]


def magnitudeEmu (c : SignedCoeff (F circomPrime)) : Emu (F circomPrime) :=
  #v[
    fieldFromBits (lowBits c.bits),
    0,
    0,
    0
  ]


def Valid (c : SignedCoeff (F circomPrime)) : Prop :=
  IsBool c.sign ∧ ∀ i : Fin coeffBits, IsBool c.bits[i]


def main (c : Var SignedCoeff (F circomPrime)) : Circuit (F circomPrime) Unit := do
  assertZero (c.sign * (c.sign - 1))
  Circuit.forEach c.bits fun b => assertZero (b * (b - 1))

instance elaborated : ElaboratedCircuit (F circomPrime) SignedCoeff unit main := by
  elaborate_circuit

def Assumptions (_ : SignedCoeff (F circomPrime)) : Prop := True

def Spec (c : SignedCoeff (F circomPrime)) : Prop := Valid c

theorem soundness :
    FormalAssertion.Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [main, Assumptions, Spec, Valid]
  obtain ⟨h_sign, h_bits⟩ := h_holds
  constructor
  · rcases mul_eq_zero.mp h_sign with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (add_neg_eq_zero.mp h1)
  · intro i
    apply IsBool.iff_mul_sub_one.mpr
    have hi : Expression.eval env input_var_bits[i.val] = input_bits[i.val] := by
      have hh := congrArg (fun v : Vector (F circomPrime) coeffBits => v[i.val]) h_input.2
      simpa only [Vector.getElem_map] using hh
    rw [← hi, sub_eq_add_neg]
    exact h_bits i

theorem completeness :
    FormalAssertion.Completeness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [main, Assumptions, Spec, Valid]
  constructor
  · simpa only [sub_eq_add_neg] using IsBool.iff_mul_sub_one.mp h_spec.1
  · intro i
    have hi : Expression.eval env.toEnvironment input_var_bits[i.val] = input_bits[i.val] := by
      have hh := congrArg (fun v : Vector (F circomPrime) coeffBits => v[i.val]) h_input.2
      simpa only [Vector.getElem_map] using hh
    rw [hi]
    simpa only [sub_eq_add_neg] using IsBool.iff_mul_sub_one.mp (h_spec.2 i)


def circuit : FormalAssertion (F circomPrime) SignedCoeff where
  main
  elaborated
  Assumptions
  Spec
  soundness
  completeness


/-- Variant of `Valid` that additionally pins the sign bit to zero. -/
def ValidZ (c : SignedCoeff (F circomPrime)) : Prop :=
  c.sign = 0 ∧ ∀ i : Fin coeffBits, IsBool c.bits[i]

lemma ValidZ.toValid {c : SignedCoeff (F circomPrime)} (h : ValidZ c) : Valid c :=
  ⟨Or.inl h.1, h.2⟩

/-- Same shape and same cost as `main`, but asserts `sign = 0` instead of
`IsBool sign`. -/
def mainZ (c : Var SignedCoeff (F circomPrime)) : Circuit (F circomPrime) Unit := do
  assertZero c.sign
  Circuit.forEach c.bits fun b => assertZero (b * (b - 1))

instance elaboratedZ : ElaboratedCircuit (F circomPrime) SignedCoeff unit mainZ := by
  elaborate_circuit

def SpecZ (c : SignedCoeff (F circomPrime)) : Prop := ValidZ c

theorem soundnessZ :
    FormalAssertion.Soundness (F circomPrime) mainZ Assumptions SpecZ := by
  circuit_proof_start [mainZ, Assumptions, SpecZ, ValidZ]
  obtain ⟨h_sign, h_bits⟩ := h_holds
  refine ⟨h_sign, ?_⟩
  intro i
  apply IsBool.iff_mul_sub_one.mpr
  have hi : Expression.eval env input_var_bits[i.val] = input_bits[i.val] := by
    have hh := congrArg (fun v : Vector (F circomPrime) coeffBits => v[i.val]) h_input.2
    simpa only [Vector.getElem_map] using hh
  rw [← hi, sub_eq_add_neg]
  exact h_bits i

theorem completenessZ :
    FormalAssertion.Completeness (F circomPrime) mainZ Assumptions SpecZ := by
  circuit_proof_start [mainZ, Assumptions, SpecZ, ValidZ]
  refine ⟨h_spec.1, ?_⟩
  intro i
  have hi : Expression.eval env.toEnvironment input_var_bits[i.val] = input_bits[i.val] := by
    have hh := congrArg (fun v : Vector (F circomPrime) coeffBits => v[i.val]) h_input.2
    simpa only [Vector.getElem_map] using hh
  rw [hi]
  simpa only [sub_eq_add_neg] using IsBool.iff_mul_sub_one.mp (h_spec.2 i)


def circuitZ : FormalAssertion (F circomPrime) SignedCoeff where
  main := mainZ
  elaborated := elaboratedZ
  Assumptions
  Spec := SpecZ
  soundness := soundnessZ
  completeness := completenessZ



lemma lowBits_bool {c : SignedCoeff (F circomPrime)} (h : Valid c) :
    ∀ i : Fin 64, IsBool (lowBits c.bits)[i] := by
  intro i
  exact h.2 ⟨i.val, i.isLt⟩

lemma low_value_lt {c : SignedCoeff (F circomPrime)} (h : Valid c) :
    (fieldFromBits (lowBits c.bits)).val < 2 ^ 64 := by
  exact fieldFromBits_lt _ fun i hi => lowBits_bool h ⟨i, hi⟩

theorem magnitude_lt {c : SignedCoeff (F circomPrime)} (h : Valid c) :
    magnitude c < 2 ^ coeffBits := by
  have hlo := low_value_lt h
  simp only [magnitude, coeffBits, limbBits] at *
  omega

theorem magnitudeEmu_normalized {c : SignedCoeff (F circomPrime)} (h : Valid c) :
    (magnitudeEmu c).Normalized limbBits := by
  intro i
  fin_cases i
  · simpa [magnitudeEmu, limbBits] using low_value_lt h
  · simp [magnitudeEmu, limbBits]
  · simp [magnitudeEmu, limbBits]
  · simp [magnitudeEmu, limbBits]

theorem magnitudeEmu_value (c : SignedCoeff (F circomPrime)) :
    BigInt.value limbBits (magnitudeEmu c) = magnitude c := by
  rw [BigInt.value_eq_sum]
  rw [Fin.sum_univ_four]
  simp [magnitudeEmu, magnitude, limbBits, numLimbs]

theorem magnitudeVar_eval (env : Environment (F circomPrime))
    (c : Var SignedCoeff (F circomPrime)) :
    Vector.map (Expression.eval env) (magnitudeVar c) =
      magnitudeEmu
        { sign := Expression.eval env c.sign,
          bits := c.bits.map (Expression.eval env) } := by
  have hlow : Expression.eval env (fieldFromBitsExpr (lowBits c.bits)) =
      fieldFromBits (lowBits (c.bits.map (Expression.eval env))) := by
    calc
      Expression.eval env (fieldFromBitsExpr (lowBits c.bits)) =
          fieldFromBits ((lowBits c.bits).map (Expression.eval env)) :=
        fieldFromBits_eval (eval := env) (lowBits c.bits)
      _ = fieldFromBits (lowBits (c.bits.map (Expression.eval env))) := by
        rw [lowBits_map]
  apply Vector.ext
  intro i hi
  have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
    simp only [numLimbs] at hi
    omega
  rcases hi' with rfl | rfl | rfl | rfl
  · simpa [magnitudeVar, magnitudeEmu] using hlow
  · simp [magnitudeVar, magnitudeEmu, Expression.eval]
  · simp [magnitudeVar, magnitudeEmu, Expression.eval]
  · simp [magnitudeVar, magnitudeEmu, Expression.eval]

theorem magnitudeVar_normalized (env : Environment (F circomPrime))
    (c : Var SignedCoeff (F circomPrime))
    (h : Valid
      { sign := Expression.eval env c.sign,
        bits := c.bits.map (Expression.eval env) }) :
    BigInt.Normalized limbBits
      (Vector.map (Expression.eval env) (magnitudeVar c)) := by
  rw [magnitudeVar_eval]
  exact magnitudeEmu_normalized h

theorem magnitudeVar_value (env : Environment (F circomPrime))
    (c : Var SignedCoeff (F circomPrime)) :
    BigInt.value limbBits (Vector.map (Expression.eval env) (magnitudeVar c)) =
      magnitude
        { sign := Expression.eval env c.sign,
          bits := c.bits.map (Expression.eval env) } := by
  rw [magnitudeVar_eval, magnitudeEmu_value]



theorem costIs_main (c : Var SignedCoeff (F circomPrime)) :
    CostIs (main c) ⟨0, 65⟩ := by
  unfold main
  have hcount :
      (⟨0, 1⟩ + ⟨coeffBits * 0, coeffBits * 1⟩ : Count)
        = ⟨0, 65⟩ := by
    decide
  rw [← hcount]
  refine CostIs.bind (CostIs.assertZero _) fun _ => ?_
  exact CostIs.forEach fun (b : Expression (F circomPrime)) n =>
    CostIs.assertZero (b * (b - 1)) n

theorem isR1CS_main (c : Var SignedCoeff (F circomPrime))
    (hsign : Affine c.sign) (hbits : AffineW c.bits) :
    IsR1CSCirc (main c) := by
  unfold main
  refine IsR1CSCirc.bind (IsR1CSCirc.assertZero ?_) fun _ => ?_
  · exact isR1CSRow_mul (F := F circomPrime) hsign (Affine.sub hsign (Affine.const 1))
  · refine IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) fun i n => ?_
    exact IsR1CSCirc.assertZero
      (isR1CSRow_mul (F := F circomPrime) (hbits i.val i.isLt)
        (Affine.sub (hbits i.val i.isLt) (Affine.const 1))) n

theorem computableWitnesses : circuit.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.assertZero_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.forEach_structuralComputableWitnesses_iff]
  exact ⟨trivial, fun _ => trivial⟩

theorem costIs_mainZ (c : Var SignedCoeff (F circomPrime)) :
    CostIs (mainZ c) ⟨0, 65⟩ := by
  unfold mainZ
  have hcount :
      (⟨0, 1⟩ + ⟨coeffBits * 0, coeffBits * 1⟩ : Count)
        = ⟨0, 65⟩ := by
    decide
  rw [← hcount]
  refine CostIs.bind (CostIs.assertZero _) fun _ => ?_
  exact CostIs.forEach fun (b : Expression (F circomPrime)) n =>
    CostIs.assertZero (b * (b - 1)) n

theorem isR1CS_mainZ (c : Var SignedCoeff (F circomPrime))
    (hsign : Affine c.sign) (hbits : AffineW c.bits) :
    IsR1CSCirc (mainZ c) := by
  unfold mainZ
  refine IsR1CSCirc.bind (IsR1CSCirc.assertZero (isR1CSRow_of_affine hsign)) fun _ => ?_
  refine IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) fun i n => ?_
  exact IsR1CSCirc.assertZero
    (isR1CSRow_mul (F := F circomPrime) (hbits i.val i.isLt)
      (Affine.sub (hbits i.val i.isLt) (Affine.const 1))) n

theorem computableWitnessesZ : circuitZ.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition input env env')
    ((mainZ input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold mainZ
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.assertZero_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.forEach_structuralComputableWitnesses_iff]
  exact ⟨trivial, fun _ => trivial⟩

end Solution.Secp256k1ScalarMul.GLV
