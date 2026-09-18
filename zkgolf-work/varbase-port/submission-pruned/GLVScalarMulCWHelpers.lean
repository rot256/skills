import Solution.Secp256k1ScalarMul.GLVScalarMulR1CS

namespace Solution.Secp256k1ScalarMul

local notation "CF" => F circomPrime
open Challenge.Utils.ComputableWitnessLemmas

namespace GLVScalarMul

lemma eval_varFromOffset_of_agreesBelow
    {A : TypeMap} [ProvableType A] {off k : ℕ}
    {env env' : ProverEnvironment (CF)}
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

lemma eval_provableWitness_output_of_agreesBelow
    {A : TypeMap} [ProvableType A]
    (compute : ProverEnvironment (CF) → A (CF))
    {off k : ℕ} {env env' : ProverEnvironment (CF)}
    (h_agree : env.AgreesBelow k env') (hk : off + size A ≤ k) :
    eval env ((ProvableType.witness (F := CF) (α := A) compute).output off) =
      eval env' ((ProvableType.witness (F := CF) (α := A) compute).output off) := by
  exact eval_varFromOffset_of_agreesBelow h_agree hk

lemma resultOutput_stable
    (input : Var ScalarMul.Inputs (CF)) {off k : ℕ}
    {env env' : ProverEnvironment (CF)}
    (h_agree : env.AgreesBelow k env') (hk : off + 9 ≤ k) :
    eval env
        ((ProvableType.witness (F := CF) (α := FlaggedPoint)
          (resultWitness input)).output off) =
      eval env'
        ((ProvableType.witness (F := CF) (α := FlaggedPoint)
          (resultWitness input)).output off) := by
  exact eval_provableWitness_output_of_agreesBelow _ h_agree (by
    simpa only [show size FlaggedPoint = 9 from rfl] using hk)

lemma coefficientOutput_stable
    (input : Var ScalarMul.Inputs (CF)) {off k : ℕ}
    {env env' : ProverEnvironment (CF)}
    (h_agree : env.AgreesBelow k env') (hk : off + 260 ≤ k) :
    eval env
        ((ProvableType.witness (F := CF) (α := GLV.Coefficients)
          (coefficientWitness input)).output off) =
      eval env'
        ((ProvableType.witness (F := CF) (α := GLV.Coefficients)
          (coefficientWitness input)).output off) := by
  exact eval_provableWitness_output_of_agreesBelow _ h_agree (by
    simpa only [show size GLV.Coefficients = 260 from rfl] using hk)

lemma scalarReduceOutput_stable
    (bits : Vector (Expression (CF)) Specs.Secp256k1.scalarBits)
    {off k : ℕ} {env env' : ProverEnvironment (CF)}
    (_h_agree : env.AgreesBelow k env') (_hk : off ≤ k)
    (hbits : eval env bits = eval env' bits) :
    eval env
        ((subcircuit GLV.ScalarReduce.circuit { bits }).output off) =
      eval env'
        ((subcircuit GLV.ScalarReduce.circuit { bits }).output off) := by
  rw [show (subcircuit GLV.ScalarReduce.circuit { bits }).output off =
      GLV.ScalarReduce.packBits bits from rfl]
  have hmap : Vector.map (Expression.eval env.toEnvironment)
      (GLV.ScalarReduce.packBits bits) =
    Vector.map (Expression.eval env'.toEnvironment)
      (GLV.ScalarReduce.packBits bits) := by
    rw [GLV.ScalarReduce.eval_packBits, GLV.ScalarReduce.eval_packBits]
    exact congrArg GLV.ScalarReduce.packed (by
      simpa only [circuit_norm] using hbits)
  simpa only [circuit_norm] using hmap

lemma tableTx_of_eval_eq
    {t : Var GLVBuildTable.Table (CF)}
    {env env' : ProverEnvironment (CF)}
    (h : eval env t = eval env' t) :
    eval env.toEnvironment t.tx = eval env'.toEnvironment t.tx := by
  simpa only [circuit_norm] using
    congrArg (fun x : GLVBuildTable.Table (CF) => x.tx) h

lemma tableTy_of_eval_eq
    {t : Var GLVBuildTable.Table (CF)}
    {env env' : ProverEnvironment (CF)}
    (h : eval env t = eval env' t) :
    eval env.toEnvironment t.ty = eval env'.toEnvironment t.ty := by
  simpa only [circuit_norm] using
    congrArg (fun x : GLVBuildTable.Table (CF) => x.ty) h

lemma tableTinf_of_eval_eq
    {t : Var GLVBuildTable.Table (CF)}
    {env env' : ProverEnvironment (CF)}
    (h : eval env t = eval env' t) :
    Vector.map (Expression.eval env.toEnvironment) t.tinf =
      Vector.map (Expression.eval env'.toEnvironment) t.tinf := by
  simpa only [circuit_norm] using
    congrArg (fun x : GLVBuildTable.Table (CF) => x.tinf) h

lemma coeffU1Bits_of_eval_eq
    {c : Var GLV.Coefficients (CF)}
    {env env' : ProverEnvironment (CF)}
    (h : eval env c = eval env' c) :
    Vector.map (Expression.eval env.toEnvironment) c.u1.bits =
      Vector.map (Expression.eval env'.toEnvironment) c.u1.bits := by
  simpa only [circuit_norm] using
    congrArg (fun x : GLV.Coefficients (CF) => x.u1.bits) h

lemma coeffU2Bits_of_eval_eq
    {c : Var GLV.Coefficients (CF)}
    {env env' : ProverEnvironment (CF)}
    (h : eval env c = eval env' c) :
    Vector.map (Expression.eval env.toEnvironment) c.u2.bits =
      Vector.map (Expression.eval env'.toEnvironment) c.u2.bits := by
  simpa only [circuit_norm] using
    congrArg (fun x : GLV.Coefficients (CF) => x.u2.bits) h

lemma coeffV1Bits_of_eval_eq
    {c : Var GLV.Coefficients (CF)}
    {env env' : ProverEnvironment (CF)}
    (h : eval env c = eval env' c) :
    Vector.map (Expression.eval env.toEnvironment) c.v1.bits =
      Vector.map (Expression.eval env'.toEnvironment) c.v1.bits := by
  simpa only [circuit_norm] using
    congrArg (fun x : GLV.Coefficients (CF) => x.v1.bits) h

lemma coeffV2Bits_of_eval_eq
    {c : Var GLV.Coefficients (CF)}
    {env env' : ProverEnvironment (CF)}
    (h : eval env c = eval env' c) :
    Vector.map (Expression.eval env.toEnvironment) c.v2.bits =
      Vector.map (Expression.eval env'.toEnvironment) c.v2.bits := by
  simpa only [circuit_norm] using
    congrArg (fun x : GLV.Coefficients (CF) => x.v2.bits) h

lemma msmInput_of_eval_eq
    (t : Var GLVBuildTable.Table (CF))
    (c : Var GLV.Coefficients (CF))
    {env env' : ProverEnvironment (CF)}
    (ht : eval env t = eval env' t)
    (hc : eval env c = eval env' c) :
    eval env
        ({ tx := t.tx, ty := t.ty, tinf := t.tinf,
           m0 := c.u1.bits, m1 := c.u2.bits,
           m2 := c.v1.bits, m3 := c.v2.bits } :
          Var GLVMSM.Inputs (CF)) =
      eval env'
        ({ tx := t.tx, ty := t.ty, tinf := t.tinf,
           m0 := c.u1.bits, m1 := c.u2.bits,
           m2 := c.v1.bits, m3 := c.v2.bits } :
          Var GLVMSM.Inputs (CF)) := by
  simp only [circuit_norm, GLVMSM.Inputs.mk.injEq]
  exact ⟨tableTx_of_eval_eq ht, tableTy_of_eval_eq ht,
    tableTinf_of_eval_eq ht, coeffU1Bits_of_eval_eq hc,
    coeffU2Bits_of_eval_eq hc, coeffV1Bits_of_eval_eq hc,
    coeffV2Bits_of_eval_eq hc⟩

attribute [local irreducible] main PointValid.main GLVScalarRelation.main

theorem generalSubcircuit_structuralComputableWitnesses_iff
    {Parent Input Output : TypeMap}
    [CircuitType Parent] [ProvableType Input] [ProvableType Output]
    (c : GeneralFormalCircuit CF Input Output)
    (parentInput : Var Parent CF)
    (input : Var Input CF) (n : ℕ)
    (env env' : ProverEnvironment CF) :
    FormalCircuitBase.Operations.StructuralComputableWitnesses
        parentInput env env' n ((subcircuitWithAssertion c input).operations n) ↔
      FormalCircuitBase.FlatOperation.StructuralComputableWitnesses
        parentInput env env' n ((c.toSubcircuit n input).ops.toFlat) := by
  unfold subcircuitWithAssertion
  simp [FormalCircuitBase.Operations.StructuralComputableWitnesses]

abbrev SCW (input : Var ScalarMul.Inputs CF)
    (env env' : ProverEnvironment CF) (offset : ℕ) (ops : Operations CF) : Prop :=
  FormalCircuitBase.Operations.StructuralComputableWitnesses input env env' offset ops

theorem appendSCW {input : Var ScalarMul.Inputs CF}
    {env env' : ProverEnvironment CF} {offset : ℕ}
    {ops₁ ops₂ : Operations CF}
    (h₁ : SCW input env env' offset ops₁)
    (h₂ : SCW input env env' (ops₁.localLength + offset) ops₂) :
    SCW input env env' offset (ops₁ ++ ops₂) :=
  (FormalCircuitBase.Operations.structuralComputableWitnesses_append).2 ⟨h₁, h₂⟩

theorem structuralResultWitness
    (input : Var ScalarMul.Inputs CF) (offset : ℕ)
    (env env' : ProverEnvironment CF) :
    SCW input env env' offset ((qCircuit input).operations offset) := by
  simp only [SCW, qCircuit, Circuit.provableWitness_structuralComputableWitnesses_iff]
  intro _ h_in
  simpa only [resultWitness, circuit_norm] using
    congrArg (fun x => encodePoint (trueResult x)) h_in

theorem structuralCoefficientWitness
    (input : Var ScalarMul.Inputs CF) (offset : ℕ)
    (env env' : ProverEnvironment CF) :
    SCW input env env' (coeffOffset offset)
      ((coeffCircuit input).operations (coeffOffset offset)) := by
  simp only [SCW, coeffCircuit,
    Circuit.provableWitness_structuralComputableWitnesses_iff]
  intro _ h_in
  simpa only [coefficientWitness, circuit_norm] using
    congrArg (fun x => coefficientValue x) h_in

theorem structuralPointValid
    (input : Var ScalarMul.Inputs CF) (offset : ℕ)
    (env env' : ProverEnvironment CF) :
    SCW input env env' (pvOffset offset)
      ((pointValidCircuit input offset).operations (pvOffset offset)) := by
  simp only [SCW, pointValidCircuit, qVar, qCircuit]
  rw [generalSubcircuit_structuralComputableWitnesses_iff]
  refine GeneralFormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
    (Parent := ScalarMul.Inputs) PointValid.circuit input
    ((ProvableType.witness (F := CF) (α := FlaggedPoint)
      (resultWitness input)).output offset) _ ?_
    PointValid.computableWitnesses env env'
  intro k e e' hle h_agree _
  exact resultOutput_stable input (off := offset) h_agree (by
    simpa only [pvOffset] using hle)

theorem structuralGLV
    (input : Var ScalarMul.Inputs CF) (x : Var GLV.SignedCoeff CF)
    (n : ℕ)
    (hstable : ∀ (k : ℕ) (env env' : ProverEnvironment CF),
      n ≤ k → env.AgreesBelow k env' →
      eval env input = eval env' input → eval env x = eval env' x)
    (env env' : ProverEnvironment CF) :
    SCW input env env' n ((GLV.circuit x).operations n) := by
  simp only [SCW]
  exact FormalAssertion.assertion_structuralComputableWitnesses_of_condition
    GLV.circuit input x n hstable GLV.computableWitnesses env env'

theorem structuralGLVZ
    (input : Var ScalarMul.Inputs CF) (x : Var GLV.SignedCoeff CF)
    (n : ℕ)
    (hstable : ∀ (k : ℕ) (env env' : ProverEnvironment CF),
      n ≤ k → env.AgreesBelow k env' →
      eval env input = eval env' input → eval env x = eval env' x)
    (env env' : ProverEnvironment CF) :
    SCW input env env' n ((GLV.circuitZ x).operations n) := by
  simp only [SCW]
  exact FormalAssertion.assertion_structuralComputableWitnesses_of_condition
    GLV.circuitZ input x n hstable GLV.computableWitnessesZ env env'

end GLVScalarMul

end Solution.Secp256k1ScalarMul
