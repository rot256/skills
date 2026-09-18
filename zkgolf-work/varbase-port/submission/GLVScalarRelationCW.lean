import Solution.Secp256k1ScalarMul.GLVScalarRelation

namespace Solution.Secp256k1ScalarMul

open Challenge.CostR1CS
open Challenge.Utils.ComputableWitnessLemmas
open Utils.Bits
open Cost
open Limbs

namespace GLV

private lemma residueSum_eval_eq
    {x : Var ResidueSum4 (F circomPrime)}
    {e e' : ProverEnvironment (F circomPrime)}
    (h : eval e x = eval e' x) :
    evalResidueSum4 e.toEnvironment x = evalResidueSum4 e'.toEnvironment x := by
  simpa [evalResidueSum4, circuit_norm] using h

private lemma positiveCoeffs_stable
    {x : Var ResidueSum4 (F circomPrime)}
    {e e' : ProverEnvironment (F circomPrime)}
    (h : eval e x = eval e' x) :
    (positiveCoeffs x).map (Expression.eval e.toEnvironment) =
      (positiveCoeffs x).map (Expression.eval e'.toEnvironment) := by
  have hx := residueSum_eval_eq h
  have h0 := congrArg (fun z : ResidueSum4 (F circomPrime) => z.t0) hx
  have h1 := congrArg (fun z : ResidueSum4 (F circomPrime) => z.t1) hx
  have h2 := congrArg (fun z : ResidueSum4 (F circomPrime) => z.t2) hx
  have h3 := congrArg (fun z : ResidueSum4 (F circomPrime) => z.t3) hx
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_map, positiveCoeffs, Vector.getElem_mapFinRange]
  by_cases hil : i < numLimbs
  · rw [dif_pos hil]
    simp only [Expression.eval]
    have h0i : Expression.eval e.toEnvironment x.t0[i] =
        Expression.eval e'.toEnvironment x.t0[i] := by
      simpa only [evalResidueSum4, Vector.getElem_map] using
        congrArg (fun z : Emu (F circomPrime) => z[i]'hil) h0
    have h1i : Expression.eval e.toEnvironment x.t1[i] =
        Expression.eval e'.toEnvironment x.t1[i] := by
      simpa only [evalResidueSum4, Vector.getElem_map] using
        congrArg (fun z : Emu (F circomPrime) => z[i]'hil) h1
    have h2i : Expression.eval e.toEnvironment x.t2[i] =
        Expression.eval e'.toEnvironment x.t2[i] := by
      simpa only [evalResidueSum4, Vector.getElem_map] using
        congrArg (fun z : Emu (F circomPrime) => z[i]'hil) h2
    have h3i : Expression.eval e.toEnvironment x.t3[i] =
        Expression.eval e'.toEnvironment x.t3[i] := by
      simpa only [evalResidueSum4, Vector.getElem_map] using
        congrArg (fun z : Emu (F circomPrime) => z[i]'hil) h3
    rw [h0i, h1i, h2i, h3i,
      eval_nConst_getElem e.toEnvironment i hil,
      eval_nConst_getElem e'.toEnvironment i hil]
  · rw [dif_neg hil]
    rfl

private lemma negativeCoeffs_stable
    {x : Var ResidueSum4 (F circomPrime)} {q : Expression (F circomPrime)}
    {e e' : ProverEnvironment (F circomPrime)}
    (hx : eval e x = eval e' x)
    (hq : Expression.eval e.toEnvironment q = Expression.eval e'.toEnvironment q) :
    (negativeCoeffs x q).map (Expression.eval e.toEnvironment) =
      (negativeCoeffs x q).map (Expression.eval e'.toEnvironment) := by
  have hx' := residueSum_eval_eq hx
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_map, negativeCoeffs, Vector.getElem_mapFinRange]
  by_cases hil : i < numLimbs
  · rw [dif_pos hil]
    simp only [Expression.eval]
    have h0 : Expression.eval e.toEnvironment x.t0[i] =
        Expression.eval e'.toEnvironment x.t0[i] := by
      simpa only [evalResidueSum4, Vector.getElem_map] using
        congrArg (fun z : ResidueSum4 (F circomPrime) => z.t0[i]'hil) hx'
    have h1 : Expression.eval e.toEnvironment x.t1[i] =
        Expression.eval e'.toEnvironment x.t1[i] := by
      simpa only [evalResidueSum4, Vector.getElem_map] using
        congrArg (fun z : ResidueSum4 (F circomPrime) => z.t1[i]'hil) hx'
    have h2 : Expression.eval e.toEnvironment x.t2[i] =
        Expression.eval e'.toEnvironment x.t2[i] := by
      simpa only [evalResidueSum4, Vector.getElem_map] using
        congrArg (fun z : ResidueSum4 (F circomPrime) => z.t2[i]'hil) hx'
    have h3 : Expression.eval e.toEnvironment x.t3[i] =
        Expression.eval e'.toEnvironment x.t3[i] := by
      simpa only [evalResidueSum4, Vector.getElem_map] using
        congrArg (fun z : ResidueSum4 (F circomPrime) => z.t3[i]'hil) hx'
    rw [h0, h1, h2, h3, hq,
      eval_nConst_getElem e.toEnvironment i hil,
      eval_nConst_getElem e'.toEnvironment i hil]
  · rw [dif_neg hil]
    rfl

theorem congruenceComputableWitnesses : congruenceCircuit.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (FormalCircuitBase.computableWitnessCondition input env env')
    ((congruenceMain input).operations offset)
  apply FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  have hw : ∀ (compute : ProverEnvironment (F circomPrime) → F circomPrime) o,
      (ProvableType.witness (α := field) compute).localLength o = 1 := fun _ _ => rfl
  have hrc : ∀ (x : Expression (F circomPrime)) o,
      (assertion (RangeCheck.circuit 3 (by decide) (by decide)) x).localLength o = 2 :=
    fun _ _ => rfl
  let q : Expression (F circomPrime) := var { index := offset }
  unfold congruenceMain
  simp only [
    Circuit.bind_structuralComputableWitnesses_iff,
    Circuit.provableWitness_structuralComputableWitnesses_iff,
    FormalAssertion.assertion_structuralComputableWitnesses_iff,
    hw, hrc]
  refine ⟨?_, ?_, ?_⟩
  · intro _ hinput
    have hp := congrArg (fun z : CongruenceInputs (F circomPrime) => z.positive) hinput
    have hn := congrArg (fun z : CongruenceInputs (F circomPrime) => z.negative) hinput
    have hp' := residueSum_eval_eq (by simpa [circuit_norm] using hp)
    have hn' := residueSum_eval_eq (by simpa [circuit_norm] using hn)
    simp only [hp', hn']
  · exact FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
      (Parent := CongruenceInputs) (RangeCheck.circuit 3 (by decide) (by decide))
      input q _ (by
        intro k e e' hk hagree _
        rw [CircuitType.eval_expression_prover_to_verifier (M := field),
          CircuitType.eval_expression_prover_to_verifier (M := field),
          CircuitType.eval_var_field, CircuitType.eval_var_field]
        simpa only [q, Expression.eval] using hagree offset (by omega))
      (RangeCheck.computableWitnesses 3 (by decide) (by decide)) env env'
  · exact FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
      (Parent := CongruenceInputs) (EqViaCarriesN.circuit sumEqParams)
      input
      { lhs := positiveCoeffs input.positive
        rhs := negativeCoeffs input.negative q } _ (by
        intro k e e' hk hagree hinput
        simp only [circuit_norm, EqViaCarries.Inputs.mk.injEq]
        constructor
        · apply positiveCoeffs_stable
          simpa [circuit_norm] using
            congrArg (fun z : CongruenceInputs (F circomPrime) => z.positive) hinput
        · apply negativeCoeffs_stable
          · simpa [circuit_norm] using
              congrArg (fun z : CongruenceInputs (F circomPrime) => z.negative) hinput
          · simpa only [q, Expression.eval] using hagree offset (by omega))
      (EqViaCarriesN.computableWitnesses sumEqParams) env env'

end GLV

namespace GLVScalarRelation

open GLV

private lemma magnitudeVar_stable
    (c : Var SignedCoeff (F circomPrime))
    {env env' : ProverEnvironment (F circomPrime)}
    (hbits : c.bits.map (Expression.eval env.toEnvironment) =
      c.bits.map (Expression.eval env'.toEnvironment)) :
    (magnitudeVar c).map (Expression.eval env.toEnvironment) =
      (magnitudeVar c).map (Expression.eval env'.toEnvironment) := by
  rw [magnitudeVar_eval, magnitudeVar_eval]
  simp only [magnitudeEmu, hbits]

private lemma mulOutputLooseQ_stable
    (X : Var (MulMod.Inputs numLimbs) (F circomPrime)) {o k : ℕ}
    {env env' : ProverEnvironment (F circomPrime)}
    (hagree : env.AgreesBelow k env') (hk : o + 2 * numLimbs ≤ k) :
    eval env ((subcircuit MulModLooseQ.circuit X).output o) =
      eval env' ((subcircuit MulModLooseQ.circuit X).output o) := by
  apply Vector.ext
  intro i hi
  rw [← ProvableType.getElem_eval_fields_prover (env := env)
      ((subcircuit MulModLooseQ.circuit X).output o) i hi,
    ← ProvableType.getElem_eval_fields_prover (env := env')
      ((subcircuit MulModLooseQ.circuit X).output o) i hi]
  simp only [circuit_norm, subcircuit, MulModLooseQ.circuit,
    MulModLooseQ.elaborated, ProvableType.varFromOffset_fields,
    Vector.getElem_mapRange, Expression.eval]
  exact hagree (o + numLimbs + i) (by omega)

private lemma mulOutputLooseWideB_stable
    (X : Var (MulMod.Inputs numLimbs) (F circomPrime)) {o k : ℕ}
    {env env' : ProverEnvironment (F circomPrime)}
    (hagree : env.AgreesBelow k env') (hk : o + 2 * numLimbs ≤ k) :
    eval env ((subcircuit scalarMulModLooseWideB X).output o) =
      eval env' ((subcircuit scalarMulModLooseWideB X).output o) := by
  apply Vector.ext
  intro i hi
  rw [← ProvableType.getElem_eval_fields_prover (env := env)
      ((subcircuit scalarMulModLooseWideB X).output o) i hi,
    ← ProvableType.getElem_eval_fields_prover (env := env')
      ((subcircuit scalarMulModLooseWideB X).output o) i hi]
  simp only [scalarMulModLooseWideB, circuit_norm, subcircuit, MulModLooseCA.circuitWideB,
    MulModLooseCA.elaborated, ProvableType.varFromOffset_fields,
    Vector.getElem_mapRange, Expression.eval]
  exact hagree (o + numLimbs + i) (by omega)

private lemma muxOutput_stable
    (X : Var (Mux.Inputs Emu) (F circomPrime)) {o k : ℕ}
    {env env' : ProverEnvironment (F circomPrime)}
    (hagree : env.AgreesBelow k env') (hk : o + numLimbs ≤ k) :
    eval env ((subcircuit (Mux.circuit (M := Emu)) X).output o) =
      eval env' ((subcircuit (Mux.circuit (M := Emu)) X).output o) := by
  exact Mux.eval_output_of_agreesBelow X hagree (by simpa only [size] using hk)

private lemma diffOf_stable
    {t n : Var Emu (F circomPrime)} {env env' : ProverEnvironment (F circomPrime)}
    (ht : t.map (Expression.eval env.toEnvironment) = t.map (Expression.eval env'.toEnvironment))
    (hn : n.map (Expression.eval env.toEnvironment) = n.map (Expression.eval env'.toEnvironment)) :
    (diffOf t n).map (Expression.eval env.toEnvironment) =
      (diffOf t n).map (Expression.eval env'.toEnvironment) := by
  apply Vector.ext
  intro i hi
  have ht' := congrArg (fun v : Vector (F circomPrime) numLimbs => v[i]'hi) ht
  have hn' := congrArg (fun v : Vector (F circomPrime) numLimbs => v[i]'hi) hn
  simp only [Vector.getElem_map] at ht' hn'
  simp only [diffOf, Vector.getElem_map, Vector.getElem_ofFn, Expression.eval, ht', hn']

private lemma magnitudeExpr_stable (c : Var SignedCoeff (F circomPrime))
    {env env' : ProverEnvironment (F circomPrime)}
    (hbits : c.bits.map (Expression.eval env.toEnvironment) =
      c.bits.map (Expression.eval env'.toEnvironment))
    (hsign : Expression.eval env.toEnvironment c.sign =
      Expression.eval env'.toEnvironment c.sign) :
    Expression.eval env.toEnvironment (magnitudeExpr c) =
      Expression.eval env'.toEnvironment (magnitudeExpr c) := by
  rw [magnitudeExpr_eval, magnitudeExpr_eval, hbits, hsign]

private lemma scaleVecOutput_stable
    (X : Var ScaleVec.Inputs (F circomPrime)) {o k : ℕ}
    {env env' : ProverEnvironment (F circomPrime)}
    (hagree : env.AgreesBelow k env') (hk : o + numLimbs ≤ k) :
    eval env ((subcircuit ScaleVec.circuit X).output o) =
      eval env' ((subcircuit ScaleVec.circuit X).output o) := by
  apply Vector.ext
  intro i hi
  rw [← ProvableType.getElem_eval_fields_prover (env := env)
      ((subcircuit ScaleVec.circuit X).output o) i hi,
    ← ProvableType.getElem_eval_fields_prover (env := env')
      ((subcircuit ScaleVec.circuit X).output o) i hi]
  simp only [circuit_norm, subcircuit, ScaleVec.circuit,
    ScaleVec.elaborated, ProvableType.varFromOffset_fields,
    Vector.getElem_mapRange, Expression.eval]
  exact hagree (o + i) (by omega)

private lemma negMagOutput_stable
    (X : Var NegativeMagnitude.Inputs (F circomPrime)) {o k : ℕ}
    {env env' : ProverEnvironment (F circomPrime)}
    (hagree : env.AgreesBelow k env') (hk : o + 1 ≤ k) :
    Expression.eval env.toEnvironment
        ((subcircuit NegativeMagnitude.circuit X).output o) =
      Expression.eval env'.toEnvironment
        ((subcircuit NegativeMagnitude.circuit X).output o) := by
  simp only [circuit_norm, subcircuit, NegativeMagnitude.circuit,
    NegativeMagnitude.elaborated, Expression.eval]
  exact hagree o (by omega)

private lemma scaleVecOutputMap_stable
    (X : Var ScaleVec.Inputs (F circomPrime)) {o k : ℕ}
    {env env' : ProverEnvironment (F circomPrime)}
    (hagree : env.AgreesBelow k env') (hk : o + numLimbs ≤ k) :
    Vector.map (Expression.eval env.toEnvironment) (ScaleVec.circuit.output X o) =
      Vector.map (Expression.eval env'.toEnvironment) (ScaleVec.circuit.output X o) :=
  emu_map_eval_eq_of_eval_eq (scaleVecOutput_stable X hagree hk)

private lemma negMagOutputE_stable
    (X : Var NegativeMagnitude.Inputs (F circomPrime)) {o k : ℕ}
    {env env' : ProverEnvironment (F circomPrime)}
    (hagree : env.AgreesBelow k env') (hk : o + 1 ≤ k) :
    Expression.eval env.toEnvironment (NegativeMagnitude.circuit.output X o) =
      Expression.eval env'.toEnvironment (NegativeMagnitude.circuit.output X o) :=
  negMagOutput_stable X hagree hk

private lemma qRelNat_stable
    {mu1 mu2 nm1 nm2 : Expression (F circomPrime)} {c e d f : Var Emu (F circomPrime)}
    {env env' : ProverEnvironment (F circomPrime)}
    (h1 : Expression.eval env.toEnvironment mu1 = Expression.eval env'.toEnvironment mu1)
    (h2 : Expression.eval env.toEnvironment mu2 = Expression.eval env'.toEnvironment mu2)
    (hn1 : Expression.eval env.toEnvironment nm1 = Expression.eval env'.toEnvironment nm1)
    (hn2 : Expression.eval env.toEnvironment nm2 = Expression.eval env'.toEnvironment nm2)
    (hc : c.map (Expression.eval env.toEnvironment) = c.map (Expression.eval env'.toEnvironment))
    (he : e.map (Expression.eval env.toEnvironment) = e.map (Expression.eval env'.toEnvironment))
    (hd : d.map (Expression.eval env.toEnvironment) = d.map (Expression.eval env'.toEnvironment))
    (hf : f.map (Expression.eval env.toEnvironment) = f.map (Expression.eval env'.toEnvironment)) :
    qRelNat env.toEnvironment mu1 mu2 nm1 nm2 c e d f
      = qRelNat env'.toEnvironment mu1 mu2 nm1 nm2 c e d f := by
  simp only [qRelNat, relLhsNat, relRhs0Nat, h1, h2, hn1, hn2, hc, he, hd, hf]

private lemma relLhs_stable
    {mu1 mu2 : Expression (F circomPrime)} {c e : Var Emu (F circomPrime)}
    {env env' : ProverEnvironment (F circomPrime)}
    (h1 : Expression.eval env.toEnvironment mu1 = Expression.eval env'.toEnvironment mu1)
    (h2 : Expression.eval env.toEnvironment mu2 = Expression.eval env'.toEnvironment mu2)
    (hc : c.map (Expression.eval env.toEnvironment) = c.map (Expression.eval env'.toEnvironment))
    (he : e.map (Expression.eval env.toEnvironment) = e.map (Expression.eval env'.toEnvironment)) :
    (RelCells.relLhs mu1 mu2 c e).map (Expression.eval env.toEnvironment) =
      (RelCells.relLhs mu1 mu2 c e).map (Expression.eval env'.toEnvironment) := by
  apply Vector.ext
  intro i hi
  have hci := congrArg (fun v : Vector (F circomPrime) numLimbs => v[i]'hi) hc
  have hei := congrArg (fun v : Vector (F circomPrime) numLimbs => v[i]'hi) he
  simp only [Vector.getElem_map] at hci hei
  simp only [RelCells.relLhs, Vector.getElem_map, Vector.getElem_ofFn, RelCells.lhsCell,
    Expression.eval, RelCells.natE, h1, h2, hci, hei]

private lemma relRhs_stable
    {nm1 nm2 q : Expression (F circomPrime)} {d f : Var Emu (F circomPrime)}
    {env env' : ProverEnvironment (F circomPrime)}
    (hn1 : Expression.eval env.toEnvironment nm1 = Expression.eval env'.toEnvironment nm1)
    (hn2 : Expression.eval env.toEnvironment nm2 = Expression.eval env'.toEnvironment nm2)
    (hq : Expression.eval env.toEnvironment q = Expression.eval env'.toEnvironment q)
    (hd : d.map (Expression.eval env.toEnvironment) = d.map (Expression.eval env'.toEnvironment))
    (hf : f.map (Expression.eval env.toEnvironment) = f.map (Expression.eval env'.toEnvironment)) :
    (RelCells.relRhs nm1 nm2 q d f).map (Expression.eval env.toEnvironment) =
      (RelCells.relRhs nm1 nm2 q d f).map (Expression.eval env'.toEnvironment) := by
  apply Vector.ext
  intro i hi
  have hdi := congrArg (fun v : Vector (F circomPrime) numLimbs => v[i]'hi) hd
  have hfi := congrArg (fun v : Vector (F circomPrime) numLimbs => v[i]'hi) hf
  simp only [Vector.getElem_map] at hdi hfi
  simp only [RelCells.relRhs, Vector.getElem_map, Vector.getElem_ofFn, RelCells.rhsCell,
    Expression.eval, RelCells.natE, hn1, hn2, hq, hdi, hfi]

private lemma qRelInv_stable
    {mu1 mu2 nm1 nm2 : Expression (F circomPrime)} {c e d f : Var Emu (F circomPrime)}
    {env env' : ProverEnvironment (F circomPrime)}
    (h1 : Expression.eval env.toEnvironment mu1 = Expression.eval env'.toEnvironment mu1)
    (h2 : Expression.eval env.toEnvironment mu2 = Expression.eval env'.toEnvironment mu2)
    (hn1 : Expression.eval env.toEnvironment nm1 = Expression.eval env'.toEnvironment nm1)
    (hn2 : Expression.eval env.toEnvironment nm2 = Expression.eval env'.toEnvironment nm2)
    (hc : c.map (Expression.eval env.toEnvironment) = c.map (Expression.eval env'.toEnvironment))
    (he : e.map (Expression.eval env.toEnvironment) = e.map (Expression.eval env'.toEnvironment))
    (hd : d.map (Expression.eval env.toEnvironment) = d.map (Expression.eval env'.toEnvironment))
    (hf : f.map (Expression.eval env.toEnvironment) = f.map (Expression.eval env'.toEnvironment)) :
    Expression.eval env.toEnvironment (qRelInv mu1 mu2 nm1 nm2 c e d f) =
      Expression.eval env'.toEnvironment (qRelInv mu1 mu2 nm1 nm2 c e d f) := by
  have hL := relLhs_stable h1 h2 hc he
  have hR := relRhs_stable (q := (0 : Expression (F circomPrime)))
    hn1 hn2 (by rfl) hd hf
  have hLi : ∀ (i : ℕ) (hi : i < numLimbs),
      Expression.eval env.toEnvironment ((RelCells.relLhs mu1 mu2 c e)[i]'hi) =
        Expression.eval env'.toEnvironment ((RelCells.relLhs mu1 mu2 c e)[i]'hi) := by
    intro i hi
    simpa only [Vector.getElem_map] using
      congrArg (fun v : Vector (F circomPrime) numLimbs => v[i]'hi) hL
  have hRi : ∀ (i : ℕ) (hi : i < numLimbs),
      Expression.eval env.toEnvironment ((RelCells.relRhs nm1 nm2 0 d f)[i]'hi) =
        Expression.eval env'.toEnvironment ((RelCells.relRhs nm1 nm2 0 d f)[i]'hi) := by
    intro i hi
    simpa only [Vector.getElem_map] using
      congrArg (fun v : Vector (F circomPrime) numLimbs => v[i]'hi) hR
  have hpL : Expression.eval env.toEnvironment
        (MulMod.polyEvalExpr (RelCells.relLhs mu1 mu2 c e)
          ((2 : F circomPrime) ^ limbBits)) =
      Expression.eval env'.toEnvironment
        (MulMod.polyEvalExpr (RelCells.relLhs mu1 mu2 c e)
          ((2 : F circomPrime) ^ limbBits)) := by
    simp only [MulMod.polyEvalExpr_eval]
    apply Finset.sum_congr rfl
    intro i _
    rw [hLi i.val i.isLt]
  have hpR : Expression.eval env.toEnvironment
        (MulMod.polyEvalExpr (RelCells.relRhs nm1 nm2 0 d f)
          ((2 : F circomPrime) ^ limbBits)) =
      Expression.eval env'.toEnvironment
        (MulMod.polyEvalExpr (RelCells.relRhs nm1 nm2 0 d f)
          ((2 : F circomPrime) ^ limbBits)) := by
    simp only [MulMod.polyEvalExpr_eval]
    apply Finset.sum_congr rfl
    intro i _
    rw [hRi i.val i.isLt]
  simp only [qRelInv, Expression.eval]
  rw [hpL, hpR]

private def mainW (offset : ℕ) (input : Var Inputs (F circomPrime)) :
    Var Emu (F circomPrime) :=
  (subcircuit scalarMulModLooseWideB
    { a := eigenvalueConst, b := input.s, modulus := nConst }).output (offset + 1 + 0)

private def mainNm1 (offset : ℕ) (input : Var Inputs (F circomPrime)) :
    Expression (F circomPrime) :=
  (subcircuit NegativeMagnitude.circuit
    { sign := input.u1.sign, magnitude := magnitudeExpr input.u1 }).output
      (offset + 1 + 0 + 713)

private def mainNm2 (offset : ℕ) (input : Var Inputs (F circomPrime)) :
    Expression (F circomPrime) :=
  (subcircuit NegativeMagnitude.circuit
    { sign := input.u2.sign, magnitude := magnitudeExpr input.u2 }).output
      (offset + 1 + 0 + 713 + 1)

private def mainC (offset : ℕ) (input : Var Inputs (F circomPrime)) :
    Var Emu (F circomPrime) :=
  (subcircuit ScaleVec.circuit { a := input.s, b := magnitudeExpr input.v1 }).output
    (offset + 1 + 0 + 713 + 1 + 1)

private def mainD (offset : ℕ) (input : Var Inputs (F circomPrime)) :
    Var Emu (F circomPrime) :=
  (subcircuit ScaleVec.circuit { a := mainC offset input, b := input.v1.sign }).output
    (offset + 1 + 0 + 713 + 1 + 1 + 4)

private def mainE (offset : ℕ) (input : Var Inputs (F circomPrime)) :
    Var Emu (F circomPrime) :=
  (subcircuit ScaleVec.circuit
    { a := mainW offset input, b := magnitudeExpr input.v2 }).output
      (offset + 1 + 0 + 713 + 1 + 1 + 4 + 4)

private def mainF (offset : ℕ) (input : Var Inputs (F circomPrime)) :
    Var Emu (F circomPrime) :=
  (subcircuit ScaleVec.circuit { a := mainE offset input, b := input.v2.sign }).output
    (offset + 1 + 0 + 713 + 1 + 1 + 4 + 4 + 4)

private def mainQ (offset : ℕ) (input : Var Inputs (F circomPrime)) :
    Expression (F circomPrime) :=
  qRelInv (magnitudeExpr input.u1) (magnitudeExpr input.u2)
    (mainNm1 offset input) (mainNm2 offset input)
    (mainC offset input) (mainE offset input) (mainD offset input) (mainF offset input)

private def mainGroupedInput (offset : ℕ) (input : Var Inputs (F circomPrime)) :
    Var (GroupedEqX.InputsX numLimbs) (F circomPrime) :=
  { lhs := RelCells.relLhs (magnitudeExpr input.u1) (magnitudeExpr input.u2)
      (mainC offset input) (mainE offset input),
    rhs := RelCells.relRhs (mainNm1 offset input) (mainNm2 offset input)
      (mainQ offset input) (mainD offset input) (mainF offset input) }

private lemma mainQ_stable (offset k : ℕ) (input : Var Inputs (F circomPrime))
    {env env' : ProverEnvironment (F circomPrime)}
    (hagree : env.AgreesBelow k env')
    (hk : offset + 1 + 713 + 1 + 1 + 4 + 4 + 4 + 4 ≤ k)
    (hinput : eval env input = eval env' input) :
    Expression.eval env.toEnvironment (mainQ offset input) =
      Expression.eval env'.toEnvironment (mainQ offset input) := by
  obtain ⟨s, u1, u2, v1, v2⟩ := input
  have hnl : numLimbs = 4 := rfl
  simp only [circuit_norm, Inputs.mk.injEq, SignedCoeff.mk.injEq] at hinput
  unfold mainQ mainNm1 mainNm2 mainC mainE mainD mainF mainW
  exact qRelInv_stable
    (magnitudeExpr_stable u1 hinput.2.1.2 hinput.2.1.1)
    (magnitudeExpr_stable u2 hinput.2.2.1.2 hinput.2.2.1.1)
    (negMagOutput_stable _ hagree (by omega))
    (negMagOutput_stable _ hagree (by omega))
    (emu_map_eval_eq_of_eval_eq (scaleVecOutput_stable _ hagree (by omega)))
    (emu_map_eval_eq_of_eval_eq (scaleVecOutput_stable _ hagree (by omega)))
    (emu_map_eval_eq_of_eval_eq (scaleVecOutput_stable _ hagree (by omega)))
    (emu_map_eval_eq_of_eval_eq (scaleVecOutput_stable _ hagree (by omega)))

private lemma mainGroupedInput_stable (offset k : ℕ)
    (input : Var Inputs (F circomPrime))
    {env env' : ProverEnvironment (F circomPrime)}
    (hagree : env.AgreesBelow k env')
    (hk : offset + 1 + 713 + 1 + 1 + 4 + 4 + 4 + 4 ≤ k)
    (hinput : eval env input = eval env' input) :
    eval env (mainGroupedInput offset input) = eval env' (mainGroupedInput offset input) := by
  obtain ⟨s, u1, u2, v1, v2⟩ := input
  have hnl : numLimbs = 4 := rfl
  have hinput' := hinput
  simp only [circuit_norm, Inputs.mk.injEq, SignedCoeff.mk.injEq] at hinput'
  simp only [mainGroupedInput, circuit_norm, GroupedEqX.InputsX.mk.injEq]
  exact ⟨relLhs_stable
      (magnitudeExpr_stable u1 hinput'.2.1.2 hinput'.2.1.1)
      (magnitudeExpr_stable u2 hinput'.2.2.1.2 hinput'.2.2.1.1)
      (scaleVecOutputMap_stable _ hagree (by omega))
      (scaleVecOutputMap_stable _ hagree (by omega)),
    relRhs_stable
      (negMagOutputE_stable _ hagree (by omega))
      (negMagOutputE_stable _ hagree (by omega))
      (mainQ_stable offset k { s := s, u1 := u1, u2 := u2, v1 := v1, v2 := v2 }
        hagree hk hinput)
      (scaleVecOutputMap_stable _ hagree (by omega))
      (scaleVecOutputMap_stable _ hagree (by omega))⟩

attribute [local irreducible] qRelInv

set_option maxHeartbeats 1000000 in
theorem computableWitnesses : circuit.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations offset)
  apply FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  obtain ⟨s, u1, u2, v1, v2⟩ := input
  have hw : ∀ (compute : ProverEnvironment (F circomPrime) → F circomPrime) o,
      (ProvableType.witness (α := field) compute).localLength o = 1 := fun _ _ => rfl
  have haz : ∀ (x : Expression (F circomPrime)) o,
      (assertZero x).localLength o = 0 := fun _ _ => rfl
  have hmulLooseWideB : ∀ (X : Var (MulMod.Inputs numLimbs) (F circomPrime)) o,
      (subcircuit scalarMulModLooseWideB X).localLength o = 713 := fun _ _ => rfl
  have hnmag : ∀ (X : Var NegativeMagnitude.Inputs (F circomPrime)) o,
      (subcircuit NegativeMagnitude.circuit X).localLength o = 1 := fun _ _ => rfl
  have hscale : ∀ (X : Var ScaleVec.Inputs (F circomPrime)) o,
      (subcircuit ScaleVec.circuit X).localLength o = 4 := fun _ _ => rfl
  have hwf : ∀ (compute : ProverEnvironment (F circomPrime) → F circomPrime) o,
      (witnessField compute).localLength o = 1 := fun _ _ => rfl
  unfold main
  simp only [
    Witnessable.witness_eq,
    Circuit.bind_structuralComputableWitnesses_iff,
    Circuit.provableWitness_structuralComputableWitnesses_iff,
    Circuit.witnessField_structuralComputableWitnesses_iff,
    Circuit.assertZero_structuralComputableWitnesses_iff,
    FormalCircuit.subcircuit_structuralComputableWitnesses_iff,
    FormalAssertion.assertion_structuralComputableWitnesses_iff,
    hw, haz, hmulLooseWideB, hnmag, hscale, hwf]
  have hnl : numLimbs = 4 := rfl
  refine ⟨?_, trivial, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the inverse witness for the non-vanishing certificate
    intro _ hinput
    simp only [circuit_norm, Inputs.mk.injEq, SignedCoeff.mk.injEq] at hinput
    simp only [Expression.eval]
    rw [magnitudeExpr_stable v1 hinput.2.2.2.1.2 hinput.2.2.2.1.1,
      magnitudeExpr_stable v2 hinput.2.2.2.2.2 hinput.2.2.2.2.1]
  · -- W = λ·s mod n
    refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) scalarMulModLooseWideB _ _ _ ?_
      (MulModLooseCA.computableWitnessesWideB secpParams gfMul posOfMul 5 vMul vMul
        hgvMul hNfMul hNfMul) env env'
    intro k e e' _ _ hinput
    simp only [circuit_norm, Inputs.mk.injEq, SignedCoeff.mk.injEq,
      MulMod.Inputs.mk.injEq] at hinput ⊢
    exact ⟨by rw [show eigenvalueConst = emuConst eigenvalue from rfl,
        DivOrZero.eval_emuConst, DivOrZero.eval_emuConst], hinput.1,
      by rw [show nConst = emuConst scalarOrder from rfl,
        DivOrZero.eval_emuConst, DivOrZero.eval_emuConst]⟩
  · -- nm1
    refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) NegativeMagnitude.circuit _ _ _ ?_
      NegativeMagnitude.computableWitnesses env env'
    intro k e e' _ _ hinput
    simp only [circuit_norm, Inputs.mk.injEq, SignedCoeff.mk.injEq,
      NegativeMagnitude.Inputs.mk.injEq] at hinput ⊢
    exact ⟨hinput.2.1.1, magnitudeExpr_stable u1 hinput.2.1.2 hinput.2.1.1⟩
  · -- nm2
    refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) NegativeMagnitude.circuit _ _ _ ?_
      NegativeMagnitude.computableWitnesses env env'
    intro k e e' _ _ hinput
    simp only [circuit_norm, Inputs.mk.injEq, SignedCoeff.mk.injEq,
      NegativeMagnitude.Inputs.mk.injEq] at hinput ⊢
    exact ⟨hinput.2.2.1.1, magnitudeExpr_stable u2 hinput.2.2.1.2 hinput.2.2.1.1⟩
  · -- c = s · |v₁|
    refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) ScaleVec.circuit _ _ _ ?_
      ScaleVec.computableWitnesses env env'
    intro k e e' _ _ hinput
    simp only [circuit_norm, Inputs.mk.injEq, SignedCoeff.mk.injEq,
      ScaleVec.Inputs.mk.injEq] at hinput ⊢
    exact ⟨hinput.1, magnitudeExpr_stable v1 hinput.2.2.2.1.2 hinput.2.2.2.1.1⟩
  · -- d = c · sign(v₁)
    refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) ScaleVec.circuit _ _ _ ?_
      ScaleVec.computableWitnesses env env'
    intro k e e' hk hagree hinput
    simp only [circuit_norm, Inputs.mk.injEq, SignedCoeff.mk.injEq,
      ScaleVec.Inputs.mk.injEq] at hinput ⊢
    exact ⟨emu_map_eval_eq_of_eval_eq (scaleVecOutput_stable _ hagree (by omega)),
      hinput.2.2.2.1.1⟩
  · -- e = W · |v₂|
    refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) ScaleVec.circuit _ _ _ ?_
      ScaleVec.computableWitnesses env env'
    intro k e e' hk hagree hinput
    simp only [circuit_norm, Inputs.mk.injEq, SignedCoeff.mk.injEq,
      ScaleVec.Inputs.mk.injEq] at hinput ⊢
    exact ⟨emu_map_eval_eq_of_eval_eq (mulOutputLooseWideB_stable _ hagree (by omega)),
      magnitudeExpr_stable v2 hinput.2.2.2.2.2 hinput.2.2.2.2.1⟩
  · -- f = e · sign(v₂)
    refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) ScaleVec.circuit _ _ _ ?_
      ScaleVec.computableWitnesses env env'
    intro k e e' hk hagree hinput
    simp only [circuit_norm, Inputs.mk.injEq, SignedCoeff.mk.injEq,
      ScaleVec.Inputs.mk.injEq] at hinput ⊢
    exact ⟨emu_map_eval_eq_of_eval_eq (scaleVecOutput_stable _ hagree (by omega)),
      hinput.2.2.2.2.1⟩
  · -- the range check on the affine quotient
    refine FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) (RangeCheck.circuit qBitsRel (by decide) (by decide)) _ _ _ ?_
      (RangeCheck.computableWitnesses qBitsRel (by decide) (by decide)) env env'
    intro k e e' hk hagree hinput
    have hstable := mainQ_stable offset k
      { s := s, u1 := u1, u2 := u2, v1 := v1, v2 := v2 } hagree (by omega) hinput
    unfold mainQ mainNm1 mainNm2 mainC mainE mainD mainF mainW at hstable
    simp only [mainC, mainE, mainW] at hstable
    simpa only [circuit_norm] using hstable
  · -- the grouped equality certifying the integer identity
    refine FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs)
      (GroupedEqXV.circuitNoTop 64 gfFold posOfFold 3 vRelL vRelR hgvRel (by norm_num)) _ _ _ ?_
      (GroupedEqXV.computableWitnessesNoTop 64 gfFold posOfFold 3 vRelL vRelR hgvRel
        (by norm_num))
      env env'
    intro k e e' hk hagree hinput
    have hstable := mainGroupedInput_stable offset k
      { s := s, u1 := u1, u2 := u2, v1 := v1, v2 := v2 } hagree (by omega) hinput
    unfold mainGroupedInput mainQ mainNm1 mainNm2 mainC mainE mainD mainF mainW at hstable
    simp only [mainC, mainE, mainW] at hstable
    exact hstable

end GLVScalarRelation
end Solution.Secp256k1ScalarMul
