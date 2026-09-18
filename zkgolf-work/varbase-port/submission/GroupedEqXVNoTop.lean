import Solution.Secp256k1ScalarMul.GroupedEqXV

/-!
# `GroupedEqXV` without the final native-field row

The carry loop already proves equality over the bounded integer representatives.
At quotient-inversion call sites, the native polynomial identity is true by
construction, so asserting it again costs one redundant R1CS row.  This wrapper
moves that identity into the formal assumptions and omits the row.
-/

namespace Solution.Secp256k1ScalarMul

section
variable {p : ℕ} [Fact p.Prime]
variable {L : ℕ} [NeZero L]

namespace GroupedEqXV

/-- The native-field identity asserted by the deleted final row. -/
def LinIdent (B : ℕ) (input : GroupedEqX.InputsX L (F p)) : Prop :=
  (∑ i : Fin L, input.lhs[i.val] * ((2 : F p) ^ B) ^ i.val)
    = ∑ i : Fin L, input.rhs[i.val] * ((2 : F p) ^ B) ^ i.val

/-- Ordinary coefficient bounds plus the native identity supplied by a caller. -/
def AssumptionsNoTop (B : ℕ) (NfL NfR : ℕ → ℕ)
    (input : GroupedEqX.InputsX L (F p)) : Prop :=
  Assumptions NfL NfR input ∧ LinIdent B input

/-- `main` with its final native-field equality row removed. -/
def mainNoTop (B : ℕ) (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GVXHyps p L B gf posOf G V VR) [Fact (p > 2)]
    (input : Var (GroupedEqX.InputsX L) (F p)) : Circuit (F p) Unit :=
  carryLoop B gf posOf VR.OFFf V.Wf hgv.2.2.2.1 input.lhs input.rhs (G - 2) 0

omit [NeZero L] in
lemma main_eq_bind_noTop (B : ℕ) (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GVXHyps p L B gf posOf G V VR) [Fact (p > 2)]
    (input : Var (GroupedEqX.InputsX L) (F p)) :
    main B gf posOf G V VR hgv input
      = (mainNoTop B gf posOf G V VR hgv input >>= fun _ =>
          assertZero
            (MulMod.polyEvalExpr
              (Vector.ofFn fun j : Fin L =>
                input.lhs[j.val]'j.isLt - input.rhs[j.val]'j.isLt)
              ((2 : F p) ^ B))) := rfl

instance elaboratedNoTop (B : ℕ) (gf posOf : ℕ → ℕ) (G : ℕ)
    (V VR : GroupedEqV.VParams) (hgv : GVXHyps p L B gf posOf G V VR)
    [Fact (p > 2)] :
    ElaboratedCircuit (F p) (GroupedEqX.InputsX L) unit
      (mainNoTop B gf posOf G V VR hgv) where
  localLength _ := widthAllocFrom V.Wf (G - 2) 0
  localLength_eq := by
    intro input offset
    simp only [mainNoTop,
      carryLoop_localLength B gf posOf VR.OFFf V.Wf hgv.2.2.2.1 input.lhs input.rhs]
  subcircuitsConsistent := by
    intro input offset
    exact carryLoop_subcircuitsConsistent B gf posOf VR.OFFf V.Wf hgv.2.2.2.1
      _ _ _ _ offset
  channelsLawful := by
    intro input offset
    exact carryLoop_channelsLawful B gf posOf VR.OFFf V.Wf hgv.2.2.2.1 _ _ _ _ _

def circuitNoTop (B : ℕ) (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GVXHyps p L B gf posOf G V VR) (hB1 : 1 ≤ B)
    [Fact (p > 2)] : FormalAssertion (F p) (GroupedEqX.InputsX L) where
  main := mainNoTop B gf posOf G V VR hgv
  Assumptions := AssumptionsNoTop B V.Nf VR.Nf
  Spec := GroupedEqX.Spec B L
  soundness := by
    intro i₀ env input_var input h_input h_assumptions h_holds
    have ha_e : ∀ (j : ℕ) (hj : j < L),
        Expression.eval env (input_var.lhs[j]'hj) = input.lhs[j]'hj := by
      intro j hj
      simpa [circuit_norm, CircuitType.eval_expression, ProvableType.eval,
        explicit_provable_type, Vector.getElem_map] using
          congrArg (fun x : GroupedEqX.InputsX L (F p) => x.lhs[j]'hj) h_input
    have hb_e : ∀ (j : ℕ) (hj : j < L),
        Expression.eval env (input_var.rhs[j]'hj) = input.rhs[j]'hj := by
      intro j hj
      simpa [circuit_norm, CircuitType.eval_expression, ProvableType.eval,
        explicit_provable_type, Vector.getElem_map] using
          congrArg (fun x : GroupedEqX.InputsX L (F p) => x.rhs[j]'hj) h_input
    have hrow : Expression.eval env
        (MulMod.polyEvalExpr
          (Vector.ofFn fun j : Fin L =>
            input_var.lhs[j.val]'j.isLt - input_var.rhs[j.val]'j.isLt)
          ((2 : F p) ^ B)) = 0 := by
      rw [polyEvalExpr_diff_eval]
      have hl : (∑ i : Fin L, Expression.eval env (input_var.lhs[i.val]'i.isLt)
            * ((2 : F p) ^ B) ^ i.val)
          = ∑ i : Fin L, input.lhs[i.val]'i.isLt * ((2 : F p) ^ B) ^ i.val :=
        Finset.sum_congr rfl (fun i _ => by rw [ha_e i.val i.isLt])
      have hr : (∑ i : Fin L, Expression.eval env (input_var.rhs[i.val]'i.isLt)
            * ((2 : F p) ^ B) ^ i.val)
          = ∑ i : Fin L, input.rhs[i.val]'i.isLt * ((2 : F p) ^ B) ^ i.val :=
        Finset.sum_congr rfl (fun i _ => by rw [hb_e i.val i.isLt])
      rw [hl, hr, h_assumptions.2, sub_self]
    have hfull : ConstraintsHold.Soundness env
        ((main B gf posOf G V VR hgv input_var).operations i₀) := by
      rw [main_eq_bind_noTop, Circuit.bind_operations_eq]
      rw [ConstraintsHold.Soundness, Operations.forAllNoOffset_append]
      refine ⟨h_holds, ?_⟩
      simpa [circuit_norm] using hrow
    obtain ⟨hspec, _⟩ :=
      (circuit B gf posOf G V VR hgv hB1).soundness i₀ env input_var input h_input
        h_assumptions.1 hfull
    refine ⟨hspec, ?_⟩
    exact carryLoop_requirements B gf posOf VR.OFFf V.Wf hgv.2.2.2.1 env
      input_var.lhs input_var.rhs _ _ _
  completeness := by
    intro i₀ env input_var h_uses input h_input h_assumptions h_spec
    have h_uses_full : env.UsesLocalWitnessesCompleteness i₀
        ((main B gf posOf G V VR hgv input_var).operations i₀) := by
      rw [main_eq_bind_noTop]
      simp only [circuit_norm]
      exact h_uses
    have hfull : ConstraintsHold.Completeness env
        ((main B gf posOf G V VR hgv input_var).operations i₀) :=
      (circuit B gf posOf G V VR hgv hB1).completeness i₀ env input_var
        h_uses_full input h_input h_assumptions.1 h_spec
    rw [main_eq_bind_noTop, Circuit.bind_operations_eq, ConstraintsHold.Completeness,
      Operations.forAllNoOffset_append] at hfull
    exact hfull.1

theorem computableWitnessesNoTop (B : ℕ) (gf posOf : ℕ → ℕ) (G : ℕ)
    (V VR : GroupedEqV.VParams) (hgv : GVXHyps p L B gf posOf G V VR)
    (hB1 : 1 ≤ B) [Fact (p > 2)] :
    (circuitNoTop B gf posOf G V VR hgv hB1).ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition
      input env env')
    ((mainNoTop B gf posOf G V VR hgv input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold mainNoTop
  exact carryLoop_structuralComputableWitnesses B gf posOf VR.OFFf V.Wf
    hgv.2.2.2.1 input input.lhs input.rhs env env'
    (by
      intro e e' h_parent k
      have hparts :
          (∀ a ∈ input.lhs, Expression.eval e.toEnvironment a =
              Expression.eval e'.toEnvironment a) ∧
            ∀ a ∈ input.rhs, Expression.eval e.toEnvironment a =
              Expression.eval e'.toEnvironment a := by
        simpa [circuit_norm, CircuitType.eval_expression_prover_to_verifier,
          CircuitType.eval_expression, ProvableType.eval, explicit_provable_type] using h_parent
      exact carryExpr_eval_stable B gf posOf VR.OFFf
        e.toEnvironment e'.toEnvironment input.lhs input.rhs
        (fun j hj => hparts.1 _ (by
          simp only [Vector.mem_iff_getElem]
          exact ⟨j, hj, rfl⟩))
        (fun j hj => hparts.2 _ (by
          simp only [Vector.mem_iff_getElem]
          exact ⟨j, hj, rfl⟩)) k)
    (G - 2) 0 offset

end GroupedEqXV

end

end Solution.Secp256k1ScalarMul
