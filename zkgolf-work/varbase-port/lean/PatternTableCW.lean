import Solution.Secp256k1ScalarMul.Lazy.PatternTableCost
import Solution.Secp256k1ScalarMul.NegYAffineCW

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

theorem structuralComputableWitnesses (offset : ℕ) (b : Var Bases CF) (env env' : PE) :
    FormalCircuitBase.Operations.StructuralComputableWitnesses b env env' offset
      ((main b).operations offset) := by
  have hpa : ∀ (X : Var PhiPairAdd.Inputs CF) (o : ℕ),
      (subcircuit PhiPairAdd.circuit X).localLength o = 1188 := fun _ _ => rfl
  have hca : ∀ (X : Var CompleteAdd.Inputs CF) (o : ℕ),
      (subcircuit CompleteAdd.circuit X).localLength o = 1235 := fun _ _ => rfl
  have hmux : ∀ (X : Var (Mux.Inputs Emu) CF) (o : ℕ),
      (subcircuit (Mux.circuit (M := Emu)) X).localLength o = 4 := fun _ _ => rfl
  have hneg : ∀ (X : VP) (o : ℕ), (subcircuit NegYAffine.circuit X).localLength o = 68 :=
    fun _ _ => rfl
  simp only [main, negCanon, Circuit.bind_structuralComputableWitnesses_iff,
    FormalCircuit.subcircuit_structuralComputableWitnesses_iff,
    Circuit.pure_structuralComputableWitnesses_iff, Circuit.bind_output_eq, Circuit.pure_output_eq,
    hpa, hca, hmux, hneg, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
        (Parent := Bases) NegYAffine.circuit _ _ _ ?_ NegYAffine.computableWitnesses env env')
    | (refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
        (Parent := Bases) PhiPairAdd.circuit _ _ _ ?_ PhiPairAdd.computableWitnesses env env')
    | (refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
        (Parent := Bases) (Mux.circuit (M := Emu)) _ _ _ ?_ (Mux.computableWitnesses (M := Emu)) env env')
    | (refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
        (Parent := Bases) CompleteAdd.circuit _ _ _ ?_ CompleteAdd.computableWitnesses env env')
  all_goals
    intro k e e' hle h_agree h_in
    obtain ⟨hr0, hr1, hr2, hr3⟩ := bases_parts b h_in
    try simp only [circuit_norm] at hle
  all_goals first
    -- inputs of the two negations
    | exact hr1
    | exact hr3
    -- pair additions
    | exact cond_phiPairAdd _ _ hr0 hr1
    | exact cond_phiPairAdd _ _ hr0 (withY_stable _ _ hr1 (negY_output_stable _ hr1 h_agree (by omega)))
    | exact cond_phiPairAdd _ _ hr2 hr3
    | exact cond_phiPairAdd _ _ hr2 (withY_stable _ _ hr3 (negY_output_stable _ hr3 h_agree (by omega)))
    -- canonicalising muxes of `vp`, `vm` (x then y)
    | exact cond_muxEmu _ _ _
        (point_parts _ (phiPairAdd_output_stable _ (cond_phiPairAdd _ _ hr2 hr3) h_agree (by omega))).2.2
        zeroConst_emu_stable
        (point_parts _ (phiPairAdd_output_stable _ (cond_phiPairAdd _ _ hr2 hr3) h_agree (by omega))).1
    | exact cond_muxEmu _ _ _
        (point_parts _ (phiPairAdd_output_stable _ (cond_phiPairAdd _ _ hr2 hr3) h_agree (by omega))).2.2
        zeroConst_emu_stable
        (point_parts _ (phiPairAdd_output_stable _ (cond_phiPairAdd _ _ hr2 hr3) h_agree (by omega))).2.1
    | exact cond_muxEmu _ _ _
        (point_parts _ (phiPairAdd_output_stable _ (cond_phiPairAdd _ _ hr2
          (withY_stable _ _ hr3 (negY_output_stable _ hr3 h_agree (by omega)))) h_agree (by omega))).2.2
        zeroConst_emu_stable
        (point_parts _ (phiPairAdd_output_stable _ (cond_phiPairAdd _ _ hr2
          (withY_stable _ _ hr3 (negY_output_stable _ hr3 h_agree (by omega)))) h_agree (by omega))).1
    | exact cond_muxEmu _ _ _
        (point_parts _ (phiPairAdd_output_stable _ (cond_phiPairAdd _ _ hr2
          (withY_stable _ _ hr3 (negY_output_stable _ hr3 h_agree (by omega)))) h_agree (by omega))).2.2
        zeroConst_emu_stable
        (point_parts _ (phiPairAdd_output_stable _ (cond_phiPairAdd _ _ hr2
          (withY_stable _ _ hr3 (negY_output_stable _ hr3 h_agree (by omega)))) h_agree (by omega))).2.1
    -- negations inside `negCanon vp` / `negCanon vm`
    | exact withXY_stable _ _ _
        (phiPairAdd_output_stable _ (cond_phiPairAdd _ _ hr2 hr3) h_agree (by omega))
        (canon_muxes_stable _ (phiPairAdd_output_stable _ (cond_phiPairAdd _ _ hr2 hr3) h_agree (by omega))
          h_agree (by omega)).1
        (canon_muxes_stable _ (phiPairAdd_output_stable _ (cond_phiPairAdd _ _ hr2 hr3) h_agree (by omega))
          h_agree (by omega)).2
    | exact withXY_stable _ _ _
        (phiPairAdd_output_stable _ (cond_phiPairAdd _ _ hr2
          (withY_stable _ _ hr3 (negY_output_stable _ hr3 h_agree (by omega)))) h_agree (by omega))
        (canon_muxes_stable _ (phiPairAdd_output_stable _ (cond_phiPairAdd _ _ hr2
          (withY_stable _ _ hr3 (negY_output_stable _ hr3 h_agree (by omega)))) h_agree (by omega))
          h_agree (by omega)).1
        (canon_muxes_stable _ (phiPairAdd_output_stable _ (cond_phiPairAdd _ _ hr2
          (withY_stable _ _ hr3 (negY_output_stable _ hr3 h_agree (by omega)))) h_agree (by omega))
          h_agree (by omega)).2
    -- the eight complete additions
    | exact cond_completeAdd _ _
        (phiPairAdd_output_stable _ (cond_phiPairAdd _ _ hr0 hr1) h_agree (by omega))
        (negCanon_outputs_stable _ (phiPairAdd_output_stable _ (cond_phiPairAdd _ _ hr2 hr3)
          h_agree (by omega)) h_agree (by omega)).1
    | exact cond_completeAdd _ _
        (phiPairAdd_output_stable _ (cond_phiPairAdd _ _ hr0 hr1) h_agree (by omega))
        (negCanon_outputs_stable _ (phiPairAdd_output_stable _ (cond_phiPairAdd _ _ hr2 hr3)
          h_agree (by omega)) h_agree (by omega)).2
    | exact cond_completeAdd _ _
        (phiPairAdd_output_stable _ (cond_phiPairAdd _ _ hr0 hr1) h_agree (by omega))
        (negCanon_outputs_stable _ (phiPairAdd_output_stable _ (cond_phiPairAdd _ _ hr2
          (withY_stable _ _ hr3 (negY_output_stable _ hr3 h_agree (by omega)))) h_agree (by omega))
          h_agree (by omega)).1
    | exact cond_completeAdd _ _
        (phiPairAdd_output_stable _ (cond_phiPairAdd _ _ hr0 hr1) h_agree (by omega))
        (negCanon_outputs_stable _ (phiPairAdd_output_stable _ (cond_phiPairAdd _ _ hr2
          (withY_stable _ _ hr3 (negY_output_stable _ hr3 h_agree (by omega)))) h_agree (by omega))
          h_agree (by omega)).2
    | exact cond_completeAdd _ _
        (phiPairAdd_output_stable _ (cond_phiPairAdd _ _ hr0
          (withY_stable _ _ hr1 (negY_output_stable _ hr1 h_agree (by omega)))) h_agree (by omega))
        (negCanon_outputs_stable _ (phiPairAdd_output_stable _ (cond_phiPairAdd _ _ hr2 hr3)
          h_agree (by omega)) h_agree (by omega)).1
    | exact cond_completeAdd _ _
        (phiPairAdd_output_stable _ (cond_phiPairAdd _ _ hr0
          (withY_stable _ _ hr1 (negY_output_stable _ hr1 h_agree (by omega)))) h_agree (by omega))
        (negCanon_outputs_stable _ (phiPairAdd_output_stable _ (cond_phiPairAdd _ _ hr2 hr3)
          h_agree (by omega)) h_agree (by omega)).2
    | exact cond_completeAdd _ _
        (phiPairAdd_output_stable _ (cond_phiPairAdd _ _ hr0
          (withY_stable _ _ hr1 (negY_output_stable _ hr1 h_agree (by omega)))) h_agree (by omega))
        (negCanon_outputs_stable _ (phiPairAdd_output_stable _ (cond_phiPairAdd _ _ hr2
          (withY_stable _ _ hr3 (negY_output_stable _ hr3 h_agree (by omega)))) h_agree (by omega))
          h_agree (by omega)).1
    | exact cond_completeAdd _ _
        (phiPairAdd_output_stable _ (cond_phiPairAdd _ _ hr0
          (withY_stable _ _ hr1 (negY_output_stable _ hr1 h_agree (by omega)))) h_agree (by omega))
        (negCanon_outputs_stable _ (phiPairAdd_output_stable _ (cond_phiPairAdd _ _ hr2
          (withY_stable _ _ hr3 (negY_output_stable _ hr3 h_agree (by omega)))) h_agree (by omega))
          h_agree (by omega)).2
    -- canonicalising muxes and negations of the eight sums
    | exact cond_muxEmu _ _ _
        (point_parts _ (completeAdd_output_stable _ h_agree (by omega))).2.2
        zeroConst_emu_stable
        (point_parts _ (completeAdd_output_stable _ h_agree (by omega))).1
    | exact cond_muxEmu _ _ _
        (point_parts _ (completeAdd_output_stable _ h_agree (by omega))).2.2
        zeroConst_emu_stable
        (point_parts _ (completeAdd_output_stable _ h_agree (by omega))).2.1
    | exact withXY_stable _ _ _
        (completeAdd_output_stable _ h_agree (by omega))
        (canon_muxes_stable _ (completeAdd_output_stable _ h_agree (by omega)) h_agree (by omega)).1
        (canon_muxes_stable _ (completeAdd_output_stable _ h_agree (by omega)) h_agree (by omega)).2

theorem computableWitnesses : circuit.base.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (FormalCircuitBase.computableWitnessCondition input env env') ((main input).operations offset)
  exact FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
    input env env' (structuralComputableWitnesses offset input env env')

/-! ### Output stability -/

theorem output_stable (b : Var Bases CF) (n : ℕ) {k : ℕ} {e e' : PE}
    (h_agree : e.AgreesBelow k e') (hk : n + 15528 ≤ k) :
    eval e ((main b).output n) = eval e' ((main b).output n) := by
  have hpa : ∀ (X : Var PhiPairAdd.Inputs CF) (o : ℕ),
      (subcircuit PhiPairAdd.circuit X).localLength o = 1188 := fun _ _ => rfl
  have hca : ∀ (X : Var CompleteAdd.Inputs CF) (o : ℕ),
      (subcircuit CompleteAdd.circuit X).localLength o = 1235 := fun _ _ => rfl
  have hmux : ∀ (X : Var (Mux.Inputs Emu) CF) (o : ℕ),
      (subcircuit (Mux.circuit (M := Emu)) X).localLength o = 4 := fun _ _ => rfl
  have hneg : ∀ (X : VP) (o : ℕ), (subcircuit NegYAffine.circuit X).localLength o = 68 :=
    fun _ _ => rfl
  simp only [main, negCanon, Circuit.bind_output_eq, Circuit.pure_output_eq, hpa, hca, hmux, hneg]
  simp only [circuit_norm, RawTable.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | exact (negCanon_outputs_stable _ (completeAdd_output_stable _ h_agree (by omega))
        h_agree (by omega)).2
    | exact completeAdd_output_stable _ h_agree (by omega)
    | (simpa only [circuit_norm] using completeAdd_output_stable (off := _) _ h_agree (by omega))

theorem call_output_stable (b : Var Bases CF) (n : ℕ) {k : ℕ} {e e' : PE}
    (h_agree : e.AgreesBelow k e') (hk : n + 15528 ≤ k) :
    eval e ((subcircuit circuit b).output n) = eval e' ((subcircuit circuit b).output n) := by
  rw [show (subcircuit circuit b).output n = (main b).output n from (elaborated.output_eq b n).symm]
  exact output_stable b n h_agree hk

end Solution.Secp256k1ScalarMul.PatTable
