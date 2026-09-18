import Solution.Secp256k1ScalarMul.VarLookup
import Solution.Secp256k1ScalarMul.Cost
import Solution.Secp256k1ScalarMul.IsZeroFeSumR



namespace Solution.Secp256k1ScalarMul
namespace VarLookup


private lemma vec_entry_eval_eq {n : ℕ} {e e' : ProverEnvironment (F circomPrime)}
    {v : Vector (Var Emu (F circomPrime)) n}
    (h : eval e.toEnvironment v = eval e'.toEnvironment v) (i : ℕ) (hi : i < n) :
    Vector.map (Expression.eval e.toEnvironment) (v[i]'hi)
      = Vector.map (Expression.eval e'.toEnvironment) (v[i]'hi) := by
  have h1 := getElem_eval_vector (α := Emu) (env := e.toEnvironment) v i hi
  have h2 := getElem_eval_vector (α := Emu) (env := e'.toEnvironment) v i hi
  have hcong := congrArg (fun w : Vector (Emu (F circomPrime)) n => w[i]'hi) h
  simp only [] at hcong
  rw [← h1, ← h2] at hcong
  simpa only [ProvableType.eval_fields] using hcong


private lemma parent_decomp {e e' : ProverEnvironment (F circomPrime)}
    {tx ty : Vector (Var Emu (F circomPrime)) 16}
    {tinf : Vector (Expression (F circomPrime)) 16}
    {b3 b2 b1 b0 : Expression (F circomPrime)}
    (h : eval e (⟨tx, ty, tinf, b3, b2, b1, b0⟩ : Var Inputs (F circomPrime))
      = eval e' (⟨tx, ty, tinf, b3, b2, b1, b0⟩ : Var Inputs (F circomPrime))) :
    eval e.toEnvironment tx = eval e'.toEnvironment tx ∧
    eval e.toEnvironment ty = eval e'.toEnvironment ty ∧
    Vector.map (Expression.eval e.toEnvironment) tinf
      = Vector.map (Expression.eval e'.toEnvironment) tinf ∧
    Expression.eval e.toEnvironment b3 = Expression.eval e'.toEnvironment b3 ∧
    Expression.eval e.toEnvironment b2 = Expression.eval e'.toEnvironment b2 ∧
    Expression.eval e.toEnvironment b1 = Expression.eval e'.toEnvironment b1 ∧
    Expression.eval e.toEnvironment b0 = Expression.eval e'.toEnvironment b0 := by
  simpa only [circuit_norm, Inputs.mk.injEq] using h

set_option maxHeartbeats 3200000 in

private lemma cond_level1 {e e' : ProverEnvironment (F circomPrime)}
    (tx ty : Vector (Var Emu (F circomPrime)) 16)
    (tinf : Vector (Expression (F circomPrime)) 16)
    (b3 b2 b1 b0 : Expression (F circomPrime))
    (i j : ℕ) (hi : i < 16) (hj : j < 16)
    (h_in : eval e (⟨tx, ty, tinf, b3, b2, b1, b0⟩ : Var Inputs (F circomPrime))
      = eval e' (⟨tx, ty, tinf, b3, b2, b1, b0⟩ : Var Inputs (F circomPrime))) :
    eval e ({ selector := b0,
              ifTrue := { x := tx[i]'hi, y := ty[i]'hi },
              ifFalse := { x := tx[j]'hj, y := ty[j]'hj } }
      : Var (Mux.Inputs XY) (F circomPrime))
    = eval e' ({ selector := b0,
                 ifTrue := { x := tx[i]'hi, y := ty[i]'hi },
                 ifFalse := { x := tx[j]'hj, y := ty[j]'hj } }
      : Var (Mux.Inputs XY) (F circomPrime)) := by
  obtain ⟨htx, hty, -, -, -, -, hb0⟩ := parent_decomp h_in
  simp only [circuit_norm]; rw [Mux.Inputs.mk.injEq, XY.mk.injEq, XY.mk.injEq]
  exact ⟨hb0, ⟨vec_entry_eval_eq htx i hi, vec_entry_eval_eq hty i hi⟩,
    vec_entry_eval_eq htx j hj, vec_entry_eval_eq hty j hj⟩

set_option maxHeartbeats 3200000 in

private lemma cond_mux_pair {e e' : ProverEnvironment (F circomPrime)}
    (sel : Expression (F circomPrime))
    (hsel : Expression.eval e.toEnvironment sel = Expression.eval e'.toEnvironment sel)
    (X1 X2 : Var (Mux.Inputs XY) (F circomPrime)) (o1 o2 k : ℕ)
    (h_agree : e.AgreesBelow k e') (hk1 : o1 + 8 ≤ k) (hk2 : o2 + 8 ≤ k) :
    eval e ({ selector := sel,
              ifTrue := (subcircuit (Mux.circuit (M := XY)) X1).output o1,
              ifFalse := (subcircuit (Mux.circuit (M := XY)) X2).output o2 }
      : Var (Mux.Inputs XY) (F circomPrime))
    = eval e' ({ selector := sel,
                 ifTrue := (subcircuit (Mux.circuit (M := XY)) X1).output o1,
                 ifFalse := (subcircuit (Mux.circuit (M := XY)) X2).output o2 }
      : Var (Mux.Inputs XY) (F circomPrime)) := by
  simp only [circuit_norm]; rw [Mux.Inputs.mk.injEq]
  refine ⟨hsel, ?_, ?_⟩
  · have h := Mux.eval_output_of_agreesBelow (M := XY) X1 (offset := o1) h_agree
      (by rw [show size XY = 8 from rfl]; omega)
    simp only [circuit_norm] at h; exact h
  · have h := Mux.eval_output_of_agreesBelow (M := XY) X2 (offset := o2) h_agree
      (by rw [show size XY = 8 from rfl]; omega)
    simp only [circuit_norm] at h; exact h

/-- The `x` coordinate of a mux output only depends on the cells it occupies. -/
private lemma cond_mux_x {e e' : ProverEnvironment (F circomPrime)}
    (X : Var (Mux.Inputs XY) (F circomPrime)) (o k : ℕ)
    (h_agree : e.AgreesBelow k e') (hk : o + 8 ≤ k) :
    eval e ((subcircuit (Mux.circuit (M := XY)) X).output o).x
      = eval e' ((subcircuit (Mux.circuit (M := XY)) X).output o).x := by
  have h := Mux.eval_output_of_agreesBelow (M := XY) X (offset := o) h_agree
    (by rw [show size XY = 8 from rfl]; omega)
  simp only [circuit_norm] at h ⊢
  rw [VarLookup.XY.mk.injEq] at h
  exact h.1

set_option maxHeartbeats 12800000 in
theorem computableWitnesses : circuit.base.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  obtain ⟨tx, ty, tinf, b3, b2, b1, b0⟩ := input
  have hmxF : ∀ (X : Var (Mux.Inputs XY) (F circomPrime)) (o : ℕ),
      (subcircuit (Mux.circuit (M := XY)) X).localLength o = 8 := fun _ _ => rfl
  unfold main
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.pure_structuralComputableWitnesses_iff,
    and_true, hmxF]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- 1-8: level-0 blocks t01 .. tEF
  · exact Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) (Mux.circuit (M := XY)) _ _ _
      (fun k e e' _ _ h_in => cond_level1 tx ty tinf b3 b2 b1 b0 1 0 (by norm_num) (by norm_num) h_in)
      (Mux.computableWitnesses (M := XY)) env env'
  · exact Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) (Mux.circuit (M := XY)) _ _ _
      (fun k e e' _ _ h_in => cond_level1 tx ty tinf b3 b2 b1 b0 3 2 (by norm_num) (by norm_num) h_in)
      (Mux.computableWitnesses (M := XY)) env env'
  · exact Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) (Mux.circuit (M := XY)) _ _ _
      (fun k e e' _ _ h_in => cond_level1 tx ty tinf b3 b2 b1 b0 5 4 (by norm_num) (by norm_num) h_in)
      (Mux.computableWitnesses (M := XY)) env env'
  · exact Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) (Mux.circuit (M := XY)) _ _ _
      (fun k e e' _ _ h_in => cond_level1 tx ty tinf b3 b2 b1 b0 7 6 (by norm_num) (by norm_num) h_in)
      (Mux.computableWitnesses (M := XY)) env env'
  · exact Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) (Mux.circuit (M := XY)) _ _ _
      (fun k e e' _ _ h_in => cond_level1 tx ty tinf b3 b2 b1 b0 9 8 (by norm_num) (by norm_num) h_in)
      (Mux.computableWitnesses (M := XY)) env env'
  · exact Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) (Mux.circuit (M := XY)) _ _ _
      (fun k e e' _ _ h_in => cond_level1 tx ty tinf b3 b2 b1 b0 11 10 (by norm_num) (by norm_num) h_in)
      (Mux.computableWitnesses (M := XY)) env env'
  · exact Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) (Mux.circuit (M := XY)) _ _ _
      (fun k e e' _ _ h_in => cond_level1 tx ty tinf b3 b2 b1 b0 13 12 (by norm_num) (by norm_num) h_in)
      (Mux.computableWitnesses (M := XY)) env env'
  · exact Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) (Mux.circuit (M := XY)) _ _ _
      (fun k e e' _ _ h_in => cond_level1 tx ty tinf b3 b2 b1 b0 15 14 (by norm_num) (by norm_num) h_in)
      (Mux.computableWitnesses (M := XY)) env env'
  -- 9-12: level-1 blocks u0 .. u3
  · refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) (Mux.circuit (M := XY)) _ _ _ ?_
      (Mux.computableWitnesses (M := XY)) env env'
    intro k e e' hle h_agree h_in
    simp only [circuit_norm] at hle
    exact cond_mux_pair b1 (parent_decomp h_in).2.2.2.2.2.1 _ _ _ _ k h_agree
      (by omega) (by omega)
  · refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) (Mux.circuit (M := XY)) _ _ _ ?_
      (Mux.computableWitnesses (M := XY)) env env'
    intro k e e' hle h_agree h_in
    simp only [circuit_norm] at hle
    exact cond_mux_pair b1 (parent_decomp h_in).2.2.2.2.2.1 _ _ _ _ k h_agree
      (by omega) (by omega)
  · refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) (Mux.circuit (M := XY)) _ _ _ ?_
      (Mux.computableWitnesses (M := XY)) env env'
    intro k e e' hle h_agree h_in
    simp only [circuit_norm] at hle
    exact cond_mux_pair b1 (parent_decomp h_in).2.2.2.2.2.1 _ _ _ _ k h_agree
      (by omega) (by omega)
  · refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) (Mux.circuit (M := XY)) _ _ _ ?_
      (Mux.computableWitnesses (M := XY)) env env'
    intro k e e' hle h_agree h_in
    simp only [circuit_norm] at hle
    exact cond_mux_pair b1 (parent_decomp h_in).2.2.2.2.2.1 _ _ _ _ k h_agree
      (by omega) (by omega)
  -- 13-14: level-2 blocks v0, v1
  · refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) (Mux.circuit (M := XY)) _ _ _ ?_
      (Mux.computableWitnesses (M := XY)) env env'
    intro k e e' hle h_agree h_in
    simp only [circuit_norm] at hle
    exact cond_mux_pair b2 (parent_decomp h_in).2.2.2.2.1 _ _ _ _ k h_agree
      (by omega) (by omega)
  · refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) (Mux.circuit (M := XY)) _ _ _ ?_
      (Mux.computableWitnesses (M := XY)) env env'
    intro k e e' hle h_agree h_in
    simp only [circuit_norm] at hle
    exact cond_mux_pair b2 (parent_decomp h_in).2.2.2.2.1 _ _ _ _ k h_agree
      (by omega) (by omega)
  -- 15: level-3 block w
  · refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) (Mux.circuit (M := XY)) _ _ _ ?_
      (Mux.computableWitnesses (M := XY)) env env'
    intro k e e' hle h_agree h_in
    simp only [circuit_norm] at hle
    exact cond_mux_pair b3 (parent_decomp h_in).2.2.2.1 _ _ _ _ k h_agree
      (by omega) (by omega)
  -- 16: the zero test on the selected `x`
  · refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) IsZeroFeSumR.circuit _ _ _ ?_
      IsZeroFeSumR.computableWitnesses env env'
    intro k e e' hle h_agree _
    simp only [circuit_norm] at hle
    exact cond_mux_x _ _ k h_agree (by omega)

theorem computableWitness : ∀ n input,
    ProverEnvironment.OnlyAccessedBelow n
      (fun env : ProverEnvironment (F circomPrime) => eval env input) →
    Circuit.ComputableWitnesses (main input) n :=
  Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnesses_implies
    (circuit := circuit.base) computableWitnesses


private lemma fpVar_stable {off k : ℕ} {env env' : ProverEnvironment (F circomPrime)}
    (h_agree : env.AgreesBelow k env') (hk : off + size FlaggedPoint ≤ k) :
    eval env ((varFromOffset FlaggedPoint off : FlaggedPoint (Expression (F circomPrime))))
      = eval env' ((varFromOffset FlaggedPoint off : FlaggedPoint (Expression (F circomPrime)))) := by
  rw [CircuitType.eval_expression_prover_to_verifier (M := FlaggedPoint),
    CircuitType.eval_expression_prover_to_verifier (M := FlaggedPoint), ProvableType.ext_iff]
  intro i hi
  rw [← ProvableType.getElem_eval_toElements
      (varFromOffset FlaggedPoint off : FlaggedPoint (Expression (F circomPrime))) i hi,
    ← ProvableType.getElem_eval_toElements
      (varFromOffset FlaggedPoint off : FlaggedPoint (Expression (F circomPrime))) i hi]
  simp only [varFromOffset, ProvableType.toElements_fromElements, Vector.getElem_mapRange,
    Expression.eval]
  exact h_agree (off + i) (by omega)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
/-- The circuit's output is the contiguous block of nine cells starting at
`offset + 112`: the final coordinate mux followed by the recovered flag. -/
theorem output_eq (input : Var Inputs (F circomPrime)) (offset : ℕ) :
    (main input).output offset = varFromOffset FlaggedPoint (offset + 112) := by
  simp only [circuit_norm, main, Mux.circuit, Mux.elaborated,
    IsZeroFeSumR.circuit, IsZeroFeSumR.elaborated, varFromOffset]
  rfl


lemma eval_output_of_agreesBelow (input : Var Inputs (F circomPrime)) {offset k : ℕ}
    {env env' : ProverEnvironment (F circomPrime)}
    (h_agree : env.AgreesBelow k env') (hk : offset + 122 ≤ k) :
    eval env ((main input).output offset) = eval env' ((main input).output offset) := by
  rw [output_eq input offset]
  have hsz : size FlaggedPoint = 9 := rfl
  exact fpVar_stable (off := offset + 112) h_agree (by rw [hsz]; omega)


lemma eval_subOutput_of_agreesBelow (input : Var Inputs (F circomPrime)) {offset k : ℕ}
    {env env' : ProverEnvironment (F circomPrime)}
    (h_agree : env.AgreesBelow k env') (hk : offset + 122 ≤ k) :
    eval env ((subcircuit circuit input).output offset)
      = eval env' ((subcircuit circuit input).output offset) := by
  have h := eval_output_of_agreesBelow input h_agree hk
  rw [elaborated.output_eq input offset] at h
  exact h

end VarLookup

namespace Cost

open Challenge.CostR1CS

attribute [local irreducible] isR1CSRow r1csProducts operationsIsR1CS flatOperationsIsR1CS

/-- Affineness of a coordinate pair. -/
def AffineXY (v : Var VarLookup.XY (F circomPrime)) : Prop :=
  AffineW v.x ∧ AffineW v.y

theorem AffineXY.affineProvable {v : Var VarLookup.XY (F circomPrime)} (h : AffineXY v) :
    AffineProvable v := by
  obtain ⟨hx, hy⟩ := h
  intro j hj
  simp only [circuit_norm, explicit_provable_type]
  exact AffineW.append hx hy j hj

theorem affineW_mux_x (b : Var (Mux.Inputs VarLookup.XY) (F circomPrime)) (n : ℕ) :
    AffineW ((subcircuit (Mux.circuit (M := VarLookup.XY)) b).output n).x := by
  simp only [circuit_norm, subcircuit, Mux.circuit, Mux.elaborated]
  exact affineW_mapRange_var _

def varLookupCost : Count := ⟨122, 122⟩

theorem costIs_varLookup (input : Var VarLookup.Inputs (F circomPrime)) :
    CostIs (VarLookup.main input) varLookupCost := by
  rw [show varLookupCost = (⟨8, 8⟩ : Count) + (⟨8, 8⟩ + (⟨8, 8⟩ + (⟨8, 8⟩ + (⟨8, 8⟩ + (⟨8, 8⟩ + (⟨8, 8⟩ + (⟨8, 8⟩ + (⟨8, 8⟩ + (⟨8, 8⟩ + (⟨8, 8⟩ + (⟨8, 8⟩ + (⟨8, 8⟩ + (⟨8, 8⟩ + (⟨8, 8⟩ + (⟨2, 2⟩ + (Count.zero))))))))))))))))
        from by decide]
  unfold VarLookup.main
  refine CostIs.bind (costIs_sub_mux _) fun t01 => ?_
  refine CostIs.bind (costIs_sub_mux _) fun t23 => ?_
  refine CostIs.bind (costIs_sub_mux _) fun t45 => ?_
  refine CostIs.bind (costIs_sub_mux _) fun t67 => ?_
  refine CostIs.bind (costIs_sub_mux _) fun t89 => ?_
  refine CostIs.bind (costIs_sub_mux _) fun tAB => ?_
  refine CostIs.bind (costIs_sub_mux _) fun tCD => ?_
  refine CostIs.bind (costIs_sub_mux _) fun tEF => ?_
  refine CostIs.bind (costIs_sub_mux _) fun u0 => ?_
  refine CostIs.bind (costIs_sub_mux _) fun u1 => ?_
  refine CostIs.bind (costIs_sub_mux _) fun u2 => ?_
  refine CostIs.bind (costIs_sub_mux _) fun u3 => ?_
  refine CostIs.bind (costIs_sub_mux _) fun v0 => ?_
  refine CostIs.bind (costIs_sub_mux _) fun v1 => ?_
  refine CostIs.bind (costIs_sub_mux _) fun w => ?_
  exact CostIs.bind (costIs_sub_isZeroFeSumR _) fun z => CostIs.pure _

theorem costIs_sub_varLookup (b : Var VarLookup.Inputs (F circomPrime)) :
    CostIs (subcircuit VarLookup.circuit b) varLookupCost :=
  CostIs.subcircuit fun n => costIs_varLookup b n

theorem isR1CS_varLookup (input : Var VarLookup.Inputs (F circomPrime))
    (htab : AffineTableV input.tx input.ty input.tinf)
    (hb3 : Affine input.b3) (hb2 : Affine input.b2)
    (hb1 : Affine input.b1) (hb0 : Affine input.b0) :
    IsR1CSCirc (VarLookup.main input) := by
  obtain ⟨htx, hty, -⟩ := htab
  have hentry : ∀ (i : ℕ) (h : i < 16),
      AffineProvable
        ({ x := input.tx[i]'h, y := input.ty[i]'h } : Var VarLookup.XY (F circomPrime)) :=
    fun i h => AffineXY.affineProvable ⟨htx i h, hty i h⟩
  unfold VarLookup.main
  refine IsR1CSCirc.bind_out (isR1CS_sub_mux _ hb0 (hentry 1 (by norm_num)) (hentry 0 (by norm_num))) fun t01 => ?_
  refine IsR1CSCirc.bind_out (isR1CS_sub_mux _ hb0 (hentry 3 (by norm_num)) (hentry 2 (by norm_num))) fun t23 => ?_
  refine IsR1CSCirc.bind_out (isR1CS_sub_mux _ hb0 (hentry 5 (by norm_num)) (hentry 4 (by norm_num))) fun t45 => ?_
  refine IsR1CSCirc.bind_out (isR1CS_sub_mux _ hb0 (hentry 7 (by norm_num)) (hentry 6 (by norm_num))) fun t67 => ?_
  refine IsR1CSCirc.bind_out (isR1CS_sub_mux _ hb0 (hentry 9 (by norm_num)) (hentry 8 (by norm_num))) fun t89 => ?_
  refine IsR1CSCirc.bind_out (isR1CS_sub_mux _ hb0 (hentry 11 (by norm_num)) (hentry 10 (by norm_num))) fun tAB => ?_
  refine IsR1CSCirc.bind_out (isR1CS_sub_mux _ hb0 (hentry 13 (by norm_num)) (hentry 12 (by norm_num))) fun tCD => ?_
  refine IsR1CSCirc.bind_out (isR1CS_sub_mux _ hb0 (hentry 15 (by norm_num)) (hentry 14 (by norm_num))) fun tEF => ?_
  refine IsR1CSCirc.bind_out (isR1CS_sub_mux _ hb1 (affineProvable_sub_mux _ _) (affineProvable_sub_mux _ _)) fun u0 => ?_
  refine IsR1CSCirc.bind_out (isR1CS_sub_mux _ hb1 (affineProvable_sub_mux _ _) (affineProvable_sub_mux _ _)) fun u1 => ?_
  refine IsR1CSCirc.bind_out (isR1CS_sub_mux _ hb1 (affineProvable_sub_mux _ _) (affineProvable_sub_mux _ _)) fun u2 => ?_
  refine IsR1CSCirc.bind_out (isR1CS_sub_mux _ hb1 (affineProvable_sub_mux _ _) (affineProvable_sub_mux _ _)) fun u3 => ?_
  refine IsR1CSCirc.bind_out (isR1CS_sub_mux _ hb2 (affineProvable_sub_mux _ _) (affineProvable_sub_mux _ _)) fun v0 => ?_
  refine IsR1CSCirc.bind_out (isR1CS_sub_mux _ hb2 (affineProvable_sub_mux _ _) (affineProvable_sub_mux _ _)) fun v1 => ?_
  refine IsR1CSCirc.bind_out (isR1CS_sub_mux _ hb3 (affineProvable_sub_mux _ _) (affineProvable_sub_mux _ _)) fun w => ?_
  exact IsR1CSCirc.bind_out (isR1CS_sub_isZeroFeSumR _ (affineW_mux_x _ _)) fun z => IsR1CSCirc.pure _

theorem isR1CS_sub_varLookup (b : Var VarLookup.Inputs (F circomPrime))
    (htab : AffineTableV b.tx b.ty b.tinf)
    (hb3 : Affine b.b3) (hb2 : Affine b.b2) (hb1 : Affine b.b1) (hb0 : Affine b.b0) :
    IsR1CSCirc (subcircuit VarLookup.circuit b) :=
  IsR1CSCirc.subcircuit fun n => isR1CS_varLookup b htab hb3 hb2 hb1 hb0 n

set_option maxRecDepth 4000 in
theorem affineFP_sub_varLookup (b : Var VarLookup.Inputs (F circomPrime)) (n : ℕ) :
    AffineFP ((subcircuit VarLookup.circuit b).output n) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [circuit_norm, subcircuit, VarLookup.circuit, VarLookup.elaborated]
  · exact affineW_mapRange_var _
  · exact affineW_mapRange_var _
  · exact Affine.var _

theorem affineProvable_sub_varLookup (b : Var VarLookup.Inputs (F circomPrime)) (n : ℕ) :
    AffineProvable ((subcircuit VarLookup.circuit b).output n) :=
  (affineFP_sub_varLookup b n).affineProvable

end Cost
end Solution.Secp256k1ScalarMul
