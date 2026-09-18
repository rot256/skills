import Solution.Secp256k1ScalarMul.ScalarMul
import Solution.Secp256k1ScalarMul.MainTheorems
import Solution.Secp256k1ScalarMul.GLVScalarMulCostCW
import Challenge.Instances.Secp256k1ScalarMul.Interface
import Challenge.Utils.ComputableWitnessLemmas

namespace Solution.Secp256k1ScalarMul

open Challenge.Instances.Secp256k1ScalarMul

def packCoord (v : Vector (Expression (F Interface.circomPrime)) Interface.coordBytes) :
    Var Emu (F Interface.circomPrime) :=
  Vector.ofFn fun k : Fin numLimbs =>
    Fin.foldl bytesPerLimb (fun acc t =>
      acc + v[Interface.coordBytes - 1 - (bytesPerLimb * k.val + t.val)]'(by
          have hk := k.isLt; have ht := t.isLt
          simp only [numLimbs, bytesPerLimb, Interface.coordBytes] at hk ht ⊢
          omega)
        * (((2 ^ (8 * t.val) : ℕ) : F Interface.circomPrime) : Expression (F Interface.circomPrime)))
      0

noncomputable def main (input : Var Interface.Input (F Interface.circomPrime)) :
    Circuit (F Interface.circomPrime) (Var Interface.Output (F Interface.circomPrime)) := do
  let out ← subcircuit GLVScalarMul.circuit
    { bits := input.bits, px := packCoord input.px, py := packCoord input.py }
  return { x := out.x, y := out.y, isInf := out.isInf }

noncomputable instance elaborated :
    ElaboratedCircuit (F Interface.circomPrime) Interface.Input Interface.Output main := by
  elaborate_circuit_naive

@[reducible] def allocations : Nat := 122710
@[reducible] def constraints : Nat := 123688

private theorem interfaceSpec_of_scalarSpec
    {input : Interface.Input (F Interface.circomPrime)}
    {x y : Vector (F Interface.circomPrime) Interface.coordBytes}
    {isInf : F Interface.circomPrime}
    (hvalid : ScalarMul.Outputs.Valid { x := x, y := y, isInf := isInf })
    (hspec : Specs.Secp256k1ScalarMul.Spec (input.bits.map ZMod.val)
      { x := Interface.decodeCoord input.px, y := Interface.decodeCoord input.py }
      (ScalarMul.decodeOutput { x := x, y := y, isInf := isInf }))
    {data : ProverData (F Interface.circomPrime)} :
    Interface.Spec input { x := x, y := y, isInf := isInf } data := by
  unfold Interface.Spec
  refine ⟨MainTheorems.outputValid_of_valid hvalid, ?_⟩
  rw [show Interface.decodeOutput { x := x, y := y, isInf := isInf } =
      ScalarMul.decodeOutput { x := x, y := y, isInf := isInf } from by
    simpa only using MainTheorems.decodeOutput_eq
      ({ x := x, y := y, isInf := isInf } :
        ScalarMul.Outputs (F Interface.circomPrime))]
  exact hspec

private theorem main_output_eq
    (input : Var Interface.Input (F Interface.circomPrime)) (n : ℕ) :
    elaborated.output input n =
      ({
        x := (GLVScalarMul.circuit.output
          { bits := input.bits, px := MainTheorems.packCoordE input.px,
            py := MainTheorems.packCoordE input.py } n).x
        y := (GLVScalarMul.circuit.output
          { bits := input.bits, px := MainTheorems.packCoordE input.px,
            py := MainTheorems.packCoordE input.py } n).y
        isInf := (GLVScalarMul.circuit.output
          { bits := input.bits, px := MainTheorems.packCoordE input.px,
            py := MainTheorems.packCoordE input.py } n).isInf
      } : Var Interface.Output (F Interface.circomPrime)) := by
  rw [← elaborated.output_eq]
  unfold main
  rw [Circuit.bind_output_eq, Circuit.pure_output_eq]
  rfl

set_option maxHeartbeats 200000 in
theorem soundness :
    GeneralFormalCircuit.Soundness (F Interface.circomPrime) main
      Interface.Assumptions Interface.Spec := by
  circuit_proof_start
  obtain ⟨h_bits_eq, h_px_eq, h_py_eq⟩ := h_input
  obtain ⟨h_bits, h_px_bytes, h_py_bytes, h_px_lt, h_py_lt, h_curve⟩ := h_assumptions
  rw [show GLVScalarMul.circuit.Assumptions = ScalarMul.Assumptions from rfl,
    show GLVScalarMul.circuit.Spec = ScalarMul.Spec from rfl,
    show packCoord = MainTheorems.packCoordE from rfl,
    MainTheorems.eval_packCoordE, MainTheorems.eval_packCoordE,
    h_px_eq, h_py_eq] at h_holds
  simp only [ScalarMul.Assumptions, ScalarMul.Spec] at h_holds
  obtain ⟨h_valid, h_spec⟩ := h_holds
    ⟨fun i => MainTheorems.isBool_of_val_lt_two (h_bits i),
     MainTheorems.pack_valid input_px h_px_bytes h_px_lt,
     MainTheorems.pack_valid input_py h_py_bytes h_py_lt,
     by rw [MainTheorems.decodeFe_pack input_px h_px_bytes,
            MainTheorems.decodeFe_pack input_py h_py_bytes]
        exact h_curve⟩
  refine ⟨?_, ?_⟩
  · rw [MainTheorems.decodeFe_pack input_px h_px_bytes,
        MainTheorems.decodeFe_pack input_py h_py_bytes] at h_spec
    change Interface.Spec { bits := input_bits, px := input_px, py := input_py }
      {
        x := Vector.map (Expression.eval env)
          (elaborated.output
            { bits := input_var_bits, px := input_var_px, py := input_var_py } i₀).x
        y := Vector.map (Expression.eval env)
          (elaborated.output
            { bits := input_var_bits, px := input_var_px, py := input_var_py } i₀).y
        isInf := Expression.eval env
          (elaborated.output
            { bits := input_var_bits, px := input_var_px, py := input_var_py } i₀).isInf
      } env.data
    rw [main_output_eq]
    simp only
    exact interfaceSpec_of_scalarSpec
      (input := { bits := input_bits, px := input_px, py := input_py })
      (x := Vector.map (Expression.eval env)
        (GLVScalarMul.circuit.output
          { bits := input_var_bits, px := MainTheorems.packCoordE input_var_px,
            py := MainTheorems.packCoordE input_var_py } i₀).x)
      (y := Vector.map (Expression.eval env)
        (GLVScalarMul.circuit.output
          { bits := input_var_bits, px := MainTheorems.packCoordE input_var_px,
            py := MainTheorems.packCoordE input_var_py } i₀).y)
      (isInf := Expression.eval env
        (GLVScalarMul.circuit.output
          { bits := input_var_bits, px := MainTheorems.packCoordE input_var_px,
            py := MainTheorems.packCoordE input_var_py } i₀).isInf)
      (data := env.data) h_valid h_spec
  · exact Or.inl rfl

set_option maxHeartbeats 4000000 in
theorem completeness :
    GeneralFormalCircuit.Completeness (F Interface.circomPrime) main
      Interface.ProverAssumptions Interface.ProverSpec := by
  circuit_proof_start
  obtain ⟨h_bits_eq, h_px_eq, h_py_eq⟩ := h_input
  obtain ⟨h_bits, h_px_bytes, h_py_bytes, h_px_lt, h_py_lt, h_curve⟩ := h_assumptions
  refine ⟨?_, trivial⟩
  rw [show GLVScalarMul.circuit.Assumptions = ScalarMul.Assumptions from rfl,
    show packCoord = MainTheorems.packCoordE from rfl,
    MainTheorems.eval_packCoordE, MainTheorems.eval_packCoordE,
    h_px_eq, h_py_eq]
  refine ⟨fun i => MainTheorems.isBool_of_val_lt_two (h_bits i),
    MainTheorems.pack_valid input_px h_px_bytes h_px_lt,
    MainTheorems.pack_valid input_py h_py_bytes h_py_lt, ?_⟩
  rw [MainTheorems.decodeFe_pack input_px h_px_bytes,
      MainTheorems.decodeFe_pack input_py h_py_bytes]
  exact h_curve

section Cost

open Challenge.CostR1CS
open Solution.Secp256k1ScalarMul.Cost

attribute [local irreducible] isR1CSRow r1csProducts operationsIsR1CS flatOperationsIsR1CS

private theorem affineW_packCoord (v : Vector (Expression (F Interface.circomPrime)) Interface.coordBytes)
    (hv : AffineW v) : AffineW (packCoord v) := by
  intro k hk
  unfold packCoord
  rw [Vector.getElem_ofFn]
  refine affine_finFoldl' _ _ Affine.zero fun acc t hacc => ?_
  exact Affine.add hacc (Affine.mul_deg0 (hv _ (by
    simp only [bytesPerLimb, Interface.coordBytes]
    omega)) (degree_const _))

private theorem costIs_main (input : Var Interface.Input (F Interface.circomPrime)) :
    CostIs (main input) ⟨allocations, constraints⟩ := by
  rw [show (⟨allocations, constraints⟩ : Count) = glvScalarMulCost + Count.zero from by decide]
  unfold main
  exact CostIs.bind (costIs_sub_glvScalarMul _) fun out => CostIs.pure _

theorem mainCost : Challenge.CostR1CS.circuitCost main ⟨allocations, constraints⟩ :=
  fun input => costIs_main input

private theorem isR1CS_main_param (input : Var Interface.Input (F Interface.circomPrime))
    (hbits : AffineW input.bits) (hpx : AffineW input.px) (hpy : AffineW input.py) :
    IsR1CSCirc (main input) := by
  unfold main
  refine IsR1CSCirc.bind_out (isR1CS_sub_glvScalarMul _ ?_) fun nout => ?_
  · exact ⟨fun i hi => hbits i hi, affineW_packCoord _ hpx,
      affineW_packCoord _ hpy⟩
  exact IsR1CSCirc.pure _

private theorem affineOutput_rewrap
    (c : Circuit (F Interface.circomPrime)
      (Var ScalarMul.Outputs (F Interface.circomPrime)))
    (h : ∀ n,
      AffineW (c.output n).x ∧
      AffineW (c.output n).y ∧
      Affine (c.output n).isInf) :
    AffineOutput (do
      let out ← c
      return ({ x := out.x, y := out.y, isInf := out.isInf } :
        Var Interface.Output (F Interface.circomPrime))) := by
  intro n
  rw [Circuit.bind_output_eq, Circuit.pure_output_eq]
  have hn := h n
  exact affineProvable_interfaceOutput hn.1 hn.2.1 hn.2.2

private theorem affineOutput_main (input : Var Interface.Input (F Interface.circomPrime)) :
    AffineOutput (main input) := by
  unfold main
  apply affineOutput_rewrap
  intro n
  exact affineOut_sub_glvScalarMul
    { bits := input.bits, px := packCoord input.px, py := packCoord input.py } n

theorem isR1CS : Challenge.CostR1CS.isR1CS main :=
  isR1CS_of_IsR1CSCirc
    (fun input hinput =>
      isR1CS_main_param input (affineInput_components input hinput).1
        (affineInput_components input hinput).2.1
        (affineInput_components input hinput).2.2)
    (fun input _ => affineOutput_main input)

end Cost

section ComputableWitness

open Challenge.Utils.ComputableWitnessLemmas

attribute [local irreducible] main GLVScalarMul.circuit GLVScalarMul.main

private lemma eval_packCoord_congr
    {e1 e2 : ProverEnvironment (F Interface.circomPrime)}
    (v : Vector (Expression (F Interface.circomPrime)) Interface.coordBytes)
    (h : Vector.map (Expression.eval e1.toEnvironment) v
        = Vector.map (Expression.eval e2.toEnvironment) v) :
    Vector.map (Expression.eval e1.toEnvironment) (packCoord v)
      = Vector.map (Expression.eval e2.toEnvironment) (packCoord v) := by
  rw [show packCoord = MainTheorems.packCoordE from rfl,
    MainTheorems.eval_packCoordE, MainTheorems.eval_packCoordE, h]

theorem computableWitness : ∀ n input,
  ProverEnvironment.OnlyAccessedBelow n
    (fun env : ProverEnvironment (F Interface.circomPrime) => eval env input) →
  Circuit.ComputableWitnesses (main input) n := by
  intro n input hinput env env'
  change (main input).operations n |>.forAllFlat n
    { witness := fun k _ compute => env.AgreesBelow k env' → compute env = compute env' }
  have hstruct :
      Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.StructuralComputableWitnesses
        input env env' n ((main input).operations n) := by
    unfold main
    simp only [
      Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
      Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_structuralComputableWitnesses_iff,
      Challenge.Utils.ComputableWitnessLemmas.Circuit.pure_structuralComputableWitnesses_iff, and_true]
    refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses
      GLVScalarMul.circuit input
      { bits := input.bits, px := packCoord input.px, py := packCoord input.py } n ?_
      GLVScalarMul.computableWitnesses env env'
    intro e1 e2 h_input_eq
    simp only [circuit_norm, ScalarMul.Inputs.mk.injEq]
    refine ⟨?_, ?_, ?_⟩
    · simpa [circuit_norm] using
        congrArg (fun x : Interface.Input (F Interface.circomPrime) => x.bits) h_input_eq
    · exact eval_packCoord_congr input.px
        (by simpa [circuit_norm] using
          congrArg (fun x : Interface.Input (F Interface.circomPrime) => x.px) h_input_eq)
    · exact eval_packCoord_congr input.py
        (by simpa [circuit_norm] using
          congrArg (fun x : Interface.Input (F Interface.circomPrime) => x.py) h_input_eq)
  have hflat :=
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
      input env env' hstruct
  unfold Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition at hflat
  rw [← Operations.forAll_toFlat_iff] at hflat ⊢
  let targetCondition : Condition (F Interface.circomPrime) :=
    { witness := fun k _ compute => env.AgreesBelow k env' → compute env = compute env' }
  apply FlatOperation.forAll_implies (F := F Interface.circomPrime) n ?_ hflat
  have himplies : ∀ (ops : List (FlatOperation (F Interface.circomPrime))) (off : ℕ),
      n ≤ off →
      FlatOperation.forAll off
        (Condition.implies
          (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition
            input env env')
          targetCondition).ignoreSubcircuit
        ops := by
    intro ops off hoff
    induction ops generalizing off with
    | nil => simp [FlatOperation.forAll]
    | cons op ops ih =>
      cases op with
      | witness m compute =>
          simp only [FlatOperation.forAll, Condition.implies, Condition.ignoreSubcircuit]
          constructor
          · intro hparent hagree
            exact hparent hagree
              (hinput env env' (ProverEnvironment.agreesBelow_of_le hagree hoff))
          · exact ih (m + off) (by omega)
      | assert e =>
          simp only [FlatOperation.forAll, Condition.implies, Condition.ignoreSubcircuit]
          exact ⟨by intro _; trivial, ih off hoff⟩
      | lookup l =>
          simp only [FlatOperation.forAll, Condition.implies, Condition.ignoreSubcircuit]
          exact ⟨by intro _; trivial, ih off hoff⟩
      | interact i =>
          simp only [FlatOperation.forAll, Condition.implies, Condition.ignoreSubcircuit]
          exact ⟨by intro _; trivial, ih off hoff⟩
  exact himplies ((main input).operations n).toFlat n (le_refl n)

end ComputableWitness

end Solution.Secp256k1ScalarMul
