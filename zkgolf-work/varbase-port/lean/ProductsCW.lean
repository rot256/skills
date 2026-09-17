import Solution.Secp256k1ScalarMul.Lazy.SquareCW

/-! Computable witnesses and output stability of the nine-product circuit. -/

namespace Solution.Secp256k1ScalarMulFixedBase.LazyVar.Products

open SmallSquare Sparse32 SparseX
open Challenge.CostR1CS Cost
open Challenge.Utils.ComputableWitnessLemmas


set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem input_eval_eq (i : Var Inputs Field) {e e' : ProverEnvironment Field}
    (h : eval e i = eval e' i) :
    Vector.map (Expression.eval e.toEnvironment) i.a =
        Vector.map (Expression.eval e'.toEnvironment) i.a ∧
    Vector.map (Expression.eval e.toEnvironment) i.b =
        Vector.map (Expression.eval e'.toEnvironment) i.b ∧
    Vector.map (Expression.eval e.toEnvironment) i.x =
        Vector.map (Expression.eval e'.toEnvironment) i.x ∧
    Vector.map (Expression.eval e.toEnvironment) i.y =
        Vector.map (Expression.eval e'.toEnvironment) i.y ∧
    Vector.map (Expression.eval e.toEnvironment) i.tx =
        Vector.map (Expression.eval e'.toEnvironment) i.tx ∧
    Vector.map (Expression.eval e.toEnvironment) i.ty =
        Vector.map (Expression.eval e'.toEnvironment) i.ty := by
  exact ⟨by simpa only [circuit_norm] using congrArg Inputs.a h,
    by simpa only [circuit_norm] using congrArg Inputs.b h,
    by simpa only [circuit_norm] using congrArg Inputs.x h,
    by simpa only [circuit_norm] using congrArg Inputs.y h,
    by simpa only [circuit_norm] using congrArg Inputs.tx h,
    by simpa only [circuit_norm] using congrArg Inputs.ty h⟩

theorem computableWitnesses : circuit.ComputableWitnesses := by
  intro n input env env'
  change Operations.forAllFlat n
    (FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations n)
  apply FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  simp only [main, Circuit.bind_structuralComputableWitnesses_iff,
    Circuit.pure_structuralComputableWitnesses_iff]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  all_goals
    rw [FormalCircuit.subcircuit_structuralComputableWitnesses_iff]
    apply FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
    rotate_left
    first
    | exact Solution.Secp256k1ScalarMul.Lazy.SquareCW.computableWitnesses
    | exact Sparse32Mul.computableWitnesses
  all_goals
    intro k e e' hk hag hp
    obtain ⟨ha, hb, hx, hy, htx, hty⟩ := input_eval_eq input hp
    simp only [xSExpr, xPExpr, circuit_norm, map_vaddE, map_vsubE, map_embedExpr,
      ha, hb, hx, hy, htx, hty]
  all_goals
    simp only [Sparse32Square.circuit, Sparse32Square.elaborated,
      Sparse32Mul.circuit, Sparse32Mul.elaborated, circuit_norm] at hk
    have hsa := Solution.Secp256k1ScalarMul.Lazy.SquareCW.output_stable input.a (n + 12 + 12 + 9 + 12 + 9) hag (by omega)
    simp only [Sparse32Square.circuit, Sparse32Square.elaborated, circuit_norm] at hsa
    simp only [Sparse32Square.circuit, Sparse32Square.elaborated,
      Sparse32Mul.circuit, Sparse32Mul.elaborated, circuit_norm, hsa]
  have hsb := Solution.Secp256k1ScalarMul.Lazy.SquareCW.output_stable input.b (n + 12 + 12 + 9 + 12 + 9 + 9 + 12) hag (by omega)
  simp only [Sparse32Square.circuit, Sparse32Square.elaborated, circuit_norm] at hsb
  simp only [hsb]

lemma mul_reconstruction_stable (n : ℕ) {k : ℕ} {env env' : ProverEnvironment Field}
    (hag : env.AgreesBelow k env') (hk : n + 12 ≤ k) :
    Vector.map (Expression.eval env.toEnvironment)
        (Sparse32Mul.outputExpr (Vector.mapRange 12 fun j => var { index := n + j })) =
      Vector.map (Expression.eval env'.toEnvironment)
        (Sparse32Mul.outputExpr (Vector.mapRange 12 fun j => var { index := n + j })) := by
  have h := Sparse32Mul.output_stable ⟨default, default⟩ n hag hk
  simpa only [Sparse32Mul.circuit, Sparse32Mul.elaborated, circuit_norm] using h

lemma square_reconstruction_stable (n : ℕ) {k : ℕ} {env env' : ProverEnvironment Field}
    (hag : env.AgreesBelow k env') (hk : n + 9 ≤ k) :
    Vector.map (Expression.eval env.toEnvironment)
        (Sparse32Square.outputExpr (Vector.mapRange 9 fun j => var { index := n + j })) =
      Vector.map (Expression.eval env'.toEnvironment)
        (Sparse32Square.outputExpr (Vector.mapRange 9 fun j => var { index := n + j })) := by
  have h := Solution.Secp256k1ScalarMul.Lazy.SquareCW.output_stable default n hag hk
  simpa only [Sparse32Square.circuit, Sparse32Square.elaborated, circuit_norm] using h

theorem output_stable (i : Var Inputs Field) (n : ℕ) {k : ℕ}
    {env env' : ProverEnvironment Field} (hag : env.AgreesBelow k env')
    (hk : n + 96 ≤ k) : eval env ((main i).output n) = eval env' ((main i).output n) := by
  simp only [main, Sparse32Square.circuit, Sparse32Square.elaborated,
    Sparse32Mul.circuit, Sparse32Mul.elaborated, circuit_norm, Outputs.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | exact mul_reconstruction_stable _ hag (by omega)
    | exact square_reconstruction_stable _ hag (by omega)

theorem call_output_stable (i : Var Inputs Field) (n : ℕ) {k : ℕ}
    {env env' : ProverEnvironment Field} (hag : env.AgreesBelow k env')
    (hk : n + 96 ≤ k) :
    eval env ((subcircuit circuit i).output n) = eval env' ((subcircuit circuit i).output n) := by
  rw [call_output]
  exact output_stable i n hag hk

end Solution.Secp256k1ScalarMulFixedBase.LazyVar.Products
