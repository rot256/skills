import Solution.Secp256k1ScalarMul.Lazy.ProductsShape
import Solution.Secp256k1ScalarMulFixedBase.CWHelpers

/-! Computable witnesses and output stability of `Sparse32Square` (the
`UploadPart5` versions are not imported by this tree). -/

namespace Solution.Secp256k1ScalarMul.Lazy.SquareCW

open Solution.Secp256k1ScalarMulFixedBase
open Challenge.CostR1CS Cost
open Challenge.Utils.ComputableWitnessLemmas

abbrev Field := SmallSquare.Field
abbrev Coeffs := fields 8

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem output_eq (a : Var Coeffs Field) (n : ℕ) :
    (subcircuit Sparse32Square.circuit a).output n =
      Sparse32Square.outputExpr (varFromOffset (fields 9) n) := by
  simp only [Sparse32Square.circuit, Sparse32Square.elaborated, circuit_norm]

theorem computableWitnesses : Sparse32Square.circuit.ComputableWitnesses := by
  intro n a env env'
  change Operations.forAllFlat n
    (FormalCircuitBase.computableWitnessCondition a env env')
    ((Sparse32Square.main a).operations n)
  apply FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  simp only [Sparse32Square.main, Circuit.bind_structuralComputableWitnesses_iff,
    Circuit.provableWitness_structuralComputableWitnesses_iff,
    Circuit.forEach_structuralComputableWitnesses_iff,
    Circuit.assertZero_structuralComputableWitnesses_iff,
    Circuit.pure_structuralComputableWitnesses_iff]
  exact ⟨fun _ hp => congrArg Sparse32Square.productsValue hp, fun _ => trivial, trivial⟩

theorem output_stable (a : Var Coeffs Field) (n : ℕ) {k : ℕ}
    {env env' : ProverEnvironment Field} (hag : env.AgreesBelow k env')
    (hk : n + 9 ≤ k) :
    eval env ((subcircuit Sparse32Square.circuit a).output n) =
      eval env' ((subcircuit Sparse32Square.circuit a).output n) := by
  rw [output_eq]
  let products := (varFromOffset (fields 9) n : Var (fields 9) Field)
  have hp : Vector.map (Expression.eval env.toEnvironment) products =
      Vector.map (Expression.eval env'.toEnvironment) products := by
    apply Vector.ext
    intro row hr
    simp only [products, circuit_norm]
    exact hag (n + row) (by omega)
  have ho : Vector.map (Expression.eval env.toEnvironment) (Sparse32Square.outputExpr products) =
      Vector.map (Expression.eval env'.toEnvironment) (Sparse32Square.outputExpr products) :=
    (Sparse32Square.eval_outputExpr env.toEnvironment products).trans
      ((congrArg Sparse32Square.outputValue hp).trans
        (Sparse32Square.eval_outputExpr env'.toEnvironment products).symm)
  apply Vector.ext
  intro j hj
  rw [← ProvableType.getElem_eval_fields_prover,
    ← ProvableType.getElem_eval_fields_prover]
  simpa only [Vector.getElem_map] using congrArg (fun z : Coeffs Field => z[j]) ho

end Solution.Secp256k1ScalarMul.Lazy.SquareCW
