import Solution.Secp256k1ScalarMul.Lazy.Relations
import Solution.Secp256k1ScalarMulFixedBase.CWHelpers

/-! Computable witnesses and output stability of `Sparse32Normalize`. -/

namespace Solution.Secp256k1ScalarMulFixedBase.Sparse32Normalize

open SmallSquare Sparse32
open Challenge.CostR1CS Cost
open Challenge.Utils.ComputableWitnessLemmas

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem computableWitnesses : circuit.base.ComputableWitnesses := by
  intro n input env env'
  change Operations.forAllFlat n (FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations n)
  apply FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  simp only [main, Circuit.bind_structuralComputableWitnesses_iff,
    and_true, subcircuitWithAssertion,
    FormalCircuitBase.Operations.StructuralComputableWitnesses, Circuit.operations, and_true]
  exact GeneralFormalCircuit.subcircuit_flatStructuralComputableWitnesses
    (SmallNormalize.circuit .w32) input input n (fun _ _ h => h)
    (SmallNormalize.computableWitnesses .w32) env env'

theorem output_stable (raw : Var Emu Field) {n k : ℕ} {e e' : ProverEnvironment Field}
    (hr : eval e raw = eval e' raw) (h : e.AgreesBelow k e') (hk : n + 252 ≤ k) :
    eval e ((main raw).output n) = eval e' ((main raw).output n) := by
  rw [output_eq]
  have hs := SmallNormalize.output_stable .w32 raw hr h hk
  simp only [circuit_norm, eval_balanceExpr] at hs ⊢
  rw [hs]

theorem call_output_stable (raw : Var Emu Field) {n k : ℕ} {e e' : ProverEnvironment Field}
    (hr : eval e raw = eval e' raw) (h : e.AgreesBelow k e') (hk : n + 252 ≤ k) :
    eval e ((circuit raw).output n) = eval e' ((circuit raw).output n) := by
  rw [call_output]; exact output_stable raw hr h hk

end Solution.Secp256k1ScalarMulFixedBase.Sparse32Normalize
