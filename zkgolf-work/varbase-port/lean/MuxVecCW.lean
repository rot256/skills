import Solution.Secp256k1ScalarMul.Lazy.MuxVec
import Solution.Secp256k1ScalarMulFixedBase.CWHelpers

/-! Computable witnesses and output stability of the vector mux. -/

namespace Solution.Secp256k1ScalarMulFixedBase.LazyVar.MuxVec

open SmallSquare Sparse32 SparseX
open Challenge.CostR1CS Cost
open Challenge.Utils.ComputableWitnessLemmas

set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem computableWitnesses : circuit.ComputableWitnesses := by
  intro n input env env'
  change Operations.forAllFlat n (FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations n)
  apply FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  simp only [main, Circuit.bind_structuralComputableWitnesses_iff,
    Circuit.provableWitness_structuralComputableWitnesses_iff,
    Circuit.forEach_structuralComputableWitnesses_iff,
    Circuit.assertZero_structuralComputableWitnesses_iff,
    Circuit.pure_structuralComputableWitnesses_iff]
  exact ⟨fun _ hp => by rw [hp], fun _ => trivial, trivial⟩

theorem call_output_stable (i : Var Inputs Field) (n : ℕ) {k : ℕ}
    {e e' : ProverEnvironment Field} (hag : e.AgreesBelow k e') (hk : n + 8 ≤ k) :
    eval e ((subcircuit circuit i).output n) = eval e' ((subcircuit circuit i).output n) := by
  rw [call_output, ProvableType.eval_varFromOffset_prover, ProvableType.eval_varFromOffset_prover]
  congr 1
  apply Vector.ext
  intro j hj
  simp only [Vector.getElem_mapRange]
  exact hag (n + j) (by change j < 8 at hj; omega)

end Solution.Secp256k1ScalarMulFixedBase.LazyVar.MuxVec
