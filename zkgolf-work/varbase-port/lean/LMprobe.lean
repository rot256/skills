import Solution.Secp256k1ScalarMul.Lazy.LazyMSM
import Solution.Secp256k1ScalarMul.Lazy.StepOutput

namespace Solution.Secp256k1ScalarMul.LazyMSM
open Specs.ShortWeierstrass Specs.Secp256k1
open Solution.Secp256k1ScalarMulFixedBase.SparseX
open Solution.Secp256k1ScalarMulFixedBase.LazyVar
open Solution.Secp256k1ScalarMul.Lazy

set_option maxHeartbeats 4000000

def accL (input : Var Inputs (F circomPrime)) (i₀ : ℕ) : ℕ → Var LazyPt (F circomPrime)
  | 0 => seed input
  | k + 1 => Step.outputAt (i₀ + k * stepLen + 122)

set_option pp.explicit true in
#check @Step.circuit_localLength

lemma foldlAcc_eq_accL (input : Var Inputs (F circomPrime)) (i₀ : ℕ) (i : Fin 64) :
    Circuit.FoldlM.foldlAcc i₀ (Vector.finRange 64) (stepBody input) (seed input) i =
      accL input i₀ i.val := by
  simp only [Circuit.FoldlM.foldlAcc, Vector.getElem_finRange, stepBody, circuit_norm,
    GLVMSM.varLookup_localLength, Step.output_eq_outputAt]
  set_option pp.explicit true in trace_state
  sorry

end Solution.Secp256k1ScalarMul.LazyMSM
