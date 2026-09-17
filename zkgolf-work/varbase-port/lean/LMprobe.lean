import Solution.Secp256k1ScalarMul.Lazy.LazyMSM

namespace Solution.Secp256k1ScalarMul.LazyMSM
open Specs.ShortWeierstrass Specs.Secp256k1
open Solution.Secp256k1ScalarMulFixedBase.SparseX
open Solution.Secp256k1ScalarMulFixedBase.LazyVar
open Solution.Secp256k1ScalarMul.Lazy

set_option maxHeartbeats 4000000

theorem probe : GeneralFormalCircuit.Soundness (F circomPrime) (Output := unit) main (fun i _ => Assumptions i)
    (fun i _ _ => Spec i) := by
  circuit_proof_start_core
  simp only [main, circuit_norm] at h_holds
  obtain ⟨h_fold, h_rest⟩ := h_holds
  clear h_rest
  simp only [stepBody, circuit_norm, GLVMSM.varLookup_localLength, Step.circuit_localLength] at h_fold
  trace_state
  sorry

end Solution.Secp256k1ScalarMul.LazyMSM
