import Solution.Secp256k1ScalarMul.Lazy.PatternTable

namespace Solution.Secp256k1ScalarMul.PatTable
open Specs.ShortWeierstrass Specs.Secp256k1
open GLVBuildTable

set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

theorem probe : Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [negCanon, withY, withXY, PhiPairAdd.circuit, PhiPairAdd.Assumptions, PhiPairAdd.Spec,
    CompleteAdd.circuit, CompleteAdd.Assumptions, CompleteAdd.Spec,
    NegYAffine.circuit, NegYAffine.Assumptions, NegYAffine.Spec,
    Mux.circuit, Mux.Assumptions, Mux.Spec]
  obtain ⟨hn1, hn3, hup, hum, hvp, hvm, hvpx, hvpy, hnvp, hvmx, hvmy, hnvm, h15, h7, h11, h3, h13, h5, h9, h1, h0x, h0y, h0, h8x, h8y, h8, h4x, h4y, h4, h12x, h12y, h12, h2x, h2y, h2, h10x, h10y, h10, h6x, h6y, h6, h14x, h14y, h14⟩ := h_holds
  clear hn1 hn3 hup hum hvp hvm hvpx hvpy hnvp hvmx hvmy hnvm h15 h7 h11 h3 h13 h5 h9 h1 h0x h0y h0 h8x h8y h8 h4x h4y h4 h12x h12y h12 h2x h2y h2 h10x h10y h10 h6x h6y h6 h14x h14y
  trace_state
  sorry

end Solution.Secp256k1ScalarMul.PatTable
