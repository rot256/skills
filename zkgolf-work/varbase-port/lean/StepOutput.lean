import Solution.Secp256k1ScalarMul.Lazy.Step
import Solution.Secp256k1ScalarMul.Lazy.StepCost

/-! Closed form of the step output: the last three output muxes and the
`zOut` flag, at fixed offsets from the step's base offset. -/

namespace Solution.Secp256k1ScalarMulFixedBase.LazyVar.Step

open SmallSquare Sparse32 SparseX
open Solution.Secp256k1ScalarMul.Lazy
open Solution.Secp256k1ScalarMulFixedBase.LazyVar

set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 20000

/-- Output variables of a step whose local witnesses start at `n₀`. -/
def outputAt (n₀ : ℕ) : Var LazyPt Field :=
  { x := varFromOffset (fields 8) (n₀ + 1468),
    y := varFromOffset (fields 8) (n₀ + 1492),
    isInf := var ⟨n₀ + 513⟩ + var ⟨n₀ + 1450⟩ - var ⟨n₀ + 1451⟩ }

lemma output_eq_outputAt (n : ℕ) (hn : n + 1 ≤ depth) (i : Var Inputs Field) (n₀ : ℕ) :
    (circuit n hn).output i n₀ = outputAt n₀ := by
  show (elaborated n hn).output i n₀ = _
  simp +arith only [elaborated, outputAt, main, Sparse32Normalize.circuit, Sparse32Normalize.elaborated,
    MulCell.circuit, MulCell.elaborated, Products.circuit, Products.elaborated,
    Certs.circuit, Certs.elaborated, Cert.circuit, Cert3.circuit, RangeCheck.circuit,
    MuxVec.circuit, MuxVec.elaborated, circuit_norm, numLimbs, Nat.reduceAdd, Nat.reduceSub,
    Secp256k1ScalarMul.Lazy.qbits, Secp256k1ScalarMul.Lazy.tbits, ukbits, ut0bits, ut1bits]

end Solution.Secp256k1ScalarMulFixedBase.LazyVar.Step
