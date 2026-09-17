import Solution.Secp256k1ScalarMul.Lazy.Step
import Solution.Secp256k1ScalarMul.Lazy.CertsCost
import Solution.Secp256k1ScalarMul.Lazy.ProductsShape

/-! Cost and local length of one chain step. -/

namespace Solution.Secp256k1ScalarMulFixedBase.LazyVar.Step

open SmallSquare Sparse32 SparseX Challenge.CostR1CS Cost
open Solution.Secp256k1ScalarMul.Lazy
open Solution.Secp256k1ScalarMulFixedBase.LazyVar

set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 20000

/-- `1500` allocations, `1513` constraints per step. -/
def stepCost : Count := ⟨1500, 1513⟩

theorem cost (n : ℕ) (hn : n + 1 ≤ depth) (i : Var Inputs Field) :
    CostIs (main n hn i) stepCost := by
  rw [show stepCost = ⟨4, 0⟩ + (⟨252, 256⟩ + (⟨4, 0⟩ + (⟨252, 256⟩ + (⟨2, 0⟩ + (⟨0, 1⟩ +
    (⟨0, 1⟩ + (⟨0, 1⟩ + (⟨0, 1⟩ + (⟨0, 1⟩ + (⟨0, 1⟩ + (⟨1, 1⟩ + (Products.cost +
    (Certs.certsCost + (⟨1, 1⟩ + (⟨1, 1⟩ + (⟨8, 8⟩ + (⟨8, 8⟩ + (⟨8, 8⟩ + (⟨8, 8⟩ +
    (⟨8, 8⟩ + (⟨8, 8⟩ + Count.zero))))))))))))))))))))) by decide]
  dsimp only [main]
  refine CostIs.bind (CostIs.provableWitness _) fun _ => ?_
  refine CostIs.bind (CostIs.subcircuitWithAssertion (Sparse32Normalize.cost _)) fun _ => ?_
  refine CostIs.bind (CostIs.provableWitness _) fun _ => ?_
  refine CostIs.bind (CostIs.subcircuitWithAssertion (Sparse32Normalize.cost _)) fun _ => ?_
  refine CostIs.bind (CostIs.provableWitness _) fun _ => ?_
  refine CostIs.bind (CostIs.assertZero _) fun _ => ?_
  refine CostIs.bind (CostIs.assertZero _) fun _ => ?_
  refine CostIs.bind (CostIs.assertZero _) fun _ => ?_
  refine CostIs.bind (CostIs.assertZero _) fun _ => ?_
  refine CostIs.bind (CostIs.assertZero _) fun _ => ?_
  refine CostIs.bind (CostIs.assertZero _) fun _ => ?_
  refine CostIs.bind (MulCell.costIs_call _) fun _ => ?_
  refine CostIs.bind (Products.costIs_call _) fun _ => ?_
  refine CostIs.bind (Certs.costIs_call _ _ _) fun _ => ?_
  refine CostIs.bind (MulCell.costIs_call _) fun _ => ?_
  refine CostIs.bind (MulCell.costIs_call _) fun _ => ?_
  refine CostIs.bind (MuxVec.costIs_call _) fun _ => ?_
  refine CostIs.bind (MuxVec.costIs_call _) fun _ => ?_
  refine CostIs.bind (MuxVec.costIs_call _) fun _ => ?_
  refine CostIs.bind (MuxVec.costIs_call _) fun _ => ?_
  refine CostIs.bind (MuxVec.costIs_call _) fun _ => ?_
  refine CostIs.bind (MuxVec.costIs_call _) fun _ => ?_
  exact CostIs.pure _

theorem costIs_call (n : ℕ) (hn : n + 1 ≤ depth) (i : Var Inputs Field) :
    CostIs (subcircuitWithAssertion (circuit n hn) i) stepCost :=
  CostIs.subcircuitWithAssertion (fun k => cost n hn i k)

lemma localLength (n : ℕ) (hn : n + 1 ≤ depth) (i : Var Inputs Field) (o : ℕ) :
    (main n hn i).localLength o = 1500 := by
  simp +arith only [main, Sparse32Normalize.circuit, Sparse32Normalize.elaborated,
    MulCell.circuit, MulCell.elaborated, Products.circuit, Products.elaborated,
    Certs.circuit, Certs.elaborated, Cert.circuit, Cert3.circuit, RangeCheck.circuit,
    MuxVec.circuit, MuxVec.elaborated, circuit_norm, numLimbs, Nat.reduceAdd, Nat.reduceSub,
    Secp256k1ScalarMul.Lazy.qbits, Secp256k1ScalarMul.Lazy.tbits, ukbits, ut0bits, ut1bits]

lemma call_localLength (n : ℕ) (hn : n + 1 ≤ depth) (i : Var Inputs Field) (o : ℕ) :
    (subcircuitWithAssertion (circuit n hn) i).localLength o = 1500 := by
  simp only [subcircuitWithAssertion, circuit_norm]
  exact localLength n hn i o

end Solution.Secp256k1ScalarMulFixedBase.LazyVar.Step

namespace Solution.Secp256k1ScalarMulFixedBase.LazyVar.Step
open SmallSquare Sparse32 SparseX Challenge.CostR1CS Cost
open Solution.Secp256k1ScalarMul.Lazy
open Solution.Secp256k1ScalarMulFixedBase.LazyVar

lemma circuit_localLength (n : ℕ) (hn : n + 1 ≤ depth) (i : Var Inputs Field) :
    (circuit n hn).localLength i = 1500 := by
  rw [show (circuit n hn).localLength i = (main n hn i).localLength 0 from
    ((elaborated n hn).localLength_eq i 0).symm]
  exact localLength n hn i 0

end Solution.Secp256k1ScalarMulFixedBase.LazyVar.Step
