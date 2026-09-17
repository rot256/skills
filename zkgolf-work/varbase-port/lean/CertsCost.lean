import Solution.Secp256k1ScalarMul.Lazy.Certs

/-! Cost, R1CS shape and local length of the certificate-slot assertion. -/

namespace Solution.Secp256k1ScalarMulFixedBase.LazyVar.Certs

open SmallSquare Sparse32 SparseX Challenge.CostR1CS Cost
open Solution.Secp256k1ScalarMul.Lazy
open Solution.Secp256k1ScalarMulFixedBase.LazyVar

set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 20000

/-- 17 product cells and the four certificates. -/
def certsCost : Count := ⟨839, 848⟩

theorem cost (i : Var Inputs Field) : CostIs (main i) certsCost := by
  rw [show certsCost = ⟨1, 1⟩ + (⟨1, 1⟩ + (⟨1, 1⟩ + (⟨1, 1⟩ + (⟨1, 1⟩ + (⟨1, 1⟩ + (⟨1, 1⟩ +
    (⟨1, 1⟩ + (⟨1, 1⟩ + (⟨1, 1⟩ + (⟨1, 1⟩ + (⟨1, 1⟩ + (⟨1, 1⟩ + (⟨1, 1⟩ + (⟨1, 1⟩ + (⟨1, 1⟩ +
    (⟨1, 1⟩ + (⟨qbits .rel1 + tbits .rel1 - 2, qbits .rel1 + tbits .rel1⟩ + (Cert3.cost3 +
    (⟨qbits .xeq + tbits .xeq - 2, qbits .xeq + tbits .xeq⟩ +
    (⟨qbits .rel2 + tbits .rel2 - 2, qbits .rel2 + tbits .rel2⟩ + Count.zero)))))))))))))))))))) by
    decide]
  unfold main
  refine CostIs.bind (MulCell.costIs_call _) fun _ => ?_
  refine CostIs.bind (MulCell.costIs_call _) fun _ => ?_
  refine CostIs.bind (MulCell.costIs_call _) fun _ => ?_
  refine CostIs.bind (MulCell.costIs_call _) fun _ => ?_
  refine CostIs.bind (MulCell.costIs_call _) fun _ => ?_
  refine CostIs.bind (MulCell.costIs_call _) fun _ => ?_
  refine CostIs.bind (MulCell.costIs_call _) fun _ => ?_
  refine CostIs.bind (MulCell.costIs_call _) fun _ => ?_
  refine CostIs.bind (MulCell.costIs_call _) fun _ => ?_
  refine CostIs.bind (MulCell.costIs_call _) fun _ => ?_
  refine CostIs.bind (MulCell.costIs_call _) fun _ => ?_
  refine CostIs.bind (MulCell.costIs_call _) fun _ => ?_
  refine CostIs.bind (MulCell.costIs_call _) fun _ => ?_
  refine CostIs.bind (MulCell.costIs_call _) fun _ => ?_
  refine CostIs.bind (MulCell.costIs_call _) fun _ => ?_
  refine CostIs.bind (MulCell.costIs_call _) fun _ => ?_
  refine CostIs.bind (MulCell.costIs_call _) fun _ => ?_
  refine CostIs.bind (CostIs.assertion (Cert.cost .rel1 _)) fun _ => ?_
  refine CostIs.bind (CostIs.assertion (Cert3.cost _)) fun _ => ?_
  refine CostIs.bind (CostIs.assertion (Cert.cost .xeq _)) fun _ => ?_
  exact CostIs.assertion (Cert.cost .rel2 _)

theorem costIs_call (n : ℕ) (hn : n ≤ depth) (i : Var Inputs Field) : CostIs (assertion (circuit n hn) i) certsCost :=
  CostIs.assertion (fun n => cost i n)

lemma localLength (i : Var Inputs Field) (n : ℕ) : (main i).localLength n = 839 := by
  simp only [main, MulCell.circuit, MulCell.elaborated, Cert.circuit, Cert3.circuit,
    RangeCheck.circuit, circuit_norm]
  decide

end Solution.Secp256k1ScalarMulFixedBase.LazyVar.Certs
