import Solution.Secp256k1ScalarMul.Lazy.LazyMSMComplete
import Solution.Secp256k1ScalarMul.VarLookupCW

/-! The lazy chain as a `GeneralFormalCircuit`, its cost and its local length. -/

namespace Solution.Secp256k1ScalarMul.LazyMSM

open Specs.ShortWeierstrass Specs.Secp256k1
open Solution.Secp256k1ScalarMulFixedBase.SparseX
open Solution.Secp256k1ScalarMulFixedBase.LazyVar
open Solution.Secp256k1ScalarMul.Lazy
open Challenge.CostR1CS Cost

set_option maxHeartbeats 4000000

noncomputable def circuit : GeneralFormalCircuit (F circomPrime) Inputs unit where
  main := main
  Assumptions := fun i _ => Assumptions i
  Spec := fun i _ _ => Spec i
  ProverAssumptions := fun i _ _ => ProverAssumptions i
  ProverSpec := fun _ _ _ => True
  soundness := soundness
  completeness := completeness

/-- `64 · 1622 + 4 + 176 + 176` allocations, `64 · 1635 + 1 + 4 + 178 + 178 + 4` rows. -/
def cost : Count := ⟨104164, 105005⟩

lemma stepBody_cost (input : Var Inputs (F circomPrime)) (acc : Var LazyPt (F circomPrime))
    (k : Fin 64) : CostIs (stepBody input acc k) ⟨1622, 1635⟩ := by
  rw [show (⟨1622, 1635⟩ : Count) = varLookupCost + Step.stepCost from by decide]
  unfold stepBody
  exact CostIs.bind (costIs_sub_varLookup _) fun t => Step.costIs_call _ _ _

theorem costIs_main (input : Var Inputs (F circomPrime)) : CostIs (main input) cost := by
  rw [show cost = ⟨64 * 1622, 64 * 1635⟩ + (⟨0, 1⟩ + (⟨1, 1⟩ + (⟨1, 1⟩ +
    (⟨qbits .rel1 + tbits .rel1 - 2, qbits .rel1 + tbits .rel1⟩ + (⟨1, 1⟩ + (⟨1, 1⟩ +
    (⟨qbits .fin + tbits .fin - 2, qbits .fin + tbits .fin⟩ + (⟨0, 1⟩ + (⟨0, 1⟩ + (⟨0, 1⟩ +
    ⟨0, 1⟩)))))))))) from by decide]
  dsimp only [main]
  refine CostIs.bind (CostIs.foldlRange fun acc k n => stepBody_cost input acc k n) fun _ => ?_
  refine CostIs.bind (CostIs.assertZero _) fun _ => ?_
  refine CostIs.bind (MulCell.costIs_call _) fun _ => ?_
  refine CostIs.bind (MulCell.costIs_call _) fun _ => ?_
  refine CostIs.bind (CostIs.assertion (Cert.cost .rel1 _)) fun _ => ?_
  refine CostIs.bind (MulCell.costIs_call _) fun _ => ?_
  refine CostIs.bind (MulCell.costIs_call _) fun _ => ?_
  refine CostIs.bind (CostIs.assertion (Cert.cost .fin _)) fun _ => ?_
  refine CostIs.bind (CostIs.assertZero _) fun _ => ?_
  refine CostIs.bind (CostIs.assertZero _) fun _ => ?_
  refine CostIs.bind (CostIs.assertZero _) fun _ => ?_
  exact CostIs.assertZero _

theorem costIs_call (input : Var Inputs (F circomPrime)) :
    CostIs (subcircuitWithAssertion circuit input) cost :=
  CostIs.subcircuitWithAssertion (fun n => costIs_main input n)

lemma localLength (input : Var Inputs (F circomPrime)) (n : ℕ) :
    (main input).localLength n = 104164 := by
  simp +arith only [main, circuit_norm, stepBody_localLength', dif_pos True.intro, MulCell.circuit,
    MulCell.elaborated, Cert.circuit, Cert.elaborated, RangeCheck.circuit, qbits, tbits,
    Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul]

lemma circuit_localLength (input : Var Inputs (F circomPrime)) :
    circuit.localLength input = 104164 := by
  rw [show circuit.localLength input = (main input).localLength 0 from
    (elaborated.localLength_eq input 0).symm]
  exact localLength input 0

end Solution.Secp256k1ScalarMul.LazyMSM
