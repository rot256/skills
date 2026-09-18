import Solution.Secp256k1ScalarMul.MulModSqN32
import Solution.Secp256k1ScalarMul.Cost

/-! Cost, R1CS and affinity certificates for `MulModSqN32`. -/

namespace Solution.Secp256k1ScalarMul
namespace Cost

open Challenge.CostR1CS

attribute [local irreducible] isR1CSRow r1csProducts operationsIsR1CS flatOperationsIsR1CS

def mulModSqN32Cost : Count := ⟨348, 350⟩

theorem costIs_mulModSqN32 (input : Var MulModSqN32.Inputs (F circomPrime)) :
    CostIs (MulModSqN32.main input) mulModSqN32Cost := by
  obtain ⟨a, b⟩ := input
  rw [show mulModSqN32Cost
        = ⟨4, 0⟩ + (⟨252, 256⟩ + (mulModFold32TInvCost + Count.zero)) from by decide]
  unfold MulModSqN32.main
  refine CostIs.bind (CostIs.provableWitness _) fun r => ?_
  refine CostIs.bind (costIs_assertion_normalize secpParams _) fun _ => ?_
  refine CostIs.bind (costIs_assertion_mulModFold32TInv _ _ _ _) fun _ => ?_
  exact CostIs.pure _

theorem costIs_sub_mulModSqN32 (input : Var MulModSqN32.Inputs (F circomPrime)) :
    CostIs (subcircuit MulModSqN32.circuit input) mulModSqN32Cost :=
  CostIs.subcircuit fun n => costIs_mulModSqN32 input n

theorem isR1CS_mulModSqN32 (input : Var MulModSqN32.Inputs (F circomPrime))
    (ha : AffineW input.a) (hb : AffineW input.b) :
    IsR1CSCirc (MulModSqN32.main input) := by
  obtain ⟨a, b⟩ := input
  unfold MulModSqN32.main
  refine IsR1CSCirc.bind_out (isR1CS_provableWitness_bigInt _) fun nr => ?_
  refine IsR1CSCirc.bind
    (isR1CS_assertion_normalize secpParams _ (affineW_provableWitness_bigInt _ nr)) fun _ => ?_
  refine IsR1CSCirc.bind
    (isR1CS_assertion_mulModFold32TInv _ _ _ _ ha hb ?_)
    fun _ => IsR1CSCirc.pure _
  exact affineW_varFromOffset _ _

theorem isR1CS_sub_mulModSqN32 (input : Var MulModSqN32.Inputs (F circomPrime))
    (ha : AffineW input.a) (hb : AffineW input.b) :
    IsR1CSCirc (subcircuit MulModSqN32.circuit input) :=
  IsR1CSCirc.subcircuit fun n => isR1CS_mulModSqN32 input ha hb n

theorem affineW_sub_mulModSqN32 (input : Var MulModSqN32.Inputs (F circomPrime)) (n : ℕ) :
    AffineW ((subcircuit MulModSqN32.circuit input).output n) := by
  simp only [circuit_norm, subcircuit, MulModSqN32.circuit, MulModSqN32.elaborated]
  exact affineW_varFromOffset _ _

end Cost
end Solution.Secp256k1ScalarMul
