import Solution.Secp256k1ScalarMul.SubModTheorems
import Challenge.Utils.ComputableWitnessLemmas
import Solution.Secp256k1ScalarMul.AddMod
import Solution.Secp256k1ScalarMul.ValidP

namespace Solution.Secp256k1ScalarMul
namespace SubMod

structure Inputs (F : Type) where
  a : Emu F
  b : Emu F
deriving ProvableStruct

def main (input : Var Inputs (F circomPrime)) :
    Circuit (F circomPrime) (Var Emu (F circomPrime)) := do
  let { a, b } := input

  -- witness r = (a + P256 - b) % P256 and the borrow bit
  let r ← ProvableType.witness (α := Emu) fun env =>
    emuOfNat ((evalEmu env a + P256 - evalEmu env b) % P256)
  let q ← ProvableType.witness (α := field) fun env =>
    (((if evalEmu env a < evalEmu env b then 1 else 0 : ℕ)) : F circomPrime)

  -- q is boolean
  assertZero (q * (q - 1))

  -- r is normalized and canonical, using the sparse shape of secp256k1's p.
  ValidP.circuit r

  -- r + b = a + q·P256 as integers, limb-coefficient-wise.
  -- Width-5 vector; every coefficient is additive-scale (`< 2^65 + 2`), so the
  -- narrow-carry `EqViaCarriesN` (`eqNParamsAdd`) runs each offset carry at
  -- 3 bits instead of the multiplication width 69.
  let lhs : Vector (Expression (F circomPrime)) (2 * 3 - 1) :=
    Vector.mapFinRange (2 * 3 - 1) fun k =>
      if h : k.val < numLimbs then r[k.val]'h + b[k.val]'h else 0
  let rhs : Vector (Expression (F circomPrime)) (2 * 3 - 1) :=
    Vector.mapFinRange (2 * 3 - 1) fun k =>
      if h : k.val < numLimbs then a[k.val]'h + q * pConst[k.val]'h else 0
  EqViaCarriesN.circuit eqNParamsAdd { lhs := lhs, rhs := rhs }

  return r

instance elaborated : ElaboratedCircuit (F circomPrime) Inputs Emu main := by
  elaborate_circuit

def Assumptions (input : Inputs (F circomPrime)) : Prop :=
  Fe.Valid input.a ∧ Fe.Valid input.b

def Spec (input : Inputs (F circomPrime)) (out : Emu (F circomPrime)) : Prop :=
  Fe.Valid out ∧ decodeFe out = decodeFe input.a - decodeFe input.b

theorem soundness : Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [ValidP.circuit, ValidP.main, ValidP.Assumptions, ValidP.Spec,
    EqViaCarriesN.circuit, EqViaCarriesN.elaborated, EqViaCarriesN.main,
    EqViaCarriesN.Assumptions, EqViaCarriesN.Spec]
  obtain ⟨hq_bool, hr_valid, h_eq_impl⟩ := h_holds
  apply soundness_coreN i₀ env input_var_a input_var_b input_a input_b
    h_input.1 h_input.2 h_assumptions.1 h_assumptions.2 hq_bool hr_valid.1
  · intro _
    rw [pConst_value env]
    exact hr_valid.2
  · exact h_eq_impl

theorem completeness : Completeness (F circomPrime) main Assumptions := by
  circuit_proof_start [ValidP.circuit, ValidP.main, ValidP.Assumptions, ValidP.Spec,
    EqViaCarriesN.circuit, EqViaCarriesN.elaborated, EqViaCarriesN.main,
    EqViaCarriesN.Assumptions, EqViaCarriesN.Spec]
  have heva : evalEmu env input_var_a = BigInt.value limbBits input_a := by
    rw [evalEmu, BigInt.value, ← h_input.1]
  have hevb : evalEmu env input_var_b = BigInt.value limbBits input_b := by
    rw [evalEmu, BigInt.value, ← h_input.2]
  rw [heva, hevb] at h_env
  obtain ⟨hq, hr_norm, hr_lt, h_eq⟩ :=
    completeness_coreN i₀ env.toEnvironment input_var_a input_var_b input_a input_b
      h_input.1 h_input.2 h_assumptions.1 h_assumptions.2 h_env.1 h_env.2
  refine ⟨hq, ⟨hr_norm, ?_⟩, h_eq⟩
  rw [← pConst_value env.toEnvironment]
  exact hr_lt.2

def circuit : FormalCircuit (F circomPrime) Inputs Emu where
  main; elaborated; Assumptions; Spec; soundness; completeness

end SubMod

namespace SubMod3
open SubMod AddMod

end SubMod3
end Solution.Secp256k1ScalarMul

namespace Solution.Secp256k1ScalarMul
namespace SubMod
open AddMod

end SubMod
end Solution.Secp256k1ScalarMul

namespace Solution.Secp256k1ScalarMul
namespace SubMod3
open AddMod

end SubMod3
end Solution.Secp256k1ScalarMul
