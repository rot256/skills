import Solution.Secp256k1ScalarMul.Lazy.Step
import Solution.Secp256k1ScalarMul.Lazy.StepCost
import Solution.Secp256k1ScalarMul.Lazy.ChainAlgebra
import Solution.Secp256k1ScalarMul.VarLookup

/-!
# The lazy multi-scalar chain

Seed `E(1111)`, then 64 steps `R ← 2R + E(nibble_k)` (a `VarLookup` and a
lazy `Step` each), and the final equality `R = E(1111)` certified on the lazy
coordinates.  `sp := tinf[15]` is the special-scalar flag: with `sp = 1` the
chain proves nothing and the four coefficients are forced to `1`.
-/

namespace Solution.Secp256k1ScalarMul.LazyMSM

open Specs.ShortWeierstrass Specs.Secp256k1
open Solution.Secp256k1ScalarMulFixedBase.SparseX
open Solution.Secp256k1ScalarMulFixedBase.LazyVar
open Solution.Secp256k1ScalarMul.Lazy

abbrev Inputs := GLVMSM.Inputs
abbrev LazyPt := Step.LazyPt

def bitIdx (k : Fin 64) : ℕ := GLVMSM.coeffBits - 1 - k.val

lemma bitIdx_lt (k : Fin 64) : bitIdx k < GLVMSM.coeffBits := by
  simp only [bitIdx, GLVMSM.coeffBits]; omega

def lkInput (input : Var Inputs (F circomPrime)) (k : Fin 64) :
    Var VarLookup.Inputs (F circomPrime) :=
  { tx := input.tx, ty := input.ty, tinf := input.tinf,
    b3 := input.m3[bitIdx k]'(bitIdx_lt k), b2 := input.m2[bitIdx k]'(bitIdx_lt k),
    b1 := input.m1[bitIdx k]'(bitIdx_lt k), b0 := input.m0[bitIdx k]'(bitIdx_lt k) }

def spE (input : Var Inputs (F circomPrime)) : Expression (F circomPrime) := input.tinf[15]

def seed (input : Var Inputs (F circomPrime)) : Var LazyPt (F circomPrime) :=
  { x := embedExpr input.tx[15], y := embedExpr input.ty[15], isInf := input.tinf[15] }

noncomputable def stepBody (input : Var Inputs (F circomPrime))
    (acc : Var LazyPt (F circomPrime)) (k : Fin 64) :
    Circuit (F circomPrime) (Var LazyPt (F circomPrime)) := do
  let t ← subcircuit VarLookup.circuit (lkInput input k)
  Step.circuit k.val (by have := k.isLt; simp only [depth]; omega) { acc := acc, t := t, sp := spE input }

def stepLen : ℕ := 122 + 1500

private noncomputable def stepLength (input : Var Inputs (F circomPrime)) :
    Circuit.ConstantLength
      (fun (x : Var LazyPt (F circomPrime) × Fin 64) => stepBody input x.1 x.2) where
  localLength := stepLen
  localLength_eq x n := by
    simp only [stepBody, stepLen, circuit_norm, GLVMSM.varLookup_localLength]
    rw [Step.circuit_localLength]

/-- `(1 − m₀) + Σ_{i ≥ 1} m_i`: zero iff the magnitude is exactly `1`. -/
def unitDefect (m : Var (fields GLVMSM.coeffBits) (F circomPrime)) : Expression (F circomPrime) :=
  ((1 : Expression (F circomPrime)) - m[0]) +
    Fin.foldl 63 (fun acc i => acc + m[i.val + 1]'(by
      have := i.isLt; simp only [GLVMSM.coeffBits]; omega)) 0

noncomputable def main (input : Var Inputs (F circomPrime)) : Circuit (F circomPrime) Unit := do
  let acc ← Circuit.foldlRange 64 (seed input) (stepBody input) (stepLength input)
  let sp := spE input
  Circuit.assertZero ((1 - sp) * (acc.isInf - sp))
  let ex := Products.vsubE acc.x (embedExpr input.tx[15])
  let ey := Products.vsubE acc.y (embedExpr input.ty[15])
  let hxl ← subcircuit MulCell.circuit ⟨1 - sp, Certs.half ex false⟩
  let hxh ← subcircuit MulCell.circuit ⟨1 - sp, Certs.half ex true⟩
  assertion (Cert.circuit .rel1) #v[hxl, hxh]
  let hyl ← subcircuit MulCell.circuit ⟨1 - sp, Certs.half ey false⟩
  let hyh ← subcircuit MulCell.circuit ⟨1 - sp, Certs.half ey true⟩
  assertion (Cert.circuit .fin) #v[hyl, hyh]
  Circuit.assertZero (sp * unitDefect input.m0)
  Circuit.assertZero (sp * unitDefect input.m1)
  Circuit.assertZero (sp * unitDefect input.m2)
  Circuit.assertZero (sp * unitDefect input.m3)

noncomputable instance elaborated : ElaboratedCircuit (F circomPrime) Inputs unit main := by
  elaborate_circuit

/-- Magnitude exactly one: bit 0 set, all others clear. -/
def UnitBits (m : Vector (F circomPrime) GLVMSM.coeffBits) : Prop :=
  m[0] = 1 ∧ ∀ i : Fin GLVMSM.coeffBits, 1 ≤ i.val → m[i] = 0

def Assumptions (input : Inputs (F circomPrime)) : Prop := GLVMSM.Assumptions input

/-- With `sp = 0` the chain result equals `E(1111)`; with `sp = 1` all four
coefficients have magnitude one. -/
def Spec (input : Inputs (F circomPrime)) : Prop :=
  (input.tinf[15] = 0 →
    LazyChain.chainAcc input GLVMSM.coeffBits =
      decodePoint (GLVMSM.tableEntry input 15 (by norm_num))) ∧
  (input.tinf[15] = 1 → UnitBits input.m0 ∧ UnitBits input.m1 ∧ UnitBits input.m2 ∧ UnitBits input.m3)

/-- Honest-prover preconditions: either no table entry is infinite, or the
all-plus entry is infinite and the coefficients are `±1`. -/
def ProverAssumptions (input : Inputs (F circomPrime)) : Prop :=
  GLVMSM.Assumptions input ∧
  (input.tinf[15] = 0 → ∀ i : Fin 16, input.tinf[i] = 0) ∧
  (input.tinf[15] = 0 →
    LazyChain.chainAcc input GLVMSM.coeffBits =
      decodePoint (GLVMSM.tableEntry input 15 (by norm_num))) ∧
  (input.tinf[15] = 1 → UnitBits input.m0 ∧ UnitBits input.m1 ∧ UnitBits input.m2 ∧ UnitBits input.m3)

end Solution.Secp256k1ScalarMul.LazyMSM
