import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Solution.Secp256k1ScalarMul.Lazy_Donor6

/-! Remaining fixed-base sparse gadgets (patchgravity, zk.golf submission
d59c8bf7) needed by the variable-base lazy chain: the wide product assertion,
the sparse normaliser and its shape. -/

/- === Sparse32Wide === -/
section
namespace Solution.Secp256k1ScalarMulFixedBase.Sparse32Wide

open SmallSquare Sparse32 SparseX Challenge.CostR1CS Cost
open Challenge.Utils.ComputableWitnessLemmas

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 20000

attribute [local irreducible] isR1CSRow r1csProducts operationsIsR1CS flatOperationsIsR1CS

lemma affine_productHalfExpr (z : Var (fields 8) Field) (hz : AffineW z)
    (side : Bool) : Affine (productHalfExpr z side) := by
  cases side
  · simp only [productHalfExpr, Bool.false_eq_true, ↓reduceIte]
    exact Affine.add
      (Affine.add
        (Affine.add (hz 0 (by decide)) (Affine.fconst_mul _ (hz 1 (by decide))))
        (Affine.fconst_mul _ (hz 2 (by decide))))
      (Affine.fconst_mul _ (hz 3 (by decide)))
  · simp only [productHalfExpr, ↓reduceIte]
    exact Affine.add
      (Affine.add
        (Affine.add (hz 4 (by decide)) (Affine.fconst_mul _ (hz 5 (by decide))))
        (Affine.fconst_mul _ (hz 6 (by decide))))
      (Affine.fconst_mul _ (hz 7 (by decide)))

end Solution.Secp256k1ScalarMulFixedBase.Sparse32Wide
end

/- === Sparse32Normalize === -/
section
namespace Solution.Secp256k1ScalarMulFixedBase.Sparse32Normalize

open SmallSquare
open Sparse32

set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 20000

def balance (u : Digits Field) : Digits Field :=
  Vector.ofFn fun i => u[i.val] - ((m : ℤ) : Field)

def balanceExpr (u : Var (Digits) Field) : Var (Digits) Field :=
  Vector.ofFn fun i => u[i.val] - ((m : ℤ) : Field)

lemma eval_balanceExpr (env : Environment Field) (u : Var (Digits) Field) :
    Vector.map (Expression.eval env) (balanceExpr u) =
      balance (Vector.map (Expression.eval env) u) := by
  apply Vector.ext
  intro i hi
  simp only [balanceExpr, balance, circuit_norm, Vector.getElem_ofFn]
  rw [sub_eq_add_neg]

lemma balance_spec (raw : Emu Field) (u : Digits Field)
    (hu : ∀ i : Fin 8,
      u[i.val] = ((Sparse32.unsignedDigit raw i : ℕ) : Field)) :
    ∀ i : Fin 8, (balance u)[i.val] = ((Sparse32.digitZ raw i : ℤ) : Field) := by
  intro i
  rw [balance, Vector.getElem_ofFn, hu i]
  simp only [Sparse32.digitZ, Int.cast_sub, Int.cast_natCast]

def main (raw : Var Emu Field) : Circuit Field (Var Digits Field) := do
  let u ← SmallNormalize.circuit .w32 raw
  return balanceExpr u

instance elaborated : ElaboratedCircuit Field Emu Digits main := by
  elaborate_circuit

def Assumptions (_ : Emu Field) (_ : ProverData Field) : Prop := True

def ProverAssumptions (raw : Emu Field) (_ : ProverData Field) (_ : ProverHint Field) : Prop :=
  BigInt.Normalized 64 raw

def Spec (raw : Emu Field) (out : Digits Field) (_ : ProverData Field) : Prop :=
  SlopeRep raw out

def ProverSpec (_ : Emu Field) (_ : Digits Field) (_ : ProverHint Field) : Prop := True

theorem soundness :
    GeneralFormalCircuit.Soundness Field main Assumptions Spec := by
  circuit_proof_start [SmallNormalize.circuit, SmallNormalize.Assumptions,
    SmallNormalize.Spec]
  refine ⟨h_holds.1, ?_⟩
  let u : Digits Field :=
    Vector.map (Expression.eval env) ((SmallNormalize.main .w32 input_var).output i₀)
  have hu : ∀ j : Fin 8,
      u[j.val] = ((Sparse32.unsignedDigit input j : ℕ) : Field) := by
    intro j
    simpa only [u, Sparse32.unsignedDigit, SmallNormalize.main, circuit_norm,
      count, Vector.getElem_map] using h_holds.2 j
  intro i
  let uv : Var Digits Field := (SmallNormalize.main .w32 input_var).output i₀
  have he := congrArg (fun v : Digits Field => v[i.val]) (eval_balanceExpr env uv)
  have hb := balance_spec input u hu i
  simpa only [uv, u, SmallNormalize.main, circuit_norm] using he.trans hb

theorem completeness :
    GeneralFormalCircuit.Completeness Field main ProverAssumptions ProverSpec := by
  circuit_proof_start [SmallNormalize.circuit, SmallNormalize.Assumptions,
    SmallNormalize.Spec, SmallNormalize.ProverAssumptions, SmallNormalize.ProverSpec]
  exact h_assumptions

def circuit : GeneralFormalCircuit Field Emu Digits where
  main := main
  Assumptions := Assumptions
  Spec := Spec
  ProverAssumptions := ProverAssumptions
  ProverSpec := ProverSpec
  soundness := soundness
  completeness := completeness

lemma output_eq (raw : Var Emu Field) (n : ℕ) :
    (main raw).output n = balanceExpr ((SmallNormalize.main .w32 raw).output n) := by
  change balanceExpr ((SmallNormalize.circuit .w32 raw).output n) = _
  rw [SmallNormalize.call_output]

lemma call_output (raw : Var Emu Field) (n : ℕ) :
    (circuit raw).output n = (main raw).output n :=
  (elaborated.output_eq raw n).symm

end Solution.Secp256k1ScalarMulFixedBase.Sparse32Normalize
end

/- === Sparse32NormalizeShape === -/
section
namespace Solution.Secp256k1ScalarMulFixedBase.Sparse32Normalize

open SmallSquare Sparse32 Challenge.CostR1CS Cost

set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 20000

theorem cost (raw : Var Emu Field) : CostIs (main raw) ⟨252, 256⟩ := by
  rw [show (⟨252, 256⟩ : Count) = ⟨252, 256⟩ + Count.zero by decide]
  unfold main
  refine CostIs.bind
    (CostIs.subcircuitWithAssertion (SmallNormalize.cost .w32 raw)) fun _ => ?_
  exact CostIs.pure _

theorem shape (raw : Var Emu Field) (hraw : AffineW raw) :
    IsR1CSCirc (main raw) := by
  unfold main
  refine IsR1CSCirc.bind_out
    (IsR1CSCirc.subcircuitWithAssertion
      (SmallNormalize.shape .w32 raw hraw)) fun _ => ?_
  exact IsR1CSCirc.pure _

lemma affine_balanceExpr (u : Var Digits Field) (hu : AffineW u) :
    AffineW (balanceExpr u) := by
  intro i hi
  rw [balanceExpr, Vector.getElem_ofFn]
  exact Affine.sub (hu i hi) (Affine.const _)

lemma affine_output (raw : Var Emu Field) (hraw : AffineW raw) (n : ℕ) :
    AffineW ((main raw).output n) := by
  rw [output_eq]
  exact affine_balanceExpr _ (SmallNormalize.affine_output .w32 raw hraw n)

end Solution.Secp256k1ScalarMulFixedBase.Sparse32Normalize
end
