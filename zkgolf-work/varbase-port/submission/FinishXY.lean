import Solution.Secp256k1ScalarMul.CompleteAdd
import Solution.Secp256k1ScalarMul.Double
import Solution.Secp256k1ScalarMul.Params
import Solution.Secp256k1ScalarMul.MulModSub2W32M
import Solution.Secp256k1ScalarMul.MulModSub2F32W2
import Challenge.Utils.ComputableWitnessLemmas

/-!
# Stage 3 of the fused double-add: the output coordinates

Given the stage-2 multiplier `A` and the effective `x_S` and `R = (rx, ry)`:

* `x₄ = A² − x_S' − rx`;
* `y₄ = A·(x₄ − rx) − ry`.

Both formulas are now **unconditional**: stage 2 arranges `A ≡ −λ₁` on the
`T = 𝒪` branch (by negating the guarded denominator and feeding `2·λ₁` to the
numerator mux), so `x₄` is unchanged (it is a square) and the sign that used to
be folded into a four-cell borrow-operand `Mux` is already carried by `A`.
That deletes the `bMul` mux outright: four allocations and four rows per step.
-/

namespace Solution.Secp256k1ScalarMul
namespace FinishXY

open Specs.ShortWeierstrass Specs.Secp256k1
open CompleteAdd

structure Inputs (F : Type) where
  rx : Emu F
  ry : Emu F
  tIsInf : F
  mulA : Emu F
  xSe : Emu F
  /-- The eight 32-bit limbs of `mulA`, so the squaring certificate can run in
  base `2^32` (`mulA` is their affine recombination). -/
  mulA32 : BigInt 8 F
deriving ProvableStruct

structure Output (F : Type) where
  x4 : Emu F
  y4 : Emu F
deriving ProvableStruct

def main (input : Var Inputs (F circomPrime)) :
    Circuit (F circomPrime) (Var Output (F circomPrime)) := do
  let { rx, ry, tIsInf := _, mulA := _, xSe, mulA32 } := input

  let x4 ← subcircuit MulModSub2F32W2.circuit
    { a := mulA32, b := mulA32, s1 := xSe, s2 := rx }

  let bChord : Var Emu (F circomPrime) := Vector.ofFn fun k : Fin numLimbs =>
    x4[k.val]'k.isLt
      + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
        - rx[k.val]'k.isLt)
  let y4 ← subcircuit MulModSub2W32M.circuit
    { a := mulA32, b := bChord, s1 := ry, s2 := zeroConst }

  return { x4 := x4, y4 := y4 }

instance elaborated : ElaboratedCircuit (F circomPrime) Inputs Output main := by
  elaborate_circuit

def Assumptions (input : Inputs (F circomPrime)) : Prop :=
  Fe.Valid input.rx ∧ Fe.Valid input.ry ∧ IsBool input.tIsInf ∧
    Fe.NormW2 input.mulA ∧ Fe.Valid input.xSe ∧
    Norm33 input.mulA32 ∧ input.mulA = Limbs32.emuOf32V input.mulA32

def Spec (input : Inputs (F circomPrime)) (out : Output (F circomPrime)) : Prop :=
  Fe.Valid out.x4 ∧
  decodeFe out.x4 = decodeFe input.mulA * decodeFe input.mulA
    - decodeFe input.xSe - decodeFe input.rx ∧
  Fe.Valid out.y4 ∧
  decodeFe out.y4 = decodeFe input.mulA * (decodeFe out.x4 - decodeFe input.rx)
    - decodeFe input.ry

theorem soundness : Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [MulModSub2W32M.circuit, MulModSub2W32M.Assumptions, MulModSub2W32M.Spec,
    MulModSub2F32W2.circuit, MulModSub2F32W2.Assumptions, MulModSub2F32W2.Spec, secpParams]
  obtain ⟨hx4, hy4⟩ := h_holds
  obtain ⟨hRx, hRy, htib, hmulAv, hxSev, hA32v, hmulAeq⟩ := h_assumptions
  obtain ⟨hIRx, hIRy, hITi, hImulA, hIxSe, hIA32⟩ := h_input
  obtain ⟨hx4v, hx4e⟩ := hx4 ⟨hA32v, hA32v, hxSev, hRx⟩
  rw [← hmulAeq] at hx4e
  -- borrow decode for the multiplier operand
  have hbCd : decodeFe (Vector.map (Expression.eval env)
        (Vector.ofFn fun k : Fin numLimbs =>
          (var { index := i₀ + k.val } : Expression (F circomPrime))
          + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
            - input_var_rx[k.val]'k.isLt)))
      = decodeFe (Vector.map (Expression.eval env)
          (Vector.mapRange numLimbs fun j => var { index := i₀ + j }))
        - decodeFe input_rx := by
    have hconv : (Vector.ofFn fun k : Fin numLimbs =>
          (var { index := i₀ + k.val } : Expression (F circomPrime))
          + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
            - input_var_rx[k.val]'k.isLt))
        = (Vector.ofFn fun k : Fin numLimbs =>
          (Vector.mapRange numLimbs fun j =>
            var (F := F circomPrime) { index := i₀ + j })[k.val]'k.isLt
          + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
            - input_var_rx[k.val]'k.isLt)) := rfl
    rw [hconv, map_eval_borrow, hIRx]
    exact decodeFe_borrow _ input_rx hx4v.1 hRx
  -- y₄ multiply-subtract discharge
  obtain ⟨hy4v, hy4e⟩ := hy4 (by
    refine ⟨hA32v, ?_, hRy, fe_valid_eval_zeroConst env⟩
    · intro i
      have hx4l := hx4v.1 i
      simp only [Fin.getElem_fin, Vector.getElem_map, Vector.getElem_mapRange] at hx4l
      have hpq := congrArg (fun v : Emu (F circomPrime) => v[i.val]'i.isLt) hIRx
      simp only [Vector.getElem_map] at hpq
      simp only [Vector.getElem_map, Vector.getElem_ofFn]
      simp only [circuit_norm, hpq]
      have hlb := limb_borrow_lt i.val hx4l (hRx.1 i)
      rw [sub_eq_add_neg] at hlb
      exact hlb)
  rw [← hmulAeq] at hy4e
  -- assemble
  have hz0 : decodeFe (Vector.map (Expression.eval env) zeroConst) = 0 := by
    rw [DivOrZero.eval_zeroConst, decodeFe, value_emuOfNat (by positivity), Nat.cast_zero]
  rw [hz0, sub_zero] at hy4e
  refine ⟨hx4v, hx4e, hy4v, ?_⟩
  rw [hy4e, hbCd]

theorem completeness : Completeness (F circomPrime) main Assumptions := by
  circuit_proof_start [MulModSub2W32M.circuit, MulModSub2W32M.Assumptions, MulModSub2W32M.Spec,
    MulModSub2F32W2.circuit, MulModSub2F32W2.Assumptions, MulModSub2F32W2.Spec, secpParams]
  obtain ⟨hx4, hy4⟩ := h_env
  obtain ⟨hRx, hRy, htib, hmulAv, hxSev, hA32v, hmulAeq⟩ := h_assumptions
  obtain ⟨hIRx, hIRy, hITi, hImulA, hIxSe, hIA32⟩ := h_input
  obtain ⟨hx4v, hx4e⟩ := hx4 ⟨hA32v, hA32v, hxSev, hRx⟩
  refine ⟨⟨hA32v, hA32v, hxSev, hRx⟩,
    ⟨hA32v, ?_, hRy, fe_valid_eval_zeroConst env.toEnvironment⟩⟩
  · intro i
    have hx4l := hx4v.1 i
    simp only [Fin.getElem_fin, Vector.getElem_map, Vector.getElem_mapRange] at hx4l
    have hpq := congrArg (fun v : Emu (F circomPrime) => v[i.val]'i.isLt) hIRx
    simp only [Vector.getElem_map] at hpq
    simp only [Vector.getElem_map, Vector.getElem_ofFn]
    simp only [circuit_norm, hpq]
    have hlb := limb_borrow_lt i.val hx4l (hRx.1 i)
    rw [sub_eq_add_neg] at hlb
    exact hlb

def circuit : FormalCircuit (F circomPrime) Inputs Output where
  main; elaborated; Assumptions; Spec; soundness; completeness

end FinishXY
end Solution.Secp256k1ScalarMul
