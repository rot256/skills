import Solution.Secp256k1ScalarMul.CompleteAdd
import Solution.Secp256k1ScalarMul.DivOrZeroF3
import Solution.Secp256k1ScalarMul.DivOrZeroS32
import Solution.Secp256k1ScalarMul.MulModSub2F32
import Solution.Secp256k1ScalarMul.EqFe
import Solution.Secp256k1ScalarMul.Mux
import Challenge.Utils.ComputableWitnessLemmas

/-!
# Stage 1 of the fused double-add: flags, conditional slope, and x_S

Computes, for `R = (rx, ry)` and `T = (tx, ty)` (coordinates canonical):
* `sameX1 = [tx = rx]`, `oppY1 = [ry = ty]` — the case flags;
* `λ₁` — the chord slope of `(R, T)`, or the tangent slope at `R` when
  `sameX1` (division-by-zero yields `λ₁ = 0`, flagged by the denominator);
* `x_S = λ₁² − rx − tx`.

The specification exposes the slope certificate conditioned on the `sameX1`
flag value, matching `FusedStepTheorems.fused_soundness_core` exactly.
-/

namespace Solution.Secp256k1ScalarMul
namespace SlopeXS

open Specs.ShortWeierstrass Specs.Secp256k1
open CompleteAdd

structure Inputs (F : Type) where
  rx : Emu F
  ry : Emu F
  tx : Emu F
  ty : Emu F
  /-- The `T = 𝒪` flag.  It joins `sameX1` in selecting the tangent branch, so
  that on that path `λ₁` is the tangent slope at `R` and stage 2 can take its
  own slope to be zero, making the stage-2 multiplier a *free affine* sum. -/
  tIsInf : F
deriving ProvableStruct

structure Output (F : Type) where
  sameX1 : F
  oppY1 : F
  /-- `sameX1 ∨ tIsInf`: the tangent-branch selector. -/
  sel1 : F
  lam1 : Emu F
  xS : Emu F
  /-- The eight 32-bit limbs of `λ₁`, exposed for free: `lam1` is their affine
  recombination, so a downstream certificate can run in base `2^32`. -/
  lam32 : BigInt 8 F
deriving ProvableStruct

def yDiffInvCompute (input : Var Inputs (F circomPrime))
    (env : ProverEnvironment (F circomPrime)) : F circomPrime :=
  let rx := Vector.map (Expression.eval env.toEnvironment) input.rx
  let tx := Vector.map (Expression.eval env.toEnvironment) input.tx
  let d := Expression.eval env.toEnvironment (input.ry[0] - input.ty[0])
  if decodeFe tx = decodeFe rx then
    if d = 0 then 0 else d⁻¹
  else 0

/-- Boolean OR via `a + b - a*b` for boolean `a`, `b`. -/
lemma isBool_or_expr {x a b : F circomPrime} (ha : IsBool a) (hb : IsBool b)
    (h : x = a + b + -(a * b)) : IsBool x := by
  rcases ha with h1 | h1 <;> rcases hb with h2 | h2 <;> rw [h, h1, h2]
  · exact Or.inl (by ring)
  · exact Or.inr (by ring)
  · exact Or.inr (by ring)
  · exact Or.inr (by ring)

/-- The OR is `1` as soon as its left operand is. -/
lemma or_eq_one_of_left {x a b : F circomPrime} (h : x = a + b + -(a * b)) (ha : a = 1) :
    x = 1 := by rw [h, ha]; ring

def main (input : Var Inputs (F circomPrime)) :
    Circuit (F circomPrime) (Var Output (F circomPrime)) := do
  let { rx, ry, tx, ty, tIsInf } := input

  let sameX1 ← subcircuit EqFe.circuit { a := tx, b := rx }
  let yDiff := ry[0] - ty[0]
  let yDiffInv ← witnessField (yDiffInvCompute input)
  let oppY1 <== yDiff * yDiffInv
  assertZero (yDiff * (sameX1 - oppY1))
  let sel1 <== sameX1 + tIsInf - sameX1 * tIsInf

  -- borrow-free chord numerator/denominator and the tangent denominator 2·ry
  let dyU : Var Emu (F circomPrime) := Vector.ofFn fun k : Fin numLimbs =>
    ty[k.val]'k.isLt
      + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
        - ry[k.val]'k.isLt)
  let dxU : Var Emu (F circomPrime) := Vector.ofFn fun k : Fin numLimbs =>
    tx[k.val]'k.isLt
      + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
        - rx[k.val]'k.isLt)
  let tDen : Var Emu (F circomPrime) := Vector.ofFn fun k : Fin numLimbs =>
    ry[k.val]'k.isLt + ry[k.val]'k.isLt

  let den1 ← subcircuit (Mux.circuit (M := Emu))
    { selector := sel1, ifTrue := tDen, ifFalse := dxU }
  let lam32 ← subcircuit DivOrZeroS32.circuit
    { sel := sel1, x := rx, dyU := dyU, den := den1 }
  let lam1 : Var Emu (F circomPrime) := Limbs32.emuOf32 lam32

  let xS ← subcircuit MulModSub2F32.circuit { a := lam32, b := lam32, s1 := rx, s2 := tx }

  return { sameX1 := sameX1, oppY1 := oppY1, sel1 := sel1, lam1 := lam1, xS := xS, lam32 := lam32 }

instance elaborated : ElaboratedCircuit (F circomPrime) Inputs Output main := by
  elaborate_circuit

def Assumptions (input : Inputs (F circomPrime)) : Prop :=
  Fe.Valid input.rx ∧ Fe.Valid input.ry ∧ Fe.Valid input.tx ∧ Fe.Valid input.ty ∧
    IsBool input.tIsInf

def Spec (input : Inputs (F circomPrime)) (out : Output (F circomPrime)) : Prop :=
  out.sameX1 = (if decodeFe input.tx = decodeFe input.rx then 1 else 0) ∧
  out.oppY1 = (if out.sameX1 = 1 then
    if input.ry[0] = input.ty[0] then 0 else 1
    else 0) ∧
  out.sel1 = out.sameX1 + input.tIsInf - out.sameX1 * input.tIsInf ∧
  BigInt.Normalized limbBits out.lam1 ∧
  ((if out.sel1 = 1 then decodeFe input.ry + decodeFe input.ry
      else decodeFe input.tx - decodeFe input.rx) ≠ 0 →
    decodeFe out.lam1 *
      (if out.sel1 = 1 then decodeFe input.ry + decodeFe input.ry
        else decodeFe input.tx - decodeFe input.rx) =
      (if out.sel1 = 1 then 3 * (decodeFe input.rx * decodeFe input.rx)
        else decodeFe input.ty - decodeFe input.ry)) ∧
  Fe.Valid out.xS ∧
  decodeFe out.xS = decodeFe out.lam1 * decodeFe out.lam1
    - decodeFe input.rx - decodeFe input.tx ∧
  BigInt.Normalized 32 out.lam32 ∧
  out.lam1 = Limbs32.emuOf32V out.lam32

set_option maxHeartbeats 1600000 in
theorem soundness : Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [EqFe.circuit, EqFe.Assumptions, EqFe.Spec,
    Mux.circuit, Mux.Assumptions, Mux.Spec,
    DivOrZeroS32.circuit, DivOrZeroS32.Assumptions, DivOrZeroS32.Spec,
    MulModSub2F32.circuit, MulModSub2F32.Assumptions, MulModSub2F32.Spec, secpParams]
  obtain ⟨hsameX1, hcancel, hcancelG, hsel1, hden1, hlam1, hxS⟩ := h_holds
  rw [show i₀ + 3 + 1 + 1 = i₀ + 5 from rfl] at hsel1 hden1 hlam1 hxS
  obtain ⟨hRx, hRy, hTx, hTy, htib⟩ := h_assumptions
  obtain ⟨hIRx, hIRy, hITx, hITy, hITi⟩ := h_input
  -- chord denominator decode
  have hdxe : decodeFe (Vector.map (Expression.eval env)
        (Vector.ofFn fun k : Fin numLimbs => input_var_tx[k.val]'k.isLt
          + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
            - input_var_rx[k.val]'k.isLt)))
      = decodeFe input_tx - decodeFe input_rx := by
    rw [map_eval_borrow, hITx, hIRx]
    exact decodeFe_borrow input_tx input_rx hTx.1 hRx
  have hdye : decodeFe (Vector.map (Expression.eval env)
        (Vector.ofFn fun k : Fin numLimbs => input_var_ty[k.val]'k.isLt
          + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
            - input_var_ry[k.val]'k.isLt)))
      = decodeFe input_ty - decodeFe input_ry := by
    rw [map_eval_borrow, hITy, hIRy]
    exact decodeFe_borrow input_ty input_ry hTy.1 hRy
  have hsameX1' := EqFe.flag_eq_decode_eq hTx hRx hsameX1
  have hsx1b : IsBool _ := isBool_of_eq_ite hsameX1'
  have hsel1b : IsBool (env.get (i₀ + 5)) :=
    isBool_or_expr hsx1b htib hsel1
  have hRy0 : Expression.eval env input_var_ry[0] = input_ry[0] := by
    simpa only [Vector.getElem_map] using
      congrArg (fun v : Emu (F circomPrime) => v[0]) hIRy
  have hTy0 : Expression.eval env input_var_ty[0] = input_ty[0] := by
    simpa only [Vector.getElem_map] using
      congrArg (fun v : Emu (F circomPrime) => v[0]) hITy
  have hoppY1' : env.get (i₀ + 3 + 1) =
      (if env.get (i₀ + 2) = 1 then
        if input_ry[0] = input_ty[0] then 0 else 1
        else 0) := by
    rw [hRy0, hTy0] at hcancel hcancelG
    by_cases h : input_ry[0] = input_ty[0]
    · have hd0 : input_ry[0] + -input_ty[0] = 0 := by
        rw [h]
        ring
      rw [hd0] at hcancel
      simp only [zero_mul] at hcancel
      rw [hcancel]
      split <;> rfl
    · have hd : input_ry[0] + -input_ty[0] ≠ 0 := by
        simpa [sub_eq_add_neg] using sub_ne_zero.mpr h
      have hsame_or_cancel : env.get (i₀ + 2) = env.get (i₀ + 3 + 1) := by
        have hzero : env.get (i₀ + 2) + -env.get (i₀ + 3 + 1) = 0 :=
          mul_left_cancel₀ hd hcancelG
        exact sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hzero)
      rw [← hsame_or_cancel]
      by_cases hs : env.get (i₀ + 2) = 1
      · rw [if_pos hs, if_neg h, hs]
      · have hs0 : env.get (i₀ + 2) = 0 := by
          rcases hsx1b with hs0 | hs1
          · exact hs0
          · exact False.elim (hs hs1)
        rw [if_neg hs, hs0]
  have hden1b := hden1 hsel1b
  rw [map_eval_sum2_input env _ input_ry hIRy] at hden1b
  -- dyU (chord numerator) bounds
  have hdyU_limb : ∀ i : Fin numLimbs,
      ZMod.val (Expression.eval env
        ((Vector.ofFn fun k : Fin numLimbs => input_var_ty[k.val]'k.isLt
          + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
            - input_var_ry[k.val]'k.isLt))[i.val]'i.isLt)) < 3 * 2 ^ limbBits := by
    intro i
    have hcell := congrArg (fun v : Emu (F circomPrime) => v[i.val]'i.isLt)
      (map_eval_borrow env input_var_ty input_var_ry)
    rw [hITy, hIRy] at hcell
    simp only [Vector.getElem_map, Vector.getElem_ofFn] at hcell ⊢
    rw [hcell]
    exact limb_borrow_lt i.val (hTy.1 i) (hRy.1 i)
  have hdyU_val : BigInt.value limbBits (Vector.map (Expression.eval env)
        (Vector.ofFn fun k : Fin numLimbs => input_var_ty[k.val]'k.isLt
          + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
            - input_var_ry[k.val]'k.isLt))) < 3 * P256 := by
    rw [map_eval_borrow, hITy, hIRy]
    exact value_borrow_lt input_ty input_ry hTy hRy
  obtain ⟨hlam1v, hlam1e⟩ := hlam1 (by
    refine ⟨hRx, hsel1b, hdyU_limb, hdyU_val, ?_, ?_, ?_⟩
    · intro i
      have hcellden : (Vector.map (Expression.eval env)
            (Vector.mapRange numLimbs fun j =>
              var (F := F circomPrime) { index := i₀ + 5 + 1 + j }))[i.val]'i.isLt
          = env.get (i₀ + 5 + 1 + i.val) := by
        rw [Vector.getElem_map, Vector.getElem_mapRange]; rfl
      rw [← hcellden, hden1b]
      split
      · exact lt_trans (limb_sum2_bound input_ry hRy.1 i) (by norm_num [limbBits])
      · have hcell := congrArg (fun v : Emu (F circomPrime) => v[i.val]'i.isLt)
          (map_eval_borrow env input_var_tx input_var_rx)
        rw [hITx, hIRx] at hcell
        simp only [Vector.getElem_map, Vector.getElem_ofFn] at hcell ⊢
        rw [hcell]
        exact limb_borrow_lt i.val (hTx.1 i) (hRx.1 i)
    · rw [hden1b]
      split
      · exact lt_trans (value_sum2_bound input_ry hRy) (by have := P256_pos; omega)
      · rw [map_eval_borrow, hITx, hIRx]
        exact value_borrow_lt input_tx input_rx hTx hRx
    · rw [hden1b]
      split
      · exact value_sum2_alias input_ry hRy
      · rename_i hsx_ne
        intro hmod
        exfalso
        apply hsx_ne
        have hd0 : decodeFe (Vector.map (Expression.eval env)
              (Vector.ofFn fun k : Fin numLimbs => input_var_tx[k.val]'k.isLt
                + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
                  - input_var_rx[k.val]'k.isLt))) = 0 := by
          have hcast := (ZMod.natCast_eq_zero_iff (BigInt.value limbBits
            (Vector.map (Expression.eval env)
              (Vector.ofFn fun k : Fin numLimbs => input_var_tx[k.val]'k.isLt
                + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
                  - input_var_rx[k.val]'k.isLt)))) P256).mpr (Nat.dvd_of_mod_eq_zero hmod)
          simpa only [decodeFe] using hcast
        rw [hdxe] at hd0
        exact or_eq_one_of_left hsel1 (by rw [hsameX1', if_pos (sub_eq_zero.mp hd0)]))
  obtain ⟨hxSv, hxSe⟩ := hxS ⟨hlam1v, hlam1v, hRx, hTx⟩
  -- decoded denominator of the divider equals the flag-conditioned ite
  have hdend : decodeFe (Vector.map (Expression.eval env)
        (Vector.mapRange numLimbs fun j =>
          var (F := F circomPrime) { index := i₀ + 5 + 1 + j }))
      = if env.get (i₀ + 5) = 1
        then decodeFe input_ry + decodeFe input_ry
        else decodeFe input_tx - decodeFe input_rx := by
    rw [hden1b, apply_ite decodeFe, decodeFe_sum2 input_ry hRy.1, hdxe]
  simp only [Limbs32.eval_emuOf32]
  have hsel1S : env.get (i₀ + 5)
      = env.get (i₀ + 2) + input_tIsInf - env.get (i₀ + 2) * input_tIsInf := by
    rw [hsel1]; ring
  refine ⟨hsameX1', hoppY1', hsel1S,
    Limbs32.normalized_emuOf32 hlam1v, ?_, hxSv, hxSe,
    hlam1v, by first | rfl | trivial⟩
  intro hne
  rw [← hdend] at hne
  have h := hlam1e hne
  rw [hdend] at h
  rw [h]
  split
  · rfl
  · exact hdye

set_option maxHeartbeats 1600000 in
theorem completeness : Completeness (F circomPrime) main Assumptions := by
  circuit_proof_start [EqFe.circuit, EqFe.Assumptions, EqFe.Spec,
    Mux.circuit, Mux.Assumptions, Mux.Spec,
    DivOrZeroS32.circuit, DivOrZeroS32.Assumptions, DivOrZeroS32.Spec,
    MulModSub2F32.circuit, MulModSub2F32.Assumptions, MulModSub2F32.Spec, secpParams]
  obtain ⟨hsameX1, hcancel, hcancelG, hsel1, hden1, hlam1, hxS⟩ := h_env
  rw [show i₀ + 3 + 1 + 1 = i₀ + 5 from rfl] at hsel1 hden1 hlam1 hxS
  obtain ⟨hRx, hRy, hTx, hTy, htib⟩ := h_assumptions
  obtain ⟨hIRx, hIRy, hITx, hITy, hITi⟩ := h_input
  -- chord denominator decode
  have hdxe : decodeFe (Vector.map (Expression.eval env.toEnvironment)
        (Vector.ofFn fun k : Fin numLimbs => input_var_tx[k.val]'k.isLt
          + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
            - input_var_rx[k.val]'k.isLt)))
      = decodeFe input_tx - decodeFe input_rx := by
    rw [map_eval_borrow, hITx, hIRx]
    exact decodeFe_borrow input_tx input_rx hTx.1 hRx
  have hdye : decodeFe (Vector.map (Expression.eval env.toEnvironment)
        (Vector.ofFn fun k : Fin numLimbs => input_var_ty[k.val]'k.isLt
          + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
            - input_var_ry[k.val]'k.isLt)))
      = decodeFe input_ty - decodeFe input_ry := by
    rw [map_eval_borrow, hITy, hIRy]
    exact decodeFe_borrow input_ty input_ry hTy.1 hRy
  have hsameX1' := EqFe.flag_eq_decode_eq hTx hRx hsameX1
  have hsx1b : IsBool _ := isBool_of_eq_ite hsameX1'
  have hsel1b : IsBool (env.get (i₀ + 5)) :=
    isBool_or_expr hsx1b htib hsel1
  have hRy0 : Expression.eval env.toEnvironment input_var_ry[0] = input_ry[0] := by
    simpa only [Vector.getElem_map] using
      congrArg (fun v : Emu (F circomPrime) => v[0]) hIRy
  have hTy0 : Expression.eval env.toEnvironment input_var_ty[0] = input_ty[0] := by
    simpa only [Vector.getElem_map] using
      congrArg (fun v : Emu (F circomPrime) => v[0]) hITy
  have hDiff0 :
      Expression.eval env.toEnvironment (input_var_ry[0] - input_var_ty[0]) =
        input_ry[0] + -input_ty[0] := by
    simp only [Expression.eval]
    rw [hRy0, hTy0]
    ring
  have hcancelAssert :
      (Expression.eval env.toEnvironment input_var_ry[0] +
          -Expression.eval env.toEnvironment input_var_ty[0]) *
        (env.get (i₀ + 2) + -env.get (i₀ + 3 + 1)) = 0 := by
    rw [hRy0, hTy0, hcancelG, hcancel]
    simp only [yDiffInvCompute]
    rw [hIRx, hITx, hRy0, hTy0, hDiff0]
    by_cases hx : decodeFe input_tx = decodeFe input_rx
    · rw [if_pos hx]
      have hsx : env.get (i₀ + 2) = 1 := by rw [hsameX1', if_pos hx]
      rw [hsx]
      by_cases hy : input_ry[0] + -input_ty[0] = 0
      · rw [if_pos hy, hy]
        ring
      · rw [if_neg hy, mul_inv_cancel₀ hy]
        ring
    · rw [if_neg hx]
      have hsx : env.get (i₀ + 2) = 0 := by rw [hsameX1', if_neg hx]
      rw [hsx]
      ring
  have hden1b := hden1 hsel1b
  rw [map_eval_sum2_input env.toEnvironment _ input_ry hIRy] at hden1b
  -- dyU (chord numerator) bounds
  have hdyU_limb : ∀ i : Fin numLimbs,
      ZMod.val (Expression.eval env.toEnvironment
        ((Vector.ofFn fun k : Fin numLimbs => input_var_ty[k.val]'k.isLt
          + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
            - input_var_ry[k.val]'k.isLt))[i.val]'i.isLt)) < 3 * 2 ^ limbBits := by
    intro i
    have hcell := congrArg (fun v : Emu (F circomPrime) => v[i.val]'i.isLt)
      (map_eval_borrow env.toEnvironment input_var_ty input_var_ry)
    rw [hITy, hIRy] at hcell
    simp only [Vector.getElem_map, Vector.getElem_ofFn] at hcell ⊢
    rw [hcell]
    exact limb_borrow_lt i.val (hTy.1 i) (hRy.1 i)
  have hdyU_val : BigInt.value limbBits (Vector.map (Expression.eval env.toEnvironment)
        (Vector.ofFn fun k : Fin numLimbs => input_var_ty[k.val]'k.isLt
          + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
            - input_var_ry[k.val]'k.isLt))) < 3 * P256 := by
    rw [map_eval_borrow, hITy, hIRy]
    exact value_borrow_lt input_ty input_ry hTy hRy
  obtain ⟨hlam1v, hlam1e⟩ := hlam1 (by
    refine ⟨hRx, hsel1b, hdyU_limb, hdyU_val, ?_, ?_, ?_⟩
    · intro i
      have hcellden : (Vector.map (Expression.eval env.toEnvironment)
            (Vector.mapRange numLimbs fun j =>
              var (F := F circomPrime) { index := i₀ + 5 + 1 + j }))[i.val]'i.isLt
          = env.get (i₀ + 5 + 1 + i.val) := by
        rw [Vector.getElem_map, Vector.getElem_mapRange]; rfl
      rw [← hcellden, hden1b]
      split
      · exact lt_trans (limb_sum2_bound input_ry hRy.1 i) (by norm_num [limbBits])
      · have hcell := congrArg (fun v : Emu (F circomPrime) => v[i.val]'i.isLt)
          (map_eval_borrow env.toEnvironment input_var_tx input_var_rx)
        rw [hITx, hIRx] at hcell
        simp only [Vector.getElem_map, Vector.getElem_ofFn] at hcell ⊢
        rw [hcell]
        exact limb_borrow_lt i.val (hTx.1 i) (hRx.1 i)
    · rw [hden1b]
      split
      · exact lt_trans (value_sum2_bound input_ry hRy) (by have := P256_pos; omega)
      · rw [map_eval_borrow, hITx, hIRx]
        exact value_borrow_lt input_tx input_rx hTx hRx
    · rw [hden1b]
      split
      · exact value_sum2_alias input_ry hRy
      · rename_i hsx_ne
        intro hmod
        exfalso
        apply hsx_ne
        have hd0 : decodeFe (Vector.map (Expression.eval env.toEnvironment)
              (Vector.ofFn fun k : Fin numLimbs => input_var_tx[k.val]'k.isLt
                + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
                  - input_var_rx[k.val]'k.isLt))) = 0 := by
          have hcast := (ZMod.natCast_eq_zero_iff (BigInt.value limbBits
            (Vector.map (Expression.eval env.toEnvironment)
              (Vector.ofFn fun k : Fin numLimbs => input_var_tx[k.val]'k.isLt
                + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
                  - input_var_rx[k.val]'k.isLt)))) P256).mpr (Nat.dvd_of_mod_eq_zero hmod)
          simpa only [decodeFe] using hcast
        rw [hdxe] at hd0
        exact or_eq_one_of_left hsel1 (by rw [hsameX1', if_pos (sub_eq_zero.mp hd0)]))
  refine ⟨hcancelG, hcancelAssert, hsel1, hsel1b, ⟨hRx, hsel1b, hdyU_limb, hdyU_val, ?_, ?_, ?_⟩,
    ⟨hlam1v, hlam1v, hRx, hTx⟩⟩
  · intro i
    have hcellden : (Vector.map (Expression.eval env.toEnvironment)
          (Vector.mapRange numLimbs fun j =>
            var (F := F circomPrime) { index := i₀ + 5 + 1 + j }))[i.val]'i.isLt
        = env.get (i₀ + 5 + 1 + i.val) := by
      rw [Vector.getElem_map, Vector.getElem_mapRange]; rfl
    rw [← hcellden, hden1b]
    split
    · exact lt_trans (limb_sum2_bound input_ry hRy.1 i) (by norm_num [limbBits])
    · have hcell := congrArg (fun v : Emu (F circomPrime) => v[i.val]'i.isLt)
        (map_eval_borrow env.toEnvironment input_var_tx input_var_rx)
      rw [hITx, hIRx] at hcell
      simp only [Vector.getElem_map, Vector.getElem_ofFn] at hcell ⊢
      rw [hcell]
      exact limb_borrow_lt i.val (hTx.1 i) (hRx.1 i)
  · rw [hden1b]
    split
    · exact lt_trans (value_sum2_bound input_ry hRy) (by have := P256_pos; omega)
    · rw [map_eval_borrow, hITx, hIRx]
      exact value_borrow_lt input_tx input_rx hTx hRx
  · rw [hden1b]
    split
    · exact value_sum2_alias input_ry hRy
    · rename_i hsx_ne
      intro hmod
      exfalso
      apply hsx_ne
      have hd0 : decodeFe (Vector.map (Expression.eval env.toEnvironment)
            (Vector.ofFn fun k : Fin numLimbs => input_var_tx[k.val]'k.isLt
              + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
                - input_var_rx[k.val]'k.isLt))) = 0 := by
        have hcast := (ZMod.natCast_eq_zero_iff (BigInt.value limbBits
          (Vector.map (Expression.eval env.toEnvironment)
            (Vector.ofFn fun k : Fin numLimbs => input_var_tx[k.val]'k.isLt
              + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
                - input_var_rx[k.val]'k.isLt)))) P256).mpr (Nat.dvd_of_mod_eq_zero hmod)
        simpa only [decodeFe] using hcast
      rw [hdxe] at hd0
      exact or_eq_one_of_left hsel1 (by rw [hsameX1', if_pos (sub_eq_zero.mp hd0)])

def circuit : FormalCircuit (F circomPrime) Inputs Output where
  main; elaborated; Assumptions; Spec; soundness; completeness

end SlopeXS
end Solution.Secp256k1ScalarMul
