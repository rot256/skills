import Solution.Secp256k1ScalarMul.CompleteAdd
import Solution.Secp256k1ScalarMul.DivOrZeroS32
import Solution.Secp256k1ScalarMul.DivOrZeroN32
import Solution.Secp256k1ScalarMul.Limbs33
import Solution.Secp256k1ScalarMul.AddMod
import Solution.Secp256k1ScalarMul.ParamsW2
import Solution.Secp256k1ScalarMul.EqFe
import Solution.Secp256k1ScalarMul.Mux
import Challenge.Utils.ComputableWitnessLemmas

/-!
# Stage 2 of the fused double-add: the second conditional slope

Given `R = (rx, ry)`, the `T = 𝒪` flag, `λ₁` and `x_S` from stage 1, compute:
* `xSe` — `x_S` re-routed to `rx` when `T = 𝒪` (forces the tangent branch);
* `sameX2 = [xSe = rx]` and `tsel = tIsInf ∨ sameX2`;
* `w` — `2·ry / (xSe − rx)` on the chord path, `3·rx²/(2·ry)` on the tangent
  path (`tsel` muxes the denominator so its `≡ 0 (mod p)` assumption holds);
* `mulA = λ₁ + w` (chord) or `w` (tangent), the stage-2 multiplier.

The `tsel`-denominator mux is what keeps `DivOrZeroF3`'s side condition: a
borrow-free x-difference is `≡ 0 (mod p)` only at limbwise equality, which is
exactly when `sameX2` (hence `tsel`) redirects to the never-vanishing `2·ry`.
-/

namespace Solution.Secp256k1ScalarMul
namespace Slope2

open Specs.ShortWeierstrass Specs.Secp256k1
open CompleteAdd

structure Inputs (F : Type) where
  rx : Emu F
  ry : Emu F
  tIsInf : F
  lam1 : Emu F
  xS : Emu F
  /-- The eight 32-bit limbs of `λ₁` (`lam1` is their affine recombination). -/
  lam32 : BigInt 8 F
deriving ProvableStruct

structure Output (F : Type) where
  xSe : Emu F
  sameX2 : F
  tsel : F
  w : Emu F
  mulA : Emu F
  /-- The eight 32-bit limbs of the stage-2 multiplier, so that stage 3 can run
  its squaring certificate in base `2^32`. -/
  mulA32 : BigInt 8 F
deriving ProvableStruct

/-- Boolean OR via `a + b − a·b` for boolean `a`, `b`. -/
lemma isBool_of_eq_or {x a b : F circomPrime} (ha : IsBool a) (hb : IsBool b)
    (h : x = a + b - a * b) : IsBool x := by
  rcases ha with h1 | h1 <;> rcases hb with h2 | h2 <;> rw [h, h1, h2]
  · exact Or.inl (by ring)
  · exact Or.inr (by ring)
  · exact Or.inr (by ring)
  · exact Or.inr (by ring)

/-- Evaluated shape of a flag-guarded limb vector: the flag lands in limb 0. -/
lemma map_eval_denSafe (env : Environment (F circomPrime))
    (d : Var Emu (F circomPrime)) (z : Expression (F circomPrime)) :
    Vector.map (Expression.eval env) (DivOrZeroS32.denSafeVec d z)
      = Vector.ofFn fun k : Fin numLimbs =>
          (Vector.map (Expression.eval env) d)[k.val]'k.isLt
            + (if k.val = 0 then Expression.eval env z else 0) := by
  apply Vector.ext
  intro i hi
  have hi4 : i < 4 := hi
  simp only [Vector.getElem_map, DivOrZeroS32.denSafeVec, Vector.getElem_ofFn]
  by_cases h : i = 0 <;> simp [h, circuit_norm]

/-- Limbwise value of a flag-guarded limb vector. -/
lemma limb_flag_val {v : Emu (F circomPrime)} {z : F circomPrime} (hz : IsBool z)
    (i : ℕ) (hi : i < numLimbs) (hv : (v[i]'hi).val < 3 * 2 ^ limbBits - 1) :
    ((Vector.ofFn fun k : Fin numLimbs =>
        v[k.val]'k.isLt + (if k.val = 0 then z else 0))[i]'hi).val
      = (v[i]'hi).val + (if i = 0 then z.val else 0) := by
  have hzv : z.val ≤ 1 := by
    rcases hz with h | h
    · rw [h]; simp
    · rw [h, ZMod.val_one]
  simp only [Vector.getElem_ofFn]
  have hb : (3 : ℕ) * 2 ^ limbBits < circomPrime := by decide
  by_cases h0 : i = 0
  · subst h0
    simp only [reduceIte]
    rw [ZMod.val_add_of_lt]
    omega
  · simp only [if_neg h0, add_zero, Nat.add_zero]

set_option maxRecDepth 4000 in
/-- Value of a flag-guarded limb vector. -/
lemma value_flag {v : Emu (F circomPrime)} {z : F circomPrime} (hz : IsBool z)
    (hv : ∀ i : Fin numLimbs, (v[i.val]'i.isLt).val < 3 * 2 ^ limbBits - 1) :
    BigInt.value limbBits (Vector.ofFn fun k : Fin numLimbs =>
        v[k.val]'k.isLt + (if k.val = 0 then z else 0))
      = BigInt.value limbBits v + z.val := by
  rw [BigInt.value_eq_sum, BigInt.value_eq_sum, Fin.sum_univ_four, Fin.sum_univ_four]
  have h0 := limb_flag_val hz 0 (by decide) (hv 0)
  norm_num at h0 ⊢
  rw [h0]
  ring

/-- Sharper borrow-limb bound: the guarded denominator needs one bit of slack in
limb 0 for the tangent flag. -/
lemma limb_borrow_lt' {q p : F circomPrime} (k : ℕ)
    (hq : q.val < 2 ^ limbBits) (hp : p.val < 2 ^ limbBits) :
    (q + (((twoPBorrowDigit k : ℕ) : F circomPrime) - p)).val < 3 * 2 ^ limbBits - 1 := by
  rw [limb_borrow_val k hq hp]
  have hD : twoPBorrowDigit k ≤ 2 ^ 65 - 2 := by
    unfold twoPBorrowDigit; split <;> decide
  have h65 : (2 : ℕ) ^ 65 = 2 * 2 ^ limbBits := by decide
  omega

/-- Limbwise value of the flag-guarded denominator. -/
lemma denSafe_limb_val (env : Environment (F circomPrime))
    (d : Var Emu (F circomPrime)) (z : Expression (F circomPrime))
    (hz : IsBool (Expression.eval env z))
    (i : ℕ) (hi : i < numLimbs)
    (hd : ((Vector.map (Expression.eval env) d)[i]'hi).val < 3 * 2 ^ limbBits - 1) :
    ((Vector.map (Expression.eval env) (DivOrZeroS32.denSafeVec d z))[i]'hi).val
      = ((Vector.map (Expression.eval env) d)[i]'hi).val
        + (if i = 0 then (Expression.eval env z).val else 0) := by
  have h := congrArg (fun v : Emu (F circomPrime) => v[i]'hi) (map_eval_denSafe env d z)
  dsimp only at h
  rw [h]
  exact limb_flag_val hz i hi hd

lemma denSafe_limb_lt (env : Environment (F circomPrime))
    (d : Var Emu (F circomPrime)) (z : Expression (F circomPrime))
    (hz : IsBool (Expression.eval env z))
    (i : ℕ) (hi : i < numLimbs)
    (hd : ((Vector.map (Expression.eval env) d)[i]'hi).val < 3 * 2 ^ limbBits - 1) :
    ((Vector.map (Expression.eval env) (DivOrZeroS32.denSafeVec d z))[i]'hi).val
      < 3 * 2 ^ limbBits := by
  rw [denSafe_limb_val env d z hz i hi hd]
  have hzv : (Expression.eval env z).val ≤ 1 := by
    rcases hz with h | h
    · rw [h]; simp
    · rw [h, ZMod.val_one]
  split <;> omega

lemma denSafe_value (env : Environment (F circomPrime))
    (d : Var Emu (F circomPrime)) (z : Expression (F circomPrime))
    (hz : IsBool (Expression.eval env z))
    (hd : ∀ i : Fin numLimbs,
      ((Vector.map (Expression.eval env) d)[i.val]'i.isLt).val < 3 * 2 ^ limbBits - 1) :
    BigInt.value limbBits (Vector.map (Expression.eval env) (DivOrZeroS32.denSafeVec d z))
      = BigInt.value limbBits (Vector.map (Expression.eval env) d)
        + (Expression.eval env z).val := by
  rw [map_eval_denSafe]
  exact value_flag hz hd

lemma denSafe_decodeFe (env : Environment (F circomPrime))
    (d : Var Emu (F circomPrime)) (z : Expression (F circomPrime))
    (hz : IsBool (Expression.eval env z))
    (hd : ∀ i : Fin numLimbs,
      ((Vector.map (Expression.eval env) d)[i.val]'i.isLt).val < 3 * 2 ^ limbBits - 1) :
    decodeFe (Vector.map (Expression.eval env) (DivOrZeroS32.denSafeVec d z))
      = decodeFe (Vector.map (Expression.eval env) d)
        + (((Expression.eval env z).val : ℕ) : Specs.Secp256k1.Fp) := by
  simp only [decodeFe]
  rw [denSafe_value env d z hz hd, Nat.cast_add]

/-- Evaluated shape of a `−1`-guarded limb vector. -/
lemma map_eval_denSafe_neg (env : Environment (F circomPrime))
    (d : Var Emu (F circomPrime)) (z : Expression (F circomPrime))
    (hz : Expression.eval env z = -1) :
    Vector.map (Expression.eval env) (DivOrZeroS32.denSafeVec d z)
      = Vector.ofFn fun k : Fin numLimbs =>
          (Vector.map (Expression.eval env) d)[k.val]'k.isLt
            + (if k.val = 0 then (-1 : F circomPrime) else 0) := by
  rw [map_eval_denSafe]
  simp only [hz]

/-- Limbwise value of a `−1`-guarded limb vector: only limb 0 moves, by one. -/
lemma limb_flag_val_neg {v : Emu (F circomPrime)}
    (h0 : 1 ≤ (v[0]'(by decide : (0:ℕ) < numLimbs)).val)
    (i : ℕ) (hi : i < numLimbs) :
    ((Vector.ofFn fun k : Fin numLimbs =>
        v[k.val]'k.isLt + (if k.val = 0 then (-1 : F circomPrime) else 0))[i]'hi).val
        + (if i = 0 then 1 else 0)
      = (v[i]'hi).val := by
  simp only [Vector.getElem_ofFn]
  by_cases hzi : i = 0
  · subst hzi
    have h0' : 1 ≤ (v[0]'hi).val := h0
    simp only [reduceIte]
    have hs : v[0]'hi + (-1 : F circomPrime) = v[0]'hi - 1 := by ring
    have h1 : (1 : F circomPrime).val ≤ (v[0]'hi).val := by rw [ZMod.val_one]; exact h0'
    rw [hs, ZMod.val_sub h1, ZMod.val_one]
    omega
  · simp only [if_neg hzi, add_zero, Nat.add_zero]

set_option maxRecDepth 4000 in
/-- Value of a `−1`-guarded limb vector. -/
lemma value_flag_neg {v : Emu (F circomPrime)}
    (h0 : 1 ≤ (v[0]'(by decide : (0:ℕ) < numLimbs)).val) :
    BigInt.value limbBits (Vector.ofFn fun k : Fin numLimbs =>
        v[k.val]'k.isLt + (if k.val = 0 then (-1 : F circomPrime) else 0)) + 1
      = BigInt.value limbBits v := by
  rw [BigInt.value_eq_sum, BigInt.value_eq_sum, Fin.sum_univ_four, Fin.sum_univ_four]
  have e0 := limb_flag_val_neg h0 0 (by decide)
  norm_num at e0 ⊢
  omega

/-- The natural-number cast of `2p − 1`. -/
lemma cast_twoP_sub_one : ((2 * P256 - 1 : ℕ) : Specs.Secp256k1.Fp) = -1 := by
  have h1 : (1 : ℕ) ≤ 2 * P256 := by have := P256_pos; omega
  rw [Nat.cast_sub h1]
  push_cast
  rw [ZMod.natCast_self]
  ring

/-- Everything the stage-2 divider needs from the tangent-guarded denominator,
where the guard is `−t` for a boolean `t`. -/
lemma den2_guard_facts (env : Environment (F circomPrime))
    (d : Var Emu (F circomPrime)) (z : Expression (F circomPrime))
    (t : F circomPrime) (ht : Expression.eval env z = -t) (htb : IsBool t)
    (hd0 : 1 ≤ ((Vector.map (Expression.eval env) d)[0]'(by decide : (0:ℕ) < numLimbs)).val)
    (hdl : ∀ i : Fin numLimbs,
      ((Vector.map (Expression.eval env) d)[i.val]'i.isLt).val < 3 * 2 ^ limbBits - 1)
    (hv0 : t = 0 → BigInt.value limbBits (Vector.map (Expression.eval env) d) < 3 * P256)
    (hv1 : t = 1 → BigInt.value limbBits (Vector.map (Expression.eval env) d) = 2 * P256)
    (hnz : t = 0 → BigInt.value limbBits (Vector.map (Expression.eval env) d) % P256 ≠ 0) :
    (∀ i : Fin numLimbs,
      ((Vector.map (Expression.eval env) (DivOrZeroS32.denSafeVec d z))[i.val]'i.isLt).val
        < 3 * 2 ^ limbBits)
    ∧ BigInt.value limbBits (Vector.map (Expression.eval env) (DivOrZeroS32.denSafeVec d z))
        < 3 * P256
    ∧ BigInt.value limbBits (Vector.map (Expression.eval env) (DivOrZeroS32.denSafeVec d z))
        % P256 ≠ 0
    ∧ decodeFe (Vector.map (Expression.eval env) (DivOrZeroS32.denSafeVec d z))
        = (if t = 1 then -1 else decodeFe (Vector.map (Expression.eval env) d)) := by
  have hP1 : (1 : ℕ) < P256 := by decide
  rcases htb with h0 | h1
  · subst h0
    have hz0 : Expression.eval env z = 0 := by rw [ht]; ring
    have hzb : IsBool (Expression.eval env z) := Or.inl hz0
    refine ⟨fun i => denSafe_limb_lt env d z hzb i.val i.isLt (hdl i), ?_, ?_, ?_⟩
    · rw [denSafe_value env d z hzb hdl, hz0, ZMod.val_zero, Nat.add_zero]
      exact hv0 rfl
    · rw [denSafe_value env d z hzb hdl, hz0, ZMod.val_zero, Nat.add_zero]
      exact hnz rfl
    · rw [denSafe_decodeFe env d z hzb hdl, hz0, ZMod.val_zero, Nat.cast_zero, add_zero,
        if_neg zero_ne_one]
  · subst h1
    have hzn : Expression.eval env z = -1 := ht
    have hmap := map_eval_denSafe_neg env d z hzn
    have hval := value_flag_neg (v := Vector.map (Expression.eval env) d) hd0
    have hdv : BigInt.value limbBits (Vector.map (Expression.eval env) d) = 2 * P256 := hv1 rfl
    have hgv : BigInt.value limbBits (Vector.map (Expression.eval env)
        (DivOrZeroS32.denSafeVec d z)) = 2 * P256 - 1 := by
      rw [hmap]; omega
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      rw [hmap]
      have hli := limb_flag_val_neg (v := Vector.map (Expression.eval env) d) hd0 i.val i.isLt
      have hb := hdl i
      omega
    · rw [hgv]; omega
    · rw [hgv, show 2 * P256 - 1 = P256 + (P256 - 1) from by omega,
        Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
      omega
    · rw [if_pos rfl]
      show ((BigInt.value limbBits (Vector.map (Expression.eval env)
        (DivOrZeroS32.denSafeVec d z)) : ℕ) : Specs.Secp256k1.Fp) = -1
      rw [hgv]
      exact cast_twoP_sub_one

/-- Two canonical limb vectors with equal decoded value have equal integer value. -/
lemma value_eq_of_decodeFe_eq {a b : Emu (F circomPrime)} (ha : Fe.Valid a) (hb : Fe.Valid b)
    (h : decodeFe a = decodeFe b) :
    BigInt.value limbBits a = BigInt.value limbBits b := by
  have hv := congrArg ZMod.val h
  simpa only [decodeFe, ZMod.val_natCast_of_lt ha.2, ZMod.val_natCast_of_lt hb.2] using hv

def main (input : Var Inputs (F circomPrime)) :
    Circuit (F circomPrime) (Var Output (F circomPrime)) := do
  let rx := input.rx
  let ry := input.ry
  let tIsInf := input.tIsInf
  let xS := input.xS
  let lam32 := input.lam32

  -- effective S.x: `T = 𝒪` re-routes stage 2 into the tangent branch
  let xSe ← subcircuit (Mux.circuit (M := Emu))
    { selector := tIsInf, ifTrue := rx, ifFalse := xS }

  let sameX2 ← subcircuit EqFe.circuit { a := xSe, b := rx }
  -- Since `tIsInf = 1` routes `xSe := rx`, it implies `sameX2 = 1`.
  -- Hence the boolean OR formerly assigned here is exactly `sameX2`.
  let tsel := sameX2

  let tDen : Var Emu (F circomPrime) := Vector.ofFn fun k : Fin numLimbs =>
    ry[k.val]'k.isLt + ry[k.val]'k.isLt
  let den2U : Var Emu (F circomPrime) := Vector.ofFn fun k : Fin numLimbs =>
    xSe[k.val]'k.isLt
      + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
        - rx[k.val]'k.isLt)
  -- The stage-2 denominator only ever has to be *non-zero mod p*: nothing reads
  -- its exact value.  So instead of a four-cell `Mux` against `2·ry` we fold the
  -- tangent selector into limb 0 as a free affine addend.  The borrow form
  -- `den2U` has integer value `xSe + 2p − rx`, which is `≡ 0 (mod p)` exactly
  -- when `xSe = rx`, i.e. exactly when `tsel = 1` — and there the guarded value
  -- is `2p + 1 ≡ 1`, so the divider's alias premise is never satisfiable.
  let den2 : Var Emu (F circomPrime) := DivOrZeroS32.denSafeVec den2U (-tsel)
  -- On the `T = 𝒪` branch the numerator is zero, so `w = 0`: stage 1 already
  -- carries the tangent slope there (its selector is `sameX1 ∨ tIsInf`), and
  -- the stage-2 multiplier becomes the *unconditional* sum `λ₁ + w`, a free
  -- affine recombination instead of an eight-cell mux.  Since the numerator is
  -- no longer a conditional square, the divider needs neither a convolution
  -- nor a `2m−1`-cell target mux.
  let twoLam1 : Var Emu (F circomPrime) := Vector.ofFn fun k : Fin numLimbs =>
    input.lam1[k.val]'k.isLt + input.lam1[k.val]'k.isLt
  let num2 ← subcircuit (Mux.circuit (M := Emu))
    { selector := tIsInf, ifTrue := twoLam1, ifFalse := tDen }
  let w32 ← subcircuit DivOrZeroN32.circuit { num := num2, den := den2 }
  let w : Var Emu (F circomPrime) := Limbs32.emuOf32 w32

  let mulA32 : Var (BigInt 8) (F circomPrime) := Vector.ofFn fun k : Fin 8 =>
    lam32[k.val]'k.isLt + w32[k.val]'k.isLt
  let mulA : Var Emu (F circomPrime) := Limbs32.emuOf32 mulA32

  return { xSe := xSe, sameX2 := sameX2, tsel := tsel, w := w, mulA := mulA, mulA32 := mulA32 }

instance elaborated : ElaboratedCircuit (F circomPrime) Inputs Output main := by
  elaborate_circuit

def Assumptions (input : Inputs (F circomPrime)) : Prop :=
  Fe.Valid input.rx ∧ Fe.Valid input.ry ∧ IsBool input.tIsInf ∧
    BigInt.Normalized limbBits input.lam1 ∧ Fe.Valid input.xS ∧
    BigInt.Normalized 32 input.lam32 ∧ input.lam1 = Limbs32.emuOf32V input.lam32

def Spec (input : Inputs (F circomPrime)) (out : Output (F circomPrime)) : Prop :=
  Fe.Valid out.xSe ∧
  decodeFe out.xSe =
    (if input.tIsInf = 1 then decodeFe input.rx else decodeFe input.xS) ∧
  out.sameX2 = (if decodeFe out.xSe = decodeFe input.rx then 1 else 0) ∧
  out.tsel = input.tIsInf + out.sameX2 - input.tIsInf * out.sameX2 ∧
  BigInt.Normalized limbBits out.w ∧
  ((if out.tsel = 1 then -1
      else decodeFe out.xSe - decodeFe input.rx) ≠ 0 →
    decodeFe out.w *
      (if out.tsel = 1 then -1
        else decodeFe out.xSe - decodeFe input.rx) =
      (if input.tIsInf = 1 then decodeFe input.lam1 + decodeFe input.lam1
        else decodeFe input.ry + decodeFe input.ry)) ∧
  Fe.NormW2 out.mulA ∧
  decodeFe out.mulA = decodeFe input.lam1 + decodeFe out.w ∧
  Norm33 out.mulA32 ∧
  out.mulA = Limbs32.emuOf32V out.mulA32

set_option maxHeartbeats 3200000 in
theorem soundness : Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [EqFe.circuit, EqFe.Assumptions, EqFe.Spec,
    Mux.circuit, Mux.Assumptions, Mux.Spec,
    DivOrZeroN32.circuit, DivOrZeroN32.Assumptions, DivOrZeroN32.Spec,
    AddMod.circuit, AddMod.Assumptions, AddMod.Spec, secpParams]
  obtain ⟨hxSe, hsameX2, hnum, hw⟩ := h_holds
  obtain ⟨hRx, hRy, htib, hlam1v, hxSv, hlam32v, hlam1eq⟩ := h_assumptions
  obtain ⟨hIRx, hIRy, hITi, hIlam1, hIxS, hIlam32⟩ := h_input
  -- xSe mux
  have hxSeb := hxSe htib
  have hxSev := fe_valid_of_eq_ite hRx hxSv hxSeb
  -- sameX2 flag
  have hsameX2' := EqFe.flag_eq_decode_eq hxSev hRx hsameX2
  have hsx2b : IsBool _ := isBool_of_eq_ite hsameX2'
  have htselS : env.get (i₀ + numLimbs + 2)
      = input_tIsInf + env.get (i₀ + numLimbs + 2)
        - input_tIsInf * env.get (i₀ + numLimbs + 2) := by
    rcases htib with hti0 | hti1
    · rw [hti0]; ring
    · have hxSeEq : decodeFe
          (Vector.map (Expression.eval env)
            (Vector.mapRange numLimbs fun i => var { index := i₀ + i })) =
          decodeFe input_rx := by rw [hxSeb, if_pos hti1]
      rw [hsameX2', if_pos hxSeEq, hti1]
      ring
  have htselb := hsx2b
  -- the borrow form of the stage-2 denominator, before the tangent guard
  have hconv : (Vector.ofFn fun k : Fin numLimbs =>
        (var { index := i₀ + k.val } : Expression (F circomPrime))
        + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
          - input_var_rx[k.val]'k.isLt))
      = (Vector.ofFn fun k : Fin numLimbs =>
        (Vector.mapRange numLimbs fun j =>
          var (F := F circomPrime) { index := i₀ + j })[k.val]'k.isLt
        + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
          - input_var_rx[k.val]'k.isLt)) := rfl
  have hden2Ue : decodeFe (Vector.map (Expression.eval env)
        (Vector.ofFn fun k : Fin numLimbs =>
          (var { index := i₀ + k.val } : Expression (F circomPrime))
          + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
            - input_var_rx[k.val]'k.isLt)))
      = decodeFe (Vector.map (Expression.eval env)
          (Vector.mapRange numLimbs fun j => var { index := i₀ + j }))
        - decodeFe input_rx := by
    rw [hconv, map_eval_borrow, hIRx]
    exact decodeFe_borrow _ input_rx hxSev.1 hRx
  have hvalU : BigInt.value limbBits (Vector.map (Expression.eval env)
        (Vector.ofFn fun k : Fin numLimbs =>
          (var { index := i₀ + k.val } : Expression (F circomPrime))
          + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
            - input_var_rx[k.val]'k.isLt)))
      = BigInt.value limbBits (Vector.map (Expression.eval env)
          (Vector.mapRange numLimbs fun j => var { index := i₀ + j }))
        + 2 * P256 - BigInt.value limbBits input_rx := by
    rw [hconv, map_eval_borrow, hIRx]
    exact value_borrow _ input_rx hxSev.1 hRx.1
  have hdlimbs : ∀ i : Fin numLimbs,
      ((Vector.map (Expression.eval env)
        (Vector.ofFn fun k : Fin numLimbs =>
          (var { index := i₀ + k.val } : Expression (F circomPrime))
          + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
            - input_var_rx[k.val]'k.isLt)))[i.val]'i.isLt).val < 3 * 2 ^ limbBits - 1 := by
    intro i
    have hxl := hxSev.1 i
    simp only [Fin.getElem_fin, Vector.getElem_map, Vector.getElem_mapRange] at hxl
    simp only [Vector.getElem_map, Vector.getElem_ofFn]
    have hpq := congrArg (fun v : Emu (F circomPrime) => v[i.val]'i.isLt) hIRx
    simp only [Vector.getElem_map] at hpq
    simp only [circuit_norm, hpq]
    have hlb := limb_borrow_lt' i.val hxl (hRx.1 i)
    rw [sub_eq_add_neg] at hlb
    exact hlb
  have htselE : Expression.eval env (var (F := F circomPrime) { index := i₀ + numLimbs + 1 + 1 })
      = env.get (i₀ + numLimbs + 2) := by
    rw [show i₀ + numLimbs + 1 + 1 = i₀ + numLimbs + 2 from by omega]
    rfl
  have hsx2bE : IsBool (Expression.eval env (var (F := F circomPrime)
      { index := i₀ + numLimbs + 1 + 1 })) := by
    rw [htselE]; exact hsx2b
  have htsel1 : env.get (i₀ + numLimbs + 2) = 1 →
      BigInt.value limbBits (Vector.map (Expression.eval env)
        (Vector.mapRange numLimbs fun j => var { index := i₀ + j }))
        = BigInt.value limbBits input_rx := by
    intro h1
    by_cases hc : decodeFe (Vector.map (Expression.eval env)
        (Vector.mapRange numLimbs fun j => var { index := i₀ + j })) = decodeFe input_rx
    · exact value_eq_of_decodeFe_eq hxSev hRx hc
    · rw [hsameX2', if_neg hc] at h1
      exact absurd h1 zero_ne_one
  have hP1 : (1 : ℕ) < P256 := by decide
  have hnegE : Expression.eval env
      (-(var (F := F circomPrime) { index := i₀ + numLimbs + 1 + 1 }))
      = -(env.get (i₀ + numLimbs + 2)) := by
    rw [show i₀ + numLimbs + 1 + 1 = i₀ + numLimbs + 2 from by omega]
    show (-1 : F circomPrime) * env.get (i₀ + numLimbs + 2) = _
    ring
  have hd0 : 1 ≤ ((Vector.map (Expression.eval env)
        (Vector.ofFn fun k : Fin numLimbs =>
          (var { index := i₀ + k.val } : Expression (F circomPrime))
          + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
            - input_var_rx[k.val]'k.isLt)))[0]'(by decide : (0:ℕ) < numLimbs)).val := by
    have hxl : (env.get i₀).val < 2 ^ limbBits := by
      simpa [circuit_norm] using hxSev.1 (0 : Fin numLimbs)
    have hr : (input_rx[0]'(by decide : (0:ℕ) < numLimbs)).val < 2 ^ limbBits := by
      simpa using hRx.1 (0 : Fin numLimbs)
    simp only [Vector.getElem_map, Vector.getElem_ofFn]
    have hpq := congrArg
      (fun v : Emu (F circomPrime) => v[0]'(by decide : (0:ℕ) < numLimbs)) hIRx
    simp only [Vector.getElem_map] at hpq
    simp only [circuit_norm, hpq]
    rw [← sub_eq_add_neg, limb_borrow_val 0 hxl hr]
    have hge := twoPBorrowDigit_ge 0
    omega
  obtain ⟨hglimb, hvbound, hnalias, hdendU⟩ :=
    den2_guard_facts env _
      (-(var (F := F circomPrime) { index := i₀ + numLimbs + 1 + 1 }))
      (env.get (i₀ + numLimbs + 2)) hnegE hsx2b hd0 hdlimbs
      (fun _ => by
        rw [hvalU]
        have hx := hxSev.2
        have hr := hRx.2
        omega)
      (fun h1 => by
        rw [hvalU, htsel1 h1]
        omega)
      (fun h0 => by
        intro hmod
        have hz0 : decodeFe (Vector.map (Expression.eval env)
              (Vector.ofFn fun k : Fin numLimbs =>
                (var { index := i₀ + k.val } : Expression (F circomPrime))
                + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
                  - input_var_rx[k.val]'k.isLt))) = 0 := by
          have hcast := (ZMod.natCast_eq_zero_iff (BigInt.value limbBits
            (Vector.map (Expression.eval env)
              (Vector.ofFn fun k : Fin numLimbs =>
                (var { index := i₀ + k.val } : Expression (F circomPrime))
                + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
                  - input_var_rx[k.val]'k.isLt)))) P256).mpr (Nat.dvd_of_mod_eq_zero hmod)
          simpa only [decodeFe] using hcast
        rw [hden2Ue] at hz0
        rw [hsameX2', if_pos (sub_eq_zero.mp hz0)] at h0
        exact one_ne_zero h0)
  have hdend := hdendU
  rw [hden2Ue] at hdend
  -- numerator mux: `2·λ₁` on the `T = 𝒪` branch, `2·ry` otherwise
  have hnumb := hnum htib
  rw [map_eval_sum2_input env _ input_lam1 hIlam1,
    map_eval_sum2_input env _ input_ry hIRy] at hnumb
  -- discharge divider assumptions
  obtain ⟨hwv, hwe⟩ := hw (by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro i
      have hcellnum : (Vector.map (Expression.eval env)
            (Vector.mapRange numLimbs fun j =>
              var (F := F circomPrime)
                { index := i₀ + numLimbs + 3 + j }))[i.val]'i.isLt
          = env.get (i₀ + numLimbs + 3 + i.val) := by
        rw [Vector.getElem_map, Vector.getElem_mapRange]; rfl
      rw [← hcellnum, hnumb]
      split
      · have hb := limb_sum2_bound input_lam1 hlam1v i
        simp only [Vector.getElem_ofFn] at hb ⊢
        exact lt_trans hb (by norm_num [limbBits])
      · have hb := limb_sum2_bound input_ry hRy.1 i
        simp only [Vector.getElem_ofFn] at hb ⊢
        exact lt_trans hb (by norm_num [limbBits])
    · rw [hnumb]
      split
      · rw [value_sum2 input_lam1 hlam1v]
        have h := BigInt.value_lt hlam1v
        have : (2:ℕ) ^ (limbBits * numLimbs) + 2 ^ (limbBits * numLimbs) < 3 * P256 := by decide
        omega
      · exact lt_trans (value_sum2_bound input_ry hRy) (by have := P256_pos; omega)
    · intro i
      have hdl := hglimb i
      rwa [Vector.getElem_map] at hdl
    · exact hvbound
    · exact hnalias)
  -- the stage-2 multiplier is the unreduced limbwise sum λ₁ + w in the 32-bit view
  have hconvA : ∀ off : ℕ, (Vector.ofFn fun k : Fin 8 =>
        input_var_lam32[k.val]'k.isLt
          + (var (F := F circomPrime) { index := off + k.val } : Expression (F circomPrime)))
      = (Vector.ofFn fun k : Fin 8 => input_var_lam32[k.val]'k.isLt
          + (Vector.mapRange 8 fun j =>
              var (F := F circomPrime) { index := off + j })[k.val]'k.isLt) := fun _ => rfl
  have hmulAb : Vector.map (Expression.eval env)
      (Vector.ofFn fun k : Fin 8 => input_var_lam32[k.val]'k.isLt
        + (var (F := F circomPrime)
            { index := i₀ + numLimbs + 3 + numLimbs + k.val } : Expression (F circomPrime)))
      = Vector.ofFn fun k : Fin 8 => input_lam32[k.val]'k.isLt
          + (Vector.map (Expression.eval env)
              (Vector.mapRange 8 fun j => var (F := F circomPrime)
                { index := i₀ + numLimbs + 3 + numLimbs + j }))[k.val]'k.isLt := by
    rw [hconvA, map_eval_sum8, hIlam32]
  have hA32 : Norm33 _ := norm33_of_eq hmulAb (norm33_sum hlam32v hwv)
  simp only [Limbs32.eval_emuOf32]
  refine ⟨hxSev, ?_, hsameX2', htselS, Limbs32.normalized_emuOf32 hwv, ?_,
    normW2_emuOf32V hA32, ?_, hA32, by first | rfl | trivial⟩
  · rw [hxSeb, apply_ite decodeFe]
  · intro hne
    rw [← hdend] at hne
    have h := hwe hne
    rw [hdend] at h
    rw [h, hnumb, apply_ite decodeFe]
    split
    · exact decodeFe_sum2 input_lam1 hlam1v
    · exact decodeFe_sum2 input_ry hRy.1
  · rw [hmulAb, decodeFe_emuOf32V_sum hlam32v hwv, hlam1eq]

theorem completeness : Completeness (F circomPrime) main Assumptions := by
  circuit_proof_start [EqFe.circuit, EqFe.Assumptions, EqFe.Spec,
    Mux.circuit, Mux.Assumptions, Mux.Spec,
    DivOrZeroN32.circuit, DivOrZeroN32.Assumptions, DivOrZeroN32.Spec,
    AddMod.circuit, AddMod.Assumptions, AddMod.Spec, secpParams]
  obtain ⟨hxSe, hsameX2, hnum, hw⟩ := h_env
  obtain ⟨hRx, hRy, htib, hlam1v, hxSv, hlam32v, hlam1eq⟩ := h_assumptions
  obtain ⟨hIRx, hIRy, hITi, hIlam1, hIxS, hIlam32⟩ := h_input
  -- xSe mux
  have hxSeb := hxSe htib
  have hxSev := fe_valid_of_eq_ite hRx hxSv hxSeb
  -- sameX2 flag
  have hsameX2' := EqFe.flag_eq_decode_eq hxSev hRx hsameX2
  have hsx2b : IsBool _ := isBool_of_eq_ite hsameX2'
  have htselS : env.get (i₀ + numLimbs + 2)
      = input_tIsInf + env.get (i₀ + numLimbs + 2)
        - input_tIsInf * env.get (i₀ + numLimbs + 2) := by
    rcases htib with hti0 | hti1
    · rw [hti0]; ring
    · have hxSeEq : decodeFe
          (Vector.map (Expression.eval env.toEnvironment)
            (Vector.mapRange numLimbs fun i => var { index := i₀ + i })) =
          decodeFe input_rx := by rw [hxSeb, if_pos hti1]
      rw [hsameX2', if_pos hxSeEq, hti1]
      ring
  have htselb := hsx2b
  -- the borrow form of the stage-2 denominator, before the tangent guard
  have hconv : (Vector.ofFn fun k : Fin numLimbs =>
        (var { index := i₀ + k.val } : Expression (F circomPrime))
        + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
          - input_var_rx[k.val]'k.isLt))
      = (Vector.ofFn fun k : Fin numLimbs =>
        (Vector.mapRange numLimbs fun j =>
          var (F := F circomPrime) { index := i₀ + j })[k.val]'k.isLt
        + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
          - input_var_rx[k.val]'k.isLt)) := rfl
  have hden2Ue : decodeFe (Vector.map (Expression.eval env.toEnvironment)
        (Vector.ofFn fun k : Fin numLimbs =>
          (var { index := i₀ + k.val } : Expression (F circomPrime))
          + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
            - input_var_rx[k.val]'k.isLt)))
      = decodeFe (Vector.map (Expression.eval env.toEnvironment)
          (Vector.mapRange numLimbs fun j => var { index := i₀ + j }))
        - decodeFe input_rx := by
    rw [hconv, map_eval_borrow, hIRx]
    exact decodeFe_borrow _ input_rx hxSev.1 hRx
  have hvalU : BigInt.value limbBits (Vector.map (Expression.eval env.toEnvironment)
        (Vector.ofFn fun k : Fin numLimbs =>
          (var { index := i₀ + k.val } : Expression (F circomPrime))
          + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
            - input_var_rx[k.val]'k.isLt)))
      = BigInt.value limbBits (Vector.map (Expression.eval env.toEnvironment)
          (Vector.mapRange numLimbs fun j => var { index := i₀ + j }))
        + 2 * P256 - BigInt.value limbBits input_rx := by
    rw [hconv, map_eval_borrow, hIRx]
    exact value_borrow _ input_rx hxSev.1 hRx.1
  have hdlimbs : ∀ i : Fin numLimbs,
      ((Vector.map (Expression.eval env.toEnvironment)
        (Vector.ofFn fun k : Fin numLimbs =>
          (var { index := i₀ + k.val } : Expression (F circomPrime))
          + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
            - input_var_rx[k.val]'k.isLt)))[i.val]'i.isLt).val < 3 * 2 ^ limbBits - 1 := by
    intro i
    have hxl := hxSev.1 i
    simp only [Fin.getElem_fin, Vector.getElem_map, Vector.getElem_mapRange] at hxl
    simp only [Vector.getElem_map, Vector.getElem_ofFn]
    have hpq := congrArg (fun v : Emu (F circomPrime) => v[i.val]'i.isLt) hIRx
    simp only [Vector.getElem_map] at hpq
    simp only [circuit_norm, hpq]
    have hlb := limb_borrow_lt' i.val hxl (hRx.1 i)
    rw [sub_eq_add_neg] at hlb
    exact hlb
  have htselE : Expression.eval env.toEnvironment (var (F := F circomPrime) { index := i₀ + numLimbs + 1 + 1 })
      = env.get (i₀ + numLimbs + 2) := by
    rw [show i₀ + numLimbs + 1 + 1 = i₀ + numLimbs + 2 from by omega]
    rfl
  have hsx2bE : IsBool (Expression.eval env.toEnvironment (var (F := F circomPrime)
      { index := i₀ + numLimbs + 1 + 1 })) := by
    rw [htselE]; exact hsx2b
  have htsel1 : env.get (i₀ + numLimbs + 2) = 1 →
      BigInt.value limbBits (Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange numLimbs fun j => var { index := i₀ + j }))
        = BigInt.value limbBits input_rx := by
    intro h1
    by_cases hc : decodeFe (Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange numLimbs fun j => var { index := i₀ + j })) = decodeFe input_rx
    · exact value_eq_of_decodeFe_eq hxSev hRx hc
    · rw [hsameX2', if_neg hc] at h1
      exact absurd h1 zero_ne_one
  have hP1 : (1 : ℕ) < P256 := by decide
  have hnegE : Expression.eval env.toEnvironment
      (-(var (F := F circomPrime) { index := i₀ + numLimbs + 1 + 1 }))
      = -(env.get (i₀ + numLimbs + 2)) := by
    rw [show i₀ + numLimbs + 1 + 1 = i₀ + numLimbs + 2 from by omega]
    show (-1 : F circomPrime) * env.get (i₀ + numLimbs + 2) = _
    ring
  have hd0 : 1 ≤ ((Vector.map (Expression.eval env.toEnvironment)
        (Vector.ofFn fun k : Fin numLimbs =>
          (var { index := i₀ + k.val } : Expression (F circomPrime))
          + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
            - input_var_rx[k.val]'k.isLt)))[0]'(by decide : (0:ℕ) < numLimbs)).val := by
    have hxl : (env.get i₀).val < 2 ^ limbBits := by
      simpa [circuit_norm] using hxSev.1 (0 : Fin numLimbs)
    have hr : (input_rx[0]'(by decide : (0:ℕ) < numLimbs)).val < 2 ^ limbBits := by
      simpa using hRx.1 (0 : Fin numLimbs)
    simp only [Vector.getElem_map, Vector.getElem_ofFn]
    have hpq := congrArg
      (fun v : Emu (F circomPrime) => v[0]'(by decide : (0:ℕ) < numLimbs)) hIRx
    simp only [Vector.getElem_map] at hpq
    simp only [circuit_norm, hpq]
    rw [← sub_eq_add_neg, limb_borrow_val 0 hxl hr]
    have hge := twoPBorrowDigit_ge 0
    omega
  obtain ⟨hglimb, hvbound, hnalias, hdendU⟩ :=
    den2_guard_facts env.toEnvironment _
      (-(var (F := F circomPrime) { index := i₀ + numLimbs + 1 + 1 }))
      (env.get (i₀ + numLimbs + 2)) hnegE hsx2b hd0 hdlimbs
      (fun _ => by
        rw [hvalU]
        have hx := hxSev.2
        have hr := hRx.2
        omega)
      (fun h1 => by
        rw [hvalU, htsel1 h1]
        omega)
      (fun h0 => by
        intro hmod
        have hz0 : decodeFe (Vector.map (Expression.eval env.toEnvironment)
              (Vector.ofFn fun k : Fin numLimbs =>
                (var { index := i₀ + k.val } : Expression (F circomPrime))
                + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
                  - input_var_rx[k.val]'k.isLt))) = 0 := by
          have hcast := (ZMod.natCast_eq_zero_iff (BigInt.value limbBits
            (Vector.map (Expression.eval env.toEnvironment)
              (Vector.ofFn fun k : Fin numLimbs =>
                (var { index := i₀ + k.val } : Expression (F circomPrime))
                + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
                  - input_var_rx[k.val]'k.isLt)))) P256).mpr (Nat.dvd_of_mod_eq_zero hmod)
          simpa only [decodeFe] using hcast
        rw [hden2Ue] at hz0
        rw [hsameX2', if_pos (sub_eq_zero.mp hz0)] at h0
        exact one_ne_zero h0)
  -- numerator mux: `2·λ₁` on the `T = 𝒪` branch, `2·ry` otherwise
  have hnumb := hnum htib
  rw [map_eval_sum2_input env.toEnvironment _ input_lam1 hIlam1,
    map_eval_sum2_input env.toEnvironment _ input_ry hIRy] at hnumb
  refine ⟨htib, htib, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · intro i
    have hcellnum : (Vector.map (Expression.eval env.toEnvironment)
          (Vector.mapRange numLimbs fun j =>
            var (F := F circomPrime)
              { index := i₀ + numLimbs + 3 + j }))[i.val]'i.isLt
        = env.get (i₀ + numLimbs + 3 + i.val) := by
      rw [Vector.getElem_map, Vector.getElem_mapRange]; rfl
    rw [← hcellnum, hnumb]
    split
    · have hb := limb_sum2_bound input_lam1 hlam1v i
      simp only [Vector.getElem_ofFn] at hb ⊢
      exact lt_trans hb (by norm_num [limbBits])
    · have hb := limb_sum2_bound input_ry hRy.1 i
      simp only [Vector.getElem_ofFn] at hb ⊢
      exact lt_trans hb (by norm_num [limbBits])
  · rw [hnumb]
    split
    · rw [value_sum2 input_lam1 hlam1v]
      have h := BigInt.value_lt hlam1v
      have : (2:ℕ) ^ (limbBits * numLimbs) + 2 ^ (limbBits * numLimbs) < 3 * P256 := by decide
      omega
    · exact lt_trans (value_sum2_bound input_ry hRy) (by have := P256_pos; omega)
  · intro i
    have hdl := hglimb i
    rwa [Vector.getElem_map] at hdl
  · exact hvbound
  · exact hnalias


def circuit : FormalCircuit (F circomPrime) Inputs Output where
  main; elaborated; Assumptions; Spec; soundness; completeness

end Slope2
end Solution.Secp256k1ScalarMul
