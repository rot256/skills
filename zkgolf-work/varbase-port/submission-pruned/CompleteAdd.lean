import Solution.Secp256k1ScalarMul.AddMod
import Solution.Secp256k1ScalarMul.SubMod
import Solution.Secp256k1ScalarMul.IsZeroFe
import Solution.Secp256k1ScalarMul.Mux
import Solution.Secp256k1ScalarMul.DivOrZeroTheorems
import Solution.Secp256k1ScalarMul.CompleteAddTheorems
import Solution.Secp256k1ScalarMul.EqFe
import Solution.Secp256k1ScalarMul.DivOrZeroF3
import Solution.Secp256k1ScalarMul.DivOrZeroS32
import Solution.Secp256k1ScalarMul.MulModSub2F32
import Solution.Secp256k1ScalarMul.MulMod
import Solution.Secp256k1ScalarMul.MulModFold
import Solution.Secp256k1ScalarMul.Params
import Solution.Secp256k1ScalarMul.MulModSub2W32N
import Solution.Secp256k1ScalarMul.CancelLow
import Solution.Secp256k1ScalarMul.CancelTheorems
import Solution.Secp256k1ScalarMul.ValidP
import Solution.Secp256k1ScalarMul.OrderFactsCerts
import Challenge.Utils.ComputableWitnessLemmas

namespace Solution.Secp256k1ScalarMul

namespace MulModSub2

end MulModSub2

namespace MulModSub2D3

/-- Inputs of `MulModSub2D3`: factor `a` and subtrahends canonical; factor
`b` unreduced (limbs `< 3·2^64`, value `< 3p`). -/
structure Inputs (F : Type) where
  a : Emu F
  b : Emu F
  s1 : Emu F
  s2 : Emu F
deriving ProvableStruct

/-- Preconditions: all four operands are canonical emulated field elements. -/
def Assumptions (input : Inputs (F circomPrime)) : Prop :=
  BigInt.Normalized limbBits input.a ∧
    (∀ i : Fin numLimbs, (input.b[i.val]).val < 3 * 2 ^ limbBits) ∧
    BigInt.value limbBits input.b < 3 * P256 ∧
    Fe.Valid input.s1 ∧ Fe.Valid input.s2

end MulModSub2D3

namespace CompleteAdd

structure Inputs (F : Type) where
  P : FlaggedPoint F
  Q : FlaggedPoint F
deriving ProvableStruct

def main (input : Var Inputs (F circomPrime)) :
    Circuit (F circomPrime) (Var FlaggedPoint (F circomPrime)) := do
  let { P, Q } := input

  -- case flags: sameX from the RAW limb differences Q.x − P.x (canonical
  -- coordinates are limbwise-equal iff value-equal, so no `SubMod`/reduction)
  let sameX ← subcircuit EqFe.circuit { a := Q.x, b := P.x }
  -- cancellation flag: both finite, same x, opposite y ⇒ 𝒪.  Two rows, via the
  -- low-limb inverse witness (`CancelTheorems.cancelLow_eq_mul`).
  let cancel ← subcircuit CancelLow.circuit { sameX := sameX, y1 := P.y, y2 := Q.y }

  -- chord numerator Q.y + (2p − P.y) via the borrow-free constants and the
  -- doubling denominator 2·P.y — both reduction-free, consumed by DivOrZeroF3
  let dyU : Var Emu (F circomPrime) := Vector.ofFn fun k : Fin numLimbs =>
    Q.y[k.val]'k.isLt
      + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
        - P.y[k.val]'k.isLt)
  -- chord denominator Q.x + (2p − P.x): raw borrow-free (value in (p,3p)), no SubMod
  let dxU : Var Emu (F circomPrime) := Vector.ofFn fun k : Fin numLimbs =>
    Q.x[k.val]'k.isLt
      + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
        - P.x[k.val]'k.isLt)
  let tDen : Var Emu (F circomPrime) := Vector.ofFn fun k : Fin numLimbs =>
    P.y[k.val]'k.isLt + P.y[k.val]'k.isLt

  -- slope denominator: tangent (raw `2y`) or chord (dxU), by sameX
  let den ← subcircuit (Mux.circuit (M := Emu))
    { selector := sameX, ifTrue := tDen, ifFalse := dxU }
  -- fused conditional slope: (3·P.x² or dyU) / den, giving 0 when den = 0.
  -- The slope is witnessed in eight 32-bit limbs, which costs exactly what four
  -- 64-bit limbs cost and lets the square below run its certificate in base 2^32.
  let lam32 ← subcircuit DivOrZeroS32.circuit { sel := sameX, x := P.x, dyU := dyU, den := den }

  -- affine result: x₃ = λ² − P.x − Q.x, y₃ = λ·(P.x − x₃) − P.y — each a single
  -- fused multiply-subtract via the offset target certificate
  let x3 ← subcircuit MulModSub2F32.circuit { a := lam32, b := lam32, s1 := P.x, s2 := Q.x }
  let xdU : Var Emu (F circomPrime) := Vector.ofFn fun k : Fin numLimbs =>
    P.x[k.val]'k.isLt
      + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
        - x3[k.val]'k.isLt)
  let y3 ← subcircuit MulModSub2W32N.circuit { a := lam32, b := xdU, s1 := P.y, s2 := zeroConst }

  -- Cancellation needs only an infinity flag: the coordinates remain the
  -- canonical affine-formula result and are ignored by `decodePoint` at
  -- infinity.  This removes a nine-cell point mux from every addition.
  -- `P` is statically finite at every call site (the table bases `r0`, `r1` and
  -- their sum `t3` are affine points), so the `P = 𝒪` mux is not built.
  -- Only the two coordinate lanes are muxed against `P`: on the `Q = 𝒪` branch
  -- `Q.x` is the canonical zero (an assumption discharged at every call site),
  -- while `P` is finite and secp256k1 has no affine point with `x = 0`, so
  -- `sameX = 0` and hence `cancel = 0 = P.isInf`.  The infinity lane of the
  -- point mux is therefore redundant and is not built.
  -- The `ifTrue` lane is the *raw limbwise difference* `P.x − Q.x`, and the
  -- selector is the (mutually exclusive, hence boolean) sum `Q.isInf + cancel`.
  -- On the `Q = 𝒪` branch `Q.x` is the canonical zero, so the lane is `P.x`,
  -- exactly as before; on the cancellation branch `sameX = 1` forces the two
  -- canonical x-limb vectors to be equal, so the lane is the zero vector and
  -- the output x-coordinate is canonically zero *for free* — which is what the
  -- table build used to buy with a separate nine-fold canonicalisation mux.
  let dxCanon : Var Emu (F circomPrime) := Vector.ofFn fun k : Fin numLimbs =>
    (P.x[k.val]'k.isLt) - (Q.x[k.val]'k.isLt)
  let outX ← subcircuit (Mux.circuit (M := Emu))
    { selector := Q.isInf + cancel, ifTrue := dxCanon, ifFalse := x3 }
  let outY ← subcircuit (Mux.circuit (M := Emu))
    { selector := Q.isInf, ifTrue := P.y, ifFalse := y3 }
  return { x := outX, y := outY, isInf := cancel }

instance elaborated : ElaboratedCircuit (F circomPrime) Inputs FlaggedPoint main := by
  elaborate_circuit

def Assumptions (input : Inputs (F circomPrime)) : Prop :=
  input.P.Valid ∧ input.Q.Valid ∧ input.P.isInf = 0 ∧
    (input.Q.isInf = 1 → decodeFe input.Q.x = 0)

def Spec (input : Inputs (F circomPrime)) (out : FlaggedPoint (F circomPrime)) : Prop :=
  out.Valid ∧
    decodePoint out =
      Specs.ShortWeierstrass.add Specs.Secp256k1.curve
        (decodePoint input.P) (decodePoint input.Q) ∧
    (out.isInf = 1 → decodeFe out.x = 0)

/-- Borrow-form evaluation against a raw witness block: the `x₃` wire unfolds
to `var` indices `off + k`, and the evaluated borrow vector is the pointwise
borrow of the evaluated block (the shape `decodeFe_borrow`/`value_borrow_lt`
are stated over). -/
lemma map_eval_borrow_vfo (env : Environment (F circomPrime))
    (qx : Emu (Expression (F circomPrime))) (off : ℕ) :
    Vector.map (Expression.eval env) (Vector.ofFn fun k : Fin numLimbs =>
        qx[k.val]'k.isLt
          + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
            - var { index := off + k.val }))
      = Vector.ofFn (fun k : Fin numLimbs =>
        (Vector.map (Expression.eval env) qx)[k.val]
          + (((twoPBorrowDigit k.val : ℕ) : F circomPrime)
            - (Vector.map (Expression.eval env)
                (Vector.mapRange numLimbs fun j => var { index := off + j }))[k.val]'k.isLt)) := by
  apply Vector.ext
  intro j hj
  simp [circuit_norm, Vector.getElem_map, Vector.getElem_ofFn, Vector.getElem_mapRange]
  ring

/-- Subtracting a canonically-zero limb vector is the identity. -/
lemma rawdiff_of_canon_zero {a b : Emu (F circomPrime)} (hb : Fe.Valid b)
    (h0 : decodeFe b = 0) :
    (Vector.ofFn fun k : Fin numLimbs => (a[k.val]'k.isLt) - (b[k.val]'k.isLt)) = a := by
  have hval : BigInt.value limbBits b = 0 := by
    have hv := congrArg ZMod.val h0
    simpa only [decodeFe, ZMod.val_natCast_of_lt hb.2, ZMod.val_zero] using hv
  have hz := (BigInt.value_eq_zero_iff (B := limbBits) b).mp hval
  apply Vector.ext
  intro j hj
  rw [Vector.getElem_ofFn]
  have hj' := hz ⟨j, hj⟩
  rw [Fin.getElem_fin] at hj'
  rw [hj', sub_zero]

/-- The raw limbwise difference of two canonical elements that decode equal is
canonically zero. -/
lemma rawdiff_decodeFe_zero {a b : Emu (F circomPrime)} (ha : Fe.Valid a) (hb : Fe.Valid b)
    (h : decodeFe a = decodeFe b) :
    decodeFe (Vector.ofFn fun k : Fin numLimbs => (a[k.val]'k.isLt) - (b[k.val]'k.isLt)) = 0 := by
  have hval := (rawdiff_value_zero_iff a b ha hb).mpr h
  rw [decodeFe, hval, Nat.cast_zero]

/-- The raw limbwise difference of two canonical elements that decode equal is
the zero vector, hence valid. -/
lemma rawdiff_valid_of_eq {a b : Emu (F circomPrime)} (ha : Fe.Valid a) (hb : Fe.Valid b)
    (h : decodeFe a = decodeFe b) :
    Fe.Valid (Vector.ofFn fun k : Fin numLimbs => (a[k.val]'k.isLt) - (b[k.val]'k.isLt)) := by
  have hval := (rawdiff_value_zero_iff a b ha hb).mpr h
  have hz := (BigInt.value_eq_zero_iff (B := limbBits)
    (Vector.ofFn fun k : Fin numLimbs => (a[k.val]'k.isLt) - (b[k.val]'k.isLt))).mp hval
  refine ⟨fun i => ?_, ?_⟩
  · have := hz i
    rw [Fin.getElem_fin] at this ⊢
    rw [this, ZMod.val_zero]
    exact Nat.two_pow_pos _
  · rw [hval]; exact P256_pos

/-- On the `Q = 𝒪` branch the cancellation flag is provably zero. -/
private lemma cancel_zero_of_Qinf {cancelv sameXv a b Qinf : F circomPrime}
    {u v : Specs.Secp256k1.Fp}
    (hcancelSpec : cancelv = if a = b then 0 else sameXv)
    (hsameXd : sameXv = if u = v then 1 else 0)
    (hne : Qinf = 1 → u ≠ v) : Qinf = 1 → cancelv = 0 := by
  intro h
  rw [hcancelSpec, hsameXd, if_neg (hne h)]
  split <;> rfl

private lemma sameX_one_of_cancel {cancelv sameXv a b : F circomPrime}
    (hcancelSpec : cancelv = if a = b then 0 else sameXv)
    (hc1 : cancelv = 1) : sameXv = 1 := by
  rw [hc1] at hcancelSpec
  split at hcancelSpec
  · exact absurd hcancelSpec one_ne_zero
  · exact hcancelSpec.symm

private lemma decode_eq_of_sameX {sameXv : F circomPrime} {u v : Specs.Secp256k1.Fp}
    (hsameXd : sameXv = if u = v then 1 else 0) (h1 : sameXv = 1) : u = v := by
  rw [h1] at hsameXd
  by_contra h
  rw [if_neg h] at hsameXd
  exact one_ne_zero hsameXd

private lemma isBool_add_excl {a b : F circomPrime} (ha : IsBool a) (hb : IsBool b)
    (hexcl : a = 1 → b = 0) : IsBool (a + b) := by
  rcases ha with h | h
  · rw [h, zero_add]; exact hb
  · rw [h, hexcl h, add_zero]; exact Or.inr rfl

/-- Validity and canonical-zero-on-cancellation for the raw-difference x-mux. -/
private lemma outX_valid_zero {Px Qx x3v outXv : Emu (F circomPrime)}
    {Qinf cancelv sameXv a b : F circomPrime}
    (hPx : Fe.Valid Px) (hQx : Fe.Valid Qx) (hx3v : Fe.Valid x3v)
    (hQb : IsBool Qinf) (hcb : IsBool cancelv)
    (hQcanon : Qinf = 1 → decodeFe Qx = 0)
    (hcancelSpec : cancelv = if a = b then 0 else sameXv)
    (hsameXd : sameXv = if decodeFe Qx = decodeFe Px then 1 else 0)
    (hexcl : Qinf = 1 → cancelv = 0)
    (hX : outXv = if Qinf + cancelv = 1 then
        (Vector.ofFn fun k : Fin numLimbs => (Px[k.val]'k.isLt) - (Qx[k.val]'k.isLt))
      else x3v) :
    Fe.Valid outXv ∧ (cancelv = 1 → decodeFe outXv = 0) := by
  have hxeq : cancelv = 1 → decodeFe Px = decodeFe Qx := fun hc1 =>
    (decode_eq_of_sameX hsameXd (sameX_one_of_cancel hcancelSpec hc1)).symm
  constructor
  · rcases hQb with hq0 | hq1
    · rcases hcb with hc0 | hc1
      · rw [hX, if_neg (by rw [hq0, hc0, add_zero]; exact zero_ne_one)]; exact hx3v
      · rw [hX, if_pos (by rw [hq0, hc1, zero_add])]
        exact rawdiff_valid_of_eq hPx hQx (hxeq hc1)
    · rw [hX, if_pos (by rw [hq1, hexcl hq1, add_zero]),
        rawdiff_of_canon_zero hQx (hQcanon hq1)]
      exact hPx
  · intro hc1
    have hq0 : Qinf = 0 := by
      rcases hQb with h | h
      · exact h
      · exact absurd (hexcl h) (by rw [hc1]; exact one_ne_zero)
    rw [hX, if_pos (by rw [hq0, hc1, zero_add])]
    exact rawdiff_decodeFe_zero hPx hQx (hxeq hc1)

/-- The two coordinate muxes reproduce the full nine-cell point mux, because on
the `Q = 𝒪` branch the cancellation flag is provably zero (the `sameX` test
fails there) and `P.isInf = 0`.  The cancellation branch now carries the muxed
coordinates themselves (which are canonically zero in the x-lane). -/
private lemma mux_pair_eq {Px Py Qx x3v y3v outXv outYv : Emu (F circomPrime)}
    {Pinf Qinf cancelv : F circomPrime}
    (hcb : IsBool cancelv)
    (hexcl : Qinf = 1 → cancelv = 0)
    (hQx : Fe.Valid Qx) (hQcanon : Qinf = 1 → decodeFe Qx = 0)
    (hPinf0 : Pinf = 0)
    (hX : outXv = if Qinf + cancelv = 1 then
        (Vector.ofFn fun k : Fin numLimbs => (Px[k.val]'k.isLt) - (Qx[k.val]'k.isLt))
      else x3v)
    (hY : outYv = if Qinf = 1 then Py else y3v) :
    (⟨outXv, outYv, cancelv⟩ : FlaggedPoint (F circomPrime))
      = if Qinf = 1 then (⟨Px, Py, Pinf⟩ : FlaggedPoint (F circomPrime))
        else (if cancelv = 1 then (⟨outXv, outYv, 1⟩ : FlaggedPoint (F circomPrime))
          else ⟨x3v, y3v, 0⟩) := by
  by_cases h : Qinf = 1
  · rw [if_pos h, hX, if_pos (by rw [h, hexcl h, add_zero]),
      rawdiff_of_canon_zero hQx (hQcanon h), hexcl h, hPinf0, hY, if_pos h]
  · rw [if_neg h]
    rcases hcb with hc0 | hc1
    · rw [if_neg (by rw [hc0]; exact zero_ne_one), hc0, hX,
        if_neg (by rw [hc0, add_zero]; exact h), hY, if_neg h]
    · rw [if_pos hc1, hc1]

set_option maxRecDepth 4000 in
theorem soundness : Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [SubMod.circuit, SubMod.Assumptions, SubMod.Spec,
    CancelLow.circuit, CancelLow.Assumptions, CancelLow.Spec,
    
    MulMod.circuit, MulMod.Assumptions, MulMod.Spec,
    MulModSub2F32.circuit, MulModSub2F32.Assumptions, MulModSub2F32.Spec,
    MulModSub2W32N.circuit, MulModSub2W32N.Assumptions, MulModSub2W32N.Spec,
    EqFe.circuit, EqFe.Assumptions, EqFe.Spec,
    Mux.circuit, Mux.Assumptions, Mux.Spec,
    DivOrZeroS32.circuit, DivOrZeroS32.Assumptions, DivOrZeroS32.Spec, secpParams]
  obtain ⟨hsameX, hcancel, hden,
    hlam, hx3, hy3, houtX, houtY⟩ := h_holds
  -- input validity components
  have hPx : Fe.Valid input_P_x := h_assumptions.1.2.1
  have hPy : Fe.Valid input_P_y := h_assumptions.1.2.2.1
  have hQx : Fe.Valid input_Q_x := h_assumptions.2.1.2.1
  have hQy : Fe.Valid input_Q_y := h_assumptions.2.1.2.2.1
  have hPinf0 : input_P_isInf = 0 := h_assumptions.2.2.1
  have hQcanon : input_Q_isInf = 1 → decodeFe input_Q_x = 0 := h_assumptions.2.2.2
  have hpn := pConst_normalized env
  have hpv := pConst_value env
  obtain ⟨⟨hIPx, hIPy, hIPi⟩, hIQx, hIQy, hIQi⟩ := h_input
  -- raw borrow denominator for the chord (mirrors dyU, with x-coords)
  have hdxe : decodeFe (Vector.map (Expression.eval env)
        (Vector.ofFn fun k : Fin numLimbs => input_var_Q_x[k.val]'k.isLt
          + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
            - input_var_P_x[k.val]'k.isLt)))
      = decodeFe input_Q_x - decodeFe input_P_x := by
    rw [map_eval_borrow, hIQx, hIPx]
    exact decodeFe_borrow input_Q_x input_P_x hQx.1 hPx
  -- sameX via the packed-halves equality flag: decode-equal iff chord difference zero
  have hsameXd := EqFe.flag_eq_decode_eq hQx hPx hsameX
  have hcond : (decodeFe input_Q_x = decodeFe input_P_x)
      ↔ (decodeFe (Vector.map (Expression.eval env)
        (Vector.ofFn fun k : Fin numLimbs => input_var_Q_x[k.val]'k.isLt
          + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
            - input_var_P_x[k.val]'k.isLt))) = 0) := by
    rw [hdxe, sub_eq_zero]
  have hsameX' := hsameXd.trans (if_congr hcond rfl rfl)
  have hsxb : IsBool _ := isBool_of_eq_ite hsameX'
  let syv : Emu (F circomPrime) :=
    emuOfNat ((decodeFe input_P_y + decodeFe input_Q_y).val)
  have hsye : decodeFe syv = decodeFe input_P_y + decodeFe input_Q_y := by
    exact decodeFe_emuOfNat_val _
  have hoppYghost :
      (if decodeFe input_P_y + decodeFe input_Q_y = 0 then (1 : F circomPrime) else 0)
        = if decodeFe syv = 0 then 1 else 0 := by
    rw [hsye]
  have hcancelmul := fun (hQ0 : input_Q_isInf = 0) =>
    cancelLow_eq_mul h_assumptions.1 h_assumptions.2.1 hPinf0 hQ0 hsameXd
      (hcancel hsxb)
  have hcb := isBool_of_eq_ite_zero (hcancel hsxb) hsxb
  have hz0 : decodeFe (Vector.map (Expression.eval env) zeroConst) = 0 := by
    rw [DivOrZero.eval_zeroConst, decodeFe, value_emuOfNat (by positivity), Nat.cast_zero]
  -- ghost tangent-numerator chain (algebraically 3·P.x²), only to feed
  -- `soundness_core`'s hypothesis shape; the real content is `DivOrZeroF.Spec`
  let x1sqv : Emu (F circomPrime) := emuOfNat ((decodeFe input_P_x * decodeFe input_P_x).val)
  have hx1sqd : decodeFe x1sqv = decodeFe input_P_x * decodeFe input_P_x :=
    decodeFe_emuOfNat_val _
  let x1sq2v : Emu (F circomPrime) := emuOfNat ((decodeFe x1sqv + decodeFe x1sqv).val)
  have hx1sq2e : decodeFe x1sq2v = decodeFe x1sqv + decodeFe x1sqv :=
    decodeFe_emuOfNat_val _
  let tNumv : Emu (F circomPrime) := emuOfNat ((decodeFe x1sq2v + decodeFe x1sqv).val)
  have htNume : decodeFe tNumv = decodeFe x1sq2v + decodeFe x1sqv :=
    decodeFe_emuOfNat_val _
  -- raw tangent denominator facts (unreduced `2y`)
  have htDene := decodeFe_sum2 input_P_y hPy.1
  -- denominator mux
  have hden' := hden (by rw [hsameX']; exact isBool_ite)
  rw [map_eval_sum2_input env _ input_P_y hIPy] at hden'
  -- chord numerator ghost: the eval of the circuit `dyU` variable is the borrow value
  have hdye : decodeFe (Vector.map (Expression.eval env)
        (Vector.ofFn fun k : Fin numLimbs => input_var_Q_y[k.val]'k.isLt
          + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
            - input_var_P_y[k.val]'k.isLt)))
      = decodeFe input_Q_y - decodeFe input_P_y := by
    rw [map_eval_borrow, hIQy, hIPy]
    exact decodeFe_borrow input_Q_y input_P_y hQy.1 hPy
  -- fused conditional slope certificate (widened chord denominator via DivOrZeroF3)
  obtain ⟨hlamv, hlam1'⟩ := hlam (by
    refine ⟨hPx, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hsameX']; exact isBool_ite
    · intro i
      have hcell := congrArg (fun v : Emu (F circomPrime) => v[i.val]'i.isLt)
        (map_eval_borrow env input_var_Q_y input_var_P_y)
      rw [hIQy, hIPy] at hcell
      simp only [Vector.getElem_map, Vector.getElem_ofFn] at hcell ⊢
      rw [hcell]
      exact limb_borrow_lt i.val (hQy.1 i) (hPy.1 i)
    · rw [map_eval_borrow, hIQy, hIPy]
      exact value_borrow_lt input_Q_y input_P_y hQy hPy
    · intro i
      have hcellden : (Vector.map (Expression.eval env)
            (Vector.mapRange numLimbs fun j =>
              var (F := F circomPrime) { index := i₀ + 3 + 2 + j }))[i.val]'i.isLt
          = env.get (i₀ + 3 + 2 + i.val) := by
        rw [Vector.getElem_map, Vector.getElem_mapRange]; rfl
      rw [← hcellden, hden']
      split
      · exact lt_trans (limb_sum2_bound input_P_y hPy.1 i) (by norm_num [limbBits])
      · have hcell := congrArg (fun v : Emu (F circomPrime) => v[i.val]'i.isLt)
          (map_eval_borrow env input_var_Q_x input_var_P_x)
        rw [hIQx, hIPx] at hcell
        simp only [Vector.getElem_map, Vector.getElem_ofFn] at hcell ⊢
        rw [hcell]
        exact limb_borrow_lt i.val (hQx.1 i) (hPx.1 i)
    · rw [hden']
      split
      · exact lt_trans (value_sum2_bound input_P_y hPy) (by have := P256_pos; omega)
      · rw [map_eval_borrow, hIQx, hIPx]
        exact value_borrow_lt input_Q_x input_P_x hQx hPx
    · rw [hden']
      split
      · exact value_sum2_alias input_P_y hPy
      · rename_i hsx_ne
        intro hmod
        exfalso
        apply hsx_ne
        have hd0 : decodeFe (Vector.map (Expression.eval env)
              (Vector.ofFn fun k : Fin numLimbs => input_var_Q_x[k.val]'k.isLt
                + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
                  - input_var_P_x[k.val]'k.isLt))) = 0 := by
          have hcast := (ZMod.natCast_eq_zero_iff (BigInt.value limbBits
            (Vector.map (Expression.eval env)
              (Vector.ofFn fun k : Fin numLimbs => input_var_Q_x[k.val]'k.isLt
                + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
                  - input_var_P_x[k.val]'k.isLt)))) P256).mpr (Nat.dvd_of_mod_eq_zero hmod)
          simpa only [decodeFe] using hcast
        rw [hsameX', if_pos hd0])
  -- affine result chain (fused multiply-subtracts, split via ghosts)
  obtain ⟨hx3v, hx3full⟩ := hx3 ⟨hlamv, hlamv, hPx, hQx⟩
  obtain ⟨lamSqg, hlamSqd, hx3e3⟩ := split_mulsub hx3full
  obtain ⟨xsg, hxse, hx3e⟩ := split3_sub hx3e3
  obtain ⟨hy3v, hy3full⟩ := hy3 (by
    refine ⟨hlamv, ?_, hPy, fe_valid_eval_zeroConst env⟩
    · intro i
      have hpq := congrArg (fun v : Emu (F circomPrime) => v[i.val]'i.isLt) hIPx
      simp only [Vector.getElem_map] at hpq
      have hx3l := hx3v.1 i
      rw [Fin.getElem_fin, Vector.getElem_map, Vector.getElem_mapRange] at hx3l
      simp only [circuit_norm] at hx3l
      simp only [circuit_norm, Vector.getElem_map, Vector.getElem_ofFn, hpq]
      rw [← sub_eq_add_neg]
      exact limb_borrow_lt i.val (hPx.1 i) hx3l)
  rw [map_eval_borrow_vfo, hIPx] at hy3full
  have hxde := decodeFe_borrow input_P_x _ hPx.1 hx3v
  rw [hz0, sub_zero] at hy3full
  obtain ⟨yprodg, hyprodd, hy3e⟩ := split_mulsub1 hy3full
  -- output selection muxes
  have hs1gen : ∀ (X Y : Emu (F circomPrime)) (c : F circomPrime), IsBool c →
      (⟨X, Y, c⟩ : FlaggedPoint (F circomPrime))
        = if c = 1 then (⟨X, Y, 1⟩ : FlaggedPoint (F circomPrime)) else ⟨X, Y, 0⟩ := by
    intro X Y c hc
    rcases hc with h | h <;> rw [h]
    · exact rfl
    · exact rfl
  -- on the `Q = 𝒪` branch the flag lane is provably zero, so the two coordinate
  -- muxes reproduce the full point mux
  have hPx0 : decodeFe input_P_x ≠ 0 :=
    OrderFactsCerts.noXZero_secp (P := ⟨decodeFe input_P_x, decodeFe input_P_y⟩)
      (h_assumptions.1.2.2.2 hPinf0)
  have hQb : IsBool input_Q_isInf := h_assumptions.2.1.1
  have hexcl := cancel_zero_of_Qinf (hcancel hsxb) hsameXd
    (fun hQ1 => by rw [hQcanon hQ1]; exact fun h => hPx0 h.symm)
  have hX' := houtX (isBool_add_excl hQb hcb hexcl)
  rw [map_eval_rawdiff, hIPx, hIQx] at hX'
  obtain ⟨houtXvalid, houtXzero⟩ :=
    outX_valid_zero hPx hQx hx3v hQb hcb hQcanon (hcancel hsxb) hsameXd hexcl hX'
  have houtYvalid : Fe.Valid _ := fe_valid_of_eq_ite hPy hy3v (houtY hQb)
  have hs2' := mux_pair_eq hcb hexcl hQx hQcanon hPinf0 hX' (houtY hQb)
  -- bridge `DivOrZeroF.Spec` into `soundness_core`'s `hlam` shape: with the ghost
  -- `numv := if sameX = 1 then tNumv else dyU`, the tangent branch reduces to 3·P.x²
  refine and_assoc.mp ⟨?_, houtXzero⟩
  exact soundness_core h_assumptions.1 h_assumptions.2.1 hdxe hdye hsameX' hsye hoppYghost
    hx1sqd hx1sq2e htNume htDene rfl hden'
    (by
      intro hne
      rw [hlam1' hne, apply_ite decodeFe]
      split
      · rw [htNume, hx1sq2e, hx1sqd]; ring
      · rfl)
    hlamSqd hxse hx3v hx3e hxde hyprodd
    hy3v hy3e hcancelmul houtXvalid houtYvalid rfl rfl rfl hs2'
    (by rw [if_neg (show input_P_isInf ≠ 1 by rw [hPinf0]; exact zero_ne_one)])

theorem completeness : Completeness (F circomPrime) main Assumptions := by
  circuit_proof_start [SubMod.circuit, SubMod.Assumptions, SubMod.Spec,
    CancelLow.circuit, CancelLow.Assumptions, CancelLow.Spec,
    
    MulMod.circuit, MulMod.Assumptions, MulMod.Spec,
    MulModSub2F32.circuit, MulModSub2F32.Assumptions, MulModSub2F32.Spec,
    MulModSub2W32N.circuit, MulModSub2W32N.Assumptions, MulModSub2W32N.Spec,
    EqFe.circuit, EqFe.Assumptions, EqFe.Spec,
    Mux.circuit, Mux.Assumptions, Mux.Spec,
    DivOrZeroS32.circuit, DivOrZeroS32.Assumptions, DivOrZeroS32.Spec, secpParams]
  obtain ⟨hsameX, hcancel, hden,
    hlam, hx3, hy3, houtX, houtY⟩ := h_env
  -- input validity components
  have hPx : Fe.Valid input_P_x := h_assumptions.1.2.1
  have hPy : Fe.Valid input_P_y := h_assumptions.1.2.2.1
  have hQx : Fe.Valid input_Q_x := h_assumptions.2.1.2.1
  have hQy : Fe.Valid input_Q_y := h_assumptions.2.1.2.2.1
  have hpn := pConst_normalized env.toEnvironment
  have hpv := pConst_value env.toEnvironment
  obtain ⟨⟨hIPx, hIPy, hIPi⟩, hIQx, hIQy, hIQi⟩ := h_input
  -- raw borrow denominator for the chord (mirrors dyU, with x-coords)
  have hdxe : decodeFe (Vector.map (Expression.eval env.toEnvironment)
        (Vector.ofFn fun k : Fin numLimbs => input_var_Q_x[k.val]'k.isLt
          + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
            - input_var_P_x[k.val]'k.isLt)))
      = decodeFe input_Q_x - decodeFe input_P_x := by
    rw [map_eval_borrow, hIQx, hIPx]
    exact decodeFe_borrow input_Q_x input_P_x hQx.1 hPx
  have hsameXd := EqFe.flag_eq_decode_eq hQx hPx hsameX
  have hcond : (decodeFe input_Q_x = decodeFe input_P_x)
      ↔ (decodeFe (Vector.map (Expression.eval env.toEnvironment)
        (Vector.ofFn fun k : Fin numLimbs => input_var_Q_x[k.val]'k.isLt
          + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
            - input_var_P_x[k.val]'k.isLt))) = 0) := by
    rw [hdxe, sub_eq_zero]
  have hsameX' := hsameXd.trans (if_congr hcond rfl rfl)
  have hsxb : IsBool _ := isBool_of_eq_ite hsameX'
  have hdenb := hden hsxb
  rw [map_eval_sum2_input env.toEnvironment _ input_P_y hIPy] at hdenb
  -- chord numerator (dyU) bounds, shared by both discharge sites
  have hdyU_limb : ∀ i : Fin numLimbs,
      ZMod.val (Expression.eval env.toEnvironment
        ((Vector.ofFn fun k : Fin numLimbs => input_var_Q_y[k.val]'k.isLt
          + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
            - input_var_P_y[k.val]'k.isLt))[i.val]'i.isLt)) < 3 * 2 ^ limbBits := by
    intro i
    have hcell := congrArg (fun v : Emu (F circomPrime) => v[i.val]'i.isLt)
      (map_eval_borrow env.toEnvironment input_var_Q_y input_var_P_y)
    rw [hIQy, hIPy] at hcell
    simp only [Vector.getElem_map, Vector.getElem_ofFn] at hcell ⊢
    rw [hcell]
    exact limb_borrow_lt i.val (hQy.1 i) (hPy.1 i)
  have hdyU_val : BigInt.value limbBits (Vector.map (Expression.eval env.toEnvironment)
        (Vector.ofFn fun k : Fin numLimbs => input_var_Q_y[k.val]'k.isLt
          + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
            - input_var_P_y[k.val]'k.isLt))) < 3 * P256 := by
    rw [map_eval_borrow, hIQy, hIPy]
    exact value_borrow_lt input_Q_y input_P_y hQy hPy
  obtain ⟨hlamv, -⟩ := hlam (by
    refine ⟨hPx, hsxb, hdyU_limb, hdyU_val, ?_, ?_, ?_⟩
    · intro i
      have hcellden : (Vector.map (Expression.eval env.toEnvironment)
            (Vector.mapRange numLimbs fun j =>
              var (F := F circomPrime) { index := i₀ + 3 + 2 + j }))[i.val]'i.isLt
          = env.get (i₀ + 3 + 2 + i.val) := by
        rw [Vector.getElem_map, Vector.getElem_mapRange]; rfl
      rw [← hcellden, hdenb]
      split
      · exact lt_trans (limb_sum2_bound input_P_y hPy.1 i) (by norm_num [limbBits])
      · have hcell := congrArg (fun v : Emu (F circomPrime) => v[i.val]'i.isLt)
          (map_eval_borrow env.toEnvironment input_var_Q_x input_var_P_x)
        rw [hIQx, hIPx] at hcell
        simp only [Vector.getElem_map, Vector.getElem_ofFn] at hcell ⊢
        rw [hcell]
        exact limb_borrow_lt i.val (hQx.1 i) (hPx.1 i)
    · rw [hdenb]
      split
      · exact lt_trans (value_sum2_bound input_P_y hPy) (by have := P256_pos; omega)
      · rw [map_eval_borrow, hIQx, hIPx]
        exact value_borrow_lt input_Q_x input_P_x hQx hPx
    · rw [hdenb]
      split
      · exact value_sum2_alias input_P_y hPy
      · rename_i hsx_ne
        intro hmod
        exfalso
        apply hsx_ne
        have hd0 : decodeFe (Vector.map (Expression.eval env.toEnvironment)
              (Vector.ofFn fun k : Fin numLimbs => input_var_Q_x[k.val]'k.isLt
                + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
                  - input_var_P_x[k.val]'k.isLt))) = 0 := by
          have hcast := (ZMod.natCast_eq_zero_iff (BigInt.value limbBits
            (Vector.map (Expression.eval env.toEnvironment)
              (Vector.ofFn fun k : Fin numLimbs => input_var_Q_x[k.val]'k.isLt
                + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
                  - input_var_P_x[k.val]'k.isLt)))) P256).mpr (Nat.dvd_of_mod_eq_zero hmod)
          simpa only [decodeFe] using hcast
        rw [hsameX', if_pos hd0])
  obtain ⟨hx3v, -⟩ := hx3 ⟨hlamv, hlamv, hPx, hQx⟩
  obtain ⟨hy3v, -⟩ := hy3 (by
    refine ⟨hlamv, ?_, hPy, fe_valid_eval_zeroConst env.toEnvironment⟩
    · intro i
      have hpq := congrArg (fun v : Emu (F circomPrime) => v[i.val]'i.isLt) hIPx
      simp only [Vector.getElem_map] at hpq
      have hx3l := hx3v.1 i
      rw [Fin.getElem_fin, Vector.getElem_map, Vector.getElem_mapRange] at hx3l
      simp only [circuit_norm] at hx3l
      simp only [circuit_norm, Vector.getElem_map, Vector.getElem_ofFn, hpq]
      rw [← sub_eq_add_neg]
      exact limb_borrow_lt i.val (hPx.1 i) hx3l)
  have hPinf0 : input_P_isInf = 0 := h_assumptions.2.2.1
  have hQcanon : input_Q_isInf = 1 → decodeFe input_Q_x = 0 := h_assumptions.2.2.2
  have hQb : IsBool input_Q_isInf := h_assumptions.2.1.1
  have hcb := isBool_of_eq_ite_zero (hcancel hsxb) hsxb
  have hPx0 : decodeFe input_P_x ≠ 0 :=
    OrderFactsCerts.noXZero_secp (P := ⟨decodeFe input_P_x, decodeFe input_P_y⟩)
      (h_assumptions.1.2.2.2 hPinf0)
  have hexcl := cancel_zero_of_Qinf (hcancel hsxb) hsameXd
    (fun hQ1 => by rw [hQcanon hQ1]; exact fun h => hPx0 h.symm)
  refine ⟨hsxb, hsxb,
    ⟨hPx, hsxb, hdyU_limb, hdyU_val,
     (by
      intro i
      have hcellden : (Vector.map (Expression.eval env.toEnvironment)
            (Vector.mapRange numLimbs fun j =>
              var (F := F circomPrime) { index := i₀ + 3 + 2 + j }))[i.val]'i.isLt
          = env.get (i₀ + 3 + 2 + i.val) := by
        rw [Vector.getElem_map, Vector.getElem_mapRange]; rfl
      rw [← hcellden, hdenb]
      split
      · exact lt_trans (limb_sum2_bound input_P_y hPy.1 i) (by norm_num [limbBits])
      · have hcell := congrArg (fun v : Emu (F circomPrime) => v[i.val]'i.isLt)
          (map_eval_borrow env.toEnvironment input_var_Q_x input_var_P_x)
        rw [hIQx, hIPx] at hcell
        simp only [Vector.getElem_map, Vector.getElem_ofFn] at hcell ⊢
        rw [hcell]
        exact limb_borrow_lt i.val (hQx.1 i) (hPx.1 i)),
     (by
      rw [hdenb]
      split
      · exact lt_trans (value_sum2_bound input_P_y hPy) (by have := P256_pos; omega)
      · rw [map_eval_borrow, hIQx, hIPx]
        exact value_borrow_lt input_Q_x input_P_x hQx hPx),
     (by
      rw [hdenb]
      split
      · exact value_sum2_alias input_P_y hPy
      · rename_i hsx_ne
        intro hmod
        exfalso
        apply hsx_ne
        have hd0 : decodeFe (Vector.map (Expression.eval env.toEnvironment)
              (Vector.ofFn fun k : Fin numLimbs => input_var_Q_x[k.val]'k.isLt
                + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
                  - input_var_P_x[k.val]'k.isLt))) = 0 := by
          have hcast := (ZMod.natCast_eq_zero_iff (BigInt.value limbBits
            (Vector.map (Expression.eval env.toEnvironment)
              (Vector.ofFn fun k : Fin numLimbs => input_var_Q_x[k.val]'k.isLt
                + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
                  - input_var_P_x[k.val]'k.isLt)))) P256).mpr (Nat.dvd_of_mod_eq_zero hmod)
          simpa only [decodeFe] using hcast
        rw [hsameX', if_pos hd0])⟩,
    ⟨hlamv, hlamv, hPx, hQx⟩,
    (by
    refine ⟨hlamv, ?_, hPy, fe_valid_eval_zeroConst env.toEnvironment⟩
    · intro i
      have hpq := congrArg (fun v : Emu (F circomPrime) => v[i.val]'i.isLt) hIPx
      simp only [Vector.getElem_map] at hpq
      have hx3l := hx3v.1 i
      rw [Fin.getElem_fin, Vector.getElem_map, Vector.getElem_mapRange] at hx3l
      simp only [circuit_norm] at hx3l
      simp only [circuit_norm, Vector.getElem_map, Vector.getElem_ofFn, hpq]
      rw [← sub_eq_add_neg]
      exact limb_borrow_lt i.val (hPx.1 i) hx3l),
    isBool_add_excl hQb hcb hexcl, hQb⟩

def circuit : FormalCircuit (F circomPrime) Inputs FlaggedPoint where
  main; elaborated; Assumptions; Spec; soundness; completeness

end CompleteAdd
end Solution.Secp256k1ScalarMul

namespace Solution.Secp256k1ScalarMul

namespace MulMod

end MulMod

namespace MulModSub2
open AddMod

end MulModSub2
end Solution.Secp256k1ScalarMul

namespace Solution.Secp256k1ScalarMul
namespace CompleteAdd
open AddMod

private lemma expression_stable_of_field_eval_eq
    {env env' : ProverEnvironment (F circomPrime)}
    {x : Expression (F circomPrime)}
    (h : eval env x = eval env' x) :
    Expression.eval env.toEnvironment x = Expression.eval env'.toEnvironment x := by
  rw [CircuitType.eval_expression_prover_to_verifier (M := field),
    CircuitType.eval_expression_prover_to_verifier (M := field)] at h
  rw [CircuitType.eval_var_field, CircuitType.eval_var_field] at h
  exact h

set_option maxHeartbeats 3200000 in
theorem computableWitnesses : circuit.base.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  obtain ⟨P, Q⟩ := input
  have hsub : ∀ (X : Var SubMod.Inputs (F circomPrime)) (o : ℕ),
      (subcircuit SubMod.circuit X).localLength o = 285 := fun _ _ => rfl
  have hcanc : ∀ (X : Var CancelLow.Inputs (F circomPrime)) (o : ℕ),
      (subcircuit CancelLow.circuit X).localLength o = 2 := fun _ _ => rfl
  have hdivF3 : ∀ (X : Var DivOrZeroS32.Inputs (F circomPrime)) (o : ℕ),
      (subcircuit DivOrZeroS32.circuit X).localLength o = 442 := fun _ _ => rfl
  have hms2 : ∀ (X : Var MulModSub2F32.Inputs (F circomPrime)) (o : ℕ),
      (subcircuit MulModSub2F32.circuit X).localLength o = 356 := fun _ _ => rfl
  have hms2W32N : ∀ (X : Var MulModSub2W32N.Inputs (F circomPrime)) (o : ℕ),
      (subcircuit MulModSub2W32N.circuit X).localLength o = 420 := fun _ _ => rfl
  have hmxE : ∀ (X : Var (Mux.Inputs Emu) (F circomPrime)) (o : ℕ),
      (subcircuit (Mux.circuit (M := Emu)) X).localLength o = 4 := fun _ _ => rfl
  have hiszD : ∀ (x : Var EqFe.Inputs (F circomPrime)) (o : ℕ),
      (subcircuit EqFe.circuit x).localLength o = 3 := fun _ _ => rfl
  -- cheap bridge `circuit.output = main.output` (the raw `rfl` whnf is too costly
  -- for `DivOrZeroF3` since its output threads through `MulModTargetT`)
  have hFout3 : ∀ (X : Var DivOrZeroS32.Inputs (F circomPrime)) (o : ℕ),
      DivOrZeroS32.circuit.output X o = (DivOrZeroS32.main X).output o :=
    fun X o => (DivOrZeroS32.elaborated.output_eq X o).symm
  have hpc : ∀ {e e' : ProverEnvironment (F circomPrime)},
      Vector.map (Expression.eval e.toEnvironment) pConst
        = Vector.map (Expression.eval e'.toEnvironment) pConst := by
    intro e e'; rw [DivOrZero.eval_pConst, DivOrZero.eval_pConst]
  have iszDOut : ∀ (x : Var EqFe.Inputs (F circomPrime)) {e e' : ProverEnvironment (F circomPrime)}
      {O k' : ℕ}, e.AgreesBelow k' e' → O + 3 ≤ k' →
      Expression.eval e.toEnvironment ((subcircuit EqFe.circuit x).output O)
        = Expression.eval e'.toEnvironment ((subcircuit EqFe.circuit x).output O) := by
    intro x e e' O k' hag hk
    exact expression_stable_of_field_eval_eq
      (EqFe.eval_output_of_agreesBelow x (offset := O) hag hk)
  have mulStable : ∀ {e e' : ProverEnvironment (F circomPrime)} (a b : Expression (F circomPrime)),
      Expression.eval e.toEnvironment a = Expression.eval e'.toEnvironment a →
      Expression.eval e.toEnvironment b = Expression.eval e'.toEnvironment b →
      Expression.eval e.toEnvironment (a * b) = Expression.eval e'.toEnvironment (a * b) := by
    intro e e' a b ha hb
    change Expression.eval e.toEnvironment (Expression.mul a b)
      = Expression.eval e'.toEnvironment (Expression.mul a b)
    rw [eval_mul, eval_mul, ha, hb]
  have hcell : ∀ {e e' : ProverEnvironment (F circomPrime)} (x : Var Emu (F circomPrime)),
      Vector.map (Expression.eval e.toEnvironment) x
        = Vector.map (Expression.eval e'.toEnvironment) x →
      ∀ (i : ℕ) (hi : i < numLimbs),
      Expression.eval e.toEnvironment (x[i]'hi) =
        Expression.eval e'.toEnvironment (x[i]'hi) := by
    intro e e' x hx i hi
    have := congrArg (fun v : Vector (F circomPrime) numLimbs => v[i]'hi) hx
    simpa only [Vector.getElem_map] using this
  have hnl : numLimbs = 4 := rfl
  have hsE : size Emu = 4 := rfl
  have hsF : size FlaggedPoint = 9 := rfl
  -- named block outputs at concrete offsets (mirrors `main`)
  let sameX : Var field (F circomPrime) :=
    (subcircuit EqFe.circuit { a := Q.x, b := P.x }).output offset
  let cancel : Var field (F circomPrime) :=
    (subcircuit CancelLow.circuit { sameX := sameX, y1 := P.y, y2 := Q.y }).output (offset + 3)
  let dyU : Var Emu (F circomPrime) := Vector.ofFn fun k : Fin numLimbs =>
    Q.y[k.val]'k.isLt
      + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
        - P.y[k.val]'k.isLt)
  let dxU : Var Emu (F circomPrime) := Vector.ofFn fun k : Fin numLimbs =>
    Q.x[k.val]'k.isLt
      + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
        - P.x[k.val]'k.isLt)
  let tDen : Var Emu (F circomPrime) := Vector.ofFn fun k : Fin numLimbs =>
    P.y[k.val]'k.isLt + P.y[k.val]'k.isLt
  let den : Var Emu (F circomPrime) :=
    (subcircuit (Mux.circuit (M := Emu))
      { selector := sameX, ifTrue := tDen, ifFalse := dxU }).output
      (offset + 3 + 2)
  let lam32 : Var (BigInt 8) (F circomPrime) :=
    (subcircuit DivOrZeroS32.circuit { sel := sameX, x := P.x, dyU := dyU, den := den }).output
      (offset + 3 + 2 + 4)
  let x3 : Var Emu (F circomPrime) :=
    (subcircuit MulModSub2F32.circuit { a := lam32, b := lam32, s1 := P.x, s2 := Q.x }).output
      (offset + 3 + 2 + 4 + 442)
  let xdU : Var Emu (F circomPrime) := Vector.ofFn fun k : Fin numLimbs =>
    P.x[k.val]'k.isLt
      + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
        - x3[k.val]'k.isLt)
  let y3 : Var Emu (F circomPrime) :=
    (subcircuit MulModSub2W32N.circuit { a := lam32, b := xdU, s1 := P.y, s2 := zeroConst }).output
      (offset + 3 + 2 + 4 + 442 + 356)
  let s1 : Var FlaggedPoint (F circomPrime) :=
    { x := x3, y := y3, isInf := cancel }
  unfold main
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.pure_structuralComputableWitnesses_iff,
    hsub, hcanc, hdivF3, hms2, hms2W32N, hmxE, hiszD, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- 1. sameX ← EqFe { Q.x, P.x }
  · refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) EqFe.circuit _ _ _ ?_
      EqFe.computableWitnesses env env'
    intro k e e' hle h_agree h_in
    simp only [circuit_norm, Inputs.mk.injEq, FlaggedPoint.mk.injEq] at h_in
    obtain ⟨⟨hPx, _, _⟩, hQx, _, _⟩ := h_in
    simp only [circuit_norm] at ⊢; rw [EqFe.Inputs.mk.injEq]
    exact ⟨hQx, hPx⟩
  -- 2. cancel ← CancelLow { sameX, P.y, Q.y }
  · refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) CancelLow.circuit _ _ _ ?_ CancelLow.computableWitnesses env env'
    intro k e e' hle h_agree h_in
    simp only [circuit_norm, Inputs.mk.injEq, FlaggedPoint.mk.injEq] at h_in
    obtain ⟨⟨_, hPy, _⟩, _, hQy, _⟩ := h_in
    simp only [circuit_norm] at ⊢; rw [CancelLow.Inputs.mk.injEq]
    exact ⟨iszDOut _ (O := offset) h_agree (by omega), hPy, hQy⟩
  -- 3. den ← Mux { sameX, tDen, dxU }
  · refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) (Mux.circuit (M := Emu)) _ _ _ ?_ (Mux.computableWitnesses (M := Emu)) env env'
    intro k e e' hle h_agree h_in
    simp only [circuit_norm, Inputs.mk.injEq, FlaggedPoint.mk.injEq] at h_in
    obtain ⟨⟨hPx, hPy, _⟩, hQx, _, _⟩ := h_in
    simp only [circuit_norm] at ⊢; rw [Mux.Inputs.mk.injEq]
    refine ⟨iszDOut _ (O := offset) h_agree (by omega), ?_, ?_⟩
    · apply Vector.ext
      intro i hi
      simp only [Vector.getElem_map, Vector.getElem_ofFn]
      simp only [Expression.eval, hcell _ hPy i hi]
    · show Vector.map (Expression.eval e.toEnvironment)
          (Vector.ofFn fun k : Fin numLimbs => Q.x[k.val]'k.isLt
            + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
              - P.x[k.val]'k.isLt))
        = Vector.map (Expression.eval e'.toEnvironment)
          (Vector.ofFn fun k : Fin numLimbs => Q.x[k.val]'k.isLt
            + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
              - P.x[k.val]'k.isLt))
      rw [map_eval_borrow, map_eval_borrow, hQx, hPx]
  -- 4. lam32 ← DivOrZeroS32 { sameX, P.x, dyU, den }
  · refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) DivOrZeroS32.circuit _ _ _ ?_ DivOrZeroS32.computableWitnesses env env'
    intro k e e' hle h_agree h_in
    simp only [circuit_norm, Inputs.mk.injEq, FlaggedPoint.mk.injEq] at h_in
    obtain ⟨⟨hPx, hPy, _⟩, _, hQy, _⟩ := h_in
    simp only [circuit_norm] at ⊢; rw [DivOrZeroS32.Inputs.mk.injEq]
    refine ⟨iszDOut _ (O := offset) h_agree (by omega), hPx, ?_,
      emu_map_eval_eq_of_eval_eq (Mux.eval_output_of_agreesBelow (M := Emu)
        { selector := sameX, ifTrue := tDen, ifFalse := dxU }
        (offset := offset + 3 + 2) h_agree (by omega))⟩
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_map, Vector.getElem_ofFn]
    simp only [Expression.eval, hcell _ hQy i hi, hcell _ hPy i hi]
  -- 9. x3 ← MulModSub2F32 { lam32, lam32, P.x, Q.x }
  · refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) MulModSub2F32.circuit _ _ _ ?_ MulModSub2F32.computableWitnesses env env'
    intro k e e' hle h_agree h_in
    simp only [circuit_norm, Inputs.mk.injEq, FlaggedPoint.mk.injEq] at h_in
    obtain ⟨⟨hPx, _, _⟩, hQx, _, _⟩ := h_in
    have hlam := MulMod.bigInt_map_eval_eq_of_eval_eq
      (DivOrZeroS32.eval_output_of_agreesBelow { sel := sameX, x := P.x, dyU := dyU, den := den }
        (offset := offset + 3 + 2 + 4) h_agree (by omega))
    simp only [circuit_norm] at ⊢; rw [MulModSub2F32.Inputs.mk.injEq, hFout3]
    exact ⟨hlam, hlam, hPx, hQx⟩
  -- 11. y3 ← MulModSub2W32N { lam32, xdU, P.y, zeroConst }
  · refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) MulModSub2W32N.circuit _ _ _ ?_ MulModSub2W32N.computableWitnesses env env'
    intro k e e' hle h_agree h_in
    simp only [circuit_norm, Inputs.mk.injEq, FlaggedPoint.mk.injEq] at h_in
    obtain ⟨⟨hPx, hPy, _⟩, _, _, _⟩ := h_in
    have hlam := MulMod.bigInt_map_eval_eq_of_eval_eq
      (DivOrZeroS32.eval_output_of_agreesBelow { sel := sameX, x := P.x, dyU := dyU, den := den }
        (offset := offset + 3 + 2 + 4) h_agree (by omega))
    have hx3s := emu_map_eval_eq_of_eval_eq
      (MulModSub2F32.eval_output_of_agreesBelow { a := lam32, b := lam32, s1 := P.x, s2 := Q.x }
        (offset := offset + 3 + 2 + 4 + 442) h_agree (by omega))
    simp only [circuit_norm] at ⊢; rw [MulModSub2W32N.Inputs.mk.injEq, hFout3]
    refine ⟨hlam, ?_, hPy, by rw [DivOrZero.eval_zeroConst, DivOrZero.eval_zeroConst]⟩
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_map, Vector.getElem_ofFn]
    have hPx_i := hcell _ hPx i hi
    have hx3_i := hcell _ hx3s i hi
    simp only [Expression.eval]
    exact congrArg₂ (· + ·) hPx_i
      (congrArg₂ (· + ·) rfl (congrArg (HMul.hMul (-1 : F circomPrime)) hx3_i))
  -- 14. outX ← Mux { Q.isInf, P.x, x3 }
  · refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) (Mux.circuit (M := Emu)) _ _ _ ?_
      (Mux.computableWitnesses (M := Emu)) env env'
    intro k e e' hle h_agree h_in
    simp only [circuit_norm] at hle
    simp only [circuit_norm, Inputs.mk.injEq, FlaggedPoint.mk.injEq] at h_in
    obtain ⟨⟨hPx, hPy, hPi⟩, hQx, hQy, hQi⟩ := h_in
    simp only [circuit_norm] at ⊢
    rw [Mux.Inputs.mk.injEq]
    refine ⟨?_, ?_, emu_map_eval_eq_of_eval_eq
      (MulModSub2F32.eval_output_of_agreesBelow { a := lam32, b := lam32, s1 := P.x, s2 := Q.x }
        (offset := offset + 3 + 2 + 4 + 442) h_agree (by omega))⟩
    · exact congrArg₂ (· + ·) hQi
        (CancelLow.eval_output_of_agreesBelow
          { sameX := EqFe.circuit.output { a := Q.x, b := P.x } offset, y1 := P.y, y2 := Q.y }
          (offset := offset + 3) h_agree (by omega))
    · rw [map_eval_rawdiff, map_eval_rawdiff, hPx, hQx]
  -- 15. outY ← Mux { Q.isInf, P.y, y3 }
  · refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) (Mux.circuit (M := Emu)) _ _ _ ?_
      (Mux.computableWitnesses (M := Emu)) env env'
    intro k e e' hle h_agree h_in
    simp only [circuit_norm] at hle
    simp only [circuit_norm, Inputs.mk.injEq, FlaggedPoint.mk.injEq] at h_in
    obtain ⟨⟨hPx, hPy, hPi⟩, _, _, hQi⟩ := h_in
    simp only [circuit_norm] at ⊢
    rw [Mux.Inputs.mk.injEq]
    exact ⟨hQi, hPy, emu_map_eval_eq_of_eval_eq
      (MulModSub2W32N.eval_output_of_agreesBelow { a := lam32, b := xdU, s1 := P.y, s2 := zeroConst }
        (offset := offset + 3 + 2 + 4 + 442 + 356) h_agree (by omega))⟩

private lemma emuVar_stable {off k : ℕ} {env env' : ProverEnvironment (F circomPrime)}
    (h_agree : env.AgreesBelow k env') (hk : off + size Emu ≤ k) :
    eval env ((varFromOffset Emu off : Var Emu (F circomPrime)))
      = eval env' ((varFromOffset Emu off : Var Emu (F circomPrime))) := by
  rw [CircuitType.eval_expression_prover_to_verifier (M := Emu),
    CircuitType.eval_expression_prover_to_verifier (M := Emu), ProvableType.ext_iff]
  intro i hi
  rw [← ProvableType.getElem_eval_toElements
      (varFromOffset Emu off : Var Emu (F circomPrime)) i hi,
    ← ProvableType.getElem_eval_toElements
      (varFromOffset Emu off : Var Emu (F circomPrime)) i hi]
  simp only [varFromOffset, ProvableType.toElements_fromElements, Vector.getElem_mapRange,
    Expression.eval]
  exact h_agree (off + i) (by omega)

lemma eval_output_of_agreesBelow (input : Var Inputs (F circomPrime)) {offset k : ℕ}
    {env env' : ProverEnvironment (F circomPrime)}
    (h_agree : env.AgreesBelow k env') (hk : offset + 1235 ≤ k) :
    eval env ((main input).output offset) = eval env' ((main input).output offset) := by
  obtain ⟨P, Q⟩ := input
  change eval env
      ({ x := varFromOffset Emu (offset + 1227),
         y := varFromOffset Emu (offset + 1231),
         isInf := var { index := offset + 4 } } : Var FlaggedPoint (F circomPrime)) =
    eval env'
      ({ x := varFromOffset Emu (offset + 1227),
         y := varFromOffset Emu (offset + 1231),
         isInf := var { index := offset + 4 } } : Var FlaggedPoint (F circomPrime))
  simp only [circuit_norm]
  rw [FlaggedPoint.mk.injEq]
  refine ⟨?_, ?_, h_agree (offset + 4) (by omega)⟩
  · simpa only [circuit_norm] using
      emuVar_stable (off := offset + 1227) h_agree (by rw [show size Emu = 4 from rfl]; omega)
  · simpa only [circuit_norm] using
      emuVar_stable (off := offset + 1231) h_agree (by rw [show size Emu = 4 from rfl]; omega)

end CompleteAdd
end Solution.Secp256k1ScalarMul
