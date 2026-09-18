import Solution.Secp256k1ScalarMul.CompleteAdd
import Solution.Secp256k1ScalarMul.DivOrZeroW
import Solution.Secp256k1ScalarMul.ProofBlocker
import Challenge.Utils.ComputableWitnessLemmas



namespace Solution.Secp256k1ScalarMul
namespace Double

open CompleteAdd


structure Inputs (F : Type) where
  P : FlaggedPoint F
deriving ProvableStruct

def main (input : Var Inputs (F circomPrime)) :
    Circuit (F circomPrime) (Var FlaggedPoint (F circomPrime)) := do
  let P := input.P

  -- tangent denominator: raw 2·P.y  (secp256k1 has a = 0)
  let tDen : Var Emu (F circomPrime) := Vector.ofFn fun k : Fin numLimbs =>
    P.y[k.val]'k.isLt + P.y[k.val]'k.isLt

  -- slope λ = 3x²/2y: the square is interpolated INSIDE the wide-target
  -- division certificate, so no MulMod ever materializes 3x².  The division
  -- also returns its internal zero flag, avoiding a duplicate `IsZeroFeD`.
  let div ← subcircuit DivOrZeroW.circuit { num := P.x, den := tDen }
  let lam := div.lam

  -- affine result: x₃ = λ² − P.x − P.x, y₃ = λ·(P.x − x₃) − P.y — each a
  -- single fused multiply-subtract via the offset target certificate
  let x3 ← subcircuit MulModSub2.circuit { a := lam, b := lam, s1 := P.x, s2 := P.x }
  let xdU : Var Emu (F circomPrime) := Vector.ofFn fun k : Fin numLimbs =>
    P.x[k.val]'k.isLt
      + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
        - x3[k.val]'k.isLt)
  let y3 ← subcircuit MulModSub2D3.circuit { a := lam, b := xdU, s1 := P.y, s2 := zeroConst }

  -- secp256k1 has no affine points of order two (`ProofBlocker.noOrderTwo`), so a
  -- valid affine `P` has `P.y ≠ 0`, hence the doubling denominator `2·P.y` never
  -- vanishes for finite inputs and the output infinity flag equals the input
  -- flag exactly (`2·𝒪 = 𝒪`, and `2·P` is finite for finite on-curve `P`).
  -- No extra witness/row is needed for the flag.
  return { x := x3, y := y3, isInf := P.isInf }

instance elaborated : ElaboratedCircuit (F circomPrime) Inputs FlaggedPoint main := by
  elaborate_circuit


def outputAt (input : Var Inputs (F circomPrime)) (offset : ℕ) : Var FlaggedPoint (F circomPrime) :=
  { x := varFromOffset Emu (offset + 751)
    y := varFromOffset Emu (offset + 1185)
    isInf := input.P.isInf }

lemma output_eq_outputAt (input : Var Inputs (F circomPrime)) (offset : ℕ) :
    (main input).output offset = outputAt input offset := by
  rw [elaborated.output_eq]
  simp only [elaborated, outputAt]
  norm_num [secpParams, secpParams3, eqNParamsAdd, eqNParams3Add,
    GroupedEqXV.widthAllocFrom, vMul, wfMul, vW, vrW, wfW,
    vMulD3, vrMulD3, wfMulD3,
    numLimbs, limbBits]


def Assumptions (input : Inputs (F circomPrime)) : Prop :=
  input.P.Valid


def Spec (input : Inputs (F circomPrime)) (out : FlaggedPoint (F circomPrime)) : Prop :=
  out.Valid ∧
    decodePoint out =
      Specs.ShortWeierstrass.add Specs.Secp256k1.curve
        (decodePoint input.P) (decodePoint input.P)


theorem double_soundness_core
    {P s1 s2 out infv finv : FlaggedPoint (F circomPrime)}
    {x1sqv x1sq2v tNumv tDenv lamv lamSqv xsv x3v xdv yprodv y3v : Emu (F circomPrime)}
    {oppY : F circomPrime}
    (hP : P.Valid)
    (hx1sq : decodeFe x1sqv = decodeFe P.x * decodeFe P.x)
    (hx1sq2 : decodeFe x1sq2v = decodeFe x1sqv + decodeFe x1sqv)
    (htNum : decodeFe tNumv = decodeFe x1sq2v + decodeFe x1sqv)
    (htDen : decodeFe tDenv = decodeFe P.y + decodeFe P.y)
    (hoppY : oppY = if decodeFe tDenv = 0 then 1 else 0)
    (hlam : decodeFe tDenv ≠ 0 → decodeFe lamv * decodeFe tDenv = decodeFe tNumv)
    (hlamSq : decodeFe lamSqv = decodeFe lamv * decodeFe lamv)
    (hxs : decodeFe xsv = decodeFe lamSqv - decodeFe P.x)
    (hx3v : Fe.Valid x3v) (hx3 : decodeFe x3v = decodeFe xsv - decodeFe P.x)
    (hxd : decodeFe xdv = decodeFe P.x - decodeFe x3v)
    (hyprod : decodeFe yprodv = decodeFe lamv * decodeFe xdv)
    (hy3v : Fe.Valid y3v) (hy3 : decodeFe y3v = decodeFe yprodv - decodeFe P.y)
    (hinfx : Fe.Valid infv.x) (hinfy : Fe.Valid infv.y) (hinff : infv.isInf = 1)
    (hfin : finv = ⟨x3v, y3v, 0⟩)
    (hs1 : s1 = if oppY = 1 then infv else finv)
    (hs2 : s2 = if P.isInf = 1 then P else s1)
    (hout : out = if P.isInf = 1 then P else s2) :
    out.Valid ∧
      decodePoint out =
        Specs.ShortWeierstrass.add Specs.Secp256k1.curve (decodePoint P) (decodePoint P) := by
  have hz0 : decodeFe (emuOfNat 0 : Emu (F circomPrime)) = 0 := by
    rw [decodeFe, value_emuOfNat (by positivity), Nat.cast_zero]
  exact soundness_core (dxv := emuOfNat 0) (dyv := emuOfNat 0) (syv := tDenv)
    (numv := tNumv) (denv := tDenv) (sameX := 1) (cancel := oppY)
    hP hP
    (by rw [sub_self]; exact hz0)
    (by rw [sub_self]; exact hz0)
    (by rw [if_pos hz0])
    htDen hoppY hx1sq hx1sq2 htNum htDen
    (by rw [if_pos (rfl : (1 : F circomPrime) = 1)])
    (by rw [if_pos (rfl : (1 : F circomPrime) = 1)])
    hlam hlamSq hxs hx3v hx3 hxd hyprod hy3v hy3
    (fun _ => by rw [one_mul])
    hinfx hinfy hinff hfin hs1 hs2 hout


private lemma decodeFe_emuOfNat_val (f : Specs.Secp256k1.Fp) :
    decodeFe (emuOfNat f.val) = f := by
  show ((BigInt.value limbBits (emuOfNat f.val) : ℕ) : Specs.Secp256k1.Fp) = f
  rw [value_emuOfNat (lt_trans (ZMod.val_lt f) P256_lt), ZMod.natCast_val, ZMod.cast_id]


theorem double_soundness_coreW
    {P s1 s2 out infv finv : FlaggedPoint (F circomPrime)}
    {tDenv lamv lamSqv xsv x3v xdv yprodv y3v : Emu (F circomPrime)}
    {oppY : F circomPrime}
    (hP : P.Valid)
    (htDen : decodeFe tDenv = decodeFe P.y + decodeFe P.y)
    (hoppY : oppY = if decodeFe tDenv = 0 then 1 else 0)
    (hlam : decodeFe tDenv ≠ 0 →
      decodeFe lamv * decodeFe tDenv = 3 * (decodeFe P.x * decodeFe P.x))
    (hlamSq : decodeFe lamSqv = decodeFe lamv * decodeFe lamv)
    (hxs : decodeFe xsv = decodeFe lamSqv - decodeFe P.x)
    (hx3v : Fe.Valid x3v) (hx3 : decodeFe x3v = decodeFe xsv - decodeFe P.x)
    (hxd : decodeFe xdv = decodeFe P.x - decodeFe x3v)
    (hyprod : decodeFe yprodv = decodeFe lamv * decodeFe xdv)
    (hy3v : Fe.Valid y3v) (hy3 : decodeFe y3v = decodeFe yprodv - decodeFe P.y)
    (hinfx : Fe.Valid infv.x) (hinfy : Fe.Valid infv.y) (hinff : infv.isInf = 1)
    (hfin : finv = ⟨x3v, y3v, 0⟩)
    (hs1 : s1 = if oppY = 1 then infv else finv)
    (hs2 : s2 = if P.isInf = 1 then P else s1)
    (hout : out = if P.isInf = 1 then P else s2) :
    out.Valid ∧
      decodePoint out =
        Specs.ShortWeierstrass.add Specs.Secp256k1.curve (decodePoint P) (decodePoint P) := by
  set xsq : Specs.Secp256k1.Fp := decodeFe P.x * decodeFe P.x with hxsq
  exact double_soundness_core
    (x1sqv := emuOfNat xsq.val)
    (x1sq2v := emuOfNat (xsq + xsq).val)
    (tNumv := emuOfNat ((xsq + xsq) + xsq).val)
    hP
    (decodeFe_emuOfNat_val xsq)
    (by rw [decodeFe_emuOfNat_val, decodeFe_emuOfNat_val])
    (by rw [decodeFe_emuOfNat_val, decodeFe_emuOfNat_val, decodeFe_emuOfNat_val])
    htDen hoppY
    (fun h => by rw [decodeFe_emuOfNat_val, hlam h, hxsq]; ring)
    hlamSq hxs hx3v hx3 hxd hyprod hy3v hy3
    hinfx hinfy hinff hfin hs1 hs2 hout

private lemma mux_idempotent
    {P s1 s2 : FlaggedPoint (F circomPrime)} {b : F circomPrime}
    (hb : IsBool b) (hs2 : s2 = if b = 1 then P else s1) :
    s2 = if b = 1 then P else s2 := by
  rcases hb with h0 | h1
  · simp [h0]
  · simpa [h1] using hs2


private lemma direct_output_of_muxed
    {P infv : FlaggedPoint (F circomPrime)}
    {x y : Emu (F circomPrime)} {opp outInf : F circomPrime}
    {target : Specs.ShortWeierstrass.GroupPoint Specs.Secp256k1.Fp}
    (hPbool : IsBool P.isInf) (hoppbool : IsBool opp)
    (hx : Fe.Valid x) (hy : Fe.Valid y) (hinf : infv.isInf = 1)
    (houtInf : outInf = P.isInf + opp - P.isInf * opp)
    (hold :
      (if P.isInf = 1 then P else if opp = 1 then infv else ⟨x, y, 0⟩).Valid ∧
      decodePoint (if P.isInf = 1 then P else if opp = 1 then infv else ⟨x, y, 0⟩)
        = target) :
    (⟨x, y, outInf⟩ : FlaggedPoint (F circomPrime)).Valid ∧
      decodePoint ⟨x, y, outInf⟩ = target := by
  rcases hPbool with hP0 | hP1 <;> rcases hoppbool with ho0 | ho1
  · have hz : outInf = 0 := by rw [houtInf, hP0, ho0]; norm_num
    simpa [hP0, ho0, hz] using hold
  · have hz : outInf = 1 := by rw [houtInf, hP0, ho1]; norm_num
    refine ⟨⟨Or.inr hz, hx, hy, fun h => ?_⟩, ?_⟩
    · rw [hz] at h
      exfalso
      exact one_ne_zero h
    · rw [decodePoint_of_isInf hz, ← hold.2]
      simp only [hP0, ho1, if_false, if_true]
      exact (decodePoint_of_isInf hinf).symm
  · have hz : outInf = 1 := by rw [houtInf, hP1, ho0]; norm_num
    refine ⟨⟨Or.inr hz, hx, hy, fun h => ?_⟩, ?_⟩
    · rw [hz] at h
      exfalso
      exact one_ne_zero h
    · rw [decodePoint_of_isInf hz, ← hold.2]
      simp only [hP1, if_true]
      exact (decodePoint_of_isInf hP1).symm
  · have hz : outInf = 1 := by rw [houtInf, hP1, ho1]; norm_num
    refine ⟨⟨Or.inr hz, hx, hy, fun h => ?_⟩, ?_⟩
    · rw [hz] at h
      exfalso
      exact one_ne_zero h
    · rw [decodePoint_of_isInf hz, ← hold.2]
      simp only [hP1, if_true]
      exact (decodePoint_of_isInf hP1).symm

theorem soundness : Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [SubMod.circuit, SubMod.Assumptions, SubMod.Spec,
    MulModSub2.circuit, MulModSub2.Assumptions, MulModSub2.Spec,
    MulModSub2D3.circuit, MulModSub2D3.Assumptions, MulModSub2D3.Spec,
    Mux.circuit, Mux.Assumptions, Mux.Spec,
    DivOrZeroW.circuit, DivOrZeroW.Assumptions, DivOrZeroW.Spec, secpParams]
  obtain ⟨hlam, hx3, hy3⟩ := h_holds
  have hPbool : IsBool input_P_isInf := h_assumptions.1
  have hPx : Fe.Valid input_P_x := h_assumptions.2.1
  have hPy : Fe.Valid input_P_y := h_assumptions.2.2.1
  have hpn := pConst_normalized env
  have hpv := pConst_value env
  -- the raw 2y denominator: map-eval bridge, decode, and zero-flag conversion
  have hy_map : Vector.map (Expression.eval env) input_var_P_y = input_P_y := h_input.2.1
  have hden_map := map_eval_sum2_input env _ _ hy_map
  have htDene := decodeFe_sum2 input_P_y hPy.1
  -- slope (square fused into the wide-target certificate)
  obtain ⟨hlamv, hlam1, -, hoppY⟩ := hlam
    ⟨hPx, (fun i => by simp only [hden_map]; exact limb_sum2_bound input_P_y hPy.1 i),
      (by simp only [hden_map]; exact value_sum2_bound input_P_y hPy),
      (by simp only [hden_map]; exact value_sum2_alias input_P_y hPy)⟩
  simp only [hden_map] at hlam1 hoppY
  have hoppY' := hoppY
  -- affine result chain (fused multiply-subtracts, split via ghosts)
  obtain ⟨hx3v, hx3full⟩ := hx3 ⟨hlamv.1, hlamv.1, hPx⟩
  obtain ⟨lamSqg, hlamSqd, hx3e3⟩ := split_mulsub hx3full
  obtain ⟨xsg, hxse, hx3e⟩ := split3_sub hx3e3
  have hx_map : Vector.map (Expression.eval env) input_var_P_x = input_P_x := h_input.1
  obtain ⟨hy3v, hy3full⟩ := hy3 (by
    refine ⟨hlamv.1, ?_, ?_, hPy, fe_valid_eval_zeroConst env⟩
    · intro i
      have hpq := congrArg (fun v : Emu (F circomPrime) => v[i.val]'i.isLt) hx_map
      simp only [Vector.getElem_map] at hpq
      have hx3l := hx3v.1 i
      rw [Fin.getElem_fin, Vector.getElem_map, Vector.getElem_mapRange] at hx3l
      simp only [circuit_norm] at hx3l
      simp only [circuit_norm, Vector.getElem_map, Vector.getElem_ofFn, hpq]
      rw [← sub_eq_add_neg]
      exact limb_borrow_lt i.val (hPx.1 i) hx3l
    · rw [map_eval_borrow_vfo, hx_map]
      exact value_borrow_lt input_P_x _ hPx hx3v)
  rw [map_eval_borrow_vfo, hx_map] at hy3full
  have hxde := decodeFe_borrow input_P_x _ hPx.1 hx3v
  have hz0 : decodeFe (Vector.map (Expression.eval env) zeroConst) = 0 := by
    rw [DivOrZero.eval_zeroConst, decodeFe, value_emuOfNat (by positivity), Nat.cast_zero]
  rw [hz0, sub_zero] at hy3full
  obtain ⟨yprodg, hyprodd, hy3e⟩ := split_mulsub1 hy3full
  let Pval : FlaggedPoint (F circomPrime) :=
    { x := input_P_x, y := input_P_y, isInf := input_P_isInf }
  let opp : F circomPrime := env.get (i₀ + 1)
  let x3val : Emu (F circomPrime) := Vector.map (Expression.eval env)
    (varFromOffset Emu (i₀ + 751))
  let y3val : Emu (F circomPrime) := Vector.map (Expression.eval env)
    (varFromOffset Emu (i₀ + 751 + 434))
  let infv : FlaggedPoint (F circomPrime) :=
    { x := Vector.map (Expression.eval env) zeroConst,
      y := Vector.map (Expression.eval env) zeroConst, isInf := 1 }
  let finv : FlaggedPoint (F circomPrime) := { x := x3val, y := y3val, isInf := 0 }
  let s1v : FlaggedPoint (F circomPrime) := if opp = 1 then infv else finv
  let oldout : FlaggedPoint (F circomPrime) :=
    if Pval.isInf = 1 then Pval else s1v
  have hx3v' : Fe.Valid x3val := by simpa [x3val, circuit_norm] using hx3v
  have hy3v' : Fe.Valid y3val := by simpa [y3val, circuit_norm] using hy3v
  have hold : oldout.Valid ∧
      decodePoint oldout = Specs.ShortWeierstrass.add Specs.Secp256k1.curve
        (decodePoint Pval) (decodePoint Pval) := by
    apply double_soundness_coreW (P := Pval) (s1 := s1v) (s2 := oldout)
      (out := oldout) (infv := infv) (finv := finv)
    · exact h_assumptions
    · exact htDene
    · exact hoppY'
    · exact hlam1
    · exact hlamSqd
    · exact hxse
    · exact hx3v'
    · exact hx3e
    · exact hxde
    · exact hyprodd
    · exact hy3v'
    · exact hy3e
    · exact fe_valid_eval_zeroConst env
    · exact fe_valid_eval_zeroConst env
    · rfl
    · rfl
    · rfl
    · rfl
    · exact mux_idempotent hPbool rfl
  -- secp256k1 has no order-two point: for a finite valid `P`, `P.y ≠ 0`, so the
  -- doubling denominator `2·P.y` is nonzero and the zero flag `opp` is `0`.
  have hopp0 : input_P_isInf = 0 → opp = 0 := by
    intro h0
    have honc := h_assumptions.2.2.2 h0
    have hyne : decodeFe input_P_y ≠ 0 := ProofBlocker.noOrderTwo _ honc
    have h2y : decodeFe input_P_y + decodeFe input_P_y ≠ 0 := by
      intro hsum
      apply hyne
      have h2 : (2 : Specs.Secp256k1.Fp) * decodeFe input_P_y = 0 := by
        rw [two_mul]; exact hsum
      rcases mul_eq_zero.mp h2 with h | h
      · exact absurd h Specs.Secp256k1.two_ne_zero_fp
      · exact h
    show env.get (i₀ + 1) = 0
    rw [hoppY', if_neg (by rw [htDene]; exact h2y)]
  have hgoal : ({ x := x3val, y := y3val, isInf := input_P_isInf } :
        FlaggedPoint (F circomPrime)).Valid ∧
      decodePoint { x := x3val, y := y3val, isInf := input_P_isInf } =
        Specs.ShortWeierstrass.add Specs.Secp256k1.curve
          (decodePoint Pval) (decodePoint Pval) := by
    rcases hPbool with h0 | h1
    · -- finite input: the zero flag vanishes, so the muxed output is exactly the
      -- affine result `finv`, which is the returned point
      have hopp := hopp0 h0
      have holdeq : oldout = { x := x3val, y := y3val, isInf := input_P_isInf } := by
        simp only [oldout, Pval, s1v, finv, h0, hopp,
          if_neg (by norm_num : (0 : F circomPrime) ≠ 1)]
      rw [← holdeq]; exact hold
    · -- infinite input: both sides are the point at infinity
      refine ⟨⟨Or.inr h1, hx3v', hy3v', fun h => absurd (h.symm.trans h1) zero_ne_one⟩, ?_⟩
      have hPinf : decodePoint Pval = Specs.ShortWeierstrass.GroupPoint.infinity :=
        decodePoint_of_isInf (by simpa [Pval] using h1)
      have hnew : decodePoint { x := x3val, y := y3val, isInf := input_P_isInf }
          = Specs.ShortWeierstrass.GroupPoint.infinity :=
        decodePoint_of_isInf h1
      rw [hnew, hPinf]
      rfl
  exact hgoal

theorem completeness : Completeness (F circomPrime) main Assumptions := by
  circuit_proof_start [SubMod.circuit, SubMod.Assumptions, SubMod.Spec,
    MulModSub2.circuit, MulModSub2.Assumptions, MulModSub2.Spec,
    MulModSub2D3.circuit, MulModSub2D3.Assumptions, MulModSub2D3.Spec,
    Mux.circuit, Mux.Assumptions, Mux.Spec,
    DivOrZeroW.circuit, DivOrZeroW.Assumptions, DivOrZeroW.Spec, secpParams]
  obtain ⟨hlam, hx3, hy3⟩ := h_env
  have hPbool : IsBool input_P_isInf := h_assumptions.1
  have hPx : Fe.Valid input_P_x := h_assumptions.2.1
  have hPy : Fe.Valid input_P_y := h_assumptions.2.2.1
  have hpn := pConst_normalized env.toEnvironment
  have hpv := pConst_value env.toEnvironment
  have hy_map : Vector.map (Expression.eval env.toEnvironment) input_var_P_y = input_P_y :=
    h_input.2.1
  have hden_map := map_eval_sum2_input env.toEnvironment _ _ hy_map
  obtain ⟨hlamv, -, -, -⟩ := hlam
    ⟨hPx, (fun i => by simp only [hden_map]; exact limb_sum2_bound input_P_y hPy.1 i),
      (by simp only [hden_map]; exact value_sum2_bound input_P_y hPy),
      (by simp only [hden_map]; exact value_sum2_alias input_P_y hPy)⟩
  obtain ⟨hx3v, -⟩ := hx3 ⟨hlamv.1, hlamv.1, hPx⟩
  have hx_map : Vector.map (Expression.eval env.toEnvironment) input_var_P_x = input_P_x :=
    h_input.1
  obtain ⟨hy3v, -⟩ := hy3 (by
    refine ⟨hlamv.1, ?_, ?_, hPy, fe_valid_eval_zeroConst env.toEnvironment⟩
    · intro i
      have hpq := congrArg (fun v : Emu (F circomPrime) => v[i.val]'i.isLt) hx_map
      simp only [Vector.getElem_map] at hpq
      have hx3l := hx3v.1 i
      rw [Fin.getElem_fin, Vector.getElem_map, Vector.getElem_mapRange] at hx3l
      simp only [circuit_norm] at hx3l
      simp only [circuit_norm, Vector.getElem_map, Vector.getElem_ofFn, hpq]
      rw [← sub_eq_add_neg]
      exact limb_borrow_lt i.val (hPx.1 i) hx3l
    · rw [map_eval_borrow_vfo, hx_map]
      exact value_borrow_lt input_P_x _ hPx hx3v)
  refine ⟨⟨hPx,
      (fun i => by simp only [hden_map]; exact limb_sum2_bound input_P_y hPy.1 i),
      (by simp only [hden_map]; exact value_sum2_bound input_P_y hPy),
      (by simp only [hden_map]; exact value_sum2_alias input_P_y hPy)⟩,
    ⟨hlamv.1, hlamv.1, hPx⟩,
    (by
    refine ⟨hlamv.1, ?_, ?_, hPy, fe_valid_eval_zeroConst env.toEnvironment⟩
    · intro i
      have hpq := congrArg (fun v : Emu (F circomPrime) => v[i.val]'i.isLt) hx_map
      simp only [Vector.getElem_map] at hpq
      have hx3l := hx3v.1 i
      rw [Fin.getElem_fin, Vector.getElem_map, Vector.getElem_mapRange] at hx3l
      simp only [circuit_norm] at hx3l
      simp only [circuit_norm, Vector.getElem_map, Vector.getElem_ofFn, hpq]
      rw [← sub_eq_add_neg]
      exact limb_borrow_lt i.val (hPx.1 i) hx3l
    · rw [map_eval_borrow_vfo, hx_map]
      exact value_borrow_lt input_P_x _ hPx hx3v)⟩

def circuit : FormalCircuit (F circomPrime) Inputs FlaggedPoint where
  main; elaborated; Assumptions; Spec; soundness; completeness

end Double
end Solution.Secp256k1ScalarMul



namespace Solution.Secp256k1ScalarMul
namespace Double
open AddMod

private theorem toFlat_append (a b : Operations (F circomPrime)) :
    (a ++ b).toFlat = a.toFlat ++ b.toFlat := by
  induction a using Operations.induct with
  | empty => simp [Operations.toFlat]
  | witness _ _ _ ih | assert _ _ ih | lookup _ _ ih | interact _ _ ih =>
    simp [Operations.toFlat, ih]
  | subcircuit s _ ih => simp [Operations.toFlat, ih, List.append_assoc]

private theorem toFlat_flatten (L : List (Operations (F circomPrime))) :
    Operations.toFlat L.flatten = (L.map Operations.toFlat).flatten := by
  induction L with
  | nil => rfl
  | cons a rest ih =>
    rw [List.flatten_cons, toFlat_append, ih, List.map_cons, List.flatten_cons]

private theorem flatStructural_of_no_witness
    {Parent : TypeMap} [CircuitType Parent]
    (parentInput : Var Parent (F circomPrime))
    (env env' : ProverEnvironment (F circomPrime)) :
    ∀ (ops : List (FlatOperation (F circomPrime))) (offset : ℕ),
      (∀ x ∈ ops, match x with | .witness _ _ => False | _ => True) →
      Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.FlatOperation.StructuralComputableWitnesses
        parentInput env env' offset ops := by
  intro ops
  induction ops with
  | nil => intro offset _; trivial
  | cons x rest ih =>
    intro offset h
    have h_rest : ∀ y ∈ rest, match y with | .witness _ _ => False | _ => True :=
      fun y hy => h y (List.mem_cons_of_mem _ hy)
    cases x with
    | witness m c => exact absurd (h _ (List.mem_cons_self ..)) (by simp)
    | assert e => exact ih offset h_rest
    | lookup l => exact ih offset h_rest
    | interact i => exact ih offset h_rest

private lemma expression_stable_of_field_eval_eq
    {env env' : ProverEnvironment (F circomPrime)}
    {x : Expression (F circomPrime)}
    (h : eval env x = eval env' x) :
    Expression.eval env.toEnvironment x = Expression.eval env'.toEnvironment x := by
  rw [CircuitType.eval_expression_prover_to_verifier (M := field),
    CircuitType.eval_expression_prover_to_verifier (M := field)] at h
  rw [CircuitType.eval_var_field, CircuitType.eval_var_field] at h
  exact h


private lemma mulModCircuit_output_cell_stable
    (X : Var (MulMod.Inputs numLimbs) (F circomPrime)) {o k : ℕ}
    {e e' : ProverEnvironment (F circomPrime)}
    (h_agree : e.AgreesBelow k e') (hk : o + numLimbs + numLimbs ≤ k)
    (i : ℕ) (hi : i < numLimbs) :
    Expression.eval e.toEnvironment
        (((MulMod.circuit secpParams gfMul posOfMul 5 vMul vMul hgvMul hNfMul hNfMul).output
          X o)[i]'hi)
      = Expression.eval e'.toEnvironment
        (((MulMod.circuit secpParams gfMul posOfMul 5 vMul vMul hgvMul hNfMul hNfMul).output
          X o)[i]'hi) := by
  have hout : (MulMod.circuit secpParams gfMul posOfMul 5 vMul vMul hgvMul hNfMul hNfMul).output
      X o = varFromOffset (BigInt numLimbs) (o + numLimbs) := rfl
  rw [hout,
    show (varFromOffset (BigInt numLimbs) (o + numLimbs)
        : Var (BigInt numLimbs) (F circomPrime))[i]'hi
      = var { index := o + numLimbs + i } from by
    rw [ProvableType.varFromOffset_fields]
    simp [Vector.getElem_mapRange]]
  exact h_agree (o + numLimbs + i) (by omega)

private lemma tDen_map_stable {e e' : ProverEnvironment (F circomPrime)}
    {y : Var Emu (F circomPrime)}
    (h : Vector.map (Expression.eval e.toEnvironment) y
      = Vector.map (Expression.eval e'.toEnvironment) y) :
    Vector.map (Expression.eval e.toEnvironment)
      (Vector.ofFn fun k : Fin numLimbs => y[k.val]'k.isLt + y[k.val]'k.isLt)
      = Vector.map (Expression.eval e'.toEnvironment)
        (Vector.ofFn fun k : Fin numLimbs => y[k.val]'k.isLt + y[k.val]'k.isLt) := by
  apply Vector.ext
  intro i hi
  have hcell : Expression.eval e.toEnvironment (y[i]'hi)
      = Expression.eval e'.toEnvironment (y[i]'hi) := by
    have := congrArg (fun v : Vector (F circomPrime) numLimbs => v[i]'hi) h
    simpa only [Vector.getElem_map] using this
  simp only [Vector.getElem_map, Vector.getElem_ofFn]
  rw [show Expression.eval e.toEnvironment (y[i]'hi + y[i]'hi)
        = Expression.eval e.toEnvironment (y[i]'hi)
          + Expression.eval e.toEnvironment (y[i]'hi) from rfl,
    show Expression.eval e'.toEnvironment (y[i]'hi + y[i]'hi)
        = Expression.eval e'.toEnvironment (y[i]'hi)
          + Expression.eval e'.toEnvironment (y[i]'hi) from rfl, hcell]

set_option maxHeartbeats 3200000 in
theorem computableWitnesses : circuit.base.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  obtain ⟨P⟩ := input
  have hdivW : ∀ (X : Var DivOrZero.Inputs (F circomPrime)) (o : ℕ),
      (subcircuit DivOrZeroW.circuit X).localLength o = 751 := fun _ _ => rfl
  have hms2 : ∀ (X : Var MulModSub2.Inputs (F circomPrime)) (o : ℕ),
      (subcircuit MulModSub2.circuit X).localLength o = 434 := fun _ _ => rfl
  have hms2D3 : ∀ (X : Var MulModSub2D3.Inputs (F circomPrime)) (o : ℕ),
      (subcircuit MulModSub2D3.circuit X).localLength o = 434 := fun _ _ => rfl
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
  -- named block outputs (mirrors `main`)
  let tDen : Var Emu (F circomPrime) := Vector.ofFn fun k : Fin numLimbs =>
    P.y[k.val]'k.isLt + P.y[k.val]'k.isLt
  let div : Var DivOrZeroW.Output (F circomPrime) :=
    (subcircuit DivOrZeroW.circuit { num := P.x, den := tDen }).output offset
  let lam : Var Emu (F circomPrime) := div.lam
  let x3 : Var Emu (F circomPrime) :=
    (subcircuit MulModSub2.circuit { a := lam, b := lam, s1 := P.x, s2 := P.x }).output
      (offset + 751)
  let xdU : Var Emu (F circomPrime) := Vector.ofFn fun k : Fin numLimbs =>
    P.x[k.val]'k.isLt
      + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
        - x3[k.val]'k.isLt)
  unfold main
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.pure_structuralComputableWitnesses_iff,
    hdivW, hms2, hms2D3, and_true]
  refine ⟨?_, ?_, ?_⟩
  -- 1. div ← DivOrZeroW { P.x, tDen }; returns both λ and the zero flag
  · refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) DivOrZeroW.circuit _ _ _ ?_ DivOrZeroW.computableWitnesses env env'
    intro k e e' hle h_agree h_in
    simp only [circuit_norm, Inputs.mk.injEq, FlaggedPoint.mk.injEq] at h_in
    obtain ⟨hPx, hPy, _⟩ := h_in
    simp only [circuit_norm] at ⊢; rw [DivOrZero.Inputs.mk.injEq]
    exact ⟨hPx, tDen_map_stable hPy⟩
  -- 2. x3 ← MulModSub2 { lam, lam, P.x, P.x }
  · refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) MulModSub2.circuit _ _ _ ?_ MulModSub2.computableWitnesses env env'
    intro k e e' hle h_agree h_in
    simp only [circuit_norm, Inputs.mk.injEq, FlaggedPoint.mk.injEq] at h_in
    obtain ⟨hPx, _, _⟩ := h_in
    have hlam := emu_map_eval_eq_of_eval_eq
      (DivOrZeroW.eval_lam_output_of_agreesBelow { num := P.x, den := tDen }
        (offset := offset) h_agree (by omega))
    simp only [circuit_norm] at ⊢; rw [MulModSub2.Inputs.mk.injEq]
    exact ⟨hlam, hlam, hPx, hPx⟩
  -- 3. y3 ← MulModSub2D3 { lam, xdU, P.y, zeroConst }
  · refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) MulModSub2D3.circuit _ _ _ ?_ MulModSub2D3.computableWitnesses env env'
    intro k e e' hle h_agree h_in
    simp only [circuit_norm, Inputs.mk.injEq, FlaggedPoint.mk.injEq] at h_in
    obtain ⟨hPx, hPy, _⟩ := h_in
    have hlam := emu_map_eval_eq_of_eval_eq
      (DivOrZeroW.eval_lam_output_of_agreesBelow { num := P.x, den := tDen }
        (offset := offset) h_agree (by omega))
    have hx3s := emu_map_eval_eq_of_eval_eq
      (MulModSub2.eval_output_of_agreesBelow { a := lam, b := lam, s1 := P.x, s2 := P.x }
        (offset := offset + 751) h_agree (by omega))
    simp only [circuit_norm] at ⊢; rw [MulModSub2D3.Inputs.mk.injEq]
    refine ⟨hlam, ?_, hPy, by rw [DivOrZero.eval_zeroConst, DivOrZero.eval_zeroConst]⟩
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_map, Vector.getElem_ofFn]
    have hPx_i := hcell _ hPx i hi
    have hx3_i := hcell _ hx3s i hi
    simp only [Expression.eval]
    exact congrArg₂ (· + ·) hPx_i
      (congrArg₂ (· + ·) rfl (congrArg (HMul.hMul (-1 : F circomPrime)) hx3_i))

theorem computableWitness : ∀ n input,
    ProverEnvironment.OnlyAccessedBelow n
      (fun env : ProverEnvironment (F circomPrime) => eval env input) →
    Circuit.ComputableWitnesses (main input) n :=
  Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnesses_implies
    (circuit := circuit.base) computableWitnesses

private lemma fpVar_stable {off k : ℕ} {env env' : ProverEnvironment (F circomPrime)}
    (h_agree : env.AgreesBelow k env') (hk : off + size FlaggedPoint ≤ k) :
    eval env ((varFromOffset FlaggedPoint off : FlaggedPoint (Expression (F circomPrime))))
      = eval env' ((varFromOffset FlaggedPoint off : FlaggedPoint (Expression (F circomPrime)))) := by
  rw [CircuitType.eval_expression_prover_to_verifier (M := FlaggedPoint),
    CircuitType.eval_expression_prover_to_verifier (M := FlaggedPoint), ProvableType.ext_iff]
  intro i hi
  rw [← ProvableType.getElem_eval_toElements
      (varFromOffset FlaggedPoint off : FlaggedPoint (Expression (F circomPrime))) i hi,
    ← ProvableType.getElem_eval_toElements
      (varFromOffset FlaggedPoint off : FlaggedPoint (Expression (F circomPrime))) i hi]
  simp only [varFromOffset, ProvableType.toElements_fromElements, Vector.getElem_mapRange,
    Expression.eval]
  exact h_agree (off + i) (by omega)


lemma eval_output_of_agreesBelow (input : Var Inputs (F circomPrime)) {offset k : ℕ}
    {env env' : ProverEnvironment (F circomPrime)}
    (h_input : eval env input = eval env' input)
    (h_agree : env.AgreesBelow k env') (hk : offset + 1619 ≤ k) :
    eval env ((main input).output offset) = eval env' ((main input).output offset) := by
  rw [elaborated.output_eq input offset]
  change eval env
      ({ x := varFromOffset Emu (offset + 751),
         y := varFromOffset Emu (offset + 751 + 434),
         isInf := input.P.isInf } :
        Var FlaggedPoint (F circomPrime)) =
    eval env'
      ({ x := varFromOffset Emu (offset + 751),
         y := varFromOffset Emu (offset + 751 + 434),
         isInf := input.P.isInf } :
        Var FlaggedPoint (F circomPrime))
  simp only [circuit_norm]
  rw [FlaggedPoint.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · apply Vector.ext
    intro i hi
    simp only [numLimbs] at hi
    simp only [Vector.getElem_map, varFromOffset, ProvableType.toElements_fromElements,
      Vector.getElem_mapRange, Expression.eval]
    exact h_agree _ (by omega)
  · apply Vector.ext
    intro i hi
    simp only [numLimbs] at hi
    simp only [Vector.getElem_map, varFromOffset, ProvableType.toElements_fromElements,
      Vector.getElem_mapRange, Expression.eval]
    exact h_agree _ (by omega)
  · have h := congrArg
      (fun z : Inputs (F circomPrime) => z.P.isInf) h_input
    simpa only [circuit_norm] using h

end Double
end Solution.Secp256k1ScalarMul
