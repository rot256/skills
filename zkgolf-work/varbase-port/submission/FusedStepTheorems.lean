import Solution.Secp256k1ScalarMul.CompleteAddTheorems
import Solution.Secp256k1ScalarMul.Bridge
import Solution.Secp256k1ScalarMul.ProofBlocker
import Solution.Secp256k1ScalarMul.CancelTheorems
import Solution.Secp256k1ScalarMul.OrderFactsCerts

/-!
# Value-level soundness core for the fused double-add step

`fused_soundness_core` proves that the ELM λ-chain of `FusedStep` computes
`(R + R) + T` under the complete group law, taking all circuit facts in
decoded form.

Structure (R, T finite, not the cancellation case):
* `S := (xS, yS)` with the ghost `yS := λ₁·(R.x − xS) − R.y` equals
  `add R T` — tangent branch when `T.x = R.x` (then `T = R`), chord otherwise.
* If `xS = R.x` then `yS = −R.y`, so `S = −R` and `add S R = 𝒪`; the circuit
  raises exactly the `zOut` flag.  No torsion facts are needed: whenever the
  flag fires, 𝒪 is the correct answer.
* Otherwise the second chord: the slope of `(S, R)` is `−(λ₁ + w)` where
  `w·(xS − R.x) = 2·R.y`, and squaring absorbs the sign:
  `x₄ = (λ₁+w)² − xS − R.x`, `y₄ = (λ₁+w)·(x₄ − R.x) − R.y`.
* `(R+T)+R = (R+R)+T` closes the generic branch through the Mathlib bridge.
-/

namespace Solution.Secp256k1ScalarMul
namespace FusedStepTheorems

open Specs.ShortWeierstrass Specs.Secp256k1
open CompleteAdd

/-- Extensionality for `FlaggedPoint` values. -/
lemma fp_ext {P Q : FlaggedPoint (F circomPrime)}
    (hx : P.x = Q.x) (hy : P.y = Q.y) (hi : P.isInf = Q.isInf) : P = Q := by
  cases P; cases Q
  simp only [FlaggedPoint.mk.injEq]
  exact ⟨hx, hy, hi⟩

/-- Group-law commutation: `(a+b)+a = (a+a)+b` at the bridge level. -/
lemma add_rot (a b : Bridge.W.Point) :
    add curve (add curve (Bridge.toSpec a) (Bridge.toSpec b)) (Bridge.toSpec a)
      = add curve (add curve (Bridge.toSpec a) (Bridge.toSpec a)) (Bridge.toSpec b) := by
  rw [← Bridge.bridge_add, ← Bridge.bridge_add, ← Bridge.bridge_add, ← Bridge.bridge_add]
  congr 1
  abel

/-- Wrapper for `add_rot` on spec-level points known to be on the curve. -/
lemma add_rot' (G H : GroupPoint Fp)
    (hG : OnCurveOrInfinity curve G) (hH : OnCurveOrInfinity curve H) :
    add curve (add curve G H) G = add curve (add curve G G) H := by
  have ha := Bridge.toSpec_fromSpec G hG
  have hb := Bridge.toSpec_fromSpec H hH
  rw [← ha, ← hb, add_rot]

/-- Cancellation branch: `(b+b) + (−b) = b`. -/
lemma add_dbl_neg (b : Bridge.W.Point) :
    add curve (add curve (Bridge.toSpec b) (Bridge.toSpec b)) (Bridge.toSpec (-b))
      = Bridge.toSpec b := by
  rw [← Bridge.bridge_add, ← Bridge.bridge_add]
  rw [show b + b + -b = b by abel]

/-- `toSpec` of a negated finite bridge point is the y-negated affine point. -/
lemma toSpec_neg_mk (P : Point Fp) (hP : OnCurve curve P) :
    Bridge.toSpec (-(Bridge.mkPoint P hP)) = .affine ⟨P.x, -P.y⟩ := by
  rw [Bridge.mkPoint, WeierstrassCurve.Affine.Point.neg_some]
  simp [Bridge.toSpec, WeierstrassCurve.Affine.negY, Bridge.W]

lemma toSpec_mk (P : Point Fp) (hP : OnCurve curve P) :
    Bridge.toSpec (Bridge.mkPoint P hP) = .affine P := rfl

/-- Nonzero doubled y-coordinate for finite on-curve points. -/
lemma two_y_ne_zero {P : Point Fp} (hP : OnCurve curve P) : P.y + P.y ≠ 0 := by
  intro h
  apply ProofBlocker.noOrderTwo P hP
  have h2 : (2 : Fp) * P.y = 0 := by linear_combination h
  rcases mul_eq_zero.mp h2 with h' | h'
  · exact absurd h' CompleteAdd.two_ne_zero_fp
  · exact h'

/-- The affine double is the tangent point (no order-2 points on secp256k1). -/
lemma add_self_eq_tangent (P : Point Fp) (hP : OnCurve curve P) :
    add curve (.affine P) (.affine P) = .affine (tangent curve P) := by
  rw [show (P : Point Fp) = ⟨P.x, P.y⟩ from rfl, add_affine]
  rw [if_pos rfl, if_neg (fun h : P.y = -P.y => two_y_ne_zero hP (by linear_combination h))]

/--
Stage 2 of the chain: given `S = (xS, yS)` on-curve with the ghost identity
`yS = λ₁·(R.x − xS) − R.y`, the circuit's `(x₄, y₄, zOut)` decodes to
`add (affine S) (affine R)`.
-/
theorem stage2_core
    {x4v y4v : Emu (F circomPrime)}
    {rx ry xS yS lam1d wd den2d mulAd bMuld : Fp}
    {sameX2 zOut : F circomPrime}
    (hRon : ry ^ 2 = rx ^ 3 + 7)
    (hSon : yS ^ 2 = xS ^ 3 + 7)
    (hyS : yS = lam1d * (rx - xS) - ry)
    (hsameX2 : sameX2 = if xS = rx then 1 else 0)
    (hden2 : den2d = if sameX2 = 1 then -1 else xS - rx)
    (hw : den2d ≠ 0 → wd * den2d = ry + ry)
    (hmulA : mulAd = lam1d + wd)
    (hx4v : Fe.Valid x4v)
    (hx4 : decodeFe x4v = mulAd * mulAd - xS - rx)
    (hbMul : bMuld = decodeFe x4v - rx)
    (hy4v : Fe.Valid y4v)
    (hy4 : decodeFe y4v = mulAd * bMuld - ry)
    (hzOut : zOut = sameX2) :
    (FlaggedPoint.Valid ⟨x4v, y4v, zOut⟩) ∧
      decodePoint (⟨x4v, y4v, zOut⟩ : FlaggedPoint (F circomPrime)) =
        add curve (.affine ⟨xS, yS⟩) (.affine ⟨rx, ry⟩) := by
  have h2ry : ry + ry ≠ 0 := two_y_ne_zero (P := ⟨rx, ry⟩) ((CompleteAdd.onCurve_iff _).mpr hRon)
  by_cases hxsr : xS = rx
  · -- S = −R: the flag fires and the sum is 𝒪
    have hsx : sameX2 = 1 := by rw [hsameX2, if_pos hxsr]
    have hz1 : zOut = 1 := by rw [hzOut, hsx]
    have hySr : yS = -ry := by rw [hyS, hxsr]; ring
    refine ⟨⟨Or.inr hz1, hx4v, hy4v,
      fun h0 => absurd (hz1.symm.trans h0) one_ne_zero⟩, ?_⟩
    rw [decodePoint_of_isInf hz1, add_affine, if_pos hxsr, if_pos (by rw [hySr])]
  · -- proper chord (S, R)
    have hsx : sameX2 = 0 := by rw [hsameX2, if_neg hxsr]
    have hz0 : zOut = 0 := by rw [hzOut, hsx]
    have hden2' : den2d = xS - rx := by
      rw [hden2, if_neg (by rw [hsx]; exact zero_ne_one)]
    have hdne : den2d ≠ 0 := by rw [hden2']; exact sub_ne_zero.mpr hxsr
    have hw' : wd * (xS - rx) = ry + ry := by rw [← hden2']; exact hw hdne
    have hrxS : rx - xS ≠ 0 := sub_ne_zero.mpr (fun h => hxsr h.symm)
    -- the chord slope of (S, R) is −(λ₁ + w)
    have hslope : (ry - yS) / (rx - xS) = -(lam1d + wd) := by
      rw [div_eq_iff hrxS]
      linear_combination -hyS - hw'
    refine ⟨⟨Or.inl hz0, hx4v, hy4v, fun _ => ?_⟩, ?_⟩
    · -- curve membership via `chord_oncurve` with s = −(λ₁+w)
      rw [CompleteAdd.onCurve_iff]
      exact chord_oncurve (x₁ := xS) (y₁ := yS) (x₂ := rx) (y₂ := ry)
        (s := -(lam1d + wd)) hSon hRon
        (by rw [sub_ne_zero]; exact fun h => hxsr h.symm)
        (by linear_combination hyS + hw')
        (by rw [hx4, hmulA]; ring)
        (by rw [hy4, hbMul, hmulA]; linear_combination hyS + hw')
    · rw [hz0, decodePoint_mk_zero, add_affine, if_neg hxsr, chord_eq]
      have hx4' : decodeFe x4v = ((ry - yS) / (rx - xS)) ^ 2 - xS - rx := by
        rw [hslope, hx4, hmulA]; ring
      refine congrArg _ ?_
      have hy4' : decodeFe y4v
          = (ry - yS) / (rx - xS) * (xS - (((ry - yS) / (rx - xS)) ^ 2 - xS - rx)) - yS := by
        rw [← hx4', hslope, hy4, hbMul, hmulA]
        linear_combination hyS + hw'
      rw [Point.mk.injEq]
      exact ⟨hx4', hy4'⟩

/--
The value-level soundness core for the fused ELM double-add: the circuit's
flag/mux structure computes `(R + R) + T` under the complete group law.
-/
theorem fused_soundness_core
    {R T out : FlaggedPoint (F circomPrime)}
    {xSv x4v y4v : Emu (F circomPrime)}
    {lam1d wd den1d den2d xSed mulAd bMuld : Fp}
    {sameX1 sel1 sameX2 tsel cancel cancelG : F circomPrime}
    (hR : R.Valid) (hT : T.Valid)
    (hsameX1 : sameX1 = if decodeFe T.x = decodeFe R.x then 1 else 0)
    (hsel1 : sel1 = sameX1 + T.isInf - sameX1 * T.isInf)
    (hden1 : den1d = if sel1 = 1 then decodeFe R.y + decodeFe R.y
      else decodeFe T.x - decodeFe R.x)
    (hlam1 : den1d ≠ 0 → lam1d * den1d =
      (if sel1 = 1 then 3 * (decodeFe R.x * decodeFe R.x)
       else decodeFe T.y - decodeFe R.y))
    (hxS : decodeFe xSv = lam1d * lam1d - decodeFe R.x - decodeFe T.x)
    (hxSe : xSed = if T.isInf = 1 then decodeFe R.x else decodeFe xSv)
    (hsameX2 : sameX2 = if xSed = decodeFe R.x then 1 else 0)
    (htsel : tsel = T.isInf + sameX2 - T.isInf * sameX2)
    (hden2 : den2d = if tsel = 1 then -1
      else xSed - decodeFe R.x)
    (hw : den2d ≠ 0 → wd * den2d =
      (if T.isInf = 1 then lam1d + lam1d else decodeFe R.y + decodeFe R.y))
    (hmulA : mulAd = lam1d + wd)
    (hx4v : Fe.Valid x4v)
    (hx4 : decodeFe x4v = mulAd * mulAd - xSed - decodeFe R.x)
    (hbMul : bMuld = decodeFe x4v - decodeFe R.x)
    (hy4v : Fe.Valid y4v)
    (hy4 : decodeFe y4v = mulAd * bMuld - decodeFe R.y)
    (hcancel : cancel = if sameX1 = 1 then
      if R.y[0] = T.y[0] then 0 else 1
      else 0)
    (hTcanon : T.isInf = 1 → decodeFe T.x = 0)
    (hcancelG : cancelG = cancel * (1 + -R.isInf))
    (houtx : out.x = if R.isInf + cancelG = 1 then T.x else x4v)
    (houty : out.y = if R.isInf = 1 then T.y else (if cancel = 1 then R.y else y4v))
    (houti : out.isInf =
      R.isInf * T.isInf + (1 - R.isInf - cancelG) * (tsel - T.isInf)) :
    out.Valid ∧
      decodePoint out =
        add curve (add curve (decodePoint R) (decodePoint R)) (decodePoint T) := by
  set zOut : F circomPrime := tsel - T.isInf with hzOutDef
  have hzOut : zOut = sameX2 * (1 - T.isInf) := by rw [hzOutDef, htsel]; ring
  rcases hR.1 with hRinf | hRinf
  case inr =>
    -- R = 𝒪: out = T, and (𝒪 + 𝒪) + T = T
    have hcg : cancelG = 0 := by rw [hcancelG, hRinf]; ring
    have hE : out = T := by
      refine fp_ext ?_ ?_ ?_
      · rw [houtx, hRinf, hcg, if_pos (by ring)]
      · rw [houty, if_pos hRinf]
      · rw [houti, hRinf, hcg]; ring
    rw [hE, decodePoint_of_isInf hRinf, add_inf_left, add_inf_left]
    exact ⟨hT, rfl⟩
  -- R finite
  have hcg : cancelG = cancel := by rw [hcancelG, hRinf]; ring
  have hne01 : ¬((0 : F circomPrime) + 0 = 1) := fun h =>
    zero_ne_one (α := F circomPrime) (by linear_combination h)
  have hgen : cancel = 0 → out = ⟨x4v, y4v, zOut⟩ := by
    intro hc
    refine fp_ext ?_ ?_ ?_
    · rw [houtx, hRinf, hcg, hc, if_neg hne01]
    · rw [houty, if_neg (by rw [hRinf]; exact zero_ne_one),
        if_neg (by rw [hc]; exact zero_ne_one)]
    · rw [houti, hRinf, hcg, hc]; ring
  have hcanx : cancel = 1 → out.x = T.x := fun hc => by
    rw [houtx, hRinf, hcg, hc, if_pos (by ring)]
  have hcany : cancel = 1 → out.y = R.y := fun hc => by
    rw [houty, if_neg (by rw [hRinf]; exact zero_ne_one), if_pos hc]
  have hcani : cancel = 1 → out.isInf = 0 := fun hc => by
    rw [houti, hRinf, hcg, hc]; ring
  set rx := decodeFe R.x with hrx
  set ry := decodeFe R.y with hry
  have hRon : ry ^ 2 = rx ^ 3 + 7 := (CompleteAdd.onCurve_iff _).mp (hR.2.2.2 hRinf)
  have h2ry : ry + ry ≠ 0 := two_y_ne_zero (P := ⟨rx, ry⟩) ((CompleteAdd.onCurve_iff _).mpr hRon)
  have hdpR : decodePoint R = .affine ⟨rx, ry⟩ := decodePoint_of_finite hRinf
  rcases hT.1 with hTinf | hTinf
  · -- T finite: the main chain
    set tx := decodeFe T.x with htx
    set ty := decodeFe T.y with hty
    have hTon : ty ^ 2 = tx ^ 3 + 7 := (CompleteAdd.onCurve_iff _).mp (hT.2.2.2 hTinf)
    have hdpT : decodePoint T = .affine ⟨tx, ty⟩ := decodePoint_of_finite hTinf
    have hTi0 : T.isInf ≠ 1 := by rw [hTinf]; exact zero_ne_one
    have hxSe' : xSed = decodeFe xSv := by rw [hxSe, if_neg hTi0]
    have htsel' : tsel = sameX2 := by rw [htsel, hTinf]; ring
    have hzOut' : zOut = sameX2 := by rw [hzOut, hTinf]; ring
    have hmulA' : mulAd = lam1d + wd := hmulA
    have hbMul' : bMuld = decodeFe x4v - rx := hbMul
    have hden2' : den2d = if sameX2 = 1 then -1 else decodeFe xSv - rx := by
      rw [hden2, htsel', hxSe']
    have hw' : den2d ≠ 0 → wd * den2d = ry + ry := fun h => by
      rw [hw h, if_neg hTi0]
    have hsameX2' : sameX2 = if decodeFe xSv = rx then 1 else 0 := by
      rw [hsameX2, hxSe']
    have hx4' : decodeFe x4v = mulAd * mulAd - decodeFe xSv - rx := by
      rw [hx4, hxSe']
    by_cases hxx : tx = rx
    · -- stage 1 is the tangent: T = R or T = −R
      have hsx1 : sameX1 = 1 := by rw [hsameX1, if_pos hxx]
      have hs1 : sel1 = 1 := by rw [hsel1, hsx1, hTinf]; ring
      have hden1' : den1d = ry + ry := by rw [hden1, if_pos hs1]
      have hlam1t : lam1d * (ry + ry) = 3 * (rx * rx) := by
        have h := hlam1 (by rw [hden1']; exact h2ry)
        rw [hden1', if_pos hs1] at h
        exact h
      have hty2 : ty ^ 2 = ry ^ 2 := by rw [hTon, hRon, hxx]
      by_cases hyy : ry + ty = 0
      · -- T = −R: cancellation, out = R
        have hneY : ry ≠ ty := by
          intro heq
          apply h2ry
          simpa only [← heq] using hyy
        have hlow : R.y[0] ≠ T.y[0] := by
          intro heq
          have hfull := (low_y_eq_iff_of_same_x hR hT hRinf hTinf hxx).mp heq
          exact hneY hfull
        have hc : cancel = 1 := by simp [hcancel, hsx1, hlow]
        have hox := hcanx hc
        have hoy := hcany hc
        have hoi := hcani hc
        have hoxd : decodeFe out.x = rx := by rw [hox, ← htx]; exact hxx
        have hoyd : decodeFe out.y = ry := by rw [hoy, ← hry]
        refine ⟨⟨Or.inl hoi, by rw [hox]; exact hT.2.1, by rw [hoy]; exact hR.2.2.1,
          fun _ => ?_⟩, ?_⟩
        · rw [CompleteAdd.onCurve_iff]
          show decodeFe out.y ^ 2 = decodeFe out.x ^ 3 + 7
          rw [hoxd, hoyd]; exact hRon
        rw [decodePoint_of_finite hoi, hoxd, hoyd, ← hdpR]
        have htyv : ty = -ry := by linear_combination hyy
        have hbmk := toSpec_mk ⟨rx, ry⟩ ((CompleteAdd.onCurve_iff _).mpr hRon)
        have hTmk : decodePoint T =
            Bridge.toSpec (-(Bridge.mkPoint ⟨rx, ry⟩ ((CompleteAdd.onCurve_iff _).mpr hRon))) := by
          rw [hdpT, toSpec_neg_mk]
          exact congrArg _ (by rw [Point.mk.injEq]; exact ⟨hxx, htyv⟩)
        rw [hdpR, hTmk, ← hbmk, add_dbl_neg, hbmk]
      · -- T = R: the chain computes (2R) + R = 2R + T
        have hty' : ty = ry := by
          rcases eq_or_eq_neg_of_sq_eq hty2 with h | h
          · exact h
          · exact absurd (by rw [h]; ring : ry + ty = 0) hyy
        have hlow : R.y[0] = T.y[0] :=
          (low_y_eq_iff_of_same_x hR hT hRinf hTinf hxx).mpr hty'.symm
        have hc : cancel = 0 := by simp [hcancel, hsx1, hlow]
        have hm2' : out = ⟨x4v, y4v, zOut⟩ := hgen hc
        -- the intermediate S is the tangent double of R
        set yS : Fp := lam1d * (rx - decodeFe xSv) - ry with hyS
        have hxSd : decodeFe xSv = lam1d * lam1d - rx - rx := by
          rw [hxS, hxx]
        have hSon : yS ^ 2 = decodeFe xSv ^ 3 + 7 :=
          tangent_oncurve hRon (by linear_combination hlam1t) (by rw [hxSd]) rfl
        obtain ⟨hval, heq⟩ := stage2_core hRon hSon hyS.symm hsameX2' hden2' hw'
          hmulA' hx4v hx4' hbMul' hy4v hy4 hzOut'
        rw [hm2']
        refine ⟨hval, ?_⟩
        rw [heq, hdpR, hdpT]
        -- add (affine R) (affine R) = affine S
        have hdbl : add curve (.affine ⟨rx, ry⟩) (.affine ⟨rx, ry⟩)
            = .affine ⟨decodeFe xSv, yS⟩ := by
          rw [add_self_eq_tangent ⟨rx, ry⟩ ((CompleteAdd.onCurve_iff _).mpr hRon), tangent_eq]
          refine congrArg _ ?_
          have hlam1v : lam1d = 3 * rx ^ 2 / (2 * ry) := by
            rw [eq_div_iff (by intro h; exact h2ry (by linear_combination h))]
            linear_combination hlam1t
          rw [Point.mk.injEq]
          constructor
          · rw [hxSd, hlam1v]; ring
          · rw [hyS, hxSd, hlam1v]; ring
        rw [hdbl, show (⟨tx, ty⟩ : Point Fp) = ⟨rx, ry⟩ from by
          rw [Point.mk.injEq]; exact ⟨hxx, hty'⟩]
    · -- generic chord stage 1: S = R + T
      have hsx1 : sameX1 = 0 := by rw [hsameX1, if_neg hxx]
      have hs1 : sel1 = 0 := by rw [hsel1, hsx1, hTinf]; ring
      have hden1' : den1d = tx - rx := by
        rw [hden1, if_neg (by rw [hs1]; exact zero_ne_one)]
      have hdne1 : den1d ≠ 0 := by
        rw [hden1']; exact sub_ne_zero.mpr hxx
      have hlam1c : lam1d * (tx - rx) = ty - ry := by
        have h := hlam1 hdne1
        rw [hden1', if_neg (by rw [hs1]; exact zero_ne_one)] at h
        exact h
      have hc : cancel = 0 := by simp [hcancel, hsx1]
      have hm2' : out = ⟨x4v, y4v, zOut⟩ := hgen hc
      set yS : Fp := lam1d * (rx - decodeFe xSv) - ry with hyS
      have hSon : yS ^ 2 = decodeFe xSv ^ 3 + 7 :=
        chord_oncurve (s := lam1d) hRon hTon (sub_ne_zero.mpr hxx) hlam1c
          (by rw [hxS]) rfl
      obtain ⟨hval, heq⟩ := stage2_core hRon hSon hyS.symm hsameX2' hden2' hw'
        hmulA' hx4v hx4' hbMul' hy4v hy4 hzOut'
      rw [hm2']
      refine ⟨hval, ?_⟩
      rw [heq, hdpR, hdpT]
      -- affine S = add (affine R) (affine T), then rotate the association
      have hS : (.affine ⟨decodeFe xSv, yS⟩ : GroupPoint Fp)
          = add curve (.affine ⟨rx, ry⟩) (.affine ⟨tx, ty⟩) := by
        rw [add_affine, if_neg (fun h => hxx h.symm), chord_eq]
        refine congrArg _ ?_
        have hslope1 : (ty - ry) / (tx - rx) = lam1d :=
          (div_eq_iff (sub_ne_zero.mpr hxx)).mpr hlam1c.symm
        rw [Point.mk.injEq, hslope1]
        exact ⟨by rw [hxS]; ring, by rw [hyS, hxS]; ring⟩
      rw [hS, add_rot' _ _ (by exact hR.2.2.2 hRinf) (by exact hT.2.2.2 hTinf)]
  · -- T = 𝒪: the chain degenerates to the tangent doubling of R
    have hdpT : decodePoint T = .infinity := decodePoint_of_isInf hTinf
    have hxSe' : xSed = rx := by rw [hxSe, if_pos hTinf]
    have hsx2 : sameX2 = 1 := by rw [hsameX2, if_pos hxSe']
    have htsel' : tsel = 1 := by rw [htsel, hTinf, hsx2]; ring
    have hden2' : den2d = -1 := by rw [hden2, if_pos htsel']
    have hs1 : sel1 = 1 := by rw [hsel1, hTinf]; ring
    have hden1' : den1d = ry + ry := by rw [hden1, if_pos hs1]
    have hwt : lam1d * (ry + ry) = 3 * (rx * rx) := by
      have h := hlam1 (by rw [hden1']; exact h2ry)
      rw [hden1', if_pos hs1] at h
      exact h
    have hw0 : wd = -(lam1d + lam1d) := by
      have h := hw (by rw [hden2']; exact neg_ne_zero.mpr one_ne_zero)
      rw [hden2', if_pos hTinf] at h
      linear_combination -h
    have hmulA' : mulAd = -lam1d := by rw [hmulA, hw0]; ring
    have hbMul' : bMuld = decodeFe x4v - rx := hbMul
    have hzo : zOut = 0 := by rw [hzOut, hTinf, hsx2]; ring
    have hTx0 : decodeFe T.x = 0 := hTcanon hTinf
    have hRxne : rx ≠ 0 :=
      OrderFactsCerts.noXZero_secp (P := ⟨rx, ry⟩) ((CompleteAdd.onCurve_iff _).mpr hRon)
    have htxne : decodeFe T.x ≠ rx := by
      rw [hTx0]
      exact fun h => hRxne h.symm
    have hsx1 : sameX1 = 0 := by rw [hsameX1, hrx, if_neg htxne]
    have hc : cancel = 0 := by simp [hcancel, hsx1]
    have hm2' : out = ⟨x4v, y4v, zOut⟩ := hgen hc
    have hx4t : decodeFe x4v = lam1d * lam1d - rx - rx := by
      rw [hx4, hmulA', hxSe']; ring
    have hy4t : decodeFe y4v = lam1d * (rx - decodeFe x4v) - ry := by
      rw [hy4, hmulA', hbMul']; ring
    rw [hm2']
    constructor
    · exact ⟨Or.inl hzo, hx4v, hy4v, fun _ => by
        rw [CompleteAdd.onCurve_iff]
        exact tangent_oncurve hRon (by linear_combination hwt) (by rw [hx4t]) hy4t⟩
    · rw [hdpT, hdpR, add_self_eq_tangent ⟨rx, ry⟩ ((CompleteAdd.onCurve_iff _).mpr hRon),
        add_inf_right, hzo, decodePoint_mk_zero, tangent_eq]
      refine congrArg _ ?_
      have hwv : lam1d = 3 * rx ^ 2 / (2 * ry) := by
        rw [eq_div_iff (by intro h; exact h2ry (by linear_combination h))]
        linear_combination hwt
      rw [Point.mk.injEq]
      exact ⟨by rw [hx4t, hwv]; ring, by rw [hy4t, hx4t, hwv]; ring⟩

end FusedStepTheorems
end Solution.Secp256k1ScalarMul
