import Solution.Secp256k1ScalarMul.Lazy.StepSpec

/-!
# Value-level correctness of one chain step

Everything the step circuit certifies, stated on plain values, implies the
step specification.  The circuit soundness proof only has to instantiate this.
-/

namespace Solution.Secp256k1ScalarMulFixedBase.LazyVar.Step

open SmallSquare Sparse32 SparseX
open Solution.Secp256k1ScalarMul.Lazy
open Solution.Secp256k1ScalarMulFixedBase.LazyVar
open Specs.ShortWeierstrass Specs.Secp256k1
open Solution.Secp256k1ScalarMul.FusedStepTheorems

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! ### Boolean helpers -/

lemma isBool_of_mul (c : Field) (h : c * (1 - c) = 0) : IsBool c := by
  rcases mul_eq_zero.mp h with h | h
  · exact Or.inl h
  · exact Or.inr (by linear_combination -h)

lemma isBool_mul' (a b : Field) (ha : IsBool a) (hb : IsBool b) : IsBool (a * b) := by
  rcases ha with h | h <;> rcases hb with h' | h' <;> simp [IsBool, h, h']

lemma isBool_or' (z r : Field) (hz : IsBool z) (hr : IsBool r) : IsBool (z + r - z * r) := by
  rcases hz with h | h <;> rcases hr with h' | h' <;> simp [IsBool, h, h']

/-! ### Casting the output vectors -/

section Casts
variable (a b ax ay : fields 8 Field) (tx ty : Emu Field) (p : Products.Outputs Field)
  (hp : Products.Spec ⟨a, b, ax, ay, tx, ty⟩ p)
include hp

lemma sa_cast (k : Fin 8) : p.sa[k.val] = ((sparseSquare (digitsZ a) k : ℤ) : Field) := by
  rw [hp.2.2.2.2.2.1]; exact Certs.sqVec_cast _ (digitsZ a) (digitsZ_cast a) k

lemma sb_cast (k : Fin 8) : p.sb[k.val] = ((sparseSquare (digitsZ b) k : ℤ) : Field) := by
  rw [hp.2.2.2.2.2.2.2.1]; exact Certs.sqVec_cast _ (digitsZ b) (digitsZ_cast b) k

lemma xP_cast (k : Fin 8) :
    (Products.vadd (Products.vsub p.sb p.sa) (embedVec tx))[k.val] =
      ((xPZ (digitsZ a) (digitsZ b) (emuz tx) k : ℤ) : Field) := by
  simp only [xPZ]
  exact Certs.vadd_cast _ _ (fun j => sparseSquare (digitsZ b) j - sparseSquare (digitsZ a) j)
    (embed (emuz tx)) (Certs.vsub_cast _ _ _ _ (sb_cast a b ax ay tx ty p hp) (sa_cast a b ax ay tx ty p hp))
    (embedVec_cast tx) k

lemma pb_cast (k : Fin 8) :
    p.pb[k.val] = ((sparseMul (digitsZ b)
      (fun j => zwords ax j - xPZ (digitsZ a) (digitsZ b) (emuz tx) j) k : ℤ) : Field) := by
  rw [hp.2.2.2.2.2.2.2.2]
  refine Certs.mulVec_cast _ _ _ _ (digitsZ_cast b) ?_ k
  intro j
  simp only [Products.xPVal]
  exact Certs.vsub_cast _ _ (zwords ax) _ (zwords_cast ax) (xP_cast a b ax ay tx ty p hp) j

lemma yP_cast (k : Fin 8) :
    (Products.vsub p.pb ay)[k.val] =
      ((yPZ (digitsZ a) (digitsZ b) (zwords ax) (zwords ay) (emuz tx) k : ℤ) : Field) := by
  simp only [yPZ]
  exact Certs.vsub_cast _ _ _ (zwords ay) (pb_cast a b ax ay tx ty p hp) (zwords_cast ay) k

end Casts

lemma zwords_zero (zv : fields 8 Field) (hzv : ∀ k : Fin 8, zv[k.val] = 0) :
    zwords zv = fun _ => 0 := by
  funext k
  simp only [zwords, hzv k]
  have := LazyX.lift_cast 0 (by norm_num [LazyX.nativeHalf])
  rwa [Int.cast_zero] at this

lemma digits_of_rep (lam : Emu Field) (a : fields 8 Field) (ha : SlopeRep lam a) :
    Digits (digitsZ a) := by
  intro i
  rw [ha.digitsZ_eq]
  have := digitZ_bounds lam i
  omega

lemma valZ_embedVec (t : Emu Field) (ht : BigInt.Normalized 64 t) :
    valZ (zwords (embedVec t)) = decodeFe t := by
  rw [embed_zwords t ht, valZ_embed]

/-! ### The step lemma -/

theorem step_values (n : ℕ) (hn : n + 1 ≤ depth)
    (ax ay : fields 8 Field) (aInf : Field) (tx ty : Emu Field) (tInf sp : Field)
    (lam1 lam2 : Emu Field) (a b : fields 8 Field) (c z g rt zrt zOut : Field)
    (p : Products.Outputs Field) (zv xw xv xo yw yv yo : fields 8 Field)
    (hA : Assumptions n ⟨⟨ax, ay, aInf⟩, ⟨tx, ty, tInf⟩, sp⟩)
    (ha : SlopeRep lam1 a) (hb : SlopeRep lam2 b)
    (hc : c * (1 - c) = 0) (hz : z * (1 - z) = 0) (hcz : c * z = 0)
    (hic : aInf * c = 0) (hiz : aInf * z = 0)
    (hspt : (1 - sp) * tInf = 0)
    (hg : g = (1 - sp) * (1 - aInf))
    (hp : Products.Spec ⟨a, b, ax, ay, tx, ty⟩ p)
    (hcert : Certs.Assumptions n ⟨a, b, ax, ay, tx, ty, p, g, c, z⟩ →
      Certs.Spec ⟨a, b, ax, ay, tx, ty, p, g, c, z⟩)
    (hrt : rt = aInf * tInf) (hzrt : zrt = z * rt) (hzo : zOut = z + rt - zrt)
    (hzv : ∀ k : Fin 8, zv[k.val] = 0)
    (hxw : IsBool c → xw = if c = 1 then ax else Products.vadd (Products.vsub p.sb p.sa) (embedVec tx))
    (hxv : IsBool aInf → xv = if aInf = 1 then embedVec tx else xw)
    (hxo : IsBool zOut → xo = if zOut = 1 then zv else xv)
    (hyw : IsBool c → yw = if c = 1 then ay else Products.vsub p.pb ay)
    (hyv : IsBool aInf → yv = if aInf = 1 then embedVec ty else yw)
    (hyo : IsBool zOut → yo = if zOut = 1 then zv else yv) :
    Spec n ⟨⟨ax, ay, aInf⟩, ⟨tx, ty, tInf⟩, sp⟩ ⟨xo, yo, zOut⟩ := by
  simp only [Assumptions, LazyValid, OnCurveLazy, TValid] at hA
  obtain ⟨⟨hIb, hX, hY⟩, hOC, ⟨hTb, hTx, hTy, hTC⟩, hSp⟩ := hA
  have hcB : IsBool c := isBool_of_mul c hc
  have hzB : IsBool z := isBool_of_mul z hz
  have hrtB : IsBool rt := by rw [hrt]; exact isBool_mul' _ _ hIb hTb
  have hzoB : IsBool zOut := by rw [hzo, hzrt]; exact isBool_or' _ _ hzB hrtB
  have hDa : Digits (digitsZ a) := digits_of_rep lam1 a ha
  have hDb : Digits (digitsZ b) := digits_of_rep lam2 b hb
  have hCx : Canon (emuz tx) := emuz_bounds tx hTx
  have hCy : Canon (emuz ty) := emuz_bounds ty hTy
  have hxPz : zwords (Products.vadd (Products.vsub p.sb p.sa) (embedVec tx)) =
      xPZ (digitsZ a) (digitsZ b) (emuz tx) :=
    zwords_of_cast _ _ (xP_cast a b ax ay tx ty p hp)
      (fun k => xIn_native (xP_bounds hDa hDb hCx) k)
  have hyPz : zwords (Products.vsub p.pb ay) =
      yPZ (digitsZ a) (digitsZ b) (zwords ax) (zwords ay) (emuz tx) :=
    zwords_of_cast _ _ (yP_cast a b ax ay tx ty p hp)
      (fun k => yIn_native hn (yP_bounds hDa hDb hX hY hCx) k)
  have hzvz := zwords_zero zv hzv
  have hxo' := hxo hzoB
  have hyo' := hyo hzoB
  have hxv' := hxv hIb
  have hyv' := hyv hIb
  have hxw' := hxw hcB
  have hyw' := hyw hcB
  refine ⟨⟨hzoB, ?_, ?_⟩, ?_⟩
  · -- XIn of the output x
    show XIn (zwords xo)
    rw [hxo']
    split_ifs with h0
    · rw [hzvz]; exact xIn_zero
    rw [hxv']
    split_ifs with h1
    · rw [embed_zwords tx hTx]; exact xIn_embed hCx
    rw [hxw']
    split_ifs with h2
    · exact hX
    rw [hxPz]; exact xP_bounds hDa hDb hCx
  · -- YIn of the output y
    show YIn (n + 1) (zwords yo)
    rw [hyo']
    split_ifs with h0
    · rw [hzvz]; exact yIn_zero _
    rw [hyv']
    split_ifs with h1
    · rw [embed_zwords ty hTy]; exact yIn_embed hCy _
    rw [hyw']
    split_ifs with h2
    · exact yIn_succ_of hY
    rw [hyPz]; exact yP_bounds hDa hDb hX hY hCx
  · -- the group law
    intro hsp0
    replace hsp0 : sp = 0 := hsp0
    have htInf : tInf = 0 := by rw [hsp0] at hspt; simpa using hspt
    have hT : decodeFe ty ^ 2 = decodeFe tx ^ 3 + 7 := hTC htInf
    have hrt0 : rt = 0 := by rw [hrt, htInf, mul_zero]
    have hzo' : zOut = z := by rw [hzo, hzrt, hrt0]; ring
    have hdT : decodeT ⟨tx, ty, tInf⟩ = .affine ⟨decodeFe tx, decodeFe ty⟩ := by
      simp only [decodeT, htInf, zero_ne_one, ↓reduceIte]
    refine ⟨htInf, ?_⟩
    rcases hIb with hI0 | hI1
    · -- R is affine
      have hg1 : g = 1 := by rw [hg, hsp0, hI0]; ring
      have hR : valZ (zwords ay) ^ 2 = valZ (zwords ax) ^ 3 + 7 := hOC hI0
      have hdR : decodeL ⟨ax, ay, aInf⟩ = .affine ⟨valZ (zwords ax), valZ (zwords ay)⟩ := by
        simp only [decodeL, hI0, zero_ne_one, ↓reduceIte]
      have hspec := hcert ⟨by rw [hg1]; exact Or.inr rfl, hcB, hzB, hcz,
        fun _ => ⟨hDa, hDb, hX, hY, hTx, hTy, hp⟩⟩ hg1
      simp only [Certs.aF, Certs.bF, Certs.rx, Certs.ry, Certs.tX, Certs.tY, Certs.xS] at hspec
      have hI0' : ¬ aInf = 1 := by rw [hI0]; exact zero_ne_one
      rw [hxv', if_neg hI0'] at hxo'
      rw [hyv', if_neg hI0'] at hyo'
      rw [hdR, hdT]
      rcases hcB with hc0 | hc1
      · -- generic first addition
        obtain ⟨hchord, huni⟩ := hspec.1 hc0
        have hfa := StepMath.first_add (aF := valZ (digitsZ a)) hR hT
          (by linear_combination hchord) (by linear_combination huni)
        have hc0' : ¬ c = 1 := by rw [hc0]; exact zero_ne_one
        rw [hxw', if_neg hc0'] at hxo'
        rw [hyw', if_neg hc0'] at hyo'
        rcases hzB with hz0 | hz1
        · -- generic second addition
          have hrel2 := hspec.2.2.2 hc0 hz0
          have h2ry : valZ (zwords ay) + valZ (zwords ay) ≠ 0 :=
            two_y_ne_zero (P := ⟨valZ (zwords ax), valZ (zwords ay)⟩)
              ((Solution.Secp256k1ScalarMul.CompleteAdd.onCurve_iff _).mpr hR)
          have hne : valZ (digitsZ a) * valZ (digitsZ a) - valZ (zwords ax) - decodeFe tx ≠
              valZ (zwords ax) := by
            intro h
            apply h2ry
            rw [h] at hrel2
            linear_combination -hrel2
          have hsa := StepMath.second_add (bF := valZ (digitsZ b)) hR hT hfa.1 hfa.2 rfl hne
            (by linear_combination hrel2)
          have hzo0 : zOut = 0 := by rw [hzo', hz0]
          have hzo0' : ¬ zOut = 1 := by rw [hzo0]; exact zero_ne_one
          rw [if_neg hzo0'] at hxo' hyo'
          have e1 : valZ (xPZ (digitsZ a) (digitsZ b) (emuz tx)) =
              valZ (digitsZ b) * valZ (digitsZ b) -
                (valZ (digitsZ a) * valZ (digitsZ a) - valZ (zwords ax) - decodeFe tx) -
                valZ (zwords ax) := by
            rw [xPZ_value]; ring
          have e2 : valZ (yPZ (digitsZ a) (digitsZ b) (zwords ax) (zwords ay) (emuz tx)) =
              valZ (digitsZ b) * (valZ (zwords ax) -
                (valZ (digitsZ b) * valZ (digitsZ b) -
                  (valZ (digitsZ a) * valZ (digitsZ a) - valZ (zwords ax) - decodeFe tx) -
                  valZ (zwords ax))) - valZ (zwords ay) := by
            rw [yPZ_value, e1]
          refine ⟨fun _ => ?_, ?_⟩
          · show valZ (zwords yo) ^ 2 = valZ (zwords xo) ^ 3 + 7
            rw [hxo', hyo', hxPz, hyPz, e1, e2]
            exact hsa.1
          · simp only [decodeL, hzo0, zero_ne_one, ↓reduceIte]
            rw [hxo', hyo', hxPz, hyPz, e1, e2]
            exact hsa.2.symm
        · -- S = −R: the result is 𝒪
          have hxs := hspec.2.2.1 hz1
          have hzo1 : zOut = 1 := by rw [hzo', hz1]
          have hxS : valZ (digitsZ a) * valZ (digitsZ a) - valZ (zwords ax) - decodeFe tx =
              valZ (zwords ax) := by linear_combination hxs
          refine ⟨fun h => absurd h (by rw [hzo1]; exact one_ne_zero), ?_⟩
          simp only [decodeL, hzo1, ↓reduceIte]
          exact (StepMath.second_inf hR hT hfa.2 hxS (by rw [hxS]; ring)).symm
      · -- cancellation `T = −R`: the result is `R`
        obtain ⟨hx1, hy1⟩ := hspec.2.1 hc1
        have hz0 : z = 0 := by rw [hc1, one_mul] at hcz; exact hcz
        have hzo0 : zOut = 0 := by rw [hzo', hz0]
        have hzo0' : ¬ zOut = 1 := by rw [hzo0]; exact zero_ne_one
        rw [hxw', if_pos hc1] at hxo'
        rw [hyw', if_pos hc1] at hyo'
        rw [if_neg hzo0'] at hxo' hyo'
        have htx' : decodeFe tx = valZ (zwords ax) := by linear_combination -hx1
        have hty' : decodeFe ty = -valZ (zwords ay) := by linear_combination hy1
        refine ⟨fun _ => ?_, ?_⟩
        · show valZ (zwords yo) ^ 2 = valZ (zwords xo) ^ 3 + 7
          rw [hxo', hyo']; exact hR
        · simp only [decodeL, hzo0, zero_ne_one, ↓reduceIte]
          rw [hxo', hyo', htx', hty']
          exact (StepMath.cancel_core hR).symm
    · -- R = 𝒪: the result is `T`
      have hc0 : c = 0 := by rw [hI1, one_mul] at hic; exact hic
      have hz0 : z = 0 := by rw [hI1, one_mul] at hiz; exact hiz
      have hzo0 : zOut = 0 := by rw [hzo', hz0]
      have hzo0' : ¬ zOut = 1 := by rw [hzo0]; exact zero_ne_one
      rw [hxv', if_pos hI1] at hxo'
      rw [hyv', if_pos hI1] at hyo'
      rw [if_neg hzo0'] at hxo' hyo'
      have hdR : decodeL ⟨ax, ay, aInf⟩ = .infinity := by
        simp only [decodeL, hI1, ↓reduceIte]
      rw [hdR, hdT]
      refine ⟨fun _ => ?_, ?_⟩
      · show valZ (zwords yo) ^ 2 = valZ (zwords xo) ^ 3 + 7
        rw [hxo', hyo', valZ_embedVec tx hTx, valZ_embedVec ty hTy]; exact hT
      · simp only [decodeL, hzo0, zero_ne_one, ↓reduceIte]
        rw [hxo', hyo', valZ_embedVec tx hTx, valZ_embedVec ty hTy]
        rfl

end Solution.Secp256k1ScalarMulFixedBase.LazyVar.Step

/-! ### Completeness on values -/

namespace Solution.Secp256k1ScalarMulFixedBase.LazyVar.Step

open SmallSquare Sparse32 SparseX
open Solution.Secp256k1ScalarMul.Lazy
open Solution.Secp256k1ScalarMulFixedBase.LazyVar
open Specs.ShortWeierstrass Specs.Secp256k1
open Solution.Secp256k1ScalarMul.FusedStepTheorems

set_option autoImplicit false
set_option maxHeartbeats 4000000

lemma valZ_of_rep (s : Fp) (a : fields 8 Field) (ha : SlopeRep (slopeWitness s) a) :
    valZ (digitsZ a) = s := by
  rw [valZ_eq, ha.reconstructFp, slopeWitness_valueFp]

lemma cflagV_bool (i : Inputs Field) : IsBool (cflagV i) := by
  unfold cflagV; split_ifs <;> simp [IsBool]

lemma zflagV_bool (i : Inputs Field) : IsBool (zflagV i) := by
  unfold zflagV; split_ifs <;> simp [IsBool]

/-- All step constraints hold on the honest witnesses. -/
theorem step_complete (n : ℕ) (hn : n + 1 ≤ depth)
    (ax ay : fields 8 Field) (aInf : Field) (tx ty : Emu Field) (tInf sp : Field)
    (a b : fields 8 Field) (c z g : Field) (p : Products.Outputs Field)
    (hA : ProverAssumptions n ⟨⟨ax, ay, aInf⟩, ⟨tx, ty, tInf⟩, sp⟩)
    (ha : SlopeRep (lam1W ⟨⟨ax, ay, aInf⟩, ⟨tx, ty, tInf⟩, sp⟩) a)
    (hb : SlopeRep (lam2W ⟨⟨ax, ay, aInf⟩, ⟨tx, ty, tInf⟩, sp⟩) b)
    (hc : c = cflagV ⟨⟨ax, ay, aInf⟩, ⟨tx, ty, tInf⟩, sp⟩)
    (hz : z = zflagV ⟨⟨ax, ay, aInf⟩, ⟨tx, ty, tInf⟩, sp⟩)
    (hg : g = (1 - sp) * (1 - aInf))
    (hp : Products.Spec ⟨a, b, ax, ay, tx, ty⟩ p) :
    c * (1 - c) = 0 ∧ z * (1 - z) = 0 ∧ c * z = 0 ∧ aInf * c = 0 ∧ aInf * z = 0 ∧
    (1 - sp) * tInf = 0 ∧
    (Certs.Assumptions n ⟨a, b, ax, ay, tx, ty, p, g, c, z⟩ ∧
      Certs.Spec ⟨a, b, ax, ay, tx, ty, p, g, c, z⟩) ∧
    IsBool c ∧ IsBool aInf ∧ IsBool (z + aInf * tInf + -(z * (aInf * tInf))) := by
  simp only [ProverAssumptions, Assumptions, LazyValid, OnCurveLazy, TValid] at hA
  obtain ⟨⟨⟨hIb, hX, hY⟩, hOC, ⟨hTb, hTx, hTy, hTC⟩, hSp⟩, hSpT⟩ := hA
  have hcB : IsBool c := by rw [hc]; exact cflagV_bool _
  have hzB : IsBool z := by rw [hz]; exact zflagV_bool _
  have hDa : Digits (digitsZ a) := digits_of_rep _ a ha
  have hDb : Digits (digitsZ b) := digits_of_rep _ b hb
  have haF : valZ (digitsZ a) = slope1 ⟨⟨ax, ay, aInf⟩, ⟨tx, ty, tInf⟩, sp⟩ := valZ_of_rep _ a ha
  have hbF : valZ (digitsZ b) = slope2 ⟨⟨ax, ay, aInf⟩, ⟨tx, ty, tInf⟩, sp⟩ := valZ_of_rep _ b hb
  -- the flag conditions, with projections reduced
  have hc' : c = if aInf = 0 ∧ valZ (zwords ax) = decodeFe tx ∧ valZ (zwords ay) = -decodeFe ty
      then 1 else 0 := hc
  have hxS : xSV ⟨⟨ax, ay, aInf⟩, ⟨tx, ty, tInf⟩, sp⟩ =
      slope1 ⟨⟨ax, ay, aInf⟩, ⟨tx, ty, tInf⟩, sp⟩ * slope1 ⟨⟨ax, ay, aInf⟩, ⟨tx, ty, tInf⟩, sp⟩ -
        valZ (zwords ax) - decodeFe tx := rfl
  have hz' : z = if aInf = 0 ∧ c = 0 ∧ xSV ⟨⟨ax, ay, aInf⟩, ⟨tx, ty, tInf⟩, sp⟩ = valZ (zwords ax)
      then 1 else 0 := by rw [hz, hc]; rfl
  have hcz : c * z = 0 := by
    rw [hz']
    split_ifs with h
    · rw [h.2.1]; ring
    · ring
  have hic : aInf * c = 0 := by
    rw [hc']
    split_ifs with h
    · rw [h.1]; ring
    · ring
  have hiz : aInf * z = 0 := by
    rw [hz']
    split_ifs with h
    · rw [h.1]; ring
    · ring
  have hspt : (1 - sp) * tInf = 0 := by
    rcases hSp with h | h
    · rw [hSpT h]; ring
    · rw [h]; ring
  have hgB : IsBool g := by
    rw [hg]
    rcases hSp with h | h <;> rcases hIb with h' | h' <;> simp [IsBool, h, h']
  refine ⟨by rcases hcB with h | h <;> rw [h] <;> ring, by rcases hzB with h | h <;> rw [h] <;> ring,
    hcz, hic, hiz, hspt, ⟨⟨hgB, hcB, hzB, hcz, fun _ => ⟨hDa, hDb, hX, hY, hTx, hTy, hp⟩⟩, ?_⟩,
    hcB, hIb, ?_⟩
  · -- the certified relations
    intro hg1
    -- gate = 1 forces sp = 0 and R affine
    have hsp0 : sp = 0 := by
      rcases hSp with h | h
      · exact h
      · exfalso; rw [hg, h] at hg1; simp at hg1
    have hI0 : aInf = 0 := by
      rcases hIb with h | h
      · exact h
      · exfalso; rw [hg, h] at hg1; simp at hg1
    have htInf : tInf = 0 := hSpT hsp0
    have hR := hOC hI0
    have hT := hTC htInf
    have h2ry : valZ (zwords ay) + valZ (zwords ay) ≠ 0 :=
      two_y_ne_zero (P := ⟨valZ (zwords ax), valZ (zwords ay)⟩)
        ((Solution.Secp256k1ScalarMul.CompleteAdd.onCurve_iff _).mpr hR)
    simp only [Certs.Spec, Certs.aF, Certs.bF, Certs.rx, Certs.ry, Certs.tX, Certs.tY, Certs.xS]
    rw [haF, hbF]
    have hs1 : slope1 ⟨⟨ax, ay, aInf⟩, ⟨tx, ty, tInf⟩, sp⟩ =
        if decodeFe tx = valZ (zwords ax) then
          (if decodeFe ty = -valZ (zwords ay) then 0
            else 3 * valZ (zwords ax) ^ 2 / (2 * valZ (zwords ay)))
        else (decodeFe ty - valZ (zwords ay)) / (decodeFe tx - valZ (zwords ax)) := by
      simp only [slope1, rx, ry, tX, tY, hI0, zero_ne_one, ↓reduceIte]
    have hs2 : slope2 ⟨⟨ax, ay, aInf⟩, ⟨tx, ty, tInf⟩, sp⟩ =
        if xSV ⟨⟨ax, ay, aInf⟩, ⟨tx, ty, tInf⟩, sp⟩ = valZ (zwords ax) then 0
        else 2 * valZ (zwords ay) / (valZ (zwords ax) - xSV ⟨⟨ax, ay, aInf⟩, ⟨tx, ty, tInf⟩, sp⟩) -
          slope1 ⟨⟨ax, ay, aInf⟩, ⟨tx, ty, tInf⟩, sp⟩ := rfl
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- c = 0: chord and unified relations
      intro hc0
      rw [hc'] at hc0
      have hnot : ¬ (aInf = 0 ∧ valZ (zwords ax) = decodeFe tx ∧ valZ (zwords ay) = -decodeFe ty) := by
        intro h; rw [if_pos h] at hc0; exact one_ne_zero hc0
      rw [hs1]
      by_cases hx : decodeFe tx = valZ (zwords ax)
      · rw [if_pos hx]
        have hy : ¬ decodeFe ty = -valZ (zwords ay) := by
          intro hy; exact hnot ⟨hI0, hx.symm, by rw [hy]; ring⟩
        rw [if_neg hy]
        -- T = R
        have hyy : decodeFe ty = valZ (zwords ay) := by
          have h0 : (decodeFe ty - valZ (zwords ay)) * (decodeFe ty + valZ (zwords ay)) = 0 := by
            linear_combination hT - hR + (decodeFe tx ^ 2 + decodeFe tx * valZ (zwords ax) +
              valZ (zwords ax) ^ 2) * hx
          rcases mul_eq_zero.mp h0 with h | h
          · linear_combination h
          · exfalso; exact hy (by linear_combination h)
        have h2 : (2 : Fp) * valZ (zwords ay) ≠ 0 := by
          intro h; exact h2ry (by linear_combination h)
        rw [hx, hyy]
        refine ⟨by ring, ?_⟩
        rw [div_mul_eq_mul_div, sub_eq_zero, div_eq_iff h2]
        ring
      · rw [if_neg hx]
        have hne : decodeFe tx - valZ (zwords ax) ≠ 0 := sub_ne_zero.mpr hx
        refine ⟨?_, ?_⟩
        · rw [div_mul_eq_mul_div, mul_div_cancel_right₀ _ hne]; ring
        · rw [div_mul_eq_mul_div, sub_eq_zero, div_eq_iff hne]
          linear_combination hT - hR
    · -- c = 1: T = −R
      intro hc1
      rw [hc'] at hc1
      by_cases h : aInf = 0 ∧ valZ (zwords ax) = decodeFe tx ∧ valZ (zwords ay) = -decodeFe ty
      · exact ⟨by rw [h.2.1]; ring, by rw [h.2.2]; ring⟩
      · rw [if_neg h] at hc1; exact absurd hc1 zero_ne_one
    · -- z = 1: xS = x
      intro hz1
      rw [hz'] at hz1
      by_cases h : aInf = 0 ∧ c = 0 ∧ xSV ⟨⟨ax, ay, aInf⟩, ⟨tx, ty, tInf⟩, sp⟩ = valZ (zwords ax)
      · rw [← hxS, h.2.2]; ring
      · rw [if_neg h] at hz1; exact absurd hz1 zero_ne_one
    · -- c = 0, z = 0: the two-slope identity
      intro hc0 hz0
      rw [hz'] at hz0
      have hne : ¬ xSV ⟨⟨ax, ay, aInf⟩, ⟨tx, ty, tInf⟩, sp⟩ = valZ (zwords ax) := by
        intro h; rw [if_pos ⟨hI0, hc0, h⟩] at hz0; exact one_ne_zero hz0
      rw [← hxS, hs2, if_neg hne]
      have hd : valZ (zwords ax) - xSV ⟨⟨ax, ay, aInf⟩, ⟨tx, ty, tInf⟩, sp⟩ ≠ 0 :=
        sub_ne_zero.mpr (Ne.symm hne)
      rw [show slope1 ⟨⟨ax, ay, aInf⟩, ⟨tx, ty, tInf⟩, sp⟩ +
          (2 * valZ (zwords ay) / (valZ (zwords ax) - xSV ⟨⟨ax, ay, aInf⟩, ⟨tx, ty, tInf⟩, sp⟩) -
            slope1 ⟨⟨ax, ay, aInf⟩, ⟨tx, ty, tInf⟩, sp⟩) =
          2 * valZ (zwords ay) / (valZ (zwords ax) - xSV ⟨⟨ax, ay, aInf⟩, ⟨tx, ty, tInf⟩, sp⟩) by ring,
        div_mul_cancel₀ _ hd]
      ring
  · -- the output flag is boolean
    have hrtB : IsBool (aInf * tInf) := isBool_mul' _ _ hIb hTb
    have := isBool_or' z (aInf * tInf) hzB hrtB
    rwa [sub_eq_add_neg] at this

end Solution.Secp256k1ScalarMulFixedBase.LazyVar.Step
