import Solution.Secp256k1ScalarMul.Lazy.Interval

/-!
# Certificate layouts for the variable-base lazy chain

Mirrors `Sparse32.CertLayout` of the fixed-base record (patchgravity,
d59c8bf7): every lazy value certified `≡ 0 (mod q)` has a fixed integer
envelope, from which the quotient and carry offsets and bit widths follow.
The slots of one chain step `R' = (R + T) + R`:

* `rel1` (two halves): chord relation `a (T.x − x) − T.y + y`, or the
  x-equality `x − T.x` on the cancellation branch `T = −R`;
* `uni` (three limbs, wider): the unified slope relation
  `a (y + T.y) − (x² + x T.x + T.x²)`, which also pins the tangent when
  `T = R`, or the y-equality `y + T.y` on the cancellation branch;
* `xeq` (two halves): `xS − x` on the `S = −R` branch;
* `rel2` (two halves): two-slope identity `(a + b)(x − xS) + 2 y`.

The final assertion reuses `rel1` and `uni`.
-/

namespace Solution.Secp256k1ScalarMul.Lazy

open Solution.Secp256k1ScalarMulFixedBase.Sparse32

set_option autoImplicit false
set_option maxHeartbeats 24000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 1024

/-- Constant envelope of the lazy `x` coordinate (`x' = b² − a² + T.x`, union with
`x`, `T.x` and `0`). -/
def xLo : Words ℤ := wsub (sqLo digLo digHi) (sqHi digLo digHi)
def xHi : Words ℤ := wadd (wsub (sqHi digLo digHi) (sqLo digLo digHi)) embHi

/-- Envelope of the update `b (x − x')`. -/
def yStepLo : Words ℤ := prodLo digLo digHi (wsub xLo xHi) (wsub xHi xLo)
def yStepHi : Words ℤ := prodHi digLo digHi (wsub xLo xHi) (wsub xHi xLo)

/-- Depth-indexed envelope of the lazy `y` coordinate: the seed is canonical, and
each step outputs one of `y' = b (x − x') − y`, `y`, `T.y`, `0`. -/
def yBounds : ℕ → Words ℤ × Words ℤ
  | 0 => (wzero, embHi)
  | n+1 =>
      let p := yBounds n
      (wmin (wmin (wsub yStepLo p.2) p.1) wzero, wmax (wmax (wsub yStepHi p.1) p.2) embHi)

def yLoAt (n : ℕ) : Words ℤ := (yBounds n).1
def yHiAt (n : ℕ) : Words ℤ := (yBounds n).2

abbrev depth : ℕ := 64
def yLo : Words ℤ := yLoAt depth
def yHi : Words ℤ := yHiAt depth

lemma yBounds_step (n : ℕ) (i : Fin 8) :
    yLoAt (n+1) i = min (min (yStepLo i - yHiAt n i) (yLoAt n i)) 0 ∧
    yHiAt (n+1) i = max (max (yStepHi i - yLoAt n i) (yHiAt n i)) (embHi i) := ⟨rfl, rfl⟩

lemma yBounds_mono (n : ℕ) (i : Fin 8) :
    yLoAt (n+1) i ≤ yLoAt n i ∧ yHiAt n i ≤ yHiAt (n+1) i := by
  rw [(yBounds_step n i).1, (yBounds_step n i).2]
  exact ⟨(min_le_left _ _).trans (min_le_right _ _), (le_max_right _ _).trans (le_max_left _ _)⟩

lemma yBounds_le {n m : ℕ} (h : n ≤ m) (i : Fin 8) :
    yLoAt m i ≤ yLoAt n i ∧ yHiAt n i ≤ yHiAt m i := by
  induction h with
  | refl => exact ⟨le_rfl, le_rfl⟩
  | @step m _ ih =>
      have := yBounds_mono m i
      exact ⟨this.1.trans ih.1, ih.2.trans this.2⟩

lemma yBounds_steady {n : ℕ} (hn : n ≤ depth) (i : Fin 8) :
    yLo i ≤ yLoAt n i ∧ yHiAt n i ≤ yHi i := yBounds_le hn i

lemma yBounds_zero_mem (n : ℕ) (i : Fin 8) : yLoAt n i ≤ 0 ∧ 0 ≤ yHiAt n i := by
  cases n with
  | zero => simp [yLoAt, yHiAt, yBounds, wzero, embHi, dcap_nonneg]
  | succ n =>
      rw [(yBounds_step n i).1, (yBounds_step n i).2]
      exact ⟨min_le_right _ _, (dcap_nonneg i).trans (le_max_right _ _)⟩

lemma yBounds_emb_mem (n : ℕ) (i : Fin 8) : yLoAt n i ≤ 0 ∧ embHi i ≤ yHiAt n i := by
  cases n with
  | zero => simp [yLoAt, yHiAt, yBounds, wzero]
  | succ n =>
      rw [(yBounds_step n i).1, (yBounds_step n i).2]
      exact ⟨min_le_right _ _, le_max_right _ _⟩

/-- Envelope of `xS = a² − x − T.x`. -/
def xSLo : Words ℤ := wsub (wsub (sqLo digLo digHi) xHi) embHi
def xSHi : Words ℤ := wsub (wsub (sqHi digLo digHi) xLo) embLo

/-! ### Two-half slot contents -/
def chordLo : Words ℤ := wadd (prodLo digLo digHi (wsub embLo xHi) (wsub embHi xLo)) (wsub yLo embHi)
def chordHi : Words ℤ := wadd (prodHi digLo digHi (wsub embLo xHi) (wsub embHi xLo)) (wsub yHi embLo)
def xeq1Lo : Words ℤ := wsub xLo embHi
def xeq1Hi : Words ℤ := wsub xHi embLo
def rel1Lo : Words ℤ := wmin (wmin chordLo xeq1Lo) wzero
def rel1Hi : Words ℤ := wmax (wmax chordHi xeq1Hi) wzero
def xeqLo : Words ℤ := wmin (wsub xSLo xHi) wzero
def xeqHi : Words ℤ := wmax (wsub xSHi xLo) wzero
def rel2Lo : Words ℤ :=
  wmin (wsub (prodLo dig2Lo dig2Hi (wsub xLo xSHi) (wsub xHi xSLo)) (wscale 2 yHi)) wzero
def rel2Hi : Words ℤ :=
  wmax (wsub (prodHi dig2Lo dig2Hi (wsub xLo xSHi) (wsub xHi xSLo)) (wscale 2 yLo)) wzero

/-! ### Three-limb slot content (unified relation) -/
def uniRawLo : Words ℤ :=
  wsub (wsub (wsub (prodLo digLo digHi (wadd yLo embLo) (wadd yHi embHi)) (sqHi xLo xHi))
    (prodHi xLo xHi embLo embHi)) (sqHi embLo embHi)
def uniRawHi : Words ℤ :=
  wsub (wsub (wsub (prodHi digLo digHi (wadd yLo embLo) (wadd yHi embHi)) (sqLo xLo xHi))
    (prodLo xLo xHi embLo embHi)) (sqLo embLo embHi)
def yeqLo : Words ℤ := wadd yLo embLo
def yeqHi : Words ℤ := wadd yHi embHi
def uniLo : Words ℤ := wmin (wmin uniRawLo yeqLo) wzero
def uniHi : Words ℤ := wmax (wmax uniRawHi yeqHi) wzero
/-- Final equality slot `y − T.y` (gated, or `0`). -/
def finLo : Words ℤ := wmin (wsub yLo embHi) wzero
def finHi : Words ℤ := wmax (wsub yHi embLo) wzero

inductive VarLayout where
  | rel1
  | xeq
  | rel2
  | fin
  deriving DecidableEq

def slotLo : VarLayout → Words ℤ
  | .rel1 => rel1Lo
  | .xeq => xeqLo
  | .rel2 => rel2Lo
  | .fin => finLo

def slotHi : VarLayout → Words ℤ
  | .rel1 => rel1Hi
  | .xeq => xeqHi
  | .rel2 => rel2Hi
  | .fin => finHi

def loMin (l : VarLayout) : ℤ := lowHalf (slotLo l)
def loMax (l : VarLayout) : ℤ := lowHalf (slotHi l)
def hiMin (l : VarLayout) : ℤ := highHalf (slotLo l)
def hiMax (l : VarLayout) : ℤ := highHalf (slotHi l)

def qbits : VarLayout → ℕ
  | .rel1 => 85
  | .xeq => 37
  | .rel2 => 86
  | .fin => 85

def tbits : VarLayout → ℕ
  | .rel1 => 93
  | .xeq => 46
  | .rel2 => 94
  | .fin => 93

def kmin : VarLayout → ℤ
  | .rel1 => -16320115796211931381695261
  | .xeq => -48318383303
  | .rel2 => -33019860973776849567019680
  | .fin => -16193584966913837944492930

def tmin : VarLayout → ℤ
  | .rel1 => -3470244817853828247017939232
  | .xeq => -21118354193453
  | .rel2 => -7020338184441123877755872359
  | .fin => -3443634642430263366552932479

private def kmax (l : VarLayout) : ℤ := kmin l + 2^(qbits l) - 1
private def tmax (l : VarLayout) : ℤ := tmin l + 2^(tbits l) - 1

private lemma honest_parameter_bounds : ∀ l : VarLayout,
    q*(kmin l-1) < loMin l+R*hiMin l ∧
    loMax l+R*hiMax l < q*(kmax l+1) ∧
    kmax l-kmin l < 2^(qbits l) ∧
    R*(tmin l-1) < loMin l-(R-c)*kmax l ∧
    loMax l-(R-c)*kmin l < R*(tmax l+1) ∧
    tmax l-tmin l < 2^(tbits l) := by
  intro l
  cases l <;> decide

lemma certificate_complete (l : VarLayout) (L U k : ℤ)
    (hL : loMin l ≤ L ∧ L ≤ loMax l)
    (hU : hiMin l ≤ U ∧ U ≤ hiMax l)
    (he : L+R*U=q*k) :
    (0 ≤ k-kmin l ∧ k-kmin l < 2^(qbits l)) ∧
    (0 ≤ (R-1)*k-U-tmin l ∧
      (R-1)*k-U-tmin l < 2^(tbits l)) := by
  have hp := honest_parameter_bounds l
  norm_num [q, R, c] at hp he ⊢
  omega

def residualLo (l : VarLayout) (L kr vr : ℤ) : ℤ :=
  L-(R-c)*(kr+kmin l)-R*(vr+tmin l)

def residualHi (l : VarLayout) (U kr vr : ℤ) : ℤ :=
  U-(R-1)*(kr+kmin l)+(vr+tmin l)

private lemma admitted_extrema : ∀ l : VarLayout,
    -(2^240 : ℤ) < loMin l-(R-c)*(kmin l+2^(qbits l)-1)-
        R*(tmin l+2^(tbits l)-1) ∧
    loMax l-(R-c)*kmin l-R*tmin l < 2^240 ∧
    -(2^240 : ℤ) < hiMin l-(R-1)*(kmin l+2^(qbits l)-1)+tmin l ∧
    hiMax l-(R-1)*kmin l+(tmin l+2^(tbits l)-1) < 2^240 := by
  intro l
  cases l <;> decide

lemma certificate_residual_bounds (l : VarLayout) (L U kr vr : ℤ)
    (hL : loMin l ≤ L ∧ L ≤ loMax l)
    (hU : hiMin l ≤ U ∧ U ≤ hiMax l)
    (hk : 0 ≤ kr ∧ kr < 2^(qbits l))
    (hv : 0 ≤ vr ∧ vr < 2^(tbits l)) :
    (-(2^240 : ℤ) < residualLo l L kr vr ∧ residualLo l L kr vr < 2^240) ∧
    (-(2^240 : ℤ) < residualHi l U kr vr ∧ residualHi l U kr vr < 2^240) := by
  have he := admitted_extrema l
  simp only [residualLo, residualHi]
  norm_num [R, c] at he ⊢
  omega

lemma certificate_no_wrap (l : VarLayout) (L U kr vr : ℤ)
    (hL : loMin l ≤ L ∧ L ≤ loMax l)
    (hU : hiMin l ≤ U ∧ U ≤ hiMax l)
    (hk : 0 ≤ kr ∧ kr < 2^(qbits l))
    (hv : 0 ≤ vr ∧ vr < 2^(tbits l)) :
    (-(nativePrime : ℤ) < residualLo l L kr vr ∧
      residualLo l L kr vr < nativePrime) ∧
    (-(nativePrime : ℤ) < residualHi l U kr vr ∧
      residualHi l U kr vr < nativePrime) := by
  have h := certificate_residual_bounds l L U kr vr hL hU hk hv
  norm_num [nativePrime] at h ⊢
  omega

lemma endpoints_centered (l : VarLayout) :
    -nativeHalf < loMin l ∧ loMax l < nativeHalf ∧
      -nativeHalf < hiMin l ∧ hiMax l < nativeHalf := by
  cases l <;> decide

lemma certificate_sound (l : VarLayout) (L U kr vr : ℤ)
    (hL : loMin l ≤ L ∧ L ≤ loMax l)
    (hU : hiMin l ≤ U ∧ U ≤ hiMax l)
    (hk : 0 ≤ kr ∧ kr < 2^(qbits l))
    (hv : 0 ≤ vr ∧ vr < 2^(tbits l))
    (h0 : ((residualLo l L kr vr : ℤ) : ZMod nativePrime)=0)
    (h1 : ((residualHi l U kr vr : ℤ) : ZMod nativePrime)=0) :
    L+R*U=q*(kr+kmin l) := by
  have hb := certificate_no_wrap l L U kr vr hL hU hk hv
  have he0 : residualLo l L kr vr=0 :=
    Solution.Secp256k1ScalarMulFixedBase.AffineRangeBounds.zero_of_native_zero h0 hb.1.1 hb.1.2
  have he1 : residualHi l U kr vr=0 :=
    Solution.Secp256k1ScalarMulFixedBase.AffineRangeBounds.zero_of_native_zero h1 hb.2.1 hb.2.2
  rw [q_eq_R2_sub_c]
  simp only [residualLo, residualHi] at he0 he1
  linear_combination he0+R*he1

/-- Any word vector inside the slot envelope has halves inside the layout. -/
lemma slot_half_bounds (l : VarLayout) (z : Words ℤ)
    (hz : ∀ i, slotLo l i ≤ z i ∧ z i ≤ slotHi l i) :
    (loMin l ≤ lowHalf z ∧ lowHalf z ≤ loMax l) ∧
    (hiMin l ≤ highHalf z ∧ highHalf z ≤ hiMax l) := by
  simpa only [loMin, loMax, hiMin, hiMax] using half_interval z (slotLo l) (slotHi l) hz

lemma qbits_valid (l : VarLayout) : 2 ^ qbits l < circomPrime := by
  cases l <;> decide
lemma tbits_valid (l : VarLayout) : 2 ^ tbits l < circomPrime := by
  cases l <;> decide
lemma qbits_pos (l : VarLayout) : 1 ≤ qbits l := by
  cases l <;> decide
lemma tbits_pos (l : VarLayout) : 1 ≤ tbits l := by
  cases l <;> decide

/-! ## Three-limb certificate parameters -/

def limb0 {K : Type*} [CommRing K] (w : Words K) : K := w 0 + H * w 1 + H ^ 2 * w 2
def limb1 {K : Type*} [CommRing K] (w : Words K) : K := w 3 + H * w 4 + H ^ 2 * w 5
def limb2 {K : Type*} [CommRing K] (w : Words K) : K := w 6 + H * w 7

def W96 : ℤ := 2 ^ 96
def W192 : ℤ := 2 ^ 192
def W64 : ℤ := 2 ^ 64

lemma eval_eq_limbs (w : Words ℤ) :
    Solution.Secp256k1ScalarMulFixedBase.Sparse32.eval w H = limb0 w + W96 * limb1 w + W192 * limb2 w := by
  simp only [Solution.Secp256k1ScalarMulFixedBase.Sparse32.eval, limb0, limb1, limb2, Fin.sum_univ_succ, Fin.sum_univ_zero]
  norm_num [Fin.succ, H, W96, W192]
  simp
  ring

lemma limb_interval (f lo hi : Words ℤ) (hf : ∀ i, lo i ≤ f i ∧ f i ≤ hi i) :
    (limb0 lo ≤ limb0 f ∧ limb0 f ≤ limb0 hi) ∧
    (limb1 lo ≤ limb1 f ∧ limb1 f ≤ limb1 hi) ∧
    (limb2 lo ≤ limb2 f ∧ limb2 f ≤ limb2 hi) := by
  simp only [limb0, limb1, limb2, H]
  have h0 := hf 0; have h1 := hf 1; have h2 := hf 2; have h3 := hf 3
  have h4 := hf 4; have h5 := hf 5; have h6 := hf 6; have h7 := hf 7
  norm_num at *
  omega

def l0Min : ℤ := limb0 uniLo
def l0Max : ℤ := limb0 uniHi
def l1Min : ℤ := limb1 uniLo
def l1Max : ℤ := limb1 uniHi
def l2Min : ℤ := limb2 uniLo
def l2Max : ℤ := limb2 uniHi

def ukmin : ℤ := -69470289418662407843111130085823220377
def ukbits : ℕ := 127
def ut0min : ℤ := -12389053923401762962337737545768947209381
def ut0bits : ℕ := 135
def ut1min : ℤ := -152029987281850257267045087993171210058
def ut1bits : ℕ := 128

private def ukmax : ℤ := ukmin + 2^ukbits - 1
private def ut0max : ℤ := ut0min + 2^ut0bits - 1
private def ut1max : ℤ := ut1min + 2^ut1bits - 1

private lemma uni_honest :
    q*(ukmin-1) < l0Min+W96*l1Min+W192*l2Min ∧
    l0Max+W96*l1Max+W192*l2Max < q*(ukmax+1) ∧
    W96*(ut0min-1) < l0Min+c*ukmin ∧ l0Max+c*ukmax < W96*(ut0max+1) ∧
    W96*(ut1min-1) < l1Min+ut0min ∧ l1Max+ut0max < W96*(ut1max+1) := by
  decide

lemma uni_complete (L0 L1 L2 k : ℤ)
    (h0 : l0Min ≤ L0 ∧ L0 ≤ l0Max) (h1 : l1Min ≤ L1 ∧ L1 ≤ l1Max)
    (h2 : l2Min ≤ L2 ∧ L2 ≤ l2Max)
    (he : L0+W96*L1+W192*L2 = q*k) :
    (0 ≤ k-ukmin ∧ k-ukmin < 2^ukbits) ∧
    (0 ≤ (L0+c*k)/W96-ut0min ∧ (L0+c*k)/W96-ut0min < 2^ut0bits) ∧
    (0 ≤ (L1+(L0+c*k)/W96)/W96-ut1min ∧ (L1+(L0+c*k)/W96)/W96-ut1min < 2^ut1bits) ∧
    (L0+c*k) % W96 = 0 ∧ (L1+(L0+c*k)/W96) % W96 = 0 ∧
    L2+(L1+(L0+c*k)/W96)/W96 = W64*k := by
  have hp := uni_honest
  simp only [ukmax, ut0max, ut1max] at hp
  norm_num [q, c, W96, W192, W64] at hp he ⊢
  omega

def ures0 (L0 kr t0r : ℤ) : ℤ := L0+c*(kr+ukmin)-W96*(t0r+ut0min)
def ures1 (L1 t0r t1r : ℤ) : ℤ := L1+(t0r+ut0min)-W96*(t1r+ut1min)
def ures2 (L2 t1r kr : ℤ) : ℤ := L2+(t1r+ut1min)-W64*(kr+ukmin)

private lemma uni_extrema :
    -(2^240 : ℤ) < l0Min+c*ukmin-W96*ut0max ∧ l0Max+c*ukmax-W96*ut0min < 2^240 ∧
    -(2^240 : ℤ) < l1Min+ut0min-W96*ut1max ∧ l1Max+ut0max-W96*ut1min < 2^240 ∧
    -(2^240 : ℤ) < l2Min+ut1min-W64*ukmax ∧ l2Max+ut1max-W64*ukmin < 2^240 := by
  decide

lemma uni_centered :
    -nativeHalf < l0Min ∧ l0Max < nativeHalf ∧ -nativeHalf < l1Min ∧ l1Max < nativeHalf ∧
    -nativeHalf < l2Min ∧ l2Max < nativeHalf := by
  decide

lemma uni_no_wrap (L0 L1 L2 kr t0r t1r : ℤ)
    (h0 : l0Min ≤ L0 ∧ L0 ≤ l0Max) (h1 : l1Min ≤ L1 ∧ L1 ≤ l1Max)
    (h2 : l2Min ≤ L2 ∧ L2 ≤ l2Max)
    (hk : 0 ≤ kr ∧ kr < 2^ukbits) (ht0 : 0 ≤ t0r ∧ t0r < 2^ut0bits)
    (ht1 : 0 ≤ t1r ∧ t1r < 2^ut1bits) :
    (-(nativePrime : ℤ) < ures0 L0 kr t0r ∧ ures0 L0 kr t0r < nativePrime) ∧
    (-(nativePrime : ℤ) < ures1 L1 t0r t1r ∧ ures1 L1 t0r t1r < nativePrime) ∧
    (-(nativePrime : ℤ) < ures2 L2 t1r kr ∧ ures2 L2 t1r kr < nativePrime) := by
  have he := uni_extrema
  simp only [ukmax, ut0max, ut1max] at he
  simp only [ures0, ures1, ures2]
  norm_num [c, W96, W64, nativePrime, ukbits, ut0bits, ut1bits] at he hk ht0 ht1 ⊢
  omega

lemma uni_sound (L0 L1 L2 kr t0r t1r : ℤ)
    (h0 : l0Min ≤ L0 ∧ L0 ≤ l0Max) (h1 : l1Min ≤ L1 ∧ L1 ≤ l1Max)
    (h2 : l2Min ≤ L2 ∧ L2 ≤ l2Max)
    (hk : 0 ≤ kr ∧ kr < 2^ukbits) (ht0 : 0 ≤ t0r ∧ t0r < 2^ut0bits)
    (ht1 : 0 ≤ t1r ∧ t1r < 2^ut1bits)
    (e0 : ((ures0 L0 kr t0r : ℤ) : ZMod nativePrime) = 0)
    (e1 : ((ures1 L1 t0r t1r : ℤ) : ZMod nativePrime) = 0)
    (e2 : ((ures2 L2 t1r kr : ℤ) : ZMod nativePrime) = 0) :
    L0+W96*L1+W192*L2 = q*(kr+ukmin) := by
  have hb := uni_no_wrap L0 L1 L2 kr t0r t1r h0 h1 h2 hk ht0 ht1
  have z0 : ures0 L0 kr t0r = 0 :=
    Solution.Secp256k1ScalarMulFixedBase.AffineRangeBounds.zero_of_native_zero e0 hb.1.1 hb.1.2
  have z1 : ures1 L1 t0r t1r = 0 :=
    Solution.Secp256k1ScalarMulFixedBase.AffineRangeBounds.zero_of_native_zero e1 hb.2.1.1 hb.2.1.2
  have z2 : ures2 L2 t1r kr = 0 :=
    Solution.Secp256k1ScalarMulFixedBase.AffineRangeBounds.zero_of_native_zero e2 hb.2.2.1 hb.2.2.2
  simp only [ures0, ures1, ures2] at z0 z1 z2
  have hq : q = W192 * W64 - c := by norm_num [q, c, W192, W64]
  have h96 : W192 = W96 * W96 := by norm_num [W192, W96]
  rw [hq, h96]
  linear_combination z0 + W96 * z1 + W96 * W96 * z2

lemma uni_limb_bounds (z : Words ℤ) (hz : ∀ i, uniLo i ≤ z i ∧ z i ≤ uniHi i) :
    (l0Min ≤ limb0 z ∧ limb0 z ≤ l0Max) ∧ (l1Min ≤ limb1 z ∧ limb1 z ≤ l1Max) ∧
    (l2Min ≤ limb2 z ∧ limb2 z ≤ l2Max) := by
  simpa only [l0Min, l0Max, l1Min, l1Max, l2Min, l2Max] using limb_interval z uniLo uniHi hz

lemma ukbits_valid : 2 ^ ukbits < circomPrime := by decide
lemma ut0bits_valid : 2 ^ ut0bits < circomPrime := by decide
lemma ut1bits_valid : 2 ^ ut1bits < circomPrime := by decide
lemma ukbits_pos : 1 ≤ ukbits := by decide
lemma ut0bits_pos : 1 ≤ ut0bits := by decide
lemma ut1bits_pos : 1 ≤ ut1bits := by decide

end Solution.Secp256k1ScalarMul.Lazy
