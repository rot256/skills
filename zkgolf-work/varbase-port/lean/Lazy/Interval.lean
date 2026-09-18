import Solution.Secp256k1ScalarMul.Lazy_Donor7
import Solution.Secp256k1ScalarMul.Params

/-! ## merged from `Lazy/Interval.lean` -/
section
/-!
# Interval bounds for sparse products with arbitrary coefficient envelopes

The fixed-base development (patchgravity, zk.golf submission d59c8bf7) bounds
sparse products only for balanced slope digits against a signed state.  The
variable-base chain multiplies arbitrary bounded envelopes (lazy `x`, lazy
`y`, embedded canonical table coordinates), so we prove the general
rectangle-corner bound once and instantiate it structurally.
-/

namespace Solution.Secp256k1ScalarMul.Lazy

open Solution.Secp256k1ScalarMulFixedBase.Sparse32

set_option autoImplicit false

/-- Minimum of the four corner products of `[a₁,a₂] × [x₁,x₂]`. -/
def cornerLo (a₁ a₂ x₁ x₂ : ℤ) : ℤ :=
  min (min (a₁*x₁) (a₂*x₁)) (min (a₁*x₂) (a₂*x₂))

/-- Maximum of the four corner products of `[a₁,a₂] × [x₁,x₂]`. -/
def cornerHi (a₁ a₂ x₁ x₂ : ℤ) : ℤ :=
  max (max (a₁*x₁) (a₂*x₁)) (max (a₁*x₂) (a₂*x₂))

private lemma min_mul_le {a x₁ x₂ : ℤ} (hx : x₁ ≤ x₂) (x : ℤ) (h : x₁ ≤ x ∧ x ≤ x₂) :
    min (a*x₁) (a*x₂) ≤ a*x ∧ a*x ≤ max (a*x₁) (a*x₂) := by
  rcases le_or_gt 0 a with ha | ha
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_left h.1 ha),
      (mul_le_mul_of_nonneg_left h.2 ha).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_left h.2 ha.le),
      (mul_le_mul_of_nonpos_left h.1 ha.le).trans (le_max_left _ _)⟩

private lemma mul_min_le {x a₁ a₂ : ℤ} (a : ℤ) (h : a₁ ≤ a ∧ a ≤ a₂) :
    min (a₁*x) (a₂*x) ≤ a*x ∧ a*x ≤ max (a₁*x) (a₂*x) := by
  have := min_mul_le (a := x) (x₁ := a₁) (x₂ := a₂) (h.1.trans h.2) a h
  simpa only [mul_comm x] using this

/-- Bilinear extrema on a rectangle occur at its corners. -/
lemma corner_bounds {a x a₁ a₂ x₁ x₂ : ℤ}
    (ha : a₁ ≤ a ∧ a ≤ a₂) (hx : x₁ ≤ x ∧ x ≤ x₂) :
    cornerLo a₁ a₂ x₁ x₂ ≤ a*x ∧ a*x ≤ cornerHi a₁ a₂ x₁ x₂ := by
  have h1 := min_mul_le (a := a) (hx.1.trans hx.2) x hx
  have h2 := mul_min_le (x := x₁) a ha
  have h3 := mul_min_le (x := x₂) a ha
  unfold cornerLo cornerHi
  constructor
  · calc
      _ ≤ min (a*x₁) (a*x₂) := min_le_min h2.1 h3.1
      _ ≤ a*x := h1.1
  · calc
      a*x ≤ max (a*x₁) (a*x₂) := h1.2
      _ ≤ _ := max_le_max h2.2 h3.2

/-- Lower envelope of `sparseMul a x` for coefficientwise intervals. -/
def prodLo (aLo aHi xLo xHi : Words ℤ) (k : Fin 8) : ℤ :=
  ∑ i : Fin 8, ∑ j : Fin 8, redCoeff i j k * cornerLo (aLo i) (aHi i) (xLo j) (xHi j)

/-- Upper envelope of `sparseMul a x` for coefficientwise intervals. -/
def prodHi (aLo aHi xLo xHi : Words ℤ) (k : Fin 8) : ℤ :=
  ∑ i : Fin 8, ∑ j : Fin 8, redCoeff i j k * cornerHi (aLo i) (aHi i) (xLo j) (xHi j)

lemma sparseMul_interval (aLo aHi xLo xHi a x : Words ℤ)
    (ha : ∀ i, aLo i ≤ a i ∧ a i ≤ aHi i)
    (hx : ∀ j, xLo j ≤ x j ∧ x j ≤ xHi j) (k : Fin 8) :
    prodLo aLo aHi xLo xHi k ≤ sparseMul a x k ∧
      sparseMul a x k ≤ prodHi aLo aHi xLo xHi k := by
  have ht (i j : Fin 8) := corner_bounds (ha i) (hx j)
  have hw (i j : Fin 8) : 0 ≤ redCoeff i j k := redCoeff_nonneg i j k
  constructor
  · exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_left (ht i j).1 (hw i j)
  · exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_left (ht i j).2 (hw i j)

/-- Square envelope (corner bound on the same interval; sound, slightly loose). -/
def sqLo (xLo xHi : Words ℤ) : Words ℤ := prodLo xLo xHi xLo xHi
def sqHi (xLo xHi : Words ℤ) : Words ℤ := prodHi xLo xHi xLo xHi

lemma sparseSquare_interval (xLo xHi x : Words ℤ)
    (hx : ∀ j, xLo j ≤ x j ∧ x j ≤ xHi j) (k : Fin 8) :
    sqLo xLo xHi k ≤ sparseSquare x k ∧ sparseSquare x k ≤ sqHi xLo xHi k :=
  sparseMul_interval xLo xHi xLo xHi x x hx hx k

/-- Balanced slope digits as a coefficient envelope. -/
def digLo : Words ℤ := fun _ => -m
def digHi : Words ℤ := fun _ => m - 1

/-- The mixed slope `a + b` used by the second relation. -/
def dig2Lo : Words ℤ := fun _ => -2*m
def dig2Hi : Words ℤ := fun _ => 2*m - 2

/-- Embedded canonical coordinates occupy `[0, dcap]`. -/
def embLo : Words ℤ := fun _ => 0
def embHi : Words ℤ := dcap

lemma embed_interval (T : Fin 4 → ℤ) (hT : ∀ i, 0 ≤ T i ∧ T i ≤ wordMax) (i : Fin 8) :
    embLo i ≤ embed T i ∧ embed T i ≤ embHi i :=
  embed_bounds T hT i

lemma digits_interval (a : Words ℤ) (ha : ∀ i, -m ≤ a i ∧ a i ≤ m - 1) (i : Fin 8) :
    digLo i ≤ a i ∧ a i ≤ digHi i := ha i

lemma digits2_interval (a b : Words ℤ) (ha : ∀ i, -m ≤ a i ∧ a i ≤ m - 1)
    (hb : ∀ i, -m ≤ b i ∧ b i ≤ m - 1) (i : Fin 8) :
    dig2Lo i ≤ a i + b i ∧ a i + b i ≤ dig2Hi i := by
  have := ha i; have := hb i
  simp only [dig2Lo, dig2Hi]
  omega

/-- Pointwise interval union, used for muxed branches. -/
def wmin (u v : Words ℤ) : Words ℤ := fun i => min (u i) (v i)
def wmax (u v : Words ℤ) : Words ℤ := fun i => max (u i) (v i)
def wsub (u v : Words ℤ) : Words ℤ := fun i => u i - v i
def wadd (u v : Words ℤ) : Words ℤ := fun i => u i + v i
def wneg (u : Words ℤ) : Words ℤ := fun i => -u i
def wscale (s : ℤ) (u : Words ℤ) : Words ℤ := fun i => s * u i
def wzero : Words ℤ := fun _ => 0

/-- Interval arithmetic on envelopes: the difference `u - v`. -/
lemma sub_interval {uLo uHi vLo vHi u v : Words ℤ}
    (hu : ∀ i, uLo i ≤ u i ∧ u i ≤ uHi i) (hv : ∀ i, vLo i ≤ v i ∧ v i ≤ vHi i) (i : Fin 8) :
    wsub uLo vHi i ≤ u i - v i ∧ u i - v i ≤ wsub uHi vLo i := by
  have := hu i; have := hv i
  simp only [wsub]; omega

lemma add_interval {uLo uHi vLo vHi u v : Words ℤ}
    (hu : ∀ i, uLo i ≤ u i ∧ u i ≤ uHi i) (hv : ∀ i, vLo i ≤ v i ∧ v i ≤ vHi i) (i : Fin 8) :
    wadd uLo vLo i ≤ u i + v i ∧ u i + v i ≤ wadd uHi vHi i := by
  have := hu i; have := hv i
  simp only [wadd]; omega

lemma scale_interval {uLo uHi u : Words ℤ} (s : ℤ) (hs : 0 ≤ s)
    (hu : ∀ i, uLo i ≤ u i ∧ u i ≤ uHi i) (i : Fin 8) :
    wscale s uLo i ≤ s * u i ∧ s * u i ≤ wscale s uHi i := by
  have := hu i
  simp only [wscale]
  exact ⟨mul_le_mul_of_nonneg_left this.1 hs, mul_le_mul_of_nonneg_left this.2 hs⟩

lemma neg_interval {uLo uHi u : Words ℤ}
    (hu : ∀ i, uLo i ≤ u i ∧ u i ≤ uHi i) (i : Fin 8) :
    wneg uHi i ≤ -u i ∧ -u i ≤ wneg uLo i := by
  have := hu i
  simp only [wneg]; omega

lemma union_left {uLo uHi vLo vHi u : Words ℤ}
    (hu : ∀ i, uLo i ≤ u i ∧ u i ≤ uHi i) (i : Fin 8) :
    wmin uLo vLo i ≤ u i ∧ u i ≤ wmax uHi vHi i := by
  have := hu i
  simp only [wmin, wmax]
  exact ⟨(min_le_left _ _).trans this.1, this.2.trans (le_max_left _ _)⟩

lemma union_right {uLo uHi vLo vHi v : Words ℤ}
    (hv : ∀ i, vLo i ≤ v i ∧ v i ≤ vHi i) (i : Fin 8) :
    wmin uLo vLo i ≤ v i ∧ v i ≤ wmax uHi vHi i := by
  have := hv i
  simp only [wmin, wmax]
  exact ⟨(min_le_right _ _).trans this.1, this.2.trans (le_max_right _ _)⟩

lemma zero_interval (i : Fin 8) : wzero i ≤ (0 : ℤ) ∧ (0 : ℤ) ≤ wzero i := by
  simp [wzero]

end Solution.Secp256k1ScalarMul.Lazy
end

/-! ## merged from `Lazy/Bounds.lean` -/
section
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
end

/-! ## merged from `Lazy/Cert.lean` -/
section
/-!
# Zero-row certificate `L + R·U ≡ 0 (mod q)` for the variable-base layouts

Port of `Sparse32Cert` from the fixed-base record (patchgravity, d59c8bf7)
over `VarLayout`: two implicit range checks on affine expressions, no
allocated product rows.
-/

namespace Solution.Secp256k1ScalarMulFixedBase.LazyVar.Cert

open Solution.Secp256k1ScalarMul.Lazy
open Challenge.CostR1CS
open Challenge.Utils.ComputableWitnessLemmas

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

abbrev Field := SmallSquare.Field


def Assumptions (l : VarLayout) (i : fields 2 Field) : Prop :=
  (loMin l ≤ LazyX.lift (i[0]'(by decide)) ∧ LazyX.lift (i[0]'(by decide)) ≤ loMax l) ∧
  (hiMin l ≤ LazyX.lift (i[1]'(by decide)) ∧ LazyX.lift (i[1]'(by decide)) ≤ hiMax l)

def Spec (i : fields 2 Field) : Prop :=
  Sparse32.q ∣ LazyX.lift (i[0]'(by decide)) + Sparse32.R * LazyX.lift (i[1]'(by decide))

def rawQ (i : fields 2 Field) : Field :=
  (Sparse32.q : Field)⁻¹ * ((i[0]'(by decide)) + (Sparse32.R : Field) * (i[1]'(by decide)))
def qValue (l : VarLayout) (i : fields 2 Field) : Field := rawQ i - (kmin l : Field)
def vValue (l : VarLayout) (i : fields 2 Field) : Field :=
  (Sparse32.R : Field)⁻¹ * ((i[0]'(by decide)) - ((Sparse32.R-Sparse32.c : ℤ) : Field) * rawQ i) - (tmin l : Field)

def rawQExpr (i : Var (fields 2) Field) : Expression Field :=
  (Sparse32.q : Field)⁻¹ * ((i[0]'(by decide)) + (Sparse32.R : Field) * (i[1]'(by decide)))
def qExpr (l : VarLayout) (i : Var (fields 2) Field) : Expression Field :=
  rawQExpr i - (kmin l : Field)
def vExpr (l : VarLayout) (i : Var (fields 2) Field) : Expression Field :=
  (Sparse32.R : Field)⁻¹ * ((i[0]'(by decide)) - ((Sparse32.R-Sparse32.c : ℤ) : Field) * rawQExpr i) -
    (tmin l : Field)

def main (l : VarLayout) (i : Var (fields 2) Field) : Circuit Field Unit := do
  assertion (RangeCheck.circuit (qbits l) (qbits_valid l) (qbits_pos l)) (qExpr l i)
  assertion (RangeCheck.circuit (tbits l) (tbits_valid l) (tbits_pos l)) (vExpr l i)

instance elaborated (l : VarLayout) : ElaboratedCircuit Field (fields 2) unit (main l) := by
  elaborate_circuit

lemma values_sound (l : VarLayout) (i : fields 2 Field) (h : Assumptions l i)
    (hk : (qValue l i).val < 2 ^ qbits l) (hv : (vValue l i).val < 2 ^ tbits l) :
    Spec i := by
  have hn :
      (i[0]'(by decide)) - ((Sparse32.R-Sparse32.c : ℤ) : Field) * rawQ i -
          (Sparse32.R : Field) * ((Sparse32.R : Field)⁻¹ *
            ((i[0]'(by decide)) - ((Sparse32.R-Sparse32.c : ℤ) : Field) * rawQ i)) = 0 ∧
        (i[1]'(by decide)) - ((Sparse32.R-1 : ℤ) : Field) * rawQ i +
          (Sparse32.R : Field)⁻¹ *
            ((i[0]'(by decide)) - ((Sparse32.R-Sparse32.c : ℤ) : Field) * rawQ i) = 0 := by
    simpa only [rawQ, Sparse32.q,
      Sparse32.R, Sparse32.c,
      SmallSquare.q, SmallSquare.R,
      SmallSquare.c] using
        SmallCert.native (i[0]'(by decide)) (i[1]'(by decide))
  simp only [rawQ] at hn
  have h0 :
      ((LazyX.lift (i[0]'(by decide)) - (Sparse32.R-Sparse32.c) * ((qValue l i).val + kmin l) -
        Sparse32.R * ((vValue l i).val + tmin l) : ℤ) : Field) = 0 := by
    push_cast
    simp only [LazyX.cast_lift, FoldQuot.natCast_val_F, qValue,
      vValue, rawQ]
    push_cast at hn ⊢
    linear_combination hn.1
  have h1 :
      ((LazyX.lift (i[1]'(by decide)) - (Sparse32.R-1) * ((qValue l i).val + kmin l) +
        ((vValue l i).val + tmin l) : ℤ) : Field) = 0 := by
    push_cast
    simp only [LazyX.cast_lift, FoldQuot.natCast_val_F, qValue,
      vValue, rawQ]
    push_cast at hn ⊢
    linear_combination hn.2
  have he := certificate_sound l
    (LazyX.lift (i[0]'(by decide))) (LazyX.lift (i[1]'(by decide)))
    (qValue l i).val (vValue l i).val h.1 h.2
    ⟨by omega, by exact_mod_cast hk⟩ ⟨by omega, by exact_mod_cast hv⟩ h0 h1
  exact ⟨(qValue l i).val + kmin l, he⟩

lemma values_complete (l : VarLayout) (i : fields 2 Field) (h : Assumptions l i)
    (hs : Spec i) :
    (qValue l i).val < 2 ^ qbits l ∧ (vValue l i).val < 2 ^ tbits l := by
  obtain ⟨k, hk⟩ := hs
  have hb := certificate_complete l
    (LazyX.lift (i[0]'(by decide))) (LazyX.lift (i[1]'(by decide))) k h.1 h.2 hk
  have he := congrArg (fun z : ℤ => (z : Field)) hk
  push_cast at he
  simp only [LazyX.cast_lift] at he
  have hq : rawQ i = (k : Field) := by
    unfold rawQ
    rw [he, ← mul_assoc]
    have hqn : (Sparse32.q : Field) ≠ 0 := by decide
    rw [inv_mul_cancel₀ hqn, one_mul]
  have hqv : qValue l i = ((k-kmin l : ℤ) : Field) := by
    simp only [qValue, hq, Int.cast_sub]
  have hn := (SmallCert.native (i[0]'(by decide)) (i[1]'(by decide))).2
  change (i[1]'(by decide)) - ((Sparse32.R-1 : ℤ) : Field) * rawQ i +
    (Sparse32.R : Field)⁻¹ * ((i[0]'(by decide)) - ((Sparse32.R-Sparse32.c : ℤ) : Field) * rawQ i) = 0 at hn
  rw [hq] at hn
  have hvv :
      vValue l i = (((Sparse32.R-1)*k-LazyX.lift (i[1]'(by decide))-tmin l : ℤ) : Field) := by
    unfold vValue
    rw [hq]
    push_cast at hn ⊢
    rw [LazyX.cast_lift]
    linear_combination hn
  constructor
  · rw [hqv]
    exact AffineNarrow.range_of_int _ _ hb.1 (qbits_valid l)
  · rw [hvv]
    exact AffineNarrow.range_of_int _ _ hb.2 (tbits_valid l)

lemma eval_expr (l : VarLayout) (env : Environment Field) (i : Var (fields 2) Field) :
    Expression.eval env (qExpr l i) = qValue l (eval env i) ∧
    Expression.eval env (vExpr l i) = vValue l (eval env i) := by
  simp only [qExpr, vExpr, rawQExpr, qValue, vValue, rawQ, Expression.eval,
    circuit_norm, neg_one_mul, sub_eq_add_neg, and_self]

theorem soundness (l : VarLayout) :
    FormalAssertion.Soundness Field (main l) (Assumptions l) Spec := by
  circuit_proof_start_core
  have he := eval_expr l env input_var
  rw [h_input] at he
  simp only [main, circuit_norm, RangeCheck.circuit, RangeCheck.Assumptions,
    RangeCheck.Spec] at h_holds ⊢
  exact values_sound l input h_assumptions
    (by simpa only [he.1] using h_holds.1) (by simpa only [he.2] using h_holds.2)

theorem completeness (l : VarLayout) :
    FormalAssertion.Completeness Field (main l) (Assumptions l) Spec := by
  circuit_proof_start_core
  have he := eval_expr l env.toEnvironment input_var
  have hi : eval env.toEnvironment input_var = input := by
    simpa only [circuit_norm] using h_input
  rw [hi] at he
  have hv := values_complete l input h_assumptions h_spec
  simp only [main, circuit_norm, RangeCheck.circuit, RangeCheck.Assumptions, RangeCheck.Spec]
  exact ⟨by simpa only [he.1] using hv.1, by simpa only [he.2] using hv.2⟩

def circuit (l : VarLayout) : FormalAssertion Field (fields 2) where
  main := main l
  Assumptions := Assumptions l
  Spec := Spec
  soundness := soundness l
  completeness := completeness l

theorem cost (l : VarLayout) (i : Var (fields 2) Field) :
    CostIs (main l i) ⟨qbits l+tbits l-2, qbits l+tbits l⟩ := by
  rw [show (⟨qbits l+tbits l-2, qbits l+tbits l⟩ : Count) =
    ⟨qbits l-1, qbits l⟩ + ⟨tbits l-1, tbits l⟩ by
      cases l <;> decide]
  unfold main
  refine CostIs.bind
    (Cost.costIs_assertion_implicitRangeCheck _ _ _ _) fun _ => ?_
  exact Cost.costIs_assertion_implicitRangeCheck _ _ _ _

lemma affine_expr (l : VarLayout) (i : Var (fields 2) Field) (hi : AffineW i) :
    Affine (qExpr l i) ∧ Affine (vExpr l i) := by
  have hq : Affine (rawQExpr i) :=
    Affine.fconst_mul _
      (Affine.add (hi _ (by decide)) (Affine.fconst_mul _ (hi _ (by decide))))
  exact ⟨Affine.sub hq (Affine.const _),
    Affine.sub
      (Affine.fconst_mul _ (Affine.sub (hi _ (by decide)) (Affine.fconst_mul _ hq)))
      (Affine.const _)⟩

theorem shape (l : VarLayout) (i : Var (fields 2) Field) (hi : AffineW i) :
    IsR1CSCirc (main l i) := by
  have h := affine_expr l i hi
  unfold main
  refine IsR1CSCirc.bind
    (Cost.isR1CS_assertion_implicitRangeCheck _ _ _ _ h.1)
    fun _ => ?_
  exact Cost.isR1CS_assertion_implicitRangeCheck _ _ _ _ h.2

lemma expr_stable (l : VarLayout) (i : Var (fields 2) Field)
    {e e' : ProverEnvironment Field} (h : eval e i = eval e' i) :
    eval e (qExpr l i) = eval e' (qExpr l i) ∧
      eval e (vExpr l i) = eval e' (vExpr l i) := by
  have h' : eval e.toEnvironment i = eval e'.toEnvironment i := by
    simpa only [circuit_norm] using h
  simpa only [circuit_norm, (eval_expr l e.toEnvironment i).1,
    (eval_expr l e'.toEnvironment i).1, (eval_expr l e.toEnvironment i).2,
    (eval_expr l e'.toEnvironment i).2, h']

theorem computableWitnesses (l : VarLayout) : (circuit l).ComputableWitnesses := by
  intro n input env env'
  change Operations.forAllFlat n (FormalCircuitBase.computableWitnessCondition input env env')
    ((main l input).operations n)
  apply FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  simp only [main, Circuit.bind_structuralComputableWitnesses_iff]
  constructor
  · exact CWHelpers.assertion_structuralComputableWitnesses_of_condition
      (RangeCheck.circuit (qbits l) (qbits_valid l) (qbits_pos l))
      input _ _ (fun _ _ _ _ _ h => (expr_stable l input h).1)
      (RangeCheck.computableWitnesses _ _ _) env env'
  · exact CWHelpers.assertion_structuralComputableWitnesses_of_condition
      (RangeCheck.circuit (tbits l) (tbits_valid l) (tbits_pos l))
      input _ _ (fun _ _ _ _ _ h => (expr_stable l input h).2)
      (RangeCheck.computableWitnesses _ _ _) env env'

/-- Integer-valued halves inside the layout satisfy the assumptions, and the
specification is divisibility of the integer value. -/
lemma model (l : VarLayout) (i : fields 2 Field) (L H : ℤ)
    (hL : loMin l ≤ L ∧ L ≤ loMax l)
    (hH : hiMin l ≤ H ∧ H ≤ hiMax l)
    (hl : (i[0]'(by decide)) = (L : Field))
    (hh : (i[1]'(by decide)) = (H : Field)) :
    Assumptions l i ∧ (Spec i ↔ Sparse32.q ∣ L+Sparse32.R*H) := by
  have he := endpoints_centered l
  have hhalf : Sparse32.nativeHalf = LazyX.nativeHalf := by
    norm_num [Sparse32.nativeHalf,
      Sparse32.nativePrime, LazyX.nativeHalf]
  have hlift : LazyX.lift (i[0]'(by decide)) = L := by
    rw [hl]
    apply LazyX.lift_cast
    rw [← hhalf]
    omega
  have hlifth : LazyX.lift (i[1]'(by decide)) = H := by
    rw [hh]
    apply LazyX.lift_cast
    rw [← hhalf]
    omega
  simp only [Assumptions, Spec, hlift, hlifth]
  exact ⟨⟨hL, hH⟩, trivial⟩

lemma localLength (l : VarLayout) (i : Var (fields 2) Field) (o : ℕ) :
    (main l i).localLength o = qbits l + tbits l - 2 := by
  simp only [main, RangeCheck.circuit, circuit_norm]
  cases l <;> decide

end Solution.Secp256k1ScalarMulFixedBase.LazyVar.Cert
end

/-! ## merged from `Lazy/Cert3.lean` -/
section
/-!
# Three-limb zero-row certificate for the unified slope relation

The unified relation `a (y + T.y) − (x² + x T.x + T.x²)` has coefficients of
about 171 bits, too wide for the two-half certificate (its residual would pass
the native prime).  Splitting the eight coefficients as `L0 + 2^96 L1 + 2^192 L2`
and carrying twice keeps every native residual below 2^240.  The quotient and
the two carries are affine in the limbs, so the certificate is still three
implicit range checks and no product rows (same idea as patchgravity's
`Sparse32Cert`, d59c8bf7).
-/

namespace Solution.Secp256k1ScalarMulFixedBase.LazyVar.Cert3

open Solution.Secp256k1ScalarMul.Lazy
open Challenge.CostR1CS
open Challenge.Utils.ComputableWitnessLemmas

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

abbrev Field := SmallSquare.Field

def Assumptions (i : fields 3 Field) : Prop :=
  (l0Min ≤ LazyX.lift (i[0]'(by decide)) ∧ LazyX.lift (i[0]'(by decide)) ≤ l0Max) ∧
  (l1Min ≤ LazyX.lift (i[1]'(by decide)) ∧ LazyX.lift (i[1]'(by decide)) ≤ l1Max) ∧
  (l2Min ≤ LazyX.lift (i[2]'(by decide)) ∧ LazyX.lift (i[2]'(by decide)) ≤ l2Max)

def Spec (i : fields 3 Field) : Prop :=
  Sparse32.q ∣ LazyX.lift (i[0]'(by decide)) + W96 * LazyX.lift (i[1]'(by decide)) +
    W192 * LazyX.lift (i[2]'(by decide))

def rawK (i : fields 3 Field) : Field :=
  (Sparse32.q : Field)⁻¹ *
    ((i[0]'(by decide)) + (W96 : Field) * (i[1]'(by decide)) + (W192 : Field) * (i[2]'(by decide)))
def rawT0 (i : fields 3 Field) : Field :=
  (W96 : Field)⁻¹ * ((i[0]'(by decide)) + (Sparse32.c : Field) * rawK i)
def rawT1 (i : fields 3 Field) : Field :=
  (W96 : Field)⁻¹ * ((i[1]'(by decide)) + rawT0 i)
def kValue (i : fields 3 Field) : Field := rawK i - (ukmin : Field)
def t0Value (i : fields 3 Field) : Field := rawT0 i - (ut0min : Field)
def t1Value (i : fields 3 Field) : Field := rawT1 i - (ut1min : Field)

def rawKExpr (i : Var (fields 3) Field) : Expression Field :=
  (Sparse32.q : Field)⁻¹ *
    ((i[0]'(by decide)) + (W96 : Field) * (i[1]'(by decide)) + (W192 : Field) * (i[2]'(by decide)))
def rawT0Expr (i : Var (fields 3) Field) : Expression Field :=
  (W96 : Field)⁻¹ * ((i[0]'(by decide)) + (Sparse32.c : Field) * rawKExpr i)
def rawT1Expr (i : Var (fields 3) Field) : Expression Field :=
  (W96 : Field)⁻¹ * ((i[1]'(by decide)) + rawT0Expr i)
def kExpr (i : Var (fields 3) Field) : Expression Field := rawKExpr i - (ukmin : Field)
def t0Expr (i : Var (fields 3) Field) : Expression Field := rawT0Expr i - (ut0min : Field)
def t1Expr (i : Var (fields 3) Field) : Expression Field := rawT1Expr i - (ut1min : Field)

def main (i : Var (fields 3) Field) : Circuit Field Unit := do
  assertion (RangeCheck.circuit ukbits ukbits_valid ukbits_pos) (kExpr i)
  assertion (RangeCheck.circuit ut0bits ut0bits_valid ut0bits_pos) (t0Expr i)
  assertion (RangeCheck.circuit ut1bits ut1bits_valid ut1bits_pos) (t1Expr i)

instance elaborated : ElaboratedCircuit Field (fields 3) unit main := by
  elaborate_circuit

lemma q_ne : (Sparse32.q : Field) ≠ 0 := by decide
lemma w96_ne : (W96 : Field) ≠ 0 := by decide
lemma w192_ne : (W192 : Field) ≠ 0 := by decide

/-- The three native carry identities hold by construction of the raw values. -/
lemma native (i : fields 3 Field) :
    (i[0]'(by decide)) + (Sparse32.c : Field) * rawK i - (W96 : Field) * rawT0 i = 0 ∧
    (i[1]'(by decide)) + rawT0 i - (W96 : Field) * rawT1 i = 0 ∧
    (i[2]'(by decide)) + rawT1 i - (W64 : Field) * rawK i = 0 := by
  have hq : (Sparse32.q : Field) = (W192 : Field) * (W64 : Field) - (Sparse32.c : Field) := by
    norm_num [Sparse32.q, Sparse32.c, W192, W64]
  have h192 : (W192 : Field) = (W96 : Field) * (W96 : Field) := by norm_num [W192, W96]
  refine ⟨?_, ?_, ?_⟩
  · unfold rawT0
    rw [mul_inv_cancel_left₀ w96_ne]
    ring
  · unfold rawT1
    rw [mul_inv_cancel_left₀ w96_ne]
    ring
  · have hk : (Sparse32.q : Field) * rawK i =
        (i[0]'(by decide)) + (W96 : Field) * (i[1]'(by decide)) + (W192 : Field) * (i[2]'(by decide)) := by
      unfold rawK; rw [mul_inv_cancel_left₀ q_ne]
    have ht0 : (W96 : Field) * rawT0 i = (i[0]'(by decide)) + (Sparse32.c : Field) * rawK i := by
      unfold rawT0; rw [mul_inv_cancel_left₀ w96_ne]
    have ht1 : (W96 : Field) * rawT1 i = (i[1]'(by decide)) + rawT0 i := by
      unfold rawT1; rw [mul_inv_cancel_left₀ w96_ne]
    have hz : (W192 : Field) * ((i[2]'(by decide)) + rawT1 i - (W64 : Field) * rawK i) = 0 := by
      linear_combination (W96 : Field) * ht1 + ht0 - hk + rawK i * hq +
        rawT1 i * h192
    rcases mul_eq_zero.mp hz with h | h
    · exact absurd h w192_ne
    · exact h

lemma values_sound (i : fields 3 Field) (h : Assumptions i)
    (hk : (kValue i).val < 2 ^ ukbits) (h0 : (t0Value i).val < 2 ^ ut0bits)
    (h1 : (t1Value i).val < 2 ^ ut1bits) :
    Spec i := by
  have hn := native i
  have e0 : ((ures0 (LazyX.lift (i[0]'(by decide))) (kValue i).val (t0Value i).val : ℤ) : Field)
      = 0 := by
    simp only [ures0]
    push_cast
    simp only [LazyX.cast_lift, FoldQuot.natCast_val_F, kValue, t0Value]
    linear_combination hn.1
  have e1 : ((ures1 (LazyX.lift (i[1]'(by decide))) (t0Value i).val (t1Value i).val : ℤ) : Field)
      = 0 := by
    simp only [ures1]
    push_cast
    simp only [LazyX.cast_lift, FoldQuot.natCast_val_F, t0Value, t1Value]
    linear_combination hn.2.1
  have e2 : ((ures2 (LazyX.lift (i[2]'(by decide))) (t1Value i).val (kValue i).val : ℤ) : Field)
      = 0 := by
    simp only [ures2]
    push_cast
    simp only [LazyX.cast_lift, FoldQuot.natCast_val_F, t1Value, kValue]
    linear_combination hn.2.2
  have he := uni_sound (LazyX.lift (i[0]'(by decide))) (LazyX.lift (i[1]'(by decide)))
    (LazyX.lift (i[2]'(by decide))) (kValue i).val (t0Value i).val (t1Value i).val
    h.1 h.2.1 h.2.2 ⟨by omega, by exact_mod_cast hk⟩ ⟨by omega, by exact_mod_cast h0⟩
    ⟨by omega, by exact_mod_cast h1⟩ e0 e1 e2
  exact ⟨(kValue i).val + ukmin, he⟩

lemma values_complete (i : fields 3 Field) (h : Assumptions i) (hs : Spec i) :
    (kValue i).val < 2 ^ ukbits ∧ (t0Value i).val < 2 ^ ut0bits ∧
      (t1Value i).val < 2 ^ ut1bits := by
  obtain ⟨k, hk⟩ := hs
  set L0 := LazyX.lift (i[0]'(by decide)) with hL0
  set L1 := LazyX.lift (i[1]'(by decide)) with hL1
  set L2 := LazyX.lift (i[2]'(by decide)) with hL2
  have hb := uni_complete L0 L1 L2 k h.1 h.2.1 h.2.2 hk
  obtain ⟨hbk, hbt0, hbt1, hd0, hd1, hl2⟩ := hb
  -- integer carries
  set T0 : ℤ := (L0 + Sparse32.c * k) / W96 with hT0
  set T1 : ℤ := (L1 + T0) / W96 with hT1
  have hT0e : L0 + Sparse32.c * k = W96 * T0 := by
    have := Int.ediv_add_emod (L0 + Sparse32.c * k) W96
    rw [hd0, add_zero] at this
    linear_combination -this
  have hT1e : L1 + T0 = W96 * T1 := by
    have := Int.ediv_add_emod (L1 + T0) W96
    rw [hd1, add_zero] at this
    linear_combination -this
  have hi0 : (i[0]'(by decide)) = (L0 : Field) := by rw [hL0, LazyX.cast_lift]
  have hi1 : (i[1]'(by decide)) = (L1 : Field) := by rw [hL1, LazyX.cast_lift]
  have hi2 : (i[2]'(by decide)) = (L2 : Field) := by rw [hL2, LazyX.cast_lift]
  have hrawK : rawK i = (k : Field) := by
    unfold rawK
    rw [hi0, hi1, hi2]
    have : ((L0 + W96 * L1 + W192 * L2 : ℤ) : Field) = ((Sparse32.q * k : ℤ) : Field) := by
      rw [hk]
    push_cast at this
    rw [this, ← mul_assoc, inv_mul_cancel₀ q_ne, one_mul]
  have hrawT0 : rawT0 i = (T0 : Field) := by
    unfold rawT0
    rw [hi0, hrawK]
    have : ((L0 + Sparse32.c * k : ℤ) : Field) = ((W96 * T0 : ℤ) : Field) := by rw [hT0e]
    push_cast at this
    rw [this, ← mul_assoc, inv_mul_cancel₀ w96_ne, one_mul]
  have hrawT1 : rawT1 i = (T1 : Field) := by
    unfold rawT1
    rw [hi1, hrawT0]
    have : ((L1 + T0 : ℤ) : Field) = ((W96 * T1 : ℤ) : Field) := by rw [hT1e]
    push_cast at this
    rw [this, ← mul_assoc, inv_mul_cancel₀ w96_ne, one_mul]
  refine ⟨?_, ?_, ?_⟩
  · rw [show kValue i = ((k - ukmin : ℤ) : Field) by simp only [kValue, hrawK, Int.cast_sub]]
    exact AffineNarrow.range_of_int _ _ hbk ukbits_valid
  · rw [show t0Value i = ((T0 - ut0min : ℤ) : Field) by
      simp only [t0Value, hrawT0, Int.cast_sub]]
    exact AffineNarrow.range_of_int _ _ hbt0 ut0bits_valid
  · rw [show t1Value i = ((T1 - ut1min : ℤ) : Field) by
      simp only [t1Value, hrawT1, Int.cast_sub]]
    exact AffineNarrow.range_of_int _ _ hbt1 ut1bits_valid

lemma eval_expr (env : Environment Field) (i : Var (fields 3) Field) :
    Expression.eval env (kExpr i) = kValue (eval env i) ∧
    Expression.eval env (t0Expr i) = t0Value (eval env i) ∧
    Expression.eval env (t1Expr i) = t1Value (eval env i) := by
  simp only [kExpr, t0Expr, t1Expr, rawKExpr, rawT0Expr, rawT1Expr, kValue, t0Value, t1Value,
    rawK, rawT0, rawT1, Expression.eval, circuit_norm, neg_one_mul, sub_eq_add_neg, and_self]

theorem soundness : FormalAssertion.Soundness Field main Assumptions Spec := by
  circuit_proof_start_core
  have he := eval_expr env input_var
  rw [h_input] at he
  simp only [main, circuit_norm, RangeCheck.circuit, RangeCheck.Assumptions,
    RangeCheck.Spec] at h_holds ⊢
  exact values_sound input h_assumptions
    (by simpa only [he.1] using h_holds.1) (by simpa only [he.2.1] using h_holds.2.1)
    (by simpa only [he.2.2] using h_holds.2.2)

theorem completeness : FormalAssertion.Completeness Field main Assumptions Spec := by
  circuit_proof_start_core
  have he := eval_expr env.toEnvironment input_var
  have hi : eval env.toEnvironment input_var = input := by
    simpa only [circuit_norm] using h_input
  rw [hi] at he
  have hv := values_complete input h_assumptions h_spec
  simp only [main, circuit_norm, RangeCheck.circuit, RangeCheck.Assumptions, RangeCheck.Spec]
  exact ⟨by simpa only [he.1] using hv.1, by simpa only [he.2.1] using hv.2.1,
    by simpa only [he.2.2] using hv.2.2⟩

def circuit : FormalAssertion Field (fields 3) where
  main := main
  Assumptions := Assumptions
  Spec := Spec
  soundness := soundness
  completeness := completeness

def cost3 : Count := ⟨ukbits + ut0bits + ut1bits - 3, ukbits + ut0bits + ut1bits⟩

theorem cost (i : Var (fields 3) Field) : CostIs (main i) cost3 := by
  rw [show cost3 = ⟨ukbits-1, ukbits⟩ + (⟨ut0bits-1, ut0bits⟩ + ⟨ut1bits-1, ut1bits⟩) by decide]
  unfold main
  refine CostIs.bind (Cost.costIs_assertion_implicitRangeCheck _ _ _ _) fun _ => ?_
  refine CostIs.bind (Cost.costIs_assertion_implicitRangeCheck _ _ _ _) fun _ => ?_
  exact Cost.costIs_assertion_implicitRangeCheck _ _ _ _

lemma affine_expr (i : Var (fields 3) Field) (hi : AffineW i) :
    Affine (kExpr i) ∧ Affine (t0Expr i) ∧ Affine (t1Expr i) := by
  have hk : Affine (rawKExpr i) :=
    Affine.fconst_mul _
      (Affine.add (Affine.add (hi _ (by decide)) (Affine.fconst_mul _ (hi _ (by decide))))
        (Affine.fconst_mul _ (hi _ (by decide))))
  have ht0 : Affine (rawT0Expr i) :=
    Affine.fconst_mul _ (Affine.add (hi _ (by decide)) (Affine.fconst_mul _ hk))
  have ht1 : Affine (rawT1Expr i) :=
    Affine.fconst_mul _ (Affine.add (hi _ (by decide)) ht0)
  exact ⟨Affine.sub hk (Affine.const _), Affine.sub ht0 (Affine.const _),
    Affine.sub ht1 (Affine.const _)⟩

theorem shape (i : Var (fields 3) Field) (hi : AffineW i) : IsR1CSCirc (main i) := by
  have h := affine_expr i hi
  unfold main
  refine IsR1CSCirc.bind (Cost.isR1CS_assertion_implicitRangeCheck _ _ _ _ h.1) fun _ => ?_
  refine IsR1CSCirc.bind (Cost.isR1CS_assertion_implicitRangeCheck _ _ _ _ h.2.1) fun _ => ?_
  exact Cost.isR1CS_assertion_implicitRangeCheck _ _ _ _ h.2.2

lemma expr_stable (i : Var (fields 3) Field)
    {e e' : ProverEnvironment Field} (h : eval e i = eval e' i) :
    eval e (kExpr i) = eval e' (kExpr i) ∧
      eval e (t0Expr i) = eval e' (t0Expr i) ∧ eval e (t1Expr i) = eval e' (t1Expr i) := by
  have h' : eval e.toEnvironment i = eval e'.toEnvironment i := by
    simpa only [circuit_norm] using h
  simpa only [circuit_norm, (eval_expr e.toEnvironment i).1, (eval_expr e'.toEnvironment i).1,
    (eval_expr e.toEnvironment i).2.1, (eval_expr e'.toEnvironment i).2.1,
    (eval_expr e.toEnvironment i).2.2, (eval_expr e'.toEnvironment i).2.2, h']

theorem computableWitnesses : circuit.ComputableWitnesses := by
  intro n input env env'
  change Operations.forAllFlat n (FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations n)
  apply FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  simp only [main, Circuit.bind_structuralComputableWitnesses_iff]
  refine ⟨?_, ?_, ?_⟩
  · exact CWHelpers.assertion_structuralComputableWitnesses_of_condition
      (RangeCheck.circuit ukbits ukbits_valid ukbits_pos)
      input _ _ (fun _ _ _ _ _ h => (expr_stable input h).1)
      (RangeCheck.computableWitnesses _ _ _) env env'
  · exact CWHelpers.assertion_structuralComputableWitnesses_of_condition
      (RangeCheck.circuit ut0bits ut0bits_valid ut0bits_pos)
      input _ _ (fun _ _ _ _ _ h => (expr_stable input h).2.1)
      (RangeCheck.computableWitnesses _ _ _) env env'
  · exact CWHelpers.assertion_structuralComputableWitnesses_of_condition
      (RangeCheck.circuit ut1bits ut1bits_valid ut1bits_pos)
      input _ _ (fun _ _ _ _ _ h => (expr_stable input h).2.2)
      (RangeCheck.computableWitnesses _ _ _) env env'

lemma model (i : fields 3 Field) (L0 L1 L2 : ℤ)
    (h0 : l0Min ≤ L0 ∧ L0 ≤ l0Max) (h1 : l1Min ≤ L1 ∧ L1 ≤ l1Max)
    (h2 : l2Min ≤ L2 ∧ L2 ≤ l2Max)
    (hi0 : (i[0]'(by decide)) = (L0 : Field))
    (hi1 : (i[1]'(by decide)) = (L1 : Field))
    (hi2 : (i[2]'(by decide)) = (L2 : Field)) :
    Assumptions i ∧ (Spec i ↔ Sparse32.q ∣ L0 + W96 * L1 + W192 * L2) := by
  have he := uni_centered
  have hhalf : Sparse32.nativeHalf = LazyX.nativeHalf := by
    norm_num [Sparse32.nativeHalf, Sparse32.nativePrime, LazyX.nativeHalf]
  have hl0 : LazyX.lift (i[0]'(by decide)) = L0 := by
    rw [hi0]; apply LazyX.lift_cast; rw [← hhalf]; omega
  have hl1 : LazyX.lift (i[1]'(by decide)) = L1 := by
    rw [hi1]; apply LazyX.lift_cast; rw [← hhalf]; omega
  have hl2 : LazyX.lift (i[2]'(by decide)) = L2 := by
    rw [hi2]; apply LazyX.lift_cast; rw [← hhalf]; omega
  simp only [Assumptions, Spec, hl0, hl1, hl2]
  exact ⟨⟨h0, h1, h2⟩, trivial⟩

lemma localLength (i : Var (fields 3) Field) (o : ℕ) :
    (main i).localLength o = ukbits + ut0bits + ut1bits - 3 := by
  simp only [main, RangeCheck.circuit, circuit_norm]
  decide

end Solution.Secp256k1ScalarMulFixedBase.LazyVar.Cert3
end

/-! ## merged from `Lazy/Relations.lean` -/
section
/-!
# Integer models of one variable-base chain step

The step computes `(R + T) + R` on a lazy accumulator `R = (x, y)` (eight
signed radix-`2^32` coefficients each, never normalised) and a canonical table
point `T`.  With balanced slope digits `a` (chord or tangent of `(R, T)`) and
`b` (second slope, through the two-slope identity), all quantities are
integer coefficient vectors; this file gives their envelopes and their
evaluations in the secp256k1 base field.
-/

namespace Solution.Secp256k1ScalarMulFixedBase.LazyVar

open Sparse32 SparseX
open Solution.Secp256k1ScalarMul.Lazy

set_option autoImplicit false
set_option maxHeartbeats 4000000

abbrev Field := SmallSquare.Field

/-! ## Integer models -/

def chordZ (a x y : Words ℤ) (Tx Ty : Fin 4 → ℤ) : Words ℤ :=
  fun k => sparseMul a (fun j => embed Tx j - x j) k - embed Ty k + y k

def yeqZ (y : Words ℤ) (Ty : Fin 4 → ℤ) (sgn : ℤ) : Words ℤ :=
  fun k => y k - sgn * embed Ty k

def xSZ (a x : Words ℤ) (Tx : Fin 4 → ℤ) : Words ℤ :=
  fun k => sparseSquare a k - x k - embed Tx k

def xeq1Z (x : Words ℤ) (Tx : Fin 4 → ℤ) : Words ℤ :=
  fun k => x k - embed Tx k

def xeq2Z (a x : Words ℤ) (Tx : Fin 4 → ℤ) : Words ℤ :=
  fun k => xSZ a x Tx k - x k

/-- Unified slope relation `a (y + T.y) − (x² + x T.x + T.x²)`. -/
def uniZ (a x y : Words ℤ) (Tx Ty : Fin 4 → ℤ) : Words ℤ :=
  fun k => sparseMul a (fun j => y j + embed Ty j) k -
    (sparseSquare x k + sparseMul x (embed Tx) k + sparseSquare (embed Tx) k)

/-- The second relation `(a + b)(x − xS) − 2y` (two-slope identity). -/
def rel2Z' (a b x y : Words ℤ) (Tx : Fin 4 → ℤ) : Words ℤ :=
  fun k => sparseMul (fun j => a j + b j) (fun j => x j - xSZ a x Tx j) k - 2 * y k

def xPZ (a b : Words ℤ) (Tx : Fin 4 → ℤ) : Words ℤ :=
  fun k => sparseSquare b k - sparseSquare a k + embed Tx k

def yPZ (a b x y : Words ℤ) (Tx : Fin 4 → ℤ) : Words ℤ :=
  fun k => sparseMul b (fun j => x j - xPZ a b Tx j) k - y k

/-! ## Envelopes -/

def Digits (a : Words ℤ) : Prop := ∀ i, -m ≤ a i ∧ a i ≤ m - 1
def Canon (T : Fin 4 → ℤ) : Prop := ∀ i, 0 ≤ T i ∧ T i ≤ wordMax
def XIn (x : Words ℤ) : Prop := ∀ i, xLo i ≤ x i ∧ x i ≤ xHi i
def YIn (n : ℕ) (y : Words ℤ) : Prop := ∀ i, yLoAt n i ≤ y i ∧ y i ≤ yHiAt n i

lemma yIn_steady {n : ℕ} (hn : n ≤ depth) {y : Words ℤ} (hy : YIn n y) :
    ∀ i, yLo i ≤ y i ∧ y i ≤ yHi i := by
  intro i
  have h := yBounds_steady hn i
  have := hy i
  exact ⟨h.1.trans this.1, this.2.trans h.2⟩

lemma embed_in {T : Fin 4 → ℤ} (hT : Canon T) : ∀ i, embLo i ≤ embed T i ∧ embed T i ≤ embHi i :=
  embed_interval T hT

lemma chord_bounds {a x y : Words ℤ} {Tx Ty : Fin 4 → ℤ} {n : ℕ} (hn : n ≤ depth)
    (ha : Digits a) (hx : XIn x) (hy : YIn n y) (hTx : Canon Tx) (hTy : Canon Ty) :
    ∀ k, chordLo k ≤ chordZ a x y Tx Ty k ∧ chordZ a x y Tx Ty k ≤ chordHi k := by
  intro k
  have hd : ∀ j, wsub embLo xHi j ≤ embed Tx j - x j ∧ embed Tx j - x j ≤ wsub embHi xLo j :=
    fun j => sub_interval (embed_in hTx) hx j
  have hp := sparseMul_interval digLo digHi (wsub embLo xHi) (wsub embHi xLo) a
    (fun j => embed Tx j - x j) (digits_interval a ha) hd k
  have hty := embed_in hTy k
  have hyk := yIn_steady hn hy k
  simp only [chordLo, chordHi, chordZ, wadd, wsub]
  omega

lemma rel1_of_chord {a x y : Words ℤ} {Tx Ty : Fin 4 → ℤ} {n : ℕ} (hn : n ≤ depth)
    (ha : Digits a) (hx : XIn x) (hy : YIn n y) (hTx : Canon Tx) (hTy : Canon Ty) :
    ∀ k, slotLo .rel1 k ≤ chordZ a x y Tx Ty k ∧ chordZ a x y Tx Ty k ≤ slotHi .rel1 k := by
  intro k
  have h := chord_bounds hn ha hx hy hTx hTy k
  simp only [slotLo, slotHi, rel1Lo, rel1Hi, wmin, wmax]
  constructor
  · exact (min_le_left _ _).trans ((min_le_left _ _).trans h.1)
  · exact h.2.trans ((le_max_left _ _).trans (le_max_left _ _))

lemma rel1_of_xeq1 {x : Words ℤ} {Tx : Fin 4 → ℤ} (hx : XIn x) (hTx : Canon Tx) :
    ∀ k, slotLo .rel1 k ≤ xeq1Z x Tx k ∧ xeq1Z x Tx k ≤ slotHi .rel1 k := by
  intro k
  have hxk := hx k
  have htk := embed_in hTx k
  simp only [slotLo, slotHi, rel1Lo, rel1Hi, xeq1Lo, xeq1Hi, xeq1Z, wmin, wmax, wsub, embLo] at *
  constructor
  · exact (min_le_left _ _).trans ((min_le_right _ _).trans (by omega))
  · exact le_trans (by omega) ((le_max_right _ _).trans (le_max_left _ _))

lemma slot_zero (l : VarLayout) : ∀ k, slotLo l k ≤ 0 ∧ 0 ≤ slotHi l k := by
  intro k
  cases l <;> simp [slotLo, slotHi, rel1Lo, rel1Hi, xeqLo, xeqHi, rel2Lo, rel2Hi, finLo, finHi,
    wmin, wmax, wzero]

lemma uni_zero : ∀ k, uniLo k ≤ 0 ∧ 0 ≤ uniHi k := by
  intro k
  simp [uniLo, uniHi, wmin, wmax, wzero]

lemma xS_bounds {a x : Words ℤ} {Tx : Fin 4 → ℤ}
    (ha : Digits a) (hx : XIn x) (hTx : Canon Tx) :
    ∀ k, xSLo k ≤ xSZ a x Tx k ∧ xSZ a x Tx k ≤ xSHi k := by
  intro k
  have hs := sparseSquare_interval digLo digHi a (digits_interval a ha) k
  have hxk := hx k
  have htk := embed_in hTx k
  simp only [xSLo, xSHi, xSZ, wsub]
  omega

lemma xeq2_bounds {a x : Words ℤ} {Tx : Fin 4 → ℤ}
    (ha : Digits a) (hx : XIn x) (hTx : Canon Tx) :
    ∀ k, slotLo .xeq k ≤ xeq2Z a x Tx k ∧ xeq2Z a x Tx k ≤ slotHi .xeq k := by
  intro k
  have hs := xS_bounds ha hx hTx k
  have hxk := hx k
  simp only [slotLo, slotHi, xeqLo, xeqHi, xeq2Z, wmin, wmax, wsub] at *
  constructor
  · exact (min_le_left _ _).trans (by omega)
  · exact le_trans (by omega) (le_max_left _ _)

lemma uni_bounds {a x y : Words ℤ} {Tx Ty : Fin 4 → ℤ} {n : ℕ} (hn : n ≤ depth)
    (ha : Digits a) (hx : XIn x) (hy : YIn n y) (hTx : Canon Tx) (hTy : Canon Ty) :
    ∀ k, uniLo k ≤ uniZ a x y Tx Ty k ∧ uniZ a x y Tx Ty k ≤ uniHi k := by
  intro k
  have hys := yIn_steady hn hy
  have hs : ∀ j, wadd yLo embLo j ≤ y j + embed Ty j ∧ y j + embed Ty j ≤ wadd yHi embHi j :=
    fun j => add_interval hys (embed_in hTy) j
  have hp := sparseMul_interval digLo digHi (wadd yLo embLo) (wadd yHi embHi) a
    (fun j => y j + embed Ty j) (digits_interval a ha) hs k
  have hsx := sparseSquare_interval xLo xHi x hx k
  have hpx := sparseMul_interval xLo xHi embLo embHi x (embed Tx) hx (embed_in hTx) k
  have hst := sparseSquare_interval embLo embHi (embed Tx) (embed_in hTx) k
  simp only [uniLo, uniHi, uniRawLo, uniRawHi, uniZ, wmin, wmax, wsub] at *
  constructor
  · exact (min_le_left _ _).trans ((min_le_left _ _).trans (by omega))
  · exact le_trans (by omega) ((le_max_left _ _).trans (le_max_left _ _))

lemma uni_of_yeq {y : Words ℤ} {Ty : Fin 4 → ℤ} {n : ℕ} (hn : n ≤ depth)
    (hy : YIn n y) (hTy : Canon Ty) :
    ∀ k, uniLo k ≤ yeqZ y Ty (-1) k ∧ yeqZ y Ty (-1) k ≤ uniHi k := by
  intro k
  have hty := embed_in hTy k
  have hyk := yIn_steady hn hy k
  simp only [uniLo, uniHi, yeqLo, yeqHi, yeqZ, wmin, wmax, wadd, embLo] at *
  constructor
  · exact (min_le_left _ _).trans ((min_le_right _ _).trans (by omega))
  · exact le_trans (by omega) ((le_max_right _ _).trans (le_max_left _ _))

lemma rel2_bounds {a b x y : Words ℤ} {Tx : Fin 4 → ℤ} {n : ℕ} (hn : n ≤ depth)
    (ha : Digits a) (hb : Digits b) (hx : XIn x) (hy : YIn n y) (hTx : Canon Tx) :
    ∀ k, slotLo .rel2 k ≤ rel2Z' a b x y Tx k ∧ rel2Z' a b x y Tx k ≤ slotHi .rel2 k := by
  intro k
  have hxs := xS_bounds ha hx hTx
  have hd : ∀ j, wsub xLo xSHi j ≤ x j - xSZ a x Tx j ∧ x j - xSZ a x Tx j ≤ wsub xHi xSLo j :=
    fun j => sub_interval hx hxs j
  have hp := sparseMul_interval dig2Lo dig2Hi (wsub xLo xSHi) (wsub xHi xSLo)
    (fun j => a j + b j) (fun j => x j - xSZ a x Tx j) (digits2_interval a b ha hb) hd k
  have hyk := yIn_steady hn hy k
  simp only [slotLo, slotHi, rel2Lo, rel2Hi, rel2Z', wmin, wmax, wsub, wscale] at *
  constructor
  · exact (min_le_left _ _).trans (by omega)
  · exact le_trans (by omega) (le_max_left _ _)

lemma xP_bounds {a b : Words ℤ} {Tx : Fin 4 → ℤ}
    (ha : Digits a) (hb : Digits b) (hTx : Canon Tx) : XIn (xPZ a b Tx) := by
  intro k
  have hsa := sparseSquare_interval digLo digHi a (digits_interval a ha) k
  have hsb := sparseSquare_interval digLo digHi b (digits_interval b hb) k
  have htk := embed_in hTx k
  simp only [xLo, xHi, xPZ, wsub, wadd, embLo] at *
  omega

lemma xLo_nonpos (k : Fin 8) : xLo k ≤ 0 ∧ embHi k ≤ xHi k := by
  have := sparseSquare_interval digLo digHi digLo (digits_interval _ (fun _ => by
    simp only [digLo]; constructor <;> norm_num [m])) k
  simp only [xLo, xHi, wsub, wadd, sqLo, sqHi] at *
  omega

lemma xIn_embed {Tx : Fin 4 → ℤ} (hTx : Canon Tx) : XIn (embed Tx) := by
  intro k
  have h := embed_in hTx k
  have h0 := xLo_nonpos k
  simp only [embLo] at h
  exact ⟨h0.1.trans h.1, h.2.trans h0.2⟩

lemma xIn_zero : XIn (fun _ => 0) := by
  intro k
  show xLo k ≤ 0 ∧ 0 ≤ xHi k
  have h0 := xLo_nonpos k
  have := dcap_nonneg k
  simp only [embHi] at h0
  exact ⟨h0.1, by omega⟩

lemma yP_bounds {a b x y : Words ℤ} {Tx : Fin 4 → ℤ} {n : ℕ}
    (ha : Digits a) (hb : Digits b) (hx : XIn x) (hy : YIn n y) (hTx : Canon Tx) :
    YIn (n+1) (yPZ a b x y Tx) := by
  intro k
  have hxp := xP_bounds ha hb hTx
  have hd : ∀ j, wsub xLo xHi j ≤ x j - xPZ a b Tx j ∧ x j - xPZ a b Tx j ≤ wsub xHi xLo j :=
    fun j => sub_interval hx hxp j
  have hp := sparseMul_interval digLo digHi (wsub xLo xHi) (wsub xHi xLo) b
    (fun j => x j - xPZ a b Tx j) (digits_interval b hb) hd k
  have hyk := hy k
  rw [(yBounds_step n k).1, (yBounds_step n k).2]
  simp only [yPZ, yStepLo, yStepHi] at *
  constructor
  · exact (min_le_left _ _).trans ((min_le_left _ _).trans (by omega))
  · exact le_trans (by omega) ((le_max_left _ _).trans (le_max_left _ _))

lemma yIn_succ_of {n : ℕ} {y : Words ℤ} (hy : YIn n y) : YIn (n+1) y := by
  intro k
  have := hy k
  have hm := yBounds_mono n k
  exact ⟨hm.1.trans this.1, this.2.trans hm.2⟩

lemma yIn_embed {Ty : Fin 4 → ℤ} (hTy : Canon Ty) (n : ℕ) : YIn n (embed Ty) := by
  intro k
  have h := embed_in hTy k
  have h0 := yBounds_emb_mem n k
  simp only [embLo] at h
  exact ⟨h0.1.trans h.1, h.2.trans h0.2⟩

lemma yIn_zero (n : ℕ) : YIn n (fun _ => 0) := yBounds_zero_mem n

/-! ## Field semantics -/

abbrev Fp := Specs.Secp256k1.Fp

def valZ (w : Words ℤ) : Fp := ((Sparse32.eval w Sparse32.H : ℤ) : Fp)

def slopeFp (a : Words ℤ) : Fp :=
  Sparse32.eval (fun k => (a k : Fp)) (Sparse32.H : Fp)

lemma valZ_eq (w : Words ℤ) :
    valZ w = Sparse32.eval (fun i => (w i : Fp)) (Sparse32.H : Fp) := SparseX.eval_cast w

lemma eval_add' {K : Type*} [CommRing K] (a b : Words K) (r : K) :
    Sparse32.eval (fun i => a i + b i) r = Sparse32.eval a r + Sparse32.eval b r := by
  simp only [Sparse32.eval, add_mul, Finset.sum_add_distrib]

lemma eval_smul' {K : Type*} [CommRing K] (s : K) (a : Words K) (r : K) :
    Sparse32.eval (fun i => s * a i) r = s * Sparse32.eval a r := by
  simp only [Sparse32.eval, Finset.mul_sum, mul_assoc]

lemma valZ_sub (a b : Words ℤ) : valZ (fun i => a i - b i) = valZ a - valZ b := by
  unfold valZ; rw [SparseX.eval_sub]; push_cast; rfl

lemma valZ_add (a b : Words ℤ) : valZ (fun i => a i + b i) = valZ a + valZ b := by
  unfold valZ; rw [eval_add']; push_cast; rfl

lemma valZ_smul (s : ℤ) (a : Words ℤ) : valZ (fun i => s * a i) = (s : Fp) * valZ a := by
  unfold valZ; rw [eval_smul']; push_cast; rfl

lemma valZ_mul (a b : Words ℤ) : valZ (sparseMul a b) = valZ a * valZ b := by
  unfold valZ
  rw [SparseX.eval_cast]
  have hm : (fun k => ((sparseMul a b k : ℤ) : Fp)) =
      sparseMul (fun k => (a k : Fp)) (fun k => (b k : Fp)) := by
    funext k
    exact (sparseMul_map (Int.castRingHom Fp) a b k).symm
  rw [hm, eval_sparseMul _ _ _ SparseX.curve_root, ← SparseX.eval_cast a, ← SparseX.eval_cast b]

lemma valZ_sq (a : Words ℤ) : valZ (sparseSquare a) = valZ a * valZ a := valZ_mul a a

lemma valZ_embed (T : Emu Field) : valZ (embed (emuz T)) = decodeFe T := by
  unfold valZ
  rw [SparseX.embed_value]
  rfl

lemma valZ_fun_sub (f g : Words ℤ) : valZ (fun i => f i - g i) = valZ f - valZ g := valZ_sub f g

lemma dvd_iff (w : Words ℤ) : Sparse32.q ∣ Sparse32.eval w Sparse32.H ↔ valZ w = 0 :=
  SparseX.dvd_q_iff _

/-- Chord relation: `a (Tx − x) − Ty + y`. -/
lemma chordZ_value (a x y : Words ℤ) (Tx Ty : Emu Field) :
    valZ (chordZ a x y (emuz Tx) (emuz Ty)) =
      valZ a * (decodeFe Tx - valZ x) - decodeFe Ty + valZ y := by
  have h1 : chordZ a x y (emuz Tx) (emuz Ty) =
      fun k => (sparseMul a (fun j => embed (emuz Tx) j - x j) k - embed (emuz Ty) k) + y k := by
    funext k; simp only [chordZ]
  rw [h1, valZ_add, valZ_sub, valZ_mul, valZ_sub, valZ_embed, valZ_embed]

lemma yeqZ_value (y : Words ℤ) (Ty : Emu Field) (sgn : ℤ) :
    valZ (yeqZ y (emuz Ty) sgn) = valZ y - (sgn : Fp) * decodeFe Ty := by
  have h1 : yeqZ y (emuz Ty) sgn = fun k => y k - sgn * embed (emuz Ty) k := rfl
  rw [h1, valZ_sub, valZ_smul, valZ_embed]

lemma xSZ_value (a x : Words ℤ) (Tx : Emu Field) :
    valZ (xSZ a x (emuz Tx)) = valZ a * valZ a - valZ x - decodeFe Tx := by
  have h1 : xSZ a x (emuz Tx) = fun k => (sparseSquare a k - x k) - embed (emuz Tx) k := rfl
  rw [h1, valZ_sub, valZ_sub, valZ_sq, valZ_embed]

lemma xeq1Z_value (x : Words ℤ) (Tx : Emu Field) :
    valZ (xeq1Z x (emuz Tx)) = valZ x - decodeFe Tx := by
  have h1 : xeq1Z x (emuz Tx) = fun k => x k - embed (emuz Tx) k := rfl
  rw [h1, valZ_sub, valZ_embed]

lemma xeq2Z_value (a x : Words ℤ) (Tx : Emu Field) :
    valZ (xeq2Z a x (emuz Tx)) = valZ (xSZ a x (emuz Tx)) - valZ x := by
  have h1 : xeq2Z a x (emuz Tx) = fun k => xSZ a x (emuz Tx) k - x k := rfl
  rw [h1, valZ_sub]

lemma uniZ_value (a x y : Words ℤ) (Tx Ty : Emu Field) :
    valZ (uniZ a x y (emuz Tx) (emuz Ty)) =
      valZ a * (valZ y + decodeFe Ty) -
        (valZ x * valZ x + valZ x * decodeFe Tx + decodeFe Tx * decodeFe Tx) := by
  have h1 : uniZ a x y (emuz Tx) (emuz Ty) =
      fun k => sparseMul a (fun j => y j + embed (emuz Ty) j) k -
        ((sparseSquare x k + sparseMul x (embed (emuz Tx)) k) + sparseSquare (embed (emuz Tx)) k) := rfl
  rw [h1, valZ_sub, valZ_mul, valZ_add, valZ_add, valZ_add, valZ_sq, valZ_mul, valZ_sq,
    valZ_embed, valZ_embed]

lemma rel2Z_value (a b x y : Words ℤ) (Tx : Emu Field) :
    valZ (rel2Z' a b x y (emuz Tx)) =
      (valZ a + valZ b) * (valZ x - valZ (xSZ a x (emuz Tx))) - 2 * valZ y := by
  have h1 : rel2Z' a b x y (emuz Tx) =
      fun k => sparseMul (fun j => a j + b j) (fun j => x j - xSZ a x (emuz Tx) j) k -
        2 * y k := rfl
  rw [h1, valZ_sub, valZ_mul, valZ_add, valZ_sub, valZ_smul]
  push_cast; ring

lemma xPZ_value (a b : Words ℤ) (Tx : Emu Field) :
    valZ (xPZ a b (emuz Tx)) = valZ b * valZ b - valZ a * valZ a + decodeFe Tx := by
  have h1 : xPZ a b (emuz Tx) = fun k => (sparseSquare b k - sparseSquare a k) + embed (emuz Tx) k := rfl
  rw [h1, valZ_add, valZ_sub, valZ_sq, valZ_sq, valZ_embed]

lemma yPZ_value (a b x y : Words ℤ) (Tx : Emu Field) :
    valZ (yPZ a b x y (emuz Tx)) = valZ b * (valZ x - valZ (xPZ a b (emuz Tx))) - valZ y := by
  have h1 : yPZ a b x y (emuz Tx) =
      fun k => sparseMul b (fun j => x j - xPZ a b (emuz Tx) j) k - y k := rfl
  rw [h1, valZ_sub, valZ_mul, valZ_sub]

/-! ## Casting field-level vectors to their integer models -/

lemma sparseMul_cast (U V : Words ℤ) (u v : Fin 8 → Field)
    (hu : ∀ k, u k = (U k : Field)) (hv : ∀ k, v k = (V k : Field)) (k : Fin 8) :
    sparseMul u v k = ((sparseMul U V k : ℤ) : Field) := by
  have hu' : u = fun k => ((U k : ℤ) : Field) := funext hu
  have hv' : v = fun k => ((V k : ℤ) : Field) := funext hv
  rw [hu', hv']
  exact sparseMul_map (Int.castRingHom Field) U V k

lemma zwords_cast (x : fields 8 Field) (k : Fin 8) : x[k.val] = ((zwords x k : ℤ) : Field) := by
  simp only [zwords, LazyX.cast_lift]

lemma digitsZ_cast (a : fields 8 Field) (k : Fin 8) : a[k.val] = ((digitsZ a k : ℤ) : Field) := by
  simp only [digitsZ, LazyX.cast_lift]

lemma embedVec_cast (u : Emu Field) (k : Fin 8) :
    (embedVec u)[k.val] = ((embed (emuz u) k : ℤ) : Field) := by
  simp only [embedVec, Vector.getElem_ofFn, embed, emuz]
  split_ifs <;> simp only [Int.cast_zero, Int.cast_natCast, FoldQuot.natCast_val_F]

lemma lowHalf_cast (Z : Words ℤ) :
    lowHalf (fun k => ((Z k : ℤ) : Field)) = ((lowHalf Z : ℤ) : Field) := by
  simp only [lowHalf]; push_cast; rfl

lemma highHalf_cast (Z : Words ℤ) :
    highHalf (fun k => ((Z k : ℤ) : Field)) = ((highHalf Z : ℤ) : Field) := by
  simp only [highHalf]; push_cast; rfl

lemma limb0_cast (Z : Words ℤ) :
    limb0 (fun k => ((Z k : ℤ) : Field)) = ((limb0 Z : ℤ) : Field) := by
  simp only [limb0]; push_cast; rfl

lemma limb1_cast (Z : Words ℤ) :
    limb1 (fun k => ((Z k : ℤ) : Field)) = ((limb1 Z : ℤ) : Field) := by
  simp only [limb1]; push_cast; rfl

lemma limb2_cast (Z : Words ℤ) :
    limb2 (fun k => ((Z k : ℤ) : Field)) = ((limb2 Z : ℤ) : Field) := by
  simp only [limb2]; push_cast; rfl

/-- Lifting an integer-valued word vector back: needed to feed lazy outputs into
the next step's model. -/
lemma zwords_of_cast (Z : Words ℤ) (v : fields 8 Field)
    (hv : ∀ k, v[k.val] = ((Z k : ℤ) : Field))
    (hb : ∀ k, -LazyX.nativeHalf ≤ Z k ∧ Z k ≤ LazyX.nativeHalf) :
    zwords v = Z := by
  funext k
  simp only [zwords, hv k]
  exact LazyX.lift_cast _ (hb k)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
private lemma xLo_native : ∀ k : Fin 8, -LazyX.nativeHalf ≤ xLo k ∧ xHi k ≤ LazyX.nativeHalf := by
  decide

set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
private lemma yLo_native : ∀ k : Fin 8, -LazyX.nativeHalf ≤ yLo k ∧ yHi k ≤ LazyX.nativeHalf := by
  decide

lemma xIn_native {x : Words ℤ} (hx : XIn x) (k : Fin 8) :
    -LazyX.nativeHalf ≤ x k ∧ x k ≤ LazyX.nativeHalf := by
  have h := hx k
  have hc := xLo_native k
  omega

lemma yIn_native {n : ℕ} (hn : n ≤ depth) {y : Words ℤ} (hy : YIn n y) (k : Fin 8) :
    -LazyX.nativeHalf ≤ y k ∧ y k ≤ LazyX.nativeHalf := by
  have h := yIn_steady hn hy k
  have hc := yLo_native k
  omega

end Solution.Secp256k1ScalarMulFixedBase.LazyVar
end

/-! ## merged from `Lazy/MulCell.lean` -/
section
/-!
# One rank-1 product cell `v = p · q`

Used for the flag muxes of the certificate contents and the output muxes.
-/

namespace Solution.Secp256k1ScalarMulFixedBase.LazyVar.MulCell

open SmallSquare Challenge.CostR1CS Cost
open Challenge.Utils.ComputableWitnessLemmas

set_option autoImplicit false

structure Inputs (F : Type) where
  p : F
  q : F
deriving ProvableStruct

def main (i : Var Inputs Field) : Circuit Field (Var field Field) := do
  let v ← ProvableType.witness (α := field) fun env =>
    let iv : Inputs Field := eval env i
    iv.p * iv.q
  Circuit.assertZero (v - i.p * i.q)
  return v

instance elaborated : ElaboratedCircuit Field Inputs field main := by
  elaborate_circuit

def Assumptions (_ : Inputs Field) : Prop := True

def Spec (i : Inputs Field) (o : Field) : Prop := o = i.p * i.q

theorem soundness : Soundness Field main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨hp, hq⟩ := h_input
  linear_combination h_holds

theorem completeness : Completeness Field main Assumptions := by
  circuit_proof_start
  obtain ⟨hp, hq⟩ := h_input
  rw [h_env]
  ring

def circuit : FormalCircuit Field Inputs field where
  main := main
  elaborated := elaborated
  Assumptions := Assumptions
  Spec := Spec
  soundness := soundness
  completeness := completeness

theorem costIs_main (i : Var Inputs Field) : CostIs (main i) ⟨1, 1⟩ := by
  rw [show (⟨1, 1⟩ : Count) = ⟨1, 0⟩ + (⟨0, 1⟩ + Count.zero) by decide]
  unfold main
  refine CostIs.bind (CostIs.provableWitness _) fun _ => ?_
  refine CostIs.bind (CostIs.assertZero _) fun _ => ?_
  exact CostIs.pure _

theorem costIs_call (i : Var Inputs Field) : CostIs (subcircuit circuit i) ⟨1, 1⟩ :=
  CostIs.subcircuit (fun n => costIs_main i n)

theorem shape (i : Var Inputs Field) (hp : Affine i.p) (hq : Affine i.q) :
    IsR1CSCirc (main i) := by
  unfold main
  refine IsR1CSCirc.bind_out (IsR1CSCirc.provableWitness _) fun k => ?_
  refine IsR1CSCirc.bind (IsR1CSCirc.assertZero ?_) fun _ => IsR1CSCirc.pure _
  exact isR1CSRow_sub_mul (Affine.var ⟨k⟩) hp hq

theorem shape_call (i : Var Inputs Field) (hp : Affine i.p) (hq : Affine i.q) :
    IsR1CSCirc (subcircuit circuit i) :=
  IsR1CSCirc.subcircuit (fun n => shape i hp hq n)

theorem call_output (i : Var Inputs Field) (n : ℕ) :
    (subcircuit circuit i).output n = varFromOffset field n :=
  (elaborated.output_eq i n).symm

theorem affine_call_output (i : Var Inputs Field) (n : ℕ) :
    Affine ((subcircuit circuit i).output n) := by
  rw [call_output]
  exact Affine.var ⟨n⟩

theorem computableWitnesses : circuit.ComputableWitnesses := by
  intro n input env env'
  change Operations.forAllFlat n (FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations n)
  apply FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  simp only [main, Circuit.bind_structuralComputableWitnesses_iff,
    Circuit.provableWitness_structuralComputableWitnesses_iff,
    Circuit.assertZero_structuralComputableWitnesses_iff,
    Circuit.pure_structuralComputableWitnesses_iff, and_true]
  intro _ hin
  rw [hin]

theorem output_stable (i : Var Inputs Field) (n : ℕ) {k : ℕ}
    {env env' : ProverEnvironment Field} (hag : env.AgreesBelow k env') (hk : n < k) :
    Expression.eval env.toEnvironment ((subcircuit circuit i).output n) =
      Expression.eval env'.toEnvironment ((subcircuit circuit i).output n) := by
  rw [call_output]
  exact hag n hk

end Solution.Secp256k1ScalarMulFixedBase.LazyVar.MulCell
end
