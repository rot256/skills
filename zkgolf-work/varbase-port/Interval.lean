import Solution.Secp256k1ScalarMulFixedBase.UploadPart2
import Solution.Secp256k1ScalarMul.Params

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
  rcases le_or_lt 0 a with ha | ha
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
