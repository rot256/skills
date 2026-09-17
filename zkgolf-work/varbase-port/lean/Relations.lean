import Solution.Secp256k1ScalarMul.Lazy.Cert

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
  cases l <;> simp [slotLo, slotHi, rel1Lo, rel1Hi, xeqLo, xeqHi, rel2Lo, rel2Hi,
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

end Solution.Secp256k1ScalarMulFixedBase.LazyVar
