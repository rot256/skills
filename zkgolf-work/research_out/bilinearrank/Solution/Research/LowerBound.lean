/-
  # Lower bound: rows control rank, quadratically

  This is the direction where R1CS is genuinely stronger than the classical bilinear
  model: a row's two factors may reference intermediate witnesses, and the witness is
  supplied nondeterministically (only *checked*, never computed).

  Nevertheless the rows cannot hide the input from the output.  Everything an `r`-row
  system knows about `(x, y)` passes through the `3r` affine coefficients
  `(a k, b k, c k)` that the inputs contribute to the rows: two inputs producing the
  same coefficients have literally the same set of satisfying witnesses, hence — by
  soundness and completeness — the same output up to the free affine part.  A bilinear
  map that factors through `3r` linear coordinates on each side has tensor rank at most
  `(3r)² = 9r²`.

  Combined with `minRows_le_tensorRank` this pins the two measures to within a square:
  `minRows f ≤ tensorRank f ≤ 9 * (minRows f)²`.
-/
import Solution.Research.UpperBound

namespace Solution.Research

open Module

variable {F : Type*} [Field F] {m n p : ℕ}

namespace R1CS

variable (S : R1CS F m n p)

/-- The witness `(x, 0, 0)`. -/
def ιx : Vec F m →ₗ[F] Wit F m n S.aux := LinearMap.inl F (Vec F m) (Vec F n × Vec F S.aux)

/-- The witness `(0, y, 0)`. -/
def ιy : Vec F n →ₗ[F] Wit F m n S.aux :=
  (LinearMap.inr F (Vec F m) (Vec F n × Vec F S.aux)) ∘ₗ
    (LinearMap.inl F (Vec F n) (Vec F S.aux))

/-- The witness `(0, 0, u)`. -/
def ιu : Vec F S.aux →ₗ[F] Wit F m n S.aux :=
  (LinearMap.inr F (Vec F m) (Vec F n × Vec F S.aux)) ∘ₗ
    (LinearMap.inr F (Vec F n) (Vec F S.aux))

/-- The `3 * rows` affine coefficients that the left input contributes to the rows. -/
def leftData : Vec F m →ₗ[F] (Fin S.rows → F) × (Fin S.rows → F) × (Fin S.rows → F) :=
  (LinearMap.pi fun k => S.A k ∘ₗ S.ιx).prod
    ((LinearMap.pi fun k => S.B k ∘ₗ S.ιx).prod (LinearMap.pi fun k => S.C k ∘ₗ S.ιx))

/-- The `3 * rows` affine coefficients that the right input contributes to the rows. -/
def rightData : Vec F n →ₗ[F] (Fin S.rows → F) × (Fin S.rows → F) × (Fin S.rows → F) :=
  (LinearMap.pi fun k => S.A k ∘ₗ S.ιy).prod
    ((LinearMap.pi fun k => S.B k ∘ₗ S.ιy).prod (LinearMap.pi fun k => S.C k ∘ₗ S.ιy))

lemma leftData_eq_zero_iff (x : Vec F m) :
    S.leftData x = 0 ↔ ∀ k, S.A k (S.ιx x) = 0 ∧ S.B k (S.ιx x) = 0 ∧ S.C k (S.ιx x) = 0 := by
  simp [leftData, Prod.ext_iff, funext_iff, forall_and]

lemma rightData_eq_zero_iff (y : Vec F n) :
    S.rightData y = 0 ↔ ∀ k, S.A k (S.ιy y) = 0 ∧ S.B k (S.ιy y) = 0 ∧ S.C k (S.ιy y) = 0 := by
  simp [rightData, Prod.ext_iff, funext_iff, forall_and]

lemma split_x (x : Vec F m) (y : Vec F n) (u : Vec F S.aux) :
    ((x, y, u) : Wit F m n S.aux) = S.ιx x + (0, y, u) := by
  simp [ιx]

lemma split_y (x : Vec F m) (y : Vec F n) (u : Vec F S.aux) :
    ((x, y, u) : Wit F m n S.aux) = S.ιy y + (x, 0, u) := by
  simp [ιy]

/-- **Left kernel.** If an input `x₀` contributes nothing to the rows, then `f x₀ · = 0`:
the rows would be unable to distinguish it from `0`, and nondeterminism does not help,
because soundness quantifies over *all* satisfying witnesses. -/
lemma left_kernel (f : BilMap F m n p) (hc : S.Certifies (fun x y => f x y))
    (x₀ : Vec F m) (h : S.leftData x₀ = 0) (y : Vec F n) : f x₀ y = 0 := by
  obtain ⟨hsound, hcomp⟩ := hc
  rw [leftData_eq_zero_iff] at h
  -- the rows cannot see `x₀`
  have hsat : ∀ (y : Vec F n) (u : Vec F S.aux), S.Sat (0, y, u) → S.Sat (x₀, y, u) := by
    intro y u hs k
    have hA : S.A k (x₀, y, u) = S.A k (0, y, u) := by
      rw [S.split_x x₀ y u, map_add, (h k).1, zero_add]
    have hB : S.B k (x₀, y, u) = S.B k (0, y, u) := by
      rw [S.split_x x₀ y u, map_add, (h k).2.1, zero_add]
    have hC : S.C k (x₀, y, u) = S.C k (0, y, u) := by
      rw [S.split_x x₀ y u, map_add, (h k).2.2, zero_add]
    rw [hA, hB, hC]
    exact hs k
  -- hence the output differs from the one at `x = 0` by the fixed vector `Z (x₀,0,0)`
  have key : ∀ y : Vec F n, f x₀ y = S.Z (S.ιx x₀) := by
    intro y
    obtain ⟨u, hu⟩ := hcomp 0 y
    have h1 : S.out (x₀, y, u) = f x₀ y := hsound x₀ y u (hsat y u hu)
    have h2 : S.out (0, y, u) = f 0 y := hsound 0 y u hu
    have h3 : S.out (x₀, y, u) = S.Z (S.ιx x₀) + S.out (0, y, u) := by
      simp only [out]
      rw [S.split_x x₀ y u, map_add]
      abel
    rw [h1, h2] at h3
    simpa using h3
  have h0 := key 0
  simp only [map_zero] at h0
  rw [key y, ← h0]

/-- **Right kernel.** Symmetric statement. -/
lemma right_kernel (f : BilMap F m n p) (hc : S.Certifies (fun x y => f x y))
    (y₀ : Vec F n) (h : S.rightData y₀ = 0) (x : Vec F m) : f x y₀ = 0 := by
  obtain ⟨hsound, hcomp⟩ := hc
  rw [rightData_eq_zero_iff] at h
  have hsat : ∀ (x : Vec F m) (u : Vec F S.aux), S.Sat (x, 0, u) → S.Sat (x, y₀, u) := by
    intro x u hs k
    have hA : S.A k (x, y₀, u) = S.A k (x, 0, u) := by
      rw [S.split_y x y₀ u, map_add, (h k).1, zero_add]
    have hB : S.B k (x, y₀, u) = S.B k (x, 0, u) := by
      rw [S.split_y x y₀ u, map_add, (h k).2.1, zero_add]
    have hC : S.C k (x, y₀, u) = S.C k (x, 0, u) := by
      rw [S.split_y x y₀ u, map_add, (h k).2.2, zero_add]
    rw [hA, hB, hC]
    exact hs k
  have key : ∀ x : Vec F m, f x y₀ = S.Z (S.ιy y₀) := by
    intro x
    obtain ⟨u, hu⟩ := hcomp x 0
    have h1 : S.out (x, y₀, u) = f x y₀ := hsound x y₀ u (hsat x u hu)
    have h2 : S.out (x, 0, u) = f x 0 := hsound x 0 u hu
    have h3 : S.out (x, y₀, u) = S.Z (S.ιy y₀) + S.out (x, 0, u) := by
      simp only [out]
      rw [S.split_y x y₀ u, map_add]
      abel
    rw [h1, h2] at h3
    simpa using h3
  have h0 := key 0
  simp only [map_zero, LinearMap.zero_apply] at h0
  rw [key x, ← h0]

/-- **Nondeterminism cannot smuggle information.** A direction `d` of witness space that
is invisible to every row is invisible to the output as well: soundness quantifies over
*all* satisfying witnesses, so if `u` is a witness then so is `u + d`, and both must
produce the same value. Hence the output functional lies in the span of the `3 * rows`
linear forms the rows use. -/
lemma aux_kernel (f : BilMap F m n p) (hc : S.Certifies (fun x y => f x y))
    (d : Vec F S.aux)
    (h : ∀ k, S.A k (S.ιu d) = 0 ∧ S.B k (S.ιu d) = 0 ∧ S.C k (S.ιu d) = 0) :
    S.Z (S.ιu d) = 0 := by
  obtain ⟨hsound, hcomp⟩ := hc
  obtain ⟨u, hu⟩ := hcomp 0 0
  have hsplit : ((0, 0, u + d) : Wit F m n S.aux) = S.ιu d + (0, 0, u) := by
    simp [ιu, Prod.ext_iff]
    abel
  have hsat : S.Sat (0, 0, u + d) := by
    intro k
    have hA : S.A k (0, 0, u + d) = S.A k (0, 0, u) := by
      rw [hsplit, map_add, (h k).1, zero_add]
    have hB : S.B k (0, 0, u + d) = S.B k (0, 0, u) := by
      rw [hsplit, map_add, (h k).2.1, zero_add]
    have hC : S.C k (0, 0, u + d) = S.C k (0, 0, u) := by
      rw [hsplit, map_add, (h k).2.2, zero_add]
    rw [hA, hB, hC]
    exact hu k
  have h1 : S.out (0, 0, u + d) = f 0 0 := hsound 0 0 (u + d) hsat
  have h2 : S.out (0, 0, u) = f 0 0 := hsound 0 0 u hu
  have h3 : S.out (0, 0, u + d) = S.Z (S.ιu d) + S.out (0, 0, u) := by
    simp only [out]
    rw [hsplit, map_add]
    abel
  rw [h1, h2] at h3
  simpa using h3.symm

end R1CS

lemma finrank_rowData (F : Type*) [Field F] (r : ℕ) :
    finrank F ((Fin r → F) × (Fin r → F) × (Fin r → F)) = 3 * r := by
  simp [Module.finrank_prod]
  ring

/-- **Lower bound.** Any R1CS certificate for a bilinear map `f` with `r` rows forces
`tensorRank f ≤ 9 r²` — intermediate witnesses and nondeterminism cannot buy more than
a quadratic saving. -/
theorem tensorRank_le_of_certifies (f : BilMap F m n p) (S : R1CS F m n p)
    (hc : S.Certifies (fun x y => f x y)) :
    tensorRank (fun x y => f x y) ≤ 9 * S.rows ^ 2 := by
  have h := hasRankLE_of_kernel_factor f S.leftData S.rightData
    (fun x hx y => S.left_kernel f hc x hx y)
    (fun y hy x => S.right_kernel f hc y hy x)
  rw [finrank_rowData] at h
  refine tensorRank_le (h.mono ?_)
  nlinarith [S.rows.zero_le]

/-- **Rank ≤ 9 · rows².** -/
theorem tensorRank_le_nine_mul_minRows_sq (f : BilMap F m n p) :
    tensorRank (fun x y => f x y) ≤ 9 * (minRows (fun x y => f x y)) ^ 2 := by
  obtain ⟨S, hrows, hcert⟩ := hasRowsLE_minRows f
  exact le_trans (tensorRank_le_of_certifies f S hcert)
    (Nat.mul_le_mul_left 9 (Nat.pow_le_pow_left hrows 2))

/-- The empty R1CS system: no rows, no intermediate witnesses, output identically `0`. -/
def emptyR1CS (F : Type*) [Field F] (m n p : ℕ) : R1CS F m n p where
  aux := 0
  rows := 0
  A := Fin.elim0
  B := Fin.elim0
  C := Fin.elim0
  a := Fin.elim0
  b := Fin.elim0
  c := Fin.elim0
  Z := 0
  z₀ := 0

/-- The two measures are equal when either is `0`, and both vanish exactly for `f = 0`. -/
theorem minRows_eq_zero_iff (f : BilMap F m n p) :
    minRows (fun x y => f x y) = 0 ↔ ∀ x y, f x y = 0 := by
  constructor
  · intro h0
    have hr : tensorRank (fun x y => f x y) ≤ 0 := by
      simpa [h0] using tensorRank_le_nine_mul_minRows_sq f
    obtain ⟨φ, ψ, w, hf⟩ := hasRankLE_tensorRank f
    intro x y
    have := hf x y
    rw [Nat.le_zero.1 hr] at this
    simpa using this
  · intro hf
    refine Nat.le_zero.1 (minRows_le ⟨emptyR1CS F m n p, le_rfl, ?_, ?_⟩)
    · intro x y u _
      simp [R1CS.out, emptyR1CS, hf x y]
    · exact fun x y => ⟨0, fun k => Fin.elim0 k⟩

/-- A nonzero bilinear map costs at least one row. -/
theorem one_le_minRows (f : BilMap F m n p) (hf : ∃ x y, f x y ≠ 0) :
    1 ≤ minRows (fun x y => f x y) := by
  rcases Nat.eq_zero_or_pos (minRows (fun x y => f x y)) with h | h
  · obtain ⟨x, y, hxy⟩ := hf
    exact absurd ((minRows_eq_zero_iff f).1 h x y) hxy
  · exact h

end Solution.Research
