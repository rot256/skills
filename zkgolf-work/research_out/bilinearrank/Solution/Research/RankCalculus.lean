/-
  # Elementary calculus of bilinear decompositions

  Padding, additivity, double sums, and the key *factorisation* lemma: a bilinear map
  whose left and right kernels contain the kernels of two linear maps into
  finite-dimensional spaces has rank at most the product of those dimensions.
-/
import Solution.Research.Model

namespace Solution.Research

open Module

variable {F : Type*} [Field F] {m n p : ℕ}

/-- A decomposition with `r` products is also a decomposition with `r' ≥ r` products. -/
lemma HasRankLE.mono {f : Vec F m → Vec F n → Vec F p} {r r' : ℕ}
    (h : HasRankLE f r) (hr : r ≤ r') : HasRankLE f r' := by
  obtain ⟨φ, ψ, w, hf⟩ := h
  classical
  refine ⟨fun k => if k < r then φ k else 0, fun k => if k < r then ψ k else 0, w, fun x y => ?_⟩
  have hsub : ∑ k ∈ Finset.range r', ((if k < r then φ k else 0) x *
      (if k < r then ψ k else 0) y) • w k
      = ∑ k ∈ Finset.range r, ((if k < r then φ k else 0) x *
      (if k < r then ψ k else 0) y) • w k := by
    refine (Finset.sum_subset (Finset.range_mono hr) ?_).symm
    intro k _ hk
    simp only [Finset.mem_range, not_lt] at hk
    simp [Nat.not_lt.2 hk]
  rw [hsub, hf x y]
  exact Finset.sum_congr rfl fun k hk => by simp [Finset.mem_range.1 hk]

/-- The zero map has rank `0`. -/
lemma hasRankLE_zero (f : Vec F m → Vec F n → Vec F p) (h : ∀ x y, f x y = 0) :
    HasRankLE f 0 := ⟨0, 0, 0, by simp [h]⟩

/-- Rank is subadditive. -/
lemma HasRankLE.add {f f₁ f₂ : Vec F m → Vec F n → Vec F p} {r₁ r₂ : ℕ}
    (h : ∀ x y, f x y = f₁ x y + f₂ x y) (h₁ : HasRankLE f₁ r₁) (h₂ : HasRankLE f₂ r₂) :
    HasRankLE f (r₁ + r₂) := by
  obtain ⟨φ₁, ψ₁, w₁, hf₁⟩ := h₁
  obtain ⟨φ₂, ψ₂, w₂, hf₂⟩ := h₂
  classical
  refine ⟨fun k => if k < r₁ then φ₁ k else φ₂ (k - r₁),
          fun k => if k < r₁ then ψ₁ k else ψ₂ (k - r₁),
          fun k => if k < r₁ then w₁ k else w₂ (k - r₁), fun x y => ?_⟩
  rw [Finset.sum_range_add, h x y, hf₁ x y, hf₂ x y]
  congr 1
  · exact Finset.sum_congr rfl fun k hk => by simp [Finset.mem_range.1 hk]
  · refine Finset.sum_congr rfl fun k _ => ?_
    have h1 : ¬ (r₁ + k < r₁) := by omega
    simp [h1]

/-- A double sum of `d * e` rank-one terms is a decomposition with `d * e` products. -/
lemma hasRankLE_doubleSum {f : Vec F m → Vec F n → Vec F p} {d e : ℕ}
    (θ : ℕ → (Vec F m →ₗ[F] F)) (θ' : ℕ → (Vec F n →ₗ[F] F)) (w : ℕ → ℕ → Vec F p)
    (h : ∀ x y, f x y = ∑ i ∈ Finset.range d, ∑ j ∈ Finset.range e, (θ i x * θ' j y) • w i j) :
    HasRankLE f (d * e) := by
  induction d generalizing f with
  | zero => simpa using hasRankLE_zero f (by simpa using h)
  | succ d ih =>
      have h1 : HasRankLE
          (fun x y => ∑ i ∈ Finset.range d, ∑ j ∈ Finset.range e, (θ i x * θ' j y) • w i j)
          (d * e) := ih (fun _ _ => rfl)
      have h2 : HasRankLE (fun x y => ∑ j ∈ Finset.range e, (θ d x * θ' j y) • w d j) e :=
        ⟨fun _ => θ d, θ', w d, fun _ _ => rfl⟩
      have hadd := HasRankLE.add (f := f)
        (fun x y => by rw [h x y, Finset.sum_range_succ]) h1 h2
      simpa [Nat.succ_mul] using hadd

/-- Every linear map into a finite-dimensional space admits a finite "coordinate
approximation": there are `d ≤ finrank F V` linear forms `θ i` and vectors `v i` such
that `x - ∑ i < d, θ i x • v i` always lies in the kernel. -/
lemma exists_coord_approx {M V : Type*} [AddCommGroup M] [Module F M] [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] (Ψ : M →ₗ[F] V) :
    ∃ (d : ℕ) (θ : ℕ → (M →ₗ[F] F)) (v : ℕ → M), d ≤ finrank F V ∧
      ∀ x, Ψ (x - ∑ i ∈ Finset.range d, θ i x • v i) = 0 := by
  classical
  have hsurj : Ψ.rangeRestrict.range = ⊤ := LinearMap.range_rangeRestrict Ψ
  obtain ⟨σ, hσ⟩ := LinearMap.exists_rightInverse_of_surjective Ψ.rangeRestrict hsurj
  have hσ' : ∀ z, Ψ.rangeRestrict (σ z) = z := fun z => congrArg (fun L => L z) hσ
  set d := finrank F (LinearMap.range Ψ) with hd
  set b := Module.finBasis F (LinearMap.range Ψ) with hb
  refine ⟨d, fun i => if h : i < d then (b.coord ⟨i, h⟩) ∘ₗ Ψ.rangeRestrict else 0,
          fun i => if h : i < d then σ (b ⟨i, h⟩) else 0, Submodule.finrank_le _, fun x => ?_⟩
  have hrange : ∑ i ∈ Finset.range d,
      (if h : i < d then (b.coord ⟨i, h⟩) ∘ₗ Ψ.rangeRestrict else 0) x •
        (if h : i < d then σ (b ⟨i, h⟩) else 0)
      = ∑ i : Fin d, (b.repr (Ψ.rangeRestrict x) i) • σ (b i) := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => (if h : i < d then (b.coord ⟨i, h⟩) ∘ₗ
      Ψ.rangeRestrict else 0) x • (if h : i < d then σ (b ⟨i, h⟩) else 0)) d]
    exact Finset.sum_congr rfl fun i _ => by simp
  rw [hrange]
  have key : Ψ.rangeRestrict (x - ∑ i : Fin d, (b.repr (Ψ.rangeRestrict x) i) • σ (b i)) = 0 := by
    rw [map_sub, map_sum]
    simp only [map_smul, hσ']
    rw [Basis.sum_repr b (Ψ.rangeRestrict x), sub_self]
  have := congrArg (Subtype.val) key
  simpa using this

/-- **Factorisation bound.** If the kernel of a linear map `Ψx` into a finite-dimensional
space `Vx` annihilates `f` on the left, and similarly on the right, then the tensor rank
of `f` is at most `finrank Vx * finrank Vy`.

This is the engine of the lower bound: nondeterminism and intermediate witnesses cannot
make a bilinear map depend on more than the (few) affine coordinates its rows see. -/
theorem hasRankLE_of_kernel_factor {Vx Vy : Type*} [AddCommGroup Vx] [Module F Vx]
    [AddCommGroup Vy] [Module F Vy] [FiniteDimensional F Vx] [FiniteDimensional F Vy]
    (f : BilMap F m n p) (Ψx : Vec F m →ₗ[F] Vx) (Ψy : Vec F n →ₗ[F] Vy)
    (hx : ∀ x, Ψx x = 0 → ∀ y, f x y = 0)
    (hy : ∀ y, Ψy y = 0 → ∀ x, f x y = 0) :
    HasRankLE (fun x y => f x y) (finrank F Vx * finrank F Vy) := by
  obtain ⟨d, θ, v, hd, hax⟩ := exists_coord_approx Ψx
  obtain ⟨e, θ', v', he, hay⟩ := exists_coord_approx Ψy
  have key : ∀ x y, f x y
      = ∑ i ∈ Finset.range d, ∑ j ∈ Finset.range e, (θ i x * θ' j y) • f (v i) (v' j) := by
    intro x y
    have h1 : ∀ y', f x y' = f (∑ i ∈ Finset.range d, θ i x • v i) y' := by
      intro y'
      have h := hx _ (hax x) y'
      rw [map_sub] at h
      simp only [LinearMap.sub_apply, sub_eq_zero] at h
      exact h
    have h2 : ∀ x', f x' y = f x' (∑ j ∈ Finset.range e, θ' j y • v' j) := by
      intro x'
      have h := hy _ (hay y) x'
      rw [map_sub] at h
      simp only [sub_eq_zero] at h
      exact h
    rw [h1 y, map_sum]
    simp only [LinearMap.sum_apply, map_smul, LinearMap.smul_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [h2 (v i), map_sum]
    simp only [map_smul, Finset.smul_sum, smul_smul]
  exact (hasRankLE_doubleSum θ θ' (fun i j => f (v i) (v' j)) key).mono
    (Nat.mul_le_mul hd he)

end Solution.Research
