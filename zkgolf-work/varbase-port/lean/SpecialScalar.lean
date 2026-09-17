import Solution.Secp256k1ScalarMul.ShortCoeffs
import Solution.Secp256k1ScalarMul.CoeffWitness

/-!
# Special scalars

`k` is *special* when some sign pattern `s ∈ {±1}^4` with `s₀ = 1` satisfies
the fake-GLV relation `s₀ + λ s₁ + k (s₂ + λ s₃) ≡ 0`.  For such `k` the
sign-pattern table of the honest bases contains the point at infinity, and the
honest prover uses the pattern itself as its coefficient decomposition.
-/

namespace Solution.Secp256k1ScalarMul.SpecialScalar

open Specs.Secp256k1

def IsSign (z : ℤ) : Prop := z = 1 ∨ z = -1

def Relation (k : ZMod order) (s : Fin 4 → ℤ) : Prop :=
  (s 0 : ZMod order) + (ShortCoeffs.lambdaZ : ZMod order) * s 1 +
    k * ((s 2 : ZMod order) + (ShortCoeffs.lambdaZ : ZMod order) * s 3) = 0

def IsSpecial (k : ZMod order) : Prop :=
  ∃ s : Fin 4 → ℤ, (∀ j, IsSign (s j)) ∧ s 0 = 1 ∧ Relation k s

lemma isSign_natAbs {z : ℤ} (h : IsSign z) : z.natAbs = 1 := by
  rcases h with h | h <;> subst h <;> rfl

lemma isSign_ne_zero {z : ℤ} (h : IsSign z) : z ≠ 0 := by
  rcases h with h | h <;> subst h <;> decide

lemma isSign_neg {z : ℤ} (h : IsSign z) : IsSign (-z) := by
  rcases h with h | h <;> subst h <;> simp [IsSign]

/-- Normalise the first sign to `+1` (the relation is homogeneous). -/
lemma isSpecial_of_pattern (k : ZMod order) (s : Fin 4 → ℤ) (hs : ∀ j, IsSign (s j))
    (hr : Relation k s) : IsSpecial k := by
  rcases hs 0 with h0 | h0
  · exact ⟨s, hs, h0, hr⟩
  · refine ⟨fun j => -s j, fun j => isSign_neg (hs j), by rw [h0]; norm_num, ?_⟩
    unfold Relation at hr ⊢
    push_cast
    linear_combination -hr

noncomputable def specialDecomposition (k : ZMod order) (h : IsSpecial k) :
    ShortCoeffs.Decomposition k :=
  let s := Classical.choose h
  have hs := Classical.choose_spec h
  { u₁ := s 0, u₂ := s 1, v₁ := s 2, v₂ := s 3
    u₁_bound := by rw [isSign_natAbs (hs.1 0)]; decide
    u₂_bound := by rw [isSign_natAbs (hs.1 1)]; decide
    v₁_bound := by rw [isSign_natAbs (hs.1 2)]; decide
    v₂_bound := by rw [isSign_natAbs (hs.1 3)]; decide
    relation := hs.2.2
    v_nonzero := Or.inl (isSign_ne_zero (hs.1 2))
    u₁_nonneg := by rw [hs.2.1]; decide }

lemma specialDecomposition_signs (k : ZMod order) (h : IsSpecial k) :
    IsSign (specialDecomposition k h).u₁ ∧ IsSign (specialDecomposition k h).u₂ ∧
    IsSign (specialDecomposition k h).v₁ ∧ IsSign (specialDecomposition k h).v₂ :=
  ⟨(Classical.choose_spec h).1 0, (Classical.choose_spec h).1 1,
    (Classical.choose_spec h).1 2, (Classical.choose_spec h).1 3⟩

/-- Honest decomposition: the sign pattern for special scalars, otherwise any
short decomposition. -/
noncomputable def decomposition (k : ZMod order) : ShortCoeffs.Decomposition k :=
  if h : IsSpecial k then specialDecomposition k h
  else Classical.choice (ShortCoeffs.exists_decomposition k)

lemma decomposition_special (k : ZMod order) (h : IsSpecial k) :
    decomposition k = specialDecomposition k h := by
  simp only [decomposition, dif_pos h]

end Solution.Secp256k1ScalarMul.SpecialScalar
