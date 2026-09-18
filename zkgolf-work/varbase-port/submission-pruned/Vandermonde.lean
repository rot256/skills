import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Basic

namespace Solution.Secp256k1ScalarMul

open Polynomial

noncomputable def coeffPoly {K : Type*} [CommRing K] {N : ℕ} (coeffs : Fin N → K) : K[X] :=
  ∑ k : Fin N, Polynomial.monomial k.val (coeffs k)

lemma coeffPoly_eval {K : Type*} [CommRing K] {N : ℕ} (coeffs : Fin N → K) (x : K) :
    (coeffPoly coeffs).eval x = ∑ k : Fin N, coeffs k * x ^ k.val := by
  simp only [coeffPoly, eval_finset_sum, eval_monomial]

lemma coeffPoly_natDegree_lt {K : Type*} [CommRing K] {N : ℕ} (hN : 0 < N) (coeffs : Fin N → K) :
    (coeffPoly coeffs).natDegree < N := by
  have hle : (coeffPoly coeffs).natDegree ≤ N - 1 := by
    refine natDegree_sum_le_of_forall_le _ _ (fun k _ => ?_)
    exact (natDegree_monomial_le _).trans (by have := k.isLt; omega)
  omega

lemma coeffPoly_coeff {K : Type*} [CommRing K] {N : ℕ} (coeffs : Fin N → K) (j : Fin N) :
    (coeffPoly coeffs).coeff j.val = coeffs j := by
  simp only [coeffPoly, finset_sum_coeff, coeff_monomial]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    rw [if_neg]
    intro h; exact hb (Fin.ext h)
  · intro h; exact absurd (Finset.mem_univ j) h

lemma cauchy_diag {K : Type*} [CommRing K] {m : ℕ} (hm : 0 < m)
    (a b : Fin m → K) (x : K) :
    (∑ i : Fin m, a i * x ^ i.val) * (∑ j : Fin m, b j * x ^ j.val)
      = ∑ k : Fin (2 * m - 1),
          (∑ i : Fin m, if h : i.val ≤ k.val ∧ k.val - i.val < m then
            a i * b ⟨k.val - i.val, h.2⟩ else 0) * x ^ k.val := by
  rw [Fintype.sum_mul_sum]
  -- LHS = Σ_i Σ_j a_i b_j x^(i+j)
  have hL : (∑ i : Fin m, ∑ j : Fin m, a i * x ^ i.val * (b j * x ^ j.val))
      = ∑ i : Fin m, ∑ j : Fin m, (a i * b j) * x ^ (i.val + j.val) := by
    apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _
    rw [pow_add]; ring
  rw [hL]
  -- RHS: distribute the x^k into the inner sum
  have hR : (∑ k : Fin (2 * m - 1),
        (∑ i : Fin m, if h : i.val ≤ k.val ∧ k.val - i.val < m then
          a i * b ⟨k.val - i.val, h.2⟩ else 0) * x ^ k.val)
      = ∑ k : Fin (2 * m - 1), ∑ i : Fin m,
          if h : i.val ≤ k.val ∧ k.val - i.val < m then
            (a i * b ⟨k.val - i.val, h.2⟩) * x ^ k.val else 0 := by
    apply Finset.sum_congr rfl; intro k _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl; intro i _
    by_cases h : i.val ≤ k.val ∧ k.val - i.val < m
    · rw [dif_pos h, dif_pos h]
    · rw [dif_neg h, dif_neg h, zero_mul]
  rw [hR]
  conv_rhs => rw [Finset.sum_comm]
  -- goal: Σ_i Σ_j a_i b_j x^(i+j) = Σ_i Σ_k (guarded)
  -- for each i, reindex Σ_k (guarded) = Σ_j a_i b_j x^(i+j)
  apply Finset.sum_congr rfl; intro i _
  -- RHS: rewrite the dite-guarded sum over univ as a sum over the filtered set
  classical
  have hfilter : (∑ k : Fin (2 * m - 1),
        if h : i.val ≤ k.val ∧ k.val - i.val < m then
          a i * b ⟨k.val - i.val, h.2⟩ * x ^ k.val else 0)
      = ∑ k ∈ (Finset.univ.filter (fun k : Fin (2 * m - 1) => i.val ≤ k.val ∧ k.val - i.val < m)),
          if h : i.val ≤ k.val ∧ k.val - i.val < m then
            a i * b ⟨k.val - i.val, h.2⟩ * x ^ k.val else 0 := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl; intro k _
    by_cases h : i.val ≤ k.val ∧ k.val - i.val < m
    · rw [dif_pos h, if_pos h]
    · rw [dif_neg h, if_neg h]
  rw [hfilter]
  -- now bijection: j : Fin m ↔ k = i+j in the filter.  s = univ (Fin m), t = filter.
  refine Finset.sum_nbij'
    (i := fun (j : Fin m) => (⟨i.val + j.val, by have := i.isLt; have := j.isLt; omega⟩ : Fin (2 * m - 1)))
    (j := fun (k : Fin (2 * m - 1)) => (⟨min (k.val - i.val) (m - 1), by omega⟩ : Fin m))
    ?hi ?hj ?left_inv ?right_inv ?h
  case hi =>
    intro j _; refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    show i.val ≤ i.val + j.val ∧ (i.val + j.val) - i.val < m
    have := j.isLt; omega
  case hj =>
    intro k hk; exact Finset.mem_univ _
  case left_inv =>
    intro j _
    show (⟨min ((i.val + j.val) - i.val) (m - 1), _⟩ : Fin m) = j
    apply Fin.ext; show min ((i.val + j.val) - i.val) (m - 1) = j.val
    have := j.isLt; omega
  case right_inv =>
    intro k hk; obtain ⟨_, hle, hlt⟩ := Finset.mem_filter.mp hk
    show (⟨i.val + min (k.val - i.val) (m - 1), _⟩ : Fin (2 * m - 1)) = k
    apply Fin.ext; show i.val + min (k.val - i.val) (m - 1) = k.val
    omega
  case h =>
    intro j _
    show a i * b j * x ^ (i.val + j.val)
      = (if h : i.val ≤ (i.val + j.val) ∧ (i.val + j.val) - i.val < m then
          a i * b ⟨(i.val + j.val) - i.val, h.2⟩ * x ^ (i.val + j.val) else 0)
    have hguard : i.val ≤ i.val + j.val ∧ (i.val + j.val) - i.val < m := by
      have := j.isLt; omega
    rw [dif_pos hguard]
    have hbj : (⟨(i.val + j.val) - i.val, hguard.2⟩ : Fin m) = j := by
      apply Fin.ext; show (i.val + j.val) - i.val = j.val; omega
    rw [hbj]

lemma interp_uniqueness {K : Type*} [Field K] {N : ℕ}
    (u v : Fin N → K) (f : Fin N → K) (hf : Function.Injective f)
    (heval : ∀ i : Fin N, (∑ k : Fin N, u k * f i ^ k.val) = ∑ k : Fin N, v k * f i ^ k.val) :
    ∀ j : Fin N, u j = v j := by
  intro j
  have hN : 0 < N := Fin.pos_iff_nonempty.mpr ⟨j⟩
  have hpoly : coeffPoly u = coeffPoly v := by
    apply eq_of_natDegree_lt_card_of_eval_eq _ _ hf
    · intro i
      rw [coeffPoly_eval, coeffPoly_eval]; exact heval i
    · rw [Fintype.card_fin]
      exact max_lt (coeffPoly_natDegree_lt hN u) (coeffPoly_natDegree_lt hN v)
  have := congrArg (fun q => Polynomial.coeff q j.val) hpoly
  simpa only [coeffPoly_coeff] using this

end Solution.Secp256k1ScalarMul
