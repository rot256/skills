import Solution.Secp256k1ScalarMul.EqViaCarries
import Solution.Secp256k1ScalarMul.RangeCheck

namespace Solution.Secp256k1ScalarMul

section
variable {p : ℕ} [Fact p.Prime]
variable {m : ℕ} [NeZero m]

namespace MulMod

def polyEvalExpr {n : ℕ} (coeffs : Vector (Expression (F p)) n) (x : F p) : Expression (F p) :=
  Fin.foldl n (fun acc (i : Fin n) => acc + coeffs[i.val] * (x ^ i.val : F p)) 0

lemma polyEvalExpr_eval {n : ℕ} (env : Environment (F p))
    (coeffs : Vector (Expression (F p)) n) (x : F p) :
    Expression.eval env (polyEvalExpr coeffs x)
      = ∑ i : Fin n, (Expression.eval env coeffs[i.val]) * x ^ i.val := by
  simp only [polyEvalExpr]
  induction n with
  | zero => simp only [Fin.foldl_zero, Expression.eval, Finset.univ_eq_empty, Finset.sum_empty]
  | succ k ih =>
    obtain ih := ih coeffs.pop
    simp only [Vector.getElem_pop'] at ih
    rw [Fin.foldl_succ_last, Fin.sum_univ_castSucc]
    simp only [Expression.eval, Fin.val_last, Fin.val_castSucc]
    rw [← ih]

end MulMod

namespace GroupedEq

lemma sum_extend_zero (B N M : ℕ) (f : ℕ → ℕ) (hNM : N ≤ M)
    (hf : ∀ t, N ≤ t → f t = 0) :
    (∑ t ∈ Finset.range N, f t * 2 ^ (B * t)) = ∑ t ∈ Finset.range M, f t * 2 ^ (B * t) := by
  apply Finset.sum_subset
    (fun x hx => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hNM))
  intro x _ hx
  simp only [Finset.mem_range, not_lt] at hx
  rw [hf x hx, Nat.zero_mul]

end GroupedEq

end

end Solution.Secp256k1ScalarMul
