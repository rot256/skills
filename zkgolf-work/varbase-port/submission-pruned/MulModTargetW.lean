import Solution.Secp256k1ScalarMul.MulModTargetD

namespace Solution.Secp256k1ScalarMul
namespace MulModTargetW
open MulMod MulModTargetD

variable {p : ℕ} [Fact p.Prime]
variable {m : ℕ} [NeZero m]

lemma val_three_mul (h3 : 3 < p) (z : F p) (h : 3 * z.val < p) :
    ((3 : F p) * z).val = 3 * z.val := by
  have hcast : (3 : F p) = ((3 : ℕ) : F p) := by norm_num
  rw [hcast, ZMod.val_mul, ZMod.val_natCast_of_lt h3, Nat.mod_eq_of_lt h]

lemma eval_three_mul (env : Environment (F p)) (z : Expression (F p)) :
    Expression.eval env (((3 : F p) : Expression (F p)) * z)
      = (3 : F p) * Expression.eval env z := rfl

attribute [local irreducible] interpolatedMul Normalize.circuit GroupedEqXV.circuit

end MulModTargetW
end Solution.Secp256k1ScalarMul
