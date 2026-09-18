import Solution.Secp256k1ScalarMul.Params

namespace Solution.Secp256k1ScalarMul

section
variable {p : ℕ} [Fact p.Prime] {m : ℕ}

omit [Fact (Nat.Prime p)] in

theorem BigInt.value_eq_zero_iff {B : ℕ} (x : BigInt m (F p)) :
    BigInt.value B x = 0 ↔ ∀ i : Fin m, x[i] = 0 := by
  rw [BigInt.value_eq_sum, Finset.sum_eq_zero_iff]
  constructor
  · intro h i
    have hterm := h i (Finset.mem_univ i)
    have hval : (x[i]).val = 0 := by
      have hpow : 0 < 2 ^ (B * i.val) := Nat.two_pow_pos _
      rcases Nat.mul_eq_zero.mp hterm with h0 | h0
      · exact h0
      · omega
    exact (ZMod.val_eq_zero _).mp hval
  · intro h i _
    rw [h i, ZMod.val_zero, Nat.zero_mul]

end

end Solution.Secp256k1ScalarMul
