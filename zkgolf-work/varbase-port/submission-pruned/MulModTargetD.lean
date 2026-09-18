import Solution.Secp256k1ScalarMul.MulMod

namespace Solution.Secp256k1ScalarMul
namespace MulModTargetD
open MulMod

variable {p : ℕ} [Fact p.Prime]
variable {m : ℕ} [NeZero m]

lemma val_coeff_gen {B Cb : ℕ} (env : Environment (F p))
    (a b : Var (BigInt m) (F p)) (k : Fin (2 * m - 1))
    (ha : ∀ i : Fin m, (Expression.eval env a[i.val]).val < 2 ^ B)
    (hb : ∀ i : Fin m, (Expression.eval env b[i.val]).val < Cb)
    (hbound : m * (2 ^ B * Cb) < p) :
    (Expression.eval env ((bigIntMulNoReduce a b)[k.val])).val
      = ∑ i : Fin m, if h : i.val ≤ k.val ∧ k.val - i.val < m then
          (Expression.eval env a[i.val]).val
            * (Expression.eval env (b[k.val - i.val]'h.2)).val else 0 := by
  set natConv := ∑ i : Fin m, if h : i.val ≤ k.val ∧ k.val - i.val < m then
      (Expression.eval env a[i.val]).val
        * (Expression.eval env (b[k.val - i.val]'h.2)).val else 0 with hnat
  have hlt : natConv < p := by
    have hterm : ∀ i : Fin m, (if h : i.val ≤ k.val ∧ k.val - i.val < m then
        (Expression.eval env a[i.val]).val
          * (Expression.eval env (b[k.val - i.val]'h.2)).val else 0)
        ≤ 2 ^ B * Cb - 1 := by
      intro i
      by_cases h : i.val ≤ k.val ∧ k.val - i.val < m
      · rw [dif_pos h]
        have h1 := ha i
        have h2 := hb ⟨k.val - i.val, h.2⟩
        have : (Expression.eval env a[i.val]).val
            * (Expression.eval env (b[k.val - i.val]'h.2)).val < 2 ^ B * Cb :=
          Nat.mul_lt_mul'' h1 h2
        omega
      · rw [dif_neg h]; positivity
    have hcard : natConv ≤ m * (2 ^ B * Cb - 1) := by
      rw [hnat]
      calc ∑ i : Fin m, _ ≤ ∑ _i : Fin m, (2 ^ B * Cb - 1) :=
            Finset.sum_le_sum (fun i _ => hterm i)
        _ = m * (2 ^ B * Cb - 1) := by rw [Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, smul_eq_mul]
    have hCb : 0 < Cb := by
      rcases Nat.eq_zero_or_pos Cb with h0 | h; · exact absurd (hb ⟨0, Nat.pos_of_neZero m⟩) (by omega)
      · exact h
    have hpos : 0 < 2 ^ B * Cb := by positivity
    have hm : 0 < m := Nat.pos_of_neZero m
    have : m * (2 ^ B * Cb - 1) < m * (2 ^ B * Cb) :=
      (Nat.mul_lt_mul_left hm).mpr (by omega)
    omega
  have hcast : Expression.eval env ((bigIntMulNoReduce a b)[k.val]) = (natConv : F p) := by
    rw [eval_bigIntMulNoReduce_coeff, hnat, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : i.val ≤ k.val ∧ k.val - i.val < m
    · simp only [dif_pos h]
      rw [Nat.cast_mul, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    · simp only [dif_neg h, Nat.cast_zero]
  rw [hcast, ZMod.val_natCast_of_lt hlt]

lemma val_coeff_lt_gen {B Cb : ℕ} (env : Environment (F p))
    (a b : Var (BigInt m) (F p)) (k : Fin (2 * m - 1))
    (ha : ∀ i : Fin m, (Expression.eval env a[i.val]).val < 2 ^ B)
    (hb : ∀ i : Fin m, (Expression.eval env b[i.val]).val < Cb)
    (hbound : m * (2 ^ B * Cb) < p) :
    (Expression.eval env ((bigIntMulNoReduce a b)[k.val])).val < m * (2 ^ B * Cb) := by
  rw [val_coeff_gen env a b k ha hb hbound]
  have hterm : ∀ i : Fin m, (if h : i.val ≤ k.val ∧ k.val - i.val < m then
      (Expression.eval env a[i.val]).val
        * (Expression.eval env (b[k.val - i.val]'h.2)).val else 0)
      ≤ 2 ^ B * Cb - 1 := by
    intro i
    by_cases h : i.val ≤ k.val ∧ k.val - i.val < m
    · rw [dif_pos h]
      have : (Expression.eval env a[i.val]).val
          * (Expression.eval env (b[k.val - i.val]'h.2)).val < 2 ^ B * Cb :=
        Nat.mul_lt_mul'' (ha i) (hb ⟨k.val - i.val, h.2⟩)
      omega
    · rw [dif_neg h]; positivity
  have hcard : (∑ i : Fin m, if h : i.val ≤ k.val ∧ k.val - i.val < m then
      (Expression.eval env a[i.val]).val
        * (Expression.eval env (b[k.val - i.val]'h.2)).val else 0)
      ≤ m * (2 ^ B * Cb - 1) := by
    calc ∑ i : Fin m, _ ≤ ∑ _i : Fin m, (2 ^ B * Cb - 1) :=
          Finset.sum_le_sum (fun i _ => hterm i)
      _ = m * (2 ^ B * Cb - 1) := by rw [Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, smul_eq_mul]
  have hCb : 0 < Cb := by
    rcases Nat.eq_zero_or_pos Cb with h0 | h; · exact absurd (hb ⟨0, Nat.pos_of_neZero m⟩) (by omega)
    · exact h
  have hpos : 0 < 2 ^ B * Cb := by positivity
  have hm : 0 < m := Nat.pos_of_neZero m
  have : m * (2 ^ B * Cb - 1) < m * (2 ^ B * Cb) :=
    (Nat.mul_lt_mul_left hm).mpr (by omega)
  omega

lemma polyValue_mul_eq_gen {B Cb : ℕ} (env : Environment (F p))
    (a b : Var (BigInt m) (F p))
    (ha : ∀ i : Fin m, (Expression.eval env a[i.val]).val < 2 ^ B)
    (hb : ∀ i : Fin m, (Expression.eval env b[i.val]).val < Cb)
    (hbound : m * (2 ^ B * Cb) < p) :
    polyValue B (Vector.map (Expression.eval env) (bigIntMulNoReduce a b))
      = BigInt.value B (Vector.map (Expression.eval env) a)
        * BigInt.value B (Vector.map (Expression.eval env) b) := by
  rw [value_map_eval, value_map_eval]
  set av : ℕ → ℕ := fun i => if h : i < m then (Expression.eval env a[i]).val else 0 with hav
  set bv : ℕ → ℕ := fun j => if h : j < m then (Expression.eval env b[j]).val else 0 with hbv
  have hAsum : (∑ i : Fin m, (Expression.eval env a[i.val]).val * 2 ^ (B * i.val))
      = ∑ i ∈ Finset.range m, av i * 2 ^ (B * i) := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => av i * 2 ^ (B * i))]
    apply Finset.sum_congr rfl
    intro i _; simp only [hav, dif_pos i.isLt]
  have hBsum : (∑ j : Fin m, (Expression.eval env b[j.val]).val * 2 ^ (B * j.val))
      = ∑ j ∈ Finset.range m, bv j * 2 ^ (B * j) := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => bv j * 2 ^ (B * j))]
    apply Finset.sum_congr rfl
    intro j _; simp only [hbv, dif_pos j.isLt]
  rw [hAsum, hBsum, cauchy_base_pow B m av bv]
  rw [polyValue]
  rw [← Fin.sum_univ_eq_sum_range
    (fun k => (∑ i ∈ Finset.range m, if i ≤ k ∧ k - i < m then av i * bv (k - i) else 0)
      * 2 ^ (B * k))]
  apply Finset.sum_congr rfl
  intro k _
  rw [Vector.getElem_map, val_coeff_gen env a b k ha hb hbound]
  congr 1
  rw [← Fin.sum_univ_eq_sum_range
    (fun i => if i ≤ k.val ∧ k.val - i < m then av i * bv (k.val - i) else 0)]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : i.val ≤ k.val ∧ k.val - i.val < m
  · rw [dif_pos h, if_pos h]
    simp only [hav, hbv, dif_pos i.isLt, dif_pos h.2]
  · rw [dif_neg h, if_neg h]

end MulModTargetD
end Solution.Secp256k1ScalarMul
