import Solution.Secp256k1ScalarMul.MulMod
import Solution.Secp256k1ScalarMul.MulModTargetD3

/-!
# `MulModTargetW2`: wide-quotient offset certificate, doubly-unreduced `a`,
triply-unreduced `b`

`MulModTargetD3` certifies `a·b + 3n = q·n + t` with canonical `a` and a
triply-unreduced multiplicand `b` (limbs `< 3·2^B`, value `< 3n`). This
variant additionally widens `a` (limbs `< 2·2^B`, value `< 2n`) — enough for
the fused-step `mulA = λ₁ + w` limbwise sum, used both as the squared operand
(`a = b = mulA`, since `2·2^B < 3·2^B`) and against the borrow-free mux
operand. The quotient widens to `q = (a·b + 3n − t)/n < 6n + 3 < 6·2^(B·m)`:
the witness becomes `q_lo` (`BigInt m`) plus a top cell `qh ≤ 5` pinned by a
degree-6 product chain, and the LHS split cap grows to
`V.Nf = 6(m+1)·2^(2B)`; `VR.Nf = (m+1)·2^(2B)` is kept.

The coefficient-vector layer (`padD`, `sVecTD`, their `polyValue` lemmas at
the widened `qh ≤ 5` cap) reuses `MulModTargetD3`'s shapes.
-/

namespace Solution.Secp256k1ScalarMul
namespace MulModTargetW2
open MulMod
open MulModTargetD3 (padD sVecTD polyValue_padD coeff_padD_bound
  congruence_of_offset_eqD coeff_sVecT_fine val_coeff_lt_gen)

variable {p : ℕ} [Fact p.Prime]
variable {m : ℕ} [NeZero m]

private lemma eval_add_zero (env : Environment (F p)) (x : Expression (F p)) :
    Expression.eval env (x + 0) = Expression.eval env x := by
  rw [show Expression.eval env (x + 0)
        = Expression.eval env x + Expression.eval env (0 : Expression (F p)) from rfl,
    show Expression.eval env (0 : Expression (F p)) = 0 from rfl, add_zero]

private lemma eval_zero_add (env : Environment (F p)) (x : Expression (F p)) :
    Expression.eval env ((0 : Expression (F p)) + x) = Expression.eval env x := by
  rw [show Expression.eval env ((0 : Expression (F p)) + x)
        = Expression.eval env (0 : Expression (F p)) + Expression.eval env x from rfl,
    show Expression.eval env (0 : Expression (F p)) = 0 from rfl, zero_add]

/-! ## Convolution coefficient facts at two asymmetric caps -/

/-- Convolution coefficient value with caps `Ca`, `Cb` on both operands
(generalizes `MulModTargetD3.val_coeff_gen`). -/
lemma val_coeff_gen2 {Ca Cb : ℕ} (env : Environment (F p))
    (a b : Var (BigInt m) (F p)) (k : Fin (2 * m - 1))
    (ha : ∀ i : Fin m, (Expression.eval env a[i.val]).val < Ca)
    (hb : ∀ i : Fin m, (Expression.eval env b[i.val]).val < Cb)
    (hbound : m * (Ca * Cb) < p) :
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
        ≤ Ca * Cb - 1 := by
      intro i
      by_cases h : i.val ≤ k.val ∧ k.val - i.val < m
      · rw [dif_pos h]
        have h1 := ha i
        have h2 := hb ⟨k.val - i.val, h.2⟩
        have : (Expression.eval env a[i.val]).val
            * (Expression.eval env (b[k.val - i.val]'h.2)).val < Ca * Cb :=
          Nat.mul_lt_mul'' h1 h2
        omega
      · rw [dif_neg h]; positivity
    have hcard : natConv ≤ m * (Ca * Cb - 1) := by
      rw [hnat]
      calc ∑ i : Fin m, _ ≤ ∑ _i : Fin m, (Ca * Cb - 1) :=
            Finset.sum_le_sum (fun i _ => hterm i)
        _ = m * (Ca * Cb - 1) := by rw [Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, smul_eq_mul]
    have hCa : 0 < Ca := by
      rcases Nat.eq_zero_or_pos Ca with h0 | h
      · exact absurd (ha ⟨0, Nat.pos_of_neZero m⟩) (by omega)
      · exact h
    have hCb : 0 < Cb := by
      rcases Nat.eq_zero_or_pos Cb with h0 | h
      · exact absurd (hb ⟨0, Nat.pos_of_neZero m⟩) (by omega)
      · exact h
    have hpos : 0 < Ca * Cb := by positivity
    have hm : 0 < m := Nat.pos_of_neZero m
    have : m * (Ca * Cb - 1) < m * (Ca * Cb) :=
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

/-- Coefficient bound at two asymmetric caps: `< m·(Ca·Cb)`. -/
lemma val_coeff_lt_gen2 {Ca Cb : ℕ} (env : Environment (F p))
    (a b : Var (BigInt m) (F p)) (k : Fin (2 * m - 1))
    (ha : ∀ i : Fin m, (Expression.eval env a[i.val]).val < Ca)
    (hb : ∀ i : Fin m, (Expression.eval env b[i.val]).val < Cb)
    (hbound : m * (Ca * Cb) < p) :
    (Expression.eval env ((bigIntMulNoReduce a b)[k.val])).val < m * (Ca * Cb) := by
  rw [val_coeff_gen2 env a b k ha hb hbound]
  have hterm : ∀ i : Fin m, (if h : i.val ≤ k.val ∧ k.val - i.val < m then
      (Expression.eval env a[i.val]).val
        * (Expression.eval env (b[k.val - i.val]'h.2)).val else 0)
      ≤ Ca * Cb - 1 := by
    intro i
    by_cases h : i.val ≤ k.val ∧ k.val - i.val < m
    · rw [dif_pos h]
      have : (Expression.eval env a[i.val]).val
          * (Expression.eval env (b[k.val - i.val]'h.2)).val < Ca * Cb :=
        Nat.mul_lt_mul'' (ha i) (hb ⟨k.val - i.val, h.2⟩)
      omega
    · rw [dif_neg h]; positivity
  have hcard : (∑ i : Fin m, if h : i.val ≤ k.val ∧ k.val - i.val < m then
      (Expression.eval env a[i.val]).val
        * (Expression.eval env (b[k.val - i.val]'h.2)).val else 0)
      ≤ m * (Ca * Cb - 1) := by
    calc ∑ i : Fin m, _ ≤ ∑ _i : Fin m, (Ca * Cb - 1) :=
          Finset.sum_le_sum (fun i _ => hterm i)
      _ = m * (Ca * Cb - 1) := by rw [Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, smul_eq_mul]
  have hCa : 0 < Ca := by
    rcases Nat.eq_zero_or_pos Ca with h0 | h
    · exact absurd (ha ⟨0, Nat.pos_of_neZero m⟩) (by omega)
    · exact h
  have hCb : 0 < Cb := by
    rcases Nat.eq_zero_or_pos Cb with h0 | h
    · exact absurd (hb ⟨0, Nat.pos_of_neZero m⟩) (by omega)
    · exact h
  have hpos : 0 < Ca * Cb := by positivity
  have hm : 0 < m := Nat.pos_of_neZero m
  have : m * (Ca * Cb - 1) < m * (Ca * Cb) :=
    (Nat.mul_lt_mul_left hm).mpr (by omega)
  omega

/-- Refined coefficient bound: the convolution at position `k` has only as many
contributing terms as there are indices `i < m` with `i ≤ k` and `k − i < m`,
which is strictly fewer than `m` at the extreme positions. -/
lemma val_coeff_le_gen2_card {Ca Cb : ℕ} (env : Environment (F p))
    (a b : Var (BigInt m) (F p)) (k : Fin (2 * m - 1))
    (ha : ∀ i : Fin m, (Expression.eval env a[i.val]).val < Ca)
    (hb : ∀ i : Fin m, (Expression.eval env b[i.val]).val < Cb)
    (hbound : m * (Ca * Cb) < p) :
    (Expression.eval env ((bigIntMulNoReduce a b)[k.val])).val
      ≤ ((Finset.univ.filter
            (fun i : Fin m => i.val ≤ k.val ∧ k.val - i.val < m)).card) * (Ca * Cb - 1) := by
  rw [val_coeff_gen2 env a b k ha hb hbound]
  have hsplit : (∑ i : Fin m, if h : i.val ≤ k.val ∧ k.val - i.val < m then
      (Expression.eval env a[i.val]).val
        * (Expression.eval env (b[k.val - i.val]'h.2)).val else 0)
      = ∑ i ∈ Finset.univ.filter (fun i : Fin m => i.val ≤ k.val ∧ k.val - i.val < m),
        (if h : i.val ≤ k.val ∧ k.val - i.val < m then
          (Expression.eval env a[i.val]).val
            * (Expression.eval env (b[k.val - i.val]'h.2)).val else 0) := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro x _ hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    exact dif_neg hx
  rw [hsplit]
  calc (∑ i ∈ Finset.univ.filter (fun i : Fin m => i.val ≤ k.val ∧ k.val - i.val < m),
        (if h : i.val ≤ k.val ∧ k.val - i.val < m then
          (Expression.eval env a[i.val]).val
            * (Expression.eval env (b[k.val - i.val]'h.2)).val else 0))
      ≤ ∑ _i ∈ Finset.univ.filter (fun i : Fin m => i.val ≤ k.val ∧ k.val - i.val < m),
        (Ca * Cb - 1) := by
        refine Finset.sum_le_sum ?_
        intro i _
        by_cases h : i.val ≤ k.val ∧ k.val - i.val < m
        · rw [dif_pos h]
          have : (Expression.eval env a[i.val]).val
              * (Expression.eval env (b[k.val - i.val]'h.2)).val < Ca * Cb :=
            Nat.mul_lt_mul'' (ha i) (hb ⟨k.val - i.val, h.2⟩)
          omega
        · rw [dif_neg h]; positivity
    _ = ((Finset.univ.filter
            (fun i : Fin m => i.val ≤ k.val ∧ k.val - i.val < m)).card) * (Ca * Cb - 1) := by
        rw [Finset.sum_const, smul_eq_mul]

/-- `sVecTD` coefficient bound at the `qh ≤ 5` cap: `Cb + 6·2^B`. -/
lemma coeff_sVecTD_bound5 {B Cb : ℕ} (env : Environment (F p))
    (base : Vector (Expression (F p)) (2 * m - 1)) (qh : Expression (F p))
    (n : Var (BigInt m) (F p)) (k : Fin (2 * m))
    (hCb : 0 < Cb)
    (hbase : ∀ j : Fin (2 * m - 1), (Expression.eval env base[j.val]).val < Cb)
    (hqh : (Expression.eval env qh).val ≤ 5)
    (hn : ∀ i : Fin m, (Expression.eval env n[i.val]).val < 2 ^ B) :
    (Expression.eval env ((sVecTD base qh n)[k.val])).val < Cb + 6 * 2 ^ B := by
  have hpos : (0:ℕ) < 2 ^ B := Nat.two_pow_pos B
  have hflank : ∀ (hm' : m ≤ k.val ∧ k.val - m < m),
      (Expression.eval env (qh * n[k.val - m]'hm'.2)).val < 6 * 2 ^ B := by
    intro hm'
    rw [show Expression.eval env (qh * n[k.val - m]'hm'.2)
          = Expression.eval env qh * Expression.eval env (n[k.val - m]'hm'.2) from rfl]
    calc (Expression.eval env qh * Expression.eval env (n[k.val - m]'hm'.2)).val
        ≤ (Expression.eval env qh).val * (Expression.eval env (n[k.val - m]'hm'.2)).val :=
          ZMod.val_mul_le _ _
      _ ≤ 5 * (Expression.eval env (n[k.val - m]'hm'.2)).val :=
          Nat.mul_le_mul_right _ hqh
      _ < 6 * 2 ^ B := by
          have hnk : (Expression.eval env (n[k.val - m]'hm'.2)).val < 2 ^ B :=
            hn ⟨k.val - m, hm'.2⟩
          omega
  simp only [sVecTD, Vector.getElem_mapFinRange]
  by_cases hk : k.val < 2 * m - 1
  · rw [dif_pos hk]
    by_cases hm' : m ≤ k.val ∧ k.val - m < m
    · rw [dif_pos hm']
      have hadd : (Expression.eval env (base[k.val]'hk + qh * n[k.val - m]'hm'.2)).val
          ≤ (Expression.eval env (base[k.val]'hk)).val
            + (Expression.eval env (qh * n[k.val - m]'hm'.2)).val := by
        rw [show Expression.eval env (base[k.val]'hk + qh * n[k.val - m]'hm'.2)
              = Expression.eval env (base[k.val]'hk)
                + Expression.eval env (qh * n[k.val - m]'hm'.2) from rfl]
        exact ZMod.val_add_le _ _
      have hb : (Expression.eval env (base[k.val]'hk)).val < Cb := hbase ⟨k.val, hk⟩
      have hf := hflank hm'
      omega
    · rw [dif_neg hm', eval_add_zero]
      have hb : (Expression.eval env (base[k.val]'hk)).val < Cb := hbase ⟨k.val, hk⟩
      omega
  · rw [dif_neg hk]
    by_cases hm' : m ≤ k.val ∧ k.val - m < m
    · rw [dif_pos hm', eval_zero_add]
      have hf := hflank hm'
      omega
    · rw [dif_neg hm', eval_add_zero]
      rw [show Expression.eval env (0 : Expression (F p)) = 0 from rfl, ZMod.val_zero]
      omega

private lemma polyValue_eq_range_sum {B kk : ℕ} (vv : Vector (F p) kk) (f : ℕ → ℕ)
    (hf : ∀ (i : ℕ) (h : i < kk), (vv[i]'h).val * 2 ^ (B * i) = f i) :
    polyValue B vv = ∑ i ∈ Finset.range kk, f i := by
  rw [polyValue, ← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_congr rfl fun i _ => hf i.val i.isLt

/-- `polyValue` of the extended RHS at the `qh ≤ 5` cap. -/
lemma polyValue_sVecTD5 {B Cb : ℕ} (env : Environment (F p))
    (base : Vector (Expression (F p)) (2 * m - 1)) (qh : Expression (F p))
    (n : Var (BigInt m) (F p))
    (hCb : 0 < Cb)
    (hbase : ∀ j : Fin (2 * m - 1), (Expression.eval env base[j.val]).val < Cb)
    (hqh : (Expression.eval env qh).val ≤ 5)
    (hn : ∀ i : Fin m, (Expression.eval env n[i.val]).val < 2 ^ B)
    (hp1 : Cb + 6 * 2 ^ B < p) :
    polyValue B (Vector.map (Expression.eval env) (sVecTD base qh n))
      = polyValue B (Vector.map (Expression.eval env) base)
        + (Expression.eval env qh).val * 2 ^ (B * m)
            * BigInt.value B (Vector.map (Expression.eval env) n) := by
  have hm : 0 < m := Nat.pos_of_neZero m
  have hpos : (0:ℕ) < 2 ^ B := Nat.two_pow_pos B
  have hcoeff : ∀ (i : ℕ) (h : i < 2 * m),
      ((Vector.map (Expression.eval env) (sVecTD base qh n))[i]'h).val * 2 ^ (B * i)
      = (if hlt : i < 2 * m - 1 then (Expression.eval env (base[i]'hlt)).val * 2 ^ (B * i) else 0)
        + (if hm' : m ≤ i ∧ i - m < m
           then (Expression.eval env qh).val
                  * (Expression.eval env (n[i - m]'hm'.2)).val * 2 ^ (B * i)
           else 0) := by
    intro i h
    rw [Vector.getElem_map]
    simp only [sVecTD, Vector.getElem_mapFinRange]
    have hflankb : ∀ (hm' : m ≤ i ∧ i - m < m),
        (Expression.eval env qh).val * (Expression.eval env (n[i - m]'hm'.2)).val
          < 6 * 2 ^ B := by
      intro hm'
      calc (Expression.eval env qh).val * (Expression.eval env (n[i - m]'hm'.2)).val
          ≤ 5 * (Expression.eval env (n[i - m]'hm'.2)).val := Nat.mul_le_mul_right _ hqh
        _ < 6 * 2 ^ B := by
            have hnk : (Expression.eval env (n[i - m]'hm'.2)).val < 2 ^ B :=
              hn ⟨i - m, hm'.2⟩
            omega
    have hflankv : ∀ (hm' : m ≤ i ∧ i - m < m),
        (Expression.eval env (qh * n[i - m]'hm'.2)).val
          = (Expression.eval env qh).val * (Expression.eval env (n[i - m]'hm'.2)).val := by
      intro hm'
      rw [show Expression.eval env (qh * n[i - m]'hm'.2)
            = Expression.eval env qh * Expression.eval env (n[i - m]'hm'.2) from rfl]
      exact ZMod.val_mul_of_lt (lt_trans (hflankb hm') (by omega))
    by_cases hlt : i < 2 * m - 1
    · rw [dif_pos hlt, dif_pos hlt]
      by_cases hm' : m ≤ i ∧ i - m < m
      · rw [dif_pos hm', dif_pos hm']
        rw [show Expression.eval env (base[i]'hlt + qh * n[i - m]'hm'.2)
              = Expression.eval env (base[i]'hlt)
                + Expression.eval env (qh * n[i - m]'hm'.2) from rfl]
        rw [ZMod.val_add_of_lt (by
          have h1 : (Expression.eval env (base[i]'hlt)).val < Cb := hbase ⟨i, hlt⟩
          have h2 : (Expression.eval env (qh * n[i - m]'hm'.2)).val < 6 * 2 ^ B := by
            rw [hflankv hm']
            exact hflankb hm'
          omega)]
        rw [add_mul, hflankv hm']
      · rw [dif_neg hm', dif_neg hm', eval_add_zero, add_zero]
    · rw [dif_neg hlt, dif_neg hlt]
      by_cases hm' : m ≤ i ∧ i - m < m
      · rw [dif_pos hm', dif_pos hm', eval_zero_add]
        rw [hflankv hm', zero_add]
      · rw [dif_neg hm', dif_neg hm', eval_add_zero]
        rw [show Expression.eval env (0 : Expression (F p)) = 0 from rfl, ZMod.val_zero, zero_mul,
          zero_add]
  have hsum : polyValue B (Vector.map (Expression.eval env) (sVecTD base qh n))
      = (∑ i ∈ Finset.range (2 * m),
          (fun j => if hlt : j < 2 * m - 1
            then (Expression.eval env (base[j]'hlt)).val * 2 ^ (B * j) else 0) i)
        + ∑ i ∈ Finset.range (2 * m),
            (fun j => if hm' : m ≤ j ∧ j - m < m
              then (Expression.eval env qh).val
                    * (Expression.eval env (n[j - m]'hm'.2)).val * 2 ^ (B * j)
              else 0) i := by
    rw [← Finset.sum_add_distrib]
    apply polyValue_eq_range_sum
    intro i h
    rw [hcoeff i h]
  rw [hsum]
  congr 1
  · have h1 : polyValue B (Vector.map (Expression.eval env) base)
        = ∑ i ∈ Finset.range (2 * m - 1),
            (fun j => if hlt : j < 2 * m - 1
              then (Expression.eval env (base[j]'hlt)).val * 2 ^ (B * j) else 0) i := by
      apply polyValue_eq_range_sum
      intro i h
      simp only [dif_pos h, Vector.getElem_map]
    rw [h1]
    have hsub : Finset.range (2 * m - 1) ⊆ Finset.range (2 * m) := by
      intro x hx
      rw [Finset.mem_range] at hx ⊢
      omega
    symm
    apply Finset.sum_subset hsub
    intro x _ hx
    rw [Finset.mem_range] at hx
    simp only [dif_neg hx]
  · have hvanish : ∀ x ∈ Finset.range (2 * m), x ∉ Finset.Ico m (2 * m) →
        (fun j => if hm' : m ≤ j ∧ j - m < m
          then (Expression.eval env qh).val
                * (Expression.eval env (n[j - m]'hm'.2)).val * 2 ^ (B * j)
          else 0) x = 0 := by
      intro x hx hxn
      rw [Finset.mem_range] at hx
      rw [Finset.mem_Ico] at hxn
      have : ¬ (m ≤ x ∧ x - m < m) := by omega
      simp only [dif_neg this]
    calc ∑ i ∈ Finset.range (2 * m), (fun j => if hm' : m ≤ j ∧ j - m < m
            then (Expression.eval env qh).val
                  * (Expression.eval env (n[j - m]'hm'.2)).val * 2 ^ (B * j)
            else 0) i
        = ∑ i ∈ Finset.Ico m (2 * m), (fun j => if hm' : m ≤ j ∧ j - m < m
            then (Expression.eval env qh).val
                  * (Expression.eval env (n[j - m]'hm'.2)).val * 2 ^ (B * j)
            else 0) i := by
          symm
          apply Finset.sum_subset
          · rw [Finset.range_eq_Ico]
            exact Finset.Ico_subset_Ico (show (0:ℕ) ≤ m from by omega) le_rfl
          · exact hvanish
      _ = ∑ i ∈ Finset.range (2 * m - m), (fun j => if hm' : m ≤ j ∧ j - m < m
            then (Expression.eval env qh).val
                  * (Expression.eval env (n[j - m]'hm'.2)).val * 2 ^ (B * j)
            else 0) (m + i) := Finset.sum_Ico_eq_sum_range _ _ _
      _ = ∑ i ∈ Finset.range m, (fun j => if hj : j < m
            then (Expression.eval env qh).val
                  * (Expression.eval env (n[j]'hj)).val * 2 ^ (B * (m + j))
            else 0) i := by
          apply Finset.sum_congr (by congr 1; omega)
          intro i hi
          rw [Finset.mem_range] at hi
          simp only [Nat.add_sub_cancel_left]
          rw [dif_pos (⟨by omega, hi⟩ : m ≤ m + i ∧ i < m), dif_pos hi]
      _ = (Expression.eval env qh).val * 2 ^ (B * m)
            * BigInt.value B (Vector.map (Expression.eval env) n) := by
          rw [value_map_eval]
          have hG : (∑ k : Fin m, (Expression.eval env n[k.val]).val * 2 ^ (B * k.val))
              = ∑ i ∈ Finset.range m, (fun j => if hj : j < m
                  then (Expression.eval env (n[j]'hj)).val * 2 ^ (B * j) else 0) i := by
            rw [← Fin.sum_univ_eq_sum_range]
            apply Finset.sum_congr rfl
            intro k _
            simp only [dif_pos k.isLt]
          rw [hG, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.mem_range] at hi
          simp only [dif_pos hi]
          rw [show B * (m + i) = B * m + B * i from by ring, pow_add]
          ring

/-- Asymmetric-cap product bridge at two caps. -/
lemma polyValue_mul_eq_gen2 {B Ca Cb : ℕ} (env : Environment (F p))
    (a b : Var (BigInt m) (F p))
    (ha : ∀ i : Fin m, (Expression.eval env a[i.val]).val < Ca)
    (hb : ∀ i : Fin m, (Expression.eval env b[i.val]).val < Cb)
    (hbound : m * (Ca * Cb) < p) :
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
  rw [Vector.getElem_map, val_coeff_gen2 env a b k ha hb hbound]
  congr 1
  rw [← Fin.sum_univ_eq_sum_range
    (fun i => if i ≤ k.val ∧ k.val - i < m then av i * bv (k.val - i) else 0)]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : i.val ≤ k.val ∧ k.val - i.val < m
  · rw [dif_pos h, if_pos h]
    simp only [hav, hbv, dif_pos i.isLt, dif_pos h.2]
  · rw [dif_neg h, if_neg h]

/-! ## The soundness arithmetic core -/

set_option maxHeartbeats 1600000 in
/-- The arithmetic core of `MulModTargetW2` soundness. -/
lemma soundness_core_wm {B : ℕ} (hB2 : 4 ≤ B)
    (hp : 2 ^ (2 * B) * (m + 1) * 32 < p)
    (i₀ : ℕ) (env : Environment (F p))
    (a b n t : Var (BigInt m) (F p))
    (c : Vector (F p) (2 * m - 1))
    (Pv : Vector (Expression (F p)) (2 * m - 1))
    (qh : Expression (F p))
    (av bv nv tv : BigInt m (F p))
    (ha_input : Vector.map (Expression.eval env) a = av)
    (hb_input : Vector.map (Expression.eval env) b = bv)
    (hn_input : Vector.map (Expression.eval env) n = nv)
    (ht_input : Vector.map (Expression.eval env) t = tv)
    (ha_limb : ∀ i : Fin m, (av[i.val]).val < 2 * 2 ^ B)
    (hb_limb : ∀ i : Fin m, (bv[i.val]).val < 3 * 2 ^ B)
    (hn_norm : BigInt.Normalized B nv)
    (ht_limb : ∀ i : Fin m, (tv[i.val]).val < 3 * 2 ^ B)
    (hc_limb : ∀ j : Fin (2 * m - 1), (c[j.val]).val < 2 ^ B)
    (hc_val : polyValue B c = 3 * BigInt.value B nv)
    (hq_norm : BigInt.Normalized B (Vector.map (Expression.eval env)
        (Vector.mapRange m fun i ↦ var { index := i₀ + i })))
    (hqh_le : (Expression.eval env qh).val ≤ 5)
    (heqAB_get : ∀ k : Fin (2 * m - 1),
      Expression.eval env Pv[k.val] = Expression.eval env (bigIntMulNoReduce a b)[k.val])
    (h_eq_impl :
      ((∀ k : Fin (2 * m),
          (Expression.eval env ((padD (lVecC Pv c))[k.val])).val
            < 6 * ((m + 1) * 2 ^ (2 * B))) ∧
        ∀ k : Fin (2 * m),
          (Expression.eval env
            ((sVecTD (sVecT (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n t)
              qh n)[k.val])).val
            < (m + 1) * 2 ^ (2 * B)) →
        polyValue B (Vector.map (Expression.eval env) (padD (lVecC Pv c))) =
          polyValue B (Vector.map (Expression.eval env)
            (sVecTD (sVecT (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n t) qh n))) :
    BigInt.value B tv % BigInt.value B nv
      = BigInt.value B av * BigInt.value B bv % BigInt.value B nv := by
  set qVar := (Vector.mapRange m fun i ↦ var (F := F p) { index := i₀ + i }) with hqVar
  -- digit bounds
  have ha_lt : ∀ i : Fin m, (Expression.eval env a[i.val]).val < 2 * 2 ^ B := by
    intro i; rw [show Expression.eval env a[i.val] = av[i.val] from by
      rw [← ha_input]; simp only [Vector.getElem_map]]; exact ha_limb i
  have hb_lt : ∀ i : Fin m, (Expression.eval env b[i.val]).val < 3 * 2 ^ B := by
    intro i; rw [show Expression.eval env b[i.val] = bv[i.val] from by
      rw [← hb_input]; simp only [Vector.getElem_map]]; exact hb_limb i
  have hn_lt : ∀ i : Fin m, (Expression.eval env n[i.val]).val < 2 ^ B := by
    intro i; rw [show Expression.eval env n[i.val] = nv[i.val] from by
      rw [← hn_input]; simp only [Vector.getElem_map]]; exact hn_norm i
  have hqd_lt : ∀ i : Fin m, (Expression.eval env qVar[i.val]).val < 2 ^ B := by
    intro i; have := hq_norm i
    rwa [Fin.getElem_fin, Vector.getElem_map] at this
  have htd_lt : ∀ j : ℕ, (hj : j < m) → (Expression.eval env (t[j]'hj)).val < 3 * 2 ^ B := by
    intro j hj
    have h : (tv[j]'hj).val < 3 * 2 ^ B := ht_limb ⟨j, hj⟩
    rwa [show tv[j]'hj = (Vector.map (Expression.eval env) t)[j]'hj from by rw [ht_input],
      Vector.getElem_map] at h
  have hfield : m * (2 ^ B * 2 ^ B) < p := by
    have h1 : m * (2 ^ B * 2 ^ B) = m * 2 ^ (2 * B) := by rw [two_mul, pow_add]
    rw [h1]
    have h2 : m * 2 ^ (2 * B) ≤ 2 ^ (2 * B) * (m + 1) * 32 := by
      calc m * 2 ^ (2 * B) = 2 ^ (2 * B) * m := Nat.mul_comm _ _
        _ ≤ 2 ^ (2 * B) * ((m + 1) * 32) := mul_le_mul_left' (by omega) _
        _ = 2 ^ (2 * B) * (m + 1) * 32 := (mul_assoc _ _ _).symm
    omega
  have hfield6 : m * ((2 * 2 ^ B) * (3 * 2 ^ B)) < p := by
    have h1 : m * ((2 * 2 ^ B) * (3 * 2 ^ B)) = 6 * (m * 2 ^ (2 * B)) := by
      rw [two_mul B, pow_add]; ring
    rw [h1]
    have h2 : 6 * (m * 2 ^ (2 * B)) ≤ 2 ^ (2 * B) * (m + 1) * 32 := by
      calc 6 * (m * 2 ^ (2 * B)) = 2 ^ (2 * B) * (6 * m) := by ring
        _ ≤ 2 ^ (2 * B) * ((m + 1) * 32) := mul_le_mul_left' (by omega) _
        _ = 2 ^ (2 * B) * (m + 1) * 32 := (mul_assoc _ _ _).symm
    omega
  have h16B : 16 * 2 ^ B ≤ 2 ^ (2 * B) := by
    have h16 : (16 : ℕ) ≤ 2 ^ B := by
      calc (16 : ℕ) = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ B := Nat.pow_le_pow_right (by norm_num) hB2
    calc 16 * 2 ^ B ≤ 2 ^ B * 2 ^ B := Nat.mul_le_mul_right _ h16
      _ = 2 ^ (2 * B) := by rw [two_mul, pow_add]
  -- fine bound on the lVecC coefficients (with the widened conv bound)
  have hL_fine : ∀ k : Fin (2 * m - 1),
      (Expression.eval env ((lVecC Pv c)[k.val])).val
        < m * ((2 * 2 ^ B) * (3 * 2 ^ B)) + 2 ^ B := by
    intro k
    have hgetl : (lVecC Pv c)[k.val] = Pv[k.val] + ((c[k.val] : F p) : Expression (F p)) := by
      simp only [lVecC, Vector.getElem_mapFinRange]
    rw [hgetl]
    have hle : (Expression.eval env (Pv[k.val] + ((c[k.val] : F p) : Expression (F p)))).val
        ≤ (Expression.eval env Pv[k.val]).val + (c[k.val]).val := by
      rw [show Expression.eval env (Pv[k.val] + ((c[k.val] : F p) : Expression (F p)))
            = Expression.eval env Pv[k.val] + c[k.val] from rfl]
      exact ZMod.val_add_le _ _
    have hPk : (Expression.eval env Pv[k.val]).val
        < m * ((2 * 2 ^ B) * (3 * 2 ^ B)) := by
      rw [heqAB_get k]
      exact val_coeff_lt_gen2 env a b k ha_lt hb_lt hfield6
    have hck := hc_limb k
    omega
  -- fine bound on the sVecT base
  have hS_fine : ∀ j : Fin (2 * m - 1),
      (Expression.eval env ((sVecT qVar n t)[j.val])).val
        < m * 2 ^ (2 * B) + 3 * 2 ^ B :=
    fun j => coeff_sVecT_fine env qVar n t j hqd_lt hn_lt htd_lt hfield
  -- discharge the grouped-equality obligations
  have h_polyeq := h_eq_impl ⟨fun k => by
      have hcap := coeff_padD_bound env (lVecC Pv c) k
        (Cv := m * ((2 * 2 ^ B) * (3 * 2 ^ B)) + 2 ^ B) (by positivity) hL_fine
      have h2B : (2 * 2 ^ B) * (3 * 2 ^ B) = 6 * 2 ^ (2 * B) := by
        rw [two_mul B, pow_add]; ring
      rw [h2B] at hcap
      have hBle : 2 ^ B ≤ 2 ^ (2 * B) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hexp : 6 * ((m + 1) * 2 ^ (2 * B)) = m * (6 * 2 ^ (2 * B)) + 6 * 2 ^ (2 * B) := by
        ring
      omega,
    fun k => by
      have hcap := coeff_sVecTD_bound5 env (sVecT qVar n t) qh n k
        (Cb := m * 2 ^ (2 * B) + 3 * 2 ^ B) (by positivity) hS_fine hqh_le hn_lt
      have hexp : (m + 1) * 2 ^ (2 * B) = m * 2 ^ (2 * B) + 2 ^ (2 * B) := by ring
      omega⟩
  -- extract the L = 2m−1 value equation plus the top-quotient flank
  rw [polyValue_padD] at h_polyeq
  rw [polyValue_sVecTD5 env (sVecT qVar n t) qh n
    (Cb := m * 2 ^ (2 * B) + 3 * 2 ^ B) (by positivity) hS_fine hqh_le hn_lt
    (by
      have hexp : 2 ^ (2 * B) * (m + 1) * 32 = 32 * (m * 2 ^ (2 * B)) + 32 * 2 ^ (2 * B) := by
        ring
      omega)] at h_polyeq
  -- split L: polyValue (lVecC) = a·b + 3n
  have hLSplit := polyValue_lVecC_split (B := B) env Pv c
    (fun k => by
      rw [heqAB_get k]
      have h1 := val_coeff_lt_gen2 env a b k ha_lt hb_lt hfield6
      have h2 := hc_limb k
      have h2B : (2 * 2 ^ B) * (3 * 2 ^ B) = 6 * 2 ^ (2 * B) := by
        rw [two_mul B, pow_add]; ring
      rw [h2B] at h1
      have hBle : 2 ^ B ≤ 2 ^ (2 * B) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hh : m * (6 * 2 ^ (2 * B)) = 6 * (m * 2 ^ (2 * B)) := by ring
      have hexp : 2 ^ (2 * B) * (m + 1) * 32
          = 6 * (m * 2 ^ (2 * B)) + (26 * (m * 2 ^ (2 * B)) + 32 * 2 ^ (2 * B)) := by ring
      omega)
  have hPv_map : Vector.map (Expression.eval env) Pv
      = Vector.map (Expression.eval env) (bigIntMulNoReduce a b) := by
    apply Vector.ext; intro k hk
    rw [Vector.getElem_map, Vector.getElem_map]
    exact heqAB_get ⟨k, hk⟩
  have hP : polyValue B (Vector.map (Expression.eval env) (bigIntMulNoReduce a b))
      = BigInt.value B av * BigInt.value B bv := by
    rw [polyValue_mul_eq_gen2 env a b ha_lt hb_lt hfield6, ha_input, hb_input]
  -- split S base: polyValue (sVecT) = q·n + t
  have hSplit := polyValue_sVecT_split (B := B) env qVar n t
    (fun k hk => by
      have h1 := val_coeff_lt_gen env qVar n k hqd_lt hn_lt hfield
      have h2 := htd_lt k.val hk
      have h2B : 2 ^ B * 2 ^ B = 2 ^ (2 * B) := by rw [two_mul, pow_add]
      rw [h2B] at h1
      have hBle : 2 ^ B ≤ 2 ^ (2 * B) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hexp : 2 ^ (2 * B) * (m + 1) * 32
          = m * 2 ^ (2 * B) + (31 * (m * 2 ^ (2 * B)) + 32 * 2 ^ (2 * B)) := by ring
      omega)
  have hSqn : polyValue B (Vector.map (Expression.eval env) (bigIntMulNoReduce qVar n))
      = BigInt.value B (Vector.map (Expression.eval env) qVar) * BigInt.value B nv := by
    rw [polyValue_Sqn_eq env qVar n hqd_lt hn_lt hfield, ← hn_input]
  rw [hLSplit, hPv_map, hP, hc_val, hSplit, hSqn, ht_input, hn_input] at h_polyeq
  -- assemble the wide-quotient integer identity
  set qlo := BigInt.value B (Vector.map (Expression.eval env) qVar) with hqlo
  set qhv := (Expression.eval env qh).val with hqhv
  have heq : BigInt.value B av * BigInt.value B bv + 3 * BigInt.value B nv
      = (qlo + qhv * 2 ^ (B * m)) * BigInt.value B nv + BigInt.value B tv := by
    have hring : (qlo + qhv * 2 ^ (B * m)) * BigInt.value B nv
        = qlo * BigInt.value B nv + qhv * 2 ^ (B * m) * BigInt.value B nv := by ring
    omega
  exact congruence_of_offset_eqD heq

/-! ## The completeness arithmetic core -/

set_option maxHeartbeats 1600000 in
/-- The arithmetic core of `MulModTargetW2` completeness. -/
lemma completeness_core_wm {B : ℕ} (hB : 2 ^ B < p) (hB2 : 4 ≤ B)
    (hp : 2 ^ (2 * B) * (m + 1) * 32 < p)
    (i₀ : ℕ) (env : Environment (F p))
    (a b n t : Var (BigInt m) (F p))
    (c : Vector (F p) (2 * m - 1))
    (Pv : Vector (Expression (F p)) (2 * m - 1))
    (av bv nv tv : BigInt m (F p))
    (ha_input : Vector.map (Expression.eval env) a = av)
    (hb_input : Vector.map (Expression.eval env) b = bv)
    (hn_input : Vector.map (Expression.eval env) n = nv)
    (ht_input : Vector.map (Expression.eval env) t = tv)
    (ha_limb : ∀ i : Fin m, (av[i.val]).val < 2 * 2 ^ B)
    (hb_limb : ∀ i : Fin m, (bv[i.val]).val < 3 * 2 ^ B)
    (hn_norm : BigInt.Normalized B nv)
    (ht_limb : ∀ i : Fin m, (tv[i.val]).val < 3 * 2 ^ B)
    (hc_limb : ∀ j : Fin (2 * m - 1), (c[j.val]).val < 2 ^ B)
    (hc_val : polyValue B c = 3 * BigInt.value B nv)
    (hab_lt : BigInt.value B av < 2 * BigInt.value B nv)
    (hbb_lt : BigInt.value B bv < 3 * BigInt.value B nv)
    (hn_pos : 0 < BigInt.value B nv)
    (hn3D : 2 * BigInt.value B nv + 3 ≤ 2 ^ (B * m + 1))
    (ht_lt3 : BigInt.value B tv < 3 * BigInt.value B nv)
    (ht_spec : BigInt.value B tv % BigInt.value B nv
      = BigInt.value B av * BigInt.value B bv % BigInt.value B nv)
    (hqwit : ∀ i : Fin m, env.get (i₀ + i.val)
      = (((BigInt.value B av * BigInt.value B bv + 3 * BigInt.value B nv
            - BigInt.value B tv) / BigInt.value B nv % 2 ^ (B * m)
          / 2 ^ (B * i.val) % 2 ^ B : ℕ) : F p))
    (hqhwit : env.get (i₀ + m)
      = (((BigInt.value B av * BigInt.value B bv + 3 * BigInt.value B nv
            - BigInt.value B tv) / BigInt.value B nv / 2 ^ (B * m) : ℕ) : F p))
    (heqAB_get : ∀ k : Fin (2 * m - 1),
      Expression.eval env Pv[k.val] = Expression.eval env (bigIntMulNoReduce a b)[k.val]) :
    BigInt.Normalized B (Vector.map (Expression.eval env)
        (Vector.mapRange m fun i ↦ var { index := i₀ + i }))
    ∧ (BigInt.value B av * BigInt.value B bv + 3 * BigInt.value B nv
          - BigInt.value B tv) / BigInt.value B nv / 2 ^ (B * m) ≤ 5
    ∧ ((∀ k : Fin (2 * m),
          (Expression.eval env ((padD (lVecC Pv c))[k.val])).val
            < 6 * ((m + 1) * 2 ^ (2 * B))) ∧
        ∀ k : Fin (2 * m),
          (Expression.eval env
            ((sVecTD (sVecT (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n t)
              (var { index := i₀ + m }) n)[k.val])).val
            < (m + 1) * 2 ^ (2 * B))
    ∧ polyValue B (Vector.map (Expression.eval env) (padD (lVecC Pv c))) =
        polyValue B (Vector.map (Expression.eval env)
          (sVecTD (sVecT (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n t)
            (var { index := i₀ + m }) n)) := by
  set qVar := (Vector.mapRange m fun i ↦ var (F := F p) { index := i₀ + i }) with hqVar
  set qhVar := (var (F := F p) { index := i₀ + m }) with hqhVar
  set aval := BigInt.value B av with ha_def
  set bval := BigInt.value B bv with hb_def
  set nval := BigInt.value B nv with hn_def
  set tval := BigInt.value B tv with ht_def
  set qval := (aval * bval + 3 * nval - tval) / nval with hqval_def
  -- exact division: a·b + 3n = q·n + t
  have ht_le : tval ≤ aval * bval + 3 * nval := by omega
  have hkey : qval * nval + tval = aval * bval + 3 * nval := by
    have hR : (aval * bval + 3 * nval) % nval = tval % nval := by
      rw [Nat.add_mul_mod_self_right, ht_spec]
    have hdvd : nval ∣ (aval * bval + 3 * nval - tval) := by
      refine ⟨(aval * bval + 3 * nval) / nval - tval / nval, ?_⟩
      have h1 := Nat.div_add_mod (aval * bval + 3 * nval) nval
      have h2 := Nat.div_add_mod tval nval
      have hQle : tval / nval ≤ (aval * bval + 3 * nval) / nval :=
        Nat.div_le_div_right ht_le
      rw [Nat.mul_sub]
      omega
    have hqmul : qval * nval = aval * bval + 3 * nval - tval := by
      rw [hqval_def, Nat.div_mul_cancel hdvd]
    omega
  -- the wide quotient bound: q < 6n + 3 ≤ 6·2^(Bm)
  have hqval_lt : qval < 6 * 2 ^ (B * m) := by
    have hq_le : qval ≤ (aval * bval + 3 * nval) / nval :=
      Nat.div_le_div_right (Nat.sub_le _ _)
    have hq_lt : (aval * bval + 3 * nval) / nval < 6 * nval + 3 := by
      apply Nat.div_lt_of_lt_mul
      have hab : aval * bval < nval * (6 * nval) := by
        rcases Nat.eq_zero_or_pos bval with hb0 | hb0
        · rw [hb0, Nat.mul_zero]; positivity
        · calc aval * bval < 2 * nval * bval := by
                apply (Nat.mul_lt_mul_right hb0).mpr hab_lt
            _ ≤ 2 * nval * (3 * nval) := by
                apply Nat.mul_le_mul_left; omega
            _ = nval * (6 * nval) := by ring
      calc aval * bval + 3 * nval < nval * (6 * nval) + 3 * nval := by omega
        _ = nval * (6 * nval + 3) := by ring
    have hnval_lt : nval + 1 ≤ 2 ^ (B * m) := by
      have h2 : 2 ^ (B * m + 1) = 2 * 2 ^ (B * m) := by rw [pow_succ]; ring
      omega
    omega
  -- decompose q = q_lo + qh·2^(Bm), qh ∈ {0,…,5}
  set qlo := qval % 2 ^ (B * m) with hqlo_def
  set qhn := qval / 2 ^ (B * m) with hqhn_def
  have hqlo_lt : qlo < 2 ^ (B * m) := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hqhn_le : qhn ≤ 5 := by
    rw [hqhn_def]
    by_contra hgt
    push_neg at hgt
    have : 6 * 2 ^ (B * m) ≤ qval := by
      calc 6 * 2 ^ (B * m) ≤ qhn * 2 ^ (B * m) := by
            apply Nat.mul_le_mul_right; omega
        _ ≤ qval := Nat.div_mul_le_self _ _
    omega
  have hdecomp : qval = qlo + qhn * 2 ^ (B * m) := by
    rw [hqlo_def, hqhn_def, Nat.add_comm, Nat.mul_comm]
    exact (Nat.div_add_mod qval (2 ^ (B * m))).symm
  -- q_lo witness limbs: value and normalization
  have hqwit' : ∀ i : Fin m, env.get (i₀ + i.val)
      = ((qlo / 2 ^ (B * i.val) % 2 ^ B : ℕ) : F p) := by
    intro i; rw [hqwit i]
  have hqv_val : BigInt.value B (Vector.map (Expression.eval env) qVar) = qlo :=
    BigInt.value_mapRange i₀ qlo env hB hqlo_lt (by intro i; rw [hqwit' i])
  have hqv_norm : BigInt.Normalized B (Vector.map (Expression.eval env) qVar) :=
    normalized_mapRange i₀ qlo env hB (by intro i; rw [hqwit' i])
  -- the top cell evaluates to qhn
  have hqh_eval : Expression.eval env qhVar = ((qhn : ℕ) : F p) := by
    rw [hqhVar, show Expression.eval env (var (F := F p) { index := i₀ + m })
          = env.get (i₀ + m) from rfl, hqhwit]
  have hp2 : (5:ℕ) < p := by
    have h1 : (64:ℕ) ≤ 2 ^ (2 * B) := by
      calc (64:ℕ) = 2 ^ 6 := by norm_num
        _ ≤ 2 ^ (2 * B) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : 64 * 1 * 32 ≤ 2 ^ (2 * B) * (m + 1) * 32 :=
      Nat.mul_le_mul_right 32 (Nat.mul_le_mul h1 (Nat.le_add_left 1 m))
    omega
  have hqhv_val : (Expression.eval env qhVar).val = qhn := by
    rw [hqh_eval]
    apply ZMod.val_natCast_of_lt
    omega
  have hqh_le : (Expression.eval env qhVar).val ≤ 5 := by
    rw [hqhv_val]
    omega
  -- digit bounds
  have ha_lt : ∀ i : Fin m, (Expression.eval env a[i.val]).val < 2 * 2 ^ B := by
    intro i; rw [show Expression.eval env a[i.val] = av[i.val] from by
      rw [← ha_input]; simp only [Vector.getElem_map]]; exact ha_limb i
  have hb_lt : ∀ i : Fin m, (Expression.eval env b[i.val]).val < 3 * 2 ^ B := by
    intro i; rw [show Expression.eval env b[i.val] = bv[i.val] from by
      rw [← hb_input]; simp only [Vector.getElem_map]]; exact hb_limb i
  have hn_lt : ∀ i : Fin m, (Expression.eval env n[i.val]).val < 2 ^ B := by
    intro i; rw [show Expression.eval env n[i.val] = nv[i.val] from by
      rw [← hn_input]; simp only [Vector.getElem_map]]; exact hn_norm i
  have hqd_lt : ∀ i : Fin m, (Expression.eval env qVar[i.val]).val < 2 ^ B := by
    intro i; have := hqv_norm i
    rwa [Fin.getElem_fin, Vector.getElem_map] at this
  have htd_lt : ∀ j : ℕ, (hj : j < m) → (Expression.eval env (t[j]'hj)).val < 3 * 2 ^ B := by
    intro j hj
    have h : (tv[j]'hj).val < 3 * 2 ^ B := ht_limb ⟨j, hj⟩
    rwa [show tv[j]'hj = (Vector.map (Expression.eval env) t)[j]'hj from by rw [ht_input],
      Vector.getElem_map] at h
  have hfield : m * (2 ^ B * 2 ^ B) < p := by
    have h1 : m * (2 ^ B * 2 ^ B) = m * 2 ^ (2 * B) := by rw [two_mul, pow_add]
    rw [h1]
    have h2 : m * 2 ^ (2 * B) ≤ 2 ^ (2 * B) * (m + 1) * 32 := by
      calc m * 2 ^ (2 * B) = 2 ^ (2 * B) * m := Nat.mul_comm _ _
        _ ≤ 2 ^ (2 * B) * ((m + 1) * 32) := mul_le_mul_left' (by omega) _
        _ = 2 ^ (2 * B) * (m + 1) * 32 := (mul_assoc _ _ _).symm
    omega
  have hfield6 : m * ((2 * 2 ^ B) * (3 * 2 ^ B)) < p := by
    have h1 : m * ((2 * 2 ^ B) * (3 * 2 ^ B)) = 6 * (m * 2 ^ (2 * B)) := by
      rw [two_mul B, pow_add]; ring
    rw [h1]
    have h2 : 6 * (m * 2 ^ (2 * B)) ≤ 2 ^ (2 * B) * (m + 1) * 32 := by
      calc 6 * (m * 2 ^ (2 * B)) = 2 ^ (2 * B) * (6 * m) := by ring
        _ ≤ 2 ^ (2 * B) * ((m + 1) * 32) := mul_le_mul_left' (by omega) _
        _ = 2 ^ (2 * B) * (m + 1) * 32 := (mul_assoc _ _ _).symm
    omega
  -- fine coefficient bounds (as in the soundness core)
  have hL_fine : ∀ k : Fin (2 * m - 1),
      (Expression.eval env ((lVecC Pv c)[k.val])).val
        < m * ((2 * 2 ^ B) * (3 * 2 ^ B)) + 2 ^ B := by
    intro k
    have hgetl : (lVecC Pv c)[k.val] = Pv[k.val] + ((c[k.val] : F p) : Expression (F p)) := by
      simp only [lVecC, Vector.getElem_mapFinRange]
    rw [hgetl]
    have hle : (Expression.eval env (Pv[k.val] + ((c[k.val] : F p) : Expression (F p)))).val
        ≤ (Expression.eval env Pv[k.val]).val + (c[k.val]).val := by
      rw [show Expression.eval env (Pv[k.val] + ((c[k.val] : F p) : Expression (F p)))
            = Expression.eval env Pv[k.val] + c[k.val] from rfl]
      exact ZMod.val_add_le _ _
    have hPk : (Expression.eval env Pv[k.val]).val
        < m * ((2 * 2 ^ B) * (3 * 2 ^ B)) := by
      rw [heqAB_get k]
      exact val_coeff_lt_gen2 env a b k ha_lt hb_lt hfield6
    have hck := hc_limb k
    omega
  have hS_fine : ∀ j : Fin (2 * m - 1),
      (Expression.eval env ((sVecT qVar n t)[j.val])).val
        < m * 2 ^ (2 * B) + 3 * 2 ^ B :=
    fun j => coeff_sVecT_fine env qVar n t j hqd_lt hn_lt htd_lt hfield
  refine ⟨hqv_norm, hqhn_le, ⟨fun k => ?_, fun k => ?_⟩, ?_⟩
  · -- LHS obligation
    have hcap := coeff_padD_bound env (lVecC Pv c) k
      (Cv := m * ((2 * 2 ^ B) * (3 * 2 ^ B)) + 2 ^ B) (by positivity) hL_fine
    have h2B : (2 * 2 ^ B) * (3 * 2 ^ B) = 6 * 2 ^ (2 * B) := by
      rw [two_mul B, pow_add]; ring
    rw [h2B] at hcap
    have hBle : 2 ^ B ≤ 2 ^ (2 * B) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hexp : 6 * ((m + 1) * 2 ^ (2 * B)) = m * (6 * 2 ^ (2 * B)) + 6 * 2 ^ (2 * B) := by
      ring
    omega
  · -- RHS obligation
    have hcap := coeff_sVecTD_bound5 env (sVecT qVar n t) qhVar n k
      (Cb := m * 2 ^ (2 * B) + 3 * 2 ^ B) (by positivity) hS_fine hqh_le hn_lt
    have h16B : 16 * 2 ^ B ≤ 2 ^ (2 * B) := by
      have h16 : (16 : ℕ) ≤ 2 ^ B := by
        calc (16 : ℕ) = 2 ^ 4 := by norm_num
          _ ≤ 2 ^ B := Nat.pow_le_pow_right (by norm_num) hB2
      calc 16 * 2 ^ B ≤ 2 ^ B * 2 ^ B := Nat.mul_le_mul_right _ h16
        _ = 2 ^ (2 * B) := by rw [two_mul, pow_add]
    have hexp : (m + 1) * 2 ^ (2 * B) = m * 2 ^ (2 * B) + 2 ^ (2 * B) := by ring
    omega
  · -- the L = 2m value equation
    rw [polyValue_padD]
    rw [polyValue_sVecTD5 env (sVecT qVar n t) qhVar n
      (Cb := m * 2 ^ (2 * B) + 3 * 2 ^ B) (by positivity) hS_fine hqh_le hn_lt
      (by
        have h16B : 16 * 2 ^ B ≤ 2 ^ (2 * B) := by
          have h16 : (16 : ℕ) ≤ 2 ^ B := by
            calc (16 : ℕ) = 2 ^ 4 := by norm_num
              _ ≤ 2 ^ B := Nat.pow_le_pow_right (by norm_num) hB2
          calc 16 * 2 ^ B ≤ 2 ^ B * 2 ^ B := Nat.mul_le_mul_right _ h16
            _ = 2 ^ (2 * B) := by rw [two_mul, pow_add]
        have hexp : 2 ^ (2 * B) * (m + 1) * 32
            = 32 * (m * 2 ^ (2 * B)) + 32 * 2 ^ (2 * B) := by
          ring
        omega)]
    have hLSplit := polyValue_lVecC_split (B := B) env Pv c
      (fun k => by
        rw [heqAB_get k]
        have h1 := val_coeff_lt_gen2 env a b k ha_lt hb_lt hfield6
        have h2 := hc_limb k
        have h2B : (2 * 2 ^ B) * (3 * 2 ^ B) = 6 * 2 ^ (2 * B) := by
          rw [two_mul B, pow_add]; ring
        rw [h2B] at h1
        have hBle : 2 ^ B ≤ 2 ^ (2 * B) := Nat.pow_le_pow_right (by norm_num) (by omega)
        have hh : m * (6 * 2 ^ (2 * B)) = 6 * (m * 2 ^ (2 * B)) := by ring
        have hexp : 2 ^ (2 * B) * (m + 1) * 32
            = 6 * (m * 2 ^ (2 * B)) + (26 * (m * 2 ^ (2 * B)) + 32 * 2 ^ (2 * B)) := by ring
        omega)
    have hPv_map : Vector.map (Expression.eval env) Pv
        = Vector.map (Expression.eval env) (bigIntMulNoReduce a b) := by
      apply Vector.ext; intro k hk
      rw [Vector.getElem_map, Vector.getElem_map]
      exact heqAB_get ⟨k, hk⟩
    have hP : polyValue B (Vector.map (Expression.eval env) (bigIntMulNoReduce a b))
        = aval * bval := by
      rw [polyValue_mul_eq_gen2 env a b ha_lt hb_lt hfield6, ha_input, hb_input]
    have hSplit := polyValue_sVecT_split (B := B) env qVar n t
      (fun k hk => by
        have h1 := val_coeff_lt_gen env qVar n k hqd_lt hn_lt hfield
        have h2 := htd_lt k.val hk
        have h2B : 2 ^ B * 2 ^ B = 2 ^ (2 * B) := by rw [two_mul, pow_add]
        rw [h2B] at h1
        have hBle : 2 ^ B ≤ 2 ^ (2 * B) := Nat.pow_le_pow_right (by norm_num) (by omega)
        have hexp : 2 ^ (2 * B) * (m + 1) * 32
            = m * 2 ^ (2 * B) + (31 * (m * 2 ^ (2 * B)) + 32 * 2 ^ (2 * B)) := by ring
        omega)
    have hSqn : polyValue B (Vector.map (Expression.eval env) (bigIntMulNoReduce qVar n))
        = qlo * nval := by
      rw [polyValue_Sqn_eq env qVar n hqd_lt hn_lt hfield, hqv_val, hn_input]
    rw [hLSplit, hPv_map, hP, hc_val, hSplit, hSqn, ht_input, hqhv_val, hn_input]
    rw [← ht_def, ← hn_def]
    rw [hdecomp] at hkey
    have hring : (qlo + qhn * 2 ^ (B * m)) * nval
        = qlo * nval + qhn * 2 ^ (B * m) * nval := by ring
    omega

/-! ## The circuit -/

/-- Natural-number value of a witnessed limb vector under a prover environment
(private copy of `MulMod.evalValue`, which is `private` there). -/
private def evalValue (B : ℕ) (env : ProverEnvironment (F p))
    (x : Var (BigInt m) (F p)) : ℕ :=
  Solution.Secp256k1ScalarMul.Limbs.fromLimbs B
    ((x.map (Expression.eval env.toEnvironment)).toList.map ZMod.val)

/-- The `main` circuit: witness `q_lo` and the top cell `qh ≤ 5`, normalize
`q_lo`, pin `qh ∈ {0,…,5}` with a degree-6 product chain (four cells, five
rows), and certify `a·b + 3n = (q_lo + qh·2^{Bm})·n + t` as integers via the
`L = 2m` grouped equality. -/
def main (P : BigIntParams p m)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqXV.GVXHyps p (2 * m) P.B gf posOf G V VR)
    (c : Vector (F p) (2 * m - 1))
    [Fact (p > 2)]
    (input : Var (MulModTarget.Inputs m) (F p)) :
    Circuit (F p) Unit :=
  letI : NeZero (2 * m) := ⟨by have := Nat.pos_of_neZero m; omega⟩
  do
  let a := input.a
  let b := input.b
  let n := input.modulus
  let t := input.target

  -- 1. witness q_lo = ((a·b + 3n − t)/n) % 2^(Bm) as BigInt m
  let q ← ProvableType.witness (α := BigInt m) fun env =>
    let qval : ℕ := (evalValue P.B env a * evalValue P.B env b
        + 3 * evalValue P.B env n - evalValue P.B env t) / evalValue P.B env n
        % 2 ^ (P.B * m)
    Vector.ofFn fun k : Fin m => ((qval / 2 ^ (P.B * k.val) % 2 ^ P.B : ℕ) : F p)

  -- 2. witness the quotient's top cell
  let qh ← ProvableType.witness (α := field) fun env =>
    (((evalValue P.B env a * evalValue P.B env b
        + 3 * evalValue P.B env n - evalValue P.B env t) / evalValue P.B env n
        / 2 ^ (P.B * m) : ℕ) : F p)

  -- 3. pin qh ∈ {0,…,5}: a chain of witnessed partial products
  let u1 ← ProvableType.witness (α := field) fun env =>
    let qhn : ℕ := (evalValue P.B env a * evalValue P.B env b
        + 3 * evalValue P.B env n - evalValue P.B env t) / evalValue P.B env n
        / 2 ^ (P.B * m)
    ((qhn * (qhn - 1) : ℕ) : F p)
  let u2 ← ProvableType.witness (α := field) fun env =>
    let qhn : ℕ := (evalValue P.B env a * evalValue P.B env b
        + 3 * evalValue P.B env n - evalValue P.B env t) / evalValue P.B env n
        / 2 ^ (P.B * m)
    ((qhn * (qhn - 1) * (qhn - 2) : ℕ) : F p)
  let u3 ← ProvableType.witness (α := field) fun env =>
    let qhn : ℕ := (evalValue P.B env a * evalValue P.B env b
        + 3 * evalValue P.B env n - evalValue P.B env t) / evalValue P.B env n
        / 2 ^ (P.B * m)
    ((qhn * (qhn - 1) * (qhn - 2) * (qhn - 3) : ℕ) : F p)
  let u4 ← ProvableType.witness (α := field) fun env =>
    let qhn : ℕ := (evalValue P.B env a * evalValue P.B env b
        + 3 * evalValue P.B env n - evalValue P.B env t) / evalValue P.B env n
        / 2 ^ (P.B * m)
    ((qhn * (qhn - 1) * (qhn - 2) * (qhn - 3) * (qhn - 4) : ℕ) : F p)
  assertZero (u1 - qh * (qh - 1))
  assertZero (u2 - u1 * (qh - 2))
  assertZero (u3 - u2 * (qh - 3))
  assertZero (u4 - u3 * (qh - 4))
  assertZero (u4 * (qh - 5))

  -- 4. normalize q_lo
  Normalize.circuit P q

  -- 5. certify over the L = 2m flanks
  let Pc ← interpolatedMul a b
  GroupedEqXV.circuit P.B gf posOf G V VR hgv P.hB1
    { lhs := padD (lVecC Pc c), rhs := sVecTD (sVecT q n t) qh n }

instance elaborated (P : BigIntParams p m)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqXV.GVXHyps p (2 * m) P.B gf posOf G V VR)
    (c : Vector (F p) (2 * m - 1))
    [Fact (p > 2)] :
    ElaboratedCircuit (F p) (MulModTarget.Inputs m) unit (main P gf posOf G V VR hgv c) where
  -- q (m) + qh (1) + u1..u4 (4) + normalize q (m·B) + interpolatedMul (2m−1)
  --   + grouped carries
  localLength _ :=
    m + 5 + m * (P.B - 1) + (2 * m - 1) + GroupedEqXV.widthAllocFrom V.Wf (G - 2) 0
  localLength_eq := by
    intro input offset
    simp only [main, interpolatedMul, circuit_norm, Normalize.circuit, Normalize.elaborated,
      Normalize.main, GroupedEqXV.circuit, GroupedEqXV.elaborated,
      RangeCheck.circuit, RangeCheck.main, Gadgets.ToBits.rangeCheck, Circuit.witnessField, Circuit.assertZero]
    omega
  subcircuitsConsistent := by
    intro input offset
    simp +arith only [main, interpolatedMul, circuit_norm, Normalize.circuit, Normalize.elaborated,
      Normalize.main, GroupedEqXV.circuit, GroupedEqXV.elaborated,
      RangeCheck.circuit, RangeCheck.main, Gadgets.ToBits.rangeCheck, Circuit.witnessField, Circuit.assertZero]
  channelsLawful := by
    intro offset
    simp only [main, interpolatedMul, circuit_norm, Normalize.circuit, Normalize.elaborated,
      Normalize.main, GroupedEqXV.circuit, GroupedEqXV.elaborated,
      RangeCheck.circuit, RangeCheck.main, Gadgets.ToBits.rangeCheck, Circuit.witnessField, Circuit.assertZero]

/-- Preconditions: `a` DOUBLY UNREDUCED (limbs `< 2·2^B`, value `< 2n`); `b`
TRIPLY UNREDUCED (limbs `< 3·2^B`, value `< 3n`); `n` normalized; `target`
limbs `< 3·2^B` with value `< 3n`; `n` positive with the wide-quotient
headroom `2n + 3 ≤ 2^(Bm+1)`; `c` denotes `3n`. -/
def Assumptions (B : ℕ) (c : Vector (F p) (2 * m - 1))
    (input : MulModTarget.Inputs m (F p)) : Prop :=
  (∀ i : Fin m, (input.a[i.val]).val < 2 * 2 ^ B) ∧
    (∀ i : Fin m, (input.b[i.val]).val < 3 * 2 ^ B) ∧
    input.modulus.Normalized B ∧
    (∀ i : Fin m, (input.target[i.val]).val < 3 * 2 ^ B) ∧
    input.a.value B < 2 * input.modulus.value B ∧
    input.b.value B < 3 * input.modulus.value B ∧
    input.target.value B < 3 * input.modulus.value B ∧
    0 < input.modulus.value B ∧
    2 * input.modulus.value B + 3 ≤ 2 ^ (B * m + 1) ∧
    (∀ j : Fin (2 * m - 1), (c[j.val]).val < 2 ^ B) ∧
    polyValue B c = 3 * input.modulus.value B

/-- Postcondition: the target is congruent to `a·b` mod `n`. -/
def Spec (B : ℕ) (input : MulModTarget.Inputs m (F p)) : Prop :=
  input.target.value B % input.modulus.value B
    = (input.a.value B * input.b.value B) % input.modulus.value B

/-- The `MulModTargetW2` formal assertion at the split caps. -/
def circuit (P : BigIntParams p m)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqXV.GVXHyps p (2 * m) P.B gf posOf G V VR)
    (hNf : ∀ j, V.Nf j = 6 * ((m + 1) * 2 ^ (2 * P.B)))
    (hNfR : ∀ j, VR.Nf j = (m + 1) * 2 ^ (2 * P.B))
    (c : Vector (F p) (2 * m - 1))
    (hB2 : 4 ≤ P.B)
    (hp32 : 2 ^ (2 * P.B) * (m + 1) * 32 < p)
    [Fact (p > 2)] :
    FormalAssertion (F p) (MulModTarget.Inputs m) where
    main := main P gf posOf G V VR hgv c
    Assumptions := Assumptions P.B c
    Spec := Spec P.B
    soundness := by
      obtain ⟨B, W, hB, hW, hB1, hWB, hWp, hp⟩ := P
      circuit_proof_start [Normalize.circuit, Normalize.elaborated, Normalize.main,
        Normalize.Assumptions, Normalize.Spec,
        GroupedEqXV.circuit, GroupedEqXV.elaborated,
        GroupedEqXV.Assumptions, GroupedEqX.Spec]
      obtain ⟨ha_limb, hb_limb, hn_norm, ht_limb, hab_lt, hbb_lt, ht_lt3, hn_pos,
        hn3D, hc_limb, hc_val⟩ := h_assumptions
      obtain ⟨hu1_def, hu2_def, hu3_def, hu4_def, hu5_zero, hq_norm, hAB_ops,
        h_eq_impl⟩ := h_holds
      simp only [hNf, hNfR] at h_eq_impl
      have h_pAB := interpolatedMul_soundness (i₀ + (m + 5) + m * (B - 1))
        input_var.a input_var.b env hAB_ops
      refine ⟨?_, interpolatedMul_requirements _ _ _ _⟩
      have ha_input : Vector.map (Expression.eval env) input_var.a = input.a := by
        rw [← h_input]
      have hb_input : Vector.map (Expression.eval env) input_var.b = input.b := by
        rw [← h_input]
      have hn_input : Vector.map (Expression.eval env) input_var.modulus = input.modulus := by
        rw [← h_input]
      have ht_input : Vector.map (Expression.eval env) input_var.target = input.target := by
        rw [← h_input]
      have heqAB_get := interpolatedMul_eval_bridge env (i₀ + (m + 5) + m * (B - 1))
        input_var.a input_var.b (two_m_sub_one_lt hp) h_pAB
      have hqh_le : (Expression.eval env (var (F := F p) { index := i₀ + m })).val ≤ 5 := by
        set qhv := env.get (i₀ + m) with hqhv
        have hu1_val : env.get (i₀ + m + 1) = qhv * (qhv + -1) := by
          linear_combination hu1_def
        have hu2_val : env.get (i₀ + m + 2) = env.get (i₀ + m + 1) * (qhv + -2) := by
          linear_combination hu2_def
        have hu3_val : env.get (i₀ + m + 3) = env.get (i₀ + m + 2) * (qhv + -3) := by
          linear_combination hu3_def
        have hu4_val : env.get (i₀ + m + 4) = env.get (i₀ + m + 3) * (qhv + -4) := by
          linear_combination hu4_def
        have htri : qhv * (qhv + -1) * (qhv + -2) * (qhv + -3) * (qhv + -4)
            * (qhv + -5) = 0 := by
          have h5 : env.get (i₀ + m + 4) * (qhv + -5) = 0 := by
            linear_combination hu5_zero
          rw [hu4_val, hu3_val, hu2_val, hu1_val] at h5
          exact h5
        have hstep : ∀ {x c' : F p}, x + -c' = 0 → x = c' := by
          intro x c' h
          have h' : x - c' = 0 := by rw [sub_eq_add_neg]; exact h
          exact sub_eq_zero.mp h'
        have h015 : qhv = 0 ∨ qhv = 1 ∨ qhv = 2 ∨ qhv = 3 ∨ qhv = 4 ∨ qhv = 5 := by
          rcases mul_eq_zero.mp htri with h4 | h5'
          · rcases mul_eq_zero.mp h4 with h3 | h4'
            · rcases mul_eq_zero.mp h3 with h2 | h3'
              · rcases mul_eq_zero.mp h2 with h1 | h2'
                · rcases mul_eq_zero.mp h1 with h0 | h1'
                  · exact Or.inl h0
                  · exact Or.inr (Or.inl (hstep h1'))
                · exact Or.inr (Or.inr (Or.inl (hstep h2')))
              · exact Or.inr (Or.inr (Or.inr (Or.inl (hstep h3'))))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hstep h4')))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hstep h5')))))
        have hp5 : (5:ℕ) < p := by
          have h1 : (64:ℕ) ≤ 2 ^ (2 * B) := by
            calc (64:ℕ) = 2 ^ 6 := by norm_num
              _ ≤ 2 ^ (2 * B) := Nat.pow_le_pow_right (by norm_num) (by omega)
          have h3 : 64 * 1 * 32 ≤ 2 ^ (2 * B) * (m + 1) * 32 :=
            Nat.mul_le_mul_right 32 (Nat.mul_le_mul h1 (Nat.le_add_left 1 m))
          omega
        show (qhv).val ≤ 5
        rcases h015 with h | h | h | h | h | h
        · rw [h, ZMod.val_zero]; omega
        · rw [h, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega)]; omega
        · rw [h, show ((2 : F p)) = ((2:ℕ) : F p) from by norm_num,
            ZMod.val_natCast_of_lt (by omega)]; omega
        · rw [h, show ((3 : F p)) = ((3:ℕ) : F p) from by norm_num,
            ZMod.val_natCast_of_lt (by omega)]; omega
        · rw [h, show ((4 : F p)) = ((4:ℕ) : F p) from by norm_num,
            ZMod.val_natCast_of_lt (by omega)]; omega
        · rw [h, show ((5 : F p)) = ((5:ℕ) : F p) from by norm_num,
            ZMod.val_natCast_of_lt (by omega)]
      exact soundness_core_wm (B := B) hB2 hp32 i₀ env
        input_var.a input_var.b input_var.modulus input_var.target c
        (interpolatedMul input_var.a input_var.b (i₀ + (m + 5) + m * (B - 1))).1
        (var { index := i₀ + m })
        input.a input.b input.modulus input.target
        ha_input hb_input hn_input ht_input
        ha_limb hb_limb
        hn_norm ht_limb hc_limb hc_val hq_norm hqh_le
        heqAB_get h_eq_impl
    completeness := by
      obtain ⟨B, W, hB, hW, hB1, hWB, hWp, hp⟩ := P
      circuit_proof_start [Normalize.circuit, Normalize.elaborated, Normalize.main,
        Normalize.Assumptions, Normalize.Spec,
        GroupedEqXV.circuit, GroupedEqXV.elaborated,
        GroupedEqXV.Assumptions, GroupedEqX.Spec]
      obtain ⟨ha_limb, hb_limb, hn_norm, ht_limb, hab_lt, hbb_lt, ht_lt3, hn_pos,
        hn3D, hc_limb, hc_val⟩ := h_assumptions
      obtain ⟨hq_env, hqh_env, hu1_env, hu2_env, hu3_env, hu4_env, hAB_uses⟩ := h_env
      have h_pvAB := interpolatedMul_usesLocalWitnesses (i₀ + (m + 5) + m * (B - 1))
        (i₀ + (m + 5) + m * (B - 1)) input_var.a input_var.b env rfl hAB_uses
      have ha_input : Vector.map (Expression.eval env.toEnvironment) input_var.a = input.a := by
        rw [← h_input]
      have hb_input : Vector.map (Expression.eval env.toEnvironment) input_var.b = input.b := by
        rw [← h_input]
      have hn_input : Vector.map (Expression.eval env.toEnvironment) input_var.modulus
          = input.modulus := by
        rw [← h_input]
      have ht_input : Vector.map (Expression.eval env.toEnvironment) input_var.target
          = input.target := by
        rw [← h_input]
      have heva : evalValue B env input_var.a = BigInt.value B input.a := by
        rw [evalValue, BigInt.value, ← ha_input]
      have hevb : evalValue B env input_var.b = BigInt.value B input.b := by
        rw [evalValue, BigInt.value, ← hb_input]
      have hevn : evalValue B env input_var.modulus = BigInt.value B input.modulus := by
        rw [evalValue, BigInt.value, ← hn_input]
      have hevt : evalValue B env input_var.target = BigInt.value B input.target := by
        rw [evalValue, BigInt.value, ← ht_input]
      have hqwit : ∀ i : Fin m, env.toEnvironment.get (i₀ + i.val)
          = (((BigInt.value B input.a * BigInt.value B input.b
                + 3 * BigInt.value B input.modulus - BigInt.value B input.target)
              / BigInt.value B input.modulus % 2 ^ (B * m)
              / 2 ^ (B * i.val) % 2 ^ B : ℕ) : F p) := by
        intro i; rw [hq_env i, Vector.getElem_ofFn, heva, hevb, hevn, hevt]
      have hqhwit : env.toEnvironment.get (i₀ + m)
          = (((BigInt.value B input.a * BigInt.value B input.b
                + 3 * BigInt.value B input.modulus - BigInt.value B input.target)
              / BigInt.value B input.modulus / 2 ^ (B * m) : ℕ) : F p) := by
        rw [hqh_env, heva, hevb, hevn, hevt]
      have heqAB_get := interpolatedMul_eval_bridge_uses env.toEnvironment
        (i₀ + (m + 5) + m * (B - 1)) input_var.a input_var.b h_pvAB
      have core := completeness_core_wm (B := B) hB hB2 hp32 i₀ env.toEnvironment
        input_var.a input_var.b input_var.modulus input_var.target c
        (interpolatedMul input_var.a input_var.b (i₀ + (m + 5) + m * (B - 1))).1
        input.a input.b input.modulus input.target
        ha_input hb_input hn_input ht_input
        ha_limb hb_limb
        hn_norm ht_limb hc_limb hc_val
        hab_lt hbb_lt hn_pos hn3D ht_lt3 h_spec
        hqwit hqhwit heqAB_get
      simp only [hNf, hNfR]
      have hA015 : (evalValue B env input_var.a * evalValue B env input_var.b
            + 3 * evalValue B env input_var.modulus - evalValue B env input_var.target)
              / evalValue B env input_var.modulus / 2 ^ (B * m) = 0
          ∨ (evalValue B env input_var.a * evalValue B env input_var.b
            + 3 * evalValue B env input_var.modulus - evalValue B env input_var.target)
              / evalValue B env input_var.modulus / 2 ^ (B * m) = 1
          ∨ (evalValue B env input_var.a * evalValue B env input_var.b
            + 3 * evalValue B env input_var.modulus - evalValue B env input_var.target)
              / evalValue B env input_var.modulus / 2 ^ (B * m) = 2
          ∨ (evalValue B env input_var.a * evalValue B env input_var.b
            + 3 * evalValue B env input_var.modulus - evalValue B env input_var.target)
              / evalValue B env input_var.modulus / 2 ^ (B * m) = 3
          ∨ (evalValue B env input_var.a * evalValue B env input_var.b
            + 3 * evalValue B env input_var.modulus - evalValue B env input_var.target)
              / evalValue B env input_var.modulus / 2 ^ (B * m) = 4
          ∨ (evalValue B env input_var.a * evalValue B env input_var.b
            + 3 * evalValue B env input_var.modulus - evalValue B env input_var.target)
              / evalValue B env input_var.modulus / 2 ^ (B * m) = 5 := by
        rw [heva, hevb, hevn, hevt]
        have h := core.2.1
        generalize hX : (BigInt.value B input.a * BigInt.value B input.b
            + 3 * BigInt.value B input.modulus - BigInt.value B input.target)
          / BigInt.value B input.modulus / 2 ^ (B * m) = X at h ⊢
        omega
      refine ⟨?_, ?_, ?_, ?_, ?_, core.1,
        interpolatedMul_completeness (i₀ + (m + 5) + m * (B - 1)) input_var.a input_var.b env
          h_pvAB,
        core.2.2⟩
      · -- u1 = qh·(qh−1)
        rw [hu1_env, hqh_env]
        rcases hA015 with h | h | h | h | h | h <;> rw [h] <;> norm_num
      · -- u2 = u1·(qh−2)
        rw [hu2_env, hu1_env, hqh_env]
        rcases hA015 with h | h | h | h | h | h <;> rw [h] <;> norm_num
      · -- u3 = u2·(qh−3)
        rw [hu3_env, hu2_env, hqh_env]
        rcases hA015 with h | h | h | h | h | h <;> rw [h] <;> norm_num
      · -- u4 = u3·(qh−4)
        rw [hu4_env, hu3_env, hqh_env]
        rcases hA015 with h | h | h | h | h | h <;> rw [h] <;> norm_num
      · -- the pin row: u4·(qh−5) = 0
        rw [hu4_env, hqh_env]
        rcases hA015 with h | h | h | h | h | h <;> rw [h] <;> norm_num

/-! ## Computable witnesses -/

private lemma evalValue_stable (B : ℕ) (x : Var (BigInt m) (F p))
    {env env' : ProverEnvironment (F p)}
    (h : eval env x = eval env' x) :
    evalValue B env x = evalValue B env' x := by
  have h_vec :
      x.map (Expression.eval env.toEnvironment)
        = x.map (Expression.eval env'.toEnvironment) := by
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_map]
    have h_i := congrArg (fun y : BigInt m (F p) => y[i]) h
    rw [ProvableType.getElem_eval_fields_prover (env := env) x i hi,
      ProvableType.getElem_eval_fields_prover (env := env') x i hi]
    exact h_i
  simp [evalValue, h_vec]

attribute [local irreducible] interpolatedMul Normalize.circuit GroupedEqXV.circuit

theorem computableWitnesses (P : BigIntParams p m)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqXV.GVXHyps p (2 * m) P.B gf posOf G V VR)
    (hNf : ∀ j, V.Nf j = 6 * ((m + 1) * 2 ^ (2 * P.B)))
    (hNfR : ∀ j, VR.Nf j = (m + 1) * 2 ^ (2 * P.B))
    (c : Vector (F p) (2 * m - 1))
    (hB2 : 4 ≤ P.B)
    (hp32 : 2 ^ (2 * P.B) * (m + 1) * 32 < p)
    [Fact (p > 2)] :
    (circuit P gf posOf G V VR hgv hNf hNfR c hB2 hp32).ComputableWitnesses := by
  letI : NeZero (2 * m) := ⟨by have := Nat.pos_of_neZero m; omega⟩
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition input env env')
    ((main P gf posOf G V VR hgv c input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main
  let qc : Circuit (F p) (Var (BigInt m) (F p)) := ProvableType.witness (α := BigInt m) fun env =>
    let qval : ℕ := (evalValue P.B env input.a * evalValue P.B env input.b
        + 3 * evalValue P.B env input.modulus - evalValue P.B env input.target)
        / evalValue P.B env input.modulus % 2 ^ (P.B * m)
    Vector.ofFn fun k : Fin m => ((qval / 2 ^ (P.B * k.val) % 2 ^ P.B : ℕ) : F p)
  let q := qc.output offset
  let qhOff := offset + qc.localLength offset
  let qh : Expression (F p) := (ProvableType.witness (α := field)
    (fun env => (((evalValue P.B env input.a * evalValue P.B env input.b
        + 3 * evalValue P.B env input.modulus - evalValue P.B env input.target)
        / evalValue P.B env input.modulus / 2 ^ (P.B * m) : ℕ) : F p))).output qhOff
  let u1Off := qhOff + 1
  let u2Off := u1Off + 1
  let u3Off := u2Off + 1
  let u4Off := u3Off + 1
  let nqOff := u4Off + 1
  let nqc : Circuit (F p) Unit := Normalize.circuit P q
  let pcOff := nqOff + nqc.localLength nqOff
  let pcv := (interpolatedMul input.a input.b).output pcOff
  let eqOff := pcOff + (interpolatedMul input.a input.b).localLength pcOff
  have h_qlen : qc.localLength offset = m := by
    simp [qc, ProvableType.witness, Circuit.localLength, Operations.localLength, size]
  have h_pclen : (interpolatedMul input.a input.b).localLength pcOff = 2 * m - 1 :=
    interpolatedMul_localLength pcOff input.a input.b
  have hstab : ∀ (env₁ env₂ : ProverEnvironment (F p)),
      eval env₁ input = eval env₂ input →
      evalValue P.B env₁ input.a = evalValue P.B env₂ input.a
        ∧ evalValue P.B env₁ input.b = evalValue P.B env₂ input.b
        ∧ evalValue P.B env₁ input.modulus = evalValue P.B env₂ input.modulus
        ∧ evalValue P.B env₁ input.target = evalValue P.B env₂ input.target := by
    intro env₁ env₂ h_input
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact evalValue_stable P.B input.a (by
        simpa [circuit_norm] using congrArg (fun x : MulModTarget.Inputs m (F p) => x.a) h_input)
    · exact evalValue_stable P.B input.b (by
        simpa [circuit_norm] using congrArg (fun x : MulModTarget.Inputs m (F p) => x.b) h_input)
    · exact evalValue_stable P.B input.modulus (by
        simpa [circuit_norm] using congrArg
          (fun x : MulModTarget.Inputs m (F p) => x.modulus) h_input)
    · exact evalValue_stable P.B input.target (by
        simpa [circuit_norm] using congrArg
          (fun x : MulModTarget.Inputs m (F p) => x.target) h_input)
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.provableWitness_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.witnessField_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.assertZero_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.pure_structuralComputableWitnesses_iff,
    and_true]
  and_intros
  · -- q_lo witness reads only the input
    intro _ h_input
    obtain ⟨ha, hb, hn, ht⟩ := hstab env env' h_input
    simp only [ha, hb, hn, ht]
  · -- the top-cell witness reads only the input
    intro _ h_input
    obtain ⟨ha, hb, hn, ht⟩ := hstab env env' h_input
    simp only [ha, hb, hn, ht]
  · -- u1 reads only the input
    intro _ h_input
    obtain ⟨ha, hb, hn, ht⟩ := hstab env env' h_input
    simp only [ha, hb, hn, ht]
  · -- u2 reads only the input
    intro _ h_input
    obtain ⟨ha, hb, hn, ht⟩ := hstab env env' h_input
    simp only [ha, hb, hn, ht]
  · -- u3 reads only the input
    intro _ h_input
    obtain ⟨ha, hb, hn, ht⟩ := hstab env env' h_input
    simp only [ha, hb, hn, ht]
  · -- u4 reads only the input
    intro _ h_input
    obtain ⟨ha, hb, hn, ht⟩ := hstab env env' h_input
    simp only [ha, hb, hn, ht]
  · -- the u1-definition row carries no witnesses
    trivial
  · -- the u2-definition row carries no witnesses
    trivial
  · -- the u3-definition row carries no witnesses
    trivial
  · -- the u4-definition row carries no witnesses
    trivial
  · -- the pin row carries no witnesses
    trivial
  · -- Normalize q_lo
    exact Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
      (Normalize.circuit P) input q nqOff
      (by
        intro k env env' hle h_agree _
        have hk : offset + m ≤ k := by
          dsimp only [nqOff, u4Off, u3Off, u2Off, u1Off, qhOff] at hle
          rw [h_qlen] at hle
          omega
        exact bigIntWitnessOutput_stable _ h_agree hk)
      (Normalize.computableWitnesses P) env env'
  · -- interpolatedMul a b
    exact interpolatedMul_structuralComputableWitnesses input input.a input.b pcOff
      (by
        intro k env env' _ _ h_input
        have ha : eval env input.a = eval env' input.a := by
          simpa [circuit_norm] using congrArg (fun x : MulModTarget.Inputs m (F p) => x.a) h_input
        have hb : eval env input.b = eval env' input.b := by
          simpa [circuit_norm] using congrArg (fun x : MulModTarget.Inputs m (F p) => x.b) h_input
        exact ⟨ha, hb⟩)
      env env'
  · -- GroupedEqXV over the L = 2m flanks
    exact Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
      (GroupedEqXV.circuit P.B gf posOf G V VR hgv P.hB1) input
      { lhs := padD (lVecC pcv c), rhs := sVecTD (sVecT q input.modulus input.target) qh input.modulus }
      eqOff
      (by
        intro k env env' hle h_agree h_input
        have hk_pc : pcOff + (2 * m - 1) ≤ k := by
          dsimp only [eqOff] at hle
          rw [h_pclen] at hle
          omega
        have hk_q : offset + m ≤ k := by
          dsimp only [eqOff, pcOff, nqOff, u4Off, u3Off, u2Off, u1Off, qhOff] at hle
          rw [h_qlen] at hle
          omega
        have hPc : Vector.map (Expression.eval env.toEnvironment) pcv
            = Vector.map (Expression.eval env'.toEnvironment) pcv :=
          interpolatedMul_output_stable pcOff input.a input.b h_agree hk_pc
        have hq_vec : eval env q = eval env' q := bigIntWitnessOutput_stable _ h_agree hk_q
        have hqh_eval : Expression.eval env.toEnvironment qh
            = Expression.eval env'.toEnvironment qh := by
          show env.get qhOff = env'.get qhOff
          have hq : qhOff = offset + m := by dsimp only [qhOff]; rw [h_qlen]
          rw [hq]
          apply h_agree (offset + m)
          have : offset + m + 1 ≤ k := by
            dsimp only [eqOff, pcOff, nqOff, u4Off, u3Off, u2Off, u1Off, qhOff] at hle
            rw [h_qlen] at hle
            omega
          omega
        have hn : eval env input.modulus = eval env' input.modulus := by
          simpa [circuit_norm] using congrArg
            (fun x : MulModTarget.Inputs m (F p) => x.modulus) h_input
        have ht : eval env input.target = eval env' input.target := by
          simpa [circuit_norm] using congrArg
            (fun x : MulModTarget.Inputs m (F p) => x.target) h_input
        have hL8 : Vector.map (Expression.eval env.toEnvironment) (padD (lVecC pcv c))
            = Vector.map (Expression.eval env'.toEnvironment) (padD (lVecC pcv c)) := by
          apply Vector.ext
          intro i hi
          simp only [Vector.getElem_map, padD, Vector.getElem_mapFinRange]
          by_cases hlt : i < 2 * m - 1
          · rw [dif_pos hlt]
            simp only [lVecC, Vector.getElem_mapFinRange]
            have hpc_i : Expression.eval env.toEnvironment (pcv[i]'hlt)
                = Expression.eval env'.toEnvironment (pcv[i]'hlt) := by
              have := congrArg (fun v : Vector (F p) (2 * m - 1) => v[i]'hlt) hPc
              simpa only [Vector.getElem_map] using this
            rw [show Expression.eval env.toEnvironment
                  (pcv[i]'hlt + ((c[i]'hlt : F p) : Expression (F p)))
                  = Expression.eval env.toEnvironment (pcv[i]'hlt) + c[i]'hlt from rfl,
              show Expression.eval env'.toEnvironment
                  (pcv[i]'hlt + ((c[i]'hlt : F p) : Expression (F p)))
                  = Expression.eval env'.toEnvironment (pcv[i]'hlt) + c[i]'hlt from rfl,
              hpc_i]
          · rw [dif_neg hlt]
            rfl
        have hS8 : Vector.map (Expression.eval env.toEnvironment)
              (sVecTD (sVecT q input.modulus input.target) qh input.modulus)
            = Vector.map (Expression.eval env'.toEnvironment)
              (sVecTD (sVecT q input.modulus input.target) qh input.modulus) := by
          apply Vector.ext
          intro i hi
          have hbase_i : ∀ (hlt : i < 2 * m - 1),
              Expression.eval env.toEnvironment
                ((sVecT q input.modulus input.target)[i]'hlt)
              = Expression.eval env'.toEnvironment
                ((sVecT q input.modulus input.target)[i]'hlt) := by
            intro hlt
            have hsq_i : Expression.eval env.toEnvironment
                  ((bigIntMulNoReduce q input.modulus)[i]'hlt)
                = Expression.eval env'.toEnvironment
                  ((bigIntMulNoReduce q input.modulus)[i]'hlt) :=
              bigIntMulNoReduce_coeff_stable env.toEnvironment env'.toEnvironment
                q input.modulus
                (fun j hj => bigInt_getElem_eval_eq hq_vec j hj)
                (fun j hj => bigInt_getElem_eval_eq hn j hj) ⟨i, hlt⟩
            simp only [sVecT, Vector.getElem_mapFinRange]
            split
            · rename_i hmi
              have ht_i : Expression.eval env.toEnvironment (input.target[i]'hmi)
                  = Expression.eval env'.toEnvironment (input.target[i]'hmi) :=
                bigInt_getElem_eval_eq ht i hmi
              simp only [Expression.eval, hsq_i, ht_i]
            · exact hsq_i
          simp only [Vector.getElem_map, sVecTD, Vector.getElem_mapFinRange]
          have hflank_i : ∀ (hm' : m ≤ i ∧ i - m < m),
              Expression.eval env.toEnvironment (qh * input.modulus[i - m]'hm'.2)
              = Expression.eval env'.toEnvironment (qh * input.modulus[i - m]'hm'.2) := by
            intro hm'
            rw [show Expression.eval env.toEnvironment (qh * input.modulus[i - m]'hm'.2)
                  = Expression.eval env.toEnvironment qh
                    * Expression.eval env.toEnvironment (input.modulus[i - m]'hm'.2) from rfl,
              show Expression.eval env'.toEnvironment (qh * input.modulus[i - m]'hm'.2)
                  = Expression.eval env'.toEnvironment qh
                    * Expression.eval env'.toEnvironment (input.modulus[i - m]'hm'.2) from rfl,
              hqh_eval, bigInt_getElem_eval_eq hn (i - m) hm'.2]
          by_cases hlt : i < 2 * m - 1
          · rw [dif_pos hlt]
            by_cases hm' : m ≤ i ∧ i - m < m
            · rw [dif_pos hm']
              rw [show Expression.eval env.toEnvironment
                    ((sVecT q input.modulus input.target)[i]'hlt
                      + qh * input.modulus[i - m]'hm'.2)
                    = Expression.eval env.toEnvironment
                        ((sVecT q input.modulus input.target)[i]'hlt)
                      + Expression.eval env.toEnvironment (qh * input.modulus[i - m]'hm'.2)
                    from rfl,
                show Expression.eval env'.toEnvironment
                    ((sVecT q input.modulus input.target)[i]'hlt
                      + qh * input.modulus[i - m]'hm'.2)
                    = Expression.eval env'.toEnvironment
                        ((sVecT q input.modulus input.target)[i]'hlt)
                      + Expression.eval env'.toEnvironment (qh * input.modulus[i - m]'hm'.2)
                    from rfl,
                hbase_i hlt, hflank_i hm']
            · rw [dif_neg hm']
              rw [eval_add_zero, eval_add_zero, hbase_i hlt]
          · rw [dif_neg hlt]
            by_cases hm' : m ≤ i ∧ i - m < m
            · rw [dif_pos hm']
              rw [eval_zero_add, eval_zero_add, hflank_i hm']
            · rw [dif_neg hm']
              rfl
        simp only [circuit_norm]
        rw [hL8, hS8])
      (GroupedEqXV.computableWitnesses P.B gf posOf G V VR hgv P.hB1) env env'

end MulModTargetW2
end Solution.Secp256k1ScalarMul
