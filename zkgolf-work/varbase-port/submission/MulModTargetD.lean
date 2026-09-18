import Solution.Secp256k1ScalarMul.MulMod



namespace Solution.Secp256k1ScalarMul
namespace MulModTargetD
open MulMod

variable {p : ℕ} [Fact p.Prime]
variable {m : ℕ} [NeZero m]


def padD (v : Vector (Expression (F p)) (2 * m - 1)) : Vector (Expression (F p)) (2 * m) :=
  Vector.mapFinRange (2 * m) fun k => if h : k.val < 2 * m - 1 then v[k.val] else 0


def sVecTD (base : Vector (Expression (F p)) (2 * m - 1)) (qh : Expression (F p))
    (n : Var (BigInt m) (F p)) : Vector (Expression (F p)) (2 * m) :=
  Vector.mapFinRange (2 * m) fun k =>
    (if h : k.val < 2 * m - 1 then base[k.val] else 0)
    + (if hm : m ≤ k.val ∧ k.val - m < m then qh * n[k.val - m]'hm.2 else 0)

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




lemma coeff_padD_bound {Cv : ℕ} (env : Environment (F p))
    (v : Vector (Expression (F p)) (2 * m - 1)) (k : Fin (2 * m))
    (hCv : 0 < Cv)
    (hv : ∀ j : Fin (2 * m - 1), (Expression.eval env v[j.val]).val < Cv) :
    (Expression.eval env ((padD v)[k.val])).val < Cv := by
  simp only [padD, Vector.getElem_mapFinRange]
  by_cases h : k.val < 2 * m - 1
  · rw [dif_pos h]; exact hv ⟨k.val, h⟩
  · rw [dif_neg h]
    rw [show Expression.eval env (0 : Expression (F p)) = 0 from rfl, ZMod.val_zero]
    exact hCv


lemma coeff_sVecTD_bound {B Cb : ℕ} (env : Environment (F p))
    (base : Vector (Expression (F p)) (2 * m - 1)) (qh : Expression (F p))
    (n : Var (BigInt m) (F p)) (k : Fin (2 * m))
    (hCb : 0 < Cb)
    (hbase : ∀ j : Fin (2 * m - 1), (Expression.eval env base[j.val]).val < Cb)
    (hqh : Expression.eval env qh = 0 ∨ Expression.eval env qh = 1)
    (hn : ∀ i : Fin m, (Expression.eval env n[i.val]).val < 2 ^ B) :
    (Expression.eval env ((sVecTD base qh n)[k.val])).val < Cb + 2 ^ B := by
  have hpos : (0:ℕ) < 2 ^ B := Nat.two_pow_pos B
  have hflank : ∀ (hm' : m ≤ k.val ∧ k.val - m < m),
      (Expression.eval env (qh * n[k.val - m]'hm'.2)).val < 2 ^ B := by
    intro hm'
    rw [show Expression.eval env (qh * n[k.val - m]'hm'.2)
          = Expression.eval env qh * Expression.eval env (n[k.val - m]'hm'.2) from rfl]
    rcases hqh with h0 | h1
    · rw [h0, zero_mul, ZMod.val_zero]; omega
    · rw [h1, one_mul]; exact hn ⟨k.val - m, hm'.2⟩
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


lemma polyValue_padD {B : ℕ} (env : Environment (F p))
    (v : Vector (Expression (F p)) (2 * m - 1)) :
    polyValue B (Vector.map (Expression.eval env) (padD v))
      = polyValue B (Vector.map (Expression.eval env) v) := by
  have hm : 0 < m := Nat.pos_of_neZero m
  have h2 : polyValue B (Vector.map (Expression.eval env) (padD v))
      = ∑ i ∈ Finset.range (2 * m),
          (fun j => if h : j < 2 * m - 1
            then (Expression.eval env (v[j]'h)).val * 2 ^ (B * j) else 0) i := by
    apply polyValue_eq_range_sum
    intro i h
    by_cases hi : i < 2 * m - 1
    · simp only [dif_pos hi, Vector.getElem_map, padD, Vector.getElem_mapFinRange]
    · simp only [dif_neg hi, Vector.getElem_map, padD, Vector.getElem_mapFinRange]
      rw [show Expression.eval env (0 : Expression (F p)) = 0 from rfl, ZMod.val_zero, zero_mul]
  have h1 : polyValue B (Vector.map (Expression.eval env) v)
      = ∑ i ∈ Finset.range (2 * m - 1),
          (fun j => if h : j < 2 * m - 1
            then (Expression.eval env (v[j]'h)).val * 2 ^ (B * j) else 0) i := by
    apply polyValue_eq_range_sum
    intro i h
    simp only [dif_pos h, Vector.getElem_map]
  rw [h1, h2]
  symm
  have hsub : Finset.range (2 * m - 1) ⊆ Finset.range (2 * m) := by
    intro x hx
    rw [Finset.mem_range] at hx ⊢
    omega
  apply Finset.sum_subset hsub
  intro x _ hx
  rw [Finset.mem_range] at hx
  simp only [dif_neg hx]


lemma polyValue_sVecTD {B Cb : ℕ} (env : Environment (F p))
    (base : Vector (Expression (F p)) (2 * m - 1)) (qh : Expression (F p))
    (n : Var (BigInt m) (F p))
    (hCb : 0 < Cb)
    (hbase : ∀ j : Fin (2 * m - 1), (Expression.eval env base[j.val]).val < Cb)
    (hqh : Expression.eval env qh = 0 ∨ Expression.eval env qh = 1)
    (hn : ∀ i : Fin m, (Expression.eval env n[i.val]).val < 2 ^ B)
    (hp1 : Cb + 2 ^ B < p) :
    polyValue B (Vector.map (Expression.eval env) (sVecTD base qh n))
      = polyValue B (Vector.map (Expression.eval env) base)
        + (Expression.eval env qh).val * 2 ^ (B * m)
            * BigInt.value B (Vector.map (Expression.eval env) n) := by
  have hm : 0 < m := Nat.pos_of_neZero m
  have hpos : (0:ℕ) < 2 ^ B := Nat.two_pow_pos B
  -- per-coefficient split of the value
  have hqhv : (Expression.eval env qh).val = 0 ∨ (Expression.eval env qh).val = 1 := by
    rcases hqh with h | h
    · left; rw [h, ZMod.val_zero]
    · right
      rw [h]
      haveI : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
      exact ZMod.val_one p
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
    have hflankv : ∀ (hm' : m ≤ i ∧ i - m < m),
        (Expression.eval env (qh * n[i - m]'hm'.2)).val
          = (Expression.eval env qh).val * (Expression.eval env (n[i - m]'hm'.2)).val := by
      intro hm'
      rw [show Expression.eval env (qh * n[i - m]'hm'.2)
            = Expression.eval env qh * Expression.eval env (n[i - m]'hm'.2) from rfl]
      rcases hqh with h0 | h1
      · rw [h0, zero_mul, ZMod.val_zero, zero_mul]
      · rw [h1, one_mul, ZMod.val_one_eq_one_mod]
        haveI : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
        rw [Nat.mod_eq_of_lt (Fact.out : 1 < p), one_mul]
    by_cases hlt : i < 2 * m - 1
    · rw [dif_pos hlt, dif_pos hlt]
      by_cases hm' : m ≤ i ∧ i - m < m
      · rw [dif_pos hm', dif_pos hm']
        rw [show Expression.eval env (base[i]'hlt + qh * n[i - m]'hm'.2)
              = Expression.eval env (base[i]'hlt)
                + Expression.eval env (qh * n[i - m]'hm'.2) from rfl]
        rw [ZMod.val_add_of_lt (by
          have h1 : (Expression.eval env (base[i]'hlt)).val < Cb := hbase ⟨i, hlt⟩
          have h2 : (Expression.eval env (qh * n[i - m]'hm'.2)).val < 2 ^ B := by
            rw [hflankv hm']
            rcases hqhv with h0 | h1'
            · rw [h0, zero_mul]; omega
            · rw [h1', one_mul]; exact hn ⟨i - m, hm'.2⟩
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
  -- split the sum
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
  · -- base flank
    have h1 : polyValue B (Vector.map (Expression.eval env) base)
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
  · -- qh flank: reindex to 2^(Bm)·value(n)
    have hvanish : ∀ x ∈ Finset.range (2 * m), x ∉ Finset.Ico m (2 * m) →
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


lemma congruence_of_offset_eqD {a b qlo qh n t B m' : ℕ}
    (heq : a * b + 3 * n = (qlo + qh * 2 ^ (B * m')) * n + t) :
    t % n = a * b % n := by
  have h2 : t + (qlo + qh * 2 ^ (B * m')) * n = a * b + 3 * n := by omega
  have h3 : (t + (qlo + qh * 2 ^ (B * m')) * n) % n = (a * b + 3 * n) % n := by rw [h2]
  simpa only [Nat.add_mul_mod_self_right] using h3


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




lemma coeff_sVecT_fine {B : ℕ} (env : Environment (F p))
    (q n t : Var (BigInt m) (F p)) (k : Fin (2 * m - 1))
    (hq : ∀ i : Fin m, (Expression.eval env q[i.val]).val < 2 ^ B)
    (hn : ∀ i : Fin m, (Expression.eval env n[i.val]).val < 2 ^ B)
    (ht : ∀ j : ℕ, (hj : j < m) → (Expression.eval env (t[j]'hj)).val < 3 * 2 ^ B)
    (hfield : m * (2 ^ B * 2 ^ B) < p) :
    (Expression.eval env ((sVecT q n t)[k.val])).val < m * 2 ^ (2 * B) + 3 * 2 ^ B := by
  have hpos : (0:ℕ) < 2 ^ B := Nat.two_pow_pos B
  have h2B : 2 ^ B * 2 ^ B = 2 ^ (2 * B) := by rw [two_mul, pow_add]
  have hconv := val_coeff_lt_gen env q n k hq hn (by rw [h2B] at hfield ⊢; omega)
  rw [h2B] at hconv
  simp only [sVecT, Vector.getElem_mapFinRange]
  by_cases hk : k.val < m
  · rw [dif_pos hk]
    have hadd : (Expression.eval env ((bigIntMulNoReduce q n)[k.val] + t[k.val]'hk)).val
        ≤ (Expression.eval env ((bigIntMulNoReduce q n)[k.val])).val
          + (Expression.eval env (t[k.val]'hk)).val := by
      rw [show Expression.eval env ((bigIntMulNoReduce q n)[k.val] + t[k.val]'hk)
            = Expression.eval env ((bigIntMulNoReduce q n)[k.val])
              + Expression.eval env (t[k.val]'hk) from rfl]
      exact ZMod.val_add_le _ _
    have := ht k.val hk
    omega
  · rw [dif_neg hk]
    omega

end MulModTargetD
end Solution.Secp256k1ScalarMul
