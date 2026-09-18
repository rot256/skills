import Solution.Secp256k1ScalarMul.MulModTargetD



namespace Solution.Secp256k1ScalarMul
namespace MulModTargetW
open MulMod MulModTargetD

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

omit [Fact p.Prime] in

private lemma polyValue_eq_range_sum {B kk : ℕ} (vv : Vector (F p) kk) (f : ℕ → ℕ)
    (hf : ∀ (i : ℕ) (h : i < kk), (vv[i]'h).val * 2 ^ (B * i) = f i) :
    polyValue B vv = ∑ i ∈ Finset.range kk, f i := by
  rw [polyValue, ← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_congr rfl fun i _ => hf i.val i.isLt




lemma val_three_mul (h3 : 3 < p) (z : F p) (h : 3 * z.val < p) :
    ((3 : F p) * z).val = 3 * z.val := by
  have hcast : (3 : F p) = ((3 : ℕ) : F p) := by norm_num
  rw [hcast, ZMod.val_mul, ZMod.val_natCast_of_lt h3, Nat.mod_eq_of_lt h]


lemma eval_three_mul (env : Environment (F p)) (z : Expression (F p)) :
    Expression.eval env (((3 : F p) : Expression (F p)) * z)
      = (3 : F p) * Expression.eval env z := rfl




def lVecW (v : Vector (Expression (F p)) (2 * m - 1)) (c : Vector (F p) (2 * m)) :
    Vector (Expression (F p)) (2 * m) :=
  Vector.mapFinRange (2 * m) fun k =>
    (if h : k.val < 2 * m - 1 then v[k.val] else 0) + ((c[k.val] : F p) : Expression (F p))

omit [NeZero m] in

lemma coeff_lVecW_bound {Cv Cc : ℕ} (env : Environment (F p))
    (v : Vector (Expression (F p)) (2 * m - 1)) (c : Vector (F p) (2 * m))
    (k : Fin (2 * m))
    (hCv : 0 < Cv)
    (hv : ∀ j : Fin (2 * m - 1), (Expression.eval env v[j.val]).val < Cv)
    (hc : ∀ j : Fin (2 * m), (c[j.val]).val < Cc) :
    (Expression.eval env ((lVecW v c)[k.val])).val < Cv + Cc := by
  simp only [lVecW, Vector.getElem_mapFinRange]
  by_cases h : k.val < 2 * m - 1
  · rw [dif_pos h]
    have hle : (Expression.eval env (v[k.val]'h + ((c[k.val] : F p) : Expression (F p)))).val
        ≤ (Expression.eval env (v[k.val]'h)).val + (c[k.val]).val := by
      rw [show Expression.eval env (v[k.val]'h + ((c[k.val] : F p) : Expression (F p)))
            = Expression.eval env (v[k.val]'h) + c[k.val] from rfl]
      exact ZMod.val_add_le _ _
    have h1 : (Expression.eval env (v[k.val]'h)).val < Cv := hv ⟨k.val, h⟩
    have h2 : (c[k.val]).val < Cc := hc k
    omega
  · rw [dif_neg h, eval_zero_add]
    rw [show Expression.eval env ((c[k.val] : F p) : Expression (F p)) = c[k.val] from rfl]
    have h2 : (c[k.val]).val < Cc := hc k
    omega

omit [NeZero m] in

lemma polyValue_lVecW {B Cv Cc : ℕ} (env : Environment (F p))
    (v : Vector (Expression (F p)) (2 * m - 1)) (c : Vector (F p) (2 * m))
    (hv : ∀ j : Fin (2 * m - 1), (Expression.eval env v[j.val]).val < Cv)
    (hc : ∀ j : Fin (2 * m), (c[j.val]).val < Cc)
    (hp1 : Cv + Cc < p) :
    polyValue B (Vector.map (Expression.eval env) (lVecW v c))
      = polyValue B (Vector.map (Expression.eval env) v) + polyValue B c := by
  have hcoeff : ∀ (i : ℕ) (h : i < 2 * m),
      ((Vector.map (Expression.eval env) (lVecW v c))[i]'h).val * 2 ^ (B * i)
      = (if hlt : i < 2 * m - 1
          then (Expression.eval env (v[i]'hlt)).val * 2 ^ (B * i) else 0)
        + (c[i]'h).val * 2 ^ (B * i) := by
    intro i h
    rw [Vector.getElem_map]
    simp only [lVecW, Vector.getElem_mapFinRange]
    by_cases hlt : i < 2 * m - 1
    · rw [dif_pos hlt, dif_pos hlt]
      rw [show Expression.eval env (v[i]'hlt + ((c[i]'h : F p) : Expression (F p)))
            = Expression.eval env (v[i]'hlt) + c[i]'h from rfl]
      rw [ZMod.val_add_of_lt (by
        have h1 : (Expression.eval env (v[i]'hlt)).val < Cv := hv ⟨i, hlt⟩
        have h2 : (c[i]'h).val < Cc := hc ⟨i, h⟩
        omega)]
      ring
    · rw [dif_neg hlt, dif_neg hlt, eval_zero_add, zero_add]
      rw [show Expression.eval env ((c[i]'h : F p) : Expression (F p)) = c[i]'h from rfl]
  have hsum : polyValue B (Vector.map (Expression.eval env) (lVecW v c))
      = (∑ i ∈ Finset.range (2 * m),
          (fun j => if hlt : j < 2 * m - 1
            then (Expression.eval env (v[j]'hlt)).val * 2 ^ (B * j) else 0) i)
        + ∑ i ∈ Finset.range (2 * m),
            (fun j => if hj : j < 2 * m then (c[j]'hj).val * 2 ^ (B * j) else 0) i := by
    rw [← Finset.sum_add_distrib]
    apply polyValue_eq_range_sum
    intro i h
    rw [hcoeff i h]
    simp only [dif_pos h]
  rw [hsum]
  congr 1
  · have h1 : polyValue B (Vector.map (Expression.eval env) v)
        = ∑ i ∈ Finset.range (2 * m - 1),
            (fun j => if hlt : j < 2 * m - 1
              then (Expression.eval env (v[j]'hlt)).val * 2 ^ (B * j) else 0) i := by
      apply polyValue_eq_range_sum
      intro i h
      simp only [dif_pos h, Vector.getElem_map]
    rw [h1]
    symm
    apply Finset.sum_subset
    · intro x hx
      rw [Finset.mem_range] at hx ⊢
      omega
    · intro x _ hx
      rw [Finset.mem_range] at hx
      simp only [dif_neg hx]
  · symm
    apply polyValue_eq_range_sum
    intro i h
    simp only [dif_pos h]




def sVecX (q n : Var (BigInt m) (F p)) (xc : Vector (Expression (F p)) (2 * m - 1)) :
    Vector (Expression (F p)) (2 * m - 1) :=
  Vector.mapFinRange (2 * m - 1) fun k =>
    (bigIntMulNoReduce q n)[k.val] + ((3 : F p) : Expression (F p)) * xc[k.val]


lemma coeff_sVecX_fine {B : ℕ} (h3 : 3 < p) (env : Environment (F p))
    (q n : Var (BigInt m) (F p)) (xc : Vector (Expression (F p)) (2 * m - 1))
    (k : Fin (2 * m - 1))
    (hq : ∀ i : Fin m, (Expression.eval env q[i.val]).val < 2 ^ B)
    (hn : ∀ i : Fin m, (Expression.eval env n[i.val]).val < 2 ^ B)
    (hxc : ∀ j : Fin (2 * m - 1),
      (Expression.eval env xc[j.val]).val < m * 2 ^ (2 * B))
    (hfield : m * (2 ^ B * 2 ^ B) < p)
    (hfield3 : 3 * (m * 2 ^ (2 * B)) < p) :
    (Expression.eval env ((sVecX q n xc)[k.val])).val
      < m * 2 ^ (2 * B) + 3 * (m * 2 ^ (2 * B)) := by
  have h2B : 2 ^ B * 2 ^ B = 2 ^ (2 * B) := by rw [two_mul, pow_add]
  have hconv := val_coeff_lt_gen env q n k hq hn hfield
  rw [h2B] at hconv
  simp only [sVecX, Vector.getElem_mapFinRange]
  have hadd : (Expression.eval env ((bigIntMulNoReduce q n)[k.val]
        + ((3 : F p) : Expression (F p)) * xc[k.val])).val
      ≤ (Expression.eval env ((bigIntMulNoReduce q n)[k.val])).val
        + (Expression.eval env (((3 : F p) : Expression (F p)) * xc[k.val])).val := by
    rw [show Expression.eval env ((bigIntMulNoReduce q n)[k.val]
          + ((3 : F p) : Expression (F p)) * xc[k.val])
          = Expression.eval env ((bigIntMulNoReduce q n)[k.val])
            + Expression.eval env (((3 : F p) : Expression (F p)) * xc[k.val]) from rfl]
    exact ZMod.val_add_le _ _
  have h3x : (Expression.eval env (((3 : F p) : Expression (F p)) * xc[k.val])).val
      = 3 * (Expression.eval env xc[k.val]).val := by
    rw [eval_three_mul]
    exact val_three_mul h3 _ (by
      have hx : (Expression.eval env xc[k.val]).val < m * 2 ^ (2 * B) := hxc k
      omega)
  have hx : (Expression.eval env xc[k.val]).val < m * 2 ^ (2 * B) := hxc k
  omega


lemma polyValue_sVecX {B : ℕ} (h3 : 3 < p) (env : Environment (F p))
    (q n : Var (BigInt m) (F p)) (xc : Vector (Expression (F p)) (2 * m - 1))
    (hq : ∀ i : Fin m, (Expression.eval env q[i.val]).val < 2 ^ B)
    (hn : ∀ i : Fin m, (Expression.eval env n[i.val]).val < 2 ^ B)
    (hxc : ∀ j : Fin (2 * m - 1),
      (Expression.eval env xc[j.val]).val < m * 2 ^ (2 * B))
    (hfield : m * (2 ^ B * 2 ^ B) < p)
    (hp4 : 4 * (m * 2 ^ (2 * B)) < p) :
    polyValue B (Vector.map (Expression.eval env) (sVecX q n xc))
      = polyValue B (Vector.map (Expression.eval env) (bigIntMulNoReduce q n))
        + 3 * polyValue B (Vector.map (Expression.eval env) xc) := by
  have h2B : 2 ^ B * 2 ^ B = 2 ^ (2 * B) := by rw [two_mul, pow_add]
  have hS : polyValue B (Vector.map (Expression.eval env) (sVecX q n xc))
      = ∑ i ∈ Finset.range (2 * m - 1),
          (fun j => if hj : j < 2 * m - 1
            then ((Expression.eval env ((bigIntMulNoReduce q n)[j]'hj)).val
                + 3 * (Expression.eval env (xc[j]'hj)).val) * 2 ^ (B * j)
            else 0) i := by
    apply polyValue_eq_range_sum
    intro i h
    rw [Vector.getElem_map]
    simp only [sVecX, Vector.getElem_mapFinRange, dif_pos h]
    have hconv : (Expression.eval env ((bigIntMulNoReduce q n)[i]'h)).val
        < m * 2 ^ (2 * B) := by
      have hh := val_coeff_lt_gen env q n ⟨i, h⟩ hq hn hfield
      rw [h2B] at hh
      exact hh
    have h3x : (Expression.eval env (((3 : F p) : Expression (F p)) * (xc[i]'h))).val
        = 3 * (Expression.eval env (xc[i]'h)).val := by
      rw [eval_three_mul]
      exact val_three_mul h3 _ (by
        have hx : (Expression.eval env (xc[i]'h)).val < m * 2 ^ (2 * B) := hxc ⟨i, h⟩
        omega)
    rw [show Expression.eval env ((bigIntMulNoReduce q n)[i]'h
          + ((3 : F p) : Expression (F p)) * (xc[i]'h))
          = Expression.eval env ((bigIntMulNoReduce q n)[i]'h)
            + Expression.eval env (((3 : F p) : Expression (F p)) * (xc[i]'h)) from rfl]
    rw [ZMod.val_add_of_lt (by
      have hx : (Expression.eval env (xc[i]'h)).val < m * 2 ^ (2 * B) := hxc ⟨i, h⟩
      rw [h3x]
      omega)]
    rw [h3x]
  have hQ : polyValue B (Vector.map (Expression.eval env) (bigIntMulNoReduce q n))
      = ∑ i ∈ Finset.range (2 * m - 1),
          (fun j => if hj : j < 2 * m - 1
            then (Expression.eval env ((bigIntMulNoReduce q n)[j]'hj)).val * 2 ^ (B * j)
            else 0) i := by
    apply polyValue_eq_range_sum
    intro i h
    simp only [dif_pos h, Vector.getElem_map]
  have hX : polyValue B (Vector.map (Expression.eval env) xc)
      = ∑ i ∈ Finset.range (2 * m - 1),
          (fun j => if hj : j < 2 * m - 1
            then (Expression.eval env (xc[j]'hj)).val * 2 ^ (B * j)
            else 0) i := by
    apply polyValue_eq_range_sum
    intro i h
    simp only [dif_pos h, Vector.getElem_map]
  rw [hS, hQ, hX, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  simp only [dif_pos hi]
  ring



omit [NeZero m] in

lemma coeff_sVecTD_bound8 {B Cb : ℕ} (env : Environment (F p))
    (base : Vector (Expression (F p)) (2 * m - 1)) (qh : Expression (F p))
    (n : Var (BigInt m) (F p)) (k : Fin (2 * m))
    (hCb : 0 < Cb)
    (hbase : ∀ j : Fin (2 * m - 1), (Expression.eval env base[j.val]).val < Cb)
    (hqh : (Expression.eval env qh).val < 8)
    (hn : ∀ i : Fin m, (Expression.eval env n[i.val]).val < 2 ^ B) :
    (Expression.eval env ((sVecTD base qh n)[k.val])).val < Cb + 8 * 2 ^ B := by
  have hpos : (0:ℕ) < 2 ^ B := Nat.two_pow_pos B
  have hflank : ∀ (hm' : m ≤ k.val ∧ k.val - m < m),
      (Expression.eval env (qh * n[k.val - m]'hm'.2)).val < 8 * 2 ^ B := by
    intro hm'
    rw [show Expression.eval env (qh * n[k.val - m]'hm'.2)
          = Expression.eval env qh * Expression.eval env (n[k.val - m]'hm'.2) from rfl]
    have hmul := ZMod.val_mul (Expression.eval env qh)
      (Expression.eval env (n[k.val - m]'hm'.2))
    have hle := Nat.mod_le ((Expression.eval env qh).val
      * (Expression.eval env (n[k.val - m]'hm'.2)).val) p
    have hz : (Expression.eval env (n[k.val - m]'hm'.2)).val < 2 ^ B := hn ⟨k.val - m, hm'.2⟩
    have hprod : (Expression.eval env qh).val
        * (Expression.eval env (n[k.val - m]'hm'.2)).val < 8 * 2 ^ B :=
      Nat.mul_lt_mul'' hqh hz
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


lemma polyValue_sVecTD8 {B Cb : ℕ} (env : Environment (F p))
    (base : Vector (Expression (F p)) (2 * m - 1)) (qh : Expression (F p))
    (n : Var (BigInt m) (F p))
    (hCb : 0 < Cb)
    (hbase : ∀ j : Fin (2 * m - 1), (Expression.eval env base[j.val]).val < Cb)
    (hqh : (Expression.eval env qh).val < 8)
    (hn : ∀ i : Fin m, (Expression.eval env n[i.val]).val < 2 ^ B)
    (hp1 : Cb + 8 * 2 ^ B < p) :
    polyValue B (Vector.map (Expression.eval env) (sVecTD base qh n))
      = polyValue B (Vector.map (Expression.eval env) base)
        + (Expression.eval env qh).val * 2 ^ (B * m)
            * BigInt.value B (Vector.map (Expression.eval env) n) := by
  have hm : 0 < m := Nat.pos_of_neZero m
  have hpos : (0:ℕ) < 2 ^ B := Nat.two_pow_pos B
  have hflankv : ∀ (i : ℕ) (hm' : m ≤ i ∧ i - m < m),
      (Expression.eval env (qh * n[i - m]'hm'.2)).val
        = (Expression.eval env qh).val * (Expression.eval env (n[i - m]'hm'.2)).val := by
    intro i hm'
    rw [show Expression.eval env (qh * n[i - m]'hm'.2)
          = Expression.eval env qh * Expression.eval env (n[i - m]'hm'.2) from rfl]
    have hz : (Expression.eval env (n[i - m]'hm'.2)).val < 2 ^ B := hn ⟨i - m, hm'.2⟩
    have hprod : (Expression.eval env qh).val
        * (Expression.eval env (n[i - m]'hm'.2)).val < 8 * 2 ^ B :=
      Nat.mul_lt_mul'' hqh hz
    rw [ZMod.val_mul, Nat.mod_eq_of_lt (by omega)]
  have hflank_lt : ∀ (i : ℕ) (hm' : m ≤ i ∧ i - m < m),
      (Expression.eval env (qh * n[i - m]'hm'.2)).val < 8 * 2 ^ B := by
    intro i hm'
    rw [hflankv i hm']
    exact Nat.mul_lt_mul'' hqh (hn ⟨i - m, hm'.2⟩)
  have hcoeff : ∀ (i : ℕ) (h : i < 2 * m),
      ((Vector.map (Expression.eval env) (sVecTD base qh n))[i]'h).val * 2 ^ (B * i)
      = (if hlt : i < 2 * m - 1
          then (Expression.eval env (base[i]'hlt)).val * 2 ^ (B * i) else 0)
        + (if hm' : m ≤ i ∧ i - m < m
           then (Expression.eval env qh).val
                  * (Expression.eval env (n[i - m]'hm'.2)).val * 2 ^ (B * i)
           else 0) := by
    intro i h
    rw [Vector.getElem_map]
    simp only [sVecTD, Vector.getElem_mapFinRange]
    by_cases hlt : i < 2 * m - 1
    · rw [dif_pos hlt, dif_pos hlt]
      by_cases hm' : m ≤ i ∧ i - m < m
      · rw [dif_pos hm', dif_pos hm']
        rw [show Expression.eval env (base[i]'hlt + qh * n[i - m]'hm'.2)
              = Expression.eval env (base[i]'hlt)
                + Expression.eval env (qh * n[i - m]'hm'.2) from rfl]
        rw [ZMod.val_add_of_lt (by
          have h1 : (Expression.eval env (base[i]'hlt)).val < Cb := hbase ⟨i, hlt⟩
          have h2 := hflank_lt i hm'
          omega)]
        rw [add_mul, hflankv i hm']
      · rw [dif_neg hm', dif_neg hm', eval_add_zero, add_zero]
    · rw [dif_neg hlt, dif_neg hlt]
      by_cases hm' : m ≤ i ∧ i - m < m
      · rw [dif_pos hm', dif_pos hm', eval_zero_add]
        rw [hflankv i hm', zero_add]
      · rw [dif_neg hm', dif_neg hm', eval_add_zero]
        rw [show Expression.eval env (0 : Expression (F p)) = 0 from rfl, ZMod.val_zero,
          zero_mul, zero_add]
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



omit [Fact p.Prime] [NeZero m] in

lemma congruence_of_offset_eqW {a b qlo qh n t B m' : ℕ}
    (heq : a * b + 3 * (n * n) = (qlo + qh * 2 ^ (B * m')) * n + t) :
    t % n = a * b % n := by
  have h2 : t + (qlo + qh * 2 ^ (B * m')) * n = a * b + 3 * (n * n) := by omega
  have h3 : (t + (qlo + qh * 2 ^ (B * m')) * n) % n = (a * b + 3 * (n * n)) % n := by rw [h2]
  rw [show a * b + 3 * (n * n) = a * b + (3 * n) * n from by ring] at h3
  simpa only [Nat.add_mul_mod_self_right] using h3



set_option maxHeartbeats 1600000 in

lemma soundness_core_wx {B : ℕ} (hB3 : 3 ≤ B)
    (hp : 2 ^ (2 * B) * (4 * m + 1) * 8 < p)
    (i₀ : ℕ) (env : Environment (F p))
    (a b n x : Var (BigInt m) (F p))
    (c : Vector (F p) (2 * m))
    (Pv Xv : Vector (Expression (F p)) (2 * m - 1))
    (qh : Expression (F p))
    (av bv nv xv : BigInt m (F p))
    (ha_input : Vector.map (Expression.eval env) a = av)
    (hb_input : Vector.map (Expression.eval env) b = bv)
    (hn_input : Vector.map (Expression.eval env) n = nv)
    (hx_input : Vector.map (Expression.eval env) x = xv)
    (ha_norm : BigInt.Normalized B av)
    (hb_limb : ∀ i : Fin m, (bv[i.val]).val < 2 * 2 ^ B)
    (hn_norm : BigInt.Normalized B nv)
    (hx_norm : BigInt.Normalized B xv)
    (hc_limb : ∀ j : Fin (2 * m), (c[j.val]).val < 4 * 2 ^ B)
    (hc_val : polyValue B c = 3 * (BigInt.value B nv * BigInt.value B nv))
    (hq_norm : BigInt.Normalized B (Vector.map (Expression.eval env)
        (Vector.mapRange m fun i ↦ var { index := i₀ + i })))
    (hqh_lt : (Expression.eval env qh).val < 8)
    (heqAB_get : ∀ k : Fin (2 * m - 1),
      Expression.eval env Pv[k.val] = Expression.eval env (bigIntMulNoReduce a b)[k.val])
    (heqXX_get : ∀ k : Fin (2 * m - 1),
      Expression.eval env Xv[k.val] = Expression.eval env (bigIntMulNoReduce x x)[k.val])
    (h_eq_impl :
      ((∀ k : Fin (2 * m),
          (Expression.eval env ((lVecW Pv c)[k.val])).val
            < 2 * ((m + 1) * 2 ^ (2 * B))) ∧
        ∀ k : Fin (2 * m),
          (Expression.eval env
            ((sVecTD (sVecX (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n Xv)
              qh n)[k.val])).val
            < (4 * m + 1) * 2 ^ (2 * B)) →
        polyValue B (Vector.map (Expression.eval env) (lVecW Pv c)) =
          polyValue B (Vector.map (Expression.eval env)
            (sVecTD (sVecX (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n Xv)
              qh n))) :
    (3 * (BigInt.value B xv * BigInt.value B xv)) % BigInt.value B nv
      = BigInt.value B av * BigInt.value B bv % BigInt.value B nv := by
  set qVar := (Vector.mapRange m fun i ↦ var (F := F p) { index := i₀ + i }) with hqVar
  have hm : 0 < m := Nat.pos_of_neZero m
  have hB2 : 2 ≤ B := by omega
  have h2B : 2 ^ B * 2 ^ B = 2 ^ (2 * B) := by rw [two_mul, pow_add]
  have h64 : (64 : ℕ) ≤ 2 ^ (2 * B) := by
    calc (64 : ℕ) = 2 ^ 6 := by norm_num
      _ ≤ 2 ^ (2 * B) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hbig : 2 ^ (2 * B) * (4 * m + 1) * 8 ≥ 40 * 2 ^ (2 * B) := by nlinarith
  have h3p : 3 < p := by omega
  have h4B : 4 * 2 ^ B ≤ 2 ^ (2 * B) := by
    have h4 : (4 : ℕ) ≤ 2 ^ B := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ B := Nat.pow_le_pow_right (by norm_num) hB2
    calc 4 * 2 ^ B ≤ 2 ^ B * 2 ^ B := Nat.mul_le_mul_right _ h4
      _ = 2 ^ (2 * B) := h2B
  have h8B : 8 * 2 ^ B ≤ 2 ^ (2 * B) := by
    have h8 : (8 : ℕ) ≤ 2 ^ B := by
      calc (8 : ℕ) = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ B := Nat.pow_le_pow_right (by norm_num) hB3
    calc 8 * 2 ^ B ≤ 2 ^ B * 2 ^ B := Nat.mul_le_mul_right _ h8
      _ = 2 ^ (2 * B) := h2B
  -- digit bounds
  have ha_lt : ∀ i : Fin m, (Expression.eval env a[i.val]).val < 2 ^ B := by
    intro i; rw [show Expression.eval env a[i.val] = av[i.val] from by
      rw [← ha_input]; simp only [Vector.getElem_map]]; exact ha_norm i
  have hb_lt : ∀ i : Fin m, (Expression.eval env b[i.val]).val < 2 * 2 ^ B := by
    intro i; rw [show Expression.eval env b[i.val] = bv[i.val] from by
      rw [← hb_input]; simp only [Vector.getElem_map]]; exact hb_limb i
  have hn_lt : ∀ i : Fin m, (Expression.eval env n[i.val]).val < 2 ^ B := by
    intro i; rw [show Expression.eval env n[i.val] = nv[i.val] from by
      rw [← hn_input]; simp only [Vector.getElem_map]]; exact hn_norm i
  have hx_lt : ∀ i : Fin m, (Expression.eval env x[i.val]).val < 2 ^ B := by
    intro i; rw [show Expression.eval env x[i.val] = xv[i.val] from by
      rw [← hx_input]; simp only [Vector.getElem_map]]; exact hx_norm i
  have hqd_lt : ∀ i : Fin m, (Expression.eval env qVar[i.val]).val < 2 ^ B := by
    intro i; have := hq_norm i
    rwa [Fin.getElem_fin, Vector.getElem_map] at this
  -- field bounds
  have hfield : m * (2 ^ B * 2 ^ B) < p := by
    rw [h2B]
    nlinarith [Nat.two_pow_pos (2 * B)]
  have hfield2 : m * (2 ^ B * (2 * 2 ^ B)) < p := by
    have h1 : m * (2 ^ B * (2 * 2 ^ B)) = 2 * (m * 2 ^ (2 * B)) := by
      rw [two_mul B, pow_add]; ring
    rw [h1]
    nlinarith [Nat.two_pow_pos (2 * B)]
  have hfield3 : 3 * (m * 2 ^ (2 * B)) < p := by
    nlinarith [Nat.two_pow_pos (2 * B)]
  have hp4 : 4 * (m * 2 ^ (2 * B)) < p := by
    nlinarith [Nat.two_pow_pos (2 * B)]
  -- Xv coefficient bound (via the x·x bridge)
  have hXv_bound : ∀ j : Fin (2 * m - 1),
      (Expression.eval env Xv[j.val]).val < m * 2 ^ (2 * B) := by
    intro j
    rw [heqXX_get j]
    have hh := val_coeff_lt_gen env x x j hx_lt hx_lt hfield
    rw [h2B] at hh
    exact hh
  -- Pv coefficient bound (via the a·b bridge)
  have hPv_fine : ∀ j : Fin (2 * m - 1),
      (Expression.eval env Pv[j.val]).val < 2 * (m * 2 ^ (2 * B)) := by
    intro j
    rw [heqAB_get j]
    have hh := val_coeff_lt_gen env a b j ha_lt hb_lt hfield2
    have hx2 : m * (2 ^ B * (2 * 2 ^ B)) = 2 * (m * 2 ^ (2 * B)) := by
      rw [two_mul B, pow_add]; ring
    rw [hx2] at hh
    exact hh
  -- sVecX fine bound
  have hS_fine : ∀ j : Fin (2 * m - 1),
      (Expression.eval env ((sVecX qVar n Xv)[j.val])).val
        < m * 2 ^ (2 * B) + 3 * (m * 2 ^ (2 * B)) :=
    fun j => coeff_sVecX_fine h3p env qVar n Xv j hqd_lt hn_lt hXv_bound hfield hfield3
  -- discharge the grouped-equality obligations
  have h_polyeq := h_eq_impl ⟨fun k => by
      have hcap := coeff_lVecW_bound (Cv := 2 * (m * 2 ^ (2 * B))) (Cc := 4 * 2 ^ B)
        env Pv c k (by positivity) hPv_fine hc_limb
      have hexp : 2 * ((m + 1) * 2 ^ (2 * B))
          = 2 * (m * 2 ^ (2 * B)) + 2 * 2 ^ (2 * B) := by ring
      omega,
    fun k => by
      have hcap := coeff_sVecTD_bound8 (Cb := m * 2 ^ (2 * B) + 3 * (m * 2 ^ (2 * B)))
        env (sVecX qVar n Xv) qh n k (by positivity) hS_fine hqh_lt hn_lt
      have hexp : (4 * m + 1) * 2 ^ (2 * B)
          = m * 2 ^ (2 * B) + 3 * (m * 2 ^ (2 * B)) + 2 ^ (2 * B) := by ring
      omega⟩
  -- split both sides
  rw [polyValue_lVecW (Cv := 2 * (m * 2 ^ (2 * B))) (Cc := 4 * 2 ^ B)
    env Pv c hPv_fine hc_limb (by nlinarith [Nat.two_pow_pos (2 * B)])] at h_polyeq
  rw [polyValue_sVecTD8 (Cb := m * 2 ^ (2 * B) + 3 * (m * 2 ^ (2 * B)))
    env (sVecX qVar n Xv) qh n (by positivity) hS_fine hqh_lt hn_lt
    (by nlinarith [Nat.two_pow_pos (2 * B)])] at h_polyeq
  rw [polyValue_sVecX h3p env qVar n Xv hqd_lt hn_lt hXv_bound hfield hp4] at h_polyeq
  -- identify the four convolution values
  have hPv_map : Vector.map (Expression.eval env) Pv
      = Vector.map (Expression.eval env) (bigIntMulNoReduce a b) := by
    apply Vector.ext; intro k hk
    rw [Vector.getElem_map, Vector.getElem_map]
    exact heqAB_get ⟨k, hk⟩
  have hXv_map : Vector.map (Expression.eval env) Xv
      = Vector.map (Expression.eval env) (bigIntMulNoReduce x x) := by
    apply Vector.ext; intro k hk
    rw [Vector.getElem_map, Vector.getElem_map]
    exact heqXX_get ⟨k, hk⟩
  have hP : polyValue B (Vector.map (Expression.eval env) (bigIntMulNoReduce a b))
      = BigInt.value B av * BigInt.value B bv := by
    rw [polyValue_mul_eq_gen env a b ha_lt hb_lt hfield2, ha_input, hb_input]
  have hX : polyValue B (Vector.map (Expression.eval env) (bigIntMulNoReduce x x))
      = BigInt.value B xv * BigInt.value B xv := by
    rw [polyValue_mul_eq_gen env x x hx_lt hx_lt hfield, hx_input]
  have hSqn : polyValue B (Vector.map (Expression.eval env) (bigIntMulNoReduce qVar n))
      = BigInt.value B (Vector.map (Expression.eval env) qVar) * BigInt.value B nv := by
    rw [polyValue_Sqn_eq env qVar n hqd_lt hn_lt hfield, ← hn_input]
  rw [hPv_map, hP, hc_val, hSqn, hXv_map, hX, hn_input] at h_polyeq
  -- assemble the wide-target integer identity
  set qlo := BigInt.value B (Vector.map (Expression.eval env) qVar) with hqlo
  set qhv := (Expression.eval env qh).val with hqhv
  have heq : BigInt.value B av * BigInt.value B bv
        + 3 * (BigInt.value B nv * BigInt.value B nv)
      = (qlo + qhv * 2 ^ (B * m)) * BigInt.value B nv
        + 3 * (BigInt.value B xv * BigInt.value B xv) := by
    have hring : (qlo + qhv * 2 ^ (B * m)) * BigInt.value B nv
        = qlo * BigInt.value B nv + qhv * 2 ^ (B * m) * BigInt.value B nv := by ring
    omega
  exact congruence_of_offset_eqW heq

omit [Fact p.Prime] [NeZero m] in

private lemma bits_of_lt_eight : ∀ q : ℕ, q < 8 →
    q = q % 2 + 2 * (q / 2 % 2) + 4 * (q / 4 % 2)
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | 7, _ => rfl
  | n + 8, h => absurd h (by omega)



set_option maxHeartbeats 1600000 in

lemma completeness_core_wx {B : ℕ} (hB : 2 ^ B < p) (hB3 : 3 ≤ B)
    (hp : 2 ^ (2 * B) * (4 * m + 1) * 8 < p)
    (i₀ : ℕ) (env : Environment (F p))
    (a b n x : Var (BigInt m) (F p))
    (c : Vector (F p) (2 * m))
    (Pv Xv : Vector (Expression (F p)) (2 * m - 1))
    (av bv nv xv : BigInt m (F p))
    (ha_input : Vector.map (Expression.eval env) a = av)
    (hb_input : Vector.map (Expression.eval env) b = bv)
    (hn_input : Vector.map (Expression.eval env) n = nv)
    (hx_input : Vector.map (Expression.eval env) x = xv)
    (ha_norm : BigInt.Normalized B av)
    (hb_limb : ∀ i : Fin m, (bv[i.val]).val < 2 * 2 ^ B)
    (hn_norm : BigInt.Normalized B nv)
    (hx_norm : BigInt.Normalized B xv)
    (hc_limb : ∀ j : Fin (2 * m), (c[j.val]).val < 4 * 2 ^ B)
    (hc_val : polyValue B c = 3 * (BigInt.value B nv * BigInt.value B nv))
    (hab_lt : BigInt.value B av < BigInt.value B nv)
    (hbb_lt : BigInt.value B bv < 2 * BigInt.value B nv)
    (hxx_lt : BigInt.value B xv < BigInt.value B nv)
    (hn_pos : 0 < BigInt.value B nv)
    (hn8D : 5 * BigInt.value B nv ≤ 2 ^ (B * m + 3))
    (h_spec : (3 * (BigInt.value B xv * BigInt.value B xv)) % BigInt.value B nv
      = BigInt.value B av * BigInt.value B bv % BigInt.value B nv)
    (hqwit : ∀ i : Fin m, env.get (i₀ + i.val)
      = (((BigInt.value B av * BigInt.value B bv
            + 3 * (BigInt.value B nv * BigInt.value B nv)
            - 3 * (BigInt.value B xv * BigInt.value B xv)) / BigInt.value B nv
          % 2 ^ (B * m) / 2 ^ (B * i.val) % 2 ^ B : ℕ) : F p))
    (hqh0wit : env.get (i₀ + m)
      = ((((BigInt.value B av * BigInt.value B bv
            + 3 * (BigInt.value B nv * BigInt.value B nv)
            - 3 * (BigInt.value B xv * BigInt.value B xv)) / BigInt.value B nv
          / 2 ^ (B * m)) % 2 : ℕ) : F p))
    (hqh1wit : env.get (i₀ + m + 1)
      = ((((BigInt.value B av * BigInt.value B bv
            + 3 * (BigInt.value B nv * BigInt.value B nv)
            - 3 * (BigInt.value B xv * BigInt.value B xv)) / BigInt.value B nv
          / 2 ^ (B * m) / 2) % 2 : ℕ) : F p))
    (hqh2wit : env.get (i₀ + m + 2)
      = ((((BigInt.value B av * BigInt.value B bv
            + 3 * (BigInt.value B nv * BigInt.value B nv)
            - 3 * (BigInt.value B xv * BigInt.value B xv)) / BigInt.value B nv
          / 2 ^ (B * m) / 4) % 2 : ℕ) : F p))
    (heqAB_get : ∀ k : Fin (2 * m - 1),
      Expression.eval env Pv[k.val] = Expression.eval env (bigIntMulNoReduce a b)[k.val])
    (heqXX_get : ∀ k : Fin (2 * m - 1),
      Expression.eval env Xv[k.val] = Expression.eval env (bigIntMulNoReduce x x)[k.val]) :
    BigInt.Normalized B (Vector.map (Expression.eval env)
        (Vector.mapRange m fun i ↦ var { index := i₀ + i }))
    ∧ (Expression.eval env (var (F := F p) { index := i₀ + m }) = 0
        ∨ Expression.eval env (var (F := F p) { index := i₀ + m }) = 1)
    ∧ (Expression.eval env (var (F := F p) { index := i₀ + m + 1 }) = 0
        ∨ Expression.eval env (var (F := F p) { index := i₀ + m + 1 }) = 1)
    ∧ (Expression.eval env (var (F := F p) { index := i₀ + m + 2 }) = 0
        ∨ Expression.eval env (var (F := F p) { index := i₀ + m + 2 }) = 1)
    ∧ ((∀ k : Fin (2 * m),
          (Expression.eval env ((lVecW Pv c)[k.val])).val
            < 2 * ((m + 1) * 2 ^ (2 * B))) ∧
        ∀ k : Fin (2 * m),
          (Expression.eval env
            ((sVecTD (sVecX (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n Xv)
              (var (F := F p) { index := i₀ + m }
                + ((2 : F p) : Expression (F p)) * var { index := i₀ + m + 1 }
                + ((4 : F p) : Expression (F p)) * var { index := i₀ + m + 2 })
              n)[k.val])).val
            < (4 * m + 1) * 2 ^ (2 * B))
    ∧ polyValue B (Vector.map (Expression.eval env) (lVecW Pv c)) =
        polyValue B (Vector.map (Expression.eval env)
          (sVecTD (sVecX (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n Xv)
            (var (F := F p) { index := i₀ + m }
              + ((2 : F p) : Expression (F p)) * var { index := i₀ + m + 1 }
              + ((4 : F p) : Expression (F p)) * var { index := i₀ + m + 2 })
            n)) := by
  set qVar := (Vector.mapRange m fun i ↦ var (F := F p) { index := i₀ + i }) with hqVar
  set qhW := (var (F := F p) { index := i₀ + m }
      + ((2 : F p) : Expression (F p)) * var { index := i₀ + m + 1 }
      + ((4 : F p) : Expression (F p)) * var { index := i₀ + m + 2 }) with hqhW
  set aval := BigInt.value B av with ha_def
  set bval := BigInt.value B bv with hb_def
  set nval := BigInt.value B nv with hn_def
  set xval := BigInt.value B xv with hx_def
  set tval := 3 * (xval * xval) with ht_def
  set qval := (aval * bval + 3 * (nval * nval) - tval) / nval with hqval_def
  have hm : 0 < m := Nat.pos_of_neZero m
  have hB2 : 2 ≤ B := by omega
  have h2B : 2 ^ B * 2 ^ B = 2 ^ (2 * B) := by rw [two_mul, pow_add]
  have h64 : (64 : ℕ) ≤ 2 ^ (2 * B) := by
    calc (64 : ℕ) = 2 ^ 6 := by norm_num
      _ ≤ 2 ^ (2 * B) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hbig : 2 ^ (2 * B) * (4 * m + 1) * 8 ≥ 40 * 2 ^ (2 * B) := by nlinarith
  have h3p : 3 < p := by omega
  have h8p : 8 < p := by omega
  -- exact division: a·b + 3n² = q·n + t
  have ht_le : tval ≤ aval * bval + 3 * (nval * nval) := by
    have hxx : xval * xval < nval * nval := Nat.mul_lt_mul'' hxx_lt hxx_lt
    omega
  have hkey : qval * nval + tval = aval * bval + 3 * (nval * nval) := by
    have hR : (aval * bval + 3 * (nval * nval)) % nval = tval % nval := by
      rw [show aval * bval + 3 * (nval * nval) = aval * bval + (3 * nval) * nval from by ring,
        Nat.add_mul_mod_self_right]
      exact h_spec.symm
    have hdvd : nval ∣ (aval * bval + 3 * (nval * nval) - tval) := by
      refine ⟨(aval * bval + 3 * (nval * nval)) / nval - tval / nval, ?_⟩
      have h1 := Nat.div_add_mod (aval * bval + 3 * (nval * nval)) nval
      have h2 := Nat.div_add_mod tval nval
      have hQle : tval / nval ≤ (aval * bval + 3 * (nval * nval)) / nval :=
        Nat.div_le_div_right ht_le
      rw [Nat.mul_sub]
      omega
    have hqmul : qval * nval = aval * bval + 3 * (nval * nval) - tval := by
      rw [hqval_def, Nat.div_mul_cancel hdvd]
    omega
  -- the wide quotient bound: q < 5n ≤ 2^(Bm+3)
  have hqval_lt : qval < 2 ^ (B * m + 3) := by
    have hq_le : qval ≤ (aval * bval + 3 * (nval * nval)) / nval :=
      Nat.div_le_div_right (Nat.sub_le _ _)
    have hq_lt : (aval * bval + 3 * (nval * nval)) / nval < 5 * nval := by
      apply Nat.div_lt_of_lt_mul
      have hab : aval * bval < nval * (2 * nval) := by
        rcases Nat.eq_zero_or_pos bval with hb0 | hb0
        · rw [hb0, Nat.mul_zero]; positivity
        · calc aval * bval < nval * bval := by
                apply (Nat.mul_lt_mul_right hb0).mpr hab_lt
            _ ≤ nval * (2 * nval) := by apply Nat.mul_le_mul_left; omega
      calc aval * bval + 3 * (nval * nval) < nval * (2 * nval) + 3 * (nval * nval) := by omega
        _ = nval * (5 * nval) := by ring
    omega
  -- decompose q = q_lo + qh·2^(Bm), qh ≤ 7
  set qlo := qval % 2 ^ (B * m) with hqlo_def
  set qhn := qval / 2 ^ (B * m) with hqhn_def
  have hqlo_lt : qlo < 2 ^ (B * m) := Nat.mod_lt _ (Nat.two_pow_pos _)
  have h8pow : 2 ^ (B * m + 3) = 8 * 2 ^ (B * m) := by
    rw [pow_add]; ring
  have hqhn_le : qhn ≤ 7 := by
    rw [hqhn_def]
    by_contra hgt
    push_neg at hgt
    have : 8 * 2 ^ (B * m) ≤ qval := by
      calc 8 * 2 ^ (B * m) ≤ (qval / 2 ^ (B * m)) * 2 ^ (B * m) := by
            apply Nat.mul_le_mul_right; omega
        _ ≤ qval := Nat.div_mul_le_self _ _
    omega
  have hdecomp : qval = qlo + qhn * 2 ^ (B * m) := by
    rw [hqlo_def, hqhn_def, Nat.add_comm, Nat.mul_comm]
    exact (Nat.div_add_mod qval (2 ^ (B * m))).symm
  -- bit split of the top quotient
  have hbits : qhn = qhn % 2 + 2 * (qhn / 2 % 2) + 4 * (qhn / 4 % 2) :=
    bits_of_lt_eight qhn (by omega)
  -- q_lo witness limbs: value and normalization
  have hqwit' : ∀ i : Fin m, env.get (i₀ + i.val)
      = ((qlo / 2 ^ (B * i.val) % 2 ^ B : ℕ) : F p) := by
    intro i; rw [hqwit i]
  have hqv_val : BigInt.value B (Vector.map (Expression.eval env) qVar) = qlo :=
    BigInt.value_mapRange i₀ qlo env hB hqlo_lt (by intro i; rw [hqwit' i])
  have hqv_norm : BigInt.Normalized B (Vector.map (Expression.eval env) qVar) :=
    normalized_mapRange i₀ qlo env hB (by intro i; rw [hqwit' i])
  -- the three bits evaluate to the bit values of qhn
  have hq0_eval : Expression.eval env (var (F := F p) { index := i₀ + m })
      = ((qhn % 2 : ℕ) : F p) := by
    rw [show Expression.eval env (var (F := F p) { index := i₀ + m })
          = env.get (i₀ + m) from rfl, hqh0wit]
  have hq1_eval : Expression.eval env (var (F := F p) { index := i₀ + m + 1 })
      = ((qhn / 2 % 2 : ℕ) : F p) := by
    rw [show Expression.eval env (var (F := F p) { index := i₀ + m + 1 })
          = env.get (i₀ + m + 1) from rfl, hqh1wit]
  have hq2_eval : Expression.eval env (var (F := F p) { index := i₀ + m + 2 })
      = ((qhn / 4 % 2 : ℕ) : F p) := by
    rw [show Expression.eval env (var (F := F p) { index := i₀ + m + 2 })
          = env.get (i₀ + m + 2) from rfl, hqh2wit]
  have hbool : ∀ v : ℕ, v ≤ 1 → ((v : F p) = 0 ∨ (v : F p) = 1) := by
    intro v hv
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hv with h0 | h1
    · left; rw [h0, Nat.cast_zero]
    · right; rw [h1, Nat.cast_one]
  -- the affine top quotient evaluates to qhn
  have hqh_eval : Expression.eval env qhW = ((qhn : ℕ) : F p) := by
    rw [hqhW]
    rw [show Expression.eval env (var (F := F p) { index := i₀ + m }
          + ((2 : F p) : Expression (F p)) * var { index := i₀ + m + 1 }
          + ((4 : F p) : Expression (F p)) * var { index := i₀ + m + 2 })
          = Expression.eval env (var (F := F p) { index := i₀ + m })
            + (2 : F p) * Expression.eval env (var (F := F p) { index := i₀ + m + 1 })
            + (4 : F p) * Expression.eval env (var (F := F p) { index := i₀ + m + 2 })
          from rfl]
    rw [hq0_eval, hq1_eval, hq2_eval]
    rw [show ((qhn : ℕ) : F p)
          = ((qhn % 2 + 2 * (qhn / 2 % 2) + 4 * (qhn / 4 % 2) : ℕ) : F p) from by
        rw [← hbits]]
    push_cast
    ring
  have hqhv_val : (Expression.eval env qhW).val = qhn := by
    rw [hqh_eval]
    exact ZMod.val_natCast_of_lt (by omega)
  have hqh_lt : (Expression.eval env qhW).val < 8 := by
    rw [hqhv_val]; omega
  -- digit bounds
  have ha_lt : ∀ i : Fin m, (Expression.eval env a[i.val]).val < 2 ^ B := by
    intro i; rw [show Expression.eval env a[i.val] = av[i.val] from by
      rw [← ha_input]; simp only [Vector.getElem_map]]; exact ha_norm i
  have hb_lt : ∀ i : Fin m, (Expression.eval env b[i.val]).val < 2 * 2 ^ B := by
    intro i; rw [show Expression.eval env b[i.val] = bv[i.val] from by
      rw [← hb_input]; simp only [Vector.getElem_map]]; exact hb_limb i
  have hn_lt : ∀ i : Fin m, (Expression.eval env n[i.val]).val < 2 ^ B := by
    intro i; rw [show Expression.eval env n[i.val] = nv[i.val] from by
      rw [← hn_input]; simp only [Vector.getElem_map]]; exact hn_norm i
  have hx_lt : ∀ i : Fin m, (Expression.eval env x[i.val]).val < 2 ^ B := by
    intro i; rw [show Expression.eval env x[i.val] = xv[i.val] from by
      rw [← hx_input]; simp only [Vector.getElem_map]]; exact hx_norm i
  have hqd_lt : ∀ i : Fin m, (Expression.eval env qVar[i.val]).val < 2 ^ B := by
    intro i; have := hqv_norm i
    rwa [Fin.getElem_fin, Vector.getElem_map] at this
  -- field bounds
  have hfield : m * (2 ^ B * 2 ^ B) < p := by
    rw [h2B]
    nlinarith [Nat.two_pow_pos (2 * B)]
  have hfield2 : m * (2 ^ B * (2 * 2 ^ B)) < p := by
    have h1 : m * (2 ^ B * (2 * 2 ^ B)) = 2 * (m * 2 ^ (2 * B)) := by
      rw [two_mul B, pow_add]; ring
    rw [h1]
    nlinarith [Nat.two_pow_pos (2 * B)]
  have hfield3 : 3 * (m * 2 ^ (2 * B)) < p := by
    nlinarith [Nat.two_pow_pos (2 * B)]
  have hp4 : 4 * (m * 2 ^ (2 * B)) < p := by
    nlinarith [Nat.two_pow_pos (2 * B)]
  -- coefficient bounds (as in the soundness core)
  have hXv_bound : ∀ j : Fin (2 * m - 1),
      (Expression.eval env Xv[j.val]).val < m * 2 ^ (2 * B) := by
    intro j
    rw [heqXX_get j]
    have hh := val_coeff_lt_gen env x x j hx_lt hx_lt hfield
    rw [h2B] at hh
    exact hh
  have hPv_fine : ∀ j : Fin (2 * m - 1),
      (Expression.eval env Pv[j.val]).val < 2 * (m * 2 ^ (2 * B)) := by
    intro j
    rw [heqAB_get j]
    have hh := val_coeff_lt_gen env a b j ha_lt hb_lt hfield2
    have hx2 : m * (2 ^ B * (2 * 2 ^ B)) = 2 * (m * 2 ^ (2 * B)) := by
      rw [two_mul B, pow_add]; ring
    rw [hx2] at hh
    exact hh
  have hS_fine : ∀ j : Fin (2 * m - 1),
      (Expression.eval env ((sVecX qVar n Xv)[j.val])).val
        < m * 2 ^ (2 * B) + 3 * (m * 2 ^ (2 * B)) :=
    fun j => coeff_sVecX_fine h3p env qVar n Xv j hqd_lt hn_lt hXv_bound hfield hfield3
  -- the obligations
  have hobl : (∀ k : Fin (2 * m),
      (Expression.eval env ((lVecW Pv c)[k.val])).val
        < 2 * ((m + 1) * 2 ^ (2 * B))) ∧
      ∀ k : Fin (2 * m),
        (Expression.eval env ((sVecTD (sVecX qVar n Xv) qhW n)[k.val])).val
          < (4 * m + 1) * 2 ^ (2 * B) := by
    have h4B : 4 * 2 ^ B ≤ 2 ^ (2 * B) := by
      have h4 : (4 : ℕ) ≤ 2 ^ B := by
        calc (4 : ℕ) = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ B := Nat.pow_le_pow_right (by norm_num) hB2
      calc 4 * 2 ^ B ≤ 2 ^ B * 2 ^ B := Nat.mul_le_mul_right _ h4
        _ = 2 ^ (2 * B) := h2B
    have h8B : 8 * 2 ^ B ≤ 2 ^ (2 * B) := by
      have h8 : (8 : ℕ) ≤ 2 ^ B := by
        calc (8 : ℕ) = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ B := Nat.pow_le_pow_right (by norm_num) hB3
      calc 8 * 2 ^ B ≤ 2 ^ B * 2 ^ B := Nat.mul_le_mul_right _ h8
        _ = 2 ^ (2 * B) := h2B
    refine ⟨fun k => ?_, fun k => ?_⟩
    · have hcap := coeff_lVecW_bound (Cv := 2 * (m * 2 ^ (2 * B))) (Cc := 4 * 2 ^ B)
        env Pv c k (by positivity) hPv_fine hc_limb
      have hexp : 2 * ((m + 1) * 2 ^ (2 * B))
          = 2 * (m * 2 ^ (2 * B)) + 2 * 2 ^ (2 * B) := by ring
      omega
    · have hcap := coeff_sVecTD_bound8 (Cb := m * 2 ^ (2 * B) + 3 * (m * 2 ^ (2 * B)))
        env (sVecX qVar n Xv) qhW n k (by positivity) hS_fine hqh_lt hn_lt
      have hexp : (4 * m + 1) * 2 ^ (2 * B)
          = m * 2 ^ (2 * B) + 3 * (m * 2 ^ (2 * B)) + 2 ^ (2 * B) := by ring
      omega
  -- the value equation
  have hval : polyValue B (Vector.map (Expression.eval env) (lVecW Pv c)) =
      polyValue B (Vector.map (Expression.eval env)
        (sVecTD (sVecX qVar n Xv) qhW n)) := by
    rw [polyValue_lVecW (Cv := 2 * (m * 2 ^ (2 * B))) (Cc := 4 * 2 ^ B)
      env Pv c hPv_fine hc_limb (by nlinarith [Nat.two_pow_pos (2 * B)])]
    rw [polyValue_sVecTD8 (Cb := m * 2 ^ (2 * B) + 3 * (m * 2 ^ (2 * B)))
      env (sVecX qVar n Xv) qhW n (by positivity) hS_fine hqh_lt hn_lt
      (by nlinarith [Nat.two_pow_pos (2 * B)])]
    rw [polyValue_sVecX h3p env qVar n Xv hqd_lt hn_lt hXv_bound hfield hp4]
    have hPv_map : Vector.map (Expression.eval env) Pv
        = Vector.map (Expression.eval env) (bigIntMulNoReduce a b) := by
      apply Vector.ext; intro k hk
      rw [Vector.getElem_map, Vector.getElem_map]
      exact heqAB_get ⟨k, hk⟩
    have hXv_map : Vector.map (Expression.eval env) Xv
        = Vector.map (Expression.eval env) (bigIntMulNoReduce x x) := by
      apply Vector.ext; intro k hk
      rw [Vector.getElem_map, Vector.getElem_map]
      exact heqXX_get ⟨k, hk⟩
    have hP : polyValue B (Vector.map (Expression.eval env) (bigIntMulNoReduce a b))
        = aval * bval := by
      rw [polyValue_mul_eq_gen env a b ha_lt hb_lt hfield2, ha_input, hb_input]
    have hX : polyValue B (Vector.map (Expression.eval env) (bigIntMulNoReduce x x))
        = xval * xval := by
      rw [polyValue_mul_eq_gen env x x hx_lt hx_lt hfield, hx_input]
    have hSqn : polyValue B (Vector.map (Expression.eval env) (bigIntMulNoReduce qVar n))
        = qlo * nval := by
      rw [polyValue_Sqn_eq env qVar n hqd_lt hn_lt hfield, hqv_val, hn_input]
    rw [hPv_map, hP, hc_val, hSqn, hXv_map, hX, hqhv_val, hn_input]
    rw [← hn_def]
    rw [hdecomp] at hkey
    have hring : (qlo + qhn * 2 ^ (B * m)) * nval
        = qlo * nval + qhn * 2 ^ (B * m) * nval := by ring
    omega
  refine ⟨hqv_norm, ?_, ?_, ?_, hobl, hval⟩
  · rw [hq0_eval]; exact hbool _ (by omega)
  · rw [hq1_eval]; exact hbool _ (by omega)
  · rw [hq2_eval]; exact hbool _ (by omega)




lemma val_three_bit_lt (h8p : 8 < p) (e0 e1 e2 : F p)
    (h0 : e0 = 0 ∨ e0 = 1) (h1 : e1 = 0 ∨ e1 = 1) (h2 : e2 = 0 ∨ e2 = 1) :
    (e0 + 2 * e1 + 4 * e2).val < 8 := by
  have hv0 : e0.val ≤ 1 := by
    rcases h0 with h | h
    · rw [h, ZMod.val_zero]; omega
    · rw [h]
      haveI : Fact (1 < p) := ⟨by omega⟩
      rw [ZMod.val_one]
  have hv1 : (2 * e1).val ≤ 2 := by
    rcases h1 with h | h
    · rw [h, mul_zero, ZMod.val_zero]; omega
    · rw [h, mul_one, show ((2 : F p)) = ((2 : ℕ) : F p) from by norm_num,
        ZMod.val_natCast_of_lt (by omega)]
  have hv2 : (4 * e2).val ≤ 4 := by
    rcases h2 with h | h
    · rw [h, mul_zero, ZMod.val_zero]; omega
    · rw [h, mul_one, show ((4 : F p)) = ((4 : ℕ) : F p) from by norm_num,
        ZMod.val_natCast_of_lt (by omega)]
  have hadd1 : (e0 + 2 * e1 + 4 * e2).val ≤ (e0 + 2 * e1).val + (4 * e2).val :=
    ZMod.val_add_le _ _
  have hadd2 : (e0 + 2 * e1).val ≤ e0.val + (2 * e1).val := ZMod.val_add_le _ _
  omega


private def evalValue (B : ℕ) (env : ProverEnvironment (F p))
    (x : Var (BigInt m) (F p)) : ℕ :=
  Solution.Secp256k1ScalarMul.Limbs.fromLimbs B
    ((x.map (Expression.eval env.toEnvironment)).toList.map ZMod.val)


def main (P : BigIntParams p m)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqXV.GVXHyps p (2 * m) P.B gf posOf G V VR)
    (c : Vector (F p) (2 * m))
    [Fact (p > 2)]
    (input : Var (MulModTarget.Inputs m) (F p)) :
    Circuit (F p) Unit :=
  letI : NeZero (2 * m) := ⟨by have := Nat.pos_of_neZero m; omega⟩
  do
  let a := input.a
  let b := input.b
  let n := input.modulus
  let x := input.target

  -- 1. witness q_lo = ((a·b + 3n² − 3x²)/n) % 2^(Bm) as BigInt m
  let q ← ProvableType.witness (α := BigInt m) fun env =>
    let qval : ℕ := (evalValue P.B env a * evalValue P.B env b
        + 3 * (evalValue P.B env n * evalValue P.B env n)
        - 3 * (evalValue P.B env x * evalValue P.B env x)) / evalValue P.B env n
        % 2 ^ (P.B * m)
    Vector.ofFn fun k : Fin m => ((qval / 2 ^ (P.B * k.val) % 2 ^ P.B : ℕ) : F p)

  -- 2. witness the three top-quotient bits
  let qh0 ← ProvableType.witness (α := field) fun env =>
    ((((evalValue P.B env a * evalValue P.B env b
        + 3 * (evalValue P.B env n * evalValue P.B env n)
        - 3 * (evalValue P.B env x * evalValue P.B env x)) / evalValue P.B env n
        / 2 ^ (P.B * m)) % 2 : ℕ) : F p)
  let qh1 ← ProvableType.witness (α := field) fun env =>
    ((((evalValue P.B env a * evalValue P.B env b
        + 3 * (evalValue P.B env n * evalValue P.B env n)
        - 3 * (evalValue P.B env x * evalValue P.B env x)) / evalValue P.B env n
        / 2 ^ (P.B * m) / 2) % 2 : ℕ) : F p)
  let qh2 ← ProvableType.witness (α := field) fun env =>
    ((((evalValue P.B env a * evalValue P.B env b
        + 3 * (evalValue P.B env n * evalValue P.B env n)
        - 3 * (evalValue P.B env x * evalValue P.B env x)) / evalValue P.B env n
        / 2 ^ (P.B * m) / 4) % 2 : ℕ) : F p)

  -- 3. the bits are boolean
  assertZero (qh0 * (qh0 - 1))
  assertZero (qh1 * (qh1 - 1))
  assertZero (qh2 * (qh2 - 1))

  -- 4. normalize q_lo
  Normalize.circuit P q

  -- 5. the two convolutions
  let Pab ← interpolatedMul a b
  let Pxx ← interpolatedMul x x

  -- 6. certify over the L = 2m flanks
  GroupedEqXV.circuit P.B gf posOf G V VR hgv P.hB1
    { lhs := lVecW Pab c,
      rhs := sVecTD (sVecX q n Pxx)
        (qh0 + ((2 : F p) : Expression (F p)) * qh1
          + ((4 : F p) : Expression (F p)) * qh2) n }

instance elaborated (P : BigIntParams p m)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqXV.GVXHyps p (2 * m) P.B gf posOf G V VR)
    (c : Vector (F p) (2 * m))
    [Fact (p > 2)] :
    ElaboratedCircuit (F p) (MulModTarget.Inputs m) unit (main P gf posOf G V VR hgv c) where
  -- q (m) + bits (3) + normalize q (m·B) + two interpolations (2·(2m−1)) + grouped carries
  localLength _ :=
    m + 3 + m * (P.B - 1) + (2 * m - 1) + (2 * m - 1)
      + GroupedEqXV.widthAllocFrom V.Wf (G - 2) 0
  localLength_eq := by
    intro input offset
    simp only [main, interpolatedMul, circuit_norm, Normalize.circuit, Normalize.elaborated,
      Normalize.main, GroupedEqXV.circuit, GroupedEqXV.elaborated,
      RangeCheck.circuit, Gadgets.ToBits.rangeCheck, Circuit.assertZero]
    omega
  subcircuitsConsistent := by
    intro input offset
    simp +arith only [main, interpolatedMul, circuit_norm, Normalize.circuit, Normalize.elaborated,
      Normalize.main, GroupedEqXV.circuit, GroupedEqXV.elaborated,
      RangeCheck.circuit, Gadgets.ToBits.rangeCheck, Circuit.assertZero]
  channelsLawful := by
    intro offset
    simp only [main, interpolatedMul, circuit_norm, Normalize.circuit, Normalize.elaborated,
      Normalize.main, GroupedEqXV.circuit, GroupedEqXV.elaborated,
      RangeCheck.circuit, Gadgets.ToBits.rangeCheck, Circuit.assertZero]


def Assumptions (B : ℕ) (c : Vector (F p) (2 * m))
    (input : MulModTarget.Inputs m (F p)) : Prop :=
  input.a.Normalized B ∧
    input.b.Normalized (B + 1) ∧
    input.modulus.Normalized B ∧
    input.target.Normalized B ∧
    input.a.value B < input.modulus.value B ∧
    input.b.value B < 2 * input.modulus.value B ∧
    input.target.value B < input.modulus.value B ∧
    0 < input.modulus.value B ∧
    5 * input.modulus.value B ≤ 2 ^ (B * m + 3) ∧
    (∀ j : Fin (2 * m), (c[j.val]).val < 4 * 2 ^ B) ∧
    polyValue B c = 3 * (input.modulus.value B * input.modulus.value B)


def Spec (B : ℕ) (input : MulModTarget.Inputs m (F p)) : Prop :=
  (3 * (input.target.value B * input.target.value B)) % input.modulus.value B
    = (input.a.value B * input.b.value B) % input.modulus.value B

set_option maxHeartbeats 3200000 in

def circuit (P : BigIntParams p m)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqXV.GVXHyps p (2 * m) P.B gf posOf G V VR)
    (hNf : ∀ j, V.Nf j = 2 * ((m + 1) * 2 ^ (2 * P.B)))
    (hNfR : ∀ j, VR.Nf j = (4 * m + 1) * 2 ^ (2 * P.B))
    (c : Vector (F p) (2 * m))
    (hB3 : 3 ≤ P.B)
    (hp8 : 2 ^ (2 * P.B) * (4 * m + 1) * 8 < p)
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
      obtain ⟨ha_norm, hb_limb, hn_norm, hx_norm, hab_lt, hbb_lt, hxx_lt, hn_pos,
        hn8D, hc_limb, hc_val⟩ := h_assumptions
      obtain ⟨hqh0_zero, hqh1_zero, hqh2_zero, hq_norm, hAB_ops, hXX_ops, h_eq_impl⟩ := h_holds
      rw [interpolatedMul_localLength] at hXX_ops h_eq_impl ⊢
      simp only [hNf, hNfR] at h_eq_impl
      have h8p : 8 < p := by
        have h64 : (64 : ℕ) ≤ 2 ^ (2 * B) := by
          calc (64 : ℕ) = 2 ^ 6 := by norm_num
            _ ≤ 2 ^ (2 * B) := Nat.pow_le_pow_right (by norm_num) (by omega)
        nlinarith [Nat.pos_of_neZero m]
      have h_pAB := interpolatedMul_soundness (i₀ + (m + 3) + m * (B - 1))
        input_var.a input_var.b env hAB_ops
      have h_pXX := interpolatedMul_soundness (i₀ + (m + 3) + m * (B - 1) + (2 * m - 1))
        input_var.target input_var.target env hXX_ops
      refine ⟨?_, interpolatedMul_requirements _ _ _ _, interpolatedMul_requirements _ _ _ _⟩
      have ha_input : Vector.map (Expression.eval env) input_var.a = input.a := by
        rw [← h_input]
      have hb_input : Vector.map (Expression.eval env) input_var.b = input.b := by
        rw [← h_input]
      have hn_input : Vector.map (Expression.eval env) input_var.modulus = input.modulus := by
        rw [← h_input]
      have hx_input : Vector.map (Expression.eval env) input_var.target = input.target := by
        rw [← h_input]
      have heqAB_get := interpolatedMul_eval_bridge env (i₀ + (m + 3) + m * (B - 1))
        input_var.a input_var.b (two_m_sub_one_lt hp) h_pAB
      have heqXX_get := interpolatedMul_eval_bridge env (i₀ + (m + 3) + m * (B - 1) + (2 * m - 1))
        input_var.target input_var.target (two_m_sub_one_lt hp) h_pXX
      have hbool_of : ∀ k : ℕ,
          env.get k * (env.get k + -1) = 0 →
          env.get k = 0 ∨ env.get k = 1 := by
        intro k hzero
        rcases mul_eq_zero.mp hzero with h0 | h1
        · exact Or.inl h0
        · right
          rw [← sub_eq_add_neg] at h1
          exact sub_eq_zero.mp h1
      have hqh_lt : (Expression.eval env
          (var (F := F p) { index := i₀ + m }
            + ((2 : F p) : Expression (F p)) * var { index := i₀ + m + 1 }
            + ((4 : F p) : Expression (F p)) * var { index := i₀ + m + 2 })).val < 8 := by
        rw [show Expression.eval env
              (var (F := F p) { index := i₀ + m }
                + ((2 : F p) : Expression (F p)) * var { index := i₀ + m + 1 }
                + ((4 : F p) : Expression (F p)) * var { index := i₀ + m + 2 })
              = env.get (i₀ + m) + 2 * env.get (i₀ + m + 1) + 4 * env.get (i₀ + m + 2)
              from rfl]
        exact val_three_bit_lt h8p _ _ _
          (hbool_of _ hqh0_zero) (hbool_of _ hqh1_zero) (hbool_of _ hqh2_zero)
      exact soundness_core_wx (B := B) hB3 hp8 i₀ env
        input_var.a input_var.b input_var.modulus input_var.target c
        (interpolatedMul input_var.a input_var.b (i₀ + (m + 3) + m * (B - 1))).1
        (interpolatedMul input_var.target input_var.target
          (i₀ + (m + 3) + m * (B - 1) + (2 * m - 1))).1
        (var { index := i₀ + m }
          + ((2 : F p) : Expression (F p)) * var { index := i₀ + m + 1 }
          + ((4 : F p) : Expression (F p)) * var { index := i₀ + m + 2 })
        input.a input.b input.modulus input.target
        ha_input hb_input hn_input hx_input
        ha_norm (fun i => by have h := hb_limb i; rw [Fin.getElem_fin, pow_succ] at h; omega)
        hn_norm hx_norm hc_limb hc_val hq_norm hqh_lt
        heqAB_get heqXX_get h_eq_impl
    completeness := by
      obtain ⟨B, W, hB, hW, hB1, hWB, hWp, hp⟩ := P
      circuit_proof_start [Normalize.circuit, Normalize.elaborated, Normalize.main,
        Normalize.Assumptions, Normalize.Spec,
        GroupedEqXV.circuit, GroupedEqXV.elaborated,
        GroupedEqXV.Assumptions, GroupedEqX.Spec]
      obtain ⟨ha_norm, hb_limb, hn_norm, hx_norm, hab_lt, hbb_lt, hxx_lt, hn_pos,
        hn8D, hc_limb, hc_val⟩ := h_assumptions
      obtain ⟨hq_env, hqh0_env, hqh1_env, hqh2_env, hAB_uses, hXX_uses⟩ := h_env
      rw [interpolatedMul_localLength] at hXX_uses ⊢
      have h_pvAB := interpolatedMul_usesLocalWitnesses (i₀ + (m + 3) + m * (B - 1))
        (i₀ + (m + 3) + m * (B - 1)) input_var.a input_var.b env rfl hAB_uses
      have h_pvXX := interpolatedMul_usesLocalWitnesses
        (i₀ + (m + 3) + m * (B - 1) + (2 * m - 1)) (2 * m - 1 + (i₀ + m + 1 + 1 + 1 + m * (B - 1)))
        input_var.target input_var.target env (by omega) hXX_uses
      have ha_input : Vector.map (Expression.eval env.toEnvironment) input_var.a = input.a := by
        rw [← h_input]
      have hb_input : Vector.map (Expression.eval env.toEnvironment) input_var.b = input.b := by
        rw [← h_input]
      have hn_input : Vector.map (Expression.eval env.toEnvironment) input_var.modulus
          = input.modulus := by
        rw [← h_input]
      have hx_input : Vector.map (Expression.eval env.toEnvironment) input_var.target
          = input.target := by
        rw [← h_input]
      have heva : evalValue B env input_var.a = BigInt.value B input.a := by
        rw [evalValue, BigInt.value, ← ha_input]
      have hevb : evalValue B env input_var.b = BigInt.value B input.b := by
        rw [evalValue, BigInt.value, ← hb_input]
      have hevn : evalValue B env input_var.modulus = BigInt.value B input.modulus := by
        rw [evalValue, BigInt.value, ← hn_input]
      have hevx : evalValue B env input_var.target = BigInt.value B input.target := by
        rw [evalValue, BigInt.value, ← hx_input]
      have hqwit : ∀ i : Fin m, env.toEnvironment.get (i₀ + i.val)
          = (((BigInt.value B input.a * BigInt.value B input.b
                + 3 * (BigInt.value B input.modulus * BigInt.value B input.modulus)
                - 3 * (BigInt.value B input.target * BigInt.value B input.target))
              / BigInt.value B input.modulus % 2 ^ (B * m)
              / 2 ^ (B * i.val) % 2 ^ B : ℕ) : F p) := by
        intro i; rw [hq_env i, Vector.getElem_ofFn, heva, hevb, hevn, hevx]
      have hqh0wit : env.toEnvironment.get (i₀ + m)
          = ((((BigInt.value B input.a * BigInt.value B input.b
                + 3 * (BigInt.value B input.modulus * BigInt.value B input.modulus)
                - 3 * (BigInt.value B input.target * BigInt.value B input.target))
              / BigInt.value B input.modulus / 2 ^ (B * m)) % 2 : ℕ) : F p) := by
        rw [hqh0_env, heva, hevb, hevn, hevx]
      have hqh1wit : env.toEnvironment.get (i₀ + m + 1)
          = ((((BigInt.value B input.a * BigInt.value B input.b
                + 3 * (BigInt.value B input.modulus * BigInt.value B input.modulus)
                - 3 * (BigInt.value B input.target * BigInt.value B input.target))
              / BigInt.value B input.modulus / 2 ^ (B * m) / 2) % 2 : ℕ) : F p) := by
        rw [hqh1_env, heva, hevb, hevn, hevx]
      have hqh2wit : env.toEnvironment.get (i₀ + m + 2)
          = ((((BigInt.value B input.a * BigInt.value B input.b
                + 3 * (BigInt.value B input.modulus * BigInt.value B input.modulus)
                - 3 * (BigInt.value B input.target * BigInt.value B input.target))
              / BigInt.value B input.modulus / 2 ^ (B * m) / 4) % 2 : ℕ) : F p) := by
        rw [hqh2_env, heva, hevb, hevn, hevx]
      have heqAB_get := interpolatedMul_eval_bridge_uses env.toEnvironment
        (i₀ + (m + 3) + m * (B - 1)) input_var.a input_var.b h_pvAB
      have heqXX_get := interpolatedMul_eval_bridge_uses env.toEnvironment
        (i₀ + (m + 3) + m * (B - 1) + (2 * m - 1)) input_var.target input_var.target h_pvXX
      have core := completeness_core_wx (B := B) hB hB3 hp8 i₀ env.toEnvironment
        input_var.a input_var.b input_var.modulus input_var.target c
        (interpolatedMul input_var.a input_var.b (i₀ + (m + 3) + m * (B - 1))).1
        (interpolatedMul input_var.target input_var.target
          (i₀ + (m + 3) + m * (B - 1) + (2 * m - 1))).1
        input.a input.b input.modulus input.target
        ha_input hb_input hn_input hx_input
        ha_norm (fun i => by have h := hb_limb i; rw [Fin.getElem_fin, pow_succ] at h; omega)
        hn_norm hx_norm hc_limb hc_val
        hab_lt hbb_lt hxx_lt hn_pos hn8D h_spec
        hqwit hqh0wit hqh1wit hqh2wit heqAB_get heqXX_get
      simp only [hNf, hNfR]
      have hzero_of_bool : ∀ k : ℕ,
          (Expression.eval env.toEnvironment (var (F := F p) { index := k }) = 0
            ∨ Expression.eval env.toEnvironment (var (F := F p) { index := k }) = 1) →
          env.get k * (env.get k + -1) = 0 := by
        intro k hb
        have hg : env.get k
            = Expression.eval env.toEnvironment (var (F := F p) { index := k }) := rfl
        rw [hg]
        rcases hb with h0 | h1
        · rw [h0, zero_mul]
        · rw [h1]
          norm_num
      refine ⟨hzero_of_bool _ core.2.1, hzero_of_bool _ core.2.2.1, hzero_of_bool _ core.2.2.2.1,
        core.1,
        interpolatedMul_completeness (i₀ + (m + 3) + m * (B - 1)) input_var.a input_var.b env h_pvAB,
        interpolatedMul_completeness (i₀ + (m + 3) + m * (B - 1) + (2 * m - 1))
          input_var.target input_var.target env h_pvXX,
        core.2.2.2.2⟩



omit [NeZero m] in

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
    (hNf : ∀ j, V.Nf j = 2 * ((m + 1) * 2 ^ (2 * P.B)))
    (hNfR : ∀ j, VR.Nf j = (4 * m + 1) * 2 ^ (2 * P.B))
    (c : Vector (F p) (2 * m))
    (hB3 : 3 ≤ P.B)
    (hp8 : 2 ^ (2 * P.B) * (4 * m + 1) * 8 < p)
    [Fact (p > 2)] :
    (circuit P gf posOf G V VR hgv hNf hNfR c hB3 hp8).ComputableWitnesses := by
  letI : NeZero (2 * m) := ⟨by have := Nat.pos_of_neZero m; omega⟩
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition input env env')
    ((main P gf posOf G V VR hgv c input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main
  let qwit : ProverEnvironment (F p) → ℕ := fun env =>
    (evalValue P.B env input.a * evalValue P.B env input.b
        + 3 * (evalValue P.B env input.modulus * evalValue P.B env input.modulus)
        - 3 * (evalValue P.B env input.target * evalValue P.B env input.target))
      / evalValue P.B env input.modulus
  let qc : Circuit (F p) (Var (BigInt m) (F p)) := ProvableType.witness (α := BigInt m) fun env =>
    let qval : ℕ := qwit env % 2 ^ (P.B * m)
    Vector.ofFn fun k : Fin m => ((qval / 2 ^ (P.B * k.val) % 2 ^ P.B : ℕ) : F p)
  let q := qc.output offset
  let qh0Off := offset + qc.localLength offset
  let qh0 : Expression (F p) := (ProvableType.witness (α := field)
    (fun env => (((qwit env / 2 ^ (P.B * m)) % 2 : ℕ) : F p))).output qh0Off
  let qh1Off := qh0Off + 1
  let qh1 : Expression (F p) := (ProvableType.witness (α := field)
    (fun env => (((qwit env / 2 ^ (P.B * m) / 2) % 2 : ℕ) : F p))).output qh1Off
  let qh2Off := qh1Off + 1
  let qh2 : Expression (F p) := (ProvableType.witness (α := field)
    (fun env => (((qwit env / 2 ^ (P.B * m) / 4) % 2 : ℕ) : F p))).output qh2Off
  let nqOff := qh2Off + 1
  let nqc : Circuit (F p) Unit := Normalize.circuit P q
  let pcOff := nqOff + nqc.localLength nqOff
  let pcv := (interpolatedMul input.a input.b).output pcOff
  let pxOff := pcOff + (interpolatedMul input.a input.b).localLength pcOff
  let pxv := (interpolatedMul input.target input.target).output pxOff
  let eqOff := pxOff + (interpolatedMul input.target input.target).localLength pxOff
  have h_qlen : qc.localLength offset = m := by
    simp [qc, ProvableType.witness, Circuit.localLength, Operations.localLength, size]
  have h_pclen : (interpolatedMul input.a input.b).localLength pcOff = 2 * m - 1 :=
    interpolatedMul_localLength pcOff input.a input.b
  have h_pxlen : (interpolatedMul input.target input.target).localLength pxOff = 2 * m - 1 :=
    interpolatedMul_localLength pxOff input.target input.target
  have hstable4 : ∀ (env env' : ProverEnvironment (F p)),
      eval env input = eval env' input →
      evalValue P.B env input.a = evalValue P.B env' input.a
      ∧ evalValue P.B env input.b = evalValue P.B env' input.b
      ∧ evalValue P.B env input.modulus = evalValue P.B env' input.modulus
      ∧ evalValue P.B env input.target = evalValue P.B env' input.target := by
    intro env env' h_input
    exact ⟨evalValue_stable P.B input.a (by
        simpa [circuit_norm] using congrArg (fun x : MulModTarget.Inputs m (F p) => x.a) h_input),
      evalValue_stable P.B input.b (by
        simpa [circuit_norm] using congrArg (fun x : MulModTarget.Inputs m (F p) => x.b) h_input),
      evalValue_stable P.B input.modulus (by
        simpa [circuit_norm] using congrArg
          (fun x : MulModTarget.Inputs m (F p) => x.modulus) h_input),
      evalValue_stable P.B input.target (by
        simpa [circuit_norm] using congrArg
          (fun x : MulModTarget.Inputs m (F p) => x.target) h_input)⟩
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.provableWitness_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.assertZero_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_structuralComputableWitnesses_iff]
  and_intros
  · -- q_lo witness reads only the input
    intro _ h_input
    obtain ⟨ha, hb, hn, hx⟩ := hstable4 _ _ h_input
    simp only [ha, hb, hn, hx]
  · -- bit 0 reads only the input
    intro _ h_input
    obtain ⟨ha, hb, hn, hx⟩ := hstable4 _ _ h_input
    simp only [ha, hb, hn, hx]
  · -- bit 1 reads only the input
    intro _ h_input
    obtain ⟨ha, hb, hn, hx⟩ := hstable4 _ _ h_input
    simp only [ha, hb, hn, hx]
  · -- bit 2 reads only the input
    intro _ h_input
    obtain ⟨ha, hb, hn, hx⟩ := hstable4 _ _ h_input
    simp only [ha, hb, hn, hx]
  · -- the three boolean rows carry no witnesses
    trivial
  · trivial
  · trivial
  · -- Normalize q_lo
    exact Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
      (Normalize.circuit P) input q nqOff
      (by
        intro k env env' hle h_agree _
        have hk : offset + m ≤ k := by
          dsimp only [nqOff, qh2Off, qh1Off, qh0Off] at hle
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
  · -- interpolatedMul x x
    exact interpolatedMul_structuralComputableWitnesses input input.target input.target pxOff
      (by
        intro k env env' _ _ h_input
        have hx : eval env input.target = eval env' input.target := by
          simpa [circuit_norm] using congrArg
            (fun x : MulModTarget.Inputs m (F p) => x.target) h_input
        exact ⟨hx, hx⟩)
      env env'
  · -- GroupedEqXV over the L = 2m flanks
    exact Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
      (GroupedEqXV.circuit P.B gf posOf G V VR hgv P.hB1) input
      { lhs := lVecW pcv c,
        rhs := sVecTD (sVecX q input.modulus pxv)
          (qh0 + ((2 : F p) : Expression (F p)) * qh1
            + ((4 : F p) : Expression (F p)) * qh2) input.modulus }
      eqOff
      (by
        intro k env env' hle h_agree h_input
        have hk_px : pxOff + (2 * m - 1) ≤ k := by
          have h := hle
          dsimp only [eqOff] at h
          rw [h_pxlen] at h
          exact h
        have hk_pc : pcOff + (2 * m - 1) ≤ k := by
          have h := hle
          dsimp only [eqOff, pxOff] at h
          rw [h_pclen] at h
          omega
        have hk_q : offset + m ≤ k := by
          have h := hle
          dsimp only [eqOff, pxOff, pcOff, nqOff, qh2Off, qh1Off, qh0Off] at h
          rw [h_qlen] at h
          omega
        have hk_bits : offset + m + 3 ≤ k := by
          have h := hle
          dsimp only [eqOff, pxOff, pcOff, nqOff, qh2Off, qh1Off, qh0Off] at h
          rw [h_qlen] at h
          omega
        have hPc : Vector.map (Expression.eval env.toEnvironment) pcv
            = Vector.map (Expression.eval env'.toEnvironment) pcv :=
          interpolatedMul_output_stable pcOff input.a input.b h_agree hk_pc
        have hPx : Vector.map (Expression.eval env.toEnvironment) pxv
            = Vector.map (Expression.eval env'.toEnvironment) pxv :=
          interpolatedMul_output_stable pxOff input.target input.target h_agree hk_px
        have hq_vec : eval env q = eval env' q := bigIntWitnessOutput_stable _ h_agree hk_q
        have hbit_eval : ∀ j : ℕ, j < 3 →
            env.get (offset + m + j) = env'.get (offset + m + j) := by
          intro j hj
          apply h_agree (offset + m + j)
          omega
        have hn : eval env input.modulus = eval env' input.modulus := by
          simpa [circuit_norm] using congrArg
            (fun x : MulModTarget.Inputs m (F p) => x.modulus) h_input
        have hqh_eval : ∀ e ∈ [qh0, qh1, qh2],
            Expression.eval env.toEnvironment e = Expression.eval env'.toEnvironment e := by
          intro e he
          simp only [List.mem_cons, List.not_mem_nil, or_false] at he
          have h0 : qh0 = var (F := F p) { index := offset + m } := by
            dsimp only [qh0, qh0Off]
            rw [h_qlen]
            rfl
          have h1 : qh1 = var (F := F p) { index := offset + m + 1 } := by
            dsimp only [qh1, qh1Off, qh0Off]
            rw [h_qlen]
            rfl
          have h2 : qh2 = var (F := F p) { index := offset + m + 2 } := by
            dsimp only [qh2, qh2Off, qh1Off, qh0Off]
            rw [h_qlen]
            rfl
          rcases he with rfl | rfl | rfl
          · rw [h0]
            exact hbit_eval 0 (by omega)
          · rw [h1]
            have := hbit_eval 1 (by omega)
            simpa using this
          · rw [h2]
            have := hbit_eval 2 (by omega)
            simpa using this
        have hL8 : Vector.map (Expression.eval env.toEnvironment) (lVecW pcv c)
            = Vector.map (Expression.eval env'.toEnvironment) (lVecW pcv c) := by
          apply Vector.ext
          intro i hi
          simp only [Vector.getElem_map, lVecW, Vector.getElem_mapFinRange]
          by_cases hlt : i < 2 * m - 1
          · rw [dif_pos hlt]
            have hpc_i : Expression.eval env.toEnvironment (pcv[i]'hlt)
                = Expression.eval env'.toEnvironment (pcv[i]'hlt) := by
              have := congrArg (fun v : Vector (F p) (2 * m - 1) => v[i]'hlt) hPc
              simpa only [Vector.getElem_map] using this
            rw [show Expression.eval env.toEnvironment
                  (pcv[i]'hlt + ((c[i]'hi : F p) : Expression (F p)))
                  = Expression.eval env.toEnvironment (pcv[i]'hlt) + c[i]'hi from rfl,
              show Expression.eval env'.toEnvironment
                  (pcv[i]'hlt + ((c[i]'hi : F p) : Expression (F p)))
                  = Expression.eval env'.toEnvironment (pcv[i]'hlt) + c[i]'hi from rfl,
              hpc_i]
          · rw [dif_neg hlt]
            rfl
        have hS8 : Vector.map (Expression.eval env.toEnvironment)
              (sVecTD (sVecX q input.modulus pxv)
                (qh0 + ((2 : F p) : Expression (F p)) * qh1
                  + ((4 : F p) : Expression (F p)) * qh2) input.modulus)
            = Vector.map (Expression.eval env'.toEnvironment)
              (sVecTD (sVecX q input.modulus pxv)
                (qh0 + ((2 : F p) : Expression (F p)) * qh1
                  + ((4 : F p) : Expression (F p)) * qh2) input.modulus) := by
          set qhE := qh0 + ((2 : F p) : Expression (F p)) * qh1
            + ((4 : F p) : Expression (F p)) * qh2 with hqhE
          have hqhE_eval : Expression.eval env.toEnvironment qhE
              = Expression.eval env'.toEnvironment qhE := by
            rw [show Expression.eval env.toEnvironment qhE
                  = Expression.eval env.toEnvironment qh0
                    + (2 : F p) * Expression.eval env.toEnvironment qh1
                    + (4 : F p) * Expression.eval env.toEnvironment qh2 from rfl,
              show Expression.eval env'.toEnvironment qhE
                  = Expression.eval env'.toEnvironment qh0
                    + (2 : F p) * Expression.eval env'.toEnvironment qh1
                    + (4 : F p) * Expression.eval env'.toEnvironment qh2 from rfl,
              hqh_eval qh0 (by simp), hqh_eval qh1 (by simp), hqh_eval qh2 (by simp)]
          apply Vector.ext
          intro i hi
          have hbase_i : ∀ (hlt : i < 2 * m - 1),
              Expression.eval env.toEnvironment
                ((sVecX q input.modulus pxv)[i]'hlt)
              = Expression.eval env'.toEnvironment
                ((sVecX q input.modulus pxv)[i]'hlt) := by
            intro hlt
            have hsq_i : Expression.eval env.toEnvironment
                  ((bigIntMulNoReduce q input.modulus)[i]'hlt)
                = Expression.eval env'.toEnvironment
                  ((bigIntMulNoReduce q input.modulus)[i]'hlt) :=
              bigIntMulNoReduce_coeff_stable env.toEnvironment env'.toEnvironment
                q input.modulus
                (fun j hj => bigInt_getElem_eval_eq hq_vec j hj)
                (fun j hj => bigInt_getElem_eval_eq hn j hj) ⟨i, hlt⟩
            have hpx_i : Expression.eval env.toEnvironment (pxv[i]'hlt)
                = Expression.eval env'.toEnvironment (pxv[i]'hlt) := by
              have := congrArg (fun v : Vector (F p) (2 * m - 1) => v[i]'hlt) hPx
              simpa only [Vector.getElem_map] using this
            simp only [sVecX, Vector.getElem_mapFinRange]
            rw [show Expression.eval env.toEnvironment
                  ((bigIntMulNoReduce q input.modulus)[i]'hlt
                    + ((3 : F p) : Expression (F p)) * (pxv[i]'hlt))
                  = Expression.eval env.toEnvironment
                      ((bigIntMulNoReduce q input.modulus)[i]'hlt)
                    + (3 : F p) * Expression.eval env.toEnvironment (pxv[i]'hlt) from rfl,
              show Expression.eval env'.toEnvironment
                  ((bigIntMulNoReduce q input.modulus)[i]'hlt
                    + ((3 : F p) : Expression (F p)) * (pxv[i]'hlt))
                  = Expression.eval env'.toEnvironment
                      ((bigIntMulNoReduce q input.modulus)[i]'hlt)
                    + (3 : F p) * Expression.eval env'.toEnvironment (pxv[i]'hlt) from rfl,
              hsq_i, hpx_i]
          simp only [Vector.getElem_map, sVecTD, Vector.getElem_mapFinRange]
          have hflank_i : ∀ (hm' : m ≤ i ∧ i - m < m),
              Expression.eval env.toEnvironment (qhE * input.modulus[i - m]'hm'.2)
              = Expression.eval env'.toEnvironment (qhE * input.modulus[i - m]'hm'.2) := by
            intro hm'
            rw [show Expression.eval env.toEnvironment (qhE * input.modulus[i - m]'hm'.2)
                  = Expression.eval env.toEnvironment qhE
                    * Expression.eval env.toEnvironment (input.modulus[i - m]'hm'.2) from rfl,
              show Expression.eval env'.toEnvironment (qhE * input.modulus[i - m]'hm'.2)
                  = Expression.eval env'.toEnvironment qhE
                    * Expression.eval env'.toEnvironment (input.modulus[i - m]'hm'.2) from rfl,
              hqhE_eval, bigInt_getElem_eval_eq hn (i - m) hm'.2]
          by_cases hlt : i < 2 * m - 1
          · rw [dif_pos hlt]
            by_cases hm' : m ≤ i ∧ i - m < m
            · rw [dif_pos hm']
              rw [show Expression.eval env.toEnvironment
                    ((sVecX q input.modulus pxv)[i]'hlt
                      + qhE * input.modulus[i - m]'hm'.2)
                    = Expression.eval env.toEnvironment
                        ((sVecX q input.modulus pxv)[i]'hlt)
                      + Expression.eval env.toEnvironment (qhE * input.modulus[i - m]'hm'.2)
                    from rfl,
                show Expression.eval env'.toEnvironment
                    ((sVecX q input.modulus pxv)[i]'hlt
                      + qhE * input.modulus[i - m]'hm'.2)
                    = Expression.eval env'.toEnvironment
                        ((sVecX q input.modulus pxv)[i]'hlt)
                      + Expression.eval env'.toEnvironment (qhE * input.modulus[i - m]'hm'.2)
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

end MulModTargetW
end Solution.Secp256k1ScalarMul
