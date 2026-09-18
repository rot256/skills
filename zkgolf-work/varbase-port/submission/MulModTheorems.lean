import Solution.Secp256k1ScalarMul.Theorems



namespace Solution.Secp256k1ScalarMul
open Solution.Secp256k1ScalarMul.Limbs



namespace MulMod

section
variable {p : ℕ} [Fact p.Prime]
variable {m : ℕ} [NeZero m]



omit [NeZero m] in

lemma value_map_eval {B : ℕ} (env : Environment (F p)) (x : Var (BigInt m) (F p)) :
    BigInt.value B (Vector.map (Expression.eval env) x)
      = ∑ k : Fin m, (Expression.eval env x[k.val]).val * 2 ^ (B * k.val) := by
  rw [BigInt.value_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fin.getElem_fin, Vector.getElem_map]


lemma polyValue_mul_eq {B : ℕ} (env : Environment (F p))
    (a b : Var (BigInt m) (F p))
    (ha : ∀ i : Fin m, (Expression.eval env a[i.val]).val < 2 ^ B)
    (hb : ∀ i : Fin m, (Expression.eval env b[i.val]).val < 2 ^ B)
    (hfield : m * (2 ^ B * 2 ^ B) < p) :
    polyValue B (Vector.map (Expression.eval env) (bigIntMulNoReduce a b))
      = BigInt.value B (Vector.map (Expression.eval env) a)
        * BigInt.value B (Vector.map (Expression.eval env) b) := by
  rw [polyValue_bigIntMulNoReduce env a b ha hb hfield, value_map_eval, value_map_eval]


lemma polyValue_Sqn_eq {B : ℕ} (env : Environment (F p))
    (q n : Var (BigInt m) (F p))
    (hq : ∀ i : Fin m, (Expression.eval env q[i.val]).val < 2 ^ B)
    (hn : ∀ i : Fin m, (Expression.eval env n[i.val]).val < 2 ^ B)
    (hfield : m * (2 ^ B * 2 ^ B) < p) :
    polyValue B (Vector.map (Expression.eval env) (bigIntMulNoReduce q n))
      = BigInt.value B (Vector.map (Expression.eval env) q)
        * BigInt.value B (Vector.map (Expression.eval env) n) :=
  polyValue_mul_eq env q n hq hn hfield


lemma remainder_eq {a b q n r : ℕ} (heq : a * b = q * n + r) (hr : r < n) :
    r = a * b % n := by
  rw [heq, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]


def sVec (q n : Var (BigInt m) (F p)) (off : ℕ) :
    Vector (Expression (F p)) (2 * m - 1) :=
  Vector.mapFinRange (2 * m - 1) fun k =>
    if h : k.val < m then (bigIntMulNoReduce q n)[k.val] + var { index := off + k.val }
    else (bigIntMulNoReduce q n)[k.val]


lemma polyValue_sVec_split {B : ℕ} (env : Environment (F p))
    (q n : Var (BigInt m) (F p)) (off : ℕ)
    (hnowrap : ∀ k : Fin (2 * m - 1), k.val < m →
      (Expression.eval env ((bigIntMulNoReduce q n)[k.val])).val
        + (Expression.eval env (var (F := F p) { index := off + k.val })).val < p) :
    polyValue B (Vector.map (Expression.eval env) (sVec q n off))
      = polyValue B (Vector.map (Expression.eval env) (bigIntMulNoReduce q n))
        + BigInt.value B (Vector.map (Expression.eval env)
            (Vector.mapRange m fun i => var (F := F p) { index := off + i })) := by
  rw [polyValue, polyValue, value_map_eval]
  -- per-index value of S
  have hS : ∀ k : Fin (2 * m - 1),
      (Vector.map (Expression.eval env) (sVec q n off))[k.val].val
        = (Expression.eval env ((bigIntMulNoReduce q n)[k.val])).val
          + (if h : k.val < m then (Expression.eval env (var (F := F p) { index := off + k.val })).val else 0) := by
    intro k
    rw [Vector.getElem_map]
    simp only [sVec, Vector.getElem_mapFinRange]
    by_cases hk : k.val < m
    · simp only [dif_pos hk]
      rw [show Expression.eval env ((bigIntMulNoReduce q n)[k.val] + var { index := off + k.val })
            = Expression.eval env ((bigIntMulNoReduce q n)[k.val])
              + Expression.eval env (var (F := F p) { index := off + k.val }) from rfl,
        ZMod.val_add_of_lt (hnowrap k hk)]
    · simp only [dif_neg hk, Nat.add_zero]
  -- rewrite LHS sum
  simp only [hS]
  -- distribute (Sqn + r-part) * 2^(Bk)
  rw [show (∑ k : Fin (2 * m - 1),
        ((Expression.eval env ((bigIntMulNoReduce q n)[k.val])).val
          + (if h : k.val < m then (Expression.eval env (var (F := F p) { index := off + k.val })).val else 0))
          * 2 ^ (B * k.val))
      = (∑ k : Fin (2 * m - 1),
          (Expression.eval env ((bigIntMulNoReduce q n)[k.val])).val * 2 ^ (B * k.val))
        + (∑ k : Fin (2 * m - 1),
          (if h : k.val < m then (Expression.eval env (var (F := F p) { index := off + k.val })).val else 0)
            * 2 ^ (B * k.val)) from by
    rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro k _; ring]
  congr 1
  · -- Sqn part = polyValue Sqn
    apply Finset.sum_congr rfl; intro k _; rw [Vector.getElem_map]
  · -- r part = value r
    -- RHS: simplify the mapRange index to `env.get (off + k)`
    have hRHS : (∑ k : Fin m, (Expression.eval env (Vector.mapRange m
          fun i => var (F := F p) { index := off + i })[k.val]).val * 2 ^ (B * k.val))
        = ∑ k ∈ Finset.range m,
            (Expression.eval env (var (F := F p) { index := off + k })).val * 2 ^ (B * k) := by
      rw [← Fin.sum_univ_eq_sum_range (fun k => (Expression.eval env (var (F := F p) { index := off + k })).val * 2 ^ (B * k))]
      apply Finset.sum_congr rfl
      intro k _
      congr 2
      simp [circuit_norm]
    rw [hRHS]
    -- LHS: guarded sum over Fin (2m-1) collapses to range m (terms k≥m are 0)
    simp only [dite_eq_ite]
    rw [Fin.sum_univ_eq_sum_range (fun k =>
      (if k < m then (Expression.eval env (var (F := F p) { index := off + k })).val else 0) * 2 ^ (B * k))]
    have hext : (∑ k ∈ Finset.range (2 * m - 1),
          (if k < m then (Expression.eval env (var (F := F p) { index := off + k })).val else 0)
            * 2 ^ (B * k))
        = ∑ k ∈ Finset.range m,
          (Expression.eval env (var (F := F p) { index := off + k })).val * 2 ^ (B * k) := by
      rw [← Finset.sum_subset (Finset.range_subset_range.mpr (by have := Nat.pos_of_neZero m; omega : m ≤ 2 * m - 1))
        (f := fun k => (if k < m then (Expression.eval env (var (F := F p) { index := off + k })).val else 0) * 2 ^ (B * k))]
      · apply Finset.sum_congr rfl; intro k hk
        rw [Finset.mem_range] at hk; rw [if_pos hk]
      · intro k _ hk
        rw [Finset.mem_range] at hk; rw [if_neg hk, Nat.zero_mul]
    rw [hext]


lemma coeff_P_bound {B : ℕ} (env : Environment (F p))
    (a b : Var (BigInt m) (F p)) (k : Fin (2 * m - 1))
    (ha : ∀ i : Fin m, (Expression.eval env a[i.val]).val < 2 ^ B)
    (hb : ∀ i : Fin m, (Expression.eval env b[i.val]).val < 2 ^ B)
    (hfield : m * (2 ^ B * 2 ^ B) < p) :
    (Expression.eval env ((bigIntMulNoReduce a b)[k.val])).val < (m + 1) * 2 ^ (2 * B) := by
  have h := val_bigIntMulNoReduce_coeff_lt env a b k ha hb hfield
  have : m * 2 ^ (2 * B) ≤ (m + 1) * 2 ^ (2 * B) := by
    apply Nat.mul_le_mul_right; omega
  omega


lemma coeff_S_bound {B : ℕ} (env : Environment (F p))
    (q n : Var (BigInt m) (F p)) (off : ℕ) (k : Fin (2 * m - 1))
    (hq : ∀ i : Fin m, (Expression.eval env q[i.val]).val < 2 ^ B)
    (hn : ∀ i : Fin m, (Expression.eval env n[i.val]).val < 2 ^ B)
    (hr : ∀ j : ℕ, j < m → (Expression.eval env (var (F := F p) { index := off + j })).val < 2 ^ B)
    (hfield : m * (2 ^ B * 2 ^ B) < p) :
    (Expression.eval env ((sVec q n off)[k.val])).val < (m + 1) * 2 ^ (2 * B) := by
  have hSqn := val_bigIntMulNoReduce_coeff_lt env q n k hq hn hfield
  have hpow : (2 : ℕ) ^ B ≤ 2 ^ (2 * B) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hmm : (m + 1) * 2 ^ (2 * B) = m * 2 ^ (2 * B) + 2 ^ (2 * B) := by ring
  rw [hmm]
  generalize hX : 2 ^ (2 * B) = X at *
  generalize hY : m * X = Y at *
  simp only [sVec, Vector.getElem_mapFinRange]
  by_cases hk : k.val < m
  · rw [dif_pos hk]
    have hr' := hr k.val hk
    have hadd : (Expression.eval env ((bigIntMulNoReduce q n)[k.val])
        + Expression.eval env (var (F := F p) { index := off + k.val })).val
        ≤ (Expression.eval env ((bigIntMulNoReduce q n)[k.val])).val
          + (Expression.eval env (var (F := F p) { index := off + k.val })).val := ZMod.val_add_le _ _
    rw [show Expression.eval env ((bigIntMulNoReduce q n)[k.val] + var { index := off + k.val })
          = Expression.eval env ((bigIntMulNoReduce q n)[k.val])
            + Expression.eval env (var (F := F p) { index := off + k.val }) from rfl]
    omega
  · rw [dif_neg hk]
    omega


lemma witnessedMul_map_eval (env : Environment (F p)) (off : ℕ)
    (a b : Var (BigInt m) (F p))
    (hprod : ∀ t : Fin (m * m),
      Expression.eval env (a[t.val / m]'(Nat.div_lt_of_lt_mul t.isLt))
          * Expression.eval env (b[t.val % m]'(Nat.mod_lt _ (Nat.pos_of_neZero m)))
        = env.get (off + t.val)) :
    Vector.map (Expression.eval env)
        (bigIntMulVars (Vector.mapRange (m * m) fun i => var (F := F p) { index := off + i }))
      = Vector.map (Expression.eval env) (bigIntMulNoReduce a b) := by
  apply map_eval_bigIntMulVars_eq env a b
  intro i j
  -- the product variable at index i*m+j reads env.get (off + (i*m+j))
  have hidx : (Vector.mapRange (m * m) fun i => var (F := F p) { index := off + i })[i.val * m + j.val]'(by
        have := i.isLt; have := j.isLt
        calc i.val * m + j.val < i.val * m + m := by omega
          _ = (i.val + 1) * m := by ring
          _ ≤ m * m := by apply Nat.mul_le_mul_right; omega)
      = var (F := F p) { index := off + (i.val * m + j.val) } := by
    simp [circuit_norm]
  rw [hidx]
  -- the product assert at t = i*m+j
  have ht : (i.val * m + j.val) < m * m := by
    have := i.isLt; have := j.isLt
    calc i.val * m + j.val < i.val * m + m := by omega
      _ = (i.val + 1) * m := by ring
      _ ≤ m * m := by apply Nat.mul_le_mul_right; omega
  have hd : (i.val * m + j.val) / m = i.val := by
    rw [Nat.mul_comm, Nat.mul_add_div (Nat.pos_of_neZero m), Nat.div_eq_of_lt j.isLt, Nat.add_zero]
  have hr : (i.val * m + j.val) % m = j.val := by
    rw [Nat.mul_comm, Nat.mul_add_mod]; exact Nat.mod_eq_of_lt j.isLt
  have := hprod ⟨i.val * m + j.val, ht⟩
  simp only [hd, hr] at this
  rw [show Expression.eval env (var (F := F p) { index := off + (i.val * m + j.val) })
        = env.get (off + (i.val * m + j.val)) from rfl, ← this]

omit [NeZero m] in

lemma eqImpl_bridge {B rOff : ℕ} (env : Environment (F p))
    (Pv Pn Qv Qn : Vector (Expression (F p)) (2 * m - 1))
    (hP_get : ∀ k : Fin (2 * m - 1), Expression.eval env Pv[k.val] = Expression.eval env Pn[k.val])
    (hQ_get : ∀ k : Fin (2 * m - 1), Expression.eval env Qv[k.val] = Expression.eval env Qn[k.val])
    (himpl :
      ((∀ k : Fin (2 * m - 1), (Expression.eval env Pv[k.val]).val < (m + 1) * 2 ^ (2 * B)) ∧
        ∀ k : Fin (2 * m - 1),
          (Expression.eval env (if h : k.val < m then Qv[k.val] + var { index := rOff + k.val }
            else Qv[k.val])).val < (m + 1) * 2 ^ (2 * B)) →
        polyValue B (Vector.map (Expression.eval env) Pv) =
          polyValue B (Vector.map (Expression.eval env)
            (Vector.mapFinRange (2 * m - 1) fun k =>
              if h : k.val < m then Qv[k.val] + var { index := rOff + k.val } else Qv[k.val]))) :
    ((∀ k : Fin (2 * m - 1), (Expression.eval env Pn[k.val]).val < (m + 1) * 2 ^ (2 * B)) ∧
      ∀ k : Fin (2 * m - 1),
        (Expression.eval env (if h : k.val < m then Qn[k.val] + var { index := rOff + k.val }
          else Qn[k.val])).val < (m + 1) * 2 ^ (2 * B)) →
      polyValue B (Vector.map (Expression.eval env) Pn) =
        polyValue B (Vector.map (Expression.eval env)
          (Vector.mapFinRange (2 * m - 1) fun k =>
            if h : k.val < m then Qn[k.val] + var { index := rOff + k.val } else Qn[k.val])) := by
  -- per-index eval equality of the two `S` dite vectors
  have hS_get : ∀ k : Fin (2 * m - 1),
      Expression.eval env (if h : k.val < m then Qv[k.val] + var (F := F p) { index := rOff + k.val } else Qv[k.val])
        = Expression.eval env (if h : k.val < m then Qn[k.val] + var (F := F p) { index := rOff + k.val } else Qn[k.val]) := by
    intro k
    by_cases hk : k.val < m
    · simp only [dif_pos hk]
      show Expression.eval env Qv[k.val] + Expression.eval env (var (F := F p) { index := rOff + k.val })
        = Expression.eval env Qn[k.val] + Expression.eval env (var (F := F p) { index := rOff + k.val })
      rw [hQ_get k]
    · simp only [dif_neg hk]; exact hQ_get k
  -- the two `S` vectors map-eval equally
  have hSvec : Vector.map (Expression.eval env)
        (Vector.mapFinRange (2 * m - 1) fun k =>
          if h : k.val < m then Qv[k.val] + var (F := F p) { index := rOff + k.val } else Qv[k.val])
      = Vector.map (Expression.eval env)
        (Vector.mapFinRange (2 * m - 1) fun k =>
          if h : k.val < m then Qn[k.val] + var (F := F p) { index := rOff + k.val } else Qn[k.val]) := by
    apply Vector.ext; intro k hk
    rw [Vector.getElem_map, Vector.getElem_map, Vector.getElem_mapFinRange, Vector.getElem_mapFinRange]
    exact hS_get ⟨k, hk⟩
  have hPvec : Vector.map (Expression.eval env) Pv = Vector.map (Expression.eval env) Pn := by
    apply Vector.ext; intro k hk; rw [Vector.getElem_map, Vector.getElem_map]; exact hP_get ⟨k, hk⟩
  intro hbounds
  rw [← hPvec, ← hSvec]
  apply himpl
  refine ⟨fun k => ?_, fun k => ?_⟩
  · rw [hP_get k]; exact hbounds.1 k
  · rw [hS_get k]; exact hbounds.2 k

omit [NeZero m] in

lemma eqConj_bridge {B rOff : ℕ} (env : Environment (F p))
    (Pv Pn Qv Qn : Vector (Expression (F p)) (2 * m - 1))
    (hP_get : ∀ k : Fin (2 * m - 1), Expression.eval env Pv[k.val] = Expression.eval env Pn[k.val])
    (hQ_get : ∀ k : Fin (2 * m - 1), Expression.eval env Qv[k.val] = Expression.eval env Qn[k.val])
    (hconj :
      ((∀ k : Fin (2 * m - 1), (Expression.eval env Pn[k.val]).val < (m + 1) * 2 ^ (2 * B)) ∧
        (∀ k : Fin (2 * m - 1),
          (Expression.eval env (if h : k.val < m then Qn[k.val] + var { index := rOff + k.val }
            else Qn[k.val])).val < (m + 1) * 2 ^ (2 * B))) ∧
        polyValue B (Vector.map (Expression.eval env) Pn) =
          polyValue B (Vector.map (Expression.eval env)
            (Vector.mapFinRange (2 * m - 1) fun k =>
              if h : k.val < m then Qn[k.val] + var { index := rOff + k.val } else Qn[k.val]))) :
    ((∀ k : Fin (2 * m - 1), (Expression.eval env Pv[k.val]).val < (m + 1) * 2 ^ (2 * B)) ∧
      (∀ k : Fin (2 * m - 1),
        (Expression.eval env (if h : k.val < m then Qv[k.val] + var { index := rOff + k.val }
          else Qv[k.val])).val < (m + 1) * 2 ^ (2 * B))) ∧
        polyValue B (Vector.map (Expression.eval env) Pv) =
          polyValue B (Vector.map (Expression.eval env)
            (Vector.mapFinRange (2 * m - 1) fun k =>
              if h : k.val < m then Qv[k.val] + var { index := rOff + k.val } else Qv[k.val])) := by
  have hS_get : ∀ k : Fin (2 * m - 1),
      Expression.eval env (if h : k.val < m then Qv[k.val] + var (F := F p) { index := rOff + k.val } else Qv[k.val])
        = Expression.eval env (if h : k.val < m then Qn[k.val] + var (F := F p) { index := rOff + k.val } else Qn[k.val]) := by
    intro k
    by_cases hk : k.val < m
    · simp only [dif_pos hk]
      show Expression.eval env Qv[k.val] + Expression.eval env (var (F := F p) { index := rOff + k.val })
        = Expression.eval env Qn[k.val] + Expression.eval env (var (F := F p) { index := rOff + k.val })
      rw [hQ_get k]
    · simp only [dif_neg hk]; exact hQ_get k
  have hPvec : Vector.map (Expression.eval env) Pv = Vector.map (Expression.eval env) Pn := by
    apply Vector.ext; intro k hk; rw [Vector.getElem_map, Vector.getElem_map]; exact hP_get ⟨k, hk⟩
  have hSvec : Vector.map (Expression.eval env)
        (Vector.mapFinRange (2 * m - 1) fun k =>
          if h : k.val < m then Qv[k.val] + var (F := F p) { index := rOff + k.val } else Qv[k.val])
      = Vector.map (Expression.eval env)
        (Vector.mapFinRange (2 * m - 1) fun k =>
          if h : k.val < m then Qn[k.val] + var (F := F p) { index := rOff + k.val } else Qn[k.val]) := by
    apply Vector.ext; intro k hk
    rw [Vector.getElem_map, Vector.getElem_map, Vector.getElem_mapFinRange, Vector.getElem_mapFinRange]
    exact hS_get ⟨k, hk⟩
  refine ⟨⟨fun k => ?_, fun k => ?_⟩, ?_⟩
  · rw [hP_get k]; exact hconj.1.1 k
  · rw [hS_get k]; exact hconj.1.2 k
  · rw [hPvec, hSvec]; exact hconj.2


lemma mulMod_soundness_core {B : ℕ} (hp : 2 ^ (2 * B) * (m + 1) * 4 < p)
    (i₀ : ℕ) (env : Environment (F p))
    (input_var : ProvablePair (BigInt m) (ProvablePair (BigInt m) (BigInt m)) (Expression (F p)))
    (input : ProvablePair (BigInt m) (ProvablePair (BigInt m) (BigInt m)) (F p))
    (h_input : (Vector.map (Expression.eval env) input_var.1,
        Vector.map (Expression.eval env) input_var.2.1,
        Vector.map (Expression.eval env) input_var.2.2) = input)
    (ha_norm : BigInt.Normalized B input.1) (hb_norm : BigInt.Normalized B input.2.1)
    (hn_norm : BigInt.Normalized B input.2.2)
    (hq_norm : BigInt.Normalized B (Vector.map (Expression.eval env)
        (Vector.mapRange m fun i ↦ var { index := i₀ + i })))
    (hr_norm : BigInt.Normalized B (Vector.map (Expression.eval env)
        (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })))
    (h_eq_impl :
      ((∀ k : Fin (2 * m - 1),
          (Expression.eval env (bigIntMulNoReduce input_var.1 input_var.2.1)[k.val]).val
            < (m + 1) * 2 ^ (2 * B)) ∧
        ∀ k : Fin (2 * m - 1),
          (Expression.eval env
            (if h : k.val < m then
              (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2)[k.val] +
                var { index := i₀ + m + k.val }
            else (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2)[k.val])).val
            < (m + 1) * 2 ^ (2 * B)) →
        polyValue B (Vector.map (Expression.eval env) (bigIntMulNoReduce input_var.1 input_var.2.1)) =
          polyValue B
            (Vector.map (Expression.eval env)
              (Vector.mapFinRange (2 * m - 1) fun k ↦
                if h : k.val < m then
                  (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2)[k.val] +
                    var { index := i₀ + m + k.val }
                else (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2)[k.val])))
    (h_lt_impl :
      BigInt.Normalized B (Vector.map (Expression.eval env)
          (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })) ∧
        BigInt.Normalized B (Vector.map (Expression.eval env) input_var.2.2) →
        BigInt.value B (Vector.map (Expression.eval env)
            (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })) <
          BigInt.value B (Vector.map (Expression.eval env) input_var.2.2)) :
    BigInt.Normalized B (Vector.map (Expression.eval env)
        (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })) ∧
      BigInt.value B (Vector.map (Expression.eval env)
          (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })) =
        BigInt.value B input.1 * BigInt.value B input.2.1 % BigInt.value B input.2.2 := by
  -- abbreviations
  set qVar := (Vector.mapRange m fun i ↦ var (F := F p) { index := i₀ + i }) with hqVar
  set rVar := (Vector.mapRange m fun i ↦ var (F := F p) { index := i₀ + m + i }) with hrVar
  set qv := (Vector.map (Expression.eval env) qVar : BigInt m (F p)) with hqv
  set rv := (Vector.map (Expression.eval env) rVar : BigInt m (F p)) with hrv
  -- digit bounds (each input/witness limb < 2^B)
  have ha_lt : ∀ i : Fin m, (Expression.eval env input_var.1[i.val]).val < 2 ^ B := by
    intro i; rw [show Expression.eval env input_var.1[i.val] = input.1[i.val] from by
      rw [← h_input]; simp only [Vector.getElem_map]]; exact ha_norm i
  have hb_lt : ∀ i : Fin m, (Expression.eval env input_var.2.1[i.val]).val < 2 ^ B := by
    intro i; rw [show Expression.eval env input_var.2.1[i.val] = input.2.1[i.val] from by
      rw [← h_input]; simp only [Vector.getElem_map]]; exact hb_norm i
  have hn_lt : ∀ i : Fin m, (Expression.eval env input_var.2.2[i.val]).val < 2 ^ B := by
    intro i; rw [show Expression.eval env input_var.2.2[i.val] = input.2.2[i.val] from by
      rw [← h_input]; simp only [Vector.getElem_map]]; exact hn_norm i
  have hqd_lt : ∀ i : Fin m, (Expression.eval env qVar[i.val]).val < 2 ^ B := by
    intro i; have := hq_norm i; rwa [hqv, Fin.getElem_fin, Vector.getElem_map] at this
  have hrd_lt : ∀ j : ℕ, j < m → (Expression.eval env (var (F := F p) { index := i₀ + m + j })).val < 2 ^ B := by
    intro j hj; have := hr_norm ⟨j, hj⟩
    rwa [hrv, Fin.getElem_fin, Vector.getElem_map, hrVar,
      show (Vector.mapRange m fun i ↦ var (F := F p) { index := i₀ + m + i })[j]
        = var (F := F p) { index := i₀ + m + j } from by simp [circuit_norm]] at this
  -- field-overflow bound for Cauchy
  have hfield : m * (2 ^ B * 2 ^ B) < p := by
    have h1 : m * (2 ^ B * 2 ^ B) = m * 2 ^ (2 * B) := by rw [two_mul, pow_add]
    rw [h1]
    have h2 : m * 2 ^ (2 * B) ≤ 2 ^ (2 * B) * (m + 1) * 4 := by nlinarith [Nat.two_pow_pos (2 * B)]
    omega
  -- the `S` vector in the goal is exactly `sVec qVar input_var.2.2 (i₀ + m)`
  have hS_eq : (Vector.mapFinRange (2 * m - 1) fun k ↦
        if h : k.val < m then (bigIntMulNoReduce qVar input_var.2.2)[k.val] + var { index := i₀ + m + k.val }
        else (bigIntMulNoReduce qVar input_var.2.2)[k.val])
      = sVec qVar input_var.2.2 (i₀ + m) := by
    rfl
  -- discharge EqViaCarries assumptions, get polyValue P = polyValue S
  have h_polyeq := h_eq_impl ⟨fun k => coeff_P_bound env input_var.1 input_var.2.1 k ha_lt hb_lt hfield,
    fun k => by
      have hb := coeff_S_bound env qVar input_var.2.2 (i₀ + m) k hqd_lt hn_lt hrd_lt hfield
      rw [sVec, Vector.getElem_mapFinRange] at hb
      exact hb⟩
  rw [hS_eq] at h_polyeq
  -- Cauchy: polyValue P = a.value * b.value
  have hP : polyValue B (Vector.map (Expression.eval env) (bigIntMulNoReduce input_var.1 input_var.2.1))
      = BigInt.value B input.1 * BigInt.value B input.2.1 := by
    rw [polyValue_mul_eq env input_var.1 input_var.2.1 ha_lt hb_lt hfield, ← h_input]
  -- split S: polyValue S = polyValue Sqn + r.value
  have hSplit := polyValue_sVec_split (B := B) env qVar input_var.2.2 (i₀ + m)
    (fun k hk => by
      have h1 := val_bigIntMulNoReduce_coeff_lt env qVar input_var.2.2 k hqd_lt hn_lt hfield
      have h2 := hrd_lt k.val hk
      have hpow : (2 : ℕ) ^ B ≤ 2 ^ (2 * B) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h3 : m * 2 ^ (2 * B) + 2 ^ (2 * B) ≤ 2 ^ (2 * B) * (m + 1) * 4 := by nlinarith [Nat.two_pow_pos (2 * B)]
      omega)
  -- polyValue Sqn = q.value * n.value
  have hSqn : polyValue B (Vector.map (Expression.eval env) (bigIntMulNoReduce qVar input_var.2.2))
      = BigInt.value B qv * BigInt.value B input.2.2 := by
    rw [polyValue_Sqn_eq env qVar input_var.2.2 hqd_lt hn_lt hfield, ← h_input]
  -- r.value of the rVar vector is rv
  have hrval : BigInt.value B (Vector.map (Expression.eval env)
      (Vector.mapRange m fun i => var (F := F p) { index := i₀ + m + i })) = BigInt.value B rv := by
    rw [hrv, hrVar]
  -- combine: a.value * b.value = q.value * n.value + r.value
  rw [hP] at h_polyeq
  rw [hSplit, hSqn, hrval] at h_polyeq
  -- r.value < n.value from LessThan
  have hn_eq : BigInt.value B (Vector.map (Expression.eval env) input_var.2.2) = BigInt.value B input.2.2 := by
    rw [← h_input]
  have hn_norm' : BigInt.Normalized B (Vector.map (Expression.eval env) input_var.2.2) := by
    rw [show (Vector.map (Expression.eval env) input_var.2.2) = input.2.2 from by rw [← h_input]]
    exact hn_norm
  have hr_lt_n : BigInt.value B rv < BigInt.value B input.2.2 := by
    have := h_lt_impl ⟨hr_norm, hn_norm'⟩
    rwa [hn_eq] at this
  -- conclude
  refine ⟨hr_norm, ?_⟩
  exact remainder_eq h_polyeq hr_lt_n


lemma mulMod_soundness_core_wm {B : ℕ} (hp : 2 ^ (2 * B) * (m + 1) * 4 < p)
    (i₀ : ℕ) (env : Environment (F p))
    (a b n : Var (BigInt m) (F p))
    (Pv Qv : Vector (Expression (F p)) (2 * m - 1))
    (input : ProvablePair (BigInt m) (ProvablePair (BigInt m) (BigInt m)) (F p))
    (h_input : (Vector.map (Expression.eval env) a,
        Vector.map (Expression.eval env) b,
        Vector.map (Expression.eval env) n) = input)
    (ha_norm : BigInt.Normalized B input.1) (hb_norm : BigInt.Normalized B input.2.1)
    (hn_norm : BigInt.Normalized B input.2.2)
    (hq_norm : BigInt.Normalized B (Vector.map (Expression.eval env)
        (Vector.mapRange m fun i ↦ var { index := i₀ + i })))
    (hr_norm : BigInt.Normalized B (Vector.map (Expression.eval env)
        (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })))
    (heqAB_get : ∀ k : Fin (2 * m - 1),
      Expression.eval env Pv[k.val] = Expression.eval env (bigIntMulNoReduce a b)[k.val])
    (heqQN_get : ∀ k : Fin (2 * m - 1),
      Expression.eval env Qv[k.val]
        = Expression.eval env (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n)[k.val])
    (h_eq_impl :
      ((∀ k : Fin (2 * m - 1), (Expression.eval env Pv[k.val]).val < (m + 1) * 2 ^ (2 * B)) ∧
        ∀ k : Fin (2 * m - 1),
          (Expression.eval env
            (if h : k.val < m then Qv[k.val] + var { index := i₀ + m + k.val } else Qv[k.val])).val
            < (m + 1) * 2 ^ (2 * B)) →
        polyValue B (Vector.map (Expression.eval env) Pv) =
          polyValue B (Vector.map (Expression.eval env)
            (Vector.mapFinRange (2 * m - 1) fun k ↦
              if h : k.val < m then Qv[k.val] + var { index := i₀ + m + k.val } else Qv[k.val])))
    (h_lt_impl :
      BigInt.Normalized B (Vector.map (Expression.eval env)
          (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })) ∧
        BigInt.Normalized B (Vector.map (Expression.eval env) n) →
        BigInt.value B (Vector.map (Expression.eval env)
            (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })) <
          BigInt.value B (Vector.map (Expression.eval env) n)) :
    BigInt.Normalized B (Vector.map (Expression.eval env)
        (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })) ∧
      BigInt.value B (Vector.map (Expression.eval env)
          (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })) =
        BigInt.value B input.1 * BigInt.value B input.2.1 % BigInt.value B input.2.2 := by
  -- convert the implication to the schoolbook form via the eval bridges
  have h_eq_impl' := eqImpl_bridge (rOff := i₀ + m) env Pv (bigIntMulNoReduce a b)
    Qv (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n)
    heqAB_get heqQN_get h_eq_impl
  -- assemble the schoolbook triple and feed the schoolbook core
  exact mulMod_soundness_core (B := B) hp i₀ env (a, b, n) input h_input
    ha_norm hb_norm hn_norm hq_norm hr_norm h_eq_impl' h_lt_impl

omit [NeZero m] in

lemma normalized_mapRange {B : ℕ} (off N : ℕ) (env : Environment (F p))
    (hB : 2 ^ B < p)
    (hwit : ∀ i : Fin m, env.get (off + i.val) = ((N / 2 ^ (B * i.val) % 2 ^ B : ℕ) : F p)) :
    BigInt.Normalized B (Vector.map (Expression.eval env)
      (Vector.mapRange m fun i => var (F := F p) { index := off + i })) := by
  intro i
  have hget : (Vector.map (Expression.eval env)
      (Vector.mapRange m fun j => var (F := F p) { index := off + j }))[i.val] = env.get (off + i.val) := by
    simp [circuit_norm]
  rw [Fin.getElem_fin, hget, hwit i, ZMod.val_natCast_of_lt
    (lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos B)) (le_of_lt hB))]
  exact Nat.mod_lt _ (Nat.two_pow_pos B)


lemma mulMod_completeness_core {B : ℕ} (hB : 2 ^ B < p)
    (hp : 2 ^ (2 * B) * (m + 1) * 4 < p)
    (i₀ : ℕ) (env : Environment (F p))
    (input_var : ProvablePair (BigInt m) (ProvablePair (BigInt m) (BigInt m)) (Expression (F p)))
    (input : ProvablePair (BigInt m) (ProvablePair (BigInt m) (BigInt m)) (F p))
    (h_input : (Vector.map (Expression.eval env) input_var.1,
        Vector.map (Expression.eval env) input_var.2.1,
        Vector.map (Expression.eval env) input_var.2.2) = input)
    (ha_norm : BigInt.Normalized B input.1) (hb_norm : BigInt.Normalized B input.2.1)
    (hn_norm : BigInt.Normalized B input.2.2)
    (hab_lt : BigInt.value B input.1 < BigInt.value B input.2.2)
    (hbb_lt : BigInt.value B input.2.1 < BigInt.value B input.2.2)
    (hn_pos : 0 < BigInt.value B input.2.2)
    (hqwit : ∀ i : Fin m, env.get (i₀ + i.val)
      = ((BigInt.value B input.1 * BigInt.value B input.2.1 / BigInt.value B input.2.2
          / 2 ^ (B * i.val) % 2 ^ B : ℕ) : F p))
    (hrwit : ∀ i : Fin m, env.get (i₀ + m + i.val)
      = ((BigInt.value B input.1 * BigInt.value B input.2.1 % BigInt.value B input.2.2
          / 2 ^ (B * i.val) % 2 ^ B : ℕ) : F p)) :
    BigInt.Normalized B (Vector.map (Expression.eval env)
        (Vector.mapRange m fun i ↦ var { index := i₀ + i })) ∧
      BigInt.Normalized B (Vector.map (Expression.eval env)
          (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })) ∧
        (((∀ k : Fin (2 * m - 1),
                (Expression.eval env (bigIntMulNoReduce input_var.1 input_var.2.1)[k.val]).val
                  < (m + 1) * 2 ^ (2 * B)) ∧
              ∀ k : Fin (2 * m - 1),
                (Expression.eval env
                  (if h : k.val < m then
                    (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2)[k.val] +
                      var { index := i₀ + m + k.val }
                  else (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2)[k.val])).val
                  < (m + 1) * 2 ^ (2 * B)) ∧
            polyValue B (Vector.map (Expression.eval env) (bigIntMulNoReduce input_var.1 input_var.2.1)) =
              polyValue B
                (Vector.map (Expression.eval env)
                  (Vector.mapFinRange (2 * m - 1) fun k ↦
                    if h : k.val < m then
                      (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2)[k.val] +
                        var { index := i₀ + m + k.val }
                    else (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2)[k.val]))) ∧
          (BigInt.Normalized B (Vector.map (Expression.eval env)
                (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })) ∧
              BigInt.Normalized B (Vector.map (Expression.eval env) input_var.2.2)) ∧
            BigInt.value B (Vector.map (Expression.eval env)
                (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })) <
              BigInt.value B (Vector.map (Expression.eval env) input_var.2.2) := by
  -- abbreviations for the two witness values
  set a := BigInt.value B input.1 with ha_def
  set b := BigInt.value B input.2.1 with hb_def
  set n := BigInt.value B input.2.2 with hn_def
  set qval := a * b / n with hqval_def
  set rval := a * b % n with hrval_def
  -- the witness-evaluated inputs are the input components
  have hmap_a : BigInt.value B (Vector.map (Expression.eval env) input_var.1) = a := by
    rw [ha_def, ← h_input]
  have hmap_b : BigInt.value B (Vector.map (Expression.eval env) input_var.2.1) = b := by
    rw [hb_def, ← h_input]
  have hmap_n : BigInt.value B (Vector.map (Expression.eval env) input_var.2.2) = n := by
    rw [hn_def, ← h_input]
  have hmap_n_norm : BigInt.Normalized B (Vector.map (Expression.eval env) input_var.2.2) := by
    rw [show (Vector.map (Expression.eval env) input_var.2.2) = input.2.2 from by rw [← h_input]]
    exact hn_norm
  -- n is positive and bounded by 2^(B*m)
  have hn_lt : n < 2 ^ (B * m) := BigInt.value_lt hn_norm
  -- q = a*b/n < n  (since a < n, b < n ⇒ a*b < n*n)
  have hq_lt_n : qval < n := by
    rw [hqval_def]
    apply Nat.div_lt_of_lt_mul
    have hab : a * b < n * n := by
      rcases Nat.eq_zero_or_pos b with hb0 | hb0
      · rw [hb0, Nat.mul_zero]; exact Nat.mul_pos hn_pos hn_pos
      · calc a * b < n * b := by
              apply (Nat.mul_lt_mul_right hb0).mpr hab_lt
          _ ≤ n * n := by apply Nat.mul_le_mul_left; omega
    omega
  have hqval_lt : qval < 2 ^ (B * m) := lt_trans hq_lt_n hn_lt
  have hrval_lt : rval < 2 ^ (B * m) := lt_trans (Nat.mod_lt _ hn_pos) hn_lt
  -- values of the witness vectors
  have hqv_val : BigInt.value B (Vector.map (Expression.eval env)
      (Vector.mapRange m fun i ↦ var { index := i₀ + i })) = qval :=
    BigInt.value_mapRange i₀ qval env hB hqval_lt (by intro i; rw [hqwit i])
  have hrv_val : BigInt.value B (Vector.map (Expression.eval env)
      (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })) = rval :=
    BigInt.value_mapRange (i₀ + m) rval env hB hrval_lt (by intro i; rw [hrwit i])
  -- normalizations of the witness vectors
  have hqv_norm : BigInt.Normalized B (Vector.map (Expression.eval env)
      (Vector.mapRange m fun i ↦ var { index := i₀ + i })) :=
    normalized_mapRange i₀ qval env hB (by intro i; rw [hqwit i])
  have hrv_norm : BigInt.Normalized B (Vector.map (Expression.eval env)
      (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })) :=
    normalized_mapRange (i₀ + m) rval env hB (by intro i; rw [hrwit i])
  -- digit bounds (for Cauchy / coefficient bounds)
  have ha_lt : ∀ i : Fin m, (Expression.eval env input_var.1[i.val]).val < 2 ^ B := by
    intro i; rw [show Expression.eval env input_var.1[i.val] = input.1[i.val] from by
      rw [← h_input]; simp only [Vector.getElem_map]]; exact ha_norm i
  have hb_lt : ∀ i : Fin m, (Expression.eval env input_var.2.1[i.val]).val < 2 ^ B := by
    intro i; rw [show Expression.eval env input_var.2.1[i.val] = input.2.1[i.val] from by
      rw [← h_input]; simp only [Vector.getElem_map]]; exact hb_norm i
  have hn_lt' : ∀ i : Fin m, (Expression.eval env input_var.2.2[i.val]).val < 2 ^ B := by
    intro i; rw [show Expression.eval env input_var.2.2[i.val] = input.2.2[i.val] from by
      rw [← h_input]; simp only [Vector.getElem_map]]; exact hn_norm i
  have hqd_lt : ∀ i : Fin m, (Expression.eval env (Vector.mapRange m fun j ↦ var (F := F p) { index := i₀ + j })[i.val]).val < 2 ^ B := by
    intro i; have := hqv_norm i; rwa [Fin.getElem_fin, Vector.getElem_map] at this
  have hrd_lt : ∀ j : ℕ, j < m → (Expression.eval env (var (F := F p) { index := i₀ + m + j })).val < 2 ^ B := by
    intro j hj; have := hrv_norm ⟨j, hj⟩
    rwa [Fin.getElem_fin, Vector.getElem_map,
      show (Vector.mapRange m fun i ↦ var (F := F p) { index := i₀ + m + i })[j]
        = var (F := F p) { index := i₀ + m + j } from by simp [circuit_norm]] at this
  -- field-overflow bound for Cauchy
  have hfield : m * (2 ^ B * 2 ^ B) < p := by
    have h1 : m * (2 ^ B * 2 ^ B) = m * 2 ^ (2 * B) := by rw [two_mul, pow_add]
    rw [h1]
    have h2 : m * 2 ^ (2 * B) ≤ 2 ^ (2 * B) * (m + 1) * 4 := by nlinarith [Nat.two_pow_pos (2 * B)]
    omega
  -- the `S` vector is exactly `sVec qVar input_var.2.2 (i₀ + m)`
  have hS_eq : (Vector.mapFinRange (2 * m - 1) fun k ↦
        if h : k.val < m then (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2)[k.val]
          + var { index := i₀ + m + k.val }
        else (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2)[k.val])
      = sVec (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2 (i₀ + m) := rfl
  -- polyValue P = a * b
  have hP : polyValue B (Vector.map (Expression.eval env) (bigIntMulNoReduce input_var.1 input_var.2.1))
      = a * b := by
    rw [polyValue_mul_eq env input_var.1 input_var.2.1 ha_lt hb_lt hfield, hmap_a, hmap_b]
  -- polyValue S = qval * n + rval = a * b
  have hSplit := polyValue_sVec_split (B := B) env (Vector.mapRange m fun i ↦ var { index := i₀ + i })
    input_var.2.2 (i₀ + m)
    (fun k hk => by
      have h1 := val_bigIntMulNoReduce_coeff_lt env (Vector.mapRange m fun i ↦ var { index := i₀ + i })
        input_var.2.2 k hqd_lt hn_lt' hfield
      have h2 := hrd_lt k.val hk
      have hpow : (2 : ℕ) ^ B ≤ 2 ^ (2 * B) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h3 : m * 2 ^ (2 * B) + 2 ^ (2 * B) ≤ 2 ^ (2 * B) * (m + 1) * 4 := by nlinarith [Nat.two_pow_pos (2 * B)]
      omega)
  have hSqn : polyValue B (Vector.map (Expression.eval env)
      (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2))
      = qval * n := by
    rw [polyValue_Sqn_eq env (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2 hqd_lt hn_lt' hfield,
      hqv_val, hmap_n]
  have hpolyS : polyValue B (Vector.map (Expression.eval env)
      (Vector.mapFinRange (2 * m - 1) fun k ↦
        if h : k.val < m then (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2)[k.val]
          + var { index := i₀ + m + k.val }
        else (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2)[k.val]))
      = a * b := by
    rw [hS_eq, hSplit, hSqn, hrv_val, hqval_def, hrval_def, Nat.div_add_mod']
  -- assemble
  refine ⟨hqv_norm, hrv_norm, ⟨⟨?_, ?_⟩, ?_⟩, ⟨hrv_norm, ?_⟩, ?_⟩
  · intro k; exact coeff_P_bound env input_var.1 input_var.2.1 k ha_lt hb_lt hfield
  · intro k
    have hb := coeff_S_bound env (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2 (i₀ + m) k
      hqd_lt hn_lt' hrd_lt hfield
    rw [sVec, Vector.getElem_mapFinRange] at hb
    exact hb
  · rw [hP, hpolyS]
  · exact hmap_n_norm
  · rw [hrv_val, hmap_n, hrval_def]
    exact Nat.mod_lt _ hn_pos


lemma mulMod_completeness_core_wm {B : ℕ} (hB : 2 ^ B < p)
    (hp : 2 ^ (2 * B) * (m + 1) * 4 < p)
    (i₀ : ℕ) (env : Environment (F p))
    (a b n : Var (BigInt m) (F p))
    (Pv Qv : Vector (Expression (F p)) (2 * m - 1))
    (input : ProvablePair (BigInt m) (ProvablePair (BigInt m) (BigInt m)) (F p))
    (h_input : (Vector.map (Expression.eval env) a,
        Vector.map (Expression.eval env) b,
        Vector.map (Expression.eval env) n) = input)
    (ha_norm : BigInt.Normalized B input.1) (hb_norm : BigInt.Normalized B input.2.1)
    (hn_norm : BigInt.Normalized B input.2.2)
    (hab_lt : BigInt.value B input.1 < BigInt.value B input.2.2)
    (hbb_lt : BigInt.value B input.2.1 < BigInt.value B input.2.2)
    (hn_pos : 0 < BigInt.value B input.2.2)
    (hqwit : ∀ i : Fin m, env.get (i₀ + i.val)
      = ((BigInt.value B input.1 * BigInt.value B input.2.1 / BigInt.value B input.2.2
          / 2 ^ (B * i.val) % 2 ^ B : ℕ) : F p))
    (hrwit : ∀ i : Fin m, env.get (i₀ + m + i.val)
      = ((BigInt.value B input.1 * BigInt.value B input.2.1 % BigInt.value B input.2.2
          / 2 ^ (B * i.val) % 2 ^ B : ℕ) : F p))
    (heqAB_get : ∀ k : Fin (2 * m - 1),
      Expression.eval env Pv[k.val] = Expression.eval env (bigIntMulNoReduce a b)[k.val])
    (heqQN_get : ∀ k : Fin (2 * m - 1),
      Expression.eval env Qv[k.val]
        = Expression.eval env (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n)[k.val]) :
    BigInt.Normalized B (Vector.map (Expression.eval env)
        (Vector.mapRange m fun i ↦ var { index := i₀ + i })) ∧
      BigInt.Normalized B (Vector.map (Expression.eval env)
          (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })) ∧
        (((∀ k : Fin (2 * m - 1), (Expression.eval env Pv[k.val]).val < (m + 1) * 2 ^ (2 * B)) ∧
            (∀ k : Fin (2 * m - 1),
              (Expression.eval env
                (if h : k.val < m then Qv[k.val] + var { index := i₀ + m + k.val } else Qv[k.val])).val
                < (m + 1) * 2 ^ (2 * B))) ∧
            polyValue B (Vector.map (Expression.eval env) Pv) =
              polyValue B (Vector.map (Expression.eval env)
                (Vector.mapFinRange (2 * m - 1) fun k ↦
                  if h : k.val < m then Qv[k.val] + var { index := i₀ + m + k.val } else Qv[k.val]))) ∧
          (BigInt.Normalized B (Vector.map (Expression.eval env)
                (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })) ∧
              BigInt.Normalized B (Vector.map (Expression.eval env) n)) ∧
            BigInt.value B (Vector.map (Expression.eval env)
                (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })) <
              BigInt.value B (Vector.map (Expression.eval env) n) := by
  obtain ⟨hqn, hrn, hconj, hlt⟩ :=
    mulMod_completeness_core (B := B) hB hp i₀ env (a, b, n) input h_input
      ha_norm hb_norm hn_norm hab_lt hbb_lt hn_pos hqwit hrwit
  exact ⟨hqn, hrn,
    eqConj_bridge (rOff := i₀ + m) env Pv (bigIntMulNoReduce a b) Qv
      (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n)
      heqAB_get heqQN_get hconj, hlt⟩




def sVecT (q n t : Var (BigInt m) (F p)) :
    Vector (Expression (F p)) (2 * m - 1) :=
  Vector.mapFinRange (2 * m - 1) fun k =>
    if h : k.val < m then (bigIntMulNoReduce q n)[k.val] + t[k.val]'h
    else (bigIntMulNoReduce q n)[k.val]


lemma polyValue_sVecT_split {B : ℕ} (env : Environment (F p))
    (q n t : Var (BigInt m) (F p))
    (hnowrap : ∀ k : Fin (2 * m - 1), (hk : k.val < m) →
      (Expression.eval env ((bigIntMulNoReduce q n)[k.val])).val
        + (Expression.eval env (t[k.val]'hk)).val < p) :
    polyValue B (Vector.map (Expression.eval env) (sVecT q n t))
      = polyValue B (Vector.map (Expression.eval env) (bigIntMulNoReduce q n))
        + BigInt.value B (Vector.map (Expression.eval env) t) := by
  rw [polyValue, polyValue, value_map_eval]
  have hS : ∀ k : Fin (2 * m - 1),
      (Vector.map (Expression.eval env) (sVecT q n t))[k.val].val
        = (Expression.eval env ((bigIntMulNoReduce q n)[k.val])).val
          + (if hk : k.val < m then (Expression.eval env (t[k.val]'hk)).val else 0) := by
    intro k
    rw [Vector.getElem_map]
    simp only [sVecT, Vector.getElem_mapFinRange]
    by_cases hk : k.val < m
    · simp only [dif_pos hk]
      rw [show Expression.eval env ((bigIntMulNoReduce q n)[k.val] + t[k.val]'hk)
            = Expression.eval env ((bigIntMulNoReduce q n)[k.val])
              + Expression.eval env (t[k.val]'hk) from rfl,
        ZMod.val_add_of_lt (hnowrap k hk)]
    · simp only [dif_neg hk, Nat.add_zero]
  simp only [hS]
  rw [show (∑ k : Fin (2 * m - 1),
        ((Expression.eval env ((bigIntMulNoReduce q n)[k.val])).val
          + (if hk : k.val < m then (Expression.eval env (t[k.val]'hk)).val else 0))
          * 2 ^ (B * k.val))
      = (∑ k : Fin (2 * m - 1),
          (Expression.eval env ((bigIntMulNoReduce q n)[k.val])).val * 2 ^ (B * k.val))
        + (∑ k : Fin (2 * m - 1),
          (if hk : k.val < m then (Expression.eval env (t[k.val]'hk)).val else 0)
            * 2 ^ (B * k.val)) from by
    rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro k _; ring]
  congr 1
  · apply Finset.sum_congr rfl; intro k _; rw [Vector.getElem_map]
  · -- the guarded tail sum collapses to the `Fin m` value sum of `t`
    set tval : ℕ → ℕ := fun j => if hj : j < m then (Expression.eval env (t[j]'hj)).val else 0
      with htval
    have hguard : ∀ k : Fin (2 * m - 1),
        (if hk : k.val < m then (Expression.eval env (t[k.val]'hk)).val else 0) = tval k.val := by
      intro k; simp only [htval]
    simp only [hguard]
    rw [Fin.sum_univ_eq_sum_range (fun k => tval k * 2 ^ (B * k))]
    have hRHS : (∑ k : Fin m, (Expression.eval env t[k.val]).val * 2 ^ (B * k.val))
        = ∑ k ∈ Finset.range m, tval k * 2 ^ (B * k) := by
      rw [← Fin.sum_univ_eq_sum_range (fun k => tval k * 2 ^ (B * k))]
      apply Finset.sum_congr rfl; intro k _
      congr 1
      simp only [htval, dif_pos k.isLt]
    rw [hRHS]
    refine (Finset.sum_subset
      (Finset.range_subset_range.mpr (by have := Nat.pos_of_neZero m; omega : m ≤ 2 * m - 1))
      (fun k _ hk => ?_)).symm
    rw [Finset.mem_range] at hk
    simp only [htval, dif_neg hk, Nat.zero_mul]


lemma coeff_S_boundT {B : ℕ} (env : Environment (F p))
    (q n t : Var (BigInt m) (F p)) (k : Fin (2 * m - 1))
    (hq : ∀ i : Fin m, (Expression.eval env q[i.val]).val < 2 ^ B)
    (hn : ∀ i : Fin m, (Expression.eval env n[i.val]).val < 2 ^ B)
    (ht : ∀ j : ℕ, (hj : j < m) → (Expression.eval env (t[j]'hj)).val < 2 ^ B)
    (hfield : m * (2 ^ B * 2 ^ B) < p) :
    (Expression.eval env ((sVecT q n t)[k.val])).val < (m + 1) * 2 ^ (2 * B) := by
  have hSqn := val_bigIntMulNoReduce_coeff_lt env q n k hq hn hfield
  have hpow : (2 : ℕ) ^ B ≤ 2 ^ (2 * B) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hmm : (m + 1) * 2 ^ (2 * B) = m * 2 ^ (2 * B) + 2 ^ (2 * B) := by ring
  rw [hmm]
  generalize hX : 2 ^ (2 * B) = X at *
  generalize hY : m * X = Y at *
  simp only [sVecT, Vector.getElem_mapFinRange]
  by_cases hk : k.val < m
  · rw [dif_pos hk]
    have ht' := ht k.val hk
    have hadd : (Expression.eval env ((bigIntMulNoReduce q n)[k.val])
        + Expression.eval env (t[k.val]'hk)).val
        ≤ (Expression.eval env ((bigIntMulNoReduce q n)[k.val])).val
          + (Expression.eval env (t[k.val]'hk)).val := ZMod.val_add_le _ _
    rw [show Expression.eval env ((bigIntMulNoReduce q n)[k.val] + t[k.val]'hk)
          = Expression.eval env ((bigIntMulNoReduce q n)[k.val])
            + Expression.eval env (t[k.val]'hk) from rfl]
    omega
  · rw [dif_neg hk]
    omega


lemma mulModTarget_soundness_core_wm {B : ℕ} (hp : 2 ^ (2 * B) * (m + 1) * 4 < p)
    (i₀ : ℕ) (env : Environment (F p))
    (a b n t : Var (BigInt m) (F p))
    (Pv : Vector (Expression (F p)) (2 * m - 1))
    (av bv nv tv : BigInt m (F p))
    (ha_input : Vector.map (Expression.eval env) a = av)
    (hb_input : Vector.map (Expression.eval env) b = bv)
    (hn_input : Vector.map (Expression.eval env) n = nv)
    (ht_input : Vector.map (Expression.eval env) t = tv)
    (ha_norm : BigInt.Normalized B av) (hb_norm : BigInt.Normalized B bv)
    (hn_norm : BigInt.Normalized B nv) (ht_norm : BigInt.Normalized B tv)
    (ht_lt : BigInt.value B tv < BigInt.value B nv)
    (hq_norm : BigInt.Normalized B (Vector.map (Expression.eval env)
        (Vector.mapRange m fun i ↦ var { index := i₀ + i })))
    (heqAB_get : ∀ k : Fin (2 * m - 1),
      Expression.eval env Pv[k.val] = Expression.eval env (bigIntMulNoReduce a b)[k.val])
    (h_eq_impl :
      ((∀ k : Fin (2 * m - 1), (Expression.eval env Pv[k.val]).val < (m + 1) * 2 ^ (2 * B)) ∧
        ∀ k : Fin (2 * m - 1),
          (Expression.eval env
            (if h : k.val < m then
              (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n)[k.val]
                + t[k.val]'h
            else (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n)[k.val])).val
            < (m + 1) * 2 ^ (2 * B)) →
        polyValue B (Vector.map (Expression.eval env) Pv) =
          polyValue B (Vector.map (Expression.eval env)
            (Vector.mapFinRange (2 * m - 1) fun k ↦
              if h : k.val < m then
                (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n)[k.val]
                  + t[k.val]'h
              else (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n)[k.val]))) :
    BigInt.value B tv = BigInt.value B av * BigInt.value B bv % BigInt.value B nv := by
  set qVar := (Vector.mapRange m fun i ↦ var (F := F p) { index := i₀ + i }) with hqVar
  set qv := (Vector.map (Expression.eval env) qVar : BigInt m (F p)) with hqv
  -- digit bounds
  have ha_lt : ∀ i : Fin m, (Expression.eval env a[i.val]).val < 2 ^ B := by
    intro i; rw [show Expression.eval env a[i.val] = av[i.val] from by
      rw [← ha_input]; simp only [Vector.getElem_map]]; exact ha_norm i
  have hb_lt : ∀ i : Fin m, (Expression.eval env b[i.val]).val < 2 ^ B := by
    intro i; rw [show Expression.eval env b[i.val] = bv[i.val] from by
      rw [← hb_input]; simp only [Vector.getElem_map]]; exact hb_norm i
  have hn_lt : ∀ i : Fin m, (Expression.eval env n[i.val]).val < 2 ^ B := by
    intro i; rw [show Expression.eval env n[i.val] = nv[i.val] from by
      rw [← hn_input]; simp only [Vector.getElem_map]]; exact hn_norm i
  have hqd_lt : ∀ i : Fin m, (Expression.eval env qVar[i.val]).val < 2 ^ B := by
    intro i; have := hq_norm i; rwa [hqv, Fin.getElem_fin, Vector.getElem_map] at this
  have htd_lt : ∀ j : ℕ, (hj : j < m) → (Expression.eval env (t[j]'hj)).val < 2 ^ B := by
    intro j hj
    have := ht_norm ⟨j, hj⟩
    rwa [Fin.getElem_fin,
      show tv[j]'hj = (Vector.map (Expression.eval env) t)[j]'hj from by rw [ht_input],
      Vector.getElem_map] at this
  have hfield : m * (2 ^ B * 2 ^ B) < p := by
    have h1 : m * (2 ^ B * 2 ^ B) = m * 2 ^ (2 * B) := by rw [two_mul, pow_add]
    rw [h1]
    have h2 : m * 2 ^ (2 * B) ≤ 2 ^ (2 * B) * (m + 1) * 4 := by nlinarith [Nat.two_pow_pos (2 * B)]
    omega
  -- the `S` vector in the implication is exactly `sVecT qVar n t`
  have hS_eq : (Vector.mapFinRange (2 * m - 1) fun k ↦
        if h : k.val < m then (bigIntMulNoReduce qVar n)[k.val] + t[k.val]'h
        else (bigIntMulNoReduce qVar n)[k.val])
      = sVecT qVar n t := rfl
  -- discharge the coefficient bounds, get the polyValue equality
  have h_polyeq := h_eq_impl ⟨fun k => by
      rw [show Expression.eval env Pv[k.val]
            = Expression.eval env (bigIntMulNoReduce a b)[k.val] from heqAB_get k]
      exact coeff_P_bound env a b k ha_lt hb_lt hfield,
    fun k => by
      have hb' := coeff_S_boundT env qVar n t k hqd_lt hn_lt htd_lt hfield
      rw [sVecT, Vector.getElem_mapFinRange] at hb'
      exact hb'⟩
  rw [hS_eq] at h_polyeq
  -- rewrite the abstract lhs through the eval bridge
  have hPv_map : Vector.map (Expression.eval env) Pv
      = Vector.map (Expression.eval env) (bigIntMulNoReduce a b) := by
    apply Vector.ext; intro k hk
    rw [Vector.getElem_map, Vector.getElem_map]
    exact heqAB_get ⟨k, hk⟩
  rw [hPv_map] at h_polyeq
  -- Cauchy: polyValue P = a.value * b.value
  have hP : polyValue B (Vector.map (Expression.eval env) (bigIntMulNoReduce a b))
      = BigInt.value B av * BigInt.value B bv := by
    rw [polyValue_mul_eq env a b ha_lt hb_lt hfield, ha_input, hb_input]
  -- split S: polyValue S = polyValue Sqn + t.value
  have hSplit := polyValue_sVecT_split (B := B) env qVar n t
    (fun k hk => by
      have h1 := val_bigIntMulNoReduce_coeff_lt env qVar n k hqd_lt hn_lt hfield
      have h2 := htd_lt k.val hk
      have hpow : (2 : ℕ) ^ B ≤ 2 ^ (2 * B) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h3 : m * 2 ^ (2 * B) + 2 ^ (2 * B) ≤ 2 ^ (2 * B) * (m + 1) * 4 := by
        nlinarith [Nat.two_pow_pos (2 * B)]
      omega)
  -- polyValue Sqn = q.value * n.value
  have hSqn : polyValue B (Vector.map (Expression.eval env) (bigIntMulNoReduce qVar n))
      = BigInt.value B qv * BigInt.value B nv := by
    rw [polyValue_Sqn_eq env qVar n hqd_lt hn_lt hfield, ← hn_input]
  -- combine: a.value * b.value = q.value * n.value + t.value
  rw [hP] at h_polyeq
  rw [hSplit, hSqn, ht_input] at h_polyeq
  -- conclude via remainder uniqueness
  exact remainder_eq h_polyeq ht_lt


lemma mulModTarget_completeness_core_wm {B : ℕ} (hB : 2 ^ B < p)
    (hp : 2 ^ (2 * B) * (m + 1) * 4 < p)
    (i₀ : ℕ) (env : Environment (F p))
    (a b n t : Var (BigInt m) (F p))
    (Pv : Vector (Expression (F p)) (2 * m - 1))
    (av bv nv tv : BigInt m (F p))
    (ha_input : Vector.map (Expression.eval env) a = av)
    (hb_input : Vector.map (Expression.eval env) b = bv)
    (hn_input : Vector.map (Expression.eval env) n = nv)
    (ht_input : Vector.map (Expression.eval env) t = tv)
    (ha_norm : BigInt.Normalized B av) (hb_norm : BigInt.Normalized B bv)
    (hn_norm : BigInt.Normalized B nv) (ht_norm : BigInt.Normalized B tv)
    (hab_lt : BigInt.value B av < BigInt.value B nv)
    (hbb_lt : BigInt.value B bv < BigInt.value B nv)
    (hn_pos : 0 < BigInt.value B nv)
    (ht_spec : BigInt.value B tv = BigInt.value B av * BigInt.value B bv % BigInt.value B nv)
    (hqwit : ∀ i : Fin m, env.get (i₀ + i.val)
      = ((BigInt.value B av * BigInt.value B bv / BigInt.value B nv
          / 2 ^ (B * i.val) % 2 ^ B : ℕ) : F p))
    (heqAB_get : ∀ k : Fin (2 * m - 1),
      Expression.eval env Pv[k.val] = Expression.eval env (bigIntMulNoReduce a b)[k.val]) :
    BigInt.Normalized B (Vector.map (Expression.eval env)
        (Vector.mapRange m fun i ↦ var { index := i₀ + i })) ∧
      ((∀ k : Fin (2 * m - 1), (Expression.eval env Pv[k.val]).val < (m + 1) * 2 ^ (2 * B)) ∧
        ∀ k : Fin (2 * m - 1),
          (Expression.eval env
            (if h : k.val < m then
              (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n)[k.val]
                + t[k.val]'h
            else (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n)[k.val])).val
            < (m + 1) * 2 ^ (2 * B)) ∧
        polyValue B (Vector.map (Expression.eval env) Pv) =
          polyValue B (Vector.map (Expression.eval env)
            (Vector.mapFinRange (2 * m - 1) fun k ↦
              if h : k.val < m then
                (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n)[k.val]
                  + t[k.val]'h
              else (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n)[k.val])) := by
  set aval := BigInt.value B av with ha_def
  set bval := BigInt.value B bv with hb_def
  set nval := BigInt.value B nv with hn_def
  set qval := aval * bval / nval with hqval_def
  -- n bounded, q < n < 2^(Bm)
  have hn_ltpow : nval < 2 ^ (B * m) := BigInt.value_lt hn_norm
  have hq_lt_n : qval < nval := by
    rw [hqval_def]
    apply Nat.div_lt_of_lt_mul
    have hab : aval * bval < nval * nval := by
      rcases Nat.eq_zero_or_pos bval with hb0 | hb0
      · rw [hb0, Nat.mul_zero]; exact Nat.mul_pos hn_pos hn_pos
      · calc aval * bval < nval * bval := by
              apply (Nat.mul_lt_mul_right hb0).mpr hab_lt
          _ ≤ nval * nval := by apply Nat.mul_le_mul_left; omega
    omega
  have hqval_lt : qval < 2 ^ (B * m) := lt_trans hq_lt_n hn_ltpow
  -- q witness vector value / normalization
  have hqv_val : BigInt.value B (Vector.map (Expression.eval env)
      (Vector.mapRange m fun i ↦ var { index := i₀ + i })) = qval :=
    BigInt.value_mapRange i₀ qval env hB hqval_lt (by intro i; rw [hqwit i])
  have hqv_norm : BigInt.Normalized B (Vector.map (Expression.eval env)
      (Vector.mapRange m fun i ↦ var { index := i₀ + i })) :=
    normalized_mapRange i₀ qval env hB (by intro i; rw [hqwit i])
  -- digit bounds
  have ha_lt : ∀ i : Fin m, (Expression.eval env a[i.val]).val < 2 ^ B := by
    intro i; rw [show Expression.eval env a[i.val] = av[i.val] from by
      rw [← ha_input]; simp only [Vector.getElem_map]]; exact ha_norm i
  have hb_lt : ∀ i : Fin m, (Expression.eval env b[i.val]).val < 2 ^ B := by
    intro i; rw [show Expression.eval env b[i.val] = bv[i.val] from by
      rw [← hb_input]; simp only [Vector.getElem_map]]; exact hb_norm i
  have hn_lt' : ∀ i : Fin m, (Expression.eval env n[i.val]).val < 2 ^ B := by
    intro i; rw [show Expression.eval env n[i.val] = nv[i.val] from by
      rw [← hn_input]; simp only [Vector.getElem_map]]; exact hn_norm i
  have hqd_lt : ∀ i : Fin m,
      (Expression.eval env (Vector.mapRange m fun j ↦ var (F := F p) { index := i₀ + j })[i.val]).val < 2 ^ B := by
    intro i; have := hqv_norm i; rwa [Fin.getElem_fin, Vector.getElem_map] at this
  have htd_lt : ∀ j : ℕ, (hj : j < m) → (Expression.eval env (t[j]'hj)).val < 2 ^ B := by
    intro j hj
    have := ht_norm ⟨j, hj⟩
    rwa [Fin.getElem_fin,
      show tv[j]'hj = (Vector.map (Expression.eval env) t)[j]'hj from by rw [ht_input],
      Vector.getElem_map] at this
  have hfield : m * (2 ^ B * 2 ^ B) < p := by
    have h1 : m * (2 ^ B * 2 ^ B) = m * 2 ^ (2 * B) := by rw [two_mul, pow_add]
    rw [h1]
    have h2 : m * 2 ^ (2 * B) ≤ 2 ^ (2 * B) * (m + 1) * 4 := by nlinarith [Nat.two_pow_pos (2 * B)]
    omega
  have hS_eq : (Vector.mapFinRange (2 * m - 1) fun k ↦
        if h : k.val < m then
          (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n)[k.val]
            + t[k.val]'h
        else (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n)[k.val])
      = sVecT (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n t := rfl
  -- the abstract lhs evaluates like the schoolbook convolution
  have hPv_map : Vector.map (Expression.eval env) Pv
      = Vector.map (Expression.eval env) (bigIntMulNoReduce a b) := by
    apply Vector.ext; intro k hk
    rw [Vector.getElem_map, Vector.getElem_map]
    exact heqAB_get ⟨k, hk⟩
  -- polyValue P = a·b
  have hP : polyValue B (Vector.map (Expression.eval env) (bigIntMulNoReduce a b))
      = aval * bval := by
    rw [polyValue_mul_eq env a b ha_lt hb_lt hfield, ha_input, hb_input]
  -- polyValue S = q·n + t.value = a·b
  have hSplit := polyValue_sVecT_split (B := B) env
    (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n t
    (fun k hk => by
      have h1 := val_bigIntMulNoReduce_coeff_lt env
        (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n k hqd_lt hn_lt' hfield
      have h2 := htd_lt k.val hk
      have hpow : (2 : ℕ) ^ B ≤ 2 ^ (2 * B) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h3 : m * 2 ^ (2 * B) + 2 ^ (2 * B) ≤ 2 ^ (2 * B) * (m + 1) * 4 := by
        nlinarith [Nat.two_pow_pos (2 * B)]
      omega)
  have hSqn : polyValue B (Vector.map (Expression.eval env)
      (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n))
      = qval * nval := by
    rw [polyValue_Sqn_eq env (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n
      hqd_lt hn_lt' hfield, hqv_val, hn_input]
  refine ⟨hqv_norm, ⟨fun k => ?_, fun k => ?_⟩, ?_⟩
  · rw [show Expression.eval env Pv[k.val]
        = Expression.eval env (bigIntMulNoReduce a b)[k.val] from heqAB_get k]
    exact coeff_P_bound env a b k ha_lt hb_lt hfield
  · have hb' := coeff_S_boundT env (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n t k
      hqd_lt hn_lt' htd_lt hfield
    rw [sVecT, Vector.getElem_mapFinRange] at hb'
    exact hb'
  · rw [hPv_map, hS_eq, hSplit, hSqn, ht_input, hP, ht_spec, hqval_def]
    exact (Nat.div_add_mod' _ _).symm




def lVecC (Pv : Vector (Expression (F p)) (2 * m - 1)) (c : Vector (F p) (2 * m - 1)) :
    Vector (Expression (F p)) (2 * m - 1) :=
  Vector.mapFinRange (2 * m - 1) fun k => Pv[k.val] + (c[k.val] : Expression (F p))


lemma polyValue_lVecC_split {B : ℕ} (env : Environment (F p))
    (Pv : Vector (Expression (F p)) (2 * m - 1)) (c : Vector (F p) (2 * m - 1))
    (hnowrap : ∀ k : Fin (2 * m - 1),
      (Expression.eval env Pv[k.val]).val + (c[k.val]).val < p) :
    polyValue B (Vector.map (Expression.eval env) (lVecC Pv c))
      = polyValue B (Vector.map (Expression.eval env) Pv) + polyValue B c := by
  rw [polyValue, polyValue, polyValue, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [Vector.getElem_map, Vector.getElem_map]
  simp only [lVecC, Vector.getElem_mapFinRange]
  rw [show Expression.eval env (Pv[k.val] + (c[k.val] : Expression (F p)))
        = Expression.eval env Pv[k.val] + c[k.val] from rfl,
    ZMod.val_add_of_lt (hnowrap k)]
  ring


lemma coeff_L_boundC {B : ℕ} (env : Environment (F p))
    (a b : Var (BigInt m) (F p)) (c : Vector (F p) (2 * m - 1)) (k : Fin (2 * m - 1))
    (ha : ∀ i : Fin m, (Expression.eval env a[i.val]).val < 2 ^ B)
    (hb : ∀ i : Fin m, (Expression.eval env b[i.val]).val < 2 ^ B)
    (hc : ∀ j : Fin (2 * m - 1), (c[j.val]).val < 2 ^ B)
    (hfield : m * (2 ^ B * 2 ^ B) < p) :
    (Expression.eval env ((bigIntMulNoReduce a b)[k.val])).val + (c[k.val]).val
      < (m + 1) * 2 ^ (2 * B) := by
  have hconv := val_bigIntMulNoReduce_coeff_lt env a b k ha hb hfield
  have hck := hc k
  have hpow : (2 : ℕ) ^ B ≤ 2 ^ (2 * B) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hmm : (m + 1) * 2 ^ (2 * B) = m * 2 ^ (2 * B) + 2 ^ (2 * B) := by ring
  omega


lemma coeff_S_boundT3 {B : ℕ} (hB2 : 2 ≤ B) (env : Environment (F p))
    (q n t : Var (BigInt m) (F p)) (k : Fin (2 * m - 1))
    (hq : ∀ i : Fin m, (Expression.eval env q[i.val]).val < 2 ^ B)
    (hn : ∀ i : Fin m, (Expression.eval env n[i.val]).val < 2 ^ B)
    (ht : ∀ j : ℕ, (hj : j < m) → (Expression.eval env (t[j]'hj)).val < 3 * 2 ^ B)
    (hfield : m * (2 ^ B * 2 ^ B) < p) :
    (Expression.eval env ((sVecT q n t)[k.val])).val < (m + 1) * 2 ^ (2 * B) := by
  have hSqn := val_bigIntMulNoReduce_coeff_lt env q n k hq hn hfield
  have h32B : 3 * 2 ^ B ≤ 2 ^ (2 * B) := by
    have h4 : (4 : ℕ) ≤ 2 ^ B := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ B := Nat.pow_le_pow_right (by norm_num) hB2
    calc 3 * 2 ^ B ≤ 2 ^ B * 2 ^ B := by nlinarith [Nat.two_pow_pos B]
      _ = 2 ^ (2 * B) := by rw [two_mul, pow_add]
  have hmm : (m + 1) * 2 ^ (2 * B) = m * 2 ^ (2 * B) + 2 ^ (2 * B) := by ring
  rw [hmm]
  generalize hX : 2 ^ (2 * B) = X at *
  generalize hY : m * X = Y at *
  simp only [sVecT, Vector.getElem_mapFinRange]
  by_cases hk : k.val < m
  · rw [dif_pos hk]
    have ht' := ht k.val hk
    have hadd : (Expression.eval env ((bigIntMulNoReduce q n)[k.val])
        + Expression.eval env (t[k.val]'hk)).val
        ≤ (Expression.eval env ((bigIntMulNoReduce q n)[k.val])).val
          + (Expression.eval env (t[k.val]'hk)).val := ZMod.val_add_le _ _
    rw [show Expression.eval env ((bigIntMulNoReduce q n)[k.val] + t[k.val]'hk)
          = Expression.eval env ((bigIntMulNoReduce q n)[k.val])
            + Expression.eval env (t[k.val]'hk) from rfl]
    omega
  · rw [dif_neg hk]
    omega


lemma congruence_of_offset_eq {a b q n t : ℕ} (heq : a * b + 3 * n = q * n + t) :
    t % n = a * b % n := by
  have h2 : t + q * n = a * b + 3 * n := by omega
  have h3 : (t + q * n) % n = (a * b + 3 * n) % n := by rw [h2]
  simpa only [Nat.add_mul_mod_self_right] using h3


lemma mulModTarget3_soundness_core_wm {B : ℕ} (hB2 : 2 ≤ B)
    (hp : 2 ^ (2 * B) * (m + 1) * 4 < p)
    (i₀ : ℕ) (env : Environment (F p))
    (a b n t : Var (BigInt m) (F p))
    (c : Vector (F p) (2 * m - 1))
    (Pv : Vector (Expression (F p)) (2 * m - 1))
    (av bv nv tv : BigInt m (F p))
    (ha_input : Vector.map (Expression.eval env) a = av)
    (hb_input : Vector.map (Expression.eval env) b = bv)
    (hn_input : Vector.map (Expression.eval env) n = nv)
    (ht_input : Vector.map (Expression.eval env) t = tv)
    (ha_norm : BigInt.Normalized B av) (hb_norm : BigInt.Normalized B bv)
    (hn_norm : BigInt.Normalized B nv)
    (ht_limb : ∀ i : Fin m, (tv[i.val]).val < 3 * 2 ^ B)
    (hc_limb : ∀ j : Fin (2 * m - 1), (c[j.val]).val < 2 ^ B)
    (hc_val : polyValue B c = 3 * BigInt.value B nv)
    (hq_norm : BigInt.Normalized B (Vector.map (Expression.eval env)
        (Vector.mapRange m fun i ↦ var { index := i₀ + i })))
    (heqAB_get : ∀ k : Fin (2 * m - 1),
      Expression.eval env Pv[k.val] = Expression.eval env (bigIntMulNoReduce a b)[k.val])
    (h_eq_impl :
      ((∀ k : Fin (2 * m - 1),
          (Expression.eval env (Pv[k.val] + (c[k.val] : Expression (F p)))).val
            < (m + 1) * 2 ^ (2 * B)) ∧
        ∀ k : Fin (2 * m - 1),
          (Expression.eval env
            (if h : k.val < m then
              (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n)[k.val]
                + t[k.val]'h
            else (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n)[k.val])).val
            < (m + 1) * 2 ^ (2 * B)) →
        polyValue B (Vector.map (Expression.eval env)
            (Vector.mapFinRange (2 * m - 1) fun k ↦
              Pv[k.val] + (c[k.val] : Expression (F p)))) =
          polyValue B (Vector.map (Expression.eval env)
            (Vector.mapFinRange (2 * m - 1) fun k ↦
              if h : k.val < m then
                (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n)[k.val]
                  + t[k.val]'h
              else (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n)[k.val]))) :
    BigInt.value B tv % BigInt.value B nv
      = BigInt.value B av * BigInt.value B bv % BigInt.value B nv := by
  set qVar := (Vector.mapRange m fun i ↦ var (F := F p) { index := i₀ + i }) with hqVar
  set qv := (Vector.map (Expression.eval env) qVar : BigInt m (F p)) with hqv
  -- digit bounds
  have ha_lt : ∀ i : Fin m, (Expression.eval env a[i.val]).val < 2 ^ B := by
    intro i; rw [show Expression.eval env a[i.val] = av[i.val] from by
      rw [← ha_input]; simp only [Vector.getElem_map]]; exact ha_norm i
  have hb_lt : ∀ i : Fin m, (Expression.eval env b[i.val]).val < 2 ^ B := by
    intro i; rw [show Expression.eval env b[i.val] = bv[i.val] from by
      rw [← hb_input]; simp only [Vector.getElem_map]]; exact hb_norm i
  have hn_lt : ∀ i : Fin m, (Expression.eval env n[i.val]).val < 2 ^ B := by
    intro i; rw [show Expression.eval env n[i.val] = nv[i.val] from by
      rw [← hn_input]; simp only [Vector.getElem_map]]; exact hn_norm i
  have hqd_lt : ∀ i : Fin m, (Expression.eval env qVar[i.val]).val < 2 ^ B := by
    intro i; have := hq_norm i; rwa [hqv, Fin.getElem_fin, Vector.getElem_map] at this
  have htd_lt : ∀ j : ℕ, (hj : j < m) → (Expression.eval env (t[j]'hj)).val < 3 * 2 ^ B := by
    intro j hj
    have h : (tv[j]'hj).val < 3 * 2 ^ B := ht_limb ⟨j, hj⟩
    rwa [show tv[j]'hj = (Vector.map (Expression.eval env) t)[j]'hj from by rw [ht_input],
      Vector.getElem_map] at h
  have hfield : m * (2 ^ B * 2 ^ B) < p := by
    have h1 : m * (2 ^ B * 2 ^ B) = m * 2 ^ (2 * B) := by rw [two_mul, pow_add]
    rw [h1]
    have h2 : m * 2 ^ (2 * B) ≤ 2 ^ (2 * B) * (m + 1) * 4 := by nlinarith [Nat.two_pow_pos (2 * B)]
    omega
  -- the two sides in the implication are exactly `lVecC Pv c` / `sVecT qVar n t`
  have hL_eq : (Vector.mapFinRange (2 * m - 1) fun k ↦
        Pv[k.val] + ((c[k.val] : F p) : Expression (F p)))
      = lVecC Pv c := rfl
  have hS_eq : (Vector.mapFinRange (2 * m - 1) fun k ↦
        if h : k.val < m then (bigIntMulNoReduce qVar n)[k.val] + t[k.val]'h
        else (bigIntMulNoReduce qVar n)[k.val])
      = sVecT qVar n t := rfl
  -- discharge the coefficient bounds, get the polyValue equality
  have h_polyeq := h_eq_impl ⟨fun k => by
      rw [show Expression.eval env (Pv[k.val] + ((c[k.val] : F p) : Expression (F p)))
            = Expression.eval env Pv[k.val] + c[k.val] from rfl]
      have hle := ZMod.val_add_le (Expression.eval env Pv[k.val]) (c[k.val])
      rw [show Expression.eval env Pv[k.val]
            = Expression.eval env (bigIntMulNoReduce a b)[k.val] from heqAB_get k] at hle ⊢
      have hb' := coeff_L_boundC env a b c k ha_lt hb_lt hc_limb hfield
      omega,
    fun k => by
      have hb' := coeff_S_boundT3 hB2 env qVar n t k hqd_lt hn_lt htd_lt hfield
      rw [sVecT, Vector.getElem_mapFinRange] at hb'
      exact hb'⟩
  rw [hL_eq, hS_eq] at h_polyeq
  -- split L: polyValue L = polyValue Pv + polyValue c = a·b + 3n
  have hLSplit := polyValue_lVecC_split (B := B) env Pv c
    (fun k => by
      rw [heqAB_get k]
      have h1 := val_bigIntMulNoReduce_coeff_lt env a b k ha_lt hb_lt hfield
      have h2 := hc_limb k
      have hpow : (2 : ℕ) ^ B ≤ 2 ^ (2 * B) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h3 : m * 2 ^ (2 * B) + 2 ^ (2 * B) ≤ 2 ^ (2 * B) * (m + 1) * 4 := by
        nlinarith [Nat.two_pow_pos (2 * B)]
      omega)
  -- rewrite the abstract lhs through the eval bridge
  have hPv_map : Vector.map (Expression.eval env) Pv
      = Vector.map (Expression.eval env) (bigIntMulNoReduce a b) := by
    apply Vector.ext; intro k hk
    rw [Vector.getElem_map, Vector.getElem_map]
    exact heqAB_get ⟨k, hk⟩
  have hP : polyValue B (Vector.map (Expression.eval env) (bigIntMulNoReduce a b))
      = BigInt.value B av * BigInt.value B bv := by
    rw [polyValue_mul_eq env a b ha_lt hb_lt hfield, ha_input, hb_input]
  -- split S: polyValue S = polyValue Sqn + t.value
  have hSplit := polyValue_sVecT_split (B := B) env qVar n t
    (fun k hk => by
      have h1 := val_bigIntMulNoReduce_coeff_lt env qVar n k hqd_lt hn_lt hfield
      have h2 := htd_lt k.val hk
      have hpow : (2 : ℕ) ^ B ≤ 2 ^ (2 * B) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h3 : m * 2 ^ (2 * B) + 3 * 2 ^ (2 * B) ≤ 2 ^ (2 * B) * (m + 1) * 4 := by
        nlinarith [Nat.two_pow_pos (2 * B)]
      have h4 : 3 * 2 ^ B ≤ 3 * 2 ^ (2 * B) := by
        have := Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) (show B ≤ 2 * B by omega)
        omega
      omega)
  have hSqn : polyValue B (Vector.map (Expression.eval env) (bigIntMulNoReduce qVar n))
      = BigInt.value B qv * BigInt.value B nv := by
    rw [polyValue_Sqn_eq env qVar n hqd_lt hn_lt hfield, ← hn_input]
  -- combine: a·b + 3n = q·n + t, conclude the congruence
  rw [hLSplit, hPv_map, hP, hc_val] at h_polyeq
  rw [hSplit, hSqn, ht_input] at h_polyeq
  exact congruence_of_offset_eq h_polyeq

set_option maxHeartbeats 1600000 in

lemma mulModTarget3_completeness_core_wm {B : ℕ} (hB : 2 ^ B < p) (hB2 : 2 ≤ B)
    (hp : 2 ^ (2 * B) * (m + 1) * 4 < p)
    (i₀ : ℕ) (env : Environment (F p))
    (a b n t : Var (BigInt m) (F p))
    (c : Vector (F p) (2 * m - 1))
    (Pv : Vector (Expression (F p)) (2 * m - 1))
    (av bv nv tv : BigInt m (F p))
    (ha_input : Vector.map (Expression.eval env) a = av)
    (hb_input : Vector.map (Expression.eval env) b = bv)
    (hn_input : Vector.map (Expression.eval env) n = nv)
    (ht_input : Vector.map (Expression.eval env) t = tv)
    (ha_norm : BigInt.Normalized B av) (hb_norm : BigInt.Normalized B bv)
    (hn_norm : BigInt.Normalized B nv)
    (ht_limb : ∀ i : Fin m, (tv[i.val]).val < 3 * 2 ^ B)
    (hc_limb : ∀ j : Fin (2 * m - 1), (c[j.val]).val < 2 ^ B)
    (hc_val : polyValue B c = 3 * BigInt.value B nv)
    (hab_lt : BigInt.value B av < BigInt.value B nv)
    (hbb_lt : BigInt.value B bv < BigInt.value B nv)
    (hn_pos : 0 < BigInt.value B nv)
    (hn3 : BigInt.value B nv + 3 ≤ 2 ^ (B * m))
    (ht_lt3 : BigInt.value B tv < 3 * BigInt.value B nv)
    (ht_spec : BigInt.value B tv % BigInt.value B nv
      = BigInt.value B av * BigInt.value B bv % BigInt.value B nv)
    (hqwit : ∀ i : Fin m, env.get (i₀ + i.val)
      = (((BigInt.value B av * BigInt.value B bv + 3 * BigInt.value B nv
            - BigInt.value B tv) / BigInt.value B nv
          / 2 ^ (B * i.val) % 2 ^ B : ℕ) : F p))
    (heqAB_get : ∀ k : Fin (2 * m - 1),
      Expression.eval env Pv[k.val] = Expression.eval env (bigIntMulNoReduce a b)[k.val]) :
    BigInt.Normalized B (Vector.map (Expression.eval env)
        (Vector.mapRange m fun i ↦ var { index := i₀ + i })) ∧
      ((∀ k : Fin (2 * m - 1),
          (Expression.eval env (Pv[k.val] + (c[k.val] : Expression (F p)))).val
            < (m + 1) * 2 ^ (2 * B)) ∧
        ∀ k : Fin (2 * m - 1),
          (Expression.eval env
            (if h : k.val < m then
              (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n)[k.val]
                + t[k.val]'h
            else (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n)[k.val])).val
            < (m + 1) * 2 ^ (2 * B)) ∧
        polyValue B (Vector.map (Expression.eval env)
            (Vector.mapFinRange (2 * m - 1) fun k ↦
              Pv[k.val] + (c[k.val] : Expression (F p)))) =
          polyValue B (Vector.map (Expression.eval env)
            (Vector.mapFinRange (2 * m - 1) fun k ↦
              if h : k.val < m then
                (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n)[k.val]
                  + t[k.val]'h
              else (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n)[k.val])) := by
  set aval := BigInt.value B av with ha_def
  set bval := BigInt.value B bv with hb_def
  set nval := BigInt.value B nv with hn_def
  set tval := BigInt.value B tv with ht_def
  set qval := (aval * bval + 3 * nval - tval) / nval with hqval_def
  -- the offset dividend is exactly divisible: a·b + 3n = q·n + t
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
  -- the quotient is small: q < n + 3 ≤ 2^(Bm)
  have hqval_lt : qval < 2 ^ (B * m) := by
    have hq_le : qval ≤ (aval * bval + 3 * nval) / nval :=
      Nat.div_le_div_right (Nat.sub_le _ _)
    have hq_lt : (aval * bval + 3 * nval) / nval < nval + 3 := by
      apply Nat.div_lt_of_lt_mul
      have hab : aval * bval < nval * nval := by
        rcases Nat.eq_zero_or_pos bval with hb0 | hb0
        · rw [hb0, Nat.mul_zero]; exact Nat.mul_pos hn_pos hn_pos
        · calc aval * bval < nval * bval := by
                apply (Nat.mul_lt_mul_right hb0).mpr hab_lt
            _ ≤ nval * nval := by apply Nat.mul_le_mul_left; omega
      calc aval * bval + 3 * nval < nval * nval + 3 * nval := by omega
        _ = nval * (nval + 3) := by ring
    omega
  -- q witness vector value / normalization
  have hqv_val : BigInt.value B (Vector.map (Expression.eval env)
      (Vector.mapRange m fun i ↦ var { index := i₀ + i })) = qval :=
    BigInt.value_mapRange i₀ qval env hB hqval_lt (by intro i; rw [hqwit i])
  have hqv_norm : BigInt.Normalized B (Vector.map (Expression.eval env)
      (Vector.mapRange m fun i ↦ var { index := i₀ + i })) :=
    normalized_mapRange i₀ qval env hB (by intro i; rw [hqwit i])
  -- digit bounds
  have ha_lt : ∀ i : Fin m, (Expression.eval env a[i.val]).val < 2 ^ B := by
    intro i; rw [show Expression.eval env a[i.val] = av[i.val] from by
      rw [← ha_input]; simp only [Vector.getElem_map]]; exact ha_norm i
  have hb_lt : ∀ i : Fin m, (Expression.eval env b[i.val]).val < 2 ^ B := by
    intro i; rw [show Expression.eval env b[i.val] = bv[i.val] from by
      rw [← hb_input]; simp only [Vector.getElem_map]]; exact hb_norm i
  have hn_lt' : ∀ i : Fin m, (Expression.eval env n[i.val]).val < 2 ^ B := by
    intro i; rw [show Expression.eval env n[i.val] = nv[i.val] from by
      rw [← hn_input]; simp only [Vector.getElem_map]]; exact hn_norm i
  have hqd_lt : ∀ i : Fin m,
      (Expression.eval env (Vector.mapRange m fun j ↦ var (F := F p) { index := i₀ + j })[i.val]).val < 2 ^ B := by
    intro i; have := hqv_norm i; rwa [Fin.getElem_fin, Vector.getElem_map] at this
  have htd_lt : ∀ j : ℕ, (hj : j < m) → (Expression.eval env (t[j]'hj)).val < 3 * 2 ^ B := by
    intro j hj
    have h : (tv[j]'hj).val < 3 * 2 ^ B := ht_limb ⟨j, hj⟩
    rwa [show tv[j]'hj = (Vector.map (Expression.eval env) t)[j]'hj from by rw [ht_input],
      Vector.getElem_map] at h
  have hfield : m * (2 ^ B * 2 ^ B) < p := by
    have h1 : m * (2 ^ B * 2 ^ B) = m * 2 ^ (2 * B) := by rw [two_mul, pow_add]
    rw [h1]
    have h2 : m * 2 ^ (2 * B) ≤ 2 ^ (2 * B) * (m + 1) * 4 := by nlinarith [Nat.two_pow_pos (2 * B)]
    omega
  have hL_eq : (Vector.mapFinRange (2 * m - 1) fun k ↦
        Pv[k.val] + ((c[k.val] : F p) : Expression (F p)))
      = lVecC Pv c := rfl
  have hS_eq : (Vector.mapFinRange (2 * m - 1) fun k ↦
        if h : k.val < m then
          (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n)[k.val]
            + t[k.val]'h
        else (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n)[k.val])
      = sVecT (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n t := rfl
  -- the abstract lhs evaluates like the schoolbook convolution
  have hPv_map : Vector.map (Expression.eval env) Pv
      = Vector.map (Expression.eval env) (bigIntMulNoReduce a b) := by
    apply Vector.ext; intro k hk
    rw [Vector.getElem_map, Vector.getElem_map]
    exact heqAB_get ⟨k, hk⟩
  have hP : polyValue B (Vector.map (Expression.eval env) (bigIntMulNoReduce a b))
      = aval * bval := by
    rw [polyValue_mul_eq env a b ha_lt hb_lt hfield, ha_input, hb_input]
  -- split L: polyValue L = a·b + 3n
  have hLSplit := polyValue_lVecC_split (B := B) env Pv c
    (fun k => by
      rw [heqAB_get k]
      have h1 := val_bigIntMulNoReduce_coeff_lt env a b k ha_lt hb_lt hfield
      have h2 := hc_limb k
      have hpow : (2 : ℕ) ^ B ≤ 2 ^ (2 * B) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h3 : m * 2 ^ (2 * B) + 2 ^ (2 * B) ≤ 2 ^ (2 * B) * (m + 1) * 4 := by
        nlinarith [Nat.two_pow_pos (2 * B)]
      omega)
  -- split S: polyValue S = q·n + t.value
  have hSplit := polyValue_sVecT_split (B := B) env
    (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n t
    (fun k hk => by
      have h1 := val_bigIntMulNoReduce_coeff_lt env
        (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n k hqd_lt hn_lt' hfield
      have h2 := htd_lt k.val hk
      have hpow : (2 : ℕ) ^ B ≤ 2 ^ (2 * B) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h3 : m * 2 ^ (2 * B) + 3 * 2 ^ (2 * B) ≤ 2 ^ (2 * B) * (m + 1) * 4 := by
        nlinarith [Nat.two_pow_pos (2 * B)]
      have h4 : 3 * 2 ^ B ≤ 3 * 2 ^ (2 * B) := by
        have := Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) (show B ≤ 2 * B by omega)
        omega
      omega)
  have hSqn : polyValue B (Vector.map (Expression.eval env)
      (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n))
      = qval * nval := by
    rw [polyValue_Sqn_eq env (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n
      hqd_lt hn_lt' hfield, hqv_val, hn_input]
  refine ⟨hqv_norm, ⟨fun k => ?_, fun k => ?_⟩, ?_⟩
  · rw [show Expression.eval env (Pv[k.val] + ((c[k.val] : F p) : Expression (F p)))
          = Expression.eval env Pv[k.val] + c[k.val] from rfl]
    have hle := ZMod.val_add_le (Expression.eval env Pv[k.val]) (c[k.val])
    rw [show Expression.eval env Pv[k.val]
          = Expression.eval env (bigIntMulNoReduce a b)[k.val] from heqAB_get k] at hle ⊢
    have hb' := coeff_L_boundC env a b c k ha_lt hb_lt hc_limb hfield
    omega
  · have hb' := coeff_S_boundT3 hB2 env (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n t k
      hqd_lt hn_lt' htd_lt hfield
    rw [sVecT, Vector.getElem_mapFinRange] at hb'
    exact hb'
  · rw [hL_eq, hS_eq, hLSplit, hSplit, hSqn, ht_input, hPv_map, hP, hc_val]
    omega

end

end MulMod

end Solution.Secp256k1ScalarMul
