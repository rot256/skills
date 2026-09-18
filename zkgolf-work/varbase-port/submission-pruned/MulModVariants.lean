import Solution.Secp256k1ScalarMul.MulMod

namespace Solution.Secp256k1ScalarMul
open Solution.Secp256k1ScalarMul.Limbs

namespace MulMod

section
variable {p : ℕ} [Fact p.Prime]
variable {m : ℕ} [NeZero m]

omit [NeZero m] in

lemma remainder_congr {a b q n r : ℕ} (heq : a * b = q * n + r) :
    r % n = a * b % n := by
  rw [heq, Nat.add_comm, Nat.add_mul_mod_self_right]

lemma mulMod_soundness_core_loose {B : ℕ} (hp : 2 ^ (2 * B) * (m + 1) * 4 < p)
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
                else (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2)[k.val]))) :
    BigInt.Normalized B (Vector.map (Expression.eval env)
        (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })) ∧
      BigInt.value B (Vector.map (Expression.eval env)
          (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })) %
          BigInt.value B input.2.2 =
        BigInt.value B input.1 * BigInt.value B input.2.1 % BigInt.value B input.2.2 := by
  set qVar := (Vector.mapRange m fun i ↦ var (F := F p) { index := i₀ + i }) with hqVar
  set rVar := (Vector.mapRange m fun i ↦ var (F := F p) { index := i₀ + m + i }) with hrVar
  set qv := (Vector.map (Expression.eval env) qVar : BigInt m (F p)) with hqv
  set rv := (Vector.map (Expression.eval env) rVar : BigInt m (F p)) with hrv
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
  have hfield : m * (2 ^ B * 2 ^ B) < p := by
    have h1 : m * (2 ^ B * 2 ^ B) = m * 2 ^ (2 * B) := by rw [two_mul, pow_add]
    rw [h1]
    have h2 : m * 2 ^ (2 * B) ≤ 2 ^ (2 * B) * (m + 1) * 4 := by nlinarith [Nat.two_pow_pos (2 * B)]
    omega
  have hS_eq : (Vector.mapFinRange (2 * m - 1) fun k ↦
        if h : k.val < m then (bigIntMulNoReduce qVar input_var.2.2)[k.val] + var { index := i₀ + m + k.val }
        else (bigIntMulNoReduce qVar input_var.2.2)[k.val])
      = sVec qVar input_var.2.2 (i₀ + m) := by
    rfl
  have h_polyeq := h_eq_impl ⟨fun k => coeff_P_bound env input_var.1 input_var.2.1 k ha_lt hb_lt hfield,
    fun k => by
      have hb := coeff_S_bound env qVar input_var.2.2 (i₀ + m) k hqd_lt hn_lt hrd_lt hfield
      rw [sVec, Vector.getElem_mapFinRange] at hb
      exact hb⟩
  rw [hS_eq] at h_polyeq
  have hP : polyValue B (Vector.map (Expression.eval env) (bigIntMulNoReduce input_var.1 input_var.2.1))
      = BigInt.value B input.1 * BigInt.value B input.2.1 := by
    rw [polyValue_mul_eq env input_var.1 input_var.2.1 ha_lt hb_lt hfield, ← h_input]
  have hSplit := polyValue_sVec_split (B := B) env qVar input_var.2.2 (i₀ + m)
    (fun k hk => by
      have h1 := val_bigIntMulNoReduce_coeff_lt env qVar input_var.2.2 k hqd_lt hn_lt hfield
      have h2 := hrd_lt k.val hk
      have hpow : (2 : ℕ) ^ B ≤ 2 ^ (2 * B) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h3 : m * 2 ^ (2 * B) + 2 ^ (2 * B) ≤ 2 ^ (2 * B) * (m + 1) * 4 := by nlinarith [Nat.two_pow_pos (2 * B)]
      omega)
  have hSqn : polyValue B (Vector.map (Expression.eval env) (bigIntMulNoReduce qVar input_var.2.2))
      = BigInt.value B qv * BigInt.value B input.2.2 := by
    rw [polyValue_Sqn_eq env qVar input_var.2.2 hqd_lt hn_lt hfield, ← h_input]
  have hrval : BigInt.value B (Vector.map (Expression.eval env)
      (Vector.mapRange m fun i => var (F := F p) { index := i₀ + m + i })) = BigInt.value B rv := by
    rw [hrv, hrVar]
  rw [hP] at h_polyeq
  rw [hSplit, hSqn, hrval] at h_polyeq
  refine ⟨hr_norm, ?_⟩
  exact remainder_congr h_polyeq

lemma mulMod_soundness_core_loose_wm {B : ℕ} (hp : 2 ^ (2 * B) * (m + 1) * 4 < p)
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
              if h : k.val < m then Qv[k.val] + var { index := i₀ + m + k.val } else Qv[k.val]))) :
    BigInt.Normalized B (Vector.map (Expression.eval env)
        (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })) ∧
      BigInt.value B (Vector.map (Expression.eval env)
          (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })) %
          BigInt.value B input.2.2 =
        BigInt.value B input.1 * BigInt.value B input.2.1 % BigInt.value B input.2.2 := by
  have h_eq_impl' := eqImpl_bridge (rOff := i₀ + m) env Pv (bigIntMulNoReduce a b)
    Qv (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n)
    heqAB_get heqQN_get h_eq_impl
  exact mulMod_soundness_core_loose (B := B) hp i₀ env (a, b, n) input h_input
    ha_norm hb_norm hn_norm hq_norm hr_norm h_eq_impl'

lemma mulMod_completeness_core_wideb {B : ℕ} (hB : 2 ^ B < p)
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
  set a := BigInt.value B input.1 with ha_def
  set b := BigInt.value B input.2.1 with hb_def
  set n := BigInt.value B input.2.2 with hn_def
  set qval := a * b / n with hqval_def
  set rval := a * b % n with hrval_def
  have hmap_a : BigInt.value B (Vector.map (Expression.eval env) input_var.1) = a := by
    rw [ha_def, ← h_input]
  have hmap_b : BigInt.value B (Vector.map (Expression.eval env) input_var.2.1) = b := by
    rw [hb_def, ← h_input]
  have hmap_n : BigInt.value B (Vector.map (Expression.eval env) input_var.2.2) = n := by
    rw [hn_def, ← h_input]
  have hmap_n_norm : BigInt.Normalized B (Vector.map (Expression.eval env) input_var.2.2) := by
    rw [show (Vector.map (Expression.eval env) input_var.2.2) = input.2.2 from by rw [← h_input]]
    exact hn_norm
  have hn_lt : n < 2 ^ (B * m) := BigInt.value_lt hn_norm

  have hb_lt2 : b < 2 ^ (B * m) := BigInt.value_lt hb_norm
  have hqval_lt : qval < 2 ^ (B * m) := by
    rw [hqval_def]
    apply Nat.div_lt_of_lt_mul
    rcases Nat.eq_zero_or_pos b with hb0 | hb0
    · rw [hb0, Nat.mul_zero]
      exact Nat.mul_pos hn_pos (Nat.two_pow_pos (B * m))
    · calc a * b < n * b := by
            apply (Nat.mul_lt_mul_right hb0).mpr hab_lt
        _ ≤ n * 2 ^ (B * m) := by apply Nat.mul_le_mul_left; omega
  have hrval_lt : rval < 2 ^ (B * m) := lt_trans (Nat.mod_lt _ hn_pos) hn_lt
  have hqv_val : BigInt.value B (Vector.map (Expression.eval env)
      (Vector.mapRange m fun i ↦ var { index := i₀ + i })) = qval :=
    BigInt.value_mapRange i₀ qval env hB hqval_lt (by intro i; rw [hqwit i])
  have hrv_val : BigInt.value B (Vector.map (Expression.eval env)
      (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })) = rval :=
    BigInt.value_mapRange (i₀ + m) rval env hB hrval_lt (by intro i; rw [hrwit i])
  have hqv_norm : BigInt.Normalized B (Vector.map (Expression.eval env)
      (Vector.mapRange m fun i ↦ var { index := i₀ + i })) :=
    normalized_mapRange i₀ qval env hB (by intro i; rw [hqwit i])
  have hrv_norm : BigInt.Normalized B (Vector.map (Expression.eval env)
      (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })) :=
    normalized_mapRange (i₀ + m) rval env hB (by intro i; rw [hrwit i])
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
  have hfield : m * (2 ^ B * 2 ^ B) < p := by
    have h1 : m * (2 ^ B * 2 ^ B) = m * 2 ^ (2 * B) := by rw [two_mul, pow_add]
    rw [h1]
    have h2 : m * 2 ^ (2 * B) ≤ 2 ^ (2 * B) * (m + 1) * 4 := by nlinarith [Nat.two_pow_pos (2 * B)]
    omega
  have hS_eq : (Vector.mapFinRange (2 * m - 1) fun k ↦
        if h : k.val < m then (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2)[k.val]
          + var { index := i₀ + m + k.val }
        else (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2)[k.val])
      = sVec (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2 (i₀ + m) := rfl
  have hP : polyValue B (Vector.map (Expression.eval env) (bigIntMulNoReduce input_var.1 input_var.2.1))
      = a * b := by
    rw [polyValue_mul_eq env input_var.1 input_var.2.1 ha_lt hb_lt hfield, hmap_a, hmap_b]
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

lemma mulMod_completeness_core_wideb_wm {B : ℕ} (hB : 2 ^ B < p)
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
    mulMod_completeness_core_wideb (B := B) hB hp i₀ env (a, b, n) input h_input
      ha_norm hb_norm hn_norm hab_lt hn_pos hqwit hrwit
  exact ⟨hqn, hrn,
    eqConj_bridge (rOff := i₀ + m) env Pv (bigIntMulNoReduce a b) Qv
      (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n)
      heqAB_get heqQN_get hconj, hlt⟩

def AssumptionsWideB (B : ℕ) (input : Inputs m (F p)) : Prop :=
  let a := input.a
  let b := input.b
  let n := input.modulus
  a.Normalized B ∧ b.Normalized B ∧ n.Normalized B ∧
    a.value B < n.value B ∧ 0 < n.value B

end

end MulMod

namespace MulModLoose

section
variable {p : ℕ} [Fact p.Prime]
variable {m : ℕ} [NeZero m]

open Solution.Secp256k1ScalarMul.MulMod
open private evalValue from Solution.Secp256k1ScalarMul.MulMod

def main (P : BigIntParams p m)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqXV.GVXHyps p (2 * m - 1) P.B gf posOf G V VR)
    [Fact (p > 2)]
    (input : Var (MulMod.Inputs m) (F p)) :
    Circuit (F p) (Var (BigInt m) (F p)) :=
  letI : NeZero (2 * m - 1) := ⟨by have := Nat.pos_of_neZero m; omega⟩
  do
  let a := input.a
  let b := input.b
  let n := input.modulus
  let q ← ProvableType.witness (α := BigInt m) fun env =>
    let prod := evalValue P.B env a * evalValue P.B env b
    let qval : ℕ := prod / evalValue P.B env n
    Vector.ofFn fun k : Fin m => ((qval / 2 ^ (P.B * k.val) % 2 ^ P.B : ℕ) : F p)
  let r ← ProvableType.witness (α := BigInt m) fun env =>
    let prod := evalValue P.B env a * evalValue P.B env b
    let rval : ℕ := prod % evalValue P.B env n
    Vector.ofFn fun k : Fin m => ((rval / 2 ^ (P.B * k.val) % 2 ^ P.B : ℕ) : F p)
  Normalize.circuit P q
  Normalize.circuit P r
  let Pc ← interpolatedMul a b
  let Sqn : Vector (Expression (F p)) (2 * m - 1) := bigIntMulNoReduce q n
  let S : Vector (Expression (F p)) (2 * m - 1) := Vector.mapFinRange (2 * m - 1) fun k =>
    if h : k.val < m then Sqn[k.val] + r[k.val]'h else Sqn[k.val]
  GroupedEqXV.circuit P.B gf posOf G V VR hgv P.hB1 { lhs := Pc, rhs := S }
  return r

instance elaborated (P : BigIntParams p m)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqXV.GVXHyps p (2 * m - 1) P.B gf posOf G V VR)
    [Fact (p > 2)] :
    ElaboratedCircuit (F p) (MulMod.Inputs m) (BigInt m) (main P gf posOf G V VR hgv) where

  localLength _ :=
    m + m + m * (P.B - 1) + m * (P.B - 1) + (2 * m - 1)
      + GroupedEqXV.widthAllocFrom V.Wf (G - 2) 0
  output _ i0 := varFromOffset (BigInt m) (i0 + m)
  localLength_eq := by
    intro input offset
    simp only [main, interpolatedMul, circuit_norm, Normalize.circuit, Normalize.elaborated,
      Normalize.main, GroupedEqXV.circuit, GroupedEqXV.elaborated]
    omega
  output_eq := by
    intro input offset
    simp only [main, interpolatedMul, circuit_norm, Normalize.circuit, Normalize.elaborated,
      Normalize.main, GroupedEqXV.circuit, GroupedEqXV.elaborated]
  subcircuitsConsistent := by
    intro input offset
    simp +arith only [main, interpolatedMul, circuit_norm, Normalize.circuit, Normalize.elaborated,
      Normalize.main, GroupedEqXV.circuit, GroupedEqXV.elaborated]
  channelsLawful := by
    intro input offset
    simp only [main, interpolatedMul, circuit_norm, Normalize.circuit, Normalize.elaborated,
      Normalize.main, GroupedEqXV.circuit, GroupedEqXV.elaborated]

def Spec (B : ℕ) (input : MulMod.Inputs m (F p)) (out : BigInt m (F p)) : Prop :=
  let a := input.a
  let b := input.b
  let n := input.modulus
  out.Normalized B ∧ out.value B % n.value B = (a.value B * b.value B) % n.value B

def circuit (P : BigIntParams p m)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqXV.GVXHyps p (2 * m - 1) P.B gf posOf G V VR)
    (hNf : ∀ j, V.Nf j = (m + 1) * 2 ^ (2 * P.B))
    (hNfR : ∀ j, VR.Nf j = (m + 1) * 2 ^ (2 * P.B))
    [Fact (p > 2)] :
    FormalCircuit (F p) (MulMod.Inputs m) (BigInt m) where
    main := main P gf posOf G V VR hgv
    Assumptions := MulMod.Assumptions P.B
    Spec := Spec P.B
    soundness := by
      obtain ⟨B, W, hB, hW, hB1, hWB, hWp, hp⟩ := P
      circuit_proof_start [Normalize.circuit, Normalize.elaborated, Normalize.main,
        Normalize.Assumptions, Normalize.Spec,
        GroupedEqXV.circuit, GroupedEqXV.elaborated,
        GroupedEqXV.Assumptions, GroupedEqX.Spec]
      obtain ⟨ha_norm, hb_norm, hn_norm, hab_lt, hbb_lt, hn_pos⟩ := h_assumptions
      obtain ⟨hq_norm, hr_norm, hAB_ops, h_eq_impl⟩ := h_holds
      simp only [hNf, hNfR] at h_eq_impl
      have hpm : 2 * m - 1 < p := two_m_sub_one_lt hp
      have h_pAB := interpolatedMul_soundness (i₀ + m + m + m * (B - 1) + m * (B - 1))
        input_var.a input_var.b env hAB_ops
      refine ⟨?_, interpolatedMul_requirements _ _ _ _⟩
      have h_input' : (Vector.map (Expression.eval env) input_var.a,
          Vector.map (Expression.eval env) input_var.b,
          Vector.map (Expression.eval env) input_var.modulus)
            = ((input.a, input.b, input.modulus) :
              ProvablePair (BigInt m) (ProvablePair (BigInt m) (BigInt m)) (F p)) := by
        simp only [← h_input]
      have heqAB_get := interpolatedMul_eval_bridge env (i₀ + m + m + m * (B - 1) + m * (B - 1))
        input_var.a input_var.b hpm h_pAB
      exact MulMod.mulMod_soundness_core_loose_wm (B := B) hp i₀ env
        input_var.a input_var.b input_var.modulus
        (interpolatedMul input_var.a input_var.b (i₀ + m + m + m * (B - 1) + m * (B - 1))).1
        (bigIntMulNoReduce (Vector.mapRange m fun i => var { index := i₀ + i })
          input_var.modulus)
        (input.a, input.b, input.modulus) h_input' ha_norm hb_norm hn_norm hq_norm hr_norm
        heqAB_get (fun _ => rfl) h_eq_impl
    completeness := by
      obtain ⟨B, W, hB, hW, hB1, hWB, hWp, hp⟩ := P
      circuit_proof_start [Normalize.circuit, Normalize.elaborated, Normalize.main,
        Normalize.Assumptions, Normalize.Spec,
        GroupedEqXV.circuit, GroupedEqXV.elaborated,
        GroupedEqXV.Assumptions, GroupedEqX.Spec]
      obtain ⟨ha_norm, hb_norm, hn_norm, hab_lt, hbb_lt, hn_pos⟩ := h_assumptions
      obtain ⟨hq_env, hr_env, hAB_uses⟩ := h_env
      have h_pvAB := interpolatedMul_usesLocalWitnesses (i₀ + m + m + m * (B - 1) + m * (B - 1))
        (i₀ + m + m + m * (B - 1) + m * (B - 1)) input_var.a input_var.b env rfl hAB_uses
      have heva : evalValue B env input_var.a = BigInt.value B input.a := by
        rw [evalValue, BigInt.value, ← h_input]
      have hevb : evalValue B env input_var.b = BigInt.value B input.b := by
        rw [evalValue, BigInt.value, ← h_input]
      have hevn : evalValue B env input_var.modulus = BigInt.value B input.modulus := by
        rw [evalValue, BigInt.value, ← h_input]
      have hqwit : ∀ i : Fin m, env.toEnvironment.get (i₀ + i.val)
          = ((BigInt.value B input.a * BigInt.value B input.b / BigInt.value B input.modulus
              / 2 ^ (B * i.val) % 2 ^ B : ℕ) : F p) := by
        intro i; rw [hq_env i, Vector.getElem_ofFn, heva, hevb, hevn]
      have hrwit : ∀ i : Fin m, env.toEnvironment.get (i₀ + m + i.val)
          = ((BigInt.value B input.a * BigInt.value B input.b % BigInt.value B input.modulus
              / 2 ^ (B * i.val) % 2 ^ B : ℕ) : F p) := by
        intro i; rw [hr_env i, Vector.getElem_ofFn, heva, hevb, hevn]
      have h_input' : (Vector.map (Expression.eval env.toEnvironment) input_var.a,
          Vector.map (Expression.eval env.toEnvironment) input_var.b,
          Vector.map (Expression.eval env.toEnvironment) input_var.modulus)
            = ((input.a, input.b, input.modulus) :
              ProvablePair (BigInt m) (ProvablePair (BigInt m) (BigInt m)) (F p)) := by
        simp only [← h_input]
      have heqAB_get := interpolatedMul_eval_bridge_uses env.toEnvironment
        (i₀ + m + m + m * (B - 1) + m * (B - 1)) input_var.a input_var.b h_pvAB
      have core := MulMod.mulMod_completeness_core_wm (B := B) hB hp i₀ env.toEnvironment
        input_var.a input_var.b input_var.modulus
        (interpolatedMul input_var.a input_var.b (i₀ + m + m + m * (B - 1) + m * (B - 1))).1
        (bigIntMulNoReduce (Vector.mapRange m fun i => var { index := i₀ + i })
          input_var.modulus)
        (input.a, input.b, input.modulus) h_input' ha_norm hb_norm hn_norm hab_lt hbb_lt hn_pos
        hqwit hrwit heqAB_get (fun _ => rfl)
      simp only [hNf, hNfR]
      exact ⟨core.1, core.2.1,
        interpolatedMul_completeness (i₀ + m + m + m * (B - 1) + m * (B - 1))
          input_var.a input_var.b env h_pvAB,
        core.2.2.1⟩

attribute [local irreducible] interpolatedMul Normalize.circuit GroupedEqXV.circuit

end

end MulModLoose

namespace MulModLooseCA

/-! ### Constant-`a` specialisation of `MulModLoose`

When the `a` operand is a compile-time constant vector, the product polynomial
`a * b` is already an *affine* expression vector, so there is no need to witness
its `2m-1` convolution coefficients and pin them with `2m-1` interpolation rows:
we can hand the raw `bigIntMulNoReduce a b` straight to the grouped equality.
This is exactly the same move the `q * n` side already makes.  It saves
`⟨2m-1, 2m-1⟩`.
-/

section
variable {p : ℕ} [Fact p.Prime]
variable {m : ℕ} [NeZero m]

open Solution.Secp256k1ScalarMul.MulMod
open private evalValue from Solution.Secp256k1ScalarMul.MulMod

def main (P : BigIntParams p m)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqXV.GVXHyps p (2 * m - 1) P.B gf posOf G V VR)
    [Fact (p > 2)]
    (input : Var (MulMod.Inputs m) (F p)) :
    Circuit (F p) (Var (BigInt m) (F p)) :=
  letI : NeZero (2 * m - 1) := ⟨by have := Nat.pos_of_neZero m; omega⟩
  do
  let a := input.a
  let b := input.b
  let n := input.modulus
  let q ← ProvableType.witness (α := BigInt m) fun env =>
    let prod := evalValue P.B env a * evalValue P.B env b
    let qval : ℕ := prod / evalValue P.B env n
    Vector.ofFn fun k : Fin m => ((qval / 2 ^ (P.B * k.val) % 2 ^ P.B : ℕ) : F p)
  let r ← ProvableType.witness (α := BigInt m) fun env =>
    let prod := evalValue P.B env a * evalValue P.B env b
    let rval : ℕ := prod % evalValue P.B env n
    Vector.ofFn fun k : Fin m => ((rval / 2 ^ (P.B * k.val) % 2 ^ P.B : ℕ) : F p)
  Normalize.circuit P q
  Normalize.circuit P r
  let Pc : Vector (Expression (F p)) (2 * m - 1) := bigIntMulNoReduce a b
  let Sqn : Vector (Expression (F p)) (2 * m - 1) := bigIntMulNoReduce q n
  let S : Vector (Expression (F p)) (2 * m - 1) := Vector.mapFinRange (2 * m - 1) fun k =>
    if h : k.val < m then Sqn[k.val] + r[k.val]'h else Sqn[k.val]
  GroupedEqXV.circuit P.B gf posOf G V VR hgv P.hB1 { lhs := Pc, rhs := S }
  return r

instance elaborated (P : BigIntParams p m)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqXV.GVXHyps p (2 * m - 1) P.B gf posOf G V VR)
    [Fact (p > 2)] :
    ElaboratedCircuit (F p) (MulMod.Inputs m) (BigInt m) (main P gf posOf G V VR hgv) where

  localLength _ :=
    m + m + m * (P.B - 1) + m * (P.B - 1)
      + GroupedEqXV.widthAllocFrom V.Wf (G - 2) 0
  output _ i0 := varFromOffset (BigInt m) (i0 + m)
  localLength_eq := by
    intro input offset
    simp only [main, circuit_norm, Normalize.circuit, Normalize.elaborated,
      Normalize.main, GroupedEqXV.circuit, GroupedEqXV.elaborated]
    omega
  output_eq := by
    intro input offset
    simp only [main, circuit_norm, Normalize.circuit, Normalize.elaborated,
      Normalize.main, GroupedEqXV.circuit, GroupedEqXV.elaborated]
  subcircuitsConsistent := by
    intro input offset
    simp +arith only [main, circuit_norm, Normalize.circuit, Normalize.elaborated,
      Normalize.main, GroupedEqXV.circuit, GroupedEqXV.elaborated]
  channelsLawful := by
    intro input offset
    simp only [main, circuit_norm, Normalize.circuit, Normalize.elaborated,
      Normalize.main, GroupedEqXV.circuit, GroupedEqXV.elaborated]

def Spec (B : ℕ) (input : MulMod.Inputs m (F p)) (out : BigInt m (F p)) : Prop :=
  let a := input.a
  let b := input.b
  let n := input.modulus
  out.Normalized B ∧ out.value B % n.value B = (a.value B * b.value B) % n.value B

def circuitWideB (P : BigIntParams p m)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqXV.GVXHyps p (2 * m - 1) P.B gf posOf G V VR)
    (hNf : ∀ j, V.Nf j = (m + 1) * 2 ^ (2 * P.B))
    (hNfR : ∀ j, VR.Nf j = (m + 1) * 2 ^ (2 * P.B))
    [Fact (p > 2)] :
    FormalCircuit (F p) (MulMod.Inputs m) (BigInt m) where
    main := main P gf posOf G V VR hgv
    Assumptions := MulMod.AssumptionsWideB P.B
    Spec := Spec P.B
    soundness := by
      obtain ⟨B, W, hB, hW, hB1, hWB, hWp, hp⟩ := P
      circuit_proof_start [Normalize.circuit, Normalize.elaborated, Normalize.main,
        Normalize.Assumptions, Normalize.Spec,
        GroupedEqXV.circuit, GroupedEqXV.elaborated,
        GroupedEqXV.Assumptions, GroupedEqX.Spec]
      obtain ⟨ha_norm, hb_norm, hn_norm, hab_lt, hn_pos⟩ := h_assumptions
      obtain ⟨hq_norm, hr_norm, h_eq_impl⟩ := h_holds
      simp only [hNf, hNfR] at h_eq_impl
      have h_input' : (Vector.map (Expression.eval env) input_var.a,
          Vector.map (Expression.eval env) input_var.b,
          Vector.map (Expression.eval env) input_var.modulus)
            = ((input.a, input.b, input.modulus) :
              ProvablePair (BigInt m) (ProvablePair (BigInt m) (BigInt m)) (F p)) := by
        simp only [← h_input]
      exact MulMod.mulMod_soundness_core_loose_wm (B := B) hp i₀ env
        input_var.a input_var.b input_var.modulus
        (bigIntMulNoReduce input_var.a input_var.b)
        (bigIntMulNoReduce (Vector.mapRange m fun i => var { index := i₀ + i })
          input_var.modulus)
        (input.a, input.b, input.modulus) h_input' ha_norm hb_norm hn_norm hq_norm hr_norm
        (fun _ => rfl) (fun _ => rfl) h_eq_impl
    completeness := by
      obtain ⟨B, W, hB, hW, hB1, hWB, hWp, hp⟩ := P
      circuit_proof_start [Normalize.circuit, Normalize.elaborated, Normalize.main,
        Normalize.Assumptions, Normalize.Spec,
        GroupedEqXV.circuit, GroupedEqXV.elaborated,
        GroupedEqXV.Assumptions, GroupedEqX.Spec]
      obtain ⟨ha_norm, hb_norm, hn_norm, hab_lt, hn_pos⟩ := h_assumptions
      obtain ⟨hq_env, hr_env⟩ := h_env
      have heva : evalValue B env input_var.a = BigInt.value B input.a := by
        rw [evalValue, BigInt.value, ← h_input]
      have hevb : evalValue B env input_var.b = BigInt.value B input.b := by
        rw [evalValue, BigInt.value, ← h_input]
      have hevn : evalValue B env input_var.modulus = BigInt.value B input.modulus := by
        rw [evalValue, BigInt.value, ← h_input]
      have hqwit : ∀ i : Fin m, env.toEnvironment.get (i₀ + i.val)
          = ((BigInt.value B input.a * BigInt.value B input.b / BigInt.value B input.modulus
              / 2 ^ (B * i.val) % 2 ^ B : ℕ) : F p) := by
        intro i; rw [hq_env i, Vector.getElem_ofFn, heva, hevb, hevn]
      have hrwit : ∀ i : Fin m, env.toEnvironment.get (i₀ + m + i.val)
          = ((BigInt.value B input.a * BigInt.value B input.b % BigInt.value B input.modulus
              / 2 ^ (B * i.val) % 2 ^ B : ℕ) : F p) := by
        intro i; rw [hr_env i, Vector.getElem_ofFn, heva, hevb, hevn]
      have h_input' : (Vector.map (Expression.eval env.toEnvironment) input_var.a,
          Vector.map (Expression.eval env.toEnvironment) input_var.b,
          Vector.map (Expression.eval env.toEnvironment) input_var.modulus)
            = ((input.a, input.b, input.modulus) :
              ProvablePair (BigInt m) (ProvablePair (BigInt m) (BigInt m)) (F p)) := by
        simp only [← h_input]
      have core := MulMod.mulMod_completeness_core_wideb_wm (B := B) hB hp i₀ env.toEnvironment
        input_var.a input_var.b input_var.modulus
        (bigIntMulNoReduce input_var.a input_var.b)
        (bigIntMulNoReduce (Vector.mapRange m fun i => var { index := i₀ + i })
          input_var.modulus)
        (input.a, input.b, input.modulus) h_input' ha_norm hb_norm hn_norm hab_lt hn_pos
        hqwit hrwit (fun _ => rfl) (fun _ => rfl)
      simp only [hNf, hNfR]
      exact ⟨core.1, core.2.1, core.2.2.1⟩

attribute [local irreducible] Normalize.circuit GroupedEqXV.circuit

theorem computableWitnessesWideB (P : BigIntParams p m)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqXV.GVXHyps p (2 * m - 1) P.B gf posOf G V VR)
    (hNf : ∀ j, V.Nf j = (m + 1) * 2 ^ (2 * P.B))
    (hNfR : ∀ j, VR.Nf j = (m + 1) * 2 ^ (2 * P.B))
    [Fact (p > 2)] :
    (circuitWideB P gf posOf G V VR hgv hNf hNfR).ComputableWitnesses := by
  letI : NeZero (2 * m - 1) := ⟨by have := Nat.pos_of_neZero m; omega⟩
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition input env env')
    ((main P gf posOf G V VR hgv input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main
  let qc : Circuit (F p) (Var (BigInt m) (F p)) := ProvableType.witness (α := BigInt m) fun env =>
    let prod := evalValue P.B env input.a * evalValue P.B env input.b
    let qval : ℕ := prod / evalValue P.B env input.modulus
    Vector.ofFn fun k : Fin m => ((qval / 2 ^ (P.B * k.val) % 2 ^ P.B : ℕ) : F p)
  let q := qc.output offset
  let rOff := offset + qc.localLength offset
  let rc : Circuit (F p) (Var (BigInt m) (F p)) := ProvableType.witness (α := BigInt m) fun env =>
    let prod := evalValue P.B env input.a * evalValue P.B env input.b
    let rval : ℕ := prod % evalValue P.B env input.modulus
    Vector.ofFn fun k : Fin m => ((rval / 2 ^ (P.B * k.val) % 2 ^ P.B : ℕ) : F p)
  let r := rc.output rOff
  let nqOff := rOff + rc.localLength rOff
  let nqc : Circuit (F p) Unit := Normalize.circuit P q
  let nrOff := nqOff + nqc.localLength nqOff
  let nrc : Circuit (F p) Unit := Normalize.circuit P r
  let eqOff := nrOff + nrc.localLength nrOff
  let pcv : Vector (Expression (F p)) (2 * m - 1) := bigIntMulNoReduce input.a input.b
  let Sqn : Vector (Expression (F p)) (2 * m - 1) := bigIntMulNoReduce q input.modulus
  let Sv : Vector (Expression (F p)) (2 * m - 1) := Vector.mapFinRange (2 * m - 1) fun k =>
    if h : k.val < m then Sqn[k.val] + r[k.val]'h else Sqn[k.val]
  let eqc : Circuit (F p) Unit :=
    GroupedEqXV.circuit P.B gf posOf G V VR hgv P.hB1 { lhs := pcv, rhs := Sv }
  have h_qlen : qc.localLength offset = m := by
    simp [qc, ProvableType.witness, Circuit.localLength, Operations.localLength, size]
  have h_rlen : rc.localLength rOff = m := by
    simp [rc, ProvableType.witness, Circuit.localLength, Operations.localLength, size]
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.provableWitness_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.pure_structuralComputableWitnesses_iff,
    and_true]
  and_intros
  · intro _ h_input
    have ha : evalValue P.B env input.a = evalValue P.B env' input.a :=
      MulMod.evalValue_stable P.B input.a (by
        simpa [circuit_norm] using congrArg (fun x : MulMod.Inputs m (F p) => x.a) h_input)
    have hb : evalValue P.B env input.b = evalValue P.B env' input.b :=
      MulMod.evalValue_stable P.B input.b (by
        simpa [circuit_norm] using congrArg (fun x : MulMod.Inputs m (F p) => x.b) h_input)
    have hn : evalValue P.B env input.modulus = evalValue P.B env' input.modulus :=
      MulMod.evalValue_stable P.B input.modulus (by
        simpa [circuit_norm] using congrArg (fun x : MulMod.Inputs m (F p) => x.modulus) h_input)
    simp only [ha, hb, hn]
  · intro _ h_input
    have ha : evalValue P.B env input.a = evalValue P.B env' input.a :=
      MulMod.evalValue_stable P.B input.a (by
        simpa [circuit_norm] using congrArg (fun x : MulMod.Inputs m (F p) => x.a) h_input)
    have hb : evalValue P.B env input.b = evalValue P.B env' input.b :=
      MulMod.evalValue_stable P.B input.b (by
        simpa [circuit_norm] using congrArg (fun x : MulMod.Inputs m (F p) => x.b) h_input)
    have hn : evalValue P.B env input.modulus = evalValue P.B env' input.modulus :=
      MulMod.evalValue_stable P.B input.modulus (by
        simpa [circuit_norm] using congrArg (fun x : MulMod.Inputs m (F p) => x.modulus) h_input)
    simp only [ha, hb, hn]
  · exact Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
      (Normalize.circuit P) input q nqOff
      (by
        intro k env env' hle h_agree _
        have hk : offset + m ≤ k := by
          dsimp only [nqOff, rOff] at hle
          rw [h_qlen] at hle
          omega
        exact MulMod.bigIntWitnessOutput_stable _ h_agree hk)
      (Normalize.computableWitnesses P) env env'
  · exact Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
      (Normalize.circuit P) input r nrOff
      (by
        intro k env env' hle h_agree _
        have hk : rOff + m ≤ k := by
          dsimp only [nrOff, nqOff] at hle
          rw [h_rlen] at hle
          omega
        exact MulMod.bigIntWitnessOutput_stable _ h_agree hk)
      (Normalize.computableWitnesses P) env env'
  · exact Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
      (GroupedEqXV.circuit P.B gf posOf G V VR hgv P.hB1) input { lhs := pcv, rhs := Sv } eqOff
      (by
        intro k env env' hle h_agree h_input
        have hk_q : offset + m ≤ k := by
          dsimp only [eqOff, nrOff, nqOff, rOff] at hle
          rw [h_qlen] at hle
          omega
        have hk_r : rOff + m ≤ k := by
          dsimp only [eqOff, nrOff, nqOff] at hle
          rw [h_rlen] at hle
          omega
        have ha : eval env input.a = eval env' input.a := by
          simpa [circuit_norm] using congrArg (fun x : MulMod.Inputs m (F p) => x.a) h_input
        have hb : eval env input.b = eval env' input.b := by
          simpa [circuit_norm] using congrArg (fun x : MulMod.Inputs m (F p) => x.b) h_input
        have hPc : Vector.map (Expression.eval env.toEnvironment) pcv
            = Vector.map (Expression.eval env'.toEnvironment) pcv := by
          apply Vector.ext
          intro t ht
          simp only [Vector.getElem_map, pcv]
          exact MulMod.bigIntMulNoReduce_coeff_stable env.toEnvironment env'.toEnvironment
            input.a input.b
            (fun j hj => MulMod.bigInt_getElem_eval_eq ha j hj)
            (fun j hj => MulMod.bigInt_getElem_eval_eq hb j hj) ⟨t, ht⟩
        have hq_vec : eval env q = eval env' q := MulMod.bigIntWitnessOutput_stable _ h_agree hk_q
        have hr_vec : eval env r = eval env' r := MulMod.bigIntWitnessOutput_stable _ h_agree hk_r
        have hn : eval env input.modulus = eval env' input.modulus := by
          simpa [circuit_norm] using congrArg (fun x : MulMod.Inputs m (F p) => x.modulus) h_input
        have hr_map : r.map (Expression.eval env.toEnvironment)
            = r.map (Expression.eval env'.toEnvironment) := MulMod.bigInt_map_eval_eq_of_eval_eq hr_vec
        have hS : Vector.map (Expression.eval env.toEnvironment) Sv
            = Vector.map (Expression.eval env'.toEnvironment) Sv := by
          apply Vector.ext
          intro i hi
          have hsq_i : Expression.eval env.toEnvironment Sqn[i]
              = Expression.eval env'.toEnvironment Sqn[i] :=
            MulMod.bigIntMulNoReduce_coeff_stable env.toEnvironment env'.toEnvironment q input.modulus
              (fun j hj => MulMod.bigInt_getElem_eval_eq hq_vec j hj)
              (fun j hj => MulMod.bigInt_getElem_eval_eq hn j hj) ⟨i, hi⟩
          simp only [Vector.getElem_map, Sv, Vector.getElem_mapFinRange]
          split
          · rename_i hlt
            have hr_i : Expression.eval env.toEnvironment (r[i]'hlt)
                = Expression.eval env'.toEnvironment (r[i]'hlt) := by
              have := congrArg (fun v : Vector (F p) m => v[i]'hlt) hr_map
              simpa only [Vector.getElem_map] using this
            simp only [Expression.eval, hsq_i, hr_i]
          · exact hsq_i
        simp only [circuit_norm]
        rw [hPc, hS])
      (GroupedEqXV.computableWitnesses P.B gf posOf G V VR hgv P.hB1) env env'

end

end MulModLooseCA

end Solution.Secp256k1ScalarMul
