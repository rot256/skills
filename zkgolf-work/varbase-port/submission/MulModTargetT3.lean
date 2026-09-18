import Solution.Secp256k1ScalarMul.MulModTargetT
import Solution.Secp256k1ScalarMul.ParamsWT3
import Batteries.Tactic.OpenPrivate



namespace Solution.Secp256k1ScalarMul
namespace MulModTargetT3
open MulMod MulModTargetD MulModTargetW MulModTargetT

-- Bring the private `evalValue` that `MulModTargetT.main`'s witnesses are built from into scope
-- (unambiguous: the other modules' `evalValue`s are private). The eval-stability helpers are
-- re-derived locally below against this same `evalValue`.
open private evalValue from Solution.Secp256k1ScalarMul.MulModTargetT

variable {p : ℕ} [Fact p.Prime]
variable {m : ℕ} [NeZero m]

omit [NeZero m] in
private lemma eval_add_zero3 (env : Environment (F p)) (x : Expression (F p)) :
    Expression.eval env (x + 0) = Expression.eval env x := by
  rw [show Expression.eval env (x + 0)
        = Expression.eval env x + Expression.eval env (0 : Expression (F p)) from rfl,
    show Expression.eval env (0 : Expression (F p)) = 0 from rfl, add_zero]

omit [NeZero m] in
private lemma eval_zero_add3 (env : Environment (F p)) (x : Expression (F p)) :
    Expression.eval env ((0 : Expression (F p)) + x) = Expression.eval env x := by
  rw [show Expression.eval env ((0 : Expression (F p)) + x)
        = Expression.eval env (0 : Expression (F p)) + Expression.eval env x from rfl,
    show Expression.eval env (0 : Expression (F p)) = 0 from rfl, zero_add]

omit [NeZero m] in
private lemma evalValue_stable3 (B : ℕ) (x : Var (BigInt m) (F p))
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

omit [NeZero m] in
private lemma target_map_stable3 (x : Var (MulModTargetT.TargetVec m) (F p))
    {env env' : ProverEnvironment (F p)}
    (h : eval env x = eval env' x) :
    Vector.map (Expression.eval env.toEnvironment) x
      = Vector.map (Expression.eval env'.toEnvironment) x := by
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_map]
  rw [ProvableType.getElem_eval_fields_prover (env := env) x i hi,
    ProvableType.getElem_eval_fields_prover (env := env') x i hi]
  exact congrArg (fun y : MulModTargetT.TargetVec m (F p) => y[i]'hi) h

omit [Fact p.Prime] [NeZero m] in
private lemma bits_of_lt_eight3 : ∀ q : ℕ, q < 8 →
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
/-- Widened (`<3p` operand) fork of `MulModTargetT.soundness_core_t`. The `b` limbs may be
`< 3·2^B`, the V-side coefficient bound is `(3m+1)·2^(2B)`. VR side is unchanged. -/
lemma soundness_core_t3 {B : ℕ} (hB3 : 3 ≤ B)
    (hp : 2 ^ (2 * B) * (4 * m + 1) * 8 < p)
    (i₀ : ℕ) (env : Environment (F p))
    (a b n : Var (BigInt m) (F p))
    (c : Vector (F p) (2 * m))
    (Pv Tv : Vector (Expression (F p)) (2 * m - 1))
    (qh : Expression (F p))
    (av bv nv : BigInt m (F p))
    (ha_input : Vector.map (Expression.eval env) a = av)
    (hb_input : Vector.map (Expression.eval env) b = bv)
    (hn_input : Vector.map (Expression.eval env) n = nv)
    (ha_norm : BigInt.Normalized B av)
    (hb_limb : ∀ i : Fin m, (bv[i.val]).val < 3 * 2 ^ B)
    (hn_norm : BigInt.Normalized B nv)
    (hc_limb : ∀ j : Fin (2 * m), (c[j.val]).val < 4 * 2 ^ B)
    (hc_val : polyValue B c = 3 * (BigInt.value B nv * BigInt.value B nv))
    (hq_norm : BigInt.Normalized B (Vector.map (Expression.eval env)
        (Vector.mapRange m fun i ↦ var { index := i₀ + i })))
    (hqh_lt : (Expression.eval env qh).val < 8)
    (hT_bound : ∀ j : Fin (2 * m - 1),
      (Expression.eval env Tv[j.val]).val < 3 * m * 2 ^ (2 * B))
    (heqAB_get : ∀ k : Fin (2 * m - 1),
      Expression.eval env Pv[k.val] = Expression.eval env (bigIntMulNoReduce a b)[k.val])
    (h_eq_impl :
      ((∀ k : Fin (2 * m),
          (Expression.eval env ((lVecW Pv c)[k.val])).val
            < (3 * m + 1) * 2 ^ (2 * B)) ∧
        ∀ k : Fin (2 * m),
          (Expression.eval env
            ((sVecTD (sVecT (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n Tv)
              qh n)[k.val])).val
            < (4 * m + 1) * 2 ^ (2 * B)) →
        polyValue B (Vector.map (Expression.eval env) (lVecW Pv c)) =
          polyValue B (Vector.map (Expression.eval env)
            (sVecTD (sVecT (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n Tv)
              qh n))) :
    polyValue B (Vector.map (Expression.eval env) Tv) % BigInt.value B nv
      = BigInt.value B av * BigInt.value B bv % BigInt.value B nv := by
  set qVar := (Vector.mapRange m fun i ↦ var (F := F p) { index := i₀ + i }) with hqVar
  have hm : 0 < m := Nat.pos_of_neZero m
  have hB2 : 2 ≤ B := by omega
  have h2B : 2 ^ B * 2 ^ B = 2 ^ (2 * B) := by rw [two_mul, pow_add]
  have h64 : (64 : ℕ) ≤ 2 ^ (2 * B) := by
    calc (64 : ℕ) = 2 ^ 6 := by norm_num
      _ ≤ 2 ^ (2 * B) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hbig : 2 ^ (2 * B) * (4 * m + 1) * 8 ≥ 40 * 2 ^ (2 * B) := by nlinarith
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
  have hb_lt : ∀ i : Fin m, (Expression.eval env b[i.val]).val < 3 * 2 ^ B := by
    intro i; rw [show Expression.eval env b[i.val] = bv[i.val] from by
      rw [← hb_input]; simp only [Vector.getElem_map]]; exact hb_limb i
  have hn_lt : ∀ i : Fin m, (Expression.eval env n[i.val]).val < 2 ^ B := by
    intro i; rw [show Expression.eval env n[i.val] = nv[i.val] from by
      rw [← hn_input]; simp only [Vector.getElem_map]]; exact hn_norm i
  have hqd_lt : ∀ i : Fin m, (Expression.eval env qVar[i.val]).val < 2 ^ B := by
    intro i; have := hq_norm i
    rwa [Fin.getElem_fin, Vector.getElem_map] at this
  -- field bounds
  have hfield : m * (2 ^ B * 2 ^ B) < p := by
    rw [h2B]
    nlinarith [Nat.two_pow_pos (2 * B)]
  have hfield2 : m * (2 ^ B * (3 * 2 ^ B)) < p := by
    have h1 : m * (2 ^ B * (3 * 2 ^ B)) = 3 * (m * 2 ^ (2 * B)) := by
      rw [two_mul B, pow_add]; ring
    rw [h1]
    nlinarith [Nat.two_pow_pos (2 * B)]
  have hp4 : m * 2 ^ (2 * B) + 3 * m * 2 ^ (2 * B) < p := by
    have hEq : m * 2 ^ (2 * B) + 3 * m * 2 ^ (2 * B) = 4 * (m * 2 ^ (2 * B)) := by ring
    rw [hEq]
    nlinarith [Nat.two_pow_pos (2 * B)]
  -- Pv coefficient bound (via the a·b bridge)
  have hPv_fine : ∀ j : Fin (2 * m - 1),
      (Expression.eval env Pv[j.val]).val < 3 * (m * 2 ^ (2 * B)) := by
    intro j
    rw [heqAB_get j]
    have hh := val_coeff_lt_gen env a b j ha_lt hb_lt hfield2
    have hx2 : m * (2 ^ B * (3 * 2 ^ B)) = 3 * (m * 2 ^ (2 * B)) := by
      rw [two_mul B, pow_add]; ring
    rw [hx2] at hh
    exact hh
  -- sVecT fine bound
  have hS_fine : ∀ j : Fin (2 * m - 1),
      (Expression.eval env ((sVecT qVar n Tv)[j.val])).val
        < m * 2 ^ (2 * B) + 3 * (m * 2 ^ (2 * B)) :=
    fun j => coeff_sVecT_bound env qVar n Tv j hqd_lt hn_lt hT_bound hfield
  -- discharge the grouped-equality obligations
  have h_polyeq := h_eq_impl ⟨fun k => by
      have hcap := coeff_lVecW_bound (Cv := 3 * (m * 2 ^ (2 * B))) (Cc := 4 * 2 ^ B)
        env Pv c k (by positivity) hPv_fine hc_limb
      have hexp : (3 * m + 1) * 2 ^ (2 * B)
          = 3 * (m * 2 ^ (2 * B)) + 2 ^ (2 * B) := by ring
      omega,
    fun k => by
      have hcap := coeff_sVecTD_bound8 (Cb := m * 2 ^ (2 * B) + 3 * (m * 2 ^ (2 * B)))
        env (sVecT qVar n Tv) qh n k (by positivity) hS_fine hqh_lt hn_lt
      have hexp : (4 * m + 1) * 2 ^ (2 * B)
          = m * 2 ^ (2 * B) + 3 * (m * 2 ^ (2 * B)) + 2 ^ (2 * B) := by ring
      omega⟩
  -- split both sides
  rw [polyValue_lVecW (Cv := 3 * (m * 2 ^ (2 * B))) (Cc := 4 * 2 ^ B)
    env Pv c hPv_fine hc_limb (by nlinarith [Nat.two_pow_pos (2 * B)])] at h_polyeq
  rw [polyValue_sVecTD8 (Cb := m * 2 ^ (2 * B) + 3 * (m * 2 ^ (2 * B)))
    env (sVecT qVar n Tv) qh n (by positivity) hS_fine hqh_lt hn_lt
    (by nlinarith [Nat.two_pow_pos (2 * B)])] at h_polyeq
  rw [polyValue_sVecT env qVar n Tv hqd_lt hn_lt hT_bound hfield hp4] at h_polyeq
  -- identify the convolution values
  have hPv_map : Vector.map (Expression.eval env) Pv
      = Vector.map (Expression.eval env) (bigIntMulNoReduce a b) := by
    apply Vector.ext; intro k hk
    rw [Vector.getElem_map, Vector.getElem_map]
    exact heqAB_get ⟨k, hk⟩
  have hP : polyValue B (Vector.map (Expression.eval env) (bigIntMulNoReduce a b))
      = BigInt.value B av * BigInt.value B bv := by
    rw [polyValue_mul_eq_gen env a b ha_lt hb_lt hfield2, ha_input, hb_input]
  have hSqn : polyValue B (Vector.map (Expression.eval env) (bigIntMulNoReduce qVar n))
      = BigInt.value B (Vector.map (Expression.eval env) qVar) * BigInt.value B nv := by
    rw [polyValue_Sqn_eq env qVar n hqd_lt hn_lt hfield, ← hn_input]
  rw [hPv_map, hP, hc_val, hSqn, hn_input] at h_polyeq
  -- assemble the wide-target integer identity
  set qlo := BigInt.value B (Vector.map (Expression.eval env) qVar) with hqlo
  set qhv := (Expression.eval env qh).val with hqhv
  have heq : BigInt.value B av * BigInt.value B bv
        + 3 * (BigInt.value B nv * BigInt.value B nv)
      = (qlo + qhv * 2 ^ (B * m)) * BigInt.value B nv
        + polyValue B (Vector.map (Expression.eval env) Tv) := by
    have hring : (qlo + qhv * 2 ^ (B * m)) * BigInt.value B nv
        = qlo * BigInt.value B nv + qhv * 2 ^ (B * m) * BigInt.value B nv := by ring
    omega
  exact congruence_of_offset_eqW heq


set_option maxHeartbeats 1600000 in
/-- Widened (`<3p` operand) fork of `MulModTargetT.completeness_core_t`. -/
lemma completeness_core_t3 {B : ℕ} (hB : 2 ^ B < p) (hB3 : 3 ≤ B)
    (hp : 2 ^ (2 * B) * (4 * m + 1) * 8 < p)
    (i₀ : ℕ) (env : Environment (F p))
    (a b n : Var (BigInt m) (F p))
    (c : Vector (F p) (2 * m))
    (Pv Tv : Vector (Expression (F p)) (2 * m - 1))
    (av bv nv : BigInt m (F p))
    (ha_input : Vector.map (Expression.eval env) a = av)
    (hb_input : Vector.map (Expression.eval env) b = bv)
    (hn_input : Vector.map (Expression.eval env) n = nv)
    (ha_norm : BigInt.Normalized B av)
    (hb_limb : ∀ i : Fin m, (bv[i.val]).val < 3 * 2 ^ B)
    (hn_norm : BigInt.Normalized B nv)
    (hc_limb : ∀ j : Fin (2 * m), (c[j.val]).val < 4 * 2 ^ B)
    (hc_val : polyValue B c = 3 * (BigInt.value B nv * BigInt.value B nv))
    (hab_lt : BigInt.value B av < BigInt.value B nv)
    (hbb_lt : BigInt.value B bv < 3 * BigInt.value B nv)
    (hn_pos : 0 < BigInt.value B nv)
    (hn8D : 6 * BigInt.value B nv ≤ 2 ^ (B * m + 3))
    (hT_bound : ∀ j : Fin (2 * m - 1),
      (Expression.eval env Tv[j.val]).val < 3 * m * 2 ^ (2 * B))
    (hT_le : polyValue B (Vector.map (Expression.eval env) Tv)
      ≤ 3 * (BigInt.value B nv * BigInt.value B nv))
    (h_spec : polyValue B (Vector.map (Expression.eval env) Tv) % BigInt.value B nv
      = BigInt.value B av * BigInt.value B bv % BigInt.value B nv)
    (hqwit : ∀ i : Fin m, env.get (i₀ + i.val)
      = (((BigInt.value B av * BigInt.value B bv
            + 3 * (BigInt.value B nv * BigInt.value B nv)
            - polyValue B (Vector.map (Expression.eval env) Tv)) / BigInt.value B nv
          % 2 ^ (B * m) / 2 ^ (B * i.val) % 2 ^ B : ℕ) : F p))
    (hqh0wit : env.get (i₀ + m)
      = ((((BigInt.value B av * BigInt.value B bv
            + 3 * (BigInt.value B nv * BigInt.value B nv)
            - polyValue B (Vector.map (Expression.eval env) Tv)) / BigInt.value B nv
          / 2 ^ (B * m)) % 2 : ℕ) : F p))
    (hqh1wit : env.get (i₀ + m + 1)
      = ((((BigInt.value B av * BigInt.value B bv
            + 3 * (BigInt.value B nv * BigInt.value B nv)
            - polyValue B (Vector.map (Expression.eval env) Tv)) / BigInt.value B nv
          / 2 ^ (B * m) / 2) % 2 : ℕ) : F p))
    (hqh2wit : env.get (i₀ + m + 2)
      = ((((BigInt.value B av * BigInt.value B bv
            + 3 * (BigInt.value B nv * BigInt.value B nv)
            - polyValue B (Vector.map (Expression.eval env) Tv)) / BigInt.value B nv
          / 2 ^ (B * m) / 4) % 2 : ℕ) : F p))
    (heqAB_get : ∀ k : Fin (2 * m - 1),
      Expression.eval env Pv[k.val] = Expression.eval env (bigIntMulNoReduce a b)[k.val]) :
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
            < (3 * m + 1) * 2 ^ (2 * B)) ∧
        ∀ k : Fin (2 * m),
          (Expression.eval env
            ((sVecTD (sVecT (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n Tv)
              (var (F := F p) { index := i₀ + m }
                + ((2 : F p) : Expression (F p)) * var { index := i₀ + m + 1 }
                + ((4 : F p) : Expression (F p)) * var { index := i₀ + m + 2 })
              n)[k.val])).val
            < (4 * m + 1) * 2 ^ (2 * B))
    ∧ polyValue B (Vector.map (Expression.eval env) (lVecW Pv c)) =
        polyValue B (Vector.map (Expression.eval env)
          (sVecTD (sVecT (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n Tv)
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
  set tval := polyValue B (Vector.map (Expression.eval env) Tv) with ht_def
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
  have ht_le : tval ≤ aval * bval + 3 * (nval * nval) := by omega
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
  -- the wide quotient bound: q < 6n ≤ 2^(Bm+3)
  have hqval_lt : qval < 2 ^ (B * m + 3) := by
    have hq_le : qval ≤ (aval * bval + 3 * (nval * nval)) / nval :=
      Nat.div_le_div_right (Nat.sub_le _ _)
    have hq_lt : (aval * bval + 3 * (nval * nval)) / nval < 6 * nval := by
      apply Nat.div_lt_of_lt_mul
      have hab : aval * bval < nval * (3 * nval) := by
        rcases Nat.eq_zero_or_pos bval with hb0 | hb0
        · rw [hb0, Nat.mul_zero]; positivity
        · calc aval * bval < nval * bval := by
                apply (Nat.mul_lt_mul_right hb0).mpr hab_lt
            _ ≤ nval * (3 * nval) := by apply Nat.mul_le_mul_left; omega
      calc aval * bval + 3 * (nval * nval) < nval * (3 * nval) + 3 * (nval * nval) := by omega
        _ = nval * (6 * nval) := by ring
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
    bits_of_lt_eight3 qhn (by omega)
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
  have hb_lt : ∀ i : Fin m, (Expression.eval env b[i.val]).val < 3 * 2 ^ B := by
    intro i; rw [show Expression.eval env b[i.val] = bv[i.val] from by
      rw [← hb_input]; simp only [Vector.getElem_map]]; exact hb_limb i
  have hn_lt : ∀ i : Fin m, (Expression.eval env n[i.val]).val < 2 ^ B := by
    intro i; rw [show Expression.eval env n[i.val] = nv[i.val] from by
      rw [← hn_input]; simp only [Vector.getElem_map]]; exact hn_norm i
  have hqd_lt : ∀ i : Fin m, (Expression.eval env qVar[i.val]).val < 2 ^ B := by
    intro i; have := hqv_norm i
    rwa [Fin.getElem_fin, Vector.getElem_map] at this
  -- field bounds
  have hfield : m * (2 ^ B * 2 ^ B) < p := by
    rw [h2B]
    nlinarith [Nat.two_pow_pos (2 * B)]
  have hfield2 : m * (2 ^ B * (3 * 2 ^ B)) < p := by
    have h1 : m * (2 ^ B * (3 * 2 ^ B)) = 3 * (m * 2 ^ (2 * B)) := by
      rw [two_mul B, pow_add]; ring
    rw [h1]
    nlinarith [Nat.two_pow_pos (2 * B)]
  have hp4 : m * 2 ^ (2 * B) + 3 * m * 2 ^ (2 * B) < p := by
    have hEq : m * 2 ^ (2 * B) + 3 * m * 2 ^ (2 * B) = 4 * (m * 2 ^ (2 * B)) := by ring
    rw [hEq]
    nlinarith [Nat.two_pow_pos (2 * B)]
  -- coefficient bounds
  have hPv_fine : ∀ j : Fin (2 * m - 1),
      (Expression.eval env Pv[j.val]).val < 3 * (m * 2 ^ (2 * B)) := by
    intro j
    rw [heqAB_get j]
    have hh := val_coeff_lt_gen env a b j ha_lt hb_lt hfield2
    have hx2 : m * (2 ^ B * (3 * 2 ^ B)) = 3 * (m * 2 ^ (2 * B)) := by
      rw [two_mul B, pow_add]; ring
    rw [hx2] at hh
    exact hh
  have hS_fine : ∀ j : Fin (2 * m - 1),
      (Expression.eval env ((sVecT qVar n Tv)[j.val])).val
        < m * 2 ^ (2 * B) + 3 * (m * 2 ^ (2 * B)) :=
    fun j => coeff_sVecT_bound env qVar n Tv j hqd_lt hn_lt hT_bound hfield
  -- the obligations
  have hobl : (∀ k : Fin (2 * m),
      (Expression.eval env ((lVecW Pv c)[k.val])).val
        < (3 * m + 1) * 2 ^ (2 * B)) ∧
      ∀ k : Fin (2 * m),
        (Expression.eval env ((sVecTD (sVecT qVar n Tv) qhW n)[k.val])).val
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
    · have hcap := coeff_lVecW_bound (Cv := 3 * (m * 2 ^ (2 * B))) (Cc := 4 * 2 ^ B)
        env Pv c k (by positivity) hPv_fine hc_limb
      have hexp : (3 * m + 1) * 2 ^ (2 * B)
          = 3 * (m * 2 ^ (2 * B)) + 2 ^ (2 * B) := by ring
      omega
    · have hcap := coeff_sVecTD_bound8 (Cb := m * 2 ^ (2 * B) + 3 * (m * 2 ^ (2 * B)))
        env (sVecT qVar n Tv) qhW n k (by positivity) hS_fine hqh_lt hn_lt
      have hexp : (4 * m + 1) * 2 ^ (2 * B)
          = m * 2 ^ (2 * B) + 3 * (m * 2 ^ (2 * B)) + 2 ^ (2 * B) := by ring
      omega
  -- the value equation
  have hval : polyValue B (Vector.map (Expression.eval env) (lVecW Pv c)) =
      polyValue B (Vector.map (Expression.eval env)
        (sVecTD (sVecT qVar n Tv) qhW n)) := by
    rw [polyValue_lVecW (Cv := 3 * (m * 2 ^ (2 * B))) (Cc := 4 * 2 ^ B)
      env Pv c hPv_fine hc_limb (by nlinarith [Nat.two_pow_pos (2 * B)])]
    rw [polyValue_sVecTD8 (Cb := m * 2 ^ (2 * B) + 3 * (m * 2 ^ (2 * B)))
      env (sVecT qVar n Tv) qhW n (by positivity) hS_fine hqh_lt hn_lt
      (by nlinarith [Nat.two_pow_pos (2 * B)])]
    rw [polyValue_sVecT env qVar n Tv hqd_lt hn_lt hT_bound hfield hp4]
    rw [← ht_def]
    have hPv_map : Vector.map (Expression.eval env) Pv
        = Vector.map (Expression.eval env) (bigIntMulNoReduce a b) := by
      apply Vector.ext; intro k hk
      rw [Vector.getElem_map, Vector.getElem_map]
      exact heqAB_get ⟨k, hk⟩
    have hP : polyValue B (Vector.map (Expression.eval env) (bigIntMulNoReduce a b))
        = aval * bval := by
      rw [polyValue_mul_eq_gen env a b ha_lt hb_lt hfield2, ha_input, hb_input]
    have hSqn : polyValue B (Vector.map (Expression.eval env) (bigIntMulNoReduce qVar n))
        = qlo * nval := by
      rw [polyValue_Sqn_eq env qVar n hqd_lt hn_lt hfield, hqv_val, hn_input]
    rw [hPv_map, hP, hc_val, hSqn, hqhv_val, hn_input]
    rw [← hn_def]
    rw [hdecomp] at hkey
    have hring : (qlo + qhn * 2 ^ (B * m)) * nval
        = qlo * nval + qhn * 2 ^ (B * m) * nval := by ring
    omega
  refine ⟨hqv_norm, ?_, ?_, ?_, hobl, hval⟩
  · rw [hq0_eval]; exact hbool _ (by omega)
  · rw [hq1_eval]; exact hbool _ (by omega)
  · rw [hq2_eval]; exact hbool _ (by omega)


/-- Widened assumptions: `b` limbs `< 3·2^B`, `b < 3n`, quotient slack `6n`. -/
def Assumptions3 (B : ℕ) (c : Vector (F p) (2 * m))
    (input : MulModTargetT.Inputs m (F p)) : Prop :=
  input.a.Normalized B ∧
    (∀ i : Fin m, (input.b[i.val]).val < 3 * 2 ^ B) ∧
    input.modulus.Normalized B ∧
    input.a.value B < input.modulus.value B ∧
    input.b.value B < 3 * input.modulus.value B ∧
    0 < input.modulus.value B ∧
    6 * input.modulus.value B ≤ 2 ^ (B * m + 3) ∧
    (∀ j : Fin (2 * m), (c[j.val]).val < 4 * 2 ^ B) ∧
    polyValue B c = 3 * (input.modulus.value B * input.modulus.value B) ∧
    (∀ k : Fin (2 * m - 1), (input.target[k.val]).val < 3 * m * 2 ^ (2 * B)) ∧
    polyValue B input.target ≤ 3 * (input.modulus.value B * input.modulus.value B)


set_option maxHeartbeats 3200000 in
theorem soundness3 (P : BigIntParams p m)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqXV.GVXHyps p (2 * m) P.B gf posOf G V VR)
    (hNf : ∀ j, V.Nf j = (3 * m + 1) * 2 ^ (2 * P.B))
    (hNfR : ∀ j, VR.Nf j = (4 * m + 1) * 2 ^ (2 * P.B))
    (c : Vector (F p) (2 * m))
    (hB3 : 3 ≤ P.B)
    (hp8 : 2 ^ (2 * P.B) * (4 * m + 1) * 8 < p)
    [Fact (p > 2)] :
    FormalAssertion.Soundness (F p) (MulModTargetT.main P gf posOf G V VR hgv c)
      (Assumptions3 P.B c) (MulModTargetT.Spec P.B) := by
  obtain ⟨B, W, hB, hW, hB1, hWB, hWp, hp⟩ := P
  circuit_proof_start [MulModTargetT.main, MulModTargetT.elaborated,
    Normalize.circuit, Normalize.elaborated, Normalize.main,
    Normalize.Assumptions, Normalize.Spec,
    GroupedEqXV.circuit, GroupedEqXV.elaborated,
    GroupedEqXV.Assumptions, GroupedEqX.Spec]
  obtain ⟨ha_norm, hb_limb, hn_norm, hab_lt, hbb_lt, hn_pos,
    hn8D, hc_limb, hc_val, hT_lt, hT_le⟩ := h_assumptions
  obtain ⟨hqh0_zero, hqh1_zero, hqh2_zero, hq_norm, hAB_ops, h_eq_impl⟩ := h_holds
  simp only [hNf, hNfR] at h_eq_impl
  have h8p : 8 < p := by
    have hpos : 0 < 2 ^ (2 * B) * (4 * m + 1) := by positivity
    nlinarith [hp8]
  have h_pAB := interpolatedMul_soundness (i₀ + (m + 3) + m * (B - 1))
    input_var.a input_var.b env hAB_ops
  refine ⟨?_, interpolatedMul_requirements _ _ _ _⟩
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
  have hT_bound : ∀ j : Fin (2 * m - 1),
      (Expression.eval env input_var.target[j.val]).val < 3 * m * 2 ^ (2 * B) := by
    intro j
    have hbridge : Expression.eval env input_var.target[j.val] = input.target[j.val] := by
      rw [← h_input]; simp [Vector.getElem_map]
    rw [hbridge]; exact hT_lt j
  have hcore := soundness_core_t3 (B := B) hB3 hp8 i₀ env
    input_var.a input_var.b input_var.modulus c
    (interpolatedMul input_var.a input_var.b (i₀ + (m + 3) + m * (B - 1))).1
    input_var.target
    (var { index := i₀ + m }
      + ((2 : F p) : Expression (F p)) * var { index := i₀ + m + 1 }
      + ((4 : F p) : Expression (F p)) * var { index := i₀ + m + 2 })
    input.a input.b input.modulus
    ha_input hb_input hn_input
    ha_norm hb_limb
    hn_norm hc_limb hc_val hq_norm hqh_lt hT_bound heqAB_get h_eq_impl
  rw [hx_input] at hcore
  exact hcore


set_option maxHeartbeats 3200000 in
theorem completeness3 (P : BigIntParams p m)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqXV.GVXHyps p (2 * m) P.B gf posOf G V VR)
    (hNf : ∀ j, V.Nf j = (3 * m + 1) * 2 ^ (2 * P.B))
    (hNfR : ∀ j, VR.Nf j = (4 * m + 1) * 2 ^ (2 * P.B))
    (c : Vector (F p) (2 * m))
    (hB3 : 3 ≤ P.B)
    (hp8 : 2 ^ (2 * P.B) * (4 * m + 1) * 8 < p)
    [Fact (p > 2)] :
    FormalAssertion.Completeness (F p) (MulModTargetT.main P gf posOf G V VR hgv c)
      (Assumptions3 P.B c) (MulModTargetT.Spec P.B) := by
  obtain ⟨B, W, hB, hW, hB1, hWB, hWp, hp⟩ := P
  circuit_proof_start [MulModTargetT.main, MulModTargetT.elaborated,
    Normalize.circuit, Normalize.elaborated, Normalize.main,
    Normalize.Assumptions, Normalize.Spec,
    GroupedEqXV.circuit, GroupedEqXV.elaborated,
    GroupedEqXV.Assumptions, GroupedEqX.Spec]
  obtain ⟨ha_norm, hb_limb, hn_norm, hab_lt, hbb_lt, hn_pos,
    hn8D, hc_limb, hc_val, hT_lt, hT_le⟩ := h_assumptions
  obtain ⟨hq_env, hqh0_env, hqh1_env, hqh2_env, hAB_uses⟩ := h_env
  have h_pvAB := interpolatedMul_usesLocalWitnesses (i₀ + (m + 3) + m * (B - 1))
    (i₀ + (m + 3) + m * (B - 1)) input_var.a input_var.b env rfl hAB_uses
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
  have hqwit : ∀ i : Fin m, env.toEnvironment.get (i₀ + i.val)
      = (((BigInt.value B input.a * BigInt.value B input.b
            + 3 * (BigInt.value B input.modulus * BigInt.value B input.modulus)
            - polyValue B (Vector.map (Expression.eval env.toEnvironment) input_var.target))
          / BigInt.value B input.modulus % 2 ^ (B * m)
          / 2 ^ (B * i.val) % 2 ^ B : ℕ) : F p) := by
    intro i; rw [hq_env i, Vector.getElem_ofFn, heva, hevb, hevn]
  have hqh0wit : env.toEnvironment.get (i₀ + m)
      = ((((BigInt.value B input.a * BigInt.value B input.b
            + 3 * (BigInt.value B input.modulus * BigInt.value B input.modulus)
            - polyValue B (Vector.map (Expression.eval env.toEnvironment) input_var.target))
          / BigInt.value B input.modulus / 2 ^ (B * m)) % 2 : ℕ) : F p) := by
    rw [hqh0_env, heva, hevb, hevn]
  have hqh1wit : env.toEnvironment.get (i₀ + m + 1)
      = ((((BigInt.value B input.a * BigInt.value B input.b
            + 3 * (BigInt.value B input.modulus * BigInt.value B input.modulus)
            - polyValue B (Vector.map (Expression.eval env.toEnvironment) input_var.target))
          / BigInt.value B input.modulus / 2 ^ (B * m) / 2) % 2 : ℕ) : F p) := by
    rw [hqh1_env, heva, hevb, hevn]
  have hqh2wit : env.toEnvironment.get (i₀ + m + 2)
      = ((((BigInt.value B input.a * BigInt.value B input.b
            + 3 * (BigInt.value B input.modulus * BigInt.value B input.modulus)
            - polyValue B (Vector.map (Expression.eval env.toEnvironment) input_var.target))
          / BigInt.value B input.modulus / 2 ^ (B * m) / 4) % 2 : ℕ) : F p) := by
    rw [hqh2_env, heva, hevb, hevn]
  have heqAB_get := interpolatedMul_eval_bridge_uses env.toEnvironment
    (i₀ + (m + 3) + m * (B - 1)) input_var.a input_var.b h_pvAB
  have hT_bound : ∀ j : Fin (2 * m - 1),
      (Expression.eval env.toEnvironment input_var.target[j.val]).val
        < 3 * m * 2 ^ (2 * B) := by
    intro j
    have hbridge : Expression.eval env.toEnvironment input_var.target[j.val]
        = input.target[j.val] := by
      rw [← h_input]; simp [Vector.getElem_map]
    rw [hbridge]; exact hT_lt j
  have hT_le' : polyValue B (Vector.map (Expression.eval env.toEnvironment) input_var.target)
      ≤ 3 * (BigInt.value B input.modulus * BigInt.value B input.modulus) := by
    rw [hx_input]; exact hT_le
  have h_spec' : polyValue B (Vector.map (Expression.eval env.toEnvironment) input_var.target)
        % BigInt.value B input.modulus
      = BigInt.value B input.a * BigInt.value B input.b % BigInt.value B input.modulus := by
    rw [hx_input]; exact h_spec
  have core := completeness_core_t3 (B := B) hB hB3 hp8 i₀ env.toEnvironment
    input_var.a input_var.b input_var.modulus c
    (interpolatedMul input_var.a input_var.b (i₀ + (m + 3) + m * (B - 1))).1
    input_var.target
    input.a input.b input.modulus
    ha_input hb_input hn_input
    ha_norm hb_limb
    hn_norm hc_limb hc_val
    hab_lt hbb_lt hn_pos hn8D hT_bound hT_le' h_spec'
    hqwit hqh0wit hqh1wit hqh2wit heqAB_get
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
    core.2.2.2.2⟩


set_option maxHeartbeats 3200000 in
def circuit3 (P : BigIntParams p m)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqXV.GVXHyps p (2 * m) P.B gf posOf G V VR)
    (hNf : ∀ j, V.Nf j = (3 * m + 1) * 2 ^ (2 * P.B))
    (hNfR : ∀ j, VR.Nf j = (4 * m + 1) * 2 ^ (2 * P.B))
    (c : Vector (F p) (2 * m))
    (hB3 : 3 ≤ P.B)
    (hp8 : 2 ^ (2 * P.B) * (4 * m + 1) * 8 < p)
    [Fact (p > 2)] :
    FormalAssertion (F p) (MulModTargetT.Inputs m) where
    main := MulModTargetT.main P gf posOf G V VR hgv c
    Assumptions := Assumptions3 P.B c
    Spec := MulModTargetT.Spec P.B
    soundness := soundness3 P gf posOf G V VR hgv hNf hNfR c hB3 hp8
    completeness := completeness3 P gf posOf G V VR hgv hNf hNfR c hB3 hp8


attribute [local irreducible] interpolatedMul Normalize.circuit GroupedEqXV.circuit

-- `ComputableWitnesses` depends only on `main`, which `circuit3` shares with
-- `MulModTargetT.circuit`. We cannot reuse `MulModTargetT.computableWitnesses` directly (its `hNf`
-- argument has the `2·((m+1)·…)` shape, false for the widened `V`), so we port its proof body;
-- the private helpers it uses are brought into scope by the `open private` above.
theorem computableWitnesses3 (P : BigIntParams p m)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqXV.GVXHyps p (2 * m) P.B gf posOf G V VR)
    (hNf : ∀ j, V.Nf j = (3 * m + 1) * 2 ^ (2 * P.B))
    (hNfR : ∀ j, VR.Nf j = (4 * m + 1) * 2 ^ (2 * P.B))
    (c : Vector (F p) (2 * m))
    (hB3 : 3 ≤ P.B)
    (hp8 : 2 ^ (2 * P.B) * (4 * m + 1) * 8 < p)
    [Fact (p > 2)] :
    (circuit3 P gf posOf G V VR hgv hNf hNfR c hB3 hp8).ComputableWitnesses := by
  letI : NeZero (2 * m) := ⟨by have := Nat.pos_of_neZero m; omega⟩
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition input env env')
    ((MulModTargetT.main P gf posOf G V VR hgv c input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold MulModTargetT.main
  let qwit : ProverEnvironment (F p) → ℕ := fun env =>
    (evalValue P.B env input.a * evalValue P.B env input.b
        + 3 * (evalValue P.B env input.modulus * evalValue P.B env input.modulus)
        - polyValue P.B (Vector.map (Expression.eval env.toEnvironment) input.target))
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
  let eqOff := pcOff + (interpolatedMul input.a input.b).localLength pcOff
  have h_qlen : qc.localLength offset = m := by
    simp [qc, ProvableType.witness, Circuit.localLength, Operations.localLength, size]
  have h_pclen : (interpolatedMul input.a input.b).localLength pcOff = 2 * m - 1 :=
    interpolatedMul_localLength pcOff input.a input.b
  have hstable4 : ∀ (env env' : ProverEnvironment (F p)),
      eval env input = eval env' input →
      evalValue P.B env input.a = evalValue P.B env' input.a
      ∧ evalValue P.B env input.b = evalValue P.B env' input.b
      ∧ evalValue P.B env input.modulus = evalValue P.B env' input.modulus
      ∧ polyValue P.B (Vector.map (Expression.eval env.toEnvironment) input.target)
        = polyValue P.B (Vector.map (Expression.eval env'.toEnvironment) input.target) := by
    intro env env' h_input
    refine ⟨evalValue_stable3 P.B input.a (by
        simpa [circuit_norm] using congrArg (fun x : MulModTargetT.Inputs m (F p) => x.a) h_input),
      evalValue_stable3 P.B input.b (by
        simpa [circuit_norm] using congrArg (fun x : MulModTargetT.Inputs m (F p) => x.b) h_input),
      evalValue_stable3 P.B input.modulus (by
        simpa [circuit_norm] using congrArg
          (fun x : MulModTargetT.Inputs m (F p) => x.modulus) h_input),
      ?_⟩
    refine congrArg (polyValue P.B) (target_map_stable3 input.target ?_)
    simpa [circuit_norm] using congrArg (fun x : MulModTargetT.Inputs m (F p) => x.target) h_input
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.provableWitness_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.assertZero_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_structuralComputableWitnesses_iff]
  and_intros
  · intro _ h_input
    obtain ⟨ha, hb, hn, ht⟩ := hstable4 _ _ h_input
    simp only [ha, hb, hn, ht]
  · intro _ h_input
    obtain ⟨ha, hb, hn, ht⟩ := hstable4 _ _ h_input
    simp only [ha, hb, hn, ht]
  · intro _ h_input
    obtain ⟨ha, hb, hn, ht⟩ := hstable4 _ _ h_input
    simp only [ha, hb, hn, ht]
  · intro _ h_input
    obtain ⟨ha, hb, hn, ht⟩ := hstable4 _ _ h_input
    simp only [ha, hb, hn, ht]
  · trivial
  · trivial
  · trivial
  · exact Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
      (Normalize.circuit P) input q nqOff
      (by
        intro k env env' hle h_agree _
        have hk : offset + m ≤ k := by
          dsimp only [nqOff, qh2Off, qh1Off, qh0Off] at hle
          rw [h_qlen] at hle
          omega
        exact bigIntWitnessOutput_stable _ h_agree hk)
      (Normalize.computableWitnesses P) env env'
  · exact interpolatedMul_structuralComputableWitnesses input input.a input.b pcOff
      (by
        intro k env env' _ _ h_input
        have ha : eval env input.a = eval env' input.a := by
          simpa [circuit_norm] using congrArg (fun x : MulModTargetT.Inputs m (F p) => x.a) h_input
        have hb : eval env input.b = eval env' input.b := by
          simpa [circuit_norm] using congrArg (fun x : MulModTargetT.Inputs m (F p) => x.b) h_input
        exact ⟨ha, hb⟩)
      env env'
  · exact Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
      (GroupedEqXV.circuit P.B gf posOf G V VR hgv P.hB1) input
      { lhs := lVecW pcv c,
        rhs := sVecTD (sVecT q input.modulus input.target)
          (qh0 + ((2 : F p) : Expression (F p)) * qh1
            + ((4 : F p) : Expression (F p)) * qh2) input.modulus }
      eqOff
      (by
        intro k env env' hle h_agree h_input
        have hk_pc : pcOff + (2 * m - 1) ≤ k := by
          have h := hle
          dsimp only [eqOff] at h
          rw [h_pclen] at h
          exact h
        have hk_q : offset + m ≤ k := by
          have h := hle
          dsimp only [eqOff, pcOff, nqOff, qh2Off, qh1Off, qh0Off] at h
          rw [h_qlen] at h
          omega
        have hk_bits : offset + m + 3 ≤ k := by
          have h := hle
          dsimp only [eqOff, pcOff, nqOff, qh2Off, qh1Off, qh0Off] at h
          rw [h_qlen] at h
          omega
        have hPc : Vector.map (Expression.eval env.toEnvironment) pcv
            = Vector.map (Expression.eval env'.toEnvironment) pcv :=
          interpolatedMul_output_stable pcOff input.a input.b h_agree hk_pc
        have hq_vec : eval env q = eval env' q := bigIntWitnessOutput_stable _ h_agree hk_q
        have hx_map : Vector.map (Expression.eval env.toEnvironment) input.target
            = Vector.map (Expression.eval env'.toEnvironment) input.target := by
          refine target_map_stable3 input.target ?_
          simpa [circuit_norm] using congrArg (fun x : MulModTargetT.Inputs m (F p) => x.target) h_input
        have hbit_eval : ∀ j : ℕ, j < 3 →
            env.get (offset + m + j) = env'.get (offset + m + j) := by
          intro j hj
          apply h_agree (offset + m + j)
          omega
        have hn : eval env input.modulus = eval env' input.modulus := by
          simpa [circuit_norm] using congrArg
            (fun x : MulModTargetT.Inputs m (F p) => x.modulus) h_input
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
              (sVecTD (sVecT q input.modulus input.target)
                (qh0 + ((2 : F p) : Expression (F p)) * qh1
                  + ((4 : F p) : Expression (F p)) * qh2) input.modulus)
            = Vector.map (Expression.eval env'.toEnvironment)
              (sVecTD (sVecT q input.modulus input.target)
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
            have hT_i : Expression.eval env.toEnvironment (input.target[i]'hlt)
                = Expression.eval env'.toEnvironment (input.target[i]'hlt) := by
              have := congrArg (fun v : Vector (F p) (2 * m - 1) => v[i]'hlt) hx_map
              simpa only [Vector.getElem_map] using this
            simp only [MulModTargetT.sVecT, Vector.getElem_mapFinRange]
            rw [show Expression.eval env.toEnvironment
                  ((bigIntMulNoReduce q input.modulus)[i]'hlt + input.target[i]'hlt)
                  = Expression.eval env.toEnvironment
                      ((bigIntMulNoReduce q input.modulus)[i]'hlt)
                    + Expression.eval env.toEnvironment (input.target[i]'hlt) from rfl,
              show Expression.eval env'.toEnvironment
                  ((bigIntMulNoReduce q input.modulus)[i]'hlt + input.target[i]'hlt)
                  = Expression.eval env'.toEnvironment
                      ((bigIntMulNoReduce q input.modulus)[i]'hlt)
                    + Expression.eval env'.toEnvironment (input.target[i]'hlt) from rfl,
              hsq_i, hT_i]
          simp only [Vector.getElem_map, MulModTargetD.sVecTD, Vector.getElem_mapFinRange]
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
                    ((sVecT q input.modulus input.target)[i]'hlt
                      + qhE * input.modulus[i - m]'hm'.2)
                    = Expression.eval env.toEnvironment
                        ((sVecT q input.modulus input.target)[i]'hlt)
                      + Expression.eval env.toEnvironment (qhE * input.modulus[i - m]'hm'.2)
                    from rfl,
                show Expression.eval env'.toEnvironment
                    ((sVecT q input.modulus input.target)[i]'hlt
                      + qhE * input.modulus[i - m]'hm'.2)
                    = Expression.eval env'.toEnvironment
                        ((sVecT q input.modulus input.target)[i]'hlt)
                      + Expression.eval env'.toEnvironment (qhE * input.modulus[i - m]'hm'.2)
                    from rfl,
                hbase_i hlt, hflank_i hm']
            · rw [dif_neg hm']
              rw [eval_add_zero3, eval_add_zero3, hbase_i hlt]
          · rw [dif_neg hlt]
            by_cases hm' : m ≤ i ∧ i - m < m
            · rw [dif_pos hm']
              rw [eval_zero_add3, eval_zero_add3, hflank_i hm']
            · rw [dif_neg hm']
              rfl
        simp only [circuit_norm]
        rw [hL8, hS8])
      (GroupedEqXV.computableWitnesses P.B gf posOf G V VR hgv P.hB1) env env'

end MulModTargetT3
end Solution.Secp256k1ScalarMul
