import Solution.Secp256k1ScalarMul.Params



namespace Solution.Secp256k1ScalarMul
open Solution.Secp256k1ScalarMul.Limbs

namespace ToBytes




theorem two_pow_64_lt_circomPrime : (2 : ℕ) ^ 64 < circomPrime := by decide



section
variable {p : ℕ} [Fact p.Prime]


theorem eval_foldl_add (env : Environment (F p)) (n : ℕ)
    (g : Fin n → Expression (F p)) :
    Expression.eval env (Fin.foldl n (fun acc i => acc + g i) 0)
      = ∑ i : Fin n, Expression.eval env (g i) := by
  induction n with
  | zero => simp [Expression.eval]
  | succ k ih =>
    simp [Fin.foldl_succ_last, Fin.sum_univ_castSucc, Expression.eval, ih]


theorem eval_row_iff (env : Environment (F p)) {n : ℕ}
    (g : Fin n → Expression (F p)) (e : Expression (F p)) :
    Expression.eval env (Fin.foldl n (fun acc i => acc + g i) 0 - e) = 0
      ↔ (∑ i : Fin n, Expression.eval env (g i)) = Expression.eval env e := by
  have hsub : Expression.eval env (Fin.foldl n (fun acc i => acc + g i) 0 - e)
      = Expression.eval env (Fin.foldl n (fun acc i => acc + g i) 0)
        - Expression.eval env e := by
    show Expression.eval env (Expression.add _ (Expression.mul (Expression.const (-1)) e)) = _
    simp only [Expression.eval]
    ring
  rw [hsub, sub_eq_zero, eval_foldl_add]

end




theorem byteSum_eq_limb (v k : ℕ) :
    (∑ t ∈ Finset.range 8, v / 2 ^ (8 * (8 * k + t)) % 256 * 2 ^ (8 * t))
      = v / 2 ^ (64 * k) % 2 ^ 64 := by
  have h : ∀ t, v / 2 ^ (8 * (8 * k + t)) = v / 2 ^ (64 * k) / 2 ^ (8 * t) := by
    intro t
    rw [Nat.div_div_eq_div_mul, ← pow_add]
    congr 1
    ring
  calc (∑ t ∈ Finset.range 8, v / 2 ^ (8 * (8 * k + t)) % 256 * 2 ^ (8 * t))
      = ∑ t ∈ Finset.range 8, v / 2 ^ (64 * k) / 2 ^ (8 * t) % 2 ^ 8 * 2 ^ (8 * t) := by
        apply Finset.sum_congr rfl
        intro t _
        rw [h t]
        norm_num
    _ = v / 2 ^ (64 * k) % 2 ^ (8 * 8) := limb_decomp_mod 8 8 (v / 2 ^ (64 * k))
    _ = v / 2 ^ (64 * k) % 2 ^ 64 := by norm_num


theorem sum_regroup (B n : ℕ) (f : ℕ → ℕ) : ∀ m : ℕ,
    (∑ i ∈ Finset.range (m * n), f i * 2 ^ (B * i))
      = ∑ k ∈ Finset.range m,
          (∑ t ∈ Finset.range n, f (n * k + t) * 2 ^ (B * t)) * 2 ^ (B * n * k) := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ← ih, show (m + 1) * n = m * n + n by ring,
      Finset.sum_range_add]
    congr 1
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro t _
    rw [show n * m + t = m * n + t by ring, mul_assoc, ← pow_add]
    congr 2
    ring


theorem value_limb_eq (x : Emu (F circomPrime)) (hx : x.Normalized limbBits)
    (k : Fin numLimbs) :
    x.value limbBits / 2 ^ (64 * k.val) % 2 ^ 64 = (x[k]).val := by
  rw [BigInt.value_eq_sum]
  have hstep : (∑ j : Fin numLimbs, (x[j]).val * 2 ^ (limbBits * j.val))
      = ∑ j ∈ Finset.range numLimbs,
          (if h : j < numLimbs then (x[j]'h).val else 0) * 2 ^ (64 * j) := by
    rw [← Fin.sum_univ_eq_sum_range
      (fun j => (if h : j < numLimbs then (x[j]'h).val else 0) * 2 ^ (64 * j))]
    apply Finset.sum_congr rfl
    intro j _
    rw [dif_pos j.isLt]
    rfl
  rw [hstep, digit_extract 64 (fun j => if h : j < numLimbs then (x[j]'h).val else 0)
    (by
      intro j
      dsimp only
      by_cases h : j < numLimbs
      · rw [dif_pos h]
        exact hx ⟨j, h⟩
      · rw [dif_neg h]
        exact Nat.two_pow_pos 64)
    numLimbs k.val k.isLt, dif_pos k.isLt]
  rw [Fin.getElem_fin]




theorem soundness_core (env : Environment (F circomPrime)) (i₀ : ℕ)
    (input : Emu (F circomPrime))
    (h_bytes : ∀ i : Fin coordBytes, (env.get (i₀ + i.val)).val < 2 ^ 8)
    (h_rows : ∀ k : Fin numLimbs,
      (∑ t : Fin bytesPerLimb,
          env.get (i₀ + (bytesPerLimb * k.val + t.val))
            * ((2 ^ (8 * t.val) : ℕ) : F circomPrime))
        = input[k.val]'k.isLt) :
    Limbs.fromLimbs 8 (List.map ZMod.val
        (Vector.map (Expression.eval env)
          (Vector.mapRange coordBytes fun i =>
            var (F := F circomPrime) { index := i₀ + i })).toList)
      = BigInt.value limbBits input := by
  -- the LHS is the `BigInt.value 8` of the output vector
  have hval : Limbs.fromLimbs 8 (List.map ZMod.val
        (Vector.map (Expression.eval env)
          (Vector.mapRange coordBytes fun i =>
            var (F := F circomPrime) { index := i₀ + i })).toList)
      = BigInt.value 8 (Vector.map (Expression.eval env)
          (Vector.mapRange coordBytes fun i =>
            var (F := F circomPrime) { index := i₀ + i })) := rfl
  rw [hval, BigInt.value_eq_sum, BigInt.value_eq_sum]
  -- per-index output value: `out[i] = env.get (i₀ + i)`
  have hget : ∀ (i : ℕ) (h : i < coordBytes),
      (Vector.map (Expression.eval env)
        (Vector.mapRange coordBytes fun j =>
          var (F := F circomPrime) { index := i₀ + j }))[i] = env.get (i₀ + i) := by
    intro i h
    simp [circuit_norm]
  -- ℕ-level per-row equations
  have hrow_nat : ∀ k : Fin numLimbs,
      (∑ t ∈ Finset.range 8, (env.get (i₀ + (8 * k.val + t))).val * 2 ^ (8 * t))
        = (input[k.val]'k.isLt).val := by
    intro k
    have hidx : ∀ t : Fin bytesPerLimb, 8 * k.val + t.val < coordBytes := by
      intro t
      have hk := k.isLt
      have ht := t.isLt
      simp only [numLimbs, bytesPerLimb, coordBytes] at hk ht ⊢
      omega
    -- cast the field-level row into a ℕ-cast of the byte sum
    have hcast : (∑ t : Fin bytesPerLimb,
          env.get (i₀ + (bytesPerLimb * k.val + t.val))
            * ((2 ^ (8 * t.val) : ℕ) : F circomPrime))
        = ((∑ t ∈ Finset.range 8,
            (env.get (i₀ + (8 * k.val + t))).val * 2 ^ (8 * t) : ℕ) : F circomPrime) := by
      rw [← Fin.sum_univ_eq_sum_range
        (fun t => (env.get (i₀ + (8 * k.val + t))).val * 2 ^ (8 * t)) 8, Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro t _
      rw [Nat.cast_mul, ZMod.natCast_zmod_val]
    -- the byte sum does not wrap: it is `< 2^64 < circomPrime`
    have hlt : (∑ t ∈ Finset.range 8,
        (env.get (i₀ + (8 * k.val + t))).val * 2 ^ (8 * t)) < 2 ^ 64 := by
      have h := sum_lt_pow (B := 8) (n := 8)
        (fun t : Fin 8 => (env.get (i₀ + (8 * k.val + t.val))).val)
        (fun t => h_bytes ⟨8 * k.val + t.val, hidx t⟩)
      rw [← Fin.sum_univ_eq_sum_range
        (fun t => (env.get (i₀ + (8 * k.val + t))).val * 2 ^ (8 * t)) 8]
      calc (∑ t : Fin 8, (env.get (i₀ + (8 * k.val + t.val))).val * 2 ^ (8 * t.val))
          < 2 ^ (8 * 8) := h
        _ = 2 ^ 64 := by norm_num
    have h := h_rows k
    rw [hcast] at h
    rw [← h, ZMod.val_natCast_of_lt (lt_trans hlt two_pow_64_lt_circomPrime)]
  -- regroup the 32-byte base-2^8 sum into the 4-limb base-2^64 sum
  calc (∑ i : Fin coordBytes,
        ((Vector.map (Expression.eval env)
          (Vector.mapRange coordBytes fun j =>
            var (F := F circomPrime) { index := i₀ + j }))[i]).val * 2 ^ (8 * i.val))
      = ∑ i ∈ Finset.range (4 * 8), (env.get (i₀ + i)).val * 2 ^ (8 * i) := by
        rw [← Fin.sum_univ_eq_sum_range (fun i => (env.get (i₀ + i)).val * 2 ^ (8 * i)) 32]
        apply Finset.sum_congr rfl
        intro i _
        rw [Fin.getElem_fin, hget i.val i.isLt]
    _ = ∑ k ∈ Finset.range 4,
          (∑ t ∈ Finset.range 8, (env.get (i₀ + (8 * k + t))).val * 2 ^ (8 * t))
            * 2 ^ (8 * 8 * k) :=
        sum_regroup 8 8 (fun i => (env.get (i₀ + i)).val) 4
    _ = ∑ k : Fin numLimbs, (input[k]).val * 2 ^ (limbBits * k.val) := by
        rw [← Fin.sum_univ_eq_sum_range (fun k =>
          (∑ t ∈ Finset.range 8, (env.get (i₀ + (8 * k + t))).val * 2 ^ (8 * t))
            * 2 ^ (8 * 8 * k)) 4]
        apply Finset.sum_congr rfl
        intro k _
        rw [hrow_nat k, Fin.getElem_fin]


theorem completeness_core (input : Emu (F circomPrime))
    (h_norm : input.Normalized limbBits) (k : Fin numLimbs)
    (b : Fin bytesPerLimb → F circomPrime)
    (hb : ∀ t : Fin bytesPerLimb,
      b t = ((input.value limbBits / 2 ^ (8 * (bytesPerLimb * k.val + t.val)) % 256 : ℕ)
        : F circomPrime)) :
    (∑ t : Fin bytesPerLimb, b t * ((2 ^ (8 * t.val) : ℕ) : F circomPrime))
      = input[k.val]'k.isLt := by
  have hcast : (∑ t : Fin bytesPerLimb, b t * ((2 ^ (8 * t.val) : ℕ) : F circomPrime))
      = ((∑ t ∈ Finset.range 8,
          input.value limbBits / 2 ^ (8 * (8 * k.val + t)) % 256 * 2 ^ (8 * t) : ℕ)
        : F circomPrime) := by
    rw [← Fin.sum_univ_eq_sum_range
      (fun t => input.value limbBits / 2 ^ (8 * (8 * k.val + t)) % 256 * 2 ^ (8 * t)) 8,
      Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro t _
    rw [hb t]
    push_cast
    ring
  rw [hcast, byteSum_eq_limb, value_limb_eq input h_norm k, ZMod.natCast_zmod_val,
    Fin.getElem_fin]

end ToBytes

end Solution.Secp256k1ScalarMul
