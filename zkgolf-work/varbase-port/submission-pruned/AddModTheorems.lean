import Solution.Secp256k1ScalarMul.Params

namespace Solution.Secp256k1ScalarMul
open Solution.Secp256k1ScalarMul.Limbs

lemma P256_pos : 0 < P256 := by decide

lemma P256_lt : P256 < 2 ^ (limbBits * numLimbs) := by decide

lemma two_pow_limb_lt : 2 ^ limbBits < circomPrime := by decide

lemma limb_add_lt : 2 ^ limbBits + 2 ^ limbBits < circomPrime := by decide

lemma limb_add_le_bound :
    2 ^ limbBits + 2 ^ limbBits ≤ (3 + 1) * 2 ^ (2 * limbBits) := by decide

lemma limbOfNat_lt (v k : ℕ) : limbOfNat v k < 2 ^ limbBits :=
  Nat.mod_lt _ (Nat.two_pow_pos limbBits)

lemma val_limbOfNat (v k : ℕ) :
    ((limbOfNat v k : ℕ) : F circomPrime).val = limbOfNat v k :=
  ZMod.val_natCast_of_lt (lt_trans (limbOfNat_lt v k) two_pow_limb_lt)

lemma emuOfNat_getElem (v k : ℕ) (hk : k < numLimbs) :
    (emuOfNat v)[k]'hk = ((limbOfNat v k : ℕ) : F circomPrime) := by
  simp only [emuOfNat, Vector.getElem_ofFn]

lemma emuOfNat_normalized (v : ℕ) : (emuOfNat v).Normalized limbBits := by
  intro i
  rw [Fin.getElem_fin, emuOfNat_getElem v i.val i.isLt, val_limbOfNat]
  exact limbOfNat_lt v i.val

lemma value_emuOfNat {v : ℕ} (hv : v < 2 ^ (limbBits * numLimbs)) :
    BigInt.value limbBits (emuOfNat v) = v := by
  rw [BigInt.value_eq_sum]
  have hsum : (∑ k : Fin numLimbs, ((emuOfNat v)[k]).val * 2 ^ (limbBits * k.val))
      = ∑ k ∈ Finset.range numLimbs,
          (v / 2 ^ (limbBits * k) % 2 ^ limbBits) * 2 ^ (limbBits * k) := by
    rw [← Fin.sum_univ_eq_sum_range
      (fun k => (v / 2 ^ (limbBits * k) % 2 ^ limbBits) * 2 ^ (limbBits * k))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fin.getElem_fin, emuOfNat_getElem v i.val i.isLt, val_limbOfNat]
    rfl
  rw [hsum, limb_decomp_mod, Nat.mod_eq_of_lt hv]

lemma limb_sum_P256 :
    (∑ k ∈ Finset.range numLimbs, limbOfNat P256 k * 2 ^ (limbBits * k)) = P256 := by
  have h : (∑ k ∈ Finset.range numLimbs, limbOfNat P256 k * 2 ^ (limbBits * k))
      = ∑ k ∈ Finset.range numLimbs,
          (P256 / 2 ^ (limbBits * k) % 2 ^ limbBits) * 2 ^ (limbBits * k) :=
    Finset.sum_congr rfl fun k _ => rfl
  rw [h, limb_decomp_mod, Nat.mod_eq_of_lt P256_lt]

lemma eval_pConst_getElem (env : Environment (F circomPrime)) (k : ℕ) (hk : k < numLimbs) :
    Expression.eval env (pConst[k]'hk) = ((limbOfNat P256 k : ℕ) : F circomPrime) :=
  congrArg (Expression.eval env) (Vector.getElem_ofFn ..)

lemma eval_pConst (env : Environment (F circomPrime)) :
    Vector.map (Expression.eval env) pConst = emuOfNat P256 := by
  apply Vector.ext
  intro k hk
  rw [Vector.getElem_map, eval_pConst_getElem env k hk, emuOfNat_getElem P256 k hk]

lemma pConst_normalized (env : Environment (F circomPrime)) :
    BigInt.Normalized limbBits (Vector.map (Expression.eval env) pConst) := by
  rw [eval_pConst]
  exact emuOfNat_normalized P256

lemma pConst_value (env : Environment (F circomPrime)) :
    BigInt.value limbBits (Vector.map (Expression.eval env) pConst) = P256 := by
  rw [eval_pConst]
  exact value_emuOfNat P256_lt

lemma eval_outVar_getElem (env : Environment (F circomPrime)) (i₀ k : ℕ) (hk : k < numLimbs) :
    (Vector.map (Expression.eval env)
        (Vector.mapRange numLimbs fun i => var (F := F circomPrime) { index := i₀ + i }))[k]'hk
      = env.get (i₀ + k) := by
  simp [circuit_norm]

lemma outVar_val_lt (env : Environment (F circomPrime)) (i₀ : ℕ)
    (h : BigInt.Normalized limbBits (Vector.map (Expression.eval env)
      (Vector.mapRange numLimbs fun i => var { index := i₀ + i }))) :
    ∀ k : ℕ, k < numLimbs → (env.get (i₀ + k)).val < 2 ^ limbBits := by
  intro k hk
  have hval := h ⟨k, hk⟩
  rwa [Fin.getElem_fin, eval_outVar_getElem env i₀ k hk] at hval

lemma value_outVar (B : ℕ) (env : Environment (F circomPrime)) (i₀ : ℕ) :
    BigInt.value B (Vector.map (Expression.eval env)
        (Vector.mapRange numLimbs fun i => var { index := i₀ + i }))
      = ∑ k ∈ Finset.range numLimbs, (env.get (i₀ + k)).val * 2 ^ (B * k) := by
  rw [BigInt.value_eq_sum,
    ← Fin.sum_univ_eq_sum_range (fun k => (env.get (i₀ + k)).val * 2 ^ (B * k))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fin.getElem_fin, eval_outVar_getElem env i₀ i.val i.isLt]

lemma value_eq_range_sum (B : ℕ) (x : Emu (F circomPrime)) :
    BigInt.value B x
      = ∑ k ∈ Finset.range numLimbs,
          (if h : k < numLimbs then (x[k]'h).val else 0) * 2 ^ (B * k) := by
  rw [BigInt.value_eq_sum,
    ← Fin.sum_univ_eq_sum_range
      (fun k => (if h : k < numLimbs then (x[k]'h).val else 0) * 2 ^ (B * k))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dif_pos i.isLt, Fin.getElem_fin]

lemma polyValue_padded (B : ℕ) (env : Environment (F circomPrime))
    (f : (k : Fin (2 * 3 - 1)) → k.val < numLimbs → Expression (F circomPrime))
    (c : ℕ → ℕ)
    (hval : ∀ (k : Fin (2 * 3 - 1)) (h : k.val < numLimbs),
      (Expression.eval env (f k h)).val = c k.val) :
    polyValue B (Vector.map (Expression.eval env)
        (Vector.mapFinRange (2 * 3 - 1) fun k =>
          if h : k.val < numLimbs then f k h else 0))
      = ∑ k ∈ Finset.range numLimbs, c k * 2 ^ (B * k) := by
  have hterm : ∀ k : Fin (2 * 3 - 1),
      ((Vector.map (Expression.eval env)
        (Vector.mapFinRange (2 * 3 - 1) fun k =>
          if h : k.val < numLimbs then f k h else 0))[k.val]).val * 2 ^ (B * k.val)
      = (if k.val < numLimbs then c k.val else 0) * 2 ^ (B * k.val) := by
    intro k
    rw [Vector.getElem_map, Vector.getElem_mapFinRange]
    by_cases hk : k.val < numLimbs
    · rw [dif_pos hk, if_pos hk, hval ⟨k.val, k.isLt⟩ hk]
    · rw [dif_neg hk, if_neg hk]
      norm_num [circuit_norm]
  rw [polyValue, Finset.sum_congr rfl (fun k _ => hterm k),
    Fin.sum_univ_eq_sum_range (fun k => (if k < numLimbs then c k else 0) * 2 ^ (B * k))]
  rw [← Finset.sum_subset (Finset.range_subset_range.mpr (by decide : numLimbs ≤ 2 * 3 - 1))
    (f := fun k => (if k < numLimbs then c k else 0) * 2 ^ (B * k))]
  · exact Finset.sum_congr rfl fun k hk => by rw [if_pos (Finset.mem_range.mp hk)]
  · intro k _ hk
    rw [Finset.mem_range] at hk
    rw [if_neg hk, Nat.zero_mul]

lemma val_add_limb {u v : F circomPrime}
    (hu : u.val < 2 ^ limbBits) (hv : v.val < 2 ^ limbBits) :
    (u + v).val = u.val + v.val :=
  ZMod.val_add_of_lt (by have := limb_add_lt; omega)

lemma bound_add_limb {u v : F circomPrime}
    (hu : u.val < 2 ^ limbBits) (hv : v.val < 2 ^ limbBits) :
    (u + v).val < (3 + 1) * 2 ^ (2 * limbBits) := by
  have h := ZMod.val_add_le u v
  have := limb_add_le_bound
  omega

lemma val_q_mul_limb {qN : ℕ} (hqN : qN ≤ 1) (k : ℕ) :
    (((qN : ℕ) : F circomPrime) * ((limbOfNat P256 k : ℕ) : F circomPrime)).val
      = qN * limbOfNat P256 k := by
  have hq_lt : qN < circomPrime := by
    have := two_pow_limb_lt
    have := Nat.two_pow_pos limbBits
    omega
  rw [ZMod.val_mul_of_lt, ZMod.val_natCast_of_lt hq_lt, val_limbOfNat]
  rw [ZMod.val_natCast_of_lt hq_lt, val_limbOfNat]
  have h1 := limbOfNat_lt P256 k
  have h2 : qN * limbOfNat P256 k ≤ 1 * limbOfNat P256 k :=
    Nat.mul_le_mul_right _ hqN
  have := two_pow_limb_lt
  omega

namespace AddMod

lemma limb_add_le_boundN : 2 ^ limbBits + 2 ^ limbBits ≤ 2 ^ 65 + 2 := by decide

lemma bound_add_limbN {u v : F circomPrime}
    (hu : u.val < 2 ^ limbBits) (hv : v.val < 2 ^ limbBits) :
    (u + v).val < 2 ^ 65 + 2 := by
  have h := ZMod.val_add_le u v
  have := limb_add_le_boundN
  omega

end AddMod

end Solution.Secp256k1ScalarMul
