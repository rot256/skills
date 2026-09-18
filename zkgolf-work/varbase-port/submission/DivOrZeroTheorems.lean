import Solution.Secp256k1ScalarMul.Params



namespace Solution.Secp256k1ScalarMul
namespace DivOrZero



lemma P256_pos : 0 < P256 := by decide

lemma one_lt_P256 : 1 < P256 := by decide


lemma P256_lt : P256 < 2 ^ (limbBits * numLimbs) := by decide


lemma two_pow_limb_lt : 2 ^ limbBits < circomPrime := by decide

instance : NeZero P256 := ⟨Nat.pos_iff_ne_zero.mp P256_pos⟩



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


lemma fe_valid_emuOfNat {v : ℕ} (hv : v < P256) : Fe.Valid (emuOfNat v) :=
  ⟨emuOfNat_normalized v, by rw [value_emuOfNat (lt_trans hv P256_lt)]; exact hv⟩


lemma secpParams_B : secpParams.B = limbBits := rfl



lemma eval_emuConst_getElem (env : Environment (F circomPrime)) (v k : ℕ)
    (hk : k < numLimbs) :
    Expression.eval env ((emuConst v)[k]'hk) = ((limbOfNat v k : ℕ) : F circomPrime) := by
  simp only [emuConst]
  rw [Vector.getElem_ofFn]
  rfl


lemma eval_emuConst (env : Environment (F circomPrime)) (v : ℕ) :
    Vector.map (Expression.eval env) (emuConst v) = emuOfNat v := by
  apply Vector.ext
  intro k hk
  rw [Vector.getElem_map, eval_emuConst_getElem env v k hk, emuOfNat_getElem v k hk]

lemma eval_pConst (env : Environment (F circomPrime)) :
    Vector.map (Expression.eval env) pConst = emuOfNat P256 :=
  eval_emuConst env P256

lemma eval_oneConst (env : Environment (F circomPrime)) :
    Vector.map (Expression.eval env) oneConst = emuOfNat 1 :=
  eval_emuConst env 1

lemma eval_zeroConst (env : Environment (F circomPrime)) :
    Vector.map (Expression.eval env) zeroConst = emuOfNat 0 :=
  eval_emuConst env 0

lemma pConst_normalized (env : Environment (F circomPrime)) :
    BigInt.Normalized limbBits (Vector.map (Expression.eval env) pConst) := by
  rw [eval_pConst]
  exact emuOfNat_normalized P256

lemma pConst_value (env : Environment (F circomPrime)) :
    BigInt.value limbBits (Vector.map (Expression.eval env) pConst) = P256 := by
  rw [eval_pConst]
  exact value_emuOfNat P256_lt

lemma value_emuOfNat_one : BigInt.value limbBits (emuOfNat 1) = 1 :=
  value_emuOfNat (by decide)

lemma value_emuOfNat_zero : BigInt.value limbBits (emuOfNat 0) = 0 :=
  value_emuOfNat (by decide)




lemma val_decodeFe {x : Emu (F circomPrime)} (hx : Fe.Valid x) :
    (decodeFe x).val = BigInt.value limbBits x := by
  rw [decodeFe, ZMod.val_natCast, Nat.mod_eq_of_lt hx.2]


lemma decodeFe_of_value_eq_zero {x : Emu (F circomPrime)}
    (h : BigInt.value limbBits x = 0) : decodeFe x = 0 := by
  rw [decodeFe, h, Nat.cast_zero]




lemma mul_cast_of_mod_eq {l d n : ℕ} (h : l * d % P256 = n) :
    (l : Specs.Secp256k1.Fp) * (d : Specs.Secp256k1.Fp) = (n : Specs.Secp256k1.Fp) := by
  rw [← h, ZMod.natCast_mod, Nat.cast_mul]


lemma mul_cast_of_mod_eq3 {l d n : ℕ} (h : n % P256 = l * d % P256) :
    (l : Specs.Secp256k1.Fp) * (d : Specs.Secp256k1.Fp) = (n : Specs.Secp256k1.Fp) := by
  have hc : ((n : ℕ) : Specs.Secp256k1.Fp) = ((l * d : ℕ) : Specs.Secp256k1.Fp) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mpr h
  push_cast at hc
  linear_combination -hc


lemma witness_val_den_zero (n : Specs.Secp256k1.Fp) :
    (n * (0 : Specs.Secp256k1.Fp)⁻¹).val = 0 := by
  rw [inv_zero, mul_zero, ZMod.val_zero]


lemma witness_cert_nonzero {nv dv : ℕ} (hnv : nv < P256)
    (hd : (dv : Specs.Secp256k1.Fp) ≠ 0) :
    ((nv : Specs.Secp256k1.Fp) * (dv : Specs.Secp256k1.Fp)⁻¹).val * dv % P256 = nv := by
  have h1 : ((((nv : Specs.Secp256k1.Fp) * (dv : Specs.Secp256k1.Fp)⁻¹).val * dv : ℕ) :
      Specs.Secp256k1.Fp) = (nv : Specs.Secp256k1.Fp) := by
    push_cast [ZMod.natCast_val, ZMod.cast_id]
    rw [mul_assoc, inv_mul_cancel₀ hd, mul_one]
  calc ((nv : Specs.Secp256k1.Fp) * (dv : Specs.Secp256k1.Fp)⁻¹).val * dv % P256
      = ((((nv : Specs.Secp256k1.Fp) * (dv : Specs.Secp256k1.Fp)⁻¹).val * dv : ℕ) :
          Specs.Secp256k1.Fp).val := by rw [ZMod.val_natCast]
    _ = ((nv : Specs.Secp256k1.Fp)).val := by rw [h1]
    _ = nv := by rw [ZMod.val_natCast, Nat.mod_eq_of_lt hnv]


lemma witness_cert_nonzero3 {nv dv : ℕ}
    (hd : (dv : Specs.Secp256k1.Fp) ≠ 0) :
    (nv : ℕ) % P256
      = ((nv : Specs.Secp256k1.Fp) * (dv : Specs.Secp256k1.Fp)⁻¹).val * dv % P256 := by
  have h1 : ((((nv : Specs.Secp256k1.Fp) * (dv : Specs.Secp256k1.Fp)⁻¹).val * dv : ℕ) :
      Specs.Secp256k1.Fp) = (nv : Specs.Secp256k1.Fp) := by
    push_cast [ZMod.natCast_val, ZMod.cast_id]
    rw [mul_assoc, inv_mul_cancel₀ hd, mul_one]
  calc (nv : ℕ) % P256
      = ((nv : Specs.Secp256k1.Fp)).val := by rw [ZMod.val_natCast]
    _ = ((((nv : Specs.Secp256k1.Fp) * (dv : Specs.Secp256k1.Fp)⁻¹).val * dv : ℕ) :
          Specs.Secp256k1.Fp).val := by rw [h1]
    _ = ((nv : Specs.Secp256k1.Fp) * (dv : Specs.Secp256k1.Fp)⁻¹).val * dv % P256 := by
        rw [ZMod.val_natCast]

end DivOrZero
end Solution.Secp256k1ScalarMul
