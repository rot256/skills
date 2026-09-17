import Solution.Secp256k1ScalarMul.Lazy_Donor1


-- Adapted donor module: CanonicalizeTheorems
section DonorFile2_0

namespace Solution.Secp256k1ScalarMulFixedBase
open Solution.Secp256k1ScalarMulFixedBase.Limbs

namespace Canonicalize

lemma polyValue_padded_gen (L : ℕ) [NeZero L] (hL : numLimbs ≤ L) (B : ℕ)
    (env : Environment (F circomPrime))
    (f : (k : Fin L) → k.val < numLimbs → Expression (F circomPrime))
    (c : ℕ → ℕ)
    (hval : ∀ (k : Fin L) (h : k.val < numLimbs),
      (Expression.eval env (f k h)).val = c k.val) :
    polyValue B (Vector.map (Expression.eval env)
        (Vector.mapFinRange L fun k =>
          if h : k.val < numLimbs then f k h else 0))
      = ∑ k ∈ Finset.range numLimbs, c k * 2 ^ (B * k) := by
  have hterm : ∀ k : Fin L,
      ((Vector.map (Expression.eval env)
        (Vector.mapFinRange L fun k =>
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
  rw [← Finset.sum_subset (Finset.range_subset_range.mpr hL)
    (f := fun k => (if k < numLimbs then c k else 0) * 2 ^ (B * k))]
  · exact Finset.sum_congr rfl fun k hk => by rw [if_pos (Finset.mem_range.mp hk)]
  · intro k _ hk
    rw [Finset.mem_range] at hk
    rw [if_neg hk, Nat.zero_mul]

lemma eval_cExp (env : Environment (F circomPrime)) (v k : ℕ) :
    Expression.eval env (CompactAdd.cExp v k) = ((limbOfNat v k : ℕ) : F circomPrime) :=
  rfl

lemma eval_emuPoly (env : Environment (F circomPrime)) (a : Var Emu (F circomPrime)) :
    Expression.eval env (emuPoly a)
      = ((BigInt.value limbBits (Vector.map (Expression.eval env) a) : ℕ) : F circomPrime) := by
  rw [value_eq_range_sum limbBits (Vector.map (Expression.eval env) a)]
  simp only [numLimbs, Finset.sum_range_succ, Finset.sum_range_zero,
    Nat.zero_add, emuPoly, wP, Expression.eval, Vector.getElem_map]
  push_cast [FieldUtils.natCast_val]
  ring

lemma P256_castF_ne_zero : ((P256 : ℕ) : F circomPrime) ≠ 0 := by decide

lemma eval_bExpr (env : Environment (F circomPrime)) (x r : Var Emu (F circomPrime))
    (bN : ℕ)
    (h : BigInt.value limbBits (Vector.map (Expression.eval env) x)
        = bN * P256 + BigInt.value limbBits (Vector.map (Expression.eval env) r)) :
    Expression.eval env (bExpr x r) = ((bN : ℕ) : F circomPrime) := by
  have hinv : (((P256 : ℕ) : F circomPrime))⁻¹ * ((P256 : ℕ) : F circomPrime) = 1 :=
    inv_mul_cancel₀ P256_castF_ne_zero
  have hkey : Expression.eval env (emuPoly x) - Expression.eval env (emuPoly r)
      = ((bN : ℕ) : F circomPrime) * ((P256 : ℕ) : F circomPrime) := by
    rw [eval_emuPoly, eval_emuPoly, h]; push_cast; ring
  simp only [bExpr, Expression.eval]
  linear_combination (((P256 : ℕ) : F circomPrime))⁻¹ * hkey
    + ((bN : ℕ) : F circomPrime) * hinv

lemma boundAt_lin_pos (k : Fin 5) (hk : k.val < 4) :
    EqViaCarriesFlex.boundAt linFlex.M k.val = 2 ^ 67 := by
  fin_cases k <;> revert hk <;> decide

lemma boundAt_lin_top : EqViaCarriesFlex.boundAt linFlex.M 4 = 2 ^ 4 := by decide

lemma lhs_bound (env : Environment (F circomPrime))
    (rE : Var Emu (F circomPrime)) (bE : Expression (F circomPrime)) (bN : ℕ)
    (hb : Expression.eval env bE = ((bN : ℕ) : F circomPrime)) (hbN : bN ≤ 1)
    (hr : ∀ (k : ℕ) (hk : k < numLimbs),
      (Expression.eval env (rE[k]'hk)).val < 2 ^ limbBits) :
    ∀ k : Fin 5,
      (Expression.eval env
          (if h : k.val < 4 then
            rE[k.val]'h + bE * CompactAdd.cExp P256 k.val
          else 0)).val < EqViaCarriesFlex.boundAt linFlex.M k.val := by
  intro k
  by_cases hk : k.val < 4
  · rw [dif_pos hk,
      show Expression.eval env (rE[k.val]'hk + bE * CompactAdd.cExp P256 k.val)
          = Expression.eval env (rE[k.val]'hk)
            + Expression.eval env bE * Expression.eval env (CompactAdd.cExp P256 k.val)
          from rfl,
      hb, eval_cExp]
    have h1 := ZMod.val_add_le (Expression.eval env (rE[k.val]'hk))
      (((bN : ℕ) : F circomPrime) * ((limbOfNat P256 k.val : ℕ) : F circomPrime))
    rw [val_q_mul_limb hbN k.val] at h1
    have h2 := limbOfNat_lt P256 k.val
    have h3 : bN * limbOfNat P256 k.val ≤ 1 * limbOfNat P256 k.val :=
      Nat.mul_le_mul_right _ hbN
    have h4 := hr k.val hk
    have hf : (2 : ℕ) ^ limbBits ≤ 2 ^ 66 := by norm_num [limbBits]
    rw [boundAt_lin_pos k hk]
    omega
  · rw [dif_neg hk, show Expression.eval env (0 : Expression (F circomPrime)) = 0 from rfl,
      ZMod.val_zero]
    have hk4 : k.val = 4 := by omega
    rw [hk4, boundAt_lin_top]; positivity

lemma rhs_bound (env : Environment (F circomPrime))
    (x_var : Var Emu (F circomPrime)) (x : Emu (F circomPrime))
    (h_input : Vector.map (Expression.eval env) x_var = x)
    (hx : x.Normalized limbBits) :
    ∀ k : Fin 5,
      (Expression.eval env (if h : k.val < 4 then x_var[k.val] else 0)).val
        < EqViaCarriesFlex.boundAt linFlex.M k.val := by
  intro k
  by_cases hk : k.val < 4
  · rw [dif_pos hk, show Expression.eval env (x_var[k.val]'hk) = x[k.val]'hk from by
        rw [← h_input, Vector.getElem_map]]
    have h4 : (x[k.val]'hk).val < 2 ^ limbBits := hx ⟨k.val, hk⟩
    rw [boundAt_lin_pos k hk]
    have : (2 : ℕ) ^ limbBits ≤ 2 ^ 67 := by norm_num [limbBits]
    omega
  · rw [dif_neg hk, show Expression.eval env (0 : Expression (F circomPrime)) = 0 from rfl,
      ZMod.val_zero]
    have hk4 : k.val = 4 := by omega
    rw [hk4, boundAt_lin_top]; positivity

lemma polyValue_lhs (env : Environment (F circomPrime))
    (rE : Var Emu (F circomPrime)) (bE : Expression (F circomPrime)) (bN : ℕ)
    (hb : Expression.eval env bE = ((bN : ℕ) : F circomPrime)) (hbN : bN ≤ 1)
    (hr : ∀ (k : ℕ) (hk : k < numLimbs),
      (Expression.eval env (rE[k]'hk)).val < 2 ^ limbBits) :
    polyValue limbBits (Vector.map (Expression.eval env)
        (Vector.mapFinRange 5 fun k =>
          if h : k.val < 4 then
            rE[k.val]'h + bE * CompactAdd.cExp P256 k.val
          else 0))
      = BigInt.value limbBits (Vector.map (Expression.eval env) rE) + bN * P256 := by
  refine (polyValue_padded_gen 5 (by decide) limbBits env
      (fun k h => rE[k.val]'h + bE * CompactAdd.cExp P256 k.val)
      (fun k => if h : k < numLimbs then
        (Expression.eval env (rE[k]'h)).val + bN * limbOfNat P256 k else 0) ?_).trans ?_
  · intro k hk
    rw [show Expression.eval env (rE[k.val]'hk + bE * CompactAdd.cExp P256 k.val)
        = Expression.eval env (rE[k.val]'hk)
          + Expression.eval env bE * Expression.eval env (CompactAdd.cExp P256 k.val)
        from rfl,
      hb, eval_cExp, ZMod.val_add_of_lt, val_q_mul_limb hbN k.val]
    · simp only [dif_pos hk]
    · rw [val_q_mul_limb hbN k.val]
      have h2 := limbOfNat_lt P256 k.val
      have h3 : bN * limbOfNat P256 k.val ≤ 1 * limbOfNat P256 k.val := Nat.mul_le_mul_right _ hbN
      have h4 := hr k.val hk
      have := limb_add_lt
      omega
  · rw [value_eq_range_sum limbBits (Vector.map (Expression.eval env) rE)]
    have hsplit : (∑ k ∈ Finset.range numLimbs,
          (if h : k < numLimbs then
            (Expression.eval env (rE[k]'h)).val + bN * limbOfNat P256 k else 0) * 2 ^ (limbBits * k))
        = (∑ k ∈ Finset.range numLimbs,
            (if h : k < numLimbs then
              ((Vector.map (Expression.eval env) rE)[k]'(by simpa using h)).val else 0) * 2 ^ (limbBits * k))
          + ∑ k ∈ Finset.range numLimbs, bN * (limbOfNat P256 k * 2 ^ (limbBits * k)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk' : k < numLimbs := Finset.mem_range.mp hk
      simp only [dif_pos hk', Vector.getElem_map]
      ring
    rw [hsplit, ← Finset.mul_sum, limb_sum_P256]

lemma polyValue_rhs (env : Environment (F circomPrime))
    (x_var : Var Emu (F circomPrime)) (x : Emu (F circomPrime))
    (h_input : Vector.map (Expression.eval env) x_var = x) :
    polyValue limbBits (Vector.map (Expression.eval env)
        (Vector.mapFinRange 5 fun k => if h : k.val < 4 then x_var[k.val] else 0))
      = BigInt.value limbBits x := by
  refine (polyValue_padded_gen 5 (by decide) limbBits env
      (fun k h => x_var[k.val]'h)
      (fun k => if h : k < numLimbs then (x[k]'h).val else 0) ?_).trans ?_
  · intro k hk
    rw [show Expression.eval env (x_var[k.val]'hk) = x[k.val]'hk from by
      rw [← h_input, Vector.getElem_map]]
    simp only [dif_pos hk]
  · rw [value_eq_range_sum limbBits x]

lemma canonical_lhs_bound (env : Environment (F circomPrime))
    (rE : Var Emu (F circomPrime)) (bE : Expression (F circomPrime)) (bN : ℕ)
    (hb : Expression.eval env bE = ((bN : ℕ) : F circomPrime)) (hbN : bN ≤ 1)
    (hr : ∀ (k : ℕ) (hk : k < numLimbs),
      (Expression.eval env (rE[k]'hk)).val < 2 ^ limbBits) :
    ∀ k : Fin 5,
      (Expression.eval env
        (if h : k.val < 4 then rE[k.val]'h + bE * CompactAdd.cExp P256 k.val else 0)).val
        < vCanonicalL.Nf k.val := by
  intro k
  by_cases hk : k.val < 4
  · rw [dif_pos hk, show Expression.eval env
        (rE[k.val]'hk + bE * CompactAdd.cExp P256 k.val) =
          Expression.eval env (rE[k.val]'hk) +
            Expression.eval env bE * Expression.eval env (CompactAdd.cExp P256 k.val) from rfl,
      hb, eval_cExp, ZMod.val_add_of_lt, val_q_mul_limb hbN k.val]
    · simp only [vCanonicalL, nfCanonicalL, if_pos hk]
      have h4 := hr k.val hk
      have h2 := limbOfNat_lt P256 k.val
      have hmul : bN * limbOfNat P256 k.val ≤ limbOfNat P256 k.val := by
        nlinarith
      have hmul_lt : bN * limbOfNat P256 k.val < 2 ^ limbBits :=
        lt_of_le_of_lt hmul h2
      have hsum : (Expression.eval env (rE[k.val]'hk)).val +
          bN * limbOfNat P256 k.val < 2 ^ 65 := by
        calc
          _ < 2 ^ limbBits + 2 ^ limbBits := Nat.add_lt_add h4 hmul_lt
          _ = 2 ^ 65 := by norm_num [limbBits]
      simpa [limbBits] using hsum
    · rw [val_q_mul_limb hbN k.val]
      have h4 := hr k.val hk
      have h2 := limbOfNat_lt P256 k.val
      have hmul : bN * limbOfNat P256 k.val ≤ limbOfNat P256 k.val := by
        nlinarith
      have hmul_lt : bN * limbOfNat P256 k.val < 2 ^ limbBits :=
        lt_of_le_of_lt hmul h2
      have hsum : (Expression.eval env (rE[k.val]'hk)).val +
          bN * limbOfNat P256 k.val < circomPrime := by
        exact lt_trans (Nat.add_lt_add h4 hmul_lt) limb_add_lt
      exact hsum
  · rw [dif_neg hk]
    simp only [vCanonicalL, nfCanonicalL, if_neg hk, Expression.eval, ZMod.val_zero]
    omega

lemma canonical_rhs_bound (env : Environment (F circomPrime))
    (x_var : Var Emu (F circomPrime)) (x : Emu (F circomPrime))
    (h_input : Vector.map (Expression.eval env) x_var = x)
    (hx : x.Normalized limbBits) :
    ∀ k : Fin 5,
      (Expression.eval env (if h : k.val < 4 then x_var[k.val] else 0)).val
        < vCanonicalR.Nf k.val := by
  intro k
  by_cases hk : k.val < 4
  · rw [dif_pos hk, show Expression.eval env (x_var[k.val]'hk) = x[k.val]'hk from by
        rw [← h_input, Vector.getElem_map]]
    simpa [vCanonicalR, nfCanonicalR, hk, limbBits] using hx ⟨k.val, hk⟩
  · rw [dif_neg hk]
    simp only [Expression.eval, ZMod.val_zero]
    simp [vCanonicalR, nfCanonicalR, hk]

lemma val_byteSum_lt (b : Fin bytesPerLimb → F circomPrime)
    (hb : ∀ t, (b t).val < 2 ^ 8) :
    (∑ t : Fin bytesPerLimb,
        b t * ((2 ^ (8 * t.val) : ℕ) : F circomPrime)).val < 2 ^ 64 := by
  have hcast : (∑ t : Fin bytesPerLimb, b t * ((2 ^ (8 * t.val) : ℕ) : F circomPrime))
      = ((∑ t : Fin bytesPerLimb, (b t).val * 2 ^ (8 * t.val) : ℕ) : F circomPrime) := by
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro t _
    rw [Nat.cast_mul, ZMod.natCast_zmod_val]
  have hlt : (∑ t : Fin bytesPerLimb, (b t).val * 2 ^ (8 * t.val)) < 2 ^ 64 := by
    have hle : ∀ t : Fin bytesPerLimb,
        (b t).val * 2 ^ (8 * t.val) ≤ (2 ^ 8 - 1) * 2 ^ (8 * t.val) :=
      fun t => Nat.mul_le_mul_right _ (by have := hb t; omega)
    calc (∑ t : Fin bytesPerLimb, (b t).val * 2 ^ (8 * t.val))
        ≤ ∑ t : Fin bytesPerLimb, (2 ^ 8 - 1) * 2 ^ (8 * t.val) :=
          Finset.sum_le_sum fun t _ => hle t
      _ = 2 ^ 64 - 1 := by decide
      _ < 2 ^ 64 := by norm_num
  rw [hcast, ZMod.val_natCast_of_lt (lt_trans hlt ToBytes.two_pow_64_lt_circomPrime)]
  exact hlt

lemma spec_of_validPBytes {x input : Emu (F circomPrime)}
    {out : fields coordBytes (F circomPrime)} {data : ProverData (F circomPrime)}
    (hmod : BigInt.value limbBits x = BigInt.value limbBits input % P256)
    (hbytes : ValidPBytes.Spec x out data) : Spec input out := by
  constructor
  · exact hbytes.2.1
  ·
    rw [hbytes.2.2, hmod]
    simp only [decodeFe, ZMod.val_natCast]

/-- The four base-`2^64` limbs of `P256`, recombined over `F circomPrime`. -/
lemma limbF_sum_P256 :
    ((limbOfNat P256 0 : ℕ) : F circomPrime)
      + ((limbOfNat P256 1 : ℕ) : F circomPrime) * (2 : F circomPrime) ^ 64
      + ((limbOfNat P256 2 : ℕ) : F circomPrime) * (2 : F circomPrime) ^ 128
      + ((limbOfNat P256 3 : ℕ) : F circomPrime) * (2 : F circomPrime) ^ 192
      = ((P256 : ℕ) : F circomPrime) := by
  have h : limbOfNat P256 0 + limbOfNat P256 1 * 2 ^ 64 + limbOfNat P256 2 * 2 ^ 128
      + limbOfNat P256 3 * 2 ^ 192 = P256 := by
    have h := limb_sum_P256
    simpa only [numLimbs, limbBits, Finset.sum_range_succ, Finset.sum_range_zero,
      Nat.mul_zero, pow_zero, Nat.mul_one, zero_add] using h
  have h2 := congrArg (fun n : ℕ => (n : F circomPrime)) h
  push_cast at h2
  linear_combination h2

lemma eval_emuPoly_expand (env : Environment (F circomPrime)) (a : Var Emu (F circomPrime)) :
    Expression.eval env (emuPoly a)
      = Expression.eval env a[0] + Expression.eval env a[1] * (2 : F circomPrime) ^ 64
        + Expression.eval env a[2] * (2 : F circomPrime) ^ 128
        + Expression.eval env a[3] * (2 : F circomPrime) ^ 192 := by
  simp only [emuPoly, wP, limbBits, Expression.eval]
  push_cast
  ring

/-- The native-field row that `GroupedFlex.mainNoTop` deletes holds identically
once the conditional-reduction bit is the inverted affine expression `bExpr`. -/
lemma canonical_linIdent (env : Environment (F circomPrime))
    (xE rE : Var Emu (F circomPrime)) (bE : Expression (F circomPrime))
    (hbE : bE = bExpr xE rE) :
    GroupedFlex.LinIdent 64
      { lhs := Vector.map (Expression.eval env)
          (Vector.mapFinRange 5 fun k : Fin 5 =>
            if h : k.val < 4 then rE[k.val]'h + bE * CompactAdd.cExp P256 k.val else 0),
        rhs := Vector.map (Expression.eval env)
          (Vector.mapFinRange 5 fun k : Fin 5 =>
            if h : k.val < 4 then xE[k.val]'h else 0) } := by
  have hP := limbF_sum_P256
  have hb : Expression.eval env bE * ((P256 : ℕ) : F circomPrime)
      = Expression.eval env (emuPoly xE) - Expression.eval env (emuPoly rE) := by
    rw [hbE]
    simp only [bExpr, Expression.eval]
    field_simp [P256_castF_ne_zero]
    ring
  rw [eval_emuPoly_expand, eval_emuPoly_expand] at hb
  simp only [GroupedFlex.LinIdent, Fin.sum_univ_five, Vector.getElem_map,
    Vector.getElem_mapFinRange]
  norm_num [Expression.eval, eval_cExp]
  linear_combination hb + Expression.eval env bE * hP

set_option maxHeartbeats 12000000 in
theorem soundness : Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [GroupedFlex.circuitNoTop, GroupedFlex.elaboratedNoTop,
    GroupedFlex.mainNoTop, GroupedFlex.AssumptionsNoTop, GroupedFlex.Assumptions,
    EqViaCarriesFlex.Spec,
    ValidPBytes.circuit, ValidPBytes.main, ValidPBytes.Assumptions,
    ValidPBytes.Spec]
  obtain ⟨hb_bool, h_valid_bytes, h_eq_impl⟩ := h_holds

  set rVar : Var Emu (F circomPrime) :=
    Vector.mapRange numLimbs fun i => var { index := i₀ + i } with hrVar
  set bE : Expression (F circomPrime) := bExpr input_var rVar with hbEdef

  have hb01 : (Expression.eval env bE).val ≤ 1 := by
    rcases mul_eq_zero.mp hb_bool with h | h
    · rw [h, ZMod.val_zero]; omega
    · rw [add_neg_eq_zero] at h; rw [h, ZMod.val_one]
  have hb_cast : Expression.eval env bE
      = (((Expression.eval env bE).val : ℕ) : F circomPrime) :=
    (ZMod.natCast_zmod_val _).symm
  set bN := (Expression.eval env bE).val with hbNdef

  have hr_lt : ∀ (k : ℕ) (hk : k < numLimbs),
      (Expression.eval env (rVar[k]'hk)).val < 2 ^ limbBits := by
    intro k hk
    simpa only [Fin.getElem_fin, Vector.getElem_map] using
      h_valid_bytes.1.1 ⟨k, hk⟩

  have h_lhs_bound :
      ∀ k : Fin 5,
        (Expression.eval env
          (if h : k.val < 4 then
            var { index := i₀ + k.val } + bE * CompactAdd.cExp P256 k.val
          else 0)).val < vCanonicalL.Nf k.val := by
    intro k
    have hterm :
        (if h : k.val < 4 then
          var { index := i₀ + k.val } + bE * CompactAdd.cExp P256 k.val
        else 0)
        =
        (if h : k.val < 4 then
          rVar[k.val]'h + bE * CompactAdd.cExp P256 k.val
        else 0) := by
      by_cases hk : k.val < 4
      · simp only [hk, ↓reduceDIte, hrVar]
        rw [Vector.getElem_mapRange]
      · simp only [hk, ↓reduceDIte]
    rw [hterm]
    exact canonical_lhs_bound env rVar _ bN hb_cast hb01 hr_lt k
  have hvecExpr :
      (Vector.mapFinRange 5 fun k : Fin 5 =>
        if h : k.val < 4 then
          (var { index := i₀ + k.val } : Expression (F circomPrime))
            + bE * CompactAdd.cExp P256 k.val
        else 0)
      =
      (Vector.mapFinRange 5 fun k : Fin 5 =>
        if h : k.val < 4 then
          rVar[k.val]'h + bE * CompactAdd.cExp P256 k.val
        else 0) := by
    apply Vector.ext
    intro k hk
    rw [Vector.getElem_mapFinRange, Vector.getElem_mapFinRange]
    by_cases hlt : k < 4
    · simp only [hlt, ↓reduceDIte, hrVar]
      rw [Vector.getElem_mapRange]
    · simp only [hlt, ↓reduceDIte]
  have h_polyeq := h_eq_impl
    ⟨⟨h_lhs_bound,
      canonical_rhs_bound env input_var input h_input h_assumptions⟩,
     by
      rw [hvecExpr]
      exact canonical_linIdent env input_var rVar bE hbEdef⟩
  rw [show (64 : ℕ) = limbBits from rfl] at h_polyeq
  have h_lhs_poly :
      polyValue limbBits
        (Vector.map (Expression.eval env)
          (Vector.mapFinRange 5 fun k =>
            if h : k.val < 4 then
              var { index := i₀ + k.val } + bE * CompactAdd.cExp P256 k.val
            else 0)) =
          BigInt.value limbBits (Vector.map (Expression.eval env) rVar) + bN * P256 := by
    rw [hvecExpr]
    exact polyValue_lhs env rVar _ bN hb_cast hb01 hr_lt
  rw [h_lhs_poly, polyValue_rhs env input_var input h_input] at h_polyeq

  have hrV_mod : BigInt.value limbBits (Vector.map (Expression.eval env) rVar)
      = BigInt.value limbBits input % P256 := by
    rw [← h_polyeq, Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt h_valid_bytes.1.2]
  have h_valid_output :
      Fe.Valid (Vector.map (Expression.eval env) rVar) ∧
        ToBytes.Spec (Vector.map (Expression.eval env) rVar)
          (Vector.map (Expression.eval env)
            (ValidPBytes.circuit.output rVar (i₀ + numLimbs))) :=
    h_valid_bytes
  simpa only [Spec, numLimbs, hrVar, ValidPBytes.circuit, circuit_norm,
    ValidPBytes.elaborated, Fin.getElem_fin, Vector.getElem_map,
    Vector.getElem_mapRange, Expression.eval] using spec_of_validPBytes
    (data := env.data)
    (x := Vector.map (Expression.eval env) rVar)
    (input := input)
    (hmod := hrV_mod)
    h_valid_output

set_option maxHeartbeats 4000000 in
theorem completeness : Completeness (F circomPrime) main Assumptions := by
  circuit_proof_start [GroupedFlex.circuitNoTop, GroupedFlex.elaboratedNoTop,
    GroupedFlex.mainNoTop, GroupedFlex.AssumptionsNoTop, GroupedFlex.Assumptions,
    EqViaCarriesFlex.Spec,
    ValidPBytes.circuit, ValidPBytes.main, ValidPBytes.ProverAssumptions,
    ValidPBytes.ProverSpec, ValidPBytes.Assumptions, ValidPBytes.Spec]
  obtain ⟨h_wit_r, _h_vpb_complete⟩ := h_env

  have hev : evalEmu env input_var = BigInt.value limbBits input := by
    rw [evalEmu, BigInt.value, ← h_input]
  rw [hev] at h_wit_r
  set vx := BigInt.value limbBits input with hvx
  have hvx_lt : vx < 2 ^ (limbBits * numLimbs) := BigInt.value_lt h_assumptions

  have hb2 : vx / P256 ≤ 1 := by
    have h2P : (2 : ℕ) ^ (limbBits * numLimbs) < 2 * P256 := by decide
    exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul P256_pos).mpr (by omega))
  set bN := vx / P256 with hbNdef
  set rN := vx % P256 with hrNdef
  have hrN_lt : rN < P256 := Nat.mod_lt _ P256_pos
  have hrN_pow : rN < 2 ^ (limbBits * numLimbs) := lt_trans hrN_lt P256_lt

  set rVar : Var Emu (F circomPrime) :=
    Vector.mapRange numLimbs fun i => var { index := i₀ + i } with hrVar
  have hvec : Vector.map (Expression.eval env.toEnvironment) rVar = emuOfNat rN := by
    apply Vector.ext
    intro k hk
    simp only [hrVar, Vector.getElem_map, Vector.getElem_mapRange]
    exact h_wit_r ⟨k, by simpa only [numLimbs] using hk⟩
  have hr_valid : Fe.Valid (Vector.map (Expression.eval env.toEnvironment) rVar) := by
    rw [hvec]
    exact ⟨emuOfNat_normalized rN, by
      rw [value_emuOfNat hrN_pow]
      exact hrN_lt⟩
  have hr_lt : ∀ (k : ℕ) (hk : k < numLimbs),
      (Expression.eval env.toEnvironment (rVar[k]'hk)).val < 2 ^ limbBits := by
    intro k hk
    have h := hr_valid.1 ⟨k, hk⟩
    simpa only [Fin.getElem_fin, Vector.getElem_map] using h

  have hb_cast : Expression.eval env.toEnvironment (bExpr input_var rVar)
      = ((bN : ℕ) : F circomPrime) := by
    refine eval_bExpr env.toEnvironment input_var rVar bN ?_
    have h1 : BigInt.value limbBits (Vector.map (Expression.eval env.toEnvironment) input_var) = vx := by
      rw [h_input, hvx]
    have h2 : BigInt.value limbBits (Vector.map (Expression.eval env.toEnvironment) rVar) = rN := by
      rw [hvec, value_emuOfNat hrN_pow]
    rw [h1, h2, hbNdef, hrNdef]
    have h := Nat.div_add_mod vx P256
    have hc : (vx / P256) * P256 = P256 * (vx / P256) := Nat.mul_comm _ _
    omega
  set bE : Expression (F circomPrime) := bExpr input_var rVar with hbEdef

  have hvecExpr :
      (Vector.mapFinRange 5 fun k : Fin 5 =>
        if h : k.val < 4 then
          (var { index := i₀ + k.val } : Expression (F circomPrime))
            + bE * CompactAdd.cExp P256 k.val
        else 0)
      =
      (Vector.mapFinRange 5 fun k : Fin 5 =>
        if h : k.val < 4 then
          rVar[k.val]'h + bE * CompactAdd.cExp P256 k.val
        else 0) := by
    apply Vector.ext
    intro k hk
    rw [Vector.getElem_mapFinRange, Vector.getElem_mapFinRange]
    by_cases hlt : k < 4
    · simp only [hlt, ↓reduceDIte, hrVar]
      rw [Vector.getElem_mapRange]
    · simp only [hlt, ↓reduceDIte]

  rw [show (64 : ℕ) = limbBits from rfl]
  refine ⟨?_, ?_, ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩⟩
  ·
    rw [hb_cast]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb2 with h | h <;> rw [h] <;> push_cast <;> ring
  · exact hr_valid
  ·
    intro k
    have hterm :
        (if h : k.val < 4 then
          var { index := i₀ + k.val } + bE * CompactAdd.cExp P256 k.val
        else 0)
        =
        (if h : k.val < 4 then
          rVar[k.val]'h + bE * CompactAdd.cExp P256 k.val
        else 0) := by
      by_cases hk : k.val < 4
      · simp only [hk, ↓reduceDIte, hrVar]
        rw [Vector.getElem_mapRange]
      · simp only [hk, ↓reduceDIte]
    rw [hterm]
    exact canonical_lhs_bound env.toEnvironment rVar _ bN hb_cast hb2 hr_lt k
  · exact canonical_rhs_bound env.toEnvironment input_var input h_input h_assumptions
  ·
    rw [show limbBits = (64 : ℕ) from rfl, hvecExpr]
    exact canonical_linIdent env.toEnvironment input_var rVar bE hbEdef
  ·
    have h_lhs_poly :
        polyValue limbBits
          (Vector.map (Expression.eval env.toEnvironment)
            (Vector.mapFinRange 5 fun k =>
              if h : k.val < 4 then
                var { index := i₀ + k.val } + bE * CompactAdd.cExp P256 k.val
              else 0)) =
          BigInt.value limbBits (Vector.map (Expression.eval env.toEnvironment) rVar) + bN * P256 := by
      rw [hvecExpr]
      exact polyValue_lhs env.toEnvironment rVar _ bN hb_cast hb2 hr_lt
    rw [h_lhs_poly, polyValue_rhs env.toEnvironment input_var input h_input,
      hvec, value_emuOfNat hrN_pow, hbNdef, hrNdef, ← hvx]
    have h := Nat.div_add_mod vx P256
    have hc : (vx / P256) * P256 = P256 * (vx / P256) := Nat.mul_comm _ _
    omega

end Canonicalize
end Solution.Secp256k1ScalarMulFixedBase

end DonorFile2_0

-- Adapted donor module: CompleteAddTheorems
section DonorFile2_1

namespace Solution.Secp256k1ScalarMulFixedBase
namespace CompleteAdd

lemma P256_pos : 0 < P256 := by decide

lemma P256_lt : P256 < 2 ^ (limbBits * numLimbs) := by decide

lemma two_pow_limb_lt : 2 ^ limbBits < circomPrime := by decide

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

lemma pConst_normalized (env : Environment (F circomPrime)) :
    BigInt.Normalized limbBits (Vector.map (Expression.eval env) pConst) := by
  rw [pConst, eval_emuConst]
  exact emuOfNat_normalized P256

lemma pConst_value (env : Environment (F circomPrime)) :
    BigInt.value limbBits (Vector.map (Expression.eval env) pConst) = P256 := by
  rw [pConst, eval_emuConst]
  exact value_emuOfNat P256_lt

lemma two_ne_zero_fp : (2 : Specs.Secp256k1.Fp) ≠ 0 := by
  have h2 : ((2 : ℕ) : Specs.Secp256k1.Fp) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hdvd
    have hle : P256 ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    have : 2 < P256 := by decide
    omega
  simpa using h2

lemma eq_or_eq_neg_of_sq_eq {K : Type} [Field K] {a b : K} (h : a ^ 2 = b ^ 2) :
    a = b ∨ a = -b := by
  have hz : (a - b) * (a + b) = 0 := by linear_combination h
  rcases mul_eq_zero.mp hz with h' | h'
  · exact Or.inl (sub_eq_zero.mp h')
  · exact Or.inr (eq_neg_of_add_eq_zero_left h')

theorem chord_oncurve {K : Type} [Field K] {x₁ y₁ x₂ y₂ s x₃ y₃ bb : K}
    (h₁ : y₁ ^ 2 = x₁ ^ 3 + bb) (h₂ : y₂ ^ 2 = x₂ ^ 3 + bb)
    (hne : x₂ - x₁ ≠ 0) (hs : s * (x₂ - x₁) = y₂ - y₁)
    (hx₃ : x₃ = s * s - x₁ - x₂) (hy₃ : y₃ = s * (x₁ - x₃) - y₁) :
    y₃ ^ 2 = x₃ ^ 3 + bb := by
  subst hx₃; subst hy₃
  apply mul_left_cancel₀ hne
  linear_combination ((x₂ - x₁) - (s * s - x₁ - x₂ - x₁)) * h₁
    + (s * s - x₁ - x₂ - x₁) * h₂
    + (s * s - x₁ - x₂ - x₁) * (y₁ + y₂ + s * (x₂ - x₁)) * hs

theorem tangent_oncurve {K : Type} [Field K] {x₁ y₁ s x₃ y₃ bb : K}
    (h₁ : y₁ ^ 2 = x₁ ^ 3 + bb) (hs : s * (2 * y₁) = 3 * x₁ ^ 2)
    (hx₃ : x₃ = s * s - x₁ - x₁) (hy₃ : y₃ = s * (x₁ - x₃) - y₁) :
    y₃ ^ 2 = x₃ ^ 3 + bb := by
  subst hx₃; subst hy₃
  linear_combination h₁ + (s * s - x₁ - x₁ - x₁) * hs

open Specs.ShortWeierstrass in
lemma add_inf_left (q : GroupPoint Specs.Secp256k1.Fp) :
    add Specs.Secp256k1.curve .infinity q = q := rfl

open Specs.ShortWeierstrass in
lemma add_inf_right (p : Point Specs.Secp256k1.Fp) :
    add Specs.Secp256k1.curve (.affine p) .infinity = .affine p := rfl

open Specs.ShortWeierstrass in
lemma add_affine (px py qx qy : Specs.Secp256k1.Fp) :
    add Specs.Secp256k1.curve (.affine ⟨px, py⟩) (.affine ⟨qx, qy⟩)
      = if px = qx then
          (if py = -qy then .infinity
            else .affine (tangent Specs.Secp256k1.curve ⟨px, py⟩))
        else .affine (chord ⟨px, py⟩ ⟨qx, qy⟩) := rfl

open Specs.ShortWeierstrass in

lemma onCurve_iff (p : Point Specs.Secp256k1.Fp) :
    OnCurve Specs.Secp256k1.curve p ↔ p.y ^ 2 = p.x ^ 3 + 7 := by
  simp [OnCurve, Specs.Secp256k1.curve]

open Specs.ShortWeierstrass in

lemma tangent_eq (px py : Specs.Secp256k1.Fp) :
    tangent Specs.Secp256k1.curve ⟨px, py⟩
      = { x := (3 * px ^ 2 / (2 * py)) ^ 2 - 2 * px,
          y := 3 * px ^ 2 / (2 * py)
            * (px - ((3 * px ^ 2 / (2 * py)) ^ 2 - 2 * px)) - py } := by
  simp [tangent, Specs.Secp256k1.curve]

open Specs.ShortWeierstrass in

lemma chord_eq (px py qx qy : Specs.Secp256k1.Fp) :
    chord ⟨px, py⟩ ⟨qx, qy⟩
      = { x := ((qy - py) / (qx - px)) ^ 2 - px - qx,
          y := (qy - py) / (qx - px)
            * (px - (((qy - py) / (qx - px)) ^ 2 - px - qx)) - py } := rfl

lemma decodePoint_of_isInf {p : FlaggedPoint (F circomPrime)} (h : p.isInf = 1) :
    decodePoint p = .infinity := by
  simp only [decodePoint]
  rw [if_pos h]

lemma decodePoint_of_finite {p : FlaggedPoint (F circomPrime)} (h : p.isInf = 0) :
    decodePoint p = .affine { x := decodeFe p.x, y := decodeFe p.y } := by
  simp only [decodePoint]
  rw [if_neg (by rw [h]; exact zero_ne_one)]

lemma decodePoint_mk_zero (x y : Emu (F circomPrime)) :
    decodePoint ⟨x, y, 0⟩ = .affine { x := decodeFe x, y := decodeFe y } :=
  decodePoint_of_finite rfl

theorem soundness_core
    {P Q s1 s2 out infv finv : FlaggedPoint (F circomPrime)}
    {dxv dyv syv x1sqv x1sq2v tNumv tDenv numv denv lamv lamSqv xsv x3v xdv yprodv y3v
      : Emu (F circomPrime)}
    {sameX oppY cancel : F circomPrime}
    (hP : P.Valid) (hQ : Q.Valid)
    (hdx : decodeFe dxv = decodeFe Q.x - decodeFe P.x)
    (hdy : decodeFe dyv = decodeFe Q.y - decodeFe P.y)
    (hsameX : sameX = if decodeFe dxv = 0 then 1 else 0)
    (hsy : decodeFe syv = decodeFe P.y + decodeFe Q.y)
    (hoppY : oppY = if decodeFe syv = 0 then 1 else 0)
    (hx1sq : decodeFe x1sqv = decodeFe P.x * decodeFe P.x)
    (hx1sq2 : decodeFe x1sq2v = decodeFe x1sqv + decodeFe x1sqv)
    (htNum : decodeFe tNumv = decodeFe x1sq2v + decodeFe x1sqv)
    (htDen : decodeFe tDenv = decodeFe P.y + decodeFe P.y)
    (hnum : numv = if sameX = 1 then tNumv else dyv)
    (hden : denv = if sameX = 1 then tDenv else dxv)
    (hlam : decodeFe denv ≠ 0 → decodeFe lamv * decodeFe denv = decodeFe numv)
    (hlamSq : decodeFe lamSqv = decodeFe lamv * decodeFe lamv)
    (hxs : decodeFe xsv = decodeFe lamSqv - decodeFe P.x)
    (hx3v : Fe.Valid x3v) (hx3 : decodeFe x3v = decodeFe xsv - decodeFe Q.x)
    (hxd : decodeFe xdv = decodeFe P.x - decodeFe x3v)
    (hyprod : decodeFe yprodv = decodeFe lamv * decodeFe xdv)
    (hy3v : Fe.Valid y3v) (hy3 : decodeFe y3v = decodeFe yprodv - decodeFe P.y)
    (hcancel : cancel = sameX * oppY)
    (hinfx : Fe.Valid infv.x) (hinfy : Fe.Valid infv.y) (hinff : infv.isInf = 1)
    (hfin : finv = ⟨x3v, y3v, 0⟩)
    (hs1 : s1 = if cancel = 1 then infv else finv)
    (hs2 : s2 = if Q.isInf = 1 then P else s1)
    (hout : out = if P.isInf = 1 then Q else s2) :
    out.Valid ∧
      decodePoint out =
        Specs.ShortWeierstrass.add Specs.Secp256k1.curve (decodePoint P) (decodePoint Q) := by
  rcases hP.1 with hPinf | hPinf
  ·
    have hPne1 : P.isInf ≠ 1 := by rw [hPinf]; exact zero_ne_one
    rw [hout, if_neg hPne1]
    rcases hQ.1 with hQinf | hQinf
    ·
      have hQne1 : Q.isInf ≠ 1 := by rw [hQinf]; exact zero_ne_one
      rw [hs2, if_neg hQne1, decodePoint_of_finite hPinf, decodePoint_of_finite hQinf,
        add_affine]
      have hPc : decodeFe P.y ^ 2 = decodeFe P.x ^ 3 + 7 :=
        (onCurve_iff _).mp (hP.2.2.2 hPinf)
      have hQc : decodeFe Q.y ^ 2 = decodeFe Q.x ^ 3 + 7 :=
        (onCurve_iff _).mp (hQ.2.2.2 hQinf)
      by_cases hxx : decodeFe Q.x = decodeFe P.x
      ·
        have hsx : sameX = 1 := by rw [hsameX, hdx, if_pos (by rw [hxx, sub_self])]
        rw [if_pos hxx.symm]
        by_cases hyy : decodeFe P.y + decodeFe Q.y = 0
        ·
          have hoy : oppY = 1 := by rw [hoppY, hsy, if_pos hyy]
          have hc1 : cancel = 1 := by rw [hcancel, hsx, hoy, one_mul]
          rw [hs1, if_pos hc1, if_pos (eq_neg_of_add_eq_zero_left hyy),
            decodePoint_of_isInf hinff]
          exact ⟨⟨Or.inr hinff, hinfx, hinfy,
            fun h0 => absurd (hinff.symm.trans h0) one_ne_zero⟩, rfl⟩
        ·
          have hoy : oppY = 0 := by rw [hoppY, hsy, if_neg hyy]
          have hc0 : cancel = 0 := by rw [hcancel, hoy, mul_zero]
          rw [hs1, if_neg (by rw [hc0]; exact zero_ne_one), hfin,
            if_neg (fun h => hyy (by rw [h]; ring))]

          have hqy : decodeFe Q.y = decodeFe P.y := by
            rcases eq_or_eq_neg_of_sq_eq (show decodeFe Q.y ^ 2 = decodeFe P.y ^ 2 by
              rw [hQc, hPc, hxx]) with h | h
            · exact h
            · exact absurd (by rw [h]; ring) hyy
          have hpy0 : decodeFe P.y ≠ 0 := by
            intro h0
            exact hyy (by rw [hqy, h0, add_zero])
          have h2py : decodeFe P.y + decodeFe P.y ≠ 0 := by
            rw [← two_mul]
            exact mul_ne_zero two_ne_zero_fp hpy0
          have hdenv : decodeFe denv = decodeFe P.y + decodeFe P.y := by
            rw [hden, if_pos hsx, htDen]
          have hlam' : decodeFe lamv * (decodeFe P.y + decodeFe P.y)
              = decodeFe P.x * decodeFe P.x + decodeFe P.x * decodeFe P.x
                + decodeFe P.x * decodeFe P.x := by
            have h := hlam (by rw [hdenv]; exact h2py)
            rw [hdenv] at h
            rw [h, hnum, if_pos hsx, htNum, hx1sq2, hx1sq]
          have hslope : decodeFe lamv = 3 * decodeFe P.x ^ 2 / (2 * decodeFe P.y) := by
            rw [eq_div_iff (by rw [two_mul]; exact h2py)]
            linear_combination hlam'
          have hX : decodeFe x3v
              = (3 * decodeFe P.x ^ 2 / (2 * decodeFe P.y)) ^ 2 - 2 * decodeFe P.x := by
            rw [hx3, hxs, hlamSq, hslope, hxx]; ring
          have hY : decodeFe y3v
              = 3 * decodeFe P.x ^ 2 / (2 * decodeFe P.y)
                * (decodeFe P.x
                  - ((3 * decodeFe P.x ^ 2 / (2 * decodeFe P.y)) ^ 2 - 2 * decodeFe P.x))
                - decodeFe P.y := by
            rw [hy3, hyprod, hxd, hslope, hX]
          refine ⟨⟨Or.inl rfl, hx3v, hy3v, fun _ => ?_⟩, ?_⟩
          · rw [onCurve_iff]
            exact tangent_oncurve (s := decodeFe lamv) hPc (by linear_combination hlam')
              (by rw [hx3, hxs, hlamSq, hxx]) (by rw [hy3, hyprod, hxd])
          · rw [decodePoint_mk_zero, tangent_eq]
            simp only [Specs.ShortWeierstrass.GroupPoint.affine.injEq,
              Specs.ShortWeierstrass.Point.mk.injEq]
            exact ⟨hX, hY⟩
      ·
        have hdne : decodeFe Q.x - decodeFe P.x ≠ 0 := sub_ne_zero.mpr hxx
        have hsx : sameX = 0 := by rw [hsameX, hdx, if_neg hdne]
        have hc0 : cancel = 0 := by rw [hcancel, hsx, zero_mul]
        rw [if_neg (fun h => hxx h.symm), hs1,
          if_neg (by rw [hc0]; exact zero_ne_one), hfin]
        have hdenv : decodeFe denv = decodeFe Q.x - decodeFe P.x := by
          rw [hden, if_neg (by rw [hsx]; exact zero_ne_one), hdx]
        have hlam' : decodeFe lamv * (decodeFe Q.x - decodeFe P.x)
            = decodeFe Q.y - decodeFe P.y := by
          have h := hlam (by rw [hdenv]; exact hdne)
          rw [hdenv] at h
          rw [h, hnum, if_neg (by rw [hsx]; exact zero_ne_one), hdy]
        have hslope : decodeFe lamv
            = (decodeFe Q.y - decodeFe P.y) / (decodeFe Q.x - decodeFe P.x) := by
          rw [eq_div_iff hdne]
          exact hlam'
        have hX : decodeFe x3v
            = ((decodeFe Q.y - decodeFe P.y) / (decodeFe Q.x - decodeFe P.x)) ^ 2
              - decodeFe P.x - decodeFe Q.x := by
          rw [hx3, hxs, hlamSq, hslope]; ring
        have hY : decodeFe y3v
            = (decodeFe Q.y - decodeFe P.y) / (decodeFe Q.x - decodeFe P.x)
              * (decodeFe P.x
                - (((decodeFe Q.y - decodeFe P.y) / (decodeFe Q.x - decodeFe P.x)) ^ 2
                  - decodeFe P.x - decodeFe Q.x))
              - decodeFe P.y := by
          rw [hy3, hyprod, hxd, hslope, hX]
        refine ⟨⟨Or.inl rfl, hx3v, hy3v, fun _ => ?_⟩, ?_⟩
        · rw [onCurve_iff]
          exact chord_oncurve hPc hQc hdne hlam'
            (by rw [hx3, hxs, hlamSq]) (by rw [hy3, hyprod, hxd])
        · rw [decodePoint_mk_zero, chord_eq]
          simp only [Specs.ShortWeierstrass.GroupPoint.affine.injEq,
            Specs.ShortWeierstrass.Point.mk.injEq]
          exact ⟨hX, hY⟩
    ·
      rw [hs2, if_pos hQinf]
      refine ⟨hP, ?_⟩
      rw [decodePoint_of_isInf hQinf, decodePoint_of_finite hPinf, add_inf_right]
  ·
    rw [hout, if_pos hPinf]
    refine ⟨hQ, ?_⟩
    rw [decodePoint_of_isInf hPinf, add_inf_left]

end CompleteAdd
end Solution.Secp256k1ScalarMulFixedBase

end DonorFile2_1

-- Adapted donor module: PairAddTheorems
section DonorFile2_2

namespace Solution.Secp256k1ScalarMulFixedBase
open Solution.Secp256k1ScalarMulFixedBase.Limbs

namespace PairAdd

open CompactAdd (cExp qpCoeff c976 cK)
open Canonicalize (eval_cExp polyValue_padded_gen)

def qpCoeffNat (env : Environment (F circomPrime)) (q : Var Emu (F circomPrime))
    (qtv k : ℕ) : ℕ :=
  (if h : k < 4 then (Expression.eval env (q[k]'h)).val * limbOfNat P256 0 else 0)
    + (if h : 1 ≤ k ∧ k - 1 < 4 then (Expression.eval env (q[k-1]'h.2)).val * limbOfNat P256 1 else 0)
    + (if h : 2 ≤ k ∧ k - 2 < 4 then (Expression.eval env (q[k-2]'h.2)).val * limbOfNat P256 2 else 0)
    + (if h : 3 ≤ k ∧ k - 3 < 4 then (Expression.eval env (q[k-3]'h.2)).val * limbOfNat P256 3 else 0)
    + (if k = 4 then qtv * limbOfNat P256 0 else 0)
    + (if k = 5 then qtv * limbOfNat P256 1 else 0)
    + (if k = 6 then qtv * limbOfNat P256 2 else 0)
    + (if k = 7 then qtv * limbOfNat P256 3 else 0)

lemma eval_qpCoeff_eq (env : Environment (F circomPrime)) (q : Var Emu (F circomPrime))
    (qt : Expression (F circomPrime)) (k : ℕ) :
    Expression.eval env (qpCoeff q qt k)
      = ((qpCoeffNat env q (Expression.eval env qt).val k : ℕ) : F circomPrime) := by
  rw [qpCoeff, qpCoeffNat]
  simp only [F, cExp,
    apply_dite (Expression.eval env), apply_ite (Expression.eval env),
    apply_dite (fun n : ℕ => (n : F circomPrime)), apply_ite (fun n : ℕ => (n : F circomPrime)),
    Nat.cast_add, Nat.cast_mul, Nat.cast_zero, ZMod.natCast_zmod_val,
    Expression.eval]

lemma qpCoeffNat_lt (env : Environment (F circomPrime)) (q : Var Emu (F circomPrime))
    (qtv k : ℕ) (hq : ∀ (i : ℕ) (h : i < 4), (Expression.eval env (q[i]'h)).val < 2 ^ 64)
    (hqt : qtv < 2 ^ 64) :
    qpCoeffNat env q qtv k < 4 * 2 ^ 128 := by
  have hlimb : ∀ j, limbOfNat P256 j < 2 ^ 64 := fun j => by
    have := limbOfNat_lt P256 j; simpa [limbBits] using this
  have hC : (2 : ℕ) ^ 64 * 2 ^ 64 = 2 ^ 128 := by norm_num
  have q04 : (if h : k < 4 then (Expression.eval env (q[k]'h)).val * limbOfNat P256 0 else 0)
      + (if k = 4 then qtv * limbOfNat P256 0 else 0) < 2 ^ 128 := by
    by_cases a : k < 4
    · rw [dif_pos a, if_neg (by omega : ¬ k = 4)]
      have := Nat.mul_lt_mul'' (hq k a) (hlimb 0); omega
    · rw [dif_neg a]
      by_cases b : k = 4
      · rw [if_pos b]; have := Nat.mul_lt_mul'' hqt (hlimb 0); omega
      · rw [if_neg b]; omega
  have q15 : (if h : 1 ≤ k ∧ k - 1 < 4 then (Expression.eval env (q[k-1]'h.2)).val * limbOfNat P256 1 else 0)
      + (if k = 5 then qtv * limbOfNat P256 1 else 0) < 2 ^ 128 := by
    by_cases a : 1 ≤ k ∧ k - 1 < 4
    · rw [dif_pos a, if_neg (by omega : ¬ k = 5)]
      have := Nat.mul_lt_mul'' (hq (k-1) a.2) (hlimb 1); omega
    · rw [dif_neg a]
      by_cases b : k = 5
      · rw [if_pos b]; have := Nat.mul_lt_mul'' hqt (hlimb 1); omega
      · rw [if_neg b]; omega
  have q26 : (if h : 2 ≤ k ∧ k - 2 < 4 then (Expression.eval env (q[k-2]'h.2)).val * limbOfNat P256 2 else 0)
      + (if k = 6 then qtv * limbOfNat P256 2 else 0) < 2 ^ 128 := by
    by_cases a : 2 ≤ k ∧ k - 2 < 4
    · rw [dif_pos a, if_neg (by omega : ¬ k = 6)]
      have := Nat.mul_lt_mul'' (hq (k-2) a.2) (hlimb 2); omega
    · rw [dif_neg a]
      by_cases b : k = 6
      · rw [if_pos b]; have := Nat.mul_lt_mul'' hqt (hlimb 2); omega
      · rw [if_neg b]; omega
  have q37 : (if h : 3 ≤ k ∧ k - 3 < 4 then (Expression.eval env (q[k-3]'h.2)).val * limbOfNat P256 3 else 0)
      + (if k = 7 then qtv * limbOfNat P256 3 else 0) < 2 ^ 128 := by
    by_cases a : 3 ≤ k ∧ k - 3 < 4
    · rw [dif_pos a, if_neg (by omega : ¬ k = 7)]
      have := Nat.mul_lt_mul'' (hq (k-3) a.2) (hlimb 3); omega
    · rw [dif_neg a]
      by_cases b : k = 7
      · rw [if_pos b]; have := Nat.mul_lt_mul'' hqt (hlimb 3); omega
      · rw [if_neg b]; omega
  unfold qpCoeffNat
  omega

lemma val_qpCoeff_eq (env : Environment (F circomPrime)) (q : Var Emu (F circomPrime))
    (qt : Expression (F circomPrime)) (k : ℕ)
    (hq : ∀ (i : ℕ) (h : i < 4), (Expression.eval env (q[i]'h)).val < 2 ^ 64)
    (hqt : (Expression.eval env qt).val < 2 ^ 64) :
    (Expression.eval env (qpCoeff q qt k)).val = qpCoeffNat env q (Expression.eval env qt).val k := by
  rw [eval_qpCoeff_eq]
  have hlt : qpCoeffNat env q (Expression.eval env qt).val k < circomPrime := by
    have := qpCoeffNat_lt env q (Expression.eval env qt).val k hq hqt
    have hb : 4 * 2 ^ 128 < circomPrime := by decide
    omega
  rw [ZMod.val_natCast_of_lt hlt]

set_option exponentiation.threshold 1200 in

lemma polyValue_qpCoeff (env : Environment (F circomPrime)) (q : Var Emu (F circomPrime))
    (qt : Expression (F circomPrime))
    (hq : ∀ (i : ℕ) (h : i < 4), (Expression.eval env (q[i]'h)).val < 2 ^ 64)
    (hqt : (Expression.eval env qt).val < 2 ^ 64) :
    (∑ k ∈ Finset.range 9, (Expression.eval env (qpCoeff q qt k)).val * 2 ^ (64 * k))
      = (BigInt.value 64 (Vector.map (Expression.eval env) q)
          + (Expression.eval env qt).val * 2 ^ 256) * P256 := by
  have hval : ∀ k, (Expression.eval env (qpCoeff q qt k)).val
      = qpCoeffNat env q (Expression.eval env qt).val k :=
    fun k => val_qpCoeff_eq env q qt k hq hqt
  simp only [hval]
  rw [value_eq_range_sum]
  conv_rhs => rw [← limb_sum_P256]
  simp only [numLimbs, Finset.sum_range_succ, Finset.sum_range_zero, Vector.getElem_map, qpCoeffNat,
    Nat.reduceLT, Nat.reduceSub, Nat.reduceLeDiff, Nat.reduceEqDiff,
    and_false, and_true, and_self,
    reduceDIte, reduceIte, add_zero, zero_add]
  ring

lemma val_qpCoeff_lt (env : Environment (F circomPrime)) (q : Var Emu (F circomPrime))
    (qt : Expression (F circomPrime)) (k : ℕ)
    (hq : ∀ (i : ℕ) (h : i < 4), (Expression.eval env (q[i]'h)).val < 2 ^ 64)
    (hqt : (Expression.eval env qt).val < 2 ^ 64) :
    (Expression.eval env (qpCoeff q qt k)).val < 4 * 2 ^ 128 := by
  rw [val_qpCoeff_eq env q qt k hq hqt]
  exact qpCoeffNat_lt env q (Expression.eval env qt).val k hq hqt

lemma eval_qpCoeff_high (env : Environment (F circomPrime)) (q : Var Emu (F circomPrime))
    (qt : Expression (F circomPrime)) (k : ℕ) (hk : 8 ≤ k) :
    (Expression.eval env (qpCoeff q qt k)).val = 0 := by
  rw [eval_qpCoeff_eq]
  have : qpCoeffNat env q (Expression.eval env qt).val k = 0 := by
    unfold qpCoeffNat
    rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  rw [this, Nat.cast_zero, ZMod.val_zero]

lemma val_qpCoeff_seven (env : Environment (F circomPrime)) (q : Var Emu (F circomPrime))
    (qt : Expression (F circomPrime))
    (hq : ∀ (i : ℕ) (h : i < 4), (Expression.eval env (q[i]'h)).val < 2 ^ 64)
    (hqt : (Expression.eval env qt).val < 2 ^ 3) :
    (Expression.eval env (qpCoeff q qt 7)).val < 2 ^ 67 := by
  rw [val_qpCoeff_eq env q qt 7 hq (by omega)]
  unfold qpCoeffNat
  rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl]
  have hlimb : limbOfNat P256 3 < 2 ^ 64 := by
    have := limbOfNat_lt P256 3; simpa [limbBits] using this
  have hm := Nat.mul_lt_mul'' hqt hlimb
  omega

lemma val_qpCoeff_tail (env : Environment (F circomPrime)) (q : Var Emu (F circomPrime))
    (qt : Expression (F circomPrime)) (k : ℕ) (hk : 7 ≤ k)
    (hq : ∀ (i : ℕ) (h : i < 4), (Expression.eval env (q[i]'h)).val < 2 ^ 64)
    (hqt : (Expression.eval env qt).val < 2 ^ 3) :
    (Expression.eval env (qpCoeff q qt k)).val < 2 ^ 67 := by
  rcases (show k = 7 ∨ 8 ≤ k by omega) with hk7 | hk8
  · rw [hk7]; exact val_qpCoeff_seven env q qt hq hqt
  · rw [eval_qpCoeff_high env q qt k hk8]; positivity

lemma digit_lt_of_norm (env : Environment (F circomPrime)) (a : Var Emu (F circomPrime))
    (h : BigInt.Normalized 64 (Vector.map (Expression.eval env) a)) :
    ∀ i : Fin 4, (Expression.eval env a[i.val]).val < 2 ^ 64 := by
  intro i; have := h i; rwa [Fin.getElem_fin, Vector.getElem_map] at this

lemma polyValue9_split (env : Environment (F circomPrime))
    (A B : Fin 9 → Expression (F circomPrime))
    (hb : ∀ k : Fin 9,
      (Expression.eval env (A k)).val + (Expression.eval env (B k)).val < circomPrime) :
    polyValue 64 (Vector.map (Expression.eval env) (Vector.mapFinRange 9 fun k => A k + B k))
      = (∑ k ∈ Finset.range 9,
          (if h : k < 9 then (Expression.eval env (A ⟨k, h⟩)).val else 0) * 2 ^ (64 * k))
        + (∑ k ∈ Finset.range 9,
          (if h : k < 9 then (Expression.eval env (B ⟨k, h⟩)).val else 0) * 2 ^ (64 * k)) := by
  rw [polyValue,
    ← Fin.sum_univ_eq_sum_range
      (fun k => (if h : k < 9 then (Expression.eval env (A ⟨k, h⟩)).val else 0) * 2 ^ (64 * k)),
    ← Fin.sum_univ_eq_sum_range
      (fun k => (if h : k < 9 then (Expression.eval env (B ⟨k, h⟩)).val else 0) * 2 ^ (64 * k)),
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [Vector.getElem_map, Vector.getElem_mapFinRange, dif_pos k.isLt, dif_pos k.isLt]
  have hk : (⟨k.val, k.isLt⟩ : Fin 9) = k := rfl
  rw [hk,
    show Expression.eval env (A k + B k) = Expression.eval env (A k) + Expression.eval env (B k) from rfl,
    ZMod.val_add_of_lt (hb k)]
  ring

lemma digit_lt_of_norm' (env : Environment (F circomPrime)) (a : Var Emu (F circomPrime))
    (h : BigInt.Normalized 64 (Vector.map (Expression.eval env) a)) :
    ∀ (i : ℕ) (hi : i < 4), (Expression.eval env (a[i]'hi)).val < 2 ^ 64 :=
  fun i hi => digit_lt_of_norm env a h ⟨i, hi⟩

lemma val_add3 (env : Environment (F circomPrime)) (a b c : Expression (F circomPrime))
    (ha : (Expression.eval env a).val < 2 ^ 64) (hb : (Expression.eval env b).val < 2 ^ 64)
    (hc : (Expression.eval env c).val < 2 ^ 64) :
    (Expression.eval env (a + b + c)).val
      = (Expression.eval env a).val + (Expression.eval env b).val + (Expression.eval env c).val := by
  have hpr : 3 * 2 ^ 64 < circomPrime := by decide
  rw [show Expression.eval env (a + b + c)
        = Expression.eval env a + Expression.eval env b + Expression.eval env c from rfl]
  have h1 : (Expression.eval env a + Expression.eval env b).val
      = (Expression.eval env a).val + (Expression.eval env b).val := ZMod.val_add_of_lt (by omega)
  rw [ZMod.val_add_of_lt (by rw [h1]; omega), h1]

lemma sum_guard_triple (env : Environment (F circomPrime)) (x1 xA xT1 : Var Emu (F circomPrime))
    (h1 : BigInt.Normalized 64 (Vector.map (Expression.eval env) x1))
    (hA : BigInt.Normalized 64 (Vector.map (Expression.eval env) xA))
    (hT1 : BigInt.Normalized 64 (Vector.map (Expression.eval env) xT1)) :
    (∑ k ∈ Finset.range 9,
        (if h : k < 9 then
          (Expression.eval env
            (if h' : k < 4 then x1[k]'h' + xA[k]'h' + xT1[k]'h' else 0)).val else 0) * 2 ^ (64 * k))
      = BigInt.value 64 (Vector.map (Expression.eval env) x1)
        + BigInt.value 64 (Vector.map (Expression.eval env) xA)
        + BigInt.value 64 (Vector.map (Expression.eval env) xT1) := by
  have d1 := digit_lt_of_norm' env x1 h1
  have dA := digit_lt_of_norm' env xA hA
  have dT1 := digit_lt_of_norm' env xT1 hT1
  rw [value_eq_range_sum 64 (Vector.map (Expression.eval env) x1),
    value_eq_range_sum 64 (Vector.map (Expression.eval env) xA),
    value_eq_range_sum 64 (Vector.map (Expression.eval env) xT1)]
  simp only [numLimbs, Finset.sum_range_succ, Finset.sum_range_zero, Vector.getElem_map,
    Nat.reduceLT, reduceDIte]
  have hz : Expression.eval env (0 : Expression (F circomPrime)) = 0 := rfl
  rw [val_add3 env _ _ _ (d1 0 (by omega)) (dA 0 (by omega)) (dT1 0 (by omega)),
    val_add3 env _ _ _ (d1 1 (by omega)) (dA 1 (by omega)) (dT1 1 (by omega)),
    val_add3 env _ _ _ (d1 2 (by omega)) (dA 2 (by omega)) (dT1 2 (by omega)),
    val_add3 env _ _ _ (d1 3 (by omega)) (dA 3 (by omega)) (dT1 3 (by omega))]
  simp only [hz, ZMod.val_zero, zero_mul, add_zero]
  ring

lemma polyValue_o2_rhs (env : Environment (F circomPrime))
    (q6 : Var Emu (F circomPrime)) (q6t : Expression (F circomPrime))
    (x1 xA xT1 : Var Emu (F circomPrime))
    (hq6 : BigInt.Normalized 64 (Vector.map (Expression.eval env) q6))
    (hq6t : (Expression.eval env q6t).val < 2 ^ 64)
    (hx1 : BigInt.Normalized 64 (Vector.map (Expression.eval env) x1))
    (hxA : BigInt.Normalized 64 (Vector.map (Expression.eval env) xA))
    (hxT1 : BigInt.Normalized 64 (Vector.map (Expression.eval env) xT1)) :
    polyValue 64 (Vector.map (Expression.eval env)
        (Vector.mapFinRange 9 fun k =>
          qpCoeff q6 q6t k.val
            + (if h : k.val < 4 then x1[k.val]'h + xA[k.val]'h + xT1[k.val]'h else 0)))
      = (BigInt.value 64 (Vector.map (Expression.eval env) q6)
          + (Expression.eval env q6t).val * 2 ^ 256) * P256
        + BigInt.value 64 (Vector.map (Expression.eval env) x1)
        + BigInt.value 64 (Vector.map (Expression.eval env) xA)
        + BigInt.value 64 (Vector.map (Expression.eval env) xT1) := by
  have hq6d := digit_lt_of_norm' env q6 hq6
  rw [polyValue9_split env (fun k => qpCoeff q6 q6t k.val)
    (fun k => if h : k.val < 4 then x1[k.val]'h + xA[k.val]'h + xT1[k.val]'h else 0)
    (by
      intro k
      dsimp only
      have hq := val_qpCoeff_lt env q6 q6t k.val hq6d hq6t
      have hg : (Expression.eval env
          (if h : k.val < 4 then x1[k.val]'h + xA[k.val]'h + xT1[k.val]'h else 0)).val < 3 * 2 ^ 64 := by
        by_cases hk : k.val < 4
        · rw [dif_pos hk, val_add3 env _ _ _ (digit_lt_of_norm' env x1 hx1 k.val hk)
            (digit_lt_of_norm' env xA hxA k.val hk) (digit_lt_of_norm' env xT1 hxT1 k.val hk)]
          have := digit_lt_of_norm' env x1 hx1 k.val hk
          have := digit_lt_of_norm' env xA hxA k.val hk
          have := digit_lt_of_norm' env xT1 hxT1 k.val hk
          omega
        · rw [dif_neg hk, show Expression.eval env (0 : Expression (F circomPrime)) = 0 from rfl,
            ZMod.val_zero]; positivity
      have hpr : 4 * 2 ^ 128 + 3 * 2 ^ 64 < circomPrime := by decide
      omega)]
  rw [sum_guard_triple env x1 xA xT1 hx1 hxA hxT1]
  rw [show (∑ k ∈ Finset.range 9,
        (if h : k < 9 then (Expression.eval env (qpCoeff q6 q6t (⟨k, h⟩ : Fin 9).val)).val else 0)
          * 2 ^ (64 * k))
      = ∑ k ∈ Finset.range 9, (Expression.eval env (qpCoeff q6 q6t k)).val * 2 ^ (64 * k) from by
    apply Finset.sum_congr rfl; intro k hk; rw [dif_pos (Finset.mem_range.mp hk)]]
  rw [polyValue_qpCoeff env q6 q6t hq6d hq6t]
  ring

lemma polyValue_pad9_7 (env : Environment (F circomPrime))
    (P : Vector (Expression (F circomPrime)) 7) :
    (∑ k ∈ Finset.range 9,
        (if h : k < 9 then
          (Expression.eval env (if h' : k < 7 then P[k]'h' else 0)).val else 0) * 2 ^ (64 * k))
      = polyValue 64 (Vector.map (Expression.eval env) P) := by
  rw [polyValue]
  have hfin : (∑ k : Fin 7, ((Vector.map (Expression.eval env) P)[k.val]).val * 2 ^ (64 * k.val))
      = ∑ k ∈ Finset.range 7,
          (if h' : k < 7 then (Expression.eval env (P[k]'h')).val else 0) * 2 ^ (64 * k) := by
    rw [← Fin.sum_univ_eq_sum_range
      (fun k => (if h' : k < 7 then (Expression.eval env (P[k]'h')).val else 0) * 2 ^ (64 * k))]
    apply Finset.sum_congr rfl
    intro k _
    rw [dif_pos k.isLt, Vector.getElem_map]
  rw [hfin, ← Finset.sum_subset (Finset.range_subset_range.mpr (by omega : 7 ≤ 9))
    (f := fun k => (if h : k < 9 then
        (Expression.eval env (if h' : k < 7 then P[k]'h' else 0)).val else 0) * 2 ^ (64 * k))]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    rw [dif_pos (by omega : k < 9), dif_pos hk, dif_pos hk]
  · intro k hk9 hk7
    rw [Finset.mem_range] at hk9
    rw [Finset.mem_range] at hk7
    rw [dif_pos (by omega : k < 9), dif_neg (by omega : ¬ k < 7),
      show Expression.eval env (0 : Expression (F circomPrime)) = 0 from rfl, ZMod.val_zero,
      Nat.zero_mul]

lemma polyValue_pad9_cExp (env : Environment (F circomPrime)) (v : ℕ) (hv : v < 2 ^ 320) :
    (∑ k ∈ Finset.range 9,
        (if h : k < 9 then (Expression.eval env (if k < 5 then cExp v k else 0)).val else 0)
          * 2 ^ (64 * k))
      = v := by
  have hstep : (∑ k ∈ Finset.range 9,
        (if h : k < 9 then (Expression.eval env (if k < 5 then cExp v k else 0)).val else 0)
          * 2 ^ (64 * k))
      = ∑ k ∈ Finset.range 5, (v / 2 ^ (64 * k) % 2 ^ 64) * 2 ^ (64 * k) := by
    rw [← Finset.sum_subset (Finset.range_subset_range.mpr (by omega : 5 ≤ 9))
      (f := fun k => (if h : k < 9 then
          (Expression.eval env (if k < 5 then cExp v k else 0)).val else 0) * 2 ^ (64 * k))]
    · apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_range] at hk
      rw [dif_pos (by omega : k < 9), if_pos hk, eval_cExp, val_limbOfNat]
      rfl
    · intro k hk9 hk5
      rw [Finset.mem_range] at hk9
      rw [Finset.mem_range] at hk5
      rw [dif_pos (by omega : k < 9), if_neg (by omega : ¬ k < 5),
        show Expression.eval env (0 : Expression (F circomPrime)) = 0 from rfl, ZMod.val_zero,
        Nat.zero_mul]
  rw [hstep, limb_decomp_mod 64 5 v, Nat.mod_eq_of_lt (by
    have : (2:ℕ) ^ (64 * 5) = 2 ^ 320 := by norm_num
    omega)]

lemma polyValue_o2_lhs (env : Environment (F circomPrime)) (lam1 : Var Emu (F circomPrime))
    (P : Vector (Expression (F circomPrime)) 7)
    (hP : ∀ k : Fin 7,
      Expression.eval env P[k.val] = Expression.eval env (bigIntMulNoReduce lam1 lam1)[k.val])
    (hlam : BigInt.Normalized 64 (Vector.map (Expression.eval env) lam1)) :
    polyValue 64 (Vector.map (Expression.eval env)
        (Vector.mapFinRange 9 fun k =>
          (if h : k.val < 7 then P[k.val]'h else 0)
            + (if k.val < 5 then cExp (4 * P256) k.val else 0)))
      = BigInt.value 64 (Vector.map (Expression.eval env) lam1)
          * BigInt.value 64 (Vector.map (Expression.eval env) lam1) + 4 * P256 := by
  have hdig := digit_lt_of_norm env lam1 hlam
  rw [polyValue9_split env (fun k => if h : k.val < 7 then P[k.val]'h else 0)
    (fun k => if k.val < 5 then cExp (4 * P256) k.val else 0)
    (by
      intro k
      dsimp only
      have hA : (Expression.eval env (if h : k.val < 7 then P[k.val]'h else 0)).val < 4 * 2 ^ 128 := by
        by_cases hk : k.val < 7
        · rw [dif_pos hk, hP ⟨k.val, hk⟩]
          exact val_bigIntMulNoReduce_coeff_lt env lam1 lam1 ⟨k.val, hk⟩ hdig hdig (by decide)
        · rw [dif_neg hk, show Expression.eval env (0 : Expression (F circomPrime)) = 0 from rfl,
            ZMod.val_zero]; positivity
      have hB : (Expression.eval env (if k.val < 5 then cExp (4 * P256) k.val else 0)).val < 2 ^ 64 := by
        by_cases hk : k.val < 5
        · rw [if_pos hk, eval_cExp, val_limbOfNat]; exact limbOfNat_lt _ _
        · rw [if_neg hk, show Expression.eval env (0 : Expression (F circomPrime)) = 0 from rfl,
            ZMod.val_zero]; positivity
      have hpr : 4 * 2 ^ 128 + 2 ^ 64 < circomPrime := by decide
      omega)]
  dsimp only
  rw [polyValue_pad9_7 env P, polyValue_pad9_cExp env (4 * P256) (by decide)]
  have hpv : polyValue 64 (Vector.map (Expression.eval env) P)
      = BigInt.value 64 (Vector.map (Expression.eval env) lam1)
        * BigInt.value 64 (Vector.map (Expression.eval env) lam1) := by
    rw [← MulMod.polyValue_mul_eq env lam1 lam1 hdig hdig (by decide)]
    simp only [polyValue, Vector.getElem_map]
    apply Finset.sum_congr rfl
    intro i _
    rw [hP i]
  rw [hpv]

lemma o2_identity (env : Environment (F circomPrime))
    (lam1 x1 xA xT1 q6 : Var Emu (F circomPrime)) (q6t : Expression (F circomPrime))
    (P : Vector (Expression (F circomPrime)) 7)
    (hP : ∀ k : Fin 7,
      Expression.eval env P[k.val] = Expression.eval env (bigIntMulNoReduce lam1 lam1)[k.val])
    (hlam : BigInt.Normalized 64 (Vector.map (Expression.eval env) lam1))
    (hx1 : BigInt.Normalized 64 (Vector.map (Expression.eval env) x1))
    (hxA : BigInt.Normalized 64 (Vector.map (Expression.eval env) xA))
    (hxT1 : BigInt.Normalized 64 (Vector.map (Expression.eval env) xT1))
    (hq6 : BigInt.Normalized 64 (Vector.map (Expression.eval env) q6))
    (hq6t : (Expression.eval env q6t).val < 2 ^ 64)
    (hspec : polyValue 64 (Vector.map (Expression.eval env)
          (Vector.mapFinRange 9 fun k =>
            (if h : k.val < 7 then P[k.val]'h else 0)
              + (if k.val < 5 then cExp (4 * P256) k.val else 0)))
        = polyValue 64 (Vector.map (Expression.eval env)
          (Vector.mapFinRange 9 fun k =>
            qpCoeff q6 q6t k.val
              + (if h : k.val < 4 then x1[k.val]'h + xA[k.val]'h + xT1[k.val]'h else 0)))) :
    (BigInt.value 64 (Vector.map (Expression.eval env) lam1)
          * BigInt.value 64 (Vector.map (Expression.eval env) lam1) + 4 * P256
        = (BigInt.value 64 (Vector.map (Expression.eval env) q6)
            + (Expression.eval env q6t).val * 2 ^ 256) * P256
          + BigInt.value 64 (Vector.map (Expression.eval env) x1)
          + BigInt.value 64 (Vector.map (Expression.eval env) xA)
          + BigInt.value 64 (Vector.map (Expression.eval env) xT1))
      ∧ (decodeFe (Vector.map (Expression.eval env) x1)
          = decodeFe (Vector.map (Expression.eval env) lam1) ^ 2
            - decodeFe (Vector.map (Expression.eval env) xA)
            - decodeFe (Vector.map (Expression.eval env) xT1)) := by
  have hL := polyValue_o2_lhs env lam1 P hP hlam
  have hR := polyValue_o2_rhs env q6 q6t x1 xA xT1 hq6 hq6t hx1 hxA hxT1
  have hnat := hL.symm.trans (hspec.trans hR)
  refine ⟨hnat, ?_⟩
  have hcast := congrArg (Nat.cast : ℕ → Specs.Secp256k1.Fp) hnat
  push_cast at hcast
  rw [show ((P256 : ℕ) : Specs.Secp256k1.Fp) = 0 from ZMod.natCast_self _] at hcast
  simp only [decodeFe, limbBits, mul_zero, add_zero, zero_add] at hcast ⊢
  rw [sq]
  linear_combination -hcast

lemma boundAt_quadFlexT_lo (k : Fin 9) (hk : k.val < 7) :
    EqViaCarriesFlex.boundAt EqViaCarriesFlexT.quadFlexT.M k.val = 5 * 2 ^ 128 := by
  fin_cases k <;> revert hk <;> decide

lemma boundAt_quadFlexT_hi (k : Fin 9) (hk : 7 ≤ k.val) :
    EqViaCarriesFlex.boundAt EqViaCarriesFlexT.quadFlexT.M k.val = 2 ^ 67 := by
  fin_cases k <;> revert hk <;> decide

lemma o2_discharge (env : Environment (F circomPrime))
    (lam1 x1 xA xT1 q6 : Var Emu (F circomPrime)) (q6t : Expression (F circomPrime))
    (P : Vector (Expression (F circomPrime)) 7)
    (hP : ∀ k : Fin 7,
      Expression.eval env P[k.val] = Expression.eval env (bigIntMulNoReduce lam1 lam1)[k.val])
    (hlam : BigInt.Normalized 64 (Vector.map (Expression.eval env) lam1))
    (hx1 : BigInt.Normalized 64 (Vector.map (Expression.eval env) x1))
    (hxA : BigInt.Normalized 64 (Vector.map (Expression.eval env) xA))
    (hxT1 : BigInt.Normalized 64 (Vector.map (Expression.eval env) xT1))
    (hq6 : BigInt.Normalized 64 (Vector.map (Expression.eval env) q6))
    (hq6t : (Expression.eval env q6t).val < 2 ^ 3) :
    (∀ k : Fin 9,
        ((Vector.map (Expression.eval env)
          (Vector.mapFinRange 9 fun k =>
            (if h : k.val < 7 then P[k.val]'h else 0)
              + (if k.val < 5 then cExp (4 * P256) k.val else 0)))[k.val]).val
        < EqViaCarriesFlex.boundAt EqViaCarriesFlexT.quadFlexT.M k.val)
    ∧ (∀ k : Fin 9,
        ((Vector.map (Expression.eval env)
          (Vector.mapFinRange 9 fun k =>
            qpCoeff q6 q6t k.val
              + (if h : k.val < 4 then x1[k.val]'h + xA[k.val]'h + xT1[k.val]'h else 0)))[k.val]).val
        < EqViaCarriesFlex.boundAt EqViaCarriesFlexT.quadFlexT.M k.val) := by
  have hdig := digit_lt_of_norm env lam1 hlam
  have hq6d := digit_lt_of_norm' env q6 hq6
  have hq6t64 : (Expression.eval env q6t).val < 2 ^ 64 := by omega
  constructor
  · intro k
    rw [Vector.getElem_map, Vector.getElem_mapFinRange]
    by_cases hk7 : k.val < 7
    · rw [boundAt_quadFlexT_lo k hk7]
      have hA : (Expression.eval env (if h : k.val < 7 then P[k.val]'h else 0)).val < 4 * 2 ^ 128 := by
        rw [dif_pos hk7, hP ⟨k.val, hk7⟩]
        exact val_bigIntMulNoReduce_coeff_lt env lam1 lam1 ⟨k.val, hk7⟩ hdig hdig (by decide)
      have hB : (Expression.eval env (if k.val < 5 then cExp (4 * P256) k.val else 0)).val < 2 ^ 64 := by
        by_cases hk : k.val < 5
        · rw [if_pos hk, eval_cExp, val_limbOfNat]; exact limbOfNat_lt _ _
        · rw [if_neg hk, show Expression.eval env (0 : Expression (F circomPrime)) = 0 from rfl,
            ZMod.val_zero]; positivity
      have hle := ZMod.val_add_le
        (Expression.eval env (if h : k.val < 7 then P[k.val]'h else 0))
        (Expression.eval env (if k.val < 5 then cExp (4 * P256) k.val else 0))
      rw [show Expression.eval env
            ((if h : k.val < 7 then P[k.val]'h else 0) + (if k.val < 5 then cExp (4 * P256) k.val else 0))
          = Expression.eval env (if h : k.val < 7 then P[k.val]'h else 0)
            + Expression.eval env (if k.val < 5 then cExp (4 * P256) k.val else 0) from rfl]
      omega
    · rw [boundAt_quadFlexT_hi k (by omega),
        show Expression.eval env
            ((if h : k.val < 7 then P[k.val]'h else 0) + (if k.val < 5 then cExp (4 * P256) k.val else 0))
          = Expression.eval env (if h : k.val < 7 then P[k.val]'h else 0)
            + Expression.eval env (if k.val < 5 then cExp (4 * P256) k.val else 0) from rfl,
        dif_neg hk7, if_neg (show ¬ k.val < 5 by omega),
        show Expression.eval env (0 : Expression (F circomPrime)) = 0 from rfl, add_zero,
        ZMod.val_zero]
      positivity
  · intro k
    rw [Vector.getElem_map, Vector.getElem_mapFinRange]
    have hg : (Expression.eval env
        (if h : k.val < 4 then x1[k.val]'h + xA[k.val]'h + xT1[k.val]'h else 0)).val < 3 * 2 ^ 64 := by
      by_cases hk : k.val < 4
      · rw [dif_pos hk, val_add3 env _ _ _ (digit_lt_of_norm' env x1 hx1 k.val hk)
          (digit_lt_of_norm' env xA hxA k.val hk) (digit_lt_of_norm' env xT1 hxT1 k.val hk)]
        have := digit_lt_of_norm' env x1 hx1 k.val hk
        have := digit_lt_of_norm' env xA hxA k.val hk
        have := digit_lt_of_norm' env xT1 hxT1 k.val hk
        omega
      · rw [dif_neg hk, show Expression.eval env (0 : Expression (F circomPrime)) = 0 from rfl,
          ZMod.val_zero]; positivity
    have hle := ZMod.val_add_le (Expression.eval env (qpCoeff q6 q6t k.val))
      (Expression.eval env (if h : k.val < 4 then x1[k.val]'h + xA[k.val]'h + xT1[k.val]'h else 0))
    rw [show Expression.eval env
          (qpCoeff q6 q6t k.val + (if h : k.val < 4 then x1[k.val]'h + xA[k.val]'h + xT1[k.val]'h else 0))
        = Expression.eval env (qpCoeff q6 q6t k.val)
          + Expression.eval env (if h : k.val < 4 then x1[k.val]'h + xA[k.val]'h + xT1[k.val]'h else 0)
        from rfl]
    by_cases hk7 : k.val < 7
    · rw [boundAt_quadFlexT_lo k hk7]
      have hqp := val_qpCoeff_lt env q6 q6t k.val hq6d hq6t64
      omega
    · rw [boundAt_quadFlexT_hi k (by omega)]
      have hg0 : (Expression.eval env
          (if h : k.val < 4 then x1[k.val]'h + xA[k.val]'h + xT1[k.val]'h else 0)).val = 0 := by
        rw [dif_neg (show ¬ k.val < 4 by omega),
          show Expression.eval env (0 : Expression (F circomPrime)) = 0 from rfl, ZMod.val_zero]
      have hqp := val_qpCoeff_tail env q6 q6t k.val (by omega) hq6d hq6t
      omega

lemma polyValue5_eq (env : Environment (F circomPrime))
    (g : Fin 5 → Expression (F circomPrime)) :
    polyValue 64 (Vector.map (Expression.eval env) (Vector.mapFinRange 5 g))
      = ∑ k ∈ Finset.range 5,
          (if h : k < 5 then (Expression.eval env (g ⟨k, h⟩)).val else 0) * 2 ^ (64 * k) := by
  rw [polyValue, ← Fin.sum_univ_eq_sum_range
      (fun k => (if h : k < 5 then (Expression.eval env (g ⟨k, h⟩)).val else 0) * 2 ^ (64 * k))]
  apply Finset.sum_congr rfl
  intro k _
  rw [Vector.getElem_map, Vector.getElem_mapFinRange, dif_pos k.isLt]

lemma limb_sum_range (m v : ℕ) (hv : v < 2 ^ (64 * m)) :
    (∑ k ∈ Finset.range m, limbOfNat v k * 2 ^ (64 * k)) = v := by
  have h : (∑ k ∈ Finset.range m, limbOfNat v k * 2 ^ (64 * k))
      = ∑ k ∈ Finset.range m, (v / 2 ^ (64 * k) % 2 ^ 64) * 2 ^ (64 * k) :=
    Finset.sum_congr rfl fun k _ => rfl
  rw [h, limb_decomp_mod, Nat.mod_eq_of_lt hv]

lemma val_add2 (env : Environment (F circomPrime)) (a b : Expression (F circomPrime))
    (ha : (Expression.eval env a).val < 2 ^ 64) (hb : (Expression.eval env b).val < 2 ^ 64) :
    (Expression.eval env (a + b)).val
      = (Expression.eval env a).val + (Expression.eval env b).val := by
  have hlt : (Expression.eval env a).val + (Expression.eval env b).val < circomPrime := by
    have h2 : (2:ℕ) ^ 64 + 2 ^ 64 < circomPrime := by decide
    omega
  rw [show Expression.eval env (a + b) = Expression.eval env a + Expression.eval env b from rfl,
    ZMod.val_add_of_lt hlt]

lemma val_add_cExp (env : Environment (F circomPrime)) (a : Expression (F circomPrime)) (v k : ℕ)
    (ha : (Expression.eval env a).val < 2 ^ 64) :
    (Expression.eval env (a + cExp v k)).val = (Expression.eval env a).val + limbOfNat v k := by
  have hc : (Expression.eval env (cExp v k)).val = limbOfNat v k := by
    rw [eval_cExp, val_limbOfNat]
  have hlt : (Expression.eval env a).val + (Expression.eval env (cExp v k)).val < circomPrime := by
    rw [hc]
    have hb := limbOfNat_lt v k
    simp only [limbBits] at hb
    have h2 : (2:ℕ) ^ 64 + 2 ^ 64 < circomPrime := by decide
    omega
  rw [show Expression.eval env (a + cExp v k)
        = Expression.eval env a + Expression.eval env (cExp v k) from rfl,
    ZMod.val_add_of_lt hlt, hc]

lemma polyValue_dblock_lhs (env : Environment (F circomPrime))
    (d xA : Var Emu (F circomPrime)) (d4 : Expression (F circomPrime))
    (hd : BigInt.Normalized 64 (Vector.map (Expression.eval env) d))
    (hxA : BigInt.Normalized 64 (Vector.map (Expression.eval env) xA)) :
    polyValue 64 (Vector.map (Expression.eval env)
        (Vector.mapFinRange 5 fun k => if h : k.val < 4 then d[k.val]'h + xA[k.val]'h else d4))
      = BigInt.value 64 (Vector.map (Expression.eval env) d)
        + (Expression.eval env d4).val * 2 ^ 256
        + BigInt.value 64 (Vector.map (Expression.eval env) xA) := by
  have dd := digit_lt_of_norm' env d hd
  have dA := digit_lt_of_norm' env xA hxA
  rw [polyValue5_eq, value_eq_range_sum 64 (Vector.map (Expression.eval env) d),
    value_eq_range_sum 64 (Vector.map (Expression.eval env) xA)]
  simp only [numLimbs, Finset.sum_range_succ, Finset.sum_range_zero, Vector.getElem_map,
    Nat.reduceLT, Nat.reduceMul, reduceDIte, zero_add]
  rw [val_add2 env _ _ (dd 0 (by omega)) (dA 0 (by omega)),
    val_add2 env _ _ (dd 1 (by omega)) (dA 1 (by omega)),
    val_add2 env _ _ (dd 2 (by omega)) (dA 2 (by omega)),
    val_add2 env _ _ (dd 3 (by omega)) (dA 3 (by omega))]
  ring

lemma polyValue_dblock_rhs (env : Environment (F circomPrime)) (xT : Var Emu (F circomPrime))
    (hxT : BigInt.Normalized 64 (Vector.map (Expression.eval env) xT)) :
    polyValue 64 (Vector.map (Expression.eval env)
        (Vector.mapFinRange 5 fun k =>
          if h : k.val < 4 then xT[k.val]'h + cExp (2 * P256) k.val else cExp (2 * P256) 4))
      = BigInt.value 64 (Vector.map (Expression.eval env) xT) + 2 * P256 := by
  have dT := digit_lt_of_norm' env xT hxT
  have hls : limbOfNat (2 * P256) 0 * 2 ^ 0 + limbOfNat (2 * P256) 1 * 2 ^ 64
      + limbOfNat (2 * P256) 2 * 2 ^ 128 + limbOfNat (2 * P256) 3 * 2 ^ 192
      + limbOfNat (2 * P256) 4 * 2 ^ 256 = 2 * P256 := by
    have key := limb_sum_range 5 (2 * P256) (by
      have h : P256 < 2 ^ 256 := P256_lt
      have e1 : (2:ℕ) ^ 257 = 2 ^ 256 * 2 := pow_succ 2 256
      have e2 : (2:ℕ) ^ 257 ≤ 2 ^ (64 * 5) := Nat.pow_le_pow_right (by norm_num) (by norm_num)
      omega)
    simpa [Finset.sum_range_succ, Finset.sum_range_zero] using key
  rw [polyValue5_eq, value_eq_range_sum 64 (Vector.map (Expression.eval env) xT)]
  simp only [numLimbs, Finset.sum_range_succ, Finset.sum_range_zero, Vector.getElem_map,
    Nat.reduceLT, Nat.reduceMul, reduceDIte, zero_add]
  rw [val_add_cExp env _ (2 * P256) 0 (dT 0 (by omega)),
    val_add_cExp env _ (2 * P256) 1 (dT 1 (by omega)),
    val_add_cExp env _ (2 * P256) 2 (dT 2 (by omega)),
    val_add_cExp env _ (2 * P256) 3 (dT 3 (by omega)),
    show Expression.eval env (cExp (2 * P256) 4) = ((limbOfNat (2 * P256) 4 : ℕ) : F circomPrime)
      from eval_cExp env (2 * P256) 4, val_limbOfNat]
  conv_rhs => rw [← hls]
  ring

lemma dblock_identity (env : Environment (F circomPrime))
    (d xA xT : Var Emu (F circomPrime)) (d4 : Expression (F circomPrime))
    (hd : BigInt.Normalized 64 (Vector.map (Expression.eval env) d))
    (hxA : BigInt.Normalized 64 (Vector.map (Expression.eval env) xA))
    (hxT : BigInt.Normalized 64 (Vector.map (Expression.eval env) xT))
    (hspec : polyValue 64 (Vector.map (Expression.eval env)
          (Vector.mapFinRange 5 fun k => if h : k.val < 4 then d[k.val]'h + xA[k.val]'h else d4))
        = polyValue 64 (Vector.map (Expression.eval env)
          (Vector.mapFinRange 5 fun k =>
            if h : k.val < 4 then xT[k.val]'h + cExp (2 * P256) k.val else cExp (2 * P256) 4))) :
    BigInt.value 64 (Vector.map (Expression.eval env) d)
        + (Expression.eval env d4).val * 2 ^ 256
        + BigInt.value 64 (Vector.map (Expression.eval env) xA)
      = BigInt.value 64 (Vector.map (Expression.eval env) xT) + 2 * P256 := by
  have hL := polyValue_dblock_lhs env d xA d4 hd hxA
  have hR := polyValue_dblock_rhs env xT hxT
  exact hL.symm.trans (hspec.trans hR)

lemma dblock_fp (env : Environment (F circomPrime))
    (d xA xT : Var Emu (F circomPrime)) (d4 : Expression (F circomPrime))
    (hd : BigInt.Normalized 64 (Vector.map (Expression.eval env) d))
    (hxA : BigInt.Normalized 64 (Vector.map (Expression.eval env) xA))
    (hxT : BigInt.Normalized 64 (Vector.map (Expression.eval env) xT))
    (hspec : polyValue 64 (Vector.map (Expression.eval env)
          (Vector.mapFinRange 5 fun k => if h : k.val < 4 then d[k.val]'h + xA[k.val]'h else d4))
        = polyValue 64 (Vector.map (Expression.eval env)
          (Vector.mapFinRange 5 fun k =>
            if h : k.val < 4 then xT[k.val]'h + cExp (2 * P256) k.val else cExp (2 * P256) 4))) :
    ((BigInt.value 64 (Vector.map (Expression.eval env) d)
        + (Expression.eval env d4).val * 2 ^ 256 : ℕ) : Specs.Secp256k1.Fp)
      = decodeFe (Vector.map (Expression.eval env) xT)
        - decodeFe (Vector.map (Expression.eval env) xA) := by
  have hnat := dblock_identity env d xA xT d4 hd hxA hxT hspec
  have hcast := congrArg (Nat.cast : ℕ → Specs.Secp256k1.Fp) hnat
  push_cast at hcast
  rw [show ((P256 : ℕ) : Specs.Secp256k1.Fp) = 0 from ZMod.natCast_self _] at hcast
  simp only [decodeFe, limbBits, mul_zero, add_zero] at hcast ⊢
  push_cast
  linear_combination hcast


lemma boundAt_linFlexT_pos (k : Fin 5) (hk : k.val < 4) :
    EqViaCarriesFlex.boundAt EqViaCarriesFlexT.linFlexT.M k.val = 2 ^ 67 := by
  fin_cases k <;> revert hk <;> decide

lemma boundAt_linFlexT_top :
    EqViaCarriesFlex.boundAt EqViaCarriesFlexT.linFlexT.M 4 = 2 ^ 4 := by decide

lemma dblock_discharge (env : Environment (F circomPrime))
    (d xA xT : Var Emu (F circomPrime)) (d4 : Expression (F circomPrime))
    (hd : BigInt.Normalized 64 (Vector.map (Expression.eval env) d))
    (hxA : BigInt.Normalized 64 (Vector.map (Expression.eval env) xA))
    (hxT : BigInt.Normalized 64 (Vector.map (Expression.eval env) xT))
    (hd4 : (Expression.eval env d4).val < 4) :
    (∀ k : Fin 5,
        ((Vector.map (Expression.eval env)
          (Vector.mapFinRange 5 fun k =>
            if h : k.val < 4 then d[k.val]'h + xA[k.val]'h else d4))[k.val]).val
        < EqViaCarriesFlex.boundAt EqViaCarriesFlexT.linFlexT.M k.val)
    ∧ (∀ k : Fin 5,
        ((Vector.map (Expression.eval env)
          (Vector.mapFinRange 5 fun k =>
            if h : k.val < 4 then xT[k.val]'h + cExp (2 * P256) k.val else cExp (2 * P256) 4))[k.val]).val
        < EqViaCarriesFlex.boundAt EqViaCarriesFlexT.linFlexT.M k.val) := by
  have dd := digit_lt_of_norm' env d hd
  have dA := digit_lt_of_norm' env xA hxA
  have dT := digit_lt_of_norm' env xT hxT
  constructor
  · intro k
    rw [Vector.getElem_map, Vector.getElem_mapFinRange]
    by_cases hk : k.val < 4
    · rw [dif_pos hk, boundAt_linFlexT_pos k hk,
        val_add2 env _ _ (dd k.val hk) (dA k.val hk)]
      have := dd k.val hk; have := dA k.val hk
      have hf : (2:ℕ) ^ 64 + 2 ^ 64 < 2 ^ 67 := by norm_num
      omega
    · have hk4 : k.val = 4 := by omega
      rw [dif_neg hk, hk4, boundAt_linFlexT_top]
      omega
  · intro k
    rw [Vector.getElem_map, Vector.getElem_mapFinRange]
    by_cases hk : k.val < 4
    · rw [dif_pos hk, boundAt_linFlexT_pos k hk,
        val_add_cExp env _ (2 * P256) k.val (dT k.val hk)]
      have h1 := dT k.val hk
      have h2 := limbOfNat_lt (2 * P256) k.val
      simp only [limbBits] at h2
      have hf : (2:ℕ) ^ 64 + 2 ^ 64 < 2 ^ 67 := by norm_num
      omega
    · have hk4 : k.val = 4 := by omega
      rw [dif_neg hk, hk4, boundAt_linFlexT_top, eval_cExp, val_limbOfNat]
      decide

lemma c2a_fp (env : Environment (F circomPrime))
    (lam2 x2 x1 xT2 q6 : Var Emu (F circomPrime)) (q6t : Expression (F circomPrime))
    (P : Vector (Expression (F circomPrime)) 7)
    (hP : ∀ k : Fin 7,
      Expression.eval env P[k.val] = Expression.eval env (bigIntMulNoReduce lam2 lam2)[k.val])
    (hlam : BigInt.Normalized 64 (Vector.map (Expression.eval env) lam2))
    (hx2 : BigInt.Normalized 64 (Vector.map (Expression.eval env) x2))
    (hx1 : BigInt.Normalized 64 (Vector.map (Expression.eval env) x1))
    (hxT2 : BigInt.Normalized 64 (Vector.map (Expression.eval env) xT2))
    (hq6 : BigInt.Normalized 64 (Vector.map (Expression.eval env) q6))
    (hq6t : (Expression.eval env q6t).val < 2 ^ 64)
    (hspec : polyValue 64 (Vector.map (Expression.eval env)
          (Vector.mapFinRange 9 fun k =>
            (if h : k.val < 7 then P[k.val]'h else 0)
              + (if k.val < 5 then cExp (4 * P256) k.val else 0)))
        = polyValue 64 (Vector.map (Expression.eval env)
          (Vector.mapFinRange 9 fun k =>
            qpCoeff q6 q6t k.val
              + (if h : k.val < 4 then x2[k.val]'h + x1[k.val]'h + xT2[k.val]'h else 0)))) :
    decodeFe (Vector.map (Expression.eval env) x2)
      = decodeFe (Vector.map (Expression.eval env) lam2) ^ 2
        - decodeFe (Vector.map (Expression.eval env) x1)
        - decodeFe (Vector.map (Expression.eval env) xT2) :=
  (o2_identity env lam2 x2 x1 xT2 q6 q6t P hP hlam hx2 hx1 hxT2 hq6 hq6t hspec).2

lemma polyValue64_conv (env : Environment (F circomPrime)) (a b : Var Emu (F circomPrime))
    (ha : ∀ i : Fin 4, (Expression.eval env a[i.val]).val < 2 ^ 65)
    (hb : ∀ i : Fin 4, (Expression.eval env b[i.val]).val < 2 ^ 65) :
    polyValue 64 (Vector.map (Expression.eval env) (bigIntMulNoReduce a b))
      = (∑ i : Fin 4, (Expression.eval env a[i.val]).val * 2 ^ (64 * i.val))
        * (∑ j : Fin 4, (Expression.eval env b[j.val]).val * 2 ^ (64 * j.val)) := by
  have hbound : (4:ℕ) * (2 ^ 65 * 2 ^ 65) < circomPrime := by decide
  set av : ℕ → ℕ := fun i => if h : i < 4 then (Expression.eval env a[i]).val else 0 with hav
  set bv : ℕ → ℕ := fun j => if h : j < 4 then (Expression.eval env b[j]).val else 0 with hbv
  have hAsum : (∑ i : Fin 4, (Expression.eval env a[i.val]).val * 2 ^ (64 * i.val))
      = ∑ i ∈ Finset.range 4, av i * 2 ^ (64 * i) := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => av i * 2 ^ (64 * i))]
    apply Finset.sum_congr rfl; intro i _; simp only [hav, dif_pos i.isLt]
  have hBsum : (∑ j : Fin 4, (Expression.eval env b[j.val]).val * 2 ^ (64 * j.val))
      = ∑ j ∈ Finset.range 4, bv j * 2 ^ (64 * j) := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => bv j * 2 ^ (64 * j))]
    apply Finset.sum_congr rfl; intro j _; simp only [hbv, dif_pos j.isLt]
  rw [hAsum, hBsum, cauchy_base_pow 64 4 av bv, polyValue,
    ← Fin.sum_univ_eq_sum_range
      (fun k => (∑ i ∈ Finset.range 4, if i ≤ k ∧ k - i < 4 then av i * bv (k - i) else 0)
        * 2 ^ (64 * k))]
  apply Finset.sum_congr rfl
  intro k _
  rw [Vector.getElem_map, val_bigIntMulNoReduce_coeff env a b k ha hb hbound]
  congr 1
  rw [← Fin.sum_univ_eq_sum_range
    (fun i => if i ≤ k.val ∧ k.val - i < 4 then av i * bv (k.val - i) else 0)]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : i.val ≤ k.val ∧ k.val - i.val < 4
  · rw [dif_pos h, if_pos h]; simp only [hav, hbv, dif_pos i.isLt, dif_pos h.2]
  · rw [dif_neg h, if_neg h]

lemma eval_sub (env : Environment (F circomPrime)) (a b : Expression (F circomPrime)) :
    Expression.eval env (a - b) = Expression.eval env a - Expression.eval env b := by
  show Expression.eval env (Expression.add a (Expression.mul (Expression.const (-1)) b))
      = Expression.eval env a - Expression.eval env b
  rw [eval_add, eval_mul]
  show Expression.eval env a + (-1) * Expression.eval env b = _
  ring

lemma val_sub_add_const (a b : F circomPrime) (c : ℕ)
    (hle : b.val ≤ a.val + c) (hlt : a.val + c - b.val < circomPrime) :
    (a + ((c : ℕ) : F circomPrime) - b).val = a.val + c - b.val := by
  have hcast : ((a.val + c - b.val : ℕ) : F circomPrime) = a + ((c : ℕ) : F circomPrime) - b := by
    rw [Nat.cast_sub hle]
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  rw [← hcast, ZMod.val_natCast_of_lt hlt]

lemma val_sub_add_const' (a b : F circomPrime) (c : ℕ)
    (hle : b.val ≤ a.val + c) (hlt : a.val + c - b.val < circomPrime) :
    (a - b + ((c : ℕ) : F circomPrime)).val = a.val + c - b.val := by
  rw [show a - b + ((c : ℕ) : F circomPrime) = a + ((c : ℕ) : F circomPrime) - b from by ring]
  exact val_sub_add_const a b c hle hlt

lemma polyValue10_split (env : Environment (F circomPrime))
    (A B : Fin 10 → Expression (F circomPrime))
    (hb : ∀ k : Fin 10,
      (Expression.eval env (A k)).val + (Expression.eval env (B k)).val < circomPrime) :
    polyValue 64 (Vector.map (Expression.eval env) (Vector.mapFinRange 10 fun k => A k + B k))
      = (∑ k ∈ Finset.range 10,
          (if h : k < 10 then (Expression.eval env (A ⟨k, h⟩)).val else 0) * 2 ^ (64 * k))
        + (∑ k ∈ Finset.range 10,
          (if h : k < 10 then (Expression.eval env (B ⟨k, h⟩)).val else 0) * 2 ^ (64 * k)) := by
  rw [polyValue,
    ← Fin.sum_univ_eq_sum_range
      (fun k => (if h : k < 10 then (Expression.eval env (A ⟨k, h⟩)).val else 0) * 2 ^ (64 * k)),
    ← Fin.sum_univ_eq_sum_range
      (fun k => (if h : k < 10 then (Expression.eval env (B ⟨k, h⟩)).val else 0) * 2 ^ (64 * k)),
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [Vector.getElem_map, Vector.getElem_mapFinRange, dif_pos k.isLt, dif_pos k.isLt]
  have hk : (⟨k.val, k.isLt⟩ : Fin 10) = k := rfl
  rw [hk,
    show Expression.eval env (A k + B k) = Expression.eval env (A k) + Expression.eval env (B k) from rfl,
    ZMod.val_add_of_lt (hb k)]
  ring

lemma polyValue_pad10_7 (env : Environment (F circomPrime))
    (P : Vector (Expression (F circomPrime)) 7) :
    (∑ k ∈ Finset.range 10,
        (if h : k < 10 then
          (Expression.eval env (if h' : k < 7 then P[k]'h' else 0)).val else 0) * 2 ^ (64 * k))
      = polyValue 64 (Vector.map (Expression.eval env) P) := by
  rw [polyValue]
  have hfin : (∑ k : Fin 7, ((Vector.map (Expression.eval env) P)[k.val]).val * 2 ^ (64 * k.val))
      = ∑ k ∈ Finset.range 7,
          (if h' : k < 7 then (Expression.eval env (P[k]'h')).val else 0) * 2 ^ (64 * k) := by
    rw [← Fin.sum_univ_eq_sum_range
      (fun k => (if h' : k < 7 then (Expression.eval env (P[k]'h')).val else 0) * 2 ^ (64 * k))]
    apply Finset.sum_congr rfl
    intro k _
    rw [dif_pos k.isLt, Vector.getElem_map]
  rw [hfin, ← Finset.sum_subset (Finset.range_subset_range.mpr (by omega : 7 ≤ 10))
    (f := fun k => (if h : k < 10 then
        (Expression.eval env (if h' : k < 7 then P[k]'h' else 0)).val else 0) * 2 ^ (64 * k))]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    rw [dif_pos (by omega : k < 10), dif_pos hk, dif_pos hk]
  · intro k hk10 hk7
    rw [Finset.mem_range] at hk10
    rw [Finset.mem_range] at hk7
    rw [dif_pos (by omega : k < 10), dif_neg (by omega : ¬ k < 7),
      show Expression.eval env (0 : Expression (F circomPrime)) = 0 from rfl, ZMod.val_zero,
      Nat.zero_mul]

lemma polyValue_pad10_cExp (env : Environment (F circomPrime)) (v : ℕ) (hv : v < 2 ^ 320) :
    (∑ k ∈ Finset.range 10,
        (if h : k < 10 then (Expression.eval env (if k < 5 then cExp v k else 0)).val else 0)
          * 2 ^ (64 * k))
      = v := by
  have hstep : (∑ k ∈ Finset.range 10,
        (if h : k < 10 then (Expression.eval env (if k < 5 then cExp v k else 0)).val else 0)
          * 2 ^ (64 * k))
      = ∑ k ∈ Finset.range 5, (v / 2 ^ (64 * k) % 2 ^ 64) * 2 ^ (64 * k) := by
    rw [← Finset.sum_subset (Finset.range_subset_range.mpr (by omega : 5 ≤ 10))
      (f := fun k => (if h : k < 10 then
          (Expression.eval env (if k < 5 then cExp v k else 0)).val else 0) * 2 ^ (64 * k))]
    · apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_range] at hk
      rw [dif_pos (by omega : k < 10), if_pos hk, eval_cExp, val_limbOfNat]
      rfl
    · intro k hk10 hk5
      rw [Finset.mem_range] at hk10
      rw [Finset.mem_range] at hk5
      rw [dif_pos (by omega : k < 10), if_neg (by omega : ¬ k < 5),
        show Expression.eval env (0 : Expression (F circomPrime)) = 0 from rfl, ZMod.val_zero,
        Nat.zero_mul]
  rw [hstep, limb_decomp_mod 64 5 v, Nat.mod_eq_of_lt (by
    have : (2:ℕ) ^ (64 * 5) = 2 ^ 320 := by norm_num
    omega)]

lemma val_mul_const (env : Environment (F circomPrime)) (c : ℕ) (e : Expression (F circomPrime))
    (he : (Expression.eval env e).val < 2 ^ 64) (hc : c < 2 ^ 33) :
    (Expression.eval env (((c : ℕ) : F circomPrime) * e)).val = c * (Expression.eval env e).val := by
  have hcp : c < circomPrime := by
    have h33 : (2:ℕ) ^ 33 < circomPrime := by decide
    omega
  have hprod : c * (Expression.eval env e).val < circomPrime := by
    have : (2:ℕ) ^ 33 * 2 ^ 64 < circomPrime := by decide
    calc c * (Expression.eval env e).val < 2 ^ 33 * 2 ^ 64 := Nat.mul_lt_mul'' hc he
      _ < circomPrime := this
  rw [show Expression.eval env (((c : ℕ) : F circomPrime) * e)
        = ((c : ℕ) : F circomPrime) * Expression.eval env e from rfl,
    ZMod.val_mul, ZMod.val_natCast_of_lt hcp, Nat.mod_eq_of_lt hprod]

lemma val_affine3 (env : Environment (F circomPrime)) (a b e : Expression (F circomPrime)) (c : ℕ)
    (ha : (Expression.eval env a).val < 2 ^ 64) (hb : (Expression.eval env b).val < 2 ^ 64)
    (he : (Expression.eval env e).val < 2 ^ 64) (hc : c < 2 ^ 33) :
    (Expression.eval env (a + b + ((c : ℕ) : F circomPrime) * e)).val
      = (Expression.eval env a).val + (Expression.eval env b).val + c * (Expression.eval env e).val := by
  have hab : (Expression.eval env (a + b)).val
      = (Expression.eval env a).val + (Expression.eval env b).val := val_add2 env a b ha hb
  have hmul := val_mul_const env c e he hc
  have hlt : (Expression.eval env (a + b)).val
      + (Expression.eval env (((c : ℕ) : F circomPrime) * e)).val < circomPrime := by
    rw [hab, hmul]
    have h1 : c * (Expression.eval env e).val < 2 ^ 33 * 2 ^ 64 := Nat.mul_lt_mul'' hc he
    have h2 : (2:ℕ) ^ 64 + 2 ^ 64 + 2 ^ 33 * 2 ^ 64 < circomPrime := by decide
    omega
  rw [show Expression.eval env (a + b + ((c : ℕ) : F circomPrime) * e)
        = Expression.eval env (a + b) + Expression.eval env (((c : ℕ) : F circomPrime) * e) from rfl,
    ZMod.val_add_of_lt hlt, hab, hmul]

set_option maxRecDepth 4000 in

lemma xd_value (env : Environment (F circomPrime)) (xT x : Var Emu (F circomPrime))
    (hxT : BigInt.Normalized 64 (Vector.map (Expression.eval env) xT))
    (hx : BigInt.Normalized 64 (Vector.map (Expression.eval env) x)) :
    (∑ j : Fin 4, (Expression.eval env
        (xT[j.val]'j.isLt + ((2 ^ 64 - 1 : ℕ) : F circomPrime) - x[j.val]'j.isLt)).val
          * 2 ^ (64 * j.val))
      + BigInt.value 64 (Vector.map (Expression.eval env) x)
    = BigInt.value 64 (Vector.map (Expression.eval env) xT) + (2 ^ 256 - 1) := by
  have hval : ∀ j : Fin 4, (Expression.eval env
      (xT[j.val]'j.isLt + ((2 ^ 64 - 1 : ℕ) : F circomPrime) - x[j.val]'j.isLt)).val
      = (Expression.eval env (xT[j.val]'j.isLt)).val + (2 ^ 64 - 1)
        - (Expression.eval env (x[j.val]'j.isLt)).val := by
    intro j
    have hxj := digit_lt_of_norm' env x hx j.val j.isLt
    have hxTj := digit_lt_of_norm' env xT hxT j.val j.isLt
    have hle : (Expression.eval env (x[j.val]'j.isLt)).val
        ≤ (Expression.eval env (xT[j.val]'j.isLt)).val + (2 ^ 64 - 1) :=
      le_trans (Nat.le_pred_of_lt hxj) (Nat.le_add_left _ _)
    have hlt : (Expression.eval env (xT[j.val]'j.isLt)).val + (2 ^ 64 - 1)
        - (Expression.eval env (x[j.val]'j.isLt)).val < circomPrime :=
      lt_of_le_of_lt (Nat.sub_le _ _)
        (lt_of_lt_of_le (Nat.add_lt_add_right hxTj (2 ^ 64 - 1))
          (by decide : (2 : ℕ) ^ 64 + (2 ^ 64 - 1) ≤ circomPrime))
    rw [eval_sub, show Expression.eval env (xT[j.val]'j.isLt + ((2 ^ 64 - 1 : ℕ) : F circomPrime))
          = Expression.eval env (xT[j.val]'j.isLt) + ((2 ^ 64 - 1 : ℕ) : F circomPrime)
          from eval_add env _ _]
    exact val_sub_add_const _ _ _ hle hlt
  rw [MulMod.value_map_eval, MulMod.value_map_eval, ← Finset.sum_add_distrib]
  have hterm : ∀ j : Fin 4,
      (Expression.eval env (xT[j.val]'j.isLt + ((2 ^ 64 - 1 : ℕ) : F circomPrime) - x[j.val]'j.isLt)).val
          * 2 ^ (64 * j.val)
        + (Expression.eval env x[j.val]).val * 2 ^ (64 * j.val)
      = ((Expression.eval env xT[j.val]).val + (2 ^ 64 - 1)) * 2 ^ (64 * j.val) := by
    intro j
    rw [hval j, ← Nat.add_mul]
    congr 1
    have := digit_lt_of_norm' env x hx j.val j.isLt
    omega
  rw [Finset.sum_congr rfl (fun j _ => hterm j)]
  have hsplit : (∑ j : Fin 4, ((Expression.eval env xT[j.val]).val + (2 ^ 64 - 1)) * 2 ^ (64 * j.val))
      = (∑ j : Fin 4, (Expression.eval env xT[j.val]).val * 2 ^ (64 * j.val))
        + ∑ j : Fin 4, (2 ^ 64 - 1) * 2 ^ (64 * j.val) := by
    rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro j _; ring
  have hpow : (∑ j : Fin 4, (2 ^ 64 - 1) * 2 ^ (64 * j.val)) = 2 ^ 256 - 1 := by
    rw [Fin.sum_univ_eq_sum_range (fun j => (2 ^ 64 - 1) * 2 ^ (64 * j)),
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
  rw [hsplit, hpow, ← MulMod.value_map_eval]

lemma eval_xd (env : Environment (F circomPrime)) (xT x : Var Emu (F circomPrime))
    (hxT : BigInt.Normalized 64 (Vector.map (Expression.eval env) xT))
    (hx : BigInt.Normalized 64 (Vector.map (Expression.eval env) x))
    (i : ℕ) (hi : i < 4) :
    (Expression.eval env (xT[i]'hi + ((2 ^ 64 - 1 : ℕ) : F circomPrime) - x[i]'hi)).val
      = (Expression.eval env (xT[i]'hi)).val + (2 ^ 64 - 1) - (Expression.eval env (x[i]'hi)).val := by
  have hxj := digit_lt_of_norm' env x hx i hi
  have hxTj := digit_lt_of_norm' env xT hxT i hi
  have hle : (Expression.eval env (x[i]'hi)).val
      ≤ (Expression.eval env (xT[i]'hi)).val + (2 ^ 64 - 1) :=
    le_trans (Nat.le_pred_of_lt hxj) (Nat.le_add_left _ _)
  have hlt : (Expression.eval env (xT[i]'hi)).val + (2 ^ 64 - 1)
      - (Expression.eval env (x[i]'hi)).val < circomPrime :=
    lt_of_le_of_lt (Nat.sub_le _ _)
      (lt_of_lt_of_le (Nat.add_lt_add_right hxTj (2 ^ 64 - 1))
        (by decide : (2 : ℕ) ^ 64 + (2 ^ 64 - 1) ≤ circomPrime))
  rw [eval_sub, show Expression.eval env (xT[i]'hi + ((2 ^ 64 - 1 : ℕ) : F circomPrime))
        = Expression.eval env (xT[i]'hi) + ((2 ^ 64 - 1 : ℕ) : F circomPrime) from eval_add env _ _]
  exact val_sub_add_const _ _ _ hle hlt

lemma eval_xd_lt (env : Environment (F circomPrime)) (xT x : Var Emu (F circomPrime))
    (hxT : BigInt.Normalized 64 (Vector.map (Expression.eval env) xT))
    (hx : BigInt.Normalized 64 (Vector.map (Expression.eval env) x))
    (i : ℕ) (hi : i < 4) :
    (Expression.eval env (xT[i]'hi + ((2 ^ 64 - 1 : ℕ) : F circomPrime) - x[i]'hi)).val < 2 ^ 65 := by
  rw [eval_xd env xT x hxT hx i hi]
  have hxTj := digit_lt_of_norm' env xT hxT i hi
  have h : (2 : ℕ) ^ 64 + (2 ^ 64 - 1) < 2 ^ 65 := by decide
  omega

/-! ### Borrow-pilot: `dtil = xT + twoPBorrowDigit − xA`, fat-limb, no re-limbing

`dtil` is the wire-only analogue of `xd` above, using the non-uniform digit
vector `twoPBorrowDigit` (sum `= 2·P256`) instead of the uniform `2^64 − 1`
(sum `= 2^256 − 1`). Each limb is bounded by `3·2^64` instead of `2^65`
(§BORROW-PILOT, `BorrowFree.lean`). -/

lemma eval_dtil (env : Environment (F circomPrime)) (xT xA : Var Emu (F circomPrime))
    (hxT : BigInt.Normalized 64 (Vector.map (Expression.eval env) xT))
    (hxA : BigInt.Normalized 64 (Vector.map (Expression.eval env) xA))
    (i : ℕ) (hi : i < 4) :
    (Expression.eval env
        (xT[i]'hi + ((twoPBorrowDigit i : ℕ) : F circomPrime) - xA[i]'hi)).val
      = (Expression.eval env (xT[i]'hi)).val + twoPBorrowDigit i
          - (Expression.eval env (xA[i]'hi)).val := by
  have hxAi := digit_lt_of_norm' env xA hxA i hi
  have hxTi := digit_lt_of_norm' env xT hxT i hi
  have hDge : (2:ℕ) ^ 64 ≤ twoPBorrowDigit i := twoPBorrowDigit_ge i
  have hDlt := twoPBorrowDigit_lt i
  have hle : (Expression.eval env (xA[i]'hi)).val
      ≤ (Expression.eval env (xT[i]'hi)).val + twoPBorrowDigit i := by omega
  have hlt : (Expression.eval env (xT[i]'hi)).val + twoPBorrowDigit i
      - (Expression.eval env (xA[i]'hi)).val < circomPrime := by
    have hb : (2:ℕ) ^ 64 + 2 ^ 65 < circomPrime := by decide
    omega
  rw [eval_sub, show Expression.eval env (xT[i]'hi + ((twoPBorrowDigit i : ℕ) : F circomPrime))
        = Expression.eval env (xT[i]'hi) + ((twoPBorrowDigit i : ℕ) : F circomPrime)
        from eval_add env _ _]
  exact val_sub_add_const _ _ _ hle hlt

lemma eval_dtil_lt (env : Environment (F circomPrime)) (xT xA : Var Emu (F circomPrime))
    (hxT : BigInt.Normalized 64 (Vector.map (Expression.eval env) xT))
    (hxA : BigInt.Normalized 64 (Vector.map (Expression.eval env) xA))
    (i : ℕ) (hi : i < 4) :
    (Expression.eval env
        (xT[i]'hi + ((twoPBorrowDigit i : ℕ) : F circomPrime) - xA[i]'hi)).val
      < 3 * 2 ^ 64 := by
  rw [eval_dtil env xT xA hxT hxA i hi]
  have hxTi := digit_lt_of_norm' env xT hxT i hi
  have hD := twoPBorrowDigit_lt i
  omega

set_option maxRecDepth 4000 in

/-- The weighted sum of `dtil`'s (fat) limbs equals `xT + 2·P256 − xA`
exactly, as a natural number — the fat-limb analogue of `xd_value`. -/
lemma dtil_value (env : Environment (F circomPrime)) (xT xA : Var Emu (F circomPrime))
    (hxT : BigInt.Normalized 64 (Vector.map (Expression.eval env) xT))
    (hxA : BigInt.Normalized 64 (Vector.map (Expression.eval env) xA)) :
    (∑ j : Fin 4, (Expression.eval env
        (xT[j.val]'j.isLt + ((twoPBorrowDigit j.val : ℕ) : F circomPrime) - xA[j.val]'j.isLt)).val
          * 2 ^ (64 * j.val))
      + BigInt.value 64 (Vector.map (Expression.eval env) xA)
    = BigInt.value 64 (Vector.map (Expression.eval env) xT) + 2 * P256 := by
  rw [MulMod.value_map_eval, MulMod.value_map_eval, ← Finset.sum_add_distrib]
  have hterm : ∀ j : Fin 4,
      (Expression.eval env
          (xT[j.val]'j.isLt + ((twoPBorrowDigit j.val : ℕ) : F circomPrime) - xA[j.val]'j.isLt)).val
          * 2 ^ (64 * j.val)
        + (Expression.eval env xA[j.val]).val * 2 ^ (64 * j.val)
      = ((Expression.eval env xT[j.val]).val + twoPBorrowDigit j.val) * 2 ^ (64 * j.val) := by
    intro j
    rw [eval_dtil env xT xA hxT hxA j.val j.isLt, ← Nat.add_mul]
    congr 1
    have := digit_lt_of_norm' env xA hxA j.val j.isLt
    have hDge : (2:ℕ) ^ 64 ≤ twoPBorrowDigit j.val := twoPBorrowDigit_ge j.val
    omega
  rw [Finset.sum_congr rfl (fun j _ => hterm j)]
  have hsplit : (∑ j : Fin 4,
      ((Expression.eval env xT[j.val]).val + twoPBorrowDigit j.val) * 2 ^ (64 * j.val))
      = (∑ j : Fin 4, (Expression.eval env xT[j.val]).val * 2 ^ (64 * j.val))
        + ∑ j : Fin 4, twoPBorrowDigit j.val * 2 ^ (64 * j.val) := by
    rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro j _; ring
  have hpow : (∑ j : Fin 4, twoPBorrowDigit j.val * 2 ^ (64 * j.val)) = 2 * P256 := by
    rw [Fin.sum_univ_eq_sum_range (fun j => twoPBorrowDigit j * 2 ^ (64 * j))]
    exact twoPBorrowDigit_sum
  rw [hsplit, hpow, ← MulMod.value_map_eval]

/-- Fat-limb analogue of `polyValue64_conv`: the convolution of a canonical
`lam` (`< 2^64` per limb) with a fat `dtil` (`< 3·2^64` per limb) still
evaluates, via `interpolatedMul`'s exact polynomial identity, to the plain
product of the two weighted sums — no truncation, regardless of the wider
per-limb bound. -/
lemma polyValue64_conv_fat (env : Environment (F circomPrime)) (lam dtil : Var Emu (F circomPrime))
    (ha : ∀ i : Fin 4, (Expression.eval env lam[i.val]).val < 2 ^ 64)
    (hb : ∀ i : Fin 4, (Expression.eval env dtil[i.val]).val < 3 * 2 ^ 64) :
    polyValue 64 (Vector.map (Expression.eval env) (bigIntMulNoReduce lam dtil))
      = (∑ i : Fin 4, (Expression.eval env lam[i.val]).val * 2 ^ (64 * i.val))
        * (∑ j : Fin 4, (Expression.eval env dtil[j.val]).val * 2 ^ (64 * j.val)) := by
  have ha66 : ∀ i : Fin 4, (Expression.eval env lam[i.val]).val < 2 ^ 66 :=
    fun i => lt_trans (ha i) (by norm_num)
  have hb66 : ∀ i : Fin 4, (Expression.eval env dtil[i.val]).val < 2 ^ 66 :=
    fun i => lt_trans (hb i) (by norm_num)
  have hbound : (4:ℕ) * (2 ^ 66 * 2 ^ 66) < circomPrime := by decide
  set av : ℕ → ℕ := fun i => if h : i < 4 then (Expression.eval env lam[i]).val else 0 with hav
  set bv : ℕ → ℕ := fun j => if h : j < 4 then (Expression.eval env dtil[j]).val else 0 with hbv
  have hAsum : (∑ i : Fin 4, (Expression.eval env lam[i.val]).val * 2 ^ (64 * i.val))
      = ∑ i ∈ Finset.range 4, av i * 2 ^ (64 * i) := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => av i * 2 ^ (64 * i))]
    apply Finset.sum_congr rfl; intro i _; simp only [hav, dif_pos i.isLt]
  have hBsum : (∑ j : Fin 4, (Expression.eval env dtil[j.val]).val * 2 ^ (64 * j.val))
      = ∑ j ∈ Finset.range 4, bv j * 2 ^ (64 * j) := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => bv j * 2 ^ (64 * j))]
    apply Finset.sum_congr rfl; intro j _; simp only [hbv, dif_pos j.isLt]
  rw [hAsum, hBsum, cauchy_base_pow 64 4 av bv, polyValue,
    ← Fin.sum_univ_eq_sum_range
      (fun k => (∑ i ∈ Finset.range 4, if i ≤ k ∧ k - i < 4 then av i * bv (k - i) else 0)
        * 2 ^ (64 * k))]
  apply Finset.sum_congr rfl
  intro k _
  rw [Vector.getElem_map, val_bigIntMulNoReduce_coeff env lam dtil k ha66 hb66 hbound]
  congr 1
  rw [← Fin.sum_univ_eq_sum_range
    (fun i => if i ≤ k.val ∧ k.val - i < 4 then av i * bv (k.val - i) else 0)]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : i.val ≤ k.val ∧ k.val - i.val < 4
  · rw [dif_pos h, if_pos h]; simp only [hav, hbv, dif_pos i.isLt, dif_pos h.2]
  · rw [dif_neg h, if_neg h]

/-- Each convolution coefficient of `lam * dtil` is `< 4·(2^64·(3·2^64)) = 12·2^128`
(the fattened quad-tent coefficient bound, §BORROW-PILOT). -/
lemma val_conv_lam_dtil_lt (env : Environment (F circomPrime)) (lam dtil : Var Emu (F circomPrime))
    (k : Fin 7)
    (hlam : ∀ i : Fin 4, (Expression.eval env lam[i.val]).val < 2 ^ 64)
    (hdtil : ∀ i : Fin 4, (Expression.eval env dtil[i.val]).val < 3 * 2 ^ 64) :
    (Expression.eval env ((bigIntMulNoReduce lam dtil)[k.val])).val
      < 4 * (2 ^ 64 * (3 * 2 ^ 64)) := by
  have ha66 : ∀ i : Fin 4, (Expression.eval env lam[i.val]).val < 2 ^ 66 :=
    fun i => lt_trans (hlam i) (by norm_num)
  have hb66 : ∀ i : Fin 4, (Expression.eval env dtil[i.val]).val < 2 ^ 66 :=
    fun i => lt_trans (hdtil i) (by norm_num)
  have hbound : (4:ℕ) * (2 ^ 66 * 2 ^ 66) < circomPrime := by decide
  rw [val_bigIntMulNoReduce_coeff env lam dtil k ha66 hb66 hbound]
  have hterm : ∀ i : Fin 4, (if h : i.val ≤ k.val ∧ k.val - i.val < 4 then
      (Expression.eval env lam[i.val]).val
        * (Expression.eval env (dtil[k.val - i.val]'h.2)).val else 0)
      ≤ 2 ^ 64 * (3 * 2 ^ 64) - 1 := by
    intro i
    by_cases h : i.val ≤ k.val ∧ k.val - i.val < 4
    · rw [dif_pos h]
      have h1 := hlam i
      have h2 := hdtil ⟨k.val - i.val, h.2⟩
      have hmul : (Expression.eval env lam[i.val]).val
          * (Expression.eval env (dtil[k.val - i.val]'h.2)).val
          < 2 ^ 64 * (3 * 2 ^ 64) := Nat.mul_lt_mul'' h1 h2
      omega
    · rw [dif_neg h]; positivity
  calc ∑ i : Fin 4, _ ≤ ∑ _i : Fin 4, (2 ^ 64 * (3 * 2 ^ 64) - 1) :=
        Finset.sum_le_sum (fun i _ => hterm i)
    _ = 4 * (2 ^ 64 * (3 * 2 ^ 64) - 1) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    _ < 4 * (2 ^ 64 * (3 * 2 ^ 64)) := by omega

/-- Fp-level: the weighted sum of `dtil = xT + twoPBorrowDigit - xA`'s fat
limbs equals `decodeFe xT - decodeFe xA` (mod p) — the wire-only, `d`/`d4`-
free analogue of `dblock_fp`. -/
lemma dtil_fp (env : Environment (F circomPrime)) (xT xA : Var Emu (F circomPrime))
    (hxT : BigInt.Normalized 64 (Vector.map (Expression.eval env) xT))
    (hxA : BigInt.Normalized 64 (Vector.map (Expression.eval env) xA)) :
    ((∑ j : Fin 4, (Expression.eval env
        (xT[j.val]'j.isLt + ((twoPBorrowDigit j.val : ℕ) : F circomPrime) - xA[j.val]'j.isLt)).val
          * 2 ^ (64 * j.val) : ℕ) : Specs.Secp256k1.Fp)
      = decodeFe (Vector.map (Expression.eval env) xT)
        - decodeFe (Vector.map (Expression.eval env) xA) := by
  have hnat := dtil_value env xT xA hxT hxA
  have hcast := congrArg (Nat.cast : ℕ → Specs.Secp256k1.Fp) hnat
  push_cast at hcast
  rw [show ((P256 : ℕ) : Specs.Secp256k1.Fp) = 0 from ZMod.natCast_self _] at hcast
  simp only [decodeFe, limbBits, mul_zero, add_zero] at hcast ⊢
  push_cast
  linear_combination hcast

set_option maxRecDepth 4000 in
/-- Fat-limb analogue of `polyValue_a2_lhs`: the LHS of the combined stageA
identity (`λ·dtil + cExp(8·P256)`, no `lp` fold term since `dtil` has no
separate top digit) evaluates to the plain product of the weighted sums plus
`8·P256`. -/
lemma polyValue_a2_lhs_fat (env : Environment (F circomPrime))
    (lam dtil : Var Emu (F circomPrime)) (P : Vector (Expression (F circomPrime)) 7)
    (hP : ∀ k : Fin 7,
      Expression.eval env P[k.val] = Expression.eval env (bigIntMulNoReduce lam dtil)[k.val])
    (hlam : BigInt.Normalized 64 (Vector.map (Expression.eval env) lam))
    (hdtil : ∀ i : Fin 4, (Expression.eval env dtil[i.val]).val < 3 * 2 ^ 64) :
    polyValue 64 (Vector.map (Expression.eval env)
        (Vector.mapFinRange 9 fun k =>
          (if h : k.val < 7 then P[k.val]'h else 0)
            + (if k.val < 5 then cExp (8 * P256) k.val else 0)))
      = (∑ i : Fin 4, (Expression.eval env lam[i.val]).val * 2 ^ (64 * i.val))
          * (∑ j : Fin 4, (Expression.eval env dtil[j.val]).val * 2 ^ (64 * j.val))
        + 8 * P256 := by
  have hlamd := digit_lt_of_norm env lam hlam
  rw [polyValue9_split env (fun k => if h : k.val < 7 then P[k.val]'h else 0)
    (fun k => if k.val < 5 then cExp (8 * P256) k.val else 0)
    (by
      intro k
      dsimp only
      have hA : (Expression.eval env (if h : k.val < 7 then P[k.val]'h else 0)).val
          < 4 * (2 ^ 64 * (3 * 2 ^ 64)) := by
        by_cases hk : k.val < 7
        · rw [dif_pos hk, hP ⟨k.val, hk⟩]
          exact val_conv_lam_dtil_lt env lam dtil ⟨k.val, hk⟩ hlamd hdtil
        · rw [dif_neg hk, show Expression.eval env (0 : Expression (F circomPrime)) = 0 from rfl,
            ZMod.val_zero]; positivity
      have hB : (Expression.eval env (if k.val < 5 then cExp (8 * P256) k.val else 0)).val < 2 ^ 64 := by
        by_cases hk : k.val < 5
        · rw [if_pos hk, eval_cExp, val_limbOfNat]; exact limbOfNat_lt _ _
        · rw [if_neg hk, show Expression.eval env (0 : Expression (F circomPrime)) = 0 from rfl,
            ZMod.val_zero]; positivity
      have hpr : 4 * (2 ^ 64 * (3 * 2 ^ 64)) + 2 ^ 64 < circomPrime := by decide
      omega)]
  dsimp only
  rw [polyValue_pad9_7 env P, polyValue_pad9_cExp env (8 * P256) (by
    have h : P256 < 2 ^ 256 := P256_lt
    have e1 : (2:ℕ) ^ 3 * 2 ^ 256 = 2 ^ 259 := by rw [← pow_add]
    have e2 : (2:ℕ) ^ 259 ≤ 2 ^ 320 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
    have e3 : 8 * P256 < 2 ^ 3 * 2 ^ 256 := by
      have : (8:ℕ) = 2 ^ 3 := by norm_num
      rw [this]; exact Nat.mul_lt_mul_of_pos_left h (by positivity)
    omega)]
  have hpv : polyValue 64 (Vector.map (Expression.eval env) P)
      = (∑ i : Fin 4, (Expression.eval env lam[i.val]).val * 2 ^ (64 * i.val))
        * (∑ j : Fin 4, (Expression.eval env dtil[j.val]).val * 2 ^ (64 * j.val)) := by
    rw [← polyValue64_conv_fat env lam dtil hlamd hdtil]
    simp only [polyValue, Vector.getElem_map]
    apply Finset.sum_congr rfl
    intro i _
    rw [hP i]
  rw [hpv]

/-- Tight (`≤`, not just `<`) per-term convolution bound — needed because
the loose `< 12·2^128` bound (`val_conv_lam_dtil_lt`) leaves no room to add
`cExp` on top at the combined-identity positions `k < 5`. -/
lemma val_conv_lam_dtil_le (env : Environment (F circomPrime)) (lam dtil : Var Emu (F circomPrime))
    (k : Fin 7)
    (hlam : ∀ i : Fin 4, (Expression.eval env lam[i.val]).val < 2 ^ 64)
    (hdtil : ∀ i : Fin 4, (Expression.eval env dtil[i.val]).val < 3 * 2 ^ 64) :
    (Expression.eval env ((bigIntMulNoReduce lam dtil)[k.val])).val
      ≤ 4 * ((2 ^ 64 - 1) * (3 * 2 ^ 64 - 1)) := by
  have ha66 : ∀ i : Fin 4, (Expression.eval env lam[i.val]).val < 2 ^ 66 :=
    fun i => lt_trans (hlam i) (by norm_num)
  have hb66 : ∀ i : Fin 4, (Expression.eval env dtil[i.val]).val < 2 ^ 66 :=
    fun i => lt_trans (hdtil i) (by norm_num)
  have hbound : (4:ℕ) * (2 ^ 66 * 2 ^ 66) < circomPrime := by decide
  rw [val_bigIntMulNoReduce_coeff env lam dtil k ha66 hb66 hbound]
  have hterm : ∀ i : Fin 4, (if h : i.val ≤ k.val ∧ k.val - i.val < 4 then
      (Expression.eval env lam[i.val]).val
        * (Expression.eval env (dtil[k.val - i.val]'h.2)).val else 0)
      ≤ (2 ^ 64 - 1) * (3 * 2 ^ 64 - 1) := by
    intro i
    by_cases h : i.val ≤ k.val ∧ k.val - i.val < 4
    · rw [dif_pos h]
      have h1 := hlam i
      have h2 : (Expression.eval env (dtil[k.val - i.val]'h.2)).val < 3 * 2 ^ 64 := hdtil ⟨k.val - i.val, h.2⟩
      exact Nat.mul_le_mul (by omega) (by omega)
    · rw [dif_neg h]; positivity
  calc ∑ i : Fin 4, _ ≤ ∑ _i : Fin 4, ((2 ^ 64 - 1) * (3 * 2 ^ 64 - 1)) :=
        Finset.sum_le_sum (fun i _ => hterm i)
    _ = 4 * ((2 ^ 64 - 1) * (3 * 2 ^ 64 - 1)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-- Fat-limb analogue of `a2_discharge`: bound side-conditions for the
combined `gfQuadFat` identity, directly against `vQuadFat.Nf` (no `boundAt`
table needed since `GroupedFlex.Assumptions` is parametrized by `Nf` raw). -/
lemma a2_discharge_fat (env : Environment (F circomPrime))
    (lam dtil yT yA qs : Var Emu (F circomPrime)) (qst : Expression (F circomPrime))
    (P : Vector (Expression (F circomPrime)) 7)
    (hP : ∀ k : Fin 7,
      Expression.eval env P[k.val] = Expression.eval env (bigIntMulNoReduce lam dtil)[k.val])
    (hlam : BigInt.Normalized 64 (Vector.map (Expression.eval env) lam))
    (hdtil : ∀ i : Fin 4, (Expression.eval env dtil[i.val]).val < 3 * 2 ^ 64)
    (hqs : BigInt.Normalized 64 (Vector.map (Expression.eval env) qs))
    (hqst : (Expression.eval env qst).val < 2 ^ 3)
    (hyT : BigInt.Normalized 64 (Vector.map (Expression.eval env) yT))
    (hyA : BigInt.Normalized 64 (Vector.map (Expression.eval env) yA)) :
    (∀ k : Fin 9,
        ((Vector.map (Expression.eval env)
          (Vector.mapFinRange 9 fun k =>
            (if h : k.val < 7 then P[k.val]'h else 0)
              + (if k.val < 5 then cExp (8 * P256) k.val else 0)))[k.val]).val
        < vQuadFat.Nf k.val)
    ∧ (∀ k : Fin 9,
        ((Vector.map (Expression.eval env)
          (Vector.mapFinRange 9 fun k =>
            qpCoeff qs qst k.val
              + (if h : k.val < 4 then
                  yT[k.val]'h - yA[k.val]'h
                    + (((2 ^ 64 - 1 + limbOfNat cK k.val : ℕ) : F circomPrime)
                        : Expression (F circomPrime)) else 0)))[k.val]).val
        < vQuadFat.Nf k.val) := by
  have hqst64 : (Expression.eval env qst).val < 2 ^ 64 := by omega
  have hqsd := digit_lt_of_norm' env qs hqs
  constructor
  · intro k
    rw [Vector.getElem_map, Vector.getElem_mapFinRange]
    by_cases hk7 : k.val < 7
    · rw [vQuadFat_Nf_lo k hk7]
      have hA : (Expression.eval env (if h : k.val < 7 then P[k.val]'h else 0)).val
          ≤ 4 * ((2 ^ 64 - 1) * (3 * 2 ^ 64 - 1)) := by
        rw [dif_pos hk7, hP ⟨k.val, hk7⟩]
        exact val_conv_lam_dtil_le env lam dtil ⟨k.val, hk7⟩ (digit_lt_of_norm env lam hlam) hdtil
      have hB : (Expression.eval env (if k.val < 5 then cExp (8 * P256) k.val else 0)).val < 2 ^ 64 := by
        by_cases hk : k.val < 5
        · rw [if_pos hk, eval_cExp, val_limbOfNat]; exact limbOfNat_lt _ _
        · rw [if_neg hk, show Expression.eval env (0 : Expression (F circomPrime)) = 0 from rfl,
            ZMod.val_zero]; positivity
      have hle := ZMod.val_add_le
        (Expression.eval env (if h : k.val < 7 then P[k.val]'h else 0))
        (Expression.eval env (if k.val < 5 then cExp (8 * P256) k.val else 0))
      rw [show Expression.eval env
            ((if h : k.val < 7 then P[k.val]'h else 0) + (if k.val < 5 then cExp (8 * P256) k.val else 0))
          = Expression.eval env (if h : k.val < 7 then P[k.val]'h else 0)
            + Expression.eval env (if k.val < 5 then cExp (8 * P256) k.val else 0) from rfl]
      have hconcrete : 4 * ((2 ^ 64 - 1) * (3 * 2 ^ 64 - 1)) + (2 ^ 64 - 1) < 12 * 2 ^ 128 := by decide
      omega
    · rw [vQuadFat_Nf_hi k (by omega),
        show Expression.eval env
            ((if h : k.val < 7 then P[k.val]'h else 0) + (if k.val < 5 then cExp (8 * P256) k.val else 0))
          = Expression.eval env (if h : k.val < 7 then P[k.val]'h else 0)
            + Expression.eval env (if k.val < 5 then cExp (8 * P256) k.val else 0) from rfl,
        dif_neg hk7, if_neg (show ¬ k.val < 5 by omega),
        show Expression.eval env (0 : Expression (F circomPrime)) = 0 from rfl, add_zero,
        ZMod.val_zero]
      positivity
  · intro k
    rw [Vector.getElem_map, Vector.getElem_mapFinRange]
    have hg : (Expression.eval env (if h : k.val < 4 then
        yT[k.val]'h - yA[k.val]'h
          + (((2 ^ 64 - 1 + limbOfNat cK k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
        else 0)).val < 2 ^ 67 := by
      by_cases hk : k.val < 4
      · have hyAj := digit_lt_of_norm' env yA hyA k.val hk
        have hyTj := digit_lt_of_norm' env yT hyT k.val hk
        have hcK := limbOfNat_lt cK k.val
        simp only [limbBits] at hcK
        rw [dif_pos hk,
          show Expression.eval env (yT[k.val]'hk - yA[k.val]'hk
                + (((2 ^ 64 - 1 + limbOfNat cK k.val : ℕ) : F circomPrime) : Expression (F circomPrime)))
            = Expression.eval env (yT[k.val]'hk - yA[k.val]'hk)
              + ((2 ^ 64 - 1 + limbOfNat cK k.val : ℕ) : F circomPrime) from eval_add env _ _,
          eval_sub,
          val_sub_add_const' _ _ _ (by omega) (by
            have h : (2:ℕ) ^ 64 + (2 ^ 64 - 1 + 2 ^ 64) < circomPrime := by decide
            omega)]
        omega
      · rw [dif_neg hk, show Expression.eval env (0 : Expression (F circomPrime)) = 0 from rfl,
          ZMod.val_zero]; positivity
    have hle := ZMod.val_add_le (Expression.eval env (qpCoeff qs qst k.val))
      (Expression.eval env (if h : k.val < 4 then
        yT[k.val]'h - yA[k.val]'h
          + (((2 ^ 64 - 1 + limbOfNat cK k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
        else 0))
    rw [show Expression.eval env
          (qpCoeff qs qst k.val + (if h : k.val < 4 then
            yT[k.val]'h - yA[k.val]'h
              + (((2 ^ 64 - 1 + limbOfNat cK k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
            else 0))
        = Expression.eval env (qpCoeff qs qst k.val)
          + Expression.eval env (if h : k.val < 4 then
              yT[k.val]'h - yA[k.val]'h
                + (((2 ^ 64 - 1 + limbOfNat cK k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
              else 0) from rfl]
    by_cases hk7 : k.val < 7
    · rw [vQuadFat_Nf_lo k hk7]
      have hqp := val_qpCoeff_lt env qs qst k.val hqsd hqst64
      omega
    · rw [vQuadFat_Nf_hi k (by omega)]
      have hg0 : (Expression.eval env (if h : k.val < 4 then
          yT[k.val]'h - yA[k.val]'h
            + (((2 ^ 64 - 1 + limbOfNat cK k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
          else 0)).val = 0 := by
        rw [dif_neg (show ¬ k.val < 4 by omega),
          show Expression.eval env (0 : Expression (F circomPrime)) = 0 from rfl, ZMod.val_zero]
      have hqp := val_qpCoeff_tail env qs qst k.val (by omega) hqsd hqst
      omega

lemma sum_guard_affine (env : Environment (F circomPrime)) (y3 yT2 lam2 : Var Emu (F circomPrime))
    (hy3 : BigInt.Normalized 64 (Vector.map (Expression.eval env) y3))
    (hyT2 : BigInt.Normalized 64 (Vector.map (Expression.eval env) yT2))
    (hlam : BigInt.Normalized 64 (Vector.map (Expression.eval env) lam2)) :
    (∑ k ∈ Finset.range 10,
        (if h : k < 10 then
          (Expression.eval env
            (if h' : k < 4 then y3[k]'h' + yT2[k]'h' + ((c976 : ℕ) : F circomPrime) * lam2[k]'h'
             else 0)).val else 0) * 2 ^ (64 * k))
      = BigInt.value 64 (Vector.map (Expression.eval env) y3)
        + BigInt.value 64 (Vector.map (Expression.eval env) yT2)
        + c976 * BigInt.value 64 (Vector.map (Expression.eval env) lam2) := by
  have dy := digit_lt_of_norm' env y3 hy3
  have dyT := digit_lt_of_norm' env yT2 hyT2
  have dl := digit_lt_of_norm' env lam2 hlam
  have hc976 : c976 < 2 ^ 33 := by decide
  rw [value_eq_range_sum 64 (Vector.map (Expression.eval env) y3),
    value_eq_range_sum 64 (Vector.map (Expression.eval env) yT2),
    value_eq_range_sum 64 (Vector.map (Expression.eval env) lam2)]
  simp only [numLimbs, Finset.sum_range_succ, Finset.sum_range_zero, Vector.getElem_map,
    Nat.reduceLT, reduceDIte]
  rw [val_affine3 env _ _ _ _ (dy 0 (by omega)) (dyT 0 (by omega)) (dl 0 (by omega)) hc976,
    val_affine3 env _ _ _ _ (dy 1 (by omega)) (dyT 1 (by omega)) (dl 1 (by omega)) hc976,
    val_affine3 env _ _ _ _ (dy 2 (by omega)) (dyT 2 (by omega)) (dl 2 (by omega)) hc976,
    val_affine3 env _ _ _ _ (dy 3 (by omega)) (dyT 3 (by omega)) (dl 3 (by omega)) hc976]
  simp only [show Expression.eval env (0 : Expression (F circomPrime)) = 0 from rfl,
    ZMod.val_zero, zero_mul, add_zero]
  ring

lemma polyValue_c2b_lhs (env : Environment (F circomPrime))
    (lam2 xT2 x2 : Var Emu (F circomPrime)) (P : Vector (Expression (F circomPrime)) 7)
    (hlam : BigInt.Normalized 64 (Vector.map (Expression.eval env) lam2))
    (hxT2 : BigInt.Normalized 64 (Vector.map (Expression.eval env) xT2))
    (hx2 : BigInt.Normalized 64 (Vector.map (Expression.eval env) x2))
    (hP : ∀ k : Fin 7, Expression.eval env P[k.val]
      = Expression.eval env (bigIntMulNoReduce lam2
          (Vector.ofFn fun i : Fin 4 =>
            xT2[i.val]'i.isLt + ((2 ^ 64 - 1 : ℕ) : F circomPrime) - x2[i.val]'i.isLt))[k.val]) :
    polyValue 64 (Vector.map (Expression.eval env)
        (Vector.mapFinRange 10 fun k =>
          (if h : k.val < 7 then P[k.val]'h else 0)
            + (if k.val < 5 then cExp (2 ^ 35 * P256) k.val else 0)))
      = BigInt.value 64 (Vector.map (Expression.eval env) lam2)
          * (∑ j : Fin 4, (Expression.eval env
              (xT2[j.val]'j.isLt + ((2 ^ 64 - 1 : ℕ) : F circomPrime) - x2[j.val]'j.isLt)).val
                * 2 ^ (64 * j.val))
        + 2 ^ 35 * P256 := by
  have hlamlt : ∀ i : Fin 4, (Expression.eval env lam2[i.val]).val < 2 ^ 65 := by
    intro i; have := digit_lt_of_norm env lam2 hlam i
    have h64 : (2:ℕ) ^ 64 < 2 ^ 65 := by norm_num
    omega
  have hxdlt : ∀ i : Fin 4, (Expression.eval env
      (Vector.ofFn fun j : Fin 4 =>
        xT2[j.val]'j.isLt + ((2 ^ 64 - 1 : ℕ) : F circomPrime) - x2[j.val]'j.isLt)[i.val]).val < 2 ^ 65 := by
    intro i; rw [Vector.getElem_ofFn]; exact eval_xd_lt env xT2 x2 hxT2 hx2 i.val i.isLt
  have hpad : polyValue 64 (Vector.map (Expression.eval env) P)
      = polyValue 64 (Vector.map (Expression.eval env) (bigIntMulNoReduce lam2
          (Vector.ofFn fun j : Fin 4 =>
            xT2[j.val]'j.isLt + ((2 ^ 64 - 1 : ℕ) : F circomPrime) - x2[j.val]'j.isLt))) := by
    simp only [polyValue, Vector.getElem_map]
    apply Finset.sum_congr rfl
    intro i _; rw [hP i]
  rw [polyValue10_split env (fun k => if h : k.val < 7 then P[k.val]'h else 0)
    (fun k => if k.val < 5 then cExp (2 ^ 35 * P256) k.val else 0) (by
      intro k
      dsimp only
      have hA : (Expression.eval env (if h : k.val < 7 then P[k.val]'h else 0)).val < 4 * 2 ^ 130 := by
        by_cases hk : k.val < 7
        · rw [dif_pos hk, hP ⟨k.val, hk⟩]
          have := val_bigIntMulNoReduce_coeff_lt env lam2 _ ⟨k.val, hk⟩ hlamlt hxdlt (by decide)
          simpa using this
        · rw [dif_neg hk, show Expression.eval env (0 : Expression (F circomPrime)) = 0 from rfl,
            ZMod.val_zero]; positivity
      have hB : (Expression.eval env (if k.val < 5 then cExp (2 ^ 35 * P256) k.val else 0)).val < 2 ^ 64 := by
        by_cases hk : k.val < 5
        · rw [if_pos hk, eval_cExp, val_limbOfNat]; exact limbOfNat_lt _ _
        · rw [if_neg hk, show Expression.eval env (0 : Expression (F circomPrime)) = 0 from rfl,
            ZMod.val_zero]; positivity
      have hpr : 4 * 2 ^ 130 + 2 ^ 64 < circomPrime := by decide
      omega)]
  dsimp only
  rw [polyValue_pad10_7 env P, polyValue_pad10_cExp env (2 ^ 35 * P256) (by
      have h : P256 < 2 ^ 256 := P256_lt
      have e1 : (2:ℕ) ^ 35 * 2 ^ 256 = 2 ^ 291 := by rw [← pow_add]
      have e2 : (2:ℕ) ^ 291 ≤ 2 ^ 320 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
      have e3 : 2 ^ 35 * P256 < 2 ^ 35 * 2 ^ 256 := Nat.mul_lt_mul_of_pos_left h (by positivity)
      omega), hpad,
    polyValue64_conv env lam2 _ hlamlt hxdlt, ← MulMod.value_map_eval env lam2]
  refine congrArg (· + 2 ^ 35 * P256) ?_
  refine congrArg (BigInt.value 64 (Vector.map (Expression.eval env) lam2) * ·) ?_
  exact Finset.sum_congr rfl fun j _ => by rw [Vector.getElem_ofFn]

lemma polyValue_c2b_rhs (env : Environment (F circomPrime))
    (q7 : Var Emu (F circomPrime)) (q7t : Expression (F circomPrime))
    (y3 yT2 lam2 : Var Emu (F circomPrime))
    (hq7 : BigInt.Normalized 64 (Vector.map (Expression.eval env) q7))
    (hq7t : (Expression.eval env q7t).val < 2 ^ 64)
    (hy3 : BigInt.Normalized 64 (Vector.map (Expression.eval env) y3))
    (hyT2 : BigInt.Normalized 64 (Vector.map (Expression.eval env) yT2))
    (hlam : BigInt.Normalized 64 (Vector.map (Expression.eval env) lam2)) :
    polyValue 64 (Vector.map (Expression.eval env)
        (Vector.mapFinRange 10 fun k =>
          qpCoeff q7 q7t k.val
            + (if h : k.val < 4 then
                y3[k.val]'h + yT2[k.val]'h + ((c976 : ℕ) : F circomPrime) * lam2[k.val]'h else 0)))
      = (BigInt.value 64 (Vector.map (Expression.eval env) q7)
          + (Expression.eval env q7t).val * 2 ^ 256) * P256
        + BigInt.value 64 (Vector.map (Expression.eval env) y3)
        + BigInt.value 64 (Vector.map (Expression.eval env) yT2)
        + c976 * BigInt.value 64 (Vector.map (Expression.eval env) lam2) := by
  have hq7d := digit_lt_of_norm' env q7 hq7
  rw [polyValue10_split env (fun k => qpCoeff q7 q7t k.val)
    (fun k => if h : k.val < 4 then
        y3[k.val]'h + yT2[k.val]'h + ((c976 : ℕ) : F circomPrime) * lam2[k.val]'h else 0)
    (by
      intro k
      dsimp only
      have hqp := val_qpCoeff_lt env q7 q7t k.val hq7d hq7t
      have hg : (Expression.eval env (if h : k.val < 4 then
          y3[k.val]'h + yT2[k.val]'h + ((c976 : ℕ) : F circomPrime) * lam2[k.val]'h else 0)).val
          < 2 ^ 98 := by
        by_cases hk : k.val < 4
        · rw [dif_pos hk, val_affine3 env _ _ _ _ (digit_lt_of_norm' env y3 hy3 k.val hk)
            (digit_lt_of_norm' env yT2 hyT2 k.val hk) (digit_lt_of_norm' env lam2 hlam k.val hk)
            (by decide : c976 < 2 ^ 33)]
          have h1 := digit_lt_of_norm' env y3 hy3 k.val hk
          have h2 := digit_lt_of_norm' env yT2 hyT2 k.val hk
          have h3 := digit_lt_of_norm' env lam2 hlam k.val hk
          have h4 : c976 * (Expression.eval env lam2[k.val]).val < 2 ^ 33 * 2 ^ 64 :=
            Nat.mul_lt_mul'' (by decide) h3
          have h5 : (2:ℕ) ^ 33 * 2 ^ 64 < 2 ^ 98 := by norm_num
          omega
        · rw [dif_neg hk, show Expression.eval env (0 : Expression (F circomPrime)) = 0 from rfl,
            ZMod.val_zero]; positivity
      have hpr : 4 * 2 ^ 128 + 2 ^ 98 < circomPrime := by decide
      omega)]
  rw [sum_guard_affine env y3 yT2 lam2 hy3 hyT2 hlam,
    show (∑ k ∈ Finset.range 10,
          (if h : k < 10 then (Expression.eval env (qpCoeff q7 q7t (⟨k, h⟩ : Fin 10).val)).val else 0)
            * 2 ^ (64 * k))
        = ∑ k ∈ Finset.range 9, (Expression.eval env (qpCoeff q7 q7t k)).val * 2 ^ (64 * k) from by
      rw [Finset.sum_range_succ, dif_pos (show (9:ℕ) < 10 by omega),
        eval_qpCoeff_high env q7 q7t 9 (by omega), zero_mul, add_zero]
      apply Finset.sum_congr rfl; intro k hk
      rw [Finset.mem_range] at hk
      rw [dif_pos (by omega : k < 10)]]
  rw [polyValue_qpCoeff env q7 q7t hq7d hq7t]
  ring

set_option maxRecDepth 4000 in

lemma c2b_fp (env : Environment (F circomPrime))
    (lam2 xT2 x2 y3 yT2 q7 : Var Emu (F circomPrime)) (q7t : Expression (F circomPrime))
    (P : Vector (Expression (F circomPrime)) 7)
    (hP : ∀ k : Fin 7, Expression.eval env P[k.val]
      = Expression.eval env (bigIntMulNoReduce lam2
          (Vector.ofFn fun i : Fin 4 =>
            xT2[i.val]'i.isLt + ((2 ^ 64 - 1 : ℕ) : F circomPrime) - x2[i.val]'i.isLt))[k.val])
    (hlam : BigInt.Normalized 64 (Vector.map (Expression.eval env) lam2))
    (hxT2 : BigInt.Normalized 64 (Vector.map (Expression.eval env) xT2))
    (hx2 : BigInt.Normalized 64 (Vector.map (Expression.eval env) x2))
    (hy3 : BigInt.Normalized 64 (Vector.map (Expression.eval env) y3))
    (hyT2 : BigInt.Normalized 64 (Vector.map (Expression.eval env) yT2))
    (hq7 : BigInt.Normalized 64 (Vector.map (Expression.eval env) q7))
    (hq7t : (Expression.eval env q7t).val < 2 ^ 64)
    (hspec : polyValue 64 (Vector.map (Expression.eval env)
          (Vector.mapFinRange 10 fun k =>
            (if h : k.val < 7 then P[k.val]'h else 0)
              + (if k.val < 5 then cExp (2 ^ 35 * P256) k.val else 0)))
        = polyValue 64 (Vector.map (Expression.eval env)
          (Vector.mapFinRange 10 fun k =>
            qpCoeff q7 q7t k.val
              + (if h : k.val < 4 then
                  y3[k.val]'h + yT2[k.val]'h + ((c976 : ℕ) : F circomPrime) * lam2[k.val]'h else 0)))) :
    decodeFe (Vector.map (Expression.eval env) y3)
      = decodeFe (Vector.map (Expression.eval env) lam2)
          * (decodeFe (Vector.map (Expression.eval env) xT2)
            - decodeFe (Vector.map (Expression.eval env) x2))
        - decodeFe (Vector.map (Expression.eval env) yT2) := by
  have hL := polyValue_c2b_lhs env lam2 xT2 x2 P hlam hxT2 hx2 hP
  have hR := polyValue_c2b_rhs env q7 q7t y3 yT2 lam2 hq7 hq7t hy3 hyT2 hlam
  have hxd := xd_value env xT2 x2 hxT2 hx2
  rw [show (2 ^ 256 - 1 : ℕ) = c976 + P256 from by
    norm_num [c976, P256, Specs.Secp256k1.p]] at hxd
  have hnat := hL.symm.trans (hspec.trans hR)
  have hc1 := congrArg (Nat.cast : ℕ → Specs.Secp256k1.Fp) hnat
  have hc2 := congrArg (Nat.cast : ℕ → Specs.Secp256k1.Fp) hxd
  push_cast at hc1 hc2
  rw [show ((P256 : ℕ) : Specs.Secp256k1.Fp) = 0 from ZMod.natCast_self _] at hc1 hc2
  simp only [decodeFe, limbBits]
  linear_combination -hc1
    + ((BigInt.value 64 (Vector.map (Expression.eval env) lam2) : ℕ) : Specs.Secp256k1.Fp) * hc2

lemma polyValue9_split3 (env : Environment (F circomPrime))
    (A B C : Fin 9 → Expression (F circomPrime))
    (hb : ∀ k : Fin 9, (Expression.eval env (A k)).val + (Expression.eval env (B k)).val
      + (Expression.eval env (C k)).val < circomPrime) :
    polyValue 64 (Vector.map (Expression.eval env) (Vector.mapFinRange 9 fun k => A k + B k + C k))
      = (∑ k ∈ Finset.range 9, (if h : k < 9 then (Expression.eval env (A ⟨k, h⟩)).val else 0) * 2 ^ (64 * k))
        + (∑ k ∈ Finset.range 9, (if h : k < 9 then (Expression.eval env (B ⟨k, h⟩)).val else 0) * 2 ^ (64 * k))
        + (∑ k ∈ Finset.range 9, (if h : k < 9 then (Expression.eval env (C ⟨k, h⟩)).val else 0) * 2 ^ (64 * k)) := by
  rw [polyValue,
    ← Fin.sum_univ_eq_sum_range
      (fun k => (if h : k < 9 then (Expression.eval env (A ⟨k, h⟩)).val else 0) * 2 ^ (64 * k)),
    ← Fin.sum_univ_eq_sum_range
      (fun k => (if h : k < 9 then (Expression.eval env (B ⟨k, h⟩)).val else 0) * 2 ^ (64 * k)),
    ← Fin.sum_univ_eq_sum_range
      (fun k => (if h : k < 9 then (Expression.eval env (C ⟨k, h⟩)).val else 0) * 2 ^ (64 * k)),
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [Vector.getElem_map, Vector.getElem_mapFinRange, dif_pos k.isLt, dif_pos k.isLt, dif_pos k.isLt]
  have hk : (⟨k.val, k.isLt⟩ : Fin 9) = k := rfl
  have h1 : (Expression.eval env (A k) + Expression.eval env (B k)).val
      = (Expression.eval env (A k)).val + (Expression.eval env (B k)).val :=
    ZMod.val_add_of_lt (by have := hb k; have := (Expression.eval env (C k)).val.zero_le; omega)
  rw [hk,
    show Expression.eval env (A k + B k + C k)
        = Expression.eval env (A k) + Expression.eval env (B k) + Expression.eval env (C k) from rfl,
    ZMod.val_add_of_lt (by rw [h1]; have := hb k; omega), h1]
  ring

set_option exponentiation.threshold 1200 in

lemma lp_block (env : Environment (F circomPrime)) (lam : Var Emu (F circomPrime))
    (lp : Vector (Expression (F circomPrime)) 4) (d4 : Expression (F circomPrime))
    (hlam : BigInt.Normalized 64 (Vector.map (Expression.eval env) lam))
    (hlp : ∀ (j : ℕ) (hj : j < 4), Expression.eval env (lp[j]'hj)
      = Expression.eval env (lam[j]'hj) * Expression.eval env d4)
    (hd4 : (Expression.eval env d4).val < 4) :
    (∑ k ∈ Finset.range 9,
        (if h : k < 9 then
          (Expression.eval env (if h' : 4 ≤ k ∧ k < 8 then lp[k - 4]'(by omega) else 0)).val
          else 0) * 2 ^ (64 * k))
      = (Expression.eval env d4).val
        * BigInt.value 64 (Vector.map (Expression.eval env) lam) * 2 ^ 256 := by
  have dl := digit_lt_of_norm' env lam hlam
  have hlpval : ∀ (j : ℕ) (hj : j < 4), (Expression.eval env (lp[j]'hj)).val
      = (Expression.eval env (lam[j]'hj)).val * (Expression.eval env d4).val := by
    intro j hj
    rw [hlp j hj, ZMod.val_mul, Nat.mod_eq_of_lt (by
      have h1 := dl j hj
      have h2 : (Expression.eval env (lam[j]'hj)).val * (Expression.eval env d4).val < 2 ^ 64 * 4 :=
        Nat.mul_lt_mul'' h1 hd4
      have h3 : (2:ℕ) ^ 64 * 4 < circomPrime := by decide
      omega)]
  rw [value_eq_range_sum 64 (Vector.map (Expression.eval env) lam)]
  simp only [numLimbs, Finset.sum_range_succ, Finset.sum_range_zero, Vector.getElem_map,
    Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceSub, and_false, and_true,
    reduceDIte]
  rw [hlpval 0 (by omega), hlpval 1 (by omega), hlpval 2 (by omega), hlpval 3 (by omega)]
  simp only [show Expression.eval env (0 : Expression (F circomPrime)) = 0 from rfl,
    ZMod.val_zero, zero_mul, add_zero, zero_add]
  ring

lemma ya_value (env : Environment (F circomPrime)) (yT yA : Var Emu (F circomPrime))
    (hyT : BigInt.Normalized 64 (Vector.map (Expression.eval env) yT))
    (hyA : BigInt.Normalized 64 (Vector.map (Expression.eval env) yA)) :
    (∑ j : Fin 4, (Expression.eval env
        (yT[j.val]'j.isLt - yA[j.val]'j.isLt
          + (((2 ^ 64 - 1 + limbOfNat cK j.val : ℕ) : F circomPrime)
              : Expression (F circomPrime)))).val * 2 ^ (64 * j.val))
      + BigInt.value 64 (Vector.map (Expression.eval env) yA)
    = BigInt.value 64 (Vector.map (Expression.eval env) yT) + 2 * P256 := by
  have hkey : (2 ^ 256 - 1) + cK = 2 * P256 := by
    have h1 : (2 ^ 256 - 1 : ℕ) = c976 + P256 := by norm_num [c976, P256, Specs.Secp256k1.p]
    have h2 : cK = P256 - c976 := rfl
    have h3 : c976 ≤ P256 := by norm_num [c976, P256, Specs.Secp256k1.p]
    omega
  have hval : ∀ j : Fin 4, (Expression.eval env
      (yT[j.val]'j.isLt - yA[j.val]'j.isLt
        + (((2 ^ 64 - 1 + limbOfNat cK j.val : ℕ) : F circomPrime) : Expression (F circomPrime)))).val
      = (Expression.eval env (yT[j.val]'j.isLt)).val + (2 ^ 64 - 1 + limbOfNat cK j.val)
        - (Expression.eval env (yA[j.val]'j.isLt)).val := by
    intro j
    have hyAj := digit_lt_of_norm' env yA hyA j.val j.isLt
    have hyTj := digit_lt_of_norm' env yT hyT j.val j.isLt
    have hcK := limbOfNat_lt cK j.val
    simp only [limbBits] at hcK
    have hle : (Expression.eval env (yA[j.val]'j.isLt)).val
        ≤ (Expression.eval env (yT[j.val]'j.isLt)).val + (2 ^ 64 - 1 + limbOfNat cK j.val) := by omega
    have hlt : (Expression.eval env (yT[j.val]'j.isLt)).val + (2 ^ 64 - 1 + limbOfNat cK j.val)
        - (Expression.eval env (yA[j.val]'j.isLt)).val < circomPrime := by
      have h : (2:ℕ) ^ 64 + (2 ^ 64 - 1 + 2 ^ 64) < circomPrime := by decide
      omega
    rw [show Expression.eval env (yT[j.val]'j.isLt - yA[j.val]'j.isLt
            + (((2 ^ 64 - 1 + limbOfNat cK j.val : ℕ) : F circomPrime) : Expression (F circomPrime)))
        = Expression.eval env (yT[j.val]'j.isLt - yA[j.val]'j.isLt)
          + ((2 ^ 64 - 1 + limbOfNat cK j.val : ℕ) : F circomPrime) from eval_add env _ _,
      eval_sub]
    exact val_sub_add_const' _ _ _ hle hlt
  rw [MulMod.value_map_eval, MulMod.value_map_eval, ← Finset.sum_add_distrib]
  have hterm : ∀ j : Fin 4,
      (Expression.eval env (yT[j.val]'j.isLt - yA[j.val]'j.isLt
        + (((2 ^ 64 - 1 + limbOfNat cK j.val : ℕ) : F circomPrime) : Expression (F circomPrime)))).val
          * 2 ^ (64 * j.val)
        + (Expression.eval env yA[j.val]).val * 2 ^ (64 * j.val)
      = ((Expression.eval env yT[j.val]).val + (2 ^ 64 - 1 + limbOfNat cK j.val)) * 2 ^ (64 * j.val) := by
    intro j
    rw [hval j, ← Nat.add_mul]
    congr 1
    have := digit_lt_of_norm' env yA hyA j.val j.isLt
    omega
  rw [Finset.sum_congr rfl (fun j _ => hterm j)]
  have hsplit : (∑ j : Fin 4,
        ((Expression.eval env yT[j.val]).val + (2 ^ 64 - 1 + limbOfNat cK j.val)) * 2 ^ (64 * j.val))
      = (∑ j : Fin 4, (Expression.eval env yT[j.val]).val * 2 ^ (64 * j.val))
        + ∑ j : Fin 4, (2 ^ 64 - 1 + limbOfNat cK j.val) * 2 ^ (64 * j.val) := by
    rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro j _; ring
  rw [hsplit, ← MulMod.value_map_eval]
  have hcksum := limb_sum_range 4 cK (by
    have e : (2:ℕ) ^ (64 * 4) = 2 ^ 256 := by norm_num
    have hcKlt : cK < 2 ^ 256 := by decide
    omega)
  have hfin : (∑ j : Fin 4, (2 ^ 64 - 1 + limbOfNat cK j.val) * 2 ^ (64 * j.val))
      = (2 ^ 256 - 1) + cK := by
    rw [Fin.sum_univ_eq_sum_range (fun j => (2 ^ 64 - 1 + limbOfNat cK j) * 2 ^ (64 * j))]
    have hsplit2 : (∑ k ∈ Finset.range 4, (2 ^ 64 - 1 + limbOfNat cK k) * 2 ^ (64 * k))
        = (∑ k ∈ Finset.range 4, (2 ^ 64 - 1) * 2 ^ (64 * k))
          + ∑ k ∈ Finset.range 4, limbOfNat cK k * 2 ^ (64 * k) := by
      rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro k _; ring
    have hones : (∑ k ∈ Finset.range 4, (2 ^ 64 - 1) * 2 ^ (64 * k)) = 2 ^ 256 - 1 := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_zero]
      norm_num
    rw [hsplit2, hones, hcksum]
  rw [hfin, hkey]

lemma sum_guard_ya (env : Environment (F circomPrime)) (yT yA : Var Emu (F circomPrime)) :
    (∑ k ∈ Finset.range 9, (if h : k < 9 then
        (Expression.eval env (if h' : k < 4 then
          yT[k]'h' - yA[k]'h'
            + (((2 ^ 64 - 1 + limbOfNat cK k : ℕ) : F circomPrime) : Expression (F circomPrime))
          else 0)).val else 0) * 2 ^ (64 * k))
      = ∑ j : Fin 4, (Expression.eval env
          (yT[j.val]'j.isLt - yA[j.val]'j.isLt
            + (((2 ^ 64 - 1 + limbOfNat cK j.val : ℕ) : F circomPrime) : Expression (F circomPrime)))).val
            * 2 ^ (64 * j.val) := by
  rw [show (∑ j : Fin 4, (Expression.eval env
          (yT[j.val]'j.isLt - yA[j.val]'j.isLt
            + (((2 ^ 64 - 1 + limbOfNat cK j.val : ℕ) : F circomPrime) : Expression (F circomPrime)))).val
            * 2 ^ (64 * j.val))
        = ∑ j ∈ Finset.range 4, (if h : j < 4 then
            (Expression.eval env (yT[j]'h - yA[j]'h
              + (((2 ^ 64 - 1 + limbOfNat cK j : ℕ) : F circomPrime) : Expression (F circomPrime)))).val
            else 0) * 2 ^ (64 * j) from by
      rw [← Fin.sum_univ_eq_sum_range (fun j => (if h : j < 4 then
            (Expression.eval env (yT[j]'h - yA[j]'h
              + (((2 ^ 64 - 1 + limbOfNat cK j : ℕ) : F circomPrime) : Expression (F circomPrime)))).val
            else 0) * 2 ^ (64 * j))]
      apply Finset.sum_congr rfl; intro j _; rw [dif_pos j.isLt]]
  rw [← Finset.sum_subset (Finset.range_subset_range.mpr (by omega : 4 ≤ 9))
    (f := fun k => (if h : k < 9 then
        (Expression.eval env (if h' : k < 4 then
          yT[k]'h' - yA[k]'h'
            + (((2 ^ 64 - 1 + limbOfNat cK k : ℕ) : F circomPrime) : Expression (F circomPrime))
          else 0)).val else 0) * 2 ^ (64 * k))]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    rw [dif_pos (by omega : k < 9), dif_pos hk, dif_pos hk]
  · intro k hk9 hk4
    rw [Finset.mem_range] at hk9
    rw [Finset.mem_range] at hk4
    rw [dif_pos (by omega : k < 9), dif_neg (by omega : ¬ k < 4),
      show Expression.eval env (0 : Expression (F circomPrime)) = 0 from rfl, ZMod.val_zero,
      Nat.zero_mul]

set_option maxRecDepth 4000 in

lemma polyValue_a2_lhs (env : Environment (F circomPrime))
    (lam d : Var Emu (F circomPrime)) (lp : Vector (Expression (F circomPrime)) 4)
    (d4 : Expression (F circomPrime)) (P : Vector (Expression (F circomPrime)) 7)
    (hP : ∀ k : Fin 7,
      Expression.eval env P[k.val] = Expression.eval env (bigIntMulNoReduce lam d)[k.val])
    (hlam : BigInt.Normalized 64 (Vector.map (Expression.eval env) lam))
    (hd : BigInt.Normalized 64 (Vector.map (Expression.eval env) d))
    (hlp : ∀ (j : ℕ) (hj : j < 4), Expression.eval env (lp[j]'hj)
      = Expression.eval env (lam[j]'hj) * Expression.eval env d4)
    (hd4 : (Expression.eval env d4).val < 4) :
    polyValue 64 (Vector.map (Expression.eval env)
        (Vector.mapFinRange 9 fun k =>
          (if h : k.val < 7 then P[k.val]'h else 0)
            + (if h : 4 ≤ k.val ∧ k.val < 8 then lp[k.val - 4]'(by omega) else 0)
            + (if k.val < 5 then cExp (8 * P256) k.val else 0)))
      = BigInt.value 64 (Vector.map (Expression.eval env) lam)
          * BigInt.value 64 (Vector.map (Expression.eval env) d)
        + (Expression.eval env d4).val * BigInt.value 64 (Vector.map (Expression.eval env) lam) * 2 ^ 256
        + 8 * P256 := by
  have hlamd := digit_lt_of_norm env lam hlam
  have hdd := digit_lt_of_norm env d hd
  rw [polyValue9_split3 env (fun k => if h : k.val < 7 then P[k.val]'h else 0)
    (fun k => if h : 4 ≤ k.val ∧ k.val < 8 then lp[k.val - 4]'(by omega) else 0)
    (fun k => if k.val < 5 then cExp (8 * P256) k.val else 0) (by
      intro k
      dsimp only
      have hA : (Expression.eval env (if h : k.val < 7 then P[k.val]'h else 0)).val < 4 * 2 ^ 128 := by
        by_cases hk : k.val < 7
        · rw [dif_pos hk, hP ⟨k.val, hk⟩]
          exact val_bigIntMulNoReduce_coeff_lt env lam d ⟨k.val, hk⟩ hlamd hdd (by decide)
        · rw [dif_neg hk, show Expression.eval env (0 : Expression (F circomPrime)) = 0 from rfl,
            ZMod.val_zero]; positivity
      have hB : (Expression.eval env (if h : 4 ≤ k.val ∧ k.val < 8 then lp[k.val - 4]'(by omega) else 0)).val
          < 2 ^ 67 := by
        by_cases hk : 4 ≤ k.val ∧ k.val < 8
        · have hk4 : k.val - 4 < 4 := by omega
          rw [dif_pos hk, hlp (k.val - 4) hk4, ZMod.val_mul]
          have h1 := digit_lt_of_norm' env lam hlam (k.val - 4) hk4
          have h2 : (Expression.eval env (lam[k.val - 4]'hk4)).val * (Expression.eval env d4).val < 2 ^ 64 * 4 :=
            Nat.mul_lt_mul'' h1 hd4
          have h3 : (2:ℕ) ^ 64 * 4 < 2 ^ 67 := by norm_num
          exact lt_of_le_of_lt (Nat.mod_le _ _) (lt_trans h2 h3)
        · rw [dif_neg hk, show Expression.eval env (0 : Expression (F circomPrime)) = 0 from rfl,
            ZMod.val_zero]; positivity
      have hC : (Expression.eval env (if k.val < 5 then cExp (8 * P256) k.val else 0)).val < 2 ^ 64 := by
        by_cases hk : k.val < 5
        · rw [if_pos hk, eval_cExp, val_limbOfNat]; exact limbOfNat_lt _ _
        · rw [if_neg hk, show Expression.eval env (0 : Expression (F circomPrime)) = 0 from rfl,
            ZMod.val_zero]; positivity
      have hpr : 4 * 2 ^ 128 + 2 ^ 67 + 2 ^ 64 < circomPrime := by decide
      omega)]
  dsimp only
  rw [polyValue_pad9_7 env P, lp_block env lam lp d4 hlam hlp hd4,
    polyValue_pad9_cExp env (8 * P256) (by
      have h : P256 < 2 ^ 256 := P256_lt
      have e1 : (2:ℕ) ^ 3 * 2 ^ 256 = 2 ^ 259 := by rw [← pow_add]
      have e2 : (2:ℕ) ^ 259 ≤ 2 ^ 320 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
      have e3 : 8 * P256 < 2 ^ 3 * 2 ^ 256 := by
        have : (8:ℕ) = 2 ^ 3 := by norm_num
        rw [this]; exact Nat.mul_lt_mul_of_pos_left h (by positivity)
      omega)]
  have hpv : polyValue 64 (Vector.map (Expression.eval env) P)
      = BigInt.value 64 (Vector.map (Expression.eval env) lam)
        * BigInt.value 64 (Vector.map (Expression.eval env) d) := by
    rw [← MulMod.polyValue_mul_eq env lam d hlamd hdd (by decide)]
    simp only [polyValue, Vector.getElem_map]
    apply Finset.sum_congr rfl; intro i _; rw [hP i]
  rw [hpv]

set_option maxRecDepth 4000 in

lemma polyValue_a2_rhs (env : Environment (F circomPrime))
    (qs : Var Emu (F circomPrime)) (qst : Expression (F circomPrime))
    (yT yA : Var Emu (F circomPrime))
    (hqs : BigInt.Normalized 64 (Vector.map (Expression.eval env) qs))
    (hqst : (Expression.eval env qst).val < 2 ^ 64)
    (hyT : BigInt.Normalized 64 (Vector.map (Expression.eval env) yT))
    (hyA : BigInt.Normalized 64 (Vector.map (Expression.eval env) yA)) :
    polyValue 64 (Vector.map (Expression.eval env)
        (Vector.mapFinRange 9 fun k =>
          qpCoeff qs qst k.val
            + (if h : k.val < 4 then
                yT[k.val]'h - yA[k.val]'h
                  + (((2 ^ 64 - 1 + limbOfNat cK k.val : ℕ) : F circomPrime)
                      : Expression (F circomPrime)) else 0)))
      = (BigInt.value 64 (Vector.map (Expression.eval env) qs)
          + (Expression.eval env qst).val * 2 ^ 256) * P256
        + ∑ j : Fin 4, (Expression.eval env
            (yT[j.val]'j.isLt - yA[j.val]'j.isLt
              + (((2 ^ 64 - 1 + limbOfNat cK j.val : ℕ) : F circomPrime) : Expression (F circomPrime)))).val
              * 2 ^ (64 * j.val) := by
  have hqsd := digit_lt_of_norm' env qs hqs
  rw [polyValue9_split env (fun k => qpCoeff qs qst k.val)
    (fun k => if h : k.val < 4 then
        yT[k.val]'h - yA[k.val]'h
          + (((2 ^ 64 - 1 + limbOfNat cK k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
      else 0)
    (by
      intro k
      dsimp only
      have hqp := val_qpCoeff_lt env qs qst k.val hqsd hqst
      have hg : (Expression.eval env (if h : k.val < 4 then
          yT[k.val]'h - yA[k.val]'h
            + (((2 ^ 64 - 1 + limbOfNat cK k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
          else 0)).val < 2 ^ 67 := by
        by_cases hk : k.val < 4
        · have hyAj := digit_lt_of_norm' env yA hyA k.val hk
          have hyTj := digit_lt_of_norm' env yT hyT k.val hk
          have hcK := limbOfNat_lt cK k.val
          simp only [limbBits] at hcK
          rw [dif_pos hk,
            show Expression.eval env (yT[k.val]'hk - yA[k.val]'hk
                  + (((2 ^ 64 - 1 + limbOfNat cK k.val : ℕ) : F circomPrime) : Expression (F circomPrime)))
              = Expression.eval env (yT[k.val]'hk - yA[k.val]'hk)
                + ((2 ^ 64 - 1 + limbOfNat cK k.val : ℕ) : F circomPrime) from eval_add env _ _,
            eval_sub,
            val_sub_add_const' _ _ _ (by omega) (by
              have h : (2:ℕ) ^ 64 + (2 ^ 64 - 1 + 2 ^ 64) < circomPrime := by decide
              omega)]
          omega
        · rw [dif_neg hk, show Expression.eval env (0 : Expression (F circomPrime)) = 0 from rfl,
            ZMod.val_zero]; positivity
      have hpr : 4 * 2 ^ 128 + 2 ^ 67 < circomPrime := by decide
      omega)]
  rw [show (∑ k ∈ Finset.range 9,
        (if h : k < 9 then (Expression.eval env (qpCoeff qs qst (⟨k, h⟩ : Fin 9).val)).val else 0)
          * 2 ^ (64 * k))
      = ∑ k ∈ Finset.range 9, (Expression.eval env (qpCoeff qs qst k)).val * 2 ^ (64 * k) from by
    apply Finset.sum_congr rfl; intro k hk; rw [dif_pos (Finset.mem_range.mp hk)]]
  rw [polyValue_qpCoeff env qs qst hqsd hqst, sum_guard_ya env yT yA]


set_option maxRecDepth 4000 in
/-- Fat-limb analogue of `a2_fp` (§BORROW-PILOT): `λ·dtil ≡ yT - yA (mod p)`,
directly from the single combined `gfQuadFat` identity — no separate
`dblock`/`lp` step, `dtil` carries the whole borrow-free difference. -/
lemma a2_fp_fat (env : Environment (F circomPrime))
    (lam dtil yT yA qs : Var Emu (F circomPrime)) (qst : Expression (F circomPrime))
    (P : Vector (Expression (F circomPrime)) 7)
    (hP : ∀ k : Fin 7,
      Expression.eval env P[k.val] = Expression.eval env (bigIntMulNoReduce lam dtil)[k.val])
    (hlam : BigInt.Normalized 64 (Vector.map (Expression.eval env) lam))
    (hdtil : ∀ i : Fin 4, (Expression.eval env dtil[i.val]).val < 3 * 2 ^ 64)
    (hqs : BigInt.Normalized 64 (Vector.map (Expression.eval env) qs))
    (hqst : (Expression.eval env qst).val < 2 ^ 64)
    (hyT : BigInt.Normalized 64 (Vector.map (Expression.eval env) yT))
    (hyA : BigInt.Normalized 64 (Vector.map (Expression.eval env) yA))
    (hspec : polyValue 64 (Vector.map (Expression.eval env)
          (Vector.mapFinRange 9 fun k =>
            (if h : k.val < 7 then P[k.val]'h else 0)
              + (if k.val < 5 then cExp (8 * P256) k.val else 0)))
        = polyValue 64 (Vector.map (Expression.eval env)
          (Vector.mapFinRange 9 fun k =>
            qpCoeff qs qst k.val
              + (if h : k.val < 4 then
                  yT[k.val]'h - yA[k.val]'h
                    + (((2 ^ 64 - 1 + limbOfNat cK k.val : ℕ) : F circomPrime)
                        : Expression (F circomPrime)) else 0)))) :
    ((∑ j : Fin 4, (Expression.eval env dtil[j.val]).val * 2 ^ (64 * j.val) : ℕ)
        : Specs.Secp256k1.Fp)
        * decodeFe (Vector.map (Expression.eval env) lam)
      = decodeFe (Vector.map (Expression.eval env) yT)
        - decodeFe (Vector.map (Expression.eval env) yA) := by
  have hL := polyValue_a2_lhs_fat env lam dtil P hP hlam hdtil
  have hR := polyValue_a2_rhs env qs qst yT yA hqs hqst hyT hyA
  have hya := ya_value env yT yA hyT hyA
  have hnat := hL.symm.trans (hspec.trans hR)
  have hc1 := congrArg (Nat.cast : ℕ → Specs.Secp256k1.Fp) hnat
  have hc2 := congrArg (Nat.cast : ℕ → Specs.Secp256k1.Fp) hya
  have hc3 := congrArg (Nat.cast : ℕ → Specs.Secp256k1.Fp) (MulMod.value_map_eval (B := 64) env lam)
  push_cast at hc1 hc2 hc3
  rw [show ((P256 : ℕ) : Specs.Secp256k1.Fp) = 0 from ZMod.natCast_self _] at hc1 hc2
  simp only [decodeFe, limbBits]
  push_cast
  linear_combination hc1 + hc2
    + (∑ i : Fin 4, ((Expression.eval env dtil[i.val]).val : Specs.Secp256k1.Fp) * 2 ^ (64 * i.val)) * hc3


lemma val_convLX_lt (env : Environment (F circomPrime)) (a b : Var Emu (F circomPrime))
    (k : Fin 7)
    (ha : ∀ i : Fin 4, (Expression.eval env a[i.val]).val < 2 ^ 64)
    (hb : ∀ i : Fin 4, (Expression.eval env b[i.val]).val < 2 ^ 65) :
    (Expression.eval env ((bigIntMulNoReduce a b)[k.val])).val < 4 * 2 ^ 129 := by
  have ha' : ∀ i : Fin 4, (Expression.eval env a[i.val]).val < 2 ^ 65 :=
    fun i => lt_trans (ha i) (by norm_num)
  rw [val_bigIntMulNoReduce_coeff env a b k ha' hb (by decide : (4:ℕ) * (2 ^ 65 * 2 ^ 65) < circomPrime)]
  simp only [numLimbs]
  have hterm : ∀ i : Fin 4, (if h : i.val ≤ k.val ∧ k.val - i.val < 4 then
      (Expression.eval env a[i.val]).val
        * (Expression.eval env (b[k.val - i.val]'h.2)).val else 0)
      ≤ 2 ^ 64 * 2 ^ 65 - 1 := by
    intro i
    by_cases h : i.val ≤ k.val ∧ k.val - i.val < 4
    · rw [dif_pos h]
      have h1 := ha i
      have h2 := hb ⟨k.val - i.val, h.2⟩
      have : (Expression.eval env a[i.val]).val
          * (Expression.eval env (b[k.val - i.val]'h.2)).val < 2 ^ 64 * 2 ^ 65 :=
        Nat.mul_lt_mul'' h1 h2
      omega
    · rw [dif_neg h]; positivity
  have hcard : (∑ i : Fin 4, if h : i.val ≤ k.val ∧ k.val - i.val < 4 then
      (Expression.eval env a[i.val]).val
        * (Expression.eval env (b[k.val - i.val]'h.2)).val else 0)
      ≤ 4 * (2 ^ 64 * 2 ^ 65 - 1) := by
    calc _ ≤ ∑ _i : Fin 4, (2 ^ 64 * 2 ^ 65 - 1) := Finset.sum_le_sum (fun i _ => hterm i)
      _ = 4 * (2 ^ 64 * 2 ^ 65 - 1) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hfin : (4:ℕ) * (2 ^ 64 * 2 ^ 65 - 1) < 4 * 2 ^ 129 := by norm_num
  omega

lemma polyValue_pad10_7_add (env : Environment (F circomPrime))
    (P2 P1 : Vector (Expression (F circomPrime)) 7)
    (hb : ∀ k : Fin 7,
      (Expression.eval env P2[k.val]).val + (Expression.eval env P1[k.val]).val < circomPrime) :
    (∑ k ∈ Finset.range 10,
        (if h : k < 10 then
          (Expression.eval env (if h' : k < 7 then P2[k]'h' + P1[k]'h' else 0)).val else 0)
          * 2 ^ (64 * k))
      = polyValue 64 (Vector.map (Expression.eval env) P2)
        + polyValue 64 (Vector.map (Expression.eval env) P1) := by
  have key : ∀ k ∈ Finset.range 10,
      (if h : k < 10 then
          (Expression.eval env (if h' : k < 7 then P2[k]'h' + P1[k]'h' else 0)).val else 0)
        * 2 ^ (64 * k)
      = (if h : k < 10 then
            (Expression.eval env (if h' : k < 7 then P2[k]'h' else 0)).val else 0) * 2 ^ (64 * k)
        + (if h : k < 10 then
            (Expression.eval env (if h' : k < 7 then P1[k]'h' else 0)).val else 0) * 2 ^ (64 * k) := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [dif_pos hk, dif_pos hk, dif_pos hk]
    by_cases h7 : k < 7
    · rw [dif_pos h7, dif_pos h7, dif_pos h7,
        show Expression.eval env (P2[k]'h7 + P1[k]'h7)
            = Expression.eval env (P2[k]'h7) + Expression.eval env (P1[k]'h7) from rfl,
        ZMod.val_add_of_lt (hb ⟨k, h7⟩), Nat.add_mul]
    · rw [dif_neg h7, dif_neg h7, dif_neg h7,
        show Expression.eval env (0 : Expression (F circomPrime)) = 0 from rfl,
        ZMod.val_zero, Nat.zero_mul, add_zero]
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, polyValue_pad10_7, polyValue_pad10_7]





lemma boundAt_wideFlexT_lo (k : Fin 10) (hk : k.val < 7) :
    EqViaCarriesFlex.boundAt EqViaCarriesFlexT.wideFlexT.M k.val = 13 * 2 ^ 128 := by
  fin_cases k <;> revert hk <;> decide

lemma boundAt_wideFlexT_hi (k : Fin 10) (hk : 7 ≤ k.val) :
    EqViaCarriesFlex.boundAt EqViaCarriesFlexT.wideFlexT.M k.val = 2 ^ 67 := by
  fin_cases k <;> revert hk <;> decide

lemma a2_discharge (env : Environment (F circomPrime))
    (lam d yT yA qs : Var Emu (F circomPrime)) (qst d4 : Expression (F circomPrime))
    (lp : Vector (Expression (F circomPrime)) 4) (P : Vector (Expression (F circomPrime)) 7)
    (hP : ∀ k : Fin 7,
      Expression.eval env P[k.val] = Expression.eval env (bigIntMulNoReduce lam d)[k.val])
    (hlam : BigInt.Normalized 64 (Vector.map (Expression.eval env) lam))
    (hd : BigInt.Normalized 64 (Vector.map (Expression.eval env) d))
    (hlp : ∀ (j : ℕ) (hj : j < 4), Expression.eval env (lp[j]'hj)
      = Expression.eval env (lam[j]'hj) * Expression.eval env d4)
    (hd4 : (Expression.eval env d4).val < 4)
    (hqs : BigInt.Normalized 64 (Vector.map (Expression.eval env) qs))
    (hqst : (Expression.eval env qst).val < 2 ^ 3)
    (hyT : BigInt.Normalized 64 (Vector.map (Expression.eval env) yT))
    (hyA : BigInt.Normalized 64 (Vector.map (Expression.eval env) yA)) :
    (∀ k : Fin 9,
        ((Vector.map (Expression.eval env)
          (Vector.mapFinRange 9 fun k =>
            (if h : k.val < 7 then P[k.val]'h else 0)
              + (if h : 4 ≤ k.val ∧ k.val < 8 then lp[k.val - 4]'(by omega) else 0)
              + (if k.val < 5 then cExp (8 * P256) k.val else 0)))[k.val]).val
        < EqViaCarriesFlex.boundAt EqViaCarriesFlexT.quadFlexT.M k.val)
    ∧ (∀ k : Fin 9,
        ((Vector.map (Expression.eval env)
          (Vector.mapFinRange 9 fun k =>
            qpCoeff qs qst k.val
              + (if h : k.val < 4 then
                  yT[k.val]'h - yA[k.val]'h
                    + (((2 ^ 64 - 1 + limbOfNat cK k.val : ℕ) : F circomPrime)
                        : Expression (F circomPrime)) else 0)))[k.val]).val
        < EqViaCarriesFlex.boundAt EqViaCarriesFlexT.quadFlexT.M k.val) := by
  have hlamd := digit_lt_of_norm env lam hlam
  have hdd := digit_lt_of_norm env d hd
  have hqsd := digit_lt_of_norm' env qs hqs
  have hqst64 : (Expression.eval env qst).val < 2 ^ 64 := by omega
  constructor
  · intro k
    rw [Vector.getElem_map, Vector.getElem_mapFinRange]
    have hB : (Expression.eval env (if h : 4 ≤ k.val ∧ k.val < 8 then lp[k.val - 4]'(by omega) else 0)).val
        < 2 ^ 67 := by
      by_cases hk : 4 ≤ k.val ∧ k.val < 8
      · have hk4 : k.val - 4 < 4 := by omega
        rw [dif_pos hk, hlp (k.val - 4) hk4, ZMod.val_mul]
        have h1 := digit_lt_of_norm' env lam hlam (k.val - 4) hk4
        have h2 : (Expression.eval env (lam[k.val - 4]'hk4)).val * (Expression.eval env d4).val < 2 ^ 64 * 4 :=
          Nat.mul_lt_mul'' h1 hd4
        have h3 : (2:ℕ) ^ 64 * 4 < 2 ^ 67 := by norm_num
        exact lt_of_le_of_lt (Nat.mod_le _ _) (lt_trans h2 h3)
      · rw [dif_neg hk, show Expression.eval env (0 : Expression (F circomPrime)) = 0 from rfl,
          ZMod.val_zero]; positivity
    have hC : (Expression.eval env (if k.val < 5 then cExp (8 * P256) k.val else 0)).val < 2 ^ 64 := by
      by_cases hk : k.val < 5
      · rw [if_pos hk, eval_cExp, val_limbOfNat]; exact limbOfNat_lt _ _
      · rw [if_neg hk, show Expression.eval env (0 : Expression (F circomPrime)) = 0 from rfl,
          ZMod.val_zero]; positivity
    have t1 := ZMod.val_add_le
      (Expression.eval env (if h : k.val < 7 then P[k.val]'h else 0)
        + Expression.eval env (if h : 4 ≤ k.val ∧ k.val < 8 then lp[k.val - 4]'(by omega) else 0))
      (Expression.eval env (if k.val < 5 then cExp (8 * P256) k.val else 0))
    have t2 := ZMod.val_add_le
      (Expression.eval env (if h : k.val < 7 then P[k.val]'h else 0))
      (Expression.eval env (if h : 4 ≤ k.val ∧ k.val < 8 then lp[k.val - 4]'(by omega) else 0))
    rw [show Expression.eval env
          ((if h : k.val < 7 then P[k.val]'h else 0)
            + (if h : 4 ≤ k.val ∧ k.val < 8 then lp[k.val - 4]'(by omega) else 0)
            + (if k.val < 5 then cExp (8 * P256) k.val else 0))
        = Expression.eval env (if h : k.val < 7 then P[k.val]'h else 0)
            + Expression.eval env (if h : 4 ≤ k.val ∧ k.val < 8 then lp[k.val - 4]'(by omega) else 0)
          + Expression.eval env (if k.val < 5 then cExp (8 * P256) k.val else 0) from rfl]
    by_cases hk7 : k.val < 7
    · rw [boundAt_quadFlexT_lo k hk7]
      have hA : (Expression.eval env (if h : k.val < 7 then P[k.val]'h else 0)).val < 4 * 2 ^ 128 := by
        rw [dif_pos hk7, hP ⟨k.val, hk7⟩]
        exact val_bigIntMulNoReduce_coeff_lt env lam d ⟨k.val, hk7⟩ hlamd hdd (by decide)
      omega
    · rw [boundAt_quadFlexT_hi k (by omega)]
      have hA0 : (Expression.eval env (if h : k.val < 7 then P[k.val]'h else 0)).val = 0 := by
        rw [dif_neg hk7, show Expression.eval env (0 : Expression (F circomPrime)) = 0 from rfl,
          ZMod.val_zero]
      have hC0 : (Expression.eval env (if k.val < 5 then cExp (8 * P256) k.val else 0)).val = 0 := by
        rw [if_neg (show ¬ k.val < 5 by omega),
          show Expression.eval env (0 : Expression (F circomPrime)) = 0 from rfl, ZMod.val_zero]
      omega
  · intro k
    rw [Vector.getElem_map, Vector.getElem_mapFinRange]
    have hg : (Expression.eval env (if h : k.val < 4 then
        yT[k.val]'h - yA[k.val]'h
          + (((2 ^ 64 - 1 + limbOfNat cK k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
        else 0)).val < 2 ^ 67 := by
      by_cases hk : k.val < 4
      · have hyAj := digit_lt_of_norm' env yA hyA k.val hk
        have hyTj := digit_lt_of_norm' env yT hyT k.val hk
        have hcK := limbOfNat_lt cK k.val
        simp only [limbBits] at hcK
        rw [dif_pos hk,
          show Expression.eval env (yT[k.val]'hk - yA[k.val]'hk
                + (((2 ^ 64 - 1 + limbOfNat cK k.val : ℕ) : F circomPrime) : Expression (F circomPrime)))
            = Expression.eval env (yT[k.val]'hk - yA[k.val]'hk)
              + ((2 ^ 64 - 1 + limbOfNat cK k.val : ℕ) : F circomPrime) from eval_add env _ _,
          eval_sub,
          val_sub_add_const' _ _ _ (by omega) (by
            have h : (2:ℕ) ^ 64 + (2 ^ 64 - 1 + 2 ^ 64) < circomPrime := by decide
            omega)]
        omega
      · rw [dif_neg hk, show Expression.eval env (0 : Expression (F circomPrime)) = 0 from rfl,
          ZMod.val_zero]; positivity
    have hle := ZMod.val_add_le (Expression.eval env (qpCoeff qs qst k.val))
      (Expression.eval env (if h : k.val < 4 then
        yT[k.val]'h - yA[k.val]'h
          + (((2 ^ 64 - 1 + limbOfNat cK k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
        else 0))
    rw [show Expression.eval env
          (qpCoeff qs qst k.val + (if h : k.val < 4 then
            yT[k.val]'h - yA[k.val]'h
              + (((2 ^ 64 - 1 + limbOfNat cK k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
            else 0))
        = Expression.eval env (qpCoeff qs qst k.val)
          + Expression.eval env (if h : k.val < 4 then
              yT[k.val]'h - yA[k.val]'h
                + (((2 ^ 64 - 1 + limbOfNat cK k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
              else 0) from rfl]
    by_cases hk7 : k.val < 7
    · rw [boundAt_quadFlexT_lo k hk7]
      have hqp := val_qpCoeff_lt env qs qst k.val hqsd hqst64
      omega
    · rw [boundAt_quadFlexT_hi k (by omega)]
      have hg0 : (Expression.eval env (if h : k.val < 4 then
          yT[k.val]'h - yA[k.val]'h
            + (((2 ^ 64 - 1 + limbOfNat cK k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
          else 0)).val = 0 := by
        rw [dif_neg (show ¬ k.val < 4 by omega),
          show Expression.eval env (0 : Expression (F circomPrime)) = 0 from rfl, ZMod.val_zero]
      have hqp := val_qpCoeff_tail env qs qst k.val (by omega) hqsd hqst
      omega


lemma c2b_discharge (env : Environment (F circomPrime))
    (lam2 xT2 x2 y3 yT2 q7 : Var Emu (F circomPrime)) (q7t : Expression (F circomPrime))
    (P : Vector (Expression (F circomPrime)) 7)
    (hP : ∀ k : Fin 7, Expression.eval env P[k.val]
      = Expression.eval env (bigIntMulNoReduce lam2
          (Vector.ofFn fun i : Fin 4 =>
            xT2[i.val]'i.isLt + ((2 ^ 64 - 1 : ℕ) : F circomPrime) - x2[i.val]'i.isLt))[k.val])
    (hlam : BigInt.Normalized 64 (Vector.map (Expression.eval env) lam2))
    (hxT2 : BigInt.Normalized 64 (Vector.map (Expression.eval env) xT2))
    (hx2 : BigInt.Normalized 64 (Vector.map (Expression.eval env) x2))
    (hy3 : BigInt.Normalized 64 (Vector.map (Expression.eval env) y3))
    (hyT2 : BigInt.Normalized 64 (Vector.map (Expression.eval env) yT2))
    (hq7 : BigInt.Normalized 64 (Vector.map (Expression.eval env) q7))
    (hq7t : (Expression.eval env q7t).val < 2 ^ 3) :
    (∀ k : Fin 10,
        ((Vector.map (Expression.eval env)
          (Vector.mapFinRange 10 fun k =>
            (if h : k.val < 7 then P[k.val]'h else 0)
              + (if k.val < 5 then cExp (2 ^ 35 * P256) k.val else 0)))[k.val]).val
        < EqViaCarriesFlex.boundAt EqViaCarriesFlexT.wideFlexT.M k.val)
    ∧ (∀ k : Fin 10,
        ((Vector.map (Expression.eval env)
          (Vector.mapFinRange 10 fun k =>
            qpCoeff q7 q7t k.val
              + (if h : k.val < 4 then
                  y3[k.val]'h + yT2[k.val]'h + ((c976 : ℕ) : F circomPrime) * (lam2[k.val]'h) else 0)))[k.val]).val
        < EqViaCarriesFlex.boundAt EqViaCarriesFlexT.wideFlexT.M k.val) := by
  have hlamlt : ∀ i : Fin 4, (Expression.eval env lam2[i.val]).val < 2 ^ 64 :=
    digit_lt_of_norm env lam2 hlam
  have hxdlt : ∀ i : Fin 4, (Expression.eval env
      (Vector.ofFn fun j : Fin 4 =>
        xT2[j.val]'j.isLt + ((2 ^ 64 - 1 : ℕ) : F circomPrime) - x2[j.val]'j.isLt)[i.val]).val < 2 ^ 65 := by
    intro i; rw [Vector.getElem_ofFn]; exact eval_xd_lt env xT2 x2 hxT2 hx2 i.val i.isLt
  have hq7d := digit_lt_of_norm' env q7 hq7
  have hq7t64 : (Expression.eval env q7t).val < 2 ^ 64 := by omega
  constructor
  · intro k
    rw [Vector.getElem_map, Vector.getElem_mapFinRange]
    by_cases hk7 : k.val < 7
    · rw [boundAt_wideFlexT_lo k hk7]
      have hA : (Expression.eval env (if h : k.val < 7 then P[k.val]'h else 0)).val < 4 * 2 ^ 129 := by
        rw [dif_pos hk7, hP ⟨k.val, hk7⟩]
        exact val_convLX_lt env lam2 _ ⟨k.val, hk7⟩ (fun i => hlamlt i) hxdlt
      have hC : (Expression.eval env (if k.val < 5 then cExp (2 ^ 35 * P256) k.val else 0)).val < 2 ^ 64 := by
        by_cases hk : k.val < 5
        · rw [if_pos hk, eval_cExp, val_limbOfNat]; exact limbOfNat_lt _ _
        · rw [if_neg hk, show Expression.eval env (0 : Expression (F circomPrime)) = 0 from rfl,
            ZMod.val_zero]; positivity
      have hle := ZMod.val_add_le (Expression.eval env (if h : k.val < 7 then P[k.val]'h else 0))
        (Expression.eval env (if k.val < 5 then cExp (2 ^ 35 * P256) k.val else 0))
      rw [show Expression.eval env
            ((if h : k.val < 7 then P[k.val]'h else 0)
              + (if k.val < 5 then cExp (2 ^ 35 * P256) k.val else 0))
          = Expression.eval env (if h : k.val < 7 then P[k.val]'h else 0)
            + Expression.eval env (if k.val < 5 then cExp (2 ^ 35 * P256) k.val else 0) from rfl]
      omega
    · rw [boundAt_wideFlexT_hi k (by omega),
        show Expression.eval env
            ((if h : k.val < 7 then P[k.val]'h else 0)
              + (if k.val < 5 then cExp (2 ^ 35 * P256) k.val else 0))
          = Expression.eval env (if h : k.val < 7 then P[k.val]'h else 0)
            + Expression.eval env (if k.val < 5 then cExp (2 ^ 35 * P256) k.val else 0) from rfl,
        dif_neg hk7, if_neg (show ¬ k.val < 5 by omega),
        show Expression.eval env (0 : Expression (F circomPrime)) = 0 from rfl, add_zero,
        ZMod.val_zero]
      positivity
  · intro k
    rw [Vector.getElem_map, Vector.getElem_mapFinRange]
    have hg : (Expression.eval env (if h : k.val < 4 then
        y3[k.val]'h + yT2[k.val]'h
          + (((c976 : ℕ) : F circomPrime) : Expression (F circomPrime)) * (lam2[k.val]'h) else 0)).val
        < 2 ^ 98 := by
      by_cases hk : k.val < 4
      · rw [dif_pos hk, val_affine3 env _ _ _ _ (digit_lt_of_norm' env y3 hy3 k.val hk)
          (digit_lt_of_norm' env yT2 hyT2 k.val hk) (digit_lt_of_norm' env lam2 hlam k.val hk)
          (by decide : c976 < 2 ^ 33)]
        have h1 := digit_lt_of_norm' env y3 hy3 k.val hk
        have h2 := digit_lt_of_norm' env yT2 hyT2 k.val hk
        have h3 := digit_lt_of_norm' env lam2 hlam k.val hk
        have h4 : c976 * (Expression.eval env lam2[k.val]).val < 2 ^ 33 * 2 ^ 64 :=
          Nat.mul_lt_mul'' (by decide) h3
        have h5 : (2:ℕ) ^ 33 * 2 ^ 64 < 2 ^ 98 := by norm_num
        omega
      · rw [dif_neg hk, show Expression.eval env (0 : Expression (F circomPrime)) = 0 from rfl,
          ZMod.val_zero]; positivity
    have hle := ZMod.val_add_le (Expression.eval env (qpCoeff q7 q7t k.val))
      (Expression.eval env (if h : k.val < 4 then
        y3[k.val]'h + yT2[k.val]'h
          + (((c976 : ℕ) : F circomPrime) : Expression (F circomPrime)) * (lam2[k.val]'h) else 0))
    rw [show Expression.eval env
          (qpCoeff q7 q7t k.val + (if h : k.val < 4 then
            y3[k.val]'h + yT2[k.val]'h
              + (((c976 : ℕ) : F circomPrime) : Expression (F circomPrime)) * (lam2[k.val]'h) else 0))
        = Expression.eval env (qpCoeff q7 q7t k.val)
          + Expression.eval env (if h : k.val < 4 then
              y3[k.val]'h + yT2[k.val]'h
                + (((c976 : ℕ) : F circomPrime) : Expression (F circomPrime)) * (lam2[k.val]'h) else 0)
        from rfl]
    by_cases hk7 : k.val < 7
    · rw [boundAt_wideFlexT_lo k hk7]
      have hqp := val_qpCoeff_lt env q7 q7t k.val hq7d hq7t64
      omega
    · rw [boundAt_wideFlexT_hi k (by omega)]
      have hg0 : (Expression.eval env (if h : k.val < 4 then
          y3[k.val]'h + yT2[k.val]'h
            + (((c976 : ℕ) : F circomPrime) : Expression (F circomPrime)) * (lam2[k.val]'h) else 0)).val
          = 0 := by
        rw [dif_neg (show ¬ k.val < 4 by omega),
          show Expression.eval env (0 : Expression (F circomPrime)) = 0 from rfl, ZMod.val_zero]
      have hqp := val_qpCoeff_tail env q7 q7t k.val (by omega) hq7d hq7t
      omega

/-! ### §BORROW-ROLLOUT: fat-limb C1 lemmas (`d2 → dtilOf xT2 x1`)

Mirrors of `polyValue_c1_lhs`/`c1_identity`/`c1_fp`/`c1_discharge` with the
`d2`/`d24`/`lp2` machinery deleted: `P2 = lam2 ⊛ dtil2` (fat limbs, coeff
`< 12·2^128`) sits next to `P1 = lam1 ⊛ xd1` (`< 8·2^128`) under the widened
`vWideFat` tent (`21·2^128`). -/

set_option maxRecDepth 4000 in
lemma polyValue_c1_lhs_fat (env : Environment (F circomPrime))
    (lam2 dtil2 lam1 xA x1 : Var Emu (F circomPrime))
    (P2 P1 : Vector (Expression (F circomPrime)) 7)
    (hP2 : ∀ k : Fin 7,
      Expression.eval env P2[k.val] = Expression.eval env (bigIntMulNoReduce lam2 dtil2)[k.val])
    (hP1 : ∀ k : Fin 7,
      Expression.eval env P1[k.val] = Expression.eval env (bigIntMulNoReduce lam1
        (Vector.ofFn fun i : Fin 4 =>
          xA[i.val]'i.isLt + ((2 ^ 64 - 1 : ℕ) : F circomPrime) - x1[i.val]'i.isLt))[k.val])
    (hlam2 : BigInt.Normalized 64 (Vector.map (Expression.eval env) lam2))
    (hdtil2 : ∀ i : Fin 4, (Expression.eval env dtil2[i.val]).val < 3 * 2 ^ 64)
    (hlam1 : BigInt.Normalized 64 (Vector.map (Expression.eval env) lam1))
    (hxA : BigInt.Normalized 64 (Vector.map (Expression.eval env) xA))
    (hx1 : BigInt.Normalized 64 (Vector.map (Expression.eval env) x1)) :
    polyValue 64 (Vector.map (Expression.eval env)
        (Vector.mapFinRange 10 fun k =>
          (if h : k.val < 7 then P2[k.val]'h + P1[k.val]'h else 0)
            + (if k.val < 5 then cExp (2 ^ 34 * P256) k.val else 0)))
      = BigInt.value 64 (Vector.map (Expression.eval env) lam2)
          * (∑ j : Fin 4, (Expression.eval env dtil2[j.val]).val * 2 ^ (64 * j.val))
        + BigInt.value 64 (Vector.map (Expression.eval env) lam1)
          * (∑ j : Fin 4, (Expression.eval env
              (xA[j.val]'j.isLt + ((2 ^ 64 - 1 : ℕ) : F circomPrime) - x1[j.val]'j.isLt)).val
                * 2 ^ (64 * j.val))
        + 2 ^ 34 * P256 := by
  have hlam1lt : ∀ i : Fin 4, (Expression.eval env lam1[i.val]).val < 2 ^ 64 :=
    digit_lt_of_norm env lam1 hlam1
  have hlam2lt : ∀ i : Fin 4, (Expression.eval env lam2[i.val]).val < 2 ^ 64 :=
    digit_lt_of_norm env lam2 hlam2
  have hxdlt : ∀ i : Fin 4, (Expression.eval env
      (Vector.ofFn fun j : Fin 4 =>
        xA[j.val]'j.isLt + ((2 ^ 64 - 1 : ℕ) : F circomPrime) - x1[j.val]'j.isLt)[i.val]).val < 2 ^ 65 := by
    intro i; rw [Vector.getElem_ofFn]; exact eval_xd_lt env xA x1 hxA hx1 i.val i.isLt

  have hpv2 : polyValue 64 (Vector.map (Expression.eval env) P2)
      = BigInt.value 64 (Vector.map (Expression.eval env) lam2)
        * (∑ j : Fin 4, (Expression.eval env dtil2[j.val]).val * 2 ^ (64 * j.val)) := by
    have hconv : polyValue 64 (Vector.map (Expression.eval env) P2)
        = polyValue 64 (Vector.map (Expression.eval env) (bigIntMulNoReduce lam2 dtil2)) := by
      simp only [polyValue, Vector.getElem_map]
      apply Finset.sum_congr rfl; intro i _; rw [hP2 i]
    rw [hconv, polyValue64_conv_fat env lam2 dtil2 hlam2lt hdtil2, ← MulMod.value_map_eval env lam2]
  have hpv1 : polyValue 64 (Vector.map (Expression.eval env) P1)
      = BigInt.value 64 (Vector.map (Expression.eval env) lam1)
        * (∑ j : Fin 4, (Expression.eval env
            (xA[j.val]'j.isLt + ((2 ^ 64 - 1 : ℕ) : F circomPrime) - x1[j.val]'j.isLt)).val
              * 2 ^ (64 * j.val)) := by
    have hconv : polyValue 64 (Vector.map (Expression.eval env) P1)
        = polyValue 64 (Vector.map (Expression.eval env) (bigIntMulNoReduce lam1
            (Vector.ofFn fun j : Fin 4 =>
              xA[j.val]'j.isLt + ((2 ^ 64 - 1 : ℕ) : F circomPrime) - x1[j.val]'j.isLt))) := by
      simp only [polyValue, Vector.getElem_map]
      apply Finset.sum_congr rfl; intro i _; rw [hP1 i]
    rw [hconv, polyValue64_conv env lam1 _
      (fun i => lt_trans (hlam1lt i) (by norm_num)) hxdlt, ← MulMod.value_map_eval env lam1]
    refine congrArg (BigInt.value 64 (Vector.map (Expression.eval env) lam1) * ·) ?_
    exact Finset.sum_congr rfl fun j _ => by rw [Vector.getElem_ofFn]
  rw [polyValue10_split env
    (fun k => if h : k.val < 7 then P2[k.val]'h + P1[k.val]'h else 0)
    (fun k => if k.val < 5 then cExp (2 ^ 34 * P256) k.val else 0) (by
      intro k
      dsimp only
      have hA : (Expression.eval env (if h : k.val < 7 then P2[k.val]'h + P1[k.val]'h else 0)).val
          < 20 * 2 ^ 128 := by
        by_cases hk : k.val < 7
        · rw [dif_pos hk]
          have h2 : (Expression.eval env (P2[k.val]'hk)).val < 4 * (2 ^ 64 * (3 * 2 ^ 64)) := by
            rw [hP2 ⟨k.val, hk⟩]
            exact val_conv_lam_dtil_lt env lam2 dtil2 ⟨k.val, hk⟩ hlam2lt hdtil2
          have h1 : (Expression.eval env (P1[k.val]'hk)).val < 4 * 2 ^ 129 := by
            rw [hP1 ⟨k.val, hk⟩]
            exact val_convLX_lt env lam1 _ ⟨k.val, hk⟩ (fun i => hlam1lt i) hxdlt
          have hle := ZMod.val_add_le (Expression.eval env (P2[k.val]'hk))
            (Expression.eval env (P1[k.val]'hk))
          rw [show Expression.eval env (P2[k.val]'hk + P1[k.val]'hk)
              = Expression.eval env (P2[k.val]'hk) + Expression.eval env (P1[k.val]'hk) from rfl]
          have hs : (4:ℕ) * (2 ^ 64 * (3 * 2 ^ 64)) + 4 * 2 ^ 129 = 20 * 2 ^ 128 := by norm_num
          omega
        · rw [dif_neg hk, show Expression.eval env (0 : Expression (F circomPrime)) = 0 from rfl,
            ZMod.val_zero]; positivity
      have hC : (Expression.eval env (if k.val < 5 then cExp (2 ^ 34 * P256) k.val else 0)).val < 2 ^ 64 := by
        by_cases hk : k.val < 5
        · rw [if_pos hk, eval_cExp, val_limbOfNat]; exact limbOfNat_lt _ _
        · rw [if_neg hk, show Expression.eval env (0 : Expression (F circomPrime)) = 0 from rfl,
            ZMod.val_zero]; positivity
      have hpr : 20 * 2 ^ 128 + 2 ^ 64 < circomPrime := by decide
      omega)]
  dsimp only
  rw [polyValue_pad10_7_add env P2 P1 (by
      intro k
      have h2 : (Expression.eval env (P2[k.val]'k.isLt)).val < 4 * (2 ^ 64 * (3 * 2 ^ 64)) := by
        rw [hP2 k]
        exact val_conv_lam_dtil_lt env lam2 dtil2 k hlam2lt hdtil2
      have h1 : (Expression.eval env (P1[k.val]'k.isLt)).val < 4 * 2 ^ 129 := by
        rw [hP1 k]; exact val_convLX_lt env lam1 _ k (fun i => hlam1lt i) hxdlt
      have hpr : 4 * (2 ^ 64 * (3 * 2 ^ 64)) + 4 * 2 ^ 129 < circomPrime := by decide
      omega),
    polyValue_pad10_cExp env (2 ^ 34 * P256) (by
      have h : P256 < 2 ^ 256 := P256_lt
      have e1 : (2:ℕ) ^ 34 * 2 ^ 256 = 2 ^ 290 := by rw [← pow_add]
      have e2 : (2:ℕ) ^ 290 ≤ 2 ^ 320 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
      have e3 : 2 ^ 34 * P256 < 2 ^ 34 * 2 ^ 256 := Nat.mul_lt_mul_of_pos_left h (by positivity)
      omega),
    hpv2, hpv1]

set_option maxRecDepth 4000 in
lemma c1_fp_fat (env : Environment (F circomPrime))
    (lam2 dtil2 lam1 xA x1 yT2 yA q3 : Var Emu (F circomPrime)) (q3t : Expression (F circomPrime))
    (P2 P1 : Vector (Expression (F circomPrime)) 7)
    (hP2 : ∀ k : Fin 7,
      Expression.eval env P2[k.val] = Expression.eval env (bigIntMulNoReduce lam2 dtil2)[k.val])
    (hP1 : ∀ k : Fin 7,
      Expression.eval env P1[k.val] = Expression.eval env (bigIntMulNoReduce lam1
        (Vector.ofFn fun i : Fin 4 =>
          xA[i.val]'i.isLt + ((2 ^ 64 - 1 : ℕ) : F circomPrime) - x1[i.val]'i.isLt))[k.val])
    (hlam2 : BigInt.Normalized 64 (Vector.map (Expression.eval env) lam2))
    (hdtil2 : ∀ i : Fin 4, (Expression.eval env dtil2[i.val]).val < 3 * 2 ^ 64)
    (hlam1 : BigInt.Normalized 64 (Vector.map (Expression.eval env) lam1))
    (hxA : BigInt.Normalized 64 (Vector.map (Expression.eval env) xA))
    (hx1 : BigInt.Normalized 64 (Vector.map (Expression.eval env) x1))
    (hyT2 : BigInt.Normalized 64 (Vector.map (Expression.eval env) yT2))
    (hyA : BigInt.Normalized 64 (Vector.map (Expression.eval env) yA))
    (hq3 : BigInt.Normalized 64 (Vector.map (Expression.eval env) q3))
    (hq3t : (Expression.eval env q3t).val < 2 ^ 64)
    (hspec : polyValue 64 (Vector.map (Expression.eval env)
          (Vector.mapFinRange 10 fun k =>
            (if h : k.val < 7 then P2[k.val]'h + P1[k.val]'h else 0)
              + (if k.val < 5 then cExp (2 ^ 34 * P256) k.val else 0)))
        = polyValue 64 (Vector.map (Expression.eval env)
          (Vector.mapFinRange 10 fun k =>
            qpCoeff q3 q3t k.val
              + (if h : k.val < 4 then
                  yT2[k.val]'h + yA[k.val]'h + ((c976 : ℕ) : F circomPrime) * (lam1[k.val]'h) else 0)))) :
    ((∑ j : Fin 4, (Expression.eval env dtil2[j.val]).val * 2 ^ (64 * j.val) : ℕ)
        : Specs.Secp256k1.Fp)
        * decodeFe (Vector.map (Expression.eval env) lam2)
      + decodeFe (Vector.map (Expression.eval env) lam1)
        * (decodeFe (Vector.map (Expression.eval env) xA)
          - decodeFe (Vector.map (Expression.eval env) x1))
      = decodeFe (Vector.map (Expression.eval env) yT2)
        + decodeFe (Vector.map (Expression.eval env) yA) := by
  have hL := polyValue_c1_lhs_fat env lam2 dtil2 lam1 xA x1 P2 P1 hP2 hP1 hlam2 hdtil2 hlam1 hxA hx1
  have hR := polyValue_c2b_rhs env q3 q3t yT2 yA lam1 hq3 hq3t hyT2 hyA hlam1
  have hnat := hL.symm.trans (hspec.trans hR)
  have hxd := xd_value env xA x1 hxA hx1
  rw [show (2 ^ 256 - 1 : ℕ) = c976 + P256 from by
    norm_num [c976, P256, Specs.Secp256k1.p]] at hxd
  have hc1 := congrArg (Nat.cast : ℕ → Specs.Secp256k1.Fp) hnat
  have hc2 := congrArg (Nat.cast : ℕ → Specs.Secp256k1.Fp) hxd
  push_cast at hc1 hc2
  rw [show ((P256 : ℕ) : Specs.Secp256k1.Fp) = 0 from ZMod.natCast_self _] at hc1 hc2
  simp only [decodeFe, limbBits]
  push_cast
  linear_combination hc1 - (↑(BigInt.value 64 (Vector.map (Expression.eval env) lam1))
      : Specs.Secp256k1.Fp) * hc2

lemma c1_discharge_fat (env : Environment (F circomPrime))
    (lam2 dtil2 lam1 xA x1 yT2 yA q3 : Var Emu (F circomPrime)) (q3t : Expression (F circomPrime))
    (P2 P1 : Vector (Expression (F circomPrime)) 7)
    (hP2 : ∀ k : Fin 7,
      Expression.eval env P2[k.val] = Expression.eval env (bigIntMulNoReduce lam2 dtil2)[k.val])
    (hP1 : ∀ k : Fin 7,
      Expression.eval env P1[k.val] = Expression.eval env (bigIntMulNoReduce lam1
        (Vector.ofFn fun i : Fin 4 =>
          xA[i.val]'i.isLt + ((2 ^ 64 - 1 : ℕ) : F circomPrime) - x1[i.val]'i.isLt))[k.val])
    (hlam2 : BigInt.Normalized 64 (Vector.map (Expression.eval env) lam2))
    (hdtil2 : ∀ i : Fin 4, (Expression.eval env dtil2[i.val]).val < 3 * 2 ^ 64)
    (hlam1 : BigInt.Normalized 64 (Vector.map (Expression.eval env) lam1))
    (hxA : BigInt.Normalized 64 (Vector.map (Expression.eval env) xA))
    (hx1 : BigInt.Normalized 64 (Vector.map (Expression.eval env) x1))
    (hyT2 : BigInt.Normalized 64 (Vector.map (Expression.eval env) yT2))
    (hyA : BigInt.Normalized 64 (Vector.map (Expression.eval env) yA))
    (hq3 : BigInt.Normalized 64 (Vector.map (Expression.eval env) q3))
    (hq3t : (Expression.eval env q3t).val < 2 ^ 3) :
    (∀ k : Fin 10,
        ((Vector.map (Expression.eval env)
          (Vector.mapFinRange 10 fun k =>
            (if h : k.val < 7 then P2[k.val]'h + P1[k.val]'h else 0)
              + (if k.val < 5 then cExp (2 ^ 34 * P256) k.val else 0)))[k.val]).val
        < vWideFat.Nf k.val)
    ∧ (∀ k : Fin 10,
        ((Vector.map (Expression.eval env)
          (Vector.mapFinRange 10 fun k =>
            qpCoeff q3 q3t k.val
              + (if h : k.val < 4 then
                  yT2[k.val]'h + yA[k.val]'h + ((c976 : ℕ) : F circomPrime) * (lam1[k.val]'h) else 0)))[k.val]).val
        < vWideFat.Nf k.val) := by
  have hlam1lt : ∀ i : Fin 4, (Expression.eval env lam1[i.val]).val < 2 ^ 64 :=
    digit_lt_of_norm env lam1 hlam1
  have hlam2lt : ∀ i : Fin 4, (Expression.eval env lam2[i.val]).val < 2 ^ 64 :=
    digit_lt_of_norm env lam2 hlam2
  have hxdlt : ∀ i : Fin 4, (Expression.eval env
      (Vector.ofFn fun j : Fin 4 =>
        xA[j.val]'j.isLt + ((2 ^ 64 - 1 : ℕ) : F circomPrime) - x1[j.val]'j.isLt)[i.val]).val < 2 ^ 65 := by
    intro i; rw [Vector.getElem_ofFn]; exact eval_xd_lt env xA x1 hxA hx1 i.val i.isLt
  have hq3d := digit_lt_of_norm' env q3 hq3
  have hq3t64 : (Expression.eval env q3t).val < 2 ^ 64 := by omega
  constructor
  · intro k
    rw [Vector.getElem_map, Vector.getElem_mapFinRange]
    have hC : (Expression.eval env (if k.val < 5 then cExp (2 ^ 34 * P256) k.val else 0)).val < 2 ^ 64 := by
      by_cases hk : k.val < 5
      · rw [if_pos hk, eval_cExp, val_limbOfNat]; exact limbOfNat_lt _ _
      · rw [if_neg hk, show Expression.eval env (0 : Expression (F circomPrime)) = 0 from rfl,
          ZMod.val_zero]; positivity
    have hle := ZMod.val_add_le
      (Expression.eval env (if h : k.val < 7 then P2[k.val]'h + P1[k.val]'h else 0))
      (Expression.eval env (if k.val < 5 then cExp (2 ^ 34 * P256) k.val else 0))
    rw [show Expression.eval env
          ((if h : k.val < 7 then P2[k.val]'h + P1[k.val]'h else 0)
            + (if k.val < 5 then cExp (2 ^ 34 * P256) k.val else 0))
        = Expression.eval env (if h : k.val < 7 then P2[k.val]'h + P1[k.val]'h else 0)
          + Expression.eval env (if k.val < 5 then cExp (2 ^ 34 * P256) k.val else 0) from rfl]
    by_cases hk7 : k.val < 7
    · rw [vWideFat_Nf_lo k hk7]
      have hA : (Expression.eval env (if h : k.val < 7 then P2[k.val]'h + P1[k.val]'h else 0)).val
          < 20 * 2 ^ 128 := by
        rw [dif_pos hk7]
        have h2 : (Expression.eval env (P2[k.val]'hk7)).val < 4 * (2 ^ 64 * (3 * 2 ^ 64)) := by
          rw [hP2 ⟨k.val, hk7⟩]
          exact val_conv_lam_dtil_lt env lam2 dtil2 ⟨k.val, hk7⟩ hlam2lt hdtil2
        have h1 : (Expression.eval env (P1[k.val]'hk7)).val < 4 * 2 ^ 129 := by
          rw [hP1 ⟨k.val, hk7⟩]; exact val_convLX_lt env lam1 _ ⟨k.val, hk7⟩ (fun i => hlam1lt i) hxdlt
        have hle2 := ZMod.val_add_le (Expression.eval env (P2[k.val]'hk7))
          (Expression.eval env (P1[k.val]'hk7))
        rw [show Expression.eval env (P2[k.val]'hk7 + P1[k.val]'hk7)
            = Expression.eval env (P2[k.val]'hk7) + Expression.eval env (P1[k.val]'hk7) from rfl]
        have hs : (4:ℕ) * (2 ^ 64 * (3 * 2 ^ 64)) + 4 * 2 ^ 129 = 20 * 2 ^ 128 := by norm_num
        omega
      have hconcrete : (20:ℕ) * 2 ^ 128 + 2 ^ 64 < 21 * 2 ^ 128 := by decide
      omega
    · rw [vWideFat_Nf_hi k (by omega)]
      have hA0 : (Expression.eval env (if h : k.val < 7 then P2[k.val]'h + P1[k.val]'h else 0)).val = 0 := by
        rw [dif_neg hk7, show Expression.eval env (0 : Expression (F circomPrime)) = 0 from rfl,
          ZMod.val_zero]
      have hC0 : (Expression.eval env (if k.val < 5 then cExp (2 ^ 34 * P256) k.val else 0)).val = 0 := by
        rw [if_neg (show ¬ k.val < 5 by omega),
          show Expression.eval env (0 : Expression (F circomPrime)) = 0 from rfl, ZMod.val_zero]
      omega
  · intro k
    rw [Vector.getElem_map, Vector.getElem_mapFinRange]
    have hg : (Expression.eval env (if h : k.val < 4 then
        yT2[k.val]'h + yA[k.val]'h
          + (((c976 : ℕ) : F circomPrime) : Expression (F circomPrime)) * (lam1[k.val]'h) else 0)).val
        < 2 ^ 98 := by
      by_cases hk : k.val < 4
      · rw [dif_pos hk, val_affine3 env _ _ _ _ (digit_lt_of_norm' env yT2 hyT2 k.val hk)
          (digit_lt_of_norm' env yA hyA k.val hk) (digit_lt_of_norm' env lam1 hlam1 k.val hk)
          (by decide : c976 < 2 ^ 33)]
        have h1 := digit_lt_of_norm' env yT2 hyT2 k.val hk
        have h2 := digit_lt_of_norm' env yA hyA k.val hk
        have h3 := digit_lt_of_norm' env lam1 hlam1 k.val hk
        have h4 : c976 * (Expression.eval env lam1[k.val]).val < 2 ^ 33 * 2 ^ 64 :=
          Nat.mul_lt_mul'' (by decide) h3
        have h5 : (2:ℕ) ^ 33 * 2 ^ 64 < 2 ^ 98 := by norm_num
        omega
      · rw [dif_neg hk, show Expression.eval env (0 : Expression (F circomPrime)) = 0 from rfl,
          ZMod.val_zero]; positivity
    have hle := ZMod.val_add_le (Expression.eval env (qpCoeff q3 q3t k.val))
      (Expression.eval env (if h : k.val < 4 then
        yT2[k.val]'h + yA[k.val]'h
          + (((c976 : ℕ) : F circomPrime) : Expression (F circomPrime)) * (lam1[k.val]'h) else 0))
    rw [show Expression.eval env
          (qpCoeff q3 q3t k.val + (if h : k.val < 4 then
            yT2[k.val]'h + yA[k.val]'h
              + (((c976 : ℕ) : F circomPrime) : Expression (F circomPrime)) * (lam1[k.val]'h) else 0))
        = Expression.eval env (qpCoeff q3 q3t k.val)
          + Expression.eval env (if h : k.val < 4 then
              yT2[k.val]'h + yA[k.val]'h
                + (((c976 : ℕ) : F circomPrime) : Expression (F circomPrime)) * (lam1[k.val]'h) else 0)
        from rfl]
    by_cases hk7 : k.val < 7
    · rw [vWideFat_Nf_lo k hk7]
      have hqp := val_qpCoeff_lt env q3 q3t k.val hq3d hq3t64
      omega
    · rw [vWideFat_Nf_hi k (by omega)]
      have hg0 : (Expression.eval env (if h : k.val < 4 then
          yT2[k.val]'h + yA[k.val]'h
            + (((c976 : ℕ) : F circomPrime) : Expression (F circomPrime)) * (lam1[k.val]'h) else 0)).val
          = 0 := by
        rw [dif_neg (show ¬ k.val < 4 by omega),
          show Expression.eval env (0 : Expression (F circomPrime)) = 0 from rfl, ZMod.val_zero]
      have hqp := val_qpCoeff_tail env q3 q3t k.val (by omega) hq3d hq3t
      omega

end PairAdd
end Solution.Secp256k1ScalarMulFixedBase

end DonorFile2_2

-- Adapted donor module: PairAddCompleteTheorems
section DonorFile2_3

namespace Solution.Secp256k1ScalarMulFixedBase
open Solution.Secp256k1ScalarMulFixedBase.Limbs
namespace PairAdd
open CompactAdd (cExp qpCoeff c976 cK)
open CompactAdd (invModP dFullVal chVal lamVal lamValEnv x3Val x3Quot slopeQuot)

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

lemma quot_recompose (q : ℕ) : (q % 2 ^ 256) + (q / 2 ^ 256) * 2 ^ 256 = q := by
  rw [Nat.add_comm]; exact Nat.div_add_mod' q (2 ^ 256)

lemma two_pow255_lt_P256 : (2:ℕ) ^ 255 < P256 := by decide

lemma evalEmu_eq_value (env : ProverEnvironment (F circomPrime)) (v : Var Emu (F circomPrime)) :
    evalEmu env v
      = BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) v) := by
  rfl

lemma div_div_lt (n a b c : ℕ) (hab : 0 < a * b) (h : n < c * (a * b)) :
    n / a / b < c := by
  rw [Nat.div_div_eq_div_mul]
  exact (Nat.div_lt_iff_lt_mul hab).mpr h

lemma P256_lt256 : P256 < 2 ^ 256 := by
  have := CompleteAdd.P256_lt; simpa [limbBits, numLimbs] using this

lemma dFullVal_lt (env : ProverEnvironment (F circomPrime)) (xT xA : Var Emu (F circomPrime))
    (hxT : evalEmu env xT < 2 ^ 256) :
    CompactAdd.dFullVal env xT xA < 4 * 2 ^ 256 := by
  have hP := P256_lt256
  unfold CompactAdd.dFullVal
  omega

lemma d4_bound (env : ProverEnvironment (F circomPrime)) (xT xA : Var Emu (F circomPrime))
    (hxT : evalEmu env xT < 2 ^ 256) :
    CompactAdd.dFullVal env xT xA / 2 ^ 256 < 2 ^ 2 := by
  have h := dFullVal_lt env xT xA hxT
  rw [show (2:ℕ) ^ 2 = 4 from rfl]
  exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h)


lemma dblock_spec_complete (env : Environment (F circomPrime))
    (d xA xT : Var Emu (F circomPrime)) (d4 : Expression (F circomPrime))
    (hd : BigInt.Normalized 64 (Vector.map (Expression.eval env) d))
    (hxA : BigInt.Normalized 64 (Vector.map (Expression.eval env) xA))
    (hxT : BigInt.Normalized 64 (Vector.map (Expression.eval env) xT))
    (hdfull : BigInt.value 64 (Vector.map (Expression.eval env) d)
        + (Expression.eval env d4).val * 2 ^ 256
      = 2 * P256 + BigInt.value 64 (Vector.map (Expression.eval env) xT)
        - BigInt.value 64 (Vector.map (Expression.eval env) xA)) :
    polyValue 64 (Vector.map (Expression.eval env)
        (Vector.mapFinRange 5 fun k => if h : k.val < 4 then d[k.val]'h + xA[k.val]'h else d4))
      = polyValue 64 (Vector.map (Expression.eval env)
          (Vector.mapFinRange 5 fun k =>
            if h : k.val < 4 then xT[k.val]'h + cExp (2 * P256) k.val else cExp (2 * P256) 4)) := by
  rw [polyValue_dblock_lhs env d xA d4 hd hxA, polyValue_dblock_rhs env xT hxT]
  have hxAlt : BigInt.value 64 (Vector.map (Expression.eval env) xA) < 2 ^ 256 :=
    BigInt.value_lt hxA
  have hP := two_pow255_lt_P256
  have h256 : (2:ℕ) ^ 256 = 2 ^ 255 * 2 := by ring
  omega

lemma o2_spec_complete (env : Environment (F circomPrime))
    (lam1 x1 xA xT1 q6 : Var Emu (F circomPrime)) (q6t : Expression (F circomPrime))
    (P : Vector (Expression (F circomPrime)) 7)
    (hP : ∀ k : Fin 7,
      Expression.eval env P[k.val] = Expression.eval env (bigIntMulNoReduce lam1 lam1)[k.val])
    (hlam : BigInt.Normalized 64 (Vector.map (Expression.eval env) lam1))
    (hx1 : BigInt.Normalized 64 (Vector.map (Expression.eval env) x1))
    (hxA : BigInt.Normalized 64 (Vector.map (Expression.eval env) xA))
    (hxT1 : BigInt.Normalized 64 (Vector.map (Expression.eval env) xT1))
    (hq6 : BigInt.Normalized 64 (Vector.map (Expression.eval env) q6))
    (hq6t : (Expression.eval env q6t).val < 2 ^ 64)
    (hx1v : BigInt.value 64 (Vector.map (Expression.eval env) x1)
      = (BigInt.value 64 (Vector.map (Expression.eval env) lam1)
          * BigInt.value 64 (Vector.map (Expression.eval env) lam1) + 4 * P256
        - BigInt.value 64 (Vector.map (Expression.eval env) xA)
        - BigInt.value 64 (Vector.map (Expression.eval env) xT1)) % P256)
    (hqv : BigInt.value 64 (Vector.map (Expression.eval env) q6)
        + (Expression.eval env q6t).val * 2 ^ 256
      = (BigInt.value 64 (Vector.map (Expression.eval env) lam1)
          * BigInt.value 64 (Vector.map (Expression.eval env) lam1) + 4 * P256
        - BigInt.value 64 (Vector.map (Expression.eval env) xA)
        - BigInt.value 64 (Vector.map (Expression.eval env) xT1)) / P256) :
    polyValue 64 (Vector.map (Expression.eval env)
        (Vector.mapFinRange 9 fun k =>
          (if h : k.val < 7 then P[k.val]'h else 0)
            + (if k.val < 5 then cExp (4 * P256) k.val else 0)))
      = polyValue 64 (Vector.map (Expression.eval env)
          (Vector.mapFinRange 9 fun k =>
            qpCoeff q6 q6t k.val
              + (if h : k.val < 4 then x1[k.val]'h + xA[k.val]'h + xT1[k.val]'h else 0))) := by
  rw [polyValue_o2_lhs env lam1 P hP hlam,
      polyValue_o2_rhs env q6 q6t x1 xA xT1 hq6 hq6t hx1 hxA hxT1]
  have hxAlt : BigInt.value 64 (Vector.map (Expression.eval env) xA) < 2 ^ 256 :=
    BigInt.value_lt hxA
  have hxT1lt : BigInt.value 64 (Vector.map (Expression.eval env) xT1) < 2 ^ 256 :=
    BigInt.value_lt hxT1
  set lv := BigInt.value 64 (Vector.map (Expression.eval env) lam1)
  set vA := BigInt.value 64 (Vector.map (Expression.eval env) xA)
  set vT1 := BigInt.value 64 (Vector.map (Expression.eval env) xT1)
  set N := lv * lv + 4 * P256 - vA - vT1 with hN
  rw [hqv, hx1v]
  have hP256 : (2:ℕ) ^ 256 < P256 * 2 := by decide
  have hbound : vA + vT1 ≤ lv * lv + 4 * P256 := by
    have : (4:ℕ) * P256 > 2 * 2 ^ 256 := by decide
    omega
  have hdm := Nat.div_add_mod' N P256
  show lv * lv + 4 * P256 = (N / P256) * P256 + N % P256 + vA + vT1
  omega

lemma c2b_spec_complete (env : Environment (F circomPrime))
    (lam2 xT2 x2 y3 yT2 q7 : Var Emu (F circomPrime)) (q7t : Expression (F circomPrime))
    (P : Vector (Expression (F circomPrime)) 7)
    (hP : ∀ k : Fin 7, Expression.eval env P[k.val]
      = Expression.eval env (bigIntMulNoReduce lam2
          (Vector.ofFn fun i : Fin 4 =>
            xT2[i.val]'i.isLt + ((2 ^ 64 - 1 : ℕ) : F circomPrime) - x2[i.val]'i.isLt))[k.val])
    (hlam : BigInt.Normalized 64 (Vector.map (Expression.eval env) lam2))
    (hxT2 : BigInt.Normalized 64 (Vector.map (Expression.eval env) xT2))
    (hx2 : BigInt.Normalized 64 (Vector.map (Expression.eval env) x2))
    (hy3 : BigInt.Normalized 64 (Vector.map (Expression.eval env) y3))
    (hyT2 : BigInt.Normalized 64 (Vector.map (Expression.eval env) yT2))
    (hq7 : BigInt.Normalized 64 (Vector.map (Expression.eval env) q7))
    (hq7t : (Expression.eval env q7t).val < 2 ^ 64)
    (hy3v : BigInt.value 64 (Vector.map (Expression.eval env) y3)
      = (BigInt.value 64 (Vector.map (Expression.eval env) lam2)
          * (BigInt.value 64 (Vector.map (Expression.eval env) xT2) + (2 ^ 256 - 1)
              - BigInt.value 64 (Vector.map (Expression.eval env) x2))
        + 2 ^ 35 * P256 - BigInt.value 64 (Vector.map (Expression.eval env) yT2)
        - c976 * BigInt.value 64 (Vector.map (Expression.eval env) lam2)) % P256)
    (hqv : BigInt.value 64 (Vector.map (Expression.eval env) q7)
        + (Expression.eval env q7t).val * 2 ^ 256
      = (BigInt.value 64 (Vector.map (Expression.eval env) lam2)
          * (BigInt.value 64 (Vector.map (Expression.eval env) xT2) + (2 ^ 256 - 1)
              - BigInt.value 64 (Vector.map (Expression.eval env) x2))
        + 2 ^ 35 * P256 - BigInt.value 64 (Vector.map (Expression.eval env) yT2)
        - c976 * BigInt.value 64 (Vector.map (Expression.eval env) lam2)) / P256)
    (hbound : BigInt.value 64 (Vector.map (Expression.eval env) yT2)
        + c976 * BigInt.value 64 (Vector.map (Expression.eval env) lam2)
      ≤ BigInt.value 64 (Vector.map (Expression.eval env) lam2)
          * (BigInt.value 64 (Vector.map (Expression.eval env) xT2) + (2 ^ 256 - 1)
              - BigInt.value 64 (Vector.map (Expression.eval env) x2))
        + 2 ^ 35 * P256) :
    polyValue 64 (Vector.map (Expression.eval env)
        (Vector.mapFinRange 10 fun k =>
          (if h : k.val < 7 then P[k.val]'h else 0)
            + (if k.val < 5 then cExp (2 ^ 35 * P256) k.val else 0)))
      = polyValue 64 (Vector.map (Expression.eval env)
          (Vector.mapFinRange 10 fun k =>
            qpCoeff q7 q7t k.val
              + (if h : k.val < 4 then
                  y3[k.val]'h + yT2[k.val]'h + ((c976 : ℕ) : F circomPrime) * lam2[k.val]'h else 0))) := by
  rw [polyValue_c2b_lhs env lam2 xT2 x2 P hlam hxT2 hx2 hP,
      polyValue_c2b_rhs env q7 q7t y3 yT2 lam2 hq7 hq7t hy3 hyT2 hlam]
  have hxd := xd_value env xT2 x2 hxT2 hx2

  set S := ∑ j : Fin 4, (Expression.eval env
      (xT2[j.val]'j.isLt + ((2 ^ 64 - 1 : ℕ) : F circomPrime) - x2[j.val]'j.isLt)).val
        * 2 ^ (64 * j.val) with hSdef
  set lv := BigInt.value 64 (Vector.map (Expression.eval env) lam2)
  set vxT2 := BigInt.value 64 (Vector.map (Expression.eval env) xT2)
  set vx2 := BigInt.value 64 (Vector.map (Expression.eval env) x2)
  set vyT2 := BigInt.value 64 (Vector.map (Expression.eval env) yT2)
  set vy3 := BigInt.value 64 (Vector.map (Expression.eval env) y3)

  have hSeq : S = vxT2 + (2 ^ 256 - 1) - vx2 := by
    have hvx2 : vx2 < 2 ^ 256 := BigInt.value_lt hx2
    omega
  rw [hSeq] at *
  set M := lv * (vxT2 + (2 ^ 256 - 1) - vx2) + 2 ^ 35 * P256 - vyT2 - c976 * lv with hM
  rw [hqv, hy3v]
  have hdm := Nat.div_add_mod' M P256
  show lv * (vxT2 + (2 ^ 256 - 1) - vx2) + 2 ^ 35 * P256
      = (M / P256) * P256 + M % P256 + vyT2 + c976 * lv
  omega



lemma slope_num_mod_zero (lv d d4v dfull ch : ℕ)
    (hrec : d + d4v * 2 ^ 256 = dfull)
    (hlv : lv = ch * invModP dfull % P256)
    (hne : (dfull : Specs.Secp256k1.Fp) ≠ 0)
    (hbound : ch ≤ lv * d + d4v * lv * 2 ^ 256 + 8 * P256) :
    (lv * d + d4v * lv * 2 ^ 256 + 8 * P256 - ch) % P256 = 0 := by
  have hlvfp : (lv : Specs.Secp256k1.Fp) * (dfull : Specs.Secp256k1.Fp)
      = (ch : Specs.Secp256k1.Fp) := by
    rw [hlv, invModP, ZMod.natCast_mod]
    push_cast [ZMod.natCast_val, ZMod.cast_id]
    rw [mul_assoc, inv_mul_cancel₀ hne, mul_one]
  have hrecfp : (d : Specs.Secp256k1.Fp) + (d4v : Specs.Secp256k1.Fp) * 2 ^ 256
      = (dfull : Specs.Secp256k1.Fp) := by
    have := congrArg (Nat.cast : ℕ → Specs.Secp256k1.Fp) hrec
    push_cast at this ⊢; linear_combination this
  have hNfp : ((lv * d + d4v * lv * 2 ^ 256 + 8 * P256 - ch : ℕ) : Specs.Secp256k1.Fp) = 0 := by
    rw [Nat.cast_sub hbound]
    push_cast
    have hp : (P256 : Specs.Secp256k1.Fp) = 0 := ZMod.natCast_self _
    have key : (lv : Specs.Secp256k1.Fp) * d + d4v * lv * 2 ^ 256 = ch := by
      have : (lv : Specs.Secp256k1.Fp) * d + d4v * lv * 2 ^ 256
          = lv * (d + d4v * 2 ^ 256) := by ring
      rw [this, hrecfp, hlvfp]
    rw [hp]; linear_combination key
  have hdvd : P256 ∣ (lv * d + d4v * lv * 2 ^ 256 + 8 * P256 - ch) :=
    (ZMod.natCast_eq_zero_iff _ P256).mp hNfp
  have := (Nat.modEq_zero_iff_dvd).mpr hdvd
  simpa using this

lemma slope2_num_mod_zero (lam2 d2 d24v dfull2 lam1 xd y1 vyT2 vyA : ℕ)
    (hrec : d2 + d24v * 2 ^ 256 = dfull2)
    (hlam2 : lam2 = (2 * P256 + vyT2 - y1) * invModP dfull2 % P256)
    (hy1 : y1 = (lam1 * xd + 2 ^ 35 * P256 - vyA - c976 * lam1) % P256)
    (hne : (dfull2 : Specs.Secp256k1.Fp) ≠ 0)
    (hy1bound : vyA + c976 * lam1 ≤ lam1 * xd + 2 ^ 35 * P256)
    (hbound : vyT2 + vyA + c976 * lam1
      ≤ lam2 * d2 + lam1 * xd + d24v * lam2 * 2 ^ 256 + 2 ^ 34 * P256) :
    (lam2 * d2 + lam1 * xd + d24v * lam2 * 2 ^ 256 + 2 ^ 34 * P256
      - vyT2 - vyA - c976 * lam1) % P256 = 0 := by
  have hp : (P256 : Specs.Secp256k1.Fp) = 0 := ZMod.natCast_self _
  have hy1lt : y1 < P256 := hy1 ▸ Nat.mod_lt _ P256_pos
  have hy1fp : (y1 : Specs.Secp256k1.Fp)
      = (lam1 : _) * (xd : _) + 2 ^ 35 * P256 - vyA - c976 * lam1 := by
    rw [hy1, ZMod.natCast_mod, Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast; ring
  have hlam2fp : (lam2 : Specs.Secp256k1.Fp) * (dfull2 : _)
      = (2 * P256 + vyT2 - y1 : ℕ) := by
    rw [hlam2, invModP, ZMod.natCast_mod]
    push_cast [ZMod.natCast_val, ZMod.cast_id]
    rw [mul_assoc, inv_mul_cancel₀ hne, mul_one]
  have hch2bound : y1 ≤ 2 * P256 + vyT2 := by omega
  have hrecfp : (d2 : Specs.Secp256k1.Fp) + (d24v : _) * 2 ^ 256 = (dfull2 : _) := by
    have := congrArg (Nat.cast : ℕ → Specs.Secp256k1.Fp) hrec
    push_cast at this ⊢; linear_combination this
  have hNfp : ((lam2 * d2 + lam1 * xd + d24v * lam2 * 2 ^ 256 + 2 ^ 34 * P256
      - vyT2 - vyA - c976 * lam1 : ℕ) : Specs.Secp256k1.Fp) = 0 := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast
    have key : (lam2 : Specs.Secp256k1.Fp) * d2 + d24v * lam2 * 2 ^ 256
        = (2 * P256 + vyT2 - y1 : ℕ) := by
      have : (lam2 : Specs.Secp256k1.Fp) * d2 + d24v * lam2 * 2 ^ 256
          = lam2 * (d2 + d24v * 2 ^ 256) := by ring
      rw [this, hrecfp, hlam2fp]
    rw [Nat.cast_sub hch2bound] at key
    push_cast at key
    rw [hp] at key hy1fp ⊢
    linear_combination key - hy1fp
  have hdvd : P256 ∣ (lam2 * d2 + lam1 * xd + d24v * lam2 * 2 ^ 256 + 2 ^ 34 * P256
      - vyT2 - vyA - c976 * lam1) :=
    (ZMod.natCast_eq_zero_iff _ P256).mp hNfp
  have := (Nat.modEq_zero_iff_dvd).mpr hdvd
  simpa using this

lemma mod_P256_ne_zero_of_fp_ne {n : ℕ} (h : (n : Specs.Secp256k1.Fp) ≠ 0) :
    n % P256 ≠ 0 := fun hm =>
  h ((ZMod.natCast_eq_zero_iff _ _).mpr (Nat.dvd_of_mod_eq_zero hm))

lemma lamValEnv_chord (env : ProverEnvironment (F circomPrime))
    (xT xA yT yA : Var Emu (F circomPrime))
    (hne : (dFullVal env xT xA : Specs.Secp256k1.Fp) ≠ 0) :
    lamValEnv env xT xA yT yA
      = chVal env yT yA * invModP (dFullVal env xT xA) % P256 := by
  have hm : dFullVal env xT xA % P256 ≠ 0 := mod_P256_ne_zero_of_fp_ne hne
  unfold lamValEnv lamVal
  rw [if_neg (by simpa using hm)]

lemma lamValEnv_lt (env : ProverEnvironment (F circomPrime))
    (xT xA yT yA : Var Emu (F circomPrime)) :
    lamValEnv env xT xA yT yA < P256 := by
  unfold lamValEnv lamVal
  split <;> [split; skip] <;> exact Nat.mod_lt _ P256_pos

lemma x3Quot_top_bound (env : ProverEnvironment (F circomPrime))
    (xT xA yT yA : Var Emu (F circomPrime)) :
    CompactAdd.x3Quot env xT xA yT yA / 2 ^ 256 < 2 ^ 1 := by
  have hlv : lamValEnv env xT xA yT yA < P256 := lamValEnv_lt env xT xA yT yA
  have hP := P256_lt256
  have hpos : 0 < P256 := P256_pos
  unfold CompactAdd.x3Quot
  refine div_div_lt _ P256 (2 ^ 256) (2 ^ 1) (Nat.mul_pos hpos (by positivity)) ?_
  have hlv2 : lamValEnv env xT xA yT yA * lamValEnv env xT xA yT yA < P256 * 2 ^ 256 := by
    nlinarith [hlv, hP, hpos]
  have h4 : 4 * P256 < P256 * 2 ^ 256 := by nlinarith [hP, hpos]
  omega

lemma slopeQuot_top_bound (env : ProverEnvironment (F circomPrime))
    (xT xA yT yA : Var Emu (F circomPrime))
    (hxT : evalEmu env xT < 2 ^ 256) (hyA : evalEmu env yA < 2 ^ 256) :
    CompactAdd.slopeQuot env xT xA yT yA / 2 ^ 256 < 2 ^ 3 := by
  have hlv : lamValEnv env xT xA yT yA < P256 := lamValEnv_lt env xT xA yT yA
  have hP := P256_lt256
  have hpos : 0 < P256 := P256_pos
  have hdf : dFullVal env xT xA < 3 * 2 ^ 256 := by unfold dFullVal; omega
  unfold CompactAdd.slopeQuot
  refine div_div_lt _ P256 (2 ^ 256) (2 ^ 3) (Nat.mul_pos hpos (by positivity)) ?_
  set denv := (if (dFullVal env xT xA % P256 == 0) && ((evalEmu env yA + evalEmu env yT) % P256 == 0)
        then 1
        else if dFullVal env xT xA % P256 == 0 then evalEmu env yA else dFullVal env xT xA) with hdenv
  have hden : denv ≤ 3 * 2 ^ 256 := by rw [hdenv]; split <;> [skip; split] <;> omega
  have hmul : lamValEnv env xT xA yT yA * denv ≤ lamValEnv env xT xA yT yA * (3 * 2 ^ 256) :=
    Nat.mul_le_mul_left _ hden
  have hmul2 : lamValEnv env xT xA yT yA * (3 * 2 ^ 256) < 8 * (P256 * 2 ^ 256) := by
    nlinarith [hlv, hpos]
  have h8 : 8 * P256 < 8 * (P256 * 2 ^ 256) := by nlinarith [hP, hpos]
  exact lt_of_le_of_lt (Nat.sub_le _ _) (by omega)

/-- In the incomplete-add branch the denominator is nonzero modulo `p`, so
`slopeQuot` uses the chord denominator.  Its top quotient fits in two bits. -/
lemma slopeQuot_top_bound_chord (env : ProverEnvironment (F circomPrime))
    (xT xA yT yA : Var Emu (F circomPrime))
    (hxT : evalEmu env xT < 2 ^ 256) (hyA : evalEmu env yA < 2 ^ 256)
    (hne : (dFullVal env xT xA : Specs.Secp256k1.Fp) ≠ 0) :
    CompactAdd.slopeQuot env xT xA yT yA / 2 ^ 256 < 2 ^ 2 := by
  have hlv : lamValEnv env xT xA yT yA < P256 := lamValEnv_lt env xT xA yT yA
  have hpos : 0 < P256 := P256_pos
  have hm : dFullVal env xT xA % P256 ≠ 0 := mod_P256_ne_zero_of_fp_ne hne
  have hP : P256 < 2 ^ 256 := P256_lt256
  have hdf : dFullVal env xT xA < 3 * 2 ^ 256 := by
    unfold dFullVal
    omega
  unfold CompactAdd.slopeQuot
  dsimp only
  have hmB : (dFullVal env xT xA % P256 == 0) = false := by
    exact beq_eq_false_iff_ne.mpr hm
  rw [hmB]
  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  refine div_div_lt _ P256 (2 ^ 256) (2 ^ 2) (Nat.mul_pos hpos (by positivity)) ?_
  have hmul_le : lamValEnv env xT xA yT yA * dFullVal env xT xA
      ≤ lamValEnv env xT xA yT yA * (3 * 2 ^ 256) :=
    Nat.mul_le_mul_left _ (le_of_lt hdf)
  have hmul : lamValEnv env xT xA yT yA * dFullVal env xT xA
      < 3 * (P256 * 2 ^ 256) := by
    have ht : lamValEnv env xT xA yT yA * (3 * 2 ^ 256)
        < 3 * (P256 * 2 ^ 256) := by nlinarith [hlv, hpos]
    exact lt_of_le_of_lt hmul_le ht
  have h8 : 8 * P256 < P256 * 2 ^ 256 := by
    simpa [mul_comm] using
      (Nat.mul_lt_mul_of_pos_left (show 8 < 2 ^ 256 by norm_num) hpos)
  exact lt_of_le_of_lt (Nat.sub_le _ _) (by omega)

lemma lam2W_lt (env : ProverEnvironment (F circomPrime))
    (xA yA x1 lam1 xT2 yT2 : Var Emu (F circomPrime)) :
    lam2W env xA yA x1 lam1 xT2 yT2 < P256 := by
  unfold lam2W; exact Nat.mod_lt _ P256_pos

lemma x2Quot_top_bound (env : ProverEnvironment (F circomPrime))
    (x1 xT2 lam2 : Var Emu (F circomPrime)) (hlam2 : evalEmu env lam2 < P256) :
    x2Quot env x1 xT2 lam2 / 2 ^ 256 < 2 ^ 1 := by
  have hP := P256_lt256
  have hpos : 0 < P256 := P256_pos
  unfold x2Quot
  refine div_div_lt _ P256 (2 ^ 256) (2 ^ 1) (Nat.mul_pos hpos (by positivity)) ?_
  have hlv2 : evalEmu env lam2 * evalEmu env lam2 < P256 * 2 ^ 256 := by
    nlinarith [hlam2, hP, hpos]
  have h4 : 4 * P256 < P256 * 2 ^ 256 := by nlinarith [hP, hpos]
  omega

lemma slope2Quot_top_bound (env : ProverEnvironment (F circomPrime))
    (xA yA x1 lam1 xT2 yT2 : Var Emu (F circomPrime))
    (hlam1 : evalEmu env lam1 < P256)
    (hxT2 : evalEmu env xT2 < 2 ^ 256) (hxA : evalEmu env xA < 2 ^ 256) :
    slope2Quot env xA yA x1 lam1 xT2 yT2 / 2 ^ 256 < 2 ^ 3 := by
  have hlv : lam2W env xA yA x1 lam1 xT2 yT2 < P256 := lam2W_lt env xA yA x1 lam1 xT2 yT2
  have hP := P256_lt256
  have hpos : 0 < P256 := P256_pos
  have hdf : dFullVal env xT2 x1 < 3 * 2 ^ 256 := by unfold dFullVal; omega
  unfold slope2Quot
  refine div_div_lt _ P256 (2 ^ 256) (2 ^ 3) (Nat.mul_pos hpos (by positivity)) ?_
  set xd := evalEmu env xA + (2 ^ 256 - 1) - evalEmu env x1 with hxddef
  have hxdlt : xd ≤ 2 * 2 ^ 256 := by rw [hxddef]; omega
  have hA : lam2W env xA yA x1 lam1 xT2 yT2 * dFullVal env xT2 x1 < 3 * (P256 * 2 ^ 256) := by
    calc lam2W env xA yA x1 lam1 xT2 yT2 * dFullVal env xT2 x1
        ≤ lam2W env xA yA x1 lam1 xT2 yT2 * (3 * 2 ^ 256) := Nat.mul_le_mul_left _ (by omega)
      _ < 3 * (P256 * 2 ^ 256) := by nlinarith [hlv, hpos]
  have hB : evalEmu env lam1 * xd < 2 * (P256 * 2 ^ 256) := by
    calc evalEmu env lam1 * xd
        ≤ evalEmu env lam1 * (2 * 2 ^ 256) := Nat.mul_le_mul_left _ hxdlt
      _ < 2 * (P256 * 2 ^ 256) := by nlinarith [hlam1, hpos]
  have h34 : 2 ^ 34 * P256 < P256 * 2 ^ 256 := by nlinarith [hP, hpos]
  refine lt_of_le_of_lt (Nat.sub_le _ _) ?_
  refine lt_of_le_of_lt (Nat.sub_le _ _) ?_
  refine lt_of_le_of_lt (Nat.sub_le _ _) ?_
  omega

lemma y32Quot_top_bound (env : ProverEnvironment (F circomPrime))
    (xT2 yT2 lam2 x2 : Var Emu (F circomPrime))
    (hlam2 : evalEmu env lam2 < P256) (hxT2 : evalEmu env xT2 < 2 ^ 256) :
    y32Quot env xT2 yT2 lam2 x2 / 2 ^ 256 < 2 ^ 3 := by
  have hP := P256_lt256
  have hpos : 0 < P256 := P256_pos
  unfold y32Quot
  refine div_div_lt _ P256 (2 ^ 256) (2 ^ 3) (Nat.mul_pos hpos (by positivity)) ?_
  set xd := evalEmu env xT2 + (2 ^ 256 - 1) - evalEmu env x2 with hxddef
  have hxdlt : xd ≤ 2 * 2 ^ 256 := by rw [hxddef]; omega
  have hB : evalEmu env lam2 * xd < 2 * (P256 * 2 ^ 256) := by
    calc evalEmu env lam2 * xd
        ≤ evalEmu env lam2 * (2 * 2 ^ 256) := Nat.mul_le_mul_left _ hxdlt
      _ < 2 * (P256 * 2 ^ 256) := by nlinarith [hlam2, hpos]
  have h35 : 2 ^ 35 * P256 < P256 * 2 ^ 256 := by nlinarith [hP, hpos]
  refine lt_of_le_of_lt (Nat.sub_le _ _) ?_
  refine lt_of_le_of_lt (Nat.sub_le _ _) ?_
  omega

lemma couple_vec (env : ProverEnvironment (F circomPrime)) (o V : ℕ)
    (hpin : ∀ i : Fin 4, env.get (o + ↑i) = (emuOfNat V)[↑i]) :
    Vector.map (Expression.eval env.toEnvironment) (Vector.mapRange 4 fun i => var {index := o + i})
      = emuOfNat V := by
  apply Vector.ext
  intro k hk
  rw [Vector.getElem_map, Vector.getElem_mapRange]
  exact hpin ⟨k, hk⟩

lemma couple_value (env : ProverEnvironment (F circomPrime)) (o V : ℕ) (hV : V < 2 ^ 256)
    (hpin : ∀ i : Fin 4, env.get (o + ↑i) = (emuOfNat V)[↑i]) :
    BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange 4 fun i => var {index := o + i})) = V := by
  rw [couple_vec env o V hpin]; exact value_emuOfNat (by simpa [limbBits, numLimbs] using hV)

lemma couple_norm (env : ProverEnvironment (F circomPrime)) (o V : ℕ)
    (hpin : ∀ i : Fin 4, env.get (o + ↑i) = (emuOfNat V)[↑i]) :
    BigInt.Normalized 64 (Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange 4 fun i => var {index := o + i})) := by
  rw [couple_vec env o V hpin]; simpa [limbBits] using emuOfNat_normalized V

lemma couple_rc (env : ProverEnvironment (F circomPrime)) (o Q k : ℕ)
    (hpin : env.get o = ((Q : ℕ) : F circomPrime)) (hb : Q < 2 ^ k) (hk : k ≤ 3) :
    ZMod.val (env.get o) < 2 ^ k := by
  have hQP : Q < circomPrime :=
    lt_of_lt_of_le hb (le_trans (Nat.pow_le_pow_right (by norm_num) hk)
      (le_of_lt (by decide : (2:ℕ) ^ 3 < circomPrime)))
  rw [hpin, ZMod.val_natCast_of_lt hQP]; exact hb

lemma siteO2_complete (env : ProverEnvironment (F circomPrime))
    {oLam1 oX1 oQ6 oQ6t oConvLL : ℕ}
    (input_var_A_x input_var_T1_x input_var_T1_y input_var_A_y : Emu (Expression (F circomPrime)))
    (hxA : BigInt.Normalized 64 (Vector.map (Expression.eval env.toEnvironment) input_var_A_x))
    (hxT1 : BigInt.Normalized 64 (Vector.map (Expression.eval env.toEnvironment) input_var_T1_x))
    (hpin_lam1 : ∀ i : Fin 4, env.get (oLam1 + ↑i)
      = (emuOfNat (lamValEnv env input_var_T1_x input_var_A_x input_var_T1_y input_var_A_y))[↑i])
    (hpin_x1 : ∀ i : Fin 4, env.get (oX1 + ↑i)
      = (emuOfNat (x3Val env input_var_T1_x input_var_A_x input_var_T1_y input_var_A_y))[↑i])
    (hpin_q6 : ∀ i : Fin 4, env.get (oQ6 + ↑i)
      = (emuOfNat (x3Quot env input_var_T1_x input_var_A_x input_var_T1_y input_var_A_y % 2 ^ 256))[↑i])
    (hpin_q6t : env.get oQ6t
      = ((x3Quot env input_var_T1_x input_var_A_x input_var_T1_y input_var_A_y / 2 ^ 256 : ℕ) : F circomPrime))
    (hpin_conv : ∀ i : Fin (2 * 4 - 1), env.get (oConvLL + ↑i)
      = (Vector.ofFn fun k : Fin (2 * 4 - 1) =>
          Expression.eval env.toEnvironment
            (bigIntMulNoReduce
              (Vector.mapRange 4 fun i => var (F := F circomPrime) {index := oLam1 + i})
              (Vector.mapRange 4 fun i => var (F := F circomPrime) {index := oLam1 + i}))[↑k])[↑i]) :
    (Normalize.Assumptions (Vector.map (Expression.eval env.toEnvironment)
          (Vector.mapRange 4 fun i => var {index := oX1 + i})) ∧
        Normalize.Spec 64 (Vector.map (Expression.eval env.toEnvironment)
          (Vector.mapRange 4 fun i => var {index := oX1 + i}))) ∧
      (Normalize.Assumptions (Vector.map (Expression.eval env.toEnvironment)
            (Vector.mapRange 4 fun i => var {index := oQ6 + i})) ∧
          Normalize.Spec 64 (Vector.map (Expression.eval env.toEnvironment)
            (Vector.mapRange 4 fun i => var {index := oQ6 + i}))) ∧
        ZMod.val (env.get oQ6t) < 2 ^ 1 ∧
          (∀ i : Fin (2 * 4 - 1),
              Expression.eval env.toEnvironment (GroupedFlex.polyEvalExpr
                  (Vector.mapRange 4 fun i => var (F := F circomPrime) {index := oLam1 + i})
                  ((↑i + (1 : ℕ) : ℕ) : F circomPrime))
                * Expression.eval env.toEnvironment (GroupedFlex.polyEvalExpr
                  (Vector.mapRange 4 fun i => var (F := F circomPrime) {index := oLam1 + i})
                  ((↑i + (1 : ℕ) : ℕ) : F circomPrime))
                + -Expression.eval env.toEnvironment (GroupedFlex.polyEvalExpr
                  (Vector.mapRange (2 * 4 - 1) fun i => var (F := F circomPrime) {index := oConvLL + i})
                  ((↑i + (1 : ℕ) : ℕ) : F circomPrime)) = 0) ∧
            (GroupedFlex.Assumptions vQuad.Nf vQuad.Nf
                { lhs := Vector.map (Expression.eval env.toEnvironment)
                    (Vector.mapFinRange 9 fun k =>
                      (if h : ↑k < 7 then var (F := F circomPrime) {index := oConvLL + ↑k} else 0)
                        + (if ↑k < 5 then cExp (4 * P256) ↑k else 0)),
                  rhs := Vector.map (Expression.eval env.toEnvironment)
                    (Vector.mapFinRange 9 fun k =>
                      qpCoeff (Vector.mapRange 4 fun i => var {index := oQ6 + i}) (var {index := oQ6t}) ↑k
                        + (if h : ↑k < 4 then var {index := oX1 + ↑k} + input_var_A_x[↑k] + input_var_T1_x[↑k]
                            else 0)) } ∧
              EqViaCarriesFlex.Spec EqViaCarriesFlexT.quadFlexT.B
                { lhs := Vector.map (Expression.eval env.toEnvironment)
                    (Vector.mapFinRange 9 fun k =>
                      (if h : ↑k < 7 then var (F := F circomPrime) {index := oConvLL + ↑k} else 0)
                        + (if ↑k < 5 then cExp (4 * P256) ↑k else 0)),
                  rhs := Vector.map (Expression.eval env.toEnvironment)
                    (Vector.mapFinRange 9 fun k =>
                      qpCoeff (Vector.mapRange 4 fun i => var {index := oQ6 + i}) (var {index := oQ6t}) ↑k
                        + (if h : ↑k < 4 then var {index := oX1 + ↑k} + input_var_A_x[↑k] + input_var_T1_x[↑k]
                            else 0)) }) := by
  set lam1 : Var Emu (F circomPrime) := Vector.mapRange 4 fun i => var {index := oLam1 + i} with hlam1
  set x1 : Var Emu (F circomPrime) := Vector.mapRange 4 fun i => var {index := oX1 + i} with hx1
  set q6 : Var Emu (F circomPrime) := Vector.mapRange 4 fun i => var {index := oQ6 + i} with hq6
  have hnormx1 : BigInt.Normalized 64 (Vector.map (Expression.eval env.toEnvironment) x1) := couple_norm env oX1 _ hpin_x1
  have hnormq6 : BigInt.Normalized 64 (Vector.map (Expression.eval env.toEnvironment) q6) := couple_norm env oQ6 _ hpin_q6
  have hnormlam1 : BigInt.Normalized 64 (Vector.map (Expression.eval env.toEnvironment) lam1) := couple_norm env oLam1 _ hpin_lam1
  have hlt_lam1 : lamValEnv env input_var_T1_x input_var_A_x input_var_T1_y input_var_A_y < 2 ^ 256 :=
    lt_trans (lamValEnv_lt env input_var_T1_x input_var_A_x input_var_T1_y input_var_A_y) P256_lt256
  have hval_lam1 : BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) lam1)
      = lamValEnv env input_var_T1_x input_var_A_x input_var_T1_y input_var_A_y :=
    couple_value env oLam1 _ hlt_lam1 hpin_lam1
  have hval_x1 : BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) x1)
      = x3Val env input_var_T1_x input_var_A_x input_var_T1_y input_var_A_y :=
    couple_value env oX1 _ (by unfold x3Val; exact lt_trans (Nat.mod_lt _ P256_pos) P256_lt256) hpin_x1
  have hval_q6 : BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) q6)
      = x3Quot env input_var_T1_x input_var_A_x input_var_T1_y input_var_A_y % 2 ^ 256 :=
    couple_value env oQ6 _ (Nat.mod_lt _ (by positivity)) hpin_q6
  have hpin' : ∀ k : Fin (2 * 4 - 1), env.get (oConvLL + k.val)
      = Expression.eval env.toEnvironment ((bigIntMulNoReduce lam1 lam1)[k.val]) := by
    intro k
    have := hpin_conv k; simpa only [Fin.getElem_fin, Vector.getElem_ofFn] using this
  have hP := MulMod.interpolatedMul_eval_bridge_uses env.toEnvironment oConvLL lam1 lam1 hpin'
  have hq6t_val : (Expression.eval env.toEnvironment (var {index := oQ6t})).val < 2 ^ 64 := by
    show ZMod.val (env.get oQ6t) < 2 ^ 64
    rw [hpin_q6t]
    have hb := x3Quot_top_bound env input_var_T1_x input_var_A_x input_var_T1_y input_var_A_y
    have hQP : x3Quot env input_var_T1_x input_var_A_x input_var_T1_y input_var_A_y / 2 ^ 256 < circomPrime :=
      lt_of_lt_of_le hb (le_of_lt (by decide : (2:ℕ) ^ 1 < circomPrime))
    rw [ZMod.val_natCast_of_lt hQP]
    exact lt_trans hb (by decide)
  have hx1v : BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) x1)
      = (BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) lam1)
          * BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) lam1) + 4 * P256
        - BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) input_var_A_x)
        - BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) input_var_T1_x)) % P256 := by
    rw [hval_x1, hval_lam1]; unfold x3Val
    rw [evalEmu_eq_value env input_var_A_x, evalEmu_eq_value env input_var_T1_x]
  have hqv : BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) q6)
        + (Expression.eval env.toEnvironment (var {index := oQ6t})).val * 2 ^ 256
      = (BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) lam1)
          * BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) lam1) + 4 * P256
        - BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) input_var_A_x)
        - BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) input_var_T1_x)) / P256 := by
    rw [hval_q6, hval_lam1]
    show _ + (env.get oQ6t).val * 2 ^ 256 = _
    rw [hpin_q6t]
    have hb := x3Quot_top_bound env input_var_T1_x input_var_A_x input_var_T1_y input_var_A_y
    have hQP : x3Quot env input_var_T1_x input_var_A_x input_var_T1_y input_var_A_y / 2 ^ 256 < circomPrime :=
      lt_of_lt_of_le hb (le_of_lt (by decide : (2:ℕ) ^ 1 < circomPrime))
    rw [ZMod.val_natCast_of_lt hQP]
    unfold x3Quot
    rw [evalEmu_eq_value env input_var_A_x, evalEmu_eq_value env input_var_T1_x]
    exact quot_recompose _
  have hq6t3 : (Expression.eval env.toEnvironment (var {index := oQ6t})).val < 2 ^ 3 := by
    show ZMod.val (env.get oQ6t) < 2 ^ 3
    have := couple_rc env oQ6t _ 1 hpin_q6t
      (x3Quot_top_bound env input_var_T1_x input_var_A_x input_var_T1_y input_var_A_y) (by norm_num)
    omega
  have hdis := o2_discharge env.toEnvironment lam1 x1 input_var_A_x input_var_T1_x q6 (var {index := oQ6t})
    (MulMod.interpolatedMul lam1 lam1 oConvLL).1 hP hnormlam1 hnormx1 hxA hxT1 hnormq6 hq6t3
  have hspec := o2_spec_complete env.toEnvironment lam1 x1 input_var_A_x input_var_T1_x q6 (var {index := oQ6t})
    (MulMod.interpolatedMul lam1 lam1 oConvLL).1 hP hnormlam1 hnormx1 hxA hxT1 hnormq6 hq6t_val hx1v hqv
  have hx1fold : ∀ (i : ℕ) (hi : i < 4), (x1[i]'hi) = var (F := F circomPrime) {index := oX1 + i} :=
    fun i hi => Vector.getElem_mapRange i hi
  refine ⟨⟨trivial, hnormx1⟩, ⟨trivial, hnormq6⟩, ?_, ?_, ?_, ?_⟩
  · exact couple_rc env oQ6t _ 1 hpin_q6t
      (x3Quot_top_bound env input_var_T1_x input_var_A_x input_var_T1_y input_var_A_y) (by norm_num)
  · intro i
    rw [add_neg_eq_zero]
    exact MulMod.interpolatedMul_points_of_pins env.toEnvironment oConvLL lam1 lam1 hpin' i
  · refine ⟨fun k => ?_, fun k => ?_⟩
    · have hk := hdis.1 k
      rw [vQuad_Nf_eq_boundAt k]
      simp only [Vector.getElem_map, Vector.getElem_mapFinRange,
        MulMod.interpolatedMul_output, numLimbs, Vector.getElem_mapRange] at hk ⊢; exact hk
    · have hk := hdis.2 k
      rw [vQuad_Nf_eq_boundAt k]
      simp only [Vector.getElem_map, Vector.getElem_mapFinRange, hx1fold] at hk ⊢; exact hk
  · simp only [EqViaCarriesFlex.Spec]
    simp only [MulMod.interpolatedMul_output, numLimbs, Vector.getElem_mapRange, hx1fold] at hspec
    exact hspec

lemma slopeQuot_chord_eq (env : ProverEnvironment (F circomPrime))
    (xT xA yT yA : Var Emu (F circomPrime))
    (hmod : dFullVal env xT xA % P256 ≠ 0) :
    slopeQuot env xT xA yT yA
      = (lamValEnv env xT xA yT yA * dFullVal env xT xA + 8 * P256 - chVal env yT yA) / P256 := by
  unfold slopeQuot
  have hef : (dFullVal env xT xA % P256 == 0) = false := by simpa using hmod
  simp only [hef, Bool.false_and, if_false, Bool.false_eq_true]

lemma siteA1_complete (env : ProverEnvironment (F circomPrime)) {i₀ : ℕ}
    (input_var_A_x input_var_T1_x : Emu (Expression (F circomPrime)))
    (hxA : BigInt.Normalized 64 (Vector.map (Expression.eval env.toEnvironment) input_var_A_x))
    (hxT1 : BigInt.Normalized 64 (Vector.map (Expression.eval env.toEnvironment) input_var_T1_x))
    (hpin_d : ∀ i : Fin 4, env.get (i₀ + ↑i)
      = (emuOfNat (dFullVal env input_var_T1_x input_var_A_x % 2 ^ 256))[↑i])
    (hpin_d4 : env.get (i₀ + 4)
      = ((dFullVal env input_var_T1_x input_var_A_x / 2 ^ 256 : ℕ) : F circomPrime)) :
    (Normalize.Assumptions (Vector.map (Expression.eval env.toEnvironment)
          (Vector.mapRange 4 fun i => var {index := i₀ + i})) ∧
        Normalize.Spec 64 (Vector.map (Expression.eval env.toEnvironment)
          (Vector.mapRange 4 fun i => var {index := i₀ + i}))) ∧
      ZMod.val (env.get (i₀ + 4)) < 2 ^ 2 ∧
        (GroupedFlex.Assumptions vLin.Nf vLin.Nf
            { lhs := Vector.map (Expression.eval env.toEnvironment)
                (Vector.mapFinRange 5 fun k =>
                  if h : ↑k < 4 then var {index := i₀ + ↑k} + input_var_A_x[↑k] else var {index := i₀ + 4}),
              rhs := Vector.map (Expression.eval env.toEnvironment)
                (Vector.mapFinRange 5 fun k =>
                  if h : ↑k < 4 then input_var_T1_x[↑k] + cExp (2 * P256) ↑k else cExp (2 * P256) 4) } ∧
          EqViaCarriesFlex.Spec EqViaCarriesFlexT.linFlexT.B
            { lhs := Vector.map (Expression.eval env.toEnvironment)
                (Vector.mapFinRange 5 fun k =>
                  if h : ↑k < 4 then var {index := i₀ + ↑k} + input_var_A_x[↑k] else var {index := i₀ + 4}),
              rhs := Vector.map (Expression.eval env.toEnvironment)
                (Vector.mapFinRange 5 fun k =>
                  if h : ↑k < 4 then input_var_T1_x[↑k] + cExp (2 * P256) ↑k else cExp (2 * P256) 4) }) := by
  set d : Var Emu (F circomPrime) := Vector.mapRange 4 fun i => var {index := i₀ + i} with hd_def
  have hnormd : BigInt.Normalized 64 (Vector.map (Expression.eval env.toEnvironment) d) := couple_norm env i₀ _ hpin_d
  have hxTlt : evalEmu env input_var_T1_x < 2 ^ 256 := by
    rw [evalEmu_eq_value]; exact BigInt.value_lt hxT1
  have hd4' : (Expression.eval env.toEnvironment (var {index := i₀ + 4})).val < 4 := by
    show ZMod.val (env.get (i₀ + 4)) < 4
    rw [hpin_d4]
    have hb := d4_bound env input_var_T1_x input_var_A_x hxTlt
    have hQP : dFullVal env input_var_T1_x input_var_A_x / 2 ^ 256 < circomPrime :=
      lt_of_lt_of_le hb (le_of_lt (by decide : (2:ℕ) ^ 2 < circomPrime))
    rw [ZMod.val_natCast_of_lt hQP]; exact hb
  have hdfold : ∀ (i : ℕ) (hi : i < 4), (d[i]'hi) = var (F := F circomPrime) {index := i₀ + i} :=
    fun i hi => Vector.getElem_mapRange i hi

  have hval_d : BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) d)
      = dFullVal env input_var_T1_x input_var_A_x % 2 ^ 256 :=
    couple_value env i₀ _ (Nat.mod_lt _ (by positivity)) hpin_d
  have hdfull : BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) d)
      + (Expression.eval env.toEnvironment (var {index := i₀ + 4})).val * 2 ^ 256
      = 2 * P256 + BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) input_var_T1_x)
        - BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) input_var_A_x) := by
    rw [hval_d]
    show _ + (env.get (i₀ + 4)).val * 2 ^ 256 = _
    rw [hpin_d4]
    have hb := d4_bound env input_var_T1_x input_var_A_x hxTlt
    have hQP : dFullVal env input_var_T1_x input_var_A_x / 2 ^ 256 < circomPrime :=
      lt_of_lt_of_le hb (le_of_lt (by decide : (2:ℕ) ^ 2 < circomPrime))
    rw [ZMod.val_natCast_of_lt hQP, quot_recompose]
    unfold dFullVal
    rw [evalEmu_eq_value env input_var_T1_x, evalEmu_eq_value env input_var_A_x]
  have hdis := dblock_discharge env.toEnvironment d input_var_A_x input_var_T1_x (var {index := i₀ + 4})
    hnormd hxA hxT1 hd4'
  have hspec := dblock_spec_complete env.toEnvironment d input_var_A_x input_var_T1_x (var {index := i₀ + 4})
    hnormd hxA hxT1 hdfull
  refine ⟨⟨trivial, hnormd⟩, ?_, ?_, ?_⟩
  · exact couple_rc env (i₀ + 4) _ 2 hpin_d4 (d4_bound env input_var_T1_x input_var_A_x hxTlt) (by norm_num)
  · refine ⟨fun k => ?_, fun k => ?_⟩
    · have hk := hdis.1 k
      rw [vLin_Nf_eq_boundAt k]
      simp only [Vector.getElem_map, Vector.getElem_mapFinRange, hdfold] at hk ⊢; exact hk
    · have hk := hdis.2 k
      rw [vLin_Nf_eq_boundAt k]
      simp only [Vector.getElem_map, Vector.getElem_mapFinRange] at hk ⊢; exact hk
  · simp only [EqViaCarriesFlex.Spec]
    simp only [hdfold] at hspec
    exact hspec


lemma siteC2a_complete (env : ProverEnvironment (F circomPrime))
    {oLam2 oX2 oX1 oQ6b oQ6tb oConvLL2 : ℕ}
    (input_var_T2_x : Emu (Expression (F circomPrime)))
    (hlam2 : BigInt.Normalized 64 (Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange 4 fun i => var {index := oLam2 + i})))
    (hlam2lt : evalEmu env (Vector.mapRange 4 fun i => var {index := oLam2 + i}) < P256)
    (hx1 : BigInt.Normalized 64 (Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange 4 fun i => var {index := oX1 + i})))
    (hxT2 : BigInt.Normalized 64 (Vector.map (Expression.eval env.toEnvironment) input_var_T2_x))
    (hpin_x2 : ∀ i : Fin 4, env.get (oX2 + ↑i)
      = (emuOfNat (x2W env (Vector.mapRange 4 fun i => var {index := oX1 + i}) input_var_T2_x
          (Vector.mapRange 4 fun i => var {index := oLam2 + i})))[↑i])
    (hpin_q6 : ∀ i : Fin 4, env.get (oQ6b + ↑i)
      = (emuOfNat (x2Quot env (Vector.mapRange 4 fun i => var {index := oX1 + i}) input_var_T2_x
          (Vector.mapRange 4 fun i => var {index := oLam2 + i}) % 2 ^ 256))[↑i])
    (hpin_q6t : env.get oQ6tb
      = ((x2Quot env (Vector.mapRange 4 fun i => var {index := oX1 + i}) input_var_T2_x
          (Vector.mapRange 4 fun i => var {index := oLam2 + i}) / 2 ^ 256 : ℕ) : F circomPrime))
    (hpin_conv : ∀ i : Fin (2 * 4 - 1), env.get (oConvLL2 + ↑i)
      = (Vector.ofFn fun k : Fin (2 * 4 - 1) =>
          Expression.eval env.toEnvironment
            (bigIntMulNoReduce
              (Vector.mapRange 4 fun i => var (F := F circomPrime) {index := oLam2 + i})
              (Vector.mapRange 4 fun i => var (F := F circomPrime) {index := oLam2 + i}))[↑k])[↑i]) :
    (Normalize.Assumptions (Vector.map (Expression.eval env.toEnvironment)
          (Vector.mapRange 4 fun i => var {index := oX2 + i})) ∧
        Normalize.Spec 64 (Vector.map (Expression.eval env.toEnvironment)
          (Vector.mapRange 4 fun i => var {index := oX2 + i}))) ∧
      (Normalize.Assumptions (Vector.map (Expression.eval env.toEnvironment)
            (Vector.mapRange 4 fun i => var {index := oQ6b + i})) ∧
          Normalize.Spec 64 (Vector.map (Expression.eval env.toEnvironment)
            (Vector.mapRange 4 fun i => var {index := oQ6b + i}))) ∧
        ZMod.val (env.get oQ6tb) < 2 ^ 1 ∧
          (∀ i : Fin (2 * 4 - 1),
              Expression.eval env.toEnvironment (GroupedFlex.polyEvalExpr
                  (Vector.mapRange 4 fun i => var (F := F circomPrime) {index := oLam2 + i})
                  ((↑i + (1 : ℕ) : ℕ) : F circomPrime))
                * Expression.eval env.toEnvironment (GroupedFlex.polyEvalExpr
                  (Vector.mapRange 4 fun i => var (F := F circomPrime) {index := oLam2 + i})
                  ((↑i + (1 : ℕ) : ℕ) : F circomPrime))
                + -Expression.eval env.toEnvironment (GroupedFlex.polyEvalExpr
                  (Vector.mapRange (2 * 4 - 1) fun i => var (F := F circomPrime) {index := oConvLL2 + i})
                  ((↑i + (1 : ℕ) : ℕ) : F circomPrime)) = 0) ∧
            (GroupedFlex.Assumptions vQuad.Nf vQuad.Nf
                { lhs := Vector.map (Expression.eval env.toEnvironment)
                    (Vector.mapFinRange 9 fun k =>
                      (if h : ↑k < 7 then var (F := F circomPrime) {index := oConvLL2 + ↑k} else 0)
                        + (if ↑k < 5 then cExp (4 * P256) ↑k else 0)),
                  rhs := Vector.map (Expression.eval env.toEnvironment)
                    (Vector.mapFinRange 9 fun k =>
                      qpCoeff (Vector.mapRange 4 fun i => var {index := oQ6b + i}) (var {index := oQ6tb}) ↑k
                        + (if h : ↑k < 4 then var {index := oX2 + ↑k} + var {index := oX1 + ↑k} + input_var_T2_x[↑k]
                            else 0)) } ∧
              EqViaCarriesFlex.Spec EqViaCarriesFlexT.quadFlexT.B
                { lhs := Vector.map (Expression.eval env.toEnvironment)
                    (Vector.mapFinRange 9 fun k =>
                      (if h : ↑k < 7 then var (F := F circomPrime) {index := oConvLL2 + ↑k} else 0)
                        + (if ↑k < 5 then cExp (4 * P256) ↑k else 0)),
                  rhs := Vector.map (Expression.eval env.toEnvironment)
                    (Vector.mapFinRange 9 fun k =>
                      qpCoeff (Vector.mapRange 4 fun i => var {index := oQ6b + i}) (var {index := oQ6tb}) ↑k
                        + (if h : ↑k < 4 then var {index := oX2 + ↑k} + var {index := oX1 + ↑k} + input_var_T2_x[↑k]
                            else 0)) }) := by
  set lam2 : Var Emu (F circomPrime) := Vector.mapRange 4 fun i => var {index := oLam2 + i} with hlam2def
  set x2 : Var Emu (F circomPrime) := Vector.mapRange 4 fun i => var {index := oX2 + i} with hx2def
  set x1 : Var Emu (F circomPrime) := Vector.mapRange 4 fun i => var {index := oX1 + i} with hx1def
  set q6 : Var Emu (F circomPrime) := Vector.mapRange 4 fun i => var {index := oQ6b + i} with hq6def
  have hnormx2 : BigInt.Normalized 64 (Vector.map (Expression.eval env.toEnvironment) x2) := couple_norm env oX2 _ hpin_x2
  have hnormq6 : BigInt.Normalized 64 (Vector.map (Expression.eval env.toEnvironment) q6) := couple_norm env oQ6b _ hpin_q6
  have hval_x2 : BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) x2)
      = x2W env x1 input_var_T2_x lam2 :=
    couple_value env oX2 _ (by unfold x2W; exact lt_trans (Nat.mod_lt _ P256_pos) P256_lt256) hpin_x2
  have hval_q6 : BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) q6)
      = x2Quot env x1 input_var_T2_x lam2 % 2 ^ 256 :=
    couple_value env oQ6b _ (Nat.mod_lt _ (by positivity)) hpin_q6
  have hpin' : ∀ k : Fin (2 * 4 - 1), env.get (oConvLL2 + k.val)
      = Expression.eval env.toEnvironment ((bigIntMulNoReduce lam2 lam2)[k.val]) := by
    intro k
    have := hpin_conv k; simpa only [Fin.getElem_fin, Vector.getElem_ofFn] using this
  have hP := MulMod.interpolatedMul_eval_bridge_uses env.toEnvironment oConvLL2 lam2 lam2 hpin'
  have hq6t_val : (Expression.eval env.toEnvironment (var {index := oQ6tb})).val < 2 ^ 64 := by
    show ZMod.val (env.get oQ6tb) < 2 ^ 64
    rw [hpin_q6t]
    have hb := x2Quot_top_bound env x1 input_var_T2_x lam2 hlam2lt
    have hQP : x2Quot env x1 input_var_T2_x lam2 / 2 ^ 256 < circomPrime :=
      lt_of_lt_of_le hb (le_of_lt (by decide : (2:ℕ) ^ 1 < circomPrime))
    rw [ZMod.val_natCast_of_lt hQP]
    exact lt_trans hb (by decide)
  have hx1v : BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) x2)
      = (BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) lam2)
          * BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) lam2) + 4 * P256
        - BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) x1)
        - BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) input_var_T2_x)) % P256 := by
    rw [hval_x2]; unfold x2W
    rw [evalEmu_eq_value env lam2, evalEmu_eq_value env x1, evalEmu_eq_value env input_var_T2_x]
  have hqv : BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) q6)
        + (Expression.eval env.toEnvironment (var {index := oQ6tb})).val * 2 ^ 256
      = (BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) lam2)
          * BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) lam2) + 4 * P256
        - BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) x1)
        - BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) input_var_T2_x)) / P256 := by
    rw [hval_q6]
    show _ + (env.get oQ6tb).val * 2 ^ 256 = _
    rw [hpin_q6t]
    have hb := x2Quot_top_bound env x1 input_var_T2_x lam2 hlam2lt
    have hQP : x2Quot env x1 input_var_T2_x lam2 / 2 ^ 256 < circomPrime :=
      lt_of_lt_of_le hb (le_of_lt (by decide : (2:ℕ) ^ 1 < circomPrime))
    rw [ZMod.val_natCast_of_lt hQP]
    unfold x2Quot
    rw [evalEmu_eq_value env lam2, evalEmu_eq_value env x1, evalEmu_eq_value env input_var_T2_x]
    exact quot_recompose _
  have hq6t3 : (Expression.eval env.toEnvironment (var {index := oQ6tb})).val < 2 ^ 3 := by
    show ZMod.val (env.get oQ6tb) < 2 ^ 3
    have := couple_rc env oQ6tb _ 1 hpin_q6t
      (x2Quot_top_bound env x1 input_var_T2_x lam2 hlam2lt) (by norm_num)
    omega
  have hdis := o2_discharge env.toEnvironment lam2 x2 x1 input_var_T2_x q6 (var {index := oQ6tb})
    (MulMod.interpolatedMul lam2 lam2 oConvLL2).1 hP hlam2 hnormx2 hx1 hxT2 hnormq6 hq6t3
  have hspec := o2_spec_complete env.toEnvironment lam2 x2 x1 input_var_T2_x q6 (var {index := oQ6tb})
    (MulMod.interpolatedMul lam2 lam2 oConvLL2).1 hP hlam2 hnormx2 hx1 hxT2 hnormq6 hq6t_val hx1v hqv
  have hx2fold : ∀ (i : ℕ) (hi : i < 4), (x2[i]'hi) = var (F := F circomPrime) {index := oX2 + i} :=
    fun i hi => Vector.getElem_mapRange i hi
  have hx1fold : ∀ (i : ℕ) (hi : i < 4), (x1[i]'hi) = var (F := F circomPrime) {index := oX1 + i} :=
    fun i hi => Vector.getElem_mapRange i hi
  refine ⟨⟨trivial, hnormx2⟩, ⟨trivial, hnormq6⟩, ?_, ?_, ?_, ?_⟩
  · exact couple_rc env oQ6tb _ 1 hpin_q6t (x2Quot_top_bound env x1 input_var_T2_x lam2 hlam2lt) (by norm_num)
  · intro i
    rw [add_neg_eq_zero]
    exact MulMod.interpolatedMul_points_of_pins env.toEnvironment oConvLL2 lam2 lam2 hpin' i
  · refine ⟨fun k => ?_, fun k => ?_⟩
    · have hk := hdis.1 k
      rw [vQuad_Nf_eq_boundAt k]
      simp only [Vector.getElem_map, Vector.getElem_mapFinRange,
        MulMod.interpolatedMul_output, numLimbs, Vector.getElem_mapRange] at hk ⊢; exact hk
    · have hk := hdis.2 k
      rw [vQuad_Nf_eq_boundAt k]
      simp only [Vector.getElem_map, Vector.getElem_mapFinRange, hx2fold, hx1fold] at hk ⊢; exact hk
  · simp only [EqViaCarriesFlex.Spec]
    simp only [MulMod.interpolatedMul_output, numLimbs, Vector.getElem_mapRange, hx2fold, hx1fold] at hspec
    exact hspec

lemma siteC2b_complete (env : ProverEnvironment (F circomPrime))
    {oLam2 oX2 oY3 oQ7 oQ7t oConvLX2 : ℕ}
    (input_var_T2_x input_var_T2_y : Emu (Expression (F circomPrime)))
    (hlam2 : BigInt.Normalized 64 (Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange 4 fun i => var {index := oLam2 + i})))
    (hlam2lt : evalEmu env (Vector.mapRange 4 fun i => var {index := oLam2 + i}) < P256)
    (hx2 : BigInt.Normalized 64 (Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange 4 fun i => var {index := oX2 + i})))
    (hxT2 : BigInt.Normalized 64 (Vector.map (Expression.eval env.toEnvironment) input_var_T2_x))
    (hxT2lt : evalEmu env input_var_T2_x < 2 ^ 256)
    (hyT2 : BigInt.Normalized 64 (Vector.map (Expression.eval env.toEnvironment) input_var_T2_y))
    (hpin_y3 : ∀ i : Fin 4, env.get (oY3 + ↑i)
      = (emuOfNat (y32W env input_var_T2_x input_var_T2_y
          (Vector.mapRange 4 fun i => var {index := oLam2 + i})
          (Vector.mapRange 4 fun i => var {index := oX2 + i})))[↑i])
    (hpin_q7 : ∀ i : Fin 4, env.get (oQ7 + ↑i)
      = (emuOfNat (y32Quot env input_var_T2_x input_var_T2_y
          (Vector.mapRange 4 fun i => var {index := oLam2 + i})
          (Vector.mapRange 4 fun i => var {index := oX2 + i}) % 2 ^ 256))[↑i])
    (hpin_q7t : env.get oQ7t
      = ((y32Quot env input_var_T2_x input_var_T2_y
          (Vector.mapRange 4 fun i => var {index := oLam2 + i})
          (Vector.mapRange 4 fun i => var {index := oX2 + i}) / 2 ^ 256 : ℕ) : F circomPrime))
    (hpin_conv : ∀ i : Fin (2 * 4 - 1), env.get (oConvLX2 + ↑i)
      = (Vector.ofFn fun k : Fin (2 * 4 - 1) =>
          Expression.eval env.toEnvironment
            (bigIntMulNoReduce
              (Vector.mapRange 4 fun i => var (F := F circomPrime) {index := oLam2 + i})
              (Vector.ofFn fun i : Fin 4 =>
                input_var_T2_x[↑i] + Expression.const ((2 ^ 64 - 1 : ℕ) : F circomPrime)
                  - var (F := F circomPrime) {index := oX2 + ↑i}))[↑k])[↑i]) :
    (Normalize.Assumptions (Vector.map (Expression.eval env.toEnvironment)
          (Vector.mapRange 4 fun i => var {index := oY3 + i})) ∧
        Normalize.Spec 64 (Vector.map (Expression.eval env.toEnvironment)
          (Vector.mapRange 4 fun i => var {index := oY3 + i}))) ∧
      (Normalize.Assumptions (Vector.map (Expression.eval env.toEnvironment)
            (Vector.mapRange 4 fun i => var {index := oQ7 + i})) ∧
          Normalize.Spec 64 (Vector.map (Expression.eval env.toEnvironment)
            (Vector.mapRange 4 fun i => var {index := oQ7 + i}))) ∧
        ZMod.val (env.get oQ7t) < 2 ^ 3 ∧
          (∀ i : Fin (2 * 4 - 1),
              Expression.eval env.toEnvironment (GroupedFlex.polyEvalExpr
                  (Vector.mapRange 4 fun i => var (F := F circomPrime) {index := oLam2 + i})
                  ((↑i + (1 : ℕ) : ℕ) : F circomPrime))
                * Expression.eval env.toEnvironment (GroupedFlex.polyEvalExpr
                  (Vector.ofFn fun i : Fin 4 =>
                    input_var_T2_x[↑i] + Expression.const ((2 ^ 64 - 1 : ℕ) : F circomPrime)
                      - var (F := F circomPrime) {index := oX2 + ↑i})
                  ((↑i + (1 : ℕ) : ℕ) : F circomPrime))
                + -Expression.eval env.toEnvironment (GroupedFlex.polyEvalExpr
                  (Vector.mapRange (2 * 4 - 1) fun i => var (F := F circomPrime) {index := oConvLX2 + i})
                  ((↑i + (1 : ℕ) : ℕ) : F circomPrime)) = 0) ∧
            (GroupedFlex.Assumptions vWide.Nf vWide.Nf
                { lhs := Vector.map (Expression.eval env.toEnvironment)
                    (Vector.mapFinRange 10 fun k =>
                      (if h : ↑k < 7 then var (F := F circomPrime) {index := oConvLX2 + ↑k} else 0)
                        + (if ↑k < 5 then cExp (2 ^ 35 * P256) ↑k else 0)),
                  rhs := Vector.map (Expression.eval env.toEnvironment)
                    (Vector.mapFinRange 10 fun k =>
                      qpCoeff (Vector.mapRange 4 fun i => var {index := oQ7 + i}) (var {index := oQ7t}) ↑k
                        + (if h : ↑k < 4 then var {index := oY3 + ↑k} + input_var_T2_y[↑k]
                            + ((c976 : ℕ) : F circomPrime) * var (F := F circomPrime) {index := oLam2 + ↑k} else 0)) } ∧
              EqViaCarriesFlex.Spec EqViaCarriesFlexT.wideFlexT.B
                { lhs := Vector.map (Expression.eval env.toEnvironment)
                    (Vector.mapFinRange 10 fun k =>
                      (if h : ↑k < 7 then var (F := F circomPrime) {index := oConvLX2 + ↑k} else 0)
                        + (if ↑k < 5 then cExp (2 ^ 35 * P256) ↑k else 0)),
                  rhs := Vector.map (Expression.eval env.toEnvironment)
                    (Vector.mapFinRange 10 fun k =>
                      qpCoeff (Vector.mapRange 4 fun i => var {index := oQ7 + i}) (var {index := oQ7t}) ↑k
                        + (if h : ↑k < 4 then var {index := oY3 + ↑k} + input_var_T2_y[↑k]
                            + ((c976 : ℕ) : F circomPrime) * var (F := F circomPrime) {index := oLam2 + ↑k} else 0)) }) := by
  set lam2 : Var Emu (F circomPrime) := Vector.mapRange 4 fun i => var {index := oLam2 + i} with hlam2def
  set x2 : Var Emu (F circomPrime) := Vector.mapRange 4 fun i => var {index := oX2 + i} with hx2def
  set y3 : Var Emu (F circomPrime) := Vector.mapRange 4 fun i => var {index := oY3 + i} with hy3def
  set q7 : Var Emu (F circomPrime) := Vector.mapRange 4 fun i => var {index := oQ7 + i} with hq7def
  set xd2 : Var Emu (F circomPrime) := Vector.ofFn fun i : Fin 4 =>
    input_var_T2_x[i.val]'i.isLt + Expression.const ((2 ^ 64 - 1 : ℕ) : F circomPrime) - x2[i.val]'i.isLt with hxd2def
  have hnormy3 : BigInt.Normalized 64 (Vector.map (Expression.eval env.toEnvironment) y3) := couple_norm env oY3 _ hpin_y3
  have hnormq7 : BigInt.Normalized 64 (Vector.map (Expression.eval env.toEnvironment) q7) := couple_norm env oQ7 _ hpin_q7
  have hval_y3 : BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) y3)
      = y32W env input_var_T2_x input_var_T2_y lam2 x2 :=
    couple_value env oY3 _ (by unfold y32W; exact lt_trans (Nat.mod_lt _ P256_pos) P256_lt256) hpin_y3
  have hval_q7 : BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) q7)
      = y32Quot env input_var_T2_x input_var_T2_y lam2 x2 % 2 ^ 256 :=
    couple_value env oQ7 _ (Nat.mod_lt _ (by positivity)) hpin_q7
  have hlam2fold : ∀ (i : ℕ) (hi : i < 4), (lam2[i]'hi) = var (F := F circomPrime) {index := oLam2 + i} :=
    fun i hi => Vector.getElem_mapRange i hi
  have hx2fold : ∀ (i : ℕ) (hi : i < 4), (x2[i]'hi) = var (F := F circomPrime) {index := oX2 + i} :=
    fun i hi => Vector.getElem_mapRange i hi
  have hy3fold : ∀ (i : ℕ) (hi : i < 4), (y3[i]'hi) = var (F := F circomPrime) {index := oY3 + i} :=
    fun i hi => Vector.getElem_mapRange i hi
  have hxd_eq : xd2 = (Vector.ofFn fun i : Fin 4 =>
        input_var_T2_x[i.val]'i.isLt + Expression.const ((2 ^ 64 - 1 : ℕ) : F circomPrime)
          - var (F := F circomPrime) { index := oX2 + i.val }) := by
    rw [hxd2def]
    apply Vector.ext; intro j hj
    simp only [Vector.getElem_ofFn, hx2fold]
  have hpin' : ∀ k : Fin (2 * 4 - 1), env.get (oConvLX2 + k.val)
      = Expression.eval env.toEnvironment ((bigIntMulNoReduce lam2 xd2)[k.val]) := by
    intro k
    rw [hxd_eq]
    have := hpin_conv k; simpa only [Fin.getElem_fin, Vector.getElem_ofFn] using this
  have hP := MulMod.interpolatedMul_eval_bridge_uses env.toEnvironment oConvLX2 lam2 xd2 hpin'

  have hq7t_val : (Expression.eval env.toEnvironment (var {index := oQ7t})).val < 2 ^ 64 := by
    show ZMod.val (env.get oQ7t) < 2 ^ 64
    rw [hpin_q7t]
    have hb := y32Quot_top_bound env input_var_T2_x input_var_T2_y lam2 x2 hlam2lt hxT2lt
    have hQP : y32Quot env input_var_T2_x input_var_T2_y lam2 x2 / 2 ^ 256 < circomPrime :=
      lt_of_lt_of_le hb (le_of_lt (by decide : (2:ℕ) ^ 3 < circomPrime))
    rw [ZMod.val_natCast_of_lt hQP]
    exact lt_trans hb (by decide)

  have hlam2v : BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) lam2) < P256 := by
    rw [← evalEmu_eq_value]; exact hlam2lt
  have hyT2lt : BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) input_var_T2_y) < 2 ^ 256 :=
    BigInt.value_lt hyT2
  have hy3v : BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) y3)
      = (BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) lam2)
          * (BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) input_var_T2_x) + (2 ^ 256 - 1)
              - BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) x2))
        + 2 ^ 35 * P256 - BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) input_var_T2_y)
        - c976 * BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) lam2)) % P256 := by
    rw [hval_y3]; unfold y32W
    rw [evalEmu_eq_value env lam2, evalEmu_eq_value env input_var_T2_x, evalEmu_eq_value env x2,
      evalEmu_eq_value env input_var_T2_y]
  have hqv : BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) q7)
        + (Expression.eval env.toEnvironment (var {index := oQ7t})).val * 2 ^ 256
      = (BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) lam2)
          * (BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) input_var_T2_x) + (2 ^ 256 - 1)
              - BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) x2))
        + 2 ^ 35 * P256 - BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) input_var_T2_y)
        - c976 * BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) lam2)) / P256 := by
    rw [hval_q7]
    show _ + (env.get oQ7t).val * 2 ^ 256 = _
    rw [hpin_q7t]
    have hb := y32Quot_top_bound env input_var_T2_x input_var_T2_y lam2 x2 hlam2lt hxT2lt
    have hQP : y32Quot env input_var_T2_x input_var_T2_y lam2 x2 / 2 ^ 256 < circomPrime :=
      lt_of_lt_of_le hb (le_of_lt (by decide : (2:ℕ) ^ 3 < circomPrime))
    rw [ZMod.val_natCast_of_lt hQP]
    unfold y32Quot
    rw [evalEmu_eq_value env lam2, evalEmu_eq_value env input_var_T2_x, evalEmu_eq_value env x2,
      evalEmu_eq_value env input_var_T2_y]
    exact quot_recompose _
  have hbound : BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) input_var_T2_y)
        + c976 * BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) lam2)
      ≤ BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) lam2)
          * (BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) input_var_T2_x) + (2 ^ 256 - 1)
              - BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) x2))
        + 2 ^ 35 * P256 := by
    have hP256 := two_pow255_lt_P256
    have hc : c976 * BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) lam2)
        + BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) input_var_T2_y) ≤ 2 ^ 35 * P256 := by
      have h1 : c976 * BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) lam2) ≤ c976 * P256 :=
        Nat.mul_le_mul_left _ (le_of_lt hlam2v)
      have h2 : (c976 : ℕ) = 2 ^ 32 + 976 := rfl
      nlinarith [hlam2v, hyT2lt, hP256, P256_pos]
    omega
  have hq7t3 : (Expression.eval env.toEnvironment (var {index := oQ7t})).val < 2 ^ 3 := by
    show ZMod.val (env.get oQ7t) < 2 ^ 3
    exact couple_rc env oQ7t _ 3 hpin_q7t
      (y32Quot_top_bound env input_var_T2_x input_var_T2_y lam2 x2 hlam2lt hxT2lt) (by norm_num)
  have hdis := c2b_discharge env.toEnvironment lam2 input_var_T2_x x2 y3 input_var_T2_y q7 (var {index := oQ7t})
    (MulMod.interpolatedMul lam2 xd2 oConvLX2).1 hP hlam2 hxT2 hx2 hnormy3 hyT2 hnormq7 hq7t3
  have hspec := c2b_spec_complete env.toEnvironment lam2 input_var_T2_x x2 y3 input_var_T2_y q7 (var {index := oQ7t})
    (MulMod.interpolatedMul lam2 xd2 oConvLX2).1 hP hlam2 hxT2 hx2 hnormy3 hyT2 hnormq7 hq7t_val hy3v hqv hbound
  refine ⟨⟨trivial, hnormy3⟩, ⟨trivial, hnormq7⟩, ?_, ?_, ?_, ?_⟩
  · exact couple_rc env oQ7t _ 3 hpin_q7t (y32Quot_top_bound env input_var_T2_x input_var_T2_y lam2 x2 hlam2lt hxT2lt) (by norm_num)
  · intro i
    rw [add_neg_eq_zero]
    have h := MulMod.interpolatedMul_points_of_pins env.toEnvironment oConvLX2 lam2 xd2 hpin' i
    rw [hxd_eq] at h
    simpa only [Fin.getElem_fin] using h
  · refine ⟨fun k => ?_, fun k => ?_⟩
    · have hk := hdis.1 k
      rw [vWide_Nf_eq_boundAt k]
      simp only [Vector.getElem_map, Vector.getElem_mapFinRange,
        MulMod.interpolatedMul_output, numLimbs, Vector.getElem_mapRange] at hk ⊢; exact hk
    · have hk := hdis.2 k
      rw [vWide_Nf_eq_boundAt k]
      simp only [Vector.getElem_map, Vector.getElem_mapFinRange, hy3fold, hlam2fold] at hk ⊢; exact hk
  · simp only [EqViaCarriesFlex.Spec]
    simp only [MulMod.interpolatedMul_output, numLimbs, Vector.getElem_mapRange, hy3fold, hlam2fold] at hspec
    exact hspec


/-- §BORROW-PILOT (completeness Spec side): fat-limb analogue of
`a2_spec_complete` — the combined `gfQuadFat` identity's two sides evaluate
equal for the honest witness, with `dtil`'s weighted limb sum abstracted as
the raw `Σ` (the caller supplies its `= dFullVal` fact through `hqv`/`hrem`). -/
lemma a2_spec_fat_complete (env : Environment (F circomPrime))
    (lam dtil : Var Emu (F circomPrime)) (qst : Expression (F circomPrime))
    (qs yT yA : Var Emu (F circomPrime))
    (P : Vector (Expression (F circomPrime)) 7)
    (hP : ∀ k : Fin 7,
      Expression.eval env P[k.val] = Expression.eval env (bigIntMulNoReduce lam dtil)[k.val])
    (hlam : BigInt.Normalized 64 (Vector.map (Expression.eval env) lam))
    (hdtil : ∀ i : Fin 4, (Expression.eval env dtil[i.val]).val < 3 * 2 ^ 64)
    (hqs : BigInt.Normalized 64 (Vector.map (Expression.eval env) qs))
    (hqst : (Expression.eval env qst).val < 2 ^ 64)
    (hyT : BigInt.Normalized 64 (Vector.map (Expression.eval env) yT))
    (hyA : BigInt.Normalized 64 (Vector.map (Expression.eval env) yA))
    (hqv : BigInt.value 64 (Vector.map (Expression.eval env) qs)
        + (Expression.eval env qst).val * 2 ^ 256
      = (BigInt.value 64 (Vector.map (Expression.eval env) lam)
            * (∑ j : Fin 4, (Expression.eval env dtil[j.val]).val * 2 ^ (64 * j.val))
          + 8 * P256
        - (BigInt.value 64 (Vector.map (Expression.eval env) yT) + 2 * P256
            - BigInt.value 64 (Vector.map (Expression.eval env) yA))) / P256)
    (hrem : (BigInt.value 64 (Vector.map (Expression.eval env) lam)
            * (∑ j : Fin 4, (Expression.eval env dtil[j.val]).val * 2 ^ (64 * j.val))
          + 8 * P256
        - (BigInt.value 64 (Vector.map (Expression.eval env) yT) + 2 * P256
            - BigInt.value 64 (Vector.map (Expression.eval env) yA))) % P256 = 0) :
    polyValue 64 (Vector.map (Expression.eval env)
        (Vector.mapFinRange 9 fun k =>
          (if h : k.val < 7 then P[k.val]'h else 0)
            + (if k.val < 5 then cExp (8 * P256) k.val else 0)))
      = polyValue 64 (Vector.map (Expression.eval env)
          (Vector.mapFinRange 9 fun k =>
            qpCoeff qs qst k.val
              + (if h : k.val < 4 then
                  yT[k.val]'h - yA[k.val]'h
                    + (((2 ^ 64 - 1 + limbOfNat cK k.val : ℕ) : F circomPrime)
                        : Expression (F circomPrime)) else 0))) := by
  rw [polyValue_a2_lhs_fat env lam dtil P hP hlam hdtil,
      polyValue_a2_rhs env qs qst yT yA hqs hqst hyT hyA]
  have hya := ya_value env yT yA hyT hyA
  have hyAlt : BigInt.value 64 (Vector.map (Expression.eval env) yA) < 2 ^ 256 :=
    BigInt.value_lt hyA
  have hyTlt : BigInt.value 64 (Vector.map (Expression.eval env) yT) < 2 ^ 256 :=
    BigInt.value_lt hyT
  have hlamsum : (∑ i : Fin 4, (Expression.eval env lam[i.val]).val * 2 ^ (64 * i.val))
      = BigInt.value 64 (Vector.map (Expression.eval env) lam) :=
    (MulMod.value_map_eval env lam).symm
  rw [hlamsum]
  set A := BigInt.value 64 (Vector.map (Expression.eval env) lam)
      * (∑ j : Fin 4, (Expression.eval env dtil[j.val]).val * 2 ^ (64 * j.val)) with hAdef
  set S := ∑ j : Fin 4, (Expression.eval env
      (yT[j.val]'j.isLt - yA[j.val]'j.isLt
        + (((2 ^ 64 - 1 + limbOfNat cK j.val : ℕ) : F circomPrime) : Expression (F circomPrime)))).val
        * 2 ^ (64 * j.val) with hSdef
  set vyT := BigInt.value 64 (Vector.map (Expression.eval env) yT)
  set vyA := BigInt.value 64 (Vector.map (Expression.eval env) yA)
  set N := A + 8 * P256 - (vyT + 2 * P256 - vyA) with hNdef
  rw [hqv]
  have hdm := Nat.div_add_mod' N P256
  have hP256 : (2:ℕ) ^ 256 < P256 * 2 := by decide
  show A + 8 * P256 = (N / P256) * P256 + S
  omega

/-- §BORROW-PILOT (completeness): replaces `siteA1_complete`+`siteA2_complete`
for the new (5-conjunct) stageA. `dtil` is wire-only, so there are no
`d`/`d4`/`lp` pins at all. -/
lemma siteA_fat_complete (env : ProverEnvironment (F circomPrime))
    {oLam1 oQs oQst oConvLD : ℕ}
    (input_var_A_x input_var_A_y input_var_T1_x input_var_T1_y : Emu (Expression (F circomPrime)))
    (hxA : BigInt.Normalized 64 (Vector.map (Expression.eval env.toEnvironment) input_var_A_x))
    (hyA : BigInt.Normalized 64 (Vector.map (Expression.eval env.toEnvironment) input_var_A_y))
    (hxT1 : BigInt.Normalized 64 (Vector.map (Expression.eval env.toEnvironment) input_var_T1_x))
    (hyT1 : BigInt.Normalized 64 (Vector.map (Expression.eval env.toEnvironment) input_var_T1_y))
    (hxT1lt : evalEmu env input_var_T1_x < 2 ^ 256)
    (hyAlt : evalEmu env input_var_A_y < 2 ^ 256)
    (hne : (dFullVal env input_var_T1_x input_var_A_x : Specs.Secp256k1.Fp) ≠ 0)
    (hpin_lam1 : ∀ i : Fin 4, env.get (oLam1 + ↑i)
      = (emuOfNat (lamValEnv env input_var_T1_x input_var_A_x input_var_T1_y input_var_A_y))[↑i])
    (hpin_qs : ∀ i : Fin 4, env.get (oQs + ↑i)
      = (emuOfNat (slopeQuot env input_var_T1_x input_var_A_x input_var_T1_y input_var_A_y % 2 ^ 256))[↑i])
    (hpin_qst : env.get oQst
      = ((slopeQuot env input_var_T1_x input_var_A_x input_var_T1_y input_var_A_y / 2 ^ 256 : ℕ) : F circomPrime))
    (hpin_conv : ∀ i : Fin (2 * 4 - 1), env.get (oConvLD + ↑i)
      = (Vector.ofFn fun k : Fin (2 * 4 - 1) =>
          Expression.eval env.toEnvironment
            (bigIntMulNoReduce
              (Vector.mapRange 4 fun i => var (F := F circomPrime) {index := oLam1 + i})
              (dtilOf input_var_T1_x input_var_A_x))[↑k])[↑i]) :
    (Normalize.Assumptions (Vector.map (Expression.eval env.toEnvironment)
          (Vector.mapRange 4 fun i => var {index := oLam1 + i})) ∧
        Normalize.Spec 64 (Vector.map (Expression.eval env.toEnvironment)
          (Vector.mapRange 4 fun i => var {index := oLam1 + i}))) ∧
      (Normalize.Assumptions (Vector.map (Expression.eval env.toEnvironment)
            (Vector.mapRange 4 fun i => var {index := oQs + i})) ∧
          Normalize.Spec 64 (Vector.map (Expression.eval env.toEnvironment)
            (Vector.mapRange 4 fun i => var {index := oQs + i}))) ∧
        ZMod.val (env.get oQst) < 2 ^ 2 ∧
          (∀ i : Fin (2 * 4 - 1),
              Expression.eval env.toEnvironment (GroupedFlex.polyEvalExpr
                  (Vector.mapRange 4 fun i => var (F := F circomPrime) {index := oLam1 + i})
                  ((↑i + (1 : ℕ) : ℕ) : F circomPrime))
                * Expression.eval env.toEnvironment (GroupedFlex.polyEvalExpr
                  (dtilOf input_var_T1_x input_var_A_x)
                  ((↑i + (1 : ℕ) : ℕ) : F circomPrime))
                + -Expression.eval env.toEnvironment (GroupedFlex.polyEvalExpr
                  (Vector.mapRange (2 * 4 - 1) fun i => var (F := F circomPrime) {index := oConvLD + i})
                  ((↑i + (1 : ℕ) : ℕ) : F circomPrime)) = 0) ∧
            (GroupedFlex.Assumptions vQuadFat.Nf vQuadFat.Nf
                { lhs := Vector.map (Expression.eval env.toEnvironment)
                    (Vector.mapFinRange 9 fun k =>
                      (if h : ↑k < 7 then var (F := F circomPrime) {index := oConvLD + ↑k} else 0)
                        + (if ↑k < 5 then cExp (8 * P256) ↑k else 0)),
                  rhs := Vector.map (Expression.eval env.toEnvironment)
                    (Vector.mapFinRange 9 fun k =>
                      qpCoeff (Vector.mapRange 4 fun i => var {index := oQs + i}) (var {index := oQst}) ↑k
                        + (if h : ↑k < 4 then input_var_T1_y[↑k] - input_var_A_y[↑k]
                            + Expression.const ((2 ^ 64 - 1 + limbOfNat cK ↑k : ℕ) : F circomPrime) else 0)) } ∧
              EqViaCarriesFlex.Spec 64
                { lhs := Vector.map (Expression.eval env.toEnvironment)
                    (Vector.mapFinRange 9 fun k =>
                      (if h : ↑k < 7 then var (F := F circomPrime) {index := oConvLD + ↑k} else 0)
                        + (if ↑k < 5 then cExp (8 * P256) ↑k else 0)),
                  rhs := Vector.map (Expression.eval env.toEnvironment)
                    (Vector.mapFinRange 9 fun k =>
                      qpCoeff (Vector.mapRange 4 fun i => var {index := oQs + i}) (var {index := oQst}) ↑k
                        + (if h : ↑k < 4 then input_var_T1_y[↑k] - input_var_A_y[↑k]
                            + Expression.const ((2 ^ 64 - 1 + limbOfNat cK ↑k : ℕ) : F circomPrime) else 0)) }) := by
  set lam1 : Var Emu (F circomPrime) := Vector.mapRange 4 fun i => var {index := oLam1 + i} with hlam1def
  set qs : Var Emu (F circomPrime) := Vector.mapRange 4 fun i => var {index := oQs + i} with hqsdef
  have hnormlam1 : BigInt.Normalized 64 (Vector.map (Expression.eval env.toEnvironment) lam1) := couple_norm env oLam1 _ hpin_lam1
  have hnormqs : BigInt.Normalized 64 (Vector.map (Expression.eval env.toEnvironment) qs) := couple_norm env oQs _ hpin_qs
  have hdtilfold : ∀ (j : ℕ) (hj : j < 4), (dtilOf input_var_T1_x input_var_A_x)[j]'hj
      = input_var_T1_x[j]'hj
          + (((twoPBorrowDigit j : ℕ) : F circomPrime) : Expression (F circomPrime))
          - input_var_A_x[j]'hj := by
    intro j hj
    rw [dtilOf, Vector.getElem_ofFn]
  have hdtilbound : ∀ i : Fin 4,
      (Expression.eval env.toEnvironment (dtilOf input_var_T1_x input_var_A_x)[i.val]).val < 3 * 2 ^ 64 := by
    intro i
    rw [hdtilfold i.val i.isLt]
    exact eval_dtil_lt env.toEnvironment input_var_T1_x input_var_A_x hxT1 hxA i.val i.isLt

  have hlt_lam1 : lamValEnv env input_var_T1_x input_var_A_x input_var_T1_y input_var_A_y < 2 ^ 256 :=
    lt_trans (lamValEnv_lt env input_var_T1_x input_var_A_x input_var_T1_y input_var_A_y) P256_lt256
  have hval_lam1 : BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) lam1)
      = lamValEnv env input_var_T1_x input_var_A_x input_var_T1_y input_var_A_y :=
    couple_value env oLam1 _ hlt_lam1 hpin_lam1
  have hval_qs : BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) qs)
      = slopeQuot env input_var_T1_x input_var_A_x input_var_T1_y input_var_A_y % 2 ^ 256 :=
    couple_value env oQs _ (Nat.mod_lt _ (by positivity)) hpin_qs

  have hSdtil : (∑ j : Fin 4,
        (Expression.eval env.toEnvironment (dtilOf input_var_T1_x input_var_A_x)[j.val]).val
          * 2 ^ (64 * j.val))
      = dFullVal env input_var_T1_x input_var_A_x := by
    have hdv := dtil_value env.toEnvironment input_var_T1_x input_var_A_x hxT1 hxA
    have hsum_eq : (∑ j : Fin 4,
          (Expression.eval env.toEnvironment (dtilOf input_var_T1_x input_var_A_x)[j.val]).val
            * 2 ^ (64 * j.val))
        = ∑ j : Fin 4, (Expression.eval env.toEnvironment
            (input_var_T1_x[j.val]'j.isLt
              + (((twoPBorrowDigit j.val : ℕ) : F circomPrime) : Expression (F circomPrime))
              - input_var_A_x[j.val]'j.isLt)).val * 2 ^ (64 * j.val) := by
      apply Finset.sum_congr rfl; intro j _; rw [hdtilfold j.val j.isLt]
    have hxAlt : BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) input_var_A_x) < 2 ^ 256 :=
      BigInt.value_lt hxA
    have hP256 : (2:ℕ) ^ 256 < P256 * 2 := by decide
    unfold dFullVal
    rw [evalEmu_eq_value env input_var_T1_x, evalEmu_eq_value env input_var_A_x, hsum_eq]
    omega

  have hchval : chVal env input_var_T1_y input_var_A_y
      = BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) input_var_T1_y) + 2 * P256
        - BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) input_var_A_y) := by
    unfold chVal
    rw [evalEmu_eq_value env input_var_T1_y, evalEmu_eq_value env input_var_A_y]
    have hyTlt : BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) input_var_T1_y) < 2 ^ 256 :=
      BigInt.value_lt hyT1
    omega

  have hlv : BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) lam1)
      = chVal env input_var_T1_y input_var_A_y * invModP (dFullVal env input_var_T1_x input_var_A_x) % P256 := by
    rw [hval_lam1, lamValEnv_chord env input_var_T1_x input_var_A_x input_var_T1_y input_var_A_y hne]

  have hchbound : chVal env input_var_T1_y input_var_A_y
      ≤ BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) lam1)
          * (∑ j : Fin 4,
              (Expression.eval env.toEnvironment (dtilOf input_var_T1_x input_var_A_x)[j.val]).val
                * 2 ^ (64 * j.val))
        + 8 * P256 := by
    have hyTlt : BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) input_var_T1_y) < 2 ^ 256 :=
      BigInt.value_lt hyT1
    have hP256 : (2:ℕ) ^ 256 < P256 * 2 := by decide
    rw [hchval]; omega

  have hrem : (BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) lam1)
          * (∑ j : Fin 4,
              (Expression.eval env.toEnvironment (dtilOf input_var_T1_x input_var_A_x)[j.val]).val
                * 2 ^ (64 * j.val))
        + 8 * P256
      - (BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) input_var_T1_y) + 2 * P256
          - BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) input_var_A_y))) % P256 = 0 := by
    have hkey := slope_num_mod_zero
      (BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) lam1))
      (∑ j : Fin 4,
        (Expression.eval env.toEnvironment (dtilOf input_var_T1_x input_var_A_x)[j.val]).val
          * 2 ^ (64 * j.val))
      0 (dFullVal env input_var_T1_x input_var_A_x) (chVal env input_var_T1_y input_var_A_y)
      (by rw [hSdtil]; ring) hlv hne (by simpa using hchbound)
    rw [hchval] at hkey
    simpa using hkey

  have hqv : BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) qs)
        + (Expression.eval env.toEnvironment (var {index := oQst})).val * 2 ^ 256
      = (BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) lam1)
            * (∑ j : Fin 4,
                (Expression.eval env.toEnvironment (dtilOf input_var_T1_x input_var_A_x)[j.val]).val
                  * 2 ^ (64 * j.val))
          + 8 * P256
        - (BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) input_var_T1_y) + 2 * P256
            - BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) input_var_A_y))) / P256 := by
    rw [hval_qs]
    show slopeQuot env input_var_T1_x input_var_A_x input_var_T1_y input_var_A_y % 2 ^ 256
      + (env.get oQst).val * 2 ^ 256 = _
    rw [hpin_qst]
    have hb := slopeQuot_top_bound env input_var_T1_x input_var_A_x input_var_T1_y input_var_A_y hxT1lt hyAlt
    have hQP : slopeQuot env input_var_T1_x input_var_A_x input_var_T1_y input_var_A_y / 2 ^ 256 < circomPrime :=
      lt_of_lt_of_le hb (le_of_lt (by decide : (2:ℕ) ^ 3 < circomPrime))
    rw [ZMod.val_natCast_of_lt hQP, quot_recompose]
    have hmod : dFullVal env input_var_T1_x input_var_A_x % P256 ≠ 0 := mod_P256_ne_zero_of_fp_ne hne
    rw [slopeQuot_chord_eq env input_var_T1_x input_var_A_x input_var_T1_y input_var_A_y hmod]
    rw [hval_lam1, hSdtil, hchval]

  have hpin' : ∀ k : Fin (2 * 4 - 1), env.get (oConvLD + k.val)
      = Expression.eval env.toEnvironment
          ((bigIntMulNoReduce lam1 (dtilOf input_var_T1_x input_var_A_x))[k.val]) := by
    intro k
    have := hpin_conv k; simpa only [Fin.getElem_fin, Vector.getElem_ofFn] using this
  have hP := MulMod.interpolatedMul_eval_bridge_uses env.toEnvironment oConvLD lam1
    (dtilOf input_var_T1_x input_var_A_x) hpin'
  have hqst64 : (Expression.eval env.toEnvironment (var {index := oQst})).val < 2 ^ 64 := by
    show ZMod.val (env.get oQst) < 2 ^ 64
    rw [hpin_qst]
    have hb := slopeQuot_top_bound env input_var_T1_x input_var_A_x input_var_T1_y input_var_A_y hxT1lt hyAlt
    have hQP : slopeQuot env input_var_T1_x input_var_A_x input_var_T1_y input_var_A_y / 2 ^ 256 < circomPrime :=
      lt_of_lt_of_le hb (le_of_lt (by decide : (2:ℕ) ^ 3 < circomPrime))
    rw [ZMod.val_natCast_of_lt hQP]
    exact lt_trans hb (by decide)
  have hqst2 : (Expression.eval env.toEnvironment (var {index := oQst})).val < 2 ^ 2 := by
    show ZMod.val (env.get oQst) < 2 ^ 2
    exact couple_rc env oQst _ 2 hpin_qst
      (slopeQuot_top_bound_chord env input_var_T1_x input_var_A_x input_var_T1_y input_var_A_y
        hxT1lt hyAlt hne) (by norm_num)
  have hdis := a2_discharge_fat env.toEnvironment lam1 (dtilOf input_var_T1_x input_var_A_x)
    input_var_T1_y input_var_A_y qs (var {index := oQst})
    (MulMod.interpolatedMul lam1 (dtilOf input_var_T1_x input_var_A_x) oConvLD).1 hP
    hnormlam1 hdtilbound hnormqs (lt_trans hqst2 (by norm_num)) hyT1 hyA
  have hspec := a2_spec_fat_complete env.toEnvironment lam1 (dtilOf input_var_T1_x input_var_A_x)
    (var {index := oQst}) qs input_var_T1_y input_var_A_y
    (MulMod.interpolatedMul lam1 (dtilOf input_var_T1_x input_var_A_x) oConvLD).1 hP
    hnormlam1 hdtilbound hnormqs hqst64 hyT1 hyA hqv hrem
  refine ⟨⟨trivial, hnormlam1⟩, ⟨trivial, hnormqs⟩, ?_, ?_, ?_, ?_⟩
  · exact hqst2
  · intro i
    rw [add_neg_eq_zero]
    exact MulMod.interpolatedMul_points_of_pins env.toEnvironment oConvLD lam1
      (dtilOf input_var_T1_x input_var_A_x) hpin' i
  · refine ⟨fun k => ?_, fun k => ?_⟩
    · have hk := hdis.1 k
      simp only [Vector.getElem_map, Vector.getElem_mapFinRange,
        MulMod.interpolatedMul_output, numLimbs, Vector.getElem_mapRange] at hk ⊢
      exact hk
    · exact hdis.2 k
  · simp only [EqViaCarriesFlex.Spec]
    simp only [MulMod.interpolatedMul_output, numLimbs, Vector.getElem_mapRange] at hspec
    exact hspec

set_option maxRecDepth 4000 in
/-- §BORROW-ROLLOUT (completeness Spec side): fat-limb analogue of
`c1_spec_complete` — no `d24`/`lp2` terms; `dtil2`'s weighted limb sum enters
through `hqv`/`hrem`/`hbound` as the raw `Σ`. -/
lemma c1_spec_fat_complete (env : Environment (F circomPrime))
    (lam2 dtil2 lam1 xA x1 : Var Emu (F circomPrime))
    (q3t : Expression (F circomPrime)) (q3 yT2 yA : Var Emu (F circomPrime))
    (P2 P1 : Vector (Expression (F circomPrime)) 7)
    (hP2 : ∀ k : Fin 7,
      Expression.eval env P2[k.val] = Expression.eval env (bigIntMulNoReduce lam2 dtil2)[k.val])
    (hP1 : ∀ k : Fin 7,
      Expression.eval env P1[k.val] = Expression.eval env (bigIntMulNoReduce lam1
        (Vector.ofFn fun i : Fin 4 =>
          xA[i.val]'i.isLt + ((2 ^ 64 - 1 : ℕ) : F circomPrime) - x1[i.val]'i.isLt))[k.val])
    (hlam2 : BigInt.Normalized 64 (Vector.map (Expression.eval env) lam2))
    (hdtil2 : ∀ i : Fin 4, (Expression.eval env dtil2[i.val]).val < 3 * 2 ^ 64)
    (hlam1 : BigInt.Normalized 64 (Vector.map (Expression.eval env) lam1))
    (hxA : BigInt.Normalized 64 (Vector.map (Expression.eval env) xA))
    (hx1 : BigInt.Normalized 64 (Vector.map (Expression.eval env) x1))
    (hq3 : BigInt.Normalized 64 (Vector.map (Expression.eval env) q3))
    (hq3t : (Expression.eval env q3t).val < 2 ^ 64)
    (hyT2 : BigInt.Normalized 64 (Vector.map (Expression.eval env) yT2))
    (hyA : BigInt.Normalized 64 (Vector.map (Expression.eval env) yA))
    (hqv : BigInt.value 64 (Vector.map (Expression.eval env) q3)
        + (Expression.eval env q3t).val * 2 ^ 256
      = (BigInt.value 64 (Vector.map (Expression.eval env) lam2)
            * (∑ j : Fin 4, (Expression.eval env dtil2[j.val]).val * 2 ^ (64 * j.val))
          + BigInt.value 64 (Vector.map (Expression.eval env) lam1)
              * (BigInt.value 64 (Vector.map (Expression.eval env) xA) + (2 ^ 256 - 1)
                  - BigInt.value 64 (Vector.map (Expression.eval env) x1))
          + 2 ^ 34 * P256
        - BigInt.value 64 (Vector.map (Expression.eval env) yT2)
        - BigInt.value 64 (Vector.map (Expression.eval env) yA)
        - c976 * BigInt.value 64 (Vector.map (Expression.eval env) lam1)) / P256)
    (hrem : (BigInt.value 64 (Vector.map (Expression.eval env) lam2)
            * (∑ j : Fin 4, (Expression.eval env dtil2[j.val]).val * 2 ^ (64 * j.val))
          + BigInt.value 64 (Vector.map (Expression.eval env) lam1)
              * (BigInt.value 64 (Vector.map (Expression.eval env) xA) + (2 ^ 256 - 1)
                  - BigInt.value 64 (Vector.map (Expression.eval env) x1))
          + 2 ^ 34 * P256
        - BigInt.value 64 (Vector.map (Expression.eval env) yT2)
        - BigInt.value 64 (Vector.map (Expression.eval env) yA)
        - c976 * BigInt.value 64 (Vector.map (Expression.eval env) lam1)) % P256 = 0)
    (hbound : BigInt.value 64 (Vector.map (Expression.eval env) yT2)
        + BigInt.value 64 (Vector.map (Expression.eval env) yA)
        + c976 * BigInt.value 64 (Vector.map (Expression.eval env) lam1)
      ≤ BigInt.value 64 (Vector.map (Expression.eval env) lam2)
            * (∑ j : Fin 4, (Expression.eval env dtil2[j.val]).val * 2 ^ (64 * j.val))
          + BigInt.value 64 (Vector.map (Expression.eval env) lam1)
              * (BigInt.value 64 (Vector.map (Expression.eval env) xA) + (2 ^ 256 - 1)
                  - BigInt.value 64 (Vector.map (Expression.eval env) x1))
          + 2 ^ 34 * P256) :
    polyValue 64 (Vector.map (Expression.eval env)
        (Vector.mapFinRange 10 fun k =>
          (if h : k.val < 7 then P2[k.val]'h + P1[k.val]'h else 0)
            + (if k.val < 5 then cExp (2 ^ 34 * P256) k.val else 0)))
      = polyValue 64 (Vector.map (Expression.eval env)
          (Vector.mapFinRange 10 fun k =>
            qpCoeff q3 q3t k.val
              + (if h : k.val < 4 then
                  yT2[k.val]'h + yA[k.val]'h + ((c976 : ℕ) : F circomPrime) * (lam1[k.val]'h) else 0))) := by
  rw [polyValue_c1_lhs_fat env lam2 dtil2 lam1 xA x1 P2 P1 hP2 hP1 hlam2 hdtil2 hlam1 hxA hx1,
      polyValue_c2b_rhs env q3 q3t yT2 yA lam1 hq3 hq3t hyT2 hyA hlam1]
  have hxd := xd_value env xA x1 hxA hx1
  set Sd := ∑ j : Fin 4, (Expression.eval env dtil2[j.val]).val * 2 ^ (64 * j.val) with hSddef
  set S := ∑ j : Fin 4, (Expression.eval env
      (xA[j.val]'j.isLt + ((2 ^ 64 - 1 : ℕ) : F circomPrime) - x1[j.val]'j.isLt)).val
        * 2 ^ (64 * j.val) with hSdef
  set vlam2 := BigInt.value 64 (Vector.map (Expression.eval env) lam2)
  set vlam1 := BigInt.value 64 (Vector.map (Expression.eval env) lam1)
  set vxA := BigInt.value 64 (Vector.map (Expression.eval env) xA)
  set vx1 := BigInt.value 64 (Vector.map (Expression.eval env) x1)
  set vyT2 := BigInt.value 64 (Vector.map (Expression.eval env) yT2)
  set vyA := BigInt.value 64 (Vector.map (Expression.eval env) yA)
  have hSeq : S = vxA + (2 ^ 256 - 1) - vx1 := by
    have hvx1 : vx1 < 2 ^ 256 := BigInt.value_lt hx1
    omega
  rw [hSeq] at *
  set N := vlam2 * Sd + vlam1 * (vxA + (2 ^ 256 - 1) - vx1) + 2 ^ 34 * P256
      - vyT2 - vyA - c976 * vlam1 with hNdef
  rw [hqv]
  have hdm := Nat.div_add_mod' N P256
  show vlam2 * Sd + vlam1 * (vxA + (2 ^ 256 - 1) - vx1) + 2 ^ 34 * P256
      = (N / P256) * P256 + vyT2 + vyA + c976 * vlam1
  omega

/-- §BORROW-ROLLOUT (completeness): replaces `siteC1d_complete`+`siteC1_complete`
for the new (6-conjunct) stageC1. `dtil2 = dtilOf xT2 x1` is wire-only, so
there are no `d2`/`d24`/`lp2` pins. -/
lemma siteC1_fat_complete (env : ProverEnvironment (F circomPrime))
    {oLam2 oLam1 oX1 oQ3 oQ3t oConvLX1 oConvLD2 : ℕ}
    (input_var_A_x input_var_A_y input_var_T2_x input_var_T2_y : Emu (Expression (F circomPrime)))
    (hxA : BigInt.Normalized 64 (Vector.map (Expression.eval env.toEnvironment) input_var_A_x))
    (hyA : BigInt.Normalized 64 (Vector.map (Expression.eval env.toEnvironment) input_var_A_y))
    (hxT2 : BigInt.Normalized 64 (Vector.map (Expression.eval env.toEnvironment) input_var_T2_x))
    (hyT2 : BigInt.Normalized 64 (Vector.map (Expression.eval env.toEnvironment) input_var_T2_y))
    (hlam1 : BigInt.Normalized 64 (Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange 4 fun i => var {index := oLam1 + i})))
    (hx1 : BigInt.Normalized 64 (Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange 4 fun i => var {index := oX1 + i})))
    (hxAlt : evalEmu env input_var_A_x < 2 ^ 256)
    (hxT2lt : evalEmu env input_var_T2_x < 2 ^ 256)
    (hlam1lt : evalEmu env (Vector.mapRange 4 fun i => var {index := oLam1 + i}) < P256)
    (hne2 : (dFullVal env input_var_T2_x (Vector.mapRange 4 fun i => var {index := oX1 + i})
      : Specs.Secp256k1.Fp) ≠ 0)
    (hpin_lam2 : ∀ i : Fin 4, env.get (oLam2 + ↑i)
      = (emuOfNat (lam2W env input_var_A_x input_var_A_y (Vector.mapRange 4 fun i => var {index := oX1 + i})
          (Vector.mapRange 4 fun i => var {index := oLam1 + i}) input_var_T2_x input_var_T2_y))[↑i])
    (hpin_q3 : ∀ i : Fin 4, env.get (oQ3 + ↑i)
      = (emuOfNat (slope2Quot env input_var_A_x input_var_A_y (Vector.mapRange 4 fun i => var {index := oX1 + i})
          (Vector.mapRange 4 fun i => var {index := oLam1 + i}) input_var_T2_x input_var_T2_y % 2 ^ 256))[↑i])
    (hpin_q3t : env.get oQ3t
      = ((slope2Quot env input_var_A_x input_var_A_y (Vector.mapRange 4 fun i => var {index := oX1 + i})
          (Vector.mapRange 4 fun i => var {index := oLam1 + i}) input_var_T2_x input_var_T2_y / 2 ^ 256 : ℕ) : F circomPrime))
    (hpin_convLX1 : ∀ i : Fin (2 * 4 - 1), env.get (oConvLX1 + ↑i)
      = (Vector.ofFn fun k : Fin (2 * 4 - 1) =>
          Expression.eval env.toEnvironment
            (bigIntMulNoReduce
              (Vector.mapRange 4 fun i => var (F := F circomPrime) {index := oLam1 + i})
              (Vector.ofFn fun i : Fin 4 =>
                input_var_A_x[↑i] + Expression.const ((2 ^ 64 - 1 : ℕ) : F circomPrime)
                  - var (F := F circomPrime) {index := oX1 + ↑i}))[↑k])[↑i])
    (hpin_convLD2 : ∀ i : Fin (2 * 4 - 1), env.get (oConvLD2 + ↑i)
      = (Vector.ofFn fun k : Fin (2 * 4 - 1) =>
          Expression.eval env.toEnvironment
            (bigIntMulNoReduce
              (Vector.mapRange 4 fun i => var (F := F circomPrime) {index := oLam2 + i})
              (dtilOf input_var_T2_x (Vector.mapRange 4 fun i => var (F := F circomPrime) {index := oX1 + i})))[↑k])[↑i]) :
    (Normalize.Assumptions (Vector.map (Expression.eval env.toEnvironment)
          (Vector.mapRange 4 fun i => var {index := oLam2 + i})) ∧
        Normalize.Spec 64 (Vector.map (Expression.eval env.toEnvironment)
          (Vector.mapRange 4 fun i => var {index := oLam2 + i}))) ∧
      (Normalize.Assumptions (Vector.map (Expression.eval env.toEnvironment)
            (Vector.mapRange 4 fun i => var {index := oQ3 + i})) ∧
          Normalize.Spec 64 (Vector.map (Expression.eval env.toEnvironment)
            (Vector.mapRange 4 fun i => var {index := oQ3 + i}))) ∧
        ZMod.val (env.get oQ3t) < 2 ^ 3 ∧
          (∀ i : Fin (2 * 4 - 1),
              Expression.eval env.toEnvironment (GroupedFlex.polyEvalExpr
                  (Vector.mapRange 4 fun i => var (F := F circomPrime) {index := oLam1 + i})
                  ((↑i + (1 : ℕ) : ℕ) : F circomPrime))
                * Expression.eval env.toEnvironment (GroupedFlex.polyEvalExpr
                  (Vector.ofFn fun i : Fin 4 =>
                    input_var_A_x[↑i] + Expression.const ((2 ^ 64 - 1 : ℕ) : F circomPrime)
                      - var (F := F circomPrime) {index := oX1 + ↑i})
                  ((↑i + (1 : ℕ) : ℕ) : F circomPrime))
                + -Expression.eval env.toEnvironment (GroupedFlex.polyEvalExpr
                  (Vector.mapRange (2 * 4 - 1) fun i => var (F := F circomPrime) {index := oConvLX1 + i})
                  ((↑i + (1 : ℕ) : ℕ) : F circomPrime)) = 0) ∧
            (∀ i : Fin (2 * 4 - 1),
                Expression.eval env.toEnvironment (GroupedFlex.polyEvalExpr
                    (Vector.mapRange 4 fun i => var (F := F circomPrime) {index := oLam2 + i})
                    ((↑i + (1 : ℕ) : ℕ) : F circomPrime))
                  * Expression.eval env.toEnvironment (GroupedFlex.polyEvalExpr
                    (dtilOf input_var_T2_x (Vector.mapRange 4 fun i => var (F := F circomPrime) {index := oX1 + i}))
                    ((↑i + (1 : ℕ) : ℕ) : F circomPrime))
                  + -Expression.eval env.toEnvironment (GroupedFlex.polyEvalExpr
                    (Vector.mapRange (2 * 4 - 1) fun i => var (F := F circomPrime) {index := oConvLD2 + i})
                    ((↑i + (1 : ℕ) : ℕ) : F circomPrime)) = 0) ∧
              (GroupedFlex.Assumptions vWideFat.Nf vWideFat.Nf
                  { lhs := Vector.map (Expression.eval env.toEnvironment)
                      (Vector.mapFinRange 10 fun k =>
                        (if h : ↑k < 7 then var (F := F circomPrime) {index := oConvLD2 + ↑k}
                            + var (F := F circomPrime) {index := oConvLX1 + ↑k} else 0)
                          + (if ↑k < 5 then cExp (2 ^ 34 * P256) ↑k else 0)),
                    rhs := Vector.map (Expression.eval env.toEnvironment)
                      (Vector.mapFinRange 10 fun k =>
                        qpCoeff (Vector.mapRange 4 fun i => var {index := oQ3 + i}) (var {index := oQ3t}) ↑k
                          + (if h : ↑k < 4 then input_var_T2_y[↑k] + input_var_A_y[↑k]
                              + ((c976 : ℕ) : F circomPrime) * var (F := F circomPrime) {index := oLam1 + ↑k} else 0)) } ∧
                EqViaCarriesFlex.Spec 64
                  { lhs := Vector.map (Expression.eval env.toEnvironment)
                      (Vector.mapFinRange 10 fun k =>
                        (if h : ↑k < 7 then var (F := F circomPrime) {index := oConvLD2 + ↑k}
                            + var (F := F circomPrime) {index := oConvLX1 + ↑k} else 0)
                          + (if ↑k < 5 then cExp (2 ^ 34 * P256) ↑k else 0)),
                    rhs := Vector.map (Expression.eval env.toEnvironment)
                      (Vector.mapFinRange 10 fun k =>
                        qpCoeff (Vector.mapRange 4 fun i => var {index := oQ3 + i}) (var {index := oQ3t}) ↑k
                          + (if h : ↑k < 4 then input_var_T2_y[↑k] + input_var_A_y[↑k]
                              + ((c976 : ℕ) : F circomPrime) * var (F := F circomPrime) {index := oLam1 + ↑k} else 0)) }) := by
  set lam2 : Var Emu (F circomPrime) := Vector.mapRange 4 fun i => var {index := oLam2 + i} with hlam2def
  set lam1 : Var Emu (F circomPrime) := Vector.mapRange 4 fun i => var {index := oLam1 + i} with hlam1def
  set x1 : Var Emu (F circomPrime) := Vector.mapRange 4 fun i => var {index := oX1 + i} with hx1def
  set q3 : Var Emu (F circomPrime) := Vector.mapRange 4 fun i => var {index := oQ3 + i} with hq3def
  set xd1 : Var Emu (F circomPrime) := Vector.ofFn fun i : Fin 4 =>
    input_var_A_x[i.val]'i.isLt + Expression.const ((2 ^ 64 - 1 : ℕ) : F circomPrime) - x1[i.val]'i.isLt with hxd1def
  have hnormlam2 : BigInt.Normalized 64 (Vector.map (Expression.eval env.toEnvironment) lam2) := couple_norm env oLam2 _ hpin_lam2
  have hnormq3 : BigInt.Normalized 64 (Vector.map (Expression.eval env.toEnvironment) q3) := couple_norm env oQ3 _ hpin_q3
  have hlam1fold : ∀ (i : ℕ) (hi : i < 4), (lam1[i]'hi) = var (F := F circomPrime) {index := oLam1 + i} :=
    fun i hi => Vector.getElem_mapRange i hi
  have hx1fold : ∀ (i : ℕ) (hi : i < 4), (x1[i]'hi) = var (F := F circomPrime) {index := oX1 + i} :=
    fun i hi => Vector.getElem_mapRange i hi

  have hdtilfold : ∀ (j : ℕ) (hj : j < 4), (dtilOf input_var_T2_x x1)[j]'hj
      = input_var_T2_x[j]'hj
          + (((twoPBorrowDigit j : ℕ) : F circomPrime) : Expression (F circomPrime))
          - x1[j]'hj := by
    intro j hj
    rw [dtilOf, Vector.getElem_ofFn]
  have hdtilbound : ∀ i : Fin 4,
      (Expression.eval env.toEnvironment (dtilOf input_var_T2_x x1)[i.val]).val < 3 * 2 ^ 64 := by
    intro i
    rw [hdtilfold i.val i.isLt]
    exact eval_dtil_lt env.toEnvironment input_var_T2_x x1 hxT2 hx1 i.val i.isLt
  have hSdtil : (∑ j : Fin 4,
        (Expression.eval env.toEnvironment (dtilOf input_var_T2_x x1)[j.val]).val
          * 2 ^ (64 * j.val))
      = dFullVal env input_var_T2_x x1 := by
    have hdv := dtil_value env.toEnvironment input_var_T2_x x1 hxT2 hx1
    have hsum_eq : (∑ j : Fin 4,
          (Expression.eval env.toEnvironment (dtilOf input_var_T2_x x1)[j.val]).val
            * 2 ^ (64 * j.val))
        = ∑ j : Fin 4, (Expression.eval env.toEnvironment
            (input_var_T2_x[j.val]'j.isLt
              + (((twoPBorrowDigit j.val : ℕ) : F circomPrime) : Expression (F circomPrime))
              - x1[j.val]'j.isLt)).val * 2 ^ (64 * j.val) := by
      apply Finset.sum_congr rfl; intro j _; rw [hdtilfold j.val j.isLt]
    have hx1lt' : BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) x1) < 2 ^ 256 :=
      BigInt.value_lt hx1
    have hP256 : (2:ℕ) ^ 256 < P256 * 2 := by decide
    unfold dFullVal
    rw [evalEmu_eq_value env input_var_T2_x, evalEmu_eq_value env x1, hsum_eq]
    omega

  have hlt_lam2 : lam2W env input_var_A_x input_var_A_y x1 lam1 input_var_T2_x input_var_T2_y < 2 ^ 256 :=
    lt_trans (lam2W_lt env input_var_A_x input_var_A_y x1 lam1 input_var_T2_x input_var_T2_y) P256_lt256
  have hval_lam2 : BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) lam2)
      = lam2W env input_var_A_x input_var_A_y x1 lam1 input_var_T2_x input_var_T2_y :=
    couple_value env oLam2 _ hlt_lam2 hpin_lam2
  have hval_q3 : BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) q3)
      = slope2Quot env input_var_A_x input_var_A_y x1 lam1 input_var_T2_x input_var_T2_y % 2 ^ 256 :=
    couple_value env oQ3 _ (Nat.mod_lt _ (by positivity)) hpin_q3

  have hpin2' : ∀ k : Fin (2 * 4 - 1), env.get (oConvLD2 + k.val)
      = Expression.eval env.toEnvironment ((bigIntMulNoReduce lam2 (dtilOf input_var_T2_x x1))[k.val]) := by
    intro k
    have := hpin_convLD2 k; simpa only [Fin.getElem_fin, Vector.getElem_ofFn] using this
  have hPb2 := MulMod.interpolatedMul_eval_bridge_uses env.toEnvironment oConvLD2 lam2
    (dtilOf input_var_T2_x x1) hpin2'

  have hxd_eq : xd1 = (Vector.ofFn fun i : Fin 4 =>
        input_var_A_x[i.val]'i.isLt + Expression.const ((2 ^ 64 - 1 : ℕ) : F circomPrime)
          - var (F := F circomPrime) { index := oX1 + i.val }) := by
    rw [hxd1def]
    apply Vector.ext; intro j hj
    simp only [Vector.getElem_ofFn, hx1fold]
  have hpin1' : ∀ k : Fin (2 * 4 - 1), env.get (oConvLX1 + k.val)
      = Expression.eval env.toEnvironment ((bigIntMulNoReduce lam1 xd1)[k.val]) := by
    intro k
    rw [hxd_eq]
    have := hpin_convLX1 k; simpa only [Fin.getElem_fin, Vector.getElem_ofFn] using this
  have hPb1 := MulMod.interpolatedMul_eval_bridge_uses env.toEnvironment oConvLX1 lam1 xd1 hpin1'
  have hq3t : (Expression.eval env.toEnvironment (var {index := oQ3t})).val < 2 ^ 64 := by
    show ZMod.val (env.get oQ3t) < 2 ^ 64
    rw [hpin_q3t]
    have hb := slope2Quot_top_bound env input_var_A_x input_var_A_y x1 lam1 input_var_T2_x input_var_T2_y hlam1lt hxT2lt hxAlt
    have hQP : slope2Quot env input_var_A_x input_var_A_y x1 lam1 input_var_T2_x input_var_T2_y / 2 ^ 256 < circomPrime :=
      lt_of_lt_of_le hb (le_of_lt (by decide : (2:ℕ) ^ 3 < circomPrime))
    rw [ZMod.val_natCast_of_lt hQP]
    exact lt_trans hb (by decide)

  have hlam1v : BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) lam1) < P256 := by
    rw [← evalEmu_eq_value]; exact hlam1lt
  have hyAv : BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) input_var_A_y) < 2 ^ 256 :=
    BigInt.value_lt hyA
  have hyT2v : BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) input_var_T2_y) < 2 ^ 256 :=
    BigInt.value_lt hyT2

  set y1v := y1W env input_var_A_x input_var_A_y x1 lam1 with hy1vdef
  have hy1coup : y1v = (BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) lam1)
        * (BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) input_var_A_x) + (2 ^ 256 - 1)
            - BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) x1))
      + 2 ^ 35 * P256 - BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) input_var_A_y)
      - c976 * BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) lam1)) % P256 := by
    rw [hy1vdef]; unfold y1W
    rw [evalEmu_eq_value env lam1, evalEmu_eq_value env input_var_A_x, evalEmu_eq_value env x1,
      evalEmu_eq_value env input_var_A_y]

  have hlam2coup : BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) lam2)
      = (2 * P256 + BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) input_var_T2_y) - y1v)
        * invModP (dFullVal env input_var_T2_x x1) % P256 := by
    rw [hval_lam2]; unfold lam2W
    rw [evalEmu_eq_value env input_var_T2_y]

  have hrem : (BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) lam2)
          * (∑ j : Fin 4,
              (Expression.eval env.toEnvironment (dtilOf input_var_T2_x x1)[j.val]).val
                * 2 ^ (64 * j.val))
        + BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) lam1)
            * (BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) input_var_A_x) + (2 ^ 256 - 1)
                - BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) x1))
        + 2 ^ 34 * P256
        - BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) input_var_T2_y)
        - BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) input_var_A_y)
        - c976 * BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) lam1)) % P256 = 0 := by
    have hy1b : BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) input_var_A_y)
        + c976 * BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) lam1)
        ≤ BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) lam1)
            * (BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) input_var_A_x) + (2 ^ 256 - 1)
                - BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) x1))
          + 2 ^ 35 * P256 := by
      have hP := two_pow255_lt_P256
      have h1 : c976 * BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) lam1) ≤ c976 * P256 :=
        Nat.mul_le_mul_left _ (le_of_lt hlam1v)
      have h2 : (c976 : ℕ) = 2 ^ 32 + 976 := rfl
      have : BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) input_var_A_y)
          + c976 * BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) lam1) ≤ 2 ^ 35 * P256 := by
        nlinarith [hlam1v, hyAv, hP, P256_pos]
      omega
    have hnbound : BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) input_var_T2_y)
        + BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) input_var_A_y)
        + c976 * BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) lam1)
        ≤ BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) lam2)
              * (∑ j : Fin 4,
                  (Expression.eval env.toEnvironment (dtilOf input_var_T2_x x1)[j.val]).val
                    * 2 ^ (64 * j.val))
            + BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) lam1)
                * (BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) input_var_A_x) + (2 ^ 256 - 1)
                    - BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) x1))
            + 0 * BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) lam2) * 2 ^ 256
            + 2 ^ 34 * P256 := by
      have hP := two_pow255_lt_P256
      have h1 : c976 * BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) lam1) ≤ c976 * P256 :=
        Nat.mul_le_mul_left _ (le_of_lt hlam1v)
      have h2 : (c976 : ℕ) = 2 ^ 32 + 976 := rfl
      have hle : BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) input_var_T2_y)
          + BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) input_var_A_y)
          + c976 * BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) lam1) ≤ 2 ^ 34 * P256 := by
        nlinarith [hlam1v, hyAv, hyT2v, hP, P256_pos]
      omega
    have hkey := slope2_num_mod_zero
      (BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) lam2))
      (∑ j : Fin 4,
        (Expression.eval env.toEnvironment (dtilOf input_var_T2_x x1)[j.val]).val * 2 ^ (64 * j.val))
      0 (dFullVal env input_var_T2_x x1)
      (BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) lam1))
      (BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) input_var_A_x) + (2 ^ 256 - 1)
        - BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) x1))
      y1v
      (BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) input_var_T2_y))
      (BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) input_var_A_y))
      (by rw [hSdtil]; ring) hlam2coup hy1coup hne2 hy1b hnbound
    simpa using hkey

  have hbound : BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) input_var_T2_y)
      + BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) input_var_A_y)
      + c976 * BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) lam1)
    ≤ BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) lam2)
          * (∑ j : Fin 4,
              (Expression.eval env.toEnvironment (dtilOf input_var_T2_x x1)[j.val]).val
                * 2 ^ (64 * j.val))
        + BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) lam1)
            * (BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) input_var_A_x) + (2 ^ 256 - 1)
                - BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) x1))
        + 2 ^ 34 * P256 := by
    have hP := two_pow255_lt_P256
    have h1 : c976 * BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) lam1) ≤ c976 * P256 :=
      Nat.mul_le_mul_left _ (le_of_lt hlam1v)
    have h2 : (c976 : ℕ) = 2 ^ 32 + 976 := rfl
    have hle : BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) input_var_T2_y)
        + BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) input_var_A_y)
        + c976 * BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) lam1) ≤ 2 ^ 34 * P256 := by
      nlinarith [hlam1v, hyAv, hyT2v, hP, P256_pos]
    omega

  have hqv : BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) q3)
        + (Expression.eval env.toEnvironment (var {index := oQ3t})).val * 2 ^ 256
      = (BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) lam2)
            * (∑ j : Fin 4,
                (Expression.eval env.toEnvironment (dtilOf input_var_T2_x x1)[j.val]).val
                  * 2 ^ (64 * j.val))
          + BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) lam1)
              * (BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) input_var_A_x) + (2 ^ 256 - 1)
                  - BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) x1))
          + 2 ^ 34 * P256
          - BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) input_var_T2_y)
          - BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) input_var_A_y)
          - c976 * BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) lam1)) / P256 := by
    rw [hval_q3]
    show slope2Quot env input_var_A_x input_var_A_y x1 lam1 input_var_T2_x input_var_T2_y % 2 ^ 256
      + (env.get oQ3t).val * 2 ^ 256 = _
    rw [hpin_q3t]
    have hb := slope2Quot_top_bound env input_var_A_x input_var_A_y x1 lam1 input_var_T2_x input_var_T2_y hlam1lt hxT2lt hxAlt
    have hQP : slope2Quot env input_var_A_x input_var_A_y x1 lam1 input_var_T2_x input_var_T2_y / 2 ^ 256 < circomPrime :=
      lt_of_lt_of_le hb (le_of_lt (by decide : (2:ℕ) ^ 3 < circomPrime))
    rw [ZMod.val_natCast_of_lt hQP, quot_recompose]
    unfold slope2Quot
    rw [evalEmu_eq_value env lam1, evalEmu_eq_value env input_var_A_x, evalEmu_eq_value env x1,
      evalEmu_eq_value env input_var_T2_y, evalEmu_eq_value env input_var_A_y,
      ← hval_lam2, ← hSdtil]
  have hq3t3 : (Expression.eval env.toEnvironment (var {index := oQ3t})).val < 2 ^ 3 := by
    show ZMod.val (env.get oQ3t) < 2 ^ 3
    exact couple_rc env oQ3t _ 3 hpin_q3t
      (slope2Quot_top_bound env input_var_A_x input_var_A_y x1 lam1 input_var_T2_x input_var_T2_y hlam1lt hxT2lt hxAlt) (by norm_num)
  have hdis := c1_discharge_fat env.toEnvironment lam2 (dtilOf input_var_T2_x x1) lam1 input_var_A_x x1
    input_var_T2_y input_var_A_y q3 (var {index := oQ3t})
    (MulMod.interpolatedMul lam2 (dtilOf input_var_T2_x x1) oConvLD2).1
    (MulMod.interpolatedMul lam1 xd1 oConvLX1).1 hPb2 hPb1 hnormlam2 hdtilbound hlam1 hxA hx1 hyT2 hyA hnormq3 hq3t3
  have hspec := c1_spec_fat_complete env.toEnvironment lam2 (dtilOf input_var_T2_x x1) lam1 input_var_A_x x1
    (var {index := oQ3t}) q3 input_var_T2_y input_var_A_y
    (MulMod.interpolatedMul lam2 (dtilOf input_var_T2_x x1) oConvLD2).1
    (MulMod.interpolatedMul lam1 xd1 oConvLX1).1 hPb2 hPb1 hnormlam2 hdtilbound hlam1 hxA hx1 hnormq3 hq3t hyT2 hyA hqv hrem hbound
  refine ⟨⟨trivial, hnormlam2⟩, ⟨trivial, hnormq3⟩, ?_, ?_, ?_, ?_, ?_⟩
  · exact couple_rc env oQ3t _ 3 hpin_q3t
      (slope2Quot_top_bound env input_var_A_x input_var_A_y x1 lam1 input_var_T2_x input_var_T2_y hlam1lt hxT2lt hxAlt) (by norm_num)
  · intro i
    rw [add_neg_eq_zero]
    have h := MulMod.interpolatedMul_points_of_pins env.toEnvironment oConvLX1 lam1 xd1 hpin1' i
    rw [hxd_eq] at h
    simpa only [Fin.getElem_fin] using h
  · intro i
    rw [add_neg_eq_zero]
    exact MulMod.interpolatedMul_points_of_pins env.toEnvironment oConvLD2 lam2
      (dtilOf input_var_T2_x x1) hpin2' i
  · refine ⟨fun k => ?_, fun k => ?_⟩
    · have hk := hdis.1 k
      simp only [Vector.getElem_map, Vector.getElem_mapFinRange,
        MulMod.interpolatedMul_output, numLimbs, Vector.getElem_mapRange] at hk ⊢
      exact hk
    · have hk := hdis.2 k
      simp only [Vector.getElem_map, Vector.getElem_mapFinRange, hlam1fold] at hk ⊢; exact hk
  · simp only [EqViaCarriesFlex.Spec]
    simp only [MulMod.interpolatedMul_output, numLimbs, Vector.getElem_mapRange, hlam1fold] at hspec
    exact hspec


lemma lamValEnv_slope_fp (env : ProverEnvironment (F circomPrime))
    (xT xA yT yA : Var Emu (F circomPrime))
    (hne : (dFullVal env xT xA : Specs.Secp256k1.Fp) ≠ 0) :
    (lamValEnv env xT xA yT yA : Specs.Secp256k1.Fp) * (dFullVal env xT xA : Specs.Secp256k1.Fp)
      = (chVal env yT yA : Specs.Secp256k1.Fp) := by
  have hm : dFullVal env xT xA % P256 ≠ 0 := mod_P256_ne_zero_of_fp_ne hne
  rw [lamValEnv_chord env xT xA yT yA hne, invModP, ZMod.natCast_mod]
  push_cast [ZMod.natCast_val, ZMod.cast_id]
  rw [mul_assoc, inv_mul_cancel₀ hne, mul_one]

lemma x3Val_fp (env : ProverEnvironment (F circomPrime))
    (xT xA yT yA : Var Emu (F circomPrime))
    (hxA : evalEmu env xA < 2 ^ 256) (hxT : evalEmu env xT < 2 ^ 256) :
    (x3Val env xT xA yT yA : Specs.Secp256k1.Fp)
      = (lamValEnv env xT xA yT yA : Specs.Secp256k1.Fp) ^ 2
        - (evalEmu env xA : Specs.Secp256k1.Fp) - (evalEmu env xT : Specs.Secp256k1.Fp) := by
  unfold x3Val
  have hlv : lamValEnv env xT xA yT yA < P256 := lamValEnv_lt env xT xA yT yA
  have hP := two_pow255_lt_P256
  have hb : evalEmu env xA + evalEmu env xT
      ≤ lamValEnv env xT xA yT yA * lamValEnv env xT xA yT yA + 4 * P256 := by
    have : (4:ℕ) * P256 > 2 * 2 ^ 256 := by
      have := P256_lt256; omega
    omega
  rw [ZMod.natCast_mod, Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast
  have hp : (P256 : Specs.Secp256k1.Fp) = 0 := ZMod.natCast_self _
  rw [hp]; ring

lemma emuVal_sub_fp (env : ProverEnvironment (F circomPrime)) (a b : Var Emu (F circomPrime))
    (hb : evalEmu env b < 2 ^ 256) :
    ((2 * P256 + evalEmu env a - evalEmu env b : ℕ) : Specs.Secp256k1.Fp)
      = decodeFe (Vector.map (Expression.eval env.toEnvironment) a)
        - decodeFe (Vector.map (Expression.eval env.toEnvironment) b) := by
  have hP := two_pow255_lt_P256
  rw [Nat.cast_sub (by omega)]
  push_cast
  have hp : (P256 : Specs.Secp256k1.Fp) = 0 := ZMod.natCast_self _
  rw [decodeFe, decodeFe]
  simp only [limbBits] at *
  rw [evalEmu_eq_value env a, evalEmu_eq_value env b] at *
  rw [hp]; ring

end PairAdd
end Solution.Secp256k1ScalarMulFixedBase

end DonorFile2_3

-- Adapted donor module: FoldQuot
section DonorFile2_4

/-!
# Folded (pseudo-Mersenne) quotient layout

secp256k1's prime satisfies `P256 = 2 ^ 256 - cF` with `cF = 2 ^ 32 + 977`, i.e.
`2 ^ 256 ≡ cF (mod P256)`.  A 4-limb product `a * b` is produced by
`interpolatedMul` as `7` unreduced convolution positions `P 0 … P 6`.  Folding
positions `4, 5, 6` back onto `0, 1, 2` with the *constant* multiplier `cF` is a
free affine recombination that shrinks the value from `< 2^518` to `< 2^323`, so
the modular quotient fits in **one** wire below `2^68` instead of a full 4-limb
BigInt needing a 256-bit range check.

`foldLhs P v` is the folded left-hand side (plus a constant `v`, always a
multiple of `P256` chosen large enough to keep the quotient non-negative) and
`foldRhs q a b c` is `q * P256 + a + b + c`, both living on `L = 4` positions.
-/

namespace Solution.Secp256k1ScalarMulFixedBase
namespace FoldQuot

open CompactAdd (cExp)
open Challenge.CostR1CS
open Solution.Secp256k1ScalarMulFixedBase.Limbs

/-- `2 ^ 256 - P256`. -/
def cF : ℕ := 2 ^ 32 + 977

lemma p_add_cF : P256 + cF = 2 ^ 256 := by decide

/-- Wide constant limbs on 4 positions: position 3 absorbs limbs 3 and 4. -/
def offLimb (v k : ℕ) : ℕ :=
  if k = 3 then limbOfNat v 3 + 2 ^ 64 * limbOfNat v 4 else limbOfNat v k

def wExp (v k : ℕ) : Expression (F circomPrime) := ((offLimb v k : ℕ) : F circomPrime)

/-- Folded left-hand side: convolution positions `4,5,6` scaled by `cF` and
added onto positions `0,1,2`, plus the constant `v`. -/
def foldLhs (P : Vector (Expression (F circomPrime)) 7) (v k : ℕ) :
    Expression (F circomPrime) :=
  (if h : k < 4 then P[k]'(by omega) else 0)
    + (if h : k < 3 then ((cF : ℕ) : F circomPrime) * (P[k + 4]'(by omega)) else 0)
    + wExp v k

/-- Right-hand side: single-wire quotient times the (constant) prime, plus three
normalized 4-limb values. -/
def foldRhs (q : Expression (F circomPrime)) (a b c : Var Emu (F circomPrime)) (k : ℕ) :
    Expression (F circomPrime) :=
  q * cExp P256 k + (if h : k < 4 then a[k]'h + b[k]'h + c[k]'h else 0)

/-- The high half of a convolution, as a natural number. -/
def convHigh (env : Environment (F circomPrime)) (P : Vector (Expression (F circomPrime)) 7) : ℕ :=
  ∑ t : Fin 3, (Expression.eval env (P[t.val + 4]'(by omega))).val * 2 ^ (64 * t.val)

/-- `convHigh` only depends on the evaluations of the two multiplicands. -/
lemma convHigh_eq_of_eval_eq {e e' : Environment (F circomPrime)}
    {a b : Var Emu (F circomPrime)}
    (ha : a.map (Expression.eval e) = a.map (Expression.eval e'))
    (hb : b.map (Expression.eval e) = b.map (Expression.eval e')) :
    convHigh e (bigIntMulNoReduce a b) = convHigh e' (bigIntMulNoReduce a b) := by
  have hae : ∀ (i : ℕ) (hi : i < 4),
      Expression.eval e (a[i]'hi) = Expression.eval e' (a[i]'hi) := by
    intro i hi
    have := congrArg (fun w : Vector (F circomPrime) 4 => w[i]'hi) ha
    simpa only [Vector.getElem_map] using this
  have hbe : ∀ (i : ℕ) (hi : i < 4),
      Expression.eval e (b[i]'hi) = Expression.eval e' (b[i]'hi) := by
    intro i hi
    have := congrArg (fun w : Vector (F circomPrime) 4 => w[i]'hi) hb
    simpa only [Vector.getElem_map] using this
  have hcoeff : ∀ k : Fin (2 * 4 - 1),
      Expression.eval e ((bigIntMulNoReduce a b)[k.val])
        = Expression.eval e' ((bigIntMulNoReduce a b)[k.val]) := by
    intro k
    rw [eval_bigIntMulNoReduce_coeff e a b k, eval_bigIntMulNoReduce_coeff e' a b k]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : i.val ≤ k.val ∧ k.val - i.val < 4
    · rw [dif_pos h, dif_pos h, hae i.val i.isLt, hbe (k.val - i.val) h.2]
    · rw [dif_neg h, dif_neg h]
  simp only [convHigh]
  apply Finset.sum_congr rfl
  intro t _
  have h := hcoeff ⟨t.val + 4, by omega⟩
  simp only [Fin.val_mk] at h
  exact congrArg (fun z : F circomPrime => z.val * 2 ^ (64 * t.val)) h

/-! ### Affineness -/

theorem affine_wExp (v k : ℕ) : Affine (wExp v k) := Affine.const _

theorem affine_foldLhs {P : Vector (Expression (F circomPrime)) 7}
    (hP : ∀ (j : ℕ) (hj : j < 7), Affine (P[j]'hj)) (v k : ℕ) : Affine (foldLhs P v k) := by
  unfold foldLhs
  refine Affine.add (Affine.add ?_ ?_) (affine_wExp _ _)
  · split
    · exact hP _ (by omega)
    · exact Affine.zero
  · split
    · exact Affine.fconst_mul _ (hP _ (by omega))
    · exact Affine.zero

theorem affine_foldRhs {q : Expression (F circomPrime)} {a b c : Var Emu (F circomPrime)}
    (hq : Affine q) (ha : AffineW a) (hb : AffineW b) (hc : AffineW c) (k : ℕ) :
    Affine (foldRhs q a b c k) := by
  unfold foldRhs
  refine Affine.add (Affine.mul_deg0 hq (CompactAdd.degree_cExp _ _)) ?_
  split
  · exact Affine.add (Affine.add (ha _ (by assumption)) (hb _ (by assumption)))
      (hc _ (by assumption))
  · exact Affine.zero

/-! ### Environment stability (for computable witnesses) -/

lemma foldLhs_eval_stable {e e' : Environment (F circomPrime)}
    {P : Vector (Expression (F circomPrime)) 7}
    (hP : ∀ (j : ℕ) (hj : j < 7), Expression.eval e (P[j]'hj) = Expression.eval e' (P[j]'hj))
    (v k : ℕ) :
    Expression.eval e (foldLhs P v k) = Expression.eval e' (foldLhs P v k) := by
  unfold foldLhs
  by_cases h4 : k < 4 <;> by_cases h3 : k < 3
  · simp only [dif_pos h4, dif_pos h3, wExp, Expression.eval,
      hP k (by omega), hP (k + 4) (by omega)]
  · simp only [dif_pos h4, dif_neg h3, wExp, Expression.eval, hP k (by omega)]
  · omega
  · simp only [dif_neg h4, dif_neg h3, wExp, Expression.eval]

lemma foldRhs_eval_stable {e e' : Environment (F circomPrime)}
    {q : Expression (F circomPrime)} {a b c : Var Emu (F circomPrime)}
    (hq : Expression.eval e q = Expression.eval e' q)
    (ha : ∀ (j : ℕ) (hj : j < 4), Expression.eval e (a[j]'hj) = Expression.eval e' (a[j]'hj))
    (hb : ∀ (j : ℕ) (hj : j < 4), Expression.eval e (b[j]'hj) = Expression.eval e' (b[j]'hj))
    (hc : ∀ (j : ℕ) (hj : j < 4), Expression.eval e (c[j]'hj) = Expression.eval e' (c[j]'hj))
    (k : ℕ) :
    Expression.eval e (foldRhs q a b c k) = Expression.eval e' (foldRhs q a b c k) := by
  unfold foldRhs
  by_cases hk : k < 4
  · simp only [dif_pos hk, cExp, Expression.eval, hq, ha k hk, hb k hk, hc k hk]
  · simp only [dif_neg hk, cExp, Expression.eval, hq]

/-! ### Constant-offset bookkeeping -/

lemma offLimb_sum (v : ℕ) (hv : v < 2 ^ 320) :
    ∑ k ∈ Finset.range 4, offLimb v k * 2 ^ (64 * k) = v := by
  have hdec := limb_decomp_mod 64 5 v
  rw [show (64 : ℕ) * 5 = 320 from rfl, Nat.mod_eq_of_lt hv] at hdec
  rw [show (∑ k ∈ Finset.range 4, offLimb v k * 2 ^ (64 * k))
      = ∑ i ∈ Finset.range 5, (v / 2 ^ (64 * i) % 2 ^ 64) * 2 ^ (64 * i) from ?_]
  · exact hdec
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero, offLimb, limbOfNat, limbBits]
    norm_num
    ring

lemma offLimb_lt (v : ℕ) (hv : v < 2 ^ 258) (k : ℕ) : offLimb v k < 2 ^ 67 := by
  have hl3 : limbOfNat v 3 < 2 ^ 64 := by
    have := limbOfNat_lt v 3; simpa [limbBits] using this
  have hl4 : limbOfNat v 4 < 4 := by
    have hdiv : v / 2 ^ 256 < 4 := by
      have h258 : (2 : ℕ) ^ 258 = 4 * 2 ^ 256 := by
        rw [show (258 : ℕ) = 2 + 256 from rfl, pow_add]
        norm_num
      exact Nat.div_lt_of_lt_mul (by omega)
    have : limbOfNat v 4 ≤ v / 2 ^ 256 := by
      simp only [limbOfNat, limbBits, show 64 * 4 = 256 from rfl]
      exact Nat.mod_le _ _
    omega
  unfold offLimb
  split
  · omega
  · have := limbOfNat_lt v k
    simp only [limbBits] at this
    omega

lemma val_wExp (env : Environment (F circomPrime)) (v k : ℕ) (hv : v < 2 ^ 258) :
    (Expression.eval env (wExp v k)).val = offLimb v k := by
  show (((offLimb v k : ℕ) : F circomPrime)).val = offLimb v k
  refine ZMod.val_natCast_of_lt ?_
  have h1 := offLimb_lt v hv k
  have h2 : (2 : ℕ) ^ 67 < circomPrime := by decide
  omega

/-! ### Coefficient bounds -/

lemma eval_foldLhs_cast (env : Environment (F circomPrime))
    (P : Vector (Expression (F circomPrime)) 7) (v : ℕ) (k : ℕ) (hk : k < 4) :
    Expression.eval env (foldLhs P v k)
      = ((((Expression.eval env (P[k]'(by omega))).val
          + (if h : k < 3 then cF * (Expression.eval env (P[k + 4]'(by omega))).val else 0)
          + offLimb v k : ℕ)) : F circomPrime) := by
  unfold foldLhs wExp
  rw [dif_pos hk]
  by_cases h3 : k < 3
  · rw [dif_pos h3, dif_pos h3]
    simp only [Expression.eval]
    push_cast
    rw [ZMod.natCast_val, ZMod.natCast_val, ZMod.cast_id, ZMod.cast_id]
  · rw [dif_neg h3, dif_neg h3]
    simp only [Expression.eval]
    push_cast
    rw [ZMod.natCast_val, ZMod.cast_id]

lemma val_foldLhs (env : Environment (F circomPrime))
    (P : Vector (Expression (F circomPrime)) 7) (v : ℕ) (hv : v < 2 ^ 258)
    (hP : ∀ k : Fin 7, (Expression.eval env (P[k.val])).val < 4 * 2 ^ 128) (k : ℕ) (hk : k < 4) :
    (Expression.eval env (foldLhs P v k)).val
      = (Expression.eval env (P[k]'(by omega))).val
        + (if h : k < 3 then cF * (Expression.eval env (P[k + 4]'(by omega))).val else 0)
        + offLimb v k := by
  have hA : (Expression.eval env (P[k]'(by omega))).val < 4 * 2 ^ 128 := hP ⟨k, by omega⟩
  have hoff := offLimb_lt v hv k
  have hcF : cF = 2 ^ 32 + 977 := rfl
  have hbound : (Expression.eval env (P[k]'(by omega))).val
      + (if h : k < 3 then cF * (Expression.eval env (P[k + 4]'(by omega))).val else 0)
      + offLimb v k < circomPrime := by
    by_cases h3 : k < 3
    · rw [dif_pos h3]
      have hB : (Expression.eval env (P[k + 4]'(by omega))).val < 4 * 2 ^ 128 :=
        hP ⟨k + 4, by omega⟩
      have hprime : (4 : ℕ) * 2 ^ 128 + (2 ^ 32 + 977) * (4 * 2 ^ 128) + 2 ^ 67 < circomPrime := by
        decide
      have : cF * (Expression.eval env (P[k + 4]'(by omega))).val
          ≤ (2 ^ 32 + 977) * (4 * 2 ^ 128) := by
        rw [hcF]; exact Nat.mul_le_mul_left _ (by omega)
      omega
    · rw [dif_neg h3]
      have hprime : (4 : ℕ) * 2 ^ 128 + 2 ^ 67 < circomPrime := by decide
      omega
  rw [eval_foldLhs_cast env P v k hk, ZMod.val_natCast_of_lt hbound]

lemma foldLhs_lt_aux (env : Environment (F circomPrime))
    (P : Vector (Expression (F circomPrime)) 7) (v : ℕ) (hv : v < 2 ^ 258)
    (hP : ∀ k : Fin 7, (Expression.eval env (P[k.val])).val < 4 * 2 ^ 128)
    (k : ℕ) (hk : k < 3) (Cb N : ℕ)
    (hB : (Expression.eval env (P[k + 4]'(by omega))).val ≤ Cb)
    (hN : 4 * 2 ^ 128 + (2 ^ 32 + 977) * Cb + 2 ^ 67 ≤ N) :
    (Expression.eval env (foldLhs P v k)).val < N := by
  have hoff := offLimb_lt v hv k
  have hA : (Expression.eval env (P[k]'(by omega))).val < 4 * 2 ^ 128 := hP ⟨k, by omega⟩
  have hval := val_foldLhs env P v hv hP k (by omega)
  rw [hval, dif_pos hk]
  have hcF : cF = 2 ^ 32 + 977 := rfl
  have hmul : cF * (Expression.eval env (P[k + 4]'(by omega))).val
      ≤ (2 ^ 32 + 977) * Cb := by
    rw [hcF]; exact Nat.mul_le_mul_left _ hB
  omega

lemma foldLhs_lt (env : Environment (F circomPrime))
    (P : Vector (Expression (F circomPrime)) 7) (v : ℕ) (hv : v < 2 ^ 258)
    (hP : ∀ k : Fin 7, (Expression.eval env (P[k.val])).val < 4 * 2 ^ 128)
    (hPhi : ∀ k : Fin 7, 5 ≤ k.val →
      (Expression.eval env (P[k.val])).val < (7 - k.val) * 2 ^ 128)
    (k : Fin 4) :
    (Expression.eval env (foldLhs P v k.val)).val < vFoldL.Nf k.val := by
  have hk : k.val = 0 ∨ k.val = 1 ∨ k.val = 2 ∨ k.val = 3 := by have := k.isLt; omega
  rcases hk with h | h | h | h
  · rw [h, show vFoldL.Nf 0 = 2 ^ 162 + 2 ^ 140 from by norm_num [vFoldL, nfFoldL]]
    refine foldLhs_lt_aux env P v hv hP 0 (by omega) (4 * 2 ^ 128) _ ?_ (by norm_num)
    exact le_of_lt (hP ⟨0 + 4, by omega⟩)
  · rw [h, show vFoldL.Nf 1 = 2 ^ 161 + 2 ^ 141 from by norm_num [vFoldL, nfFoldL]]
    refine foldLhs_lt_aux env P v hv hP 1 (by omega) (2 * 2 ^ 128) _ ?_ (by norm_num)
    have h5 : (Expression.eval env (P[1 + 4]'(by omega))).val < 2 * 2 ^ 128 :=
      hPhi ⟨5, by omega⟩ (Nat.le_refl 5)
    exact le_of_lt h5
  · rw [h, show vFoldL.Nf 2 = 2 ^ 160 + 2 ^ 140 from by norm_num [vFoldL, nfFoldL]]
    refine foldLhs_lt_aux env P v hv hP 2 (by omega) (1 * 2 ^ 128) _ ?_ (by norm_num)
    have h6 : (Expression.eval env (P[2 + 4]'(by omega))).val < 1 * 2 ^ 128 :=
      hPhi ⟨6, by omega⟩ (by norm_num)
    exact le_of_lt h6
  · have hoff := offLimb_lt v hv k.val
    have hA : (Expression.eval env (P[k.val]'(by omega))).val < 4 * 2 ^ 128 :=
      hP ⟨k.val, by omega⟩
    have hval := val_foldLhs env P v hv hP k.val k.isLt
    rw [hval, dif_neg (by omega : ¬ k.val < 3),
      show vFoldL.Nf k.val = 2 ^ 131 from by rw [h]; norm_num [vFoldL, nfFoldL]]
    have : (4 : ℕ) * 2 ^ 128 + 2 ^ 67 < 2 ^ 131 := by norm_num
    omega

lemma eval_foldRhs_cast (env : Environment (F circomPrime)) (q : Expression (F circomPrime))
    (a b c : Var Emu (F circomPrime)) (k : ℕ) (hk : k < 4) :
    Expression.eval env (foldRhs q a b c k)
      = ((((Expression.eval env q).val * limbOfNat P256 k
          + (Expression.eval env (a[k]'hk)).val + (Expression.eval env (b[k]'hk)).val
          + (Expression.eval env (c[k]'hk)).val : ℕ)) : F circomPrime) := by
  unfold foldRhs
  rw [dif_pos hk]
  simp only [Expression.eval, CompactAdd.cExp]
  push_cast
  rw [ZMod.natCast_val, ZMod.natCast_val, ZMod.natCast_val, ZMod.natCast_val,
    ZMod.cast_id, ZMod.cast_id, ZMod.cast_id, ZMod.cast_id]
  ring

lemma val_foldRhs (env : Environment (F circomPrime)) (q : Expression (F circomPrime))
    (a b c : Var Emu (F circomPrime))
    (hq : (Expression.eval env q).val < 2 ^ 68)
    (ha : BigInt.Normalized 64 (Vector.map (Expression.eval env) a))
    (hb : BigInt.Normalized 64 (Vector.map (Expression.eval env) b))
    (hc : BigInt.Normalized 64 (Vector.map (Expression.eval env) c))
    (k : ℕ) (hk : k < 4) :
    (Expression.eval env (foldRhs q a b c k)).val
      = (Expression.eval env q).val * limbOfNat P256 k
        + (Expression.eval env (a[k]'hk)).val + (Expression.eval env (b[k]'hk)).val
        + (Expression.eval env (c[k]'hk)).val := by
  have hav := PairAdd.digit_lt_of_norm' env a ha k hk
  have hbv := PairAdd.digit_lt_of_norm' env b hb k hk
  have hcv := PairAdd.digit_lt_of_norm' env c hc k hk
  have hlimb : limbOfNat P256 k < 2 ^ 64 := by
    have := limbOfNat_lt P256 k; simpa [limbBits] using this
  have hmul : (Expression.eval env q).val * limbOfNat P256 k ≤ 2 ^ 68 * 2 ^ 64 :=
    Nat.mul_le_mul (by omega) (by omega)
  have hbig : (2 : ℕ) ^ 68 * 2 ^ 64 + 3 * 2 ^ 64 < circomPrime := by decide
  rw [eval_foldRhs_cast env q a b c k hk, ZMod.val_natCast_of_lt (by omega)]

lemma foldRhs_lt (env : Environment (F circomPrime)) (q : Expression (F circomPrime))
    (a b c : Var Emu (F circomPrime))
    (hq : (Expression.eval env q).val < 2 ^ 68)
    (ha : BigInt.Normalized 64 (Vector.map (Expression.eval env) a))
    (hb : BigInt.Normalized 64 (Vector.map (Expression.eval env) b))
    (hc : BigInt.Normalized 64 (Vector.map (Expression.eval env) c))
    (k : Fin 4) :
    (Expression.eval env (foldRhs q a b c k.val)).val < vFoldR.Nf k.val := by
  have hav := PairAdd.digit_lt_of_norm' env a ha k.val k.isLt
  have hbv := PairAdd.digit_lt_of_norm' env b hb k.val k.isLt
  have hcv := PairAdd.digit_lt_of_norm' env c hc k.val k.isLt
  have hlimb : limbOfNat P256 k.val < 2 ^ 64 := by
    have := limbOfNat_lt P256 k.val; simpa [limbBits] using this
  have hmul : (Expression.eval env q).val * limbOfNat P256 k.val ≤ 2 ^ 68 * 2 ^ 64 :=
    Nat.mul_le_mul (by omega) (by omega)
  have hNf : vFoldR.Nf k.val = 2 ^ 133 := by
    show (if k.val < 4 then 2 ^ 133 else 1) = 2 ^ 133
    rw [if_pos k.isLt]
  have hbig : (2 : ℕ) ^ 68 * 2 ^ 64 + 3 * 2 ^ 64 < 2 ^ 133 := by decide
  rw [val_foldRhs env q a b c hq ha hb hc k.val k.isLt, hNf]
  omega

/-! ### Splitting a convolution into low part and folded high part -/

/-- The low four positions of a 7-position convolution. -/
def convLow (env : Environment (F circomPrime)) (P : Vector (Expression (F circomPrime)) 7) : ℕ :=
  ∑ t : Fin 4, (Expression.eval env (P[t.val]'(by omega))).val * 2 ^ (64 * t.val)

set_option exponentiation.threshold 1200 in
lemma polyValue_split4 (env : Environment (F circomPrime))
    (P : Vector (Expression (F circomPrime)) 7) :
    polyValue 64 (Vector.map (Expression.eval env) P)
      = convLow env P + 2 ^ 256 * convHigh env P := by
  simp only [polyValue, convLow, convHigh, Vector.getElem_map, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Fin.isValue, Fin.val_zero, Fin.val_succ]
  ring

lemma convLow_lt (env : Environment (F circomPrime)) (P : Vector (Expression (F circomPrime)) 7)
    (hP : ∀ k : Fin 7, (Expression.eval env (P[k.val])).val < 4 * 2 ^ 128) :
    convLow env P < 2 ^ 322 + 2 ^ 259 := by
  have h0 : (Expression.eval env (P[0]'(by omega))).val < 4 * 2 ^ 128 := hP ⟨0, by omega⟩
  have h1 : (Expression.eval env (P[1]'(by omega))).val < 4 * 2 ^ 128 := hP ⟨1, by omega⟩
  have h2 : (Expression.eval env (P[2]'(by omega))).val < 4 * 2 ^ 128 := hP ⟨2, by omega⟩
  have h3 : (Expression.eval env (P[3]'(by omega))).val < 4 * 2 ^ 128 := hP ⟨3, by omega⟩
  simp only [convLow, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ]
  norm_num
  omega

lemma convHigh_lt (env : Environment (F circomPrime)) (P : Vector (Expression (F circomPrime)) 7)
    (hP : ∀ k : Fin 7, (Expression.eval env (P[k.val])).val < 4 * 2 ^ 128) :
    convHigh env P < 2 ^ 259 := by
  have h4 : (Expression.eval env (P[4]'(by omega))).val < 4 * 2 ^ 128 := hP ⟨4, by omega⟩
  have h5 : (Expression.eval env (P[5]'(by omega))).val < 4 * 2 ^ 128 := hP ⟨5, by omega⟩
  have h6 : (Expression.eval env (P[6]'(by omega))).val < 4 * 2 ^ 128 := hP ⟨6, by omega⟩
  simp only [convHigh, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ]
  norm_num
  omega

/-! ### Polynomial values -/

set_option exponentiation.threshold 1200 in
lemma polyValue_foldLhs (env : Environment (F circomPrime))
    (P : Vector (Expression (F circomPrime)) 7) (v : ℕ) (hv : v < 2 ^ 258)
    (hP : ∀ k : Fin 7, (Expression.eval env (P[k.val])).val < 4 * 2 ^ 128) :
    polyValue 64 (Vector.map (Expression.eval env)
          (Vector.mapFinRange 4 fun k : Fin 4 => foldLhs P v k.val))
        + P256 * convHigh env P
      = polyValue 64 (Vector.map (Expression.eval env) P) + v := by
  have e0 := val_foldLhs env P v hv hP 0 (by omega)
  have e1 := val_foldLhs env P v hv hP 1 (by omega)
  have e2 := val_foldLhs env P v hv hP 2 (by omega)
  have e3 := val_foldLhs env P v hv hP 3 (by omega)
  rw [dif_pos (by omega : (0 : ℕ) < 3)] at e0
  rw [dif_pos (by omega : (1 : ℕ) < 3)] at e1
  rw [dif_pos (by omega : (2 : ℕ) < 3)] at e2
  rw [dif_neg (by omega : ¬ (3 : ℕ) < 3)] at e3
  have hoff : offLimb v 0 + offLimb v 1 * 2 ^ 64 + offLimb v 2 * 2 ^ 128
      + offLimb v 3 * 2 ^ 192 = v := by
    have h := offLimb_sum v (by omega)
    simpa only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.mul_zero, pow_zero,
      Nat.mul_one, zero_add] using h
  have hA : polyValue 64 (Vector.map (Expression.eval env)
        (Vector.mapFinRange 4 fun k : Fin 4 => foldLhs P v k.val))
      = convLow env P + cF * convHigh env P + v := by
    simp only [polyValue, Vector.getElem_map, Vector.getElem_mapFinRange, Fin.sum_univ_succ,
      Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ, convLow, convHigh]
    rw [e0, e1, e2, e3]
    simp only [Nat.mul_zero, pow_zero, Nat.mul_one, add_zero, zero_add]
    ring_nf
    omega
  have hsplit := polyValue_split4 env P
  have hpc : P256 + cF = 2 ^ 256 := p_add_cF
  have hmix : cF * convHigh env P + P256 * convHigh env P = 2 ^ 256 * convHigh env P := by
    rw [← Nat.add_mul, Nat.add_comm cF P256, hpc]
  rw [hA, hsplit]
  omega

set_option exponentiation.threshold 1200 in
lemma polyValue_foldRhs (env : Environment (F circomPrime)) (q : Expression (F circomPrime))
    (a b c : Var Emu (F circomPrime))
    (hq : (Expression.eval env q).val < 2 ^ 68)
    (ha : BigInt.Normalized 64 (Vector.map (Expression.eval env) a))
    (hb : BigInt.Normalized 64 (Vector.map (Expression.eval env) b))
    (hc : BigInt.Normalized 64 (Vector.map (Expression.eval env) c)) :
    polyValue 64 (Vector.map (Expression.eval env)
          (Vector.mapFinRange 4 fun k : Fin 4 => foldRhs q a b c k.val))
      = (Expression.eval env q).val * P256
        + BigInt.value 64 (Vector.map (Expression.eval env) a)
        + BigInt.value 64 (Vector.map (Expression.eval env) b)
        + BigInt.value 64 (Vector.map (Expression.eval env) c) := by
  have e0 := val_foldRhs env q a b c hq ha hb hc 0 (by omega)
  have e1 := val_foldRhs env q a b c hq ha hb hc 1 (by omega)
  have e2 := val_foldRhs env q a b c hq ha hb hc 2 (by omega)
  have e3 := val_foldRhs env q a b c hq ha hb hc 3 (by omega)
  have hva := MulMod.value_map_eval (B := 64) env a
  have hvb := MulMod.value_map_eval (B := 64) env b
  have hvc := MulMod.value_map_eval (B := 64) env c
  have hlimb : limbOfNat P256 0 + limbOfNat P256 1 * 2 ^ 64 + limbOfNat P256 2 * 2 ^ 128
      + limbOfNat P256 3 * 2 ^ 192 = P256 := by
    have h := limb_sum_P256
    simpa only [numLimbs, limbBits, Finset.sum_range_succ, Finset.sum_range_zero,
      Nat.mul_zero, pow_zero, Nat.mul_one, zero_add] using h
  simp only [polyValue, Vector.getElem_map, Vector.getElem_mapFinRange, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ] at hva hvb hvc ⊢
  rw [e0, e1, e2, e3, hva, hvb, hvc]
  simp only [Nat.mul_zero, pow_zero, Nat.mul_one, add_zero, zero_add]
  set l0 := limbOfNat P256 0 with hl0
  set l1 := limbOfNat P256 1 with hl1
  set l2 := limbOfNat P256 2 with hl2
  set l3 := limbOfNat P256 3 with hl3
  rw [← hlimb]
  ring

/-! ### Certificate inversion

The folded quotient `q` is pinned by the very identity it appears in, and
`P256` is a compile-time constant, so `q` can be written directly as an affine
expression over already-allocated wires instead of being witnessed.
-/

lemma natCast_val_F (x : F circomPrime) : ((x.val : ℕ) : F circomPrime) = x :=
  ZMod.natCast_zmod_val x

/-- The weight `2 ^ (64 * k)` as a field constant. -/
def wPow (k : ℕ) : F circomPrime := ((2 ^ (64 * k) : ℕ) : F circomPrime)

/-- `∑_{k<4} foldLhs P v k * 2 ^ (64 k)` as an expression. -/
def lhsPoly (P : Vector (Expression (F circomPrime)) 7) (v : ℕ) : Expression (F circomPrime) :=
  foldLhs P v 0 + wPow 1 * foldLhs P v 1 + wPow 2 * foldLhs P v 2 + wPow 3 * foldLhs P v 3

/-- `∑_{k<4} (a k + b k + c k) * 2 ^ (64 k)` as an expression. -/
def tailPoly (a b c : Var Emu (F circomPrime)) : Expression (F circomPrime) :=
  (a[0] + b[0] + c[0]) + wPow 1 * (a[1] + b[1] + c[1])
    + wPow 2 * (a[2] + b[2] + c[2]) + wPow 3 * (a[3] + b[3] + c[3])

/-- The folded quotient recovered as an affine expression. -/
def foldQInv (P : Vector (Expression (F circomPrime)) 7) (v : ℕ)
    (a b c : Var Emu (F circomPrime)) : Expression (F circomPrime) :=
  (((P256 : ℕ) : F circomPrime)⁻¹) * (lhsPoly P v - tailPoly a b c)

theorem affine_lhsPoly {P : Vector (Expression (F circomPrime)) 7}
    (hP : ∀ (j : ℕ) (hj : j < 7), Affine (P[j]'hj)) (v : ℕ) : Affine (lhsPoly P v) := by
  unfold lhsPoly
  exact Affine.add (Affine.add (Affine.add (affine_foldLhs hP v 0)
    (Affine.fconst_mul _ (affine_foldLhs hP v 1)))
    (Affine.fconst_mul _ (affine_foldLhs hP v 2)))
    (Affine.fconst_mul _ (affine_foldLhs hP v 3))

theorem affine_tailPoly {a b c : Var Emu (F circomPrime)}
    (ha : AffineW a) (hb : AffineW b) (hc : AffineW c) : Affine (tailPoly a b c) := by
  unfold tailPoly
  have h : ∀ (k : ℕ) (hk : k < 4), Affine (a[k]'hk + b[k]'hk + c[k]'hk) := fun k hk =>
    Affine.add (Affine.add (ha k hk) (hb k hk)) (hc k hk)
  exact Affine.add (Affine.add (Affine.add (h 0 (by decide))
    (Affine.fconst_mul _ (h 1 (by decide))))
    (Affine.fconst_mul _ (h 2 (by decide))))
    (Affine.fconst_mul _ (h 3 (by decide)))

theorem affine_foldQInv {P : Vector (Expression (F circomPrime)) 7}
    (hP : ∀ (j : ℕ) (hj : j < 7), Affine (P[j]'hj)) (v : ℕ)
    {a b c : Var Emu (F circomPrime)}
    (ha : AffineW a) (hb : AffineW b) (hc : AffineW c) :
    Affine (foldQInv P v a b c) :=
  Affine.fconst_mul _ (Affine.sub (affine_lhsPoly hP v) (affine_tailPoly ha hb hc))

lemma eval_lhsPoly (env : Environment (F circomPrime))
    (P : Vector (Expression (F circomPrime)) 7) (v : ℕ) :
    Expression.eval env (lhsPoly P v)
      = ((polyValue 64 (Vector.map (Expression.eval env)
          (Vector.mapFinRange 4 fun k : Fin 4 => foldLhs P v k.val)) : ℕ) : F circomPrime) := by
  simp only [polyValue, Vector.getElem_map, Vector.getElem_mapFinRange, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ, lhsPoly, wPow, Expression.eval]
  push_cast [natCast_val_F]
  ring

lemma eval_tailPoly (env : Environment (F circomPrime)) (a b c : Var Emu (F circomPrime)) :
    Expression.eval env (tailPoly a b c)
      = ((BigInt.value 64 (Vector.map (Expression.eval env) a)
            + BigInt.value 64 (Vector.map (Expression.eval env) b)
            + BigInt.value 64 (Vector.map (Expression.eval env) c) : ℕ) : F circomPrime) := by
  have hva := MulMod.value_map_eval (B := 64) env a
  have hvb := MulMod.value_map_eval (B := 64) env b
  have hvc := MulMod.value_map_eval (B := 64) env c
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ] at hva hvb hvc
  rw [hva, hvb, hvc]
  simp only [tailPoly, wPow, Expression.eval]
  push_cast [natCast_val_F]
  ring

lemma P256_cast_ne_zero : ((P256 : ℕ) : F circomPrime) ≠ 0 := by decide

/-- Given the natural-number certificate identity, the inverted quotient
expression evaluates to exactly the honest quotient. -/
lemma eval_foldQInv_of_identity (env : Environment (F circomPrime))
    (P : Vector (Expression (F circomPrime)) 7) (v : ℕ)
    (a b c : Var Emu (F circomPrime)) (q0 : ℕ)
    (hid : polyValue 64 (Vector.map (Expression.eval env)
          (Vector.mapFinRange 4 fun k : Fin 4 => foldLhs P v k.val))
        = q0 * P256 + BigInt.value 64 (Vector.map (Expression.eval env) a)
          + BigInt.value 64 (Vector.map (Expression.eval env) b)
          + BigInt.value 64 (Vector.map (Expression.eval env) c)) :
    Expression.eval env (foldQInv P v a b c) = ((q0 : ℕ) : F circomPrime) := by
  have hL := eval_lhsPoly env P v
  have hT := eval_tailPoly env a b c
  have hkey : Expression.eval env (lhsPoly P v) - Expression.eval env (tailPoly a b c)
      = ((q0 : ℕ) : F circomPrime) * ((P256 : ℕ) : F circomPrime) := by
    rw [hL, hT, hid]; push_cast; ring
  have hinv : (((P256 : ℕ) : F circomPrime))⁻¹ * ((P256 : ℕ) : F circomPrime) = 1 :=
    inv_mul_cancel₀ P256_cast_ne_zero
  simp only [foldQInv, Expression.eval]
  linear_combination (((P256 : ℕ) : F circomPrime))⁻¹ * hkey
    + ((q0 : ℕ) : F circomPrime) * hinv

/-! ### Soundness -/

/-- Convolution positions of `lam * lam` are bounded by `4 * 2^128`. -/
lemma conv_coeff_lt (env : Environment (F circomPrime)) (lam : Var Emu (F circomPrime))
    (P : Vector (Expression (F circomPrime)) 7)
    (hP : ∀ k : Fin 7,
      Expression.eval env P[k.val] = Expression.eval env (bigIntMulNoReduce lam lam)[k.val])
    (hlam : BigInt.Normalized 64 (Vector.map (Expression.eval env) lam)) :
    ∀ k : Fin 7, (Expression.eval env (P[k.val])).val < 4 * 2 ^ 128 := by
  intro k
  have hdig := PairAdd.digit_lt_of_norm env lam hlam
  rw [hP k]
  exact val_bigIntMulNoReduce_coeff_lt env lam lam k hdig hdig (by decide)

/-- The top two convolution positions of `lam * lam` carry only `2` resp. `1`
term, so they are bounded by `2 * 2^128` resp. `2^128`. -/
lemma conv_coeff_hi (env : Environment (F circomPrime)) (lam : Var Emu (F circomPrime))
    (P : Vector (Expression (F circomPrime)) 7)
    (hP : ∀ k : Fin 7,
      Expression.eval env P[k.val] = Expression.eval env (bigIntMulNoReduce lam lam)[k.val])
    (hlam : BigInt.Normalized 64 (Vector.map (Expression.eval env) lam)) :
    ∀ k : Fin 7, 5 ≤ k.val → (Expression.eval env (P[k.val])).val < (7 - k.val) * 2 ^ 128 := by
  intro k hk
  have hdig := PairAdd.digit_lt_of_norm env lam hlam
  have h2 := hdig ⟨2, by omega⟩
  have h3 := hdig ⟨3, by omega⟩
  have hmul23 : (Expression.eval env lam[2]).val * (Expression.eval env lam[3]).val < 2 ^ 128 := by
    have := Nat.mul_lt_mul'' h2 h3
    simpa using this
  have hmul32 : (Expression.eval env lam[3]).val * (Expression.eval env lam[2]).val < 2 ^ 128 := by
    have := Nat.mul_lt_mul'' h3 h2
    simpa using this
  have hmul33 : (Expression.eval env lam[3]).val * (Expression.eval env lam[3]).val < 2 ^ 128 := by
    have := Nat.mul_lt_mul'' h3 h3
    simpa using this
  rw [hP k, val_bigIntMulNoReduce_coeff (B := 64) env lam lam k hdig hdig (by decide)]
  have hk56 : k.val = 5 ∨ k.val = 6 := by have := k.isLt; omega
  rcases hk56 with h5 | h6
  · rw [h5]
    simp only [Fin.sum_univ_four]
    norm_num
    omega
  · rw [h6]
    simp only [Fin.sum_univ_four]
    norm_num
    omega

/-- Bound discharge for the two `GroupedFlex.Assumptions` families. -/
lemma fold_discharge (env : Environment (F circomPrime))
    (lam a b c : Var Emu (F circomPrime)) (q : Expression (F circomPrime))
    (P : Vector (Expression (F circomPrime)) 7)
    (hP : ∀ k : Fin 7,
      Expression.eval env P[k.val] = Expression.eval env (bigIntMulNoReduce lam lam)[k.val])
    (hlam : BigInt.Normalized 64 (Vector.map (Expression.eval env) lam))
    (ha : BigInt.Normalized 64 (Vector.map (Expression.eval env) a))
    (hb : BigInt.Normalized 64 (Vector.map (Expression.eval env) b))
    (hc : BigInt.Normalized 64 (Vector.map (Expression.eval env) c))
    (hq : (Expression.eval env q).val < 2 ^ 68) :
    (∀ k : Fin 4,
        ((Vector.map (Expression.eval env)
          (Vector.mapFinRange 4 fun k : Fin 4 => foldLhs P (4 * P256) k.val))[k.val]).val
        < vFoldL.Nf k.val)
    ∧ (∀ k : Fin 4,
        ((Vector.map (Expression.eval env)
          (Vector.mapFinRange 4 fun k : Fin 4 => foldRhs q a b c k.val))[k.val]).val
        < vFoldR.Nf k.val) := by
  have hPb := conv_coeff_lt env lam P hP hlam
  have hPhi := conv_coeff_hi env lam P hP hlam
  constructor
  · intro k
    rw [Vector.getElem_map, Vector.getElem_mapFinRange]
    exact foldLhs_lt env P (4 * P256) (by decide) hPb hPhi k
  · intro k
    rw [Vector.getElem_map, Vector.getElem_mapFinRange]
    exact foldRhs_lt env q a b c hq ha hb hc k

/-- The field-level consequence of the folded identity. -/
lemma fold_identity (env : Environment (F circomPrime))
    (lam a b c : Var Emu (F circomPrime)) (q : Expression (F circomPrime))
    (P : Vector (Expression (F circomPrime)) 7)
    (hP : ∀ k : Fin 7,
      Expression.eval env P[k.val] = Expression.eval env (bigIntMulNoReduce lam lam)[k.val])
    (hlam : BigInt.Normalized 64 (Vector.map (Expression.eval env) lam))
    (ha : BigInt.Normalized 64 (Vector.map (Expression.eval env) a))
    (hb : BigInt.Normalized 64 (Vector.map (Expression.eval env) b))
    (hc : BigInt.Normalized 64 (Vector.map (Expression.eval env) c))
    (hq : (Expression.eval env q).val < 2 ^ 68)
    (hspec : polyValue 64 (Vector.map (Expression.eval env)
          (Vector.mapFinRange 4 fun k : Fin 4 => foldLhs P (4 * P256) k.val))
        = polyValue 64 (Vector.map (Expression.eval env)
          (Vector.mapFinRange 4 fun k : Fin 4 => foldRhs q a b c k.val))) :
    decodeFe (Vector.map (Expression.eval env) a)
      = decodeFe (Vector.map (Expression.eval env) lam) ^ 2
        - decodeFe (Vector.map (Expression.eval env) b)
        - decodeFe (Vector.map (Expression.eval env) c) := by
  have hPb := conv_coeff_lt env lam P hP hlam
  have hdig := PairAdd.digit_lt_of_norm env lam hlam
  have hL := polyValue_foldLhs env P (4 * P256) (by decide) hPb
  have hR := polyValue_foldRhs env q a b c hq ha hb hc
  have hpv : polyValue 64 (Vector.map (Expression.eval env) P)
      = BigInt.value 64 (Vector.map (Expression.eval env) lam)
        * BigInt.value 64 (Vector.map (Expression.eval env) lam) := by
    rw [← MulMod.polyValue_mul_eq env lam lam hdig hdig (by decide)]
    simp only [polyValue, Vector.getElem_map]
    exact Finset.sum_congr rfl fun i _ => by rw [hP i]
  rw [hspec, hR, hpv] at hL
  have hnat : (Expression.eval env q).val * P256
      + BigInt.value 64 (Vector.map (Expression.eval env) a)
      + BigInt.value 64 (Vector.map (Expression.eval env) b)
      + BigInt.value 64 (Vector.map (Expression.eval env) c)
      + P256 * convHigh env P
      = BigInt.value 64 (Vector.map (Expression.eval env) lam)
        * BigInt.value 64 (Vector.map (Expression.eval env) lam) + 4 * P256 := hL
  have hcast := congrArg (Nat.cast : ℕ → Specs.Secp256k1.Fp) hnat
  push_cast at hcast
  rw [show ((P256 : ℕ) : Specs.Secp256k1.Fp) = 0 from ZMod.natCast_self _] at hcast
  simp only [decodeFe, limbBits, mul_zero, add_zero, zero_add, zero_mul] at hcast ⊢
  rw [sq]
  linear_combination hcast

/-! ### Completeness -/

/-- The honest quotient wire value: the usual quotient minus the folded-away
high half of the convolution. -/
def qFoldVal (env : ProverEnvironment (F circomPrime)) (lam b c : Var Emu (F circomPrime)) : ℕ :=
  (evalEmu env lam * evalEmu env lam + 4 * P256 - evalEmu env b - evalEmu env c) / P256
    - convHigh env.toEnvironment (bigIntMulNoReduce lam lam)

lemma qFoldVal_eq_of_eval_eq {e e' : ProverEnvironment (F circomPrime)}
    {lam b c : Var Emu (F circomPrime)}
    (hlam : eval e lam = eval e' lam) (hb : eval e b = eval e' b)
    (hc : eval e c = eval e' c) :
    qFoldVal e lam b c = qFoldVal e' lam b c := by
  unfold qFoldVal
  rw [evalEmu_eq_of_eval_eq hlam, evalEmu_eq_of_eval_eq hb, evalEmu_eq_of_eval_eq hc,
    convHigh_eq_of_eval_eq (emu_map_eval_eq_of_eval_eq hlam)
      (emu_map_eval_eq_of_eval_eq hlam)]

lemma qFoldVal_eq (env : ProverEnvironment (F circomPrime)) (lam b c : Var Emu (F circomPrime)) :
    qFoldVal env lam b c
      = (BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) lam)
            * BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) lam) + 4 * P256
          - BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) b)
          - BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) c)) / P256
        - convHigh env.toEnvironment (bigIntMulNoReduce lam lam) := by
  unfold qFoldVal
  rw [PairAdd.evalEmu_eq_value env lam, PairAdd.evalEmu_eq_value env b,
    PairAdd.evalEmu_eq_value env c]

/-- Key decomposition: the unfolded quotient minus the folded-away high half is
the quotient of the folded remainder `R`. -/
lemma fold_D_decomp (La Bv Cv L4 H : ℕ)
    (hsplit : La * La = L4 + 2 ^ 256 * H)
    (hbv : Bv < 2 ^ 256) (hcv : Cv < 2 ^ 256) :
    La * La + 4 * P256 - Bv - Cv = P256 * H + (L4 + cF * H + 4 * P256 - Bv - Cv) := by
  have hmix : P256 * H + cF * H = 2 ^ 256 * H := by
    rw [← Nat.add_mul, Nat.add_comm P256 cF, Nat.add_comm cF P256, p_add_cF]
  have h4p : 2 ^ 256 + 2 ^ 256 ≤ 4 * P256 := by decide
  omega

set_option exponentiation.threshold 1200 in
lemma qFoldVal_lt (env : ProverEnvironment (F circomPrime)) (lam b c : Var Emu (F circomPrime))
    (hlam : BigInt.Normalized 64 (Vector.map (Expression.eval env.toEnvironment) lam))
    (hb : BigInt.Normalized 64 (Vector.map (Expression.eval env.toEnvironment) b))
    (hc : BigInt.Normalized 64 (Vector.map (Expression.eval env.toEnvironment) c)) :
    qFoldVal env lam b c < 2 ^ 67 := by
  have hdig := PairAdd.digit_lt_of_norm env.toEnvironment lam hlam
  have hPb : ∀ k : Fin 7,
      (Expression.eval env.toEnvironment
        ((bigIntMulNoReduce lam lam)[k.val])).val < 4 * 2 ^ 128 := fun k =>
    val_bigIntMulNoReduce_coeff_lt env.toEnvironment lam lam k hdig hdig (by decide)
  set La := BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) lam) with hLa
  set Bv := BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) b) with hBv
  set Cv := BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) c) with hCv
  set H := convHigh env.toEnvironment (bigIntMulNoReduce lam lam) with hH
  set L4 := convLow env.toEnvironment (bigIntMulNoReduce lam lam) with hL4
  have hsplit : La * La = L4 + 2 ^ 256 * H := by
    rw [hLa, ← MulMod.polyValue_mul_eq env.toEnvironment lam lam hdig hdig (by decide)]
    exact polyValue_split4 env.toEnvironment (bigIntMulNoReduce lam lam)
  have hbv : Bv < 2 ^ 256 := by
    have := BigInt.value_lt (B := 64) hb
    simpa using this
  have hcv : Cv < 2 ^ 256 := by
    have := BigInt.value_lt (B := 64) hc
    simpa using this
  have hL4b : L4 < 2 ^ 322 + 2 ^ 259 := convLow_lt env.toEnvironment _ hPb
  have hHb : H < 2 ^ 259 := convHigh_lt env.toEnvironment _ hPb
  have hdec := fold_D_decomp La Bv Cv L4 H hsplit hbv hcv
  set R := L4 + cF * H + 4 * P256 - Bv - Cv with hR
  have hPpos : 0 < P256 := by decide
  have hdivD : (La * La + 4 * P256 - Bv - Cv) / P256 = H + R / P256 := by
    rw [hdec, Nat.mul_add_div hPpos]
  have hqf : qFoldVal env lam b c = R / P256 := by
    rw [qFoldVal_eq]
    rw [← hLa, ← hBv, ← hCv, ← hH, hdivD]
    exact Nat.add_sub_cancel_left _ _
  have hcFH : cF * H ≤ (2 ^ 32 + 977) * 2 ^ 259 := by
    have : cF * H ≤ cF * 2 ^ 259 := Nat.mul_le_mul_left _ (by omega)
    simpa only [cF] using this
  have hRb : R < 2 ^ 67 * P256 := by
    have hb2 : (2 : ℕ) ^ 322 + 2 ^ 259 + (2 ^ 32 + 977) * 2 ^ 259 + 4 * P256 < 2 ^ 67 * P256 := by
      decide
    omega
  rw [hqf]
  exact (Nat.div_lt_iff_lt_mul hPpos).mpr (by omega)

/-- With the honest witnesses the folded polynomial identity holds. -/
lemma fold_spec_complete (env : Environment (F circomPrime))
    (lam a b c : Var Emu (F circomPrime)) (q : Expression (F circomPrime))
    (P : Vector (Expression (F circomPrime)) 7)
    (hP : ∀ k : Fin 7,
      Expression.eval env P[k.val] = Expression.eval env (bigIntMulNoReduce lam lam)[k.val])
    (hlam : BigInt.Normalized 64 (Vector.map (Expression.eval env) lam))
    (ha : BigInt.Normalized 64 (Vector.map (Expression.eval env) a))
    (hb : BigInt.Normalized 64 (Vector.map (Expression.eval env) b))
    (hc : BigInt.Normalized 64 (Vector.map (Expression.eval env) c))
    (hq : (Expression.eval env q).val < 2 ^ 68)
    (hav : BigInt.value 64 (Vector.map (Expression.eval env) a)
      = (BigInt.value 64 (Vector.map (Expression.eval env) lam)
          * BigInt.value 64 (Vector.map (Expression.eval env) lam) + 4 * P256
        - BigInt.value 64 (Vector.map (Expression.eval env) b)
        - BigInt.value 64 (Vector.map (Expression.eval env) c)) % P256)
    (hqv : (Expression.eval env q).val
      = (BigInt.value 64 (Vector.map (Expression.eval env) lam)
          * BigInt.value 64 (Vector.map (Expression.eval env) lam) + 4 * P256
        - BigInt.value 64 (Vector.map (Expression.eval env) b)
        - BigInt.value 64 (Vector.map (Expression.eval env) c)) / P256
        - convHigh env (bigIntMulNoReduce lam lam)) :
    polyValue 64 (Vector.map (Expression.eval env)
          (Vector.mapFinRange 4 fun k : Fin 4 => foldLhs P (4 * P256) k.val))
      = polyValue 64 (Vector.map (Expression.eval env)
          (Vector.mapFinRange 4 fun k : Fin 4 => foldRhs q a b c k.val)) := by
  have hPb := conv_coeff_lt env lam P hP hlam
  have hdig := PairAdd.digit_lt_of_norm env lam hlam
  have hCH : convHigh env P = convHigh env (bigIntMulNoReduce lam lam) := by
    simp only [convHigh]
    refine Finset.sum_congr rfl fun t _ => ?_
    exact congrArg (fun z : F circomPrime => z.val * 2 ^ (64 * t.val))
      (hP ⟨t.val + 4, by omega⟩)
  have hpv : polyValue 64 (Vector.map (Expression.eval env) P)
      = BigInt.value 64 (Vector.map (Expression.eval env) lam)
        * BigInt.value 64 (Vector.map (Expression.eval env) lam) := by
    rw [← MulMod.polyValue_mul_eq env lam lam hdig hdig (by decide)]
    simp only [polyValue, Vector.getElem_map]
    exact Finset.sum_congr rfl fun i _ => by rw [hP i]
  have hL := polyValue_foldLhs env P (4 * P256) (by decide) hPb
  rw [hpv, hCH] at hL
  have hRv := polyValue_foldRhs env q a b c hq ha hb hc
  set La := BigInt.value 64 (Vector.map (Expression.eval env) lam) with hLa
  set Bv := BigInt.value 64 (Vector.map (Expression.eval env) b) with hBv
  set Cv := BigInt.value 64 (Vector.map (Expression.eval env) c) with hCv
  set H := convHigh env (bigIntMulNoReduce lam lam) with hHdef
  set L4 := convLow env (bigIntMulNoReduce lam lam) with hL4def
  have hsplit : La * La = L4 + 2 ^ 256 * H := by
    rw [hLa, ← MulMod.polyValue_mul_eq env lam lam hdig hdig (by decide)]
    exact polyValue_split4 env (bigIntMulNoReduce lam lam)
  have hbv : Bv < 2 ^ 256 := by
    have := BigInt.value_lt (B := 64) hb
    simpa using this
  have hcv : Cv < 2 ^ 256 := by
    have := BigInt.value_lt (B := 64) hc
    simpa using this
  have hdec := fold_D_decomp La Bv Cv L4 H hsplit hbv hcv
  set R := L4 + cF * H + 4 * P256 - Bv - Cv with hRdef
  have hPpos : 0 < P256 := by decide
  have hdivD : (La * La + 4 * P256 - Bv - Cv) / P256 = H + R / P256 := by
    rw [hdec, Nat.mul_add_div hPpos]
  have hmodD : (La * La + 4 * P256 - Bv - Cv) % P256 = R % P256 := by
    rw [hdec, Nat.mul_add_mod]
  have hqv' : (Expression.eval env q).val = R / P256 := by
    rw [hqv, hdivD]
    exact Nat.add_sub_cancel_left _ _
  have hQM : R = (Expression.eval env q).val * P256 + R % P256 := by
    rw [hqv']
    exact (Nat.div_add_mod' R P256).symm
  have h4p : 2 ^ 256 + 2 ^ 256 ≤ 4 * P256 := by decide
  rw [hRv, hav, hmodD]
  omega


end FoldQuot
end Solution.Secp256k1ScalarMulFixedBase

end DonorFile2_4

-- Adapted donor module: CrtMul
section DonorFile2_5

/-!
# The CRT (residue-ring) fold multiply

`MulMod.interpolatedMul` pins the full `2m-1 = 7` coefficient convolution of two
4-limb operands at a cost of `⟨7,7⟩`.  But **nothing in this circuit ever reads
those seven coefficients**: every consumer immediately applies `FoldQuot.foldLhs`
(or `FoldWide.foldLhs2`), i.e. reduces the product modulo `X^4 - cF` with
`cF = 2^32 + 977`.

Multiplication in the residue ring `F_r[X]/(X^4 - cF)` has bilinear rank equal to
`2*4 - k` where `k` is the number of distinct irreducible factors of `X^4 - cF`
over the BN254 scalar field.  `cF` is a fourth power there, so `X^4 - cF` splits
completely, `k = 4`, and the rank is `4`.

`crtFoldMul` realises that: it witnesses the **four folded** coefficients
`z_k + cF * z_{k+4}` directly and pins them with one row per fourth root of `cF`,
at a cost of `⟨4,4⟩`.  Each row is a single product of two affine forms, since
the roots are compile-time constants.
-/

namespace Solution.Secp256k1ScalarMulFixedBase

open GroupedFlex (polyEvalExpr polyEvalExpr_eval)

namespace CrtMul

/-- The four fourth roots of `cF = 2^32 + 977` in the BN254 scalar field. -/
def rhoNat : Vector ℕ 4 :=
  #v[6022495585687529434600811952072328267646044551480745240691212116594068018376,
     6407184712893995821909607707030380421668643124835825632869578387818341362621,
     15481058158945279400336798038226894666879721275580208710828625798757467132996,
     15865747286151745787645593793184946820902319848935289103006992069981740477241]

/-- The `j`-th root as a field constant. -/
def rho (j : Fin 4) : F circomPrime := ((rhoNat[j.val] : ℕ) : F circomPrime)

lemma rhoNat_pow4 : ∀ j (hj : j < 4),
    (rhoNat[j]'hj) ^ 4 % circomPrime = FoldQuot.cF % circomPrime := by decide

lemma rhoNat_lt : ∀ j (hj : j < 4), (rhoNat[j]'hj) < circomPrime := by decide

lemma rhoNat_ne : ∀ i (hi : i < 4), ∀ j (hj : j < 4),
    i ≠ j → (rhoNat[i]'hi) ≠ (rhoNat[j]'hj) := by decide

/-- `ρ_j ^ 4 = cF` in the field. -/
theorem rho_pow4 (j : Fin 4) : (rho j) ^ 4 = ((FoldQuot.cF : ℕ) : F circomPrime) := by
  have h : ((rhoNat[j.val] ^ 4 : ℕ) : F circomPrime) = ((FoldQuot.cF : ℕ) : F circomPrime) :=
    (ZMod.natCast_eq_natCast_iff' _ _ _).mpr (rhoNat_pow4 j.val j.isLt)
  simpa only [rho, Nat.cast_pow] using h

theorem rho_injective : Function.Injective rho := by
  intro i j hij
  by_contra hne
  have hij' := (ZMod.natCast_eq_natCast_iff' _ _ _).mp hij
  rw [Nat.mod_eq_of_lt (rhoNat_lt i.val i.isLt), Nat.mod_eq_of_lt (rhoNat_lt j.val j.isLt)] at hij'
  exact rhoNat_ne i.val i.isLt j.val j.isLt (fun h => hne (Fin.ext h)) hij'

/-- The folded convolution coefficient at position `k`: `P k + cF * P (k+4)`,
with no fold contribution at `k = 3`.  This is exactly the part of the product
that `FoldQuot.foldLhs` retains. -/
def foldCoeff (P : Vector (Expression (F circomPrime)) 7) (k : ℕ) : Expression (F circomPrime) :=
  (if h : k < 4 then P[k]'(by omega) else 0)
    + (if h : k < 3 then ((FoldQuot.cF : ℕ) : F circomPrime) * (P[k + 4]'(by omega)) else 0)

lemma foldLhs_eq_foldCoeff_add (P : Vector (Expression (F circomPrime)) 7) (v k : ℕ) :
    FoldQuot.foldLhs P v k = foldCoeff P k + FoldQuot.wExp v k := rfl

/-- The rank-4 residue-ring multiply: witness the four folded coefficients and
pin them at the four fourth roots of `cF`. -/
def crtFoldMul (a b : Var Emu (F circomPrime)) :
    Circuit (F circomPrime) (Vector (Expression (F circomPrime)) 4) := do
  let z ← ProvableType.witness (α := fields 4) fun env =>
    Vector.ofFn fun k : Fin 4 =>
      Expression.eval env.toEnvironment (foldCoeff (bigIntMulNoReduce a b) k.val)
  let constraints : Vector (Expression (F circomPrime)) 4 :=
    Vector.mapFinRange 4 fun j =>
      polyEvalExpr a (rho j) * polyEvalExpr b (rho j) - polyEvalExpr z (rho j)
  Circuit.forEach constraints assertZero
  return z

/-- The output wires of `crtFoldMul`. -/
def zVec4 (off : ℕ) : Vector (Expression (F circomPrime)) 4 :=
  Vector.mapRange 4 fun i => var (F := F circomPrime) { index := off + i }

lemma crtFoldMul_output (off : ℕ) (a b : Var Emu (F circomPrime)) :
    (crtFoldMul a b off).1 = zVec4 off := by
  simp only [crtFoldMul, zVec4, circuit_norm]

lemma crtFoldMul_localLength (off : ℕ) (a b : Var Emu (F circomPrime)) :
    Operations.localLength (crtFoldMul a b off).2 = 4 := by
  simp only [crtFoldMul, circuit_norm]

/-! ### Soundness -/

/-- The product of two limb-polynomial evaluations is the evaluation of the
convolution. -/
lemma prod_eq_conv_sum (env : Environment (F circomPrime)) (a b : Var Emu (F circomPrime))
    (c : F circomPrime) :
    Expression.eval env (polyEvalExpr a c) * Expression.eval env (polyEvalExpr b c)
      = ∑ k : Fin 7, Expression.eval env ((bigIntMulNoReduce a b)[k.val]) * c ^ k.val := by
  rw [polyEvalExpr_eval, polyEvalExpr_eval,
    cauchy_diag (m := 4) (by norm_num)
      (fun i : Fin 4 => Expression.eval env a[i.val])
      (fun i : Fin 4 => Expression.eval env b[i.val]) c]
  apply Finset.sum_congr rfl; intro k _
  congr 1
  exact (eval_bigIntMulNoReduce_coeff env a b k).symm

/-- Expanding a degree-`<7` polynomial evaluated at a fourth root of `cF` in
terms of the four folded coefficients. -/
lemma sum7_eq_sum4_fold (env : Environment (F circomPrime))
    (P : Vector (Expression (F circomPrime)) 7) (j : Fin 4) :
    (∑ k : Fin 7, Expression.eval env (P[k.val]) * (rho j) ^ k.val)
      = ∑ k : Fin 4, Expression.eval env (foldCoeff P k.val) * (rho j) ^ k.val := by
  have hr : (rho j) ^ 4 = ((FoldQuot.cF : ℕ) : F circomPrime) := rho_pow4 j
  simp only [foldCoeff, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    Fin.isValue]
  norm_num
  simp only [Expression.eval]
  rw [show (rho j) ^ 4 = ((FoldQuot.cF : ℕ) : F circomPrime) from hr,
    show (rho j) ^ 5 = ((FoldQuot.cF : ℕ) : F circomPrime) * rho j from by
      rw [show (5 : ℕ) = 4 + 1 from rfl, pow_succ, hr],
    show (rho j) ^ 6 = ((FoldQuot.cF : ℕ) : F circomPrime) * (rho j) ^ 2 from by
      rw [show (6 : ℕ) = 4 + 2 from rfl, pow_add, hr]]
  ring

/-- Given the four root rows, the witnessed coefficients are the folded
convolution coefficients. -/
lemma crt_eval_bridge (env : Environment (F circomPrime)) (off : ℕ)
    (a b : Var Emu (F circomPrime))
    (hpts : ∀ j : Fin 4,
      Expression.eval env (polyEvalExpr a (rho j))
          * Expression.eval env (polyEvalExpr b (rho j))
        = Expression.eval env (polyEvalExpr (zVec4 off) (rho j))) :
    ∀ k : Fin 4, Expression.eval env ((zVec4 off)[k.val])
      = Expression.eval env (foldCoeff (bigIntMulNoReduce a b) k.val) := by
  refine interp_uniqueness
    (fun k => Expression.eval env ((zVec4 off)[k.val]))
    (fun k => Expression.eval env (foldCoeff (bigIntMulNoReduce a b) k.val))
    rho rho_injective ?_
  intro j
  have hz : Expression.eval env (polyEvalExpr (zVec4 off) (rho j))
      = ∑ k : Fin 4, Expression.eval env ((zVec4 off)[k.val]) * (rho j) ^ k.val :=
    polyEvalExpr_eval _ _ _
  exact ((hpts j).trans hz).symm.trans
    ((prod_eq_conv_sum env a b (rho j)).trans (sum7_eq_sum4_fold env (bigIntMulNoReduce a b) j))

/-- Completeness direction: if the witness wires carry the honest folded
coefficients, the four root rows hold. -/
lemma crt_points_of_pins (env : Environment (F circomPrime)) (off : ℕ)
    (a b : Var Emu (F circomPrime))
    (h : ∀ k : Fin 4, env.get (off + k.val)
        = Expression.eval env (foldCoeff (bigIntMulNoReduce a b) k.val)) :
    ∀ j : Fin 4,
      Expression.eval env (polyEvalExpr a (rho j))
          * Expression.eval env (polyEvalExpr b (rho j))
        = Expression.eval env (polyEvalExpr (zVec4 off) (rho j)) := by
  intro j
  have hz : Expression.eval env (polyEvalExpr (zVec4 off) (rho j))
      = ∑ k : Fin 4, Expression.eval env ((zVec4 off)[k.val]) * (rho j) ^ k.val :=
    polyEvalExpr_eval _ _ _
  have hsum : (∑ k : Fin 4,
        Expression.eval env (foldCoeff (bigIntMulNoReduce a b) k.val) * (rho j) ^ k.val)
      = ∑ k : Fin 4, Expression.eval env ((zVec4 off)[k.val]) * (rho j) ^ k.val := by
    apply Finset.sum_congr rfl; intro k _
    congr 1
    rw [← h k]
    simp only [zVec4, Vector.getElem_mapRange, Expression.eval]
  exact (prod_eq_conv_sum env a b (rho j)).trans
    ((sum7_eq_sum4_fold env (bigIntMulNoReduce a b) j).trans (hsum.trans hz.symm))

end CrtMul

namespace Cost
open Challenge.CostR1CS

theorem affineW_crtFoldMul_output (a b : Var Emu (F circomPrime)) (off : ℕ) :
    AffineW ((CrtMul.crtFoldMul a b).output off) := by
  rw [show (CrtMul.crtFoldMul a b).output off = CrtMul.zVec4 off
      from CrtMul.crtFoldMul_output off a b]
  intro k hk
  rw [CrtMul.zVec4, Vector.getElem_mapRange]; exact Affine.var _

theorem costIs_crtFoldMul (a b : Var Emu (F circomPrime)) :
    CostIs (CrtMul.crtFoldMul a b) ⟨4, 4⟩ := by
  rw [show (⟨4, 4⟩ : Count) = ⟨4, 0⟩ + (⟨4 * 0, 4 * 1⟩ + Count.zero) from by decide]
  unfold CrtMul.crtFoldMul
  refine CostIs.bind (CostIs.provableWitness _) fun z => ?_
  refine CostIs.bind (CostIs.forEach fun a k => CostIs.assertZero _ k) fun _ => ?_
  exact CostIs.pure _

theorem isR1CS_crtFoldMul (a b : Var Emu (F circomPrime))
    (ha : AffineW a) (hb : AffineW b) :
    IsR1CSCirc (CrtMul.crtFoldMul a b) := by
  unfold CrtMul.crtFoldMul
  refine IsR1CSCirc.bind_out (IsR1CSCirc.provableWitness _) fun nz => ?_
  refine IsR1CSCirc.bind ?_ fun _ => ?_
  · refine IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) fun t k => ?_
    refine IsR1CSCirc.assertZero ?_ k
    rw [Vector.getElem_mapFinRange]
    exact isR1CSRow_mul_sub (affine_polyEvalExpr _ _ (fun i hi => ha i hi))
      (affine_polyEvalExpr _ _ (fun i hi => hb i hi))
      (affine_polyEvalExpr _ _ (fun i hi =>
        affineW_provableWitness_bigInt (k := 4) _ nz i hi))
  exact IsR1CSCirc.pure _

end Cost

end Solution.Secp256k1ScalarMulFixedBase

end DonorFile2_5
