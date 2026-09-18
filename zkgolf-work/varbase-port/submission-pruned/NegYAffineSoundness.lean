import Solution.Secp256k1ScalarMul.NegYAffineBase
import Solution.Secp256k1ScalarMul.CompleteAddTheorems
import Solution.Secp256k1ScalarMul.OrderFactsCerts

namespace Solution.Secp256k1ScalarMul
namespace NegYAffine

open Specs.ShortWeierstrass Specs.Secp256k1

private lemma bool_val_le_one {x : F circomPrime} (hx : IsBool x) : x.val ≤ 1 := by
  have := IsBool.val_lt_two hx
  omega

private lemma nat_limb_eq
    {r b q cin cout : F circomPrime} {pd : ℕ}
    (hr : r.val < radix) (hb : b.val < radix)
    (hq : IsBool q) (hcin : IsBool cin) (hcout : IsBool cout)
    (hpd : pd < radix)
    (h : r + b + cin = q * (pd : F circomPrime) + (radix : F circomPrime) * cout) :
    r.val + b.val + cin.val = q.val * pd + radix * cout.val := by
  have hqv := bool_val_le_one hq
  have hciv := bool_val_le_one hcin
  have hcov := bool_val_le_one hcout
  have hl : r.val + b.val + cin.val < circomPrime := by
    have : 2 * radix + 1 < circomPrime := by decide
    omega
  have hrhs : q.val * pd + radix * cout.val < circomPrime := by
    have hcap : 2 * radix + 1 < circomPrime := by decide
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hqv with hq0 | hq1
    · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hcov with hc0 | hc1
      · simp only [hq0, hc0, zero_mul, mul_zero, add_zero]
        omega
      · simp only [hq0, hc1, zero_mul, mul_one, zero_add]
        omega
    · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hcov with hc0 | hc1
      · simp only [hq1, hc0, one_mul, mul_zero, add_zero]
        omega
      · simp only [hq1, hc1, one_mul, mul_one]
        omega
  have hlhs_cast : r + b + cin =
      ((r.val + b.val + cin.val : ℕ) : F circomPrime) := by
    push_cast
    rw [ZMod.natCast_zmod_val r, ZMod.natCast_zmod_val b,
      ZMod.natCast_zmod_val cin]
  have hrhs_cast : q * (pd : F circomPrime) + (radix : F circomPrime) * cout =
      ((q.val * pd + radix * cout.val : ℕ) : F circomPrime) := by
    push_cast
    rw [ZMod.natCast_zmod_val q, ZMod.natCast_zmod_val cout]
  have hv := congrArg ZMod.val h
  rw [hlhs_cast, hrhs_cast, ZMod.val_natCast_of_lt hl,
    ZMod.val_natCast_of_lt hrhs] at hv
  exact hv

/-- The top limb needs no range check of its own: once the three borrow bits are
pinned by the range checks on limbs 0..2, the field equation for limb 3 already
forces it into `[0, radix)`. -/
private lemma nat_last_bound
    {r b q cin : F circomPrime} {pd : ℕ}
    (hq : IsBool q) (hpd : pd < radix)
    (hle : b.val + cin.val ≤ q.val * pd)
    (h : r + b + cin = q * (pd : F circomPrime)) :
    r.val < radix ∧ r.val + b.val + cin.val = q.val * pd := by
  have hqv := bool_val_le_one hq
  have hqpd : q.val * pd ≤ pd := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hqv with h0 | h1
    · simp [h0]
    · simp [h1]
  set N : ℕ := q.val * pd - (b.val + cin.val) with hN
  have hsum : N + b.val + cin.val = q.val * pd := by omega
  have hNlt : N < radix := by omega
  have hNp : N < circomPrime := lt_trans hNlt (by decide : radix < circomPrime)
  have hcast : ((N : ℕ) : F circomPrime) + b + cin = q * (pd : F circomPrime) := by
    have hh : ((N + b.val + cin.val : ℕ) : F circomPrime)
        = ((q.val * pd : ℕ) : F circomPrime) := congrArg _ hsum
    push_cast at hh
    rw [ZMod.natCast_zmod_val b, ZMod.natCast_zmod_val cin, ZMod.natCast_zmod_val q] at hh
    linear_combination hh
  have hreq : r = ((N : ℕ) : F circomPrime) := by linear_combination h - hcast
  rw [hreq, ZMod.val_natCast_of_lt hNp]
  exact ⟨hNlt, hsum⟩

private lemma value_expand (v : Emu (F circomPrime)) :
    BigInt.value limbBits v =
      v[0].val + radix * v[1].val + radix ^ 2 * v[2].val + radix ^ 3 * v[3].val := by
  rw [BigInt.value_eq_sum]
  simp only [numLimbs, Fin.sum_univ_four, Fin.getElem_fin]
  norm_num [limbBits, radix]
  ring

/-- The borrow out of limb 2 never exceeds the room left in the top limb. -/
private lemma top_bound
    (q r0 r1 r2 y0 y1 y2 y3 c0 c1 c2 : ℕ)
    (hq : q ≤ 1)
    (hr0 : r0 < radix) (hr1 : r1 < radix) (hr2 : r2 < radix)
    (e0 : r0 + y0 = q * p0 + radix * c0)
    (e1 : r1 + y1 + c0 = q * pHi + radix * c1)
    (e2 : r2 + y2 + c1 = q * pHi + radix * c2)
    (hone : q = 1 → y0 + radix * y1 + radix ^ 2 * y2 + radix ^ 3 * y3 < P256)
    (hzero : q = 0 → y0 = 0 ∧ y1 = 0 ∧ y2 = 0 ∧ y3 = 0) :
    y3 + c2 ≤ q * pHi := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hq with h | h
  · obtain ⟨a0, a1, a2, a3⟩ := hzero h
    subst h; subst a0; subst a1; subst a2; subst a3
    norm_num [radix, p0, pHi] at hr0 hr1 hr2 e0 e1 e2 ⊢
    omega
  · have hlt := hone h
    subst h
    norm_num [radix, p0, pHi, P256, Specs.Secp256k1.p] at hr0 hr1 hr2 e0 e1 e2 hlt ⊢
    omega

private lemma weighted_sum_eq
    (q r0 r1 r2 r3 y0 y1 y2 y3 c0 c1 c2 : ℕ)
    (hq : q ≤ 1)
    (e0 : r0 + y0 = q * p0 + radix * c0)
    (e1 : r1 + y1 + c0 = q * pHi + radix * c1)
    (e2 : r2 + y2 + c1 = q * pHi + radix * c2)
    (e3 : r3 + y3 + c2 = q * pHi) :
    r0 + radix * r1 + radix ^ 2 * r2 + radix ^ 3 * r3 +
        (y0 + radix * y1 + radix ^ 2 * y2 + radix ^ 3 * y3) =
      q * P256 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hq with hq0 | hq1
  · simp only [hq0, zero_mul] at e0 e1 e2 e3 ⊢
    norm_num [radix, p0, pHi, P256, Specs.Secp256k1.p] at e0 e1 e2 e3 ⊢
    omega
  · simp only [hq1, one_mul] at e0 e1 e2 e3 ⊢
    norm_num [radix, p0, pHi, P256, Specs.Secp256k1.p] at e0 e1 e2 e3 ⊢
    omega

/-- A two-row zero test pins `c` to the indicator of `d = 0`. -/
private lemma zero_test_sound {d c v : F circomPrime}
    (hA : c - 1 + d * v = 0) (hB : d * c = 0) :
    c = if d = 0 then 1 else 0 := by
  by_cases hd : d = 0
  · rw [if_pos hd]
    rw [hd] at hA
    linear_combination hA
  · rw [if_neg hd]
    rcases mul_eq_zero.mp hB with h | h
    · exact absurd h hd
    · exact h

private lemma radix_cast_val : ((radix : ℕ) : F circomPrime).val = radix :=
  ZMod.val_natCast_of_lt (by decide)

private lemma radix_cast_ne_zero : ((radix : ℕ) : F circomPrime) ≠ 0 := by
  intro hh
  have := radix_cast_val
  rw [hh, ZMod.val_zero] at this
  exact absurd this.symm (by decide)

/-- On the infinity branch limb 0 cannot borrow. -/
private lemma c0_zero_of_q_zero {q y c r : F circomPrime} (hc : IsBool c)
    (hy0 : y = 0) (hr : r.val < radix) (hq : q = 0)
    (h : r + y = q * (p0 : F circomPrime) + (radix : F circomPrime) * c) : c = 0 := by
  rcases hc with h0 | h1
  · exact h0
  · exfalso
    rw [hy0, hq, h1] at h
    have hreq : r = ((radix : ℕ) : F circomPrime) := by linear_combination h
    rw [hreq, radix_cast_val] at hr
    omega

/-- Because `p1 = p2 = 2^64 - 1`, a borrow out of a middle limb happens exactly
when `y + cin = 2^64`.  So the zero-test witness `z` is forced to be the correct
borrow bit, and the limb result is automatically in range — no range check is
needed on limbs 1 and 2. -/
private lemma hi_limb_sound {q y c z r : F circomPrime}
    (hq : IsBool q) (hy : y.val < radix) (hc : IsBool c)
    (hq0 : q = 0 → y = 0 ∧ c = 0)
    (hz : z = if y + c - ((radix : ℕ) : F circomPrime) = 0 then 1 else 0)
    (h : r + y + c = q * (pHi : F circomPrime) + ((radix : ℕ) : F circomPrime) * z) :
    IsBool z ∧ r.val < radix ∧ (q = 0 → z = 0) := by
  by_cases hd : y + c - ((radix : ℕ) : F circomPrime) = 0
  · rw [if_pos hd] at hz
    have hq1 : q = 1 := by
      rcases hq with h0 | h1
      · exfalso
        obtain ⟨hy0, hc0⟩ := hq0 h0
        rw [hy0, hc0] at hd
        exact radix_cast_ne_zero (by linear_combination -hd)
      · exact h1
    subst hz
    subst hq1
    have hreq : r = ((pHi : ℕ) : F circomPrime) := by linear_combination h - hd
    refine ⟨Or.inr rfl, ?_, ?_⟩
    · rw [hreq, ZMod.val_natCast_of_lt (by decide : pHi < circomPrime)]
      decide
    · intro hcontra
      exact absurd hcontra one_ne_zero
  · rw [if_neg hd] at hz
    subst hz
    rw [mul_zero, add_zero] at h
    have hle : y.val + c.val ≤ q.val * pHi := by
      rcases hq with h0 | h1
      · obtain ⟨hy0, hc0⟩ := hq0 h0
        rw [h0, hy0, hc0]
        simp
      · rw [h1, ZMod.val_one, one_mul]
        have hcv := bool_val_le_one hc
        by_contra hcon
        push_neg at hcon
        have hrx : radix = 18446744073709551616 := by norm_num [radix]
        have hsum : y.val + c.val = radix := by
          simp only [pHi] at hcon
          rw [hrx] at hy ⊢
          omega
        refine absurd ?_ hd
        have hcc : ((y.val + c.val : ℕ) : F circomPrime) = ((radix : ℕ) : F circomPrime) :=
          congrArg _ hsum
        push_cast at hcc
        rw [ZMod.natCast_zmod_val y, ZMod.natCast_zmod_val c] at hcc
        linear_combination hcc
    obtain ⟨hrl, _⟩ := nat_last_bound hq (by decide : pHi < radix) hle h
    exact ⟨Or.inl rfl, hrl, fun _ => rfl⟩

set_option maxHeartbeats 2000000 in
private theorem soundnessCore
    (P : FlaggedPoint (F circomPrime)) (r : Emu (F circomPrime))
    (c0 c1 c2 v1 v2 : F circomPrime)
    (hP : P.Valid) (hcan : P.isInf = 1 → P.y = emuOfNat 0)
    (hc0 : IsBool c0)
    (hA1 : c1 - 1 + (P.y[1] + c0 - ((radix : ℕ) : F circomPrime)) * v1 = 0)
    (hB1 : (P.y[1] + c0 - ((radix : ℕ) : F circomPrime)) * c1 = 0)
    (hA2 : c2 - 1 + (P.y[2] + c1 - ((radix : ℕ) : F circomPrime)) * v2 = 0)
    (hB2 : (P.y[2] + c1 - ((radix : ℕ) : F circomPrime)) * c2 = 0)
    (h0 : r[0] + P.y[0] = (1 - P.isInf) * (p0 : F circomPrime) +
      (radix : F circomPrime) * c0)
    (h1 : r[1] + P.y[1] + c0 = (1 - P.isInf) * (pHi : F circomPrime) +
      (radix : F circomPrime) * c1)
    (h2 : r[2] + P.y[2] + c1 = (1 - P.isInf) * (pHi : F circomPrime) +
      (radix : F circomPrime) * c2)
    (h3 : r[3] + P.y[3] + c2 = (1 - P.isInf) * (pHi : F circomPrime))
    (hr0 : r[0].val < radix) :
    Fe.Valid r ∧ decodeFe r = -decodeFe P.y := by
  have hq : IsBool (1 - P.isInf) := by
    rcases hP.1 with hz | ho
    · rw [hz]
      exact Or.inr (by ring)
    · rw [ho]
      exact Or.inl (by ring)
  have hy := hP.2.2.1
  have hyzero : (1 - P.isInf) = 0 → ∀ (i : ℕ) (hi : i < numLimbs), (P.y[i]'hi) = 0 := by
    intro hq0 i hi
    have hisinf : P.isInf = 1 := by linear_combination -hq0
    rw [hcan hisinf]
    simp [emuOfNat, limbOfNat]
  have hz1 : c1 = if P.y[1] + c0 - ((radix : ℕ) : F circomPrime) = 0 then 1 else 0 :=
    zero_test_sound hA1 hB1
  have hz2 : c2 = if P.y[2] + c1 - ((radix : ℕ) : F circomPrime) = 0 then 1 else 0 :=
    zero_test_sound hA2 hB2
  have hc0zero : (1 - P.isInf) = 0 → c0 = 0 := fun hh =>
    c0_zero_of_q_zero hc0 (hyzero hh 0 (by decide)) hr0 hh h0
  obtain ⟨hc1, hr1, hz1zero⟩ := hi_limb_sound hq (hy.1 1) hc0
    (fun hh => ⟨hyzero hh 1 (by decide), hc0zero hh⟩) hz1 h1
  obtain ⟨hc2, hr2, _⟩ := hi_limb_sound hq (hy.1 2) hc1
    (fun hh => ⟨hyzero hh 2 (by decide), hz1zero hh⟩) hz2 h2
  have e0 := nat_limb_eq hr0 (hy.1 0) hq (Or.inl rfl) hc0
    (by decide : p0 < radix) (by simpa using h0)
  have e1 := nat_limb_eq hr1 (hy.1 1) hq hc0 hc1
    (by decide : pHi < radix) h1
  have e2 := nat_limb_eq hr2 (hy.1 2) hq hc1 hc2
    (by decide : pHi < radix) h2
  have hle : P.y[3].val + c2.val ≤ (1 - P.isInf).val * pHi := by
    refine top_bound (1 - P.isInf).val r[0].val r[1].val r[2].val
      P.y[0].val P.y[1].val P.y[2].val P.y[3].val c0.val c1.val c2.val
      (bool_val_le_one hq) hr0 hr1 hr2 (by simpa using e0) e1 e2 ?_ ?_
    · intro _
      have hv := hy.2
      rw [value_expand] at hv
      exact hv
    · intro hq0
      have hisinf : P.isInf = 1 := by
        rcases hP.1 with hz | ho
        · exfalso
          rw [hz, sub_zero, ZMod.val_one] at hq0
          exact absurd hq0 (by decide)
        · exact ho
      have hy0 : P.y = emuOfNat 0 := hcan hisinf
      have hlimb : ∀ (i : ℕ) (hi : i < numLimbs), (P.y[i]'hi).val = 0 := by
        intro i hi
        rw [hy0]
        simp [emuOfNat, limbOfNat]
      exact ⟨hlimb 0 (by decide), hlimb 1 (by decide), hlimb 2 (by decide),
        hlimb 3 (by decide)⟩
  obtain ⟨hr3, e3⟩ := nat_last_bound hq (by decide : pHi < radix) hle h3
  have hrn : r.Normalized limbBits := by
    intro i
    fin_cases i
    · simpa [radix] using hr0
    · simpa [radix] using hr1
    · simpa [radix] using hr2
    · simpa [radix] using hr3
  have hval : BigInt.value limbBits r + BigInt.value limbBits P.y =
      (1 - P.isInf).val * P256 := by
    rw [BigInt.value_eq_sum, BigInt.value_eq_sum]
    simp only [numLimbs, Fin.sum_univ_four, Fin.getElem_fin, ZMod.val_zero] at e0 e1 e2 e3 ⊢
    norm_num [limbBits]
    simpa [radix, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      (weighted_sum_eq
        (q := (1 - P.isInf).val)
        (r0 := r[0].val) (r1 := r[1].val) (r2 := r[2].val) (r3 := r[3].val)
        (y0 := P.y[0].val) (y1 := P.y[1].val) (y2 := P.y[2].val)
        (y3 := P.y[3].val)
        (c0 := c0.val) (c1 := c1.val) (c2 := c2.val)
        (bool_val_le_one hq) (by simpa using e0) e1 e2 e3)
  have hlt : BigInt.value limbBits r < P256 := by
    rcases hP.1 with hi | hi
    · have hqv : (1 - P.isInf).val = 1 := by rw [hi, sub_zero, ZMod.val_one]
      rw [hqv, one_mul] at hval
      have hy0 : decodeFe P.y ≠ 0 :=
        OrderFactsCerts.noOrderTwo_secp _ (hP.2.2.2 hi)
      have hyvpos : 0 < BigInt.value limbBits P.y := by
        by_contra hz
        have hzv : BigInt.value limbBits P.y = 0 := by omega
        apply hy0
        simp only [decodeFe]
        have hzcast := congrArg (Nat.cast : ℕ → Fp) hzv
        simpa using hzcast
      omega
    · have hy0 : P.y = emuOfNat 0 := hcan hi
      have hqv : (1 - P.isInf).val = 0 := by rw [hi]; norm_num
      have hyv : BigInt.value limbBits P.y = 0 := by
        rw [hy0, CompleteAdd.value_emuOfNat (by decide)]
      rw [hyv, hqv, zero_mul] at hval
      have hrzero : BigInt.value limbBits r = 0 := by omega
      rw [hrzero]
      norm_num [P256, Specs.Secp256k1.p]
  refine ⟨⟨hrn, hlt⟩, ?_⟩
  have hcast := congrArg (Nat.cast : ℕ → Fp) hval
  push_cast at hcast
  rw [show ((P256 : ℕ) : Fp) = 0 from ZMod.natCast_self _, mul_zero] at hcast
  simp only [decodeFe]
  linear_combination hcast

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem soundness : Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [RangeCheck.circuit, RangeCheck.Assumptions, RangeCheck.Spec]
  obtain ⟨hc0, hA1, hB1, hA2, hB2, hRC0⟩ := h_holds
  obtain ⟨hP, hcan⟩ := h_assumptions
  obtain ⟨hx, hy, hi⟩ := h_input
  have hcin0 : IsBool (env.get i₀) := by
    rw [IsBool.iff_mul_sub_one]
    simpa only [sub_eq_add_neg] using hc0
  have hyi : ∀ (i : ℕ) (hip : i < numLimbs),
      Expression.eval env (input_var_y[i]'hip) = input_y[i]'hip := by
    intro i hip
    simpa only [Vector.getElem_map] using
      congrArg (fun v : Emu (F circomPrime) => v[i]'hip) hy
  simp only [d1Expr, d2Expr, Expression.eval] at hA1 hB1 hA2 hB2
  rw [hyi 1 (by decide)] at hA1 hB1
  rw [hyi 2 (by decide)] at hA2 hB2
  refine soundnessCore
    ({ x := input_x, y := input_y, isInf := input_isInf } :
      FlaggedPoint (F circomPrime)) _
    (env.get i₀) (env.get (i₀ + 1 + 1)) (env.get (i₀ + 1 + 1 + 1 + 1))
    (env.get (i₀ + 1)) (env.get (i₀ + 1 + 1 + 1))
    hP hcan hcin0 ?hA1 ?hB1 ?hA2 ?hB2 ?h0 ?h1 ?h2 ?h3 ?r0
  case hA1 => linear_combination hA1
  case hB1 => linear_combination hB1
  case hA2 => linear_combination hA2
  case hB2 => linear_combination hB2
  case r0 => simpa [Vector.getElem_map, radix, secpParams] using hRC0
  all_goals
    simp only [result, qExpr, Vector.getElem_map, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ, Expression.eval]
    rw [hyi, hi]
    ring

end NegYAffine
end Solution.Secp256k1ScalarMul
