import Solution.Secp256k1ScalarMul.Params
import Clean.Gadgets.IsZeroField
import Mathlib.Tactic.IntervalCases

namespace Solution.Secp256k1ScalarMul
namespace ValidP

open Utils.Bits

/-- Sum `1 - bit` over a slice. On boolean bits this is zero exactly when the
whole slice consists of ones. -/
def deficitSlice {n : ℕ} (bits : Vector (Expression (F circomPrime)) n)
    (start len : ℕ) (h : start + len ≤ n) : Expression (F circomPrime) :=
  Fin.foldl len (fun acc i => acc + (1 - bits[start + i.val]'(by omega))) 0

def dc (x start len : ℕ) : ℕ :=
  ∑ i : Fin len, if x.testBit (start + i.val) then 0 else 1

theorem dc_zero_iff (x start len : ℕ) :
    dc x start len = 0 ↔ ∀ i : Fin len, x.testBit (start + i.val) = true := by
  simp [dc]

theorem dc_ne_iff (x start len : ℕ) :
    dc x start len ≠ 0 ↔ ∃ i : Fin len, x.testBit (start + i.val) = false := by
  simp [dc]

theorem dc_le (x start len : ℕ) : dc x start len ≤ len := by
  unfold dc
  calc
    (∑ i : Fin len, if x.testBit (start + i.val) then 0 else 1)
        ≤ ∑ _i : Fin len, 1 := by
          apply Finset.sum_le_sum
          intro i _
          split <;> omega
    _ = len := by simp

theorem cast_zero_iff {n : ℕ} (hn : n < circomPrime) :
    ((n : ℕ) : F circomPrime) = 0 ↔ n = 0 := by
  rw [ZMod.natCast_eq_zero_iff]
  constructor
  · intro hd
    rcases hd with ⟨k, hk⟩
    by_cases hk0 : k = 0
    · simp [hk0] at hk
      exact hk
    · have : circomPrime ≤ n := by
        rw [hk]
        exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hk0)
      omega
  · rintro rfl
    exact dvd_zero _

lemma eval_fold {n : ℕ} (env : Environment (F Solution.Secp256k1ScalarMul.circomPrime))
    (g : Fin n → Expression (F Solution.Secp256k1ScalarMul.circomPrime)) :
    Expression.eval env (Fin.foldl n (fun acc i => acc + g i) 0)
      = ∑ i : Fin n, Expression.eval env (g i) := by
  induction n with
  | zero => simp [Expression.eval]
  | succ k ih =>
    simp [Fin.foldl_succ_last, Fin.sum_univ_castSucc, Expression.eval, ih]

lemma eval_ds {n start len : ℕ} (h : start + len ≤ n)
    (env : Environment (F Solution.Secp256k1ScalarMul.circomPrime))
    (bits : Vector (Expression (F Solution.Secp256k1ScalarMul.circomPrime)) n)
    (x : F Solution.Secp256k1ScalarMul.circomPrime)
    (hb : Vector.map (Expression.eval env) bits = fieldToBits n x) :
    Expression.eval env (ValidP.deficitSlice bits start len h)
      = ((dc x.val start len : ℕ) : F Solution.Secp256k1ScalarMul.circomPrime) := by
  rw [ValidP.deficitSlice, eval_fold, dc, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hi : start + i.val < n := by omega
  have he := congrArg (fun v : Vector (F Solution.Secp256k1ScalarMul.circomPrime) n =>
    v[start + i.val]'hi) hb
  simp only [Vector.getElem_map] at he
  simp only [fieldToBits, Vector.getElem_map, toBits, Vector.getElem_mapRange] at he
  rw [show Expression.eval env (1 - bits[start + i.val]'hi)
      = 1 - Expression.eval env (bits[start + i.val]'hi) by
        simp only [Expression.eval]; ring, he]
  split <;> simp

theorem mapRange_eval_bit (env : Environment (F circomPrime)) (offset i : ℕ)
    (hi : i < limbBits) (x : F circomPrime)
    (hb : Vector.map (Expression.eval env)
      (Vector.mapRange limbBits fun j => var { index := offset + j }) =
        fieldToBits limbBits x) :
    env.get (offset + i) = if x.val.testBit i then 1 else 0 := by
  have h := congrArg (fun v : Vector (F circomPrime) limbBits => v[i]'hi) hb
  simp only [Vector.getElem_map] at h
  simp only [fieldToBits, Vector.getElem_map, toBits, Vector.getElem_mapRange] at h
  simp only [Expression.eval] at h
  split <;> simp_all

/-- Read the `i`-th bit off an arbitrary decomposition vector, given its value
equals `fieldToBits`.  Shape-agnostic: works for the affine-top vector where the
last entry is not a bare witness variable. -/
theorem vec_eval_bit (env : Environment (F circomPrime)) {n : ℕ}
    (b : Vector (Expression (F circomPrime)) n) (x : F circomPrime)
    (hb : Vector.map (Expression.eval env) b = fieldToBits n x)
    (i : ℕ) (hi : i < n) :
    Expression.eval env b[i] = if x.val.testBit i then 1 else 0 := by
  have h := congrArg (fun v : Vector (F circomPrime) n => v[i]'hi) hb
  simp only [Vector.getElem_map] at h
  simp only [fieldToBits, Vector.getElem_map, toBits, Vector.getElem_mapRange] at h
  split <;> simp_all

/-- For an affine-top vector `(mapRange w var).push top`, the low `w` cells are
plain witnesses, so their environment value is the corresponding bit. -/
theorem push_eval_bit (env : Environment (F circomPrime)) {w : ℕ} (base : ℕ)
    (top : Expression (F circomPrime)) (x : F circomPrime)
    (hb : Vector.map (Expression.eval env)
      ((Vector.mapRange w fun j => var { index := base + j }).push top) =
        fieldToBits (w + 1) x)
    (i : ℕ) (hi : i < w) :
    env.get (base + i) = if x.val.testBit i then 1 else 0 := by
  have h := vec_eval_bit env _ x hb i (by omega)
  rwa [Vector.getElem_push_lt hi, Vector.getElem_mapRange, Expression.eval] at h

theorem value_testBit (x : Emu (F circomPrime)) (hn : BigInt.Normalized limbBits x)
    (k : Fin 4) (j : Fin 64) :
    (BigInt.value limbBits x).testBit (64 * k.val + j.val) = x[k.val].val.testBit j.val := by
  fin_cases k
  · simp only [Fin.isValue, Nat.mul_zero, Nat.zero_add]
    have hn0 : x[0].val < 2^64 := by simpa [limbBits] using hn 0
    rw [show BigInt.value limbBits x =
        2^64 * (x[1].val + 2^64 * (x[2].val + 2^64 * x[3].val)) + x[0].val by
      rw [BigInt.value_eq_sum]; norm_num [Fin.sum_univ_succ]; ring_nf]
    rw [Nat.testBit_two_pow_mul_add _ hn0 j.val, if_pos j.isLt]
  · simp only [Fin.isValue, Nat.mul_one]
    have hn0 : x[0].val < 2^64 := by simpa [limbBits] using hn 0
    have hn1 : x[1].val < 2^64 := by simpa [limbBits] using hn 1
    rw [show BigInt.value limbBits x =
        2^64 * (x[1].val + 2^64 * (x[2].val + 2^64 * x[3].val)) + x[0].val by
      rw [BigInt.value_eq_sum]; norm_num [Fin.sum_univ_succ]; ring_nf]
    rw [Nat.testBit_two_pow_mul_add _ hn0 (64 + j.val), if_neg (by omega)]
    simp only [Nat.add_sub_cancel_left]
    rw [show x[1].val + 2^64 * (x[2].val + 2^64 * x[3].val)
        = 2^64 * (x[2].val + 2^64 * x[3].val) + x[1].val by ring]
    rw [Nat.testBit_two_pow_mul_add _ hn1 j.val, if_pos j.isLt]
  · simp only [Fin.isValue, Nat.reduceMul]
    have hn2 : x[2].val < 2^64 := by simpa [limbBits] using hn 2
    rw [show BigInt.value limbBits x =
        2^128 * (x[2].val + 2^64 * x[3].val) + (x[0].val + 2^64 * x[1].val) by
      rw [BigInt.value_eq_sum]; norm_num [Fin.sum_univ_succ]; ring_nf]
    have hlo : x[0].val + 2^64 * x[1].val < 2^128 := by
      have h0 := hn 0; have h1 := hn 1
      norm_num [limbBits] at h0 h1 ⊢
      nlinarith
    rw [Nat.testBit_two_pow_mul_add _ hlo (128 + j.val), if_neg (by omega)]
    simp only [Nat.add_sub_cancel_left]
    rw [show x[2].val + 2^64 * x[3].val = 2^64 * x[3].val + x[2].val by ring]
    rw [Nat.testBit_two_pow_mul_add _ hn2 j.val, if_pos j.isLt]
  · simp only [Fin.isValue, Nat.reduceMul]
    rw [show BigInt.value limbBits x =
        2^192 * x[3].val + (x[0].val + 2^64 * x[1].val + 2^128 * x[2].val) by
      rw [BigInt.value_eq_sum]; norm_num [Fin.sum_univ_succ]; ring_nf]
    have hlo : x[0].val + 2^64 * x[1].val + 2^128 * x[2].val < 2^192 := by
      have h0 := hn 0; have h1 := hn 1; have h2 := hn 2
      norm_num [limbBits] at h0 h1 h2 ⊢
      nlinarith
    rw [Nat.testBit_two_pow_mul_add _ hlo (192 + j.val), if_neg (by omega)]
    simp only [Nat.add_sub_cancel_left]

theorem value_testBit_global (x : Emu (F circomPrime)) (hn : BigInt.Normalized limbBits x)
    (i : ℕ) (hi : i < 256) :
    (BigInt.value limbBits x).testBit i =
      (x[i / 64]'(by norm_num [numLimbs]; omega)).val.testBit (i % 64) := by
  let k : Fin 4 := ⟨i / 64, by omega⟩
  let j : Fin 64 := ⟨i % 64, Nat.mod_lt _ (by norm_num)⟩
  have h := value_testBit x hn k j
  simpa [k, j, Nat.mul_comm, Nat.div_add_mod] using h

def topDC (x : Emu (F circomPrime)) : ℕ :=
  dc x[0].val 33 31 + dc x[1].val 0 64 + dc x[2].val 0 64 + dc x[3].val 0 64

def midDC (x : Emu (F circomPrime)) : ℕ := dc x[0].val 10 22

def lowDC (x : Emu (F circomPrime)) : ℕ := dc x[0].val 0 4

theorem cast_add4_zero_iff (a b c d : ℕ) (h : a + b + c + d < circomPrime) :
    ((a : F circomPrime) + (b : F circomPrime) + (c : F circomPrime) +
      (d : F circomPrime) = 0) ↔ a + b + c + d = 0 := by
  rw [← Nat.cast_add, ← Nat.cast_add, ← Nat.cast_add]
  exact cast_zero_iff h

theorem top_count_cast_zero_iff (a b c d : ℕ) :
    ((dc a 33 31 : F circomPrime) + (dc b 0 64 : F circomPrime) +
      (dc c 0 64 : F circomPrime) + (dc d 0 64 : F circomPrime) = 0) ↔
      dc a 33 31 + dc b 0 64 + dc c 0 64 + dc d 0 64 = 0 := by
  apply cast_add4_zero_iff
  have h0 := dc_le a 33 31
  have h1 := dc_le b 0 64
  have h2 := dc_le c 0 64
  have h3 := dc_le d 0 64
  exact lt_of_le_of_lt (by omega) (by decide +kernel : 223 < circomPrime)

theorem mid_cast_zero_iff (x : Emu (F circomPrime)) :
    ((dc x[0].val 10 22 : F circomPrime) = 0) ↔ midDC x = 0 := by
  apply cast_zero_iff
  exact lt_of_le_of_lt (dc_le x[0].val 10 22)
    (by decide +kernel : 22 < circomPrime)

theorem low_cast_zero_iff (x : Emu (F circomPrime)) :
    ((dc x[0].val 0 4 : F circomPrime) = 0) ↔ lowDC x = 0 := by
  apply cast_zero_iff
  exact lt_of_le_of_lt (dc_le x[0].val 0 4)
    (by decide +kernel : 4 < circomPrime)

set_option maxRecDepth 5000 in
theorem topDC_zero_high_bits (x : Emu (F circomPrime)) (hn : BigInt.Normalized limbBits x)
    (ht : topDC x = 0) (i : ℕ) (hi0 : 33 ≤ i) (hi1 : i < 256) :
    (BigInt.value limbBits x).testBit i = true := by
  have hd0 : dc x[0].val 33 31 = 0 := by unfold topDC at ht; omega
  have hd1 : dc x[1].val 0 64 = 0 := by unfold topDC at ht; omega
  have hd2 : dc x[2].val 0 64 = 0 := by unfold topDC at ht; omega
  have hd3 : dc x[3].val 0 64 = 0 := by unfold topDC at ht; omega
  by_cases h64 : i < 64
  · have hv := value_testBit x hn 0 ⟨i, h64⟩
    have hidx : i - 33 < 31 := by omega
    have h := (dc_zero_iff x[0].val 33 31).mp hd0 ⟨i - 33, hidx⟩
    calc
      (BigInt.value limbBits x).testBit i = x[0].val.testBit i := by simpa using hv
      _ = true := by simpa [Nat.add_sub_of_le hi0] using h
  · by_cases h128 : i < 128
    · have hv := value_testBit x hn 1 ⟨i - 64, by omega⟩
      have hidx : i - 64 < 64 := by omega
      have h := (dc_zero_iff x[1].val 0 64).mp hd1 ⟨i - 64, hidx⟩
      calc
        (BigInt.value limbBits x).testBit i = x[1].val.testBit (i - 64) := by
          simpa [Nat.add_sub_of_le (by omega : 64 ≤ i)] using hv
        _ = true := by simpa using h
    · by_cases h192 : i < 192
      · have hv := value_testBit x hn 2 ⟨i - 128, by omega⟩
        have hidx : i - 128 < 64 := by omega
        have h := (dc_zero_iff x[2].val 0 64).mp hd2 ⟨i - 128, hidx⟩
        calc
          (BigInt.value limbBits x).testBit i = x[2].val.testBit (i - 128) := by
            simpa [Nat.add_sub_of_le (by omega : 128 ≤ i)] using hv
          _ = true := by simpa using h
      · have hv := value_testBit x hn 3 ⟨i - 192, by omega⟩
        have hidx : i - 192 < 64 := by omega
        have h := (dc_zero_iff x[3].val 0 64).mp hd3 ⟨i - 192, hidx⟩
        calc
          (BigInt.value limbBits x).testBit i = x[3].val.testBit (i - 192) := by
            simpa [Nat.add_sub_of_le (by omega : 192 ≤ i)] using hv
          _ = true := by simpa using h

theorem topDC_ne_high_zero (x : Emu (F circomPrime)) (hn : BigInt.Normalized limbBits x)
    (ht : topDC x ≠ 0) :
    ∃ i, 33 ≤ i ∧ i < 256 ∧ (BigInt.value limbBits x).testBit i = false := by
  have hor : dc x[0].val 33 31 ≠ 0 ∨ dc x[1].val 0 64 ≠ 0 ∨
      dc x[2].val 0 64 ≠ 0 ∨ dc x[3].val 0 64 ≠ 0 := by
    unfold topDC at ht
    omega
  rcases hor with h0 | h1 | h2 | h3
  · rcases (dc_ne_iff x[0].val 33 31).mp h0 with ⟨j, hj⟩
    refine ⟨33 + j.val, by omega, by omega, ?_⟩
    calc
      (BigInt.value limbBits x).testBit (33 + j.val) =
          x[0].val.testBit (33 + j.val) := by
        simpa using value_testBit x hn 0 ⟨33 + j.val, by omega⟩
      _ = false := hj
  · rcases (dc_ne_iff x[1].val 0 64).mp h1 with ⟨j, hj⟩
    refine ⟨64 + j.val, by omega, by omega, ?_⟩
    calc
      (BigInt.value limbBits x).testBit (64 + j.val) = x[1].val.testBit j.val := by
        simpa using value_testBit x hn 1 j
      _ = false := by simpa using hj
  · rcases (dc_ne_iff x[2].val 0 64).mp h2 with ⟨j, hj⟩
    refine ⟨128 + j.val, by omega, by omega, ?_⟩
    calc
      (BigInt.value limbBits x).testBit (128 + j.val) = x[2].val.testBit j.val := by
        simpa using value_testBit x hn 2 j
      _ = false := by simpa using hj
  · rcases (dc_ne_iff x[3].val 0 64).mp h3 with ⟨j, hj⟩
    refine ⟨192 + j.val, by omega, by omega, ?_⟩
    calc
      (BigInt.value limbBits x).testBit (192 + j.val) = x[3].val.testBit j.val := by
        simpa using value_testBit x hn 3 j
      _ = false := by simpa using hj

set_option maxHeartbeats 1000000 in
theorem p_high_bit (i : ℕ) (hlo : 33 ≤ i) (hhi : i < 256) :
    P256.testBit i = true := by
  interval_cases i <;> decide +kernel

theorem lt_of_zero_in_one_run (N M lo hi : ℕ)
    (hz : ∃ i, lo ≤ i ∧ i < hi ∧ N.testBit i = false)
    (hm : ∀ i, lo ≤ i → i < hi → M.testBit i = true)
    (habove : ∀ j, hi ≤ j → N.testBit j = M.testBit j) : N < M := by
  let s := (Finset.range hi).filter fun i => lo ≤ i ∧ N.testBit i = false
  have hs : s.Nonempty := by
    rcases hz with ⟨i, hi0, hi1, hi2⟩
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi1, hi0, hi2⟩⟩
  let i := s.max' hs
  have himem : i ∈ s := Finset.max'_mem s hs
  have hip := Finset.mem_filter.mp himem
  have hiHi : i < hi := Finset.mem_range.mp hip.1
  have hiLo : lo ≤ i := hip.2.1
  have hiN : N.testBit i = false := hip.2.2
  refine Nat.lt_of_testBit i hiN (hm i hiLo hiHi) ?_
  intro j hij
  by_cases hj : j < hi
  · have hjlo : lo ≤ j := by omega
    have hmj := hm j hjlo hj
    have hNj : N.testBit j = true := by
      cases hbit : N.testBit j
      · have hjmem : j ∈ s := Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr hj, hjlo, hbit⟩
        have := Finset.le_max' s j hjmem
        omega
      · rfl
    rw [hNj, hmj]
  · exact habove j (by omega)

theorem lt_p_of_high_zero (N : ℕ) (hN : N < 2^256)
    (hz : ∃ i, 33 ≤ i ∧ i < 256 ∧ N.testBit i = false) : N < P256 := by
  refine lt_of_zero_in_one_run N P256 33 256 hz p_high_bit ?_
  intro j h256j
  have hpPow : 2^256 ≤ 2^j := Nat.pow_le_pow_right (by norm_num) h256j
  have hNb : N < 2^j := lt_of_lt_of_le hN hpPow
  have hPb : P256 < 2^j := lt_of_lt_of_le (by decide : P256 < 2^256) hpPow
  rw [Nat.testBit_eq_false_of_lt hNb, Nat.testBit_eq_false_of_lt hPb]

set_option maxHeartbeats 1000000 in
theorem p_mid_bit (i : ℕ) (hlo : 10 ≤ i) (hhi : i < 32) :
    P256.testBit i = true := by
  interval_cases i <;> decide +kernel

theorem value_testBit_limb0 (x : Emu (F circomPrime)) (hn : BigInt.Normalized limbBits x)
    (i : ℕ) (hi : i < 64) :
    (BigInt.value limbBits x).testBit i = x[0].val.testBit i := by
  simpa using value_testBit x hn 0 ⟨i, hi⟩

theorem equal_above32 (x : Emu (F circomPrime)) (hn : BigInt.Normalized limbBits x)
    (ht : topDC x = 0) (hb32 : x[0].val.testBit 32 = false) :
    ∀ j, 32 ≤ j → (BigInt.value limbBits x).testBit j = P256.testBit j := by
  intro j hj
  by_cases hj256 : j < 256
  · rcases eq_or_lt_of_le hj with rfl | hjgt
    · rw [value_testBit_limb0 x hn 32 (by omega), hb32]
      decide +kernel
    · rw [topDC_zero_high_bits x hn ht j (by omega) hj256,
        p_high_bit j (by omega) hj256]
  · have h256j : 256 ≤ j := by omega
    have hN := BigInt.value_lt hn
    norm_num [limbBits, numLimbs] at hN
    have hpPow : 2^256 ≤ 2^j := Nat.pow_le_pow_right (by norm_num) h256j
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hN hpPow),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by decide : P256 < 2^256) hpPow)]

theorem midDC_zero_mid_bits (x : Emu (F circomPrime)) (hn : BigInt.Normalized limbBits x)
    (hm : midDC x = 0) (i : ℕ) (hi0 : 10 ≤ i) (hi1 : i < 32) :
    (BigInt.value limbBits x).testBit i = true := by
  have hd : dc x[0].val 10 22 = 0 := hm
  have hidx : i - 10 < 22 := by omega
  have h := (dc_zero_iff x[0].val 10 22).mp hd ⟨i - 10, hidx⟩
  rw [value_testBit_limb0 x hn i (by omega)]
  simpa [Nat.add_sub_of_le hi0] using h

theorem midDC_ne_mid_zero (x : Emu (F circomPrime)) (hn : BigInt.Normalized limbBits x)
    (hm : midDC x ≠ 0) :
    ∃ i, 10 ≤ i ∧ i < 32 ∧ (BigInt.value limbBits x).testBit i = false := by
  rcases (dc_ne_iff x[0].val 10 22).mp hm with ⟨j, hj⟩
  refine ⟨10 + j.val, by omega, by omega, ?_⟩
  rw [value_testBit_limb0 x hn (10 + j.val) (by omega)]
  simpa using hj

theorem equal_above10 (x : Emu (F circomPrime)) (hn : BigInt.Normalized limbBits x)
    (ht : topDC x = 0) (hb32 : x[0].val.testBit 32 = false) (hm : midDC x = 0) :
    ∀ j, 10 ≤ j → (BigInt.value limbBits x).testBit j = P256.testBit j := by
  intro j hj
  by_cases hj32 : j < 32
  · rw [midDC_zero_mid_bits x hn hm j hj hj32, p_mid_bit j hj hj32]
  · exact equal_above32 x hn ht hb32 j (by omega)

set_option maxHeartbeats 1000000 in
theorem p_zero_6_10 (i : ℕ) (hlo : 6 ≤ i) (hhi : i < 10) :
    P256.testBit i = false := by
  interval_cases i <;> decide +kernel

set_option maxHeartbeats 1000000 in
theorem p_low_bit (i : ℕ) (hhi : i < 4) : P256.testBit i = true := by
  interval_cases i <;> decide +kernel

def zeroRun (x : Emu (F circomPrime)) : Prop :=
  ∀ i, 6 ≤ i → i < 10 → x[0].val.testBit i = false

def Pattern (x : Emu (F circomPrime)) : Prop :=
  topDC x ≠ 0 ∨
    (x[0].val.testBit 32 = false ∧
      (midDC x ≠ 0 ∨
        (zeroRun x ∧
          (x[0].val.testBit 5 = false ∨
            (x[0].val.testBit 4 = false ∧ lowDC x ≠ 0)))))

def bitNat (b : Bool) : ℕ := if b then 1 else 0

def bitField (b : Bool) : F circomPrime := if b then 1 else 0

theorem bitField_eq_natCast (b : Bool) : bitField b = (bitNat b : F circomPrime) := by
  cases b <;> rfl

theorem bitNat_le_one (b : Bool) : bitNat b ≤ 1 := by
  cases b <;> simp [bitNat]

theorem bitNat_zero_iff (b : Bool) : bitNat b = 0 ↔ b = false := by
  cases b <;> simp [bitNat]

theorem bitField_zero_iff (b : Bool) : bitField b = 0 ↔ b = false := by
  rw [bitField_eq_natCast, cast_zero_iff
    (lt_of_le_of_lt (bitNat_le_one b) (by decide +kernel : 1 < circomPrime)),
    bitNat_zero_iff]

theorem bitNat_sum4_lt_prime (a b c d : Bool) :
    bitNat a + bitNat b + bitNat c + bitNat d < circomPrime := by
  have ha := bitNat_le_one a
  have hb := bitNat_le_one b
  have hc := bitNat_le_one c
  have hd := bitNat_le_one d
  exact lt_of_le_of_lt (by omega) (by decide +kernel : 4 < circomPrime)

theorem split_boolean_sum_constraint (t z : F circomPrime) (b : Bool)
    (hz : z = 0 ∨ z = 1)
    (h : t * (bitField b + z) = 0) :
    t * bitField b = 0 ∧ t * z = 0 := by
  rcases hz with rfl | rfl
  · cases b <;> simp [bitField] at h ⊢ <;> exact h
  · cases b with
    | false => simpa [bitField] using h
    | true =>
        have htwo : (1 + 1 : F circomPrime) ≠ 0 := by decide
        have ht : t = 0 := (mul_eq_zero.mp (by simpa [bitField] using h)).resolve_right htwo
        simp [bitField, ht]

theorem pattern_of_constraints (x : Emu (F circomPrime))
    {topEq midEq throughMid through5 lowEq : F circomPrime}
    (htopEq : topEq = if topDC x = 0 then 1 else 0)
    (hbit32 : topEq * bitField (x[0].val.testBit 32) = 0)
    (hmidEq : midEq = if midDC x = 0 then 1 else 0)
    (hthroughMid : throughMid = topEq * midEq)
    (hzeroRun : throughMid *
      (bitField (x[0].val.testBit 9) + bitField (x[0].val.testBit 8) +
       bitField (x[0].val.testBit 7) + bitField (x[0].val.testBit 6)) = 0)
    (hthrough5 : through5 = throughMid * bitField (x[0].val.testBit 5))
    (hbit4 : through5 * bitField (x[0].val.testBit 4) = 0)
    (hlowEq : lowEq = if lowDC x = 0 then 1 else 0)
    (hstrict : through5 * lowEq = 0) : Pattern x := by
  by_cases ht : topDC x ≠ 0
  · exact Or.inl ht
  · have ht0 : topDC x = 0 := not_ne_iff.mp ht
    right
    have hb32 : x[0].val.testBit 32 = false := by
      apply (bitField_zero_iff _).mp
      rw [htopEq, if_pos ht0] at hbit32
      simpa only [one_mul] using hbit32
    refine ⟨hb32, ?_⟩
    by_cases hm : midDC x ≠ 0
    · exact Or.inl hm
    · have hm0 : midDC x = 0 := not_ne_iff.mp hm
      right
      have hsum := hzeroRun
      rw [hthroughMid, htopEq, if_pos ht0, hmidEq, if_pos hm0] at hsum
      simp only [one_mul] at hsum
      simp only [bitField_eq_natCast] at hsum
      have hsumNat := (cast_add4_zero_iff _ _ _ _
        (bitNat_sum4_lt_prime _ _ _ _)).mp hsum
      have hzeros : x[0].val.testBit 9 = false ∧
          x[0].val.testBit 8 = false ∧ x[0].val.testBit 7 = false ∧
          x[0].val.testBit 6 = false := by
        exact ⟨(bitNat_zero_iff _).mp (by omega),
          (bitNat_zero_iff _).mp (by omega),
          (bitNat_zero_iff _).mp (by omega),
          (bitNat_zero_iff _).mp (by omega)⟩
      have hz : zeroRun x := by
        intro i hi0 hi1
        interval_cases i <;> simp_all
      refine ⟨hz, ?_⟩
      by_cases hb5 : x[0].val.testBit 5 = false
      · exact Or.inl hb5
      · have hb5t : x[0].val.testBit 5 = true := by simpa using hb5
        right
        have hb4 : x[0].val.testBit 4 = false := by
          apply (bitField_zero_iff _).mp
          rw [hthrough5, hthroughMid, htopEq, if_pos ht0, hmidEq, if_pos hm0] at hbit4
          simpa only [bitField, hb5t, if_true, one_mul] using hbit4
        refine ⟨hb4, ?_⟩
        intro hl0
        rw [hthrough5, hthroughMid, htopEq, if_pos ht0, hmidEq, if_pos hm0,
          hlowEq, if_pos hl0] at hstrict
        simp [bitField, hb5t] at hstrict

theorem constraints_of_pattern (x : Emu (F circomPrime))
    {topEq midEq throughMid through5 lowEq : F circomPrime}
    (htopEq : topEq = if topDC x = 0 then 1 else 0)
    (hmidEq : midEq = if midDC x = 0 then 1 else 0)
    (hthroughMid : throughMid = topEq * midEq)
    (hthrough5 : through5 = throughMid * bitField (x[0].val.testBit 5))
    (hlowEq : lowEq = if lowDC x = 0 then 1 else 0)
    (hpatt : Pattern x) :
    topEq * bitField (x[0].val.testBit 32) = 0 ∧
      throughMid *
        (bitField (x[0].val.testBit 9) + bitField (x[0].val.testBit 8) +
         bitField (x[0].val.testBit 7) + bitField (x[0].val.testBit 6)) = 0 ∧
      through5 * bitField (x[0].val.testBit 4) = 0 ∧
      through5 * lowEq = 0 := by
  by_cases ht : topDC x ≠ 0
  · simp [htopEq, ht, hthroughMid, hthrough5]
  · have ht0 : topDC x = 0 := not_ne_iff.mp ht
    rcases hpatt with htop | ⟨hb32, hrest⟩
    · exact (ht htop).elim
    by_cases hm : midDC x ≠ 0
    · simp [htopEq, ht0, hmidEq, hm, hthroughMid, hthrough5, bitField, hb32]
    · have hm0 : midDC x = 0 := not_ne_iff.mp hm
      rcases hrest with hmid | ⟨hz, hlow⟩
      · exact (hm hmid).elim
      have h9 := hz 9 (by omega) (by omega)
      have h8 := hz 8 (by omega) (by omega)
      have h7 := hz 7 (by omega) (by omega)
      have h6 := hz 6 (by omega) (by omega)
      by_cases hb5 : x[0].val.testBit 5 = false
      · simp [htopEq, ht0, hmidEq, hm0, hthroughMid, hthrough5, bitField,
          hb32, h9, h8, h7, h6, hb5]
      · have hb5t : x[0].val.testBit 5 = true := by simpa using hb5
        rcases hlow with hb5f | ⟨hb4, hl⟩
        · exact (hb5 hb5f).elim
        simp [htopEq, ht0, hmidEq, hm0, hthroughMid, hthrough5, hlowEq,
          bitField, hb32, h9, h8, h7, h6, hb5t, hb4, hl]

theorem equal_above33 (x : Emu (F circomPrime)) (hn : BigInt.Normalized limbBits x)
    (ht : topDC x = 0) :
    ∀ j, 33 ≤ j → (BigInt.value limbBits x).testBit j = P256.testBit j := by
  intro j hj
  by_cases hj256 : j < 256
  · rw [topDC_zero_high_bits x hn ht j hj hj256, p_high_bit j hj hj256]
  · have h256j : 256 ≤ j := by omega
    have hN := BigInt.value_lt hn
    norm_num [limbBits, numLimbs] at hN
    have hpPow : 2^256 ≤ 2^j := Nat.pow_le_pow_right (by norm_num) h256j
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hN hpPow),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by decide : P256 < 2^256) hpPow)]

theorem equal_above5 (x : Emu (F circomPrime)) (hn : BigInt.Normalized limbBits x)
    (ht : topDC x = 0) (hb32 : x[0].val.testBit 32 = false) (hm : midDC x = 0)
    (hz : zeroRun x) :
    ∀ j, 5 < j → (BigInt.value limbBits x).testBit j = P256.testBit j := by
  intro j hj
  by_cases hj10 : j < 10
  · rw [value_testBit_limb0 x hn j (by omega), hz j (by omega) hj10,
      p_zero_6_10 j (by omega) hj10]
  · exact equal_above10 x hn ht hb32 hm j (by omega)

theorem equal_above4 (x : Emu (F circomPrime)) (hn : BigInt.Normalized limbBits x)
    (ht : topDC x = 0) (hb32 : x[0].val.testBit 32 = false) (hm : midDC x = 0)
    (hz : zeroRun x) (hb5 : x[0].val.testBit 5 = true) :
    ∀ j, 4 < j → (BigInt.value limbBits x).testBit j = P256.testBit j := by
  intro j hj
  rcases eq_or_lt_of_le (by omega : 5 ≤ j) with rfl | hj5
  · rw [value_testBit_limb0 x hn 5 (by omega), hb5]
    decide +kernel
  · exact equal_above5 x hn ht hb32 hm hz j hj5

theorem lowDC_ne_low_zero (x : Emu (F circomPrime)) (hn : BigInt.Normalized limbBits x)
    (hl : lowDC x ≠ 0) :
    ∃ i, i < 4 ∧ (BigInt.value limbBits x).testBit i = false := by
  rcases (dc_ne_iff x[0].val 0 4).mp hl with ⟨j, hj⟩
  refine ⟨j.val, j.isLt, ?_⟩
  rw [value_testBit_limb0 x hn j.val (by omega)]
  simpa using hj

theorem lt_of_one_in_zero_run (N M lo hi : ℕ)
    (hz : ∃ i, lo ≤ i ∧ i < hi ∧ N.testBit i = true)
    (hm : ∀ i, lo ≤ i → i < hi → M.testBit i = false)
    (habove : ∀ j, hi ≤ j → N.testBit j = M.testBit j) : M < N := by
  let s := (Finset.range hi).filter fun i => lo ≤ i ∧ N.testBit i = true
  have hs : s.Nonempty := by
    rcases hz with ⟨i, hi0, hi1, hi2⟩
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi1, hi0, hi2⟩⟩
  let i := s.max' hs
  have himem : i ∈ s := Finset.max'_mem s hs
  have hip := Finset.mem_filter.mp himem
  have hiHi : i < hi := Finset.mem_range.mp hip.1
  have hiLo : lo ≤ i := hip.2.1
  have hiN : N.testBit i = true := hip.2.2
  refine Nat.lt_of_testBit i (hm i hiLo hiHi) hiN ?_
  intro j hij
  by_cases hj : j < hi
  · have hjlo : lo ≤ j := by omega
    have hmj := hm j hjlo hj
    have hNj : N.testBit j = false := by
      cases hbit : N.testBit j
      · rfl
      · have hjmem : j ∈ s := Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr hj, hjlo, hbit⟩
        have := Finset.le_max' s j hjmem
        omega
    rw [hNj, hmj]
  · exact (habove j (by omega)).symm

set_option maxRecDepth 5000 in
theorem pattern_iff_lt (x : Emu (F circomPrime)) (hn : BigInt.Normalized limbBits x) :
    Pattern x ↔ BigInt.value limbBits x < P256 := by
  let N := BigInt.value limbBits x
  have hN : N < 2^256 := by
    have := BigInt.value_lt hn
    simpa [N, limbBits, numLimbs] using this
  constructor
  · intro hpatt
    by_cases ht : topDC x ≠ 0
    · exact lt_p_of_high_zero N hN (topDC_ne_high_zero x hn ht)
    · have ht0 : topDC x = 0 := not_ne_iff.mp ht
      rcases hpatt with htop | ⟨hb32, hrest⟩
      · exact (ht htop).elim
      by_cases hm : midDC x ≠ 0
      · exact lt_of_zero_in_one_run N P256 10 32 (midDC_ne_mid_zero x hn hm)
          p_mid_bit (equal_above32 x hn ht0 hb32)
      · have hm0 : midDC x = 0 := not_ne_iff.mp hm
        rcases hrest with hmid | ⟨hz, hlow⟩
        · exact (hm hmid).elim
        by_cases hb5 : x[0].val.testBit 5 = false
        · refine Nat.lt_of_testBit 5 ?_ (by decide +kernel) ?_
          · rw [value_testBit_limb0 x hn 5 (by omega), hb5]
          · exact equal_above5 x hn ht0 hb32 hm0 hz
        · have hb5t : x[0].val.testBit 5 = true := by simpa using hb5
          rcases hlow with hb5f | ⟨hb4, hl⟩
          · exact (hb5 hb5f).elim
          exact lt_of_zero_in_one_run N P256 0 4
            (by simpa [N] using lowDC_ne_low_zero x hn hl)
            (fun i _ hi => p_low_bit i hi)
            (fun j hj => by
              rcases eq_or_lt_of_le hj with rfl | hj4
              · rw [value_testBit_limb0 x hn 4 (by omega), hb4]
                decide +kernel
              · exact equal_above4 x hn ht0 hb32 hm0 hz hb5t j hj4)
  · intro hlt
    by_cases ht : topDC x ≠ 0
    · exact Or.inl ht
    · right
      have ht0 : topDC x = 0 := not_ne_iff.mp ht
      have hb32 : x[0].val.testBit 32 = false := by
        cases hb : x[0].val.testBit 32
        · rfl
        · exfalso
          have hPN : P256 < N := Nat.lt_of_testBit 32 (by decide +kernel)
            (by rw [value_testBit_limb0 x hn 32 (by omega), hb])
            (fun j hj => (equal_above33 x hn ht0 j (by omega)).symm)
          omega
      refine ⟨hb32, ?_⟩
      by_cases hm : midDC x ≠ 0
      · exact Or.inl hm
      · right
        have hm0 : midDC x = 0 := not_ne_iff.mp hm
        have hz : zeroRun x := by
          intro i hi0 hi1
          cases hb : x[0].val.testBit i
          · rfl
          · exfalso
            have hNi : N.testBit i = true := by
              rw [value_testBit_limb0 x hn i (by omega), hb]
            have hPN : P256 < N := lt_of_one_in_zero_run N P256 6 10
              ⟨i, hi0, hi1, hNi⟩ p_zero_6_10
              (fun j hj => equal_above10 x hn ht0 hb32 hm0 j hj)
            omega
        refine ⟨hz, ?_⟩
        cases hb5 : x[0].val.testBit 5
        · exact Or.inl (by simpa using hb5)
        · right
          have hb4 : x[0].val.testBit 4 = false := by
            cases h4 : x[0].val.testBit 4
            · rfl
            · exfalso
              have hPN : P256 < N := Nat.lt_of_testBit 4 (by decide +kernel)
                (by rw [value_testBit_limb0 x hn 4 (by omega), h4])
                (fun j hj => (equal_above4 x hn ht0 hb32 hm0 hz hb5 j hj).symm)
              omega
          refine ⟨hb4, ?_⟩
          intro hl0
          have hEq : N = P256 := Nat.eq_of_testBit_eq fun i => by
            by_cases hi4 : i < 4
            · have hli : x[0].val.testBit i = true := by
                simpa using (dc_zero_iff x[0].val 0 4).mp hl0 ⟨i, hi4⟩
              rw [value_testBit_limb0 x hn i (by omega)]
              rw [hli, p_low_bit i hi4]
            · rcases eq_or_lt_of_le (by omega : 4 ≤ i) with rfl | hi
              · rw [value_testBit_limb0 x hn 4 (by omega), hb4]
                decide +kernel
              · exact equal_above4 x hn ht0 hb32 hm0 hz hb5 i hi
          omega

end ValidP
end Solution.Secp256k1ScalarMul
