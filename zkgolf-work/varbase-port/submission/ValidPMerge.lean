import Solution.Secp256k1ScalarMul.ValidPTheorems

/-!
# Merged sparse-prime comparison rows

`ValidP` proves `x < p` for `p = 2^256 - 2^32 - 977` from the bit
decomposition of the four limbs.  The prefix-equality chain of the original
formulation spends three separate `assertZero` rows,

```
topEq * b32 = 0
throughMid * (b9 + b8 + b7 + b6) = 0
through5 * (b4 + lowEq) = 0
```

Every summand occurring in those rows is a `0/1` value, so the three rows can
be collapsed into a single row by nesting the products into two auxiliary
witnesses that replace `throughMid` and `through5`:

```
u <== b5 * (b4 + lowEq)
v <== midEq * ((b9 + b8 + b7 + b6) + u)
topEq * (b32 + v) = 0
```

This keeps the witness count (`8` for the tail) but drops two rows, because a
sum of `0/1` values vanishes exactly when every summand vanishes.

`split_merged` recovers the four original constraint facts from the merged
row (soundness) and `merged_of_constraints` rebuilds the merged row from them
(completeness).
-/

namespace Solution.Secp256k1ScalarMul
namespace ValidP

/-- A sum of seven `0/1` field elements vanishes only if every summand does. -/
private lemma exists_nat_of_zeroOne {x : F circomPrime} (h : x = 0 ∨ x = 1) :
    ∃ n : ℕ, n ≤ 1 ∧ x = (n : F circomPrime) := by
  rcases h with rfl | rfl
  · exact ⟨0, by norm_num⟩
  · exact ⟨1, by norm_num⟩

theorem zeroOne_sum7_zero {a b c d e f g : F circomPrime}
    (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) (hc : c = 0 ∨ c = 1)
    (hd : d = 0 ∨ d = 1) (he : e = 0 ∨ e = 1) (hf : f = 0 ∨ f = 1)
    (hg : g = 0 ∨ g = 1)
    (h : a + b + c + d + e + f + g = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 ∧ e = 0 ∧ f = 0 ∧ g = 0 := by
  obtain ⟨na, hna, rfl⟩ := exists_nat_of_zeroOne ha
  obtain ⟨nb, hnb, rfl⟩ := exists_nat_of_zeroOne hb
  obtain ⟨nc, hnc, rfl⟩ := exists_nat_of_zeroOne hc
  obtain ⟨nd, hnd, rfl⟩ := exists_nat_of_zeroOne hd
  obtain ⟨ne, hne, rfl⟩ := exists_nat_of_zeroOne he
  obtain ⟨nf, hnf, rfl⟩ := exists_nat_of_zeroOne hf
  obtain ⟨ng, hng, rfl⟩ := exists_nat_of_zeroOne hg
  have hsum : ((na + nb + nc + nd + ne + nf + ng : ℕ) : F circomPrime) = 0 := by
    push_cast
    linear_combination h
  have hlt : na + nb + nc + nd + ne + nf + ng < circomPrime :=
    lt_of_le_of_lt (by omega) (by decide +kernel : 7 < circomPrime)
  have hzero := (cast_zero_iff hlt).mp hsum
  have e1 : na = 0 := by omega
  have e2 : nb = 0 := by omega
  have e3 : nc = 0 := by omega
  have e4 : nd = 0 := by omega
  have e5 : ne = 0 := by omega
  have e6 : nf = 0 := by omega
  have e7 : ng = 0 := by omega
  exact ⟨by simp [e1], by simp [e2], by simp [e3], by simp [e4], by simp [e5],
    by simp [e6], by simp [e7]⟩

/-- `bitField` values are `0/1`. -/
theorem bitField_zeroOne (b : Bool) : bitField b = 0 ∨ bitField b = 1 := by
  cases b <;> simp [bitField]

/-- Splitting the merged row back into the four constraint facts consumed by
`pattern_of_constraints`. -/
theorem split_merged (x : Emu (F circomPrime))
    {topEq midEq lowEq u v : F circomPrime}
    (htopEq : topEq = if topDC x = 0 then 1 else 0)
    (hmidEq : midEq = if midDC x = 0 then 1 else 0)
    (hlowEq : lowEq = if lowDC x = 0 then 1 else 0)
    (hu : u = bitField (x[0].val.testBit 5) *
      (bitField (x[0].val.testBit 4) + lowEq))
    (hv : v = midEq *
      (bitField (x[0].val.testBit 9) + bitField (x[0].val.testBit 8) +
        bitField (x[0].val.testBit 7) + bitField (x[0].val.testBit 6) + u))
    (h : topEq * (bitField (x[0].val.testBit 32) + v) = 0) :
    topEq * bitField (x[0].val.testBit 32) = 0 ∧
      (topEq * midEq) *
        (bitField (x[0].val.testBit 9) + bitField (x[0].val.testBit 8) +
          bitField (x[0].val.testBit 7) + bitField (x[0].val.testBit 6)) = 0 ∧
      ((topEq * midEq) * bitField (x[0].val.testBit 5)) *
        bitField (x[0].val.testBit 4) = 0 ∧
      ((topEq * midEq) * bitField (x[0].val.testBit 5)) * lowEq = 0 := by
  have htb : topEq = 0 ∨ topEq = 1 := by rw [htopEq]; split <;> simp
  have hmb : midEq = 0 ∨ midEq = 1 := by rw [hmidEq]; split <;> simp
  have hlb : lowEq = 0 ∨ lowEq = 1 := by rw [hlowEq]; split <;> simp
  subst hu hv
  rcases htb with ht | ht
  · subst ht; exact ⟨by ring, by ring, by ring, by ring⟩
  rcases hmb with hm | hm
  · subst ht; subst hm
    exact ⟨by linear_combination h, by ring, by ring, by ring⟩
  subst ht; subst hm
  cases hb5 : x[0].val.testBit 5 with
  | false =>
      rw [hb5] at h
      have hbf : bitField false = (0 : F circomPrime) := rfl
      rw [hbf] at h ⊢
      obtain ⟨e32, e9, e8, e7, e6, -, -⟩ :=
        zeroOne_sum7_zero (bitField_zeroOne (x[0].val.testBit 32))
          (bitField_zeroOne (x[0].val.testBit 9)) (bitField_zeroOne (x[0].val.testBit 8))
          (bitField_zeroOne (x[0].val.testBit 7)) (bitField_zeroOne (x[0].val.testBit 6))
          (Or.inl rfl) (Or.inl rfl)
          (by linear_combination h :
            bitField (x[0].val.testBit 32) + bitField (x[0].val.testBit 9) +
              bitField (x[0].val.testBit 8) + bitField (x[0].val.testBit 7) +
              bitField (x[0].val.testBit 6) + (0 : F circomPrime) +
              (0 : F circomPrime) = 0)
      exact ⟨by rw [e32]; ring, by rw [e9, e8, e7, e6]; ring, by ring, by ring⟩
  | true =>
      rw [hb5] at h
      have hbt : bitField true = (1 : F circomPrime) := rfl
      rw [hbt] at h ⊢
      obtain ⟨e32, e9, e8, e7, e6, e4, el⟩ :=
        zeroOne_sum7_zero (bitField_zeroOne (x[0].val.testBit 32))
          (bitField_zeroOne (x[0].val.testBit 9)) (bitField_zeroOne (x[0].val.testBit 8))
          (bitField_zeroOne (x[0].val.testBit 7)) (bitField_zeroOne (x[0].val.testBit 6))
          (bitField_zeroOne (x[0].val.testBit 4)) hlb
          (by linear_combination h :
            bitField (x[0].val.testBit 32) + bitField (x[0].val.testBit 9) +
              bitField (x[0].val.testBit 8) + bitField (x[0].val.testBit 7) +
              bitField (x[0].val.testBit 6) + bitField (x[0].val.testBit 4) +
              lowEq = 0)
      exact ⟨by rw [e32]; ring, by rw [e9, e8, e7, e6]; ring,
        by rw [e4]; ring, by rw [el]; ring⟩

/-- The merged row follows from the four original constraint facts. -/
theorem merged_of_constraints (x : Emu (F circomPrime))
    {topEq midEq lowEq u v : F circomPrime}
    (hu : u = bitField (x[0].val.testBit 5) *
      (bitField (x[0].val.testBit 4) + lowEq))
    (hv : v = midEq *
      (bitField (x[0].val.testBit 9) + bitField (x[0].val.testBit 8) +
        bitField (x[0].val.testBit 7) + bitField (x[0].val.testBit 6) + u))
    (h1 : topEq * bitField (x[0].val.testBit 32) = 0)
    (h2 : (topEq * midEq) *
      (bitField (x[0].val.testBit 9) + bitField (x[0].val.testBit 8) +
        bitField (x[0].val.testBit 7) + bitField (x[0].val.testBit 6)) = 0)
    (h3 : ((topEq * midEq) * bitField (x[0].val.testBit 5)) *
      bitField (x[0].val.testBit 4) = 0)
    (h4 : ((topEq * midEq) * bitField (x[0].val.testBit 5)) * lowEq = 0) :
    topEq * (bitField (x[0].val.testBit 32) + v) = 0 := by
  subst hv hu
  linear_combination h1 + h2 + h3 + h4

/-- Soundness bridge: the merged row implies the comparison `Pattern`. -/
theorem pattern_of_merged (x : Emu (F circomPrime))
    {topEq midEq lowEq u v : F circomPrime}
    (htopEq : topEq = if topDC x = 0 then 1 else 0)
    (hmidEq : midEq = if midDC x = 0 then 1 else 0)
    (hlowEq : lowEq = if lowDC x = 0 then 1 else 0)
    (hu : u = bitField (x[0].val.testBit 5) *
      (bitField (x[0].val.testBit 4) + lowEq))
    (hv : v = midEq *
      (bitField (x[0].val.testBit 9) + bitField (x[0].val.testBit 8) +
        bitField (x[0].val.testBit 7) + bitField (x[0].val.testBit 6) + u))
    (h : topEq * (bitField (x[0].val.testBit 32) + v) = 0) :
    Pattern x := by
  obtain ⟨h1, h2, h3, h4⟩ := split_merged x htopEq hmidEq hlowEq hu hv h
  exact pattern_of_constraints x htopEq h1 hmidEq rfl h2 rfl h3 hlowEq h4

/-- Completeness bridge: the comparison `Pattern` implies the merged row. -/
theorem merged_of_pattern (x : Emu (F circomPrime))
    {topEq midEq lowEq u v : F circomPrime}
    (htopEq : topEq = if topDC x = 0 then 1 else 0)
    (hmidEq : midEq = if midDC x = 0 then 1 else 0)
    (hlowEq : lowEq = if lowDC x = 0 then 1 else 0)
    (hu : u = bitField (x[0].val.testBit 5) *
      (bitField (x[0].val.testBit 4) + lowEq))
    (hv : v = midEq *
      (bitField (x[0].val.testBit 9) + bitField (x[0].val.testBit 8) +
        bitField (x[0].val.testBit 7) + bitField (x[0].val.testBit 6) + u))
    (hpatt : Pattern x) :
    topEq * (bitField (x[0].val.testBit 32) + v) = 0 := by
  obtain ⟨h1, h2, h3, h4⟩ :=
    constraints_of_pattern x htopEq hmidEq rfl rfl hlowEq hpatt
  exact merged_of_constraints x hu hv h1 h2 h3 h4

end ValidP
end Solution.Secp256k1ScalarMul
