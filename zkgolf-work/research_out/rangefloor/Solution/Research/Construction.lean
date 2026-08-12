/-
  # A range check of score `2 * n - 1`

  The folklore construction witnesses `n` bits and asserts `n` booleanity rows, for a
  score of `⟨n, n⟩ = 2 * n`.  But the recomposition `x = ∑ 2 ^ i * b i` is affine and
  therefore free, so the lowest bit need not be allocated at all: it is *defined* as the
  affine form `b₀ := x - ∑_{i ≥ 1} 2 ^ i * b i`, and booleanity of that affine form is
  still one single row.

  That gives `⟨n - 1, n⟩ = 2 * n - 1`, which beats `2 * n` for every `n ≥ 1`.
-/
import Solution.Research.Model

namespace Solution.Research

open Finset

variable {F : Type*} [Field F] {m : ℕ}

/-! ## Natural number preliminaries -/

/-- Binary expansion: the first `n` binary digits of `k` recompose `k % 2 ^ n`. -/
theorem sum_two_pow_mul_bit (n k : ℕ) :
    ∑ i ∈ range n, 2 ^ i * (k / 2 ^ i % 2) = k % 2 ^ n := by
  induction n generalizing k with
  | zero => simp [Nat.mod_one]
  | succ n ih =>
    rw [Finset.sum_range_succ']
    have h : ∀ i ∈ range n, 2 ^ (i + 1) * (k / 2 ^ (i + 1) % 2)
        = 2 * (2 ^ i * (k / 2 / 2 ^ i % 2)) := by
      intro i _
      rw [Nat.div_div_eq_div_mul, show (2 : ℕ) * 2 ^ i = 2 ^ (i + 1) by ring]
      ring
    rw [Finset.sum_congr rfl h, ← Finset.mul_sum, ih (k / 2)]
    have hm : k % 2 ^ (n + 1) = k % 2 + 2 * (k / 2 % 2 ^ n) := by
      rw [pow_succ, mul_comm (2 ^ n) 2, Nat.mod_mul]
    simp only [pow_zero, one_mul, Nat.div_one]
    omega

/-- A sum of `n` binary digits weighted by powers of two is `< 2 ^ n`. -/
theorem sum_two_pow_mul_lt (n : ℕ) (c : ℕ → ℕ) (hc : ∀ i, c i ≤ 1) :
    ∑ i ∈ range n, 2 ^ i * c i < 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have : 2 ^ n * c n ≤ 2 ^ n := by
      calc 2 ^ n * c n ≤ 2 ^ n * 1 := Nat.mul_le_mul_left _ (hc n)
        _ = 2 ^ n := by ring
    omega

/-! ## The system -/

/-- The affine form `b₀ = x - ∑_{i < m} 2 ^ (i+1) * w i`, the implicitly defined low bit. -/
def lowBit (F : Type*) [Field F] (m : ℕ) : Aff F m where
  cx := 1
  cw := fun i => -(2 ^ ((i : ℕ) + 1))
  c := 0

/-- The affine form selecting the `i`-th witness. -/
def sel (F : Type*) [Field F] {m : ℕ} (i : Fin m) : Aff F m where
  cx := 0
  cw := fun j => if j = i then 1 else 0
  c := 0

/-- Booleanity row for an affine form `L` : `L * (L - 1) = 0`. -/
def boolRow (L : Aff F m) : Row F m where
  A := L
  B := { L with c := L.c - 1 }
  C := { cx := 0, cw := 0, c := 0 }

/-- The score-`(2 * (m+1) - 1)` system certifying the `(m+1)`-bit range:
    `m` allocated bits `w 0, …, w (m-1)`, and `m + 1` booleanity rows — the extra row
    being booleanity of the *free affine form* `x - ∑ 2 ^ (i+1) * w i`. -/
def rangeSystem (F : Type*) [Field F] (m : ℕ) : System F m (m + 1) where
  row := Fin.cases (boolRow (lowBit F m)) (fun i => boolRow (sel F i))

@[simp] theorem sel_eval {m : ℕ} (i : Fin m) (x : F) (w : Fin m → F) :
    (sel F i).eval x w = w i := by
  simp [sel, Aff.eval]

@[simp] theorem lowBit_eval {m : ℕ} (x : F) (w : Fin m → F) :
    (lowBit F m).eval x w = x - ∑ i : Fin m, 2 ^ ((i : ℕ) + 1) * w i := by
  simp [lowBit, Aff.eval, sub_eq_add_neg, Finset.sum_neg_distrib]

theorem boolRow_holds_iff (L : Aff F m) (x : F) (w : Fin m → F) :
    (boolRow L).Holds x w ↔ L.eval x w = 0 ∨ L.eval x w = 1 := by
  have hB : ({ L with c := L.c - 1 } : Aff F m).eval x w = L.eval x w - 1 := by
    simp only [Aff.eval]; ring
  have hC : ({ cx := 0, cw := 0, c := 0 } : Aff F m).eval x w = 0 := by
    simp [Aff.eval]
  simp only [Row.Holds, boolRow, hB, hC, mul_eq_zero, sub_eq_zero]

/-- Satisfaction of the whole system, unfolded. -/
theorem rangeSystem_sat_iff {m : ℕ} (x : F) :
    (rangeSystem F m).Sat x ↔ ∃ w : Fin m → F,
      (∀ i, w i = 0 ∨ w i = 1) ∧
      (x - ∑ i : Fin m, 2 ^ ((i : ℕ) + 1) * w i = 0 ∨
       x - ∑ i : Fin m, 2 ^ ((i : ℕ) + 1) * w i = 1) := by
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨w, ?_, ?_⟩
    · intro i
      have := hw i.succ
      rw [show (rangeSystem F m).row i.succ = boolRow (sel F i) from by
        simp [rangeSystem]] at this
      simpa using (boolRow_holds_iff _ x w).1 this
    · have := hw 0
      rw [show (rangeSystem F m).row 0 = boolRow (lowBit F m) from by
        simp [rangeSystem]] at this
      simpa using (boolRow_holds_iff _ x w).1 this
  · rintro ⟨w, hbits, hlow⟩
    refine ⟨w, ?_⟩
    intro j
    refine Fin.cases ?_ ?_ j
    · rw [show (rangeSystem F m).row 0 = boolRow (lowBit F m) from by simp [rangeSystem]]
      exact (boolRow_holds_iff _ x w).2 (by simpa using hlow)
    · intro i
      rw [show (rangeSystem F m).row i.succ = boolRow (sel F i) from by simp [rangeSystem]]
      exact (boolRow_holds_iff _ x w).2 (by simpa using hbits i)

/-! ## The main construction theorem -/

/-- A field element that is a weighted sum of `n` bits is the image of a natural `< 2 ^ n`. -/
theorem exists_nat_lt_of_bits (n : ℕ) (b : ℕ → F) (hb : ∀ j, b j = 0 ∨ b j = 1) :
    ∃ k : ℕ, k < 2 ^ n ∧ ∑ j ∈ range n, 2 ^ j * b j = (k : F) := by
  classical
  refine ⟨∑ j ∈ range n, 2 ^ j * (if b j = 1 then 1 else 0), ?_, ?_⟩
  · exact sum_two_pow_mul_lt n _ (by intro i; split <;> simp)
  · push_cast
    refine Finset.sum_congr rfl ?_
    intro j _
    rcases hb j with h | h <;> simp [h]

/-- **The construction.**  For every field `F` and every `m`, the system `rangeSystem F m`
    — `m` witness allocations and `m + 1` rows — certifies the `(m + 1)`-bit range.
    Its score is `m + (m + 1) = 2 * (m + 1) - 1`. -/
theorem rangeSystem_certifies (m : ℕ) : (rangeSystem F m).Certifies (m + 1) := by
  classical
  intro x
  rw [rangeSystem_sat_iff]
  constructor
  · rintro ⟨w, hbits, hlow⟩
    set b0 : F := x - ∑ i : Fin m, 2 ^ ((i : ℕ) + 1) * w i with hb0
    set W : ℕ → F := fun j => if h : j < m then w ⟨j, h⟩ else 0 with hW
    set b : ℕ → F := fun j => if j = 0 then b0 else W (j - 1) with hb
    have hbval : ∀ j, b j = 0 ∨ b j = 1 := by
      intro j
      rcases Nat.eq_zero_or_pos j with h | h
      · subst h; simpa [hb] using hlow
      · have hbj : b j = W (j - 1) := by
          simp only [hb]
          rw [if_neg (by omega)]
        rw [hbj, hW]
        by_cases hlt : j - 1 < m
        · simp only [dif_pos hlt]; exact hbits _
        · simp [dif_neg hlt]
    obtain ⟨k, hk, hsum⟩ := exists_nat_lt_of_bits (m + 1) b hbval
    refine ⟨k, hk, ?_⟩
    rw [← hsum, Finset.sum_range_succ']
    have : ∀ j ∈ range m, (2 : F) ^ (j + 1) * b (j + 1) = 2 ^ (j + 1) * W j := by
      intro j _; simp [hb]
    rw [Finset.sum_congr rfl this]
    have hWsum : ∑ j ∈ range m, (2 : F) ^ (j + 1) * W j
        = ∑ i : Fin m, 2 ^ ((i : ℕ) + 1) * w i := by
      rw [← Fin.sum_univ_eq_sum_range (fun j => (2 : F) ^ (j + 1) * W j) m]
      refine Finset.sum_congr rfl ?_
      intro i _
      simp [hW, i.isLt]
    rw [hWsum]
    simp [hb, hb0]
  · rintro ⟨k, hk, rfl⟩
    refine ⟨fun i => ((k / 2 ^ ((i : ℕ) + 1) % 2 : ℕ) : F), ?_, ?_⟩
    · intro i
      have h2 : k / 2 ^ ((i : ℕ) + 1) % 2 = 0 ∨ k / 2 ^ ((i : ℕ) + 1) % 2 = 1 := by omega
      rcases h2 with h | h <;> simp [h]
    · have hnat : (∑ j ∈ range m, 2 ^ (j + 1) * (k / 2 ^ (j + 1) % 2)) + k % 2 = k := by
        have h1 := sum_two_pow_mul_bit (m + 1) k
        rw [Finset.sum_range_succ'] at h1
        rw [Nat.mod_eq_of_lt hk] at h1
        simpa using h1
      have hcast : ∑ i : Fin m, (2 : F) ^ ((i : ℕ) + 1) * ((k / 2 ^ ((i : ℕ) + 1) % 2 : ℕ) : F)
          = ((∑ j ∈ range m, 2 ^ (j + 1) * (k / 2 ^ (j + 1) % 2) : ℕ) : F) := by
        rw [Nat.cast_sum,
          ← Fin.sum_univ_eq_sum_range
            (fun j => ((2 ^ (j + 1) * (k / 2 ^ (j + 1) % 2) : ℕ) : F)) m]
        refine Finset.sum_congr rfl ?_
        intro i _
        push_cast
        ring
      rw [hcast]
      have : ((k : ℕ) : F) - ((∑ j ∈ range m, 2 ^ (j + 1) * (k / 2 ^ (j + 1) % 2) : ℕ) : F)
          = ((k % 2 : ℕ) : F) := by
        have hc2 : ((k : ℕ) : F)
            = ((∑ j ∈ range m, 2 ^ (j + 1) * (k / 2 ^ (j + 1) % 2) : ℕ) : F)
              + ((k % 2 : ℕ) : F) := by
          rw [← Nat.cast_add, hnat]
        rw [hc2]
        ring
      rw [this]
      have h2 : k % 2 = 0 ∨ k % 2 = 1 := by omega
      rcases h2 with h | h <;> simp [h]

/-- The score of the construction is `2 * n - 1`, strictly below the folklore `2 * n`. -/
theorem exists_system_score_lt_two_mul (n : ℕ) (hn : 1 ≤ n) :
    ∃ (S : System F (n - 1) n), S.Certifies n ∧ S.score = 2 * n - 1 ∧ S.score < 2 * n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  refine ⟨by simpa using rangeSystem F m, ?_, ?_, ?_⟩
  · simpa using rangeSystem_certifies (F := F) m
  · simp [System.score]; omega
  · simp [System.score]; omega

end Solution.Research
