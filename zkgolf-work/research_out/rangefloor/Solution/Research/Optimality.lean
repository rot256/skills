/-
  # Putting the two halves together

  Over an algebraically closed field of characteristic zero:

  * every system certifying a range of `n ≥ 2` bits has score at least `3`
    (`score_ge_three`);
  * the score-`3` system of `Solution.Research.Construction` certifies the `2`-bit range.

  Hence for `n = 2` the exact optimum is `3 = 2 * n - 1`: the folklore `2 * n` is *not*
  optimal, and `2 * n - 1` cannot be improved at `n = 2`.
-/
import Solution.Research.Construction
import Solution.Research.LowerBound
import Solution.Research.OneWitness

namespace Solution.Research

variable {F : Type*} [Field F] {m r n : ℕ}

/-! ## Basic facts about the target set -/

theorem nat_mem_rangeSet {k : ℕ} (h : k < 2 ^ n) : ((k : ℕ) : F) ∈ RangeSet F n := ⟨k, h, rfl⟩

theorem nat_notMem_rangeSet [CharZero F] {k : ℕ} (h : ¬ k < 2 ^ n) :
    ((k : ℕ) : F) ∉ RangeSet F n := by
  rintro ⟨k', hk', hk⟩
  have hkk : k = k' := Nat.cast_injective hk
  subst hkk
  exact h hk'

theorem rangeSet_ne_univ [CharZero F] : RangeSet F n ≠ Set.univ := by
  intro h
  exact nat_notMem_rangeSet (F := F) (k := 2 ^ n) (by omega) (h ▸ Set.mem_univ _)

theorem not_atMostTwo_rangeSet [CharZero F] (hn : 2 ≤ n) : ¬ AtMostTwo (RangeSet F n) := by
  rintro ⟨a, b, hab⟩
  have h4 : (4 : ℕ) ≤ 2 ^ n := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h0 := hab (nat_mem_rangeSet (F := F) (k := 0) (by omega))
  have h1 := hab (nat_mem_rangeSet (F := F) (k := 1) (by omega))
  have h2 := hab (nat_mem_rangeSet (F := F) (k := 2) (by omega))
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h0 h1 h2
  have c01 : ((0 : ℕ) : F) ≠ ((1 : ℕ) : F) := by
    simp only [ne_eq, Nat.cast_inj]; omega
  have c02 : ((0 : ℕ) : F) ≠ ((2 : ℕ) : F) := by
    simp only [ne_eq, Nat.cast_inj]; omega
  have c12 : ((1 : ℕ) : F) ≠ ((2 : ℕ) : F) := by
    simp only [ne_eq, Nat.cast_inj]; omega
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
    first
      | exact c01 (h0.trans h1.symm)
      | exact c02 (h0.trans h2.symm)
      | exact c12 (h1.trans h2.symm)

theorem not_coAtMostOne_rangeSet [CharZero F] : ¬ CoAtMostOne (RangeSet F n) := by
  rintro ⟨a, ha⟩
  have hne : ((2 ^ n : ℕ) : F) ≠ ((2 ^ n + 1 : ℕ) : F) := by
    simp only [ne_eq, Nat.cast_inj]; omega
  rcases eq_or_ne ((2 ^ n : ℕ) : F) a with h | h
  · exact nat_notMem_rangeSet (F := F) (k := 2 ^ n + 1) (by omega)
      (ha _ (fun hc => hne ((hc.trans h.symm).symm)))
  · exact nat_notMem_rangeSet (F := F) (k := 2 ^ n) (by omega) (ha _ h)

/-! ## No cheap system certifies two bits -/

theorem no_rows_not_certifies [CharZero F] (S : System F m 0) : ¬ S.Certifies n := by
  intro hc
  have huniv : S.solutions = Set.univ := zero_rows_solutions S
  apply rangeSet_ne_univ (F := F) (n := n)
  rw [← huniv]
  ext x
  exact (hc x).symm

theorem one_row_not_certifies [IsAlgClosed F] [CharZero F] (S : System F m 1) (hn : 2 ≤ n) :
    ¬ S.Certifies n := by
  intro hc
  have hset : rowSolutions (S.row 0) = RangeSet F n := by
    ext x
    rw [← hc x]
    constructor
    · rintro ⟨w, hw⟩
      exact ⟨w, fun j => by simpa [Fin.fin_one_eq_zero j] using hw⟩
    · rintro ⟨w, hw⟩
      exact ⟨w, hw 0⟩
  rcases one_row_dichotomy (S.row 0) with h | h
  · exact not_atMostTwo_rangeSet (F := F) hn (hset ▸ h)
  · exact not_coAtMostOne_rangeSet (F := F) (n := n) (hset ▸ h)

theorem no_witness_not_certifies [CharZero F] (S : System F 0 r) (hn : 2 ≤ n) :
    ¬ S.Certifies n := by
  intro hc
  have hset : S.solutions = RangeSet F n := by ext x; exact hc x
  rcases zero_witness_dichotomy S with h | h
  · exact not_atMostTwo_rangeSet (F := F) hn (hset ▸ h)
  · exact rangeSet_ne_univ (F := F) (n := n) (hset ▸ h)

/-- Five distinct `n`-bit values, for `n ≥ 3`. -/
theorem five_le_card_rangeFinset [CharZero F] (hn : 3 ≤ n) :
    ∃ Z : Finset F, 5 ≤ Z.card ∧ ∀ x ∈ Z, x ∈ RangeSet F n := by
  classical
  refine ⟨(Finset.range 5).image (fun k : ℕ => (k : F)), ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]
  · intro x hx
    simp only [Finset.mem_image, Finset.mem_range] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    have h8 : (8 : ℕ) ≤ 2 ^ n := by
      calc (8 : ℕ) = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    exact nat_mem_rangeSet (by omega)

/-- **A single witness certifies at most two bits**, however many rows are used. -/
theorem one_witness_not_certifies [IsAlgClosed F] [CharZero F] (S : System F 1 r) (hn : 3 ≤ n) :
    ¬ S.Certifies n := by
  intro hc
  have hset : S.solutions = RangeSet F n := by ext x; exact hc x
  rcases one_witness_dichotomy S with h | h
  · obtain ⟨Z, hZcard, hZmem⟩ := five_le_card_rangeFinset (F := F) (n := n) hn
    exact (hset ▸ h).not_five Z hZmem hZcard
  · exact not_coAtMostOne_rangeSet (F := F) (n := n) (hset ▸ h)

/-! ## The score bound -/

/-- **No system of score `≤ 2` certifies a range of two or more bits.**
    The statement quantifies over *all* systems: any number of witnesses, arbitrary
    affine forms, no assumption that any witness is a bit. -/
theorem score_ge_three [IsAlgClosed F] [CharZero F] (S : System F m r) (hn : 2 ≤ n)
    (hc : S.Certifies n) : 3 ≤ S.score := by
  by_contra hlt
  rw [System.score_eq] at hlt
  push_neg at hlt
  have key : ∀ (r' : ℕ), ∀ (m' : ℕ), m' + r' < 3 → ∀ (T : System F m' r'), ¬ T.Certifies n := by
    intro r'
    match r' with
    | 0 => intro m' _ T hcT; exact no_rows_not_certifies T hcT
    | 1 => intro m' _ T hcT; exact one_row_not_certifies T hn hcT
    | 2 =>
      intro m' hm T hcT
      have hm0 : m' = 0 := by omega
      subst hm0
      exact no_witness_not_certifies T hn hcT
    | (k + 3) => intro m' hm T _; omega
  exact key r m hlt S hc

/-- **Certifying three or more bits needs at least two witness allocations**, however
    many rows are used. -/
theorem alloc_ge_two [IsAlgClosed F] [CharZero F] (S : System F m r) (hn : 3 ≤ n)
    (hc : S.Certifies n) : 2 ≤ m := by
  by_contra hlt
  push_neg at hlt
  have key : ∀ (m' : ℕ), m' < 2 → ∀ (T : System F m' r), ¬ T.Certifies n := by
    intro m'
    match m' with
    | 0 => intro _ T hcT; exact no_witness_not_certifies T (by omega) hcT
    | 1 => intro _ T hcT; exact one_witness_not_certifies T hn hcT
    | (k + 2) => intro hk T _; omega
  exact key m hlt S hc

/-- **No system of score `≤ 3` certifies a range of three or more bits.**  Again the
    statement quantifies over all systems.  Combined with the score-`(2 * n - 1)`
    construction this pins the optimum for `n = 3` to `4` or `5`. -/
theorem score_ge_four [IsAlgClosed F] [CharZero F] (S : System F m r) (hn : 3 ≤ n)
    (hc : S.Certifies n) : 4 ≤ S.score := by
  by_contra hlt
  rw [System.score_eq] at hlt
  push_neg at hlt
  have key : ∀ (m' : ℕ), ∀ (r' : ℕ), m' + r' < 4 → ∀ (T : System F m' r'), ¬ T.Certifies n := by
    intro m'
    match m' with
    | 0 => intro r' _ T hcT; exact no_witness_not_certifies T (by omega) hcT
    | 1 => intro r' _ T hcT; exact one_witness_not_certifies T hn hcT
    | 2 =>
      intro r' hr T hcT
      match r' with
      | 0 => exact no_rows_not_certifies T hcT
      | 1 => exact one_row_not_certifies T (by omega) hcT
      | (k + 2) => omega
    | 3 =>
      intro r' hr T hcT
      match r' with
      | 0 => exact no_rows_not_certifies T hcT
      | (k + 1) => omega
    | (k + 4) => intro r' hr T _; omega
  exact key m r hlt S hc

/-- **A structural constraint on *every* certifying system, for every `n ≥ 2`.**
    Each individual row of a system that certifies an `n`-bit range must, on its own, be
    satisfiable for all but at most one value of `x`.  (Otherwise that single row already
    cuts the accepted set down to at most two values, which cannot be the `n`-bit range.)
    In particular no row may be a constraint on `x` alone, and each row must involve a
    witness nontrivially. -/
theorem row_coAtMostOne_of_certifies [IsAlgClosed F] [CharZero F] (S : System F m r)
    (hn : 2 ≤ n) (hc : S.Certifies n) (j : Fin r) : CoAtMostOne (rowSolutions (S.row j)) := by
  rcases one_row_dichotomy (S.row j) with ⟨a, b, hab⟩ | h
  · exact absurd (⟨a, b, fun x hx => hab (by
      obtain ⟨w, hw⟩ := (hc x).2 hx
      exact ⟨w, hw j⟩)⟩ : AtMostTwo (RangeSet F n)) (not_atMostTwo_rangeSet hn)
  · exact h

/-- **The optimum at `n = 2` is exactly `3`.**  The set of achievable scores for a
    `2`-bit range check has least element `3 = 2 * 2 - 1 < 2 * 2`. -/
theorem least_score_two_bits [IsAlgClosed F] [CharZero F] :
    IsLeast {s : ℕ | ∃ (m r : ℕ) (S : System F m r), S.Certifies 2 ∧ S.score = s} 3 := by
  constructor
  · exact ⟨1, 2, rangeSystem F 1, rangeSystem_certifies 1, rfl⟩
  · rintro s ⟨m, r, S, hc, rfl⟩
    exact score_ge_three S le_rfl hc

end Solution.Research
