/-
  Does a range check cost at least 2 score per bit?

  In this cost model score = allocations + constraints, each row is exactly one
  product (A·w)(B·w) = (C·w), and affine combinations are FREE. The standard
  n-bit range check witnesses n boolean bits and asserts n booleanity rows plus
  one free affine recomposition, costing ⟨n, n⟩ = 2n score.

  EVERY tree in this project pays that rate, and on RSA it is 81.4% of the entire
  circuit. Beating it, even by a constant factor, would be worth more than every
  structural technique found so far combined. Nobody has proved it is optimal.

  ---------------------------------------------------------------------------------
  ANSWER (see `ANSWER.md` in this directory for the full discussion).

  * `2 * n` is **not** optimal: `2 * n - 1` is achievable for every `n ≥ 1`, over every
    field, by *not* allocating the low bit — it is the free affine form
    `x - ∑_{i ≥ 1} 2 ^ i * b i`, and its booleanity is still a single row.
    (`Construction.rangeSystem_certifies`, `Construction.exists_system_score_lt_two_mul`.)

  * `2 * n - 1` cannot be improved at `n = 2`: over an algebraically closed field of
    characteristic zero the minimum score of *any* system certifying a two-bit range
    is exactly `3`.  (`Optimality.least_score_two_bits`.)  The lower bound quantifies
    over arbitrary systems — arbitrary affine forms, arbitrary field witnesses; nothing
    assumes the witnesses are bits.  Its two ingredients are of independent interest:
    one row can never certify more than one bit no matter how many witnesses it is
    given (`LowerBound.one_row_dichotomy`), and a system with no witnesses at all
    accepts at most two values of `x` or all of them
    (`LowerBound.zero_witness_dichotomy`).

  * For every `n ≥ 2` there is also a structural constraint on all certifying systems:
    each row on its own must be satisfiable for all but at most one `x`
    (`Optimality.row_coAtMostOne_of_certifies`).

  * For `n ≥ 3` the floor rises to `4`: a *single* witness can never certify more than
    two bits, however many rows it is given (`OneWitness.one_witness_dichotomy`,
    `Optimality.one_witness_not_certifies`), so every system certifying three or more
    bits allocates at least two witnesses (`Optimality.alloc_ge_two`) and scores at
    least `4` (`Optimality.score_ge_four`).

  * For `n ≥ 3` the exact optimum (`4` or `5 = 2 * 3 - 1`) is **open** here; `ANSWER.md`
    records the Bezout-style argument that gives `2 * n - 1` in general, says precisely
    which algebraic-geometry input is missing from the formalisation, and identifies the
    single remaining configuration — two witnesses and two rows — that would settle
    `n = 3`.
  ---------------------------------------------------------------------------------
-/
import Solution.Research.Model
import Solution.Research.Construction
import Solution.Research.LowerBound
import Solution.Research.Optimality
import Solution.Research.Conic

namespace Solution.Research

/-  The original sketch of the question.  Its `Row` is superseded by the model in
    `Solution/Research/Model.lean`, which spells the affine forms out as
    `cx * x + ∑ i, cw i * w i + c`; it is kept here, commented out, so that the
    starting point is still visible.  The placeholder `theorem range_check_floor : True`
    is replaced by the real statement below.

    structure Row (F : Type*) [Field F] (m : ℕ) where
      A : Fin (m + 1) → F
      B : Fin (m + 1) → F
      C : Fin (m + 1) → F

    theorem range_check_floor : True := by trivial
-/

variable {F : Type*} [Field F]

/-- **`2 * n` is not optimal.**  Over any field and for any `n ≥ 1` there is a system
    with `n - 1` witness allocations and `n` rows — score `2 * n - 1` — that is
    satisfiable at `x` exactly when `x` is the image of a natural number `< 2 ^ n`. -/
theorem range_check_below_two_n (n : ℕ) (hn : 1 ≤ n) :
    ∃ S : System F (n - 1) n, S.Certifies n ∧ S.score = 2 * n - 1 ∧ S.score < 2 * n :=
  exists_system_score_lt_two_mul n hn

/-- **The floor at two bits is exactly `3 = 2 * 2 - 1`.**  Over an algebraically closed
    field of characteristic zero, `3` is the least score of any system certifying the
    two-bit range: the improved construction is optimal, and no further constant-factor
    saving exists at `n = 2`. -/
theorem range_check_floor [IsAlgClosed F] [CharZero F] :
    IsLeast {s : ℕ | ∃ (m r : ℕ) (S : System F m r), S.Certifies 2 ∧ S.score = s} 3 :=
  least_score_two_bits

/-- **A single witness certifies at most two bits.**  No matter how many rows it is
    given, a system with one witness allocation cannot certify a range of three or more
    bits: its accepted set has at most four elements or misses at most one element of
    `F`, and the `n`-bit range is neither. -/
theorem range_check_one_witness_limit [IsAlgClosed F] [CharZero F] {r n : ℕ}
    (S : System F 1 r) (hn : 3 ≤ n) : ¬ S.Certifies n :=
  one_witness_not_certifies S hn

/-- **The floor for three or more bits is at least `4`.**  Every system certifying an
    `n`-bit range with `n ≥ 3` has score at least `4` — and at least two witness
    allocations (`alloc_ge_two`).  With the score-`(2 * n - 1)` construction this pins
    the optimum at `n = 3` to `4` or `5`. -/
theorem range_check_floor_three_bits [IsAlgClosed F] [CharZero F] {m r n : ℕ}
    (S : System F m r) (hn : 3 ≤ n) (hc : S.Certifies n) : 4 ≤ S.score :=
  score_ge_four S hn hc

/-- The same two statements over `ℂ`, as a concrete instance. -/
theorem range_check_floor_complex :
    (∀ n : ℕ, 1 ≤ n → ∃ S : System ℂ (n - 1) n, S.Certifies n ∧ S.score < 2 * n) ∧
      IsLeast {s : ℕ | ∃ (m r : ℕ) (S : System ℂ m r), S.Certifies 2 ∧ S.score = s} 3 :=
  ⟨fun n hn => by
    obtain ⟨S, hS, _, hlt⟩ := range_check_below_two_n (F := ℂ) n hn
    exact ⟨S, hS, hlt⟩, range_check_floor⟩

end Solution.Research
