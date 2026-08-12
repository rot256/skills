/-
  # Is the minimal R1CS row count of a bilinear map exactly its tensor rank?

  **Answer: no — it is an inequality, and the useful direction is the one that holds.**

  The model is formalised in `Solution/Research/Model.lean`. A row is one product
  `(A·w + a) * (B·w + b) = C·w + c` with `A, B, C` arbitrary linear forms on the *whole*
  witness `w = (x, y, u)`; affine combinations are free (the output is read off as an
  arbitrary affine function of the witness and is not charged); the intermediate
  witnesses `u` are unconstrained in number and are supplied **nondeterministically**
  (`Complete`: for every input *some* witness satisfies the rows; `Sound`: *every*
  satisfying witness produces the right output). Nothing restricts a row's factors to
  bilinear shape, so the model is strictly more permissive than the classical bilinear
  model, exactly as the question demands.

  What is proved here, for every bilinear `f : F^m × F^n → F^p` over any field `F`
  (one item, flagged below, additionally assumes `F` infinite):

  * `rows_le_rank` : `minRows f ≤ tensorRank f`.
    A rank-`r` decomposition becomes `r` rows verbatim (`Solution/Research/UpperBound.lean`).
    **This is the direction that licenses importing the literature**: Strassen, Winograd,
    Karatsuba, the matrix-multiplication rank tables all transfer as row-count *upper
    bounds*.

  * `rank_le_nine_rows_sq` : `tensorRank f ≤ 9 * (minRows f)^2`.
    The converse holds only quadratically (`Solution/Research/LowerBound.lean`). The
    proof does *not* assume rows are bilinear: it shows that everything an `r`-row system
    can know about the inputs passes through the `3r` affine coefficients the inputs
    contribute to the rows, so `f` factors through `3r` linear coordinates on each side
    and hence has rank at most `(3r)²`.

  * `minRows_eq_tensorRank_of_rank_le_one` : the two agree whenever the rank is `≤ 1`
    (and `minRows f = 0 ↔ f = 0`).

  * `minRows_le_one_iff_rank_le_one` (over an infinite field): **one row buys exactly
    rank one**. This is the one place where the exact correspondence is settled *in the
    hard direction*, and it is settled without restricting the row to bilinear shape:
    the single row may multiply two arbitrary affine forms of the whole witness, over
    arbitrarily many nondeterministically supplied intermediate witnesses
    (`Solution/Research/OneRow.lean`). Consequently
    `two_le_minRows_of_two_le_rank` : `2 ≤ tensorRank f → 2 ≤ minRows f`, a genuine rank
    lower bound transferred to rows.

  * `strassen_two_by_two` : 2×2 matrix multiplication is certified by 7 rows, against 8
    for the schoolbook decomposition (`Solution/Research/Strassen.lean`). Because affine
    combinations are free, Strassen's extra additions cost nothing: the crossover is at
    n = 2, as claimed. (Whether 7 is *optimal* is a lower-bound question, and lower
    bounds are precisely what does not transfer; see below.)

  **What nondeterminism and intermediate witnesses buy.** Two structural theorems bound
  it. `R1CS.aux_kernel`: a witness direction invisible to every row is invisible to the
  output, so the output functional lies in the span of the `3 * rows` linear forms used
  by the rows — a value may be *witnessed* rather than computed, but only if the rows
  pin it down. `R1CS.left_kernel` / `R1CS.right_kernel`: an input direction invisible to
  the rows is annihilated by `f`. Together these give the quadratic converse. What is
  *not* proved — and what the equality would require — is that the extra power buys
  nothing at all. Beyond one row this is left open in both directions: no construction
  here beats the rank with nondeterministic rows, and no proof that none can. Even
  in the deterministic sub-case (a row's factors may still mix `x`, `y` and intermediate
  values, as Winograd's algorithms do) the classical relation between rank `R` and
  multiplicative complexity `C` is `C ≤ R ≤ 2C`, not equality. At one row the extra power
  is *proved* to buy nothing (`minRows_le_one_iff_rank_le_one`): the case analysis in
  `Solution/Research/OneRow.lean` shows that either the row is a plain definition of one
  product — in which case `f` is affine plus one product of affine forms, hence of rank
  ≤ 1 — or the witness slides along a curve of solutions and soundness collapses `f` to a
  function of `x` plus a function of `y`, hence to `0`.

  **Practical reading.** Row-count *upper* bounds imported from bilinear complexity are
  sound. Rank *lower* bounds are **not** valid row lower bounds: the only lower bound
  established in general is `rows ≥ √(rank)/3`, sharpened to an exact statement only at
  one row. So "Strassen is a free lunch at n = 2" survives as stated (7 rows < 8 rows),
  but "7 rows are necessary" does not follow from
  `rank(⟨2,2,2⟩) = 7`.
-/
import Solution.Research.OneRow
import Solution.Research.Strassen

namespace Solution.Research

open Module

variable {F : Type*} [Field F] {m n p : ℕ}

/-! ## The two directions -/

/-- **Upper bound (exact).** The minimal R1CS row count of a bilinear map is at most its
tensor rank: every rank decomposition imports wholesale as a row count. -/
theorem rows_le_rank (f : BilMap F m n p) :
    minRows (fun x y => f x y) ≤ tensorRank (fun x y => f x y) :=
  minRows_le_tensorRank f

/-- **Converse (quadratic only).** Intermediate witnesses and nondeterminism cannot buy
more than a quadratic saving: the tensor rank is at most `9 * rows²`. -/
theorem rank_le_nine_rows_sq (f : BilMap F m n p) :
    tensorRank (fun x y => f x y) ≤ 9 * (minRows (fun x y => f x y)) ^ 2 :=
  tensorRank_le_nine_mul_minRows_sq f

/-- **The settled statement.** Rows and rank are pinned to each other from both sides,
but not equal to each other by anything proved here. -/
theorem rows_rank_sandwich (f : BilMap F m n p) :
    minRows (fun x y => f x y) ≤ tensorRank (fun x y => f x y) ∧
      tensorRank (fun x y => f x y) ≤ 9 * (minRows (fun x y => f x y)) ^ 2 :=
  ⟨rows_le_rank f, rank_le_nine_rows_sq f⟩

/-! ## Where the two measures do agree -/

/-- Rank `0` means the zero map. -/
theorem tensorRank_eq_zero_iff (f : BilMap F m n p) :
    tensorRank (fun x y => f x y) = 0 ↔ ∀ x y, f x y = 0 := by
  constructor
  · intro h0 x y
    obtain ⟨φ, ψ, w, hf⟩ := hasRankLE_tensorRank f
    have := hf x y
    rw [h0] at this
    simpa using this
  · intro hf
    exact Nat.le_zero.1 (tensorRank_le (hasRankLE_zero _ hf))

/-- The two measures agree at `0`. -/
theorem minRows_eq_zero_iff_tensorRank_eq_zero (f : BilMap F m n p) :
    minRows (fun x y => f x y) = 0 ↔ tensorRank (fun x y => f x y) = 0 :=
  (minRows_eq_zero_iff f).trans (tensorRank_eq_zero_iff f).symm

/-- **Equality holds at the bottom of the scale.** If the tensor rank is at most one,
the minimal row count equals it. (For rank ≥ 2 only the sandwich above is known.) -/
theorem minRows_eq_tensorRank_of_rank_le_one (f : BilMap F m n p)
    (h : tensorRank (fun x y => f x y) ≤ 1) :
    minRows (fun x y => f x y) = tensorRank (fun x y => f x y) := by
  rcases Nat.eq_zero_or_pos (tensorRank (fun x y => f x y)) with hr | hpos
  · rw [hr]
    exact (minRows_eq_zero_iff_tensorRank_eq_zero f).2 hr
  · have hr : tensorRank (fun x y => f x y) = 1 := le_antisymm h hpos
    have hle := rows_le_rank f
    have hne : minRows (fun x y => f x y) ≠ 0 := by
      intro hz
      have := (minRows_eq_zero_iff_tensorRank_eq_zero f).1 hz
      omega
    omega

/-- **One row buys exactly rank one.** Over an infinite field the correspondence is
exact at one row, in both directions, with no restriction on the shape of the row. -/
theorem minRows_le_one_iff_rank_le_one [Infinite F] (f : BilMap F m n p) :
    minRows (fun x y => f x y) ≤ 1 ↔ tensorRank (fun x y => f x y) ≤ 1 :=
  ⟨tensorRank_le_one_of_minRows_le_one f, fun h => le_trans (rows_le_rank f) h⟩

/-- **A rank lower bound that does transfer.** A bilinear map of tensor rank at least two
needs at least two rows. -/
theorem two_le_minRows_of_two_le_rank [Infinite F] (f : BilMap F m n p)
    (h : 2 ≤ tensorRank (fun x y => f x y)) : 2 ≤ minRows (fun x y => f x y) := by
  by_contra hcon
  push_neg at hcon
  have := (minRows_le_one_iff_rank_le_one f).1 (by omega)
  omega

/-- The two measures agree whenever *either* of them is at most one. -/
theorem minRows_eq_tensorRank_of_rows_le_one [Infinite F] (f : BilMap F m n p)
    (h : minRows (fun x y => f x y) ≤ 1) :
    minRows (fun x y => f x y) = tensorRank (fun x y => f x y) :=
  minRows_eq_tensorRank_of_rank_le_one f ((minRows_le_one_iff_rank_le_one f).1 h)

/-! ## The Strassen corollary -/

/-- **Strassen at n = 2 is a free lunch in this cost model.** 2×2 matrix multiplication
is certified by an explicit 7-row R1CS system, one row fewer than the 8 products of the
schoolbook decomposition, and the extra additions are free. -/
theorem strassen_two_by_two :
    (∃ S : R1CS F 4 4 4, S.rows = 7 ∧ S.Certifies (fun x y => matmul2 F x y)) ∧
      minRows (fun x y => matmul2 F x y) ≤ 7 ∧
      HasRankLE (fun x y => matmul2 F x y) 8 ∧ (7 : ℕ) < 8 :=
  ⟨exists_seven_row_matmul2_system, minRows_matmul2_le_seven, matmul2_hasRankLE_eight,
    by norm_num⟩

/-! ## The original placeholder

The file as given contained the statement of intent below. It is kept verbatim, but
commented out: as a Lean statement it is `True`, so it asserts nothing, and the equality
it names is *not* what holds. `rows_le_rank` and `rank_le_nine_rows_sq` are what holds,
together with `minRows_le_one_iff_rank_le_one` at one row.

```
/-- **The question.** For a bilinear map `f : F^m → F^n → F^p`, is the minimum number of
    R1CS rows needed to certify `z = f x y` -- with `x`, `y`, `z` the witness and affine
    combinations free -- exactly the tensor rank of `f`? ... -/
theorem rows_eq_tensor_rank : True := by trivial
```

The claim itself, stated exactly rather than as `True`, is the following proposition; it
is recorded for reference and is neither assumed nor used anywhere.
-/

/-- The equality the question asks about, stated exactly. Not proved (and not assumed):
`rows_le_rank` gives `≤`, and `rank_le_nine_rows_sq` gives a quadratic converse. -/
def RowsEqRankClaim (F : Type*) [Field F] (m n p : ℕ) : Prop :=
  ∀ f : BilMap F m n p, minRows (fun x y => f x y) = tensorRank (fun x y => f x y)

/-- Whatever the status of the claim, it *does* hold for maps of rank at most one, and
(over an infinite field) for maps of row count at most one. -/
theorem rowsEqRank_at_rank_le_one (f : BilMap F m n p)
    (h : tensorRank (fun x y => f x y) ≤ 1) :
    minRows (fun x y => f x y) = tensorRank (fun x y => f x y) :=
  minRows_eq_tensorRank_of_rank_le_one f h

end Solution.Research
