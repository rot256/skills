# Summary of changes for run 1211bc6e-83bd-48df-822d-e6d9d574c382
## The question, settled

`Solution/Research/` now contains a complete, compiling formalisation of the R1CS-rows-vs-tensor-rank question. `lake build` succeeds with zero errors (I added `@[default_target]` to the `Solution` library so a bare `lake build` covers it), there are no `sorry`s, and `#print axioms` on every headline result gives exactly `[propext, Classical.choice, Quot.sound]`.

**Answer: it is an inequality, not an equality — and the useful direction is the one that holds.**

### The model (`Model.lean`)
`R1CS F m n p` charges one row per product `(A·w + a)*(B·w + b) = C·w + c`, where `A, B, C` are *arbitrary* linear forms on the whole witness `w = (x, y, u)` — nothing is restricted to bilinear shape, so a factor may mix inputs and intermediate witnesses freely. The output is an arbitrary affine function of the witness, charged nothing. The system is genuinely nondeterministic: `Complete` says *some* witness satisfies the rows for each input, `Sound` says *every* satisfying witness yields the right output. `minRows f` is the least row count of such a certificate; `tensorRank f` is the classical bilinear complexity.

### What is proved
- `rows_le_rank` : `minRows f ≤ tensorRank f`, over any field. A rank-`r` decomposition becomes `r` rows verbatim.
- `rank_le_nine_rows_sq` : `tensorRank f ≤ 9 · (minRows f)²`. The converse holds only quadratically. The proof does not assume rows are bilinear: everything an `r`-row system can know about the inputs passes through the `3r` affine coefficients the inputs contribute to the rows, so `f` factors through `3r` linear coordinates per side.
- `minRows_le_one_iff_rank_le_one` (infinite field): **one row buys exactly rank one**, and hence `two_le_minRows_of_two_le_rank` : rank ≥ 2 forces ≥ 2 rows. This is the hard direction, settled at one row with the row left completely unrestricted. The argument (`OneRow.lean`, ~530 lines) is a case analysis: either some witness direction is invisible to both factors but shifts the right-hand side — the row is then a plain definition of one product and `f` is affine plus one product of affine forms, which bilinearity collapses to rank ≤ 1 — or the witness slides along a hyperbola/line of solutions and soundness forces `f` to be a function of `x` plus a function of `y`, hence `0`.
- `minRows f = 0 ↔ f = 0`, and equality of the two measures whenever either is ≤ 1.

### What nondeterminism and intermediate witnesses buy
Bounded, never unbounded. `R1CS.aux_kernel`: a witness direction invisible to every row is invisible to the output, so a value may be *witnessed* rather than computed only if the rows pin it down. `R1CS.left_kernel`/`right_kernel`: an input direction invisible to the rows is annihilated by `f`. Together these give the quadratic converse. At one row the extra power is proved to buy *nothing*. Beyond one row it is left open in both directions: no construction here beats the rank with nondeterministic rows, and no proof that none can. (Even in the deterministic sub-case the classical relation is `C ≤ R ≤ 2C`, not equality.)

### The Strassen corollary — survives, as an upper bound
`strassen_two_by_two` packages an explicit 7-row R1CS certificate for 2×2 matrix multiplication against the schoolbook 8-product decomposition, with the extra additions free: the crossover is at n = 2. What does **not** follow is optimality — "7 rows are necessary" would need a rank lower bound to transfer, and rank lower bounds transfer only at one row.

### Practical reading
Row-count *upper* bounds imported from the bilinear-complexity literature are sound and can be cited directly. Rank *lower* bounds are not valid row lower bounds; the general lower bound available is `rows ≥ √(rank)/3`, sharpened to exact only at one row.

The original placeholder `theorem rows_eq_tensor_rank : True := by trivial` is preserved (commented, with an explanation that as Lean it asserts nothing and the equality it names is not what holds); the claim it intended is recorded exactly as the unused proposition `RowsEqRankClaim`.

Files: `Model.lean`, `RankCalculus.lean`, `UpperBound.lean`, `LowerBound.lean`, `AffineAlgebra.lean`, `OneRow.lean`, `Strassen.lean`, `BilinearRank.lean` (the top-level answer file). All work is committed and pushed.