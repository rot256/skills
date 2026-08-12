You are answering ONE open question in Lean 4. There is no circuit to optimise and no score to beat.

## The question

In a cost model where score = allocations + constraints, each row is exactly one product
`(A·w)(B·w) = (C·w)` with A, B, C affine over the witness vector, and affine combinations
are FREE — **what does it cost to certify that a value is n bits wide?**

The standard construction witnesses n boolean bits and asserts n booleanity rows
`b_i * (b_i - 1) = 0`, with the recomposition `x = Σ 2^i b_i` free because it is affine.
That is `⟨n, n⟩ = 2n` score. Every tree in this project pays exactly that rate.

**Is 2n optimal? Prove it, or beat it.**

`Solution/Research/RangeFloor.lean` sketches a `Row` structure and states the question.
The formalisation is deliberately left to you — pinning down what "this system is
satisfiable exactly when x < 2^n" should mean is part of the work, and the sketch is a
suggestion rather than a constraint.

## Why this matters, so you can judge what counts as progress

On the RSA challenge, range checks are **81.4% of the entire circuit cost**. A constant-
factor improvement would be worth more than every structural optimisation found in this
project so far, combined. A proof of optimality is also valuable: it closes the largest
remaining question and redirects effort.

## What would count as a refutation

Any sound construction certifying `x < 2^n` in fewer than `2n` score. Ideas worth
testing before concluding it is impossible:
- amortisation across MANY simultaneous range checks (our circuits do hundreds; is the
  marginal cost of the k-th check lower than the first?)
- non-binary decompositions — base 4, base 2^k, or mixed radix — trading witness count
  against booleanity degree. Note a base-4 digit needs `d(d-1)(d-2)(d-3) = 0`, which is
  degree 4 and so needs 2 rows, but it certifies 2 bits: that is 1.5 score/bit if the
  digit witness is 1 allocation. **Check that carefully — if it works it is the answer.**
- certifying a SUM or other aggregate of many values rather than each individually
- exploiting that our values are already constrained by other rows

## Hard requirements

- `lake build` compiles with ZERO errors.
- `#print axioms` on your main result is a subset of `propext`, `Quot.sound`,
  `Classical.choice`. No `sorryAx`, no new `axiom`, no `native_decide` / `bv_decide`.
- If you prove a bound, state precisely what it quantifies over — a bound that assumes
  the bits are witnessed individually assumes the conclusion and is worth nothing.
- If you cannot settle it, say exactly where the argument breaks and what you ruled out.
  A well-delimited partial result is a good outcome; a vague one is not.

## Deliverable

The complete `Solution/Research/` directory, compiling. In your summary: the exact
statement you proved or refuted, whether 2n survives, and — if you found a construction
below 2n — its score, its soundness argument, and the smallest n at which it wins.
