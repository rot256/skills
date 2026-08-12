You are settling ONE foundational question in Lean 4. There is no circuit to write and no score to beat.

## The question

Our cost model charges one row per PRODUCT and makes all affine combinations FREE. That
is exactly the classical model of BILINEAR COMPLEXITY: linear operations free, count the
multiplications.

**Is the minimal R1CS row count of a bilinear map exactly its tensor rank?**

`Solution/Research/BilinearRank.lean` states it. Prove both directions, or identify
precisely where the correspondence fails and in which direction.

## Why the answer changes what we do

If exact, the whole bilinear-complexity literature becomes directly citable as ROW COUNTS
rather than as a loose analogy — Strassen, Winograd, Alder–Strassen, the
matrix-multiplication tensor-rank tables — and their constructions import wholesale. A
concrete consequence already claimed in this project and worth checking as a corollary:
**Strassen would be a free lunch here with crossover at n = 2 rather than the n ≈ 100 of
the machine-arithmetic setting**, because we do not pay for the additions.

If it is only an inequality, we need to know which way and by how much before trusting
any imported count.

## Where the difficulty is

The upper bound should be easy: a rank-r decomposition
`f(x,y) = Σ_{k<r} c_k · (u_k ⬝ x) * (v_k ⬝ y)` gives r rows immediately, since each
factor is affine and hence free, as is the recombination.

The lower bound is the real content, and there are two ways R1CS is STRONGER than the
classical bilinear model — both must be handled or the theorem is false as stated:

1. **Intermediate witnesses.** A row's factors may reference witnesses pinned by earlier
   rows, so products need not be `(affine in x) * (affine in y)`. Classical bilinear
   complexity forbids this.
2. **Nondeterminism.** The prover supplies witness values; we only check relations. A
   value may be witnessed and verified rather than computed.

Decide whether that extra power strictly helps. If it does, the honest theorem is an
inequality, and the interesting question becomes how large the gap can be.

## Hard requirements

- `lake build` compiles with ZERO errors.
- `#print axioms` on your main result is a subset of `propext`, `Quot.sound`,
  `Classical.choice`. No `sorryAx`, no new `axiom`, no `native_decide` / `bv_decide`.
- Formalise the model yourself; the sketch in the file is a suggestion. Getting the
  definitions right IS the task, and a theorem about the wrong model is worth nothing.
- Do not assume the conclusion. A "lower bound" that restricts rows to bilinear form has
  assumed exactly what is in question.

## Deliverable

The complete `Solution/Research/` directory, compiling. In your summary: the exact
statement you settled, whether it is an equality or an inequality, what nondeterminism
and intermediate witnesses buy, and whether the Strassen corollary survives.
