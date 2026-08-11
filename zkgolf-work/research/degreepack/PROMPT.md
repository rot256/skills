You are settling TWO foundational questions in Lean 4. No circuit, no score.

## The questions

Reduce a boolean function to its MULTILINEAR polynomial over the cube (unique, since
`x^2 = x`). Two independent lines of work in this project agree on the following, both
confirmed by exhaustive search over small multipliers, but NEITHER IS PROVED:

1. **Multilinear degree 3 never packs.** For `f, g` non-affine on `{0,1}^3` with disjoint
   input triples, no single R1CS row determines `z = f(a) + λ·g(b)` for any `λ ≠ 0` —
   including when `z` appears quadratically via a decoy root.
2. **Multilinear degree 2 packs exactly 2.** Two instances share a row; three never do.

`Solution/Research/DegreePack.lean` states both. Prove them, or refute either.

## Why this is worth a slot

These bound a whole search space rather than one gadget. Degree-3 gadgets (Maj, XOR3,
AND3) are the dominant per-bit cost in SHA-256 and Keccak, so people keep looking for a
way to pack them; an exhaustive search over multipliers with coefficients in [-3,3] came
back empty, and a separate 759,375-candidate search for Maj came back empty. **Proving it
closes that search permanently.** Refuting it would be one of the largest results
available in this project.

## The sketched arguments — verify or replace them

Degree 3: apply the projector onto the bi-non-affine part. Since `f² = f` and `g² = g` on
the cube, `z²` contributes a nonzero `2λ · f̃ ⊗ g̃` term, while `z·A` (A affine) is
annihilated by the projector, as are `R₀` and any product `P₀Q₀` of affine forms. Hence
`λ = 0`.

Degree 2: the C-slot shape `γz = P₀Q₀ − R₀` forces the quadratic part of the packed
target to have rank ≤ 2 modulo the free diagonal shifts `αᵢ(xᵢ² − xᵢ)`, which vanish on
the cube. For k gadgets on disjoint variables the form is a direct sum of k blocks of rank
≥ 1, so k ≤ 2.

**Both sketches may be wrong or incomplete — they are hand arguments, not proofs.** In
particular the degree-2 case has a known subtlety: for gadgets SHARING variables the
rank-≤2 condition is a system of vanishing 3×3 minors, and two consecutive `Ch` instances
DO admit a rank-≤2 shift while three do not. Handle shared variables, or state clearly
that your theorem covers only the disjoint case.

## Hard requirements

- `lake build` compiles with ZERO errors.
- `#print axioms` on each result is a subset of `propext`, `Quot.sound`,
  `Classical.choice`. No `sorryAx`, no new `axiom`, no `native_decide` / `bv_decide`.
- Formalise "a single R1CS row determines z" yourself and state it explicitly. The decoy
  root case is not optional — it is where a naive proof goes wrong.
- Partial results are welcome if delimited. "Proved for disjoint inputs, open for shared"
  is a good outcome; an unqualified claim that silently assumes disjointness is not.

## Deliverable

The complete `Solution/Research/` directory, compiling. In your summary: which statements
you proved, whether shared variables are covered, whether the decoy-root case is handled,
and the printed axiom lists.
