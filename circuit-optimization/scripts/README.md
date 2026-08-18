# Scripts

Self-checking terminal tools for the constraint-golfing loop.
Sage handles algebra and GF(2) synthesis, cvc5 handles SMT, and plain Python defines the shared XAG format.

| file | does | run with |
|------|------|----------|
| `synthesize.sage` | **find** a single rank-1 constraint `(o+A)*R=O` for a boolean function, by fixing `R` and solving an exact linear system over `QQ`; re-verifies every hit | `sage` |
| `cofactors.sage` | **certify** (Groebner) the output is uniquely determined and extract the cofactors; reports the excluded characteristics | `sage` |
| `exact_xag.sage` | search small multi-output GF(2) XAGs by increasing AND count; full or CEGAR constraints, care masks, optional XOR tie-break | `sage` |
| `regular_reduce.sage` | reduce one Boolean output by its full translation-invariance subspace and minimal on-set affine hull; optionally synthesize and lift the reduced XAG | `sage` |
| `quadratic_and_count.sage` | factor one quadratic Boolean function through `rank(B_f)/2` products and emit the XAG | `sage` |
| `xag.py` | validate, evaluate, serialize, and measure the shared version-1 XAG JSON format | Python or Sage |
| `paar_optimize.sage` | heuristically factor one or more Boolean ANFs into a shared XAG; optional seeded affine-input trials | `sage` |
| `xag_rewrite.sage` | rewrite bounded fanout-safe cuts of at most six leaves, prune dangling ANDs, and prove a whole-network miter | `sage` |
| `verify.smt2` | **prove** a candidate row forces `o=f` and is non-vacuous, over a real `F_p` (`QF_FF`) | `cvc5` |
| `impossible.smt2` | **prove** no single constraint of the shape `(o+A)*R=O` computes a target, over a real `F_p` (`QF_FF`) | `cvc5` |

```bash
sage scripts/synthesize.sage      # scans an integer grid; prints a gadget per 3-bit function
sage scripts/cofactors.sage       # prints the cofactors and excluded characteristics
cvc5 scripts/verify.smt2          # XOR3/Maj: forces o=f (unsat) and is non-vacuous (sat)
cvc5 scripts/impossible.smt2      # AND3/OR3: no encoding of the shape (unsat)
sage scripts/exact_xag.sage       # deterministic exact-synthesis self-tests
sage scripts/regular_reduce.sage  # deterministic regularity-reduction self-tests
sage scripts/quadratic_and_count.sage  # deterministic polar-rank self-tests
sage scripts/paar_optimize.sage   # deterministic heuristic-synthesis self-tests
sage scripts/xag_rewrite.sage     # deterministic cut/splicing/miter self-tests
```

cvc5 `QF_FF` proves a statement about the *specific* prime in the `.smt2` file (swap it for your circuit's field) -- exact, no "unit over the reals" side condition.
Sage over `QQ` yields small, prime-independent constants and a single "holds for all char > bound" result.
Use both.

Load the search as a library:

```text
sage: load("scripts/synthesize.sage")
sage: find(3, [0,1,1,0,1,0,0,1])   # parity -> coefficient dict over QQ, or None within grid
```

## GF(2) XAG Synthesis

`regular_reduce.sage`, `exact_xag.sage`, `quadratic_and_count.sage`, and `xag.py` use only the GF(2) XAG model: an AND of affine forms costs one while XOR, NOT, and affine fan-in cost zero.
They do not price prime-field R1CS, AIR/STARK, or PLONKish circuits.

Exact synthesis accepts one or more truth tables and one care mask per output.
Table index `i` means `x[j] = (i >> j) & 1`, and a zero care bit leaves only that output/point unspecified.
Budgets are searched in increasing AND count; `--optimize-xor` adds an informational lexicographic tie-break and requires `--mode full`.

```bash
# x0 AND x1: scan through one AND and emit a version-1 XAG
DOT_SAGE=/private/tmp/sage-xag sage scripts/exact_xag.sage \
  --num-inputs 2 --output 0001 --max-ands 1

# Factor x0*x1 + x2*x3 into the two products emitted by polar elimination
DOT_SAGE=/private/tmp/sage-xag sage scripts/quadratic_and_count.sage \
  --table 0001000100011110
```

The programmatic exact-synthesis entry points are:

```python
load("scripts/exact_xag.sage")
xag = search_minimum(2, [[0, 0, 0, 1]], max_ands=1, mode="full")
xag = synthesize(2, [[0, 0, 0, 1]], and_count=1)
```

`outputs` and `care_masks` are lists of length-`2^n` bit sequences, while outputs may also be Sage `BooleanFunction` objects.
Every returned result is exhaustively checked on cared points.
`mode="cegar"` starts with one assignment and adds counterexamples until the decoded graph verifies.

The shared JSON schema is deliberately small:

```json
{
  "format": "xag",
  "version": 1,
  "num_inputs": 2,
  "gates": [{
    "left":  {"constant": 0, "terms": [0]},
    "right": {"constant": 0, "terms": [1]}
  }],
  "outputs": [{"constant": 0, "terms": [2]}],
  "metrics": {"and_count": 1, "and_depth": 1, "xor_count": 0}
}
```

Signals `0 .. num_inputs-1` are inputs and signal `num_inputs+i` is gate `i`.
Gate affine forms may reference only earlier signals.
`xag.py` normalizes terms, rejects forward references, recomputes metrics, and exposes construction, serialization, evaluation, and truth-table helpers.

The exact encoder uses Sage `BooleanPolynomialRing` and `CNFEncoder`, then the installed open-source `pycosat` solver.
Keep exact synthesis near six inputs and decompose or rewrite larger functions.

## Regularity Reduction

`regular_reduce.sage` accepts exactly one fully specified output and emits a versioned JSON reduction report.
It does not extend the paper's scalar results to multi-output functions.
The autosymmetry pass enumerates the full subspace `V = {a : f(x) = f(x+a)}`, emits affine quotient forms and the quotient truth table, and verifies the lifted identity at every input.
The D-reduction pass computes the affine hull of a nonempty on-set, emits a `max(codimension-1, 0)` product tree for its canonical affine membership factors, emits the projection truth table, and verifies `f = chi_A * f_A` exhaustively.
Constant zero is reported separately because its empty on-set has no unique nonempty associated affine hull.

```bash
# Analyze a three-input function whose on-set is {000, 101, 110}.
sage scripts/regular_reduce.sage --table 10000110

# Exactly synthesize locally and emit a verified lifted version-1 XAG.
sage scripts/regular_reduce.sage --table 10000110 \
  --exact-local --max-local-ands 1
```

The exact local target is the autosymmetry quotient of the affine-hull projection and is capped at six inputs.
When synthesis succeeds, the report gives the constructive upper bound `codimension(A) + local AND count` and the actual lifted XAG count after constant folding.
The local search scans its requested budget in increasing order, and the complete lifted XAG is compared by its measured AND count.

## Heuristic Synthesis and Bounded Rewriting

`paar_optimize.sage` greedily factors frequent ANF variable pairs across all outputs and may try seeded invertible affine input transforms.
It verifies complete truth tables and labels results as heuristic.

`xag_rewrite.sage` resynthesizes bounded fanout-safe cuts, prunes dangling gates, and accepts only a strict whole-network cost improvement.
The default tuple is `(and_count, and_depth)`, so XOR count is ignored.
It checks local truth tables exhaustively and proves the whole-network miter with cvc5, falling back to enumeration only for small networks.

```bash
sage scripts/paar_optimize.sage --num-inputs 3 --truth-table 00010111 \
  --seed 19 --affine-trials 8 --output majority.json
sage scripts/xag_rewrite.sage input.json output.json --max-cut 6 \
  --max-window-ands 6 --cost-profile and-depth
```

The JSON `xor_count` is a direct-affine proxy and does not model global linear-circuit sharing.
XOR-aware options apply only after AND count, and after depth in rewriting.
The rewriter is conservative rather than complete: it expands only non-root gates without external fanout and caps cuts per root.
