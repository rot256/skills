You are proving a small, self-contained Lean 4 lemma and its converse. No circuit, no score.

## The task

`Solution/Research/Switch.lean` states:

```lean
theorem switch_pins_multiset (a b o : F) (h : (o - a) * (o - b) = 0) :
    (o = a ∧ a + b - o = b) ∨ (o = b ∧ a + b - o = a)
```

Prove it, then state and prove the CONVERSE (completeness): for either choice of
`o ∈ {a, b}` the row `(o - a) * (o - b) = 0` holds and `a + b - o` is the other element.

This should be short. It is stated because it is load-bearing, not because it is hard.

## Why it is load-bearing

It is the soundness core of a one-row 2x2 switch. The usual encoding uses a boolean
selector — `out1 = a + s*(b-a)`, `out2 = a + b - out1`, `s*(s-1) = 0` — at 2 rows and
2 witnesses. This encoding witnesses only `out1`, spends ONE row, and gets `out2` free
because `a + b - out1` is affine and affine combinations cost nothing in our model.

Composed with a Waksman network (`n·log₂n - n + 1` switches, realising every permutation
in `S_n`) that gives a permutation / multiset-equality certificate at
`2(n·log₂n - n + 1)` score with **no random challenge**. That last part is why we care:
our soundness obligation is an unconditional `∀ env, constraints_hold env → spec env`,
so the usual grand-product permutation argument — which needs a verifier challenge — is
unavailable to us at any price.

## Worth doing if the main lemma goes quickly

State and prove the n-element version: that a network of such switches, with the
outputs of one feeding the inputs of the next, yields a multiset equal to the input
multiset. `Multiset` in Mathlib is the right vehicle. This is the statement a circuit
would actually consume, and having it proved generically is worth more than the 2-element
case alone.

## Hard requirements

- `lake build` compiles with ZERO errors.
- `#print axioms` on each result is a subset of `propext`, `Quot.sound`,
  `Classical.choice`. No `sorryAx`, no new `axiom`, no `native_decide` / `bv_decide`.
- Do not weaken the statement. If you think it is false, give the counterexample and stop
  — note `F` is a field, so it has no zero divisors, which is what the proof turns on.

## Deliverable

The complete `Solution/Research/` directory, compiling. In your summary: the statements
you proved, whether you got the n-element multiset version, and the printed axiom list.
