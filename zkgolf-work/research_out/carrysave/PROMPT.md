You are proving ONE mathematical lemma in Lean 4. This is not a circuit optimization task and there is no score to beat.

## The task

`Solution/CarrySave/Basic.lean` states two theorems and leaves the first as `sorry`.
Prove it. The second follows from the first by instantiation and is already written.

```lean
def maj (x y z : ℕ) : ℕ := (x &&& y) ||| (z &&& (x ^^^ y))

theorem add_eq_xor_add_two_mul_maj (n : ℕ) (x y z : ℕ)
    (hx : x < 2 ^ n) (hy : y < 2 ^ n) (hz : z < 2 ^ n) :
    x + y + z = (x ^^^ y ^^^ z) + 2 * maj x y z
```

This is the bitwise-parallel 3:2 carry-save adder identity: the sum of three naturals
equals their bitwise XOR plus twice their bitwise majority. It is exact over ℕ — there
is no modular reduction anywhere in the statement.

## What is known

It has been verified numerically on 10^5 random inputs for each of SHA-256's four
diffusion functions (Σ0, Σ1, σ0, σ1) at n = 32. It is almost certainly true. It is
not proved, and that is the whole of what is wanted here.

## Route suggestions, in the order I would try them

1. **Bitwise induction.** `Nat.binaryRec`, or induction on `n` peeling the low bit with
   `Nat.div2` / `Nat.mod_two_eq_zero_or_one`, reducing to the eight cases of the
   single-bit full adder. Mathlib's `Nat.testBit` extensionality (`Nat.eq_of_testBit_eq`)
   does NOT apply directly because the two sides are sums, not bitwise expressions —
   but `Nat.testBit_add` style lemmas plus a carry invariant may.
2. **Via `BitVec`.** If `BitVec 32` has better Mathlib support for this shape, prove it
   there and transfer. Note the statement is exact over ℕ, so a `BitVec` proof must
   handle the carry out of the top bit rather than wrapping — state the `BitVec` version
   carefully or it will be a different (false) theorem.
3. **Split into the two standard halves**, which may each be easier than the whole:
   `x + y = (x ^^^ y) + 2 * (x &&& y)` first, then fold in `z`.

## Hard requirements

- `lake build` must compile with ZERO errors.
- `#print axioms Solution.CarrySave.add_eq_xor_add_two_mul_maj` must print a subset of
  `propext`, `Quot.sound`, `Classical.choice`. **No `sorryAx`, no new `axiom`, and no
  `native_decide` / `decide +native` / `bv_decide`** — those admit results by an extra
  axiom and are not acceptable.
- Do not change the STATEMENT of the theorem or the definition of `maj`. If you believe
  the statement as written is false, do not patch it — say so, give the counterexample,
  and stop.

## If the bound turns out to be unnecessary

The `2 ^ n` hypotheses are supplied because the intended use is n = 32. If your proof
does not need them, prove the unbounded version instead, keep the bounded one as a
corollary so the second theorem still typechecks, and say clearly in your summary that
the bound was not needed.

## Deliverable

The complete `Solution/CarrySave/` directory, compiling, with the `sorry` gone. In your
summary state: which route worked, whether the bound was needed, and the axiom list you
actually printed.
