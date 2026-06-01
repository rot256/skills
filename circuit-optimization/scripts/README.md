# scripts

Self-checking helpers for the constraint-golfing loop, cross-checked against the
SHA-256 gadgets in `~/src/clean`. Two tools, no Python glue: **Sage** for the algebra
(search + certificates) and **cvc5** for SMT (`QF_FF`, finite-field theory, invoked
directly on `.smt2` files).

| file | does | run with |
|------|------|----------|
| `synthesize.sage` | **find** a single rank-1 constraint `(o+A)·R=O` for a boolean function, by fixing `R` and solving an exact linear system over `QQ`; re-verifies every hit | `sage` |
| `cofactors.sage` | **certify** (Gröbner) the output is uniquely determined and extract `linear_combination`/`ring` cofactors for a proof assistant; reports the excluded characteristics | `sage` |
| `verify.smt2` | **prove** a candidate row forces `o=f` and is non-vacuous, over a real `F_p` (`QF_FF`) | `cvc5` |
| `impossible.smt2` | **prove** no single constraint of the shape `(o+A)·R=O` computes a target, over a real `F_p` (`QF_FF`) | `cvc5` |

```bash
sage synthesize.sage      # scans an integer grid; prints a gadget per 3-bit function
sage cofactors.sage       # reproduces CarrySave.lean cofactors + excluded chars
cvc5 verify.smt2          # XOR3/Maj: forces o=f (unsat) + non-vacuous (sat)
cvc5 impossible.smt2      # AND3/OR3: no encoding of the shape (unsat)
```

**Two complementary guarantees.** cvc5 `QF_FF` proves a statement about the *specific*
prime in the `.smt2` file (swap it for your circuit's field) — exact, no "unit over the
reals" side condition. Sage over `QQ` (`synthesize.sage`, `cofactors.sage`) yields
small, prime-independent constants — integers or small-denominator fractions — and a
single "holds for all fields of char > bound" result, which is the form the `clean`
Lean proofs consume. Use both: Sage to find/certify nice constants for all large fields,
cvc5 to nail down a particular field exactly.

Load the search as a library:

```text
sage: load("synthesize.sage")
sage: find(3, [0,1,1,0,1,0,0,1])   # parity -> coefficient dict over QQ, or None within grid
```
