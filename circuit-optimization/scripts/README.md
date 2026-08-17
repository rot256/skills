# scripts

Self-checking helpers for the constraint-golfing loop.
Two tools, no Python glue: **Sage** for the algebra (search + certificates) and **cvc5** for SMT (`QF_FF`, finite-field theory, invoked directly on `.smt2` files).

| file | does | run with |
|------|------|----------|
| `synthesize.sage` | **find** a single rank-1 constraint `(o+A)*R=O` for a boolean function, by fixing `R` and solving an exact linear system over `QQ`; re-verifies every hit | `sage` |
| `cofactors.sage` | **certify** (Groebner) the output is uniquely determined and extract the cofactors; reports the excluded characteristics | `sage` |
| `verify.smt2` | **prove** a candidate row forces `o=f` and is non-vacuous, over a real `F_p` (`QF_FF`) | `cvc5` |
| `impossible.smt2` | **prove** no single constraint of the shape `(o+A)*R=O` computes a target, over a real `F_p` (`QF_FF`) | `cvc5` |

```bash
sage synthesize.sage      # scans an integer grid; prints a gadget per 3-bit function
sage cofactors.sage       # prints the cofactors + excluded chars
cvc5 verify.smt2          # XOR3/Maj: forces o=f (unsat) + non-vacuous (sat)
cvc5 impossible.smt2      # AND3/OR3: no encoding of the shape (unsat)
```

cvc5 `QF_FF` proves a statement about the *specific* prime in the `.smt2` file (swap it for your circuit's field) -- exact, no "unit over the reals" side condition.
Sage over `QQ` yields small, prime-independent constants and a single "holds for all char > bound" result.
Use both.

Load the search as a library:

```text
sage: load("synthesize.sage")
sage: find(3, [0,1,1,0,1,0,0,1])   # parity -> coefficient dict over QQ, or None within grid
```
