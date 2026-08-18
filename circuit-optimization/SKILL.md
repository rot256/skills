---
name: circuit-optimization
description: Optimizing arithmetic circuits / constraint systems (R1CS, PLONKish, AIR) for zero-knowledge proofs -- minimizing multiplication constraints, rows, witnesses, and gate degree. Use when reducing constraint/witness counts, designing or golfing R1CS/PLONK/AIR gadgets (boolean ops, adders, range checks, hashes like SHA-256/Keccak/Poseidon), doing foreign-field/non-native or CRT/RNS arithmetic, choosing lookups vs arithmetic, or using SMT (cvc5) and SageMath (Groebner basis) to synthesize, verify, and certify constraint encodings.
---

# Circuit optimization

Reduce the cost of an arithmetic circuit / constraint system without breaking soundness.
A toolbox and a method, not a fixed playbook: `references/techniques.md` primes known moves but is deliberately incomplete -- the largest wins come from composing tricks or from structure specific to your circuit.
Arithmetization-specific moves live in their own reference, so far `references/r1cs.md` -- measured prices, and where each trick stops working.

## Know what is free

Every optimization moves work into what the proof system charges nothing for and minimizes what it charges for.

| System | Pays for | Free / cheap |
|--------|----------|--------------|
| **R1CS** (Groth16, Marlin, Spartan) | multiplication rows `(A*z)(B*z)=(C*z)` | linear combinations feeding a row, inlined wire definitions (a standalone asserted equality still costs a row) |
| **PLONKish** (halo2, plonky2/3, Kimchi) | rows x columns; FFT blowup proportional to max gate degree | additions within a gate, selectors on unused rows |
| **AIR / STARK** | trace width x length; constraint degree | -- |

State the scarce metric (mult-constraints? rows? witnesses? degree?) and get a baseline before optimizing.

## Workflow

1. Establish the cost metric before anything else.
   Ask the user which resource is scarce, or take it from its formal definition -- the scoring function, the cost model in the proof system's documentation, or the counter the toolchain actually reports.
   Witnesses and constraints are not interchangeable, and a metric that charges only rows reorders every trade-off in the references, so a change that looks like a win under a guessed metric can measure as a loss.
2. Measure the scarce resource; find the dominating hotspot.
3. Prime with `references/techniques.md` plus the reference for your arithmetization (`references/r1cs.md`), then look for structure the catalogue misses -- usually the bigger win.
4. Synthesize a candidate. Small boolean gadgets: search exactly with `scripts/synthesize.sage` (fix the multiplier `R`, solve a linear system over `QQ`).
5. Verify soundness before trusting it: `scripts/verify.smt2` (cvc5 `QF_FF`) proves the constraint forces the output over a real `F_p`; `scripts/impossible.smt2` proves a shape impossible when the search is empty.
6. Certify if needed: `scripts/cofactors.sage` extracts the cofactors proving the output is uniquely determined.
7. Re-measure; track the bounds each trick relies on (field size, carry width, characteristic).

## Tools

Two tools on PATH, no Python glue: **Sage** for algebra (search + certificates), **cvc5** for SMT (`QF_FF`, run directly on `.smt2`).

```bash
sage scripts/synthesize.sage     # single-constraint encoding of a 3-bit function (exact over QQ)
sage scripts/cofactors.sage      # XOR3/Maj soundness cofactors + excluded chars (Groebner)
cvc5 scripts/verify.smt2         # prove a row forces o = f, over a real F_p
cvc5 scripts/impossible.smt2     # prove AND3/OR3 have no single-constraint encoding of the shape
```

cvc5 `QF_FF` proves a statement about the *specific* prime in the file (exact, no side condition); Sage over `QQ` yields small prime-independent constants and a single "holds for all char > bound" result.
Use both. See `references/smt.md`, `references/sage.md`.

## Files

- `references/techniques.md` -- cross-arithmetization catalogue (carry-save, CRT/RNS, lookups, range-check/spread, custom gates, non-deterministic advice, solver methods, primitive notes).
- `references/r1cs.md` -- R1CS: what one row can do (single-row multipliers, lambda-packing, decoy roots, sqrt(N) law), not materialising values, free affine structure, bound arithmetic for non-native modmul, lower-bound tools, traps, the GF(2) cost model, and the baseline moves with their soundness side conditions. Measured prices throughout.
  PLONKish and AIR have no reference yet -- their material is still in the catalogue.
- `references/smt.md` -- cvc5 / SMT-LIB: verify, prove impossibility, model the field.
- `references/sage.md` -- SageMath: Groebner ideal-membership proofs, cofactor lifts, CRT/RNS bounds, computing hard-coded constants.
- `scripts/` -- `synthesize.sage`, `cofactors.sage`, `verify.smt2`, `impossible.smt2`. Self-checking.
