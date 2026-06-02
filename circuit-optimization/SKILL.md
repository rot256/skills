---
name: circuit-optimization
description: Optimizing arithmetic circuits / constraint systems (R1CS, PLONKish, AIR) for zero-knowledge proofs — minimizing multiplication constraints, rows, witnesses, and gate degree. Use when reducing constraint/witness counts, designing or golfing R1CS/PLONK/AIR gadgets (boolean ops, adders, range checks, hashes like SHA-256/Keccak/Poseidon), doing foreign-field/non-native or CRT/RNS arithmetic, choosing lookups vs arithmetic, or using SMT (cvc5) and SageMath (Gröbner basis) to synthesize, verify, and certify constraint encodings.
---

# Circuit optimization

Reduce the cost of an arithmetic circuit / constraint system without breaking soundness.
A toolbox and a method, not a fixed playbook: `references/techniques.md` primes known
moves but is deliberately incomplete — the largest wins come from composing tricks or
from structure specific to your circuit.

## Know what is free

Every optimization moves work into what the proof system charges nothing for and
minimizes what it charges for.

| System | Pays for | Free / cheap |
|--------|----------|--------------|
| **R1CS** (Groth16, Marlin, Spartan) | multiplication rows `(A·z)(B·z)=(C·z)` | linear combinations feeding a row, inlined wire definitions (a standalone asserted equality still costs a row) |
| **PLONKish** (halo2, plonky2/3, Kimchi) | rows × columns; FFT blowup ∝ max gate degree | additions within a gate, selectors on unused rows |
| **AIR / STARK** | trace width × length; constraint degree | — |

State the scarce metric (mult-constraints? rows? witnesses? degree?) and get a baseline
before optimizing.

## Workflow

1. Measure the scarce resource; find the dominating hotspot.
2. Prime with `references/techniques.md`, then look for structure the catalogue misses —
   usually the bigger win.
3. Synthesize a candidate. Small boolean gadgets: search exactly with
   `scripts/synthesize.sage` (fix the multiplier `R`, solve a linear system over `QQ`).
4. Verify soundness before trusting it: `scripts/verify.smt2` (cvc5 `QF_FF`) proves the
   constraint forces the output over a real `F_p`; `scripts/impossible.smt2` proves a
   shape impossible when the search is empty.
5. Certify for a proof assistant if needed: `scripts/cofactors.sage` extracts the
   cofactors proving the output is uniquely determined.
6. Re-measure; track the bounds each trick relies on (field size, carry width,
   characteristic).

## Tools

Two tools on PATH, no Python glue: **Sage** for algebra (search + certificates), **cvc5**
for SMT (`QF_FF`, run directly on `.smt2`).

```bash
sage scripts/synthesize.sage     # single-constraint encoding of a 3-bit function (exact over QQ)
sage scripts/cofactors.sage      # XOR3/Maj soundness cofactors + excluded chars (Gröbner)
cvc5 scripts/verify.smt2         # prove a row forces o = f, over a real F_p
cvc5 scripts/impossible.smt2     # prove AND3/OR3 have no single-constraint encoding of the shape
```

cvc5 `QF_FF` proves a statement about the *specific* prime in the file (exact, no side
condition); Sage over `QQ` yields small prime-independent constants and a single "holds
for all char > bound" result (the form Lean proofs consume). Use both. See
`references/smt.md`, `references/sage.md`.

## Files

- `references/techniques.md` — the catalogue (free linear combos, multi-operand add,
  carry-save, single-constraint boolean gadgets, CRT/RNS, lookups, range-check/spread,
  custom gates, non-deterministic advice, solver methods, primitive notes).
- `references/smt.md` — cvc5 / SMT-LIB: verify, prove impossibility, model the field.
- `references/sage.md` — SageMath: Gröbner ideal-membership proofs, cofactor lifts,
  CRT/RNS bounds, computing hard-coded constants.
- `scripts/` — `synthesize.sage`, `cofactors.sage`, `verify.smt2`, `impossible.smt2`.
  Self-checking, cross-checked against the verified SHA-256 gadgets in `~/src/clean`.

## Lean / Clean

Circuits proven in Lean (e.g. Clean, `~/src/clean`): unless explicitly asked, never change the spec to make a proof pass, and never leave `sorry` — leave the proof unfinished and say what is missing.
