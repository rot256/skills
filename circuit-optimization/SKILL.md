---
name: circuit-optimization
description: Optimizing arithmetic circuits / constraint systems (R1CS, PLONKish, AIR) for zero-knowledge proofs -- minimizing multiplication constraints, rows, witnesses, trace cells, interactions, and gate degree. Use when reducing constraint/witness/column counts, designing or golfing R1CS/PLONK/AIR gadgets (boolean ops, adders, range checks, hashes like SHA-256/Keccak/Poseidon), designing AIR chips, buses, lookups or memory arguments, deciding whether to add a custom gate / sub-AIR / precompile and pricing its selector, budgeting constraint degree, doing foreign-field/non-native or CRT/RNS arithmetic, choosing lookups vs arithmetic, or using SMT (cvc5) and SageMath (Groebner basis) to synthesize, verify, and certify constraint encodings.
---

# Circuit optimization

Reduce the cost of an arithmetic circuit / constraint system without breaking soundness.
A toolbox and a method, not a fixed playbook: `references/techniques.md` primes known moves but is deliberately incomplete -- the largest wins come from composing tricks or from structure specific to your circuit.
Arithmetization-specific moves live in their own reference: `references/r1cs.md`, `references/air.md` and `references/plonkish.md`.
Two resources are priced separately because they are *global* rather than local: constraint degree (`references/degree.md`),
which is almost always under-spent, and a bespoke relation added to the system itself -- a custom gate, a sub-AIR, a
precompile -- which is charged once against every circuit whether it is used or not (`references/gates.md`).

## Know what is free

Every optimization moves work into what the proof system charges nothing for and minimizes what it charges for.

| System | Pays for | Free / cheap |
|--------|----------|--------------|
| **R1CS** (Groth16, Marlin, Spartan) | multiplication rows `(A*z)(B*z)=(C*z)` | linear combinations feeding a row, inlined wire definitions (a standalone asserted equality still costs a row) |
| **AIR / STARK** | `(preprocessed + main + permutation width) x padded height`; interactions; max constraint degree | constraints themselves, periodic/preprocessed columns, `is_transition` gating, anything affine in committed columns, values read from the next row |
| **PLONKish** | rows x columns; gate degree; copy constraints and their permutation columns; selector groups | additions within a gate, rotations within a region, selectors on unused rows, unrouted advice wires |

State the scarce metric (mult-constraints? trace cells? interactions? degree?) and get a baseline before optimizing.
The two most common ways to waste a week: optimizing width while padding eats the win, and reducing a degree that was not the global maximum.

## Workflow

1. Establish the cost metric before anything else.
   Ask the user which resource is scarce, or take it from its formal definition -- the scoring function, the cost model in the proof system's documentation, or the counter the toolchain actually reports.
   Witnesses, constraints, columns, interactions and degree are not interchangeable, and a metric that charges only rows reorders every trade-off in the references, so a change that looks like a win under a guessed metric can measure as a loss.
2. Measure the scarce resource; find the dominating hotspot.
   Trace-based systems ship static cost oracles -- use them (`air.md` I.6).
3. Prime with `references/techniques.md` plus the reference for your arithmetization (`references/r1cs.md`, `references/air.md`, `references/plonkish.md`, `references/degree.md`),
   then look for structure the catalogue misses -- usually the bigger win.
   If the candidate is a new relation for the *system* rather than an encoding inside one circuit, price it with `references/gates.md` first: it will usually say no.
4. Synthesize a candidate.
   Small boolean gadgets: search exactly with `scripts/synthesize.sage` (fix the multiplier `R`, solve a linear system over `QQ`).
5. Verify soundness before trusting it: `scripts/verify.smt2` (cvc5 `QF_FF`) proves the constraint forces the output over a real `F_p`;
   `scripts/impossible.smt2` proves a shape impossible when the search is empty.
   For a trace-based system, also evaluate every constraint on every row of a concrete trace and mutation-test it (`air.md` XI.2).
6. Certify if needed: `scripts/cofactors.sage` extracts the cofactors proving the output is uniquely determined.
7. Re-measure; track the bounds each trick relies on (field size, carry width, characteristic, trace length).

## Tools

Two tools on PATH, no Python glue: **Sage** for algebra (search + certificates), **cvc5** for SMT (`QF_FF`, run directly on `.smt2`).

```bash
sage scripts/synthesize.sage     # single-constraint encoding of a 3-bit function (exact over QQ)
sage scripts/cofactors.sage      # XOR3/Maj soundness cofactors + excluded chars (Groebner)
cvc5 scripts/verify.smt2         # prove a row forces o = f, over a real F_p
cvc5 scripts/impossible.smt2     # prove AND3/OR3 have no single-constraint encoding of the shape
```

cvc5 `QF_FF` proves a statement about the *specific* prime in the file (exact, no side condition);
Sage over `QQ` yields small prime-independent constants and a single "holds for all char > bound" result.
Use both.
See `references/smt.md`, `references/sage.md`.

## Files

- `references/techniques.md` -- cross-arithmetization catalogue (carry-save, CRT/RNS, lookups, range-check/spread, custom gates, non-deterministic advice, solver methods, primitive notes).
- `references/r1cs.md` -- R1CS: what one row can do (single-row multipliers, lambda-packing, decoy roots, sqrt(N) law), not materialising values, free affine structure, bound arithmetic for non-native modmul, lower-bound tools, traps, the GF(2) cost model, and the baseline moves with their soundness side conditions.
  Measured prices throughout.
- `references/air.md` -- AIR / STARK: the area law and which ceiling binds, column engineering, the two-row window, degree, lookups and buses from the designer's side, multi-AIR machine economics, memory and mutable state, non-native arithmetic, a calibration chapter of worked good/bad encodings, traps, and floors.
- `references/plonkish.md` -- PLONKish: why a copy constraint is not free, advice vs routed wires, gate packing and the wire budget, selector grouping, the degree-for-wires dial inside a gate, the decomposition and hard-wire-budget gadget catalogues, non-native arithmetic with the two bound derivations that set every other cost, lookup-table design (accumulator columns, sparse base-B where the base is a carry budget, free rotations), and gate-specific traps.
- `references/gates.md` -- bespoke relations (custom gates, sub-AIRs, precompiles), shared across arithmetizations: what a selector, a degree and the circuit-wide maxima actually cost before the relation is used once; multiplexing and de-multiplexing; relation vs lookup; how relations are invented (substitution, identity choice, search); when the answer is "no relation". A worked break-even and a decision procedure.
- `references/degree.md` -- constraint degree as an economic resource: exact cost per backend, the bracket theorem (`D in {3,5,9,17,33}`), the blowup cliff, degree matching and where the free headroom goes, buying degree back with a column, the gating tax, and where the trade inverts (sumcheck, folding). Two worked break-evens and a decision procedure.
- `references/deferral.md` -- *optional.* Moving work out of the circuit into a second proof over a domain where it is native: the emission, the co-processor's marginal row cost, the reconciliation you must budget for, and the break-even (≈40--50 emulated operations).
- `references/smt.md` -- cvc5 / SMT-LIB: verify, prove impossibility, model the field.
- `references/sage.md` -- SageMath: Groebner ideal-membership proofs, cofactor lifts, CRT/RNS bounds, computing hard-coded constants.
- `scripts/` -- `synthesize.sage`, `cofactors.sage`, `verify.smt2`, `impossible.smt2`.
  Self-checking.
- `CORPUS.md` -- bookkeeping only: which systems have already been read. The references deliberately do not name them, so
  this is the record that lets the corpus grow without duplicated effort. Never cite it from a technique.
