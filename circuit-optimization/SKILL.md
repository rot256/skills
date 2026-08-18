---
name: circuit-optimization
description: Optimizing arithmetic circuits and constraint systems (R1CS, PLONKish, AIR) for zero-knowledge proofs.
---

# Circuit Optimization

Reduce the cost of an arithmetic circuit / constraint system.
A toolbox and a method, not a fixed playbook: `references/techniques.md` primes known moves but is deliberately incomplete -- the largest wins come from composing tricks or from structure specific to your circuit.
Start Boolean work with `references/boolean-zk.md`: it separates deterministic function complexity from relation/checker complexity and routes each backend to its actual cost model.
Arithmetization-specific moves live in their own reference: `references/r1cs-fp.md`, `references/r1cs-gf2.md`, `references/air.md` and `references/plonkish.md`.
Sumcheck prover scheduling is optional and backend-specific; use `references/sumcheck.md` only after the proof system is known to use sumcheck.
Two resources are priced separately because they are *global* rather than local: constraint degree (`references/degree.md`), which is almost always under-spent, and a bespoke relation added to the system itself -- a custom gate, a sub-AIR, or a precompile -- which is charged once against every circuit whether it is used or not (`references/gates.md`).

## Know What Is Free

Every optimization moves work into what the proof system charges nothing for and minimizes what it charges for.

| System | Pays for | Free / cheap |
|--------|----------|--------------|
| **R1CS** (Groth16, Marlin, Spartan) | multiplication rows `(A*z)(B*z)=(C*z)` | linear combinations feeding a row, inlined wire definitions (a standalone asserted equality still costs a row) |
| **Restricted GF(2) XAG/R1CS** | witnessed products / AND gates | XOR, NOT, constants, and arbitrary affine fan-in; this equivalence does not extend to advice-bearing relations |
| **Native GF(2^k)** | base-field products, nonlinear word relations, and committed values as defined by the backend | inlineable base-field linear forms, basis changes, fixed multipliers, and Frobenius maps |
| **AIR / STARK** | `(preprocessed + main + permutation width) x padded height`; interactions; max constraint degree | constraints themselves, periodic/preprocessed columns, `is_transition` gating, anything affine in committed columns, values read from the next row |
| **PLONKish** | rows x columns; gate degree; copy constraints and their permutation columns; selector groups | additions within a gate, rotations within a region, selectors on unused rows, unrouted advice wires |

State the scarce metric (mult-constraints? trace cells? interactions? degree?) and get a baseline before optimizing.
The two most common ways to waste a week: optimizing width while padding eats the win, and reducing a degree that was not the global maximum.

## Workflow

1. Establish the cost metric before anything else.
   Ask the user which resource is scarce, or take it from its formal definition -- the scoring function, the cost model in the proof system's documentation, or the counter the toolchain actually reports.
   Witnesses, constraints, columns, interactions and degree are not interchangeable, and a metric that charges only rows reorders every trade-off in the references, so a change that looks like a win under a guessed metric can measure as a loss.
2. Measure the scarce resource; find the dominating hotspot.
   Trace-based systems ship static cost oracles -- use them (`air.md` "Static Cost Oracles").
3. Prime with `references/techniques.md` plus the reference for your arithmetization (`references/r1cs-fp.md`, `references/air.md`, `references/plonkish.md`, `references/degree.md`).
   For Boolean work, read `references/boolean-zk.md` before importing multiplicative-complexity or XOR-minimization results, then look for structure the catalogue misses -- usually the bigger win.
   If the candidate is a new relation for the *system* rather than an encoding inside one circuit, price it with `references/gates.md` first: it will usually say no.
4. Synthesize a candidate.
   Small boolean gadgets: search exactly with `scripts/synthesize.sage` (fix the multiplier `R`, solve a linear system over `QQ`).
   Restricted GF(2) XAGs: use `scripts/regular_reduce.sage` to remove affine regularity from a scalar function, `scripts/quadratic_and_count.sage` for a scalar quadratic, `scripts/exact_xag.sage` for a small exact search, `scripts/paar_optimize.sage` for a heuristic seed, and `scripts/xag_rewrite.sage` for verified bounded rewriting.
5. Verify soundness before trusting it: `scripts/verify.smt2` (cvc5 `QF_FF`) proves the constraint forces the output over a real `F_p`;
   `scripts/impossible.smt2` proves a shape impossible when the search is empty.
   For a trace-based system, also evaluate every constraint on every row of a concrete trace and mutation-test it (`air.md` "Three Checks Worth Demanding").
6. Certify if needed: `scripts/cofactors.sage` extracts the cofactors proving the output is uniquely determined.
7. Re-measure; track the bounds each trick relies on (field size, carry width, characteristic, trace length).

## Tools

**Sage** for algebra (search and certificates), **cvc5** for SMT over finite fields (`QF_FF`, run directly on `.smt2`).

```bash
sage scripts/synthesize.sage     # single-constraint encoding of a 3-bit function (exact over QQ)
sage scripts/cofactors.sage      # XOR3/Maj soundness cofactors + excluded chars (Groebner)
cvc5 scripts/verify.smt2         # prove a row forces o = f, over a real F_p
cvc5 scripts/impossible.smt2     # prove AND3/OR3 have no single-constraint encoding of the shape
sage scripts/exact_xag.sage      # increasing-budget GF(2) XAG self-tests
sage scripts/regular_reduce.sage # autosymmetry and D-reduction self-tests
sage scripts/quadratic_and_count.sage  # polar-factorized quadratic GF(2) construction
sage scripts/paar_optimize.sage  # heuristic shared-ANF factoring self-tests
sage scripts/xag_rewrite.sage    # bounded exact rewrite and miter self-tests
```

cvc5 `QF_FF` proves a statement about the *specific* prime in the file (exact, no side condition); Sage over `QQ` yields small prime-independent constants and a single "holds for all char > bound" result.
Use both. See `references/smt.md`, `references/sage.md`.

## Files

- `references/techniques.md` -- cross-arithmetization catalogue (carry-save, CRT/RNS, lookups, range-check/spread, custom gates, non-deterministic advice, solver methods, primitive notes).
- `references/boolean-zk.md` -- Boolean-specific ZK rewrites: binary-word repacking, witnessed compute-then-check, relational don't-cares, permutation certificates, post-commitment fingerprints, Freivalds checks, and co-processor deferral.
  XOR count is a secondary, explicitly model-dependent metric.
- `references/r1cs-fp.md` -- R1CS over a prime field: what one row can do (single-row multipliers, lambda-packing, decoy roots, baby-step giant-step), not materialising values, free affine structure, bound arithmetic for non-native modmul, traps, and the baseline moves with their soundness side conditions.
- `references/r1cs-gf2.md` -- restricted free-affine GF(2) constructions: adders, conditional linear maps, affine reductions, quadratic factoring, don't-cares, ANF factoring, and bounded XAG rewriting.
- `references/binary-extension-fields.md` -- arithmetic native to GF(2^k) or built as a tower over it: cost-model separation, linear basis changes, bilinear rank, RMFE and commitment packing, multiplication and inversion through towers, witnessed inverse checks, Frobenius-oriented nonlinear layers, and evaluation/interpolation constructions.
- `references/air.md` -- AIR / STARK: the area law and which ceiling binds, column engineering, the two-row window, degree, lookups and buses from the designer's side, multi-AIR machine economics, memory and mutable state, non-native arithmetic, a calibration chapter of worked good/bad encodings, traps, and fixed backend charges.
- `references/plonkish.md` -- PLONKish: why a copy constraint is not free, advice vs routed wires, gate packing and the wire budget, selector grouping, the degree-for-wires dial inside a gate, the decomposition and hard-wire-budget gadget catalogues, non-native arithmetic with the two bound derivations that set every other cost, lookup-table design (accumulator columns, sparse base-B where the base is a carry budget, free rotations), and gate-specific traps.
- `references/gates.md` -- bespoke relations (custom gates, sub-AIRs, precompiles), shared across arithmetizations: what a selector, a degree and the circuit-wide maxima actually cost before the relation is used once; multiplexing and de-multiplexing; relation vs lookup; how relations are invented (substitution, identity choice, search); when the answer is "no relation". A worked break-even and a decision procedure.
- `references/degree.md` -- constraint degree as an economic resource: exact cost per backend, the bracket theorem (`D in {3,5,9,17,33}`), the blowup cliff, degree matching and where the free headroom goes, buying degree back with a column, the gating tax, and where the trade inverts (sumcheck, folding). Two worked break-evens and a decision procedure.
- `references/deferral.md` -- *optional.* Moving work out of the circuit into a second proof over a domain where it is native: the emission, the co-processor's marginal row cost, the reconciliation you must budget for, and the break-even (~40--50 emulated operations).
- `references/sumcheck.md` -- *optional.* Prover scheduling for sumcheck-based backends: tower-field rounds, small/base/extension multiplication separation, delayed folding, and equality-polynomial factoring; these do not reduce the circuit itself.
- `references/smt.md` -- cvc5 / SMT-LIB: verify, prove impossibility, model the field.
- `references/sage.md` -- SageMath: Groebner ideal-membership proofs, cofactor lifts, CRT/RNS bounds, computing hard-coded constants.
- `scripts/` -- self-checking Sage, Python, and cvc5 tools documented in `scripts/README.md`.
- `CORPUS.md` -- bookkeeping for systems and primary resources already read or queued; never cite it from a technique.

## Useful Resources

- https://zk.golf/llms.txt : circuit-golfing platform scored by witnesses + constraints -- challenge list and REST API.
  The measured prices in `references/r1cs-fp.md` were taken under that cost model.
- https://github.com/usnistgov/Circuits/ : machine-readable AND-minimized circuits for the primitives tabulated in `r1cs-gf2.md` "Published AND-Gate Records for Standard Primitives".
- mockturtle, the EPFL logic-synthesis library, implements XAG rewriting, resubstitution and refactoring with AND-count objectives; ABC does not because it prices AND and XOR alike.
