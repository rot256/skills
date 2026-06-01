---
name: circuit-optimization
description: Optimizing arithmetic circuits / constraint systems (R1CS, PLONKish, AIR) for zero-knowledge proofs — minimizing multiplication constraints, rows, witnesses, and gate degree. Use when reducing constraint/witness counts, designing or golfing R1CS/PLONK/AIR gadgets (boolean ops, adders, range checks, hashes like SHA-256/Keccak/Poseidon), doing foreign-field/non-native or CRT/RNS arithmetic, choosing lookups vs arithmetic, or using SMT (cvc5) and SageMath (Gröbner basis) to synthesize, verify, and certify constraint encodings.
---

# Circuit optimization

Reduce the cost of an arithmetic circuit / constraint system without breaking
soundness. This skill is a **toolbox and a method**, not a fixed playbook.

> **Read this first: the tricks here are starting points.** The catalogue in
> `references/techniques.md` primes you with known moves; it is deliberately
> incomplete. Real wins usually come from *composing* tricks or from structure
> specific to your circuit that no catalogue lists. Always treat a known trick as a
> lens to look through, then keep searching — and write down what you find.

## When to use

- Cutting constraint / witness / row counts in R1CS, PLONKish, or AIR.
- Designing or golfing gadgets: boolean logic, adders, comparisons, range checks,
  hashes (SHA-256, Keccak, Poseidon), foreign-field / non-native arithmetic.
- Deciding lookups vs. arithmetic, or how to lay out custom gates.
- Using a solver/algebra system to **find**, **verify**, or **certify** an encoding.

## The one mental model: know what is free

Every optimization is "move work into what your proof system charges nothing for, and
minimize what it charges for."

| System | Pays for | Free / cheap |
|--------|----------|--------------|
| **R1CS** (Groth16, Marlin, Spartan) | multiplication rows `(A·z)(B·z)=(C·z)` | linear combinations *feeding a row* and inlined wire definitions (a standalone asserted equality still costs a row) |
| **PLONKish** (halo2, plonky2/3, Kimchi) | rows × columns; FFT blowup ∝ **max gate degree** | additions within a gate, selectors on unused rows |
| **AIR / STARK** | trace width × length; constraint degree | — |

Before optimizing, state the metric (mult-constraints? rows? witnesses? degree?) and
get a baseline count. Optimize the thing that is actually scarce.

## Workflow

1. **Measure.** Count the scarce resource for the current circuit. Identify the
   hotspot (the gadget or pattern dominating the count).
2. **Prime with the catalogue.** Skim `references/techniques.md` for moves that fit
   the hotspot's shape (boolean logic → §3,§4,§7; big-int → §5; repeated tables →
   §6; hard-to-compute values → §9).
3. **Look for structure the catalogue misses.** Use the prompts at the end of
   `techniques.md`. The biggest wins are usually here, not in the list.
4. **Synthesize a candidate encoding.** For small boolean gadgets, search exactly with
   `scripts/synthesize.sage` (fix the multiplier `R`, solve a linear system over `QQ`).
5. **Verify it is sound** before trusting it: `scripts/verify.smt2` (cvc5, `QF_FF`)
   proves the constraint forces the intended output over a real `F_p`;
   `scripts/impossible.smt2` proves a shape is *impossible* when the search comes up
   empty. See `references/smt.md`.
6. **Certify for a proof assistant** if the circuit is formally verified:
   `scripts/cofactors.sage` (Sage Gröbner basis) extracts the `linear_combination` /
   `ring` cofactors and proves the output is uniquely determined. See
   `references/sage.md`.
7. **Re-measure and keep the proofs green.** Optimization without a correctness check
   is how soundness bugs ship. Track the bounds each trick relies on (field size,
   carry width, characteristic).

## Tools quickstart

Two tools on PATH, **no Python glue**: **Sage** for the algebra (search + certificates),
**cvc5** for SMT — `QF_FF` finite-field theory, run directly on `.smt2` files.

```bash
# Find a single-constraint encoding of a 3-bit function (exact over QQ, deterministic)
sage scripts/synthesize.sage

# Reproduce the SHA-256 XOR3/Maj soundness cofactors + excluded chars (Gröbner lift)
sage scripts/cofactors.sage

# Prove a candidate row forces o = f and is non-vacuous, over a real F_p
cvc5 scripts/verify.smt2

# Prove AND3/OR3 have no single-constraint encoding of the shape, over a real F_p
cvc5 scripts/impossible.smt2
```

**Two complementary guarantees.** cvc5 `QF_FF` proves a statement about the *specific*
prime in the `.smt2` file (swap in your circuit's field) — exact, no "unit over the
reals" side condition. Sage over `QQ` yields small, prime-independent constants —
integers or small-denominator fractions — and a single "holds for all fields of
char > bound" result, the form the `clean` Lean proofs consume. Use both: Sage to
find/certify nice constants valid for all large fields, cvc5 to pin a particular field
exactly. All four are self-checking and were cross-checked against the verified SHA-256
gadgets in `~/src/clean` (`Clean/Gadgets/SHA256/CarrySave.lean`); read the scope caveats
in `references/smt.md` and `references/sage.md`.

## Files

- `references/techniques.md` — the catalogue (free linear combos, multi-operand add,
  carry-save, single-constraint boolean gadgets, CRT/RNS & foreign-field, lookups,
  range-check/spread, custom gates, non-deterministic advice, solver/algebra methods,
  primitive-specific notes). Cited; **starting points**.
- `references/smt.md` — cvc5 / SMT-LIB: verify, prove impossibility, (carefully)
  synthesize; how to model the field.
- `references/sage.md` — SageMath: Gröbner ideal-membership proofs, cofactor lifts,
  CRT/RNS bound checking, elimination/resultants.
- `references/sha256-case-study.md` — the `clean` SHA-256 R1CS reductions worked
  end-to-end, with constraint counts and the tool loop that found them.
- `scripts/` — `synthesize.sage`, `cofactors.sage` (Sage: search + Gröbner
  certificates), `verify.smt2`, `impossible.smt2` (cvc5 `QF_FF`: exact per-field
  proofs). Self-checking, cross-checked against `clean`.

## Non-negotiables

- **Soundness first.** A cheaper circuit that is under-constrained is broken. Every
  witness hint (`<--`) needs a determining constraint (`===`); every reduction needs
  its bound proven. The most common ZK bug is exactly an optimization that forgot to
  pin a value — see `techniques.md` §9.
- **Verify end-to-end.** Prove the optimized gadget equals the spec (SMT/Sage, or a
  proof assistant if available). If you cannot fully verify, say what is unproven.
- **The catalogue is a floor, not a ceiling.** When you find a new trick, add it to
  `references/techniques.md`.
