# SMT (cvc5 / SMT-LIB) for constraint golfing

`cvc5` does two jobs: **verify** a candidate encoding and **prove impossibility**. It
speaks the SMT-LIB finite-field theory `QF_FF` directly, so you reason in the *actual*
field `F_p` — no "over the reals plus a unit side condition" detour. Run it on the file
(`cvc5 scripts/verify.smt2`); write SMT-LIB by hand or generate it from Sage — no Python
driver.

`scripts/verify.smt2` and `scripts/impossible.smt2` are worked examples; this file
explains the SMT-LIB so you can adapt them.

## When SMT is the right tool

| Goal | SMT verdict | Reliable? |
|------|-------------|-----------|
| Prove constraint forces `o = f` | `unsat` of (bits ∧ constraint ∧ `o≠f`) | yes, fast |
| Prove constraint pins `o` to a bit | follows from above, or check `o∉{0,1}` unsat | yes |
| Prove NO encoding of a shape exists | `unsat` of the synthesis query | yes (can be slow) |
| FIND coefficients (satisfiable) | `sat` + model | works in `QF_FF`, but prefer `synthesize.sage` for nice constants |

Rule of thumb: **cvc5 for the `unsat` direction (exact per-field proofs), Sage for the
`sat` direction (search + prime-independent certificates).** `QF_FF` can find models
too, but Sage's `QQ` search gives small constants valid across all large fields, which
is usually what you want.

## The two guarantees: pick what you need

- **`QF_FF` over a specific `p`** — an exact theorem about *that* field. No side
  conditions: cvc5 reasons in `F_p`, so a multiplier that is a unit there just *is* a
  unit. Put your circuit's prime in the `(define-sort ...)` line and the result is about
  your circuit's field.
- **Sage over `QQ`** (`cofactors.sage`, `synthesize.sage`) — small, prime-independent
  constants and a single "holds for **all** fields of char > bound" result (the bound is
  the finite set of primes dividing the multiplier's cube-values and any coefficient
  denominators). This is the form the `clean` Lean proofs use (`char ∉ {2,3}`), so it is
  the better default when exploring techniques you intend to prove generically.

A `QF_FF` query at one large prime is a strong sanity check, **not** an all-fields
statement; for that, use the `QQ` route.

## Modeling the field in QF_FF

```smt2
(set-logic QF_FF)
(define-sort F () (_ FiniteField 21888242871839275222246405745257275088548364400416034343698204186575808495617))
(declare-const a F)                       ; field elements
(assert (or (= a (as ff0 F)) (= a (as ff1 F))))   ; a is a bit
```

- Literals: `(as ffN F)` for integer `N` (reduced mod `p`); negatives like
  `(as ff-4 F)` are accepted.
- Operations are n-ary: `(ff.add x y z ...)`, `(ff.mul x y z ...)`, plus `(ff.neg x)`.
- A constraint row is `(= (... ) (as ff0 F))` — keep it in `= 0` form to mirror
  `assertZero` rows and avoid sign mistakes.
- Disequations (`(not (= R (as ff0 F)))`) model "R is a unit on this point" directly.

## Verify a candidate row forces o = f

Check the negation is unsatisfiable, then confirm the premise is non-vacuous (else the
`unsat` is empty). Use `(push)/(pop)` for the two queries in one file; enable
incrementally so plain `cvc5 file.smt2` works:

```smt2
(set-option :incremental true)
(set-logic QF_FF)
(define-sort F () (_ FiniteField <p>))
(declare-const a F) (declare-const b F) (declare-const c F) (declare-const o F)
(assert (or (= a (as ff0 F)) (= a (as ff1 F))))   ; ... and b, c
; XOR3 row: (o + 2a + 2b + 7c)(a + b - 4c + 1) = 6a + 6b - 24c
(echo "forces o=parity (expect unsat):")
(push 1)
  (assert (= (ff.add (ff.mul (ff.add o (ff.mul (as ff2 F) a) (ff.mul (as ff2 F) b) (ff.mul (as ff7 F) c))
                             (ff.add a b (as ff1 F) (ff.mul (as ff-4 F) c)))
                     (ff.mul (as ff-6 F) a) (ff.mul (as ff-6 F) b) (ff.mul (as ff24 F) c))
             (as ff0 F)))
  (assert (not (= o (ff.add a b c (ff.mul (as ff-2 F) a b) (ff.mul (as ff-2 F) b c)
                                  (ff.mul (as ff-2 F) a c) (ff.mul (as ff4 F) a b c)))))
  (check-sat)                                       ; unsat => row forces o = parity
(pop 1)
; non-vacuity: re-run with (= o parity) instead of (not ...); expect sat.
```

`scripts/verify.smt2` is this, fully written out for XOR3 and Maj (both directions).

Useful arithmetic forms of boolean targets (3 bits):
- XOR2: `a+b−2ab` · AND: `ab` · OR: `a+b−ab` · select `a?b:c`: `c + a(b−c)`
- parity / XOR3: `a+b+c −2(ab+bc+ca) +4abc`
- majority: `ab+bc+ca −2abc`

## Prove a shape is impossible

For `(o + A)·R = O` with `A,R,O` affine and `R` a unit: the **coefficients** are the
field unknowns, the `2ⁿ` cube points are constants with `o = f(point)` plugged in.
Assert the per-point equation and `R(point) ≠ 0`, then `(check-sat)`. `unsat` means no
such encoding exists **over this `F_p`** — a genuine finite-field theorem, stronger and
cleaner than the old `QF_NRA`/reals query (no characteristic-0 caveat).

`scripts/impossible.smt2` does exactly this and proves AND3 and OR3 have no
single-constraint encoding of the shape. (For "no encoding over *any* large field", pair
it with the `QQ` Gröbner argument in `sage.md`.)

To probe a *symmetric* encoding, add symmetry relations tying the input coefficients
(`(assert (= a0 a1))`, etc.). Instructive: for Maj a symmetric encoding *does* exist over
a field (`(o − s/4)(9 − 6s) = −3s/4`, `s = a+b+c`), so a symmetric `QF_FF` query returns
**sat** — only the **integer-coefficient** symmetric encoding is impossible (a separate
search). Scope the claim to the coefficient ring: "no symmetric *integer* encoding", not
"no symmetric encoding". This is the kind of overclaim SMT catches.

## Synthesis (use sparingly)

`QF_FF` *can* return a model of the synthesis query (drop `o`, make the coefficients
unknowns, ask `(check-sat)` + `(get-value (...))`). But the model is whatever the solver
lands on — often ugly, field-specific constants. For human-readable, prime-independent
encodings prefer `scripts/synthesize.sage` (fix `R`, solve the linear system over `QQ`).

## Tips

- `cvc5 file.smt2` runs it; `cvc5 --tlimit=30000 file.smt2` bounds wall time (ms). On
  timeout cvc5 prints `unknown` — treat as "no answer", never as a proof.
- `(set-option :incremental true)` at the top lets `(push)/(pop)` work without a flag.
- `(echo "label")` annotates each `(check-sat)` so a multi-query file is readable.
- `--produce-models` then `(get-value (o))` to inspect a witness.
- Cross-check anything surprising a second way (truth-table enumeration, or Sage `QQ`).
