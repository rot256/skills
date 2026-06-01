# SageMath (Gröbner basis) for constraint golfing

Sage covers the algebra that SMT does not: **proving an output is uniquely
determined**, **extracting cofactors** for a machine-checked soundness proof,
**CRT/RNS** bound arithmetic, and **computing the constants a circuit hard-codes**
(curve/field parameters, FFT roots of unity, round constants). `scripts/cofactors.sage`
is the tested entry point; this file explains the methods.

Run `.sage` files with `sage file.sage`. Startup is a few seconds. Work over `QQ` for
search and cofactor extraction: the constants come out small and prime-independent —
integers, or small-denominator fractions — and lift to any field whose characteristic
avoids those small denominators and the multiplier's cube-values (i.e. all sufficiently
large fields). Use `GF(p)` only when a specific prime genuinely matters.

## Mental model

R1CS constraints generate a polynomial ideal `I ⊆ F[x…, o]`. On the boolean cube we
also have the relations `x²−x = 0`, generating a boolean ideal `B`. Two key queries:

- **Determinism / soundness:** does `constraint = 0` (plus `B`) force `o = f`?
  Equivalent to `(o − f)·R − constraint ∈ B` for the unit multiplier `R`. Check by
  reducing modulo a Gröbner basis of `B`; residue `0` ⇒ proven.
- **Certificate (cofactors):** express that membership as
  `(o−f)·R − constraint = Σ gᵢ·(xᵢ²−xᵢ)`. The `gᵢ` are exactly the terms a Lean
  `linear_combination` / Coq `ring` proof consumes.

## Prove a constraint determines the output, and get the cofactors

```python
R.<o,a,b,c> = PolynomialRing(QQ, order='lex')
B = R.ideal(a^2-a, b^2-b, c^2-c)           # boolean relations

maj        = a*b + c*(a + b - 2*a*b)        # target (arithmetic form)
constraint = (o + a + b - 9*c + 3)*(a + b + 6*c - 4) + 12   # the R1CS row, = 0
mult       = a + b + 6*c - 4                # the o-multiplier (must be a unit)

P    = (o - maj) * mult
diff = P - constraint
assert diff.reduce(B.groebner_basis()) == 0   # PROOF: constraint forces o = maj
cof  = diff.lift(B)                            # cofactors g_i  (diff = sum g_i*(x_i^2-x_i))
print(cof)   # -> [2*b*c - b - c - 1, 2*a*c - a - c - 1, 12*a*b - 6*a - 6*b + 54]
```

Those three cofactors are exactly the `linear_combination` terms in
`Clean/Gadgets/SHA256/CarrySave.lean` (`maj3_unique`). For XOR3 the same script
yields `[-4bc+2b+2c-3, -4ac+2a+2c-3, 16ab-8a-8b+32]`. So Sage *finds* the proof and
Lean *checks* it — no cofactor guessing by hand.

Sign/ordering note: `lift` returns *a* valid cofactor tuple; many exist (the ideal
is not a free module). Any tuple that `ring`/`linear_combination` accepts is fine.
If your prover wants a specific arrangement, the relation is just
`constraint + Σ gᵢ·(xᵢ²−xᵢ) = (o−f)·R`.

## Prove no smaller / symmetric encoding exists

Set up the coefficients as symbolic unknowns and the 2ⁿ point conditions as
polynomial equations, then ask whether the system has a solution (e.g. via a Gröbner
basis of the elimination ideal, or by `solve`). Adding symmetry relations (e.g.
`a`- and `b`-coefficients equal) and getting an *empty* variety proves "no symmetric
single-constraint `maj` encoding exists" — the result quoted in `CarrySave.lean`.
For pure existence/impossibility over a *specific* field, cvc5 / `QF_FF`
(`scripts/impossible.smt2`) is often easier; use Sage when you want the algebraic
certificate or a statement that holds across **all** large fields at once.

## CRT / RNS bound checking (foreign-field arithmetic)

When proving `a·b ≡ r (mod p)` non-natively via `a·b = q·p + r` checked mod `n`
(native) and mod `2^t` (limbs), the soundness hinges on a bound. Sage is the place
to *prove* it before you trust the circuit:

```python
p = 2^256 - 2^32 - 977          # secp256k1 base field (foreign modulus)
n = <native field modulus>
t = 264                         # 3 x 88-bit limbs
# Soundness needs the SIGNED difference D = a*b - q*p - r forced into a window
# narrower than the CRT modulus n*2^t.  That requires range bounds on a,b,q,r --
# (p-1)^2 < n*2^t alone only bounds a*b, NOT q*p + r or the sign of D.
A = B = p - 1                   # range bounds you actually enforce on a, b
Q = (A*B) // p + 1              # max quotient given those bounds
R = p - 1                       # r reduced into [0, p)
Dmax = A*B + Q*p + R            # crude bound on |D|
assert Dmax < n * 2^t           # CRT lift of D is unambiguous  =>  equality holds
```

Also use Sage to pick limb sizes, count required range checks, and sanity-check
carry propagation symbolically. RNS: `CRT_list([r1,r2,...],[m1,m2,...])` reconstructs
and `crt` bounds help reason about when you must leave RNS (comparisons/range checks
are the expensive exits).

## Computing constants (elliptic curves, fields, gadget parameters)

Sage is also the right place to *compute the constants a circuit hard-codes* — curve
parameters, FFT roots of unity, Montgomery factors, hash round constants, GLV scalars.
Getting these right out-of-circuit (and checking them) prevents a whole class of "wrong
constant" bugs. Elliptic-curve and finite-field arithmetic are first-class in Sage.

```python
# A pairing-friendly curve and its scalar field (BN254 / alt_bn128)
q = 21888242871839275222246405745257275088696311157297823662689037894645226208583
r = 21888242871839275222246405745257275088548364400416034343698204186575808495617
Fq = GF(q)
E  = EllipticCurve(Fq, [0, 3])           # y^2 = x^3 + 3
assert E.order() == r                    # verify the scalar-field order
G  = E(1, 2); assert G.order() == r      # a generator

# FFT evaluation domain: 2-adicity and a primitive 2^k-th root of unity of GF(r)
Fr     = GF(r)
k      = (r - 1).valuation(2)            # = 28 for BN254  -> max domain 2^28
g      = Fr.multiplicative_generator()   # NB: factors r-1; can hang on big fields (see caveat)
omega  = g ^ ((r - 1) // 2^k)            # primitive 2^k-th root of unity in Fr
assert omega^(2^k) == 1 and omega^(2^(k-1)) != 1

# Poseidon S-box exponent: smallest alpha>1 coprime to p-1   (=5 for BN254)
alpha = next(a for a in range(2, 30) if gcd(a, r - 1) == 1)
# Montgomery constant R = 2^256 mod r ; field inverses, CRT, etc. are one call each
Rmont = (2^256) % r
```

EC tasks Sage makes trivial: curve order / cofactor (`E.order()`, `E.cofactor()`),
torsion and generators (`E.gens()`, `P.order()`), scalar mult and pairings
(`P.weil_pairing(Q, n)`, `P.tate_pairing(...)`), point (de)compression, hash-to-curve
SWU/isogeny maps, twist and embedding-degree checks, GLV endomorphism constants (the
cube root `beta ∈ Fq` and `lambda ∈ Fr`), and finding low-Hamming-weight or `2`-adic
parameters for efficient in-circuit arithmetic.

**Performance caveat:** `GF(r).multiplicative_generator()` and some order/torsion calls
**factor `r−1`** (or the group order), which can hang on 254-bit fields. Either supply a
known generator, factor once and cache (`(r-1).factor()` with hints, or hardcode the
known factorization), or compute on a small friendly field (e.g. Goldilocks
`2^64−2^32+1`, 2-adicity 32) when you only need to validate the *method*. `valuation`,
modular arithmetic, and `EllipticCurve(...).order()` for standard curves are fast.

## Other handy Sage tools

- `resultant` / `elimination_ideal` — eliminate an intermediate witness to see the
  direct input→output relation a gadget enforces.
- `R.<...> = PolynomialRing(GF(p))` then `I.variety()` — enumerate all solutions of a
  small constraint system over a (small) field; good for exhaustive soundness checks.
- `factor` on the eliminated polynomial — reveals the "(o − f)·(unit)" structure that
  makes a single-constraint encoding work.

## Discipline

Always pair a Sage *finding* with a machine-checked *proof* (Lean/Coq) or at least a
second independent check. `reduce(...) == 0` over `QQ` is a real proof of the
polynomial identity, but the field-characteristic side conditions (multiplier ≠ 0,
char ∉ small set) must be discharged separately — see how `CarrySave.lean` proves
`a + b + 6c − 4 ≠ 0` by an 8-way boolean case split.
