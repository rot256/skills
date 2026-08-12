# What does an `n`-bit range check cost?

**Short answer.** `2n` is *not* optimal — `2n - 1` is achievable for every `n ≥ 1`, over
every field. And `2n - 1` is optimal at `n = 2`: there the exact minimum is `3`, proved
against *arbitrary* systems (arbitrary affine forms, arbitrary field-element witnesses,
no assumption that anything is a bit). For `n ≥ 3` the formal floor is `4` (§3b: one
witness certifies at most two bits), and the exact optimum — `4` or `5 = 2·3 - 1` — is
left open here; §5 gives the Bezout-style argument that says it is again `2n - 1`, states
exactly which algebraic-geometry input is missing from the formalisation, and pinpoints
the one remaining configuration (two witnesses, two rows) that would settle `n = 3`.

So: the cost per bit is `2`, not `1.5`; the only saving over the folklore construction is
a single unit, and it is a real one — it applies to every range check in the project.

---

## 1. The model (`Model.lean`)

An affine form in the public input `x : F` and the witness vector `w : Fin m → F` is

```
L.eval x w = L.cx * x + ∑ i, L.cw i * w i + L.c        -- `Aff F m`
```

A row is `(A.eval x w) * (B.eval x w) = C.eval x w` (`Row F m`, `Row.Holds`). A system is
`r` such rows over `m` witnesses (`System F m r`), its **score** is `m + r`, and it
**certifies the `n`-bit range** when

```
∀ x : F, (∃ w, ∀ j, (S.row j).Holds x w)  ↔  ∃ k : ℕ, k < 2 ^ n ∧ x = (k : F)
```

(`System.Certifies`). Note what is and is not assumed:

* affine forms are free — they are the `A`, `B`, `C` of the rows, never a row themselves;
* the witnesses are arbitrary field elements, in arbitrary number, used arbitrarily;
* `x` itself costs nothing: it is the public input, not an allocation.

The forward direction of the `↔` is soundness, the backward direction completeness. This
is the definition the lower bound quantifies over, so the bound is not question-begging:
nothing in it presumes a bit decomposition.

## 2. Beating `2n`: score `2n - 1` for every `n` (`Construction.lean`)

The folklore system allocates `b 0, …, b (n-1)`, asserts `n` booleanity rows and gets the
recomposition `x = ∑ 2 ^ i * b i` for free: `⟨n, n⟩ = 2n`.

But then the *low bit need not be allocated at all*. Allocate `b 1, …, b (n-1)` only
(`n - 1` allocations) and define

```
b₀ := x - ∑_{i = 1}^{n-1} 2 ^ i * b i        -- a free affine form
```

Asserting `b₀ * (b₀ - 1) = 0` is still exactly one row (a product of two affine forms), so
the system has `n - 1` allocations and `n` rows:

```
score = (n - 1) + n = 2n - 1 < 2n.
```

* `Solution.Research.rangeSystem` — the system (for `n = m + 1`).
* `Solution.Research.rangeSystem_certifies` — it certifies the `(m+1)`-bit range, over an
  arbitrary field, both directions.
* `Solution.Research.exists_system_score_lt_two_mul` — score `= 2n - 1 < 2n` for `n ≥ 1`.
* `Solution.Research.range_check_below_two_n` (in `RangeFloor.lean`) — the same, stated
  as the headline refutation of `2n`.

This is directly implementable in the project's cost model: the low bit is an
`Expression`, not a `witness` call, and `b₀ * (b₀ - 1)` is one degree-2 product, hence one
`assert` accepted by `Challenge.CostR1CS.isR1CSRow`. Every range check in the RSA tree can
drop exactly one allocation.

## 3. `2n - 1` is optimal at `n = 2` (`LowerBound.lean`, `Optimality.lean`)

Over an algebraically closed field of characteristic zero:

```
Solution.Research.range_check_floor :
  IsLeast {s | ∃ m r (S : System F m r), S.Certifies 2 ∧ S.score = s} 3
```

Membership is the construction of §2 (`m = 1`, `r = 2`). The lower bound
(`score_ge_three`) says no system of score `≤ 2` certifies a range of `n ≥ 2` bits, and it
rests on two facts that are interesting on their own:

* **One row certifies at most one bit** (`one_row_dichotomy`). For *any* `m` and any row,
  the set of accepted `x` either has at most two elements or omits at most one element of
  `F`. The proof is a complete case analysis on the witness parts `u₁ = A.cw`,
  `u₂ = B.cw`, `u₃ = C.cw`:
  * `u₁ ≠ 0` and `u₂ ≠ 0`: pick `v` with `⟨u₁,v⟩ ≠ 0 ≠ ⟨u₂,v⟩` and put `w = t·v`; the row
    becomes a quadratic in `t` with nonzero leading coefficient, which has a root — so
    *every* `x` is accepted;
  * `u₁ ≠ 0`, `u₂ = 0` (and symmetrically): the row is `⟨b(x)·u₁ - u₃, w⟩ = d(x) - a(x)b(x)`,
    solvable whenever `b(x)·u₁ ≠ u₃`, which fails for at most one `x` — unless `b` is
    constant, in which case the row degenerates to an affine condition on `x`;
  * `u₁ = u₂ = 0`: if `u₃ ≠ 0` every `x` is accepted, otherwise the row is a univariate
    quadratic in `x`, with at most two roots unless it is identically zero.
* **No witnesses ⇒ at most two values** (`zero_witness_dichotomy`): with `m = 0` every row
  is a univariate quadratic in `x`, so the accepted set is all of `F` or has `≤ 2`
  elements.

Since `{0,1,2,3}` has four elements and infinite complement in characteristic zero, both
alternatives fail, and every `(m, r)` with `m + r ≤ 2` is ruled out (`r = 0`: everything is
accepted; `r = 1`: the first fact; `r = 2, m = 0`: the second).

**Scope of the hypotheses.** Algebraic closure is used only to solve a quadratic in the
witness; characteristic zero only so that `0,1,2,3` are distinct and `2 ^ n`, `2 ^ n + 1`
are outside the range. Over a large prime field the same conclusion holds — the missing
step is that for a quadratic `q`, the set `{x | q(x) is a square}` has about `p/2`
elements, which is a standard character-sum count but is not formalised here.

### 3a. A constraint on every certifying system, for every `n`

The one-row dichotomy also yields a statement valid for all `n ≥ 2`, not just `n = 2`
(`row_coAtMostOne_of_certifies`): in *any* system that certifies an `n`-bit range, every
single row, taken on its own, must be satisfiable for all but at most one value of `x`.
Otherwise that one row already restricts the accepted set to at most two values. In
particular no row may constrain `x` alone, and every row must use a witness nontrivially.
Both constructions below and in §2 satisfy this, as they must.

### 3b. One witness certifies at most two bits, for every `n` (`OneWitness.lean`)

The next step of the lower bound is proved against arbitrary systems with a *single*
witness `y` and **any** number of rows:

```
Solution.Research.one_witness_dichotomy (S : System F 1 r) :
  AtMostFourRoots S.solutions ∨ CoAtMostOne S.solutions
```

where `AtMostFourRoots S` means `S` contains no five distinct elements. With one witness
each row is `α y² + β(x) y + γ(x) = 0` with `α ∈ F` a *constant* (it is `A.cw 0 * B.cw 0`),
`deg β ≤ 1` and `deg γ ≤ 2`. The proof:

* If two rows have a non-proportional pair `(α, β)` — more precisely, if some combination
  eliminates `y²` nontrivially — one gets a *linear* consequence `b(x) y + g(x) = 0` with
  `deg b ≤ 1`, `deg g ≤ 2`. For `x` with `b(x) ≠ 0` the witness is forced,
  `y = g(x)/b(x)`, and substituting into row `k` and clearing denominators gives
  `P k = C αₖ * g² - βₖ * g * b + γₖ * b²`, a polynomial of degree `≤ 4`. Either some
  `P k ≠ 0`, and then every accepted `x` with `b(x) ≠ 0` is one of its `≤ 4` roots (so at
  most `4 + 1` — the bookkeeping is done so that the conclusion is "no five accepted
  values"), or all `P k = 0` and every `x` with `b(x) ≠ 0` is accepted, so at most one `x`
  is missed.
* If no such consequence exists, all rows are proportional as quadratics in `y`, and a
  single quadratic in one unknown always has a root over an algebraically closed field
  unless it is a nonzero constant; the accepted set is then all of `F` or the zero set of
  a nonzero polynomial of degree `≤ 2`.

Since the `n`-bit range with `n ≥ 3` contains five distinct values and misses infinitely
many, neither alternative can be the range set: `one_witness_not_certifies`. Hence
`alloc_ge_two` (three bits need at least two allocations) and, ruling out the remaining
configurations of score `≤ 3` — `(m,r) ∈ {(0,∗),(1,∗),(2,0),(2,1),(3,0)}` —
`score_ge_four`.

## 4. The bound is not about bits (`Conic.lean`)

To show the lower bound really does range over exotic systems, here is a score-`3`
two-bit certifier in which no bit is ever witnessed. Take the four points
`(0,0), (1,1), (2,4), (3,9)` on `w = x²`, and two degenerate conics of the pencil through
them (each a pair of lines, hence exactly one R1CS row):

```
(w - x) * (w - 5x + 6) = 0
(w - 2x) * (w - 4x + 3) = 0
```

Their common solutions are exactly the four base points, so the accepted `x` are exactly
`0,1,2,3`, with the single witness `w` taking the values `0,1,4,9`
(`conicSystem_certifies`, valid whenever `3 ≠ 0` in `F`). One allocation, two rows: score
`3` again.

This is the honest version of the "base-4 digit" idea in the problem statement, and it
shows why that idea does not give `1.5` per bit in general — see §6.

## 5. General `n`: why `2n - 1` should be the answer (not formalised)

Let `V ⊆ A^{1+m}` be the solution set of the `r` rows and `S = π_x(V)` the accepted set,
`|S| = 2 ^ n`. Since `S` is finite, `x` is constant on each irreducible component of `V`,
so `V` has at least `2 ^ n` irreducible components, each of codimension `≥ 1`.

* Each row is a quadric, so by the refined Bezout theorem the total degree of `V` is at
  most `2 ^ r`, giving `2 ^ n ≤ 2 ^ r`, i.e. **`r ≥ n`**.
* Every irreducible component of `V` of codimension `c` is a component of the intersection
  of `c` generic linear combinations of the defining quadrics, so the components of a
  fixed codimension `c` have total degree at most `2 ^ c`. Summing over `1 ≤ c ≤ m + 1`
  gives `|S| ≤ 2 + 4 + … + 2 ^ (m+1) = 2 ^ (m+2) - 2`, hence `2 ^ n < 2 ^ (m+2)`, i.e.
  **`m ≥ n - 1`**.

Together: `score = m + r ≥ 2n - 1`, matched by §2. Both bullets are tight in the extremal
case: the bit construction is `n` quadrics in `A^n` cutting out exactly `2 ^ n` isolated
points.

**What is missing in Lean.** Mathlib has no refined Bezout theorem, no degree theory for
affine varieties, and no "components of codimension `c` are components of `c` generic
combinations" lemma. Formalising either bullet means building that theory first; it is
well beyond a targeted development, which is why the formal results stop where the
elementary eliminations of §3/§3b stop.

**Exactly where the formal argument stops.** For `n = 3` the score-`4` configurations are
`(m,r) = (0,4), (1,3), (2,2), (3,1), (4,0)`. All are ruled out above except **`(2,2)`:
two witnesses `y, z` and two rows**. What is needed there is the elimination of two
unknowns from two quadrics, i.e. either (a) the statement that two conics in `P²` always
meet (Bezout in the smallest case), or (b) a resultant computation `Res_z`, `Res_y` with
explicit degree bookkeeping. Mathlib does have `Polynomial.resultant`, so route (b) is
not out of reach, but it is a development in its own right: the accepted set has to be
tracked through several coordinate normalisations of the pair `(y,z)`, and every branch
needs its own degree bound. Until it is done, `4 ≤ score` is the honest formal floor for
`n ≥ 3`, with `5 = 2n - 1` achieved and conjectured optimal.

## 6. Ideas that were checked and do **not** beat `2n - 1`

* **Base-4 (and base-`2^k`) digits.** A digit `d ∈ {0,1,2,3}` satisfies the degree-4
  condition `d(d-1)(d-2)(d-3) = 0`. Written with an auxiliary product this is
  `u = d(d-3)` and `u(u+2) = 0`: 2 allocations and 2 rows, i.e. `4` score for `2` bits —
  the same `2` per bit. It cannot be done with `1` allocation and `2` rows *in the digit
  alone*: two quadratics in a single variable cut out at most two values, and
  `one_row_dichotomy` is the general form of that obstruction. The digit *can* be pinned
  with `1` extra witness and `2` rows when it is a free affine function of `x`
  (§4) — but only one digit of a decomposition can be free (the others must be
  allocated), so a `2k`-bit value costs `(k - 1)` digits `+ k` auxiliaries `= 2k - 1`
  allocations and `2k` rows: `4k - 1 = 2n - 1` again. Base `2^k` behaves the same way.
* **Amortisation over many range checks.** Repeating the degree argument of §5 with `t`
  public inputs and `|S| = 2 ^ (tn)`: components have codimension `≥ t`, so
  `2 ^ (tn) ≤ 2 ^ r` and `2 ^ (tn) ≤ 2 ^ (t + m + 1)`, giving `score ≥ 2tn - t = t(2n-1)`.
  That is exactly `t` independent copies: the marginal cost of the `k`-th check is not
  lower than the first. (Same caveat: this is the non-formalised Bezout argument. What
  *is* formalised transfers only in the weak form that fixing all but one input reduces a
  multi-check system to a single-check one, so the score-`3` bound applies to the whole.)
* **Certifying an aggregate instead of each value.** A sum `∑ x_i` being `n`-bit does not
  imply the summands are — it is a strictly weaker statement, so it does not replace the
  individual checks; and certifying the sum itself is a single range check, subject to the
  same bound.
* **Higher-degree witnesses / non-boolean rows in general.** These are exactly what the
  lower bound of §3 quantifies over, and at `n = 2` they buy nothing.

## 7. File map

| file | contents |
|---|---|
| `Model.lean` | affine forms, rows, systems, score, `Certifies` |
| `Construction.lean` | the score-`2n - 1` system and its correctness, both directions |
| `LowerBound.lean` | `one_row_dichotomy`, `zero_witness_dichotomy`, supporting field lemmas |
| `OneWitness.lean` | `quad_family_dichotomy`, `one_witness_dichotomy` (one witness ⇒ at most two bits) |
| `Optimality.lean` | `score_ge_three`, `alloc_ge_two`, `score_ge_four`, `least_score_two_bits`, `row_coAtMostOne_of_certifies` |
| `Conic.lean` | the bit-free score-`3` two-bit certifier |
| `RangeFloor.lean` | the headline statements (`range_check_below_two_n`, `range_check_floor`, `range_check_floor_three_bits`) |

All results are `sorry`-free and depend only on `propext`, `Classical.choice`, `Quot.sound`.
