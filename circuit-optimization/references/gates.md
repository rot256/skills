# Designing a Bespoke Relation (Custom Gates, sub-AIRs, Precompiles)

*When to add one, what it costs before it is used once, how they are actually invented, and when the answer is "no gate".*

A **bespoke relation** is a constraint you add to the *system* rather than to a circuit: a PLONKish custom gate, an AIR sub-AIR or chip, a precompile, a flavor extension.
The economics are the same in all of them and differ from ordinary circuit golfing in one respect:

> **A bespoke relation is never priced per use. Every component of its cost is charged once against the whole system.**
> "It makes this gadget 3x smaller" is not, by itself, an argument.

Arithmetization-specific pricing lives in `plonkish.md` and `air.md`; degree alone lives in `degree.md`; the moves you should exhaust *before* proposing a relation are in `techniques.md`.

## The Axioms

**The activation is a committed column, and it is committed everywhere.** In a gate-based system that is a preprocessed selector -- fixed at build time, in the verification key, opened alongside everything else, so the prover neither chooses it nor skips it; rows that do not use the gate still commit to it being zero.
In a multi-AIR machine the analogue is coarser and more expensive: a new chip is a whole trace with its own padding, its own interaction columns and its own entry in every verification key and every shape (`air.md` "Chip Clusters and the Shape Catalogue").
Either way the charge lands on circuits that never invoke the relation.

**Degree is a step function, and the system pays the max.** One relation sets the budget for every other relation in the system.
What it costs is a jump to the next bracket, not a proportional charge (`degree.md` "The Bracket Theorem").

**The circuit-wide maxima are the tax nobody sees.** Several quantities are a `max` over all relation types present, not a sum: the shared constraint-vector width, the constants-per-row count, the challenge-power allocation.
One relation used once sets them for everyone.
None of them show up in a gate count.

**At most one relation is active per row -- that is what makes both maxima and multiplexing possible.** Mutual exclusivity is why the costs above are maxima rather than sums, and it is exactly the property a multiplex consumes.
Spend it knowingly.

**The break-even is a padding question, not an arithmetic one.** Row savings only matter when they cross a power of two.
See I.7.

# What a Bespoke Relation Actually Costs

## The Marginal Selector
Marginal price of one additional selector, by backend shape:

| backend shape | where the selector lives | marginal price of one more |
|---|---|---|
| KZG PLONKish | a fixed column (after selector compression) | 1 scalar evaluation in the proof |
| commitment-per-gate-type PLONKish | one commitment per gate type in the verification key | 1 group element in the VK, 1 transcript absorb, 1 verifier scalar-mul |
| FRI PLONKish | one column of the preprocessed oracle | 1 extension eval at $\zeta$ + 1 base element in **every** query leaf |
| sumcheck PLONKish | one precomputed entity | +1 field element in the sumcheck evaluations, +1 VK point, +1 verifier scalar-mul |
| AIR | a preprocessed column, or an entire extra AIR | 1 preprocessed column x padded height, or a whole trace + its interaction columns |

**Measured.** With a rate of $2^{-3}$, 28 FRI query rounds and a 64-bit field, one extra selector column costs $28 \times 8 = 224$ bytes of query openings plus a 16-byte opening at $\zeta$: **about 240 bytes of proof, permanently, per selector**, before any degree effect.
In a sumcheck backend the same selector is **32 bytes**.

Production gate sets are small, and that is the budget you are asking to extend: one widely deployed flavor has 28 preprocessed entities of which **14 are selectors** (the rest are permutation sigmas, identity polynomials, Lagranges and lookup tables); its extended sibling has 43 entities and **20 selectors**.

> **Where it stops.** Two ways.
> (i) The *runtime* price of an inactive selector can be near zero -- a relation that returns early when its selector is
> zero, plus lazy materialization of the row's entities, means columns no active relation reads are never touched. The
> **fixed** prices (VK size, proof size, verifier scalar-mul) survive that optimization entirely. Never reason about
> selector cost from prover wall-clock alone.
> (ii) In a system with an on-chain or cross-language verifier, the entity *ordering* is load-bearing: adding a selector
> is a migration across every reimplementation of the verifier, not a code change.

## The Degree Step Function
Degree never costs "a bit more" (`degree.md` "What a Unit of Degree Costs").
Three concrete shapes:

- **KZG PLONKish.** The extended domain grows until $2^{\text{ext}} \ge n(D-1)$.
  Degree 9 gives an $8n$ extended domain; degree 10 gives $16n$.
  **The whole quotient FFT pipeline doubles for one degree.**
- **FRI AIR.** $\lceil\log_2(D-1)\rceil$ quotient chunks, and $D \le 2^b + 1$ is *asserted*: degree is bought with FRI blowup, i.e. with the entire LDE of every column of every chip.
  It also caps trace height.
- **Sumcheck.** Each round ships $D+1$ scalars, and the round count is often a padded constant.
  With 25 rounds and a 32-byte field, **one unit of degree = 800 bytes of proof, forever, for every circuit in the system.**

**The 25:1 rule.** In that last setting a selector costs 32 bytes and a degree costs 800.
**In a sumcheck backend, always spend a selector or a column to avoid a degree.** In a quotient backend the ratio is even more lopsided *at a bracket boundary* and exactly zero *inside* one -- which is why "The Degree Step Function" and `degree.md` "The Bracket Theorem" must be answered together.

A revealing artifact: in one deployed flavor every subrelation is capped at degree 5, with a single exception -- the $x^5$ S-box of a hash relation, which alone sets the system-wide maximum and taxes 800 bytes onto every proof.
Whether that is worth it is an empirical question about hash volume.
"The Break-Even, Worked" is how you answer it.

> **Where it stops.** Some systems do not price degree at all, they *reject* it: a hard
> `assert!(max_constraint_degree <= 3)` at construction, a panic naming the quotient factor, a debug-assert that the AIR
> degree exceeds `blowup + 1`. In those systems the answer to "can I have one more degree" is no, and the only move is
> "Trading Degree for Width"'s degree-for-width trade.

## Routed and Unrouted Wires
Every gate-based system splits its width into cells the permutation can reach and cells it cannot.
Only routed cells receive values from elsewhere; unrouted ("advice") cells must be produced *and* consumed inside the relation.

Representative ratios: 135 total wires with **80 routed**; 15 columns with the **first 7** copyable; 4 wires all routed but with the next row available as a shift; per-column opt-in where each equality-enabled column costs a sigma and a permutation-chunk slot.

**An extra routed column is not one column.** Where the permutation product is chunked at $\lceil P/(D-2)\rceil$ (`degree.md` "The $D-2$ Law"), the marginal routed column can be the one that opens a new chunk -- one more commitment plus its openings.
Note the coupling: raising the degree *reduces* the chunk count.

Unrouted width is why a hash gate can occupy 135 wires without requiring 135 permutation columns.

> **Where it stops.** A relation designed around unrouted advice cannot have those values read by anything else. If a
> later revision needs the intermediate, you pay a redesign, not a routing change. The hedge is a companion row whose
> first cells *are* routable ("Two-Row Relation Shapes").

## The Selector-Group Tax
Where gates are bin-packed into selector *groups*, the packing invariant is
$$|G| + \max_{g\in G}\deg(g) \;\le\; \text{cap}$$
and the filter that zeroes a gate outside its own rows is a **product over the rest of the group**, so **effective degree = gate degree + $|G| - 1$**, plus one more if there is more than one selector polynomial.

Three charges from one relation:

1. **A high-degree gate shrinks its own group.** A degree-7 gate at cap 9 leaves room for one group-mate.
   Every other gate landing there is a wasted slot.
2. **There is a cliff at the first extra selector.** The fast path applies while $\max\deg + n_{\text{gates}} - 1 \le \text{cap}$, giving one selector polynomial. Crossing it costs a second selector column **and** $+1$ filter degree on *every gate in the circuit*, which shrinks every group's capacity, which can cascade into a third.
   **The selector price is super-linear near the cliff, not additive.**
3. **Overshooting is fatal, not expensive** -- the builder panics.

> **Where it stops.** The packing is greedy over a degree-sorted list, so it is neither optimal nor hintable: two
> low-degree gates cannot be forced into a group with a spare slot if the sort puts a mid-degree gate between them. Your
> only lever is each gate's own declared degree -- which is why "The Degree-for-Wires Dial"'s "re-minimize the degree after fixing the wire
> count" is worth the effort.

## The Circuit-Wide Maxima

Quantities that are a `max` over all relation types present, not a sum:

- **Shared constraint-vector width.** Every gate writes into one shared vector and constraint $i$ of every gate is summed into slot $i$.
  The vector -- and the challenge-power reduction over it, at every evaluation point -- is as wide as your fattest relation.
- **Constants per row**, capped (often at 2) and asserted.
  A relation wanting a third constant is not expensive; it is rejected.
- **Challenge-power allocation**, sized by the largest single relation, explicitly because gates are mutually exclusive.
  That is ~21 powers instead of the ~128 you would get by summing every relation's constraint count.
- **Maximum subrelation length** in a sumcheck system -- the degree tax of I.2.
  Note the *number* of subrelations is a **sum**, and it sizes the accumulator every active row carries.

**Worked.** A Poseidon gate at sponge width 12 with 8 full and 22 partial rounds has $12\cdot 7 + 22 + 12 + 1 = 119$ constraints.
A 4-bit random-access gate with 2 copies has $2(4+2) = 12$.
Adding **one** Poseidon row to a circuit whose next-largest relation has ~21 constraints widens the per-point constraint vector from 21 to 119: **5.7x more terms**, at every evaluation point, on every row.

> **Where it stops.** Challenge-power reuse requires *genuine* mutual exclusivity. The moment two relations can be active
> on the same row -- which is exactly what a bitpattern multiplex ("Selectors Without New Columns") creates under one master selector -- you need
> distinct powers for the overlapping identities, or a proof of bitpattern disjointness.
> And none of these maxima appear in any gate count or cost report. The only way to see them is to diff the circuit's
> common data before and after.

## Selector Compression
Where the frontend compresses selectors automatically, $\ell$ mutually row-disjoint selectors share one fixed column with member $k$ recovered as
$$s_k \;\mapsto\; q\prod_{1\le h\le \ell,\ h\ne k}(h - q),$$
so **combining $\ell$ selectors adds $\ell - 1$ to the degree of every gate in that combination**, subject to $\max_i(d_i - 1) + \ell \le D$.

The discipline it requires: *every polynomial constraint involving a compressible selector $s$ must have the form $s\cdot t = 0$ with $t$ free of compressible selectors*.
Multiply two together, or put one inside a lookup input, and it must become an uncompressible selector -- one private fixed column, no sharing.

> **Where it stops.** Three ways.
> (i) Whether two selectors combine depends on where the layout engine actually placed the regions, and layout engines do
> not optimize for it. Combination quality is not under your control.
> (ii) A relation whose activation must gate a lookup cannot use a compressible selector at all.
> (iii) **Hand-rolled fixed columns cannot join the automatic combining.** Manual selector packing is usually
> counterproductive for exactly this reason.

## The Break-Even, Worked

> **A bespoke relation pays for its selector when the rows it removes exceed the circuit height divided by the number of
> committed-and-opened columns -- and, in every power-of-two-padded system, only when that removal actually shrinks the
> padded height.**

**(a) Prover time, sumcheck backend.** Sumcheck and the folding step are both linear in $(\text{entities}) \times N$.
One more selector takes 41 entities to 42; removing $\Delta$ rows takes $N$ to $N-\Delta$.
Net win iff
$$42(N-\Delta) < 41N \iff \Delta > N/42.$$
At $N = 2^{19} = 524{,}288$ that is $\Delta > 12{,}483$ rows.
A gadget saving 3 rows per use needs **~4,161 uses in the same circuit** before the gate pays for itself; at 1 row per use, ~12,483.

**(b) Proof size, same backend.** $+1$ selector is $+32$ bytes and it is **never recovered** -- row savings do not shrink a proof whose round count is a padded constant.
On proof size a new selector is a pure permanent loss, bought back only in gas and prover time.
For comparison, the 800 bytes that *one degree* costs ("The Degree Step Function") would buy 25 selectors.

**(c) The padding cliff, which usually dominates.** $N$ is padded to a power of two, so saving 12,484 rows out of 524,288 changes nothing unless the total crosses $2^{18}$.
The real break-even is not $\Delta > N/42$ but *does this take the circuit under the next power of two* -- a binary question with an $\approx N/2$ answer.
**That is why new selectors are justified by whole workloads (all hashing, all RAM, all bigfield arithmetic), never by gadgets.**

**(d) Cross-check, FRI backend.** $+1$ selector is one more preprocessed polynomial: one extension opening at $\zeta$ (16 B) plus one base element in each of 28 query leaves (224 B) ~ **240 B**.
And if it is the selector that takes the group count from 1 to 2, every gate's filter gains a degree ("The Selector-Group Tax"), which can force another split and another 240 B.

**(e) The instrument.** Measure, do not estimate.
A cost model that counts fixed queries, vanishing commitments, permutation chunks and point sets gives you every term in "The Marginal Selector"--"Routed and Unrouted Wires" before and after.
If your toolchain ships one, run it; if it does not, count the same four things by hand.

# Getting the Relation Without Paying for It

## The Four Prepaid Resources
Before proposing anything, exhaust the four resources already paid for.

1. **Idle degree.** If the cap is 9 and your identity is degree 4, five degrees are sitting there.
   Designs that target a cap of 9 *"to handle constraining carries and small pieces to a range of up to $\{0..7\}$ in one row"* are spending the existing budget rather than raising it (`degree.md` "Spending the Free Headroom").
2. **Unrouted wires.** 55 of 135 wires outside the permutation, or 8 of 15.
   A wider layout inside an *existing* relation costs nothing new ("Routed and Unrouted Wires").
3. **Existing selectors, as a bitpattern.** "Selectors Without New Columns" form A -- zero new columns.
4. **An existing table.** One spread/interleave table can serve range checks *and* bitwise ops *and* interpolation inputs, so a separate range table is unnecessary.

> **Where it stops.** All four are exhaustible and three are **global**: spending idle degree, unrouted width or an
> existing table takes that resource from every other gadget in the system. Record what you spent -- the second gadget to
> reach for the same slack will find it gone, and whoever writes it will not know why.

## Two-Row Relation Shapes
Most gate-based systems give one rotation nearly free, and AIRs give the next row outright (`air.md` "The Next Row as Copy Constraint").
Lay the relation out so the value a constraint needs "afterwards" *is* the next row's cell, and the copy disappears.
Three real shapes:

- **Gate plus a companion row.** A variable-base scalar-multiplication gate occupying a main row and a following all-zero-typed row uses 15 + 12 cells for 5 scalar bits, and the companion row's first cells are still routable, so the overflow stays copyable.
- **Chaining where the terminator is a degenerate instance.** A 16-bit XOR gate constrained as $\text{in} = \sum_j \text{in}_j 2^{4j} + 2^{16}\,\text{in}'$ chains four rows into a 64-bit XOR, and *one gate whose next-row values are all zero* is exactly the assertion that the originals were 16-bit.
  **The range check falls out of the recursion base case at zero cost.**
- **Head / body / tail selectors over one identity.** Write the loop body once as a closure and instantiate it under three selectors -- initialize, body, last row -- differing only in which expression is passed in.

> **Where it stops.** A two-row relation halves the effective row budget for that gadget and constrains the layout
> engine; the companion row cannot host an unrelated gate. Three selectors over one identity is three combination slots,
> and because they fire on *adjacent* rows they combine poorly ("Selector Compression").
> And some frontends expose no rotation at all -- every relation is single-row by construction. That is why their gates
> are *wide* rather than *tall*. Do not port a two-row design into one; port the packing idea instead.

## The Degree-for-Wires Dial
The general dial: a relation that computes a degree-$N$ object inline can instead introduce non-routed intermediates and run at a bounded degree $\ge 2$.
The move worth stealing is the *second* step: after fixing the intermediate count, go back and **re-minimize the degree** as far as the same wire count permits, purely so the relation joins a bigger selector group ("The Selector-Group Tax").

```
n_intermediates = (n_points - 2) / (max_degree - 1);
degree          = (n_points - 2) / (n_intermediates + 1) + 2;   // <- the second step
```

**Worked.** 16 points at cap 8: 2 intermediates, then $14/3 + 2 = 6$.
The relation lands at **degree 6, not 8** -- two degrees handed back at zero wire cost, buying two more slots in its group.
At cap 2 it would need 14 intermediates, i.e. 48 extra wires per row.

## Small-Integer Selector Multiplexing
Instead of $k$ boolean selectors, use one selector taking values $0..k$ and build each variant's indicator algebraically:

```
Sub 1: q * [ (-1/2)(q - 3)*(q_m w_1 w_2) + sum_i q_i w_i + q_c + (q - 1)*w_4_next ]
Sub 2: q(q - 1)(q - 2) * (w_1 + w_4 - w_1_next + q_m)
```

with $q = 0$ off, $1$ plain width-4 arithmetic, $2$ arithmetic plus the next row's fourth wire, $3$ a wide addition that also **repurposes the multiplication selector as an additive term**.
Four gates, one column.

**Price: degree.** Plain $q\cdot q_m w_1 w_2$ is degree 4; multiplexing four values makes it $q(q-3) q_m w_1 w_2$, degree 5.
**Multiplexing $k$ values costs up to $k-2$ extra degree** on the terms that must be switched off -- the same algebra as the $+(\ell-1)$ of I.6.
The hard limit follows immediately: a degree-3 consistency identity under a cap of 5 admits **at most two selectors** in front of it.

> **Where it stops.** All variants must **share the row shape** -- same wires read, same coefficient selectors, with only
> scalars differing. A variant needing a fifth wire cannot join. See "De-Multiplexing" for what to do then.

## Selectors Without New Columns
**Form A -- bitpattern over selectors you already have.** Under one master selector, encode the sub-type in the *existing* arithmetic selectors.
Six memory-gate types in one relation:

| gate type | `q_mem` | `q_1` | `q_2` | `q_3` | `q_4` | `q_m` | `q_c` |
|---|---|---|---|---|---|---|---|
| RAM/ROM access | 1 | 1 | 0 | 0 | 0 | 1 | access type |
| RAM timestamp check | 1 | 1 | 0 | 0 | 1 | 0 | 0 |
| ROM consistency check | 1 | 1 | 1 | 0 | 0 | 0 | 0 |
| RAM consistency check | 1 | 0 | 0 | 1 | 0 | 0 | 0 |
| ROM table entry | 1 | 0 | 1 | 0 | 0 | 0 | 0 |
| ROM read access | 1 | 0 | 0 | 0 | 1 | 0 | 0 |

The same trick gives five non-native-field variants from $\{q_{\text{nnf}}, q_2, q_3, q_4, q_m\}$.
The elliptic relation goes further and **repurposes the multiplication selector as an is-double flag**, scaling the addition subrelations by $q_e(1 - q_{\text{dbl}})$ and the doubling ones by $q_e q_{\text{dbl}}$.

**Form B -- one multi-valued fixed column.** Where four logical selectors are needed, allocate three columns and derive two from a single $q \in \{0,1,2\}$:
$$q_{S3} = q(q-1), \qquad q_{\text{run}} = q - q_{S3}$$
giving $(0,0,0)$, $(1,0,1)$, $(2,2,0)$: one column encoding *continue the running sum* / *end of element* / *end of hash*.

**Price.** Form A: zero new columns, zero VK entries, zero proof scalars -- you pay only degree, one per selector that must appear in the product, which is why good patterns need at most two.
Form B: the derived selector is degree 2 where a plain one is degree 1.

> **Where it stops.** Form A requires the bitpatterns to be **globally non-overlapping** across every gate under the
> master selector, and that is maintained *by hand, as a comment* -- adding a seventh type means re-verifying all
> $\binom{7}{2}$ disjointness claims.
> Form B is manual combining, the thing "Selector Compression" warns against: the column can never join an automatic combination. It is
> worth it only when the values are *semantically meaningful*, so the column carries information the constraints need
> anyway. For arbitrary labels, a compressible selector plus the compressor does better.

## De-Multiplexing
Splitting one multiplexed selector into two costs one entity -- 32 bytes of proof, one VK point, one verifier scalar-mul -- and buys degree headroom plus skip granularity.
It is the right move when the shared row shape stops being shared: one deployed system split a single auxiliary selector covering RAM/ROM *and* non-native field into two relations, and split a five-way hash multiplex where its predecessor had two.

**Multiplex when the variants share wires and the shared identity fits the degree cap; split when either premise fails.** Some systems never multiplex at the value level at all, because their gate layouts genuinely differ per type.

# Relation or Lookup

## The Table-Amortization Crossover
A table occupies rows.
Widening from $b$ to $2b$ bits halves the lookups per operation but *squares* the table height.
The crossover is a straight line in operation count:
$$n_{\text{break-even}} \;=\; \frac{\text{rows}(T_{\text{wide}}) - \text{rows}(T_{\text{narrow}})}{\text{rows saved per operation}}.$$

**Worked.** A 4-bit XOR table is $16\times16 = 256$ rows; an 8-bit table is $256\times256 = 65{,}536$; the difference is $65{,}280$.
A 64-bit XOR takes 4 rows at 4-bit granularity versus 2 at 8-bit, saving 2 rows per operation.
So $n \approx 65{,}280/2 = 32{,}640$ 64-bit XORs -- at roughly 3,600 lane-XORs per Keccak permutation, about **9 permutations**.
Below that, the narrow table wins outright.

The knob is worth exposing: a table parameterized by `TABLE_BITS` with base $B$ has $B^{\text{bits}}$ rows and $\lceil 64/\text{bits}\rceil$ lookups per 64-bit lane, and the right value is workload-dependent.

> **Where it stops.** The table sets a **floor** on circuit height that no amortization removes. A chip requiring a
> minimum of $2^{16}$ rows makes a circuit that would otherwise be $2^{12}$ sixteen times taller no matter how many
> operations you do. **Check the floor before the crossover.**

## Log-Derivative Against Sorted Copy
A consistency argument needing an auxiliary sorted copy of the trace costs two rows per access; a log-derivative argument costs one row per *table entry* plus one per *read*.
When reads outnumber entries, the sorted scheme loses -- it roughly doubles the trace footprint of single-value reads.

Note what this is **not**: it is not removing the relation.
Both arguments can live in the *same* relation under the *same* master selector, distinguished by bitpattern ("Selectors Without New Columns"), with the choice made per data structure on first use.

**Price of the log-derivative side:** an inverse-helper wire, a multiplicity column on table rows, one extra Fiat-Shamir challenge, and one **linearly dependent** subrelation that must not be scaled by the row separator.

> **Where it stops.** The two schemes cannot mix inside one array, and pair-valued tables often stay on the sorted
> argument because two values per index change the fingerprint arithmetic. **The crossover is per data structure, not per
> system.**

## Unmaterialized Structured Tables
"The Table-Amortization Crossover"--"Log-Derivative Against Sorted Copy" assume the table occupies committed rows.
In a sumcheck backend with a structured-table argument it does not: the "table" is the full set of $2^n$ evaluations of the operation, and it is never written down.
All the verifier needs is that the table's multilinear extension be *quickly evaluable*; the prover exploits prefix-suffix structure to compute its round messages, but that decomposition is used only in the prover's own head and is not part of the protocol.

**The cost model changes from table height to MLE-evaluation cost plus decomposability.** A $2^{128}$ table becomes admissible; a $2^{16}$ table with an unstructured MLE may not be.

> **Where it stops.** It requires a sumcheck/multilinear backend, an operation with a quickly evaluable MLE, and one-hot
> addressing, which costs several committed sub-vectors per access. Ported naively into a quotient/plookup system it is
> strictly worse. When someone says "everything should be a lookup", the load-bearing words are *which lookup argument*.

# How Relations Are Actually Invented

## Substituting Out Intermediates
The single most productive move.
Take the naive constraint program, find every witness that exists *only* to be consumed by the next line, and inline its definition.

**Case 1 -- eliminate a coordinate.** An elliptic accumulator with $\lambda_1(x_A - x_P) = y_A - y_P$, $x_R = \lambda_1^2 - x_A - x_P$ and $(\lambda_1+\lambda_2)(x_A - x_R) = 2y_A$ becomes, after substituting $x_R$ then $y_A$, a relation over $\{x_A, x_P, y_P, \lambda_1, \lambda_2\}$ alone.
In code $Y_A$ is a *function returning an expression*, not a column -- **one materialized $y$ in the entire scalar-multiplication loop**.

**Case 2 -- never compute the intermediate at all.** Defining $r_x = s_1^2 - x_i - x_t$, $t = x_i - r_x$, $u = 2y_i - t s_1$ and $s_2 = u/t$ makes $s_2$ and $r_x$ appear only in ratios that clear, doing the step in 1 multiplication, 2 squarings and 2 divisions instead of 2, 3 and 2.

**Case 3 -- substitute a known *invariant*, not a definition.** Replacing $x_1^3$ by $y_1^2 - b$ via the curve equation turns a cubic doubling constraint into $(x_3 + 2x_1)\cdot 4y_1^2 - 9x_1(y_1^2 - b) = 0$ -- a quadratic.

**Price: degree, paid at every occurrence.** An eliminated degree-3 expression makes every constraint that mentioned it degree 3, and degree 4 once gated.
**Each column you delete typically costs 1--2 degree on every constraint that used it** -- exactly the trade "The Degree Step Function" says to take in a sumcheck backend and to check against the bracket in a quotient backend.

> **Where it stops.** Substituting an *invariant* introduces an assumption that is not locally checked: the doubling
> relation above is unsound for a point not proven on the curve, so user-supplied witness points need an explicit
> on-curve constraint. And an eliminated intermediate is an unroutable one -- any future gadget needing it must
> re-derive it, which is why such designs witness the value explicitly in one boundary row so it can leave the region.

## Lowest-Degree Equivalent Identity
Five techniques, in increasing sophistication:

1. **Roots product for small sets.** One constraint with a root at each permitted value: $a(1-a)(2-a)(3-a)(4-a) = 0$ for $a \in [0,5)$, or $(7-c)(13-c) = 0$ for $c \in \{7,13\}$.
   Degree = $|{\rm set}|$.
   A delta-range gate is exactly this at scale: $\sum_i D_i(D_i-1)(D_i-2)(D_i-3)$ over four successive differences, checking four values per row at degree 4.
2. **Lagrange interpolation from a truth table.** For a small map $f:\{x_i\}\to\{y_i\}$, $\sum_j f(x_j)\ell_j(X) - f(X)$, degree $k-1$.
   Used to compute 2- and 3-bit spreads *in parallel with* the lookups they would otherwise need, which is why a 9-bit piece gets split $3\times3$ rather than interpolated.
3. **Change the representation so the function becomes linear.** Computing $A \oplus (\neg B \wedge C)$ as the **linear** expression $2A - B + C + Q$ in a base-11 sparse form, with the lookup used only to *normalize* the 5-valued output back to binary.
   All the nonlinearity moves into the table.
4. **Express the operation as division with remainder.** A rotation as $w\cdot 2^r = e\cdot 2^{64} + s$ with $\text{rot} = s + e$: degree 1 in the witnesses, with $2^r$ supplied as a *coefficient*, so one relation serves every rotation amount.
5. **Merge disjoint cases with a free witness.** Four 130-bit range checks in two mutually exclusive pairs collapse into two, by introducing a witness $u$ defined differently in each case and left *unconstrained* in the case where neither applies.
   Four range checks become two, two gating selectors become one, cost is one advice cell.

**Price.** Each trades one resource for another: roots products spend degree; interpolation spends degree and constants; representation changes spend a table and wires; division-with-remainder spends range checks; the free witness spends a cell.

> **Where it stops -- and this is where unsound gates come from.** The *soundness* of a low-degree identity is not
> implied by its truth table on the intended domain. In technique 5 the merged constraint must be **vacuous**, not merely
> satisfiable, in the leftover case, or the free witness becomes a free forgery. In technique 4 the first published
> version was unsound for exactly this reason ("The Design-Search Log"). Matching on the intended inputs is necessary, not sufficient:
> verify with an SMT solver over the real prime (`smt.md`) or a Groebner cofactor certificate (`sage.md`).

## The Design-Search Log
Relation design is search, and the search record is the most useful artifact.
One published design log for a rotation gate lists six candidates and why each failed:

- four gate types (rotate by 1, 2, 3, and by a multiple of 4) -- **rejected on rows**: one rotation took 6 rows plus generic gates for the decomposition weights.
- decomposition into top and bottom parts -- one gate, one row, but **rejected on a missing range check**: no way to constrain the lengths of each side.
- coefficient flags turning limbs and crumbs on and off -- **rejected on degree**: *"blown up, like 12 or more"*.
- a swap option with XORs -- **rejected on the lookups-per-row budget**.
- the winner came from **transplanting an unrelated gate's trick**: express the word as a quotient and remainder, $w\cdot 2^r = e\cdot 2^{64} + s$ ("Lowest-Degree Equivalent Identity", technique 4).
- then: *"the previous approach was very efficient but not sound"* -- a malicious prover could pick $e$ and $s$ summing to a 64-bit word that is the wrong one.
  The fix is range-constraining $e < 2^r$ and $s < 2^{64}$.

**Price.** The shipped relation is 3 rows, not 1.
**The soundness fix cost two thirds of the win, and that is the normal outcome, not a failure of the process.**

> **Where it stops.** Every rejection above is against a *stated budget* -- rows, degree, lookups per row, coefficient
> count. Without a budget the search has no termination condition and you will ship the first thing that works.
> Establish the scarce metric first.

## Automatable Passes
Four of the moves above already exist as compiler passes, and knowing which are automatable tells you where to spend attention.

- **Substitution under a degree budget ("Substituting Out Intermediates"), automated.** A solver that finds variables a constraint determines, substitutes them everywhere, deletes the defining constraint and iterates to a fixpoint -- refusing any substitution that would exceed a declared bound.
  That is the coordinate elimination of "Substituting Out Intermediates" done by machine, with the bound made explicit.
  Companion passes: range-constraint elimination, memory forwarding, low-degree bus-interaction fusion.
- **Whole-relation synthesis.** Generating a workload-specific relation from a hot basic block, with profile-guided selection of which blocks to promote.
- **Selector packing ("Selector Compression"), automated.** An exclusion matrix plus greedy combination, running with no user input.
- **Degree accounting ("The Degree Step Function"), automated.** Symbolic evaluation infers the true degree and only *checks* the author's declared hint; the strict version turns the same machinery into a hard assertion.
- **Soundness of the synthesized identity.** Not automated anywhere.
  That is the part you do by hand, with `scripts/synthesize.sage`, `scripts/verify.smt2` and `scripts/cofactors.sage`.

> **Where it stops.** None of these invent the *identity*; they optimize a program you wrote. The representation changes
> of "Lowest-Degree Equivalent Identity" (sparse base-$B$ form, division-with-remainder) lie outside every one of these search spaces.
> **Automation is for the last 30%.**

# When the Answer Is "No Relation"

## Optionality and the Exit Budget
The maxima of "The Circuit-Wide Maxima" and the selector counts of "The Marginal Selector" are paid only if the relation is *present*, so mature systems keep unused relations out of circuits that do not need them:

- **Feature-flagged expressions**: each optional relation wrapped as *if feature then expr else zero*, with the verification key holding an `Option` per optional selector.
  A circuit with no XOR carries no XOR selector commitment and no XOR term in the linearization.
- **A config knob rather than an answer**: "use a dedicated gate for base-field arithmetic, rather than one gate for both base and extension field" exposed as a build option -- the question *is a second gate worth a selector slot* left to the caller.
- **Compile-time flavor bits** (`HasMemory`, `HasNonNativeField`, `HasElliptic`, ...), plus separate flavors so circuits with different needs do not pay for each other's selectors.
  Challenges for absent relations are skipped entirely, keeping prover and verifier in lockstep on the transcript.
- **Deletion.** A gate set that outlives its caller is pure cost.
  One project deleted an entire cipher gate family with the note that removing it also meant *"less work to do for verification of custom gates in wrap proofs"* -- because in a composed system every gate type is re-verified in the wrapping circuit, so an unused gate costs rows forever.

**Price.** Optionality multiplies the VK space and the test matrix: every flag combination is a distinct verification key, a distinct verifier circuit and a distinct transcript schedule.

> **Where it stops.** Optionality does not help where all circuits must share one shape -- a fixed configuration exists
> precisely so that a uniform verifier can exist, and there every relation you add is added for everyone.
> And in a shipped system with an independently-implemented verifier the *removal* cost can exceed the carrying cost:
> generated on-chain verifiers keep carrying a selector long after the reference implementation split it.
> **Budget the exit when you propose the entry.**

## Trading Degree for Width
Where the cap is enforced rather than priced ("The Degree Step Function"), the correct response is a width trade, and it is usually already a compile-time parameter.
For an S-box parameterized by (degree, registers):

| (degree, registers) | encoding | effective degree | extra columns per S-box |
|---|---|---|---|
| (5, 0) | $x^5$ | 5 | 0 |
| (5, 1) | commit $x^3$, assert $x^3 = x^2\cdot x$, output $x^3 x^2$ | 3 | 1 |
| (7, 0) | $x^7$ | 7 | 0 |
| (7, 1) | commit $x^3$, assert $x^3 = x\cdot x\cdot x$, output $(x^3)^2 x$ | 3 | 1 |
| (11, 2) | commit $x^3, x^9$ | 3 | 2 |

with the selection made at system-configuration time, not per circuit.
The worked break-even -- 141 columns against 4 quotient chunks, and why the whole-machine blowup term decides it -- is `degree.md` "Poseidon2 S-Box Register Break-Even".

> **Where it stops.** The trade is only available when the high-degree term is a *chain* you can cut. A degree-$k$
> roots-product range check ("Lowest-Degree Equivalent Identity", technique 1) has no natural midpoint: splitting it introduces $k/2$ committed
> intermediates rather than 1.

# The Decision Procedure

1. **State the scarce metric and get a baseline.** Proof size, prover time, rows, VK size -- they disagree.
   Record the circuit-wide maxima of "The Circuit-Wide Maxima" too; they will not appear in any gate count.
2. **Write the naive constraint program.** Do not optimize yet.
3. **Substitute out every intermediate** whose only consumer is the next constraint ("Substituting Out Intermediates"), recording the degree each substitution costs.
4. **Rewrite the identity** for minimum degree at fixed truth table ("Lowest-Degree Equivalent Identity"): roots product, Lagrange, representation change, division-with-remainder, free-witness case merge.
5. **Fit the row shape** to the free rotation or the next row ("Two-Row Relation Shapes").
6. **Check the degree against the bracket** ("The Degree Step Function", `degree.md` "The Bracket Theorem").
   If it does not fit, trade degree for width ("Trading Degree for Width") before trading anything else.
7. **Try, in order:** idle degree -> unrouted wires -> bitpattern over existing selectors ("Selectors Without New Columns") -> small-integer multiplex ("Small-Integer Selector Multiplexing") -> a lookup into an existing table ("The Table-Amortization Crossover"--"Log-Derivative Against Sorted Copy") -> a new selector ("The Break-Even, Worked").
   **Stop at the first that works.**
8. **Compute the break-even** ("The Break-Even, Worked") with your real $N$ and real use counts.
   If the answer needs thousands of uses in one circuit, the answer is no.
9. **Verify soundness independently** -- SMT over the real prime, or a Groebner cofactor certificate.
   "The Design-Search Log" is what happens when this step is skipped: an efficient, unsound relation.
10. **Budget the exit** ("Optionality and the Exit Budget"), and make it optional if the system allows it.

> **The one-line version.** A bespoke relation is a permanent, system-wide charge bought with a per-circuit saving, so
> the only relations that pay are the ones that serve a whole workload -- and the cheapest new relation is the one you
> encode in selectors, wires and degree you have already bought.
