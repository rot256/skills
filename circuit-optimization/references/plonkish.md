# PLONKish Optimization

*A field manual for gate-based constraint systems.*

Rows x columns, custom gates, selectors, copy constraints, lookups.
Every entry carries the mechanism, the price, and the condition under which it stops working.
The trace-based (AIR/STARK) cost model is `air.md`; constraint degree is `degree.md`; **the decision to add a gate type at all -- selector economics, multiplexing, break-even, how gates are invented -- is `gates.md`**; R1CS is `r1cs.md`; cross-arithmetization moves are `techniques.md`.

$$\text{cost} \;=\; \text{rows} \times \text{columns} \;+\; \underbrace{\text{permutation polys}}_{\text{per equality-enabled column}} \;+\; \underbrace{\text{selector columns}}_{\text{per gate group}} \qquad\text{under a cap on gate degree}$$

## The Axioms

**A copy constraint is not free.** This is the single deepest difference from an AIR, which has no permutation over its own columns at all.
Enabling equality on a column adds it to the permutation product, costing one fixed permutation polynomial and one degree in the rule; past the degree bound the product splits across sets, each with its own grand-product column.
Everything in "Rotations Replace Copies, Which Are Not Free"--"Advice (Unrouted) Wires for Anything No Gadget Reads" is a way to avoid paying it.

**A gate is a selector, and a selector is a committed column.** Adding a bespoke gate is not free even on rows that do not use it: the selector is committed over the whole domain, it enters the degree budget, and where selectors are grouped it competes for space in a selector *group* whose size is capped by the degree.
The break-even question -- how many uses does a gate need before it pays for its selector -- is `gates.md` "The Break-Even, Worked", and the answer is usually "more than you have"; the selector-group cliff is `gates.md` "The Selector-Group Tax, and the Cliff at the Second Selector".

**Rows are filled, not consumed.** A row has a fixed width, and the builder's job is to pack independent operations into the leftover columns.
Whether a row is "used" is the wrong question; how much of its width is idle is the right one ("Gate Packing: `num_ops` Comes from the Wire Budget").

**The window is a rotation, and its reach is the first thing a design fixes.** Gate-based systems differ along a few axes -- how far a gate may see, what a gate *is*, how selectors are charged -- so name the archetypes once; every section below is a statement about one of them, not about a product:

- a **rotation-based frontend** permits any `Rotation`, but only *within a region*;
- a **two-row frontend** permits exactly `Curr`/`Next`;
- a **gate-vector frontend** makes each gate a vector of independent copies of one op over a routed-wire budget, and lets a gate see one row plus those routed wires;
- a **selector-grouped frontend** bin-packs gate types into selector groups under $|G| + \max\deg(G) \le \text{cap}$.

They compose, and the backend is a fifth axis: a **KZG-based PLONKish backend** pays the degree cap where the quotient is split, a **FRI-based** one pays it as blowup.
That difference in reach drives each frontend's entire gadget style.

**Degree is a global cap that is usually under-spent.** Same as everywhere else, and it has its own reference: only $D \in \{3,5,9,17,33\}$ are rational choices, and below the cap degree is prepaid (`degree.md`).

# The Wiring Layer

Where an AIR reads the next row for free, a PLONKish system charges you for moving a value.
These three sections are the whole of that bill.

## Rotation-Based Frontend

### Rotations Replace Copies, Which Are Not Free

The design note is worth quoting:

> *"The motivation for offset references is to reduce the number of columns needed in the configuration ... If we did not
> have offset references then we would need a column to hold each value referred to by a custom gate, and we would need to
> use equality constraints to copy values from other cells ... we also do not need equality constraints to be supported for
> all of those columns."*

The price of the alternative is concrete: enabling equality on a column adds it to the permutation product $\prod_i (v_i(X) + \beta s_i(X) + \gamma)$, so each such column costs one extra fixed permutation polynomial *and* one degree in the rule; past the degree bound the product is split across $b$ sets with a separate grand-product column each.
In a gate-vector frontend the same fact presents as a *width* budget instead: only the first `num_routed_wires` columns participate, and `num_partial_products = ceil(num_routed_wires / quotient_degree_factor) - 1`.

> **Where it stops.** Rotations reach only *within a region* in a rotation-based frontend, or exactly one row in a two-row
> or gate-vector one. Crossing a region or a chip forces a real copy. And a rotation-using gate cannot be placed on an
> arbitrary row, so it cannot fill floor-planner gaps -- only rotation-free gates can.

## Gate-Vector Frontend

### Advice (Unrouted) Wires for Anything No Gadget Reads

Columns above `num_routed_wires` are committed but do **not** join the permutation argument.
Every serious gate in such a system parks its internals there:

```rust
/// An intermediate wire where the prover gives the (purported) binary decomposition of the index.
pub(crate) const fn wire_bit(&self, i: usize, copy: usize) -> usize {
    self.num_routed_wires() + copy * self.bits + i
}
```

`ExponentiationGate`'s budget is the resulting asymmetry: $\min(\text{routed}-2, (\text{wires}-2)/2) = \min(78,66) = 66$ bits.

> **Where it stops.** Anything a *gadget* must read or reuse must be routed. That is why `RandomAccessGate` exposes the
> claimed element (routed) and hides the index bits (unrouted): the caller never needs the bits.

### Gate Packing: `num_ops` Comes from the Wire Budget

Every "small" gate is a vector of independent copies of one op, and the copy count is a pure division:

```rust
pub(crate) const fn num_ops(config: &CircuitConfig) -> usize {
    let wires_per_op = 4;
    config.num_routed_wires / wires_per_op
}
```

At 80 routed wires: **20** base MADs, **10** extension MADs, **13** extension muls, **40** lookups, **26** LUT entries per row.

The universal primitive is the fused $c_0 m_0 m_1 + c_1 a$ (degree 3), and *everything* is a rewrite into it: `mul` feeds `x` into the unused addend slot rather than a zero wire; `select(b,x,y) = b\cdot x - (b\cdot y - y)` is **2** fused ops, not 3; `or(b_1,b_2)` is 2.
**In a gate-vector frontend addition is not cheaper than multiplication** -- it burns a full degree-3 slot.

Two non-obvious consequences:
- **Rows are consumed by *constant-pair fragmentation*, not by op count.** The builder reuses partially-filled rows keyed on the gate's constant vector, so 20 different $(c_0,c_1)$ pairs used once each cost 20 rows, not one.
  That is why `add`/`sub`/`mul` all normalize to $(1,1)$, $(1,-1)$, $(1,0)$.
- **A gate that emits one generator can never share a row.** `num_ops` defaults to the generator count, so `BaseSumGate`, `ExponentiationGate`, `PoseidonGate` and `CosetInterpolationGate` always take a fresh row; `RandomAccessGate` emits one per copy and can pack.

# Selectors and the Degree Budget

## Selector-Grouped and Rotation-Based Frontends Alike

### Selector Grouping Is the Tax Nobody Expects

Gates are sorted by degree and bin-packed so that
$$|G| + \max_{g\in G}\deg(g) \;\le\; \text{quotient\_degree\_factor} + 1 = 9$$
and the filter that zeroes a gate outside its rows is a **product over the group**, so **filtered degree = gate degree + $|G|$ ($+1$ for the UNUSED term when there are several selectors)**.
One selector suffices only if $\max\deg + n_{\text{gates}} - 1 \le 9$ -- with `PoseidonGate` (degree 7) present, that permits **three gate types in the entire circuit**.
A degree-9 gate panics outright.

A rotation-based frontend's version is the mirror image: $\ell$ simple selectors on disjoint row sets pack into one fixed column at the cost of $+(\ell-1)$ degree on every constraint they select, with the packing algorithm stopping at the degree bound.
Its side condition is worth quoting: *"Every polynomial constraint involving a simple selector $s$ must be of the form $s\cdot t = 0$, where $t$ is a polynomial involving no simple selectors"* -- a selector used non-linearly must be a complex selector and is left unoptimized.
And hand-made fixed columns *"cannot take part in the automatic combining"*, so manual combining is counterproductive.

**Practical rule: prefer fewer, reusable gate types of uniform degree.** A rarely-used degree-6 gate can push a common degree-3 gate into a smaller group *and* add a selector column that every row commits to.

Two more global maxima leak the same way: `num_gate_constraints` and the constants-column count are **maxima over all gate types**, so every row is evaluated against the widest gate's constraint count.
Pack aggressively within a gate type you use a lot; keep rarely-used gates narrow.

## Gate-Vector Frontend

### Trading Degree for Wires Inside One Gate

The `CosetInterpolationGate` is an explicit dial, and the design note is worth quoting: *"A full interpolation of N values corresponds to the evaluation of a degree-N polynomial. This gate can however be configured with a bounded degree of at least 2 by introducing more non-routed wires."* The worked numbers are in `gates.md` "Trade Degree for Wires Inside the Relation, Then Hand the Degree Back".
The *second* trick in that gate is the one to steal: after fixing the intermediate count, it **re-minimizes the degree** purely so the gate joins a bigger selector group.

Other shapes worth knowing:
- `BaseSumGate<B>`: base-$B$ decomposition **and** a per-limb range check in one row, at `degree = B` and $\text{num\_limbs} = \min(\log_B(p-1), \text{routed}-1)$ = 63 bits for $B=2$ on Goldilocks.
  Degree is linear in the base.
- `ReducingGate`: 43-term Horner in one **degree-2** row, because each accumulator step is its own constraint; base-field coefficients get 1 wire while accumulators get $D$, and **the last accumulator aliases the output wires**, saving $D$.
- `RandomAccessGate`: claimed element + prover one-hot bits, $2+2^{\text{bits}}$ **routed** wires and degree $\text{bits}+1$ **per access** -- the entire list is re-materialized into routed wires on every read, so random access into a length-$n$ array is $\Theta(n)$ wires per read.
- `PoseidonMdsGate`: a linear layer as a **degree-1** gate, which can join any selector group without raising its degree -- used only `if builder.config.num_routed_wires >= mds_gate.num_wires()`.

# Gadget Catalogues, and What They Reveal About the Budget

## Rotation-Based Frontend

### The Decomposition Family

Arbitrary rotations within a region buy one thing above all: a value can be *implied* by two adjacent cells of one column instead of witnessed and copied.
The decomposition family falls out of that, trading advice columns, lookups and degree.

- **Running sum.** $z_{i+1} = (z_i - k_i)/2^K$, with the word never witnessed -- recovered as $k_i = z_i - 2^K z_{i+1}$ from two adjacent rows of the *same* column and fed directly to the lookup.
  **One advice column, $W{+}1$ rows, $W$ lookups, and exactly one copy** for a $WK$-bit range check.
  *Strict mode is what actually range-checks*: only when $z_W$ is constrained to zero is the element proven $< 2^{WK}$.
- **Shifted final chunk.** To prove $\alpha < 2^n$ with $n \le K$ on a $K$-bit table, look up $\alpha$ **and** $\alpha\cdot2^{K-n}$ -- 3 rows, 2 lookups, one degree-2 bitshift gate.
  (A two-row frontend does the same *inside* the lookup argument with a scaled joint lookup, for zero witness cells.)
- **One lookup argument serving two decompositions**, folded by a selector into a single input expression -- one argument instead of two, at the cost of degree 2 in the lookup input.
- **Lookup-free running sum**, range-checking the word by the degree-$2^K$ product instead: no table at all, but `assert!(WINDOW_NUM_BITS <= 3)`.
- **Small-set Lagrange interpolation instead of a lookup.** A SHA-256 gadget interpolates the 2- and 3-bit spreads so those pieces cost *no lookup row* -- degree = domain size, which is why a 9-bit piece is split into $3\times3$ rather than interpolated.
- **Conditional canonicity.** Prove $\alpha < p$ only *when the top bit is set*, by multiplying the whole comparison by the flag $\alpha_2$: degree $+1$, and the high 120 bits come free from an existing running sum.
- **Incomplete elliptic-curve addition, and the argument that licenses it.** The incomplete formulas are degree 4 and 3; *complete* addition is 12 constraints up to degree 6 with four `inv0` witnesses, and needs two rows because it wants 9 advice columns.
  The exceptional case is discharged not by casework but by tracking **indices**: distinct indices mod sign imply distinct $x$, and the accumulator is bounded by $2^{n+1}+2^n-1 < (q-1)/2$.
  The sage check shows that first fails at $i = 252$, so **exactly the last three iterations and the final conditional subtraction use complete addition** -- everything else is incomplete.
  A hash gadget over the same operator carries a different licence: an exceptional case would yield a discrete log.
  Two companion savings: $y_A$ is *eliminated* from the accumulator by substituting the slope equations, leaving one materialized $y$ in the whole loop; and a fixed-base gadget interpolates only the $x$-coordinate, recovering $y$ from the curve equation plus a per-window constant $z_w$ chosen so that $z_w + y$ is a square and $z_w - y$ is not.
  *Stops:* the bound is the whole proof.
  Change the scalar width, the curve, or the accumulator's starting point and the index at which incompleteness becomes unsound moves with it.

## Two-Row Frontend

### Designing to a Hard Wire Budget

The opposite discipline: fix the budget, let it dictate the gadgets. 15 columns, **7 permutable**, a 2-row (`Curr`/`Next`) window, $\le 4$ lookups per row -- every design decision follows, and the design note is worth quoting:

> *"We have at most 7 copyable cells per row and gates can operate on at most 2 rows, meaning that we have an upperbound of
> at most 14 limbs per gate (or 7 limbs per row)"* $\Rightarrow \text{limbs}_{\max} = \lfloor 14/4\rfloor = 3
> \Rightarrow \ell = t/3 = 264/3 = \mathbf{88}$ bits per limb.

That is the whole derivation of the 88-bit foreign-field limb, out of a wire budget.
Other moves worth transplanting:
- **`Zero` companion rows** as pure storage, doubling the addressable cells for one selector.
- **Gate chaining through the permutation**: a gate's `Next` row *is* the next gate's `Curr` row, so the hand-off costs nothing -- but a chain must be **terminated**, which `Xor16` does with copy constraints of a row to itself (*"Warning: don't forget to check that the final row is all zeros"*).
- **Negated modulus to kill borrows.** Foreign-field multiplication uses $f' = 2^t - f$ as a public gate coefficient so no term is ever subtracted, then deletes the terms $\equiv 0 \bmod 2^t$.
- **Bisect once, not twice.** Only $p_1$ is bisected; $p_0$ spills, and the leftovers become witnessed carries $v_0, v_1$ -- *"each bisection requires constraints for the decomposition and range checks for the two halves ... we would like to avoid bisections as they are expensive."*
- **Fold the bound check into the gate that already has the value.** Folding $q' = q + f'$ into `ForeignFieldMul` saves 4 rows per multiplication (12 -> 8); the 2-limb decomposition of $q'$ saves 2 more.
  $r'$ *cannot* be folded -- *"This leaves only 2 remaining copyable cells."*
- **Lazy bound checks in a chain.** Intermediate foreign-field additions may exceed $f$; only the final result needs the $< f$ bound, taking a chain from $9n+11$ rows to $n+7$.
- **Inline a range check into a gate's spare cells**: *"Since our current row within the `Rot64` gate is almost empty, we can use it to perform the range check within the same gate."*

> **Where it stops.** The lazy-bound trick is sound only because wrapping an 88-bit limb in $\mathbb F_n$ would need
> $k \approx 2^{167}$ chained additions -- more than any admissible maximum circuit length. **The same reasoning fails for
> multiplication**: $r$ after $k$ multiplications is $\approx f^k$, and $f^k > 2^t n$ for $k>2$, so every multiplication must
> check $a,b,q,r < f$. Note also a distinction to stay careful about: $q<f$ gives *correctness*, $r<f$ gives
> *uniqueness/canonicity* -- they are different obligations.

# Non-Native Arithmetic in a Gate-Based System

Emulating a foreign field $p$ inside a native field $n$ is the same CRT/bound problem everywhere (`r1cs.md` "Bound Arithmetic", `air.md` "Non-Native and Big-Integer Arithmetic", `techniques.md` section 2).
What a gate-based system adds is a wire budget and a selector: the identity is checked by a custom gate whose modulus limbs *are* selector constants, so nearly every saving below is either a constant folded into a selector or a quotient shared across several products.
Running example: 4 limbs of $L = 68$ bits, native field with $\log n \approx 253.5$.

## The Bound Discipline: Derive Your Two Ceilings, Never Copy Them

Two inequalities decide the gate count of everything else.
Redo both for your own parameters.

**Ceiling 1 -- the whole element.** CRT needs $ab < M$; the cheapest sufficient invariant is $\max(a),\max(b) < \sqrt M$.
Since $M = 2^t n = 2^t(2^m+\ell) = 2^{t+m} + 2^t\ell > 2^{t+m}$, $\sqrt M > 2^{(t+m)/2}$; take the strictly safer $2^{\lfloor(\mathrm{msb}(M)-1)/2\rfloor}-1$.
At $t = 272$, $m = 253$: $\mathrm{msb}(M) = 525$, exponent $\lfloor524/2\rfloor = 262$, ceiling $2^{262}-1$ -- $2^{8}$ of headroom over a reduced $\sim2^{254}$.
A second constant sits an `arbitrary_secure_margin` of **20 bits** higher; crossing that aborts the build rather than emitting constraints.

**Ceiling 2 -- the single limb, which usually fires first.** The element bound does not protect the *accumulators*: $\text{hi} = c_2 + c_3 2^L$ sums **four** limb-products ($c_3 = a_3b_0+a_2b_1+a_1b_2+a_0b_3$) in $\mathbb F_n$, and overflow there destroys the mod-$2^T$ argument with no constraint failing.
With $Q$ the allowed limb width and $2^k$ the allowed number of chained additions:

$$\max\textstyle\sum\text{hi} = 2^k\bigl(3\cdot2^{2Q}\bigr) + 2^k2^L\bigl(4\cdot2^{2Q}\bigr) < 2^k(2^L{+}1)\bigl(4\cdot2^{2Q}\bigr) < n
\;\Longrightarrow\; 2Q+3 < \log n - k - L \;\Longrightarrow\; Q < \tfrac{\log n - k - L - 3}{2}$$

At $\log n = 253.5$, $L = 68$, $k = \text{MAX\_ADDITION\_LOG} = 10$: $Q = \lfloor(253.5-68-10-3)/2\rfloor = \mathbf{86}$, whence `MAX_UNREDUCED_LIMB_BITS = L + k = 78` and `PROHIBITED_LIMB_BITS = 83`, asserted $83 < 86$ at compile time.
**What the 78 buys: $2^{10} = 1024$ default-width elements added limb-wise before a reduction is forced.** Every addition doubles a limb's maximum, so from $2^{68}-1$ you get **10 free additions**; the 11th trips the check.

> **Where it stops.** The 3-bit slack between 83 and 86 is the entire safety margin -- raise $k$, raise $L$, or move to a
> native field below $\sim2^{253}$ and the assertion fires. The derivation also assumes **at most four limb-products per
> accumulator column**; widen the limb count and the constant 4 is wrong in the unsound direction.

## The Uniqueness Trap in a Lo/hi Split

Two range checks do **not** pin a decomposition.
If $\text{lo} + 2^{\text{lo\_bits}}\text{hi}$ is recombined mod $n$, then $(\text{lo},\text{hi})$ and $(\text{lo}-n_{\text{lo}}, \text{hi}+\dots)$ can both be in range.
What is missing is a *modulus* check -- a borrow comparison against $n$ itself, with $\text{hi\_diff} = n_{\text{hi}}-\text{hi}-\text{borrow}$ and $\text{lo\_diff} = (n_{\text{lo}}-1)-\text{lo}+\text{borrow}\cdot2^{\text{lo\_bits}}$ both range-constrained.
**Price:** 1 boolean $+$ 2 range constraints $+$ 1 linear identity, on top of the two range checks for `lo`/`hi` -- and *those* can be **skipped** when the halves are immediately used as lookup keys, which range-constrains them implicitly ("The Accumulator Column: Decompose, Look up and Recombine in One Column").

> **Where it stops.** Explicit precondition: *"The low `lo_bits` of `field_modulus` must be nonzero. If they are zero, the
> borrow arithmetic has undefined behaviour."* The same pattern appears open-coded in a 32-byte serialisation with a
> 128/128 split and a hand-rolled overlap bit, so audit every hand-rolled split for it, not just the library one.

> **Where this whole part stops.** Every technique above is sound *only inside a proved bound*: "Lazy Reduction: Reduce Mod $2^s$, Not Mod $p$" is licensed by
> ceiling 1 of "The Bound Discipline: Derive Your Two Ceilings, Never Copy Them", "Packing the Wires: Addition in 4 Gates, Injection in 2, Subtraction for Free" by ceiling 2, "Amortising the Quotient: N Products, One Quotient, One Pair of Carries" by both re-derived for $N$ terms, `unreduced_zero` and the remainder borrow
> by ceiling 1, and the paired 70-bit carry check is a *consequence* of how tight the batch's bounds came out.
> **The bounds compose multiplicatively**, so one element admitted with a pessimistic maximum -- a point read from a table
> whose entry maxima were taken as the max over all entries, say -- turns free additions into forced reductions all the
> way downstream. The failure mode is never a failed constraint; it is a silent wrap in $\mathbb F_n$ that makes the
> mod-$2^T$ half of "The CRT Split: One 272-bit Equality Becomes Two ~136-bit Ones" vacuous.

## Two-Row Frontend

### The CRT Split: One 272-bit Equality Becomes Two ~136-bit Ones

The prover supplies $q, r$ with $ab = qp + r$ **over $\mathbb Z$**; the circuit never checks that.
It checks the identity mod $2^T$ (the *binary basis*, $T = \text{NUM\_LIMBS}\cdot\text{NUM\_LIMB\_BITS} = 4\cdot68 = 272$) and mod $n$ (the *prime basis*).
CRT gives it mod $M = 2^T n$; both sides being $< M$ gives it over $\mathbb Z$.
Each half is cheap for a different reason.
The prime half is **one gate**, because every element carries a redundant fifth field element $\text{prime\_basis\_limb} = \sum_i \text{limb}_i 2^{68i} \bmod n$, making $a_\pi b_\pi + q_\pi(n-p) - r_\pi = 0$ a single fused multiply-add.
The binary half needs only the **partial** schoolbook product: limb-products of weight $\ge 2^{4L}$ vanish mod $2^T$, so only $c_0..c_3$ are ever formed.
**Price** per multiplication: 8 gates for the limb products (*"4 non-native field gates to check the limb multiplications, plus 4 arithmetic gates (3 big add gates + 1 unconstrained gate)"*), $+1$ prime-limb gate, $+$ quotient/remainder construction ($\approx2$ gates, 2 range-constraint triples), $+$ 2 carry range checks.

> **Where it stops.** The quotient-bound arithmetic is validated only for target moduli of 250--256 bits: below 250 it is
> unproven [Medium], above 256 four limbs do not hold the modulus at all.

### Lazy Reduction: Reduce Mod $2^s$, Not Mod $p$

Full reduction to $[0,p)$ needs a comparison chain; skip it.
Prove $\text{this} = qp + r$ with $r$ constrained only to $s = \lceil\log_2 p\rceil$ **bits** -- free, being exactly what the non-overflowing constructor already does when it range-constrains the top limb to `NUM_LAST_LIMB_BITS`.
*"We reduce an element's mod $2^t$ representation to size $2^s$ for smallest $s$ with $2^s>p$ ... suffices for addition chains."* Two economies inside: the quotient is a **single limb** (the other three wired to the zero index, prime limb *is* the quotient limb), and its range proof is $\mathrm{msb}(\max/p)+1$ rounded **up to even**, asserted $\le$ `NUM_LIMB_BITS`.
**Price** $\approx9$ gates $+$ one small range constraint $+$ 2 range-constraint triples for the remainder.

> **Where it stops.** The output is $< 2^s$, **not** $< p$. Comparing limbs against a constant needs a real reduction, and
> canonicalising chains the lazy reduction *then* a less-than. Publishing reduces only mod $2^s$, so two representations of
> one residue can both be published unless the caller reduces mod $p$.

### Amortising the Quotient: N Products, One Quotient, One Pair of Carries

Each quotient costs a range proof and each identity two carry range checks, so have **one** of each per expression.
Rearrange $\sum_j a_jb_j + \sum_i c_i = qp+r$ as $a_0b_0 = qp + \bigl(r - \sum_{j\ge1}a_jb_j - \sum_i c_i\bigr)$: one full multiplication gate handles $(a_0,b_0,q,r')$ and every other product is a cheap *partial* multiplication folded into the remainder accumulators.
**How the folding is free is the trick.** The gate evaluates $\bigl(ab + q\cdot\text{neg\_modulus} - r\bigr)/2^{136} = \text{lo} + \text{hi}\cdot2^{136}$; setting $\text{neg\_modulus} = [2^{136},0,0,0]$ and $q = [\text{lo}_1,0,\text{hi}_1,0]$ injects $\text{lo}_1$ into `lo` and $\text{lo}_1/2^{136}+\text{hi}_1$ into `hi`, and $r = [0,0,\text{lo}_1,0]$ subtracts the stray term back off, which *"saves us 2 addition gates"* -- the modulus-limb selectors have become a **shift operator**.

- **Paired carry checks.** If both carries are $\le70$ bits one accumulator handles both: each splits into $5\times14$-bit sublimbs, **3 rows**, packing 10 sublimbs plus 2 originals into $3\times4 = 12$ wire slots. 70 *is* $5\times14$.
- **The remainder borrow, folded into a selector.** $r$'s low half can exceed the positive part's and underflow in $\mathbb F_n$, wrapping and destroying the bound.
  Add the constant $\lceil\text{max\_remainders\_lo}/2^{2L}\rceil$: zero gates, it only bumps an additive constant.
  The high half needs none, $r \in [0,2^{|p|})$ against $[0,2^T)$.
- **A greedy scheduler decides when a reduction is forced.** For each of the $2N$ multiplicands compute how much the maximum quotient would shrink if *that one alone* were reduced; sort descending, reduce the single best, re-test, loop.
  Constants score 0, each avoided reduction is worth $\approx12$ gates, and it gives up when every candidate scores 0 and the product still overflows.

> **Where it stops.** `MAXIMUM_SUMMAND_COUNT` $= 2^4 = 16$ products and 16 addends -- but carry bounds scale with $N$, so
> the high-carry msb crosses 70 and the paired fast path is lost well before the cap. At least one multiplicand of the
> *whole batch* must be a witness, and $N\cdot(\text{max remainder})^2$ must fit under $M$ even after every operand is
> reduced -- checked up front, rejecting the circuit rather than building it.

### Packing the Wires: Addition in 4 Gates, Injection in 2, Subtraction for Free

Adding two elements looks like 5 gates -- four binary limbs and the prime limb.
But it touches **15 witnesses** (5 each of $x,y,z$) and 4 rows $\times$ 4 wires is **16 slots**: *"we cannot do better than 4 gates because we have a total of 15 witnesses ...
$\lceil15/4\rceil = 4$"*.
Row 1 carries $z_0 = x_0+y_0$ **and** $z_\pi = x_\pi+y_\pi$, rows 2--4 one limb each; the doubling up works because a special mode of the arithmetic relation (two distinct `q_arith` values) toggles an extra $w_1 + w_4 - w_4^{\omega}$ relation on top of the ordinary add.
Guarded by both operands being witnesses, both prime-limb multiplicative constants being 1, and their prime witness indices differing.
**`add_to_lower_limb`: 2 gates instead of 5.** To add a small *already range-constrained* field element (a skew bit, a NAF correction), do not build a whole element -- add it to limb 0 and the prime limb and bump limb 0's maximum by the caller-supplied bound, for *"2 additional constraints instead of 5/3 needed to add 2 bigfield elements and several needed to construct a bigfield element."* The assertion is $A_0 + \max(\text{other}) \le 2^{78}-1$, and the caller, not the function, must have constrained $\text{other}$ to that bound.
**Subtraction is addition plus a borrow-chain constant.** Compute $a-b$ as $a + sp - b$ for the smallest $s$ making **every limb** non-negative -- strictly stronger than making the value non-negative.
A borrow cascade fixes per-limb shifts $t_0 = 2^{\beta_0}$, $t_1 = 2^{\beta_1}-2^{\beta_0-L}$, $t_2 = 2^{\beta_2}-2^{\beta_1-L}$, $t_3 = 2^{\beta_2-L}$, redistributed so the net added quantity is exactly $sp$.
The constant folds into additive constants, so it is **free in gates**; it is paid for in the maxima $C_i = A_i + S'_i$, which shorten the chain before the next forced reduction.

> **Where it stops.** If the subtrahend has been inflated by a long addition chain its maxima grow, $s$ grows, and the
> result's maxima grow super-linearly -- hence a reduction check on *both* operands first. And if the base element is
> constant while the injected value is a witness, limbs 1--3 are re-materialised as fixed witnesses at **3 extra gates**,
> because an element's limbs must be uniformly constant or uniformly witness.

### Equality and Order Without a Reduction

**Equality in one multiplication.** Witness the indicator and either an inverse or one -- *"If $r=1$ then $X=1$, $Y=0$; if $r=0$ then $X=I$, $Y=1$"* -- and evaluate $(a-b)X = Y$.
The product comes out of the ordinary multiplication, hence is already reduced to $< 2^s$, so "equals 0 or 1" is *limb equality*: limb 0 and the prime limb equal the indicator, limbs 1--3 equal zero.
No comparison chain at all.
**Non-equality as a degree-$(L{+}R{+}1)$ product.** Two unreduced elements can differ by $kp$, $k\in[-R,L]$, and still be equal mod $p$.
Rather than reduce both, multiply out every possibility **in the prime basis only**, $\text{diff} \leftarrow \text{diff}\cdot(\text{base\_diff} \mp kp)$ with $\text{overload} = \lfloor\max/p\rfloor$ per side, then assert non-zero -- *"each loop iteration adds 1 gate"*.
For reduced inputs that is **1 gate** against $\approx12$ for a reduction, and **the constraint count is a function of how unreduced the inputs are.** **Less-than by prover-chosen borrows.** Prove $(\text{limit}-1)-x \ge 0$ limb-wise with three witnessed borrow bits and **4 range checks** (two paired calls): $r_0 = U_0-x_0+b_02^L$, $r_1 = U_1-x_1+b_12^L-b_0$, $r_2 = U_2-x_2+b_22^L-b_1$, $r_3 = U_3-x_3-b_2$, for $\approx9$ gates.
*"The prover can rearrange the borrows the way they like.
The important thing is that the borrows are constrained."* For a *boolean* answer, run an msb-to-lsb ladder whose rungs each encode $a<b$ as one witness plus one range check, $b - a + (K-1) - Kq = r < K$.

> **Where it stops.** The non-equality product has imperfect *completeness*: *"for points equal mod $r$ ... but different
> mod $p$, you can't construct a proof. The failure probability is at most $(L+R+1)/r$"* -- at $\max < 2^{256}-1$ and
> $p \ge 2^{249}$ that is $L,R \le 127$ and $< 2^{-246}$, but it grows with the addition chain. The borrow argument needs
> each per-limb quantity in $[-2^b-1,2^{b+1}]$ and those distinct mod $n$, *"which happens e.g. if $r/2 > 2^{b+1}$"*, and
> the ladder needs $2^{\text{num\_bits}} < n/2$ so the worst case $r = 2K-2$ cannot wrap. Both assume the operands' limbs
> are **already** range-constrained; the equality trick is unsound the moment its product comes from an unreduced path.

### Everything That Lives in a Selector Is Free, Including a Multiple of $p$

A field element is $\text{witness}\cdot\text{multiplicative\_constant} + \text{additive\_constant}$, so adding a constant, scaling by a constant, and adding two terms sharing a witness index are all **0 gates**; one normalisation gate flattens the form back, early-returning when already flat.
The $sp$ offsets of "Packing the Wires: Addition in 4 Gates, Injection in 2, Subtraction for Free", the remainder borrow of "Amortising the Quotient: N Products, One Quotient, One Pair of Carries", the negated modulus limbs and the fractional rotation coefficients of "Rotation for Free: Fractional Coefficients, or No Table at All" are all this one mechanism.
**`unreduced_zero()`:** for $a/b$ the circuit checks $bc = a$ where $a$ is an *input*, possibly unreduced and larger than $bc$, so the difference underflows.
Add a compile-time multiple of the modulus, $u = \lceil\max(a)/p\rceil$ with $\max(a) < \sqrt{2^T n}$ -- *"if we always add this element during division, then we never run into the formula-breaking situation"* -- for **zero gates**, its limbs being selector constants.
**N summands in $\lceil N/3\rceil$ gates:** chain add gates passing a running total out through the fourth wire into the *next row's* fourth wire, $d_{i+1} = d_i - a_i - b_i - c_i$ on every row but the last and $0 = d_i-a_i-b_i-c_i$ on it, with constants stripped into the accumulator's additive constant and the vector zero-padded to a multiple of 3.
Five additions in **2 gates**: gate 0 wires $[a_0,a_1,a_2,a_3]$, gate 1 wires $[b_0,b_1,b_2,b_3]$, $b_3 = a_0+a_1+a_2+a_3$, $b_2 = b_3+b_0+b_1$ -- against $N-1$ naive.

> **Where it stops.** Custom gates index wires by witness index and cannot absorb a scaling, so a scaled value used as
> custom-gate input must be normalised, and constants materialised: *"we disallow constants. If there are constants, we
> convert them to fixed witnesses (at the expense of 1 extra gate per constant)"*. `unreduced_zero` is sized against
> ceiling 1 of "The Bound Discipline: Derive Your Two Ceilings, Never Copy Them", and the accumulator emits a fresh witness -- if the value was only wanted inside another gate, a
> chained fused add is cheaper.

### `msub_div`: One Quotient for a Whole Formula

Rather than compute $x = \text{num}/\text{den}$ and then multiply, constrain $\text{result}\cdot\text{divisor} + \sum_i \text{mul\_left}_i\text{mul\_right}_i + \sum_j \text{to\_sub}_j = 0$ in one shot, feeding "Amortising the Quotient: N Products, One Quotient, One Pair of Carries" with `result` as first left operand, `divisor` as first right operand, remainder **fixed to zero**.
*"Algorithm is constructed in this way to ensure that all computed terms are positive ...
It is critical that ALL the terms on the LHS are positive to eliminate the possibility of underflows ... only requires one quotient and remainder + overflow limbs."* That zero remainder must be a *fixed witness*, not a constant, because *"remainder needs to be defined as wire value and not selector values"*.
**Price:** one full multiplication group $+$ $N-1$ partial groups $+$ **one** quotient range proof, against one division plus $N$ multiplications each with its own quotient.
This is why curve formulas never materialise intermediate $y$-coordinates.
A chained addition stores $(x_1^{\text{prev}}, y_1^{\text{prev}}, \lambda^{\text{prev}}, x_3^{\text{prev}})$ instead of $(x_3,y_3)$ and gets the next slope as $-\bigl(\lambda^{\text{prev}}(x_2-x_1^{\text{prev}}) + y_1^{\text{prev}} + y_1\bigr)/(x_2-x_1)$: *"we only require 2 non-native field multiplications per point addition, instead of 3"*.
A ladder goes further, keeping $y$ as an **unevaluated** record $\{\text{mul\_left},\text{mul\_right},\text{add},\text{is\_negative}\}$ fed straight into the next round's `msub_div`, sign alternating per round so every argument stays positive, one quotient paying for the whole deferred expression -- *"each iteration reduces the number of field multiplications by 1, at the cost of more additions ...
The optimal input size appears to be 4."*

> **Where it stops.** The optimum is 4 and not 16 for "Amortising the Quotient: N Products, One Quotient, One Pair of Carries"'s reason: deferred products are summands and the carry bounds
> degrade until the 70-bit paired check is lost. The divisor-non-zero check is an explicit opt-out, and every caller taking
> it must discharge non-zeroness otherwise -- in the chain, by the preceding non-equality assertion of "Equality and Order Without a Reduction", itself
> imperfectly complete. The formulas are also *incomplete*: they require $x_1 \ne x_2$ on every input.

# Lookup-Table Design

A lookup is not a function call.
Designed well, one lookup sequence proves a decomposition, a range, a recombination and a computation at once; designed badly it proves one bit of arithmetic and costs a table.

## Two-Row Frontend

### The Accumulator Column: Decompose, Look up and Recombine in One Column

A multi-table returns not slices but **accumulators**: row $j$ of column $i$ holds the *remaining* value $\bigl(S - \sum_{k<j}s_k\text{coeff}_k\bigr)/\text{coeff}_j$, so that $w_i[j] - w_i[j+1]\cdot\text{step}_{i,j} = s_{i,j}$ with the step in selectors and $w_i[j+1]$ the shifted wire.
Row 0 of each column is therefore the **fully recombined value**, and the decomposition is proved by the lookup relation itself.
For a 32-bit XOR: coefficients $(2^0,2^6,2^{12},2^{18},2^{24},2^{30})$, steps $(1,2^6,2^6,2^6,2^6,2^6)$ -- **6 lookup rows** (five 6-bit tables of $2^{12} = 4096$ entries, one 2-bit table of $2^4 = 16$) with **zero** extra gates for slicing or recombining, against a naive single table of $2^{64}$ entries.
This is the gate-based form of `air.md` "A Lookup That Computes *and* Range-Checks in the Same Message": the lookup argument *is* the range check *and* the recomposition.
**Multi-output tables give several answers per lookup.** A basic table has three columns, so $(C_2,C_3)$ is two outputs per key and the third exists whether you use it or not: an S-box table returning $S(x)$ **and** $S(x)\oplus\text{xtime}(S(x)) = 3S(x)$; a $\chi$ table returning the normalised output and $C_2/11^8$, *"to determine the value of the most significant (63rd) bit of the output"*; a hash input table returning three linear functions of the same slices -- normal accumulator, sparse accumulator, and a rotation accumulator with its correction already in the coefficients.

> **Where it stops.** The accumulator forces a *single geometric step* per column, so an output sliced differently from the
> input needs fractional coefficients ("Rotation for Free: Fractional Coefficients, or No Table at All") or a per-slice correction ("Two Accumulator Sequences in One Column, and a Twist That Turns Rotation into a Multiply"). And a two-input table spends $C_1,C_2$ as
> **keys**, leaving only $C_3$ as output: multi-output and two-in-one-out are alternatives, not a package.

### Sparse (Base-$B$) Representation, Where the Base Is a Carry Budget

Write a $k$-bit value as $\sum_i b_i B^i$, $b_i\in\{0,1\}$.
XOR of several values is then **addition** of their sparse forms plus one normalisation lookup $d \mapsto d \bmod 2$; AND and majority come from the same sum read through a different normalisation table.
**The rule for choosing $B$: it must exceed the largest digit reachable before the next normalisation** -- not the largest digit of an input, the largest after every accumulation you intend to do.
$B$ is a carry budget, and it is the only parameter in the scheme:

| operation | base $B$ | digit budget | bits/lookup | table size |
|---|---|---|---|---|
| Ch $+\ \Sigma_1$ | 28 | $7\sigma + (e+2f+3g)$, $\sigma\in[0,3]$, sum $\in[0,6]$ $\Rightarrow$ max 27 | 2 | $28^2 = 784$ |
| Maj $+\ \Sigma_0$ | 16 | $4\sigma + (a+b+c)$, both $\in[0,3]$ $\Rightarrow$ max 15 | 3 | $16^3 = 4096$ |
| $\sigma_0/\sigma_1$ | 16 | $4s_0 + s_1$, both $\in[0,3]$ | 3 | $16^3 = 4096$ |
| $\theta$ | 11 | 5-way XOR plus a rotate $\Rightarrow$ digits to 10 | 4 | $11^4 = 14641$ |
| $\rho$ | 11 (effective 3) | digits $\in[0,2]$ after $\theta$ | $\le8$ | $3^8 = 6561$ |
| $\chi$ | 11 (effective 5) | $1 + 2A - B + C \in[0,4]$ | 6 | $5^6 = 15625$ |
| byte-oriented cipher | 9 | up to 8 XOR-adds per digit | 4 | $9^4 = 6561$ |

Measured: **17,329 constraints for a one-block sponge permutation** *"using small(ish) lookup tables (total size $< 2^{64}$)"* -- $\theta$ at *"20.5 gates per 5 lanes + 25 = 127.5 per round"*, $\rho$ at 8 gates for the unrotated lane and 10 for the other 24 (248 total), $\chi$ at $12\times25 = 300$, and $\pi$ at **0 gates**, being witness re-indexing.
**The payoff is that whole layers become multiplication-free.** With an S-box table returning both $S(x)$ and $3S(x)$, and $2x = 3x\oplus x$ over $\mathrm{GF}(2^8)$, a diffusion layer is pure addition: $r_0 = 2s_0\oplus3s_1\oplus s_2\oplus s_3 = s_0^{(1)}+s_0^{(3)}+s_1^{(3)}+s_2^{(1)}+s_3^{(1)}$, and the four outputs share two intermediates $t_0 = s_0{+}s_3{+}3s_1$, $t_1 = s_1{+}s_2{+}3s_3$ -- each output one fused three-term add on top.
Round-key addition folds into the same accumulation and the row shift is 0 gates: **6 fused adds per column, 24 per round**, plus 16 table reads, and not one multiplication.

> **Where it stops.** Digit overflow is silent and catastrophic -- the normalisation table simply returns a wrong answer
> for an out-of-range digit. Track it: a per-byte `add_counts` array forcing a normalisation at threshold 3, *or earlier if
> the byte is about to enter the S-box* (base 9 with five addends plus a round key reaches 6--8); a sponge permutation that
> normalises every round to keep digits $\le2$ entering the next.

### Rotation for Free: Fractional Coefficients, or No Table at All

In the accumulator scheme a rotation is a **permutation of slice weights**, so it belongs in the coefficients, not a table; inverse powers of two are legal, selector values being field elements.
For a rotate-right by 16 on 6-bit slices, with $c = 1/2^{16}$, the output column takes $\bigl(1,\,2^6,\,c,\,c2^2,\,c2^8,\,c2^{14}\bigr)$ and the caller multiplies the accumulator by $2^{32-16}$ once -- **free**, folding into a multiplicative constant ("Everything That Lives in a Selector Is Free, Including a Multiple of $p$").
Zero extra multi-tables and zero extra gates, beyond one small intra-slice rotate table per amount.
**Better still, derive the rotation from a plain accumulator.** Row $j$ is "the value with the low $j$ slices removed and divided out", so row 2 of the *ordinary* XOR accumulator already is the top of a 12-bit rotation: with $\text{row}_0 = s_0 + 2^6s_1 + 2^{12}s_2 + 2^{18}s_3 + 2^{24}s_4 + 2^{30}s_5 = u$ and $\text{row}_2 = s_2 + 2^6s_3 + 2^{12}s_4 + 2^{18}s_5$, $\;\mathrm{ROTATE}_{12}(u) = \text{row}_2 + (\text{row}_0 - 2^{12}\text{row}_2)\cdot2^{20}$ -- *"we can get the correct value by combining values from [the] XOR table itself"*.
**1 arithmetic gate, and a whole multi-table (6 basic tables) deleted.**

> **Where it stops.** Fractional coefficients express only rotations congruent to a slice boundary modulo the slice size;
> the residue needs its own small rotate table (by 4 for a 16-rotation, by 2 for 8, by 1 for 7). The table-free derivation
> is narrower still: the amount must be an **exact multiple** of the slice size ($12 = 2\times6$). Both are sound only
> because the reconstruction is exact over the integers -- $2^{-16}$ in $\mathbb F_n$ is not a shift.

### Two Accumulator Sequences in One Column, and a Twist That Turns Rotation into a Multiply

**A step size of 0 breaks the accumulation and starts a new sum**, so one lookup column can carry two independent accumulators.
A base-11 left-rotation uses this: split the lane at the rotation boundary into a wrapping "left" part and a non-wrapping "right" part and run both through the *same* gate sequence, letting column 1 hold a pair of sums:

```
| Row | C0                                 | C1           | C2       |  Q1  |  Q2  | Q3 |
|  0  | A3.11^24 + A2.11^16 + A1.11^8 + A0 | B1.11^8 + B0 | A0.msb() | 11^8 | 11^8 | 0  |
|  1  |            A3.11^16 + A2.11^8 + A1 |           B1 | A1.msb() | 11^8 |   0  | 0  |  <- new sum
|  2  |                       A3.11^8 + A2 | B3.11^8 + B2 | A2.msb() | 11^8 | 11^8 | 0  |
|  3  |                                 A3 |           B3 | A3.msb() |
```

*"The coefficients for the rows treat Column0 as a single accumulating sum, but Column1 is a pair of accumulating sums."* The halves are stitched with one gate, $\text{left} + \text{right}\cdot11^{\text{rot}}$, and column 3 gives the per-slice msb free.
Slice sizes are chosen so the lookup *also* range-constrains each half -- *"we want to implicitly range-constrain normalized $< 11^{\text{limb\_bits}}$, which means potentially using a lookup table that is not of size $11^{\text{max\_bits\_per\_table}}$ for the most-significant slice"* -- so the table is instantiated at every slice size 1..8.
**8 gates for the unrotated lane, 10 for the other 24, 248 per round**, rotation *and* range constraint free.
**Choose the representation so that rotate-by-one is a multiply.** Where the diffusion step needs $D = C_0 \oplus \mathrm{ROTL}(C_1,1)$, store each 64-slice lane in a **65-slice twisted** form $[b_{63},\dots,b_0,b_{63}]$.
Then $\mathrm{XOR}(A,\mathrm{ROTL}(B,1))$ is $A.\text{twist} + 2B.\text{twist}$ in base 11, i.e. $D[i] = C[(i{+}4)\bmod5] + C[(i{+}1)\bmod5]\cdot B$ -- **a single constant multiply, 0 gates**, where the twisted value is $\text{state}\cdot11 + \text{state\_msb}$ and the msb arrives free in the third column of the $\chi$ table ("The Accumulator Column: Decompose, Look up and Recombine in One Column").
*"This is MUCH cheaper than the extra range constraints required for a naive left-rotation."* $D$ then has 66 slices whose top and bottom are artifacts, stripped with 3 witnesses and one assertion (**1 gate**, the multipliers being constants) plus two small range constraints and a 1-to-2 table read on the middle.

> **Where it stops.** The two-sequence trick needs 25 distinct multi-tables, one per lane rotation, and its witnesses
> cannot be derived by the generic lookup machinery -- they are built by hand. The twist rests on a compile-time assertion
> that the table's slice width **divides** the lane width: at $4 \mid 64$ the lookup sequence implies the middle term is
> $< 11^{64}$ for free; if it did not divide, that term would need its own range constraint and the saving would evaporate.

### One Lookup Producing a Modular Sum *and* a Boolean Function

Two independent sums share one sparse digit if you separate them with a **radix multiplier**.
The digit $7\sigma + (e+2f+3g)$ packs a rotation sum $\sigma\in[0,3]$ against a choice-function encoding in $[0,6]$, and the 2-D-indexed normalisation table returns $\Sigma_1\text{bit} + \mathrm{Ch}\,\text{bit} \in [0,2]$ -- **one lookup answers both**; the companion pair uses $4\sigma + (a+b+c)$ in base 16.
The multiplier 7 (resp. 4) *is* the separator, and it is exactly the digit budget of "Sparse (Base-$B$) Representation, Where the Base Is a Carry Budget" read as two fields.
The three rotations are applied by multiplying the whole sparse value by a limb-0 coefficient and correcting the rest: one correction $\delta = c_1 - B^{11}c_0$ folds into the **input table's** third-column coefficients, the other is a single constant multiply, and the limb structure $L_0 = 0..10$, $L_1 = 11..21$, $L_2 = 22..31$ is chosen so the rotation amounts $(6,11,25)$ and $(2,13,22)$ each split cleanly across it.
**Price:** one pair is 1 input lookup (3 rows) $+$ 2 arithmetic gates $+$ 1 output lookup (16 rows of the 784-entry table); the other is 1 input lookup $+$ 2 gates $+$ 11 rows of the 4096-entry table.

> **Where it stops.** The bases are exactly tight -- 28 because the maximum index is 27, 16 because it is 15. A fourth
> rotation term or a fourth Boolean input overflows the digit. And two different bases for the two pairs means the same
> word needs **two different sparse forms**, which is where ordering side-effects come from: one routine populates a
> sparse form another one copies.

### Modular Addition and Wide Bitwise Ops: Constrain the Overflow, Not the Result

**Addition mod $2^{32}$ in 1 gate.** Emit $\text{result} = a + b - \text{overflow}\cdot2^{32}$ as a single fused three-term add and range-constrain `overflow` to a handful of bits.
**That bit count is the entire soundness argument**, so every call site must justify it: a sum of six 32-bit values has overflow $\le5$ (3 bits), of seven $\le6$ (3 bits), a final two-term add 1 bit.
Message expansion frames the same trick as a division -- $(w_{\text{raw}}-w)/2^{32}$ range-constrained to **2 bits**, because a sum of four 32-bit values has quotient $\le3$.
**Wide XOR/AND in 32-bit chunks.** Slice both operands into 32-bit chunks, do one 2-to-1 table read per chunk, and reconstruct with $\sum_i \text{chunk}_i2^{32i}$ asserted against the input.
*"Since we perform the lookup from 32-bit multi-tables, the lookup operation implicitly enforces a 32-bit range constraint on each chunk"* -- so **only the tail chunk is explicitly range-constrained**: 2 range constraints for the whole operation at any width, 6 lookup rows per chunk.

> **Where it stops.** The modular add does not range-constrain its *result* -- *"marked unsafe since the result is not
> explicitly range-constrained herein."* Record which outputs a downstream lookup constrains implicitly and constrain the
> rest explicitly: two round-state words at loop exit, three initial-state words, three schedule words, and all eight
> outputs. Miss one and the hash is malleable. The chunked op stops where the reconstruction would wrap the native modulus.

### Read-Only Arrays: Build Them Lazily, or Not at All

The array is **not** created at construction; initialisation runs on the first non-constant read.
A table whose entries are all constants and whose index is always constant therefore never touches the builder -- *"if both the table entries and the index are constant, we don't need a builder as we can directly extract the desired value from `raw_entries`"* -- and constant entries go through a caching helper, so repeated constants share one witness.
A **twin** table stores a pair per index, so one read yields two field elements for one gate; that is what makes a 5-table encoding of an emulated curve point affordable, the four binary limbs plus prime limb of each coordinate packing as $(x_0,x_1),(x_2,x_3),(y_0,y_1),(y_2,y_3),(x_\pi,y_\pi)$ and a whole point costing 5 gates.
**Price:** 1 gate per read; construction 1 gate per entry.

> **Where it stops.** *"The caller must enforce that `_index < 2^table_bits`; `_index` is not constrained in this
> function."* The index range is implied only if it came from a range-constrained source or a lookup, and a constant index
> must be converted to a witness and pinned, at 1 gate.

### Several Rounds of a Permutation per Row, via a Linear Solve Inside the Relation

The obvious encoding is one round per row, four wires holding four state limbs.
But where an internal round S-boxes only `state[0]` and the internal matrix is diagonal-plus-all-ones, the other three limbs are **affine functions of the history** and can be *solved for inside the relation* rather than witnessed.
Put `state[0]` at rounds $4i{+}0..4i{+}3$ into the four wires and recover $(s_1,s_2,s_3)$ at row start by a $3\times3$ Vandermonde solve in the relation itself: **56 internal rounds in 14 rows** instead of 56.
Where no such gate exists, the initial external matrix multiply is 6 fused adds, exploiting the reuses $v_1 = v_2 + t_1$ and $v_3 = v_4 + t_2$:

$$t_1 = s_0{+}s_1{+}2s_3,\quad t_2 = s_2{+}2s_1{+}s_3,\quad v_2 = 4s_0{+}4s_1{+}t_2,\quad v_1 = v_2{+}t_1,\quad v_4 = t_1{+}4s_2{+}4s_3,\quad v_3 = v_4{+}t_2$$

> **Where it stops.** The round count must be divisible by the compression factor, asserted at compile time, and the
> compressed rows must be **contiguous** in one block. Where external and internal rounds live in separate blocks you need
> explicit state-propagation landing rows between them, and the saving shrinks by one row per boundary. The gate indexes
> wires by witness index, so constant inputs must be materialised first ("Everything That Lives in a Selector Is Free, Including a Multiple of $p$").

# Traps

The AIR trap catalogue (`air.md` "Traps") mostly transfers: range checks without canonicity, selectors that are boolean but not one-hot, advice not uniquely pinned, and small-field overflow all bite identically here.
What is specific to a gate-based system:

**A simple selector used non-linearly stops being combinable.** Automatic selector combining requires *"Every polynomial constraint involving a simple selector $s$ must be of the form $s \cdot t = 0$, where $t$ is a polynomial involving no simple selectors"*.
Multiply two simple selectors together, or put one inside a lookup input, and it must become a complex selector -- silently losing the packing, and with it the fixed-column saving that motivated the design.

**A chained gate must be terminated.** A gate such as `Xor16` chains by making each gate's `Next` row the following gate's `Curr` row, which costs nothing -- but the chain needs a final row whose inputs are all zero, done with copy constraints of a row to *itself*.
The design note carries the warning verbatim: *"Warning: don't forget to check that the final row is all zeros."* An unterminated chain is an unconstrained tail.

**Reserving degree headroom is free; discovering you need it later is not.** `set_minimum_degree` exists precisely so a downstream argument can convert slack into fewer columns.
Raising the cap inside a bracket costs nothing; crossing a bracket doubles the extended-domain work for *every* polynomial (`degree.md` "The Bracket Theorem: Only $D \in \{3, 5, 9, 17, 33\}$ Are Rational").

**A hand-rolled fixed column cannot join the automatic combining.** Manual selector packing is counterproductive wherever selectors are auto-combined, for exactly this reason -- the optimizer can only pack what it can see is a simple selector.
