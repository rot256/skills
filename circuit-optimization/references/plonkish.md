# PLONKish optimization

*A field manual for gate-based constraint systems.*

Rows x columns, custom gates, selectors, copy constraints, lookups.
Collected by reading halo2, Kimchi, Plonky2 and Barretenberg.
Every entry carries the mechanism, the price, and the condition under which it stops working.
The trace-based (AIR/STARK) cost model is `air.md`; constraint degree is `degree.md`; R1CS is `r1cs.md`;
cross-arithmetization moves are `techniques.md`.

$$\text{cost} \;=\; \text{rows} \times \text{columns} \;+\; \underbrace{\text{permutation polys}}_{\text{per equality-enabled column}} \;+\; \underbrace{\text{selector columns}}_{\text{per gate group}} \qquad\text{under a cap on gate degree}$$

## The axioms

**A copy constraint is not free.**
This is the single deepest difference from an AIR, which has no permutation over its own columns at all.
Enabling equality on a column adds it to the permutation product, costing one fixed permutation polynomial and one degree
in the rule; past the degree bound the product splits across sets, each with its own grand-product column.
Everything in I.1--I.2 is a way to avoid paying it.

**A gate is a selector, and a selector is a committed column.**
Adding a bespoke gate is not free even on rows that do not use it: the selector is committed over the whole domain, it
enters the degree budget, and in Plonky2 it competes for space in a selector *group* whose size is capped by the degree.
The break-even question -- how many uses does a gate need before it pays for its selector -- is III.1.

**Rows are filled, not consumed.**
A row has a fixed width, and the builder's job is to pack independent operations into the leftover columns.
Whether a row is "used" is the wrong question; how much of its width is idle is the right one (II.3).

**The window is a rotation, and its reach is system-specific.**
halo2 allows any `Rotation` but only *within a region*; Kimchi allows exactly `Curr`/`Next`; Plonky2 gates see one row plus
routed wires. That difference drives each system's entire gadget style.

**Degree is a global cap that is usually under-spent.**
Same as everywhere else, and it has its own reference: only $D \in \{3,5,9,17,33\}$ are rational choices, and below the cap
degree is prepaid (`degree.md`).

---

# Part I -- The wiring layer

Where an AIR reads the next row for free, a PLONKish system charges you for moving a value. These three sections are the
whole of that bill.

## I.1 Rotations replace copies -- and a copy is not free

PLONKish

halo2's own statement of the trick:

> *"The motivation for offset references is to reduce the number of columns needed in the configuration ... If we did not
> have offset references then we would need a column to hold each value referred to by a custom gate, and we would need to
> use equality constraints to copy values from other cells ... we also do not need equality constraints to be supported for
> all of those columns."* (`book/src/concepts/chips.md:36-42`)

The price of the alternative is concrete: enabling equality on a column adds it to the permutation product
$\prod_i (v_i(X) + \beta s_i(X) + \gamma)$, so each such column costs one extra fixed permutation polynomial *and* one
degree in the rule; past the degree bound halo2 splits the product across $b$ sets with a separate grand-product column each
(`design/proving-system/permutation.md:180-248`).
In Plonky2 the same fact appears as a *width* budget: only the first `num_routed_wires` columns participate, and
`num_partial_products = ceil(num_routed_wires / quotient_degree_factor) - 1` (`util/partial_products.rs:40-47`).

> **Where it stops.** Rotations reach only *within a region* (halo2) or exactly one row (Kimchi's `Curr`/`Next`, Plonky2's
> gate). Crossing a region or a chip forces a real copy. And a rotation-using gate cannot be placed on an arbitrary row, so
> it cannot fill floor-planner gaps -- only rotation-free gates can.

## I.2 Advice (unrouted) wires for anything no gadget reads

PLONKish (Plonky2)

Columns above `num_routed_wires` are committed but do **not** join the permutation argument. Every serious Plonky2 gate
parks its internals there:

```rust
/// An intermediate wire where the prover gives the (purported) binary decomposition of the index.
pub(crate) const fn wire_bit(&self, i: usize, copy: usize) -> usize {
    self.num_routed_wires() + copy * self.bits + i
}
```
(`gates/random_access.rs:116-122`). `ExponentiationGate`'s budget is the resulting asymmetry:
$\min(\text{routed}-2, (\text{wires}-2)/2) = \min(78,66) = 66$ bits (`gates/exponentiation.rs:53-58`).

> **Where it stops.** Anything a *gadget* must read or reuse must be routed. That is why `RandomAccessGate` exposes the
> claimed element (routed) and hides the index bits (unrouted): the caller never needs the bits.

## I.3 Gate packing: `num_ops` comes from the wire budget

PLONKish (Plonky2)

Every "small" gate is a vector of independent copies of one op, and the copy count is a pure division:

```rust
pub(crate) const fn num_ops(config: &CircuitConfig) -> usize {
    let wires_per_op = 4;
    config.num_routed_wires / wires_per_op
}
```
(`gates/arithmetic_base.rs:44-47`). At 80 routed wires: **20** base MADs, **10** extension MADs, **13** extension muls,
**40** lookups, **26** LUT entries per row.

The universal primitive is the fused $c_0 m_0 m_1 + c_1 a$ (degree 3), and *everything* is a rewrite into it:
`mul` feeds `x` into the unused addend slot rather than a zero wire; `select(b,x,y) = b\cdot x - (b\cdot y - y)` is **2**
fused ops, not 3; `or(b_1,b_2)` is 2. **Addition is not cheaper than multiplication in Plonky2** -- it burns a full
degree-3 slot.

Two non-obvious consequences:
- **Rows are consumed by *constant-pair fragmentation*, not by op count.** The builder reuses partially-filled rows keyed on
  the gate's constant vector (`plonk/circuit_builder.rs:813-840`), so 20 different $(c_0,c_1)$ pairs used once each cost 20
  rows, not one. That is why `add`/`sub`/`mul` all normalize to $(1,1)$, $(1,-1)$, $(1,0)$.
- **A gate that emits one generator can never share a row.** `num_ops` defaults to the generator count
  (`gates/gate.rs:241-244`), so `BaseSumGate`, `ExponentiationGate`, `PoseidonGate` and `CosetInterpolationGate` always take
  a fresh row; `RandomAccessGate` emits one per copy and can pack.

---

# Part II -- Selectors and the degree budget

## II.1 Selector grouping is the tax nobody expects

PLONKish (Plonky2), and its halo2 analogue

Gates are sorted by degree and bin-packed so that
$$|G| + \max_{g\in G}\deg(g) \;\le\; \text{quotient\_degree\_factor} + 1 = 9$$
and the filter that zeroes a gate outside its rows is a **product over the group**, so
**filtered degree = gate degree + $|G|$ ($+1$ for the UNUSED term when there are several selectors)**
(`gates/selectors.rs:101-160`, `gates/gate.rs:326-333`).
One selector suffices only if $\max\deg + n_{\text{gates}} - 1 \le 9$ -- with `PoseidonGate` (degree 7) present, that permits
**three gate types in the entire circuit**. A degree-9 gate panics outright.

halo2's version is the mirror image: $\ell$ simple selectors on disjoint row sets pack into one fixed column at the cost of
$+(\ell-1)$ degree on every constraint they select, with the packing algorithm stopping at the degree bound
(`design/implementation/selector-combining.md:24-43,81-83`).
Its side condition is worth quoting: *"Every polynomial constraint involving a simple selector $s$ must be of the form
$s\cdot t = 0$, where $t$ is a polynomial involving no simple selectors"* -- a selector used non-linearly must be a complex
selector and is left unoptimized. And hand-made fixed columns *"cannot take part in the automatic combining"*, so manual
combining is counterproductive.

**Practical rule: prefer fewer, reusable gate types of uniform degree.** A rarely-used degree-6 gate can push a common
degree-3 gate into a smaller group *and* add a selector column that every row commits to.

Two more global maxima leak the same way: `num_gate_constraints` and the constants-column count are **maxima over all gate
types** (`plonk/circuit_builder.rs:970-991,1236-1240`), so every row is evaluated against the widest gate's constraint
count. Pack aggressively within a gate type you use a lot; keep rarely-used gates narrow.

## II.2 Trading degree for wires inside one gate

PLONKish (Plonky2)

The `CosetInterpolationGate` is an explicit dial, and its doc says so: *"A full interpolation of N values corresponds to the
evaluation of a degree-N polynomial. This gate can however be configured with a bounded degree of at least 2 by introducing
more non-routed wires."*
The numbers are in IV.5. The *second* trick in that code is the one to steal: after fixing the intermediate count, it
**re-minimizes the degree** purely so the gate joins a bigger selector group.

Other shapes worth knowing:
- `BaseSumGate<B>`: base-$B$ decomposition **and** a per-limb range check in one row, at `degree = B` and
  $\text{num\_limbs} = \min(\log_B(p-1), \text{routed}-1)$ = 63 bits for $B=2$ on Goldilocks. Degree is linear in the base.
- `ReducingGate`: 43-term Horner in one **degree-2** row, because each accumulator step is its own constraint; base-field
  coefficients get 1 wire while accumulators get $D$, and **the last accumulator aliases the output wires**, saving $D$.
- `RandomAccessGate`: claimed element + prover one-hot bits, $2+2^{\text{bits}}$ **routed** wires and degree $\text{bits}+1$
  **per access** -- the entire list is re-materialized into routed wires on every read, so random access into a length-$n$
  array is $\Theta(n)$ wires per read.
- `PoseidonMdsGate`: a linear layer as a **degree-1** gate, which can join any selector group without raising its degree --
  used only `if builder.config.num_routed_wires >= mds_gate.num_wires()`.

---

# Part III -- Gadget catalogues, and what they reveal about the budget

## III.1 halo2's decomposition family

PLONKish (halo2)

- **Running sum.** $z_{i+1} = (z_i - k_i)/2^K$, with the word never witnessed -- recovered as $k_i = z_i - 2^K z_{i+1}$ from
  two adjacent rows of the *same* column and fed directly to the lookup.
  **One advice column, $W{+}1$ rows, $W$ lookups, and exactly one copy** for a $WK$-bit range check.
  *Strict mode is what actually range-checks*: only when $z_W$ is constrained to zero is the element proven $< 2^{WK}$.
- **Shifted final chunk.** To prove $\alpha < 2^n$ with $n \le K$ on a $K$-bit table, look up $\alpha$ **and**
  $\alpha\cdot2^{K-n}$ -- 3 rows, 2 lookups, one degree-2 bitshift gate. (Kimchi does the same *inside* the lookup argument
  with a scaled joint lookup, for zero witness cells.)
- **One lookup argument serving two decompositions**, folded by a selector into a single input expression -- one argument
  instead of two, at the cost of degree 2 in the lookup input.
- **Lookup-free running sum**, range-checking the word by the degree-$2^K$ product instead: no table at all, but
  `assert!(WINDOW_NUM_BITS <= 3)`.
- **Small-set Lagrange interpolation instead of a lookup.** SHA-256 interpolates the 2- and 3-bit spreads so those pieces
  cost *no lookup row* -- degree = domain size, which is why a 9-bit piece is split into $3\times3$ rather than interpolated.
- **Conditional canonicity.** Prove $\alpha < p$ only *when the top bit is set*, by multiplying the whole comparison by the
  flag $\alpha_2$: degree $+1$, and the high 120 bits come free from an existing running sum.
- **Incomplete elliptic-curve addition, and the argument that licenses it.** The incomplete formulas are degree 4 and 3;
  *complete* addition is 12 constraints up to degree 6 with four `inv0` witnesses, and needs two rows because it wants 9
  advice columns. halo2 discharges the exceptional case not by casework but by tracking **indices**: distinct indices mod
  sign imply distinct $x$, and the accumulator is bounded by $2^{n+1}+2^n-1 < (q-1)/2$. The sage check shows that first
  fails at $i = 252$, so **exactly the last three iterations and the final conditional subtraction use complete addition**
  -- everything else is incomplete. Sinsemilla uses the same operator with a different licence: an exceptional case would
  yield a discrete log. Two companion savings: $y_A$ is *eliminated* from the accumulator by substituting the slope
  equations, leaving one materialized $y$ in the whole loop; and the fixed-base gadget interpolates only the
  $x$-coordinate, recovering $y$ from the curve equation plus a per-window constant $z_w$ chosen so that $z_w + y$ is a
  square and $z_w - y$ is not.
  *Stops:* the bound is the whole proof. Change the scalar width, the curve, or the accumulator's starting point and the
  index at which incompleteness becomes unsound moves with it.

## III.2 Kimchi: designing to a hard budget

PLONKish (Kimchi)

15 columns, **7 permutable**, a 2-row (`Curr`/`Next`) window, $\le 4$ lookups per row. Every design decision follows:

> *"We have at most 7 copyable cells per row and gates can operate on at most 2 rows, meaning that we have an upperbound of
> at most 14 limbs per gate (or 7 limbs per row)"* $\Rightarrow \text{limbs}_{\max} = \lfloor 14/4\rfloor = 3
> \Rightarrow \ell = t/3 = 264/3 = \mathbf{88}$ bits per limb.

That is the whole derivation of Kimchi's 88-bit foreign-field limbs, from a wire budget.
Other moves worth transplanting:
- **`Zero` companion rows** as pure storage, doubling the addressable cells for one selector.
- **Gate chaining through the permutation**: a gate's `Next` row *is* the next gate's `Curr` row, so the hand-off costs
  nothing -- but a chain must be **terminated**, which `Xor16` does with copy constraints of a row to itself
  (*"Warning: don't forget to check that the final row is all zeros"*).
- **Negated modulus to kill borrows.** Foreign-field multiplication uses $f' = 2^t - f$ as a public gate coefficient so no
  term is ever subtracted, then deletes the terms $\equiv 0 \bmod 2^t$.
- **Bisect once, not twice.** Only $p_1$ is bisected; $p_0$ spills, and the leftovers become witnessed carries $v_0, v_1$ --
  *"each bisection requires constraints for the decomposition and range checks for the two halves ... we would like to avoid
  bisections as they are expensive."*
- **Fold the bound check into the gate that already has the value.** Folding $q' = q + f'$ into `ForeignFieldMul` saves
  4 rows per multiplication (12 -> 8); the 2-limb decomposition of $q'$ saves 2 more. $r'$ *cannot* be folded --
  *"This leaves only 2 remaining copyable cells."*
- **Lazy bound checks in a chain.** Intermediate foreign-field additions may exceed $f$; only the final result needs the
  $< f$ bound, taking a chain from $9n+11$ rows to $n+7$.
- **Inline a range check into a gate's spare cells**: *"Since our current row within the `Rot64` gate is almost empty, we can
  use it to perform the range check within the same gate."*

> **Where it stops.** The lazy-bound trick is sound only because wrapping an 88-bit limb in $\mathbb F_n$ would need
> $k \approx 2^{167}$ chained additions -- *"greater than Kimchi's maximum circuit length"*. **The same reasoning fails for
> multiplication**: $r$ after $k$ multiplications is $\approx f^k$, and $f^k > 2^t n$ for $k>2$, so every multiplication must
> check $a,b,q,r < f$. Note also the distinction the book is careful about: $q<f$ gives *correctness*, $r<f$ gives
> *uniqueness/canonicity* -- they are different obligations.

---

# Part IV -- Traps

The AIR trap catalogue (`air.md` Part X) mostly transfers: range checks without canonicity, selectors that are boolean
but not one-hot, advice not uniquely pinned, and small-field overflow all bite identically here.
What is specific to a gate-based system:

**A simple selector used non-linearly stops being combinable.**
halo2's automatic selector combining requires *"Every polynomial constraint involving a simple selector $s$ must be of the
form $s \cdot t = 0$, where $t$ is a polynomial involving no simple selectors"*
(`design/implementation/selector-combining.md:24-26`). Multiply two simple selectors together, or put one inside a lookup
input, and it must become a complex selector -- silently losing the packing, and with it the fixed-column saving that
motivated the design.

**A chained gate must be terminated.**
Kimchi's `Xor16` chains by making each gate's `Next` row the following gate's `Curr` row, which costs nothing -- but the
chain needs a final row whose inputs are all zero, done with copy constraints of a row to *itself*
(`kimchi/src/circuits/polynomials/xor.rs:47-52`). The source carries the warning verbatim:
*"Warning: don't forget to check that the final row is all zeros."* An unterminated chain is an unconstrained tail.

**Reserving degree headroom is free; discovering you need it later is not.**
`set_minimum_degree` exists precisely so a downstream argument can convert slack into fewer columns
(`halo2_proofs/src/plonk/circuit.rs:1182-1187`). Raising the cap inside a bracket costs nothing; crossing a bracket
doubles the extended-domain work for *every* polynomial (`degree.md` II.1).

**A hand-rolled fixed column cannot join the automatic combining.**
Manual selector packing is counterproductive in halo2 for exactly this reason (`selector-combining.md:106-110`) -- the
optimizer can only pack what it can see is a simple selector.
