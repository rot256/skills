# Deferring Work to Another Proof

*Emit an operation instead of executing it.
Co-processors, specialized machines, and the reconciliation you must budget for.*

**This is an optional reference.** It is the one family of optimization that is not local to a constraint system: it moves work out of the circuit entirely, into a second proof over a domain where the work is native.
Reach for it only after `techniques.md`, `air.md` / `plonkish.md` and `gates.md` are exhausted -- the fixed cost is large and the break-even is measured in thousands of operations.

## The Rule

> When a circuit repeatedly performs an operation whose cost is dominated by an **impedance mismatch** with its native
> domain -- a foreign field, a foreign group, a foreign word size -- do not optimize the emulation.
> Split the computation into (a) an **emission** in the host circuit, costing only the bandwidth of the operands, and
> (b) a **separate proof, in a domain where the operation is native**, that the emitted log was executed correctly.
> Then add (c) a **third, small proof** that the two encodings of the log agree.

The whole architecture is an amortization bet, and (c) is the part people forget to budget.

# The Emission

## Emit, Do Not Execute

The host circuit writes `(opcode, operands...)` into a dedicated block and takes the *result* back as **unconstrained witnesses**.
It sets no selectors, performs no validity checks, and does no reduction.

**Measured.** A non-native group operation emitted as two width-4 rows plus one arithmetic gate for a scalar decomposition check -- **~3 host rows per operation** -- against **~6,500 gates** for the same operation emulated in-circuit.
Ratio ~2000x.
The coordinate bindings cost zero gates because they are copy constraints on already normalized witnesses.

> **Where it stops.** The circuit no longer *knows* anything about the result: it is a raw witness. Every property you
> need -- on-curve, canonical encoding, coordinate in range -- must be re-established elsewhere or consciously dropped.
> A real deployed system drops all three in the host and re-establishes two; the third leaks, and the documented
> consequence is that aliased non-canonical coordinates in $[q, 2^{254})$ are accepted. **A deferral creates a soundness
> obligation, and if you do not discharge it somewhere you have created a gap, not an optimization.**

## Give the Deferred Type a Thinner State Model than the General One

If the host's general foreign-field type carries reduction state, bound tracking and range obligations, using it for the emission re-introduces exactly the machinery you are trying to delete.
Define a separate, stripped-down type for deferred operands so the compiler *cannot* accidentally emit the general path.

**Anything the host still checks is cost you failed to move.**

## Route Every Operation Through One Primitive, Including the Degenerate Ones

Make even the trivial cases -- adding the identity, multiplying by zero, the terminating equality -- go through the same queue primitive.
Uniformity is what lets the co-processor's relations be branch-free.

## Free Width Discrimination: Pay Half Price for Narrow Operands

If the operand decomposition is data-dependent, discriminate on it for free:

```
if (scalar.msb() < 128) { z_1 = scalar; z_2 = 0; }   // one half-width op
else                    { split_into_endomorphism_scalars(scalar, z_1, z_2); }
```

The row tracker then counts one narrow operation instead of two.
**A full-width operation costs ~2x the co-processor rows of a narrow one**, and the *protocol* can be redesigned to exploit it: draw Fiat-Shamir batching challenges short (127-bit) where full width is not needed for soundness.

> **Where it stops.** Only sound where the short challenge still gives adequate soundness. And note this makes the
> co-processor's *size* data-dependent, which is an information leak unless the trace is padded to a constant ("The Co-Processor Is a Fixed Cost, and for Zero-Knowledge It Must Be").

## Skip Degenerate Operations with Witnessed Flags, Not Branches

An operation with an identity operand or a zero scalar contributes **no** rows at all: a boolean column bears witness to the fact and the work is skipped.

> The motive is not only saved work. It *"dramatically simplifies the actual computations, by throwing out circumstances
> when there can be case logic"* -- which matters most when the co-processor is itself verified recursively.

Price: extra boolean columns plus the relations gating on them -- width traded for height and for the deletion of every edge case.

# The Co-Processor

## The Marginal Row Cost Is the Whole Economic Model

Write the row-count function down explicitly; it is six lines and it determines every design decision downstream:

```
rows_per_digit      = ceil(msm_size / ADDITIONS_PER_ROW)          // 4 additions per row
rows_for_all_rounds = (NUM_DIGITS_PER_SCALAR + 1) * rows_per_digit // 32 digits + 1 skew
num_double_rounds   = NUM_DIGITS_PER_SCALAR - 1                    // 31
rows_for_msm        = rows_for_all_rounds + num_double_rounds
precompute_rows     = 8 * m
```

| batch size $m$ | main rows $33\lceil m/4\rceil + 31$ | precompute rows $8m$ | transcript rows |
|---|---|---|---|
| 1 | 64 | 8 | 1 |
| 2 | 64 | 16 | 1 |
| 8 | 97 | 64 | 4 |
| 200 | 1681 | 1600 | 100 |

**Marginal cost ~16.5 rows per full-width point, ~8.25 per narrow one.** The 31 doubling rows are a **fixed** charge per batch regardless of size, so batching pays: 1 point costs 64 rows, 100 points cost 16.8 rows each.

> **Where it stops.** The fixed charge is per *contiguous run* of the batched opcode. Any other operation between two
> batchable ones terminates the batch and starts a new fixed charge. **Ordering your emissions is an optimization.**

## Disjoint Tables in One Trace, Wired by Multiset Equality

A machine trace has no copy constraints, so three logically separate tables -- transcript, precompute, main -- become **disjoint column groups of one trace**, communicating by emitting matching tuples into a shared grand product with an explicit domain-separation tag per tuple family.
Without the tags, tuples from different families with identical packed values produce identical fingerprints and can be substituted across families (`air.md` "Bus Separation: Tags, Widths, and the Three Aliasing Traps").

Price: the set relation's grand-product subrelation reaches degree 22 -- by far the highest in the flavor -- plus one permutation column and a log-derivative relation.

> **Where it stops.** You are paying a degree-22 relation to avoid a wiring permutation. That only wins because the three
> tables have *wildly different heights* (for a size-1 batch: 1, 8 and 64 rows), so packing them as parallel column
> groups makes the trace height the **max** rather than the **sum**. If the sections were the same height, one table
> would be better.

## Exploit a Layout Coincidence to Do Several Steps per Row

Choosing `ADDITIONS_PER_ROW == DIGIT_BITS` (both 4) is not an accident: the equality lets the same row structure serve the accumulation and the digit decomposition, and several parts of the implementation exploit it.
**Pick constants that make two unrelated loop bounds coincide, and a whole class of index arithmetic disappears** (`air.md` "Slide a Window Across `local || next` to Pack $k$ Steps per Row").

## Range-Check by Low-Degree Identity, When the Range Is Tiny

A 2-bit range check as a quartic identity, not a table read:

```
((s - 1)^2 - 1) * ((s - 2)^2 - 1) == 0
```

> *"Doing range checks this way vs permutation-based range check removes need to create sorted list + grand product
> polynomial. Probably cheaper even if we have to split each 4-bit slice into 2-bit chunks."*

That is why a 4-bit digit is *stored as two 2-bit halves*: the split exists purely to keep the range-check identity at degree 4.
Price: twice the slice columns, one degree-4 subrelation each.

> **Where it stops.** The identity has degree $2^k$ for a $k$-bit range. At $k = 4$ it is degree 16 and you have already
> lost to a lookup. Under a degree-8 budget the crossover is at 2 bits (`degree.md` "The Tax as a Formula: It Caps Window Sizes").

## Do Not Range-Constrain a Counter Another Argument Already Pins

A round counter in $\{0..7\}$ that is *never* range-constrained, with the argument written out:

> *"note that we don't actually range-constrain `round` (expensive if we don't need to!). We nonetheless can correctly
> constrain `round`, because of the multiset checks."*

The mechanism: `round` increments by 1 unless a transition flag fires, in which case `round == 7` and `round' == 0`.
A too-large `round` forces the transition flag to zero forever, which starves the multiset of a tuple emitted only at transition -- and the grand product then fails.

A companion micro-move: make the operation counter **count down** rather than up, for cheaper commitments.

> **Where it stops.** This is the most fragile trick here: it converts an explicit local constraint into a global,
> non-local one, and the argument must be re-audited whenever the multiset tuples change. Zero constraints, real
> maintenance cost.

## Trade Circuit Size for Relation Degree by Concatenating Columns

Permuting ~64 columns simultaneously means committing to all of them and a relation of degree $1 + 64 = 65$.
Instead, concatenate 16 logical columns into one polynomial and build 5 such polynomials; each group performs an independent permutation check at degree $1 + 5 = 6$.

> *"Concatenation trades circuit size (inexpensive) for relation degree (expensive). The 16x size increase is acceptable
> given the 9x degree reduction."*

Measured: a $2^{13}$ mini-circuit becomes $2^{17}$; 5 commitments instead of 64; degree 65 -> 7.

> **Where it stops.** Only where rows are genuinely cheaper than degree -- true for sumcheck provers, where per-round
> work is linear in rows but the univariate degree drives per-row cost. **In a FRI/AIR setting where blowup dominates,
> this trade inverts** (`degree.md` "Sumcheck / Multilinear: Degree Costs $d$ Scalars per Round, Not $2^{\lceil\log_2(d-1)\rceil}$ Columns").

## Split One Monolithic Relation into Selector-Gated Pieces so the Prover Can Skip

Decompose a 51-subrelation, degree-8 monolith into three 6-subrelation pieces plus a remainder, each with its own `skip()` predicate on a mutually exclusive selector.
Roughly 2/3 of the work is skipped per row.
No change to the AIR's meaning and no change to the verifier -- a purely prover-side reorganization.

> **Where it stops.** The split must preserve global subrelation *indices*, because the verifier batches subrelations by
> challenge power in exactly that order -- a brittle layout invariant. And it only pays when the selectors are genuinely
> sparse and mutually exclusive; splitting a relation whose selector is on everywhere loses the shared subexpressions.

# The Reconciliation, and the Bet

## Prove the Two Encodings Agree by Evaluating Both at a Challenge

The reconciling proof must never re-do the semantics.
It proves one scalar identity:
$$\text{acc} \;=\; \sum_i x^{\,n-1-i}\bigl(\text{op}_i + v\,a_i + v^2 b_i + v^3 c_i + v^4 d_i\bigr) \bmod q$$
while the co-processor opens the *same* columns as univariate evaluations at the same $(x, v)$.
Five distinguished wires have to be opened to establish the link.

Because the co-processor's field is larger than the host's, the identity is non-native for the reconciler, so it is proven the CRT way (`techniques.md` section 2): mod $2^{272}$ in 68-bit limbs **and** mod $r$ natively, plus range constraints, with $2^{272} r > 2^{514}$ exceeding the maximum possible value so the equation must hold over the integers.

**Price.** 81 witness columns -- 4 for the queue transcript, 13 for 68-bit limb decompositions, 64 for 14-bit microlimb decompositions -- and 2 rows per queued operation, on an even/odd cycle where even rows compute and odd rows store the shifted accumulator.

> **Where it stops.** This buys *equality of two encodings*, nothing more. It does not check the operands were valid
> (that is the co-processor's job) and it does not check the host's limbs were canonical -- which is exactly the gap "Emit, Do Not Execute"
> flags. And the batched-evaluation trick is sound only because $x, v$ are drawn **after** both tables are committed.

## Compare Commitments Instead of Hashing Data

Passing data between circuits as public inputs forces in-circuit hashing of the whole payload.
Passing **commitments** instead makes the verification $O(1)$, independent of data size.
Dynamic reads into the data column go through a log-derivative lookup at **one row per read, no copy constraint back**, so prover cost scales with the number of *reads* rather than the total data size.

Price: per data column, a value column, a read-count column, an inverses column and a selector; four subrelations (inverse correctness on read rows, on write rows, the lookup identity, and read-count locality).

**The compounding move:** the commitment equality that replaces the hash is itself an equality of *group elements* -- and group elements are cheap precisely because "Emit, Do Not Execute" already made them cheap.
**Cheapening one operation changes which optimization is worth doing next.**

> **Where it stops.** The data still occupies columns of the producing circuit; you save the *hash*, not the *storage*.

## The Co-Processor Is a Fixed Cost, and for Zero-Knowledge It Must Be

| component | fixed size |
|---|---|
| co-processor trace | $2^{15}$ rows, 86 wires / 88 witness / 119 total entities |
| reconciler mini-circuit | $2^{13}$ rows (4,096 operations max), 81 wires |
| reconciler full circuit | $2^{17}$ rows after 16x concatenation ("Trade Circuit Size for Relation Degree by Concatenating Columns") |
| merge proof | 41 field elements |

**Capacity.** At ~16.5 rows per full-width point, $2^{15}$ rows absorb **~1,900 full-width operations** (or ~3,900 narrow ones); the reconciler caps at 4,096.
One instance therefore covers roughly 1,900--4,000 deferred operations.

**The size must be constant.** Appending at a *fixed* offset means the merged table has the same total size regardless of how many operations were actually used.
A prover-supplied shift would leak the private extent, so pinning it is required for zero-knowledge, and the verifier derives the offset itself rather than reading it from the proof.

> **Where it stops.** Below capacity, unused rows are pure waste; above it you need a second instance.

## The Break-Even

- Emulated in-circuit: **~6,500 gates** per operation.
- Deferred: **~3 host rows** + ~16.5 co-processor rows + 2 reconciler rows.
- Fixed cost in committed witness cells: co-processor $2^{15}\times 88 \approx 2.9$M; reconciler $2^{13}\times 81 + 5\times 2^{17} \approx 1.3$M; **total ~4.2M cells**.
- At 15 witness columns in the host, 4.2M cells ~ 280K host rows ~ **43 emulated operations**.

**Break-even ~40--50 operations.** A single recursive verification needs 76--78, so the architecture pays for itself on the first one and everything after is nearly free.
That is the only reason it exists.

The measured trajectory is worth reading as a lesson in ordering:

| approach | operations per circuit | notes |
|---|---|---|
| naive emulation | 55 + 21 full-width | circuit exceeds 512K gates |
| deferral | 60 narrow + 21 full-width | ~100 co-processor rows per circuit |
| deferral + folding | 57--72 narrow | the final batch is pushed out entirely |

Note the second-order move in the last row: once the operations are cheap, the *next* optimization is to reduce their number, and to make the survivors narrow ("Free Width Discrimination: Pay Half Price for Narrow Operands").

# The Checklist

1. **Find the mismatch.** Cost per operation in the host must vastly exceed the cost of merely *writing down* its operands -- here, ~6,500 gates against 7 field elements.
2. **Make the emission a pure log.** No validity check, no range check, no reduction.
   Give the deferred type a stripped-down state model so the general machinery cannot creep back in ("Give the Deferred Type a Thinner State Model than the General One").
3. **Take the result back as unconstrained advice** ("Emit, Do Not Execute").
   That is what makes the emission $O(\text{operand size})$ rather than $O(\text{operation})$.
4. **Write down which obligations you dropped**, and where each is re-established.
   The ones you cannot place are soundness gaps, not savings.
5. **Budget the reconciliation.** Two encodings of one log must be proven equal, and the cheap way is a random-challenge batched evaluation of both ("Prove the Two Encodings Agree by Evaluating Both at a Challenge") -- but that third proof is a whole circuit in its own right.
   Count it.
6. **Compute the break-even in committed cells, not in operations** ("The Break-Even"), and check your workload clears it by a comfortable margin.
   Below capacity the fixed cost is pure waste.
7. **Pin the size** if the workload is private ("The Co-Processor Is a Fixed Cost, and for Zero-Knowledge It Must Be").
