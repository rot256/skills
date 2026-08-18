# AIR / PLONKish optimization

*A field manual for trace-based constraint systems.*

Non-obvious techniques for making an execution trace smaller, collected by reading the constraint systems of
OpenVM, SP1, Plonky3, Plonky2, stwo, Cairo/Stone, Miden, Valida, Jolt, Binius, halo2, Kimchi, ZisK and powdr.
Every entry carries the mechanism, the price, and the condition under which it stops working.
Cross-arithmetization moves live in `techniques.md`; R1CS in `r1cs.md`.

$$\text{cost} \;=\; \underbrace{(w_{\text{pre}} + w_{\text{main}} + w_{\text{perm}})}_{\text{width}} \times \underbrace{\lceil h \rceil_{\text{pad}}}_{\text{height}} \qquad\text{scaled by}\qquad \text{blowup} \approx d - 1$$

Prices are written $\langle\text{columns},\ \text{degree}\rangle$ per row, plus interactions where they matter.
Under a metric that charges only width, or only interactions, read the components rather than the product --
**which component is scarce changes the answer, and it changes it a lot** (I.1).

## The axioms

**You pay for area, not for constraints.**
A constraint is a polynomial identity checked on every row; adding one costs prover time but *no trace cells*.
A column costs `height` cells whether or not the row uses it.
This is the deepest difference from R1CS, where a constraint is a row and therefore is the unit of cost.
Corollary: an AIR is golfed by deleting **columns**, not by deleting constraints -- and "one more constraint, one fewer column" is almost always a win.

**Degree is a global maximum, and it is quantized.**
The whole system pays for $\max_j \deg C_j$: one stray high-degree constraint re-prices every other one (IV.1).
Below that maximum, extra degree is *already paid for* -- see IV.2, which is where most of the free money is.

**The window is two rows.**
`local` and `next`, nothing else (Plonky3 `symbolic/expression.rs:129`: "expressions cannot span more than two rows"; Kimchi `Curr`/`Next`).
halo2 relaxes this to arbitrary rotations *within a region*, and that difference drives its whole gadget style (IX).
Anything further away goes through a shift register (III.5) or a bus (III.7).

**Interactions are a third currency, priced separately from columns.**
In a materialized-permutation backend an interaction costs permutation columns; in a GKR backend it costs a global row budget and a power-of-two-padded count; in every backend it costs message width.
OpenVM meters one interaction at $\approx 9.06$ field elements of prover memory (`openvm#2764`), and caps the total at the field order because multiplicities wrap (`arch/vm.rs:923`).

**Padding is not free, and it is not empty.**
The height you pay for is the padded height, and the padding rows are *prover-chosen trace*, not zeros by law.
Every trick in Part V that gates a bus on `is_real` is one forgotten constraint away from a padding-row oracle (X.2).

**Free means verifier-evaluable, or linear in what is already committed.**
Those are the only two kinds of free column (I.5). Everything else is witness.

### Scope

**Parts I--VIII are the row-based AIR model**: a trace of columns, transition and boundary constraints over a
two-row window, no copy constraints, cross-row and cross-chip wiring done by lookups/permutation buses.
That is Plonky3, SP1, OpenVM, stwo, Cairo/Stone, Miden, Valida, RISC Zero, ZisK.
**Part IX is the PLONKish model** -- rotations, copy constraints, custom gates, wire budgets, selector combining --
which is a genuinely different cost model (halo2, Kimchi, Plonky2), kept separate rather than annotated in place.
**Parts X and XI (traps, and knowing when to stop) apply to both.**
Where a trick crosses over, the tag under its heading says so.

---

# Part I -- The cost model, and how to read it

The single most common way to waste a week is to optimize the wrong term of the product.

## I.1 The area law, and which term binds

Universal

The optimand is cells. SP1 collapses a chip to one scalar and stores it in a table:

```rust
pub fn cost(&self) -> u64 { (self.preprocessed_width() + self.width()) as u64 }
```
(`sp1/crates/hypercube/src/chip.rs:154-161`; cells = `total_width * height` at `:323-332`).
The frozen price list is worth internalizing as calibration -- `Range 3`, `Byte 13`, `Program 17`, `MemoryLocal 20`,
`Addi 30`, `Add 33`, `AluX0 34`, `Lt 44`, `Bitwise 51`, `Mul 82`, `ShaCompress 206`, `Global 241`, `DivRem 246`,
`Poseidon2 348`, `KeccakPermute 2640` (`sp1/crates/core/executor/src/artifacts/rv64im_costs.json`).

**But there are two ceilings, and they bind on different shapes.** SP1 cuts a shard on whichever hits first:

```rust
pub const ELEMENT_THRESHOLD: u64 = (1 << 28) + (1 << 27);   // 402,653,184 cells
pub const HEIGHT_THRESHOLD:  u64 = 1 << 22;                 // 4,194,304 rows
```
(`sp1/crates/core/executor/src/opts.rs:11-15`), where `trace_area` is a **sum over chips** of width x rows and
`max_height` is the **max over chips** (`vm/shapes.rs:88-243`). Writing the shard's *effective width* as

$$W_{\text{eff}} \;=\; \frac{\sum_i w_i h_i}{\max_i h_i}$$

the area ceiling binds iff $W_{\text{eff}} > 402\text{M}/4.19\text{M} \approx 96$, and the height ceiling binds otherwise.
A pure-ADD shard has $W_{\text{eff}} = 33$: it is cut at 4.19M rows having spent $138\text{M}$ cells, **34% of its area budget**.

**Read that carefully, because the obvious corollary is false.** In the height-bound regime, deleting a column does *not*
buy shard capacity -- the cut still lands at 4.19M rows of the tallest chip, so you do not fit more instructions and you
do not emit fewer shards. It does still buy **cells**, and cells are what the commitment is priced on (I.3): a
$33 \to 25$ column Add is 24% less committed data in either regime. The correct reading is
*which resource is binding has changed, so width work has stopped compounding* -- past that point the next real win is
fewer rows (V.11, VI.1), fewer interactions (I.4), or a taller allowed shape, not another column.
And note $W_{\text{eff}}$ is a property of the whole shard, not of one chip: a single narrow chip among many wide ones
does not move it.

OpenVM's oracle instead charges `total_width()`, which **includes** the permutation columns
(`metered_cost.rs:20,77-82`), and its metrics doc names the gap explicitly: `main_cells_used`
("Only main trace cells, not preprocessed or permutation trace cells") versus `total_cells_used`.
**The difference between those two numbers is your interaction bill.**

> **Where it stops.** SP1's formula omits permutation width because SP1 v5 has no permutation trace at all
> (LogUp-GKR consumes main/preprocessed directly). Porting that cost model to a system with a materialized
> permutation trace understates interactions by the largest single term. Always ask which of the three widths your backend commits.

## I.2 Gas is two-term: area plus constraint complexity

Universal

SP1 meters programs with two independently-calibrated per-AIR weights:

```rust
// 0.3 * trace_area + 0.1 * complexity
let gas = (3 * trace_area + complexity) / 10;
```
(`sp1/crates/core/executor/src/vm/gas.rs:97-98`).
The two disagree in exactly the interesting places: `Byte` = 13 area / **0** complexity, `Program` = 17 / **0**,
`DivRem` = 246 / 351, `KeccakPermute` = 2640 / 2859.

**Lookup tables are pure area with zero constraint cost.** That is the quantitative reason a big shared table is a
good trade and a wide arithmetic chip is not: they are charged on different axes.

> **Where it stops.** The 3:1 ratio is a regression against one prover on one machine
> (`opts.rs:26-34` warns it "must not be changed without re-validating"). A different memory-bandwidth profile re-weights it.

## I.3 Padding: a cliff in one backend, a step in another

Universal

OpenVM pads every AIR to `next_power_of_two_or_zero` individually (`metered/segment_ctx.rs:253-266`).
SP1 v5 pads to `n.next_multiple_of(32).max(16)` (`hypercube/src/util.rs:57`).
At 1000 uses both cost 1024 rows. **At 1025 uses OpenVM jumps to 2048 (+100%) and SP1 goes to 1056 (+3%).**

SP1 bounds *all* padding in a cluster with a static assertion:
`assert!((32 * total_columns) <= MAXIMUM_PADDING_AREA)` with `MAXIMUM_PADDING_AREA = 1<<18`
(`riscv/mod.rs:1871-1878`) -- 262,144 cells, under 0.07% of the shard budget.
The enabling structure is jagged/stacked commitment: total area is summed across chips and padded **once**,

```rust
let main_area = chips.iter().map(|air| air.width() * air.num_rows(record)).sum::<usize>()
    .next_multiple_of(1 << log_stacking_height);
```
(`hypercube/src/prover/simple.rs:33-37`) -- global waste $\leq 2^{21}$ out of 402M, i.e. **0.5%**, versus per-chip
power-of-two padding which for a 30-chip cluster approaches 50% per chip.

> **Where it stops.** Under a classical univariate multi-matrix STARK you are on the power-of-two cliff, and the
> merge/split decisions of VI.2 stop being tuning and become the dominant term. Know which you are in before
> reasoning about "a chip used 1000 times".

## I.4 Interactions are a hard budget, not a soft one

AIR with a bus

OpenVM segments on interaction count with the ceiling set to the **field order**:
`max_interactions: <Val as PrimeField32>::ORDER_U32` (`arch/vm.rs:923`), enforced at `segment_ctx.rs:466-476`.
Beyond it multiplicities wrap and the argument is unsound, not merely expensive.
Interaction cells are metered per row per interaction: `interaction_cells += padded_height * interactions`
(`segment_ctx.rs:445`).

A chip with 30 interactions per row and $2^{20}$ rows burns $2^{25}$ of that budget alone.
**Main columns hit a memory limit; interactions hit a field-order limit *and* a memory term.**
That asymmetry is why "reduce distinct interactions per row" usually beats "reduce main columns".

In a GKR backend the count is padded to a power of two **machine-wide**:

```rust
let max_interaction_arity = chips.iter().flat_map(|c| c.sends().iter().chain(c.receives()))
    .map(|i| i.values.len() + 1).max().unwrap();
let beta_seed_dim = max_interaction_arity.next_power_of_two().ilog2();
let num_interaction_variables = num_interactions.next_power_of_two().ilog2();
```
(`sp1/crates/hypercube/src/logup_gkr/prover.rs:78-97`).
These are a **max** and a **sum over the whole shard**: one chip with a 17-field interaction forces
`beta_seed_dim = 5` for everybody, and a cluster total of 257 interactions makes everyone pay for 512.

> **Where it stops.** You cannot fix this locally. Keep the widest interaction's arity just under a power of two,
> and check the cluster's total against the next power of two *before* adding a chip.

## I.5 The four tiers of "free", ordered by price

Universal

Not all free columns are free in the same currency. Cheapest first:

| tier | mechanism | prover cost | verifier cost | degree |
|---|---|---|---|---|
| **compile-time constant** | a literal in the constraint | 0 | 0 | 0 |
| **periodic column** | $K(x) = \tilde k(x^{N/k})$, verifier-evaluable | 0 | one eval of a degree-$k$ interpolant | $N - N/k$, i.e. **less than a witness column** |
| **preprocessed / fixed** | committed once at setup | commitment, reusable across proofs | opening | 1 |
| **virtual / derived** | affine (or low-degree) in committed columns | re-expanded at every use | 0 | $\deg$ of the expression |

The periodic-column degree is the underrated part. Plonky3 computes it exactly:

```rust
p => trace_len - trace_len / p,      // vs trace_len - 1 for a main column
```
(`plonky3/air/src/symbolic/variable.rs:56-69`). For $p = 2$ that is **half a trace-degree unit** cheaper than a witness column.

Cairo declares seven periodic columns for Pedersen points and Poseidon round keys, with *different periods per column*
(`column_step` 16 for full-round keys, 2 and 4 for partial-round keys, `cpu_air_definition7.inl`).
Binius's analogue is the *structured* column, whose MLE is closed-form (`m3/src/builder/structured.rs`) --
an incrementing counter costs zero commitment.

> **Where it stops.** Periodic columns need a power-of-two period dividing the trace length
> (`plonky3/commit/src/periodic.rs:8-13`) and public values -- no witness can hide there.
> The step mechanism also *fixes your row layout*: the column is only defined on rows $\{i \cdot \text{step}\}$,
> so the hash trace must be laid out to land on them.

## I.6 Measure with the tool the system already ships

Universal

Every mature framework has a static cost oracle; use it before guessing.
stwo's `InfoEvaluator` runs your `evaluate` with no trace at all and returns column counts per interaction,
constraint count, preprocessed columns, per-relation logup counts, and an arithmetic-op breakdown by field type
(`constraint_framework/src/info.rs:19-132`); `Display for FrameworkComponent` prints rows, constraints, degree bound
and total felts (`component.rs:248-263`). That is how blake derives its trace sizes (`blake/air.rs:78-88`).
Plonky3 exposes the symbolic degree walker; powdr scores every pass on the triple
(`main_columns`, `constraints`, `bus_interactions`) and prints `before -> after (Nx)` (`autoprecompiles/src/evaluation.rs:98-185`).

> **Where it stops.** These count *ops and columns*, not degree (stwo's own note: `InfoEvaluator` needs
> `ExprEvaluator` + `degree_bound` for that) and not padding. A width win that padding eats is the single most
> common false positive -- see the measured negative results in VI.7.

---

# Part II -- Column engineering: what one row can do

The unit of cost is a column, so every entry here is a way to have one fewer of them.

## II.1 Never commit a linear function of committed columns

Universal

The rule, stated by Plonky3's Poseidon2 columns doc:

> *"Because the matrix multiplications are linear functions, we need only keep auxiliary columns for the S-box computations."*
> (`poseidon2-air/src/columns.rs:4-10`)

In `eval_partial_round`, only `state[0]` is bound to a column; the internal MDS is applied to the *expression* array
and carried into the next round uncommitted (`poseidon2-air/src/air.rs:288-295`).
Price: `PARTIAL_ROUNDS * (1 + REGISTERS)` columns instead of `PARTIAL_ROUNDS * WIDTH`.
SP1's degree-3 Poseidon2 goes further and commits *nothing* per round beyond the round's input state, folding both the
round constant (degree 1) and the following linear layer (degree 1) into the $x^3$ constraint --
`8*16 + 16 + 19 + 16 = 179` columns for a 16-wide 8+20-round permutation, against 448 for one-state-per-round
(`sp1/crates/hypercube/src/operations/poseidon2/{air.rs:82-138,permutation.rs:45-54}`).
Binius states the same rule as its whole cost model: linear `add_computed` is virtual, non-linear becomes a commitment
(`m3/src/builder/table.rs`).

> **Where it stops.** Twice.
> (i) The expression DAG grows: a 13-round partial chain is a dense linear combination of 13 columns $\times$ width 16,
> and evaluation time grows even though degree does not.
> (ii) You **must** re-bind after each nonlinear step or degree compounds as $\alpha^r$.
> The moment an expression is fed to something that must be `assert_bool`'d, or used as an interaction multiplicity
> where degree 1 is required, materialize it.

## II.2 Derive one value from a total that is already pinned

Universal

If $n$ values are tied by a constraint that something else already enforces, witness $n-1$ and let the last be an expression.

OpenVM's JALR stores only the 3 high limbs of `rd`; the low limb is
`least_sig_limb = from_pc + DEFAULT_PC_STEP - composed`, and its correctness is enforced **by the range check alone**:

> *"if `rd_data` does not match the expected limb, then `least_sig_limb` becomes the real `least_sig_limb` plus the
> difference ... In that case, `least_sig_limb` >= 2^RV32_CELL_BITS."* (`jalr/core.rs:99-107`)

AUIPC does the mirror image, deriving the *most* significant PC limb as
`pc_msl = (from_pc - intermed_val) * 2^{-24}` and reusing `rd_data[0]` as `pc_limbs[0]` (`auipc/core.rs:96-98`).
Measured instances of the same move: OpenVM deleted `prev_timestamp` from every memory access, recomputing it as
`timestamp - 1 - compose(timestamp_lt_aux)` -- `MemoryReadAuxCols` **3 -> 2**, `MemoryWriteAuxCols` **7 -> 6**,
plus one equality constraint removed per access (`openvm#3069`); and deleted `buffer_ptr`/`input_ptr` in favour of their
own limbs, **"Saves 68 columns"** (`openvm#3087`).

> **Where it stops.** Two preconditions, and the second is the one people drop.
> (i) The total must be *independently* constrained -- JALR relies on "only `from_pc` in $[0, 2^{\text{PC\_BITS}})$ is
> allowed by program bus" (`jalr/core.rs:116`).
> (ii) The range check on the derived value must be **tight enough that any error overflows it**.
> If the check is on a *pair* and the partner slot is loose, the argument collapses silently.

## II.3 Split a limb by committing one half

Universal

To split $a$ at bit $r$, commit only the high part and define the low part as an expression:

```rust
fn split_unchecked(&mut self, a: E::F, r: u32) -> (E::F, E::F) {
    let h = self.eval.next_trace_mask();
    let l = a - h * E::F::from(BaseField::from_u32_unchecked(1 << r));
    (l, h)
}
```
(stwo `blake/round/constraints.rs:107-113`) -- 1 column, 0 constraints, versus 2 columns plus a recomposition constraint.
SP1's `U16toU8Operation` is the same move at word scale: only the *low* byte of each u16 limb is a column, the high byte
is `(limb - low)/2^8` -- **4 columns per 64-bit word instead of 8** (`operations/u16_operation.rs:45-53`).

> **Where it stops.** "Caller is responsible for checking that the ranges of `h*2^r` and `l` don't overlap"
> (stwo, verbatim). With only one half committed, *nothing* pins the split -- an adversary shifts value between $l$ and $h$
> unless **both** outputs are separately range-constrained. In blake that happens because the two halves go into two
> different-width XOR lookups; in SP1 the `_safe` variant adds the range checks and the `_unsafe` variant documents at each
> call site which downstream lookup discharges the obligation (`operations/bitwise_u16.rs:74-79`).

## II.4 Carries as expressions, asserted boolean -- zero carry columns

Universal, small-limb

Do not witness the carry. Define it by dividing by the base (a field constant) and constrain only that it is boolean:

```rust
for i in 0..WORD_SIZE {
    carry = (a[i] + b[i] - cols.value[i] + carry) * base.inverse();
    builder_is_real.assert_bool(carry);
}
builder.slice_range_check_u16(&cols.value.0, is_real);
```
(SP1 `operations/add.rs:63-69`). Price: 4 result columns, **0 carry columns**, 4 degree-2 constraints, 4 range lookups.
Subtraction is the identical gadget with limb $2^{16}-1-b_i$ and the chain **seeded to 1** (`operations/sub.rs:56-64`) -- zero extra cost.
With more addends the carry stops being boolean and gets a *range check* instead, still as an expression:
`Add4`/`Add5` feed `carry_limbs` straight into `slice_range_check_u8` (`operations/add4.rs:79-87`).

> **Where it stops.** Booleanity of the carry alone proves nothing: soundness needs the *result* limbs range-checked and
> the inputs already in range. The bound is $k \cdot 2^b + \text{carry} < p$ for $k$ addends of $b$-bit limbs.
> And **never let a value you must `assert_bool` have degree > 1** -- OpenVM keeps ADD and SUB on two separate carry chains
> for exactly this reason: *"We explicitly separate the constraints for ADD and SUB in order to keep degree cubic. Because we
> constrain that the carry (which is arbitrary) is bool, if carry has degree larger than 1 the max-degree constrain could be
> at least 4."* (`base_alu/core.rs:103`).

## II.5 The comparison bit *is* the carry that falls out of the window

Universal

Do not build a comparator. Decompose the shifted difference into range-checked limbs and read the answer off the top:

```rust
let intermed_val = y_minus_x + ((1 << max_bits) - 1);
let check_val    = lower + out * (1 << max_bits);
builder.when(condition).assert_eq(intermed_val, check_val);
builder.assert_bool(out);
```
(OpenVM `is_less_than/mod.rs:122`). `AssertLtSubAir` is literally `IsLtSubAir` with `out = 1` (`:66`) -- the strict
assertion and the boolean output are the same gadget.
The one-limb version is even cheaper: SP1's `U16CompareOperation` is **one column**, one boolean constraint and one lookup:
`diff = a - b + bit*2^16`, range-checked to 16 bits (`operations/u16_compare.rs:57-71`) -- and it is the atom of every
comparison in that machine.

> **Where it stops.** The hard wall of the whole comparison family:
> $$2^{\text{max\_bits}+1} \leq p \quad\Longrightarrow\quad \text{max\_bits} \leq \lfloor \log_2 p\rfloor - 1 = 29 \text{ on BabyBear}$$
> because the "negative" case puts $y-x-1$ in $[p - 2^{b}, p-1]$, which must stay disjoint from $[0, 2^{b})$
> (`openvm/crates/circuits/primitives/src/assert_less_than/mod.rs:79`, asserted at `:92`).
> `out` must be asserted boolean **unconditionally**, or a non-boolean `out` shifts the window.
> And the gadget *assumes* its inputs are already range-checked -- see VIII.22 for the [High] that cost.

## II.6 The prefix-sum "first differing limb" family

Universal

The workhorse for multi-limb comparison, equality, and canonicity. Witness a one-hot marker for the first differing
position; the **running prefix sum of the marker** is the "already found a difference" flag, so it costs no column:

```rust
for i in (0..NUM_LIMBS).rev() {
    let diff = (c[i] - b[i]) * (2*cmp_result - 1);
    prefix_sum += marker[i];  builder.assert_bool(marker[i]);
    builder.assert_zero(not(prefix_sum) * diff);        // all higher limbs equal
    builder.when(marker[i]).assert_eq(diff_val, diff);  // pin the difference
}
builder.assert_bool(prefix_sum);
builder.when(not(prefix_sum)).assert_zero(cmp_result);
```
(OpenVM `less_than/core.rs:101`). Price: `NUM_LIMBS` markers + 1 `diff_val`, degree 3, replacing `NUM_LIMBS` comparators.
SP1's 64-bit LT does the same and spends **one lookup total** on the selected pair (`operations/slt.rs:213-257`);
its canonicity gadget `FieldLtCols` is $n+2$ columns and one `LTU` byte lookup (`operations/field/range.rs:110-129`);
Valida's version is 4 flags + 9 bits + 1 inverse = **14 columns** for a 32-bit compare instead of 33 bits
(`alu_u32/src/lt/stark.rs`).

**Two free by-products.** The flags already encode equality, so `is_eq = 1 - sum(flags)` costs nothing --
SP1's branch chip gets all six of BEQ/BNE/BLT/BGE/BLTU/BGEU from one comparison
(`control_flow/branch/air.rs:164-177`). And signed comparison is unsigned comparison after an *arithmetic* sign flip:
`b_compare[top] += is_signed * 2^15 - 2^16 * b_msb` (`operations/slt.rs:139-144`) -- no second gadget.

> **Where it stops.** Both directions are load-bearing and are independently forgettable.
> The `not(prefix_sum)` chain stops a prover pointing at a *too-low* limb; a `diff_val != 0` proof stops it pointing at an
> *equal* one (`assert_one(not_eq_inv * (b - c))`, or the range-check form of V.8). `assert_bool(prefix_sum)` is what
> forbids two markers. The marker is *not* constrained to be at the lowest index or to be unique -- OpenVM says so out loud
> ("there might be multiple valid inv_marker if a != b", `branch_eq/core.rs:91`) -- which is fine for a boolean output and
> **wrong if you want to read off the differing index**.

## II.7 Selector encodings, cheapest first

Universal

Five encodings of "which of $n$ cases is this row", in increasing column-thrift and increasing degree.

**(a) One-hot whose sum *is* `is_valid`.** Zero columns for `is_valid` and zero for the opcode:

```rust
let is_valid = flags.iter().fold(ZERO, |acc, &f| { builder.assert_bool(f); acc + f.into() });
builder.assert_bool(is_valid);
let expected_opcode = flags.iter().zip(Opcode::iter()).fold(ZERO, |a,(f,op)| a + f * op as u8);
```
(OpenVM `base_alu/core.rs:84,142`; SP1 `alu/sr/mod.rs:335-347` carries the soundness argument in a comment).
`assert_bool` on the *sum* buys mutual exclusion in one degree-2 constraint regardless of $n$ -- versus $\binom n2$
pairwise products. Both `is_valid` and `opcode` stay degree-1 **expressions**, so they can be interaction multiplicities.

**(b) Drop the last flag.** `last = is_valid - sum(others)`, plus one `assert_bool` on it (`mod-builder/src/core_chip.rs:137`).
$-1$ column. Needs an independent degree-1 `is_valid` column -- circular with (a).

**(c) Simplex / `Encoder`: $k$ columns hold $\binom{k+d}{d}$ selectors at flag-degree $d$.**
Flags are lattice points $pt \in \mathbb N^k$ with $\sum pt_i \le d$, and the indicator is a multivariate falling-factorial
product (`openvm/crates/circuits/primitives/src/encoder/mod.rs:87`).
SHA-256's 18 row-index flags fit in **5 columns at $d=2$**; SHA-512's 22 in 6. OpenVM's loadstore hand-rolls the same
shape: 14 (opcode, shift) pairs in **4 columns**, as the degree-2 monomials of a $\{0,1,2\}$-simplex (`loadstore/core.rs:104`).

**(d) Suffix-sum bit packing.** Cairo commits the *suffix sums* of the 15 flag bits in one column, recovering each bit as
$f_i = \tilde f_i - 2\tilde f_{i+1}$ -- 1 column and 2 constraint families instead of 15 columns and 15 booleanity constraints
(Cairo §9.4; Stone `cpu_air_definition11.inl`, `opcode_range_check/{bit,zero}`).

**(e) Binary tag columns.** $N$ columns and degree $N$ for $2^N$ tags, with the equality indicator a product of literals
(`zkevm-circuits/gadgets/src/binary_number.rs`). Crossover against one-hot: use binary when $|T|$ is large and the tag gates
*few* constraints; use one-hot when it gates many high-degree ones.

> **Where it stops.**
> (a) works only because each flag is separately boolean -- drop that and $(2,-1)$ satisfies $\sum f = 1$ happily
> (Valida's source flags exactly this).
> (c) is the dangerous one: **every use of a flag pays $+d$ degree**, so a degree-2 `is_valid` cannot be a bus multiplicity
> (OpenVM keeps `is_valid` and `is_load` as separate degree-1 columns for that reason, `loadstore/core.rs:55`);
> and the "sum of unused lattice points is zero" constraint is mandatory -- skip it and a prover sits on an unused point where
> **all flags evaluate to 0**, silently disabling every gated constraint (`encoder/mod.rs:214`).
> (d) needs the packed value's uniqueness ($P > 2^{63}$ for Cairo) and independent range checks on the offsets.
> (e) needs explicit exclusion gates when $|T|$ is not a power of two, or the prover invents a tag no branch handles.

## II.8 Buy back flag degree with prefix helper columns

Universal, one-hot dispatch

Under one-hot dispatch the governing identity is brutal and exact:
$$\deg(\text{flag}) + \deg(\text{rule}) \;\le\; \text{budget}$$
Miden states the consequence flatly: with 7 opcode bits, *"the degree for both of these flags is 7. Since degree of
constraints in Miden VM can go up to 9, this means that operation-specific constraints cannot exceed degree 2."*

The fix is not to raise the budget but to commit *shared opcode prefixes* as columns and use them as degree-1 stand-ins:

```rust
e_0 - b_6*(1-b_5)*b_4 = 0     // deg 3  -> flags with prefix 101 cost 7-2 = 5
e_1 - b_6*b_5         = 0     // deg 2  -> flags with prefix 11  cost 5-1 = 4
```
and then **lay out the opcode space by degree class** (Miden `air/src/constraints/op_flags/mod.rs`):

| prefix | ops | helper | flag degree | headroom for the rule (budget 9) |
|---|---|---|---|---|
| `0xxxxxx` | 64 | -- | 7 | 2 |
| `100xxx-` | 8 | -- | 6 | 3 |
| `101xxxx` | 16 | `e_0` | 5 | 4 |
| `11xxx--` | 8 | `e_1` | 4 | 5 |

A third prefix then comes out **linear and free**: $b_6(1-b_5)(1-b_4) = b_6 - e_1 - e_0$.
Class flags get the same treatment -- "does this shift the stack right?" is the prefix $(1-b_6)b_5b_4$ plus two
exceptions (degree 6), not a sum of sixteen degree-7 one-hot flags.
And build all the flags from a *shared nest* of partial products: `b32 -> b321 -> b3210`, `b654321`,
$\approx 72$ multiplications for 96 op flags instead of $\approx 450$ (`op_flags/mod.rs`, `OpFlags::new`).

> **Where it stops.** The saving applies only to opcodes that *share the prefix*, so this is a global opcode-assignment
> problem decided before a single constraint is written: expensive instructions must be co-located under a short prefix,
> and that subtree is then only $2^{7-|\text{prefix}|}$ wide. Miden pays the address-space cost visibly -- the low-degree
> groups hold 8 and 16 opcodes, not 32 and 16 -- and the unused trailing bits must be **pinned**
> (`when(b6 - e1 - e0).assert_zero(b0)`), or opcode 64 and 65 become the same flag.

## II.9 Constants from flags, not from columns

Universal

Once a one-hot flag vector exists, any per-row constant is a linear combination of it, for zero columns.

Keccak needs a different 64-bit round constant per round and stores **neither** a constant column nor a preprocessed one:

```rust
let rc_bit_i: AB::Expr = local.step_flags.iter().zip(RC_BITS.iter())
    .filter(|(_, rc_bits_r)| rc_bits_r[i] != 0)
    .map(|(&step_flag, _)| step_flag.into()).sum();
```
(`plonky3/keccak-air/src/air.rs:175-185`) -- the `filter` runs at *constraint-construction* time, so the emitted
expression is a bare sum of the flags whose RC bit is 1. Degree 1.
OpenVM generalizes it: `Encoder::flag_with_val` produces $\sum_r \text{flag}_r \cdot \text{const}_r$, which is how SHA-2
reads its 64 round constants -- 128 preprocessed cells per row-group avoided (`encoder/mod.rs:186`, `sha2-air/air.rs:557`).

> **Where it stops.** The expression sums over *every* row of the block, so its symbolic size is `ROUND_ROWS` terms and it
> inherits the flag degree -- it can only appear where you have $\ge d$ degrees of headroom. Past ~64 rounds a lookup wins.
> And it needs a one-hot vector to already exist for another reason: committing flags *just* to do this is a loss against a
> periodic column (I.5).

## II.10 One column, two meanings, on disjoint row ranges

Universal

Two variants, both real savings.

**Union layouts.** OpenVM's `Sha2RoundCols` and `Sha2DigestCols` share their first three fields byte-for-byte and
reinterpret the tail; the AIR borrows whichever view it needs from the same slice
(`sha2-air/src/columns.rs:19`, `air.rs:317-321`). Trace width is $\max$, not the sum.

**Range-disjoint reuse.** A column is message-schedule carries on rows $\ge 4$ and free scratch for a wrapper chip on
rows $0..4$ -- *"Note: `carry_or_buffer` is left unconstrained on rounds 0..3"* (`sha2-air/src/columns.rs:87`).
The gating predicate is itself free: `is_row_4_or_more = is_round_row - is_first_4_rows`, a **difference of two existing
flags**, not a new column.
Cairo does the classic version: on a `jnz`, `res` is Undefined Behavior, so it holds the inverse witness $v = \text{dst}^{-1}$
instead -- an entire column of size $N$ disappears (Cairo §9.5, optimization 1).

> **Where it stops.** "Unused" must mean **unconstrained**, not merely semantically irrelevant: any constraint that reads
> the aliased column unconditionally now sees the other meaning. The row-type flags must be pinned to the row *index*
> (OpenVM does it via the encoder), or a prover picks the interpretation that suits it. And the sub-AIR must **publish**
> which rows it leaves unconstrained -- OpenVM's does; Cairo can only do it where the ISA spec says "Undefined Behavior".

## II.11 Emit results as expressions, not columns

Universal

A gadget's *output* often needs no storage at all.
SP1 hands the adapter `Word::extend_var(bit)` = $(bit,0,0,0)$ for SLT (`alu/lt/mod.rs:341`), and builds a full
sign-extended 64-bit load result from **one byte column and one bit column**:
`limb0 = byte + (2^16-2^8)*msb`, `limb1..3 = (2^16-1)*msb` (`memory/instructions/load/load_byte.rs:349-354`).
OpenVM's `less_than` core writes `[cmp_result, 0, 0, 0]` with three literal zeros; its adapter/core split exists
precisely so reads and writes cross the boundary as `AB::Expr` (`arch/integration_api.rs:87,268`).
Measured: hardcoding provably-zero upper limbs inside the bus expression removed **26 columns** across three OpenVM chip
families (`openvm#2733`).

> **Where it stops.** The consumer must accept expressions, and the expression's degree must fit wherever it lands --
> most sharply as an interaction multiplicity, where degree 1 is often required.
> The zero-substitution in `openvm#2733` is sound **only because the memory bus is a multiset hash**: "if the prover claims
> zeros but stores non-zero values, verification fails". Lift it out of that setting and it proves nothing.

## II.12 Store $2v$ when a bit is structurally zero

Universal

OpenVM's JALR target PC has a spec-mandated zero LSB, so the stored limbs are those of `to_pc * 2`:
`/// These are the limbs of to_pc * 2.` (`jalr/core.rs:44,136,150`).
The low limb is then range-checked to **15 bits instead of 16** -- the zero bit is free -- and the genuinely-discarded bit
is captured in a separate `to_pc_least_sig_bit` because `rs1 + imm` may have it set.

> **Where it stops.** The truncated bit must be discarded by *semantics*, not merely usually zero.

## II.13 Fold the polarity of an output into the gadget

Universal

Rather than compute a comparison and then negate it, define the gadget's target as the *polarity-adjusted* expression:

```rust
let cmp_eq = cmp_result * opcode_beq_flag + not(cmp_result) * opcode_bne_flag;
// then use cmp_eq wherever the equality gadget wanted its output
```
(OpenVM `branch_eq/core.rs:81`) -- BEQ and BNE in one AIR, zero extra columns, at the cost of $+1$ degree on the per-limb
constraint. Valida does the same for its four comparison opcodes with a single `output` expression
(`alu_u32/src/com/stark.rs`).

> **Where it stops.** The folded expression must itself be boolean, which follows only because `cmp_result` and the two
> opcode flags are separately boolean *and* mutually exclusive. Drop the `assert_bool` on the flag sum and `cmp_eq` can be 2.

## II.14 The nondeterministic-inverse family, and its two holes

Universal

Two columns, degree 3, no lookup:

```rust
let is_zero = 1 - inverse * a;
builder.when(is_real).assert_eq(is_zero, result);
builder.when(is_real).assert_bool(result);
builder.when(is_real).when(result).assert_zero(a);   // <- the one people drop
```
(SP1 `operations/is_zero.rs:31-82`; the four-case argument is spelled out at `:67-73`).
Variants worth knowing: OpenVM's array version puts one inverse-marker per limb and closes with **one summed constraint**
(`is_equal_array/mod.rs:51`); zkevm's `IsZero` commits only the inverse and leaves the output an expression
(`math_gadget/is_zero.rs`); zkevm's `BatchedIsZero` proves "all $N$ are zero" in **2 cells** for arbitrary $N$, at
degree $N+1$ (`gadgets/src/batched_is_zero.rs`) -- and unlike the sum-then-`IsZero` shortcut it needs **no** range bound,
which is exactly when you reach for it.

> **Where it stops.** Two distinct failures, both documented as real findings.
> (i) *On disabled rows the output is free.* With the activation flag $s=0$ **and** $a=0$, both constraints hold for any
> `out` -- so a gated `IsZero` read by an ungated consumer is prover-chosen (OpenVM audit, `circuit-primitives.md:671-707`).
> Multiply the consumer by the same flag.
> (ii) *Division by checking the product.* `a = b/c` as `b == a*c` makes $0/0$ a free oracle returning any field element
> (SP1 KALOS #8). Either constrain $c \neq 0$ or define the $c=0$ result explicitly.
> Note also that `IsZero` on a field element proves $a \equiv 0 \pmod p$, not integer zero -- which is why word versions run
> it per-limb and AND the results in a **balanced tree** to stay at degree 3 (`operations/is_zero_word.rs:86-99`).

## II.15 Sum-then-test instead of $n$ tests -- and its exact bound

Universal, small-limb

`Σ limbs = 0 ⟺ all limbs = 0` collapses $n$ `IsZero` gadgets into one.
SP1 uses it for `addr == 0` (the RISC-V `x0` invariant) with the bound stated in-source:

> *"Since `prev_addr` are composed of valid u16 limbs, adding them to check if all three limbs are zero is safe, as
> overflows are impossible"* (`memory/global.rs:409-411`).

Valida's word-equality gadget is the same idea with squares: `diff = Σ (a_i - b_i)^2`, then one inverse and one flag --
3 columns and 4 constraints for a 4-limb comparison (`cpu/src/stark.rs`, `eval_equality`).
zkevm gets `eq` for **one extra cell** by summing the diff bytes its `Lt` gadget already witnessed
(`math_gadget/comparison.rs`).

> **Where it stops.** $n \cdot (2^{\text{limb}} - 1) < p$, as a compile-time assertion.
> Beyond it a set of nonzero limbs summing to exactly $p$ passes the zero test -- in SP1's case that would let register
> `x0` hold a nonzero value. Valida's own source flags the missing range check for immediates as a TODO.
> The squares version needs the same bound *plus* the absence of a nontrivial sum-of-4-squares vanishing.

## II.16 Small-field arithmetic: what division buys you, and exactly how deep you may chain

Small field (M31 / BabyBear / KoalaBear)

**Division by a power of two is a constant multiply.** In a Mersenne field $2^{-k} \equiv 2^{31-k}$ exactly, so
`M31_4194304` *is* $2^{-9}$ (stwo-cairo `subroutines/verify_add_252.rs:110-131`; stwo's blake uses
`const INV16: BaseField = from_u32_unchecked(1 << 15)` for $2^{-16}$, `blake/round/constraints.rs:10`).
This is the engine behind II.4: **a carry is an expression, never a column**, and 252-bit addition costs
**1 witness column plus 9 degree-3 carry constraints** against a naive 27 carry columns + 27 booleanity constraints.

**The carry-chain depth bound, derived.** You may fold at most **3 nine-bit limbs** into one carry constraint. With
$|d_i| \le 1022$ the integer identity $2^{18}d_2 + 2^9 d_1 + d_0 = 2^{27}c$ has both sides under $2^{29} < p$, so the
field equation implies the integer one. A 4-limb group puts $2^{27}\cdot 1022 \approx 1.4\times10^{11}$ on the left --
the identity then holds only mod $p$, and it is unsound. Independently, the carry's root-set polynomial must stay within
the degree budget, so at most 3 admissible carry values ($\{-1,0,1\}$ or $\{0,1,2\}$); a 4-way limb sum needing
$c\in\{0,1,2,3\}$ cannot be done inline at all.

**The same bound sets your "small operand" threshold.** stwo-cairo routes add/mul to narrow components when the operands
fit, and $2^{29}$ is not arbitrary: three signed operands need $|dst - op_0 - op_1| \le 3\cdot2^{29} < p$. At $2^{30}$,
$3\cdot2^{30} > p$ and the M31 identity stops implying the integer one. The payoff is large --
`add_opcode_small` **39 columns** versus `add_opcode` **103**, with the entire 252-bit felt arithmetic collapsing to one
degree-1 constraint.

**Two membership tests that ride the same bound.** With every limb range-checked non-negative and $\sum\text{bounds} < p$:
$\sum \text{limbs} = 0 \iff$ all zero (II.15), and $\sum\text{limbs} = n\cdot\text{max} \iff$ all limbs are at the
maximum -- which is how one degree-2 constraint pins 17 consecutive limbs to a borrow pattern
(`subroutines/cond_felt_252_as_rel_imm.rs:87-108`). For a test against a *nonzero* constant, square the differences to
restore non-negativity: $\ne 0$ and $\ne P$ together cost **2 columns and 2 constraints** for a 252-bit value, and only
because $P$ has three nonzero limbs (`jnz_opcode_taken.rs:189-210`).

> **Where it stops.** All of it is one inequality: the sum of the worst-case magnitudes must stay under $p$.
> Write that inequality down next to the gadget; it is the only thing separating a field identity from an integer one.
> The interior case fails too -- $\sum = n\cdot k$ for an *interior* $k$ forces nothing.

## II.17 Two free storage classes people forget

Universal

**Instance-level values cost no rows.** PIL's `airval` / `proofval` (and the equivalent public-value slots elsewhere) hold
one field element per AIR instance, not per row. ZisK uses them for continuation state across segments, for padding counts
(IV.3), for register reload at segment boundaries, and for "this memory region is unused in this execution" switches
(`pil/zisk.pil:41-60`). A quantity that is constant over a whole instance should never be a column.

**Write every mux as `sel*(x - y) + y`, never `sel*x + (1-sel)*y`.** Same degree, one fewer multiplication in the
expression DAG, and the default arm survives for free when `sel = 0`. ZisK uses this form universally
(`main.pil:311`, `mem.pil:327,364,422`, `arith.pil:268-280`), and pairs it with
`SEGMENT_L1 * (airval - 'x) + 'x` as the standard "previous row, except on row 0 where it comes from the continuation
bus" idiom -- degree 2, no extra column, and **one constraint text serving both the intra-segment and cross-segment case**.

**Opt out of automatic booleanity when a table already forces it.** PIL's std library asserts `sel(1-sel) = 0` on every
bus selector unless you declare `sel_is_binary: 1` (`std_lookup.pil:54-56`); ZisK opts out everywhere a selector is
already pinned by a table or by a sum of disjoint booleans, saving one degree-2 constraint per bus term.

---

# Part III -- The window: what two rows can do

## III.1 The next row replaces copy constraints entirely

AIR

An AIR has no permutation argument over its own columns, and does not need one: a value produced at step $i$ and consumed
at step $i+1$ is simply read as `next`.

```rust
builder.when(transition_and_not_final)
    .assert_zeros::<U64_LIMBS, _>(array::from_fn(|limb|
        local.a_prime_prime_prime(y, x, limb) - next.a[y][x][limb]));
```
(`plonky3/keccak-air/src/air.rs:196-204`). Zero columns, zero degree.

The hidden price is **openings**: the verifier opens every main column at both $\zeta$ and $\zeta g$.
A one-row-per-instance AIR should say so and halve that:

```rust
fn main_next_row_columns(&self) -> Vec<usize> { vec![] }
```
(`plonky3/poseidon2-air/src/air.rs:140-142`, `sha256-air/src/air.rs:86-89`: *"Each row is self-contained, so no next-row
columns are needed."*)

> **Where it stops.** It is an **unchecked promise**: *"Omitting a column index when the AIR actually reads its next row
> will cause verification failures or, in the worst case, a soundness gap"* (`plonky3/air/src/air.rs:118-124`).
> Re-audit the override on every constraint change.

## III.2 `is_transition` is free; the boundary selectors are not

AIR (FRI-quotient)

In the symbolic cost model:

```rust
Self::IsFirstRow | Self::IsLastRow => 1,
Self::IsTransition | Self::Constant(_) => 0,
```
(`plonky3/air/src/symbolic/expression.rs:44-49`). The reason: boundary selectors are $Z_H(x)/(x-1)$, degree $N-1$,
while the transition selector is $x - g^{-1}$ and the quotient bound $d(N-1)+1$ has the $+1$ reserved for it exactly.

So `when_transition()` is **degree-free** and there is no excuse to omit it (VIII.1), while `when_first_row()` /
`when_last_row()` cost $+1$ -- and *that asymmetry is precisely why the expensive boundary checks are the ones that get
skipped*, which is where the cross-shard bugs live (VIII.30).

> **Where it stops.** This is a uni-STARK fact. Under multilinear/zerocheck provers the arithmetic differs
> (`transition = 1 - last`, `plonky3/multi-stark/src/selectors.rs:110-113`).
> And `is_transition_window(size)` panics for `size > 2` (`air/src/builder.rs:84-91`) -- you get a 2-row window, full stop.

## III.3 Row-cycle flags: rotation, or a periodic column

AIR

Rotation gives a one-hot round counter in **two boundary constraints and one transition constraint**, with no booleanity
check and no "exactly one is set" check -- the invariant propagates:

```rust
builder.when_first_row().assert_one(local.step_flags[0]);
builder.when_first_row().assert_zeros(local.step_flags[1..]);
builder.when_transition().assert_zeros(array::from_fn(|i|
    local.step_flags[i] - next.step_flags[(i + 1) % NUM_ROUNDS]));
```
(`plonky3/keccak-air/src/round_flags.rs:32-47`).

> **Where it stops.** It only pins the pattern *forward* from row 0, and needs `NUM_ROUNDS | trace length` or the rotation
> wraps into garbage. **A periodic column gives the same schedule with zero columns and zero constraints** (I.5) --
> the flags are only worth committing when something else *reuses them arithmetically*, as in II.9.
> Related free move: gate on "not the final step" with the complement of an existing flag,
> `not_final = 1 - step_flags[LAST]`, which is degree 1 and composes with the degree-0 `is_transition` for a total of $+1$
> (`keccak-air/src/air.rs:51-54`, reused across ~50 constraint groups). The complement assumes booleanity, which here is
> inherited from the rotation invariant rather than asserted.

## III.4 Slide a window across `local ‖ next` to pack $k$ steps per row

AIR

Concatenate the two rows' arrays and index into the combined array; a dependency of depth $\le$ (window width) crosses the
row boundary for free:

```rust
let a = ndarray::concatenate(Axis(0), &[local.work_vars.a, next.work_vars.a]).unwrap();
... maj_field(a.row(i+3), a.row(i+2), a.row(i+1)) ...
```
(OpenVM `sha2-air/src/air.rs:524,589`) -- **4 SHA rounds per row with zero copy columns** for a 3-deep dependency, because
the window is 8 wide.
Kimchi's packing is the extreme version: 5 Poseidon rounds per row, 5 scalar-mul bits per 2 rows, 8 endo-crumbs per row
(IX.7).

> **Where it stops.** Exactly 2 rows. Dependencies deeper than $2 \times$ (rounds per row) need III.5.

## III.5 Shift registers past the window -- and *combine before you pipeline*

AIR

SHA's message schedule needs $w_{t-16}$, far outside any window. Three column banks pipeline it forward 4 rows at a time:

```
/// Here intermediate(i) = w_i + sig_0(w_{i+1}); Intermed_t represents the intermediate t rounds ago
/// This is needed to constrain the message schedule, since we can only constrain on two rows at a time
pub intermed_4, intermed_8, intermed_12
```
(OpenVM `sha2-air/src/columns.rs:122`, shifts at `air.rs:443`).

**The trick inside the trick:** the pipelined value is the *already-combined* $w_i + \sigma_0(w_{i+1})$ in 16-bit limbs,
not the 32 bits -- so the register is **2 cells wide instead of 32**.

> **Where it stops.** "Combine before you pipeline" works only because the downstream use is a sum. A register carrying
> something that will be consumed bitwise has to stay wide.

## III.6 A row-local identity needs no transition gate -- and the wraparound is a gift

AIR

From Plonky3's LogUp binding:

> *"The identity is cyclic in the trace domain, so it does not need a transition gate. Forcing it on every row also pins
> the last-row value used by the accumulator's terminal binding."* (`plonky3/lookup/src/logup.rs:353-358`)

Even though `when_transition` is degree-free, dropping it removes a multiplication from every row's evaluation **and**
extends the constraint across the wrap, giving the terminal binding for nothing.

> **Where it stops.** Only for constraints that read the current row only. Anything touching `next` on the last row wraps
> to row 0 and is false -- which is the other half of VIII.1.

## III.7 Send on row A, receive on row B: a bus instead of adjacency

AIR with a bus

When the two rows are 17 apart, or in different chips, or in no fixed order, use an interaction and a **disambiguating tag**:

```rust
let next_idx = select(is_last_block_of_trace, ONE, global_block_idx + ONE);
self.private_bus.send(builder, composed_hash.chain(once(next_idx)), is_digest_row);
self.private_bus.receive(builder, prev_hash.chain(once(global_block_idx)), is_digest_row);
```
(OpenVM `sha2-air/src/air.rs:358-382`). Zero extra columns for the linkage.

Taken to its conclusion this replaces *all* sequencing: SP1's chips are **local-row-only** and carry program order on a
`State` interaction -- `receive_state(clk, pc)`, `send_state(clk + Δ, next_pc)` (`adapter/state.rs:82-88`).
The consequences are worth stealing wholesale: padding rows emit nothing and need no constraints; rows may be shuffled or
generated in parallel; and each instruction class gets its own optimally-shaped chip instead of one wide CPU row paying
every opcode's columns on every row.
SP1's hash precompiles do the same *within* one operation -- 80 rows of SHA compress with no `next_row` constraint anywhere,
each row receiving `(clk, ptrs, index, a..h)` and sending `(..., index+1, a'..h')` (`sha256/compress/air.rs:99-177`).

> **Where it stops.** The tag must be **globally unique per link**, or sends and receives cross-match between unrelated
> instances (OpenVM forces `global_block_idx` to start at 1 and increment, `air.rs:269-293`).
> The chain also *wraps* -- OpenVM's own SOUNDNESS.md flags "On the last block, this constraint wraps around" as a case to
> reason about separately.
> And the payload is not free: Keccak's state message is 100 field elements per row, which is arguably worse than a
> transition constraint. Compare III.1 before reaching for this.

---

# Part IV -- Degree: the master budget

This part is the one that pays for itself. Everything in it follows from one observation: **the system pays for the
maximum, so the maximum is prepaid.**
`degree.md` is the full treatment -- exact cost formulas per backend, the bracket theorem, the $D-2$ law, two worked
break-evens, and the decision procedure. What follows is the AIR-facing summary.

**The one fact to internalize first.** Every FRI-quotient cost is a function of $2^{\lceil\log_2(D-1)\rceil}$, never of
$D$, so degree is *completely free* inside the brackets $\{3\}$, $\{4,5\}$, $\{6,7,8,9\}$, $\{10..17\}$ -- and only the
bracket tops $D = 2^j + 1$ are rational choices. Miden (9), Plonky2 (9), RISC Zero (5), SP1 (3) and OpenVM (3) all sit on
one; Plonky3's degree-7 Poseidon2 AIR does not, and therefore pays for 9 while using 7.
**Round the declared budget up to the nearest $2^j+1$, then go looking for what to spend the slack on.**

## IV.1 What degree actually costs, per backend

Universal

| backend | the mechanism | the price of degree $d$ |
|---|---|---|
| **FRI-quotient AIR** (Plonky3, OpenVM, SP1 v4) | quotient degree $d(N-1)$, split into chunks | $2^{\lceil \log_2(d-1)\rceil}$ quotient chunks; FRI blowup $\ge d-1$ (`plonky3/uni-stark/src/{symbolic.rs:81-87,security.rs:80-84}`) |
| **ethSTARK-style composition** | degree adjustment $\alpha_j x^{D-D_j-1} + \beta_j$ | composition trace of $D$ columns of length $N$, $D$ = smallest power of two $> \max_j D_j$ (ethSTARK §3.6.1) |
| **stwo / circle** | `max_constraint_log_degree_bound` | $\log_2 N + \lceil\log_2(d-1)\rceil$, taken as a **max over all components** (`core/air/components.rs:10-16`) |
| **height ceiling** | blowup eats two-adicity | max trace height $= 2^{\text{TWO\_ADICITY} - \lceil\log_2(d-1)\rceil}$ (`openvm/crates/vm/src/arch/vm.rs:716-717`) |
| **Plonky2 (PLONKish)** | selector groups | $|G| + \max_{g\in G}\deg(g) \le \text{quotient\_degree\_factor}+1 = 9$ (`gates/selectors.rs:150-160`) |

Two things to take from the table. First, **the cost is quantized**: one stray degree-5 constraint moves $D$ from 4 to 8
and *doubles* the composition trace even if the other 51 constraints are degree 3 (ethSTARK §3.6.1).
Second, degree buys **height**: raising `max_constraint_degree` from 3 to 7 in OpenVM costs a factor of 4 in the maximum
trace height available to every AIR in the segment.

> **Where it stops.** Understating your declared bound is a **soundness** bug, not an error --
> stwo checks nothing (`assert_constraints` only checks vanishing on the trace domain) and FRI fails later
> (`constraint_framework/src/component.rs:101`, `prover/assert.rs:78-93`). Overstating it wastes prover work on a larger
> quotient domain. Plonky3 makes both explicit at `air/src/air.rs:176-184`.

## IV.2 Degree matching: the budget is prepaid, so saturate it

Universal

**Once `max_degree = D` is fixed, every constraint of degree $< D$ is unused headroom.** You can fold a selector,
inline an intermediate column, or switch to a higher-degree identity *at zero marginal cost*.
Conversely one degree-$(D{+}1)$ constraint re-prices the entire system.

Three concrete instances of collecting the free money:

- **SP1 bills any chip with even one interaction at the machine maximum:**
  ```rust
  if !sends.is_empty() || !receives.is_empty() {
      max_constraint_degree = max(max_constraint_degree, MAX_CONSTRAINT_DEGREE);
  }
  ```
  (`hypercube/src/chip.rs:783-790`). So on any chip that touches a bus, degree-2 and degree-3 tricks -- encoders (II.7c),
  fused selectors, root-set constraints (IV.7) -- are **free**. A pure-arithmetic chip with no interactions is the only
  place where staying at degree 1--2 pays.
- **stwo's Poseidon already pays $+2$ for `pow5`, so it could batch its logup 4-wide at no extra cost** -- degree $1+4 = 5$
  still rounds to the same bound -- but ships pairs (`examples/poseidon/mod.rs:186`).
  The general rule that falls out: **batch lookup fractions up to $k = d_{\max} - 1$, where $d_{\max}$ is set by your
  arithmetic constraints** (V.9).
- **Plonky2's `CosetInterpolationGate` re-minimizes its own degree after fixing the wire count**, purely so it lands in a
  larger selector group:
  ```rust
  let n_intermediates = (n_points - 2) / (max_degree - 1);
  // Minimizing the degree this way allows the gate to be in a larger selector group
  let degree = (n_points - 2) / (n_intermediates + 1) + 2;
  ```
  (`gates/coset_interpolation.rs:71-96`).

The dual move exists too: SP1's wide Poseidon2 adds a **tautology** to raise its degree to the machine maximum, so the
prover sees a uniform quotient degree across chips:
```rust
// Dummy constraints to normalize to DEGREE.
let lhs = (0..DEGREE).map(|_| state[0][0].into()).product::<AB::Expr>();
builder.assert_eq(lhs, rhs);
```
(`recursion/machine/src/chips/poseidon2_wide/air.rs:40-47`).

Two more places the slack goes, both worth real columns:
**accumulator and bus chunking** -- a running product absorbs $D-2$ multiplicands per row and a LogUp fraction column
absorbs $D-1$ messages, so at Plonky2's 80 routed wires degree 8 buys back **60 committed columns** over degree 2
(`degree.md` II.3--II.4); and **inlining**, which is powdr's entire optimizer: delete a witness column by substituting its
definition, for as long as the budget holds (`constraint-solver/src/inliner.rs:76-83`).

> **Where it stops.** "Free" is per-*AIR* where the max is per-AIR (Plonky3, stwo declare per component) and
> per-*machine* where it is global (SP1's `MAX_CONSTRAINT_DEGREE = 3`, OpenVM's `SystemConfig::max_constraint_degree`).
> Check which before spending. And saturating the budget removes your headroom to *gate* the constraint later (IV.3) --
> a degree-$D$ body can never be multiplied by a selector again.
> One asymmetry to keep in view: **enabling zero-knowledge costs exactly one degree**
> (`(degree_hint + is_zk).max(2)`, `plonky3/uni-stark/src/symbolic.rs:23`), so an AIR that may later be proven in ZK mode
> should target $2^j$, not $2^j+1$, or it doubles its quotient chunk count on the day someone flips the flag.

## IV.3 `when(x)` is a multiplication, and sometimes you must give it up

Universal

`FilteredAirBuilder` has exactly one job:
```rust
fn assert_zero<I: Into<Self::Expr>>(&mut self, x: I) {
    self.inner.assert_zero(self.condition() * x.into());
}
```
(`plonky3/air/src/filtered.rs:56-58`). Filters are **multiplicative masks, not branches** -- a zero condition does not
skip work, it annihilates. Nesting two `when`s adds both degrees.

When the body is already at the cap, the escape is to assert it **unconditionally and fill dummy values** on the rows where
it is meaningless:

> *"We would like to constrain this only on round rows, but we can't do a conditional check because the degree is already 3.
> So we must fill in `intermed_4` with dummy values on the first round row and the digest row."*
> (OpenVM `sha2-air/src/air.rs:439`; same reasoning at `:573,600`; the whole SHA-2 family went **degree 4 -> 3** by this
> route, `openvm#2550`.)

The opposite move -- **pre-multiply a selector into a committed column** -- buys the degree back for one column:
`is_sllw_imm = is_sllw * imm_c` (SP1 `alu/sll/mod.rs:474`), `sra_msb_v0123 = b_msb * v_0123` (`alu/sr/mod.rs:546`).

**Write the constraint twice instead of selecting inside it.** `when(f).assert_bool(c)` is $f\cdot c(c-1)$, degree
$1 + 2\deg c$. With a flag-selected $c = f_{\text{add}}e_{\text{add}} + f_{\text{sub}}e_{\text{sub}}$ that is
$1+2\cdot 2 = 5$; with two gated copies of a degree-1 $c$ it is 3. Cost: $2\times$ the constraints, **zero extra columns**
(OpenVM `base_alu/core.rs:103-124`). Constraint *count* and constraint *degree* are different currencies, and this sells
the cheap one.

**Pad by repeating a real row and gate only the lookups.** The cleanest way out of the dilemma, from stwo-cairo:
duplicate the first real input into every padding row (`self.inputs.resize(size, *self.inputs.first().unwrap())`,
`prover/src/witness/components/ret_opcode.rs:28-32`) and let the enabler multiply **only the LogUp multiplicities** --
arithmetic constraints stay ungated and cost no degree at all. 1 boolean column + 1 booleanity constraint per component.
ZisK removes even that column where padding rows claim a *true* fact: its secondary machines let padding rows send
`ADD(0,0) = (0,0)` and cancel them with a **single degree-0 bus term per AIR instance**, weighted by an instance-level
value equal to the padding count (`state-machines/binary/pil/binary.pil:158-161`).

> **Where it stops.** The dummy-fill trick requires the column to be **unread on those rows** and the freedom to be one you
> own. It is a soundness-relevant trade, not a free win: `openvm#2550`'s own note is that the AIR must be checked never to
> consume the dummies. Repeat-a-real-row requires the padded row to genuinely satisfy every ungated constraint -- which is
> why copying is mandatory and why a component with **zero** real rows cannot exist (`assert_ne!(n_active_rows, 0)`).
> And if your selector is a product of flags, hoist it into a degree-1 committed column instead of recomputing it (II.7).

## IV.4 Degree reduction with an intermediate column: exact price, exact break-even

Universal

The escape hatch: commit the partial product, continue from there. One column and one constraint per split, cutting
degree by (arity $-1$).

```rust
// Monolith chi is degree 4; a log_blowup = 1 prover accepts at most degree 3.
builder.assert_eq(chi[j], andn * x[sub(j, 4)]);          // degree 3 binding
pack_bits_le((0..n).map(|j| x[sub(j,1)].xor(&chi[j])))   // degree 2 output
```
(`plonky3/monolith-air/src/air.rs:615-625`, rationale at `:19-27`).
stwo's Poseidon does one reset per `pow5` -- 1 column + 1 degree-5 constraint -- and *partial rounds reset only `state[0]`*,
1 column instead of 16, which is the entire point of partial rounds in an AIR
(`examples/poseidon/mod.rs`, `N_COLUMNS_PER_REP = N_STATE*(1 + FULL_ROUNDS) + N_PARTIAL_ROUNDS`).
Cairo's "quadratic AIR" discipline does it exactly twice in the whole CPU AIR (§9.3).

**The break-even is sharp: it pays only if the split constraint is the *global* max.**
Monolith's is (degree 4 -> 3 is the difference between `log_blowup` 2 and 1). Cairo's is.
If something else in the AIR is already at the cap, the extra column is pure loss.

> **Where it stops.** Resetting *more often than necessary* also wastes columns: at stwo's `LOG_EXPAND = 2` you can afford
> degree 5, so exactly one `pow5` per reset is optimal and two would be a 16$\times$ mistake in the other direction.
> Note also that stwo's `add_intermediate` is **not** a degree reset -- it defaults to identity and only names a
> subexpression for CSE (`lib.rs:126-136`, `expr/degree.rs:34-46`).

## IV.5 The degree $\leftrightarrow$ width dial, with two worked break-evens

Universal

**Worked example 1 -- Plonky3 `SBOX_REGISTERS`.** `eval_sbox` computes $x^D$ either inline or via committed
intermediates, and the shipped degree table is `(3,0)->3, (5,0)->5, (7,0)->7, (5,1)|(7,1)|(11,2)->3`
(`poseidon2-air/src/air.rs:151-159,305-340`). For BabyBear, $W=16$, $HF=4$, $P=13$, $D=7$, with row width
$W + 2 \cdot HF \cdot W(1+R) + P(1+R)$:

| $R$ | columns | degree | blowup | cost $\propto w \times \text{blowup}$ |
|---|---|---|---|---|
| 0 | 157 | 7 | 8 | **1256** |
| 1 | 298 | 3 | 2 | **596** |

**1.9$\times$ the columns buys 2.1$\times$ overall.** Which is why the shipped example uses `SBOX_REGISTERS = 1` on
BabyBear and `0` on KoalaBear -- whose S-box is already $x^3$ (`examples/prove_prime_field_31.rs:127,154,212,239`).
That is the cheapest version of the dial: **choose a field whose smallest $\alpha$ with $\gcd(\alpha, p-1)=1$ is 3.**

**Worked example 2 -- Plonky2's interpolation gate.** For 16 points, $D=2$:
`max_degree = 8` gives 2 intermediates, actual degree 6, 47 wires (37 routed), 12 constraints;
`max_degree = 2` gives 14 intermediates, degree 2, 95 wires (37 routed), 60 constraints.
**Same routed count either way; the price of low degree is 48 advice wires and 5$\times$ the constraints.**

> **Where it stops.** `eval_sbox` **panics** outside its table -- the register count must be *optimal* for the degree, not
> merely sufficient. And the whole trade inverts if some *other* constraint in the AIR is already at the max: degree is a
> per-AIR maximum, so lowering one gadget below it buys nothing (IV.2).

## IV.6 Prefer a vanishing-set constraint to a chain

Universal

When a quantity is known to land in a small set, assert the *root polynomial* instead of building the operation.

- **5-way XOR in degree 3.** For booleans, $\sum_{y} a'[y] - c' \in \{0,2,4\}$, so
  `diff * (diff - 2) * (diff - 4) = 0` (`plonky3/keccak-air/src/air.rs:131-139`; SP1 `keccak256/air.rs:96-107`).
  Degree 3 instead of 5, zero aux columns. Generalizes to $\prod_{k \text{ even}}(\text{diff}-k)=0$, degree $\lceil m/2\rceil+1$.
- **Carry-free modular addition.** `acc*(acc+2^32)*(acc+2*2^32) = 0` plus the same mod $2^{16}$, i.e. a CRT pair --
  **zero carry columns**, 2 constraints per 32-bit add (`plonky3/air/src/utils.rs:82-133`).
- **A 3-element set that moves with a branch.** `assert_tern(mem_as - is_store*2)` encodes "`mem_as` in $\{0,1,2\}$ if load,
  $\{2,3,4\}$ if store" in **one** degree-3 constraint (OpenVM `adapters/loadstore.rs:208`).
- **Small-set membership.** $w(1-w)(2-w)\cdots(r-1-w)$, degree $r$, zero rows, zero lookups (halo2 `utilities.rs:170-174`).
  And the roots need not be constants: $(a-x)(a-y)(a-z)=0$ pins $a$ to one of three arbitrary polynomials.
- **Sorted range check with jumps.** Miden allows the sorted column's step to be any of $\{0,1,3,9,\dots,2187\}$, a single
  degree-9 constraint, so the table only needs the values actually used (`air/src/constraints/range/mod.rs`).

> **Where it stops.** All of these need the inputs *already* pinned to the domain where the algebra is valid --
> booleanity for the XOR form, pre-range-checked limbs and $P > 3\cdot2^{16}$ for `add3` (Plonky3 panics otherwise, `:79-80`),
> $\{0,1,a\}\times\{0,1,b\}$ for OpenVM's degree-3 rewrite of its degree-4 odometer predicate (`range_tuple/mod.rs:222-225`).
> And the degree grows with the set: `range_check` dies past ~3-bit pieces under a degree-9 budget
> (halo2 `decompose_running_sum.rs:18-23`, `assert!(WINDOW_NUM_BITS <= 3)`), and Miden's degree-9 range constraint
> **cannot be multiplied by any selector at all**.

## IV.7 Pick the cheapest algebraic identity for the same function

Universal

Same truth table, different degree:

| function | naive | cheap | why |
|---|---|---|---|
| $\mathrm{Ch}(e,f,g)$ | `xor(and, andn)`, 3--4 | $ef + (1-e)g$, **2** | disjoint AND-terms collapse the XOR to an addition (`plonky3/sha256-air/src/air.rs:293-295,705-712`) |
| $\mathrm{Maj}(a,b,c)$ | -- | $ab + c(a+b-2ab)$, 3 | (`:721-731`) |
| $a \lor b$ | dedicated table op | $(a \oplus b) \oplus (a \wedge b)$ | Miden deleted `u32or`: chiplet degree **6 -> 5**, transition constraints **19 -> 17**, internal selector 2 columns -> 1 (`miden#366`) |
| $a \lor b$, $a \oplus b$ from $a \wedge b$ | separate gadgets | $a+b-\text{and}$ and $a+b-2\,\text{and}$ | **zero** extra columns and zero degree over the AND (Valida `alu_u32/src/bitwise/stark.rs`) |
| $2^k$ from bits of $k$ | one-hot table | $\prod_i (1 + (2^{2^i}-1)b_i)$ | $\log_2 XLEN$ factors (Jolt `pow2.rs`); SP1 stores it in 3 degree-2 steps for a 16-way selector in **9 columns** (`alu/sll/mod.rs:357-359`) |
| conditional swap | 2 muxes | $out_1 = in_1 + b(in_2-in_1)$, $out_1+out_2 = in_1+in_2$ | the second output is **degree 1** by conservation (SP1 `chips/select.rs:198-207`) |

> **Where it stops.** The `Ch` collapse needs the OR-terms *provably disjoint*. Miden's OR synthesis costs three chiplet
> operations instead of one (`keccak256` execution +2.3%) -- a constraint-degree win paid for in rows.
> Valida's identities are integer identities holding in $\mathbb F_p$ only while $x + y < p$.

## IV.8 Algebraically-equivalent lower-degree substitutes -- powerful and dangerous

Universal, one-hot dispatch

Miden's aggregate shift flags are **not** the sum of the sixteen degree-7 one-hot flags. They are a different polynomial
that agrees with the true flag *only on well-formed traces*:

```rust
// These are NOT the same expressions as right_shift[15] / left_shift[15].
// They use low-degree bit prefixes that are algebraically equivalent on
// valid traces (exactly one opcode active), but produce lower-degree expressions.
let right_shift_scalar = prefix_011 + op5(PUSH) + op6(U32SPLIT);   // degree 6
let left_shift_scalar  = prefix_010 + u32_add3_madd_group + ...;   // degree 5
```
(`miden/air/src/constraints/op_flags/mod.rs`). Drops 1--2 degrees on every constraint they gate, and they gate the whole
stack-shift machinery.

> **Where it stops.** This is the sharpest trick in the manual and the easiest to get wrong. The substitute agrees with the
> true flag **only where the op-bit constraints already hold**, so:
> it must never appear in a constraint whose job is to *establish* well-formedness of the op bits;
> and it must not be used where the AIR must reject a malformed row -- you would be conditioning on a polynomial that is
> meaningless there.
> Miden's own source also documents a non-obvious exclusion ("DYNCALL is intentionally excluded -- it left-shifts the stack
> but uses decoder hasher state for overflow constraints"), which is the shape of mistake this invites.

## IV.9 Interaction fields and multiplicities are degree-budgeted too

AIR with a bus

Every OpenVM sub-AIR documents its degree as $\deg(\text{count}) + \max(1, \deg(x), \deg(y))$
(`assert_less_than/mod.rs:72`, `offline_checker/bridge.rs:294`), and the backend prices it:

> *"per AIR: it gets the max degree across all `fields` and max degree across all `count` across all interactions.
> It uses this to set the per-AIR interaction chunking."* (`openvm#407`)

**Consequence: a degree-2 field expression in one bus send shrinks the chunk size for the entire AIR**, so fewer
interactions share each permutation column. Keeping field expressions at degree 1 is worth real columns.
Miden puts a number on the other end: with a degree-9 budget, a lookup bus row can carry **at most 7 fractions**, and
*"If any of these flags have degree greater than 2 then this will increase the overall degree of the constraint and reduce
the number of lookup requests that can be accommodated by the bus per row."*

> **Where it stops.** The corollary cuts both ways: making a lookup conditional by multiplying the multiplicity by a flag
> (V.1) is free only while $\deg(\text{count})$ stays inside the budget you had left.

## IV.10 Where the trade inverts

Universal

The FRI-quotient pricing of Part IV is not universal.

- **Sumcheck / multilinear / GKR backends** (HyperPlonk, SP1 Hypercube, Jolt): there is no quotient polynomial to blow up.
  Jolt has no AIR degree at all and instead prices *per cycle* -- *"An instruction emulated by an eight-instruction virtual
  sequence is approximately eight times more expensive to prove"* -- so its answer to a hard instruction is a **longer
  instruction sequence**, never a cleverer high-degree constraint.
- **Folding schemes** (Nova/Sangria/ProtoGalaxy): high degree is *worse* than linear in the folding step, so the
  degree-vs-width dial tilts hard toward width.
- **Small-field/tower systems** (Binius): the currency is bits committed, not degree; linear operations over the tower are
  free and only AND-like (degree $\ge 2$) operations cost commitments (`m3/src/builder/table.rs`).

> **Where it stops.** Do not import a degree budget across these boundaries. The single question that resolves it:
> *what does the prover commit to that grows with $d$?*

---

# Part V -- Lookups and buses, from the designer's side

Nothing here is about how a lookup argument is proved. It is about what a row can buy with one.

## V.1 The multiplicity is an expression, so a conditional lookup is free

AIR with a bus

There is no separate "enable". The count is just another expression:
a flag; a **sum** of flags (`opcode_mulh_flag + opcode_mulhsu_flag`, OpenVM `mulh/core.rs:157`);
a **difference** (`is_valid - special_case`, `divrem/core.rs:315`; `is_real - imm_c` to skip a register read on immediate
rows, SP1 `adapter/register/alu_type.rs:137`); a **running prefix sum** (`less_than/core.rs:133`);
a **product** (`is_begin * next.is_terminate`, `connector/mod.rs:206`).

stwo goes one step further and lets the numerator be *signed*, so one column serves both a send and a receive
(`plonk/mod.rs:69-84`), or uses $\pm 1$ constants with **no multiplicity column at all** (`state_machine/components.rs:47-57`).
OpenVM's memory boundary chip uses a signed count in $\{-1,0,1\}$, pinned by the cubic $d = d^3$, so **one row is both the
initial-state send and the final-state receive** (`persistent.rs:41-44,86-89`) -- and then gets two more selectors free from
the same column: $d^2$ = "row is live", $d(d+1)$ = "$d=1$".

> **Where it stops.** Three conditions, each of which has been a real finding.
> (i) The count must be **provably zero on padding rows** or the padding row emits a real request (VIII.6).
> (ii) It must be **provably boolean** where the argument assumes it -- "Caller must constrain that `enabled` is boolean"
> (OpenVM `program/bus.rs:27`) -- a non-boolean count silently multiplies the request; `is_real - imm_c` needs
> `when_not(is_real).assert_zero(imm_c)` or a padding row emits a **negative** multiplicity.
> (iii) $\deg(\text{count})$ counts against the budget (IV.9).
> Note also the alternative OpenVM considered and rejected, because the reasoning is instructive: *"range checks could
> always be done, if the aux subrow values are set to 0 when `count == 0` ... It however leads to the annoyance that you
> must update the RangeChecker's multiplicities even on dummy padding rows"* (`assert_less_than/mod.rs:31-37`).

## V.2 One table, many operations: the opcode is a *field*, not a chip

AIR with a bus

SP1's `ByteChip` is one preprocessed table of $2^{16}$ rows holding **all** results side by side, with one multiplicity
column per opcode:

```rust
pub struct BytePreprocessedCols<T> { b, c, and, or, xor, ltu, msb }   // 7
pub struct ByteMultCols<T> { multiplicities: [T; NUM_BYTE_OPS] }     // 6
```
(`bytes/columns.rs:15-45`). Total width 13, matching `"Byte": 13` in the cost table.
**Adding a 7th operation costs one preprocessed column and one multiplicity column on $2^{16}$ rows** -- versus a whole new
table at $2^{16} \times (\text{its own width} + 1)$.
OpenVM does the identical thing with *no* preprocessed trace, generating the table from transition constraints and storing
operands **as bits** so the XOR result is an algebraic expression ($x_i + y_i - 2x_iy_i$) costing zero table columns
(`bitwise_op_lookup/mod.rs:97,194-238`).

> **Where it stops.** The ops must share an index domain, and the result must be a *function* of the key -- you cannot have
> the same $(x,y,\text{op})$ admit two valid $z$.
> The opcode at the *call site* must be a constant or a provably-correct selector combination (II.7), or a prover swaps AND
> for OR.
> And a gate-generated table must **pin its own height**: *"Constrain the last counter value to ensure trace height equals
> range_max. This is critical as the trace height is not part of the verification key"* (`range_gate/mod.rs:198-202`) --
> plus a *monotone* quantity connecting first row to last, or the anchor alone is insufficient (`var_range/README.md`).

## V.3 Two checks per lookup, and tuple lookups

AIR with a bus

The byte table's two key slots both carry information, so a range check gets two values per interaction:

```rust
while index + 1 < input.len() {
    self.send_byte(U8Range, zero, input[index], input[index+1], mult); index += 2;
}
```
(SP1 `air/word.rs:55-80`) -- $\lceil n/2 \rceil$ interactions for $n$ bytes.
Measured: switching OpenVM's load/store core from per-byte to paired lookups took the reth benchmark
**144 -> 120 segments (-16.7%)** (`openvm#2841`).

The generalization is a **tuple range checker**: one interaction for $(x,y)$ when the product of ranges is small.
*"When you know you want to range check `(x, y)` ... and $2^{x+y} < \sim 2^{20}$, then you can use this chip to do the range
check in one interaction versus the two interactions necessary"* (`openvm/range_tuple/README.md`).
That is how schoolbook multiplication pays for (limb, carry) in one message.

Two corollaries worth internalizing:
- **Pack odd-length lists across sources.** *"range checking the limbs of immediate and PC separately would result in
  additional range checks since they both have odd number of limbs"* (`auipc/core.rs:135`).
- **Skip a value already checked in another role**: *"pc_limbs[0] is already range checked through rd_data[0], so we skip it"* (`:140`).

> **Where it stops.** Pairing needs a *symmetric* predicate -- comparisons are asymmetric and get one lookup each, and u16
> checks cannot pair because they need the whole key space.
> The tuple checker needs $\prod\text{sizes}$ to be a power of two under $\sim2^{20}$, every size $>1$, and $N>1$
> (`range_tuple/{bus.rs:14-19,mod.rs:244-256}`), and callers must size the carry dimension for the worst case.

## V.4 A variable-width range table serves every bit width at once

AIR with a bus

Make the width part of the key: the table enumerates every $(v, b)$ with $v < 2^b$, $b \in [0, b_{\max}]$.

```rust
let key = [self.value, self.max_bits];
self.bus.lookup_key(builder, key, count);
```
(OpenVM `var_range/bus.rs:81`; SP1's `RangeChip` is the same at $2^{17}$ rows, `range/columns.rs:45-55`).
Height is $2^{b_{\max}+1}$ -- exactly $2\times$ a single fixed table -- and that $2\times$ buys **all** widths.

Three things it unlocks that a fixed table cannot:
- **$b$ may be a witness expression.** SP1's shifts range-check each limb to `bit_shift` and `16 - bit_shift`, which is what
  makes a variable shift cheap (`alu/sll/mod.rs:363-386`).
- **$b = 0$ is a free "assert $x = 0$"**, since the table's first row is $(0,0)$ -- OpenVM's SHIFT uses it for the
  zero-shift case with no branch (`shift/core.rs:383`).
- **A shorter final limb costs nothing.** Decompose an $N$-bit value into $\lceil N/k\rceil$ limbs and check the last to
  $N \bmod k$ bits **on the same table**:
  ```rust
  let range_bits = bits_remaining.min(self.range_max_bits());
  self.bus.range_check(*limb, range_bits).eval(builder, count);
  ```
  (`assert_less_than/mod.rs:149-159`).

> **Where it stops.** $b \le b_{\max}$, and if $b$ is witness-controlled the prover can always choose a *larger* $b$ than you
> intended -- it must be pinned by another constraint. Constant callers are safe.

## V.5 A lookup that computes *and* range-checks in the same message

Universal

The best lookups do two jobs.

- **Spread / interleaved bits** (halo2 SHA-256). $\mathtt{spread}(x)$ inserts a zero between every pair of bits.
  A lookup into the $2^{16}\times 3$ table proves the chunk is 16 bits **and** returns its spread form
  (*"We do not require a separate table for range checks because spread can be used"*), and then adding spread words puts
  the **XOR in the even bits and the carry/majority in the odd bits** with no cross-bit carries.
  Measured from the book's own cost table: $Maj$ 4 lookups/4 rows, $Ch$ 8/8, $\Sigma_i$ 6/6, **24 rows per compression
  round, 2099 rows per SHA-256 block**.
- **Diluted form** (Cairo). The same idea with `spacing` zero bits, which makes $x+y = (x\oplus y) + 2(x\wedge y)$ hold with
  **no carry propagation** -- so AND, XOR *and* OR come out of one witness set with **degree-1** constraints and zero bit
  columns (`diluted_check_cell.h`, `bitwise/*` constraints).
- **XOR as a sign-bit extractor.** $x \oplus m = x + m - 2(x \wedge m)$ for a single-bit mask, so one XOR lookup pins the
  msb *and* range-checks the byte -- replacing 8 boolean columns and a recomposition (OpenVM `shift/core.rs:196-202`).
- **XOR as a "no overlapping bits" check.** $x \oplus m = x + m$ iff $x \wedge m = 0$, which is how JAL proves its top limb
  has no bits above `PC_BITS` on a bus it already uses (`jal_lui/core.rs:91`).
- **Bitwise ops where the lookup *is* the computation.** SP1's `BitwiseOperation` owns only the result bytes and has not a
  single arithmetic constraint -- degree 1 everywhere (`operations/bitwise.rs:69-77`).

> **Where it stops.** Spread needs a shared $2^{16}$ table, so it is only for large circuits (*"It requires a minimum of
> $2^{16}$ circuit rows"*), and the carry out of a multi-operand addition must be **separately** constrained to the exact
> range for that operand count -- which is why halo2's design distinguishes $reduce_6$ from $reduce_7$ and reduces
> $W_{62..63}$ eagerly ("would require handling a carry of up to 10 rather than 6, so it's not worth the complexity").
> Diluted form needs $(n_{\text{bits}}-1)\cdot\text{spacing} < 64$ and a diluted-check permutation, without which
> $x+y = \text{xor} + 2\,\text{and}$ is satisfiable by garbage.
> The single-bit-mask XOR trick does not extend to multi-bit masks unless $x \wedge m$ is already a witness.

## V.6 Decompose, scale, and divide -- three ways to reshape a range check

AIR with a bus

- **Scale up to check a narrower bound on a wider table.** If $x$ is already known $< 2^k$, then $x\cdot2^{k-b} < 2^k$
  iff $x < 2^b$ -- a free constant multiplication inside the interaction field
  (OpenVM `rv32-adapters/src/vec_heap.rs:182-192`). **This absolutely requires the prior $x<2^k$ fact**, which OpenVM
  justifies explicitly: "since limbs are read from memory we already know that limb[i] < 2^RV32_CELL_BITS".
- **Shift and double-lookup when you have no prior bound.** $x < \text{max}$ and $x + (\text{max}-2^b) < \text{max}$
  together give $x < 2^b$: 2 interactions of 1 field, and **the only variant that presupposes nothing**
  (`range/bus.rs:100-114`; needs $2\cdot\text{max} < p$).
  Kimchi's version does it *inside* the lookup argument with a scaled joint lookup -- $v_{11}$ and $2^9 v_{11}$ both looked
  up in a 12-bit table gives a 3-bit check with **zero extra witness cells and zero constraints**.
- **Divide in-field to prove divisibility and range in one lookup.** $(x - s)/4 < 2^{14}$ proves both that $x \equiv s
  \pmod 4$ and that $x$ is bounded, because a non-multiple's quotient is a huge field element:
  ```rust
  // (limb[0] - shift_amount) / 4 < 2^14  =>  limb[0] - shift_amount < 2^16
  self.range_bus.range_check((mem_ptr_limbs[0] - shift_amount) * F::from_u32(4).inverse(), 14)
  ```
  (OpenVM `adapters/loadstore.rs:188-194`). SP1 uses the same idiom to certify `clk == 1 (mod 8)` **and** 16-bit-ness in one
  message (`adapter/state.rs:88-94`), and to extract three address-offset bits while returning the aligned address as an
  expression (`operations/address.rs:89-110`).

> **Where it stops.** For the scale-up: without the prior bound, field wraparound passes.
> For the division: $2^{\text{bits}} \times \text{divisor} < p$, the divisor must be invertible, and the shifted range must
> *exactly* cover the original -- otherwise you have proven a weaker statement than you think.

## V.7 Delete a range check that a tighter known range already implies

Universal

powdr mechanises this and the procedure is the interesting part: strip every *pure* range-check interaction out of the
system, re-run the solver on the **remainder**, and keep a check only if it still adds information:

```rust
if current_rc != current_rc.conjunction(rc) { keep }
```
(`range_constraint_optimizer.rs:52-138`).

The pass has three side conditions that are exactly the ones a human gets wrong:
multiplicity must be **exactly 1** (conditional checks are skipped); a stateful bus never qualifies; and
**you may not use a check to justify deleting itself** -- hence the strip-then-re-derive order.
Re-emission must never *widen* a range: `batch_make_range_constraints` returns an error rather than approximate.

Related powdr passes worth applying by hand:
- **Recognize the self-XOR idiom.** `XOR(x, x, 0)` carries no XOR information; it degenerates to "x is a byte", which then
  becomes deletable or batchable (`bitwise_lookup.rs:89-101`).
- **Replace a small lookup with a polynomial.** For a stateless interaction with $\le 256$ input points, enumerate the
  function graph and match it against a library (identity, $1-x$, $x+y$, $xy$, $x+y-xy$, $x+y-2xy$); on a unique match emit
  `output = f(inputs)` plus range checks that V.7 then usually deletes
  (`low_degree_bus_interaction_optimizer.rs:98-143,334-373`).
- **Trade a 1-bit range check for $x(x-1)=0$**, but only `if rc == from_mask(1) && assert_bool(expr).degree() <= bound`
  (`range_constraint_optimizer.rs:107-122`) -- `assert_bool(expr)` is degree $2\deg(\text{expr})$, so this dies immediately
  on composite expressions.

> **Where it stops.** The low-degree replacement has a knife-edge: the replacement range constraints must not be **wider**
> than the ones used to enumerate the domain; if they cannot be implemented exactly, powdr keeps the original interaction
> *and* adds the polynomial rather than risk it.

## V.8 Prove non-zero with a range check instead of an inverse column

AIR with a bus

$v - 1 \in [0, 2^8)$ implies $v \ge 1$. The unused second slot takes the constant 0:

```rust
// Range check to ensure diff_val is non-zero.
self.bus.send_range(cols.diff_val - AB::Expr::ONE, AB::F::ZERO).eval(builder, prefix_sum);
```
(OpenVM `less_than/core.rs:131`; also `divrem/core.rs:313`, `branch_lt/core.rs:152`).
Price: 1 interaction, and it **saves the inverse witness column plus its degree-2 constraint**.

> **Where it stops.** It proves *positivity within the table's window*, not non-zeroness in general -- $v = 2^8+1$ also
> passes. Safe here only because `diff_val` is a difference of limb-bounded values and the same check bounds it.

## V.9 Fraction batching and message-width economics

AIR with a bus

Two independent knobs.

**Fractions per column.** $\frac ab + \frac cd = \frac{ad+cb}{bd}$, so $k$ pending fractions can share one accumulator
column at the cost of a degree-$k$ denominator:

```rust
// finalize_logup_batched(k): chunk pending fractions, one cumulative-sum column per chunk
```
(stwo `constraint_framework/src/lib.rs:185-232`; `finalize_logup_in_pairs` is $k=2$).
Each stwo interaction column is `SECURE_EXTENSION_DEGREE = 4` committed M31 columns, so pairing halves
$4n \to 4\lceil n/2\rceil$. Degree is $1+k$.
**Columns shrink as $1/k$ while degree grows linearly in $k$** -- so batch up to the budget you already pay (IV.2), and no
further. LogUp's own framing is the same parameter $\ell$: $\ell=1$ gives $M+1$ commitments at degree 3;
$\ell = M+1$ gives one extra commitment at degree $M+3$; the optimum "depends on the used polynomial commitment scheme".

**Message width.** The combine is linear, so the *denominator* is degree 1 regardless of tuple width -- but every field is a
committed column on both sides. Two mitigations from the field:
split one wide message into two tagged messages at the same timestamp (OpenVM's Keccak state: *"We use two interactions
bound with the same timestamp to avoid having a really large message length"*, `keccakf_op/air.rs:168-182`),
and pack small values into one field element (`b0 + 256*b1`, or SP1's global message repacked from 4$\times$u16 into
3 elements of 24/24/16 bits at the cost of 2 columns and 2 lookups, `memory/local.rs:299-304`).

> **Where it stops.** stwo's batching chunks **consecutive** pending fractions, so emission order dictates pairing.
> A multiplicity-0 entry is *not* free -- it still occupies a batch slot and still multiplies its denominator in, and its
> denominator must still be non-zero, so padding tuples must be well-formed values rather than garbage.
> Packing is injective only if the packed pieces are independently range-checked -- otherwise it is a value forgery.

## V.10 Bus separation: tags, widths, and the three aliasing traps

AIR with a bus

A bus is a namespace, and namespaces collide.

- **Distinct relations need distinct challenge sets.** blake defines five separate `XorElements{12,9,8,7,4}` precisely
  because one shared relation would let a 4-bit XOR tuple be satisfied by a 12-bit table entry (`blake/mod.rs:54-58`).
  Sharing one relation across semantically different tables is a soundness hole; the residual risk is marked in-repo as
  "TODO: Separate lookups by w".
- **One payload width per bus.** The fingerprint folds a tuple aligned to *its own* length, so a shorter tuple is implicitly
  left-zero-padded and `[x]` **collides with** `[0, x]` (`plonky3/lookup/src/types.rs:93-124`).
- **A discriminator belongs inside the message.** SP1 funnelled Memory and Syscall interactions through one Global bus with
  no kind field; a memory send could satisfy a syscall receive ([High]). The fix is the one worth copying: fold `kind`
  into the *unused high bits of an already-range-checked limb*, `values[0] + 2^16 * kind` -- **zero extra field elements**.
- **Do not encode the bus index in an exponent.** OpenVM's $1/(X^b + h(\sigma))$ separation was [High]: $X^b + c$ factors,
  so by partial fractions terms from different buses cancel. The bus index must make the denominator *linear*.

The general rule that generates all four: **if a value steers a message, it belongs in the message.**
SP1's CPU selected which shard/clk to send using `is_memory` but never sent `is_memory` -- so it was free, and a prover
flipped it ([High]).

> **Where it stops.** Multiplicities are field elements and **wrap**. Plonky3 enforces $\sum_i w_i h_i < p$ exactly and states
> the division of labour: the framework *trusts* the AIR to bound each row's count and never verifies it
> (`lookup/src/count.rs:8-24`, `types.rs:334-380`). At $p \approx 2^{31}$, $2^{21}$ rows $\times$ weight $2^{10}$ already
> brushes the bound.

## V.11 Chip specialization: the cost-per-row $\times$ count arithmetic

AIR with a bus

Moving a computation to a dedicated chip is worth it when the receiving chip's rows are fewer or narrower, and the
arithmetic is explicit.

- **Deduplicate by content.** OpenVM's Poseidon2 periphery chip has height = number of *distinct* $(\text{input},
  \text{output})$ pairs, because identical tuples collapse into one row with `mult > 1` (`system/poseidon2/air.rs:69-76`).
  Only the top half of the output is published, so the message is `WIDTH + WIDTH/2 = 24` fields rather than 32.
  SP1 charges `InstructionFetch` (36) per dynamic instruction but `InstructionDecode` (61) only per **distinct** instruction
  word in the shard -- a 1M-instruction loop over a 500-instruction body pays 36M + 30,500 instead of 97M, a **62% saving**
  (`executor/src/vm/shapes.rs:86-95`).
- **Split the once-per-invocation work into a control chip.** SP1's precompiles have `rows_per_event` of 80 (SHA compress),
  48 (SHA extend), 24 (Keccak); the control AIR is added **once**, not per row:
  one SHA-256 compression costs $80 \times 206 + \mathbf{53}$, where inlining that 53-wide logic would cost $80\times53 = 4240$ -- **80$\times$ more**
  (`executor/src/air.rs:473-499`, `utils.rs:130-136`).
  The break-even: $\text{control\_width}\times(\text{rows\_per\_event}-1) > \text{rows\_per\_event}\times\text{interaction\_cost}$.

> **Where it stops.** Deduplication is sound only because the relation is a **function** -- identical inputs must have
> identical outputs. It would be unsound for a relation with witness freedom.
> Publishing half an output is fine for compression and wrong if a caller needs the full state.
> And the control chip pays $\ge 1$ extra interaction per row of the wide chip.

## V.12 When a lookup is *not* the answer

Universal

Three honest counterexamples.

- **Fixed cost per shard.** SP1's `BYTE_NUM_ROWS = 2^16` and `RANGE_NUM_ROWS = 2^17` are paid **in every shard**, even one
  that does a single byte lookup: $2^{16}\cdot13 + 2^{17}\cdot3 = \mathbf{1{,}245{,}184}$ cells of floor
  (`executor/src/vm/shapes.rs:61-64`).
- **Table amortization.** Kimchi's own note on `Xor16`: *"We could halve the number of rows of the 64-bit XOR gadget by
  having lookups for 8 bits at a time ... Rough computations show that if we run 8 or more Keccaks in one circuit we should
  use the 8-bit XOR table."* The table costs $2^{2k}$ rows and only amortizes over enough instances.
- **Do the arithmetic natively and lookup only the overflow.** Jolt does *not* look up addition: it adds in the scalar field
  and applies a range-check lookup purely to truncate the 65th bit -- one constraint plus one lookup against a $2^{128}$-entry
  two-operand table. That trick requires the field to be strictly wider than the operation's natural output, so on
  BabyBear/Goldilocks it is unavailable and you are back to limbs.

## V.13 Message-shape tricks: tags, truncation, partitions, replicas, indirection

AIR with a bus

Five moves from stwo-cairo, whose components are *machine-generated from a cost model* -- so every shape in them is an
optimizer's output rather than a preference.

**One challenge set for every relation, separated by a hard-coded tag.**
There is exactly one `relation!` type in the whole Cairo AIR, with 128 alpha powers; each logical relation prepends a
constant ID as tuple entry 0 (`crates/cairo-air/src/relations.rs:5-25`). Since $\mathrm{combine}(v) = \sum_i \alpha^i v_i - z$,
the tag contributes a *constant*, i.e. it just shifts $z$. Zero witness columns, zero constraints, replacing ~40
independently-drawn challenge tuples -- and the saving lands in the **recursive verifier**, which would otherwise
materialize all those alpha powers.
*Stops:* the IDs are hashes committed as source constants and **nothing checks distinctness** -- a collision silently
merges two relations. Contrast V.10, where separate challenge sets were the point: the tag is what makes sharing safe.

**Truncate the tuple to prove a range bound for free.**
`combine` folds only `values.len()` alpha powers, so a short tuple is *identical* to the zero-padded long one.
The `id -> felt252` table always yields 28 limbs; a consumer that knows its value is $< 2^{36}$ supplies **only 4** --
and matching a row then *forces* limbs 4..27 to be zero (`subroutines/read_positive_known_id_num_bits_36.rs:26-40`).
`ceil(bits/9)` columns and **zero constraints**.
*Stops:* only when the excess is exactly zero, i.e. `bits ≡ 0 mod 9`; otherwise you pay a conditional range check on the
ragged top limb. And it is the same padding convention that makes `[x]` alias `[0,x]` in V.10 -- here it is load-bearing
rather than a bug, which is precisely why one bus must have one semantic.

**Name range tables by their bit partition so one lookup absorbs the exact leftovers.**
A `range_check_a_b_c` component is a $2^{a+b+c}$-row preprocessed table whose $k$-th column is bit-slice $k$ of the row
index. The shipped shapes are `[4,3] [4,4] [9,9] [7,2,5] [3,6,6,3] [4,4,4,4] [3,3,3,3,3]` -- each one exists because some
specific limb regrouping leaves exactly those widths. Cairo's three 16-bit instruction offsets over 9-bit memory limbs
leave $7,2,5$ and $4,3$: **two lookups instead of five**, and the 9-bit-wide pieces need no check at all because they
*are* memory limbs, already checked (`subroutines/encode_offsets.rs:40-71`).
*Stops:* $\sum\text{bits} < 31$, table size exponential in the sum -- you can bundle many narrow checks
(`3_3_3_3_3` = 32K rows) but only two wide ones (`9_9` = 256K). Every new shape is a fixed table committed for *every*
proof.

**Replicate a hot relation to stay under the multiplicity-wrap bound.**
Multiplicities are field elements; if a relation is used $\ge p$ times the column wraps and the argument accepts a row
that was never yielded. `RangeCheck_9_9` is therefore **eight relations A..H over the same preprocessed table**, with
eight multiplicity columns, and consumers round-robin across them (`components/range_check_9_9.rs:5-7,58-145`).
The bound is checked statically by the verifier from a per-component-per-row use table (`verifier.rs:83-97`).
Price: $N-1$ extra multiplicity columns on the table; **zero** on the consumer side, which just picks a different tag.
*Stops:* this is a soundness patch, not an optimization -- and it is a *verifier-side precondition*, not an in-circuit
constraint.

**Two-level indirection: address -> small id -> value.**
The memory bus never carries a 252-bit felt; it carries a 1-element id, and the id space is partitioned by value width so
a value $\le 2^{72}$ costs **9 trace cells instead of 29**. Ids are deduplicated by value, so the value tables have one
row per *distinct* value rather than per cell (`crates/adapter/src/memory.rs:160-187`). Two further gifts fall out:
value equality becomes **id equality** -- one shared column and two lookups, zero constraints, versus 28 limb equalities
(`subroutines/mem_verify_equal.rs:26-37`) -- and both tables yield into the *same* relation with the small table's tuple
being the big one's truncation, so consumers never learn which table an id came from.
*Stops:* the small-id space is capped and overflow silently spills into the big table, so the compression is best-effort;
the verifier must check the id range does not wrap the field; and the limbs are only proven 9-bit, so the representation
is **not canonical** -- which is exactly why the zero-test needs the "$\ne 0$ **and** $\ne P$" double check of II.15.

---

# Part VI -- Machine-level economics

Everything above is per-chip. This part is the layer where chips are created and destroyed.

## VI.1 Split a hot chip by subcase; merge cold chips

Universal

**Split.** SP1's `AluX0Chip` handles every ALU instruction whose destination is `x0`:
*"Since `x0` is hardwired to zero in RISC-V, the arithmetic result is discarded. This chip only verifies the instruction
against the program table and performs the register accesses"* (`alu/alu_x0.rs:37-41`).
A `DIV` with `rd = x0` costs **34 cells instead of 246 -- 86% off.**
Measured elsewhere: splitting OpenVM's `AddSub` into `AddSub` + `AddI` (the distribution was 75% immediate) took the AddI
chip to **width 25 (-26%), 16 interactions (-20%)** from 34/20, and removed **1B of 6.8B cells** on the reth benchmark
(`openvm#2953`). Row-type specialization inside one trace did even better: OpenVM's `FriReducedOpeningChip` went
**64 -> 26 columns (-59%)**, with leaf cells -6.9%/-13.3%/-16.0% across three benchmarks (`openvm#1248`).

**Merge.** OpenVM's persistent-memory boundary chip serves both the initial and final state in one AIR with the signed
selector of V.1 -- for $a=600, b=100$ that is 1024 rows instead of 1152, and one fewer AIR in every vk and every shape.

> **Where it stops.** Splitting is not free: each new chip adds $32\times\text{width}$ of worst-case padding, an entry in the
> shape/vk cross-product (VI.3), and forces both variants into the same cluster so a shard containing one of each pays both
> fixed costs. SP1 stops at ~30 chips in the base core cluster. Merging costs $+1$ selector column on **every** row and
> $+1$ degree wherever it multiplies a constraint -- SP1 deliberately does *not* merge its two memory-boundary chips.

## VI.2 The adapter/core split, and why it makes the split above pay

AIR with a bus

Width is additive:
```rust
fn width(&self) -> usize { self.adapter.width() + self.core.width() }
let (local_adapter, local_core) = local.split_at(self.adapter.width());
```
(OpenVM `arch/integration_api.rs:220-278`). One `Rv32BaseAluAdapterAir` -- 2 reads, 1 write, execution bridge -- is shared
by ALU, shift, less-than, mul, mulh and divrem, and the core hands over reads/writes as `AB::Expr` with **zero columns of
glue**.

The flip side is that a 2-read/1-write adapter carries $\approx 15$--20 columns and 6 memory-bus messages on **every row of
every ALU chip**, whether the core is 3 columns (ADD) or 40 (DIV).
**That is why subcase splitting pays: the core is what you delete, and the adapter stays.**

> **Where it stops.** The adapter multiplies `is_valid` into bus multiplicities, so the contract is a degree-1 `is_valid`
> and degree-$\le$1 read/write expressions -- *"Adapters should document the max constraint degree as a function of the
> constraint degrees of `reads, writes, instruction`"* (`integration_api.rs:43`).
> You cannot amortize an adapter over rows unless you pack multiple operations per row, and each extra read is another
> 3 columns and 2 messages.

## VI.3 Adding a chip is a build-system cost, not a marginal one

Universal, recursive systems

In SP1 v5, "shape" means *which chips exist*, not how tall they are:
```rust
pub fn smallest_cluster(&self, chips) -> Option<&BTreeSet<Chip<F,A>>> {
    self.chip_clusters.iter().filter(|c| chips.is_subset(c)).min_by_key(|c| c.len())
}
```
(`hypercube/src/machine.rs:9-36`) -- and **every shard is charged for the whole cluster**, not just the chips it used.
The catalogue then multiplies out: ~30 clusters $\times$ 194 main-area buckets $\times$ 35 preprocessed-area buckets, each
one a compiled recursion program with its own vk (`prover/src/shapes.rs:702-747`).
The design response is visible in the source: instead of the power set of 6 extensions (64 clusters) they ship **8**,
taking only $\binom E0$, $\binom E1$ and $\binom EE$ -- so a program mixing two extensions jumps straight to
all-extensions and pays for all six (`riscv/mod.rs:738-746`).

> **Where it stops.** This is specific to systems with a precompiled recursive verifier per shape. In a system without one,
> a new chip costs only its own area.

## VI.4 Shard boundaries are the most expensive rows in the machine

Universal, sharded

SP1 charges each address touched across a boundary **one `MemoryLocal` row and two `Global` rows**:
$20 + 2\times241 = \mathbf{502}$ cells per touched address (`executor/src/utils.rs:139-140`) -- 15$\times$ a whole `Add`,
2$\times$ a `DivRem`. And the shard checker assumes all 32 registers are re-touched every shard, i.e. 16,064 cells of
unavoidable tax per shard.
OpenVM's is the same law expressed as Merkle re-hashing: per page fault, $2\cdot2^{\text{PAGE\_BITS}}$ boundary rows plus
$2\cdot\text{nodes\_per\_page}$ merkle rows plus the corresponding Poseidon2 -- every factor of 2 being "init tree + final
tree" (`metered/memory_ctx.rs:262-273`).

**The design lever is locality**, not cleverness: SP1 charges the 502 only on the first touch per shard, so batching calls
that touch the same buffer collapses many 502s into one.

## VI.5 Read-only data needs no timestamp at all

Universal

The single biggest structural saving in the memory layer.
OpenVM's program table is a **`LookupBus`**, not a permutation bus: the key is $(pc, \text{opcode}, \text{operands})$ with a
multiplicity and nothing else -- no timestamp, no previous value -- backed by a preprocessed trace whose only main column is
`exec_freq` (`program/{bus.rs:9-11,air.rs:18,62-67}`).
**0 memory columns, 0 timestamp, 1 lookup per fetch**, against $\approx 7$ columns + 2 interactions + 2 range lookups if the
ROM were modelled as memory (VII.1).

> **Where it stops.** The instant the data can change. Two guards are required: the table must be preprocessed/committed so
> its contents are fixed by the verifying key, and nothing may write to that address range -- self-modifying or untrusted
> code needs a different path (SP1's untrusted-program mode plus a page-protection bus).
> RISC Zero, which keeps the i-cache in real memory, therefore *does* pay a monotonicity lookup for fetch -- but a
> **non-strict** one, $(cycle - loadCycle)\cdot2$, so many fetches can share a cycle (`decode.ipp:30`).

## VI.6 ISA and layout choices are constraint choices

Universal

The cheapest constraint is the one you never write. Five documented instances:

- **Delete the register file.** Valida has no general-purpose registers: every operand is an `fp`-relative memory offset, so
  the effective address `fp + operands.a()` is degree 1 and the whole register-file AIR and its permutation argument
  disappear. Price: 3 memory channels budgeted on *every* CPU row (21 columns) whether used or not.
- **Count instructions, not bytes.** Valida's `pc` is an instruction index, so the sequential update is `pc + 1` and a
  byte-address branch target is handled by multiplying the *other* side by 24 rather than dividing. Only possible with a
  fixed-width encoding -- which is itself an argument for one.
- **Bound the state motion.** Miden: all operations shift the stack by at most one item, and depth never drops below 16.
  That collapses all stack motion into two flags and one depth constraint.
- **Allow only power-of-two structure.** Miden's batch group count is 1, 2, 4 or 8, padded with NOOPs -- three flag columns
  instead of a 4-bit count and a comparison.
- **Choose the operand encoding so the table decomposes.** Jolt *interleaves* the bits of $x$ and $y$ rather than
  concatenating them, because concatenation has no prefix/suffix structure while interleaving makes XOR split additively at
  any even cut. Zero constraint cost -- it is purely a choice of index encoding -- and it converts an intractable table into
  eight $\Theta(T)$ phases.

> **Where it stops.** These are bets that the proof metric dominates the cycle metric, and Miden documents the failure mode
> exactly: trace length is $\max(\text{stack rows}, \text{range rows}, \text{chiplet rows})$ rounded to a power of two, so
> *"Mixing opcode types unevenly can thus produce a cycle-efficient program that is still proving-expensive."*
> An ISA tuned to shrink one segment can silently make another the binding one.

## VI.7 Two measured negative results, kept for calibration

Universal

**Width is not the objective.** OpenVM deleted 12 specialized pairing opcodes, *"removed 16527 columns"* -- and cells went
**25.4M -> 92.6M (3.65$\times$)** because the work reappeared as many more rows in generic chips (`openvm#1413`).
**Optimize $\text{width}\times\text{padded height}$, never width alone.**

**Padding eats small width wins.** Thinning `AddSub` from 34 to 32 columns and 20 to 19 interactions projected 1.63B cells;
it measured **0.12B** -- *0.2% of total cells* -- because each chip pads to its own power-of-two height (`openvm#2957`).
The author's conclusion is the right one: the effort belonged in splitting *all* the immediate chips, not thinning one.

---

# Part VII -- Memory and mutable state

The circuit-design side of a memory argument. How the argument is *proved* is out of scope; what it costs per access is not.

## VII.1 One access is two interactions, and a read is a cheaper write

AIR with a bus

Every logical access is a *receive* of the old tuple and a *send* of the new one on the same bus:

```rust
self.memory_bus.receive(address, prev_data, prev_timestamp).eval(builder, enabled);
self.memory_bus.send(address, data, timestamp).eval(builder, enabled);
```
(OpenVM `offline_checker/bridge.rs:326-332`). A **read is literally a write with `prev_data = data`** (`:233`).
Nothing constrains that `prev_data` matches an earlier row -- the multiset does that.

The saving that falls out: reads need no `prev_data` columns.
`MemoryReadAuxCols { base }` vs `MemoryWriteAuxCols { base, prev_data: [T; N] }` -- with $N=4$ and `AUX_LEN=2`,
**3 columns versus 7**.

The measured cost sheet, worth memorizing as calibration:

| | columns/access | interactions | lookups |
|---|---|---|---|
| openvm read (BLOCK=4) | 3 | 2 | 2 |
| openvm write (BLOCK=4) | 7 | 2 | 2 |
| openvm read-or-immediate | 5 | 2 (count 0 if imm) | 2 |
| sp1 general memory | 9 | 2 | 2 |
| sp1 register | 6 | 2 | 2 |
| risc0 read | 4 | 2 | **1** |
| risc0 write | 6 | 2 | 1 |
| **program ROM fetch (openvm)** | **0** | 1 (lookup) | 0 |

> **Where it stops.** Three obligations. Some chip must send the initial state and receive the final state of every cell, or
> the multiset balances against fabricated history. Any chip that can emit an unpaired send forges memory.
> And the read/write saving holds **only if the sent `data` is bit-identical to the received `prev_data`** -- a
> "read and sign-extend in place" shortcut silently becomes a write of the extended value.

## VII.2 Timestamps: the free ones, the derived ones, and the 29-bit wall

AIR with a bus

**Free.** risc0 never stores the current timestamp -- it is `cycle*2` for reads and `cycle*2+1` for writes, and only
`prevCycle` is a column (`circuit/mem.ipp:34,52`).
**Constant-offset slots.** SP1 gives each access within an instruction a compile-time slot: `clk_low + MemoryAccessPosition`
(`adapter/register/r_type.rs:115-121`), zero columns.
**Derived limbs.** For registers, only the *low* limb of $t - t_{\text{prev}} - 1$ is witnessed; the high limb is an
expression, range-checked directly (`air/memory.rs:340-359`) -- $-1$ column and $-1$ constraint per access.
**Two columns instead of five.** SP1's register accesses drop `prev_high` and `compare_low` entirely, paid for by a
*shadow read* in a `MemoryBump` chip that re-syncs every register when the clock's high limb rolls over:
*"we ensure that all register accesses have the high limb of the timestamp and previous timestamp to be equal ... through
adding in a 'shadow' read"* (`memory/consistency/columns.rs:12-27`) -- **9 columns saved on every ALU row**.

**The wall.** Monotonicity is a range check on $t - t_{\text{prev}} - 1$, and it inherits II.5's bound:
$\text{max\_bits} \le 29$ on BabyBear, which means the **whole trace's timestamp span** must fit in 29 bits.
And per-access checks are worthless without a *global* bound: OpenVM range-checks the segment's final timestamp in two
limbs for 1 column and 2 lookups (`connector/mod.rs:214-225`), without which a prover sets the initial timestamp *above*
the final one and reorders memory freely ([High], VIII.30).

> **Where it stops.** Slot offsets need $\#\text{slots} \le \text{CLK\_INC}$; SP1 sets `CLK_INC = 8` with 5 slots and
> *proves* the lattice with one lookup ($(clk-1)/8 < 2^{13}$ certifies both $clk \equiv 1 \bmod 8$ and 16-bit-ness).
> Widen the slot set past 8 and instruction $i$'s slot 8 aliases instruction $i+1$'s slot 0.
> risc0's $\times2$ spacing gives exactly **two** slots per cycle -- a read and a write are fine, *two reads* of the same
> address collide, which is why the `sameReg` coalescing gadget exists (VII.4).
> And the table must cover the trace: risc0's own source carries the live TODO
> *"table size needs to handle max cycles * 2, this presumes no more than 10 cycles per row"* -- exceed it and monotonicity
> silently stops being enforced.

## VII.3 One bus for every address space; reserve space 0

AIR with a bus

Key the tuple on $(\text{address\_space}, \text{pointer})$ and the register file, RAM, public-values space and native space
all share one chip and one argument -- 1 extra field element per interaction, saving an entire duplicated chip and boundary
machinery per space (`offline_checker/bus.rs:90-94`).
Reserving space 0 as "not memory" then deletes a constraint outright:

> *"We do not need to constrain `address_space != 0` since this is done implicitly by the memory interactions argument
> together with initial/final memory chips."* (`bridge.rs:138-140`)

and lets the same flag be both the space tag and the read multiplicity: `rs2_as ∈ {0,1}` is passed **directly** as the
address space *and* as the count, so an immediate operand costs no memory interaction at all
(`adapters/alu.rs:121-132`).

> **Where it stops.** That deleted constraint is a **global** argument: every boundary chip must only ever emit space $\ge 1$.
> Break the boundary chip's coverage and space 0 becomes a free-write oracle.
> The flag-as-multiplicity trick needs three side conditions, all present in the source and all forgettable: the tag must be
> boolean; it must be *forced off* on padding rows (`when(rs2_as).assert_one(is_valid)`); and when it says "immediate", the
> data must be **constrained** to the immediate, or the prover reads an unconstrained value for free.

## VII.4 Registers, `x0`, and aliasing

Universal

- **Registers are just memory.** risc0 typedefs `RegMemReadBlock = PhysMemReadBlock` at a fixed base.
  SP1 puts registers at addresses $< 2^{16}$ of the same flat space and fences RAM off them with **one column**:
  ```rust
  // Check that `addr >= 2^16`, so it doesn't touch registers.
  builder.assert_eq(cols.top_two_limb_inv * sum_top_two_limb, is_real);
  ```
  (`operations/address.rs:84-87`). The fence must be on *every* chip that computes an address.
- **`x0` writes: redirect the address, don't gate the multiplicity.** risc0 adds 64 words when the register index is zero so
  the write lands in dead space -- multiplicity stays a constant 1, so there is no `assert_bool` on a count and no degree
  increase (`inst.ipp:147-153`). The alternative, a conditional write, needs the flag pinned *externally*: OpenVM publishes
  `needs_write` as operand `f` on the program bus so the **program** decides (`adapters/rdwrite.rs:101-126`); un-pinned, it
  is a free write-suppression oracle.
- **Turn a write into a read for free** by passing `prev_value` as the write value, when you need the timestamp bump but not
  the change (SP1 `r_type.rs:132-153`).
- **Aliasing is the classic trap.** risc0's `DualReg` coalesces `rs1 == rs2` with one bit and one quadratic constraint, and
  its comment enumerates all four cases -- relying on **the memory argument itself** to reject `sameReg = 0` when they alias
  (the missing `PICUS_ASSERT` is flagged as a TODO in-source). That only works because the timestamp is unique per
  (cycle, slot); it *depends on* VII.2's spacing.

## VII.5 Two structural wins: block granularity and lazy normalization

Universal

**Block granularity.** The bus carries a `BLOCK`-sized data vector, not one cell: OpenVM fixes `DEFAULT_BLOCK_SIZE = 4`
even though `lb`/`lh` need fewer bytes, amortizing the `prev_timestamp` and lt-aux overhead over the block.
Sub-block access must then be decoded *outside* the bus and the alignment constrained, which SP1 buys with exactly one
lookup (V.6).

**Lazy normalization.** Instruction chips send `clk_low + increment` and `pc + 4` *without* carry propagation or range
checks; a dedicated `StateBumpChip` receives the non-canonical state and re-emits a canonical one, paying the carry logic
once per **overflow event** rather than once per row (`adapter/{state.rs:82-88,bump.rs:191-235}`).
The precondition is named in-source: *"`is_clk` is a boolean value. This is possible because the `clk` does not increment by
more than $2^{24}$ in a single instruction cycle"* -- a big precompile that jumps the clock further breaks it.

The same idea at limb level is **overflow/lazy limbs**: OpenVM's mod-builder lets BigInt limbs exceed `limb_bits` during
intermediate arithmetic and materializes a new witness column only when the implied carry width would exceed the budget:
```rust
if carry_bits > a.max_carry_bits { a.save(); }   // max_carry_bits = MODULUS_BITS - limb_bits - 2
```
(`mod-builder/src/field_variable.rs:107`, `builder.rs:101`) -- IV.4 automated, with the bound
`overflow_bits <= floor(log2 p) - 1` so negative limbs cannot alias positive ones.

---

# Part VIII -- Non-native and big-integer arithmetic

The CRT/bound discipline is shared with R1CS (`r1cs.md` Part IV and `techniques.md` §2). What is AIR-specific is that the
identity is checked **coefficient-wise**, which turns a big-integer multiply into a wide row of degree-2 constraints.

## VIII.1 The coefficient-wise vanishing identity

Universal

Write every value in base $B$ as a polynomial and form
$$V(x) = \text{op}(x) - \text{result}(x) - \text{carry}(x)\cdot p(x)$$
If the integer identity holds with honest digits then $V(B) = 0$, so $(x - B) \mid V(x)$. Witness the quotient
$W(x) = V(x)/(x-B)$ and assert $V - W\cdot(x-B) = 0$ **coefficient by coefficient**:

```rust
let root_monomial = Polynomial::new(vec![-limb, one]);          // (x - 2^8)
let constraints = p_vanishing - &(p_witness * root_monomial);
for constr in constraints.as_coefficients() { builder.assert_zero(constr); }
```
(SP1 `operations/field/util_air.rs:12-26`).
Price for $n$ limbs: `result` $n$ + `carry` $n$ + `witness` $2n-2$ = $\mathbf{4n-2}$ columns and $2n-2$ **degree-2**
constraints. $n=32$ gives 126 columns per modular multiply, with **no bit decomposition anywhere**.

> **Where it stops.** The $\mathbb F_q$ coefficient identity must lift to $\mathbb Z$: every coefficient of both sides must
> be $< q/2$ in absolute value. $|V_k| \le n(B-1)^2 + n(B-1)^2 + (B-1) \approx 4.2\times10^6$ for $n=32$, comfortably under
> $2^{30}$ -- but the bound is what caps $n$, and it is what forces chunking (VIII.3).

## VIII.2 The witness offset, derived rather than guessed

Universal

The witness coefficients are running polynomial carries, computed by a Horner-from-the-top pass with
`debug_assert_eq!(pol_carry, 0)` -- which *is* the statement $V(B)=0$ (`field_op.rs:87-94`). Hence
$$W_j = V_{j+1} + B\,W_{j+1} \quad\Longrightarrow\quad |W_j| \;\le\; \frac{\max_k|V_k|}{B-1}$$
Plug in: $n=32$ gives $2\cdot32\cdot255 = 16{,}320 < 2^{14}$; $n=48$ (BLS12-381) gives $24{,}480 < 2^{15}$.
Those are **exactly** the shipped constants (`secp256k1.rs:40`, `bls12_381.rs:43`, `ed25519.rs:29`).

**Rule: $\text{WITNESS\_OFFSET} \gtrsim 2n(B-1)$ for a single multiply, times the number of summed products.**
secp256k1 at $2^{14}$ has 0.4% headroom -- this is a tight constant, not a round number.

The offset itself exists only because $W$ is *signed* and range tables are unsigned: the trace stores $W_j + 2^k$ and the
AIR subtracts the constant back as a free degree-0 term. The same bias trick appears in OpenVM's `check_carry_to_zero`,
with its own hard assertion `carry_abs_bits + limb_bits < F::bits() - 1` "so that it is contained in $[-p/2, p/2]$".

> **Where it stops.** The proven bound is *asymmetric*: range-checking the shifted column proves
> $W \in [-2^k, 2^{16}-2^k)$, which is fine for the lifting argument and not fine if $W$ is reused elsewhere.
> And trace generation must use an **arithmetic shift**, not division, for negative carries -- OpenVM's README shows
> $-63 \gg 2 = -16$ versus $-63/4 = -15$.

## VIII.3 One gadget, four operations -- by rewriting the identity

Universal

Sub and Div are never computed forward; they are checked in reverse, reusing the *same* vanishing polynomial with $a$ and
`result` swapped:

```rust
let (p_a, p_result) = match op {
    Add | Mul => (p_a_param, self.result.into()),
    Sub | Div => (self.result.into(), p_a_param),     // swap
};
```
(`field_op.rs:470-477`). $a-b=r \Leftrightarrow r+b=a$; $a/b=r \Leftrightarrow r\cdot b=a$.
**Division needs no inverse chip and costs exactly one multiplication**, with the same column count as add.

Three refinements on the same theme:
- `FieldDenCols` folds a $\pm1$ into the same $b\cdot r$ product, so $a/(1\pm b)$ is one gadget -- in ed25519 point addition
  that replaces two inversions and two muls with two den-cols.
- `FieldInnerProductCols` batches $L$ products into **one** carry and **one** witness set, saving $(L-1)(4n-2)$ columns.
- Non-zeroness is proven by running the *same* Div gadget with numerator 1 (`weierstrass_add.rs:470-482`) -- cheaper and
  lower-degree than an `IsZero` over limbs plus a reduction.

> **Where it stops.** Each has a stated precondition that is not a circuit fact.
> `/0` is unconstrained ("the constraints do not check for division by zero", `field_op.rs:28`).
> `FieldDenCols` assumes the denominator is never zero -- for Ed25519 that is true because $d$ is a non-square, a *curve*
> fact. The inner product's batching limit is quantitative: $(L+1)n(B-1)^2 \le (B-1)\cdot\text{OFFSET}$ gives
> $\mathbf{L \le 2}$ at $n=32$ with $2^{14}$, which is exactly what the code uses, and the source says so.
> Proving $\ne 0$ in $\mathbb F_p$ still needs canonicity, or $b = p$ also passes.

## VIII.4 Chunking, blending, and multiplexing

Universal

- **Chain the chunks by passing carry columns as the next addend.** `u256x2048_mul` threads `outputs[i-1].carry` directly
  into `eval_mul_and_carry` for step $i$ -- no copy constraints, no extra columns (`u256x2048_mul/air.rs:615-633`).
  This *is* the workaround for VIII.2's bound: a single 2048-bit gadget would need
  $\text{OFFSET} \approx 2\cdot256\cdot255 = 130{,}560 > 2^{16}$.
- **Blend two moduli instead of branching.** `p_modulus = modulus_poly * (1 - is_zero) + x^{32} * is_zero` makes one chip
  cover "mod $m$" and "mod $2^{256}$" (`uint256/air.rs:412-419`), with `modulus_is_zero` computed by **one** `IsZero` on
  the byte *sum* (II.15).
- **Multiplex the operation with selector-weighted polynomials.** `p_op = p_add*is_add + p_sub*is_sub + ...`
  (`field_op.rs:391-400`) -- $k-1$ selector columns, degree 3, saving an entire chip and its memory plumbing per opcode.
  The syscall id is a blend too, so one chip receives three syscalls.

> **Where it stops.** Blending and multiplexing both spend degree on the same budget, and they do not compose: at a degree-3
> cap you get bilinear-times-one-flag and cannot also multiplex the modulus in the same gadget.

---

# Part IX -- The PLONKish model

A different cost model, kept separate because the two do not mix. Rows $\times$ columns is still the area, but three things
change: **copy constraints exist and are not free**, **gates are custom and are packed into rows**, and **selectors have
their own economics**.

## IX.1 Rotations replace copies -- and a copy is not free

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

## IX.2 Advice (unrouted) wires for anything no gadget reads

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

## IX.3 Gate packing: `num_ops` comes from the wire budget

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

## IX.4 Selector grouping is the tax nobody expects

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

## IX.5 Trading degree for wires inside one gate

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

## IX.6 halo2's decomposition family

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

## IX.7 Kimchi: designing to a hard budget

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

# Part X -- Traps

Every entry is a documented failure mode, and every one of them arises **precisely from an optimization**.
Three rules generate most of the list:

1. **A gadget's documented assumption is a constraint someone still has to write.**
2. **If a value steers a message, it belongs in the message.**
3. **The trace layout is the prover's choice, not trace-generation's.**

## X.1 Row-boundary traps

**Wraparound.** The trace domain is cyclic: `next` at the final row *is* row 0
(`plonky3/air/src/check_constraints.rs:564`). An ungated step relation lets the prover treat the trace as a **ring** --
a cycle $s_0\to\dots\to s_{N-1}\to s_0$ with no distinguished start satisfies every transition constraint while never
touching the real initial state. `when_transition()` is degree-free (III.2); there is no excuse.

**The opposite error.** Once everything is transition-gated, the last row has *no* constraints, and the terminal boundary
assertion never gets written. SP1's `FriFoldChip` [High]: a chunk with `is_real = 1` could run off the end and never be
finalized, so memory accesses happened that no syscall paid for. The five-constraint recipe:
(1) flags boolean; (2) `is_last_iteration = 0 ⇒ local.is_real = next.is_real`; (3) `is_last_iteration = 1 ⇒ is_real = 1`;
(4) `is_real = 0 ⇒ next.is_real = 0`; (5) **on the final row**, `is_real = 0` OR `is_last_iteration = 1`.

**One token.** SP1's `exp_reverse_bits` gated its accumulator recurrence with `when_not(is_last)` where
`when_not(is_first)` was meant, leaving the *initial* accumulator unpinned — [High], zero-cost fix.

**Stacking two chips in one table breaks both boundary selectors.** SP1's `MultiBuilder` implemented `is_first_row` as
`global_is_first_row AND local_condition`, which is identically zero for the *second* stacked chip -- its initialization
constraints were silently never placed [High]. The fix (+1 column, ~4 constraints) typically eats the savings that motivated
the stacking.

## X.2 Padding and `is_real`

**Padding rows emit interactions.** SP1's ECALL chip sent a syscall with multiplicity `send_to_table`, a byte of a previous
register value that is unconstrained on padding rows [High] -- free syscalls. The rule is per-bus, per-chip:
`when_not(is_real).assert_zero(mult)` **and** `assert_bool(mult)`.

**Free selectors on padding rows are an arbitrary-memory oracle.** SP1's CPU fetched its instruction with multiplicity
`is_real`, so on padding rows the instruction *and every selector* was prover-chosen -- and the memory lookups keyed off
those selectors [**Critical**]. Force the whole row into a canonical inert shape.

**`is_real` must be boolean, and monotone.** A non-boolean flag scales every gated multiplicity. And "real rows come first"
is a *constraint*, not a fact about your trace generator: interleaving `1,0,1,0` breaks every argument about "the last real
row" -- `when_transition: is_real = 0 ⇒ next.is_real = 0`.

**Padding rows structurally inside a block.** OpenVM's `FriReducedOpeningAir` permitted `workload -> disabled` [High]:
the adversary stops the last block short and the truncated rows' reads and writes belong to no instruction.
Enumerate the state machine's legal successors explicitly.

## X.3 Bus and interaction traps

Beyond V.10's aliasing family:

**Skipping permutation columns when a scope has no interactions** also skips the constraint that its cumulative sum is
**zero**, and the verifier still adds that unconstrained value into the global balance [High].
**Cumulative sums must be observed** in the transcript, or the prover picks them after seeing the challenge; and chip
metadata must come from the *verifier's* vkey, never from the proof.
**A memory read that does not advance the timestamp is a no-op**: the send and receive are identical with opposite signs and
cancel exactly, leaving `data` unconstrained -- *"We could just change the data in the trace to whatever we want, and it
would still be accepted."*
**An initialization table with no uniqueness constraint** lets the prover initialize the same address twice and run two
independent value-histories forward; the argument balances perfectly and memory *semantics* are gone [High].

## X.4 Range, limbs, and small-field overflow

Beyond II.5's $\le 29$-bit cliff:

**Using a comparison gadget without discharging its precondition.** OpenVM's `VolatileBoundaryAir` used
`IsLtArrayWhenTransition` to force strictly increasing addresses, but the gadget *assumes* range-checked operands and the
AIR never did [High]: each pairwise difference stays in $[0,2^{29})$ while the **sum** wraps, so the "strictly increasing"
sequence returns to its start and uniqueness is void.

**Decomposition without canonicity.** 31 bits span $[0,2^{31})$, which strictly contains $[0,p)$ for BabyBear, so about
1 in 15 elements has **two** valid decompositions -- and SP1's fed `sample_bits` for FRI query indices.
The efficient fix is worth copying: compare the top limb against the modulus' top limb and force the rest to zero when
equal, exploiting $p-1 \equiv 0 \bmod 2^{16}$ -- **one column, one lookup** (`operations/sp1_field_word.rs:57-83`).

**Deferred normalization that outgrows two different bounds at once.** OpenVM's `FieldVariable::save_if_overflow` saved when
the carry would exceed the *range checker's* capacity, but with a large `range_checker_bits` the carries could still overflow
the *proving field*. And the reverse cliff is real: making `range_checker_bits` too small means products can never be
range-checked at all -- for $\mathbb F_{p^{12}}$ multiplication the lower bound rose from 17 to 21, which would have grown
the range-checker AIR from $2^{18}$ to $2^{22}$ rows. **You are squeezed between two bounds, and the slack is where the
optimization lives.**

## X.5 Degree reduction and selector traps

**The rewrite that assumes booleanity *and* implication.** `enabled * (1 - is_immediate) → enabled - is_immediate` is an
identity **only** when both are boolean *and* `is_immediate ⇒ enabled`. Otherwise `is_immediate = 1, enabled = 0` gives an
activation flag of $-1$, which flips a send into a receive. OpenVM's own note justifies both premises by hand -- exactly the
kind of justification that rots when a caller is added.

**Selectors that are boolean, or sum to one, but not both.** Sum-to-one without booleanity admits $(2,-1)$: two branches
fire with opposite weights, so $\sum s_i C_i = 0$ is satisfied by $2C_0 = C_1$ rather than by any branch holding.
Booleanity without sum-to-one admits all-zero -- no branch constrained at all.
For the packed encoder (II.7c) **all three** constraint families are mandatory.

**Reusing a column across "mutually exclusive" branches that are not.** Exclusivity is a constraint, not a fact.
Plonky3's exclusive-flag LogUp optimization -- which collapses $n$ branch denominators into one -- says so verbatim:
*"The flags must be boolean. The flags must sum to at most one on every row. The AIR must enforce both rules. This field
only carries the flags."*
SP1's recursion CPU shared memory columns between `is_load` and `is_store`, and the load branch only asserted the memory
value did not *change*, never that the register received it [**Critical**].

## X.6 Cross-shard and aggregation

**Boundary state pinned at one end only.** OpenVM constrained the *final* timestamp $< 2^{29}$ but left the **initial** one
free, so the prover sets it *greater* than the final one, the total increase is up to $p$, and every memory-ordering check
becomes unsound [High]. Note from III.2 that first/last-row selectors are the *expensive* ones -- which is precisely the
temptation to skip them.

**A field that never enters the hash it is supposed to be bound by.** SP1 v4 added `initial_global_cumulative_sum` to the
verifying key without adding it to the vk hash or the challenger observation, so two vks collided [High].
**Adding a vk/public-values field is a three-site change** -- struct, hash, observe -- and the compiler checks none of them.

---

# Part XI -- Knowing when to stop

## XI.1 The floors that exist

Universal

Unlike R1CS (`r1cs.md` Part V), there is no clean geometric floor on trace area -- the trace is a *layout*, not a variety.
What you do have:

- **The interaction floor.** A value that must cross a chip boundary costs at least one message of its own width on both
  sides. Splitting is bounded below by that (V.11).
- **The degree floor.** A relation of algebraic degree $d$ needs $\lceil\log_2 d\rceil$ committed intermediate steps if the
  budget is 2, and exactly $\lceil d/(\text{budget}-1)\rceil$ splits in general (IV.4). $y = x^5$ under a degree-3 budget is
  two columns, and no trick removes them.
- **The table floor.** A lookup table costs $2^{\text{key bits}}$ rows *in every shard that touches it*, and that number is
  in the code, not in your estimate (V.12).
- **The padding floor.** Under power-of-two padding, a chip used $n$ times costs $2^{\lceil\log_2 n\rceil}$ rows, and no
  column reduction changes that (I.3).

## XI.2 The three checks that actually catch things

Universal

- **Evaluate every constraint on every row of a concrete trace**, then **mutate the trace and assert something catches it**.
  Plonky3's `check_constraints` plus proptest mutation tests do exactly this -- each test flips one bit and asserts a
  constraint fires (`keccak-air/src/air.rs:235-417`). It is the only cheap way to discover that an "implicit range check"
  you assumed was there (II.3, X.4) is not.
- **Track the bus, not just the sum.** stwo's `relation_tracker` dumps every $(\text{relation}, \text{tuple},
  \text{multiplicity})$ so you find *which* tuple is unbalanced rather than only that the sum is nonzero.
- **Make forgetting impossible.** stwo panics on `LogupAtRow was not finalized` and on double-finalize; OpenVM asserts its
  degree bound at the end of every optimization pipeline; powdr asserts that all PC lookups vanished.
  A constraint you *cannot* forget is worth more than one you remember today.

> **The honest limit.** `check_constraints` proves your valid traces pass and your specific corruptions fail.
> It does not prove soundness of an under-constrained layout, and no tool in this manual does.
> Treat every "optimal" as "not beaten yet", and every "sound" as "not broken yet".

## XI.3 Re-derive the reported cost from what the system emits

Universal

The same trap as `r1cs.md` VI.1, with sharper teeth here because there are three numbers.
A width improvement that padding eats (VI.7), a column saving that adds an interaction, an interaction saving that adds a
degree -- each shows up as a win in one counter and a loss in another.
**Report the triple (columns, interactions, degree) and the measured cells, or you have not measured anything.**
