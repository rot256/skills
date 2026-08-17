# Constraint degree as an economic resource

*Why the whole system pays for the maximum, why most of the budget is already prepaid, and how to spend it.*

Degree is the one resource in a constraint system that is **global, quantized, and usually under-spent**.
This reference is the arithmetic behind that sentence: what a unit of degree costs in each backend, which values of the
budget are rational, how to detect and spend unused headroom (*degree matching*), when to buy degree back with a column,
and where the whole trade inverts.

Arithmetization-specific material lives in `air.md` (Part IV summarises this file from the AIR side) and `r1cs.md`.

**Notation.** $n$ = trace height, $D$ = the system-wide max constraint degree, $d$ = one constraint's degree,
$b = \log_2(\text{blowup})$, $W$ = trace width, $E$ = extension degree.

---

# Part I -- What a unit of degree costs

## I.1 The quotient identity

FRI-quotient STARK

A degree-$d$ constraint composed with degree-$(n-1)$ trace polynomials has degree $d(n-1)$; Plonky3 states the bound with
the transition-selector correction:

> *"The quotient machinery bounds a constraint of degree `d` by a polynomial of degree at most `d * (trace_len - 1) + 1`
> (the `+ 1` covers the linear transition selector)."* (`plonky3/air/src/symbolic/builder.rs:88-102`)

Dividing by $Z_H$ leaves $\approx (d-1)n$, committed in chunks whose count is **rounded up to a power of two**:

```rust
// We bound the degree of the quotient polynomial by constraint_degree - 1,
// then choose the number of quotient chunks as the smallest power of two >= (constraint_degree - 1).
log2_ceil_usize(constraint_degree - 1)
```
(`plonky3/uni-stark/src/symbolic.rs:84-87`)

**Price.** $2^{\lceil\log_2(D-1)\rceil}$ chunks, each $E$ base-field columns of height $n$, all LDE'd and committed
(`uni-stark/src/prover.rs:187-190,263-264,319`).
halo2 does the same in the KZG setting -- `quotient_poly_degree = cs.degree() - 1`, then
`while (1 << extended_k) < n * quotient_poly_degree { extended_k += 1 }` (`poly/domain.rs:41-53`).
RISC Zero: `num_segment_polynomials = max_degree - 1` (`zkp/src/prove/soundness.rs:175-180`).

> **Where it stops.** The `ceil` is the entire story, and it is the subject of Part II. $D-1 = 5$ and $D-1 = 8$ both cost
> 8 chunks, so degrees 6, 7 and 8 are free upgrades over 5.

## I.2 The blowup cliff: $D \le 2^b + 1$

FRI-quotient STARK

The prover needs the trace on the quotient domain. If that domain is no larger than the committed LDE and shares its coset
shift, this is a **free truncation of an array you already have**; otherwise it is a full iDFT + DFT of the whole trace:

```rust
if domain.shift() == Val::GENERATOR && lde.height() >= domain.size() {
    return lde.split_rows(domain.size()).0.as_cow().bit_reverse_rows();
}
// ... otherwise coset_idft_batch, truncate, resize, coset_dft_batch
```
(`plonky3/fri/src/two_adic_pcs.rs:376-404`; the quotient domain's shift *is* `Val::GENERATOR`,
`commit/src/domain.rs:236`).

So the branch reduces exactly to $2^b \ge 2^{\lceil\log_2(D-1)\rceil}$, i.e. $\boxed{D \le 2^b + 1}$.
Crossing it costs one `coset_idft_batch` over the full $W$-wide LDE plus one `coset_dft_batch` -- roughly a doubling of the
prover's DFT bill for a 300-column AIR.

**Three independent teams picked $D - 1 = \text{blowup}$.**
Plonky2: `rate_bits: 3`, `max_quotient_degree_factor: 8` (`plonk/circuit_data.rs:108-118`), with
`max_fft_points = 1 << (degree_bits + max(rate_bits, log2_ceil(quotient_degree_factor)))` (`circuit_builder.rs:1179`) --
the config is tuned to make that `max` a tie.
RISC Zero: `INV_RATE = 4` and `num_segment_polynomials = 4`.
OpenVM inverts the relation and *derives* the blowup from the degree:
```rust
let mut log_blowup = 1;
while config.max_constraint_degree > (1 << log_blowup) + 1 { log_blowup += 1; }
```
(`openvm/crates/vm/src/utils/stark_utils.rs:84-87`).

> **Where it stops.** This is why raising $D$ from 3 to 7 in a VM is never a local change: it takes $b$ from 1 to 3 and
> **quadruples the LDE of every column of every chip**, not just the chip that wanted the degree (worked in III.2).

## I.3 Degree spends two-adicity, i.e. it caps trace height

FRI-quotient STARK

The quotient domain must exist, and in a two-adic field it does not exist above $2^{\text{TWO\_ADICITY}}$
(`plonky3/commit/src/domain.rs:223-237`; surfaced as `QuotientDomainTooLarge`).
OpenVM computes the ceiling and enforces it before proving (`arch/vm.rs:716-718`).

BabyBear, `TWO_ADICITY = 27`:

| $D$ | $\lceil\log_2(D-1)\rceil$ | max trace height |
|---|---|---|
| 2 | 0 | $2^{27}$ |
| 3 | 1 | $2^{26}$ |
| 4--5 | 2 | $2^{25}$ |
| 6--9 | 3 | $2^{24}$ |
| 10--17 | 4 | $2^{23}$ |

> **Where it stops.** Goldilocks has `TWO_ADICITY = 32`, so the cap almost never binds; on BabyBear/KoalaBear it binds at
> production shard sizes. Note this table has **the same bracket structure** as II.1 -- height is lost only at bracket
> boundaries, never inside one.

## I.4 The soundness price is logarithmic -- and that is a trap

Universal

Degree enters the DEEP-ALI out-of-domain error linearly, hence the *bit* count logarithmically:
$$\varepsilon_{\text{DEEP}} = L^+ \cdot \frac{\max\deg \cdot (k + \max\text{combo} - 1) + (k-1)}{|F|}$$
(`plonky3/security/src/deep.rs:3-28`).
$D: 3 \to 7$ costs $\log_2(7/3) \approx 1.22$ bits; $D: 3\to 9$ costs $\approx 1.58$. Recover them with one extra FRI query
or two grinding bits.

> **Where it stops -- and this is the trap.** Degree looks nearly free in the soundness spreadsheet and is brutally
> expensive in the prover's concrete cost (I.1--I.3). **Never budget degree from the soundness analysis.**
> Note also that the AIR-composition error depends on the *number* of constraints, not their degree
> (`plonky3/security/src/stark.rs:46`), so splitting one degree-$d$ constraint into $k$ degree-2 constraints trades a
> $\log d$ term for a $\log k$ term -- a wash.

## I.5 Degree is in the proof, and worse in a recursive verifier

FRI-quotient STARK

Every quotient chunk is opened at $\zeta$ and shipped (`uni-stark/src/prover.rs:378`), and the verifier recombines them
through Lagrange coefficients over the split domains (`verifier.rs:97-131,363`).
Price: $2^{\lceil\log_2(D-1)\rceil}\cdot E$ extension elements plus their Merkle paths **in every query round**.

> **Where it stops.** In a recursive setting the verifier's recombination is itself constrained, so quotient chunks cost
> *recursion-circuit rows*. That is why recursion layers pick small $D$ even when the app layer does not.

## I.6 Zero-knowledge costs exactly one degree

FRI-quotient STARK

```rust
let constraint_degree = (degree_hint + is_zk).max(2);
```
(`plonky3/uni-stark/src/symbolic.rs:23,64`; same in `batch-stark/src/symbolic.rs:77`).

> **Where it stops -- and nobody documents this.** If your AIR sits at $D = 2^j + 1$ (a bracket *top*, II.1), enabling ZK
> pushes you to $2^j + 2$ and **doubles the quotient chunk count**: $D=9$ + ZK $\to 10 \to 16$ chunks.
> **Any AIR that may later be proven in ZK mode should target $D = 2^j$, one below the bracket top.**

---

# Part II -- Degree matching

## II.1 The bracket theorem: only $D \in \{3, 5, 9, 17, 33\}$ are rational

FRI-quotient STARK

Every cost in Part I is a function of $2^{\lceil\log_2(D-1)\rceil}$, never of $D$ itself. That quantity is **constant** on
$$D \in [\,2^{j-1}+2,\; 2^j+1\,] \;\Longrightarrow\; 2^{\lceil\log_2(D-1)\rceil} = 2^j$$
i.e. the brackets $\{3\}$, $\{4,5\}$, $\{6,7,8,9\}$, $\{10..17\}$, $\{18..33\}$.
**Within a bracket degree is completely free**: quotient chunks, LDE size, FFT size, opening count, two-adicity
consumption and the blowup requirement are all identical.

Practitioners converged on bracket tops:

| system | $D$ | bracket top? | citation |
|---|---|---|---|
| Miden VM | 9 | yes ($2^3+1$) | `docs/src/design/index.md:24` |
| Plonky2 selector budget | 9 | yes | `plonk/circuit_builder.rs:1151` (`quotient_degree_factor + 1`) |
| RISC Zero | 5 | yes ($2^2+1$) | `zkp/src/prove/soundness.rs:175` |
| SP1 Hypercube | 3 | yes ($2^1+1$) | `hypercube/src/chip.rs:17` |
| OpenVM (default) | 3 | yes | `arch/config.rs:33` |
| powdr $\to$ OpenVM | $2b+1$ | yes for $b\in\{1,2\}$ | `powdr/openvm/src/lib.rs:97` |
| Plonky3 `Poseidon2Air` (7,0) | 7 | **no** -- inside $\{6..9\}$ | `poseidon2-air/src/air.rs:151-159` |

The last row is the instructive one. A `SBOX_DEGREE=7, SBOX_REGISTERS=0` Poseidon2 AIR reports degree 7 and therefore
pays for 8 quotient chunks -- **the same price as degree 9**. Proven alone, two degrees are on the table for free, enough
to fold an `is_real` selector and a boolean check into the round constraints at zero marginal cost.

> **Where it stops.** Plonky2 does **not** round chunks to a power of two -- it uses exactly `quotient_degree_factor`
> chunks (`circuit_data.rs:496,652`), so its bracket structure is degenerate: cost is linear in $D$ up to `rate_bits`,
> after which the `max(rate_bits, ...)` of I.2 takes over. stwo quantizes even harder (II.5).

## II.2 The rule that follows

FRI-quotient STARK

**Round the declared budget up to the nearest $2^j+1$. Always. It is free.**
halo2 makes this an API, because reserving is free:
```rust
/// Sets the minimum degree required by the circuit, which can be set to a
/// larger amount than actually needed. This can be used, for example, to
/// force the permutation argument to involve more columns in the same set.
pub fn set_minimum_degree(&mut self, degree: usize)
```
(`halo2_proofs/src/plonk/circuit.rs:1182-1187`; `degree()` takes the max with it at `:1398-1425`.)
Plonky3's counterpart is the `max_constraint_degree()` hint: over-declaring is **allowed and silent**, with only a
debug-assert that the hint is not too *small* (`uni-stark/src/symbolic.rs:22-40`).

And the detector for the opposite mistake ships in OpenVM:
```rust
match config.max_constraint_degree.cmp(&max_constraint_degree) {
    Ordering::Greater => tracing::warn!("config.max_constraint_degree ({}) > vk max_constraint_degree() ({})", ...),
    Ordering::Less    => tracing::info!(...),
    Ordering::Equal   => {}
}
```
(`openvm/crates/sdk/src/util.rs:5-24`) -- `Greater` means the prover is paying for degree nobody used, and it is a
**warning**, not a note.

## II.3 The $D-2$ law: degree is running-product capacity

Universal

Any grand-product or running-sum accumulator has the shape $z' \cdot(\text{stuff}) = z\cdot(\text{other stuff})$.
With $z$ and $z'$ each contributing degree 1, exactly $D-2$ multiplicands fit per row.
**Three unrelated codebases state the same constant:**

- halo2: `let chunk_len = pk.vk.cs_degree - 2;` (`plonk/permutation/prover.rs:74`), with the intent spelled out --
  *"We will fit as many polynomials $p_i(X)$ as possible into the required degree of the circuit, so the following will
  not affect the required degree"* (`plonk/permutation.rs:29-34`).
- RISC Zero: *"From one row to the next, (max_degree - 2) bounds the number of accumulated values"*
  (`zkp/src/prove/soundness.rs:217`).
- Plonky2: `chunk_size = max_degree; n.div_ceil(chunk_size) - 1` (`util/partial_products.rs:40-47`).

**Worked.** Plonky2 standard config, 80 routed wires, $D=8$: $\lceil 80/8\rceil - 1 = 9$ partial-product columns,
$\times\,2$ challenges = **18 columns**. At $D=2$: $\lceil 80/2\rceil - 1 = 39$, $\times 2$ = **78 columns**.
**Degree 8 buys back 60 committed columns.**

> **Where it stops.** The $-2$ assumes both $z(X)$ and $z(\omega X)$ appear. Log-derivative arguments have a different
> constant -- see II.4.

## II.4 The LogUp variant: $D-1$ messages per fraction column

AIR with a bus

Plonky3 computes the fraction constraint's degree exactly:
$$\deg = \max\Bigl(1 + \textstyle\sum_i \deg(e_i),\ \max_i\bigl(\deg(m_i) + \textstyle\sum_{j\ne i}\deg(e_j)\bigr)\Bigr)$$
(`plonky3/lookup/src/logup.rs:434-504`; enforced as `assert_zero_ext(common_denominator * frac_local - numerator)` at `:358`).

Batching $k$ unit-degree messages into one fraction column costs degree $1+k$:

| messages/column $k$ | fraction degree | permutation columns for 12 messages |
|---|---|---|
| 1 | 2 | 12 |
| 2 | 3 | 6 |
| 3 | 4 | 4 |
| 8 | 9 | 2 |

**Degree buys permutation-trace width, one column per unit.**
Miden's "at most 7 trace columns in the same trace row" at $D=9$ is the same law with the table side also on the bus.
ZisK's compiler states the fusion rule directly: bus terms fuse only while
`deg(combined_num) <= MAX_CONSTRAINT_DEGREE` and `deg(combined_den) <= MAX_CONSTRAINT_DEGREE - 1`, so at $D=3$ with
unit-degree fields **bus terms fuse exactly two-by-two** (`pil2-components/lib/std/pil/std_sum.pil:337-380`).

> **Where it stops.** Multiplicities are in the budget too, on the numerator side. A degree-2 multiplicity
> (e.g. `is_real * count`) with $k=3$ unit-degree elements ties at 4; at $k=4$ the *count* sets the AIR's degree, not the
> fields. Mutually exclusive branches take a per-branch **max** instead of the sum
> (`plonky3/lookup/src/logup.rs:456-477`) -- that is the escape hatch.

## II.5 Three interaction budgets, and one that is a hard $\deg \le 1$

AIR with a bus

| system | budget | citation | escape |
|---|---|---|---|
| OpenVM primitives | $\deg(\text{count}) + \max(1,\deg x,\deg y)$ | `assert_less_than/mod.rs:70-73`, `is_less_than/mod.rs:62-65` | keep `count` affine; commit $x,y$ |
| powdr | `bus_interactions = identities - 1` | `powdr/openvm/src/lib.rs:97-100` | none; the optimizer respects it |
| **SP1 Hypercube** | **affine only** -- `panic!("degree multiple is too high")` | `hypercube/src/lookup/builder.rs:110-113` | commit an intermediate column |
| Plonky3 LogUp | the formula of II.4 | `lookup/src/logup.rs:445-504` | flagged/exclusive form |

SP1's is the strictest and the most consequential: a message field like `is_real * addr` is *illegal*; you must commit it.
That converts a degree question into a width question unconditionally, which is why SP1's chips are wide and shallow.
powdr's bus budget is one **lower** than its identity budget for exactly the reason in II.4 -- an optimizer using a single
budget would emit unprovable AIRs.

## II.6 Where the free headroom actually goes

Universal

Once the budget is set, spend the slack in this order.

**(a) Fold selectors into bodies instead of committing selector products.**
A degree-1 selector multiplied into a degree-$(D-1)$ body is free; a *committed* product of two flags is a column.

**(b) Any chip that touches a bus has already bought degree 3.**
```rust
if !sends.is_empty() || !receives.is_empty() {
    max_constraint_degree = max(max_constraint_degree, MAX_CONSTRAINT_DEGREE);
}
```
(`sp1/crates/hypercube/src/chip.rs:102-110`) -- a *floor*, not a ceiling. A chip author who keeps a constraint at degree 2
"to be safe" is spending an intermediate column for literally nothing.

**(c) Widen accumulator and bus chunks to $D-2$ / $D-1$ per column** (II.3, II.4).

**(d) Inline intermediate columns away until the budget is full.** This is powdr's entire optimizer:
```rust
pub struct DegreeBound { pub identities: usize, pub bus_interactions: usize }
/// Returns an inlining discriminator that allows everything to be inlined as long as
/// the given degree bound is not violated.
pub fn inline_everything_below_degree_bound(...)
```
(`powdr/constraint-solver/src/inliner.rs:14-17,76-83`) -- each inline deletes one column $\times$ trace height and raises
some constraints' degree, converting free headroom directly into committed-data savings.

**(e) Pick a richer degree-$D$ identity for the same price.**
Miden's 16-bit range check is a set-membership product with exactly $D=9$ roots, and *which* 9 is free:
$\{0,1,2,4,\dots,128\}$ gives a minimum trace length of 1024; $\{0,1,3,9,\dots,2187\}$ gives **64**.
Same degree, same columns, **16$\times$ better** (`miden/docs/src/design/range.md:83-85,137-139`).

## II.7 Saturation done right, in one function

PLONKish (Plonky2)

The most instructive piece of degree-golfing code in any of these repos:

```rust
pub(crate) fn with_max_degree(subgroup_bits: usize, max_degree: usize) -> Self {
    let n_points = 1 << subgroup_bits;
    // Number of intermediate values required to compute interpolation with degree bound
    let n_intermediates = (n_points - 2) / (max_degree - 1);
    // Find minimum degree such that (n_points - 2) / (degree - 1) < n_intermediates + 1
    // Minimizing the degree this way allows the gate to be in a larger selector group
    let degree = (n_points - 2) / (n_intermediates + 1) + 2;
```
(`plonky2/src/gates/coset_interpolation.rs:71-96`)

**Step 1: buy the fewest intermediate wires that fit the budget. Step 2: having already paid for those wires, lower the
degree as far as the same wire count permits** -- because degree below the cap is *not* free in Plonky2's selector-group
accounting (II.8), even though it is free in the quotient accounting.

Worked, `arity_bits = 4`, `max_degree = 8`: $n_{\text{points}}=16$, $n_{\text{int}} = 14/7 = 2$,
$\deg = 14/3 + 2 = 6$. The gate lands at **6, not 8** -- two degrees handed back at zero wire cost, buying two more slots
in its selector group. At `max_degree = 2` it would be 14 intermediates, i.e. **48 extra wires per FRI-arity row.**

## II.8 Selector groups: low-degree gates are packed, not wasted

PLONKish (Plonky2)

> *"Partition the gates into (the smallest amount of) groups $\{G_i\}$, such that for each group $G$,
> $|G| + \max_{g\in G}\deg(g) \le \text{max\_degree}$."* (`gates/selectors.rs:101-113`)

with `max_degree = quotient_degree_factor + 1 = 9`, and the filter a literal product over the other indices
(`gates/gate.rs:143-154,326-333`).
So a degree-$g$ gate consumes $g$ of the budget and **denies $g$ slots to its group-mates**. A single degree-8 gate forces
$|G| = 1$ -- a private selector column. Degree $\ge$ `max_degree` panics outright (`selectors.rs:143-148`).

> **Where it stops.** Degree and *cardinality* are fungible: four degree-2 gates cost $4+2 = 6 \le 9$, but a fifth
> degree-5 gate blows the group. **Reducing one gate's degree by 1 can save an entire selector column across the whole
> circuit** -- a global saving from a local edit.

## II.9 One component's degree taxes every other component

stwo / multi-AIR

```rust
pub fn composition_log_degree_bound(&self) -> u32 {
    self.components.iter().map(|c| c.max_constraint_log_degree_bound()).max().unwrap()
}
```
(`stwo/crates/stwo/src/core/air/components.rs:19-25`) -- "the whole system pays for the maximum" in five lines.
stwo works in log-space, so the budget is quantized to powers of two with no intermediate values at all: **every** Cairo
component declares `log_size() + 1`, a uniform degree-2 budget.

> **Where it stops.** One component asking for degree 3 moves the global bound to `log_size + 2`, doubling the
> composition-evaluation domain for the *entire* Cairo AIR -- dozens of components, hundreds of columns. That is why
> `cube_252` exists as a separate component with an intermediate column rather than a cubic constraint inline.
> And the free-headroom argument runs the other way here: at `log_size + 2`, degrees 3 **and** 4 cost the same, so a
> system that ever needs 3 should design for 4.

---

# Part III -- Buying degree back with a column

## III.1 The split: one column $\times$ trace height, and only worth it at the global max

Universal

Replace $y = f(x)$ of degree $d$ by a committed $t$ with $t = f_1(x)$ and $y = f_2(t)$, $d_1 + d_2 \approx d$.
The canonical instance:

```rust
(7, 0) => x.exp_const_u64::<7>(),                       // degree 7, 0 columns
(7, 1) => { builder.assert_eq(committed_x3, x.cube());  // degree 3
            committed_x3.square() * x }                  // degree 3
(11, 2) => { ... }
```
(`plonky3/poseidon2-air/src/air.rs:305-340`; degrees tabulated at `:151-159`:
$(3,0)\to3$, $(5,0)\to5$, $(7,0)\to7$, $(5,1)|(7,1)|(11,2)\to3$).
Price: exactly `SBOX_REGISTERS` columns per S-box.

> **Where it stops -- the single most common degree-golfing mistake.** *The split pays only if the constraint being split
> is the global maximum.* If anything else in the AIR is already at degree 7, splitting the S-box to 3 buys nothing and
> costs 141 columns. Plonky3 makes the global degree computable before you commit anything
> (`get_max_constraint_degree`, `air/src/symbolic/builder.rs:104-159`), so there is no excuse for guessing.

## III.2 Worked break-even #1 -- Poseidon2 registers: 141 columns against 4 quotient chunks

FRI-quotient STARK

BabyBear, `WIDTH = 16`, `HALF_FULL_ROUNDS = 4`, `PARTIAL_ROUNDS = 13`, `SBOX_DEGREE = 7`,
width $W(R) = 16 + 8(16R+16) + 13(R+1)$:

| $R$ | $D$ | $W(R)$ | chunks | quotient base cols ($\times E{=}4$) |
|---|---|---|---|---|
| 0 | 7 | 157 | 8 | 32 |
| 1 | 3 | 298 | 2 | 8 |

Registers cost $298-157 = \mathbf{141}$ columns, a $1.90\times$ width increase.

**Committed cells** at $b=3$ (both configs avoid the I.2 cliff):
$R{=}0$: $(157+32)\cdot 8n = 1512n$. $R{=}1$: $(298+8)\cdot 8n = 2448n$. -> **high degree wins commitment by $1.62\times$.**

**Constraint-evaluation cells** (AIR evaluated over the quotient domain at full width):
$R{=}0$: $8n \times 157 = 1256n$. $R{=}1$: $2n\times 298 = 596n$. -> **low degree wins evaluation by $2.11\times$.**

**Break-even.** With $h$ = cost of committing one field element and $e$ = cost of one column-point of constraint work,
high degree wins iff
$$(2448-1512)\,h \;>\; (1256-596)\,e \quad\Longleftrightarrow\quad \frac he > \frac{660}{936} \approx 0.705$$
For a Poseidon2-based Merkle tree over BabyBear that ratio is comfortably above 1 -- which is why Plonky3's Poseidon2 AIR
defaults to the wide-degree form. For a Keccak/Blake3 tree on a machine with vectorized field arithmetic it can flip.

**The decisive term is not in that table.** OpenVM picks $R=1$ anyway, because at $D=7$ the required blowup goes from
$2^1$ to $2^3$ (I.2), multiplying the committed cells of **every chip in the VM** by 4:
```rust
if max_constraint_degree >= 7 { Self::Register0(...) } else { Self::Register1(...) }
```
(`openvm/crates/vm/src/system/poseidon2/mod.rs:45-51`, with `DEFAULT_POSEIDON2_MAX_CONSTRAINT_DEGREE = 3`).

> **The rule.** Degree-vs-width is a *chip-local* optimization only while the blowup does not move. The moment
> $D$ crosses $2^b+1$ it becomes a whole-system calculation, and the chip that wanted the degree almost never wins it.

## III.3 Worked break-even #2 -- halo2 permutation chunking

PLONKish (halo2)

Circuit with $k=18$, $T=100$ polynomials on the extended domain, $P=50$ permutation-enabled columns.
Extended factor $X(D) = 2^{\lceil\log_2(D-1)\rceil}$, permutation columns $Z(D) = \lceil 50/(D-2)\rceil$ (II.3),
extended cells $= (T + Z(D))\cdot X(D)\cdot n$:

| $D$ | $X$ | $Z$ | extended cells | vs $D{=}5$ |
|---|---|---|---|---|
| 3 | 2 | 50 | $300n$ | -- (usually infeasible for gates) |
| **4** | 4 | 25 | $500n$ | **worse** |
| 5 | 4 | 17 | $468n$ | baseline |
| 6 | 8 | 13 | $904n$ | worse |
| 7 | 8 | 10 | $880n$ | worse |
| 8 | 8 | 9 | $872n$ | worse |
| 9 | 8 | 8 | $864n$ | worse on FFT, **9 fewer MSMs** |

**Two conclusions.**
1. **$D=4$ is never rational** -- same extended domain as 5, 8 more permutation columns, strictly less gate headroom.
   Identically $\{6,7,8\}$ are never rational versus 9, and $\{10..16\}$ never versus 17. This is II.2 restated with numbers.
2. **$5 \to 9$ is a genuine trade.** Cost $396n$ extra extended cells; benefit 9 fewer committed polynomials, i.e. 9 MSMs
   of size $2^{18}$ ($\approx 180n$ field-mul-equivalents at ~0.2n group ops each and ~100 muls per group op) --
   close, and it **flips with $P$**: at $P=200$, $Z(5)=67$ and $Z(9)=29$, so the saving is 38 MSMs $\approx 760n$ against
   $364n$ extra FFT, and $D=9$ wins clearly.

## III.4 Duplicating a constraint instead of selecting inside it

Universal

```rust
// We explicitly separate the constraints for ADD and SUB in order to keep degree
// cubic. Because we constrain that the carry (which is arbitrary) is bool, if
// carry has degree larger than 1 the max-degree constrain could be at least 4.
carry_add[i] = ...; builder.when(opcode_add_flag).assert_bool(carry_add[i]);
carry_sub[i] = ...; builder.when(opcode_sub_flag).assert_bool(carry_sub[i]);
```
(`openvm/extensions/rv32im/circuit/src/base_alu/core.rs:103-124`)

The arithmetic: `when(f).assert_bool(c)` is $f\cdot c(c-1)$, degree $1 + 2\deg(c)$. With $\deg c = 1$ that is 3, exactly
the cap. If $c$ were the flag-selected expression $f_{\text{add}}e_{\text{add}} + f_{\text{sub}}e_{\text{sub}}$ (degree 2),
the constraint would be $1 + 2\cdot2 = \mathbf{5}$.

Price: $2\times$ the constraints, **no extra columns** -- the copies read the same witness.
**Constraint count and constraint degree are different currencies** (count enters soundness logarithmically, degree enters
cost multiplicatively), and this trade sells the cheap one.

> **Where it stops.** With $k$ opcodes you write $k$ copies and the prover evaluates all $k$ on every quotient-domain row.
> Past a handful, committing a selected intermediate column wins. The companion move -- keeping a selector *affine* so it
> can be multiplied into anything -- is stated in-source: *"we need to keep the degree of `is_valid` and `is_load` to 1"*
> (`loadstore/core.rs:55`).

---

# Part IV -- The gating tax

## IV.1 `when(c)` is a multiplication, and the three built-in selectors differ

AIR

```rust
fn assert_zero<I: Into<Self::Expr>>(&mut self, x: I) { self.inner.assert_zero(self.condition() * x.into()); }
```
(`plonky3/air/src/filtered.rs:55-57`), and

```rust
Self::IsFirstRow | Self::IsLastRow => 1,
Self::IsTransition | Self::Constant(_) => 0,
```
(`air/src/symbolic/expression.rs:44-50`), because *"Boundary selectors are non-zero at a single row, so they are
degree-$(N-1)$ polynomials, while the transition selector only needs to vanish on the last row and so is linear."*

**`when_transition()` is free** -- absorbed by the $+1$ in $d(n-1)+1$. `when_first_row()` / `when_last_row()` cost a full
degree, and so does any witness-column selector.

> **Where it stops.** A body already at $D$ cannot be gated by anything except `when_transition`. That single fact forces
> every workaround in IV.2--IV.4.

## IV.2 The tax as a formula: it caps window sizes

PLONKish (halo2)

> *"Given that the `range_check` constraint will be toggled by a selector, in practice we will have a
> `selector * range_check(word, range)` expression of degree `range + 1`. This means that $2^K$ has to be at most
> `degree_bound - 1` in order for the range check constraint to stay within the degree bound."*
> (`halo2_gadgets/src/utilities/decompose_running_sum.rs:18-23`, enforced as `assert!(WINDOW_NUM_BITS <= 3)`)

So $2^K + 1 \le D$. The tax bites hardest exactly at $D \in \{4,8,16\}$ -- the degrees just *below* a bracket top --
which is another reason never to sit at $2^j$ (except under I.6's ZK caveat).

> **Where it stops -- and this is the whole argument for lookups.** A lookup costs
> $\max(4,\ 2 + \deg(\text{input}) + \deg(\text{table}))$ degree (`halo2_proofs/src/plonk/lookup.rs:52-71`),
> **independent of the bit width**: a 10-bit lookup costs the same degree as a 1-bit one.
> Break-even: product range checks win below $\lceil\log_2(D-1)\rceil$ bits per row, lookups above.
> Orchard's `LookupRangeCheckConfig` does 10 bits per row where the product form does 3 -- a **3.3$\times$ row saving**
> for three extra columns amortized over the circuit.

## IV.3 Giving up gating entirely

AIR

When the body is at the cap, the only escape is to make the constraint true on **every** row, padding included, and pay
in trace generation instead:

```
// fill in the first dummy row. we need to do this first, so we can compute the carries that make the
// constraint_word_addition constraints hold on dummy rows
```
(`openvm/extensions/sha2/circuit/src/sha2_chips/block_hasher_chip/trace.rs:133-136`; the padding-row filler at
`crates/circuits/sha2-air/src/trace.rs:424-482` even works in the native field *because the padding values overflow the
intended ranges*, and the encoder carries an extra slot "for dummy (padding) rows").
This is how OpenVM's SHA-2 family went **degree 4 -> 3** (`openvm#2550`).

The documented counter-example is worth as much:

> *"N.B.: in fact range checks could always be done, if the aux subrow values are set to 0 when `count == 0`. This would
> slightly simplify the range check interactions, although usually doesn't change the overall constraint degree. It
> however leads to the annoyance that you must update the RangeChecker's multiplicities even on dummy padding rows."*
> (`openvm/crates/circuits/primitives/src/assert_less_than/mod.rs:31-37`)

> **Where it stops.** Ungating moves cost from the **degree** budget to the **multiplicity** budget: an ungated
> interaction fires on padding rows, so the table's multiplicity column must absorb $n - \text{rows\_used}$ phantom
> lookups. Fine for a counter, fatal for a bus whose terminal must balance.

## IV.4 Pad by repeating a real row, and gate only the lookups

AIR

The cleanest resolution of IV.3's dilemma, from stwo-cairo: rather than zero-filling (which violates the arithmetic
constraints and forces *every* constraint to be gated), duplicate the first real input and zero only the enabler:

```rust
self.inputs.resize(size, *self.inputs.first().unwrap());   // repeat a real row
```
(`stwo-cairo/crates/prover/src/witness/components/ret_opcode.rs:28-32`)
The enabler then multiplies **only the LogUp multiplicities**; arithmetic constraints stay ungated.

Price: 1 boolean column + 1 booleanity constraint per component. Padding rows contribute zero to every LogUp sum because
both the use and the yield carry weight 0.

ZisK removes even that column, in the case where padding rows claim a *true* fact: its secondary machines let padding rows
send `ADD(0,0) = (0,0)` and cancel them with **one degree-0 bus term per AIR instance**, weighted by an instance-level
value equal to the padding count (`state-machines/binary/pil/binary.pil:158-161`).

> **Where it stops.** A padded row must genuinely satisfy every ungated constraint -- which is why *copying a real row is
> mandatory* and why a component with **zero** real rows cannot exist (`assert_ne!(n_active_rows, 0)`).
> ZisK's variant needs the padding row's claim to be true *and* the cancelling term to be exactly countable.

---

# Part V -- Where the trade inverts

## V.1 Sumcheck / multilinear: degree costs $d$ scalars per round, not $2^{\lceil\log_2(d-1)\rceil}$ columns

Sumcheck backends

There is no quotient polynomial and no LDE. The composed constraint's degree sets the degree of the univariate polynomial
the prover sends in each of the $\mu = \log n$ rounds:
`partially_verify_sumcheck_proof(..., MAX_CONSTRAINT_DEGREE + 1)` (`sp1/crates/hypercube/src/verifier/shard.rs:411-416`),
`transcript.message().read_scalar_slice(max_degree)` (`binius/.../verify_sumcheck.rs:73-77`).

Cost: $O(d\mu)$ proof elements and $O(d)$ prover work per round, against $O(2^{\lceil\log_2 d\rceil} n)$ **committed**
field elements in a quotient prover. HyperPlonk states it directly:

> *"The resulting ZeroCheck requires the prover to do only about $s + d\mu$ group exponentiations, which is much smaller
> than $ds$ in Plonk."* ... *"the additional arithmetic work that the prover needs to do depends on the number of
> multiplication gates in the circuit implementing the custom gate $G$, not on the total degree of $G$."*
> (eprint 2022/1355)

**Rule: budget by multiplication count, not degree.** $x^7$ as $((x^2)^2)\cdot x^2\cdot x$ costs 4 multiplications whether
or not you split it, and splitting it into committed columns is now a **pure loss** -- commitment is the expensive part
and you just added a column.

Binius draws the free/paid line at degree 1 rather than at a cap:
> *"The cost of the column's evaluations are proportional to the polynomial degree of the expression. When the expression
> is linear, the column's cost is minimal. When the expression is non-linear, the column is committed."*
> (`binius/crates/m3/src/builder/table.rs:193-212`)

i.e. degree 1 is free, degree $\ge 2$ costs one commitment, and **degrees 2 through 100 cost the same commitment.**
The budget question becomes "how many non-linear columns", not "how deep".

> **Where it stops -- twice.**
> (i) **Batching still takes a max**: `max_degree = max_degree.max(claim.max_individual_degree())` -- one high-degree
> claim still sets the round-polynomial size for everything batched with it. The "whole system pays for the maximum"
> pathology *survives* the change of backend; only the price of the maximum changes from multiplicative to additive.
> (ii) **Univariate skip re-inverts it**: with $\ell$ skipped rounds the degree cost is *multiplied* by $2^\ell - 1$
> (`openvm/crates/recursion/src/batch_constraint/mod.rs:366`). Skipping and high degree do not compose.

## V.2 Folding schemes: degree is worse than linear

Folding / accumulation

Folding a degree-$d$ relation by a random linear combination produces cross terms at every intermediate power.
Sangria: *"Cross terms will now have powers of $r$ from 1 to $d-1$ ... the prover will perform $O(d(n+s))$ field
operations and $O(d(n+s))$ point additions."*
ProtoGalaxy prices it in the recursive verifier, which is what matters: marginal work
$d + \log n$ field ops and $d + \log n$ **compressed hashes** per fold.

Nominally $O(d)$; in practice worse than linear in wall-clock, for two reasons.
(i) The $d-1$ cross-term commitments are **MSMs over the full witness** -- $O(dn)$ *group* operations, and a group
operation is ~100$\times$ a field multiplication. Moving Nova ($d=2$, one cross term) to a degree-5 gate **quadruples the
MSM bill**.
(ii) Each unit of degree adds a hash *inside* the recursion circuit, and hashes dominate a folding IVC step.

> **Where it stops.** ProtoGalaxy's contribution is that the Lagrange basis keeps the $d$-dependence linear rather than
> exponential when folding $k$ instances -- but this is still the only regime with **no free bracket at all**. There is no
> $\lceil\log_2\rceil$ to hide behind.

## V.3 The three regimes, side by side

| backend | cost of degree $D$ | the rule |
|---|---|---|
| FRI / quotient STARK | $\propto 2^{\lceil\log_2(D-1)\rceil}$ field work, plus a blowup cliff at $D = 2^b+1$ | **round up to $2^j+1$; degree is free inside a bracket** |
| Sumcheck / multilinear | $\propto d\log n$ proof + $d$ prover work per round; commitment count is what costs | **budget by multiplication count, not degree** |
| Folding / accumulation | $\propto (d-1)$ MSMs + $d$ in-circuit hashes | **keep $d$ minimal; every increment is genuinely paid for** |

---

# The decision procedure

1. **Compute your AIR's actual max degree symbolically before committing to anything.**
   `get_max_constraint_degree` (`plonky3/air/src/symbolic/builder.rs:104`), `cs.degree()`
   (`halo2_proofs/src/plonk/circuit.rs:1398`), stwo's `ExprEvaluator` + `degree_bound`.
2. **Round the declared budget up to the nearest $2^j+1$** -- 3, 5, 9, 17, 33. Free (II.1).
   If ZK may be enabled later, target $2^j$ instead (I.6).
3. **Check $D \le 2^b + 1$.** If not you are paying two extra DFTs per proof, and in a VM a 4--8$\times$ LDE on
   *every chip* (I.2, III.2).
4. **Check $\log n \le \text{TWO\_ADICITY} - \lceil\log_2(D-1)\rceil$** (I.3).
5. **Spend the slack**, in this order: fold selectors into bodies; widen accumulator/bus chunks to $D-2$ / $D-1$;
   inline intermediate columns away; pick a richer degree-$D$ identity for the same price (II.6).
6. **Split a constraint only when it is the global maximum**, and re-run step 1 to verify the split actually moved the max
   (III.1).
7. **If you are on a sumcheck or folding backend, throw out steps 2--6** and use Part V.

> **The one-line version.** The system pays for the maximum, the maximum is quantized, and almost every circuit is sitting
> strictly inside a bracket with degrees it has already bought and is not using.
