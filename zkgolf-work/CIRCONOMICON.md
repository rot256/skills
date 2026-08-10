# The Circonomicon

*A field manual for rank-1 constraint systems.*

Non-obvious techniques for making arithmetic circuits smaller, collected from a
competitive optimization loop against live opponents. Every entry carries the
mechanism, the measured price, and the condition under which it stops working.

$$(A\cdot w)(B\cdot w) = (C\cdot w) \qquad\text{score} = \text{allocations} + \text{constraints}$$

## The axioms

**One product per row.** Enforced *syntactically*, not semantically. A row has
exactly one multiplication and the checker walks the expression tree.

**Affine is free.** Additions, subtractions, and multiplication by any
compile-time constant cost nothing. Not "cheap" — zero.

**You pay twice.** `witness` is $\langle 1,0\rangle$, `assertZero` is
$\langle 0,1\rangle$. Score counts both, so a value pinned by its own row
costs $2$.

**Shape, not rank.** The product counter looks through *constant* factors only,
so $ab + ac$ is rejected — rank 1, two syntactic products. Design to the literal
shape.

**No escape hatches.** Lookups and interactions are counted at zero — and then
make the R1CS obligation *unprovable*. There is no loophole, only a trap.

### Scope

**Parts I–VI are the large prime field** ($\mathbb{F}_r$, $r \approx 2^{254}$).
Every price, identity, and floor in them assumes it. **Part VII is the GF(2)
model**, which is a different cost model with a different row form — most of what
follows is void there, and it is kept separate rather than annotated in place
precisely because the two do not mix.

### On evidence grades

*Measured* means the constant was read out of a tree that built and verified.
*Proved* means an argument, checked. *Estimated* means a model, and is marked as
such. The distinction between these three is the most valuable thing in this
collection, and collapsing them is how a work queue fills with items worth
nothing.

---

# Part I — What one row can do

A rank-1 row looks like it can express exactly one multiplication. It can express
considerably more, because the multiplier and the target are free to be any
affine forms you like — and because a row that pins a value can also imply
properties of it at no extra cost.

## I.1 The single-row non-vanishing multiplier

**$\langle 1,1\rangle$ per output bit** · Universal · Measured

Encode the output $z$ of a small boolean function in one row of the shape

$$L_1 - (z + L_2)\cdot M = 0$$

where $L_1, L_2, M$ are affine in the boolean inputs and $M$ **never vanishes on
the boolean cube**. The row is linear in $z$, so $z$ is uniquely pinned — and it
inherits booleanity, so the usual $z(z-1)=0$ row disappears.

$$
\begin{aligned}
\textsf{XOR3}\quad & (6a + 6b - 24c) - (z + 2a + 2b + 7c)(a + b - 4c + 1) = 0 && M \in \{\pm1,\pm2,\pm3\}\\
\textsf{CHI}\quad & (4a + 2b) - (z + 3a - b - c)(4a + b + c - 3) = 0 && M \in \{\pm1,\pm2,\pm3\}\\
\textsf{MAJ3}\quad & 12 + (z + a + b - 9c + 3)(a + b + 6c - 4) = 0 && M \in \{\pm2,\pm3,\pm4\}\\
\textsf{CARRY}\quad & \text{same row as MAJ3, since } \mathrm{carry}(a,b,c) = \mathrm{maj}(a,b,c)
\end{aligned}
$$

The multiplier must be affine **in the inputs only**; $z$ must not appear in it.
What makes the construction work is that $M\cdot(f + L_2)$ collapses to an affine
$L_1$ modulo the boolean ideal $x^2 = x$.

To apply it to a new function: pick an affine $M$ nonzero everywhere on the cube,
then solve for $L_1, L_2$ so the row reproduces the truth table. Verifying that
$M$ never vanishes *is* the uniqueness proof.

An exhaustive SMT sweep found that **192 of the 256 three-input boolean
functions** admit this form. The native gate library is not $\{\wedge,\oplus\}$ —
it is three-quarters of all ternary functions, each at one row.

> **Where it stops.** The other 64 functions have no non-vanishing affine
> multiplier. For those, reach for the decoy-root form in I.4, which always
> exists.

## I.2 λ-packed twin instances — half a row per bit

**$\tfrac12 + \tfrac12$ per bit** · Universal, where a gadget runs twice · Measured

One row per output bit looks like the floor. It is not, whenever you need the
same function *twice*. A 32-bit value occupies 32 of the field's 254 bits, so
pack two instances into one witness at a separating base $\lambda = 2^{40}$,
$z_j = f(A)_j + \lambda f(B)_j$, and pin both with a single rank-1 row.

$$(-3e + 2f + 4g + 2\lambda u)(e - 2f + 4g - 2\lambda u) + \bigl(3e + (8\lambda+4)f - 8g + 4\lambda^2 u - 8z\bigr) = 0$$

This reduces to $8(z - z_{\text{honest}}) = 0$ modulo the input booleanity
relations, and $8$ is a unit. Cost $\langle 32,32\rangle$ for 64 output bits,
against $\langle 64,64\rangle$ for two separate gadgets — exactly halved.

**The design constraint is the whole technique:** the two instances must *share
most of their inputs*, so the row stays affine in a small input set. A hash with
a shift-register state supplies this for free by pairing adjacent rounds —
$\mathrm{Ch}(e',e,f)$ reuses $e$ and $f$, so the packed pair is a function of only
four booleans. The packed word is then consumed additively downstream, which
splits the two $\lambda$-slots apart at no cost.

Measured saving: 128 score per round pair, 4,096 per 512-bit block.

## I.3 The packing constant is the ratio of the downstream weights

**unpacking costs zero** · Universal · Measured

The part that is easy to miss about λ-packing: **λ is not a free parameter you
tune for separation — it is determined by the consumer.** Choose

$$\lambda = \frac{\text{weight of slot 2}}{\text{weight of slot 1}}$$

*in the sum that consumes both*, and the packed value unpacks itself for nothing.
Two lanes two bit-positions apart in the same downstream field sum give
$\lambda = 4$; two lanes entering at the same weight give $\lambda = 1$; two
instances consumed by different rounds of a fused adder give $\lambda = 2^{40}$.

Where the two slots are genuinely independent, λ is instead set by a headroom
argument: slots below $2^{35}$ with $\lambda = 2^{40}$ leaves five bits of margin
and needs a prime above $2^{76}$.

A second identity worth having, because it avoids the cross term outright —
**difference of squares** packs a pair of two-input XORs into one row with one
witness, with $\lambda = r^2$:

$$\mathrm{xor}_2(a,b) + \lambda\,\mathrm{xor}_2(c,d) = \bigl[2a - 2b + 2\lambda(c+d) - 1\bigr] - \bigl(r(c+d) - (1-a+b)\bigr)\bigl(r(c+d) + (1-a+b)\bigr)$$

## I.4 The out-of-range decoy root

**1 row, no disambiguation** · Universal · Measured

A row $(z - r_1)(z - r_2) = 0$ is one constraint but does not pin $z$ — it admits
two solutions, which is normally why the single-row form is preferred. The trick
is to make the wrong solution *arithmetically unreachable* rather than excluding
it with a second row.

Choose $r_1, r_2$ so that on every input assignment exactly one root is the
honest value and the other is displaced by a huge power of two $\Omega$. The
consuming addition already lives in a bounded window and rejects the decoy at
zero cost. With $\lambda = 2^{40}$, $\Omega = 2^{80}$:

$$\Bigl(z - \bigl((1+\lambda)a + \Omega(a-b)\bigr)\Bigr)\Bigl(z - \bigl(c + \lambda u + \Omega(1-a-b)\bigr)\Bigr) = 0$$

When $a = b$ the first factor is honest and $\Omega(a-b)$ vanishes; when
$a \neq b$ the second is honest and $\Omega(1-a-b)$ vanishes. Either way the
decoy is $2^{80}$ away, and a 35-bit packed addition cannot absorb it.

The two-root form *always* exists — interpolate through the two branch values —
and is always one row. Its cost is not in rows but in proof: the soundness
obligation moves into the adder, where you must show the operands are bounded.

## I.5 Gated booleanity

**saves 1 row per gated bit** · Universal · Measured

When a witness bit must be boolean *if* a region is active and zero otherwise,
don't emit $b(b-1)=0$ plus a masking row. Emit one row:

$$b\,(b - \mathrm{active}) = 0, \qquad \mathrm{active}\ \text{an affine boolean}$$

At $\mathrm{active}=1$ this is exactly booleanity; at $\mathrm{active}=0$ it
forces $b=0$. In a 255-byte variable-length padding check this covers all seven
witnessed low bits of every byte at seven rows per byte with no masking rows at
all — it is what makes "every byte past the message length is zero" free.

## I.6 The range check's top bit is derived, not witnessed — $\langle n-1, n\rangle$

**saves 2 at every quotient and carry** · Universal · Measured

To prove $x < 2^n$: witness only $n-1$ bits, assert booleanity on each, then form
the top bit as the *affine* expression

$$\mathrm{top} := (2^{n-1})^{-1}\Bigl(x - \sum_{i<n-1} b_i 2^i\Bigr)$$

and assert booleanity on that. **The linking row $x = \sum b_i 2^i$ never
exists** — it holds as a ring identity. Soundness: $\mathrm{top}\in\{0,1\}$ and
$\mathrm{low} < 2^{n-1}$ force $x = \mathrm{low}$ or $x = \mathrm{low} + 2^{n-1}$,
both $< 2^n$.

The reflex is $n$ witnesses $+\ n$ booleanity rows $+\ 1$ linking row. The saving
looks like 2 units, but it multiplies: every quotient wire and every grouped
carry in the circuit is a range check. A 256-bit normalisation is
$\langle 252,256\rangle$ rather than $\langle 256,260\rangle$.

The same "define the last one affinely" move recurs whenever a small set of
witnessed bits has a known sum: witness two of three borrow bits and *define* the
third as $b_0 := s - 2b_1 - 4b_2$; the booleanity rows then pin all three, and
both the linking row and one allocation vanish.

## I.7 One-directional zero-implication in $\langle 1,1\rangle$ — the weak inverse witness

**$\langle 1,1\rangle$ vs $\langle 2,3\rangle$** · Universal · Measured

To assert $d = 0 \Rightarrow t = 0$, witness one field element $u$ and assert a
single row:

$$t - d\,u = 0$$

If $d = 0$ the row forces $t = 0$; if $d \neq 0$ the prover sets $u = t/d$ and the
row is vacuous.

The reflex is to materialise $z = \mathrm{IsZero}(d)$ — an inverse witness plus a
flag, $\langle 2,2\rangle$ — and then assert $tz = 0$, total $\langle 2,3\rangle$.
But **most canonicality and comparison logic only ever needs the implication,
never the biconditional.** One canonicality gadget went from "three zero-test
gadgets and two product witnesses, 8 allocations and 12 rows" to "four bare
witnesses and four rows".

Probably the most portable single item here: audit every zero-test in a design
and ask whether the converse direction is ever used.

## I.8 A $k$-way disjunction is a product chain, not a selector tree

**~2× on any mux-shaped constraint** · Universal · Measured

To assert "at least one of $l_0,\dots,l_{k-1}$ is zero", do not witness $k$
selector bits, gate a row on each, and add a sum-to-one row. Just assert the
product:

$$l_0 l_1 l_2 l_3 l_4 = 0 \qquad\text{as 3 intermediate product cells + 1 terminal row}$$

$$\text{product chain: } k-2 \text{ cells} + k-1 \text{ rows} \qquad\text{selector tree: } k \text{ bits} + k \text{ gated rows} + 1$$

Roughly half the cost, and it removes the booleanity obligations entirely. It
appears inside a 4096-bit comparison that comes to $\langle 73,155\rangle = 228$
total — a five-way "one of these radix-packed prefix differences equals $\delta$"
resolved by one product chain, replacing four selector cells and five
selector-gated rows.

The disjunction shape is far more common than it looks: any "one of these cases
holds" is one, and so is every multiplexer whose branches you were about to prove
mutually exclusive.

## I.9 A rank-$r$ quadratic costs $\lceil r/2\rceil$ rows, not $r$

**exact 2×** · Universal · Proved, matching

The naive idiom accumulates $x_i\,l_i(x)$ at $r$ rows and $r-1$ witnesses.
Instead **diagonalise the form at compile time**. Over $\mathbb{F}_p$,
Chevalley–Warning forces every form in $\geq 3$ variables to be isotropic, so $q$
splits into hyperbolic planes perpendicular to an anisotropic kernel of dimension
$\leq 2$ — and each hyperbolic plane is a product of two linear forms, hence one
row.

The move that makes it tight: **let the last row's $C$-slot absorb the running
sum**, which is affine and therefore free:

$$l_{2t-1}\,l_{2t} = z - u_1 - \cdots - u_{t-1}$$

Cost $\lceil r/2\rceil$ rows $+\ \lceil r/2\rceil - 1$ witnesses. Optimality is
matching: rank is subadditive and each row contributes rank $\leq 2$. A sum of
eight squares is 7, against 15 naive.

Over the BN254 scalar prime, one row each: $x^2+y^2$, $x^2-y^2$, $x^2+2y^2$,
$x^2+3y^2$, $x^2+6y^2$, $x^2+13y^2$. Not one row: $x^2+5y^2$, $x^2+7y^2$,
$x^2+11y^2$, $x^2+17y^2$. The criterion is $\left(\frac{ab}{r}\right) = 1$, using
$\left(\frac{-1}{r}\right) = 1$.

> **Where it stops.** Hunting for *free* low-rank combinations in an arbitrary
> constraint span does not pay: the rank-$\leq 2$ locus in symmetric
> $N\times N$ matrices has codimension $(N-1)(N-2)/2$, so generically there is
> nothing there, and finding one is MinRank.

## I.10 Split algebras: rank collapses from $2n-1$ to $n$

**$n$ rows instead of $2n-1$** · Non-native arithmetic · Proved (Winograd)

Multiplication in $F[u]/P$ with $\deg P = n$ and $k$ distinct irreducible factors
needs $2n-k$ multiplications (Winograd 1977; Alder–Strassen 1981). Because the
CRT change of basis is *linear*, hence free in R1CS, a fully split modulus gives
$n$ rows.

$$
\begin{aligned}
\text{row 1:}\quad & (a + ib)(c + id) = p_1\\
\text{row 2:}\quad & (a - ib)(c - id) = p_2\\
\text{then}\quad & e = \tfrac{p_1+p_2}{2},\quad f = \tfrac{p_1-p_2}{2i}\quad\text{both FREE}
\end{aligned}
$$

Score 4, against Karatsuba's 6. This is literally Winograd's result that complex
multiplication needs 3 real multiplications but only 2 over $\mathbb{C}$.

BN254's scalar prime has $r \equiv 1 \bmod 2^{28}$, so $-1$ is a square and
$n \mid r-1$ for every $n = 2^k$, $k \leq 28$, plus many odd $n$. Cyclic
convolution of length $n$ likewise costs $n$ rows whenever $n \mid r-1$, with both
DFTs free.

> **Where it stops.** Only for genuinely *wrapped* ring arithmetic. A full
> product still needs $2n-1$ — the collapse is paid for by the wrap, not by the
> field.

## I.11 The $\sqrt{N}$ law — any function on $N$ points costs $\sim 2\sqrt{N}$ rows

**$N=256$: 75 vs 509** · Universal · Measured schedule

Baby-step/giant-step (Paterson–Stockmeyer 1973). To evaluate a degree-$N$
univariate $P$: compute $x^2,\dots,x^k$ in $k-1$ rows, then write

$$P = \sum_j B_j(x)\,(x^k)^j, \qquad \deg B_j < k$$

**Each $B_j$ is a free affine combination of powers you already have**, so the
Horner recursion in $y = x^k$ costs one row per giant step. Optimum at
$k \approx \sqrt{N}$.

| $N$ | this | naive |
|---:|---:|---:|
| 16 | 19 | 29 |
| 256 | 75 | 509 |
| 1024 | 143 | 2045 |
| 4096 | 271 | 8189 |

This applies wherever a table, an S-box, a piecewise function, or "membership in
an arbitrary set of $N$ elements" appears. A matching lower bound survives
nondeterminism — parameter counting gives $s \gtrsim 0.58\sqrt{N}$ — so
$2\sqrt{N}$ is within $\sim 3.5\times$ of optimal and **you should stop there**.

---

# Part II — Don't materialise the value

The deepest savings are not cheaper gadgets. They are values that never get
written down. Every entry here is a way of noticing that something you are paying
to construct is not actually needed in the form you are constructing it.

## II.1 Assertion, not value — and the scope rule that decides whether it transfers

**−531 per site** · Non-native arithmetic · Measured

A value that is only ever the **target** of a certificate can be deleted
outright: nothing reads it, it merely has to satisfy an equation, so run the
certificate directly against the target expression and the witness disappears.

It **cannot** delete an operand. An operand of a non-native product must have
limb-certified digits or its field convolution coefficients carry no integer
meaning — confirmed by 200/200 successful forgeries at toy scale when the
certification was removed.

So the audit question is not *"does anything read this value?"* but *"does
anything read it as an operand of a product?"*

| class | verdict | instance |
|---|---|---|
| **target** | deletable | curve-equation residue, terminal slope residue — −531 each |
| **operand** | irreducible | chain residues $r_i$, each read by the next squaring |
| **certificate-by-range** | *looks* deletable, is not | quotients $q_i$ are read by nobody, but removing their range checks is a forgery: the dimension count (171 free unknowns against 37 group equations) is what pins the reduction |

## II.2 The consumer-functional law

**4 cells → 2** · Non-native arithmetic · Proved from source

The sharp, quantitative form of II.1. A multi-cell value costs in proportion to
its number of cells in every gadget that builds it by selection — but each
consumer reads only a set of *linear functionals* of the cell vector. **The number
of cells you must produce is $\dim \mathrm{span}\{\text{all consumers'
functionals}\}$, not the arity of the type.**

Proved from source for the dominant consumer in both elliptic-curve trees: with a
one-carry group schedule, a target vector enters through exactly two independent
functionals, $T_{\text{lo}} = t_0 + 2^{64}t_1$ and
$T_{\text{hi}} = t_2 + 2^{64}t_3$. Positions 2 and 3 appear in no row but the
single final polynomial-evaluation row.

| consumer | rank |
|---|---:|
| convolution multiplicand | 4 (full; never reducible) |
| certificate addend, one-carry group schedule | 2 |
| value only tested for zero or equality | 1 |
| circuit output | whatever the interface declares |

The audit rule: for every value produced by a selector, list its consumers, write
down each consumer's functionals, and produce only a *basis* of their span.

## II.3 State the spec as a congruence, not a canonical value

**~980 → 0** · Universal · Measured

A 256-bit scalar supplied as bits does not need a witnessed canonical remainder
mod the group order. Packing the bits into limbs is a pure affine recombination,
and the value it denotes is *already in the right congruence class*.

The record's scalar reduction is literally `pure (packBits input.bits)` with a
proved cost of zero, and its spec is stated as
$\text{value} \bmod n = \text{scalar} \bmod n$ rather than as an equality.
Avoided: a witnessed remainder plus quotient, with normalisation on both, plus a
comparison — about 980 allocations and 989 constraints.

**The precondition is the whole trick.** Audit every normalisation and every
comparison against the question "does any consumer need more than the congruence
class?" Each one that turns out not to is worth hundreds of rows.

## II.4 Field subtraction should cost exactly zero

**285/294 → 0/0** · Non-native arithmetic · Measured

Do not reduce $a - b$ before feeding it to the next multiplication. Represent it
limbwise as $a_k + \mathrm{borrow}_k - b_k$, where $\mathrm{borrow}$ is a
*compile-time constant* limb vector encoding $2p$, chosen so every limb stays
non-negative and the total stays below $3p$. That expression is affine, hence
free.

$$\mathrm{borrow}_0 = 2^{65} - 2^{33} - 1954, \qquad \mathrm{borrow}_{k>0} = 2^{65} - 2$$

Then instantiate the modmul certificate with input bounds
$C_a, C_b \leq 4\cdot 2^{64}$. **The folded certificate's cost is invariant in
those bounds** — still $\langle 184,186\rangle$. Only the carry-width proof
obligation moves.

Every difference in the affine chord/tangent/double formulas becomes free. The
record contains *zero* explicit subtraction gadgets in its fused double-add. It
composes with sum-of-products: the same slack lets a fused
$r = ab - s_1 - s_2$ put both subtrahends straight into the certificate target
unreduced, so a multiply-subtract-two costs the same as a plain multiply.

## II.5 Keep it a polynomial — mux at the cell level, not the field level

**−1,050 per slope** · Non-native arithmetic · Measured

A Weierstrass slope must divide by either $x_2 - x_1$ (chord) or $2y$ (tangent),
with numerator either $y_2 - y_1$ or $3x^2$. The naive route reduces $x^2$, scales
by 3, muxes against $dy$, then runs a division certificate — *two* reductions.

Instead: compute the square as a raw 7-cell convolution and **never reduce it**.
Mux the 7-cell vector against the zero-padded alternative — one row per cell — and
hand the resulting *polynomial* directly to a single certificate. The square never
becomes a field element.

$$
\begin{aligned}
\text{fused select-and-divide} &= 476/481\\
&= \text{zero-test } 2/2 + 3\times\text{4-limb mux} + \text{interpolatedMul } 7/7\\
&\quad + \text{7-cell mux } 7/7 + \text{4 result witnesses} + \text{validator } 260/267 + \text{certificate } 184/186\\
\text{reduce-then-divide} &= 999/1008
\end{aligned}
$$

**General rule:** selection, scaling by small constants, and addition all work at
the polynomial level for one row per cell. Only the final certificate pays for a
reduction.

## II.6 Defer every intermediate reduction into one integer identity

**−2,998 on one gadget** · Non-native arithmetic · Measured

Wherever a gadget performs several independent modular reductions only to combine
the results into one final congruence, **every reduction but the last is waste**.
Defer them into a single natural-number identity with one witnessed quotient and
one carry chain.

Measured: a scalar relation that used to perform four separate reductions to
build one congruence went from $\langle 2365,2387\rangle$ to
$\langle 874,880\rangle$ — $-1{,}491$ allocations and $-1{,}507$ rows. The
supporting work is three small files: a magnitude-parameter instance, the
per-position cells, and a scaling vector. That is the usual shape — a deferred
identity needs its own bound instance and nothing else.

The same law priced on a multiply chain: one reduction shared across $M$ products
costs 424 rows at $M=1$, 457 at $M=2$, 490 at $M=4$. Each extra product adds about
33.

**The grep signature:** two or more mod-reduction subcircuits whose outputs feed a
common assertion.

## II.7 Score is $2\times$ bits of *advice*, not $2\times$ bits

Universal reframing · Derived

The 2-per-bit charge applies only to values pinned to a finite set *by rows*. It
does not apply to values whose bounds are **implied**. Convolution cells of
already-bounded operands cost zero — which is why a $2k-1$-point multiply
witnesses 15 cells with no range check at all. So the invariant is:

$$\text{score} \approx 2\times\bigl(\text{bits of nondeterministic advice not polynomial in prior advice}\bigr)$$

This reframing is not cosmetic; it relocates most of the supposed floor. In one
scalar-multiplication step the genuine advice is only the two division outputs.
Three further 256-bit values are *polynomial* in that advice and are therefore
materialised by choice, not necessity — 94,302 score of a 160,146 "floor" turned
out to be a representation decision.

It also answers a question worth posing directly: is a value known to be a sum of
products of bounded things cheaper to range-check? It is not merely cheaper. It is
*free*.

## II.8 Fuse a double-and-add so the intermediate never exists

**~826 per step** · Short-Weierstrass curves · Measured

Compute $2R + T$ as $(R+T)+R$ through a shared slope chain, so that the
$y$-coordinate of the intermediate $S = R+T$ is *never a wire*
(Eisenträger–Lauter–Montgomery, read as a circuit optimization rather than a
speedup):

$$
\begin{aligned}
\lambda_1 &= \mathrm{slope}(R,T) & x_S &= \lambda_1^2 - R_x - T_x\\
w &= \frac{2R_y}{x_S - R_x} & A &= \lambda_1 + w\\
x_4 &= A^2 - x_S - R_x & y_4 &= A(x_4 - R_x) - R_y
\end{aligned}
$$

$y_S$ never appears. Fused $\langle 2056,2069\rangle$ against unfused
$\langle 1627,1638\rangle + \langle 1255,1263\rangle = \langle 2882,2901\rangle$.

A companion move makes the tangent-path sign free: write $2p$ in a digit set where
every digit exceeds the limb bound, so $\mathrm{digit}_k - v_k$ is a *borrow-free
affine* encoding of $-v$. Since $A^2$ is sign-insensitive, the $y$-coordinate then
needs no multiplier-operand mux at all.

## II.9 Allocate $n-1$ of $n$ tied values and derive the last affinely

**recurs everywhere** · Universal · Measured

Whenever $n$ values are tied by one affine relation, allocate $n-1$ and *define*
the last. The derived value still needs its own booleanity or range row, but the
allocation and the linking row both vanish. This is the same move as I.6, and once
you see it, it is everywhere.

$$c_{n+1} := 2^{-1}\bigl(a_n + b_n + c_n - z_n\bigr) \qquad\text{affine in the SUM bits}$$

Only the 32 sum bits are allocated, and each per-bit row does double duty —
pinning $z_i$ boolean *and* the carry boolean. $\langle 32,32\rangle$ against
$\langle 32,33\rangle$.

The same shape appears in a fused adder's low carry (a pure affine expression of
everything else, pinned by one booleanity row), in a byte range check that
witnesses seven bits and derives the eighth, and in a borrow column that witnesses
two of three bits.

**The general law, and it is the most transferable idea in the collection:** a
value determined by a linear equation from already-materialised values must be
written as that linear expression, never as a fresh witness plus a defining row.
Grouped-equality carries follow it exactly — the carry out of group $k$ is

$$c_{k+1} = \frac{G_k(\mathrm{lhs}) + (c_k - \mathrm{OFF}_k) - G_k(\mathrm{rhs})}{2^{B\cdot gf(k)}} + \mathrm{OFF}_{k+1}$$

which is affine, so the only emitted operation is a range check on it. Zero carry
allocations, and the group-identity rows disappear entirely.

## II.10 Words consumed only as a field sum are never reduced at all

**−33 alloc per word** · Universal · Measured

II.7 says the charge is on advice. Here is what that looks like in practice: **a
word whose only consumer is an addition never needs its $\bmod\ 2^n$ reduction
performed.** Not a cheaper reduction — none.

The last two message-schedule words cost $\langle 58,58\rangle$, allocating no
output bits and no carry, against $\langle 91,92\rangle$ for a full step. They are
consumed only inside a fused tail adder's field sum, so the reduction that would
produce their bits is simply never emitted: $-33$ alloc, $-34$ rows each.

The chaining word between blocks gets the same treatment — carried as a raw field
value with a bound loose enough to keep the next round's six-operand window in
range, saving its 32 allocations and 32 booleanity rows. A "deferred add" gadget in
that style costs *literally zero*: it is `pure (a + b)`, certified at
`Count.zero`. It is free wiring wearing the shape of a gadget.

The same logic reshapes selection. Choosing among five candidate digests by
witnessing **8 field words** and asserting
$\mathrm{flagSum}\cdot(\mathrm{cand} - \mathrm{digest}) = 0$ is
$\langle 8,40\rangle$. The bit-level version would be 256 witnesses and 1,280 rows.

## II.11 Never assert your last equation — solve it for one unknown

**−2 per reduction, composes** · Universal · Measured

A gadget that ends "…and therefore the accumulated identity holds" is asserting a
row it could instead *make true by construction*. Solve the final equation for one
coefficient and substitute the affine solution:

$$\mathrm{top} := \frac{\mathrm{polyEval}(\mathrm{lhs}, 2^B) - \mathrm{polyEval}(\mathrm{lowVec\ rhs}, 2^B)}{2^{B(L-1)}}$$

Affine, so free. The coefficient vector now witnesses $2m-2$ cells instead of
$2m-1$, and the closing row disappears; the remaining interpolation rows still pin
it soundly.

Worth $-2$ per reduction on its own, which is why one ledger closes at 9,870 rather
than 9,871. Its real value is that it composes: once the top coefficient is an
expression rather than a witness, it can be spliced into a multiply that accepts a
supplied coefficient vector, and the two savings stack.

## II.12 Cost a gadget against the rank of what its consumer reads

**372 vs 682 — 46% off** · Non-native arithmetic · Verified numerically

The sharpest instance of II.2 in the collection. A squaring produces 341
convolution coefficients — but the grouped carry check downstream reads only **38
group sums** of them. So the projection the consumer needs has rank 38, and the
gadget should be priced against 38, not 341.

Writing the square in terms of that projection gives an identity whose high part is
a quadratic form, and here the factor of two from I.9 appears in the wild:

$$S(c) = \beta(c)^2 + (c - t^9)\,\mathrm{Hi}(c)$$

$$t^9\,\mathrm{Hi}(c) = \sum_{i+j\geq 9} h_i h_j = 2h_8(A_1 - A_4) + 2h_7(A_2 - A_4) + 2h_6(A_3 - A_4) + A_5(2A_4 - A_5)$$

The $9\times 9$ anti-triangular 0/1 matrix $[\,i+j\geq 9\,]$ has rank exactly 8, and
it is **symmetric with split signature $(4,4)$** — so it decomposes into 4
hyperbolic pairs, i.e. 4 products where a general rank-8 bilinear form would need 8.
*That* factor of two is precisely what "a square is cheaper than a product" means
here.

One further saving falls out free: $\mathrm{Hi}$ has degree $2K-2$ in the
evaluation variable, so **its value at the last evaluation point is an affine
combination of the others** and costs nothing. Hence $4(2K-1)$ cells and rows, not
$4\cdot 2K$.

Total $\langle 186,186\rangle = 372$, against 682 for the coefficient-wise
multiply. Note the discipline this implies: the same tree uses the plain multiply
in the one place where all coefficients *are* consumed, and the projected form
everywhere else. The choice is made per call site, from the consumer.

## II.13 Verification, not computation — witness the answer and check a relation

**the architecture, not a gadget** · Universal · Measured

The largest structural lever in the collection, and the one most easily missed
because it is not a gadget at all. **The output does not have to be computed. It
has to be checked.** If a cheap relation characterises the right answer, witness
the answer as pure advice and assert the relation.

Worked instance, a variable-base scalar multiplication $Q = kP$. The output point
$Q$ is **9 witnesses of pure advice**. Soundness comes from three facts that are
collectively far cheaper than computing $Q$:

$$u_1 P + u_2 \varphi(P) + v_1 Q + v_2 \varphi(Q) = \mathcal{O}, \qquad u_1 + \lambda u_2 + k(v_1 + \lambda v_2) \equiv 0 \pmod n, \qquad v_1 + \lambda v_2 \neq 0$$

together forcing $Q = kP$. Because all four lattice coefficients are 64-bit plus
sign, the group check is a 4-scalar multi-scalar multiplication over a 16-entry
table of sign-adjusted subset sums, **consuming one bit from each of the four
scalars per iteration** — window width 4 *across* scalars, not per scalar. 64
iterations and 63 doublings, for a 256-bit scalar.

The generalisable shape: find a *verification identity* whose cost is set by the
size of the certificate rather than by the length of the computation, then push
the computation entirely into the prover. Look for it wherever a function has an
efficiently checkable inverse, a group law, or a lattice relation.

## II.14 The degree ladder — put a polynomial in a *factor*, not only in the target

**$-29{,}200$ modelled** · Non-native arithmetic · Verified 200/200 against real points

II.5 keeps a raw convolution as a certificate *target*, which is free. The next
move is to keep one as a **factor**, which costs one extra fold level and is
affordable only once the limb count is small. This is where you decide between
materialising a value and raising a certificate's degree — and the two prices are
directly comparable:

| | $4\times 64$ | $8\times 32$ |
|---|---:|---:|
| $D=2$ certificate | 214 | 214 |
| $D=3$ certificate | **1597 — infeasible**, the folded position exceeds $2^{253}$ | 454 |
| $D=4$ certificate | — | 1004 |
| $D=5$ | fold overflow, dead | fold overflow, dead |
| materialising the value instead | 531 | 531 |

So merging is a **loss of 700** at $4\times 64$ and a **gain of 290** at
$8\times 32$. The limb width decides whether the technique exists at all.

Concretely, two rows of a fused double-and-add collapse into one degree-3
certificate that never materialises $x_R$:

$$(\lambda_1^2 - 2x_P - x_Q)(\lambda_1 + \lambda_2) + 2y_P = 0 \pmod p$$

materialising $\lambda_2$ only; and the next row becomes a degree-2 certificate
with *two convolutions under one quotient*, which also never touches $x_R$. A step
goes from four materialisations to three.

> **The general rule, and it is the one to carry away.** A value consumed *only
> additively* can be carried as a polynomial for free at any depth. A value
> consumed *multiplicatively* must either be materialised (531) or raise the
> certificate degree ($+240$ for $D{=}2\to 3$, $+550$ for $D{=}3\to 4$). **Compare
> those two numbers before witnessing anything.** Note also that $D=4$ constrains
> the limb count to $7 \leq k \leq 9$, or the $2m-1$-point interpolation itself
> overflows the native field.

## II.15 Fuse the terminal step with the output comparison

**~8,021 per instance** · Universal · Measured

Never materialise a value you are about to constrain to a public expression.

For $e = 65537 = 2^{16}+1$, the naive chain is 16 squarings, one multiply, and an
equality test against the padded target. Instead run one first square, 14 middle
squares, and **one ternary reduction asserting $a\cdot a\cdot s \equiv \mathrm{EM}
\pmod n$ directly**, with $\mathrm{EM}$ a public affine vector of the digest
bytes.

Because the residue *is* the given target, that step allocates no residue limbs
and pays **no residue certification at all** — compare a squaring's
$\langle 3925,4096\rangle = 8{,}021$ for exactly that. The fused step costs
$\langle 12955,13018\rangle$ and replaces a squaring plus a multiply plus an
equality.

The pattern generalises past modular exponentiation: any computation ending in
"…and the result equals this public thing" should assert the last relation against
the public thing rather than producing a value and comparing.

---

# Part III — Free things engineers pay for

"Affine is free" is easy to say and hard to internalise. Each of these is a place
where a standard gadget gets reached for and the answer was already sitting in the
circuit as a linear combination.

## III.1 The range check *is* the output encoding

**−1,032 for a two-coordinate point** · Universal · Measured

Any value that must be proved canonical is already bit-decomposed. If the interface
wants it as bytes, build each byte as an affine combination *of the very bits the
range check allocated*. A standalone serialiser for one 256-bit coordinate is 256
allocations and 260 constraints; folded into the validator it is $0/0$.

**Generalises to every multi-consumer bit vector.** Whenever two passes over the
same value both need its bits — range check, comparison, serialisation,
bit-selection, a boolean gate — allocate the bits once and make every other
consumer an affine function of them. Audit for any value that is decomposed twice;
each redundant decomposition is $n$ allocations plus $n+1$ rows.

The strongest form of this is a **free radix change**: repacking already-certified
bits from base $2^{24}$ into base $2^{16}$ is a pure total function on expressions,
$\langle 0,0\rangle$, with no circuit at all. That is what lets a circuit use one
limb width for its main chain and a different one for a final step whose
coefficients would otherwise overflow.

## III.2 Comparing input bits against a constant costs zero allocations

**44 score for all exceptional-case handling** · Universal · Measured

Given boolean bits and a compile-time constant $k$, the *mismatch count*

$$\sum_i \bigl(\text{if } \mathrm{bit}_i(k) \text{ then } 1 - b_i \text{ else } b_i\bigr)$$

is a purely affine expression, lies in $[0,256]$ so it cannot wrap, and is zero
exactly when the bits encode $k$. It costs nothing — no witness, no row. Only the
zero *test* costs anything, and two tests can share one: materialise the product and
run a single zero-check for $\langle 3,3\rangle$.

Measured: the fixed-base record screens four exceptional scalars with two shared
zero-tests and two affine muxes — 44 score, 0.06% of the circuit, for the entire
exceptional-case handling of a scalar multiplication. The generalisable pattern is
*enumerate the finitely many bad inputs, detect them affinely, and route both
operands to a constant safe state* so the incomplete formula never sees a degenerate
case.

**General rule:** any predicate that is an affine function of the input bits and
cannot wrap is free. Push all constant-comparison logic into that form before
reaching for a comparator.

## III.3 Adding a constant makes the low bits affine — charge $32 - v_2(C)$

**31/30/29 vs 32** · Universal · Measured

In $z = b + C \bmod 2^{32}$ with $C$ constant there is no carry into bit 0, so
$z_0 = b_0 \oplus C_0$ — affine. If $C \equiv 2 \pmod 4$ the low *two* bits are
affine; if $C \equiv 4 \pmod 8$, the low three. Witness only the remaining high bits
and start the affine carry chain there.

| constant | cost |
|---|---|
| odd | $\langle 31,31\rangle$ |
| $\equiv 2 \pmod 4$ | $\langle 30,30\rangle$ |
| $\equiv 4 \pmod 8$ | $\langle 29,29\rangle$ |
| general 2-operand | $\langle 32,32\rangle$ |

Applied to a SHA-256 chaining add against the IV: $H_1, H_6, H_7$ odd give 31 each;
$H_2 = \mathtt{0x3c6ef372}$ and $H_3 = \mathtt{0xa54ff53a}$ are $2 \bmod 4$ giving 30
each; $H_5 = \mathtt{0x9b05688c}$ is $4 \bmod 8$ giving 29. 182 instead of 192, free.

Check the 2-adic valuation of *every* constant addend — round constants, length
words, IVs.

## III.4 One-hot from a witnessed field index, via binomial moments

**508 for a 256-way one-hot** · Universal · Measured

To prove a length-$n$ flag vector is the indicator of a witnessed index $L$, do not
decompose $L$ and do not emit $n$ equality gadgets. The moments
$M_d = \sum_k F_k \binom{k}{d}$ are *free affine combinations*, because the
binomials are compile-time constants. Assert Pascal's recurrence:

$$(L - d)\,M_d - (d+1)\,M_{d+1} = 0, \qquad d = 1,\dots,n-2$$

With $M_0 = \sum F = 1$ and $M_1 = \sum k F_k = L$, this forces
$M_d = \binom{L}{d}$ for every $d$, which forces $F$ to be one-hot at $L$.

At $n = 256$ that is 254 rank-1 rows — and **the two normalisation equations cost
zero**, because only 254 flags are witnessed and the last two are *defined* to make
them hold identically. The flags are then reusable as free affine selectors
everywhere downstream.

> **Don't confuse this with the other one-hot bound.** The proved $2^w - w - 1$
> lower bound is for building a one-hot from $w$ *boolean bits*. This is the
> different — and cheaper — problem of pinning a one-hot to a *field element*.

## III.5 Constant tables: the payload is free, and the one-hot is sub-linear

**2048 entries × $2\times 256$-bit payload $= \langle 225,225\rangle$** · Universal · Measured

**Part A — the payload costs nothing.** If the table entries are compile-time
constants and $e$ is a one-hot vector of variables, then $\mathrm{out} = \sum_i e_i
c_i$ is affine: $\langle 0,0\rangle$ per output column, *independent of payload
width*. Only building $e$ costs anything.

**Part B — a $k\times k$ one-hot needs only $(k-1)^2$ products.** Given two one-hot
vectors of length 4, the 16 outer-product cells need only the $3\times 3$ sub-grid
witnessed. The last column follows from the row identity $\sum_c \mathrm{cell}(a,c)
= P_a$, the last row from the column identity, and the corner from either — all
*polynomial* identities, so no booleanity of the underlying bits is needed to derive
them. Nested: 4-bit one-hot $=$ 9 products, 6-bit $=$ 45, 7-bit $=$ 63.

Contrast the *variable*-table case, where none of this applies: 16 entries × 9 fields
as a mux tree is $\langle 122,122\rangle$.

> **The boundary.** All of this is for *constant* data. A mux over variable data is
> $\langle \mathrm{size}, \mathrm{size}\rangle$ — one row per element, genuinely not
> free. See VI.4.

## III.6 Orthogonal idempotents make products of table reads affine

**$\langle 257,257\rangle \to \langle 225,225\rangle$ per window** · Universal · Measured

For a one-hot $e$ (so $e_a e_b = \delta_{ab} e_a$) and two constant tables,

$$\Bigl(\sum_a e_a u_a\Bigr)\Bigl(\sum_a e_a v_a\Bigr) = \sum_a e_a (u_a v_a)$$

— **affine in $e$, with compile-time coefficients.** A quadratic form in table
lookups is therefore free. Exploit it with

$$(P_0 + V_1)(P_1 + V_0) = P_0P_1 + P_0V_0 + P_1V_1 + V_0V_1$$

Because branch indicators of the same one-hot are orthogonal, $P_0P_1 = 0$, and
$V_0V_1$ is the free affine correction. **One row therefore pins two of the four
outer selector terms.**

Everyone knows the affine-remainder trick — a 4-way select of variable values costs
3 products because the one-hot sums to 1. Getting to 2 requires seeing that products
of *constant-table reads* collapse. Worth 672 score across 21 windows in one tree.

## III.7 Make the recoding a re-indexing, not a circuit

**$\langle 0,0\rangle$** · Universal · Measured

Booth and NAF recoding are normally implemented as arithmetic on the scalar, costing
rows per digit. Instead, **choose the digit convention so the recoded digit is
literally a bit of the input.** With $w$-bit windows and digits
$2\cdot\mathrm{window} + 1 - 2^w$ — always odd, always signed — the recoded bit
vector is just $\mathrm{bits}[254-c]$, with a constant at the top position.

The conditional complement that implements the sign is absorbed into the selector's
first product layer as $w_i = \mathrm{XNOR}(\mathrm{sign}, b_i)$, which you were
paying for anyway. Total cost of the recoding: zero.

Generalises to any windowed or signed decomposition of a witnessed integer. The move
is to let the *convention* absorb the work rather than the circuit.

## III.8 Prove a fact about your constant data to delete circuit logic

**deletes a whole borrow column** · Universal · Measured

Before adding witnesses, ask whether a compile-time invariant of your *precomputed
tables* makes them unnecessary.

Worked instance: every entry in a fixed-base table satisfies
$y \bmod 2^{64} \leq p \bmod 2^{64}$. Since $p = 2^{256} - 2^{32} - 977$ has upper
limbs all $2^{64}-1$, that single low-limb inequality forces *every* schoolbook
borrow of $p - y$ to vanish. Negation therefore becomes plain limbwise constant
subtraction — no packed-borrow column, no witnessed bits, no booleanity rows.

The invariant is discharged once, at compile time, against data you generated
yourself.

## III.9 Read the interface's assumptions before validating anything

**15,840 avoided** · Universal habit · Measured

The least mathematical entry here and one of the most valuable. The challenge
interface may already *give* you the well-formedness of public inputs as a
hypothesis. If it does, every byte you range-check is score spent proving something
you were handed.

In one tree the specification supplies "these inputs are octet strings" for free, so
the circuit never range-checks a public input byte. The byte-unpacking and the
entire PKCS#1 padding construction are certified at `Count.zero` — they emit no
operations at all, because the padding is a compile-time constant vector combined
affinely with the digest.

Cost of not reading it: 1,056 input bytes at $\langle 7,8\rangle$ each is **15,840
score**, about 5% of that circuit, for nothing.

## III.10 A gadget with constant arguments is not a cheaper gadget — it is no gadget

**$\langle 195,196\rangle \to \langle 61,61\rangle$** · Universal · Measured

In the first rounds of a hash, most of the state still equals the initialisation
vector. $\mathrm{Ch}(e,f,g)$ with $f$ and $g$ constant is, per bit, either a constant
or $e_j$ or $1-e_j$ — **affine, hence free.** Same for $\mathrm{Maj}$ with two
constant arguments.

| round | cost |
|---|---|
| round 1 of block 1 — no Ch gadget, no Maj gadget at all | $\langle 130,132\rangle$ |
| round 0 of block 1 — everything constant except one word | $\langle 61,61\rangle$ |
| a general round | $\langle 195,196\rangle$ |

Several constants can also be *folded together* at compile time — three constant
addends become one — and subtracting a constant is free two's complement,
$\mathrm{not}(C) + 1$, with no borrow logic.

**The audit:** walk the first and last rounds of any iterated construction and ask,
per gadget, how many of its arguments are compile-time known. The answer is rarely
zero, and every constant argument collapses part of the truth table into affine
wiring.

## III.11 Invert the certificate to move the awkward operand into the target

**−75 alloc / −77 constr per site** · Non-native arithmetic · Measured

You want $r = c\,a \bmod p$ with $c$ a compile-time constant, and you want to run the
certificate in a cheaper limb view than the one $a$ arrives in. Naively you must
re-limb $a$, which costs a normalisation. Don't — **certify the equation the other
way round.**

$c$ is invertible mod $p$, so $r = ca$ is equivalent to $c^{-1}r = a$. In that form
the two multiplicands are the freshly witnessed remainder (whose limbs come free out
of the bytes its canonicality check already allocates) and the compile-time constant
$c^{-1}$ — while $a$ appears *only as the certificate target*, an affine addend,
cheap in any limb view.

This is the consumer-functional law used as a design move rather than an audit:
targets are read as affine addends and are cheap in any view; multiplicands need full
rank. An inversion that swaps which value sits where can pay for itself outright.

**Sweep for it:** any fixed multiplier — endomorphism constants, curve constants,
Montgomery or Barrett factors, round constants — whose operand arrives in the wrong
view.

## III.12 Radix-pack before comparing, and let one product chain finish it

**4096-bit $<$ in $\langle 73,155\rangle = 228$** · Universal · Measured

A wide comparison is not a wide circuit if you pack first. Bytes are already known
to be bytes (III.9), and packing is affine, so it is free:

$$512 \text{ bytes} \longrightarrow 90 \text{ chunks of 6 bytes } (48\text{ bits}) \longrightarrow 18 \text{ groups of 5 chunks } (240\text{ bits})$$

both widths safely under the native prime. Then witness 17 prefix flags "groups
$0..g-1$ all equal", witness $\delta - 1$ range-checked to give strictness, and
close the five-way case split with **one product chain** (I.8) rather than five
selector-gated rows.

Total $\langle 73,155\rangle$ for a 4096-bit comparison — 0.07% of the circuit it
sits in. The three layers are independent and each is worth stealing on its own:
pack into the largest chunks the field allows, carry equality as prefix flags
rather than per-limb tests, and finish a disjunction with a product.

---

# Part IV — Bound arithmetic

In any non-native circuit, a quiet fraction of the score is decided not by the
algorithm but by the integers you wrote in the parameter file. This is the least
glamorous part of the subject and among the most reliably profitable.

## IV.1 Pseudo-Mersenne folding collapses the quotient to a single wire

**176/178 vs 464/468** · Structured modulus · Measured

The single biggest lever in non-native arithmetic. For $p = 2^{256} - c$ with $c$
small, $2^{256} \equiv c \pmod p$. Fold the high convolution positions back onto the
low ones by

$$d_k = c_k + c\cdot c_{k+m}$$

— **a free affine recombination**, because $c$ is a compile-time constant.

This shrinks the certified value from $\sim 2^{518}$ to $\sim 2^{323}$, so the
quotient becomes a *single field element* instead of a multi-limb big integer needing
its own 256-bit normalisation. And because each limb of $p$ is a constant, the whole
right-hand side $q\,p_k + t_k$ is affine in $q$, so the closing equation is one affine
row.

The textbook non-native modmul witnesses $q$ as a full-width integer and pays a range
check plus a second convolution $q \circledast p$. **Folding first makes both
disappear.**

> **Where it stops.** Requires a pseudo-Mersenne or low-Hamming-weight modulus. For a
> generic modulus — an RSA modulus, say — the quotient is irreducibly wide, and the
> score goes back to being dominated by certifying its bits.

## IV.2 Choose the limb base so the fold constant is limb-aligned

**176/178 → 97/99** · Non-native arithmetic · Measured

The fold constant enters the carry width *linearly*, so its representation in your
chosen base is a first-class cost decision. With $c = 2^{32} + 977$:

| base | digits of $c$ | cell inflation |
|---|---|---|
| $2^{64}$ | one 33-bit digit | $2^{33}$ |
| $2^{32}$ | $977$ and $1$ | $979$ |

The 15-cell convolution costs 8 rows more than the 7-cell one, but the quotient drops
$69 \to 38$ bits and the carry $101 \to 45$.

**And the re-limbing is free.** Splitting a 64-bit limb costs exactly what
normalising it already cost — witness the low half, range-check it, define the high
half affinely, range-check that — while additionally handing you the narrower limbs.
Better still, a value that already went through a byte-serialising validity check
hands you its 32-bit limbs as a pure affine recombination of four bytes, at zero cost.

A related freebie: you need not re-limb *both* operands. Place a 64-bit operand's
limbs at the *even* 32-bit positions with the literal zero expression at odd
positions. Half the positions are structurally zero, so the cap analysis charges the
smaller bound — mixed-base multiplication with no conversion at all.

## IV.3 Balanced (signed) limbs buy a bit of carry *and* a bit of quotient

**−20 per reduction** · Non-native arithmetic · Measured

Subtract a compile-time shift from every limb — affine, hence free — so digits carry
magnitude $\approx 2^{B-1}$ instead of $2^B - 1$. Each convolution coefficient loses
about two bits, so each carry width loses one: $\sum W_f$ goes 1170 → 1152 and the
peak width 33 → 32.

**The second effect is the one that is easy to miss.** Storing the residue in a
representative interval *centred on zero* rather than $[0,N)$ tightens the bound on
the next square, which drops the quotient's top limb by a bit — another $-2$ per
squaring, and the only reason that narrower quotient is sound at all.

Design note worth stealing: define the shift once in the *finest* radix and derive
every other view from it. Here one byte-level constant is read at three different limb
widths, which is what lets the circuit change radix mid-computation for free. Its
digits are genuinely mixed-radix — the correct cap at one width is $8{,}421{,}504$,
where the tempting $2^{23}$ is strictly smaller and *unsound*, and $2^{24}$ wastes a
full bit.

## IV.4 Exact mixed-radix bounds, never rounded powers of two

**a record, on four constants** · Non-native arithmetic · Measured

A bound written as $2^a$, or as a sum of two powers of two, is an *over-estimate* of a
quantity whose true value is a small integer multiple of a power of two. Carry width is

$$W_f = \bigl\lceil \log_2\bigl(\mathrm{OFF}_L + \mathrm{OFF}_R\bigr)\bigr\rceil$$

so rounding each addend up can push the ceiling across an integer boundary — and a bit
is 2 score at *every site sharing the parameter*.

| | rounded | exact |
|---|---|---|
| $\mathrm{Nf}_L$ | $2^{77}$ | $979\cdot 2^{67} + 3\cdot 2^{32}$ |
| $\mathrm{Nf}_R$ | $2^{70}$ | $2^{69} + 3\cdot 2^{64}$ |
| $\mathrm{OFF}_L$ | $2^{45} + 2^{14}$ | $979\cdot 2^{35} + 8192$ |
| $\mathrm{OFF}_R$ | $2^{39}$ | $2^{37} + 3\cdot 2^{32} + 256$ |

Carry width $46 \to 45$. That single bit propagated as $\langle -1,-1\rangle$ through
every gadget sharing the instance, for $-92$ at the top and a leaderboard record.

Note the shapes: $979 = 977 + 2$, the Solinas constant plus the borrow-free digit cap;
and $3$ is the digit cap. **The constants are structured, and the structure is what
the rounding destroys.**

The check is cheap and mechanical: for every bound constant in every parameter file,
write the true bound as an exact integer expression, recompute the ceiling, and see
whether the width falls. Any file whose entries are bare powers of two is a candidate.

## IV.5 Triangular term counts — the top cell has exactly one term

**−152, −124** · Non-native arithmetic · Measured

A convolution's per-position term count is $1,2,\dots,n,\dots,2,1$ — not a uniform
maximum. Declaring the bound as a constant function of position at the maximum cell
count over-charges every position but the middle, and the width tables should be
visibly tent-shaped.

$$\mathrm{qnCap}(m,k) = \min(k+1,\ m,\ 3m-1-k), \qquad \mathrm{triCap}(m,k) = \min\!\left(\tbinom{k+2}{2},\ \tbinom{3m-1-k}{2}\right)$$

The sharpest consequence: **the top cell has exactly one term**, and that is where the
quotient width gets decided. Two separate records came from noticing this on a single
position.

**The generalisation is two levers that only work together.** Lever A: propagate the
triangular profile through the fold, which turns a naive uniform cap into a steeply
decaying digit profile. Lever B: with $G$ groups, exactly one carry is materialised and
only its width is billed — and that width is dominated by the *top cell of the paid
group*, since $\mathrm{OFF}_L(0) \approx \mathrm{Nf}(gf_0 - 1)/2^B$. So widen group 0
until its top position sits at the *small* end of the decaying profile.

$$d = [6840,\ 5871,\ 4894,\ 3917,\ 2940,\ 1963,\ 986,\ 9] \quad\text{(not a uniform 979)}$$

Regrouping $[2,1,5] \to [6,1,1]$ makes $\mathrm{OFF}_L(0)$ read $d_5 = 1963$ rather
than $d_1 = 5871$:

$$1963\cdot 2^{34} \approx 3.372\times 10^{13}, \quad \mathrm{OFF}_R \approx 5.6\times 10^{11}, \quad \text{sum} \approx 3.43\times 10^{13} < 2^{45}$$

so $W_f = 45$; under $[2,1,5]$ the sum is $\approx 1.01\times 10^{14}$ and $W_f = 47$.
Two bits off every certificate sharing the instance.

**Neither lever works alone.** With a constant cap, regrouping changes nothing at all.
That is why this stayed unexploited for so long: each half, tried by itself, measures as
worth zero.

Exact cost of one certificate, $m$ limbs and one paid carry:

$$\bigl\langle (2m-1) + 1 + (q_{\text{bits}}-1) + (W_f-1),\ (2m-1) + q_{\text{bits}} + W_f + 1 \bigr\rangle$$

At $m=8$, $q_{\text{bits}}=38$, $W_f=45$ that is $\langle 97,99\rangle$.

**And the group schedule itself should follow the tent.** Group width is a per-position
optimisation against the local bound, not a global constant: wide groups where the tent
is thin at the edges, narrow where the coefficients peak. One graduated schedule runs
9, then 13, 12, 13, 6, 1 across 767 positions. The tents also *chain*: a square's
per-position bound should feed the next product's convolution directly rather than being
flattened to a scalar maximum first.

## IV.6 The residue-ring multiply — the fold polynomial is yours to choose

**$\langle 4,4\rangle$ vs $\langle 7,7\rangle$** · Non-native arithmetic · Measured + proved optimal

When a circuit multiplies limb vectors and immediately folds, it never consumes the full
$2m-1$ convolution — it consumes only $z \bmod (X^m - c_F)$. Multiplication in the
residue ring has bilinear rank

$$\sum_i \bigl(2\deg f_i - 1\bigr) \quad\text{over the irreducible factors } f_i$$

which beats $2m-1$ **whenever the modulus splits**. The gadget: witness the $m$ folded
coefficients $F$, and for each root $\rho$ emit one row

$$\Bigl(\sum_i a_i \rho^i\Bigr)\Bigl(\sum_i b_i \rho^i\Bigr) = \sum_k F_k \rho^k$$

one product per row, every coefficient a compile-time constant hence affine-free.
Soundness is Vandermonde uniqueness: $F - F_{\text{true}}$ has degree $< m$ and $m$
roots.

Measured: $c_F = 2^{32} + 977$ is a fourth power mod the BN254 scalar field, so
$X^4 - c_F$ splits completely and the rank is 4 — $\langle 4,4\rangle$ per product
against $\langle 7,7\rangle$.

**Before pricing a limb multiply, ask what the consumer actually reads.** If it reads a
residue, the fold polynomial is a free design choice and you should choose it to split.
Note the counterweight: splitting *most* is not the same as being best, because
coefficient size is priced too — at one base there were two admissible degree-8 moduli
and the smaller-coefficient one won despite splitting less.

## IV.7 Fold an intermediate into a consumer that has spare arity

**15,360 — the entire #1 vs #2 gap** · Universal · Measured

If your XOR gadget takes three operands per row and a consumer is currently using two,
an intermediate that is a pure affine combination of things that consumer already reads
is **free to fold in**.

In Keccak's $\theta$ the value $D[x] = C[x-1] \oplus \mathrm{ROT}(C[x+1],1)$ is never
materialised: it is folded into the very XOR3 that already had to consume $A[x,y]$.
Rotation is free wiring, so the rotated operand costs nothing to supply.

| | per round |
|---|---|
| $D$ materialised (rival) | $\langle 320,320\rangle + \langle 1600,1600\rangle = \langle 2560,2560\rangle$ |
| $D$ fused (record) | $\langle 640,640\rangle + \langle 1600,1600\rangle = \langle 2240,2240\rangle$ |

Both trees have identical XOR3 and $\chi$ rows. The fusion is the *only* difference, and
it is the whole 15,360-point gap between first and second place.

**The counting rule:** fold when the consumer's available arity exceeds the arity it
currently uses. This is the cheapest kind of win to find and the easiest to leave on the
table, because the intermediate usually has a name in the specification, and naming a
thing invites materialising it.

## IV.8 Sparse-prime canonicality, and knowing which sites need it at all

**264/272 vs 520/529** · Structured modulus · Measured

Two savings, and the second is larger than the first.

**Exploit the modulus's binary shape.** Do not normalise and then run a generic
comparison against $p$ — that decomposes 256 bits and then allocates another
256-bit difference, 520/529. Keep the limb bit-decompositions in scope and use
the fact that $p = 2^{256} - 2^{32} - 977$ has only **six zero bit positions**
(32, 9, 8, 7, 6, 4). Three zero tests summarise the long all-ones runs and a
couple of witnesses carry the prefix state. With the weak-inverse form of I.7
replacing those zero tests, the tail is four bare witnesses and four rows. At the
limb level the statement is simply

$$r < p \iff (r_1, r_2, r_3) \neq (2^{64}-1, 2^{64}-1, 2^{64}-1) \ \lor\ r_0 < p_0$$

**Then ask which sites need canonicality at all.** Full canonicality ($< p$) is
needed only at the *output* and wherever an equality or comparison is decided.
Every multiplication **operand** needs only a limb bound — a slope used solely as
a multiplicand never needs to be canonical, and saying so in the specification is
what makes the cheaper validator sound. Auditing a tree against that single
question is worth hundreds of rows per site, and it is the same audit as II.3 run
one level lower.

---

# Part V — Knowing when to stop

Proving a gadget is at its floor is worth as much as another optimization, because it
redirects every future hour. These are the only three tools that work, and each has a
sharp edge.

## V.1 Krull codimension — you can only shave rows by shaving witnesses

Universal · Proved

Each row is one hypersurface, so by Krull's height theorem every component of the
solution variety has codimension $\leq k$. If soundness demands the witness be
determined by the inputs, then $k \geq m - \dim V$, and

$$\text{score} \geq 2m - \dim V$$

> **Corrected, and the correction matters.** The argument above assumes every witness is
> uniquely pinned. Soundness only requires the *output* to be pinned, so intermediates may
> have positive-dimensional fibres. With $d$ the generic fibre dimension the honest bound is
> $$k \geq m - d, \qquad \text{score} \geq 2m - d$$
> and since $0 \leq d \leq m$ this bottoms out at $\text{score} \geq m$, where $m$ is a
> *design parameter*. **As a floor on a relation, Krull says nothing.** Treat it as a
> per-circuit bookkeeping identity, never as a floor.

**The strategic consequence survives, for a better reason.** A free dimension is worth 1 to
keep (drop the row, keep the allocation) but **2 to remove** — solve an affine functional
for one wire and substitute, which is free, and shrinking a fibre cannot break
output-constancy so soundness is automatic. So $d > 0$ is not an opportunity: **it is a
defect report naming $d$ deletable allocations.** Verified on 33,288 random systems with
zero counterexamples.

The dichotomy is exhaustive: either the freedom is *unused*, and it normalises away; or it
is *used*, and the fibre was not positive-dimensional in that direction. There is no third
case. The deepest reason is Lang–Weil: a positive-dimensional fibre over $\mathbb{F}_r$ is
automatically *nonempty*, so it carries no soundness content at all — the rows you would
"save" were never doing soundness work. **Dimension is soundness-inert over a finite field.**

So: you still cannot shave rows by cleverness in the constraint layer, only by shaving
witnesses. Conversely $k > m - \dim V$ *proves* redundancy exists.

**The auditor this yields.** $d$ is the corank of the Jacobian $\partial(\text{rows})/\partial w$
at a generic honest witness — a mechanical check naming exactly how many allocations are
free to delete. The compile-time companion is specific to R1CS: the degree-2 part of every
row is $(a_w\!\cdot\!w)(b_w\!\cdot\!w)$ with $a_w, b_w$ *compile-time constants*, so every
fibre's asymptotic cone lies in one fixed variety known before running anything.

## V.2 Bezout degree — and the bound that does *not* hold over $\mathbb{F}_p$

Universal · Carries a trap

Each row at most doubles degree, so $k \geq \log_2 \deg(\text{graph of the certified
relation})$. Sanity checks: $y = x^5$ needs $k \geq 3$, so a 3-row S-box is optimal and
no nondeterministic trick shaves it; $y = 1/x$ has graph $xy = 1$ of degree 2, so
$k \geq 1$ — correctly *not* penalising the witnessed-inverse trick.

> **The trap.** $\mathrm{MC} \geq \deg - 1$ **does not hold over $\mathbb{F}_p$.** One
> row doubles multilinear degree, so you only get $\mathrm{rows} \geq \lceil \log_2
> \deg\rceil$. Do not import the GF(2) degree bound (VII.4) to convince yourself an
> $\mathbb{F}_p$ gadget is optimal — the zero-test trick, a degree-$n$ function in two rows, is exactly
> the loophole.

A second trap, learned expensively: the Bezout row floor is valid only when the accepted
set is finite *in the ambient space you are arguing in*. When a 256-bit value's acceptor
lives in $\mathbb{F}_r^8$ rather than $\mathbb{F}_r^1$, a positive-dimensional component
escapes Bezout entirely and the honest floor drops by $4\times$. Check the ambient
dimension before quoting a floor.

## V.3 Counting over $\mathbb{F}_p$ — the bound that survives nondeterminism

Universal · Proved

A $k$-row, $m$-wire system is described by $3k(m+1)$ field elements, so with $s = k+m$,

$$s \geq 2\sqrt{\frac{\log_p |F|}{3}} - 1$$

This gives $s \geq 295$ for an arbitrary 16-bit table — **a rigorous proof that
lookup-free table emulation is expensive**, and the reason the $\sqrt N$ law of I.11 is
the right tool rather than a workaround.

> **Which of these survive nondeterminism.** Only V.1 was cracked, and it was the weakest.
> The Bezout bound *survives projection* — linear projection does not raise degree, so
> $\deg \overline{\pi(V)} \leq \deg V \leq 2^k$ and the bound holds for arbitrary fibres. The
> counting bound is manifestly nondeterminism-proof, since it counts circuits rather than
> varieties. **The money is in degree, not dimension.**

> **A ceiling on the whole hypersurface-counting programme.** Storch (1972) and
> Eisenbud–Evans (1973): every algebraic set in $\mathbb{A}^N$ is cut out set-theoretically
> by $N$ equations. So *any* argument that merely counts hypersurfaces can never prove a
> relation-level floor above $N = \text{inputs} + \text{outputs}$. Combined with arithmetical
> rank being degree-blind, that programme was capped before it began — which is why the
> rank-1, degree-2 *shape* is the only thing left to exploit.

> **Honest limit on all three tools.** They are geometric: they constrain the variety
> over the algebraic closure, while soundness concerns only the $\mathbb{F}_p$-points. By
> Lang–Weil they are effectively unconditional for gadgets under about 63 rows, and
> genuinely open above that. And there is no theory beyond them — our cost measure is
> *nondeterministic nonscalar complexity*, for which no superlinear lower bound is known
> on any explicit function, and the commutative-algebra invariant that would settle it
> (arithmetical rank) is provably degree-blind. Treat every "proved optimal" as "not
> beaten yet".

---

# Part VI — Traps

Each of these cost real submissions. They are included because the failure mode is
invisible from inside the design.

## VI.1 The exported cost must be definitionally equal to the internal ledger

Cost two submissions

If the top-level cost theorem is `fun input => Comb.costIs_main input`, the exported
literals must be *defeq* to whatever the internal constant evaluates to. Shrink the
circuit, update the internal constant, forget the exported one, and the term no longer
has its ascribed type — elaboration fails outright.

Twice this hid a finished improvement. Once a complete residue-ring multiply shipped with
the internal ledger correctly advanced and the exported literals still holding the value
from a small unrelated change: hard type error, status *failed*, and the improvement
invisible. Once an improvement was proved in a module nothing imported, so nineteen
consecutive submissions would have scored the old number even had they built.

**The rule:** after any cost change, re-derive the exported literals *from* the internal
constant rather than editing them by hand, and check every intermediate aggregate on the
path up. **The diagnostic:** extract every cost constant from both trees and diff; if the
top-level pair differs from its container's pair, that is the bug.

## VI.2 A pattern that has paid twice is a reason to check the next instance, never to assume it

Cost a work slot

After the exact-bounds lever (IV.4) paid twice, a sweep was queued over "the remaining
instances" on the assumption that they were still set from the uniform bound. They were
not — two of them were already exactly triangular, and the queued item was worth zero.

The same shape recurs with proxies. A lead was tracked by watching a *step total* rather
than the site it was actually about; the first unrelated change to that step reported the
lead as landed. **A proxy witness reports the tree moving, not the lead landing.**

Both are the same error: substituting an inference for a sighting. In a codebase being
changed concurrently by several agents, the only durable statement is one anchored to a
constant you have just read.

## VI.3 False friends — things that look like tricks and are not

Priced at zero

**A mux over variable data is not free.** It is $\langle \mathrm{size},
\mathrm{size}\rangle$ — one row per element. A 4-limb point mux is $\langle 4,4\rangle$;
a full accumulator-state mux is $\langle 16,16\rangle$. Only *constant-table* selection is
free (III.5), and conflating the two will make you budget a design that cannot be built.

**Splitting limbs "for free" is a re-accounting, not a saving.** It is free only because
the normalisation it replaces already cost the same. The actual saving is downstream, in
the narrower quotient and carry (IV.2) — quote it there, not twice.

**Merging duplicated one-hot decodes is ordinary common-subexpression elimination.** Real,
worth a few units once, and not a technique.

**The $2k-1$-point multiply is textbook Toom-style evaluation.** What is R1CS-specific —
and the only part worth writing down — is that the evaluation points being *compile-time
constants* is what keeps each row rank-1 and therefore legal. Its transferable variants are
the *mixed-width* form, which multiplies an $n_1$-vector by an $n_2$-vector at
$\langle n_1+n_2-1, n_1+n_2-1\rangle$ instead of padding both to the longer length, and the
*split-assert* form, which separates witnessing the coefficients from asserting the points
so a caller holding its own coefficients pays only $\langle 0, n-1\rangle$.

---

# Part VII — The GF(2) model

A separate cost model, kept separate on purpose. The field is $\mathbb{F}_2$ and
every row must literally have the shape

$$\mathrm{var}_k - A\cdot B, \qquad A, B \text{ affine}$$

with the $t$-th row's output side being exactly variable $n_0 + t$. That last
clause — the row must *produce a fresh output variable in sequence* — is what
voids most of Parts I–VI, because it forbids the free-standing affine assertion
that nearly every prime-field trick depends on.

Score is essentially $2\times$ the AND-gate count.

## VII.1 What is free, and it is most of the cipher

Everything $\mathbb{F}_2$-linear costs nothing: XOR, rotations, shifts, NOT, and
XOR with a constant. For Keccak that means $\theta$, $\rho$, $\pi$ and $\iota$ are
**all free**, and the entire permutation is priced by $\chi$ alone at one AND per
bit — $1600$ products per round, $12 \times 1600 = 19{,}200$ allocations and the
same in rows.

For SHA-256 the $\sigma$ and $\Sigma$ functions are likewise free, and what
remains is the adders and the two nonlinear functions.

This is the exact mirror of the prime field, where $\theta$ costs 2,240 per round
and XOR costs a row. **Do not carry intuitions across.**

## VII.2 The inversion: witness the product, derive the value

**the model's defining move**

Where the prime model says *witness the value and pin it*, the canonical model
says the opposite. Pinning a carry directly,

$$(c_{i+1} - c_i) - (x_i + c_i)(y_i + c_i) = 0$$

is a legal R1CS row and an **illegal canonical row**, because its output side is
not a bare fresh variable. So witness the product instead,

$$d_i := (x_i + c_i)(y_i + c_i)$$

and read the carry back as $c_{i+1} = c_i + d_i$ — a free affine prefix sum of the
witnessed products. Zero copy rows.

Every gadget in this model is built by asking *which product do I witness*, never
*which value do I pin*.

## VII.3 A full adder costs exactly one AND; a half adder with a constant costs zero

The carry of a full adder is a majority, and over $\mathbb{F}_2$

$$\mathrm{maj}(x,y,z) = (x+z)(y+z) + z$$

is a single product, while the sum $x \oplus y \oplus z$ is free. **One AND per
full adder.**

Better: a half adder whose second input is a *constant* dot is entirely free,
because both its sum $x \oplus K_i$ and its carry $x \cdot K_i$ are affine over
$\mathbb{F}_2$. It buys you a row exactly once, at whichever column you choose to
spend it — so the placement of constant addends inside a column-compression tree
is a real design decision.

Measured: a 4-operand-plus-constant 32-bit adder is $2 + 3 + 3 + 28\cdot 4 = 120$
products; a 7-operand version is 208, and that one additionally requires two
specific bits of the constant to vanish for the free half adder to be placeable.
Column 31 drops its carries entirely and is a plain XOR of its dots.

## VII.4 The multi-operand degree bound — and the error that inflates it

**Proved, and it closed a claimed 20,862-point gap to at most 1,182**

The ANF degree of the top output bit of a $k$-operand width-$n$ adder grows
**linearly in $k$**, so Schnorr's $\mathrm{MC} \geq \deg - 1$ bites much harder
than the two-operand case suggests. Exact degrees by Möbius transform:

| $k$ | degree | $\mathrm{MC} \geq$ at $n=32$ | column compression |
|---:|---|---:|---:|
| 2 | $n$ | 31 | 31 |
| 3 | $2n-3$ | 60 | 61 |
| 4 | $3n-6$ | 89 | 92 |
| 5 | $4n-11$ | 116 | 121 |

Adding a compile-time constant addend does **not** lower the degree, so
constant-fed trees inherit the bound. Exact SAT synthesis confirms the tightness
at small $n$: $\mathrm{MC}(3\text{-operand} \bmod 2^4) = 5 = 2n-3$, with
$\mathrm{MC} \leq 4$ proved UNSAT.

> **The error worth naming.** Quoting the *two*-operand degree for a $k$-operand
> adder understates the floor badly. Doing so once produced a claimed
> 20,862-point gap where the honest per-gadget slack is at most 591 ANDs
> $=1{,}182$ score. When a floor looks generous, check that its degree argument
> used the right arity.

## VII.5 The non-transfer list

| | prime R1CS | canonical GF(2) |
|---|---|---|
| single-row non-vanishing multiplier (I.1) | $\langle 1,1\rangle$ per bit | **impossible** — the only nonvanishing affine multiplier over $\mathbb{F}_2$ is 1, and the output cannot sit inside a multiplicand |
| λ-packing (I.2, I.3) | halves Ch/Maj/XOR2 | **impossible** — no constants but 0 and 1, so there is no λ |
| decoy roots (I.4) | 1 row | impossible for the same reason |
| booleanity rows | needed unless implied | never — every element *is* a bit |
| bit decomposition (II.10, III.1) | a real cost to defer | meaningless — words *are* bit vectors |
| XOR, rotations, XOR-with-constant | free (affine) | free ($\mathbb{F}_2$-linear) — **the one that ports** |
| $\theta, \rho, \pi, \iota$ | $\theta$ costs 2,240/round | **free** |
| a pure affine assertion | 1 row, 0 witnesses | not expressible as a useful row |
| "assertion, not value" (II.1) | $-531$ per site | a category error — there is no materialised emulated value to delete |

## VII.6 Where the prime field wins, and by how much

The two models are not ordered; each wins somewhere, and the boundary is a packing
rule rather than a slogan.

$\mathbb{F}_p$ **wins on wide fan-in conjunctions.** $\mathrm{AND}(x_1,\dots,x_n)$
is $s = \sum x_i - n$ — free, affine — followed by a two-row zero test. **Two rows
independent of $n$**, against $n-1$ AND gates over GF(2), which is tight there by
Schnorr's degree bound. Same for OR.

GF(2) **wins on XOR**, free there and a row in the prime field. That single
asymmetry is why a field-based SHA-256 needs $\sim 30{,}952$ nonlinear constraints
while the boolean circuit needs $22{,}573$ AND gates.

**Practical rule for the prime field:** keep values integer-packed so XOR chains
become free sums, and bit-split only when a genuinely bitwise operation forces it.

**Ceiling on the whole question:** the counting bound over a 254-bit field is
weaker than the GF(2) bound by a factor

$$\frac{\sqrt{3\log_2 p}}{2} \approx 14$$

so information-theoretically a large field can buy at most $\sim 14$–$16\times$
over the best boolean circuit. Published AND-gate records are a realistic if
modestly loose guide to what is reachable.

---

*Compiled from a running optimization loop against live competitors under the cost model
$\text{allocations} + \text{constraints}$. Prices are the deltas actually observed on
submission, not projections.*
