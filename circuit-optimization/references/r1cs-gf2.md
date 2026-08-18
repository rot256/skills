# R1CS Optimization Over GF(2)

*A field manual for the boolean cost model.*

A separate cost model, kept apart on purpose: prime-field R1CS is `r1cs-fp.md`, cross-arithmetization moves are `techniques.md`.
The field is $\mathbb{F}_2$ and every row must literally have the shape $var_k - A\cdot B, A, B affine$ with the $t$-th row's output side being exactly variable $n_0 + t$.
That last clause -- the row must *produce a fresh output variable in sequence* -- is what voids most of the prime-field material, because it forbids the free-standing affine assertion that nearly every prime-field trick depends on.

Cost is essentially $2\times$ the AND-gate count.

## The Free Linear Layers
Everything $\mathbb{F}_2$-linear costs nothing: XOR, rotations, shifts, NOT, and XOR with a constant.
For Keccak that means $\theta$, $\rho$, $\pi$ and $\iota$ are **all free**, and the entire permutation is priced by $\chi$ alone at one AND per bit -- $1600$ products per round, $12 \times 1600 = 19{,}200$ witnesses and the same in rows.

For SHA-256 the $\sigma$ and $\Sigma$ functions are likewise free, and what remains is the adders and the two nonlinear functions.

This is the exact mirror of the prime field, where $\theta$ costs 2,240 per round and XOR costs a row.
**Do not carry intuitions across.**

## Full Adders and Free Half Adders
The carry of a full adder is a majority, and over $\mathbb{F}_2$ $maj(x,y,z) = (x+z)(y+z) + z$ is a single product, while the sum $x \oplus y \oplus z$ is free.
**One AND per full adder.**

Better: a half adder whose second input is a *constant* dot is entirely free, because both its sum $x \oplus K_i$ and its carry $x \cdot K_i$ are affine over $\mathbb{F}_2$.
It buys you a row exactly once, at whichever column you choose to spend it -- so the placement of constant addends inside a column-compression tree is a real design decision.

Measured: a 4-operand-plus-constant 32-bit adder is $2 + 3 + 3 + 28\cdot 4 = 120$ products; a 7-operand version is 208, and that one additionally requires two specific bits of the constant to vanish for the free half adder to be placeable.
Column 31 drops its carries entirely and is a plain XOR of its dots.

## Non-Portable Prime-Field Tricks
| | prime R1CS | GF(2) (row-sequential) |
|---|---|---|
| single-row non-vanishing multiplier (`r1cs-fp.md` "The Single-Row Non-Vanishing Multiplier") | $\langle 1,1\rangle$ per bit | **impossible** -- the only nonvanishing affine multiplier over $\mathbb{F}_2$ is 1, and the output cannot sit inside a multiplicand |
| lambda-packing (`r1cs-fp.md` "Paired Gadget Packing", "Consumer-Determined Lambda Packing") | halves Ch/Maj/XOR2 | **impossible** -- no constants but 0 and 1, so there is no lambda |
| decoy roots (`r1cs-fp.md` "Out-of-Range Decoy Roots") | 1 row | impossible for the same reason |
| booleanity rows | needed unless implied | never -- every element *is* a bit |
| bit decomposition (`r1cs-fp.md` "Unreduced Words in Field Sums", "Shared Bit Decomposition") | a real cost to defer | meaningless -- words *are* bit vectors |
| XOR, rotations, XOR-with-constant | free (affine) | free ($\mathbb{F}_2$-linear) -- **the one that ports** |
| $\theta, \rho, \pi, \iota$ | $\theta$ costs 2,240/round | **free** |
| a pure affine assertion | 1 row, 0 witnesses | not expressible as a useful row |
| "assertion, not value" ("Deletable Certificate Targets") | $-531$ per site | a category error -- there is no materialised emulated value to delete |

## Prime Field Versus GF(2)
The two models are not ordered; each wins somewhere, and the boundary is a packing rule rather than a slogan.

$\mathbb{F}_p$ **wins on wide fan-in conjunctions.** $AND(x_1,\dots,x_n)$ is $s = \sum x_i - n$ -- free, affine -- followed by a two-row zero test.
**Two rows independent of $n$**, against $n-1$ AND gates over GF(2), which is tight there by Schnorr's degree bound.
Same for OR.

GF(2) **wins on XOR**, free there and a row in the prime field.
That single asymmetry is why a field-based SHA-256 needs $\sim 30{,}952$ nonlinear constraints while the boolean circuit needs $22{,}573$ AND gates.

**Practical rule for the prime field:** keep values integer-packed so XOR chains become free sums, and bit-split only when a genuinely bitwise operation forces it.

**Ceiling on the whole question:** the counting bound over a 254-bit field is weaker than the GF(2) bound by a factor $\frac{\sqrt{3\log_2 p}}{2} \approx 14$ so information-theoretically a large field can buy at most $\sim 14$-$16\times$ over the best boolean circuit.
Published AND-gate records are a realistic if modestly loose guide to what is reachable.

## GF(2)

### Witnessing Products Rather Than Values
Where the prime model says *witness the value and pin it*, this model says the opposite.
Pinning a carry directly, $(c_{i+1} - c_i) - (x_i + c_i)(y_i + c_i) = 0$ is a legal R1CS row and an **illegal row here**, because its output side is not a bare fresh variable.
So witness the product instead, $d_i := (x_i + c_i)(y_i + c_i)$ and read the carry back as $c_{i+1} = c_i + d_i$ -- a free affine prefix sum of the witnessed products.
Zero copy rows.

Every gadget in this model is built by asking *which product do I witness*, never *which value do I pin*.

### The Multi-Operand Degree Bound
The ANF degree of the top output bit of a $k$-operand width-$n$ adder grows **linearly in $k$**, so Schnorr's $MC \geq \deg - 1$ bites much harder than the two-operand case suggests.
Exact degrees by Mobius transform:

| $k$ | degree | $MC \geq$ at $n=32$ | column compression |
|---:|---|---:|---:|
| 2 | $n$ | 31 | 31 |
| 3 | $2n-3$ | 60 | 61 |
| 4 | $3n-6$ | 89 | 92 |
| 5 | $4n-11$ | 116 | 121 |

Adding a compile-time constant addend does **not** lower the degree, so constant-fed trees inherit the bound.
Exact SAT synthesis confirms the tightness at small $n$: $MC(3-operand \bmod 2^4) = 5 = 2n-3$, with $MC \leq 4$ proved UNSAT.

> **The error worth naming.**
> Quoting the *two*-operand degree for a $k$-operand adder understates the floor badly.
> Doing so once produced an apparent 20,862 gap where the honest per-gadget slack is at most 591 ANDs $=1{,}182$ cost.
> When a floor looks generous, check that its degree argument used the right arity.
