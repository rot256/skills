# R1CS Optimization Over GF(2)

The field is $\mathbb{F}_2$ and every row has the shape $var_k - A\cdot B$ with $A, B$ affine, the $t$-th row's output side being exactly variable $n_0 + t$.
That last clause -- every row produces a fresh output variable in sequence -- is what makes this a different cost model: there is no free-standing affine assertion to lean on.
Only the AND gates cost anything: everything $\mathbb{F}_2$-linear is free, so the count of witnessed products is the whole bill.

## The Free Linear Layers

Everything $\mathbb{F}_2$-linear costs nothing: XOR, rotations, shifts, NOT, and XOR with a constant.
For Keccak that means $\theta$, $\rho$, $\pi$ and $\iota$ are **all free**, and the entire permutation is priced by $\chi$ alone at one AND per bit -- $1600$ products per round, $12 \times 1600 = 19{,}200$ witnesses and the same in rows.

For SHA-256 the $\sigma$ and $\Sigma$ functions are likewise free, and what remains is the adders and the two nonlinear functions.

## Full Adders and Free Half Adders

The carry of a full adder is a majority, and over $\mathbb{F}_2$ $maj(x,y,z) = (x+z)(y+z) + z$ is a single product, while the sum $x \oplus y \oplus z$ is free.
**One AND per full adder.**

Better: a half adder whose second input is a *constant* dot is entirely free, because both its sum $x \oplus K_i$ and its carry $x \cdot K_i$ are affine over $\mathbb{F}_2$.
It buys you a row exactly once, at whichever column you choose to spend it -- so the placement of constant addends inside a column-compression tree is a real design decision.

Measured: a 4-operand-plus-constant 32-bit adder is $2 + 3 + 3 + 28\cdot 4 = 120$ products; a 7-operand version is 208, and that one additionally requires two specific bits of the constant to vanish for the free half adder to be placeable.
Column 31 drops its carries entirely and is a plain XOR of its dots.

## Witnessing Products Rather Than Values

Pinning a carry directly, $(c_{i+1} - c_i) - (x_i + c_i)(y_i + c_i) = 0$, is **not a legal row**: its output side is not a bare fresh variable.
So witness the product instead, $d_i := (x_i + c_i)(y_i + c_i)$ and read the carry back as $c_{i+1} = c_i + d_i$ -- a free affine prefix sum of the witnessed products.
Zero copy rows.

Every gadget in this model is built by asking *which product do I witness*, never *which value do I pin*.

## The Multi-Operand Degree Bound

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
> One such miscount put the apparent slack near 10,400 AND gates, where the honest per-gadget figure was at most 591.
> When a floor looks generous, check that its degree argument used the right arity.
