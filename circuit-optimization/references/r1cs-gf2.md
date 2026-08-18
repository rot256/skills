# R1CS Optimization Over GF(2)

The field is $\mathbb{F}_2$ and every row has the shape $var_k - A\cdot B$ with $A, B$ affine, the $t$-th row's output side being exactly variable $n_0 + t$.
That last clause -- every row produces a fresh output variable in sequence -- is what makes this a different cost model: there is no free-standing affine assertion to lean on.
Only the AND gates cost anything: everything $\mathbb{F}_2$-linear is free, so the count of witnessed products is the whole bill.

## The Free Linear Layers

Everything $\mathbb{F}_2$-linear costs nothing: XOR, rotations, shifts, NOT, and XOR with a constant.
For Keccak that means $\theta$, $\rho$, $\pi$ and $\iota$ are **all free**, and the entire permutation is priced by $\chi$ alone at one AND per bit -- $1600$ products per round, $12 \times 1600 = 19{,}200$ witnesses and the same in rows.

For SHA-256 the $\sigma$ and $\Sigma$ functions are likewise free, and what remains is the adders and the two nonlinear functions.

## Every Two-Input Gate Costs Zero or One Product

Write any two-input function uniquely as f(x,y) = a + bx + cy + dxy over GF(2).
The quadratic coefficient d is either 0 or 1, so of the sixteen two-input functions exactly eight are affine and free, and exactly eight cost exactly one product.
AND, NAND, OR and NOR are therefore all the same price, because complementing an input or an output is free, and XOR and XNOR cost nothing at all.
The gate taxonomy inherited from hardware carries no cost information here, and neither do the NAND-universality rewritings that go with it: the only question worth asking about a two-input gate is whether its quadratic coefficient vanishes.
Where it stops: at fan-in above two the counting collapses, and the bound that replaces it is the degree bound recorded in "The Multi-Operand Degree Bound".

## A Two-Way Select Costs One Product

Selecting between two values, out = s*a + (1+s)*b over GF(2), is out = b + s*(a + b), one product however the select was originally written.
A T flip-flop's Q_next = T xor Q is the degenerate case and is free; expanding it into T*(1+Q) + (1+T)*Q, as a hardware text will, raises a free operation to two products.
A JK form Q_next = J*(1+Q) + (1+K)*Q collapses the same way to J + Q*(J + K + 1), which checks out at Q = 0 giving J and at Q = 1 giving K + 1.
Where it stops: the identity saves nothing when both selected sides are compile-time constants, since the whole select is then affine and free, and it does not amortize across width -- one selector driving n data bits costs one product per bit, so a win there has to come from making the difference a + b constant rather than from the select.

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

## Published AND-Gate Records for Standard Primitives

The NIST Circuit Complexity Project publishes gate-level circuits for standard primitives, reporting total gate count, a per-type breakdown, and depth.
Its figures, in gates: the AES S-box at 113 total, 32 AND, 77 XOR, 4 XNOR, 0 NOT, total depth 27, AND depth 6.
AES-128 with both key and message as circuit inputs at 28,600 total, 6,400 AND, 21,356 XOR, 844 XNOR, 0 NOT, total depth 326, AND depth 60.
SHA-256 on a message input at 115,882 total, 22,385 AND, 89,248 XOR, 3,894 XNOR, 355 NOT, total depth 5,403, AND depth 1,604.
Only the AND column is a price in this model: the XOR, XNOR and NOT columns are free, and both depth columns are free.
That the AES-128 circuit spends 21,356 XOR and 844 XNOR gates to reach 6,400 AND gates is the shape you want, not a cost to be alarmed by.
Use these as a ceiling on what a hand-built gadget should cost, and as the number to beat before claiming an improvement.
They are the best published circuits, not proved optima, so they are not floors.

## Match the Metric Before Importing a Published Circuit

A published boolean circuit was minimized for one metric: total gate count for lightweight cryptography on constrained devices, nonlinear gate count for multi-party computation, zero-knowledge proofs and side-channel protection, and AND depth for homomorphic encryption.
Only the nonlinear count is charged in this model.
A circuit whose selling point is low depth has traded AND gates away for depth and is the wrong import here; Boyar, Find and Peralta, "Small Low-Depth Circuits for Cryptographic Applications" (2019), is exactly such a line of work.
The same holds for total-gate-count minimization, which spends effort shaving XOR, XNOR and NOT gates that this model gives away.
Reading the metric costs nothing, and importing against the wrong one costs the full difference in AND count.
Where it stops: if the boolean gadget is embedded in a trace-based system rather than being the whole circuit, rows and width are charged too, and a long AND chain can re-enter the bill as sequential rows, at which point depth is no longer free and the low-depth variant is worth re-pricing.

## Linear-Layer XOR Minimization Prices What This Model Gives Away

An entire literature minimizes the XOR count of a linear layer given as an m x n binary matrix, and none of it transfers.
Three distinct metrics appear, and they are not interchangeable: direct XOR (d-XOR), implementing each output row independently at weight(M) - m operations; sequential XOR (s-XOR), counting only in-place updates x_i = x_i xor x_j, which is the metric for quantum implementations; and general XOR (g-XOR), counting operations that write to a fresh target, whose minimization is the Shortest Linear Program problem, NP-hard by Boyar, Matthews and Peralta (2013).
All three price XOR, which is free here, so an SLP-optimal linear layer and the naive row-by-row one both cost zero AND gates.
s-XOR is irrelevant twice over, since a constraint system has no register to update in place.
Do not spend search time here, and do not accept an XOR count as evidence that a linear layer was optimized for you.
Where the concern comes back: only where an XOR is actually charged, which in practice means bits materialized in a prime field, where a bitwise XOR is a row.
There the better move is upstream, keeping values packed so the XOR is a free field sum, rather than importing an SLP solver.

## Minimal Sum-of-Products Is the Wrong Objective

Classical minimization -- Karnaugh maps, prime implicants, Quine-McCluskey -- minimizes the number of product terms and literals in an AND-OR-NOT basis, on the premise that each term and each literal is a component to be built.
That premise is false here: complements are free, the OR is not the operation we charge, and XOR, which a sum-of-products basis cannot express compactly, costs nothing.
The gap is measurable on the standard textbook examples.
A function whose minimal sum of products is y = a + b'c + bc', three product terms, is a + b + c + a*(b + c) over GF(2): one product.
A second, minimizing to Z = A'B' + A'C + B'C, has ANF 1 + A + B + AB + AC + BC, which factors as 1 + A + B + C + (A + C)*(B + C): again one product against three.
So a minimal SOP is not a minimal product count, and on small examples it overshoots by around a factor of three.
The objective that replaces it: put the function in algebraic normal form, read its degree for the lower bound, and factor the degree-two-and-above part into as few products as possible, sweeping everything else into the free affine layer.

## Paar's Greedy Pair Heuristic, and Its Monomial Form

Paar (1997) minimizes XOR count greedily: represent the target as a binary matrix, count for every unordered pair of columns how many rows contain both, extract the most frequent pair as a new variable t = x_i xor x_j, append t as a column and clear those two entries in every row containing the pair, and repeat until every output row has a single entry.
The transposition is what matters here.
Represent an n-variable boolean function with m monomials as an m x n binary matrix whose rows are the monomials' exponent vectors, and run the identical algorithm: row addition becomes monomial multiplication, so each extracted pair is one AND gate rather than one XOR gate, and the greedy step is shared-submonomial extraction that minimizes AND count directly.
The heuristic is greedy, with no optimality guarantee, and the plain transposition implements each monomial independently and shares nothing across degrees, so it needs the affine normalization of "Affine Equivalence Is Free, So Synthesize the Class Representative" to be worth running.
Where it stops: Paar's heuristic is cancellation-free.
A cancellation is a gate whose two inputs share a term that vanishes, and a greedy pair-frequency search can never construct one, which is why cancellation-free algorithms are sub-optimal (Boyar, Find and Peralta, 2019); Maximov and Ekdahl (2019), Banik, Funabiki and Isobe (2019), and Xiang, Zeng, Lin, Bao and Zhang (2020) exploit cancellation.
That blind spot is also what licenses the monomial reinterpretation, since monomial multiplication has no cancellation to model.

## Affine Equivalence Is Free, So Synthesize the Class Representative

Over GF(2) an invertible affine change of input variables and an affine correction of the output are XOR and NOT only, hence free in this model.
The AND count of f therefore equals the AND count of every function in its affine equivalence class, so synthesize whichever representative is cheapest and compose the free affine maps back on.
The pipeline for a single boolean function f of degree d: split f into homogeneous parts f = a + f_1 xor ... xor f_d, apply an affine transformation to the top part f_d alone to reduce its monomial count and fold any lower-degree monomials it creates into the corresponding f_i, run the monomial form of Paar's heuristic on the degree-d terms, apply the inverse affine transformation to the resulting circuit, and repeat downward.
Measured, for n = 6: there are 150,357 affine equivalence classes, and the top homogeneous part of a class representative reduces to 1 monomial for each of the 74,596 degree-6 classes, 1 for each of the 73,262 degree-5 classes, at most 3 for each of the 2,465 degree-4 classes, at most 5 for each of the 30 degree-3 classes, and at most 3 for each of the 3 degree-2 classes.
So on six variables the top layer of any boolean function collapses to at most five monomials before a single gate is chosen.
The price is locating the right affine equivalence class, which is the most time-consuming phase; everything after it is cheap.
Where it stops: the method matches known optimal nonlinear-gate counts only for some classes at n <= 6, which is the range where optimal values exist to compare against, and it is currently more efficient only when a low-weight class representative is available.

## Multiplicative Complexity Is a Floor Only Without Nondeterminism

Multiplicative complexity is the minimum number of AND gates in a circuit over the basis (AND, XOR, 1) that computes f, put on its modern footing by Boyar, Peralta and Pochuev (2000), with exact results for small classes by Find, Smith-Tone and Sonmez Turan (2017), Calik, Sonmez Turan and Peralta (2019), and Sonmez Turan and Peralta (2021).
In the cost model of this file an MC bound is a genuine floor on rows, and it is worth being explicit about why: every non-input variable is the output side of some row, there is no free-standing assertion to hang a check on, and therefore the prover has no advice to supply.
The constraint system and the circuit are the same object here, which is a property of this model rather than of MC.
The moment the arithmetization admits a free witness and an assertion -- any prime-field R1CS, AIR or PLONKish system -- MC stops lower-bounding the constraint count, because you may witness the answer and check a relation rather than evaluate one.
The sharpest case is inversion in GF(2^k): the forward map is a chain of multiplications, while checking a witnessed y against x*y = 1 is one multiplication plus whatever handles x = 0, and the gap widens with k.
So quote MC as a floor only after confirming the surrounding system cannot supply advice, and never carry it into the prime field.
