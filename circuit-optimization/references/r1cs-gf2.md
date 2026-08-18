# R1CS Optimization Over GF(2)

The field is $\mathbb{F}_2$ and every row has the shape $var_k - A\cdot B$ with $A, B$ affine, the $t$-th row's output side being exactly variable $n_0 + t$.
That last clause -- every row produces a fresh output variable in sequence -- is what makes this a different cost model: there is no free-standing affine assertion to lean on.
Only the AND gates cost anything: everything $\mathbb{F}_2$-linear is free, so the count of witnessed products is the whole bill.
For Boolean relations in advice-bearing R1CS, AIR, PLONKish, lookup, or custom-gate systems, start with `boolean-zk.md`; the exact XAG equivalence in this file does not apply there automatically.
For a proof system native over $\mathbb F_{2^k}$ or a tower priced in subfield multiplications, use `binary-extension-fields.md` instead of treating each native product as one bit AND.

## The Free Linear Layers

Everything $\mathbb{F}_2$-linear costs nothing: XOR, rotations, shifts, NOT, and XOR with a constant.
For Keccak, $\theta$, $\rho$, $\pi$, and $\iota$ are free, so only $\chi$ is charged at one AND per bit.
For SHA-256, the $\sigma$ and $\Sigma$ maps are free, leaving adders and nonlinear choice/majority logic.

## Every Two-Input Gate Costs Zero or One Product

Write any two-input function uniquely as f(x,y) = a + bx + cy + dxy over GF(2).
The quadratic coefficient d is either 0 or 1, so of the sixteen two-input functions exactly eight are affine and free, and exactly eight cost exactly one product.
AND, NAND, OR and NOR are therefore all the same price, because complementing an input or an output is free, and XOR and XNOR cost nothing at all.
Hardware gate taxonomy and NAND-only rewrites are irrelevant; above fan-in two, use ANF factoring and polar-rank constructions instead.

## A Two-Way Select Costs One Product

Selecting between two values, out = s*a + (1+s)*b over GF(2), is out = b + s*(a + b), one product however the select was originally written.
If both branches are constants the select is affine and free; an unconstrained $n$-bit word mux costs $n$ products unless the branch difference has lower rank.

## Full Adders and Free Half Adders

The carry of a full adder is a majority, and over $\mathbb{F}_2$ $maj(x,y,z) = (x+z)(y+z) + z$ is a single product, while the sum $x \oplus y \oplus z$ is free.
Ripple addition modulo $2^n$ uses $n-1$ products because the top carry is discarded, or $n$ products when carry-out is returned.
A half adder with a constant input is free, so place constant dots where they replace a paid half adder in a column-compression tree; the top column also discards its carries.

## Witnessing Products Rather Than Values

Pinning a carry directly, $(c_{i+1} - c_i) - (x_i + c_i)(y_i + c_i) = 0$, is **not a legal row**: its output side is not a bare fresh variable.
So witness the product instead, $d_i := (x_i + c_i)(y_i + c_i)$ and read the carry back as $c_{i+1} = c_i + d_i$ -- a free affine prefix sum of the witnessed products.
Zero copy rows.

Every gadget in this model is built by asking *which product do I witness*, never *which value do I pin*.

## Published AND-Gate Records for Standard Primitives

The NIST circuits provide useful ceilings: AES S-box 32 AND, AES-128 with key input 6,400 AND, and SHA-256 22,385 AND.
Ignore their XOR/XNOR/NOT totals in this model, and treat the AND counts as lineage-specific upper bounds rather than optima.

## Match the Metric Before Importing a Published Circuit

Import only circuits optimized for nonlinear/AND count; total gate count and low-depth designs may spend extra ANDs to save resources this model does not charge.
If the target is trace- or row-scheduled, reprice depth, width, and materialized affine values in the appropriate backend reference.

## Linear-Layer XOR Minimization Prices What This Model Gives Away

Direct, sequential, and general XOR minimization all optimize a resource that costs zero here.
Build small nonlinear cores joined by arbitrary affine maps, and use XOR count only as an explicit tie-break for a measured implementation cost.
If XORs are materialized in another backend, reprice the complete circuit there instead of combining XOR and AND into a unit gate count.

## Minimal Sum-of-Products Is the Wrong Objective

Karnaugh, Quine-McCluskey, and SOP minimization price complements, literals, and ORs instead of the products in an XAG.
Convert to ANF and factor affine forms; for example $a+b'c+bc'=a+b+c+a(b+c)$ uses one product rather than three SOP terms.
A minimal SOP is therefore not a minimum-product XAG.

## The Unfactored ANF Is Only an Upper Bound

Every Boolean function has a unique algebraic normal form, so it is a reliable interchange format but not a minimum circuit.
Realizing every degree-$d$ monomial as its own chain gives the construction bound

$$MC(f)\leq\sum_{S:a_S=1}\max(0,|S|-1),$$

before sharing products between monomials or outputs.
Use the unfactored count to size a baseline, run factoring or exact synthesis, and stop quoting it as soon as a shared realization exists.

## Conditional Linear Maps Cost Their Rank

Let a selector $s$ choose between a vector $u$ and a fixed linear image $T(u)$, so the output is $u+s(T-I)u$.
If $r=\operatorname{rank}(T-I)$, factor $T-I=AB$, compute the $r$ products $s(Bu)_i$, and apply $A$ for free.
A word mux between unconstrained $n$-bit words uses $n$ products, while a promised difference subspace of dimension $r$ reduces the construction to $r$ only if the constraints enforce the promise.
A conditional cyclic rotation by $d$ positions uses $n-\gcd(n,d)$ products after factoring $T-I$.
A conditional nonzero logical shift has full-rank $T-I$ and uses $n$ products.
The unconditional maps themselves, including rotations, shifts, basis changes, and any fixed binary matrix, remain free.

## Basic Word Gadgets

Build modular subtraction like addition: $n-1$ products modulo $2^n$, or $n$ when borrow-out is returned.
Use the final borrow as an unsigned less-than bit in the same $n$-product construction.
Build equality as the product of the $n$ affine bit-equalities $1+x_i+y_i$, using $n-1$ products.
For Hamming distance, XOR corresponding inputs for free and feed the result to the popcount construction.
These are prices for materialized deterministic outputs; an advice-bearing checker or a backend-native comparison relation must be priced in its own reference rather than imported here.

## Bilinear Maps and Tower Arithmetic

Fixed linear maps, basis conversions, permutations, rotations, and Frobenius maps cost no products, so expose them around the nonlinear core instead of materializing their XOR networks.
A rank-$R$ decomposition of a bilinear tensor gives an $R$-product construction: evaluate its two families of linear forms, multiply corresponding pairs, and linearly recombine the results.
The scalar dot product, componentwise product, and full outer product have direct $n$-, $n$-, and $mn$-product constructions respectively.
For length-$2^t$ polynomial multiplication, recursive Karatsuba gives a $3^t$-product construction before any modulus-specific reduction.
Ordinary Toom-$k$ interpolation needs $2k-1$ distinct projective evaluation points, so over $\mathbb F_2$ the three available points already block the direct Toom-3 recipe; moving evaluations into an extension field is allowed only after repricing those extension multiplications.
A tower of $t$ quadratic extensions similarly gives a $3^t$-product field-multiplication construction, hence 27 products for one quadratic-tower construction of $\mathbb F_{2^8}$ multiplication.
Search for a smaller multiplication tensor in the chosen basis before using the tower construction as a baseline.

## Paar's Greedy Pair Heuristic, and Its Monomial Form

Represent ANF monomials as rows of exponent vectors, repeatedly extract the variable pair occurring in the most rows, and replace it with one shared product.
Run the heuristic across all outputs and after several affine input transforms, keeping the lowest AND count and then depth.
It is fast but cancellation-free and has no optimality guarantee, so verify the result exhaustively and use exact synthesis on small residual windows.

## Affine Equivalence Is Free, So Synthesize the Class Representative

Over GF(2) an invertible affine change of input variables and an affine correction of the output are XOR and NOT only, hence free in this model.
Thus $f(x)$ and $g(Ax+a)+b\mathbin{\cdot}x+c$ have the same multiplicative complexity for invertible $A$.
Synthesize the cheapest representative and compose the free affine maps back on.
For a heuristic search, minimize the highest homogeneous ANF part under affine transforms, fold induced lower-degree terms downward, factor, and repeat by degree.
Use full affine classes rather than hardware NPN classes; for multiple outputs, search transforms and products jointly because per-output minima need not share.

## Quotient Translation Invariances Exactly

For a scalar function $f$, compute the translation-invariance subspace

$$
V_f=\{a:f(x)=f(x+a)\text{ for every }x\}.
$$

If $\dim V_f=k$, choose a rank-$(n-k)$ linear map $L$ with kernel $V_f$ and define the quotient function $g$ by $f(x)=g(Lx)$.
Synthesize the smaller $g$ and substitute its inputs with the affine forms in $L$.
For several outputs, use only a jointly verified common invariance subspace because separate scalar quotients do not prove that their nonlinear cores share.

## Factor the Affine Hull of the On-Set

For a nonzero scalar function whose on-set lies in a proper affine space $A=a+V$, write $f=\chi_A f_A$, where $f_A$ is the projection to $\dim A$ coordinates.
If $c=n-\dim A\geq1$, express membership as a $c-1$ product tree of independent affine equality bits.
Compute the minimal affine hull, synthesize $f_A$, join it to the membership bit with one product, and compare the complete lifted XAG with direct synthesis.
The zero function is already free, and a full-dimensional hull gives no reduction.
If $f$ is also translation-invariant, quotient the projected $f_A$ before synthesis and verify the composed coordinate map exhaustively.
Use `scripts/regular_reduce.sage` to emit and verify these reductions and optionally synthesize a lifted local XAG.

## Use XAG Counts, Not AIG Counts

An AND-inverter graph (AIG) charges three AND nodes for every XOR, so AIG size is the wrong cost function and XAG size is the right one.
Counts for AIGs, standard cells, LUTs, or total gates have no fixed conversion to this metric.

## Synthesize Small Functions Directly

Every four-input scalar function needs at most 3 ANDs, and every five-input scalar function needs at most 4.
Direct synthesis is practical through roughly six inputs; above that, decompose or rewrite bounded cuts.
For multiple outputs, synthesize jointly so they can share products.

## Factor Quadratics by Polar Rank

For a quadratic Boolean function $f$, let $B_f$ be its polar matrix: the symmetric, zero-diagonal matrix whose $(i,j)$ entry for $i\ne j$ is the coefficient of $x_ix_j$ in the ANF.
Its rank is even, and symplectic elimination emits a construction with $\operatorname{rank}(B_f)/2$ products.
Thus it emits two products for $x_1x_2+x_3x_4$ and one for $x_1x_2+x_1x_3=x_1(x_2+x_3)$.
For vector outputs, synthesize jointly so outputs can share products.

## Free AND Gates from Don't Cares

A two-input AND becomes affine if any input pattern is unreachable: replace it by $a+b+1$, $a$, $b$, or $0$ when $(0,0)$, $(0,1)$, $(1,0)$, or $(1,1)$ is excluded.
Prove unreachability with SAT/SMT against all constraints and prover-controlled values, then verify the whole rewritten circuit.
An honest witness generator never emitting the pattern is not a proof of a relational don't-care.

## Redundancy Removal, Retargeted at Products

Retarget redundancy removal to maximum fanout-free cones and accept only a strict AND-count reduction.
Track affine relations such as $a\ne b$, not only fixed values, because XOR has no controlling value and stops ordinary AIG implication.
Delete hazard-only consensus logic immediately because constraint evaluation has no glitches.

## XOR Bi-Decomposition Comes First

For a partition $f(X)=h(g_A(X_A,X_C),g_B(X_B,X_C))$, test XOR glue first because it is free; AND and OR glue each cost one product.
With disjoint supports, optimize both halves independently and add their AND counts.
Reject a legal decomposition unless it lowers the total product count because support size and wiring are free.

## Ashenhurst-Curtis Under an AND Budget

Use Ashenhurst-Curtis charts to replace a bound input set by $k$ interface functions when the chart has at most $2^k$ compatibility classes.
Interface width is free, so choose any affine encoding of those classes that minimizes $MC(G)+MC(H)$.
Enumeration is exponential and decomposition proves representability, not savings; accept only a lower total AND count.

## Decision Diagrams Price One Product per Node

Shannon, positive Davio, and negative Davio nodes each give a one-product construction, and a Davio node is free when its Boolean derivative is constant.
Use functional or Kronecker diagrams as construction fallbacks, with internal-node count as an AND upper bound.
The bound can be poor and multiplication has exponential BDD size, so prefer factoring or cut synthesis for arithmetic functions.

## Synthesize Outputs in Sequence, Then Permute Them

Build outputs sequentially while retaining all products, try several output orders, and keep the cheapest shared network.
Outputs differing by an affine form can reuse the same nonlinear core.

## The Windowed Rewriting Loop

Above the exact-synthesis frontier, alternate three bounded passes.
Rewriting replaces a small cut by a searched XAG up to free affine maps; resubstitution expresses a node using existing signals and don't-cares; refactoring resynthesizes a fanout-free cone.
Accept by whole-network AND count, then depth, and prove equivalence after each accepted rewrite.
Use several structurally different seeds because the loop is local and non-monotone; stop when a full pass yields no improvement or the runtime budget expires.

## Keep Exact Synthesis Local

Encode $k$ abstract AND gates with arbitrary affine fan-ins, constrain their truth-table values with SAT, and search $k=0,1,\ldots$ until SAT.
Use care masks and shared multi-output synthesis when the specification permits them, but keep exact windows near six inputs and decompose larger functions.
CEGAR may start with only selected cared truth-table rows, but every candidate still needs exhaustive checking.
Do not import AIG fence encodings mechanically because an XAG input is an arbitrary affine form rather than one direct predecessor.

## Reference AND Counts

Every figure here is an AND count over (AND, XOR, NOT).

| function | AND gates | status |
|---|---:|---|
| n-bit two-operand addition modulo $2^n$ | $n-1$ | ripple construction with discarded top carry |
| n-bit two-operand addition with carry-out | $n$ | ripple construction |
| n-bit subtraction modulo $2^n$ / with borrow-out | $n-1$ / $n$ | affine reduction to addition |
| n-bit unsigned less-than | $n$ | final-borrow construction |
| n-bit equality output | $n-1$ | product of affine bit equalities |
| conditional rotation by $d$ | $n-\gcd(n,d)$ | factorization of $T-I$ |
| dot product of two n-bit vectors | $n$ | direct products and affine sum |
| Hamming weight or Hamming distance of n bits | $n-HW(n)$ | popcount construction, with $HW(n)$ the binary Hamming weight of $n$ |

Thus a 32-bit popcount costs 31 products and a 7-bit popcount costs 4.
Published primitive counts come from different circuit lineages, so compare before and after within one lineage rather than mixing baselines.
