# Binary Extension-Field Arithmetic

This file covers arithmetic over $\mathbb F_{2^k}$ and extensions of it, separately from the scalar GF(2) XAG model in `r1cs-gf2.md` and large-prime-field arithmetic in `r1cs-fp.md`.
Always state whether one multiplication means a native $\mathbb F_{2^k}$ constraint, a multiplication in a smaller subfield, or an expanded bit circuit.

## Price the Actual Scalar Field

If the proof system is native over $K=\mathbb F_{2^k}$, a rank-$R$ multiplication algorithm for an extension of $K$ uses $R$ nonlinear $K$-products when all $K$-linear maps can be inlined.
If the backend commits intermediate words or has several nonlinear constraint classes, charge those words, classes, and their independent padding thresholds as well.
If the circuit is expanded to GF(2), reprice every $K$-product as a bit circuit and then optimize the composed network because separate submultipliers may share products.

## Keep Fixed Linear Maps Outside the Nonlinear Core

Basis changes, Frobenius maps, modular reduction, and multiplication by a fixed field element are linear over GF(2).
They cost no products in a free-affine XAG and no native products when the backend explicitly supports their GF(2)-linear coordinate maps, but Frobenius is not generally linear over the extension field itself and materialized values may still cost rows or committed words.
Choose the basis around the cheapest nonlinear multiplication tensor, then absorb the surrounding linear maps into adjacent constraints.

Compile a fixed linearized polynomial $c+\sum_i\beta_i x^{2^i}$ to one GF(2)-affine coordinate map and fuse it with adjacent fixed maps instead of materializing each Frobenius power and fixed product.
Stop when the backend cannot express that coordinate map virtually or its fan-in, evaluation, or commitment cost exceeds the decomposed form.

## Translate a Basis Without Changing the Field

For every irreducible $F(x)\in\mathbb F_2[x]$, $F(x+1)$ is irreducible and $\{1,(b+1),\ldots,(b+1)^{m-1}\}$ is a basis whenever $b$ is a degree-$m$ root of $F$.
The PB-to-translated-basis map is a fixed invertible Pascal matrix over GF(2), so it is a linear conversion rather than an AND-consuming gadget.
A multiplier that stays in the translated basis has the same nonlinear core as the original polynomial-basis multiplier; include conversion or materialization costs if either boundary uses another basis.
Do not infer that an arbitrary irreducible polynomial translates to a trinomial: the sparse form exists only when the corresponding translated polynomial is sparse.

## Separate Product Formation from Reduction

Schoolbook multiplication of two $m$-bit polynomial representatives forms $m^2$ pairwise bit products, while reduction modulo any fixed binary polynomial is GF(2)-linear.
A sparse modulus can reduce XOR count, linear depth, or materialized-word cost without reducing this $m^2$ nonlinear baseline.
Apply Karatsuba or a lower-rank multiplication tensor to the product-formation stage, then perform the chosen fixed reduction linearly.

## Use Bilinear Rank With Its Model Attached

A rank-$R$ decomposition of multiplication in $\mathbb F_{q^n}$ over $\mathbb F_q$ gives $R$ base-field products surrounded by $\mathbb F_q$-linear maps.
Symmetric rank can exceed ordinary tensor rank, so require a symmetric algorithm only when the surrounding constraint or implementation actually needs the same linear forms on both inputs.
Compare candidate decompositions after expanding them to the backend's actual scalar products and linear maps.

## Compose Towers as Upper Bounds

For positive $m,n$, bilinear complexity satisfies

$$
\mu_q(mn)\leq\mu_q(m)\mu_{q^m}(n).
$$

This prices a recursive tower construction but does not prove it optimal, since a direct multiplication tensor for the composite extension can be smaller.
Compare direct and tower decompositions after expanding them to the backend's true scalar field and fusing all surrounding linear maps.

## Pack Coordinatewise Products With an RMFE

A reverse multiplication-friendly embedding uses GF(2)-linear maps

$$
\phi:\mathbb F_2^k\longrightarrow\mathbb F_{2^e},\qquad
\psi:\mathbb F_{2^e}\longrightarrow\mathbb F_2^k
$$

such that $x\mathbin\odot y=\psi(\phi(x)\phi(y))$, packing $k$ coordinatewise bit products into one extension-field product.
Choose the extension degree by the complete rate and proof cost rather than by counting the single displayed multiplication.
An ordinary basis packing lacks this identity: it preserves coordinatewise addition but does not turn coordinatewise multiplication into extension-field multiplication.
Charge image or kernel membership, padding, commitments, modular linear checks, and decoding; RMFE packing is a relation-level transformation, not an ordinary change of basis for one field element.

## Keep Columns in the Smallest Sound Tower Field

When an arithmetization permits a declared subfield for each committed column, store bits and narrow limbs in the smallest tower level that contains them and embed them linearly into the security field only when a gate or challenge requires it.
The gate relation still lives in the declared ambient system and every subfield-membership condition remains part of soundness; this is not permission to mix incompatible field operations informally.
Packing several small-field coefficients into one larger tower symbol can remove commitment-time embedding expansion, but openings, evaluation proofs, and sumchecks still pay for the packed block.
Keep derived linear or packed polynomials virtual when their evaluator is a small composition, and materialize them when repeated queries or expression growth exceed the cost of one committed column.

## Preserve Ground-Field Extraction When Packing

Packing $2^\kappa$ coefficients from $K$ into one element of a degree-$2^\kappa$ extension $L$ is reversible for $K$-valued data, but the same basis combination is not injective on $L^{2^\kappa}$.
Therefore a verifier cannot soundly accept an extension-valued partial evaluation merely because its basis combination matches the packed claim.
Use a small-field commitment with an explicit ground-field extractor or a ring-switching check in $L\otimes_K L$, and charge its tensor representation, transpositions, sumcheck, and final opening.
Treat no-embedding-overhead as a commitment claim only; it does not imply free evaluation proofs or fewer arithmetic constraints.

## Align Polynomial Bases Across the PCS

For an additive-NTT or binary-FRI backend, choose the coefficient basis, evaluation subspaces, and folding maps so that one fold deletes the same Boolean coordinate used by the multilinear representation.
This can remove repeated permutations and basis conversions without changing the committed polynomial.
Tune skipped oracle commitments, Merkle caps, and early termination together because fewer trees can increase cleartext remainders, query count, or proximity error.

## Keep the Artin-Schreier Constant

For a quadratic extension $L=K[u]$ with $u^2+u=\beta$, compute

$$p_0=a_0b_0,\qquad p_1=a_1b_1,\qquad p_2=(a_0+a_1)(b_0+b_1).$$

Then

$$
(a_0+a_1u)(b_0+b_1u)
=(p_0+\beta p_1)+(p_2+p_0)u,
$$

which uses three nonlinear $K$-products because multiplication by fixed $\beta$ is linear.
Never replace $u^2+u=\beta$ by $u^2=u$: an idempotent in a field is only $0$ or $1$ and cannot generate a quadratic extension.

## Constrain Inverse-or-Zero Without a Flag

In characteristic two, witness $y$ and enforce

$$
x(xy+1)=0,\qquad y(xy+1)=0.
$$

If $x\ne0$, the first equation forces $xy=1$, while if $x=0$, the second forces $y=0$.
Expanded as $x^2y+x=0$ and $xy^2+y=0$, the only squarings are Frobenius maps, but the two cubic relations must still be priced under the backend's degree and commitment model.
If the input is already constrained nonzero, replace both equations by the single check $xy=1$.

## Recurse Through Quadratic Tower Norms

For $L=K[u]/(u^2+\gamma u+\beta)$ and nonzero $z=a+bu$, compute

$$
N=a(a+b\gamma)+\beta b^2,qquad
z^{-1}=N^{-1}(a+b\gamma+bu).
$$

This reduces one inversion in $L$ to one inversion in $K$, three general $K$-products, a squaring, and fixed maps, and it can recurse down a quadratic tower.
Compare this evaluator with an addition chain after pricing squaring, fixed maps, depth, and materialization in the actual backend, and prefer a witnessed inverse check when advice is allowed.
The norm is nonzero only for nonzero $z$, so handle the selected zero convention separately.

## Evaluate Inversion With an Addition Chain Only When Needed

If a nonzero input's inverse may be advice, witness $y$ and check $xy=1$ before building a deterministic exponentiation circuit.
When the inverse must be evaluated, Itoh-Tsujii reduces $x^{-1}=x^{2^m-2}$ to an addition chain for $m-1$: a chain of length $k$ uses exactly $k$ general field multiplications and $m$ squarings when every multi-Frobenius map is expanded into direct squarings.
A shortest chain minimizes only general multiplications; optimize the actual chain against the cost of Frobenius maps, materialized intermediates, depth, and reuse in the selected basis and backend.
This construction assumes $x\ne0$, so handle zero separately when the required function is inverse-or-zero.

## Test Composed Polynomials by Trace

Let $F(y)=y^m+f_{m-1}y^{m-1}+\cdots+f_0$ be irreducible over GF(2), and let $a\in\mathbb F_2$.
The composition $F(x^2+x+a)$ is irreducible exactly when $f_{m-1}+ma=1$ in GF(2).
The composition $F(x^4+x+1)$ is irreducible exactly when $m$ is odd and $f_{m-1}=0$.
Check these conditions before constructing a tower, then verify the concrete composed polynomial in Sage rather than relying on its displayed shape.

## Use Evaluation and Interpolation for Large Extensions

Lift operands to a Riemann-Roch space, evaluate them at places, multiply pointwise, interpolate the product, and evaluate it at the output place.
If output evaluation is onto and product evaluation is injective, $N_1$ degree-one places and $N_2$ degree-two places give an $N_1+3N_2$ base-field-product construction.
Reprice every degree-two and base-field product recursively, and treat curve-existence bounds as construction bounds rather than small-circuit optima.
When evaluations use multiplicity, the extra coordinates are local-expansion or Hasse coefficients in characteristic two, not ordinary derivatives, and their truncated-algebra multiplication costs must also be included.

## Use Normal Bases for Frobenius-Heavy Computations

In a normal basis, Frobenius powering is a cyclic coordinate shift, so inversion or exponentiation chains with many squarings can become substantially cheaper.
This does not make multiplication sparse: price the normal-basis multiplication tensor, conversions at the circuit boundary, and any committed permutations or dense affine forms.
Do not treat the number of nonzero entries in a published normal-basis multiplication table as an AND count, bilinear rank, or backend constraint count.
Choose a normal basis only after comparing the full multiplication-plus-Frobenius workload with polynomial and tower bases.

## Keep Equivariant Rank Separate From Product Count

An equivariant multiplication algorithm of block rank $\sigma$ in a degree-$n$ normal basis performs $\sigma n$ coefficientwise base-field products plus fixed convolutional maps.
The block rank therefore measures Frobenius-compatible structure rather than AND count, ordinary tensor rank, or proof constraints.
Use it only when the backend or implementation separately benefits from cyclic normal-basis processing, and expand every block to the actual base-field products before comparing nonlinear cost.

## Build Nonlinear Layers Around Frobenius

For an exponent whose binary expansion has Hamming weight $h$, form its Frobenius powers linearly and multiply those powers with $h-1$ general field products.
For example, $x^7=x\,x^2\,x^4$ uses two products when squaring is inlineable, but a custom degree-seven relation or sumcheck composition can have a different price.
Partial-round designs reduce active nonlinear outputs only after the proof backend's committed-column, degree, and virtual-evaluation costs are included.
Do not select the exponent or round count from arithmetic cost alone; characteristic-two subspace trails, differential behavior, and algebraic-system attacks need a field-specific security argument.

## Factor Structured Linear Layers

A matrix of the form $M=D+J$, where $D$ is diagonal and $J$ is all ones, can be evaluated by sharing $s=\sum_jx_j$ and returning $D_{ii}x_i+s$ in each lane.
In a binary extension field, every fixed diagonal multiplication is GF(2)-linear, so an inlineable backend can keep the entire layer virtual instead of materializing a dense matrix product.
Price the shared sum, fixed maps, and fanout when the backend charges virtual evaluation or committed intermediates.
Reject the factorization if the chosen structured matrix fails the permutation's diffusion or subspace-trail requirements.

## Verify the Coordinate Map Before Counting

For every proposed tower, prove that the displayed coordinates form a basis and derive each generator relation in that same basis.
Test multiplication on the basis vectors before accepting gate counts; setting both operands to the tower generator immediately detects a dropped constant in its square relation.
Only after the algebra passes should a hardware AND/XOR tally be translated into native-field constraints, bit products, or backend-specific committed cost.
