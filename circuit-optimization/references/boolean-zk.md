# Boolean Optimization for Zero-Knowledge Circuits

## Repack for Binary-Native Word Systems

Charge committed words and each native nonlinear word-constraint class, including class-specific padding.
Repack a bit circuit before pricing it because one word AND is not one scalar AND and shifted XOR operands may be absorbed into a native constraint.
Measure the compiled allocation tuple rather than the sum of raw constraints: independently padded ZERO, word-AND, integer-multiply, binary-field-multiply, and committed-word domains can have different cliffs.
Prefer rewrites that eliminate a constraint class or cross one of its padding boundaries; replacing many word ANDs by an integer or binary-field multiplication can lose if it opens a new class or enlarges its domain.
Keep XOR and compatible shifts as virtual affine operands of the nonlinear relation, and flatten their cones only while operand size and shift composition remain within backend limits.
For limb-based arithmetic lookups, sweep the limb width because larger limbs reduce requests and carry chains but grow the table and can force columns into a larger tower field.
Run constant and zero propagation, common-subexpression elimination, and dead-code elimination before materializing intermediates, and do not pin a value as committed unless a public output, chip call, or later relation observes it.
Track distinct shifted operands and witness-evaluation instructions when they dominate, while treating scratch-slot pooling as a memory optimization rather than a proof-cost reduction.
Treat large affine layers as free only from nonlinear constraints, since materialized words, memory traffic, and prover evaluation may still cost.
For proof systems whose scalar field is $\mathbb F_{2^k}$, use `binary-extension-fields.md` to price native products, towers, basis changes, and bit-expanded fallbacks.

## Witnessed Compute-Then-Check

Replace deterministic evaluation with prover-supplied output and advice only when a cheaper identity constrains every observable result.
For inversion with $x\ne0$, witness $y$ and check $xy=1$, which costs one multiplication plus the cost of enforcing the precondition.
If zero is allowed, constrain the selected convention completely; for $\operatorname{inv}(0)=0$, a zero flag must force both the zero case and $y=0$.
In characteristic two, `binary-extension-fields.md` "Constrain Inverse-or-Zero Without a Flag" gives a flag-free pair of relations when cubic checks are cheap.
For division, square roots, and other multivalued operations, constrain exceptional inputs and select a canonical result whenever the result is observable.
For bit or limb decompositions, range-check every part and reconstruct the source, since reconstruction alone permits field-valued parts.
Compare the checker plus all domain and routing constraints against direct evaluation.

## Relational Don't-Cares

Simplify a local pattern only if the circuit constraints exclude it for every satisfying witness, including disabled rows, padding rows, public inputs, and lookup multiplicities.
Prove $R(x,w)=0\Longrightarrow\neg P(x,w)$ with a whole-circuit SMT miter or algebraic certificate, then verify the rewritten circuit.
The witness generator's behavior is not a proof because a malicious prover may choose different advice.
Do not quotient witness variables by a Boolean translation invariance or affine hull unless the projection preserves every existential fiber and the lifted relation remains complete and sound.

## Native Permutation and Multiset Checks

Replace a deterministic sorting or permutation network with a witnessed ordering or a backend-native permutation or lookup argument when the full certificate is cheaper.
A witnessed permutation needs range, uniqueness, and value binding, while a sorted-list certificate needs sortedness and multiset equality.
A challenge-based multiset check may compare $\prod_i(\alpha-a_i)$ with $\prod_i(\alpha-b_i)$ after both multisets are bound.
For unequal multisets of length $N$ over $\mathbb F_q$, this check has false-accept probability at most $N/q$.
In characteristic two, do not import additive timestamp arguments mechanically; a multiplicative timestamp needs a separate nonzero constraint because zero is a fixed point.
Charge challenges, accumulators or interaction columns, boundary constraints, tuple compression, and reconciliation.
Compare the complete native-argument cost with the deterministic network, including challenges, accumulators, and boundary constraints.

## Post-Commitment Fingerprints

After binding vectors $u,v\in\mathbb F_q^N$, compare $\sum_i u_i\alpha^i$ and $\sum_i v_i\alpha^i$ for a fresh challenge $\alpha$.
If $u\ne v$, the false-accept probability is at most $(N-1)/q$.
This replaces many equality checks with one randomized identity but adds challenge phases and field operations.
Bind the claimed vectors before $\alpha$, account for aggregate error, and add range constraints when modular equality must imply integer equality.

## Freivalds Matrix-Product Checks

After binding $A$, $B$, and claimed product $C$, sample $r\in\mathbb F_q^n$ and check $A(Br)=Cr$.
One field challenge has false-accept probability at most $1/q$, while a Boolean challenge vector gives the classical bound $1/2$, and independent repetitions multiply the error probabilities.
This replaces a dense matrix product with matrix-vector products, but the actual saving depends on which matrices are fixed and which products are affine in the backend.
Charge repetitions, commitments, and challenge-dependent columns before accepting the rewrite.

## Transcript Discipline

First bind every value covered by the claim, then derive a domain-separated challenge, then commit to challenge-dependent accumulators, and finally enforce the identity and boundary conditions.
If the challenge is known before the claim is bound, the prover can choose a false claim in the check's kernel and the probability bound is void.
Account for the union of all randomized-check errors and stop when it exceeds the protocol's soundness budget.
Protect zero knowledge separately by blinding commitments and opened aggregates that would otherwise reveal witness information.

## Deferral and Co-Processors

Let a native proof system compute the Boolean-heavy component and let the outer circuit verify its proof or commitment.
Charge proof emission, native proving, commitment binding, transcript order, verification, and state reconciliation as described in `deferral.md`.
Accept deferral only when the complete path beats in-circuit execution at the target batch size without changing the required trust and soundness model.
