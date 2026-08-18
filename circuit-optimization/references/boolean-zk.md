# Boolean Optimization for Zero-Knowledge Circuits

Boolean logic has no backend-independent price.
Name the arithmetization and minimize its charged tuple, with soundness first, nonlinear or committed cost second, degree and depth when globally relevant, and XOR or witness-generation work only when measured.
An AND-minimum XAG is optimal only in the restricted free-affine model of `r1cs-gf2.md`.

## Function Evaluation and Relation Checking

A deterministic circuit computes $y=f(x)$, while a ZK circuit may check an existential relation $R(x,y,w)=0$ using prover-supplied advice $w$.
The relation must be complete for allowed $(x,y)$ and sound in the form $R(x,y,w)=0\Longrightarrow(x,y)\in\mathcal R$ for every witness.
Advice helps only when checking the graph of the function is cheaper than evaluating it, after charging its range checks, routing, commitments, and witness generation.
Stop removing constraints when any remaining prover freedom can affect a public output or a later constraint.

## Backend Cost Models

These are separate models, not terms in one universal gate count.

### Restricted GF(2) XAG/R1CS

Charge one row for each fresh product and treat affine fan-in, XOR, NOT, constants, and affine outputs as free.
In this model only, AND count equals multiplicative complexity and supplies exact deterministic lower bounds.
Use `r1cs-gf2.md` for identities, constructions, synthesis, and bounds, and stop when the required deterministic XAG meets a proved lower bound.

### Binary-Native Word Systems

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
Stop when no rewrite reduces the padded constraint tuple or another measured bottleneck.

### Large-Prime-Field R1CS

Charge multiplication rows, including standalone asserted equalities when the row model requires them.
Field-linear row inputs are free, but Boolean XOR on $0/1$ values is nonlinear because $x\mathbin\oplus y=x+y-2xy$.
Deterministic GF(2) bounds do not apply to an advice-bearing prime-field relation.
Use `r1cs-fp.md`, and stop when no sound rewrite reduces rows after Boolean, range, and boundary constraints are included.

### AIR/STARK

Charge committed width times padded height, interactions, and maximum constraint degree.
Affine identities do not consume trace cells unless their values are materialized, while dependencies may consume rows and raise degree.
Binary-field AIR still has trace, padding, degree, and interaction costs rather than scalar XAG costs.
Use `air.md` and `degree.md`, and stop when the full padded trace and interaction tuple no longer improves.

### PLONKish, Lookups, and Custom Relations

Charge rows by columns, occupied gate slots, copy or permutation columns, selector groups, degree, lookups, and setup costs.
Price a Boolean operation at its marginal slot cost because XOR, AND, or a whole truth table may fit an already-paid custom gate or lookup.
Use `plonkish.md`, `gates.md`, and `degree.md`, and stop when no rewrite improves the complete layout rather than an isolated gate count.

### Optional Sumcheck Prover Cost

This is a proof-system cost profile, not a Boolean circuit optimization.
Charge committed multilinear length, individual degree, field-arithmetic classes, rounds, openings, hashing, and prover memory traffic only when the chosen backend uses sumcheck.
Circuit rewrites may reduce those inputs, but changing the sumcheck prover's evaluation schedule does not reduce the circuit or its constraints.
Use the optional `sumcheck.md` only when the selected proof backend actually uses sumcheck.

## Witnessed Compute-Then-Check

Witness an expensive result and verify a cheaper identity.
For inversion with $x\ne0$, witness $y$ and check $xy=1$, which costs one multiplication plus the cost of enforcing the precondition.
If zero is allowed, constrain the selected convention completely; for $\operatorname{inv}(0)=0$, a zero flag must force both the zero case and $y=0$.
In characteristic two, `binary-extension-fields.md` "Constrain Inverse-or-Zero Without a Flag" gives a flag-free pair of relations when cubic checks are cheap.
For division, square roots, and other multivalued operations, constrain exceptional inputs and select a canonical result whenever the result is observable.
For bit or limb decompositions, range-check every part and reconstruct the source, since reconstruction alone permits field-valued parts.
Stop when the checker plus all domain and routing constraints is no cheaper than direct evaluation.

## Relational Don't-Cares

Simplify a local pattern only if the circuit constraints exclude it for every satisfying witness, including disabled rows, padding rows, public inputs, and lookup multiplicities.
Prove $R(x,w)=0\Longrightarrow\neg P(x,w)$ with a whole-circuit SMT miter or algebraic certificate, then verify the rewritten circuit.
The witness generator's behavior is not a proof because a malicious prover may choose different advice.
Do not quotient witness variables by a Boolean translation invariance or affine hull unless the projection preserves every existential fiber and the lifted relation remains complete and sound.
Stop using a don't-care as soon as its exclusion depends only on intended execution or an unconstrained value.

## Native Permutation and Multiset Checks

Replace a deterministic sorting or permutation network with a witnessed ordering or a backend-native permutation or lookup argument when the full certificate is cheaper.
A witnessed permutation needs range, uniqueness, and value binding, while a sorted-list certificate needs sortedness and multiset equality.
A challenge-based multiset check may compare $\prod_i(\alpha-a_i)$ with $\prod_i(\alpha-b_i)$ after both multisets are bound.
For unequal multisets of length $N$ over $\mathbb F_q$, this check has false-accept probability at most $N/q$.
In characteristic two, do not import additive timestamp arguments mechanically; a multiplicative timestamp needs a separate nonzero constraint because zero is a fixed point.
Charge challenges, accumulators or interaction columns, boundary constraints, tuple compression, and reconciliation.
Stop when the native argument's complete cost is not below the deterministic network or when the transcript cannot bind the claimed values before the challenge.

## Post-Commitment Fingerprints

After binding vectors $u,v\in\mathbb F_q^N$, compare $\sum_i u_i\alpha^i$ and $\sum_i v_i\alpha^i$ for a fresh challenge $\alpha$.
If $u\ne v$, the false-accept probability is at most $(N-1)/q$.
This replaces many equality checks with one randomized identity but adds challenge phases and field operations.
Stop if the required aggregate soundness error is too large, the claimed vectors are not bound before $\alpha$, or modular equality does not imply the intended integer equality without range bounds.

## Freivalds Matrix-Product Checks

After binding $A$, $B$, and claimed product $C$, sample $r\in\mathbb F_q^n$ and check $A(Br)=Cr$.
One field challenge has false-accept probability at most $1/q$, while a Boolean challenge vector gives the classical bound $1/2$, and independent repetitions multiply the error probabilities.
This replaces a dense matrix product with matrix-vector products, but the actual saving depends on which matrices are fixed and which products are affine in the backend.
Stop when repetitions, commitments, or challenge-dependent columns erase the saving, or when the prover can choose the claim after seeing $r$.

## Transcript Discipline

First bind every value covered by the claim, then derive a domain-separated challenge, then commit to challenge-dependent accumulators, and finally enforce the identity and boundary conditions.
If the challenge is known before the claim is bound, the prover can choose a false claim in the check's kernel and the probability bound is void.
Account for the union of all randomized-check errors and stop when it exceeds the protocol's soundness budget.
Protect zero knowledge separately by blinding commitments and opened aggregates that would otherwise reveal witness information.

## Deferral and Co-Processors

Let a native proof system compute the Boolean-heavy component and let the outer circuit verify its proof or commitment.
This bypasses deterministic multiplicative complexity because it changes the checked relation, not because gates disappeared for free.
Charge proof emission, native proving, commitment binding, transcript order, verification, and state reconciliation as described in `deferral.md`.
Stop when the complete deferred path does not beat in-circuit execution at the target batch size or weakens the required trust and soundness model.

## Lower-Bound Scope

Deterministic GF(2) multiplicative complexity lower-bounds only interfaces that require an explicit XAG with free affine operations and no independent advice or native relation.
It does not automatically lower-bound prime-field advice relations, AIR certificates, word constraints, lookups, custom gates, randomized arguments, or deferred proofs.
For those systems, prove a lower bound for the allowed checker relation and witness model.
Record the model beside every bound and stop claiming optimality outside it.

## Review Checklist

- Name the backend and its charged tuple.
- Separate deterministic evaluation from existential checking.
- Include advice, domain, boundary, padding, lookup, routing, and reconciliation costs.
- Prove every relational don't-care against all satisfying witnesses.
- Bind claims before deriving randomized-check challenges.
- Track aggregate soundness error and zero-knowledge leakage.
- Minimize nonlinear or committed cost first, and report XOR cost separately when it is measured.
