# Sumcheck Prover Optimization

This file applies only when the selected proof backend uses sumcheck over multilinear polynomials.
These techniques change prover arithmetic, memory, commitments, or openings; they do not by themselves reduce the Boolean circuit or its constraints.

## Tower-Field Sumcheck

Keep Boolean witness polynomials over the base field while drawing the soundness-critical challenges from a large tower field.
When the protocol supplies an embedding lemma, fix the first variables to public tower-basis elements and use random large-field challenges only for the remaining rounds, so early folding and message work stays in smaller subfields.
Require the individual degree to fit below the relevant tower-step degree; group adjacent tower levels when necessary, and include the resulting basis width and soundness error.
Ordinary extension-field packing preserves addition but not coordinatewise Boolean multiplication, so it cannot replace this construction or an RMFE.
Price the large-field tail, basis-switching reduction, final commitment opening, and any permutation or wiring check that still uses an ordinary top-field protocol.
Stop when the relation lacks base-field coefficient structure, its degree forces an expensive tower jump, or the unoptimized subprotocols dominate.

## Small-Field Prover Scheduling

For an integrand that is a product of base- or subfield-valued multilinears, benchmark base-by-base, base-by-extension, and extension-by-extension multiplication separately.
Delay extension-valued folding for a short prefix by expanding or interpolating the product over the small field, then switch to the ordinary folding algorithm before the retained products or memory grow too large.
Choose the switch round from measured arithmetic and memory costs, the number of multiplicands, and the instance length; maximizing the small-field prefix is generally wrong.
A Toom-Cook-style prefix can reduce small-field products and memory, but only when its interpolation points are distinct and every required scaling factor is nonzero in the field.
Keep challenges in the security field and retain the final committed-polynomial opening, since this scheduler does not alter sumcheck soundness or reduce circuit constraints.
Stop when the optimized prefix loses to ordinary folding on the actual field implementation or when its precomputation and memory traffic dominate.

## Equality-Polynomial Factoring

When the integrand contains $\widetilde{\operatorname{eq}}(w,X)\prod_k p_k(X)$, factor the equality polynomial into bound-prefix, current-variable, and remaining-suffix terms.
Prove the lower-degree product sum without the current equality factor and reconstruct the transmitted round polynomial from the verifier's running claim.
Split the remaining variables into two halves and memoize their equality tables so every round reuses square-root-sized data instead of rebuilding a full suffix table.
Because $w$ contains verifier randomness, these early weights are already security-field values, so price small-by-large rather than small-by-small multiplication.
Constrain or avoid any reconstruction denominator that can vanish, and retain the final oracle opening.
Stop when equality-table work is not the bottleneck or the split's memory access outweighs the saved field multiplications.
