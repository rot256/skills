# Catalogue of circuit-optimization techniques

> **These are starting points, not a closed list.** Every entry is a lens, not a
> recipe. The best optimization for *your* circuit is often a composition of these,
> or something not yet written down. Treat this as priming, then look for structure
> specific to your problem — and add what you discover back here.

Cost models to anchor on:
- **R1CS / QAP (Groth16, Marlin, Spartan):** cost = number of **multiplication**
  rows `(A·z)(B·z)=(C·z)`. Linear combinations are *free as inputs to a row*; a
  standalone affine equality still costs a row unless absorbed by substitution.
- **PLONKish (halo2, plonky2/3, Kimchi):** cost = rows × columns, plus an FFT /
  quotient blowup that grows with the **max gate degree**.
- **AIR / STARK:** cost = trace width × length, plus constraint degree.

The optimizer's job is to move work into whatever is free in your model and to
minimize whatever is paid.

---

## 1. Free linear combinations (R1CS)

Products cost a constraint; additions and constant-scalings are free *as the linear
combinations `A/B/C` feeding a row, or as an inlined wire definition*. A pure linear
relation that must be *asserted* on its own still costs one (degenerate) row unless
you eliminate it by substituting the defined wire wherever it is consumed. Fold all
affine work into the `A/B/C` linear combinations and **defer reductions**: accumulate
`a+b+c+d` as one field value and bit-decompose/range-check **once**, instead of per
operation. A weighted sum `3a+5b+7c` is 0 constraints; only `a·b`-style products
cost. Caveat: very long combinations densify the `A/B/C` matrices (key size, MSM
scalar work), so "free" is asymptotic. Does not transfer to PLONK's fixed-fan-in gate
(see §6). [Vitalik QAP](https://vitalik.eth.limo/general/2016/12/10/qap.html) ·
[RareSkills R1CS](https://rareskills.io/post/rank-1-constraint-system)

## 2. Multi-operand add + decompose-once

The R1CS form of §1 for modular addition: to compute `(Σ opⱼ) mod 2^w`, witness the
`w` output bits and `cw` carry bits, add booleanity, and impose **one** linear row
`Σ value(opⱼ) = value(z) + 2^w·Σ 2ⁱ cᵢ`. Chaining binary adds re-witnesses outputs
and carries every step; one multi-operand reduction does it once. Pick the **minimal
carry width**: the sum is `< n·2^w`, so `cw` bits suffice when `n ≤ 2^cw` (a 4-operand
add needs `cw=2`, not 3). Soundness lifts the field equation to ℕ only if **both
sides** stay below `p`: the operand sum is `< n·2^w`, and the witnessed RHS
`z + 2^w·carry` can reach `≈ 2^w·2^cw`, so require `p > 2^w·max(n, 2^cw)` (clean's
`p > 2^35 = 2^32·8`, with `n, 2^cw ≤ 8`). This is the bellman SHA-256 pattern and
`clean`'s `AddMod32`. [bellman sha256.rs](https://github.com/zkcrypto/bellman/blob/main/src/gadgets/sha256.rs)
· see `sha256-case-study.md`.

## 3. Carry-save / full-adder identity

For bits, `a + b + c = (a⊕b⊕c) + 2·maj(a,b,c)`. So a 3-input bit-logic step becomes
a **linear** check `a+b+c = s + 2·cy` — but it pins `s,cy` to (parity, maj) only when
**both** `s` and `cy` are constrained boolean. Booleanity of `cy` alone does *not*
force `cy = maj`; the carry-save win (witness only `cy`, feed `s = a+b+c−2cy`
downstream as an un-witnessed linear combination) is sound only because the downstream
consumer (here `AddMod32`'s bit-decomposition of the aggregate) pins the result — the
soundness lives in the *composed* circuit, not in `cy`'s booleanity. It halves the
witnesses for Σ/σ and Maj and needs char ∉ {2,3}.
[full adder = XOR + majority](https://www.electronics-tutorials.ws/combination/comb_7.html)

## 4. Single rank-1 constraint per boolean function

Assuming the inputs are already constrained boolean, put the output in a
**multiplicand** and divide by an affine form `R`: `(o + A)·R = O` ⇒ `o = O/R − A`,
which uniquely determines `o` — and, when the target is boolean, pins it to `{0,1}`
(booleanity for free) — **provided `R` is a unit in the actual field `F_p`** on every
input point (i.e. `p` divides none of the values `R` takes). Beats the degree-2
intuition: parity (degree 3) fits one constraint of this shape. Not every function
fits *this shape*: AND3 and OR3 have no such single constraint (cvc5 proves the
synthesis query `unsat` in `QF_FF` over the actual `F_p` — an exact finite-field
statement). Find coefficients by linear search over `QQ` (`scripts/synthesize.sage`);
prove correctness with cvc5 `QF_FF` (`scripts/verify.smt2`, `scripts/impossible.smt2`)
and certify across all large fields with Gröbner cofactors (`scripts/cofactors.sage`).
`clean` ships these for SHA-256:
- **XOR3:** `(o + 2a + 2b + 7c)(a + b − 4c + 1) = 6a + 6b − 24c`
- **Maj:**  `(o + a + b − 9c + 3)(a + b + 6c − 4) = −12`

**Scope your impossibility claims by the coefficient ring.** Maj has *no symmetric
encoding with small integer coefficients* (brute force confirms), which is why `clean`
uses the asymmetric `−9c`/`6c` form. But over a field a symmetric encoding *does*
exist — e.g. `(o − s/4)(9 − 6s) = −3s/4` with `s = a+b+c` (verified on all 8 points;
needs char > 3). "Asymmetry unavoidable" is true for integer coefficients, false over
`F_p`. State which ring you searched.

Boolean gadget identities to keep handy: AND `ab`; XOR2 `a+b−2ab`; CH `e(f−g)+g`;
MAJ `ab+ac+bc−2abc`; select `a?b:c` = `c+a(b−c)`. [halo2 tips](https://zcash.github.io/halo2/user/tips-and-tricks.html)

## 5. CRT / RNS decomposition, foreign-field arithmetic

Represent big-integer / non-native values as small limbs. To prove `a·b ≡ r (mod p)`
in native field `n`: write `a·b = q·p + r` and check it **mod n** (native, cheap) and
**mod 2^t** (limbs, cheap). CRT pins the full integer equality only if the signed
difference `D = a·b − q·p − r` is forced into a window narrower than the CRT modulus
`n·2^t` — which requires **range-checking `a,b,q,r`** (so `|D| < n·2^t`), not merely
`(p−1)² < n·2^t` (that bounds `a·b` alone, not `q·p+r` or the sign). Getting this
bound wrong is a classic soundness hole. It replaces one gigantic integer identity
with two narrow ones. Mina/Kimchi: 256-bit
field in **88-bit limbs** → 264 bits → 3 cells, FF-mul in 2 rows; each limb gets a
range check. RNS keeps residues mod several coprime primes (cheap independent ops)
but **comparisons/range checks force an expensive exit from RNS**, so stay in RNS as
long as possible. The bound is the soundness-critical part — *prove* it (see
`sage.md`), don't assume it.
[Mina FF-mul](https://o1-labs.github.io/proof-systems/kimchi/foreign_field_mul.html) ·
[0xPARC non-native + CRT](https://notes.0xparc.org/problems/nonnative-arithmetic/) ·
[eprint 2025/695](https://eprint.iacr.org/2025/695.pdf)

## 6. Lookup arguments (plookup, LogUp, logUp-GKR, cq, Lasso)

Replace many arithmetic/boolean constraints by "is this tuple in table T?". A range
check or a *chunk* of bitwise logic collapses to one lookup — but the table size is
arity-dependent: a 2-input k-bit XOR needs a `(x,y,z)` table of size `2^(2k)`, so in
practice you chunk into small `k` (e.g. 8-bit) sub-lookups, not "one lookup" for a
full word. LogUp uses the log-derivative identity
`Σ_a 1/(X−a) = Σ_b m_b/(X−b)` (handles multiplicities). Tradeoffs:
- **plookup** O(N log N), cost tied to table size N.
- **LogUp** ~3–4× fewer committed oracles; **logUp-GKR** commits only the
  multiplicity column for M columns into one table.
- **cq** prover time **independent of table size** (after preprocessing).
- **Lasso** for m lookups into size-N table commits ~`m + N` *small* values; pay only
  for entries actually accessed; great for decomposable (SOS) tables — range checks,
  bitwise ops, big-int, even RISC-V steps.

Win only when a table replaces *many* constraints or is heavily reused. A static
indexed lookup is *not* RAM: read/write memory needs a full consistency argument
(address, timestamp, value tuples, sorted by a permutation/log-derivative argument,
plus "a read returns the last write"). [Lasso eprint 2023/1216](https://eprint.iacr.org/2023/1216)
· [cq eprint 2022/1763](https://eprint.iacr.org/2022/1763) · [logUp-GKR eprint 2023/1284](https://eprint.iacr.org/2023/1284)
· [Mina lookups](https://o1-labs.github.io/proof-systems/kimchi/lookup.html)

## 7. Bit-decomposition, range checks, and the "spread" trick

- **Pack** values as one field element; decompose only when bits are needed, and
  reuse the decomposition for *both* the range check and the logic.
- **Small-set via product of factors** (halo2): `a∈{0..4}` ⇒ one degree-5 row
  `a(1−a)(2−a)(3−a)(4−a)=0`; `a∈{7,13}` ⇒ `(7−a)(13−a)=0`. Raises gate degree
  linearly — fine for tiny sets, use a lookup for large ranges.
- **Spread / interleave** (zcash halo2 SHA-256): map a k-bit dense word to a word
  with a 0 between every bit. A lookup into the spread table *simultaneously*
  range-checks the chunk **and** returns its spread form. Adding two spread words puts
  the **XOR in even positions and the carry/AND in odd positions** — one addition
  yields both. Needs a shared 2^16-row table.

[halo2 tips](https://zcash.github.io/halo2/user/tips-and-tricks.html) ·
[halo2 table16 / spread](https://zcash.github.io/halo2/design/gadgets/sha256/table16.html)

## 8. Custom / higher-degree gates (PLONKish)

Bundle several ops into one row with a higher-degree custom gate + selectors +
rotations (referencing `w(ωX)`, the next row, needs no copy constraint). Trades
polynomial degree for fewer rows; the cost lands in the quotient polynomial: a max
**gate** degree `d` makes the **quotient** degree ≈ `d·n`, so raising `d` means more
quotient chunks / commitments and larger FFTs (the exact tolerable degree is
backend-specific — many KZG/FFT setups are tuned around a small constant times `n`).
Sweet spot degree 3–5 on KZG/FFT; multilinear/sumcheck backends
(HyperPlonk) relax the degree penalty. Folding schemes (Sangria, ProtoGalaxy) dislike
high degree. [kobi.one custom gates](https://kobi.one/2021/05/20/plonk-custom-gates.html)
· [HyperPlonk eprint 2022/1355](https://eprint.iacr.org/2022/1355)

## 9. Non-deterministic advice (compute-then-verify)

Compute the hard thing out-of-circuit and only *verify* it cheaply. Many ops are hard
forward, easy to check:
- **IsZero/inverse** (circom): hint `inv=1/in` (or 0); `out <== 1 − in·inv`,
  `in·out === 0` ⇒ `out=(in==0)` in 2 constraints, no division gate.
- **Division** `q=a/b`: witness `q`, assert `q·b === a` (and ensure `b ≠ 0`, else `q`
  is unconstrained).
- **sqrt** `r`: assert `r·r === a` (pins `r` only up to sign — add a canonicality /
  sign constraint if the root itself, not just `r²`, is used downstream).
- **Bit-decomp:** witness bits, assert booleanity + `Σ bᵢ2ⁱ === x`.

**Critical caveat — the #1 soundness bug:** every hint value that influences an output
must be *uniquely pinned* by constraints. The practical rule is to pair each `<--`
(witness assignment) with a determining `===`; the precise condition is that no
prover-chosen freedom reaches an output. (Auxiliary witnesses that provably cannot
affect any output may be left non-unique, but that is the exception — when in doubt,
pin it.) [circom witness](https://docs.circom.io/getting-started/computing-the-witness/)
· [circom comparators](https://circom.erhant.me/comparators/) ·
[zkSecurity circom pitfalls](https://blog.zksecurity.xyz/posts/circom-pitfalls-2/)

## 10. Solver- and algebra-aided synthesis & verification

- **SMT over finite fields** to *find* minimal encodings of small functions and to
  *detect under-constraint* (ask for two distinct witnesses agreeing on I/O; a model
  is a soundness counterexample). Tools: cvc5/Z3, AC4, zkFuzz, Veridise's checkers.
- **Gröbner / ideal methods** to prove outputs are uniquely determined and to extract
  soundness cofactors (see `sage.md`). Both blow up with degree/variables — apply
  per-gadget, not whole-circuit.

[SMT over finite fields, arXiv 2305.00028](https://arxiv.org/pdf/2305.00028) ·
[Veridise under-constrained detection](https://veridise.com/wp-content/uploads/2025/01/Automated-Detection-of-Underconstrained-Circuits-for-Zero-Knowledge-Proofs.pdf)

## 11. More moves worth reaching for

Shorter entries; each is a full topic on its own.

- **Folding / incremental proving** (Nova, SuperNova, HyperNova, ProtoStar): fold many
  instances of a step circuit into one *relaxed* R1CS instance, so a long repeated
  computation costs ≈ one step's proving per step plus a cheap fold, not a monolithic
  proof. Penalizes high-degree gates unless the scheme handles them. [Nova](https://eprint.iacr.org/2021/370)
- **Montgomery / Barrett reduction in-circuit:** don't compute `mod m` directly —
  witness the quotient/correction and verify `x − q·m = r` with `r` range-checked
  into `[0,m)`; keep values in Montgomery form to make repeated modmul cheap. Same
  hint-and-check shape as §9, with the bound discipline of §5.
- **Mux / select chains:** binary select `y + s·(x−y)` (1 mult). Multi-way: one-hot
  selectors `sᵢ` with `Σsᵢ = 1` and `Σ sᵢ·vᵢ`, or a lookup for large fan-in. Avoid
  nested `IsEqual` ladders.
- **Lazy / redundant-limb arithmetic:** carry values in signed or oversized
  ("slack") limbs and **defer carry propagation**, range-checking only at boundaries
  where overflow could occur — fewer normalizations in long limb computations.
- **Batched range checks:** prove many bounds at once via running-sum range arguments
  or chunked lookups; pack several small bounded values into one field element (with a
  combined range check) when their total bit-width stays under `log₂ p`.
- **Batched inversion (Montgomery's trick):** invert `n` field elements with **one**
  inverse plus `3(n−1)` mults via prefix products — turns per-element division into a
  single hinted inverse verified once.
- **Random linear combination (RLC) batching:** collapse many equalities `aᵢ = bᵢ`
  into one check `Σ αⁱ(aᵢ − bᵢ) = 0` with a verifier/Fiat-Shamir challenge `α` (mind
  the soundness error `deg/|F|` and that `α` must be sampled *after* the values are
  committed).
- **ECC scalar multiplication:** fixed-base **windowing** and **wNAF** to cut additions;
  **GLV** endomorphism splitting to halve the scalar bit-length; complete addition
  formulas to avoid special-case branches; batch the affine inversions (above).
- **Degree reduction:** when the quotient blowup dominates (PLONK/AIR), *introduce
  intermediate witnesses* to split a high-degree gate into several low-degree ones —
  the inverse trade of §8, made when rows are cheaper than degree.

## 12. Primitive-specific notes

- **SHA-256:** R1CS ~25k–30k constraints/compression (figures vary with what's
  counted); halo2 spread implementation ≈2,099 rows with a shared 2^16 table.
  See `sha256-case-study.md` for the `clean` R1CS reductions.
- **Keccak:** sparse-representation trick (bit ops become base-b additions, reduced by
  a parity lookup); 8-bit XOR table does 8-bit XOR in one constraint; usually a
  separate circuit linked by lookups. [PSE sparse trick](https://hackmd.io/@pse-zkevm/Byvsth4xY)
- **Poseidon:** HADES = full rounds wrap **partial** rounds (S-box on one element) →
  far fewer nonlinear constraints; S-box `x^5`. PlonK-specific arithmetization tricks
  cut up to −70% constraints; Poseidon2 lightens linear layers.
  [Poseidon eprint 2019/458](https://eprint.iacr.org/2019/458.pdf) ·
  [eprint 2022/462](https://eprint.iacr.org/2022/462) ·
  [Poseidon2 eprint 2023/323](https://eprint.iacr.org/2023/323.pdf)

---

## Where to look next (prompts for finding new tricks)

- What is *free* in my proof system, and what am I paying for per operation? Move work
  into the free part.
- Can an expensive forward computation be replaced by a cheap verification of a hint?
- Is there a representation (spread, RNS, sparse, Montgomery, redundant) in which my
  operation becomes linear or a lookup?
- Is a value over-witnessed — can a downstream consumer take it as a linear
  combination instead of a fresh witness?
- Can a solver/algebra system find a smaller encoding of this gadget than I wrote by
  hand? Can it prove mine is already minimal?
- Am I range-checking more than necessary? Can one decomposition serve two purposes?
- Does batching/folding many instances amortize a fixed cost?
