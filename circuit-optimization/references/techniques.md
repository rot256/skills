# Catalogue of circuit-optimization techniques

Lenses, not recipes. The wins are usually a composition of these or structure specific
to your circuit; add what you discover.

## 1. Free linear combinations (R1CS)

Products cost a row; affine combinations are free *as the `A/B/C` inputs to a row, or as
an inlined wire definition*. A standalone asserted affine equality still costs one
(degenerate) row unless eliminated by substitution. Defer reductions: accumulate
`a+b+c+d` as one field value and bit-decompose/range-check **once**, not per operation.
Caveat: long combinations densify the `A/B/C` matrices (key size, MSM scalar work), so
"free" is asymptotic. No analogue in PLONK's fixed-fan-in gate (§8).

## 2. Multi-operand add, decompose once (R1CS)

For `(Σ opⱼ) mod 2^w`: witness the `w` output bits and `cw` carry bits, add booleanity,
and impose **one** linear row `Σ value(opⱼ) = value(z) + 2^w·Σ 2ⁱ cᵢ`. Chaining binary
adds re-witnesses outputs and carries each step; one multi-operand reduction does it
once. Minimal carry width: the sum is `< n·2^w`, so `cw` bits suffice when `n ≤ 2^cw`
(a 4-operand add needs `cw=2`). The field equation lifts to ℕ only if **both sides** stay
below `p`: the operand sum is `< n·2^w`, the witnessed RHS reaches `≈ 2^w·2^cw`, so
require `p > 2^w·max(n, 2^cw)` (clean's `AddMod32`: `p > 2^35`, with `n, 2^cw ≤ 8`).

## 3. Carry-save / full-adder identity

For bits, `a + b + c = (a⊕b⊕c) + 2·maj(a,b,c)`, so a 3-input bit step is the linear check
`a+b+c = s + 2·cy`. This pins `s,cy` to (parity, maj) only when **both** are constrained
boolean; booleanity of `cy` alone does **not** force `cy = maj`. Witnessing only `cy` and
feeding `s = a+b+c−2cy` downstream as a linear combination is sound only because the
consumer (e.g. §2's bit-decomposition) pins the result — the soundness lives in the
*composed* circuit. Halves the witnesses for Σ/σ and Maj. Needs char ∉ {2,3}.

## 4. Single rank-1 constraint per boolean function

Inputs already boolean: put the output in a **multiplicand** over an affine form `R`:
`(o + A)·R = O` ⇒ `o = O/R − A`, uniquely determined — and pinned to `{0,1}` when the
target is boolean (booleanity for free) — **provided `R` is a unit in `F_p`** on every
input point. Beats the degree-2 intuition: parity (degree 3) fits one such constraint.
Not every function fits *this shape*: AND3 and OR3 do not (cvc5 proves the synthesis
query `unsat` in `QF_FF`). Search coefficients over `QQ` (`scripts/synthesize.sage`);
prove with cvc5 (`scripts/verify.smt2`, `scripts/impossible.smt2`); certify across all
large fields with Gröbner cofactors (`scripts/cofactors.sage`). clean's SHA-256:
- **XOR3:** `(o + 2a + 2b + 7c)(a + b − 4c + 1) = 6a + 6b − 24c`
- **Maj:**  `(o + a + b − 9c + 3)(a + b + 6c − 4) = −12`

**Scope impossibility by the coefficient ring.** Maj has no symmetric *small-integer*
encoding (brute force), which is why clean uses the asymmetric form — but a symmetric
encoding exists over a field: `(o − s/4)(9 − 6s) = −3s/4` with `s = a+b+c` (char > 3).
"Asymmetry unavoidable" holds for integer coefficients, fails over `F_p`.

## 5. CRT / RNS, foreign-field arithmetic

Represent big / non-native values as small limbs. To prove `a·b ≡ r (mod p)` in native
field `n`: write `a·b = q·p + r` and check it **mod n** and **mod 2^t**. CRT pins the
integer equality only if `D = a·b − q·p − r` is forced into a window narrower than the
CRT modulus `n·2^t` — which requires **range-checking `a,b,q,r`** (so `|D| < n·2^t`), not
merely `(p−1)² < n·2^t` (that bounds `a·b` alone, not `q·p+r` or the sign). A classic
soundness hole. Mina/Kimchi: 256-bit field in **88-bit limbs** → 3 cells, FF-mul in 2
rows, each limb range-checked. RNS gives cheap independent ops, but comparisons /
range checks force an expensive **exit from RNS** — stay in RNS as long as possible.
*Prove* the bound (`sage.md`), don't assume it.

## 6. Lookup arguments

Replace many arithmetic/boolean constraints by "is this tuple in table T?". Table size is
arity-dependent: a 2-input k-bit XOR needs a `(x,y,z)` table of size `2^(2k)`, so chunk
into small `k` (e.g. 8-bit), not one lookup per word. LogUp uses the log-derivative
identity `Σ_a 1/(X−a) = Σ_b m_b/(X−b)` (handles multiplicities); Lasso pays only for
entries accessed, for decomposable (SOS) tables. Worth it only when a table replaces
*many* constraints or is heavily reused. A static indexed lookup is **not** RAM:
read/write memory needs a full consistency argument (address, timestamp, value tuples,
sorted by a permutation/log-derivative argument, plus "a read returns the last write").

## 7. Bit-decomposition, range checks, spread

- **Pack** as one field element; decompose only when bits are needed, and reuse the
  decomposition for *both* the range check and the logic.
- **Small set via product of factors** (halo2): `a∈{0..4}` ⇒ degree-5 row
  `a(1−a)(2−a)(3−a)(4−a)=0`. Raises gate degree linearly — tiny sets only; lookup for
  large ranges.
- **Spread / interleave** (zcash halo2 SHA-256): map a k-bit word to one with a 0 between
  every bit. A lookup into the spread table *simultaneously* range-checks the chunk and
  returns its spread form. Adding two spread words puts the **XOR in even positions and
  the carry/AND in odd positions** — one addition yields both. Needs a shared 2^16 table.

## 8. Custom / higher-degree gates (PLONKish)

Bundle ops into one row with a higher-degree gate + selectors + rotations (`w(ωX)`, the
next row, needs no copy constraint). Trades degree for rows: max **gate** degree `d`
makes the **quotient** degree ≈ `d·n` → more quotient chunks/commitments, larger FFTs
(the tolerable `d` is backend-specific). Sweet spot 3–5 on KZG/FFT; sumcheck backends
(HyperPlonk) relax the penalty; folding schemes (Sangria, ProtoGalaxy) dislike high
degree.

## 9. Non-deterministic advice (compute-then-verify)

Compute the hard value out-of-circuit, verify it cheaply (inverse, division, sqrt,
bit-decomposition). **Soundness rule, the #1 ZK bug:** every hint value reaching an output
must be uniquely pinned by constraints — pair each `<--` with a determining `===`; the
precise condition is that no prover-chosen freedom reaches an output. (sqrt pins only up
to sign; add a canonicality constraint if the root itself is used downstream.)

## 10. Solver- and algebra-aided methods

- **SMT over finite fields** (cvc5 `QF_FF`) to *find* minimal encodings and *detect
  under-constraint* (ask for two distinct witnesses agreeing on I/O; a model is a
  counterexample).
- **Gröbner / ideal methods** to prove outputs uniquely determined and extract soundness
  cofactors (`sage.md`). Both blow up with degree/variables — per-gadget, not
  whole-circuit.

## 11. Further moves

- **Folding** (Nova, SuperNova, HyperNova, ProtoStar): fold many step instances into one
  *relaxed* R1CS — a long repeated computation costs ≈ one step's proving per step plus a
  cheap fold. Penalizes high degree.
- **Montgomery / Barrett in-circuit:** don't compute `mod m`; witness the
  quotient/correction and verify `x − q·m = r` with `r` range-checked into `[0,m)`.
  Hint-and-check (§9) with the bound discipline of §5.
- **Lazy / redundant-limb arithmetic:** carry signed or oversized ("slack") limbs and
  defer carry propagation, range-checking only at overflow boundaries.
- **Batched inversion (Montgomery's trick):** invert `n` elements with **one** inverse +
  `3(n−1)` mults via prefix products.
- **RLC batching:** collapse equalities `aᵢ = bᵢ` into `Σ αⁱ(aᵢ − bᵢ) = 0` with a
  Fiat-Shamir `α`; soundness error `deg/|F|`, and `α` must be sampled **after** the values
  are committed.
- **ECC:** GLV endomorphism splitting halves the scalar bit-length; windowing/wNAF cut
  additions; batch the affine inversions (above).
- **Degree reduction:** introduce intermediate witnesses to split a high-degree gate into
  low-degree ones — the inverse of §8, when rows are cheaper than degree.

## 12. Primitive-specific notes

- **SHA-256:** R1CS ~25k–30k constraints/compression; halo2 spread ≈2,099 rows with a
  shared 2^16 table.
- **Keccak:** sparse-representation trick (bit ops become base-b additions, reduced by a
  parity lookup); usually a separate circuit linked by lookups.
- **Poseidon:** HADES wraps full rounds around **partial** rounds (S-box on one element) →
  far fewer nonlinear constraints; S-box `x^5`. Poseidon2 lightens linear layers.
