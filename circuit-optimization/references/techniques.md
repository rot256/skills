# Catalogue of circuit-optimization techniques

Moves that survive the choice of proof system.
R1CS-specific: `r1cs.md`.

## 1. Carry-save / full-adder identity

For bits, `a + b + c = (a xor b xor c) + 2*maj(a,b,c)`, so a 3-input bit step is the linear check `a+b+c = s + 2*cy`.
This pins `s,cy` to (parity, maj) only when **both** are constrained boolean; booleanity of `cy` alone does **not** force `cy = maj`.
Witnessing only `cy` and feeding `s = a+b+c-2cy` downstream as a linear combination is sound only because the consumer (e.g. the bit-decomposition of `r1cs.md` VIII.2) pins the result -- the soundness lives in the *composed* circuit.
Halves the witnesses for Sigma/sigma and Maj.
Needs char not in {2,3}.

## 2. CRT / RNS, foreign-field arithmetic

Represent big / non-native values as small limbs.
To prove `a*b = r (mod p)` in native field `n`: write `a*b = q*p + r` and check it **mod n** and **mod 2^t**.
CRT pins the integer equality only if `D = a*b - q*p - r` is forced into a window narrower than the CRT modulus `n*2^t` -- which requires **range-checking `a,b,q,r`** (so `|D| < n*2^t`), not merely `(p-1)^2 < n*2^t` (that bounds `a*b` alone, not `q*p+r` or the sign).
A classic soundness hole.
Mina/Kimchi: 256-bit field in **88-bit limbs** -> 3 cells, FF-mul in 2 rows, each limb range-checked.
RNS gives cheap independent ops, but comparisons / range checks force an expensive **exit from RNS** -- stay in RNS as long as possible.
*Prove* the bound (`sage.md`), don't assume it.
On R1CS the choice of limb base, the fold polynomial, and the exact bound constants are themselves the optimization -- `r1cs.md` Part IV.

## 3. Lookup arguments

Replace many arithmetic/boolean constraints by "is this tuple in table T?".
Table size is arity-dependent: a 2-input k-bit XOR needs a `(x,y,z)` table of size `2^(2k)`, so chunk into small `k` (e.g. 8-bit), not one lookup per word.
LogUp uses the log-derivative identity `sum_a 1/(X-a) = sum_b m_b/(X-b)` (handles multiplicities); Lasso pays only for entries accessed, for decomposable (SOS) tables.
Worth it only when a table replaces *many* constraints or is heavily reused.
A static indexed lookup is **not** RAM: read/write memory needs a full consistency argument (address, timestamp, value tuples, sorted by a permutation/log-derivative argument, plus "a read returns the last write").
Where lookups are unavailable or uncounted, an arbitrary table on `N` points is still only `~2*sqrt(N)` rows (`r1cs.md` I.11), and there is a proof that you cannot do much better (`r1cs.md` V.3).

## 4. Bit-decomposition, range checks, spread

- **Pack** as one field element; decompose only when bits are needed, and reuse the decomposition for *both* the range check and the logic.
- **Small set via product of factors** (halo2): `a in {0..4}` => degree-5 row `a(1-a)(2-a)(3-a)(4-a)=0`.
  Raises gate degree linearly -- tiny sets only; lookup for large ranges.
- **Spread / interleave** (zcash halo2 SHA-256): map a k-bit word to one with a 0 between every bit.
  A lookup into the spread table *simultaneously* range-checks the chunk and returns its spread form.
  Adding two spread words puts the **XOR in even positions and the carry/AND in odd positions** -- one addition yields both.
  Needs a shared 2^16 table.

## 5. Custom / higher-degree gates (PLONKish)

Bundle ops into one row with a higher-degree gate + selectors + rotations (`w(omega*X)`, the next row, needs no copy constraint).
Trades degree for rows: max **gate** degree `d` makes the **quotient** degree ~ `d*n` -> more quotient chunks/commitments, larger FFTs (the tolerable `d` is backend-specific).
Sweet spot 3-5 on KZG/FFT; sumcheck backends (HyperPlonk) relax the penalty; folding schemes (Sangria, ProtoGalaxy) dislike high degree.

## 6. Non-deterministic advice (compute-then-verify)

Compute the hard value out-of-circuit, verify it cheaply (inverse, division, sqrt, bit-decomposition).
**Soundness rule, the #1 ZK bug:** every hint value reaching an output must be uniquely pinned by constraints -- pair each `<--` with a determining `===`; the precise condition is that no prover-chosen freedom reaches an output.
(sqrt pins only up to sign; add a canonicality constraint if the root itself is used downstream.)
Taken to its limit this replaces the computation entirely: witness the answer and assert a verification identity (`r1cs.md` II.13).

## 7. Solver- and algebra-aided methods

- **SMT over finite fields** (cvc5 `QF_FF`) to *find* minimal encodings and *detect under-constraint* (ask for two distinct witnesses agreeing on I/O; a model is a counterexample).
- **Groebner / ideal methods** to prove outputs uniquely determined and extract soundness cofactors (`sage.md`).
  Both blow up with degree/variables -- per-gadget, not whole-circuit.

## 8. Further moves

- **Montgomery / Barrett in-circuit:** don't compute `mod m`; witness the quotient/correction and verify `x - q*m = r` with `r` range-checked into `[0,m)`.
  Hint-and-check (section 6) with the bound discipline of section 2.
- **Lazy / redundant-limb arithmetic:** carry signed or oversized ("slack") limbs and defer carry propagation, range-checking only at overflow boundaries.
- **Batched inversion (Montgomery's trick):** invert `n` elements with **one** inverse + `3(n-1)` mults via prefix products.
- **RLC batching:** collapse equalities `a_i = b_i` into `sum_i alpha^i*(a_i - b_i) = 0` with a Fiat-Shamir `alpha`;
  soundness error `deg/|F|`, and `alpha` must be sampled **after** the values are committed.
- **ECC:** GLV endomorphism splitting halves the scalar bit-length; windowing/wNAF cut additions; batch the affine inversions (above).
- **Degree reduction:** introduce intermediate witnesses to split a high-degree gate into low-degree ones -- the inverse of section 5, when rows are cheaper than degree.
