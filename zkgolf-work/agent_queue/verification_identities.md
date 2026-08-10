Deep research task for a ZK circuit optimization competition. One idea, applied across five primitives, hunting for constructions. Do NOT do cost accounting, do NOT compute lower bounds or score tables.

## The idea

In R1CS the prover supplies witnesses for free-ish; we only pay for the CHECKS.
So the largest structural lever available is:

  **The output does not have to be computed. It has to be checked.**

If there is a cheap relation that CHARACTERISES the correct answer, witness the answer
as pure advice and assert the relation. We have already exploited this once, with a
big win: for secp256k1 variable-base scalar multiplication, the output point Q is
witnessed as 9 field elements of advice, and soundness comes from a lattice relation
(u1 P + u2 phi(P) + v1 Q + v2 phi(Q) = O together with a congruence on the
coefficients and a nonvanishing condition) checked by a single 4-scalar
multi-scalar-multiplication — far cheaper than computing Q.

**Your job: find more instances of this shape.** Systematically, across primitives.

## Setting

Plain R1CS over a native prime field F_r, r ~ 2^254. Score = allocations + rows.
Affine combinations FREE. Each row is one product. No lookups, no custom gates, no
random challenges (so NO Fiat–Shamir, NO probabilistic checks — every relation must
be a genuine identity for FIXED public coefficients). Range checks cost rows.

## The primitives to attack

1. **SHA-256** (full hash, and the compression function). The compression function's
   round update is a BIJECTION given the message word. Questions:
   - Is there a cheap relation characterising "H = SHA256(M)" other than running the
     rounds? Almost certainly not for the full hash, but look for PARTIAL versions:
     can several rounds be collapsed into one relation of higher degree that is
     cheaper than the rounds separately? The round function is
     "add, apply GF(2)-linear maps, apply Ch/Maj" — composing two rounds gives a
     relation in more variables; is the composed relation cheaper to certify than two
     separate ones? Work out the 2-round composition explicitly and say.
   - The message schedule is a LINEAR recurrence plus carries. Can the whole schedule
     be certified by ONE relation over the 64 words plus witnessed carries, rather
     than 48 separate relations? Write the identity.

2. **Keccak-f1600.** chi is invertible (it is a permutation of the 5-bit row) and its
   INVERSE has a known closed form. theta is linear and invertible. Questions:
   - Is chi^{-1} cheaper to certify than chi? Give both and compare product counts.
   - The whole round is invertible; does running some rounds backward from a
     witnessed midpoint help? Where does it stop helping?
   - theta's inverse is a dense linear map — is the *inverse* direction of any round
     component cheaper because of the free-affine rule? Be concrete.

3. **RSA modular exponentiation, s^65537 mod n**, n a 4096-bit variable modulus.
   - Instead of certifying 16 squarings separately, is there a single relation
     characterising "t = s^(2^16) mod n"? Consider: witness all 17 intermediate
     values, then look for a TELESCOPING identity, or a relation over a polynomial
     ring encoding all 16 squarings at once.
   - Fermat/Euler-style relations need the factorization (unavailable). But: are
     there identities involving only n, s, and the intermediates that certify the
     chain more cheaply than 16 separate quotient certificates? Consider certifying
     the chain modulo an auxiliary structured modulus and separately bounding.

4. **secp256k1 fixed-base scalar multiplication.** We have the lattice trick for
   VARIABLE base. For FIXED base the generator is a constant, so:
   - is there a cheaper verification identity specific to the fixed base? E.g. can
     the lattice relation degenerate because one of the points is constant?
   - Elliptic nets / division polynomials: kP can be characterised by an elliptic
     divisibility sequence recurrence. For a FIXED base the initial terms are
     constants. Give the recurrence, the number of F_p multiplications per bit, and
     the point-recovery formula. This may be a genuinely new formulation for us.
   - Pairing-based check: e(P, Q') = e(Q, P')-style relations require a pairing-
     friendly curve; secp256k1 is not. Confirm or refute concretely (embedding
     degree of secp256k1) and drop it if dead.

5. **Cross-cutting: what makes a good verification identity?** Write down the general
   recipe you extract. In particular characterise when witnessing an answer + checking
   is cheaper than computing: it needs (a) the answer to be describable in few field
   elements, (b) a relation of low degree, (c) no expensive range/canonicality
   obligations on the witnessed answer. Point (c) is the usual killer — witnessed
   values often need range checks that eat the saving. Say for each of your findings
   what range obligations the witnessed advice carries.

## Also research these general sources of "cheap characterisation"

- functions with efficiently checkable inverses (modular inverse: 1 row; square root;
  discrete log in a group where the check is a group law)
- permutation / sorting certificates without random challenges
- rank, determinant, and matrix-identity certificates
- resultants and elimination: replacing a chain of relations by one resultant
- "Elliptic nets" (Stange), "division polynomials", "Somos sequences" — get the actual
  recurrences and multiplication counts

## Output

For each primitive: the verification identity/identities you found (written out as
equations), the count of products needed to check them, the range/canonicality
obligations on the witnessed advice, the soundness argument sketch, and the source
(title, authors, link) for anything from the literature.

End with a ranked list, most promising first, and for each the single next step.
Be blunt about dead ends and say why they die in one sentence each. Every claim
traceable to a source you fetched or arithmetic you show explicitly.
