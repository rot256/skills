Research + search task for a ZK circuit optimization competition. This one is about the GF(2) cost model ONLY — do not mix in large-prime-field techniques, they do not transfer.

Do NOT do cost accounting, do NOT compute lower bounds or feasibility tables. Find
CONSTRUCTIONS with concrete AND-gate counts, and cite real sources you fetched.

## The GF(2) cost model

The field is F_2. Every constraint row must literally have the shape

    var_k  -  A * B ,      A and B affine over F_2

and the t-th row's output variable must be exactly variable n_0 + t — i.e. **each row
produces a fresh output variable, in sequence.** That sequencing requirement is the
key restriction: you cannot write a free-standing affine assertion, and the output of
a row cannot appear inside a multiplicand of that same row.

Consequences:
- everything F_2-linear is FREE: XOR, NOT, rotations, shifts, XOR-with-constant
- score is essentially 2 x (number of AND gates)
- the design question is always "which PRODUCT do I witness", never "which value do I
  pin". E.g. a full-adder carry is maj(x,y,z) = (x+z)(y+z) + z — one product, and the
  sum x^y^z is free.

## The two challenges

(A) gf2-sha256-compress-canonical — the SHA-256 compression function
(B) gf2-k12-compress-canonical — KangarooTwelve, i.e. Keccak-p[1600, 12 rounds].
    Note theta, rho, pi, iota are ALL FREE here (F_2-linear); only chi costs, at one
    AND per bit, 1600 per round, 12 rounds.

## What to research

1. **Best published multiplicative complexity (AND-gate count) constructions.**
   Hunt for the actual records and the constructions behind them:
   - SHA-256: the lowest published AND-gate counts. Look at the MPC/FHE/garbled-circuit
     literature where AND count is THE metric — Boyar–Peralta's circuit minimization
     work, the "Bristol Fashion" circuit collection (and its successors), the
     TinyGarble / ABY / MP-SPDZ circuit libraries, and any paper claiming an improved
     AND count for SHA-256. Report the number and the technique.
   - Keccak chi: chi is 5 bits in, 5 bits out, y_i = x_i XOR (NOT x_{i+1} AND x_{i+2}).
     Naively 5 ANDs per 5-bit row. **Is 5 optimal?** Search for the multiplicative
     complexity of the Keccak chi S-box — this is a well-studied 5-bit S-box and
     there are published MC results for it. If MC(chi) < 5, that is an enormous win
     (12 rounds x 320 rows x saving). Report the exact published MC and, if it is
     below 5, THE ACTUAL CIRCUIT.
   - Also look for the MC of the AES S-box, the multiplicative complexity tables for
     small S-boxes (Boyar–Peralta, Stoffelen's SAT-based MC results, Courtois et al.),
     since the methodology transfers.

2. **Adders.** The dominant cost in SHA-256 over GF(2) is the modular additions.
   Research the lowest-AND-count constructions for:
   - 2-operand n-bit addition mod 2^n (ripple = n-1 ANDs; is there better? the
     answer relates to the ANF degree bound MC >= deg - 1)
   - multi-operand addition (k operands, width n) — column compression / Wallace
     trees using full adders (1 AND each) and half adders. A half adder with a
     COMPILE-TIME CONSTANT operand is FREE over F_2 (both sum x^K and carry x*K are
     affine) — so constant addends should be placed to maximise free half-adders.
     Find the best known column-compression schedules and the exact AND counts.
   - Look for published "minimum AND count adder" results and for the
     Boyar–Peralta–Pornin style optimized adders.

3. **Circuit minimization TOOLS we could actually run.** Find and report concrete,
   runnable tools for AND-count minimization over GF(2):
   - SAT-based exact synthesis (Stoffelen's tool, `sboxgates`, `LIGHTER`, `PEIGEN`)
   - Boyar–Peralta heuristics implementations
   - ABC / mockturtle (the EPFL logic synthesis library has an XAG — XOR-AND-graph —
     package with explicit multiplicative-complexity-aware optimization; `mockturtle`
     has `xag_algebraic_rewriting` and MC-aware resynthesis)
   Give install/run instructions and say which is most likely to help on a
   SHA-256-sized circuit vs an S-box-sized one.

4. **The XAG viewpoint.** Represent the whole circuit as an XOR-AND-Graph and apply
   MC-preserving/reducing rewrites. Research the literature on XAG optimization for
   multiplicative complexity (there is a body of work driven by FHE and by quantum
   T-count minimization — T-count over the Clifford+T gate set is essentially the
   same metric as AND count, so the QUANTUM RESOURCE ESTIMATION literature is a rich
   and often-overlooked source of low-AND circuits for SHA-256 and Keccak. Grover
   oracle papers for SHA-256 and Keccak report exact Toffoli counts — go get them,
   those Toffoli counts ARE AND counts).
   This is likely the highest-value item on this list. Chase it.

5. **The sequencing restriction.** Given that each row must output a fresh variable
   in order and the output cannot appear in its own multiplicands, check whether any
   of the constructions you find need a rewrite to fit, and say how.

## Output

- The best published AND counts you can find for SHA-256 compression and for
  Keccak-p[1600] / chi, with source (title, authors, link) for each, and whether the
  count includes or excludes the message schedule / padding.
- The MC of the Keccak chi S-box, sourced. If below 5, give the circuit.
- Best adder constructions with AND counts.
- A list of runnable tools with commands.
- A ranked list of what to try first.

Every number must come with a source you actually fetched. If you cannot find a
number, say "not found" rather than estimating.
