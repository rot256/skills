# Pending research agent briefs

Launched at the 20-agent concurrency cap; these were rejected and parked here.
Relaunch with the Agent tool (general-purpose) verbatim when slots free up.

- `gf2_mult_complexity.md`  — GF(2) AND-gate-count constructions for sha256-compress
  and k12-compress. Highest-value item inside it: the quantum resource-estimation
  literature (Grover oracles for SHA-256 / Keccak report exact Toffoli counts, and a
  Toffoli count IS an AND count), plus the published multiplicative complexity of the
  Keccak chi 5-bit S-box.
  CAUTION, from the verification-identities pass that has since run: GF(2) AND counts
  do NOT transfer to this cost model. XOR is free over GF(2) and costs a row over F_r,
  so every "reduce the AND count by introducing XORs" rewrite inverts sign. Measured:
  Ch = g^(e&(f^g)) is <3,3>/bit against <1,1>/bit for g + e(f-g); Maj = (a&b)^(c&(a^b))
  is <4,4>/bit against <1,1>/bit for the MAJ3 row. Price every imported gate count in
  F_r rows before believing it.

- ~~`verification_identities.md`~~ — DONE 2026-08-11. Results are in `leads.json` under
  ids: ecip-derandomized (rewritten with the derived answer),
  derandomised-multiset-product-tree, r1cs-is-a-bilinear-rank-model,
  keccak-chi-one-row-per-bit, sha256-composition-is-a-wash,
  rsa-limb-fold-and-vandermonde, elliptic-nets-dead, certifying-algorithms-frame.

RULE: do not let these decay into chat-only leads. That is what leads.json exists for.
