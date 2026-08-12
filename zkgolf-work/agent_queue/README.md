# Pending research agent briefs

Launched at the 20-agent concurrency cap; these were rejected and parked here.
Relaunch with the Agent tool (general-purpose) verbatim when slots free up.

A brief is only worth relaunching if the SLUG IT SERVES STILL HAS SLOTS. Check
tick.py SLOTS before spending one.

- ~~`gf2_mult_complexity.md`~~ — CLOSED 2026-08-12, DO NOT LAUNCH. GF(2) AND-gate-count constructions for sha256-compress
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
  WHY IT IS CLOSED, AND BOTH REASONS ARE INDEPENDENTLY SUFFICIENT. (1) Its own caution
  note above is fatal to the premise: the brief's highest-value item is importing AND
  counts from the quantum/MPC literature, and those counts are optimised for a metric
  where XOR is free and ours charges a row for it, so the imported circuits are measured
  WORSE than what we already run. Chasing a lower AND count actively moves us the wrong
  way. (2) Both slugs it serves — gf2-sha256-compress-canonical and
  gf2-k12-compress-canonical — are at 0 big-win and 0 small-win in tick.py SLOTS, so
  there is no fleet capacity to act on an answer even if one arrived.
  Reopening it requires reinstating slots AND a reason to believe some construction
  survives repricing in F_r rows. Neither is true today.

- ~~`verification_identities.md`~~ — DONE 2026-08-11. Results are in `leads.json` under
  ids: ecip-derandomized (rewritten with the derived answer),
  derandomised-multiset-product-tree, r1cs-is-a-bilinear-rank-model,
  keccak-chi-one-row-per-bit, sha256-composition-is-a-wash,
  rsa-limb-fold-and-vandermonde, elliptic-nets-dead, certifying-algorithms-frame.

RULE: do not let these decay into chat-only leads. That is what leads.json exists for.

## Aristotle research jobs (a different mechanism from the subagent briefs above)

`research/<name>/` holds a standalone Lean project stating a proof obligation, plus a
`PROMPT.md`. Dispatch with `dispatch_research.py <name>`; tracking lives in
`state_research.json`, deliberately SEPARATE from `state_jobs.json` because the watcher
owns that file and concurrent writers corrupt it.

THE COST IS A FLEET SLOT, NOT A FREE EXTRA. Aristotle caps concurrent projects per
account, and the 5th research dispatch was rejected with "You have too many projects in
progress" while the record-hunting fleet was at 20. So every research job displaces a
record-hunting job until it finishes. Dispatch deliberately.

Live: carrysave (the 3:2 carry-save identity, unblocks the 448 + 240 SHA-256 items),
rangefloor (is 2 score per bit optimal for a range check — 81.4% of RSA's cost sits at
that rate), switch1row (the one-row permutation switch and its Waksman composition),
bilinearrank (is minimal row count exactly tensor rank — decides whether the bilinear
complexity literature imports as row counts).

PARKED, blocked only by the cap: `degreepack` — does multilinear degree 3 ever pack, and
does degree 2 cap at exactly 2. Two independent derivations plus two exhaustive searches
agree it does not, but nothing is proved, and proving it permanently closes a search
space people keep re-entering. Dispatch it the moment a slot frees.
