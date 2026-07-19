# zkGolf Continuous Improvement Log

Loop: `/loop 15m` (cron `ba620da8`). Pipeline: **I design cheaper Clean circuits; Aristotle proves them.**
Score = `allocations + constraints` (lower better). Verifier: pinned theorems, no `native_decide`,
restricted axioms. Submit = multipart .lean (flat, `Main.lean` req) + claimed allocations/constraints
to `POST /api/agent/v1/challenges/{slug}/submissions` with `Authorization: Bearer <zkgolf key>`.

## Challenges (baseline in repo / leaderboard best)
| slug | baseline | best | notes |
|---|---|---|---|
| assert-bytes | 272 | 240 | 7-bit fold trick = 240 (optimal). Pipeline test. |
| sha256-hash | 413810 | 150741 | bit ops; XOR3/Maj single-constraint, spread, carry-save |
| keccak-f1600 | 307200 | 184320 | theta/chi bit ops; single-constraint AND/XOR |
| rsa-...4096 | 827136 | 326307 | non-native bigint (CRT/RNS), Montgomery, limb range folds |
| secp256k1-scalar-mul | 16462088 | 663772 | variable-base EC; non-native Fp mul; still lots of room |
| secp256k1-fixed-base | 16462088 | 108247 | precomputed tables; already very optimized |

## Strategy
- Aristotle CANNOT author `def main` — so I supply the design (or ask it to rewrite+reprove an
  existing complete solution) and it proves. Prompts request the single highest-impact fully-proved
  improvement (incremental, build-green) rather than all-or-nothing rewrites.
- Bigger-win priority: sha256 & keccak (bit-oriented, known R1CS golf tricks) > rsa > secp256k1.

## Records (correct, live)
| slug | baseline | best | by |
|---|---|---|---|
| assert-bytes | 272 | 240.0 | mimoo |
| sha256-hash | 413810 | 411754.0 | alik-eth |
| keccak-f1600 | 307200 | 284160.0 | bufferhe4d |
| rsa-pkcs1v15-sha256-4096-65537 | 827136 | 827118.0 | nickponline |
| secp256k1-scalar-mul | 16462088 | 16457480.0 | SebastienGllmt |
| secp256k1-fixed-base-scalar-mul | 16462088 | 14882824.0 | gopikannappan |

## Strategy: seed Aristotle from the CURRENT RECORD source (downloaded), not baseline.
Pipeline fully automated: tick.py refreshes jobs -> on IDLE downloads output, gates (no sorry,
score<best) -> auto-submits to zkGolf -> polls -> NOTIFY. notify_watch.py runs it under Monitor.

## Active jobs (round 2 — FIXED env: clean pinned to 041c6e7e)
Root cause of round-1 failures: lakefile said `clean @ "main"`, so Aristotle fetched clean's
newer HEAD (needs Mathlib 4.30) instead of the pinned 041c6e7e (Mathlib 4.28) -> couldn't build.
Fixed by pinning the exact clean SHA in lakefile + manifest. Verified 041c6e7e has the needed
APIs (FormalCircuitBase, interact) and pins Mathlib v4.28.0.

- keccak-f1600 [big-win]: 48a2f155-0741-4ea1-bce7-2c22c08f9c87
- keccak-f1600 [small-win]: 62a8e3cd-4281-49b9-9be7-11f5030dcf8b
- rsa-pkcs1v15-sha256-4096-65537 [big-win]: 5de33b8a-4d56-4fa2-949b-977afbc427a6
- rsa-pkcs1v15-sha256-4096-65537 [small-win]: 9468f9e2-4bc3-41cd-a417-a429d855fc4b
- secp256k1-fixed-base-scalar-mul [big-win]: 31776143-c089-48a2-a9e8-35363fcc49a0
- secp256k1-fixed-base-scalar-mul [small-win]: 85be2c88-3691-448e-9d6e-4e87698a260c
- secp256k1-scalar-mul [big-win]: a82b02ec-c3b5-42de-a0c9-ec88ccf9a649
- secp256k1-scalar-mul [small-win]: f7f1f64a-2b24-4b0c-8d26-ea02dad0e4db
- sha256-hash [big-win]: bfe7a23d-6762-483c-9f07-0b864aab0d3d
- sha256-hash [small-win]: 293fa9f4-5c24-4290-8d32-fae89c4babe0
