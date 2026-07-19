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

## Active jobs (improve-on-record round 1)
- assert-bytes: 4588f3f8-9dfe-4f08-b9da-7a1293344140 [RUNNING]
- keccak-f1600: 3df118f9-2ce1-4e37-83d3-c81ad60f10e5 [RUNNING]
- rsa-pkcs1v15-sha256-4096-65537: bf17255d-451f-4c55-9e63-580c8c5c00d4 [RUNNING]
- secp256k1-fixed-base-scalar-mul: 4ad3e1df-f399-4ad3-bf37-bb35832721e0 [RUNNING]
- secp256k1-scalar-mul: adc39f3b-89bc-4412-baad-cef887f1e3b1 [RUNNING]
- sha256-hash: 1b8a3e4e-d768-4b89-b06e-704be32ef390 [RUNNING]
