#!/usr/bin/env python3
import re
"""Generate prompts/ (big-win) and prompts_small/ (small-win) from targets.json."""
import json, os, glob
HERE = os.path.dirname(os.path.abspath(__file__)); os.chdir(HERE)
tg=json.load(open("targets.json"))
try: RESEARCH=json.load(open("research.json"))
except Exception: RESEARCH={}
INST={"gf2-k12-compress-canonical":"KangarooTwelveGF2","gf2-sha256-compress-canonical":"SHA256CompressGF2Canonical","sha256-hash":"SHA256","keccak-f1600":"KeccakF1600","rsa-pkcs1v15-sha256-4096-65537":"RSASSAPKCS1v15_SHA256_4096_65537","secp256k1-scalar-mul":"Secp256k1ScalarMul","secp256k1-fixed-base-scalar-mul":"Secp256k1ScalarMulFixedBase"}
IDEAS={
 "gf2-k12-compress-canonical":"Over GF(2) every element is ALREADY a bit — booleanity is FREE, so the ONLY cost is chi's multiplication. Baseline is 1600 allocs + 1600 constraints per round x 12 rounds = 38400, i.e. exactly ONE multiplication per state bit. theta/rho/pi/iota are linear over GF(2) and must stay FREE affine combinations. To beat the baseline you must beat the MULTIPLICATIVE COMPLEXITY of chi itself: chi_i = a_i + a_{i+2} + a_{i+1}*a_{i+2} over GF(2). Look for shared products across the 5-bit row, algebraic identities that compute 5 chi outputs with FEWER than 5 multiplications, and any product reusable between rounds. Also check whether the FINAL round can skip materializing intermediates.",
 "gf2-sha256-compress-canonical":"Over GF(2) bits are free of booleanity constraints; XOR/rotate/shift are FREE affine combinations. Cost concentrates in AND-gates (Ch, Maj) and in the ADDITION carries (mod-2^32 addition is NOT linear over GF(2) — the carry chain is the expensive part). Minimize AND-count: Maj = ab+ac+bc (3 muls, or 1 mul via ab+c(a+b)), Ch = c+a(b+c) is ONE mul. Use carry-save/3:2 compressors to cut the number of carry chains before a final ripple, and share subexpressions across the 64 rounds. Baseline 95904; the record is 45264 — a large structural gap, so rethink the adder.",
 "sha256-hash":"Single-constraint XOR3/Maj/Ch gadgets; carry-save multi-operand addition; fold the top bit of 32-bit range checks; keep XOR/rotations as free linear combos.",
 "keccak-f1600":"theta/rho/pi are linear XOR/rotations — keep FREE; only charge booleanity + chi's AND (chi = a ⊕ ((¬b)&c); ¬b=1-b affine; AND and XOR each one rank-1 row); iota XORs a constant.",
 "rsa-pkcs1v15-sha256-4096-65537":"Non-native bigint mul+reduce dominates: CRT/RNS or Montgomery, minimal limbs, carry-save, top-bit-fold limb range checks; exploit FIXED modulus + exponent 65537.",
 "secp256k1-scalar-mul":"Windowed double-and-add; incomplete/affine add formulas; minimal-limb non-native Fp with carry-save + top-bit-fold range checks; GLV endomorphism decomposition.",
 "secp256k1-fixed-base-scalar-mul":"Precompute window multiples of G as circuit CONSTANTS (free); signed-digit (wNAF) windows; minimal-constraint selection; carry-save non-native adds with top-bit-fold range checks.",
}
# READY-TO-IMPLEMENT WORK QUEUE. Unlike the RESEARCHED TECHNIQUES block at the end of the prompt
# (candidate ideas from the literature that must be checked against this cost model), everything here
# was DERIVED FROM THIS SOLUTION'S OWN SOURCE AND COST PROOFS, with the saving predicted from the
# record's measured primitive costs. Ordered by (confidence / effort), cheapest-and-safest first, so a
# job that only has budget for one item takes the one most likely to land.
WORKQUEUE={
 "secp256k1-fixed-base-scalar-mul": (47435, 34030, [
  ("~8000 — NEVER MATERIALISE THE ACCUMULATOR x AT ALL. THE ALGEBRA IS VERIFIED NUMERICALLY; THE BOUNDS ARE "
   "YOUR JOB","*** FIRST, WHERE THE SCORE ACTUALLY IS, READ OUT OF THIS TREE'S OWN LEAN COST PROOFS — IT IS NOT "
   "WHERE MOST JOBS LOOK. *** 638 of the 855 allocations in a chain step are range/canonicity bits: stageX is "
   "<423,425> = <4,0> limbs + <252,256> canonicity + <4,4> convolution + <66,67> quotient range + <97,98> grouped "
   "carry fold. Over 21 steps x 2 stages that is ~13,400 allocations of pure bit-pinning, about 26,900 score, "
   "*** 57%% OF THE ENTIRE CIRCUIT. THE ACTUAL MULTIPLICATIONS COST 4 ROWS EACH. *** Select12 is 9,450 (19.9%%) and "
   "is only the THIRD lever. Do not golf the selector before reading this item. *** THE PROPOSAL. *** The chain is "
   "R2: lambda_i^2 = x_{i+1} + x_i + x_{T_i}, and R1: lambda_{i+1}(x_{T_{i+1}} - x_{i+1}) + lambda_i(x_{T_i} - "
   "x_{i+1}) = y_{T_{i+1}} + y_{T_i}, with every x_T and y_T a free affine form. UNROLL R2 ALL THE WAY: x_{i+1} = "
   "sum_{j<=i} (-1)^{i-j} lambda_j^2 - sum_{j<=i} (-1)^{i-j} x_{T_j} + (-1)^{i+1} x_0. VERIFIED NUMERICALLY ON REAL "
   "secp256k1 POINTS — 50 random scalars, all 21 steps, 21 terms deep, ZERO VIOLATIONS — so every accumulator "
   "x-coordinate is an ALTERNATING SUM OF THE RAW lambda_j^2 CONVOLUTIONS plus free table reads. Two facts make it "
   "usable: THE CELL COUNT DOES NOT GROW (summing 21 convolutions coefficient-wise still leaves 2k-1 cells) and THE "
   "COEFFICIENTS GROW BY AT MOST 21x, i.e. +5 BITS. So x is carried UNREDUCED FOR THE WHOLE CHAIN and is never "
   "materialised; only the lambda_i are, and each step has ONE certificate (R1, degree 3, two convolutions under one "
   "quotient) instead of two materialisations and two certificates. *** THE ARITHMETIC AND THE BREAK-EVEN. *** "
   "Current step = 2 x [materialise 512 + cert(D=2) ~343] = 1,714. Proposed = 512 + cert(D=3, two convolutions), so "
   "IT WINS IFF THAT CERTIFICATE COSTS UNDER 1,202. II.14 prices D=2 at 214, D=3 at 454, D=4 at 1,004 at 8x32 limbs. "
   "At ~750 the total is 41,342 (-6,072); at 500 it is 36,092 (-11,322); at 1,000 only -822. PRICE THE CERTIFICATE "
   "BEFORE WRITING ANY LEAN. *** THE PRECONDITION IS HARD AND YOU MUST CHECK IT FIRST: THIS NEEDS 8x32 LIMBS. *** "
   "II.14 records that D=3 is DEAD at 4x64 because the folded position exceeds 2^253, and an independent bound "
   "agrees: at 4x64 the carried x polynomial has 7 cells of magnitude <= 4*2^128*21 = 2^134.4, and "
   "|lambda(t)|*|x(t)| at t <= 10 is about 2^233 — under 2^254 but with only ~20 bits of margin BEFORE you add the "
   "second convolution and the quotient term. At 8x32 the same computation gives about 2^204, comfortable. Also note "
   "8x32 doubles x_T's operand functionals, pushing the selector from m=7 to m=11 (450 -> 570 per window) — that "
   "cost is already included in the numbers above. *** WHY THIS IS THE RIGHT TARGET AND NOT JUST A SAVING: *** a "
   "point is determined by x plus one sign bit, 257 bits, but the chain currently spends 512 bits of advice per step "
   "for those 257 bits of information. This proposal reaches 256 plus the certificate, which IS the floor."),
  ("0 — THE -1 AT 47,413 IS SETTLED NEGATIVE, 0-FOR-3, AND tick.py NOW BLOCKS IT","*** DO NOT READ THIS AS "
   "'ROW DELETION IS BANNED' — IT IS LIVE AND PAYING. *** GroupedFlex.circuitNoTop is already in the 47,414 tree "
   "at ChainFold.lean:309 and :371 and ChainFoldCW.lean:56 and :258, with FoldLinIdent.lean discharging the "
   "obligation and GroupedFlexNoTop.lean carrying 28 references of working machinery. WHAT IS REJECTED IS ONE "
   "MORE SITE. *** THE EXACT EDIT: in ChainFoldCW.lean, theorem PairAddFold.stageO2_scw, take ll_effNT instead of "
   "ll_eff in the simp set and GroupedFlex.circuitNoTop / computableWitnessesNoTop instead of "
   "GroupedFlex.circuit / computableWitnesses at `64 gfFold posOfFold 3 vFoldL vFoldR hgvFold`. That is the "
   "WHOLE -1: cheapCost 1589 -> 1588, combCost 23754 -> 23753, Main 23754 -> 23753. Allocations do not move "
   "(localLength is 97 either way) — it deletes a CONSTRAINT only. *** IT WAS JUDGED AND REJECTED TWICE, AND "
   "THESE ARE REJECTIONS, NOT TIMEOUTS: db0c21da submitted 08:42:19Z judged 08:55:46Z, 7ab899af submitted "
   "08:50:30Z judged 09:08:24Z, plus fd50107d later the same day, ALL status=failed score=null. The "
   "zk.golf submission API has NO reason field, so do not go looking for an error string. *** THE TWO ARE ONE "
   "FACT, NOT TWO. The trees genuinely differ — one adds FoldLinIdent5.lean, the other FoldQInvW.lean, and they "
   "diverge by 56 lines in ChainFold, 110 in ChainFoldComplete, 21 in ChainFoldSound — but they are IDENTICAL to "
   "each other in exactly the four files carrying the flip and its bookkeeping (ChainFoldCW, CheapIncompleteAdd, "
   "Comb, Main). Two independent ways of discharging the LinIdent obligation, same site, both rejected. The SITE "
   "is the invariant. Static check rules out the cheap causes: zero native_decide / bv_decide / bare axiom / "
   "sorry, computableWitness present throughout. *** IT HAS BEEN REJECTED THREE TIMES OUT OF THREE (db0c21da, "
   "7ab899af, fd50107d) UNDER THREE DIFFERENT PROOF ROUTES (FoldLinIdent5, FoldQInvW, FoldQInvC1) — BUT A "
   "COMPETITOR HAS SINCE BANKED THE SAME TECHNIQUE FAMILY ON VARIABLE BASE, SO THE DIRECTION IS VIABLE AND "
   "ONLY OUR JUSTIFICATION WAS WRONG. *** tick.py now WARNS rather than blocks, so you can submit — but read "
   "the next paragraph before you do, because three slots have already gone this way. *** HOW THEY MADE IT "
   "SOUND, FROM THEIR OWN TWO FILES: *** MulModFold32TInv recovers the folded quotient as an affine "
   "expression AFTER the interpolated product is allocated and *** RETAINS ITS RANGE CHECK ***, then "
   "GroupedEqXVNoTop drops the native row because *** THE CARRY LOOP ALREADY PROVES EQUALITY OVER THE BOUNDED "
   "INTEGER REPRESENTATIVES *** — the native identity moves into the formal assumptions. THAT is the shape "
   "that works: something ELSE must already pin the bounded integer equality, and the quotient range check "
   "must survive. Our three attempts instead justified the deletion by an identity true BY CONSTRUCTION OF "
   "THE SUBSTITUTED EXPRESSION, which excludes no environments and is why the verifier threw them out. *** BANKED ON THE SEVENTH ATTEMPT — AND THE FIX WAS TO WRITE NO NEW "
   "PROOF AT ALL. THIS ITEM IS A CORRECTION OF ITS OWN EARLIER ADVICE. *** Six attempts flipped "
   "PairAddFold.stageO2_scw to GroupedFlex.circuitNoTop and were rejected, and this item previously told you the "
   "site was probably closed and that the argument shape was the defect. BOTH CLAIMS WERE WRONG. Submission "
   "a578b8f3 verified at 46,783 with the flip at exactly that site. *** WHAT THE WINNING DIFF ACTUALLY IS: FOUR "
   "LINES. *** ChainFoldSound.lean:176 went from `h1 h5 h7 h6 h8` to `h1 h5 h7 h6 (fun h => h8 <h, "
   "CrtMul.crt_linIdent env _ _ _ _ _>)`. The NoTop variant takes its assumption as a PAIR — the original "
   "hypothesis plus the LinIdent obligation — and the obligation is discharged by APPLYING crt_linIdent, A LEMMA "
   "THAT WAS ALREADY IN THE TREE AND ALREADY PROVEN, used at the sibling stageX site and at four places besides "
   "(ChainFoldComplete:408, :816, ChainFoldSound:176, :350). Add one cost lemma "
   "(costIs_foldFlexGNoTopO2, stageO2 <423,426> -> <423,425>) and the circuitNoTop swap, and that is the entire "
   "change. NO NEW MATHEMATICS. *** WHY THE FIRST SIX FAILED, AND THE GENERAL RULE TO TAKE FROM IT: *** every one "
   "of them WROTE A NEW JUSTIFICATION FILE — FoldLinIdent5, FoldQInvW, FoldQInvC1, FoldQInvW-revised, an extension "
   "of FoldLinIdent/FoldQInv, FoldLinIdent5 again — each re-proving something the tree could already prove, each "
   "defective in its own way. *** WHEN A SIBLING SITE ALREADY DOES WHAT YOU WANT, APPLY ITS LEMMA AT YOUR SITE "
   "BEFORE YOU PROVE A NEW ONE. *** Grep the tree for the obligation you are about to discharge; if a lemma of "
   "that shape exists, the job is plumbing, not mathematics. That is worth checking on every deletion of this "
   "kind, not just this one."),
  ("12404 — THE LARGEST ITEM ON THIS SLUG BY A FACTOR OF THREE","THE SQUARES TELESCOPE AT B=16. Re-derived against "
   "the live 47,435 tree: the per-window baseline is now ChainExtFold.extCost <855,860> = 1,715 (it was 1,734), the "
   "target stays 1,060, so the saving is 655 per window and 20*655 - 696 (terminal) = -12,404, landing about "
   "35,031. EVERY PIECE OF INFRASTRUCTURE THIS NEEDS IS STILL AT THE LINE QUOTED: InterpMul.lean:29 "
   "interpolatedMul_output, :170 affineW_interpolatedMul_output, Vandermonde.lean:33 cauchy_diag, :110 "
   "interp_uniqueness, FoldQuot.lean:39 foldLhs (still hard-coded to 7 positions, needs 4), :92 affine_foldLhs, "
   "Chain.lean:184 impliedY. PORT, DO NOT WRITE: the RSA tree already has the mixed-length multiply at "
   "projs/rsa-pkcs1v15-sha256-4096-65537/Solution/RSASSAPKCS1v15_SHA256_4096_65537/InterpMulX.lean — "
   "cauchy_diag_mixed:11, mulNoReduceX:91, interpolatedMulX:123. "
   "*** ONE THING THAT IS NOT A BLOCKER BUT WILL LOOK LIKE ONE: at B=16 the residue modulus is X^16 - X^2 - 977, "
   "which has NO ROOTS in F_r, so there is no crtFoldMul <4,4> shortcut at that base and the 31-position plain "
   "interpolation this item already prices IS the right cost. Do not go hunting for the rank-4 trick there. ***"),
  ("3490 — BASE 2^32, AND THE FOLD-SPLITTING QUESTION IS NOW SETTLED","MOVE THE WITNESSED LIMBS TO BASE 2^32. "
   "Re-derived per site against live costs: stageX 849 -> 700 (-150, x20), stageO2 849 -> 700 (-150), stageC1 866 "
   "-> 738 (-128, x20), stageAF and stageYF 854 -> 704 (-150 each), and Select12 450 -> 570 which is +120 x21 = "
   "+2,520 against you. Net -3,490 full-plain, -3,406 mixed-plain, about -3,868 / -3,740 once the root-eval delta "
   "is added. THE ITEM'S EXACT CONSTANTS WERE ALL RE-VERIFIED BY INDEPENDENT COMPUTATION: n = "
   "[1,2,3,4,5,6,7,8,7,6,5,4,3,2,1], K = [6840,5871,4894,3917,2940,1963,986,9], NfL[0] and NfL[7] exact, "
   "OFF_L(0) = 8431020801062 with 2^42 < OFF_L+OFF_R < 2^43 so W0 = 43 is confirmed tight, and q_max has bit-length "
   "36 so the RangeCheck width is 36. "
   "*** THE BLOCKER, NEWLY UNDERSTOOD, AND IT IS WHY stageC1's DELTA SHRANK FROM -140 TO -128: at base 2^32 the "
   "residue modulus is NOT X^8 - cFold. cFold = 2^32+977 is one digit at base 2^64 but TWO at base 2^32, so it is "
   "X^8 - X - 977, which has ONE root in F_r (factors 1,2,2,3) against X^4 - cFold's FOUR. That is exactly why the "
   "live tree gets CrtMul.crtFoldMul at <4,4> and base 2^32 cannot: the honest cost there is the full 15-position "
   "interpolation <15,15>, +22 per multiply site. That is ALREADY INSIDE the -3,490 above. Do not re-litigate it "
   "and do not expect crtFoldMul to port. ***"),
  ("918 — DELETE BOTH Canonicalize.main CALLS","THE MECHANISM IS INTACT AND EVERY LINE REFERENCE HAS MOVED, so read "
   "these rather than the old ones: delete Comb.lean:216-217 (-1,046), add back the ValidP tail at "
   "ValidP.lean:80-83 (+16 for two sites), and widen the mux at FinalAdd.lean:934 from 8 limbs to 64 bytes (+112). "
   "Net -918. canonicalizeCost is now <260,263> = 523 each (CanonicalizeCost.lean:256), and the bit decomposition "
   "has moved inside ValidPBytes.circuit at <256,260>. Both consumers already call NormalizeImplicit "
   "(ChainFold.lean:304, ChainFinishFold.lean:37) and NormalizeImplicitBytes has identical cost <252,256>. "
   "CombSound.finalAdd_assumptions is still at exactly line 714. THE CHEAP FALLBACK IS -14, NOT -24 (drop r <4,0> "
   "plus the booleanity row plus the GroupedFlex <0,2>, 7 per site over two sites). Reachability has moved too: 50 "
   "of 191 files are unreachable from Main.lean, not 60 of 196, and ChainStartFold.lean is DELETED so ignore any "
   "advice referring to it."),
  ("67 — THE CHEAPEST REAL WIN, AND HALF OF IT NEEDS NO WORK AT ALL","INVERT THE REMAINING QUOTIENTS AND DROP THE "
   "NATIVE GroupedFlex ROW. Already landed at stageO2 and stageX: those pass the affine CrtMul.crtQInv straight "
   "into RangeCheck (ChainFold.lean:39-40, :306-307), and Canonicalize's booleanity bit is likewise an affine "
   "bExpr (Canonicalize.lean:779-801). STILL WITNESSED at ChainFold.lean:166 (stageC1, x20), "
   "PairAddFoldA.lean:125 (stageAF), ChainFinishFold.lean:38 (stageYF) = 22 allocations. Plus 45 rows, one per "
   "live GroupedFlex.circuit site (1 stageO2 + 20 stageX + 20 stageC1 + stageAF + stageYF + 2 Canonicalize). "
   "*** 23 OF THOSE 45 ROWS NEED NO INVERSION WORK WHATSOEVER — at the 21 already-inverted fold sites and the 2 "
   "Canonicalize sites, L - q*P256 - T is already identically zero as a polynomial in the wires, so the native row "
   "is pure waste. Take those first. *** Note GroupedFlex.mainNoTop DOES NOT EXIST yet; GroupedFlex.main:202-205 "
   "still ends in assertZero (polyEvalExpr ...). AND IGNORE THE OLD SELF-CHECK: the allocations-versus-rows gap is "
   "113 (23,774 - 23,661), not 90, decomposed as stageO2 3 + 20x stageX 3 + 20x stageC1 2 + stageAF 2 + stageYF 2 "
   "+ 2x canon 3."),
  ("16 — SWAP routedA FOR routedT","FinalAdd.lean:927 still builds routedA with Mux.circuit (M := "
   "Chain.ChainState) at <16,16>, and there is no routedT — input.T is used raw at :930 and :931. Restoring the "
   "routed form costs +16 and deletes the 32-point mux. Unchanged by the re-derivation; the line reference is "
   "still exact."),
  ("discipline — SURVIVAL, AND EVERY COUNT IN THE OLD VERSION HAS MOVED","BUY ELABORATION HEADROOM. Current "
   "measurements against the live tree: `irreducible` in 45 of 191 solution files (was 48 of 202); 1,543 plain "
   "`by decide` (was 1,626); heaviest file still EvenTableTop.lean at 135 (was 132). THE ONE FIGURE THAT HAS NOT "
   "MOVED IS THE IMPORTANT ONE: exactly 34 uses of `decide +kernel` across all eight trees, 17 here and 17 in "
   "scalar-mul, ZERO everywhere else — so the cheap kernel-side form is still almost entirely untaken. Toolchain "
   "is still pinned at v4.28.0. THE FORBIDDEN BAND HAS NARROWED: three separate trees reached exactly 47,417 and "
   "all three failed, so the danger zone is now 47,435 -> 47,417, an 18-point gap rather than 20."),
  ("discipline — RE-DERIVE THE WHOLE COST CHAIN LAST","Whatever you change, the ledger literal to update is "
   "`<19 * 1080, 19 * 1085>` and it appears THREE times: Comb.lean:182, :187 and :437. Main.lean and combCost "
   "currently agree at 23,661/23,774 — keep them agreeing. The live chain is recodeCost <0,0> + 2x selectCost "
   "<225,225> + startCost <849,854> + <19*1080, 19*1085> + topSelectCost <11,11> + implicitScreenedCost "
   "<1311,1318> + 2x canonicalizeCost <260,263>, and it closes at exactly 47,435."),
  ("null result — THE BOUND FAMILY IS EXHAUSTED, RE-VERIFIED NUMERICALLY","EVERY LIVE GroupedFlex INSTANCE IS "
   "ALREADY AT ITS EXACT MINIMUM Wf. Recomputed from each shipped Nf tent and again from honest caps: vFoldL 98, "
   "vFoldWL 100, vFoldAL 99, vFoldYL 99, vCanonicalL 1 — shipped equals minimum in all five, both ways. Only Wf(0) "
   "is billed (G = 3 so carryLoop runs one iteration) at 2 score per bit. In particular tightening nfFoldWL at "
   "position 1 GAINS NOTHING: the honest folded cap there is 10*2^160 + 9780*2^128 + 2^99, giving OFF_L(0) = "
   "10*2^96 = 2^99 + 2^97 > 2^99, so Wf stays 100. NormalizeImplicit is 4x<63,64> = 508 and RangeCheck is <n-1,n> "
   "with certificate inversion already applied internally (RangeCheck.lean:15-19). ONE OLD CLAIM IS WRONG: there "
   "are TWO live Muxes in FinalAdd, at :927 and :934 — :931 is ChainFinishFold.circuit, not a Mux. "
   "*** AND THE RULE THIS FAMILY TAUGHT US THE HARD WAY: CHECK REACHABILITY BEFORE CHECKING ARITHMETIC. The "
   "loose-looking tents (wfFold5 = 100, wfFold2 = 102, wfWideFold = 102, vFoldPL = 102) are all DEAD CODE — "
   "vFold5L is instantiated by no GroupedFlex.circuit call at all, and its true minimum is 98, so a correct "
   "two-bit tightening there would still be worth exactly zero. ***"),
  ("null result — WINDOW WIDTH, STILL NULL BUT THE OPTIMUM HAS DRIFTED","The live selector is still the two-level "
   "7-bit-inner / 4-bit-outer shape (SelectCost.lean hot7/hot6, pairs (0,1),(2,3),(4,5),(7,8),(9,10) plus bit 6), "
   "i.e. a=7, b=4, m=11 — which is the shape the old sweep concluded was optimal, so the structural argument "
   "stands. IGNORE ITS NUMBERS THOUGH: that sweep reproduced 49,596 and the tree is 47,435. Select is now 450 "
   "(was 514, -12.5%) while the addition is 1,715 (was 1,734, -1.1%), and cheapening the SELECT faster than the "
   "ADDITION pushes the optimum toward WIDER windows — so if this is ever revisited the direction is w >= 12, not "
   "below. Still not worth a slot on its own."),
 ]),
 "secp256k1-scalar-mul": (304224, None, [
  ("~44000 — THE LAST STRUCTURAL LEVER, AND THE STEP IS MEASURED TO BE SITTING EXACTLY ON ITS FLOOR","*** THE "
   "FUSED 2A+T STEP MATERIALISES FIVE 256-BIT ELEMENTS. THE QUESTION IS WHETHER FOUR SUFFICE. *** In this model a "
   "materialised 256-bit F_q element costs 512 (2 per bit) and a degree-2 congruence certificate costs 196, with a "
   "full non-native multiply-to-new-element at 717. The step forces five materialisations (lambda1, x_S, A, x4, "
   "y4), the step floor is ~3,897 (~280,000 overall), and the local floor analysis says NOT ONE POINT IS "
   "RECOVERABLE without dropping a materialisation. So do not go looking for rows to shave inside the step — "
   "there are none. The only question is whether a 2A+T FORMULA EXISTS THAT NEEDS ONLY FOUR. That is ~44,000 and "
   "the only remaining lever below ~260,000. *** WHY IT IS PLAUSIBLE: THE TRICK ALREADY WORKED ONCE. *** The "
   "fused Eisentrager-Lauter-Montgomery double-add removes a materialisation the naive route pays — "
   "fusedStepCost <2034,2047> = 4,081 against 5,735 unfused — precisely because the intermediate y NEVER BECOMES "
   "A WIRE. Ask whether the same absorption applies a second time. *** DO THE BOUND ARITHMETIC BEFORE THE "
   "ALGEBRA. *** The degree ladder is where this lives: merging two rows into one degree-3 certificate that never "
   "materialises x_R costs 454 against 531, a gain of 290 AT 8x32 LIMBS — and at 4x64 the identical merge "
   "OVERFLOWS AND LOSES 700. Limb width decides whether the technique exists at all. *** SIX DIRECTIONS ARE "
   "CLOSED, DO NOT SPEND A SLOT ON THEM: *** batch inversion (loses 1434(n-1) at every n, because I = M = S = one "
   "reduction here so the whole I/M-ratio literature runs backwards); projective/Jacobian/co-Z/complete formulas "
   "(2.3x-5.3x worse than affine, and the real reason is algebraic degree — Jacobian Y3 is degree 13, forcing 4+ "
   "materialisations, while affine-with-witnessed-slope is degree 2); x-only differential addition (2.6x worse, "
   "AND UNSOUND — without a pinned difference the chaining relation has both x(P+T) and x(P-T) as roots, verified "
   "0/600, so a prover gets a free sign per window); wNAF and Joint Sparse Form (their advantage is AVERAGE-CASE "
   "digit sparsity and a circuit pays the WORST case — in-circuit JSF is identical to plain interleaving, and the "
   "general rule is that ANY technique whose benefit is an average over inputs is worth zero here); alternative "
   "curve models (cofactor 1 means no point of order 2/3/4, and x^3+7 has no root in F_q since q = 1 mod 3 — so "
   "Montgomery, Edwards, Jacobi quartic, Huff and Hessian are all unavailable, as is every isogenous curve); "
   "Semaev summation polynomials (S3 IS the x-only relation, S4 has 191 monomials at degree 12, S5 is degree "
   "32)."),
  ("33000 to 49000 — THE ONLY ITEM AIMED AT WHERE THE SCORE ACTUALLY IS","REWRITE THE EXCEPTION DETECTOR SO THE STEP "
   "STOPS MATERIALISING 256-BIT VALUES. MEASURE FIRST, THEN BELIEVE THIS: one glvStep costs 4,369 (<2178,2191>, GLVStepCostCW.lean:18), of which FIVE "
   "256-BIT RANGE CHECKS (Normalize32 504, ValidP 525, Normalize32 504, ValidP 525, ValidP 525) are 2,583 — 59% of "
   "the step, 160,146 across the 62 steps, AND 52% OF THE WHOLE 307,228 TREE. Folds are about 1,386 per step, "
   "VarLookup 244 (5.6%), muxes and flags 156 (3.6%). EVERY OTHER ITEM IN THIS QUEUE IS ROUNDING BY COMPARISON. "
   "Materialisation is 512 each and NOBODY HAS BEATEN THAT, but do not call it PROVED — the Bezout argument is "
   "valid only for an acceptor in A^1 and this one lives in F_r^8, so the honest proved floor is ~127. DO NOT "
   "SPEND THIS SLOT HUNTING THAT GAP (the analysis says zero margin). The lever is MATERIALISING FEWER VALUES, "
   "which "
   "means removing the exception-detection work that forces them. IDEA C (ceiling): deleting mulModSub2F32 from the "
   "step is 721 per step = -44,702 gross; realistic net -18,600 to -31,000. IDEA B (ceiling): deleting "
   "mulModSub2W32M is 855 per step = -53,010 gross; realistic net about -24,800. IDEA A is a PRECONDITION, NOT A "
   "WIN — it was priced at -4,340 against an old tree and is now worth about -1,744, because the tinf mux lane it "
   "targeted is already gone; what remains is IsZeroFeSumR 4x64 = 256 plus 24 per step of tIsInf muxes. DO A ONLY TO "
   "UNBLOCK B AND C. The replacement certificates do not exist in the tree, so the net figures are bounded "
   "estimates, not derivations — the gross removals (721 and 855 per step) ARE exact."),
  ("18000 — THE CHEAPEST BIG ITEM ON THE BOARD, AND IT IS A PORT OF SOMETHING ALREADY SHIPPED","PORT THE SQUARES "
   "TELESCOPE FROM FIXED-BASE AND DELETE x4 FROM THE STEP. In the ELM step ONLY lambda1 AND w ARE GENUINE ADVICE "
   "(2 x 531 = 1,062 per step); xS, x4 and y4 are DERIVED — each is a polynomial in prior advice, so each of the "
   "three ~510-point materialisations is RECOVERABLE WORK, NOT FLOOR. That is 94,302 across the tree sitting in "
   "values nothing forces us to witness. TAKE THE FIRST ONE: carry x4 = w (x) (2*lambda1 + w) + tx UNREDUCED. Its "
   "ONLY MULTIPLICATIVE CONSUMER IS THE lambda1 CERTIFICATE lambda1 (x) (tx - rx) = ty - ry, so carrying it raises "
   "that certificate from degree 2 to degree 3 and nothing else changes. PRICE: -531 for the deleted "
   "materialisation, +240 for the widened certificate, NET -291 PER STEP x 62 = -18,042. THE INSTRUMENT ALREADY "
   "EXISTS — the fixed-base tree does exactly this and it landed; read that code rather than deriving the widened "
   "quotient from scratch, and apply the exact-bounds law to the new carry width (ceil(log2(OFF_L + OFF_R)), NOT a "
   "rounded power of two). IF THIS LANDS, y4 AND xS ARE THE SAME SHAPE and the remaining ~63,000 is a repeat."),
  ("19800 — THE AUDIT IS DONE AND IT CAME BACK POSITIVE; TWO 64-BIT FOLDS PER STEP","THE SIGHTING IS "
   "CONFIRMED, SO SKIP STRAIGHT TO THE PORT. ParamsFoldT.lean:42 has qBitsFoldT = 69 against "
   "ParamsFold32T.lean:67 qBitsFold32T = 36, so MulModFoldT is the base-2^64 fold, and it is live at exactly TWO "
   "sites on the step path: DivOrZeroF3.lean:326 and DivOrZeroS32.lean:366. Both reach the step through "
   "SlopeXS/Slope2 -> FusedStep -> GLVStep. A third site, PointValid.lean:62, is NOT on the per-step path -- do "
   "not count it and do not port it for per-step gain. THE REPLACEMENT FAMILY IS ALREADY BUILT AND COSTED: "
   "mulModFold32Cost <97,99>, mulModFold32TCost <93,95>, mulModFold32MCost <159,161>, mulModFold32NCost "
   "<157,159>. This is the same mechanical change that already landed elsewhere in this tree "
   "(DivOrZeroN32 -> Fold32N), so read that diff rather than deriving it. "
   "*** ONE THING IS NOT VERIFIED AND YOU SHOULD CHECK IT FIRST, IT TAKES MINUTES: the -160 per instance is "
   "from an earlier CERT64 354 vs CERT32 194 measurement. Cost.lean:2313 defines mulModFoldTCount only as a "
   "Count EXPRESSION with NO proved numeric constant, unlike every 32-bit variant which has one. Evaluate "
   "mulModFoldTCount numerically and re-derive the delta before you size the work: the SIGHTING is confirmed, "
   "the 19,840 is not. ***"),
  ("14600 — SETTLE THE KILL-SWITCH BEFORE SPENDING THE SLOT","THE +-1 SIGNED-DIGIT MIGRATION, WHICH SUBSUMES THE "
   "NEGATION-SYMMETRY ITEM. Re-derived against the current tree: the loop saving is -7,296 (VarLookup is <122,122> = "
   "244 today, being 15 muxes x 8 fields plus IsZeroFeSumR; under signed digits it becomes 7x8 + 3 XNOR + 4 negation "
   "+ 2 isInf = 65 products = 130, i.e. -114 per lookup x 64), and the table saving is about -10,148 (8 independent "
   "entries need ~7 adds against today's glvSubsetCost <14004,14092> = 28,096 for 11 adds), against a parity payback "
   "of +2,808. Net about -14,600. CORRECTION TO THE OLD ITEM, WHICH LISTED THIS AS TWO SEPARATE WINS: negation "
   "symmetry is NOT available today, because T[15-i] = -T[i] is FALSE for this table — it is a {0,1} subset-sum "
   "table with t0 = infConst (GLVBuildTable.lean:656), so t15 = r0+r1+r2+r3 is not -t0. Symmetry exists ONLY AFTER "
   "the migration, so this is one item. THE KILL-SWITCH, SETTLE IT FIRST: if FusedStep cannot accept an UNREDUCED "
   "table y, per-step negation costs SubMod 577 x 62 = +35,774 and the whole thing dies. Determine that before "
   "writing anything else."),
  ("2272 — CONCRETE, AND THE ITEM THAT USED TO SIT HERE WAS MOSTLY DEAD","PORT DivOrZeroS32 TO A 32-BIT FOLD. It "
   "still runs MulModFoldT <176,178> at DivOrZeroS32.lean:309 DESPITE already witnessing lam32 in 8x32 limbs and "
   "re-assembling through Limbs32.emuOf32; its 32-bit sibling DivOrZeroN32 is <418,420>. 71 live instances at -32 "
   "each = -2,272. RISK: the target is a 7-cell polynomial, so it needs a new Fold32-with-polynomial-target "
   "instance. SECONDARY, same item: MulModSub2D3 <438,441> is still un-ported at CompleteAdd.lean:620 (x9) and "
   "PhiPairAdd.lean:328 (x2), 11 sites at -24 to -28 each = -264 to -308. IGNORE THE OLD ITEM'S TWO OTHER "
   "PARAGRAPHS: MulModNorm and MulModNorm32 DO NOT EXIST anywhere in this tree, and 'every remaining mulModSub2 "
   "still at 440 allocations' is false — mulModSub2Cost is <438,441> and its only wiring site is off the live "
   "path."),
  ("744 — SAFEST WORK ON THE BOARD, AND HALF OF IT HAS NOW LANDED SO READ THE TREE BEFORE YOU START","TWO BOUND PATTERNS ON THE FOLDS. (a) "
   "POSITION-DEPENDENT Nf PLUS A LATER CARRY GROUP, -496 LEFT OF THE ORIGINAL -1,240. VERIFIED LANDED, DO NOT REDO: ParamsFold32 is now gfFold32 = [6,1,1..] with wfFold32 = 45 and qBitsFold32 = 38 (ParamsFold32.lean:47/72/75), and ParamsFold32T is gf [6,1,1..] with wfFold32T = 43, qBitsFold32T = 36 (ParamsFold32T.lean:52/74/77). The Fold32 regrouping IS THE -248 THAT SET THE 307,228 RECORD. STILL OPEN AND STILL WORTH -496: ParamsFold32M and ParamsFold32N are BOTH still gf = [3,1,4,4..], posOf = [0,3,4,8,12..], with wfFold32M = 79 and wfFold32N = 78 (ParamsFold32M.lean:32/35/47, ParamsFold32N.lean:32/35/47). Regrouping each to [5,1,2] should take 79 -> 77 and 78 -> 76, i.e. -248 apiece over 62 instances. THE QUOTIENTS ARE ALREADY EXACT — qBitsFold32M = 69 and qBitsFold32N = 68 are triangular, so DO NOT touch them; the win is in Wf only. Every Nf is declared as a CONSTANT function of position "
   "at the maximum cell count, while the true folded-digit profile decays steeply: Fold32 and Fold32T give d = "
   "[6840, 5871, 4894, 3917, 2940, 1963, 986, 9] x Ca*Cb, and Fold32M and Fold32N give d = [2932, 2935, 1959, 1958, "
   "982, 981, 5, 4] x Ca*Cb. Since OFF_L(0) ~ Nf(gf_0 - 1)/2^B and only Wf(0) is charged, you must make Nf "
   "POSITION-DEPENDENT **and** push the single materialised carry to a later group — NEITHER LEVER WORKS ALONE, "
   "since with constant Nf the regrouping changes nothing. ALSO STILL OPEN ON THE 64-BIT SIDE: qBitsFoldT 69 -> 68 "
   "over 73 = -146; and wfFold 100 -> 99 over 23 = -46 (ParamsFold at B=64 is FIXED at [2,1,1] — gf_0 > 2 breaks "
   "2^Wf * 2^192 < p). *** THIS HAS BEEN ATTEMPTED ONCE AND THE SUBMISSION FAILED. The arithmetic was RIGHT — that "
   "attempt reached mulModFold32TCost <95,97> -> <93,95>, exactly the two bits derived above — so the defect is "
   "almost certainly the LEAN SIDE CONDITION, not the bound. The GVXHyps conditions check arithmetically "
   "(worst case Fold32 at gf_0 = 6 gives about 2^238 against 2^254) BUT THAT WAS CHECKED IN PYTHON, NOT LEAN, "
   "and the `by decide` on the THIRD condition is where it fails. SO: DISCHARGE THAT CONDITION FIRST, ON ONE "
   "INSTANCE, BEFORE TOUCHING THE OTHER FOUR. If `by decide` cannot close it at gf_0 = 6, FALL BACK TO A "
   "SMALLER gf_0 AND TAKE ONE BIT INSTEAD OF TWO — half of this item is worth far more than a failed "
   "submission. Dispatch from the CURRENT seed: the failed attempt also carried lost ground in "
   "divUncheckedD3, doubleCost, mulModSub2, mulModSub2D3 and phiPairAdd. *** (b) A PROVABLY ZERO CONVOLUTION CELL, -248, NO SOUNDNESS OBLIGATION: interpolatedMul is "
   "charged <15,15> in all four 32-bit folds, but in Fold32M and Fold32N the second operand's ODD 32-bit positions "
   "are the LITERAL ZERO EXPRESSION (MulModFold32M.expand32), so deg(a*b) <= 13 and cell c_14 is identically zero. "
   "Fourteen evaluation points suffice: <14,14>, -2 per instance x 124."),
  ("1240 — THREE SURVIVING MUXES AND GUARDS IN THE FUSED STEP","WHAT IS LEFT OF THE OLD 32-BIT-ACCUMULATOR ITEM. Its "
   "headline of -16,616 IS GONE and its ledger was stale: glvStep is 4,377 = 244 + 1,641 + 870 + 1,592 + 30, not "
   "4,477 = 270 + 1,655 + 892 + 1,624 + 36. Three sub-items survive: the bMul Mux at FinishXY.lean:57 is 8 per step "
   "x 62 = -496; the xSe Mux at Slope2.lean:71 is 8 per step x 62 = -496; and DivOrZeroS32's isZeroFeSum <2,2> is 4 "
   "per step x 62 = -248. The rest already landed — DivOrZeroN32 moved to Fold32N (FusedCost.lean:407-413), "
   "FinishXY.lean:47/60 is done, and the VarLookup win arrived by a different route (135 -> 122). One sub-item is "
   "genuinely cost-neutral; do not spend time on it. *** RE-VERIFIED AGAINST THE 306,406 RECORD TREE: ALL THREE SUB-ITEMS ARE STILL OPEN. The bMul Mux is still at FinishXY.lean:58, Slope2 still imports Mux, and DivOrZeroS32 still calls IsZeroFeSum at :273. The -274 that set 306,406 was -4 per step over 62 steps plus -26 outside the loop, and it was NOT any of these -- do not assume it was. ***"),
  ("8 — RE-DERIVED AGAINST THE 304206 TREE, AND IT HALVED","ONE TABLE MICRO-WIN LEFT, NOT TWO. (ii) -8 STANDS, "
   "VERIFIED VERBATIM: sign0 is still a live selector at GLVBuildTable.lean:353, `{ selector := input.sign0, "
   "ifTrue := negPy, ifFalse := input.P.y }`. (i) IS DEAD — the -16 for deleting the t4x and t8x canon-x muxes in "
   "Subset.main is GONE: `t4x` and `t8x` now have ZERO occurrences anywhere in the Solution tree, and "
   "GLVBuildTable.lean:620-623 is a different piece of code (Subset.main's t3/t12 PhiPairAdd and a "
   "canonicalisation comment). Do not go looking for them. THIS IS WHY THE STALENESS BANNER MATTERS: the item "
   "carried the label 'VERBATIM, STILL THERE' and half of it had already landed. NOTE THE OLDEST VERSION OF THIS "
   "ITEM ENDED WITH 'DO NOT HUNT FOR THOUSANDS HERE' AND THAT ADVICE IS STILL WRONG — the signed-digit migration "
   "restructures this very table for about -10,000."),
  ("speculative — no droppable site has been verified","TWO AUDITS THAT CAME BACK EMPTY, KEPT ONLY SO THEY ARE NOT "
   "RE-OPENED BLIND. (a) MUXES WHOSE CONSUMER READS ONLY A PREDICATE: the exemplar cited by the old item IS NOT IN "
   "THIS TREE — Slope2.lean:85-86 still has the den2 Mux, and denSafeVec exists only at DivOrZeroF3.lean:169 where "
   "it serves the zero guard, not the tangent selector. The full hot-path Emu-Mux inventory is SlopeXS.lean:96, "
   "Slope2.lean:71/85/93, FinishXY.lean:57 and FusedStep.lean:63/65/67 — eight muxes at 8 per step = 64 per step, "
   "3,968 total — and NONE was found whose consumer reads only a predicate; den1, den2, num2 and bMul all determine "
   "a value. Price per deletion if one is ever found: -496. (b) ValidP versus Normalize: <260,265> against "
   "<252,256> is 17 per site across 212 live sites, but every one either feeds an EqFe (which needs canonicality) "
   "or becomes an accumulator coordinate that must be Valid. NO DROPPABLE SITE VERIFIED. Ceiling if a whole class "
   "ever fell: 17 x 62 = 1,054."),
  ("demoted — the specific win cannot recur","THE lambda CERTIFICATE INVERSION. The old item pointed at "
   "GLVScalarRelation.lean:100-103; those lines are now the vInv witness body and an assertZero. lambda is still in "
   "the A-slot but at :104-105, in scalarMulModLooseWideB with a := eigenvalueConst and b := input.s. The '531/535 "
   "lv2 intermediate' it hoped to delete is mulModLooseQCount <531,535> at MulModLooseQ.lean:419, and MulModLooseQ "
   "IS WIRED TO NOTHING — the deferred-relation rewrite already removed it, which is where the -1,072 went. The "
   "ceiling here is now the whole relation at 1,754, of which <720,724> = 1,444 is the remaining MulModLoose."),
 ]),
 "sha256-hash": (144985, None, [
  ("0 — THE -6 AT 144,321 IS 0-FOR-3 AND ALL THREE TREES SHARE ONE EDIT. ANSWER A BOUND QUESTION BEFORE YOU TRY "
   "A FOURTH","*** THREE INDEPENDENT TREES REACHED 144,321 = 71,872 alloc + 72,449 constr AND ALL THREE WERE "
   "JUDGED AND REJECTED (1ee0c2b0, bad91b20, 635fa2cf). *** They are 12, 14 and 19 files apart from one another, "
   "so they are genuinely different implementations — but intersecting their diffs against the seed leaves only "
   "FOUR common files, two of which (CostSparseD, Main) are cost bookkeeping. THE SUBSTANTIVE SHARED EDIT IS TWO "
   "FILES: CompressBlockWideSparseDPack and R1CSCompressorsD. *** WHAT IT DOES: *** swaps the wide round family "
   "for a W4 variant — import SHA256RoundsW4 for SHA256RoundsW, call SHA256Rounds63.circuit62_pairedW4 for "
   "circuit62_pairedW, use r1cs_sub_sha256Rounds62_pairedW4 and affineW_subOut_sha256Rounds62_pairedW4, pulling in "
   "R1CSWidePrimitivesD4 — *** AND WEAKENS AN ASSUMPTION: RPShared.Numeric5W input.state[3] and input.state[7] "
   "BECOME RPShared.Numeric4W. *** That bound weakening is where the -6 comes from and it is the prime suspect: if "
   "state[3] or state[7] can exceed the Numeric4W bound the circuit is unsound, and it would be rejected "
   "IDENTICALLY in every implementation of the same idea — exactly what happened. *** SO ANSWER THIS FIRST, AND IT "
   "NEEDS NO CERTIFICATE: what are the true bounds on state[3] and state[7] entering circuit62 on this seed, and "
   "do they fit Numeric4W? DERIVE THE BOUND, DO NOT ASSUME IT. *** If they fit, say why and the -6 should land. If "
   "they do not, the W4 route is closed and saying so is worth a slot, because it stops a fourth, fifth and sixth "
   "job rediscovering it. *** WHAT IS NOT CONDEMNED: THE SCORE. *** 144,321 by some route OTHER than the W4 swap "
   "is untouched by any of this, and three rejections is well inside the range where persistence has paid here — "
   "variable-base 303,328 took five trees and the fixed-base stageO2 deletion took seven."),
  ("0 — THE -10 AT 144,343 TOOK TEN SUBMISSIONS AND THEN TOOK THE RECORD. READ THE WHOLE LEDGER","*** NINE VERIFIER TIMEOUTS AND THEN A "
   "VERIFICATION ON THE TENTH (1433c4a5), WHICH TOOK THE RECORD. THE ROUTE IS EXPENSIVE TO ELABORATE AND "
   "ENTIRELY SOUND — IF YOU READ A TIMEOUT AS A VERDICT YOU WILL ABANDON A WINNER. WHAT THE NINE WERE: *** Two variants of one route both land on 144,343 = "
   "71,883 alloc + 72,460 constr (-5/-5 from the 144,353 seed). Variant one was submitted SEVEN times "
   "(dbe3eb9d, 5bbb2947, e7e8c2ca, 8ec2e71c, 55ea494e, 28c6d25f, 156ea28e) and timed out every time before the "
   "resubmit budget was exhausted; variant two (927b52a1) timed out on its first attempt. Not one of the eight "
   "was ever JUDGED — no soundness verdict, no rejection, nothing. *** THEY ARE NOT INDEPENDENT ATTEMPTS: they "
   "change 25 of the same files against the seed (31 and 28 changed respectively), so this is ONE route with "
   "implementation variation, and eight timeouts are weaker evidence than eight independent trees would be. *** "
   "SIZE WAS NEVER THE EXPLANATION, AND THAT PART STILL HOLDS. A LARGER reduction on this same seed was "
   "judged promptly: 144,337 (-16, 71,880 + 72,457, sub 74afb362) came back `failed score=None` — rejected on "
   "the merits, not timed out. So the verifier handles trees of this size fine; something in the -10 route is "
   "specifically expensive to elaborate. *** WHERE TO LOOK, AS A HYPOTHESIS RATHER THAN A FINDING. *** The "
   "judged 144,337 touches 15 files; the timed-out route touches 25 shared ones. Fourteen files are in the "
   "timed-out route and NOT in the judged one: CompressBlock5, CompressBlock5DPack, Cost, TailAdders, "
   "TailPairTight, TailPairWide, and the deferred/tail computable-witness cluster ComputableDeferredBlocks, "
   "ComputableMainSparseD, ComputableDCompressorsFull, ComputableDOutputAgreement, ComputableTailPairs, "
   "ComputablePackTail, ComputableCompressBlock1Sparse, ComputableCompressBlockWideSparse. THAT CLUSTER IS THE "
   "EXPENSIVE PART — it is witness-side machinery, which is where elaboration cost hides without changing a "
   "single row. *** WHAT TO DO, NOW THAT THE ROUTE HAS WON. *** Take it, and buy elaboration headroom in the "
   "SAME submission — the per-run success probability is the only thing between this route and a record. DO NOT "
   "read a timeout as a verdict on your tree, and DO NOT trade the reduction down for a safer one you merely "
   "fear will time out: nine timeouts here were followed by a clean verification of the SAME score. IF YOUR EDIT "
   "AVOIDS THE CLUSTER none of this applies — 144,337 got a verdict on its first try, and was rejected on the "
   "merits, which is a real defect and a different problem."),
  ("0 — TODAY'S TWO ATTEMPTS, AND HOW TO IDENTIFY YOUR OWN EDIT","*** 2026-08-12, TWO SUBMISSIONS OFF THE "
   "144,353 SEED, OPPOSITE OUTCOMES, AND THE DIFFERENCE MATTERS. *** -16 (144,337 = 71,880 alloc + 72,457 "
   "constr, sub 74afb362) was JUDGED AND REJECTED — status=failed, score=null. -10 (144,343 = 71,883 + 72,460, "
   "sub dbe3eb9d) hit a VERIFIER TIMEOUT — never judged, so it is evidence of NOTHING about that tree, and it "
   "has been RESUBMITTED UNCHANGED. Do not read the rejection as a verdict on the timeout or vice versa; they "
   "were 34 files apart. *** BOTH MOVED ALLOCATIONS AND CONSTRAINTS BY THE SAME AMOUNT — -8/-8 and -5/-5 — "
   "which is the signature of deleting WHOLE ALLOCATED ROWS (each deleted row is one alloc plus one "
   "constraint), not of collapsing a product into an affine combination. If your edit moves only one of the "
   "two counters you are doing something structurally different from either of these, and neither result "
   "applies to you. *** THE SUBMISSION DESCRIPTION DOES NOT IDENTIFY YOUR EDIT — DO NOT TRUST IT. *** It is "
   "generated from a fixed technique scan of the tree, so both submissions above carry BYTE-IDENTICAL "
   "description strings despite being 34 files apart. The only way to know what changed is "
   "`diff -rq projs/sha256-hash/Solution/SHA256 <your tree>`. Name the FILES you touched in your summary; a "
   "score is not an identifier and treating it as one has already cost slots on this slug."),
  ("survival first — BUT WE HAVE NOW BANKED ONE, AND IT SETTLES THE WALL QUESTION","*** THE FULL SUBMISSION LEDGER ON THIS SLUG, AND IT SETTLES THE WALL QUESTION AGAINST THE OBVIOUS READING. -612 TIMED OUT. -306 TIMED OUT. -298 VERIFIED AND TOOK THE RECORD (144,687, from yash1io's 144,985). -280 TIMED OUT TWICE. TWO FACTS, AND THE SECOND IS THE ACTIONABLE ONE. (1) SIZE DOES NOT PREDICT THE OUTCOME: the SMALLEST reduction we have attempted here timed out while a LARGER one verified, so AIMING SMALLER IS NOT A STRATEGY and has now cost four attempts. (2) EVERY SINGLE FAILURE ON THIS SLUG IS A VERIFIER TIMEOUT — not one soundness failure, not one bad ledger. So the binding constraint is ELABORATION TIME AND NOTHING ELSE, and the -280 at 144,389 IS A SOUND SOLUTION THAT SIMPLY WILL NOT ELABORATE IN BUDGET. *** RETRY AN IDENTICAL SOLUTION RATHER THAN ABANDONING IT — BUT READ WHICH FAILURE YOU GOT. *** The harness reports two DIFFERENT terminal failures and they mean opposite things. `VERIFIER TIMEOUT` means zk.golf returned status=timeout: the verifier gave up, your solution was never judged, and RESUBMITTING THE SAME TREE IS THE CORRECT MOVE. `failed score=None` means status=failed or error: zk.golf judged it and rejected it — a broken build, a bad axiom, or an unsound circuit — and resubmitting unchanged will fail again. MEASURED LEDGER ON THIS SLUG, and the timeouts really are stochastic: the same -280 landing at 144,389 was submitted FIVE times — one VERIFIED AND TOOK THE RECORD, three timed out, one hard-failed. Two of the timeouts arrived AFTER the successful run on the identical tree, so a timeout is evidence about that RUN and nothing else. Earlier attempts: -612 timed out, -306 timed out, -298 verified first try. *** A TIMEOUT IS NOT EVIDENCE THAT YOUR SOLUTION IS SOUND — IT IS EVIDENCE OF NOTHING AT ALL. *** Measured both ways on this slug: 144,389 timed out repeatedly and then VERIFIED on retry, while 144,353 timed out once and then came back HARD-REJECTED (`failed score=None`) when a retry actually got judged. Same signal, opposite truths underneath. So retrying is how you FIND OUT which case you are in, not a way of winning. *** THE -36 FROM THE 144,389 SEED IS A DEAD END — FOUR ATTEMPTS, THREE DETERMINISTIC REJECTIONS. *** It landed at 144,353 and was submitted four times: one VERIFIER TIMEOUT and then THREE `failed score=None`. *** READ THAT AS A CHANGE, NOT AS A SCORE. The seed has since moved to 144,373, so 144,353 is now reachable by a DIFFERENT -20 that has nothing to do with the defective one, and a job hitting that total today is not necessarily repeating the mistake. What is condemned is the specific reduction that the 144,389 seed made obvious, not the number 144,353. Identify your change and judge it on its own; if it is genuinely a different edit, submit it. *** A rejection is not a timeout — the verifier JUDGED it and threw it out, so it is deterministic and three of them at the same score is not variance, it is a genuine defect in that reduction (a broken build, a disallowed axiom, or an unsound row). CONTRAST IT WITH 144,389, WHICH LOOKED SIMILAR AND WAS NOT: that one was three TIMEOUTS plus one rejection, and it verified on the fifth try. Timeouts are worth retrying; rejections are not. If you rediscover the -36 at 144,353 — and four jobs before you did, so you probably will — DO NOT SUBMIT IT UNCHANGED. Either find the defect first, or take a different reduction. WHAT TO DO WITH YOUR SLOT. (1) On a TIMEOUT, resubmit unchanged once or twice — it is cheap and it converts an unknown into an answer. Do not trade the reduction down for a safer one you merely fear will time out. (2) On a `failed score=None`, STOP RESUBMITTING and find the defect: the verifier judged it and rejected it, so the build, the axioms or the soundness proof is genuinely wrong and an identical resubmission cannot pass. (3) Buy headroom in the SAME submission either way, since it raises the per-run success probability and a cost-neutral tidy-up cannot be submitted alone — BUT NOT WITH `decide +kernel`, WHICH IS THE WRONG TOOL HERE AND MAY BE PART OF THE PROBLEM. Measured on this tree: the import closure of Solution.SHA256.Main is 156 files containing 5,073 `norm_num`, 3,253 `omega`, 2,063 `simp only`, 1,507 `rfl` and only 30 `decide` — and ZERO `decide +kernel`. There is nothing here for it to convert. Worse, `maxHeartbeats` bounds the ELABORATOR only: exhausting it throws a deterministic error, which is a clean fast rejection, while KERNEL type-checking escapes that brake entirely and burns unbounded wall clock (measured: 18.6 s of type checking under maxHeartbeats set to a tenth of default). So moving work kernel-side trades a clean failure for exactly the unbounded burn that is killing us. WHAT TO DO INSTEAD, IN ORDER: (i) the 5,073 `norm_num` calls are the biggest single count and most of them discharge closed literal index bounds like `0 < 8` — `norm_num` is `simp` PLUS extension dispatch over the full Mathlib simp set and is never cheaper than `simp` on the same goal, so step down the ladder `norm_num` -> `norm_num only [...]` -> `norm_num1` (which does not call simp at all), checking each site compiles rather than sweeping blind — AND EXCLUDE PRIMALITY GOALS FROM THAT PASS: `Nat.minFacAux` is well-founded recursive and therefore irreducible since Lean 4.9.0, so `decide` cannot reduce it and Mathlib documents `norm_num` as MUCH FASTER there, the opposite of the general rule; (ii) `omega` costs scale with CONTEXT size, not goal size, because it processes every hypothesis — hoisting a repeated shape into one lemma proved once and applying it with a closed side condition measured 2.8x faster, and `omega -splitNatSub -splitMinMax` removes default-on search that most sites do not need; (iii) `irreducible` on heavy definitions still stands. (4) DO NOT AIM SMALLER TO DODGE THE WALL — the smallest reduction attempted here (-280) needed five tries while a larger one (-298) verified immediately. Size does not predict the outcome. BUY ELABORATION HEADROOM BEFORE YOU REDUCE ANY "
   "SCORE. Post-harness-fix this challenge is 0 FOR 2 AND BOTH FAILURES WERE VERIFIER TIMEOUTS: 144,858 (-612) and "
   "145,164 (-306). BUT A COMPETITOR THEN LANDED A -480 THAT VERIFIED, SO THE WALL IS NOT SIZE — IT IS THE PROOF COST OF "
   "THE PARTICULAR CHANGE. A -480 whose obligations are cheap beats a -306 whose obligations are expensive, so "
   "do NOT simply aim smaller; aim for changes that add little elaboration. Their tree uses irreducible in 38 "
   "of 149 files, EXACTLY AS OURS DOES, so that is not where their margin came from. The whole "
   "timeout ledger across every slug is 6, of which 4 are fixed-base and 2 are this one: BOTH LARGE TREES AND "
   "NOTHING ELSE. THE ONLY MOVE THAT HELPS IS SHRINKING THE PROOF RATHER THAN THE CIRCUIT — mark the heavy "
   "definitions irreducible. *** DO NOT BLANKET-CONVERT `by decide` TO `decide +kernel` — that advice was derived from the fixed-base tree (1,659 `decide` sites) and does NOT transfer here, and it can make timeouts WORSE: maxHeartbeats bounds only the elaborator, so kernel work escapes the brake and burns unbounded wall clock. `decide +kernel` is correct in exactly one narrow case — a bounded-quantifier decide over a LARGE range, where it is about 1.5x faster and, measured at N=4000, survives where plain `decide` aborts with a stack overflow. On small closed goals it measured about 25% WORSE, because it creates an auxiliary declaration for the kernel. *** Targets for irreducible: cost constants, the big params and schedule tables, any def whose body is a large "
   "literal vector), and prefer a submission that verifies at a modest gain over one that times out at a large "
   "one. A reduction that cannot be verified banks nothing and burns the slot."),
  ("448 — A NEW LEVER, AND THE SHAPE IT ATTACKS IS SITTING IN Cost.lean RIGHT NOW","TRUNCATE THE SIGMA CARRY WORD "
   "MOD 2^32 AND ONE LANE DISAPPEARS. Cost.lean:50-53 declares sigmaCost = <32,32>, lowerSigma0Cost = <32,32> and "
   "lowerSigma1Cost = <32,32>, each 32 XOR3 lanes at <1,1> (Cost.lean:170 proves CostIs (subcircuit Xor3.circuit b) "
   "sigmaCost). THE IDENTITY, VERIFIED OVER 20,000 RANDOM WORDS FOR ALL FOUR MAPS: Sigma0(a) = rotr2 + rotr13 + "
   "rotr22 - 2*SUM_{j=0}^{30} 2^j maj(a_{j+2}, a_{j+13}, a_{j+22}) (mod 2^32). The exact-over-Z identity runs j to "
   "31, but that top carry term enters with a factor of 2, so its weight is 2^32 AND IT VANISHES MOD 2^32. EXACTLY "
   "ONE LANE IS DROPPABLE — j=30 has weight 2^31 and is live, so do not try for two. MAJ3 is single-row native with "
   "implied booleanity ((2s-3)(4o-s) = s), so each surviving lane is still <1,1> and sigmaCost goes <32,32> -> "
   "<31,31>: -2 PER SIGMA INSTANCE. IT IS SOUND HERE BECAUSE EVERY CONSUMER TAKES THE WORD, NOT THE BITS — "
   "ComputablePairB1.lean:113 reads (newE + sigma + Maj a b c + (2^32-1-d) + 1), a mod-2^32 sum — and a's bits are "
   "already decomposed for Ch and Maj, so the rotations stay free affine reads. SITES: roundCost (Cost.lean:63) "
   "charges 2 * sigmaCost per round and each schedule step charges 2 lower sigmas, so 64 rounds and 48 steps is 224 "
   "instances = -448 per block. COUNT THE ACTUAL INSTANCES, DO NOT TRUST THAT ARITHMETIC. THAT CHECK IS NOW DONE — DO NOT REDO IT. "
   "The concern was that truncation pushes each addend into [0, 2^33) and grows every fused reduction's carry by one, so a carry sitting exactly on a power-of-two boundary would cancel the round's saving. MEASURED over "
   "4.2e5 states INCLUDING SATURATED EXTREMES: the quotient is e' in {0..6} (3 bits) and a' in {0..8} (4 bits). NEITHER IS ON A BOUNDARY, so the full -448 stands and you should take it. "
   "IT IS ALSO WIDER THAN THIS ITEM ORIGINALLY SAID. The criterion is v2(coefficient) + j >= 32, and once the words are in carry-save form (see the PRECONDITION item) Sigma0 and Sigma1 ALSO enter at coefficient -2, so their bit 31 is free too — 64 rounds x 2 Sigmas + 48 steps x 2 sigmas = 224 gadget bits per block. Maj and Ch enter at coefficient +1 and have NO free bit; do not try to extend it to them. THIS IS NOT THE REFUTED "
   "IDEA: sigma-as-majority followed by 2:1 maj packing is dead; this is TRUNCATION, and nothing refutes it."),
  ("PRECONDITION FOR THE -448 AND 240 ITEMS — DO THIS ONE FIRST","REWRITE Sigma0/Sigma1/sigma0/sigma1 IN CARRY-SAVE FORM AND "
   "NEVER MATERIALISE THEM. The integer identity A + B + C = (A xor B xor C) + 2*maj(A,B,C) holds bitwise-parallel on "
   "words, so each diffusion function is a FREE integer affine combination of rotations MINUS TWICE a majority word: "
   "Sigma0(a) = [ROTR2 + ROTR13 + ROTR22](a) - 2*N0 with N0 = sum_j 2^j maj(a_{j+2}, a_{j+13}, a_{j+22}), and "
   "likewise Sigma1 with (6,11,25), sigma0 with (7,18,SHR3), sigma1 with (17,19,SHR10). VERIFIED on 1e5 random "
   "inputs per function and 1e5 full-round states. The whole round then fuses to e' == d + h + K + W + "
   "[ROTR6+ROTR11+ROTR25](e) + Ch(e,f,g) - 2*N1 (mod 2^32), and a' the same plus [ROTR2+ROTR13+ROTR22](a) + "
   "Maj(a,b,c) - 2*N0. Sigma0, Sigma1, T1 and T2 are NEVER MATERIALISED — the entire nonlinearity of a round is "
   "three majority words and one Ch word. THIS IS COST-NEUTRAL ON ITS OWN (a maj bit and an xor3 bit are both <1,1>, "
   "and maj = (s - xor3)/2 with s free, so they are affinely interchangeable) — take it because it is what makes the "
   "-448 SIGMA TRUNCATION item exist, it enables the 240 SHR-PACKING item, and it deletes four 32-bit intermediate words per "
   "round from the witness. FIRST STEP: prove A + B + C = (A ^^^ B ^^^ C) + 2 * maj A B C over Nat restricted to "
   "< 2^32, then emit N0, N1 and fold the rotation sums into the existing free linear combination."),
  ("240 — THE SHR POSITIONS ARE DEGREE 2, AND DEGREE 2 PACKS TWO PER ROW","sigma0 AND sigma1 FEED COMPILE-TIME ZEROS "
   "AT THEIR SHR POSITIONS, WHICH COLLAPSES THOSE GADGETS FROM DEGREE 3 TO DEGREE 2: maj(A,B,0) = A AND B and "
   "xor3(A,B,0) = A XOR B. sigma0's third operand is 0 at positions 29,30,31 and sigma1's at 22..31. Bit 31 is "
   "already free by the -448 truncation item, so sigma0 has 2 ANDs left (positions 29-30, ONE ROW) and sigma1 has 9 (positions "
   "22-30, FIVE ROWS): 5 rows per schedule step, 240 per block. THE DICHOTOMY BEHIND IT IS PROVED AND YOU SHOULD "
   "RELY ON IT: reduce a gadget to its multilinear polynomial over the boolean cube. DEGREE 2 (Ch, XOR2, AND2) takes "
   "the C-slot shape gamma*z = P0*Q0 - R0 and packs EXACTLY 2 per row — never 3, because for k gadgets on disjoint "
   "variables the quadratic form is a direct sum of k rank->=1 blocks while the C-slot shape needs rank <= 2 modulo "
   "the free diagonal shifts. DEGREE 3 (Maj, XOR3, AND3) packs NEVER, including against decoy roots. SO DO NOT "
   "SPEND ANY TIME LOOKING FOR A ROW THAT PACKS TWO Maj OR TWO XOR3 — that search is closed by proof and by "
   "exhaustive search over multipliers with coefficients in [-3,3], which found zero hits even for pairs sharing "
   "one or two inputs. circomlib's O1 pass already kills mid = b*c for 13 bits per SigmaPlus (624 constraints), but "
   "no implementation found packs the surviving degree-2 gadgets."),
  ("CHEAP, CHECK BEFORE PRICING","THE MESSAGE-SCHEDULE QUOTIENT IS EXACTLY 2 BITS. Machine-checked over 2e5 random "
   "4-tuples: q_i in {0,1,2,3}, and it follows immediately because after the -2n corrections all four terms are "
   "genuine 32-bit words so their sum is < 4*2^32. In carry-save form the whole schedule step is ONE FREE AFFINE "
   "FORM plus two majority words plus this quotient — the bracketed rotation/shift sums plus W[i-7] plus W[i-16] "
   "are entirely free, and the only nonlinearity is -2*n1(W[i-2]) - 2*n0(W[i-15]). LOOK AT WHAT MessageSchedule "
   "CURRENTLY CHARGES FIRST: if it already witnesses 2 bits this is worth zero; if it charges 3 bits or a product "
   "chain, replace with two witnessed bits and let the reduction row absorb q = q0 + 2*q1 for free. Carries cannot "
   "be shared across words — each W feeds exactly one sigma0 and one sigma1 in its lifetime and the majority words "
   "of different steps have disjoint variable sets."),
  ("DO NOT SPEND TIME HERE — FOUR CLOSED DIRECTIONS","(1) SPARSE/SPREAD REPRESENTATION (the halo2 table16 route, "
   "2099 rows): its ENTIRE saving is that the dense<->spread bijection is one LOOKUP row. Enforcing it "
   "arithmetically means decomposing the 16-bit chunk into bits and re-summing with weights 4^i, i.e. back to >= 1 "
   "row per bit. We have no lookups; there is no lookup-free variant. (2) MEET-IN-THE-MIDDLE / running rounds "
   "backward: the backward round invokes the IDENTICAL four nonlinear gadgets on the identical words — the "
   "bijection is realised entirely by free affine rearrangement, so direction does not touch the nonlinear content. "
   "Zero gain. (3) ROTATION-FRIENDLY REPRESENTATIONS (evaluation at a 32nd root of unity in F_r, F_2[x]/(x^32-1)): "
   "every invertible linear change of representation is free in BOTH directions and therefore cannot change the "
   "cost of anything; the bit vector already has rotation free AND addition free. (4) RANK/TENSOR DIAGONALISATION "
   "of the Sigma words: the quadratic part is rank <= 32 and would give 16 rows, but the cubic part is a DIAGONAL "
   "3-tensor with 32 nonzero entries and slice rank exactly 32, so it costs at least ceil(32/3) and realistically "
   "32. THE LESSON WORTH CARRYING: the single-row non-vanishing-multiplier gadget is extraordinarily good precisely "
   "because it computes a degree-3 function in ONE row by hiding the degree in a division — rank methods must pay "
   "for degree 3 explicitly and cannot compete. ONE GENUINE SMALL ITEM, not a dead end: on the FIRST block the "
   "state is the constant IV, so round 0's gadgets are compile-time constants and at round 1 both Maj and Ch have "
   "two constant arguments and collapse to free affine functions — about 2 rounds' worth, block 1 only."),
  ("~474 — OPERATIONAL, THE MATH IS ALREADY DONE, AND THIS ROUTE HAS NOW BANKED A RECORD THE HARD WAY. *** The deferred family this item tells you to wire up is EXPENSIVE TO ELABORATE AND ENTIRELY SOUND: three separate jobs followed this item to the identical 144,343, nine submissions timed out, and THE TENTH VERIFIED AND TOOK THE RECORD (1433c4a5). *** CORRECTION TO AN EARLIER VERSION OF THIS HEADLINE, AND IT WAS WRONG IN THE DIRECTION THAT COSTS RECORDS. It told you that if you could not buy elaboration headroom you should take a different item rather than ship a tenth timeout. The tenth was not a timeout. Persistence on this exact route is what banked the record, and the advice would have thrown it away. *** SO: DO THIS ITEM. Buy elaboration headroom in the SAME submission, because the per-run success probability is the only thing between this route and a record. And if you land on a score that has timed out before, SUBMIT IT ANYWAY — a timeout is evidence about a RUN, never about your tree.","WIRE THE DEFERRED-CHAIN CONFIGURATION INTO THE "
   "EXPORTED COST. Nineteen consecutive jobs proved a ~144,996 configuration in a side module and then submitted a "
   "tree whose Main-reachable cost still read 145,470, so every one of them scored NOTHING. Main.lean is a SINGLE "
   "IMPORT LINE, `import Solution.SHA256.MainSparse`, and MainSparse.lean:26-27 is where allocations := 72445 and "
   "constraints := 73025 actually live. A PROVED COST LEMMA IS NOT A SCORE — the only number that counts is the one "
   "reachable from Main by imports. YOUR JOB: build the compressBlock/checkPad pipeline out of the deferred family "
   "that ALREADY EXISTS in this tree (DeferWord, DeferredChain, DeferredH, RawChain, SelectRawH, Unreduced, "
   "WideChain, ReduceWord7, LazyAdd32, CompressBlock*D, SelectDigestD, plus sha256RoundPairWCost <330,332> for the "
   "wide-input first pair), route MainSparse.main through it, and UPDATE MainSparse.allocations AND "
   "MainSparse.constraints TO THE NEW VALUES. The saving is deferring the d and h reductions, which ANALYSIS.md "
   "section 3 independently prices at about 500. STATE THE FINAL Main-REACHABLE allocations AND constraints "
   "EXPLICITLY IN YOUR SUMMARY, and make sure no other module in the tree declares a competing allocations/constraints "
   "pair. DO NOT LEAVE A SEPARATE CostSparseMain.lean PROVING A BETTER NUMBER THAT NOTHING IMPORTS — that is exactly "
   "the failure mode that wasted nineteen jobs."),
  ("null result — THE PADDING BLOCK IS FULLY INDEPENDENT, MEASURED. DO NOT RE-DERIVE IT","THE ~2062 "
   "ZERO-ALLOCATION ROWS IN THE PADDING PREDICATE ARE NOT SLACK. Row-deletion criterion run over BN254 F_r with "
   "exact sparse Gaussian elimination: rows 2062, RANK 2062, KERNEL DIMENSION 0, deletable rows 0. Same for "
   "CheckPad7Sparse (2063) and dense CheckPad7 (2167). Verified three ways — the four row families reproduce all "
   "three Lean Count values exactly, honest witnesses satisfy every row while a corrupted low bit breaks rows, "
   "and an elimination-free peeling certificate gives the same rank. THE REASON: every row uniquely owns a "
   "quadratic monomial nothing else can cancel — pair rows own msg[a]^2, low-bit rows own l[j][t]^2, SparseW0 "
   "rows own msg[c]*f[len], and the lenFlags rows sit in m*f[k] with a unitriangular binomial matrix. THIS BLOCK "
   "HAS THE LARGEST constraints-minus-allocations GAP IN THE TREE (2062 against a next-largest of 32) AND IT IS "
   "STILL AT ITS FLOOR — do not spend a slot looking for redundancy here. WHERE A SAVING COULD STILL COME FROM: "
   "a different row SHAPE, not fewer rows. The tree already does this once — the paired high-bit row folds two "
   "byte checks into one row via (x_a - 1024 x_b)(x_a + 1024 x_b). Hunt for more foldings of that kind. The one "
   "thing NOT tested is cross-block redundancy against the packing and message-schedule blocks, which would need "
   "the whole 30k-row system in a single elimination."),
  ("~15000 if it works — THE ONLY UNEXPLORED SPACE LEFT","LET ROW COEFFICIENTS DRAW ON OTHER ALLOCATED WITNESSES, NOT "
   "JUST INPUT BITS. Every analysis of this circuit so far — including the tree's own audit sections — silently "
   "restricts A, B and C to be affine in the INPUT BITS. THE COST MODEL FORBIDS NO SUCH THING. It forbids two "
   "products in a row; a row may legally be affine in ANY ALLOCATED WITNESS, including other sigma lanes, Ch/Maj "
   "outputs and carry bits. That is a strictly larger space and nothing in this tree closes it. THE TREE ALREADY "
   "EXPLOITS A WEAK FORM OF IT ONCE, AND IT WAS THE BIGGEST WIN IN THE FILE: PackedMaj.Spec IS ONLY THE ROW, with "
   "FusedAAdder recovering the exact value downstream via PackedMajOne.packed_exact, which took Maj from <32,64> to "
   "<32,32> — worth 4,960. GENERALISE IT. FORMULATION TO DECIDE: T*M = P*Q + L with M, Q, L in V = span{1, bits, "
   "PRIOR WITNESSES} and P in span{M, 1} (that last containment is forced — the multiplier IS one factor of the "
   "product — and pure rank arguments miss it). PRIZE: a sigma-lane pair at 1 allocation + 2 rows is about 15,000, "
   "i.e. 10% of the circuit; at 1 allocation + 1 row it is about 30,000. Confidence is low, but this is the only "
   "direction not already refuted, and the refutations below are exact so there is nothing else to try."),
  ("null result — THE SIGMAS ARE CLOSED BY AN EXACT CRITERION","STOP ATTACKING THE SIGMA/Sigma LANES. Complete "
   "single-row taxonomy from A*B + C = 0, substituting the honest z = T(x): FORM I (a_z b_z = 0) is T*M = P*Q + L "
   "with P FORCED into span{M, 1}; FORM II (a_z b_z != 0) is T^2 + U*T = P*Q + L. Both reduce to exact linear "
   "algebra, and the controls reproduce every shipped gadget (Xor3 with M = x1 - x0, Maj32, Ch32, PackedCh, "
   "PackedMaj). THE CRITERION: A LAMBDA-PACKED PAIR OF GATE LANES ADMITS A ROW IFF THE TWO LANES SHARE AT LEAST TWO "
   "INPUT BITS. 2-shared XOR3 DOES pack (M = x2 - x1, checked on all 16 cube points). 1-shared and 0-shared XOR3 have "
   "an EMPTY multiplier space AND an unsolvable form II — meaning NO ROW CAN EVEN MENTION SUCH A z, which closes "
   "multi-row schemes as well. AND SHA-256 NEVER QUALIFIES, BECAUSE ALL FOUR ROTATION TRIPLES ARE SIDON SETS: Sigma0 "
   "{2,13,22}, Sigma1 {6,11,25}, sigma0 {7,18,3}, sigma1 {17,19,10} all have pairwise-distinct differences mod 32. "
   "Swept over every lane pair that actually meets on a common word (Sigma0xSigma0, Sigma1xSigma1, sigma0xsigma0, "
   "sigma1xsigma1, and sigma0xsigma1 on W[j] which meet 13 steps apart): MAX SHARED IS 1, ALWAYS. Sigma0xsigma0 does "
   "reach 2 but acts on state words versus schedule words and never meets. THIS IS A PROPERTY OF THE CONSTANT CHOICE, "
   "NOT A MISSING GADGET."),
  ("null result — RETRACTS AN EARLIER ITEM IN THIS QUEUE","THE <0,2062> PADDING BLOCK IS AN ACCOUNTING ARTIFACT, NOT "
   "SLACK. An earlier version of this workqueue pointed at checkPad7SparseUnchecked as the one place a "
   "redundancy argument could bite, on the grounds that it is the only <0, large> Count in the tree. That reading is "
   "WRONG: its 1673 allocations are HOISTED TO TOP LEVEL and are SCHEDULE INPUT BITS — 239 bytes x 7, the sigma0 "
   "inputs of W[1..15] across 4 blocks — sitting at the proved 2-per-bit floor. Only 119 high-bit pairs and 16 "
   "SparseW0 rows are genuinely extra. DO NOT SPEND A SLOT RUNNING ROW-DELETION ON IT. The ledger overall is rows = "
   "allocations + 580 exactly, i.e. SCORE = 2 x (WITNESS COUNT) + 580, so the ONLY lever anywhere in this circuit is "
   "FEWER WITNESSES. Per round the floor is 32 Sigma0 + 32 Sigma1 (2/bit, unpackable) + 32 Ch + 32 Maj (1/bit, "
   "packed) + 64 decomposition bits (2/bit, proved optimal) + 9 adder units = 329, WHICH IS EXACTLY WHAT SHIPS."),
  ("null results — ELEVEN IDEAS REFUTED WITH EXACT LINEAR ALGEBRA","DO NOT RE-PROPOSE ANY OF THESE. (a) SIGMA AS "
   "MAJORITY (Sigma0 = X + Y + Z - 2*maj, then pack maj 2:1), which would have been worth 19,840: a maj-pair with one "
   "shared input HAS a multiplier, M = 1 - 2*x2, but quad(T*M) is NOT in the pencil m_i q_j + m_j q_i; the 0-shared "
   "case has no multiplier at all. (b) Ch-pair plus lambda^2 * Maj-pair in one 8-variable witness, 9,920: no affine "
   "multiplier drops the degree. (c) 3-deep Ch chain, 3,413: form I's multiplier fails the pencil test, form II "
   "unsolvable. (d) 3-deep Maj chain, 3,413: same, plus 4 piecewise-affine cells cannot be covered by 2 rows (an "
   "x_0-coefficient contradiction in all three pairings). (e) xor3 + lambda*xor2, xor3 + lambda*ch, xor3 + "
   "lambda*maj, ch + lambda*maj, ~2,600 each: multiplier space empty. (f) three xor2 lanes per witness, 2,392: an "
   "explicit 3x3 minor on rows(0,2,4)/cols(1,3,5) is nonzero, so rank > 2 for EVERY diagonal. (g) the "
   "top-bit-affine trick on the round decompositions, 824: one fused equation buys exactly ONE free affine bit and "
   "the tree already spends it on lowCarry — 31 bits + 3 carry witnesses and 32 bits + 2 carry witnesses are both "
   "34/35. (h) pair booleanity of decomposition bits, ~20,000: difference-of-squares needs A PRIORI BOUNDED slots and "
   "free bit witnesses have none; the only bound available (byte < 256) is already spent on the high bit. (i) "
   "restructuring as 4 message compressions plus 1 selected final block, 0: still 5 compressions, and it loses block "
   "5's constant-message free schedule worth ~4,300. (j) more known-constant padded bytes, ~0: byte 255 is the ONLY "
   "structured byte (8*{0..31}, so 3 unconditional zero bits) and ScheduleStepPair17 and ScheduleStepPairWm15Low3 "
   "already harvest it. (k) cheaper length one-hot, ~250: the 256 step functions [j < len] span 256 dimensions with "
   "only 2 degrees of freedom from the Assumptions sums, so 254 witnesses IS the floor. ALSO ZERO: "
   "Paterson-Stockmeyer sqrt(N), base-B digits, wide fan-in AND/IsZero — no small-domain function exists here (every "
   "domain is 2^32) and the only equality structure is the one-hot, already at 1 row per flag. STILL TRUE AND STILL "
   "WORTH KNOWING: XOR4 and XOR5 cannot be done in one row (exactly 192 of the 256 three-input boolean functions are "
   "one-row pinnable; f is BLOCKED iff c_123 != 0 and c_23, c_13, c_12 all lie in {0, -c_123}), and dim{A affine : "
   "deg(A * parity_n) <= 2} = 0 for n = 4,5,6,7 computed EXACTLY OVER Q, so XOR5 as two chained XOR3 rows at 2 "
   "allocations + 2 rows is OPTIMAL."),
  ("~46 — opportunistic only, take it if already editing ScheduleStepPair","THE INTERIOR SCHEDULE PAIRS CARRY 92 "
   "POINTS OF ALLOCATION SLACK. The pair floor is <181,183> and the tree ships <182,183>: 14 xor2 witnesses covering "
   "26 lanes where 13 would suffice, 23 per block across 4 blocks. LastLanePack <1,1> already PROVES one witness can "
   "carry both lanes; it works at the tail only because both halves feed the SINGLE lambda-packed row of "
   "FusedETailPack. Unlocking the interior needs a lambda-fused ScheduleStepPair adder, which costs back one free "
   "lowCarry per pair, so expected value is about +46 with low confidence. DO NOT SPEND A SLOT ON THIS ALONE."),
 ]),
 "keccak-f1600": (307200, 184320, [
  ("0 — CHI IS AT A PROVED FLOOR. I OPENED THIS DIRECTION AND IT IS NOW CLOSED EXHAUSTIVELY.","*** RETRACTION: "
   "AN EARLIER VERSION OF THIS ITEM SAID A PROVED PACKING BARRIER 'DOES NOT APPLY TO CHI' AND POINTED YOU AT "
   "HALVING CHI. THAT WAS WRONG, AND AN EXHAUSTIVE SEARCH HAS SETTLED IT NEGATIVELY. *** The barrier refutation is "
   "real — gadgets that SHARE inputs can pack a cubic target into one row — but it does not reach chi. DO NOT "
   "SPEND A SLOT HERE. *** THE PROOF, SO NOBODY REDOES IT. *** A single row pinning z splits into exactly two "
   "families: FAMILY I (z in the C-slot only) reaches multilinear degree <= 2 ONLY, and FAMILY II (the "
   "non-vanishing multiplier, z = L1/M - L2) reaches degree up to n. The target y_i + c*y_{i+1} is degree 3, so "
   "Family I is excluded outright. For Family II with y_0 on (x0,x1,x2) and y_1 on (x1,x2,x3) — sharing two of "
   "three inputs, exactly the regime where the barrier fails — the encodability system has det A(c) IDENTICALLY "
   "ZERO in c, so the multiplier space is always at least one-dimensional (this IS the shared-input degeneracy). "
   "But a 4x4 minor equals -8c^2, so for every c != 0 the space is EXACTLY one-dimensional and spanned by m* = "
   "(1,0,-2,-1,0), forcing M = 1 - 2x_1 - x_2 up to scale — AND THAT VANISHES ON THE WHOLE FACE x_1=0, x_2=1, four "
   "of sixteen cube points, so the multiplier is not non-vanishing and the row does not pin anything. Proved exact "
   "for all c != 0 in any characteristic other than 2. The distance-2 pair has no solution either. *** AND THE "
   "ALLOCATION COUNT IS ALSO AT ITS FLOOR: *** the nonlinear parts of y_0..y_4 have RANK 5, because each y_i "
   "uniquely owns the monomial x_i x_{i+1} x_{i+2}, and each witness wire contributes at most one dimension — so "
   "at least 5 allocations are needed and the tree already uses exactly 5. CHI COSTS 10 PER 5-BIT LANE ROW AND "
   "THAT IS OPTIMAL. THERE IS ZERO SLACK IN CHI. *** WHY THE WHOLE LOCAL-GADGET DIRECTION IS DEAD HERE: *** an "
   "exhaustive classification of all 65,536 four-input boolean functions finds only 686 single-row encodable, and "
   "NO DEGREE-4 FUNCTION AT ALL — the native gate library collapses from 75%% at n=3 to 1%% at n=4. That one fact "
   "also kills 4-input XOR and any theta/chi fusion. *** SPEND THE SLOT ON THETA INSTEAD: *** theta is 4,480 of "
   "the 7,680 constraints per round, its cost is entirely GF(2)-linearity failing to be F_p-linearity, and the "
   "n=4 collapse says no better LOCAL gadget exists there either — so beating 184,320 needs a STRUCTURAL change, "
   "not a gadget."),
  ("76800 FOR RUNG A, 122880 FOR THE WHOLE PORT — AN ORDERED PLAN, NOT A RESEARCH TASK","THE RECORD TREE AND YOURS "
   "ARE THE SAME TREE. Every file in projs/keccak-f1600/reference/ (byte-identical to the 184320 record) is either "
   "identical to yours or is YOUR FILE WITH `computableWitnesses` DELETED AND THE CIRCUIT SWAPPED. *** soundness, "
   "completeness, mainCost AND isR1CS ALL TRANSFER VERBATIM. *** The record omits computableWitness everywhere "
   "(grep it — zero hits), and that is the ONLY thing you have to supply. Your tree already has 11 per-gadget "
   "computableWitnesses proofs; most port mechanically. "
   "*** TAKE RUNG A FIRST — IT IS 63% OF THE GAP FOR ~10% OF THE WORK. *** "
   "RUNG A: swap ChiLane ALONE to the record's single-row chi. Round 6400 -> 4800, score 230400, -76800. Needs ONE "
   "new leaf computableWitnesses (ChiLane becomes a leaf instead of an AndLane+XorLane composite); ThetaC, "
   "ThetaXor, Theta and KeccakRound cw are ALL UNCHANGED, only Permutation constants move. "
   "RUNG B: add Xor3Lane + Xor5Lane (ThetaC 1280 -> 640). Round 4160, score 199680, -107520. This rung IS the tree "
   "at reference/rival-thryec-199680/, whose ThetaXor is identical to yours, so your ThetaXor cw still transfers "
   "with zero edits. RUNG C: add the theta-D fusion (ThetaXor takes c, not d, and absorbs D into the 3-input row). "
   "Round 3840, score 184320, -122880. "
   "THE CHI ROW, WHICH IS THE WHOLE OF RUNG A: `assertZero ((4*a[i] + 2*b[i]) - (z[i] + 3*a[i] - b[i] - c[i]) * "
   "(4*a[i] + b[i] + c[i] - 3))` with the witness computed at the NATURAL-NUMBER level as "
   "`((env a[i]).val ^^^ ((1 - (env b[i]).val) &&& (env c[i]).val) : N)`. DO NOT solve the row for z with a field "
   "inverse in the generator — compute the semantic value and let completeness prove it satisfies the row. The "
   "multiplier M = 4a+b+c-3 is -3,-2,-2,-1 when a=0 and 1,2,2,3 when a=1, so it never vanishes, and output "
   "booleanity is INHERITED from the inputs rather than asserted — that is why one row replaces two rows plus two "
   "witness vectors. "
   "*** IT NEEDS Fact (p > 3), NOT Fact (p > 2). Copy MainTheorems.lean from the reference FIRST — it adds "
   "`instance : Fact (circomPrime > 3)`. Do that before anything else; it is a safe no-op on its own. *** "
   "*** THE TRAP THAT WILL SILENTLY BREAK THIS: copying a reference file VERBATIM DROPS the "
   "`attribute [local irreducible] main` lines your tree places before its cw proofs (ThetaC, Xor5Lane, ThetaXor, "
   "Theta, KeccakRound, Permutation all have them; the reference has NONE because it has no cw proofs). Those "
   "attributes are what stop `simp [circuit_norm]` unfolding a 3840-operation do-block. RE-ADD EVERY ONE. *** "
   "Also delete ThetaD.lean, XorLane.lean and AndLane.lean once Rung C lands — they are orphans in the reference "
   "(nothing imports them) but the lakefile globs all of Solution/, so they still cost elaboration and still carry "
   "cw proofs you would have to keep green for nothing. "
   "BUILD AFTER EVERY SINGLE FILE, DO NOT BATCH. Commit a green build at whichever rung you reach; each rung is "
   "independently submittable and each strictly beats 307200. "
   "ON ELABORATION RISK: every symbolic offset SHRINKS by 40%, and both halves are independently known to fit — the "
   "reference circuit was accepted by the leaderboard, and your tree already carries the cw layer at 1.67x the "
   "operation count. Do NOT reach for `decide +kernel` here: there is no `decide` in either tree, the boolean-cube "
   "exhaustions use `rcases <;> ring` and `linear_combination` which are already the cheap form, and introducing "
   "`decide` would be a regression."),
  ("48 to 15360 — A NEW PROBLEM STATEMENT, AND THIS CORPUS PREVIOUSLY TOLD YOU NOT TO LOOK HERE","RE-WIRE THETA AS "
   "A SHORTEST-LINEAR-PROGRAM IN THE 3-INPUT-XOR BASIS. THE REFRAMING IS THE FINDING: a value costs a row exactly "
   "when it must be a bare bit-valued witness, and Xor3Lane pins z = a XOR b XOR c in ONE row, while an input must "
   "be an already-materialised bit or a constant ('a+b' is NOT a legal input). So theta's cost IS the minimum gate "
   "count of a straight-line program over {XOR of <=3 materialised bits} producing the 1600 theta outputs from the "
   "1600 state bits. THE CORPUS ENTRY SAYING 'SLP MINIMIZATION BUYS EXACTLY ZERO HERE' IS RIGHT FOR THE GF(2) "
   "CHALLENGES AND WRONG FOR THIS ONE — read the theta-as-SLP entry before you believe it. COST LAW: round score = "
   "153,600 + 48h with h the helper-gate count. The standing 184,320 is h = 640, i.e. 320 column-slices x (one "
   "intermediate + one parity) + 1,600 outputs — the TEXTBOOK circuit re-basis'd into 3-input gates, not an SLP "
   "optimum. PROVED FLOOR: exhaustively on the real w=64 index structure, a target is a 3-XOR of other targets and "
   "raw bits in EXACTLY 4 ways (same-column siblings), 'target = 2 targets + <=1 input' has ZERO solutions and "
   "'target = 3 targets' has ZERO solutions, so every column-slice needs at least one first-partial helper and "
   "theta >= 1,920 gates/round = 168,960. THE RECORD SITS 15,360 ABOVE THAT. EVIDENCE THE CONSTRUCTION IS NOT "
   "OPTIMAL: on the 3-column analogue — verified structurally faithful, same target-relation census as w=64 — the "
   "2-helpers-per-column construction gives 21 gates and SAT FINDS 20; the seeds-only sub-problem goes 9 -> 8. THE "
   "MECHANISM, WHICH IS THE PART TO CARRY OVER: NEVER MATERIALISE A CLEAN COLUMN PARITY. Carry a RIDER bit through "
   "the helper chain so it lands as the seed target's own A-bit, and assemble the last column's parity INSIDE a "
   "target gate from a shared partial plus an already-computed target (g1 = A[1][1] XOR A[1][3] XOR A[2][3] with "
   "the rider from a foreign column, ending at g6 = C[0] XOR C[1] XOR A[2][3] which IS the target A'[2][3]). "
   "PRICING: h = 639, ONE HELPER SAVED PER ROUND, is 184,272 — A STRICT IMPROVEMENT AND THEREFORE A RECORD, SINCE "
   "A TIE IS NOT. h = 533 is 179,184. h = 320 is 168,960. *** HOW TO SEARCH, AND IT IS NOT WHAT WAS TRIED BEFORE: an exact SAT encoding settled the 3-column analogue (21 -> 20) and STALLED past an hour on the 5-column one. Use the PUBLISHED HEURISTIC instead — extend Boyar-Peralta by enumerating ALL TRIPLES i<j<k as candidate new base elements alongside all pairs, score each by the resulting distance-to-target vector, and WHEN CANDIDATES TIE BREAK RANDOMLY AND RESTART THE WHOLE SEARCH MANY TIMES. The randomised tie-breaking plus restarts is where the gain comes from, not the greedy step. Algorithm 3 (PickNewBaseElementXOR3) of PMC10807753; original 3-input extension eprint 2021/1400; existing code at imada.sdu.dk/~joan/xor/Improved2.cc and github demirmehmet0/SBP. ONE ADAPTATION IN OUR FAVOUR: that literature prunes hard on a DEPTH bound because it targets low-latency hardware — WE HAVE NO DEPTH CONSTRAINT, only gate count, so drop the depth pruning and the search has strictly more freedom than the published runs. *** SOUNDNESS OBLIGATION: NONE NEW — every gate is still "
   "Xor3Lane with the same row identity, the same non-vanishing multiplier and the same free output booleanity; "
   "ONLY THE WIRING CHANGES. Implementation is a machine-generated wiring table replacing ThetaC and ThetaXor, plus "
   "one cost constant. HONEST LIMIT, DO NOT OVERSELL IT: the 20-gate win is on the 3-column analogue, not on "
   "Keccak's theta; it proves the 2-helpers-per-column FAMILY is not optimal for theta-shaped maps, and the real "
   "saving may be O(1) rather than proportional. TAKE THE SMALL VERSION FIRST — one helper is already a record."),
  ("122880","PORT THE 184320 RECORD AND PROVE computableWitness — THIS IS THE WHOLE JOB ON THIS SLUG. Your seed "
            "Solution/KeccakF1600/ is the 307200 BASELINE, not the record: it has no Xor3Lane.lean and its allocations "
            "are 153600. The 184320 record is in reference/ and it OMITS computableWitness, which configs lists in "
            "theorem_names, so it cannot be submitted as-is. THE PORT IS SMALL AND MECHANICAL: diffing baseline against "
            "record file by file, AndLane/XorLane/ThetaD differ ONLY by the deleted computableWitnesses block and ThetaC "
            "only by that block plus a Fact (p > 3) instance. The real work is TWO NEW LEAF PROOFS — "
            "Xor3Lane.computableWitnesses and ChiLane.computableWitnesses — and both gadgets are exactly "
            "`witnessVector 64 ...; Circuit.forEach ... assertZero`, the SAME SHAPE as the baseline's XorLane, whose "
            "proof at XorLane.lean:104-135 is about 30 lines and transposes directly (h_input.1 / .2.1 / .2.2 for three "
            "inputs). Everything else is recomposition — Xor5Lane over two Xor3Lane subcircuits, ThetaXor taking Inputs "
            "field c instead of d, Theta dropping the ThetaD step — plus verbatim copies of Cost.lean, "
            "PermutationDefs.lean, PermutationCost.lean and Main.lean from reference/."),
  ("1","AND YOU MUST BEAT 184320, NOT MATCH IT. ordian already holds 184320, and a TIE DOES NOT DISPLACE A RECORD — "
        "confirmed on the gf2-k12 challenge, where a baseline-equal submission verified but never reached the "
        "leaderboard. So pair the port with at least ONE point of saving. Where it is NOT: chi is at the proved "
        "multiplicative floor (1 row per state bit, MC(chi_5) = 5 is SAT-proved), rho/pi/iota are free, and the "
        "input/output boundary is exactly 0. ALL remaining slack is THETA's 2240 per round — of which 320 are Xor5 "
        "INTERMEDIATES (the t = a^b^c of each 5-input column parity) and 320 the C bits, with D already fused away."),
 ]),
 "rsa-pkcs1v15-sha256-4096-65537": (321769, None, [
  ("218 — ONE PARAMS FILE, AND THE CORPUS ENTRY SAYING THIS WAS ALREADY HALF-TAKEN IS WRONG","BALANCE THE q AND n "
   "LIMBS. Params24.lean's live cap functions nfBalMiddleN24 and nfBalFirstN24 use WindowCaps.limbCap — the "
   "UNSIGNED 2^B - 1 — for BOTH operands. Balancing (q' = q - 2^23, n' = n - 2^23) is affine, and the cross terms "
   "are affine too because the evaluation point is a compile-time constant, so the q*n coefficient cap drops by "
   "log2(4/3). PRICED AGAINST A CAP MODEL THAT REPRODUCES wtableBalMiddle24 ENTRY FOR ENTRY (sum 1152, cost 2,267): "
   "balancing both operands gives 2,255, i.e. -12 PER MIDDLE SQUARING. The first square additionally uses limbCap "
   "on the a^2 side (nfBalFirstP24 uses limbCap where nfBalMiddleP24 uses fixedBalCap), and balancing the signature "
   "is free since the shift is affine in the input bytes and the cross term 2S*s' is a constant-vector convolution "
   "— first-square carries 2,303 -> ~2,255. TOTAL 14*12 + 48 + 2 = 218. DO NOT BELIEVE THE 'PARTIALLY TAKEN, ~98 "
   "REMAINING' CLAIM: the -120 that took 321,889 -> 321,769 was -8 per squaring and lived ENTIRELY in the "
   "WindowSquare term (380 -> 372 via 10*(m/gw)-4); the live carry cost is STILL 2,267, which is exactly what the "
   "unsigned caps give. OBLIGATION: re-prove the signed q*n coefficient bound — the Nf monotonicity chain in "
   "Params24.lean and the GVXHyps no-wrap condition with the new OFF constants. THIS IS A CAP-FUNCTION AND "
   "REGENERATED-TABLE CHANGE IN ONE FILE, the same shape as the -92 that landed on secp256k1. EVERYTHING ELSE HERE "
   "IS EXHAUSTED: every charged carry cell in all three tables already sits at ceil(log2(OFF_P + OFF_N)) with ZERO "
   "slack, the term counts are exact per-position, and the final-block grouping is PROVED OPTIMAL by a DP over all "
   "consecutive-group partitions. Do not sweep those again."),
  ("8540 — SETTLE THE ADDITION CHAIN; THE PROOF THAT BLOCKS IT IS MISSING","THE ONLY STRUCTURAL LEVER LEFT ON "
   "THIS CHALLENGE. The chain is 1 first squaring + 14 middle squarings + 1 fused ternary final = 16 reductions "
   "to reach 65537 = 2^16 + 1, and 79.7% of the whole circuit is range checks at 2 score per certified bit "
   "across those 16 steps, so the ONLY way down is FEWER REDUCTIONS. A mid-chain TERNARY step (a*a*b, residue "
   "unknown so it pays its own 4,096-bit range check) models at about 30,900 at B=24 from sqMulModBalToCount, "
   "against 39,404 for two binary steps. A chain with b = 13 squarings and t = 2 ternary steps has exponent "
   "bound 2^13 * 3^2 = 73,728 >= 65537 and would cost about 313,227 — ABOUT -8,540. Optimality.lean:52 asserts "
   "this is the only cheaper configuration AND that Chain.not_reachable_of_prod_73728 proves 65537 is "
   "UNREACHABLE in it — BUT THAT PROOF IS NOT IN THE TREE. Optimality.lean is now entirely a comment, its "
   "Optimality/ subdirectory has been removed, and its numerals refer to a superseded 326,297 design. SO SETTLE "
   "IT: either exhibit a length-15 chain reaching 65537 with 13 squarings and 2 ternary steps, in which case "
   "build it, or PROVE 65537 unreachable there and say so, which retires the lever permanently and is worth "
   "recording either way. THE -8,540 IS MODELLED, NOT MEASURED: the ternary-step cost assumed about 58 groups "
   "and W about 34 for a 3m-1 = 512-position equality check, and the gadget was not built. DO NOT BOTHER "
   "RETUNING THE CARRY TABLES — all three (wtableBalMiddle24, wtableFbal, wfFinal16Table) were checked element "
   "by element and every entry already equals the pointwise minimum, group width is maximal at gf = 9 (gf = 10 "
   "gives 2^268 > p), group placement is optimal, and the triangular-term-count pattern is already banked in "
   "wconv. Those sweeps are worth ZERO here. NOTE ALSO that CostFloor.lean:45 asserts 326,297 and "
   "Optimality.lean quotes 321,889 while Main.lean sums to 321,769; those files are in a dead import subtree, "
   "and rec.tar.gz in that directory is STALE."),
  ("1450","The q*n limb caps are UNSIGNED (limbCap = 2^B - 1) while the a^2 caps are balanced (fixedBalCap ~ 2^(B-1)), and "
          "q*n DOMINATES the coefficient cap: peak 2^55.74 against 2^54.42 balanced. Witness q's limbs offset "
          "(q_i = q_i' + 2^23) and offset n's limbs affinely (free — n's limbs are already affine in the input bytes). The "
          "correction Q(c)N(c) = Q'(c)N'(c) + 2^23*U(c)*(Q'(c)+N'(c)) + 2^46*U(c)^2 is ENTIRELY AFFINE because c is a fixed "
          "compile-time evaluation point, so it stays one product row. 1.32 bits x 2 x 37 carries x 15 squarings."),
 ]),
}
BIG_MIN = 500   # a big-win slot spent below this is a wasted slot: the small-win fleet already covers it
def _gain(label):
    m = re.match(r"\s*~?(\d+)", label)
    return int(m.group(1)) if m else None
def workqueue_block(slug, big):
    wq=WORKQUEUE.get(slug)
    if not wq: return ""
    derived,pred,items=wq
    now=tg[slug]["target"]           # live, so the header cannot go stale as records land
    # Split the queue by purpose. Handing the SAME cheapest-first list to both fleets is what made the
    # ambitious fleet spend every slot on 8- and 22-point parameter tweaks while the structural items
    # sat untouched. Items with no leading number (discipline notes, null results) go to BOTH.
    sized  = [(g,t2,t) for (t2,t) in items for g in [_gain(t2)]]
    if big:
        keep = [(g,t2,t) for (g,t2,t) in sized if g is None or g >= BIG_MIN]
        keep.sort(key=lambda x: -(x[0] or 10**9))          # largest first; unnumbered notes lead
        head=(f"\n\nPRIORITY WORK QUEUE — DERIVED FROM THIS SOLUTION'S OWN SOURCE AND COST PROOFS, NOT SPECULATION.\n"
              f"Each item was worked out against the {derived} solution, with the saving predicted from its own measured\n"
              f"primitive costs. These are NOT literature candidates to evaluate — they are work items. They are ordered\n"
              f"LARGEST FIRST, and that is the order you should attempt them.\n"
              f"*** THIS IS A BIG-WIN SLOT. DO NOT SPEND IT ON ANYTHING WORTH LESS THAN {BIG_MIN} — a separate fleet is\n"
              f"already working the small mechanical items, so landing one here is pure duplication and the slot is\n"
              f"wasted. Items below {BIG_MIN} have been REMOVED from this list on purpose; if you find yourself with\n"
              f"time left over, go DEEPER on the largest item rather than sideways onto a cheap one. A partial but\n"
              f"compiling step toward the largest item is worth more than a complete small one. ***\n")
    else:
        keep = [(g,t2,t) for (g,t2,t) in sized if g is None or g < BIG_MIN]
        keep.sort(key=lambda x: (x[0] if x[0] is not None else -1))
        head=(f"\n\nPRIORITY WORK QUEUE — DERIVED FROM THIS SOLUTION'S OWN SOURCE AND COST PROOFS, NOT SPECULATION.\n"
              f"Each item was worked out against the {derived} solution, with the saving predicted from its own measured\n"
              f"primitive costs. These are NOT literature candidates to evaluate — they are work items. They are ordered\n"
              f"CHEAPEST-AND-SAFEST FIRST, so if you can only land one, take the first one you can fully prove.\n"
              f"*** THIS IS A SMALL-WIN SLOT. The large structural items are deliberately NOT listed here — another\n"
              f"fleet is working them. Your job is a CERTAIN, VERIFIED reduction, however small. ***\n")
    if not keep:   # never emit an empty queue — fall back to the whole list rather than no guidance
        keep = sorted(sized, key=lambda x: -(x[0] or 10**9)) if big else sorted(sized, key=lambda x: (x[0] if x[0] is not None else -1))
    if now!=derived:
        head+=(f"*** THE SEED HAS MOVED ON FROM {derived} TO {now} SINCE THESE WERE DERIVED — A GAP OF "
               f"{derived-now}. TREAT EVERY FIGURE BELOW AS STALE UNTIL YOU CHECK IT. ***\n"
               f"MANY OF THESE ITEMS QUOTE LEDGERS THAT NO LONGER MATCH THE TREE, and an item whose premise has\n"
               f"moved is usually PARTLY OR WHOLLY DONE. BEFORE IMPLEMENTING ANY ITEM, GREP THE SEED FOR THE\n"
               f"CONSTANT IT QUOTES: if the item says a gadget costs X and the tree says Y, the item is out of\n"
               f"date and its predicted saving is NOT what you will get. Re-derive the saving from the CURRENT\n"
               f"constants before committing to the work, and say in your summary which figure you used.\n"
               f"CHECK THE SEED BEFORE IMPLEMENTING ANY ITEM — re-deriving work already in the tree wastes the whole job.\n"
               f"The mechanisms and bound arithmetic below remain valid regardless of which have landed; only the\n"
               f"predicted savings are relative to {derived}. A quick way to tell which non-native sites are still\n"
               f"UNFOLDED: an unfolded site uses the `gfQuad`/`gfWideFat` grouped-carry path and witnesses a full 4-limb\n"
               f"quotient with a ~252/256 NormalizeImplicit on it; a folded one uses `gfFold` with ONE carry and a single\n"
               f"quotient wire. Grep for those and work the sites that are still on the unfolded path.\n")
    elif pred and big:
        head+=f"Implementing all of them is predicted to reach about {pred}.\n"
    return head+"\n".join(f"  [~{t2} score] {t}" for (g,t2,t) in keep)
def seed_cost(slug, inst):
    """(allocations+constraints) actually present in projs/<slug>/Solution/<inst>/Main.lean.

    Returns None if the defs are not plain numeric literals -- callers must treat None as
    "unknown", never as "equal to the target". THIS IS READ FROM projs/, WHICH IS WHAT
    tick.py SEEDS JOBS FROM (`proj_dir = f"projs/{slug}"`). Do not switch it to records/:
    records/ is the leader's tree and is NOT always copied into projs/ -- the computableWitness
    gate in check_records.py deliberately skips the copy, and that divergence is exactly the
    thing this function exists to detect.
    """
    p = f"projs/{slug}/Solution/{inst}/Main.lean"
    try: src = open(p).read()
    except OSError: return None
    got = {}
    for name in ("allocations", "constraints"):
        m = re.search(r"def\s+" + name + r"\s*:\s*Nat\s*:=\s*(\d+)\b", src)
        if not m: return None
        got[name] = int(m.group(1))
    return got["allocations"] + got["constraints"]

os.makedirs("prompts",exist_ok=True); os.makedirs("prompts_small",exist_ok=True)
def tmpl(inst,t,framing,ideas,show_target=True,wq="",seed=None):
    # NEVER state the target as if it were the seed's cost. They coincide only when the last
    # reseed succeeded; when it did not, saying "your seed scores {t}" is a flat lie and the job
    # spends its whole budget confused about what it is holding.
    divergent = seed is not None and seed != t
    if show_target and not divergent:
        goal=(f"scoring allocations+constraints = {t}, defining ALL\n"
              f"required declarations INCLUDING `computableWitness`, and it passes the verifier. GOAL: a NEW solution scoring\n"
              f"STRICTLY BELOW {t} that STILL fully verifies.")
    elif show_target:
        goal=(f"scoring allocations+constraints = {seed}, defining ALL\n"
              f"required declarations INCLUDING `computableWitness`, and it passes the verifier.\n"
              f"\n"
              f"*** READ THIS BEFORE ANYTHING ELSE — YOUR SEED IS NOT THE RECORD. ***\n"
              f"The seed you have been given scores {seed}. The standing record is {t}, a gap of {seed - t}\n"
              f"({100.0*(seed-t)/seed:.0f}% of your seed). The record holder's tree is NOT in `Solution/` because it omits\n"
              f"`computableWitness` and is therefore not a valid submission — but its circuit IS reproducible. It is\n"
              f"supplied to you as read-only context in `reference/*.lean.txt`.\n"
              f"YOUR JOB IS NOT TO INVENT A NEW OPTIMIZATION. It is to PORT the reference circuit onto this valid\n"
              f"baseline and re-prove `computableWitness` (adapt the one already in your seed). Read `reference/`\n"
              f"FIRST, diff it against `Solution/`, and reproduce its structure. Anything strictly below {seed} is\n"
              f"progress; reaching {t} recovers the full gap; below {t} takes the record.\n"
              f"GOAL: a NEW solution scoring STRICTLY BELOW {seed} that STILL fully verifies.")
    else:
        # small-win: no numeric anchor — the seed IS the SOTA; beat it by any margin
        sota=("seed IS the current state of the art (SOTA)." if not divergent else
              f"seed is NOT the state of the art — it scores {seed} against a standing record of {t}. The record\n"
              "tree is read-only context in `reference/*.lean.txt` (it omits `computableWitness`, so it cannot be\n"
              "submitted as-is); port from it rather than inventing.")
        goal=("defining ALL required declarations INCLUDING `computableWitness`, and it passes the verifier — this\n"
              f"{sota} GOAL: ANY new solution that scores STRICTLY LESS than the\n"
              "seed and STILL fully verifies. There is no number to hit — beat the seed by ANY margin, however small; a\n"
              "single-unit fully-verified reduction is a win. Read `allocations`+`constraints` in the seed to know what to beat.")
    return f"""You are optimizing a zkGolf circuit in the Clean Lean-4 framework (clean pinned @ 041c6e7e, Lean v4.28.0, Mathlib v4.28.0).

TARGET: `Solution/{inst}/` contains a VALID, VERIFIED seed {goal} {framing}

Rewrite `main` (and helpers); set `@[reducible] def allocations` and `def constraints` to the true new cost; KEEP
+ re-prove EVERY required declaration: `main`, `elaborated`, `soundness`, `completeness`, `mainCost`, `isR1CS`, and
**`computableWitness`** (MANDATORY — the verifier runs `lean4export` over the config theorem list and ABORTS
(exit 134) if it is missing; never drop or rename it).

HARD REQUIREMENTS: do NOT change `Challenge/`; keep exact signatures; NO `sorry`/`admit`/`native_decide`; permitted
axioms only (`propext`,`Quot.sound`,`Classical.choice`, the challenge `hCircomPrime`, and `Specs.*.hPrime` if the seed
uses it); `mainCost` proves `circuitCost main ⟨allocations,constraints⟩`; `isR1CS` holds; keep the build green.
If a full rewrite is too big, make the single highest-impact FULLY-PROVED reduction keeping all declarations.

MANDATORY SELF-VERIFICATION BEFORE RETURNING (a submission that only *looks* right but fails the real Lean build is
WORSE than no submission — it wastes a record attempt). You MUST, in your own environment:
  1. Run `lake build` on the full Solution and confirm it compiles with ZERO errors (warnings-as-errors too). Do not
     trust that edits compile — actually build them.
  2. Run `#print axioms main` (and for `soundness`,`completeness`,`isR1CS`,`computableWitness`) and confirm the printed
     axioms are a SUBSET of the permitted set above — in particular NO `sorryAx` and no newly-declared `axiom`.
  3. Confirm no `opaque`/trusted-predicate shortcut left a required theorem vacuously true or unprovable at the config layer.
If you CANNOT achieve a clean build + clean axioms at your target cost, DO NOT return the broken lower-cost attempt —
instead return the best solution you DID build and axiom-check successfully, even if its cost is higher (a verified
higher cost beats an unverified lower one). Never return code you have not compiled.
- FILE LIMIT: the zkGolf submission accepts at most 1000 .lean files (plenty of headroom). Splitting proofs across many focused modules is fine; do NOT contort the circuit to minimize file count. Optimize for LOWEST cost (allocations+constraints), not fewest files.

OPTIMIZATION IDEAS (verify before use): {ideas}{wq}
Return the complete updated `Solution/{inst}/` files, fully compiling."""
for slug,inst in INST.items():
    t=tg[slug]["target"]
    sc=seed_cost(slug,inst)
    if sc is None:
        print(f"WARN {slug}: could not read allocations/constraints from the seed's Main.lean — "
              f"prompt falls back to asserting the target ({t}) is the seed cost. VERIFY BY HAND.")
    elif sc != t:
        print(f"SEED DIVERGENCE {slug}: projs/ seed scores {sc}, target is {t} (gap {sc-t}). "
              f"Prompt now states both and points the job at reference/.")
    open(f"prompts/{slug}.md","w").write(tmpl(inst,t,"Be ambitious — aim for a large structural reduction.",IDEAS[slug],wq=workqueue_block(slug,True),seed=sc))
    open(f"prompts_small/{slug}.md","w").write(tmpl(inst,t,"Prefer a SMALL, safe, guaranteed-provable reduction; certainty of a verified result matters most.",IDEAS[slug],show_target=False,wq=workqueue_block(slug,False),seed=sc))
kref="\n\nREFERENCE: `reference/*.lean.txt` is the record which hits the target cost but OMITS `computableWitness` (now invalid). Reproduce its circuit optimization on the valid baseline AND add a fully-proved `computableWitness` (adapt the baseline's). Reference files are context only, not compiled."
for f in ("prompts/keccak-f1600.md","prompts_small/keccak-f1600.md"):
    if os.path.exists(f): open(f,"a").write(kref)

# Cross-pollination: RSA, secp-scalar-mul and secp-fixed-base all bottleneck on the SAME
# primitive — non-native bigint arithmetic mod a fixed prime (limb mul + reduce + carry/range
# checks). Each challenge evolved a gadget the others lack. `reference/*.lean.txt` holds the
# DONOR gadget from the sibling challenge (context only, NOT compiled); port its idea into this
# Solution if it lowers cost, keeping every required theorem incl. computableWitness fully proved.
XPOLL={
 "rsa-pkcs1v15-sha256-4096-65537":
   "CROSS-POLLINATION: `reference/*.lean.txt` are the `EqViaCarriesFlex`/`GroupedFlex`/`FlexInstances` "
   "gadgets from the secp256k1 solutions — a FLEXIBLE limb-width equality/carry check. This RSA solution "
   "uses fixed-width `GroupedEqXV`. If the flexible-limb packing lets the 4096-bit mul-reduce equality use "
   "FEWER/wider limbs (fewer range-check rows), port it into `MulMod`/`EqViaCarries` here. Re-prove all theorems.",
 "secp256k1-scalar-mul":
   "CROSS-POLLINATION: `reference/*.lean.txt` are the `EqViaCarriesFlex`/`GroupedFlex`/`FlexInstances` "
   "gadgets from the FIXED-BASE secp solution — a FLEXIBLE limb-width equality/carry check this solution "
   "lacks (it uses fixed `GroupedEqXV`). If flexible limb widths reduce the Fp mul-mod carry/range rows, "
   "port the idea into `MulMod`/`EqViaCarries`. Re-prove all theorems incl. computableWitness.",
 "secp256k1-fixed-base-scalar-mul":
   "CROSS-POLLINATION: `reference/*.lean.txt` are secp256k1-scalar-mul's `GroupedEqXV`/`GroupedEqX` and "
   "`MulModTargetW`/`MulModVariants` — a richer multiply-target + XV equality-grouping family this fixed-base "
   "solution never adopted. If the XV grouping or a MulModTarget variant lowers this solution's non-native "
   "mul-mod cost below the `Flex` path, port it. Re-prove all theorems incl. computableWitness.",
}
for slug,txt in XPOLL.items():
    f=f"prompts/{slug}.md"
    if os.path.exists(f) and os.path.isdir(f"projs/{slug}/reference"): open(f,"a").write("\n\n"+txt)

# Rival submissions harvested by pull_others.py. The seed is always the CURRENT RECORD (ours or a
# competitor's), so without this we only ever see the #1 entry and never anyone else's approach.
for slug in INST:
    rivals=sorted(glob.glob(f"projs/{slug}/reference/rival-*"))
    if not rivals: continue
    who=", ".join(os.path.basename(d).replace("rival-","").replace("-"," @ ") for d in rivals)
    blk=("\n\nRIVAL SOLUTIONS: `reference/rival-<author>-<score>/` holds another competitor's FULL submission to this "
         f"same challenge ({who}), as .lean.txt — context only, NOT compiled and NOT part of your Solution. It is a "
         "DIFFERENT line of attack from the seed, which is always the current record. READ IT. A worse TOTAL score can "
         "still hide a better individual gadget: the score sums the whole circuit, so a solution 10% behind overall may "
         "still beat the seed on one primitive. Look specifically for gadgets the seed lacks, different limb geometry, "
         "different exception handling, and anything that costs fewer rows for the same job. Port what wins and re-prove "
         "it; ignore what does not. MANIFEST.txt in each directory records the author, score and submission id.")
    for f in (f"prompts/{slug}.md", f"prompts_small/{slug}.md"):
        if os.path.exists(f): open(f,"a").write(blk)

# Externally-researched techniques (research.json, refreshed by periodic web research) — injected
# into BOTH big- and small-win prompts. These are candidate ideas from the ZK literature; this
# challenge is R1CS with cost = allocations+constraints, so Aristotle MUST verify each applies here.
for slug in INST:
    bullets=[b for b in RESEARCH.get(slug,[]) if isinstance(b,str)]
    bullets+=[b for b in RESEARCH.get("_common",[]) if isinstance(b,str)]  # cross-cutting: applies to every challenge
    if not bullets: continue
    block="\n\nRESEARCHED TECHNIQUES (from external ZK literature — VERIFY each maps to this R1CS cost model before use; ignore lookup/GKR/sum-check-only tricks that don't lower allocations+constraints here):\n"+"\n".join(f"- {b}" for b in bullets)
    for f in (f"prompts/{slug}.md", f"prompts_small/{slug}.md"):
        if os.path.exists(f): open(f,"a").write(block)
print("prompts generated")
