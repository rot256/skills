#!/usr/bin/env python3
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
 "secp256k1-fixed-base-scalar-mul": (49218, 49536, [
  ("2060 — LOWEST-RISK STRUCTURAL WIN, DO THIS FIRST","WITNESS NARROW, VIEW WIDE: MOVE lambda AND x TO B = 32 AT THE "
   "SQUARING SITE ONLY. Materialising a 256-bit value costs EXACTLY 512 at any limb width (NormalizeImplicit is "
   "<m*(B-1), m*B>, so 4+508 = 8+504), so limb width is FREE TO CHOOSE and what it changes is the MAGNITUDE BUDGET "
   "that sets the quotient and carry widths — and those are LINEAR in limb width at 2 score per bit. Per stageX site, "
   "4x64 -> B=32: materialisation 512 -> 512 (a wash), lambda^2 <7,7> = 14 -> <15,15> = 30, quotient 67 bits (134) -> "
   "38 bits (75), grouped carry W=98 (196) -> W=70 (140). Stage 856 -> 758 = -98, across ~21 sites (19 ext + stageO2 "
   "in the start fold + the ChainExtFold inside FinalAdd) = -2,060. THE PRE-FOLD POSITIONS DROP FROM 4*2^128 = 2^130 "
   "TO 8*2^64 = 2^67, so folded positions go 2^163 -> 2^100 and a group of g=4 becomes admissible where 64-bit limbs "
   "force g=2 — that is where the carry saving comes from. CRITICAL: DO NOT CONVERT THE TABLES OR THE SELECTS. Witness "
   "lambda and x as BigInt 8 at B=32 and define the 4x64 view by the FREE AFFINE RECOMBINATION lam64[i] = lam32[2i] + "
   "2^32*lam32[2i+1], so stageC1 — whose multiplicands include SELECTED table limbs and therefore genuinely need "
   "64-bit granularity — is completely untouched. Pushing the table to 8x32 columns is a measured LOSS: +60 "
   "allocations per select (15 outer cells x 4 extra columns) = +2,520 against ~-1,600. New proof burden is ONE "
   "FoldParams instance and an m=8 interpolatedMul call; the group-law proofs do not change at all."),
  ("928 — A PURE DUPLICATION THE CIRCUIT IS PAYING FOR TWICE","DELETE BOTH Canonicalize.main CALLS AND REUSE THE "
   "DECOMPOSITION THE CHAIN ALREADY COMPUTES. canonicalizeCost <263,265> is 12 (conditional reduction) + 8 "
   "(ValidP.tail) + 508 BIT DECOMPOSITION (96.2%), and that 508 is 4 x ToBitsAffine 63 (ValidP.lean:75) which is "
   "CONSTRAINT-FOR-CONSTRAINT IDENTICAL to RangeCheck.main — the only difference is that RangeCheck returns Unit "
   "instead of the bit vector. ChainFold.stageX:297 and ChainFinishFold:37 EACH ALREADY CALL NormalizeImplicit on the "
   "final chord x and y, so the circuit ALREADY COMPUTES BOTH 256-BIT DECOMPOSITIONS, THROWS THE BITS AWAY, AND THEN "
   "PAYS 1,016 TO RECOMPUTE THEM. EDITS: add NormalizeImplicitBytes (NormalizeImplicit with RangeCheck swapped for "
   "ToBitsAffine, returning the bits; identical cost <252,256>); use it in the FINAL stageX/stageYF only, leaving the "
   "in-loop ones alone; append ValidP.tail to each (+16); move the exceptional-branch mux at FinalAdd.lean:935 from 8 "
   "limbs to 64 bytes (+112 — the special branch supplies CONSTANT byte vectors, free, cf. Comb.zeroBytes); delete "
   "Comb.lean:211-212 (-1,056). OBLIGATION: strengthen FinalAdd.ImplicitSpec's CompactAdd.NormPoint from Normalized "
   "limbBits (< 2^256) to Fe.Valid (< p) for the chord coordinates — the honest witness is ALREADY canonical "
   "(x3Val/y3Val are `... % P256`, CompactAdd.lean:550), so this restates a true fact rather than adding arithmetic; "
   "the isInf = 1 -> bytes = 0 clause must be restated at byte level. IF THAT PROOF PROVES TOO HEAVY, TAKE THE CHEAP "
   "FALLBACK FOR -24 AND ALMOST NO WORK: drop the b/r/GroupedFlex conditional-reduction machinery and assert "
   "ValidPBytes.circuit final.x directly — sound (strictly stronger) and complete (honest final.x is reduced). ALSO "
   "DELETE, ZERO SCORE BUT REAL BUILD TIME: the explicit FinalAdd.main/circuit/screenedCost path <1611,1620>, "
   "CheapIncompleteAdd, selectConstPoint, CombSound.finalAdd_assumptions:714, CombCW.lean:180-300."),
  ("11115 — THE BIG ONE, ATTEMPT AFTER THE TWO ABOVE LAND","THE SQUARES TELESCOPE: STOP MATERIALISING THE ACCUMULATOR "
   "x ENTIRELY. Unroll x_j = lambda_j^2 - x_{j-1} - xT_j and every intermediate x-coordinate is an ALTERNATING SUM OF "
   "SQUARES: x_j = sum_{i<=j} (-1)^(j-i) lambda_i^2 + (-1)^j x_0 + sum_i (+-xT_i). interpolatedMul returns its "
   "convolution positions as AFFINE WIRES and affine recombination is free, so EVERY x_j IS AVAILABLE FOR FREE AS AN "
   "UNREDUCED CONVOLUTION once the lambda_i^2 exist. The state becomes THE LAMBDAS ALONE. Per window at B=32: witness "
   "lambda_j as BigInt 8, range-checked 8x32 = 256 bits, <8,0> + <248,256> = 512; lambda_j^2 by interpolatedMul m=8 = "
   "<15,15> = 30, 15 positions each < 8*2^64 = 2^67; x_j := the telescope, FREE, 15 positions < 21*8*2^64 = 2^71.4, "
   "pre-folded onto 8 positions with cF = 2^32+977 (free) at < 2^104.4; then ONE reduction site, the slope identity "
   "in T-relative implied-y form using the tree's existing Chain.impliedY trick: lambda_j*(xT_j - x_{j-1}) + "
   "lambda_{j-1}*(xT_{j-1} - x_{j-1}) = yT_j + yT_{j-1} mod p, whose products are lambda_j * x_{j-1}^fold (30), "
   "lambda_{j-1} * x_{j-1}^fold (30) and lambda_j * xT_j (mixed radix, 8 coeffs at 2^32 x 4 at 2^64 -> 14 positions, "
   "28, SHARED between steps j and j+1) = 118. PER WINDOW 512 + 118 + 1 + 223 (quotient ~110.5 bits) + 287 (ONE "
   "carry, W ~ 143) = 1,141 AGAINST 1,734. Over 20 chain steps 34,680 -> 22,820, plus one final degree-2 "
   "materialisation of x_20 (745, no new muls). MAGNITUDE BUDGET, CHECK IT FIRST: LHS positions < 8*2^32*2^104.4*2 = "
   "2^140.5; one fold round 15 -> 8 gives positions 0..6 < 2^173.5 and position 7 < 2^140.5; g=3 gives 2^237.5 < "
   "2^254 OK while g=4 gives 2^269.5 and FAILS, so g=3 IS FORCED, leaving L=9 in groups of 3 = ONE range-checked "
   "carry. THIS IS ILLEGAL AT B=64 — a degree-3 product there has 10 positions and folding to 4 reaches 2^262, over "
   "the native field, while folding to 6 forces g=1 and FIVE carries of 165 bits = 1,650. SO DO THE B=32 ITEM FIRST. "
   "PROOF: the group law x_j = lambda_j^2 - x_{j-1} - xT_j now holds BY DEFINITION rather than by assertion — that is "
   "exactly the 512 you stop paying — and the induction is that, given y_{j-1} = lambda_{j-1}(xT_{j-1} - x_{j-1}) - "
   "yT_{j-1} is the true y, the asserted slope identity plus xT_j != x_{j-1} forces lambda_j to be the chord slope. "
   "THE NON-COLLISION SIDE CONDITIONS ARE THE TREE'S EXISTING OrderFacts/OrderFactsChain OBLIGATIONS, UNCHANGED. The "
   "genuinely new work is mechanical: a GroupedFlex instance at L=9, B=32, g=3 with degree-3 Nf/OFFf/Wf bounds (a "
   "FoldParams-style file, all `by decide`) and a generalised interpolatedMulGen n1 n2 returning n1+n2-1 positions, a "
   "direct generalisation of InterpMul.lean whose Vandermonde machinery is already present. RE-SWEEP THE WINDOW WIDTH "
   "IN THE SAME JOB — w=12 is optimal only against a 1,734 addition, and at ~1,141 the optimum moves toward 10, worth "
   "roughly another 1,700 that is otherwise given back."),
  ("32 — SMALL, SAFE, TAKE IT ALONGSIDE ANYTHING","FinalAdd REROUTES BOTH OPERANDS WHEN ONLY ONE NEEDS TO MOVE. The "
   "screening apparatus itself is already essentially free — mismatchCount (FinalAdd.lean:29) is a pure 256-term "
   "affine expression at 0 wires and 0 rows, specialPoint (:273) selects among the three exceptional answers with "
   "ZERO wires by exploiting (bit0,bit3) parity, and isInf is literally the EitherZero output wire — so the only "
   "recoverable slack is the routing. DROP routedA, the 16-limb ChainState mux, and keep routedT: -32. In each of the "
   "four exceptional branches the entire scalar is pinned, so st27 is one of 4 compile-time points and `decodeFe A.x "
   "!= decodeFe safeT.x` is four `decide`s, discharged in CombSound.implicitFinalAdd_assumptions:755 which already "
   "has hA : zsmul s (.affine G) = ... in hand. (Symmetrically you may instead drop routedT for -16 using the "
   "already-existing CombSound.safeA_x_ne_top:669. YOU CANNOT DROP BOTH — completeness genuinely needs one safe "
   "operand.)"),
  ("~1344 — RE-DERIVE THE FIGURE, THE BASE MOVED","PACK THE SELECTED y AS TWO 128-BIT HALVES. y is a PURE AFFINE "
   "ADDEND everywhere — PairAddFoldA.stageAF (:118) multiplies only lam by dtilOf xT xA with yT/yA appearing solely "
   "inside FoldTail.rhsVecR, stageC1 (:154) is the same with yT2 only in foldRhsY, and stageX/stageO2 use xT only as "
   "an addend since x' = lam^2 - x - xT. So take C from 8 to 6 and Cy from 4 to 2. THE -1,344 WAS COMPUTED AGAINST A "
   "266/266 selectCost AND THE TREE IS NOW AT 257/257, so RE-DERIVE the delta from the current SelectCost.lean rather "
   "than trusting the number. EDITS: replace the `nyn : fields 60` y witness with `fields 30` (halves at limb "
   "positions 0 and 2; limbs 1 and 3 become literal zero, hence free) and the `nyo : Emu` sign mux with a 2-wire mux; "
   "on the table side emit Borrow.half128 of magYNat instead of four limbs — PackEmu.packEmuOfNat IS ALREADY THAT "
   "FUNCTION, with value_packEmuOfNat proving BigInt.value unchanged; add twoPBorrowHalf : Fin 2 -> N beside "
   "twoPBorrowDigit with 2^128 <= D_h < 2^129 and D_0 + 2^128*D_1 = 2*P256, templated on the existing _ge/_lt/_sum "
   "lemmas; rehypothesise the chain from Fe.Valid to Fe.ValidW, for which PackedY.lean ALREADY has NormalizedP, "
   "Fe.ValidW, TValidP, NormAffP and ChainStartP/ChainExtP/ChainFinishP but is UNREACHABLE from Main — wire it in. "
   "Budget up to 80 for one extra carry bit at positions 0 and 2 of foldRhsY/rhsVecR."),
  ("null result — do not spend on this","THE WINDOW WIDTH IS OPTIMAL AT w = 12 AGAINST THE CURRENT 1,734-PER-ADDITION "
   "CHAIN, BY TWO INDEPENDENT ROUTES. A model calibrated to reproduce 49,596 with ZERO error sweeps w = 8..16 as "
   "59750, 55826, 51906, 50802, 49596, 50140, 52590, 58462, 63606; and structurally, Select12's two-level shape costs "
   "2^a + 2C*2^b with a+b = m and C = 4, minimised at 2^a = 8*2^b i.e. a = (m+3)/2, which for m=11 is a=7,b=4 — "
   "EXACTLY what the tree does, with three levels collapsing to two. An earlier estimate of 48,072 at w=12 was wrong "
   "in level AND curvature. Non-uniform widths are legal but worth only ~528 for a third gadget shape. DO NOT SPEND A "
   "SLOT ON WINDOW WIDTH ALONE — the one time to revisit it is INSIDE a job that also collapses the per-addition "
   "cost, since the optimum trades select cost against ADDITION cost."),
 ]),
 "secp256k1-scalar-mul": (315768, None, [
  ("~496","PORT finishXY FROM OUR OWN LOSING SUBMISSION e0e8dc40 (score 319301, VERIFIED). It ran from the same seed as "
          "the 319001 record and lost by 300, but it is CHEAPER on finishXYCost — 805/811 against the record's 809/815, "
          "-8 per site — and on mulModSub2F32Cost (365/368 against 365/370), and it carries a file the record lacks, "
          "divTargetS32Cost. finishXY sits inside fusedStep once per loop step, so at 62 steps this is worth up to "
          "~496. VERIFY THE SITE COUNT: the delta must propagate into fusedStep, glvStep and glvMSMAssert, or the count "
          "is wrong. Download the tree from /api/submissions/e0e8dc40-b896-40e8-a26e-7e770208be74/download."),
  ("16616 — THIS BREAKS 300,000, EVERY NUMBER MEASURED","CARRY THE ACCUMULATOR x IN 32-BIT LIMBS, THEN MOVE THREE MORE CERTIFICATES ONTO MulModFold32. Exact ledger: glvStep 4477 = VarLookup 270 + SlopeXS 1655 + Slope2 892 + FinishXY 1624 + 36. Of that 2583 (57.7%) is five 256-bit range checks AT THEIR PROVED FLOOR and 1470 (32.8%) is folds — 3 x MulModFoldT at 354 plus 2 x MulModFold32 at 204. Subtracting the certificate floor (5 x 716), VarLookup and the flags leaves EXACTLY 501 = 3 x (354-204) + 3 x 17, SO THE WHOLE RECOVERABLE GAP IS THE FOLD-BASE CHOICE. ENABLING FACT: a 256-bit range check costs EXACTLY 512 in either view (4 + 4*(63+64) = 8 + 8*(31+32)), so witnessing xS and x4 as BigInt 8 rather than Emu is COST-NEUTRAL — <4,0> + ValidP <260,265> equals <8,0> + Normalize32 <248,256> + tail <8,9>, both <264,265>. EDITS IN ORDER. E4 (enabler, 0): witness xS and x4 as BigInt 8 and add ValidP32 — pure re-indexing of ValidP.tail from 64-bit slices to 32-bit. E1 (-150/step, -9,300): DivOrZeroN32 moves MulModFoldT -> MulModFold32; the cap holds verbatim at 8*2^32*3*2^32 = 24*2^64 <= 2^69. E2 (-150/step, -9,300): MulModSub2W2 -> MulModSub2F32W2 for y4; WATCH THE CAP — a 2p borrow puts b limbs at 3*2^32 = 2^69.58, one bit over, so either use a p-based borrow schedule or widen wfFold32 48->49 and qBitsFold32 39->40 at <+2,+2>, making it -148. E3 (-8/step, -496): move the y4 sign OUT of the operand slot INTO the target slot — assert mulA*(x4-rx) = +-(y4+ry) and mux the target, which is always free-shaped; same inversion that took mulModSub2 883 to mulModBeta32 733. E5 (-14/step, -868): delete the xSe mux and test the predicate on xS directly, since its three consumers read only a predicate, a value mod p, and an affine addend. E6 (+10/step): replace the R.isInf output mux by input-gating — THIS IS THE EDIT THAT KEEPS THE TABLE AT 4x64 and so keeps VarLookup at 270, by demoting tx and ty to pure affine target addends. NET E1-E6 = -268 PER STEP = -16,616, LANDING 299,820. OPTIONAL: E7 (-4/step) drop DivOrZeroS32 internal IsZeroFeSum guard, since den1 is provably non-zero (sel1=0 gives tx != rx; sel1=1 gives 2ry != 0 because secp256k1 has odd prime order hence no affine 2-torsion); E8 (-22/step, -1,364) derive T.isInf affinely instead of muxing it through the lookup tree. WITH BOTH: -294/step, 298,208. MulModSub2F32W2 ALREADY HAS THE REQUIRED INTERFACE and MulModFold32 accepts an arbitrary Emu target, so NO NEW CERTIFICATE GADGET IS NEEDED."),
  ("~48700 STACKED — THE AMBITIOUS ROUTE, DO A THEN C THEN B","THE BINDING CONSTRAINT IS NOT THE GROUP LAW, IT IS THE EXCEPTION DETECTORS. Only lambda1 and w are materialised because the arithmetic needs them; xS, x4 and y4 are materialised ONLY so three limb-level detectors can read canonical representatives (sameX1 needs rx = previous x4, oppY1 needs ry = previous y4, sameX2 needs xS). Every eliminate-an-intermediate idea dies unless it ALSO replaces the detector. IDEA A (-4,340, do first, it is a precondition for B): a table entry vanishes iff (e1 + e2*lambda) + s*(e3 + e4*lambda) = 0 mod n; over the basis {P, phiP, Q, phiQ} there are EXACTLY SIX bad s including 1 and n-1, but over the UNIMODULAR basis {P, phiP, Q+P, phi(Q+P)} there are FIVE and THE TWO SETS ARE DISJOINT — so ONE WITNESSED BIT choosing the basis makes the table identity-free for every s, after which tIsInf is identically 0 and leaves the loop. The entire obligation is that disjointness: a finite check on 11 constants mod n, closable by decide. IDEA C (-17,700): w*(lambda1 (x) lambda1 - 2rx - tx) = 2ry replaces both the xS certificate and the w division, and x4 = w (x) (2*lambda1 + w) + tx uses ONE convolution not two. Repair sameX2 with a witnessed boolean zOut pinned by zOut*(lambda1 (x) lambda1 - 2rx - tx) = 0 — an ordinary degree-2 assertion, and the converse is free because zOut = 0 makes the chord row w*0 = 2ry, unsatisfiable since ry != 0. IDEA B (-31,000): delete the accumulator y entirely — substitute 2ty for 2ry at the stage-1 tangent (legal since ty = +-ry != 0 by no-2-torsion), set the stage-2 tangent denominator to the CONSTANT 1 (the branch is flagged O anyway so w is harmless garbage), and replace oppY1 by cancel-pinning: assert cancel*(1-sameX1) = 0 and sameX1*(ty - ry - 2*cancel*ty) = 0, which is UNSATISFIABLE FOR THE WRONG BIT so no IsZero and no non-native inverse is needed. THIS IS NOT THE DEAD y-FREE LOOP: that one introduced a NEW FREE WITNESS which was underdetermined; here nothing new is witnessed — y4 occurs linearly with unit coefficient in exactly one equation which DEFINES it, so eliminating that variable and that equation leaves solution sets in BIJECTION BY PROJECTION. Band -33,000 to -49,000; the uncertainty is a 22-position convolution needing a fresh ParamsD3-style instrument recursion."),
  ("146 CONFIRMED AND STILL UNCLAIMED","FINISH THE DERIVED-WIDTH SWEEP IN THE FOLD FAMILY. The 32-bit half of this item ALREADY LANDED as the 315828 record: ParamsFold32T now declares wfFold32T = 46 and qBitsFold32T = 37 (down from 48 and 39), giving MulModFold32T at <97,99> beside the old <101,103> and -608 overall, within 8 of the predicted 616. THE BASE-2^64 SITES ARE UNTOUCHED — mulModFold is still 176/178 — so the same reasoning applies there: these gadgets take the operand caps Ca and Cb as PARAMETERS but hard-code the DERIVED quotient and carry widths at the widest admissible product, so any call site with tighter operands overpays. REMAINING: MulModFold at (2^64, 2^64) worth 80 across 10 sites; MulModFold at (2^64, 3*2^64) worth 44 across 11 sites; GLVStepLastSlope at :143 and :145 worth 16, easy because each ifFalse operand is provably already zero; PointValid fold widths worth 6. NO SOUNDNESS OBLIGATION, one completeness bound per instantiation — this class predicted to within 1.3% last time and is the most reliable work on the board."),
  ("1536","COLLAPSE VarLookup's isInf LANE FROM 15 PRODUCTS TO 3. The lane is expensive only because tinf is treated as a 16-vector of variables — but tinf[0] = 1 is a CONSTANT (RawTable.mk infConst) and entries 1-15 are subset sums of four bases of PRIME ORDER, so if they are provably never infinity the lane collapses to out_isInf = e_0 = (1-b0)(1-b1)(1-b2)(1-b3), i.e. -12 allocations and -12 rows across 64 lookups. THE OBLIGATION IS ONE LEMMA — tinf[i] = 0 for i >= 1, from GLVBuildTable.Subset.Spec plus P != O — AND THE SAME LEMMA ALSO RELEASES the 12 x-canonicalisation muxes at GLVBuildTable.lean:620-644 for another 96."),
  ("1072","INVERT THE lambda CERTIFICATE AT GLVScalarRelation.lean:100-103 — THE LAST LIVE INVERSION SITE IN EITHER TREE. The GLV eigenvalue lambda sits in the A-OPERAND slot of a generic MulModLoose. Certify lambda^-1 (x) t3 = |v2|*s (mod n) instead: the convolution becomes FULLY AFFINE, |v2|*s moves into the target as a 4-cell addend, and the entire 531/535 lv2 intermediate DISAPPEARS, taking 1251/1259 to 717/721. THE INVERSION IS LOAD-BEARING, NOT JUST THE FUSION — forward-fused, cell widths blow vMul.Nf and force Wf from 68 to 134 (+198) plus a five-limb quotient (+63). beta is already inverted; every other constant in both trees is already in a free slot, so this is the last one."),
  ("8060","FOLD NEGATION SYMMETRY INTO varLookup. It is a 4-level mux tree, 15 muxes x 9 fields = <135,135> = 270 per step, the mux-tree optimum FOR A 16-ENTRY TABLE — but T[15-i] = -T[i], since flipping all four sign bits negates the point, and glvBuildTable already builds only 8 independent entries. Select on 3 XNOR-ed bits (the trick Select12 already uses in the fixed-base tree) plus ONE conditional negation via the free offset representation: at 64-bit limbs that is 3 + 7*9 + 4 = 70 products = 140, i.e. -130 PER STEP = -8,060. At 32-bit limbs it is 130 products = 260, only -10 per step, BUT IT IS WHAT MAKES THE FULL 32-BIT PORT ABOVE AVAILABLE — so these two items are ONE DECISION. Combined -460/step = -28,520, landing about 287,900."),
  ("~13200 but high risk","THE +-1 SIGNED-DIGIT MIGRATION — READ THE COSTING BEFORE STARTING, THE EASY VERSION OF THIS IS WRONG. The horizontal-line identity R + phi(R) = -phi^2(R) is real, but beta^2*x mod p is NOT free affine in a non-native representation: it is MulModBeta32 at 733, so a 'free' entry costs 733, not 0. Store phi^2(R) = (beta^2 x_R, +y_R) so the y wire is shared. Table-side yield is about -7,300, NOT the ~10,550 previously recorded. THE REAL PAYLOAD IS THE LOOP: an 8-entry signed table halves VarLookup from 15 muxes to 7, 270 -> 126 across 63 lookups = -9,072, netting -8,568 ONLY IF FusedStep can accept an UNREDUCED table y (a 4-limb mux, +8 per step); if it cannot, the per-step negation is SubMod 577 x 62 = +35,774 and the idea DIES — SETTLE THAT QUESTION FIRST, IT IS THE WHOLE BET. Then pay back ~+2,719: a +-1 digit set represents exactly the ODD integers, the lattice does not deliver odd |u_i|, so a parity correction costs one VarLookup plus one CompleteAdd. Net about -13,200, at the cost of re-proving GLVMSM, GLVStep, VarLookup, GLVScalarRelation and FakeGLVSound. SOUNDNESS: do NOT assume R_+- != O — Q is only assumed Valid and k = -+1 makes R_+- = O, so the build must be O-TOLERANT. That works out for free because beta^2*0 = 0 and noXZero_secp gives x = 0 iff infinity."),
  ("24","TWO SAFE MICRO-WINS IN THE TABLE, THE ONLY SLACK LEFT THERE. (i) -16: delete the t4x and t8x canon-x muxes in Subset.main — Assumptions already give Q.isInf = 1 -> Q.x = 0, and MulModBeta32.Spec gives decodeFe(beta*0) = 0, so both are provably redundant; thread the two hypotheses into Subset.Assumptions. (ii) -8: constant-fold sign0 = 0 in Prepare.main, legal because the final predicate is acc.isInf = 1 and is invariant under global negation of the table (needs negation-closure of ShortCoeffs.exists_decomposition). THE TABLE IS OTHERWISE WITHIN ~1,000 OF ITS FLOOR: 61% of its 30,968 is range checks already proved optimal and 34% is fold certificates already at the cheapest shape. DO NOT HUNT FOR THOUSANDS HERE."),
  ("~9000","FINISH THE 8x32 RE-LIMB. The 32-bit limb VIEW (Limbs32.lean) is a FREE AFFINE recombination "
           "x_k = v_{2k} + 2^32*v_{2k+1}; DivOrZeroS32.lean and MulModSqN32Cost.lean show it applied to a certificate. "
           "The Normalize is COST-NEUTRAL between views (8 + 8*31 = 256 alloc, 8*32 = 256 constr, identical to 4 + 4*63 "
           "and 4*64); the entire gain is that the fold constant 2^32 + 977 is TWO TINY LIMBS in base 2^32 against ONE "
           "33-BIT limb in base 2^64, and that width enters the carry LINEARLY. IT IS ADOPTED PER CERTIFICATE — no "
           "whole-tree rewrite, and the Spec never changes. LANDED, DO NOT REDO: slopeXS, finishXY, phiPairAdd, the "
           "nine table-side completeAdd sites, PointValid's squaring certificate, and both GLVBuildTable.Prepare sites "
           "(MulModBeta32). PointValid IS FINISHED — its cube is an interpolatedMul at 7/7 and its curve equation is a "
           "fold, so the squaring was the only convertible certificate; do NOT go looking for 'the other two'. WHAT IS "
           "LEFT: every remaining mulModSub2 OUTSIDE finishXY, still at 440 allocations. WHEN THE OPERAND ARRIVES IN "
           "BASE 2^64 AND RE-LIMBING IT WOULD COST A Normalize, USE THE CERTIFICATE-INVERSION MOVE (see the common "
           "playbook): if the other multiplicand is a compile-time constant c, certify c^-1*r = a instead of r = c*a, "
           "which puts the awkward value in the TARGET slot where 64-bit limbs suffice. THE PORT SHOWS AS AN "
           "ALLOCATION DROP (slopeXS 899 -> 824, mulModSub2 440 -> 357), so read ALLOCATIONS to tell ported from "
           "unported at a glance. NOTE MulModNorm (432/434) and MulModNorm32 (357/359) are in the tree but WIRED TO "
           "NOTHING — attractive numbers, zero of the integration work done. A Limbs33.lean exists in an earlier tree, "
           "so widths other than 32 are worth a sweep once these land."),
  ("~700 each","SWEEP EVERY REMAINING Mux WHOSE CONSUMER READS ONLY A PREDICATE, NOT THE VALUE. The 317790 record took -744 by deleting ONE Emu-wide Mux: Slope2's stage-2 denominator was a Mux against 2*R.y (4 witnesses + 4 rows) and became `DivOrZeroS32.denSafeVec den2U tsel`, folding the tangent selector into LIMB 0 as a free affine addend, because a denominator only has to be NON-ZERO mod p and nothing reads its exact value. A further -2/-2 followed because the numerator stopped being a conditional square, so the divider needed neither a convolution nor a 2m-1-cell target mux. denSafeVec was already in the playbook and had already landed once — that says nothing about whether every SITE is swept, and this one was worth 744. GO FIND THE REST: any Mux feeding a denominator, a zero-guard, or a consumer that reads only a PREDICATE (non-zero, in-range, congruent) rather than the value. Price each deleted Emu-wide Mux at 4 allocations + 4 rows, times its site count."),
  ("~189 each","SIZE EVERY QUOTIENT RANGE CHECK TO ITS CALL SITE, NOT TO ITS TYPE. MulModLooseQ.lean shows the pattern: "
          "MulModLoose witnesses q = a*b/n as a full 4-limb BigInt and range-checks all four limbs at 252/256, but every "
          "scalar-side GLV call site multiplies by a value below 2^limbBits so the honest q < 2^65 — low limb full "
          "check, second limb BOOLEAN, top two ASSERTED ZERO, giving 63/67 and -189 per site with NO change to the "
          "certificate or the Spec. SWEEP EVERY REMAINING Normalize / NormalizeTight / full-width quotient check and "
          "ask: what is the largest value this witness can honestly take GIVEN THE OPERANDS AT THIS SITE?"),
  ("~500","AUDIT EVERY REMAINING ValidP CALL: does any consumer need UNIQUENESS, or only the congruence class / a range "
          "bound? Canonicality is uniqueness, and most consumers need neither. ALREADY LANDED, DO NOT REDO: the "
          "NormalizeFe weakening at 134 divOrZeroF3 sites and both divUncheckedD3 sites, and the ValidP ASSERTION "
          "MERGE (260/267 -> 260/265, four final quadratic assertions into one with NO new witnesses) which is in the "
          "current seed."),
 ]),
 "sha256-hash": (145470, None, [
  ("~2062 is the only slack","THE WHOLE TREE IS AT THE r = m FLOOR EXCEPT THE PADDING CHECK — GO THERE FIRST AND DO "
        "NOT RE-DERIVE THE GADGETS. I ranked every `def X : Count := <a, c>` in Solution/SHA256 by c - a. "
        "checkPad7SparseUnchecked is <0, 2062> — ZERO ALLOCATIONS, 2062 ROWS — and THE NEXT LARGEST GAP IN THE ENTIRE "
        "TREE IS 88. Every compress block, both message schedules and every per-lane gadget sits within 88 of rows = "
        "allocations, which is the structural floor since each row introduces at most one witness. So the only part of "
        "this circuit whose row count is NOT explained by witness-pinning is a single pure-assertion padding predicate "
        "worth 1.4% of the score. BE HONEST ABOUT WHAT THAT DOES AND DOES NOT PROVE: an assertion block pins no "
        "witnesses, so this is not a proof that 2062 is above its own floor — it is the observation that this is the "
        "one place a redundancy argument could bite. USE THE ROW-DELETION CRITERION, which is exactly built for this: "
        "expand each row into its quadratic-monomial coefficient vector plus linear part, solve sum_k lambda_k "
        "Q_k[i,j] = 0 by PLAIN GAUSSIAN ELIMINATION (no Groebner basis), then either delete any row with lambda_k != 0 "
        "or use the resulting free linear constraint to eliminate a wire. Yield is ~0% on hand-tight circuits and 20%+ "
        "on mechanically generated ones, and a 2062-row all-assertion predicate is far more likely to be the latter. "
        "ALREADY LANDED, DO NOT REDO: the one-row gadgets are in this tree — ch32Cost, and32Cost and lowerSigma0Cost "
        "are all <32, 32>, one row and one allocation per bit."),
  ("blocked, do not try","XOR4 AND XOR5 CANNOT BE DONE IN ONE ROW — THIS IS PROVED, NOT A SEARCH FAILURE, so the "
        "message-schedule sigmas cannot be widened past three inputs. Exactly 192 of the 256 three-input boolean "
        "functions are one-row pinnable; f is BLOCKED iff c_{123} != 0 and (c_{23}, c_{13}, c_{12}) all lie in {0, "
        "-c_{123}}, which covers the 8 point-indicators and complements, AND3/OR3/NAND3/NOR3, and the weight-{1,3,5,7} "
        "functions with |c_{123}| = 1. For parity specifically, dim{A affine : deg(A * parity_n) <= 2} = 0 for n = "
        "4,5,6,7 computed EXACTLY OVER Q, so it holds over every field, and the two-row/one-witness case-split variant "
        "dies too. XOR5 as two chained XOR3 rows at 2 allocations + 2 rows is OPTIMAL. Spend the slot on the padding "
        "block instead."),
 ]),
 "keccak-f1600": (307200, 184320, [
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
 "rsa-pkcs1v15-sha256-4096-65537": (321889, None, [
  ("1450","The q*n limb caps are UNSIGNED (limbCap = 2^B - 1) while the a^2 caps are balanced (fixedBalCap ~ 2^(B-1)), and "
          "q*n DOMINATES the coefficient cap: peak 2^55.74 against 2^54.42 balanced. Witness q's limbs offset "
          "(q_i = q_i' + 2^23) and offset n's limbs affinely (free — n's limbs are already affine in the input bytes). The "
          "correction Q(c)N(c) = Q'(c)N'(c) + 2^23*U(c)*(Q'(c)+N'(c)) + 2^46*U(c)^2 is ENTIRELY AFFINE because c is a fixed "
          "compile-time evaluation point, so it stays one product row. 1.32 bits x 2 x 37 carries x 15 squarings."),
 ]),
}
def workqueue_block(slug):
    wq=WORKQUEUE.get(slug)
    if not wq: return ""
    derived,pred,items=wq
    now=tg[slug]["target"]           # live, so the header cannot go stale as records land
    head=(f"\n\nPRIORITY WORK QUEUE — DERIVED FROM THIS SOLUTION'S OWN SOURCE AND COST PROOFS, NOT SPECULATION.\n"
          f"Each item was worked out against the {derived} solution, with the saving predicted from its own measured\n"
          f"primitive costs. These are NOT literature candidates to evaluate — they are work items. They are ordered\n"
          f"CHEAPEST-AND-SAFEST FIRST, so if you can only land one, take the first one you can fully prove.\n")
    if now!=derived:
        head+=(f"*** THE SEED HAS MOVED ON TO {now} SINCE THESE WERE DERIVED, SO SOME MAY ALREADY BE DONE. ***\n"
               f"CHECK THE SEED BEFORE IMPLEMENTING ANY ITEM — re-deriving work already in the tree wastes the whole job.\n"
               f"The mechanisms and bound arithmetic below remain valid regardless of which have landed; only the\n"
               f"predicted savings are relative to {derived}. A quick way to tell which non-native sites are still\n"
               f"UNFOLDED: an unfolded site uses the `gfQuad`/`gfWideFat` grouped-carry path and witnesses a full 4-limb\n"
               f"quotient with a ~252/256 NormalizeImplicit on it; a folded one uses `gfFold` with ONE carry and a single\n"
               f"quotient wire. Grep for those and work the sites that are still on the unfolded path.\n")
    elif pred:
        head+=f"Implementing all of them is predicted to reach about {pred}.\n"
    return head+"\n".join(f"  [~{s} score] {t}" for s,t in items)
os.makedirs("prompts",exist_ok=True); os.makedirs("prompts_small",exist_ok=True)
def tmpl(inst,t,framing,ideas,show_target=True,wq=""):
    if show_target:
        goal=(f"scoring allocations+constraints = {t}, defining ALL\n"
              f"required declarations INCLUDING `computableWitness`, and it passes the verifier. GOAL: a NEW solution scoring\n"
              f"STRICTLY BELOW {t} that STILL fully verifies.")
    else:
        # small-win: no numeric anchor — the seed IS the SOTA; beat it by any margin
        goal=("defining ALL required declarations INCLUDING `computableWitness`, and it passes the verifier — this\n"
              "seed IS the current state of the art (SOTA). GOAL: ANY new solution that scores STRICTLY LESS than the\n"
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
    open(f"prompts/{slug}.md","w").write(tmpl(inst,t,"Be ambitious — aim for a large structural reduction.",IDEAS[slug],wq=workqueue_block(slug)))
    open(f"prompts_small/{slug}.md","w").write(tmpl(inst,t,"Prefer a SMALL, safe, guaranteed-provable reduction; certainty of a verified result matters most.",IDEAS[slug],show_target=False,wq=workqueue_block(slug)))
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
