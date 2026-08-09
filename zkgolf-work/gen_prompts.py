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
 "secp256k1-fixed-base-scalar-mul": (49218, 49536, [
  ("1974 — NEW, AND THE FIRST SELECT-SIDE WIN IN MANY PASSES","RANK-2 PAIRING IN THE SELECT TOP MUX. An R1CS "
   "row can carry RANK 2, and the top stage is spending one product per RANK-1 term. It computes f_c = SUM_{i<16} "
   "u_i * leaf_{c,i} with u the one-hot on the top 4 bits and leaf_{c,i} = SUM_j T_c[i,j] e_j a FREE affine "
   "combination of the low one-hot. Since u and e are one-hot (u_i u_i2 = 0 and e_j e_j2 = delta e_j), set "
   "A = u_i + SUM_j T_c[i2,j] e_j and B = u_i2 + SUM_j T_c[i,j] e_j. Then A*B = u_i*leaf_{c,i} + "
   "u_i2*leaf_{c,i2} + SUM_j T_c[i,j]T_c[i2,j]*e_j: the cross term u_i u_i2 VANISHES IDENTICALLY on the boolean "
   "cube, and the (gamma.e)(delta.e) term COLLAPSES TO A LINEAR combination of the e_j — a free affine correction "
   "with compile-time coefficients. ONE ROW DELIVERS TWO OF THE SIXTEEN TERMS, so a column costs 8 products "
   "instead of 15. COST: the 4x4 top tensor costs +9 (blk already holds the two pair-products), columns 8x15 = "
   "120 -> 8x8 = 64, net -47 units per select = -94 score x 21 = -1,974. CALIBRATION YOU CAN CHECK: Select12 has "
   "257 allocations = w 11 + blk 5 + i4 9 + i6 45 + i7 63 + xa 48 + xb 12 + ya 48 + yb 12 + yo 4, matching "
   "select_sub_localLength = 257 at Comb.lean:79, and the same model reproduces the packed-y item at exactly "
   "-1,344. STACKS WITH PACKED-y: 122 + 9 + 48 + 2 = 192 per select, -2,730 together. SOUNDNESS: you need (i) "
   "hot7Val v * hot7Val v2 = 0 for v != v2 — the tree already proves the SUM form via SelectPrelude.hot4Val_sum15 "
   "and the hot6Val/hot7Val chain, and the QUADRATIC orthogonality is the new lemma, write it first — and (ii) "
   "u_i u_i2 = 0 from top-bit booleanity. IF (i) IS DROPPED the prover supplies a NON-one-hot e, the correction "
   "term stops matching (gamma.e)(delta.e), and f_c can take a value OFF THE TABLE. EDITS: replace the "
   "nxa/nxb/nya/nyb blocks (48+12+48+12) with a fields-9 top-one-hot block plus fields-64 paired products; "
   "rewrite Select.selected/zsel/selected2/xSelExpr in SelectPrelude.lean, the isR1CSRow_mul_sub chain at "
   "Comb.lean:224-300, SelectCost.lean, and the selected*_val lemmas in SelectTheorems.lean and "
   "SelectSound12.lean. Row DENSITY is unchanged; only the count drops. This touches the largest proof files in "
   "the tree, so if the verifier times out that is INFRASTRUCTURE — just resubmit the same tree."),
  ("ALWAYS DO THIS LAST — IT HAS COST US THREE SUBMISSIONS","RE-DERIVE THE WHOLE COST CHAIN, NOT JUST Main. "
   "Comb.costIs_main contains a HARD-CODED LITERAL for the chain body — `<19 * 1113, 19 * 1117>` — which is NOT "
   "written as 19 * chainBodyCost, so it does NOT track changes to selectCost or extCost. A submission claiming "
   "-2 failed for exactly this: it lowered extCost, canonicalizeCost and implicitScreenedCost by one allocation "
   "each but left the 1113 alone, so chainBody became 1112 and the `by decide` could no longer close. The leaf "
   "changes were worth -22 allocations while combCost moved only -2 — A LEDGER THAT DOES NOT ADD UP CANNOT "
   "ELABORATE. GREP THE COST PROOFS FOR NUMERIC LITERALS, NOT JUST FOR `def X : Count`. Then re-derive "
   "Main.lean's allocations AND constraints "
   "FROM THE INTERNAL COST CONSTANT, NEVER BY HAND. mainCost is `fun input => Comb.costIs_main input`, so the "
   "literal pair in Main.lean must be DEFINITIONALLY EQUAL to combCost. If you shrink the circuit, update "
   "combCost, and forget Main, the term no longer has the ascribed type and the WHOLE SUBMISSION FAILS TO "
   "BUILD — while also claiming the wrong score. MEASURED: submission e8070daa shipped a complete CRT fold "
   "multiply with combCost correctly at <24377,24467>, left Main.lean at 24560/24650, and came back `failed` "
   "claiming -8 instead of -374. CHECK EVERY CONSTANT ON THE PATH from the gadget you changed up to Main: "
   "extCost, startCost, implicitScreenedCost, canonicalizeCost, combCost, then Main. Before you finish, diff "
   "every `def X : Count := <a, c>` in your tree against the seed and confirm Main's pair equals the "
   "top-level container's pair."),
  ("90 — CONFIRMED, MECHANICAL, NO PARAMETER FILES. DO THIS FIRST","INVERT THE FOLD QUOTIENT, THEN DELETE THE "
   "GroupedFlex NATIVE ROW. All 45 certificates have the shape SUM_k lhs_k 2^(64k) = q*P256 + SUM_k tail_k 2^(64k) "
   "with P256 a COMPILE-TIME CONSTANT, and q is currently ProvableType.witness (alpha := field) at <1,0>. The honest "
   "q AS A FIELD ELEMENT is exactly q = (SUM lhs_k 2^(64k) - SUM tail_k 2^(64k)) * (P256 : F)^(-1) — an AFFINE "
   "EXPRESSION in wires already allocated (the convLL/convLD/convLX* z-wires, x2/lam2/y3, xPrev, xT). (P256:F)^(-1) "
   "is a numeral hence free, q * cExp P256 k stays affine, so foldRhs/rhsVecR/rhsVec are unchanged in shape, and "
   "RangeCheck.circuit ALREADY TAKES AN Expression so there is NO API CHANGE. That is -45 allocations. SITES: "
   "ChainFold.lean:35 (stageO2), :159 (stageC1), :298 (stageX); PairAddFoldA.lean:123 (stageAF); "
   "ChainFinishFold.lean:38 (stageYF); Canonicalize.lean:773 (the b wire). SOUNDNESS: the natural-number identity "
   "still follows from the carry range check plus the per-position bounds, which is ALL GroupedFlex soundness uses; "
   "q.val < 2^67/68/69 is still enforced by the surviving RangeCheck; q.val*p_k + tail_k.val < 2^131 < p so nothing "
   "wraps. COMPLETENESS: cast the ALREADY-PROVEN natural-number identity (ChainFold.siteC2a_fold_complete and "
   "friends) mod circomPrime and solve for q. (P256 : F circomPrime) != 0 is `by decide`. For Canonicalize, b := "
   "(SUM x_k 2^(64k) - SUM r_k 2^(64k)) * P256^(-1) and the booleanity row assertZero (b*(b-1)) STAYS — still rank-1 "
   "with b affine — pinning b in {0,1}, with x < 2^256 < 2*P256 giving the honest b in {0,1}. THEN, IN THE SAME JOB "
   "AND STRICTLY AFTER: GroupedFlex.lean:201-204 emits assertZero (polyEvalExpr (ofFn fun j => Pc[j] - Sc[j]) (2^B)), "
   "which once q is inverted evaluates to L - q*P256 - T = IDENTICALLY ZERO AS A POLYNOMIAL IN THE WIRES — a row "
   "carrying no information. Add a GroupedFlex.mainNoTop variant whose soundness takes the field identity as a "
   "HYPOTHESIS DISCHARGED BY `ring` rather than as a row, cost <widthAllocFrom, widthConsFrom> instead of <., .+1>. "
   "That is -45 rows, reused by all 45 sites. THESE 90 ARE EXACTLY THE ALLOCATIONS-VERSUS-ROWS GAP (24,843 - 24,753 "
   "= 90 = +1 per RangeCheck for the derived-top-bit booleanity row, +1 per GroupedFlex for the native row), so "
   "after this the gap should be +45, not +90 — USE THAT AS YOUR CHECK."),
  ("22 — FOUR CONFIRMED PARAMETER HITS, ALL MECHANICAL","SHARED FoldParams INSTANCES ARE SIZED FOR THEIR WIDEST "
   "CONSUMER AND FOUR SITES ARE OVERPAYING BY CONSTRUCTION. (a) -8: Canonicalize's carry width is sized to a TYPE, "
   "not the site. GroupedFlexInstances.lean:57-70 sets vCanonicalL/vCanonicalR at OFFf = 3/4 and Wf = fun _ => 3, but "
   "gfLin 0 = 1 so carry 0 sits at the 2^64 boundary over position 0 alone, where L_0 = r_0 + b*p_0 < 2^65 and R_0 = "
   "x_0 < 2^64 make the honest carry lie in {0,1}; GVXHyps k=0 forces only OFF_L0 >= 1 and OFF_R0 >= 0, so OFF_R0 + "
   "OFF_L0 = 1 < 2^1 and Wf 0 = 1. Only Wf 0 is billed, so make the parameters NON-UNIFORM: Wf k := if k = 0 then 1 "
   "else 3, OFF_L k := if k = 0 then 1 else 3, OFF_R k := if k = 0 then 0 else 4 (k >= 1 must keep OFF_L1 >= 2). "
   "RangeCheck.circuit 1 is legal and costs <0,1>; GroupedFlex <2,4> -> <0,2>, at both call sites. (b) -6: stageAF "
   "pays the two-convolution tent for a ONE-convolution site — PairAddFoldA.lean:127 passes P1 := ZeroConv.zeroP7, an "
   "ALL-ZERO CONSTANT VECTOR (FoldTail.lean:20). Apply FoldWide.convTerms (the position-aware machinery ALREADY "
   "EXISTS at FoldWide.lean:191 and was simply never wired to FoldPair): L_1 < 6*2^160 + 2^142 rather than the "
   "assumed 2^165 = 32*2^160, and N_R = 2^133 since this site's q < 2^68 not 2^69, giving OFF_L0 + OFF_R0 < 2^99, so "
   "wfFoldP 102 -> 99 and <101,103> -> <98,100>. 98 is NOT reachable, do not try. (c) -6: stageYF likewise — "
   "FoldParamsC1's vFold2L is documented for 'a sum of two convolutions' but ChainFinishFold.lean:42 feeds "
   "FoldQuad.lhsVec convLX2 (2^35 * P256), ONE convolution with xdOf < 2*2^64; position-aware bounds give OFF_L0 = "
   "2^98 + 2^77 + 2^35 and wfFold2 102 -> 99. (d) -2: ChainFinishFold.lean:40 range-checks 69 bits but LHS < 2^323 + "
   "2^291.4 gives q < 2^67 + 2^36 < 2^68, so 69 -> 68."),
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
   "DELETE, ZERO SCORE BUT REAL BUILD TIME — 60 OF THE 196 FILES ARE DEAD: the explicit "
   "FinalAdd.main/circuit/screenedCost path <1611,1620>, CheapIncompleteAdd, selectConstPoint, "
   "CombSound.finalAdd_assumptions:714, CombCW.lean:180-300, ChainStartFold.lean, ChainFinishY.lean, TopSelect*.lean, "
   "SelectX.lean, TopSel*.lean, PairAddFold5.lean, FoldWideParams.lean. NOTE ChainStartFold.lean:63 startCost "
   "<1154,1160> IS DEAD CODE — the live start is ChainFold.lean:453 <859,863>; do not price against the dead one."),
  ("4246 — RE-PRICED AND CORRECTED; PREFER THE MIXED-RADIX HALF","MOVE THE WITNESSED LIMBS TO BASE 2^32. "
   "Materialising a 256-bit value costs EXACTLY 512 at any limb width (NormalizeImplicit is <m(B-1), mB>, so "
   "m + m(B-1) + mB = 2mB = 512), so limb width is FREE and what it changes is the MAGNITUDE BUDGET setting the "
   "quotient and carry widths — linear in limb width at 2 score per bit. BASELINE, WHICH CLOSES EXACTLY AT 49,196: "
   "Select12 <257,257> x21, stageAF <429,431>, stageO2 <427,429>, stageC1 <438,440> x20, stageX <427,429> x20, "
   "stageYF <429,431>, plus 1,146 of glue. PER-SITE TARGETS: stageX 856 -> 700; stageC1 878 -> 856 (mixed radix) or "
   "738 (full narrow); stageAF/stageYF 860 -> 826 or 704; Select12 514 unchanged under mixed radix, 634 under full "
   "narrowing. RANKED: full 8x32 + root-eval -4,246; MIXED-RADIX + root-eval -4,118; full plain -3,868; mixed plain "
   "-3,784; narrow-lambda alone -3,276. PER CHAIN WINDOW FULL AND MIXED ARE EXACTLY EQUAL (726 + 634 = 846 + 514 = "
   "1,360); the full conversion's whole edge comes from stageAF/stageYF, which have no matching select, and is "
   "inside modelling slack. SO PREFER MIXED RADIX — it touches only InterpMul, where the full conversion rewrites "
   "Select12 soundness and completeness for 8 limbs, AND THE MIXED MULTIPLY IS ALREADY BUILT AND PROVED IN A "
   "SIBLING TREE: projs/rsa-pkcs1v15-sha256-4096-65537/.../InterpMulX.lean has cauchy_diag_mixed, mulNoReduceX, "
   "interpolatedMulX (a : Vector _ n1) (b : Vector _ n2), costIs_interpolatedMulX at <n1+n2-1, n1+n2-1>, "
   "isR1CS_interpolatedMulX and the soundness bridges. PORT IT, DO NOT WRITE IT. MIXED BASES NEED NO NEW MACHINERY: "
   "pad the 4x64 operand with EXPLICIT ZEROS to stride 2, b2 = [b0,0,b1,0,b2,0,b3] : Vector _ 7, so polyEvalExpr b2 "
   "c = SUM b_i c^(2i) is the strided evaluation, still affine; interpolatedMulX at n1=8, n2=7 gives 14 positions "
   "at <14,14>. The selected xT STAYS 4x64 on the EVEN positions of a B=32 RHS and this moves neither W nor the "
   "quotient — additive terms are free at any radix, only MULTIPLICANDS care. EXACT CONSTANTS FOR THE NARROW "
   "stageX, DO NOT ROUND THEM: L=8, gf=(6,1,1), posOf=(0,6,7,8), G=3; multiplicities n = "
   "[1,2,3,4,5,6,7,8,7,6,5,4,3,2,1]; the fold X^8 = X + 977 gives K = [6840,5871,4894,3917,2940,1963,986,9] with "
   "K_k = n_k + [k>=1] n_{k+7} + [k<=6]*977*n_{k+8}; NfL[k] = K_k*(2^32-1)^2 + limb_k(4*P256) + 1 for k<=6 and "
   "NfL[7] = 9*(2^32-1)^2 + 2^34, so NfL[0] = 126175729405422475414389 and NfL[7] = 166020696603256422409; NfR[k] "
   "= q*limb_k(P256) + 2*(2^32-1) + 1 with q_max = 38654706636 giving RangeCheck width 36; OFF_L(0) = "
   "8431020801062 and OFF_R(0) = 42949673935 sum to 8473970474997 < 2^43, so W_0 = 43 and GroupedFlex is <42,44>. "
   "ROUNDING NfL UP TO 2^77 GIVES W = 46 AND COSTS +126 ACROSS THE TREE — this trap has already cost a full bit "
   "elsewhere in this codebase."),
  ("12870 — THE BIG ONE. DO THIS AT B = 16, NOT B = 32","THE SQUARES TELESCOPE: STOP MATERIALISING THE "
   "ACCUMULATOR x ENTIRELY. Unrolling x_j = lambda_j^2 - x_{j-1} - xT_j makes every intermediate x-coordinate an "
   "ALTERNATING SUM OF SQUARES, and interpolatedMul returns its convolution positions as AFFINE WIRES "
   "(interpolatedMul_output at InterpMul.lean:29, affineW_interpolatedMul_output at :170), with affine closure "
   "under +, - and CONSTANT scaling given by Affine.add / Affine.sub / Affine.fconst_mul — used exactly this way "
   "in FoldQuot.affine_foldLhs (FoldQuot.lean:92). So every x_j is FREE as an unreduced convolution: ZERO "
   "allocations, ZERO rows. The state becomes THE LAMBDAS ALONE. VERIFIED SAFE: no IN-LOOP consumer needs a "
   "normalized x. Chain.ChainExt.Assumptions (Chain.lean:295) does demand BigInt.Normalized 64, but that is the "
   "CURRENT gadget own spec which you are replacing, and its semantic uses (decodeFe x, and decodeFe x != "
   "decodeFe T.x) are CONGRUENCE-ONLY; GroupedFlex.Assumptions (:376) needs only lhs[k].val < Nf_L k, which is "
   "parametrised. The only hard requirements are TERMINAL (Chain.ChainFinish.Assumptions :347 and "
   "FinalAdd.ImplicitAssumptions) and ONE materialisation discharges both. PER WINDOW AT B=16: lambda witness + "
   "NormalizeImplicit 512 (16 x <15,16> + 16 — the floor, same at any base); lambda^2 at m=16 = 62; the MERGED "
   "product 62; mixed-radix lambda_j * xT_j amortised 56; quotient witness 1; quotient RangeCheck 77 bits = 153; "
   "GroupedFlex 214 with ONE carry. TOTAL 1,060 AGAINST 1,734. At B=32 it is 1,355, because the GVXHyps tail "
   "clause forces TWO carries there (541) — B=16 IS THE OPTIMUM AND IT IS NOT CLOSE. MERGE THE TWO lambda*x "
   "PRODUCTS: the identity is lambda_j*xT_j + lambda_{j-1}*xT_{j-1} - (lambda_j + lambda_{j-1})*x_{j-1} = yT_j + "
   "yT_{j-1}, and lambda_j + lambda_{j-1} is an AFFINE vector, so the two lambda*x products become ONE at a cost "
   "of one bit. USE THIS EXACT GVXHyps INSTANCE: L=16, gf=[7,2,7], G=3, Wf=[107,106] (only Wf[0] is "
   "range-checked), q < 2^77, OFF_L = [127084444460856594797708922674256, 73525315039237962920340117665780], "
   "OFF_R = [316917709114615889152944510701, 158461348078042219126140571470]; clause (d) reads 219.84 / 138.93 "
   "and clause (10) reads 221.72 against log2 p = 253.60, at least 32 bits of margin everywhere. DO NOT USE "
   "gf=[9,1,6] — it is 2 cheaper and leaves only 2.67 bits on clause (d). REGENERATE Nf RATHER THAN TRUSTING "
   "DIGITS: n_k = min(k+1, 2M-1-k); X_k = 21*n_k*2^(2B) + 22*2^64*[k = 0 mod (64/B) and k < M] + 2^B; X^f = "
   "fold_M(X); LX = fold_M(conv(2^(B+1)*1_M, X^f)); LT = fold_M(conv(2^B*1_M, xT)); Nf_L[k] = LX[k] + "
   "2*2^64*[k even] + 2*LT[k]; Nf_R[k] = 2^Wq*limb_B(P256,k) + 2*LT[k]. NEVER round an Nf up to a power of two — "
   "that trap costs a full bit. TERMINAL: materialise x_20 as a normalized 4x64 Emu immediately BEFORE FinalAdd "
   "and FinalAdd IS UNCHANGED; it carries NO new products, costing 512 + 1 + RangeCheck 37 bits (73) + "
   "GroupedFlex gf=[10,1,5] G=3 W=56 (110) = 696. lambda needs NO re-materialisation: lam64[i] = SUM_t "
   "lam_narrow[k*i+t]*2^(B*t) is free affine and Normalized 64 by construction. INFRASTRUCTURE — MOST OF IT "
   "ALREADY EXISTS: you need a generalised interpolatedMul at n1 x n2 -> n1+n2-1, and interp_uniqueness "
   "(Vandermonde.lean:110) is ALREADY general in N while the cost and R1CS lemmas (InterpMul.lean:170-202) "
   "generalise VERBATIM; the ONLY obstruction is cauchy_diag (Vandermonde.lean:33), stated at equal m — AND "
   "cauchy_diag_mixed, mulNoReduceX, interpolatedMulX, costIs_interpolatedMulX and isR1CS_interpolatedMulX ALL "
   "ALREADY EXIST AND ARE PROVED in projs/rsa-pkcs1v15-sha256-4096-65537/.../InterpMulX.lean. PORT THEM. Also "
   "needed: a BigIntParams circomPrime 16 at B=16 (Theorems.lean:774, all by-decide and SLACKER than the "
   "shipped B=64 instance), a width-M pseudo-Mersenne fold (FoldQuot.foldLhs :39 is hard-coded 7 -> 4), and a "
   "Chain.ChainState whose x is M affine expressions plus a decodeTel. Chain.impliedY (:184) is UNCHANGED. "
   "TOTAL -12,870, LANDING ABOUT 36,326. ESCAPE HATCH IF ELABORATION BLOWS UP: depth is nearly free (d=1 gives "
   "1,042 against d=21 giving 1,058), so RE-MATERIALISE EVERY k WINDOWS at about 696 each and lose almost "
   "nothing. The real risk is elaboration time, not arithmetic — at depth 21 each interpolation row has ~320 "
   "nonzeros in its B vector instead of ~8. A VERIFIER TIMEOUT IS INFRASTRUCTURE: resubmit, or drop the depth. "
   "DO NOT ABANDON THE SCHEME."),
  ("16 — HALF OF THIS LANDED; TAKE THE OTHER HALF","FinalAdd IS KEEPING THE EXPENSIVE MUX AND DROPPED THE CHEAP "
   "ONE — SWAP THEM. The screening apparatus is already essentially free (mismatchCount at FinalAdd.lean:29 is a "
   "pure 256-term affine expression at 0 wires and 0 rows; specialPoint at :273 selects among the three "
   "exceptional answers with ZERO wires by exploiting (bit0,bit3) parity; isInf is literally the EitherZero "
   "output wire), so the only slack is the operand routing, and only ONE operand needs to move to break "
   "A.x == T.x. A previous job dropped routedT, the 8-limb Select.AffPoint mux worth <8,8> = 16, and LEFT "
   "routedA, the 16-limb Chain.ChainState mux worth <16,16> = 32, in place at FinalAdd.lean:927. DO THE "
   "OPPOSITE: restore routedT (+16) and drop routedA (-32), for a net -16. YOU CANNOT DROP BOTH — completeness "
   "genuinely needs one safe operand. Dropping routedA needs decodeFe A.x != decodeFe safeT.x, and in each of "
   "the four exceptional branches the ENTIRE SCALAR IS PINNED, so st27 is one of 4 compile-time points and the "
   "disequality is four `decide`s, discharged where CombSound.implicitFinalAdd_assumptions:755 already has "
   "hA : zsmul s (.affine G) = ... in hand."),
  ("VERIFIED TIGHT — DO NOT RE-ATTACK ANY OF THESE","NEGATIVE RESULTS ON THE FOLD, RE-DERIVED FROM THE TREE. vFoldL's "
   "Wf = 98 (stageO2 + 20 x stageX, 4,116 score): L_1 = P_1 + cFold*P_5 + w_1 with P_1, P_5 <= 2(2^64-1)^2 gives L_1 "
   "> 2^161 STRICTLY, so the carry exceeds 2^97 and 97 is impossible. vFoldWL's Wf = 100 (20 x stageC1, 4,000): the "
   "combined S_5 < 10*2^128 gives OFF_L0 ~ 10*2^96 > 2^99, and tightening nfFoldWL 1 or nfFoldWR GAINS NOTHING. THE "
   "FOLD GROUPING gfFold = [2,1,1] IS FORCED FROM BOTH SIDES: gf 0 = 3 would give Wf = 97 but the group-0 sum is "
   "~2^288 >> p; gf 0 = 1 gives the same Wf = 98 but the final-row tail is ~2^259 > p. G = 3 is the minimum so ONE "
   "CARRY IS THE MINIMUM, and GroupedFlex's score is exactly 2 * Wf 0. QUOTIENTS ARE TIGHT at 67 (stageX, stageO2), "
   "68 (stageAF) and 69 (stageC1). RangeCheck is at 2/bit - 1 and ALREADY applies certificate inversion itself "
   "(RangeCheck.lean:16-19). NormalizeImplicit = 4 x <63,64> = 508 is exactly 256 bits of materialisation and admits "
   "NO site-specific narrowing. There is NO live use of the expensive Gadgets.ToBits.rangeCheck <n,n+1>. THREE "
   "SEARCH PATTERNS CAME BACK EMPTY: no Mux whose consumer reads only a predicate (the three live Muxes at "
   "FinalAdd.lean:927/931/938 all have their exact limbs read); no linking loops (every live row contains a genuine "
   "product except the GroupedFlex native row); no materialised-but-only-asserted value except that same row. "
   "Select12 already returns x as a PURE AFFINE EXPRESSION (Comb.lean:57), so that lever is spent."),
  ("null result — do not spend on this","THE WINDOW WIDTH IS OPTIMAL AT w = 12 AGAINST THE CURRENT 1,734-PER-ADDITION "
   "CHAIN, BY TWO INDEPENDENT ROUTES. A model calibrated to reproduce 49,596 with ZERO error sweeps w = 8..16 as "
   "59750, 55826, 51906, 50802, 49596, 50140, 52590, 58462, 63606; and structurally, Select12's two-level shape costs "
   "2^a + 2C*2^b with a+b = m and C = 4, minimised at 2^a = 8*2^b i.e. a = (m+3)/2, which for m=11 is a=7,b=4 — "
   "EXACTLY what the tree does, with three levels collapsing to two. An earlier estimate of 48,072 at w=12 was wrong "
   "in level AND curvature. Non-uniform widths are legal but worth only ~528 for a third gadget shape. DO NOT SPEND A "
   "SLOT ON WINDOW WIDTH ALONE — the one time to revisit it is INSIDE a job that also collapses the per-addition "
   "cost, since the optimum trades select cost against ADDITION cost."),
 ]),
 "secp256k1-scalar-mul": (308278, None, [
  ("33000 to 49000 — THE ONLY ITEM AIMED AT WHERE THE SCORE ACTUALLY IS","REWRITE THE EXCEPTION DETECTOR SO THE STEP "
   "STOPS MATERIALISING 256-BIT VALUES. MEASURE FIRST, THEN BELIEVE THIS: one glvStep costs 4,377, of which FIVE "
   "256-BIT RANGE CHECKS (Normalize32 504, ValidP 525, Normalize32 504, ValidP 525, ValidP 525) are 2,583 — 59% of "
   "the step, 160,146 across the 62 steps, AND 52% OF THE WHOLE 308,278 TREE. Folds are 1,394 per step (31.8%), "
   "VarLookup 244 (5.6%), muxes and flags 156 (3.6%). EVERY OTHER ITEM IN THIS QUEUE IS ROUNDING BY COMPARISON. "
   "Materialisation is at its proved floor of ~512 each, so the ONLY lever is MATERIALISING FEWER VALUES, which "
   "means removing the exception-detection work that forces them. IDEA C (ceiling): deleting mulModSub2F32 from the "
   "step is 721 per step = -44,702 gross; realistic net -18,600 to -31,000. IDEA B (ceiling): deleting "
   "mulModSub2W32M is 855 per step = -53,010 gross; realistic net about -24,800. IDEA A is a PRECONDITION, NOT A "
   "WIN — it was priced at -4,340 against an old tree and is now worth about -1,744, because the tinf mux lane it "
   "targeted is already gone; what remains is IsZeroFeSumR 4x64 = 256 plus 24 per step of tIsInf muxes. DO A ONLY TO "
   "UNBLOCK B AND C. The replacement certificates do not exist in the tree, so the net figures are bounded "
   "estimates, not derivations — the gross removals (721 and 855 per step) ARE exact."),
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
  ("1488 — SAFEST WORK ON THE BOARD, AND IT REPLACES THREE DELETED ITEMS","TWO BOUND PATTERNS ON THE FOLDS. (a) "
   "POSITION-DEPENDENT Nf PLUS A LATER CARRY GROUP, -1,240. Every Nf is declared as a CONSTANT function of position "
   "at the maximum cell count, while the true folded-digit profile decays steeply: Fold32 and Fold32T give d = "
   "[6840, 5871, 4894, 3917, 2940, 1963, 986, 9] x Ca*Cb, and Fold32M and Fold32N give d = [2932, 2935, 1959, 1958, "
   "982, 981, 5, 4] x Ca*Cb. Since OFF_L(0) ~ Nf(gf_0 - 1)/2^B and only Wf(0) is charged, you must make Nf "
   "POSITION-DEPENDENT **and** push the single materialised carry to a later group — NEITHER LEVER WORKS ALONE, "
   "since with constant Nf the regrouping changes nothing. DERIVED: ParamsFold32T [2,1,5] -> [6,1,1] takes Wf 45 -> "
   "43 over 76 instances = -304; ParamsFold32 [2,1,5] -> [6,1,1] takes 47 -> 45 over 62 = -248; ParamsFold32M "
   "[3,1,4] -> [5,1,2] takes 79 -> 77 over 62 = -248; ParamsFold32N likewise 78 -> 76 = -248; qBitsFoldT 69 -> 68 "
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
   "genuinely cost-neutral; do not spend time on it."),
  ("24 — VERBATIM, STILL THERE","TWO TABLE MICRO-WINS. (i) -16: delete the t4x and t8x canon-x muxes in "
   "Subset.main, still at GLVBuildTable.lean:620-623 as 2 x <4,4>. (ii) -8: sign0 is still a live selector at "
   "GLVBuildTable.lean:352-353. NOTE THE OLD VERSION OF THIS ITEM ENDED WITH 'DO NOT HUNT FOR THOUSANDS HERE' AND "
   "THAT ADVICE IS NOW WRONG — the signed-digit migration restructures this very table for about -10,000."),
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
 "sha256-hash": (145470, None, [
  ("~474 — OPERATIONAL, THE MATH IS ALREADY DONE. DO THIS FIRST","WIRE THE DEFERRED-CHAIN CONFIGURATION INTO THE "
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
    open(f"prompts/{slug}.md","w").write(tmpl(inst,t,"Be ambitious — aim for a large structural reduction.",IDEAS[slug],wq=workqueue_block(slug,True)))
    open(f"prompts_small/{slug}.md","w").write(tmpl(inst,t,"Prefer a SMALL, safe, guaranteed-provable reduction; certainty of a verified result matters most.",IDEAS[slug],show_target=False,wq=workqueue_block(slug,False)))
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
