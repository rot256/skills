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
 "secp256k1-fixed-base-scalar-mul": (50395, 49536, [
  ("~7900","ALIGN THE LIMB WIDTH TO THE PSEUDO-MERSENNE OFFSET: USE 8 LIMBS OF 32 BITS. p = 2^256 - 2^32 - 977, so at L=32 the 2^32 shift is EXACTLY ONE LIMB and the only fold blow-up is the 10-bit factor 977; at L=64 or L=86 the shift is MISALIGNED and costs 32-42 extra bits, landing straight on the carry witnesses. Modelled reduction cost per non-native multiply: L=86 -> 493, L=64 -> 401, L=32 -> 189, L=16 -> 186. THE GADGET AT L=32,k=8, 189 score: fold to 8 coefficients d'_0..d'_7 (free affine, |d'| <= 979*8*2^64 ~ 2^77); assert sum d'_m 2^(32m) = 0 mod n in ONE ROW with zero allocations; witness e0 (46 bits) and assert d'_0 = 2^32 e0; witness e1 (47 bits) and assert d'_1 + e0 = 2^32 e1. Then D = 0 mod 2^64 and mod n with |D| <= 2^301 < n*2^64 ~ 2^318, forcing D = 0 over Z. Costs: product rows go 7 -> 15 per multiply (+1,200) and the selection width C goes 6 -> 11 (+~1,500); reduction saves 2 x (401-189) x 25 = +10,600. NET ~ +7,900. The three Lean obligations are elementary: the |d'| interval bound from limb range checks, e0/e1 in range, and the CRT step. AFTER LANDING THIS, RE-SWEEP THE WINDOW WIDTH — the optimum moves DOWN as addition cost falls (modelled w=10 at S_add=1476), and holding w fixed gives most of the win back."),
  ("2700","LARGEST LEVER, PURE NUMERAL WORK, AND STILL UNTOUCHED AFTER SIX RECORDS. The folded-quotient range checks "
          "sit at 67/69/67 (ChainFold.lean:36 stageO2, :160 stageC1, :299 stageX) against DERIVED bounds of 33/36/33. "
          "Successive jobs have shaved ONE bit or sidestepped it — DERIVE THE BOUND INSTEAD. It is q <= cFold*H/p + 1 + "
          "bias_mult = 2^32 + 982 = 33 BITS for a 4p-biased fold; stageC1's is 36. RangeCheck n costs (n-1, n), so "
          "~2700 across 19 + 19 + 2 sites. FoldQuad and hgvFold are UNTOUCHED because q < 2^33 implies q < 2^67 — a "
          "numeral change plus ONE completeness bound per stage, and no soundness obligation."),
  ("1470","CARRY THE TABLE POINT'S y AS TWO WIRES, NOT FOUR — the consumer-functional law. The selected y is consumed at "
          "three sites and every one is an AFFINE ADDEND of a folded certificate, never a multiplicand: stageC1 via "
          "foldRhsY, stageYF via FoldQuadC1.rhsVec, and stageO2. THE COMB HAS NO DOUBLING AND NO TANGENT, so y never "
          "enters a denominator or interpolatedMul. GroupedFlex emits one carry over positions {0,1} plus one final "
          "polyEval row, so the certificate reads only Y_lo = y0 + 2^64 y1 and Y_hi = y2 + 2^64 y3. -70 per window x "
          "21, plus ~12 from shrunken FinalAdd routing. RE-DERIVE hgvFold: position 0 reaches ~1.25*2^131 against "
          "nfFoldR 0 = 2^132, carry width +2."),
  ("588","Select12's inner one-hot still misses the proved 2^w-w-1 minimum. RE-DERIVE FROM THE CURRENT TREE — the base "
         "has moved repeatedly (selectCost is now 283/284, below every earlier record) and the two-wire-y item changes "
         "N from 9 to 7."),
 ]),
 "secp256k1-scalar-mul": (316436, None, [
  ("~496","PORT finishXY FROM OUR OWN LOSING SUBMISSION e0e8dc40 (score 319301, VERIFIED). It ran from the same seed as "
          "the 319001 record and lost by 300, but it is CHEAPER on finishXYCost — 805/811 against the record's 809/815, "
          "-8 per site — and on mulModSub2F32Cost (365/368 against 365/370), and it carries a file the record lacks, "
          "divTargetS32Cost. finishXY sits inside fusedStep once per loop step, so at 62 steps this is worth up to "
          "~496. VERIFY THE SITE COUNT: the delta must propagate into fusedStep, glvStep and glvMSMAssert, or the count "
          "is wrong. Download the tree from /api/submissions/e0e8dc40-b896-40e8-a26e-7e770208be74/download."),
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
