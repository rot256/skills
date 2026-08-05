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
 "secp256k1-fixed-base-scalar-mul": (50825, 49536, [
  ("42","FREE, TWO LINES, DO IT FIRST. SelectCost.lean witnesses `bits : fields 3` plus 3 booleanity rows plus one "
        "linking row selectedE = b0 + 2*b1 + 4*b2 = 3 alloc / 4 rows, where `RangeCheck.circuit 3` applied to selectedE "
        "is 2 alloc / 3 rows — RangeCheck n is (n-1, n) on an EXPRESSION. The do-not-allocate-the-top-bit rule is "
        "simply not applied at this site. 2 score x 21 windows."),
  ("2700","LARGEST LEVER, PURE NUMERAL WORK, AND STILL ESSENTIALLY UNTOUCHED. The folded-quotient range checks sit at "
          "67/69/67 (ChainFold.lean:36 stageO2, :160 stageC1, :299 stageX) against DERIVED bounds of 33/36/33. Two "
          "separate jobs have now shaved ONE bit each instead of deriving the value — do not do that again. THE TRUE "
          "BOUND IS q <= cFold*H/p + 1 + bias_mult = 2^32 + 982 = 33 BITS for a 4p-biased fold; stageC1's is 36. "
          "RangeCheck n costs (n-1, n), so ~2700 across 19 + 19 + 2 sites. FoldQuad and hgvFold are UNTOUCHED because "
          "q < 2^33 implies q < 2^67 — a numeral change plus ONE completeness bound per stage, no soundness obligation."),
  ("1470","CARRY THE TABLE POINT'S y AS TWO WIRES, NOT FOUR — the consumer-functional law. The selected y is consumed at "
          "three sites and every one is an AFFINE ADDEND of a folded certificate, never a multiplicand: stageC1 via "
          "foldRhsY, stageYF via FoldQuadC1.rhsVec, and stageO2. THE COMB HAS NO DOUBLING AND NO TANGENT, so y never "
          "enters a denominator or interpolatedMul. GroupedFlex emits one carry over positions {0,1} plus one final "
          "polyEval row, so the certificate reads only Y_lo = y0 + 2^64 y1 and Y_hi = y2 + 2^64 y3. Current y side is "
          "82/83 (yNegProd 60/60 + eProd 15/15 + bits 3/3 + link 0/1 + y 4/4); proposed 47/48 (yNegProd 2 wires x 15, "
          "eProd holding ONE borrow bit since merging limbs 2,3 and 0,1 cancels the internal borrows, that bit as "
          "RangeCheck 1 on the selected expression = 0/1, y 2/2). -70 per window x 21, plus ~12 from shrunken FinalAdd "
          "routing. RE-DERIVE hgvFold: position 0 reaches ~1.25*2^131 against nfFoldR 0 = 2^132, carry width +2."),
  ("588","Select12's inner one-hot still misses the proved 2^w-w-1 minimum. RE-DERIVE FROM THE CURRENT TREE — the base "
         "has moved repeatedly (hot4 has been seen at both `fields 14` and `fields 15` across records) and the "
         "two-wire-y item above changes N from 9 to 7. Do not use any older cell recipe."),
 ]),
 "secp256k1-scalar-mul": (331777, None, [
  ("~20000","FINISH THE 8x32 RE-LIMB — A THIRD OF IT LANDED, THE REST IS MECHANICAL. The 331777 record added "
            "Limbs32.lean (the 32-bit limb VIEW, a FREE AFFINE recombination x_k = v_{2k} + 2^32*v_{2k+1}) and "
            "DivOrZeroS32.lean (that view applied to the conditional slope certificate), worth -150 per slopeXS site "
            "= -10,523. THE Normalize IS COST-NEUTRAL between the views (8 + 8*31 = 256 alloc, 8*32 = 256 constr, "
            "identical to 4 + 4*63 and 4*64), so nothing is lost; the whole gain is that the fold constant 2^32 + 977 "
            "is TWO TINY LIMBS in base 2^32 against ONE 33-BIT limb in base 2^64, and that width enters the carry "
            "LINEARLY. BECAUSE THE VIEW IS AFFINE IT CAN BE ADOPTED PER CERTIFICATE — no whole-tree rewrite. STILL ON "
            "THE 64-BIT VIEW: slope2, slopeLam, finishXY, mulModSub2, and the PointValid certificates. Port "
            "DivOrZeroS32's shape to each; the only obligation is the per-site carry bound, since the Spec is "
            "unchanged."),
  ("~189 each","SIZE EVERY QUOTIENT RANGE CHECK TO ITS CALL SITE, NOT TO ITS TYPE — the newest landed mechanism and "
          "the same error class as the fixed-base 67-bits-against-33 item. MulModLooseQ.lean shows the pattern: "
          "MulModLoose witnesses q = a*b/n as a full 4-limb BigInt and range-checks all four limbs at 252/256, but every "
          "scalar-side GLV call site multiplies by a value below 2^limbBits so the honest q < 2^65 — low limb full "
          "check, second limb BOOLEAN, top two ASSERTED ZERO, giving 63/64 + 0/1 + 0/1 + 0/1 = 63/67 and -189 per site "
          "with NO change to the certificate or the Spec. SWEEP EVERY REMAINING Normalize / NormalizeTight / "
          "full-width quotient check in this tree and ask: what is the largest value this witness can honestly take "
          "GIVEN THE OPERANDS AT THIS SITE? Anything bounded well below its declared width is paying for bits it can "
          "never use."),
  ("~531 each","KEEP SWEEPING MulModSub2 FOR THE 'ASSERTION, NOT VALUE' REWRITE — PARTLY LANDED, MORE REMAINS, AND IT IS "
          "THE LARGEST SYSTEMATIC LEVER LEFT. MulModSub2 witnesses the canonical remainder and pays ValidP (260/267) plus "
          "four limb witnesses = 440/445 = 885. Where NO CONSUMER READS THE REMAINDER — it only has to be zero — replace "
          "it with MulModEqFold: one MulModFold certificate run directly against target 0 + s1 + s2, 176/178 = 354, "
          "saving 531. ALREADY CONVERTED, DO NOT REDO: PointValid (1576/1604 -> 1143/1166, -871, more than one site) and "
          "the terminal glvStepLastSlope. THE ATOM HAS MOVED AGAIN since those notes: divOrZeroF3 is now 448/450 (it was "
          "460/462, and 468/473 before that), after a SECOND assertion-not-value pass at the same 134 sites worth "
          "-24 each, plus SqEqGated (a GATED congruence folded with no materialised remainder: mux BOTH the factor "
          "and the target against zero so the gated branch degenerates to 0 = 0, 184/186 against 440/445) and "
          "denSafeVec (a zero-guard as an affine addend on limb 0 instead of a 4/4 Mux). RE-MEASURE THE ATOM BEFORE "
          "COSTING; with ~350 live certificates the rest of the tree is unswept. NO soundness obligation — the folded certificate proves more, "
          "not less. Audit each site by asking: does anything READ this remainder, or does it only need to VANISH?"),
  ("~500","AUDIT EVERY REMAINING ValidP CALL THE WAY PointValid WAS AUDITED, with the same question in its other form: "
          "does any consumer need UNIQUENESS, or only the congruence class / a range bound? Canonicality is uniqueness, "
          "and most consumers need neither. The NormalizeFe weakening has already landed at 134 divOrZeroF3 sites and at "
          "both divUncheckedD3 sites in PhiPairAdd — do not redo those."),
  ("32400","RE-LIMB 4x64 -> 8x32, AND SHIP IT ALONE — the old instruction to ship it with the all-odd recode is RETRACTED, "
           "they are INDEPENDENT. The fold constant c = 2^32 + 977 is ONE 33-bit limb in base 2^64 (f = 32) but two tiny "
           "limbs (977, 1) in base 2^32 (f ~ 10), and f enters the carry width LINEARLY. CERT(4x64) = 176/178 = 354 "
           "measured; CERT(8x32) ~ 205, delta 150 +- 6. Then 350 certificates x 150 = -52,500, against 64 lookups x +240 "
           "= +15,360, 62 steps x +72 mux widening = +4,464, and ~300 table muxes: NET -32,376. FRESH is unchanged, so "
           "the 512-per-element floor is untouched. IGNORE any older entry quoting CERT 365 -> 214 or -26,600 — it is "
           "internally inconsistent, though its bottom line is close. NOTE: re-measure CERT against the CURRENT tree "
           "first; MulModEqFold has already changed which certificates are live."),
  ("~2500","MARGINAL, DO LAST, AND ONLY AFTER 8x32: the all-odd signed-digit recode (digits d_i = 2b_i - 1 in {+-1}, a "
           "pure wire permutation at 0/0). Its ledger is NOT the -22k an older entry claims: lookups -9,600, but only "
           "about half the exception apparatus is deletable (-3,100) because R = O and x_S = x are NOT excludable, the "
           "parity obligation costs ONE OR TWO extra glvStep at 4,907 each, and the 8-entry +- table needs 12 additions "
           "against today's 11 (+2,781). NET -5,012 TO -112. The recode also does NOT make the table identity-free — six "
           "values of q still select O. Lean will need a COSET Minkowski (the short all-odd representative lives in a "
           "coset of 2L, covolume 16n, bound 2^65.6), not the existing pigeonhole."),
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
