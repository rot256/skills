# Case study: SHA-256 in R1CS (the `clean` reductions)

A worked example of stacking the techniques in `techniques.md` on a real primitive.
Source: `~/src/clean` (`Clean/Gadgets/SHA256/`, `tricks.md`). Every step is backed by
a Lean soundness **and** completeness proof — optimization without a correctness
regression. `W` = witnesses, `C` = constraints (per block unless noted).

This is illustrative, **not a ceiling.** Each step opened the next; the last word has
not been written.

## The reductions, in order

### 1. Multi-operand `AddMod32` (technique §1–§2)

Linear combinations are free; only product rows cost. So instead of chaining binary
`add32` (each re-witnesses 32 output bits + a carry), sum all `n ≤ 8` operands as one
free linear combination and bit-decompose **once**:

- per call: 32 output-bit witnesses + `cw` carry witnesses, `32+cw` booleanity rows,
  and **1** linear row `Σ value(opⱼ) = value(z) + 2³²·Σ 2ⁱ cᵢ`.
- Soundness lifts the field equation to ℕ because the operand sum is `< 8·2³² = 2³⁵ < p`.

Effect: the 6-/7-operand Davies–Meyer adds for `new_a`/`new_e` collapse from an
`add32` chain to one reduction each — round **455 → 294 W**. Schedule uses
`(a+b+c+d) mod 2³² = add32 (add32 a b) (add32 c d)` as a single 4-operand add: step
**227 → 163 W**, schedule **10896 → 7824 W**.

### 2. Minimal carry width (technique §2)

The sum is `< n·2³²`, so the carry `≤ n−1`; `cw` carry bits suffice when `n ≤ 2^cw`.
`AddMod32` is parameterized by `cw` (`2^cw ≤ 8` keeps the soundness lift valid) and
each caller picks the minimum. Round adds (`n=6,7`) keep `cw=3`; schedule add (`n=4`)
drops to `cw=2` → **−48 W, −48 C** per block (one carry bit + one booleanity row on
each of the 48 schedule steps). Soundness needs only `2^cw ≤ 8`; completeness uses
`n ≤ 2^cw`.

### 3. Carry-save witness halving for Σ/σ and Maj (technique §3)

The four Σ/σ are 3-input XORs, `Maj` is 3-input majority. Use
`a+b+c = (a⊕b⊕c) + 2·maj(a,b,c)`: witness only the **carry bit** (= `maj`) per output
bit; the XOR result is consumed downstream by `AddMod32` as an **un-witnessed linear
combination** `a+b+c−2·cy`. Halves each Σ/σ and `Maj` from 64 → 32 witnesses; block
**26904 → 17688 W**. Needs char ∉ {2,3} (already have `p > 2³⁵`). Soundness is *not*
local: `cy`'s booleanity alone does not force `cy = maj` (see techniques.md §3) — it
is the composed `FormalCircuit`, where the downstream bit-decomposition pins the
aggregate, that makes this sound. That subtlety is exactly what motivated step 4.

### 4. Single-constraint-per-bit for Σ/σ (XOR3) and Maj (technique §4)

The shipped encoding. Replace the carry-save *two* rows per bit with **one** quadratic
row per output bit, linear in `o` with a multiplier that never vanishes on the boolean
cube (values only `±1,±2,±3,±4`), so `o` is uniquely the target bit and no separate
booleanity row is needed:

- **XOR3:** `(o + 2a + 2b + 7c)(a + b − 4c + 1) = 6a + 6b − 24c`
- **Maj:**  `(o + a + b − 9c + 3)(a + b + 6c − 4) = −12`

Effect (constraints): Σ/σ XOR block **27088 → 19920 C** (−26%); Maj 64 → 32 per call,
block **19920 → 17872 C**. Witness counts unchanged.

## How the constants were found and proved (the tool loop)

This is the canonical SMT + Sage + proof-assistant pipeline this skill teaches:

1. **Search** the coefficients: a search over small R1CS encodings — a quadratic
   surface through the eight `(a,b,c,target)` points whose `o`-multiplier never vanishes
   on the cube. (`scripts/synthesize.sage` does the linear-algebra version over `QQ`,
   giving prime-independent constants; cvc5 `QF_FF` can search too but returns
   field-specific, often ugly constants — see `smt.md`.)
2. **Verify** the encoding forces the target and pins `o` to a bit, over the actual
   `F_p` (`scripts/verify.smt2`, cvc5 `QF_FF` `unsat` of the negation — no
   "unit over the reals" caveat; `scripts/impossible.smt2` for the impossibility
   direction, see `smt.md`). On the asymmetry: a brute-force search shows
   no symmetric encoding with **small integer coefficients** exists — which is why
   `clean` uses the asymmetric `−9c`/`6c` form. Note the scope: over a field a
   symmetric encoding *does* exist (`(o − s/4)(9 − 6s) = −3s/4`, `s=a+b+c`), so
   "asymmetry unavoidable" is an *integer-coefficient* statement, not a field one.
   (`clean`'s tricks.md/`CarrySave.lean` state this without the qualifier — worth
   tightening there.)
3. **Certify** for the proof assistant: a Gröbner-basis ideal lift gives the
   `linear_combination` cofactors for the soundness (`xor3_unique`, `maj3_unique`) and
   completeness (`xor3_complete`, `maj3_complete`) proofs
   (`scripts/cofactors.sage` reproduces them exactly).

Shared lemmas live in `Clean/Gadgets/SHA256/CarrySave.lean`.

## Lessons that generalize

- **Count what your model charges for.** Here two scarce resources (W and C) trade
  against each other; techniques 3 and 4 move cost between them.
- **Each trick exposes the next.** Multi-operand add made the XOR result a free linear
  combination, which made carry-save profitable, which motivated the single-constraint
  encoding.
- **Optimize with proofs attached.** Every reduction kept soundness + completeness
  proofs green, so "faster" never silently became "unsound."
- **Bounds are the soundness surface.** `p > 2³⁵`, `2^cw ≤ 8`, char ∉ {2,3} — each
  reduction is valid only inside a stated bound. Track them.

## Not done

Lookups (spread tables, §7) and a PLONKish layout (§8) are untouched here and would
change the picture entirely on a different backend. The R1CS numbers above are a local
optimum for one arithmetization, not the global best for SHA-256. Keep looking.
