# Variable-base port of the fixed-base lazy arithmetic (work in progress)

Port of the techniques from patchgravity's secp256k1 fixed-base record
(28,042; zk.golf submission d59c8bf7-9065-4e9c-9ef1-65074f7b2718) to the
variable-base scalar multiplication (our record 302,138).

Credits: the sparse 8x32 ring `Fr[t]/(t^8 - t - 977)`, the 12-product CRT
multiply, the zero-row two-half certificate (`Sparse32Cert`), lazy `x` with a
bounded envelope and the balanced-digit slope representation are
patchgravity's; the exception handling and the variable-base step design below
are ours.

## Settled step design (cost units = allocations + constraints)

Order `(R + T) + R` with the cancelled form `x' = b^2 - a^2 + T.x`, which keeps
the lazy `x` envelope constant at 76 bits and `y` at 126 bits over 62 steps
(`envelope4.py`, variant without the T-infinity branch; layouts in
`elm2.json`).  Two other orders were modelled and rejected:

* double-then-add (`envelope3.py`): `x` doubles every step, certificate
  residual exceeds the native prime by step 30 (unsound);
* the unified slope formula `a (yR + Ty) = xR^2 + xR Tx + Tx^2`: residual 262
  bits > native prime (unsound with the two-half certificate).

Per step:

| item | units |
|---|---|
| two slope witnesses + `Sparse32Normalize` range checks | 1,024 |
| products (chord mul, two squares, rel2 mul, y' mul, tangent-at-T) | ~150 |
| certificate slots: chord/y-eq (85/93), x-eq (37/46), tangent-at-T (69/99), rel2 (86/94) | ~1,210 |
| output muxes and flags | ~130 |
| VarLookup (unchanged) | 244 |

About 2,750 per step, ~171k for the chain, ~205k to 215k total.

## Exceptions (all real on variable base)

* `T = R` and `T = -R` are common in early steps (consecutive nibble patterns
  coincide, probability ~1/16 per step), so they are handled in-circuit with
  prover flags `e` (x-equality certified in the x-eq slot) and `s` (sign;
  `y`-equality folded into the chord slot content).  `T = R` computes
  `S = 2T` with the tangent at the canonical table point.
* `T = -2R` (flag `z`, x-eq of `xS` and `xR` shares the x-eq slot) outputs
  infinity; `R = ∞` outputs `T` by mux.
* `T = ∞` only occurs for eight special scalars under all-odd recoding; it is
  delegated to a global fallback (`Σ σ_i B_i = ∞` with the existing complete
  adders, `σ ∈ {±1}^4`) and per step `(1 - sp) · tInf = 0` is asserted.
* All-odd recoding needs a parity correction: the final assertion becomes
  `acc = -Σ p_i B_i`.

## Files

* `Interval.lean` — generic rectangle-corner bounds for `sparseMul` with
  arbitrary coefficient envelopes (first Lean file of the port; lives at
  `Solution/Secp256k1ScalarMul/Lazy/Interval.lean` in the Lake project).
* `envelope*.py`, `gen4.py` — envelope models; `envelope.py` reproduces
  patchgravity's `wideKmin` table exactly (validation).
