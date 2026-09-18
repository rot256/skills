import Solution.Secp256k1ScalarMul.Params
import Solution.Secp256k1ScalarMul.GroupedEqXV

/-!
# Grouped-carry schedule for the *folded* modular-multiplication certificate

secp256k1's prime is pseudo-Mersenne, `p = 2^256 − 2^32 − 977`, i.e.
`2^256 ≡ cFold (mod p)` with `cFold = 2^32 + 977`.  The `L = 7` product
coefficients of `a·b` can therefore be *folded* onto `L = 4` positions by the
free linear recombination `d_k = c_k + cFold·c_{k+4}`, which shrinks the
quotient from a full 256-bit `BigInt` (4 witnesses + 252 range-check rows) to a
single 69-bit wire, and shortens the carry chain from three 68-bit carries to
a single 101-bit one.

The schedule below groups the four folded positions as `[2, 1, 1]`, so exactly
one carry (index 0, straddling positions 0–1) is materialised and the final two
positions are absorbed by the closing linear row.
-/

namespace Solution.Secp256k1ScalarMul

/-- `2^256 = p + cFold`; the pseudo-Mersenne fold constant. -/
def cFold : ℕ := 2 ^ 32 + 977

/-- Group widths of the folded schedule: `[2, 1, 1, …]`. -/
def gfFold (k : ℕ) : ℕ := if k = 0 then 2 else 1

/-- Group start positions of the folded schedule: `0, 2, 3, 4, …`. -/
def posOfFold (k : ℕ) : ℕ := if k = 0 then 0 else k + 1

end Solution.Secp256k1ScalarMul
