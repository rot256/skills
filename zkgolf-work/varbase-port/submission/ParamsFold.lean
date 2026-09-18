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

/-- LHS coefficient cap: folded product digits are `< 2^166`.

Position 1 is *smaller*: it folds convolution cell 5, whose triangular term
count is only 2 (against the uniform bound of `numLimbs = 4`), so the folded
digit stays below `7·2^160` instead of `13·2^160`.  That single fact is what
lets the first grouped carry be 99 bits wide rather than 100. -/
def nfFoldL (k : ℕ) : ℕ := if k = 1 then 7 * 2 ^ 160 else 13 * 2 ^ 160

/-- RHS coefficient cap: `q·p_k + t_k < 2^137`. -/
def nfFoldR (_ : ℕ) : ℕ := 2 ^ 133

def offFoldL (k : ℕ) : ℕ :=
  if k = 0 then 7 * 2 ^ 96 + 13 * 2 ^ 32 else 13 * 2 ^ 96 + 13 * 2 ^ 32

def offFoldR (_ : ℕ) : ℕ := 2 ^ 69 + 2 ^ 5

def wfFold (k : ℕ) : ℕ := if k = 0 then 99 else 100

/-- Bit width of the folded quotient wire.  The folded value satisfies
`D < 25·2^320` (the top folded digit is *not* multiplied by `cFold`, so it stays
below `2^133`), hence `q = (D − target)/p < 2^69`. -/
@[reducible] def qBitsFold : ℕ := 68

def vFoldL : GroupedEqV.VParams where
  Nf := nfFoldL
  OFFf := offFoldL
  Wf := wfFold
  Nmax := 0
  OFFmax := 0
  Wmax := 100

def vFoldR : GroupedEqV.VParams where
  Nf := nfFoldR
  OFFf := offFoldR
  Wf := wfFold
  Nmax := 0
  OFFmax := 0
  Wmax := 100

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem hgvFold :
    GroupedEqXV.GVXHyps circomPrime 4 64 gfFold posOfFold 3 vFoldL vFoldR := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, by norm_num, by decide, by decide, by decide⟩
  · intro k
    match k with
    | 0 => rfl
    | (n + 1) => simp only [posOfFold, gfFold]; split_ifs <;> omega
  · intro k; simp only [gfFold]; split_ifs <;> omega
  · intro k
    simp only [vFoldL, wfFold]
    split_ifs <;> exact ⟨by norm_num, by decide⟩
  · intro j
    simp only [vFoldL, vFoldR, nfFoldL, nfFoldR]
    split_ifs <;> exact ⟨by norm_num, Nat.one_le_two_pow⟩
  · intro k hk
    have hcase : k = 0 ∨ k = 1 := by omega
    rcases hcase with rfl | rfl <;>
      exact ⟨by decide, ⟨by decide, by decide⟩, by decide⟩

end Solution.Secp256k1ScalarMul
