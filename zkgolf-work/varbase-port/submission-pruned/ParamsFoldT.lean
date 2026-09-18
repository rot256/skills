import Solution.Secp256k1ScalarMul.ParamsFold

/-!
# Grouped-carry schedule for the *folded* certificate with a polynomial target

`MulModFoldT` certifies `polyValue T ≡ a·b (mod p)` where the target `T` is a
full `2m−1 = 7` position polynomial (not a reduced `BigInt`).  Both sides are
folded onto four positions with the pseudo-Mersenne relation
`2^256 ≡ cFold (mod p)`, so *both* digit families are bounded by `13·2^160`
(instead of the asymmetric `25·2^160 / 2^134` split of `MulModFold`).

The schedule is the same `[2, 1, 1]` grouping: a single carry, this time of
101 bits, plus the closing linear row.
-/

namespace Solution.Secp256k1ScalarMul

/-- LHS coefficient cap of the folded polynomial-target certificate.

Position 1 is *smaller*: it folds convolution cell 5, whose triangular term
count is only 2 (against the uniform bound of `numLimbs = 4`), so the folded
digit stays below `7·2^160` instead of `13·2^160`. -/
def nfFoldTL (k : ℕ) : ℕ := if k = 1 then 7 * 2 ^ 160 else 13 * 2 ^ 160

/-- RHS coefficient cap: `q·p_k + T_k + cFold·T_{k+4} < 2^166`.

Position 1 folds target cell 5, which every call site keeps below `6·2^128`
(it is either a two-term convolution cell scaled by 3, or a zero pad), so the
folded digit stays below `8·2^160`.  Together with the LHS refinement this is
exactly what brings the single grouped carry down from 101 to 100 bits. -/
def nfFoldTR (k : ℕ) : ℕ := if k = 1 then 8 * 2 ^ 160 else 13 * 2 ^ 160

def offFoldTL (k : ℕ) : ℕ :=
  if k = 0 then 7 * 2 ^ 96 + 13 * 2 ^ 32 else 13 * 2 ^ 96 + 13 * 2 ^ 32

def offFoldTR (k : ℕ) : ℕ :=
  if k = 0 then 8 * 2 ^ 96 + 13 * 2 ^ 32 else 13 * 2 ^ 96 + 13 * 2 ^ 32

def wfFoldT (k : ℕ) : ℕ := if k = 0 then 100 else 101

/-- Bit width of the quotient wire of the polynomial-target certificate. -/
@[reducible] def qBitsFoldT : ℕ := 69

def vFoldTL : GroupedEqV.VParams where
  Nf := nfFoldTL
  OFFf := offFoldTL
  Wf := wfFoldT
  Nmax := 0
  OFFmax := 0
  Wmax := 101

def vFoldTR : GroupedEqV.VParams where
  Nf := nfFoldTR
  OFFf := offFoldTR
  Wf := wfFoldT
  Nmax := 0
  OFFmax := 0
  Wmax := 101

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem hgvFoldT :
    GroupedEqXV.GVXHyps circomPrime 4 64 gfFold posOfFold 3 vFoldTL vFoldTR := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, by norm_num, by decide, by decide, by decide⟩
  · intro k
    match k with
    | 0 => rfl
    | (n + 1) => simp only [posOfFold, gfFold]; split_ifs <;> omega
  · intro k; simp only [gfFold]; split_ifs <;> omega
  · intro k
    simp only [vFoldTL, wfFoldT]
    split_ifs <;> exact ⟨by norm_num, by decide⟩
  · intro j
    simp only [vFoldTL, vFoldTR, nfFoldTL, nfFoldTR]
    split_ifs <;> exact ⟨by norm_num, by norm_num⟩
  · intro k hk
    have hcase : k = 0 ∨ k = 1 := by omega
    rcases hcase with rfl | rfl <;>
      exact ⟨by decide, ⟨by decide, by decide⟩, by decide⟩

end Solution.Secp256k1ScalarMul
