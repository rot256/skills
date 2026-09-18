import Solution.Secp256k1ScalarMul.Params
import Solution.Secp256k1ScalarMul.ParamsFold
import Solution.Secp256k1ScalarMul.GroupedEqXV

/-!
# Grouped-carry schedule for the *deferred* mod-`n` congruence

The GLV scalar-side relation

`u₁ + λ·u₂ + s·(v₁ + λ·v₂) ≡ 0  (mod n)`

is certified without ever reducing the four partial products mod `n`.  Each of
the four signed terms is carried as a four-position limb vector whose cells are
allowed to be as wide as `2^131`; the whole identity is closed by a *single*
grouped carry plus one linear row, exactly as the folded `p`-certificate does.

The schedule reuses `gfFold`/`posOfFold` (groups `[2,1,1]`), so exactly one
carry — straddling positions 0–1 — is materialised.
-/

namespace Solution.Secp256k1ScalarMul

/-- Bias multiplier: the LHS is biased by `biasKRel · n` so that the certified
integer difference is non-negative. -/
@[reducible] def biasKRel : ℕ := 2 ^ 66

/-- Bit width of the deferred-congruence quotient wire. -/
@[reducible] def qBitsRel : ℕ := 67

/-- LHS cell cap.  Position `1` is capped tightly: the true maximum of cell 1 is
`λ₁·(2^64-1) + 2·(2^128-1) + 2^66·n₁ < 5·2^128`, well below the generic `2^131`.
Only `wfRel 0` is charged, and it is driven by `Nf 1` through the group-0
offset, so tightening this one position buys a bit of carry width. -/
def nfRelL (k : ℕ) : ℕ := if k = 1 then 5 * 2 ^ 128 else 2 ^ 131

/-- RHS cell cap; position `1` tightened as for `nfRelL`. -/
def nfRelR (k : ℕ) : ℕ := if k = 1 then 10 * 2 ^ 128 else 2 ^ 132

def offRelL (k : ℕ) : ℕ := if k = 0 then 5 * 2 ^ 64 + 7 else 2 ^ 67 + 8

def offRelR (k : ℕ) : ℕ := if k = 0 then 10 * 2 ^ 64 + 15 else 2 ^ 68 + 16

def wfRel (k : ℕ) : ℕ := if k = 0 then 68 else 69

def vRelL : GroupedEqV.VParams where
  Nf := nfRelL
  OFFf := offRelL
  Wf := wfRel
  Nmax := 0
  OFFmax := 0
  Wmax := 69

def vRelR : GroupedEqV.VParams where
  Nf := nfRelR
  OFFf := offRelR
  Wf := wfRel
  Nmax := 0
  OFFmax := 0
  Wmax := 69

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem hgvRel :
    GroupedEqXV.GVXHyps circomPrime 4 64 gfFold posOfFold 3 vRelL vRelR := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, by norm_num, by decide, by decide, by decide⟩
  · intro k
    match k with
    | 0 => rfl
    | (n + 1) => simp only [posOfFold, gfFold]; split_ifs <;> omega
  · intro k; simp only [gfFold]; split_ifs <;> omega
  · intro k
    simp only [vRelL, wfRel]
    split_ifs <;> exact ⟨by norm_num, by decide⟩
  · intro j
    simp only [vRelL, vRelR, nfRelL, nfRelR]
    split_ifs <;> exact ⟨by norm_num, by norm_num⟩
  · intro k hk
    have hcase : k = 0 ∨ k = 1 := by omega
    rcases hcase with rfl | rfl <;>
      exact ⟨by decide, ⟨by decide, by decide⟩, by decide⟩

end Solution.Secp256k1ScalarMul
