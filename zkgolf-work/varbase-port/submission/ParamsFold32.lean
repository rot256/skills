import Solution.Secp256k1ScalarMul.Params
import Solution.Secp256k1ScalarMul.ParamsFold
import Solution.Secp256k1ScalarMul.GroupedEqXV

/-!
# Grouped-carry schedule for the *32-bit* folded certificate

`p = 2^256 − 2^32 − 977`, so `2^256 ≡ cFold = 2^32 + 977 (mod p)`.  In base
`2^64` that constant is a single 33-bit digit; in base `2^32` it is the two
*tiny* digits `977` and `1`.  Since the fold constant enters the carry width
linearly, running the certificate on eight 32-bit limbs shrinks the quotient
from 69 bits to 38 and the single grouped carry from 101 bits to 48 — the
15-cell convolution costs 8 rows more, so a certificate goes from 176/178 to
101/103.

Schedule: `L = 8` positions, groups `[2, 1, 5]` (`G = 3`), so exactly one
48-bit carry is materialised (straddling positions 0–1) and the remaining six
positions are absorbed by the closing linear row.
-/

namespace Solution.Secp256k1ScalarMul

/-- Group widths of the 32-bit folded schedule: `[6, 1, 1, 1, …]`. -/
def gfFold32 (k : ℕ) : ℕ := if k = 0 then 6 else 1

/-- Group start positions: `0, 6, 7, 8, …`. -/
def posOfFold32 (k : ℕ) : ℕ := if k = 0 then 0 else k + 5

/-- Position-dependent folded-digit multiplier, in units of `Ca·Cb = 2^66`.

A convolution's term count is *triangular* — `1, 2, …, 8, …, 2, 1` — so the
folded digit `c_k + 977·c_{k+8} + c_{k+7}` decays steeply with the position
instead of sitting at the uniform maximum `979·8`. -/
def dFold32 (k : ℕ) : ℕ :=
  if k = 0 then 6840 else if k = 1 then 5871 else if k = 2 then 4894
  else if k = 3 then 3917 else if k = 4 then 2940 else if k = 5 then 1963
  else if k = 6 then 986 else 9

/-- LHS coefficient cap: a folded digit at position `k` is `< D_k·2^66 + 3·2^32`. -/
def nfFold32L (k : ℕ) : ℕ := dFold32 k * 2 ^ 66 + 3 * 2 ^ 32

/-- RHS coefficient cap: `q·p_k + t_k < 2^39·2^32 + 3·2^64 < 2^72`. -/
def nfFold32R (_ : ℕ) : ℕ := 2 ^ 71 + 3 * 2 ^ 64

def offFold32L (k : ℕ) : ℕ := if k = 0 then 33724083219955 else 16939351023279

def offFold32R (_ : ℕ) : ℕ := 562640715907

def wfFold32 (_ : ℕ) : ℕ := 45

/-- Bit width of the folded quotient wire. -/
@[reducible] def qBitsFold32 : ℕ := 38

def vFold32L : GroupedEqV.VParams where
  Nf := nfFold32L
  OFFf := offFold32L
  Wf := wfFold32
  Nmax := 0
  OFFmax := 0
  Wmax := 45

def vFold32R : GroupedEqV.VParams where
  Nf := nfFold32R
  OFFf := offFold32R
  Wf := wfFold32
  Nmax := 0
  OFFmax := 0
  Wmax := 45

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem hgvFold32 :
    GroupedEqXV.GVXHyps circomPrime 8 32 gfFold32 posOfFold32 3 vFold32L vFold32R := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, by norm_num, by decide, by decide, ?_⟩
  · intro k
    match k with
    | 0 => rfl
    | (n + 1) =>
      simp only [posOfFold32, gfFold32]
      split_ifs <;> omega
  · intro k; simp only [gfFold32]; split_ifs <;> omega
  · intro k
    simp only [vFold32L, wfFold32]
    exact ⟨by norm_num, by decide⟩
  · intro j
    simp only [vFold32L, vFold32R, nfFold32L, nfFold32R, dFold32]
    refine ⟨?_, by norm_num⟩
    split_ifs <;> norm_num
  · intro k hk
    have hcase : k = 0 ∨ k = 1 := by omega
    rcases hcase with rfl | rfl <;>
      exact ⟨by decide, ⟨by decide, by decide⟩, by decide⟩
  · decide

end Solution.Secp256k1ScalarMul
