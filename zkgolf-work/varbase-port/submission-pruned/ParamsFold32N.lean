import Solution.Secp256k1ScalarMul.Params
import Solution.Secp256k1ScalarMul.ParamsFold
import Solution.Secp256k1ScalarMul.GroupedEqXV

/-!
# Grouped-carry schedule for the *mixed* 32-bit folded certificate

`MulModFold32` runs the pseudo-Mersenne fold `2^256 ≡ 2^32 + 977 (mod p)` in
base `2^32`, where the fold constant splits into the two tiny digits `977` and
`1`.  That schedule assumes *both* operands have 32-bit limbs, which caps a
product cell at `2^69`.

The schedule below is the same fold run at a much larger cell cap, `3·2^98`.
That is what one gets when only the *first* operand carries 32-bit limbs and
the second is an ordinary four-limb `Emu` re-read at the even 32-bit positions
(its odd positions are the literal zero expression).  Such a product cell is
bounded by `4·2^32·(3·2^64) ≤ 3·2^98` (only the four *even* positions of the
second operand are nonzero), so:

* a folded left digit is `< 2937·2^98 + 3·2^32 < 2^110`;
* the quotient wire is 69 bits (against 69 for the unfolded 64-bit schedule);
* a right digit `q·p_k + t_k` is `< 2^69·2^32 + 3·2^64 < 2^103`;
* one 78-bit carry suffices, with the groups `[3, 1, 4]`.

The resulting certificate costs `161/163`, against `176/178` for the 64-bit
`MulModFoldT` shape it replaces.
-/

namespace Solution.Secp256k1ScalarMul

/-- Group widths of the mixed 32-bit folded schedule: `[5, 1, 2, 2, …]`. -/
def gfFold32N (k : ℕ) : ℕ := if k = 0 then 5 else if k = 1 then 1 else 2

/-- Group start positions: `0, 5, 6, 8, 10, …`. -/
def posOfFold32N (k : ℕ) : ℕ := if k = 0 then 0 else if k = 1 then 5 else 2 * k + 2

/-- Position-dependent folded-digit multiplier, in units of the cell cap.

A convolution's term count is *triangular*, and here only the *even* positions
of the second operand are nonzero, so the `k`-th cell carries at most
`sparseCnt k ∈ {1,1,2,2,3,3,4,4,3,3,2,2,1,1,0}` terms.  The folded digit
`c_k + 977·c_{k+8} + c_{k+7}` therefore decays steeply with the position
instead of sitting at the uniform maximum `979·4`. -/
def dFold32N (k : ℕ) : ℕ :=
  if k = 0 then 2932 else if k = 1 then 2935 else if k = 2 then 1959
  else if k = 3 then 1958 else if k = 4 then 982 else if k = 5 then 981
  else if k = 6 then 5 else 4

/-- LHS coefficient cap: a folded digit at position `k` is `< D_k·(3 * 2 ^ 96) + 2^34`. -/
def nfFold32NL (k : ℕ) : ℕ := dFold32N k * (3 * 2 ^ 96) + 2 ^ 34

/-- RHS coefficient cap. -/
def nfFold32NR (_ : ℕ) : ℕ := 2 ^ 100 + 3 * 2 ^ 64

def offFold32NL (k : ℕ) : ℕ := if k = 0 then 54344108066376976963321 else 54288767821580184065782

def offFold32NR (_ : ℕ) : ℕ := 295147905260957204499

def wfFold32N (_ : ℕ) : ℕ := 76

/-- Bit width of the folded quotient wire. -/
@[reducible] def qBitsFold32N : ℕ := 68

def vFold32NL : GroupedEqV.VParams where
  Nf := nfFold32NL
  OFFf := offFold32NL
  Wf := wfFold32N
  Nmax := 0
  OFFmax := 0
  Wmax := 76

def vFold32NR : GroupedEqV.VParams where
  Nf := nfFold32NR
  OFFf := offFold32NR
  Wf := wfFold32N
  Nmax := 0
  OFFmax := 0
  Wmax := 76

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem hgvFold32N :
    GroupedEqXV.GVXHyps circomPrime 8 32 gfFold32N posOfFold32N 3 vFold32NL vFold32NR := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, by norm_num, by decide, by decide, ?_⟩
  · intro k
    match k with
    | 0 => rfl
    | 1 => rfl
    | (n + 2) =>
      simp only [posOfFold32N, gfFold32N]
      split_ifs <;> omega
  · intro k; simp only [gfFold32N]; split_ifs <;> omega
  · intro k
    simp only [vFold32NL, wfFold32N]
    exact ⟨by norm_num, by decide⟩
  · intro j
    simp only [vFold32NL, vFold32NR, nfFold32NL, nfFold32NR, dFold32N]
    refine ⟨?_, by norm_num⟩
    split_ifs <;> norm_num
  · intro k hk
    have hcase : k = 0 ∨ k = 1 := by omega
    rcases hcase with rfl | rfl <;>
      exact ⟨by decide, ⟨by decide, by decide⟩, by decide⟩
  · decide

end Solution.Secp256k1ScalarMul
