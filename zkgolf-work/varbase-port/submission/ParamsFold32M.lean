import Solution.Secp256k1ScalarMul.Params
import Solution.Secp256k1ScalarMul.ParamsFold
import Solution.Secp256k1ScalarMul.GroupedEqXV

/-!
# Grouped-carry schedule for the *mixed* 32-bit folded certificate

`MulModFold32` runs the pseudo-Mersenne fold `2^256 ≡ 2^32 + 977 (mod p)` in
base `2^32`, where the fold constant splits into the two tiny digits `977` and
`1`.  That schedule assumes *both* operands have 32-bit limbs, which caps a
product cell at `2^69`.

The schedule below is the same fold run at a much larger cell cap, `3·2^99`.
That is what one gets when only the *first* operand carries 32-bit limbs and
the second is an ordinary four-limb `Emu` re-read at the even 32-bit positions
(its odd positions are the literal zero expression).  Such a product cell is
bounded by `4·2^33·(3·2^64) ≤ 3·2^99` (only the four *even* positions of the
second operand are nonzero), so:

* a folded left digit is `< 2937·2^99 + 3·2^32 < 2^111`;
* the quotient wire is 70 bits (against 69 for the unfolded 64-bit schedule);
* a right digit `q·p_k + t_k` is `< 2^70·2^32 + 3·2^64 < 2^104`;
* one 79-bit carry suffices, with the groups `[3, 1, 4]`.

The resulting certificate costs `163/165`, against `176/178` for the 64-bit
`MulModFoldT` shape it replaces.
-/

namespace Solution.Secp256k1ScalarMul

/-- Group widths of the mixed 32-bit folded schedule: `[5, 1, 2, 2, …]`. -/
def gfFold32M (k : ℕ) : ℕ := if k = 0 then 5 else if k = 1 then 1 else 2

/-- Group start positions: `0, 5, 6, 8, 10, …`. -/
def posOfFold32M (k : ℕ) : ℕ := if k = 0 then 0 else if k = 1 then 5 else 2 * k + 2

/-- Position-dependent folded-digit multiplier, in units of the cell cap.

A convolution's term count is *triangular*, and here only the *even* positions
of the second operand are nonzero, so the `k`-th cell carries at most
`sparseCnt k ∈ {1,1,2,2,3,3,4,4,3,3,2,2,1,1,0}` terms.  The folded digit
`c_k + 977·c_{k+8} + c_{k+7}` therefore decays steeply with the position
instead of sitting at the uniform maximum `979·4`. -/
def dFold32M (k : ℕ) : ℕ :=
  if k = 0 then 2932 else if k = 1 then 2935 else if k = 2 then 1959
  else if k = 3 then 1958 else if k = 4 then 982 else if k = 5 then 981
  else if k = 6 then 5 else 4

/-- LHS coefficient cap: a folded digit at position `k` is `< D_k·(3 * 2 ^ 97) + 2^34`. -/
def nfFold32ML (k : ℕ) : ℕ := dFold32M k * (3 * 2 ^ 97) + 2 ^ 34

/-- RHS coefficient cap. -/
def nfFold32MR (_ : ℕ) : ℕ := 2 ^ 101 + 3 * 2 ^ 64

def offFold32ML (k : ℕ) : ℕ := if k = 0 then 108688216132753953926638 else 108577535643160368131560

def offFold32MR (_ : ℕ) : ℕ := 590295810509029507107

def wfFold32M (_ : ℕ) : ℕ := 77

/-- Bit width of the folded quotient wire. -/
@[reducible] def qBitsFold32M : ℕ := 69

def vFold32ML : GroupedEqV.VParams where
  Nf := nfFold32ML
  OFFf := offFold32ML
  Wf := wfFold32M
  Nmax := 0
  OFFmax := 0
  Wmax := 77

def vFold32MR : GroupedEqV.VParams where
  Nf := nfFold32MR
  OFFf := offFold32MR
  Wf := wfFold32M
  Nmax := 0
  OFFmax := 0
  Wmax := 77

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem hgvFold32M :
    GroupedEqXV.GVXHyps circomPrime 8 32 gfFold32M posOfFold32M 3 vFold32ML vFold32MR := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, by norm_num, by decide, by decide, ?_⟩
  · intro k
    match k with
    | 0 => rfl
    | 1 => rfl
    | (n + 2) =>
      simp only [posOfFold32M, gfFold32M]
      split_ifs <;> omega
  · intro k; simp only [gfFold32M]; split_ifs <;> omega
  · intro k
    simp only [vFold32ML, wfFold32M]
    exact ⟨by norm_num, by decide⟩
  · intro j
    simp only [vFold32ML, vFold32MR, nfFold32ML, nfFold32MR, dFold32M]
    refine ⟨?_, by norm_num⟩
    split_ifs <;> norm_num
  · intro k hk
    have hcase : k = 0 ∨ k = 1 := by omega
    rcases hcase with rfl | rfl <;>
      exact ⟨by decide, ⟨by decide, by decide⟩, by decide⟩
  · decide

end Solution.Secp256k1ScalarMul
