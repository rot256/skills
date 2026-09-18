import Solution.Secp256k1ScalarMul.Params
import Solution.Secp256k1ScalarMul.ParamsFold
import Solution.Secp256k1ScalarMul.GroupedEqXV

/-!
# Grouped-carry schedule for the *tight* 32-bit folded certificate

This is the schedule of `ParamsFold32` re-derived at the smaller product-cell
cap that a call site with genuine 32-bit operands actually implies.  With
`Ca = Cb = 2^32` a convolution cell is below `t_k·2^64` where `t_k` is the
number of terms of that cell — the convolution term count is **triangular**,
`1, 2, …, 8, …, 2, 1`, not a uniform `8` — so the folded digit caps decay
steeply with the position:

  `D = [6840, 5871, 4894, 3917, 2940, 1963, 986, 9]`  (in units of `2^64`).

Two levers have to be pulled together, and neither works alone.  Making `Nf`
**position dependent** does nothing while the single materialised carry sits at
the bottom of the digit vector, because `OFF_L(0) ≈ Nf(gf₀ − 1)/2^B` is charged
at the *largest* cap in the first group; and regrouping does nothing while `Nf`
is a constant.  Doing both — groups `[6, 1, 1]` instead of `[2, 1, 5]`, so the
one range-checked carry now spans positions `0 … 5` and is charged at `D₅` — cuts
the carry from 45 bits to 43.

* a folded left digit at position `k` is `< D_k·2^64 + 3·2^32`;
* the quotient wire is 36 bits: the top convolution cell `c₁₄ = a₇·b₇`
  is a *single* product, so the folded integer is below `9·2^288 + 2^266`, which is
  under `2^36·p`;
* a right digit `q·p_k + t_k` is `< 2^69 + 3·2^64`;
* one 43-bit carry suffices, with the groups `[6, 1, 1]`.

Every bound below is written as an **exact** integer rather than rounded up to a
power of two: since the carry width is `⌈log₂(OFF_L + OFF_R)⌉`, rounding each
addend up would push that ceiling across an integer boundary and cost a full bit
at every site sharing the instance.

The resulting certificate costs `93/95`, against `101/103` for `MulModFold32`.
-/

namespace Solution.Secp256k1ScalarMul

/-- Group widths of the tight 32-bit folded schedule: `[6, 1, 1, 1, …]`. -/
def gfFold32T (k : ℕ) : ℕ := if k = 0 then 6 else 1

/-- Group start positions: `0, 6, 7, 8, …`. -/
def posOfFold32T (k : ℕ) : ℕ := if k = 0 then 0 else k + 5

/-- Position-dependent folded-digit multiplier, in units of `2^64`. -/
def dFold32T (k : ℕ) : ℕ :=
  if k = 0 then 6840 else if k = 1 then 5871 else if k = 2 then 4894
  else if k = 3 then 3917 else if k = 4 then 2940 else if k = 5 then 1963
  else if k = 6 then 986 else 9

/-- LHS coefficient cap: a folded digit at position `k` is `< D_k·2^64 + 3·2^32`. -/
def nfFold32TL (k : ℕ) : ℕ := dFold32T k * 2 ^ 64 + 3 * 2 ^ 32

/-- RHS coefficient cap: `q·p_k + t_k < 2^37·2^32 + 3·2^64 = 2^69 + 3·2^64`. -/
def nfFold32TR (_ : ℕ) : ℕ := 2 ^ 69 + 3 * 2 ^ 64

def offFold32TL (k : ℕ) : ℕ := if k = 0 then 8431020804991 else 4234837755822

def offFold32TR (_ : ℕ) : ℕ := 150323855395

def wfFold32T (_ : ℕ) : ℕ := 43

/-- Bit width of the folded quotient wire. -/
@[reducible] def qBitsFold32T : ℕ := 36

def vFold32TL : GroupedEqV.VParams where
  Nf := nfFold32TL
  OFFf := offFold32TL
  Wf := wfFold32T
  Nmax := 0
  OFFmax := 0
  Wmax := 43

def vFold32TR : GroupedEqV.VParams where
  Nf := nfFold32TR
  OFFf := offFold32TR
  Wf := wfFold32T
  Nmax := 0
  OFFmax := 0
  Wmax := 43

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem hgvFold32T :
    GroupedEqXV.GVXHyps circomPrime 8 32 gfFold32T posOfFold32T 3 vFold32TL vFold32TR := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, by norm_num, by decide, by decide, ?_⟩
  · intro k
    match k with
    | 0 => rfl
    | (n + 1) =>
      simp only [posOfFold32T, gfFold32T]
      split_ifs <;> omega
  · intro k; simp only [gfFold32T]; split_ifs <;> omega
  · intro k
    simp only [vFold32TL, wfFold32T]
    exact ⟨by norm_num, by decide⟩
  · intro j
    simp only [vFold32TL, vFold32TR, nfFold32TL, nfFold32TR, dFold32T]
    refine ⟨?_, by norm_num⟩
    split_ifs <;> norm_num
  · intro k hk
    have hcase : k = 0 ∨ k = 1 := by omega
    rcases hcase with rfl | rfl <;>
      exact ⟨by decide, ⟨by decide, by decide⟩, by decide⟩
  · decide

end Solution.Secp256k1ScalarMul
