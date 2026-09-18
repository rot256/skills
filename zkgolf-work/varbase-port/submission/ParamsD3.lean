import Solution.Secp256k1ScalarMul.Params
import Solution.Secp256k1ScalarMul.MulMod

/-!
# `L=8` wide-quotient grouped-carry schedule (`D3` family)

Schedule for the triply-unreduced-multiplicand `MulModTargetD3` certificate:
the LHS carries `a·b` with `b` triply unreduced (limbs `< 3·2^64`, coefficient
cap `15·2^128`), the RHS carries `q·n + target` with a 6-cell quotient
(4 limbs + two-bit top), so the convolution spans `L = 8` positions. Same
paid-group partition `[2,2,2]` as the `D` family (the instrument recursion
reproduces the `D` tables exactly and yields these at the widened cap); the
three offset carries widen from 68 to 69 bits.
-/

namespace Solution.Secp256k1ScalarMul

/-- Group sizes `[2,2,2,1,1]` (groups 3–4 are the unpaid terminal zone). -/
def gfMulD3 (k : ℕ) : ℕ := if k ≤ 2 then 2 else 1

/-- Group start positions `[0,2,4,6,7]`, then `k+3` onward. -/
def posOfMulD3 (k : ℕ) : ℕ := if k ≤ 3 then 2 * k else k + 3

/-- LHS coefficient cap for the triply-unreduced multiplicand:
`3·(m+1)·2^(2B) = 15·2^128` dominates the `< 12·2^128` wide product. -/
def nfMulD3 (_ : ℕ) : ℕ := 15 * 2 ^ 128

/-- RHS coefficient cap: unchanged `(m+1)·2^(2B) = 5·2^128` (the two-bit top
quotient contributes `< 3·2^64` per position, absorbed by the `(m+1)` slack). -/
def nfrMulD3 (_ : ℕ) : ℕ := 5 * 2 ^ 128

/-- LHS offset schedule (`15·2^64 + 14`, then `15·2^64 + 15`). -/
def offMulD3 (k : ℕ) : ℕ :=
  if k = 0 then 276701161105643274254 else 276701161105643274255

/-- RHS offset schedule (`5·2^64 + 4`, then `5·2^64 + 5`). -/
def offrMulD3 (k : ℕ) : ℕ :=
  if k = 0 then 92233720368547758084 else 92233720368547758085

def wfMulD3 (_ : ℕ) : ℕ := 69

def vMulD3 : GroupedEqV.VParams where
  Nf := nfMulD3
  OFFf := offMulD3
  Wf := wfMulD3
  Nmax := 0
  OFFmax := 0
  Wmax := 69

def vrMulD3 : GroupedEqV.VParams where
  Nf := nfrMulD3
  OFFf := offrMulD3
  Wf := wfMulD3
  Nmax := 0
  OFFmax := 0
  Wmax := 69

private lemma hgv_pos : ∀ k, posOfMulD3 (k + 1) = posOfMulD3 k + gfMulD3 k := by
  intro k; simp only [posOfMulD3, gfMulD3]; split_ifs <;> omega

private lemma hgv_gf : ∀ k, 0 < gfMulD3 k := by
  intro k; simp only [gfMulD3]; split_ifs <;> omega

private lemma hgv_w : ∀ k, 0 < vMulD3.Wf k ∧ 2 ^ vMulD3.Wf k < circomPrime := by
  intro k
  simp only [vMulD3, wfMulD3]
  exact ⟨by norm_num, by decide⟩

private lemma hgv_nf : ∀ j, 0 < vMulD3.Nf j ∧ 0 < vrMulD3.Nf j := by
  intro j
  simp only [vMulD3, vrMulD3, nfMulD3, nfrMulD3]
  exact ⟨by norm_num, by norm_num⟩

theorem hgvMulD3 :
    GroupedEqXV.GVXHyps circomPrime 8 64 gfMulD3 posOfMulD3 5 vMulD3 vrMulD3 := by
  refine ⟨rfl, hgv_pos, hgv_gf, hgv_w, hgv_nf, ?_, by norm_num,
    by simp only [vMulD3, vrMulD3, wfMulD3, nfMulD3, nfrMulD3, offMulD3, offrMulD3,
         gfMulD3, posOfMulD3, circomPrime,
         Challenge.Instances.Secp256k1ScalarMul.Interface.circomPrime]
       norm_num [Finset.sum_range_succ, Finset.sum_range_zero],
    by simp only [vMulD3, vrMulD3, wfMulD3, nfMulD3, nfrMulD3, offMulD3, offrMulD3,
         gfMulD3, posOfMulD3, circomPrime,
         Challenge.Instances.Secp256k1ScalarMul.Interface.circomPrime]
       norm_num [Finset.sum_range_succ, Finset.sum_range_zero],
    by simp only [vMulD3, vrMulD3, wfMulD3, nfMulD3, nfrMulD3, offMulD3, offrMulD3,
         gfMulD3, posOfMulD3, circomPrime,
         Challenge.Instances.Secp256k1ScalarMul.Interface.circomPrime]
       norm_num [Finset.sum_range_succ, Finset.sum_range_zero]⟩
  intro k hk
  have hcase : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hcase with rfl | rfl | rfl | rfl <;>
    · refine ⟨?_, ⟨?_, ?_⟩, ?_⟩ <;>
        · simp only [vMulD3, vrMulD3, wfMulD3, nfMulD3, nfrMulD3, offMulD3, offrMulD3,
            gfMulD3, posOfMulD3, circomPrime,
            Challenge.Instances.Secp256k1ScalarMul.Interface.circomPrime]
          norm_num [Finset.sum_range_succ, Finset.sum_range_zero]

/-- The LHS grouped cap is three times the `(m+1)·2^(2B)` bound. -/
theorem hNfMulD3 : ∀ j, vMulD3.Nf j = 3 * ((numLimbs + 1) * 2 ^ (2 * secpParams.B)) :=
  fun _ => rfl

/-- The RHS grouped cap keeps the `(m+1)·2^(2B)` bound. -/
theorem hNfrMulD3 : ∀ j, vrMulD3.Nf j = (numLimbs + 1) * 2 ^ (2 * secpParams.B) :=
  fun _ => rfl

end Solution.Secp256k1ScalarMul
