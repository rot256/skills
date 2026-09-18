import Solution.Secp256k1ScalarMul.Params
import Solution.Secp256k1ScalarMul.MulMod



namespace Solution.Secp256k1ScalarMul


def gfMulD (k : ℕ) : ℕ := if k ≤ 2 then 2 else 1


def posOfMulD (k : ℕ) : ℕ := if k ≤ 3 then 2 * k else k + 3


def nfMulD (_ : ℕ) : ℕ := 10 * 2 ^ 128


def nfrMulD (_ : ℕ) : ℕ := 5 * 2 ^ 128


def offMulD (k : ℕ) : ℕ :=
  if k = 0 then 184467440737095516169 else 184467440737095516170


def offrMulD (k : ℕ) : ℕ :=
  if k = 0 then 92233720368547758084 else 92233720368547758085

def wfMulD (_ : ℕ) : ℕ := 68

def vMulD : GroupedEqV.VParams where
  Nf := nfMulD
  OFFf := offMulD
  Wf := wfMulD
  Nmax := 0
  OFFmax := 0
  Wmax := 68

def vrMulD : GroupedEqV.VParams where
  Nf := nfrMulD
  OFFf := offrMulD
  Wf := wfMulD
  Nmax := 0
  OFFmax := 0
  Wmax := 68

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem hgvMulD :
    GroupedEqXV.GVXHyps circomPrime 8 64 gfMulD posOfMulD 5 vMulD vrMulD := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, by norm_num, by decide, by decide, by decide⟩
  · intro k; simp only [posOfMulD, gfMulD]; split_ifs <;> omega
  · intro k; simp only [gfMulD]; split_ifs <;> omega
  · intro k
    simp only [vMulD, wfMulD]
    exact ⟨by norm_num, by decide⟩
  · intro j
    simp only [vMulD, vrMulD, nfMulD, nfrMulD]
    exact ⟨by norm_num, by norm_num⟩
  · intro k hk
    have hcase : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hcase with rfl | rfl | rfl | rfl <;>
      exact ⟨by decide, ⟨by decide, by decide⟩, by decide⟩


theorem hNfMulD : ∀ j, vMulD.Nf j = 2 * ((numLimbs + 1) * 2 ^ (2 * secpParams.B)) :=
  fun _ => rfl


theorem hNfrMulD : ∀ j, vrMulD.Nf j = (numLimbs + 1) * 2 ^ (2 * secpParams.B) :=
  fun _ => rfl

end Solution.Secp256k1ScalarMul
