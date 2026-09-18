import Solution.Secp256k1ScalarMul.ParamsW



namespace Solution.Secp256k1ScalarMul


def nfMul3 (_ : ℕ) : ℕ := 13 * 2 ^ 128


def offMul3 (k : ℕ) : ℕ :=
  if k = 0 then 239807672958224171020 else 239807672958224171021


def vW3 : GroupedEqV.VParams where
  Nf := nfMul3
  OFFf := offMul3
  Wf := wfW
  Nmax := 0
  OFFmax := 0
  Wmax := 69


set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem hgvW3 :
    GroupedEqXV.GVXHyps circomPrime 8 64 gfMulD posOfMulD 5 vW3 vrW := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, by norm_num, by decide, by decide, by decide⟩
  · intro k; simp only [posOfMulD, gfMulD]; split_ifs <;> omega
  · intro k; simp only [gfMulD]; split_ifs <;> omega
  · intro k
    simp only [vW3, wfW]
    exact ⟨by norm_num, by decide⟩
  · intro j
    simp only [vW3, vrW, nfMul3, nfrW]
    exact ⟨by norm_num, by norm_num⟩
  · intro k hk
    have hcase : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hcase with rfl | rfl | rfl | rfl <;>
      exact ⟨by decide, ⟨by decide, by decide⟩, by decide⟩


theorem hNfW3 : ∀ j, vW3.Nf j = (3 * numLimbs + 1) * 2 ^ (2 * secpParams.B) :=
  fun _ => rfl

end Solution.Secp256k1ScalarMul
