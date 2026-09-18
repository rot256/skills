import Solution.Secp256k1ScalarMul.ParamsD



namespace Solution.Secp256k1ScalarMul


def nfrW (_ : ℕ) : ℕ := 17 * 2 ^ 128


def offrW (k : ℕ) : ℕ :=
  if k = 0 then 313594649253062377488 else 313594649253062377489

def wfW (_ : ℕ) : ℕ := 69

def vW : GroupedEqV.VParams where
  Nf := nfMulD
  OFFf := offMulD
  Wf := wfW
  Nmax := 0
  OFFmax := 0
  Wmax := 69

def vrW : GroupedEqV.VParams where
  Nf := nfrW
  OFFf := offrW
  Wf := wfW
  Nmax := 0
  OFFmax := 0
  Wmax := 69

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem hgvW :
    GroupedEqXV.GVXHyps circomPrime 8 64 gfMulD posOfMulD 5 vW vrW := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, by norm_num, by decide, by decide, by decide⟩
  · intro k; simp only [posOfMulD, gfMulD]; split_ifs <;> omega
  · intro k; simp only [gfMulD]; split_ifs <;> omega
  · intro k
    simp only [vW, wfW]
    exact ⟨by norm_num, by decide⟩
  · intro j
    simp only [vW, vrW, nfMulD, nfrW]
    exact ⟨by norm_num, by norm_num⟩
  · intro k hk
    have hcase : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hcase with rfl | rfl | rfl | rfl <;>
      exact ⟨by decide, ⟨by decide, by decide⟩, by decide⟩


theorem hNfW : ∀ j, vW.Nf j = 2 * ((numLimbs + 1) * 2 ^ (2 * secpParams.B)) :=
  fun _ => rfl


theorem hNfrW : ∀ j, vrW.Nf j = (4 * numLimbs + 1) * 2 ^ (2 * secpParams.B) :=
  fun _ => rfl


def threeP2Limbs : Vector (F circomPrime) 8 :=
  Vector.ofFn fun k : Fin 8 =>
    if k.val < 7 then ((limbOfNat (3 * (P256 * P256)) k.val : ℕ) : F circomPrime)
    else ((3 * (P256 * P256) / 2 ^ (limbBits * 7) : ℕ) : F circomPrime)


lemma threeP2_head_eq : 3 * (P256 * P256) / 2 ^ (limbBits * 7) = 55340232221128654847 := by
  decide

private lemma limbOfNatW_lt (v k : ℕ) : limbOfNat v k < 2 ^ limbBits :=
  Nat.mod_lt _ (Nat.two_pow_pos limbBits)

private lemma val_limbOfNatW (v k : ℕ) :
    ((limbOfNat v k : ℕ) : F circomPrime).val = limbOfNat v k :=
  ZMod.val_natCast_of_lt (lt_trans (limbOfNatW_lt v k) (by decide))


lemma threeP2Limbs_limb_lt : ∀ j : Fin 8, ((threeP2Limbs)[j.val]).val < 4 * 2 ^ limbBits := by
  decide


lemma polyValue_threeP2Limbs : polyValue limbBits threeP2Limbs = 3 * (P256 * P256) := by
  decide

end Solution.Secp256k1ScalarMul
