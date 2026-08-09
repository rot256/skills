import Solution.SHA256.DeferredSpec
import Solution.SHA256.MainTheorems

/-!
# The deferred Merkle–Damgård chain

`chainStateD` is the chain of block states as the *circuit* computes them: state words
3 and 7 are never reduced, so they only agree with the true chain modulo `2^32`.
-/

namespace Solution.SHA256

open Challenge.Instances.SHA256.Interface (inputBufferLen circomPrime)

/-- The chain of block outputs with the two feed-forward words left unreduced. -/
def chainStateD (msg : Vector ℕ inputBufferLen) (len : ℕ) : ℕ → Vector ℕ 8
  | 0 => Specs.SHA256.H0
  | k + 1 => Deferred.compressBlockD (chainStateD msg len k) (specBlock msg len k)

lemma chainStateD_lt (msg : Vector ℕ inputBufferLen) (len : ℕ) :
    ∀ (k i : ℕ) (hi : i < 8), i ≠ 3 → i ≠ 7 → (chainStateD msg len k)[i] < 2^32 := by
  intro k
  induction k with
  | zero =>
    intro i hi _ _
    have hcases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
    simp only [chainStateD]
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num [Specs.SHA256.H0]
  | succ m _ =>
    intro i hi h3 h7
    exact Deferred.compressBlockD_lt_two_pow _ _ i hi h3 h7

lemma chainStateD_bound (msg : Vector ℕ inputBufferLen) (len : ℕ) :
    ∀ (k i : ℕ) (hi : i < 8), (chainStateD msg len k)[i] < (k + 1) * 2^32 := by
  intro k
  induction k with
  | zero =>
    intro i hi
    have hcases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
    simp only [chainStateD]
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num [Specs.SHA256.H0]
  | succ m ih =>
    intro i hi
    have h := Deferred.compressBlockD_bound (chainStateD msg len m) (specBlock msg len m)
      ((m + 1) * 2^32) (fun j hj => ih j hj) i hi
    simp only [chainStateD]
    have harith : (m + 1) * 2^32 + 2^32 = (m + 1 + 1) * 2^32 := by ring
    omega

lemma chainStateD_mod (msg : Vector ℕ inputBufferLen) (len : ℕ) :
    ∀ (k i : ℕ) (hi : i < 8),
      (chainStateD msg len k)[i] % 2^32 = (chainState msg len k)[i] := by
  intro k
  induction k with
  | zero =>
    intro i hi
    have hcases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
    simp only [chainStateD, chainState]
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num [Specs.SHA256.H0]
  | succ m ih =>
    intro i hi
    have hcongr : Specs.SHA256.compressBlock (chainStateD msg len m) (specBlock msg len m)
        = Specs.SHA256.compressBlock (chainState msg len m) (specBlock msg len m) := by
      refine Deferred.compressBlock_congr37 _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · have h := ih 0 (by norm_num)
        have hlt := chainStateD_lt msg len m 0 (by norm_num) (by norm_num) (by norm_num)
        omega
      · have h := ih 1 (by norm_num)
        have hlt := chainStateD_lt msg len m 1 (by norm_num) (by norm_num) (by norm_num)
        omega
      · have h := ih 2 (by norm_num)
        have hlt := chainStateD_lt msg len m 2 (by norm_num) (by norm_num) (by norm_num)
        omega
      · have h := ih 4 (by norm_num)
        have hlt := chainStateD_lt msg len m 4 (by norm_num) (by norm_num) (by norm_num)
        omega
      · have h := ih 5 (by norm_num)
        have hlt := chainStateD_lt msg len m 5 (by norm_num) (by norm_num) (by norm_num)
        omega
      · have h := ih 6 (by norm_num)
        have hlt := chainStateD_lt msg len m 6 (by norm_num) (by norm_num) (by norm_num)
        omega
      · have h := ih 3 (by norm_num)
        have hmod : (chainState msg len m)[3] % 2^32 = (chainState msg len m)[3] := by
          have : (chainState msg len m)[3] < 2^32 := by
            match m with
            | 0 => norm_num [chainState, Specs.SHA256.H0]
            | j + 1 =>
              simp only [chainState, SHA256Rounds.compressBlock_getElem _ _ 3 (by norm_num)]
              exact Deferred.add32_lt _ _
          omega
        omega
      · have h := ih 7 (by norm_num)
        have hmod : (chainState msg len m)[7] % 2^32 = (chainState msg len m)[7] := by
          have : (chainState msg len m)[7] < 2^32 := by
            match m with
            | 0 => norm_num [chainState, Specs.SHA256.H0]
            | j + 1 =>
              simp only [chainState, SHA256Rounds.compressBlock_getElem _ _ 7 (by norm_num)]
              exact Deferred.add32_lt _ _
          omega
        omega
    simp only [chainStateD, chainState]
    rw [Deferred.compressBlockD_mod _ _ i hi, hcongr]

lemma digest_finalD
    (states : Vector (SHA256State (F circomPrime)) paddedBlocksLen)
    (msg : Vector ℕ inputBufferLen) (ℓ : ℕ) (hℓ : ℓ ≤ inputBufferLen)
    (hsv : ∀ k : Fin paddedBlocksLen,
      Vector.map valueBits states[k] = chainStateD msg ℓ (k.val + 1))
    (w : Fin 8) (hw : w.val < 8) :
    valueBits ((stateForLen states ℓ)[w.val]'hw) % 2^32 =
      (Specs.SHA256.sha256 (Specs.SHA256.truncate msg ℓ hℓ))[w.val]'hw := by
  have hpos := numBlocksForLen_pos ℓ
  have hle := numBlocksForLen_le hℓ
  simp only [paddedBlocksLen] at hle
  rw [stateForLen_eq states ℓ hℓ, sha256_eq_chainState msg ℓ hℓ]
  set nb := numBlocksForLen ℓ with hnb
  have hk : nb - 1 < paddedBlocksLen := by simp only [paddedBlocksLen]; omega
  have hst := hsv ⟨nb - 1, hk⟩
  have hkv : (⟨nb - 1, hk⟩ : Fin paddedBlocksLen).val + 1 = nb := by simp only; omega
  rw [hkv] at hst
  rw [← chainStateD_mod msg ℓ nb w.val hw, ← hst, Vector.getElem_map]
  congr 2

end Solution.SHA256
