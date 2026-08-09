import Solution.SHA256.Round63DM

/-!
# Spec-level facts for the deferred state words

State words 3 (`d`) and 7 (`h`) enter `sha256Round` only through `add32`, so the
compression function only depends on them modulo `2^32`.  That is what lets the
Merkle–Damgård feed-forward for those two words stay *unreduced* across blocks.
-/

namespace Solution.SHA256
namespace Deferred

open Specs.SHA256

lemma sha256Round_congr37 (s s' : Vector ℕ 8) (k w : ℕ)
    (h0 : s[0] = s'[0]) (h1 : s[1] = s'[1]) (h2 : s[2] = s'[2])
    (h4 : s[4] = s'[4]) (h5 : s[5] = s'[5]) (h6 : s[6] = s'[6])
    (h3 : s[3] % 2^32 = s'[3] % 2^32) (h7 : s[7] % 2^32 = s'[7] % 2^32) :
    sha256Round s k w = sha256Round s' k w := by
  have hadd : ∀ x y z : ℕ, x % 2^32 = y % 2^32 → add32 x z = add32 y z := by
    intro x y z hxy
    unfold add32
    omega
  have h7' : ∀ z, add32 s[7] z = add32 s'[7] z := fun z => hadd _ _ z h7
  have h3' : ∀ z, add32 s[3] z = add32 s'[3] z := fun z => hadd _ _ z h3
  simp only [sha256Round, h0, h1, h2, h4, h5, h6, h7', h3']

lemma sha256Compress_congr37 (s s' : Vector ℕ 8) (w : Vector ℕ 64)
    (h0 : s[0] = s'[0]) (h1 : s[1] = s'[1]) (h2 : s[2] = s'[2])
    (h4 : s[4] = s'[4]) (h5 : s[5] = s'[5]) (h6 : s[6] = s'[6])
    (h3 : s[3] % 2^32 = s'[3] % 2^32) (h7 : s[7] % 2^32 = s'[7] % 2^32) :
    sha256Compress s w = sha256Compress s' w := by
  rw [SHA256Rounds.sha256Compress_eq_valStateAfterRound,
    SHA256Rounds.sha256Compress_eq_valStateAfterRound]
  have key : ∀ n : ℕ, 1 ≤ n →
      SHA256Rounds.valStateAfterRound s w n = SHA256Rounds.valStateAfterRound s' w n := by
    intro n hn
    induction n with
    | zero => omega
    | succ m ih =>
      by_cases hm : m = 0
      · subst hm
        rw [SHA256Rounds.valStateAfterRound_succ s w 0 (by norm_num),
          SHA256Rounds.valStateAfterRound_succ s' w 0 (by norm_num)]
        exact sha256Round_congr37 s s' _ _ h0 h1 h2 h4 h5 h6 h3 h7
      · by_cases hlt : m < 64
        · rw [SHA256Rounds.valStateAfterRound_succ s w m hlt,
            SHA256Rounds.valStateAfterRound_succ s' w m hlt, ih (by omega)]
        · rw [SHA256Rounds.valStateAfterRound, SHA256Rounds.valStateAfterRound,
            dif_neg hlt, dif_neg hlt, ih (by omega)]
  exact key 64 (by norm_num)

lemma compressBlock_congr37 (s s' : Vector ℕ 8) (b : Vector ℕ 16)
    (h0 : s[0] = s'[0]) (h1 : s[1] = s'[1]) (h2 : s[2] = s'[2])
    (h4 : s[4] = s'[4]) (h5 : s[5] = s'[5]) (h6 : s[6] = s'[6])
    (h3 : s[3] % 2^32 = s'[3] % 2^32) (h7 : s[7] % 2^32 = s'[7] % 2^32) :
    compressBlock s b = compressBlock s' b := by
  have hc := sha256Compress_congr37 s s' (messageSchedule b) h0 h1 h2 h4 h5 h6 h3 h7
  have hadd : ∀ x y z : ℕ, x % 2^32 = y % 2^32 → add32 x z = add32 y z := by
    intro x y z hxy
    unfold add32
    omega
  apply Vector.ext
  intro i hi
  rw [SHA256Rounds.compressBlock_getElem _ _ i hi, SHA256Rounds.compressBlock_getElem _ _ i hi, hc]
  have hcases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h0]
  · rw [h1]
  · rw [h2]
  · exact hadd _ _ _ h3
  · rw [h4]
  · rw [h5]
  · rw [h6]
  · exact hadd _ _ _ h7

/-- `compressBlock` with the two deferred feed-forward additions left unreduced. -/
def compressBlockD (s : Vector ℕ 8) (b : Vector ℕ 16) : Vector ℕ 8 :=
  let c := sha256Compress s (messageSchedule b)
  Vector.mapFinRange 8 fun i =>
    if i.val = 3 ∨ i.val = 7 then s[i.val] + c[i.val] else add32 s[i.val] c[i.val]

lemma compressBlockD_getElem_ne (s : Vector ℕ 8) (b : Vector ℕ 16) (i : ℕ) (hi : i < 8)
    (h3 : i ≠ 3) (h7 : i ≠ 7) :
    (compressBlockD s b)[i] = (compressBlock s b)[i] := by
  rw [SHA256Rounds.compressBlock_getElem s b i hi]
  simp only [compressBlockD, Vector.getElem_mapFinRange, Fin.getElem_fin]
  rw [if_neg (by simp only [not_or]; exact ⟨h3, h7⟩)]

lemma compressBlockD_getElem_eq (s : Vector ℕ 8) (b : Vector ℕ 16) (i : ℕ) (hi : i < 8)
    (h : i = 3 ∨ i = 7) :
    (compressBlockD s b)[i] = s[i] + (sha256Compress s (messageSchedule b))[i] := by
  simp only [compressBlockD, Vector.getElem_mapFinRange, Fin.getElem_fin, if_pos h]

lemma compressBlockD_mod (s : Vector ℕ 8) (b : Vector ℕ 16) (i : ℕ) (hi : i < 8) :
    (compressBlockD s b)[i] % 2^32 = (compressBlock s b)[i] := by
  by_cases h : i = 3 ∨ i = 7
  · rw [compressBlockD_getElem_eq s b i hi h, SHA256Rounds.compressBlock_getElem s b i hi]
    unfold add32
    rfl
  · rw [compressBlockD_getElem_ne s b i hi (by tauto) (by tauto),
      SHA256Rounds.compressBlock_getElem s b i hi]
    unfold add32
    omega

lemma compressBlockD_lt (s : Vector ℕ 8) (b : Vector ℕ 16) (i : ℕ) (hi : i < 8)
    (hw : (sha256Compress s (messageSchedule b))[i] < 2^32) (h : i = 3 ∨ i = 7) :
    (compressBlockD s b)[i] < s[i] + 2^32 := by
  rw [compressBlockD_getElem_eq s b i hi h]
  omega

lemma add32_lt (x y : ℕ) : add32 x y < 2^32 := by
  unfold add32
  exact Nat.mod_lt _ (by norm_num)

/-- How many rounds it takes for state slot `i` to become an `add32` output. -/
def ageIdx (i : ℕ) : ℕ :=
  if i = 0 ∨ i = 4 then 1 else if i = 1 ∨ i = 5 then 2 else if i = 2 ∨ i = 6 then 3 else 4

lemma ageIdx_pos (i : ℕ) : 1 ≤ ageIdx i := by
  simp only [ageIdx]
  split
  · omega
  · split
    · omega
    · split <;> omega

lemma valStateAfterRound_lt (s : Vector ℕ 8) (w : Vector ℕ 64) :
    ∀ n : ℕ, n ≤ 64 → ∀ (i : ℕ) (hi : i < 8), ageIdx i ≤ n →
      (SHA256Rounds.valStateAfterRound s w n)[i] < 2^32 := by
  intro n
  induction n with
  | zero =>
    intro _ i _ hage
    have := ageIdx_pos i
    omega
  | succ m ih =>
    intro h64 i hi hage
    rw [SHA256Rounds.valStateAfterRound_succ s w m (by omega), Round63DM.sha256Round_eq]
    have ihm := ih (by omega)
    have hcases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
    have hage' : ageIdx i ≤ m + 1 := hage
    simp only [ageIdx] at hage'
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [Round63DM.vec8_getElem0]; exact add32_lt _ _
    · rw [Round63DM.vec8_getElem1]
      exact ihm 0 (by norm_num) (by simp only [ageIdx]; norm_num at hage' ⊢; omega)
    · rw [Round63DM.vec8_getElem2]
      exact ihm 1 (by norm_num) (by simp only [ageIdx]; norm_num at hage' ⊢; omega)
    · rw [Round63DM.vec8_getElem3]
      exact ihm 2 (by norm_num) (by simp only [ageIdx]; norm_num at hage' ⊢; omega)
    · rw [Round63DM.vec8_getElem4]; exact add32_lt _ _
    · rw [Round63DM.vec8_getElem5]
      exact ihm 4 (by norm_num) (by simp only [ageIdx]; norm_num at hage' ⊢; omega)
    · rw [Round63DM.vec8_getElem6]
      exact ihm 5 (by norm_num) (by simp only [ageIdx]; norm_num at hage' ⊢; omega)
    · rw [Round63DM.vec8_getElem7]
      exact ihm 6 (by norm_num) (by simp only [ageIdx]; norm_num at hage' ⊢; omega)

lemma sha256Compress_lt (s : Vector ℕ 8) (w : Vector ℕ 64) (i : ℕ) (hi : i < 8) :
    (sha256Compress s w)[i] < 2^32 := by
  rw [SHA256Rounds.sha256Compress_eq_valStateAfterRound]
  refine valStateAfterRound_lt s w 64 (by norm_num) i hi ?_
  simp only [ageIdx]
  split
  · omega
  · split
    · omega
    · split <;> omega

lemma compressBlockD_bound (s : Vector ℕ 8) (b : Vector ℕ 16) (B : ℕ)
    (hs : ∀ (i : ℕ) (hi : i < 8), s[i] < B) (i : ℕ) (hi : i < 8) :
    (compressBlockD s b)[i] < B + 2^32 := by
  by_cases h : i = 3 ∨ i = 7
  · rw [compressBlockD_getElem_eq s b i hi h]
    have := sha256Compress_lt s (messageSchedule b) i hi
    have := hs i hi
    omega
  · rw [compressBlockD_getElem_ne s b i hi (by tauto) (by tauto),
      SHA256Rounds.compressBlock_getElem s b i hi]
    have : add32 s[i] (sha256Compress s (messageSchedule b))[i] < 2^32 := add32_lt _ _
    omega

lemma compressBlockD_lt_two_pow (s : Vector ℕ 8) (b : Vector ℕ 16) (i : ℕ) (hi : i < 8)
    (h3 : i ≠ 3) (h7 : i ≠ 7) :
    (compressBlockD s b)[i] < 2^32 := by
  rw [compressBlockD_getElem_ne s b i hi h3 h7, SHA256Rounds.compressBlock_getElem s b i hi]
  exact add32_lt _ _

end Deferred
end Solution.SHA256
