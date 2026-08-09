import Solution.SHA256.SHA256Rounds

/-!
# Deferred chaining value for the `h` slot

The Merkle-Damgård feed-forward word `H[7]` is consumed by the next block **only
additively** (it enters round `0`'s `T1` sum and nothing else) and is otherwise only a
digest candidate.  So it never has to be presented as a bit vector: we carry it as a
single unreduced field value, packed into coordinate `0` of the usual 32-lane
presentation (`rawWord`), with all other coordinates zero.  `valueBits` of such a word is
exactly the carried value, and `fromBitsExpr` of it is exactly the carried expression, so
every consumer that reads only the packed numeric value keeps working unchanged.

This file provides

* `rawWord` and its evaluation lemmas, and
* the arithmetic fact that the SHA-256 specification only depends on the `h` slot of the
  incoming chaining state **modulo `2^32`** (`compressBlock_congr7`), which is what lets
  the deferred value stand in for the reduced one.
-/

section
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2)]

namespace Solution.SHA256

/-- Carry a value in coordinate `0` of a 32-lane presentation, all other lanes zero. -/
def rawWord (e : Expression (F p)) : Var (fields 32) (F p) :=
  Vector.ofFn fun i : Fin 32 => if i.val = 0 then e else 0

@[simp] lemma rawWord_getElem_zero (e : Expression (F p)) :
    (rawWord e)[0]'(by norm_num) = e := by
  rw [rawWord, Vector.getElem_ofFn]
  simp

lemma rawWord_getElem_succ (e : Expression (F p)) (i : ℕ) (hi : i < 32) (h0 : i ≠ 0) :
    (rawWord e)[i]'hi = 0 := by
  rw [rawWord, Vector.getElem_ofFn]
  simp [h0]

/-- The packed value of a `rawWord` is the value of its single lane. -/
lemma valueBits_rawWord (env : Environment (F p)) (e : Expression (F p)) :
    valueBits (Vector.map (Expression.eval env) (rawWord e))
      = (Expression.eval env e).val := by
  unfold valueBits
  rw [Finset.sum_eq_single (⟨0, by norm_num⟩ : Fin 32)]
  · simp only [Fin.getElem_fin, Vector.getElem_map, Fin.val_mk, pow_zero, mul_one]
    rw [rawWord_getElem_zero]
  · intro i _ hi
    have hi0 : i.val ≠ 0 := fun h => hi (Fin.ext h)
    simp only [Fin.getElem_fin, Vector.getElem_map]
    rw [rawWord_getElem_succ e i.val i.isLt hi0]
    simp [Expression.eval]
  · intro h; exact absurd (Finset.mem_univ _) h

end Solution.SHA256
end

namespace Solution.SHA256
namespace DeferredH

open Specs.SHA256

lemma add32_congr_left {x y : ℕ} (z : ℕ) (h : x % 2^32 = y % 2^32) :
    _root_.add32 x z = _root_.add32 y z := by
  unfold _root_.add32
  omega

/-- One SHA-256 round only depends on the `h` slot modulo `2^32`. -/
lemma sha256Round_congr7 (sv sv' : Vector ℕ 8) (k w : ℕ)
    (h : ∀ (i : ℕ) (hi : i < 8), i ≠ 7 → sv[i] = sv'[i])
    (h7 : sv[7] % 2^32 = sv'[7] % 2^32) :
    sha256Round sv k w = sha256Round sv' k w := by
  have e0 := h 0 (by norm_num) (by norm_num)
  have e1 := h 1 (by norm_num) (by norm_num)
  have e2 := h 2 (by norm_num) (by norm_num)
  have e3 := h 3 (by norm_num) (by norm_num)
  have e4 := h 4 (by norm_num) (by norm_num)
  have e5 := h 5 (by norm_num) (by norm_num)
  have e6 := h 6 (by norm_num) (by norm_num)
  rw [SHA256Rounds.sha256Round_literal, SHA256Rounds.sha256Round_literal,
    e0, e1, e2, e3, e4, e5, e6,
    add32_congr_left (upperSigma1 sv'[4]) h7]

lemma valStateAfterRound_congr7 (sv sv' : Vector ℕ 8) (sch : Vector ℕ 64)
    (h : ∀ (i : ℕ) (hi : i < 8), i ≠ 7 → sv[i] = sv'[i])
    (h7 : sv[7] % 2^32 = sv'[7] % 2^32) :
    ∀ (n : ℕ), 0 < n →
      SHA256Rounds.valStateAfterRound sv sch n = SHA256Rounds.valStateAfterRound sv' sch n := by
  intro n
  induction n with
  | zero => intro hn; exact absurd hn (lt_irrefl 0)
  | succ m ih =>
    intro _
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp only [SHA256Rounds.valStateAfterRound, dif_pos (show (0:ℕ) < 64 by norm_num)]
      exact sha256Round_congr7 sv sv' _ _ h h7
    · simp only [SHA256Rounds.valStateAfterRound]
      by_cases hm64 : m < 64
      · rw [dif_pos hm64, dif_pos hm64, ih hm]
      · rw [dif_neg hm64, dif_neg hm64, ih hm]

/-- The whole block compression only depends on the `h` slot modulo `2^32`. -/
lemma compressBlock_congr7 (sv sv' : Vector ℕ 8) (blk : Vector ℕ 16)
    (h : ∀ (i : ℕ) (hi : i < 8), i ≠ 7 → sv[i] = sv'[i])
    (h7 : sv[7] % 2^32 = sv'[7] % 2^32) :
    compressBlock sv blk = compressBlock sv' blk := by
  have hcomp : sha256Compress sv (messageSchedule blk) = sha256Compress sv' (messageSchedule blk) := by
    rw [SHA256Rounds.sha256Compress_eq_valStateAfterRound,
      SHA256Rounds.sha256Compress_eq_valStateAfterRound]
    exact valStateAfterRound_congr7 sv sv' _ h h7 64 (by norm_num)
  simp only [compressBlock, hcomp]
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_mapFinRange]
  simp only [Fin.getElem_fin, Fin.val_mk]
  by_cases hi7 : i = 7
  · subst hi7
    exact add32_congr_left _ h7
  · rw [h i hi hi7]

section
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2)]


/-- Replace the deferred `h` slot (index 7) of a chaining state. -/
def withH7 {F : Type} (st : SHA256State F) (w : fields 32 F) : SHA256State F :=
  #v[st[0], st[1], st[2], st[3], st[4], st[5], st[6], w]

@[simp] lemma withH7_getElem7 {F : Type} (st : SHA256State F) (w : fields 32 F) :
    (withH7 st w)[7]'(by norm_num) = w := rfl

lemma withH7_getElem_ne7 {F : Type} (st : SHA256State F) (w : fields 32 F)
    (i : ℕ) (hi : i < 8) (h : i ≠ 7) : (withH7 st w)[i]'hi = st[i]'hi := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

lemma eval_withH7 (env : Environment (F p)) (st : SHA256State (Expression (F p)))
    (w : Var (fields 32) (F p)) :
    eval env (withH7 st w) = withH7 (eval env st) (eval env w) := by
  apply Vector.ext
  intro i hi
  rw [← getElem_eval_vector]
  by_cases h7 : i = 7
  · subst h7
    rw [withH7_getElem7, withH7_getElem7, CircuitType.eval_var_fields]
  · rw [withH7_getElem_ne7 _ _ i hi h7, withH7_getElem_ne7 _ _ i hi h7,
      getElem_eval_vector]

/-- The chaining-state values as the SHA-256 specification sees them: the deferred `h`
slot is read modulo `2^32`, every other slot is already reduced. -/
def stateValsD (st : SHA256State (F p)) : Vector ℕ 8 :=
  (st.map valueBits).set 7 (valueBits (st[7]'(by norm_num)) % 2^32)

lemma stateValsD_getElem_ne7 (st : SHA256State (F p)) (i : ℕ) (hi : i < 8) (h : i ≠ 7) :
    (stateValsD st)[i]'hi = valueBits (st[i]'hi) := by
  simp only [stateValsD]
  rw [Vector.getElem_set_ne _ _ (by omega), Vector.getElem_map]

lemma stateValsD_getElem7 (st : SHA256State (F p)) :
    (stateValsD st)[7]'(by norm_num) = valueBits (st[7]'(by norm_num)) % 2^32 := by
  simp only [stateValsD]
  rw [Vector.getElem_set_self]

/-- If the `h` slot happens to be reduced, `stateValsD` is the plain value vector. -/
lemma stateValsD_eq_map (st : SHA256State (F p)) (h : valueBits (st[7]'(by norm_num)) < 2^32) :
    stateValsD st = st.map valueBits := by
  simp only [stateValsD]
  rw [Nat.mod_eq_of_lt h]
  apply Vector.ext
  intro i hi
  by_cases h7 : i = 7
  · subst h7; rw [Vector.getElem_set_self, Vector.getElem_map]
  · rw [Vector.getElem_set_ne _ _ (by omega)]

/-- The specification only looks at the deferred slot modulo `2^32`, so it does not care
whether it was reduced. -/
lemma compressBlock_stateValsD (st : SHA256State (F p)) (blk : Vector ℕ 16) :
    Specs.SHA256.compressBlock (stateValsD st) blk
      = Specs.SHA256.compressBlock (st.map valueBits) blk := by
  apply compressBlock_congr7
  · intro i hi h7
    rw [stateValsD_getElem_ne7 st i hi h7, Vector.getElem_map]
  · rw [stateValsD_getElem7, Vector.getElem_map, Nat.mod_mod_of_dvd _ dvd_rfl]

/-- Packed value of a two-summand deferred word (expression form). -/
lemma valueBits_rawWord_addE (env : Environment (F p)) (a b : Expression (F p))
    (x y : ℕ)
    (ha : Expression.eval env a = ((x : ℕ) : F p))
    (hb : Expression.eval env b = ((y : ℕ) : F p))
    (hlt : x + y < p) :
    valueBits (Vector.map (Expression.eval env) (rawWord (a + b))) = x + y := by
  rw [valueBits_rawWord]
  rw [show Expression.eval env (a + b)
      = Expression.eval env a + Expression.eval env b from rfl, ha, hb]
  rw [show ((x : ℕ) : F p) + ((y : ℕ) : F p) = ((x + y : ℕ) : F p) from by push_cast; ring]
  exact ZMod.val_natCast_of_lt hlt

/-- Packed value of a two-summand deferred word. -/
lemma valueBits_rawWord_add (env : Environment (F p)) (X Y : Var (fields 32) (F p))
    (x y : ℕ)
    (hX : Expression.eval env (fromBitsExpr X) = ((x : ℕ) : F p))
    (hY : Expression.eval env (fromBitsExpr Y) = ((y : ℕ) : F p))
    (hlt : x + y < p) :
    valueBits (Vector.map (Expression.eval env)
        (rawWord (fromBitsExpr X + fromBitsExpr Y))) = x + y := by
  rw [valueBits_rawWord]
  rw [show Expression.eval env (fromBitsExpr X + fromBitsExpr Y)
      = Expression.eval env (fromBitsExpr X) + Expression.eval env (fromBitsExpr Y) from rfl,
    hX, hY]
  rw [show ((x : ℕ) : F p) + ((y : ℕ) : F p) = ((x + y : ℕ) : F p) from by push_cast; ring]
  exact ZMod.val_natCast_of_lt hlt

lemma stateValsD_withH7 (st : SHA256State (F p)) (w : fields 32 (F p))
    (h : valueBits w = valueBits (st[7]'(by norm_num)) % 2^32) :
    stateValsD (withH7 st w) = stateValsD st := by
  apply Vector.ext
  intro i hi
  by_cases h7 : i = 7
  · subst h7
    rw [stateValsD_getElem7, stateValsD_getElem7, withH7_getElem7, h,
      Nat.mod_mod_of_dvd _ dvd_rfl]
  · rw [stateValsD_getElem_ne7 _ i hi h7, stateValsD_getElem_ne7 _ i hi h7,
      withH7_getElem_ne7 _ _ i hi h7]

/-- Packed value of a deferred word built from a bounded value plus a normalized word. -/
lemma valueBits_rawWord_add_norm (env : Environment (F p)) (X Y : Var (fields 32) (F p))
    (bX : ℕ)
    (hX : valueBits (Vector.map (Expression.eval env) X) < bX)
    (hY : Normalized (Vector.map (Expression.eval env) Y))
    (hb : bX + 2^32 ≤ p) :
    valueBits (Vector.map (Expression.eval env)
        (rawWord (fromBitsExpr X + fromBitsExpr Y)))
      = valueBits (Vector.map (Expression.eval env) X)
        + valueBits (Vector.map (Expression.eval env) Y) := by
  have hy := valueBits_lt_two_pow _ hY
  exact valueBits_rawWord_add env X Y _ _
    (Add32.fromBitsExpr_eval_normalized env X _ rfl)
    (Add32.fromBitsExpr_eval_normalized env Y _ rfl)
    (by omega)

lemma valueBits_rawWord_add_lt (env : Environment (F p)) (X Y : Var (fields 32) (F p))
    (bX : ℕ)
    (hX : valueBits (Vector.map (Expression.eval env) X) < bX)
    (hY : Normalized (Vector.map (Expression.eval env) Y))
    (hb : bX + 2^32 ≤ p) :
    valueBits (Vector.map (Expression.eval env)
        (rawWord (fromBitsExpr X + fromBitsExpr Y)))
      < valueBits (Vector.map (Expression.eval env) X) + 2^32 := by
  have hy := valueBits_lt_two_pow _ hY
  rw [valueBits_rawWord_add_norm env X Y bX hX hY hb]
  omega

end

end DeferredH
end Solution.SHA256
