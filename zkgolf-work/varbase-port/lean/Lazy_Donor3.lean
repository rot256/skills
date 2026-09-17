import Solution.Secp256k1ScalarMul.Lazy_Donor2


-- Adapted donor module: FoldWide
section DonorFile3_0

/-!
# Folded (pseudo-Mersenne) quotient layout for the *wide* slope identity

Same idea as `FoldQuot`, but for the two-convolution "wide" site
`lam2 * dtil2 + lam1 * xd + 2^34 * p = q * p + yT2 + yA + c976 * lam1`.

Folding positions `4,5,6` of the *summed* convolution onto `0,1,2` with the
constant `cF = 2 ^ 256 - P256` is again a free affine recombination.  It
shrinks the modular quotient to a single wire below `2 ^ 70` and puts both
sides of the identity on `L = 4` positions.
-/

namespace Solution.Secp256k1ScalarMulFixedBase
namespace FoldWide

open Challenge.CostR1CS
open FoldQuot (cF p_add_cF)
open CompactAdd (cExp qpCoeff c976)
open Solution.Secp256k1ScalarMulFixedBase.Limbs

/-- Wide constant limbs on 4 positions: position 3 absorbs everything at or
above `2 ^ 192`. -/
def offLimbW (v k : ℕ) : ℕ := if k = 3 then v / 2 ^ 192 else limbOfNat v k

def wExpW (v k : ℕ) : Expression (F circomPrime) := ((offLimbW v k : ℕ) : F circomPrime)

/-- Summed convolution coefficient at position `k`, as a natural number. -/
def sumPQ (env : Environment (F circomPrime))
    (P Q : Vector (Expression (F circomPrime)) 7) (k : ℕ) : ℕ :=
  if h : k < 7 then (Expression.eval env (P[k]'h + Q[k]'h)).val else 0

def convLow2 (env : Environment (F circomPrime))
    (P Q : Vector (Expression (F circomPrime)) 7) : ℕ :=
  ∑ t ∈ Finset.range 4, sumPQ env P Q t * 2 ^ (64 * t)

def convHigh2 (env : Environment (F circomPrime))
    (P Q : Vector (Expression (F circomPrime)) 7) : ℕ :=
  ∑ t ∈ Finset.range 3, sumPQ env P Q (t + 4) * 2 ^ (64 * t)

/-- Folded left-hand side of the wide identity. -/
def foldLhs2 (P Q : Vector (Expression (F circomPrime)) 7) (v k : ℕ) :
    Expression (F circomPrime) :=
  (if h : k < 4 then P[k]'(by omega) + Q[k]'(by omega) else 0)
    + (if h : k < 3 then ((cF : ℕ) : F circomPrime) * (P[k + 4]'(by omega) + Q[k + 4]'(by omega))
       else 0)
    + wExpW v k

/-- Folded right-hand side of the wide identity. -/
def foldRhsY (q : Expression (F circomPrime)) (a b lam : Var Emu (F circomPrime)) (k : ℕ) :
    Expression (F circomPrime) :=
  q * cExp P256 k
    + (if h : k < 4 then a[k]'h + b[k]'h + ((c976 : ℕ) : F circomPrime) * (lam[k]'h) else 0)

/-- The unfolded (padded, 10-position) left-hand side used by the current
`PairAdd` certificates. -/
def wideLhs (P Q : Vector (Expression (F circomPrime)) 7) (v : ℕ) (k : ℕ) :
    Expression (F circomPrime) :=
  (if h : k < 7 then P[k]'h + Q[k]'h else 0) + (if k < 5 then cExp v k else 0)

/-! ### Affineness -/

theorem affine_foldLhs2 {P Q : Vector (Expression (F circomPrime)) 7}
    (hP : ∀ (j : ℕ) (hj : j < 7), Affine (P[j]'hj))
    (hQ : ∀ (j : ℕ) (hj : j < 7), Affine (Q[j]'hj)) (v k : ℕ) :
    Affine (foldLhs2 P Q v k) := by
  unfold foldLhs2 wExpW
  refine Affine.add (Affine.add ?_ ?_) (Affine.const _)
  · split
    · exact Affine.add (hP _ (by omega)) (hQ _ (by omega))
    · exact Affine.zero
  · split
    · exact Affine.fconst_mul _ (Affine.add (hP _ (by omega)) (hQ _ (by omega)))
    · exact Affine.zero

theorem affine_foldRhsY {q : Expression (F circomPrime)} {a b lam : Var Emu (F circomPrime)}
    (hq : Affine q) (ha : AffineW a) (hb : AffineW b) (hlam : AffineW lam) (k : ℕ) :
    Affine (foldRhsY q a b lam k) := by
  unfold foldRhsY
  refine Affine.add (Affine.mul_deg0 hq (CompactAdd.degree_cExp _ _)) ?_
  split
  · exact Affine.add (Affine.add (ha _ (by assumption)) (hb _ (by assumption)))
      (Affine.fconst_mul _ (hlam _ (by assumption)))
  · exact Affine.zero

/-! ### Environment stability -/

lemma foldLhs2_eval_stable {e e' : Environment (F circomPrime)}
    {P Q : Vector (Expression (F circomPrime)) 7}
    (hP : ∀ (j : ℕ) (hj : j < 7), Expression.eval e (P[j]'hj) = Expression.eval e' (P[j]'hj))
    (hQ : ∀ (j : ℕ) (hj : j < 7), Expression.eval e (Q[j]'hj) = Expression.eval e' (Q[j]'hj))
    (v k : ℕ) :
    Expression.eval e (foldLhs2 P Q v k) = Expression.eval e' (foldLhs2 P Q v k) := by
  unfold foldLhs2 wExpW
  by_cases h4 : k < 4 <;> by_cases h3 : k < 3
  · simp only [dif_pos h4, dif_pos h3, Expression.eval,
      hP k (by omega), hQ k (by omega), hP (k + 4) (by omega), hQ (k + 4) (by omega)]
  · simp only [dif_pos h4, dif_neg h3, Expression.eval, hP k (by omega), hQ k (by omega)]
  · omega
  · simp only [dif_neg h4, dif_neg h3, Expression.eval]

lemma foldRhsY_eval_stable {e e' : Environment (F circomPrime)}
    {q : Expression (F circomPrime)} {a b lam : Var Emu (F circomPrime)}
    (hq : Expression.eval e q = Expression.eval e' q)
    (ha : ∀ (j : ℕ) (hj : j < 4), Expression.eval e (a[j]'hj) = Expression.eval e' (a[j]'hj))
    (hb : ∀ (j : ℕ) (hj : j < 4), Expression.eval e (b[j]'hj) = Expression.eval e' (b[j]'hj))
    (hlam : ∀ (j : ℕ) (hj : j < 4),
      Expression.eval e (lam[j]'hj) = Expression.eval e' (lam[j]'hj))
    (k : ℕ) :
    Expression.eval e (foldRhsY q a b lam k) = Expression.eval e' (foldRhsY q a b lam k) := by
  unfold foldRhsY
  by_cases hk : k < 4
  · simp only [dif_pos hk, cExp, Expression.eval, hq, ha k hk, hb k hk, hlam k hk]
  · simp only [dif_neg hk, cExp, Expression.eval, hq]

/-! ### Constant-offset bookkeeping -/

lemma offLimbW_sum (v : ℕ) :
    ∑ k ∈ Finset.range 4, offLimbW v k * 2 ^ (64 * k) = v := by
  have hdec := limb_decomp_mod 64 3 v
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, offLimbW, limbOfNat, limbBits]
  norm_num
  norm_num [Finset.sum_range_succ] at hdec
  omega

lemma offLimbW_lt (v : ℕ) (hv : v < 2 ^ 291) (k : ℕ) : offLimbW v k < 2 ^ 99 := by
  unfold offLimbW
  split
  · have : v / 2 ^ 192 < 2 ^ 99 := by
      refine Nat.div_lt_of_lt_mul ?_
      have : (2 : ℕ) ^ 99 * 2 ^ 192 = 2 ^ 291 := by rw [← pow_add]
      omega
    omega
  · have := limbOfNat_lt v k
    simp only [limbBits] at this
    have h : (2 : ℕ) ^ 64 < 2 ^ 99 := by norm_num
    omega

/-! ### Coefficient values and bounds -/

lemma sumPQ_lt (env : Environment (F circomPrime))
    (P Q : Vector (Expression (F circomPrime)) 7)
    (hPQ : ∀ k : Fin 7, (Expression.eval env (P[k.val] + Q[k.val])).val < 20 * 2 ^ 128)
    (k : ℕ) : sumPQ env P Q k < 20 * 2 ^ 128 := by
  unfold sumPQ
  split
  · rename_i h
    exact hPQ ⟨k, h⟩
  · positivity

lemma eval_foldLhs2_cast (env : Environment (F circomPrime))
    (P Q : Vector (Expression (F circomPrime)) 7) (v : ℕ) (k : ℕ) (hk : k < 4) :
    Expression.eval env (foldLhs2 P Q v k)
      = (((sumPQ env P Q k
          + (if k < 3 then cF * sumPQ env P Q (k + 4) else 0)
          + offLimbW v k : ℕ)) : F circomPrime) := by
  unfold foldLhs2 wExpW sumPQ
  rw [dif_pos hk, dif_pos (show k < 7 by omega)]
  by_cases h3 : k < 3
  · rw [dif_pos h3, if_pos h3, dif_pos (show k + 4 < 7 by omega)]
    simp only [Expression.eval]
    push_cast
    rw [ZMod.natCast_val, ZMod.natCast_val, ZMod.cast_id, ZMod.cast_id]
  · rw [dif_neg h3, if_neg h3]
    simp only [Expression.eval]
    push_cast
    rw [ZMod.natCast_val, ZMod.cast_id]

lemma val_foldLhs2 (env : Environment (F circomPrime))
    (P Q : Vector (Expression (F circomPrime)) 7) (v : ℕ) (hv : v < 2 ^ 291)
    (hPQ : ∀ k : Fin 7, (Expression.eval env (P[k.val] + Q[k.val])).val < 20 * 2 ^ 128)
    (k : ℕ) (hk : k < 4) :
    (Expression.eval env (foldLhs2 P Q v k)).val
      = sumPQ env P Q k + (if k < 3 then cF * sumPQ env P Q (k + 4) else 0) + offLimbW v k := by
  have hA := sumPQ_lt env P Q hPQ k
  have hB := sumPQ_lt env P Q hPQ (k + 4)
  have hoff := offLimbW_lt v hv k
  have hcF : cF = 2 ^ 32 + 977 := rfl
  have hmul : cF * sumPQ env P Q (k + 4) ≤ (2 ^ 32 + 977) * (20 * 2 ^ 128) := by
    rw [hcF]; exact Nat.mul_le_mul_left _ (by omega)
  have hprime : (20 : ℕ) * 2 ^ 128 + (2 ^ 32 + 977) * (20 * 2 ^ 128) + 2 ^ 99 < circomPrime := by
    decide
  have hbound : sumPQ env P Q k + (if k < 3 then cF * sumPQ env P Q (k + 4) else 0)
      + offLimbW v k < circomPrime := by
    split_ifs <;> omega
  rw [eval_foldLhs2_cast env P Q v k hk, ZMod.val_natCast_of_lt hbound]

/-- Number of nonzero products contributing to a length-4 convolution at
position `k`: the tent profile `1,2,3,4,3,2,1`. -/
def convTerms (k : ℕ) : ℕ := if k < 4 then k + 1 else 7 - k

/-- Position-aware bound on a convolution coefficient: position `k` sums only
`convTerms k` products, not all four.  This is what makes the folded positions
`1` and `2` (which absorb positions `5` and `6`) strictly cheaper than the
uniform bound suggests. -/
lemma conv_coeff_pos_lt (env : Environment (F circomPrime))
    (a b : Var Emu (F circomPrime)) (B A Bd : ℕ) (k : Fin 7)
    (ha2 : ∀ i : Fin 4, (Expression.eval env a[i.val]).val < 2 ^ B)
    (hb2 : ∀ i : Fin 4, (Expression.eval env b[i.val]).val < 2 ^ B)
    (hfield : (4 : ℕ) * (2 ^ B * 2 ^ B) < circomPrime)
    (ha : ∀ i : Fin 4, (Expression.eval env a[i.val]).val < A)
    (hb : ∀ i : Fin 4, (Expression.eval env b[i.val]).val < Bd) :
    (Expression.eval env ((bigIntMulNoReduce a b)[k.val])).val
      < convTerms k.val * (A * Bd) := by
  have hA : 0 < A := lt_of_le_of_lt (Nat.zero_le _) (ha 0)
  have hB : 0 < Bd := lt_of_le_of_lt (Nat.zero_le _) (hb 0)
  have hAB : 0 < A * Bd := Nat.mul_pos hA hB
  rw [val_bigIntMulNoReduce_coeff env a b k ha2 hb2 hfield]
  simp only [numLimbs]
  have hterm : ∀ i : Fin 4, (if h : i.val ≤ k.val ∧ k.val - i.val < 4 then
      (Expression.eval env a[i.val]).val
        * (Expression.eval env (b[k.val - i.val]'h.2)).val else 0)
      ≤ (if i.val ≤ k.val ∧ k.val - i.val < 4 then A * Bd - 1 else 0) := by
    intro i
    by_cases h : i.val ≤ k.val ∧ k.val - i.val < 4
    · rw [dif_pos h, if_pos h]
      have h2 : (Expression.eval env (b[k.val - i.val]'h.2)).val < Bd :=
        hb ⟨k.val - i.val, h.2⟩
      have := Nat.mul_lt_mul'' (ha i) h2
      omega
    · rw [dif_neg h, if_neg h]
  have hsum : (∑ i : Fin 4, if h : i.val ≤ k.val ∧ k.val - i.val < 4 then
      (Expression.eval env a[i.val]).val
        * (Expression.eval env (b[k.val - i.val]'h.2)).val else 0)
      ≤ ∑ i : Fin 4, (if i.val ≤ k.val ∧ k.val - i.val < 4 then A * Bd - 1 else 0) :=
    Finset.sum_le_sum (fun i _ => hterm i)
  have hcount : (∑ i : Fin 4, (if i.val ≤ k.val ∧ k.val - i.val < 4 then A * Bd - 1 else 0))
      = convTerms k.val * (A * Bd - 1) := by
    fin_cases k <;> simp [Fin.sum_univ_four, convTerms] <;> ring
  have hpos : 0 < convTerms k.val := by fin_cases k <;> simp [convTerms]
  have hlt : convTerms k.val * (A * Bd - 1) < convTerms k.val * (A * Bd) :=
    Nat.mul_lt_mul_of_pos_left (by omega) hpos
  omega

lemma sumPQ_pos_lt (env : Environment (F circomPrime))
    (P Q : Vector (Expression (F circomPrime)) 7) (C : ℕ)
    (hPQ : ∀ k : Fin 7,
      (Expression.eval env (P[k.val] + Q[k.val])).val < convTerms k.val * C)
    (k : Fin 7) : sumPQ env P Q k.val < convTerms k.val * C := by
  unfold sumPQ
  rw [dif_pos k.isLt]
  exact hPQ k

/-- The position-aware hypothesis implies the uniform one (`convTerms ≤ 4`). -/
lemma convTerms_uniform (env : Environment (F circomPrime))
    (P Q : Vector (Expression (F circomPrime)) 7) (C : ℕ)
    (hPQ : ∀ k : Fin 7,
      (Expression.eval env (P[k.val] + Q[k.val])).val < convTerms k.val * C)
    (k : Fin 7) : (Expression.eval env (P[k.val] + Q[k.val])).val < 4 * C := by
  have hc : convTerms k.val ≤ 4 := by
    have := k.isLt; simp only [convTerms]; split_ifs <;> omega
  exact lt_of_lt_of_le (hPQ k) (Nat.mul_le_mul_right _ hc)

lemma foldLhs2_lt (env : Environment (F circomPrime))
    (P Q : Vector (Expression (F circomPrime)) 7) (v : ℕ) (hv : v < 2 ^ 291)
    (hPQ : ∀ k : Fin 7,
      (Expression.eval env (P[k.val] + Q[k.val])).val < convTerms k.val * (5 * 2 ^ 128))
    (k : Fin 4) :
    (Expression.eval env (foldLhs2 P Q v k.val)).val < vFoldWL.Nf k.val := by
  have hU : ∀ j : Fin 7, (Expression.eval env (P[j.val] + Q[j.val])).val < 20 * 2 ^ 128 := by
    intro j
    have := convTerms_uniform env P Q (5 * 2 ^ 128) hPQ j
    omega
  have hval := val_foldLhs2 env P Q v hv hU k.val k.isLt
  have hoff := offLimbW_lt v hv k.val
  have hcF : cF = 2 ^ 32 + 977 := rfl
  rw [hval]
  have hk4 : k.val = 0 ∨ k.val = 1 ∨ k.val = 2 ∨ k.val = 3 := by have := k.isLt; omega
  rcases hk4 with h | h | h | h
  · have hA := sumPQ_pos_lt env P Q _ hPQ ⟨0, by norm_num⟩
    have hB := sumPQ_pos_lt env P Q _ hPQ ⟨4, by norm_num⟩
    norm_num [convTerms] at hA hB
    rw [h, if_pos (by norm_num : (0:ℕ) < 3), show vFoldWL.Nf 0 = 2 ^ 164 from rfl,
      show (0:ℕ) + 4 = 4 from rfl]
    rw [h] at hoff
    have hmul : cF * sumPQ env P Q 4 ≤ (2 ^ 32 + 977) * (15 * 2 ^ 128) := by
      rw [hcF]; exact Nat.mul_le_mul_left _ (by omega)
    have hnum : (5 : ℕ) * 2 ^ 128 + (2 ^ 32 + 977) * (15 * 2 ^ 128) + 2 ^ 99 < 2 ^ 164 := by
      decide
    omega
  · have hA := sumPQ_pos_lt env P Q _ hPQ ⟨1, by norm_num⟩
    have hB := sumPQ_pos_lt env P Q _ hPQ ⟨5, by norm_num⟩
    norm_num [convTerms] at hA hB
    rw [h, if_pos (by norm_num : (1:ℕ) < 3), show vFoldWL.Nf 1 = 2 ^ 163 + 2 ^ 162 from rfl,
      show (1:ℕ) + 4 = 5 from rfl]
    rw [h] at hoff
    have hmul : cF * sumPQ env P Q 5 ≤ (2 ^ 32 + 977) * (10 * 2 ^ 128) := by
      rw [hcF]; exact Nat.mul_le_mul_left _ (by omega)
    have hnum : (10 : ℕ) * 2 ^ 128 + (2 ^ 32 + 977) * (10 * 2 ^ 128) + 2 ^ 99
        < 2 ^ 163 + 2 ^ 162 := by decide
    omega
  · have hA := sumPQ_pos_lt env P Q _ hPQ ⟨2, by norm_num⟩
    have hB := sumPQ_pos_lt env P Q _ hPQ ⟨6, by norm_num⟩
    norm_num [convTerms] at hA hB
    rw [h, if_pos (by norm_num : (2:ℕ) < 3), show vFoldWL.Nf 2 = 2 ^ 163 from rfl,
      show (2:ℕ) + 4 = 6 from rfl]
    rw [h] at hoff
    have hmul : cF * sumPQ env P Q 6 ≤ (2 ^ 32 + 977) * (5 * 2 ^ 128) := by
      rw [hcF]; exact Nat.mul_le_mul_left _ (by omega)
    have hnum : (15 : ℕ) * 2 ^ 128 + (2 ^ 32 + 977) * (5 * 2 ^ 128) + 2 ^ 99 < 2 ^ 163 := by
      decide
    omega
  · have hA := sumPQ_pos_lt env P Q _ hPQ ⟨3, by norm_num⟩
    norm_num [convTerms] at hA
    rw [h, if_neg (by norm_num), show vFoldWL.Nf 3 = 2 ^ 134 from rfl]
    rw [h] at hoff
    have hnum : (20 : ℕ) * 2 ^ 128 + 2 ^ 99 < 2 ^ 134 := by decide
    omega

lemma eval_foldRhsY_cast (env : Environment (F circomPrime)) (q : Expression (F circomPrime))
    (a b lam : Var Emu (F circomPrime)) (k : ℕ) (hk : k < 4) :
    Expression.eval env (foldRhsY q a b lam k)
      = ((((Expression.eval env q).val * limbOfNat P256 k
          + (Expression.eval env (a[k]'hk)).val + (Expression.eval env (b[k]'hk)).val
          + c976 * (Expression.eval env (lam[k]'hk)).val : ℕ)) : F circomPrime) := by
  unfold foldRhsY
  rw [dif_pos hk]
  simp only [Expression.eval, CompactAdd.cExp]
  push_cast
  rw [ZMod.natCast_val, ZMod.natCast_val, ZMod.natCast_val, ZMod.natCast_val,
    ZMod.cast_id, ZMod.cast_id, ZMod.cast_id, ZMod.cast_id]
  ring

lemma val_foldRhsY (env : Environment (F circomPrime)) (q : Expression (F circomPrime))
    (a b lam : Var Emu (F circomPrime))
    (hq : (Expression.eval env q).val < 2 ^ 70)
    (ha : BigInt.Normalized 64 (Vector.map (Expression.eval env) a))
    (hb : BigInt.Normalized 64 (Vector.map (Expression.eval env) b))
    (hlam : BigInt.Normalized 64 (Vector.map (Expression.eval env) lam))
    (k : ℕ) (hk : k < 4) :
    (Expression.eval env (foldRhsY q a b lam k)).val
      = (Expression.eval env q).val * limbOfNat P256 k
        + (Expression.eval env (a[k]'hk)).val + (Expression.eval env (b[k]'hk)).val
        + c976 * (Expression.eval env (lam[k]'hk)).val := by
  have hav := PairAdd.digit_lt_of_norm' env a ha k hk
  have hbv := PairAdd.digit_lt_of_norm' env b hb k hk
  have hlv := PairAdd.digit_lt_of_norm' env lam hlam k hk
  have hlimb : limbOfNat P256 k < 2 ^ 64 := by
    have := limbOfNat_lt P256 k; simpa [limbBits] using this
  have hmul : (Expression.eval env q).val * limbOfNat P256 k ≤ 2 ^ 70 * 2 ^ 64 :=
    Nat.mul_le_mul (by omega) (by omega)
  have hmul2 : c976 * (Expression.eval env (lam[k]'hk)).val ≤ (2 ^ 32 + 976) * 2 ^ 64 :=
    Nat.mul_le_mul_left _ (by omega)
  have hbig : (2 : ℕ) ^ 70 * 2 ^ 64 + 2 ^ 64 + 2 ^ 64 + (2 ^ 32 + 976) * 2 ^ 64 < circomPrime := by
    decide
  rw [eval_foldRhsY_cast env q a b lam k hk, ZMod.val_natCast_of_lt (by omega)]

lemma foldRhsY_lt (env : Environment (F circomPrime)) (q : Expression (F circomPrime))
    (a b lam : Var Emu (F circomPrime))
    (hq : (Expression.eval env q).val < 2 ^ 70)
    (ha : BigInt.Normalized 64 (Vector.map (Expression.eval env) a))
    (hb : BigInt.Normalized 64 (Vector.map (Expression.eval env) b))
    (hlam : BigInt.Normalized 64 (Vector.map (Expression.eval env) lam))
    (k : Fin 4) :
    (Expression.eval env (foldRhsY q a b lam k.val)).val < vFoldWR.Nf k.val := by
  have hav := PairAdd.digit_lt_of_norm' env a ha k.val k.isLt
  have hbv := PairAdd.digit_lt_of_norm' env b hb k.val k.isLt
  have hlv := PairAdd.digit_lt_of_norm' env lam hlam k.val k.isLt
  have hlimb : limbOfNat P256 k.val < 2 ^ 64 := by
    have := limbOfNat_lt P256 k.val; simpa [limbBits] using this
  have hmul : (Expression.eval env q).val * limbOfNat P256 k.val ≤ 2 ^ 70 * 2 ^ 64 :=
    Nat.mul_le_mul (by omega) (by omega)
  have hmul2 : c976 * (Expression.eval env (lam[k.val]'k.isLt)).val ≤ (2 ^ 32 + 976) * 2 ^ 64 :=
    Nat.mul_le_mul_left _ (by omega)
  have hNf : vFoldWR.Nf k.val = 2 ^ 135 := by
    show (if k.val < 4 then 2 ^ 135 else 1) = 2 ^ 135
    rw [if_pos k.isLt]
  have hbig : (2 : ℕ) ^ 70 * 2 ^ 64 + 2 ^ 64 + 2 ^ 64 + (2 ^ 32 + 976) * 2 ^ 64 < 2 ^ 135 := by
    decide
  rw [val_foldRhsY env q a b lam hq ha hb hlam k.val k.isLt, hNf]
  omega

/-! ### Polynomial values -/

set_option exponentiation.threshold 1200 in
lemma polyValue_foldLhs2 (env : Environment (F circomPrime))
    (P Q : Vector (Expression (F circomPrime)) 7) (v : ℕ) (hv : v < 2 ^ 291)
    (hPQ : ∀ k : Fin 7, (Expression.eval env (P[k.val] + Q[k.val])).val < 20 * 2 ^ 128) :
    polyValue 64 (Vector.map (Expression.eval env)
        (Vector.mapFinRange 4 fun k : Fin 4 => foldLhs2 P Q v k.val))
      = convLow2 env P Q + cF * convHigh2 env P Q + v := by
  have e0 := val_foldLhs2 env P Q v hv hPQ 0 (by omega)
  have e1 := val_foldLhs2 env P Q v hv hPQ 1 (by omega)
  have e2 := val_foldLhs2 env P Q v hv hPQ 2 (by omega)
  have e3 := val_foldLhs2 env P Q v hv hPQ 3 (by omega)
  rw [if_pos (by omega : (0 : ℕ) < 3)] at e0
  rw [if_pos (by omega : (1 : ℕ) < 3)] at e1
  rw [if_pos (by omega : (2 : ℕ) < 3)] at e2
  rw [if_neg (by omega : ¬ (3 : ℕ) < 3)] at e3
  have hoff : offLimbW v 0 + offLimbW v 1 * 2 ^ 64 + offLimbW v 2 * 2 ^ 128
      + offLimbW v 3 * 2 ^ 192 = v := by
    have h := offLimbW_sum v
    simpa only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.mul_zero, pow_zero,
      Nat.mul_one, zero_add] using h
  simp only [polyValue, Vector.getElem_map, Vector.getElem_mapFinRange, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ, convLow2, convHigh2,
    Finset.sum_range_succ, Finset.sum_range_zero]
  rw [e0, e1, e2, e3]
  simp only [Nat.mul_zero, pow_zero, Nat.mul_one, add_zero, zero_add]
  ring_nf
  omega

set_option exponentiation.threshold 1200 in
lemma polyValue_wideLhs (env : Environment (F circomPrime))
    (P Q : Vector (Expression (F circomPrime)) 7) (v : ℕ) (hv : v < 2 ^ 320)
    (hPQ : ∀ k : Fin 7, (Expression.eval env (P[k.val] + Q[k.val])).val < 20 * 2 ^ 128) :
    polyValue 64 (Vector.map (Expression.eval env)
        (Vector.mapFinRange 10 fun k : Fin 10 => wideLhs P Q v k.val))
      = convLow2 env P Q + 2 ^ 256 * convHigh2 env P Q + v := by
  have hval : ∀ k, k < 10 → (Expression.eval env (wideLhs P Q v k)).val
      = sumPQ env P Q k + (if k < 5 then limbOfNat v k else 0) := by
    intro k hk
    unfold wideLhs sumPQ
    have hA : (Expression.eval env (if h : k < 7 then P[k]'h + Q[k]'h else 0)).val
        = (if h : k < 7 then (Expression.eval env (P[k]'h + Q[k]'h)).val else 0) := by
      by_cases h : k < 7
      · rw [dif_pos h, dif_pos h]
      · rw [dif_neg h, dif_neg h,
          show Expression.eval env (0 : Expression (F circomPrime)) = 0 from rfl, ZMod.val_zero]
    have hB : (Expression.eval env (if k < 5 then cExp v k else 0)).val
        = (if k < 5 then limbOfNat v k else 0) := by
      by_cases h : k < 5
      · rw [if_pos h, if_pos h, Canonicalize.eval_cExp, val_limbOfNat]
      · rw [if_neg h, if_neg h,
          show Expression.eval env (0 : Expression (F circomPrime)) = 0 from rfl, ZMod.val_zero]
    have hAlt : (Expression.eval env (if h : k < 7 then P[k]'h + Q[k]'h else 0)).val
        < 20 * 2 ^ 128 := by
      rw [hA]; split
      · rename_i h; exact hPQ ⟨k, h⟩
      · positivity
    have hBlt : (Expression.eval env (if k < 5 then cExp v k else 0)).val < 2 ^ 64 := by
      rw [hB]; split
      · have := limbOfNat_lt v k; simpa [limbBits] using this
      · positivity
    have hle := ZMod.val_add_le (Expression.eval env (if h : k < 7 then P[k]'h + Q[k]'h else 0))
      (Expression.eval env (if k < 5 then cExp v k else 0))
    have hpr : (20 : ℕ) * 2 ^ 128 + 2 ^ 64 < circomPrime := by decide
    rw [show Expression.eval env ((if h : k < 7 then P[k]'h + Q[k]'h else 0)
          + (if k < 5 then cExp v k else 0))
        = Expression.eval env (if h : k < 7 then P[k]'h + Q[k]'h else 0)
          + Expression.eval env (if k < 5 then cExp v k else 0) from rfl]
    rw [ZMod.val_add_of_lt (by omega), hA, hB]
  have hlimbs : limbOfNat v 0 + limbOfNat v 1 * 2 ^ 64 + limbOfNat v 2 * 2 ^ 128
      + limbOfNat v 3 * 2 ^ 192 + limbOfNat v 4 * 2 ^ 256 = v := by
    have hdec := limb_decomp_mod 64 5 v
    rw [show (64 : ℕ) * 5 = 320 from rfl, Nat.mod_eq_of_lt hv] at hdec
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, limbOfNat, limbBits] at hdec ⊢
    norm_num at hdec ⊢
    omega
  simp only [polyValue, Vector.getElem_map, Vector.getElem_mapFinRange, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ, convLow2, convHigh2,
    Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hval 0 (by omega), hval 1 (by omega), hval 2 (by omega), hval 3 (by omega),
    hval 4 (by omega), hval 5 (by omega), hval 6 (by omega), hval 7 (by omega),
    hval 8 (by omega), hval 9 (by omega)]
  norm_num
  simp only [sumPQ, dif_neg (by omega : ¬ (7 : ℕ) < 7), dif_neg (by omega : ¬ (8 : ℕ) < 7),
    dif_neg (by omega : ¬ (9 : ℕ) < 7)]
  ring_nf
  omega

set_option exponentiation.threshold 1200 in
lemma polyValue_foldRhsY (env : Environment (F circomPrime)) (q : Expression (F circomPrime))
    (a b lam : Var Emu (F circomPrime))
    (hq : (Expression.eval env q).val < 2 ^ 70)
    (ha : BigInt.Normalized 64 (Vector.map (Expression.eval env) a))
    (hb : BigInt.Normalized 64 (Vector.map (Expression.eval env) b))
    (hlam : BigInt.Normalized 64 (Vector.map (Expression.eval env) lam)) :
    polyValue 64 (Vector.map (Expression.eval env)
        (Vector.mapFinRange 4 fun k : Fin 4 => foldRhsY q a b lam k.val))
      = (Expression.eval env q).val * P256
        + BigInt.value 64 (Vector.map (Expression.eval env) a)
        + BigInt.value 64 (Vector.map (Expression.eval env) b)
        + c976 * BigInt.value 64 (Vector.map (Expression.eval env) lam) := by
  have e0 := val_foldRhsY env q a b lam hq ha hb hlam 0 (by omega)
  have e1 := val_foldRhsY env q a b lam hq ha hb hlam 1 (by omega)
  have e2 := val_foldRhsY env q a b lam hq ha hb hlam 2 (by omega)
  have e3 := val_foldRhsY env q a b lam hq ha hb hlam 3 (by omega)
  have hva := MulMod.value_map_eval (B := 64) env a
  have hvb := MulMod.value_map_eval (B := 64) env b
  have hvl := MulMod.value_map_eval (B := 64) env lam
  have hlimb : limbOfNat P256 0 + limbOfNat P256 1 * 2 ^ 64 + limbOfNat P256 2 * 2 ^ 128
      + limbOfNat P256 3 * 2 ^ 192 = P256 := by
    have h := limb_sum_P256
    simpa only [numLimbs, limbBits, Finset.sum_range_succ, Finset.sum_range_zero,
      Nat.mul_zero, pow_zero, Nat.mul_one, zero_add] using h
  simp only [polyValue, Vector.getElem_map, Vector.getElem_mapFinRange, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ] at hva hvb hvl ⊢
  rw [e0, e1, e2, e3, hva, hvb, hvl]
  simp only [Nat.mul_zero, pow_zero, Nat.mul_one, add_zero, zero_add]
  set l0 := limbOfNat P256 0
  set l1 := limbOfNat P256 1
  set l2 := limbOfNat P256 2
  set l3 := limbOfNat P256 3
  rw [← hlimb]
  ring

/-! ### The wide fold bridge -/

lemma convHigh2_lt (env : Environment (F circomPrime))
    (P Q : Vector (Expression (F circomPrime)) 7)
    (hPQ : ∀ k : Fin 7, (Expression.eval env (P[k.val] + Q[k.val])).val < 20 * 2 ^ 128) :
    convHigh2 env P Q < 2 ^ 262 := by
  have h4 := sumPQ_lt env P Q hPQ 4
  have h5 := sumPQ_lt env P Q hPQ 5
  have h6 := sumPQ_lt env P Q hPQ 6
  simp only [convHigh2, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  omega

lemma convLow2_lt (env : Environment (F circomPrime))
    (P Q : Vector (Expression (F circomPrime)) 7)
    (hPQ : ∀ k : Fin 7, (Expression.eval env (P[k.val] + Q[k.val])).val < 20 * 2 ^ 128) :
    convLow2 env P Q < 2 ^ 324 + 2 ^ 323 := by
  have h0 := sumPQ_lt env P Q hPQ 0
  have h1 := sumPQ_lt env P Q hPQ 1
  have h2 := sumPQ_lt env P Q hPQ 2
  have h3 := sumPQ_lt env P Q hPQ 3
  simp only [convLow2, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  omega

/-- Shifting the quotient by the folded-away high half. -/
lemma fold_shift (L4 H T v : ℕ) (hT : T ≤ L4 + cF * H + v) :
    L4 + 2 ^ 256 * H + v - T = P256 * H + (L4 + cF * H + v - T) := by
  have hpc : P256 + cF = 2 ^ 256 := p_add_cF
  have hmix : P256 * H + cF * H = 2 ^ 256 * H := by
    rw [← Nat.add_mul, hpc]
  omega

end FoldWide
end Solution.Secp256k1ScalarMulFixedBase

end DonorFile3_0

-- Adapted donor module: CrtFold
section DonorFile3_1

/-!
# Bridging the CRT multiply into the existing fold certificates

`FoldQuot.foldLhs` / `FoldWide.foldLhs2` take the seven raw convolution
coefficients and fold them onto four positions.  `CrtMul.crtFoldMul` produces
the four folded coefficients directly, so the certificate's left-hand side
becomes `crtLhs` / `crtLhs2`: the witnessed coefficient plus the constant
offset limb.

The bound and identity lemmas in `FoldQuot` / `FoldWideC1` are already stated
for an *arbitrary* coefficient vector `P` together with a hypothesis
`hP : ∀ k, eval P[k] = eval (bigIntMulNoReduce a b)[k]`, so they can be reused
verbatim with `P := bigIntMulNoReduce a b` (a free expression vector) once the
evaluated `crtLhs` vector has been rewritten into the evaluated `foldLhs`
vector.  That rewrite is exactly what this file provides.
-/

namespace Solution.Secp256k1ScalarMulFixedBase

open GroupedFlex (polyEvalExpr)
open Challenge.CostR1CS

namespace CrtMul

/-- Narrow folded left-hand side built from the four CRT witnesses. -/
def crtLhs (Fv : Vector (Expression (F circomPrime)) 4) (v k : ℕ) :
    Expression (F circomPrime) :=
  (if h : k < 4 then Fv[k]'h else 0) + FoldQuot.wExp v k

/-- Wide folded left-hand side built from two sets of four CRT witnesses. -/
def crtLhs2 (Fv Gv : Vector (Expression (F circomPrime)) 4) (v k : ℕ) :
    Expression (F circomPrime) :=
  (if h : k < 4 then Fv[k]'h + Gv[k]'h else 0) + FoldWide.wExpW v k

theorem affine_crtLhs {Fv : Vector (Expression (F circomPrime)) 4}
    (hF : ∀ (j : ℕ) (hj : j < 4), Affine (Fv[j]'hj)) (v k : ℕ) : Affine (crtLhs Fv v k) := by
  unfold crtLhs
  refine Affine.add ?_ (FoldQuot.affine_wExp _ _)
  split
  · exact hF _ (by omega)
  · exact Affine.zero

theorem affine_crtLhs2 {Fv Gv : Vector (Expression (F circomPrime)) 4}
    (hF : ∀ (j : ℕ) (hj : j < 4), Affine (Fv[j]'hj))
    (hG : ∀ (j : ℕ) (hj : j < 4), Affine (Gv[j]'hj)) (v k : ℕ) :
    Affine (crtLhs2 Fv Gv v k) := by
  unfold crtLhs2
  refine Affine.add ?_ (Affine.const _)
  split
  · exact Affine.add (hF _ (by omega)) (hG _ (by omega))
  · exact Affine.zero

/-! ### Environment stability -/

lemma foldCoeff_eval_stable {e e' : Environment (F circomPrime)}
    {P : Vector (Expression (F circomPrime)) 7}
    (hP : ∀ (j : ℕ) (hj : j < 7), Expression.eval e (P[j]'hj) = Expression.eval e' (P[j]'hj))
    (k : ℕ) :
    Expression.eval e (foldCoeff P k) = Expression.eval e' (foldCoeff P k) := by
  unfold foldCoeff
  by_cases h4 : k < 4 <;> by_cases h3 : k < 3
  · simp only [dif_pos h4, dif_pos h3, Expression.eval, hP k (by omega), hP (k + 4) (by omega)]
  · simp only [dif_pos h4, dif_neg h3, Expression.eval, hP k (by omega)]
  · omega
  · simp only [dif_neg h4, dif_neg h3, Expression.eval]

lemma crtLhs_eval_stable {e e' : Environment (F circomPrime)}
    {Fv : Vector (Expression (F circomPrime)) 4}
    (hF : ∀ (j : ℕ) (hj : j < 4), Expression.eval e (Fv[j]'hj) = Expression.eval e' (Fv[j]'hj))
    (v k : ℕ) :
    Expression.eval e (crtLhs Fv v k) = Expression.eval e' (crtLhs Fv v k) := by
  unfold crtLhs FoldQuot.wExp
  by_cases h4 : k < 4
  · simp only [dif_pos h4, Expression.eval, hF k h4]
  · simp only [dif_neg h4, Expression.eval]

lemma crtLhs2_eval_stable {e e' : Environment (F circomPrime)}
    {Fv Gv : Vector (Expression (F circomPrime)) 4}
    (hF : ∀ (j : ℕ) (hj : j < 4), Expression.eval e (Fv[j]'hj) = Expression.eval e' (Fv[j]'hj))
    (hG : ∀ (j : ℕ) (hj : j < 4), Expression.eval e (Gv[j]'hj) = Expression.eval e' (Gv[j]'hj))
    (v k : ℕ) :
    Expression.eval e (crtLhs2 Fv Gv v k) = Expression.eval e' (crtLhs2 Fv Gv v k) := by
  unfold crtLhs2 FoldWide.wExpW
  by_cases h4 : k < 4
  · simp only [dif_pos h4, Expression.eval, hF k h4, hG k h4]
  · simp only [dif_neg h4, Expression.eval]

/-! ### Evaluated-vector bridges -/

/-- The evaluated narrow CRT left-hand side equals the evaluated folded
convolution left-hand side. -/
lemma map_crtLhs_eq (env : Environment (F circomPrime)) (off : ℕ)
    (a b : Var Emu (F circomPrime)) (v : ℕ)
    (hpts : ∀ j : Fin 4,
      Expression.eval env (polyEvalExpr a (rho j))
          * Expression.eval env (polyEvalExpr b (rho j))
        = Expression.eval env (polyEvalExpr (zVec4 off) (rho j))) :
    Vector.map (Expression.eval env)
        (Vector.mapFinRange 4 fun k : Fin 4 => crtLhs (zVec4 off) v k.val)
      = Vector.map (Expression.eval env)
        (Vector.mapFinRange 4 fun k : Fin 4 =>
          FoldQuot.foldLhs (bigIntMulNoReduce a b) v k.val) := by
  have hbr := crt_eval_bridge env off a b hpts
  apply Vector.ext
  intro k hk
  rw [Vector.getElem_map, Vector.getElem_map, Vector.getElem_mapFinRange,
    Vector.getElem_mapFinRange]
  rw [foldLhs_eq_foldCoeff_add]
  show Expression.eval env ((if h : k < 4 then _ else 0) + FoldQuot.wExp v k)
    = Expression.eval env (foldCoeff (bigIntMulNoReduce a b) k + FoldQuot.wExp v k)
  rw [dif_pos hk]
  show Expression.eval env ((zVec4 off)[k]) + Expression.eval env (FoldQuot.wExp v k)
    = Expression.eval env (foldCoeff (bigIntMulNoReduce a b) k)
      + Expression.eval env (FoldQuot.wExp v k)
  rw [show Expression.eval env ((zVec4 off)[k])
      = Expression.eval env ((zVec4 off)[(⟨k, hk⟩ : Fin 4).val]) from rfl, hbr ⟨k, hk⟩]

/-- The evaluated wide CRT left-hand side equals the evaluated folded
convolution left-hand side. -/
lemma map_crtLhs2_eq (env : Environment (F circomPrime)) (off2 off1 : ℕ)
    (a2 b2 a1 b1 : Var Emu (F circomPrime)) (v : ℕ)
    (hpts2 : ∀ j : Fin 4,
      Expression.eval env (polyEvalExpr a2 (rho j))
          * Expression.eval env (polyEvalExpr b2 (rho j))
        = Expression.eval env (polyEvalExpr (zVec4 off2) (rho j)))
    (hpts1 : ∀ j : Fin 4,
      Expression.eval env (polyEvalExpr a1 (rho j))
          * Expression.eval env (polyEvalExpr b1 (rho j))
        = Expression.eval env (polyEvalExpr (zVec4 off1) (rho j))) :
    Vector.map (Expression.eval env)
        (Vector.mapFinRange 4 fun k : Fin 4 => crtLhs2 (zVec4 off2) (zVec4 off1) v k.val)
      = Vector.map (Expression.eval env)
        (Vector.mapFinRange 4 fun k : Fin 4 =>
          FoldWide.foldLhs2 (bigIntMulNoReduce a2 b2) (bigIntMulNoReduce a1 b1) v k.val) := by
  have hbr2 := crt_eval_bridge env off2 a2 b2 hpts2
  have hbr1 := crt_eval_bridge env off1 a1 b1 hpts1
  apply Vector.ext
  intro k hk
  rw [Vector.getElem_map, Vector.getElem_map, Vector.getElem_mapFinRange,
    Vector.getElem_mapFinRange]
  have e2 : Expression.eval env ((zVec4 off2)[k]'hk)
      = Expression.eval env (foldCoeff (bigIntMulNoReduce a2 b2) k) := hbr2 ⟨k, hk⟩
  have e1 : Expression.eval env ((zVec4 off1)[k]'hk)
      = Expression.eval env (foldCoeff (bigIntMulNoReduce a1 b1) k) := hbr1 ⟨k, hk⟩
  have hA : Expression.eval env (crtLhs2 (zVec4 off2) (zVec4 off1) v k)
      = Expression.eval env ((zVec4 off2)[k]'hk) + Expression.eval env ((zVec4 off1)[k]'hk)
        + Expression.eval env (FoldWide.wExpW v k) := by
    simp only [crtLhs2, dif_pos hk, Expression.eval]
  have hB : Expression.eval env (FoldWide.foldLhs2
        (bigIntMulNoReduce a2 b2) (bigIntMulNoReduce a1 b1) v k)
      = Expression.eval env (foldCoeff (bigIntMulNoReduce a2 b2) k)
        + Expression.eval env (foldCoeff (bigIntMulNoReduce a1 b1) k)
        + Expression.eval env (FoldWide.wExpW v k) := by
    unfold FoldWide.foldLhs2 foldCoeff
    by_cases h3 : k < 3
    · simp only [dif_pos hk, dif_pos h3, Expression.eval]; ring
    · simp only [dif_pos hk, dif_neg h3, Expression.eval]; ring
  rw [hA, hB, e1, e2]

end CrtMul

end Solution.Secp256k1ScalarMulFixedBase

end DonorFile3_1

-- Adapted donor module: FoldQInv
section DonorFile3_2

/-!
# Certificate inversion for the narrow (CRT-folded) reduction sites

The folded quotient `q` of a narrow certificate is pinned by the very identity
it appears in, and `P256` is a compile-time constant, so instead of witnessing
`q` it can be written directly as the affine expression

  `q = (∑ₖ lhsₖ 2^(64k) - ∑ₖ tailₖ 2^(64k)) * (P256 : F)⁻¹`

over wires that are already allocated.  That saves one allocation per site
while leaving the surviving `RangeCheck` (which already accepts an arbitrary
`Expression`) and the `GroupedFlex` shape untouched.
-/

namespace Solution.Secp256k1ScalarMulFixedBase

open Challenge.CostR1CS
open Solution.Secp256k1ScalarMulFixedBase.Limbs

namespace CrtMul

/-- `∑_{k<4} crtLhs Fv v k * 2 ^ (64 k)` as an expression. -/
def crtLhsPoly (Fv : Vector (Expression (F circomPrime)) 4) (v : ℕ) :
    Expression (F circomPrime) :=
  crtLhs Fv v 0 + FoldQuot.wPow 1 * crtLhs Fv v 1 + FoldQuot.wPow 2 * crtLhs Fv v 2
    + FoldQuot.wPow 3 * crtLhs Fv v 3

/-- The folded quotient of a narrow certificate, recovered as an affine
expression over already-allocated wires. -/
def crtQInv (Fv : Vector (Expression (F circomPrime)) 4) (v : ℕ)
    (a b c : Var Emu (F circomPrime)) : Expression (F circomPrime) :=
  (((P256 : ℕ) : F circomPrime)⁻¹) * (crtLhsPoly Fv v - FoldQuot.tailPoly a b c)

theorem affine_crtLhsPoly {Fv : Vector (Expression (F circomPrime)) 4}
    (hF : ∀ (j : ℕ) (hj : j < 4), Affine (Fv[j]'hj)) (v : ℕ) : Affine (crtLhsPoly Fv v) := by
  unfold crtLhsPoly
  exact Affine.add (Affine.add (Affine.add (affine_crtLhs hF v 0)
    (Affine.fconst_mul _ (affine_crtLhs hF v 1)))
    (Affine.fconst_mul _ (affine_crtLhs hF v 2)))
    (Affine.fconst_mul _ (affine_crtLhs hF v 3))

theorem affine_crtQInv {Fv : Vector (Expression (F circomPrime)) 4}
    (hF : ∀ (j : ℕ) (hj : j < 4), Affine (Fv[j]'hj)) (v : ℕ)
    {a b c : Var Emu (F circomPrime)}
    (ha : AffineW a) (hb : AffineW b) (hc : AffineW c) :
    Affine (crtQInv Fv v a b c) :=
  Affine.fconst_mul _ (Affine.sub (affine_crtLhsPoly hF v) (FoldQuot.affine_tailPoly ha hb hc))

lemma tailPoly_eval_stable {e e' : Environment (F circomPrime)}
    {a b c : Var Emu (F circomPrime)}
    (ha : ∀ (j : ℕ) (hj : j < 4), Expression.eval e (a[j]'hj) = Expression.eval e' (a[j]'hj))
    (hb : ∀ (j : ℕ) (hj : j < 4), Expression.eval e (b[j]'hj) = Expression.eval e' (b[j]'hj))
    (hc : ∀ (j : ℕ) (hj : j < 4), Expression.eval e (c[j]'hj) = Expression.eval e' (c[j]'hj)) :
    Expression.eval e (FoldQuot.tailPoly a b c)
      = Expression.eval e' (FoldQuot.tailPoly a b c) := by
  simp only [FoldQuot.tailPoly, Expression.eval,
    ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), ha 3 (by decide),
    hb 0 (by decide), hb 1 (by decide), hb 2 (by decide), hb 3 (by decide),
    hc 0 (by decide), hc 1 (by decide), hc 2 (by decide), hc 3 (by decide)]

lemma crtQInv_eval_stable {e e' : Environment (F circomPrime)}
    {Fv : Vector (Expression (F circomPrime)) 4}
    (hF : ∀ (j : ℕ) (hj : j < 4), Expression.eval e (Fv[j]'hj) = Expression.eval e' (Fv[j]'hj))
    (v : ℕ) {a b c : Var Emu (F circomPrime)}
    (ha : ∀ (j : ℕ) (hj : j < 4), Expression.eval e (a[j]'hj) = Expression.eval e' (a[j]'hj))
    (hb : ∀ (j : ℕ) (hj : j < 4), Expression.eval e (b[j]'hj) = Expression.eval e' (b[j]'hj))
    (hc : ∀ (j : ℕ) (hj : j < 4), Expression.eval e (c[j]'hj) = Expression.eval e' (c[j]'hj)) :
    Expression.eval e (crtQInv Fv v a b c) = Expression.eval e' (crtQInv Fv v a b c) := by
  simp only [crtQInv, crtLhsPoly, Expression.eval,
    crtLhs_eval_stable hF v 0, crtLhs_eval_stable hF v 1,
    crtLhs_eval_stable hF v 2, crtLhs_eval_stable hF v 3,
    tailPoly_eval_stable ha hb hc]

lemma eval_crtLhsPoly (env : Environment (F circomPrime))
    (Fv : Vector (Expression (F circomPrime)) 4) (v : ℕ) :
    Expression.eval env (crtLhsPoly Fv v)
      = ((polyValue 64 (Vector.map (Expression.eval env)
          (Vector.mapFinRange 4 fun k : Fin 4 => crtLhs Fv v k.val)) : ℕ) : F circomPrime) := by
  simp only [polyValue, Vector.getElem_map, Vector.getElem_mapFinRange,
    Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ, crtLhsPoly,
    FoldQuot.wPow, Expression.eval]
  push_cast [FoldQuot.natCast_val_F]
  ring

/-- Given the natural-number certificate identity, the inverted quotient
expression evaluates to exactly the honest quotient. -/
lemma eval_crtQInv_of_identity (env : Environment (F circomPrime))
    (Fv : Vector (Expression (F circomPrime)) 4) (v : ℕ)
    (a b c : Var Emu (F circomPrime)) (q0 : ℕ)
    (hid : polyValue 64 (Vector.map (Expression.eval env)
          (Vector.mapFinRange 4 fun k : Fin 4 => crtLhs Fv v k.val))
        = q0 * P256 + BigInt.value 64 (Vector.map (Expression.eval env) a)
          + BigInt.value 64 (Vector.map (Expression.eval env) b)
          + BigInt.value 64 (Vector.map (Expression.eval env) c)) :
    Expression.eval env (crtQInv Fv v a b c) = ((q0 : ℕ) : F circomPrime) := by
  have hL := eval_crtLhsPoly env Fv v
  have hT := FoldQuot.eval_tailPoly env a b c
  have hkey : Expression.eval env (crtLhsPoly Fv v)
      - Expression.eval env (FoldQuot.tailPoly a b c)
      = ((q0 : ℕ) : F circomPrime) * ((P256 : ℕ) : F circomPrime) := by
    rw [hL, hT, hid]; push_cast; ring
  have hinv : (((P256 : ℕ) : F circomPrime))⁻¹ * ((P256 : ℕ) : F circomPrime) = 1 :=
    inv_mul_cancel₀ FoldQuot.P256_cast_ne_zero
  simp only [crtQInv, Expression.eval]
  linear_combination (((P256 : ℕ) : F circomPrime))⁻¹ * hkey
    + ((q0 : ℕ) : F circomPrime) * hinv

end CrtMul

end Solution.Secp256k1ScalarMulFixedBase

end DonorFile3_2

-- Adapted donor module: AffineRangeBounds
section DonorFile3_3

/-!
Integer bounds for the shifted certificates. These lemmas deliberately distinguish
honest semantic assignments (completeness) from replacement-range assumptions
(soundness). No old quotient or carry range is assumed in the soundness direction.
-/
namespace Solution.Secp256k1ScalarMulFixedBase.AffineRangeBounds

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

def B : ℤ := 2 ^ 64
def D : ℤ := B - 1
def R : ℤ := B ^ 2
def c : ℤ := 2 ^ 32 + 977
def q : ℤ := B ^ 4 - c
def nativePrime : ℕ := 21888242871839275222246405745257275088548364400416034343698204186575808495617

def Limb (a : ℤ) : Prop := 0 ≤ a ∧ a ≤ D

theorem centered_product_bounds {a b : ℤ} (ha : Limb a) (hb : Limb b) :
    -B * D ≤ 2*a*b - B*(a+b) ∧ 2*a*b - B*(a+b) ≤ 0 := by
  have hB : 2 ≤ B := by norm_num [B]
  obtain ⟨ha0, haD⟩ := ha
  obtain ⟨hb0, hbD⟩ := hb
  have hDa : 0 ≤ D-a := by omega
  have hDb : 0 ≤ D-b := by omega
  constructor
  · by_cases h : 2*a ≤ B
    · have hh := mul_nonneg (sub_nonneg.mpr h) hDb
      have he := mul_nonneg (show 0 ≤ B-2 by omega) ha0
      dsimp [D] at *
      nlinarith
    · have hh := mul_nonneg (show 0 ≤ 2*a-B by omega) hb0
      have he := mul_nonneg (show 0 ≤ B by omega) hDa
      dsimp [D] at *
      nlinarith
  · have h1 := mul_nonneg ha0 hDb
    have h2 := mul_nonneg hb0 hDa
    dsimp [D] at *
    nlinarith

theorem zero_of_native_zero {z : ℤ}
    (hz : (z : ZMod nativePrime) = 0)
    (hlo : -(nativePrime : ℤ) < z) (hhi : z < nativePrime) : z = 0 := by
  obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd z nativePrime).mp hz
  norm_num [nativePrime] at hk hlo hhi
  omega

namespace Narrow

def sum (l : Fin 4 → ℤ) : ℤ := l 0 + l 1 + l 2 + l 3
def carryShift (l : Fin 4 → ℤ) : ℤ := c * (l 2 + l 3)
def quotientOffset : ℤ := 2*B + 4
def carryOffset : ℤ := (c+8)*B + 4

def low (P : Fin 7 → ℤ) (Y : Fin 4 → ℤ) : ℤ :=
  P 0 + c*P 4 + (B-4*c) - Y 0 + B*(P 1 + c*P 5 + D - Y 1)
def high (P : Fin 7 → ℤ) (Y : Fin 4 → ℤ) : ℤ :=
  P 2 + c*P 6 + D - Y 2 + B*(P 3 + (4*B-1) - Y 3)

def ProductBounds (P : Fin 7 → ℤ) : Prop :=
  ∀ i, 0 ≤ P i ∧ P i < 4 * B^2
def TailBounds (Y : Fin 4 → ℤ) : Prop :=
  ∀ i, 0 ≤ Y i ∧ Y i ≤ 3*D

theorem completeness (l : Fin 4 → ℤ) (P : Fin 7 → ℤ) (Y : Fin 4 → ℤ) (k : ℤ)
    (hl : ∀ i, Limb (l i)) (hP : ProductBounds P) (hY : TailBounds Y)
    (hP3 : P 3 = 2*l 0*l 3 + 2*l 1*l 2)
    (hP5 : P 5 = 2*l 2*l 3)
    (hsem : low P Y + R * high P Y = q*k) :
    (0 ≤ k ∧ k < 2^67) ∧
    (0 ≤ k - sum l + quotientOffset ∧ k - sum l + quotientOffset < 2^66) ∧
    (0 ≤ (R-1)*k - high P Y - carryShift l + carryOffset ∧
      (R-1)*k - high P Y - carryShift l + carryOffset < 2^97) := by
  have hc03 := centered_product_bounds (hl 0) (hl 3)
  have hc12 := centered_product_bounds (hl 1) (hl 2)
  have hc23 := centered_product_bounds (hl 2) (hl 3)
  have hcenter3 : -2*B*D ≤ P 3 - B*sum l ∧ P 3 - B*sum l ≤ 0 := by
    rw [hP3]
    dsimp [sum]
    constructor <;> nlinarith [hc03.1, hc03.2, hc12.1, hc12.2]
  have hcenter5 : -B*D ≤ P 5 - B*(l 2+l 3) ∧ P 5 - B*(l 2+l 3) ≤ 0 := by
    simpa [hP5] using hc23
  have hp0 := hP 0; have hp1 := hP 1; have hp2 := hP 2; have hp3 := hP 3
  have hp4 := hP 4; have hp5 := hP 5; have hp6 := hP 6
  have hy0 := hY 0; have hy1 := hY 1; have hy2 := hY 2; have hy3 := hY 3
  have hl0 := hl 0; have hl1 := hl 1; have hl2 := hl 2; have hl3 := hl 3
  have hk : 0 ≤ k ∧ k < 2^67 := by
    norm_num [low, high, R, q, B, c, D] at hp0 hp1 hp2 hp3 hp4 hp5 hp6 hy0 hy1 hy2 hy3 hsem ⊢
    omega
  refine ⟨hk, ?_, ?_⟩
  · norm_num [low, high, sum, quotientOffset, R, q, Limb, B, c, D] at hp0 hp1 hp2 hp3 hp4 hp5 hp6 hy0 hy1 hy2 hy3 hl0 hl1 hl2 hl3 hcenter3 hsem ⊢
    omega
  · norm_num [low, high, sum, carryShift, carryOffset, R, q, Limb, B, c, D] at hp0 hp1 hp2 hp3 hp4 hp5 hp6 hy0 hy1 hy2 hy3 hl0 hl1 hl2 hl3 hcenter5 hsem hk ⊢
    omega

theorem soundness (l : Fin 4 → ℤ) (P : Fin 7 → ℤ) (Y : Fin 4 → ℤ) (r v : ℤ)
    (hl : ∀ i, Limb (l i)) (hP : ProductBounds P) (hY : TailBounds Y)
    (hr : 0 ≤ r ∧ r < 2^66) (hv : 0 ≤ v ∧ v < 2^97)
    (hlo : ((low P Y - (R-c)*(r + sum l - quotientOffset)
      - R*(v + carryShift l - carryOffset) : ℤ) : ZMod nativePrime) = 0)
    (hhi : ((high P Y - (R-1)*(r + sum l - quotientOffset)
      + (v + carryShift l - carryOffset) : ℤ) : ZMod nativePrime) = 0) :
    low P Y + R*high P Y = q*(r + sum l - quotientOffset) := by
  have hp0 := hP 0; have hp1 := hP 1; have hp2 := hP 2; have hp3 := hP 3
  have hp4 := hP 4; have hp5 := hP 5; have hp6 := hP 6
  have hy0 := hY 0; have hy1 := hY 1; have hy2 := hY 2; have hy3 := hY 3
  have hl0 := hl 0; have hl1 := hl 1; have hl2 := hl 2; have hl3 := hl 3
  have hE0 : low P Y - (R-c)*(r + sum l - quotientOffset)
      - R*(v + carryShift l - carryOffset) = 0 := by
    apply zero_of_native_zero hlo
    all_goals
      norm_num [low, high, sum, quotientOffset, carryShift, carryOffset, nativePrime,
        R, q, Limb, B, c, D] at hp0 hp1 hp2 hp3 hp4 hp5 hp6 hy0 hy1 hy2 hy3 hl0 hl1 hl2 hl3 hr hv ⊢
      omega
  have hE1 : high P Y - (R-1)*(r + sum l - quotientOffset)
      + (v + carryShift l - carryOffset) = 0 := by
    apply zero_of_native_zero hhi
    all_goals
      norm_num [low, high, sum, quotientOffset, carryShift, carryOffset, nativePrime,
        R, q, Limb, B, c, D] at hp0 hp1 hp2 hp3 hp4 hp5 hp6 hy0 hy1 hy2 hy3 hl0 hl1 hl2 hl3 hr hv ⊢
      omega
  have hq : q = R^2-c := by dsimp [q, R]; ring
  rw [hq]
  linear_combination hE0 + R*hE1

end Narrow

namespace Wide

def sum (a b x : Fin 4 → ℤ) : ℤ := Narrow.sum a + 2*Narrow.sum b - Narrow.sum x
def delta (A T x : Fin 4 → ℤ) : ℤ := A 2+A 3+T 2+T 3-2*x 2-2*x 3
def halfC : ℤ := (c-1)/2
def carryShift (a b A T x : Fin 4 → ℤ) : ℤ :=
  c*(a 2+a 3)+2*c*(b 2+b 3)+halfC*delta A T x
def quotientOffset : ℤ := 4*B+16*c+16
def carryOffset : ℤ := (2*c+40)*B+10*c+10
def off0 : ℤ := B-977*2^34
def off1 : ℤ := B-5
def off3 : ℤ := 2^34*B-1

def low (P : Fin 7 → ℤ) (Y : Fin 4 → ℤ) : ℤ :=
  P 0+c*P 4+off0-Y 0+B*(P 1+c*P 5+off1-Y 1)
def high (P : Fin 7 → ℤ) (Y : Fin 4 → ℤ) : ℤ :=
  P 2+c*P 6+D-Y 2+B*(P 3+off3-Y 3)
def ProductBounds (P : Fin 7 → ℤ) : Prop := ∀ i, 0 ≤ P i ∧ P i < 20*B^2
def TailBounds (Y : Fin 4 → ℤ) : Prop := ∀ i, 0 ≤ Y i ∧ Y i ≤ (c+1)*D

def term (a b A T x : Fin 4 → ℤ) (i j : Fin 4) : ℤ :=
  a i*(A j+D-x j)+b i*(T j+(if j.val=0 then 2*B-2*c else 2*B-2)-x j)
def V (a b A T x : ℤ) : ℤ := a*A+b*T+(B-a-b)*x
def W (a b A T x : ℤ) : ℤ := (a-B/2)*(A-x)+(b-B/2)*(T-x)

lemma v_bounds {a b A T x : ℤ} (ha : Limb a) (hb : Limb b)
    (hA : Limb A) (hT : Limb T) (hx : Limb x) :
    -(B-2)*D ≤ V a b A T x ∧ V a b A T x ≤ 2*D^2 := by
  obtain ⟨ha0, haD⟩ := ha
  obtain ⟨hb0, hbD⟩ := hb
  obtain ⟨hA0, hAD⟩ := hA
  obtain ⟨hT0, hTD⟩ := hT
  obtain ⟨hx0, hxD⟩ := hx
  have h1 := mul_nonneg ha0 hA0
  have h2 := mul_nonneg hb0 hT0
  have h3 := mul_nonneg ha0 (sub_nonneg.mpr hAD)
  have h4 := mul_nonneg hb0 (sub_nonneg.mpr hTD)
  have hB : 2 ≤ B := by norm_num [B]
  by_cases h : a+b ≤ B
  · have h5 := mul_nonneg (show 0 ≤ B-a-b by omega) hx0
    have h6 := mul_nonneg (show 0 ≤ B-a-b by omega) (sub_nonneg.mpr hxD)
    dsimp [V, D] at *
    constructor <;> nlinarith
  · have h5 := mul_nonneg (show 0 ≤ a+b-B by omega) hx0
    have h6 := mul_nonneg (show 0 ≤ a+b-B by omega) (sub_nonneg.mpr hxD)
    dsimp [V, D] at *
    constructor <;> nlinarith

lemma centered_diff_bounds {a A x : ℤ} (ha : Limb a) (hA : Limb A) (hx : Limb x) :
    -(B/2)*D ≤ (a-B/2)*(A-x) ∧ (a-B/2)*(A-x) ≤ (B/2)*D := by
  obtain ⟨ha0, haD⟩ := ha
  obtain ⟨hA0, hAD⟩ := hA
  obtain ⟨hx0, hxD⟩ := hx
  have hm : 0 ≤ B-a := by dsimp [D] at haD; omega
  have hd1 : 0 ≤ D-A+x := by omega
  have hd2 : 0 ≤ D+A-x := by omega
  have h1 := mul_nonneg ha0 hd1
  have h2 := mul_nonneg hm hd2
  have h3 := mul_nonneg ha0 hd2
  have h4 := mul_nonneg hm hd1
  norm_num [B, D] at *
  constructor <;> nlinarith

lemma w_bounds {a b A T x : ℤ} (ha : Limb a) (hb : Limb b)
    (hA : Limb A) (hT : Limb T) (hx : Limb x) :
    -B*D ≤ W a b A T x ∧ W a b A T x ≤ B*D := by
  have h1 := centered_diff_bounds ha hA hx
  have h2 := centered_diff_bounds hb hT hx
  norm_num [W, B, D] at h1 h2 ⊢
  omega

theorem completeness (a b A T x : Fin 4 → ℤ) (P : Fin 7 → ℤ) (Y : Fin 4 → ℤ) (k : ℤ)
    (ha : ∀ i, Limb (a i)) (hb : ∀ i, Limb (b i)) (hA : ∀ i, Limb (A i))
    (hT : ∀ i, Limb (T i)) (hx : ∀ i, Limb (x i))
    (hP : ProductBounds P) (hY : TailBounds Y)
    (hP3 : P 3 = term a b A T x 0 3+term a b A T x 1 2+
      term a b A T x 2 1+term a b A T x 3 0)
    (hP5 : P 5 = term a b A T x 2 3+term a b A T x 3 2)
    (hsem : low P Y+R*high P Y = q*k) :
    (0 ≤ k ∧ k < 2^69) ∧
    (0 ≤ k-sum a b x+quotientOffset ∧ k-sum a b x+quotientOffset < 2^68) ∧
    (0 ≤ (R-1)*k-high P Y-carryShift a b A T x+carryOffset ∧
      (R-1)*k-high P Y-carryShift a b A T x+carryOffset < 2^99) := by
  have hv03 := v_bounds (ha 0) (hb 0) (hA 3) (hT 3) (hx 3)
  have hv12 := v_bounds (ha 1) (hb 1) (hA 2) (hT 2) (hx 2)
  have hv21 := v_bounds (ha 2) (hb 2) (hA 1) (hT 1) (hx 1)
  have hv30 := v_bounds (ha 3) (hb 3) (hA 0) (hT 0) (hx 0)
  have hw23 := w_bounds (ha 2) (hb 2) (hA 3) (hT 3) (hx 3)
  have hw32 := w_bounds (ha 3) (hb 3) (hA 2) (hT 2) (hx 2)
  have ha0 := ha 0; have ha1 := ha 1; have ha2 := ha 2; have ha3 := ha 3
  have hb0 := hb 0; have hb1 := hb 1; have hb2 := hb 2; have hb3 := hb 3
  have hA0 := hA 0; have hA1 := hA 1; have hA2 := hA 2; have hA3 := hA 3
  have hT0 := hT 0; have hT1 := hT 1; have hT2 := hT 2; have hT3 := hT 3
  have hx0 := hx 0; have hx1 := hx 1; have hx2 := hx 2; have hx3 := hx 3
  have hcenter3 : -4*(B-2)*D-(2*c+10)*D ≤ P 3-B*sum a b x ∧
      P 3-B*sum a b x ≤ 8*D^2 := by
    norm_num [V, term, sum, Narrow.sum, Limb, B, D, c] at hv03 hv12 hv21 hv30 hP3 ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 ⊢
    constructor <;> nlinarith
  have hcenter5 : -2*c*R*D-6*c*B*D-2*R*D ≤ c*B*P 5-R*carryShift a b A T x ∧
      c*B*P 5-R*carryShift a b A T x ≤ 2*c*R*D+2*R*D := by
    have he : c*B*P 5-R*carryShift a b A T x =
        c*B*(W (a 2) (b 2) (A 3) (T 3) (x 3)+W (a 3) (b 3) (A 2) (T 2) (x 2))-
        c*B*(a 2+a 3+2*b 2+2*b 3)+(R/2)*delta A T x := by
      rw [hP5]
      norm_num [term, W, carryShift, halfC, delta, R, B, D, c]
      ring
    rw [he]
    norm_num [delta, R, B, D, c, Limb] at ha2 ha3 hb2 hb3 hA2 hA3 hT2 hT3 hx2 hx3 hw23 hw32 ⊢
    omega
  have hp0 := hP 0; have hp1 := hP 1; have hp2 := hP 2; have hp3 := hP 3
  have hp4 := hP 4; have hp5 := hP 5; have hp6 := hP 6
  have hy0 := hY 0; have hy1 := hY 1; have hy2 := hY 2; have hy3 := hY 3
  have hk : 0 ≤ k ∧ k < 2^69 := by
    norm_num [low, high, off0, off1, off3, R, q, B, c, D] at hp0 hp1 hp2 hp3 hp4 hp5 hp6 hy0 hy1 hy2 hy3 hsem ⊢
    omega
  refine ⟨hk, ?_, ?_⟩
  · norm_num [low, high, off0, off1, off3, sum, Narrow.sum, quotientOffset, R, q, Limb, B, c, D] at hp0 hp1 hp2 hp3 hp4 hp5 hp6 hy0 hy1 hy2 hy3 ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hx0 hx1 hx2 hx3 hcenter3 hsem ⊢
    omega
  · norm_num [low, high, off0, off1, off3, carryOffset, R, q, B, c, D] at hp0 hp1 hp2 hp3 hp4 hp5 hp6 hy0 hy1 hy2 hy3 hcenter5 hsem hk ⊢
    omega

theorem soundness (a b A T x : Fin 4 → ℤ) (P : Fin 7 → ℤ) (Y : Fin 4 → ℤ) (r v : ℤ)
    (ha : ∀ i, Limb (a i)) (hb : ∀ i, Limb (b i)) (hA : ∀ i, Limb (A i))
    (hT : ∀ i, Limb (T i)) (hx : ∀ i, Limb (x i))
    (hP : ProductBounds P) (hY : TailBounds Y)
    (hr : 0 ≤ r ∧ r < 2^68) (hv : 0 ≤ v ∧ v < 2^99)
    (hlo : ((low P Y-(R-c)*(r+sum a b x-quotientOffset)-
      R*(v+carryShift a b A T x-carryOffset) : ℤ) : ZMod nativePrime) = 0)
    (hhi : ((high P Y-(R-1)*(r+sum a b x-quotientOffset)+
      (v+carryShift a b A T x-carryOffset) : ℤ) : ZMod nativePrime) = 0) :
    low P Y+R*high P Y = q*(r+sum a b x-quotientOffset) := by
  have ha0 := ha 0; have ha1 := ha 1; have ha2 := ha 2; have ha3 := ha 3
  have hb0 := hb 0; have hb1 := hb 1; have hb2 := hb 2; have hb3 := hb 3
  have hA2 := hA 2; have hA3 := hA 3; have hT2 := hT 2; have hT3 := hT 3
  have hx0 := hx 0; have hx1 := hx 1; have hx2 := hx 2; have hx3 := hx 3
  have hp0 := hP 0; have hp1 := hP 1; have hp2 := hP 2; have hp3 := hP 3
  have hp4 := hP 4; have hp5 := hP 5; have hp6 := hP 6
  have hy0 := hY 0; have hy1 := hY 1; have hy2 := hY 2; have hy3 := hY 3
  have hE0 : low P Y-(R-c)*(r+sum a b x-quotientOffset)-
      R*(v+carryShift a b A T x-carryOffset) = 0 := by
    apply zero_of_native_zero hlo
    all_goals
      norm_num [low, high, off0, off1, off3, sum, Narrow.sum, quotientOffset, carryShift,
        halfC, delta, carryOffset, nativePrime, R, q, Limb, B, c, D] at   hp0 hp1 hp2 hp3 hp4 hp5 hp6 hy0 hy1 hy2 hy3 ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hA2 hA3 hT2 hT3 hx0 hx1 hx2 hx3 hr hv ⊢
      omega
  have hE1 : high P Y-(R-1)*(r+sum a b x-quotientOffset)+
      (v+carryShift a b A T x-carryOffset) = 0 := by
    apply zero_of_native_zero hhi
    all_goals
      norm_num [low, high, off0, off1, off3, sum, Narrow.sum, quotientOffset, carryShift,
        halfC, delta, carryOffset, nativePrime, R, q, Limb, B, c, D] at   hp0 hp1 hp2 hp3 hp4 hp5 hp6 hy0 hy1 hy2 hy3 ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hA2 hA3 hT2 hT3 hx0 hx1 hx2 hx3 hr hv ⊢
      omega
  have hq : q = R^2-c := by dsimp [q, R]; ring
  rw [hq]
  linear_combination hE0+R*hE1

end Wide
end Solution.Secp256k1ScalarMulFixedBase.AffineRangeBounds

end DonorFile3_3

-- Adapted donor module: AffineNarrow
section DonorFile3_4

namespace Solution.Secp256k1ScalarMulFixedBase.AffineNarrow

open AffineRangeBounds
open Challenge.CostR1CS Cost

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

/-- `products` contains existing convolution expressions used only by the contract.
The two emitted range checks read the retained folded witnesses and limb wires. -/
structure Inputs (F : Type) where
  lam : Emu F
  x : Emu F
  a : Emu F
  b : Emu F
  products : Vector F 7
  folded : Vector F 4
deriving ProvableStruct

def limbs (input : Inputs (F circomPrime)) (i : Fin 4) : ℤ := input.lam[i].val
def products (input : Inputs (F circomPrime)) (i : Fin 7) : ℤ := input.products[i].val
def tails (input : Inputs (F circomPrime)) (i : Fin 4) : ℤ :=
  (input.x[i].val : ℤ) + input.a[i].val + input.b[i].val

def folded (P : Fin 7 → ℤ) (i : Fin 4) : ℤ :=
  P ⟨i.val, by omega⟩ + if h : i.val < 3 then c*P ⟨i.val+4, by omega⟩ else 0

def Assumptions (input : Inputs (F circomPrime)) : Prop :=
  (∀ i, Limb (limbs input i)) ∧ Narrow.ProductBounds (products input) ∧
  Narrow.TailBounds (tails input) ∧
  products input 3 = 2*limbs input 0*limbs input 3 + 2*limbs input 1*limbs input 2 ∧
  products input 5 = 2*limbs input 2*limbs input 3 ∧
  ∀ i, input.folded[i] = ((folded (products input) i : ℤ) : F circomPrime)

def Spec (input : Inputs (F circomPrime)) : Prop :=
  q ∣ Narrow.low (products input) (tails input) + R*Narrow.high (products input) (tails input)

def lowValue (input : Inputs (F circomPrime)) : F circomPrime :=
  input.folded[0] + ((B-4*c : ℤ) : F circomPrime) - (input.x[0]+input.a[0]+input.b[0]) +
    (B : F circomPrime) * (input.folded[1] + (D : F circomPrime) - (input.x[1]+input.a[1]+input.b[1]))
def highValue (input : Inputs (F circomPrime)) : F circomPrime :=
  input.folded[2] + (D : F circomPrime) - (input.x[2]+input.a[2]+input.b[2]) +
    (B : F circomPrime) * (input.folded[3] + ((4*B-1 : ℤ) : F circomPrime) - (input.x[3]+input.a[3]+input.b[3]))
def quotientValue (input : Inputs (F circomPrime)) : F circomPrime :=
  (q : F circomPrime)⁻¹ * (lowValue input + (R : F circomPrime)*highValue input)
def carryValue (input : Inputs (F circomPrime)) : F circomPrime :=
  (R : F circomPrime)⁻¹ * (lowValue input - ((R-c : ℤ) : F circomPrime)*quotientValue input)
def rValue (input : Inputs (F circomPrime)) : F circomPrime :=
  quotientValue input - (input.lam[0]+input.lam[1]+input.lam[2]+input.lam[3]) +
    (Narrow.quotientOffset : F circomPrime)
def vValue (input : Inputs (F circomPrime)) : F circomPrime :=
  carryValue input - (c : F circomPrime)*(input.lam[2]+input.lam[3]) +
    (Narrow.carryOffset : F circomPrime)

def lowExpr (input : Var Inputs (F circomPrime)) : Expression (F circomPrime) :=
  input.folded[0] + (((B-4*c : ℤ) : F circomPrime) : Expression (F circomPrime)) -
    (input.x[0]+input.a[0]+input.b[0]) +
    (B : F circomPrime) * (input.folded[1] + (D : F circomPrime) - (input.x[1]+input.a[1]+input.b[1]))
def highExpr (input : Var Inputs (F circomPrime)) : Expression (F circomPrime) :=
  input.folded[2] + (D : F circomPrime) - (input.x[2]+input.a[2]+input.b[2]) +
    (B : F circomPrime) * (input.folded[3] + ((4*B-1 : ℤ) : F circomPrime) - (input.x[3]+input.a[3]+input.b[3]))
def quotientExpr (input : Var Inputs (F circomPrime)) : Expression (F circomPrime) :=
  (q : F circomPrime)⁻¹ * (lowExpr input + (R : F circomPrime)*highExpr input)
def carryExpr (input : Var Inputs (F circomPrime)) : Expression (F circomPrime) :=
  (R : F circomPrime)⁻¹ * (lowExpr input - ((R-c : ℤ) : F circomPrime)*quotientExpr input)
def rExpr (input : Var Inputs (F circomPrime)) : Expression (F circomPrime) :=
  quotientExpr input - (input.lam[0]+input.lam[1]+input.lam[2]+input.lam[3]) +
    (Narrow.quotientOffset : F circomPrime)
def vExpr (input : Var Inputs (F circomPrime)) : Expression (F circomPrime) :=
  carryExpr input - (c : F circomPrime)*(input.lam[2]+input.lam[3]) +
    (Narrow.carryOffset : F circomPrime)

def main (input : Var Inputs (F circomPrime)) : Circuit (F circomPrime) Unit := do
  assertion (RangeCheck.circuit 66 (by decide) (by decide)) (rExpr input)
  assertion (RangeCheck.circuit 97 (by decide) (by decide)) (vExpr input)

instance elaborated : ElaboratedCircuit (F circomPrime) Inputs unit main := by
  elaborate_circuit

lemma low_cast (input : Inputs (F circomPrime)) (h : Assumptions input) :
    lowValue input = ((Narrow.low (products input) (tails input) : ℤ) : F circomPrime) := by
  have h0 : input.folded[0] = ((products input 0 + c*products input 4 : ℤ) : F circomPrime) := h.2.2.2.2.2 0
  have h1 : input.folded[1] = ((products input 1 + c*products input 5 : ℤ) : F circomPrime) := h.2.2.2.2.2 1
  rw [lowValue, h0, h1]
  simp only [Narrow.low, tails, Fin.getElem_fin, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Int.cast_add, Int.cast_sub, Int.cast_mul,
    Int.cast_natCast, FoldQuot.natCast_val_F]

lemma high_cast (input : Inputs (F circomPrime)) (h : Assumptions input) :
    highValue input = ((Narrow.high (products input) (tails input) : ℤ) : F circomPrime) := by
  have h2 : input.folded[2] = ((products input 2 + c*products input 6 : ℤ) : F circomPrime) := h.2.2.2.2.2 2
  have h3 : input.folded[3] = ((products input 3 : ℤ) : F circomPrime) := by
    simpa [folded] using h.2.2.2.2.2 3
  rw [highValue, h2, h3]
  simp only [Narrow.high, tails, Fin.getElem_fin, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Int.cast_add, Int.cast_sub, Int.cast_mul,
    Int.cast_natCast, FoldQuot.natCast_val_F]

lemma quotient_ne_zero : (q : F circomPrime) ≠ 0 := by decide
lemma radix_ne_zero : (R : F circomPrime) ≠ 0 := by decide

lemma native_residuals (input : Inputs (F circomPrime)) :
    lowValue input - ((R-c : ℤ) : F circomPrime)*quotientValue input -
      (R : F circomPrime)*carryValue input = 0 ∧
    highValue input - ((R-1 : ℤ) : F circomPrime)*quotientValue input + carryValue input = 0 := by
  have hq : (q : F circomPrime) = (R : F circomPrime)^2 - (c : F circomPrime) := by
    norm_num [q, R, B, c]
  have hl : lowValue input - ((R-c : ℤ) : F circomPrime)*quotientValue input -
      (R : F circomPrime)*carryValue input = 0 := by
    unfold carryValue
    rw [← mul_assoc, mul_inv_cancel₀ radix_ne_zero, one_mul, sub_self]
  refine ⟨hl, ?_⟩
  have hf : lowValue input + (R : F circomPrime)*highValue input =
      (q : F circomPrime)*quotientValue input := by
    unfold quotientValue
    rw [← mul_assoc, mul_inv_cancel₀ quotient_ne_zero, one_mul]
  have he : (R : F circomPrime) *
      (highValue input - ((R-1 : ℤ) : F circomPrime)*quotientValue input + carryValue input) = 0 := by
    rw [hq] at hf
    push_cast at hl ⊢
    linear_combination hf - hl
  exact (mul_eq_zero.mp he).resolve_left radix_ne_zero

lemma decoded_casts (input : Inputs (F circomPrime)) :
    (((rValue input).val + Narrow.sum (limbs input) - Narrow.quotientOffset : ℤ) : F circomPrime) = quotientValue input ∧
    (((vValue input).val + Narrow.carryShift (limbs input) - Narrow.carryOffset : ℤ) : F circomPrime) = carryValue input := by
  simp only [Narrow.sum, Narrow.carryShift, limbs, Fin.getElem_fin, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Int.cast_sub, Int.cast_add,
    Int.cast_mul, Int.cast_natCast, FoldQuot.natCast_val_F, rValue, vValue]
  constructor <;> ring

theorem soundness_values (input : Inputs (F circomPrime)) (h : Assumptions input)
    (hr : (rValue input).val < 2^66) (hv : (vValue input).val < 2^97) : Spec input := by
  have hlow := low_cast input h
  have hhigh := high_cast input h
  have hnative := native_residuals input
  have hdecode := decoded_casts input
  have hlo : ((Narrow.low (products input) (tails input) -
      (R-c)*((rValue input).val + Narrow.sum (limbs input) - Narrow.quotientOffset) -
      R*((vValue input).val + Narrow.carryShift (limbs input) - Narrow.carryOffset) : ℤ) :
      ZMod nativePrime) = 0 := by
    change (_ : F circomPrime) = 0
    push_cast
    rw [hlow, ← hdecode.1, ← hdecode.2] at hnative
    push_cast at hnative
    exact hnative.1
  have hhi : ((Narrow.high (products input) (tails input) -
      (R-1)*((rValue input).val + Narrow.sum (limbs input) - Narrow.quotientOffset) +
      ((vValue input).val + Narrow.carryShift (limbs input) - Narrow.carryOffset) : ℤ) :
      ZMod nativePrime) = 0 := by
    change (_ : F circomPrime) = 0
    push_cast
    rw [hhigh, ← hdecode.1, ← hdecode.2] at hnative
    push_cast at hnative
    exact hnative.2
  have he := Narrow.soundness (limbs input) (products input) (tails input)
    (rValue input).val (vValue input).val h.1 h.2.1 h.2.2.1
    ⟨by omega, by exact_mod_cast hr⟩ ⟨by omega, by exact_mod_cast hv⟩ hlo hhi
  exact ⟨_, he⟩

lemma honest_native_values (input : Inputs (F circomPrime)) (h : Assumptions input) (k : ℤ)
    (hk : Narrow.low (products input) (tails input) + R*Narrow.high (products input) (tails input) = q*k) :
    quotientValue input = (k : F circomPrime) ∧
    carryValue input = (((R-1)*k - Narrow.high (products input) (tails input) : ℤ) : F circomPrime) := by
  have hf := congrArg (fun z : ℤ => (z : F circomPrime)) hk
  push_cast at hf
  have hqv : quotientValue input = (k : F circomPrime) := by
    rw [quotientValue, low_cast input h, high_cast input h, hf,
      ← mul_assoc, inv_mul_cancel₀ quotient_ne_zero, one_mul]
  refine ⟨hqv, ?_⟩
  have hn := (native_residuals input).2
  rw [hqv, high_cast input h] at hn
  push_cast at hn ⊢
  linear_combination hn

lemma range_of_int (n : ℕ) (z : ℤ) (hz : 0 ≤ z ∧ z < 2^n)
    (hn : (2 : ℕ)^n < circomPrime) : (z : F circomPrime).val < 2^n := by
  have hzn : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hz.1
  have hzlt : z.toNat < 2^n := by exact_mod_cast (show (z.toNat : ℤ) < 2^n by omega)
  have hcast := congrArg (fun a : ℤ => (a : F circomPrime)) hzn
  simp only [Int.cast_natCast] at hcast
  rw [← hcast, ZMod.val_natCast_of_lt (lt_trans hzlt hn)]
  exact hzlt

theorem completeness_values (input : Inputs (F circomPrime)) (h : Assumptions input)
    (hs : Spec input) : (rValue input).val < 2^66 ∧ (vValue input).val < 2^97 := by
  obtain ⟨k, hk⟩ := hs
  have hb := Narrow.completeness (limbs input) (products input) (tails input) k
    h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 hk
  have hn := honest_native_values input h k hk
  have hr : rValue input = ((k - Narrow.sum (limbs input) + Narrow.quotientOffset : ℤ) : F circomPrime) := by
    simp only [rValue, hn.1, Narrow.sum, limbs, Fin.getElem_fin, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Int.cast_sub, Int.cast_add,
      Int.cast_natCast, FoldQuot.natCast_val_F]
  have hv : vValue input = (((R-1)*k - Narrow.high (products input) (tails input) -
      Narrow.carryShift (limbs input) + Narrow.carryOffset : ℤ) : F circomPrime) := by
    simp only [vValue, hn.2, Narrow.carryShift, limbs, Fin.getElem_fin, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Int.cast_sub, Int.cast_add,
      Int.cast_mul, Int.cast_natCast, FoldQuot.natCast_val_F]
  constructor
  · rw [hr]
    exact range_of_int 66 _ hb.2.1 (by decide)
  · rw [hv]
    exact range_of_int 97 _ hb.2.2 (by decide)

lemma eval_rExpr (env : Environment (F circomPrime)) (input : Var Inputs (F circomPrime)) :
    Expression.eval env (rExpr input) = rValue (eval env input) := by
  simp only [rExpr, quotientExpr, lowExpr, highExpr, rValue, quotientValue, lowValue, highValue,
    circuit_norm, sub_eq_add_neg]

lemma eval_vExpr (env : Environment (F circomPrime)) (input : Var Inputs (F circomPrime)) :
    Expression.eval env (vExpr input) = vValue (eval env input) := by
  simp only [vExpr, carryExpr, quotientExpr, lowExpr, highExpr, vValue, carryValue,
    quotientValue, lowValue, highValue, circuit_norm, sub_eq_add_neg]

theorem soundness : FormalAssertion.Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start_core
  have hr := eval_rExpr env input_var
  have hv := eval_vExpr env input_var
  rw [h_input] at hr hv
  simp only [main, circuit_norm, RangeCheck.circuit, RangeCheck.Assumptions, RangeCheck.Spec] at h_holds ⊢
  exact soundness_values input h_assumptions (by simpa only [hr] using h_holds.1)
    (by simpa only [hv] using h_holds.2)

theorem completeness : FormalAssertion.Completeness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start_core
  have hr := eval_rExpr env.toEnvironment input_var
  have hv := eval_vExpr env.toEnvironment input_var
  have hi : eval env.toEnvironment input_var = input := by simpa only [circuit_norm] using h_input
  rw [hi] at hr hv
  have hb := completeness_values input h_assumptions h_spec
  simp only [main, circuit_norm, RangeCheck.circuit, RangeCheck.Assumptions, RangeCheck.Spec]
  exact ⟨by simpa only [hr] using hb.1, by simpa only [hv] using hb.2⟩

def circuit : FormalAssertion (F circomPrime) Inputs where
  main; elaborated; Assumptions; Spec; soundness; completeness

theorem costIs_main (input : Var Inputs (F circomPrime)) :
    CostIs (main input) ⟨161, 163⟩ := by
  rw [show (⟨161, 163⟩ : Count) = ⟨65, 66⟩ + ⟨96, 97⟩ by decide]
  unfold main
  refine CostIs.bind (costIs_assertion_implicitRangeCheck 66 (by decide) (by decide) _) fun _ => ?_
  exact costIs_assertion_implicitRangeCheck 97 (by decide) (by decide) _

lemma affine_low {i : Var Inputs (F circomPrime)}
    (hx : AffineW i.x) (ha : AffineW i.a) (hb : AffineW i.b) (hf : AffineW i.folded) :
    Affine (lowExpr i) := by
  unfold lowExpr
  exact Affine.add
    (Affine.sub (Affine.add (hf 0 (by decide)) (Affine.const _))
      (Affine.add (Affine.add (hx 0 (by decide)) (ha 0 (by decide))) (hb 0 (by decide))))
    (Affine.fconst_mul _ (Affine.sub (Affine.add (hf 1 (by decide)) (Affine.const _))
      (Affine.add (Affine.add (hx 1 (by decide)) (ha 1 (by decide))) (hb 1 (by decide)))))

lemma affine_high {i : Var Inputs (F circomPrime)}
    (hx : AffineW i.x) (ha : AffineW i.a) (hb : AffineW i.b) (hf : AffineW i.folded) :
    Affine (highExpr i) := by
  unfold highExpr
  exact Affine.add
    (Affine.sub (Affine.add (hf 2 (by decide)) (Affine.const _))
      (Affine.add (Affine.add (hx 2 (by decide)) (ha 2 (by decide))) (hb 2 (by decide))))
    (Affine.fconst_mul _ (Affine.sub (Affine.add (hf 3 (by decide)) (Affine.const _))
      (Affine.add (Affine.add (hx 3 (by decide)) (ha 3 (by decide))) (hb 3 (by decide)))))

lemma affine_quotient {i : Var Inputs (F circomPrime)}
    (hx : AffineW i.x) (ha : AffineW i.a) (hb : AffineW i.b) (hf : AffineW i.folded) :
    Affine (quotientExpr i) :=
  Affine.fconst_mul _ (Affine.add (affine_low hx ha hb hf)
    (Affine.fconst_mul _ (affine_high hx ha hb hf)))

lemma affine_carry {i : Var Inputs (F circomPrime)}
    (hx : AffineW i.x) (ha : AffineW i.a) (hb : AffineW i.b) (hf : AffineW i.folded) :
    Affine (carryExpr i) :=
  Affine.fconst_mul _ (Affine.sub (affine_low hx ha hb hf)
    (Affine.fconst_mul _ (affine_quotient hx ha hb hf)))

lemma affine_r {i : Var Inputs (F circomPrime)}
    (hl : AffineW i.lam) (hx : AffineW i.x) (ha : AffineW i.a)
    (hb : AffineW i.b) (hf : AffineW i.folded) : Affine (rExpr i) :=
  Affine.add (Affine.sub (affine_quotient hx ha hb hf)
    (Affine.add (Affine.add (Affine.add (hl 0 (by decide)) (hl 1 (by decide)))
      (hl 2 (by decide))) (hl 3 (by decide)))) (Affine.const _)

lemma affine_v {i : Var Inputs (F circomPrime)}
    (hl : AffineW i.lam) (hx : AffineW i.x) (ha : AffineW i.a)
    (hb : AffineW i.b) (hf : AffineW i.folded) : Affine (vExpr i) :=
  Affine.add (Affine.sub (affine_carry hx ha hb hf)
    (Affine.fconst_mul _ (Affine.add (hl 2 (by decide)) (hl 3 (by decide))))) (Affine.const _)

lemma shape (i : Var Inputs (F circomPrime))
    (hl : AffineW i.lam) (hx : AffineW i.x) (ha : AffineW i.a)
    (hb : AffineW i.b) (hf : AffineW i.folded) : IsR1CSCirc (main i) := by
  unfold main
  refine IsR1CSCirc.bind (isR1CS_assertion_implicitRangeCheck 66 (by decide) (by decide) _
    (affine_r hl hx ha hb hf)) fun _ => ?_
  exact isR1CS_assertion_implicitRangeCheck 97 (by decide) (by decide) _ (affine_v hl hx ha hb hf)

end Solution.Secp256k1ScalarMulFixedBase.AffineNarrow

end DonorFile3_4

-- Adapted donor module: GroupLaw
section DonorFile3_5

namespace Solution.Secp256k1ScalarMulFixedBase.GroupLaw

open Specs.ShortWeierstrass Specs.Secp256k1
open WeierstrassCurve.Affine

noncomputable section

def W : WeierstrassCurve Fp where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := 0
  a₆ := 7

lemma W_a₁ : W.a₁ = 0 := rfl
lemma W_a₂ : W.a₂ = 0 := rfl
lemma W_a₃ : W.a₃ = 0 := rfl
lemma W_a₄ : W.a₄ = 0 := rfl
lemma W_a₆ : W.a₆ = (7 : Fp) := rfl

lemma hΔ : W.Δ ≠ 0 := by
  have hcast : ((21168 : ℕ) : Fp) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hdvd
    exact absurd (Nat.le_of_dvd (by norm_num) hdvd) (by norm_num [p])
  have hΔeq : W.Δ = -((21168 : ℕ) : Fp) := by
    simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈, W_a₁, W_a₂, W_a₃, W_a₄, W_a₆]
    push_cast
    ring
  rw [hΔeq, neg_ne_zero]
  exact hcast

lemma negY_eq (x y : Fp) : negY W x y = -y := by
  simp only [negY, W_a₁, W_a₃]
  ring

lemma equation_iff_onCurve {x y : Fp} : Equation W x y ↔ OnCurve curve ⟨x, y⟩ := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [W_a₁, W_a₂, W_a₃, W_a₄, W_a₆, OnCurve, curve]
  constructor <;> intro h <;> linear_combination h

lemma nonsingular_of_onCurve {x y : Fp} (h : OnCurve curve ⟨x, y⟩) : Nonsingular W x y :=
  (equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp (equation_iff_onCurve.mpr h)

lemma onCurve_of_nonsingular {x y : Fp} (h : Nonsingular W x y) : OnCurve curve ⟨x, y⟩ :=
  equation_iff_onCurve.mp h.left

def toW : (P : GroupPoint Fp) → OnCurveOrInfinity curve P → Point W
  | .infinity, _ => 0
  | .affine ⟨x, y⟩, h => .some (nonsingular_of_onCurve h)

def fromW : Point W → GroupPoint Fp
  | 0 => .infinity
  | @WeierstrassCurve.Affine.Point.some _ _ _ x y _ => .affine ⟨x, y⟩

@[simp] lemma fromW_zero : fromW (0 : Point W) = .infinity := rfl

lemma fromW_onCurve (p : Point W) : OnCurveOrInfinity curve (fromW p) := by
  cases p with
  | zero => trivial
  | some h => exact onCurve_of_nonsingular h

lemma fromW_toW (P : GroupPoint Fp) (h : OnCurveOrInfinity curve P) : fromW (toW P h) = P := by
  cases P with
  | infinity => simp only [toW, fromW]
  | affine Q => cases Q; simp only [toW, fromW]

lemma toW_fromW (p : Point W) : toW (fromW p) (fromW_onCurve p) = p := by
  cases p with
  | zero => rfl
  | some h => rfl

lemma toW_congr {P P' : GroupPoint Fp} (h : OnCurveOrInfinity curve P)
    (h' : OnCurveOrInfinity curve P') (e : P = P') : toW P h = toW P' h' := by
  subst e; rfl

def specNeg : GroupPoint Fp → GroupPoint Fp
  | .infinity => .infinity
  | .affine P => .affine ⟨P.x, -P.y⟩

lemma fromW_neg (p : Point W) : fromW (-p) = specNeg (fromW p) := by
  cases p with
  | zero => rfl
  | some h =>
      show GroupPoint.affine ⟨_, negY W _ _⟩ = GroupPoint.affine ⟨_, -_⟩
      rw [negY_eq]

lemma fromW_add (p q : Point W) : fromW (p + q) = add curve (fromW p) (fromW q) := by
  rcases p with _ | @⟨x₁, y₁, h₁⟩ <;> rcases q with _ | @⟨x₂, y₂, h₂⟩
  · rfl
  · rfl
  · rfl
  ·
    show fromW (Point.some h₁ + Point.some h₂)
        = add curve (.affine ⟨x₁, y₁⟩) (.affine ⟨x₂, y₂⟩)
    by_cases hx : x₁ = x₂
    · by_cases hy : y₁ = -y₂
      ·
        have hy' : y₁ = negY W x₂ y₂ := by rw [negY_eq]; exact hy
        rw [Point.add_of_Y_eq hx hy']
        show GroupPoint.infinity
            = (if x₁ = x₂ then (if y₁ = -y₂ then GroupPoint.infinity
                else .affine (tangent curve ⟨x₁, y₁⟩)) else .affine (chord ⟨x₁, y₁⟩ ⟨x₂, y₂⟩))
        rw [if_pos hx, if_pos hy]
      ·
        have hy' : y₁ ≠ negY W x₂ y₂ := by rw [negY_eq]; exact hy
        rw [Point.add_of_Y_ne hy']
        show GroupPoint.affine ⟨addX W x₁ x₂ (slope W x₁ x₂ y₁ y₂),
              addY W x₁ x₂ y₁ (slope W x₁ x₂ y₁ y₂)⟩
            = (if x₁ = x₂ then (if y₁ = -y₂ then GroupPoint.infinity
              else .affine (tangent curve ⟨x₁, y₁⟩)) else .affine (chord ⟨x₁, y₁⟩ ⟨x₂, y₂⟩))
        rw [if_pos hx, if_neg hy]
        subst hx
        have hℓ : slope W x₁ x₁ y₁ y₂ = (3 * x₁ ^ 2 + curve.a) / (2 * y₁) := by
          rw [slope_of_Y_ne rfl hy', negY_eq]
          simp only [W_a₁, W_a₂, W_a₄, curve]
          rw [show y₁ - -y₁ = 2 * y₁ by ring]
          ring
        rw [hℓ]
        simp only [addX, addY, negAddY, negY_eq, W_a₁, W_a₂, tangent, curve,
          GroupPoint.affine.injEq, Point.mk.injEq]
        constructor <;> ring
    ·
      rw [Point.add_of_X_ne hx]
      show GroupPoint.affine ⟨addX W x₁ x₂ (slope W x₁ x₂ y₁ y₂),
            addY W x₁ x₂ y₁ (slope W x₁ x₂ y₁ y₂)⟩
          = (if x₁ = x₂ then (if y₁ = -y₂ then GroupPoint.infinity
            else .affine (tangent curve ⟨x₁, y₁⟩)) else .affine (chord ⟨x₁, y₁⟩ ⟨x₂, y₂⟩))
      rw [if_neg hx]
      have hℓ : slope W x₁ x₂ y₁ y₂ = (y₂ - y₁) / (x₂ - x₁) := by
        rw [slope_of_X_ne hx]
        rw [div_eq_div_iff (sub_ne_zero.mpr hx) (sub_ne_zero.mpr (Ne.symm hx))]
        ring
      rw [hℓ]
      simp only [addX, addY, negAddY, negY_eq, W_a₁, W_a₂, chord,
        GroupPoint.affine.injEq, Point.mk.injEq]
      constructor <;> ring

lemma add_eq {P Q : GroupPoint Fp} (hP : OnCurveOrInfinity curve P)
    (hQ : OnCurveOrInfinity curve Q) :
    add curve P Q = fromW (toW P hP + toW Q hQ) := by
  rw [fromW_add, fromW_toW, fromW_toW]

lemma toW_add_eq {P Q : GroupPoint Fp} (hP : OnCurveOrInfinity curve P)
    (hQ : OnCurveOrInfinity curve Q) (h : OnCurveOrInfinity curve (add curve P Q)) :
    toW (add curve P Q) h = toW P hP + toW Q hQ := by
  rw [toW_congr h (fromW_onCurve _) (add_eq hP hQ)]
  exact toW_fromW _

theorem add_comm' {P Q : GroupPoint Fp} (hP : OnCurveOrInfinity curve P)
    (hQ : OnCurveOrInfinity curve Q) :
    add curve P Q = add curve Q P := by
  rw [add_eq hP hQ, add_eq hQ hP, add_comm]

theorem add_assoc' {P Q R : GroupPoint Fp} (hP : OnCurveOrInfinity curve P)
    (hQ : OnCurveOrInfinity curve Q) (hR : OnCurveOrInfinity curve R) :
    add curve (add curve P Q) R = add curve P (add curve Q R) := by
  have hPQ : OnCurveOrInfinity curve (add curve P Q) := by
    rw [add_eq hP hQ]; exact fromW_onCurve _
  have hQR : OnCurveOrInfinity curve (add curve Q R) := by
    rw [add_eq hQ hR]; exact fromW_onCurve _
  rw [add_eq hPQ hR, add_eq hP hQR]
  congr 1
  rw [toW_add_eq hP hQ, toW_add_eq hQ hR, add_assoc]

def nsmulSpec : ℕ → GroupPoint Fp → GroupPoint Fp
  | 0, _ => .infinity
  | (n + 1), P => add curve (nsmulSpec n P) P

def zsmul : ℤ → GroupPoint Fp → GroupPoint Fp
  | .ofNat n, P => nsmulSpec n P
  | .negSucc n, P => specNeg (nsmulSpec (n + 1) P)

lemma nsmulSpec_eq {P : GroupPoint Fp} (h : OnCurveOrInfinity curve P) (n : ℕ) :
    nsmulSpec n P = fromW (n • toW P h) := by
  induction n with
  | zero => simp [nsmulSpec]
  | succ k ih =>
      rw [nsmulSpec, ih, succ_nsmul, fromW_add, fromW_toW]

lemma zsmul_eq {P : GroupPoint Fp} (h : OnCurveOrInfinity curve P) (n : ℤ) :
    zsmul n P = fromW (n • toW P h) := by
  cases n with
  | ofNat k =>
      show nsmulSpec k P = fromW ((k : ℤ) • toW P h)
      rw [nsmulSpec_eq h k, natCast_zsmul]
  | negSucc k =>
      show specNeg (nsmulSpec (k + 1) P) = fromW (Int.negSucc k • toW P h)
      rw [nsmulSpec_eq h (k + 1), negSucc_zsmul, fromW_neg]

theorem zsmul_onCurveOrInfinity {P : GroupPoint Fp} (h : OnCurveOrInfinity curve P) (n : ℤ) :
    OnCurveOrInfinity curve (zsmul n P) := by
  rw [zsmul_eq h]; exact fromW_onCurve _

theorem zsmul_add {P : GroupPoint Fp} (h : OnCurveOrInfinity curve P) (a b : ℤ) :
    zsmul (a + b) P = add curve (zsmul a P) (zsmul b P) := by
  rw [zsmul_eq h, zsmul_eq h, zsmul_eq h, add_zsmul, fromW_add]

lemma zsmul_one_affine (P : Point Fp) (h : OnCurve curve P) :
    zsmul 1 (.affine P) = .affine P := by
  rw [zsmul_eq (P := .affine P) h, one_zsmul, fromW_toW]

lemma zsmul_zero_affine (P : Point Fp) (h : OnCurve curve P) :
    zsmul 0 (.affine P) = .infinity := by
  rw [zsmul_eq (P := .affine P) h, zero_zsmul]; rfl

lemma fromW_eq_infinity_iff (p : Point W) : fromW p = .infinity ↔ p = 0 := by
  cases p with
  | zero => exact iff_of_true rfl rfl
  | some h =>
      constructor
      · intro hc; exact absurd hc (by simp [fromW])
      · intro hc; exact absurd hc (Point.some_ne_zero h)

def horner (a : ℤ) (b : ℕ) : ℤ := 2 * a + (b : ℤ)

lemma foldl_cast (l : List ℕ) (s : ℕ) :
    l.foldl horner (s : ℤ) = ((l.foldl (fun a b => 2 * a + b) s : ℕ) : ℤ) := by
  induction l generalizing s with
  | nil => rfl
  | cons b t ih =>
      simp only [List.foldl_cons, horner]
      rw [show (2 * (s : ℤ) + (b : ℤ)) = ((2 * s + b : ℕ) : ℤ) by push_cast; ring]
      exact ih (2 * s + b)

lemma foldl_step_eq (P : Point Fp) (hP : OnCurve curve P) :
    ∀ (l : List ℕ), (∀ b ∈ l, b < 2) → ∀ (s : ℤ) (acc : GroupPoint Fp),
      acc = zsmul s (.affine P) →
      l.foldl (step curve P) acc
        = zsmul (l.foldl horner s) (.affine P) := by
  have hPI : OnCurveOrInfinity curve (.affine P) := hP
  intro l
  induction l with
  | nil => intro _ s acc hacc; simpa using hacc
  | cons b t ih =>
      intro hb s acc hacc
      simp only [List.foldl_cons]
      have hb2 : b < 2 := hb b (List.mem_cons_self ..)
      have htail : ∀ b' ∈ t, b' < 2 := fun b' hb' => hb b' (List.mem_cons_of_mem _ hb')
      have hdb : add curve (zsmul s (.affine P)) (zsmul s (.affine P))
          = zsmul (s + s) (.affine P) := (zsmul_add hPI s s).symm
      have hstep : step curve P acc b = zsmul (horner s b) (.affine P) := by
        subst hacc
        simp only [step]
        by_cases hb1 : b = 1
        · subst hb1
          rw [if_pos rfl, hdb]
          have hcalc : add curve (zsmul (s + s) (.affine P)) (.affine P)
              = zsmul (s + s + 1) (.affine P) := by
            nth_rewrite 2 [← zsmul_one_affine P hP]
            rw [← zsmul_add hPI (s + s) 1]
          rw [hcalc]; congr 1; simp only [horner]; push_cast; ring
        · rw [if_neg hb1, hdb]
          have hz : b = 0 := by omega
          subst hz; congr 1; simp only [horner]; push_cast; ring
      rw [ih htail (horner s b) _ hstep]

theorem scalarMul_eq_zsmul {n : ℕ} (bits : Vector ℕ n) (P : Point Fp)
    (hbits : IsBitArray bits) (hP : OnCurve curve P) :
    scalarMul curve bits P = zsmul ((scalarOfBits bits : ℕ) : ℤ) (.affine P) := by
  have hbl : ∀ b ∈ bits.toList, b < 2 := by
    intro b hb
    rw [List.mem_iff_getElem] at hb
    obtain ⟨i, hi, rfl⟩ := hb
    rw [Vector.length_toList] at hi
    have := hbits ⟨i, hi⟩
    simpa [Vector.getElem_toList] using this
  have hfold : bits.foldl (step curve P) .infinity
      = bits.toList.foldl (step curve P) .infinity := by
    rcases bits with ⟨xs, hxs⟩
    simp [Vector.foldl_mk, Array.foldl_toList, Vector.toList]
  have hscalar : scalarOfBits bits = bits.toList.foldl (fun a b => 2 * a + b) 0 := by
    rw [scalarOfBits]
    rcases bits with ⟨xs, hxs⟩
    simp [Vector.foldl_mk, Array.foldl_toList, Vector.toList]
  rw [scalarMul, hfold]
  have hbase : (GroupPoint.infinity : GroupPoint Fp) = zsmul (((0 : ℕ) : ℤ)) (.affine P) :=
    (zsmul_zero_affine P hP).symm
  rw [foldl_step_eq P hP bits.toList hbl ((0 : ℕ) : ℤ) .infinity hbase]
  rw [foldl_cast bits.toList 0, hscalar]

end

end Solution.Secp256k1ScalarMulFixedBase.GroupLaw

end DonorFile3_5

-- Adapted donor module: TableReflect
section DonorFile3_6

namespace Solution.Secp256k1ScalarMulFixedBase.TableReflect

open Specs.ShortWeierstrass Specs.Secp256k1
open Solution.Secp256k1ScalarMulFixedBase.GroupLaw

set_option maxRecDepth 65536

theorem add_chord (x1 y1 x2 y2 s x3 y3 : Fp)
    (hx : x1 ≠ x2)
    (hs : s * (x2 - x1) = y2 - y1)
    (hx3 : x3 = s ^ 2 - x1 - x2)
    (hy3 : y3 = s * (x1 - x3) - y1) :
    add curve (.affine ⟨x1, y1⟩) (.affine ⟨x2, y2⟩) = .affine ⟨x3, y3⟩ := by
  show (if x1 = x2 then if y1 = -y2 then GroupPoint.infinity
      else .affine (tangent curve ⟨x1, y1⟩) else .affine (chord ⟨x1, y1⟩ ⟨x2, y2⟩))
      = .affine ⟨x3, y3⟩
  rw [if_neg hx]
  have hne : x2 - x1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  have hslope : (y2 - y1) / (x2 - x1) = s := by
    rw [div_eq_iff hne, hs]
  simp only [chord, hslope, GroupPoint.affine.injEq, Point.mk.injEq]
  subst hx3 hy3
  exact ⟨by ring, by ring⟩

theorem add_tangent (x1 y1 s x3 y3 : Fp)
    (hy : y1 ≠ -y1)
    (hs : s * (2 * y1) = 3 * x1 ^ 2)
    (hx3 : x3 = s ^ 2 - 2 * x1)
    (hy3 : y3 = s * (x1 - x3) - y1) :
    add curve (.affine ⟨x1, y1⟩) (.affine ⟨x1, y1⟩) = .affine ⟨x3, y3⟩ := by
  show (if x1 = x1 then if y1 = -y1 then GroupPoint.infinity
      else .affine (tangent curve ⟨x1, y1⟩) else .affine (chord ⟨x1, y1⟩ ⟨x1, y1⟩))
      = .affine ⟨x3, y3⟩
  rw [if_pos rfl, if_neg hy]
  have h2y : (2 : Fp) * y1 ≠ 0 := by
    intro hc
    apply hy
    have h0 : y1 + y1 = 0 := by linear_combination hc
    linear_combination h0
  have hslope : (3 * y1 * 0 + 3 * x1 ^ 2 + curve.a) / (2 * y1) = s := by
    rw [div_eq_iff h2y]
    show 3 * y1 * 0 + 3 * x1 ^ 2 + (0 : Fp) = s * (2 * y1)
    rw [hs]; ring
  have hslope' : (3 * x1 ^ 2 + curve.a) / (2 * y1) = s := by
    rw [← hslope]; ring_nf
  simp only [tangent, hslope', GroupPoint.affine.injEq, Point.mk.injEq]
  subst hx3 hy3
  exact ⟨by ring, by ring⟩

def cstep (qx : Fp) (p : Point Fp) (s : Fp) : Point Fp :=
  let x3 := s ^ 2 - p.x - qx
  ⟨x3, s * (p.x - x3) - p.y⟩

def cnth (qx : Fp) : Point Fp → List Fp → ℕ → Point Fp
  | p, _, 0 => p
  | p, [], _ + 1 => p
  | p, s :: rest, k + 1 => cnth qx (cstep qx p s) rest k

def cchecks (qx qy : Fp) : Point Fp → List Fp → Bool
  | _, [] => true
  | p, s :: rest =>
      (decide (p.x ≠ qx) && decide (s * (qx - p.x) = qy - p.y))
        && cchecks qx qy (cstep qx p s) rest

theorem chordChainOK {G : Point Fp} (hG : OnCurve curve G) {qx qy : Fp} {q : ℤ}
    (hQ : zsmul q (.affine G) = .affine ⟨qx, qy⟩) :
    ∀ (slopes : List Fp) (p : Point Fp) (a : ℤ),
      zsmul a (.affine G) = .affine p →
      cchecks qx qy p slopes = true →
      ∀ k, k ≤ slopes.length →
        zsmul (a + k * q) (.affine G) = .affine (cnth qx p slopes k) := by
  have hGI : OnCurveOrInfinity curve (.affine G) := hG
  intro slopes
  induction slopes with
  | nil =>
      intro p a hp _ k hk
      have hk0 : k = 0 := Nat.le_zero.mp hk
      subst hk0
      simpa using hp
  | cons s rest ih =>
      intro p a hp hchk k hk
      obtain ⟨hstep, hrest⟩ := Bool.and_eq_true _ _ |>.mp hchk
      obtain ⟨hne, hsl⟩ := Bool.and_eq_true _ _ |>.mp hstep
      have hne' : p.x ≠ qx := of_decide_eq_true hne
      have hsl' : s * (qx - p.x) = qy - p.y := of_decide_eq_true hsl

      have hp' : zsmul (a + q) (.affine G) = .affine (cstep qx p s) := by
        rw [zsmul_add hGI a q, hp, hQ]
        exact add_chord p.x p.y qx qy s _ _ hne' hsl' rfl rfl
      cases k with
      | zero => simpa using hp
      | succ m =>
          have hm : m ≤ rest.length := by
            simpa [List.length_cons] using Nat.succ_le_succ_iff.mp hk
          have := ih (cstep qx p s) (a + q) hp' hrest m hm
          rw [show a + (↑(m + 1)) * q = (a + q) + ↑m * q by push_cast; ring]
          simpa [cnth] using this

/-- Low 64-bit limb of the secp256k1 prime, i.e. `P256 % 2^64`. -/
def lowP : ℕ := 18446744069414583343

/-- Per-point certificate carried along a chord chain: the `y`-coordinate is
nonzero, *and* its low 64-bit limb does not exceed the low limb of the prime.
The second conjunct says exactly that the schoolbook subtraction `P256 - y`
produces no borrows, which is what lets the width-12 selector recover the
positive `y` limbs from the negated ones by a purely affine expression — no
borrow bits and no extra selected column.  Both facts are established in the
*same* traversal, so certifying them costs one chain walk, not two. -/
def yOK (y : Fp) : Bool :=
  decide (y ≠ 0) && decide (y.val % 18446744073709551616 ≤ lowP)

theorem yOK_elim {y : Fp} (h : yOK y = true) :
    y ≠ 0 ∧ y.val % 18446744073709551616 ≤ lowP := by
  obtain ⟨h1, h2⟩ := Bool.and_eq_true _ _ |>.mp h
  exact ⟨of_decide_eq_true h1, of_decide_eq_true h2⟩

def allYne0 (qx : Fp) : Point Fp → List Fp → Bool
  | p, [] => yOK p.y
  | p, s :: rest => yOK p.y && allYne0 qx (cstep qx p s) rest

def cchecksY (qx qy : Fp) : Point Fp → List Fp → Bool
  | p, [] => yOK p.y
  | p, s :: rest =>
      ((decide (p.x ≠ qx) && decide (s * (qx - p.x) = qy - p.y)) && yOK p.y) &&
        cchecksY qx qy (cstep qx p s) rest

theorem cchecksY_elim (qx qy : Fp) :
    ∀ (slopes : List Fp) (p : Point Fp), cchecksY qx qy p slopes = true →
      cchecks qx qy p slopes = true ∧ allYne0 qx p slopes = true := by
  intro slopes
  induction slopes with
  | nil =>
      intro p h
      exact ⟨rfl, h⟩
  | cons s rest ih =>
      intro p h
      simp only [cchecksY, Bool.and_eq_true] at h
      rcases h with ⟨⟨⟨hx, hs⟩, hy⟩, hrest⟩
      have hr := ih (cstep qx p s) hrest
      constructor
      · simp only [cchecks, Bool.and_eq_true]
        exact ⟨⟨hx, hs⟩, hr.1⟩
      · simp only [allYne0, Bool.and_eq_true]
        exact ⟨hy, hr.2⟩

theorem cnth_y_ne_zero (qx : Fp) :
    ∀ (slopes : List Fp) (p : Point Fp),
      allYne0 qx p slopes = true →
      ∀ k, k ≤ slopes.length →
        (cnth qx p slopes k).y ≠ 0 ∧
          (cnth qx p slopes k).y.val % 18446744073709551616 ≤ lowP := by
  intro slopes
  induction slopes with
  | nil =>
      intro p hchk k hk
      have hk0 : k = 0 := Nat.le_zero.mp hk
      subst hk0
      exact yOK_elim hchk
  | cons s rest ih =>
      intro p hchk k hk
      obtain ⟨hhead, htail⟩ := Bool.and_eq_true _ _ |>.mp hchk
      cases k with
      | zero => exact yOK_elim hhead
      | succ m =>
          have hm : m ≤ rest.length := by
            simpa [List.length_cons] using Nat.succ_le_succ_iff.mp hk
          simpa [cnth] using ih (cstep qx p s) htail m hm

def dstep (p : Point Fp) (s : Fp) : Point Fp :=
  let x3 := s ^ 2 - 2 * p.x
  ⟨x3, s * (p.x - x3) - p.y⟩

def dnth : Point Fp → List Fp → ℕ → Point Fp
  | p, _, 0 => p
  | p, [], _ + 1 => p
  | p, s :: rest, k + 1 => dnth (dstep p s) rest k

def dchecks : Point Fp → List Fp → Bool
  | _, [] => true
  | p, s :: rest =>
      (decide (p.y ≠ -p.y) && decide (s * (2 * p.y) = 3 * p.x ^ 2))
        && dchecks (dstep p s) rest

theorem dblChainOK {G : Point Fp} (hG : OnCurve curve G) :
    ∀ (slopes : List Fp) (p : Point Fp) (a : ℤ),
      zsmul a (.affine G) = .affine p →
      dchecks p slopes = true →
      ∀ k, k ≤ slopes.length →
        zsmul (2 ^ k * a) (.affine G) = .affine (dnth p slopes k) := by
  have hGI : OnCurveOrInfinity curve (.affine G) := hG
  intro slopes
  induction slopes with
  | nil =>
      intro p a hp _ k hk
      have hk0 : k = 0 := Nat.le_zero.mp hk
      subst hk0
      simpa using hp
  | cons s rest ih =>
      intro p a hp hchk k hk
      obtain ⟨hstep, hrest⟩ := Bool.and_eq_true _ _ |>.mp hchk
      obtain ⟨hne, hsl⟩ := Bool.and_eq_true _ _ |>.mp hstep
      have hne' : p.y ≠ -p.y := of_decide_eq_true hne
      have hsl' : s * (2 * p.y) = 3 * p.x ^ 2 := of_decide_eq_true hsl
      have hp' : zsmul (2 * a) (.affine G) = .affine (dstep p s) := by
        rw [show (2 : ℤ) * a = a + a by ring, zsmul_add hGI a a, hp]
        exact add_tangent p.x p.y s _ _ hne' hsl' rfl rfl
      cases k with
      | zero => simpa using hp
      | succ m =>
          have hm : m ≤ rest.length := by
            simpa [List.length_cons] using Nat.succ_le_succ_iff.mp hk
          have := ih (dstep p s) (2 * a) hp' hrest m hm
          rw [show (2 : ℤ) ^ (m + 1) * a = 2 ^ m * (2 * a) by ring]
          simpa [dnth] using this

end Solution.Secp256k1ScalarMulFixedBase.TableReflect

end DonorFile3_6
