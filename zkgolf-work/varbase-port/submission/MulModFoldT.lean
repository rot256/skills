import Solution.Secp256k1ScalarMul.MulModFold
import Solution.Secp256k1ScalarMul.CrtMul
import Solution.Secp256k1ScalarMul.ParamsFoldT
import Challenge.Utils.ComputableWitnessLemmas

/-!
# Folded modular-multiplication certificate with a *polynomial* target

Certifies `polyValue T ≡ a·b (mod p)` for the secp256k1 base prime
`p = 2^256 − 2^32 − 977`, where the target `T` is a raw `2m−1 = 7`-cell
convolution vector (as produced by, e.g., `3·(x ⊛ x)`), not a reduced
`BigInt`.

Both sides are folded onto four positions using `2^256 ≡ cFold (mod p)`:

* left:  `L_k = P_k + cFold·P_{k+4} + off_k`  (`k < 3`), `L_3 = P_3 + off_3`,
  where `Σ off_k 2^{64k} = kOffT·p`;
* right: `R_k = q·p_k + T_k + cFold·T_{k+4}`  (`k < 3`), `R_3 = q·p_3 + T_3`.

The constant offset `kOffT·p ≈ 2^325` dominates the folded target, so the
quotient `q = (D − R_T)/p` is a nonnegative single wire of 69 bits, and the
grouped equality needs a single 101-bit carry.  This replaces the unfolded
`MulModTargetT3` certificate (a full 256-bit quotient plus three carries).
-/

set_option exponentiation.threshold 400

namespace Solution.Secp256k1ScalarMul
namespace MulModFoldT

open MulMod
open Solution.Secp256k1ScalarMul.Limbs
open MulModFold

/-- Raw `2m−1`-cell target polynomial. -/
@[reducible] def TVec : TypeMap := fields (2 * numLimbs - 1)

/-- Inputs: two `BigInt` factors and a raw 7-cell target polynomial. -/
structure Inputs (F : Type) where
  a : Emu F
  b : Emu F
  target : TVec F
deriving ProvableStruct

/-- Offset multiplier: `kOffT · p` dominates every folded target value. -/
def kOffT : ℕ := 2 ^ 68

/-- Constant offset digits, `Σ offTNat k · 2^{64k} = kOffT·p`. -/
def offTNat (k : ℕ) : ℕ :=
  if k = 0 then kOffT * P256 % 2 ^ 64
  else if k = 1 then kOffT * P256 / 2 ^ 64 % 2 ^ 64
  else if k = 2 then kOffT * P256 / 2 ^ 128 % 2 ^ 64
  else kOffT * P256 / 2 ^ 192

lemma offTNat_sum :
    offTNat 0 + offTNat 1 * 2 ^ 64 + offTNat 2 * 2 ^ 128 + offTNat 3 * 2 ^ 192
      = kOffT * P256 := by
  decide

lemma offTNat_lt (k : ℕ) : offTNat k < 2 ^ 133 := by
  unfold offTNat; split_ifs <;> decide

/-- The three low offset digits are ordinary 64-bit limbs. -/
lemma offTNat_top : offTNat 3 < 2 ^ 132 := by decide

lemma offTNat_low_lt {k : ℕ} (hk : k < 3) : offTNat k < 2 ^ 64 := by
  have : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases this with rfl | rfl | rfl <;> decide

def offTE (k : ℕ) : Expression (F circomPrime) :=
  (((offTNat k : ℕ) : F circomPrime) : Expression (F circomPrime))

/-- The folded left-hand side. -/
def foldLhsT (Pc : Vector (Expression (F circomPrime)) (2 * numLimbs - 1)) :
    Vector (Expression (F circomPrime)) numLimbs :=
  #v[ Pc[0] + cfE * Pc[4] + offTE 0,
      Pc[1] + cfE * Pc[5] + offTE 1,
      Pc[2] + cfE * Pc[6] + offTE 2,
      Pc[3] + offTE 3 ]

/-- The folded right-hand side: `q·p` plus the folded target. -/
def foldRhsT (q : Expression (F circomPrime))
    (T : Vector (Expression (F circomPrime)) (2 * numLimbs - 1)) :
    Vector (Expression (F circomPrime)) numLimbs :=
  #v[ q * pElim 0 + (T[0] + cfE * T[4]),
      q * pElim 1 + (T[1] + cfE * T[5]),
      q * pElim 2 + (T[2] + cfE * T[6]),
      q * pElim 3 + T[3] ]

/-! ## Pure arithmetic -/

/-- The fold identity for the left-hand side. -/
lemma foldT_lhs_identity (c0 c1 c2 c3 c4 c5 c6 : ℕ) :
    ((c0 + cFold * c4 + offTNat 0) + (c1 + cFold * c5 + offTNat 1) * 2 ^ 64
        + (c2 + cFold * c6 + offTNat 2) * 2 ^ 128 + (c3 + offTNat 3) * 2 ^ 192)
      + P256 * (c4 + c5 * 2 ^ 64 + c6 * 2 ^ 128)
    = (c0 + c1 * 2 ^ 64 + c2 * 2 ^ 128 + c3 * 2 ^ 192 + c4 * 2 ^ 256 + c5 * 2 ^ 320
        + c6 * 2 ^ 384) + kOffT * P256 := by
  have hstep :
      ((c0 + cFold * c4 + offTNat 0) + (c1 + cFold * c5 + offTNat 1) * 2 ^ 64
        + (c2 + cFold * c6 + offTNat 2) * 2 ^ 128 + (c3 + offTNat 3) * 2 ^ 192)
      + P256 * (c4 + c5 * 2 ^ 64 + c6 * 2 ^ 128)
      = (c0 + c1 * 2 ^ 64 + c2 * 2 ^ 128 + c3 * 2 ^ 192)
        + (cFold + P256) * (c4 + c5 * 2 ^ 64 + c6 * 2 ^ 128)
        + (offTNat 0 + offTNat 1 * 2 ^ 64 + offTNat 2 * 2 ^ 128 + offTNat 3 * 2 ^ 192) := by
    ring
  rw [hstep, cFold_add, offTNat_sum]
  ring

/-- The fold identity for the target side. -/
lemma foldT_rhs_identity (t0 t1 t2 t3 t4 t5 t6 : ℕ) :
    ((t0 + cFold * t4) + (t1 + cFold * t5) * 2 ^ 64 + (t2 + cFold * t6) * 2 ^ 128
        + t3 * 2 ^ 192)
      + P256 * (t4 + t5 * 2 ^ 64 + t6 * 2 ^ 128)
    = t0 + t1 * 2 ^ 64 + t2 * 2 ^ 128 + t3 * 2 ^ 192 + t4 * 2 ^ 256 + t5 * 2 ^ 320
        + t6 * 2 ^ 384 := by
  have hstep :
      ((t0 + cFold * t4) + (t1 + cFold * t5) * 2 ^ 64 + (t2 + cFold * t6) * 2 ^ 128
        + t3 * 2 ^ 192)
      + P256 * (t4 + t5 * 2 ^ 64 + t6 * 2 ^ 128)
      = (t0 + t1 * 2 ^ 64 + t2 * 2 ^ 128 + t3 * 2 ^ 192)
        + (cFold + P256) * (t4 + t5 * 2 ^ 64 + t6 * 2 ^ 128) := by ring
  rw [hstep, cFold_add]
  ring

/-- Final congruence step. -/
lemma targetT_congr {A Bv PT q M MT D RT : ℕ}
    (hD : D + P256 * M = A * Bv + kOffT * P256)
    (hRT : RT + P256 * MT = PT)
    (hEq : D = q * P256 + RT) :
    PT % P256 = A * Bv % P256 := by
  have h : PT + P256 * (q + M) = A * Bv + P256 * (kOffT + MT) := by
    calc PT + P256 * (q + M)
        = (RT + P256 * MT) + P256 * (q + M) := by rw [hRT]
      _ = (q * P256 + RT) + P256 * M + P256 * MT := by ring
      _ = D + P256 * M + P256 * MT := by rw [← hEq]
      _ = (A * Bv + kOffT * P256) + P256 * MT := by rw [hD]
      _ = A * Bv + P256 * (kOffT + MT) := by ring
  have h2 : (PT + P256 * (q + M)) % P256 = (A * Bv + P256 * (kOffT + MT)) % P256 := by rw [h]
  rwa [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left] at h2

/-! ## Value-level digit lemmas -/

/-- Value of a left digit `x + cFold·y + d`. -/
lemma val_lhsT_digit {Nb OB : ℕ} {x y : F circomPrime} {d : ℕ}
    (hx : x.val < Nb) (hy : y.val < Nb) (hd : d < OB)
    (hNb : Nb * (1 + cFold) + OB ≤ 13 * 2 ^ 160) :
    (x + ((cFold : ℕ) : F circomPrime) * y + ((d : ℕ) : F circomPrime)).val
        = x.val + cFold * y.val + d ∧
      x.val + cFold * y.val + d < 13 * 2 ^ 160 :=
  MulModFold.val_lhs_digit hx hy hd hNb (by decide)

lemma val_lhsT_digit_top {Nb OB : ℕ} {x : F circomPrime} {d : ℕ}
    (hx : x.val < Nb) (hd : d < OB)
    (hNb : Nb * (1 + cFold) + OB ≤ 13 * 2 ^ 160) :
    (x + ((d : ℕ) : F circomPrime)).val = x.val + d ∧ x.val + d < 13 * 2 ^ 160 :=
  MulModFold.val_lhs_digit_top hx hd hNb (by decide)

/-- Value of a right digit `q·p_k + (x + cFold·y)`. -/
lemma val_rhsT_digit {Nb : ℕ} {q x y : F circomPrime} {k : ℕ}
    (hq : q.val < 2 ^ 69) (hx : x.val < Nb) (hy : y.val < Nb)
    (hNb : Nb * (1 + cFold) + 2 ^ 133 ≤ 13 * 2 ^ 160) :
    (q * ((pNat k : ℕ) : F circomPrime) + (x + ((cFold : ℕ) : F circomPrime) * y)).val
        = q.val * pNat k + (x.val + cFold * y.val) ∧
      q.val * pNat k + (x.val + cFold * y.val) < 13 * 2 ^ 160 := by
  have hpk := pNat_lt k
  have hqp : q.val * pNat k < 2 ^ 133 := by
    calc q.val * pNat k < 2 ^ 69 * 2 ^ 64 :=
          Nat.mul_lt_mul_of_lt_of_le hq (by omega) (by positivity)
      _ = 2 ^ 133 := by norm_num
  have hxy : x.val + cFold * y.val < 13 * 2 ^ 160 - 2 ^ 133 := by
    have h1 : cFold * y.val ≤ cFold * (Nb - 1) := Nat.mul_le_mul_left _ (by omega)
    have h2 : Nb * (1 + cFold) = Nb + cFold * Nb := by ring
    have h3 : cFold * (Nb - 1) ≤ cFold * Nb := Nat.mul_le_mul_left _ (by omega)
    omega
  have hsum : q.val * pNat k + (x.val + cFold * y.val) < 13 * 2 ^ 160 := by omega
  have hpsmall : (2 : ℕ) ^ 166 < circomPrime := by decide
  have hmulq : (q * ((pNat k : ℕ) : F circomPrime)).val = q.val * pNat k :=
    val_mul_natCast (by omega) (by omega)
  have hmulc : (((cFold : ℕ) : F circomPrime) * y).val = cFold * y.val :=
    val_natCast_mul cFold_lt (by omega)
  have hxyv : (x + ((cFold : ℕ) : F circomPrime) * y).val = x.val + cFold * y.val := by
    rw [ZMod.val_add_of_lt (by rw [hmulc]; omega), hmulc]
  refine ⟨?_, hsum⟩
  rw [ZMod.val_add_of_lt (by rw [hmulq, hxyv]; omega), hmulq, hxyv]

lemma val_rhsT_digit_top {Nb : ℕ} {q x : F circomPrime} {k : ℕ}
    (hq : q.val < 2 ^ 69) (hx : x.val < Nb)
    (hNb : Nb * (1 + cFold) + 2 ^ 133 ≤ 13 * 2 ^ 160) :
    (q * ((pNat k : ℕ) : F circomPrime) + x).val = q.val * pNat k + x.val ∧
      q.val * pNat k + x.val < 13 * 2 ^ 160 := by
  have hpk := pNat_lt k
  have hqp : q.val * pNat k < 2 ^ 133 := by
    calc q.val * pNat k < 2 ^ 69 * 2 ^ 64 :=
          Nat.mul_lt_mul_of_lt_of_le hq (by omega) (by positivity)
      _ = 2 ^ 133 := by norm_num
  have hNble : Nb ≤ Nb * (1 + cFold) := Nat.le_mul_of_pos_right _ (by omega)
  have hsum : q.val * pNat k + x.val < 13 * 2 ^ 160 := by omega
  have hpsmall : (2 : ℕ) ^ 166 < circomPrime := by decide
  have hmulq : (q * ((pNat k : ℕ) : F circomPrime)).val = q.val * pNat k :=
    val_mul_natCast (by omega) (by omega)
  exact ⟨by rw [ZMod.val_add_of_lt (by rw [hmulq]; omega), hmulq], hsum⟩

/-- Value of a right digit `q·p_k + (x + cFold·y)`, with *separate* caps for the
two coefficient positions.  Folded position 1 reads target cell 5, which every
call site keeps well below the uniform cap, so the digit stays under `8·2^160`. -/
lemma val_rhsT_digit1 {Nx Ny : ℕ} {q x y : F circomPrime} {k : ℕ}
    (hq : q.val < 2 ^ 69) (hx : x.val < Nx) (hy : y.val < Ny)
    (hN : Nx + cFold * Ny + 2 ^ 133 ≤ 8 * 2 ^ 160) :
    (q * ((pNat k : ℕ) : F circomPrime) + (x + ((cFold : ℕ) : F circomPrime) * y)).val
        = q.val * pNat k + (x.val + cFold * y.val) ∧
      q.val * pNat k + (x.val + cFold * y.val) < 8 * 2 ^ 160 := by
  have hpk := pNat_lt k
  have hqp : q.val * pNat k < 2 ^ 133 := by
    calc q.val * pNat k < 2 ^ 69 * 2 ^ 64 :=
          Nat.mul_lt_mul_of_lt_of_le hq (by omega) (by positivity)
      _ = 2 ^ 133 := by norm_num
  have h1 : cFold * y.val ≤ cFold * (Ny - 1) := Nat.mul_le_mul_left _ (by omega)
  have h3 : cFold * (Ny - 1) ≤ cFold * Ny := Nat.mul_le_mul_left _ (by omega)
  have hsum : q.val * pNat k + (x.val + cFold * y.val) < 8 * 2 ^ 160 := by omega
  have hpsmall : (2 : ℕ) ^ 166 < circomPrime := by decide
  have hmulq : (q * ((pNat k : ℕ) : F circomPrime)).val = q.val * pNat k :=
    val_mul_natCast (by omega) (by omega)
  have hmulc : (((cFold : ℕ) : F circomPrime) * y).val = cFold * y.val :=
    val_natCast_mul cFold_lt (by omega)
  have hxyv : (x + ((cFold : ℕ) : F circomPrime) * y).val = x.val + cFold * y.val := by
    rw [ZMod.val_add_of_lt (by rw [hmulc]; omega), hmulc]
  refine ⟨?_, hsum⟩
  rw [ZMod.val_add_of_lt (by rw [hmulq, hxyv]; omega), hmulq, hxyv]

/-! ## Digit bounds and `polyValue` of the two sides -/

/-- The folded left-hand value. -/
def foldDNatT (env : Environment (F circomPrime)) (a b : Var Emu (F circomPrime)) : ℕ :=
  (convNat env a b 0 + cFold * convNat env a b 4 + offTNat 0)
    + (convNat env a b 1 + cFold * convNat env a b 5 + offTNat 1) * 2 ^ 64
    + (convNat env a b 2 + cFold * convNat env a b 6 + offTNat 2) * 2 ^ 128
    + (convNat env a b 3 + offTNat 3) * 2 ^ 192

/-- The folded left-hand value, expressed through witnessed coefficients. -/
def foldDNatTOf (env : Environment (F circomPrime))
    (Pv : Vector (Expression (F circomPrime)) (2 * numLimbs - 1)) : ℕ :=
  ((Expression.eval env Pv[0]).val + cFold * (Expression.eval env Pv[4]).val + offTNat 0)
    + ((Expression.eval env Pv[1]).val + cFold * (Expression.eval env Pv[5]).val + offTNat 1)
        * 2 ^ 64
    + ((Expression.eval env Pv[2]).val + cFold * (Expression.eval env Pv[6]).val + offTNat 2)
        * 2 ^ 128
    + ((Expression.eval env Pv[3]).val + offTNat 3) * 2 ^ 192

/-- The folded target value. -/
def foldRTNat (env : Environment (F circomPrime))
    (T : Vector (Expression (F circomPrime)) (2 * numLimbs - 1)) : ℕ :=
  ((Expression.eval env T[0]).val + cFold * (Expression.eval env T[4]).val)
    + ((Expression.eval env T[1]).val + cFold * (Expression.eval env T[5]).val) * 2 ^ 64
    + ((Expression.eval env T[2]).val + cFold * (Expression.eval env T[6]).val) * 2 ^ 128
    + (Expression.eval env T[3]).val * 2 ^ 192

lemma foldLhsT_bound (env : Environment (F circomPrime))
    (Pv : Vector (Expression (F circomPrime)) (2 * numLimbs - 1)) (Nb : ℕ)
    (hPv : ∀ k : Fin (2 * numLimbs - 1), (Expression.eval env Pv[k.val]).val < Nb)
    (hNb : Nb * (1 + cFold) + 2 ^ 133 ≤ 13 * 2 ^ 160) :
    ∀ k : Fin numLimbs, (Expression.eval env (foldLhsT Pv)[k.val]).val < 13 * 2 ^ 160 := by
  intro k
  have h0 := hPv ⟨0, by decide⟩
  have h1 := hPv ⟨1, by decide⟩
  have h2 := hPv ⟨2, by decide⟩
  have h3 := hPv ⟨3, by decide⟩
  have h4 := hPv ⟨4, by decide⟩
  have h5 := hPv ⟨5, by decide⟩
  have h6 := hPv ⟨6, by decide⟩
  fin_cases k
  · have := val_lhsT_digit h0 h4 (offTNat_lt 0) hNb
    show (Expression.eval env (foldLhsT Pv)[0]).val < 13 * 2 ^ 160
    rw [show Expression.eval env (foldLhsT Pv)[0]
        = Expression.eval env Pv[0] + ((cFold : ℕ) : F circomPrime) * Expression.eval env Pv[4]
          + ((offTNat 0 : ℕ) : F circomPrime) from rfl, this.1]
    exact this.2
  · have := val_lhsT_digit h1 h5 (offTNat_lt 1) hNb
    show (Expression.eval env (foldLhsT Pv)[1]).val < 13 * 2 ^ 160
    rw [show Expression.eval env (foldLhsT Pv)[1]
        = Expression.eval env Pv[1] + ((cFold : ℕ) : F circomPrime) * Expression.eval env Pv[5]
          + ((offTNat 1 : ℕ) : F circomPrime) from rfl, this.1]
    exact this.2
  · have := val_lhsT_digit h2 h6 (offTNat_lt 2) hNb
    show (Expression.eval env (foldLhsT Pv)[2]).val < 13 * 2 ^ 160
    rw [show Expression.eval env (foldLhsT Pv)[2]
        = Expression.eval env Pv[2] + ((cFold : ℕ) : F circomPrime) * Expression.eval env Pv[6]
          + ((offTNat 2 : ℕ) : F circomPrime) from rfl, this.1]
    exact this.2
  · have := val_lhsT_digit_top h3 (offTNat_lt 3) hNb
    show (Expression.eval env (foldLhsT Pv)[3]).val < 13 * 2 ^ 160
    rw [show Expression.eval env (foldLhsT Pv)[3]
        = Expression.eval env Pv[3] + ((offTNat 3 : ℕ) : F circomPrime) from rfl, this.1]
    exact this.2

/-- Digit bounds of the folded left-hand side, refined at position 1.

Position 1 folds convolution cell 5, whose triangular term count is only 2, so
it is bounded by the smaller cap `nfFoldTL 1 = 7·2^160`. -/
lemma foldLhsT_boundN (env : Environment (F circomPrime))
    (Pv : Vector (Expression (F circomPrime)) (2 * numLimbs - 1)) (Nb N5 : ℕ)
    (hPv : ∀ k : Fin (2 * numLimbs - 1), (Expression.eval env Pv[k.val]).val < Nb)
    (h5 : (Expression.eval env Pv[5]).val < N5)
    (hNb : Nb * (1 + cFold) + 2 ^ 133 ≤ 13 * 2 ^ 160)
    (hN5 : Nb + cFold * N5 + 2 ^ 133 ≤ 7 * 2 ^ 160) :
    ∀ k : Fin numLimbs, (Expression.eval env (foldLhsT Pv)[k.val]).val < nfFoldTL k.val := by
  have hbase := foldLhsT_bound env Pv Nb hPv hNb
  intro k
  fin_cases k
  · show (Expression.eval env (foldLhsT Pv)[0]).val < nfFoldTL 0
    simpa only [nfFoldTL, if_neg (by decide : ¬ (0 : ℕ) = 1)] using hbase ⟨0, by decide⟩
  · have h1 := hPv ⟨1, by decide⟩
    have hd := val_lhs_digit2 h1 h5 (offTNat_lt 1) hN5 (by decide)
    show (Expression.eval env (foldLhsT Pv)[1]).val < nfFoldTL 1
    rw [show Expression.eval env (foldLhsT Pv)[1]
        = Expression.eval env Pv[1] + ((cFold : ℕ) : F circomPrime) * Expression.eval env Pv[5]
          + ((offTNat 1 : ℕ) : F circomPrime) from rfl, hd.1]
    simpa only [nfFoldTL, if_pos (rfl : (1 : ℕ) = 1)] using hd.2
  · show (Expression.eval env (foldLhsT Pv)[2]).val < nfFoldTL 2
    simpa only [nfFoldTL, if_neg (by decide : ¬ (2 : ℕ) = 1)] using hbase ⟨2, by decide⟩
  · show (Expression.eval env (foldLhsT Pv)[3]).val < nfFoldTL 3
    simpa only [nfFoldTL, if_neg (by decide : ¬ (3 : ℕ) = 1)] using hbase ⟨3, by decide⟩

lemma foldLhsT_polyValue (env : Environment (F circomPrime))
    (Pv : Vector (Expression (F circomPrime)) (2 * numLimbs - 1)) (Nb : ℕ)
    (hPv : ∀ k : Fin (2 * numLimbs - 1), (Expression.eval env Pv[k.val]).val < Nb)
    (hNb : Nb * (1 + cFold) + 2 ^ 133 ≤ 13 * 2 ^ 160) :
    polyValue 64 (Vector.map (Expression.eval env) (foldLhsT Pv)) = foldDNatTOf env Pv := by
  have h0 := hPv ⟨0, by decide⟩
  have h1 := hPv ⟨1, by decide⟩
  have h2 := hPv ⟨2, by decide⟩
  have h3 := hPv ⟨3, by decide⟩
  have h4 := hPv ⟨4, by decide⟩
  have h5 := hPv ⟨5, by decide⟩
  have h6 := hPv ⟨6, by decide⟩
  have e0 := (val_lhsT_digit h0 h4 (offTNat_lt 0) hNb).1
  have e1 := (val_lhsT_digit h1 h5 (offTNat_lt 1) hNb).1
  have e2 := (val_lhsT_digit h2 h6 (offTNat_lt 2) hNb).1
  have e3 := (val_lhsT_digit_top h3 (offTNat_lt 3) hNb).1
  rw [polyValue_four]
  simp only [Vector.getElem_map]
  rw [show (foldLhsT Pv)[0] = Pv[0] + cfE * Pv[4] + offTE 0 from rfl,
    show (foldLhsT Pv)[1] = Pv[1] + cfE * Pv[5] + offTE 1 from rfl,
    show (foldLhsT Pv)[2] = Pv[2] + cfE * Pv[6] + offTE 2 from rfl,
    show (foldLhsT Pv)[3] = Pv[3] + offTE 3 from rfl]
  rw [show Expression.eval env (Pv[0] + cfE * Pv[4] + offTE 0)
      = Expression.eval env Pv[0] + ((cFold : ℕ) : F circomPrime) * Expression.eval env Pv[4]
        + ((offTNat 0 : ℕ) : F circomPrime) from rfl,
    show Expression.eval env (Pv[1] + cfE * Pv[5] + offTE 1)
      = Expression.eval env Pv[1] + ((cFold : ℕ) : F circomPrime) * Expression.eval env Pv[5]
        + ((offTNat 1 : ℕ) : F circomPrime) from rfl,
    show Expression.eval env (Pv[2] + cfE * Pv[6] + offTE 2)
      = Expression.eval env Pv[2] + ((cFold : ℕ) : F circomPrime) * Expression.eval env Pv[6]
        + ((offTNat 2 : ℕ) : F circomPrime) from rfl,
    show Expression.eval env (Pv[3] + offTE 3)
      = Expression.eval env Pv[3] + ((offTNat 3 : ℕ) : F circomPrime) from rfl,
    e0, e1, e2, e3]
  rfl

lemma foldRhsT_bound (env : Environment (F circomPrime))
    (q : Expression (F circomPrime))
    (T : Vector (Expression (F circomPrime)) (2 * numLimbs - 1)) (Nt : ℕ)
    (hq : (Expression.eval env q).val < 2 ^ 69)
    (hT : ∀ k : Fin (2 * numLimbs - 1), (Expression.eval env T[k.val]).val < Nt)
    (hNt : Nt * (1 + cFold) + 2 ^ 133 ≤ 13 * 2 ^ 160) :
    ∀ k : Fin numLimbs, (Expression.eval env (foldRhsT q T)[k.val]).val < 13 * 2 ^ 160 := by
  intro k
  have h0 := hT ⟨0, by decide⟩
  have h1 := hT ⟨1, by decide⟩
  have h2 := hT ⟨2, by decide⟩
  have h3 := hT ⟨3, by decide⟩
  have h4 := hT ⟨4, by decide⟩
  have h5 := hT ⟨5, by decide⟩
  have h6 := hT ⟨6, by decide⟩
  fin_cases k
  · have := val_rhsT_digit (k := 0) hq h0 h4 hNt
    show (Expression.eval env (foldRhsT q T)[0]).val < 13 * 2 ^ 160
    rw [show Expression.eval env (foldRhsT q T)[0]
        = Expression.eval env q * ((pNat 0 : ℕ) : F circomPrime)
          + (Expression.eval env T[0]
            + ((cFold : ℕ) : F circomPrime) * Expression.eval env T[4]) from rfl, this.1]
    exact this.2
  · have := val_rhsT_digit (k := 1) hq h1 h5 hNt
    show (Expression.eval env (foldRhsT q T)[1]).val < 13 * 2 ^ 160
    rw [show Expression.eval env (foldRhsT q T)[1]
        = Expression.eval env q * ((pNat 1 : ℕ) : F circomPrime)
          + (Expression.eval env T[1]
            + ((cFold : ℕ) : F circomPrime) * Expression.eval env T[5]) from rfl, this.1]
    exact this.2
  · have := val_rhsT_digit (k := 2) hq h2 h6 hNt
    show (Expression.eval env (foldRhsT q T)[2]).val < 13 * 2 ^ 160
    rw [show Expression.eval env (foldRhsT q T)[2]
        = Expression.eval env q * ((pNat 2 : ℕ) : F circomPrime)
          + (Expression.eval env T[2]
            + ((cFold : ℕ) : F circomPrime) * Expression.eval env T[6]) from rfl, this.1]
    exact this.2
  · have := val_rhsT_digit_top (k := 3) hq h3 hNt
    show (Expression.eval env (foldRhsT q T)[3]).val < 13 * 2 ^ 160
    rw [show Expression.eval env (foldRhsT q T)[3]
        = Expression.eval env q * ((pNat 3 : ℕ) : F circomPrime)
          + Expression.eval env T[3] from rfl, this.1]
    exact this.2

/-- Digit bounds of the folded right-hand side, refined at position 1. -/
lemma foldRhsT_boundN (env : Environment (F circomPrime))
    (q : Expression (F circomPrime))
    (T : Vector (Expression (F circomPrime)) (2 * numLimbs - 1)) (Nt Nt5 : ℕ)
    (hq : (Expression.eval env q).val < 2 ^ 69)
    (hT : ∀ k : Fin (2 * numLimbs - 1), (Expression.eval env T[k.val]).val < Nt)
    (h5 : (Expression.eval env T[5]).val < Nt5)
    (hNt : Nt * (1 + cFold) + 2 ^ 133 ≤ 13 * 2 ^ 160)
    (hN5 : Nt + cFold * Nt5 + 2 ^ 133 ≤ 8 * 2 ^ 160) :
    ∀ k : Fin numLimbs, (Expression.eval env (foldRhsT q T)[k.val]).val < nfFoldTR k.val := by
  have hbase := foldRhsT_bound env q T Nt hq hT hNt
  intro k
  fin_cases k
  · show (Expression.eval env (foldRhsT q T)[0]).val < nfFoldTR 0
    simpa only [nfFoldTR, if_neg (by decide : ¬ (0 : ℕ) = 1)] using hbase ⟨0, by decide⟩
  · have h1 := hT ⟨1, by decide⟩
    have hd := val_rhsT_digit1 (k := 1) hq h1 h5 hN5
    show (Expression.eval env (foldRhsT q T)[1]).val < nfFoldTR 1
    rw [show Expression.eval env (foldRhsT q T)[1]
        = Expression.eval env q * ((pNat 1 : ℕ) : F circomPrime)
          + (Expression.eval env T[1]
            + ((cFold : ℕ) : F circomPrime) * Expression.eval env T[5]) from rfl, hd.1]
    simpa only [nfFoldTR, if_pos (rfl : (1 : ℕ) = 1)] using hd.2
  · show (Expression.eval env (foldRhsT q T)[2]).val < nfFoldTR 2
    simpa only [nfFoldTR, if_neg (by decide : ¬ (2 : ℕ) = 1)] using hbase ⟨2, by decide⟩
  · show (Expression.eval env (foldRhsT q T)[3]).val < nfFoldTR 3
    simpa only [nfFoldTR, if_neg (by decide : ¬ (3 : ℕ) = 1)] using hbase ⟨3, by decide⟩

lemma foldRhsT_polyValue (env : Environment (F circomPrime))
    (q : Expression (F circomPrime))
    (T : Vector (Expression (F circomPrime)) (2 * numLimbs - 1)) (Nt : ℕ)
    (hq : (Expression.eval env q).val < 2 ^ 69)
    (hT : ∀ k : Fin (2 * numLimbs - 1), (Expression.eval env T[k.val]).val < Nt)
    (hNt : Nt * (1 + cFold) + 2 ^ 133 ≤ 13 * 2 ^ 160) :
    polyValue 64 (Vector.map (Expression.eval env) (foldRhsT q T))
      = (Expression.eval env q).val * P256 + foldRTNat env T := by
  have h0 := hT ⟨0, by decide⟩
  have h1 := hT ⟨1, by decide⟩
  have h2 := hT ⟨2, by decide⟩
  have h3 := hT ⟨3, by decide⟩
  have h4 := hT ⟨4, by decide⟩
  have h5 := hT ⟨5, by decide⟩
  have h6 := hT ⟨6, by decide⟩
  have e0 := (val_rhsT_digit (k := 0) hq h0 h4 hNt).1
  have e1 := (val_rhsT_digit (k := 1) hq h1 h5 hNt).1
  have e2 := (val_rhsT_digit (k := 2) hq h2 h6 hNt).1
  have e3 := (val_rhsT_digit_top (k := 3) hq h3 hNt).1
  rw [polyValue_four]
  simp only [Vector.getElem_map]
  rw [show (foldRhsT q T)[0] = q * pElim 0 + (T[0] + cfE * T[4]) from rfl,
    show (foldRhsT q T)[1] = q * pElim 1 + (T[1] + cfE * T[5]) from rfl,
    show (foldRhsT q T)[2] = q * pElim 2 + (T[2] + cfE * T[6]) from rfl,
    show (foldRhsT q T)[3] = q * pElim 3 + T[3] from rfl]
  rw [show Expression.eval env (q * pElim 0 + (T[0] + cfE * T[4]))
      = Expression.eval env q * ((pNat 0 : ℕ) : F circomPrime)
        + (Expression.eval env T[0]
          + ((cFold : ℕ) : F circomPrime) * Expression.eval env T[4]) from rfl,
    show Expression.eval env (q * pElim 1 + (T[1] + cfE * T[5]))
      = Expression.eval env q * ((pNat 1 : ℕ) : F circomPrime)
        + (Expression.eval env T[1]
          + ((cFold : ℕ) : F circomPrime) * Expression.eval env T[5]) from rfl,
    show Expression.eval env (q * pElim 2 + (T[2] + cfE * T[6]))
      = Expression.eval env q * ((pNat 2 : ℕ) : F circomPrime)
        + (Expression.eval env T[2]
          + ((cFold : ℕ) : F circomPrime) * Expression.eval env T[6]) from rfl,
    show Expression.eval env (q * pElim 3 + T[3])
      = Expression.eval env q * ((pNat 3 : ℕ) : F circomPrime)
        + Expression.eval env T[3] from rfl,
    e0, e1, e2, e3, ← pNat_sum]
  unfold foldRTNat
  ring

/-! ## The certificate -/

/-- The witnessed quotient. -/
def qNatT (env : Environment (F circomPrime)) (input : Var Inputs (F circomPrime)) : ℕ :=
  (foldDNatT env input.a input.b - foldRTNat env input.target) / P256

lemma foldDNatT_ge (env : Environment (F circomPrime)) (a b : Var Emu (F circomPrime)) :
    kOffT * P256 ≤ foldDNatT env a b := by
  rw [← offTNat_sum]
  unfold foldDNatT
  gcongr <;> omega

/-- The digit cap implied by the coefficient cap. -/
lemma cap_lhsT {N : ℕ} (hcap : N ≤ 12 * 2 ^ 128) :
    N * (1 + cFold) + 2 ^ 133 ≤ 13 * 2 ^ 160 := by
  have hcf : cFold = 2 ^ 32 + 977 := rfl
  rw [hcf]
  have hmul : N * (1 + (2 ^ 32 + 977)) ≤ 12 * 2 ^ 128 * (1 + (2 ^ 32 + 977)) :=
    Nat.mul_le_mul_right _ hcap
  omega

/-- The refined cap at folded position 1 on the left: cell 5 carries only two
convolution terms, so the digit stays under `7·2^160`. -/
lemma cap_lhsT5 {N M : ℕ} (hcap : N ≤ 12 * 2 ^ 128) (hM : 4 * M ≤ N) :
    N + cFold * (2 * M) + 2 ^ 133 ≤ 7 * 2 ^ 160 := by
  have hcf : cFold = 2 ^ 32 + 977 := rfl
  rw [hcf]
  have h2M : 2 * M ≤ 6 * 2 ^ 128 := by omega
  have hmul : (2 ^ 32 + 977) * (2 * M) ≤ (2 ^ 32 + 977) * (6 * 2 ^ 128) :=
    Nat.mul_le_mul_left _ h2M
  omega

/-- The refined cap at folded position 1 on the right. -/
lemma cap_rhsT5 {Nt Nt5 : ℕ} (hNt : Nt ≤ 12 * 2 ^ 128) (hNt5 : Nt5 ≤ 6 * 2 ^ 128) :
    Nt + cFold * Nt5 + 2 ^ 133 ≤ 8 * 2 ^ 160 := by
  have hcf : cFold = 2 ^ 32 + 977 := rfl
  rw [hcf]
  have hmul : (2 ^ 32 + 977) * Nt5 ≤ (2 ^ 32 + 977) * (6 * 2 ^ 128) :=
    Nat.mul_le_mul_left _ hNt5
  omega

lemma foldDNatT_lt {Ca Cb : ℕ} (env : Environment (F circomPrime))
    (a b : Var Emu (F circomPrime))
    (ha : ∀ i : Fin numLimbs, (Expression.eval env (a[i.val]'i.isLt)).val < Ca)
    (hb : ∀ i : Fin numLimbs, (Expression.eval env (b[i.val]'i.isLt)).val < Cb)
    (hcap : numLimbs * (Ca * Cb) ≤ 12 * 2 ^ 128) :
    foldDNatT env a b < 29 * 2 ^ 320 := by
  have hcapL := cap_lhsT hcap
  have hdig : ∀ j k : ℕ,
      convNat env a b j + cFold * convNat env a b k + offTNat j < 13 * 2 ^ 160 := by
    intro j k
    have hj := convNat_lt env a b ha hb j
    have hk := convNat_lt env a b ha hb k
    have hoff := offTNat_lt j
    have hmul : cFold * convNat env a b k ≤ cFold * (numLimbs * (Ca * Cb) - 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have hexp : numLimbs * (Ca * Cb) * (1 + cFold)
        = numLimbs * (Ca * Cb) + cFold * (numLimbs * (Ca * Cb)) := by ring
    have hmul2 : cFold * (numLimbs * (Ca * Cb) - 1) ≤ cFold * (numLimbs * (Ca * Cb)) :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  have h0 := hdig 0 4
  have h1 := hdig 1 5
  have h2 := hdig 2 6
  have h3 : convNat env a b 3 + offTNat 3 < 2 ^ 132 + 12 * 2 ^ 128 := by
    have hj := convNat_lt env a b ha hb 3
    have hoff : offTNat 3 < 2 ^ 132 := offTNat_top
    omega
  unfold foldDNatT
  omega

/-- The folded target is dominated by the constant offset. -/
lemma foldRTNat_lt_offset (env : Environment (F circomPrime))
    (T : Vector (Expression (F circomPrime)) (2 * numLimbs - 1)) (Nt : ℕ)
    (hT : ∀ k : Fin (2 * numLimbs - 1), (Expression.eval env T[k.val]).val < Nt)
    (hNt : Nt ≤ 12 * 2 ^ 128) :
    foldRTNat env T ≤ kOffT * P256 := by
  have h0 : (Expression.eval env T[0]).val < Nt := hT ⟨0, by decide⟩
  have h1 : (Expression.eval env T[1]).val < Nt := hT ⟨1, by decide⟩
  have h2 : (Expression.eval env T[2]).val < Nt := hT ⟨2, by decide⟩
  have h3 : (Expression.eval env T[3]).val < Nt := hT ⟨3, by decide⟩
  have h4 : (Expression.eval env T[4]).val < Nt := hT ⟨4, by decide⟩
  have h5 : (Expression.eval env T[5]).val < Nt := hT ⟨5, by decide⟩
  have h6 : (Expression.eval env T[6]).val < Nt := hT ⟨6, by decide⟩
  have hcf : cFold = 2 ^ 32 + 977 := rfl
  have hk : kOffT * P256 = 2 ^ 324 - 2 ^ 100 - 977 * 2 ^ 68 := by decide
  unfold foldRTNat
  rw [hcf, hk]
  omega

lemma foldDNatTOf_eq {Ca Cb : ℕ} (env : Environment (F circomPrime))
    (a b : Var Emu (F circomPrime))
    (ha : ∀ i : Fin numLimbs, (Expression.eval env (a[i.val]'i.isLt)).val < Ca)
    (hb : ∀ i : Fin numLimbs, (Expression.eval env (b[i.val]'i.isLt)).val < Cb)
    (hbound : numLimbs * (Ca * Cb) < circomPrime)
    (Pv : Vector (Expression (F circomPrime)) (2 * numLimbs - 1))
    (hbridge : ∀ k : Fin (2 * numLimbs - 1),
      Expression.eval env Pv[k.val] = Expression.eval env (bigIntMulNoReduce a b)[k.val]) :
    foldDNatTOf env Pv = foldDNatT env a b := by
  unfold foldDNatTOf foldDNatT
  rw [hbridge ⟨0, by decide⟩, hbridge ⟨1, by decide⟩, hbridge ⟨2, by decide⟩,
    hbridge ⟨3, by decide⟩, hbridge ⟨4, by decide⟩, hbridge ⟨5, by decide⟩,
    hbridge ⟨6, by decide⟩,
    coeff_eq_convNat env a b ha hb hbound ⟨0, by decide⟩,
    coeff_eq_convNat env a b ha hb hbound ⟨1, by decide⟩,
    coeff_eq_convNat env a b ha hb hbound ⟨2, by decide⟩,
    coeff_eq_convNat env a b ha hb hbound ⟨3, by decide⟩,
    coeff_eq_convNat env a b ha hb hbound ⟨4, by decide⟩,
    coeff_eq_convNat env a b ha hb hbound ⟨5, by decide⟩,
    coeff_eq_convNat env a b ha hb hbound ⟨6, by decide⟩]

lemma foldDNatT_identity {Ca Cb : ℕ} (env : Environment (F circomPrime))
    (a b : Var Emu (F circomPrime))
    (ha : ∀ i : Fin numLimbs, (Expression.eval env (a[i.val]'i.isLt)).val < Ca)
    (hb : ∀ i : Fin numLimbs, (Expression.eval env (b[i.val]'i.isLt)).val < Cb)
    (hbound : numLimbs * (Ca * Cb) < circomPrime) :
    foldDNatT env a b
        + P256 * (convNat env a b 4 + convNat env a b 5 * 2 ^ 64
            + convNat env a b 6 * 2 ^ 128)
      = BigInt.value 64 (Vector.map (Expression.eval env) a)
          * BigInt.value 64 (Vector.map (Expression.eval env) b) + kOffT * P256 := by
  have hprod : polyValue 64 (Vector.map (Expression.eval env) (bigIntMulNoReduce a b))
      = BigInt.value 64 (Vector.map (Expression.eval env) a)
        * BigInt.value 64 (Vector.map (Expression.eval env) b) :=
    MulModTargetW2.polyValue_mul_eq_gen2 env a b ha hb hbound
  rw [polyValue_seven_map] at hprod
  rw [← hprod]
  unfold foldDNatT
  rw [← coeff_eq_convNat env a b ha hb hbound ⟨0, by decide⟩,
    ← coeff_eq_convNat env a b ha hb hbound ⟨1, by decide⟩,
    ← coeff_eq_convNat env a b ha hb hbound ⟨2, by decide⟩,
    ← coeff_eq_convNat env a b ha hb hbound ⟨3, by decide⟩,
    ← coeff_eq_convNat env a b ha hb hbound ⟨4, by decide⟩,
    ← coeff_eq_convNat env a b ha hb hbound ⟨5, by decide⟩,
    ← coeff_eq_convNat env a b ha hb hbound ⟨6, by decide⟩]
  exact foldT_lhs_identity _ _ _ _ _ _ _

/-- The folded target value against the raw `polyValue`. -/
lemma foldRTNat_identity (env : Environment (F circomPrime))
    (T : Vector (Expression (F circomPrime)) (2 * numLimbs - 1)) :
    foldRTNat env T
        + P256 * ((Expression.eval env T[4]).val + (Expression.eval env T[5]).val * 2 ^ 64
            + (Expression.eval env T[6]).val * 2 ^ 128)
      = polyValue 64 (Vector.map (Expression.eval env) T) := by
  rw [polyValue_seven_map]
  unfold foldRTNat
  exact foldT_rhs_identity _ _ _ _ _ _ _

/-- The folded left-hand side, built directly from the four CRT-multiply digits.

`CrtMul.crtMul` already emits the *folded* product `a·b mod (X^4 − cFold)`, so
all that is left is to add the constant offset digits. -/
def foldLhsC (d : Vector (Expression (F circomPrime)) numLimbs) :
    Vector (Expression (F circomPrime)) numLimbs :=
  #v[ d[0] + offTE 0, d[1] + offTE 1, d[2] + offTE 2, d[3] + offTE 3 ]

/-- Pointwise, `foldLhsC` of the CRT digits agrees with `foldLhsT` of the raw
seven-cell convolution — so every bound and `polyValue` lemma above applies. -/
lemma foldLhsC_eval_eq (env : Environment (F circomPrime))
    (a b : Var Emu (F circomPrime)) (d : Vector (Expression (F circomPrime)) numLimbs)
    (hd : ∀ k : Fin numLimbs,
      Expression.eval env d[k.val] = Expression.eval env (CrtMul.foldRawE a b)[k.val])
    (i : ℕ) (hi : i < numLimbs) :
    Expression.eval env ((foldLhsC d)[i]'hi)
      = Expression.eval env ((foldLhsT (bigIntMulNoReduce a b))[i]'hi) := by
  have hi4 : i < 4 := hi
  have h4 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases h4 with rfl | rfl | rfl | rfl
  · show Expression.eval env d[0] + ((offTNat 0 : ℕ) : F circomPrime) = _
    rw [hd ⟨0, by decide⟩]
    rfl
  · show Expression.eval env d[1] + ((offTNat 1 : ℕ) : F circomPrime) = _
    rw [hd ⟨1, by decide⟩]
    rfl
  · show Expression.eval env d[2] + ((offTNat 2 : ℕ) : F circomPrime) = _
    rw [hd ⟨2, by decide⟩]
    rfl
  · show Expression.eval env d[3] + ((offTNat 3 : ℕ) : F circomPrime) = _
    rw [hd ⟨3, by decide⟩]
    rfl

lemma foldLhsC_map_eq (env : Environment (F circomPrime))
    (a b : Var Emu (F circomPrime)) (d : Vector (Expression (F circomPrime)) numLimbs)
    (hd : ∀ k : Fin numLimbs,
      Expression.eval env d[k.val] = Expression.eval env (CrtMul.foldRawE a b)[k.val]) :
    Vector.map (Expression.eval env) (foldLhsC d)
      = Vector.map (Expression.eval env) (foldLhsT (bigIntMulNoReduce a b)) := by
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_map]
  exact foldLhsC_eval_eq env a b d hd i hi

lemma foldLhsC_stable {E1 E2 : Environment (F circomPrime)}
    (d : Vector (Expression (F circomPrime)) numLimbs)
    (h : ∀ (i : ℕ) (hi : i < numLimbs),
      Expression.eval E1 (d[i]'hi) = Expression.eval E2 (d[i]'hi)) :
    Vector.map (Expression.eval E1) (foldLhsC d)
      = Vector.map (Expression.eval E2) (foldLhsC d) := by
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_map]
  have hi4 : i < 4 := hi
  have h4 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases h4 with rfl | rfl | rfl | rfl
  · show Expression.eval E1 d[0] + ((offTNat 0 : ℕ) : F circomPrime)
      = Expression.eval E2 d[0] + ((offTNat 0 : ℕ) : F circomPrime)
    rw [h 0 (by decide)]
  · show Expression.eval E1 d[1] + ((offTNat 1 : ℕ) : F circomPrime)
      = Expression.eval E2 d[1] + ((offTNat 1 : ℕ) : F circomPrime)
    rw [h 1 (by decide)]
  · show Expression.eval E1 d[2] + ((offTNat 2 : ℕ) : F circomPrime)
      = Expression.eval E2 d[2] + ((offTNat 2 : ℕ) : F circomPrime)
    rw [h 2 (by decide)]
  · show Expression.eval E1 d[3] + ((offTNat 3 : ℕ) : F circomPrime)
      = Expression.eval E2 d[3] + ((offTNat 3 : ℕ) : F circomPrime)
    rw [h 3 (by decide)]

def main (input : Var Inputs (F circomPrime)) : Circuit (F circomPrime) Unit := do
  let q ← witnessField fun env =>
    ((qNatT env.toEnvironment input : ℕ) : F circomPrime)
  RangeCheck.circuit qBitsFoldT (by decide) (by decide) q
  let d ← CrtMul.crtMul input.a input.b
  GroupedEqXV.circuit 64 gfFold posOfFold 3 vFoldTL vFoldTR hgvFoldT (by norm_num)
    { lhs := foldLhsC d, rhs := foldRhsT q input.target }

instance elaborated : ElaboratedCircuit (F circomPrime) Inputs unit main where
  -- q (1) + range check (qBits − 1) + folded product (4) + one carry (Wf − 1)
  localLength _ := 172
  localLength_eq := by
    intro input offset
    simp only [main, CrtMul.crtMul, circuit_norm, RangeCheck.circuit,
      GroupedEqXV.circuit, GroupedEqXV.elaborated, vFoldTL, wfFoldT,
      GroupedEqXV.widthAllocFrom, qBitsFoldT, numLimbs]
  subcircuitsConsistent := by
    intro input offset
    simp +arith only [main, CrtMul.crtMul, circuit_norm, RangeCheck.circuit,
      GroupedEqXV.circuit, GroupedEqXV.elaborated]
  channelsLawful := by
    intro offset
    simp only [main, CrtMul.crtMul, circuit_norm, RangeCheck.circuit,
      GroupedEqXV.circuit, GroupedEqXV.elaborated]

def Assumptions (Ca Cb Nt Nt5 : ℕ) (input : Inputs (F circomPrime)) : Prop :=
  (∀ i : Fin numLimbs, (input.a[i.val]).val < Ca) ∧
  (∀ i : Fin numLimbs, (input.b[i.val]).val < Cb) ∧
  (∀ k : Fin (2 * numLimbs - 1), (input.target[k.val]).val < Nt) ∧
  (input.target[5]).val < Nt5

def Spec (input : Inputs (F circomPrime)) : Prop :=
  polyValue 64 input.target % P256
    = BigInt.value 64 input.a * BigInt.value 64 input.b % P256

/-- The two folds agree modulo `p`. -/
lemma foldD_mod_T {A Bv D M PT RT MT : ℕ}
    (hD : D + P256 * M = A * Bv + kOffT * P256)
    (hRT : RT + P256 * MT = PT)
    (hspec : PT % P256 = A * Bv % P256) :
    D % P256 = RT % P256 := by
  have h1 : D % P256 = A * Bv % P256 := by
    have : (D + P256 * M) % P256 = (A * Bv + P256 * kOffT) % P256 := by
      rw [hD]; ring_nf
    rwa [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left] at this
  have h2 : RT % P256 = PT % P256 := by
    have : (RT + P256 * MT) % P256 = PT % P256 := by rw [hRT]
    rwa [Nat.add_mul_mod_self_left] at this
  rw [h1, h2, hspec]

theorem soundness (Ca Cb Nt Nt5 : ℕ)
    (hcap : numLimbs * (Ca * Cb) ≤ 12 * 2 ^ 128)
    (hcapT : Nt ≤ 12 * 2 ^ 128) (hNt5 : Nt5 ≤ 6 * 2 ^ 128) :
    FormalAssertion.Soundness (F circomPrime) main (Assumptions Ca Cb Nt Nt5) Spec := by
  circuit_proof_start [RangeCheck.circuit, RangeCheck.Assumptions, RangeCheck.Spec,
    GroupedEqXV.circuit, GroupedEqXV.elaborated, GroupedEqXV.Assumptions, GroupedEqX.Spec]
  obtain ⟨hq_lt, hAB_ops, h_eq_impl⟩ := h_holds
  obtain ⟨ha_lt, hb_lt, ht_lt, ht5⟩ := h_assumptions
  obtain ⟨ha_in, hb_in, ht_in⟩ := h_input
  refine ⟨?_, CrtMul.crtMul_requirements _ _ _ _⟩
  simp only [vFoldTL, vFoldTR] at h_eq_impl
  have hd := CrtMul.crtMul_eval_bridge env (i₀ + 1 + (qBitsFoldT - 1))
    input_var_a input_var_b
    (CrtMul.crtMul_soundness (i₀ + 1 + (qBitsFoldT - 1)) input_var_a input_var_b env hAB_ops)
  have ha_lt' : ∀ i : Fin numLimbs,
      (Expression.eval env (input_var_a[i.val]'i.isLt)).val < Ca := by
    intro i
    rw [show Expression.eval env (input_var_a[i.val]'i.isLt) = input_a[i.val] from by
      rw [← ha_in]; simp only [Vector.getElem_map]]
    exact ha_lt i
  have hb_lt' : ∀ i : Fin numLimbs,
      (Expression.eval env (input_var_b[i.val]'i.isLt)).val < Cb := by
    intro i
    rw [show Expression.eval env (input_var_b[i.val]'i.isLt) = input_b[i.val] from by
      rw [← hb_in]; simp only [Vector.getElem_map]]
    exact hb_lt i
  have ht_lt' : ∀ k : Fin (2 * numLimbs - 1),
      (Expression.eval env (input_var_target[k.val]'k.isLt)).val < Nt := by
    intro k
    rw [show Expression.eval env (input_var_target[k.val]'k.isLt) = input_target[k.val] from by
      rw [← ht_in]; simp only [Vector.getElem_map]]
    exact ht_lt k
  have hNbp : numLimbs * (Ca * Cb) < circomPrime := by
    have h1 : numLimbs * (Ca * Cb) ≤ numLimbs * (Ca * Cb) * (1 + cFold) :=
      Nat.le_mul_of_pos_right _ (by omega)
    have h2 : (2 : ℕ) ^ 166 < circomPrime := by decide
    omega
  have hPv : ∀ k : Fin (2 * numLimbs - 1),
      (Expression.eval env (bigIntMulNoReduce input_var_a input_var_b)[k.val]).val
        < numLimbs * (Ca * Cb) :=
    fun k => MulModTargetW2.val_coeff_lt_gen2 env input_var_a input_var_b k ha_lt' hb_lt' hNbp
  have hqv : (Expression.eval env (var (F := F circomPrime) { index := i₀ })).val < 2 ^ 69 :=
    hq_lt
  have ht5' : (Expression.eval env (input_var_target[5]'(by decide))).val < Nt5 := by
    rw [show Expression.eval env (input_var_target[5]'(by decide)) = input_target[5] from by
      rw [← ht_in]; simp only [Vector.getElem_map]]
    exact ht5
  have hPv5 : (Expression.eval env (bigIntMulNoReduce input_var_a input_var_b)[5]).val
      < 2 * (Ca * Cb) :=
    coeff5_lt env input_var_a input_var_b ha_lt' hb_lt' hNbp
  have heq := h_eq_impl
    ⟨fun k => by
        rw [foldLhsC_eval_eq env input_var_a input_var_b _ hd k.val k.isLt]
        exact foldLhsT_boundN env _ (numLimbs * (Ca * Cb)) (2 * (Ca * Cb)) hPv hPv5
          (cap_lhsT hcap) (cap_lhsT5 hcap (le_refl _)) k,
     foldRhsT_boundN env _ input_var_target Nt Nt5 hqv ht_lt' ht5' (cap_lhsT hcapT)
       (cap_rhsT5 hcapT hNt5)⟩
  rw [foldLhsC_map_eq env input_var_a input_var_b _ hd,
    foldLhsT_polyValue env _ (numLimbs * (Ca * Cb)) hPv (cap_lhsT hcap),
    foldRhsT_polyValue env _ input_var_target Nt hqv ht_lt' (cap_lhsT hcapT),
    foldDNatTOf_eq env input_var_a input_var_b ha_lt' hb_lt' hNbp _ (fun _ => rfl)] at heq
  have hid := foldDNatT_identity env input_var_a input_var_b ha_lt' hb_lt' hNbp
  rw [ha_in, hb_in] at hid
  have hidT := foldRTNat_identity env input_var_target
  rw [ht_in] at hidT
  exact targetT_congr hid hidT heq

theorem completeness (Ca Cb Nt Nt5 : ℕ)
    (hcap : numLimbs * (Ca * Cb) ≤ 12 * 2 ^ 128)
    (hcapT : Nt ≤ 12 * 2 ^ 128) (hNt : Nt ≤ 12 * 2 ^ 128) (hNt5 : Nt5 ≤ 6 * 2 ^ 128) :
    FormalAssertion.Completeness (F circomPrime) main (Assumptions Ca Cb Nt Nt5) Spec := by
  circuit_proof_start [RangeCheck.circuit, RangeCheck.Assumptions, RangeCheck.Spec,
    GroupedEqXV.circuit, GroupedEqXV.elaborated, GroupedEqXV.Assumptions, GroupedEqX.Spec]
  obtain ⟨hq_env, hAB_uses⟩ := h_env
  obtain ⟨ha_lt, hb_lt, ht_lt, ht5⟩ := h_assumptions
  obtain ⟨ha_in, hb_in, ht_in⟩ := h_input
  simp only [vFoldTL, vFoldTR]
  have ha_lt' : ∀ i : Fin numLimbs,
      (Expression.eval env.toEnvironment (input_var_a[i.val]'i.isLt)).val < Ca := by
    intro i
    rw [show Expression.eval env.toEnvironment (input_var_a[i.val]'i.isLt) = input_a[i.val] from by
      rw [← ha_in]; simp only [Vector.getElem_map]]
    exact ha_lt i
  have hb_lt' : ∀ i : Fin numLimbs,
      (Expression.eval env.toEnvironment (input_var_b[i.val]'i.isLt)).val < Cb := by
    intro i
    rw [show Expression.eval env.toEnvironment (input_var_b[i.val]'i.isLt) = input_b[i.val] from by
      rw [← hb_in]; simp only [Vector.getElem_map]]
    exact hb_lt i
  have ht_lt' : ∀ k : Fin (2 * numLimbs - 1),
      (Expression.eval env.toEnvironment (input_var_target[k.val]'k.isLt)).val < Nt := by
    intro k
    rw [show Expression.eval env.toEnvironment (input_var_target[k.val]'k.isLt)
        = input_target[k.val] from by rw [← ht_in]; simp only [Vector.getElem_map]]
    exact ht_lt k
  have hNbp : numLimbs * (Ca * Cb) < circomPrime := by
    have h1 : numLimbs * (Ca * Cb) ≤ numLimbs * (Ca * Cb) * (1 + cFold) :=
      Nat.le_mul_of_pos_right _ (by omega)
    have h2 : (2 : ℕ) ^ 166 < circomPrime := by decide
    omega
  have h_pvAB := CrtMul.crtMul_usesLocalWitnesses (i₀ + 1 + (qBitsFoldT - 1))
    (i₀ + 1 + (qBitsFoldT - 1)) input_var_a input_var_b env rfl hAB_uses
  have hd := CrtMul.crtMul_eval_bridge_uses env.toEnvironment
    (i₀ + 1 + (qBitsFoldT - 1)) input_var_a input_var_b h_pvAB
  have hPv : ∀ k : Fin (2 * numLimbs - 1),
      (Expression.eval env.toEnvironment (bigIntMulNoReduce input_var_a input_var_b)[k.val]).val
        < numLimbs * (Ca * Cb) :=
    fun k => MulModTargetW2.val_coeff_lt_gen2 env.toEnvironment input_var_a input_var_b k
      ha_lt' hb_lt' hNbp
  set D := foldDNatT env.toEnvironment input_var_a input_var_b with hDdef
  set RT := foldRTNat env.toEnvironment input_var_target with hRTdef
  have hDge : kOffT * P256 ≤ D := foldDNatT_ge env.toEnvironment input_var_a input_var_b
  have hRTle : RT ≤ kOffT * P256 :=
    foldRTNat_lt_offset env.toEnvironment input_var_target Nt ht_lt' hNt
  have hDlt : D < 29 * 2 ^ 320 := foldDNatT_lt env.toEnvironment input_var_a input_var_b
    ha_lt' hb_lt' hcap
  have hid := foldDNatT_identity env.toEnvironment input_var_a input_var_b ha_lt' hb_lt' hNbp
  rw [ha_in, hb_in] at hid
  have hidT := foldRTNat_identity env.toEnvironment input_var_target
  rw [ht_in] at hidT
  have hDmod : D % P256 = RT % P256 := foldD_mod_T hid hidT h_spec
  have hqdef : qNatT env.toEnvironment
      { a := input_var_a, b := input_var_b, target := input_var_target } = (D - RT) / P256 := rfl
  have hqlt : (D - RT) / P256 < 2 ^ 69 := by
    have hp : P256 = 2 ^ 256 - 2 ^ 32 - 977 := by decide
    have hdiv : (D - RT) / P256 ≤ D / P256 := Nat.div_le_div_right (by omega)
    have : D / P256 < 2 ^ 69 := by
      apply Nat.div_lt_of_lt_mul
      calc D < 29 * 2 ^ 320 := hDlt
        _ ≤ 2 ^ 69 * P256 := by rw [hp]; norm_num
    omega
  have hqval : (env.get i₀).val = (D - RT) / P256 := by
    rw [hq_env, hqdef]
    exact ZMod.val_natCast_of_lt (by
      have : (2 : ℕ) ^ 72 < circomPrime := by decide
      omega)
  have hqvar : (Expression.eval env.toEnvironment
      (var (F := F circomPrime) { index := i₀ })).val < 2 ^ 69 := by
    show (env.get i₀).val < 2 ^ 69
    rw [hqval]; exact hqlt
  have ht5' : (Expression.eval env.toEnvironment
      (input_var_target[5]'(by decide))).val < Nt5 := by
    rw [show Expression.eval env.toEnvironment (input_var_target[5]'(by decide))
        = input_target[5] from by rw [← ht_in]; simp only [Vector.getElem_map]]
    exact ht5
  have hPv5 : (Expression.eval env.toEnvironment
      (bigIntMulNoReduce input_var_a input_var_b)[5]).val < 2 * (Ca * Cb) :=
    coeff5_lt env.toEnvironment input_var_a input_var_b ha_lt' hb_lt' hNbp
  refine ⟨by rw [hqval]; exact hqlt,
    CrtMul.crtMul_completeness (i₀ + 1 + (qBitsFoldT - 1)) input_var_a input_var_b env h_pvAB,
    ⟨fun k => by
        rw [foldLhsC_eval_eq env.toEnvironment input_var_a input_var_b _ hd k.val k.isLt]
        exact foldLhsT_boundN env.toEnvironment _ (numLimbs * (Ca * Cb)) (2 * (Ca * Cb)) hPv hPv5
          (cap_lhsT hcap) (cap_lhsT5 hcap (le_refl _)) k,
     foldRhsT_boundN env.toEnvironment _ input_var_target Nt Nt5 hqvar ht_lt' ht5'
       (cap_lhsT hcapT) (cap_rhsT5 hcapT hNt5)⟩, ?_⟩
  rw [foldLhsC_map_eq env.toEnvironment input_var_a input_var_b _ hd,
    foldLhsT_polyValue env.toEnvironment _ (numLimbs * (Ca * Cb)) hPv (cap_lhsT hcap),
    foldRhsT_polyValue env.toEnvironment _ input_var_target Nt hqvar ht_lt' (cap_lhsT hcapT),
    foldDNatTOf_eq env.toEnvironment input_var_a input_var_b ha_lt' hb_lt' hNbp _ (fun _ => rfl)]
  show D = (Expression.eval env.toEnvironment
    (var (F := F circomPrime) { index := i₀ })).val * P256 + RT
  show D = (env.get i₀).val * P256 + RT
  rw [hqval]
  exact (quot_reconstruct (by omega) hDmod).symm

def circuit (Ca Cb Nt Nt5 : ℕ)
    (hcap : numLimbs * (Ca * Cb) ≤ 12 * 2 ^ 128)
    (hcapT : Nt ≤ 12 * 2 ^ 128) (hNt : Nt ≤ 12 * 2 ^ 128) (hNt5 : Nt5 ≤ 6 * 2 ^ 128) :
    FormalAssertion (F circomPrime) Inputs where
  main := main
  Assumptions := Assumptions Ca Cb Nt Nt5
  Spec := Spec
  soundness := soundness Ca Cb Nt Nt5 hcap hcapT hNt5
  completeness := completeness Ca Cb Nt Nt5 hcap hcapT hNt hNt5

/-! ## Stability of the witnessed data -/

lemma tvec_getElem_eval_eq {x : Var TVec (F circomPrime)}
    {env env' : ProverEnvironment (F circomPrime)} (h : eval env x = eval env' x)
    (i : ℕ) (hi : i < 2 * numLimbs - 1) :
    Expression.eval env.toEnvironment (x[i]'hi)
      = Expression.eval env'.toEnvironment (x[i]'hi) := by
  rw [ProvableType.getElem_eval_fields_prover (env := env) x i hi,
    ProvableType.getElem_eval_fields_prover (env := env') x i hi]
  exact congrArg (fun y : TVec (F circomPrime) => y[i]'hi) h

lemma foldLhsT_stable {E1 E2 : Environment (F circomPrime)}
    (Pv : Vector (Expression (F circomPrime)) (2 * numLimbs - 1))
    (h : ∀ (i : ℕ) (hi : i < 2 * numLimbs - 1),
      Expression.eval E1 (Pv[i]'hi) = Expression.eval E2 (Pv[i]'hi)) :
    Vector.map (Expression.eval E1) (foldLhsT Pv)
      = Vector.map (Expression.eval E2) (foldLhsT Pv) := by
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_map]
  have hi4 : i < 4 := hi
  have h4 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases h4 with rfl | rfl | rfl | rfl
  · rw [show Expression.eval E1 (foldLhsT Pv)[0]
        = Expression.eval E1 Pv[0] + ((cFold : ℕ) : F circomPrime) * Expression.eval E1 Pv[4]
          + ((offTNat 0 : ℕ) : F circomPrime) from rfl,
      show Expression.eval E2 (foldLhsT Pv)[0]
        = Expression.eval E2 Pv[0] + ((cFold : ℕ) : F circomPrime) * Expression.eval E2 Pv[4]
          + ((offTNat 0 : ℕ) : F circomPrime) from rfl, h 0 (by decide), h 4 (by decide)]
  · rw [show Expression.eval E1 (foldLhsT Pv)[1]
        = Expression.eval E1 Pv[1] + ((cFold : ℕ) : F circomPrime) * Expression.eval E1 Pv[5]
          + ((offTNat 1 : ℕ) : F circomPrime) from rfl,
      show Expression.eval E2 (foldLhsT Pv)[1]
        = Expression.eval E2 Pv[1] + ((cFold : ℕ) : F circomPrime) * Expression.eval E2 Pv[5]
          + ((offTNat 1 : ℕ) : F circomPrime) from rfl, h 1 (by decide), h 5 (by decide)]
  · rw [show Expression.eval E1 (foldLhsT Pv)[2]
        = Expression.eval E1 Pv[2] + ((cFold : ℕ) : F circomPrime) * Expression.eval E1 Pv[6]
          + ((offTNat 2 : ℕ) : F circomPrime) from rfl,
      show Expression.eval E2 (foldLhsT Pv)[2]
        = Expression.eval E2 Pv[2] + ((cFold : ℕ) : F circomPrime) * Expression.eval E2 Pv[6]
          + ((offTNat 2 : ℕ) : F circomPrime) from rfl, h 2 (by decide), h 6 (by decide)]
  · rw [show Expression.eval E1 (foldLhsT Pv)[3]
        = Expression.eval E1 Pv[3] + ((offTNat 3 : ℕ) : F circomPrime) from rfl,
      show Expression.eval E2 (foldLhsT Pv)[3]
        = Expression.eval E2 Pv[3] + ((offTNat 3 : ℕ) : F circomPrime) from rfl, h 3 (by decide)]

lemma foldRhsT_stable {E1 E2 : Environment (F circomPrime)}
    (q : Expression (F circomPrime))
    (T : Vector (Expression (F circomPrime)) (2 * numLimbs - 1))
    (hq : Expression.eval E1 q = Expression.eval E2 q)
    (hT : ∀ (i : ℕ) (hi : i < 2 * numLimbs - 1),
      Expression.eval E1 (T[i]'hi) = Expression.eval E2 (T[i]'hi)) :
    Vector.map (Expression.eval E1) (foldRhsT q T)
      = Vector.map (Expression.eval E2) (foldRhsT q T) := by
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_map]
  have hi4 : i < 4 := hi
  have h4 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases h4 with rfl | rfl | rfl | rfl
  · rw [show Expression.eval E1 (foldRhsT q T)[0]
        = Expression.eval E1 q * ((pNat 0 : ℕ) : F circomPrime)
          + (Expression.eval E1 T[0]
            + ((cFold : ℕ) : F circomPrime) * Expression.eval E1 T[4]) from rfl,
      show Expression.eval E2 (foldRhsT q T)[0]
        = Expression.eval E2 q * ((pNat 0 : ℕ) : F circomPrime)
          + (Expression.eval E2 T[0]
            + ((cFold : ℕ) : F circomPrime) * Expression.eval E2 T[4]) from rfl,
      hq, hT 0 (by decide), hT 4 (by decide)]
  · rw [show Expression.eval E1 (foldRhsT q T)[1]
        = Expression.eval E1 q * ((pNat 1 : ℕ) : F circomPrime)
          + (Expression.eval E1 T[1]
            + ((cFold : ℕ) : F circomPrime) * Expression.eval E1 T[5]) from rfl,
      show Expression.eval E2 (foldRhsT q T)[1]
        = Expression.eval E2 q * ((pNat 1 : ℕ) : F circomPrime)
          + (Expression.eval E2 T[1]
            + ((cFold : ℕ) : F circomPrime) * Expression.eval E2 T[5]) from rfl,
      hq, hT 1 (by decide), hT 5 (by decide)]
  · rw [show Expression.eval E1 (foldRhsT q T)[2]
        = Expression.eval E1 q * ((pNat 2 : ℕ) : F circomPrime)
          + (Expression.eval E1 T[2]
            + ((cFold : ℕ) : F circomPrime) * Expression.eval E1 T[6]) from rfl,
      show Expression.eval E2 (foldRhsT q T)[2]
        = Expression.eval E2 q * ((pNat 2 : ℕ) : F circomPrime)
          + (Expression.eval E2 T[2]
            + ((cFold : ℕ) : F circomPrime) * Expression.eval E2 T[6]) from rfl,
      hq, hT 2 (by decide), hT 6 (by decide)]
  · rw [show Expression.eval E1 (foldRhsT q T)[3]
        = Expression.eval E1 q * ((pNat 3 : ℕ) : F circomPrime)
          + Expression.eval E1 T[3] from rfl,
      show Expression.eval E2 (foldRhsT q T)[3]
        = Expression.eval E2 q * ((pNat 3 : ℕ) : F circomPrime)
          + Expression.eval E2 T[3] from rfl,
      hq, hT 3 (by decide)]

lemma foldRTNat_stable (T : Var TVec (F circomPrime))
    {env env' : ProverEnvironment (F circomPrime)} (h : eval env T = eval env' T) :
    foldRTNat env.toEnvironment T = foldRTNat env'.toEnvironment T := by
  unfold foldRTNat
  rw [tvec_getElem_eval_eq h 0 (by decide), tvec_getElem_eval_eq h 1 (by decide),
    tvec_getElem_eval_eq h 2 (by decide), tvec_getElem_eval_eq h 3 (by decide),
    tvec_getElem_eval_eq h 4 (by decide), tvec_getElem_eval_eq h 5 (by decide),
    tvec_getElem_eval_eq h 6 (by decide)]

lemma qNatT_stable (input : Var Inputs (F circomPrime))
    {env env' : ProverEnvironment (F circomPrime)}
    (ha : eval env input.a = eval env' input.a) (hb : eval env input.b = eval env' input.b)
    (ht : eval env input.target = eval env' input.target) :
    qNatT env.toEnvironment input = qNatT env'.toEnvironment input := by
  unfold qNatT foldDNatT
  rw [MulModFold.convNat_stable input.a input.b ha hb 0,
    MulModFold.convNat_stable input.a input.b ha hb 1,
    MulModFold.convNat_stable input.a input.b ha hb 2,
    MulModFold.convNat_stable input.a input.b ha hb 3,
    MulModFold.convNat_stable input.a input.b ha hb 4,
    MulModFold.convNat_stable input.a input.b ha hb 5,
    MulModFold.convNat_stable input.a input.b ha hb 6,
    foldRTNat_stable input.target ht]

attribute [local irreducible] CrtMul.crtMul RangeCheck.circuit GroupedEqXV.circuit

theorem computableWitnesses (Ca Cb Nt Nt5 : ℕ)
    (hcap : numLimbs * (Ca * Cb) ≤ 12 * 2 ^ 128)
    (hcapT : Nt ≤ 12 * 2 ^ 128) (hNt : Nt ≤ 12 * 2 ^ 128) (hNt5 : Nt5 ≤ 6 * 2 ^ 128) :
    (circuit Ca Cb Nt Nt5 hcap hcapT hNt hNt5).ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition
      input env env') ((main input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main
  let qc : Circuit (F circomPrime) (Expression (F circomPrime)) :=
    Circuit.witnessField fun e => ((qNatT e.toEnvironment input : ℕ) : F circomPrime)
  let qv := qc.output offset
  let rcOff := offset + qc.localLength offset
  let rcc : Circuit (F circomPrime) Unit :=
    assertion (RangeCheck.circuit qBitsFoldT (by decide) (by decide)) qv
  let pcOff := rcOff + rcc.localLength rcOff
  let pcv := (CrtMul.crtMul input.a input.b).output pcOff
  let eqOff := pcOff + (CrtMul.crtMul input.a input.b).localLength pcOff
  have h_qlen : qc.localLength offset = 1 := by
    simp [qc, circuit_norm]
  have h_pclen : (CrtMul.crtMul input.a input.b).localLength pcOff = numLimbs :=
    CrtMul.crtMul_localLength pcOff input.a input.b
  have h_qvar : qv = var (F := F circomPrime) { index := offset } := rfl
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.witnessField_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.pure_structuralComputableWitnesses_iff,
    and_true]
  and_intros
  · intro _ h_input
    have ha : eval env input.a = eval env' input.a := by
      simpa [circuit_norm] using congrArg (fun x : Inputs (F circomPrime) => x.a) h_input
    have hb : eval env input.b = eval env' input.b := by
      simpa [circuit_norm] using congrArg (fun x : Inputs (F circomPrime) => x.b) h_input
    have ht : eval env input.target = eval env' input.target := by
      simpa [circuit_norm] using congrArg (fun x : Inputs (F circomPrime) => x.target) h_input
    rw [qNatT_stable input ha hb ht]
  · exact Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
      (RangeCheck.circuit qBitsFoldT (by decide) (by decide)) input qv rcOff
      (by
        intro k e1 e2 hle h_agree _
        have hk : offset + 1 ≤ k := by
          dsimp only [rcOff] at hle; rw [h_qlen] at hle; omega
        rw [h_qvar]
        simpa [circuit_norm] using h_agree offset (by omega))
      (RangeCheck.computableWitnesses qBitsFoldT (by decide) (by decide)) env env'
  · exact CrtMul.crtMul_structuralComputableWitnesses input input.a input.b pcOff
      (by
        intro k e1 e2 _ _ h_input
        have ha : eval e1 input.a = eval e2 input.a := by
          simpa [circuit_norm] using congrArg (fun x : Inputs (F circomPrime) => x.a) h_input
        have hb : eval e1 input.b = eval e2 input.b := by
          simpa [circuit_norm] using congrArg (fun x : Inputs (F circomPrime) => x.b) h_input
        exact ⟨ha, hb⟩)
      env env'
  · exact Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
      (GroupedEqXV.circuit 64 gfFold posOfFold 3 vFoldTL vFoldTR hgvFoldT (by norm_num)) input
      { lhs := foldLhsC pcv, rhs := foldRhsT qv input.target } eqOff
      (by
        intro k e1 e2 hle h_agree h_input
        have hk_pc : pcOff + numLimbs ≤ k := by
          dsimp only [eqOff] at hle; rw [h_pclen] at hle; omega
        have hk_q : offset + 1 ≤ k := by
          dsimp only [eqOff, pcOff, rcOff] at hle; rw [h_qlen] at hle; omega
        have hq : Expression.eval e1.toEnvironment (var (F := F circomPrime) { index := offset })
            = Expression.eval e2.toEnvironment (var (F := F circomPrime) { index := offset }) :=
          h_agree offset (by omega)
        have ht : eval e1 input.target = eval e2 input.target := by
          simpa [circuit_norm] using congrArg (fun x : Inputs (F circomPrime) => x.target) h_input
        have hPc : Vector.map (Expression.eval e1.toEnvironment) pcv
            = Vector.map (Expression.eval e2.toEnvironment) pcv :=
          CrtMul.crtMul_output_stable pcOff input.a input.b h_agree hk_pc
        have hPc_i : ∀ (i : ℕ) (hi : i < numLimbs),
            Expression.eval e1.toEnvironment (pcv[i]'hi)
              = Expression.eval e2.toEnvironment (pcv[i]'hi) := by
          intro i hi
          have := congrArg (fun v : Vector (F circomPrime) numLimbs => v[i]'hi) hPc
          simpa only [Vector.getElem_map] using this
        have ht_i : ∀ (i : ℕ) (hi : i < 2 * numLimbs - 1),
            Expression.eval e1.toEnvironment (input.target[i]'hi)
              = Expression.eval e2.toEnvironment (input.target[i]'hi) :=
          fun i hi => tvec_getElem_eval_eq ht i hi
        have hL := foldLhsC_stable (E1 := e1.toEnvironment) (E2 := e2.toEnvironment) pcv hPc_i
        have hR := foldRhsT_stable (E1 := e1.toEnvironment) (E2 := e2.toEnvironment)
          qv input.target (by rw [h_qvar]; exact hq) ht_i
        simp only [circuit_norm]
        rw [hL, hR])
      (GroupedEqXV.computableWitnesses 64 gfFold posOfFold 3 vFoldTL vFoldTR hgvFoldT (by norm_num))
      env env'

end MulModFoldT
end Solution.Secp256k1ScalarMul

