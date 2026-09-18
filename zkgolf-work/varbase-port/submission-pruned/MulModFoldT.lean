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

/-! ## Stability of the witnessed data -/

lemma tvec_getElem_eval_eq {x : Var TVec (F circomPrime)}
    {env env' : ProverEnvironment (F circomPrime)} (h : eval env x = eval env' x)
    (i : ℕ) (hi : i < 2 * numLimbs - 1) :
    Expression.eval env.toEnvironment (x[i]'hi)
      = Expression.eval env'.toEnvironment (x[i]'hi) := by
  rw [ProvableType.getElem_eval_fields_prover (env := env) x i hi,
    ProvableType.getElem_eval_fields_prover (env := env') x i hi]
  exact congrArg (fun y : TVec (F circomPrime) => y[i]'hi) h

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

attribute [local irreducible] CrtMul.crtMul RangeCheck.circuit GroupedEqXV.circuit

end MulModFoldT
end Solution.Secp256k1ScalarMul
