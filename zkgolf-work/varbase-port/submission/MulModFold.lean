import Solution.Secp256k1ScalarMul.ParamsFold
import Solution.Secp256k1ScalarMul.CrtMul
import Solution.Secp256k1ScalarMul.MulModTargetW2
import Solution.Secp256k1ScalarMul.InterpMul
import Solution.Secp256k1ScalarMul.RangeCheck
import Challenge.Utils.ComputableWitnessLemmas

/-!
# Folded modular-multiplication certificate

Certifies `target ≡ a·b (mod p)` for the secp256k1 base prime
`p = 2^256 − 2^32 − 977`, exploiting its pseudo-Mersenne shape.

Where the unfolded certificate (`MulModTarget3`) asserts the 7-position
integer identity `a·b + 3p = q·p + target` with a full 256-bit quotient
(4 witnesses + 252 range-check rows) and a 3-carry grouped equality, this
version first *folds* the product back onto 4 positions using
`2^256 ≡ cFold (mod p)`:

  `d_k = c_k + cFold · c_{k+4}`   (`k < 3`),  `d_3 = c_3`

which is a free linear recombination of the interpolated product
coefficients.  With `D = Σ d_k 2^{64k} + 3p` one has `D + p·M = a·b + 3p`
for `M = Σ_{k<3} c_{k+4} 2^{64k}`, hence `D ≡ a·b (mod p)`, and `D < 25·2^320`
makes the quotient `q = (D − target)/p` a **single wire of 69 bits**.
The grouped equality then needs a single 101-bit carry.
-/

set_option exponentiation.threshold 400

namespace Solution.Secp256k1ScalarMul
namespace MulModFold

open MulMod
open Solution.Secp256k1ScalarMul.Limbs

structure Inputs (F : Type) where
  a : Emu F
  b : Emu F
  target : Emu F
deriving ProvableStruct

/-- Constant offset digits, `Σ offNat k · 2^{64k} = 3·p`, packed into four
positions (the top digit absorbs the overflow and is `< 3·2^64`). -/
def offNat (k : ℕ) : ℕ :=
  if k = 0 then 3 * P256 % 2 ^ 64
  else if k = 1 then 3 * P256 / 2 ^ 64 % 2 ^ 64
  else if k = 2 then 3 * P256 / 2 ^ 128 % 2 ^ 64
  else 3 * P256 / 2 ^ 192

/-- The 64-bit limbs of the modulus. -/
def pNat (k : ℕ) : ℕ := limbOfNat P256 k

/-! ## Pure arithmetic facts -/

lemma cFold_add : cFold + P256 = 2 ^ 256 := by decide

lemma offNat_sum :
    offNat 0 + offNat 1 * 2 ^ 64 + offNat 2 * 2 ^ 128 + offNat 3 * 2 ^ 192 = 3 * P256 := by
  decide

lemma offNat_lt (k : ℕ) : offNat k < 3 * 2 ^ 64 := by
  unfold offNat; split_ifs <;> decide

lemma pNat_sum : pNat 0 + pNat 1 * 2 ^ 64 + pNat 2 * 2 ^ 128 + pNat 3 * 2 ^ 192 = P256 := by
  decide

lemma pNat_lt (k : ℕ) : pNat k < 2 ^ 64 :=
  Nat.mod_lt _ (Nat.two_pow_pos 64)

lemma p_gt : 2 ^ 255 < P256 := by decide

set_option exponentiation.threshold 400 in
/-- The pseudo-Mersenne fold identity. -/
lemma fold_identity (c0 c1 c2 c3 c4 c5 c6 : ℕ) :
    ((c0 + cFold * c4 + offNat 0) + (c1 + cFold * c5 + offNat 1) * 2 ^ 64
        + (c2 + cFold * c6 + offNat 2) * 2 ^ 128 + (c3 + offNat 3) * 2 ^ 192)
      + P256 * (c4 + c5 * 2 ^ 64 + c6 * 2 ^ 128)
    = (c0 + c1 * 2 ^ 64 + c2 * 2 ^ 128 + c3 * 2 ^ 192 + c4 * 2 ^ 256 + c5 * 2 ^ 320
        + c6 * 2 ^ 384) + 3 * P256 := by
  have hstep :
      ((c0 + cFold * c4 + offNat 0) + (c1 + cFold * c5 + offNat 1) * 2 ^ 64
        + (c2 + cFold * c6 + offNat 2) * 2 ^ 128 + (c3 + offNat 3) * 2 ^ 192)
      + P256 * (c4 + c5 * 2 ^ 64 + c6 * 2 ^ 128)
      = (c0 + c1 * 2 ^ 64 + c2 * 2 ^ 128 + c3 * 2 ^ 192)
        + (cFold + P256) * (c4 + c5 * 2 ^ 64 + c6 * 2 ^ 128)
        + (offNat 0 + offNat 1 * 2 ^ 64 + offNat 2 * 2 ^ 128 + offNat 3 * 2 ^ 192) := by
    ring
  rw [hstep, cFold_add, offNat_sum]
  ring

/-- Final congruence step. -/
lemma target_congr {A Bv T q M D : ℕ}
    (hD : D + P256 * M = A * Bv + 3 * P256) (hEq : D = q * P256 + T) :
    T % P256 = A * Bv % P256 := by
  have h : T + P256 * (q + M) = A * Bv + P256 * 3 := by
    rw [hEq] at hD; ring_nf at hD ⊢; omega
  have h2 : (T + P256 * (q + M)) % P256 = (A * Bv + P256 * 3) % P256 := by rw [h]
  rwa [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left] at h2

/-- `D ≡ a·b (mod p)`. -/
lemma foldD_mod {A Bv M D : ℕ} (hD : D + P256 * M = A * Bv + 3 * P256) :
    D % P256 = A * Bv % P256 := by
  have h : (D + P256 * M) % P256 = (A * Bv + P256 * 3) % P256 := by rw [hD]; ring_nf
  rwa [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left] at h

/-- Reconstruct the quotient identity from divisibility. -/
lemma quot_reconstruct {D T : ℕ} (hDT : T ≤ D) (hmod : D % P256 = T % P256) :
    (D - T) / P256 * P256 + T = D := by
  have hdvd : P256 ∣ (D - T) := (Nat.modEq_iff_dvd' hDT).mp hmod.symm
  rw [Nat.div_mul_cancel hdvd]
  omega

/-! ## Expression-level pieces -/

def cfE : Expression (F circomPrime) := (((cFold : ℕ) : F circomPrime) : Expression (F circomPrime))

def offE (k : ℕ) : Expression (F circomPrime) :=
  (((offNat k : ℕ) : F circomPrime) : Expression (F circomPrime))

def pElim (k : ℕ) : Expression (F circomPrime) :=
  (((pNat k : ℕ) : F circomPrime) : Expression (F circomPrime))

/-- The folded left-hand side: four positions carrying `a·b + 3p (mod p)`. -/
def foldLhs (Pc : Vector (Expression (F circomPrime)) (2 * numLimbs - 1)) :
    Vector (Expression (F circomPrime)) numLimbs :=
  #v[ Pc[0] + cfE * Pc[4] + offE 0,
      Pc[1] + cfE * Pc[5] + offE 1,
      Pc[2] + cfE * Pc[6] + offE 2,
      Pc[3] + offE 3 ]

/-- The right-hand side: `q·p + target`, affine because `p` is a constant. -/
def foldRhs (q : Expression (F circomPrime)) (t : Var Emu (F circomPrime)) :
    Vector (Expression (F circomPrime)) numLimbs :=
  #v[ q * pElim 0 + t[0], q * pElim 1 + t[1], q * pElim 2 + t[2], q * pElim 3 + t[3] ]

/-- Convolution coefficient of the two operands, in ℕ. -/
def convNat (env : Environment (F circomPrime)) (a b : Var Emu (F circomPrime)) (k : ℕ) : ℕ :=
  ∑ i : Fin numLimbs, if h : i.val ≤ k ∧ k - i.val < numLimbs then
    (Expression.eval env (a[i.val]'i.isLt)).val
      * (Expression.eval env (b[k - i.val]'h.2)).val else 0

/-- The folded left-hand value `D`. -/
def foldDNat (env : Environment (F circomPrime)) (a b : Var Emu (F circomPrime)) : ℕ :=
  (convNat env a b 0 + cFold * convNat env a b 4 + offNat 0)
    + (convNat env a b 1 + cFold * convNat env a b 5 + offNat 1) * 2 ^ 64
    + (convNat env a b 2 + cFold * convNat env a b 6 + offNat 2) * 2 ^ 128
    + (convNat env a b 3 + offNat 3) * 2 ^ 192

/-- The witnessed quotient `q = (D − target)/p`. -/
def qNat (env : Environment (F circomPrime)) (input : Var Inputs (F circomPrime)) : ℕ :=
  (foldDNat env input.a input.b
    - BigInt.value 64 (Vector.map (Expression.eval env) input.target)) / P256

/-! ## `polyValue` bridges -/

lemma polyValue_four (v : Vector (F circomPrime) 4) :
    polyValue 64 v = v[0].val + v[1].val * 2 ^ 64 + v[2].val * 2 ^ 128 + v[3].val * 2 ^ 192 := by
  simp only [polyValue, Fin.sum_univ_four]
  norm_num

lemma polyValue_seven (v : Vector (F circomPrime) 7) :
    polyValue 64 v = v[0].val + v[1].val * 2 ^ 64 + v[2].val * 2 ^ 128 + v[3].val * 2 ^ 192
      + v[4].val * 2 ^ 256 + v[5].val * 2 ^ 320 + v[6].val * 2 ^ 384 := by
  simp only [polyValue, Fin.sum_univ_seven]
  norm_num

lemma polyValue_seven_map (env : Environment (F circomPrime))
    (v : Vector (Expression (F circomPrime)) 7) :
    polyValue 64 (Vector.map (Expression.eval env) v)
      = (Expression.eval env v[0]).val + (Expression.eval env v[1]).val * 2 ^ 64
        + (Expression.eval env v[2]).val * 2 ^ 128 + (Expression.eval env v[3]).val * 2 ^ 192
        + (Expression.eval env v[4]).val * 2 ^ 256 + (Expression.eval env v[5]).val * 2 ^ 320
        + (Expression.eval env v[6]).val * 2 ^ 384 := by
  rw [polyValue_seven]
  simp only [Vector.getElem_map]

/-- The folded value expressed through the product coefficients. -/
def foldDNatOf (env : Environment (F circomPrime))
    (Pv : Vector (Expression (F circomPrime)) (2 * numLimbs - 1)) : ℕ :=
  ((Expression.eval env Pv[0]).val + cFold * (Expression.eval env Pv[4]).val + offNat 0)
    + ((Expression.eval env Pv[1]).val + cFold * (Expression.eval env Pv[5]).val + offNat 1)
        * 2 ^ 64
    + ((Expression.eval env Pv[2]).val + cFold * (Expression.eval env Pv[6]).val + offNat 2)
        * 2 ^ 128
    + ((Expression.eval env Pv[3]).val + offNat 3) * 2 ^ 192

/-! ### Field-value helpers -/

lemma val_natCast_mul {c : ℕ} {x : F circomPrime} (hc : c < circomPrime)
    (h : c * x.val < circomPrime) :
    (((c : ℕ) : F circomPrime) * x).val = c * x.val := by
  have hcv : (((c : ℕ) : F circomPrime)).val = c := ZMod.val_natCast_of_lt hc
  rw [ZMod.val_mul_of_lt (by rw [hcv]; exact h), hcv]

lemma val_mul_natCast {c : ℕ} {x : F circomPrime} (hc : c < circomPrime)
    (h : x.val * c < circomPrime) :
    (x * ((c : ℕ) : F circomPrime)).val = x.val * c := by
  have hcv : (((c : ℕ) : F circomPrime)).val = c := ZMod.val_natCast_of_lt hc
  rw [ZMod.val_mul_of_lt (by rw [hcv]; exact h), hcv]

lemma cFold_lt : cFold < circomPrime := by decide

/-- Value of an LHS digit of the shape `x + cFold·y + d`. -/
lemma val_lhs_digit {Nb OB CAP : ℕ} {x y : F circomPrime} {d : ℕ}
    (hx : x.val < Nb) (hy : y.val < Nb) (hd : d < OB)
    (hNb : Nb * (1 + cFold) + OB ≤ CAP) (hCAP : CAP < circomPrime) :
    (x + ((cFold : ℕ) : F circomPrime) * y + ((d : ℕ) : F circomPrime)).val
        = x.val + cFold * y.val + d ∧
      x.val + cFold * y.val + d < CAP := by
  have hsum : x.val + cFold * y.val + d < CAP := by
    have h1 : cFold * y.val ≤ cFold * (Nb - 1) := Nat.mul_le_mul_left _ (by omega)
    have h2 : Nb * (1 + cFold) = Nb + cFold * Nb := by ring
    have h3 : cFold * (Nb - 1) ≤ cFold * Nb := Nat.mul_le_mul_left _ (by omega)
    omega
  have hpsmall : CAP < circomPrime := hCAP
  have hmul : (((cFold : ℕ) : F circomPrime) * y).val = cFold * y.val :=
    val_natCast_mul cFold_lt (by omega)
  have hdv : (((d : ℕ) : F circomPrime)).val = d :=
    ZMod.val_natCast_of_lt (by omega)
  refine ⟨?_, hsum⟩
  rw [ZMod.val_add_of_lt (by rw [hdv, ZMod.val_add_of_lt (by rw [hmul]; omega), hmul]; omega),
    ZMod.val_add_of_lt (by rw [hmul]; omega), hmul, hdv]

/-- Value of an LHS digit of the shape `x + cFold·y + d`, with *separate* caps
for the two coefficient positions.  The triangular term count of a convolution
makes the high position strictly smaller than the low one, which is what buys a
bit of carry width at the first group. -/
lemma val_lhs_digit2 {Nx Ny OB CAP : ℕ} {x y : F circomPrime} {d : ℕ}
    (hx : x.val < Nx) (hy : y.val < Ny) (hd : d < OB)
    (hNb : Nx + cFold * Ny + OB ≤ CAP) (hCAP : CAP < circomPrime) :
    (x + ((cFold : ℕ) : F circomPrime) * y + ((d : ℕ) : F circomPrime)).val
        = x.val + cFold * y.val + d ∧
      x.val + cFold * y.val + d < CAP := by
  have hsum : x.val + cFold * y.val + d < CAP := by
    have h1 : cFold * y.val ≤ cFold * (Ny - 1) := Nat.mul_le_mul_left _ (by omega)
    have h3 : cFold * (Ny - 1) ≤ cFold * Ny := Nat.mul_le_mul_left _ (by omega)
    omega
  have hpsmall : CAP < circomPrime := hCAP
  have hmul : (((cFold : ℕ) : F circomPrime) * y).val = cFold * y.val :=
    val_natCast_mul cFold_lt (by omega)
  have hdv : (((d : ℕ) : F circomPrime)).val = d :=
    ZMod.val_natCast_of_lt (by omega)
  refine ⟨?_, hsum⟩
  rw [ZMod.val_add_of_lt (by rw [hdv, ZMod.val_add_of_lt (by rw [hmul]; omega), hmul]; omega),
    ZMod.val_add_of_lt (by rw [hmul]; omega), hmul, hdv]

/-- Value of the top LHS digit, of the shape `x + d`. -/
lemma val_lhs_digit_top {Nb OB CAP : ℕ} {x : F circomPrime} {d : ℕ}
    (hx : x.val < Nb) (hd : d < OB)
    (hNb : Nb * (1 + cFold) + OB ≤ CAP) (hCAP : CAP < circomPrime) :
    (x + ((d : ℕ) : F circomPrime)).val = x.val + d ∧ x.val + d < CAP := by
  have hcpos : 1 ≤ 1 + cFold := by omega
  have hNble : Nb ≤ Nb * (1 + cFold) := Nat.le_mul_of_pos_right _ (by omega)
  have hsum : x.val + d < CAP := by omega
  have hpsmall : CAP < circomPrime := hCAP
  have hdv : (((d : ℕ) : F circomPrime)).val = d := ZMod.val_natCast_of_lt (by omega)
  exact ⟨by rw [ZMod.val_add_of_lt (by rw [hdv]; omega), hdv], hsum⟩

/-- Value of an RHS digit `q·p_k + t_k`. -/
lemma val_rhs_digit {q t : F circomPrime} {k : ℕ}
    (hq : q.val < 2 ^ 68) (ht : t.val < 3 * 2 ^ 64) :
    (q * ((pNat k : ℕ) : F circomPrime) + t).val = q.val * pNat k + t.val ∧
      q.val * pNat k + t.val < 2 ^ 133 := by
  have hpk := pNat_lt k
  have hmulb : q.val * pNat k < 2 ^ 132 := by
    calc q.val * pNat k < 2 ^ 68 * 2 ^ 64 := by
          exact Nat.mul_lt_mul_of_lt_of_le hq (by omega) (by positivity)
      _ = 2 ^ 132 := by norm_num
  have hsum : q.val * pNat k + t.val < 2 ^ 133 := by
    have : (3 : ℕ) * 2 ^ 64 < 2 ^ 132 := by decide
    have h2 : (2 : ℕ) ^ 132 + 2 ^ 132 = 2 ^ 133 := by ring
    omega
  have hpsmall : (2 : ℕ) ^ 169 < circomPrime := by decide
  have hmul : (q * ((pNat k : ℕ) : F circomPrime)).val = q.val * pNat k :=
    val_mul_natCast (by omega) (by omega)
  exact ⟨by rw [ZMod.val_add_of_lt (by rw [hmul]; omega), hmul], hsum⟩

/-! ### Digit bounds and `polyValue` of the two sides -/

/-- Digit bounds of the folded left-hand side. -/
lemma foldLhs_bound (env : Environment (F circomPrime))
    (Pv : Vector (Expression (F circomPrime)) (2 * numLimbs - 1)) (Nb : ℕ)
    (hPv : ∀ k : Fin (2 * numLimbs - 1), (Expression.eval env Pv[k.val]).val < Nb)
    (hNb : Nb * (1 + cFold) + 3 * 2 ^ 64 ≤ 13 * 2 ^ 160) :
    ∀ k : Fin numLimbs, (Expression.eval env (foldLhs Pv)[k.val]).val < 13 * 2 ^ 160 := by
  intro k
  have h0 := hPv ⟨0, by decide⟩
  have h1 := hPv ⟨1, by decide⟩
  have h2 := hPv ⟨2, by decide⟩
  have h3 := hPv ⟨3, by decide⟩
  have h4 := hPv ⟨4, by decide⟩
  have h5 := hPv ⟨5, by decide⟩
  have h6 := hPv ⟨6, by decide⟩
  fin_cases k
  · have := val_lhs_digit h0 h4 (offNat_lt 0) hNb (by decide)
    show (Expression.eval env (foldLhs Pv)[0]).val < 13 * 2 ^ 160
    rw [show Expression.eval env (foldLhs Pv)[0]
        = Expression.eval env Pv[0] + ((cFold : ℕ) : F circomPrime) * Expression.eval env Pv[4]
          + ((offNat 0 : ℕ) : F circomPrime) from rfl, this.1]
    exact this.2
  · have := val_lhs_digit h1 h5 (offNat_lt 1) hNb (by decide)
    show (Expression.eval env (foldLhs Pv)[1]).val < 13 * 2 ^ 160
    rw [show Expression.eval env (foldLhs Pv)[1]
        = Expression.eval env Pv[1] + ((cFold : ℕ) : F circomPrime) * Expression.eval env Pv[5]
          + ((offNat 1 : ℕ) : F circomPrime) from rfl, this.1]
    exact this.2
  · have := val_lhs_digit h2 h6 (offNat_lt 2) hNb (by decide)
    show (Expression.eval env (foldLhs Pv)[2]).val < 13 * 2 ^ 160
    rw [show Expression.eval env (foldLhs Pv)[2]
        = Expression.eval env Pv[2] + ((cFold : ℕ) : F circomPrime) * Expression.eval env Pv[6]
          + ((offNat 2 : ℕ) : F circomPrime) from rfl, this.1]
    exact this.2
  · have := val_lhs_digit_top h3 (offNat_lt 3) hNb (by decide)
    show (Expression.eval env (foldLhs Pv)[3]).val < 13 * 2 ^ 160
    rw [show Expression.eval env (foldLhs Pv)[3]
        = Expression.eval env Pv[3] + ((offNat 3 : ℕ) : F circomPrime) from rfl, this.1]
    exact this.2

/-- Digit bounds of the folded left-hand side, refined at position 1.

Position 1 folds convolution cell 5, whose triangular term count is only 2, so
it is bounded by the smaller cap `nfFoldL 1 = 7·2^160`. -/
lemma foldLhs_boundN (env : Environment (F circomPrime))
    (Pv : Vector (Expression (F circomPrime)) (2 * numLimbs - 1)) (Nb N5 : ℕ)
    (hPv : ∀ k : Fin (2 * numLimbs - 1), (Expression.eval env Pv[k.val]).val < Nb)
    (h5 : (Expression.eval env Pv[5]).val < N5)
    (hNb : Nb * (1 + cFold) + 3 * 2 ^ 64 ≤ 13 * 2 ^ 160)
    (hN5 : Nb + cFold * N5 + 3 * 2 ^ 64 ≤ 7 * 2 ^ 160) :
    ∀ k : Fin numLimbs, (Expression.eval env (foldLhs Pv)[k.val]).val < nfFoldL k.val := by
  have hbase := foldLhs_bound env Pv Nb hPv hNb
  intro k
  fin_cases k
  · show (Expression.eval env (foldLhs Pv)[0]).val < nfFoldL 0
    simpa only [nfFoldL, if_neg (by decide : ¬ (0 : ℕ) = 1)] using hbase ⟨0, by decide⟩
  · have h1 := hPv ⟨1, by decide⟩
    have hd := val_lhs_digit2 h1 h5 (offNat_lt 1) hN5 (by decide)
    show (Expression.eval env (foldLhs Pv)[1]).val < nfFoldL 1
    rw [show Expression.eval env (foldLhs Pv)[1]
        = Expression.eval env Pv[1] + ((cFold : ℕ) : F circomPrime) * Expression.eval env Pv[5]
          + ((offNat 1 : ℕ) : F circomPrime) from rfl, hd.1]
    simpa only [nfFoldL, if_pos (rfl : (1 : ℕ) = 1)] using hd.2
  · show (Expression.eval env (foldLhs Pv)[2]).val < nfFoldL 2
    simpa only [nfFoldL, if_neg (by decide : ¬ (2 : ℕ) = 1)] using hbase ⟨2, by decide⟩
  · show (Expression.eval env (foldLhs Pv)[3]).val < nfFoldL 3
    simpa only [nfFoldL, if_neg (by decide : ¬ (3 : ℕ) = 1)] using hbase ⟨3, by decide⟩

/-- `polyValue` of the folded left-hand side. -/
lemma foldLhs_polyValue (env : Environment (F circomPrime))
    (Pv : Vector (Expression (F circomPrime)) (2 * numLimbs - 1)) (Nb : ℕ)
    (hPv : ∀ k : Fin (2 * numLimbs - 1), (Expression.eval env Pv[k.val]).val < Nb)
    (hNb : Nb * (1 + cFold) + 3 * 2 ^ 64 ≤ 13 * 2 ^ 160) :
    polyValue 64 (Vector.map (Expression.eval env) (foldLhs Pv)) = foldDNatOf env Pv := by
  have h0 := hPv ⟨0, by decide⟩
  have h1 := hPv ⟨1, by decide⟩
  have h2 := hPv ⟨2, by decide⟩
  have h3 := hPv ⟨3, by decide⟩
  have h4 := hPv ⟨4, by decide⟩
  have h5 := hPv ⟨5, by decide⟩
  have h6 := hPv ⟨6, by decide⟩
  have e0 := (val_lhs_digit h0 h4 (offNat_lt 0) hNb (by decide)).1
  have e1 := (val_lhs_digit h1 h5 (offNat_lt 1) hNb (by decide)).1
  have e2 := (val_lhs_digit h2 h6 (offNat_lt 2) hNb (by decide)).1
  have e3 := (val_lhs_digit_top h3 (offNat_lt 3) hNb (by decide)).1
  rw [polyValue_four]
  simp only [Vector.getElem_map]
  rw [show (foldLhs Pv)[0] = Pv[0] + cfE * Pv[4] + offE 0 from rfl,
    show (foldLhs Pv)[1] = Pv[1] + cfE * Pv[5] + offE 1 from rfl,
    show (foldLhs Pv)[2] = Pv[2] + cfE * Pv[6] + offE 2 from rfl,
    show (foldLhs Pv)[3] = Pv[3] + offE 3 from rfl]
  rw [show Expression.eval env (Pv[0] + cfE * Pv[4] + offE 0)
      = Expression.eval env Pv[0] + ((cFold : ℕ) : F circomPrime) * Expression.eval env Pv[4]
        + ((offNat 0 : ℕ) : F circomPrime) from rfl,
    show Expression.eval env (Pv[1] + cfE * Pv[5] + offE 1)
      = Expression.eval env Pv[1] + ((cFold : ℕ) : F circomPrime) * Expression.eval env Pv[5]
        + ((offNat 1 : ℕ) : F circomPrime) from rfl,
    show Expression.eval env (Pv[2] + cfE * Pv[6] + offE 2)
      = Expression.eval env Pv[2] + ((cFold : ℕ) : F circomPrime) * Expression.eval env Pv[6]
        + ((offNat 2 : ℕ) : F circomPrime) from rfl,
    show Expression.eval env (Pv[3] + offE 3)
      = Expression.eval env Pv[3] + ((offNat 3 : ℕ) : F circomPrime) from rfl,
    e0, e1, e2, e3]
  rfl

/-- Digit bounds of the right-hand side. -/
lemma foldRhs_bound (env : Environment (F circomPrime))
    (q : Expression (F circomPrime)) (t : Var Emu (F circomPrime))
    (hq : (Expression.eval env q).val < 2 ^ 68)
    (ht : ∀ i : Fin numLimbs, (Expression.eval env (t[i.val]'i.isLt)).val < 3 * 2 ^ 64) :
    ∀ k : Fin numLimbs, (Expression.eval env (foldRhs q t)[k.val]).val < 2 ^ 133 := by
  intro k
  have t0 := ht ⟨0, by decide⟩
  have t1 := ht ⟨1, by decide⟩
  have t2 := ht ⟨2, by decide⟩
  have t3 := ht ⟨3, by decide⟩
  fin_cases k
  · have := val_rhs_digit (k := 0) hq t0
    show (Expression.eval env (foldRhs q t)[0]).val < 2 ^ 133
    rw [show Expression.eval env (foldRhs q t)[0]
        = Expression.eval env q * ((pNat 0 : ℕ) : F circomPrime)
          + Expression.eval env t[0] from rfl, this.1]
    exact this.2
  · have := val_rhs_digit (k := 1) hq t1
    show (Expression.eval env (foldRhs q t)[1]).val < 2 ^ 133
    rw [show Expression.eval env (foldRhs q t)[1]
        = Expression.eval env q * ((pNat 1 : ℕ) : F circomPrime)
          + Expression.eval env t[1] from rfl, this.1]
    exact this.2
  · have := val_rhs_digit (k := 2) hq t2
    show (Expression.eval env (foldRhs q t)[2]).val < 2 ^ 133
    rw [show Expression.eval env (foldRhs q t)[2]
        = Expression.eval env q * ((pNat 2 : ℕ) : F circomPrime)
          + Expression.eval env t[2] from rfl, this.1]
    exact this.2
  · have := val_rhs_digit (k := 3) hq t3
    show (Expression.eval env (foldRhs q t)[3]).val < 2 ^ 133
    rw [show Expression.eval env (foldRhs q t)[3]
        = Expression.eval env q * ((pNat 3 : ℕ) : F circomPrime)
          + Expression.eval env t[3] from rfl, this.1]
    exact this.2

lemma bigIntValue_four (v : Emu (F circomPrime)) :
    BigInt.value 64 v = v[0].val + v[1].val * 2 ^ 64 + v[2].val * 2 ^ 128 + v[3].val * 2 ^ 192 := by
  rw [BigInt.value_eq_sum]
  simp only [Fin.sum_univ_four]
  norm_num

/-- `polyValue` of the right-hand side. -/
lemma foldRhs_polyValue (env : Environment (F circomPrime))
    (q : Expression (F circomPrime)) (t : Var Emu (F circomPrime))
    (hq : (Expression.eval env q).val < 2 ^ 68)
    (ht : ∀ i : Fin numLimbs, (Expression.eval env (t[i.val]'i.isLt)).val < 3 * 2 ^ 64) :
    polyValue 64 (Vector.map (Expression.eval env) (foldRhs q t))
      = (Expression.eval env q).val * P256
        + BigInt.value 64 (Vector.map (Expression.eval env) t) := by
  have t0 := ht ⟨0, by decide⟩
  have t1 := ht ⟨1, by decide⟩
  have t2 := ht ⟨2, by decide⟩
  have t3 := ht ⟨3, by decide⟩
  have e0 := (val_rhs_digit (k := 0) hq t0).1
  have e1 := (val_rhs_digit (k := 1) hq t1).1
  have e2 := (val_rhs_digit (k := 2) hq t2).1
  have e3 := (val_rhs_digit (k := 3) hq t3).1
  rw [polyValue_four, bigIntValue_four]
  simp only [Vector.getElem_map]
  rw [show (foldRhs q t)[0] = q * pElim 0 + t[0] from rfl,
    show (foldRhs q t)[1] = q * pElim 1 + t[1] from rfl,
    show (foldRhs q t)[2] = q * pElim 2 + t[2] from rfl,
    show (foldRhs q t)[3] = q * pElim 3 + t[3] from rfl]
  rw [show Expression.eval env (q * pElim 0 + t[0])
      = Expression.eval env q * ((pNat 0 : ℕ) : F circomPrime) + Expression.eval env t[0] from rfl,
    show Expression.eval env (q * pElim 1 + t[1])
      = Expression.eval env q * ((pNat 1 : ℕ) : F circomPrime) + Expression.eval env t[1] from rfl,
    show Expression.eval env (q * pElim 2 + t[2])
      = Expression.eval env q * ((pNat 2 : ℕ) : F circomPrime) + Expression.eval env t[2] from rfl,
    show Expression.eval env (q * pElim 3 + t[3])
      = Expression.eval env q * ((pNat 3 : ℕ) : F circomPrime) + Expression.eval env t[3] from rfl,
    e0, e1, e2, e3, ← pNat_sum]
  ring

/-- Bound on the convolution coefficients. -/
lemma convNat_lt {Ca Cb : ℕ} (env : Environment (F circomPrime))
    (a b : Var Emu (F circomPrime))
    (ha : ∀ i : Fin numLimbs, (Expression.eval env (a[i.val]'i.isLt)).val < Ca)
    (hb : ∀ i : Fin numLimbs, (Expression.eval env (b[i.val]'i.isLt)).val < Cb)
    (k : ℕ) : convNat env a b k < numLimbs * (Ca * Cb) := by
  have hCa : 0 < Ca := lt_of_le_of_lt (Nat.zero_le _) (ha ⟨0, by decide⟩)
  have hCb : 0 < Cb := lt_of_le_of_lt (Nat.zero_le _) (hb ⟨0, by decide⟩)
  have hterm : ∀ i : Fin numLimbs,
      (if h : i.val ≤ k ∧ k - i.val < numLimbs then
        (Expression.eval env (a[i.val]'i.isLt)).val
          * (Expression.eval env (b[k - i.val]'h.2)).val else 0) ≤ Ca * Cb - 1 := by
    intro i
    by_cases h : i.val ≤ k ∧ k - i.val < numLimbs
    · rw [dif_pos h]
      have hbk : (Expression.eval env (b[k - i.val]'h.2)).val < Cb := hb ⟨k - i.val, h.2⟩
      have := Nat.mul_lt_mul'' (ha i) hbk
      omega
    · rw [dif_neg h]; omega
  have hsum : convNat env a b k ≤ numLimbs * (Ca * Cb - 1) := by
    unfold convNat
    calc ∑ i : Fin numLimbs, _ ≤ ∑ _i : Fin numLimbs, (Ca * Cb - 1) :=
          Finset.sum_le_sum (fun i _ => hterm i)
      _ = numLimbs * (Ca * Cb - 1) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hpos : 0 < Ca * Cb := Nat.mul_pos hCa hCb
  have : numLimbs * (Ca * Cb - 1) < numLimbs * (Ca * Cb) :=
    (Nat.mul_lt_mul_left (by decide : 0 < numLimbs)).mpr (by omega)
  omega

/-- The product coefficients are exactly the convolutions. -/
lemma coeff_eq_convNat {Ca Cb : ℕ} (env : Environment (F circomPrime))
    (a b : Var Emu (F circomPrime))
    (ha : ∀ i : Fin numLimbs, (Expression.eval env (a[i.val]'i.isLt)).val < Ca)
    (hb : ∀ i : Fin numLimbs, (Expression.eval env (b[i.val]'i.isLt)).val < Cb)
    (hbound : numLimbs * (Ca * Cb) < circomPrime) (k : Fin (2 * numLimbs - 1)) :
    (Expression.eval env ((bigIntMulNoReduce a b)[k.val])).val = convNat env a b k.val :=
  MulModTargetW2.val_coeff_gen2 env a b k ha hb hbound

lemma coeff_eq_convNat' {Ca Cb : ℕ} (env : Environment (F circomPrime))
    (a b : Var Emu (F circomPrime))
    (ha : ∀ i : Fin numLimbs, (Expression.eval env (a[i.val]'i.isLt)).val < Ca)
    (hb : ∀ i : Fin numLimbs, (Expression.eval env (b[i.val]'i.isLt)).val < Cb)
    (hbound : numLimbs * (Ca * Cb) < circomPrime) (k : ℕ) (hk : k < 2 * numLimbs - 1) :
    (Expression.eval env ((bigIntMulNoReduce a b)[k]'hk)).val = convNat env a b k :=
  MulModTargetW2.val_coeff_gen2 env a b ⟨k, hk⟩ ha hb hbound

/-- Convolution cell 5 has only **two** terms (`a₂b₃` and `a₃b₂`), so it is
below `2·Ca·Cb` rather than the uniform `numLimbs·Ca·Cb`. -/
lemma coeff5_lt {Ca Cb : ℕ} (env : Environment (F circomPrime))
    (a b : Var Emu (F circomPrime))
    (ha : ∀ i : Fin numLimbs, (Expression.eval env (a[i.val]'i.isLt)).val < Ca)
    (hb : ∀ i : Fin numLimbs, (Expression.eval env (b[i.val]'i.isLt)).val < Cb)
    (hbound : numLimbs * (Ca * Cb) < circomPrime) :
    (Expression.eval env ((bigIntMulNoReduce a b)[5])).val < 2 * (Ca * Cb) := by
  have hCa : 0 < Ca := lt_of_le_of_lt (Nat.zero_le _) (ha ⟨0, by decide⟩)
  have hCb : 0 < Cb := lt_of_le_of_lt (Nat.zero_le _) (hb ⟨0, by decide⟩)
  have hpos : 0 < Ca * Cb := Nat.mul_pos hCa hCb
  have h := MulModTargetW2.val_coeff_le_gen2_card env a b
    (⟨5, by decide⟩ : Fin (2 * numLimbs - 1)) ha hb hbound
  have hcard : (Finset.univ.filter
      (fun i : Fin numLimbs => i.val ≤ 5 ∧ 5 - i.val < numLimbs)).card = 2 := by decide
  rw [hcard] at h
  have h' : (Expression.eval env ((bigIntMulNoReduce a b)[5])).val ≤ 2 * (Ca * Cb - 1) := h
  have hsub : 2 * (Ca * Cb - 1) < 2 * (Ca * Cb) := by
    have hlt : Ca * Cb - 1 < Ca * Cb := Nat.sub_lt hpos one_pos
    omega
  exact lt_of_le_of_lt h' hsub

/-- `foldDNatOf` of the true product coefficients is `foldDNat`. -/
lemma foldDNatOf_eq {Ca Cb : ℕ} (env : Environment (F circomPrime))
    (a b : Var Emu (F circomPrime))
    (ha : ∀ i : Fin numLimbs, (Expression.eval env (a[i.val]'i.isLt)).val < Ca)
    (hb : ∀ i : Fin numLimbs, (Expression.eval env (b[i.val]'i.isLt)).val < Cb)
    (hbound : numLimbs * (Ca * Cb) < circomPrime)
    (Pv : Vector (Expression (F circomPrime)) (2 * numLimbs - 1))
    (hbridge : ∀ k : Fin (2 * numLimbs - 1),
      Expression.eval env Pv[k.val] = Expression.eval env (bigIntMulNoReduce a b)[k.val]) :
    foldDNatOf env Pv = foldDNat env a b := by
  unfold foldDNatOf foldDNat
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

/-- The key fold identity at the level of the witnessed values. -/
lemma foldDNat_identity {Ca Cb : ℕ} (env : Environment (F circomPrime))
    (a b : Var Emu (F circomPrime))
    (ha : ∀ i : Fin numLimbs, (Expression.eval env (a[i.val]'i.isLt)).val < Ca)
    (hb : ∀ i : Fin numLimbs, (Expression.eval env (b[i.val]'i.isLt)).val < Cb)
    (hbound : numLimbs * (Ca * Cb) < circomPrime) :
    foldDNat env a b
        + P256 * (convNat env a b 4 + convNat env a b 5 * 2 ^ 64
            + convNat env a b 6 * 2 ^ 128)
      = BigInt.value 64 (Vector.map (Expression.eval env) a)
          * BigInt.value 64 (Vector.map (Expression.eval env) b) + 3 * P256 := by
  have hprod : polyValue 64 (Vector.map (Expression.eval env) (bigIntMulNoReduce a b))
      = BigInt.value 64 (Vector.map (Expression.eval env) a)
        * BigInt.value 64 (Vector.map (Expression.eval env) b) :=
    MulModTargetW2.polyValue_mul_eq_gen2 env a b ha hb hbound
  rw [polyValue_seven_map] at hprod
  rw [← hprod]
  unfold foldDNat
  rw [← coeff_eq_convNat env a b ha hb hbound ⟨0, by decide⟩,
    ← coeff_eq_convNat env a b ha hb hbound ⟨1, by decide⟩,
    ← coeff_eq_convNat env a b ha hb hbound ⟨2, by decide⟩,
    ← coeff_eq_convNat env a b ha hb hbound ⟨3, by decide⟩,
    ← coeff_eq_convNat env a b ha hb hbound ⟨4, by decide⟩,
    ← coeff_eq_convNat env a b ha hb hbound ⟨5, by decide⟩,
    ← coeff_eq_convNat env a b ha hb hbound ⟨6, by decide⟩]
  exact fold_identity _ _ _ _ _ _ _

/-- `3·p ≤ D`, so the quotient is a genuine natural number. -/
lemma foldDNat_ge (env : Environment (F circomPrime)) (a b : Var Emu (F circomPrime)) :
    3 * P256 ≤ foldDNat env a b := by
  rw [← offNat_sum]
  unfold foldDNat
  gcongr <;> omega

/-- The digit cap implied by the coefficient cap. -/
lemma cap_lhs {N : ℕ} (hcap : N ≤ 12 * 2 ^ 128) :
    N * (1 + cFold) + 3 * 2 ^ 64 ≤ 13 * 2 ^ 160 := by
  have hcf : cFold = 2 ^ 32 + 977 := rfl
  rw [hcf]
  have hmul : N * (1 + (2 ^ 32 + 977)) ≤ 12 * 2 ^ 128 * (1 + (2 ^ 32 + 977)) :=
    Nat.mul_le_mul_right _ hcap
  omega

/-- The refined cap at folded position 1: cell 5 carries only two convolution
terms, so the digit stays under `7·2^160`. -/
lemma cap_lhs5 {N M : ℕ} (hcap : N ≤ 12 * 2 ^ 128) (hM : 4 * M ≤ N) :
    N + cFold * (2 * M) + 3 * 2 ^ 64 ≤ 7 * 2 ^ 160 := by
  have hcf : cFold = 2 ^ 32 + 977 := rfl
  rw [hcf]
  have h2M : 2 * M ≤ 6 * 2 ^ 128 := by omega
  have hmul : (2 ^ 32 + 977) * (2 * M) ≤ (2 ^ 32 + 977) * (6 * 2 ^ 128) :=
    Nat.mul_le_mul_left _ h2M
  omega

/-- `D < 25·2^320` whenever the product coefficients are capped. -/
lemma foldDNat_lt {Ca Cb : ℕ} (env : Environment (F circomPrime))
    (a b : Var Emu (F circomPrime))
    (ha : ∀ i : Fin numLimbs, (Expression.eval env (a[i.val]'i.isLt)).val < Ca)
    (hb : ∀ i : Fin numLimbs, (Expression.eval env (b[i.val]'i.isLt)).val < Cb)
    (hcap : numLimbs * (Ca * Cb) ≤ 12 * 2 ^ 128) :
    foldDNat env a b < 13 * 2 ^ 320 := by
  have hcapL := cap_lhs hcap
  have hdig : ∀ j k : ℕ, convNat env a b j + cFold * convNat env a b k + offNat j < 13 * 2 ^ 160 := by
    intro j k
    have hj := convNat_lt env a b ha hb j
    have hk := convNat_lt env a b ha hb k
    have hoff := offNat_lt j
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
  -- the *top* folded digit carries no `cFold` factor, so it is far smaller
  have h3 : convNat env a b 3 + offNat 3 < 12 * 2 ^ 128 + 3 * 2 ^ 64 := by
    have hj := convNat_lt env a b ha hb 3
    have hoff := offNat_lt 3
    omega
  unfold foldDNat
  omega

/-- The folded left-hand side, built directly from the four CRT-multiply digits.

`CrtMul.crtMul` already emits the *folded* product `a·b mod (X^4 − cFold)`, so
all that is left is to add the constant offset digits. -/
def foldLhsC (d : Vector (Expression (F circomPrime)) numLimbs) :
    Vector (Expression (F circomPrime)) numLimbs :=
  #v[ d[0] + offE 0, d[1] + offE 1, d[2] + offE 2, d[3] + offE 3 ]

/-- Pointwise, `foldLhsC` of the CRT digits agrees with `foldLhs` of the raw
seven-cell convolution — so every bound and `polyValue` lemma above applies. -/
lemma foldLhsC_eval_eq (env : Environment (F circomPrime))
    (a b : Var Emu (F circomPrime)) (d : Vector (Expression (F circomPrime)) numLimbs)
    (hd : ∀ k : Fin numLimbs,
      Expression.eval env d[k.val] = Expression.eval env (CrtMul.foldRawE a b)[k.val])
    (i : ℕ) (hi : i < numLimbs) :
    Expression.eval env ((foldLhsC d)[i]'hi)
      = Expression.eval env ((foldLhs (bigIntMulNoReduce a b))[i]'hi) := by
  have hi4 : i < 4 := hi
  have h4 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases h4 with rfl | rfl | rfl | rfl
  · show Expression.eval env d[0] + ((offNat 0 : ℕ) : F circomPrime) = _
    rw [hd ⟨0, by decide⟩]
    rfl
  · show Expression.eval env d[1] + ((offNat 1 : ℕ) : F circomPrime) = _
    rw [hd ⟨1, by decide⟩]
    rfl
  · show Expression.eval env d[2] + ((offNat 2 : ℕ) : F circomPrime) = _
    rw [hd ⟨2, by decide⟩]
    rfl
  · show Expression.eval env d[3] + ((offNat 3 : ℕ) : F circomPrime) = _
    rw [hd ⟨3, by decide⟩]
    rfl

lemma foldLhsC_map_eq (env : Environment (F circomPrime))
    (a b : Var Emu (F circomPrime)) (d : Vector (Expression (F circomPrime)) numLimbs)
    (hd : ∀ k : Fin numLimbs,
      Expression.eval env d[k.val] = Expression.eval env (CrtMul.foldRawE a b)[k.val]) :
    Vector.map (Expression.eval env) (foldLhsC d)
      = Vector.map (Expression.eval env) (foldLhs (bigIntMulNoReduce a b)) := by
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
  · show Expression.eval E1 d[0] + ((offNat 0 : ℕ) : F circomPrime)
      = Expression.eval E2 d[0] + ((offNat 0 : ℕ) : F circomPrime)
    rw [h 0 (by decide)]
  · show Expression.eval E1 d[1] + ((offNat 1 : ℕ) : F circomPrime)
      = Expression.eval E2 d[1] + ((offNat 1 : ℕ) : F circomPrime)
    rw [h 1 (by decide)]
  · show Expression.eval E1 d[2] + ((offNat 2 : ℕ) : F circomPrime)
      = Expression.eval E2 d[2] + ((offNat 2 : ℕ) : F circomPrime)
    rw [h 2 (by decide)]
  · show Expression.eval E1 d[3] + ((offNat 3 : ℕ) : F circomPrime)
      = Expression.eval E2 d[3] + ((offNat 3 : ℕ) : F circomPrime)
    rw [h 3 (by decide)]

def main (input : Var Inputs (F circomPrime)) : Circuit (F circomPrime) Unit := do
  let q ← witnessField fun env =>
    ((qNat env.toEnvironment input : ℕ) : F circomPrime)
  RangeCheck.circuit qBitsFold (by decide) (by decide) q
  let d ← CrtMul.crtMul input.a input.b
  GroupedEqXV.circuit 64 gfFold posOfFold 3 vFoldL vFoldR hgvFold (by norm_num)
    { lhs := foldLhsC d, rhs := foldRhs q input.target }

instance elaborated : ElaboratedCircuit (F circomPrime) Inputs unit main where
  -- q (1) + range check (qBits − 1) + folded product (4) + one carry (Wf − 1)
  localLength _ := 170
  localLength_eq := by
    intro input offset
    simp only [main, CrtMul.crtMul, circuit_norm, RangeCheck.circuit,
      GroupedEqXV.circuit, GroupedEqXV.elaborated, vFoldL, wfFold,
      GroupedEqXV.widthAllocFrom, qBitsFold, numLimbs]
  subcircuitsConsistent := by
    intro input offset
    simp +arith only [main, CrtMul.crtMul, circuit_norm, RangeCheck.circuit,
      GroupedEqXV.circuit, GroupedEqXV.elaborated]
  channelsLawful := by
    intro offset
    simp only [main, CrtMul.crtMul, circuit_norm, RangeCheck.circuit,
      GroupedEqXV.circuit, GroupedEqXV.elaborated]

def Assumptions (Ca Cb : ℕ) (input : Inputs (F circomPrime)) : Prop :=
  (∀ i : Fin numLimbs, (input.a[i.val]).val < Ca) ∧
  (∀ i : Fin numLimbs, (input.b[i.val]).val < Cb) ∧
  (∀ i : Fin numLimbs, (input.target[i.val]).val < 3 * 2 ^ 64) ∧
  BigInt.value 64 input.target < 3 * P256

def Spec (input : Inputs (F circomPrime)) : Prop :=
  BigInt.value 64 input.target % P256
    = BigInt.value 64 input.a * BigInt.value 64 input.b % P256

theorem soundness (Ca Cb : ℕ)
    (hcap : numLimbs * (Ca * Cb) ≤ 12 * 2 ^ 128) :
    FormalAssertion.Soundness (F circomPrime) main (Assumptions Ca Cb) Spec := by
  circuit_proof_start [RangeCheck.circuit, RangeCheck.Assumptions, RangeCheck.Spec,
    GroupedEqXV.circuit, GroupedEqXV.elaborated, GroupedEqXV.Assumptions, GroupedEqX.Spec]
  obtain ⟨hq_lt, hAB_ops, h_eq_impl⟩ := h_holds
  obtain ⟨ha_lt, hb_lt, ht_lt, ht_val⟩ := h_assumptions
  obtain ⟨ha_in, hb_in, ht_in⟩ := h_input
  refine ⟨?_, CrtMul.crtMul_requirements _ _ _ _⟩
  simp only [vFoldL, vFoldR, nfFoldR] at h_eq_impl
  have hd := CrtMul.crtMul_eval_bridge env (i₀ + 1 + (qBitsFold - 1))
    input_var_a input_var_b
    (CrtMul.crtMul_soundness (i₀ + 1 + (qBitsFold - 1)) input_var_a input_var_b env hAB_ops)
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
  have ht_lt' : ∀ i : Fin numLimbs,
      (Expression.eval env (input_var_target[i.val]'i.isLt)).val < 3 * 2 ^ 64 := by
    intro i
    rw [show Expression.eval env (input_var_target[i.val]'i.isLt) = input_target[i.val] from by
      rw [← ht_in]; simp only [Vector.getElem_map]]
    exact ht_lt i
  have hNbp : numLimbs * (Ca * Cb) < circomPrime := by
    have h1 : numLimbs * (Ca * Cb) ≤ numLimbs * (Ca * Cb) * (1 + cFold) :=
      Nat.le_mul_of_pos_right _ (by omega)
    have h2 : (2 : ℕ) ^ 166 < circomPrime := by decide
    omega
  have hPv : ∀ k : Fin (2 * numLimbs - 1),
      (Expression.eval env (bigIntMulNoReduce input_var_a input_var_b)[k.val]).val
        < numLimbs * (Ca * Cb) :=
    fun k => MulModTargetW2.val_coeff_lt_gen2 env input_var_a input_var_b k ha_lt' hb_lt' hNbp
  have hqv : (Expression.eval env (var (F := F circomPrime) { index := i₀ })).val < 2 ^ 68 :=
    hq_lt
  have hPv5 : (Expression.eval env (bigIntMulNoReduce input_var_a input_var_b)[5]).val
      < 2 * (Ca * Cb) :=
    coeff5_lt env input_var_a input_var_b ha_lt' hb_lt' hNbp
  have heq := h_eq_impl
    ⟨fun k => by
        rw [foldLhsC_eval_eq env input_var_a input_var_b _ hd k.val k.isLt]
        exact foldLhs_boundN env _ (numLimbs * (Ca * Cb)) (2 * (Ca * Cb)) hPv hPv5 (cap_lhs hcap)
          (cap_lhs5 hcap (le_refl _)) k,
     foldRhs_bound env _ input_var_target hqv ht_lt'⟩
  rw [foldLhsC_map_eq env input_var_a input_var_b _ hd,
    foldLhs_polyValue env _ (numLimbs * (Ca * Cb)) hPv (cap_lhs hcap),
    foldRhs_polyValue env _ input_var_target hqv ht_lt',
    foldDNatOf_eq env input_var_a input_var_b ha_lt' hb_lt' hNbp _ (fun _ => rfl), ht_in] at heq
  have hid := foldDNat_identity env input_var_a input_var_b ha_lt' hb_lt' hNbp
  rw [ha_in, hb_in] at hid
  exact target_congr hid heq

theorem completeness (Ca Cb : ℕ)
    (hcap : numLimbs * (Ca * Cb) ≤ 12 * 2 ^ 128) :
    FormalAssertion.Completeness (F circomPrime) main (Assumptions Ca Cb) Spec := by
  circuit_proof_start [RangeCheck.circuit, RangeCheck.Assumptions, RangeCheck.Spec,
    GroupedEqXV.circuit, GroupedEqXV.elaborated, GroupedEqXV.Assumptions, GroupedEqX.Spec]
  obtain ⟨hq_env, hAB_uses⟩ := h_env
  obtain ⟨ha_lt, hb_lt, ht_lt, ht_val⟩ := h_assumptions
  obtain ⟨ha_in, hb_in, ht_in⟩ := h_input
  simp only [vFoldL, vFoldR, nfFoldR]
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
  have ht_lt' : ∀ i : Fin numLimbs,
      (Expression.eval env.toEnvironment (input_var_target[i.val]'i.isLt)).val < 3 * 2 ^ 64 := by
    intro i
    rw [show Expression.eval env.toEnvironment (input_var_target[i.val]'i.isLt)
        = input_target[i.val] from by rw [← ht_in]; simp only [Vector.getElem_map]]
    exact ht_lt i
  have hNbp : numLimbs * (Ca * Cb) < circomPrime := by
    have h1 : numLimbs * (Ca * Cb) ≤ numLimbs * (Ca * Cb) * (1 + cFold) :=
      Nat.le_mul_of_pos_right _ (by omega)
    have h2 : (2 : ℕ) ^ 166 < circomPrime := by decide
    omega
  have h_pvAB := CrtMul.crtMul_usesLocalWitnesses (i₀ + 1 + (qBitsFold - 1))
    (i₀ + 1 + (qBitsFold - 1)) input_var_a input_var_b env rfl hAB_uses
  have hd := CrtMul.crtMul_eval_bridge_uses env.toEnvironment
    (i₀ + 1 + (qBitsFold - 1)) input_var_a input_var_b h_pvAB
  have hPv : ∀ k : Fin (2 * numLimbs - 1),
      (Expression.eval env.toEnvironment (bigIntMulNoReduce input_var_a input_var_b)[k.val]).val
        < numLimbs * (Ca * Cb) :=
    fun k => MulModTargetW2.val_coeff_lt_gen2 env.toEnvironment input_var_a input_var_b k
      ha_lt' hb_lt' hNbp
  -- the folded value and the quotient
  set D := foldDNat env.toEnvironment input_var_a input_var_b with hDdef
  set T := BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) input_var_target)
    with hTdef
  have hT3 : T < 3 * P256 := by rw [hTdef, ht_in]; exact ht_val
  have hDge : 3 * P256 ≤ D := foldDNat_ge env.toEnvironment input_var_a input_var_b
  have hDlt : D < 13 * 2 ^ 320 := foldDNat_lt env.toEnvironment input_var_a input_var_b
    ha_lt' hb_lt' hcap
  have hid := foldDNat_identity env.toEnvironment input_var_a input_var_b ha_lt' hb_lt' hNbp
  rw [ha_in, hb_in] at hid
  have hDmod : D % P256 = T % P256 := by
    rw [foldD_mod hid, hTdef, ht_in]
    exact h_spec.symm
  have hqdef : qNat env.toEnvironment
      { a := input_var_a, b := input_var_b, target := input_var_target } = (D - T) / P256 := rfl
  have hqlt : (D - T) / P256 < 2 ^ 68 := by
    have hp : P256 = 2 ^ 256 - 2 ^ 32 - 977 := by decide
    have hdiv : (D - T) / P256 ≤ D / P256 := Nat.div_le_div_right (by omega)
    have : D / P256 < 2 ^ 68 := by
      apply Nat.div_lt_of_lt_mul
      calc D < 13 * 2 ^ 320 := hDlt
        _ ≤ 2 ^ 68 * P256 := by rw [hp]; norm_num
    omega
  have hqval : (env.get i₀).val = (D - T) / P256 := by
    rw [hq_env, hqdef]
    exact ZMod.val_natCast_of_lt (by
      have : (2 : ℕ) ^ 104 < circomPrime := by decide
      omega)
  have hqvar : (Expression.eval env.toEnvironment
      (var (F := F circomPrime) { index := i₀ })).val < 2 ^ 68 := by
    show (env.get i₀).val < 2 ^ 68
    rw [hqval]; exact hqlt
  refine ⟨by rw [hqval]; exact hqlt,
    CrtMul.crtMul_completeness (i₀ + 1 + (qBitsFold - 1)) input_var_a input_var_b env h_pvAB,
    ⟨fun k => by
        rw [foldLhsC_eval_eq env.toEnvironment input_var_a input_var_b _ hd k.val k.isLt]
        exact foldLhs_boundN env.toEnvironment _ (numLimbs * (Ca * Cb)) (2 * (Ca * Cb)) hPv
          (coeff5_lt env.toEnvironment input_var_a input_var_b ha_lt' hb_lt' hNbp)
          (cap_lhs hcap) (cap_lhs5 hcap (le_refl _)) k,
     foldRhs_bound env.toEnvironment _ input_var_target hqvar ht_lt'⟩, ?_⟩
  rw [foldLhsC_map_eq env.toEnvironment input_var_a input_var_b _ hd,
    foldLhs_polyValue env.toEnvironment _ (numLimbs * (Ca * Cb)) hPv (cap_lhs hcap),
    foldRhs_polyValue env.toEnvironment _ input_var_target hqvar ht_lt',
    foldDNatOf_eq env.toEnvironment input_var_a input_var_b ha_lt' hb_lt' hNbp _ (fun _ => rfl)]
  show D = (Expression.eval env.toEnvironment
    (var (F := F circomPrime) { index := i₀ })).val * P256 + T
  show D = (env.get i₀).val * P256 + T
  rw [hqval]
  exact (quot_reconstruct (by omega) hDmod).symm

def circuit (Ca Cb : ℕ)
    (hcap : numLimbs * (Ca * Cb) ≤ 12 * 2 ^ 128) :
    FormalAssertion (F circomPrime) Inputs where
  main := main
  Assumptions := Assumptions Ca Cb
  Spec := Spec
  soundness := soundness Ca Cb hcap
  completeness := completeness Ca Cb hcap

lemma foldLhs_stable {E1 E2 : Environment (F circomPrime)}
    (Pv : Vector (Expression (F circomPrime)) (2 * numLimbs - 1))
    (h : ∀ (i : ℕ) (hi : i < 2 * numLimbs - 1),
      Expression.eval E1 (Pv[i]'hi) = Expression.eval E2 (Pv[i]'hi)) :
    Vector.map (Expression.eval E1) (foldLhs Pv)
      = Vector.map (Expression.eval E2) (foldLhs Pv) := by
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_map]
  have hi4 : i < 4 := hi
  have h4 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases h4 with rfl | rfl | rfl | rfl
  · rw [show Expression.eval E1 (foldLhs Pv)[0]
        = Expression.eval E1 Pv[0] + ((cFold : ℕ) : F circomPrime) * Expression.eval E1 Pv[4]
          + ((offNat 0 : ℕ) : F circomPrime) from rfl,
      show Expression.eval E2 (foldLhs Pv)[0]
        = Expression.eval E2 Pv[0] + ((cFold : ℕ) : F circomPrime) * Expression.eval E2 Pv[4]
          + ((offNat 0 : ℕ) : F circomPrime) from rfl, h 0 (by decide), h 4 (by decide)]
  · rw [show Expression.eval E1 (foldLhs Pv)[1]
        = Expression.eval E1 Pv[1] + ((cFold : ℕ) : F circomPrime) * Expression.eval E1 Pv[5]
          + ((offNat 1 : ℕ) : F circomPrime) from rfl,
      show Expression.eval E2 (foldLhs Pv)[1]
        = Expression.eval E2 Pv[1] + ((cFold : ℕ) : F circomPrime) * Expression.eval E2 Pv[5]
          + ((offNat 1 : ℕ) : F circomPrime) from rfl, h 1 (by decide), h 5 (by decide)]
  · rw [show Expression.eval E1 (foldLhs Pv)[2]
        = Expression.eval E1 Pv[2] + ((cFold : ℕ) : F circomPrime) * Expression.eval E1 Pv[6]
          + ((offNat 2 : ℕ) : F circomPrime) from rfl,
      show Expression.eval E2 (foldLhs Pv)[2]
        = Expression.eval E2 Pv[2] + ((cFold : ℕ) : F circomPrime) * Expression.eval E2 Pv[6]
          + ((offNat 2 : ℕ) : F circomPrime) from rfl, h 2 (by decide), h 6 (by decide)]
  · rw [show Expression.eval E1 (foldLhs Pv)[3]
        = Expression.eval E1 Pv[3] + ((offNat 3 : ℕ) : F circomPrime) from rfl,
      show Expression.eval E2 (foldLhs Pv)[3]
        = Expression.eval E2 Pv[3] + ((offNat 3 : ℕ) : F circomPrime) from rfl, h 3 (by decide)]

lemma foldRhs_stable {E1 E2 : Environment (F circomPrime)}
    (q : Expression (F circomPrime)) (t : Var Emu (F circomPrime))
    (hq : Expression.eval E1 q = Expression.eval E2 q)
    (ht : ∀ (i : ℕ) (hi : i < numLimbs),
      Expression.eval E1 (t[i]'hi) = Expression.eval E2 (t[i]'hi)) :
    Vector.map (Expression.eval E1) (foldRhs q t)
      = Vector.map (Expression.eval E2) (foldRhs q t) := by
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_map]
  have hi4 : i < 4 := hi
  have h4 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases h4 with rfl | rfl | rfl | rfl
  · rw [show Expression.eval E1 (foldRhs q t)[0]
        = Expression.eval E1 q * ((pNat 0 : ℕ) : F circomPrime) + Expression.eval E1 t[0] from rfl,
      show Expression.eval E2 (foldRhs q t)[0]
        = Expression.eval E2 q * ((pNat 0 : ℕ) : F circomPrime) + Expression.eval E2 t[0] from rfl,
      hq, ht 0 (by decide)]
  · rw [show Expression.eval E1 (foldRhs q t)[1]
        = Expression.eval E1 q * ((pNat 1 : ℕ) : F circomPrime) + Expression.eval E1 t[1] from rfl,
      show Expression.eval E2 (foldRhs q t)[1]
        = Expression.eval E2 q * ((pNat 1 : ℕ) : F circomPrime) + Expression.eval E2 t[1] from rfl,
      hq, ht 1 (by decide)]
  · rw [show Expression.eval E1 (foldRhs q t)[2]
        = Expression.eval E1 q * ((pNat 2 : ℕ) : F circomPrime) + Expression.eval E1 t[2] from rfl,
      show Expression.eval E2 (foldRhs q t)[2]
        = Expression.eval E2 q * ((pNat 2 : ℕ) : F circomPrime) + Expression.eval E2 t[2] from rfl,
      hq, ht 2 (by decide)]
  · rw [show Expression.eval E1 (foldRhs q t)[3]
        = Expression.eval E1 q * ((pNat 3 : ℕ) : F circomPrime) + Expression.eval E1 t[3] from rfl,
      show Expression.eval E2 (foldRhs q t)[3]
        = Expression.eval E2 q * ((pNat 3 : ℕ) : F circomPrime) + Expression.eval E2 t[3] from rfl,
      hq, ht 3 (by decide)]

/-! ## Stability of the witnessed quotient -/

lemma convNat_stable (a b : Var Emu (F circomPrime))
    {env env' : ProverEnvironment (F circomPrime)}
    (ha : eval env a = eval env' a) (hb : eval env b = eval env' b) (k : ℕ) :
    convNat env.toEnvironment a b k = convNat env'.toEnvironment a b k := by
  unfold convNat
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : i.val ≤ k ∧ k - i.val < numLimbs
  · simp only [dif_pos h]
    rw [bigInt_getElem_eval_eq ha i.val i.isLt, bigInt_getElem_eval_eq hb (k - i.val) h.2]
  · simp only [dif_neg h]

lemma qNat_stable (input : Var Inputs (F circomPrime))
    {env env' : ProverEnvironment (F circomPrime)}
    (ha : eval env input.a = eval env' input.a) (hb : eval env input.b = eval env' input.b)
    (ht : eval env input.target = eval env' input.target) :
    qNat env.toEnvironment input = qNat env'.toEnvironment input := by
  unfold qNat foldDNat
  rw [convNat_stable input.a input.b ha hb 0, convNat_stable input.a input.b ha hb 1,
    convNat_stable input.a input.b ha hb 2, convNat_stable input.a input.b ha hb 3,
    convNat_stable input.a input.b ha hb 4, convNat_stable input.a input.b ha hb 5,
    convNat_stable input.a input.b ha hb 6, bigInt_map_eval_eq_of_eval_eq ht]

attribute [local irreducible] CrtMul.crtMul RangeCheck.circuit GroupedEqXV.circuit

theorem computableWitnesses (Ca Cb : ℕ)
    (hcap : numLimbs * (Ca * Cb) ≤ 12 * 2 ^ 128) :
    (circuit Ca Cb hcap).ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition
      input env env') ((main input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main
  let qc : Circuit (F circomPrime) (Expression (F circomPrime)) :=
    Circuit.witnessField fun e => ((qNat e.toEnvironment input : ℕ) : F circomPrime)
  let qv := qc.output offset
  let rcOff := offset + qc.localLength offset
  let rcc : Circuit (F circomPrime) Unit :=
    assertion (RangeCheck.circuit qBitsFold (by decide) (by decide)) qv
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
  · -- the quotient witness reads only the input
    intro _ h_input
    have ha : eval env input.a = eval env' input.a := by
      simpa [circuit_norm] using congrArg (fun x : Inputs (F circomPrime) => x.a) h_input
    have hb : eval env input.b = eval env' input.b := by
      simpa [circuit_norm] using congrArg (fun x : Inputs (F circomPrime) => x.b) h_input
    have ht : eval env input.target = eval env' input.target := by
      simpa [circuit_norm] using congrArg (fun x : Inputs (F circomPrime) => x.target) h_input
    rw [qNat_stable input ha hb ht]
  · -- the range check on the quotient wire
    exact Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
      (RangeCheck.circuit qBitsFold (by decide) (by decide)) input qv rcOff
      (by
        intro k e1 e2 hle h_agree _
        have hk : offset + 1 ≤ k := by
          dsimp only [rcOff] at hle; rw [h_qlen] at hle; omega
        rw [h_qvar]
        simpa [circuit_norm] using h_agree offset (by omega))
      (RangeCheck.computableWitnesses qBitsFold (by decide) (by decide)) env env'
  · -- the folded (CRT) product
    exact CrtMul.crtMul_structuralComputableWitnesses input input.a input.b pcOff
      (by
        intro k e1 e2 _ _ h_input
        have ha : eval e1 input.a = eval e2 input.a := by
          simpa [circuit_norm] using congrArg (fun x : Inputs (F circomPrime) => x.a) h_input
        have hb : eval e1 input.b = eval e2 input.b := by
          simpa [circuit_norm] using congrArg (fun x : Inputs (F circomPrime) => x.b) h_input
        exact ⟨ha, hb⟩)
      env env'
  · -- the grouped equality
    exact Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
      (GroupedEqXV.circuit 64 gfFold posOfFold 3 vFoldL vFoldR hgvFold (by norm_num)) input
      { lhs := foldLhsC pcv, rhs := foldRhs qv input.target } eqOff
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
        have ht_i : ∀ (i : ℕ) (hi : i < numLimbs),
            Expression.eval e1.toEnvironment (input.target[i]'hi)
              = Expression.eval e2.toEnvironment (input.target[i]'hi) :=
          fun i hi => bigInt_getElem_eval_eq ht i hi
        have hL := foldLhsC_stable (E1 := e1.toEnvironment) (E2 := e2.toEnvironment) pcv hPc_i
        have hR := foldRhs_stable (E1 := e1.toEnvironment) (E2 := e2.toEnvironment)
          qv input.target (by rw [h_qvar]; exact hq) ht_i
        simp only [circuit_norm]
        rw [hL, hR])
      (GroupedEqXV.computableWitnesses 64 gfFold posOfFold 3 vFoldL vFoldR hgvFold (by norm_num))
      env env'

end MulModFold
end Solution.Secp256k1ScalarMul
