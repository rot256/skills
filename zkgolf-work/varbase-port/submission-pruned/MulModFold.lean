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

/-- The 64-bit limbs of the modulus. -/
def pNat (k : ℕ) : ℕ := limbOfNat P256 k

/-! ## Pure arithmetic facts -/

lemma cFold_add : cFold + P256 = 2 ^ 256 := by decide

lemma pNat_sum : pNat 0 + pNat 1 * 2 ^ 64 + pNat 2 * 2 ^ 128 + pNat 3 * 2 ^ 192 = P256 := by
  decide

lemma pNat_lt (k : ℕ) : pNat k < 2 ^ 64 :=
  Nat.mod_lt _ (Nat.two_pow_pos 64)

/-- Reconstruct the quotient identity from divisibility. -/
lemma quot_reconstruct {D T : ℕ} (hDT : T ≤ D) (hmod : D % P256 = T % P256) :
    (D - T) / P256 * P256 + T = D := by
  have hdvd : P256 ∣ (D - T) := (Nat.modEq_iff_dvd' hDT).mp hmod.symm
  rw [Nat.div_mul_cancel hdvd]
  omega

/-! ## Expression-level pieces -/

def cfE : Expression (F circomPrime) := (((cFold : ℕ) : F circomPrime) : Expression (F circomPrime))

def pElim (k : ℕ) : Expression (F circomPrime) :=
  (((pNat k : ℕ) : F circomPrime) : Expression (F circomPrime))

/-- Convolution coefficient of the two operands, in ℕ. -/
def convNat (env : Environment (F circomPrime)) (a b : Var Emu (F circomPrime)) (k : ℕ) : ℕ :=
  ∑ i : Fin numLimbs, if h : i.val ≤ k ∧ k - i.val < numLimbs then
    (Expression.eval env (a[i.val]'i.isLt)).val
      * (Expression.eval env (b[k - i.val]'h.2)).val else 0

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

/-! ### Digit bounds and `polyValue` of the two sides -/

lemma bigIntValue_four (v : Emu (F circomPrime)) :
    BigInt.value 64 v = v[0].val + v[1].val * 2 ^ 64 + v[2].val * 2 ^ 128 + v[3].val * 2 ^ 192 := by
  rw [BigInt.value_eq_sum]
  simp only [Fin.sum_univ_four]
  norm_num

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

/-! ## Stability of the witnessed quotient -/

attribute [local irreducible] CrtMul.crtMul RangeCheck.circuit GroupedEqXV.circuit

end MulModFold
end Solution.Secp256k1ScalarMul
