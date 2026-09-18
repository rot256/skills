import Solution.Secp256k1ScalarMul.ParamsFold32N
import Solution.Secp256k1ScalarMul.MulModTargetW2
import Solution.Secp256k1ScalarMul.InterpMul
import Solution.Secp256k1ScalarMul.InterpMul14CW
import Solution.Secp256k1ScalarMul.RangeCheck
import Challenge.Utils.ComputableWitnessLemmas

/-!
# Mixed folded modular-multiplication certificate on 32-bit limbs

Certifies `target ≡ a·b (mod p)` for `p = 2^256 − 2^32 − 977`, in exactly the
same base-`2^32` fold as `MulModFold32`, but at a much larger product-cell cap
(`2^101` instead of `2^68`).

The point of the larger cap is that only the *first* operand needs genuine
32-bit limbs.  A four-limb `Emu` value can be re-read as eight base-`2^32`
positions by putting its 64-bit limbs at the even positions and the literal
zero expression at the odd ones — which is free — and the resulting cell cap
`8 * (2^32 * (3 * 2^64)) <= 2^101` is what this file is tuned for.

Since `2^256` is congruent to `2^32 + 977` mod `p`, in base `2^32` the fold
constant is the two tiny digits `977` and `1`, so

  `d_k = c_k + 977 * c_{k+8} + c_{k+7}`

inflates a cell only by a factor `979` (against `2^32` for a base-`2^64` fold).
The quotient is a single 72-bit wire and the grouped equality needs a single
81-bit carry, so the certificate costs `167/169` — against `176/178` for the
base-`2^64` `MulModFoldT` shape it replaces.
-/

set_option exponentiation.threshold 600

namespace Solution.Secp256k1ScalarMul
namespace MulModFold32N

open MulMod
open Solution.Secp256k1ScalarMul.Limbs

structure Inputs (F : Type) where
  a : BigInt 8 F
  b : BigInt 8 F
  target : Emu F
deriving ProvableStruct

/-- Constant offset digits, `Σ offNat32 k · 2^{32k} = 3·p`. -/
def offNat32 (k : ℕ) : ℕ :=
  if k = 0 then 3 * P256 % 2 ^ 32
  else if k = 1 then 3 * P256 / 2 ^ 32 % 2 ^ 32
  else if k = 2 then 3 * P256 / 2 ^ 64 % 2 ^ 32
  else if k = 3 then 3 * P256 / 2 ^ 96 % 2 ^ 32
  else if k = 4 then 3 * P256 / 2 ^ 128 % 2 ^ 32
  else if k = 5 then 3 * P256 / 2 ^ 160 % 2 ^ 32
  else if k = 6 then 3 * P256 / 2 ^ 192 % 2 ^ 32
  else 3 * P256 / 2 ^ 224

/-- The 32-bit limbs of the modulus. -/
def pNat32 (k : ℕ) : ℕ := P256 / 2 ^ (32 * k) % 2 ^ 32

/-! ## Pure arithmetic facts -/

lemma offNat32_sum :
    offNat32 0 + offNat32 1 * 2 ^ 32 + offNat32 2 * 2 ^ 64 + offNat32 3 * 2 ^ 96
      + offNat32 4 * 2 ^ 128 + offNat32 5 * 2 ^ 160 + offNat32 6 * 2 ^ 192
      + offNat32 7 * 2 ^ 224 = 3 * P256 := by
  decide

lemma offNat32_lt (k : ℕ) : offNat32 k < 3 * 2 ^ 32 := by
  unfold offNat32; split_ifs <;> decide

lemma pNat32_sum :
    pNat32 0 + pNat32 1 * 2 ^ 32 + pNat32 2 * 2 ^ 64 + pNat32 3 * 2 ^ 96
      + pNat32 4 * 2 ^ 128 + pNat32 5 * 2 ^ 160 + pNat32 6 * 2 ^ 192
      + pNat32 7 * 2 ^ 224 = P256 := by
  decide

lemma pNat32_lt (k : ℕ) : pNat32 k < 2 ^ 32 :=
  Nat.mod_lt _ (Nat.two_pow_pos 32)

/-- The pseudo-Mersenne fold identity in base `2^32`. -/
lemma fold_identity32 (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 : ℕ) :
    ((c0 + 977 * c8 + offNat32 0)
        + (c1 + 977 * c9 + c8 + offNat32 1) * 2 ^ 32
        + (c2 + 977 * c10 + c9 + offNat32 2) * 2 ^ 64
        + (c3 + 977 * c11 + c10 + offNat32 3) * 2 ^ 96
        + (c4 + 977 * c12 + c11 + offNat32 4) * 2 ^ 128
        + (c5 + 977 * c13 + c12 + offNat32 5) * 2 ^ 160
        + (c6 + 977 * c14 + c13 + offNat32 6) * 2 ^ 192
        + (c7 + c14 + offNat32 7) * 2 ^ 224)
      + P256 * (c8 + c9 * 2 ^ 32 + c10 * 2 ^ 64 + c11 * 2 ^ 96 + c12 * 2 ^ 128
          + c13 * 2 ^ 160 + c14 * 2 ^ 192)
    = (c0 + c1 * 2 ^ 32 + c2 * 2 ^ 64 + c3 * 2 ^ 96 + c4 * 2 ^ 128 + c5 * 2 ^ 160
        + c6 * 2 ^ 192 + c7 * 2 ^ 224 + c8 * 2 ^ 256 + c9 * 2 ^ 288 + c10 * 2 ^ 320
        + c11 * 2 ^ 352 + c12 * 2 ^ 384 + c13 * 2 ^ 416 + c14 * 2 ^ 448)
      + 3 * P256 := by
  have hM : (2 : ℕ) ^ 256 = P256 + (2 ^ 32 + 977) := by decide
  have hstep :
      ((c0 + 977 * c8 + offNat32 0)
        + (c1 + 977 * c9 + c8 + offNat32 1) * 2 ^ 32
        + (c2 + 977 * c10 + c9 + offNat32 2) * 2 ^ 64
        + (c3 + 977 * c11 + c10 + offNat32 3) * 2 ^ 96
        + (c4 + 977 * c12 + c11 + offNat32 4) * 2 ^ 128
        + (c5 + 977 * c13 + c12 + offNat32 5) * 2 ^ 160
        + (c6 + 977 * c14 + c13 + offNat32 6) * 2 ^ 192
        + (c7 + c14 + offNat32 7) * 2 ^ 224)
      + P256 * (c8 + c9 * 2 ^ 32 + c10 * 2 ^ 64 + c11 * 2 ^ 96 + c12 * 2 ^ 128
          + c13 * 2 ^ 160 + c14 * 2 ^ 192)
      = (c0 + c1 * 2 ^ 32 + c2 * 2 ^ 64 + c3 * 2 ^ 96 + c4 * 2 ^ 128 + c5 * 2 ^ 160
          + c6 * 2 ^ 192 + c7 * 2 ^ 224)
        + (P256 + (2 ^ 32 + 977))
            * (c8 + c9 * 2 ^ 32 + c10 * 2 ^ 64 + c11 * 2 ^ 96 + c12 * 2 ^ 128
              + c13 * 2 ^ 160 + c14 * 2 ^ 192)
        + (offNat32 0 + offNat32 1 * 2 ^ 32 + offNat32 2 * 2 ^ 64 + offNat32 3 * 2 ^ 96
          + offNat32 4 * 2 ^ 128 + offNat32 5 * 2 ^ 160 + offNat32 6 * 2 ^ 192
          + offNat32 7 * 2 ^ 224) := by
    ring
  rw [hstep, ← hM, offNat32_sum]
  ring

/-- Final congruence step. -/
lemma target_congr {A Bv T q M D : ℕ}
    (hD : D + P256 * M = A * Bv + 3 * P256) (hEq : D = q * P256 + T) :
    T % P256 = A * Bv % P256 := by
  have h : T + P256 * (q + M) = A * Bv + P256 * 3 := by
    rw [hEq] at hD; ring_nf at hD ⊢; omega
  have h2 : (T + P256 * (q + M)) % P256 = (A * Bv + P256 * 3) % P256 := by rw [h]
  rwa [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left] at h2

lemma foldD_mod {A Bv M D : ℕ} (hD : D + P256 * M = A * Bv + 3 * P256) :
    D % P256 = A * Bv % P256 := by
  have h : (D + P256 * M) % P256 = (A * Bv + P256 * 3) % P256 := by rw [hD]; ring_nf
  rwa [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left] at h

lemma quot_reconstruct {D T : ℕ} (hDT : T ≤ D) (hmod : D % P256 = T % P256) :
    (D - T) / P256 * P256 + T = D := by
  have hdvd : P256 ∣ (D - T) := (Nat.modEq_iff_dvd' hDT).mp hmod.symm
  rw [Nat.div_mul_cancel hdvd]
  omega

/-! ## Expression-level pieces -/

def c977E : Expression (F circomPrime) := (((977 : ℕ) : F circomPrime) : Expression (F circomPrime))

def offE (k : ℕ) : Expression (F circomPrime) :=
  (((offNat32 k : ℕ) : F circomPrime) : Expression (F circomPrime))

def pElim (k : ℕ) : Expression (F circomPrime) :=
  (((pNat32 k : ℕ) : F circomPrime) : Expression (F circomPrime))

/-- The folded left-hand side: eight positions carrying `a·b + 3p (mod p)`. -/
def foldLhs32 (Pc : Vector (Expression (F circomPrime)) 15) :
    Vector (Expression (F circomPrime)) 8 :=
  #v[ Pc[0] + c977E * Pc[8] + offE 0,
      Pc[1] + c977E * Pc[9] + Pc[8] + offE 1,
      Pc[2] + c977E * Pc[10] + Pc[9] + offE 2,
      Pc[3] + c977E * Pc[11] + Pc[10] + offE 3,
      Pc[4] + c977E * Pc[12] + Pc[11] + offE 4,
      Pc[5] + c977E * Pc[13] + Pc[12] + offE 5,
      Pc[6] + c977E * Pc[14] + Pc[13] + offE 6,
      Pc[7] + Pc[14] + offE 7 ]

/-- The right-hand side `q·p + target`; the four 64-bit target limbs sit at the
even 32-bit positions, which is free. -/
def foldRhs32 (q : Expression (F circomPrime)) (t : Var Emu (F circomPrime)) :
    Vector (Expression (F circomPrime)) 8 :=
  #v[ q * pElim 0 + t[0], q * pElim 1,
      q * pElim 2 + t[1], q * pElim 3,
      q * pElim 4 + t[2], q * pElim 5,
      q * pElim 6 + t[3], q * pElim 7 ]

/-- Convolution coefficient of the two operands, in ℕ. -/
def convNat (env : Environment (F circomPrime)) (a b : Var (BigInt 8) (F circomPrime))
    (k : ℕ) : ℕ :=
  ∑ i : Fin 8, if h : i.val ≤ k ∧ k - i.val < 8 then
    (Expression.eval env (a[i.val]'i.isLt)).val
      * (Expression.eval env (b[k - i.val]'h.2)).val else 0

/-- Number of *nonzero* terms in the `k`-th convolution cell when the second
operand's odd 32-bit positions vanish. -/
def sparseCnt (k : ℕ) : ℕ :=
  ∑ i : Fin 8, if (i.val ≤ k ∧ k - i.val < 8) ∧ (k + i.val) % 2 = 0 then 1 else 0

/-- Position-aware cap on the `k`-th convolution cell. -/
def sparseNf (k : ℕ) : ℕ := sparseCnt k * (3 * 2 ^ 96) + 1

/-- The folded left-hand value `D`. -/
def foldDNat (env : Environment (F circomPrime)) (a b : Var (BigInt 8) (F circomPrime)) : ℕ :=
  (convNat env a b 0 + 977 * convNat env a b 8 + offNat32 0)
    + (convNat env a b 1 + 977 * convNat env a b 9 + convNat env a b 8 + offNat32 1) * 2 ^ 32
    + (convNat env a b 2 + 977 * convNat env a b 10 + convNat env a b 9 + offNat32 2) * 2 ^ 64
    + (convNat env a b 3 + 977 * convNat env a b 11 + convNat env a b 10 + offNat32 3) * 2 ^ 96
    + (convNat env a b 4 + 977 * convNat env a b 12 + convNat env a b 11 + offNat32 4) * 2 ^ 128
    + (convNat env a b 5 + 977 * convNat env a b 13 + convNat env a b 12 + offNat32 5) * 2 ^ 160
    + (convNat env a b 6 + 977 * convNat env a b 14 + convNat env a b 13 + offNat32 6) * 2 ^ 192
    + (convNat env a b 7 + convNat env a b 14 + offNat32 7) * 2 ^ 224

/-! ## `polyValue` bridges -/

lemma polyValue_eight (v : Vector (F circomPrime) 8) :
    polyValue 32 v = v[0].val + v[1].val * 2 ^ 32 + v[2].val * 2 ^ 64 + v[3].val * 2 ^ 96
      + v[4].val * 2 ^ 128 + v[5].val * 2 ^ 160 + v[6].val * 2 ^ 192 + v[7].val * 2 ^ 224 := by
  simp only [polyValue, Fin.sum_univ_eight]
  norm_num

lemma polyValue_fifteen_map (env : Environment (F circomPrime))
    (v : Vector (Expression (F circomPrime)) 15) :
    polyValue 32 (Vector.map (Expression.eval env) v)
      = (Expression.eval env v[0]).val + (Expression.eval env v[1]).val * 2 ^ 32
        + (Expression.eval env v[2]).val * 2 ^ 64 + (Expression.eval env v[3]).val * 2 ^ 96
        + (Expression.eval env v[4]).val * 2 ^ 128 + (Expression.eval env v[5]).val * 2 ^ 160
        + (Expression.eval env v[6]).val * 2 ^ 192 + (Expression.eval env v[7]).val * 2 ^ 224
        + (Expression.eval env v[8]).val * 2 ^ 256 + (Expression.eval env v[9]).val * 2 ^ 288
        + (Expression.eval env v[10]).val * 2 ^ 320 + (Expression.eval env v[11]).val * 2 ^ 352
        + (Expression.eval env v[12]).val * 2 ^ 384 + (Expression.eval env v[13]).val * 2 ^ 416
        + (Expression.eval env v[14]).val * 2 ^ 448 := by
  simp only [polyValue, Fin.sum_univ_succ, Fin.sum_univ_zero, Vector.getElem_map]
  norm_num
  ring

/-- The folded value expressed through the product coefficients. -/
def foldDNatOf (env : Environment (F circomPrime))
    (Pv : Vector (Expression (F circomPrime)) 15) : ℕ :=
  ((Expression.eval env Pv[0]).val + 977 * (Expression.eval env Pv[8]).val + offNat32 0)
    + ((Expression.eval env Pv[1]).val + 977 * (Expression.eval env Pv[9]).val
        + (Expression.eval env Pv[8]).val + offNat32 1) * 2 ^ 32
    + ((Expression.eval env Pv[2]).val + 977 * (Expression.eval env Pv[10]).val
        + (Expression.eval env Pv[9]).val + offNat32 2) * 2 ^ 64
    + ((Expression.eval env Pv[3]).val + 977 * (Expression.eval env Pv[11]).val
        + (Expression.eval env Pv[10]).val + offNat32 3) * 2 ^ 96
    + ((Expression.eval env Pv[4]).val + 977 * (Expression.eval env Pv[12]).val
        + (Expression.eval env Pv[11]).val + offNat32 4) * 2 ^ 128
    + ((Expression.eval env Pv[5]).val + 977 * (Expression.eval env Pv[13]).val
        + (Expression.eval env Pv[12]).val + offNat32 5) * 2 ^ 160
    + ((Expression.eval env Pv[6]).val + 977 * (Expression.eval env Pv[14]).val
        + (Expression.eval env Pv[13]).val + offNat32 6) * 2 ^ 192
    + ((Expression.eval env Pv[7]).val + (Expression.eval env Pv[14]).val + offNat32 7) * 2 ^ 224

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

/-- Value of an interior LHS digit `x + 977·y + z + d`. -/
lemma val_lhs_digit {Nx Ny Nz M : ℕ} {x y z : F circomPrime} {d : ℕ}
    (hx : x.val < Nx) (hy : y.val < Ny) (hz : z.val < Nz) (hd : d < 3 * 2 ^ 32)
    (hM : Nx + 977 * Ny + Nz + 3 * 2 ^ 32 ≤ M) (hMp : M ≤ 2 ^ 111) :
    (x + ((977 : ℕ) : F circomPrime) * y + z + ((d : ℕ) : F circomPrime)).val
        = x.val + 977 * y.val + z.val + d ∧
      x.val + 977 * y.val + z.val + d < M := by
  have hsum : x.val + 977 * y.val + z.val + d < M := by
    have hy' : 977 * y.val ≤ 977 * (Ny - 1) := Nat.mul_le_mul_left _ (by omega)
    have hb : 977 * (Ny - 1) + 977 ≤ 977 * Ny := by
      have : 0 < Ny := by omega
      cases Ny with
      | zero => omega
      | succ n => simp only [Nat.succ_sub_one]; omega
    omega
  have hp112 : (2 : ℕ) ^ 112 < circomPrime := by decide
  have hmul : ((((977 : ℕ)) : F circomPrime) * y).val = 977 * y.val :=
    val_natCast_mul (by decide) (by omega)
  have hdv : (((d : ℕ) : F circomPrime)).val = d := ZMod.val_natCast_of_lt (by omega)
  refine ⟨?_, hsum⟩
  rw [ZMod.val_add_of_lt (by
      rw [hdv, ZMod.val_add_of_lt (by
        rw [ZMod.val_add_of_lt (by rw [hmul]; omega), hmul]; omega),
        ZMod.val_add_of_lt (by rw [hmul]; omega), hmul]
      omega),
    ZMod.val_add_of_lt (by
      rw [ZMod.val_add_of_lt (by rw [hmul]; omega), hmul]; omega),
    ZMod.val_add_of_lt (by rw [hmul]; omega), hmul, hdv]

/-- Value of the top LHS digit `x + y + d`. -/
lemma val_lhs_digit_top {Nx Ny M : ℕ} {x y : F circomPrime} {d : ℕ}
    (hx : x.val < Nx) (hy : y.val < Ny) (hd : d < 3 * 2 ^ 32)
    (hM : Nx + Ny + 3 * 2 ^ 32 ≤ M) (hMp : M ≤ 2 ^ 111) :
    (x + y + ((d : ℕ) : F circomPrime)).val = x.val + y.val + d ∧
      x.val + y.val + d < M := by
  have hsum : x.val + y.val + d < M := by omega
  have hp112 : (2 : ℕ) ^ 112 < circomPrime := by decide
  have hdv : (((d : ℕ) : F circomPrime)).val = d := ZMod.val_natCast_of_lt (by omega)
  refine ⟨?_, hsum⟩
  rw [ZMod.val_add_of_lt (by rw [hdv, ZMod.val_add_of_lt (by omega)]; omega),
    ZMod.val_add_of_lt (by omega), hdv]

/-- Value of an even RHS digit `q·p_k + t`. -/
lemma val_rhs_digit {q t : F circomPrime} {k : ℕ}
    (hq : q.val < 2 ^ 68) (ht : t.val < 3 * 2 ^ 64) :
    (q * ((pNat32 k : ℕ) : F circomPrime) + t).val = q.val * pNat32 k + t.val ∧
      q.val * pNat32 k + t.val < (2 ^ 100 + 3 * 2 ^ 64) := by
  have hpk := pNat32_lt k
  have hmulb : q.val * pNat32 k < 2 ^ 100 := by
    calc q.val * pNat32 k < 2 ^ 68 * 2 ^ 32 :=
          Nat.mul_lt_mul_of_lt_of_le hq (by omega) (by positivity)
      _ = 2 ^ 100 := by norm_num
  have hsum : q.val * pNat32 k + t.val < (2 ^ 100 + 3 * 2 ^ 64) := by
    have h1 : (3 : ℕ) * 2 ^ 64 + 2 ^ 100 ≤ (2 ^ 100 + 3 * 2 ^ 64) := by decide
    omega
  have hp : (2 : ℕ) ^ 105 < circomPrime := by decide
  have hmul : (q * ((pNat32 k : ℕ) : F circomPrime)).val = q.val * pNat32 k :=
    val_mul_natCast (by omega) (by omega)
  exact ⟨by rw [ZMod.val_add_of_lt (by rw [hmul]; omega), hmul], hsum⟩

/-- Value of an odd RHS digit `q·p_k`. -/
lemma val_rhs_digit_odd {q : F circomPrime} {k : ℕ} (hq : q.val < 2 ^ 68) :
    (q * ((pNat32 k : ℕ) : F circomPrime)).val = q.val * pNat32 k ∧
      q.val * pNat32 k < (2 ^ 100 + 3 * 2 ^ 64) := by
  have hpk := pNat32_lt k
  have hmulb : q.val * pNat32 k < 2 ^ 100 := by
    calc q.val * pNat32 k < 2 ^ 68 * 2 ^ 32 :=
          Nat.mul_lt_mul_of_lt_of_le hq (by omega) (by positivity)
      _ = 2 ^ 100 := by norm_num
  have hp : (2 : ℕ) ^ 105 < circomPrime := by decide
  refine ⟨val_mul_natCast (by omega) (by omega), by omega⟩

/-- Value of the bottom LHS digit `x + 977·y + d`. -/
lemma val_lhs_digit_two {Nx Ny M : ℕ} {x y : F circomPrime} {d : ℕ}
    (hx : x.val < Nx) (hy : y.val < Ny) (hd : d < 3 * 2 ^ 32)
    (hM : Nx + 977 * Ny + 3 * 2 ^ 32 ≤ M) (hMp : M ≤ 2 ^ 111) :
    (x + ((977 : ℕ) : F circomPrime) * y + ((d : ℕ) : F circomPrime)).val
        = x.val + 977 * y.val + d ∧
      x.val + 977 * y.val + d < M := by
  have hsum : x.val + 977 * y.val + d < M := by
    have hy' : 977 * y.val ≤ 977 * (Ny - 1) := Nat.mul_le_mul_left _ (by omega)
    have hb : 977 * (Ny - 1) + 977 ≤ 977 * Ny := by
      have : 0 < Ny := by omega
      cases Ny with
      | zero => omega
      | succ n => simp only [Nat.succ_sub_one]; omega
    omega
  have hp112 : (2 : ℕ) ^ 112 < circomPrime := by decide
  have hmul : ((((977 : ℕ)) : F circomPrime) * y).val = 977 * y.val :=
    val_natCast_mul (by decide) (by omega)
  have hdv : (((d : ℕ) : F circomPrime)).val = d := ZMod.val_natCast_of_lt (by omega)
  refine ⟨?_, hsum⟩
  rw [ZMod.val_add_of_lt (by
      rw [hdv, ZMod.val_add_of_lt (by rw [hmul]; omega), hmul]; omega),
    ZMod.val_add_of_lt (by rw [hmul]; omega), hmul, hdv]

/-! ### Digit bounds and `polyValue` of the two sides -/

/-- Digit bounds of the folded left-hand side. -/
lemma foldLhs32_bound (env : Environment (F circomPrime))
    (Pv : Vector (Expression (F circomPrime)) 15)
    (hPv : ∀ k : Fin 15, (Expression.eval env Pv[k.val]).val < sparseNf k.val) :
    ∀ k : Fin 8, (Expression.eval env (foldLhs32 Pv)[k.val]).val < nfFold32NL k.val := by
  intro k
  have h0 := hPv ⟨0, by decide⟩
  have h1 := hPv ⟨1, by decide⟩
  have h2 := hPv ⟨2, by decide⟩
  have h3 := hPv ⟨3, by decide⟩
  have h4 := hPv ⟨4, by decide⟩
  have h5 := hPv ⟨5, by decide⟩
  have h6 := hPv ⟨6, by decide⟩
  have h7 := hPv ⟨7, by decide⟩
  have h8 := hPv ⟨8, by decide⟩
  have h9 := hPv ⟨9, by decide⟩
  have h10 := hPv ⟨10, by decide⟩
  have h11 := hPv ⟨11, by decide⟩
  have h12 := hPv ⟨12, by decide⟩
  have h13 := hPv ⟨13, by decide⟩
  have h14 := hPv ⟨14, by decide⟩
  fin_cases k
  · have hd := val_lhs_digit_two (M := nfFold32NL 0) h0 h8 (offNat32_lt 0) (by decide) (by decide)
    show (Expression.eval env (foldLhs32 Pv)[0]).val < nfFold32NL 0
    rw [show Expression.eval env (foldLhs32 Pv)[0]
        = Expression.eval env Pv[0] + ((977 : ℕ) : F circomPrime) * Expression.eval env Pv[8]
          + ((offNat32 0 : ℕ) : F circomPrime) from rfl, hd.1]
    exact hd.2
  · have hd := val_lhs_digit (M := nfFold32NL 1) h1 h9 h8 (offNat32_lt 1) (by decide) (by decide)
    show (Expression.eval env (foldLhs32 Pv)[1]).val < nfFold32NL 1
    rw [show Expression.eval env (foldLhs32 Pv)[1]
        = Expression.eval env Pv[1] + ((977 : ℕ) : F circomPrime) * Expression.eval env Pv[9]
          + Expression.eval env Pv[8] + ((offNat32 1 : ℕ) : F circomPrime) from rfl, hd.1]
    exact hd.2
  · have hd := val_lhs_digit (M := nfFold32NL 2) h2 h10 h9 (offNat32_lt 2) (by decide) (by decide)
    show (Expression.eval env (foldLhs32 Pv)[2]).val < nfFold32NL 2
    rw [show Expression.eval env (foldLhs32 Pv)[2]
        = Expression.eval env Pv[2] + ((977 : ℕ) : F circomPrime) * Expression.eval env Pv[10]
          + Expression.eval env Pv[9] + ((offNat32 2 : ℕ) : F circomPrime) from rfl, hd.1]
    exact hd.2
  · have hd := val_lhs_digit (M := nfFold32NL 3) h3 h11 h10 (offNat32_lt 3) (by decide) (by decide)
    show (Expression.eval env (foldLhs32 Pv)[3]).val < nfFold32NL 3
    rw [show Expression.eval env (foldLhs32 Pv)[3]
        = Expression.eval env Pv[3] + ((977 : ℕ) : F circomPrime) * Expression.eval env Pv[11]
          + Expression.eval env Pv[10] + ((offNat32 3 : ℕ) : F circomPrime) from rfl, hd.1]
    exact hd.2
  · have hd := val_lhs_digit (M := nfFold32NL 4) h4 h12 h11 (offNat32_lt 4) (by decide) (by decide)
    show (Expression.eval env (foldLhs32 Pv)[4]).val < nfFold32NL 4
    rw [show Expression.eval env (foldLhs32 Pv)[4]
        = Expression.eval env Pv[4] + ((977 : ℕ) : F circomPrime) * Expression.eval env Pv[12]
          + Expression.eval env Pv[11] + ((offNat32 4 : ℕ) : F circomPrime) from rfl, hd.1]
    exact hd.2
  · have hd := val_lhs_digit (M := nfFold32NL 5) h5 h13 h12 (offNat32_lt 5) (by decide) (by decide)
    show (Expression.eval env (foldLhs32 Pv)[5]).val < nfFold32NL 5
    rw [show Expression.eval env (foldLhs32 Pv)[5]
        = Expression.eval env Pv[5] + ((977 : ℕ) : F circomPrime) * Expression.eval env Pv[13]
          + Expression.eval env Pv[12] + ((offNat32 5 : ℕ) : F circomPrime) from rfl, hd.1]
    exact hd.2
  · have hd := val_lhs_digit (M := nfFold32NL 6) h6 h14 h13 (offNat32_lt 6) (by decide) (by decide)
    show (Expression.eval env (foldLhs32 Pv)[6]).val < nfFold32NL 6
    rw [show Expression.eval env (foldLhs32 Pv)[6]
        = Expression.eval env Pv[6] + ((977 : ℕ) : F circomPrime) * Expression.eval env Pv[14]
          + Expression.eval env Pv[13] + ((offNat32 6 : ℕ) : F circomPrime) from rfl, hd.1]
    exact hd.2
  · have hd := val_lhs_digit_top (M := nfFold32NL 7) h7 h14 (offNat32_lt 7) (by decide) (by decide)
    show (Expression.eval env (foldLhs32 Pv)[7]).val < nfFold32NL 7
    rw [show Expression.eval env (foldLhs32 Pv)[7]
        = Expression.eval env Pv[7] + Expression.eval env Pv[14]
          + ((offNat32 7 : ℕ) : F circomPrime) from rfl, hd.1]
    exact hd.2

/-- `polyValue` of the folded left-hand side. -/
lemma foldLhs32_polyValue (env : Environment (F circomPrime))
    (Pv : Vector (Expression (F circomPrime)) 15)
    (hPv : ∀ k : Fin 15, (Expression.eval env Pv[k.val]).val < sparseNf k.val) :
    polyValue 32 (Vector.map (Expression.eval env) (foldLhs32 Pv)) = foldDNatOf env Pv := by
  have h0 := hPv ⟨0, by decide⟩
  have h1 := hPv ⟨1, by decide⟩
  have h2 := hPv ⟨2, by decide⟩
  have h3 := hPv ⟨3, by decide⟩
  have h4 := hPv ⟨4, by decide⟩
  have h5 := hPv ⟨5, by decide⟩
  have h6 := hPv ⟨6, by decide⟩
  have h7 := hPv ⟨7, by decide⟩
  have h8 := hPv ⟨8, by decide⟩
  have h9 := hPv ⟨9, by decide⟩
  have h10 := hPv ⟨10, by decide⟩
  have h11 := hPv ⟨11, by decide⟩
  have h12 := hPv ⟨12, by decide⟩
  have h13 := hPv ⟨13, by decide⟩
  have h14 := hPv ⟨14, by decide⟩
  have e0 := (val_lhs_digit_two (M := nfFold32NL 0) h0 h8 (offNat32_lt 0) (by decide) (by decide)).1
  have e1 := (val_lhs_digit (M := nfFold32NL 1) h1 h9 h8 (offNat32_lt 1) (by decide) (by decide)).1
  have e2 := (val_lhs_digit (M := nfFold32NL 2) h2 h10 h9 (offNat32_lt 2) (by decide) (by decide)).1
  have e3 := (val_lhs_digit (M := nfFold32NL 3) h3 h11 h10 (offNat32_lt 3) (by decide) (by decide)).1
  have e4 := (val_lhs_digit (M := nfFold32NL 4) h4 h12 h11 (offNat32_lt 4) (by decide) (by decide)).1
  have e5 := (val_lhs_digit (M := nfFold32NL 5) h5 h13 h12 (offNat32_lt 5) (by decide) (by decide)).1
  have e6 := (val_lhs_digit (M := nfFold32NL 6) h6 h14 h13 (offNat32_lt 6) (by decide) (by decide)).1
  have e7 := (val_lhs_digit_top (M := nfFold32NL 7) h7 h14 (offNat32_lt 7) (by decide) (by decide)).1
  rw [polyValue_eight]
  simp only [Vector.getElem_map]
  rw [show Expression.eval env (foldLhs32 Pv)[0]
      = Expression.eval env Pv[0] + ((977 : ℕ) : F circomPrime) * Expression.eval env Pv[8]
        + ((offNat32 0 : ℕ) : F circomPrime) from rfl,
    show Expression.eval env (foldLhs32 Pv)[1]
      = Expression.eval env Pv[1] + ((977 : ℕ) : F circomPrime) * Expression.eval env Pv[9]
        + Expression.eval env Pv[8] + ((offNat32 1 : ℕ) : F circomPrime) from rfl,
    show Expression.eval env (foldLhs32 Pv)[2]
      = Expression.eval env Pv[2] + ((977 : ℕ) : F circomPrime) * Expression.eval env Pv[10]
        + Expression.eval env Pv[9] + ((offNat32 2 : ℕ) : F circomPrime) from rfl,
    show Expression.eval env (foldLhs32 Pv)[3]
      = Expression.eval env Pv[3] + ((977 : ℕ) : F circomPrime) * Expression.eval env Pv[11]
        + Expression.eval env Pv[10] + ((offNat32 3 : ℕ) : F circomPrime) from rfl,
    show Expression.eval env (foldLhs32 Pv)[4]
      = Expression.eval env Pv[4] + ((977 : ℕ) : F circomPrime) * Expression.eval env Pv[12]
        + Expression.eval env Pv[11] + ((offNat32 4 : ℕ) : F circomPrime) from rfl,
    show Expression.eval env (foldLhs32 Pv)[5]
      = Expression.eval env Pv[5] + ((977 : ℕ) : F circomPrime) * Expression.eval env Pv[13]
        + Expression.eval env Pv[12] + ((offNat32 5 : ℕ) : F circomPrime) from rfl,
    show Expression.eval env (foldLhs32 Pv)[6]
      = Expression.eval env Pv[6] + ((977 : ℕ) : F circomPrime) * Expression.eval env Pv[14]
        + Expression.eval env Pv[13] + ((offNat32 6 : ℕ) : F circomPrime) from rfl,
    show Expression.eval env (foldLhs32 Pv)[7]
      = Expression.eval env Pv[7] + Expression.eval env Pv[14]
        + ((offNat32 7 : ℕ) : F circomPrime) from rfl,
    e0,
    e1,
    e2,
    e3,
    e4,
    e5,
    e6,
    e7]
  rfl

/-- Digit bounds of the right-hand side. -/
lemma foldRhs32_bound (env : Environment (F circomPrime))
    (q : Expression (F circomPrime)) (t : Var Emu (F circomPrime))
    (hq : (Expression.eval env q).val < 2 ^ 68)
    (ht : ∀ i : Fin numLimbs, (Expression.eval env (t[i.val]'i.isLt)).val < 3 * 2 ^ 64) :
    ∀ k : Fin 8, (Expression.eval env (foldRhs32 q t)[k.val]).val < (2 ^ 100 + 3 * 2 ^ 64) := by
  intro k
  have t0 := ht ⟨0, by decide⟩
  have t1 := ht ⟨1, by decide⟩
  have t2 := ht ⟨2, by decide⟩
  have t3 := ht ⟨3, by decide⟩
  fin_cases k
  · have hd := val_rhs_digit (k := 0) hq t0
    show (Expression.eval env (foldRhs32 q t)[0]).val < (2 ^ 100 + 3 * 2 ^ 64)
    rw [show Expression.eval env (foldRhs32 q t)[0]
        = Expression.eval env q * ((pNat32 0 : ℕ) : F circomPrime)
          + Expression.eval env t[0] from rfl, hd.1]
    exact hd.2
  · have hd := val_rhs_digit_odd (k := 1) hq
    show (Expression.eval env (foldRhs32 q t)[1]).val < (2 ^ 100 + 3 * 2 ^ 64)
    rw [show Expression.eval env (foldRhs32 q t)[1]
        = Expression.eval env q * ((pNat32 1 : ℕ) : F circomPrime) from rfl, hd.1]
    exact hd.2
  · have hd := val_rhs_digit (k := 2) hq t1
    show (Expression.eval env (foldRhs32 q t)[2]).val < (2 ^ 100 + 3 * 2 ^ 64)
    rw [show Expression.eval env (foldRhs32 q t)[2]
        = Expression.eval env q * ((pNat32 2 : ℕ) : F circomPrime)
          + Expression.eval env t[1] from rfl, hd.1]
    exact hd.2
  · have hd := val_rhs_digit_odd (k := 3) hq
    show (Expression.eval env (foldRhs32 q t)[3]).val < (2 ^ 100 + 3 * 2 ^ 64)
    rw [show Expression.eval env (foldRhs32 q t)[3]
        = Expression.eval env q * ((pNat32 3 : ℕ) : F circomPrime) from rfl, hd.1]
    exact hd.2
  · have hd := val_rhs_digit (k := 4) hq t2
    show (Expression.eval env (foldRhs32 q t)[4]).val < (2 ^ 100 + 3 * 2 ^ 64)
    rw [show Expression.eval env (foldRhs32 q t)[4]
        = Expression.eval env q * ((pNat32 4 : ℕ) : F circomPrime)
          + Expression.eval env t[2] from rfl, hd.1]
    exact hd.2
  · have hd := val_rhs_digit_odd (k := 5) hq
    show (Expression.eval env (foldRhs32 q t)[5]).val < (2 ^ 100 + 3 * 2 ^ 64)
    rw [show Expression.eval env (foldRhs32 q t)[5]
        = Expression.eval env q * ((pNat32 5 : ℕ) : F circomPrime) from rfl, hd.1]
    exact hd.2
  · have hd := val_rhs_digit (k := 6) hq t3
    show (Expression.eval env (foldRhs32 q t)[6]).val < (2 ^ 100 + 3 * 2 ^ 64)
    rw [show Expression.eval env (foldRhs32 q t)[6]
        = Expression.eval env q * ((pNat32 6 : ℕ) : F circomPrime)
          + Expression.eval env t[3] from rfl, hd.1]
    exact hd.2
  · have hd := val_rhs_digit_odd (k := 7) hq
    show (Expression.eval env (foldRhs32 q t)[7]).val < (2 ^ 100 + 3 * 2 ^ 64)
    rw [show Expression.eval env (foldRhs32 q t)[7]
        = Expression.eval env q * ((pNat32 7 : ℕ) : F circomPrime) from rfl, hd.1]
    exact hd.2

lemma bigIntValue_four (v : Emu (F circomPrime)) :
    BigInt.value 64 v = v[0].val + v[1].val * 2 ^ 64 + v[2].val * 2 ^ 128 + v[3].val * 2 ^ 192 := by
  rw [BigInt.value_eq_sum]
  simp only [Fin.sum_univ_four]
  norm_num

/-- `polyValue` of the right-hand side. -/
lemma foldRhs32_polyValue (env : Environment (F circomPrime))
    (q : Expression (F circomPrime)) (t : Var Emu (F circomPrime))
    (hq : (Expression.eval env q).val < 2 ^ 68)
    (ht : ∀ i : Fin numLimbs, (Expression.eval env (t[i.val]'i.isLt)).val < 3 * 2 ^ 64) :
    polyValue 32 (Vector.map (Expression.eval env) (foldRhs32 q t))
      = (Expression.eval env q).val * P256
        + BigInt.value 64 (Vector.map (Expression.eval env) t) := by
  have t0 := ht ⟨0, by decide⟩
  have t1 := ht ⟨1, by decide⟩
  have t2 := ht ⟨2, by decide⟩
  have t3 := ht ⟨3, by decide⟩
  have e0 := (val_rhs_digit (k := 0) hq t0).1
  have e1 := (val_rhs_digit_odd (k := 1) hq).1
  have e2 := (val_rhs_digit (k := 2) hq t1).1
  have e3 := (val_rhs_digit_odd (k := 3) hq).1
  have e4 := (val_rhs_digit (k := 4) hq t2).1
  have e5 := (val_rhs_digit_odd (k := 5) hq).1
  have e6 := (val_rhs_digit (k := 6) hq t3).1
  have e7 := (val_rhs_digit_odd (k := 7) hq).1
  rw [polyValue_eight, bigIntValue_four]
  simp only [Vector.getElem_map]
  rw [show Expression.eval env (foldRhs32 q t)[0]
      = Expression.eval env q * ((pNat32 0 : ℕ) : F circomPrime)
        + Expression.eval env t[0] from rfl,
    show Expression.eval env (foldRhs32 q t)[1]
      = Expression.eval env q * ((pNat32 1 : ℕ) : F circomPrime) from rfl,
    show Expression.eval env (foldRhs32 q t)[2]
      = Expression.eval env q * ((pNat32 2 : ℕ) : F circomPrime)
        + Expression.eval env t[1] from rfl,
    show Expression.eval env (foldRhs32 q t)[3]
      = Expression.eval env q * ((pNat32 3 : ℕ) : F circomPrime) from rfl,
    show Expression.eval env (foldRhs32 q t)[4]
      = Expression.eval env q * ((pNat32 4 : ℕ) : F circomPrime)
        + Expression.eval env t[2] from rfl,
    show Expression.eval env (foldRhs32 q t)[5]
      = Expression.eval env q * ((pNat32 5 : ℕ) : F circomPrime) from rfl,
    show Expression.eval env (foldRhs32 q t)[6]
      = Expression.eval env q * ((pNat32 6 : ℕ) : F circomPrime)
        + Expression.eval env t[3] from rfl,
    show Expression.eval env (foldRhs32 q t)[7]
      = Expression.eval env q * ((pNat32 7 : ℕ) : F circomPrime) from rfl,
    e0,
    e1,
    e2,
    e3,
    e4,
    e5,
    e6,
    e7,
    ← pNat32_sum]
  ring

/-! ### Convolution bridges -/

lemma coeff_eq_convNat {Ca Cb : ℕ} (env : Environment (F circomPrime))
    (a b : Var (BigInt 8) (F circomPrime))
    (ha : ∀ i : Fin 8, (Expression.eval env (a[i.val]'i.isLt)).val < Ca)
    (hb : ∀ i : Fin 8, (Expression.eval env (b[i.val]'i.isLt)).val < Cb)
    (hbound : 8 * (Ca * Cb) < circomPrime) (k : Fin 15) :
    (Expression.eval env ((bigIntMulNoReduce a b)[k.val])).val = convNat env a b k.val :=
  MulModTargetW2.val_coeff_gen2 env a b k ha hb hbound

/-- Exactly four of the eight indices `i < 8` have `k + i` even. -/
lemma sum_ite_parity_eight (k c : ℕ) :
    (∑ i : Fin 8, (if (k + i.val) % 2 = 0 then c else 0)) = 4 * c := by
  rw [Fin.sum_univ_eight]
  norm_num
  split_ifs <;> omega

/-- Sharper bound on the convolution coefficients when the second operand has
vanishing *odd* digits.  Exactly four of the eight summands can be nonzero, so
the cell cap halves from `8·(Ca·Cb)` to `4·(Ca·Cb)`. -/
lemma convNat_lt_sparse {Ca Cb : ℕ} (env : Environment (F circomPrime))
    (a b : Var (BigInt 8) (F circomPrime))
    (ha : ∀ i : Fin 8, (Expression.eval env (a[i.val]'i.isLt)).val < Ca)
    (hb : ∀ i : Fin 8, (Expression.eval env (b[i.val]'i.isLt)).val < Cb)
    (hbz : ∀ i : Fin 8, i.val % 2 = 1 → (Expression.eval env (b[i.val]'i.isLt)) = 0)
    (k : ℕ) : convNat env a b k < 4 * (Ca * Cb) := by
  have hCa : 0 < Ca := lt_of_le_of_lt (Nat.zero_le _) (ha ⟨0, by decide⟩)
  have hCb : 0 < Cb := lt_of_le_of_lt (Nat.zero_le _) (hb ⟨0, by decide⟩)
  have hterm : ∀ i : Fin 8, (if h : i.val ≤ k ∧ k - i.val < 8 then
      (Expression.eval env (a[i.val]'i.isLt)).val
        * (Expression.eval env (b[k - i.val]'h.2)).val else 0)
      ≤ (if (k + i.val) % 2 = 0 then Ca * Cb - 1 else 0) := by
    intro i
    by_cases h : i.val ≤ k ∧ k - i.val < 8
    · simp only [dif_pos h]
      by_cases hpar : (k + i.val) % 2 = 0
      · simp only [if_pos hpar]
        have hai : (Expression.eval env (a[i.val]'i.isLt)).val < Ca := ha i
        have hbk : (Expression.eval env (b[k - i.val]'h.2)).val < Cb := hb ⟨k - i.val, h.2⟩
        have := Nat.mul_le_mul (Nat.le_sub_one_of_lt hai) (Nat.le_sub_one_of_lt hbk)
        have hexp : Ca * Cb = (Ca - 1) * (Cb - 1) + (Ca - 1) + (Cb - 1) + 1 := by
          cases Ca with
          | zero => omega
          | succ n =>
            cases Cb with
            | zero => omega
            | succ m => simp only [Nat.succ_sub_one]; ring
        omega
      · simp only [if_neg hpar]
        have hodd : (k - i.val) % 2 = 1 := by omega
        rw [hbz ⟨k - i.val, h.2⟩ hodd]
        simp
    · simp only [dif_neg h]; omega
  have hcount : (∑ i : Fin 8, (if (k + i.val) % 2 = 0 then Ca * Cb - 1 else 0))
      = 4 * (Ca * Cb - 1) := sum_ite_parity_eight k (Ca * Cb - 1)
  have hsum : convNat env a b k ≤ 4 * (Ca * Cb - 1) := by
    unfold convNat
    calc ∑ i : Fin 8, _ ≤ ∑ i : Fin 8, (if (k + i.val) % 2 = 0 then Ca * Cb - 1 else 0) :=
          Finset.sum_le_sum fun i _ => hterm i
      _ = 4 * (Ca * Cb - 1) := hcount
  have hpos : 0 < Ca * Cb := Nat.mul_pos hCa hCb
  omega

/-- Position-aware cap on the `k`-th convolution cell: only the terms whose
parity permits a nonzero `b`-digit contribute, and there are `sparseCnt k`
of them. -/
lemma convNat_lt_sparse_tri {Ca Cb : ℕ} (env : Environment (F circomPrime))
    (a b : Var (BigInt 8) (F circomPrime))
    (ha : ∀ i : Fin 8, (Expression.eval env (a[i.val]'i.isLt)).val < Ca)
    (hb : ∀ i : Fin 8, (Expression.eval env (b[i.val]'i.isLt)).val < Cb)
    (hbz : ∀ i : Fin 8, i.val % 2 = 1 → (Expression.eval env (b[i.val]'i.isLt)) = 0)
    (hcap : Ca * Cb ≤ 3 * 2 ^ 96)
    (k : ℕ) : convNat env a b k < sparseNf k := by
  have hterm : ∀ i : Fin 8, (if h : i.val ≤ k ∧ k - i.val < 8 then
      (Expression.eval env (a[i.val]'i.isLt)).val
        * (Expression.eval env (b[k - i.val]'h.2)).val else 0)
      ≤ (if (i.val ≤ k ∧ k - i.val < 8) ∧ (k + i.val) % 2 = 0 then 1 else 0)
          * (Ca * Cb - 1) := by
    intro i
    by_cases h : i.val ≤ k ∧ k - i.val < 8
    · simp only [dif_pos h]
      by_cases hpar : (k + i.val) % 2 = 0
      · simp only [if_pos (And.intro h hpar), one_mul]
        have hai : (Expression.eval env (a[i.val]'i.isLt)).val < Ca := ha i
        have hbk : (Expression.eval env (b[k - i.val]'h.2)).val < Cb := hb ⟨k - i.val, h.2⟩
        have := Nat.mul_le_mul (Nat.le_sub_one_of_lt hai) (Nat.le_sub_one_of_lt hbk)
        have hexp : Ca * Cb = (Ca - 1) * (Cb - 1) + (Ca - 1) + (Cb - 1) + 1 := by
          cases Ca with
          | zero => omega
          | succ n =>
            cases Cb with
            | zero => omega
            | succ m => simp only [Nat.succ_sub_one]; ring
        omega
      · simp only [if_neg (fun hh : (i.val ≤ k ∧ k - i.val < 8) ∧ (k + i.val) % 2 = 0 =>
          hpar hh.2)]
        have hodd : (k - i.val) % 2 = 1 := by omega
        rw [hbz ⟨k - i.val, h.2⟩ hodd]
        simp
    · simp only [dif_neg h,
        if_neg (fun hh : (i.val ≤ k ∧ k - i.val < 8) ∧ (k + i.val) % 2 = 0 => h hh.1)]
      omega
  have hsum : convNat env a b k ≤ sparseCnt k * (Ca * Cb - 1) := by
    unfold convNat
    calc ∑ i : Fin 8, _
        ≤ ∑ i : Fin 8, (if (i.val ≤ k ∧ k - i.val < 8) ∧ (k + i.val) % 2 = 0 then 1 else 0)
            * (Ca * Cb - 1) := Finset.sum_le_sum fun i _ => hterm i
      _ = sparseCnt k * (Ca * Cb - 1) := by rw [← Finset.sum_mul]; rfl
  have hmul : sparseCnt k * (Ca * Cb - 1) ≤ sparseCnt k * (3 * 2 ^ 96) :=
    Nat.mul_le_mul le_rfl (by omega)
  calc convNat env a b k ≤ sparseCnt k * (Ca * Cb - 1) := hsum
    _ ≤ sparseCnt k * (3 * 2 ^ 96) := hmul
    _ < sparseNf k := by unfold sparseNf; exact Nat.lt_succ_self _

/-- With vanishing odd digits in the second operand the *top* convolution
coefficient is identically zero: the only index pair reaching position `14` is
`(7, 7)`, and `b[7] = 0`.  This is what shortens the quotient wire. -/
lemma convNat_14_zero (env : Environment (F circomPrime))
    (a b : Var (BigInt 8) (F circomPrime))
    (hbz : ∀ i : Fin 8, i.val % 2 = 1 → (Expression.eval env (b[i.val]'i.isLt)) = 0) :
    convNat env a b 14 = 0 := by
  have hb7 : (Expression.eval env (b[7]'(by decide))) = 0 := hbz ⟨7, by decide⟩ (by decide)
  unfold convNat
  rw [Fin.sum_univ_eight]
  norm_num [hb7]

/-- `foldDNatOf` of the true product coefficients is `foldDNat`. -/
lemma foldDNatOf_eq {Ca Cb : ℕ} (env : Environment (F circomPrime))
    (a b : Var (BigInt 8) (F circomPrime))
    (ha : ∀ i : Fin 8, (Expression.eval env (a[i.val]'i.isLt)).val < Ca)
    (hb : ∀ i : Fin 8, (Expression.eval env (b[i.val]'i.isLt)).val < Cb)
    (hbound : 8 * (Ca * Cb) < circomPrime)
    (Pv : Vector (Expression (F circomPrime)) 15)
    (hbridge : ∀ k : Fin 15,
      Expression.eval env Pv[k.val] = Expression.eval env (bigIntMulNoReduce a b)[k.val]) :
    foldDNatOf env Pv = foldDNat env a b := by
  unfold foldDNatOf foldDNat
  rw [hbridge ⟨0, by decide⟩,
    hbridge ⟨1, by decide⟩,
    hbridge ⟨2, by decide⟩,
    hbridge ⟨3, by decide⟩,
    hbridge ⟨4, by decide⟩,
    hbridge ⟨5, by decide⟩,
    hbridge ⟨6, by decide⟩,
    hbridge ⟨7, by decide⟩,
    hbridge ⟨8, by decide⟩,
    hbridge ⟨9, by decide⟩,
    hbridge ⟨10, by decide⟩,
    hbridge ⟨11, by decide⟩,
    hbridge ⟨12, by decide⟩,
    hbridge ⟨13, by decide⟩,
    hbridge ⟨14, by decide⟩,
    coeff_eq_convNat env a b ha hb hbound ⟨0, by decide⟩,
    coeff_eq_convNat env a b ha hb hbound ⟨1, by decide⟩,
    coeff_eq_convNat env a b ha hb hbound ⟨2, by decide⟩,
    coeff_eq_convNat env a b ha hb hbound ⟨3, by decide⟩,
    coeff_eq_convNat env a b ha hb hbound ⟨4, by decide⟩,
    coeff_eq_convNat env a b ha hb hbound ⟨5, by decide⟩,
    coeff_eq_convNat env a b ha hb hbound ⟨6, by decide⟩,
    coeff_eq_convNat env a b ha hb hbound ⟨7, by decide⟩,
    coeff_eq_convNat env a b ha hb hbound ⟨8, by decide⟩,
    coeff_eq_convNat env a b ha hb hbound ⟨9, by decide⟩,
    coeff_eq_convNat env a b ha hb hbound ⟨10, by decide⟩,
    coeff_eq_convNat env a b ha hb hbound ⟨11, by decide⟩,
    coeff_eq_convNat env a b ha hb hbound ⟨12, by decide⟩,
    coeff_eq_convNat env a b ha hb hbound ⟨13, by decide⟩,
    coeff_eq_convNat env a b ha hb hbound ⟨14, by decide⟩]

/-- The key fold identity at the level of the witnessed values. -/
lemma foldDNat_identity {Ca Cb : ℕ} (env : Environment (F circomPrime))
    (a b : Var (BigInt 8) (F circomPrime))
    (ha : ∀ i : Fin 8, (Expression.eval env (a[i.val]'i.isLt)).val < Ca)
    (hb : ∀ i : Fin 8, (Expression.eval env (b[i.val]'i.isLt)).val < Cb)
    (hbound : 8 * (Ca * Cb) < circomPrime) :
    foldDNat env a b
        + P256 * (convNat env a b 8 + convNat env a b 9 * 2 ^ 32
            + convNat env a b 10 * 2 ^ 64 + convNat env a b 11 * 2 ^ 96
            + convNat env a b 12 * 2 ^ 128 + convNat env a b 13 * 2 ^ 160
            + convNat env a b 14 * 2 ^ 192)
      = BigInt.value 32 (Vector.map (Expression.eval env) a)
          * BigInt.value 32 (Vector.map (Expression.eval env) b) + 3 * P256 := by
  have hprod : polyValue 32 (Vector.map (Expression.eval env) (bigIntMulNoReduce a b))
      = BigInt.value 32 (Vector.map (Expression.eval env) a)
        * BigInt.value 32 (Vector.map (Expression.eval env) b) :=
    MulModTargetW2.polyValue_mul_eq_gen2 env a b ha hb hbound
  rw [polyValue_fifteen_map] at hprod
  rw [← hprod]
  unfold foldDNat
  rw [← coeff_eq_convNat env a b ha hb hbound ⟨0, by decide⟩,
    ← coeff_eq_convNat env a b ha hb hbound ⟨1, by decide⟩,
    ← coeff_eq_convNat env a b ha hb hbound ⟨2, by decide⟩,
    ← coeff_eq_convNat env a b ha hb hbound ⟨3, by decide⟩,
    ← coeff_eq_convNat env a b ha hb hbound ⟨4, by decide⟩,
    ← coeff_eq_convNat env a b ha hb hbound ⟨5, by decide⟩,
    ← coeff_eq_convNat env a b ha hb hbound ⟨6, by decide⟩,
    ← coeff_eq_convNat env a b ha hb hbound ⟨7, by decide⟩,
    ← coeff_eq_convNat env a b ha hb hbound ⟨8, by decide⟩,
    ← coeff_eq_convNat env a b ha hb hbound ⟨9, by decide⟩,
    ← coeff_eq_convNat env a b ha hb hbound ⟨10, by decide⟩,
    ← coeff_eq_convNat env a b ha hb hbound ⟨11, by decide⟩,
    ← coeff_eq_convNat env a b ha hb hbound ⟨12, by decide⟩,
    ← coeff_eq_convNat env a b ha hb hbound ⟨13, by decide⟩,
    ← coeff_eq_convNat env a b ha hb hbound ⟨14, by decide⟩]
  exact fold_identity32 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-- `3·p ≤ D`, so the quotient is a genuine natural number. -/
lemma foldDNat_ge (env : Environment (F circomPrime)) (a b : Var (BigInt 8) (F circomPrime)) :
    3 * P256 ≤ foldDNat env a b := by
  rw [← offNat32_sum]
  unfold foldDNat
  gcongr <;> omega

/-- `D < 2^326 + 2^305` whenever the product coefficients are capped. -/
lemma foldDNat_lt {Ca Cb : ℕ} (env : Environment (F circomPrime))
    (a b : Var (BigInt 8) (F circomPrime))
    (ha : ∀ i : Fin 8, (Expression.eval env (a[i.val]'i.isLt)).val < Ca)
    (hb : ∀ i : Fin 8, (Expression.eval env (b[i.val]'i.isLt)).val < Cb)
    (hbz : ∀ i : Fin 8, i.val % 2 = 1 → (Expression.eval env (b[i.val]'i.isLt)) = 0)
    (hcap : 4 * (Ca * Cb) ≤ (3 * 2 ^ 98)) :
    foldDNat env a b < 3 * 2 ^ 322 + 2 ^ 299 := by
  have hc0 := convNat_lt_sparse env a b ha hb hbz 0
  have hc1 := convNat_lt_sparse env a b ha hb hbz 1
  have hc2 := convNat_lt_sparse env a b ha hb hbz 2
  have hc3 := convNat_lt_sparse env a b ha hb hbz 3
  have hc4 := convNat_lt_sparse env a b ha hb hbz 4
  have hc5 := convNat_lt_sparse env a b ha hb hbz 5
  have hc6 := convNat_lt_sparse env a b ha hb hbz 6
  have hc7 := convNat_lt_sparse env a b ha hb hbz 7
  have hc8 := convNat_lt_sparse env a b ha hb hbz 8
  have hc9 := convNat_lt_sparse env a b ha hb hbz 9
  have hc10 := convNat_lt_sparse env a b ha hb hbz 10
  have hc11 := convNat_lt_sparse env a b ha hb hbz 11
  have hc12 := convNat_lt_sparse env a b ha hb hbz 12
  have hc13 := convNat_lt_sparse env a b ha hb hbz 13
  have hc14 := convNat_14_zero env a b hbz
  have ho0 := offNat32_lt 0
  have ho1 := offNat32_lt 1
  have ho2 := offNat32_lt 2
  have ho3 := offNat32_lt 3
  have ho4 := offNat32_lt 4
  have ho5 := offNat32_lt 5
  have ho6 := offNat32_lt 6
  have ho7 := offNat32_lt 7
  unfold foldDNat
  omega

/-! ## The circuit -/

def Assumptions (Ca Cb : ℕ) (input : Inputs (F circomPrime)) : Prop :=
  (∀ i : Fin 8, (input.a[i.val]).val < Ca) ∧
  (∀ i : Fin 8, (input.b[i.val]).val < Cb) ∧
  (∀ i : Fin 8, i.val % 2 = 1 → (input.b[i.val]) = 0) ∧
  (∀ i : Fin numLimbs, (input.target[i.val]).val < 3 * 2 ^ 64) ∧
  BigInt.value 64 input.target < 3 * P256

def Spec (input : Inputs (F circomPrime)) : Prop :=
  BigInt.value 64 input.target % P256
    = BigInt.value 32 input.a * BigInt.value 32 input.b % P256

/-! ## Stability under environments that agree on the referenced wires -/

lemma foldLhs32_stable {E1 E2 : Environment (F circomPrime)}
    (Pv : Vector (Expression (F circomPrime)) 15)
    (h : ∀ (i : ℕ) (hi : i < 15),
      Expression.eval E1 (Pv[i]'hi) = Expression.eval E2 (Pv[i]'hi)) :
    Vector.map (Expression.eval E1) (foldLhs32 Pv)
      = Vector.map (Expression.eval E2) (foldLhs32 Pv) := by
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_map]
  have hi8 : i < 8 := hi
  have h8 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases h8 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [show Expression.eval E1 (foldLhs32 Pv)[0]
        = Expression.eval E1 Pv[0] + ((977 : ℕ) : F circomPrime) * Expression.eval E1 Pv[8]
          + ((offNat32 0 : ℕ) : F circomPrime) from rfl,
      show Expression.eval E2 (foldLhs32 Pv)[0]
        = Expression.eval E2 Pv[0] + ((977 : ℕ) : F circomPrime) * Expression.eval E2 Pv[8]
          + ((offNat32 0 : ℕ) : F circomPrime) from rfl, h 0 (by decide), h 8 (by decide)]
  · rw [show Expression.eval E1 (foldLhs32 Pv)[1]
        = Expression.eval E1 Pv[1] + ((977 : ℕ) : F circomPrime) * Expression.eval E1 Pv[9]
          + Expression.eval E1 Pv[8] + ((offNat32 1 : ℕ) : F circomPrime) from rfl,
      show Expression.eval E2 (foldLhs32 Pv)[1]
        = Expression.eval E2 Pv[1] + ((977 : ℕ) : F circomPrime) * Expression.eval E2 Pv[9]
          + Expression.eval E2 Pv[8] + ((offNat32 1 : ℕ) : F circomPrime) from rfl,
      h 1 (by decide), h 9 (by decide), h 8 (by decide)]
  · rw [show Expression.eval E1 (foldLhs32 Pv)[2]
        = Expression.eval E1 Pv[2] + ((977 : ℕ) : F circomPrime) * Expression.eval E1 Pv[10]
          + Expression.eval E1 Pv[9] + ((offNat32 2 : ℕ) : F circomPrime) from rfl,
      show Expression.eval E2 (foldLhs32 Pv)[2]
        = Expression.eval E2 Pv[2] + ((977 : ℕ) : F circomPrime) * Expression.eval E2 Pv[10]
          + Expression.eval E2 Pv[9] + ((offNat32 2 : ℕ) : F circomPrime) from rfl,
      h 2 (by decide), h 10 (by decide), h 9 (by decide)]
  · rw [show Expression.eval E1 (foldLhs32 Pv)[3]
        = Expression.eval E1 Pv[3] + ((977 : ℕ) : F circomPrime) * Expression.eval E1 Pv[11]
          + Expression.eval E1 Pv[10] + ((offNat32 3 : ℕ) : F circomPrime) from rfl,
      show Expression.eval E2 (foldLhs32 Pv)[3]
        = Expression.eval E2 Pv[3] + ((977 : ℕ) : F circomPrime) * Expression.eval E2 Pv[11]
          + Expression.eval E2 Pv[10] + ((offNat32 3 : ℕ) : F circomPrime) from rfl,
      h 3 (by decide), h 11 (by decide), h 10 (by decide)]
  · rw [show Expression.eval E1 (foldLhs32 Pv)[4]
        = Expression.eval E1 Pv[4] + ((977 : ℕ) : F circomPrime) * Expression.eval E1 Pv[12]
          + Expression.eval E1 Pv[11] + ((offNat32 4 : ℕ) : F circomPrime) from rfl,
      show Expression.eval E2 (foldLhs32 Pv)[4]
        = Expression.eval E2 Pv[4] + ((977 : ℕ) : F circomPrime) * Expression.eval E2 Pv[12]
          + Expression.eval E2 Pv[11] + ((offNat32 4 : ℕ) : F circomPrime) from rfl,
      h 4 (by decide), h 12 (by decide), h 11 (by decide)]
  · rw [show Expression.eval E1 (foldLhs32 Pv)[5]
        = Expression.eval E1 Pv[5] + ((977 : ℕ) : F circomPrime) * Expression.eval E1 Pv[13]
          + Expression.eval E1 Pv[12] + ((offNat32 5 : ℕ) : F circomPrime) from rfl,
      show Expression.eval E2 (foldLhs32 Pv)[5]
        = Expression.eval E2 Pv[5] + ((977 : ℕ) : F circomPrime) * Expression.eval E2 Pv[13]
          + Expression.eval E2 Pv[12] + ((offNat32 5 : ℕ) : F circomPrime) from rfl,
      h 5 (by decide), h 13 (by decide), h 12 (by decide)]
  · rw [show Expression.eval E1 (foldLhs32 Pv)[6]
        = Expression.eval E1 Pv[6] + ((977 : ℕ) : F circomPrime) * Expression.eval E1 Pv[14]
          + Expression.eval E1 Pv[13] + ((offNat32 6 : ℕ) : F circomPrime) from rfl,
      show Expression.eval E2 (foldLhs32 Pv)[6]
        = Expression.eval E2 Pv[6] + ((977 : ℕ) : F circomPrime) * Expression.eval E2 Pv[14]
          + Expression.eval E2 Pv[13] + ((offNat32 6 : ℕ) : F circomPrime) from rfl,
      h 6 (by decide), h 14 (by decide), h 13 (by decide)]
  · rw [show Expression.eval E1 (foldLhs32 Pv)[7]
        = Expression.eval E1 Pv[7] + Expression.eval E1 Pv[14]
          + ((offNat32 7 : ℕ) : F circomPrime) from rfl,
      show Expression.eval E2 (foldLhs32 Pv)[7]
        = Expression.eval E2 Pv[7] + Expression.eval E2 Pv[14]
          + ((offNat32 7 : ℕ) : F circomPrime) from rfl, h 7 (by decide), h 14 (by decide)]

lemma foldRhs32_stable {E1 E2 : Environment (F circomPrime)}
    (q : Expression (F circomPrime)) (t : Var Emu (F circomPrime))
    (hq : Expression.eval E1 q = Expression.eval E2 q)
    (ht : ∀ (i : ℕ) (hi : i < numLimbs),
      Expression.eval E1 (t[i]'hi) = Expression.eval E2 (t[i]'hi)) :
    Vector.map (Expression.eval E1) (foldRhs32 q t)
      = Vector.map (Expression.eval E2) (foldRhs32 q t) := by
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_map]
  have hi8 : i < 8 := hi
  have h8 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases h8 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [show Expression.eval E1 (foldRhs32 q t)[0]
        = Expression.eval E1 q * ((pNat32 0 : ℕ) : F circomPrime)
          + Expression.eval E1 t[0] from rfl,
      show Expression.eval E2 (foldRhs32 q t)[0]
        = Expression.eval E2 q * ((pNat32 0 : ℕ) : F circomPrime)
          + Expression.eval E2 t[0] from rfl, hq, ht 0 (by decide)]
  · rw [show Expression.eval E1 (foldRhs32 q t)[1]
        = Expression.eval E1 q * ((pNat32 1 : ℕ) : F circomPrime) from rfl,
      show Expression.eval E2 (foldRhs32 q t)[1]
        = Expression.eval E2 q * ((pNat32 1 : ℕ) : F circomPrime) from rfl, hq]
  · rw [show Expression.eval E1 (foldRhs32 q t)[2]
        = Expression.eval E1 q * ((pNat32 2 : ℕ) : F circomPrime)
          + Expression.eval E1 t[1] from rfl,
      show Expression.eval E2 (foldRhs32 q t)[2]
        = Expression.eval E2 q * ((pNat32 2 : ℕ) : F circomPrime)
          + Expression.eval E2 t[1] from rfl, hq, ht 1 (by decide)]
  · rw [show Expression.eval E1 (foldRhs32 q t)[3]
        = Expression.eval E1 q * ((pNat32 3 : ℕ) : F circomPrime) from rfl,
      show Expression.eval E2 (foldRhs32 q t)[3]
        = Expression.eval E2 q * ((pNat32 3 : ℕ) : F circomPrime) from rfl, hq]
  · rw [show Expression.eval E1 (foldRhs32 q t)[4]
        = Expression.eval E1 q * ((pNat32 4 : ℕ) : F circomPrime)
          + Expression.eval E1 t[2] from rfl,
      show Expression.eval E2 (foldRhs32 q t)[4]
        = Expression.eval E2 q * ((pNat32 4 : ℕ) : F circomPrime)
          + Expression.eval E2 t[2] from rfl, hq, ht 2 (by decide)]
  · rw [show Expression.eval E1 (foldRhs32 q t)[5]
        = Expression.eval E1 q * ((pNat32 5 : ℕ) : F circomPrime) from rfl,
      show Expression.eval E2 (foldRhs32 q t)[5]
        = Expression.eval E2 q * ((pNat32 5 : ℕ) : F circomPrime) from rfl, hq]
  · rw [show Expression.eval E1 (foldRhs32 q t)[6]
        = Expression.eval E1 q * ((pNat32 6 : ℕ) : F circomPrime)
          + Expression.eval E1 t[3] from rfl,
      show Expression.eval E2 (foldRhs32 q t)[6]
        = Expression.eval E2 q * ((pNat32 6 : ℕ) : F circomPrime)
          + Expression.eval E2 t[3] from rfl, hq, ht 3 (by decide)]
  · rw [show Expression.eval E1 (foldRhs32 q t)[7]
        = Expression.eval E1 q * ((pNat32 7 : ℕ) : F circomPrime) from rfl,
      show Expression.eval E2 (foldRhs32 q t)[7]
        = Expression.eval E2 q * ((pNat32 7 : ℕ) : F circomPrime) from rfl, hq]

attribute [local irreducible] interpolatedMul14 RangeCheck.circuit GroupedEqXV.circuit

/-! ## Re-reading a four-limb `Emu` at eight base-`2^32` positions

A base-`2^64` value is literally a base-`2^32` value whose odd digits vanish, so
placing the four 64-bit limbs at the even positions and the constant `0` at the
odd ones is a free (allocation-less) recombination that turns an `Emu` operand
into a `BigInt 8` operand of this certificate. -/

/-- Re-read a four-limb 64-bit vector as eight base-`2^32` digits. -/
def expand32 (v : Var Emu (F circomPrime)) : Var (BigInt 8) (F circomPrime) :=
  #v[v[0], 0, v[1], 0, v[2], 0, v[3], 0]

/-- Value-level counterpart of `expand32`. -/
def expand32V (v : Emu (F circomPrime)) : BigInt 8 (F circomPrime) :=
  #v[v[0], 0, v[1], 0, v[2], 0, v[3], 0]

lemma eval_expand32 (env : Environment (F circomPrime)) (v : Var Emu (F circomPrime)) :
    Vector.map (Expression.eval env) (expand32 v)
      = expand32V (Vector.map (Expression.eval env) v) := by
  apply Vector.ext
  intro i hi
  simp only [expand32, expand32V, Vector.getElem_map]
  match i, hi with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | 7, _ => rfl

lemma value_expand32 (v : Emu (F circomPrime)) :
    BigInt.value 32 (expand32V v) = BigInt.value 64 v := by
  rw [BigInt.value_eq_sum, bigIntValue_four]
  simp only [Fin.sum_univ_eight, expand32V, Fin.getElem_fin, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ, ZMod.val_zero]
  norm_num

/-- The odd digits of `expand32` are the literal zero expression. -/
lemma eval_expand32_odd_zero (env : Environment (F circomPrime))
    (v : Var Emu (F circomPrime)) :
    ∀ i : Fin 8, i.val % 2 = 1 → Expression.eval env ((expand32 v)[i.val]) = 0 := by
  rintro ⟨iv, hiv⟩ hodd
  have hodd' : iv % 2 = 1 := hodd
  have h4 : iv = 1 ∨ iv = 3 ∨ iv = 5 ∨ iv = 7 := by omega
  rcases h4 with rfl | rfl | rfl | rfl <;>
    first
      | rfl
      | simp [expand32]

lemma expand32V_lt {v : Emu (F circomPrime)} {C : ℕ} (hC : 0 < C)
    (h : ∀ i : Fin numLimbs, (v[i.val]).val < C) :
    ∀ i : Fin 8, ((expand32V v)[i.val]).val < C := by
  have h0 := h ⟨0, by decide⟩
  have h1 := h ⟨1, by decide⟩
  have h2 := h ⟨2, by decide⟩
  have h3 := h ⟨3, by decide⟩
  simp only [Fin.getElem_fin] at h0 h1 h2 h3
  have hz : (0 : F circomPrime).val < C := by simpa [ZMod.val_zero] using hC
  rintro ⟨iv, hiv⟩
  simp only [expand32V, Fin.getElem_fin, Vector.getElem_mk, List.getElem_toArray]
  match iv, hiv with
  | 0, _ => exact h0
  | 1, _ => exact hz
  | 2, _ => exact h1
  | 3, _ => exact hz
  | 4, _ => exact h2
  | 5, _ => exact hz
  | 6, _ => exact h3
  | 7, _ => exact hz

end MulModFold32N
end Solution.Secp256k1ScalarMul
