import Solution.Secp256k1ScalarMul.ScalarCongruence
import Solution.Secp256k1ScalarMul.ParamsRel
import Solution.Secp256k1ScalarMul.MulModFold

/-!
# Cells of the deferred mod-`n` congruence

The GLV scalar-side relation is certified without reducing any of the four
partial products modulo `n`.  Both sides of the certified integer identity are
four-position limb vectors whose cells are affine forms with compile-time
coefficients; this file defines them and proves the two facts the certificate
needs: a per-cell magnitude bound, and the `polyValue` of the whole vector.
-/

namespace Solution.Secp256k1ScalarMul
namespace RelCells

open Solution.Secp256k1ScalarMul.GLV

/-- A compile-time natural constant, as an expression. -/
def natE (v : ℕ) : Expression (F circomPrime) :=
  (((v : ℕ) : F circomPrime) : Expression (F circomPrime))

@[simp] lemma eval_natE (env : Environment (F circomPrime)) (v : ℕ) :
    Expression.eval env (natE v) = ((v : ℕ) : F circomPrime) := rfl

lemma limbOfNat_lt (v k : ℕ) : limbOfNat v k < 2 ^ limbBits :=
  Nat.mod_lt _ (Nat.two_pow_pos _)

/-! ## The two cell families -/

/-- Left-hand cell: `λₖ·|u₂| + [k=0]·|u₁| + cₖ + eₖ + bias·nₖ`. -/
def lhsCell (mu1 mu2 : Expression (F circomPrime)) (c e : Var Emu (F circomPrime))
    (k : Fin numLimbs) : Expression (F circomPrime) :=
  natE (limbOfNat eigenvalue k.val) * mu2
    + natE (if k.val = 0 then 1 else 0) * mu1
    + natE 1 * (c[k.val]'k.isLt)
    + natE 1 * (e[k.val]'k.isLt)
    + natE (biasKRel * limbOfNat scalarOrder k.val) * natE 1

def relLhs (mu1 mu2 : Expression (F circomPrime)) (c e : Var Emu (F circomPrime)) :
    Vector (Expression (F circomPrime)) numLimbs :=
  Vector.ofFn (lhsCell mu1 mu2 c e)

/-- Right-hand cell: `2λₖ·n₂ + 2[k=0]·n₁ + 2dₖ + 2fₖ + nₖ·q`. -/
def rhsCell (nm1 nm2 q : Expression (F circomPrime)) (d f : Var Emu (F circomPrime))
    (k : Fin numLimbs) : Expression (F circomPrime) :=
  natE (2 * limbOfNat eigenvalue k.val) * nm2
    + natE (if k.val = 0 then 2 else 0) * nm1
    + natE 2 * (d[k.val]'k.isLt)
    + natE 2 * (f[k.val]'k.isLt)
    + natE (limbOfNat scalarOrder k.val) * q

def relRhs (nm1 nm2 q : Expression (F circomPrime)) (d f : Var Emu (F circomPrime)) :
    Vector (Expression (F circomPrime)) numLimbs :=
  Vector.ofFn (rhsCell nm1 nm2 q d f)

/-! ## `val` of a five-term affine form -/

lemma val_lin5 (c1 c2 c3 c4 c5 : ℕ) (x1 x2 x3 x4 x5 : F circomPrime)
    (h : c1 * x1.val + c2 * x2.val + c3 * x3.val + c4 * x4.val + c5 * x5.val < circomPrime) :
    (((c1 : ℕ) : F circomPrime) * x1 + ((c2 : ℕ) : F circomPrime) * x2
      + ((c3 : ℕ) : F circomPrime) * x3 + ((c4 : ℕ) : F circomPrime) * x4
      + ((c5 : ℕ) : F circomPrime) * x5).val
      = c1 * x1.val + c2 * x2.val + c3 * x3.val + c4 * x4.val + c5 * x5.val := by
  have hfield :
      ((c1 : ℕ) : F circomPrime) * x1 + ((c2 : ℕ) : F circomPrime) * x2
        + ((c3 : ℕ) : F circomPrime) * x3 + ((c4 : ℕ) : F circomPrime) * x4
        + ((c5 : ℕ) : F circomPrime) * x5
      = ((c1 * x1.val + c2 * x2.val + c3 * x3.val + c4 * x4.val + c5 * x5.val : ℕ)
          : F circomPrime) := by
    push_cast
    rw [ZMod.natCast_zmod_val x1, ZMod.natCast_zmod_val x2, ZMod.natCast_zmod_val x3,
      ZMod.natCast_zmod_val x4, ZMod.natCast_zmod_val x5]
  rw [hfield, ZMod.val_natCast_of_lt h]

lemma val_one : (((1 : ℕ) : F circomPrime)).val = 1 := by
  rw [Nat.cast_one, ZMod.val_one]

/-! ## Cell values -/

lemma lhsCell_val (env : Environment (F circomPrime))
    (mu1 mu2 : Expression (F circomPrime)) (c e : Var Emu (F circomPrime))
    (k : Fin numLimbs)
    (h : limbOfNat eigenvalue k.val * (Expression.eval env mu2).val
        + (if k.val = 0 then 1 else 0) * (Expression.eval env mu1).val
        + (Expression.eval env (c[k.val]'k.isLt)).val
        + (Expression.eval env (e[k.val]'k.isLt)).val
        + biasKRel * limbOfNat scalarOrder k.val < circomPrime) :
    (Expression.eval env (lhsCell mu1 mu2 c e k)).val
      = limbOfNat eigenvalue k.val * (Expression.eval env mu2).val
        + (if k.val = 0 then 1 else 0) * (Expression.eval env mu1).val
        + (Expression.eval env (c[k.val]'k.isLt)).val
        + (Expression.eval env (e[k.val]'k.isLt)).val
        + biasKRel * limbOfNat scalarOrder k.val := by
  show (((limbOfNat eigenvalue k.val : ℕ) : F circomPrime) * Expression.eval env mu2
      + (((if k.val = 0 then 1 else 0 : ℕ)) : F circomPrime) * Expression.eval env mu1
      + ((1 : ℕ) : F circomPrime) * Expression.eval env (c[k.val]'k.isLt)
      + ((1 : ℕ) : F circomPrime) * Expression.eval env (e[k.val]'k.isLt)
      + ((biasKRel * limbOfNat scalarOrder k.val : ℕ) : F circomPrime)
        * ((1 : ℕ) : F circomPrime)).val = _
  rw [val_lin5 _ _ _ _ _ _ _ _ _ _ (by rw [val_one]; simpa using h), val_one]
  ring

lemma rhsCell_val (env : Environment (F circomPrime))
    (nm1 nm2 q : Expression (F circomPrime)) (d f : Var Emu (F circomPrime))
    (k : Fin numLimbs)
    (h : 2 * limbOfNat eigenvalue k.val * (Expression.eval env nm2).val
        + (if k.val = 0 then 2 else 0) * (Expression.eval env nm1).val
        + 2 * (Expression.eval env (d[k.val]'k.isLt)).val
        + 2 * (Expression.eval env (f[k.val]'k.isLt)).val
        + limbOfNat scalarOrder k.val * (Expression.eval env q).val < circomPrime) :
    (Expression.eval env (rhsCell nm1 nm2 q d f k)).val
      = 2 * limbOfNat eigenvalue k.val * (Expression.eval env nm2).val
        + (if k.val = 0 then 2 else 0) * (Expression.eval env nm1).val
        + 2 * (Expression.eval env (d[k.val]'k.isLt)).val
        + 2 * (Expression.eval env (f[k.val]'k.isLt)).val
        + limbOfNat scalarOrder k.val * (Expression.eval env q).val := by
  show (((2 * limbOfNat eigenvalue k.val : ℕ) : F circomPrime) * Expression.eval env nm2
      + (((if k.val = 0 then 2 else 0 : ℕ)) : F circomPrime) * Expression.eval env nm1
      + ((2 : ℕ) : F circomPrime) * Expression.eval env (d[k.val]'k.isLt)
      + ((2 : ℕ) : F circomPrime) * Expression.eval env (f[k.val]'k.isLt)
      + ((limbOfNat scalarOrder k.val : ℕ) : F circomPrime) * Expression.eval env q).val = _
  rw [val_lin5 _ _ _ _ _ _ _ _ _ _ (by simpa using h)]

/-! ## Cell bounds -/

lemma lhsCell_lt (env : Environment (F circomPrime))
    (mu1 mu2 : Expression (F circomPrime)) (c e : Var Emu (F circomPrime))
    (k : Fin numLimbs)
    (hmu1 : (Expression.eval env mu1).val < 2 ^ 64)
    (hmu2 : (Expression.eval env mu2).val < 2 ^ 64)
    (hc : (Expression.eval env (c[k.val]'k.isLt)).val < 2 ^ 128)
    (he : (Expression.eval env (e[k.val]'k.isLt)).val < 2 ^ 128) :
    limbOfNat eigenvalue k.val * (Expression.eval env mu2).val
      + (if k.val = 0 then 1 else 0) * (Expression.eval env mu1).val
      + (Expression.eval env (c[k.val]'k.isLt)).val
      + (Expression.eval env (e[k.val]'k.isLt)).val
      + biasKRel * limbOfNat scalarOrder k.val < 2 ^ 131 := by
  have hA : limbOfNat eigenvalue k.val * (Expression.eval env mu2).val < 2 ^ 128 := by
    have := Nat.mul_lt_mul'' (limbOfNat_lt eigenvalue k.val) hmu2
    simpa only [limbBits, show (2:ℕ) ^ 64 * 2 ^ 64 = 2 ^ 128 from by norm_num] using this
  have hB : (if k.val = 0 then 1 else 0) * (Expression.eval env mu1).val < 2 ^ 64 := by
    split <;> omega
  have hE : biasKRel * limbOfNat scalarOrder k.val < 2 ^ 130 := by
    have := limbOfNat_lt scalarOrder k.val
    simp only [limbBits] at this
    simp only [biasKRel]
    omega
  omega

lemma rhsCell_lt (env : Environment (F circomPrime))
    (nm1 nm2 q : Expression (F circomPrime)) (d f : Var Emu (F circomPrime))
    (k : Fin numLimbs)
    (hnm1 : (Expression.eval env nm1).val < 2 ^ 64)
    (hnm2 : (Expression.eval env nm2).val < 2 ^ 64)
    (hd : (Expression.eval env (d[k.val]'k.isLt)).val < 2 ^ 128)
    (hf : (Expression.eval env (f[k.val]'k.isLt)).val < 2 ^ 128)
    (hq : (Expression.eval env q).val < 2 ^ 67) :
    2 * limbOfNat eigenvalue k.val * (Expression.eval env nm2).val
      + (if k.val = 0 then 2 else 0) * (Expression.eval env nm1).val
      + 2 * (Expression.eval env (d[k.val]'k.isLt)).val
      + 2 * (Expression.eval env (f[k.val]'k.isLt)).val
      + limbOfNat scalarOrder k.val * (Expression.eval env q).val < 2 ^ 132 := by
  have hA : limbOfNat eigenvalue k.val * (Expression.eval env nm2).val < 2 ^ 128 := by
    have := Nat.mul_lt_mul'' (limbOfNat_lt eigenvalue k.val) hnm2
    simpa only [limbBits, show (2:ℕ) ^ 64 * 2 ^ 64 = 2 ^ 128 from by norm_num] using this
  have hB : (if k.val = 0 then 2 else 0) * (Expression.eval env nm1).val < 2 ^ 65 := by
    split <;> omega
  have hE : limbOfNat scalarOrder k.val * (Expression.eval env q).val < 2 ^ 131 := by
    have := Nat.mul_lt_mul'' (limbOfNat_lt scalarOrder k.val) hq
    simpa only [limbBits, show (2:ℕ) ^ 64 * 2 ^ 67 = 2 ^ 131 from by norm_num] using this
  have hA2 : 2 * limbOfNat eigenvalue k.val * (Expression.eval env nm2).val < 2 ^ 129 := by
    rw [Nat.mul_assoc]; omega
  omega

/-! ## `polyValue` of the two sides -/

lemma limb_sum_eigenvalue :
    limbOfNat eigenvalue 0 + limbOfNat eigenvalue 1 * 2 ^ 64
      + limbOfNat eigenvalue 2 * 2 ^ 128 + limbOfNat eigenvalue 3 * 2 ^ 192 = eigenvalue := by
  decide

lemma limb_sum_order :
    limbOfNat scalarOrder 0 + limbOfNat scalarOrder 1 * 2 ^ 64
      + limbOfNat scalarOrder 2 * 2 ^ 128 + limbOfNat scalarOrder 3 * 2 ^ 192
      = scalarOrder := by
  decide

lemma relLhs_polyValue (env : Environment (F circomPrime))
    (mu1 mu2 : Expression (F circomPrime)) (c e : Var Emu (F circomPrime))
    (hmu1 : (Expression.eval env mu1).val < 2 ^ 64)
    (hmu2 : (Expression.eval env mu2).val < 2 ^ 64)
    (hc : ∀ k : Fin numLimbs, (Expression.eval env (c[k.val]'k.isLt)).val < 2 ^ 128)
    (he : ∀ k : Fin numLimbs, (Expression.eval env (e[k.val]'k.isLt)).val < 2 ^ 128) :
    polyValue 64 (Vector.map (Expression.eval env) (relLhs mu1 mu2 c e))
      = eigenvalue * (Expression.eval env mu2).val + (Expression.eval env mu1).val
        + BigInt.value 64 (Vector.map (Expression.eval env) c)
        + BigInt.value 64 (Vector.map (Expression.eval env) e)
        + biasKRel * scalarOrder := by
  have hcell : ∀ (k : ℕ) (hk : k < numLimbs),
      (Expression.eval env ((relLhs mu1 mu2 c e)[k]'hk)).val
        = limbOfNat eigenvalue k * (Expression.eval env mu2).val
          + (if k = 0 then 1 else 0) * (Expression.eval env mu1).val
          + (Expression.eval env (c[k]'hk)).val
          + (Expression.eval env (e[k]'hk)).val
          + biasKRel * limbOfNat scalarOrder k := by
    intro k hk
    rw [show (relLhs mu1 mu2 c e)[k]'hk = lhsCell mu1 mu2 c e ⟨k, hk⟩ from by
      simp only [relLhs, Vector.getElem_ofFn]]
    refine lhsCell_val env mu1 mu2 c e ⟨k, hk⟩ ?_
    have := lhsCell_lt env mu1 mu2 c e ⟨k, hk⟩ hmu1 hmu2 (hc ⟨k, hk⟩) (he ⟨k, hk⟩)
    have hp : (2:ℕ) ^ 131 < circomPrime := by decide
    omega
  rw [MulModFold.polyValue_four, MulModFold.bigIntValue_four, MulModFold.bigIntValue_four]
  simp only [Vector.getElem_map, hcell, reduceIte, one_mul, zero_mul, add_zero]
  have hA := limb_sum_eigenvalue
  have hB := limb_sum_order
  set a0 := limbOfNat eigenvalue 0
  set a1 := limbOfNat eigenvalue 1
  set a2 := limbOfNat eigenvalue 2
  set a3 := limbOfNat eigenvalue 3
  set b0 := limbOfNat scalarOrder 0
  set b1 := limbOfNat scalarOrder 1
  set b2 := limbOfNat scalarOrder 2
  set b3 := limbOfNat scalarOrder 3
  simp only [if_neg (by decide : ¬(1:ℕ) = 0), if_neg (by decide : ¬(2:ℕ) = 0),
    if_neg (by decide : ¬(3:ℕ) = 0), zero_mul, add_zero]
  rw [← hA, ← hB]
  ring

lemma relRhs_polyValue (env : Environment (F circomPrime))
    (nm1 nm2 q : Expression (F circomPrime)) (d f : Var Emu (F circomPrime))
    (hnm1 : (Expression.eval env nm1).val < 2 ^ 64)
    (hnm2 : (Expression.eval env nm2).val < 2 ^ 64)
    (hd : ∀ k : Fin numLimbs, (Expression.eval env (d[k.val]'k.isLt)).val < 2 ^ 128)
    (hf : ∀ k : Fin numLimbs, (Expression.eval env (f[k.val]'k.isLt)).val < 2 ^ 128)
    (hq : (Expression.eval env q).val < 2 ^ 67) :
    polyValue 64 (Vector.map (Expression.eval env) (relRhs nm1 nm2 q d f))
      = 2 * (eigenvalue * (Expression.eval env nm2).val) + 2 * (Expression.eval env nm1).val
        + 2 * BigInt.value 64 (Vector.map (Expression.eval env) d)
        + 2 * BigInt.value 64 (Vector.map (Expression.eval env) f)
        + scalarOrder * (Expression.eval env q).val := by
  have hcell : ∀ (k : ℕ) (hk : k < numLimbs),
      (Expression.eval env ((relRhs nm1 nm2 q d f)[k]'hk)).val
        = 2 * limbOfNat eigenvalue k * (Expression.eval env nm2).val
          + (if k = 0 then 2 else 0) * (Expression.eval env nm1).val
          + 2 * (Expression.eval env (d[k]'hk)).val
          + 2 * (Expression.eval env (f[k]'hk)).val
          + limbOfNat scalarOrder k * (Expression.eval env q).val := by
    intro k hk
    rw [show (relRhs nm1 nm2 q d f)[k]'hk = rhsCell nm1 nm2 q d f ⟨k, hk⟩ from by
      simp only [relRhs, Vector.getElem_ofFn]]
    refine rhsCell_val env nm1 nm2 q d f ⟨k, hk⟩ ?_
    have := rhsCell_lt env nm1 nm2 q d f ⟨k, hk⟩ hnm1 hnm2 (hd ⟨k, hk⟩) (hf ⟨k, hk⟩) hq
    have hp : (2:ℕ) ^ 132 < circomPrime := by decide
    omega
  rw [MulModFold.polyValue_four, MulModFold.bigIntValue_four, MulModFold.bigIntValue_four]
  simp only [Vector.getElem_map, hcell, reduceIte, one_mul, zero_mul, add_zero]
  have hA := limb_sum_eigenvalue
  have hB := limb_sum_order
  set a0 := limbOfNat eigenvalue 0
  set a1 := limbOfNat eigenvalue 1
  set a2 := limbOfNat eigenvalue 2
  set a3 := limbOfNat eigenvalue 3
  set b0 := limbOfNat scalarOrder 0
  set b1 := limbOfNat scalarOrder 1
  set b2 := limbOfNat scalarOrder 2
  set b3 := limbOfNat scalarOrder 3
  simp only [if_neg (by decide : ¬(1:ℕ) = 0), if_neg (by decide : ¬(2:ℕ) = 0),
    if_neg (by decide : ¬(3:ℕ) = 0), zero_mul, add_zero]
  rw [← hA, ← hB]
  ring

/-! ## Tight caps at position 1

Only `wfRel 0` is charged by the grouped carry, and it is driven by the cap at
position 1 through the group-0 offset.  The generic `2^131` / `2^132` bounds are
loose there: the actual maxima are `< 5·2^128` and `< 10·2^128`. -/

lemma cell1_bound (kv M M1 X Y : ℕ) (hkv : kv = 1)
    (hM : M < 2 ^ 64) (hX : X < 2 ^ 128) (hY : Y < 2 ^ 128) :
    limbOfNat eigenvalue kv * M + (if kv = 0 then 1 else 0) * M1 + X + Y
      + biasKRel * limbOfNat scalarOrder kv < 5 * 2 ^ 128 := by
  subst hkv
  have hA : limbOfNat eigenvalue 1 * M ≤ limbOfNat eigenvalue 1 * (2 ^ 64 - 1) :=
    Nat.mul_le_mul_left _ (by omega)
  have hAv : limbOfNat eigenvalue 1 * (2 ^ 64 - 1)
      = 24165657730997595916524188993132075400 := by decide
  have hBv : biasKRel * limbOfNat scalarOrder 1
      = 992577389104869080242024537213332619264 := by decide
  have h128 : (2:ℕ) ^ 128 = 340282366920938463463374607431768211456 := by norm_num
  simp only [if_neg (by decide : ¬(1:ℕ) = 0), Nat.zero_mul, Nat.add_zero]
  omega

lemma cell1_boundR (kv M M1 X Y Q : ℕ) (hkv : kv = 1)
    (hM : M < 2 ^ 64) (hX : X < 2 ^ 128) (hY : Y < 2 ^ 128) (hQ : Q < 2 ^ 67) :
    2 * limbOfNat eigenvalue kv * M + (if kv = 0 then 2 else 0) * M1 + 2 * X + 2 * Y
      + limbOfNat scalarOrder kv * Q < 10 * 2 ^ 128 := by
  subst hkv
  have hA : 2 * limbOfNat eigenvalue 1 * M ≤ 2 * limbOfNat eigenvalue 1 * (2 ^ 64 - 1) :=
    Nat.mul_le_mul_left _ (by omega)
  have hAv : 2 * limbOfNat eigenvalue 1 * (2 ^ 64 - 1)
      = 48331315461995191833048377986264150800 := by decide
  have hB : limbOfNat scalarOrder 1 * Q ≤ limbOfNat scalarOrder 1 * (2 ^ 67 - 1) :=
    Nat.mul_le_mul_left _ (by omega)
  have hBv : limbOfNat scalarOrder 1 * (2 ^ 67 - 1)
      = 1985154778209738160470597142406321627077 := by decide
  have h128 : (2:ℕ) ^ 128 = 340282366920938463463374607431768211456 := by norm_num
  simp only [if_neg (by decide : ¬(1:ℕ) = 0), Nat.zero_mul, Nat.add_zero]
  omega

/-! ## Per-cell caps as stated by `GroupedEqXV.Assumptions` -/

lemma relLhs_cap (env : Environment (F circomPrime))
    (mu1 mu2 : Expression (F circomPrime)) (c e : Var Emu (F circomPrime))
    (hmu1 : (Expression.eval env mu1).val < 2 ^ 64)
    (hmu2 : (Expression.eval env mu2).val < 2 ^ 64)
    (hc : ∀ k : Fin numLimbs, (Expression.eval env (c[k.val]'k.isLt)).val < 2 ^ 128)
    (he : ∀ k : Fin numLimbs, (Expression.eval env (e[k.val]'k.isLt)).val < 2 ^ 128) :
    ∀ k : Fin numLimbs,
      (Expression.eval env ((relLhs mu1 mu2 c e)[k.val]'k.isLt)).val < nfRelL k.val := by
  intro k
  have hb := lhsCell_lt env mu1 mu2 c e k hmu1 hmu2 (hc k) (he k)
  have hp : (2:ℕ) ^ 131 < circomPrime := by decide
  have hcell : (relLhs mu1 mu2 c e)[k.val]'k.isLt = lhsCell mu1 mu2 c e k := by
    simp only [relLhs, Vector.getElem_ofFn]
  rw [hcell, lhsCell_val env mu1 mu2 c e k (by omega)]
  by_cases hk : k.val = 1
  · rw [show nfRelL k.val = 5 * 2 ^ 128 from by simp only [nfRelL, if_pos hk]]
    exact cell1_bound k.val _ _ _ _ hk hmu2 (hc k) (he k)
  · rw [show nfRelL k.val = 2 ^ 131 from by simp only [nfRelL, if_neg hk]]
    exact hb

lemma relRhs_cap (env : Environment (F circomPrime))
    (nm1 nm2 q : Expression (F circomPrime)) (d f : Var Emu (F circomPrime))
    (hnm1 : (Expression.eval env nm1).val < 2 ^ 64)
    (hnm2 : (Expression.eval env nm2).val < 2 ^ 64)
    (hd : ∀ k : Fin numLimbs, (Expression.eval env (d[k.val]'k.isLt)).val < 2 ^ 128)
    (hf : ∀ k : Fin numLimbs, (Expression.eval env (f[k.val]'k.isLt)).val < 2 ^ 128)
    (hq : (Expression.eval env q).val < 2 ^ 67) :
    ∀ k : Fin numLimbs,
      (Expression.eval env ((relRhs nm1 nm2 q d f)[k.val]'k.isLt)).val < nfRelR k.val := by
  intro k
  have hb := rhsCell_lt env nm1 nm2 q d f k hnm1 hnm2 (hd k) (hf k) hq
  have hp : (2:ℕ) ^ 132 < circomPrime := by decide
  have hcell : (relRhs nm1 nm2 q d f)[k.val]'k.isLt = rhsCell nm1 nm2 q d f k := by
    simp only [relRhs, Vector.getElem_ofFn]
  rw [hcell, rhsCell_val env nm1 nm2 q d f k (by omega)]
  by_cases hk : k.val = 1
  · rw [show nfRelR k.val = 10 * 2 ^ 128 from by simp only [nfRelR, if_pos hk]]
    exact cell1_boundR k.val _ _ _ _ _ hk hnm2 (hd k) (hf k) hq
  · rw [show nfRelR k.val = 2 ^ 132 from by simp only [nfRelR, if_neg hk]]
    exact hb

/-! ## Affineness -/

open Challenge.CostR1CS in
lemma affineW_relLhs (mu1 mu2 : Expression (F circomPrime)) (c e : Var Emu (F circomPrime))
    (h1 : Affine mu1) (h2 : Affine mu2) (hc : AffineW c) (he : AffineW e) :
    AffineW (relLhs mu1 mu2 c e) := by
  intro i hi
  unfold relLhs
  rw [Vector.getElem_ofFn]
  unfold lhsCell
  exact Affine.add (Affine.add (Affine.add (Affine.add
    (Affine.fconst_mul _ h2) (Affine.fconst_mul _ h1))
    (Affine.fconst_mul _ (hc i hi))) (Affine.fconst_mul _ (he i hi)))
    (Affine.fconst_mul _ (Affine.const _))

open Challenge.CostR1CS in
lemma affineW_relRhs (nm1 nm2 q : Expression (F circomPrime)) (d f : Var Emu (F circomPrime))
    (h1 : Affine nm1) (h2 : Affine nm2) (hq : Affine q) (hd : AffineW d) (hf : AffineW f) :
    AffineW (relRhs nm1 nm2 q d f) := by
  intro i hi
  unfold relRhs
  rw [Vector.getElem_ofFn]
  unfold rhsCell
  exact Affine.add (Affine.add (Affine.add (Affine.add
    (Affine.fconst_mul _ h2) (Affine.fconst_mul _ h1))
    (Affine.fconst_mul _ (hd i hi))) (Affine.fconst_mul _ (hf i hi)))
    (Affine.fconst_mul _ hq)

end RelCells
end Solution.Secp256k1ScalarMul
