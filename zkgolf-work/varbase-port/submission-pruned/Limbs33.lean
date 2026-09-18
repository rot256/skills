import Solution.Secp256k1ScalarMul.Limbs32
import Solution.Secp256k1ScalarMul.Params
import Solution.Secp256k1ScalarMul.MulMod
import Solution.Secp256k1ScalarMul.CompleteAddTheorems

/-!
# The widened 32-bit limb view

A value carried as eight 32-bit limbs whose limbs may be *sums* of two such
limbs (so `< 2^33 − 1`).  Its four 64-bit limbs are still the free affine
recombination `x_k = v_{2k} + 2^32·v_{2k+1}`, the recombined limbs are `< 2^65`
(`Fe.NormW2`), and the represented value is unchanged — which is all a folded
modular certificate in base `2^32` needs.
-/

namespace Solution.Secp256k1ScalarMul

open Solution.Secp256k1ScalarMul.Limbs32

/-- Limb cap of the widened 32-bit view: a limb of `λ₁ + w` is a sum of two
32-bit limbs, hence at most `2^33 − 2`. -/
def widen33 : ℕ := 2 ^ 33 - 1

/-- Limbs of a widened eight-limb value. -/
def Norm33 (v : BigInt 8 (F circomPrime)) : Prop := ∀ i : Fin 8, (v[i]).val < widen33

/-- Value of a 64-bit limb assembled from two widened 32-bit halves. -/
lemma val_combine33 {a b : F circomPrime} (ha : a.val < widen33) (hb : b.val < widen33) :
    (a + Limbs32.twoPow32 * b).val = a.val + 2 ^ 32 * b.val := by
  simp only [widen33] at ha hb
  have hp : (2 : ℕ) ^ 65 + 2 ^ 33 < circomPrime := by decide
  have hmul : (Limbs32.twoPow32 * b).val = 2 ^ 32 * b.val := by
    rw [ZMod.val_mul_of_lt (by rw [Limbs32.twoPow32_val]; omega), Limbs32.twoPow32_val]
  rw [ZMod.val_add_of_lt (by rw [hmul]; omega), hmul]

lemma value_emuOf32_33 {vv : BigInt 8 (F circomPrime)} (h : Norm33 vv) :
    BigInt.value limbBits (Limbs32.emuOf32V vv) = BigInt.value 32 vv := by
  have hlt : ∀ i : Fin 8, (vv[i.val]'i.isLt).val < widen33 := fun i => h i
  have e : ∀ k : Fin numLimbs, ((Limbs32.emuOf32V vv)[k.val]'k.isLt).val
      = (vv[2 * k.val]'(by have := k.isLt; simp only [numLimbs] at this; omega)).val
        + 2 ^ 32 * (vv[2 * k.val + 1]'(by
            have := k.isLt; simp only [numLimbs] at this; omega)).val := by
    intro k
    simp only [Limbs32.emuOf32V, Vector.getElem_ofFn]
    exact val_combine33 (by simpa using hlt ⟨2 * k.val, by
        have := k.isLt; simp only [numLimbs] at this; omega⟩)
      (by simpa using hlt ⟨2 * k.val + 1, by
        have := k.isLt; simp only [numLimbs] at this; omega⟩)
  have e0 := e ⟨0, by decide⟩
  have e1 := e ⟨1, by decide⟩
  have e2 := e ⟨2, by decide⟩
  have e3 := e ⟨3, by decide⟩
  rw [Limbs32.value64_four, Limbs32.value32_eight]
  norm_num at e0 e1 e2 e3
  omega

lemma decodeFe_emuOf32V_33 {vv : BigInt 8 (F circomPrime)} (h : Norm33 vv) :
    decodeFe (Limbs32.emuOf32V vv) = ((BigInt.value 32 vv : ℕ) : Specs.Secp256k1.Fp) := by
  rw [decodeFe, value_emuOf32_33 h]

end Solution.Secp256k1ScalarMul
