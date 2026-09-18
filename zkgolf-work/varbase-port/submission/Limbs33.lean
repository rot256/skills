import Solution.Secp256k1ScalarMul.Limbs32
import Solution.Secp256k1ScalarMul.ParamsW2

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

lemma hcap33 : 8 * (widen33 * widen33) ≤ 2 ^ 69 := by
  simp only [widen33]
  norm_num

/-- Limbs of a widened eight-limb value. -/
def Norm33 (v : BigInt 8 (F circomPrime)) : Prop := ∀ i : Fin 8, (v[i]).val < widen33

lemma norm33_of_normalized {v : BigInt 8 (F circomPrime)} (h : BigInt.Normalized 32 v) :
    Norm33 v := by
  intro i
  have := h i
  simp only [widen33]
  omega

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

/-- The 64-bit view of a widened 32-bit value is doubly unreduced. -/
lemma normW2_emuOf32V {vv : BigInt 8 (F circomPrime)} (h : Norm33 vv) :
    Fe.NormW2 (Limbs32.emuOf32V vv) := by
  intro k
  have h1 : (vv[2 * k.val]'(by have := k.isLt; simp only [numLimbs] at this; omega)).val
      < widen33 := h ⟨2 * k.val, by have := k.isLt; simp only [numLimbs] at this; omega⟩
  have h2 : (vv[2 * k.val + 1]'(by have := k.isLt; simp only [numLimbs] at this; omega)).val
      < widen33 := h ⟨2 * k.val + 1, by have := k.isLt; simp only [numLimbs] at this; omega⟩
  simp only [Limbs32.emuOf32V, Vector.getElem_ofFn]
  rw [val_combine33 h1 h2]
  simp only [widen33, limbBits] at h1 h2 ⊢
  have hm : 2 ^ 32 * (vv[2 * k.val + 1]'(by
      have := k.isLt; simp only [numLimbs] at this; omega)).val
      ≤ 2 ^ 32 * (2 ^ 33 - 2) := Nat.mul_le_mul_left _ (by omega)
  have : (2:ℕ) ^ 32 * (2 ^ 33 - 2) + (2 ^ 33 - 2) < 2 ^ (64 + 1) := by norm_num
  omega


/-- Limbwise sum of two 32-bit-limb values is widened. -/
lemma norm33_sum {u v : BigInt 8 (F circomPrime)}
    (hu : BigInt.Normalized 32 u) (hv : BigInt.Normalized 32 v) :
    Norm33 (Vector.ofFn fun k : Fin 8 => (u[k.val]'k.isLt) + (v[k.val]'k.isLt)) := by
  intro i
  have hu' := hu i
  have hv' := hv i
  simp only [Fin.getElem_fin, Vector.getElem_ofFn]
  have hlt : (u[i.val]'i.isLt).val + (v[i.val]'i.isLt).val < circomPrime := by
    have : (2:ℕ) ^ 32 + 2 ^ 32 < circomPrime := by decide
    simp only [Fin.getElem_fin] at hu' hv'
    omega
  rw [ZMod.val_add_of_lt hlt]
  simp only [widen33]
  simp only [Fin.getElem_fin] at hu' hv'
  omega

/-- `BigInt.value 32` is additive on limbwise sums of 32-bit-limb values. -/
lemma value32_sum {u v : BigInt 8 (F circomPrime)}
    (hu : BigInt.Normalized 32 u) (hv : BigInt.Normalized 32 v) :
    BigInt.value 32 (Vector.ofFn fun k : Fin 8 => (u[k.val]'k.isLt) + (v[k.val]'k.isLt))
      = BigInt.value 32 u + BigInt.value 32 v := by
  have hcell : ∀ i : Fin 8,
      ((Vector.ofFn fun k : Fin 8 => (u[k.val]'k.isLt) + (v[k.val]'k.isLt))[i.val]'i.isLt).val
        = (u[i.val]'i.isLt).val + (v[i.val]'i.isLt).val := by
    intro i
    have hu' := hu i
    have hv' := hv i
    simp only [Fin.getElem_fin] at hu' hv'
    simp only [Vector.getElem_ofFn]
    refine ZMod.val_add_of_lt ?_
    have : (2:ℕ) ^ 32 + 2 ^ 32 < circomPrime := by decide
    omega
  have h0 := hcell ⟨0, by decide⟩
  have h1 := hcell ⟨1, by decide⟩
  have h2 := hcell ⟨2, by decide⟩
  have h3 := hcell ⟨3, by decide⟩
  have h4 := hcell ⟨4, by decide⟩
  have h5 := hcell ⟨5, by decide⟩
  have h6 := hcell ⟨6, by decide⟩
  have h7 := hcell ⟨7, by decide⟩
  rw [Limbs32.value32_eight, Limbs32.value32_eight, Limbs32.value32_eight,
    h0, h1, h2, h3, h4, h5, h6, h7]
  ring

/-- Decoding a limbwise sum of two 32-bit-limb values. -/
lemma decodeFe_emuOf32V_sum {u v : BigInt 8 (F circomPrime)}
    (hu : BigInt.Normalized 32 u) (hv : BigInt.Normalized 32 v) :
    decodeFe (Limbs32.emuOf32V (Vector.ofFn fun k : Fin 8 => (u[k.val]'k.isLt) + (v[k.val]'k.isLt)))
      = decodeFe (Limbs32.emuOf32V u) + decodeFe (Limbs32.emuOf32V v) := by
  rw [decodeFe_emuOf32V_33 (norm33_sum hu hv), Limbs32.decodeFe_emuOf32V hu,
    Limbs32.decodeFe_emuOf32V hv, value32_sum hu hv]
  push_cast
  ring

lemma norm33_of_eq {u v : BigInt 8 (F circomPrime)} (h : u = v) (hv : Norm33 v) : Norm33 u := by
  rw [h]; exact hv

/-- Evaluation of a limbwise sum of two eight-limb expression vectors. -/
lemma map_eval_sum8 (env : Environment (F circomPrime))
    (uv vv : Var (BigInt 8) (F circomPrime)) :
    Vector.map (Expression.eval env)
      (Vector.ofFn fun k : Fin 8 => uv[k.val]'k.isLt + vv[k.val]'k.isLt)
      = Vector.ofFn fun k : Fin 8 =>
          (Vector.map (Expression.eval env) uv)[k.val]'k.isLt
          + (Vector.map (Expression.eval env) vv)[k.val]'k.isLt := by
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_map, Vector.getElem_ofFn]
  rfl

end Solution.Secp256k1ScalarMul
