import Solution.Secp256k1ScalarMul.Theorems
import Solution.Secp256k1ScalarMul.Params
import Solution.Secp256k1ScalarMul.Normalize
import Solution.Secp256k1ScalarMul.MulMod

/-!
# The 32-bit limb view of an emulated field element

A value that is materialised as **eight 32-bit limbs** (8 witnesses plus
`Normalize` at `B = 32`, i.e. `8 + 8·31 = 256` allocations and `8·32 = 256`
constraints) also provides its four 64-bit limbs *for free*, as the affine
recombination `x_k = v_{2k} + 2^32·v_{2k+1}`.

That costs exactly what materialising four 64-bit limbs costs
(`4 + 4·63 = 256` allocations, `4·64 = 256` constraints), so the 32-bit view is
free — and it is what lets the modular-multiplication certificate run in base
`2^32`, where the pseudo-Mersenne fold constant `2^32 + 977` is limb-aligned
(see `MulModFold32`).
-/

namespace Solution.Secp256k1ScalarMul

open Solution.Secp256k1ScalarMul.Limbs

/-- `BigIntParams` for the eight-limb, 32-bit view. -/
def secpParams32 : BigIntParams circomPrime 8 where
  B := 32
  W := 40
  hB := by decide
  hW := by decide
  hB1 := by decide
  hWB := by decide
  hWp := by decide
  hp := by decide

namespace Limbs32

def twoPow32 : F circomPrime := ((2 ^ 32 : ℕ) : F circomPrime)

def twoPow32E : Expression (F circomPrime) := (twoPow32 : Expression (F circomPrime))

lemma twoPow32_val : twoPow32.val = 2 ^ 32 :=
  ZMod.val_natCast_of_lt (by decide)

/-- Value of a 64-bit limb assembled from two 32-bit halves. -/
lemma val_combine {a b : F circomPrime} (ha : a.val < 2 ^ 32) (hb : b.val < 2 ^ 32) :
    (a + twoPow32 * b).val = a.val + 2 ^ 32 * b.val := by
  have hbb : 2 ^ 32 * b.val < 2 ^ 64 := by
    have hle : b.val ≤ 2 ^ 32 - 1 := by omega
    calc 2 ^ 32 * b.val ≤ 2 ^ 32 * (2 ^ 32 - 1) := Nat.mul_le_mul_left _ hle
      _ < 2 ^ 64 := by norm_num
  have hp : (2 : ℕ) ^ 64 + 2 ^ 32 < circomPrime := by decide
  have hmul : (twoPow32 * b).val = 2 ^ 32 * b.val := by
    rw [ZMod.val_mul_of_lt (by rw [twoPow32_val]; omega), twoPow32_val]
  rw [ZMod.val_add_of_lt (by rw [hmul]; omega), hmul]

private lemma idx_lt (k : Fin numLimbs) : 2 * k.val < 8 ∧ 2 * k.val + 1 < 8 := by
  have := k.isLt
  simp only [numLimbs] at this
  omega

/-- The four 64-bit limbs, as free affine expressions in the eight 32-bit ones. -/
def emuOf32 (v : Var (BigInt 8) (F circomPrime)) : Var Emu (F circomPrime) :=
  Vector.ofFn fun k : Fin numLimbs =>
    (v[2 * k.val]'(idx_lt k).1) + twoPow32E * (v[2 * k.val + 1]'(idx_lt k).2)

/-- Value-level counterpart of `emuOf32`. -/
def emuOf32V (v : BigInt 8 (F circomPrime)) : Emu (F circomPrime) :=
  Vector.ofFn fun k : Fin numLimbs =>
    (v[2 * k.val]'(idx_lt k).1) + twoPow32 * (v[2 * k.val + 1]'(idx_lt k).2)

lemma eval_emuOf32 (env : Environment (F circomPrime)) (v : Var (BigInt 8) (F circomPrime)) :
    Vector.map (Expression.eval env) (emuOf32 v)
      = emuOf32V (Vector.map (Expression.eval env) v) := by
  apply Vector.ext
  intro i hi
  simp only [emuOf32, emuOf32V, Vector.getElem_map, Vector.getElem_ofFn]
  rfl

lemma normalized_emuOf32 {vv : BigInt 8 (F circomPrime)} (h : BigInt.Normalized 32 vv) :
    BigInt.Normalized limbBits (emuOf32V vv) := by
  intro k
  have h1 := h ⟨2 * k.val, (idx_lt k).1⟩
  have h2 := h ⟨2 * k.val + 1, (idx_lt k).2⟩
  simp only [Fin.getElem_fin] at h1 h2
  simp only [emuOf32V, Fin.getElem_fin, Vector.getElem_ofFn]
  rw [val_combine h1 h2]
  have hb : (2 : ℕ) ^ limbBits = 2 ^ 64 := rfl
  rw [hb]
  have hm : 2 ^ 32 * (vv[2 * k.val + 1]'(idx_lt k).2).val ≤ 2 ^ 32 * (2 ^ 32 - 1) :=
    Nat.mul_le_mul_left _ (by omega)
  have hnum : (2 : ℕ) ^ 32 * (2 ^ 32 - 1) + 2 ^ 32 = 2 ^ 64 := by norm_num
  omega

lemma value32_eight (v : BigInt 8 (F circomPrime)) :
    BigInt.value 32 v = v[0].val + v[1].val * 2 ^ 32 + v[2].val * 2 ^ 64 + v[3].val * 2 ^ 96
      + v[4].val * 2 ^ 128 + v[5].val * 2 ^ 160 + v[6].val * 2 ^ 192 + v[7].val * 2 ^ 224 := by
  rw [BigInt.value_eq_sum]
  simp only [Fin.sum_univ_eight]
  norm_num

lemma value64_four (v : Emu (F circomPrime)) :
    BigInt.value limbBits v = v[0].val + v[1].val * 2 ^ 64 + v[2].val * 2 ^ 128
      + v[3].val * 2 ^ 192 := by
  rw [BigInt.value_eq_sum]
  simp only [Fin.sum_univ_four]
  norm_num

lemma value_emuOf32 {vv : BigInt 8 (F circomPrime)} (h : BigInt.Normalized 32 vv) :
    BigInt.value limbBits (emuOf32V vv) = BigInt.value 32 vv := by
  have e : ∀ k : Fin numLimbs, ((emuOf32V vv)[k.val]'k.isLt).val
      = (vv[2 * k.val]'(idx_lt k).1).val + 2 ^ 32 * (vv[2 * k.val + 1]'(idx_lt k).2).val := by
    intro k
    simp only [emuOf32V, Vector.getElem_ofFn]
    exact val_combine (by simpa using h ⟨2 * k.val, (idx_lt k).1⟩)
      (by simpa using h ⟨2 * k.val + 1, (idx_lt k).2⟩)
  have e0 := e ⟨0, by decide⟩
  have e1 := e ⟨1, by decide⟩
  have e2 := e ⟨2, by decide⟩
  have e3 := e ⟨3, by decide⟩
  rw [value64_four, value32_eight]
  norm_num at e0 e1 e2 e3
  omega

lemma emuOf32_map_stable {v : Var (BigInt 8) (F circomPrime)}
    {env env' : ProverEnvironment (F circomPrime)} (h : eval env v = eval env' v) :
    Vector.map (Expression.eval env.toEnvironment) (emuOf32 v)
      = Vector.map (Expression.eval env'.toEnvironment) (emuOf32 v) := by
  rw [eval_emuOf32, eval_emuOf32, MulMod.bigInt_map_eval_eq_of_eval_eq h]

lemma normalized_map_emuOf32 {env : Environment (F circomPrime)}
    {v : Var (BigInt 8) (F circomPrime)}
    (h : BigInt.Normalized limbBits (emuOf32V (Vector.map (Expression.eval env) v))) :
    BigInt.Normalized limbBits (Vector.map (Expression.eval env) (emuOf32 v)) := by
  rw [eval_emuOf32]; exact h

lemma normalized_map_emuOf32' {env : Environment (F circomPrime)}
    {v : Var (BigInt 8) (F circomPrime)}
    (h : BigInt.Normalized 32 (Vector.map (Expression.eval env) v)) :
    BigInt.Normalized limbBits (Vector.map (Expression.eval env) (emuOf32 v)) := by
  rw [eval_emuOf32]; exact normalized_emuOf32 h

lemma decodeFe_emuOf32V {vv : BigInt 8 (F circomPrime)} (h : BigInt.Normalized 32 vv) :
    decodeFe (emuOf32V vv) = ((BigInt.value 32 vv : ℕ) : Specs.Secp256k1.Fp) := by
  rw [decodeFe, value_emuOf32 h]

lemma decodeFe_map_emuOf32 {env : Environment (F circomPrime)}
    (v : Var (BigInt 8) (F circomPrime)) :
    decodeFe (Vector.map (Expression.eval env) (emuOf32 v))
      = decodeFe (emuOf32V (Vector.map (Expression.eval env) v)) := by
  rw [eval_emuOf32]

lemma decodeMap_emuOf32 {env : Environment (F circomPrime)}
    (v : Var (BigInt 8) (F circomPrime)) :
    Vector.map (Expression.eval env) (emuOf32 v) = emuOf32V (Vector.map (Expression.eval env) v) :=
  eval_emuOf32 env v

/-! ## Building the 32-bit limbs of a natural number -/

def limbOfNat32 (v k : ℕ) : ℕ := v / 2 ^ (32 * k) % 2 ^ 32

lemma limbOfNat32_lt (v k : ℕ) : limbOfNat32 v k < 2 ^ 32 :=
  Nat.mod_lt _ (Nat.two_pow_pos 32)

def emu32OfNat (v : ℕ) : BigInt 8 (F circomPrime) :=
  Vector.ofFn fun k : Fin 8 => ((limbOfNat32 v k.val : ℕ) : F circomPrime)

lemma val_limbOfNat32 (v k : ℕ) :
    (((limbOfNat32 v k : ℕ) : F circomPrime)).val = limbOfNat32 v k :=
  ZMod.val_natCast_of_lt (lt_trans (limbOfNat32_lt v k) (by decide))

lemma emu32OfNat_normalized (v : ℕ) : BigInt.Normalized 32 (emu32OfNat v) := by
  intro i
  simp only [emu32OfNat, Fin.getElem_fin, Vector.getElem_ofFn, val_limbOfNat32]
  exact limbOfNat32_lt v i.val

/-- The 64-bit view of the 32-bit decomposition is the 64-bit decomposition. -/
lemma emuOf32V_emu32OfNat (v : ℕ) : emuOf32V (emu32OfNat v) = emuOfNat v := by
  apply Vector.ext
  intro i hi
  simp only [emuOf32V, emu32OfNat, emuOfNat, Vector.getElem_ofFn]
  have hnat : limbOfNat v i = limbOfNat32 v (2 * i) + 2 ^ 32 * limbOfNat32 v (2 * i + 1) := by
    simp only [limbOfNat, limbOfNat32, limbBits]
    have h1 : 32 * (2 * i) = 64 * i := by ring
    have h2 : (32 : ℕ) * (2 * i + 1) = 64 * i + 32 := by ring
    have h3 : 64 * i = limbBits * i := by simp only [limbBits]
    rw [h1, h2, pow_add, ← Nat.div_div_eq_div_mul]
    have h4 : limbBits * i = 64 * i := by simp only [limbBits]
    rw [h4]
    omega
  rw [hnat]
  push_cast [twoPow32]
  ring

/-! ## Compile-time constants in the 32-bit view -/

/-- The base-`2^32` limb vector of a compile-time constant, as an expression. -/
def emu32Const (v : ℕ) : Var (BigInt 8) (F circomPrime) :=
  Vector.ofFn fun k : Fin 8 =>
    (((limbOfNat32 v k.val : ℕ) : F circomPrime) : Expression (F circomPrime))

/-- The base-`2^32` zero constant. -/
def zeroConst32 : Var (BigInt 8) (F circomPrime) := emu32Const 0

lemma eval_emu32Const (env : Environment (F circomPrime)) (v : ℕ) :
    Vector.map (Expression.eval env) (emu32Const v) = emu32OfNat v := by
  apply Vector.ext
  intro k hk
  simp only [emu32Const, emu32OfNat, Vector.getElem_map, Vector.getElem_ofFn]
  rfl

lemma eval_zeroConst32 (env : Environment (F circomPrime)) :
    Vector.map (Expression.eval env) zeroConst32 = emu32OfNat 0 :=
  eval_emu32Const env 0

lemma value_emu32OfNat_zero : BigInt.value 32 (emu32OfNat 0) = 0 := by
  rw [BigInt.value_eq_sum]
  simp only [emu32OfNat, Fin.getElem_fin, Vector.getElem_ofFn, limbOfNat32,
    Nat.zero_div, Nat.zero_mod, Nat.cast_zero, ZMod.val_zero, zero_mul]
  simp

end Limbs32
end Solution.Secp256k1ScalarMul
