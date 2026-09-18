import Solution.Secp256k1ScalarMul.Limbs32
import Solution.Secp256k1ScalarMul.ToBytes

/-!
# The 32-bit limb view of a byte-serialised coordinate

`ValidPBytes` already emits the 32 bytes of a canonical coordinate as *affine*
expressions in the bits its range check allocated.  Four consecutive bytes are
exactly one 32-bit limb, so the eight-limb base-`2^32` view of the same value is
another free affine recombination — no witness, no row.

That is what lets a modular-multiplication certificate whose operand is an
already-validated coordinate run in base `2^32` (`MulModFold32`, 101/103)
instead of base `2^64` (`MulModFold`, 176/178).
-/

namespace Solution.Secp256k1ScalarMul
namespace Bytes32

open Solution.Secp256k1ScalarMul.Limbs

private lemma idx0 (j : Fin 8) : 4 * j.val < coordBytes := by
  have := j.isLt; simp only [coordBytes]; omega

private lemma idx1 (j : Fin 8) : 4 * j.val + 1 < coordBytes := by
  have := j.isLt; simp only [coordBytes]; omega

private lemma idx2 (j : Fin 8) : 4 * j.val + 2 < coordBytes := by
  have := j.isLt; simp only [coordBytes]; omega

private lemma idx3 (j : Fin 8) : 4 * j.val + 3 < coordBytes := by
  have := j.isLt; simp only [coordBytes]; omega

/-- `2^8`, `2^16`, `2^24` as field constants. -/
def c8 : F circomPrime := ((2 ^ 8 : ℕ) : F circomPrime)
def c16 : F circomPrime := ((2 ^ 16 : ℕ) : F circomPrime)
def c24 : F circomPrime := ((2 ^ 24 : ℕ) : F circomPrime)

/-- The eight 32-bit limbs of a byte vector, as affine expressions. -/
def ofBytes (b : Var (fields coordBytes) (F circomPrime)) : Var (BigInt 8) (F circomPrime) :=
  Vector.ofFn fun j : Fin 8 =>
    (b[4 * j.val]'(idx0 j))
      + (b[4 * j.val + 1]'(idx1 j)) * (c8 : Expression (F circomPrime))
      + (b[4 * j.val + 2]'(idx2 j)) * (c16 : Expression (F circomPrime))
      + (b[4 * j.val + 3]'(idx3 j)) * (c24 : Expression (F circomPrime))

/-- Value-level counterpart of `ofBytes`. -/
def ofBytesV (b : Vector (F circomPrime) coordBytes) : BigInt 8 (F circomPrime) :=
  Vector.ofFn fun j : Fin 8 =>
    (b[4 * j.val]'(idx0 j))
      + (b[4 * j.val + 1]'(idx1 j)) * c8
      + (b[4 * j.val + 2]'(idx2 j)) * c16
      + (b[4 * j.val + 3]'(idx3 j)) * c24

lemma eval_ofBytes (env : Environment (F circomPrime))
    (b : Var (fields coordBytes) (F circomPrime)) :
    Vector.map (Expression.eval env) (ofBytes b)
      = ofBytesV (Vector.map (Expression.eval env) b) := by
  apply Vector.ext
  intro i hi
  simp only [ofBytes, ofBytesV, Vector.getElem_map, Vector.getElem_ofFn]
  rfl

private lemma limb_as_nat (b0 b1 b2 b3 : F circomPrime) :
    b0 + b1 * c8 + b2 * c16 + b3 * c24
      = ((b0.val + 2 ^ 8 * b1.val + 2 ^ 16 * b2.val + 2 ^ 24 * b3.val : ℕ) :
          F circomPrime) := by
  push_cast [c8, c16, c24]
  rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val,
    ZMod.natCast_zmod_val]
  ring

private lemma limb_val (b0 b1 b2 b3 : F circomPrime)
    (h0 : b0.val < 256) (h1 : b1.val < 256) (h2 : b2.val < 256) (h3 : b3.val < 256) :
    (b0 + b1 * c8 + b2 * c16 + b3 * c24).val
      = b0.val + 2 ^ 8 * b1.val + 2 ^ 16 * b2.val + 2 ^ 24 * b3.val := by
  rw [limb_as_nat]
  apply ZMod.val_natCast_of_lt
  have : b0.val + 2 ^ 8 * b1.val + 2 ^ 16 * b2.val + 2 ^ 24 * b3.val < 2 ^ 32 := by
    omega
  exact lt_trans this (by decide)

/-- Nat-indexed form of the byte bound. -/
private lemma byte_lt {b : Vector (F circomPrime) coordBytes}
    (hb : ∀ i : Fin coordBytes, (b[i]).val < 256) (i : ℕ) (hi : i < coordBytes) :
    (b[i]'hi).val < 256 := by
  have := hb ⟨i, hi⟩
  simpa only [Fin.getElem_fin] using this

lemma normalized_ofBytesV {b : Vector (F circomPrime) coordBytes}
    (hb : ∀ i : Fin coordBytes, (b[i]).val < 256) :
    BigInt.Normalized 32 (ofBytesV b) := by
  intro j
  have h0 := byte_lt hb (4 * j.val) (idx0 j)
  have h1 := byte_lt hb (4 * j.val + 1) (idx1 j)
  have h2 := byte_lt hb (4 * j.val + 2) (idx2 j)
  have h3 := byte_lt hb (4 * j.val + 3) (idx3 j)
  simp only [ofBytesV, Fin.getElem_fin, Vector.getElem_ofFn]
  rw [limb_val _ _ _ _ h0 h1 h2 h3]
  omega

/-- `fromLimbs` over the 32 bytes, as an explicit `Fin`-indexed sum. -/
lemma fromLimbs_bytes_sum (b : Vector (F circomPrime) coordBytes) :
    Limbs.fromLimbs 8 (b.toList.map ZMod.val)
      = ∑ i : Fin coordBytes, (b[i.val]'i.isLt).val * 2 ^ (8 * i.val) := by
  have hlen : (List.map ZMod.val b.toList).length = coordBytes := by simp
  rw [fromLimbs_eq_sum]
  rw [← Fin.sum_congr' (fun i : Fin coordBytes => (b[i.val]'i.isLt).val * 2 ^ (8 * i.val)) hlen]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Fin.getElem_fin, Fin.val_cast]
  rw [List.getElem_map, Vector.getElem_toList]
  rfl

set_option maxHeartbeats 2000000 in
lemma value_ofBytesV {b : Vector (F circomPrime) coordBytes}
    (hb : ∀ i : Fin coordBytes, (b[i]).val < 256) :
    BigInt.value 32 (ofBytesV b) = Limbs.fromLimbs 8 (b.toList.map ZMod.val) := by
  rw [Limbs32.value32_eight, fromLimbs_bytes_sum]
  have hval : ∀ j : Fin 8, ((ofBytesV b)[j.val]'(by omega)).val
      = (b[4 * j.val]'(idx0 j)).val + 2 ^ 8 * (b[4 * j.val + 1]'(idx1 j)).val
        + 2 ^ 16 * (b[4 * j.val + 2]'(idx2 j)).val
        + 2 ^ 24 * (b[4 * j.val + 3]'(idx3 j)).val := by
    intro j
    simp only [ofBytesV, Vector.getElem_ofFn]
    exact limb_val _ _ _ _ (byte_lt hb _ (idx0 j)) (byte_lt hb _ (idx1 j))
      (byte_lt hb _ (idx2 j)) (byte_lt hb _ (idx3 j))
  have e0 := hval ⟨0, by decide⟩
  have e1 := hval ⟨1, by decide⟩
  have e2 := hval ⟨2, by decide⟩
  have e3 := hval ⟨3, by decide⟩
  have e4 := hval ⟨4, by decide⟩
  have e5 := hval ⟨5, by decide⟩
  have e6 := hval ⟨6, by decide⟩
  have e7 := hval ⟨7, by decide⟩
  norm_num at e0 e1 e2 e3 e4 e5 e6 e7
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    Fin.isValue]
  norm_num
  omega

/-- From the byte spec: the derived 32-bit limbs are in range. -/
lemma normalized_of_spec {x : Emu (F circomPrime)} {b : Vector (F circomPrime) coordBytes}
    (h : ToBytes.Spec x b) : BigInt.Normalized 32 (ofBytesV b) :=
  normalized_ofBytesV h.1

/-- From the byte spec: the derived 32-bit limbs denote the same field element. -/
lemma decodeFe_of_spec {x : Emu (F circomPrime)} {b : Vector (F circomPrime) coordBytes}
    (h : ToBytes.Spec x b) :
    decodeFe (Limbs32.emuOf32V (ofBytesV b)) = decodeFe x := by
  rw [Limbs32.decodeFe_emuOf32V (normalized_ofBytesV h.1), value_ofBytesV h.1, h.2]
  rfl

lemma normalized_map_ofBytes {env : Environment (F circomPrime)} {x : Emu (F circomPrime)}
    {b : Var (fields coordBytes) (F circomPrime)}
    (h : ToBytes.Spec x (Vector.map (Expression.eval env) b)) :
    BigInt.Normalized 32 (Vector.map (Expression.eval env) (ofBytes b)) := by
  rw [eval_ofBytes]; exact normalized_of_spec h

lemma decodeFe_map_ofBytes {env : Environment (F circomPrime)} {x : Emu (F circomPrime)}
    {b : Var (fields coordBytes) (F circomPrime)}
    (h : ToBytes.Spec x (Vector.map (Expression.eval env) b)) :
    decodeFe (Limbs32.emuOf32V (Vector.map (Expression.eval env) (ofBytes b)))
      = decodeFe x := by
  rw [eval_ofBytes]; exact decodeFe_of_spec h

lemma affineW_ofBytes {b : Var (fields coordBytes) (F circomPrime)}
    (hb : Challenge.CostR1CS.AffineW b) :
    Challenge.CostR1CS.AffineW (ofBytes b) := by
  intro i hi
  have hi8 : i < 8 := hi
  rw [ofBytes, Vector.getElem_ofFn]
  refine Challenge.CostR1CS.Affine.add
    (Challenge.CostR1CS.Affine.add
      (Challenge.CostR1CS.Affine.add (hb _ (idx0 ⟨i, hi8⟩)) ?_) ?_) ?_
  · exact Challenge.CostR1CS.Affine.mul_deg0 (hb _ (idx1 ⟨i, hi8⟩))
      (Challenge.CostR1CS.degree_const _)
  · exact Challenge.CostR1CS.Affine.mul_deg0 (hb _ (idx2 ⟨i, hi8⟩))
      (Challenge.CostR1CS.degree_const _)
  · exact Challenge.CostR1CS.Affine.mul_deg0 (hb _ (idx3 ⟨i, hi8⟩))
      (Challenge.CostR1CS.degree_const _)

lemma ofBytes_map_eval_eq {b : Var (fields coordBytes) (F circomPrime)}
    {e e' : ProverEnvironment (F circomPrime)}
    (h : Vector.map (Expression.eval e.toEnvironment) b
      = Vector.map (Expression.eval e'.toEnvironment) b) :
    Vector.map (Expression.eval e.toEnvironment) (ofBytes b)
      = Vector.map (Expression.eval e'.toEnvironment) (ofBytes b) := by
  rw [eval_ofBytes, eval_ofBytes, h]

end Bytes32
end Solution.Secp256k1ScalarMul
