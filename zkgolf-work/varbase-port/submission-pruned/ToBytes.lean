import Solution.Secp256k1ScalarMul.Params
import Solution.Secp256k1ScalarMul.ToBytesTheorems
import Challenge.Utils.ComputableWitnessLemmas

namespace Solution.Secp256k1ScalarMul
namespace ToBytes

def byteOfNat (v i : ℕ) : ℕ := v / 2 ^ (8 * i) % 256

def main (x : Var Emu (F circomPrime)) :
    Circuit (F circomPrime) (Var (fields coordBytes) (F circomPrime)) := do
  -- witness the 32 little-endian bytes of the value
  let bytes ← ProvableType.witness (α := fields coordBytes) fun env =>
    Vector.ofFn fun i : Fin coordBytes =>
      ((byteOfNat (evalEmu env x) i.val : ℕ) : F circomPrime)

  -- each byte is 8 bits
  Circuit.forEach bytes (fun b => RangeCheck.circuit 8 (by decide) (by decide) b)

  -- per-limb affine recomposition: limb_k = Σ_{t<8} byte_{8k+t} · 2^(8t)
  let constraints := Vector.ofFn fun k : Fin numLimbs =>
    (Fin.foldl bytesPerLimb (fun acc t =>
      acc + bytes[bytesPerLimb * k.val + t.val]'(by
          have hk := k.isLt; have ht := t.isLt
          simp only [numLimbs, bytesPerLimb, coordBytes] at hk ht ⊢
          omega)
        * (((2 ^ (8 * t.val) : ℕ) : F circomPrime) : Expression (F circomPrime)))
      0)
    - x[k.val]'k.isLt
  Circuit.forEach constraints assertZero

  return bytes

instance elaborated : ElaboratedCircuit (F circomPrime) Emu (fields coordBytes) main := by
  elaborate_circuit

def Assumptions (x : Emu (F circomPrime)) : Prop :=
  x.Normalized limbBits

def Spec (x : Emu (F circomPrime)) (out : fields coordBytes (F circomPrime)) : Prop :=
  (∀ i : Fin coordBytes, (out[i]).val < 256) ∧
    Limbs.fromLimbs 8 (out.toList.map ZMod.val) = x.value limbBits

theorem soundness :
    Soundness (Input := Emu) (Output := fields coordBytes) (F circomPrime)
      main Assumptions Spec := by
  circuit_proof_start [RangeCheck.circuit, RangeCheck.elaborated,
    RangeCheck.Assumptions, RangeCheck.Spec]
  obtain ⟨h_bytes, h_rows⟩ := h_holds
  refine ⟨fun i => lt_of_lt_of_eq (h_bytes i) (by norm_num), ?_⟩
  apply soundness_core env i₀ input h_bytes
  intro k
  have h := h_rows k
  simp only [Vector.getElem_ofFn] at h
  rw [eval_row_iff] at h
  rw [← h_input, Vector.getElem_map]
  exact h

theorem completeness :
    Completeness (Input := Emu) (Output := fields coordBytes) (F circomPrime)
      main Assumptions := by
  circuit_proof_start [RangeCheck.circuit, RangeCheck.elaborated,
    RangeCheck.Assumptions, RangeCheck.Spec]
  obtain ⟨h_wit, -⟩ := h_env
  -- the witnessed value is the input's value
  have hv : evalEmu env input_var = BigInt.value limbBits input := by
    rw [evalEmu, h_input]
    rfl
  -- each witnessed byte is the corresponding byte of the input's value
  have hbyte : ∀ i : Fin coordBytes,
      env.get (i₀ + i.val)
        = ((byteOfNat (BigInt.value limbBits input) i.val : ℕ) : F circomPrime) := by
    intro i
    rw [h_wit i]
    simp only [Vector.getElem_ofFn, hv]
  -- a byte value is < 2^8
  have hbyte_lt : ∀ v j : ℕ, byteOfNat v j < 2 ^ 8 :=
    fun v j => Nat.mod_lt _ (by norm_num)
  refine ⟨fun i => ?_, fun k => ?_⟩
  · -- range checks: the witnessed bytes are 8-bit
    rw [hbyte i, ZMod.val_natCast_of_lt (lt_trans (hbyte_lt _ _)
      (lt_trans (by norm_num) two_pow_64_lt_circomPrime))]
    exact hbyte_lt _ _
  · -- recomposition rows
    simp only [Vector.getElem_ofFn]
    rw [eval_row_iff]
    have hx : Expression.eval env.toEnvironment (input_var[k.val]'k.isLt)
        = input[k.val]'k.isLt := by
      rw [← h_input, Vector.getElem_map]
    rw [hx]
    show (∑ t : Fin bytesPerLimb,
        env.get (i₀ + (bytesPerLimb * k.val + t.val))
          * ((2 ^ (8 * t.val) : ℕ) : F circomPrime))
      = input[k.val]'k.isLt
    apply completeness_core input h_assumptions k
    intro t
    have hidx : bytesPerLimb * k.val + t.val < coordBytes := by
      have hk := k.isLt
      have ht := t.isLt
      simp only [numLimbs, bytesPerLimb, coordBytes] at hk ht ⊢
      omega
    rw [hbyte ⟨bytesPerLimb * k.val + t.val, hidx⟩]
    simp only [byteOfNat]

def circuit : FormalCircuit (F circomPrime) Emu (fields coordBytes) where
  main; elaborated; Assumptions; Spec; soundness; completeness

end ToBytes
end Solution.Secp256k1ScalarMul
