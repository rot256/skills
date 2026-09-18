import Solution.Secp256k1ScalarMul.Cost
import Challenge.Utils.ComputableWitnessLemmas

namespace Solution.Secp256k1ScalarMul
namespace PointOutput

open Challenge.CostR1CS

def main (input : Var FlaggedPoint (F circomPrime)) :
    Circuit (F circomPrime) (Var ScalarMul.Outputs (F circomPrime)) := do
  let xb ← subcircuit ToBytes.circuit input.x
  let yb ← subcircuit ToBytes.circuit input.y
  return {
    x := Vector.ofFn fun i : Fin coordBytes =>
      xb[coordBytes - 1 - i.val]'(by omega)
    y := Vector.ofFn fun i : Fin coordBytes =>
      yb[coordBytes - 1 - i.val]'(by omega)
    isInf := input.isInf
  }

def Assumptions (input : FlaggedPoint (F circomPrime)) : Prop :=
  input.Valid ∧ (input.isInf = 1 → input.x = emuOfNat 0 ∧ input.y = emuOfNat 0)

def Spec (input : FlaggedPoint (F circomPrime))
    (out : ScalarMul.Outputs (F circomPrime)) : Prop :=
  out.Valid ∧ ScalarMul.decodeOutput out = decodePoint input

set_option maxRecDepth 8192 in
/-- The `ToBytes` + `Mux` post-processing of a `FlaggedPoint` produces a valid
`ScalarMul.Outputs`.  Standalone re-proof (formerly `VarScalarMul.output_valid`);
generic to the byte-encode/mask-to-zero-on-infinity pattern, not to the windowed
algorithm. -/
lemma output_valid (env : Environment (F circomPrime)) (M : ℕ)
    (fin : Var FlaggedPoint (F circomPrime))
    (zb : Var (fields coordBytes) (F circomPrime))
    (hzb : zb = Vector.ofFn fun _ => ((0 : F circomPrime) : Expression (F circomPrime)))
    (hbool : IsBool (Expression.eval env fin.isInf))
    (hfx : Fe.Valid (Vector.map (Expression.eval env) fin.x))
    (hfy : Fe.Valid (Vector.map (Expression.eval env) fin.y))
    (hxb_bytes : ∀ i : Fin coordBytes,
      ZMod.val (Vector.map (Expression.eval env)
        (varFromOffset (fields coordBytes) M))[i] < 256)
    (hxb_val : Limbs.fromLimbs 8
        (List.map ZMod.val (Vector.map (Expression.eval env)
          (varFromOffset (fields coordBytes) M)).toList) =
      BigInt.value limbBits (Vector.map (Expression.eval env) fin.x))
    (hyb_bytes : ∀ i : Fin coordBytes,
      ZMod.val (Vector.map (Expression.eval env)
        (varFromOffset (fields coordBytes) (M + 256)))[i] < 256)
    (hyb_val : Limbs.fromLimbs 8
        (List.map ZMod.val (Vector.map (Expression.eval env)
          (varFromOffset (fields coordBytes) (M + 256))).toList) =
      BigInt.value limbBits (Vector.map (Expression.eval env) fin.y))
    (hmx : Vector.map (Expression.eval env)
        (varFromOffset (fields coordBytes) (M + 256 + 256)) =
      if Expression.eval env fin.isInf = 1
      then Vector.map (Expression.eval env) zb
      else Vector.map (Expression.eval env)
        (varFromOffset (fields coordBytes) M))
    (hmy : Vector.map (Expression.eval env)
        (varFromOffset (fields coordBytes) (M + 256 + 256 + 32)) =
      if Expression.eval env fin.isInf = 1
      then Vector.map (Expression.eval env) zb
      else Vector.map (Expression.eval env)
        (varFromOffset (fields coordBytes) (M + 256))) :
    ScalarMul.Outputs.Valid
      { x := Vector.map (Expression.eval env)
          (Vector.ofFn fun i =>
            (var { index := M + 256 + 256 + (31 - i.val) } :
              Expression (F circomPrime))),
        y := Vector.map (Expression.eval env)
          (Vector.ofFn fun i =>
            (var { index := M + 256 + 256 + 32 + (31 - i.val) } :
              Expression (F circomPrime))),
        isInf := Expression.eval env fin.isInf } := by
  rw [ScalarMul.map_eval_ofFn_rev env (M + 256 + 256),
    ScalarMul.map_eval_ofFn_rev env (M + 256 + 256 + 32), hmx, hmy]
  simp only [ScalarMul.Outputs.Valid]
  rcases hbool with hinf0 | hinf1
  · rw [hinf0, if_neg (zero_ne_one (α := F circomPrime)),
      if_neg (zero_ne_one (α := F circomPrime))]
    refine ⟨?_, ?_, Or.inl rfl, ?_, ?_,
      fun h => absurd h (zero_ne_one (α := F circomPrime))⟩
    · intro i
      rw [Fin.getElem_fin, Vector.getElem_ofFn]
      exact hxb_bytes ⟨31 - i.val, by simp only [coordBytes]; omega⟩
    · intro i
      rw [Fin.getElem_fin, Vector.getElem_ofFn]
      exact hyb_bytes ⟨31 - i.val, by simp only [coordBytes]; omega⟩
    · simp only [ScalarMul.coordVal, ScalarMul.fromLimbs_rev_ofFn, hxb_val]
      exact hfx.2
    · simp only [ScalarMul.coordVal, ScalarMul.fromLimbs_rev_ofFn, hyb_val]
      exact hfy.2
  · rw [hinf1, if_pos rfl, if_pos rfl]
    refine ⟨?_, ?_, Or.inr rfl, ?_, ?_, fun _ => ⟨?_, ?_⟩⟩
    · intro i
      rw [Fin.getElem_fin, Vector.getElem_ofFn, ScalarMul.eval_zeroBytes_getElem env zb hzb]
      simp
    · intro i
      rw [Fin.getElem_fin, Vector.getElem_ofFn, ScalarMul.eval_zeroBytes_getElem env zb hzb]
      simp
    · simp only [ScalarMul.coordVal, ScalarMul.fromLimbs_rev_ofFn,
        ScalarMul.fromLimbs_eval_zeroBytes env zb hzb]
      exact DivOrZero.P256_pos
    · simp only [ScalarMul.coordVal, ScalarMul.fromLimbs_rev_ofFn,
        ScalarMul.fromLimbs_eval_zeroBytes env zb hzb]
      exact DivOrZero.P256_pos
    · intro i
      rw [Fin.getElem_fin, Vector.getElem_ofFn, ScalarMul.eval_zeroBytes_getElem env zb hzb]
    · intro i
      rw [Fin.getElem_fin, Vector.getElem_ofFn, ScalarMul.eval_zeroBytes_getElem env zb hzb]

def reverseBytes (bytes : Vector (F circomPrime) coordBytes) :
    Vector (F circomPrime) coordBytes := bytes.reverse

@[simp] lemma reverseBytes_getElem (bytes : Vector (F circomPrime) coordBytes)
    (i : Fin coordBytes) :
    (reverseBytes bytes)[i] =
      bytes[coordBytes - 1 - i.val]'(by omega) := by
  exact Vector.getElem_reverse i.isLt

def fromBytes (input : FlaggedPoint (F circomPrime))
    (xb yb : Vector (F circomPrime) coordBytes) :
    ScalarMul.Outputs (F circomPrime) :=
  {
    x := reverseBytes xb
    y := reverseBytes yb
    isInf := input.isInf
  }

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
lemma spec_of_bytes (input : FlaggedPoint (F circomPrime))
    (xb yb : Vector (F circomPrime) coordBytes)
    (hinput : Assumptions input)
    (hxb : ToBytes.Spec input.x xb) (hyb : ToBytes.Spec input.y yb) :
    Spec input (fromBytes input xb yb) := by
  obtain ⟨hvalid, hcanonical⟩ := hinput
  obtain ⟨hxb_bytes, hxb_val⟩ := hxb
  obtain ⟨hyb_bytes, hyb_val⟩ := hyb
  constructor
  · unfold ScalarMul.Outputs.Valid fromBytes
    refine ⟨?_, ?_, hvalid.1, ?_, ?_, ?_⟩
    · intro i
      rw [reverseBytes_getElem]
      exact hxb_bytes ⟨31 - i.val, by simp only [coordBytes]; omega⟩
    · intro i
      rw [reverseBytes_getElem]
      exact hyb_bytes ⟨31 - i.val, by simp only [coordBytes]; omega⟩
    · simpa only [reverseBytes, ScalarMul.coordVal, Vector.toList_reverse,
        List.map_reverse, List.reverse_reverse, hxb_val] using hvalid.2.1.2
    · simpa only [reverseBytes, ScalarMul.coordVal, Vector.toList_reverse,
        List.map_reverse, List.reverse_reverse, hyb_val] using hvalid.2.2.1.2
    · intro hinf
      have hc := hcanonical hinf
      constructor <;> intro i
      · have hv := hxb_val
        rw [hc.1, CompleteAdd.value_emuOfNat (by positivity)] at hv
        have hz : Limbs.fromLimbs 8 (xb.toList.map ZMod.val) = 0 := by
          simpa using hv
        rw [reverseBytes_getElem]
        exact ScalarMul.fromLimbs_vector_eq_zero_entry hz
          ⟨31 - i.val, by simp only [coordBytes]; omega⟩
      · have hv := hyb_val
        rw [hc.2, CompleteAdd.value_emuOfNat (by positivity)] at hv
        have hz : Limbs.fromLimbs 8 (yb.toList.map ZMod.val) = 0 := by
          simpa using hv
        rw [reverseBytes_getElem]
        exact ScalarMul.fromLimbs_vector_eq_zero_entry hz
          ⟨31 - i.val, by simp only [coordBytes]; omega⟩
  · unfold ScalarMul.decodeOutput decodePoint fromBytes
    by_cases hinf : input.isInf = 1
    · rw [if_pos hinf, if_pos hinf]
    · rw [if_neg hinf, if_neg hinf]
      simp only [ScalarMul.coordVal, reverseBytes, Vector.toList_reverse,
        List.map_reverse, List.reverse_reverse, hxb_val, hyb_val, decodeFe]

attribute [local irreducible] isR1CSRow r1csProducts operationsIsR1CS flatOperationsIsR1CS

end PointOutput
end Solution.Secp256k1ScalarMul
