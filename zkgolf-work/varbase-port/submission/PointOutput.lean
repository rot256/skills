import Solution.Secp256k1ScalarMul.Cost
import Challenge.Utils.ComputableWitnessLemmas



namespace Solution.Secp256k1ScalarMul
namespace PointOutput

open Challenge.CostR1CS


def zeroBytes : Var (fields coordBytes) (F circomPrime) :=
  Vector.ofFn fun _ => ((0 : F circomPrime) : Expression (F circomPrime))

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

instance elaborated :
    ElaboratedCircuit (F circomPrime) FlaggedPoint ScalarMul.Outputs main := by
  elaborate_circuit

def Assumptions (input : FlaggedPoint (F circomPrime)) : Prop :=
  input.Valid ∧ (input.isInf = 1 → input.x = emuOfNat 0 ∧ input.y = emuOfNat 0)

def Spec (input : FlaggedPoint (F circomPrime))
    (out : ScalarMul.Outputs (F circomPrime)) : Prop :=
  out.Valid ∧ ScalarMul.decodeOutput out = decodePoint input

/-- Evaluate a variable `FlaggedPoint` under an environment.  Standalone helper
(formerly `BuildTable.evP` in the retired windowed reference implementation). -/
def evP (env : Environment (F circomPrime)) (fp : Var FlaggedPoint (F circomPrime)) :
    FlaggedPoint (F circomPrime) :=
  { x := Vector.map (Expression.eval env) fp.x,
    y := Vector.map (Expression.eval env) fp.y,
    isInf := Expression.eval env fp.isInf }

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

set_option maxRecDepth 8192 in
/-- The decoded byte output equals the decoded flagged point.  Standalone re-proof
(formerly `VarScalarMul.output_decode`). -/
lemma output_decode (env : Environment (F circomPrime)) (M : ℕ)
    (fin : Var FlaggedPoint (F circomPrime))
    (zb : Var (fields coordBytes) (F circomPrime))
    (hbool : IsBool (Expression.eval env fin.isInf))
    (hxb_val : Limbs.fromLimbs 8
        (List.map ZMod.val (Vector.map (Expression.eval env)
          (varFromOffset (fields coordBytes) M)).toList) =
      BigInt.value limbBits (Vector.map (Expression.eval env) fin.x))
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
    decodePoint (evP env fin) =
      ScalarMul.decodeOutput
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
    ScalarMul.map_eval_ofFn_rev env (M + 256 + 256 + 32)]
  unfold ScalarMul.decodeOutput
  simp only [evP, decodePoint]
  rw [hmx, hmy]
  rcases hbool with hinf0 | hinf1
  · rw [hinf0, if_neg (zero_ne_one (α := F circomPrime)),
      if_neg (zero_ne_one (α := F circomPrime)),
      if_neg (zero_ne_one (α := F circomPrime)),
      if_neg (zero_ne_one (α := F circomPrime))]
    simp only [ScalarMul.coordVal, ScalarMul.fromLimbs_rev_ofFn, hxb_val, hyb_val, decodeFe]
  · rw [hinf1, if_pos rfl, if_pos rfl]

set_option maxRecDepth 8192 in
lemma output_valid_direct (env : Environment (F circomPrime)) (M : ℕ)
    (fin : Var FlaggedPoint (F circomPrime))
    (hvalid : (evP env fin).Valid)
    (hcanonical : Expression.eval env fin.isInf = 1 →
      Vector.map (Expression.eval env) fin.x = emuOfNat 0 ∧
      Vector.map (Expression.eval env) fin.y = emuOfNat 0)
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
      BigInt.value limbBits (Vector.map (Expression.eval env) fin.y)) :
    ScalarMul.Outputs.Valid
      { x := Vector.map (Expression.eval env) (Vector.ofFn fun i =>
          (var { index := M + (31 - i.val) } : Expression (F circomPrime)))
        y := Vector.map (Expression.eval env) (Vector.ofFn fun i =>
          (var { index := M + 256 + (31 - i.val) } : Expression (F circomPrime)))
        isInf := Expression.eval env fin.isInf } := by
  rw [ScalarMul.map_eval_ofFn_rev env M,
    ScalarMul.map_eval_ofFn_rev env (M + 256)]
  simp only [ScalarMul.Outputs.Valid]
  refine ⟨?_, ?_, hvalid.1, ?_, ?_, ?_⟩
  · intro i; rw [Fin.getElem_fin, Vector.getElem_ofFn]
    exact hxb_bytes ⟨31 - i.val, by simp only [coordBytes]; omega⟩
  · intro i; rw [Fin.getElem_fin, Vector.getElem_ofFn]
    exact hyb_bytes ⟨31 - i.val, by simp only [coordBytes]; omega⟩
  · simp only [ScalarMul.coordVal, ScalarMul.fromLimbs_rev_ofFn, hxb_val]
    exact hvalid.2.1.2
  · simp only [ScalarMul.coordVal, ScalarMul.fromLimbs_rev_ofFn, hyb_val]
    exact hvalid.2.2.1.2
  · intro hinf
    have hc := hcanonical hinf
    constructor <;> intro i <;> rw [Fin.getElem_fin, Vector.getElem_ofFn]
    · have hv := hxb_val
      rw [hc.1, CompleteAdd.value_emuOfNat (by positivity)] at hv
      have hz : Limbs.fromLimbs 8
          ((Vector.map (Expression.eval env)
            (varFromOffset (fields coordBytes) M)).toList.map ZMod.val) = 0 := by simpa using hv
      exact ScalarMul.fromLimbs_vector_eq_zero_entry hz
        ⟨31 - i.val, by simp only [coordBytes]; omega⟩
    · have hv := hyb_val
      rw [hc.2, CompleteAdd.value_emuOfNat (by positivity)] at hv
      have hz : Limbs.fromLimbs 8
          ((Vector.map (Expression.eval env)
            (varFromOffset (fields coordBytes) (M + 256))).toList.map ZMod.val) = 0 := by simpa using hv
      exact ScalarMul.fromLimbs_vector_eq_zero_entry hz
        ⟨31 - i.val, by simp only [coordBytes]; omega⟩

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

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem soundness :
    Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨h_tbx, h_tby⟩ := h_holds
  obtain ⟨hvalid, hcanonical⟩ := h_assumptions
  obtain ⟨hx, hy, hi⟩ := h_input
  simp only [ScalarMul.toBytes_localLength, ScalarMul.toBytes_output] at h_tbx h_tby
  unfold ToBytes.circuit ToBytes.Assumptions ToBytes.Spec at h_tbx h_tby
  dsimp only [] at h_tbx h_tby
  obtain ⟨hxb_bytes, hxb_val⟩ := h_tbx hvalid.2.1.1
  obtain ⟨hyb_bytes, hyb_val⟩ := h_tby hvalid.2.2.1.1
  have hevvalid : (evP env
      ({ x := input_var_x, y := input_var_y, isInf := input_var_isInf } :
        Var FlaggedPoint (F circomPrime))).Valid := by
    simpa [evP, hx, hy, hi] using hvalid
  have hevcanon : Expression.eval env input_var_isInf = 1 →
      Vector.map (Expression.eval env) input_var_x = emuOfNat 0 ∧
      Vector.map (Expression.eval env) input_var_y = emuOfNat 0 := by
    intro h; rw [hx, hy]; exact hcanonical (by simpa only [hi] using h)
  simp only [coordBytes, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub]
  refine ⟨⟨?_, ?_⟩, Or.inl ScalarMul.toBytes_channels,
    Or.inl ScalarMul.toBytes_channels⟩
  · rw [← hi]
    exact output_valid_direct env i₀ _ hevvalid hevcanon
      hxb_bytes (by simpa [hx] using hxb_val) hyb_bytes (by simpa [hy] using hyb_val)
  · simp only [main, circuit_norm, ScalarMul.toBytes_localLength,
      ScalarMul.toBytes_output, ScalarMul.decodeOutput, decodePoint]
    rcases hvalid.1 with h0 | h1
    · have h0' : input_isInf = 0 := h0
      rw [h0', if_neg zero_ne_one, if_neg zero_ne_one]
      rw [ScalarMul.map_eval_ofFn_rev env i₀,
        ScalarMul.map_eval_ofFn_rev env (i₀ + 256)]
      rw [show ScalarMul.coordVal
          (Vector.ofFn fun i : Fin coordBytes =>
            (Vector.map (Expression.eval env)
              (varFromOffset (fields coordBytes) i₀))[31 - i.val]'(by have := i.isLt; simp only [coordBytes] at this ⊢; omega)) =
          BigInt.value limbBits input_x from by
            simp only [ScalarMul.coordVal, ScalarMul.fromLimbs_rev_ofFn, hxb_val],
        show ScalarMul.coordVal
          (Vector.ofFn fun i : Fin coordBytes =>
            (Vector.map (Expression.eval env)
              (varFromOffset (fields coordBytes) (i₀ + 256)))[31 - i.val]'(by have := i.isLt; simp only [coordBytes] at this ⊢; omega)) =
          BigInt.value limbBits input_y from by
            simp only [ScalarMul.coordVal, ScalarMul.fromLimbs_rev_ofFn, hyb_val]]
      rfl
    · have h1' : input_isInf = 1 := h1
      rw [h1', if_pos rfl, if_pos rfl]

theorem completeness :
    Completeness (Input := FlaggedPoint) (Output := ScalarMul.Outputs)
      (F circomPrime) main Assumptions := by
  circuit_proof_start
  obtain ⟨⟨hbool, hfx, hfy, -⟩, -⟩ := h_assumptions
  unfold ToBytes.circuit ToBytes.Assumptions
  exact ⟨hfx.1, hfy.1⟩



def circuit : FormalCircuit (F circomPrime) FlaggedPoint ScalarMul.Outputs where
  main
  elaborated
  Assumptions
  Spec
  soundness
  completeness




def pointOutputCost : Count := ⟨512, 520⟩

theorem costIs_main (input : Var FlaggedPoint (F circomPrime)) :
    CostIs (main input) pointOutputCost := by
  rw [show pointOutputCost = Cost.toBytesCost +
      (Cost.toBytesCost + Count.zero) from by decide]
  unfold main
  refine CostIs.bind (Cost.costIs_sub_toBytes _) fun _ => ?_
  refine CostIs.bind (Cost.costIs_sub_toBytes _) fun _ => ?_
  exact CostIs.pure _

theorem costIs_subcircuit (input : Var FlaggedPoint (F circomPrime)) :
    CostIs (subcircuit circuit input) pointOutputCost :=
  CostIs.subcircuit fun n => costIs_main input n

attribute [local irreducible] isR1CSRow r1csProducts operationsIsR1CS flatOperationsIsR1CS

theorem isR1CS_main (input : Var FlaggedPoint (F circomPrime))
    (hinput : Cost.AffineFP input) : IsR1CSCirc (main input) := by
  unfold main
  refine IsR1CSCirc.bind_out (Cost.isR1CS_sub_toBytes _ hinput.1) fun _ => ?_
  refine IsR1CSCirc.bind_out (Cost.isR1CS_sub_toBytes _ hinput.2.1) fun _ => ?_
  exact IsR1CSCirc.pure _

theorem isR1CS_subcircuit (input : Var FlaggedPoint (F circomPrime))
    (hinput : Cost.AffineFP input) : IsR1CSCirc (subcircuit circuit input) :=
  IsR1CSCirc.subcircuit fun n => isR1CS_main input hinput n

private theorem affineProvable_outputs
    {v : Var ScalarMul.Outputs (F circomPrime)}
    (hx : AffineW v.x) (hy : AffineW v.y) (hi : Affine v.isInf) :
    AffineProvable v := by
  intro j hj
  simp only [circuit_norm, explicit_provable_type]
  exact Cost.AffineW.append hx
    (Cost.AffineW.append hy (Cost.affineW_singleton hi)) j hj



theorem computableWitnesses : circuit.base.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition
      input env env') ((main input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  obtain ⟨x, y, isInf⟩ := input
  have htb : ∀ (X : Var Emu (F circomPrime)) (o : ℕ),
      (subcircuit ToBytes.circuit X).localLength o = 256 := fun _ _ => rfl
  unfold main
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.pure_structuralComputableWitnesses_iff,
    htb, and_true]
  constructor
  · refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := FlaggedPoint) ToBytes.circuit _ _ _ ?_ ToBytes.computableWitnesses env env'
    intro k e e' _ _ h_in
    simp only [circuit_norm, FlaggedPoint.mk.injEq] at h_in
    rw [CircuitType.eval_expression_prover_to_verifier (M := Emu),
      CircuitType.eval_expression_prover_to_verifier (M := Emu),
      CircuitType.eval_var_fields, CircuitType.eval_var_fields]
    exact h_in.1
  · refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := FlaggedPoint) ToBytes.circuit _ _ _ ?_ ToBytes.computableWitnesses env env'
    intro k e e' _ _ h_in
    simp only [circuit_norm, FlaggedPoint.mk.injEq] at h_in
    rw [CircuitType.eval_expression_prover_to_verifier (M := Emu),
      CircuitType.eval_expression_prover_to_verifier (M := Emu),
      CircuitType.eval_var_fields, CircuitType.eval_var_fields]
    exact h_in.2.1

theorem computableWitness : ∀ n input,
    ProverEnvironment.OnlyAccessedBelow n
      (fun env : ProverEnvironment (F circomPrime) => eval env input) →
    Circuit.ComputableWitnesses (main input) n :=
  Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnesses_implies
    (circuit := circuit.base) computableWitnesses

theorem localLength (input : Var FlaggedPoint (F circomPrime)) :
    circuit.localLength input = 512 := rfl

lemma eval_output_of_agreesBelow (input : Var FlaggedPoint (F circomPrime))
    {offset k : ℕ} {env env' : ProverEnvironment (F circomPrime)}
    (h_input : eval env input = eval env' input)
    (h_agree : env.AgreesBelow k env') (hk : offset + 512 ≤ k) :
    eval env ((main input).output offset) =
      eval env' ((main input).output offset) := by
  simp only [circuit_norm] at h_input ⊢
  simp only [main, circuit_norm, ScalarMul.toBytes_localLength,
    ScalarMul.toBytes_output]
  rw [ScalarMul.Outputs.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · apply Vector.ext
    intro i hi
    simp only [Vector.getElem_map, Vector.getElem_ofFn,
      ProvableType.varFromOffset_fields, Vector.getElem_mapRange, Expression.eval]
    exact h_agree _ (by simp only [coordBytes] at i hi ⊢; omega)
  · apply Vector.ext
    intro i hi
    simp only [Vector.getElem_map, Vector.getElem_ofFn,
      ProvableType.varFromOffset_fields, Vector.getElem_mapRange, Expression.eval]
    exact h_agree _ (by simp only [coordBytes] at i hi ⊢; omega)
  · rw [FlaggedPoint.mk.injEq] at h_input
    exact h_input.2.2

lemma eval_subOutput_of_agreesBelow (input : Var FlaggedPoint (F circomPrime))
    {offset k : ℕ} {env env' : ProverEnvironment (F circomPrime)}
    (h_input : eval env input = eval env' input)
    (h_agree : env.AgreesBelow k env') (hk : offset + 512 ≤ k) :
    eval env ((subcircuit circuit input).output offset) =
      eval env' ((subcircuit circuit input).output offset) := by
  simpa only [subcircuit, circuit] using
    eval_output_of_agreesBelow input h_input h_agree hk

theorem affineOut_main (input : Var FlaggedPoint (F circomPrime)) (n : ℕ)
    (hi : Affine input.isInf) :
    AffineW ((main input).output n).x ∧
      AffineW ((main input).output n).y ∧
      Affine ((main input).output n).isInf := by
  simp only [circuit_norm, main, ScalarMul.toBytes_localLength,
    ScalarMul.toBytes_output]
  exact ⟨Cost.affineW_ofFn_var _, Cost.affineW_ofFn_var _, hi⟩

theorem affineOutput_main (input : Var FlaggedPoint (F circomPrime))
    (hinput : AffineProvable input) : AffineOutput (main input) := by
  have hfp := Cost.AffineFP.of_affineProvable hinput
  intro n
  obtain ⟨hx, hy, hi⟩ := affineOut_main input n hfp.2.2
  exact affineProvable_outputs hx hy hi


theorem isR1CS : Challenge.CostR1CS.isR1CS main :=
  isR1CS_of_IsR1CSCirc
    (fun input hinput => isR1CS_main input
      (Cost.AffineFP.of_affineProvable hinput))
    affineOutput_main

end PointOutput
end Solution.Secp256k1ScalarMul
