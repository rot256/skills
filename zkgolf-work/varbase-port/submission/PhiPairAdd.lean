import Solution.Secp256k1ScalarMul.CompleteAdd
import Solution.Secp256k1ScalarMul.MulModTargetD3
import Solution.Secp256k1ScalarMul.MulModFold32NInv
import Solution.Secp256k1ScalarMul.ParamsD3
import Challenge.Utils.ComputableWitnessLemmas

namespace Solution.Secp256k1ScalarMul

namespace DivUncheckedD3

/-!
`DivUncheckedD3` witnesses the quotient `λ = num / den (mod p)` for triply
unreduced operands and certifies `λ·den ≡ num (mod p)` with the folded
certificate.  The quotient is witnessed **in the eight-limb base-`2^32` view**:
eight 32-bit range checks cost `8·31 = 248` allocations / `256` rows, exactly
what the four witnesses plus the four 64-bit range checks of the base-`2^64`
view cost (`4 + 252` / `256`), so the certificate length is unchanged at
`432/434`.  Exposing the 32-bit limbs lets the consumer run its squaring
certificate in base `2^32` (`MulModSub2F32`, 357/363) instead of base `2^64`
(`MulModSub2`, 440/443).

Canonicality of `λ` is still not needed: every consumer uses `λ` only as a
multiplication operand, where the limb bound is what matters.  The 64-bit
recombination `Limbs32.emuOf32 λ32` is affine, hence free.
-/

structure Inputs (F : Type) where
  num : Emu F
  den : Emu F
deriving ProvableStruct

/-- The eight-limb, base-`2^32` view of the quotient. -/
@[reducible] def Emu32 : TypeMap := BigInt 8

def main (input : Var Inputs (F circomPrime)) :
    Circuit (F circomPrime) (Var Emu32 (F circomPrime)) := do
  let { num, den } := input

  let lam32 ← ProvableType.witness (α := Emu32) fun env =>
    let denFp : Specs.Secp256k1.Fp := ((evalEmu env den : ℕ) : Specs.Secp256k1.Fp)
    let numFp : Specs.Secp256k1.Fp := ((evalEmu env num : ℕ) : Specs.Secp256k1.Fp)
    Limbs32.emu32OfNat (numFp * denFp⁻¹).val

  -- each 32-bit limb is range checked: 8·(31/32) = 248/256, exactly what the
  -- four-limb `Normalize` costs together with its four witnesses.
  Normalize.circuit secpParams32 lam32

  MulModFold32N.circuitInv (2 ^ 32) (3 * 2 ^ 64) (by decide)
    { a := lam32, b := MulModFold32N.expand32 den, target := num }

  return lam32

instance elaborated : ElaboratedCircuit (F circomPrime) Inputs Emu32 main := by
  elaborate_circuit

def Assumptions (input : Inputs (F circomPrime)) : Prop :=
  (∀ i : Fin numLimbs, (input.num[i.val]).val < 3 * 2 ^ limbBits) ∧
    BigInt.value limbBits input.num < 3 * P256 ∧
    (∀ i : Fin numLimbs, (input.den[i.val]).val < 3 * 2 ^ limbBits) ∧
    BigInt.value limbBits input.den < 3 * P256 ∧
    (decodeFe input.den = 0 → decodeFe input.num = 0)

def Spec (input : Inputs (F circomPrime)) (out : Emu32 (F circomPrime)) : Prop :=
  BigInt.Normalized 32 out ∧
    decodeFe (Limbs32.emuOf32V out) * decodeFe input.den = decodeFe input.num

theorem soundness : Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [Normalize.circuit, Normalize.main, Normalize.Assumptions, Normalize.Spec,
    MulModFold32N.circuitInv, MulModFold32N.Assumptions, MulModFold32N.Spec]
  obtain ⟨hnum_limbs, hnum_value, hden_limbs, hden_value, -⟩ := h_assumptions
  obtain ⟨h_input_num, h_input_den⟩ := h_input
  obtain ⟨hlam_valid, hcert⟩ := h_holds
  set lam32Var := Vector.mapRange 8 fun i => var (F := F circomPrime) { index := i₀ + i }
    with hlam32Var
  have hexp_limb' : ∀ i : Fin 8,
      ((Vector.map (Expression.eval env)
          (MulModFold32N.expand32 input_var_den))[i.val]).val < 3 * 2 ^ 64 := by
    rw [MulModFold32N.eval_expand32]
    refine MulModFold32N.expand32V_lt (by positivity) ?_
    intro i
    have h := hden_limbs i
    rw [← h_input_den] at h
    simpa [limbBits] using h
  have hexp_limb : ∀ i : Fin 8,
      (Expression.eval env ((MulModFold32N.expand32 input_var_den)[i.val])).val < 3 * 2 ^ 64 :=
    fun i => by simpa [Vector.getElem_map] using hexp_limb' i
  have hspec := hcert ⟨fun i => by
      simpa [hlam32Var, secpParams32, circuit_norm] using hlam_valid i,
    hexp_limb, MulModFold32N.eval_expand32_odd_zero env input_var_den,
    fun i => by simpa [limbBits] using hnum_limbs i,
    by simpa [limbBits] using hnum_value⟩
  have hden_val32 : BigInt.value 32 (Vector.map (Expression.eval env)
        (MulModFold32N.expand32 input_var_den))
      = BigInt.value limbBits (Vector.map (Expression.eval env) input_var_den) := by
    rw [MulModFold32N.eval_expand32, MulModFold32N.value_expand32]
  have hlamval : BigInt.value 32 (Vector.map (Expression.eval env) lam32Var)
      = BigInt.value limbBits
        (Limbs32.emuOf32V (Vector.map (Expression.eval env) lam32Var)) :=
    (Limbs32.value_emuOf32 hlam_valid).symm
  rw [hden_val32, hlamval, h_input_den] at hspec
  refine ⟨hlam_valid, ?_⟩
  simp only [decodeFe]
  exact DivOrZero.mul_cast_of_mod_eq3 hspec

theorem completeness : Completeness (F circomPrime) main Assumptions := by
  circuit_proof_start [Normalize.circuit, Normalize.main, Normalize.Assumptions, Normalize.Spec,
    MulModFold32N.circuitInv, MulModFold32N.Assumptions, MulModFold32N.Spec]
  obtain ⟨hnum_limbs, hnum_value, hden_limbs, hden_value, hzero⟩ := h_assumptions
  obtain ⟨h_input_num, h_input_den⟩ := h_input
  have hlam := h_env
  have hev_num : evalEmu env input_var_num = BigInt.value limbBits input_num := by
    rw [evalEmu, BigInt.value, ← h_input_num]
  have hev_den : evalEmu env input_var_den = BigInt.value limbBits input_den := by
    rw [evalEmu, BigInt.value, ← h_input_den]
  let numFp : Specs.Secp256k1.Fp := ((BigInt.value limbBits input_num : ℕ) : Specs.Secp256k1.Fp)
  let denFp : Specs.Secp256k1.Fp := ((BigInt.value limbBits input_den : ℕ) : Specs.Secp256k1.Fp)
  set lam32Var := Vector.mapRange 8 fun i => var (F := F circomPrime) { index := i₀ + i }
    with hlam32Var
  have hlam_eval : Vector.map (Expression.eval env.toEnvironment) lam32Var
      = Limbs32.emu32OfNat (numFp * denFp⁻¹).val := by
    dsimp only [numFp, denFp]
    rw [← hev_num, ← hev_den]
    apply Vector.ext
    intro k hk
    have hentry : (Vector.map (Expression.eval env.toEnvironment) lam32Var)[k]'hk
        = env.get (i₀ + k) := by
      simp [hlam32Var, circuit_norm]
    rw [hentry]
    exact hlam ⟨k, hk⟩
  have hlam_norm : BigInt.Normalized 32
      (Vector.map (Expression.eval env.toEnvironment) lam32Var) := by
    rw [hlam_eval]
    exact Limbs32.emu32OfNat_normalized _
  have hlam_lt : (numFp * denFp⁻¹).val < P256 := ZMod.val_lt _
  have hlam_val32 : BigInt.value 32
      (Vector.map (Expression.eval env.toEnvironment) lam32Var)
      = (numFp * denFp⁻¹).val := by
    rw [hlam_eval,
      show BigInt.value 32 (Limbs32.emu32OfNat (numFp * denFp⁻¹).val)
        = BigInt.value limbBits (Limbs32.emuOf32V (Limbs32.emu32OfNat (numFp * denFp⁻¹).val)) from
      (Limbs32.value_emuOf32 (Limbs32.emu32OfNat_normalized _)).symm,
      Limbs32.emuOf32V_emu32OfNat]
    exact value_emuOfNat (lt_trans hlam_lt P256_lt)
  have hexp_limb' : ∀ i : Fin 8,
      ((Vector.map (Expression.eval env.toEnvironment)
          (MulModFold32N.expand32 input_var_den))[i.val]).val < 3 * 2 ^ 64 := by
    rw [MulModFold32N.eval_expand32]
    refine MulModFold32N.expand32V_lt (by positivity) ?_
    intro i
    have h := hden_limbs i
    rw [← h_input_den] at h
    simpa [limbBits] using h
  have hexp_limb : ∀ i : Fin 8,
      (Expression.eval env.toEnvironment
        ((MulModFold32N.expand32 input_var_den)[i.val])).val < 3 * 2 ^ 64 :=
    fun i => by simpa [Vector.getElem_map] using hexp_limb' i
  have hden_val32 : BigInt.value 32 (Vector.map (Expression.eval env.toEnvironment)
        (MulModFold32N.expand32 input_var_den))
      = BigInt.value limbBits (Vector.map (Expression.eval env.toEnvironment) input_var_den) := by
    rw [MulModFold32N.eval_expand32, MulModFold32N.value_expand32]
  refine ⟨hlam_norm, ⟨fun i => by
      simpa [hlam32Var, secpParams32, circuit_norm] using hlam_norm i,
    hexp_limb, MulModFold32N.eval_expand32_odd_zero env.toEnvironment input_var_den,
    fun i => by simpa [limbBits] using hnum_limbs i,
    by simpa [limbBits] using hnum_value⟩, ?_⟩
  · rw [hden_val32, hlam_val32, h_input_den]
    by_cases hden0 : denFp = 0
    · have hnum0 : numFp = 0 := by
        apply hzero
        simpa [decodeFe, numFp, denFp] using hden0
      rw [hden0, hnum0]
      have hmod0 : BigInt.value limbBits input_num % P256 = 0 :=
        Nat.mod_eq_zero_of_dvd
        ((ZMod.natCast_eq_zero_iff (BigInt.value limbBits input_num) P256).mp
          (by simpa [numFp] using hnum0))
      simpa using hmod0
    · change BigInt.value limbBits input_num % P256 =
        (numFp * denFp⁻¹).val * BigInt.value limbBits input_den % P256
      exact DivOrZero.witness_cert_nonzero3 hden0

def circuit : FormalCircuit (F circomPrime) Inputs Emu32 where
  main
  elaborated
  Assumptions
  Spec
  soundness
  completeness

lemma localLength (input : Var Inputs (F circomPrime)) :
    circuit.localLength input = 412 := rfl

/-- Stability of an eight-limb witness block under agreeing environments. -/
private theorem emu32WitnessOutput_stable
    (compute : ProverEnvironment (F circomPrime) → Emu32 (F circomPrime))
    {offset k : ℕ} {env env' : ProverEnvironment (F circomPrime)}
    (h_agree : env.AgreesBelow k env') (hk : offset + 8 ≤ k) :
    eval env ((ProvableType.witness (α := Emu32) compute).output offset) =
      eval env' ((ProvableType.witness (α := Emu32) compute).output offset) := by
  apply Vector.ext
  intro i hi
  rw [← ProvableType.getElem_eval_fields_prover (env := env)
      ((ProvableType.witness (α := Emu32) compute).output offset) i hi,
    ← ProvableType.getElem_eval_fields_prover (env := env')
      ((ProvableType.witness (α := Emu32) compute).output offset) i hi]
  simp only [Circuit.output, ProvableType.witness, ProvableType.varFromOffset_fields,
    Vector.getElem_mapRange, Expression.eval]
  have hi8 : i < 8 := hi
  exact h_agree (offset + i) (by omega)

attribute [local irreducible] Normalize.circuit MulModFold32N.circuitInv

theorem computableWitnesses : circuit.base.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition
      input env env') ((main input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  obtain ⟨num, den⟩ := input
  unfold main
  let lamc : Circuit (F circomPrime) (Var Emu32 (F circomPrime)) :=
    ProvableType.witness (α := Emu32) fun env =>
      let denFp : Specs.Secp256k1.Fp := ((evalEmu env den : ℕ) : Specs.Secp256k1.Fp)
      let numFp : Specs.Secp256k1.Fp := ((evalEmu env num : ℕ) : Specs.Secp256k1.Fp)
      Limbs32.emu32OfNat (numFp * denFp⁻¹).val
  let lam32 := lamc.output offset
  let validOff := offset + lamc.localLength offset
  let validc : Circuit (F circomPrime) Unit := Normalize.circuit secpParams32 lam32
  let mmOff := validOff + validc.localLength validOff
  have h_lamlen : lamc.localLength offset = 8 := by
    simp [lamc, ProvableType.witness, Circuit.localLength, Operations.localLength, size]
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.provableWitness_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.pure_structuralComputableWitnesses_iff,
    and_true]
  and_intros
  · intro _ h_input
    have hnum : evalEmu env num = evalEmu env' num :=
      evalEmu_eq_of_eval_eq (by
        simpa [circuit_norm] using
          congrArg (fun x : Inputs (F circomPrime) => x.num) h_input)
    have hden : evalEmu env den = evalEmu env' den :=
      evalEmu_eq_of_eval_eq (by
        simpa [circuit_norm] using
          congrArg (fun x : Inputs (F circomPrime) => x.den) h_input)
    simp only [hnum, hden]
  · exact
      Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
        (Parent := Inputs) (Normalize.circuit secpParams32) _ lam32 validOff
        (by
          intro k env env' hle h_agree _
          have hk : offset + 8 ≤ k := by
            dsimp only [validOff] at hle
            rw [h_lamlen] at hle
            omega
          exact emu32WitnessOutput_stable _ h_agree hk)
        (Normalize.computableWitnesses secpParams32) env env'
  · exact
      Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
        (Parent := Inputs)
        (MulModFold32N.circuitInv (2 ^ 32) (3 * 2 ^ 64) (by decide)) _
        { a := lam32, b := MulModFold32N.expand32 den, target := num }
        mmOff
        (by
          intro k env env' hle h_agree h_input
          have hk : offset + 8 ≤ k := by
            have hbase : offset + 8 ≤ mmOff := by
              dsimp only [mmOff, validOff]
              rw [h_lamlen]
              omega
            omega
          have hlam := emu32WitnessOutput_stable
            (fun env =>
              let denFp : Specs.Secp256k1.Fp :=
                ((evalEmu env den : ℕ) : Specs.Secp256k1.Fp)
              let numFp : Specs.Secp256k1.Fp :=
                ((evalEmu env num : ℕ) : Specs.Secp256k1.Fp)
              Limbs32.emu32OfNat (numFp * denFp⁻¹).val)
            h_agree hk
          have hnum : Vector.map (Expression.eval env.toEnvironment) num =
              Vector.map (Expression.eval env'.toEnvironment) num := by
            simpa [circuit_norm] using
              congrArg (fun x : Inputs (F circomPrime) => x.num) h_input
          have hden : Vector.map (Expression.eval env.toEnvironment) den =
              Vector.map (Expression.eval env'.toEnvironment) den := by
            simpa [circuit_norm] using
              congrArg (fun x : Inputs (F circomPrime) => x.den) h_input
          simp only [circuit_norm]
          rw [MulModFold32N.Inputs.mk.injEq]
          refine ⟨MulMod.bigInt_map_eval_eq_of_eval_eq hlam, ?_, hnum⟩
          rw [MulModFold32N.eval_expand32, MulModFold32N.eval_expand32]
          exact congrArg MulModFold32N.expand32V hden)
        (MulModFold32N.computableWitnessesInv (2 ^ 32) (3 * 2 ^ 64) (by decide))
        env env'

theorem computableWitness : ∀ n input,
    ProverEnvironment.OnlyAccessedBelow n
      (fun env : ProverEnvironment (F circomPrime) => eval env input) →
    Circuit.ComputableWitnesses (main input) n :=
  Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnesses_implies
    (circuit := circuit.base) computableWitnesses

lemma eval_output_of_agreesBelow (input : Var Inputs (F circomPrime)) {offset k : ℕ}
    {env env' : ProverEnvironment (F circomPrime)}
    (h_agree : env.AgreesBelow k env') (hk : offset + 8 ≤ k) :
    eval env ((main input).output offset) = eval env' ((main input).output offset) := by
  obtain ⟨num, den⟩ := input
  have hout : (main ⟨num, den⟩).output offset
      = (ProvableType.witness (α := Emu32) fun env =>
          let denFp : Specs.Secp256k1.Fp :=
            ((evalEmu env den : ℕ) : Specs.Secp256k1.Fp)
          let numFp : Specs.Secp256k1.Fp :=
            ((evalEmu env num : ℕ) : Specs.Secp256k1.Fp)
          Limbs32.emu32OfNat (numFp * denFp⁻¹).val).output offset := rfl
  rw [hout]
  exact emu32WitnessOutput_stable _ h_agree hk

end DivUncheckedD3

namespace PhiPairAdd

private abbrev divUncheckedLen : ℕ := 8 + (8 * (secpParams32.B - 1) + 156)

private abbrev mulSub2Len : ℕ := numLimbs + (260 + 92)

structure Inputs (F : Type) where
  P : FlaggedPoint F
  Q : FlaggedPoint F
deriving ProvableStruct

def main (input : Var Inputs (F circomPrime)) :
    Circuit (F circomPrime) (Var FlaggedPoint (F circomPrime)) := do
  let { P, Q } := input

  let dyU : Var Emu (F circomPrime) := Vector.ofFn fun k : Fin numLimbs =>
    Q.y[k.val]'k.isLt
      + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
        - P.y[k.val]'k.isLt)
  let dxU : Var Emu (F circomPrime) := Vector.ofFn fun k : Fin numLimbs =>
    Q.x[k.val]'k.isLt
      + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
        - P.x[k.val]'k.isLt)

  let lam32 ← subcircuit DivUncheckedD3.circuit { num := dyU, den := dxU }

  let x3 ← subcircuit MulModSub2F32.circuit { a := lam32, b := lam32, s1 := P.x, s2 := Q.x }
  let xdU : Var Emu (F circomPrime) := Vector.ofFn fun k : Fin numLimbs =>
    P.x[k.val]'k.isLt
      + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
        - x3[k.val]'k.isLt)
  let y3 ← subcircuit MulModSub2W32N.circuit { a := lam32, b := xdU, s1 := P.y, s2 := zeroConst }

  return { x := x3, y := y3, isInf := P.isInf }

instance elaborated : ElaboratedCircuit (F circomPrime) Inputs FlaggedPoint main := by
  elaborate_circuit

def FiniteAssumptions (input : Inputs (F circomPrime)) : Prop :=
  input.P.Valid ∧ input.Q.Valid ∧ input.P.isInf = 0 ∧ input.Q.isInf = 0 ∧
    decodeFe input.Q.x ≠ decodeFe input.P.x

def InfinityAssumptions (input : Inputs (F circomPrime)) : Prop :=
  input.P.Valid ∧ input.Q.Valid ∧ input.P.isInf = 1 ∧ input.Q.isInf = 1 ∧
    decodeFe input.Q.y = decodeFe input.P.y

def Assumptions (input : Inputs (F circomPrime)) : Prop :=
  input.P.Valid ∧ input.Q.Valid ∧
    ((input.P.isInf = 0 ∧ input.Q.isInf = 0 ∧
        decodeFe input.Q.x ≠ decodeFe input.P.x) ∨
      (input.P.isInf = 1 ∧ input.Q.isInf = 1 ∧
        decodeFe input.Q.y = decodeFe input.P.y))

def Spec (input : Inputs (F circomPrime)) (out : FlaggedPoint (F circomPrime)) : Prop :=
  out.Valid ∧
    decodePoint out =
      Specs.ShortWeierstrass.add Specs.Secp256k1.curve
        (decodePoint input.P) (decodePoint input.Q)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
private theorem soundness_finite : Soundness (F circomPrime) main FiniteAssumptions Spec := by
  circuit_proof_start [
    FiniteAssumptions,
    MulModSub2F32.circuit, MulModSub2F32.Assumptions, MulModSub2F32.Spec,
    MulModSub2W32N.circuit, MulModSub2W32N.Assumptions, MulModSub2W32N.Spec,
    DivUncheckedD3.circuit, DivUncheckedD3.Assumptions, DivUncheckedD3.Spec]
  obtain ⟨hlam, hx3, hy3⟩ := h_holds
  obtain ⟨hP, hQ, hP0, hQ0, hxne⟩ := h_assumptions
  have hPx : Fe.Valid input_P_x := hP.2.1
  have hPy : Fe.Valid input_P_y := hP.2.2.1
  have hQx : Fe.Valid input_Q_x := hQ.2.1
  have hQy : Fe.Valid input_Q_y := hQ.2.2.1
  obtain ⟨⟨hIPx, hIPy, hIPi⟩, hIQx, hIQy, hIQi⟩ := h_input
  have hdxe : decodeFe (Vector.map (Expression.eval env)
        (Vector.ofFn fun k : Fin numLimbs => input_var_Q_x[k.val]'k.isLt
          + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
            - input_var_P_x[k.val]'k.isLt)))
      = decodeFe input_Q_x - decodeFe input_P_x := by
    rw [CompleteAdd.map_eval_borrow, hIQx, hIPx]
    exact CompleteAdd.decodeFe_borrow input_Q_x input_P_x hQx.1 hPx
  have hdye : decodeFe (Vector.map (Expression.eval env)
        (Vector.ofFn fun k : Fin numLimbs => input_var_Q_y[k.val]'k.isLt
          + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
            - input_var_P_y[k.val]'k.isLt)))
      = decodeFe input_Q_y - decodeFe input_P_y := by
    rw [CompleteAdd.map_eval_borrow, hIQy, hIPy]
    exact CompleteAdd.decodeFe_borrow input_Q_y input_P_y hQy.1 hPy
  obtain ⟨hlamv, hlam_eq⟩ := hlam (by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro i
      have hcell := congrArg (fun v : Emu (F circomPrime) => v[i.val]'i.isLt)
        (CompleteAdd.map_eval_borrow env input_var_Q_y input_var_P_y)
      rw [hIQy, hIPy] at hcell
      simp only [Vector.getElem_map, Vector.getElem_ofFn] at hcell ⊢
      rw [hcell]
      exact CompleteAdd.limb_borrow_lt i.val (hQy.1 i) (hPy.1 i)
    · rw [CompleteAdd.map_eval_borrow, hIQy, hIPy]
      exact CompleteAdd.value_borrow_lt input_Q_y input_P_y hQy hPy
    · intro i
      have hcell := congrArg (fun v : Emu (F circomPrime) => v[i.val]'i.isLt)
        (CompleteAdd.map_eval_borrow env input_var_Q_x input_var_P_x)
      rw [hIQx, hIPx] at hcell
      simp only [Vector.getElem_map, Vector.getElem_ofFn] at hcell ⊢
      rw [hcell]
      exact CompleteAdd.limb_borrow_lt i.val (hQx.1 i) (hPx.1 i)
    · rw [CompleteAdd.map_eval_borrow, hIQx, hIPx]
      exact CompleteAdd.value_borrow_lt input_Q_x input_P_x hQx hPx
    · intro hden0
      exfalso
      rw [hdxe, sub_eq_zero] at hden0
      contradiction)
  obtain ⟨hx3v, hx3full⟩ := hx3 ⟨hlamv, hlamv, hPx, hQx⟩
  obtain ⟨lamSqg, hlamSqd, hx3e3⟩ := CompleteAdd.split_mulsub hx3full
  obtain ⟨xsg, hxse, hx3e⟩ := CompleteAdd.split3_sub hx3e3
  have hz0 : decodeFe (Vector.map (Expression.eval env) zeroConst) = 0 := by
    rw [DivOrZero.eval_zeroConst, decodeFe, value_emuOfNat (by positivity), Nat.cast_zero]
  obtain ⟨hy3v, hy3full⟩ := hy3 (by
    refine ⟨hlamv, ?_, hPy, CompleteAdd.fe_valid_eval_zeroConst env⟩
    · intro i
      have hpq := congrArg (fun v : Emu (F circomPrime) => v[i.val]'i.isLt) hIPx
      simp only [Vector.getElem_map] at hpq
      have hx3l := hx3v.1 i
      rw [Fin.getElem_fin, Vector.getElem_map, Vector.getElem_mapRange] at hx3l
      simp only [circuit_norm] at hx3l
      simp only [circuit_norm, Vector.getElem_ofFn, hpq]
      rw [← sub_eq_add_neg]
      exact CompleteAdd.limb_borrow_lt i.val (hPx.1 i) hx3l)
  rw [CompleteAdd.map_eval_borrow_vfo env input_var_P_x (i₀ + divUncheckedLen), hIPx] at hy3full
  have hxde := CompleteAdd.decodeFe_borrow input_P_x _ hPx.1 hx3v
  rw [hz0, sub_zero] at hy3full
  obtain ⟨yprodg, hyprodd, hy3e⟩ := CompleteAdd.split_mulsub1 hy3full
  let lamv : Emu (F circomPrime) :=
    Vector.map (Expression.eval env) (Vector.mapRange numLimbs fun i => var { index := i₀ + i })
  let xv : Emu (F circomPrime) :=
    Vector.map (Expression.eval env) (Vector.mapRange numLimbs fun i =>
      var { index := i₀ + divUncheckedLen + i })
  let yv : Emu (F circomPrime) :=
    Vector.map (Expression.eval env) (Vector.mapRange numLimbs fun i =>
      var { index := i₀ + divUncheckedLen + mulSub2Len + i })
  have hsameX : (0 : F circomPrime) =
      if decodeFe (Vector.map (Expression.eval env)
        (Vector.ofFn fun k : Fin numLimbs => input_var_Q_x[k.val]'k.isLt
          + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
            - input_var_P_x[k.val]'k.isLt))) = 0 then 1 else 0 := by
    rw [if_neg (by
      rw [hdxe]
      exact sub_ne_zero.mpr hxne)]
  let syv : Emu (F circomPrime) :=
    emuOfNat ((decodeFe input_P_y + decodeFe input_Q_y).val)
  have hsye : decodeFe syv = decodeFe input_P_y + decodeFe input_Q_y :=
    CompleteAdd.decodeFe_emuOfNat_val _
  let oppv : F circomPrime := if decodeFe syv = 0 then 1 else 0
  have hoppY : oppv =
      if decodeFe syv = 0 then 1 else 0 := by
    rfl
  have hs2 : (⟨xv, yv, 0⟩ : FlaggedPoint (F circomPrime)) =
      if input_Q_isInf = 1 then
        ({ x := input_P_x, y := input_P_y, isInf := input_P_isInf } :
          FlaggedPoint (F circomPrime))
      else ⟨xv, yv, 0⟩ := by
    rw [hQ0]
    rfl
  have hout : (⟨xv, yv, input_P_isInf⟩ :
        FlaggedPoint (F circomPrime)) =
      if input_P_isInf = 1 then
        ({ x := input_Q_x, y := input_Q_y, isInf := input_Q_isInf } :
          FlaggedPoint (F circomPrime))
      else ⟨xv, yv, 0⟩ := by
    rw [hP0]
    rfl
  let infpt : FlaggedPoint (F circomPrime) := ⟨xv, yv, 1⟩
  let finpt : FlaggedPoint (F circomPrime) := ⟨xv, yv, 0⟩
  exact CompleteAdd.soundness_core
    (P := ({ x := input_P_x, y := input_P_y, isInf := input_P_isInf } :
      FlaggedPoint (F circomPrime)))
    (Q := ({ x := input_Q_x, y := input_Q_y, isInf := input_Q_isInf } :
      FlaggedPoint (F circomPrime)))
    (s1 := finpt) (s2 := finpt)
    (out := ({ x := xv, y := yv, isInf := input_P_isInf } :
      FlaggedPoint (F circomPrime)))
    (infv := infpt) (finv := finpt)
    hP hQ hdxe hdye hsameX hsye hoppY
    (show decodeFe (emuOfNat ((decodeFe input_P_x * decodeFe input_P_x).val))
        = decodeFe input_P_x * decodeFe input_P_x from CompleteAdd.decodeFe_emuOfNat_val _)
    (show decodeFe (emuOfNat ((decodeFe (emuOfNat ((decodeFe input_P_x * decodeFe input_P_x).val))
          + decodeFe (emuOfNat ((decodeFe input_P_x * decodeFe input_P_x).val))).val))
        = decodeFe (emuOfNat ((decodeFe input_P_x * decodeFe input_P_x).val))
          + decodeFe (emuOfNat ((decodeFe input_P_x * decodeFe input_P_x).val)) from
          CompleteAdd.decodeFe_emuOfNat_val _)
    (show decodeFe (emuOfNat ((decodeFe (emuOfNat ((decodeFe (emuOfNat
          ((decodeFe input_P_x * decodeFe input_P_x).val))
          + decodeFe (emuOfNat ((decodeFe input_P_x * decodeFe input_P_x).val))).val))
          + decodeFe (emuOfNat ((decodeFe input_P_x * decodeFe input_P_x).val))).val))
        = decodeFe (emuOfNat ((decodeFe (emuOfNat
            ((decodeFe input_P_x * decodeFe input_P_x).val))
            + decodeFe (emuOfNat ((decodeFe input_P_x * decodeFe input_P_x).val))).val))
          + decodeFe (emuOfNat ((decodeFe input_P_x * decodeFe input_P_x).val)) from
          CompleteAdd.decodeFe_emuOfNat_val _)
      (decodeFe_sum2 input_P_y hPy.1)
      (by rw [if_neg (zero_ne_one (α := F circomPrime))])
      rfl
      (by
        intro _
        simpa using hlam_eq)
    hlamSqd hxse hx3v hx3e hxde hyprodd hy3v hy3e
      (fun _ => show (0 : F circomPrime) = 0 * oppv from by ring)
    hx3v hy3v rfl
    rfl (by rw [if_neg (zero_ne_one (α := F circomPrime))]) hs2 hout

private theorem completeness_finite : Completeness (F circomPrime) main FiniteAssumptions := by
  circuit_proof_start [
    FiniteAssumptions,
    MulModSub2F32.circuit, MulModSub2F32.Assumptions, MulModSub2F32.Spec,
    MulModSub2W32N.circuit, MulModSub2W32N.Assumptions, MulModSub2W32N.Spec,
    DivUncheckedD3.circuit, DivUncheckedD3.Assumptions, DivUncheckedD3.Spec]
  obtain ⟨hlam, hx3, hy3⟩ := h_env
  obtain ⟨hP, hQ, hP0, hQ0, hxne⟩ := h_assumptions
  have hPx : Fe.Valid input_P_x := hP.2.1
  have hPy : Fe.Valid input_P_y := hP.2.2.1
  have hQx : Fe.Valid input_Q_x := hQ.2.1
  have hQy : Fe.Valid input_Q_y := hQ.2.2.1
  obtain ⟨⟨hIPx, hIPy, hIPi⟩, hIQx, hIQy, hIQi⟩ := h_input
  have hdxe : decodeFe (Vector.map (Expression.eval env.toEnvironment)
        (Vector.ofFn fun k : Fin numLimbs => input_var_Q_x[k.val]'k.isLt
          + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
            - input_var_P_x[k.val]'k.isLt)))
      = decodeFe input_Q_x - decodeFe input_P_x := by
    rw [CompleteAdd.map_eval_borrow, hIQx, hIPx]
    exact CompleteAdd.decodeFe_borrow input_Q_x input_P_x hQx.1 hPx
  have hnumLimbs : ∀ i : Fin numLimbs,
      ((Vector.map (Expression.eval env.toEnvironment)
        (Vector.ofFn fun k : Fin numLimbs => input_var_Q_y[k.val]'k.isLt
          + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
            - input_var_P_y[k.val]'k.isLt)))[i.val]).val < 3 * 2 ^ limbBits := by
    intro i
    have hcell := congrArg (fun v : Emu (F circomPrime) => v[i.val]'i.isLt)
      (CompleteAdd.map_eval_borrow env.toEnvironment input_var_Q_y input_var_P_y)
    rw [hIQy, hIPy] at hcell
    simp only [Vector.getElem_map, Vector.getElem_ofFn] at hcell ⊢
    rw [hcell]
    exact CompleteAdd.limb_borrow_lt i.val (hQy.1 i) (hPy.1 i)
  have hnumVal : BigInt.value limbBits (Vector.map (Expression.eval env.toEnvironment)
        (Vector.ofFn fun k : Fin numLimbs => input_var_Q_y[k.val]'k.isLt
          + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
            - input_var_P_y[k.val]'k.isLt))) < 3 * P256 := by
    rw [CompleteAdd.map_eval_borrow, hIQy, hIPy]
    exact CompleteAdd.value_borrow_lt input_Q_y input_P_y hQy hPy
  have hdenLimbs : ∀ i : Fin numLimbs,
      ((Vector.map (Expression.eval env.toEnvironment)
        (Vector.ofFn fun k : Fin numLimbs => input_var_Q_x[k.val]'k.isLt
          + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
            - input_var_P_x[k.val]'k.isLt)))[i.val]).val < 3 * 2 ^ limbBits := by
    intro i
    have hcell := congrArg (fun v : Emu (F circomPrime) => v[i.val]'i.isLt)
      (CompleteAdd.map_eval_borrow env.toEnvironment input_var_Q_x input_var_P_x)
    rw [hIQx, hIPx] at hcell
    simp only [Vector.getElem_map, Vector.getElem_ofFn] at hcell ⊢
    rw [hcell]
    exact CompleteAdd.limb_borrow_lt i.val (hQx.1 i) (hPx.1 i)
  have hdenVal : BigInt.value limbBits (Vector.map (Expression.eval env.toEnvironment)
        (Vector.ofFn fun k : Fin numLimbs => input_var_Q_x[k.val]'k.isLt
          + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
            - input_var_P_x[k.val]'k.isLt))) < 3 * P256 := by
    rw [CompleteAdd.map_eval_borrow, hIQx, hIPx]
    exact CompleteAdd.value_borrow_lt input_Q_x input_P_x hQx hPx
  have hzeroDen : decodeFe (Vector.map (Expression.eval env.toEnvironment)
        (Vector.ofFn fun k : Fin numLimbs => input_var_Q_x[k.val]'k.isLt
          + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
            - input_var_P_x[k.val]'k.isLt))) = 0 →
      decodeFe (Vector.map (Expression.eval env.toEnvironment)
        (Vector.ofFn fun k : Fin numLimbs => input_var_Q_y[k.val]'k.isLt
          + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
            - input_var_P_y[k.val]'k.isLt))) = 0 := by
    intro hden0
    exfalso
    rw [hdxe, sub_eq_zero] at hden0
    contradiction
  have divAssumptions : DivUncheckedD3.Assumptions
      { num := Vector.map (Expression.eval env.toEnvironment)
          (Vector.ofFn fun k : Fin numLimbs => input_var_Q_y[k.val]'k.isLt
            + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
              - input_var_P_y[k.val]'k.isLt)),
        den := Vector.map (Expression.eval env.toEnvironment)
          (Vector.ofFn fun k : Fin numLimbs => input_var_Q_x[k.val]'k.isLt
            + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
              - input_var_P_x[k.val]'k.isLt)) } :=
    ⟨hnumLimbs, hnumVal, hdenLimbs, hdenVal, hzeroDen⟩
  obtain ⟨hlamv, -⟩ := hlam (by
    simpa [DivUncheckedD3.Assumptions] using divAssumptions)
  obtain ⟨hx3v, -⟩ := hx3 ⟨hlamv, hlamv, hPx, hQx⟩
  have yAssumptions : MulModSub2W32N.Assumptions
      { a := Vector.map (Expression.eval env.toEnvironment)
          (Vector.mapRange 8 fun i => var { index := i₀ + i }),
        b := Vector.map (Expression.eval env.toEnvironment)
          (Vector.ofFn fun k : Fin numLimbs => input_var_P_x[k.val]'k.isLt
            + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
                - var { index := i₀ + divUncheckedLen + k.val })),
        s1 := input_P_y,
        s2 := Vector.map (Expression.eval env.toEnvironment) zeroConst } := by
    refine ⟨hlamv, ?_, hPy, CompleteAdd.fe_valid_eval_zeroConst env.toEnvironment⟩
    · intro i
      have hpq := congrArg (fun v : Emu (F circomPrime) => v[i.val]'i.isLt) hIPx
      simp only [Vector.getElem_map] at hpq
      have hx3l := hx3v.1 i
      rw [Fin.getElem_fin, Vector.getElem_map, Vector.getElem_mapRange] at hx3l
      simp only [circuit_norm] at hx3l
      simp only [circuit_norm, Vector.getElem_map, Vector.getElem_ofFn, hpq]
      rw [← sub_eq_add_neg]
      exact CompleteAdd.limb_borrow_lt i.val (hPx.1 i) hx3l
  exact ⟨by simpa [DivUncheckedD3.Assumptions] using divAssumptions,
    ⟨hlamv, hlamv, hPx, hQx⟩,
    by simpa [MulModSub2W32N.Assumptions] using yAssumptions⟩

private theorem soundness_infinity :
    Soundness (F circomPrime) main InfinityAssumptions Spec := by
  circuit_proof_start [
    InfinityAssumptions,
    MulModSub2F32.circuit, MulModSub2F32.Assumptions, MulModSub2F32.Spec,
    MulModSub2W32N.circuit, MulModSub2W32N.Assumptions, MulModSub2W32N.Spec,
    DivUncheckedD3.circuit, DivUncheckedD3.Assumptions, DivUncheckedD3.Spec]
  obtain ⟨hlam, hx3, hy3⟩ := h_holds
  obtain ⟨hP, hQ, hP1, hQ1, hyEq⟩ := h_assumptions
  have hPx : Fe.Valid input_P_x := hP.2.1
  have hPy : Fe.Valid input_P_y := hP.2.2.1
  have hQx : Fe.Valid input_Q_x := hQ.2.1
  have hQy : Fe.Valid input_Q_y := hQ.2.2.1
  obtain ⟨⟨hIPx, hIPy, hIPi⟩, hIQx, hIQy, hIQi⟩ := h_input
  have hdye : decodeFe (Vector.map (Expression.eval env)
        (Vector.ofFn fun k : Fin numLimbs => input_var_Q_y[k.val]'k.isLt
          + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
            - input_var_P_y[k.val]'k.isLt)))
      = decodeFe input_Q_y - decodeFe input_P_y := by
    rw [CompleteAdd.map_eval_borrow, hIQy, hIPy]
    exact CompleteAdd.decodeFe_borrow input_Q_y input_P_y hQy.1 hPy
  obtain ⟨hlamv, -⟩ := hlam (by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro i
      have hcell := congrArg (fun v : Emu (F circomPrime) => v[i.val]'i.isLt)
        (CompleteAdd.map_eval_borrow env input_var_Q_y input_var_P_y)
      rw [hIQy, hIPy] at hcell
      simp only [Vector.getElem_map, Vector.getElem_ofFn] at hcell ⊢
      rw [hcell]
      exact CompleteAdd.limb_borrow_lt i.val (hQy.1 i) (hPy.1 i)
    · rw [CompleteAdd.map_eval_borrow, hIQy, hIPy]
      exact CompleteAdd.value_borrow_lt input_Q_y input_P_y hQy hPy
    · intro i
      have hcell := congrArg (fun v : Emu (F circomPrime) => v[i.val]'i.isLt)
        (CompleteAdd.map_eval_borrow env input_var_Q_x input_var_P_x)
      rw [hIQx, hIPx] at hcell
      simp only [Vector.getElem_map, Vector.getElem_ofFn] at hcell ⊢
      rw [hcell]
      exact CompleteAdd.limb_borrow_lt i.val (hQx.1 i) (hPx.1 i)
    · rw [CompleteAdd.map_eval_borrow, hIQx, hIPx]
      exact CompleteAdd.value_borrow_lt input_Q_x input_P_x hQx hPx
    · intro _hden0
      rw [hdye, hyEq, sub_self])
  obtain ⟨hx3v, -⟩ := hx3 ⟨hlamv, hlamv, hPx, hQx⟩
  obtain ⟨hy3v, -⟩ := hy3 (by
    refine ⟨hlamv, ?_, hPy, CompleteAdd.fe_valid_eval_zeroConst env⟩
    · intro i
      have hpq := congrArg (fun v : Emu (F circomPrime) => v[i.val]'i.isLt) hIPx
      simp only [Vector.getElem_map] at hpq
      have hx3l := hx3v.1 i
      rw [Fin.getElem_fin, Vector.getElem_map, Vector.getElem_mapRange] at hx3l
      simp only [circuit_norm] at hx3l
      simp only [circuit_norm, Vector.getElem_ofFn, hpq]
      rw [← sub_eq_add_neg]
      exact CompleteAdd.limb_borrow_lt i.val (hPx.1 i) hx3l)
  let xv : Emu (F circomPrime) :=
    Vector.map (Expression.eval env) (Vector.mapRange numLimbs fun i =>
      var { index := i₀ + divUncheckedLen + i })
  let yv : Emu (F circomPrime) :=
    Vector.map (Expression.eval env) (Vector.mapRange numLimbs fun i =>
      var { index := i₀ + divUncheckedLen + mulSub2Len + i })
  constructor
  · exact ⟨Or.inr hP1, hx3v, hy3v, fun h0 => by
      rw [hP1] at h0
      exact False.elim (one_ne_zero h0)⟩
  · rw [CompleteAdd.decodePoint_of_isInf
        (p := ({ x := xv, y := yv, isInf := input_P_isInf } :
          FlaggedPoint (F circomPrime))) hP1]
    rw [CompleteAdd.decodePoint_of_isInf
        (p := ({ x := input_P_x, y := input_P_y, isInf := input_P_isInf } :
          FlaggedPoint (F circomPrime))) hP1]
    rw [CompleteAdd.decodePoint_of_isInf
        (p := ({ x := input_Q_x, y := input_Q_y, isInf := input_Q_isInf } :
          FlaggedPoint (F circomPrime))) hQ1]
    rw [CompleteAdd.add_inf_left]

private theorem completeness_infinity :
    Completeness (F circomPrime) main InfinityAssumptions := by
  circuit_proof_start [
    InfinityAssumptions,
    MulModSub2F32.circuit, MulModSub2F32.Assumptions, MulModSub2F32.Spec,
    MulModSub2W32N.circuit, MulModSub2W32N.Assumptions, MulModSub2W32N.Spec,
    DivUncheckedD3.circuit, DivUncheckedD3.Assumptions, DivUncheckedD3.Spec]
  obtain ⟨hlam, hx3, hy3⟩ := h_env
  obtain ⟨hP, hQ, _hP1, _hQ1, hyEq⟩ := h_assumptions
  have hPx : Fe.Valid input_P_x := hP.2.1
  have hPy : Fe.Valid input_P_y := hP.2.2.1
  have hQx : Fe.Valid input_Q_x := hQ.2.1
  have hQy : Fe.Valid input_Q_y := hQ.2.2.1
  obtain ⟨⟨hIPx, hIPy, hIPi⟩, hIQx, hIQy, hIQi⟩ := h_input
  have hdye : decodeFe (Vector.map (Expression.eval env.toEnvironment)
        (Vector.ofFn fun k : Fin numLimbs => input_var_Q_y[k.val]'k.isLt
          + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
            - input_var_P_y[k.val]'k.isLt)))
      = decodeFe input_Q_y - decodeFe input_P_y := by
    rw [CompleteAdd.map_eval_borrow, hIQy, hIPy]
    exact CompleteAdd.decodeFe_borrow input_Q_y input_P_y hQy.1 hPy
  have hnumLimbs : ∀ i : Fin numLimbs,
      ((Vector.map (Expression.eval env.toEnvironment)
        (Vector.ofFn fun k : Fin numLimbs => input_var_Q_y[k.val]'k.isLt
          + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
            - input_var_P_y[k.val]'k.isLt)))[i.val]).val < 3 * 2 ^ limbBits := by
    intro i
    have hcell := congrArg (fun v : Emu (F circomPrime) => v[i.val]'i.isLt)
      (CompleteAdd.map_eval_borrow env.toEnvironment input_var_Q_y input_var_P_y)
    rw [hIQy, hIPy] at hcell
    simp only [Vector.getElem_map, Vector.getElem_ofFn] at hcell ⊢
    rw [hcell]
    exact CompleteAdd.limb_borrow_lt i.val (hQy.1 i) (hPy.1 i)
  have hnumVal : BigInt.value limbBits (Vector.map (Expression.eval env.toEnvironment)
        (Vector.ofFn fun k : Fin numLimbs => input_var_Q_y[k.val]'k.isLt
          + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
            - input_var_P_y[k.val]'k.isLt))) < 3 * P256 := by
    rw [CompleteAdd.map_eval_borrow, hIQy, hIPy]
    exact CompleteAdd.value_borrow_lt input_Q_y input_P_y hQy hPy
  have hdenLimbs : ∀ i : Fin numLimbs,
      ((Vector.map (Expression.eval env.toEnvironment)
        (Vector.ofFn fun k : Fin numLimbs => input_var_Q_x[k.val]'k.isLt
          + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
            - input_var_P_x[k.val]'k.isLt)))[i.val]).val < 3 * 2 ^ limbBits := by
    intro i
    have hcell := congrArg (fun v : Emu (F circomPrime) => v[i.val]'i.isLt)
      (CompleteAdd.map_eval_borrow env.toEnvironment input_var_Q_x input_var_P_x)
    rw [hIQx, hIPx] at hcell
    simp only [Vector.getElem_map, Vector.getElem_ofFn] at hcell ⊢
    rw [hcell]
    exact CompleteAdd.limb_borrow_lt i.val (hQx.1 i) (hPx.1 i)
  have hdenVal : BigInt.value limbBits (Vector.map (Expression.eval env.toEnvironment)
        (Vector.ofFn fun k : Fin numLimbs => input_var_Q_x[k.val]'k.isLt
          + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
            - input_var_P_x[k.val]'k.isLt))) < 3 * P256 := by
    rw [CompleteAdd.map_eval_borrow, hIQx, hIPx]
    exact CompleteAdd.value_borrow_lt input_Q_x input_P_x hQx hPx
  have hzeroDen : decodeFe (Vector.map (Expression.eval env.toEnvironment)
        (Vector.ofFn fun k : Fin numLimbs => input_var_Q_x[k.val]'k.isLt
          + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
            - input_var_P_x[k.val]'k.isLt))) = 0 →
      decodeFe (Vector.map (Expression.eval env.toEnvironment)
        (Vector.ofFn fun k : Fin numLimbs => input_var_Q_y[k.val]'k.isLt
          + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
            - input_var_P_y[k.val]'k.isLt))) = 0 := by
    intro _hden0
    rw [hdye, hyEq, sub_self]
  have divAssumptions : DivUncheckedD3.Assumptions
      { num := Vector.map (Expression.eval env.toEnvironment)
          (Vector.ofFn fun k : Fin numLimbs => input_var_Q_y[k.val]'k.isLt
            + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
              - input_var_P_y[k.val]'k.isLt)),
        den := Vector.map (Expression.eval env.toEnvironment)
          (Vector.ofFn fun k : Fin numLimbs => input_var_Q_x[k.val]'k.isLt
            + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
              - input_var_P_x[k.val]'k.isLt)) } :=
    ⟨hnumLimbs, hnumVal, hdenLimbs, hdenVal, hzeroDen⟩
  obtain ⟨hlamv, -⟩ := hlam (by
    simpa [DivUncheckedD3.Assumptions] using divAssumptions)
  obtain ⟨hx3v, -⟩ := hx3 ⟨hlamv, hlamv, hPx, hQx⟩
  have yAssumptions : MulModSub2W32N.Assumptions
      { a := Vector.map (Expression.eval env.toEnvironment)
          (Vector.mapRange 8 fun i => var { index := i₀ + i }),
        b := Vector.map (Expression.eval env.toEnvironment)
          (Vector.ofFn fun k : Fin numLimbs => input_var_P_x[k.val]'k.isLt
            + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
                - var { index := i₀ + divUncheckedLen + k.val })),
        s1 := input_P_y,
        s2 := Vector.map (Expression.eval env.toEnvironment) zeroConst } := by
    refine ⟨hlamv, ?_, hPy, CompleteAdd.fe_valid_eval_zeroConst env.toEnvironment⟩
    · intro i
      have hpq := congrArg (fun v : Emu (F circomPrime) => v[i.val]'i.isLt) hIPx
      simp only [Vector.getElem_map] at hpq
      have hx3l := hx3v.1 i
      rw [Fin.getElem_fin, Vector.getElem_map, Vector.getElem_mapRange] at hx3l
      simp only [circuit_norm] at hx3l
      simp only [circuit_norm, Vector.getElem_map, Vector.getElem_ofFn, hpq]
      rw [← sub_eq_add_neg]
      exact CompleteAdd.limb_borrow_lt i.val (hPx.1 i) hx3l
  exact ⟨by simpa [DivUncheckedD3.Assumptions] using divAssumptions,
    ⟨hlamv, hlamv, hPx, hQx⟩,
    by simpa [MulModSub2W32N.Assumptions] using yAssumptions⟩

theorem soundness : Soundness (F circomPrime) main Assumptions Spec := by
  intro offset env input_var input h_input h_assumptions h_holds
  obtain ⟨hP, hQ, hcase⟩ := h_assumptions
  rcases hcase with hfin | hinf
  · exact soundness_finite offset env input_var input h_input
      ⟨hP, hQ, hfin.1, hfin.2.1, hfin.2.2⟩ h_holds
  · exact soundness_infinity offset env input_var input h_input
      ⟨hP, hQ, hinf.1, hinf.2.1, hinf.2.2⟩ h_holds

theorem completeness : Completeness (F circomPrime) main Assumptions := by
  intro offset env input_var h_env input h_input h_assumptions
  obtain ⟨hP, hQ, hcase⟩ := h_assumptions
  rcases hcase with hfin | hinf
  · exact completeness_finite offset env input_var h_env input h_input
      ⟨hP, hQ, hfin.1, hfin.2.1, hfin.2.2⟩
  · exact completeness_infinity offset env input_var h_env input h_input
      ⟨hP, hQ, hinf.1, hinf.2.1, hinf.2.2⟩

def circuit : FormalCircuit (F circomPrime) Inputs FlaggedPoint where
  main
  elaborated
  Assumptions
  Spec
  soundness
  completeness

lemma localLength (input : Var Inputs (F circomPrime)) :
    circuit.localLength input = 1188 := rfl

theorem computableWitnesses : circuit.base.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition
      input env env') ((main input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  obtain ⟨P, Q⟩ := input
  have hdiv : ∀ (X : Var DivUncheckedD3.Inputs (F circomPrime)) (o : ℕ),
      (subcircuit DivUncheckedD3.circuit X).localLength o = 412 := fun _ _ => rfl
  have hms2 : ∀ (X : Var MulModSub2F32.Inputs (F circomPrime)) (o : ℕ),
      (subcircuit MulModSub2F32.circuit X).localLength o = 356 := fun _ _ => rfl
  have hms2W32N : ∀ (X : Var MulModSub2W32N.Inputs (F circomPrime)) (o : ℕ),
      (subcircuit MulModSub2W32N.circuit X).localLength o = 420 := fun _ _ => rfl
  have hDout : ∀ (X : Var DivUncheckedD3.Inputs (F circomPrime)) (o : ℕ),
      DivUncheckedD3.circuit.output X o = (DivUncheckedD3.main X).output o :=
    fun X o => (DivUncheckedD3.elaborated.output_eq X o).symm
  have hcell : ∀ {e e' : ProverEnvironment (F circomPrime)} (x : Var Emu (F circomPrime)),
      Vector.map (Expression.eval e.toEnvironment) x =
        Vector.map (Expression.eval e'.toEnvironment) x →
      ∀ (i : ℕ) (hi : i < numLimbs),
      Expression.eval e.toEnvironment (x[i]'hi) =
        Expression.eval e'.toEnvironment (x[i]'hi) := by
    intro e e' x hx i hi
    have := congrArg (fun v : Vector (F circomPrime) numLimbs => v[i]'hi) hx
    simpa only [Vector.getElem_map] using this
  let dyU : Var Emu (F circomPrime) := Vector.ofFn fun k : Fin numLimbs =>
    Q.y[k.val]'k.isLt
      + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
        - P.y[k.val]'k.isLt)
  let dxU : Var Emu (F circomPrime) := Vector.ofFn fun k : Fin numLimbs =>
    Q.x[k.val]'k.isLt
      + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
        - P.x[k.val]'k.isLt)
  let lam32 : Var DivUncheckedD3.Emu32 (F circomPrime) :=
    (subcircuit DivUncheckedD3.circuit { num := dyU, den := dxU }).output offset
  let x3 : Var Emu (F circomPrime) :=
    (subcircuit MulModSub2F32.circuit { a := lam32, b := lam32, s1 := P.x, s2 := Q.x }).output
      (offset + divUncheckedLen)
  let xdU : Var Emu (F circomPrime) := Vector.ofFn fun k : Fin numLimbs =>
    P.x[k.val]'k.isLt
      + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
        - x3[k.val]'k.isLt)
  unfold main
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.pure_structuralComputableWitnesses_iff,
    hdiv, hms2, hms2W32N, and_true]
  refine ⟨?_, ?_, ?_⟩
  · refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) DivUncheckedD3.circuit _ _ _ ?_
      DivUncheckedD3.computableWitnesses env env'
    intro k e e' _ _ h_in
    simp only [circuit_norm, Inputs.mk.injEq, FlaggedPoint.mk.injEq] at h_in
    obtain ⟨⟨hPx, hPy, _⟩, hQx, hQy, _⟩ := h_in
    simp only [circuit_norm] at ⊢
    rw [DivUncheckedD3.Inputs.mk.injEq]
    refine ⟨?_, ?_⟩
    · apply Vector.ext
      intro i hi
      simp only [Vector.getElem_map, Vector.getElem_ofFn]
      simp only [Expression.eval, hcell _ hQy i hi, hcell _ hPy i hi]
    · apply Vector.ext
      intro i hi
      simp only [Vector.getElem_map, Vector.getElem_ofFn]
      simp only [Expression.eval, hcell _ hQx i hi, hcell _ hPx i hi]
  · refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) MulModSub2F32.circuit _ _ _ ?_
      MulModSub2F32.computableWitnesses env env'
    intro k e e' hle h_agree h_in
    simp only [circuit_norm, Inputs.mk.injEq, FlaggedPoint.mk.injEq] at h_in
    obtain ⟨⟨hPx, _, _⟩, hQx, _, _⟩ := h_in
    have hlam := MulMod.bigInt_map_eval_eq_of_eval_eq
      (DivUncheckedD3.eval_output_of_agreesBelow { num := dyU, den := dxU }
        (offset := offset) h_agree (by omega))
    simp only [circuit_norm] at ⊢
    rw [MulModSub2F32.Inputs.mk.injEq, hDout]
    exact ⟨hlam, hlam, hPx, hQx⟩
  · refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) MulModSub2W32N.circuit _ _ _ ?_
      MulModSub2W32N.computableWitnesses env env'
    intro k e e' hle h_agree h_in
    simp only [circuit_norm, Inputs.mk.injEq, FlaggedPoint.mk.injEq] at h_in
    obtain ⟨⟨hPx, hPy, _⟩, _, _, _⟩ := h_in
    have hlam := MulMod.bigInt_map_eval_eq_of_eval_eq
      (DivUncheckedD3.eval_output_of_agreesBelow { num := dyU, den := dxU }
        (offset := offset) h_agree (by omega))
    have hx3s := emu_map_eval_eq_of_eval_eq
      (MulModSub2F32.eval_output_of_agreesBelow { a := lam32, b := lam32, s1 := P.x, s2 := Q.x }
        (offset := offset + divUncheckedLen) h_agree
        (by
          rw [show divUncheckedLen = 412 from rfl, show numLimbs = 4 from rfl]
          omega))
    simp only [circuit_norm] at ⊢
    rw [MulModSub2W32N.Inputs.mk.injEq, hDout]
    refine ⟨hlam, ?_, hPy, by rw [DivOrZero.eval_zeroConst, DivOrZero.eval_zeroConst]⟩
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_map, Vector.getElem_ofFn]
    have hPx_i := hcell _ hPx i hi
    have hx3_i := hcell _ hx3s i hi
    simp only [Expression.eval]
    exact congrArg₂ (· + ·) hPx_i
      (congrArg₂ (· + ·) rfl (congrArg (HMul.hMul (-1 : F circomPrime)) hx3_i))

theorem computableWitness : ∀ n input,
    ProverEnvironment.OnlyAccessedBelow n
      (fun env : ProverEnvironment (F circomPrime) => eval env input) →
    Circuit.ComputableWitnesses (main input) n :=
  Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnesses_implies
    (circuit := circuit.base) computableWitnesses

private lemma emuVar_stable {off k : ℕ}
    {env env' : ProverEnvironment (F circomPrime)}
    (h_agree : env.AgreesBelow k env') (hk : off + size Emu ≤ k) :
    eval env (varFromOffset Emu off : Var Emu (F circomPrime)) =
      eval env' (varFromOffset Emu off : Var Emu (F circomPrime)) := by
  rw [CircuitType.eval_expression_prover_to_verifier (M := Emu),
    CircuitType.eval_expression_prover_to_verifier (M := Emu), ProvableType.ext_iff]
  intro i hi
  rw [← ProvableType.getElem_eval_toElements
      (varFromOffset Emu off : Var Emu (F circomPrime)) i hi,
    ← ProvableType.getElem_eval_toElements
      (varFromOffset Emu off : Var Emu (F circomPrime)) i hi]
  simp only [varFromOffset, ProvableType.toElements_fromElements,
    Vector.getElem_mapRange, Expression.eval]
  exact h_agree (off + i) (by omega)

lemma eval_output_of_agreesBelow (input : Var Inputs (F circomPrime)) {offset k : ℕ}
    {env env' : ProverEnvironment (F circomPrime)}
    (h_input : eval env input = eval env' input)
    (h_agree : env.AgreesBelow k env') (hk : offset + 1188 ≤ k) :
    eval env ((main input).output offset) =
      eval env' ((main input).output offset) := by
  obtain ⟨P, Q⟩ := input
  change eval env
      ({ x := varFromOffset Emu (offset + divUncheckedLen),
         y := varFromOffset Emu (offset + divUncheckedLen + mulSub2Len),
         isInf := P.isInf } : Var FlaggedPoint (F circomPrime)) =
    eval env'
      ({ x := varFromOffset Emu (offset + divUncheckedLen),
         y := varFromOffset Emu (offset + divUncheckedLen + mulSub2Len),
         isInf := P.isInf } : Var FlaggedPoint (F circomPrime))
  simp only [circuit_norm]
  rw [FlaggedPoint.mk.injEq]
  have hp := congrArg Inputs.P h_input
  simp only [circuit_norm, FlaggedPoint.mk.injEq] at hp
  refine ⟨?_, ?_, hp.2.2⟩
  · simpa only [circuit_norm] using
      emuVar_stable (off := offset + divUncheckedLen) h_agree
        (by
          rw [show size Emu = numLimbs from rfl, show divUncheckedLen = 412 from rfl,
            show numLimbs = 4 from rfl]
          omega)
  · simpa only [circuit_norm] using
      emuVar_stable (off := offset + divUncheckedLen + mulSub2Len) h_agree
        (by
          rw [show size Emu = numLimbs from rfl, show divUncheckedLen = 412 from rfl,
            show mulSub2Len = 356 from rfl, show numLimbs = 4 from rfl]
          omega)

end PhiPairAdd

end Solution.Secp256k1ScalarMul
