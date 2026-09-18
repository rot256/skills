import Solution.Secp256k1ScalarMul.ScalarReduce
import Solution.Secp256k1ScalarMul.MulMod
import Solution.Secp256k1ScalarMul.MulModVariantsCost
import Solution.Secp256k1ScalarMul.Cost
import Solution.Secp256k1ScalarMul.Mux
import Solution.Secp256k1ScalarMul.NegativeMagnitude
import Solution.Secp256k1ScalarMul.ParamsRel
import Solution.Secp256k1ScalarMul.ScaleVec
import Solution.Secp256k1ScalarMul.RelCells
import Solution.Secp256k1ScalarMul.GroupedEqXVNoTop
import Challenge.Utils.ComputableWitnessLemmas

namespace Solution.Secp256k1ScalarMul.GLVScalarRelation

set_option maxRecDepth 4000

open Challenge.CostR1CS
open Utils.Bits
open Solution.Secp256k1ScalarMul.Cost
open Solution.Secp256k1ScalarMul.Limbs
open Solution.Secp256k1ScalarMul.GLV

structure Inputs (F : Type) where
  s : Emu F
  u1 : SignedCoeff F
  u2 : SignedCoeff F
  v1 : SignedCoeff F
  v2 : SignedCoeff F
deriving ProvableStruct

def scalarMulModLoose :=
  MulModLoose.circuit secpParams gfMul posOfMul 5 vMul vMul hgvMul hNfMul hNfMul

def scalarMulModLooseWideB :=
  MulModLooseCA.circuitWideB secpParams gfMul posOfMul 5 vMul vMul hgvMul hNfMul hNfMul

def magnitudeExpr (c : Var SignedCoeff (F circomPrime)) : Expression (F circomPrime) :=
  fieldFromBitsExpr (lowBits c.bits)

def signedResidue (c : SignedCoeff (F circomPrime)) : ZMod scalarOrder :=
  if c.sign = 1 then -((magnitude c : ℕ) : ZMod scalarOrder)
  else ((magnitude c : ℕ) : ZMod scalarOrder)

def scalarResidue (s : Emu (F circomPrime)) : ZMod scalarOrder :=
  (BigInt.value limbBits s : ZMod scalarOrder)

def Relation (input : Inputs (F circomPrime)) : Prop :=
  scalarResidue input.s *
      (signedResidue input.v1 + (eigenvalue : ZMod scalarOrder) * signedResidue input.v2) +
    signedResidue input.u1 + (eigenvalue : ZMod scalarOrder) * signedResidue input.u2 = 0

def VNonzero (input : Inputs (F circomPrime)) : Prop :=
  magnitude input.v1 ≠ 0 ∨ magnitude input.v2 ≠ 0

def Assumptions (input : Inputs (F circomPrime)) : Prop :=
  input.s.Normalized limbBits ∧ Valid input.u1 ∧ Valid input.u2 ∧
    Valid input.v1 ∧ Valid input.v2

def Spec (input : Inputs (F circomPrime)) : Prop :=
  Relation input ∧ VNonzero input

/-- The natural-number left-hand side of the certified integer identity. -/
def relLhsNat (env : Environment (F circomPrime))
    (mu1 mu2 : Expression (F circomPrime)) (c e : Var Emu (F circomPrime)) : ℕ :=
  eigenvalue * (Expression.eval env mu2).val + (Expression.eval env mu1).val
    + BigInt.value 64 (Vector.map (Expression.eval env) c)
    + BigInt.value 64 (Vector.map (Expression.eval env) e)
    + biasKRel * scalarOrder

/-- The unquotiented right-hand side of the certified integer identity. -/
def relRhs0Nat (env : Environment (F circomPrime))
    (nm1 nm2 : Expression (F circomPrime)) (d f : Var Emu (F circomPrime)) : ℕ :=
  2 * (eigenvalue * (Expression.eval env nm2).val) + 2 * (Expression.eval env nm1).val
    + 2 * BigInt.value 64 (Vector.map (Expression.eval env) d)
    + 2 * BigInt.value 64 (Vector.map (Expression.eval env) f)

/-- The witnessed quotient of the deferred mod-`n` congruence. -/
def qRelNat (env : Environment (F circomPrime))
    (mu1 mu2 nm1 nm2 : Expression (F circomPrime))
    (c e d f : Var Emu (F circomPrime)) : ℕ :=
  (relLhsNat env mu1 mu2 c e - relRhs0Nat env nm1 nm2 d f) / scalarOrder

/-- The deferred relation quotient recovered from its native-field identity.
The scalar order is nonzero in the Circom field, so this affine expression is
the unique possible quotient. -/
def qRelInv
    (mu1 mu2 nm1 nm2 : Expression (F circomPrime))
    (c e d f : Var Emu (F circomPrime)) : Expression (F circomPrime) :=
  let lhs := RelCells.relLhs mu1 mu2 c e
  let rhs0 := RelCells.relRhs nm1 nm2 0 d f
  (MulMod.polyEvalExpr lhs ((2 : F circomPrime) ^ limbBits) -
      MulMod.polyEvalExpr rhs0 ((2 : F circomPrime) ^ limbBits)) *
    ((((scalarOrder : ℕ) : F circomPrime))⁻¹)

lemma scalarOrder_cast_ne_zero : (((scalarOrder : ℕ) : F circomPrime)) ≠ 0 := by
  norm_num [scalarOrder, Specs.Secp256k1.order, circomPrime,
    Challenge.Instances.Secp256k1ScalarMul.Interface.circomPrime]
  decide

lemma eval_qRelInv_mul_order
    (env : Environment (F circomPrime))
    (mu1 mu2 nm1 nm2 : Expression (F circomPrime))
    (c e d f : Var Emu (F circomPrime)) :
    Expression.eval env (qRelInv mu1 mu2 nm1 nm2 c e d f) *
        (((scalarOrder : ℕ) : F circomPrime)) =
      Expression.eval env
        (MulMod.polyEvalExpr (RelCells.relLhs mu1 mu2 c e)
          ((2 : F circomPrime) ^ limbBits)) -
      Expression.eval env
        (MulMod.polyEvalExpr (RelCells.relRhs nm1 nm2 0 d f)
          ((2 : F circomPrime) ^ limbBits)) := by
  simp only [qRelInv, Expression.eval]
  rw [mul_assoc, inv_mul_cancel₀ scalarOrder_cast_ne_zero, mul_one]
  simp only [neg_one_mul, sub_eq_add_neg]

lemma eval_relRhs_q
    (env : Environment (F circomPrime))
    (nm1 nm2 q : Expression (F circomPrime))
    (d f : Var Emu (F circomPrime)) :
    Expression.eval env
        (MulMod.polyEvalExpr (RelCells.relRhs nm1 nm2 q d f)
          ((2 : F circomPrime) ^ limbBits)) =
      Expression.eval env
        (MulMod.polyEvalExpr (RelCells.relRhs nm1 nm2 0 d f)
          ((2 : F circomPrime) ^ limbBits)) +
      Expression.eval env q * (((scalarOrder : ℕ) : F circomPrime)) := by
  simp only [MulMod.polyEvalExpr_eval, RelCells.relRhs, Vector.getElem_ofFn,
    RelCells.rhsCell, RelCells.natE, Expression.eval, Fin.sum_univ_four]
  have hn := congrArg (fun n : ℕ => (n : F circomPrime)) RelCells.limb_sum_order
  push_cast at hn
  norm_num [limbBits] at hn ⊢
  linear_combination (Expression.eval env q) * hn

lemma qRelInv_linIdent
    (env : Environment (F circomPrime))
    (mu1 mu2 nm1 nm2 : Expression (F circomPrime))
    (c e d f : Var Emu (F circomPrime)) :
    GroupedEqXV.LinIdent limbBits
      { lhs := Vector.map (Expression.eval env) (RelCells.relLhs mu1 mu2 c e),
        rhs := Vector.map (Expression.eval env)
          (RelCells.relRhs nm1 nm2 (qRelInv mu1 mu2 nm1 nm2 c e d f) d f) } := by
  unfold GroupedEqXV.LinIdent
  simp only [Vector.getElem_map]
  rw [← MulMod.polyEvalExpr_eval env (RelCells.relLhs mu1 mu2 c e),
    ← MulMod.polyEvalExpr_eval env
      (RelCells.relRhs nm1 nm2 (qRelInv mu1 mu2 nm1 nm2 c e d f) d f)]
  have hq := eval_qRelInv_mul_order env mu1 mu2 nm1 nm2 c e d f
  rw [eval_relRhs_q]
  simpa only [add_comm] using (sub_eq_iff_eq_add.mp hq.symm)

lemma eval_qRelInv_of_identity
    (env : Environment (F circomPrime))
    (mu1 mu2 nm1 nm2 : Expression (F circomPrime))
    (c e d f : Var Emu (F circomPrime)) (q0 : F circomPrime)
    (hid : Expression.eval env
        (MulMod.polyEvalExpr (RelCells.relLhs mu1 mu2 c e)
          ((2 : F circomPrime) ^ limbBits)) =
      Expression.eval env
        (MulMod.polyEvalExpr (RelCells.relRhs nm1 nm2 0 d f)
          ((2 : F circomPrime) ^ limbBits)) +
        (((scalarOrder : ℕ) : F circomPrime)) * q0) :
    Expression.eval env (qRelInv mu1 mu2 nm1 nm2 c e d f) = q0 := by
  apply mul_right_cancel₀ scalarOrder_cast_ne_zero
  rw [eval_qRelInv_mul_order]
  rw [show Expression.eval env
        (MulMod.polyEvalExpr (RelCells.relLhs mu1 mu2 c e)
          ((2 : F circomPrime) ^ limbBits)) -
      Expression.eval env
        (MulMod.polyEvalExpr (RelCells.relRhs nm1 nm2 0 d f)
          ((2 : F circomPrime) ^ limbBits)) =
      q0 * (((scalarOrder : ℕ) : F circomPrime)) from
        sub_eq_iff_eq_add.mpr (by simpa only [add_comm, mul_comm] using hid)]

def main (input : Var Inputs (F circomPrime)) : Circuit (F circomPrime) Unit := do

  let vSum := magnitudeExpr input.v1 + magnitudeExpr input.v2
  let vInv ← witness fun env =>
    let x : F circomPrime := Expression.eval env vSum
    x⁻¹
  assertZero (vSum * vInv - 1)

  let W ← subcircuit scalarMulModLooseWideB
    { a := eigenvalueConst, b := input.s, modulus := nConst }

  let nm1 ← subcircuit NegativeMagnitude.circuit
    { sign := input.u1.sign, magnitude := magnitudeExpr input.u1 }
  let nm2 ← subcircuit NegativeMagnitude.circuit
    { sign := input.u2.sign, magnitude := magnitudeExpr input.u2 }

  let c ← subcircuit ScaleVec.circuit { a := input.s, b := magnitudeExpr input.v1 }
  let d ← subcircuit ScaleVec.circuit { a := c, b := input.v1.sign }
  let e ← subcircuit ScaleVec.circuit { a := W, b := magnitudeExpr input.v2 }
  let f ← subcircuit ScaleVec.circuit { a := e, b := input.v2.sign }

  let q := qRelInv (magnitudeExpr input.u1) (magnitudeExpr input.u2)
    nm1 nm2 c e d f
  RangeCheck.circuit qBitsRel (by decide) (by decide) q
  GroupedEqXV.circuitNoTop 64 gfFold posOfFold 3 vRelL vRelR hgvRel (by norm_num)
    { lhs := RelCells.relLhs (magnitudeExpr input.u1) (magnitudeExpr input.u2) c e,
      rhs := RelCells.relRhs nm1 nm2 q d f }

instance elaborated : ElaboratedCircuit (F circomPrime) Inputs unit main := by
  elaborate_circuit

lemma magnitudeExpr_eval (env : Environment (F circomPrime))
    (c : Var SignedCoeff (F circomPrime)) :
    Expression.eval env (magnitudeExpr c) =
      ((magnitude
        { sign := Expression.eval env c.sign,
          bits := c.bits.map (Expression.eval env) } : ℕ) : F circomPrime) := by
  let cv : SignedCoeff (F circomPrime) :=
    { sign := Expression.eval env c.sign,
      bits := c.bits.map (Expression.eval env) }
  have hlo : Expression.eval env (fieldFromBitsExpr (lowBits c.bits)) =
      fieldFromBits (lowBits cv.bits) := by
    calc
      Expression.eval env (fieldFromBitsExpr (lowBits c.bits)) =
          fieldFromBits ((lowBits c.bits).map (Expression.eval env)) :=
        fieldFromBits_eval (eval := env) (lowBits c.bits)
      _ = fieldFromBits (lowBits cv.bits) := by simp only [cv, lowBits_map]
  change Expression.eval env (fieldFromBitsExpr (lowBits c.bits)) = _
  rw [hlo]
  simp only [magnitude, cv]
  rw [ZMod.natCast_zmod_val (fieldFromBits (lowBits (c.bits.map (Expression.eval env))))]

lemma magnitude_sum_lt_prime {v1 v2 : SignedCoeff (F circomPrime)}
    (h1 : Valid v1) (h2 : Valid v2) :
    magnitude v1 + magnitude v2 < circomPrime := by
  have h1' := magnitude_lt h1
  have h2' := magnitude_lt h2
  have hcap : 2 ^ coeffBits + 2 ^ coeffBits < circomPrime := by decide
  omega

lemma magnitude_sum_ne_zero_iff {v1 v2 : SignedCoeff (F circomPrime)}
    (h1 : Valid v1) (h2 : Valid v2) :
    (((magnitude v1 + magnitude v2 : ℕ) : F circomPrime) ≠ 0) ↔
      (magnitude v1 ≠ 0 ∨ magnitude v2 ≠ 0) := by
  rw [ne_eq, ← ZMod.val_eq_zero, ZMod.val_natCast_of_lt (magnitude_sum_lt_prime h1 h2)]
  omega

/-! ## Arithmetic core of the deferred mod-`n` congruence -/

/-- The `0/1` weight attached to a sign bit. -/
def signBit (c : SignedCoeff (F circomPrime)) : ℕ := if c.sign = 1 then 1 else 0

lemma signedResidue_of_signBit (c : SignedCoeff (F circomPrime)) (h : IsBool c.sign) :
    signedResidue c = ((magnitude c : ℕ) : ZMod scalarOrder)
      - 2 * ((signBit c : ℕ) : ZMod scalarOrder) * ((magnitude c : ℕ) : ZMod scalarOrder) := by
  unfold signedResidue signBit
  rcases h with h | h <;> rw [h]
  · rw [if_neg (by exact zero_ne_one), if_neg (by exact zero_ne_one)]
    push_cast
    ring
  · rw [if_pos rfl, if_pos rfl]
    push_cast
    ring

/-- `Relation` is equivalent to the mod-`n` congruence certified by the grouped
carry check, once the `λ·s` product `Wv` is known to be congruent to `λ·s`. -/
lemma relation_iff_congr
    {u1 u2 v1 v2 : SignedCoeff (F circomPrime)} {s : Emu (F circomPrime)} {Wv : ℕ}
    (hu1 : IsBool u1.sign) (hu2 : IsBool u2.sign)
    (hv1 : IsBool v1.sign) (hv2 : IsBool v2.sign)
    (hWz : ((Wv : ℕ) : ZMod scalarOrder)
      = (eigenvalue : ZMod scalarOrder)
        * ((BigInt.value limbBits s : ℕ) : ZMod scalarOrder)) :
    Relation { s := s, u1 := u1, u2 := u2, v1 := v1, v2 := v2 } ↔
      ((eigenvalue * magnitude u2 + magnitude u1
          + magnitude v1 * BigInt.value limbBits s + magnitude v2 * Wv : ℕ) :
            ZMod scalarOrder)
        = ((2 * (eigenvalue * (signBit u2 * magnitude u2))
            + 2 * (signBit u1 * magnitude u1)
            + 2 * (signBit v1 * (magnitude v1 * BigInt.value limbBits s))
            + 2 * (signBit v2 * (magnitude v2 * Wv)) : ℕ) : ZMod scalarOrder) := by
  unfold Relation scalarResidue
  rw [signedResidue_of_signBit u1 hu1, signedResidue_of_signBit u2 hu2,
    signedResidue_of_signBit v1 hv1, signedResidue_of_signBit v2 hv2]
  push_cast
  rw [hWz]
  constructor <;> intro h <;> linear_combination h

lemma eval_mapRange_var (env : Environment (F circomPrime)) (base : ℕ) (k : ℕ)
    (hk : k < numLimbs) :
    Expression.eval env
        ((Vector.mapRange numLimbs fun i => var (F := F circomPrime) { index := base + i })[k]'hk)
      = env.get (base + k) := by
  simp only [Vector.getElem_mapRange, Expression.eval]

lemma bigIntValue_of_scaled {a cv : Emu (F circomPrime)} {m : ℕ}
    (h : ∀ k : Fin numLimbs, (cv[k.val]'k.isLt).val = (a[k.val]'k.isLt).val * m) :
    BigInt.value 64 cv = BigInt.value 64 a * m := by
  rw [MulModFold.bigIntValue_four, MulModFold.bigIntValue_four,
    h ⟨0, by decide⟩, h ⟨1, by decide⟩, h ⟨2, by decide⟩, h ⟨3, by decide⟩]
  ring

lemma val_mul_bool {x s : F circomPrime} (h : IsBool s) :
    (x * s).val = x.val * (if s = 1 then 1 else 0) := by
  rcases h with h | h <;> rw [h]
  · simp
  · simp

lemma val_natCast_magnitude {c : SignedCoeff (F circomPrime)} (h : Valid c) :
    (((magnitude c : ℕ) : F circomPrime)).val = magnitude c :=
  ZMod.val_natCast_of_lt (lt_trans (magnitude_lt h) (by decide))

/-- The certified integer identity implies the mod-`n` relation. -/
lemma relation_of_nat_identity
    {s : Emu (F circomPrime)} {u1 u2 v1 v2 : SignedCoeff (F circomPrime)}
    (hu1 : IsBool u1.sign) (hu2 : IsBool u2.sign)
    (hv1 : IsBool v1.sign) (hv2 : IsBool v2.sign)
    {mu1v mu2v nm1v nm2v cv dv ev fv qv Wv : ℕ}
    (hWz : ((Wv : ℕ) : ZMod scalarOrder)
      = (eigenvalue : ZMod scalarOrder)
        * ((BigInt.value limbBits s : ℕ) : ZMod scalarOrder))
    (hmu1 : mu1v = magnitude u1) (hmu2 : mu2v = magnitude u2)
    (hnm1 : nm1v = signBit u1 * magnitude u1) (hnm2 : nm2v = signBit u2 * magnitude u2)
    (hcv : cv = BigInt.value limbBits s * magnitude v1)
    (hdv : dv = cv * signBit v1)
    (hev : ev = Wv * magnitude v2)
    (hfv : fv = ev * signBit v2)
    (hid : eigenvalue * mu2v + mu1v + cv + ev + biasKRel * scalarOrder
      = 2 * (eigenvalue * nm2v) + 2 * nm1v + 2 * dv + 2 * fv + scalarOrder * qv) :
    Relation { s := s, u1 := u1, u2 := u2, v1 := v1, v2 := v2 } := by
  refine (relation_iff_congr (Wv := Wv) hu1 hu2 hv1 hv2 hWz).mpr ?_
  have hz := congrArg (fun x : ℕ => (x : ZMod scalarOrder)) hid
  simp only [hmu1, hmu2, hnm1, hnm2, hcv, hdv, hev, hfv] at hz
  push_cast at hz ⊢
  have hn : ((scalarOrder : ℕ) : ZMod scalarOrder) = 0 := ZMod.natCast_self _
  rw [hn] at hz
  linear_combination hz

/-- Product of two 64-bit field values: `val` is the product of the `val`s. -/
lemma val_mul_of_lt64 {x y : F circomPrime} (hx : x.val < 2 ^ 64) (hy : y.val < 2 ^ 64) :
    (x * y).val = x.val * y.val := by
  refine ZMod.val_mul_of_lt ?_
  have h : x.val * y.val < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' hx hy
  have hp : (2:ℕ) ^ 64 * 2 ^ 64 < circomPrime := by decide
  omega

/-- `val` of a sign-routed field element. -/
lemma val_ite_sign {sgn x : F circomPrime} {m : ℕ} (hx : x.val = m) :
    (if sgn = 1 then x else 0).val = (if sgn = 1 then 1 else 0) * m := by
  split
  · rw [hx, one_mul]
  · simp

theorem soundness :
    FormalAssertion.Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [MulModLoose.circuit, MulModLoose.Spec, MulModLooseCA.circuitWideB,
    MulModLooseCA.Spec, MulMod.AssumptionsWideB,
    NegativeMagnitude.circuit, NegativeMagnitude.Assumptions, NegativeMagnitude.Spec,
    ScaleVec.circuit, ScaleVec.Assumptions, ScaleVec.Spec,
    RangeCheck.circuit, RangeCheck.Assumptions, RangeCheck.Spec,
    GroupedEqXV.circuitNoTop, GroupedEqXV.elaboratedNoTop,
    GroupedEqXV.AssumptionsNoTop, GroupedEqXV.Assumptions, GroupedEqX.Spec,
    scalarMulModLooseWideB, main]
  obtain ⟨hinv, hW, hnm1, hnm2, hc, hd, he, hf, hq, hgrouped⟩ := h_holds
  set B0 : ℕ := i₀ + 1 +
      (numLimbs + numLimbs + numLimbs * (secpParams.B - 1) + numLimbs * (secpParams.B - 1) +
        GroupedEqXV.widthAllocFrom vMul.Wf (5 - 2) 0) with hB0def
  set Wvar : Var Emu (F circomPrime) :=
    Vector.mapRange numLimbs fun i => var (F := F circomPrime) { index := i₀ + 1 + numLimbs + i }
    with hWvar
  set cvar : Var Emu (F circomPrime) :=
    Vector.mapRange numLimbs fun i => var (F := F circomPrime) { index := B0 + 1 + 1 + i }
    with hcvar
  set dvar : Var Emu (F circomPrime) :=
    Vector.mapRange numLimbs fun i => var (F := F circomPrime) { index := B0 + 1 + 1 + numLimbs + i }
    with hdvar
  set evar : Var Emu (F circomPrime) :=
    Vector.mapRange numLimbs fun i =>
      var (F := F circomPrime) { index := B0 + 1 + 1 + numLimbs + numLimbs + i }
    with hevar
  set fvar : Var Emu (F circomPrime) :=
    Vector.mapRange numLimbs fun i =>
      var (F := F circomPrime) { index := B0 + 1 + 1 + numLimbs + numLimbs + numLimbs + i }
    with hfvar
  obtain ⟨hsN, hu1V, hu2V, hv1V, hv2V⟩ := h_assumptions
  -- evaluated magnitudes of the four signed coefficients
  have hmu1e := magnitudeExpr_eval env { sign := input_var_u1_sign, bits := input_var_u1_bits }
  have hmu2e := magnitudeExpr_eval env { sign := input_var_u2_sign, bits := input_var_u2_bits }
  have hmv1e := magnitudeExpr_eval env { sign := input_var_v1_sign, bits := input_var_v1_bits }
  have hmv2e := magnitudeExpr_eval env { sign := input_var_v2_sign, bits := input_var_v2_bits }
  rw [h_input.2.1.1, h_input.2.1.2] at hmu1e
  rw [h_input.2.2.1.1, h_input.2.2.1.2] at hmu2e
  rw [h_input.2.2.2.1.1, h_input.2.2.2.1.2] at hmv1e
  rw [h_input.2.2.2.2.1, h_input.2.2.2.2.2] at hmv2e
  have hmu1val : (Expression.eval env
      (magnitudeExpr { sign := input_var_u1_sign, bits := input_var_u1_bits })).val
      = magnitude { sign := input_u1_sign, bits := input_u1_bits } := by
    rw [hmu1e]; exact val_natCast_magnitude hu1V
  have hmu2val : (Expression.eval env
      (magnitudeExpr { sign := input_var_u2_sign, bits := input_var_u2_bits })).val
      = magnitude { sign := input_u2_sign, bits := input_u2_bits } := by
    rw [hmu2e]; exact val_natCast_magnitude hu2V
  have hmv1val : (Expression.eval env
      (magnitudeExpr { sign := input_var_v1_sign, bits := input_var_v1_bits })).val
      = magnitude { sign := input_v1_sign, bits := input_v1_bits } := by
    rw [hmv1e]; exact val_natCast_magnitude hv1V
  have hmv2val : (Expression.eval env
      (magnitudeExpr { sign := input_var_v2_sign, bits := input_var_v2_bits })).val
      = magnitude { sign := input_v2_sign, bits := input_v2_bits } := by
    rw [hmv2e]; exact val_natCast_magnitude hv2V
  have hmu1lt : (Expression.eval env
      (magnitudeExpr { sign := input_var_u1_sign, bits := input_var_u1_bits })).val < 2 ^ 64 := by
    rw [hmu1val]; exact magnitude_lt hu1V
  have hmu2lt : (Expression.eval env
      (magnitudeExpr { sign := input_var_u2_sign, bits := input_var_u2_bits })).val < 2 ^ 64 := by
    rw [hmu2val]; exact magnitude_lt hu2V
  have hmv1lt : (Expression.eval env
      (magnitudeExpr { sign := input_var_v1_sign, bits := input_var_v1_bits })).val < 2 ^ 64 := by
    rw [hmv1val]; exact magnitude_lt hv1V
  have hmv2lt : (Expression.eval env
      (magnitudeExpr { sign := input_var_v2_sign, bits := input_var_v2_bits })).val < 2 ^ 64 := by
    rw [hmv2val]; exact magnitude_lt hv2V
  -- the `λ·s` product
  have hWA : BigInt.Normalized secpParams.B (Vector.map (Expression.eval env) eigenvalueConst) ∧
      BigInt.Normalized secpParams.B input_s ∧
      BigInt.Normalized secpParams.B (Vector.map (Expression.eval env) nConst) ∧
      BigInt.value secpParams.B (Vector.map (Expression.eval env) eigenvalueConst) <
        BigInt.value secpParams.B (Vector.map (Expression.eval env) nConst) ∧
      0 < BigInt.value secpParams.B (Vector.map (Expression.eval env) nConst) := by
    have hev : BigInt.value secpParams.B (Vector.map (Expression.eval env) eigenvalueConst)
        = eigenvalue := eigenvalueConst_value env
    have hnv : BigInt.value secpParams.B (Vector.map (Expression.eval env) nConst)
        = scalarOrder := nConst_value env
    refine ⟨eigenvalueConst_normalized env, hsN, nConst_normalized env, ?_, ?_⟩
    · rw [hev, hnv]; exact eigenvalue_lt_order
    · rw [hnv]; exact scalarOrder_pos
  have hev : BigInt.value secpParams.B (Vector.map (Expression.eval env) eigenvalueConst)
      = eigenvalue := eigenvalueConst_value env
  have hnv : BigInt.value secpParams.B (Vector.map (Expression.eval env) nConst)
      = scalarOrder := nConst_value env
  obtain ⟨hWN, hWmod⟩ := hW hWA
  rw [hnv, hev] at hWmod
  have hWz : ((BigInt.value limbBits (Vector.map (Expression.eval env) Wvar) : ℕ) :
        ZMod scalarOrder)
      = (eigenvalue : ZMod scalarOrder) *
        ((BigInt.value limbBits input_s : ℕ) : ZMod scalarOrder) := by
    have h := (ZMod.natCast_eq_natCast_iff' _ _ scalarOrder).mpr hWmod
    push_cast at h
    exact h
  -- per-cell readings of the witnessed vectors
  have hWvec : ∀ k : Fin numLimbs,
      ((Vector.map (Expression.eval env) Wvar)[k.val]'k.isLt) = env.get (i₀ + 1 + numLimbs + k.val) := by
    intro k
    rw [Vector.getElem_map, hWvar]
    exact eval_mapRange_var env (i₀ + 1 + numLimbs) k.val k.isLt
  have hcvec : ∀ k : Fin numLimbs,
      ((Vector.map (Expression.eval env) cvar)[k.val]'k.isLt) = env.get (B0 + 1 + 1 + k.val) := by
    intro k
    rw [Vector.getElem_map, hcvar]
    exact eval_mapRange_var env (B0 + 1 + 1) k.val k.isLt
  have hdvec : ∀ k : Fin numLimbs,
      ((Vector.map (Expression.eval env) dvar)[k.val]'k.isLt)
        = env.get (B0 + 1 + 1 + numLimbs + k.val) := by
    intro k
    rw [Vector.getElem_map, hdvar]
    exact eval_mapRange_var env (B0 + 1 + 1 + numLimbs) k.val k.isLt
  have hevec : ∀ k : Fin numLimbs,
      ((Vector.map (Expression.eval env) evar)[k.val]'k.isLt)
        = env.get (B0 + 1 + 1 + numLimbs + numLimbs + k.val) := by
    intro k
    rw [Vector.getElem_map, hevar]
    exact eval_mapRange_var env (B0 + 1 + 1 + numLimbs + numLimbs) k.val k.isLt
  have hfvec : ∀ k : Fin numLimbs,
      ((Vector.map (Expression.eval env) fvar)[k.val]'k.isLt)
        = env.get (B0 + 1 + 1 + numLimbs + numLimbs + numLimbs + k.val) := by
    intro k
    rw [Vector.getElem_map, hfvar]
    exact eval_mapRange_var env (B0 + 1 + 1 + numLimbs + numLimbs + numLimbs) k.val k.isLt
  have hWlt : ∀ k : Fin numLimbs, (env.get (i₀ + 1 + numLimbs + k.val)).val < 2 ^ 64 := by
    intro k
    have h : ((Vector.map (Expression.eval env) Wvar)[k.val]'k.isLt).val < 2 ^ 64 := hWN k
    rwa [hWvec k] at h
  -- cell values
  have hcval : ∀ k : Fin numLimbs, (env.get (B0 + 1 + 1 + k.val)).val
      = (input_s[k.val]'k.isLt).val * magnitude { sign := input_v1_sign, bits := input_v1_bits } := by
    intro k
    have hsk : (input_s[k.val]'k.isLt).val < 2 ^ 64 := hsN k
    rw [hc k, val_mul_of_lt64 hsk hmv1lt, hmv1val]
  have hdval : ∀ k : Fin numLimbs, (env.get (B0 + 1 + 1 + numLimbs + k.val)).val
      = (env.get (B0 + 1 + 1 + k.val)).val *
        signBit { sign := input_v1_sign, bits := input_v1_bits } := by
    intro k
    rw [hd k, val_mul_bool hv1V.1]
    rfl
  have heval : ∀ k : Fin numLimbs, (env.get (B0 + 1 + 1 + numLimbs + numLimbs + k.val)).val
      = (env.get (i₀ + 1 + numLimbs + k.val)).val *
        magnitude { sign := input_v2_sign, bits := input_v2_bits } := by
    intro k
    rw [he k, val_mul_of_lt64 (hWlt k) hmv2lt, hmv2val]
  have hfval : ∀ k : Fin numLimbs,
      (env.get (B0 + 1 + 1 + numLimbs + numLimbs + numLimbs + k.val)).val
      = (env.get (B0 + 1 + 1 + numLimbs + numLimbs + k.val)).val *
        signBit { sign := input_v2_sign, bits := input_v2_bits } := by
    intro k
    rw [hf k, val_mul_bool hv2V.1]
    rfl
  have hnm1val : (env.get B0).val
      = signBit { sign := input_u1_sign, bits := input_u1_bits } *
        magnitude { sign := input_u1_sign, bits := input_u1_bits } := by
    rw [hnm1 hu1V.1, val_ite_sign hmu1val]
    rfl
  have hnm2val : (env.get (B0 + 1)).val
      = signBit { sign := input_u2_sign, bits := input_u2_bits } *
        magnitude { sign := input_u2_sign, bits := input_u2_bits } := by
    rw [hnm2 hu2V.1, val_ite_sign hmu2val]
    rfl
  -- cell bounds
  have hclt : ∀ k : Fin numLimbs, (Expression.eval env (cvar[k.val]'k.isLt)).val < 2 ^ 128 := by
    intro k
    have hk : Expression.eval env (cvar[k.val]'k.isLt) = env.get (B0 + 1 + 1 + k.val) := by
      have := hcvec k; rwa [Vector.getElem_map] at this
    rw [hk, hcval k]
    have h1 : (input_s[k.val]'k.isLt).val < 2 ^ 64 := hsN k
    have h2 := magnitude_lt hv1V
    calc (input_s[k.val]'k.isLt).val * magnitude { sign := input_v1_sign, bits := input_v1_bits }
        < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' h1 h2
      _ = 2 ^ 128 := by norm_num
  have hdlt : ∀ k : Fin numLimbs, (Expression.eval env (dvar[k.val]'k.isLt)).val < 2 ^ 128 := by
    intro k
    have hk : Expression.eval env (dvar[k.val]'k.isLt) = env.get (B0 + 1 + 1 + numLimbs + k.val) := by
      have := hdvec k; rwa [Vector.getElem_map] at this
    have hck : Expression.eval env (cvar[k.val]'k.isLt) = env.get (B0 + 1 + 1 + k.val) := by
      have := hcvec k; rwa [Vector.getElem_map] at this
    have hb := hclt k
    rw [hck] at hb
    rw [hk, hdval k]
    have : signBit { sign := input_v1_sign, bits := input_v1_bits } ≤ 1 := by
      unfold signBit; split <;> omega
    calc (env.get (B0 + 1 + 1 + k.val)).val *
          signBit { sign := input_v1_sign, bits := input_v1_bits }
        ≤ (env.get (B0 + 1 + 1 + k.val)).val * 1 := Nat.mul_le_mul_left _ this
      _ < 2 ^ 128 := by omega
  have helt : ∀ k : Fin numLimbs, (Expression.eval env (evar[k.val]'k.isLt)).val < 2 ^ 128 := by
    intro k
    have hk : Expression.eval env (evar[k.val]'k.isLt)
        = env.get (B0 + 1 + 1 + numLimbs + numLimbs + k.val) := by
      have := hevec k; rwa [Vector.getElem_map] at this
    rw [hk, heval k]
    have h1 := hWlt k
    have h2 := magnitude_lt hv2V
    calc (env.get (i₀ + 1 + numLimbs + k.val)).val *
          magnitude { sign := input_v2_sign, bits := input_v2_bits }
        < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' h1 h2
      _ = 2 ^ 128 := by norm_num
  have hflt : ∀ k : Fin numLimbs, (Expression.eval env (fvar[k.val]'k.isLt)).val < 2 ^ 128 := by
    intro k
    have hk : Expression.eval env (fvar[k.val]'k.isLt)
        = env.get (B0 + 1 + 1 + numLimbs + numLimbs + numLimbs + k.val) := by
      have := hfvec k; rwa [Vector.getElem_map] at this
    have hek : Expression.eval env (evar[k.val]'k.isLt)
        = env.get (B0 + 1 + 1 + numLimbs + numLimbs + k.val) := by
      have := hevec k; rwa [Vector.getElem_map] at this
    have hb := helt k
    rw [hek] at hb
    rw [hk, hfval k]
    have : signBit { sign := input_v2_sign, bits := input_v2_bits } ≤ 1 := by
      unfold signBit; split <;> omega
    calc (env.get (B0 + 1 + 1 + numLimbs + numLimbs + k.val)).val *
          signBit { sign := input_v2_sign, bits := input_v2_bits }
        ≤ (env.get (B0 + 1 + 1 + numLimbs + numLimbs + k.val)).val * 1 :=
          Nat.mul_le_mul_left _ this
      _ < 2 ^ 128 := by omega
  have hnm1lt : (Expression.eval env (var (F := F circomPrime) { index := B0 })).val < 2 ^ 64 := by
    show (env.get B0).val < 2 ^ 64
    rw [hnm1val]
    have h2 := magnitude_lt hu1V
    have : signBit { sign := input_u1_sign, bits := input_u1_bits } ≤ 1 := by
      unfold signBit; split <;> omega
    calc signBit { sign := input_u1_sign, bits := input_u1_bits } *
          magnitude { sign := input_u1_sign, bits := input_u1_bits }
        ≤ 1 * magnitude { sign := input_u1_sign, bits := input_u1_bits } :=
          Nat.mul_le_mul_right _ this
      _ < 2 ^ 64 := by omega
  have hnm2lt : (Expression.eval env (var (F := F circomPrime) { index := B0 + 1 })).val < 2 ^ 64 := by
    show (env.get (B0 + 1)).val < 2 ^ 64
    rw [hnm2val]
    have h2 := magnitude_lt hu2V
    have : signBit { sign := input_u2_sign, bits := input_u2_bits } ≤ 1 := by
      unfold signBit; split <;> omega
    calc signBit { sign := input_u2_sign, bits := input_u2_bits } *
          magnitude { sign := input_u2_sign, bits := input_u2_bits }
        ≤ 1 * magnitude { sign := input_u2_sign, bits := input_u2_bits } :=
          Nat.mul_le_mul_right _ this
      _ < 2 ^ 64 := by omega
  let qvar := qRelInv
    (magnitudeExpr { sign := input_var_u1_sign, bits := input_var_u1_bits })
    (magnitudeExpr { sign := input_var_u2_sign, bits := input_var_u2_bits })
    (var (F := F circomPrime) { index := B0 })
    (var (F := F circomPrime) { index := B0 + 1 }) cvar evar dvar fvar
  have hqlt : (Expression.eval env qvar).val < 2 ^ 67 := hq
  -- the grouped certificate
  have hpoly := hgrouped ⟨
    ⟨RelCells.relLhs_cap env _ _ cvar evar hmu1lt hmu2lt hclt helt,
      RelCells.relRhs_cap env _ _ qvar dvar fvar hnm1lt hnm2lt hdlt hflt hqlt⟩,
    qRelInv_linIdent env _ _ _ _ cvar evar dvar fvar⟩
  rw [RelCells.relLhs_polyValue env _ _ cvar evar hmu1lt hmu2lt hclt helt,
    RelCells.relRhs_polyValue env _ _ _ dvar fvar hnm1lt hnm2lt hdlt hflt hqlt] at hpoly
  -- the aggregate values
  have hcvalue : BigInt.value 64 (Vector.map (Expression.eval env) cvar)
      = BigInt.value 64 input_s * magnitude { sign := input_v1_sign, bits := input_v1_bits } :=
    bigIntValue_of_scaled (fun k => by rw [hcvec k, hcval k])
  have hdvalue : BigInt.value 64 (Vector.map (Expression.eval env) dvar)
      = BigInt.value 64 (Vector.map (Expression.eval env) cvar) *
        signBit { sign := input_v1_sign, bits := input_v1_bits } :=
    bigIntValue_of_scaled (fun k => by rw [hdvec k, hdval k, hcvec k])
  have hevalue : BigInt.value 64 (Vector.map (Expression.eval env) evar)
      = BigInt.value 64 (Vector.map (Expression.eval env) Wvar) *
        magnitude { sign := input_v2_sign, bits := input_v2_bits } :=
    bigIntValue_of_scaled (fun k => by rw [hevec k, heval k, hWvec k])
  have hfvalue : BigInt.value 64 (Vector.map (Expression.eval env) fvar)
      = BigInt.value 64 (Vector.map (Expression.eval env) evar) *
        signBit { sign := input_v2_sign, bits := input_v2_bits } :=
    bigIntValue_of_scaled (fun k => by rw [hfvec k, hfval k, hevec k])
  refine ⟨?_, ?_⟩
  · exact relation_of_nat_identity hu1V.1 hu2V.1 hv1V.1 hv2V.1 hWz
      hmu1val hmu2val hnm1val hnm2val hcvalue hdvalue hevalue hfvalue hpoly
  · -- the inverse row forces `|v₁| + |v₂| ≠ 0`
    have hcast : Expression.eval env
          (magnitudeExpr { sign := input_var_v1_sign, bits := input_var_v1_bits }) +
        Expression.eval env
          (magnitudeExpr { sign := input_var_v2_sign, bits := input_var_v2_bits })
        = ((magnitude { sign := input_v1_sign, bits := input_v1_bits } +
            magnitude { sign := input_v2_sign, bits := input_v2_bits } : ℕ) : F circomPrime) := by
      rw [hmv1e, hmv2e]; push_cast; ring
    rw [hcast] at hinv
    apply (magnitude_sum_ne_zero_iff hv1V hv2V).mp
    intro hz
    rw [hz, zero_mul] at hinv
    norm_num at hinv

lemma signBit_le_one (c : SignedCoeff (F circomPrime)) : signBit c ≤ 1 := by
  unfold signBit; split <;> omega

/-- The bias makes the certified integer difference non-negative, and keeps the
quotient below `2^67`. -/
lemma cert_of_relation
    {s W : Emu (F circomPrime)} {u1 u2 v1 v2 : SignedCoeff (F circomPrime)}
    (hu1V : Valid u1) (hu2V : Valid u2) (hv1V : Valid v1) (hv2V : Valid v2)
    (hsN : BigInt.Normalized limbBits s) (hWN : BigInt.Normalized limbBits W)
    (hWz : ((BigInt.value limbBits W : ℕ) : ZMod scalarOrder)
      = (eigenvalue : ZMod scalarOrder)
        * ((BigInt.value limbBits s : ℕ) : ZMod scalarOrder))
    (hrel : Relation { s := s, u1 := u1, u2 := u2, v1 := v1, v2 := v2 })
    {L R0 : ℕ}
    (hL : L = eigenvalue * magnitude u2 + magnitude u1
      + BigInt.value limbBits s * magnitude v1 + BigInt.value limbBits W * magnitude v2
      + biasKRel * scalarOrder)
    (hR0 : R0 = 2 * (eigenvalue * (signBit u2 * magnitude u2)) + 2 * (signBit u1 * magnitude u1)
      + 2 * (BigInt.value limbBits s * magnitude v1 * signBit v1)
      + 2 * (BigInt.value limbBits W * magnitude v2 * signBit v2)) :
    (L - R0) / scalarOrder < 2 ^ 67 ∧
      L = R0 + scalarOrder * ((L - R0) / scalarOrder) := by
  have hs256 : BigInt.value limbBits s < 2 ^ 256 := BigInt.value_lt hsN
  have hW256 : BigInt.value limbBits W < 2 ^ 256 := BigInt.value_lt hWN
  have hm1 := magnitude_lt hu1V
  have hm2 := magnitude_lt hu2V
  have hn1 := magnitude_lt hv1V
  have hn2 := magnitude_lt hv2V
  -- the unbiased part is below the bias
  have a1 : eigenvalue * magnitude u2 ≤ eigenvalue * 2 ^ 64 :=
    Nat.mul_le_mul_left _ (le_of_lt hm2)
  have a2 : BigInt.value limbBits s * magnitude v1 ≤ 2 ^ 256 * 2 ^ 64 :=
    Nat.mul_le_mul (le_of_lt hs256) (le_of_lt hn1)
  have a3 : BigInt.value limbBits W * magnitude v2 ≤ 2 ^ 256 * 2 ^ 64 :=
    Nat.mul_le_mul (le_of_lt hW256) (le_of_lt hn2)
  have hnum : eigenvalue * 2 ^ 64 + 2 ^ 64 + 2 ^ 256 * 2 ^ 64 + 2 ^ 256 * 2 ^ 64
      < biasKRel * scalarOrder := by decide
  have hm1' : magnitude u1 ≤ 2 ^ 64 := le_of_lt hm1
  have hXle : eigenvalue * magnitude u2 + magnitude u1
      + BigInt.value limbBits s * magnitude v1 + BigInt.value limbBits W * magnitude v2
      ≤ eigenvalue * 2 ^ 64 + 2 ^ 64 + 2 ^ 256 * 2 ^ 64 + 2 ^ 256 * 2 ^ 64 :=
    Nat.add_le_add (Nat.add_le_add (Nat.add_le_add a1 hm1') a2) a3
  have hXlt : eigenvalue * magnitude u2 + magnitude u1
      + BigInt.value limbBits s * magnitude v1 + BigInt.value limbBits W * magnitude v2
      < biasKRel * scalarOrder := lt_of_le_of_lt hXle hnum
  -- the routed halves are dominated by the full terms
  have t1 : 2 * (eigenvalue * (signBit u2 * magnitude u2)) ≤ 2 * (eigenvalue * magnitude u2) := by
    have h : signBit u2 * magnitude u2 ≤ magnitude u2 := by
      calc signBit u2 * magnitude u2 ≤ 1 * magnitude u2 :=
            Nat.mul_le_mul_right _ (signBit_le_one u2)
        _ = magnitude u2 := one_mul _
    exact Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left _ h)
  have t2 : 2 * (signBit u1 * magnitude u1) ≤ 2 * magnitude u1 := by
    have h : signBit u1 * magnitude u1 ≤ magnitude u1 := by
      calc signBit u1 * magnitude u1 ≤ 1 * magnitude u1 :=
            Nat.mul_le_mul_right _ (signBit_le_one u1)
        _ = magnitude u1 := one_mul _
    exact Nat.mul_le_mul_left 2 h
  have t3 : 2 * (BigInt.value limbBits s * magnitude v1 * signBit v1)
      ≤ 2 * (BigInt.value limbBits s * magnitude v1) := by
    have h : BigInt.value limbBits s * magnitude v1 * signBit v1
        ≤ BigInt.value limbBits s * magnitude v1 * 1 :=
      Nat.mul_le_mul_left _ (signBit_le_one v1)
    rw [Nat.mul_one] at h
    exact Nat.mul_le_mul_left 2 h
  have t4 : 2 * (BigInt.value limbBits W * magnitude v2 * signBit v2)
      ≤ 2 * (BigInt.value limbBits W * magnitude v2) := by
    have h : BigInt.value limbBits W * magnitude v2 * signBit v2
        ≤ BigInt.value limbBits W * magnitude v2 * 1 :=
      Nat.mul_le_mul_left _ (signBit_le_one v2)
    rw [Nat.mul_one] at h
    exact Nat.mul_le_mul_left 2 h
  have hR0le : R0 ≤ L := by omega
  have hLlt : L < 2 * (biasKRel * scalarOrder) := by omega
  -- the congruence certified by the relation
  have hcong := (relation_iff_congr (Wv := BigInt.value limbBits W)
    hu1V.1 hu2V.1 hv1V.1 hv2V.1 hWz).mp hrel
  have hLR : ((L : ℕ) : ZMod scalarOrder) = ((R0 : ℕ) : ZMod scalarOrder) := by
    rw [hL, hR0]
    push_cast at hcong ⊢
    have hn : ((scalarOrder : ℕ) : ZMod scalarOrder) = 0 := ZMod.natCast_self _
    rw [hn]
    linear_combination hcong
  have hmod : L % scalarOrder = R0 % scalarOrder :=
    (ZMod.natCast_eq_natCast_iff' _ _ _).mp hLR
  have hdvd : scalarOrder ∣ (L - R0) := (Nat.modEq_iff_dvd' hR0le).mp hmod.symm
  refine ⟨?_, ?_⟩
  · refine (Nat.div_lt_iff_lt_mul scalarOrder_pos).mpr ?_
    have h267 : (2:ℕ) ^ 67 * scalarOrder = 2 * (biasKRel * scalarOrder) := by decide
    rw [h267]
    omega
  · rw [Nat.mul_div_cancel' hdvd]
    omega

theorem completeness :
    FormalAssertion.Completeness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [MulModLoose.circuit, MulModLoose.Spec, MulModLooseCA.circuitWideB,
    MulModLooseCA.Spec, MulMod.AssumptionsWideB,
    NegativeMagnitude.circuit, NegativeMagnitude.Assumptions, NegativeMagnitude.Spec,
    ScaleVec.circuit, ScaleVec.Assumptions, ScaleVec.Spec,
    RangeCheck.circuit, RangeCheck.Assumptions, RangeCheck.Spec,
    GroupedEqXV.circuitNoTop, GroupedEqXV.elaboratedNoTop,
    GroupedEqXV.AssumptionsNoTop, GroupedEqXV.Assumptions, GroupedEqX.Spec,
    scalarMulModLooseWideB, main]
  obtain ⟨henv1, henv2, henv3, henv4, henv5, henv6, henv7, henv8⟩ := h_env
  set B0 : ℕ := i₀ + 1 +
      (numLimbs + numLimbs + numLimbs * (secpParams.B - 1) + numLimbs * (secpParams.B - 1) +
        GroupedEqXV.widthAllocFrom vMul.Wf (5 - 2) 0) with hB0def
  set Wvar : Var Emu (F circomPrime) :=
    Vector.mapRange numLimbs fun i => var (F := F circomPrime) { index := i₀ + 1 + numLimbs + i }
    with hWvar
  set cvar : Var Emu (F circomPrime) :=
    Vector.mapRange numLimbs fun i => var (F := F circomPrime) { index := B0 + 1 + 1 + i }
    with hcvar
  set dvar : Var Emu (F circomPrime) :=
    Vector.mapRange numLimbs fun i => var (F := F circomPrime) { index := B0 + 1 + 1 + numLimbs + i }
    with hdvar
  set evar : Var Emu (F circomPrime) :=
    Vector.mapRange numLimbs fun i =>
      var (F := F circomPrime) { index := B0 + 1 + 1 + numLimbs + numLimbs + i }
    with hevar
  set fvar : Var Emu (F circomPrime) :=
    Vector.mapRange numLimbs fun i =>
      var (F := F circomPrime) { index := B0 + 1 + 1 + numLimbs + numLimbs + numLimbs + i }
    with hfvar
  obtain ⟨hsN, hu1V, hu2V, hv1V, hv2V⟩ := h_assumptions
  -- evaluated magnitudes of the four signed coefficients
  have hmu1e := magnitudeExpr_eval env.toEnvironment { sign := input_var_u1_sign, bits := input_var_u1_bits }
  have hmu2e := magnitudeExpr_eval env.toEnvironment { sign := input_var_u2_sign, bits := input_var_u2_bits }
  have hmv1e := magnitudeExpr_eval env.toEnvironment { sign := input_var_v1_sign, bits := input_var_v1_bits }
  have hmv2e := magnitudeExpr_eval env.toEnvironment { sign := input_var_v2_sign, bits := input_var_v2_bits }
  rw [h_input.2.1.1, h_input.2.1.2] at hmu1e
  rw [h_input.2.2.1.1, h_input.2.2.1.2] at hmu2e
  rw [h_input.2.2.2.1.1, h_input.2.2.2.1.2] at hmv1e
  rw [h_input.2.2.2.2.1, h_input.2.2.2.2.2] at hmv2e
  have hmu1val : (Expression.eval env.toEnvironment
      (magnitudeExpr { sign := input_var_u1_sign, bits := input_var_u1_bits })).val
      = magnitude { sign := input_u1_sign, bits := input_u1_bits } := by
    rw [hmu1e]; exact val_natCast_magnitude hu1V
  have hmu2val : (Expression.eval env.toEnvironment
      (magnitudeExpr { sign := input_var_u2_sign, bits := input_var_u2_bits })).val
      = magnitude { sign := input_u2_sign, bits := input_u2_bits } := by
    rw [hmu2e]; exact val_natCast_magnitude hu2V
  have hmv1val : (Expression.eval env.toEnvironment
      (magnitudeExpr { sign := input_var_v1_sign, bits := input_var_v1_bits })).val
      = magnitude { sign := input_v1_sign, bits := input_v1_bits } := by
    rw [hmv1e]; exact val_natCast_magnitude hv1V
  have hmv2val : (Expression.eval env.toEnvironment
      (magnitudeExpr { sign := input_var_v2_sign, bits := input_var_v2_bits })).val
      = magnitude { sign := input_v2_sign, bits := input_v2_bits } := by
    rw [hmv2e]; exact val_natCast_magnitude hv2V
  have hmu1lt : (Expression.eval env.toEnvironment
      (magnitudeExpr { sign := input_var_u1_sign, bits := input_var_u1_bits })).val < 2 ^ 64 := by
    rw [hmu1val]; exact magnitude_lt hu1V
  have hmu2lt : (Expression.eval env.toEnvironment
      (magnitudeExpr { sign := input_var_u2_sign, bits := input_var_u2_bits })).val < 2 ^ 64 := by
    rw [hmu2val]; exact magnitude_lt hu2V
  have hmv1lt : (Expression.eval env.toEnvironment
      (magnitudeExpr { sign := input_var_v1_sign, bits := input_var_v1_bits })).val < 2 ^ 64 := by
    rw [hmv1val]; exact magnitude_lt hv1V
  have hmv2lt : (Expression.eval env.toEnvironment
      (magnitudeExpr { sign := input_var_v2_sign, bits := input_var_v2_bits })).val < 2 ^ 64 := by
    rw [hmv2val]; exact magnitude_lt hv2V
  -- the `λ·s` product
  have hWA : BigInt.Normalized secpParams.B (Vector.map (Expression.eval env.toEnvironment) eigenvalueConst) ∧
      BigInt.Normalized secpParams.B input_s ∧
      BigInt.Normalized secpParams.B (Vector.map (Expression.eval env.toEnvironment) nConst) ∧
      BigInt.value secpParams.B (Vector.map (Expression.eval env.toEnvironment) eigenvalueConst) <
        BigInt.value secpParams.B (Vector.map (Expression.eval env.toEnvironment) nConst) ∧
      0 < BigInt.value secpParams.B (Vector.map (Expression.eval env.toEnvironment) nConst) := by
    have hev : BigInt.value secpParams.B (Vector.map (Expression.eval env.toEnvironment) eigenvalueConst)
        = eigenvalue := eigenvalueConst_value env.toEnvironment
    have hnv : BigInt.value secpParams.B (Vector.map (Expression.eval env.toEnvironment) nConst)
        = scalarOrder := nConst_value env.toEnvironment
    refine ⟨eigenvalueConst_normalized env.toEnvironment, hsN, nConst_normalized env.toEnvironment, ?_, ?_⟩
    · rw [hev, hnv]; exact eigenvalue_lt_order
    · rw [hnv]; exact scalarOrder_pos
  have hev : BigInt.value secpParams.B (Vector.map (Expression.eval env.toEnvironment) eigenvalueConst)
      = eigenvalue := eigenvalueConst_value env.toEnvironment
  have hnv : BigInt.value secpParams.B (Vector.map (Expression.eval env.toEnvironment) nConst)
      = scalarOrder := nConst_value env.toEnvironment
  obtain ⟨hWN, hWmod⟩ := henv2 hWA
  rw [hnv, hev] at hWmod
  have hWz : ((BigInt.value limbBits (Vector.map (Expression.eval env.toEnvironment) Wvar) : ℕ) :
        ZMod scalarOrder)
      = (eigenvalue : ZMod scalarOrder) *
        ((BigInt.value limbBits input_s : ℕ) : ZMod scalarOrder) := by
    have h := (ZMod.natCast_eq_natCast_iff' _ _ scalarOrder).mpr hWmod
    push_cast at h
    exact h
  -- per-cell readings of the witnessed vectors
  have hWvec : ∀ k : Fin numLimbs,
      ((Vector.map (Expression.eval env.toEnvironment) Wvar)[k.val]'k.isLt) = env.get (i₀ + 1 + numLimbs + k.val) := by
    intro k
    rw [Vector.getElem_map, hWvar]
    exact eval_mapRange_var env.toEnvironment (i₀ + 1 + numLimbs) k.val k.isLt
  have hcvec : ∀ k : Fin numLimbs,
      ((Vector.map (Expression.eval env.toEnvironment) cvar)[k.val]'k.isLt) = env.get (B0 + 1 + 1 + k.val) := by
    intro k
    rw [Vector.getElem_map, hcvar]
    exact eval_mapRange_var env.toEnvironment (B0 + 1 + 1) k.val k.isLt
  have hdvec : ∀ k : Fin numLimbs,
      ((Vector.map (Expression.eval env.toEnvironment) dvar)[k.val]'k.isLt)
        = env.get (B0 + 1 + 1 + numLimbs + k.val) := by
    intro k
    rw [Vector.getElem_map, hdvar]
    exact eval_mapRange_var env.toEnvironment (B0 + 1 + 1 + numLimbs) k.val k.isLt
  have hevec : ∀ k : Fin numLimbs,
      ((Vector.map (Expression.eval env.toEnvironment) evar)[k.val]'k.isLt)
        = env.get (B0 + 1 + 1 + numLimbs + numLimbs + k.val) := by
    intro k
    rw [Vector.getElem_map, hevar]
    exact eval_mapRange_var env.toEnvironment (B0 + 1 + 1 + numLimbs + numLimbs) k.val k.isLt
  have hfvec : ∀ k : Fin numLimbs,
      ((Vector.map (Expression.eval env.toEnvironment) fvar)[k.val]'k.isLt)
        = env.get (B0 + 1 + 1 + numLimbs + numLimbs + numLimbs + k.val) := by
    intro k
    rw [Vector.getElem_map, hfvar]
    exact eval_mapRange_var env.toEnvironment (B0 + 1 + 1 + numLimbs + numLimbs + numLimbs) k.val k.isLt
  have hWlt : ∀ k : Fin numLimbs, (env.get (i₀ + 1 + numLimbs + k.val)).val < 2 ^ 64 := by
    intro k
    have h : ((Vector.map (Expression.eval env.toEnvironment) Wvar)[k.val]'k.isLt).val < 2 ^ 64 := hWN k
    rwa [hWvec k] at h
  -- cell values
  have hcval : ∀ k : Fin numLimbs, (env.get (B0 + 1 + 1 + k.val)).val
      = (input_s[k.val]'k.isLt).val * magnitude { sign := input_v1_sign, bits := input_v1_bits } := by
    intro k
    have hsk : (input_s[k.val]'k.isLt).val < 2 ^ 64 := hsN k
    rw [henv5 k, val_mul_of_lt64 hsk hmv1lt, hmv1val]
  have hdval : ∀ k : Fin numLimbs, (env.get (B0 + 1 + 1 + numLimbs + k.val)).val
      = (env.get (B0 + 1 + 1 + k.val)).val *
        signBit { sign := input_v1_sign, bits := input_v1_bits } := by
    intro k
    rw [henv6 k, val_mul_bool hv1V.1]
    rfl
  have heval : ∀ k : Fin numLimbs, (env.get (B0 + 1 + 1 + numLimbs + numLimbs + k.val)).val
      = (env.get (i₀ + 1 + numLimbs + k.val)).val *
        magnitude { sign := input_v2_sign, bits := input_v2_bits } := by
    intro k
    rw [henv7 k, val_mul_of_lt64 (hWlt k) hmv2lt, hmv2val]
  have hfval : ∀ k : Fin numLimbs,
      (env.get (B0 + 1 + 1 + numLimbs + numLimbs + numLimbs + k.val)).val
      = (env.get (B0 + 1 + 1 + numLimbs + numLimbs + k.val)).val *
        signBit { sign := input_v2_sign, bits := input_v2_bits } := by
    intro k
    rw [henv8 k, val_mul_bool hv2V.1]
    rfl
  have hnm1val : (env.get B0).val
      = signBit { sign := input_u1_sign, bits := input_u1_bits } *
        magnitude { sign := input_u1_sign, bits := input_u1_bits } := by
    rw [henv3 hu1V.1, val_ite_sign hmu1val]
    rfl
  have hnm2val : (env.get (B0 + 1)).val
      = signBit { sign := input_u2_sign, bits := input_u2_bits } *
        magnitude { sign := input_u2_sign, bits := input_u2_bits } := by
    rw [henv4 hu2V.1, val_ite_sign hmu2val]
    rfl
  -- cell bounds
  have hclt : ∀ k : Fin numLimbs, (Expression.eval env.toEnvironment (cvar[k.val]'k.isLt)).val < 2 ^ 128 := by
    intro k
    have hk : Expression.eval env.toEnvironment (cvar[k.val]'k.isLt) = env.get (B0 + 1 + 1 + k.val) := by
      have := hcvec k; rwa [Vector.getElem_map] at this
    rw [hk, hcval k]
    have h1 : (input_s[k.val]'k.isLt).val < 2 ^ 64 := hsN k
    have h2 := magnitude_lt hv1V
    calc (input_s[k.val]'k.isLt).val * magnitude { sign := input_v1_sign, bits := input_v1_bits }
        < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' h1 h2
      _ = 2 ^ 128 := by norm_num
  have hdlt : ∀ k : Fin numLimbs, (Expression.eval env.toEnvironment (dvar[k.val]'k.isLt)).val < 2 ^ 128 := by
    intro k
    have hk : Expression.eval env.toEnvironment (dvar[k.val]'k.isLt) = env.get (B0 + 1 + 1 + numLimbs + k.val) := by
      have := hdvec k; rwa [Vector.getElem_map] at this
    have hck : Expression.eval env.toEnvironment (cvar[k.val]'k.isLt) = env.get (B0 + 1 + 1 + k.val) := by
      have := hcvec k; rwa [Vector.getElem_map] at this
    have hb := hclt k
    rw [hck] at hb
    rw [hk, hdval k]
    have : signBit { sign := input_v1_sign, bits := input_v1_bits } ≤ 1 := by
      unfold signBit; split <;> omega
    calc (env.get (B0 + 1 + 1 + k.val)).val *
          signBit { sign := input_v1_sign, bits := input_v1_bits }
        ≤ (env.get (B0 + 1 + 1 + k.val)).val * 1 := Nat.mul_le_mul_left _ this
      _ < 2 ^ 128 := by omega
  have helt : ∀ k : Fin numLimbs, (Expression.eval env.toEnvironment (evar[k.val]'k.isLt)).val < 2 ^ 128 := by
    intro k
    have hk : Expression.eval env.toEnvironment (evar[k.val]'k.isLt)
        = env.get (B0 + 1 + 1 + numLimbs + numLimbs + k.val) := by
      have := hevec k; rwa [Vector.getElem_map] at this
    rw [hk, heval k]
    have h1 := hWlt k
    have h2 := magnitude_lt hv2V
    calc (env.get (i₀ + 1 + numLimbs + k.val)).val *
          magnitude { sign := input_v2_sign, bits := input_v2_bits }
        < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' h1 h2
      _ = 2 ^ 128 := by norm_num
  have hflt : ∀ k : Fin numLimbs, (Expression.eval env.toEnvironment (fvar[k.val]'k.isLt)).val < 2 ^ 128 := by
    intro k
    have hk : Expression.eval env.toEnvironment (fvar[k.val]'k.isLt)
        = env.get (B0 + 1 + 1 + numLimbs + numLimbs + numLimbs + k.val) := by
      have := hfvec k; rwa [Vector.getElem_map] at this
    have hek : Expression.eval env.toEnvironment (evar[k.val]'k.isLt)
        = env.get (B0 + 1 + 1 + numLimbs + numLimbs + k.val) := by
      have := hevec k; rwa [Vector.getElem_map] at this
    have hb := helt k
    rw [hek] at hb
    rw [hk, hfval k]
    have : signBit { sign := input_v2_sign, bits := input_v2_bits } ≤ 1 := by
      unfold signBit; split <;> omega
    calc (env.get (B0 + 1 + 1 + numLimbs + numLimbs + k.val)).val *
          signBit { sign := input_v2_sign, bits := input_v2_bits }
        ≤ (env.get (B0 + 1 + 1 + numLimbs + numLimbs + k.val)).val * 1 :=
          Nat.mul_le_mul_left _ this
      _ < 2 ^ 128 := by omega
  have hnm1lt : (Expression.eval env.toEnvironment (var (F := F circomPrime) { index := B0 })).val < 2 ^ 64 := by
    show (env.get B0).val < 2 ^ 64
    rw [hnm1val]
    have h2 := magnitude_lt hu1V
    have : signBit { sign := input_u1_sign, bits := input_u1_bits } ≤ 1 := by
      unfold signBit; split <;> omega
    calc signBit { sign := input_u1_sign, bits := input_u1_bits } *
          magnitude { sign := input_u1_sign, bits := input_u1_bits }
        ≤ 1 * magnitude { sign := input_u1_sign, bits := input_u1_bits } :=
          Nat.mul_le_mul_right _ this
      _ < 2 ^ 64 := by omega
  have hnm2lt : (Expression.eval env.toEnvironment (var (F := F circomPrime) { index := B0 + 1 })).val < 2 ^ 64 := by
    show (env.get (B0 + 1)).val < 2 ^ 64
    rw [hnm2val]
    have h2 := magnitude_lt hu2V
    have : signBit { sign := input_u2_sign, bits := input_u2_bits } ≤ 1 := by
      unfold signBit; split <;> omega
    calc signBit { sign := input_u2_sign, bits := input_u2_bits } *
          magnitude { sign := input_u2_sign, bits := input_u2_bits }
        ≤ 1 * magnitude { sign := input_u2_sign, bits := input_u2_bits } :=
          Nat.mul_le_mul_right _ this
      _ < 2 ^ 64 := by omega
  -- the aggregate values
  have hcvalue : BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) cvar)
      = BigInt.value 64 input_s * magnitude { sign := input_v1_sign, bits := input_v1_bits } :=
    bigIntValue_of_scaled (fun k => by rw [hcvec k, hcval k])
  have hdvalue : BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) dvar)
      = BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) cvar) *
        signBit { sign := input_v1_sign, bits := input_v1_bits } :=
    bigIntValue_of_scaled (fun k => by rw [hdvec k, hdval k, hcvec k])
  have hevalue : BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) evar)
      = BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) Wvar) *
        magnitude { sign := input_v2_sign, bits := input_v2_bits } :=
    bigIntValue_of_scaled (fun k => by rw [hevec k, heval k, hWvec k])
  have hfvalue : BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) fvar)
      = BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) evar) *
        signBit { sign := input_v2_sign, bits := input_v2_bits } :=
    bigIntValue_of_scaled (fun k => by rw [hfvec k, hfval k, hevec k])
  -- the certified integer identity
  have hLeq : relLhsNat env.toEnvironment
        (magnitudeExpr { sign := input_var_u1_sign, bits := input_var_u1_bits })
        (magnitudeExpr { sign := input_var_u2_sign, bits := input_var_u2_bits }) cvar evar
      = eigenvalue * magnitude { sign := input_u2_sign, bits := input_u2_bits }
        + magnitude { sign := input_u1_sign, bits := input_u1_bits }
        + BigInt.value limbBits input_s * magnitude { sign := input_v1_sign, bits := input_v1_bits }
        + BigInt.value limbBits (Vector.map (Expression.eval env.toEnvironment) Wvar) *
            magnitude { sign := input_v2_sign, bits := input_v2_bits }
        + biasKRel * scalarOrder := by
    unfold relLhsNat
    rw [hmu1val, hmu2val, hcvalue, hevalue]
  have hR0eq : relRhs0Nat env.toEnvironment (var (F := F circomPrime) { index := B0 })
        (var (F := F circomPrime) { index := B0 + 1 }) dvar fvar
      = 2 * (eigenvalue * (signBit { sign := input_u2_sign, bits := input_u2_bits } *
            magnitude { sign := input_u2_sign, bits := input_u2_bits }))
        + 2 * (signBit { sign := input_u1_sign, bits := input_u1_bits } *
            magnitude { sign := input_u1_sign, bits := input_u1_bits })
        + 2 * (BigInt.value limbBits input_s *
            magnitude { sign := input_v1_sign, bits := input_v1_bits } *
            signBit { sign := input_v1_sign, bits := input_v1_bits })
        + 2 * (BigInt.value limbBits (Vector.map (Expression.eval env.toEnvironment) Wvar) *
            magnitude { sign := input_v2_sign, bits := input_v2_bits } *
            signBit { sign := input_v2_sign, bits := input_v2_bits }) := by
    unfold relRhs0Nat
    show 2 * (eigenvalue * (env.get (B0 + 1)).val) + 2 * (env.get B0).val
        + 2 * BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) dvar)
        + 2 * BigInt.value 64 (Vector.map (Expression.eval env.toEnvironment) fvar) = _
    rw [hnm1val, hnm2val, hdvalue, hcvalue, hfvalue, hevalue]
  obtain ⟨hqbound, hidentity⟩ :=
    cert_of_relation hu1V hu2V hv1V hv2V hsN hWN hWz h_spec.1 hLeq hR0eq
  have hqsmall : qRelNat env.toEnvironment
      (magnitudeExpr { sign := input_var_u1_sign, bits := input_var_u1_bits })
      (magnitudeExpr { sign := input_var_u2_sign, bits := input_var_u2_bits })
      (var (F := F circomPrime) { index := B0 })
      (var (F := F circomPrime) { index := B0 + 1 }) cvar evar dvar fvar < 2 ^ 67 := hqbound
  let mu1v := magnitudeExpr { sign := input_var_u1_sign, bits := input_var_u1_bits }
  let mu2v := magnitudeExpr { sign := input_var_u2_sign, bits := input_var_u2_bits }
  let nm1v : Expression (F circomPrime) := var { index := B0 }
  let nm2v : Expression (F circomPrime) := var { index := B0 + 1 }
  let qvar := qRelInv mu1v mu2v nm1v nm2v cvar evar dvar fvar
  have hLfield : Expression.eval env.toEnvironment
        (MulMod.polyEvalExpr (RelCells.relLhs mu1v mu2v cvar evar)
          ((2 : F circomPrime) ^ limbBits)) =
      ((relLhsNat env.toEnvironment mu1v mu2v cvar evar : ℕ) : F circomPrime) := by
    rw [MulMod.polyEvalExpr_eval,
      ← GroupedEqXV.polyValue_eval_cast limbBits env.toEnvironment
        (RelCells.relLhs mu1v mu2v cvar evar)
        (Vector.map (Expression.eval env.toEnvironment)
          (RelCells.relLhs mu1v mu2v cvar evar)) (fun _ _ => by
            simp only [Vector.getElem_map]),
      RelCells.relLhs_polyValue env.toEnvironment mu1v mu2v cvar evar
        hmu1lt hmu2lt hclt helt]
    rfl
  have hRfield : Expression.eval env.toEnvironment
        (MulMod.polyEvalExpr (RelCells.relRhs nm1v nm2v 0 dvar fvar)
          ((2 : F circomPrime) ^ limbBits)) =
      ((relRhs0Nat env.toEnvironment nm1v nm2v dvar fvar : ℕ) : F circomPrime) := by
    rw [MulMod.polyEvalExpr_eval,
      ← GroupedEqXV.polyValue_eval_cast limbBits env.toEnvironment
        (RelCells.relRhs nm1v nm2v 0 dvar fvar)
        (Vector.map (Expression.eval env.toEnvironment)
          (RelCells.relRhs nm1v nm2v 0 dvar fvar)) (fun _ _ => by
            simp only [Vector.getElem_map]),
      RelCells.relRhs_polyValue env.toEnvironment nm1v nm2v 0 dvar fvar
        hnm1lt hnm2lt hdlt hflt (by norm_num [Expression.eval])]
    simp only [relRhs0Nat, Expression.eval, ZMod.val_zero, Nat.mul_zero, add_zero]
  have hidentityF : Expression.eval env.toEnvironment
        (MulMod.polyEvalExpr (RelCells.relLhs mu1v mu2v cvar evar)
          ((2 : F circomPrime) ^ limbBits)) =
      Expression.eval env.toEnvironment
        (MulMod.polyEvalExpr (RelCells.relRhs nm1v nm2v 0 dvar fvar)
          ((2 : F circomPrime) ^ limbBits)) +
        (((scalarOrder : ℕ) : F circomPrime)) *
          ((qRelNat env.toEnvironment mu1v mu2v nm1v nm2v cvar evar dvar fvar : ℕ) :
            F circomPrime) := by
    rw [hLfield, hRfield]
    have hcast := congrArg (fun n : ℕ => (n : F circomPrime)) hidentity
    push_cast at hcast
    simpa only [mu1v, mu2v, nm1v, nm2v, qRelNat] using hcast
  have hqfield : Expression.eval env.toEnvironment qvar =
      ((qRelNat env.toEnvironment mu1v mu2v nm1v nm2v cvar evar dvar fvar : ℕ) :
        F circomPrime) :=
    eval_qRelInv_of_identity env.toEnvironment mu1v mu2v nm1v nm2v cvar evar dvar fvar _
      hidentityF
  have hqval : (Expression.eval env.toEnvironment qvar).val
      = qRelNat env.toEnvironment
        (magnitudeExpr { sign := input_var_u1_sign, bits := input_var_u1_bits })
        (magnitudeExpr { sign := input_var_u2_sign, bits := input_var_u2_bits })
        (var (F := F circomPrime) { index := B0 })
        (var (F := F circomPrime) { index := B0 + 1 }) cvar evar dvar fvar := by
    rw [hqfield]
    exact ZMod.val_natCast_of_lt (lt_trans hqsmall (by decide))
  have hqlt : (Expression.eval env.toEnvironment qvar).val < 2 ^ 67 := by
    rw [hqval]
    exact hqsmall
  refine ⟨?_, hWA, hu1V.1, hu2V.1, hqlt,
    ⟨⟨RelCells.relLhs_cap env.toEnvironment _ _ cvar evar hmu1lt hmu2lt hclt helt,
      RelCells.relRhs_cap env.toEnvironment _ _ qvar dvar fvar hnm1lt hnm2lt hdlt hflt hqlt⟩,
      qRelInv_linIdent env.toEnvironment _ _ _ _ cvar evar dvar fvar⟩, ?_⟩
  · -- the inverse row
    have hvsumNe : Expression.eval env.toEnvironment
          (magnitudeExpr { sign := input_var_v1_sign, bits := input_var_v1_bits }) +
        Expression.eval env.toEnvironment
          (magnitudeExpr { sign := input_var_v2_sign, bits := input_var_v2_bits }) ≠ 0 := by
      rw [hmv1e, hmv2e, ← Nat.cast_add]
      exact (magnitude_sum_ne_zero_iff hv1V hv2V).2 h_spec.2
    rw [henv1, mul_inv_cancel₀ hvsumNe]
    ring
  · rw [RelCells.relLhs_polyValue env.toEnvironment _ _ cvar evar hmu1lt hmu2lt hclt helt,
      RelCells.relRhs_polyValue env.toEnvironment _ _ _ dvar fvar hnm1lt hnm2lt hdlt hflt hqlt]
    show relLhsNat env.toEnvironment
        (magnitudeExpr { sign := input_var_u1_sign, bits := input_var_u1_bits })
        (magnitudeExpr { sign := input_var_u2_sign, bits := input_var_u2_bits }) cvar evar
      = relRhs0Nat env.toEnvironment (var (F := F circomPrime) { index := B0 })
          (var (F := F circomPrime) { index := B0 + 1 }) dvar fvar
        + scalarOrder * (Expression.eval env.toEnvironment qvar).val
    rw [hqval]
    exact hidentity

def circuit : FormalAssertion (F circomPrime) Inputs where
  main
  elaborated
  Assumptions
  Spec
  soundness
  completeness

def relationCost : Count := ⟨865, 871⟩

theorem costIs_main (input : Var Inputs (F circomPrime)) :
    CostIs (main input) relationCost := by
  rw [show relationCost =
      ⟨1, 0⟩ + (⟨0, 1⟩ +
        (⟨713, 717⟩ + (⟨1, 1⟩ + (⟨1, 1⟩ +
          (⟨4, 4⟩ + (⟨4, 4⟩ + (⟨4, 4⟩ + (⟨4, 4⟩ +
            (⟨qBitsRel - 1, qBitsRel⟩ +
              ⟨GroupedEqXV.widthAllocFrom vRelL.Wf (3 - 2) 0,
               GroupedEqXV.widthConsFrom vRelL.Wf (3 - 2) 0⟩))))))))) from by decide]
  unfold main
  refine CostIs.bind (CostIs.witnessField _) fun _ => ?_
  refine CostIs.bind (CostIs.assertZero _) fun _ => ?_
  refine CostIs.bind (costIs_sub_mulModLooseWideBCA _) fun _ => ?_
  refine CostIs.bind (costIs_sub_negativeMagnitude _) fun _ => ?_
  refine CostIs.bind (costIs_sub_negativeMagnitude _) fun _ => ?_
  refine CostIs.bind (Cost.costIs_sub_scaleVec _) fun _ => ?_
  refine CostIs.bind (Cost.costIs_sub_scaleVec _) fun _ => ?_
  refine CostIs.bind (Cost.costIs_sub_scaleVec _) fun _ => ?_
  refine CostIs.bind (Cost.costIs_sub_scaleVec _) fun _ => ?_
  refine CostIs.bind
    (costIs_assertion_implicitRangeCheck qBitsRel (by decide) (by decide) _) fun _ => ?_
  exact costIs_assertion_groupedEqXVNoTop 64 gfFold posOfFold 3 vRelL vRelR hgvRel
    (by norm_num) _

theorem costIs_assertion (input : Var Inputs (F circomPrime)) :
    CostIs (assertion circuit input) relationCost :=
  CostIs.assertion (fun n => costIs_main input n)

lemma affineW_lowBits (bits : Vector (Expression (F circomPrime)) coeffBits)
    (hbits : AffineW bits) : AffineW (lowBits bits) := by
  intro i hi
  exact hbits i hi

lemma affine_magnitudeExpr (c : Var SignedCoeff (F circomPrime))
    (hbits : AffineW c.bits) : Affine (magnitudeExpr c) := by
  unfold magnitudeExpr
  exact affine_fieldFromBitsExpr (lowBits c.bits) (affineW_lowBits c.bits hbits)

lemma affine_qRelInv
    (mu1 mu2 nm1 nm2 : Expression (F circomPrime))
    (c e d f : Var Emu (F circomPrime))
    (hmu1 : Affine mu1) (hmu2 : Affine mu2)
    (hnm1 : Affine nm1) (hnm2 : Affine nm2)
    (hc : AffineW c) (he : AffineW e) (hd : AffineW d) (hf : AffineW f) :
    Affine (qRelInv mu1 mu2 nm1 nm2 c e d f) := by
  unfold qRelInv
  exact Affine.mul_fconst _ (Affine.sub
    (affine_polyEvalExpr _ _ (RelCells.affineW_relLhs mu1 mu2 c e hmu1 hmu2 hc he))
    (affine_polyEvalExpr _ _
      (RelCells.affineW_relRhs nm1 nm2 0 d f hnm1 hnm2 Affine.zero hd hf)))

attribute [local irreducible] isR1CSRow r1csProducts operationsIsR1CS flatOperationsIsR1CS

set_option maxHeartbeats 1000000 in
theorem isR1CS_main (input : Var Inputs (F circomPrime))
    (hs : AffineW input.s)
    (hu1s : Affine input.u1.sign) (hu1b : AffineW input.u1.bits)
    (hu2s : Affine input.u2.sign) (hu2b : AffineW input.u2.bits)
    (hv1s : Affine input.v1.sign) (hv1b : AffineW input.v1.bits)
    (hv2s : Affine input.v2.sign) (hv2b : AffineW input.v2.bits) :
    IsR1CSCirc (main input) := by
  unfold main
  have hvsum : Affine (magnitudeExpr input.v1 + magnitudeExpr input.v2) :=
    Affine.add (affine_magnitudeExpr input.v1 hv1b)
      (affine_magnitudeExpr input.v2 hv2b)
  refine IsR1CSCirc.bind_out (IsR1CSCirc.witnessField _) fun nInv => ?_
  refine IsR1CSCirc.bind (IsR1CSCirc.assertZero ?_) fun _ => ?_
  · simpa [sub_eq_add_neg] using
      isR1CSRow_mul_sub hvsum (Affine.var { index := nInv }) (Affine.const 1)
  refine IsR1CSCirc.bind_out
    (isR1CS_sub_mulModLooseWideBCA _ (degree_emuConst eigenvalue) hs
      (degree_emuConst scalarOrder)) fun nW => ?_
  refine IsR1CSCirc.bind_out
    (isR1CS_sub_negativeMagnitude _ hu1s (affine_magnitudeExpr input.u1 hu1b)) fun nn1 => ?_
  refine IsR1CSCirc.bind_out
    (isR1CS_sub_negativeMagnitude _ hu2s (affine_magnitudeExpr input.u2 hu2b)) fun nn2 => ?_
  refine IsR1CSCirc.bind_out
    (Cost.isR1CS_sub_scaleVec _ hs (affine_magnitudeExpr input.v1 hv1b)) fun nc => ?_
  refine IsR1CSCirc.bind_out
    (Cost.isR1CS_sub_scaleVec _ (Cost.affineW_sub_scaleVec _ nc) hv1s) fun nd => ?_
  refine IsR1CSCirc.bind_out
    (Cost.isR1CS_sub_scaleVec _ (affineW_sub_mulModLooseWideBCA _ nW)
      (affine_magnitudeExpr input.v2 hv2b)) fun ne => ?_
  refine IsR1CSCirc.bind_out
    (Cost.isR1CS_sub_scaleVec _ (Cost.affineW_sub_scaleVec _ ne) hv2s) fun nf => ?_
  let W := (subcircuit scalarMulModLooseWideB
    { a := eigenvalueConst, b := input.s, modulus := nConst }).output nW
  let nm1 := (subcircuit NegativeMagnitude.circuit
    { sign := input.u1.sign, magnitude := magnitudeExpr input.u1 }).output nn1
  let nm2 := (subcircuit NegativeMagnitude.circuit
    { sign := input.u2.sign, magnitude := magnitudeExpr input.u2 }).output nn2
  let c := (subcircuit ScaleVec.circuit
    { a := input.s, b := magnitudeExpr input.v1 }).output nc
  let d := (subcircuit ScaleVec.circuit { a := c, b := input.v1.sign }).output nd
  let e := (subcircuit ScaleVec.circuit
    { a := W, b := magnitudeExpr input.v2 }).output ne
  let f := (subcircuit ScaleVec.circuit { a := e, b := input.v2.sign }).output nf
  have hq := affine_qRelInv
    (magnitudeExpr input.u1) (magnitudeExpr input.u2) nm1 nm2 c e d f
    (affine_magnitudeExpr input.u1 hu1b) (affine_magnitudeExpr input.u2 hu2b)
    (Cost.affine_sub_negativeMagnitude _ nn1) (Cost.affine_sub_negativeMagnitude _ nn2)
    (Cost.affineW_sub_scaleVec _ nc) (Cost.affineW_sub_scaleVec _ ne)
    (Cost.affineW_sub_scaleVec _ nd) (Cost.affineW_sub_scaleVec _ nf)
  refine IsR1CSCirc.bind
    (isR1CS_assertion_implicitRangeCheck qBitsRel (by decide) (by decide) _
      hq) fun _ => ?_
  exact isR1CS_assertion_groupedEqXVNoTop 64 gfFold posOfFold 3 vRelL vRelR hgvRel
    (by norm_num) _
    (RelCells.affineW_relLhs _ _ _ _ (affine_magnitudeExpr input.u1 hu1b)
      (affine_magnitudeExpr input.u2 hu2b)
      (Cost.affineW_sub_scaleVec _ nc) (Cost.affineW_sub_scaleVec _ ne))
    (RelCells.affineW_relRhs _ _ _ _ _
      (Cost.affine_sub_negativeMagnitude _ nn1) (Cost.affine_sub_negativeMagnitude _ nn2)
      hq
      (Cost.affineW_sub_scaleVec _ nd) (Cost.affineW_sub_scaleVec _ nf))

theorem isR1CS_assertion (input : Var Inputs (F circomPrime))
    (hs : AffineW input.s)
    (hu1s : Affine input.u1.sign) (hu1b : AffineW input.u1.bits)
    (hu2s : Affine input.u2.sign) (hu2b : AffineW input.u2.bits)
    (hv1s : Affine input.v1.sign) (hv1b : AffineW input.v1.bits)
    (hv2s : Affine input.v2.sign) (hv2b : AffineW input.v2.bits) :
    IsR1CSCirc (assertion circuit input) :=
  IsR1CSCirc.assertion (fun n =>
    isR1CS_main input hs hu1s hu1b hu2s hu2b hv1s hv1b hv2s hv2b n)

end Solution.Secp256k1ScalarMul.GLVScalarRelation
