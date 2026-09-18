import Solution.Secp256k1ScalarMul.SignedCoeff
import Solution.Secp256k1ScalarMul.DivOrZeroTheorems

namespace Solution.Secp256k1ScalarMul.GLV

set_option maxRecDepth 2000

open Challenge.CostR1CS
open Solution.Secp256k1ScalarMul.Cost

@[reducible] def scalarOrder : ℕ := Specs.Secp256k1.order

@[reducible] def eigenvalue : ℕ :=
  37718080363155996902926221483475020450927657555482586988616620542887997980018

def nConst : Var Emu (F circomPrime) := emuConst scalarOrder

def eigenvalueConst : Var Emu (F circomPrime) := emuConst eigenvalue

lemma scalarOrder_pos : 0 < scalarOrder := by decide
lemma scalarOrder_lt_256 : scalarOrder < 2 ^ (limbBits * numLimbs) := by decide
lemma eigenvalue_lt_order : eigenvalue < scalarOrder := by decide
lemma coeff_bound_lt_order : 2 ^ coeffBits < scalarOrder := by decide

lemma eval_nConst (env : Environment (F circomPrime)) :
    Vector.map (Expression.eval env) nConst = emuOfNat scalarOrder :=
  DivOrZero.eval_emuConst env scalarOrder

lemma eval_eigenvalueConst (env : Environment (F circomPrime)) :
    Vector.map (Expression.eval env) eigenvalueConst = emuOfNat eigenvalue :=
  DivOrZero.eval_emuConst env eigenvalue

lemma nConst_normalized (env : Environment (F circomPrime)) :
    BigInt.Normalized limbBits (Vector.map (Expression.eval env) nConst) := by
  rw [eval_nConst]
  exact emuOfNat_normalized scalarOrder

lemma nConst_value (env : Environment (F circomPrime)) :
    BigInt.value limbBits (Vector.map (Expression.eval env) nConst) = scalarOrder := by
  rw [eval_nConst]
  exact value_emuOfNat scalarOrder_lt_256

lemma eigenvalueConst_normalized (env : Environment (F circomPrime)) :
    BigInt.Normalized limbBits
      (Vector.map (Expression.eval env) eigenvalueConst) := by
  rw [eval_eigenvalueConst]
  exact emuOfNat_normalized eigenvalue

lemma eigenvalueConst_value (env : Environment (F circomPrime)) :
    BigInt.value limbBits
      (Vector.map (Expression.eval env) eigenvalueConst) = eigenvalue := by
  rw [eval_eigenvalueConst]
  exact value_emuOfNat (lt_trans eigenvalue_lt_order scalarOrder_lt_256)

structure ResidueSum4 (F : Type) where
  t0 : Emu F
  t1 : Emu F
  t2 : Emu F
  t3 : Emu F
deriving ProvableStruct

structure CongruenceInputs (F : Type) where
  positive : ResidueSum4 F
  negative : ResidueSum4 F
deriving ProvableStruct

def residueValue (x : Emu (F circomPrime)) : ℕ := BigInt.value limbBits x

def sumValue (x : ResidueSum4 (F circomPrime)) : ℕ :=
  residueValue x.t0 + residueValue x.t1 + residueValue x.t2 + residueValue x.t3

def ResidueValid (x : Emu (F circomPrime)) : Prop :=
  x.Normalized limbBits ∧ residueValue x < scalarOrder

def ResidueSum4.Valid (x : ResidueSum4 (F circomPrime)) : Prop :=
  ResidueValid x.t0 ∧ ResidueValid x.t1 ∧
  ResidueValid x.t2 ∧ ResidueValid x.t3

def CongruenceInputs.Valid (input : CongruenceInputs (F circomPrime)) : Prop :=
  input.positive.Valid ∧ input.negative.Valid

def ResidueSum4.WValid (x : ResidueSum4 (F circomPrime)) : Prop :=
  x.t0.Normalized limbBits ∧ x.t1.Normalized limbBits ∧
  x.t2.Normalized limbBits ∧ x.t3.Normalized limbBits ∧
  sumValue x < 4 * scalarOrder

def CongruenceInputs.WValid (input : CongruenceInputs (F circomPrime)) : Prop :=
  input.positive.WValid ∧ input.negative.WValid

lemma sumValue_lt_four_order {x : ResidueSum4 (F circomPrime)}
    (h : x.Valid) : sumValue x < 4 * scalarOrder := by
  rcases h with ⟨⟨_, h0⟩, ⟨_, h1⟩, ⟨_, h2⟩, ⟨_, h3⟩⟩
  simp only [sumValue]
  omega

lemma ResidueSum4.wvalid_of_valid {x : ResidueSum4 (F circomPrime)}
    (h : x.Valid) : x.WValid :=
  ⟨h.1.1, h.2.1.1, h.2.2.1.1, h.2.2.2.1, sumValue_lt_four_order h⟩

def Congruent (input : CongruenceInputs (F circomPrime)) : Prop :=
  sumValue input.positive % scalarOrder = sumValue input.negative % scalarOrder

def quotient (input : CongruenceInputs (F circomPrime)) : ℕ :=
  (sumValue input.positive + 4 * scalarOrder - sumValue input.negative) / scalarOrder

lemma negative_le_offset {input : CongruenceInputs (F circomPrime)}
    (h : input.WValid) :
    sumValue input.negative ≤ sumValue input.positive + 4 * scalarOrder := by
  have hn := h.2.2.2.2.2
  have hp : 0 < scalarOrder := scalarOrder_pos
  omega

lemma quotient_lt_eight {input : CongruenceInputs (F circomPrime)}
    (h : input.WValid) : quotient input < 8 := by
  have hp := h.1.2.2.2.2
  have hn := h.2.2.2.2.2
  have hord := scalarOrder_pos
  simp only [quotient]
  apply Nat.div_lt_iff_lt_mul scalarOrder_pos |>.2
  omega

lemma quotient_exact {input : CongruenceInputs (F circomPrime)}
    (hvalid : input.WValid) (hcongruent : Congruent input) :
    sumValue input.positive + 4 * scalarOrder =
      sumValue input.negative + quotient input * scalarOrder := by
  let a := sumValue input.positive
  let b := sumValue input.negative
  have hb : b ≤ a + 4 * scalarOrder := by
    simpa [a, b] using negative_le_offset hvalid
  have hn : 0 < scalarOrder := scalarOrder_pos
  have hmod : (a + 4 * scalarOrder - b) % scalarOrder = 0 := by
    have habmod : a % scalarOrder = b % scalarOrder := by
      simpa [Congruent, a, b] using hcongruent
    apply Nat.sub_mod_eq_zero_of_mod_eq
    simpa [Nat.add_mod] using habmod
  have hdiv := (Nat.div_add_mod (a + 4 * scalarOrder - b) scalarOrder).symm
  rw [hmod, Nat.add_zero] at hdiv
  change a + 4 * scalarOrder =
    b + ((a + 4 * scalarOrder - b) / scalarOrder) * scalarOrder
  rw [Nat.mul_comm ((a + 4 * scalarOrder - b) / scalarOrder) scalarOrder]
  omega

def Certificate (input : CongruenceInputs (F circomPrime)) (q : ℕ) : Prop :=
  q < 8 ∧
    sumValue input.positive + 4 * scalarOrder =
      sumValue input.negative + q * scalarOrder

theorem certificate_soundness {input : CongruenceInputs (F circomPrime)} {q : ℕ}
    (h : Certificate input q) : Congruent input := by
  have heq := congrArg (fun x : ℕ => x % scalarOrder) h.2
  simpa [Certificate, Congruent, Nat.add_mod, Nat.mul_mod] using heq

theorem certificate_completeness {input : CongruenceInputs (F circomPrime)}
    (hvalid : input.WValid) (hcongruent : Congruent input) :
    Certificate input (quotient input) :=
  ⟨quotient_lt_eight hvalid, quotient_exact hvalid hcongruent⟩

def sumEqParams : EqViaCarriesN.NParams circomPrime where
  B := limbBits
  W := 6
  C := 2 ^ 68
  OFF := 17
  hB := by decide
  hW := by decide
  hB1 := by decide
  hC1 := by decide
  hOW := by decide
  hCO := by decide
  hWp := by decide

def evalResidueSum4 (env : Environment (F circomPrime))
    (x : Var ResidueSum4 (F circomPrime)) : ResidueSum4 (F circomPrime) :=
  { t0 := Vector.map (Expression.eval env) x.t0
    t1 := Vector.map (Expression.eval env) x.t1
    t2 := Vector.map (Expression.eval env) x.t2
    t3 := Vector.map (Expression.eval env) x.t3 }

def positiveCoeffs (x : Var ResidueSum4 (F circomPrime)) :
    Vector (Expression (F circomPrime)) (2 * 3 - 1) :=
  Vector.mapFinRange (2 * 3 - 1) fun k =>
    if h : k.val < numLimbs then
      x.t0[k.val]'h + x.t1[k.val]'h + x.t2[k.val]'h + x.t3[k.val]'h
        + (4 : F circomPrime) * nConst[k.val]'h
    else 0

def negativeCoeffs (x : Var ResidueSum4 (F circomPrime))
    (q : Expression (F circomPrime)) :
    Vector (Expression (F circomPrime)) (2 * 3 - 1) :=
  Vector.mapFinRange (2 * 3 - 1) fun k =>
    if h : k.val < numLimbs then
      x.t0[k.val]'h + x.t1[k.val]'h + x.t2[k.val]'h + x.t3[k.val]'h
        + q * nConst[k.val]'h
    else 0

def congruenceMain (input : Var CongruenceInputs (F circomPrime)) :
    Circuit (F circomPrime) Unit := do
  let q ← ProvableType.witness (α := field) fun env =>
    ((quotient
      { positive := evalResidueSum4 env input.positive
        negative := evalResidueSum4 env input.negative } : ℕ) : F circomPrime)
  RangeCheck.circuit 3 (by decide) (by decide) q
  EqViaCarriesN.circuit sumEqParams
    { lhs := positiveCoeffs input.positive
      rhs := negativeCoeffs input.negative q }

instance congruenceElaborated :
    ElaboratedCircuit (F circomPrime) CongruenceInputs unit congruenceMain := by
  elaborate_circuit

theorem costIs_congruenceMain (input : Var CongruenceInputs (F circomPrime)) :
    CostIs (congruenceMain input) ⟨38, 44⟩ := by
  rw [show (⟨38, 44⟩ : Count) =
      ⟨1, 0⟩ + (⟨2, 3⟩ + ⟨35, 41⟩) from by decide]
  unfold congruenceMain
  refine CostIs.bind (CostIs.provableWitness _) fun q => ?_
  refine CostIs.bind
    (costIs_assertion_implicitRangeCheck 3 (by decide) (by decide) q) fun _ => ?_
  exact costIs_assertion_eqViaCarriesN sumEqParams
    { lhs := positiveCoeffs input.positive
      rhs := negativeCoeffs input.negative q }

theorem affineW_positiveCoeffs (x : Var ResidueSum4 (F circomPrime))
    (h0 : AffineW x.t0) (h1 : AffineW x.t1)
    (h2 : AffineW x.t2) (h3 : AffineW x.t3) :
    AffineW (positiveCoeffs x) := by
  intro i hi
  rw [positiveCoeffs, Vector.getElem_mapFinRange]
  by_cases hk : i < numLimbs
  · rw [dif_pos hk]
    exact Affine.add
      (Affine.add (Affine.add (Affine.add
        (h0 i hk) (h1 i hk)) (h2 i hk)) (h3 i hk))
      (Affine.fconst_mul (4 : F circomPrime)
        (affineW_emuConst scalarOrder i hk))
  · rw [dif_neg hk]
    exact Affine.zero

theorem affineW_negativeCoeffs (x : Var ResidueSum4 (F circomPrime))
    (q : Expression (F circomPrime)) (hq : Affine q)
    (h0 : AffineW x.t0) (h1 : AffineW x.t1)
    (h2 : AffineW x.t2) (h3 : AffineW x.t3) :
    AffineW (negativeCoeffs x q) := by
  intro i hi
  rw [negativeCoeffs, Vector.getElem_mapFinRange]
  by_cases hk : i < numLimbs
  · rw [dif_pos hk]
    exact Affine.add
      (Affine.add (Affine.add (Affine.add
        (h0 i hk) (h1 i hk)) (h2 i hk)) (h3 i hk))
      (Affine.mul_deg0 hq (degree_emuConst scalarOrder i hk))
  · rw [dif_neg hk]
    exact Affine.zero

theorem isR1CS_congruenceMain (input : Var CongruenceInputs (F circomPrime))
    (hp0 : AffineW input.positive.t0) (hp1 : AffineW input.positive.t1)
    (hp2 : AffineW input.positive.t2) (hp3 : AffineW input.positive.t3)
    (hn0 : AffineW input.negative.t0) (hn1 : AffineW input.negative.t1)
    (hn2 : AffineW input.negative.t2) (hn3 : AffineW input.negative.t3) :
    IsR1CSCirc (congruenceMain input) := by
  unfold congruenceMain
  refine IsR1CSCirc.bind_out (IsR1CSCirc.provableWitness _) fun nq => ?_
  let q : Expression (F circomPrime) := Expression.var { index := nq }
  have hq : Affine q := Affine.var _
  refine IsR1CSCirc.bind
    (isR1CS_assertion_implicitRangeCheck 3 (by decide) (by decide) q hq) fun _ => ?_
  exact isR1CS_assertion_eqViaCarriesN sumEqParams
    { lhs := positiveCoeffs input.positive
      rhs := negativeCoeffs input.negative q }
    (affineW_positiveCoeffs input.positive hp0 hp1 hp2 hp3)
    (affineW_negativeCoeffs input.negative q hq hn0 hn1 hn2 hn3)

lemma eval_nConst_getElem (env : Environment (F circomPrime)) (i : ℕ)
    (hi : i < numLimbs) :
    Expression.eval env (nConst[i]'hi) =
      ((limbOfNat scalarOrder i : ℕ) : F circomPrime) := by
  exact DivOrZero.eval_emuConst_getElem env scalarOrder i hi

lemma bucketCoeff_val (env : Environment (F circomPrime))
    (x : Var ResidueSum4 (F circomPrime))
    (q : Expression (F circomPrime)) (qN : ℕ)
    (hq : Expression.eval env q = ((qN : ℕ) : F circomPrime))
    (hqN : qN ≤ 7)
    (hvalid : (evalResidueSum4 env x).WValid)
    (i : ℕ) (hi : i < numLimbs) :
    (Expression.eval env
      (x.t0[i]'hi + x.t1[i]'hi + x.t2[i]'hi + x.t3[i]'hi +
        q * nConst[i]'hi)).val =
      ((evalResidueSum4 env x).t0[i]'hi).val +
      ((evalResidueSum4 env x).t1[i]'hi).val +
      ((evalResidueSum4 env x).t2[i]'hi).val +
      ((evalResidueSum4 env x).t3[i]'hi).val +
      qN * limbOfNat scalarOrder i := by
  let xv := evalResidueSum4 env x
  let a := Expression.eval env (x.t0[i]'hi)
  let b := Expression.eval env (x.t1[i]'hi)
  let c := Expression.eval env (x.t2[i]'hi)
  let d := Expression.eval env (x.t3[i]'hi)
  let nl := limbOfNat scalarOrder i
  have ha : a.val < 2 ^ limbBits := by
    simpa only [a, xv, evalResidueSum4, Vector.getElem_map, Fin.getElem_fin] using
      hvalid.1 ⟨i, hi⟩
  have hb : b.val < 2 ^ limbBits := by
    simpa only [b, xv, evalResidueSum4, Vector.getElem_map, Fin.getElem_fin] using
      hvalid.2.1 ⟨i, hi⟩
  have hc : c.val < 2 ^ limbBits := by
    simpa only [c, xv, evalResidueSum4, Vector.getElem_map, Fin.getElem_fin] using
      hvalid.2.2.1 ⟨i, hi⟩
  have hd : d.val < 2 ^ limbBits := by
    simpa only [d, xv, evalResidueSum4, Vector.getElem_map, Fin.getElem_fin] using
      hvalid.2.2.2.1 ⟨i, hi⟩
  have hn : nl < 2 ^ limbBits := by
    exact DivOrZero.limbOfNat_lt scalarOrder i
  have htotal : a.val + b.val + c.val + d.val + qN * nl < circomPrime := by
    dsimp only [nl]
    have hmul_le : qN * limbOfNat scalarOrder i ≤
        7 * limbOfNat scalarOrder i := Nat.mul_le_mul_right _ hqN
    have hmul_lt : 7 * limbOfNat scalarOrder i < 7 * 2 ^ limbBits := by
      exact Nat.mul_lt_mul_of_pos_left hn (by decide)
    have hcap : 11 * 2 ^ limbBits < circomPrime := by decide
    omega
  simp only [Expression.eval, hq, eval_nConst_getElem env i hi,
    evalResidueSum4, Vector.getElem_map]
  change (a + b + c + d + ((qN : ℕ) : F circomPrime) *
      ((nl : ℕ) : F circomPrime)).val =
    a.val + b.val + c.val + d.val + qN * nl
  have hfield :
      a + b + c + d + ((qN : ℕ) : F circomPrime) *
          ((nl : ℕ) : F circomPrime) =
        ((a.val + b.val + c.val + d.val + qN * nl : ℕ) : F circomPrime) := by
    push_cast
    rw [ZMod.natCast_zmod_val a, ZMod.natCast_zmod_val b,
      ZMod.natCast_zmod_val c, ZMod.natCast_zmod_val d]
  rw [hfield, ZMod.val_natCast_of_lt htotal]

lemma limb_sum_scalarOrder :
    (∑ i ∈ Finset.range numLimbs,
      limbOfNat scalarOrder i * 2 ^ (limbBits * i)) = scalarOrder := by
  have h : (∑ i ∈ Finset.range numLimbs,
      limbOfNat scalarOrder i * 2 ^ (limbBits * i)) =
      ∑ i ∈ Finset.range numLimbs,
        (scalarOrder / 2 ^ (limbBits * i) % 2 ^ limbBits) *
          2 ^ (limbBits * i) := Finset.sum_congr rfl fun _ _ => rfl
  rw [h, limb_decomp_mod, Nat.mod_eq_of_lt scalarOrder_lt_256]

lemma polyValue_bucket (env : Environment (F circomPrime))
    (x : Var ResidueSum4 (F circomPrime))
    (q : Expression (F circomPrime)) (qN : ℕ)
    (hq : Expression.eval env q = ((qN : ℕ) : F circomPrime))
    (hqN : qN ≤ 7)
    (hvalid : (evalResidueSum4 env x).WValid) :
    polyValue limbBits (Vector.map (Expression.eval env)
      (Vector.mapFinRange (2 * 3 - 1) fun i =>
        if h : i.val < numLimbs then
          x.t0[i.val]'h + x.t1[i.val]'h + x.t2[i.val]'h + x.t3[i.val]'h +
            q * nConst[i.val]'h
        else 0)) =
      sumValue (evalResidueSum4 env x) + qN * scalarOrder := by
  let xv := evalResidueSum4 env x
  let cN : ℕ → ℕ := fun i =>
    if h : i < numLimbs then
      (xv.t0[i]'h).val + (xv.t1[i]'h).val +
        (xv.t2[i]'h).val + (xv.t3[i]'h).val +
        qN * limbOfNat scalarOrder i
    else 0
  have hpadded :
      polyValue limbBits (Vector.map (Expression.eval env)
        (Vector.mapFinRange (2 * 3 - 1) fun i =>
          if h : i.val < numLimbs then
            x.t0[i.val]'h + x.t1[i.val]'h + x.t2[i.val]'h + x.t3[i.val]'h +
              q * nConst[i.val]'h
          else 0)) =
        ∑ i ∈ Finset.range numLimbs, cN i * 2 ^ (limbBits * i) := by
    apply polyValue_padded limbBits env
      (fun i h => x.t0[i.val]'h + x.t1[i.val]'h + x.t2[i.val]'h +
        x.t3[i.val]'h + q * nConst[i.val]'h) cN
    intro i hi
    simp only [cN, dif_pos hi]
    simpa only [xv] using bucketCoeff_val env x q qN hq hqN hvalid i.val hi
  rw [hpadded]
  simp only [sumValue, residueValue]
  rw [value_eq_range_sum limbBits xv.t0, value_eq_range_sum limbBits xv.t1,
    value_eq_range_sum limbBits xv.t2, value_eq_range_sum limbBits xv.t3,
    ← limb_sum_scalarOrder]
  rw [Finset.mul_sum]
  repeat' rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hil : i < numLimbs := Finset.mem_range.mp hi
  simp only [cN, dif_pos hil]
  ring

lemma bucketCoeffs_bounds (env : Environment (F circomPrime))
    (x : Var ResidueSum4 (F circomPrime))
    (q : Expression (F circomPrime)) (qN : ℕ)
    (hq : Expression.eval env q = ((qN : ℕ) : F circomPrime))
    (hqN : qN ≤ 7)
    (hvalid : (evalResidueSum4 env x).WValid) :
    ∀ i : Fin (2 * 3 - 1),
      (Expression.eval env
        (if h : i.val < numLimbs then
          x.t0[i.val]'h + x.t1[i.val]'h + x.t2[i.val]'h + x.t3[i.val]'h +
            q * nConst[i.val]'h
        else 0)).val < sumEqParams.C := by
  intro i
  by_cases hi : i.val < numLimbs
  · rw [dif_pos hi, bucketCoeff_val env x q qN hq hqN hvalid i.val hi]
    have h0 := hvalid.1 ⟨i.val, hi⟩
    have h1 := hvalid.2.1 ⟨i.val, hi⟩
    have h2 := hvalid.2.2.1 ⟨i.val, hi⟩
    have h3 := hvalid.2.2.2.1 ⟨i.val, hi⟩
    simp only [Fin.getElem_fin] at h0 h1 h2 h3
    have hn := DivOrZero.limbOfNat_lt scalarOrder i.val
    have hmul_le : qN * limbOfNat scalarOrder i.val ≤
        7 * limbOfNat scalarOrder i.val := Nat.mul_le_mul_right _ hqN
    have hmul_lt : 7 * limbOfNat scalarOrder i.val < 7 * 2 ^ limbBits := by
      exact Nat.mul_lt_mul_of_pos_left hn (by decide)
    have hcap : 11 * 2 ^ limbBits < 2 ^ 68 := by decide
    simp only [sumEqParams]
    omega
  · rw [dif_neg hi]
    norm_num [Expression.eval, sumEqParams]

def CongruenceAssumptions (input : CongruenceInputs (F circomPrime)) : Prop :=
  input.WValid

def CongruenceSpec (input : CongruenceInputs (F circomPrime)) : Prop :=
  Congruent input

theorem congruenceSoundness :
    FormalAssertion.Soundness (F circomPrime) congruenceMain
      CongruenceAssumptions CongruenceSpec := by
  circuit_proof_start [RangeCheck.circuit, RangeCheck.elaborated,
    RangeCheck.main, RangeCheck.Assumptions, RangeCheck.Spec,
    EqViaCarriesN.circuit, EqViaCarriesN.elaborated,
    EqViaCarriesN.main, EqViaCarriesN.Assumptions, EqViaCarriesN.Spec,
    congruenceMain]
  let pvar : Var ResidueSum4 (F circomPrime) :=
    { t0 := input_var_positive_t0, t1 := input_var_positive_t1,
      t2 := input_var_positive_t2, t3 := input_var_positive_t3 }
  let nvar : Var ResidueSum4 (F circomPrime) :=
    { t0 := input_var_negative_t0, t1 := input_var_negative_t1,
      t2 := input_var_negative_t2, t3 := input_var_negative_t3 }
  let pv : ResidueSum4 (F circomPrime) :=
    { t0 := input_positive_t0, t1 := input_positive_t1,
      t2 := input_positive_t2, t3 := input_positive_t3 }
  let nv : ResidueSum4 (F circomPrime) :=
    { t0 := input_negative_t0, t1 := input_negative_t1,
      t2 := input_negative_t2, t3 := input_negative_t3 }
  have hpmap : evalResidueSum4 env pvar = pv := by
    unfold evalResidueSum4 pvar pv
    rw [h_input.1.1, h_input.1.2.1, h_input.1.2.2.1, h_input.1.2.2.2]
  have hnmap : evalResidueSum4 env nvar = nv := by
    unfold evalResidueSum4 nvar nv
    rw [h_input.2.1, h_input.2.2.1, h_input.2.2.2.1, h_input.2.2.2.2]
  have hvalid : pv.WValid ∧ nv.WValid := by
    simpa only [CongruenceAssumptions, CongruenceInputs.WValid, pv, nv] using h_assumptions
  have hpvalid : (evalResidueSum4 env pvar).WValid := hpmap.symm ▸ hvalid.1
  have hnvalid : (evalResidueSum4 env nvar).WValid := hnmap.symm ▸ hvalid.2
  let q : Expression (F circomPrime) := var { index := i₀ }
  let qN : ℕ := (env.get i₀).val
  have hq : Expression.eval env q = ((qN : ℕ) : F circomPrime) := by
    change env.get i₀ = (((env.get i₀).val : ℕ) : F circomPrime)
    exact (ZMod.natCast_zmod_val _).symm
  have hq_lt : qN < 8 := by simpa only [qN] using h_holds.1
  have hq_le : qN ≤ 7 := Nat.lt_succ_iff.mp hq_lt
  have hpBounds : ∀ i : Fin (2 * 3 - 1),
      (Expression.eval env (positiveCoeffs pvar)[i.val]).val < sumEqParams.C := by
    intro i
    rw [positiveCoeffs, Vector.getElem_mapFinRange]
    exact bucketCoeffs_bounds env pvar
      ((4 : F circomPrime) : Expression (F circomPrime))
        4 rfl (by decide) hpvalid i
  have hnBounds : ∀ i : Fin (2 * 3 - 1),
      (Expression.eval env (negativeCoeffs nvar q)[i.val]).val < sumEqParams.C := by
    intro i
    rw [negativeCoeffs, Vector.getElem_mapFinRange]
    exact bucketCoeffs_bounds env nvar q qN hq hq_le hnvalid i
  have heq := h_holds.2 ⟨hpBounds, hnBounds⟩
  have hpv := polyValue_bucket env pvar
    ((4 : F circomPrime) : Expression (F circomPrime)) 4 rfl (by decide) hpvalid
  have hnv := polyValue_bucket env nvar q qN hq hq_le hnvalid
  have heqValue : sumValue pv + 4 * scalarOrder =
      sumValue nv + qN * scalarOrder := by
    rw [← hpmap, ← hnmap]
    rw [← hpv, ← hnv]
    simpa only [positiveCoeffs, negativeCoeffs, q, pvar, nvar] using heq
  apply certificate_soundness (q := qN)
  exact ⟨hq_lt, heqValue⟩

theorem congruenceCompleteness :
    FormalAssertion.Completeness (F circomPrime) congruenceMain
      CongruenceAssumptions CongruenceSpec := by
  circuit_proof_start [RangeCheck.circuit, RangeCheck.elaborated,
    RangeCheck.main, RangeCheck.Assumptions, RangeCheck.Spec,
    EqViaCarriesN.circuit, EqViaCarriesN.elaborated,
    EqViaCarriesN.main, EqViaCarriesN.Assumptions, EqViaCarriesN.Spec,
    congruenceMain]
  let pvar : Var ResidueSum4 (F circomPrime) :=
    { t0 := input_var_positive_t0, t1 := input_var_positive_t1,
      t2 := input_var_positive_t2, t3 := input_var_positive_t3 }
  let nvar : Var ResidueSum4 (F circomPrime) :=
    { t0 := input_var_negative_t0, t1 := input_var_negative_t1,
      t2 := input_var_negative_t2, t3 := input_var_negative_t3 }
  let pv : ResidueSum4 (F circomPrime) :=
    { t0 := input_positive_t0, t1 := input_positive_t1,
      t2 := input_positive_t2, t3 := input_positive_t3 }
  let nv : ResidueSum4 (F circomPrime) :=
    { t0 := input_negative_t0, t1 := input_negative_t1,
      t2 := input_negative_t2, t3 := input_negative_t3 }
  have hpmap : evalResidueSum4 env.toEnvironment pvar = pv := by
    unfold evalResidueSum4 pvar pv
    rw [h_input.1.1, h_input.1.2.1, h_input.1.2.2.1, h_input.1.2.2.2]
  have hnmap : evalResidueSum4 env.toEnvironment nvar = nv := by
    unfold evalResidueSum4 nvar nv
    rw [h_input.2.1, h_input.2.2.1, h_input.2.2.2.1, h_input.2.2.2.2]
  have hvalid : pv.WValid ∧ nv.WValid := by
    simpa only [CongruenceAssumptions, CongruenceInputs.WValid, pv, nv] using h_assumptions
  have hpvalid : (evalResidueSum4 env.toEnvironment pvar).WValid := hpmap.symm ▸ hvalid.1
  have hnvalid : (evalResidueSum4 env.toEnvironment nvar).WValid := hnmap.symm ▸ hvalid.2
  let ci : CongruenceInputs (F circomPrime) :=
    { positive := evalResidueSum4 env.toEnvironment pvar
      negative := evalResidueSum4 env.toEnvironment nvar }
  have hcvalid : ci.WValid := ⟨hpvalid, hnvalid⟩
  have hcongruent : Congruent ci := by
    rw [show ci = { positive := pv, negative := nv } from by
      simp only [ci, hpmap, hnmap]]
    simpa only [CongruenceSpec, pv, nv] using h_spec
  let qN : ℕ := quotient ci
  let q : Expression (F circomPrime) := var { index := i₀ }
  have hq : Expression.eval env.toEnvironment q = ((qN : ℕ) : F circomPrime) := by
    change env.get i₀ = ((qN : ℕ) : F circomPrime)
    simpa only [qN, ci, pvar, nvar] using h_env
  have hcert : Certificate ci qN := by
    exact certificate_completeness hcvalid hcongruent
  have hq_le : qN ≤ 7 := Nat.lt_succ_iff.mp hcert.1
  have hpBounds : ∀ i : Fin (2 * 3 - 1),
      (Expression.eval env.toEnvironment (positiveCoeffs pvar)[i.val]).val <
        sumEqParams.C := by
    intro i
    rw [positiveCoeffs, Vector.getElem_mapFinRange]
    exact bucketCoeffs_bounds env.toEnvironment pvar
      ((4 : F circomPrime) : Expression (F circomPrime))
        4 rfl (by decide) hpvalid i
  have hnBounds : ∀ i : Fin (2 * 3 - 1),
      (Expression.eval env.toEnvironment (negativeCoeffs nvar q)[i.val]).val <
        sumEqParams.C := by
    intro i
    rw [negativeCoeffs, Vector.getElem_mapFinRange]
    exact bucketCoeffs_bounds env.toEnvironment nvar q qN hq hq_le hnvalid i
  have hpv := polyValue_bucket env.toEnvironment pvar
    ((4 : F circomPrime) : Expression (F circomPrime)) 4 rfl (by decide) hpvalid
  have hnv := polyValue_bucket env.toEnvironment nvar q qN hq hq_le hnvalid
  have heqPoly :
      polyValue limbBits
          (Vector.map (Expression.eval env.toEnvironment) (positiveCoeffs pvar)) =
        polyValue limbBits
          (Vector.map (Expression.eval env.toEnvironment) (negativeCoeffs nvar q)) := by
    simpa only [positiveCoeffs, negativeCoeffs] using hpv.trans (hcert.2.trans hnv.symm)
  refine ⟨?_, ⟨⟨hpBounds, hnBounds⟩, ?_⟩⟩
  · rw [h_env]
    exact ZMod.val_natCast_of_lt (lt_trans hcert.1 (by decide : 8 < circomPrime)) ▸ hcert.1
  · simpa only [sumEqParams, pvar, nvar, q] using heqPoly

def congruenceCircuit : FormalAssertion (F circomPrime) CongruenceInputs where
  main := congruenceMain
  elaborated := congruenceElaborated
  Assumptions := CongruenceAssumptions
  Spec := CongruenceSpec
  soundness := congruenceSoundness
  completeness := congruenceCompleteness

end Solution.Secp256k1ScalarMul.GLV
