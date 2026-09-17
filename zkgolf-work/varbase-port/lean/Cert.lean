import Solution.Secp256k1ScalarMul.Lazy.Bounds

/-!
# Zero-row certificate `L + R·U ≡ 0 (mod q)` for the variable-base layouts

Port of `Sparse32Cert` from the fixed-base record (patchgravity, d59c8bf7)
over `VarLayout`: two implicit range checks on affine expressions, no
allocated product rows.
-/

namespace Solution.Secp256k1ScalarMulFixedBase.LazyVar.Cert

open Solution.Secp256k1ScalarMul.Lazy
open Challenge.CostR1CS
open Challenge.Utils.ComputableWitnessLemmas

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

abbrev Field := SmallSquare.Field


def Assumptions (l : VarLayout) (i : fields 2 Field) : Prop :=
  (loMin l ≤ LazyX.lift (i[0]'(by decide)) ∧ LazyX.lift (i[0]'(by decide)) ≤ loMax l) ∧
  (hiMin l ≤ LazyX.lift (i[1]'(by decide)) ∧ LazyX.lift (i[1]'(by decide)) ≤ hiMax l)

def Spec (i : fields 2 Field) : Prop :=
  Sparse32.q ∣ LazyX.lift (i[0]'(by decide)) + Sparse32.R * LazyX.lift (i[1]'(by decide))

def rawQ (i : fields 2 Field) : Field :=
  (Sparse32.q : Field)⁻¹ * ((i[0]'(by decide)) + (Sparse32.R : Field) * (i[1]'(by decide)))
def qValue (l : VarLayout) (i : fields 2 Field) : Field := rawQ i - (kmin l : Field)
def vValue (l : VarLayout) (i : fields 2 Field) : Field :=
  (Sparse32.R : Field)⁻¹ * ((i[0]'(by decide)) - ((Sparse32.R-Sparse32.c : ℤ) : Field) * rawQ i) - (tmin l : Field)

def rawQExpr (i : Var (fields 2) Field) : Expression Field :=
  (Sparse32.q : Field)⁻¹ * ((i[0]'(by decide)) + (Sparse32.R : Field) * (i[1]'(by decide)))
def qExpr (l : VarLayout) (i : Var (fields 2) Field) : Expression Field :=
  rawQExpr i - (kmin l : Field)
def vExpr (l : VarLayout) (i : Var (fields 2) Field) : Expression Field :=
  (Sparse32.R : Field)⁻¹ * ((i[0]'(by decide)) - ((Sparse32.R-Sparse32.c : ℤ) : Field) * rawQExpr i) -
    (tmin l : Field)

def main (l : VarLayout) (i : Var (fields 2) Field) : Circuit Field Unit := do
  assertion (RangeCheck.circuit (qbits l) (qbits_valid l) (qbits_pos l)) (qExpr l i)
  assertion (RangeCheck.circuit (tbits l) (tbits_valid l) (tbits_pos l)) (vExpr l i)

instance elaborated (l : VarLayout) : ElaboratedCircuit Field (fields 2) unit (main l) := by
  elaborate_circuit

lemma values_sound (l : VarLayout) (i : fields 2 Field) (h : Assumptions l i)
    (hk : (qValue l i).val < 2 ^ qbits l) (hv : (vValue l i).val < 2 ^ tbits l) :
    Spec i := by
  have hn :
      (i[0]'(by decide)) - ((Sparse32.R-Sparse32.c : ℤ) : Field) * rawQ i -
          (Sparse32.R : Field) * ((Sparse32.R : Field)⁻¹ *
            ((i[0]'(by decide)) - ((Sparse32.R-Sparse32.c : ℤ) : Field) * rawQ i)) = 0 ∧
        (i[1]'(by decide)) - ((Sparse32.R-1 : ℤ) : Field) * rawQ i +
          (Sparse32.R : Field)⁻¹ *
            ((i[0]'(by decide)) - ((Sparse32.R-Sparse32.c : ℤ) : Field) * rawQ i) = 0 := by
    simpa only [rawQ, Sparse32.q,
      Sparse32.R, Sparse32.c,
      SmallSquare.q, SmallSquare.R,
      SmallSquare.c] using
        SmallCert.native (i[0]'(by decide)) (i[1]'(by decide))
  simp only [rawQ] at hn
  have h0 :
      ((LazyX.lift (i[0]'(by decide)) - (Sparse32.R-Sparse32.c) * ((qValue l i).val + kmin l) -
        Sparse32.R * ((vValue l i).val + tmin l) : ℤ) : Field) = 0 := by
    push_cast
    simp only [LazyX.cast_lift, FoldQuot.natCast_val_F, qValue,
      vValue, rawQ]
    push_cast at hn ⊢
    linear_combination hn.1
  have h1 :
      ((LazyX.lift (i[1]'(by decide)) - (Sparse32.R-1) * ((qValue l i).val + kmin l) +
        ((vValue l i).val + tmin l) : ℤ) : Field) = 0 := by
    push_cast
    simp only [LazyX.cast_lift, FoldQuot.natCast_val_F, qValue,
      vValue, rawQ]
    push_cast at hn ⊢
    linear_combination hn.2
  have he := certificate_sound l
    (LazyX.lift (i[0]'(by decide))) (LazyX.lift (i[1]'(by decide)))
    (qValue l i).val (vValue l i).val h.1 h.2
    ⟨by omega, by exact_mod_cast hk⟩ ⟨by omega, by exact_mod_cast hv⟩ h0 h1
  exact ⟨(qValue l i).val + kmin l, he⟩

lemma values_complete (l : VarLayout) (i : fields 2 Field) (h : Assumptions l i)
    (hs : Spec i) :
    (qValue l i).val < 2 ^ qbits l ∧ (vValue l i).val < 2 ^ tbits l := by
  obtain ⟨k, hk⟩ := hs
  have hb := certificate_complete l
    (LazyX.lift (i[0]'(by decide))) (LazyX.lift (i[1]'(by decide))) k h.1 h.2 hk
  have he := congrArg (fun z : ℤ => (z : Field)) hk
  push_cast at he
  simp only [LazyX.cast_lift] at he
  have hq : rawQ i = (k : Field) := by
    unfold rawQ
    rw [he, ← mul_assoc]
    have hqn : (Sparse32.q : Field) ≠ 0 := by decide
    rw [inv_mul_cancel₀ hqn, one_mul]
  have hqv : qValue l i = ((k-kmin l : ℤ) : Field) := by
    simp only [qValue, hq, Int.cast_sub]
  have hn := (SmallCert.native (i[0]'(by decide)) (i[1]'(by decide))).2
  change (i[1]'(by decide)) - ((Sparse32.R-1 : ℤ) : Field) * rawQ i +
    (Sparse32.R : Field)⁻¹ * ((i[0]'(by decide)) - ((Sparse32.R-Sparse32.c : ℤ) : Field) * rawQ i) = 0 at hn
  rw [hq] at hn
  have hvv :
      vValue l i = (((Sparse32.R-1)*k-LazyX.lift (i[1]'(by decide))-tmin l : ℤ) : Field) := by
    unfold vValue
    rw [hq]
    push_cast at hn ⊢
    rw [LazyX.cast_lift]
    linear_combination hn
  constructor
  · rw [hqv]
    exact AffineNarrow.range_of_int _ _ hb.1 (qbits_valid l)
  · rw [hvv]
    exact AffineNarrow.range_of_int _ _ hb.2 (tbits_valid l)

lemma eval_expr (l : VarLayout) (env : Environment Field) (i : Var (fields 2) Field) :
    Expression.eval env (qExpr l i) = qValue l (eval env i) ∧
    Expression.eval env (vExpr l i) = vValue l (eval env i) := by
  simp only [qExpr, vExpr, rawQExpr, qValue, vValue, rawQ, Expression.eval,
    circuit_norm, neg_one_mul, sub_eq_add_neg, and_self]

theorem soundness (l : VarLayout) :
    FormalAssertion.Soundness Field (main l) (Assumptions l) Spec := by
  circuit_proof_start_core
  have he := eval_expr l env input_var
  rw [h_input] at he
  simp only [main, circuit_norm, RangeCheck.circuit, RangeCheck.Assumptions,
    RangeCheck.Spec] at h_holds ⊢
  exact values_sound l input h_assumptions
    (by simpa only [he.1] using h_holds.1) (by simpa only [he.2] using h_holds.2)

theorem completeness (l : VarLayout) :
    FormalAssertion.Completeness Field (main l) (Assumptions l) Spec := by
  circuit_proof_start_core
  have he := eval_expr l env.toEnvironment input_var
  have hi : eval env.toEnvironment input_var = input := by
    simpa only [circuit_norm] using h_input
  rw [hi] at he
  have hv := values_complete l input h_assumptions h_spec
  simp only [main, circuit_norm, RangeCheck.circuit, RangeCheck.Assumptions, RangeCheck.Spec]
  exact ⟨by simpa only [he.1] using hv.1, by simpa only [he.2] using hv.2⟩

def circuit (l : VarLayout) : FormalAssertion Field (fields 2) where
  main := main l
  Assumptions := Assumptions l
  Spec := Spec
  soundness := soundness l
  completeness := completeness l

theorem cost (l : VarLayout) (i : Var (fields 2) Field) :
    CostIs (main l i) ⟨qbits l+tbits l-2, qbits l+tbits l⟩ := by
  rw [show (⟨qbits l+tbits l-2, qbits l+tbits l⟩ : Count) =
    ⟨qbits l-1, qbits l⟩ + ⟨tbits l-1, tbits l⟩ by
      cases l <;> decide]
  unfold main
  refine CostIs.bind
    (Cost.costIs_assertion_implicitRangeCheck _ _ _ _) fun _ => ?_
  exact Cost.costIs_assertion_implicitRangeCheck _ _ _ _

lemma affine_expr (l : VarLayout) (i : Var (fields 2) Field) (hi : AffineW i) :
    Affine (qExpr l i) ∧ Affine (vExpr l i) := by
  have hq : Affine (rawQExpr i) :=
    Affine.fconst_mul _
      (Affine.add (hi _ (by decide)) (Affine.fconst_mul _ (hi _ (by decide))))
  exact ⟨Affine.sub hq (Affine.const _),
    Affine.sub
      (Affine.fconst_mul _ (Affine.sub (hi _ (by decide)) (Affine.fconst_mul _ hq)))
      (Affine.const _)⟩

theorem shape (l : VarLayout) (i : Var (fields 2) Field) (hi : AffineW i) :
    IsR1CSCirc (main l i) := by
  have h := affine_expr l i hi
  unfold main
  refine IsR1CSCirc.bind
    (Cost.isR1CS_assertion_implicitRangeCheck _ _ _ _ h.1)
    fun _ => ?_
  exact Cost.isR1CS_assertion_implicitRangeCheck _ _ _ _ h.2

lemma expr_stable (l : VarLayout) (i : Var (fields 2) Field)
    {e e' : ProverEnvironment Field} (h : eval e i = eval e' i) :
    eval e (qExpr l i) = eval e' (qExpr l i) ∧
      eval e (vExpr l i) = eval e' (vExpr l i) := by
  have h' : eval e.toEnvironment i = eval e'.toEnvironment i := by
    simpa only [circuit_norm] using h
  simpa only [circuit_norm, (eval_expr l e.toEnvironment i).1,
    (eval_expr l e'.toEnvironment i).1, (eval_expr l e.toEnvironment i).2,
    (eval_expr l e'.toEnvironment i).2, h']

theorem computableWitnesses (l : VarLayout) : (circuit l).ComputableWitnesses := by
  intro n input env env'
  change Operations.forAllFlat n (FormalCircuitBase.computableWitnessCondition input env env')
    ((main l input).operations n)
  apply FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  simp only [main, Circuit.bind_structuralComputableWitnesses_iff]
  constructor
  · exact CWHelpers.assertion_structuralComputableWitnesses_of_condition
      (RangeCheck.circuit (qbits l) (qbits_valid l) (qbits_pos l))
      input _ _ (fun _ _ _ _ _ h => (expr_stable l input h).1)
      (RangeCheck.computableWitnesses _ _ _) env env'
  · exact CWHelpers.assertion_structuralComputableWitnesses_of_condition
      (RangeCheck.circuit (tbits l) (tbits_valid l) (tbits_pos l))
      input _ _ (fun _ _ _ _ _ h => (expr_stable l input h).2)
      (RangeCheck.computableWitnesses _ _ _) env env'

/-- Integer-valued halves inside the layout satisfy the assumptions, and the
specification is divisibility of the integer value. -/
lemma model (l : VarLayout) (i : fields 2 Field) (L H : ℤ)
    (hL : loMin l ≤ L ∧ L ≤ loMax l)
    (hH : hiMin l ≤ H ∧ H ≤ hiMax l)
    (hl : (i[0]'(by decide)) = (L : Field))
    (hh : (i[1]'(by decide)) = (H : Field)) :
    Assumptions l i ∧ (Spec i ↔ Sparse32.q ∣ L+Sparse32.R*H) := by
  have he := endpoints_centered l
  have hhalf : Sparse32.nativeHalf = LazyX.nativeHalf := by
    norm_num [Sparse32.nativeHalf,
      Sparse32.nativePrime, LazyX.nativeHalf]
  have hlift : LazyX.lift (i[0]'(by decide)) = L := by
    rw [hl]
    apply LazyX.lift_cast
    rw [← hhalf]
    omega
  have hlifth : LazyX.lift (i[1]'(by decide)) = H := by
    rw [hh]
    apply LazyX.lift_cast
    rw [← hhalf]
    omega
  simp only [Assumptions, Spec, hlift, hlifth]
  exact ⟨⟨hL, hH⟩, trivial⟩

lemma localLength (l : VarLayout) (i : Var (fields 2) Field) (o : ℕ) :
    (main l i).localLength o = qbits l + tbits l - 2 := by
  simp only [main, RangeCheck.circuit, circuit_norm]
  cases l <;> decide

end Solution.Secp256k1ScalarMulFixedBase.LazyVar.Cert
