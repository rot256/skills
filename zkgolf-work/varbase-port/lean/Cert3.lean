import Solution.Secp256k1ScalarMul.Lazy.Cert

/-!
# Three-limb zero-row certificate for the unified slope relation

The unified relation `a (y + T.y) − (x² + x T.x + T.x²)` has coefficients of
about 171 bits, too wide for the two-half certificate (its residual would pass
the native prime).  Splitting the eight coefficients as `L0 + 2^96 L1 + 2^192 L2`
and carrying twice keeps every native residual below 2^240.  The quotient and
the two carries are affine in the limbs, so the certificate is still three
implicit range checks and no product rows (same idea as patchgravity's
`Sparse32Cert`, d59c8bf7).
-/

namespace Solution.Secp256k1ScalarMulFixedBase.LazyVar.Cert3

open Solution.Secp256k1ScalarMul.Lazy
open Challenge.CostR1CS
open Challenge.Utils.ComputableWitnessLemmas

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

abbrev Field := SmallSquare.Field

def Assumptions (i : fields 3 Field) : Prop :=
  (l0Min ≤ LazyX.lift (i[0]'(by decide)) ∧ LazyX.lift (i[0]'(by decide)) ≤ l0Max) ∧
  (l1Min ≤ LazyX.lift (i[1]'(by decide)) ∧ LazyX.lift (i[1]'(by decide)) ≤ l1Max) ∧
  (l2Min ≤ LazyX.lift (i[2]'(by decide)) ∧ LazyX.lift (i[2]'(by decide)) ≤ l2Max)

def Spec (i : fields 3 Field) : Prop :=
  Sparse32.q ∣ LazyX.lift (i[0]'(by decide)) + W96 * LazyX.lift (i[1]'(by decide)) +
    W192 * LazyX.lift (i[2]'(by decide))

def rawK (i : fields 3 Field) : Field :=
  (Sparse32.q : Field)⁻¹ *
    ((i[0]'(by decide)) + (W96 : Field) * (i[1]'(by decide)) + (W192 : Field) * (i[2]'(by decide)))
def rawT0 (i : fields 3 Field) : Field :=
  (W96 : Field)⁻¹ * ((i[0]'(by decide)) + (Sparse32.c : Field) * rawK i)
def rawT1 (i : fields 3 Field) : Field :=
  (W96 : Field)⁻¹ * ((i[1]'(by decide)) + rawT0 i)
def kValue (i : fields 3 Field) : Field := rawK i - (ukmin : Field)
def t0Value (i : fields 3 Field) : Field := rawT0 i - (ut0min : Field)
def t1Value (i : fields 3 Field) : Field := rawT1 i - (ut1min : Field)

def rawKExpr (i : Var (fields 3) Field) : Expression Field :=
  (Sparse32.q : Field)⁻¹ *
    ((i[0]'(by decide)) + (W96 : Field) * (i[1]'(by decide)) + (W192 : Field) * (i[2]'(by decide)))
def rawT0Expr (i : Var (fields 3) Field) : Expression Field :=
  (W96 : Field)⁻¹ * ((i[0]'(by decide)) + (Sparse32.c : Field) * rawKExpr i)
def rawT1Expr (i : Var (fields 3) Field) : Expression Field :=
  (W96 : Field)⁻¹ * ((i[1]'(by decide)) + rawT0Expr i)
def kExpr (i : Var (fields 3) Field) : Expression Field := rawKExpr i - (ukmin : Field)
def t0Expr (i : Var (fields 3) Field) : Expression Field := rawT0Expr i - (ut0min : Field)
def t1Expr (i : Var (fields 3) Field) : Expression Field := rawT1Expr i - (ut1min : Field)

def main (i : Var (fields 3) Field) : Circuit Field Unit := do
  assertion (RangeCheck.circuit ukbits ukbits_valid ukbits_pos) (kExpr i)
  assertion (RangeCheck.circuit ut0bits ut0bits_valid ut0bits_pos) (t0Expr i)
  assertion (RangeCheck.circuit ut1bits ut1bits_valid ut1bits_pos) (t1Expr i)

instance elaborated : ElaboratedCircuit Field (fields 3) unit main := by
  elaborate_circuit

lemma q_ne : (Sparse32.q : Field) ≠ 0 := by decide
lemma w96_ne : (W96 : Field) ≠ 0 := by decide
lemma w192_ne : (W192 : Field) ≠ 0 := by decide

/-- The three native carry identities hold by construction of the raw values. -/
lemma native (i : fields 3 Field) :
    (i[0]'(by decide)) + (Sparse32.c : Field) * rawK i - (W96 : Field) * rawT0 i = 0 ∧
    (i[1]'(by decide)) + rawT0 i - (W96 : Field) * rawT1 i = 0 ∧
    (i[2]'(by decide)) + rawT1 i - (W64 : Field) * rawK i = 0 := by
  have hq : (Sparse32.q : Field) = (W192 : Field) * (W64 : Field) - (Sparse32.c : Field) := by
    norm_num [Sparse32.q, Sparse32.c, W192, W64]
  have h192 : (W192 : Field) = (W96 : Field) * (W96 : Field) := by norm_num [W192, W96]
  refine ⟨?_, ?_, ?_⟩
  · unfold rawT0
    rw [mul_inv_cancel_left₀ w96_ne]
    ring
  · unfold rawT1
    rw [mul_inv_cancel_left₀ w96_ne]
    ring
  · have hk : (Sparse32.q : Field) * rawK i =
        (i[0]'(by decide)) + (W96 : Field) * (i[1]'(by decide)) + (W192 : Field) * (i[2]'(by decide)) := by
      unfold rawK; rw [mul_inv_cancel_left₀ q_ne]
    have ht0 : (W96 : Field) * rawT0 i = (i[0]'(by decide)) + (Sparse32.c : Field) * rawK i := by
      unfold rawT0; rw [mul_inv_cancel_left₀ w96_ne]
    have ht1 : (W96 : Field) * rawT1 i = (i[1]'(by decide)) + rawT0 i := by
      unfold rawT1; rw [mul_inv_cancel_left₀ w96_ne]
    have hz : (W192 : Field) * ((i[2]'(by decide)) + rawT1 i - (W64 : Field) * rawK i) = 0 := by
      linear_combination (W96 : Field) * ht1 + ht0 - hk + rawK i * hq +
        rawT1 i * h192
    rcases mul_eq_zero.mp hz with h | h
    · exact absurd h w192_ne
    · exact h

lemma values_sound (i : fields 3 Field) (h : Assumptions i)
    (hk : (kValue i).val < 2 ^ ukbits) (h0 : (t0Value i).val < 2 ^ ut0bits)
    (h1 : (t1Value i).val < 2 ^ ut1bits) :
    Spec i := by
  have hn := native i
  have e0 : ((ures0 (LazyX.lift (i[0]'(by decide))) (kValue i).val (t0Value i).val : ℤ) : Field)
      = 0 := by
    simp only [ures0]
    push_cast
    simp only [LazyX.cast_lift, FoldQuot.natCast_val_F, kValue, t0Value]
    linear_combination hn.1
  have e1 : ((ures1 (LazyX.lift (i[1]'(by decide))) (t0Value i).val (t1Value i).val : ℤ) : Field)
      = 0 := by
    simp only [ures1]
    push_cast
    simp only [LazyX.cast_lift, FoldQuot.natCast_val_F, t0Value, t1Value]
    linear_combination hn.2.1
  have e2 : ((ures2 (LazyX.lift (i[2]'(by decide))) (t1Value i).val (kValue i).val : ℤ) : Field)
      = 0 := by
    simp only [ures2]
    push_cast
    simp only [LazyX.cast_lift, FoldQuot.natCast_val_F, t1Value, kValue]
    linear_combination hn.2.2
  have he := uni_sound (LazyX.lift (i[0]'(by decide))) (LazyX.lift (i[1]'(by decide)))
    (LazyX.lift (i[2]'(by decide))) (kValue i).val (t0Value i).val (t1Value i).val
    h.1 h.2.1 h.2.2 ⟨by omega, by exact_mod_cast hk⟩ ⟨by omega, by exact_mod_cast h0⟩
    ⟨by omega, by exact_mod_cast h1⟩ e0 e1 e2
  exact ⟨(kValue i).val + ukmin, he⟩

lemma values_complete (i : fields 3 Field) (h : Assumptions i) (hs : Spec i) :
    (kValue i).val < 2 ^ ukbits ∧ (t0Value i).val < 2 ^ ut0bits ∧
      (t1Value i).val < 2 ^ ut1bits := by
  obtain ⟨k, hk⟩ := hs
  set L0 := LazyX.lift (i[0]'(by decide)) with hL0
  set L1 := LazyX.lift (i[1]'(by decide)) with hL1
  set L2 := LazyX.lift (i[2]'(by decide)) with hL2
  have hb := uni_complete L0 L1 L2 k h.1 h.2.1 h.2.2 hk
  obtain ⟨hbk, hbt0, hbt1, hd0, hd1, hl2⟩ := hb
  -- integer carries
  set T0 : ℤ := (L0 + Sparse32.c * k) / W96 with hT0
  set T1 : ℤ := (L1 + T0) / W96 with hT1
  have hT0e : L0 + Sparse32.c * k = W96 * T0 := by
    have := Int.ediv_add_emod (L0 + Sparse32.c * k) W96
    rw [hd0, add_zero] at this
    linear_combination -this
  have hT1e : L1 + T0 = W96 * T1 := by
    have := Int.ediv_add_emod (L1 + T0) W96
    rw [hd1, add_zero] at this
    linear_combination -this
  have hi0 : (i[0]'(by decide)) = (L0 : Field) := by rw [hL0, LazyX.cast_lift]
  have hi1 : (i[1]'(by decide)) = (L1 : Field) := by rw [hL1, LazyX.cast_lift]
  have hi2 : (i[2]'(by decide)) = (L2 : Field) := by rw [hL2, LazyX.cast_lift]
  have hrawK : rawK i = (k : Field) := by
    unfold rawK
    rw [hi0, hi1, hi2]
    have : ((L0 + W96 * L1 + W192 * L2 : ℤ) : Field) = ((Sparse32.q * k : ℤ) : Field) := by
      rw [hk]
    push_cast at this
    rw [this, ← mul_assoc, inv_mul_cancel₀ q_ne, one_mul]
  have hrawT0 : rawT0 i = (T0 : Field) := by
    unfold rawT0
    rw [hi0, hrawK]
    have : ((L0 + Sparse32.c * k : ℤ) : Field) = ((W96 * T0 : ℤ) : Field) := by rw [hT0e]
    push_cast at this
    rw [this, ← mul_assoc, inv_mul_cancel₀ w96_ne, one_mul]
  have hrawT1 : rawT1 i = (T1 : Field) := by
    unfold rawT1
    rw [hi1, hrawT0]
    have : ((L1 + T0 : ℤ) : Field) = ((W96 * T1 : ℤ) : Field) := by rw [hT1e]
    push_cast at this
    rw [this, ← mul_assoc, inv_mul_cancel₀ w96_ne, one_mul]
  refine ⟨?_, ?_, ?_⟩
  · rw [show kValue i = ((k - ukmin : ℤ) : Field) by simp only [kValue, hrawK, Int.cast_sub]]
    exact AffineNarrow.range_of_int _ _ hbk ukbits_valid
  · rw [show t0Value i = ((T0 - ut0min : ℤ) : Field) by
      simp only [t0Value, hrawT0, Int.cast_sub]]
    exact AffineNarrow.range_of_int _ _ hbt0 ut0bits_valid
  · rw [show t1Value i = ((T1 - ut1min : ℤ) : Field) by
      simp only [t1Value, hrawT1, Int.cast_sub]]
    exact AffineNarrow.range_of_int _ _ hbt1 ut1bits_valid

lemma eval_expr (env : Environment Field) (i : Var (fields 3) Field) :
    Expression.eval env (kExpr i) = kValue (eval env i) ∧
    Expression.eval env (t0Expr i) = t0Value (eval env i) ∧
    Expression.eval env (t1Expr i) = t1Value (eval env i) := by
  simp only [kExpr, t0Expr, t1Expr, rawKExpr, rawT0Expr, rawT1Expr, kValue, t0Value, t1Value,
    rawK, rawT0, rawT1, Expression.eval, circuit_norm, neg_one_mul, sub_eq_add_neg, and_self]

theorem soundness : FormalAssertion.Soundness Field main Assumptions Spec := by
  circuit_proof_start_core
  have he := eval_expr env input_var
  rw [h_input] at he
  simp only [main, circuit_norm, RangeCheck.circuit, RangeCheck.Assumptions,
    RangeCheck.Spec] at h_holds ⊢
  exact values_sound input h_assumptions
    (by simpa only [he.1] using h_holds.1) (by simpa only [he.2.1] using h_holds.2.1)
    (by simpa only [he.2.2] using h_holds.2.2)

theorem completeness : FormalAssertion.Completeness Field main Assumptions Spec := by
  circuit_proof_start_core
  have he := eval_expr env.toEnvironment input_var
  have hi : eval env.toEnvironment input_var = input := by
    simpa only [circuit_norm] using h_input
  rw [hi] at he
  have hv := values_complete input h_assumptions h_spec
  simp only [main, circuit_norm, RangeCheck.circuit, RangeCheck.Assumptions, RangeCheck.Spec]
  exact ⟨by simpa only [he.1] using hv.1, by simpa only [he.2.1] using hv.2.1,
    by simpa only [he.2.2] using hv.2.2⟩

def circuit : FormalAssertion Field (fields 3) where
  main := main
  Assumptions := Assumptions
  Spec := Spec
  soundness := soundness
  completeness := completeness

def cost3 : Count := ⟨ukbits + ut0bits + ut1bits - 3, ukbits + ut0bits + ut1bits⟩

theorem cost (i : Var (fields 3) Field) : CostIs (main i) cost3 := by
  rw [show cost3 = ⟨ukbits-1, ukbits⟩ + (⟨ut0bits-1, ut0bits⟩ + ⟨ut1bits-1, ut1bits⟩) by decide]
  unfold main
  refine CostIs.bind (Cost.costIs_assertion_implicitRangeCheck _ _ _ _) fun _ => ?_
  refine CostIs.bind (Cost.costIs_assertion_implicitRangeCheck _ _ _ _) fun _ => ?_
  exact Cost.costIs_assertion_implicitRangeCheck _ _ _ _

lemma affine_expr (i : Var (fields 3) Field) (hi : AffineW i) :
    Affine (kExpr i) ∧ Affine (t0Expr i) ∧ Affine (t1Expr i) := by
  have hk : Affine (rawKExpr i) :=
    Affine.fconst_mul _
      (Affine.add (Affine.add (hi _ (by decide)) (Affine.fconst_mul _ (hi _ (by decide))))
        (Affine.fconst_mul _ (hi _ (by decide))))
  have ht0 : Affine (rawT0Expr i) :=
    Affine.fconst_mul _ (Affine.add (hi _ (by decide)) (Affine.fconst_mul _ hk))
  have ht1 : Affine (rawT1Expr i) :=
    Affine.fconst_mul _ (Affine.add (hi _ (by decide)) ht0)
  exact ⟨Affine.sub hk (Affine.const _), Affine.sub ht0 (Affine.const _),
    Affine.sub ht1 (Affine.const _)⟩

theorem shape (i : Var (fields 3) Field) (hi : AffineW i) : IsR1CSCirc (main i) := by
  have h := affine_expr i hi
  unfold main
  refine IsR1CSCirc.bind (Cost.isR1CS_assertion_implicitRangeCheck _ _ _ _ h.1) fun _ => ?_
  refine IsR1CSCirc.bind (Cost.isR1CS_assertion_implicitRangeCheck _ _ _ _ h.2.1) fun _ => ?_
  exact Cost.isR1CS_assertion_implicitRangeCheck _ _ _ _ h.2.2

lemma expr_stable (i : Var (fields 3) Field)
    {e e' : ProverEnvironment Field} (h : eval e i = eval e' i) :
    eval e (kExpr i) = eval e' (kExpr i) ∧
      eval e (t0Expr i) = eval e' (t0Expr i) ∧ eval e (t1Expr i) = eval e' (t1Expr i) := by
  have h' : eval e.toEnvironment i = eval e'.toEnvironment i := by
    simpa only [circuit_norm] using h
  simpa only [circuit_norm, (eval_expr e.toEnvironment i).1, (eval_expr e'.toEnvironment i).1,
    (eval_expr e.toEnvironment i).2.1, (eval_expr e'.toEnvironment i).2.1,
    (eval_expr e.toEnvironment i).2.2, (eval_expr e'.toEnvironment i).2.2, h']

theorem computableWitnesses : circuit.ComputableWitnesses := by
  intro n input env env'
  change Operations.forAllFlat n (FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations n)
  apply FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  simp only [main, Circuit.bind_structuralComputableWitnesses_iff]
  refine ⟨?_, ?_, ?_⟩
  · exact CWHelpers.assertion_structuralComputableWitnesses_of_condition
      (RangeCheck.circuit ukbits ukbits_valid ukbits_pos)
      input _ _ (fun _ _ _ _ _ h => (expr_stable input h).1)
      (RangeCheck.computableWitnesses _ _ _) env env'
  · exact CWHelpers.assertion_structuralComputableWitnesses_of_condition
      (RangeCheck.circuit ut0bits ut0bits_valid ut0bits_pos)
      input _ _ (fun _ _ _ _ _ h => (expr_stable input h).2.1)
      (RangeCheck.computableWitnesses _ _ _) env env'
  · exact CWHelpers.assertion_structuralComputableWitnesses_of_condition
      (RangeCheck.circuit ut1bits ut1bits_valid ut1bits_pos)
      input _ _ (fun _ _ _ _ _ h => (expr_stable input h).2.2)
      (RangeCheck.computableWitnesses _ _ _) env env'

lemma model (i : fields 3 Field) (L0 L1 L2 : ℤ)
    (h0 : l0Min ≤ L0 ∧ L0 ≤ l0Max) (h1 : l1Min ≤ L1 ∧ L1 ≤ l1Max)
    (h2 : l2Min ≤ L2 ∧ L2 ≤ l2Max)
    (hi0 : (i[0]'(by decide)) = (L0 : Field))
    (hi1 : (i[1]'(by decide)) = (L1 : Field))
    (hi2 : (i[2]'(by decide)) = (L2 : Field)) :
    Assumptions i ∧ (Spec i ↔ Sparse32.q ∣ L0 + W96 * L1 + W192 * L2) := by
  have he := uni_centered
  have hhalf : Sparse32.nativeHalf = LazyX.nativeHalf := by
    norm_num [Sparse32.nativeHalf, Sparse32.nativePrime, LazyX.nativeHalf]
  have hl0 : LazyX.lift (i[0]'(by decide)) = L0 := by
    rw [hi0]; apply LazyX.lift_cast; rw [← hhalf]; omega
  have hl1 : LazyX.lift (i[1]'(by decide)) = L1 := by
    rw [hi1]; apply LazyX.lift_cast; rw [← hhalf]; omega
  have hl2 : LazyX.lift (i[2]'(by decide)) = L2 := by
    rw [hi2]; apply LazyX.lift_cast; rw [← hhalf]; omega
  simp only [Assumptions, Spec, hl0, hl1, hl2]
  exact ⟨⟨h0, h1, h2⟩, trivial⟩

lemma localLength (i : Var (fields 3) Field) (o : ℕ) :
    (main i).localLength o = ukbits + ut0bits + ut1bits - 3 := by
  simp only [main, RangeCheck.circuit, circuit_norm]
  decide

end Solution.Secp256k1ScalarMulFixedBase.LazyVar.Cert3
