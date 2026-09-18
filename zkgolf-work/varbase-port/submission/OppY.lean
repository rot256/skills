import Solution.Secp256k1ScalarMul.IsZeroFe2



namespace Solution.Secp256k1ScalarMul
namespace OppY

structure Inputs (F : Type) where
  a : Emu F
  b : Emu F
deriving ProvableStruct

def B64 : ℕ := 18446744073709551616
def pLow : ℕ := 340282366920938463463374607427473243183
def pHigh : ℕ := 340282366920938463463374607431768211455
def pLowCarry : ℕ := 680564733841876926926749214859241454639
def pHighCarry : ℕ := 340282366920938463463374607431768211454

/-- Coefficients of the quadratic `q(x) = alphaC*x^2 + betaC*x` through
`(0,0)`, `(pLow,pHigh)`, `(pLowCarry,pHighCarry)` over `F circomPrime`. -/
def alphaC : ℕ := 16433992275906331238572095123299078612621510224808749728347908543178579115093
def betaC : ℕ := 8808687329525444888344267247997597719915412599424259680155107042291339337521

def lowExpr (a b : Var Emu (F circomPrime)) : Expression (F circomPrime) :=
  a[0] + b[0] +
    (((B64 : F circomPrime) : Expression (F circomPrime)) * (a[1] + b[1]))

def highExpr (a b : Var Emu (F circomPrime)) : Expression (F circomPrime) :=
  a[2] + b[2] +
    (((B64 : F circomPrime) : Expression (F circomPrime)) * (a[3] + b[3]))

def pairVec (lo hi : Expression (F circomPrime)) : Var Emu (F circomPrime) :=
  #v[lo, hi, 0, 0]

def constExpr (n : ℕ) : Expression (F circomPrime) :=
  ((n : F circomPrime) : Expression (F circomPrime))

/-- Value of the low pack under a prover environment. -/
def loEval (input : Var Inputs (F circomPrime))
    (env : ProverEnvironment (F circomPrime)) : F circomPrime :=
  Expression.eval env.toEnvironment (lowExpr input.a input.b)

/-- Value of the high pack under a prover environment. -/
def hiEval (input : Var Inputs (F circomPrime))
    (env : ProverEnvironment (F circomPrime)) : F circomPrime :=
  Expression.eval env.toEnvironment (highExpr input.a input.b)

/-- The cubic root detector `lo·(lo−pLow)·(lo−pLowCarry)`. -/
def wCompute (input : Var Inputs (F circomPrime))
    (env : ProverEnvironment (F circomPrime)) : F circomPrime :=
  (loEval input env * loEval input env - (pLow : F circomPrime) * loEval input env)
    * (loEval input env - (pLowCarry : F circomPrime))

/-- The interpolation residual `hi − alphaC·lo² − betaC·lo`. -/
def dCompute (input : Var Inputs (F circomPrime))
    (env : ProverEnvironment (F circomPrime)) : F circomPrime :=
  hiEval input env - (alphaC : F circomPrime) * (loEval input env * loEval input env)
    - (betaC : F circomPrime) * loEval input env

/-- The prover-chosen folding coefficient: `1` picks the interpolation residual
when the cubic detector already vanishes, `0` keeps the (nonzero) detector
otherwise.  Folding the two conditions into one field element lets a single
`IsZero` replace two, at the price of the two `z·· = 0` soundness rows. -/
def tCompute (input : Var Inputs (F circomPrime))
    (env : ProverEnvironment (F circomPrime)) : F circomPrime :=
  if wCompute input env = 0 then 1 else 0

/-- The folded element `w + t·d`. -/
def uCompute (input : Var Inputs (F circomPrime))
    (env : ProverEnvironment (F circomPrime)) : F circomPrime :=
  wCompute input env + tCompute input env * dCompute input env

def uInvCompute (input : Var Inputs (F circomPrime))
    (env : ProverEnvironment (F circomPrime)) : F circomPrime :=
  if uCompute input env = 0 then 0 else (uCompute input env)⁻¹

def main (input : Var Inputs (F circomPrime)) :
    Circuit (F circomPrime) (Expression (F circomPrime)) := do
  let lo := lowExpr input.a input.b
  let hi := highExpr input.a input.b
  -- cubic root detector: lo2 = lo^2, w = lo*(lo-pLow)*(lo-pLowCarry)
  let lo2 <== (lo * lo : Var field (F circomPrime))
  let w <== ((lo2 - constExpr pLow * lo) * (lo - constExpr pLowCarry) :
    Var field (F circomPrime))
  -- hi is interpolation-tied; the residual is affine in the cells already laid out
  let d : Expression (F circomPrime) :=
    hi - constExpr alphaC * lo2 - constExpr betaC * lo
  let t ← witnessField (tCompute input)
  let v <== (t * d : Var field (F circomPrime))
  let uInv ← witnessField (uInvCompute input)
  let z <== (1 - (w + v) * uInv : Var field (F circomPrime))
  assertZero (z * w)
  assertZero (z * d)
  return z

instance elaborated : ElaboratedCircuit (F circomPrime) Inputs field main := by
  elaborate_circuit

def Assumptions (_ : Inputs (F circomPrime)) : Prop := True

def lowF (a b : Emu (F circomPrime)) : F circomPrime :=
  a[0] + b[0] + (B64 : F circomPrime) * (a[1] + b[1])

def highF (a b : Emu (F circomPrime)) : F circomPrime :=
  a[2] + b[2] + (B64 : F circomPrime) * (a[3] + b[3])

def Spec (input : Inputs (F circomPrime)) (out : F circomPrime) : Prop :=
  let lo := lowF input.a input.b
  let hi := highF input.a input.b
  out = (if lo = 0 ∧ hi = 0 then 1 else 0) +
    (if lo = pLow ∧ hi = pHigh then 1 else 0) +
    (if lo = pLowCarry ∧ hi = pHighCarry then 1 else 0)

private lemma spec_sum_eval {lo hi z : F circomPrime}
    (hz : z = (if lo * (lo - (pLow : F circomPrime))
          * (lo - (pLowCarry : F circomPrime)) = 0 then 1 else 0)
        * (if hi - (alphaC : F circomPrime) * (lo * lo)
            - (betaC : F circomPrime) * lo = 0 then 1 else 0)) :
    z = (if lo = 0 ∧ hi = 0 then 1 else 0) +
      (if lo = pLow ∧ hi = pHigh then 1 else 0) +
      (if lo = pLowCarry ∧ hi = pHighCarry then 1 else 0) := by
  have hne01 : (pLow : F circomPrime) ≠ 0 := by decide
  have hne02 : (pLowCarry : F circomPrime) ≠ 0 := by decide
  have hne12 : (pLow : F circomPrime) ≠ (pLowCarry : F circomPrime) := by decide
  have hq1 : (alphaC : F circomPrime) * ((pLow : F circomPrime) * (pLow : F circomPrime))
      + (betaC : F circomPrime) * (pLow : F circomPrime) = (pHigh : F circomPrime) := by
    decide
  have hq2 : (alphaC : F circomPrime)
        * ((pLowCarry : F circomPrime) * (pLowCarry : F circomPrime))
      + (betaC : F circomPrime) * (pLowCarry : F circomPrime)
      = (pHighCarry : F circomPrime) := by
    decide
  by_cases h0 : lo = 0
  · subst h0
    simp only [zero_mul, if_pos rfl, one_mul] at hz
    rw [hz]
    have hn1 : ¬((0 : F circomPrime) = pLow ∧ hi = pHigh) := fun h => hne01 h.1.symm
    have hn2 : ¬((0 : F circomPrime) = pLowCarry ∧ hi = pHighCarry) :=
      fun h => hne02 h.1.symm
    simp only [hn1, hn2, if_neg, if_false, add_zero, mul_zero, zero_mul, sub_zero,
      zero_add]
    by_cases hh : hi = 0 <;> simp [hh]
  · by_cases h1 : lo = pLow
    · subst h1
      have hcube : (pLow : F circomPrime) * ((pLow : F circomPrime) - (pLow : F circomPrime))
          * ((pLow : F circomPrime) - (pLowCarry : F circomPrime)) = 0 := by
        rw [sub_self, mul_zero, zero_mul]
      rw [if_pos hcube, one_mul] at hz
      rw [hz]
      have hn0 : ¬((pLow : F circomPrime) = 0 ∧ hi = 0) := fun h => hne01 h.1
      have hn2 : ¬((pLow : F circomPrime) = (pLowCarry : F circomPrime)
          ∧ hi = pHighCarry) := fun h => hne12 h.1
      simp only [hn0, hn2, if_neg, if_false, zero_add, add_zero]
      have hiff : hi - (alphaC : F circomPrime) * ((pLow : F circomPrime)
            * (pLow : F circomPrime)) - (betaC : F circomPrime) * (pLow : F circomPrime) = 0
          ↔ hi = (pHigh : F circomPrime) := by
        constructor
        · intro h
          linear_combination h + hq1
        · intro h
          linear_combination h - hq1
      by_cases hh : hi = (pHigh : F circomPrime)
      · rw [if_pos (hiff.mpr hh), if_pos ⟨by trivial, hh⟩]
      · rw [if_neg (fun hc => hh (hiff.mp hc)), if_neg (fun hc => hh hc.2)]
    · by_cases h2 : lo = pLowCarry
      · subst h2
        have hcube : (pLowCarry : F circomPrime)
            * ((pLowCarry : F circomPrime) - (pLow : F circomPrime))
            * ((pLowCarry : F circomPrime) - (pLowCarry : F circomPrime)) = 0 := by
          rw [sub_self, mul_zero]
        rw [if_pos hcube, one_mul] at hz
        rw [hz]
        have hn0 : ¬((pLowCarry : F circomPrime) = 0 ∧ hi = 0) := fun h => hne02 h.1
        have hn1 : ¬((pLowCarry : F circomPrime) = (pLow : F circomPrime)
            ∧ hi = pHigh) := fun h => hne12 h.1.symm
        simp only [hn0, hn1, if_neg, if_false, zero_add, add_zero]
        have hiff : hi - (alphaC : F circomPrime) * ((pLowCarry : F circomPrime)
              * (pLowCarry : F circomPrime))
            - (betaC : F circomPrime) * (pLowCarry : F circomPrime) = 0
            ↔ hi = (pHighCarry : F circomPrime) := by
          constructor
          · intro h
            linear_combination h + hq2
          · intro h
            linear_combination h - hq2
        by_cases hh : hi = (pHighCarry : F circomPrime)
        · rw [if_pos (hiff.mpr hh), if_pos ⟨by trivial, hh⟩]
        · rw [if_neg (fun hc => hh (hiff.mp hc)), if_neg (fun hc => hh hc.2)]
      · have hcube : lo * (lo - (pLow : F circomPrime))
            * (lo - (pLowCarry : F circomPrime)) ≠ 0 := by
          intro h
          rcases mul_eq_zero.mp h with h' | h'
          · rcases mul_eq_zero.mp h' with h'' | h''
            · exact h0 h''
            · exact h1 (sub_eq_zero.mp h'')
          · exact h2 (sub_eq_zero.mp h')
        rw [if_neg hcube, zero_mul] at hz
        rw [hz]
        have hn0 : ¬(lo = 0 ∧ hi = 0) := fun h => h0 h.1
        have hn1 : ¬(lo = (pLow : F circomPrime) ∧ hi = pHigh) := fun h => h1 h.1
        have hn2 : ¬(lo = (pLowCarry : F circomPrime) ∧ hi = pHighCarry) :=
          fun h => h2 h.1
        simp [hn0, hn1, hn2]

theorem soundness :
    Soundness (Input := Inputs) (Output := field) (F circomPrime) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨hlo2, hw, hv, hz, h5, h6⟩ := h_holds
  obtain ⟨ha, hb⟩ := h_input
  have hlo : Expression.eval env (lowExpr input_var_a input_var_b) = lowF input_a input_b := by
    simp only [lowExpr, lowF, Expression.eval]
    have ha0 := congrArg (fun v : Emu (F circomPrime) => v[0]) ha
    have ha1 := congrArg (fun v : Emu (F circomPrime) => v[1]) ha
    have hb0 := congrArg (fun v : Emu (F circomPrime) => v[0]) hb
    have hb1 := congrArg (fun v : Emu (F circomPrime) => v[1]) hb
    simpa only [Vector.getElem_map] using congrArg₂
      (fun x y : F circomPrime => x + y) (congrArg₂ (· + ·) ha0 hb0)
        (congrArg (fun x : F circomPrime => (B64 : F circomPrime) * x)
          (congrArg₂ (· + ·) ha1 hb1))
  have hhi : Expression.eval env (highExpr input_var_a input_var_b) = highF input_a input_b := by
    simp only [highExpr, highF, Expression.eval]
    have ha2 := congrArg (fun v : Emu (F circomPrime) => v[2]) ha
    have ha3 := congrArg (fun v : Emu (F circomPrime) => v[3]) ha
    have hb2 := congrArg (fun v : Emu (F circomPrime) => v[2]) hb
    have hb3 := congrArg (fun v : Emu (F circomPrime) => v[3]) hb
    simpa only [Vector.getElem_map] using congrArg₂
      (fun x y : F circomPrime => x + y) (congrArg₂ (· + ·) ha2 hb2)
        (congrArg (fun x : F circomPrime => (B64 : F circomPrime) * x)
          (congrArg₂ (· + ·) ha3 hb3))
  simp only [Expression.eval, constExpr, hlo, hhi] at hlo2 hw hv hz h5 h6
  dsimp [Spec]
  set lo := lowF input_a input_b
  set hi := highF input_a input_b
  refine spec_sum_eval (lo := lo) (hi := hi) ?_
  set W := env.get (i₀ + 1) with hWdef
  set D := hi + -((alphaC : F circomPrime) * env.get i₀) + -((betaC : F circomPrime) * lo)
    with hDdef
  have hcub : W = lo * (lo - (pLow : F circomPrime)) * (lo - (pLowCarry : F circomPrime)) := by
    rw [hw, hlo2]; ring
  have hquad : D = hi - (alphaC : F circomPrime) * (lo * lo)
      - (betaC : F circomPrime) * lo := by
    rw [hDdef, hlo2]; ring
  rw [← hcub, ← hquad]
  by_cases hW : W = 0
  · by_cases hD : D = 0
    · have hv0 : env.get (i₀ + 1 + 1 + 1) = 0 := by rw [hv, hD, mul_zero]
      rw [if_pos hW, if_pos hD, one_mul, hz, hW, hv0]
      ring
    · rw [if_neg hD, mul_zero]
      exact (mul_eq_zero.mp h6).resolve_right hD
  · rw [if_neg hW, zero_mul]
    exact (mul_eq_zero.mp h5).resolve_right hW

private lemma uCompute_eq_zero_iff (input : Var Inputs (F circomPrime))
    (env : ProverEnvironment (F circomPrime)) :
    uCompute input env = 0 ↔ (wCompute input env = 0 ∧ dCompute input env = 0) := by
  simp only [uCompute, tCompute]
  by_cases h : wCompute input env = 0
  · rw [if_pos h, h]
    simp
  · rw [if_neg h]
    simp only [zero_mul, add_zero]
    exact ⟨fun hc => absurd hc h, fun hc => absurd hc.1 h⟩

private lemma one_sub_uu_inv (input : Var Inputs (F circomPrime))
    (env : ProverEnvironment (F circomPrime)) :
    1 + -(uCompute input env * uInvCompute input env)
      = if uCompute input env = 0 then 1 else 0 := by
  simp only [uInvCompute]
  by_cases h : uCompute input env = 0
  · rw [if_pos h, if_pos h, h]; ring
  · rw [if_neg h, if_neg h, mul_inv_cancel₀ h]; ring

theorem completeness :
    Completeness (Input := Inputs) (Output := field) (F circomPrime) main Assumptions := by
  circuit_proof_start
  obtain ⟨e1, e2, et, ev, ei, ez⟩ := h_env
  have hW : env.get (i₀ + 1) = wCompute { a := input_var_a, b := input_var_b } env := by
    rw [e2, e1]
    simp only [wCompute, loEval, constExpr, Expression.eval]
    ring
  have hD : Expression.eval env.toEnvironment (highExpr input_var_a input_var_b) +
        -(Expression.eval env.toEnvironment (constExpr alphaC) * env.get i₀) +
        -(Expression.eval env.toEnvironment (constExpr betaC) *
          Expression.eval env.toEnvironment (lowExpr input_var_a input_var_b))
      = dCompute { a := input_var_a, b := input_var_b } env := by
    rw [e1]
    simp only [dCompute, loEval, hiEval, constExpr, Expression.eval]
    ring
  have hu : env.get (i₀ + 1) + env.get (i₀ + 1 + 1 + 1)
      = uCompute { a := input_var_a, b := input_var_b } env := by
    rw [hW, ev, et, hD]
    simp only [uCompute]
  refine ⟨e1, e2, ev, ez, ?_, ?_⟩ <;>
    rw [ez, hu, ei, one_sub_uu_inv] <;>
    by_cases h : uCompute { a := input_var_a, b := input_var_b } env = 0
  · rw [if_pos h, hW, ((uCompute_eq_zero_iff _ env).mp h).1, mul_zero]
  · rw [if_neg h, zero_mul]
  · rw [if_pos h, hD, ((uCompute_eq_zero_iff _ env).mp h).2, mul_zero]
  · rw [if_neg h, zero_mul]

private lemma assignEq_output_eval_stable (r : Var field (F circomPrime)) {base k : ℕ}
    {env env' : ProverEnvironment (F circomPrime)}
    (h_agree : env.AgreesBelow k env') (hk : base < k) :
    Expression.eval env.toEnvironment
        ((HasAssignEq.assignEq (β := field (Expression (F circomPrime))) r).output base) =
      Expression.eval env'.toEnvironment
        ((HasAssignEq.assignEq (β := field (Expression (F circomPrime))) r).output base) := by
  simp only [circuit_norm, HasAssignEq.assignEq]
  exact h_agree base hk

def circuit : FormalCircuit (F circomPrime) Inputs field where
  main; elaborated; Assumptions; Spec; soundness; completeness

set_option maxRecDepth 4096 in
theorem computableWitnesses : circuit.base.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  obtain ⟨a, b⟩ := input
  have hL : ∀ (c : ProverEnvironment (F circomPrime) → F circomPrime) (o : ℕ),
      (witnessField c).localLength o = 1 := by
    intro c o
    unfold Circuit.witnessField
    change ((var <$> witnessVar c).localLength o) = 1
    rw [Circuit.map_localLength_eq]
    simp [Circuit.witnessVar, Circuit.localLength, Operations.localLength]
  have hA : ∀ (r : Var field (F circomPrime)) (o : ℕ),
      (HasAssignEq.assignEq (β := field (Expression (F circomPrime))) r).localLength o = 1 := by
    intro r o
    simp only [circuit_norm, HasAssignEq.assignEq]
  have hcells : ∀ (e e' : ProverEnvironment (F circomPrime)),
      eval e (⟨a, b⟩ : Var Inputs (F circomPrime)) =
        eval e' (⟨a, b⟩ : Var Inputs (F circomPrime)) →
      (∀ (i : ℕ) (hi : i < numLimbs),
        Expression.eval e.toEnvironment (a[i]'hi) =
          Expression.eval e'.toEnvironment (a[i]'hi)) ∧
      (∀ (i : ℕ) (hi : i < numLimbs),
        Expression.eval e.toEnvironment (b[i]'hi) =
          Expression.eval e'.toEnvironment (b[i]'hi)) := by
    intro e e' hinput
    simp only [circuit_norm, Inputs.mk.injEq] at hinput
    obtain ⟨ha, hb⟩ := hinput
    constructor
    · intro i hi
      have h := congrArg (fun v : Emu (F circomPrime) => v[i]'hi) ha
      simpa only [Vector.getElem_map] using h
    · intro i hi
      have h := congrArg (fun v : Emu (F circomPrime) => v[i]'hi) hb
      simpa only [Vector.getElem_map] using h
  have hloS : ∀ (e e' : ProverEnvironment (F circomPrime)),
      eval e (⟨a, b⟩ : Var Inputs (F circomPrime)) =
        eval e' (⟨a, b⟩ : Var Inputs (F circomPrime)) →
      Expression.eval e.toEnvironment (lowExpr a b)
        = Expression.eval e'.toEnvironment (lowExpr a b) := by
    intro e e' hinput
    obtain ⟨hcA, hcB⟩ := hcells e e' hinput
    simp only [lowExpr, Expression.eval]
    rw [hcA 0 (by decide), hcB 0 (by decide),
      hcA 1 (by decide), hcB 1 (by decide)]
  have hhiS : ∀ (e e' : ProverEnvironment (F circomPrime)),
      eval e (⟨a, b⟩ : Var Inputs (F circomPrime)) =
        eval e' (⟨a, b⟩ : Var Inputs (F circomPrime)) →
      Expression.eval e.toEnvironment (highExpr a b)
        = Expression.eval e'.toEnvironment (highExpr a b) := by
    intro e e' hinput
    obtain ⟨hcA, hcB⟩ := hcells e e' hinput
    simp only [highExpr, Expression.eval]
    rw [hcA 2 (by decide), hcB 2 (by decide),
      hcA 3 (by decide), hcB 3 (by decide)]
  unfold main
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.witnessField_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.assertZero_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.pure_structuralComputableWitnesses_iff,
    hL, hA, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  -- 1. lo2 <== lo * lo (input-only expression)
  · refine ⟨?_, ?_, ?_⟩
    · intro h_agree hin
      refine congrArg (fun x => (#v[x] : Vector (F circomPrime) 1)) ?_
      have hlo' := hloS env env' hin
      try simp only [Expression.eval, hlo']
      try rfl
    · exact IsZeroFe.equalityFieldSubcircuit_flatStructural_any
        (Parent := Inputs) (⟨a, b⟩ : Var Inputs (F circomPrime)) _ _ _ env env'
    · trivial
  -- 2. w <== (lo2 - pLow*lo) * (lo - pLowCarry): reads the lo2 cell
  · refine ⟨?_, ?_, ?_⟩
    · intro h_agree hin
      refine congrArg (fun x => (#v[x] : Vector (F circomPrime) 1)) ?_
      simp only [circuit_norm, HasAssignEq.assignEq, Circuit.witnessField,
        subcircuit] at h_agree ⊢
      have hg0 : env.get offset = env'.get offset := h_agree offset (by omega)
      have hlo' := hloS env env' hin
      try simp only [Expression.eval, hg0, hlo']
      try rfl
    · exact IsZeroFe.equalityFieldSubcircuit_flatStructural_any
        (Parent := Inputs) (⟨a, b⟩ : Var Inputs (F circomPrime)) _ _ _ env env'
    · trivial
  -- 3. t ← witnessField tCompute (input-only)
  · intro _ hin
    simp only [tCompute, wCompute, loEval, hloS env env' hin]
  -- 4. v <== t * (hi - alphaC*lo2 - betaC*lo): reads the t and lo2 cells
  · refine ⟨?_, ?_, ?_⟩
    · intro h_agree hin
      refine congrArg (fun x => (#v[x] : Vector (F circomPrime) 1)) ?_
      simp only [circuit_norm, HasAssignEq.assignEq, Circuit.witnessField,
        subcircuit] at h_agree ⊢
      have hg0 : env.get offset = env'.get offset := h_agree offset (by omega)
      have hg2 : env.get (offset + 1 + 1) = env'.get (offset + 1 + 1) :=
        h_agree (offset + 1 + 1) (by omega)
      have hlo' := hloS env env' hin
      have hhi' := hhiS env env' hin
      try simp only [Expression.eval, hg0, hg2, hlo', hhi']
      try rfl
    · exact IsZeroFe.equalityFieldSubcircuit_flatStructural_any
        (Parent := Inputs) (⟨a, b⟩ : Var Inputs (F circomPrime)) _ _ _ env env'
    · trivial
  -- 5. uInv ← witnessField uInvCompute (input-only)
  · intro _ hin
    simp only [uInvCompute, uCompute, tCompute, wCompute, dCompute, loEval, hiEval,
      hloS env env' hin, hhiS env env' hin]
  -- 6. z <== 1 - (w + v) * uInv: reads the w, v and uInv cells
  · refine ⟨?_, ?_, ?_⟩
    · intro h_agree _
      refine congrArg (fun x => (#v[x] : Vector (F circomPrime) 1)) ?_
      simp only [circuit_norm, HasAssignEq.assignEq, Circuit.witnessField,
        subcircuit] at h_agree ⊢
      have hg1 : env.get (offset + 1) = env'.get (offset + 1) :=
        h_agree (offset + 1) (by omega)
      have hg3 : env.get (offset + 1 + 1 + 1) = env'.get (offset + 1 + 1 + 1) :=
        h_agree (offset + 1 + 1 + 1) (by omega)
      have hg4 : env.get (offset + 1 + 1 + 1 + 1) = env'.get (offset + 1 + 1 + 1 + 1) :=
        h_agree (offset + 1 + 1 + 1 + 1) (by omega)
      try simp only [Expression.eval, hg1, hg3, hg4]
      try rfl
    · exact IsZeroFe.equalityFieldSubcircuit_flatStructural_any
        (Parent := Inputs) (⟨a, b⟩ : Var Inputs (F circomPrime)) _ _ _ env env'
    · trivial


theorem computableWitness : ∀ n input,
    ProverEnvironment.OnlyAccessedBelow n
      (fun env : ProverEnvironment (F circomPrime) => eval env input) →
    Circuit.ComputableWitnesses (main input) n :=
  Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnesses_implies
    (circuit := circuit.base) computableWitnesses

lemma eval_output_of_agreesBelow (input : Var Inputs (F circomPrime)) {offset k : ℕ}
    {env env' : ProverEnvironment (F circomPrime)}
    (h_agree : env.AgreesBelow k env') (hk : offset + 6 ≤ k) :
    Expression.eval env.toEnvironment (circuit.output input offset) =
      Expression.eval env'.toEnvironment (circuit.output input offset) := by
  obtain ⟨_, _⟩ := input
  simp only [circuit, circuit_norm, Expression.eval, main, HasAssignEq.assignEq,
    Circuit.witnessField] at ⊢
  exact h_agree (offset + 5) (by omega)



def lowN (a b : Emu (F circomPrime)) : ℕ :=
  a[0].val + b[0].val + B64 * (a[1].val + b[1].val)

def highN (a b : Emu (F circomPrime)) : ℕ :=
  a[2].val + b[2].val + B64 * (a[3].val + b[3].val)

lemma lowF_eq_cast (a b : Emu (F circomPrime)) :
    lowF a b = (lowN a b : F circomPrime) := by
  simp only [lowF, lowN]
  push_cast [ZMod.natCast_zmod_val]
  rw [ZMod.natCast_zmod_val a[0], ZMod.natCast_zmod_val b[0],
    ZMod.natCast_zmod_val a[1], ZMod.natCast_zmod_val b[1]]

lemma highF_eq_cast (a b : Emu (F circomPrime)) :
    highF a b = (highN a b : F circomPrime) := by
  simp only [highF, highN]
  push_cast [ZMod.natCast_zmod_val]
  rw [ZMod.natCast_zmod_val a[2], ZMod.natCast_zmod_val b[2],
    ZMod.natCast_zmod_val a[3], ZMod.natCast_zmod_val b[3]]

lemma lowN_lt_two (a b : Emu (F circomPrime)) (ha : a.Normalized limbBits)
    (hb : b.Normalized limbBits) : lowN a b < 2 * B64 * B64 := by
  have ha0 := ha 0
  have ha1 := ha 1
  have hb0 := hb 0
  have hb1 := hb 1
  norm_num [limbBits] at ha0 ha1 hb0 hb1
  simp only [lowN, B64]
  omega

lemma highN_lt_two (a b : Emu (F circomPrime)) (ha : a.Normalized limbBits)
    (hb : b.Normalized limbBits) : highN a b < 2 * B64 * B64 := by
  have ha2 := ha 2
  have ha3 := ha 3
  have hb2 := hb 2
  have hb3 := hb 3
  norm_num [limbBits] at ha2 ha3 hb2 hb3
  simp only [highN, B64]
  omega

lemma lowN_lt (a b : Emu (F circomPrime)) (ha : a.Normalized limbBits)
    (hb : b.Normalized limbBits) : lowN a b < circomPrime := by
  have h := lowN_lt_two a b ha hb
  have hq : 2 * B64 * B64 < circomPrime := by decide
  omega

lemma highN_lt (a b : Emu (F circomPrime)) (ha : a.Normalized limbBits)
    (hb : b.Normalized limbBits) : highN a b < circomPrime := by
  have h := highN_lt_two a b ha hb
  have hq : 2 * B64 * B64 < circomPrime := by decide
  omega

lemma lowF_eq_iff (a b : Emu (F circomPrime)) (ha : a.Normalized limbBits)
    (hb : b.Normalized limbBits) (n : ℕ) (hn : n < circomPrime) :
    lowF a b = (n : F circomPrime) ↔ lowN a b = n := by
  rw [lowF_eq_cast]
  constructor
  · intro h
    have hv := congrArg ZMod.val h
    rwa [ZMod.val_natCast_of_lt (lowN_lt a b ha hb), ZMod.val_natCast_of_lt hn] at hv
  · intro h
    rw [h]

lemma highF_eq_iff (a b : Emu (F circomPrime)) (ha : a.Normalized limbBits)
    (hb : b.Normalized limbBits) (n : ℕ) (hn : n < circomPrime) :
    highF a b = (n : F circomPrime) ↔ highN a b = n := by
  rw [highF_eq_cast]
  constructor
  · intro h
    have hv := congrArg ZMod.val h
    rwa [ZMod.val_natCast_of_lt (highN_lt a b ha hb), ZMod.val_natCast_of_lt hn] at hv
  · intro h
    rw [h]

lemma value_add_eq_chunks (a b : Emu (F circomPrime)) :
    BigInt.value limbBits a + BigInt.value limbBits b =
      lowN a b + B64 * B64 * highN a b := by
  rw [BigInt.value_eq_sum, BigInt.value_eq_sum]
  simp only [numLimbs, Fin.sum_univ_four]
  norm_num [lowN, highN, B64, limbBits]
  ring

private lemma decode_add_zero_iff_values (a b : Emu (F circomPrime))
    (ha : Fe.Valid a) (hb : Fe.Valid b) :
    decodeFe a + decodeFe b = 0 ↔
      BigInt.value limbBits a + BigInt.value limbBits b = 0 ∨
      BigInt.value limbBits a + BigInt.value limbBits b = P256 := by
  have hav := ha.2
  have hbv := hb.2
  have hslt : BigInt.value limbBits a + BigInt.value limbBits b < 2 * P256 := by omega
  simp only [decodeFe, ← Nat.cast_add]
  constructor
  · intro h
    have hdvd : P256 ∣ BigInt.value limbBits a + BigInt.value limbBits b :=
      (ZMod.natCast_eq_zero_iff _ _).mp h
    rcases hdvd with ⟨k, hk⟩
    rw [hk] at hslt ⊢
    have hp : 0 < P256 := by decide
    rcases k with _ | k
    · exact Or.inl (by simp)
    · rcases k with _ | k
      · exact Or.inr (by simp)
      · simp only [P256, Specs.Secp256k1.p] at hslt hp
        omega
  · rintro (h | h)
    · simp [h]
    · rw [h]
      exact (ZMod.natCast_eq_zero_iff _ _).mpr (dvd_refl P256)

private lemma chunks_zero_or_p_iff (a b : Emu (F circomPrime))
    (ha : Fe.Valid a) (hb : Fe.Valid b) :
    (lowN a b = 0 ∧ highN a b = 0) ∨
      (lowN a b = pLow ∧ highN a b = pHigh) ∨
      (lowN a b = pLowCarry ∧ highN a b = pHighCarry) ↔
    BigInt.value limbBits a + BigInt.value limbBits b = 0 ∨
      BigInt.value limbBits a + BigInt.value limbBits b = P256 := by
  have hl := lowN_lt_two a b ha.1 hb.1
  have hh := highN_lt_two a b ha.1 hb.1
  norm_num [B64] at hl hh
  rw [value_add_eq_chunks]
  simp only [B64, pLow, pHigh, pLowCarry, pHighCarry, P256,
    Specs.Secp256k1.p]
  omega


lemma cases_iff_decode_add_zero (a b : Emu (F circomPrime))
    (ha : Fe.Valid a) (hb : Fe.Valid b) :
    ((lowF a b = 0 ∧ highF a b = 0) ∨
      (lowF a b = pLow ∧ highF a b = pHigh) ∨
      (lowF a b = pLowCarry ∧ highF a b = pHighCarry)) ↔
      decodeFe a + decodeFe b = 0 := by
  have hl0 := lowF_eq_iff a b ha.1 hb.1 0 (by decide)
  have hh0 := highF_eq_iff a b ha.1 hb.1 0 (by decide)
  norm_num at hl0 hh0
  rw [hl0, hh0,
    lowF_eq_iff a b ha.1 hb.1 pLow (by decide),
    highF_eq_iff a b ha.1 hb.1 pHigh (by decide),
    lowF_eq_iff a b ha.1 hb.1 pLowCarry (by decide),
    highF_eq_iff a b ha.1 hb.1 pHighCarry (by decide),
    chunks_zero_or_p_iff a b ha hb, decode_add_zero_iff_values a b ha hb]


theorem flag_eq_decode_add_zero {a b : Emu (F circomPrime)} {out : F circomPrime}
    (ha : Fe.Valid a) (hb : Fe.Valid b) (hout : Spec { a, b } out) :
    out = if decodeFe a + decodeFe b = 0 then 1 else 0 := by
  let A0 := lowF a b = 0 ∧ highF a b = 0
  let A1 := lowF a b = pLow ∧ highF a b = pHigh
  let A2 := lowF a b = pLowCarry ∧ highF a b = pHighCarry
  have hcases : A0 ∨ A1 ∨ A2 ↔ decodeFe a + decodeFe b = 0 := by
    simpa [A0, A1, A2] using cases_iff_decode_add_zero a b ha hb
  have h01 : ¬(A0 ∧ A1) := by
    rintro ⟨h0, h1⟩
    have hn0 := (lowF_eq_iff a b ha.1 hb.1 0 (by decide)).mp h0.1
    have hn1 := (lowF_eq_iff a b ha.1 hb.1 pLow (by decide)).mp h1.1
    norm_num at hn0
    simp only [pLow] at hn1
    omega
  have h02 : ¬(A0 ∧ A2) := by
    rintro ⟨h0, h2⟩
    have hn0 := (lowF_eq_iff a b ha.1 hb.1 0 (by decide)).mp h0.1
    have hn2 := (lowF_eq_iff a b ha.1 hb.1 pLowCarry (by decide)).mp h2.1
    norm_num at hn0
    simp only [pLowCarry] at hn2
    omega
  have h12 : ¬(A1 ∧ A2) := by
    rintro ⟨h1, h2⟩
    have hn1 := (lowF_eq_iff a b ha.1 hb.1 pLow (by decide)).mp h1.1
    have hn2 := (lowF_eq_iff a b ha.1 hb.1 pLowCarry (by decide)).mp h2.1
    simp only [pLow] at hn1
    simp only [pLowCarry] at hn2
    omega
  dsimp [Spec] at hout
  change out = (if A0 then 1 else 0) + (if A1 then 1 else 0) +
    (if A2 then 1 else 0) at hout
  by_cases h0 : A0
  · have h1 : ¬A1 := fun h => h01 ⟨h0, h⟩
    have h2 : ¬A2 := fun h => h02 ⟨h0, h⟩
    have hd := hcases.mp (Or.inl h0)
    simpa [h0, h1, h2, hd] using hout
  · by_cases h1 : A1
    · have h2 : ¬A2 := fun h => h12 ⟨h1, h⟩
      have hd := hcases.mp (Or.inr (Or.inl h1))
      simpa [h0, h1, h2, hd] using hout
    · by_cases h2 : A2
      · have hd := hcases.mp (Or.inr (Or.inr h2))
        simpa [h0, h1, h2, hd] using hout
      · have hd : decodeFe a + decodeFe b ≠ 0 := by
          intro h
          rcases hcases.mpr h with h | h | h <;> contradiction
        simpa [h0, h1, h2, hd] using hout

end OppY
end Solution.Secp256k1ScalarMul
