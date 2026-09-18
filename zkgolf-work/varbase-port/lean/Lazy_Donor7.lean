import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Solution.Secp256k1ScalarMul.Lazy_Donor6

/-! Remaining fixed-base sparse gadgets (patchgravity, zk.golf submission
d59c8bf7) needed by the variable-base lazy chain: the wide product assertion,
the sparse normaliser and its shape. -/

/- === Sparse32Wide === -/
section
namespace Solution.Secp256k1ScalarMulFixedBase.Sparse32Wide

open SmallSquare Sparse32 SparseX Challenge.CostR1CS Cost
open Challenge.Utils.ComputableWitnessLemmas

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 20000

attribute [local irreducible] isR1CSRow r1csProducts operationsIsR1CS flatOperationsIsR1CS

def main (d : Fin 21) (i : Var Inputs Field) : Circuit Field Unit := do
  let za ← subcircuit Sparse32Mul.circuit (mulExpr i.a i.x i.A.point.x)
  let zb ← subcircuit Sparse32Mul.circuit (mulExpr i.b i.x i.T.point.x)
  assertion (Sparse32Cert.circuit (.wide d)) (halvesExpr i za zb)

instance elaborated (d : Fin 21) : ElaboratedCircuit Field Inputs unit (main d) := by
  elaborate_circuit

theorem soundness (d : Fin 21) :
    FormalAssertion.Soundness Field (main d) (Assumptions d) Spec := by
  circuit_proof_start_core
  simp only [main, Sparse32Mul.circuit, Sparse32Mul.Assumptions, Sparse32Cert.circuit,
    circuit_norm] at h_holds ⊢
  obtain ⟨hza, hzb, hc⟩ := h_holds
  have hia : eval env input_var.a = input.a := by
    simpa only [circuit_norm] using congrArg (fun v : Inputs Field => v.a) h_input
  have hib : eval env input_var.b = input.b := by
    simpa only [circuit_norm] using congrArg (fun v : Inputs Field => v.b) h_input
  have hix : eval env input_var.x = input.x := by
    simpa only [circuit_norm] using congrArg (fun v : Inputs Field => v.x) h_input
  have hiAx : eval env input_var.A.point.x = input.A.point.x := by
    simpa only [circuit_norm] using congrArg (fun v : Inputs Field => v.A.point.x) h_input
  have hiTx : eval env input_var.T.point.x = input.T.point.x := by
    simpa only [circuit_norm] using congrArg (fun v : Inputs Field => v.T.point.x) h_input
  have hma := eval_mulExpr env input_var.a input_var.x input_var.A.point.x
  have hmb := eval_mulExpr env input_var.b input_var.x input_var.T.point.x
  rw [hia, hix, hiAx] at hma
  rw [hib, hix, hiTx] at hmb
  simp only [circuit_norm] at hma hmb
  have hza' :
      eval env (Sparse32Mul.outputExpr
        (Vector.mapRange 12 fun j => var { index := i₀ + j })) =
        productVec input.a input.x input.A.point.x := by
    apply (mulSpec_iff input.a input.x input.A.point.x _).mp
    rw [← hma]
    simpa only [circuit_norm] using hza
  have hzb' :
      eval env (Sparse32Mul.outputExpr
        (Vector.mapRange 12 fun j => var { index := i₀ + 12 + j })) =
        productVec input.b input.x input.T.point.x := by
    apply (mulSpec_iff input.b input.x input.T.point.x _).mp
    rw [← hmb]
    simpa only [circuit_norm] using hzb
  have hh := eval_halves d env input_var
    (Sparse32Mul.outputExpr (Vector.mapRange 12 fun j => var { index := i₀ + j }))
    (Sparse32Mul.outputExpr (Vector.mapRange 12 fun j => var { index := i₀ + 12 + j }))
    input h_input h_assumptions hza' hzb'
  have hm := model d input h_assumptions
  have hca : Sparse32Cert.Assumptions (.wide d)
      (eval env (halvesExpr input_var
        (Sparse32Mul.outputExpr (Vector.mapRange 12 fun j => var { index := i₀ + j }))
        (Sparse32Mul.outputExpr
          (Vector.mapRange 12 fun j => var { index := i₀ + 12 + j })))) := by
    rw [hh]
    exact hm.1
  have hcs0 := hc (by simpa only [circuit_norm] using hca)
  have hcs : Sparse32Cert.Spec
      (eval env (halvesExpr input_var
        (Sparse32Mul.outputExpr (Vector.mapRange 12 fun j => var { index := i₀ + j }))
        (Sparse32Mul.outputExpr
          (Vector.mapRange 12 fun j => var { index := i₀ + 12 + j })))) := by
    simpa only [circuit_norm] using hcs0
  rw [hh] at hcs
  exact hm.2.mp hcs

theorem completeness (d : Fin 21) :
    FormalAssertion.Completeness Field (main d) (Assumptions d) Spec := by
  circuit_proof_start_core
  simp only [main, Sparse32Mul.circuit, Sparse32Mul.Assumptions,
    Sparse32Cert.circuit, circuit_norm, Sparse32Mul.elaborated] at h_env ⊢
  obtain ⟨hza, hzb⟩ := h_env
  have hi : eval env.toEnvironment input_var = input := by
    simpa only [circuit_norm] using h_input
  have hia : eval env.toEnvironment input_var.a = input.a := by
    simpa only [circuit_norm] using congrArg (fun v : Inputs Field => v.a) hi
  have hib : eval env.toEnvironment input_var.b = input.b := by
    simpa only [circuit_norm] using congrArg (fun v : Inputs Field => v.b) hi
  have hix : eval env.toEnvironment input_var.x = input.x := by
    simpa only [circuit_norm] using congrArg (fun v : Inputs Field => v.x) hi
  have hiAx : eval env.toEnvironment input_var.A.point.x = input.A.point.x := by
    simpa only [circuit_norm] using congrArg (fun v : Inputs Field => v.A.point.x) hi
  have hiTx : eval env.toEnvironment input_var.T.point.x = input.T.point.x := by
    simpa only [circuit_norm] using congrArg (fun v : Inputs Field => v.T.point.x) hi
  have hma := eval_mulExpr env.toEnvironment input_var.a input_var.x input_var.A.point.x
  have hmb := eval_mulExpr env.toEnvironment input_var.b input_var.x input_var.T.point.x
  rw [hia, hix, hiAx] at hma
  rw [hib, hix, hiTx] at hmb
  simp only [circuit_norm] at hma hmb
  have hza' :
      eval env.toEnvironment
          (Sparse32Mul.outputExpr
            (Vector.mapRange 12 fun j => var { index := i₀ + j })) =
        productVec input.a input.x input.A.point.x := by
    apply (mulSpec_iff input.a input.x input.A.point.x _).mp
    rw [← hma]
    simpa only [circuit_norm] using hza
  have hzb' :
      eval env.toEnvironment
          (Sparse32Mul.outputExpr
            (Vector.mapRange 12 fun j => var { index := i₀ + 12 + j })) =
        productVec input.b input.x input.T.point.x := by
    apply (mulSpec_iff input.b input.x input.T.point.x _).mp
    rw [← hmb]
    simpa only [circuit_norm] using hzb
  have hh := eval_halves d env.toEnvironment input_var
    (Sparse32Mul.outputExpr (Vector.mapRange 12 fun j => var { index := i₀ + j }))
    (Sparse32Mul.outputExpr (Vector.mapRange 12 fun j => var { index := i₀ + 12 + j }))
    input hi h_assumptions hza' hzb'
  have hout : Sparse32Cert.Assumptions (.wide d)
        (eval env.toEnvironment (halvesExpr input_var
          (Sparse32Mul.outputExpr (Vector.mapRange 12 fun j => var { index := i₀ + j }))
          (Sparse32Mul.outputExpr
            (Vector.mapRange 12 fun j => var { index := i₀ + 12 + j })))) ∧
      Sparse32Cert.Spec
        (eval env.toEnvironment (halvesExpr input_var
          (Sparse32Mul.outputExpr (Vector.mapRange 12 fun j => var { index := i₀ + j }))
          (Sparse32Mul.outputExpr
            (Vector.mapRange 12 fun j => var { index := i₀ + 12 + j })))) := by
    rw [hh]
    exact ⟨(model d input h_assumptions).1, (model d input h_assumptions).2.mpr h_spec⟩
  simpa only [circuit_norm] using hout

def circuit (d : Fin 21) : FormalAssertion Field Inputs where
  main := main d
  elaborated := elaborated d
  Assumptions := Assumptions d
  Spec := Spec
  soundness := soundness d
  completeness := completeness d

theorem cost (d : Fin 21) (i : Var Inputs Field) :
    CostIs (main d i)
      ⟨24 + qbits (.wide d) + tbits (.wide d) - 2,
        24 + qbits (.wide d) + tbits (.wide d)⟩ := by
  rw [show
    (⟨24 + qbits (.wide d) + tbits (.wide d) - 2,
      24 + qbits (.wide d) + tbits (.wide d)⟩ : Count) =
      ⟨12, 12⟩ + (⟨12, 12⟩ +
        ⟨qbits (.wide d) + tbits (.wide d) - 2,
          qbits (.wide d) + tbits (.wide d)⟩) by fin_cases d <;> decide]
  unfold main
  refine CostIs.bind (Sparse32Mul.costIs_call _) fun za => ?_
  refine CostIs.bind (Sparse32Mul.costIs_call _) fun zb => ?_
  exact CostIs.assertion (Sparse32Cert.cost (.wide d) _)

lemma localLength (d : Fin 21) (i : Var Inputs Field) (o : ℕ) :
    (main d i).localLength o = 24 + qbits (.wide d) + tbits (.wide d) - 2 := by
  simp only [main, Sparse32Mul.circuit, Sparse32Mul.elaborated, Sparse32Cert.circuit,
    Sparse32Cert.elaborated, circuit_norm]
  fin_cases d <;> decide

def AffineInput (i : Var Inputs Field) : Prop :=
  AffineW i.a ∧ AffineW i.b ∧ AffineW i.x ∧
    Packed.AffinePoint i.A ∧ Packed.AffinePoint i.T

lemma affine_differenceExpr (x : Var (fields 8) Field) (u : Var Emu Field)
    (hx : AffineW x) (hu : AffineW u) : AffineW (differenceExpr x u) := by
  intro k hk
  rw [differenceExpr, Vector.getElem_ofFn]
  exact Affine.sub (affine_embedExpr u hu k hk) (hx k hk)

lemma affine_mulExpr (a x : Var (fields 8) Field) (u : Var Emu Field)
    (ha : AffineW a) (hx : AffineW x) (hu : AffineW u) :
    Sparse32Mul.AffineInput (mulExpr a x u) := by
  exact ⟨ha, affine_differenceExpr x u hx hu⟩

lemma affine_productHalfExpr (z : Var (fields 8) Field) (hz : AffineW z)
    (side : Bool) : Affine (productHalfExpr z side) := by
  cases side
  · simp only [productHalfExpr, Bool.false_eq_true, ↓reduceIte]
    exact Affine.add
      (Affine.add
        (Affine.add (hz 0 (by decide)) (Affine.fconst_mul _ (hz 1 (by decide))))
        (Affine.fconst_mul _ (hz 2 (by decide))))
      (Affine.fconst_mul _ (hz 3 (by decide)))
  · simp only [productHalfExpr, ↓reduceIte]
    exact Affine.add
      (Affine.add
        (Affine.add (hz 4 (by decide)) (Affine.fconst_mul _ (hz 5 (by decide))))
        (Affine.fconst_mul _ (hz 6 (by decide))))
      (Affine.fconst_mul _ (hz 7 (by decide)))

lemma affine_halvesExpr (i : Var Inputs Field) (za zb : Var (fields 8) Field)
    (hi : AffineInput i) (hza : AffineW za) (hzb : AffineW zb) :
    AffineW (halvesExpr i za zb) := by
  intro k hk
  rw [halvesExpr, Vector.getElem_ofFn]
  exact Affine.sub
    (Affine.sub
      (Affine.add (affine_productHalfExpr za hza _) (affine_productHalfExpr zb hzb _))
      (hi.2.2.2.1.2 k hk))
    (hi.2.2.2.2.2 k hk)

theorem shape (d : Fin 21) (i : Var Inputs Field) (hi : AffineInput i) :
    IsR1CSCirc (main d i) := by
  unfold main
  refine IsR1CSCirc.bind_out (IsR1CSCirc.subcircuit
    (Sparse32Mul.shape _ (affine_mulExpr i.a i.x i.A.point.x
      hi.1 hi.2.2.1 hi.2.2.2.1.1))) fun za => ?_
  refine IsR1CSCirc.bind_out (IsR1CSCirc.subcircuit
    (Sparse32Mul.shape _ (affine_mulExpr i.b i.x i.T.point.x
      hi.2.1 hi.2.2.1 hi.2.2.2.2.1))) fun zb => ?_
  apply IsR1CSCirc.assertion
  apply Sparse32Cert.shape (.wide d)
  apply affine_halvesExpr i _ _ hi
  · exact Sparse32Mul.affine_call_output _ za
  · exact Sparse32Mul.affine_call_output _ zb

lemma halves_stable (i : Var Inputs Field) (za zb : Var (fields 8) Field)
    {e e' : ProverEnvironment Field} (hi : eval e i = eval e' i)
    (hza : eval e za = eval e' za) (hzb : eval e zb = eval e' zb) :
    eval e (halvesExpr i za zb) = eval e' (halvesExpr i za zb) := by
  have hA := congrArg (fun v : Inputs Field => v.A.halves) hi
  have hT := congrArg (fun v : Inputs Field => v.T.halves) hi
  simp only [circuit_norm] at hA hT hza hzb ⊢
  apply Vector.ext
  intro k hk
  have hAk := congrArg (fun v : fields 2 Field => v[k]) hA
  have hTk := congrArg (fun v : fields 2 Field => v[k]) hT
  simp only [Vector.getElem_map] at hAk hTk
  simp only [halvesExpr, Vector.getElem_map, Vector.getElem_ofFn, Expression.eval,
    eval_productHalfExpr, circuit_norm, hza, hzb, hAk, hTk]

theorem computableWitnesses (d : Fin 21) : (circuit d).ComputableWitnesses := by
  intro n input env env'
  change Operations.forAllFlat n
    (FormalCircuitBase.computableWitnessCondition input env env')
    ((main d input).operations n)
  apply FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  simp only [main, Circuit.bind_structuralComputableWitnesses_iff]
  constructor
  · rw [FormalCircuit.subcircuit_structuralComputableWitnesses_iff]
    refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      Sparse32Mul.circuit input _ _ ?_ Sparse32Mul.computableWitnesses env env'
    intro k e e' hk hag hp
    have hm := congrArg (fun v : Inputs Field => mulInput v.a v.x v.A.point.x) hp
    simp only [circuit_norm] at hm
    have he := eval_mulExpr e.toEnvironment input.a input.x input.A.point.x
    have he' := eval_mulExpr e'.toEnvironment input.a input.x input.A.point.x
    simp only [circuit_norm] at he he'
    simpa only [circuit_norm] using he.trans (hm.trans he'.symm)
  · constructor
    · rw [FormalCircuit.subcircuit_structuralComputableWitnesses_iff]
      refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
        Sparse32Mul.circuit input _ _ ?_ Sparse32Mul.computableWitnesses env env'
      intro k e e' hk hag hp
      have hm := congrArg (fun v : Inputs Field => mulInput v.b v.x v.T.point.x) hp
      simp only [circuit_norm] at hm
      have he := eval_mulExpr e.toEnvironment input.b input.x input.T.point.x
      have he' := eval_mulExpr e'.toEnvironment input.b input.x input.T.point.x
      simp only [circuit_norm] at he he'
      simpa only [circuit_norm] using he.trans (hm.trans he'.symm)
    · refine CWHelpers.assertion_structuralComputableWitnesses_of_condition
        (Sparse32Cert.circuit (.wide d)) input _ _ ?_
        (Sparse32Cert.computableWitnesses (.wide d)) env env'
      intro k e e' hk hag hp
      simp only [Sparse32Mul.circuit, Sparse32Mul.elaborated, circuit_norm] at hk
      apply halves_stable _ _ _ hp
      · rw [Sparse32Mul.call_output]
        apply Sparse32Mul.main_output_stable _ _ hag
        have hk' : n + 12 ≤ k := by omega
        exact hk'
      · rw [Sparse32Mul.call_output]
        apply Sparse32Mul.main_output_stable _ _ hag
        have hlen :
            (subcircuit Sparse32Mul.circuit
              (mulExpr input.a input.x input.A.point.x)).localLength n = 12 := by
          simp only [Sparse32Mul.circuit, Sparse32Mul.elaborated, circuit_norm]
        rw [hlen]
        omega

end Solution.Secp256k1ScalarMulFixedBase.Sparse32Wide
end

/- === Sparse32Normalize === -/
section
namespace Solution.Secp256k1ScalarMulFixedBase.Sparse32Normalize

open SmallSquare
open Sparse32

set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 20000

def balance (u : Digits Field) : Digits Field :=
  Vector.ofFn fun i => u[i.val] - ((m : ℤ) : Field)

def balanceExpr (u : Var (Digits) Field) : Var (Digits) Field :=
  Vector.ofFn fun i => u[i.val] - ((m : ℤ) : Field)

lemma eval_balanceExpr (env : Environment Field) (u : Var (Digits) Field) :
    Vector.map (Expression.eval env) (balanceExpr u) =
      balance (Vector.map (Expression.eval env) u) := by
  apply Vector.ext
  intro i hi
  simp only [balanceExpr, balance, circuit_norm, Vector.getElem_ofFn]
  rw [sub_eq_add_neg]

lemma balance_spec (raw : Emu Field) (u : Digits Field)
    (hu : ∀ i : Fin 8,
      u[i.val] = ((Sparse32.unsignedDigit raw i : ℕ) : Field)) :
    ∀ i : Fin 8, (balance u)[i.val] = ((Sparse32.digitZ raw i : ℤ) : Field) := by
  intro i
  rw [balance, Vector.getElem_ofFn, hu i]
  simp only [Sparse32.digitZ, Int.cast_sub, Int.cast_natCast]

def main (raw : Var Emu Field) : Circuit Field (Var Digits Field) := do
  let u ← SmallNormalize.circuit .w32 raw
  return balanceExpr u

instance elaborated : ElaboratedCircuit Field Emu Digits main := by
  elaborate_circuit

def Assumptions (_ : Emu Field) (_ : ProverData Field) : Prop := True

def ProverAssumptions (raw : Emu Field) (_ : ProverData Field) (_ : ProverHint Field) : Prop :=
  BigInt.Normalized 64 raw

def Spec (raw : Emu Field) (out : Digits Field) (_ : ProverData Field) : Prop :=
  SlopeRep raw out

def ProverSpec (_ : Emu Field) (_ : Digits Field) (_ : ProverHint Field) : Prop := True

theorem soundness :
    GeneralFormalCircuit.Soundness Field main Assumptions Spec := by
  circuit_proof_start [SmallNormalize.circuit, SmallNormalize.Assumptions,
    SmallNormalize.Spec]
  refine ⟨h_holds.1, ?_⟩
  let u : Digits Field :=
    Vector.map (Expression.eval env) ((SmallNormalize.main .w32 input_var).output i₀)
  have hu : ∀ j : Fin 8,
      u[j.val] = ((Sparse32.unsignedDigit input j : ℕ) : Field) := by
    intro j
    simpa only [u, Sparse32.unsignedDigit, SmallNormalize.main, circuit_norm,
      count, Vector.getElem_map] using h_holds.2 j
  intro i
  let uv : Var Digits Field := (SmallNormalize.main .w32 input_var).output i₀
  have he := congrArg (fun v : Digits Field => v[i.val]) (eval_balanceExpr env uv)
  have hb := balance_spec input u hu i
  simpa only [uv, u, SmallNormalize.main, circuit_norm] using he.trans hb

theorem completeness :
    GeneralFormalCircuit.Completeness Field main ProverAssumptions ProverSpec := by
  circuit_proof_start [SmallNormalize.circuit, SmallNormalize.Assumptions,
    SmallNormalize.Spec, SmallNormalize.ProverAssumptions, SmallNormalize.ProverSpec]
  exact h_assumptions

def circuit : GeneralFormalCircuit Field Emu Digits where
  main := main
  Assumptions := Assumptions
  Spec := Spec
  ProverAssumptions := ProverAssumptions
  ProverSpec := ProverSpec
  soundness := soundness
  completeness := completeness

lemma output_eq (raw : Var Emu Field) (n : ℕ) :
    (main raw).output n = balanceExpr ((SmallNormalize.main .w32 raw).output n) := by
  change balanceExpr ((SmallNormalize.circuit .w32 raw).output n) = _
  rw [SmallNormalize.call_output]

lemma call_output (raw : Var Emu Field) (n : ℕ) :
    (circuit raw).output n = (main raw).output n :=
  (elaborated.output_eq raw n).symm

end Solution.Secp256k1ScalarMulFixedBase.Sparse32Normalize
end

/- === Sparse32NormalizeShape === -/
section
namespace Solution.Secp256k1ScalarMulFixedBase.Sparse32Normalize

open SmallSquare Sparse32 Challenge.CostR1CS Cost

set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 20000

theorem cost (raw : Var Emu Field) : CostIs (main raw) ⟨252, 256⟩ := by
  rw [show (⟨252, 256⟩ : Count) = ⟨252, 256⟩ + Count.zero by decide]
  unfold main
  refine CostIs.bind
    (CostIs.subcircuitWithAssertion (SmallNormalize.cost .w32 raw)) fun _ => ?_
  exact CostIs.pure _

theorem shape (raw : Var Emu Field) (hraw : AffineW raw) :
    IsR1CSCirc (main raw) := by
  unfold main
  refine IsR1CSCirc.bind_out
    (IsR1CSCirc.subcircuitWithAssertion
      (SmallNormalize.shape .w32 raw hraw)) fun _ => ?_
  exact IsR1CSCirc.pure _

lemma affine_balanceExpr (u : Var Digits Field) (hu : AffineW u) :
    AffineW (balanceExpr u) := by
  intro i hi
  rw [balanceExpr, Vector.getElem_ofFn]
  exact Affine.sub (hu i hi) (Affine.const _)

lemma affine_output (raw : Var Emu Field) (hraw : AffineW raw) (n : ℕ) :
    AffineW ((main raw).output n) := by
  rw [output_eq]
  exact affine_balanceExpr _ (SmallNormalize.affine_output .w32 raw hraw n)

/-- Free affine regrouping of four raw words into the signed radix-`2^64`
representation used by endpoint products. -/
def words64Expr (raw : Var Emu Field) : Var (fields 4) Field :=
  Vector.ofFn fun j => raw[j.val] - ((m * (1 + H) : ℤ) : Field)

lemma eval_words64Expr (env : Environment Field) (raw : Var Emu Field) :
    Vector.map (Expression.eval env) (words64Expr raw) =
      words64 (Vector.map (Expression.eval env) raw) := by
  apply Vector.ext
  intro j hj
  simp only [words64Expr, words64, wordZ, circuit_norm, Vector.getElem_ofFn,
    Vector.getElem_map, Int.cast_sub, Int.cast_natCast]
  rw [sub_eq_add_neg]

lemma affine_words64Expr (raw : Var Emu Field) (hraw : AffineW raw) :
    AffineW (words64Expr raw) := by
  intro j hj
  rw [words64Expr, Vector.getElem_ofFn]
  exact Affine.sub (hraw j hj) (Affine.const _)

end Solution.Secp256k1ScalarMulFixedBase.Sparse32Normalize
end

