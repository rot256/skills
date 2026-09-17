import Solution.Secp256k1ScalarMul.Lazy.Certs
import Solution.Secp256k1ScalarMulFixedBase.CWHelpers

/-! Computable witnesses of the certificate-slot assertion. -/

namespace Solution.Secp256k1ScalarMulFixedBase.LazyVar.Certs

open SmallSquare Sparse32 SparseX
open Solution.Secp256k1ScalarMul.Lazy
open Solution.Secp256k1ScalarMulFixedBase.LazyVar
open Challenge.Utils.ComputableWitnessLemmas

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

/-- Native value of a half of an evaluated word vector. -/
def halfN (w : fields 8 Field) (side : Bool) : Field :=
  if side then Sparse32.highHalf (fun k => w[k.val]) else Sparse32.lowHalf (fun k => w[k.val])

def limbN (w : fields 8 Field) (j : Fin 3) : Field :=
  if j.val = 0 then w[0] + (H : Field) * w[1] + (H ^ 2 : Field) * w[2]
  else if j.val = 1 then w[3] + (H : Field) * w[4] + (H ^ 2 : Field) * w[5]
  else w[6] + (H : Field) * w[7]

lemma eval_half (env : Environment Field) (w : Var (fields 8) Field) (side : Bool) :
    Expression.eval env (half w side) = halfN (Vector.map (Expression.eval env) w) side := by
  rw [half, Sparse32Wide.eval_productHalfExpr]
  simp only [halfN, circuit_norm, Vector.getElem_map]

lemma eval_limb (env : Environment Field) (w : Var (fields 8) Field) (j : Fin 3) :
    Expression.eval env (limb w j) = limbN (Vector.map (Expression.eval env) w) j := by
  fin_cases j <;>
    simp only [limb, limbN, circuit_norm, Expression.eval, Fin.isValue, Fin.val_zero,
      Fin.val_one, Fin.val_two, Nat.one_ne_zero, Nat.succ_ne_self, OfNat.ofNat_ne_zero,
      OfNat.ofNat_ne_one, Nat.reduceEqDiff, ↓reduceIte, Vector.getElem_map]

lemma payload_stable (i : Var Inputs Field) {e e' : ProverEnvironment Field}
    (h : eval e i = eval e' i) :
    Vector.map (Expression.eval e.toEnvironment) (chordW i) =
      Vector.map (Expression.eval e'.toEnvironment) (chordW i) ∧
    Vector.map (Expression.eval e.toEnvironment) (xeq1W i) =
      Vector.map (Expression.eval e'.toEnvironment) (xeq1W i) ∧
    Vector.map (Expression.eval e.toEnvironment) (uniW i) =
      Vector.map (Expression.eval e'.toEnvironment) (uniW i) ∧
    Vector.map (Expression.eval e.toEnvironment) (yeqW i) =
      Vector.map (Expression.eval e'.toEnvironment) (yeqW i) ∧
    Vector.map (Expression.eval e.toEnvironment) (xeq2W i) =
      Vector.map (Expression.eval e'.toEnvironment) (xeq2W i) ∧
    Vector.map (Expression.eval e.toEnvironment) (rel2W i) =
      Vector.map (Expression.eval e'.toEnvironment) (rel2W i) ∧
    Expression.eval e.toEnvironment i.gate = Expression.eval e'.toEnvironment i.gate ∧
    Expression.eval e.toEnvironment i.cflag = Expression.eval e'.toEnvironment i.cflag ∧
    Expression.eval e.toEnvironment i.zflag = Expression.eval e'.toEnvironment i.zflag := by
  have hi : eval e.toEnvironment i = eval e'.toEnvironment i := by
    simpa only [circuit_norm] using h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 := map_chordW e.toEnvironment i
    have h2 := map_chordW e'.toEnvironment i
    rw [h1, h2, hi]
  · have h1 := map_xeq1W e.toEnvironment i
    have h2 := map_xeq1W e'.toEnvironment i
    rw [h1, h2, hi]
  · have h1 := map_uniW e.toEnvironment i
    have h2 := map_uniW e'.toEnvironment i
    rw [h1, h2, hi]
  · have h1 := map_yeqW e.toEnvironment i
    have h2 := map_yeqW e'.toEnvironment i
    rw [h1, h2, hi]
  · have h1 := map_xeq2W e.toEnvironment i
    have h2 := map_xeq2W e'.toEnvironment i
    rw [h1, h2, hi]
  · have h1 := map_rel2W e.toEnvironment i
    have h2 := map_rel2W e'.toEnvironment i
    rw [h1, h2, hi]
  · simpa only [circuit_norm] using congrArg Inputs.gate hi
  · simpa only [circuit_norm] using congrArg Inputs.cflag hi
  · simpa only [circuit_norm] using congrArg Inputs.zflag hi

lemma mulCell_localLength (i : Var MulCell.Inputs Field) (o : ℕ) :
    (subcircuit MulCell.circuit i).localLength o = 1 := by
  simp only [MulCell.circuit, MulCell.elaborated, circuit_norm]

theorem computableWitnesses (n : ℕ) (hn : n ≤ depth) : (circuit n hn).ComputableWitnesses := by
  intro o input env env'
  change Operations.forAllFlat o (FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations o)
  apply FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  simp only [main, Circuit.bind_structuralComputableWitnesses_iff,
    mulCell_localLength, MulCell.call_output]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (rw [FormalCircuit.subcircuit_structuralComputableWitnesses_iff]
       apply FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
       rotate_left
       exact MulCell.computableWitnesses)
    | (rw [FormalAssertion.assertion_structuralComputableWitnesses_iff]
       apply FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
       rotate_left
       first | exact Cert.computableWitnesses _ | exact Cert3.computableWitnesses)
  all_goals
    intro k e e' hk hag hp
    have he := payload_stable input hp
    have hag' : ∀ j, j < k → e.get j = e'.get j := hag
    simp only [Cert.circuit, Cert3.circuit, Cert.elaborated, Cert3.elaborated, circuit_norm] at hk
    simp only [circuit_norm, MulCell.Inputs.mk.injEq, eval_half, eval_limb,
      he.1, he.2.1, he.2.2.1, he.2.2.2.1, he.2.2.2.2.1, he.2.2.2.2.2.1,
      he.2.2.2.2.2.2.1, he.2.2.2.2.2.2.2.1, he.2.2.2.2.2.2.2.2]
    all_goals simp (disch := omega) only [hag']

end Solution.Secp256k1ScalarMulFixedBase.LazyVar.Certs
