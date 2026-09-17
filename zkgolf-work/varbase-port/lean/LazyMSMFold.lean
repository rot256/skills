import Solution.Secp256k1ScalarMul.Lazy.LazyMSM
import Solution.Secp256k1ScalarMul.Lazy.StepOutput

/-!
# Fold bookkeeping for the lazy chain

The accumulator after `k` steps is a fixed variable pattern (`accL`), because
each step's output consists of fresh witnesses.  The lemmas here restate the
step's `localLength`/`output` facts at the scalar-mul field instance so that
`simp` can key on them inside the fold hypotheses.
-/

namespace Solution.Secp256k1ScalarMul.LazyMSM

open Specs.ShortWeierstrass Specs.Secp256k1
open Solution.Secp256k1ScalarMulFixedBase.SparseX
open Solution.Secp256k1ScalarMulFixedBase.LazyVar
open Solution.Secp256k1ScalarMul.Lazy

set_option maxHeartbeats 4000000

/-- Accumulator variables: the seed, then the output of step `k`. -/
def accL (input : Var Inputs (F circomPrime)) (i₀ : ℕ) : ℕ → Var LazyPt (F circomPrime)
  | 0 => seed input
  | k + 1 => Step.outputAt (i₀ + k * stepLen + 122)

lemma step_localLength' (k : ℕ) (hk : k + 1 ≤ depth) (i : Var Step.Inputs (F circomPrime)) :
    @FormalCircuitBase.localLength (F circomPrime) _ Step.Inputs Step.LazyPt _ _
      (@GeneralFormalCircuit.base (F circomPrime) Step.Inputs Step.LazyPt _ _ _ (Step.circuit k hk)) i
      = 1500 :=
  Step.circuit_localLength k hk i

lemma step_output' (k : ℕ) (hk : k + 1 ≤ depth) (i : Var Step.Inputs (F circomPrime)) (n₀ : ℕ) :
    @FormalCircuitBase.output (F circomPrime) _ Step.Inputs Step.LazyPt _ _
      (@GeneralFormalCircuit.base (F circomPrime) Step.Inputs Step.LazyPt _ _ _ (Step.circuit k hk)) i n₀
      = Step.outputAt n₀ :=
  Step.output_eq_outputAt k hk i n₀

lemma stepBody_localLength (input : Var Inputs (F circomPrime)) (acc : Var LazyPt (F circomPrime))
    (k : Fin 64) (n : ℕ) : (stepBody input acc k).localLength n = 1622 := by
  simp only [stepBody, circuit_norm, GLVMSM.varLookup_localLength, step_localLength']

lemma stepBody_localLength' (input : Var Inputs (F circomPrime)) (acc : Var LazyPt (F circomPrime))
    (k : Fin 64) (n : ℕ) : Operations.localLength (stepBody input acc k n).2 = 1622 :=
  stepBody_localLength input acc k n

lemma stepBody_output (input : Var Inputs (F circomPrime)) (acc : Var LazyPt (F circomPrime))
    (k : Fin 64) (n : ℕ) : (stepBody input acc k).output n = Step.outputAt (n + 122) := by
  simp only [stepBody, circuit_norm, GLVMSM.varLookup_localLength, step_output', Step.output_eq_outputAt]

lemma stepBody_output' (input : Var Inputs (F circomPrime)) (acc : Var LazyPt (F circomPrime))
    (k : Fin 64) (n : ℕ) : (stepBody input acc k n).1 = Step.outputAt (n + 122) :=
  stepBody_output input acc k n

lemma fin_foldl_ignore_acc {α : Type} (k : ℕ) (f : ℕ → α) (init : α) :
    Fin.foldl (k + 1) (fun _ i => f i.val) init = f k := by
  rw [Fin.foldl_succ_last]
  simp

lemma foldlAcc_eq_accL (input : Var Inputs (F circomPrime)) (i₀ : ℕ) (i : Fin 64) :
    Circuit.FoldlM.foldlAcc (β := LazyPt (Expression (F circomPrime))) i₀ (Vector.finRange 64)
      (stepBody input) (seed input) i = accL input i₀ i.val := by
  simp only [Circuit.FoldlM.foldlAcc, Vector.getElem_finRange, stepBody, circuit_norm,
    GLVMSM.varLookup_localLength, step_output', step_localLength']
  rcases i with ⟨k, hk⟩
  cases k with
  | zero => simp [Fin.foldl_zero, accL]
  | succ k =>
      exact fin_foldl_ignore_acc k (fun v => Step.outputAt (i₀ + v * stepLen + 122)) (seed input)

lemma fin_foldl_eq_accL (input : Var Inputs (F circomPrime)) (i₀ : ℕ) :
    Fin.foldl 64 (fun (_ : LazyPt (Expression (F circomPrime))) (i : Fin 64) =>
      Step.outputAt (i₀ + i.val * 1622 + 122)) (seed input) = accL input i₀ 64 :=
  fin_foldl_ignore_acc 63 (fun v => Step.outputAt (i₀ + v * 1622 + 122)) (seed input)

end Solution.Secp256k1ScalarMul.LazyMSM
