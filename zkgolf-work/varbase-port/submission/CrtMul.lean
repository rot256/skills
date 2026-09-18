import Solution.Secp256k1ScalarMul.ParamsFold
import Solution.Secp256k1ScalarMul.MulModTargetW2
import Solution.Secp256k1ScalarMul.InterpMul
import Solution.Secp256k1ScalarMul.RangeCheck
import Challenge.Utils.ComputableWitnessLemmas

/-!
# A residue-ring (CRT) multiply for the pseudo-Mersenne fold

`MulMod.interpolatedMul` witnesses the `2m − 1 = 7` convolution coefficients of a
four-limb product and pins them with `7` rank-1 rows, which is optimal for a
*full* polynomial product (Fiduccia–Zalcstein).

But the folded certificates never consume the full product: `foldLhs` /
`foldLhsT` immediately reduce it modulo `X^4 − cFold`, using `2^256 ≡ cFold
(mod p)`.  Multiplication in the residue ring `F_r[X]/(X^4 − cFold)` has
bilinear rank `Σᵢ (2·deg fᵢ − 1)` over the irreducible factors of the modulus
(Winograd's `2N − k` bound), and `cFold = 2^32 + 977` happens to be a **fourth
power** in the BN254 scalar field, so `X^4 − cFold` splits completely into four
linear factors and the rank is `4`, not `7`.

This file emits that folded product directly: it witnesses the four folded
digits and asserts the polynomial identity at the four fourth roots of `cFold`.
Soundness is Vandermonde uniqueness for a degree-`< 4` polynomial at four
distinct points.  Cost `⟨4,4⟩` against `interpolatedMul`'s `⟨7,7⟩`.
-/

set_option exponentiation.threshold 400

namespace Solution.Secp256k1ScalarMul
namespace CrtMul

open MulMod

/-- `cFold` as a constant expression (a local copy of `MulModFold.cfE`, kept
here so that this file sits *below* `MulModFold` in the import graph). -/
def cfE : Expression (F circomPrime) := (((cFold : ℕ) : F circomPrime) : Expression (F circomPrime))

/-- The four fourth roots of `cFold = 2^32 + 977` in the BN254 scalar field. -/
def rootNat (j : ℕ) : ℕ :=
  if j = 0 then
    6022495585687529434600811952072328267646044551480745240691212116594068018376
  else if j = 1 then
    6407184712893995821909607707030380421668643124835825632869578387818341362621
  else if j = 2 then
    15481058158945279400336798038226894666879721275580208710828625798757467132996
  else
    15865747286151745787645593793184946820902319848935289103006992069981740477241

/-- The evaluation points, as field elements. -/
def root (j : ℕ) : F circomPrime := ((rootNat j : ℕ) : F circomPrime)

lemma rootNat_lt (j : ℕ) : rootNat j < circomPrime := by
  unfold rootNat; split_ifs <;> decide

lemma rootNat_pow {j : ℕ} (hj : j < numLimbs) :
    rootNat j * rootNat j * (rootNat j * rootNat j) % circomPrime = cFold := by
  have hj' : j < 4 := hj
  have h4 : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases h4 with rfl | rfl | rfl | rfl <;> decide

lemma root_pow4 {j : ℕ} (hj : j < numLimbs) :
    root j ^ 4 = ((cFold : ℕ) : F circomPrime) := by
  have h := rootNat_pow hj
  show ((rootNat j : ℕ) : F circomPrime) ^ 4 = _
  rw [← Nat.cast_pow,
    show rootNat j ^ 4 = rootNat j * rootNat j * (rootNat j * rootNat j) from by ring,
    ← h, ZMod.natCast_mod]

lemma rootNat_inj {i j : ℕ} (hi : i < numLimbs) (hj : j < numLimbs)
    (h : rootNat i = rootNat j) : i = j := by
  have hi' : i < 4 := hi
  have hj' : j < 4 := hj
  have hi4 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  have hj4 : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases hi4 with rfl | rfl | rfl | rfl <;> rcases hj4 with rfl | rfl | rfl | rfl <;>
    first
      | rfl
      | (exfalso; revert h; decide)

lemma root_injective : Function.Injective (fun j : Fin numLimbs => root j.val) := by
  intro i j hij
  simp only [root] at hij
  have hmod := (ZMod.natCast_eq_natCast_iff' _ _ _).mp hij
  rw [Nat.mod_eq_of_lt (rootNat_lt i.val), Nat.mod_eq_of_lt (rootNat_lt j.val)] at hmod
  exact Fin.ext (rootNat_inj i.isLt j.isLt hmod)

/-- The folded raw product, as a four-cell vector of degree-2 expressions.

This is exactly what `foldLhs` / `foldLhsT` build out of the seven raw
convolution cells (before adding the constant offset digits). -/
def foldRawE (a b : Var Emu (F circomPrime)) : Vector (Expression (F circomPrime)) numLimbs :=
  #v[ (bigIntMulNoReduce a b)[0] + cfE * (bigIntMulNoReduce a b)[4],
      (bigIntMulNoReduce a b)[1] + cfE * (bigIntMulNoReduce a b)[5],
      (bigIntMulNoReduce a b)[2] + cfE * (bigIntMulNoReduce a b)[6],
      (bigIntMulNoReduce a b)[3] ]

/-- The residue-ring multiply: witness the four folded digits, pin them with
four evaluations at the fourth roots of `cFold`. -/
def crtMul (a b : Var Emu (F circomPrime)) :
    Circuit (F circomPrime) (Vector (Expression (F circomPrime)) numLimbs) := do
  let d ← ProvableType.witness (α := fields numLimbs) fun env =>
    Vector.ofFn fun k : Fin numLimbs =>
      Expression.eval env.toEnvironment ((foldRawE a b)[k.val])
  let constraints : Vector (Expression (F circomPrime)) numLimbs :=
    Vector.mapFinRange numLimbs fun j =>
      polyEvalExpr a (root j.val) * polyEvalExpr b (root j.val) - polyEvalExpr d (root j.val)
  Circuit.forEach constraints assertZero
  return d

lemma crtMul_output (off : ℕ) (a b : Var Emu (F circomPrime)) :
    (crtMul a b off).1
      = (Vector.mapRange numLimbs fun i => var (F := F circomPrime) { index := off + i }) := by
  simp only [crtMul, circuit_norm]

lemma crtMul_localLength (off : ℕ) (a b : Var Emu (F circomPrime)) :
    Operations.localLength (crtMul a b off).2 = numLimbs := by
  simp only [crtMul, circuit_norm, Nat.mul_zero, Nat.add_zero]

/-- The witnessed digit vector, read back from the offset. -/
def dVec (off : ℕ) : Vector (Expression (F circomPrime)) numLimbs :=
  Vector.mapRange numLimbs fun i => var (F := F circomPrime) { index := off + i }

/-! ## The algebraic core -/

private lemma fold_eval_id (x cf c0 c1 c2 c3 c4 c5 c6 : F circomPrime) (he : x ^ 4 = cf) :
    c0 * x ^ 0 + c1 * x ^ 1 + c2 * x ^ 2 + c3 * x ^ 3 + c4 * x ^ 4 + c5 * x ^ 5 + c6 * x ^ 6
      = (c0 + cf * c4) * x ^ 0 + (c1 + cf * c5) * x ^ 1 + (c2 + cf * c6) * x ^ 2
        + c3 * x ^ 3 := by
  linear_combination (c4 + c5 * x + c6 * x ^ 2) * he

/-- Evaluating the raw product at a fourth root of `cFold` agrees with
evaluating the folded four-cell vector there. -/
lemma prod_eq_foldRaw (env : Environment (F circomPrime)) (a b : Var Emu (F circomPrime))
    {j : ℕ} (hj : j < numLimbs) :
    Expression.eval env (polyEvalExpr a (root j))
        * Expression.eval env (polyEvalExpr b (root j))
      = ∑ k : Fin numLimbs, Expression.eval env (foldRawE a b)[k.val] * (root j) ^ k.val := by
  set x : F circomPrime := root j with hx
  have hm : 0 < numLimbs := by decide
  rw [polyEvalExpr_eval, polyEvalExpr_eval,
    cauchy_diag hm (fun i : Fin numLimbs => Expression.eval env a[i.val])
      (fun i : Fin numLimbs => Expression.eval env b[i.val]) x]
  have hconv : ∀ k : Fin (2 * numLimbs - 1),
      (∑ i : Fin numLimbs, if hh : i.val ≤ k.val ∧ k.val - i.val < numLimbs then
        (fun i : Fin numLimbs => Expression.eval env a[i.val]) i
          * (fun i : Fin numLimbs => Expression.eval env b[i.val]) ⟨k.val - i.val, hh.2⟩ else 0)
      = Expression.eval env (bigIntMulNoReduce a b)[k.val] :=
    fun k => (eval_bigIntMulNoReduce_coeff env a b k).symm
  rw [show (∑ k : Fin (2 * numLimbs - 1),
        (∑ i : Fin numLimbs, if hh : i.val ≤ k.val ∧ k.val - i.val < numLimbs then
          (fun i : Fin numLimbs => Expression.eval env a[i.val]) i
            * (fun i : Fin numLimbs => Expression.eval env b[i.val]) ⟨k.val - i.val, hh.2⟩ else 0)
          * x ^ k.val)
      = ∑ k : Fin (2 * numLimbs - 1),
          Expression.eval env (bigIntMulNoReduce a b)[k.val] * x ^ k.val from by
    apply Finset.sum_congr rfl; intro k _; rw [hconv k]]
  have he : x ^ 4 = ((cFold : ℕ) : F circomPrime) := root_pow4 hj
  show (∑ k : Fin 7, Expression.eval env (bigIntMulNoReduce a b)[k.val] * x ^ k.val)
      = ∑ k : Fin 4, Expression.eval env (foldRawE a b)[k.val] * x ^ k.val
  rw [Fin.sum_univ_seven, Fin.sum_univ_four]
  exact fold_eval_id x _
    (Expression.eval env (bigIntMulNoReduce a b)[0])
    (Expression.eval env (bigIntMulNoReduce a b)[1])
    (Expression.eval env (bigIntMulNoReduce a b)[2])
    (Expression.eval env (bigIntMulNoReduce a b)[3])
    (Expression.eval env (bigIntMulNoReduce a b)[4])
    (Expression.eval env (bigIntMulNoReduce a b)[5])
    (Expression.eval env (bigIntMulNoReduce a b)[6]) he

/-! ## Soundness -/

lemma crtMul_soundness (off : ℕ) (a b : Var Emu (F circomPrime)) (env : Environment (F circomPrime))
    (h : Operations.forAllNoOffset
        { assert := fun e => Expression.eval env e = 0, lookup := fun l => l.Soundness env,
          interact := fun i => i.Guarantees env,
          subcircuit := fun {_n} s => s.Assumptions env → s.Spec env }
        (crtMul a b off).2) :
    ∀ j : Fin numLimbs,
      Expression.eval env (polyEvalExpr a (root j.val))
          * Expression.eval env (polyEvalExpr b (root j.val))
        = Expression.eval env (polyEvalExpr (dVec off) (root j.val)) := by
  simp only [crtMul, circuit_norm, dVec] at h ⊢
  intro j
  have hc := h j
  rw [add_neg_eq_zero] at hc
  exact hc

lemma crtMul_map_eval (env : Environment (F circomPrime)) (off : ℕ)
    (a b : Var Emu (F circomPrime))
    (hpts : ∀ j : Fin numLimbs,
      Expression.eval env (polyEvalExpr a (root j.val))
          * Expression.eval env (polyEvalExpr b (root j.val))
        = Expression.eval env (polyEvalExpr (dVec off) (root j.val))) :
    ∀ k : Fin numLimbs,
      Expression.eval env (dVec off)[k.val] = Expression.eval env (foldRawE a b)[k.val] := by
  set u : Fin numLimbs → F circomPrime :=
    fun k => Expression.eval env (dVec off)[k.val] with hu
  set v : Fin numLimbs → F circomPrime :=
    fun k => Expression.eval env (foldRawE a b)[k.val] with hv
  have hagree : ∀ j : Fin numLimbs,
      (∑ k : Fin numLimbs, u k * (root j.val) ^ k.val)
        = ∑ k : Fin numLimbs, v k * (root j.val) ^ k.val := by
    intro j
    have hd : Expression.eval env (polyEvalExpr (dVec off) (root j.val))
        = ∑ k : Fin numLimbs, u k * (root j.val) ^ k.val := polyEvalExpr_eval _ _ _
    have hab := prod_eq_foldRaw env a b (j := j.val) j.isLt
    rw [← hd, ← hpts j, hab]
  exact interp_uniqueness u v (fun j : Fin numLimbs => root j.val) root_injective hagree

lemma crtMul_eval_bridge (env : Environment (F circomPrime)) (off : ℕ)
    (a b : Var Emu (F circomPrime))
    (hpts : ∀ j : Fin numLimbs,
      Expression.eval env (polyEvalExpr a (root j.val))
          * Expression.eval env (polyEvalExpr b (root j.val))
        = Expression.eval env (polyEvalExpr (dVec off) (root j.val))) :
    ∀ k : Fin numLimbs,
      Expression.eval env (crtMul a b off).1[k.val]
        = Expression.eval env (foldRawE a b)[k.val] := by
  intro k
  rw [crtMul_output off a b]
  exact crtMul_map_eval env off a b hpts k

lemma crtMul_eval_bridge_uses (env : Environment (F circomPrime)) (off : ℕ)
    (a b : Var Emu (F circomPrime))
    (h : ∀ k : Fin numLimbs, env.get (off + k.val)
        = Expression.eval env ((foldRawE a b)[k.val])) :
    ∀ k : Fin numLimbs,
      Expression.eval env (crtMul a b off).1[k.val]
        = Expression.eval env (foldRawE a b)[k.val] := by
  intro k
  rw [crtMul_output off a b, Vector.getElem_mapRange]
  show env.get (off + k.val) = _
  exact h k

lemma crtMul_requirements (off : ℕ) (a b : Var Emu (F circomPrime))
    (env : Environment (F circomPrime)) :
    Operations.forAllNoOffset
      { interact := fun i => i.Requirements env,
        subcircuit := fun {_n} s => s.channelsWithRequirements = [] ∨ s.Assumptions env }
      (crtMul a b off).2 := by
  simp only [crtMul, circuit_norm]

lemma crtMul_usesLocalWitnesses (off off' : ℕ) (a b : Var Emu (F circomPrime))
    (penv : ProverEnvironment (F circomPrime)) (heq : off' = off)
    (h : penv.UsesLocalWitnessesCompleteness off' (crtMul a b off).2) :
    ∀ k : Fin numLimbs, penv.toEnvironment.get (off + k.val)
        = Expression.eval penv.toEnvironment ((foldRawE a b)[k.val]) := by
  subst heq
  simp only [crtMul, circuit_norm] at h
  intro k
  have := h k
  simpa only [Vector.getElem_ofFn] using this

lemma crtMul_completeness (off : ℕ) (a b : Var Emu (F circomPrime))
    (penv : ProverEnvironment (F circomPrime))
    (h : ∀ k : Fin numLimbs, penv.toEnvironment.get (off + k.val)
        = Expression.eval penv.toEnvironment ((foldRawE a b)[k.val])) :
    Operations.forAllNoOffset
      { assert := fun e => Expression.eval penv.toEnvironment e = 0,
        lookup := fun l => l.Completeness penv.toEnvironment,
        interact := fun i => i.Guarantees penv.toEnvironment,
        subcircuit := fun {_n} s => s.ProverAssumptions penv } (crtMul a b off).2 := by
  simp only [crtMul, circuit_norm]
  intro j
  rw [add_neg_eq_zero]
  rw [show Expression.eval penv.toEnvironment
        (polyEvalExpr (Vector.mapRange numLimbs fun i =>
          var (F := F circomPrime) { index := off + i }) (root j.val))
      = ∑ k : Fin numLimbs,
          Expression.eval penv.toEnvironment
            (Vector.mapRange numLimbs fun i =>
              var (F := F circomPrime) { index := off + i })[k.val] * (root j.val) ^ k.val
    from polyEvalExpr_eval _ _ _]
  rw [prod_eq_foldRaw penv.toEnvironment a b (j := j.val) j.isLt]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  rw [Vector.getElem_mapRange]
  show Expression.eval penv.toEnvironment (foldRawE a b)[k.val] = penv.toEnvironment.get (off + k.val)
  rw [h k]

/-! ## Stability -/

lemma foldRawE_eval_stable (E1 E2 : Environment (F circomPrime)) (a b : Var Emu (F circomPrime))
    (ha : ∀ (i : ℕ) (hi : i < numLimbs),
      Expression.eval E1 (a[i]'hi) = Expression.eval E2 (a[i]'hi))
    (hb : ∀ (i : ℕ) (hi : i < numLimbs),
      Expression.eval E1 (b[i]'hi) = Expression.eval E2 (b[i]'hi))
    (k : ℕ) (hk : k < numLimbs) :
    Expression.eval E1 ((foldRawE a b)[k]'hk)
      = Expression.eval E2 ((foldRawE a b)[k]'hk) := by
  have hc : ∀ (t : ℕ) (ht : t < 2 * numLimbs - 1),
      Expression.eval E1 ((bigIntMulNoReduce a b)[t]'ht)
        = Expression.eval E2 ((bigIntMulNoReduce a b)[t]'ht) :=
    fun t ht => bigIntMulNoReduce_coeff_stable E1 E2 a b ha hb ⟨t, ht⟩
  have hk' : k < 4 := hk
  have h4 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases h4 with rfl | rfl | rfl | rfl
  · show Expression.eval E1 (bigIntMulNoReduce a b)[0]
        + ((cFold : ℕ) : F circomPrime) * Expression.eval E1 (bigIntMulNoReduce a b)[4]
      = Expression.eval E2 (bigIntMulNoReduce a b)[0]
        + ((cFold : ℕ) : F circomPrime) * Expression.eval E2 (bigIntMulNoReduce a b)[4]
    rw [hc 0 (by decide), hc 4 (by decide)]
  · show Expression.eval E1 (bigIntMulNoReduce a b)[1]
        + ((cFold : ℕ) : F circomPrime) * Expression.eval E1 (bigIntMulNoReduce a b)[5]
      = Expression.eval E2 (bigIntMulNoReduce a b)[1]
        + ((cFold : ℕ) : F circomPrime) * Expression.eval E2 (bigIntMulNoReduce a b)[5]
    rw [hc 1 (by decide), hc 5 (by decide)]
  · show Expression.eval E1 (bigIntMulNoReduce a b)[2]
        + ((cFold : ℕ) : F circomPrime) * Expression.eval E1 (bigIntMulNoReduce a b)[6]
      = Expression.eval E2 (bigIntMulNoReduce a b)[2]
        + ((cFold : ℕ) : F circomPrime) * Expression.eval E2 (bigIntMulNoReduce a b)[6]
    rw [hc 2 (by decide), hc 6 (by decide)]
  · exact hc 3 (by decide)

lemma crtMul_structuralComputableWitnesses
    {Parent : TypeMap} [CircuitType Parent] (parentInput : Var Parent (F circomPrime))
    (a b : Var Emu (F circomPrime)) (offset : ℕ)
    (hinput : ∀ (k : ℕ) (env env' : ProverEnvironment (F circomPrime)),
      offset ≤ k →
      env.AgreesBelow k env' →
      eval env parentInput = eval env' parentInput →
        eval env a = eval env' a ∧ eval env b = eval env' b) :
    ∀ env env',
      Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.StructuralComputableWitnesses
        parentInput env env' offset ((crtMul a b).operations offset) := by
  intro env env'
  unfold crtMul
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.provableWitness_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.forEach_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.assertZero_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.pure_structuralComputableWitnesses_iff,
    and_true]
  constructor
  · intro h_agree h_parent
    obtain ⟨ha, hb⟩ := hinput offset env env' (Nat.le_refl offset) h_agree h_parent
    apply Vector.ext
    intro t ht
    simp only [Vector.getElem_ofFn]
    exact foldRawE_eval_stable env.toEnvironment env'.toEnvironment a b
      (fun i hi => bigInt_getElem_eval_eq ha i hi)
      (fun i hi => bigInt_getElem_eval_eq hb i hi) t ht
  · intro _
    trivial

lemma crtMul_output_stable (off : ℕ) (a b : Var Emu (F circomPrime))
    {k : ℕ} {env env' : ProverEnvironment (F circomPrime)}
    (h_agree : env.AgreesBelow k env') (hk : off + numLimbs ≤ k) :
    Vector.map (Expression.eval env.toEnvironment) (crtMul a b off).1
      = Vector.map (Expression.eval env'.toEnvironment) (crtMul a b off).1 := by
  rw [crtMul_output off a b]
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_map, Vector.getElem_mapRange, Expression.eval]
  exact h_agree (off + i) (by omega)

end CrtMul
end Solution.Secp256k1ScalarMul
