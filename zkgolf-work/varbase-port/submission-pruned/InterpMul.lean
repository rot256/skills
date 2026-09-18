import Solution.Secp256k1ScalarMul.MulModTheorems
import Solution.Secp256k1ScalarMul.Vandermonde
import Solution.Secp256k1ScalarMul.GroupedEq

namespace Solution.Secp256k1ScalarMul

section
variable {p : ℕ} [Fact p.Prime]
variable {m : ℕ} [NeZero m]

namespace MulMod

-- `polyEvalExpr` / `polyEvalExpr_eval` live in `GroupedEq.lean` (the grouped
-- equality stack consumes the same affine evaluation form).

def interpolatedMul (a b : Var (BigInt m) (F p)) :
    Circuit (F p) (Vector (Expression (F p)) (2 * m - 1)) := do
  -- witness the 2m-1 convolution coefficients directly
  let z ← ProvableType.witness (α := fields (2 * m - 1)) fun env =>
    Vector.ofFn fun k : Fin (2 * m - 1) =>
      Expression.eval env.toEnvironment ((bigIntMulNoReduce a b)[k.val])
  -- for each c = cIdx+1 ∈ {1..2m-1}, assert (polyEval a c)(polyEval b c) = polyEval z c
  let constraints : Vector (Expression (F p)) (2 * m - 1) :=
    Vector.mapFinRange (2 * m - 1) fun cIdx =>
      let c : F p := ((cIdx.val + 1 : ℕ) : F p)
      polyEvalExpr a c * polyEvalExpr b c - polyEvalExpr z c
  Circuit.forEach constraints assertZero
  return z

lemma interpolatedMul_output (off : ℕ) (a b : Var (BigInt m) (F p)) :
    (interpolatedMul a b off).1
      = (Vector.mapRange (2 * m - 1) fun i => var (F := F p) { index := off + i }) := by
  simp only [interpolatedMul, circuit_norm]

lemma interpolatedMul_localLength (off : ℕ) (a b : Var (BigInt m) (F p)) :
    Operations.localLength (interpolatedMul a b off).2 = 2 * m - 1 := by
  simp only [interpolatedMul, circuit_norm, Nat.mul_zero, Nat.add_zero]

def zVec (m off : ℕ) : Vector (Expression (F p)) (2 * m - 1) :=
  Vector.mapRange (2 * m - 1) fun i => var (F := F p) { index := off + i }

lemma interpolatedMul_soundness (off : ℕ) (a b : Var (BigInt m) (F p)) (env : Environment (F p))
    (h : Operations.forAllNoOffset
        { assert := fun e => Expression.eval env e = 0, lookup := fun l => l.Soundness env,
          interact := fun i => i.Guarantees env, subcircuit := fun {_n} s => s.Assumptions env → s.Spec env }
        (interpolatedMul a b off).2) :
    ∀ cIdx : Fin (2 * m - 1),
      Expression.eval env (polyEvalExpr a ((cIdx.val + 1 : ℕ) : F p))
          * Expression.eval env (polyEvalExpr b ((cIdx.val + 1 : ℕ) : F p))
        = Expression.eval env (polyEvalExpr (zVec m off) ((cIdx.val + 1 : ℕ) : F p)) := by
  simp only [interpolatedMul, circuit_norm, zVec] at h ⊢
  intro cIdx
  have hc := h cIdx
  simp only [Expression.eval] at hc
  rw [add_neg_eq_zero] at hc
  exact hc

lemma two_m_sub_one_lt {B : ℕ} (hp : 2 ^ (2 * B) * (m + 1) * 4 < p) :
    2 * m - 1 < p := by
  have hpow : 1 ≤ 2 ^ (2 * B) := Nat.one_le_two_pow
  have hge : 2 ^ (2 * B) * (m + 1) * 4 ≥ 1 * (m + 1) * 4 :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hpow)
  omega

lemma interp_points_injective (hpm : 2 * m - 1 < p) :
    Function.Injective (fun cIdx : Fin (2 * m - 1) => (((cIdx.val + 1 : ℕ)) : F p)) := by
  intro i j hij
  simp only at hij
  have hi : i.val + 1 < p := by have := i.isLt; omega
  have hj : j.val + 1 < p := by have := j.isLt; omega
  have := (ZMod.natCast_eq_natCast_iff' _ _ _).mp hij
  rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at this
  exact Fin.ext (by omega)

lemma interpolatedMul_map_eval (env : Environment (F p)) (off : ℕ)
    (a b : Var (BigInt m) (F p)) (hpm : 2 * m - 1 < p)
    (hpts : ∀ cIdx : Fin (2 * m - 1),
      Expression.eval env (polyEvalExpr a ((cIdx.val + 1 : ℕ) : F p))
          * Expression.eval env (polyEvalExpr b ((cIdx.val + 1 : ℕ) : F p))
        = Expression.eval env (polyEvalExpr (zVec m off) ((cIdx.val + 1 : ℕ) : F p))) :
    Vector.map (Expression.eval env) (zVec m off)
      = Vector.map (Expression.eval env) (bigIntMulNoReduce a b) := by
  have hm : 0 < m := Nat.pos_of_neZero m
  -- coefficient functions
  set u : Fin (2 * m - 1) → F p := fun k => Expression.eval env (zVec m off)[k.val] with hu
  set v : Fin (2 * m - 1) → F p := fun k => Expression.eval env (bigIntMulNoReduce a b)[k.val] with hv
  -- interpolation-uniqueness hypothesis: agreement at the 2m-1 points
  have hagree : ∀ cIdx : Fin (2 * m - 1),
      (∑ k : Fin (2 * m - 1), u k * (((cIdx.val + 1 : ℕ)) : F p) ^ k.val)
        = ∑ k : Fin (2 * m - 1), v k * (((cIdx.val + 1 : ℕ)) : F p) ^ k.val := by
    intro cIdx
    set c : F p := (((cIdx.val + 1 : ℕ)) : F p) with hcdef
    -- RHS of soundness = Σ_k u_k c^k
    have hz : Expression.eval env (polyEvalExpr (zVec m off) c)
        = ∑ k : Fin (2 * m - 1), u k * c ^ k.val := by
      rw [polyEvalExpr_eval]
    -- LHS of soundness = (Σ_i a_i c^i)(Σ_i b_i c^i)
    have hab : Expression.eval env (polyEvalExpr a c) * Expression.eval env (polyEvalExpr b c)
        = (∑ i : Fin m, Expression.eval env a[i.val] * c ^ i.val)
          * (∑ i : Fin m, Expression.eval env b[i.val] * c ^ i.val) := by
      rw [polyEvalExpr_eval, polyEvalExpr_eval]
    -- Cauchy: (Σa)(Σb) = Σ_k conv_k c^k, and conv_k = v_k
    have hcauchy := cauchy_diag hm
      (fun i : Fin m => Expression.eval env a[i.val])
      (fun i : Fin m => Expression.eval env b[i.val]) c
    have hconv : ∀ k : Fin (2 * m - 1),
        (∑ i : Fin m, if hh : i.val ≤ k.val ∧ k.val - i.val < m then
          (fun i : Fin m => Expression.eval env a[i.val]) i
            * (fun i : Fin m => Expression.eval env b[i.val]) ⟨k.val - i.val, hh.2⟩ else 0)
        = v k := by
      intro k
      show _ = Expression.eval env (bigIntMulNoReduce a b)[k.val]
      rw [eval_bigIntMulNoReduce_coeff env a b k]
    -- assemble
    have hsound := hpts cIdx
    rw [hz] at hsound
    rw [hab] at hsound
    rw [hcauchy] at hsound
    -- hsound : Σ_k conv_k c^k = Σ_k u_k c^k
    rw [← hsound]
    apply Finset.sum_congr rfl; intro k _
    rw [hconv k]
  -- apply interpolation-uniqueness
  have huniq := interp_uniqueness u v
    (fun cIdx : Fin (2 * m - 1) => (((cIdx.val + 1 : ℕ)) : F p))
    (interp_points_injective hpm) hagree
  apply Vector.ext
  intro k hk
  rw [Vector.getElem_map, Vector.getElem_map]
  exact huniq ⟨k, hk⟩

lemma interpolatedMul_eval_bridge (env : Environment (F p)) (off : ℕ) (a b : Var (BigInt m) (F p))
    (hpm : 2 * m - 1 < p)
    (hpts : ∀ cIdx : Fin (2 * m - 1),
      Expression.eval env (polyEvalExpr a ((cIdx.val + 1 : ℕ) : F p))
          * Expression.eval env (polyEvalExpr b ((cIdx.val + 1 : ℕ) : F p))
        = Expression.eval env (polyEvalExpr (zVec m off) ((cIdx.val + 1 : ℕ) : F p))) :
    ∀ k : Fin (2 * m - 1),
      Expression.eval env (interpolatedMul a b off).1[k.val]
        = Expression.eval env (bigIntMulNoReduce a b)[k.val] := by
  intro k
  rw [interpolatedMul_output off a b]
  have hvec := interpolatedMul_map_eval env off a b hpm hpts
  have := congrArg (fun w => w[k.val]) hvec
  simpa only [zVec, Vector.getElem_map] using this

lemma interpolatedMul_eval_bridge_uses (env : Environment (F p)) (off : ℕ) (a b : Var (BigInt m) (F p))
    (h : ∀ k : Fin (2 * m - 1), env.get (off + k.val)
        = Expression.eval env ((bigIntMulNoReduce a b)[k.val])) :
    ∀ k : Fin (2 * m - 1),
      Expression.eval env (interpolatedMul a b off).1[k.val]
        = Expression.eval env (bigIntMulNoReduce a b)[k.val] := by
  intro k
  rw [interpolatedMul_output off a b]
  rw [Vector.getElem_mapRange]
  show env.get (off + k.val) = _
  exact h k

lemma interpolatedMul_requirements (off : ℕ) (a b : Var (BigInt m) (F p)) (env : Environment (F p)) :
    Operations.forAllNoOffset
      { interact := fun i => i.Requirements env,
        subcircuit := fun {_n} s => s.channelsWithRequirements = [] ∨ s.Assumptions env }
      (interpolatedMul a b off).2 := by
  simp only [interpolatedMul, circuit_norm]

lemma interpolatedMul_usesLocalWitnesses (off off' : ℕ) (a b : Var (BigInt m) (F p))
    (penv : ProverEnvironment (F p)) (heq : off' = off)
    (h : penv.UsesLocalWitnessesCompleteness off' (interpolatedMul a b off).2) :
    ∀ k : Fin (2 * m - 1), penv.toEnvironment.get (off + k.val)
        = Expression.eval penv.toEnvironment ((bigIntMulNoReduce a b)[k.val]) := by
  subst heq
  simp only [interpolatedMul, circuit_norm] at h
  intro k
  have := h k
  simpa only [Vector.getElem_ofFn] using this

lemma interpolatedMul_completeness (off : ℕ) (a b : Var (BigInt m) (F p)) (penv : ProverEnvironment (F p))
    (h : ∀ k : Fin (2 * m - 1), penv.toEnvironment.get (off + k.val)
        = Expression.eval penv.toEnvironment ((bigIntMulNoReduce a b)[k.val])) :
    Operations.forAllNoOffset
      { assert := fun e => Expression.eval penv.toEnvironment e = 0,
        lookup := fun l => l.Completeness penv.toEnvironment,
        interact := fun i => i.Guarantees penv.toEnvironment, subcircuit := fun {_n} s => s.ProverAssumptions penv } (interpolatedMul a b off).2 := by
  simp only [interpolatedMul, circuit_norm]
  intro cIdx
  have hm : 0 < m := Nat.pos_of_neZero m
  set c : F p := (((cIdx.val + 1 : ℕ)) : F p) with hcdef
  rw [add_neg_eq_zero]
  -- evaluate all three point-evaluations
  rw [show Expression.eval penv.toEnvironment (polyEvalExpr a c)
        = ∑ i : Fin m, Expression.eval penv.toEnvironment a[i.val] * c ^ i.val from polyEvalExpr_eval _ _ _,
    show Expression.eval penv.toEnvironment (polyEvalExpr b c)
        = ∑ i : Fin m, Expression.eval penv.toEnvironment b[i.val] * c ^ i.val from polyEvalExpr_eval _ _ _,
    show Expression.eval penv.toEnvironment
          (polyEvalExpr (Vector.mapRange (2 * m - 1) fun i => var (F := F p) { index := off + i }) c)
        = ∑ k : Fin (2 * m - 1),
            Expression.eval penv.toEnvironment
              (Vector.mapRange (2 * m - 1) fun i => var (F := F p) { index := off + i })[k.val] * c ^ k.val
      from polyEvalExpr_eval _ _ _]
  -- Cauchy on LHS
  rw [cauchy_diag hm (fun i : Fin m => Expression.eval penv.toEnvironment a[i.val])
    (fun i : Fin m => Expression.eval penv.toEnvironment b[i.val]) c]
  -- both sides are Σ_k (something_k) c^k; show the coefficients agree
  apply Finset.sum_congr rfl; intro k _
  congr 1
  -- LHS conv coeff = eval (bigIntMulNoReduce a b)[k] = env.get (off+k) = z-cell eval
  rw [show (∑ i : Fin m, if hh : i.val ≤ k.val ∧ k.val - i.val < m then
        (fun i : Fin m => Expression.eval penv.toEnvironment a[i.val]) i
          * (fun i : Fin m => Expression.eval penv.toEnvironment b[i.val]) ⟨k.val - i.val, hh.2⟩ else 0)
      = Expression.eval penv.toEnvironment (bigIntMulNoReduce a b)[k.val] from by
    rw [eval_bigIntMulNoReduce_coeff penv.toEnvironment a b k]]
  rw [← h k]
  simp only [Vector.getElem_mapRange, Expression.eval]

end MulMod

end

end Solution.Secp256k1ScalarMul
