import Solution.Secp256k1ScalarMul.InterpMul

/-!
# A fourteen-point interpolated multiply for a *sparse* second operand

`MulMod.interpolatedMul` witnesses the `2m − 1` convolution coefficients of a
limb product and pins them by asserting the polynomial identity at `2m − 1`
hard-coded evaluation points, one rank-1 row each.  That is optimal for a *full*
product (Fiduccia–Zalcstein), but the two mixed 32-bit certificates
`MulModFold32M` / `MulModFold32N` do not multiply a full product: their second
operand is a four-limb `Emu` value re-read at the **even** base-`2^32`
positions, so `b[1] = b[3] = b[5] = b[7] = 0` is the *literal zero expression*.

With `b[7] = 0` the top convolution cell

  `c₁₄ = Σ_i a_i · b_{14−i} = a₇ · b₇`

is identically zero, so `deg (a·b) ≤ 13` and **fourteen** evaluation points
already pin the product.  This file provides that variant: it witnesses `14`
coefficients, emits `14` rows and returns the `15`-cell vector whose top entry
is the constant `0`, so it is a drop-in replacement for `interpolatedMul` at
`m = 8` — one allocation and one constraint cheaper.
-/

namespace Solution.Secp256k1ScalarMul

section
variable {p : ℕ} [Fact p.Prime]

namespace MulMod

/-- The `15`-cell coefficient vector obtained by appending the constant `0`. -/
def pushZero14 (z : Vector (Expression (F p)) 14) : Vector (Expression (F p)) 15 :=
  z.push 0

/-- Fourteen-point interpolated multiply, valid whenever `b[7] = 0`. -/
def interpolatedMul14 (a b : Var (BigInt 8) (F p)) :
    Circuit (F p) (Vector (Expression (F p)) 15) := do
  let z ← ProvableType.witness (α := fields 14) fun env =>
    Vector.ofFn fun k : Fin 14 =>
      Expression.eval env.toEnvironment ((bigIntMulNoReduce a b)[k.val])
  let constraints : Vector (Expression (F p)) 14 :=
    Vector.mapFinRange 14 fun cIdx =>
      let c : F p := ((cIdx.val + 1 : ℕ) : F p)
      polyEvalExpr a c * polyEvalExpr b c - polyEvalExpr (pushZero14 z) c
  Circuit.forEach constraints assertZero
  return pushZero14 z

/-- The witness vector of `interpolatedMul14`, as read back from the offset. -/
def zVec14 (off : ℕ) : Vector (Expression (F p)) 15 :=
  pushZero14 (Vector.mapRange 14 fun i => var (F := F p) { index := off + i })

lemma interpolatedMul14_output (off : ℕ) (a b : Var (BigInt 8) (F p)) :
    (interpolatedMul14 a b off).1 = zVec14 off := by
  simp only [interpolatedMul14, zVec14, circuit_norm]

lemma interpolatedMul14_localLength (off : ℕ) (a b : Var (BigInt 8) (F p)) :
    Operations.localLength (interpolatedMul14 a b off).2 = 14 := by
  simp only [interpolatedMul14, circuit_norm, Nat.mul_zero, Nat.add_zero]

/-! ## Splitting a fifteen-term sum whose top term vanishes -/

lemma sum15_of_top_zero (u : Fin 15 → F p) (h : u ⟨14, by decide⟩ = 0) (c : F p) :
    (∑ k : Fin 15, u k * c ^ k.val)
      = ∑ k : Fin 14, u ⟨k.val, by omega⟩ * c ^ k.val := by
  rw [Fin.sum_univ_castSucc (n := 14)]
  have : u (Fin.last 14) * c ^ (Fin.last 14).val = 0 := by
    rw [show (Fin.last 14) = (⟨14, by decide⟩ : Fin 15) from rfl, h, zero_mul]
  rw [this, add_zero]
  rfl

/-- With `b[7] = 0` the top convolution cell of an 8-limb product vanishes. -/
lemma conv14_eq_zero (env : Environment (F p)) (a b : Var (BigInt 8) (F p))
    (hb : Expression.eval env b[7] = 0) :
    Expression.eval env ((bigIntMulNoReduce a b)[14]) = 0 := by
  refine Eq.trans (eval_bigIntMulNoReduce_coeff env a b (⟨14, by decide⟩ : Fin (2 * 8 - 1))) ?_
  simp only [Fin.sum_univ_eight]
  norm_num [hb]

/-! ## Soundness -/

lemma interpolatedMul14_soundness (off : ℕ) (a b : Var (BigInt 8) (F p))
    (env : Environment (F p))
    (h : Operations.forAllNoOffset
        { assert := fun e => Expression.eval env e = 0, lookup := fun l => l.Soundness env,
          interact := fun i => i.Guarantees env,
          subcircuit := fun {_n} s => s.Assumptions env → s.Spec env }
        (interpolatedMul14 a b off).2) :
    ∀ cIdx : Fin 14,
      Expression.eval env (polyEvalExpr a ((cIdx.val + 1 : ℕ) : F p))
          * Expression.eval env (polyEvalExpr b ((cIdx.val + 1 : ℕ) : F p))
        = Expression.eval env (polyEvalExpr (zVec14 off) ((cIdx.val + 1 : ℕ) : F p)) := by
  simp only [interpolatedMul14, zVec14, circuit_norm] at h ⊢
  intro cIdx
  have hc := h cIdx
  rw [add_neg_eq_zero] at hc
  exact hc

lemma interp14_points_injective (hpm : (14 : ℕ) < p) :
    Function.Injective (fun cIdx : Fin 14 => (((cIdx.val + 1 : ℕ)) : F p)) := by
  intro i j hij
  simp only at hij
  have hi : i.val + 1 < p := by have := i.isLt; omega
  have hj : j.val + 1 < p := by have := j.isLt; omega
  have := (ZMod.natCast_eq_natCast_iff' _ _ _).mp hij
  rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at this
  exact Fin.ext (by omega)

lemma interpolatedMul14_map_eval (env : Environment (F p)) (off : ℕ)
    (a b : Var (BigInt 8) (F p)) (hpm : (14 : ℕ) < p)
    (hb : Expression.eval env b[7] = 0)
    (hpts : ∀ cIdx : Fin 14,
      Expression.eval env (polyEvalExpr a ((cIdx.val + 1 : ℕ) : F p))
          * Expression.eval env (polyEvalExpr b ((cIdx.val + 1 : ℕ) : F p))
        = Expression.eval env (polyEvalExpr (zVec14 off) ((cIdx.val + 1 : ℕ) : F p))) :
    Vector.map (Expression.eval env) (zVec14 off)
      = Vector.map (Expression.eval env) (bigIntMulNoReduce a b) := by
  set U : Fin 15 → F p := fun k => Expression.eval env (zVec14 off)[k.val] with hU
  set V : Fin 15 → F p := fun k => Expression.eval env (bigIntMulNoReduce a b)[k.val] with hV
  have hU14 : U ⟨14, by decide⟩ = 0 := by
    show Expression.eval env (zVec14 off)[14] = 0
    simp only [zVec14, pushZero14]
    rw [Vector.getElem_push_eq]
    simp only [Expression.eval]
  have hV14 : V ⟨14, by decide⟩ = 0 := conv14_eq_zero env a b hb
  -- agreement of the truncated coefficient functions at the 14 points
  have hagree : ∀ cIdx : Fin 14,
      (∑ k : Fin 14, U ⟨k.val, by omega⟩ * (((cIdx.val + 1 : ℕ)) : F p) ^ k.val)
        = ∑ k : Fin 14, V ⟨k.val, by omega⟩ * (((cIdx.val + 1 : ℕ)) : F p) ^ k.val := by
    intro cIdx
    set c : F p := (((cIdx.val + 1 : ℕ)) : F p) with hcdef
    have hz : Expression.eval env (polyEvalExpr (zVec14 off) c)
        = ∑ k : Fin 15, U k * c ^ k.val := by rw [polyEvalExpr_eval]
    have hab : Expression.eval env (polyEvalExpr a c) * Expression.eval env (polyEvalExpr b c)
        = (∑ i : Fin 8, Expression.eval env a[i.val] * c ^ i.val)
          * (∑ i : Fin 8, Expression.eval env b[i.val] * c ^ i.val) := by
      rw [polyEvalExpr_eval, polyEvalExpr_eval]
    have hcauchy := cauchy_diag (m := 8) (by decide)
      (fun i : Fin 8 => Expression.eval env a[i.val])
      (fun i : Fin 8 => Expression.eval env b[i.val]) c
    have hconv : ∀ k : Fin 15,
        (∑ i : Fin 8, if hh : i.val ≤ k.val ∧ k.val - i.val < 8 then
          (fun i : Fin 8 => Expression.eval env a[i.val]) i
            * (fun i : Fin 8 => Expression.eval env b[i.val]) ⟨k.val - i.val, hh.2⟩ else 0)
        = V k := by
      intro k
      show _ = Expression.eval env (bigIntMulNoReduce a b)[k.val]
      rw [eval_bigIntMulNoReduce_coeff env a b k]
    have hsound := hpts cIdx
    rw [hz, hab, hcauchy] at hsound
    have hL : (∑ k : Fin 15, V k * c ^ k.val) = ∑ k : Fin 15, U k * c ^ k.val := by
      rw [← hsound]
      apply Finset.sum_congr rfl; intro k _
      rw [hconv k]
    rw [← sum15_of_top_zero U hU14 c, ← sum15_of_top_zero V hV14 c, hL]
  have huniq := interp_uniqueness
    (fun k : Fin 14 => U ⟨k.val, by omega⟩) (fun k : Fin 14 => V ⟨k.val, by omega⟩)
    (fun cIdx : Fin 14 => (((cIdx.val + 1 : ℕ)) : F p))
    (interp14_points_injective hpm) hagree
  apply Vector.ext
  intro k hk
  rw [Vector.getElem_map, Vector.getElem_map]
  by_cases h14 : k < 14
  · have := huniq ⟨k, h14⟩
    exact this
  · have hk14 : k = 14 := by omega
    subst hk14
    exact hU14.trans hV14.symm

lemma interpolatedMul14_eval_bridge (env : Environment (F p)) (off : ℕ)
    (a b : Var (BigInt 8) (F p)) (hpm : (14 : ℕ) < p)
    (hb : Expression.eval env b[7] = 0)
    (hpts : ∀ cIdx : Fin 14,
      Expression.eval env (polyEvalExpr a ((cIdx.val + 1 : ℕ) : F p))
          * Expression.eval env (polyEvalExpr b ((cIdx.val + 1 : ℕ) : F p))
        = Expression.eval env (polyEvalExpr (zVec14 off) ((cIdx.val + 1 : ℕ) : F p))) :
    ∀ k : Fin 15,
      Expression.eval env (interpolatedMul14 a b off).1[k.val]
        = Expression.eval env (bigIntMulNoReduce a b)[k.val] := by
  intro k
  rw [interpolatedMul14_output off a b]
  have hvec := interpolatedMul14_map_eval env off a b hpm hb hpts
  have := congrArg (fun w => w[k.val]) hvec
  simpa only [Vector.getElem_map] using this

lemma interpolatedMul14_eval_bridge_uses (env : Environment (F p)) (off : ℕ)
    (a b : Var (BigInt 8) (F p))
    (hb : Expression.eval env b[7] = 0)
    (h : ∀ k : Fin 14, env.get (off + k.val)
        = Expression.eval env ((bigIntMulNoReduce a b)[k.val])) :
    ∀ k : Fin 15,
      Expression.eval env (interpolatedMul14 a b off).1[k.val]
        = Expression.eval env (bigIntMulNoReduce a b)[k.val] := by
  intro k
  rw [interpolatedMul14_output off a b]
  simp only [zVec14, pushZero14]
  by_cases h14 : k.val < 14
  · rw [Vector.getElem_push_lt h14, Vector.getElem_mapRange]
    show env.get (off + k.val) = _
    exact h ⟨k.val, h14⟩
  · have hk : k.val = 14 := by omega
    simp only [hk, Vector.getElem_push_eq]
    rw [show Expression.eval env (0 : Expression (F p)) = 0 from rfl]
    exact (conv14_eq_zero env a b hb).symm

lemma interpolatedMul14_requirements (off : ℕ) (a b : Var (BigInt 8) (F p))
    (env : Environment (F p)) :
    Operations.forAllNoOffset
      { interact := fun i => i.Requirements env,
        subcircuit := fun {_n} s => s.channelsWithRequirements = [] ∨ s.Assumptions env }
      (interpolatedMul14 a b off).2 := by
  simp only [interpolatedMul14, circuit_norm]

lemma interpolatedMul14_usesLocalWitnesses (off off' : ℕ) (a b : Var (BigInt 8) (F p))
    (penv : ProverEnvironment (F p)) (heq : off' = off)
    (h : penv.UsesLocalWitnessesCompleteness off' (interpolatedMul14 a b off).2) :
    ∀ k : Fin 14, penv.toEnvironment.get (off + k.val)
        = Expression.eval penv.toEnvironment ((bigIntMulNoReduce a b)[k.val]) := by
  subst heq
  simp only [interpolatedMul14, circuit_norm] at h
  intro k
  have := h k
  simpa only [Vector.getElem_ofFn] using this

set_option maxHeartbeats 1000000 in
lemma interpolatedMul14_completeness (off : ℕ) (a b : Var (BigInt 8) (F p))
    (penv : ProverEnvironment (F p))
    (hb : Expression.eval penv.toEnvironment b[7] = 0)
    (h : ∀ k : Fin 14, penv.toEnvironment.get (off + k.val)
        = Expression.eval penv.toEnvironment ((bigIntMulNoReduce a b)[k.val])) :
    Operations.forAllNoOffset
      { assert := fun e => Expression.eval penv.toEnvironment e = 0,
        lookup := fun l => l.Completeness penv.toEnvironment,
        interact := fun i => i.Guarantees penv.toEnvironment,
        subcircuit := fun {_n} s => s.ProverAssumptions penv } (interpolatedMul14 a b off).2 := by
  simp only [interpolatedMul14, circuit_norm]
  intro cIdx
  set env := penv.toEnvironment with henv
  set c : F p := (((cIdx.val + 1 : ℕ)) : F p) with hcdef
  rw [add_neg_eq_zero]
  rw [show Expression.eval env (polyEvalExpr a c)
        = ∑ i : Fin 8, Expression.eval env a[i.val] * c ^ i.val from polyEvalExpr_eval _ _ _,
    show Expression.eval env (polyEvalExpr b c)
        = ∑ i : Fin 8, Expression.eval env b[i.val] * c ^ i.val from polyEvalExpr_eval _ _ _,
    show Expression.eval env
          (polyEvalExpr (pushZero14
            (Vector.mapRange 14 fun i => (var (F := F p) { index := off + i }))) c)
        = ∑ k : Fin 15,
            Expression.eval env (pushZero14
              (Vector.mapRange 14 fun i => (var (F := F p) { index := off + i })))[k.val]
              * c ^ k.val
      from polyEvalExpr_eval _ _ _]
  rw [cauchy_diag (m := 8) (by decide) (fun i : Fin 8 => Expression.eval env a[i.val])
    (fun i : Fin 8 => Expression.eval env b[i.val]) c]
  apply Finset.sum_congr rfl; intro k _
  congr 1
  rw [show (∑ i : Fin 8, if hh : i.val ≤ k.val ∧ k.val - i.val < 8 then
        (fun i : Fin 8 => Expression.eval env a[i.val]) i
          * (fun i : Fin 8 => Expression.eval env b[i.val]) ⟨k.val - i.val, hh.2⟩ else 0)
      = Expression.eval env (bigIntMulNoReduce a b)[k.val] from by
    rw [eval_bigIntMulNoReduce_coeff env a b k]]
  simp only [pushZero14]
  by_cases h14 : k.val < 14
  · rw [Vector.getElem_push_lt h14, Vector.getElem_mapRange]
    show _ = env.get (off + k.val)
    exact (h ⟨k.val, h14⟩).symm
  · have hk : k.val = 14 := by omega
    simp only [hk, Vector.getElem_push_eq]
    rw [show Expression.eval env (0 : Expression (F p)) = 0 from rfl]
    exact conv14_eq_zero env a b hb

end MulMod
end

end Solution.Secp256k1ScalarMul
