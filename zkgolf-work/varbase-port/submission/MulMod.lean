import Solution.Secp256k1ScalarMul.LessThan
import Solution.Secp256k1ScalarMul.EqViaCarries
import Solution.Secp256k1ScalarMul.GroupedEqXV
import Solution.Secp256k1ScalarMul.InterpMul
import Solution.Secp256k1ScalarMul.MulModTheorems



namespace Solution.Secp256k1ScalarMul
open Solution.Secp256k1ScalarMul.Limbs

section
variable {p : ℕ} [Fact p.Prime]
variable {m : ℕ} [NeZero m]

namespace MulMod


structure Inputs (m : ℕ) (F : Type) where
  a : BigInt m F
  b : BigInt m F
  modulus : BigInt m F
deriving ProvableStruct


private def evalValue (B : ℕ) (env : ProverEnvironment (F p))
    (x : Var (BigInt m) (F p)) : ℕ :=
  Solution.Secp256k1ScalarMul.Limbs.fromLimbs B ((x.map (Expression.eval env.toEnvironment)).toList.map ZMod.val)



def witnessedMul (a b : Var (BigInt m) (F p)) :
    Circuit (F p) (Vector (Expression (F p)) (2 * m - 1)) := do
  -- witness the product matrix pp[i*m+j] = a[i].val * b[j].val
  let pp ← ProvableType.witness (α := fields (m * m)) fun env =>
    Vector.ofFn fun t : Fin (m * m) =>
      (Expression.eval env.toEnvironment (a[t.val / m]'(Nat.div_lt_of_lt_mul t.isLt)))
        * (Expression.eval env.toEnvironment (b[t.val % m]'(Nat.mod_lt _ (Nat.pos_of_neZero m))))
  -- assert each witnessed product equals a[i]*b[j]
  let constraints : Vector (Expression (F p)) (m * m) :=
    Vector.mapFinRange (m * m) fun t =>
      (a[t.val / m]'(Nat.div_lt_of_lt_mul t.isLt))
        * (b[t.val % m]'(Nat.mod_lt _ (Nat.pos_of_neZero m)))
        - pp[t.val]
  Circuit.forEach constraints assertZero
  return bigIntMulVars pp


lemma witnessedMul_output (off : ℕ) (a b : Var (BigInt m) (F p)) :
    (witnessedMul a b off).1
      = bigIntMulVars (Vector.mapRange (m * m) fun i => var (F := F p) { index := off + i }) := by
  simp only [witnessedMul, circuit_norm]


lemma witnessedMul_localLength (off : ℕ) (a b : Var (BigInt m) (F p)) :
    Operations.localLength (witnessedMul a b off).2 = m * m := by
  simp only [witnessedMul, circuit_norm, Nat.mul_zero, Nat.add_zero]


lemma witnessedMul_soundness (off : ℕ) (a b : Var (BigInt m) (F p)) (env : Environment (F p))
    (h : Operations.forAllNoOffset
        { assert := fun e => Expression.eval env e = 0, lookup := fun l => l.Soundness env,
          interact := fun i => i.Guarantees env, subcircuit := fun {_n} s => s.Assumptions env → s.Spec env }
        (witnessedMul a b off).2) :
    ∀ t : Fin (m * m),
      Expression.eval env (a[t.val / m]'(Nat.div_lt_of_lt_mul t.isLt))
          * Expression.eval env (b[t.val % m]'(Nat.mod_lt _ (Nat.pos_of_neZero m)))
        = env.get (off + t.val) := by
  simp only [witnessedMul, circuit_norm] at h
  intro t; have := h t; rw [add_neg_eq_zero] at this; exact this


lemma witnessedMul_eval_bridge (env : Environment (F p)) (off : ℕ) (a b : Var (BigInt m) (F p))
    (h_prod : ∀ t : Fin (m * m),
      Expression.eval env (a[t.val / m]'(Nat.div_lt_of_lt_mul t.isLt))
          * Expression.eval env (b[t.val % m]'(Nat.mod_lt _ (Nat.pos_of_neZero m)))
        = env.get (off + t.val)) :
    ∀ k : Fin (2 * m - 1),
      Expression.eval env (witnessedMul a b off).1[k.val]
        = Expression.eval env (bigIntMulNoReduce a b)[k.val] := by
  intro k
  rw [witnessedMul_output off a b]
  have hvec := witnessedMul_map_eval env off a b h_prod
  have := congrArg (fun v => v[k.val]) hvec
  simpa only [Vector.getElem_map] using this


lemma witnessedMul_requirements (off : ℕ) (a b : Var (BigInt m) (F p)) (env : Environment (F p)) :
    Operations.forAllNoOffset
      { interact := fun i => i.Requirements env,
        subcircuit := fun {_n} s => s.channelsWithRequirements = [] ∨ s.Assumptions env }
      (witnessedMul a b off).2 := by
  simp only [witnessedMul, circuit_norm]


lemma witnessedMul_usesLocalWitnesses (off off' : ℕ) (a b : Var (BigInt m) (F p))
    (penv : ProverEnvironment (F p)) (heq : off' = off)
    (h : penv.UsesLocalWitnessesCompleteness off' (witnessedMul a b off).2) :
    ∀ t : Fin (m * m), penv.toEnvironment.get (off + t.val)
        = Expression.eval penv.toEnvironment (a[t.val / m]'(Nat.div_lt_of_lt_mul t.isLt))
            * Expression.eval penv.toEnvironment (b[t.val % m]'(Nat.mod_lt _ (Nat.pos_of_neZero m))) := by
  subst heq
  simp only [witnessedMul, circuit_norm] at h
  intro t
  have := h t
  simpa only [Vector.getElem_ofFn] using this


lemma witnessedMul_completeness (off : ℕ) (a b : Var (BigInt m) (F p)) (penv : ProverEnvironment (F p))
    (h : ∀ t : Fin (m * m), penv.toEnvironment.get (off + t.val)
        = Expression.eval penv.toEnvironment (a[t.val / m]'(Nat.div_lt_of_lt_mul t.isLt))
            * Expression.eval penv.toEnvironment (b[t.val % m]'(Nat.mod_lt _ (Nat.pos_of_neZero m)))) :
    Operations.forAllNoOffset
      { assert := fun e => Expression.eval penv.toEnvironment e = 0,
        lookup := fun l => l.Completeness penv.toEnvironment,
        interact := fun i => i.Guarantees penv.toEnvironment, subcircuit := fun {_n} s => s.ProverAssumptions penv }
      (witnessedMul a b off).2 := by
  simp only [witnessedMul, circuit_norm]
  intro t; rw [h t]; ring


def main (P : BigIntParams p m)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqXV.GVXHyps p (2 * m - 1) P.B gf posOf G V VR)
    [Fact (p > 2)]
    (input : Var (Inputs m) (F p)) :
    Circuit (F p) (Var (BigInt m) (F p)) :=
  letI : NeZero (2 * m - 1) := ⟨by have := Nat.pos_of_neZero m; omega⟩
  do
  let a := input.a
  let b := input.b
  let n := input.modulus

  -- 1. witness q = (a·b)/n and r = (a·b)%n as BigInt m
  let q ← ProvableType.witness (α := BigInt m) fun env =>
    let prod := evalValue P.B env a * evalValue P.B env b
    let qval : ℕ := prod / evalValue P.B env n
    Vector.ofFn fun k : Fin m => ((qval / 2 ^ (P.B * k.val) % 2 ^ P.B : ℕ) : F p)
  let r ← ProvableType.witness (α := BigInt m) fun env =>
    let prod := evalValue P.B env a * evalValue P.B env b
    let rval : ℕ := prod % evalValue P.B env n
    Vector.ofFn fun k : Fin m => ((rval / 2 ^ (P.B * k.val) % 2 ^ P.B : ℕ) : F p)

  -- 2. normalize q and r (subcircuit calls)
  Normalize.circuit P q
  Normalize.circuit P r

  -- 3. Pc = a·b via the xJsnark interpolation check (`2m−1` coefficient
  --    witnesses + `2m−1` point rows instead of `m·m` product witnesses);
  --    Sqn = q·n as the direct schoolbook convolution (constant modulus
  --    limbs keep it affine)
  let Pc ← interpolatedMul a b
  let Sqn : Vector (Expression (F p)) (2 * m - 1) := bigIntMulNoReduce q n
  let S : Vector (Expression (F p)) (2 * m - 1) := Vector.mapFinRange (2 * m - 1) fun k =>
    if h : k.val < m then Sqn[k.val] + r[k.val]'h else Sqn[k.val]

  -- 4. certify a·b = q·n + r as integers via the grouped equality
  GroupedEqXV.circuit P.B gf posOf G V VR hgv P.hB1 { lhs := Pc, rhs := S }

  -- 5. certify r < n (subcircuit call)
  LessThan.circuit P { lhs := r, rhs := n }

  -- 6. return r
  return r

instance elaborated (P : BigIntParams p m)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqXV.GVXHyps p (2 * m - 1) P.B gf posOf G V VR)
    [Fact (p > 2)] :
    ElaboratedCircuit (F p) (Inputs m) (BigInt m) (main P gf posOf G V VR hgv) where
  -- q (m) + r (m) + normalize q (m*B) + normalize r (m*B)
  --   + interpolatedMul a b (2m−1) — the q·n convolution is witness-free
  --   + groupedEqXV (Σ (Wf k − 1)) + lessThan (m + m*B + m)
  localLength _ :=
    m + m + m * (P.B - 1) + m * (P.B - 1) + (2 * m - 1)
      + GroupedEqXV.widthAllocFrom V.Wf (G - 2) 0 + (m + m * (P.B - 1) + m)
  output _ i0 := varFromOffset (BigInt m) (i0 + m)
  localLength_eq := by
    intro input offset
    simp only [main, interpolatedMul, circuit_norm, Normalize.circuit, Normalize.elaborated,
      Normalize.main, GroupedEqXV.circuit, GroupedEqXV.elaborated,
      LessThan.circuit, LessThan.elaborated, LessThan.main, RangeCheck.circuit, Gadgets.ToBits.rangeCheck]
    omega
  output_eq := by
    intro input offset
    simp only [main, interpolatedMul, circuit_norm, Normalize.circuit, Normalize.elaborated,
      Normalize.main, GroupedEqXV.circuit, GroupedEqXV.elaborated,
      LessThan.circuit, LessThan.elaborated, LessThan.main, RangeCheck.circuit, Gadgets.ToBits.rangeCheck]
  subcircuitsConsistent := by
    intro input offset
    simp +arith only [main, interpolatedMul, circuit_norm, Normalize.circuit, Normalize.elaborated,
      Normalize.main, GroupedEqXV.circuit, GroupedEqXV.elaborated,
      LessThan.circuit, LessThan.elaborated, LessThan.main, RangeCheck.circuit, Gadgets.ToBits.rangeCheck]
  channelsLawful := by
    intro input offset
    simp only [main, interpolatedMul, circuit_norm, Normalize.circuit, Normalize.elaborated,
      Normalize.main, GroupedEqXV.circuit, GroupedEqXV.elaborated,
      LessThan.circuit, LessThan.elaborated, LessThan.main, RangeCheck.circuit, Gadgets.ToBits.rangeCheck]


def Assumptions (B : ℕ) (input : Inputs m (F p)) : Prop :=
  let a := input.a
  let b := input.b
  let n := input.modulus
  a.Normalized B ∧ b.Normalized B ∧ n.Normalized B ∧
    a.value B < n.value B ∧ b.value B < n.value B ∧ 0 < n.value B


def Spec (B : ℕ) (input : Inputs m (F p)) (out : BigInt m (F p)) : Prop :=
  let a := input.a
  let b := input.b
  let n := input.modulus
  out.Normalized B ∧ out.value B = (a.value B * b.value B) % n.value B



def circuit (P : BigIntParams p m)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqXV.GVXHyps p (2 * m - 1) P.B gf posOf G V VR)
    (hNf : ∀ j, V.Nf j = (m + 1) * 2 ^ (2 * P.B))
    (hNfR : ∀ j, VR.Nf j = (m + 1) * 2 ^ (2 * P.B))
    [Fact (p > 2)] :
    FormalCircuit (F p) (Inputs m) (BigInt m) where
    main := main P gf posOf G V VR hgv
    Assumptions := Assumptions P.B
    Spec := Spec P.B
    soundness := by
      obtain ⟨B, W, hB, hW, hB1, hWB, hWp, hp⟩ := P
      circuit_proof_start [Normalize.circuit, Normalize.elaborated, Normalize.main,
        Normalize.Assumptions, Normalize.Spec,
        GroupedEqXV.circuit, GroupedEqXV.elaborated,
        GroupedEqXV.Assumptions, GroupedEqX.Spec,
        LessThan.circuit, LessThan.elaborated, LessThan.main,
        LessThan.Assumptions, LessThan.Spec]
      obtain ⟨ha_norm, hb_norm, hn_norm, hab_lt, hbb_lt, hn_pos⟩ := h_assumptions
      obtain ⟨hq_norm, hr_norm, hAB_ops, h_eq_impl, h_lt_impl⟩ := h_holds
      simp only [hNf, hNfR] at h_eq_impl
      have hpm : 2 * m - 1 < p := two_m_sub_one_lt hp
      -- fully explicit offsets/outputs: never let Lean `whnf` the loop offset
      have h_pAB := interpolatedMul_soundness (i₀ + m + m + m * (B - 1) + m * (B - 1))
        input_var.a input_var.b env hAB_ops
      refine ⟨?_, interpolatedMul_requirements _ _ _ _⟩
      have h_input' : (Vector.map (Expression.eval env) input_var.a,
          Vector.map (Expression.eval env) input_var.b,
          Vector.map (Expression.eval env) input_var.modulus)
            = ((input.a, input.b, input.modulus) :
              ProvablePair (BigInt m) (ProvablePair (BigInt m) (BigInt m)) (F p)) := by
        simp only [← h_input]
      have heqAB_get := interpolatedMul_eval_bridge env (i₀ + m + m + m * (B - 1) + m * (B - 1))
        input_var.a input_var.b hpm h_pAB
      exact mulMod_soundness_core_wm (B := B) hp i₀ env
        input_var.a input_var.b input_var.modulus
        (interpolatedMul input_var.a input_var.b (i₀ + m + m + m * (B - 1) + m * (B - 1))).1
        (bigIntMulNoReduce (Vector.mapRange m fun i => var { index := i₀ + i })
          input_var.modulus)
        (input.a, input.b, input.modulus) h_input' ha_norm hb_norm hn_norm hq_norm hr_norm
        heqAB_get (fun _ => rfl) h_eq_impl h_lt_impl
    completeness := by
      obtain ⟨B, W, hB, hW, hB1, hWB, hWp, hp⟩ := P
      circuit_proof_start [Normalize.circuit, Normalize.elaborated, Normalize.main,
        Normalize.Assumptions, Normalize.Spec,
        GroupedEqXV.circuit, GroupedEqXV.elaborated,
        GroupedEqXV.Assumptions, GroupedEqX.Spec,
        LessThan.circuit, LessThan.elaborated, LessThan.main,
        LessThan.Assumptions, LessThan.Spec]
      obtain ⟨ha_norm, hb_norm, hn_norm, hab_lt, hbb_lt, hn_pos⟩ := h_assumptions
      obtain ⟨hq_env, hr_env, hAB_uses⟩ := h_env
      have h_pvAB := interpolatedMul_usesLocalWitnesses (i₀ + m + m + m * (B - 1) + m * (B - 1))
        (i₀ + m + m + m * (B - 1) + m * (B - 1)) input_var.a input_var.b env rfl hAB_uses
      have heva : evalValue B env input_var.a = BigInt.value B input.a := by
        rw [evalValue, BigInt.value, ← h_input]
      have hevb : evalValue B env input_var.b = BigInt.value B input.b := by
        rw [evalValue, BigInt.value, ← h_input]
      have hevn : evalValue B env input_var.modulus = BigInt.value B input.modulus := by
        rw [evalValue, BigInt.value, ← h_input]
      have hqwit : ∀ i : Fin m, env.toEnvironment.get (i₀ + i.val)
          = ((BigInt.value B input.a * BigInt.value B input.b / BigInt.value B input.modulus
              / 2 ^ (B * i.val) % 2 ^ B : ℕ) : F p) := by
        intro i; rw [hq_env i, Vector.getElem_ofFn, heva, hevb, hevn]
      have hrwit : ∀ i : Fin m, env.toEnvironment.get (i₀ + m + i.val)
          = ((BigInt.value B input.a * BigInt.value B input.b % BigInt.value B input.modulus
              / 2 ^ (B * i.val) % 2 ^ B : ℕ) : F p) := by
        intro i; rw [hr_env i, Vector.getElem_ofFn, heva, hevb, hevn]
      have h_input' : (Vector.map (Expression.eval env.toEnvironment) input_var.a,
          Vector.map (Expression.eval env.toEnvironment) input_var.b,
          Vector.map (Expression.eval env.toEnvironment) input_var.modulus)
            = ((input.a, input.b, input.modulus) :
              ProvablePair (BigInt m) (ProvablePair (BigInt m) (BigInt m)) (F p)) := by
        simp only [← h_input]
      have heqAB_get := interpolatedMul_eval_bridge_uses env.toEnvironment
        (i₀ + m + m + m * (B - 1) + m * (B - 1)) input_var.a input_var.b h_pvAB
      have core := mulMod_completeness_core_wm (B := B) hB hp i₀ env.toEnvironment
        input_var.a input_var.b input_var.modulus
        (interpolatedMul input_var.a input_var.b (i₀ + m + m + m * (B - 1) + m * (B - 1))).1
        (bigIntMulNoReduce (Vector.mapRange m fun i => var { index := i₀ + i })
          input_var.modulus)
        (input.a, input.b, input.modulus) h_input' ha_norm hb_norm hn_norm hab_lt hbb_lt hn_pos
        hqwit hrwit heqAB_get (fun _ => rfl)
      -- single explicit `exact` (lazy `.1/.2` projections; no eager `obtain` ⇒ no `whnf` blowup)
      simp only [hNf, hNfR]
      exact ⟨core.1, core.2.1,
        interpolatedMul_completeness (i₀ + m + m + m * (B - 1) + m * (B - 1))
          input_var.a input_var.b env h_pvAB,
        core.2.2⟩



lemma evalValue_stable (B : ℕ) (x : Var (BigInt m) (F p))
    {env env' : ProverEnvironment (F p)}
    (h : eval env x = eval env' x) :
    evalValue B env x = evalValue B env' x := by
  have h_vec :
      x.map (Expression.eval env.toEnvironment)
        = x.map (Expression.eval env'.toEnvironment) := by
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_map]
    have h_i := congrArg (fun y : BigInt m (F p) => y[i]) h
    rw [ProvableType.getElem_eval_fields_prover (env := env) x i hi,
      ProvableType.getElem_eval_fields_prover (env := env') x i hi]
    exact h_i
  simp [evalValue, h_vec]

lemma bigIntWitnessOutput_stable
    (compute : ProverEnvironment (F p) → BigInt m (F p))
    {offset k : ℕ} {env env' : ProverEnvironment (F p)}
    (h_agree : env.AgreesBelow k env') (hk : offset + m ≤ k) :
    eval env
        ((ProvableType.witness (α := BigInt m) compute).output offset)
      = eval env'
        ((ProvableType.witness (α := BigInt m) compute).output offset) := by
  apply Vector.ext
  intro i hi
  rw [← ProvableType.getElem_eval_fields_prover (env := env) _ i hi,
    ← ProvableType.getElem_eval_fields_prover (env := env') _ i hi]
  simp only [Circuit.output, ProvableType.witness, ProvableType.varFromOffset_fields,
    Vector.getElem_mapRange, Expression.eval]
  exact h_agree (offset + i) (by omega)


lemma bigInt_map_eval_eq_of_eval_eq {x : Var (BigInt m) (F p)}
    {env env' : ProverEnvironment (F p)} (h : eval env x = eval env' x) :
    x.map (Expression.eval env.toEnvironment) = x.map (Expression.eval env'.toEnvironment) := by
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_map]
  rw [ProvableType.getElem_eval_fields_prover (env := env) x i hi,
    ProvableType.getElem_eval_fields_prover (env := env') x i hi]
  exact congrArg (fun y : BigInt m (F p) => y[i]) h


lemma bigInt_getElem_eval_eq {x : Var (BigInt m) (F p)}
    {env env' : ProverEnvironment (F p)} (h : eval env x = eval env' x)
    (i : ℕ) (hi : i < m) :
    Expression.eval env.toEnvironment (x[i]'hi)
      = Expression.eval env'.toEnvironment (x[i]'hi) := by
  have := congrArg (fun v : Vector (F p) m => v[i]'hi) (bigInt_map_eval_eq_of_eval_eq h)
  simpa only [Vector.getElem_map] using this


lemma bigIntMulNoReduce_coeff_stable (env env' : Environment (F p))
    (a b : Var (BigInt m) (F p))
    (ha : ∀ (i : ℕ) (hi : i < m),
      Expression.eval env (a[i]'hi) = Expression.eval env' (a[i]'hi))
    (hb : ∀ (i : ℕ) (hi : i < m),
      Expression.eval env (b[i]'hi) = Expression.eval env' (b[i]'hi))
    (k : Fin (2 * m - 1)) :
    Expression.eval env ((bigIntMulNoReduce a b)[k.val])
      = Expression.eval env' ((bigIntMulNoReduce a b)[k.val]) := by
  rw [eval_bigIntMulNoReduce_coeff, eval_bigIntMulNoReduce_coeff]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : i.val ≤ k.val ∧ k.val - i.val < m
  · simp only [dif_pos h]
    rw [ha i.val i.isLt, hb (k.val - i.val) h.2]
  · simp only [dif_neg h]


lemma interpolatedMul_structuralComputableWitnesses
    {Parent : TypeMap} [CircuitType Parent] (parentInput : Var Parent (F p))
    (a b : Var (BigInt m) (F p)) (offset : ℕ)
    (hinput : ∀ (k : ℕ) (env env' : ProverEnvironment (F p)),
      offset ≤ k →
      env.AgreesBelow k env' →
      eval env parentInput = eval env' parentInput →
        eval env a = eval env' a ∧ eval env b = eval env' b) :
    ∀ env env',
      Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.StructuralComputableWitnesses
        parentInput env env' offset ((interpolatedMul a b).operations offset) := by
  intro env env'
  unfold interpolatedMul
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
    exact bigIntMulNoReduce_coeff_stable env.toEnvironment env'.toEnvironment a b
      (fun i hi => bigInt_getElem_eval_eq ha i hi)
      (fun i hi => bigInt_getElem_eval_eq hb i hi) ⟨t, ht⟩
  · intro _
    trivial


lemma interpolatedMul_output_stable
    (off : ℕ) (a b : Var (BigInt m) (F p))
    {k : ℕ} {env env' : ProverEnvironment (F p)}
    (h_agree : env.AgreesBelow k env') (hk : off + (2 * m - 1) ≤ k) :
    Vector.map (Expression.eval env.toEnvironment) (interpolatedMul a b off).1
      = Vector.map (Expression.eval env'.toEnvironment) (interpolatedMul a b off).1 := by
  rw [interpolatedMul_output off a b]
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_map, Vector.getElem_mapRange, Expression.eval]
  exact h_agree (off + i) (by omega)

-- Keep `interpolatedMul` and the child gadgets opaque during the structural
-- peel so `bind`/`provableWitness`/`assertion` do not recurse into their
-- internal witnesses; each block is discharged through its own
-- `*ComputableWitnesses` theorem instead.
attribute [local irreducible] interpolatedMul Normalize.circuit GroupedEqXV.circuit LessThan.circuit

theorem computableWitnesses (P : BigIntParams p m)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqXV.GVXHyps p (2 * m - 1) P.B gf posOf G V VR)
    (hNf : ∀ j, V.Nf j = (m + 1) * 2 ^ (2 * P.B))
    (hNfR : ∀ j, VR.Nf j = (m + 1) * 2 ^ (2 * P.B))
    [Fact (p > 2)] :
    (circuit P gf posOf G V VR hgv hNf hNfR).ComputableWitnesses := by
  letI : NeZero (2 * m - 1) := ⟨by have := Nat.pos_of_neZero m; omega⟩
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition input env env')
    ((main P gf posOf G V VR hgv input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main
  -- name each block, its output, and its starting offset
  let qc : Circuit (F p) (Var (BigInt m) (F p)) := ProvableType.witness (α := BigInt m) fun env =>
    let prod := evalValue P.B env input.a * evalValue P.B env input.b
    let qval : ℕ := prod / evalValue P.B env input.modulus
    Vector.ofFn fun k : Fin m => ((qval / 2 ^ (P.B * k.val) % 2 ^ P.B : ℕ) : F p)
  let q := qc.output offset
  let rOff := offset + qc.localLength offset
  let rc : Circuit (F p) (Var (BigInt m) (F p)) := ProvableType.witness (α := BigInt m) fun env =>
    let prod := evalValue P.B env input.a * evalValue P.B env input.b
    let rval : ℕ := prod % evalValue P.B env input.modulus
    Vector.ofFn fun k : Fin m => ((rval / 2 ^ (P.B * k.val) % 2 ^ P.B : ℕ) : F p)
  let r := rc.output rOff
  let nqOff := rOff + rc.localLength rOff
  let nqc : Circuit (F p) Unit := Normalize.circuit P q
  let nrOff := nqOff + nqc.localLength nqOff
  let nrc : Circuit (F p) Unit := Normalize.circuit P r
  let pcOff := nrOff + nrc.localLength nrOff
  let pcv := (interpolatedMul input.a input.b).output pcOff
  let eqOff := pcOff + (interpolatedMul input.a input.b).localLength pcOff
  let Sqn : Vector (Expression (F p)) (2 * m - 1) := bigIntMulNoReduce q input.modulus
  let Sv : Vector (Expression (F p)) (2 * m - 1) := Vector.mapFinRange (2 * m - 1) fun k =>
    if h : k.val < m then Sqn[k.val] + r[k.val]'h else Sqn[k.val]
  let eqc : Circuit (F p) Unit :=
    GroupedEqXV.circuit P.B gf posOf G V VR hgv P.hB1 { lhs := pcv, rhs := Sv }
  let ltOff := eqOff + eqc.localLength eqOff
  have h_qlen : qc.localLength offset = m := by
    simp [qc, ProvableType.witness, Circuit.localLength, Operations.localLength, size]
  have h_rlen : rc.localLength rOff = m := by
    simp [rc, ProvableType.witness, Circuit.localLength, Operations.localLength, size]
  have h_pclen : (interpolatedMul input.a input.b).localLength pcOff = 2 * m - 1 :=
    interpolatedMul_localLength pcOff input.a input.b
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.provableWitness_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.pure_structuralComputableWitnesses_iff,
    and_true]
  and_intros
  · -- q witness reads only the input
    intro _ h_input
    have ha : evalValue P.B env input.a = evalValue P.B env' input.a :=
      evalValue_stable P.B input.a (by
        simpa [circuit_norm] using congrArg (fun x : Inputs m (F p) => x.a) h_input)
    have hb : evalValue P.B env input.b = evalValue P.B env' input.b :=
      evalValue_stable P.B input.b (by
        simpa [circuit_norm] using congrArg (fun x : Inputs m (F p) => x.b) h_input)
    have hn : evalValue P.B env input.modulus = evalValue P.B env' input.modulus :=
      evalValue_stable P.B input.modulus (by
        simpa [circuit_norm] using congrArg (fun x : Inputs m (F p) => x.modulus) h_input)
    simp only [ha, hb, hn]
  · -- r witness reads only the input
    intro _ h_input
    have ha : evalValue P.B env input.a = evalValue P.B env' input.a :=
      evalValue_stable P.B input.a (by
        simpa [circuit_norm] using congrArg (fun x : Inputs m (F p) => x.a) h_input)
    have hb : evalValue P.B env input.b = evalValue P.B env' input.b :=
      evalValue_stable P.B input.b (by
        simpa [circuit_norm] using congrArg (fun x : Inputs m (F p) => x.b) h_input)
    have hn : evalValue P.B env input.modulus = evalValue P.B env' input.modulus :=
      evalValue_stable P.B input.modulus (by
        simpa [circuit_norm] using congrArg (fun x : Inputs m (F p) => x.modulus) h_input)
    simp only [ha, hb, hn]
  · -- Normalize q (q is the first witness output)
    exact Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
      (Normalize.circuit P) input q nqOff
      (by
        intro k env env' hle h_agree _
        have hk : offset + m ≤ k := by
          dsimp only [nqOff, rOff] at hle
          rw [h_qlen] at hle
          omega
        exact bigIntWitnessOutput_stable _ h_agree hk)
      (Normalize.computableWitnesses P) env env'
  · -- Normalize r (r is the second witness output)
    exact Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
      (Normalize.circuit P) input r nrOff
      (by
        intro k env env' hle h_agree _
        have hk : rOff + m ≤ k := by
          dsimp only [nrOff, nqOff] at hle
          rw [h_rlen] at hle
          omega
        exact bigIntWitnessOutput_stable _ h_agree hk)
      (Normalize.computableWitnesses P) env env'
  · -- interpolatedMul a b : both operands are raw inputs
    exact interpolatedMul_structuralComputableWitnesses input input.a input.b pcOff
      (by
        intro k env env' _ _ h_input
        have ha : eval env input.a = eval env' input.a := by
          simpa [circuit_norm] using congrArg (fun x : Inputs m (F p) => x.a) h_input
        have hb : eval env input.b = eval env' input.b := by
          simpa [circuit_norm] using congrArg (fun x : Inputs m (F p) => x.b) h_input
        exact ⟨ha, hb⟩)
      env env'
  · -- GroupedEqXV: lhs = Pc (interpolated coefficients), rhs = S (q·n + r)
    exact Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
      (GroupedEqXV.circuit P.B gf posOf G V VR hgv P.hB1) input { lhs := pcv, rhs := Sv } eqOff
      (by
        intro k env env' hle h_agree h_input
        have hk_pc : pcOff + (2 * m - 1) ≤ k := by
          dsimp only [eqOff] at hle
          rw [h_pclen] at hle
          omega
        have hk_q : offset + m ≤ k := by
          dsimp only [eqOff, pcOff, nrOff, nqOff, rOff] at hle
          rw [h_qlen] at hle
          omega
        have hk_r : rOff + m ≤ k := by
          dsimp only [eqOff, pcOff, nrOff, nqOff] at hle
          rw [h_rlen] at hle
          omega
        have hPc : Vector.map (Expression.eval env.toEnvironment) pcv
            = Vector.map (Expression.eval env'.toEnvironment) pcv :=
          interpolatedMul_output_stable pcOff input.a input.b h_agree hk_pc
        have hq_vec : eval env q = eval env' q := bigIntWitnessOutput_stable _ h_agree hk_q
        have hr_vec : eval env r = eval env' r := bigIntWitnessOutput_stable _ h_agree hk_r
        have hn : eval env input.modulus = eval env' input.modulus := by
          simpa [circuit_norm] using congrArg (fun x : Inputs m (F p) => x.modulus) h_input
        have hr_map : r.map (Expression.eval env.toEnvironment)
            = r.map (Expression.eval env'.toEnvironment) := bigInt_map_eval_eq_of_eval_eq hr_vec
        have hS : Vector.map (Expression.eval env.toEnvironment) Sv
            = Vector.map (Expression.eval env'.toEnvironment) Sv := by
          apply Vector.ext
          intro i hi
          have hsq_i : Expression.eval env.toEnvironment Sqn[i]
              = Expression.eval env'.toEnvironment Sqn[i] :=
            bigIntMulNoReduce_coeff_stable env.toEnvironment env'.toEnvironment q input.modulus
              (fun j hj => bigInt_getElem_eval_eq hq_vec j hj)
              (fun j hj => bigInt_getElem_eval_eq hn j hj) ⟨i, hi⟩
          simp only [Vector.getElem_map, Sv, Vector.getElem_mapFinRange]
          split
          · rename_i hlt
            have hr_i : Expression.eval env.toEnvironment (r[i]'hlt)
                = Expression.eval env'.toEnvironment (r[i]'hlt) := by
              have := congrArg (fun v : Vector (F p) m => v[i]'hlt) hr_map
              simpa only [Vector.getElem_map] using this
            simp only [Expression.eval, hsq_i, hr_i]
          · exact hsq_i
        simp only [circuit_norm]
        rw [hPc, hS])
      (GroupedEqXV.computableWitnesses P.B gf posOf G V VR hgv P.hB1) env env'
  · -- LessThan: lhs = r (prior witness output), rhs = n (raw input)
    exact Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
      (LessThan.circuit P) input { lhs := r, rhs := input.modulus } ltOff
      (by
        intro k env env' hle h_agree h_input
        have hk_r : rOff + m ≤ k := by
          dsimp only [ltOff, eqOff, pcOff, nrOff, nqOff] at hle
          rw [h_rlen] at hle
          omega
        have hr_vec : eval env r = eval env' r := bigIntWitnessOutput_stable _ h_agree hk_r
        have hn : eval env input.modulus = eval env' input.modulus := by
          simpa [circuit_norm] using congrArg (fun x : Inputs m (F p) => x.modulus) h_input
        simp only [circuit_norm]
        rw [bigInt_map_eval_eq_of_eval_eq hr_vec, bigInt_map_eval_eq_of_eval_eq hn])
      (LessThan.computableWitnesses P) env env'

end MulMod

namespace MulModTarget
open MulMod


structure Inputs (m : ℕ) (F : Type) where
  a : BigInt m F
  b : BigInt m F
  modulus : BigInt m F
  target : BigInt m F
deriving ProvableStruct


def main (P : BigIntParams p m)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqXV.GVXHyps p (2 * m - 1) P.B gf posOf G V VR)
    [Fact (p > 2)]
    (input : Var (Inputs m) (F p)) :
    Circuit (F p) Unit :=
  letI : NeZero (2 * m - 1) := ⟨by have := Nat.pos_of_neZero m; omega⟩
  do
  let a := input.a
  let b := input.b
  let n := input.modulus
  let t := input.target

  -- 1. witness q = (a·b)/n as BigInt m
  let q ← ProvableType.witness (α := BigInt m) fun env =>
    let prod := evalValue P.B env a * evalValue P.B env b
    let qval : ℕ := prod / evalValue P.B env n
    Vector.ofFn fun k : Fin m => ((qval / 2 ^ (P.B * k.val) % 2 ^ P.B : ℕ) : F p)

  -- 2. normalize q
  Normalize.circuit P q

  -- 3. Pc = a·b via the interpolation check; Sqn = q·n as the direct
  --    schoolbook convolution (constant modulus limbs keep it affine)
  let Pc ← interpolatedMul a b
  let Sqn : Vector (Expression (F p)) (2 * m - 1) := bigIntMulNoReduce q n
  let S : Vector (Expression (F p)) (2 * m - 1) := Vector.mapFinRange (2 * m - 1) fun k =>
    if h : k.val < m then Sqn[k.val] + t[k.val]'h else Sqn[k.val]

  -- 4. certify a·b = q·n + target as integers via the grouped equality
  GroupedEqXV.circuit P.B gf posOf G V VR hgv P.hB1 { lhs := Pc, rhs := S }

instance elaborated (P : BigIntParams p m)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqXV.GVXHyps p (2 * m - 1) P.B gf posOf G V VR)
    [Fact (p > 2)] :
    ElaboratedCircuit (F p) (Inputs m) unit (main P gf posOf G V VR hgv) where
  -- q (m) + normalize q (m*B) + interpolatedMul a b (2m−1)
  --   + groupedEqXV (Σ (Wf k − 1))
  localLength _ :=
    m + m * (P.B - 1) + (2 * m - 1) + GroupedEqXV.widthAllocFrom V.Wf (G - 2) 0
  localLength_eq := by
    intro input offset
    simp only [main, interpolatedMul, circuit_norm, Normalize.circuit, Normalize.elaborated,
      Normalize.main, GroupedEqXV.circuit, GroupedEqXV.elaborated,
      RangeCheck.circuit, Gadgets.ToBits.rangeCheck]
    omega
  subcircuitsConsistent := by
    intro input offset
    simp +arith only [main, interpolatedMul, circuit_norm, Normalize.circuit, Normalize.elaborated,
      Normalize.main, GroupedEqXV.circuit, GroupedEqXV.elaborated,
      RangeCheck.circuit, Gadgets.ToBits.rangeCheck]
  channelsLawful := by
    intro offset
    simp only [main, interpolatedMul, circuit_norm, Normalize.circuit, Normalize.elaborated,
      Normalize.main, GroupedEqXV.circuit, GroupedEqXV.elaborated,
      RangeCheck.circuit, Gadgets.ToBits.rangeCheck]


def Assumptions (B : ℕ) (input : Inputs m (F p)) : Prop :=
  input.a.Normalized B ∧ input.b.Normalized B ∧ input.modulus.Normalized B ∧
    input.target.Normalized B ∧
    input.a.value B < input.modulus.value B ∧
    input.b.value B < input.modulus.value B ∧
    input.target.value B < input.modulus.value B ∧
    0 < input.modulus.value B


def Spec (B : ℕ) (input : Inputs m (F p)) : Prop :=
  input.target.value B = (input.a.value B * input.b.value B) % input.modulus.value B


def circuit (P : BigIntParams p m)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqXV.GVXHyps p (2 * m - 1) P.B gf posOf G V VR)
    (hNf : ∀ j, V.Nf j = (m + 1) * 2 ^ (2 * P.B))
    (hNfR : ∀ j, VR.Nf j = (m + 1) * 2 ^ (2 * P.B))
    [Fact (p > 2)] :
    FormalAssertion (F p) (Inputs m) where
    main := main P gf posOf G V VR hgv
    Assumptions := Assumptions P.B
    Spec := Spec P.B
    soundness := by
      obtain ⟨B, W, hB, hW, hB1, hWB, hWp, hp⟩ := P
      circuit_proof_start [Normalize.circuit, Normalize.elaborated, Normalize.main,
        Normalize.Assumptions, Normalize.Spec,
        GroupedEqXV.circuit, GroupedEqXV.elaborated,
        GroupedEqXV.Assumptions, GroupedEqX.Spec]
      obtain ⟨ha_norm, hb_norm, hn_norm, ht_norm, hab_lt, hbb_lt, ht_lt, hn_pos⟩ := h_assumptions
      obtain ⟨hq_norm, hAB_ops, h_eq_impl⟩ := h_holds
      simp only [hNf, hNfR] at h_eq_impl
      have hpm : 2 * m - 1 < p := two_m_sub_one_lt hp
      have h_pAB := interpolatedMul_soundness (i₀ + m + m * (B - 1))
        input_var.a input_var.b env hAB_ops
      refine ⟨?_, interpolatedMul_requirements _ _ _ _⟩
      have ha_input : Vector.map (Expression.eval env) input_var.a = input.a := by
        rw [← h_input]
      have hb_input : Vector.map (Expression.eval env) input_var.b = input.b := by
        rw [← h_input]
      have hn_input : Vector.map (Expression.eval env) input_var.modulus = input.modulus := by
        rw [← h_input]
      have ht_input : Vector.map (Expression.eval env) input_var.target = input.target := by
        rw [← h_input]
      have heqAB_get := interpolatedMul_eval_bridge env (i₀ + m + m * (B - 1))
        input_var.a input_var.b hpm h_pAB
      exact mulModTarget_soundness_core_wm (B := B) hp i₀ env
        input_var.a input_var.b input_var.modulus input_var.target
        (interpolatedMul input_var.a input_var.b (i₀ + m + m * (B - 1))).1
        input.a input.b input.modulus input.target
        ha_input hb_input hn_input ht_input
        ha_norm hb_norm hn_norm ht_norm ht_lt hq_norm
        heqAB_get h_eq_impl
    completeness := by
      obtain ⟨B, W, hB, hW, hB1, hWB, hWp, hp⟩ := P
      circuit_proof_start [Normalize.circuit, Normalize.elaborated, Normalize.main,
        Normalize.Assumptions, Normalize.Spec,
        GroupedEqXV.circuit, GroupedEqXV.elaborated,
        GroupedEqXV.Assumptions, GroupedEqX.Spec]
      obtain ⟨ha_norm, hb_norm, hn_norm, ht_norm, hab_lt, hbb_lt, ht_lt, hn_pos⟩ := h_assumptions
      obtain ⟨hq_env, hAB_uses⟩ := h_env
      have h_pvAB := interpolatedMul_usesLocalWitnesses (i₀ + m + m * (B - 1))
        (i₀ + m + m * (B - 1)) input_var.a input_var.b env rfl hAB_uses
      have ha_input : Vector.map (Expression.eval env.toEnvironment) input_var.a = input.a := by
        rw [← h_input]
      have hb_input : Vector.map (Expression.eval env.toEnvironment) input_var.b = input.b := by
        rw [← h_input]
      have hn_input : Vector.map (Expression.eval env.toEnvironment) input_var.modulus
          = input.modulus := by
        rw [← h_input]
      have ht_input : Vector.map (Expression.eval env.toEnvironment) input_var.target
          = input.target := by
        rw [← h_input]
      have heva : evalValue B env input_var.a = BigInt.value B input.a := by
        rw [evalValue, BigInt.value, ← ha_input]
      have hevb : evalValue B env input_var.b = BigInt.value B input.b := by
        rw [evalValue, BigInt.value, ← hb_input]
      have hevn : evalValue B env input_var.modulus = BigInt.value B input.modulus := by
        rw [evalValue, BigInt.value, ← hn_input]
      have hqwit : ∀ i : Fin m, env.toEnvironment.get (i₀ + i.val)
          = ((BigInt.value B input.a * BigInt.value B input.b / BigInt.value B input.modulus
              / 2 ^ (B * i.val) % 2 ^ B : ℕ) : F p) := by
        intro i; rw [hq_env i, Vector.getElem_ofFn, heva, hevb, hevn]
      have heqAB_get := interpolatedMul_eval_bridge_uses env.toEnvironment
        (i₀ + m + m * (B - 1)) input_var.a input_var.b h_pvAB
      have core := mulModTarget_completeness_core_wm (B := B) hB hp i₀ env.toEnvironment
        input_var.a input_var.b input_var.modulus input_var.target
        (interpolatedMul input_var.a input_var.b (i₀ + m + m * (B - 1))).1
        input.a input.b input.modulus input.target
        ha_input hb_input hn_input ht_input
        ha_norm hb_norm hn_norm ht_norm hab_lt hbb_lt hn_pos h_spec
        hqwit heqAB_get
      simp only [hNf, hNfR]
      exact ⟨core.1,
        interpolatedMul_completeness (i₀ + m + m * (B - 1)) input_var.a input_var.b env h_pvAB,
        core.2⟩



attribute [local irreducible] interpolatedMul Normalize.circuit GroupedEqXV.circuit

theorem computableWitnesses (P : BigIntParams p m)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqXV.GVXHyps p (2 * m - 1) P.B gf posOf G V VR)
    (hNf : ∀ j, V.Nf j = (m + 1) * 2 ^ (2 * P.B))
    (hNfR : ∀ j, VR.Nf j = (m + 1) * 2 ^ (2 * P.B))
    [Fact (p > 2)] :
    (circuit P gf posOf G V VR hgv hNf hNfR).ComputableWitnesses := by
  letI : NeZero (2 * m - 1) := ⟨by have := Nat.pos_of_neZero m; omega⟩
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition input env env')
    ((main P gf posOf G V VR hgv input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main
  let qc : Circuit (F p) (Var (BigInt m) (F p)) := ProvableType.witness (α := BigInt m) fun env =>
    let prod := evalValue P.B env input.a * evalValue P.B env input.b
    let qval : ℕ := prod / evalValue P.B env input.modulus
    Vector.ofFn fun k : Fin m => ((qval / 2 ^ (P.B * k.val) % 2 ^ P.B : ℕ) : F p)
  let q := qc.output offset
  let nqOff := offset + qc.localLength offset
  let nqc : Circuit (F p) Unit := Normalize.circuit P q
  let pcOff := nqOff + nqc.localLength nqOff
  let pcv := (interpolatedMul input.a input.b).output pcOff
  let eqOff := pcOff + (interpolatedMul input.a input.b).localLength pcOff
  let Sqn : Vector (Expression (F p)) (2 * m - 1) := bigIntMulNoReduce q input.modulus
  let Sv : Vector (Expression (F p)) (2 * m - 1) := Vector.mapFinRange (2 * m - 1) fun k =>
    if h : k.val < m then Sqn[k.val] + input.target[k.val]'h else Sqn[k.val]
  have h_qlen : qc.localLength offset = m := by
    simp [qc, ProvableType.witness, Circuit.localLength, Operations.localLength, size]
  have h_pclen : (interpolatedMul input.a input.b).localLength pcOff = 2 * m - 1 :=
    interpolatedMul_localLength pcOff input.a input.b
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.provableWitness_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.pure_structuralComputableWitnesses_iff,
    and_true]
  and_intros
  · -- q witness reads only the input
    intro _ h_input
    have ha : evalValue P.B env input.a = evalValue P.B env' input.a :=
      evalValue_stable P.B input.a (by
        simpa [circuit_norm] using congrArg (fun x : Inputs m (F p) => x.a) h_input)
    have hb : evalValue P.B env input.b = evalValue P.B env' input.b :=
      evalValue_stable P.B input.b (by
        simpa [circuit_norm] using congrArg (fun x : Inputs m (F p) => x.b) h_input)
    have hn : evalValue P.B env input.modulus = evalValue P.B env' input.modulus :=
      evalValue_stable P.B input.modulus (by
        simpa [circuit_norm] using congrArg (fun x : Inputs m (F p) => x.modulus) h_input)
    simp only [ha, hb, hn]
  · -- Normalize q
    exact Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
      (Normalize.circuit P) input q nqOff
      (by
        intro k env env' hle h_agree _
        have hk : offset + m ≤ k := by
          dsimp only [nqOff] at hle
          rw [h_qlen] at hle
          omega
        exact bigIntWitnessOutput_stable _ h_agree hk)
      (Normalize.computableWitnesses P) env env'
  · -- interpolatedMul a b
    exact interpolatedMul_structuralComputableWitnesses input input.a input.b pcOff
      (by
        intro k env env' _ _ h_input
        have ha : eval env input.a = eval env' input.a := by
          simpa [circuit_norm] using congrArg (fun x : Inputs m (F p) => x.a) h_input
        have hb : eval env input.b = eval env' input.b := by
          simpa [circuit_norm] using congrArg (fun x : Inputs m (F p) => x.b) h_input
        exact ⟨ha, hb⟩)
      env env'
  · -- GroupedEqXV: lhs = Pc, rhs = S (q·n + target)
    exact Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
      (GroupedEqXV.circuit P.B gf posOf G V VR hgv P.hB1) input { lhs := pcv, rhs := Sv } eqOff
      (by
        intro k env env' hle h_agree h_input
        have hk_pc : pcOff + (2 * m - 1) ≤ k := by
          dsimp only [eqOff] at hle
          rw [h_pclen] at hle
          omega
        have hk_q : offset + m ≤ k := by
          dsimp only [eqOff, pcOff, nqOff] at hle
          rw [h_qlen] at hle
          omega
        have hPc : Vector.map (Expression.eval env.toEnvironment) pcv
            = Vector.map (Expression.eval env'.toEnvironment) pcv :=
          interpolatedMul_output_stable pcOff input.a input.b h_agree hk_pc
        have hq_vec : eval env q = eval env' q := bigIntWitnessOutput_stable _ h_agree hk_q
        have hn : eval env input.modulus = eval env' input.modulus := by
          simpa [circuit_norm] using congrArg (fun x : Inputs m (F p) => x.modulus) h_input
        have ht : eval env input.target = eval env' input.target := by
          simpa [circuit_norm] using congrArg (fun x : Inputs m (F p) => x.target) h_input
        have hS : Vector.map (Expression.eval env.toEnvironment) Sv
            = Vector.map (Expression.eval env'.toEnvironment) Sv := by
          apply Vector.ext
          intro i hi
          have hsq_i : Expression.eval env.toEnvironment Sqn[i]
              = Expression.eval env'.toEnvironment Sqn[i] :=
            bigIntMulNoReduce_coeff_stable env.toEnvironment env'.toEnvironment q input.modulus
              (fun j hj => bigInt_getElem_eval_eq hq_vec j hj)
              (fun j hj => bigInt_getElem_eval_eq hn j hj) ⟨i, hi⟩
          simp only [Vector.getElem_map, Sv, Vector.getElem_mapFinRange]
          split
          · rename_i hlt
            have ht_i : Expression.eval env.toEnvironment (input.target[i]'hlt)
                = Expression.eval env'.toEnvironment (input.target[i]'hlt) :=
              bigInt_getElem_eval_eq ht i hlt
            simp only [Expression.eval, hsq_i, ht_i]
          · exact hsq_i
        simp only [circuit_norm]
        rw [hPc, hS])
      (GroupedEqXV.computableWitnesses P.B gf posOf G V VR hgv P.hB1) env env'

end MulModTarget

namespace MulModTarget3
open MulMod


def main (P : BigIntParams p m)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqXV.GVXHyps p (2 * m - 1) P.B gf posOf G V VR)
    (c : Vector (F p) (2 * m - 1))
    [Fact (p > 2)]
    (input : Var (MulModTarget.Inputs m) (F p)) :
    Circuit (F p) Unit :=
  letI : NeZero (2 * m - 1) := ⟨by have := Nat.pos_of_neZero m; omega⟩
  do
  let a := input.a
  let b := input.b
  let n := input.modulus
  let t := input.target

  -- 1. witness q = (a·b + 3n − t)/n as BigInt m
  let q ← ProvableType.witness (α := BigInt m) fun env =>
    let qval : ℕ := (evalValue P.B env a * evalValue P.B env b
        + 3 * evalValue P.B env n - evalValue P.B env t) / evalValue P.B env n
    Vector.ofFn fun k : Fin m => ((qval / 2 ^ (P.B * k.val) % 2 ^ P.B : ℕ) : F p)

  -- 2. normalize q
  Normalize.circuit P q

  -- 3. L = a·b + 3n (interpolated product plus the constant limbs of 3n);
  --    S = q·n + t with the caller's affine target limbs
  let Pc ← interpolatedMul a b
  let L : Vector (Expression (F p)) (2 * m - 1) := Vector.mapFinRange (2 * m - 1) fun k =>
    Pc[k.val] + (c[k.val] : Expression (F p))
  let Sqn : Vector (Expression (F p)) (2 * m - 1) := bigIntMulNoReduce q n
  let S : Vector (Expression (F p)) (2 * m - 1) := Vector.mapFinRange (2 * m - 1) fun k =>
    if h : k.val < m then Sqn[k.val] + t[k.val]'h else Sqn[k.val]

  -- 4. certify a·b + 3n = q·n + t as integers via the grouped equality
  GroupedEqXV.circuit P.B gf posOf G V VR hgv P.hB1 { lhs := L, rhs := S }

instance elaborated (P : BigIntParams p m)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqXV.GVXHyps p (2 * m - 1) P.B gf posOf G V VR)
    (c : Vector (F p) (2 * m - 1))
    [Fact (p > 2)] :
    ElaboratedCircuit (F p) (MulModTarget.Inputs m) unit (main P gf posOf G V VR hgv c) where
  -- q (m) + normalize q (m*B) + interpolatedMul a b (2m−1)
  --   + groupedEqXV (Σ (Wf k − 1))
  localLength _ :=
    m + m * (P.B - 1) + (2 * m - 1) + GroupedEqXV.widthAllocFrom V.Wf (G - 2) 0
  localLength_eq := by
    intro input offset
    simp only [main, interpolatedMul, circuit_norm, Normalize.circuit, Normalize.elaborated,
      Normalize.main, GroupedEqXV.circuit, GroupedEqXV.elaborated,
      RangeCheck.circuit, Gadgets.ToBits.rangeCheck]
    omega
  subcircuitsConsistent := by
    intro input offset
    simp +arith only [main, interpolatedMul, circuit_norm, Normalize.circuit, Normalize.elaborated,
      Normalize.main, GroupedEqXV.circuit, GroupedEqXV.elaborated,
      RangeCheck.circuit, Gadgets.ToBits.rangeCheck]
  channelsLawful := by
    intro offset
    simp only [main, interpolatedMul, circuit_norm, Normalize.circuit, Normalize.elaborated,
      Normalize.main, GroupedEqXV.circuit, GroupedEqXV.elaborated,
      RangeCheck.circuit, Gadgets.ToBits.rangeCheck]


def Assumptions (B : ℕ) (c : Vector (F p) (2 * m - 1))
    (input : MulModTarget.Inputs m (F p)) : Prop :=
  input.a.Normalized B ∧ input.b.Normalized B ∧ input.modulus.Normalized B ∧
    (∀ i : Fin m, (input.target[i.val]).val < 3 * 2 ^ B) ∧
    input.a.value B < input.modulus.value B ∧
    input.b.value B < input.modulus.value B ∧
    input.target.value B < 3 * input.modulus.value B ∧
    0 < input.modulus.value B ∧
    input.modulus.value B + 3 ≤ 2 ^ (B * m) ∧
    (∀ j : Fin (2 * m - 1), (c[j.val]).val < 2 ^ B) ∧
    polyValue B c = 3 * input.modulus.value B


def Spec (B : ℕ) (input : MulModTarget.Inputs m (F p)) : Prop :=
  input.target.value B % input.modulus.value B
    = (input.a.value B * input.b.value B) % input.modulus.value B


def circuit (P : BigIntParams p m)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqXV.GVXHyps p (2 * m - 1) P.B gf posOf G V VR)
    (hNf : ∀ j, V.Nf j = (m + 1) * 2 ^ (2 * P.B))
    (hNfR : ∀ j, VR.Nf j = (m + 1) * 2 ^ (2 * P.B))
    (c : Vector (F p) (2 * m - 1))
    (hB2 : 2 ≤ P.B)
    [Fact (p > 2)] :
    FormalAssertion (F p) (MulModTarget.Inputs m) where
    main := main P gf posOf G V VR hgv c
    Assumptions := Assumptions P.B c
    Spec := Spec P.B
    soundness := by
      obtain ⟨B, W, hB, hW, hB1, hWB, hWp, hp⟩ := P
      circuit_proof_start [Normalize.circuit, Normalize.elaborated, Normalize.main,
        Normalize.Assumptions, Normalize.Spec,
        GroupedEqXV.circuit, GroupedEqXV.elaborated,
        GroupedEqXV.Assumptions, GroupedEqX.Spec]
      obtain ⟨ha_norm, hb_norm, hn_norm, ht_limb, hab_lt, hbb_lt, ht_lt3, hn_pos,
        hn3, hc_limb, hc_val⟩ := h_assumptions
      obtain ⟨hq_norm, hAB_ops, h_eq_impl⟩ := h_holds
      simp only [hNf, hNfR] at h_eq_impl
      have hpm : 2 * m - 1 < p := two_m_sub_one_lt hp
      have h_pAB := interpolatedMul_soundness (i₀ + m + m * (B - 1))
        input_var.a input_var.b env hAB_ops
      refine ⟨?_, interpolatedMul_requirements _ _ _ _⟩
      have ha_input : Vector.map (Expression.eval env) input_var.a = input.a := by
        rw [← h_input]
      have hb_input : Vector.map (Expression.eval env) input_var.b = input.b := by
        rw [← h_input]
      have hn_input : Vector.map (Expression.eval env) input_var.modulus = input.modulus := by
        rw [← h_input]
      have ht_input : Vector.map (Expression.eval env) input_var.target = input.target := by
        rw [← h_input]
      have heqAB_get := interpolatedMul_eval_bridge env (i₀ + m + m * (B - 1))
        input_var.a input_var.b hpm h_pAB
      exact mulModTarget3_soundness_core_wm (B := B) hB2 hp i₀ env
        input_var.a input_var.b input_var.modulus input_var.target c
        (interpolatedMul input_var.a input_var.b (i₀ + m + m * (B - 1))).1
        input.a input.b input.modulus input.target
        ha_input hb_input hn_input ht_input
        ha_norm hb_norm hn_norm ht_limb hc_limb hc_val hq_norm
        heqAB_get h_eq_impl
    completeness := by
      obtain ⟨B, W, hB, hW, hB1, hWB, hWp, hp⟩ := P
      circuit_proof_start [Normalize.circuit, Normalize.elaborated, Normalize.main,
        Normalize.Assumptions, Normalize.Spec,
        GroupedEqXV.circuit, GroupedEqXV.elaborated,
        GroupedEqXV.Assumptions, GroupedEqX.Spec]
      obtain ⟨ha_norm, hb_norm, hn_norm, ht_limb, hab_lt, hbb_lt, ht_lt3, hn_pos,
        hn3, hc_limb, hc_val⟩ := h_assumptions
      obtain ⟨hq_env, hAB_uses⟩ := h_env
      have h_pvAB := interpolatedMul_usesLocalWitnesses (i₀ + m + m * (B - 1))
        (i₀ + m + m * (B - 1)) input_var.a input_var.b env rfl hAB_uses
      have ha_input : Vector.map (Expression.eval env.toEnvironment) input_var.a = input.a := by
        rw [← h_input]
      have hb_input : Vector.map (Expression.eval env.toEnvironment) input_var.b = input.b := by
        rw [← h_input]
      have hn_input : Vector.map (Expression.eval env.toEnvironment) input_var.modulus
          = input.modulus := by
        rw [← h_input]
      have ht_input : Vector.map (Expression.eval env.toEnvironment) input_var.target
          = input.target := by
        rw [← h_input]
      have heva : evalValue B env input_var.a = BigInt.value B input.a := by
        rw [evalValue, BigInt.value, ← ha_input]
      have hevb : evalValue B env input_var.b = BigInt.value B input.b := by
        rw [evalValue, BigInt.value, ← hb_input]
      have hevn : evalValue B env input_var.modulus = BigInt.value B input.modulus := by
        rw [evalValue, BigInt.value, ← hn_input]
      have hevt : evalValue B env input_var.target = BigInt.value B input.target := by
        rw [evalValue, BigInt.value, ← ht_input]
      have hqwit : ∀ i : Fin m, env.toEnvironment.get (i₀ + i.val)
          = (((BigInt.value B input.a * BigInt.value B input.b
                + 3 * BigInt.value B input.modulus - BigInt.value B input.target)
              / BigInt.value B input.modulus
              / 2 ^ (B * i.val) % 2 ^ B : ℕ) : F p) := by
        intro i; rw [hq_env i, Vector.getElem_ofFn, heva, hevb, hevn, hevt]
      have heqAB_get := interpolatedMul_eval_bridge_uses env.toEnvironment
        (i₀ + m + m * (B - 1)) input_var.a input_var.b h_pvAB
      have core := mulModTarget3_completeness_core_wm (B := B) hB hB2 hp i₀ env.toEnvironment
        input_var.a input_var.b input_var.modulus input_var.target c
        (interpolatedMul input_var.a input_var.b (i₀ + m + m * (B - 1))).1
        input.a input.b input.modulus input.target
        ha_input hb_input hn_input ht_input
        ha_norm hb_norm hn_norm ht_limb hc_limb hc_val
        hab_lt hbb_lt hn_pos hn3 ht_lt3 h_spec
        hqwit heqAB_get
      simp only [hNf, hNfR]
      exact ⟨core.1,
        interpolatedMul_completeness (i₀ + m + m * (B - 1)) input_var.a input_var.b env h_pvAB,
        core.2⟩



attribute [local irreducible] interpolatedMul Normalize.circuit GroupedEqXV.circuit

theorem computableWitnesses (P : BigIntParams p m)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqXV.GVXHyps p (2 * m - 1) P.B gf posOf G V VR)
    (hNf : ∀ j, V.Nf j = (m + 1) * 2 ^ (2 * P.B))
    (hNfR : ∀ j, VR.Nf j = (m + 1) * 2 ^ (2 * P.B))
    (c : Vector (F p) (2 * m - 1)) (hB2 : 2 ≤ P.B)
    [Fact (p > 2)] :
    (circuit P gf posOf G V VR hgv hNf hNfR c hB2).ComputableWitnesses := by
  letI : NeZero (2 * m - 1) := ⟨by have := Nat.pos_of_neZero m; omega⟩
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition input env env')
    ((main P gf posOf G V VR hgv c input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main
  let qc : Circuit (F p) (Var (BigInt m) (F p)) := ProvableType.witness (α := BigInt m) fun env =>
    let qval : ℕ := (evalValue P.B env input.a * evalValue P.B env input.b
        + 3 * evalValue P.B env input.modulus - evalValue P.B env input.target)
        / evalValue P.B env input.modulus
    Vector.ofFn fun k : Fin m => ((qval / 2 ^ (P.B * k.val) % 2 ^ P.B : ℕ) : F p)
  let q := qc.output offset
  let nqOff := offset + qc.localLength offset
  let nqc : Circuit (F p) Unit := Normalize.circuit P q
  let pcOff := nqOff + nqc.localLength nqOff
  let pcv := (interpolatedMul input.a input.b).output pcOff
  let eqOff := pcOff + (interpolatedMul input.a input.b).localLength pcOff
  let Lv : Vector (Expression (F p)) (2 * m - 1) := Vector.mapFinRange (2 * m - 1) fun k =>
    pcv[k.val] + (c[k.val] : Expression (F p))
  let Sqn : Vector (Expression (F p)) (2 * m - 1) := bigIntMulNoReduce q input.modulus
  let Sv : Vector (Expression (F p)) (2 * m - 1) := Vector.mapFinRange (2 * m - 1) fun k =>
    if h : k.val < m then Sqn[k.val] + input.target[k.val]'h else Sqn[k.val]
  have h_qlen : qc.localLength offset = m := by
    simp [qc, ProvableType.witness, Circuit.localLength, Operations.localLength, size]
  have h_pclen : (interpolatedMul input.a input.b).localLength pcOff = 2 * m - 1 :=
    interpolatedMul_localLength pcOff input.a input.b
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.provableWitness_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.pure_structuralComputableWitnesses_iff,
    and_true]
  and_intros
  · -- q witness reads only the input
    intro _ h_input
    have ha : evalValue P.B env input.a = evalValue P.B env' input.a :=
      evalValue_stable P.B input.a (by
        simpa [circuit_norm] using congrArg (fun x : MulModTarget.Inputs m (F p) => x.a) h_input)
    have hb : evalValue P.B env input.b = evalValue P.B env' input.b :=
      evalValue_stable P.B input.b (by
        simpa [circuit_norm] using congrArg (fun x : MulModTarget.Inputs m (F p) => x.b) h_input)
    have hn : evalValue P.B env input.modulus = evalValue P.B env' input.modulus :=
      evalValue_stable P.B input.modulus (by
        simpa [circuit_norm] using
          congrArg (fun x : MulModTarget.Inputs m (F p) => x.modulus) h_input)
    have ht : evalValue P.B env input.target = evalValue P.B env' input.target :=
      evalValue_stable P.B input.target (by
        simpa [circuit_norm] using
          congrArg (fun x : MulModTarget.Inputs m (F p) => x.target) h_input)
    simp only [ha, hb, hn, ht]
  · -- Normalize q
    exact Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
      (Normalize.circuit P) input q nqOff
      (by
        intro k env env' hle h_agree _
        have hk : offset + m ≤ k := by
          dsimp only [nqOff] at hle
          rw [h_qlen] at hle
          omega
        exact bigIntWitnessOutput_stable _ h_agree hk)
      (Normalize.computableWitnesses P) env env'
  · -- interpolatedMul a b
    exact interpolatedMul_structuralComputableWitnesses input input.a input.b pcOff
      (by
        intro k env env' _ _ h_input
        have ha : eval env input.a = eval env' input.a := by
          simpa [circuit_norm] using congrArg (fun x : MulModTarget.Inputs m (F p) => x.a) h_input
        have hb : eval env input.b = eval env' input.b := by
          simpa [circuit_norm] using congrArg (fun x : MulModTarget.Inputs m (F p) => x.b) h_input
        exact ⟨ha, hb⟩)
      env env'
  · -- GroupedEqXV: lhs = Pc + 3n constants, rhs = S (q·n + target)
    exact Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
      (GroupedEqXV.circuit P.B gf posOf G V VR hgv P.hB1) input { lhs := Lv, rhs := Sv } eqOff
      (by
        intro k env env' hle h_agree h_input
        have hk_pc : pcOff + (2 * m - 1) ≤ k := by
          dsimp only [eqOff] at hle
          rw [h_pclen] at hle
          omega
        have hk_q : offset + m ≤ k := by
          dsimp only [eqOff, pcOff, nqOff] at hle
          rw [h_qlen] at hle
          omega
        have hPc : Vector.map (Expression.eval env.toEnvironment) pcv
            = Vector.map (Expression.eval env'.toEnvironment) pcv :=
          interpolatedMul_output_stable pcOff input.a input.b h_agree hk_pc
        have hq_vec : eval env q = eval env' q := bigIntWitnessOutput_stable _ h_agree hk_q
        have hn : eval env input.modulus = eval env' input.modulus := by
          simpa [circuit_norm] using
            congrArg (fun x : MulModTarget.Inputs m (F p) => x.modulus) h_input
        have ht : eval env input.target = eval env' input.target := by
          simpa [circuit_norm] using
            congrArg (fun x : MulModTarget.Inputs m (F p) => x.target) h_input
        have hL : Vector.map (Expression.eval env.toEnvironment) Lv
            = Vector.map (Expression.eval env'.toEnvironment) Lv := by
          apply Vector.ext
          intro i hi
          have hpc_i : Expression.eval env.toEnvironment (pcv[i]'hi)
              = Expression.eval env'.toEnvironment (pcv[i]'hi) := by
            have := congrArg (fun v : Vector (F p) (2 * m - 1) => v[i]'hi) hPc
            simpa only [Vector.getElem_map] using this
          simp only [Vector.getElem_map, Lv, Vector.getElem_mapFinRange]
          simp only [Expression.eval, hpc_i]
        have hS : Vector.map (Expression.eval env.toEnvironment) Sv
            = Vector.map (Expression.eval env'.toEnvironment) Sv := by
          apply Vector.ext
          intro i hi
          have hsq_i : Expression.eval env.toEnvironment Sqn[i]
              = Expression.eval env'.toEnvironment Sqn[i] :=
            bigIntMulNoReduce_coeff_stable env.toEnvironment env'.toEnvironment q input.modulus
              (fun j hj => bigInt_getElem_eval_eq hq_vec j hj)
              (fun j hj => bigInt_getElem_eval_eq hn j hj) ⟨i, hi⟩
          simp only [Vector.getElem_map, Sv, Vector.getElem_mapFinRange]
          split
          · rename_i hlt
            have ht_i : Expression.eval env.toEnvironment (input.target[i]'hlt)
                = Expression.eval env'.toEnvironment (input.target[i]'hlt) :=
              bigInt_getElem_eval_eq ht i hlt
            simp only [Expression.eval, hsq_i, ht_i]
          · exact hsq_i
        simp only [circuit_norm]
        rw [hL, hS])
      (GroupedEqXV.computableWitnesses P.B gf posOf G V VR hgv P.hB1) env env'

end MulModTarget3

end

end Solution.Secp256k1ScalarMul
