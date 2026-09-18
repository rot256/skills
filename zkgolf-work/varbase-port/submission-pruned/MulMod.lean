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

end MulMod

namespace MulModTarget
open MulMod

attribute [local irreducible] interpolatedMul Normalize.circuit GroupedEqXV.circuit

end MulModTarget

namespace MulModTarget3
open MulMod

attribute [local irreducible] interpolatedMul Normalize.circuit GroupedEqXV.circuit

end MulModTarget3

end

end Solution.Secp256k1ScalarMul
