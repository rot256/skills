import Solution.Secp256k1ScalarMul.IsZeroFe
import Solution.Secp256k1ScalarMul.Mux
import Solution.Secp256k1ScalarMul.DivOrZeroTheorems
import Solution.Secp256k1ScalarMul.CompleteAddTheorems
import Solution.Secp256k1ScalarMul.AddMod
import Solution.Secp256k1ScalarMul.IsZeroFeSum
import Solution.Secp256k1ScalarMul.Params
import Solution.Secp256k1ScalarMul.MulMod
import Solution.Secp256k1ScalarMul.MulModTargetW
import Solution.Secp256k1ScalarMul.MulModFoldTInv
import Solution.Secp256k1ScalarMul.Limbs32

namespace Solution.Secp256k1ScalarMul

namespace DivOrZeroS32
open DivOrZero MulMod MulModTargetD MulModTargetW

/-- Inputs to the fused conditional slope certificate.  `sel` selects between the
tangent square `3·x²` (`sel = 1`) and the chord numerator `dyU` (`sel = 0`); `den`
is the (possibly zero) denominator. -/
structure Inputs (F : Type) where
  sel : F
  x : Emu F
  dyU : Emu F
  den : Emu F
deriving ProvableStruct

/-- `polyValue` of a limbwise `3·v` equals `3·polyValue v`, provided each scaled
coefficient stays below the circuit modulus. -/
lemma polyValue_three_mul {n : ℕ} (env : Environment (F circomPrime))
    (v : Vector (Expression (F circomPrime)) n)
    (hv : ∀ j : Fin n, 3 * (Expression.eval env v[j.val]).val < circomPrime) :
    polyValue limbBits (Vector.map (Expression.eval env)
        (Vector.mapFinRange n fun k =>
          ((3 : F circomPrime) : Expression (F circomPrime)) * v[k.val]))
      = 3 * polyValue limbBits (Vector.map (Expression.eval env) v) := by
  rw [polyValue, polyValue, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Vector.getElem_map, Vector.getElem_map, Vector.getElem_mapFinRange]
  rw [MulModTargetW.eval_three_mul, MulModTargetW.val_three_mul (by decide) _ (hv i)]
  ring

/-- Convert `polyValue` into a `Finset.range` sum of an arbitrary coefficient
function (local copy of the `MulModTarget*` helper). -/
lemma polyValue_eq_range_sum {B kk : ℕ} (vv : Vector (F circomPrime) kk) (f : ℕ → ℕ)
    (hf : ∀ (i : ℕ) (h : i < kk), (vv[i]'h).val * 2 ^ (B * i) = f i) :
    polyValue B vv = ∑ i ∈ Finset.range kk, f i := by
  rw [polyValue, ← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_congr rfl fun i _ => hf i.val i.isLt

/-- `polyValue` of a `numLimbs`-limb value zero-padded to `2·numLimbs − 1` cells
equals its `BigInt.value`. -/
lemma polyValue_pad (env : Environment (F circomPrime)) (d : Var Emu (F circomPrime)) :
    polyValue limbBits (Vector.map (Expression.eval env)
        (Vector.mapFinRange (2 * numLimbs - 1) fun k =>
          if h : k.val < numLimbs then d[k.val]'h else (0 : Expression (F circomPrime))))
      = BigInt.value limbBits (Vector.map (Expression.eval env) d) := by
  set dm := Vector.map (Expression.eval env) d with hdm
  set g : ℕ → ℕ := fun i => if h : i < numLimbs then (dm[i]'h).val * 2 ^ (limbBits * i) else 0
    with hg
  have h1 : polyValue limbBits (Vector.map (Expression.eval env)
        (Vector.mapFinRange (2 * numLimbs - 1) fun k =>
          if h : k.val < numLimbs then d[k.val]'h else (0 : Expression (F circomPrime))))
      = ∑ i ∈ Finset.range (2 * numLimbs - 1), g i := by
    apply polyValue_eq_range_sum
    intro i hi
    rw [Vector.getElem_map, Vector.getElem_mapFinRange]
    by_cases h : i < numLimbs
    · simp only [dif_pos h, hg, hdm, Vector.getElem_map]
    · simp only [dif_neg h, hg]
      rw [show Expression.eval env (0 : Expression (F circomPrime)) = 0 from rfl,
        ZMod.val_zero, zero_mul]
  have h2 : ∑ i ∈ Finset.range (2 * numLimbs - 1), g i = ∑ i ∈ Finset.range numLimbs, g i := by
    symm
    apply Finset.sum_subset
    · intro x hx
      rw [Finset.mem_range] at hx ⊢
      simp only [numLimbs] at hx ⊢
      omega
    · intro x _ hx
      rw [Finset.mem_range] at hx
      simp only [hg, dif_neg (by simp only [numLimbs] at hx ⊢; omega)]
  have h3 : ∑ i ∈ Finset.range numLimbs, g i = BigInt.value limbBits dm := by
    rw [BigInt.value_eq_sum, ← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro k _
    simp only [hg, dif_pos k.isLt, Fin.getElem_fin]
  rw [h1, h2, h3, hdm]

/-- Per-coefficient bound and value identity for the single square convolution
`interpolatedMul xv xv`, given the interpolation constraints hold and `xv` is
normalized. -/
lemma Pxx_facts (env : Environment (F circomPrime)) (xv : Var Emu (F circomPrime)) (off : ℕ)
    (hAB : Operations.forAllNoOffset
        { assert := fun e => Expression.eval env e = 0, lookup := fun l => l.Soundness env,
          interact := fun i => i.Guarantees env,
          subcircuit := fun {_n} s => s.Assumptions env → s.Spec env }
        (MulMod.interpolatedMul xv xv off).2)
    (hxnorm : BigInt.Normalized limbBits (Vector.map (Expression.eval env) xv)) :
    (∀ k : Fin (2 * numLimbs - 1),
        (Expression.eval env (MulMod.interpolatedMul xv xv off).1[k.val]).val
          < numLimbs * 2 ^ (2 * limbBits))
      ∧ polyValue limbBits (Vector.map (Expression.eval env) (MulMod.interpolatedMul xv xv off).1)
          = BigInt.value limbBits (Vector.map (Expression.eval env) xv)
            * BigInt.value limbBits (Vector.map (Expression.eval env) xv) := by
  have hx : ∀ i : Fin numLimbs, (Expression.eval env xv[i.val]).val < 2 ^ limbBits := by
    intro i
    have := hxnorm i
    rwa [Fin.getElem_fin, Vector.getElem_map] at this
  have hfield : numLimbs * (2 ^ limbBits * 2 ^ limbBits) < circomPrime := by decide
  have hpm : 2 * numLimbs - 1 < circomPrime := by decide
  have h_pts := MulMod.interpolatedMul_soundness off xv xv env hAB
  have hbridge := MulMod.interpolatedMul_eval_bridge env off xv xv hpm h_pts
  have h2B : 2 ^ limbBits * 2 ^ limbBits = 2 ^ (2 * limbBits) := by rw [two_mul, pow_add]
  refine ⟨fun k => ?_, ?_⟩
  · rw [hbridge k]
    have hh := val_coeff_lt_gen env xv xv k hx hx hfield
    rwa [h2B] at hh
  · have hPmap : Vector.map (Expression.eval env) (MulMod.interpolatedMul xv xv off).1
        = Vector.map (Expression.eval env) (bigIntMulNoReduce xv xv) := by
      apply Vector.ext
      intro k hk
      rw [Vector.getElem_map, Vector.getElem_map]
      exact hbridge ⟨k, hk⟩
    rw [hPmap, polyValue_mul_eq_gen env xv xv hx hx hfield]

/-- Same conclusion as `Pxx_facts`, but taking the per-cell evaluation bridge
directly (so the completeness direction, which obtains the bridge from
`interpolatedMul_eval_bridge_uses`, can reuse it). -/
lemma Pxx_facts_of_bridge (env : Environment (F circomPrime)) (xv : Var Emu (F circomPrime)) (off : ℕ)
    (hbridge : ∀ k : Fin (2 * numLimbs - 1),
      Expression.eval env (MulMod.interpolatedMul xv xv off).1[k.val]
        = Expression.eval env (bigIntMulNoReduce xv xv)[k.val])
    (hxnorm : BigInt.Normalized limbBits (Vector.map (Expression.eval env) xv)) :
    (∀ k : Fin (2 * numLimbs - 1),
        (Expression.eval env (MulMod.interpolatedMul xv xv off).1[k.val]).val
          < numLimbs * 2 ^ (2 * limbBits))
      ∧ polyValue limbBits (Vector.map (Expression.eval env) (MulMod.interpolatedMul xv xv off).1)
          = BigInt.value limbBits (Vector.map (Expression.eval env) xv)
            * BigInt.value limbBits (Vector.map (Expression.eval env) xv) := by
  have hx : ∀ i : Fin numLimbs, (Expression.eval env xv[i.val]).val < 2 ^ limbBits := by
    intro i
    have := hxnorm i
    rwa [Fin.getElem_fin, Vector.getElem_map] at this
  have hfield : numLimbs * (2 ^ limbBits * 2 ^ limbBits) < circomPrime := by decide
  have h2B : 2 ^ limbBits * 2 ^ limbBits = 2 ^ (2 * limbBits) := by rw [two_mul, pow_add]
  refine ⟨fun k => ?_, ?_⟩
  · rw [hbridge k]
    have hh := val_coeff_lt_gen env xv xv k hx hx hfield
    rwa [h2B] at hh
  · have hPmap : Vector.map (Expression.eval env) (MulMod.interpolatedMul xv xv off).1
        = Vector.map (Expression.eval env) (bigIntMulNoReduce xv xv) := by
      apply Vector.ext
      intro k hk
      rw [Vector.getElem_map, Vector.getElem_map]
      exact hbridge ⟨k, hk⟩
    rw [hPmap, polyValue_mul_eq_gen env xv xv hx hx hfield]

/-- Convolution cell 5 of `x ⊛ x` has only two terms, so it is below
`2·2^(2·limbBits)` rather than the uniform `numLimbs·2^(2·limbBits)`. -/
lemma Pxx_cell5_of_bridge (env : Environment (F circomPrime)) (xv : Var Emu (F circomPrime))
    (off : ℕ)
    (hbridge : ∀ k : Fin (2 * numLimbs - 1),
      Expression.eval env (MulMod.interpolatedMul xv xv off).1[k.val]
        = Expression.eval env (bigIntMulNoReduce xv xv)[k.val])
    (hxnorm : BigInt.Normalized limbBits (Vector.map (Expression.eval env) xv)) :
    (Expression.eval env (MulMod.interpolatedMul xv xv off).1[5]).val
      < 2 * 2 ^ (2 * limbBits) := by
  have hx : ∀ i : Fin numLimbs, (Expression.eval env xv[i.val]).val < 2 ^ limbBits := by
    intro i
    have := hxnorm i
    rwa [Fin.getElem_fin, Vector.getElem_map] at this
  have hfield : numLimbs * (2 ^ limbBits * 2 ^ limbBits) < circomPrime := by decide
  have h2B : 2 ^ limbBits * 2 ^ limbBits = 2 ^ (2 * limbBits) := by rw [two_mul, pow_add]
  have hb5 : Expression.eval env (MulMod.interpolatedMul xv xv off).1[5]
      = Expression.eval env (bigIntMulNoReduce xv xv)[5] :=
    hbridge (⟨5, by decide⟩ : Fin (2 * numLimbs - 1))
  have hh := MulModFold.coeff5_lt env xv xv hx hx hfield
  rw [h2B] at hh
  rw [hb5]
  exact hh

/-- Same as `Pxx_cell5_of_bridge`, but taking the interpolation constraints. -/
lemma Pxx_cell5 (env : Environment (F circomPrime)) (xv : Var Emu (F circomPrime)) (off : ℕ)
    (hAB : Operations.forAllNoOffset
        { assert := fun e => Expression.eval env e = 0, lookup := fun l => l.Soundness env,
          interact := fun i => i.Guarantees env,
          subcircuit := fun {_n} s => s.Assumptions env → s.Spec env }
        (MulMod.interpolatedMul xv xv off).2)
    (hxnorm : BigInt.Normalized limbBits (Vector.map (Expression.eval env) xv)) :
    (Expression.eval env (MulMod.interpolatedMul xv xv off).1[5]).val
      < 2 * 2 ^ (2 * limbBits) := by
  have hpm : 2 * numLimbs - 1 < circomPrime := by decide
  have h_pts := MulMod.interpolatedMul_soundness off xv xv env hAB
  exact Pxx_cell5_of_bridge env xv off
    (MulMod.interpolatedMul_eval_bridge env off xv xv hpm h_pts) hxnorm

/-- The zero-guarded denominator `den + z·e₀`.  When the zero flag `z` is set,
every limb of `den` vanishes, so the vector is the constant `1`; otherwise it is
`den` itself.  Being a pure affine recombination it costs no witness and no row,
which is what a `Mux` here would have charged. -/
def denSafeVec (den : Var Emu (F circomPrime)) (z : Expression (F circomPrime)) :
    Var Emu (F circomPrime) :=
  Vector.ofFn fun k : Fin numLimbs =>
    (den[k.val]'k.isLt) + (if k.val = 0 then z else 0)

/-- A canonical-digit `BigInt` of value zero has every limb zero. -/
lemma limbs_zero_of_value_zero {d : Emu (F circomPrime)}
    (h : BigInt.value limbBits d = 0) : ∀ i : Fin numLimbs, d[i.val] = 0 := by
  intro i
  rw [BigInt.value_eq_sum] at h
  have hterm : (d[i]).val * 2 ^ (limbBits * i.val) = 0 :=
    (Finset.sum_eq_zero_iff.mp h) i (Finset.mem_univ i)
  have hpow : (2 : ℕ) ^ (limbBits * i.val) ≠ 0 := by positivity
  have hv : (d[i]).val = 0 := by
    rcases Nat.mul_eq_zero.mp hterm with h0 | h0
    · exact h0
    · exact absurd h0 hpow
  exact (ZMod.val_eq_zero _).mp hv

/-- Evaluated shape of `denSafeVec`: the constant `1` on the zero branch and
`den` itself otherwise. -/
lemma eval_denSafeVec (env : Environment (F circomPrime))
    (den : Var Emu (F circomPrime)) (z : Expression (F circomPrime))
    (hb : IsBool (Expression.eval env z))
    (hz : Expression.eval env z = 1 →
      BigInt.value limbBits (Vector.map (Expression.eval env) den) = 0) :
    Vector.map (Expression.eval env) (denSafeVec den z)
      = if Expression.eval env z = 1 then emuOfNat 1
        else Vector.map (Expression.eval env) den := by
  by_cases h1 : Expression.eval env z = 1
  · rw [if_pos h1]
    have hzero := limbs_zero_of_value_zero (hz h1)
    apply Vector.ext
    intro i hi
    have hi4 : i < 4 := hi
    rw [Vector.getElem_map, denSafeVec, Vector.getElem_ofFn]
    have hd0 : Expression.eval env (den[i]'hi) = 0 := by
      have := hzero ⟨i, hi⟩
      rwa [Vector.getElem_map] at this
    interval_cases i <;>
      simp [circuit_norm, hd0, h1, emuOfNat, limbOfNat, Vector.getElem_ofFn, limbBits]
  · rw [if_neg h1]
    have h0 : Expression.eval env z = 0 := by rcases hb with h | h; exacts [h, absurd h h1]
    apply Vector.ext
    intro i hi
    have hi4 : i < 4 := hi
    rw [Vector.getElem_map, denSafeVec, Vector.getElem_ofFn, Vector.getElem_map]
    interval_cases i <;> simp [circuit_norm, h0]

/-- On the `z = 0` branch the guarded denominator is the denominator itself. -/
lemma eval_denSafeVec_of_flag_zero (env : Environment (F circomPrime))
    (den : Var Emu (F circomPrime)) (z : Expression (F circomPrime))
    (h0 : Expression.eval env z = 0) :
    Vector.map (Expression.eval env) (denSafeVec den z)
      = Vector.map (Expression.eval env) den := by
  apply Vector.ext
  intro i hi
  have hi4 : i < 4 := hi
  rw [Vector.getElem_map, denSafeVec, Vector.getElem_ofFn, Vector.getElem_map]
  interval_cases i <;> simp [circuit_norm, h0]

/-- Stability of `denSafeVec` under environments agreeing on `den` and `z`. -/
lemma denSafeVec_map_eval_eq {den : Var Emu (F circomPrime)} {z : Expression (F circomPrime)}
    {e e' : ProverEnvironment (F circomPrime)}
    (hz : Expression.eval e.toEnvironment z = Expression.eval e'.toEnvironment z)
    (hd : Vector.map (Expression.eval e.toEnvironment) den
        = Vector.map (Expression.eval e'.toEnvironment) den) :
    Vector.map (Expression.eval e.toEnvironment) (denSafeVec den z)
      = Vector.map (Expression.eval e'.toEnvironment) (denSafeVec den z) := by
  apply Vector.ext
  intro i hi
  have hi4 : i < 4 := hi
  have hdi : Expression.eval e.toEnvironment (den[i]'hi)
      = Expression.eval e'.toEnvironment (den[i]'hi) := by
    have := congrArg (fun v : Emu (F circomPrime) => v[i]'hi) hd
    simpa only [Vector.getElem_map] using this
  simp only [Vector.getElem_map, denSafeVec, Vector.getElem_ofFn]
  split <;> simp [circuit_norm, hdi, hz]

/-- The eight 32-bit limbs of the witnessed slope. -/
@[reducible] def Emu32 : TypeMap := BigInt 8

/-- Stability of an eight-limb witness block under agreeing environments. -/
theorem emu32WitnessOutput_stable
    (compute : ProverEnvironment (F circomPrime) → Emu32 (F circomPrime))
    {offset k : ℕ} {env env' : ProverEnvironment (F circomPrime)}
    (h_agree : env.AgreesBelow k env') (hk : offset + 8 ≤ k) :
    eval env ((ProvableType.witness (α := Emu32) compute).output offset) =
      eval env' ((ProvableType.witness (α := Emu32) compute).output offset) := by
  apply Vector.ext
  intro i hi
  rw [← ProvableType.getElem_eval_fields_prover (env := env)
      ((ProvableType.witness (α := Emu32) compute).output offset) i hi,
    ← ProvableType.getElem_eval_fields_prover (env := env')
      ((ProvableType.witness (α := Emu32) compute).output offset) i hi]
  simp only [Circuit.output, ProvableType.witness, ProvableType.varFromOffset_fields,
    Vector.getElem_mapRange, Expression.eval]
  have hi8 : i < 8 := hi
  exact h_agree (offset + i) (by omega)

def main (input : Var Inputs (F circomPrime)) :
    Circuit (F circomPrime) (Var Emu32 (F circomPrime)) := do
  let { sel, x, dyU, den } := input

  -- Zero flag of the denominator, at one witness and one row instead of the
  -- two of a full `IsZeroFeSum`.  The single row `z · (Σ limbs) = 0` forces
  -- `z = 0` whenever the denominator is nonzero, which is all soundness needs:
  -- the certificate clause of `Spec` is guarded by `decodeFe den ≠ 0`, so on the
  -- `den = 0` branch nothing is claimed and an unconstrained `z` is harmless.
  let z ← witnessField (fun env => if evalEmu env den = 0 then 1 else 0)
  assertZero (z * (den[0] + den[1] + den[2] + den[3]))

  -- guarded denominator: `1` when `den = 0`.  The *numerator* needs no guard:
  -- the certificate is `λ·denSafe ≡ target` with `denSafe` never `≡ 0`, so it
  -- is uniformly satisfiable and no consumer needs `λ = 0` on that branch.
  let denSafe : Var Emu (F circomPrime) := denSafeVec den z

  -- the single square convolution x ⊛ x (never reduced)
  let Pxx ← MulMod.interpolatedMul x x

  -- tangent target 3·(x ⊛ x) versus chord target dyU padded to 2m−1 cells
  let Ttrue : Var (fields (2 * numLimbs - 1)) (F circomPrime) :=
    Vector.mapFinRange (2 * numLimbs - 1) fun k =>
      ((3 : F circomPrime) : Expression (F circomPrime)) * Pxx[k.val]
  let Tfalse : Var (fields (2 * numLimbs - 1)) (F circomPrime) :=
    Vector.mapFinRange (2 * numLimbs - 1) fun k =>
      if h : k.val < numLimbs then dyU[k.val]'h else (0 : Expression (F circomPrime))
  let T ← subcircuit (Mux.circuit (M := fields (2 * numLimbs - 1)))
    { selector := sel, ifTrue := Ttrue, ifFalse := Tfalse }

  -- witness the slope λ = (if sel = 1 then 3x² else dyU) · denSafe⁻¹ mod P256,
  -- directly in the eight-limb 32-bit view
  let lam32 ← ProvableType.witness (α := Emu32) fun env =>
    let denFp : Specs.Secp256k1.Fp :=
      ((if evalEmu env den = 0 then 1 else evalEmu env den : ℕ) : Specs.Secp256k1.Fp)
    let numFp : Specs.Secp256k1.Fp :=
      if Expression.eval env.toEnvironment sel = 1
      then ((3 * (evalEmu env x * evalEmu env x) : ℕ) : Specs.Secp256k1.Fp)
      else ((evalEmu env dyU : ℕ) : Specs.Secp256k1.Fp)
    Limbs32.emu32OfNat (numFp * denFp⁻¹).val

  -- each 32-bit limb is range checked: 8·(31/32) = 248/256, exactly what the
  -- four-limb `Normalize` costs together with its four witnesses.
  Normalize.circuit secpParams32 lam32

  -- certify polyValue(T) ≡ λ·denSafe (mod p) with the widened (<3·P256) denominator operand
  MulModFoldT.circuitInv (2 ^ limbBits) (3 * 2 ^ limbBits) (3 * numLimbs * 2 ^ (2 * limbBits))
    (6 * 2 ^ (2 * limbBits))
    (by decide) (by decide) (by decide) (by decide)
    { a := Limbs32.emuOf32 lam32, b := denSafe, target := T }

  return lam32

instance elaborated : ElaboratedCircuit (F circomPrime) Inputs Emu32 main := by
  elaborate_circuit

def Assumptions (input : Inputs (F circomPrime)) : Prop :=
  Fe.Valid input.x ∧
    IsBool input.sel ∧
    (∀ i : Fin numLimbs, (input.dyU[i.val]).val < 3 * 2 ^ limbBits) ∧
    BigInt.value limbBits input.dyU < 3 * P256 ∧
    (∀ i : Fin numLimbs, (input.den[i.val]).val < 3 * 2 ^ limbBits) ∧
    BigInt.value limbBits input.den < 3 * P256 ∧
    (BigInt.value limbBits input.den % P256 = 0 → BigInt.value limbBits input.den = 0)

def Spec (input : Inputs (F circomPrime)) (lam32 : Emu32 (F circomPrime)) : Prop :=
  BigInt.Normalized 32 lam32 ∧
    (decodeFe input.den ≠ 0 →
      decodeFe (Limbs32.emuOf32V lam32) * decodeFe input.den =
        (if input.sel = 1 then 3 * (decodeFe input.x * decodeFe input.x)
         else decodeFe input.dyU))

set_option maxHeartbeats 3200000 in
theorem soundness : Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [
    Mux.circuit, Mux.Assumptions, Mux.Spec,
    MulModFoldT.circuitInv, MulModFoldT.Assumptions, MulModFoldT.Spec,
    Normalize.circuit, Normalize.main, Normalize.Assumptions, Normalize.Spec]
  obtain ⟨h_x_valid, h_sel_bool, h_dyU_limb, h_dyU_val, h_den_limb3, h_den_val3, h_den_alias⟩ :=
    h_assumptions
  obtain ⟨h_input_sel, h_input_x, h_input_dyU, h_input_den⟩ := h_input
  obtain ⟨hzrow, hAB_ops, hT, hlam_valid, hmul⟩ := h_holds
  simp only [MulMod.interpolatedMul_localLength] at hT hlam_valid hmul
  set zc := env.get i₀ with hzc_def
  set denSafeVar := denSafeVec input_var_den (var (F := F circomPrime) { index := i₀ })
    with hdenSafeVar
  set off_ip := i₀ + 1 with hoff_ip
  set PxxVar := (MulMod.interpolatedMul input_var_x input_var_x off_ip).1 with hPxxVar
  set TVar := Vector.mapRange (2 * numLimbs - 1) fun i =>
    var (F := F circomPrime) { index := off_ip + (2 * numLimbs - 1) + i } with hTVar
  set lam32Var := Vector.mapRange 8 fun i =>
    var (F := F circomPrime) { index := off_ip + (2 * numLimbs - 1) + (2 * numLimbs - 1) + i }
    with hlam32Var
  set lamVar := Limbs32.emuOf32 lam32Var with hlamVar
  have hlam_valid64 : BigInt.Normalized limbBits (Vector.map (Expression.eval env) lamVar) := by
    rw [hlamVar, Limbs32.eval_emuOf32]
    exact Limbs32.normalized_emuOf32 hlam_valid
  specialize hT h_sel_bool
  have hden_get : ∀ (i : ℕ) (hi : i < 4),
      Expression.eval env (input_var_den[i]'hi) = input_den[i]'hi := by
    intro i hi
    rw [← h_input_den, Vector.getElem_map]
  -- the single row pins the flag to zero whenever the denominator is nonzero
  have hzc_of_ne : BigInt.value limbBits input_den ≠ 0 → zc = 0 := by
    intro hv
    have hsum : (input_den[0] + input_den[1] + input_den[2] + input_den[3] : F circomPrime) ≠ 0 :=
      fun hs => hv ((IsZeroFeSum.sum_field_eq_zero_iff_value input_den h_den_limb3).mp hs)
    have hzrow' : zc * (input_den[0] + input_den[1] + input_den[2] + input_den[3]) = 0 := by
      simpa [circuit_norm, hzc_def, hden_get 0 (by omega), hden_get 1 (by omega),
        hden_get 2 (by omega), hden_get 3 (by omega)] using hzrow
    rcases mul_eq_zero.mp hzrow' with h | h
    · exact h
    · exact absurd h hsum
  -- denominator alias
  have hd_iff : decodeFe input_den = 0 ↔ BigInt.value limbBits input_den = 0 := by
    constructor
    · intro h
      apply h_den_alias
      have hdvd : (P256 : ℕ) ∣ BigInt.value limbBits input_den :=
        (ZMod.natCast_eq_zero_iff _ _).mp (by simpa [decodeFe] using h)
      rcases hdvd with ⟨k, hk⟩
      rw [hk]; exact Nat.mul_mod_right _ _
    · intro h; simp [decodeFe, h]
  have hx_norm : BigInt.Normalized limbBits (Vector.map (Expression.eval env) input_var_x) := by
    rw [h_input_x]; exact h_x_valid.1
  obtain ⟨hPxx_cell, hPxx_poly⟩ := Pxx_facts env input_var_x off_ip hAB_ops hx_norm
  rw [h_input_x] at hPxx_poly
  -- the ×3 tangent-square target
  have hb : ∀ j : Fin (2 * numLimbs - 1),
      3 * (Expression.eval env PxxVar[j.val]).val < circomPrime := by
    intro j
    have hj := hPxx_cell j
    calc 3 * (Expression.eval env PxxVar[j.val]).val
        < 3 * (numLimbs * 2 ^ (2 * limbBits)) := Nat.mul_lt_mul_of_pos_left hj (by norm_num)
      _ < circomPrime := by decide
  have hTtrue_poly : polyValue limbBits (Vector.map (Expression.eval env)
        (Vector.mapFinRange (2 * numLimbs - 1) fun k =>
          ((3 : F circomPrime) : Expression (F circomPrime)) * PxxVar[k.val]))
      = 3 * (BigInt.value limbBits input_x * BigInt.value limbBits input_x) := by
    rw [polyValue_three_mul env PxxVar hb, hPxx_poly]
  have hTfalse_poly : polyValue limbBits (Vector.map (Expression.eval env)
        (Vector.mapFinRange (2 * numLimbs - 1) fun k =>
          if h : k.val < numLimbs then input_var_dyU[k.val]'h
          else (0 : Expression (F circomPrime))))
      = BigInt.value limbBits input_dyU := by
    rw [polyValue_pad env input_var_dyU, h_input_dyU]
  -- per-cell bounds on the target
  have hTtrue_cell : ∀ k : Fin (2 * numLimbs - 1),
      (Expression.eval env (((3 : F circomPrime) : Expression (F circomPrime)) * PxxVar[k.val])).val
        < 3 * numLimbs * 2 ^ (2 * limbBits) := by
    intro k
    rw [eval_three_mul, val_three_mul (by decide) _ (hb k)]
    have hj := hPxx_cell k
    have hbe : 3 * numLimbs * 2 ^ (2 * limbBits) = 3 * (numLimbs * 2 ^ (2 * limbBits)) := by ring
    rw [hbe]; exact Nat.mul_lt_mul_of_pos_left hj (by norm_num)
  have hTfalse_cell : ∀ k : Fin (2 * numLimbs - 1),
      (Expression.eval env (if h : k.val < numLimbs
        then input_var_dyU[k.val]'h
        else (0 : Expression (F circomPrime)))).val < 3 * numLimbs * 2 ^ (2 * limbBits) := by
    intro k
    by_cases h : k.val < numLimbs
    · rw [dif_pos h]
      have hlt : (Expression.eval env (input_var_dyU[k.val]'h)).val < 3 * 2 ^ limbBits := by
        have h2 : Expression.eval env (input_var_dyU[k.val]'h) = input_dyU[k.val]'h := by
          rw [← h_input_dyU, Vector.getElem_map]
        rw [h2]
        simpa using h_dyU_limb ⟨k.val, h⟩
      have hbound : 3 * 2 ^ limbBits ≤ 3 * numLimbs * 2 ^ (2 * limbBits) := by
        have h1 : 2 ^ limbBits ≤ 2 ^ (2 * limbBits) :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
        calc 3 * 2 ^ limbBits ≤ 3 * 2 ^ (2 * limbBits) := by omega
          _ ≤ 3 * numLimbs * 2 ^ (2 * limbBits) := by
              nlinarith [Nat.two_pow_pos (2 * limbBits)]
      exact lt_of_lt_of_le hlt hbound
    · rw [dif_neg h, show Expression.eval env (0 : Expression (F circomPrime)) = 0 from rfl,
        ZMod.val_zero]
      positivity
  have hTVar_cell : ∀ k : Fin (2 * numLimbs - 1),
      (env.get (off_ip + (2 * numLimbs - 1) + k.val)).val < 3 * numLimbs * 2 ^ (2 * limbBits) := by
    intro k
    have hcell : (Vector.map (Expression.eval env) TVar)[k.val]
        = env.get (off_ip + (2 * numLimbs - 1) + k.val) := by
      rw [Vector.getElem_map, hTVar, Vector.getElem_mapRange]; rfl
    rw [← hcell, hT]
    by_cases hsel : input_sel = 1
    · rw [if_pos hsel, Vector.getElem_map, Vector.getElem_mapFinRange]
      exact hTtrue_cell k
    · rw [if_neg hsel, Vector.getElem_map, Vector.getElem_mapFinRange]
      exact hTfalse_cell k
  have hPxx_cell5 := Pxx_cell5 env input_var_x off_ip hAB_ops hx_norm
  have hTVar_cell5 :
      (env.get (off_ip + (2 * numLimbs - 1) + 5)).val < 6 * 2 ^ (2 * limbBits) := by
    have hcell : (Vector.map (Expression.eval env) TVar)[5]
        = env.get (off_ip + (2 * numLimbs - 1) + 5) := by
      rw [Vector.getElem_map, hTVar, Vector.getElem_mapRange]; rfl
    rw [← hcell, hT]
    by_cases hsel : input_sel = 1
    · rw [if_pos hsel, Vector.getElem_map, Vector.getElem_mapFinRange]
      rw [eval_three_mul, val_three_mul (by decide) _ (hb ⟨5, by decide⟩)]
      have hbe : 6 * 2 ^ (2 * limbBits) = 3 * (2 * 2 ^ (2 * limbBits)) := by ring
      rw [hbe]
      exact Nat.mul_lt_mul_of_pos_left hPxx_cell5 (by norm_num)
    · rw [if_neg hsel, Vector.getElem_map, Vector.getElem_mapFinRange,
        dif_neg (by decide : ¬ ((⟨5, by decide⟩ : Fin (2 * numLimbs - 1)).val < numLimbs)),
        show Expression.eval env (0 : Expression (F circomPrime)) = 0 from rfl,
        ZMod.val_zero]
      positivity
  have hTVar_poly : polyValue limbBits (Vector.map (Expression.eval env) TVar)
      = if input_sel = 1
        then 3 * (BigInt.value limbBits input_x * BigInt.value limbBits input_x)
        else BigInt.value limbBits input_dyU := by
    rw [hT]
    by_cases hsel : input_sel = 1
    · rw [if_pos hsel, if_pos hsel]; exact hTtrue_poly
    · rw [if_neg hsel, if_neg hsel]; exact hTfalse_poly
  have hlamval : BigInt.value limbBits (Vector.map (Expression.eval env) lamVar)
      = BigInt.value limbBits
        (Limbs32.emuOf32V (Vector.map (Expression.eval env) lam32Var)) := by
    rw [hlamVar, Limbs32.eval_emuOf32]
  refine ⟨⟨hlam_valid, fun hd0 => ?_⟩, interpolatedMul_requirements _ _ _ _⟩
  -- z = 0: denSafe = den, target = 3x² or dyU
  have hval_ne : BigInt.value limbBits input_den ≠ 0 := fun h => hd0 (hd_iff.mpr h)
  have hzc0 : zc = 0 := hzc_of_ne hval_ne
  have hden : Vector.map (Expression.eval env) denSafeVar = input_den := by
    rw [hdenSafeVar,
      eval_denSafeVec_of_flag_zero env input_var_den
        (var (F := F circomPrime) { index := i₀ }) (by simpa [hzc_def] using hzc0),
      h_input_den]
  have hdenSafe_limb3 : ∀ i : Fin numLimbs,
      (Expression.eval env (denSafeVar[i.val]'i.isLt)).val < 3 * 2 ^ limbBits := by
    intro i
    rw [show Expression.eval env (denSafeVar[i.val]'i.isLt)
        = (Vector.map (Expression.eval env) denSafeVar)[i.val]'i.isLt from
      (by rw [Vector.getElem_map]), hden]
    exact h_den_limb3 i
  have hspec_of : polyValue limbBits (Vector.map (Expression.eval env) TVar) % P256
        = BigInt.value limbBits (Vector.map (Expression.eval env) lamVar)
          * BigInt.value limbBits (Vector.map (Expression.eval env) denSafeVar) % P256 :=
    hmul ⟨fun i => by
        simpa [Vector.getElem_map] using hlam_valid64 i,
      hdenSafe_limb3, hTVar_cell, hTVar_cell5⟩
  have hdenSafe_eq : BigInt.value limbBits (Vector.map (Expression.eval env) denSafeVar)
      = BigInt.value limbBits input_den := by
    rw [hden]
  by_cases hsel : input_sel = 1
  · have hTVpoly : polyValue limbBits (Vector.map (Expression.eval env) TVar)
        = 3 * (BigInt.value limbBits input_x * BigInt.value limbBits input_x) := by
      rw [hTVar_poly, if_pos hsel]
    have hspec := hspec_of
    rw [hTVpoly, hdenSafe_eq, hlamval] at hspec
    rw [if_pos hsel]
    simp only [decodeFe]
    rw [mul_cast_of_mod_eq3 hspec]
    push_cast; ring
  · have hTVpoly : polyValue limbBits (Vector.map (Expression.eval env) TVar)
        = BigInt.value limbBits input_dyU := by
      rw [hTVar_poly, if_neg hsel]
    have hspec := hspec_of
    rw [hTVpoly, hdenSafe_eq, hlamval] at hspec
    rw [if_neg hsel]
    simp only [decodeFe]
    exact mul_cast_of_mod_eq3 hspec

set_option maxHeartbeats 3200000 in
theorem completeness : Completeness (F circomPrime) main Assumptions := by
  circuit_proof_start [
    Mux.circuit, Mux.Assumptions, Mux.Spec,
    MulModFoldT.circuitInv, MulModFoldT.Assumptions, MulModFoldT.Spec,
    Normalize.circuit, Normalize.main, Normalize.Assumptions, Normalize.Spec]
  obtain ⟨h_x_valid, h_sel_bool, h_dyU_limb, h_dyU_val, h_den_limb3, h_den_val3, h_den_alias⟩ :=
    h_assumptions
  obtain ⟨h_input_sel, h_input_x, h_input_dyU, h_input_den⟩ := h_input
  obtain ⟨hz, hAB_uses, hT, hlam⟩ := h_env
  simp only [MulMod.interpolatedMul_localLength] at hT hlam ⊢
  set zc := env.get i₀ with hzc_def
  set denSafeVar := denSafeVec input_var_den (var (F := F circomPrime) { index := i₀ })
    with hdenSafeVar
  set off_ip := i₀ + 1 with hoff_ip
  set PxxVar := (MulMod.interpolatedMul input_var_x input_var_x off_ip).1 with hPxxVar
  set TVar := Vector.mapRange (2 * numLimbs - 1) fun i =>
    var (F := F circomPrime) { index := off_ip + (2 * numLimbs - 1) + i } with hTVar
  set lam32Var := Vector.mapRange 8 fun i =>
    var (F := F circomPrime) { index := off_ip + (2 * numLimbs - 1) + (2 * numLimbs - 1) + i }
    with hlam32Var
  set lamVar := Limbs32.emuOf32 lam32Var with hlamVar
  have hden_get : ∀ (i : ℕ) (hi : i < 4),
      Expression.eval env.toEnvironment (input_var_den[i]'hi) = input_den[i]'hi := by
    intro i hi
    rw [← h_input_den, Vector.getElem_map]
  have hev_den0 : evalEmu env input_var_den = BigInt.value limbBits input_den := by
    rw [evalEmu, BigInt.value, ← h_input_den]
  have hz' : zc = if BigInt.value limbBits input_den = 0 then 1 else 0 := by
    rw [hzc_def]
    simpa [hev_den0] using hz
  have hz_bool : IsBool zc := by
    rw [hz']; split
    · exact IsBool.one
    · exact IsBool.zero
  specialize hT h_sel_bool
  have hzval : zc = 1 → BigInt.value limbBits input_den = 0 := by
    intro h1
    by_contra hv
    rw [hz', if_neg hv] at h1
    exact zero_ne_one h1
  have hzrow : zc * (input_den[0] + input_den[1] + input_den[2] + input_den[3]) = 0 := by
    by_cases hv : BigInt.value limbBits input_den = 0
    · rw [(IsZeroFeSum.sum_field_eq_zero_iff_value input_den h_den_limb3).mpr hv, mul_zero]
    · rw [hz', if_neg hv, zero_mul]
  have hden : Vector.map (Expression.eval env.toEnvironment) denSafeVar
      = if zc = 1 then emuOfNat 1 else input_den := by
    rw [hdenSafeVar,
      eval_denSafeVec env.toEnvironment input_var_den
        (var (F := F circomPrime) { index := i₀ })
        hz_bool (by rw [h_input_den]; exact hzval),
      h_input_den]
    rfl
  have hd_iff : decodeFe input_den = 0 ↔ BigInt.value limbBits input_den = 0 := by
    constructor
    · intro h
      apply h_den_alias
      have hdvd : (P256 : ℕ) ∣ BigInt.value limbBits input_den :=
        (ZMod.natCast_eq_zero_iff _ _).mp (by simpa [decodeFe] using h)
      rcases hdvd with ⟨k, hk⟩
      rw [hk]; exact Nat.mul_mod_right _ _
    · intro h; simp [decodeFe, h]
  have hx_norm : BigInt.Normalized limbBits
      (Vector.map (Expression.eval env.toEnvironment) input_var_x) := by
    rw [h_input_x]; exact h_x_valid.1
  have hpvAB := MulMod.interpolatedMul_usesLocalWitnesses off_ip off_ip input_var_x input_var_x env
    rfl hAB_uses
  have hbridge := MulMod.interpolatedMul_eval_bridge_uses env.toEnvironment off_ip input_var_x
    input_var_x hpvAB
  obtain ⟨hPxx_cell, hPxx_poly⟩ := Pxx_facts_of_bridge env.toEnvironment input_var_x off_ip hbridge
    hx_norm
  rw [h_input_x] at hPxx_poly
  have hb : ∀ j : Fin (2 * numLimbs - 1),
      3 * (Expression.eval env.toEnvironment PxxVar[j.val]).val < circomPrime := by
    intro j
    have hj := hPxx_cell j
    calc 3 * (Expression.eval env.toEnvironment PxxVar[j.val]).val
        < 3 * (numLimbs * 2 ^ (2 * limbBits)) := Nat.mul_lt_mul_of_pos_left hj (by norm_num)
      _ < circomPrime := by decide
  have hTtrue_poly : polyValue limbBits (Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapFinRange (2 * numLimbs - 1) fun k =>
          ((3 : F circomPrime) : Expression (F circomPrime)) * PxxVar[k.val]))
      = 3 * (BigInt.value limbBits input_x * BigInt.value limbBits input_x) := by
    rw [polyValue_three_mul env.toEnvironment PxxVar hb, hPxx_poly]
  have hTfalse_poly : polyValue limbBits (Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapFinRange (2 * numLimbs - 1) fun k =>
          if h : k.val < numLimbs then input_var_dyU[k.val]'h
          else (0 : Expression (F circomPrime))))
      = BigInt.value limbBits input_dyU := by
    rw [polyValue_pad env.toEnvironment input_var_dyU, h_input_dyU]
  have hdenSafe_limb3 : ∀ i : Fin numLimbs,
      (Expression.eval env.toEnvironment (denSafeVar[i.val]'i.isLt)).val
        < 3 * 2 ^ limbBits := by
    intro i
    rw [show Expression.eval env.toEnvironment (denSafeVar[i.val]'i.isLt)
        = (Vector.map (Expression.eval env.toEnvironment) denSafeVar)[i.val]'i.isLt from
      (by rw [Vector.getElem_map]), hden]
    by_cases hzc : zc = 1
    · rw [if_pos hzc]
      have h := emuOfNat_normalized 1 i
      rw [Fin.getElem_fin] at h
      omega
    · rw [if_neg hzc]; exact h_den_limb3 i
  have hTtrue_cell : ∀ k : Fin (2 * numLimbs - 1),
      (Expression.eval env.toEnvironment
        (((3 : F circomPrime) : Expression (F circomPrime)) * PxxVar[k.val])).val
        < 3 * numLimbs * 2 ^ (2 * limbBits) := by
    intro k
    rw [eval_three_mul, val_three_mul (by decide) _ (hb k)]
    have hj := hPxx_cell k
    have hbe : 3 * numLimbs * 2 ^ (2 * limbBits) = 3 * (numLimbs * 2 ^ (2 * limbBits)) := by ring
    rw [hbe]; exact Nat.mul_lt_mul_of_pos_left hj (by norm_num)
  have hTfalse_cell : ∀ k : Fin (2 * numLimbs - 1),
      (Expression.eval env.toEnvironment (if h : k.val < numLimbs
        then input_var_dyU[k.val]'h
        else (0 : Expression (F circomPrime)))).val < 3 * numLimbs * 2 ^ (2 * limbBits) := by
    intro k
    by_cases h : k.val < numLimbs
    · rw [dif_pos h]
      have hlt : (Expression.eval env.toEnvironment (input_var_dyU[k.val]'h)).val
          < 3 * 2 ^ limbBits := by
        have h2 : Expression.eval env.toEnvironment (input_var_dyU[k.val]'h)
            = input_dyU[k.val]'h := by
          rw [← h_input_dyU, Vector.getElem_map]
        rw [h2]
        simpa using h_dyU_limb ⟨k.val, h⟩
      have hbound : 3 * 2 ^ limbBits ≤ 3 * numLimbs * 2 ^ (2 * limbBits) := by
        have h1 : 2 ^ limbBits ≤ 2 ^ (2 * limbBits) :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
        calc 3 * 2 ^ limbBits ≤ 3 * 2 ^ (2 * limbBits) := by omega
          _ ≤ 3 * numLimbs * 2 ^ (2 * limbBits) := by
              nlinarith [Nat.two_pow_pos (2 * limbBits)]
      exact lt_of_lt_of_le hlt hbound
    · rw [dif_neg h,
        show Expression.eval env.toEnvironment (0 : Expression (F circomPrime)) = 0 from rfl,
        ZMod.val_zero]
      positivity
  have hTVar_cell : ∀ k : Fin (2 * numLimbs - 1),
      (env.get (off_ip + (2 * numLimbs - 1) + k.val)).val < 3 * numLimbs * 2 ^ (2 * limbBits) := by
    intro k
    have hcell : (Vector.map (Expression.eval env.toEnvironment) TVar)[k.val]
        = env.get (off_ip + (2 * numLimbs - 1) + k.val) := by
      rw [Vector.getElem_map, hTVar, Vector.getElem_mapRange]; rfl
    rw [← hcell, hT]
    by_cases hsel : input_sel = 1
    · rw [if_pos hsel, Vector.getElem_map, Vector.getElem_mapFinRange]
      exact hTtrue_cell k
    · rw [if_neg hsel, Vector.getElem_map, Vector.getElem_mapFinRange]
      exact hTfalse_cell k
  have hPxx_cell5 := Pxx_cell5_of_bridge env.toEnvironment input_var_x off_ip hbridge hx_norm
  have hTVar_cell5 :
      (env.toEnvironment.get (off_ip + (2 * numLimbs - 1) + 5)).val < 6 * 2 ^ (2 * limbBits) := by
    have hcell : (Vector.map (Expression.eval env.toEnvironment) TVar)[5]
        = env.toEnvironment.get (off_ip + (2 * numLimbs - 1) + 5) := by
      rw [Vector.getElem_map, hTVar, Vector.getElem_mapRange]; rfl
    rw [← hcell, hT]
    by_cases hsel : input_sel = 1
    · rw [if_pos hsel, Vector.getElem_map, Vector.getElem_mapFinRange]
      rw [eval_three_mul, val_three_mul (by decide) _ (hb ⟨5, by decide⟩)]
      have hbe : 6 * 2 ^ (2 * limbBits) = 3 * (2 * 2 ^ (2 * limbBits)) := by ring
      rw [hbe]
      exact Nat.mul_lt_mul_of_pos_left hPxx_cell5 (by norm_num)
    · rw [if_neg hsel, Vector.getElem_map, Vector.getElem_mapFinRange,
        dif_neg (by decide : ¬ ((⟨5, by decide⟩ : Fin (2 * numLimbs - 1)).val < numLimbs)),
        show Expression.eval env.toEnvironment (0 : Expression (F circomPrime)) = 0 from rfl,
        ZMod.val_zero]
      positivity
  have hTVar_poly : polyValue limbBits (Vector.map (Expression.eval env.toEnvironment) TVar)
      = if input_sel = 1
        then 3 * (BigInt.value limbBits input_x * BigInt.value limbBits input_x)
        else BigInt.value limbBits input_dyU := by
    rw [hT]
    by_cases hsel : input_sel = 1
    · rw [if_pos hsel, if_pos hsel]; exact hTtrue_poly
    · rw [if_neg hsel, if_neg hsel]; exact hTfalse_poly
  -- the witnessed λ evaluates to the canonical fused conditional quotient
  have hev_x : evalEmu env input_var_x = BigInt.value limbBits input_x := by
    rw [evalEmu, BigInt.value, ← h_input_x]
  have hev_dyU : evalEmu env input_var_dyU = BigInt.value limbBits input_dyU := by
    rw [evalEmu, BigInt.value, ← h_input_dyU]
  have hev_den : evalEmu env input_var_den = BigInt.value limbBits input_den := by
    rw [evalEmu, BigInt.value, ← h_input_den]
  have hlam_eval : Vector.map (Expression.eval env.toEnvironment) lam32Var
      = Limbs32.emu32OfNat (ZMod.val ((if input_sel = 1
            then ((3 * (BigInt.value limbBits input_x * BigInt.value limbBits input_x) : ℕ)
                : Specs.Secp256k1.Fp)
            else ((BigInt.value limbBits input_dyU : ℕ) : Specs.Secp256k1.Fp))
          * (((if BigInt.value limbBits input_den = 0 then 1
              else BigInt.value limbBits input_den : ℕ)) : Specs.Secp256k1.Fp)⁻¹)) := by
    rw [← hev_x, ← hev_dyU, ← hev_den]
    apply Vector.ext
    intro k hk
    have hentry : (Vector.map (Expression.eval env.toEnvironment) lam32Var)[k]'hk
        = env.get (off_ip + (2 * numLimbs - 1) + (2 * numLimbs - 1) + k) := by
      rw [hlam32Var, Vector.getElem_map, Vector.getElem_mapRange]; rfl
    rw [hentry]
    have hidx : off_ip + (2 * numLimbs - 1) + (2 * numLimbs - 1) + k
        = (2 * numLimbs - 1) + off_ip + (2 * numLimbs - 1) + k := by omega
    rw [hidx]
    exact hlam ⟨k, hk⟩
  have hq_lt : ZMod.val ((if input_sel = 1
          then ((3 * (BigInt.value limbBits input_x * BigInt.value limbBits input_x) : ℕ)
              : Specs.Secp256k1.Fp)
          else ((BigInt.value limbBits input_dyU : ℕ) : Specs.Secp256k1.Fp))
        * (((if BigInt.value limbBits input_den = 0 then 1
            else BigInt.value limbBits input_den : ℕ)) : Specs.Secp256k1.Fp)⁻¹) < P256 :=
    ZMod.val_lt _
  have hlam32_norm : BigInt.Normalized 32
      (Vector.map (Expression.eval env.toEnvironment) lam32Var) := by
    rw [hlam_eval]; exact Limbs32.emu32OfNat_normalized _
  have hlam_norm : BigInt.Normalized limbBits
      (Vector.map (Expression.eval env.toEnvironment) lamVar) := by
    rw [hlamVar, Limbs32.eval_emuOf32]
    exact Limbs32.normalized_emuOf32 hlam32_norm
  have hlam_val : BigInt.value limbBits (Vector.map (Expression.eval env.toEnvironment) lamVar)
      = ZMod.val ((if input_sel = 1
            then ((3 * (BigInt.value limbBits input_x * BigInt.value limbBits input_x) : ℕ)
                : Specs.Secp256k1.Fp)
            else ((BigInt.value limbBits input_dyU : ℕ) : Specs.Secp256k1.Fp))
          * (((if BigInt.value limbBits input_den = 0 then 1
              else BigInt.value limbBits input_den : ℕ)) : Specs.Secp256k1.Fp)⁻¹) := by
    rw [hlamVar, Limbs32.eval_emuOf32, hlam_eval, Limbs32.emuOf32V_emu32OfNat]
    exact value_emuOfNat (lt_trans hq_lt P256_lt)
  have hdenSafe_val : BigInt.value limbBits
        (Vector.map (Expression.eval env.toEnvironment) denSafeVar)
      = (if BigInt.value limbBits input_den = 0 then 1
          else BigInt.value limbBits input_den) := by
    rw [hden]
    by_cases hv : BigInt.value limbBits input_den = 0
    · have hzc1 : zc = 1 := by rw [hz', if_pos hv]
      rw [if_pos hzc1, value_emuOfNat_one, if_pos hv]
    · have hzc0 : zc = 0 := by rw [hz', if_neg hv]
      rw [hzc0, if_neg (zero_ne_one (α := F circomPrime)), if_neg hv]
  have hdvSafe_ne : (((if BigInt.value limbBits input_den = 0 then 1
        else BigInt.value limbBits input_den : ℕ)) : Specs.Secp256k1.Fp) ≠ 0 := by
    by_cases hv : BigInt.value limbBits input_den = 0
    · rw [if_pos hv, Nat.cast_one]
      exact one_ne_zero
    · rw [if_neg hv]
      intro hc
      exact hv (hd_iff.mp (by simpa [decodeFe] using hc))
  have hmain : polyValue limbBits (Vector.map (Expression.eval env.toEnvironment) TVar)
        ≤ 3 * (P256 * P256)
      ∧ polyValue limbBits (Vector.map (Expression.eval env.toEnvironment) TVar) % P256
        = BigInt.value limbBits (Vector.map (Expression.eval env.toEnvironment) lamVar)
          * BigInt.value limbBits (Vector.map (Expression.eval env.toEnvironment) denSafeVar)
          % P256 := by
    rw [hlam_val, hdenSafe_val]
    by_cases hsel : input_sel = 1
    · have hTVpoly : polyValue limbBits (Vector.map (Expression.eval env.toEnvironment) TVar)
          = 3 * (BigInt.value limbBits input_x * BigInt.value limbBits input_x) := by
        rw [hTVar_poly, if_pos hsel]
      refine ⟨?_, ?_⟩
      · rw [hTVpoly]
        have hx : BigInt.value limbBits input_x < P256 := h_x_valid.2
        have hmul_le : BigInt.value limbBits input_x * BigInt.value limbBits input_x
            ≤ P256 * P256 := Nat.mul_le_mul (le_of_lt hx) (le_of_lt hx)
        omega
      · rw [hTVpoly, if_pos hsel]
        exact witness_cert_nonzero3 hdvSafe_ne
    · have hTVpoly : polyValue limbBits (Vector.map (Expression.eval env.toEnvironment) TVar)
          = BigInt.value limbBits input_dyU := by
        rw [hTVar_poly, if_neg hsel]
      refine ⟨?_, ?_⟩
      · rw [hTVpoly]
        have h1 : P256 ≤ P256 * P256 := by nlinarith [P256_pos]
        have := h_dyU_val
        omega
      · rw [hTVpoly, if_neg hsel]
        exact witness_cert_nonzero3 hdvSafe_ne
  exact ⟨by
      simpa [circuit_norm, hzc_def, hden_get 0 (by omega), hden_get 1 (by omega),
        hden_get 2 (by omega), hden_get 3 (by omega)] using hzrow,
    MulMod.interpolatedMul_completeness off_ip input_var_x input_var_x env hpvAB,
    h_sel_bool,
    hlam32_norm,
    ⟨⟨fun i => by
        simpa [Vector.getElem_map] using hlam_norm i,
      hdenSafe_limb3, hTVar_cell, hTVar_cell5⟩, hmain.2⟩⟩

def circuit : FormalCircuit (F circomPrime) Inputs Emu32 where
  main; elaborated; Assumptions; Spec; soundness; completeness

/-- Map-stability transfer for a `fields n` witness bundle (the `TargetVec` case,
mirroring `emu_map_eval_eq_of_eval_eq` for `Emu`). -/
private theorem fields_map_eval_eq_of_eval_eq {n : ℕ}
    {v : Var (fields n) (F circomPrime)} {env env' : ProverEnvironment (F circomPrime)}
    (h : eval env v = eval env' v) :
    Vector.map (Expression.eval env.toEnvironment) v
      = Vector.map (Expression.eval env'.toEnvironment) v := by
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_map]
  have h_i : (eval env v)[i] = (eval env' v)[i] := by
    simpa only using congrArg (fun y : (fields n) (F circomPrime) => y[i]) h
  rw [← ProvableType.getElem_eval_fields_prover (env := env) v i hi,
    ← ProvableType.getElem_eval_fields_prover (env := env') v i hi] at h_i
  exact h_i

set_option maxHeartbeats 6400000 in
theorem computableWitnesses : circuit.base.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  obtain ⟨sel, x, dyU, den⟩ := input
  have hzf : ∀ (c : ProverEnvironment (F circomPrime) → F circomPrime) (o : ℕ),
      (witnessField c).localLength o = 1 := by
    intro c o; simp only [circuit_norm]
  have haz : ∀ (e : Expression (F circomPrime)) (o : ℕ),
      (assertZero e).localLength o = 0 := by
    intro e o; simp only [circuit_norm]
  have hmxT : ∀ (X : Var (Mux.Inputs (fields (2 * numLimbs - 1))) (F circomPrime)) (o : ℕ),
      (subcircuit (Mux.circuit (M := fields (2 * numLimbs - 1))) X).localLength o
        = 2 * numLimbs - 1 := by
    intro X o; simp only [circuit_norm, Mux.circuit]
  have hip : ∀ (a b : Var Emu (F circomPrime)) (o : ℕ),
      (MulMod.interpolatedMul a b).localLength o = 2 * numLimbs - 1 := by
    intro a b o; exact MulMod.interpolatedMul_localLength o a b
  have hw : ∀ (c : ProverEnvironment (F circomPrime) → Emu32 (F circomPrime)) (o : ℕ),
      (ProvableType.witness (α := Emu32) c).localLength o = 8 := by
    intro c o; simp only [circuit_norm]
  have hvp : ∀ (v : Var Emu32 (F circomPrime)) (o : ℕ),
      (Normalize.circuit secpParams32 v).localLength o = 248 := fun _ _ => rfl
  have hsize : size Emu32 = 8 := rfl
  have hsize7 : size (fields (2 * numLimbs - 1)) = 2 * numLimbs - 1 := rfl
  unfold main
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.provableWitness_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.witnessField_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.assertZero_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.pure_structuralComputableWitnesses_iff,
    hzf, haz, hmxT, hip, hw, hvp, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- z witness: reads only the parent input `den`
    intro _ h_input
    have hden : evalEmu env den = evalEmu env' den :=
      evalEmu_eq_of_eval_eq (by
        simpa [circuit_norm] using
          congrArg (fun v : Inputs (F circomPrime) => v.den) h_input)
    simp only [hden]
  · -- the zero-flag row carries no witnesses
    trivial
  · -- Pxx ← interpolatedMul x x
    exact MulMod.interpolatedMul_structuralComputableWitnesses (Parent := Inputs)
      _ x x (offset + 1)
      (by
        intro k e e' h_off h_agree h_in
        have hx : eval e x = eval e' x := by
          simpa [circuit_norm] using congrArg (fun v : Inputs (F circomPrime) => v.x) h_in
        exact ⟨hx, hx⟩)
      env env'
  · -- T ← Mux (M := fields (2m-1)) { sel, Ttrue, Tfalse }
    exact Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) (Mux.circuit (M := fields (2 * numLimbs - 1))) _
      { selector := sel,
        ifTrue := Vector.mapFinRange (2 * numLimbs - 1) fun k =>
          ((3 : F circomPrime) : Expression (F circomPrime))
            * ((MulMod.interpolatedMul x x).output (offset + 1))[k.val],
        ifFalse := Vector.mapFinRange (2 * numLimbs - 1) fun k =>
          if h : k.val < numLimbs then dyU[k.val]'h else (0 : Expression (F circomPrime)) }
      (offset + 1 + (2 * numLimbs - 1))
      (by
        intro k e e' hle h_agree h_in
        have hsel : Expression.eval e.toEnvironment sel = Expression.eval e'.toEnvironment sel := by
          simpa [circuit_norm] using congrArg (fun v : Inputs (F circomPrime) => v.sel) h_in
        have hPc := MulMod.interpolatedMul_output_stable
          (offset + 1) x x h_agree (by omega)
        have hDyMap : Vector.map (Expression.eval e.toEnvironment) dyU
            = Vector.map (Expression.eval e'.toEnvironment) dyU := by
          simpa [circuit_norm] using congrArg (fun v : Inputs (F circomPrime) => v.dyU) h_in
        have hTT_eq : Vector.map (Expression.eval e.toEnvironment)
              (Vector.mapFinRange (2 * numLimbs - 1) fun j =>
                ((3 : F circomPrime) : Expression (F circomPrime))
                  * ((MulMod.interpolatedMul x x).output (offset + 1))[j.val])
            = Vector.map (Expression.eval e'.toEnvironment)
              (Vector.mapFinRange (2 * numLimbs - 1) fun j =>
                ((3 : F circomPrime) : Expression (F circomPrime))
                  * ((MulMod.interpolatedMul x x).output (offset + 1))[j.val]) := by
          apply Vector.ext
          intro i hi
          simp only [Vector.getElem_map, Vector.getElem_mapFinRange, eval_three_mul]
          have hPi := congrArg
            (fun v : Vector (F circomPrime) (2 * numLimbs - 1) => v[i]'hi) hPc
          simp only [Vector.getElem_map] at hPi
          rw [hPi]
        have hTF_eq : Vector.map (Expression.eval e.toEnvironment)
              (Vector.mapFinRange (2 * numLimbs - 1) fun j =>
                if h : j.val < numLimbs then dyU[j.val]'h
                else (0 : Expression (F circomPrime)))
            = Vector.map (Expression.eval e'.toEnvironment)
              (Vector.mapFinRange (2 * numLimbs - 1) fun j =>
                if h : j.val < numLimbs then dyU[j.val]'h
                else (0 : Expression (F circomPrime))) := by
          apply Vector.ext
          intro i hi
          simp only [Vector.getElem_map, Vector.getElem_mapFinRange]
          split_ifs with h
          · have h2 := congrArg
              (fun v : Vector (F circomPrime) numLimbs => v[i]'h) hDyMap
            simp only [Vector.getElem_map] at h2
            rw [h2]
          · rfl
        simp only [circuit_norm] at hTT_eq hTF_eq ⊢
        simp only [hsel, hTT_eq, hTF_eq])
      (Mux.computableWitnesses (M := fields (2 * numLimbs - 1))) env env'
  · -- λ witness : reads only the parent inputs (via evalEmu / sel)
    intro _ h_input
    have hden : evalEmu env den = evalEmu env' den :=
      evalEmu_eq_of_eval_eq (by
        simpa [circuit_norm] using
          congrArg (fun v : Inputs (F circomPrime) => v.den) h_input)
    have hx : evalEmu env x = evalEmu env' x :=
      evalEmu_eq_of_eval_eq (by
        simpa [circuit_norm] using
          congrArg (fun v : Inputs (F circomPrime) => v.x) h_input)
    have hdyU : evalEmu env dyU = evalEmu env' dyU :=
      evalEmu_eq_of_eval_eq (by
        simpa [circuit_norm] using
          congrArg (fun v : Inputs (F circomPrime) => v.dyU) h_input)
    have hsel : Expression.eval env.toEnvironment sel = Expression.eval env'.toEnvironment sel := by
      simpa [circuit_norm] using congrArg (fun v : Inputs (F circomPrime) => v.sel) h_input
    simp only [hden, hx, hdyU, hsel]
  · -- 32-bit limb range checks on λ
    exact Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) (Normalize.circuit secpParams32) _
      ((ProvableType.witness (α := Emu32) fun env =>
        let denFp : Specs.Secp256k1.Fp :=
          ((if evalEmu env den = 0 then 1 else evalEmu env den : ℕ) : Specs.Secp256k1.Fp)
        let numFp : Specs.Secp256k1.Fp :=
          if Expression.eval env.toEnvironment sel = 1
          then ((3 * (evalEmu env x * evalEmu env x) : ℕ) : Specs.Secp256k1.Fp)
          else ((evalEmu env dyU : ℕ) : Specs.Secp256k1.Fp)
        Limbs32.emu32OfNat (numFp * denFp⁻¹).val).output
          (offset + 1 + (2 * numLimbs - 1) + (2 * numLimbs - 1)))
      _
      (by
        intro k e e' hle h_agree _
        exact emu32WitnessOutput_stable _ h_agree
          (offset := offset + 1 + (2 * numLimbs - 1) + (2 * numLimbs - 1))
          (by omega))
      (Normalize.computableWitnesses secpParams32) env env'
  · -- MulModFoldT { λ, denSafe, T }
    exact Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs)
      (MulModFoldT.circuitInv (2 ^ limbBits) (3 * 2 ^ limbBits) (3 * numLimbs * 2 ^ (2 * limbBits))
        (6 * 2 ^ (2 * limbBits))
        (by decide) (by decide) (by decide) (by decide)) _
      { a := Limbs32.emuOf32 ((ProvableType.witness (α := Emu32) fun env =>
          let denFp : Specs.Secp256k1.Fp :=
            ((if evalEmu env den = 0 then 1 else evalEmu env den : ℕ) : Specs.Secp256k1.Fp)
          let numFp : Specs.Secp256k1.Fp :=
            if Expression.eval env.toEnvironment sel = 1
            then ((3 * (evalEmu env x * evalEmu env x) : ℕ) : Specs.Secp256k1.Fp)
            else ((evalEmu env dyU : ℕ) : Specs.Secp256k1.Fp)
          Limbs32.emu32OfNat (numFp * denFp⁻¹).val).output
            (offset + 1 + (2 * numLimbs - 1) + (2 * numLimbs - 1))),
        b := denSafeVec den
          ((witnessField (fun env => if evalEmu env den = 0 then 1 else 0)).output offset),
        target := (subcircuit (Mux.circuit (M := fields (2 * numLimbs - 1)))
          { selector := sel,
            ifTrue := Vector.mapFinRange (2 * numLimbs - 1) fun k =>
              ((3 : F circomPrime) : Expression (F circomPrime))
                * ((MulMod.interpolatedMul x x).output (offset + 1))[k.val],
            ifFalse := Vector.mapFinRange (2 * numLimbs - 1) fun k =>
              if h : k.val < numLimbs then dyU[k.val]'h
              else (0 : Expression (F circomPrime)) }).output
          (offset + 1 + (2 * numLimbs - 1)) }
      _
      (by
        intro k e e' hle h_agree h_in
        have hlam := emu32WitnessOutput_stable
          (fun env =>
            let denFp : Specs.Secp256k1.Fp :=
              ((if evalEmu env den = 0 then 1 else evalEmu env den : ℕ) : Specs.Secp256k1.Fp)
            let numFp : Specs.Secp256k1.Fp :=
              if Expression.eval env.toEnvironment sel = 1
              then ((3 * (evalEmu env x * evalEmu env x) : ℕ) : Specs.Secp256k1.Fp)
              else ((evalEmu env dyU : ℕ) : Specs.Secp256k1.Fp)
            Limbs32.emu32OfNat (numFp * denFp⁻¹).val)
          h_agree
          (offset := offset + 1 + (2 * numLimbs - 1) + (2 * numLimbs - 1))
          (k := k) (by omega)
        have hdenMap : Vector.map (Expression.eval e.toEnvironment)
              (denSafeVec den
                ((witnessField (fun env => if evalEmu env den = 0 then 1 else 0)).output offset))
            = Vector.map (Expression.eval e'.toEnvironment)
              (denSafeVec den
                ((witnessField (fun env => if evalEmu env den = 0 then 1 else 0)).output offset)) := by
          have hsel : Expression.eval e.toEnvironment
                ((witnessField (fun env => if evalEmu env den = 0 then 1 else 0)).output offset)
              = Expression.eval e'.toEnvironment
                ((witnessField (fun env => if evalEmu env den = 0 then 1 else 0)).output offset) := by
            simpa [circuit_norm] using h_agree offset (by omega)
          have hd : Vector.map (Expression.eval e.toEnvironment) den
              = Vector.map (Expression.eval e'.toEnvironment) den := by
            simpa [circuit_norm] using congrArg (fun v : Inputs (F circomPrime) => v.den) h_in
          exact denSafeVec_map_eval_eq hsel hd
        have hTO := Mux.eval_output_of_agreesBelow (M := fields (2 * numLimbs - 1))
          { selector := sel,
            ifTrue := Vector.mapFinRange (2 * numLimbs - 1) fun k =>
              ((3 : F circomPrime) : Expression (F circomPrime))
                * ((MulMod.interpolatedMul x x).output (offset + 1))[k.val],
            ifFalse := Vector.mapFinRange (2 * numLimbs - 1) fun k =>
              if h : k.val < numLimbs then dyU[k.val]'h
              else (0 : Expression (F circomPrime)) }
          h_agree (offset := offset + 1 + (2 * numLimbs - 1))
          (k := k) (by omega)
        simp only [circuit_norm]
        rw [MulModFoldT.Inputs.mk.injEq]
        exact ⟨Limbs32.emuOf32_map_stable hlam, hdenMap,
          fields_map_eval_eq_of_eval_eq hTO⟩)
      (MulModFoldT.computableWitnessesInv (2 ^ limbBits) (3 * 2 ^ limbBits)
        (3 * numLimbs * 2 ^ (2 * limbBits)) (6 * 2 ^ (2 * limbBits))
        (by decide) (by decide) (by decide) (by decide)) env env'

set_option maxHeartbeats 3200000 in
lemma eval_output_of_agreesBelow (input : Var Inputs (F circomPrime)) {offset k : ℕ}
    {env env' : ProverEnvironment (F circomPrime)}
    (h_agree : env.AgreesBelow k env')
    (hk : offset + 1 + (2 * numLimbs - 1) + (2 * numLimbs - 1)
        + 8 ≤ k) :
    eval env ((main input).output offset) = eval env' ((main input).output offset) := by
  obtain ⟨sel, x, dyU, den⟩ := input
  have hout : (main ⟨sel, x, dyU, den⟩).output offset
      = (ProvableType.witness (α := Emu32) fun env =>
          let denFp : Specs.Secp256k1.Fp :=
            ((if evalEmu env den = 0 then 1 else evalEmu env den : ℕ) : Specs.Secp256k1.Fp)
          let numFp : Specs.Secp256k1.Fp :=
            if Expression.eval env.toEnvironment sel = 1
            then ((3 * (evalEmu env x * evalEmu env x) : ℕ) : Specs.Secp256k1.Fp)
            else ((evalEmu env dyU : ℕ) : Specs.Secp256k1.Fp)
          Limbs32.emu32OfNat (numFp * denFp⁻¹).val).output
        (offset + 1
          + (MulMod.interpolatedMul x x).localLength (offset + 1)
          + (2 * numLimbs - 1)) := rfl
  have hlen : (MulMod.interpolatedMul x x).localLength (offset + 1)
      = 2 * numLimbs - 1 :=
    MulMod.interpolatedMul_localLength _ _ _
  rw [hout, hlen]
  exact emu32WitnessOutput_stable _ h_agree (by omega)

end DivOrZeroS32
end Solution.Secp256k1ScalarMul
