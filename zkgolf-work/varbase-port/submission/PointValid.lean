import Solution.Secp256k1ScalarMul.CompleteAddTheorems
import Solution.Secp256k1ScalarMul.CompleteAdd
import Solution.Secp256k1ScalarMul.AddMod
import Solution.Secp256k1ScalarMul.Mux
import Solution.Secp256k1ScalarMul.Equal
import Solution.Secp256k1ScalarMul.ValidPBytes
import Solution.Secp256k1ScalarMul.MulModSqN32
import Solution.Secp256k1ScalarMul.MulModFoldTInv
import Solution.Secp256k1ScalarMul.Bytes32
import Challenge.Utils.ComputableWitnessLemmas



namespace Solution.Secp256k1ScalarMul
namespace PointValid

structure Outputs (F : Type) where
  x : Vector F coordBytes
  y : Vector F coordBytes
deriving ProvableStruct


def sevenConst : Var Emu (F circomPrime) := emuConst 7

/-- The limb vector whose value is `7·(1 − isInf)`: `7` on the finite branch and
`0` on the infinity branch.  Adding it to `x³` turns the curve equation into a
congruence that is satisfiable in *both* branches, which is what lets the
residue `t = y·y − x³ − 7` be replaced by a bare modular certificate. -/
def sevenMask (isInf : Expression (F circomPrime)) : Var Emu (F circomPrime) :=
  Vector.ofFn fun k : Fin numLimbs =>
    if k.val = 0 then
      ((((1 : F circomPrime) : Expression (F circomPrime)) - isInf) *
        ((7 : F circomPrime) : Expression (F circomPrime)))
    else 0

/-- The `2·numLimbs − 1`-cell certificate target `x² ⊛ x + 7·(1 − isInf)`: the raw
convolution of the materialised square `x2` with `x`, with the curve constant
added into cell `0`.  Every entry is a *sum*, so no borrow is needed and each
cell stays far below the native modulus. -/
def curveTarget (Pc : Var (fields (2 * numLimbs - 1)) (F circomPrime))
    (isInf : Expression (F circomPrime)) : Var (fields (2 * numLimbs - 1)) (F circomPrime) :=
  Vector.mapFinRange (2 * numLimbs - 1) fun k =>
    if k.val = 0 then
      Pc[k.val] + ((((1 : F circomPrime) : Expression (F circomPrime)) - isInf) *
        ((7 : F circomPrime) : Expression (F circomPrime)))
    else Pc[k.val]

def main (P : Var FlaggedPoint (F circomPrime)) :
    Circuit (F circomPrime) (Var Outputs (F circomPrime)) := do
  -- The flag and both coordinate encodings are canonical.
  assertZero (P.isInf * (P.isInf - 1))
  let xb ← ValidPBytes.circuit P.x
  let yb ← ValidPBytes.circuit P.y

  -- `y² = x³ + 7` in the finite branch.  The curve equation is only a
  -- *congruence*, so neither the cube nor the residue needs a witnessed value:
  -- only `x²` is materialised, the product `x²·x` is kept as a raw `2m−1`-cell
  -- convolution, and one folded target certificate asserts
  -- `y·y ≡ x² ⊛ x + 7·(1−isInf) (mod p)`.
  let x2 ← subcircuit MulModSqN32.circuit
    { a := Bytes32.ofBytes xb, b := Bytes32.ofBytes xb }
  let Pc ← MulMod.interpolatedMul x2 P.x
  MulModFoldT.circuitInv (2 ^ 64) (2 ^ 64) (5 * 2 ^ 128) (5 * 2 ^ 128)
    (by decide) (by decide) (by decide) (by decide)
    { a := P.y, b := P.y, target := curveTarget Pc P.isInf }
  -- On the infinity branch both coordinates are zero (all limbs are canonical,
  -- so their sum vanishes only when every limb does).
  assertZero (P.isInf * (P.x[0] + P.x[1] + P.x[2] + P.x[3] +
    P.y[0] + P.y[1] + P.y[2] + P.y[3]))
  return { x := xb, y := yb }

instance elaborated : ElaboratedCircuit (F circomPrime) FlaggedPoint Outputs main := by
  elaborate_circuit


def Assumptions (_ : FlaggedPoint (F circomPrime))
    (_data : ProverData (F circomPrime)) : Prop := True


def Spec (P : FlaggedPoint (F circomPrime)) : Prop :=
  P.Valid ∧ (P.isInf = 1 → P.x = emuOfNat 0 ∧ P.y = emuOfNat 0)

def OutputSpec (P : FlaggedPoint (F circomPrime))
    (out : Outputs (F circomPrime)) (_data : ProverData (F circomPrime)) : Prop :=
  Spec P ∧ ToBytes.Spec P.x out.x ∧ ToBytes.Spec P.y out.y

def ProverAssumptions (P : FlaggedPoint (F circomPrime))
    (_data : ProverData (F circomPrime)) (_hint : ProverHint (F circomPrime)) :
    Prop := Spec P

def ProverSpec (_P : FlaggedPoint (F circomPrime))
    (_out : Outputs (F circomPrime)) (_hint : ProverHint (F circomPrime)) :
    Prop := True

private lemma seven_valid : Fe.Valid (emuOfNat 7) :=
  CompleteAdd.fe_valid_emuOfNat (by decide)

private lemma eval_sevenConst (env : Environment (F circomPrime)) :
    Vector.map (Expression.eval env) sevenConst = emuOfNat 7 := by
  exact CompleteAdd.eval_emuConst env 7

private lemma decode_seven : decodeFe (emuOfNat 7) = 7 := by
  rw [decodeFe, CompleteAdd.value_emuOfNat (by decide)]
  norm_num

private lemma eval_sevenMask (env : Environment (F circomPrime))
    (e : Expression (F circomPrime)) (hb : IsBool (Expression.eval env e)) :
    Vector.map (Expression.eval env) (sevenMask e)
      = emuOfNat (if Expression.eval env e = 1 then 0 else 7) := by
  apply Vector.ext
  intro i hi
  have hi4 : i < 4 := hi
  rw [Vector.getElem_map, sevenMask, Vector.getElem_ofFn]
  have h7 : (7 : ℕ) % 2 ^ limbBits = 7 := by norm_num [limbBits]
  have h7d : (7 : ℕ) / 2 ^ limbBits = 0 := by norm_num [limbBits]
  have h7dd : (7 : ℕ) / 2 ^ (limbBits * 2) = 0 := by norm_num [limbBits]
  have h7ddd : (7 : ℕ) / 2 ^ (limbBits * 3) = 0 := by norm_num [limbBits]
  rcases hb with h | h <;> interval_cases i <;>
    simp [circuit_norm, h, emuOfNat, limbOfNat, Vector.getElem_ofFn, h7, h7d, h7dd, h7ddd]

private lemma sevenMask_valid (env : Environment (F circomPrime))
    (e : Expression (F circomPrime)) (hb : IsBool (Expression.eval env e)) :
    Fe.Valid (Vector.map (Expression.eval env) (sevenMask e)) := by
  rw [eval_sevenMask env e hb]
  split
  · exact CompleteAdd.fe_valid_emuOfNat (by decide : (0:ℕ) < P256)
  · exact CompleteAdd.fe_valid_emuOfNat (by decide : (7:ℕ) < P256)

private lemma decode_sevenMask (env : Environment (F circomPrime))
    (e : Expression (F circomPrime)) (hb : IsBool (Expression.eval env e)) :
    decodeFe (Vector.map (Expression.eval env) (sevenMask e))
      = if Expression.eval env e = 1 then 0 else 7 := by
  rw [eval_sevenMask env e hb]
  split
  · rw [decodeFe,
      CompleteAdd.value_emuOfNat (by norm_num : (0:ℕ) < 2 ^ (limbBits * numLimbs)),
      Nat.cast_zero]
  · rw [decodeFe,
      CompleteAdd.value_emuOfNat (by norm_num : (7:ℕ) < 2 ^ (limbBits * numLimbs))]
    norm_num

private lemma value_sevenMask (env : Environment (F circomPrime))
    (e : Expression (F circomPrime)) (hb : IsBool (Expression.eval env e)) :
    BigInt.value limbBits (Vector.map (Expression.eval env) (sevenMask e))
      = if Expression.eval env e = 1 then 0 else 7 := by
  rw [eval_sevenMask env e hb]
  split
  · exact CompleteAdd.value_emuOfNat (by norm_num : (0:ℕ) < 2 ^ (limbBits * numLimbs))
  · exact CompleteAdd.value_emuOfNat (by norm_num : (7:ℕ) < 2 ^ (limbBits * numLimbs))

/-- Turn the folded certificate's nat-congruence conclusion into an `Fp`
equation. -/
private lemma sevenMask_stable {e e' : ProverEnvironment (F circomPrime)}
    (i : Expression (F circomPrime))
    (h : Expression.eval e.toEnvironment i = Expression.eval e'.toEnvironment i) :
    Vector.map (Expression.eval e.toEnvironment) (sevenMask i)
      = Vector.map (Expression.eval e'.toEnvironment) (sevenMask i) := by
  apply Vector.ext
  intro j hj
  have hj4 : j < 4 := hj
  rw [Vector.getElem_map, Vector.getElem_map, sevenMask, Vector.getElem_ofFn]
  interval_cases j <;> simp [circuit_norm, h]

/-! ### The raw cube convolution and its certificate target -/

open MulMod in
/-- Per-cell bound and value identity for `av ⊛ bv` from the per-cell evaluation
bridge (shared by the soundness and completeness directions). -/
private lemma Pab_facts_of_bridge (env : Environment (F circomPrime))
    (av bv : Var Emu (F circomPrime)) (off : ℕ)
    (hbridge : ∀ k : Fin (2 * numLimbs - 1),
      Expression.eval env (MulMod.interpolatedMul av bv off).1[k.val]
        = Expression.eval env (bigIntMulNoReduce av bv)[k.val])
    (ha : BigInt.Normalized limbBits (Vector.map (Expression.eval env) av))
    (hb : BigInt.Normalized limbBits (Vector.map (Expression.eval env) bv)) :
    (∀ k : Fin (2 * numLimbs - 1),
        (Expression.eval env (MulMod.interpolatedMul av bv off).1[k.val]).val
          < numLimbs * (2 ^ limbBits * 2 ^ limbBits))
      ∧ polyValue limbBits (Vector.map (Expression.eval env) (MulMod.interpolatedMul av bv off).1)
          = BigInt.value limbBits (Vector.map (Expression.eval env) av)
            * BigInt.value limbBits (Vector.map (Expression.eval env) bv) := by
  have ha' : ∀ i : Fin numLimbs, (Expression.eval env av[i.val]).val < 2 ^ limbBits := by
    intro i; have := ha i; rwa [Fin.getElem_fin, Vector.getElem_map] at this
  have hb' : ∀ i : Fin numLimbs, (Expression.eval env bv[i.val]).val < 2 ^ limbBits := by
    intro i; have := hb i; rwa [Fin.getElem_fin, Vector.getElem_map] at this
  have hfield : numLimbs * (2 ^ limbBits * 2 ^ limbBits) < circomPrime := by decide
  refine ⟨fun k => ?_, ?_⟩
  · rw [hbridge k]
    exact MulModTargetW2.val_coeff_lt_gen2 env av bv k ha' hb' hfield
  · have hPmap : Vector.map (Expression.eval env) (MulMod.interpolatedMul av bv off).1
        = Vector.map (Expression.eval env) (bigIntMulNoReduce av bv) := by
      apply Vector.ext
      intro k hk
      rw [Vector.getElem_map, Vector.getElem_map]
      exact hbridge ⟨k, hk⟩
    rw [hPmap, MulModTargetW2.polyValue_mul_eq_gen2 env av bv ha' hb' hfield]

open MulMod in
/-- Per-cell bound and value identity for the raw convolution `av ⊛ bv`, both
operands normalized. -/
private lemma Pab_facts (env : Environment (F circomPrime))
    (av bv : Var Emu (F circomPrime)) (off : ℕ)
    (hAB : Operations.forAllNoOffset
        { assert := fun e => Expression.eval env e = 0, lookup := fun l => l.Soundness env,
          interact := fun i => i.Guarantees env,
          subcircuit := fun {_n} s => s.Assumptions env → s.Spec env }
        (MulMod.interpolatedMul av bv off).2)
    (ha : BigInt.Normalized limbBits (Vector.map (Expression.eval env) av))
    (hb : BigInt.Normalized limbBits (Vector.map (Expression.eval env) bv)) :
    (∀ k : Fin (2 * numLimbs - 1),
        (Expression.eval env (MulMod.interpolatedMul av bv off).1[k.val]).val
          < numLimbs * (2 ^ limbBits * 2 ^ limbBits))
      ∧ polyValue limbBits (Vector.map (Expression.eval env) (MulMod.interpolatedMul av bv off).1)
          = BigInt.value limbBits (Vector.map (Expression.eval env) av)
            * BigInt.value limbBits (Vector.map (Expression.eval env) bv) := by
  have ha' : ∀ i : Fin numLimbs, (Expression.eval env av[i.val]).val < 2 ^ limbBits := by
    intro i; have := ha i; rwa [Fin.getElem_fin, Vector.getElem_map] at this
  have hb' : ∀ i : Fin numLimbs, (Expression.eval env bv[i.val]).val < 2 ^ limbBits := by
    intro i; have := hb i; rwa [Fin.getElem_fin, Vector.getElem_map] at this
  have hfield : numLimbs * (2 ^ limbBits * 2 ^ limbBits) < circomPrime := by decide
  have hpm : 2 * numLimbs - 1 < circomPrime := by decide
  have h_pts := MulMod.interpolatedMul_soundness off av bv env hAB
  have hbridge := MulMod.interpolatedMul_eval_bridge env off av bv hpm h_pts
  exact Pab_facts_of_bridge env av bv off hbridge ha hb

/-- The evaluated `curveTarget` cell. -/
private lemma eval_curveTarget_cell (env : Environment (F circomPrime))
    (Pc : Var (fields (2 * numLimbs - 1)) (F circomPrime))
    (isInf : Expression (F circomPrime)) (k : Fin (2 * numLimbs - 1)) :
    (Vector.map (Expression.eval env) (curveTarget Pc isInf))[k.val]
      = Expression.eval env Pc[k.val]
        + (if k.val = 0 then
            ((1 : F circomPrime) - Expression.eval env isInf) * (7 : F circomPrime)
          else 0) := by
  rw [Vector.getElem_map, curveTarget, Vector.getElem_mapFinRange]
  by_cases h : k.val = 0
  · simp only [if_pos h, Expression.eval]; ring
  · simp only [if_neg h, add_zero]

private lemma seven_val : ((7 : F circomPrime)).val = 7 := by decide

/-- The additive constant carried in cell `0`. -/
private lemma curveTarget_const_val (env : Environment (F circomPrime))
    (isInf : Expression (F circomPrime)) (hb : IsBool (Expression.eval env isInf)) :
    (((1 : F circomPrime) - Expression.eval env isInf) * (7 : F circomPrime)).val
      = if Expression.eval env isInf = 1 then 0 else 7 := by
  rcases hb with h | h
  · rw [h, if_neg (by simp), sub_zero, one_mul]
    exact seven_val
  · rw [h, if_pos rfl, sub_self, zero_mul, ZMod.val_zero]

private lemma curveTarget_cell_lt (env : Environment (F circomPrime))
    (Pc : Var (fields (2 * numLimbs - 1)) (F circomPrime))
    (isInf : Expression (F circomPrime)) (hb : IsBool (Expression.eval env isInf))
    (hPc : ∀ k : Fin (2 * numLimbs - 1),
      (Expression.eval env Pc[k.val]).val < numLimbs * (2 ^ limbBits * 2 ^ limbBits))
    (k : Fin (2 * numLimbs - 1)) :
    (Expression.eval env ((curveTarget Pc isInf)[k.val]'k.isLt)).val < 5 * 2 ^ 128 := by
  rw [show Expression.eval env ((curveTarget Pc isInf)[k.val]'k.isLt)
      = (Vector.map (Expression.eval env) (curveTarget Pc isInf))[k.val]'k.isLt from
      by rw [Vector.getElem_map], eval_curveTarget_cell]
  have hk := hPc k
  simp only [numLimbs, limbBits] at hk
  by_cases h : k.val = 0
  · rw [if_pos h]
    have hle := ZMod.val_add_le (Expression.eval env Pc[k.val])
      (((1 : F circomPrime) - Expression.eval env isInf) * (7 : F circomPrime))
    have hc := curveTarget_const_val env isInf hb
    have hc7 : (((1 : F circomPrime) - Expression.eval env isInf) * (7 : F circomPrime)).val ≤ 7 := by
      rw [hc]; split <;> norm_num
    have h2 : (4 : ℕ) * (2 ^ 64 * 2 ^ 64) = 4 * 2 ^ 128 := by norm_num
    omega
  · rw [if_neg h, add_zero]
    have h2 : (4 : ℕ) * (2 ^ 64 * 2 ^ 64) = 4 * 2 ^ 128 := by norm_num
    omega

private lemma curveTarget_poly (env : Environment (F circomPrime))
    (Pc : Var (fields (2 * numLimbs - 1)) (F circomPrime))
    (isInf : Expression (F circomPrime)) (hb : IsBool (Expression.eval env isInf))
    (hPc : ∀ k : Fin (2 * numLimbs - 1),
      (Expression.eval env Pc[k.val]).val < numLimbs * (2 ^ limbBits * 2 ^ limbBits)) :
    polyValue limbBits (Vector.map (Expression.eval env) (curveTarget Pc isInf))
      = polyValue limbBits (Vector.map (Expression.eval env) Pc)
        + (if Expression.eval env isInf = 1 then 0 else 7) := by
  have hc := curveTarget_const_val env isInf hb
  have hterm : ∀ i : Fin (2 * numLimbs - 1),
      ((Vector.map (Expression.eval env) (curveTarget Pc isInf))[i.val]).val
          * 2 ^ (limbBits * i.val)
        = ((Vector.map (Expression.eval env) Pc)[i.val]).val * 2 ^ (limbBits * i.val)
          + (if i.val = 0 then (if Expression.eval env isInf = 1 then 0 else 7) else 0) := by
    intro i
    rw [eval_curveTarget_cell, Vector.getElem_map]
    by_cases h : i.val = 0
    · rw [if_pos h, if_pos h]
      have hi := hPc i
      simp only [numLimbs, limbBits] at hi
      have hc7 : (((1 : F circomPrime) - Expression.eval env isInf) * (7 : F circomPrime)).val ≤ 7 := by
        rw [hc]; split <;> norm_num
      have hlt : (Expression.eval env Pc[i.val]).val
          + (((1 : F circomPrime) - Expression.eval env isInf) * (7 : F circomPrime)).val
          < circomPrime := by
        have : (4 : ℕ) * (2 ^ 64 * 2 ^ 64) + 7 < circomPrime := by decide
        omega
      have hpow : (2 : ℕ) ^ (limbBits * i.val) = 1 := by rw [h, Nat.mul_zero, pow_zero]
      rw [ZMod.val_add_of_lt hlt, hc, hpow, Nat.mul_one, Nat.mul_one]
    · rw [if_neg h, if_neg h, add_zero, add_zero]
  have hsingle : (∑ i : Fin (2 * numLimbs - 1),
        (if i.val = 0 then (if Expression.eval env isInf = 1 then 0 else 7) else 0))
      = (if Expression.eval env isInf = 1 then 0 else 7) := by
    rw [show (2 * numLimbs - 1) = 7 from rfl]
    simp
  unfold polyValue
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hterm i), Finset.sum_add_distrib,
    hsingle]

/-- Stability of the certificate target under two environments agreeing on the
convolution cells and the flag. -/
private lemma curveTarget_stable {e e' : ProverEnvironment (F circomPrime)}
    (Pc : Var (fields (2 * numLimbs - 1)) (F circomPrime))
    (isInf : Expression (F circomPrime))
    (hPc : Vector.map (Expression.eval e.toEnvironment) Pc
      = Vector.map (Expression.eval e'.toEnvironment) Pc)
    (hi : Expression.eval e.toEnvironment isInf = Expression.eval e'.toEnvironment isInf) :
    Vector.map (Expression.eval e.toEnvironment) (curveTarget Pc isInf)
      = Vector.map (Expression.eval e'.toEnvironment) (curveTarget Pc isInf) := by
  apply Vector.ext
  intro i hi'
  rw [eval_curveTarget_cell e.toEnvironment Pc isInf ⟨i, hi'⟩,
    eval_curveTarget_cell e'.toEnvironment Pc isInf ⟨i, hi'⟩]
  have hcell := congrArg
    (fun v : Vector (F circomPrime) (2 * numLimbs - 1) => v[i]'hi') hPc
  simp only [Vector.getElem_map] at hcell
  rw [hcell, hi]

private lemma cast_of_sum_mod {av bv c yv : ℕ} (h : (av * bv + c) % P256 = yv * yv % P256) :
    (av : Specs.Secp256k1.Fp) * (bv : Specs.Secp256k1.Fp) + (c : Specs.Secp256k1.Fp)
      = (yv : Specs.Secp256k1.Fp) * (yv : Specs.Secp256k1.Fp) := by
  have hcast : ((av * bv + c : ℕ) : Specs.Secp256k1.Fp)
      = ((yv * yv : ℕ) : Specs.Secp256k1.Fp) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mpr h
  push_cast at hcast
  linear_combination hcast

private lemma sum_mod_of_cast {av bv c yv : ℕ}
    (h : (av : Specs.Secp256k1.Fp) * (bv : Specs.Secp256k1.Fp) + (c : Specs.Secp256k1.Fp)
      = (yv : Specs.Secp256k1.Fp) * (yv : Specs.Secp256k1.Fp)) :
    (av * bv + c) % P256 = yv * yv % P256 := by
  refine (ZMod.natCast_eq_natCast_iff _ _ _).mp ?_
  push_cast
  linear_combination h

private lemma cast_of_target_mod {rv av bv : ℕ} (h : rv % P256 = av * bv % P256) :
    (rv : Specs.Secp256k1.Fp)
      = (av : Specs.Secp256k1.Fp) * (bv : Specs.Secp256k1.Fp) := by
  have hcast : ((rv : ℕ) : Specs.Secp256k1.Fp) = ((av * bv : ℕ) : Specs.Secp256k1.Fp) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mpr h
  push_cast at hcast
  linear_combination hcast

/-- The converse direction, used for completeness. -/
private lemma target_mod_of_cast {rv av bv : ℕ}
    (h : (rv : Specs.Secp256k1.Fp)
      = (av : Specs.Secp256k1.Fp) * (bv : Specs.Secp256k1.Fp)) :
    rv % P256 = av * bv % P256 := by
  refine (ZMod.natCast_eq_natCast_iff _ _ _).mp ?_
  push_cast
  linear_combination h

private lemma limbs_eq_zero_of_sum_eq_zero {x : Emu (F circomPrime)}
    (hx : Fe.Valid x) (hsum : x[0] + x[1] + x[2] + x[3] = 0) :
    x = emuOfNat 0 := by
  have h0 := hx.1 (0 : Fin numLimbs)
  have h1 := hx.1 (1 : Fin numLimbs)
  have h2 := hx.1 (2 : Fin numLimbs)
  have h3 := hx.1 (3 : Fin numLimbs)
  have hsum_lt : x[0].val + x[1].val + x[2].val + x[3].val < 2 ^ 66 := by
    norm_num [limbBits] at h0 h1 h2 h3 ⊢
    omega
  have hp : 2 ^ 66 < circomPrime := by decide
  have hlt : x[0].val + x[1].val + x[2].val + x[3].val < circomPrime :=
    hsum_lt.trans hp
  have hcast :
      ((x[0].val + x[1].val + x[2].val + x[3].val : ℕ) : F circomPrime) = 0 := by
    calc
      ((x[0].val + x[1].val + x[2].val + x[3].val : ℕ) : F circomPrime) =
          x[0] + x[1] + x[2] + x[3] := by
            push_cast
            rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val,
              ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
      _ = 0 := hsum
  have hsumNat : x[0].val + x[1].val + x[2].val + x[3].val = 0 := by
    have hdvd := (ZMod.natCast_eq_zero_iff _ _).mp hcast
    exact Nat.eq_zero_of_dvd_of_lt hdvd hlt
  have hx0 : x[0] = 0 := (ZMod.val_eq_zero _).mp (by omega)
  have hx1 : x[1] = 0 := (ZMod.val_eq_zero _).mp (by omega)
  have hx2 : x[2] = 0 := (ZMod.val_eq_zero _).mp (by omega)
  have hx3 : x[3] = 0 := (ZMod.val_eq_zero _).mp (by omega)
  apply Vector.ext
  intro i hi
  interval_cases i <;>
    simp [hx0, hx1, hx2, hx3, emuOfNat, Vector.getElem_ofFn, limbOfNat]

private lemma two_limbs_eq_zero_of_sum_eq_zero {x y : Emu (F circomPrime)}
    (hx : Fe.Valid x) (hy : Fe.Valid y)
    (hsum : x[0] + x[1] + x[2] + x[3] + y[0] + y[1] + y[2] + y[3] = 0) :
    x = emuOfNat 0 ∧ y = emuOfNat 0 := by
  have hx0 := hx.1 (0 : Fin numLimbs)
  have hx1 := hx.1 (1 : Fin numLimbs)
  have hx2 := hx.1 (2 : Fin numLimbs)
  have hx3 := hx.1 (3 : Fin numLimbs)
  have hy0 := hy.1 (0 : Fin numLimbs)
  have hy1 := hy.1 (1 : Fin numLimbs)
  have hy2 := hy.1 (2 : Fin numLimbs)
  have hy3 := hy.1 (3 : Fin numLimbs)
  let s : ℕ := x[0].val + x[1].val + x[2].val + x[3].val +
    y[0].val + y[1].val + y[2].val + y[3].val
  have hs_lt : s < 2 ^ 67 := by
    dsimp [s]
    norm_num [limbBits] at hx0 hx1 hx2 hx3 hy0 hy1 hy2 hy3 ⊢
    omega
  have hp : 2 ^ 67 < circomPrime := by decide
  have hlt : s < circomPrime := hs_lt.trans hp
  have hcast : (s : F circomPrime) = 0 := by
    dsimp [s]
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val,
      ZMod.natCast_zmod_val, ZMod.natCast_zmod_val,
      ZMod.natCast_zmod_val, ZMod.natCast_zmod_val,
      ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    exact hsum
  have hs0 : s = 0 := by
    have hdvd := (ZMod.natCast_eq_zero_iff _ _).mp hcast
    exact Nat.eq_zero_of_dvd_of_lt hdvd hlt
  have hxs : x[0] + x[1] + x[2] + x[3] = 0 := by
    have : x[0].val + x[1].val + x[2].val + x[3].val = 0 := by
      dsimp [s] at hs0
      omega
    rw [← ZMod.natCast_zmod_val x[0], ← ZMod.natCast_zmod_val x[1],
      ← ZMod.natCast_zmod_val x[2], ← ZMod.natCast_zmod_val x[3],
      ← Nat.cast_add, ← Nat.cast_add, ← Nat.cast_add, this]
    rfl
  have hys : y[0] + y[1] + y[2] + y[3] = 0 := by
    have : y[0].val + y[1].val + y[2].val + y[3].val = 0 := by
      dsimp [s] at hs0
      omega
    rw [← ZMod.natCast_zmod_val y[0], ← ZMod.natCast_zmod_val y[1],
      ← ZMod.natCast_zmod_val y[2], ← ZMod.natCast_zmod_val y[3],
      ← Nat.cast_add, ← Nat.cast_add, ← Nat.cast_add, this]
    rfl
  exact ⟨limbs_eq_zero_of_sum_eq_zero hx hxs,
    limbs_eq_zero_of_sum_eq_zero hy hys⟩

attribute [local irreducible] MulModFold32T.qInv MulModFold32T.lhsPolyInv
  MulModFold32T.targetPolyInv GroupedEqXV.circuitNoTop GroupedEqXV.mainNoTop

theorem soundness :
    GeneralFormalCircuit.Soundness (F circomPrime) main Assumptions OutputSpec := by
  circuit_proof_start [ValidPBytes.circuit, ValidPBytes.main,
    ValidPBytes.Assumptions, ValidPBytes.Spec,
    MulMod.circuit, MulMod.Assumptions, MulMod.Spec,
    MulModSqN32.circuit, MulModSqN32.Assumptions, MulModSqN32.Spec,
    MulModFoldT.circuitInv, MulModFoldT.Assumptions, MulModFoldT.Spec, secpParams]
  obtain ⟨hflag, hxvalid, hyvalid, hx2, hABops, hfold, hbranch⟩ := h_holds
  have hbool : IsBool input_isInf := by
    rw [IsBool.iff_mul_sub_one]
    simpa [sub_eq_add_neg] using hflag
  have hxv : Fe.Valid input_x := hxvalid.1
  have hyv : Fe.Valid input_y := hyvalid.1
  have hinfEval : Expression.eval env input_var_isInf = input_isInf := h_input.2.2
  have hmb : IsBool (Expression.eval env input_var_isInf) := by rw [hinfEval]; exact hbool
  have hz0 : decodeFe (Vector.map (Expression.eval env) zeroConst) = 0 := by
    rw [DivOrZero.eval_zeroConst, decodeFe, CompleteAdd.value_emuOfNat (by positivity),
      Nat.cast_zero]
  have hx32 : BigInt.Normalized 32
      (Vector.map (Expression.eval env) (Bytes32.ofBytes _)) :=
    Bytes32.normalized_map_ofBytes hxvalid.2
  obtain ⟨hx2v, hx2d⟩ := hx2 hx32
  rw [Bytes32.decodeFe_map_ofBytes hxvalid.2] at hx2d
  have hxeval : Vector.map (Expression.eval env) input_var_x = input_x := h_input.1
  have hyeval : Vector.map (Expression.eval env) input_var_y = input_y := h_input.2.1
  obtain ⟨hPc_cell, hPc_poly⟩ :=
    Pab_facts env
      (Vector.mapRange numLimbs fun i => var (F := F circomPrime) { index := i₀ + 260 + 260 + i })
      input_var_x (i₀ + 260 + 260 + (numLimbs + (numLimbs * (limbBits - 1) + 92))) hABops hx2v
      (by rw [hxeval]; exact hxv.1)
  have hyl : ∀ i : Fin numLimbs, ZMod.val (input_y[i.val]'i.isLt) < 2 ^ 64 := by
    intro i
    simpa [limbBits] using hyv.1 i
  have hcert := hfold ⟨hyl, hyl,
    fun k => curveTarget_cell_lt env _ input_var_isInf hmb hPc_cell k,
    curveTarget_cell_lt env _ input_var_isInf hmb hPc_cell ⟨5, by decide⟩⟩
  rw [curveTarget_poly env _ input_var_isInf hmb hPc_cell, hPc_poly, hxeval] at hcert
  have hFp := cast_of_sum_mod hcert
  have hcurve : input_isInf = 0 →
      Specs.ShortWeierstrass.OnCurve Specs.Secp256k1.curve
        { x := decodeFe input_x, y := decodeFe input_y } := by
    intro hinf
    rw [CompleteAdd.onCurve_iff]
    rw [hinfEval, hinf, if_neg (by simpa using (zero_ne_one : (0 : F circomPrime) ≠ 1))] at hFp
    simp only [decodeFe] at hx2d hFp ⊢
    push_cast at hFp
    rw [hx2d] at hFp
    linear_combination -hFp
  have hpoint : Spec
      ({ x := input_x, y := input_y, isInf := input_isInf } :
        FlaggedPoint (F circomPrime)) := by
    refine ⟨⟨hbool, hxv, hyv, hcurve⟩, ?_⟩
    intro hinf
    change input_isInf = 1 at hinf
    apply two_limbs_eq_zero_of_sum_eq_zero hxv hyv
    have hx0 : Expression.eval env input_var_x[0] = input_x[0] := by
      simpa only [Vector.getElem_map] using congrArg (fun v : Emu (F circomPrime) => v[0]) h_input.1
    have hx1 : Expression.eval env input_var_x[1] = input_x[1] := by
      simpa only [Vector.getElem_map] using congrArg (fun v : Emu (F circomPrime) => v[1]) h_input.1
    have hx2' : Expression.eval env input_var_x[2] = input_x[2] := by
      simpa only [Vector.getElem_map] using congrArg (fun v : Emu (F circomPrime) => v[2]) h_input.1
    have hx3' : Expression.eval env input_var_x[3] = input_x[3] := by
      simpa only [Vector.getElem_map] using congrArg (fun v : Emu (F circomPrime) => v[3]) h_input.1
    have hy0 : Expression.eval env input_var_y[0] = input_y[0] := by
      simpa only [Vector.getElem_map] using congrArg (fun v : Emu (F circomPrime) => v[0]) h_input.2.1
    have hy1 : Expression.eval env input_var_y[1] = input_y[1] := by
      simpa only [Vector.getElem_map] using congrArg (fun v : Emu (F circomPrime) => v[1]) h_input.2.1
    have hy2 : Expression.eval env input_var_y[2] = input_y[2] := by
      simpa only [Vector.getElem_map] using congrArg (fun v : Emu (F circomPrime) => v[2]) h_input.2.1
    have hy3 : Expression.eval env input_var_y[3] = input_y[3] := by
      simpa only [Vector.getElem_map] using congrArg (fun v : Emu (F circomPrime) => v[3]) h_input.2.1
    rw [← hx0, ← hx1, ← hx2', ← hx3', ← hy0, ← hy1, ← hy2, ← hy3]
    rw [hinf, one_mul] at hbranch
    linear_combination hbranch
  refine ⟨⟨hpoint, ?_, ?_⟩, MulMod.interpolatedMul_requirements _ _ _ _⟩
  · simpa only [circuit_norm] using hxvalid.2
  · simpa only [circuit_norm] using hyvalid.2

set_option maxHeartbeats 1000000 in
theorem completeness :
    GeneralFormalCircuit.Completeness (F circomPrime) main
      ProverAssumptions ProverSpec := by
  circuit_proof_start [ValidPBytes.circuit, ValidPBytes.main,
    ValidPBytes.ProverAssumptions, ValidPBytes.ProverSpec,
    MulMod.circuit, MulMod.Assumptions, MulMod.Spec,
    MulModSqN32.circuit, MulModSqN32.Assumptions, MulModSqN32.Spec,
    MulModFoldT.circuitInv, MulModFoldT.Assumptions, MulModFoldT.Spec, secpParams]
  obtain ⟨hxb, hyb, hx2, hu⟩ := h_env
  obtain ⟨⟨hbool0, hxv, hyv, hcurve⟩, hcanon0⟩ := h_assumptions
  have hbool : IsBool input_isInf := hbool0
  have hcanon : input_isInf = 1 → input_x = emuOfNat 0 ∧ input_y = emuOfNat 0 := hcanon0
  have hinfEval : Expression.eval env.toEnvironment input_var_isInf = input_isInf := h_input.2.2
  have hmb : IsBool (Expression.eval env.toEnvironment input_var_isInf) := by
    rw [hinfEval]; exact hbool
  have hmv := sevenMask_valid env.toEnvironment input_var_isInf hmb
  have hzv := CompleteAdd.fe_valid_eval_zeroConst env.toEnvironment
  have hz0 : decodeFe (Vector.map (Expression.eval env.toEnvironment) zeroConst) = 0 := by
    rw [DivOrZero.eval_zeroConst, decodeFe, CompleteAdd.value_emuOfNat (by positivity),
      Nat.cast_zero]
  have hx32 : BigInt.Normalized 32
      (Vector.map (Expression.eval env.toEnvironment) (Bytes32.ofBytes _)) :=
    Bytes32.normalized_map_ofBytes (hxb hxv).2
  obtain ⟨hx2v, hx2d⟩ := hx2 hx32
  rw [Bytes32.decodeFe_map_ofBytes (hxb hxv).2] at hx2d
  have hxeval : Vector.map (Expression.eval env.toEnvironment) input_var_x = input_x := h_input.1
  have hpvAB := MulMod.interpolatedMul_usesLocalWitnesses
    (i₀ + 260 + 260 + (numLimbs + (numLimbs * (limbBits - 1) + 92))) (i₀ + 260 + 260 + (numLimbs + (numLimbs * (limbBits - 1) + 92)))
    (Vector.mapRange numLimbs fun i => var (F := F circomPrime) { index := i₀ + 260 + 260 + i })
    input_var_x env rfl hu
  have hbridge := MulMod.interpolatedMul_eval_bridge_uses env.toEnvironment
    (i₀ + 260 + 260 + (numLimbs + (numLimbs * (limbBits - 1) + 92)))
    (Vector.mapRange numLimbs fun i => var (F := F circomPrime) { index := i₀ + 260 + 260 + i })
    input_var_x hpvAB
  obtain ⟨hPc_cell, hPc_poly⟩ :=
    Pab_facts_of_bridge env.toEnvironment
      (Vector.mapRange numLimbs fun i => var (F := F circomPrime) { index := i₀ + 260 + 260 + i })
      input_var_x (i₀ + 260 + 260 + (numLimbs + (numLimbs * (limbBits - 1) + 92))) hbridge hx2v
      (by rw [hxeval]; exact hxv.1)
  have hyl : ∀ i : Fin numLimbs, ZMod.val (input_y[i.val]'i.isLt) < 2 ^ 64 := by
    intro i
    simpa [limbBits] using hyv.1 i
  have hcertSpec : polyValue limbBits (Vector.map (Expression.eval env.toEnvironment)
        (curveTarget (MulMod.interpolatedMul
          (Vector.mapRange numLimbs fun i =>
            var (F := F circomPrime) { index := i₀ + 260 + 260 + i })
          input_var_x (i₀ + 260 + 260 + (numLimbs + (numLimbs * (limbBits - 1) + 92)))).1 input_var_isInf)) % P256
      = BigInt.value 64 input_y * BigInt.value 64 input_y % P256 := by
    rw [curveTarget_poly env.toEnvironment _ input_var_isInf hmb hPc_cell, hPc_poly, hxeval]
    apply sum_mod_of_cast
    rcases hbool with h0 | h1
    · rw [hinfEval, h0, if_neg (by simpa using (zero_ne_one : (0 : F circomPrime) ≠ 1))]
      have hc := hcurve h0
      rw [CompleteAdd.onCurve_iff] at hc
      simp only [decodeFe] at hx2d hc
      push_cast
      simp only [limbBits] at hx2d hc ⊢
      rw [hx2d]
      linear_combination -hc
    · obtain ⟨hcx, hcy⟩ := hcanon h1
      have hdx : decodeFe input_x = 0 := by
        rw [hcx, decodeFe, CompleteAdd.value_emuOfNat (by positivity), Nat.cast_zero]
      have hdy : decodeFe input_y = 0 := by
        rw [hcy, decodeFe, CompleteAdd.value_emuOfNat (by positivity), Nat.cast_zero]
      rw [hinfEval, h1, if_pos rfl]
      simp only [decodeFe] at hx2d hdx hdy
      push_cast
      simp only [limbBits] at hx2d hdx hdy ⊢
      rw [hdx, hdy]
      ring
  refine ⟨?_, hxv, hyv, hx32,
    MulMod.interpolatedMul_completeness (i₀ + 260 + 260 + (numLimbs + (numLimbs * (limbBits - 1) + 92))) _ _ env hpvAB,
    ⟨⟨hyl, hyl, (fun k =>
      curveTarget_cell_lt env.toEnvironment _ input_var_isInf hmb hPc_cell k),
      curveTarget_cell_lt env.toEnvironment _ input_var_isInf hmb hPc_cell ⟨5, by decide⟩⟩,
      hcertSpec⟩, ?_⟩
  · rcases hbool with h | h <;> rw [h] <;> ring
  · rcases hbool with h | h
    · rw [h, zero_mul]
    · obtain ⟨hcx, hcy⟩ := hcanon h
      have hx0 : Expression.eval env.toEnvironment input_var_x[0] = input_x[0] := by
        simpa only [Vector.getElem_map] using
          congrArg (fun v : Emu (F circomPrime) => v[0]) h_input.1
      have hx1 : Expression.eval env.toEnvironment input_var_x[1] = input_x[1] := by
        simpa only [Vector.getElem_map] using
          congrArg (fun v : Emu (F circomPrime) => v[1]) h_input.1
      have hx2' : Expression.eval env.toEnvironment input_var_x[2] = input_x[2] := by
        simpa only [Vector.getElem_map] using
          congrArg (fun v : Emu (F circomPrime) => v[2]) h_input.1
      have hx3' : Expression.eval env.toEnvironment input_var_x[3] = input_x[3] := by
        simpa only [Vector.getElem_map] using
          congrArg (fun v : Emu (F circomPrime) => v[3]) h_input.1
      have hy0 : Expression.eval env.toEnvironment input_var_y[0] = input_y[0] := by
        simpa only [Vector.getElem_map] using
          congrArg (fun v : Emu (F circomPrime) => v[0]) h_input.2.1
      have hy1 : Expression.eval env.toEnvironment input_var_y[1] = input_y[1] := by
        simpa only [Vector.getElem_map] using
          congrArg (fun v : Emu (F circomPrime) => v[1]) h_input.2.1
      have hy2 : Expression.eval env.toEnvironment input_var_y[2] = input_y[2] := by
        simpa only [Vector.getElem_map] using
          congrArg (fun v : Emu (F circomPrime) => v[2]) h_input.2.1
      have hy3 : Expression.eval env.toEnvironment input_var_y[3] = input_y[3] := by
        simpa only [Vector.getElem_map] using
          congrArg (fun v : Emu (F circomPrime) => v[3]) h_input.2.1
      rw [h, one_mul, hx0, hx1, hx2', hx3', hy0, hy1, hy2, hy3, hcx, hcy]
      norm_num [emuOfNat, Vector.getElem_ofFn, numLimbs, limbBits, limbOfNat]

def circuit : GeneralFormalCircuit (F circomPrime) FlaggedPoint Outputs where
  main := main
  elaborated := elaborated
  Assumptions := Assumptions
  Spec := OutputSpec
  ProverAssumptions := ProverAssumptions
  ProverSpec := ProverSpec
  soundness := soundness
  completeness := completeness

private theorem generalSubcircuit_structuralComputableWitnesses_iff
    {Parent Input Output : TypeMap}
    [CircuitType Parent] [ProvableType Input] [ProvableType Output]
    (c : GeneralFormalCircuit (F circomPrime) Input Output)
    (parentInput : Var Parent (F circomPrime))
    (input : Var Input (F circomPrime)) (n : ℕ)
    (env env' : ProverEnvironment (F circomPrime)) :
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.StructuralComputableWitnesses
        parentInput env env' n ((subcircuitWithAssertion c input).operations n) ↔
      Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.FlatOperation.StructuralComputableWitnesses
        parentInput env env' n ((c.toSubcircuit n input).ops.toFlat) := by
  unfold subcircuitWithAssertion
  simp [Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.StructuralComputableWitnesses]

theorem computableWitnesses : circuit.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  obtain ⟨x, y, isInf⟩ := input
  have haz : ∀ (e : Expression (F circomPrime)) o,
      (assertZero e).localLength o = 0 := fun _ _ => rfl
  have hvp : ∀ (u : Var Emu (F circomPrime)) o,
      (ValidPBytes.circuit u).localLength o = 260 := fun _ _ => rfl
  have hms2 : ∀ (u : Var MulModSqN32.Inputs (F circomPrime)) o,
      (subcircuit MulModSqN32.circuit u).localLength o = 348 := fun _ _ => rfl
  have hnl : numLimbs = 4 := rfl
  let xb : Var (fields coordBytes) (F circomPrime) := ValidPBytes.circuit.output x offset
  let o0 := offset + 520
  let x2 : Var Emu (F circomPrime) :=
    (subcircuit MulModSqN32.circuit
      { a := Bytes32.ofBytes xb, b := Bytes32.ofBytes xb }).output o0
  let o1 := o0 + 348
  let Pc : Var (fields (2 * numLimbs - 1)) (F circomPrime) :=
    (MulMod.interpolatedMul x2 x).output o1
  let o2 := o1 + (2 * numLimbs - 1)
  unfold main
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.assertZero_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.pure_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_structuralComputableWitnesses_iff,
    generalSubcircuit_structuralComputableWitnesses_iff,
    haz, hvp, hms2, and_true]
  refine ⟨trivial, ?_, ?_, ?_, ?_, ?_⟩
  · exact Challenge.Utils.ComputableWitnessLemmas.GeneralFormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := FlaggedPoint) ValidPBytes.circuit
      ({ x := x, y := y, isInf := isInf } : Var FlaggedPoint (F circomPrime))
      x _ (by
        intro k e e' _ _ h
        simp only [circuit_norm, FlaggedPoint.mk.injEq] at h ⊢
        exact h.1) ValidPBytes.computableWitnesses env env'
  · exact Challenge.Utils.ComputableWitnessLemmas.GeneralFormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := FlaggedPoint) ValidPBytes.circuit
      ({ x := x, y := y, isInf := isInf } : Var FlaggedPoint (F circomPrime))
      y _ (by
        intro k e e' _ _ h
        simp only [circuit_norm, FlaggedPoint.mk.injEq] at h ⊢
        exact h.2.1) ValidPBytes.computableWitnesses env env'
  · refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := FlaggedPoint) MulModSqN32.circuit
      ({ x := x, y := y, isInf := isInf } : Var FlaggedPoint (F circomPrime))
      { a := Bytes32.ofBytes xb, b := Bytes32.ofBytes xb } _ ?_
      MulModSqN32.computableWitnesses env env'
    intro k e e' hle hag h
    have hx : Vector.map (Expression.eval e.toEnvironment) x
        = Vector.map (Expression.eval e'.toEnvironment) x := by
      simpa only [circuit_norm, FlaggedPoint.mk.injEq] using
        congrArg (fun v : FlaggedPoint (F circomPrime) => v.x) h
    have hb : Vector.map (Expression.eval e.toEnvironment) (Bytes32.ofBytes xb)
        = Vector.map (Expression.eval e'.toEnvironment) (Bytes32.ofBytes xb) :=
      Bytes32.ofBytes_map_eval_eq
        (ValidPBytes.output_map_eval_eq x offset hag (by dsimp [o0] at hle ⊢; omega) hx)
    simp only [circuit_norm]
    rw [MulModSqN32.Inputs.mk.injEq]
    exact ⟨hb, hb⟩
  · exact MulMod.interpolatedMul_structuralComputableWitnesses (Parent := FlaggedPoint)
      ({ x := x, y := y, isInf := isInf } : Var FlaggedPoint (F circomPrime))
      x2 x o1
      (by
        intro k e e' hle hag h
        refine ⟨?_, ?_⟩
        · exact MulModSqN32.eval_output_of_agreesBelow
            { a := Bytes32.ofBytes xb, b := Bytes32.ofBytes xb }
            (offset := o0) (k := k) hag (by dsimp [o0, o1] at hle ⊢; omega)
        · simpa [circuit_norm] using
            congrArg (fun v : FlaggedPoint (F circomPrime) => v.x) h)
      env env'
  · refine Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
      (Parent := FlaggedPoint)
      (MulModFoldT.circuitInv (2 ^ 64) (2 ^ 64) (5 * 2 ^ 128) (5 * 2 ^ 128)
        (by decide) (by decide) (by decide) (by decide))
      ({ x := x, y := y, isInf := isInf } : Var FlaggedPoint (F circomPrime))
      { a := y, b := y, target := curveTarget Pc isInf } _ ?_
      (MulModFoldT.computableWitnessesInv (2 ^ 64) (2 ^ 64) (5 * 2 ^ 128) (5 * 2 ^ 128)
        (by decide) (by decide) (by decide) (by decide)) env env'
    intro k e e' hle hag h
    have hy : Vector.map (Expression.eval e.toEnvironment) y
        = Vector.map (Expression.eval e'.toEnvironment) y := by
      simpa only [circuit_norm, FlaggedPoint.mk.injEq] using
        congrArg (fun v : FlaggedPoint (F circomPrime) => v.y) h
    have hi : Expression.eval e.toEnvironment isInf = Expression.eval e'.toEnvironment isInf := by
      simpa only [circuit_norm, FlaggedPoint.mk.injEq] using
        congrArg (fun v : FlaggedPoint (F circomPrime) => v.isInf) h
    have hPc : Vector.map (Expression.eval e.toEnvironment) Pc
        = Vector.map (Expression.eval e'.toEnvironment) Pc :=
      MulMod.interpolatedMul_output_stable o1 x2 x hag
        (by
          simp only [MulMod.interpolatedMul_localLength] at hle
          dsimp [o0, o1, o2] at hle ⊢
          omega)
    simp only [circuit_norm]
    rw [MulModFoldT.Inputs.mk.injEq]
    exact ⟨hy, hy, curveTarget_stable Pc isInf hPc hi⟩

theorem computableWitness : ∀ n input,
    ProverEnvironment.OnlyAccessedBelow n
      (fun env : ProverEnvironment (F circomPrime) => eval env input) →
    Circuit.ComputableWitnesses (main input) n := by
  exact Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnesses_implies
    (circuit := circuit.base) computableWitnesses

end PointValid
end Solution.Secp256k1ScalarMul
