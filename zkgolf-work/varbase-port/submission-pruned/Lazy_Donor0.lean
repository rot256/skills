import Mathlib.Data.Nat.Size
import Clean.Circuit.Basic
import Clean.Circuit.Loops
import Clean.Gadgets.Bits
import Clean.Gadgets.Equality
import Clean.Utils.Tactics.ProvableStructDeriving
import Challenge.Utils.ComputableWitnessLemmas
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Basic
import Challenge.Specs.Secp256k1
import Challenge.Instances.Secp256k1ScalarMulFixedBase.Interface
import Challenge.Instances.Secp256k1ScalarMul.Interface
import Clean.Gadgets.IsZeroField
import Challenge.Utils.CostR1CS
import Clean.Circuit
import Clean.Utils.Bits
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Clean.Gadgets.Boolean
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Intervals

-- Adapted donor module: Theorems
section DonorFile0_0

namespace Solution.Secp256k1ScalarMulFixedBase.Limbs

def fromLimbs (limbBits : ℕ) (limbs : List ℕ) : ℕ :=
  limbs.foldr (fun limb acc => limb + acc * 2 ^ limbBits) 0

end Solution.Secp256k1ScalarMulFixedBase.Limbs

namespace Solution.Secp256k1ScalarMulFixedBase
open Solution.Secp256k1ScalarMulFixedBase.Limbs

section ComputableWitnessHelpers
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2)]

omit [Fact (p > 2)] in
theorem assertBoolComputableWitnesses :
    (assertBool (p := p)).ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition input env env')
    (((assertBool (p := p)).main input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold assertBool
  simp only [Challenge.Utils.ComputableWitnessLemmas.Circuit.assertZero_structuralComputableWitnesses_iff]

end ComputableWitnessHelpers

@[reducible] def BigInt (m : ℕ) : TypeMap := fields m

namespace BigInt

section
variable {p : ℕ} [Fact p.Prime] {m : ℕ}

def value (B : ℕ) (x : BigInt m (F p)) : ℕ :=
  Solution.Secp256k1ScalarMulFixedBase.Limbs.fromLimbs B (x.toList.map ZMod.val)

def Normalized (B : ℕ) (x : BigInt m (F p)) : Prop := ∀ i : Fin m, (x[i]).val < 2 ^ B

end

end BigInt

section
variable {p : ℕ} [Fact p.Prime]
variable {m : ℕ}

theorem fromLimbs_eq_sum {B : ℕ} (l : List ℕ) :
    Solution.Secp256k1ScalarMulFixedBase.Limbs.fromLimbs B l = ∑ i : Fin l.length, l[i] * 2 ^ (B * i.val) := by
  induction l with
  | nil => simp [Solution.Secp256k1ScalarMulFixedBase.Limbs.fromLimbs]
  | cons a t ih =>
    have hrhs : (∑ i : Fin (a :: t).length, (a :: t)[i] * 2 ^ (B * i.val))
        = a + (∑ i : Fin t.length, t[i] * 2 ^ (B * i.val)) * 2 ^ B := by
      show (∑ i : Fin (t.length + 1), (a :: t)[i] * 2 ^ (B * i.val)) = _
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, Nat.mul_zero, pow_zero, Nat.mul_one,
        Fin.val_succ]
      rw [Finset.sum_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      have hidx : (a :: t)[i.succ] = t[i] := by
        simp [List.getElem_cons_succ]
      rw [hidx, Nat.mul_add, Nat.mul_one, pow_add]
      ring
    rw [show Solution.Secp256k1ScalarMulFixedBase.Limbs.fromLimbs B (a :: t)
        = a + Solution.Secp256k1ScalarMulFixedBase.Limbs.fromLimbs B t * 2 ^ B from rfl, ih]
    exact hrhs.symm

omit [Fact (Nat.Prime p)] in

theorem BigInt.value_eq_sum {B : ℕ} (x : BigInt m (F p)) :
    BigInt.value B x = ∑ k : Fin m, (x[k]).val * 2 ^ (B * k.val) := by
  rw [BigInt.value, fromLimbs_eq_sum]
  have hlen : (x.toList.map ZMod.val).length = m := by
    simp [List.length_map, Vector.length_toList]

  rw [← Fin.sum_congr' (fun k : Fin m => (x[k]).val * 2 ^ (B * k.val)) hlen]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Fin.val_cast]
  congr 1
  rw [Fin.getElem_fin, List.getElem_map]
  rfl

theorem limb_decomp_mod (B : ℕ) : ∀ (m N : ℕ),
    (∑ i ∈ Finset.range m, (N / 2 ^ (B * i) % 2 ^ B) * 2 ^ (B * i)) = N % 2 ^ (B * m) := by
  intro m
  induction m with
  | zero => intro N; simp [Nat.mod_one]
  | succ n ih =>
    intro N
    rw [Finset.sum_range_succ']
    simp only [Nat.mul_zero, pow_zero, Nat.mul_one, Nat.div_one]
    have htail : (∑ i ∈ Finset.range n, (N / 2 ^ (B * (i + 1)) % 2 ^ B) * 2 ^ (B * (i + 1)))
        = 2 ^ B * ((N / 2 ^ B) % 2 ^ (B * n)) := by
      rw [← ih (N / 2 ^ B), Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      have h1 : N / 2 ^ (B * (i + 1)) = (N / 2 ^ B) / 2 ^ (B * i) := by
        rw [Nat.div_div_eq_div_mul, ← pow_add]; congr 1; ring
      have h2 : (2 : ℕ) ^ (B * (i + 1)) = 2 ^ B * 2 ^ (B * i) := by rw [← pow_add]; congr 1; ring
      rw [h1, h2]; ring
    rw [htail]
    have hsplit : N % 2 ^ (B * (n + 1)) = N % 2 ^ B + 2 ^ B * ((N / 2 ^ B) % 2 ^ (B * n)) := by
      conv_lhs => rw [show B * (n + 1) = B + B * n by ring, pow_add, Nat.mod_mul]
    rw [hsplit]; ring

end

section
variable {p : ℕ} [Fact p.Prime]
variable {m : ℕ} [NeZero m]

def carryOffset (B : ℕ) : ℕ := (m + 1) * 2 ^ (B + 1)

structure BigIntParams (p m : ℕ) where

  B : ℕ

  W : ℕ

  hB : 2 ^ B < p

  hW : 2 ^ W < p

  hB1 : 1 ≤ B

  hWB : carryOffset (m := m) B * 2 < 2 ^ W

  hWp : (m + 1) * 2 ^ (2 * B) * 3 + 2 ^ W * 2 ^ B + 2 ^ W < p

  hp : 2 ^ (2 * B) * (m + 1) * 4 < p

end

section
variable {p : ℕ} [Fact p.Prime]
variable {m : ℕ} [NeZero m]

end

end Solution.Secp256k1ScalarMulFixedBase

end DonorFile0_0

-- Adapted donor module: MulModTheorems
section DonorFile0_1

namespace Solution.Secp256k1ScalarMulFixedBase
open Solution.Secp256k1ScalarMulFixedBase.Limbs

namespace MulMod

section
variable {p : ℕ} [Fact p.Prime]
variable {m : ℕ} [NeZero m]

end

end MulMod

end Solution.Secp256k1ScalarMulFixedBase

end DonorFile0_1

-- Adapted donor module: Vandermonde
section DonorFile0_2

namespace Solution.Secp256k1ScalarMulFixedBase

open Polynomial

end Solution.Secp256k1ScalarMulFixedBase

end DonorFile0_2

-- Adapted donor module: Normalize
section DonorFile0_3

namespace Solution.Secp256k1ScalarMulFixedBase
open Solution.Secp256k1ScalarMulFixedBase.Limbs

section
variable {p : ℕ} [Fact p.Prime]
variable {m : ℕ}

namespace Normalize

def main (P : BigIntParams p m) [Fact (p > 2)] (x : Var (BigInt m) (F p)) :
    Circuit (F p) Unit :=
  Circuit.forEach x (fun xi => Gadgets.ToBits.rangeCheck P.B P.hB xi)

instance elaborated (P : BigIntParams p m) [Fact (p > 2)] :
    ElaboratedCircuit (F p) (BigInt m) unit (main P) where
  localLength _ := m * P.B
  localLength_eq := by
    intro input offset
    simp only [main, circuit_norm, Gadgets.ToBits.rangeCheck]
  subcircuitsConsistent := by
    intro input offset
    simp +arith only [main, circuit_norm, Gadgets.ToBits.rangeCheck]
  channelsLawful := by
    simp only [main, circuit_norm, Gadgets.ToBits.rangeCheck]

def Assumptions (_ : BigInt m (F p)) : Prop := True

def Spec (B : ℕ) (x : BigInt m (F p)) : Prop := BigInt.Normalized B x

def circuit (P : BigIntParams p m) [Fact (p > 2)] : FormalAssertion (F p) (BigInt m) where
  main := main P
  Assumptions := Assumptions
  Spec := Spec P.B
  soundness := by
    circuit_proof_start
    simp_all only [circuit_norm, Gadgets.ToBits.rangeCheck, BigInt.Normalized]
    intro i
    rw [← h_input, Vector.getElem_map]
    exact h_holds i
  completeness := by
    circuit_proof_start
    simp_all only [circuit_norm, Gadgets.ToBits.rangeCheck, BigInt.Normalized]
    intro i
    have := h_spec i
    rwa [← h_input, Vector.getElem_map] at this

end Normalize

end

end Solution.Secp256k1ScalarMulFixedBase

end DonorFile0_3

-- Adapted donor module: Equal
section DonorFile0_4

namespace Solution.Secp256k1ScalarMulFixedBase
open Solution.Secp256k1ScalarMulFixedBase.Limbs

section
variable {p : ℕ} [Fact p.Prime]
variable {m : ℕ}

namespace Equal

structure Inputs (m : ℕ) (F : Type) where
  lhs : BigInt m F
  rhs : BigInt m F
deriving ProvableStruct

end Equal

end

end Solution.Secp256k1ScalarMulFixedBase

end DonorFile0_4

-- Adapted donor module: LessThan
section DonorFile0_5

namespace Solution.Secp256k1ScalarMulFixedBase
open Solution.Secp256k1ScalarMulFixedBase.Limbs

section
variable {p : ℕ} [Fact p.Prime]
variable {m : ℕ} [NeZero m]

namespace LessThan

structure Inputs (m : ℕ) (F : Type) where
  lhs : BigInt m F
  rhs : BigInt m F
deriving ProvableStruct

private def evalValue (B : ℕ) (env : ProverEnvironment (F p))
    (x : Var (BigInt m) (F p)) : ℕ :=
  Solution.Secp256k1ScalarMulFixedBase.Limbs.fromLimbs B ((x.map (Expression.eval env.toEnvironment)).toList.map ZMod.val)

def main (P : BigIntParams p m) [Fact (p > 2)] (input : Var (Inputs m) (F p)) :
    Circuit (F p) Unit := do
  let a := input.lhs
  let b := input.rhs

  let d ← ProvableType.witness (α := BigInt m) fun env =>
    let dval : ℕ := evalValue P.B env b - 1 - evalValue P.B env a
    Vector.ofFn fun k : Fin m => ((dval / 2 ^ (P.B * k.val) % 2 ^ P.B : ℕ) : F p)

  Normalize.circuit P d

  let carry ← witnessVector (m - 1) fun env =>
    let av : ℕ → ℕ := fun j => if h : j < m then (Expression.eval env.toEnvironment a[j]).val else 0
    let dv : ℕ → ℕ := fun j => if h : j < m then (Expression.eval env.toEnvironment d[j]).val else 0
    Vector.ofFn fun k : Fin (m - 1) =>
      (((1 + ∑ j ∈ Finset.range (k.val + 1), (av j + dv j) * 2 ^ (P.B * j))
          / 2 ^ (P.B * (k.val + 1)) : ℕ) : F p)

  Circuit.forEach carry (fun c => assertZero (c * (c - 1)))

  let constraints : Vector (Expression (F p)) m := Vector.mapFinRange m fun k =>
    let carryIn : Expression (F p) :=
      if h : k.val = 0 then 0 else carry[k.val - 1]'(by omega)
    let one : Expression (F p) := if k.val = 0 then 1 else 0
    let carryOut : Expression (F p) :=
      if h : k.val < m - 1 then carry[k.val]'h else 0
    a[k.val] + d[k.val] + carryIn + one - b[k.val] - carryOut * (2 ^ P.B : F p)
  Circuit.forEach constraints assertZero

end LessThan

end

end Solution.Secp256k1ScalarMulFixedBase

end DonorFile0_5

-- Adapted donor module: EqViaCarries
section DonorFile0_6

namespace Solution.Secp256k1ScalarMulFixedBase
open Solution.Secp256k1ScalarMulFixedBase.Limbs

section
variable {p : ℕ} [Fact p.Prime]
variable {m : ℕ} [NeZero m]

namespace EqViaCarries

end EqViaCarries

end

end Solution.Secp256k1ScalarMulFixedBase

end DonorFile0_6

-- Adapted donor module: MulMod
section DonorFile0_7

namespace Solution.Secp256k1ScalarMulFixedBase
open Solution.Secp256k1ScalarMulFixedBase.Limbs

section
variable {p : ℕ} [Fact p.Prime]
variable {m : ℕ} [NeZero m]

namespace MulMod

end MulMod

end

end Solution.Secp256k1ScalarMulFixedBase

end DonorFile0_7

-- Adapted donor module: Params
section DonorFile0_8

namespace Solution.Secp256k1ScalarMulFixedBase

@[reducible] def circomPrime : ℕ :=
  Challenge.Instances.Secp256k1ScalarMul.Interface.circomPrime

-- Keep legacy donor I/O declarations available, but field algebra in this
-- variable-base port must use the variable-base verifier's permitted proof.
instance (priority := 2000) : Fact (circomPrime.Prime) :=
  ⟨Challenge.Instances.Secp256k1ScalarMul.Interface.hCircomPrime⟩

instance : Fact (circomPrime > 2) := ⟨by decide⟩

@[reducible] def P256 : ℕ := Specs.Secp256k1.p

@[reducible] def numLimbs : ℕ := 4

@[reducible] def limbBits : ℕ := 64

@[reducible] def Emu : TypeMap := BigInt numLimbs

def secpParams : BigIntParams circomPrime numLimbs where
  B := limbBits
  W := 69
  hB := by decide
  hW := by decide
  hB1 := by decide
  hWB := by decide
  hWp := by decide
  hp := by decide

def limbOfNat (v k : ℕ) : ℕ := v / 2 ^ (limbBits * k) % 2 ^ limbBits

def emuOfNat (v : ℕ) : Emu (F circomPrime) :=
  Vector.ofFn fun k : Fin numLimbs => ((limbOfNat v k.val : ℕ) : F circomPrime)

theorem emu_map_eval_eq_of_eval_eq {env env' : ProverEnvironment (F circomPrime)}
    {x : Var Emu (F circomPrime)}
    (h : eval env x = eval env' x) :
    x.map (Expression.eval env.toEnvironment) =
      x.map (Expression.eval env'.toEnvironment) := by
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_map]
  have h_i : (eval env x)[i] = (eval env' x)[i] := by
    simpa only using congrArg (fun y : Emu (F circomPrime) => y[i]) h
  rw [← ProvableType.getElem_eval_fields_prover (env := env) x i hi,
    ← ProvableType.getElem_eval_fields_prover (env := env') x i hi] at h_i
  exact h_i

def decodeFe (x : Emu (F circomPrime)) : Specs.Secp256k1.Fp :=
  ((x.value limbBits : ℕ) : Specs.Secp256k1.Fp)

end Solution.Secp256k1ScalarMulFixedBase

end DonorFile0_8

-- Adapted donor module: AddModTheorems
section DonorFile0_9

namespace Solution.Secp256k1ScalarMulFixedBase
open Solution.Secp256k1ScalarMulFixedBase.Limbs

namespace AddMod

end AddMod

end Solution.Secp256k1ScalarMulFixedBase

end DonorFile0_9

-- Adapted donor module: AddMod
section DonorFile0_10

namespace Solution.Secp256k1ScalarMulFixedBase
namespace AddMod

end AddMod
end Solution.Secp256k1ScalarMulFixedBase

end DonorFile0_10

-- Adapted donor module: SubModTheorems
section DonorFile0_11

namespace Solution.Secp256k1ScalarMulFixedBase
open Solution.Secp256k1ScalarMulFixedBase.Limbs

namespace SubMod

end SubMod

end Solution.Secp256k1ScalarMulFixedBase

end DonorFile0_11

-- Adapted donor module: SubMod
section DonorFile0_12

namespace Solution.Secp256k1ScalarMulFixedBase
namespace SubMod

end SubMod
end Solution.Secp256k1ScalarMulFixedBase

end DonorFile0_12

-- Adapted donor module: IsZeroFeTheorems
section DonorFile0_13

namespace Solution.Secp256k1ScalarMulFixedBase

section
variable {p : ℕ} [Fact p.Prime] {m : ℕ}

end

end Solution.Secp256k1ScalarMulFixedBase

end DonorFile0_13

-- Adapted donor module: IsZeroFe
section DonorFile0_14

namespace Solution.Secp256k1ScalarMulFixedBase
namespace IsZeroFe

end IsZeroFe
end Solution.Secp256k1ScalarMulFixedBase

namespace Solution.Secp256k1ScalarMulFixedBase
namespace IsZeroFeD

end IsZeroFeD
end Solution.Secp256k1ScalarMulFixedBase

end DonorFile0_14

-- Adapted donor module: Mux
section DonorFile0_15

namespace Solution.Secp256k1ScalarMulFixedBase
namespace Mux

section
variable {M : TypeMap} [ProvableType M]

end
end Mux
end Solution.Secp256k1ScalarMulFixedBase

namespace Solution.Secp256k1ScalarMulFixedBase
namespace Mux

section ComputableWitness
variable {M : TypeMap} [ProvableType M]
open Challenge.Utils.ComputableWitnessLemmas

end ComputableWitness

end Mux
end Solution.Secp256k1ScalarMulFixedBase

end DonorFile0_15

-- Adapted donor module: DivOrZeroTheorems
section DonorFile0_16

namespace Solution.Secp256k1ScalarMulFixedBase
namespace DivOrZero

lemma P256_pos : 0 < P256 := by decide

instance : NeZero P256 := ⟨Nat.pos_iff_ne_zero.mp P256_pos⟩

lemma secpParams_B : secpParams.B = limbBits := rfl

end DivOrZero
end Solution.Secp256k1ScalarMulFixedBase

end DonorFile0_16

-- Adapted donor module: DivOrZero
section DonorFile0_17

namespace Solution.Secp256k1ScalarMulFixedBase
namespace DivOrZero

end DivOrZero
end Solution.Secp256k1ScalarMulFixedBase

end DonorFile0_17

-- Adapted donor module: ToBytesTheorems
section DonorFile0_18

namespace Solution.Secp256k1ScalarMulFixedBase
open Solution.Secp256k1ScalarMulFixedBase.Limbs

namespace ToBytes

section
variable {p : ℕ} [Fact p.Prime]

end

end ToBytes

end Solution.Secp256k1ScalarMulFixedBase

end DonorFile0_18

-- Adapted donor module: ToBytes
section DonorFile0_19

namespace Solution.Secp256k1ScalarMulFixedBase
namespace ToBytes

end ToBytes
end Solution.Secp256k1ScalarMulFixedBase

end DonorFile0_19

-- Adapted donor module: Cost
section DonorFile0_20

namespace Solution.Secp256k1ScalarMulFixedBase
namespace Cost

open Challenge.CostR1CS

theorem CostIs.provableWitness {α : TypeMap} [ProvableType α]
    (compute : ProverEnvironment (F circomPrime) → α (F circomPrime)) :
    CostIs (ProvableType.witness (α := α) compute) ⟨size α, 0⟩ := by
  intro n; rfl

theorem IsR1CSCirc.provableWitness {α : TypeMap} [ProvableType α]
    (compute : ProverEnvironment (F circomPrime) → α (F circomPrime)) :
    IsR1CSCirc (ProvableType.witness (α := α) compute) := by
  intro n; trivial

theorem CostIs.subcircuitWithAssertion {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    {circuit : GeneralFormalCircuit (F circomPrime) Input Output}
    {b : Var Input (F circomPrime)} {K : Count}
    (h : ∀ n, operationCount ((circuit.main b).operations n) = K) :
    CostIs (subcircuitWithAssertion circuit b) K := by
  intro n
  show operationCount [Operation.subcircuit (circuit.toSubcircuit n b)] = K
  have hz : operationCount [Operation.subcircuit (circuit.toSubcircuit n b)]
      = nestedCount (circuit.toSubcircuit n b).ops := by
    show nestedCount _ + operationCount ([] : Operations (F circomPrime)) = nestedCount _
    rw [show operationCount ([] : Operations (F circomPrime)) = Count.zero from rfl, Count.add_zero]
  rw [hz]
  show nestedCount (NestedOperations.nested ⟨circuit.name, ((circuit.main b).operations n).toNested⟩) = K
  rw [show nestedCount (NestedOperations.nested ⟨circuit.name, ((circuit.main b).operations n).toNested⟩)
        = nestedListCount ((circuit.main b).operations n).toNested from rfl,
      Lemmas.operationCount_toNested]
  exact h n

theorem IsR1CSCirc.subcircuitWithAssertion {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    {circuit : GeneralFormalCircuit (F circomPrime) Input Output}
    {b : Var Input (F circomPrime)}
    (h : ∀ n, operationsIsR1CS ((circuit.main b).operations n)) :
    IsR1CSCirc (subcircuitWithAssertion circuit b) := by
  intro n
  show operationsIsR1CS [Operation.subcircuit (circuit.toSubcircuit n b)]
  refine ⟨?_, trivial⟩
  show flatOperationsIsR1CS (circuit.toSubcircuit n b).ops.toFlat
  have hofl : (circuit.toSubcircuit n b).ops.toFlat = ((circuit.main b).operations n).toFlat := by
    show (NestedOperations.nested ⟨circuit.name, ((circuit.main b).operations n).toNested⟩).toFlat = _
    rw [Operations.toNested_toFlat]
  rw [hofl]
  exact (Lemmas.operationsIsR1CS_iff_toFlat _).mp (h n)

theorem IsR1CSCirc.forEach_mem {α : Type} {m : ℕ} [Inhabited α] {xs : Vector α m}
    {body : α → Circuit (F circomPrime) Unit}
    {constant : Circuit.ConstantLength body}
    (h : ∀ (i : Fin m) n, operationsIsR1CS ((body xs[i.val]).operations n)) :
    IsR1CSCirc (Circuit.forEach xs body constant) := by
  intro n
  rw [Circuit.forEach.operations_eq]
  exact operationsIsR1CS_flatten_ofFn _ (fun i => h i _)

attribute [local irreducible] isR1CSRow r1csProducts operationsIsR1CS flatOperationsIsR1CS

theorem affine_fieldFromBitsExpr {n : ℕ} (bits : Var (fields n) (F circomPrime))
    (h : AffineW bits) : Affine (Utils.Bits.fieldFromBitsExpr bits) := by
  unfold Utils.Bits.fieldFromBitsExpr
  apply affine_finFoldl'
  · exact Affine.zero
  · intro acc i hacc
    exact Affine.add hacc (Affine.mul_fconst _ (h i.val i.isLt))

variable {m : ℕ}

theorem affineW_provableWitness_bigInt {k : ℕ}
    (compute : ProverEnvironment (F circomPrime) → BigInt k (F circomPrime)) (nd : ℕ) :
    AffineW ((ProvableType.witness (α := BigInt k) compute).output nd :
      Var (BigInt k) (F circomPrime)) := by
  rw [show ((ProvableType.witness (α := BigInt k) compute).output nd : Var (BigInt k) (F circomPrime))
        = varFromOffset (BigInt k) nd from rfl]
  exact affineW_varFromOffset _ _

theorem isR1CSRow_mul_sub {A B C : Expression (F circomPrime)}
    (hA : Affine A) (hB : Affine B) (hC : Affine C) : isR1CSRow (A * B - C) := by
  rcases r1csProducts_mul_affine hA hB with h | h
  · exact isR1CSRow_of_r1csProducts (k := 0)
      (by show r1csProducts (A * B + -C) = some 0
          rw [r1csProducts_add, r1csProducts_neg, r1csProducts_of_affine hC, h]) (by omega)
  · exact isR1CSRow_of_r1csProducts (k := 1)
      (by show r1csProducts (A * B + -C) = some 1
          rw [r1csProducts_add, r1csProducts_neg, r1csProducts_of_affine hC, h]) (by omega)

theorem IsR1CSCirc.bind_out_inv {α β : Type} {f : Circuit (F circomPrime) α}
    {g : α → Circuit (F circomPrime) β} (P : α → Prop)
    (hf : IsR1CSCirc f)
    (hout : ∀ n, P (f.output n))
    (hg : ∀ a, P a → IsR1CSCirc (g a)) :
    IsR1CSCirc (f >>= g) := by
  intro n
  rw [Circuit.bind_operations_eq, Lemmas.operationsIsR1CS_append]
  exact ⟨hf n, hg _ (hout _) _⟩

end Cost

namespace CompactAdd

open Challenge.CostR1CS
open Cost

attribute [local irreducible] isR1CSRow r1csProducts operationsIsR1CS flatOperationsIsR1CS

theorem isR1CSRow_add_mul_sub {C A B D : Expression (F circomPrime)}
    (hC : Affine C) (hA : Affine A) (hB : Affine B) (hD : Affine D) :
    isR1CSRow (C + A * B - D) := by
  rcases r1csProducts_mul_affine hA hB with h | h
  · refine isR1CSRow_of_r1csProducts (k := 0) ?_ (by omega)
    show r1csProducts (C + A * B + -D) = some 0
    rw [r1csProducts_add, r1csProducts_add, r1csProducts_neg, h,
        r1csProducts_of_affine hC, r1csProducts_of_affine hD]
  · refine isR1CSRow_of_r1csProducts (k := 1) ?_ (by omega)
    show r1csProducts (C + A * B + -D) = some 1
    rw [r1csProducts_add, r1csProducts_add, r1csProducts_neg, h,
        r1csProducts_of_affine hC, r1csProducts_of_affine hD]

end CompactAdd
end Solution.Secp256k1ScalarMulFixedBase

end DonorFile0_20

-- Adapted donor module: EqViaCarriesFlex
section DonorFile0_21

namespace Solution.Secp256k1ScalarMulFixedBase
open Solution.Secp256k1ScalarMulFixedBase.Limbs

section
variable {p : ℕ} [Fact p.Prime]
variable {n : ℕ} [NeZero n]

namespace EqViaCarriesFlex

end EqViaCarriesFlex

end

namespace Cost

open Challenge.CostR1CS

variable {n : ℕ}

end Cost

end Solution.Secp256k1ScalarMulFixedBase

namespace Solution.Secp256k1ScalarMulFixedBase
namespace EqViaCarriesFlex

section ComputableWitness
variable {p : ℕ} [Fact p.Prime] {n : ℕ} [NeZero n]
open Challenge.Utils.ComputableWitnessLemmas

end ComputableWitness

end EqViaCarriesFlex

end Solution.Secp256k1ScalarMulFixedBase

end DonorFile0_21

-- Adapted donor module: RangeCheck
section DonorFile0_22

namespace Solution.Secp256k1ScalarMulFixedBase
namespace RangeCheck

open Utils.Bits

section
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2)]

def main (n : ℕ) (x : Expression (F p)) : Circuit (F p) Unit := do
  let bits ← witnessVector (n - 1) (fun env => fieldToBits (n - 1) (x.eval env))
  Circuit.forEach bits (fun b => assertZero (b * (b - 1)))
  let top := (((2 ^ (n - 1) : ℕ) : F p)⁻¹ : F p) * (x - fieldFromBitsExpr bits)
  assertZero (top * (top - 1))

instance elaborated (n : ℕ) : ElaboratedCircuit (F p) field unit (main n) := by
  elaborate_circuit

def Assumptions (_x : F p) : Prop := True

def Spec (n : ℕ) (x : F p) : Prop := x.val < 2 ^ n

private theorem pow_pred_lt {n : ℕ} (hn : 2 ^ n < p) :
    2 ^ (n - 1) < p := by
  exact lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le n 1)) hn

private theorem pow_pred_ne_zero {n : ℕ} (hn : 2 ^ n < p) :
    (((2 ^ (n - 1) : ℕ) : F p) ≠ 0) := by
  intro h
  have hval : (((2 ^ (n - 1) : ℕ) : F p).val) = 2 ^ (n - 1) :=
    ZMod.val_natCast_of_lt (pow_pred_lt hn)
  rw [h, ZMod.val_zero] at hval
  have hpos : 0 < 2 ^ (n - 1) := Nat.two_pow_pos _
  omega

private theorem two_mul_pow_pred {n : ℕ} (hpos : 1 ≤ n) :
    2 * 2 ^ (n - 1) = 2 ^ n := by
  rw [Nat.mul_comm, ← Nat.pow_succ]
  congr 1
  omega

theorem soundness (n : ℕ) (hn : 2 ^ n < p) (hpos : 1 ≤ n) :
    FormalAssertion.Soundness (Input := field) (F p) (main n) Assumptions (Spec n) := by
  circuit_proof_start [main, Spec]
  obtain ⟨h_bool, h_eq⟩ := h_holds
  set bit_vars : Vector (Expression (F p)) (n - 1) :=
    Vector.mapRange (n - 1) (fun i => var ⟨i₀ + i⟩) with hbv
  have hval : ∀ (i : ℕ) (hi : i < n - 1), (bit_vars.map env)[i] = env.get (i₀ + i) := by
    intro i hi
    simp only [hbv, Vector.getElem_map, Vector.getElem_mapRange]
    rfl
  have h_bits : ∀ (i : ℕ) (hi : i < n - 1),
      (bit_vars.map env)[i] = 0 ∨ (bit_vars.map env)[i] = 1 := by
    intro i hi
    rw [hval i hi]
    rcases mul_eq_zero.mp (h_bool ⟨i, hi⟩) with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (add_neg_eq_zero.mp h1)
  have hE : Expression.eval env (fieldFromBitsExpr bit_vars)
      = fieldFromBits (bit_vars.map env) := fieldFromBits_eval bit_vars
  set L : F p := fieldFromBits (bit_vars.map env) with hL
  have hLlt : L.val < 2 ^ (n - 1) := fieldFromBits_lt _ h_bits
  rw [hE] at h_eq
  have hbase := pow_pred_ne_zero hn
  rcases mul_eq_zero.mp h_eq with h | h
  · have hin : input = L := by
      rcases mul_eq_zero.mp h with h0 | h0
      · exact absurd h0 (inv_ne_zero hbase)
      · linear_combination h0
    rw [hin]
    exact lt_of_lt_of_le hLlt (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le n 1))
  · have hin : input = L + ((2 ^ (n - 1) : ℕ) : F p) := by
      have h1 : (((2 ^ (n - 1) : ℕ) : F p)⁻¹ : F p) * (input + -L) = 1 := by
        linear_combination h
      have h2 : ((2 ^ (n - 1) : ℕ) : F p) *
          ((((2 ^ (n - 1) : ℕ) : F p)⁻¹ : F p) * (input + -L))
          = ((2 ^ (n - 1) : ℕ) : F p) := by
        rw [h1, mul_one]
      rw [← mul_assoc, mul_inv_cancel₀ hbase, one_mul] at h2
      linear_combination h2
    have hsum_lt : L.val + 2 ^ (n - 1) < 2 ^ n := by
      rw [← two_mul_pow_pred hpos]
      omega
    have hcast : input = ((L.val + 2 ^ (n - 1) : ℕ) : F p) := by
      rw [hin]
      push_cast
      rw [ZMod.natCast_zmod_val]
    rw [hcast, ZMod.val_cast_of_lt (lt_trans hsum_lt hn)]
    exact hsum_lt

theorem completeness (n : ℕ) (hn : 2 ^ n < p) (hpos : 1 ≤ n) :
    FormalAssertion.Completeness (Input := field) (F p) (main n) Assumptions (Spec n) := by
  circuit_proof_start [main, Spec]
  set bit_vars : Vector (Expression (F p)) (n - 1) :=
    Vector.mapRange (n - 1) (fun i => var ⟨i₀ + i⟩) with hbv
  refine ⟨?_, ?_⟩
  · intro i
    rw [h_env i]
    rcases @fieldToBits_bits p _ (n - 1) input i.val i.isLt with h0 | h1
    · rw [h0]; ring
    · rw [h1]; ring
  · set x : F p := input with hx
    set base : ℕ := 2 ^ (n - 1) with hbaseNat
    have hmap : bit_vars.map env.toEnvironment = fieldToBits (n - 1) x := by
      apply Vector.ext
      intro i hi
      rw [hbv, Vector.getElem_map, Vector.getElem_mapRange]
      simpa using h_env ⟨i, hi⟩
    set v : ℕ := x.val with hv
    have hE0 : Expression.eval env.toEnvironment (fieldFromBitsExpr bit_vars)
        = fieldFromBits (bit_vars.map env.toEnvironment) := fieldFromBits_eval bit_vars
    have hE : Expression.eval env.toEnvironment (fieldFromBitsExpr bit_vars)
        = ((v % base : ℕ) : F p) := by
      rw [hE0, hmap, fieldFromBits_fieldToBits_mod, hbaseNat]
    rw [hE]
    have hbaseF := pow_pred_ne_zero hn
    have hinput : x = ((base * (v / base) + v % base : ℕ) : F p) := by
      rw [show base * (v / base) + v % base = v from Nat.div_add_mod v base, hv,
        ZMod.natCast_zmod_val]
    have htop : (((2 ^ (n - 1) : ℕ) : F p)⁻¹ : F p) *
          (x + -((v % base : ℕ) : F p))
        = ((v / base : ℕ) : F p) := by
      rw [hinput]
      have hbaseF' : ((base : F p) ≠ 0) := by
        rw [hbaseNat]
        exact hbaseF
      change ((base : F p)⁻¹ : F p) *
          (((base * (v / base) + v % base : ℕ) : F p) + -((v % base : ℕ) : F p))
        = ((v / base : ℕ) : F p)
      push_cast
      field_simp [hbaseF']
      ring
    rw [htop]
    have hq_lt : v / base < 2 := by
      apply Nat.div_lt_of_lt_mul
      rw [hbaseNat, Nat.mul_comm, two_mul_pow_pred hpos]
      rw [hv]
      exact h_spec
    have hq : v / base = 0 ∨ v / base = 1 := by
      rcases Nat.eq_zero_or_pos (v / base) with h0 | hposq
      · exact Or.inl h0
      · exact Or.inr (by omega)
    rcases hq with h | h <;> rw [h] <;> norm_num

def circuit (n : ℕ) (hn : 2 ^ n < p) (hpos : 1 ≤ n) : FormalAssertion (F p) field where
  main := main n
  elaborated := elaborated n
  Assumptions := Assumptions
  Spec := Spec n
  soundness := soundness n hn hpos
  completeness := completeness n hn hpos

theorem computableWitnesses (n : ℕ) (hn : 2 ^ n < p) (hpos : 1 ≤ n) :
    (circuit n hn hpos).ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition input env env')
    ((main n input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.witnessVector_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.forEach_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.assertZero_structuralComputableWitnesses_iff,
    and_true]
  and_intros
  · intro _ h_input
    rw [CircuitType.eval_expression_prover_to_verifier (M := field),
      CircuitType.eval_expression_prover_to_verifier (M := field)] at h_input
    have h_input_expr :
        Expression.eval env.toEnvironment input = Expression.eval env'.toEnvironment input := by
      simpa only [CircuitType.eval_var_field] using h_input
    exact congrArg (fieldToBits (n - 1)) h_input_expr
  · intro _
    trivial

end

end RangeCheck
end Solution.Secp256k1ScalarMulFixedBase

end DonorFile0_22
