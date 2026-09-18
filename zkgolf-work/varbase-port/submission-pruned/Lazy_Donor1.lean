import Solution.Secp256k1ScalarMul.Lazy_Donor0

-- Adapted donor module: GroupedFlex
section DonorFile1_0

namespace Solution.Secp256k1ScalarMulFixedBase

section
variable {p : ℕ} [Fact p.Prime]
variable {L : ℕ} [NeZero L]

namespace GroupedFlex

end GroupedFlex

end

namespace Cost

open Challenge.CostR1CS

theorem costIs_implicitRangeCheck (n : ℕ) (hpos : 1 ≤ n) (x : Expression (F circomPrime)) :
    CostIs (RangeCheck.main n x) ⟨n - 1, n⟩ := by
  unfold RangeCheck.main
  rw [show (⟨n - 1, n⟩ : Count)
        = ⟨n - 1, 0⟩ + (⟨(n - 1) * 0, (n - 1) * 1⟩ + (⟨0, 1⟩ + Count.zero)) from by
      simp only [Count.zero]; congr 1 <;> simp only [Count.add_constraints] <;> omega]
  refine CostIs.bind (CostIs.witnessVector (F := F circomPrime) (n - 1) _) fun bits => ?_
  refine CostIs.bind (CostIs.forEach fun a m => CostIs.assertZero _ m) fun _ => ?_
  exact CostIs.bind (CostIs.assertZero _) fun _ => CostIs.pure _

theorem isR1CS_implicitRangeCheck (n : ℕ) (x : Expression (F circomPrime)) (hx : Affine x) :
    IsR1CSCirc (RangeCheck.main n x) := by
  unfold RangeCheck.main
  refine IsR1CSCirc.bind_out (IsR1CSCirc.witnessVector (n - 1) _) fun w => ?_
  refine IsR1CSCirc.bind ?_ fun _ => ?_
  · refine IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) fun i k => ?_
    refine IsR1CSCirc.assertZero ?_ k
    exact isR1CSRow_mul (affineW_witnessVector_output _ _ _ i.val i.isLt)
      (Affine.sub (affineW_witnessVector_output _ _ _ i.val i.isLt) (Affine.const 1))
  · refine IsR1CSCirc.bind (IsR1CSCirc.assertZero ?_) fun _ => IsR1CSCirc.pure _
    let bits : Var (fields (n - 1)) (F circomPrime) :=
      (Circuit.witnessVector (n - 1) fun env => Utils.Bits.fieldToBits (n - 1) (x.eval env)).output w
    have hbits : Affine (Utils.Bits.fieldFromBitsExpr bits) := by
      change Affine (Utils.Bits.fieldFromBitsExpr
        (Vector.mapRange (n - 1) fun i => Expression.var { index := w + i }))
      exact affine_fieldFromBitsExpr _ (affineW_mapRange_var _)
    let c : F circomPrime := (((2 ^ (n - 1) : ℕ) : F circomPrime)⁻¹ : F circomPrime)
    have htop : Affine (c * (x - Utils.Bits.fieldFromBitsExpr bits)) := by
      exact Affine.fconst_mul c (Affine.sub hx hbits)
    exact isR1CSRow_mul htop (Affine.sub htop (Affine.const 1))

theorem costIs_assertion_implicitRangeCheck (n : ℕ) (hn : (2 : ℕ) ^ n < circomPrime)
    (hpos : 1 ≤ n) (x : Expression (F circomPrime)) :
    CostIs (assertion (RangeCheck.circuit n hn hpos) x) ⟨n - 1, n⟩ :=
  CostIs.assertion (fun m => costIs_implicitRangeCheck n hpos x m)

theorem isR1CS_assertion_implicitRangeCheck (n : ℕ) (hn : (2 : ℕ) ^ n < circomPrime)
    (hpos : 1 ≤ n) (x : Expression (F circomPrime)) (hx : Affine x) :
    IsR1CSCirc (assertion (RangeCheck.circuit n hn hpos) x) :=
  IsR1CSCirc.assertion (fun m => isR1CS_implicitRangeCheck n x hx m)

section GroupedXV
variable {L : ℕ}

end GroupedXV

end Cost

end Solution.Secp256k1ScalarMulFixedBase

end DonorFile1_0

-- Adapted donor module: InterpMul
section DonorFile1_1

namespace Solution.Secp256k1ScalarMulFixedBase

section
variable {p : ℕ} [Fact p.Prime]
variable {m : ℕ} [NeZero m]

namespace MulMod

end MulMod

namespace Cost
open Challenge.CostR1CS

end Cost

end

end Solution.Secp256k1ScalarMulFixedBase

end DonorFile1_1

-- Adapted donor module: Select
section DonorFile1_2

namespace Solution.Secp256k1ScalarMulFixedBase
namespace Select

structure AffPoint (F : Type) where
  x : Emu F
  y : Emu F
deriving ProvableStruct

def blockExpr (x y wb : Expression (F circomPrime)) (v : ℕ) :
    Expression (F circomPrime) :=
  if v = 0 then ((1 : F circomPrime) : Expression (F circomPrime)) - x - y + wb
  else if v = 1 then x - wb
  else if v = 2 then y - wb
  else wb

def weightedSum {m : ℕ} (e : Var (fields m) (F circomPrime))
    (coeff : Fin m → F circomPrime) (base : F circomPrime) : Expression (F circomPrime) :=
  (Vector.ofFn fun j : Fin m => e[j.val]'j.isLt * coeff j).foldl (· + ·) 0 + base

end Select
end Solution.Secp256k1ScalarMulFixedBase

end DonorFile1_2

-- Adapted donor module: FlexInstances
section DonorFile1_3

namespace Solution.Secp256k1ScalarMulFixedBase

end Solution.Secp256k1ScalarMulFixedBase

end DonorFile1_3

-- Adapted donor module: EqViaCarriesFlexT
section DonorFile1_4

namespace Solution.Secp256k1ScalarMulFixedBase
open Solution.Secp256k1ScalarMulFixedBase.Limbs

section
variable {p : ℕ} [Fact p.Prime]
variable {n : ℕ} [NeZero n]

namespace EqViaCarriesFlexT

end EqViaCarriesFlexT

end

namespace Cost

open Challenge.CostR1CS

variable {n : ℕ}

end Cost

namespace EqViaCarriesFlexT

end EqViaCarriesFlexT

end Solution.Secp256k1ScalarMulFixedBase

namespace Solution.Secp256k1ScalarMulFixedBase
namespace EqViaCarriesFlexT

section ComputableWitness
variable {p : ℕ} [Fact p.Prime] {n : ℕ} [NeZero n]
open Challenge.Utils.ComputableWitnessLemmas

end ComputableWitness

end EqViaCarriesFlexT

end Solution.Secp256k1ScalarMulFixedBase

end DonorFile1_4

-- Adapted donor module: GroupedFlexInstances
section DonorFile1_5

namespace Solution.Secp256k1ScalarMulFixedBase

/-! ### Fattened quad instance (§BORROW-PILOT)

Same shape as `gfQuad`/`posOfQuad`/`vQuad` (`G = 5`, partition `[2,2,2,1,2]`),
but the 7 convolution-position bounds are widened `5·2^128 → 12·2^128` to
accommodate a fat-limb multiplicand (`< 3·2^64` per limb, vs `< 2^64`
canonical). `grouped_tent_fat.py` (extending the leader's `grouped_tent.py`)
confirms the DP-optimal partition is unchanged and the cost moves
`406 → 412` (`Wf` widens `68 → 69` uniformly at all 3 paid boundaries),
capacity holding with wide margin (checked up to `32·2^128`). -/

/-! ### Fattened wide instance (§BORROW-ROLLOUT, d2 site)

Same shape as `gfWide`/`posOfWide`/`vWide` (`G = 6`, partition `[2,2,2,2,1,1]`),
but the 7 convolution-position bounds are widened `13·2^128 → 21·2^128`:
after converting stageC1's `d2` to the wire-only fat `dtilOf xT2 x1`, the
LHS coefficient is `convLD2fat (< 12·2^128) + convLX1 (< 8·2^128) + cExp
(< 2^64) < 21·2^128`. The tent DP (grouped_tent script) confirms the
partition is unchanged and the cost moves `423 → 429` (`Wf` widens
`69 → 70` at the 3 wide boundaries; the 4th boundary stays at 6). -/

/-! ### Recode instance (§SKEPTIC-ROUND item 2, w9-mixed retune)

`B = 9`, `L = 30`, uniform per-position bound `1024` (recode digit rows are
10-bit affine combinations; the 4-bit top window and the tail ride the same
loose bound). Partition at max group size 2: `[1] ++ [2]×14 ++ [1]`,
`G = 16`, 14 paid interior boundaries plus the singleton tail. Same
structural regime as the shipped `L = 33` w8 instance. -/

/-! ### Folded (pseudo-Mersenne) layout: `L = 4` positions, a single carry

After folding convolution positions `4,5,6` onto `0,1,2` with the constant
`cF = 2 ^ 256 - P256`, both sides of the modular identity live on four
positions only, the quotient is a single wire below `2 ^ 68`, and one grouped
carry (positions `{0,1}`) plus the native-field row suffice. -/

/-! ### Folded layout for the wide (two-convolution) slope identity -/

end Solution.Secp256k1ScalarMulFixedBase

end DonorFile1_5

-- Adapted donor module: NormalizeImplicit
section DonorFile1_6

namespace Solution.Secp256k1ScalarMulFixedBase
open Solution.Secp256k1ScalarMulFixedBase.Limbs

namespace NormalizeImplicit

variable {m : ℕ}

namespace Cost
open Challenge.CostR1CS
open Solution.Secp256k1ScalarMulFixedBase.Cost

end Cost

end NormalizeImplicit

end Solution.Secp256k1ScalarMulFixedBase

end DonorFile1_6

-- Adapted donor module: CompactAdd
section DonorFile1_7

namespace Solution.Secp256k1ScalarMulFixedBase
namespace CompactAdd

open Specs.Secp256k1 (Fp)

def cExp (v k : ℕ) : Expression (F circomPrime) :=
  (((limbOfNat v k : ℕ) : F circomPrime) : Expression (F circomPrime))

end CompactAdd
end Solution.Secp256k1ScalarMulFixedBase

end DonorFile1_7

-- Adapted donor module: CompactAddR1CS
section DonorFile1_8

namespace Solution.Secp256k1ScalarMulFixedBase
namespace CompactAdd

open Challenge.CostR1CS
open Cost

attribute [local irreducible] isR1CSRow r1csProducts operationsIsR1CS flatOperationsIsR1CS

end CompactAdd
end Solution.Secp256k1ScalarMulFixedBase

end DonorFile1_8

-- Adapted donor module: IncompleteAdd
section DonorFile1_9

namespace Solution.Secp256k1ScalarMulFixedBase
namespace IncompleteAdd

end IncompleteAdd
end Solution.Secp256k1ScalarMulFixedBase

end DonorFile1_9

-- Adapted donor module: BorrowFree
section DonorFile1_10

/-! # Borrow-free fat-limb digit vector for `2·P256`

Pilot library for the chord-denominator de-re-limbing lever (see
`COST_NOTES.md` §BORROW-PILOT). Ported from the leader's `Params.lean`
(`twoPBorrowDigit`) and `CompleteAddTheorems.lean` (the `limb_borrow_*`/
`value_borrow` family) — verbatim in shape, since both trees target the same
`P256 = Specs.Secp256k1.p`. Proof-side only: this file adds zero circuit
cells, it only supplies the value/bound bridging lemmas needed to consume a
wire-only combination `xT[k] + twoPBorrowDigit k − xA[k]` directly (no fresh
witness, no `NormalizeImplicit`, no separate top digit) in place of a
freshly-witnessed canonical `d`.
-/

namespace Solution.Secp256k1ScalarMulFixedBase

end Solution.Secp256k1ScalarMulFixedBase

end DonorFile1_10

-- Adapted donor module: PairAdd
section DonorFile1_11

namespace Solution.Secp256k1ScalarMulFixedBase
namespace PairAdd

open CompactAdd (cExp)

syntax "stageA_simp" : tactic
macro_rules
  | `(tactic| stageA_simp) =>
    `(tactic| simp +arith (maxSteps := 4000000) only
        [stageA, dtilOf, MulMod.witnessedMul, MulMod.interpolatedMul, circuit_norm,
         NormalizeImplicit.circuit, NormalizeImplicit.elaborated,
         EqViaCarriesFlex.circuit, EqViaCarriesFlex.elaborated,
         GroupedFlex.circuit, GroupedFlex.elaborated, GroupedFlex.main,
         gfQuadFat, posOfQuadFat, vQuadFat, wfQuadFat, hgvQuadFat,
         GroupedFlex.widthAllocFrom, GroupedFlex.widthConsFrom,
         secpParams, RangeCheck.circuit, RangeCheck.elaborated, numLimbs, limbBits])

syntax "pair_add_simp" : tactic
macro_rules
  | `(tactic| pair_add_simp) =>
    `(tactic| simp +arith (maxSteps := 4000000) only
        [stageO2, stageC1, stageC2, dtilOf, MulMod.witnessedMul, MulMod.interpolatedMul, circuit_norm,
         NormalizeImplicit.circuit, NormalizeImplicit.elaborated,
         EqViaCarriesFlex.circuit, EqViaCarriesFlex.elaborated,
         GroupedFlex.circuit, GroupedFlex.elaborated, GroupedFlex.main,
         gfLin, posOfLin, vLin, wfLin, hgvLin,
         gfQuad, posOfQuad, vQuad, wfQuad, hgvQuad,
         gfWide, posOfWide, vWide, wfWide, hgvWide,
         gfWideFat, posOfWideFat, vWideFat, wfWideFat, hgvWideFat,
         GroupedFlex.widthAllocFrom, GroupedFlex.widthConsFrom,
         secpParams, RangeCheck.circuit, RangeCheck.elaborated, numLimbs, limbBits])

end PairAdd
end Solution.Secp256k1ScalarMulFixedBase

end DonorFile1_11

-- Adapted donor module: GroupedFlexNoTop
section DonorFile1_12

/-!
# `GroupedFlex` without the final native row

`GroupedFlex.main` emits a grouped carry loop followed by ONE extra row,

  `assertZero (∑ₖ (lhsₖ - rhsₖ) · (2^B)^k)`,

which pins the identity in the native field.  At every call site where the
folded quotient has already been *inverted* — i.e. written as an affine
expression over already-allocated wires rather than witnessed — that row is
identically zero as a polynomial in the wires, so it carries no information.

`mainNoTop` drops it.  The information it used to supply is instead demanded
as an extra *assumption* (`LinIdent`) on the evaluated inputs, which the caller
discharges by `ring` from the definition of the inverted quotient.
-/

namespace Solution.Secp256k1ScalarMulFixedBase

section
variable {p : ℕ} [Fact p.Prime]
variable {L : ℕ} [NeZero L]

namespace GroupedFlex

end GroupedFlex

end

namespace Cost

open Challenge.CostR1CS

section GroupedXVNoTop
variable {L : ℕ}

end GroupedXVNoTop

end Cost

end Solution.Secp256k1ScalarMulFixedBase

end DonorFile1_12

-- Adapted donor module: SparseCanonical
section DonorFile1_13

/-!
### Sparse-prime canonicity check for secp256k1

Exploits the limb structure of `p = P256 = 2^256 − 2^32 − 977`:
its 64-bit limbs are `p₀ = 0xfffffffefffffc2f`, `p₁ = p₂ = p₃ = 2^64 − 1`.
For a normalized 4-limb `r`,
  `r.value < p ⟺ (r₁,r₂,r₃ not all 2^64−1) ∨ r₀ < p₀`.
-/

namespace Solution.Secp256k1ScalarMulFixedBase
namespace SparseCanonical

open Solution.Secp256k1ScalarMulFixedBase.Limbs

end SparseCanonical
end Solution.Secp256k1ScalarMulFixedBase

end DonorFile1_13

-- Adapted donor module: ValidPTheorems
section DonorFile1_14

namespace Solution.Secp256k1ScalarMulFixedBase
namespace ValidP

open Utils.Bits

end ValidP
end Solution.Secp256k1ScalarMulFixedBase

end DonorFile1_14

-- Adapted donor module: ValidPWeak
section DonorFile1_15

/-!
# Inverse-witness ("weak") form of the sparse `x < p` comparison

The sparse comparison against `p = 2^256 - 2^32 - 977` only ever needs
implications of the shape

  "the prefix deficit is zero  ⟹  this target is zero",

never the converse.  A single row `target - deficit * u = 0` with a freshly
witnessed `u` delivers exactly that implication, and consecutive prefix stages
can be pinned by *sums* of deficit counters instead of by explicit equality
flags multiplied together.

That replaces the three `IsZeroField` gadgets and the two product witnesses of
the flag-based tail (8 allocations, 12 rows) by four bare witnesses and four
rows.
-/

namespace Solution.Secp256k1ScalarMulFixedBase
namespace ValidP

open Utils.Bits

set_option maxHeartbeats 2000000

/-! Pure arithmetic helpers.  These are stated over abstract naturals so that
`omega` never has to look at the (very large) `ZMod` atoms. -/

end ValidP
end Solution.Secp256k1ScalarMulFixedBase

end DonorFile1_15

-- Adapted donor module: ToBitsAffine
section DonorFile1_16

namespace Solution.Secp256k1ScalarMulFixedBase
namespace ToBitsAffine

open Utils.Bits

variable {p : ℕ} [Fact p.Prime] [Fact (p > 2)]

def main (w : ℕ) (x : Expression (F p)) : Circuit (F p) (Var (fields (w + 1)) (F p)) := do
  let low ← witnessVector w fun env => fieldToBits w (x.eval env)
  Circuit.forEach low assertBool
  let top := (((2 ^ w : ℕ) : F p)⁻¹ : F p) * (x - fieldFromBitsExpr low)
  assertZero (top * (top - 1))
  return low.push top

instance elaborated (w : ℕ) : ElaboratedCircuit (F p) field (fields (w + 1)) (main w) := by
  elaborate_circuit

private theorem pow_lt {w : ℕ} (hn : 2 ^ (w + 1) < p) : 2 ^ w < p :=
  lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ w)) hn

private theorem pow_ne_zero' {w : ℕ} (hn : 2 ^ (w + 1) < p) :
    (((2 ^ w : ℕ) : F p) ≠ 0) := by
  intro h
  have hval : (((2 ^ w : ℕ) : F p).val) = 2 ^ w :=
    ZMod.val_natCast_of_lt (pow_lt hn)
  rw [h, ZMod.val_zero] at hval
  have hpos : 0 < 2 ^ w := Nat.two_pow_pos _
  omega

theorem fieldFromBits_push {w : ℕ} (low : Vector (F p) w) (top : F p) :
    fieldFromBits (low.push top) = fieldFromBits low + top * ((2 ^ w : ℕ) : F p) := by
  rw [fieldFromBits_succ w (low.push top)]
  have hpop : (low.push top).pop = low := by
    apply Vector.ext; intro i hi
    simp [Vector.getElem_pop', Vector.getElem_push_lt hi]
  rw [hpop, Vector.getElem_push_eq, Nat.cast_pow, Nat.cast_ofNat]

def toBitsAffine (w : ℕ) (hn : 2 ^ (w + 1) < p) : GeneralFormalCircuit (F p) field (fields (w + 1)) where
  main := main w

  ProverAssumptions (x : F p) _ _ := x.val < 2 ^ (w + 1)

  Spec (x : F p) (bits : Vector (F p) (w + 1)) _ :=
    x.val < 2 ^ (w + 1) ∧ bits = fieldToBits (w + 1) x

  soundness := by
    circuit_proof_start
    obtain ⟨h_bool, h_eq⟩ := h_holds
    set low_vars : Vector (Expression (F p)) w := Vector.mapRange w (fun i => var ⟨i₀ + i⟩) with hlv
    set low : Vector (F p) w := low_vars.map env with hlow
    set t : F p := (((2 ^ w : ℕ) : F p)⁻¹ : F p) * (input + -Expression.eval env (fieldFromBitsExpr low_vars)) with ht
    change t * (t + -1) = 0 at h_eq
    have hbase := pow_ne_zero' (w := w) hn
    have hE : Expression.eval env (fieldFromBitsExpr low_vars) = fieldFromBits low :=
      fieldFromBits_eval low_vars
    have h_low_bool : ∀ (i : ℕ) (hi : i < w), low[i] = 0 ∨ low[i] = 1 := by
      intro i hi
      have := h_bool ⟨i, hi⟩
      simp only [IsBool, hlow, hlv, Vector.getElem_map, Vector.getElem_mapRange, Expression.eval] at this ⊢
      exact this
    have h_top_bool : t = 0 ∨ t = 1 := by
      rcases mul_eq_zero.mp h_eq with h | h
      · exact Or.inl h
      · exact Or.inr (by linear_combination h)
    set bits : Vector (F p) (w + 1) := low.push t with hbits
    have h_bits : ∀ (i : ℕ) (hi : i < w + 1), bits[i] = 0 ∨ bits[i] = 1 := by
      intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
      · rw [hbits, Vector.getElem_push_lt hlt]; exact h_low_bool i hlt
      · rw [hbits, Vector.getElem_push_eq]; exact h_top_bool
    have hrecomp : fieldFromBits bits = input := by
      rw [hbits, fieldFromBits_push, ← hE, ht]
      field_simp
      ring
    have hval : input.val < 2 ^ (w + 1) := by
      rw [← hrecomp]; exact fieldFromBits_lt bits h_bits
    have htoBits : fieldToBits (w + 1) input = bits := by
      rw [← hrecomp]; exact fieldToBits_fieldFromBits hn bits h_bits
    refine ⟨hval, ?_⟩
    rw [htoBits, hbits, hlow]
    simp only [circuit_norm, Vector.map_push, hlv, ht, h_input]

  completeness := by
    circuit_proof_start
    set low_vars : Vector (Expression (F p)) w := Vector.mapRange w (fun i => var ⟨i₀ + i⟩) with hlv
    have hbase := pow_ne_zero' (w := w) hn
    refine ⟨?_, ?_⟩
    ·
      intro i
      rw [h_env i]
      rcases fieldToBits_bits (n := w) (x := input) i.val i.isLt with h | h <;>
        rw [h] <;> simp [IsBool]
    ·
      set base : ℕ := 2 ^ w with hbaseNat
      have hmap : low_vars.map env.toEnvironment = fieldToBits w input := by
        apply Vector.ext; intro i hi
        rw [hlv, Vector.getElem_map, Vector.getElem_mapRange]
        simpa using h_env ⟨i, hi⟩
      set v : ℕ := input.val with hv
      have hE0 : Expression.eval env.toEnvironment (fieldFromBitsExpr low_vars)
          = fieldFromBits (low_vars.map env.toEnvironment) := fieldFromBits_eval low_vars
      have hE : Expression.eval env.toEnvironment (fieldFromBitsExpr low_vars)
          = ((v % base : ℕ) : F p) := by
        rw [hE0, hmap, fieldFromBits_fieldToBits_mod, hbaseNat, hv]
      have htop_val : (((2 ^ w : ℕ) : F p)⁻¹ : F p) *
            (input + -Expression.eval env.toEnvironment (fieldFromBitsExpr low_vars))
          = ((v / base : ℕ) : F p) := by
        rw [hE]
        have hbaseF : ((base : F p) ≠ 0) := by rw [hbaseNat]; exact hbase
        have hinput : input = ((base * (v / base) + v % base : ℕ) : F p) := by
          rw [show base * (v / base) + v % base = v from Nat.div_add_mod v base, hv,
            ZMod.natCast_zmod_val]
        change ((base : F p)⁻¹ : F p) * (input + -((v % base : ℕ) : F p))
          = ((v / base : ℕ) : F p)
        rw [hinput]
        push_cast
        field_simp [hbaseF]
        ring
      rw [htop_val]
      have hq_lt : v / base < 2 := by
        apply Nat.div_lt_of_lt_mul
        rw [hbaseNat, ← pow_succ]
        exact h_assumptions
      set q : ℕ := v / base with hq_def
      clear_value q
      rcases (by omega : q = 0 ∨ q = 1) with h | h <;>
        rw [h] <;> norm_num

theorem computableWitnesses (w : ℕ) (hn : 2 ^ (w + 1) < p) :
    (toBitsAffine (p := p) w hn).base.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition input env env')
    (((toBitsAffine (p := p) w hn).main input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold toBitsAffine main
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.witnessVector_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.forEach_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.assertZero_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.pure_structuralComputableWitnesses_iff,
    and_true]
  and_intros
  · intro _ h_input
    rw [CircuitType.eval_expression_prover_to_verifier (M := field),
      CircuitType.eval_expression_prover_to_verifier (M := field)] at h_input
    have h_input_expr :
        Expression.eval env.toEnvironment input = Expression.eval env'.toEnvironment input := by
      simpa only [CircuitType.eval_var_field] using h_input
    exact congrArg (Utils.Bits.fieldToBits w) h_input_expr
  · intro i
    apply Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
    · intro k env env' hk h_agree _
      rw [CircuitType.eval_expression_prover_to_verifier (M := field),
        CircuitType.eval_expression_prover_to_verifier (M := field)]
      rw [show eval env.toEnvironment
            ((witnessVector w fun env =>
                Utils.Bits.fieldToBits w (Expression.eval env.toEnvironment input)).output
          offset)[i.val] =
            env.get (offset + i.val) by
          rw [CircuitType.eval_expression (M := field)]
          simp [Circuit.witnessVector, Circuit.output,
            ProvableType.eval, explicit_provable_type, size, Vector.getElem_mapRange,
            Expression.eval],
        show eval env'.toEnvironment
            ((witnessVector w fun env =>
                Utils.Bits.fieldToBits w (Expression.eval env.toEnvironment input)).output
              offset)[i.val] =
            env'.get (offset + i.val) by
          rw [CircuitType.eval_expression (M := field)]
          simp [Circuit.witnessVector, Circuit.output,
            ProvableType.eval, explicit_provable_type, size, Vector.getElem_mapRange,
            Expression.eval]]
      exact h_agree (offset + i.val) (by
        have hi : i.val < w := i.isLt
        have hbase : offset + w ≤ k := by
          simpa [Circuit.localLength] using hk
        omega)
    · exact assertBoolComputableWitnesses

end ToBitsAffine
end Solution.Secp256k1ScalarMulFixedBase

end DonorFile1_16

-- Adapted donor module: ValidP
section DonorFile1_17

/-!
# secp256k1-specific canonical field validation

Every field-result gadget used to run `Normalize` and then the generic
`LessThan` gadget against `p`.  That decomposes 256 result bits once and then
allocates another 256-bit difference.  Here the four limb decompositions are
kept in scope and compared with the constant

`p = 2^256 - 2^32 - 977`.

The binary representation of `p` has only six zero positions:
`32, 9, 8, 7, 6, 4`.  Three zero tests summarize the long all-one runs and two
product witnesses carry the equal-prefix state.  The resulting assertion has
264 witnesses and 272 rows, versus 520 witnesses and 529 rows for
`Normalize + LessThan`.
-/

namespace Solution.Secp256k1ScalarMulFixedBase
namespace ValidP

open Utils.Bits

/-! ## Computable witnesses -/

end ValidP
end Solution.Secp256k1ScalarMulFixedBase

end DonorFile1_17

-- Adapted donor module: ValidPBytes
section DonorFile1_18

namespace Solution.Secp256k1ScalarMulFixedBase
namespace ValidPBytes

open Utils.Bits
open ValidP

theorem fieldFromBitsExpr_eval_stable {w : ℕ}
    (bits : Var (fields w) (F circomPrime))
    {env env' : ProverEnvironment (F circomPrime)}
    (hbits : ∀ (i : ℕ) (hi : i < w),
      Expression.eval env.toEnvironment (bits[i]'hi) =
        Expression.eval env'.toEnvironment (bits[i]'hi)) :
    Expression.eval env.toEnvironment (fieldFromBitsExpr bits) =
      Expression.eval env'.toEnvironment (fieldFromBitsExpr bits) := by
  change env.toEnvironment (fieldFromBitsExpr bits) =
    env'.toEnvironment (fieldFromBitsExpr bits)
  rw [fieldFromBits_eval (eval := env.toEnvironment) bits,
    fieldFromBits_eval (eval := env'.toEnvironment) bits]
  congr 1
  apply Vector.ext
  intro i hi
  simpa only [Vector.getElem_map] using hbits i hi

theorem toBitsAffine_output_eval_stable (w : ℕ) (x : Expression (F circomPrime))
    {offset k : ℕ} {env env' : ProverEnvironment (F circomPrime)}
    (hx : Expression.eval env.toEnvironment x =
      Expression.eval env'.toEnvironment x)
    (h_agree : env.AgreesBelow k env') (hk : offset + w ≤ k) :
    ∀ (i : ℕ) (hi : i < w + 1),
      Expression.eval env.toEnvironment (((ToBitsAffine.main w x).output offset)[i]'hi) =
        Expression.eval env'.toEnvironment (((ToBitsAffine.main w x).output offset)[i]'hi) := by
  intro i hi
  simp only [ToBitsAffine.main, circuit_norm]
  by_cases hlt : i < w
  · simp only [hlt, ↓reduceDIte, Vector.getElem_mapRange, Expression.eval]
    exact h_agree (offset + i) (by omega)
  · simp only [hlt, ↓reduceDIte, Expression.eval]
    rw [hx]
    rw [fieldFromBitsExpr_eval_stable (env := env) (env' := env')
      (Vector.mapRange w fun i => var { index := offset + i })
      (fun j hj => by
        rw [Vector.getElem_mapRange]
        simp only [Expression.eval]
        exact h_agree (offset + j) (by omega))]

end ValidPBytes
end Solution.Secp256k1ScalarMulFixedBase

end DonorFile1_18

-- Adapted donor module: Canonicalize
section DonorFile1_19

/-! ### merged from NormalizeR.lean (submission file-count cap) -/
section

namespace Solution.Secp256k1ScalarMulFixedBase
open Solution.Secp256k1ScalarMulFixedBase.Limbs

section
variable {p : ℕ} [Fact p.Prime]
variable {m : ℕ}

/-! `Normalize` over the `n−1`-bit `RangeCheck` gadget (one row and one
allocation fewer per limb). Kept separate from `Normalize` so the widely
consumed original keeps its offsets. -/
namespace NormalizeR

end NormalizeR

end

end Solution.Secp256k1ScalarMulFixedBase

end

/-! ### merged from LessThanR.lean (submission file-count cap) -/
section

namespace Solution.Secp256k1ScalarMulFixedBase
open Solution.Secp256k1ScalarMulFixedBase.Limbs

section
variable {p : ℕ} [Fact p.Prime]
variable {m : ℕ} [NeZero m]

namespace LessThanR

end LessThanR

end

end Solution.Secp256k1ScalarMulFixedBase

end

namespace Solution.Secp256k1ScalarMulFixedBase
namespace Canonicalize

open CompactAdd (cExp)

end Canonicalize
end Solution.Secp256k1ScalarMulFixedBase

namespace Solution.Secp256k1ScalarMulFixedBase
namespace Canonicalize
section ComputableWitness
open Challenge.Utils.ComputableWitnessLemmas
end ComputableWitness
end Canonicalize
end Solution.Secp256k1ScalarMulFixedBase

end DonorFile1_19
