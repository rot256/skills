import Solution.Secp256k1ScalarMul.ScalarCongruence
import Solution.Secp256k1ScalarMul.MainTheorems
import Challenge.Utils.ComputableWitnessLemmas

namespace Solution.Secp256k1ScalarMul.GLV.ScalarReduce

set_option maxRecDepth 3000

open Challenge.CostR1CS
open Solution.Secp256k1ScalarMul.Cost
open Solution.Secp256k1ScalarMul.Limbs

@[reducible] def scalarBits : ℕ := Specs.Secp256k1.scalarBits

structure Inputs (F : Type) where
  bits : Vector F scalarBits
deriving ProvableStruct

lemma bitIndex_lt (j : ℕ) : scalarBits - 1 - j < scalarBits := by
  simp only [scalarBits, Specs.Secp256k1.scalarBits]
  omega

def packBits (bits : Vector (Expression (F circomPrime)) scalarBits) :
    Var Emu (F circomPrime) :=
  Vector.ofFn fun k : Fin numLimbs =>
    Fin.foldl limbBits (fun acc t =>
      acc + bits[scalarBits - 1 - (limbBits * k.val + t.val)]'(bitIndex_lt _)
        * (((2 ^ t.val : ℕ) : F circomPrime) : Expression (F circomPrime)))
      0

def packed (bits : Vector (F circomPrime) scalarBits) : Emu (F circomPrime) :=
  Vector.ofFn fun k : Fin numLimbs =>
    ∑ t : Fin limbBits,
      bits[scalarBits - 1 - (limbBits * k.val + t.val)]'(bitIndex_lt _)
        * ((2 ^ t.val : ℕ) : F circomPrime)

theorem eval_packBits (env : Environment (F circomPrime))
    (bits : Vector (Expression (F circomPrime)) scalarBits) :
    Vector.map (Expression.eval env) (packBits bits) =
      packed (Vector.map (Expression.eval env) bits) := by
  apply Vector.ext
  intro k hk
  rw [Vector.getElem_map]
  simp only [packBits, packed, Vector.getElem_ofFn]
  rw [ToBytes.eval_foldl_add]
  apply Finset.sum_congr rfl
  intro t _
  simp only [Expression.eval, Vector.getElem_map]

theorem packed_getElem_val (bits : Vector (F circomPrime) scalarBits)
    (hbits : ∀ i : Fin scalarBits, IsBool bits[i])
    (k : ℕ) (hk : k < numLimbs) :
    ((packed bits)[k]'hk).val =
      ∑ t ∈ Finset.range limbBits,
        (bits[scalarBits - 1 - (limbBits * k + t)]'(bitIndex_lt _)).val * 2 ^ t := by
  have hs_lt : (∑ t ∈ Finset.range limbBits,
      (bits[scalarBits - 1 - (limbBits * k + t)]'(bitIndex_lt _)).val * 2 ^ t)
      < 2 ^ limbBits := by
    have h := sum_lt_pow (B := 1) (n := limbBits)
      (fun t : Fin limbBits =>
        (bits[scalarBits - 1 - (limbBits * k + t.val)]'(bitIndex_lt _)).val)
      (fun t => IsBool.val_lt_two
        (hbits (⟨scalarBits - 1 - (limbBits * k + t.val), bitIndex_lt _⟩ :
          Fin scalarBits)))
    calc
      (∑ t ∈ Finset.range limbBits,
          (bits[scalarBits - 1 - (limbBits * k + t)]'(bitIndex_lt _)).val * 2 ^ t) =
          ∑ t : Fin limbBits,
              (bits[scalarBits - 1 - (limbBits * k + t.val)]'(bitIndex_lt _)).val *
              2 ^ (1 * t.val) := by
            rw [← Fin.sum_univ_eq_sum_range
              (fun t =>
                (bits[scalarBits - 1 - (limbBits * k + t)]'(bitIndex_lt _)).val *
                  2 ^ t) limbBits]
            simp
      _ < 2 ^ (1 * limbBits) := h
      _ = 2 ^ limbBits := by simp
  have hcast : (packed bits)[k]'hk =
      ((∑ t ∈ Finset.range limbBits,
        (bits[scalarBits - 1 - (limbBits * k + t)]'(bitIndex_lt _)).val * 2 ^ t : ℕ) :
          F circomPrime) := by
    rw [packed, Vector.getElem_ofFn,
      ← Fin.sum_univ_eq_sum_range
        (fun t =>
          (bits[scalarBits - 1 - (limbBits * k + t)]'(bitIndex_lt _)).val * 2 ^ t)
        limbBits,
      Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro t _
    rw [Nat.cast_mul, ZMod.natCast_zmod_val]
  rw [hcast, ZMod.val_natCast_of_lt (lt_trans hs_lt (by decide : 2 ^ limbBits < circomPrime))]

theorem packed_normalized (bits : Vector (F circomPrime) scalarBits)
    (hbits : ∀ i : Fin scalarBits, IsBool bits[i]) :
    (packed bits).Normalized limbBits := by
  intro k
  rw [Fin.getElem_fin, packed_getElem_val bits hbits k.val k.isLt]
  have h := sum_lt_pow (B := 1) (n := limbBits)
    (fun t : Fin limbBits =>
      (bits[scalarBits - 1 - (limbBits * k.val + t.val)]'(bitIndex_lt _)).val)
    (fun t => IsBool.val_lt_two
      (hbits (⟨scalarBits - 1 - (limbBits * k.val + t.val), bitIndex_lt _⟩ :
        Fin scalarBits)))
  calc
    (∑ t ∈ Finset.range limbBits,
        (bits[scalarBits - 1 - (limbBits * k.val + t)]'(bitIndex_lt _)).val * 2 ^ t) =
        ∑ t : Fin limbBits,
          (bits[scalarBits - 1 - (limbBits * k.val + t.val)]'(bitIndex_lt _)).val *
            2 ^ (1 * t.val) := by
          rw [← Fin.sum_univ_eq_sum_range
            (fun t =>
              (bits[scalarBits - 1 - (limbBits * k.val + t)]'(bitIndex_lt _)).val *
                2 ^ t) limbBits]
          simp
    _ < 2 ^ (1 * limbBits) := h
    _ = 2 ^ limbBits := by simp

private lemma vector_foldl_toList {α β : Type} {m : ℕ} (v : Vector α m)
    (g : β → α → β) (init : β) : v.foldl g init = v.toList.foldl g init := by
  cases v
  simp [Vector.foldl, Array.foldl_toList]

lemma foldl_base2_eq_fromLimbs (l : List ℕ) :
    l.foldl (fun acc x => 2 * acc + x) 0 = fromLimbs 1 l.reverse := by
  rw [fromLimbs, List.foldr_reverse]
  congr 1
  funext acc x
  norm_num [Nat.add_comm, Nat.mul_comm]

private theorem scalarOfBitsNat_eq_le_sum (bits : Vector ℕ scalarBits) :
    Specs.ShortWeierstrass.scalarOfBits bits =
      ∑ j ∈ Finset.range scalarBits,
        bits[scalarBits - 1 - j]'(bitIndex_lt _) * 2 ^ j := by
  rw [Specs.ShortWeierstrass.scalarOfBits, vector_foldl_toList,
    foldl_base2_eq_fromLimbs, fromLimbs_eq_sum,
    ← Fin.sum_univ_eq_sum_range
      (fun j => bits[scalarBits - 1 - j]'(bitIndex_lt _) * 2 ^ j) scalarBits]
  have hlen : bits.toList.reverse.length = scalarBits := by simp
  rw [← Fin.sum_congr'
    (fun j : Fin scalarBits =>
      bits[scalarBits - 1 - j.val]'(bitIndex_lt _) * 2 ^ j.val) hlen]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Fin.val_cast, Fin.getElem_fin]
  congr 1
  rw [List.getElem_reverse, Vector.getElem_toList]
  simp only [Vector.length_toList]
  simp

theorem scalarOfBits_eq_le_sum (bits : Vector (F circomPrime) scalarBits) :
    Specs.ShortWeierstrass.scalarOfBits (bits.map ZMod.val) =
      ∑ j ∈ Finset.range scalarBits,
        (bits[scalarBits - 1 - j]'(bitIndex_lt _)).val * 2 ^ j := by
  rw [scalarOfBitsNat_eq_le_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Vector.getElem_map]
  rfl

theorem packed_value (bits : Vector (F circomPrime) scalarBits)
    (hbits : ∀ i : Fin scalarBits, IsBool bits[i]) :
    BigInt.value limbBits (packed bits) =
      Specs.ShortWeierstrass.scalarOfBits (bits.map ZMod.val) := by
  rw [scalarOfBits_eq_le_sum, BigInt.value_eq_sum]
  calc
    (∑ k : Fin numLimbs, ((packed bits)[k]).val * 2 ^ (limbBits * k.val)) =
        ∑ k ∈ Finset.range numLimbs,
          (∑ t ∈ Finset.range limbBits,
            (bits[scalarBits - 1 - (limbBits * k + t)]'(bitIndex_lt _)).val * 2 ^ t) *
              2 ^ (1 * limbBits * k) := by
      rw [← Fin.sum_univ_eq_sum_range
        (fun k =>
          (∑ t ∈ Finset.range limbBits,
            (bits[scalarBits - 1 - (limbBits * k + t)]'(bitIndex_lt _)).val * 2 ^ t) *
              2 ^ (1 * limbBits * k)) numLimbs]
      apply Finset.sum_congr rfl
      intro k _
      rw [Fin.getElem_fin, packed_getElem_val bits hbits k.val k.isLt]
      simp only [limbBits]
    _ = ∑ j ∈ Finset.range (numLimbs * limbBits),
        (bits[scalarBits - 1 - j]'(bitIndex_lt _)).val * 2 ^ (1 * j) :=
      (ToBytes.sum_regroup 1 limbBits
        (fun j => (bits[scalarBits - 1 - j]'(bitIndex_lt _)).val) numLimbs).symm
    _ = ∑ j ∈ Finset.range scalarBits,
        (bits[scalarBits - 1 - j]'(bitIndex_lt _)).val * 2 ^ j := by
      simp only [numLimbs, limbBits, scalarBits, Specs.Secp256k1.scalarBits,
        Nat.one_mul]

def scalarValue (input : Inputs (F circomPrime)) : ℕ :=
  Specs.ShortWeierstrass.scalarOfBits (input.bits.map ZMod.val)

/-- The packed 256-bit scalar is already a normalized four-limb representative.
The downstream relation is modulo `scalarOrder`, so explicitly witnessing the
canonical remainder and proving the integer quotient relation is unnecessary:
`packBits input.bits` has exactly the required residue. -/
def main (input : Var Inputs (F circomPrime)) :
    Circuit (F circomPrime) (Var Emu (F circomPrime)) :=
  pure (packBits input.bits)

instance elaborated : ElaboratedCircuit (F circomPrime) Inputs Emu main := by
  elaborate_circuit

def Assumptions (input : Inputs (F circomPrime)) : Prop :=
  ∀ i : Fin scalarBits, IsBool input.bits[i]

def Spec (input : Inputs (F circomPrime)) (out : Emu (F circomPrime)) : Prop :=
  out.Normalized limbBits ∧
  BigInt.value limbBits out % scalarOrder = scalarValue input % scalarOrder

theorem soundness :
    Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start
  have hout : Vector.map (Expression.eval env) (packBits input_var_bits) =
      packed input_bits := by
    rw [eval_packBits, h_input]
  rw [hout]
  exact ⟨packed_normalized input_bits h_assumptions,
    congrArg (fun x : ℕ => x % scalarOrder) (packed_value input_bits h_assumptions)⟩

theorem completeness : Completeness (F circomPrime) main Assumptions := by
  circuit_proof_start

def circuit : FormalCircuit (F circomPrime) Inputs Emu where
  main
  elaborated
  Assumptions
  Spec
  soundness
  completeness

theorem affineW_packBits (bits : Vector (Expression (F circomPrime)) scalarBits)
    (hbits : AffineW bits) : AffineW (packBits bits) := by
  intro k hk
  unfold packBits
  rw [Vector.getElem_ofFn]
  refine affine_finFoldl' _ _ Affine.zero fun acc t hacc => ?_
  exact Affine.add hacc (Affine.mul_deg0
    (hbits _ (bitIndex_lt _)) (degree_const _))

theorem costIs_main (input : Var Inputs (F circomPrime)) :
    CostIs (main input) Count.zero := by
  unfold main
  exact CostIs.pure _

theorem isR1CS_main (input : Var Inputs (F circomPrime))
    (_hbits : AffineW input.bits) : IsR1CSCirc (main input) := by
  unfold main
  exact IsR1CSCirc.pure _

theorem computableWitnesses : circuit.base.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition
      input env env') ((main input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main
  simp only [Challenge.Utils.ComputableWitnessLemmas.Circuit.pure_structuralComputableWitnesses_iff]

end Solution.Secp256k1ScalarMul.GLV.ScalarReduce
