import Solution.Secp256k1ScalarMul.ValidP
import Solution.Secp256k1ScalarMul.ToBytes

namespace Solution.Secp256k1ScalarMul
namespace ValidPBytes

open Utils.Bits
open ValidP

/-- Pack one little-endian byte from the four limb bit vectors. -/
def byteFromBits (b0 b1 b2 b3 : Var (fields limbBits) (F circomPrime))
    (t : Fin coordBytes) : Expression (F circomPrime) :=
  Fin.foldl 8 (fun acc j =>
    let k := 8 * (t.val % bytesPerLimb) + j.val
    let bit := if t.val < 8 then b0[k]'(by
        have hm : t.val % 8 < 8 := Nat.mod_lt _ (by decide)
        change 8 * (t.val % 8) + j.val < 64
        omega)
      else if t.val < 16 then b1[k]'(by
        have hm : t.val % 8 < 8 := Nat.mod_lt _ (by decide)
        change 8 * (t.val % 8) + j.val < 64
        omega)
      else if t.val < 24 then b2[k]'(by
        have hm : t.val % 8 < 8 := Nat.mod_lt _ (by decide)
        change 8 * (t.val % 8) + j.val < 64
        omega)
      else b3[k]'(by
        have hm : t.val % 8 < 8 := Nat.mod_lt _ (by decide)
        change 8 * (t.val % 8) + j.val < 64
        omega)
    acc + bit * (((2 ^ j.val : ℕ) : F circomPrime) : Expression (F circomPrime))) 0

/-- `ValidP`, additionally exposing the already-proven coordinate bits as bytes.
The returned bytes are affine expressions, so this has exactly the same local
length and constraints as `ValidP.main`. -/
def main (x : Var Emu (F circomPrime)) :
    Circuit (F circomPrime) (Var (fields coordBytes) (F circomPrime)) := do
  let b0 ← ToBitsAffine.toBitsAffine 63 secpParams.hB x[0]
  let b1 ← ToBitsAffine.toBitsAffine 63 secpParams.hB x[1]
  let b2 ← ToBitsAffine.toBitsAffine 63 secpParams.hB x[2]
  let b3 ← ToBitsAffine.toBitsAffine 63 secpParams.hB x[3]
  ValidP.tail b0 b1 b2 b3
  return Vector.ofFn fun t => byteFromBits b0 b1 b2 b3 t

instance elaborated : ElaboratedCircuit (F circomPrime) Emu (fields coordBytes) main := by
  elaborate_circuit

def Assumptions (_x : Emu (F circomPrime)) (_data : ProverData (F circomPrime)) :
    Prop := True

def ProverAssumptions (x : Emu (F circomPrime))
    (_data : ProverData (F circomPrime)) (_hint : ProverHint (F circomPrime)) :
    Prop := Fe.Valid x

def Spec (x : Emu (F circomPrime)) (bytes : fields coordBytes (F circomPrime))
    (_data : ProverData (F circomPrime)) : Prop :=
  Fe.Valid x ∧ ToBytes.Spec x bytes

def ProverSpec (x : Emu (F circomPrime))
    (bytes : fields coordBytes (F circomPrime)) (_hint : ProverHint (F circomPrime)) :
    Prop := ToBytes.Spec x bytes

private def byteFromFieldBits
    (b0 b1 b2 b3 : Vector (F circomPrime) limbBits) (t : Fin coordBytes) :
    F circomPrime :=
  Fin.foldl 8 (fun acc j =>
    let k := 8 * (t.val % bytesPerLimb) + j.val
    let bit := if t.val < 8 then b0[k]'(by
        have hm : t.val % 8 < 8 := Nat.mod_lt _ (by decide)
        change 8 * (t.val % 8) + j.val < 64
        omega)
      else if t.val < 16 then b1[k]'(by
        have hm : t.val % 8 < 8 := Nat.mod_lt _ (by decide)
        change 8 * (t.val % 8) + j.val < 64
        omega)
      else if t.val < 24 then b2[k]'(by
        have hm : t.val % 8 < 8 := Nat.mod_lt _ (by decide)
        change 8 * (t.val % 8) + j.val < 64
        omega)
      else b3[k]'(by
        have hm : t.val % 8 < 8 := Nat.mod_lt _ (by decide)
        change 8 * (t.val % 8) + j.val < 64
        omega)
    acc + bit * ((2 ^ j.val : ℕ) : F circomPrime)) 0

lemma eval_byteFromBits (env : Environment (F circomPrime))
    (b0 b1 b2 b3 : Var (fields limbBits) (F circomPrime))
    (t : Fin coordBytes) :
    Expression.eval env (byteFromBits b0 b1 b2 b3 t) =
      byteFromFieldBits (Vector.map (Expression.eval env) b0)
        (Vector.map (Expression.eval env) b1)
        (Vector.map (Expression.eval env) b2)
        (Vector.map (Expression.eval env) b3) t := by
  unfold byteFromBits byteFromFieldBits
  rw [ToBytes.eval_foldl_add]
  simp only [Fin.foldl_to_sum, Expression.eval, Vector.getElem_map]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> rfl

private lemma fromBits_chunk (v : ℕ) (r : Fin 8) :
    fromBits (Vector.ofFn fun j : Fin 8 => (toBits 64 v)[8 * r.val + j.val]'(by
      have hr := r.isLt
      have hj := j.isLt
      omega)) = ToBytes.byteOfNat v r.val := by
  rw [show (Vector.ofFn fun j : Fin 8 => (toBits 64 v)[8 * r.val + j.val]'(by
        have hr := r.isLt
        have hj := j.isLt
        omega)) = toBits 8 (v / 2 ^ (8 * r.val)) by
      apply Vector.ext
      intro i hi
      simp only [Vector.getElem_ofFn, toBits, Vector.getElem_mapRange]
      rw [Nat.testBit_div_two_pow]
      rw [show 8 * r.val + i = i + 8 * r.val by omega]]
  rw [fromBits_toBits_mod]
  unfold ToBytes.byteOfNat
  norm_num

set_option maxHeartbeats 0 in
private lemma byteFromFieldBits_eq_byteOfNat (z : F circomPrime)
    (r : Fin bytesPerLimb) :
    byteFromFieldBits (fieldToBits 64 z) (fieldToBits 64 z)
      (fieldToBits 64 z) (fieldToBits 64 z) ⟨r.val, by
        have hr := r.isLt
        simp only [bytesPerLimb, coordBytes] at hr ⊢
        omega⟩ = ((ToBytes.byteOfNat z.val r.val : ℕ) : F circomPrime) := by
  rw [show byteFromFieldBits (fieldToBits 64 z) (fieldToBits 64 z)
      (fieldToBits 64 z) (fieldToBits 64 z) ⟨r.val, by
        have hr := r.isLt
        simp only [bytesPerLimb, coordBytes] at hr ⊢
        omega⟩ = fieldFromBits (Vector.ofFn fun j : Fin 8 =>
          (fieldToBits 64 z)[8 * r.val + j.val]'(by
            have hr := r.isLt
            have hj := j.isLt
            simp only [bytesPerLimb] at hr
            omega)) by
      rw [fieldFromBits_as_sum]
      unfold byteFromFieldBits
      simp only [Fin.foldl_to_sum, fieldToBits, Vector.getElem_map,
        Vector.getElem_ofFn]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [Finset.mem_univ, true_and] at hj
      rw [if_pos (by simpa only [bytesPerLimb] using r.isLt)]
      simp only [bytesPerLimb, Nat.mod_eq_of_lt r.isLt]
      push_cast
      rfl]
  unfold fieldFromBits fieldToBits
  simp only [Vector.getElem_map]
  rw [show Vector.map ZMod.val
      (Vector.ofFn fun j : Fin 8 =>
        ((toBits 64 z.val)[8 * r.val + j.val]'(by
          have hr := r.isLt
          have hj := j.isLt
          simp only [bytesPerLimb] at hr
          omega) : F circomPrime)) =
      Vector.ofFn (fun j : Fin 8 =>
        (toBits 64 z.val)[8 * r.val + j.val]'(by
          have hr := r.isLt
          have hj := j.isLt
          simp only [bytesPerLimb] at hr
          omega)) by
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_map, Vector.getElem_ofFn]
    have hidx : 8 * r.val + i < 64 := by
      have hr := r.isLt
      simp only [bytesPerLimb] at hr
      omega
    rcases (show (toBits 64 z.val)[8 * r.val + i]'hidx = 0 ∨
        (toBits 64 z.val)[8 * r.val + i]'hidx = 1 from by
      simp [toBits, Vector.getElem_mapRange]) with h | h <;> rw [h]
    · exact ZMod.val_zero
    · exact ZMod.val_natCast_of_lt (by decide : 1 < circomPrime)]
  change ((fromBits (Vector.ofFn fun j : Fin 8 =>
    (toBits 64 z.val)[8 * r.val + j.val]'(by
      have hr := r.isLt
      have hj := j.isLt
      simp only [bytesPerLimb] at hr
      omega)) : ℕ) : F circomPrime) = _
  rw [fromBits_chunk z.val ⟨r.val, by simpa only [bytesPerLimb] using r.isLt⟩]

private lemma byteFromFieldBits_selected
    (b0 b1 b2 b3 : F circomPrime) (t : Fin coordBytes) :
    byteFromFieldBits (fieldToBits 64 b0) (fieldToBits 64 b1)
      (fieldToBits 64 b2) (fieldToBits 64 b3) t =
      ((ToBytes.byteOfNat
        (if t.val < 8 then b0.val else if t.val < 16 then b1.val
          else if t.val < 24 then b2.val else b3.val)
        (t.val % 8) : ℕ) : F circomPrime) := by
  have hr : t.val % 8 < 8 := Nat.mod_lt _ (by decide)
  by_cases h0 : t.val < 8
  · simpa [byteFromFieldBits, h0, Nat.mod_eq_of_lt h0] using
      byteFromFieldBits_eq_byteOfNat b0 ⟨t.val, h0⟩
  · by_cases h1 : t.val < 16
    · simpa [byteFromFieldBits, h0, h1] using
        byteFromFieldBits_eq_byteOfNat b1 ⟨t.val % 8, hr⟩
    · by_cases h2 : t.val < 24
      · simpa [byteFromFieldBits, h0, h1, h2] using
          byteFromFieldBits_eq_byteOfNat b2 ⟨t.val % 8, hr⟩
      · simpa [byteFromFieldBits, h0, h1, h2] using
          byteFromFieldBits_eq_byteOfNat b3 ⟨t.val % 8, hr⟩

set_option maxHeartbeats 2000000 in
private lemma bytes_recompose (x : Emu (F circomPrime))
    (hn : BigInt.Normalized limbBits x)
    (bytes : Vector (F circomPrime) coordBytes)
    (hbyte : ∀ t : Fin coordBytes,
      bytes[t] = ((ToBytes.byteOfNat (x[t.val / 8]'(by
        have ht := t.isLt
        simp only [coordBytes, numLimbs] at ht ⊢
        omega)).val (t.val % 8) : ℕ) : F circomPrime)) :
    Limbs.fromLimbs 8 (List.map ZMod.val bytes.toList) =
      BigInt.value limbBits x := by
  rw [fromLimbs_eq_sum, BigInt.value_eq_sum]
  simp only [Fin.getElem_fin, List.getElem_map, Vector.getElem_toList]
  let bf : ℕ → ℕ := fun i =>
    if hi : i < coordBytes then (bytes[i]'hi).val else 0
  have hinner (k : ℕ) (hk4 : k < 4) :
      (∑ t ∈ Finset.range 8, bf (8 * k + t) * 2 ^ (8 * t)) =
        (x[k]'hk4).val := by
    calc
      (∑ t ∈ Finset.range 8, bf (8 * k + t) * 2 ^ (8 * t)) =
          ∑ t ∈ Finset.range 8,
            ToBytes.byteOfNat (x[k]'hk4).val t * 2 ^ (8 * t) := by
        apply Finset.sum_congr rfl
        intro t ht
        have ht8 : t < 8 := Finset.mem_range.mp ht
        have hi : 8 * k + t < coordBytes := by simp only [coordBytes]; omega
        have hbval := congrArg ZMod.val (hbyte ⟨8 * k + t, hi⟩)
        simp only [Fin.getElem_fin] at hbval
        rw [show bf (8 * k + t) = (bytes[8 * k + t]'hi).val by simp [bf, hi],
          hbval, ZMod.val_natCast_of_lt]
        · unfold ToBytes.byteOfNat
          have hdiv : (8 * k + t) / 8 = k := by omega
          have hmod : (8 * k + t) % 8 = t := by omega
          simp only [hdiv, hmod]
        · unfold ToBytes.byteOfNat
          exact lt_trans (Nat.mod_lt _ (by norm_num : 0 < 256))
            (by decide : 256 < circomPrime)
      _ = (x[k]'hk4).val := by
        unfold ToBytes.byteOfNat
        have hlimb : (x[k]'hk4).val < 2 ^ 64 := by
          simpa only [limbBits] using hn ⟨k, hk4⟩
        have hlimbNum : (x[k]'hk4).val < 18446744073709551616 := by
          norm_num at hlimb ⊢
          exact hlimb
        have hsum := ToBytes.byteSum_eq_limb (x[k]'hk4).val 0
        norm_num at hsum
        rw [Nat.mod_eq_of_lt hlimbNum] at hsum
        exact hsum
  let envB : Environment (F circomPrime) :=
    { get := fun i => if hi : i < coordBytes then bytes[i]'hi else 0
      data := fun _ _ => #[] }
  have hbytes : ∀ i : Fin coordBytes, (envB.get i.val).val < 2 ^ 8 := by
    intro i
    rw [show envB.get i.val = bytes[i] by simp [envB]]
    rw [hbyte i, ZMod.val_natCast_of_lt]
    · unfold ToBytes.byteOfNat
      exact Nat.mod_lt _ (by norm_num)
    · unfold ToBytes.byteOfNat
      exact lt_trans (Nat.mod_lt _ (by norm_num : 0 < 256))
        (by decide : 256 < circomPrime)
  have hrows : ∀ k : Fin numLimbs,
      (∑ t : Fin bytesPerLimb,
          envB.get (bytesPerLimb * k.val + t.val) *
            ((2 ^ (8 * t.val) : ℕ) : F circomPrime)) =
        x[k.val]'k.isLt := by
    intro k
    have hnat := hinner k.val k.isLt
    have hcast := congrArg (fun z : ℕ => (z : F circomPrime)) hnat
    change ((∑ t ∈ Finset.range 8,
      bf (8 * k.val + t) * 2 ^ (8 * t) : ℕ) : F circomPrime) =
        ((x[k.val]'k.isLt).val : F circomPrime) at hcast
    rw [Nat.cast_sum] at hcast
    calc
      (∑ t : Fin bytesPerLimb,
          envB.get (bytesPerLimb * k.val + t.val) *
            ((2 ^ (8 * t.val) : ℕ) : F circomPrime)) =
          ∑ t ∈ Finset.range 8,
            ((bf (8 * k.val + t) * 2 ^ (8 * t) : ℕ) :
              F circomPrime) := by
        rw [show (∑ t : Fin bytesPerLimb,
            envB.get (bytesPerLimb * k.val + t.val) *
              ((2 ^ (8 * t.val) : ℕ) : F circomPrime)) =
            ∑ t ∈ Finset.range 8,
              envB.get (8 * k.val + t) *
                ((2 ^ (8 * t) : ℕ) : F circomPrime) by
          simpa only [bytesPerLimb] using
            Fin.sum_univ_eq_sum_range
              (fun t => envB.get (8 * k.val + t) *
                ((2 ^ (8 * t) : ℕ) : F circomPrime)) 8]
        apply Finset.sum_congr rfl
        intro t ht
        have ht8 : t < 8 := Finset.mem_range.mp ht
        have hk4 : k.val < 4 := by
          simpa only [numLimbs] using k.isLt
        have hi : 8 * k.val + t < coordBytes := by
          simp only [coordBytes]
          omega
        rw [show envB.get (8 * k.val + t) = bytes[8 * k.val + t]'hi by
          simp only [envB, hi, ↓reduceDIte]]
        rw [show bf (8 * k.val + t) = (bytes[8 * k.val + t]'hi).val by
          simp only [bf, hi, ↓reduceDIte]]
        rw [Nat.cast_mul, ZMod.natCast_zmod_val]
      _ = ((x[k.val]'k.isLt).val : F circomPrime) := hcast
      _ = x[k.val]'k.isLt := ZMod.natCast_zmod_val _
  have hcore := ToBytes.soundness_core envB 0 x
    (fun i => by simpa using hbytes i)
    (fun k => by simpa using hrows k)
  have hout :
      Vector.map (Expression.eval envB)
        (Vector.mapRange coordBytes fun i =>
          var (F := F circomPrime) { index := 0 + i }) = bytes := by
    apply Vector.ext
    intro i hi
    simp [envB, circuit_norm, hi]
  rw [hout] at hcore
  simpa only [fromLimbs_eq_sum, BigInt.value_eq_sum, Fin.getElem_fin,
    List.getElem_map, Vector.getElem_toList] using hcore

private lemma bytes_of_fieldToBits_spec (x : Emu (F circomPrime))
    (hn : BigInt.Normalized limbBits x) :
    ToBytes.Spec x (Vector.ofFn fun t => byteFromFieldBits
      (fieldToBits 64 x[0]) (fieldToBits 64 x[1])
      (fieldToBits 64 x[2]) (fieldToBits 64 x[3]) t) := by
  let bytes : Vector (F circomPrime) coordBytes := Vector.ofFn fun t =>
    byteFromFieldBits (fieldToBits 64 x[0]) (fieldToBits 64 x[1])
      (fieldToBits 64 x[2]) (fieldToBits 64 x[3]) t
  have hbyte : ∀ t : Fin coordBytes,
      bytes[t] = ((ToBytes.byteOfNat (x[t.val / 8]'(by
        have ht := t.isLt
        simp only [coordBytes, numLimbs] at ht ⊢
        omega)).val (t.val % 8) : ℕ) : F circomPrime) := by
    intro t
    rw [show bytes[t] = byteFromFieldBits
      (fieldToBits 64 x[0]) (fieldToBits 64 x[1])
      (fieldToBits 64 x[2]) (fieldToBits 64 x[3]) t by simp [bytes]]
    rw [byteFromFieldBits_selected]
    congr 2
    split_ifs with h0 h1 h2
    · have hd : t.val / 8 = 0 := Nat.div_eq_of_lt h0
      simpa [hd]
    · have hd : t.val / 8 = 1 := by omega
      simpa [hd]
    · have hd : t.val / 8 = 2 := by omega
      simpa [hd]
    · have ht := t.isLt
      simp only [coordBytes] at ht
      have hd : t.val / 8 = 3 := by omega
      simpa [hd]
  refine ⟨?_, ?_⟩
  · intro t
    change (bytes[t]).val < 256
    rw [hbyte t, ZMod.val_natCast_of_lt (by
      unfold ToBytes.byteOfNat
      exact lt_trans (Nat.mod_lt _ (by norm_num : 0 < 256)) (by decide : 256 < circomPrime))]
    unfold ToBytes.byteOfNat
    exact Nat.mod_lt _ (by norm_num)
  · exact bytes_recompose x hn bytes hbyte

set_option maxHeartbeats 4000000 in
theorem soundness :
    GeneralFormalCircuit.Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [ValidP.tail, ToBitsAffine.toBitsAffine, ToBitsAffine.main,
    Gadgets.IsZeroField.circuit,
    Gadgets.IsZeroField.Assumptions, Gadgets.IsZeroField.Spec]
  obtain ⟨⟨hn0, hb0⟩, ⟨hn1, hb1⟩, ⟨hn2, hb2⟩, ⟨hn3, hb3⟩,
    htopEq, hmidEq, hlowEq, hu, hv, hmerged⟩ := h_holds
  have hx : ∀ (i : ℕ) (hi : i < 4), Expression.eval env input_var[i] = input[i] := by
    intro i hi
    rw [← h_input, Vector.getElem_map]
  rw [hx 0 (by omega)] at hn0 hb0
  rw [hx 1 (by omega)] at hn1 hb1
  rw [hx 2 (by omega)] at hn2 hb2
  rw [hx 3 (by omega)] at hn3 hb3
  have hn : BigInt.Normalized limbBits input := by
    intro i
    fin_cases i <;> assumption
  rw [eval_ds (by decide) env _ input[0] hb0,
    eval_ds (by decide) env _ input[1] hb1,
    eval_ds (by decide) env _ input[2] hb2,
    eval_ds (by decide) env _ input[3] hb3] at htopEq
  rw [eval_ds (by decide) env _ input[0] hb0] at hmidEq hlowEq
  simp only [top_count_cast_zero_iff] at htopEq
  change _ = if topDC input = 0 then 1 else 0 at htopEq
  simp only [mid_cast_zero_iff input] at hmidEq
  simp only [low_cast_zero_iff input] at hlowEq
  have hb0val : ∀ (i : ℕ) (hi : i < 63),
      env.get (i₀ + i) = if input[0].val.testBit i then 1 else 0 := by
    exact fun i hi => push_eval_bit env i₀ _ input[0] hb0 i hi
  have hu' : env.get (i₀ + 63 + 63 + 63 + 63 + 2 + 2 + 2) =
      bitField (input[0].val.testBit 5) *
        (bitField (input[0].val.testBit 4) +
          env.get (i₀ + 63 + 63 + 63 + 63 + 2 + 2 + 1)) := by
    rw [bitField, ← hb0val 5 (by omega), bitField, ← hb0val 4 (by omega)]
    exact hu
  have hv' : env.get (i₀ + 63 + 63 + 63 + 63 + 2 + 2 + 2 + 1) =
      env.get (i₀ + 63 + 63 + 63 + 63 + 2 + 1) *
        (bitField (input[0].val.testBit 9) + bitField (input[0].val.testBit 8) +
          bitField (input[0].val.testBit 7) + bitField (input[0].val.testBit 6) +
          env.get (i₀ + 63 + 63 + 63 + 63 + 2 + 2 + 2)) := by
    rw [bitField, ← hb0val 9 (by omega), bitField, ← hb0val 8 (by omega),
      bitField, ← hb0val 7 (by omega), bitField, ← hb0val 6 (by omega)]
    exact hv
  have hmerged' : env.get (i₀ + 63 + 63 + 63 + 63 + 1) *
      (bitField (input[0].val.testBit 32) +
        env.get (i₀ + 63 + 63 + 63 + 63 + 2 + 2 + 2 + 1)) = 0 := by
    rw [bitField, ← hb0val 32 (by omega)]
    exact hmerged
  have hpatt : Pattern input :=
    pattern_of_merged input htopEq hmidEq hlowEq hu' hv' hmerged'
  refine ⟨⟨hn, (pattern_iff_lt input hn).mp hpatt⟩, ?_⟩
  have hb0' :
      Vector.map (Expression.eval env)
          (ToBitsAffine.main 63 input_var[0] i₀).1 =
        fieldToBits 64 input[0] := by
    simpa only [ToBitsAffine.main, circuit_norm] using hb0
  have hb1' :
      Vector.map (Expression.eval env)
          (ToBitsAffine.main 63 input_var[1] (i₀ + 63)).1 =
        fieldToBits 64 input[1] := by
    simpa only [ToBitsAffine.main, circuit_norm] using hb1
  have hb2' :
      Vector.map (Expression.eval env)
          (ToBitsAffine.main 63 input_var[2] (i₀ + 63 + 63)).1 =
        fieldToBits 64 input[2] := by
    simpa only [ToBitsAffine.main, circuit_norm] using hb2
  have hb3' :
      Vector.map (Expression.eval env)
          (ToBitsAffine.main 63 input_var[3] (i₀ + 63 + 63 + 63)).1 =
        fieldToBits 64 input[3] := by
    simpa only [ToBitsAffine.main, circuit_norm] using hb3
  have hout :
      Vector.map (Expression.eval env)
        (Vector.ofFn fun t => byteFromBits
          (ToBitsAffine.main 63 input_var[0] i₀).1
          (ToBitsAffine.main 63 input_var[1] (i₀ + 63)).1
          (ToBitsAffine.main 63 input_var[2] (i₀ + 63 + 63)).1
          (ToBitsAffine.main 63 input_var[3] (i₀ + 63 + 63 + 63)).1 t) =
        Vector.ofFn fun t => byteFromFieldBits
          (fieldToBits 64 input[0]) (fieldToBits 64 input[1])
          (fieldToBits 64 input[2]) (fieldToBits 64 input[3]) t := by
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_map, Vector.getElem_ofFn]
    rw [eval_byteFromBits, hb0', hb1', hb2', hb3']
  change ToBytes.Spec input
    (Vector.map (Expression.eval env)
      (Vector.ofFn fun t => byteFromBits
        (ToBitsAffine.main 63 input_var[0] i₀).1
        (ToBitsAffine.main 63 input_var[1] (i₀ + 63)).1
        (ToBitsAffine.main 63 input_var[2] (i₀ + 63 + 63)).1
        (ToBitsAffine.main 63 input_var[3] (i₀ + 63 + 63 + 63)).1 t))
  rw [hout]
  exact bytes_of_fieldToBits_spec input hn

set_option maxHeartbeats 0 in
theorem completeness :
    GeneralFormalCircuit.Completeness (F circomPrime) main
      ProverAssumptions ProverSpec := by
  circuit_proof_start [ValidP.tail, ToBitsAffine.toBitsAffine, ToBitsAffine.main,
    Gadgets.IsZeroField.circuit,
    Gadgets.IsZeroField.Assumptions, Gadgets.IsZeroField.Spec]
  obtain ⟨hb0gen, hb1gen, hb2gen, hb3gen, htopEq, hmidEq, hlowEq, hu, hv⟩ := h_env
  have hx : ∀ (i : ℕ) (hi : i < 4),
      Expression.eval env.toEnvironment input_var[i] = input[i] := by
    intro i hi
    rw [← h_input, Vector.getElem_map]
  have hn := h_assumptions.1
  have hn0 : (Expression.eval env.toEnvironment input_var[0]).val < 2 ^ limbBits := by
    rw [hx 0 (by omega)]
    exact hn 0
  have hn1 : (Expression.eval env.toEnvironment input_var[1]).val < 2 ^ limbBits := by
    rw [hx 1 (by omega)]
    exact hn 1
  have hn2 : (Expression.eval env.toEnvironment input_var[2]).val < 2 ^ limbBits := by
    rw [hx 2 (by omega)]
    exact hn 2
  have hn3 : (Expression.eval env.toEnvironment input_var[3]).val < 2 ^ limbBits := by
    rw [hx 3 (by omega)]
    exact hn 3
  obtain ⟨-, hb0⟩ := hb0gen hn0
  obtain ⟨-, hb1⟩ := hb1gen hn1
  obtain ⟨-, hb2⟩ := hb2gen hn2
  obtain ⟨-, hb3⟩ := hb3gen hn3
  rw [hx 0 (by omega)] at hb0
  rw [hx 1 (by omega)] at hb1
  rw [hx 2 (by omega)] at hb2
  rw [hx 3 (by omega)] at hb3
  rw [eval_ds (by decide) env.toEnvironment _ input[0] hb0,
    eval_ds (by decide) env.toEnvironment _ input[1] hb1,
    eval_ds (by decide) env.toEnvironment _ input[2] hb2,
    eval_ds (by decide) env.toEnvironment _ input[3] hb3] at htopEq
  rw [eval_ds (by decide) env.toEnvironment _ input[0] hb0] at hmidEq hlowEq
  simp only [top_count_cast_zero_iff] at htopEq
  change _ = if topDC input = 0 then 1 else 0 at htopEq
  simp only [mid_cast_zero_iff input] at hmidEq
  simp only [low_cast_zero_iff input] at hlowEq
  have hb0val : ∀ (i : ℕ) (hi : i < 63),
      env.get (i₀ + i) = if input[0].val.testBit i then 1 else 0 := by
    exact fun i hi => push_eval_bit env.toEnvironment i₀ _ input[0] hb0 i hi
  have hu' : env.get (i₀ + 63 + 63 + 63 + 63 + 2 + 2 + 2) =
      bitField (input[0].val.testBit 5) *
        (bitField (input[0].val.testBit 4) +
          env.get (i₀ + 63 + 63 + 63 + 63 + 2 + 2 + 1)) := by
    rw [bitField, ← hb0val 5 (by omega), bitField, ← hb0val 4 (by omega)]
    exact hu
  have hv' : env.get (i₀ + 63 + 63 + 63 + 63 + 2 + 2 + 2 + 1) =
      env.get (i₀ + 63 + 63 + 63 + 63 + 2 + 1) *
        (bitField (input[0].val.testBit 9) + bitField (input[0].val.testBit 8) +
          bitField (input[0].val.testBit 7) + bitField (input[0].val.testBit 6) +
          env.get (i₀ + 63 + 63 + 63 + 63 + 2 + 2 + 2)) := by
    rw [bitField, ← hb0val 9 (by omega), bitField, ← hb0val 8 (by omega),
      bitField, ← hb0val 7 (by omega), bitField, ← hb0val 6 (by omega)]
    exact hv
  have hpatt : Pattern input := (pattern_iff_lt input hn).mpr h_assumptions.2
  have hmerged := merged_of_pattern input htopEq hmidEq hlowEq hu' hv' hpatt
  rw [bitField, ← hb0val 32 (by omega)] at hmerged
  refine ⟨⟨hn0, hn1, hn2, hn3, hu, hv, hmerged⟩, ?_⟩
  have hb0' :
      Vector.map (Expression.eval env.toEnvironment)
          (ToBitsAffine.main 63 input_var[0] i₀).1 =
        fieldToBits 64 input[0] := by
    simpa only [ToBitsAffine.main, circuit_norm] using hb0
  have hb1' :
      Vector.map (Expression.eval env.toEnvironment)
          (ToBitsAffine.main 63 input_var[1] (i₀ + 63)).1 =
        fieldToBits 64 input[1] := by
    simpa only [ToBitsAffine.main, circuit_norm] using hb1
  have hb2' :
      Vector.map (Expression.eval env.toEnvironment)
          (ToBitsAffine.main 63 input_var[2] (i₀ + 63 + 63)).1 =
        fieldToBits 64 input[2] := by
    simpa only [ToBitsAffine.main, circuit_norm] using hb2
  have hb3' :
      Vector.map (Expression.eval env.toEnvironment)
          (ToBitsAffine.main 63 input_var[3] (i₀ + 63 + 63 + 63)).1 =
        fieldToBits 64 input[3] := by
    simpa only [ToBitsAffine.main, circuit_norm] using hb3
  have hout :
      Vector.map (Expression.eval env.toEnvironment)
        (Vector.ofFn fun t => byteFromBits
          (ToBitsAffine.main 63 input_var[0] i₀).1
          (ToBitsAffine.main 63 input_var[1] (i₀ + 63)).1
          (ToBitsAffine.main 63 input_var[2] (i₀ + 63 + 63)).1
          (ToBitsAffine.main 63 input_var[3] (i₀ + 63 + 63 + 63)).1 t) =
        Vector.ofFn fun t => byteFromFieldBits
          (fieldToBits 64 input[0]) (fieldToBits 64 input[1])
          (fieldToBits 64 input[2]) (fieldToBits 64 input[3]) t := by
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_map, Vector.getElem_ofFn]
    rw [eval_byteFromBits, hb0', hb1', hb2', hb3']
  change ToBytes.Spec input
    (Vector.map (Expression.eval env.toEnvironment)
      (Vector.ofFn fun t => byteFromBits
        (ToBitsAffine.main 63 input_var[0] i₀).1
        (ToBitsAffine.main 63 input_var[1] (i₀ + 63)).1
        (ToBitsAffine.main 63 input_var[2] (i₀ + 63 + 63)).1
        (ToBitsAffine.main 63 input_var[3] (i₀ + 63 + 63 + 63)).1 t))
  rw [hout]
  exact bytes_of_fieldToBits_spec input hn
/-- The 63 witnessed bits of one limb, together with the affine top bit, are
stable under environments that agree below the end of the range check, provided
the limb itself is. -/
lemma toBits63_map_eval_eq (xe : Expression (F circomPrime)) (o : ℕ)
    {e e' : ProverEnvironment (F circomPrime)} {k : ℕ}
    (hag : e.AgreesBelow k e') (hk : o + 63 ≤ k)
    (hx : Expression.eval e.toEnvironment xe = Expression.eval e'.toEnvironment xe) :
    Vector.map (Expression.eval e.toEnvironment) (ToBitsAffine.main 63 xe o).1
      = Vector.map (Expression.eval e'.toEnvironment) (ToBitsAffine.main 63 xe o).1 := by
  have hvar : ∀ i, i < 63 →
      e.get (o + i) = e'.get (o + i) := fun i hi => hag (o + i) (by omega)
  have hlow : Vector.map (Expression.eval e.toEnvironment)
        (Vector.mapRange 63 fun i => var (F := F circomPrime) { index := o + i })
      = Vector.map (Expression.eval e'.toEnvironment)
        (Vector.mapRange 63 fun i => var (F := F circomPrime) { index := o + i }) := by
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_map, Vector.getElem_mapRange, Expression.eval]
    exact hvar i hi
  simp only [ToBitsAffine.main, circuit_norm]
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_map]
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
  · simp only [Vector.getElem_push_lt h, Vector.getElem_mapRange, Expression.eval]
    exact hvar i h
  · subst h
    simp only [Vector.getElem_push_eq, Expression.eval]
    simp only [fieldFromBits_eval, hlow, hx]

/-- The byte vector produced by `ValidPBytes` depends only on the environment
below the end of its own witness block, and on the input limbs. -/
lemma output_map_eval_eq (x : Var Emu (F circomPrime)) (o : ℕ)
    {e e' : ProverEnvironment (F circomPrime)} {k : ℕ}
    (hag : e.AgreesBelow k e') (hk : o + 252 ≤ k)
    (hx : Vector.map (Expression.eval e.toEnvironment) x
        = Vector.map (Expression.eval e'.toEnvironment) x) :
    Vector.map (Expression.eval e.toEnvironment) ((main x).output o)
      = Vector.map (Expression.eval e'.toEnvironment) ((main x).output o) := by
  have hxi : ∀ (i : ℕ) (hi : i < 4), Expression.eval e.toEnvironment (x[i]'hi)
      = Expression.eval e'.toEnvironment (x[i]'hi) := by
    intro i hi
    have h := congrArg (fun v : Emu (F circomPrime) => v[i]'hi) hx
    simpa only [Vector.getElem_map] using h
  have h0 := toBits63_map_eval_eq x[0] o hag (by omega) (hxi 0 (by omega))
  have h1 := toBits63_map_eval_eq x[1] (o + 63) hag (by omega) (hxi 1 (by omega))
  have h2 := toBits63_map_eval_eq x[2] (o + 63 + 63) hag (by omega) (hxi 2 (by omega))
  have h3 := toBits63_map_eval_eq x[3] (o + 63 + 63 + 63) hag (by omega) (hxi 3 (by omega))
  simp only [main, ToBitsAffine.toBitsAffine, ToBitsAffine.main, circuit_norm]
  apply Vector.ext
  intro t ht
  simp only [Vector.getElem_map, Vector.getElem_ofFn]
  rw [eval_byteFromBits, eval_byteFromBits]
  simp only [ToBitsAffine.main, circuit_norm] at h0 h1 h2 h3
  rw [h0, h1, h2, h3]

def circuit : GeneralFormalCircuit (F circomPrime) Emu (fields coordBytes) where
  main := main
  elaborated := elaborated
  Assumptions := Assumptions
  Spec := Spec
  ProverAssumptions := ProverAssumptions
  ProverSpec := ProverSpec
  soundness := soundness
  completeness := completeness

theorem computableWitnesses : circuit.base.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition
      input env env')
    ((main input).operations offset)
  simpa only [main, ValidP.main, Circuit.operations] using
    ValidP.computableWitnesses offset input env env'

theorem computableWitness : ∀ n input,
    ProverEnvironment.OnlyAccessedBelow n
      (fun env : ProverEnvironment (F circomPrime) => eval env input) →
    Circuit.ComputableWitnesses (main input) n :=
  Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnesses_implies
    (circuit := circuit.base) computableWitnesses

end ValidPBytes
end Solution.Secp256k1ScalarMul
