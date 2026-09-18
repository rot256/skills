import Solution.Secp256k1ScalarMul.GLVMSM
import Solution.Secp256k1ScalarMul.SignedCoeff
import Solution.Secp256k1ScalarMul.Phi
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.List.Indexes

namespace Solution.Secp256k1ScalarMul.GLVMSMTheorems

open Specs.ShortWeierstrass Specs.Secp256k1

private lemma vector_foldl_toList {α β : Type} {m : ℕ} (v : Vector α m)
    (g : β → α → β) (init : β) : v.foldl g init = v.toList.foldl g init := by
  cases v
  simp [Vector.foldl, Array.foldl_toList]

lemma scalarOfBits_reverse_eq_ofDigits {n : ℕ} (bits : Vector ℕ n) :
    scalarOfBits bits.reverse = Nat.ofDigits 2 bits.toList := by
  unfold scalarOfBits
  rw [vector_foldl_toList, Vector.toList_reverse, List.foldl_reverse,
    Nat.ofDigits_eq_foldr]
  congr 1
  funext x y
  simp only [Nat.cast_id]
  omega

lemma fromBits_eq_ofDigits {n : ℕ} (bits : Vector ℕ n) :
    Utils.Bits.fromBits bits = Nat.ofDigits 2 bits.toList := by
  rw [Utils.Bits.fromBits, Fin.foldl_to_sum, Nat.ofDigits_eq_sum_mapIdx,
    List.mapIdx_eq_ofFn, List.sum_ofFn]
  let e : Fin n ≃ Fin bits.toList.length :=
    { toFun := fun i => ⟨i.val, by simpa using i.isLt⟩
      invFun := fun i => ⟨i.val, by simpa using i.isLt⟩
      left_inv := by intro i; apply Fin.ext; rfl
      right_inv := by intro i; apply Fin.ext; rfl }
  apply Finset.sum_equiv e
  · intro i
    simp
  · intro i _
    simp only [List.get_eq_getElem, Vector.getElem_toList]
    have hv : (e i).val = i.val := by dsimp [e]
    simp only [hv]

lemma scalarOfBits_reverse_eq_fromBits {n : ℕ} (bits : Vector ℕ n) :
    scalarOfBits bits.reverse = Utils.Bits.fromBits bits := by
  rw [scalarOfBits_reverse_eq_ofDigits, fromBits_eq_ofDigits]

lemma fieldFromBits_val_of_bool {n : ℕ} (bits : Vector (F circomPrime) n)
    (hbits : ∀ i : Fin n, IsBool bits[i]) (hn : 2 ^ n < circomPrime) :
    (Utils.Bits.fieldFromBits bits).val =
      Utils.Bits.fromBits (bits.map ZMod.val) := by
  unfold Utils.Bits.fieldFromBits
  rw [ZMod.val_natCast_of_lt]
  have hone : ((1 : F circomPrime).val) = 1 := by
    change (((1 : ℕ) : F circomPrime).val) = 1
    exact ZMod.val_natCast_of_lt (by decide)
  exact lt_trans (Utils.Bits.fromBits_lt _ fun i hi => by
    have hb := hbits ⟨i, hi⟩
    rw [Vector.getElem_map]
    rcases hb with h0 | h1
    · left
      simpa only [Fin.getElem_fin, ZMod.val_zero] using congrArg ZMod.val h0
    · right
      simpa only [Fin.getElem_fin, hone] using congrArg ZMod.val h1) hn

lemma magnitude_eq_fromBits {c : GLV.SignedCoeff (F circomPrime)}
    (hc : GLV.Valid c) :
    GLV.magnitude c = Utils.Bits.fromBits (c.bits.map ZMod.val) := by
  simp only [GLV.magnitude, GLV.lowBits_eq_self]
  exact fieldFromBits_val_of_bool c.bits hc.2 (by decide)

theorem scalarOfBits_coeff_eq_magnitude {c : GLV.SignedCoeff (F circomPrime)}
    (hc : GLV.Valid c) :
    scalarOfBits ((c.bits.map ZMod.val).reverse) = GLV.magnitude c := by
  rw [scalarOfBits_reverse_eq_fromBits, magnitude_eq_fromBits hc]

def bitList (m : Vector (F circomPrime) GLVMSM.coeffBits) : List ℕ :=
  (m.map ZMod.val).reverse.toList

def scanValue (m : Vector (F circomPrime) GLVMSM.coeffBits) (k : ℕ) : ℕ :=
  ((bitList m).take k).foldl (fun acc bit => 2 * acc + bit) 0

lemma bitList_length (m : Vector (F circomPrime) GLVMSM.coeffBits) :
    (bitList m).length = GLVMSM.coeffBits := by
  simp [bitList]

lemma bitList_getElem (m : Vector (F circomPrime) GLVMSM.coeffBits)
    (k : ℕ) (hk : k < GLVMSM.coeffBits) :
    (bitList m)[k]'(by simpa [bitList] using hk) =
      (m[GLVMSM.coeffBits - 1 - k]'(by
        simp only [GLVMSM.coeffBits] at hk ⊢
        omega)).val := by
  simp only [bitList, Vector.toList_reverse]
  rw [List.getElem_reverse]
  simp only [List.length_map, Vector.length_toList, Vector.getElem_toList,
    Vector.getElem_map]
  rfl

lemma scanValue_succ (m : Vector (F circomPrime) GLVMSM.coeffBits)
    (k : ℕ) (hk : k < GLVMSM.coeffBits) :
    scanValue m (k + 1) =
      2 * scanValue m k +
        (m[GLVMSM.coeffBits - 1 - k]'(by
          simp only [GLVMSM.coeffBits] at hk ⊢
          omega)).val := by
  unfold scanValue
  rw [List.take_succ, List.foldl_append]
  have hget : (bitList m)[k]? = some
      ((m[GLVMSM.coeffBits - 1 - k]'(by
        simp only [GLVMSM.coeffBits] at hk ⊢
        omega)).val) := by
    rw [List.getElem?_eq_getElem (by simpa [bitList_length] using hk)]
    congr
    exact bitList_getElem m k hk
  rw [hget]
  rfl

lemma scanValue_final (m : Vector (F circomPrime) GLVMSM.coeffBits) :
    scanValue m GLVMSM.coeffBits =
      scalarOfBits ((m.map ZMod.val).reverse) := by
  unfold scanValue scalarOfBits bitList
  rw [vector_foldl_toList]
  simp only [Vector.toList_reverse]
  have ht : List.take GLVMSM.coeffBits (m.map ZMod.val).toList.reverse =
      (m.map ZMod.val).toList.reverse :=
    (List.take_eq_self_iff _).mpr (by simp)
  rw [ht]

def pickW (b : Bool) (P : Bridge.W.Point) : Bridge.W.Point :=
  if b then P else 0

def subsetW (B : Fin 4 → Bridge.W.Point) (t : ℕ) : Bridge.W.Point :=
  (pickW (decide (t / 2 ^ 0 % 2 = 1)) (B 0) +
      pickW (decide (t / 2 ^ 1 % 2 = 1)) (B 1)) +
    (pickW (decide (t / 2 ^ 2 % 2 = 1)) (B 2) +
      pickW (decide (t / 2 ^ 3 % 2 = 1)) (B 3))

def linComb (B : Fin 4 → Bridge.W.Point) (a0 a1 a2 a3 : ℕ) : Bridge.W.Point :=
  (a0 • B 0 + a1 • B 1) + (a2 • B 2 + a3 • B 3)

lemma subsetW_nibble {b0 b1 b2 b3 : F circomPrime}
    (h0 : IsBool b0) (h1 : IsBool b1) (h2 : IsBool b2) (h3 : IsBool b3)
    (B : Fin 4 → Bridge.W.Point) :
    subsetW B (8 * b3.val + 4 * b2.val + 2 * b1.val + b0.val) =
      linComb B b0.val b1.val b2.val b3.val := by
  have hone : ((1 : F circomPrime).val) = 1 := by
    change (((1 : ℕ) : F circomPrime).val) = 1
    exact ZMod.val_natCast_of_lt (by decide)
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;>
    rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;>
    subst_vars <;> simp [subsetW, pickW, linComb, hone] <;> abel

def TableFor (input : GLVMSM.Inputs (F circomPrime))
    (B : Fin 4 → Bridge.W.Point) : Prop :=
  ∀ i : Fin 16,
    decodePoint (GLVMSM.tableEntry input i.val i.isLt) =
      Bridge.toSpec (subsetW B i.val)

lemma selectedAt_eq (input : GLVMSM.Inputs (F circomPrime))
    (B : Fin 4 → Bridge.W.Point)
    (hall : GLVMSM.Assumptions input) (htable : TableFor input B)
    (k : ℕ) (hk : k < GLVMSM.coeffBits) :
    GLVMSM.selectedAt input k hk =
      Bridge.toSpec
        (linComb B
          (input.m0[GLVMSM.coeffBits - 1 - k]'(by
            simp only [GLVMSM.coeffBits] at hk ⊢; omega)).val
          (input.m1[GLVMSM.coeffBits - 1 - k]'(by
            simp only [GLVMSM.coeffBits] at hk ⊢; omega)).val
          (input.m2[GLVMSM.coeffBits - 1 - k]'(by
            simp only [GLVMSM.coeffBits] at hk ⊢; omega)).val
          (input.m3[GLVMSM.coeffBits - 1 - k]'(by
            simp only [GLVMSM.coeffBits] at hk ⊢; omega)).val) := by
  obtain ⟨_, _, hm0, hm1, hm2, hm3⟩ := hall
  have h0 := hm0 ⟨GLVMSM.coeffBits - 1 - k, by
    simp only [GLVMSM.coeffBits] at hk ⊢; omega⟩
  have h1 := hm1 ⟨GLVMSM.coeffBits - 1 - k, by
    simp only [GLVMSM.coeffBits] at hk ⊢; omega⟩
  have h2 := hm2 ⟨GLVMSM.coeffBits - 1 - k, by
    simp only [GLVMSM.coeffBits] at hk ⊢; omega⟩
  have h3 := hm3 ⟨GLVMSM.coeffBits - 1 - k, by
    simp only [GLVMSM.coeffBits] at hk ⊢; omega⟩
  have hone : ((1 : F circomPrime).val) = 1 := by
    change (((1 : ℕ) : F circomPrime).val) = 1
    exact ZMod.val_natCast_of_lt (by decide)
  have hn : GLVMSM.nibbleAt input k hk < 16 := by
    unfold GLVMSM.nibbleAt
    rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;>
      rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;>
      simp_all [hone]
  unfold GLVMSM.selectedAt
  rw [dif_pos hn, htable ⟨_, hn⟩]
  unfold GLVMSM.nibbleAt
  exact congrArg Bridge.toSpec (subsetW_nibble h0 h1 h2 h3 B)

lemma specAcc_eq (input : GLVMSM.Inputs (F circomPrime))
    (B : Fin 4 → Bridge.W.Point)
    (hall : GLVMSM.Assumptions input) (htable : TableFor input B) :
    ∀ k, k ≤ GLVMSM.coeffBits →
      GLVMSM.specAcc input k =
        Bridge.toSpec
          (linComb B (scanValue input.m0 k) (scanValue input.m1 k)
            (scanValue input.m2 k) (scanValue input.m3 k)) := by
  intro k
  induction k with
  | zero =>
      intro _
      simp [GLVMSM.specAcc, scanValue, linComb]
  | succ k ih =>
      intro hle
      have hk : k < GLVMSM.coeffBits := by omega
      rw [GLVMSM.specAcc, dif_pos hk, ih (by omega)]
      rw [selectedAt_eq input B hall htable k hk]
      unfold GLVStep.dbl
      rw [← Bridge.bridge_add, ← Bridge.bridge_add]
      apply congrArg Bridge.toSpec
      rw [scanValue_succ input.m0 k hk, scanValue_succ input.m1 k hk,
        scanValue_succ input.m2 k hk, scanValue_succ input.m3 k hk]
      unfold linComb
      simp only [two_mul, add_nsmul]
      abel

theorem specAcc_final_eq (input : GLVMSM.Inputs (F circomPrime))
    (B : Fin 4 → Bridge.W.Point)
    (hall : GLVMSM.Assumptions input) (htable : TableFor input B) :
    GLVMSM.specAcc input GLVMSM.coeffBits =
      Bridge.toSpec
        (linComb B
          (scalarOfBits ((input.m0.map ZMod.val).reverse))
          (scalarOfBits ((input.m1.map ZMod.val).reverse))
          (scalarOfBits ((input.m2.map ZMod.val).reverse))
          (scalarOfBits ((input.m3.map ZMod.val).reverse))) := by
  rw [specAcc_eq input B hall htable GLVMSM.coeffBits (le_refl _)]
  simp only [scanValue_final]

end Solution.Secp256k1ScalarMul.GLVMSMTheorems
