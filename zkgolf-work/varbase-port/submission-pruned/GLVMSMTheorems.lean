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

end Solution.Secp256k1ScalarMul.GLVMSMTheorems
