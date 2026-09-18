import Solution.Secp256k1ScalarMul.Params
import Solution.Secp256k1ScalarMul.IsZeroFe
import Solution.Secp256k1ScalarMul.IsZeroFeTheorems
import Challenge.Utils.ComputableWitnessLemmas
import Clean.Gadgets.IsZeroField

namespace Solution.Secp256k1ScalarMul
namespace IsZeroFeSum

theorem sum_field_eq_zero_iff_value (x : Emu (F circomPrime))
    (hbound : ∀ i : Fin numLimbs, (x[i.val]'i.isLt).val < 3 * 2 ^ limbBits) :
    (x[0] + x[1] + x[2] + x[3] : F circomPrime) = 0 ↔ BigInt.value limbBits x = 0 := by
  rw [BigInt.value_eq_zero_iff]
  have hb0 : (x[0]).val < 3 * 2 ^ limbBits := hbound 0
  have hb1 : (x[1]).val < 3 * 2 ^ limbBits := hbound 1
  have hb2 : (x[2]).val < 3 * 2 ^ limbBits := hbound 2
  have hb3 : (x[3]).val < 3 * 2 ^ limbBits := hbound 3
  constructor
  · intro hsum
    set S : ℕ := (x[0]).val + (x[1]).val + (x[2]).val + (x[3]).val with hS
    have hScast : ((S : ℕ) : F circomPrime) = x[0] + x[1] + x[2] + x[3] := by
      rw [hS]; push_cast; rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val,
        ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    have hcast : ((S : ℕ) : F circomPrime) = 0 := by rw [hScast]; exact hsum
    have hdvd : circomPrime ∣ S := (ZMod.natCast_eq_zero_iff _ _).mp hcast
    have hbig : 4 * (3 * 2 ^ limbBits) < circomPrime := by decide
    have hSlt : S < circomPrime := by rw [hS]; omega
    have hS0 : S = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hSlt
    have hv0 : (x[0]).val = 0 := by rw [hS] at hS0; omega
    have hv1 : (x[1]).val = 0 := by rw [hS] at hS0; omega
    have hv2 : (x[2]).val = 0 := by rw [hS] at hS0; omega
    have hv3 : (x[3]).val = 0 := by rw [hS] at hS0; omega
    have hx0 : x[0] = 0 := (ZMod.val_eq_zero _).mp hv0
    have hx1 : x[1] = 0 := (ZMod.val_eq_zero _).mp hv1
    have hx2 : x[2] = 0 := (ZMod.val_eq_zero _).mp hv2
    have hx3 : x[3] = 0 := (ZMod.val_eq_zero _).mp hv3
    intro i
    fin_cases i
    · simpa using hx0
    · simpa using hx1
    · simpa using hx2
    · simpa using hx3
  · intro hall
    have hx0 : x[0] = (0 : F circomPrime) := by simpa using hall 0
    have hx1 : x[1] = (0 : F circomPrime) := by simpa using hall 1
    have hx2 : x[2] = (0 : F circomPrime) := by simpa using hall 2
    have hx3 : x[3] = (0 : F circomPrime) := by simpa using hall 3
    rw [hx0, hx1, hx2, hx3]; ring

end IsZeroFeSum
end Solution.Secp256k1ScalarMul
