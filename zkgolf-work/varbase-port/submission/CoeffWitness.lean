import Solution.Secp256k1ScalarMul.SignedCoeff
import Solution.Secp256k1ScalarMul.ShortCoeffs



namespace Solution.Secp256k1ScalarMul.CoeffWitness

open Utils.Bits
open Solution.Secp256k1ScalarMul.GLV


def signBit (z : ℤ) : F circomPrime :=
  if z < 0 then 1 else 0


def magnitudeBits (z : ℤ) : Vector (F circomPrime) coeffBits :=
  (toBits coeffBits z.natAbs).map fun b : ℕ => (b : F circomPrime)


def ofInt (z : ℤ) : SignedCoeff (F circomPrime) :=
  { sign := signBit z, bits := magnitudeBits z }

lemma magnitudeBits_map_val (z : ℤ) :
    (magnitudeBits z).map ZMod.val = toBits coeffBits z.natAbs := by
  simp only [magnitudeBits, Vector.map_map]
  exact val_natCast_toBits (p := circomPrime)

lemma magnitudeBits_get (z : ℤ) (i : Fin coeffBits) :
    (magnitudeBits z)[i] =
      ((toBits coeffBits z.natAbs)[i] : F circomPrime) := by
  exact Vector.getElem_map (fun b : ℕ => (b : F circomPrime)) i.isLt

lemma magnitudeBits_get_val (z : ℤ) (i : Fin coeffBits) :
    (magnitudeBits z)[i].val = (toBits coeffBits z.natAbs)[i] := by
  calc
    (magnitudeBits z)[i].val = ((magnitudeBits z).map ZMod.val)[i] :=
      (Vector.getElem_map ZMod.val i.isLt).symm
    _ = (toBits coeffBits z.natAbs)[i] := by
      rw [magnitudeBits_map_val]

lemma magnitudeBits_isBool (z : ℤ) (i : Fin coeffBits) :
    IsBool (magnitudeBits z)[i] := by
  rw [magnitudeBits_get]
  rw [show (toBits coeffBits z.natAbs)[i] =
      (if z.natAbs.testBit i.val then 1 else 0) from
    Vector.getElem_mapRange i.val i.isLt]
  split
  · exact IsBool.one
  · exact IsBool.zero

lemma signBit_isBool (z : ℤ) : IsBool (signBit z) := by
  simp only [signBit]
  split
  · exact IsBool.one
  · exact IsBool.zero

theorem ofInt_valid (z : ℤ) : Valid (ofInt z) := by
  exact ⟨signBit_isBool z, magnitudeBits_isBool z⟩

theorem fromBits_magnitudeBits (z : ℤ)
    (hz : z.natAbs < 2 ^ coeffBits) :
    fromBits ((ofInt z).bits.map ZMod.val) = z.natAbs := by
  rw [show (ofInt z).bits = magnitudeBits z from rfl,
    magnitudeBits_map_val, fromBits_toBits hz]

lemma lowBits_ofInt (z : ℤ) :
    lowBits (ofInt z).bits =
      (toBits 64 z.natAbs).map fun b : ℕ => (b : F circomPrime) := rfl

lemma lowValue_ofInt (z : ℤ) :
    (fieldFromBits (lowBits (ofInt z).bits)).val = z.natAbs % 2 ^ 64 := by
  rw [lowBits_ofInt]
  simp only [fieldFromBits, Vector.map_map]
  rw [val_natCast_toBits, fromBits_toBits_mod, ZMod.val_natCast]
  apply Nat.mod_eq_of_lt
  have hmod : z.natAbs % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by positivity)
  have hp : 2 ^ 64 < circomPrime := by
    change 18446744073709551616 <
      21888242871839275222246405745257275088548364400416034343698204186575808495617
    norm_num
  omega

theorem magnitude_ofInt (z : ℤ) (hz : z.natAbs < 2 ^ coeffBits) :
    magnitude (ofInt z) = z.natAbs := by
  rw [magnitude, lowValue_ofInt]
  simp only [coeffBits, limbBits] at hz ⊢
  rw [Nat.mod_eq_of_lt hz]

theorem signBit_eq_one_iff (z : ℤ) : signBit z = 1 ↔ z < 0 := by
  simp [signBit]

theorem signBit_eq_zero_iff (z : ℤ) : signBit z = 0 ↔ 0 ≤ z := by
  simp [signBit, not_lt]

theorem signedValue_ofInt (z : ℤ) (hz : z.natAbs < 2 ^ coeffBits) :
    signedValue (ofInt z) = z := by
  rw [signedValue, magnitude_ofInt z hz]
  change (if signBit z = 1 then -(↑z.natAbs : ℤ) else ↑z.natAbs) = z
  by_cases hneg : z < 0
  · rw [if_pos (signBit_eq_one_iff z |>.2 hneg)]
    rcases Int.natAbs_eq z with hpos | hneg'
    · omega
    · exact hneg'.symm
  · rw [if_neg]
    · exact Int.natAbs_of_nonneg (by omega)
    · exact fun h => hneg ((signBit_eq_one_iff z).1 h)


def ofDecomposition {k : ZMod Specs.Secp256k1.order}
    (d : ShortCoeffs.Decomposition k) : Coefficients (F circomPrime) :=
  { u1 := ofInt d.u₁
    u2 := ofInt d.u₂
    v1 := ofInt d.v₁
    v2 := ofInt d.v₂ }

theorem ofDecomposition_valid {k : ZMod Specs.Secp256k1.order}
    (d : ShortCoeffs.Decomposition k) :
    Valid (ofDecomposition d).u1 ∧ Valid (ofDecomposition d).u2 ∧
      Valid (ofDecomposition d).v1 ∧ Valid (ofDecomposition d).v2 := by
  exact ⟨ofInt_valid _, ofInt_valid _, ofInt_valid _, ofInt_valid _⟩

/-- The first coefficient of a decomposition is non-negative, so its sign bit is
zero.  This is what lets the table build skip the sign multiplexer on the base
point's y-coordinate. -/
theorem ofDecomposition_u1_sign {k : ZMod Specs.Secp256k1.order}
    (d : ShortCoeffs.Decomposition k) :
    (ofDecomposition d).u1.sign = 0 :=
  (signBit_eq_zero_iff _).2 d.u₁_nonneg

theorem ofDecomposition_values {k : ZMod Specs.Secp256k1.order}
    (d : ShortCoeffs.Decomposition k) :
    signedValue (ofDecomposition d).u1 = d.u₁ ∧
      signedValue (ofDecomposition d).u2 = d.u₂ ∧
      signedValue (ofDecomposition d).v1 = d.v₁ ∧
      signedValue (ofDecomposition d).v2 = d.v₂ := by
  exact ⟨signedValue_ofInt _ d.u₁_bound,
    signedValue_ofInt _ d.u₂_bound,
    signedValue_ofInt _ d.v₁_bound,
    signedValue_ofInt _ d.v₂_bound⟩

theorem ofDecomposition_magnitudes {k : ZMod Specs.Secp256k1.order}
    (d : ShortCoeffs.Decomposition k) :
    magnitude (ofDecomposition d).u1 = d.u₁.natAbs ∧
      magnitude (ofDecomposition d).u2 = d.u₂.natAbs ∧
      magnitude (ofDecomposition d).v1 = d.v₁.natAbs ∧
      magnitude (ofDecomposition d).v2 = d.v₂.natAbs := by
  exact ⟨magnitude_ofInt _ d.u₁_bound,
    magnitude_ofInt _ d.u₂_bound,
    magnitude_ofInt _ d.v₁_bound,
    magnitude_ofInt _ d.v₂_bound⟩

theorem ofDecomposition_v_nonzero {k : ZMod Specs.Secp256k1.order}
    (d : ShortCoeffs.Decomposition k) :
    magnitude (ofDecomposition d).v1 ≠ 0 ∨
      magnitude (ofDecomposition d).v2 ≠ 0 := by
  simp only [ofDecomposition]
  rw [magnitude_ofInt _ d.v₁_bound, magnitude_ofInt _ d.v₂_bound]
  rcases d.v_nonzero with hv | hv
  · exact Or.inl (by simpa using hv)
  · exact Or.inr (by simpa using hv)

theorem ofDecomposition_signed_v_nonzero
    {k : ZMod Specs.Secp256k1.order}
    (d : ShortCoeffs.Decomposition k) :
    signedValue (ofDecomposition d).v1 ≠ 0 ∨
      signedValue (ofDecomposition d).v2 ≠ 0 := by
  simp only [ofDecomposition]
  rw [signedValue_ofInt _ d.v₁_bound, signedValue_ofInt _ d.v₂_bound]
  exact d.v_nonzero

theorem ofDecomposition_relation {k : ZMod Specs.Secp256k1.order}
    (d : ShortCoeffs.Decomposition k) :
    (signedValue (ofDecomposition d).u1 : ZMod Specs.Secp256k1.order) +
        (ShortCoeffs.lambdaZ : ZMod Specs.Secp256k1.order) *
          signedValue (ofDecomposition d).u2 +
      k * ((signedValue (ofDecomposition d).v1 : ZMod Specs.Secp256k1.order) +
        (ShortCoeffs.lambdaZ : ZMod Specs.Secp256k1.order) *
          signedValue (ofDecomposition d).v2) = 0 := by
  simp only [ofDecomposition]
  rw [signedValue_ofInt _ d.u₁_bound, signedValue_ofInt _ d.u₂_bound,
    signedValue_ofInt _ d.v₁_bound, signedValue_ofInt _ d.v₂_bound]
  exact d.relation

end Solution.Secp256k1ScalarMul.CoeffWitness
