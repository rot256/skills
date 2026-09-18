import Solution.Secp256k1ScalarMul.Params
import Solution.Secp256k1ScalarMul.Mux
import Solution.Secp256k1ScalarMul.IsZeroFeSumR
import Solution.Secp256k1ScalarMul.OrderFactsCerts

/-!
# Table lookup by a four-bit nibble

The sixteen table entries are selected by a binary mux tree.  Only the two
coordinates travel through the tree: the infinity flag of the selected entry is
*recovered* from its `x` coordinate by a single zero test.  This is sound
because the two possible states are separated by `x`:

* an entry flagged as infinity is encoded canonically with `x = 0`
  (`Assumptions`), and
* a finite entry is a point of secp256k1, and secp256k1 has no affine point
  with `x = 0` (`OrderFactsCerts.noXZero_secp`, a quadratic non-residue
  certificate for `7`).

Muxing eight field elements instead of nine and paying two cells for the zero
test costs `122` rows instead of `135`.
-/

namespace Solution.Secp256k1ScalarMul
namespace VarLookup

structure Inputs (F : Type) where
  tx : Vector (Emu F) 16
  ty : Vector (Emu F) 16
  tinf : Vector F 16
  b3 : F
  b2 : F
  b1 : F
  b0 : F
deriving ProvableStruct

/-- The pair of coordinates carried through the mux tree. -/
structure XY (F : Type) where
  x : Emu F
  y : Emu F
deriving ProvableStruct

def nibble (input : Inputs (F circomPrime)) : ℕ :=
  8 * input.b3.val + 4 * input.b2.val + 2 * input.b1.val + input.b0.val

def entry (input : Inputs (F circomPrime)) (i : ℕ) (h : i < 16) :
    FlaggedPoint (F circomPrime) :=
  { x := input.tx[i]'h, y := input.ty[i]'h, isInf := input.tinf[i]'h }

def main (input : Var Inputs (F circomPrime)) :
    Circuit (F circomPrime) (Var FlaggedPoint (F circomPrime)) := do
  let b3 := input.b3; let b2 := input.b2; let b1 := input.b1; let b0 := input.b0
  let T : (i : ℕ) → i < 16 → Var XY (F circomPrime) := fun i h =>
    { x := input.tx[i]'h, y := input.ty[i]'h }
  -- level 0: select by b0 within each adjacent pair
  let t01 ← subcircuit (Mux.circuit (M := XY)) { selector := b0, ifTrue := T 1 (by norm_num), ifFalse := T 0 (by norm_num) }
  let t23 ← subcircuit (Mux.circuit (M := XY)) { selector := b0, ifTrue := T 3 (by norm_num), ifFalse := T 2 (by norm_num) }
  let t45 ← subcircuit (Mux.circuit (M := XY)) { selector := b0, ifTrue := T 5 (by norm_num), ifFalse := T 4 (by norm_num) }
  let t67 ← subcircuit (Mux.circuit (M := XY)) { selector := b0, ifTrue := T 7 (by norm_num), ifFalse := T 6 (by norm_num) }
  let t89 ← subcircuit (Mux.circuit (M := XY)) { selector := b0, ifTrue := T 9 (by norm_num), ifFalse := T 8 (by norm_num) }
  let tAB ← subcircuit (Mux.circuit (M := XY)) { selector := b0, ifTrue := T 11 (by norm_num), ifFalse := T 10 (by norm_num) }
  let tCD ← subcircuit (Mux.circuit (M := XY)) { selector := b0, ifTrue := T 13 (by norm_num), ifFalse := T 12 (by norm_num) }
  let tEF ← subcircuit (Mux.circuit (M := XY)) { selector := b0, ifTrue := T 15 (by norm_num), ifFalse := T 14 (by norm_num) }
  -- level 1: select by b1
  let u0 ← subcircuit (Mux.circuit (M := XY)) { selector := b1, ifTrue := t23, ifFalse := t01 }
  let u1 ← subcircuit (Mux.circuit (M := XY)) { selector := b1, ifTrue := t67, ifFalse := t45 }
  let u2 ← subcircuit (Mux.circuit (M := XY)) { selector := b1, ifTrue := tAB, ifFalse := t89 }
  let u3 ← subcircuit (Mux.circuit (M := XY)) { selector := b1, ifTrue := tEF, ifFalse := tCD }
  -- level 2: select by b2
  let v0 ← subcircuit (Mux.circuit (M := XY)) { selector := b2, ifTrue := u1, ifFalse := u0 }
  let v1 ← subcircuit (Mux.circuit (M := XY)) { selector := b2, ifTrue := u3, ifFalse := u2 }
  -- level 3: select by b3
  let w ← subcircuit (Mux.circuit (M := XY)) { selector := b3, ifTrue := v1, ifFalse := v0 }
  -- the infinity flag of the selected entry, recovered from its x coordinate
  let z ← subcircuit IsZeroFeSumR.circuit w.x
  return { x := w.x, y := w.y, isInf := z }

instance elaborated : ElaboratedCircuit (F circomPrime) Inputs FlaggedPoint main := by
  elaborate_circuit

def Assumptions (input : Inputs (F circomPrime)) : Prop :=
  IsBool input.b3 ∧ IsBool input.b2 ∧ IsBool input.b1 ∧ IsBool input.b0 ∧
  (∀ i : Fin 16, (entry input i.val i.isLt).Valid) ∧
  (∀ i : Fin 16, (entry input i.val i.isLt).isInf = 1 →
    decodeFe (entry input i.val i.isLt).x = 0)

def Spec (input : Inputs (F circomPrime)) (out : FlaggedPoint (F circomPrime)) : Prop :=
  ∃ h : nibble input < 16, out = entry input (nibble input) h

/-- The infinity flag of a valid, canonically encoded entry is exactly the zero
test of its `x` coordinate. -/
theorem isInf_eq_isZero_x {P : FlaggedPoint (F circomPrime)} (hP : P.Valid)
    (hcanon : P.isInf = 1 → decodeFe P.x = 0) :
    (if BigInt.value limbBits P.x = 0 then (1 : F circomPrime) else 0) = P.isInf := by
  obtain ⟨hb, hxv, hyv, honc⟩ := hP
  have hval : decodeFe P.x = 0 ↔ BigInt.value limbBits P.x = 0 := by
    constructor
    · intro h
      have hlt : BigInt.value limbBits P.x < Specs.Secp256k1.p := hxv.2
      have := congrArg ZMod.val h
      rwa [decodeFe, ZMod.val_cast_of_lt hlt, ZMod.val_zero] at this
    · intro h
      simp only [decodeFe, h, Nat.cast_zero]
  rcases hb with h0 | h1
  · -- finite entry: on the curve, hence `x ≠ 0`
    have hx : decodeFe P.x ≠ 0 := OrderFactsCerts.noXZero_secp (honc h0)
    rw [if_neg (fun h => hx (hval.mpr h)), h0]
  · rw [if_pos (hval.mp (hcanon h1)), h1]

/-- The zero test of the limb sum of table entry `k` recovers its infinity flag. -/
theorem isInf_recover (input : Inputs (F circomPrime))
    (hA : ∀ i : Fin 16, (entry input i.val i.isLt).Valid)
    (hC : ∀ i : Fin 16, (entry input i.val i.isLt).isInf = 1 →
      decodeFe (entry input i.val i.isLt).x = 0)
    (k : ℕ) (hk : k < 16) :
    (if IsZeroFeSumR.limbSum (input.tx[k]'hk) = 0 then (1 : F circomPrime) else 0)
      = input.tinf[k]'hk := by
  have hV := hA ⟨k, hk⟩
  have hbound : ∀ i : Fin numLimbs, ((input.tx[k]'hk)[i.val]'i.isLt).val < 3 * 2 ^ limbBits := by
    intro i
    have h1 := hV.2.1.1 i
    simp only [entry, Fin.getElem_fin] at h1
    omega
  simp only [IsZeroFeSumR.limbSum, IsZeroFeSum.sum_field_eq_zero_iff_value _ hbound]
  exact isInf_eq_isZero_x hV (hC ⟨k, hk⟩)

/-- `isInf_recover` restated in the shape produced by the normalization used in
`soundness`, so that it applies by syntactic matching. -/
theorem isInf_recover_ev (env : Environment (F circomPrime))
    (tx ty : Vector (Emu (Expression (F circomPrime))) 16)
    (tinf : Vector (Expression (F circomPrime)) 16)
    (b3 b2 b1 b0 : F circomPrime)
    (hA : ∀ i : Fin 16, (entry (Inputs.mk (eval env tx) (eval env ty)
      (Vector.map (Expression.eval env) tinf) b3 b2 b1 b0) i.val i.isLt).Valid)
    (hC : ∀ i : Fin 16, (entry (Inputs.mk (eval env tx) (eval env ty)
        (Vector.map (Expression.eval env) tinf) b3 b2 b1 b0) i.val i.isLt).isInf = 1 →
      decodeFe (entry (Inputs.mk (eval env tx) (eval env ty)
        (Vector.map (Expression.eval env) tinf) b3 b2 b1 b0) i.val i.isLt).x = 0)
    (k : ℕ) (hk : k < 16) :
    (if IsZeroFeSumR.limbSum (Vector.map (Expression.eval env) (tx[k]'hk)) = 0
        then (1 : F circomPrime) else 0) = Expression.eval env (tinf[k]'hk) := by
  have h := isInf_recover _ hA hC k hk
  simpa only [← getElem_eval_vector, ProvableType.eval_fields, Vector.getElem_map] using h

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem soundness : Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [Mux.circuit, Mux.Assumptions, Mux.Spec,
    IsZeroFeSumR.circuit, IsZeroFeSumR.Assumptions, IsZeroFeSumR.Spec]
  obtain ⟨hb3, hb2, hb1, hb0, htab, hcanon⟩ := h_assumptions
  obtain ⟨hx, hy, hinf, -, -, -, -⟩ := h_input
  subst hx hy hinf
  obtain ⟨h01, h23, h45, h67, h89, hAB, hCD, hEF, hu0, hu1, hu2, hu3, hv0, hv1, hw, sz⟩ :=
    h_holds
  have s01 := h01 hb0; have s23 := h23 hb0; have s45 := h45 hb0; have s67 := h67 hb0
  have s89 := h89 hb0; have sAB := hAB hb0; have sCD := hCD hb0; have sEF := hEF hb0
  have su0 := hu0 hb1; have su1 := hu1 hb1; have su2 := hu2 hb1; have su3 := hu3 hb1
  have sv0 := hv0 hb2; have sv1 := hv1 hb2; have sw := hw hb3
  clear h01 h23 h45 h67 h89 hAB hCD hEF hu0 hu1 hu2 hu3 hv0 hv1 hw
  rcases hb3 with e3 | e3 <;> rcases hb2 with e2 | e2 <;>
    rcases hb1 with e1 | e1 <;> rcases hb0 with e0 | e0 <;> subst e3 e2 e1 e0 <;>
    refine ⟨by simp only [nibble, ZMod.val_zero, ZMod.val_one]; norm_num, ?_⟩
  all_goals
    have hxy := sw
    simp only [sv0, sv1, su0, su1, su2, su3, s01, s23, s45, s67, s89, sAB, sCD, sEF,
      zero_ne_one, if_true, if_false, XY.mk.injEq] at hxy
    simp only [entry, nibble, ZMod.val_zero, ZMod.val_one, Nat.mul_zero, Nat.mul_one,
      Nat.add_zero, Nat.zero_add, Nat.reduceAdd, FlaggedPoint.mk.injEq,
      ← getElem_eval_vector, ProvableType.eval_fields, Vector.getElem_map]
    refine ⟨hxy.1, hxy.2, ?_⟩
    rw [sz]
    simp only [hxy.1]
    exact isInf_recover_ev env input_var_tx input_var_ty input_var_tinf _ _ _ _
      htab hcanon _ (by norm_num)

theorem completeness : Completeness (F circomPrime) main Assumptions := by
  circuit_proof_start [Mux.circuit, Mux.Assumptions, Mux.Spec,
    IsZeroFeSumR.circuit, IsZeroFeSumR.Assumptions, IsZeroFeSumR.Spec]
  obtain ⟨hb3, hb2, hb1, hb0, -, -⟩ := h_assumptions
  exact ⟨hb0, hb0, hb0, hb0, hb0, hb0, hb0, hb0, hb1, hb1, hb1, hb1, hb2, hb2, hb3⟩

def circuit : FormalCircuit (F circomPrime) Inputs FlaggedPoint where
  main; elaborated; Assumptions; Spec; soundness; completeness

end VarLookup
end Solution.Secp256k1ScalarMul
