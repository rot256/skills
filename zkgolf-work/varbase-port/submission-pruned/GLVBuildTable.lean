import Solution.Secp256k1ScalarMul.CompleteAdd
import Solution.Secp256k1ScalarMul.PhiPairAdd
import Solution.Secp256k1ScalarMul.Phi
import Solution.Secp256k1ScalarMul.OrderFactsCerts
import Solution.Secp256k1ScalarMul.MulModBeta32
import Solution.Secp256k1ScalarMul.NegYAffine

namespace Solution.Secp256k1ScalarMul
namespace GLVBuildTable

open Specs.ShortWeierstrass Specs.Secp256k1

structure Inputs (F : Type) where
  P : FlaggedPoint F
  Q : FlaggedPoint F
  sign0 : F
  sign1 : F
  sign2 : F
  sign3 : F
deriving ProvableStruct

structure Bases (F : Type) where
  r0 : FlaggedPoint F
  r1 : FlaggedPoint F
  r2 : FlaggedPoint F
  r3 : FlaggedPoint F
deriving ProvableStruct

structure RawTable (F : Type) where
  t0 : FlaggedPoint F
  t1 : FlaggedPoint F
  t2 : FlaggedPoint F
  t3 : FlaggedPoint F
  t4 : FlaggedPoint F
  t5 : FlaggedPoint F
  t6 : FlaggedPoint F
  t7 : FlaggedPoint F
  t8 : FlaggedPoint F
  t9 : FlaggedPoint F
  t10 : FlaggedPoint F
  t11 : FlaggedPoint F
  t12 : FlaggedPoint F
  t13 : FlaggedPoint F
  t14 : FlaggedPoint F
  t15 : FlaggedPoint F
deriving ProvableStruct

structure Table (F : Type) where
  tx : Vector (Emu F) 16
  ty : Vector (Emu F) 16
  tinf : Vector F 16
deriving ProvableStruct

def baseEntry (b : Bases (F circomPrime)) : Fin 4 → FlaggedPoint (F circomPrime)
  | ⟨0, _⟩ => b.r0
  | ⟨1, _⟩ => b.r1
  | ⟨2, _⟩ => b.r2
  | ⟨3, _⟩ => b.r3

def rawEntry (t : RawTable (F circomPrime)) : Fin 16 → FlaggedPoint (F circomPrime)
  | ⟨0, _⟩ => t.t0
  | ⟨1, _⟩ => t.t1
  | ⟨2, _⟩ => t.t2
  | ⟨3, _⟩ => t.t3
  | ⟨4, _⟩ => t.t4
  | ⟨5, _⟩ => t.t5
  | ⟨6, _⟩ => t.t6
  | ⟨7, _⟩ => t.t7
  | ⟨8, _⟩ => t.t8
  | ⟨9, _⟩ => t.t9
  | ⟨10, _⟩ => t.t10
  | ⟨11, _⟩ => t.t11
  | ⟨12, _⟩ => t.t12
  | ⟨13, _⟩ => t.t13
  | ⟨14, _⟩ => t.t14
  | _ => t.t15

def entry (t : Table (F circomPrime)) (i : ℕ) (h : i < 16) :
    FlaggedPoint (F circomPrime) :=
  { x := t.tx[i]'h, y := t.ty[i]'h, isInf := t.tinf[i]'h }

def betaNat : ℕ :=
  0x7ae96a2b657c07106e64479eac3434e99cf0497512f58995c1396c28719501ee

abbrev MM := MulMod.circuit secpParams gfMul posOfMul 5 vMul vMul
  hgvMul hNfMul hNfMul

def negGP : GroupPoint Fp → GroupPoint Fp
  | .infinity => .infinity
  | .affine P => .affine { x := P.x, y := -P.y }

def phiGP : GroupPoint Fp → GroupPoint Fp
  | .infinity => .infinity
  | .affine P => .affine { x := Phi.beta * P.x, y := P.y }

def signedGP (s : F circomPrime) (P : GroupPoint Fp) : GroupPoint Fp :=
  if s = 1 then negGP P else P

def signedBase (input : Inputs (F circomPrime)) : Fin 4 → GroupPoint Fp
  | ⟨0, _⟩ => signedGP input.sign0 (decodePoint input.P)
  | ⟨1, _⟩ => signedGP input.sign1 (phiGP (decodePoint input.P))
  | ⟨2, _⟩ => signedGP input.sign2 (decodePoint input.Q)
  | ⟨3, _⟩ => signedGP input.sign3 (phiGP (decodePoint input.Q))

def bitAt (t j : ℕ) : Bool := decide (t / 2 ^ j % 2 = 1)

def pick (b : Bool) (P : GroupPoint Fp) : GroupPoint Fp :=
  if b then P else .infinity

def subsetPoint (B : Fin 4 → GroupPoint Fp) (t : ℕ) : GroupPoint Fp :=
  add curve
    (add curve (pick (bitAt t 0) (B 0)) (pick (bitAt t 1) (B 1)))
    (add curve (pick (bitAt t 2) (B 2)) (pick (bitAt t 3) (B 3)))

lemma add_infinity_left (P : GroupPoint Fp) :
    add curve .infinity P = P := rfl

lemma add_infinity_right (P : GroupPoint Fp) :
    add curve P .infinity = P := by
  cases P <;> rfl

lemma subsetPoint_0 (B : Fin 4 → GroupPoint Fp) :
    subsetPoint B 0 = .infinity := by
  simp [subsetPoint, pick, bitAt, add_infinity_left, add_infinity_right]

lemma subsetPoint_1 (B : Fin 4 → GroupPoint Fp) :
    subsetPoint B 1 = B 0 := by
  simp [subsetPoint, pick, bitAt, add_infinity_left, add_infinity_right]

lemma subsetPoint_2 (B : Fin 4 → GroupPoint Fp) :
    subsetPoint B 2 = B 1 := by
  simp [subsetPoint, pick, bitAt, add_infinity_left, add_infinity_right]

lemma subsetPoint_3 (B : Fin 4 → GroupPoint Fp) :
    subsetPoint B 3 = add curve (B 0) (B 1) := by
  simp [subsetPoint, pick, bitAt, add_infinity_left, add_infinity_right]

lemma subsetPoint_4 (B : Fin 4 → GroupPoint Fp) :
    subsetPoint B 4 = B 2 := by
  simp [subsetPoint, pick, bitAt, add_infinity_left, add_infinity_right]

lemma subsetPoint_5 (B : Fin 4 → GroupPoint Fp) :
    subsetPoint B 5 = add curve (B 0) (B 2) := by
  simp [subsetPoint, pick, bitAt, add_infinity_left, add_infinity_right]

lemma subsetPoint_6 (B : Fin 4 → GroupPoint Fp) :
    subsetPoint B 6 = add curve (B 1) (B 2) := by
  simp [subsetPoint, pick, bitAt, add_infinity_left, add_infinity_right]

lemma subsetPoint_7 (B : Fin 4 → GroupPoint Fp) :
    subsetPoint B 7 = add curve (add curve (B 0) (B 1)) (B 2) := by
  simp [subsetPoint, pick, bitAt, add_infinity_left, add_infinity_right]

lemma subsetPoint_8 (B : Fin 4 → GroupPoint Fp) :
    subsetPoint B 8 = B 3 := by
  simp [subsetPoint, pick, bitAt, add_infinity_left, add_infinity_right]

lemma subsetPoint_9 (B : Fin 4 → GroupPoint Fp) :
    subsetPoint B 9 = add curve (B 0) (B 3) := by
  simp [subsetPoint, pick, bitAt, add_infinity_left, add_infinity_right]

lemma subsetPoint_10 (B : Fin 4 → GroupPoint Fp) :
    subsetPoint B 10 = add curve (B 1) (B 3) := by
  simp [subsetPoint, pick, bitAt, add_infinity_left, add_infinity_right]

lemma subsetPoint_11 (B : Fin 4 → GroupPoint Fp) :
    subsetPoint B 11 = add curve (add curve (B 0) (B 1)) (B 3) := by
  simp [subsetPoint, pick, bitAt, add_infinity_left, add_infinity_right]

lemma subsetPoint_12 (B : Fin 4 → GroupPoint Fp) :
    subsetPoint B 12 = add curve (B 2) (B 3) := by
  simp [subsetPoint, pick, bitAt, add_infinity_left, add_infinity_right]

lemma subsetPoint_13 (B : Fin 4 → GroupPoint Fp) :
    subsetPoint B 13 = add curve (B 0) (add curve (B 2) (B 3)) := by
  simp [subsetPoint, pick, bitAt, add_infinity_left, add_infinity_right]

lemma subsetPoint_14 (B : Fin 4 → GroupPoint Fp) :
    subsetPoint B 14 = add curve (B 1) (add curve (B 2) (B 3)) := by
  simp [subsetPoint, pick, bitAt, add_infinity_left, add_infinity_right]

lemma subsetPoint_15 (B : Fin 4 → GroupPoint Fp) :
    subsetPoint B 15 =
      add curve (add curve (B 0) (B 1)) (add curve (B 2) (B 3)) := by
  simp [subsetPoint, pick, bitAt, add_infinity_left, add_infinity_right]

def valueFP (x y : Emu (F circomPrime)) (isInf : F circomPrime) :
    FlaggedPoint (F circomPrime) := { x, y, isInf }

lemma neg_valueFP
    {P : FlaggedPoint (F circomPrime)} {ny : Emu (F circomPrime)}
    (hP : P.Valid) (hny : Fe.Valid ny)
    (heq : decodeFe ny = -decodeFe P.y) :
    (valueFP P.x ny P.isInf).Valid ∧
      decodePoint (valueFP P.x ny P.isInf) = negGP (decodePoint P) := by
  constructor
  · refine ⟨hP.1, hP.2.1, hny, ?_⟩
    intro hi
    have hc := hP.2.2.2 hi
    rw [onCurve_iff] at hc ⊢
    change (decodeFe ny) ^ 2 = (decodeFe P.x) ^ 3 + 7
    rw [heq, neg_sq]
    exact hc
  · by_cases hi : P.isInf = 1
    · simp [decodePoint, valueFP, hi, negGP]
    · simp [decodePoint, valueFP, hi, negGP, heq]

lemma phi_valueFP
    {P : FlaggedPoint (F circomPrime)} {px : Emu (F circomPrime)}
    (hP : P.Valid) (hpx : Fe.Valid px)
    (heq : decodeFe px = Phi.beta * decodeFe P.x) :
    (valueFP px P.y P.isInf).Valid ∧
      decodePoint (valueFP px P.y P.isInf) = phiGP (decodePoint P) := by
  constructor
  · refine ⟨hP.1, hpx, hP.2.2.1, ?_⟩
    intro hi
    have hc := hP.2.2.2 hi
    rw [onCurve_iff] at hc ⊢
    change (decodeFe P.y) ^ 2 = (decodeFe px) ^ 3 + 7
    rw [heq, mul_pow, Phi.beta_cube, one_mul]
    exact hc
  · by_cases hi : P.isInf = 1
    · simp [decodePoint, valueFP, hi, phiGP]
    · simp [decodePoint, valueFP, hi, phiGP, heq]

lemma selected_point {s : F circomPrime}
    {pos neg out : FlaggedPoint (F circomPrime)}
    (hs : IsBool s) (hp : pos.Valid) (hn : neg.Valid)
    (hneg : decodePoint neg = negGP (decodePoint pos))
    (hout : out = if s = 1 then neg else pos) :
    out.Valid ∧ decodePoint out = signedGP s (decodePoint pos) := by
  rcases hs with h0 | h1
  · rw [h0] at hout ⊢
    simp only [zero_ne_one, if_false, signedGP] at hout ⊢
    subst out
    exact ⟨hp, rfl⟩
  · rw [h1] at hout ⊢
    simp only [if_pos rfl, signedGP] at hout ⊢
    subst out
    exact ⟨hn, hneg⟩

lemma evalInf_valid (env : Environment (F circomPrime)) :
    (valueFP (Vector.map (Expression.eval env) infConst.x)
      (Vector.map (Expression.eval env) infConst.y)
      (Expression.eval env infConst.isInf)).Valid := by
  have hx : Vector.map (Expression.eval env) infConst.x = emuOfNat 0 :=
    DivOrZero.eval_zeroConst env
  have hy : Vector.map (Expression.eval env) infConst.y = emuOfNat 0 :=
    DivOrZero.eval_zeroConst env
  have hi : Expression.eval env infConst.isInf = 1 := rfl
  simp only [valueFP, hx, hy, hi]
  exact ⟨Or.inr rfl, DivOrZero.fe_valid_emuOfNat DivOrZero.P256_pos,
    DivOrZero.fe_valid_emuOfNat DivOrZero.P256_pos, fun h => absurd h one_ne_zero⟩

lemma decode_evalInf (env : Environment (F circomPrime)) :
    decodePoint (valueFP (Vector.map (Expression.eval env) infConst.x)
      (Vector.map (Expression.eval env) infConst.y)
      (Expression.eval env infConst.isInf)) = .infinity := by
  rw [decodePoint]
  exact if_pos rfl

lemma decode_beta : decodeFe (emuOfNat betaNat) = Phi.beta := by
  rw [decodeFe, DivOrZero.value_emuOfNat (by norm_num [betaNat, limbBits, numLimbs])]
  rfl

lemma beta32_cast : ((MulModBeta32.betaNat : ℕ) : Fp) = Phi.beta := by
  have h : decodeFe (emuOfNat betaNat) = ((betaNat : ℕ) : Fp) := by
    rw [decodeFe, DivOrZero.value_emuOfNat (by norm_num [betaNat, limbBits, numLimbs])]
  rw [show MulModBeta32.betaNat = betaNat from rfl, ← h, decode_beta]

lemma beta_ne_one : Phi.beta ≠ 1 := by decide

private lemma signedGP_affine_x (s : F circomPrime) (x y : Fp) :
    ∃ y' : Fp, signedGP s (.affine { x := x, y := y }) =
      .affine { x := x, y := y' } := by
  unfold signedGP negGP
  by_cases hs : s = 1
  · use -y
    simp [hs]
  · use y
    simp [hs]

private lemma signedGP_phi_affine_x (s : F circomPrime) (x y : Fp) :
    ∃ y' : Fp, signedGP s (phiGP (.affine { x := x, y := y })) =
      .affine { x := Phi.beta * x, y := y' } := by
  simpa [phiGP] using signedGP_affine_x s (Phi.beta * x) y

private lemma decodePoint_eq_affine_finite
    {P : FlaggedPoint (F circomPrime)} {Q : Point Fp}
    (hV : P.Valid) (h : decodePoint P = .affine Q) :
    P.isInf = 0 := by
  rcases hV.1 with h0 | h1
  · exact h0
  · exfalso
    rw [CompleteAdd.decodePoint_of_isInf h1] at h
    cases h

private lemma decodePoint_eq_affine_x
    {P : FlaggedPoint (F circomPrime)} {Q : Point Fp}
    (hfin : P.isInf = 0) (h : decodePoint P = .affine Q) :
    decodeFe P.x = Q.x := by
  rw [CompleteAdd.decodePoint_of_finite hfin] at h
  injection h with hQ
  exact congrArg Point.x hQ

private lemma decodePoint_eq_infinity_isInf
    {P : FlaggedPoint (F circomPrime)}
    (hV : P.Valid) (h : decodePoint P = .infinity) :
    P.isInf = 1 := by
  rcases hV.1 with h0 | h1
  · exfalso
    rw [CompleteAdd.decodePoint_of_finite h0] at h
    cases h
  · exact h1

namespace Prepare

def main (input : Var Inputs (F circomPrime)) :
    Circuit (F circomPrime) (Var Bases (F circomPrime)) := do
  let phiPx ← subcircuit MulModBeta32.circuit { a := input.P.x }
  let phiQx ← subcircuit MulModBeta32.circuit { a := input.Q.x }
  let negPy ← subcircuit NegYAffine.circuit input.P
  let negQy ← subcircuit NegYAffine.circuit input.Q
  let Pphi : Var FlaggedPoint (F circomPrime) :=
    { x := phiPx, y := input.P.y, isInf := input.P.isInf }
  let Qphi : Var FlaggedPoint (F circomPrime) :=
    { x := phiQx, y := input.Q.y, isInf := input.Q.isInf }
  let nP : Var FlaggedPoint (F circomPrime) :=
    { x := input.P.x, y := negPy, isInf := input.P.isInf }
  let nQ : Var FlaggedPoint (F circomPrime) :=
    { x := input.Q.x, y := negQy, isInf := input.Q.isInf }
  let nPphi : Var FlaggedPoint (F circomPrime) :=
    { x := phiPx, y := negPy, isInf := input.P.isInf }
  let nQphi : Var FlaggedPoint (F circomPrime) :=
    { x := phiQx, y := negQy, isInf := input.Q.isInf }
  -- Only the y-coordinate changes under sign selection.  Selecting whole
  -- nine-cell points needlessly duplicated the unchanged x-coordinate and
  -- infinity flag; four-limb y muxes keep all downstream inputs affine.
  -- `sign0` is pinned to zero by the coefficient witness (the whole
  -- decomposition may be negated, so we normalise the first sign away), hence
  -- `r0` is literally the input point and needs no selection at all.
  let r1y ← subcircuit (Mux.circuit (M := Emu))
    { selector := input.sign1, ifTrue := negPy, ifFalse := input.P.y }
  let r2y ← subcircuit (Mux.circuit (M := Emu))
    { selector := input.sign2, ifTrue := negQy, ifFalse := input.Q.y }
  let r3y ← subcircuit (Mux.circuit (M := Emu))
    { selector := input.sign3, ifTrue := negQy, ifFalse := input.Q.y }
  return {
    r0 := { x := input.P.x, y := input.P.y, isInf := input.P.isInf }
    r1 := { x := phiPx, y := r1y, isInf := input.P.isInf }
    r2 := { x := input.Q.x, y := r2y, isInf := input.Q.isInf }
    r3 := { x := phiQx, y := r3y, isInf := input.Q.isInf }
  }

instance elaborated : ElaboratedCircuit (F circomPrime) Inputs Bases main := by
  elaborate_circuit

def Assumptions (input : Inputs (F circomPrime)) : Prop :=
  input.P.Valid ∧ input.Q.Valid ∧
    input.sign0 = 0 ∧ IsBool input.sign1 ∧
    IsBool input.sign2 ∧ IsBool input.sign3 ∧
    (input.P.isInf = 1 → input.P.y = emuOfNat 0) ∧
    (input.Q.isInf = 1 → input.Q.y = emuOfNat 0)

def Spec (input : Inputs (F circomPrime)) (out : Bases (F circomPrime)) : Prop :=
  (∀ i : Fin 4, (baseEntry out i).Valid ∧
    decodePoint (baseEntry out i) = signedBase input i) ∧
  (input.Q.isInf = 1 → input.Q.y = emuOfNat 0 →
    decodeFe out.r3.y = decodeFe out.r2.y) ∧
  (input.Q.x = emuOfNat 0 → decodeFe out.r2.x = 0 ∧ decodeFe out.r3.x = 0)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem soundness : Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [MulModBeta32.circuit, MulModBeta32.Assumptions, MulModBeta32.Spec,
    NegYAffine.circuit, NegYAffine.Assumptions, NegYAffine.Spec,
    Mux.circuit, Mux.Assumptions, Mux.Spec]
  obtain ⟨hphiP, hphiQ, hnegP, hnegQ, hm1, hm2, hm3⟩ := h_holds
  obtain ⟨hPv, hQv, hs0, hs1, hs2, hs3, hPcan, hQcan⟩ := h_assumptions
  obtain ⟨hphiPv, hphiPfull⟩ := hphiP hPv.2.1
  obtain ⟨hphiQv, hphiQfull⟩ := hphiQ hQv.2.1
  have hphiPd := hphiPfull
  have hphiQd := hphiQfull
  rw [beta32_cast] at hphiPd hphiQd
  obtain ⟨hnegPv, hnegPe⟩ := hnegP ⟨hPv, hPcan⟩
  obtain ⟨hnegQv, hnegQe⟩ := hnegQ ⟨hQv, hQcan⟩
  have hphiPfp := phi_valueFP hPv hphiPv (by simpa [mul_comm] using hphiPd)
  have hphiQfp := phi_valueFP hQv hphiQv (by simpa [mul_comm] using hphiQd)
  have hnegPfp := neg_valueFP hPv hnegPv hnegPe
  have hnegQfp := neg_valueFP hQv hnegQv hnegQe
  have hnegPhiPfp := neg_valueFP hphiPfp.1 hnegPv hnegPe
  have hnegPhiQfp := neg_valueFP hphiQfp.1 hnegQv hnegQe
  have hm1' :
      valueFP (Vector.map (Expression.eval env)
        ((subcircuit MulModBeta32.circuit { a := input_var_P_x }).output i₀))
        (Vector.map (Expression.eval env)
          ((subcircuit (Mux.circuit (M := Emu))
            { selector := input_var_sign1,
              ifTrue := (subcircuit NegYAffine.circuit
                { x := input_var_P_x, y := input_var_P_y, isInf := input_var_P_isInf }).output
                (i₀ + 341 + 341), ifFalse := input_var_P_y }).output
            (i₀ + 341 + 341 + 68 + 68))) input_P_isInf =
        if input_sign1 = 1 then valueFP
          (Vector.map (Expression.eval env)
            ((subcircuit MulModBeta32.circuit { a := input_var_P_x }).output i₀))
          (Vector.map (Expression.eval env)
            ((subcircuit NegYAffine.circuit
              { x := input_var_P_x, y := input_var_P_y, isInf := input_var_P_isInf }).output
              (i₀ + 341 + 341))) input_P_isInf
        else valueFP
          (Vector.map (Expression.eval env)
            ((subcircuit MulModBeta32.circuit { a := input_var_P_x }).output i₀))
          input_P_y input_P_isInf := by
    have hy := hm1 hs1
    rw [show (if input_sign1 = 1 then valueFP _ _ input_P_isInf else valueFP _ input_P_y input_P_isInf) =
      valueFP _ (if input_sign1 = 1 then _ else input_P_y) input_P_isInf from by
        split <;> rfl]
    exact congrArg (fun y => valueFP _ y input_P_isInf) hy
  have hm2' :
      valueFP input_Q_x (Vector.map (Expression.eval env)
        ((subcircuit (Mux.circuit (M := Emu))
          { selector := input_var_sign2,
            ifTrue := (subcircuit NegYAffine.circuit
              { x := input_var_Q_x, y := input_var_Q_y, isInf := input_var_Q_isInf }).output
              (i₀ + 341 + 341 + 68), ifFalse := input_var_Q_y }).output
          (i₀ + 341 + 341 + 68 + 68 + 4))) input_Q_isInf =
        if input_sign2 = 1 then valueFP input_Q_x
          (Vector.map (Expression.eval env)
            ((subcircuit NegYAffine.circuit
              { x := input_var_Q_x, y := input_var_Q_y, isInf := input_var_Q_isInf }).output
              (i₀ + 341 + 341 + 68))) input_Q_isInf
        else { x := input_Q_x, y := input_Q_y, isInf := input_Q_isInf } := by
    have hy := hm2 hs2
    rw [show (if input_sign2 = 1 then valueFP input_Q_x _ input_Q_isInf else _) =
      valueFP input_Q_x (if input_sign2 = 1 then _ else input_Q_y) input_Q_isInf from by
        split <;> rfl]
    exact congrArg (fun y => valueFP input_Q_x y input_Q_isInf) hy
  have hm3' :
      valueFP (Vector.map (Expression.eval env)
        ((subcircuit MulModBeta32.circuit { a := input_var_Q_x }).output (i₀ + 341)))
        (Vector.map (Expression.eval env)
          ((subcircuit (Mux.circuit (M := Emu))
            { selector := input_var_sign3,
              ifTrue := (subcircuit NegYAffine.circuit
                { x := input_var_Q_x, y := input_var_Q_y, isInf := input_var_Q_isInf }).output
                (i₀ + 341 + 341 + 68), ifFalse := input_var_Q_y }).output
            (i₀ + 341 + 341 + 68 + 68 + 4 + 4))) input_Q_isInf =
        if input_sign3 = 1 then valueFP
          (Vector.map (Expression.eval env)
            ((subcircuit MulModBeta32.circuit { a := input_var_Q_x }).output (i₀ + 341)))
          (Vector.map (Expression.eval env)
            ((subcircuit NegYAffine.circuit
              { x := input_var_Q_x, y := input_var_Q_y, isInf := input_var_Q_isInf }).output
              (i₀ + 341 + 341 + 68))) input_Q_isInf
        else valueFP
          (Vector.map (Expression.eval env)
            ((subcircuit MulModBeta32.circuit { a := input_var_Q_x }).output (i₀ + 341)))
          input_Q_y input_Q_isInf := by
    have hy := hm3 hs3
    rw [show (if input_sign3 = 1 then valueFP _ _ input_Q_isInf else valueFP _ input_Q_y input_Q_isInf) =
      valueFP _ (if input_sign3 = 1 then _ else input_Q_y) input_Q_isInf from by
        split <;> rfl]
    exact congrArg (fun y => valueFP _ y input_Q_isInf) hy
  have hr0 : ({ x := input_P_x, y := input_P_y, isInf := input_P_isInf } :
        FlaggedPoint (F circomPrime)).Valid ∧
      decodePoint { x := input_P_x, y := input_P_y, isInf := input_P_isInf } =
        signedGP input_sign0
          (decodePoint { x := input_P_x, y := input_P_y, isInf := input_P_isInf }) :=
    selected_point (s := input_sign0) (Or.inl hs0) hPv hnegPfp.1 hnegPfp.2
      (by simp [hs0])
  have hr1 := selected_point hs1 hphiPfp.1 hnegPhiPfp.1 hnegPhiPfp.2 hm1'
  have hr2 := selected_point hs2 hQv hnegQfp.1 hnegQfp.2 hm2'
  have hr3 := selected_point hs3 hphiQfp.1 hnegPhiQfp.1 hnegPhiQfp.2 hm3'
  have hphiPfp' := hphiPfp.2
  have hphiQfp' := hphiQfp.2
  simp only [DivOrZero.secpParams_B] at hr1 hr3 hphiPfp' hphiQfp'
  rw [hphiPfp'] at hr1
  rw [hphiQfp'] at hr3
  refine ⟨?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · simpa [baseEntry, signedBase, DivOrZero.secpParams_B] using hr0
    · simpa [baseEntry, signedBase, DivOrZero.secpParams_B] using hr1
    · simpa [baseEntry, signedBase, DivOrZero.secpParams_B] using hr2
    · simpa [baseEntry, signedBase, DivOrZero.secpParams_B] using hr3
  · intro _hQinf hQy0
    have hQy0d : decodeFe input_Q_y = 0 := by
      rw [hQy0]
      simpa using CompleteAdd.decodeFe_emuOfNat_val (0 : Specs.Secp256k1.Fp)
    have hnegQ0 : decodeFe
        (Vector.map (Expression.eval env)
          ((subcircuit NegYAffine.circuit
            { x := input_var_Q_x, y := input_var_Q_y, isInf := input_var_Q_isInf }).output
            (i₀ + 341 + 341 + 68))) = 0 := by
      have h := hnegQe
      rw [hQy0d, neg_zero] at h
      simpa only [circuit_norm] using h
    have hy2 := hm2 hs2
    have hy3 := hm3 hs3
    have hy2raw := congrArg (fun P : FlaggedPoint (F circomPrime) => decodeFe P.y) hm2'
    have hy3raw := congrArg (fun P : FlaggedPoint (F circomPrime) => decodeFe P.y) hm3'
    have hy2sem : decodeFe
        (Vector.map (Expression.eval env)
          ((subcircuit (Mux.circuit (M := Emu))
            { selector := input_var_sign2,
              ifTrue := (subcircuit NegYAffine.circuit
                { x := input_var_Q_x, y := input_var_Q_y, isInf := input_var_Q_isInf }).output
                (i₀ + 341 + 341 + 68), ifFalse := input_var_Q_y }).output
            (i₀ + 341 + 341 + 68 + 68 + 4))) =
        decodeFe
          (if input_sign2 = 1 then
            valueFP input_Q_x
              (Vector.map (Expression.eval env)
                ((subcircuit NegYAffine.circuit
                  { x := input_var_Q_x, y := input_var_Q_y, isInf := input_var_Q_isInf }).output
                  (i₀ + 341 + 341 + 68)))
              input_Q_isInf
          else valueFP input_Q_x input_Q_y input_Q_isInf).y := by
      simpa only [valueFP] using hy2raw
    have hy3sem : decodeFe
        (Vector.map (Expression.eval env)
          ((subcircuit (Mux.circuit (M := Emu))
            { selector := input_var_sign3,
              ifTrue := (subcircuit NegYAffine.circuit
                { x := input_var_Q_x, y := input_var_Q_y, isInf := input_var_Q_isInf }).output
                (i₀ + 341 + 341 + 68), ifFalse := input_var_Q_y }).output
            (i₀ + 341 + 341 + 68 + 68 + 4 + 4))) =
        decodeFe
          (if input_sign3 = 1 then
            valueFP
              (Vector.map (Expression.eval env)
                ((subcircuit MulModBeta32.circuit { a := input_var_Q_x }).output
                  (i₀ + 341)))
              (Vector.map (Expression.eval env)
                ((subcircuit NegYAffine.circuit
                  { x := input_var_Q_x, y := input_var_Q_y, isInf := input_var_Q_isInf }).output
                  (i₀ + 341 + 341 + 68)))
              input_Q_isInf
          else
            valueFP
              (Vector.map (Expression.eval env)
                ((subcircuit MulModBeta32.circuit { a := input_var_Q_x }).output
                  (i₀ + 341)))
              input_Q_y input_Q_isInf).y := by
      simpa only [valueFP] using hy3raw
    have hy2z : decodeFe
        (Vector.map (Expression.eval env)
          ((subcircuit (Mux.circuit (M := Emu))
            { selector := input_var_sign2,
              ifTrue := (subcircuit NegYAffine.circuit
                { x := input_var_Q_x, y := input_var_Q_y, isInf := input_var_Q_isInf }).output
                (i₀ + 341 + 341 + 68), ifFalse := input_var_Q_y }).output
            (i₀ + 341 + 341 + 68 + 68 + 4))) = 0 := by
      rw [hy2sem]
      split
      · exact hnegQ0
      · exact hQy0d
    have hy3z : decodeFe
        (Vector.map (Expression.eval env)
          ((subcircuit (Mux.circuit (M := Emu))
            { selector := input_var_sign3,
              ifTrue := (subcircuit NegYAffine.circuit
                { x := input_var_Q_x, y := input_var_Q_y, isInf := input_var_Q_isInf }).output
                (i₀ + 341 + 341 + 68), ifFalse := input_var_Q_y }).output
            (i₀ + 341 + 341 + 68 + 68 + 4 + 4))) = 0 := by
      rw [hy3sem]
      split
      · exact hnegQ0
      · exact hQy0d
    simpa only [baseEntry, circuit_norm] using hy3z.trans hy2z.symm
  · intro hQx0
    have hQx0d : decodeFe input_Q_x = 0 := by
      rw [hQx0]
      simpa using CompleteAdd.decodeFe_emuOfNat_val (0 : Specs.Secp256k1.Fp)
    have hphiQ0 : decodeFe
        (Vector.map (Expression.eval env)
          ((subcircuit MulModBeta32.circuit { a := input_var_Q_x }).output (i₀ + 341))) = 0 := by
      have h := hphiQd
      rw [hQx0d, mul_zero] at h
      simpa only [circuit_norm] using h
    exact ⟨by simpa only [circuit_norm] using hQx0d,
      by simpa only [circuit_norm] using hphiQ0⟩

set_option maxRecDepth 8192 in
theorem completeness : Completeness (F circomPrime) main Assumptions := by
  circuit_proof_start [MulModBeta32.circuit, MulModBeta32.Assumptions, MulModBeta32.Spec,
    NegYAffine.circuit, NegYAffine.Assumptions, NegYAffine.Spec,
    Mux.circuit, Mux.Assumptions, Mux.Spec]
  obtain ⟨hPv, hQv, -, hs1, hs2, hs3, hPcan, hQcan⟩ := h_assumptions
  exact ⟨hPv.2.1, hQv.2.1, ⟨hPv, hPcan⟩, ⟨hQv, hQcan⟩,
    hs1, hs2, hs3⟩

def circuit : FormalCircuit (F circomPrime) Inputs Bases where
  main; elaborated; Assumptions; Spec; soundness; completeness

set_option maxRecDepth 8192 in
lemma localLength (input : Var Inputs (F circomPrime)) :
    circuit.localLength input = 830 := rfl

end Prepare

namespace Subset

def main (input : Var Bases (F circomPrime)) :
    Circuit (F circomPrime) (Var RawTable (F circomPrime)) := do
  let t3 ← subcircuit PhiPairAdd.circuit { P := input.r0, Q := input.r1 }
  let t12 ← subcircuit PhiPairAdd.circuit { P := input.r2, Q := input.r3 }
  -- canonicalise `t12`'s x-coordinate immediately: the three additions that
  -- consume it as their `Q` argument need `Q.isInf = 1 → decodeFe Q.x = 0`.
  let t12x ← subcircuit (Mux.circuit (M := Emu))
    { selector := t12.isInf, ifTrue := zeroConst, ifFalse := t12.x }
  let t12 : Var FlaggedPoint (F circomPrime) := { x := t12x, y := t12.y, isInf := t12.isInf }
  let t5 ← subcircuit CompleteAdd.circuit { P := input.r0, Q := input.r2 }
  let t9 ← subcircuit CompleteAdd.circuit { P := input.r0, Q := input.r3 }
  let t6 ← subcircuit CompleteAdd.circuit { P := input.r1, Q := input.r2 }
  let t10 ← subcircuit CompleteAdd.circuit { P := input.r1, Q := input.r3 }
  let t7 ← subcircuit CompleteAdd.circuit { P := t3, Q := input.r2 }
  let t11 ← subcircuit CompleteAdd.circuit { P := t3, Q := input.r3 }
  let t13 ← subcircuit CompleteAdd.circuit { P := input.r0, Q := t12 }
  let t14 ← subcircuit CompleteAdd.circuit { P := input.r1, Q := t12 }
  let t15 ← subcircuit CompleteAdd.circuit { P := t3, Q := t12 }
  return RawTable.mk infConst input.r0 input.r1 t3 input.r2 t5 t6 t7
    input.r3 t9 t10 t11 t12 t13 t14 t15

instance elaborated : ElaboratedCircuit (F circomPrime) Bases RawTable main := by
  elaborate_circuit

def Assumptions (input : Bases (F circomPrime)) : Prop :=
  (∀ i : Fin 4, (baseEntry input i).Valid) ∧
    PhiPairAdd.FiniteAssumptions { P := input.r0, Q := input.r1 } ∧
    PhiPairAdd.Assumptions { P := input.r2, Q := input.r3 } ∧
    (input.r2.isInf = 1 → decodeFe input.r2.x = 0) ∧
    (input.r3.isInf = 1 → decodeFe input.r3.x = 0)

def Spec (input : Bases (F circomPrime)) (out : RawTable (F circomPrime)) : Prop :=
  ∀ i : Fin 16, (rawEntry out i).Valid ∧
    decodePoint (rawEntry out i) =
      subsetPoint (fun j => decodePoint (baseEntry input j)) i.val ∧
    ((rawEntry out i).isInf = 1 → decodeFe (rawEntry out i).x = 0)

private lemma canonX_spec (env : Environment (F circomPrime))
    {P : FlaggedPoint (F circomPrime)} {x : Emu (F circomPrime)}
    {G : Specs.ShortWeierstrass.GroupPoint Specs.Secp256k1.Fp}
    (hP : P.Valid) (hdec : decodePoint P = G)
    (hx : x = if P.isInf = 1 then Vector.map (Expression.eval env) zeroConst else P.x) :
    ({ x := x, y := P.y, isInf := P.isInf } : FlaggedPoint (F circomPrime)).Valid ∧
      decodePoint ({ x := x, y := P.y, isInf := P.isInf } : FlaggedPoint (F circomPrime)) = G ∧
      ((({ x := x, y := P.y, isInf := P.isInf } : FlaggedPoint (F circomPrime)).isInf = 1) →
        decodeFe ({ x := x, y := P.y, isInf := P.isInf } : FlaggedPoint (F circomPrime)).x = 0) := by
  have hzv : Fe.Valid (Vector.map (Expression.eval env) zeroConst) :=
    CompleteAdd.fe_valid_eval_zeroConst env
  have hzd : decodeFe (Vector.map (Expression.eval env) zeroConst) = 0 := by
    rw [DivOrZero.eval_zeroConst, decodeFe, value_emuOfNat (by positivity), Nat.cast_zero]
  constructor
  · refine ⟨hP.1, ?_, hP.2.2.1, ?_⟩
    · rw [hx]
      by_cases hi : P.isInf = 1
      · rw [if_pos hi]
        exact hzv
      · rw [if_neg hi]
        exact hP.2.1
    · intro hfin
      have hxfin : x = P.x := by
        rw [hx]
        exact if_neg (by intro h; rw [hfin] at h; exact zero_ne_one h)
      rw [hxfin]
      exact hP.2.2.2 hfin
  · constructor
    · by_cases hi : P.isInf = 1
      · have hPinf : decodePoint P = .infinity := by simp [decodePoint, hi]
        rw [hPinf] at hdec
        simp [decodePoint, hi, hdec]
      · have hxfin : x = P.x := by
          rw [hx]
          exact if_neg hi
        simpa [decodePoint, hi, hxfin] using hdec
    · intro hi
      rw [hx, if_pos hi, hzd]

theorem soundness : Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [PhiPairAdd.circuit, PhiPairAdd.Assumptions, PhiPairAdd.Spec,
    CompleteAdd.circuit, CompleteAdd.Assumptions, CompleteAdd.Spec,
    Mux.circuit, Mux.Assumptions, Mux.Spec]
  obtain ⟨h3, h12, h12x, h5, h9, h6, h10, h7, h11, h13, h14, h15⟩ := h_holds
  obtain ⟨hbaseAss, hphiFin, hphiQAss, hcanon2, hcanon3⟩ := h_assumptions
  have hphiAss : PhiPairAdd.Assumptions
      { P := { x := input_r0_x, y := input_r0_y, isInf := input_r0_isInf },
        Q := { x := input_r1_x, y := input_r1_y, isInf := input_r1_isInf } } :=
    ⟨hphiFin.1, hphiFin.2.1,
      Or.inl ⟨hphiFin.2.2.1, hphiFin.2.2.2.1, hphiFin.2.2.2.2⟩⟩
  have hr0fin : input_r0_isInf = 0 := by simpa only using hphiFin.2.2.1
  have hr1fin : input_r1_isInf = 0 := by simpa only using hphiFin.2.2.2.1
  have h0v := hbaseAss 0; have h1v := hbaseAss 1
  have h2v := hbaseAss 2; have h3v := hbaseAss 3
  have s3 := h3 hphiAss; have s5 := h5 ⟨h0v, h2v, hr0fin, hcanon2⟩
  have s9 := h9 ⟨h0v, h3v, hr0fin, hcanon3⟩; have s6 := h6 ⟨h1v, h2v, hr1fin, hcanon2⟩
  have s10 := h10 ⟨h1v, h3v, hr1fin, hcanon3⟩; have s12 := h12 hphiQAss
  have c12 := canonX_spec env s12.1 s12.2 (h12x s12.1.1)
  have s7 := h7 ⟨s3.1, h2v, hr0fin, hcanon2⟩; have s11 := h11 ⟨s3.1, h3v, hr0fin, hcanon3⟩
  have s13 := h13 ⟨h0v, c12.1, hr0fin, c12.2.2⟩
  have s14 := h14 ⟨h1v, c12.1, hr1fin, c12.2.2⟩
  have s15 := h15 ⟨s3.1, c12.1, hr0fin, c12.2.2⟩
  rw [s3.2] at s7 s11 s15
  rw [c12.2.1] at s13 s14 s15
  have hz0 : decodeFe (Vector.map (Expression.eval env) zeroConst) = 0 := by
    rw [DivOrZero.eval_zeroConst, decodeFe, value_emuOfNat (by positivity), Nat.cast_zero]
  intro i
  fin_cases i
  · constructor
    · simpa only [rawEntry] using evalInf_valid env
    · constructor
      · simpa only [rawEntry, subsetPoint_0] using decode_evalInf env
      · intro _
        simpa only [rawEntry, infConst] using hz0
  · constructor
    · simpa only [rawEntry] using h0v
    · constructor
      · simpa only [rawEntry, baseEntry, subsetPoint_1]
      · intro h
        simp only [rawEntry] at h
        rw [hr0fin] at h
        exact (zero_ne_one (α := F circomPrime) h).elim
  · constructor
    · simpa only [rawEntry] using h1v
    · constructor
      · simpa only [rawEntry, baseEntry, subsetPoint_2]
      · intro h
        simp only [rawEntry] at h
        rw [hr1fin] at h
        exact (zero_ne_one (α := F circomPrime) h).elim
  · constructor
    · simpa only [rawEntry, baseEntry, subsetPoint_3] using s3.1
    · constructor
      · simpa only [rawEntry, baseEntry, subsetPoint_3] using s3.2
      · intro h
        simp only [rawEntry] at h
        rw [hr0fin] at h
        exact (zero_ne_one (α := F circomPrime) h).elim
  · refine ⟨by simpa only [rawEntry] using h2v, ?_, ?_⟩
    · simpa only [rawEntry, baseEntry, subsetPoint_4]
    · simpa only [rawEntry] using hcanon2
  · simpa only [rawEntry, baseEntry, subsetPoint_5] using s5
  · simpa only [rawEntry, baseEntry, subsetPoint_6] using s6
  · simpa only [rawEntry, baseEntry, subsetPoint_7] using s7
  · refine ⟨by simpa only [rawEntry] using h3v, ?_, ?_⟩
    · simpa only [rawEntry, baseEntry, subsetPoint_8]
    · simpa only [rawEntry] using hcanon3
  · simpa only [rawEntry, baseEntry, subsetPoint_9] using s9
  · simpa only [rawEntry, baseEntry, subsetPoint_10] using s10
  · simpa only [rawEntry, baseEntry, subsetPoint_11] using s11
  · simpa only [rawEntry, baseEntry, subsetPoint_12] using c12
  · simpa only [rawEntry, baseEntry, subsetPoint_13] using s13
  · simpa only [rawEntry, baseEntry, subsetPoint_14] using s14
  · simpa only [rawEntry, baseEntry, subsetPoint_15] using s15

theorem completeness : Completeness (F circomPrime) main Assumptions := by
  circuit_proof_start [PhiPairAdd.circuit, PhiPairAdd.Assumptions, PhiPairAdd.Spec,
    CompleteAdd.circuit, CompleteAdd.Assumptions, CompleteAdd.Spec,
    Mux.circuit, Mux.Assumptions, Mux.Spec]
  obtain ⟨h3, h12, h12x, h5, h9, h6, h10, h7, h11, h13, h14, h15⟩ := h_env
  obtain ⟨hbaseAss, hphiFin, hphiQAss, hcanon2, hcanon3⟩ := h_assumptions
  have hphiAss : PhiPairAdd.Assumptions
      { P := { x := input_r0_x, y := input_r0_y, isInf := input_r0_isInf },
        Q := { x := input_r1_x, y := input_r1_y, isInf := input_r1_isInf } } :=
    ⟨hphiFin.1, hphiFin.2.1,
      Or.inl ⟨hphiFin.2.2.1, hphiFin.2.2.2.1, hphiFin.2.2.2.2⟩⟩
  have hr0fin : input_r0_isInf = 0 := by simpa only using hphiFin.2.2.1
  have hr1fin : input_r1_isInf = 0 := by simpa only using hphiFin.2.2.2.1
  have h0v := hbaseAss 0; have h1v := hbaseAss 1
  have h2v := hbaseAss 2; have h3v := hbaseAss 3
  have s3 := h3 hphiAss
  have s12 := h12 hphiQAss
  have c12 := canonX_spec env s12.1 s12.2 (h12x s12.1.1)
  exact ⟨hphiAss, hphiQAss, s12.1.1,
    ⟨h0v, h2v, hr0fin, hcanon2⟩, ⟨h0v, h3v, hr0fin, hcanon3⟩,
    ⟨h1v, h2v, hr1fin, hcanon2⟩, ⟨h1v, h3v, hr1fin, hcanon3⟩,
    ⟨s3.1, h2v, hr0fin, hcanon2⟩, ⟨s3.1, h3v, hr0fin, hcanon3⟩,
    ⟨h0v, c12.1, hr0fin, c12.2.2⟩,
    ⟨h1v, c12.1, hr1fin, c12.2.2⟩, ⟨s3.1, c12.1, hr0fin, c12.2.2⟩⟩

def circuit : FormalCircuit (F circomPrime) Bases RawTable where
  main; elaborated; Assumptions; Spec; soundness; completeness

set_option maxRecDepth 8192 in
lemma localLength (input : Var Bases (F circomPrime)) :
    circuit.localLength input = 13495 := rfl

end Subset

lemma subsetAssumptions_of_prepare_spec
    {input : Inputs (F circomPrime)} {bases : Bases (F circomPrime)}
    (hprep : Prepare.Spec input bases)
    (hPfin : input.P.isInf = 0)
    (hPxne : decodeFe input.P.x ≠ 0)
    (hQvalid : input.Q.Valid)
    (hQcanon : input.Q.isInf = 1 → input.Q.x = emuOfNat 0 ∧ input.Q.y = emuOfNat 0) :
    Subset.Assumptions bases := by
  have hbase : ∀ i : Fin 4, (baseEntry bases i).Valid := fun i => (hprep.1 i).1
  have hPdecode :
      decodePoint input.P = .affine
        { x := decodeFe input.P.x, y := decodeFe input.P.y } :=
    CompleteAdd.decodePoint_of_finite hPfin
  obtain ⟨y0, hsg0⟩ :=
    signedGP_affine_x input.sign0 (decodeFe input.P.x) (decodeFe input.P.y)
  obtain ⟨y1, hsg1⟩ :=
    signedGP_phi_affine_x input.sign1 (decodeFe input.P.x) (decodeFe input.P.y)
  have hb0 :
      decodePoint (baseEntry bases 0) =
        .affine { x := decodeFe input.P.x, y := y0 } := by
    simpa only [baseEntry, signedBase, hPdecode, hsg0] using (hprep.1 0).2
  have hb1 :
      decodePoint (baseEntry bases 1) =
        .affine { x := Phi.beta * decodeFe input.P.x, y := y1 } := by
    simpa only [baseEntry, signedBase, hPdecode, hsg1] using (hprep.1 1).2
  have h0inf : (baseEntry bases 0).isInf = 0 :=
    decodePoint_eq_affine_finite (hbase 0) hb0
  have h1inf : (baseEntry bases 1).isInf = 0 :=
    decodePoint_eq_affine_finite (hbase 1) hb1
  have hx0 : decodeFe (baseEntry bases 0).x = decodeFe input.P.x :=
    decodePoint_eq_affine_x h0inf hb0
  have hx1 : decodeFe (baseEntry bases 1).x = Phi.beta * decodeFe input.P.x :=
    decodePoint_eq_affine_x h1inf hb1
  have hneqP : decodeFe (baseEntry bases 1).x ≠ decodeFe (baseEntry bases 0).x := by
    intro hx
    rw [hx1, hx0] at hx
    have hprod : (Phi.beta - 1) * decodeFe input.P.x = 0 := by
      rw [sub_mul, one_mul]
      exact sub_eq_zero.mpr hx
    rcases mul_eq_zero.mp hprod with hb | hx0'
    · exact beta_ne_one (sub_eq_zero.mp hb)
    · exact hPxne hx0'
  have hpass :
      PhiPairAdd.FiniteAssumptions { P := baseEntry bases 0, Q := baseEntry bases 1 } :=
    ⟨hbase 0, hbase 1, h0inf, h1inf, hneqP⟩
  have hqall :
      PhiPairAdd.Assumptions { P := baseEntry bases 2, Q := baseEntry bases 3 } ∧
        ((baseEntry bases 2).isInf = 1 → decodeFe (baseEntry bases 2).x = 0) ∧
        ((baseEntry bases 3).isInf = 1 → decodeFe (baseEntry bases 3).x = 0) := by
    by_cases hQfin : input.Q.isInf = 0
    · have hQdecode :
          decodePoint input.Q = .affine
            { x := decodeFe input.Q.x, y := decodeFe input.Q.y } :=
        CompleteAdd.decodePoint_of_finite hQfin
      obtain ⟨y2, hsg2⟩ :=
        signedGP_affine_x input.sign2 (decodeFe input.Q.x) (decodeFe input.Q.y)
      obtain ⟨y3, hsg3⟩ :=
        signedGP_phi_affine_x input.sign3 (decodeFe input.Q.x) (decodeFe input.Q.y)
      have hb2 :
          decodePoint (baseEntry bases 2) =
            .affine { x := decodeFe input.Q.x, y := y2 } := by
        simpa only [baseEntry, signedBase, hQdecode, hsg2] using (hprep.1 2).2
      have hb3 :
          decodePoint (baseEntry bases 3) =
            .affine { x := Phi.beta * decodeFe input.Q.x, y := y3 } := by
        simpa only [baseEntry, signedBase, hQdecode, hsg3] using (hprep.1 3).2
      have h2inf : (baseEntry bases 2).isInf = 0 :=
        decodePoint_eq_affine_finite (hbase 2) hb2
      have h3inf : (baseEntry bases 3).isInf = 0 :=
        decodePoint_eq_affine_finite (hbase 3) hb3
      have hx2 : decodeFe (baseEntry bases 2).x = decodeFe input.Q.x :=
        decodePoint_eq_affine_x h2inf hb2
      have hx3 : decodeFe (baseEntry bases 3).x = Phi.beta * decodeFe input.Q.x :=
        decodePoint_eq_affine_x h3inf hb3
      have hQxne : decodeFe input.Q.x ≠ 0 :=
        OrderFactsCerts.noXZero_secp (hQvalid.2.2.2 hQfin)
      have hneqQ : decodeFe (baseEntry bases 3).x ≠ decodeFe (baseEntry bases 2).x := by
        intro hx
        rw [hx3, hx2] at hx
        have hprod : (Phi.beta - 1) * decodeFe input.Q.x = 0 := by
          rw [sub_mul, one_mul]
          exact sub_eq_zero.mpr hx
        rcases mul_eq_zero.mp hprod with hb | hx0'
        · exact beta_ne_one (sub_eq_zero.mp hb)
        · exact hQxne hx0'
      exact ⟨⟨hbase 2, ⟨hbase 3, Or.inl ⟨h2inf, h3inf, hneqQ⟩⟩⟩,
        fun h => (zero_ne_one (α := F circomPrime) (h2inf.symm.trans h)).elim,
        fun h => (zero_ne_one (α := F circomPrime) (h3inf.symm.trans h)).elim⟩
    · have hQinf : input.Q.isInf = 1 := by
        rcases hQvalid.1 with h0 | h1
        · exact False.elim (hQfin h0)
        · exact h1
      have hQdecode : decodePoint input.Q = .infinity :=
        CompleteAdd.decodePoint_of_isInf hQinf
      have hb2 : decodePoint (baseEntry bases 2) = .infinity := by
        simpa [baseEntry, signedBase, hQdecode, signedGP, negGP] using
          (hprep.1 2).2
      have hb3 : decodePoint (baseEntry bases 3) = .infinity := by
        simpa [baseEntry, signedBase, hQdecode, signedGP, negGP, phiGP] using
          (hprep.1 3).2
      have h2inf : (baseEntry bases 2).isInf = 1 :=
        decodePoint_eq_infinity_isInf (hbase 2) hb2
      have h3inf : (baseEntry bases 3).isInf = 1 :=
        decodePoint_eq_infinity_isInf (hbase 3) hb3
      have hyEq : decodeFe (baseEntry bases 3).y = decodeFe (baseEntry bases 2).y := by
        simpa [baseEntry] using hprep.2.1 hQinf (hQcanon hQinf).2
      have hcx := hprep.2.2 (hQcanon hQinf).1
      exact ⟨⟨hbase 2, ⟨hbase 3, Or.inr ⟨h2inf, h3inf, hyEq⟩⟩⟩,
        fun _ => hcx.1, fun _ => hcx.2⟩
  exact ⟨hbase, hpass, hqall.1, hqall.2.1, hqall.2.2⟩

namespace Pack

def pack (input : Var RawTable (F circomPrime)) : Var Table (F circomPrime) :=
  let es : Vector (Var FlaggedPoint (F circomPrime)) 16 :=
    #v[input.t0, input.t1, input.t2, input.t3, input.t4, input.t5, input.t6, input.t7,
       input.t8, input.t9, input.t10, input.t11, input.t12, input.t13, input.t14, input.t15]
  {
    tx := Vector.ofFn fun i : Fin 16 => es[i.val].x
    ty := Vector.ofFn fun i : Fin 16 => es[i.val].y
    tinf := Vector.ofFn fun i : Fin 16 => es[i.val].isInf }

set_option maxRecDepth 8192 in
lemma eval_pack_entry_whole (env : Environment (F circomPrime))
    (input : Var RawTable (F circomPrime)) (i : Fin 16) :
    entry (eval env (pack input)) i.val i.isLt = rawEntry (eval env input) i := by
  fin_cases i <;> simp [pack, entry, rawEntry, circuit_norm,
    ← getElem_eval_vector]

end Pack

def Assumptions (input : Inputs (F circomPrime)) : Prop :=
  Prepare.Assumptions input ∧ input.P.isInf = 0 ∧ decodeFe input.P.x ≠ 0 ∧
    (input.Q.isInf = 1 → input.Q.x = emuOfNat 0 ∧ input.Q.y = emuOfNat 0)

end GLVBuildTable
end Solution.Secp256k1ScalarMul
