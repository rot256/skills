import Solution.Secp256k1ScalarMul.VarLookup
import Solution.Secp256k1ScalarMul.VarLookupCW
import Solution.Secp256k1ScalarMul.CompleteAdd
import Solution.Secp256k1ScalarMul.Double
import Solution.Secp256k1ScalarMul.FusedStep



namespace Solution.Secp256k1ScalarMul
namespace GLVStep

open Specs.ShortWeierstrass Specs.Secp256k1

structure Inputs (F : Type) where
  acc : FlaggedPoint F
  tx : Vector (Emu F) 16
  ty : Vector (Emu F) 16
  tinf : Vector F 16
  b3 : F
  b2 : F
  b1 : F
  b0 : F
deriving ProvableStruct

def toLk (input : Inputs (F circomPrime)) : VarLookup.Inputs (F circomPrime) :=
  { tx := input.tx, ty := input.ty, tinf := input.tinf,
    b3 := input.b3, b2 := input.b2, b1 := input.b1, b0 := input.b0 }

def nibble (input : Inputs (F circomPrime)) : ℕ := VarLookup.nibble (toLk input)

def entry (input : Inputs (F circomPrime)) (i : ℕ) (h : i < 16) :
    FlaggedPoint (F circomPrime) := VarLookup.entry (toLk input) i h

def dbl (P : GroupPoint Fp) : GroupPoint Fp := add curve P P

def main (input : Var Inputs (F circomPrime)) :
    Circuit (F circomPrime) (Var FlaggedPoint (F circomPrime)) := do
  let ent ← subcircuit VarLookup.circuit
    { tx := input.tx, ty := input.ty, tinf := input.tinf,
      b3 := input.b3, b2 := input.b2, b1 := input.b1, b0 := input.b0 }
  subcircuit FusedStep.circuit { acc := input.acc, t := ent }

instance elaborated : ElaboratedCircuit (F circomPrime) Inputs FlaggedPoint main := by
  elaborate_circuit

def Assumptions (input : Inputs (F circomPrime)) : Prop :=
  input.acc.Valid ∧
  (∀ i : Fin 16, (entry input i.val i.isLt).Valid) ∧
  (∀ i : Fin 16, (VarLookup.entry (toLk input) i.val i.isLt).isInf = 1 →
    decodeFe (VarLookup.entry (toLk input) i.val i.isLt).x = 0) ∧
  IsBool input.b3 ∧ IsBool input.b2 ∧ IsBool input.b1 ∧ IsBool input.b0

def Spec (input : Inputs (F circomPrime)) (out : FlaggedPoint (F circomPrime)) : Prop :=
  out.Valid ∧ ∃ h : nibble input < 16,
    decodePoint out = add curve (dbl (decodePoint input.acc))
      (decodePoint (entry input (nibble input) h))

theorem soundness : Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [VarLookup.circuit, VarLookup.Assumptions, VarLookup.Spec,
    FusedStep.circuit, FusedStep.Assumptions, FusedStep.Spec]
  obtain ⟨hacc, htab, htabCanon, hb3, hb2, hb1, hb0⟩ := h_assumptions
  let input0 : Inputs (F circomPrime) :=
    { acc := { x := input_acc_x, y := input_acc_y, isInf := input_acc_isInf },
      tx := input_tx, ty := input_ty, tinf := input_tinf,
      b3 := input_b3, b2 := input_b2, b1 := input_b1, b0 := input_b0 }
  obtain ⟨hlk, hfs⟩ := h_holds
  obtain ⟨hnib, hent⟩ := hlk ⟨hb3, hb2, hb1, hb0, htab, htabCanon⟩
  have hentv := htab ⟨_, hnib⟩
  have hentCanon := htabCanon ⟨_, hnib⟩
  obtain ⟨houtv, houte⟩ := hfs ⟨hacc, hent ▸ hentv, by
    intro hInf
    have hInfEq := congrArg (fun P : FlaggedPoint (F circomPrime) => P.isInf) hent
    have hInf' : (VarLookup.entry (toLk input0) (nibble input0) hnib).isInf = 1 := by
      simpa [input0, toLk, nibble] using hInfEq.symm.trans hInf
    have hxDecodeEq := congrArg (fun P : FlaggedPoint (F circomPrime) => decodeFe P.x) hent
    exact hxDecodeEq.trans (by
      simpa [input0, toLk, nibble] using hentCanon hInf')⟩
  refine ⟨houtv, hnib, ?_⟩
  rw [houte, hent]
  rfl

theorem completeness : Completeness (F circomPrime) main Assumptions := by
  circuit_proof_start [VarLookup.circuit, VarLookup.Assumptions, VarLookup.Spec,
    FusedStep.circuit, FusedStep.Assumptions, FusedStep.Spec]
  obtain ⟨hacc, htab, htabCanon, hb3, hb2, hb1, hb0⟩ := h_assumptions
  let input0 : Inputs (F circomPrime) :=
    { acc := { x := input_acc_x, y := input_acc_y, isInf := input_acc_isInf },
      tx := input_tx, ty := input_ty, tinf := input_tinf,
      b3 := input_b3, b2 := input_b2, b1 := input_b1, b0 := input_b0 }
  obtain ⟨hlk, -⟩ := h_env
  obtain ⟨hnib, hent⟩ := hlk ⟨hb3, hb2, hb1, hb0, htab, htabCanon⟩
  have hentv := htab ⟨_, hnib⟩
  have hentCanon := htabCanon ⟨_, hnib⟩
  exact ⟨⟨hb3, hb2, hb1, hb0, htab, htabCanon⟩, ⟨hacc, hent ▸ hentv, by
    intro hInf
    have hInfEq := congrArg (fun P : FlaggedPoint (F circomPrime) => P.isInf) hent
    have hInf' : (VarLookup.entry (toLk input0) (nibble input0) hnib).isInf = 1 := by
      simpa [input0, toLk, nibble] using hInfEq.symm.trans hInf
    have hxDecodeEq := congrArg (fun P : FlaggedPoint (F circomPrime) => decodeFe P.x) hent
    exact hxDecodeEq.trans (by
      simpa [input0, toLk, nibble] using hentCanon hInf')⟩⟩

def circuit : FormalCircuit (F circomPrime) Inputs FlaggedPoint where
  main; elaborated; Assumptions; Spec; soundness; completeness

lemma localLength (input : Var Inputs (F circomPrime)) :
    circuit.localLength input = 2149 := rfl

def outputAt (n : ℕ) : Var FlaggedPoint (F circomPrime) :=
  varFromOffset FlaggedPoint (n + 2140)

lemma output_eq_outputAt (input : Var Inputs (F circomPrime)) (n : ℕ) :
    circuit.output input n = outputAt n := by
  show elaborated.output input n = _
  simp only [elaborated, outputAt, FusedStep.varFromOffset_flaggedPoint, numLimbs,
    show secpParams32.B = 32 from rfl,
    show ProvableStruct.combinedSize VarLookup.XY = 8 from rfl]

end GLVStep
end Solution.Secp256k1ScalarMul
