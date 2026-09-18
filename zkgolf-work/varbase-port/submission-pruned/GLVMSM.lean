import Solution.Secp256k1ScalarMul.VarLookup
import Solution.Secp256k1ScalarMul.VarLookupCW
import Solution.Secp256k1ScalarMul.CompleteAdd
import Solution.Secp256k1ScalarMul.IsZeroFe
import Solution.Secp256k1ScalarMul.Mux
import Solution.Secp256k1ScalarMul.DivOrZeroTheorems
import Solution.Secp256k1ScalarMul.CompleteAddTheorems
import Solution.Secp256k1ScalarMul.AddMod
import Solution.Secp256k1ScalarMul.IsZeroFeSum
import Solution.Secp256k1ScalarMul.Params
import Solution.Secp256k1ScalarMul.MulMod
import Solution.Secp256k1ScalarMul.MulModTargetW
import Solution.Secp256k1ScalarMul.ProofBlocker
import Solution.Secp256k1ScalarMul.DivOrZeroF3
import Solution.Secp256k1ScalarMul.DivOrZeroS32
import Solution.Secp256k1ScalarMul.MulModSub2F32
import Solution.Secp256k1ScalarMul.EqFe
import Solution.Secp256k1ScalarMul.MulModFold32NInv
import Solution.Secp256k1ScalarMul.Limbs33
import Solution.Secp256k1ScalarMul.ValidP
import Solution.Secp256k1ScalarMul.ParamsFold
import Solution.Secp256k1ScalarMul.GroupedEqXV
import Solution.Secp256k1ScalarMul.MulModTargetW2
import Solution.Secp256k1ScalarMul.InterpMul
import Solution.Secp256k1ScalarMul.RangeCheck
import Solution.Secp256k1ScalarMul.InterpMul14CW
import Solution.Secp256k1ScalarMul.GroupedEqXVNoTop
import Solution.Secp256k1ScalarMul.Limbs32
import Solution.Secp256k1ScalarMul.FusedStepTheorems
import Solution.Secp256k1ScalarMul.CancelTheorems
import Solution.Secp256k1ScalarMul.ScalarMulTheorems

namespace Solution.Secp256k1ScalarMul
namespace GLVMSM

open Specs.ShortWeierstrass Specs.Secp256k1

def coeffBits : ℕ := 64

structure Inputs (F : Type) where
  tx : Vector (Emu F) 16
  ty : Vector (Emu F) 16
  tinf : Vector F 16
  m0 : Vector F coeffBits
  m1 : Vector F coeffBits
  m2 : Vector F coeffBits
  m3 : Vector F coeffBits
deriving ProvableStruct

def tableEntry (input : Inputs (F circomPrime)) (i : ℕ) (h : i < 16) :
    FlaggedPoint (F circomPrime) :=
  { x := input.tx[i]'h, y := input.ty[i]'h, isInf := input.tinf[i]'h }

def nibbleAt (input : Inputs (F circomPrime)) (k : ℕ) (hk : k < coeffBits) : ℕ :=
  8 * (input.m3[coeffBits - 1 - k]'(by simp only [coeffBits] at hk ⊢; omega)).val +
  4 * (input.m2[coeffBits - 1 - k]'(by simp only [coeffBits] at hk ⊢; omega)).val +
  2 * (input.m1[coeffBits - 1 - k]'(by simp only [coeffBits] at hk ⊢; omega)).val +
      (input.m0[coeffBits - 1 - k]'(by simp only [coeffBits] at hk ⊢; omega)).val

def selectedAt (input : Inputs (F circomPrime)) (k : ℕ) (hk : k < coeffBits) :
    GroupPoint Fp :=
  if hn : nibbleAt input k hk < 16 then
    decodePoint (tableEntry input (nibbleAt input k hk) hn)
  else .infinity

def Assumptions (input : Inputs (F circomPrime)) : Prop :=
  (∀ i : Fin 16, (tableEntry input i.val i.isLt).Valid) ∧
  (∀ i : Fin 16, (tableEntry input i.val i.isLt).isInf = 1 →
    decodeFe (tableEntry input i.val i.isLt).x = 0) ∧
  (∀ i : Fin coeffBits, IsBool input.m0[i]) ∧
  (∀ i : Fin coeffBits, IsBool input.m1[i]) ∧
  (∀ i : Fin coeffBits, IsBool input.m2[i]) ∧
  (∀ i : Fin coeffBits, IsBool input.m3[i])

-- index 0 = infinity placeholder, index 1 = VarLookup seed, index k+2 = fold-step k output

/-- The VarLookup output sits at offset `n + 112` (localLength 122, size 9). -/
lemma varLookup_output (input : Var VarLookup.Inputs (F circomPrime)) (n : ℕ) :
    VarLookup.circuit.output input n = varFromOffset FlaggedPoint (n + 112) := by
  show VarLookup.elaborated.output input n = _
  rw [← VarLookup.elaborated.output_eq input n]
  exact VarLookup.output_eq input n

lemma varLookup_localLength (input : Var VarLookup.Inputs (F circomPrime)) :
    VarLookup.circuit.localLength input = 122 := rfl

-- The VarLookup seed output equals the (opaque) accVar index-1 var.

-- Fold over the normal steps, starting the accumulator at the VarLookup seed.

-- Generalized GLVStep transition: consuming a GLVStep at bit position `pos`.

lemma tableEntry_index_congr (input : Inputs (F circomPrime)) (i j : ℕ) (hi : i < 16) (hj : j < 16)
    (h : i = j) : tableEntry input i hi = tableEntry input j hj := by subst h; rfl

-- The VarLookup seed satisfies the invariant for index 1.

end GLVMSM
end Solution.Secp256k1ScalarMul
