import Solution.Secp256k1ScalarMul.GroupedEq

namespace Solution.Secp256k1ScalarMul

section
variable {p : ℕ} [Fact p.Prime]

namespace GroupedEqX

@[reducible] def CoeffsX (L : ℕ) : TypeMap := fields L

structure InputsX (L : ℕ) (F : Type) where
  lhs : CoeffsX L F
  rhs : CoeffsX L F
deriving ProvableStruct

def groupExprX (B g L : ℕ) (x : Var (CoeffsX L) (F p)) (k : ℕ) :
    Expression (F p) :=
  MulMod.polyEvalExpr
    (Vector.ofFn fun i : Fin g =>
      if h : g * k + i.val < L then x[g * k + i.val]'h else 0)
    ((2 : F p) ^ B)

def groupExprW (B L : ℕ) (gf posOf : ℕ → ℕ) (x : Var (CoeffsX L) (F p)) (k : ℕ) :
    Expression (F p) :=
  MulMod.polyEvalExpr
    (Vector.ofFn fun i : Fin (gf k) =>
      if h : posOf k + i.val < L then x[posOf k + i.val]'h else 0)
    ((2 : F p) ^ B)

lemma groupExprW_eval (env : Environment (F p)) (B L : ℕ) (gf posOf : ℕ → ℕ)
    (x : Var (CoeffsX L) (F p)) (k : ℕ) :
    Expression.eval env (groupExprW B L gf posOf x k)
      = ∑ i ∈ Finset.range (gf k),
          (if h : posOf k + i < L then Expression.eval env (x[posOf k + i]'h) else 0)
            * ((2 : F p) ^ B) ^ i := by
  rw [groupExprW, MulMod.polyEvalExpr_eval,
    ← Fin.sum_univ_eq_sum_range (fun i =>
      (if h : posOf k + i < L then Expression.eval env (x[posOf k + i]'h) else 0)
        * ((2 : F p) ^ B) ^ i)]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [Vector.getElem_ofFn]
  by_cases h : posOf k + i.val < L
  · rw [dif_pos h, dif_pos h]
  · rw [dif_neg h, dif_neg h]
    rfl

def Spec (B : ℕ) (L : ℕ) (input : InputsX L (F p)) : Prop :=
  polyValue B input.lhs = polyValue B input.rhs

end GroupedEqX

end

-- (The RSA tree's `GadgetCost` certificate section for the uniform-parameter
-- `GroupedEqX.circuit` is not ported: the graduated `GroupedEqXV` path this
-- tree uses carries its own certificates, inlined in `Cost.lean`.)

end Solution.Secp256k1ScalarMul
