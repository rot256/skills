import Solution.SHA256.Add32

/-! # Deferred chaining words

SHA-256's state words `d` and `h` are consumed **only additively** — by the
round-0 sum of the next block and, for word 7, by the digest selector.  A block
therefore does not have to spend a 32-bit decomposition (32 allocations + 32
booleanity rows) on its word-7 feed-forward addition: it can hand the *unreduced*
sum on as a sparse word carrying the value in lane 0.

`deferWord a b` is that sparse word for the sum `a + b`.  It is kept
`irreducible` so that the (large) subcircuit-output expressions that get passed
to it are never duplicated across the 32 lanes during elaboration.
-/

section
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2)] [Fact (p > 2^35)]

namespace Solution.SHA256

/-- The unreduced sum `a + b`, carried in lane 0 of a sparse 32-lane word. -/
def deferWord (a b : Var (fields 32) (F p)) : Var (fields 32) (F p) :=
  sparseWordG (fromBitsExpr a + fromBitsExpr b)

lemma eval_deferWord (env : Environment (F p)) (a b : Var (fields 32) (F p))
    (x y : fields 32 (F p))
    (ha : Vector.map (Expression.eval env) a = x)
    (hb : Vector.map (Expression.eval env) b = y) :
    valueBits (Vector.map (Expression.eval env) (deferWord a b))
      = ((valueBits x + valueBits y : ℕ) : F p).val := by
  rw [deferWord, valueBits_sparseWordG]
  have hA : Expression.eval env (fromBitsExpr a) = ((valueBits x : ℕ) : F p) :=
    Add32.fromBitsExpr_eval_normalized env a x ha
  have hB : Expression.eval env (fromBitsExpr b) = ((valueBits y : ℕ) : F p) :=
    Add32.fromBitsExpr_eval_normalized env b y hb
  have : Expression.eval env (fromBitsExpr a + fromBitsExpr b)
      = ((valueBits x : ℕ) : F p) + ((valueBits y : ℕ) : F p) := by
    simp only [Expression.eval, hA, hB]
  rw [this]
  push_cast
  ring_nf

/-- Value of a deferred word, as a natural number, under a bound keeping the sum
below the field characteristic. -/
lemma valueBits_deferWord (env : Environment (F p)) (a b : Var (fields 32) (F p))
    (x y : fields 32 (F p))
    (ha : Vector.map (Expression.eval env) a = x)
    (hb : Vector.map (Expression.eval env) b = y)
    (hlt : valueBits x + valueBits y < 2^35) :
    valueBits (Vector.map (Expression.eval env) (deferWord a b))
      = valueBits x + valueBits y := by
  rw [eval_deferWord env a b x y ha hb]
  have hp : (2:ℕ)^35 < p := Fact.out
  exact ZMod.val_natCast_of_lt (by omega)

attribute [irreducible] deferWord

end Solution.SHA256
end
