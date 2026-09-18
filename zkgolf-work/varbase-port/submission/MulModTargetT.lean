import Solution.Secp256k1ScalarMul.MulModTargetW



namespace Solution.Secp256k1ScalarMul
namespace MulModTargetT
open MulMod MulModTargetD MulModTargetW

variable {p : ℕ} [Fact p.Prime]
variable {m : ℕ} [NeZero m]

omit [Fact p.Prime] [NeZero m] in
private lemma bits_of_lt_eight : ∀ q : ℕ, q < 8 →
    q = q % 2 + 2 * (q / 2 % 2) + 4 * (q / 4 % 2)
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | 7, _ => rfl
  | n + 8, h => absurd h (by omega)

omit [Fact p.Prime] in
private lemma polyValue_eq_range_sum {B kk : ℕ} (vv : Vector (F p) kk) (f : ℕ → ℕ)
    (hf : ∀ (i : ℕ) (h : i < kk), (vv[i]'h).val * 2 ^ (B * i) = f i) :
    polyValue B vv = ∑ i ∈ Finset.range kk, f i := by
  rw [polyValue, ← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_congr rfl fun i _ => hf i.val i.isLt

/-- A reducible alias for `fields (2 * m - 1)`, so the `ProvableStruct` deriving handler
can process the `target` field (it cannot digest the `2*m-1` subtraction inline). -/
@[reducible] def TargetVec (m : ℕ) : TypeMap := fields (2 * m - 1)

/-- Inputs: `a`, `b`, `modulus` are `BigInt m`, but `target` is a caller-supplied raw
convolution vector of `2*m-1` field cells. -/
structure Inputs (m : ℕ) (F : Type) where
  a : BigInt m F
  b : BigInt m F
  modulus : BigInt m F
  target : TargetVec m F
deriving ProvableStruct


/-- The "flank base" vector: convolution of `q·n` plus the raw target vector `T`
(no `×3`, unlike `sVecX` which multiplied an internal x-square by 3). -/
def sVecT (q n : Var (BigInt m) (F p)) (T : Vector (Expression (F p)) (2 * m - 1)) :
    Vector (Expression (F p)) (2 * m - 1) :=
  Vector.mapFinRange (2 * m - 1) fun k =>
    (bigIntMulNoReduce q n)[k.val] + T[k.val]


lemma coeff_sVecT_bound {B : ℕ} (env : Environment (F p))
    (q n : Var (BigInt m) (F p)) (T : Vector (Expression (F p)) (2 * m - 1))
    (k : Fin (2 * m - 1))
    (hq : ∀ i : Fin m, (Expression.eval env q[i.val]).val < 2 ^ B)
    (hn : ∀ i : Fin m, (Expression.eval env n[i.val]).val < 2 ^ B)
    (hT : ∀ j : Fin (2 * m - 1),
      (Expression.eval env T[j.val]).val < 3 * m * 2 ^ (2 * B))
    (hfield : m * (2 ^ B * 2 ^ B) < p) :
    (Expression.eval env ((sVecT q n T)[k.val])).val
      < m * 2 ^ (2 * B) + 3 * (m * 2 ^ (2 * B)) := by
  have h2B : 2 ^ B * 2 ^ B = 2 ^ (2 * B) := by rw [two_mul, pow_add]
  have hconv := val_coeff_lt_gen env q n k hq hn hfield
  rw [h2B] at hconv
  simp only [sVecT, Vector.getElem_mapFinRange]
  have hadd : (Expression.eval env ((bigIntMulNoReduce q n)[k.val] + T[k.val])).val
      ≤ (Expression.eval env ((bigIntMulNoReduce q n)[k.val])).val
        + (Expression.eval env (T[k.val])).val := by
    rw [show Expression.eval env ((bigIntMulNoReduce q n)[k.val] + T[k.val])
          = Expression.eval env ((bigIntMulNoReduce q n)[k.val])
            + Expression.eval env (T[k.val]) from rfl]
    exact ZMod.val_add_le _ _
  have hTk : (Expression.eval env T[k.val]).val < 3 * (m * 2 ^ (2 * B)) := by
    have := hT k; rw [mul_assoc] at this; exact this
  omega


lemma polyValue_sVecT {B : ℕ} (env : Environment (F p))
    (q n : Var (BigInt m) (F p)) (T : Vector (Expression (F p)) (2 * m - 1))
    (hq : ∀ i : Fin m, (Expression.eval env q[i.val]).val < 2 ^ B)
    (hn : ∀ i : Fin m, (Expression.eval env n[i.val]).val < 2 ^ B)
    (hT : ∀ j : Fin (2 * m - 1),
      (Expression.eval env T[j.val]).val < 3 * m * 2 ^ (2 * B))
    (hfield : m * (2 ^ B * 2 ^ B) < p)
    (hp4 : m * 2 ^ (2 * B) + 3 * m * 2 ^ (2 * B) < p) :
    polyValue B (Vector.map (Expression.eval env) (sVecT q n T))
      = polyValue B (Vector.map (Expression.eval env) (bigIntMulNoReduce q n))
        + polyValue B (Vector.map (Expression.eval env) T) := by
  have h2B : 2 ^ B * 2 ^ B = 2 ^ (2 * B) := by rw [two_mul, pow_add]
  have hcoeff : ∀ (i : ℕ) (h : i < 2 * m - 1),
      ((Vector.map (Expression.eval env) (sVecT q n T))[i]'(by omega)).val * 2 ^ (B * i)
      = (Expression.eval env ((bigIntMulNoReduce q n)[i]'h)).val * 2 ^ (B * i)
        + (Expression.eval env (T[i]'h)).val * 2 ^ (B * i) := by
    intro i h
    rw [Vector.getElem_map]
    simp only [sVecT, Vector.getElem_mapFinRange]
    rw [show Expression.eval env ((bigIntMulNoReduce q n)[i]'h + T[i]'h)
          = Expression.eval env ((bigIntMulNoReduce q n)[i]'h)
            + Expression.eval env (T[i]'h) from rfl]
    rw [ZMod.val_add_of_lt (by
      have hconv : (Expression.eval env ((bigIntMulNoReduce q n)[i]'h)).val < m * 2 ^ (2 * B) := by
        have hh := val_coeff_lt_gen env q n ⟨i, h⟩ hq hn hfield
        rw [h2B] at hh; exact hh
      have hTk : (Expression.eval env (T[i]'h)).val < 3 * m * 2 ^ (2 * B) := hT ⟨i, h⟩
      omega)]
    ring
  have hsum : polyValue B (Vector.map (Expression.eval env) (sVecT q n T))
      = (∑ i ∈ Finset.range (2 * m - 1),
          (fun j => if hj : j < 2 * m - 1
            then (Expression.eval env ((bigIntMulNoReduce q n)[j]'hj)).val * 2 ^ (B * j)
            else 0) i)
        + ∑ i ∈ Finset.range (2 * m - 1),
            (fun j => if hj : j < 2 * m - 1
              then (Expression.eval env (T[j]'hj)).val * 2 ^ (B * j) else 0) i := by
    rw [← Finset.sum_add_distrib]
    apply polyValue_eq_range_sum
    intro i h
    rw [hcoeff i h]
    simp only [dif_pos h]
  rw [hsum]
  congr 1
  · symm
    apply polyValue_eq_range_sum
    intro i h
    simp only [dif_pos h, Vector.getElem_map]
  · symm
    apply polyValue_eq_range_sum
    intro i h
    simp only [dif_pos h, Vector.getElem_map]




private def evalValue (B : ℕ) (env : ProverEnvironment (F p))
    (x : Var (BigInt m) (F p)) : ℕ :=
  Solution.Secp256k1ScalarMul.Limbs.fromLimbs B
    ((x.map (Expression.eval env.toEnvironment)).toList.map ZMod.val)




def main (P : BigIntParams p m)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqXV.GVXHyps p (2 * m) P.B gf posOf G V VR)
    (c : Vector (F p) (2 * m))
    [Fact (p > 2)]
    (input : Var (Inputs m) (F p)) :
    Circuit (F p) Unit :=
  letI : NeZero (2 * m) := ⟨by have := Nat.pos_of_neZero m; omega⟩
  do
  let a := input.a
  let b := input.b
  let n := input.modulus
  let x := input.target

  -- 1. witness q_lo = ((a·b + 3n² − polyValue(target))/n) % 2^(Bm) as BigInt m
  let q ← ProvableType.witness (α := BigInt m) fun env =>
    let qval : ℕ := (evalValue P.B env a * evalValue P.B env b
        + 3 * (evalValue P.B env n * evalValue P.B env n)
        - polyValue P.B (Vector.map (Expression.eval env.toEnvironment) x))
        / evalValue P.B env n
        % 2 ^ (P.B * m)
    Vector.ofFn fun k : Fin m => ((qval / 2 ^ (P.B * k.val) % 2 ^ P.B : ℕ) : F p)

  -- 2. witness the three top-quotient bits
  let qh0 ← ProvableType.witness (α := field) fun env =>
    ((((evalValue P.B env a * evalValue P.B env b
        + 3 * (evalValue P.B env n * evalValue P.B env n)
        - polyValue P.B (Vector.map (Expression.eval env.toEnvironment) x))
        / evalValue P.B env n
        / 2 ^ (P.B * m)) % 2 : ℕ) : F p)
  let qh1 ← ProvableType.witness (α := field) fun env =>
    ((((evalValue P.B env a * evalValue P.B env b
        + 3 * (evalValue P.B env n * evalValue P.B env n)
        - polyValue P.B (Vector.map (Expression.eval env.toEnvironment) x))
        / evalValue P.B env n
        / 2 ^ (P.B * m) / 2) % 2 : ℕ) : F p)
  let qh2 ← ProvableType.witness (α := field) fun env =>
    ((((evalValue P.B env a * evalValue P.B env b
        + 3 * (evalValue P.B env n * evalValue P.B env n)
        - polyValue P.B (Vector.map (Expression.eval env.toEnvironment) x))
        / evalValue P.B env n
        / 2 ^ (P.B * m) / 4) % 2 : ℕ) : F p)

  -- 3. the bits are boolean
  assertZero (qh0 * (qh0 - 1))
  assertZero (qh1 * (qh1 - 1))
  assertZero (qh2 * (qh2 - 1))

  -- 4. normalize q_lo
  Normalize.circuit P q

  -- 5. the single convolution
  let Pab ← interpolatedMul a b

  -- 6. certify over the L = 2m flanks
  GroupedEqXV.circuit P.B gf posOf G V VR hgv P.hB1
    { lhs := lVecW Pab c,
      rhs := sVecTD (sVecT q n x)
        (qh0 + ((2 : F p) : Expression (F p)) * qh1
          + ((4 : F p) : Expression (F p)) * qh2) n }

instance elaborated (P : BigIntParams p m)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqXV.GVXHyps p (2 * m) P.B gf posOf G V VR)
    (c : Vector (F p) (2 * m))
    [Fact (p > 2)] :
    ElaboratedCircuit (F p) (Inputs m) unit (main P gf posOf G V VR hgv c) where
  -- q (m) + bits (3) + normalize q (m·B) + one interpolation (2m−1) + grouped carries
  localLength _ :=
    m + 3 + m * (P.B - 1) + (2 * m - 1)
      + GroupedEqXV.widthAllocFrom V.Wf (G - 2) 0
  localLength_eq := by
    intro input offset
    simp only [main, interpolatedMul, circuit_norm, Normalize.circuit, Normalize.elaborated,
      Normalize.main, GroupedEqXV.circuit, GroupedEqXV.elaborated,
      RangeCheck.circuit, Circuit.assertZero]
    omega
  subcircuitsConsistent := by
    intro input offset
    simp +arith only [main, interpolatedMul, circuit_norm, Normalize.circuit, Normalize.elaborated,
      Normalize.main, GroupedEqXV.circuit, GroupedEqXV.elaborated,
      RangeCheck.circuit, Circuit.assertZero]
  channelsLawful := by
    intro offset
    simp only [main, interpolatedMul, circuit_norm, Normalize.circuit, Normalize.elaborated,
      Normalize.main, GroupedEqXV.circuit, GroupedEqXV.elaborated,
      RangeCheck.circuit, Circuit.assertZero]


def Assumptions (B : ℕ) (c : Vector (F p) (2 * m))
    (input : Inputs m (F p)) : Prop :=
  input.a.Normalized B ∧
    input.b.Normalized (B + 1) ∧
    input.modulus.Normalized B ∧
    input.a.value B < input.modulus.value B ∧
    input.b.value B < 2 * input.modulus.value B ∧
    0 < input.modulus.value B ∧
    5 * input.modulus.value B ≤ 2 ^ (B * m + 3) ∧
    (∀ j : Fin (2 * m), (c[j.val]).val < 4 * 2 ^ B) ∧
    polyValue B c = 3 * (input.modulus.value B * input.modulus.value B) ∧
    (∀ k : Fin (2 * m - 1), (input.target[k.val]).val < 3 * m * 2 ^ (2 * B)) ∧
    polyValue B input.target ≤ 3 * (input.modulus.value B * input.modulus.value B)


def Spec (B : ℕ) (input : Inputs m (F p)) : Prop :=
  polyValue B input.target % input.modulus.value B
    = (input.a.value B * input.b.value B) % input.modulus.value B



end MulModTargetT
end Solution.Secp256k1ScalarMul
