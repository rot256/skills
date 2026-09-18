import Mathlib.Data.Nat.Size
import Clean.Circuit.Basic
import Clean.Circuit.Loops
import Clean.Gadgets.Bits
import Clean.Gadgets.Equality
import Clean.Utils.Tactics.ProvableStructDeriving
import Challenge.Utils.ComputableWitnessLemmas

namespace Solution.Secp256k1ScalarMul.Limbs

def fromLimbs (limbBits : ℕ) (limbs : List ℕ) : ℕ :=
  limbs.foldr (fun limb acc => limb + acc * 2 ^ limbBits) 0

end Solution.Secp256k1ScalarMul.Limbs

namespace Solution.Secp256k1ScalarMul

section ComputableWitnessHelpers
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2)]

omit [Fact (p > 2)] in
theorem assertBoolComputableWitnesses :
    (assertBool (p := p)).ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition input env env')
    (((assertBool (p := p)).main input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold assertBool
  simp only [Challenge.Utils.ComputableWitnessLemmas.Circuit.assertZero_structuralComputableWitnesses_iff]

end ComputableWitnessHelpers

open Solution.Secp256k1ScalarMul.Limbs

@[reducible] def BigInt (m : ℕ) : TypeMap := fields m

namespace BigInt

section
variable {p : ℕ} [Fact p.Prime] {m : ℕ}

def value (B : ℕ) (x : BigInt m (F p)) : ℕ :=
  Solution.Secp256k1ScalarMul.Limbs.fromLimbs B (x.toList.map ZMod.val)

def Normalized (B : ℕ) (x : BigInt m (F p)) : Prop := ∀ i : Fin m, (x[i]).val < 2 ^ B

end

end BigInt

section
variable {p : ℕ} [Fact p.Prime]
variable {m : ℕ}

theorem fromLimbs_injective {B : ℕ} :
    ∀ {l₁ l₂ : List ℕ}, l₁.length = l₂.length →
      (∀ x ∈ l₁, x < 2 ^ B) → (∀ x ∈ l₂, x < 2 ^ B) →
      Solution.Secp256k1ScalarMul.Limbs.fromLimbs B l₁ = Solution.Secp256k1ScalarMul.Limbs.fromLimbs B l₂ → l₁ = l₂ := by
  intro l₁
  induction l₁ with
  | nil =>
    intro l₂ hlen _ _ _
    exact (List.length_eq_zero_iff.mp hlen.symm).symm
  | cons a t ih =>
    intro l₂ hlen h₁ h₂ hval
    match l₂ with
    | b :: s =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      have ha : a < 2 ^ B := h₁ a (List.mem_cons_self ..)
      have hb : b < 2 ^ B := h₂ b (List.mem_cons_self ..)
      simp only [Solution.Secp256k1ScalarMul.Limbs.fromLimbs, List.foldr_cons] at hval ⊢
      -- `hval : a + (foldr .. t) * 2^B = b + (foldr .. s) * 2^B`
      -- take mod 2^B to get `a = b`, then div to recurse.
      have hpow : 0 < 2 ^ B := Nat.two_pow_pos B
      have hmod : a = b := by
        have := congrArg (· % 2 ^ B) hval
        simp only [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ha,
          Nat.mod_eq_of_lt hb] at this
        exact this
      subst hmod
      have hrest : (t.foldr (fun limb acc => limb + acc * 2 ^ B) 0)
          = (s.foldr (fun limb acc => limb + acc * 2 ^ B) 0) := by
        have := congrArg (· / 2 ^ B) hval
        simp only [Nat.add_mul_div_right _ _ hpow,
          Nat.div_eq_of_lt ha, Nat.zero_add] at this
        exact this
      have := ih hlen (fun x hx => h₁ x (List.mem_cons_of_mem _ hx))
        (fun x hx => h₂ x (List.mem_cons_of_mem _ hx)) hrest
      rw [this]

theorem BigInt.value_inj {B : ℕ} {a b : BigInt m (F p)}
    (ha : a.Normalized B) (hb : b.Normalized B)
    (h : a.value B = b.value B) : a = b := by
  -- the limb-value lists are equal by base-`2^B` uniqueness …
  have hlists : a.toList.map ZMod.val = b.toList.map ZMod.val := by
    apply fromLimbs_injective (B := B)
    · simp only [List.length_map, Vector.length_toList]
    · intro x hx
      simp only [List.mem_map, Vector.mem_toList_iff] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      obtain ⟨i, hi, rfl⟩ := Vector.getElem_of_mem hy
      exact ha ⟨i, hi⟩
    · intro x hx
      simp only [List.mem_map, Vector.mem_toList_iff] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      obtain ⟨i, hi, rfl⟩ := Vector.getElem_of_mem hy
      exact hb ⟨i, hi⟩
    · exact h
  -- … then `ZMod.val` is injective, so the limb vectors are equal.
  have : a.toList = b.toList :=
    List.map_injective_iff.mpr (ZMod.val_injective p) hlists
  exact Vector.toList_inj.mp this

theorem fromLimbs_eq_sum {B : ℕ} (l : List ℕ) :
    Solution.Secp256k1ScalarMul.Limbs.fromLimbs B l = ∑ i : Fin l.length, l[i] * 2 ^ (B * i.val) := by
  induction l with
  | nil => simp [Solution.Secp256k1ScalarMul.Limbs.fromLimbs]
  | cons a t ih =>
    have hrhs : (∑ i : Fin (a :: t).length, (a :: t)[i] * 2 ^ (B * i.val))
        = a + (∑ i : Fin t.length, t[i] * 2 ^ (B * i.val)) * 2 ^ B := by
      show (∑ i : Fin (t.length + 1), (a :: t)[i] * 2 ^ (B * i.val)) = _
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, Nat.mul_zero, pow_zero, Nat.mul_one,
        Fin.val_succ]
      rw [Finset.sum_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      have hidx : (a :: t)[i.succ] = t[i] := by
        simp [List.getElem_cons_succ]
      rw [hidx, Nat.mul_add, Nat.mul_one, pow_add]
      ring
    rw [show Solution.Secp256k1ScalarMul.Limbs.fromLimbs B (a :: t)
        = a + Solution.Secp256k1ScalarMul.Limbs.fromLimbs B t * 2 ^ B from rfl, ih]
    exact hrhs.symm

omit [Fact (Nat.Prime p)] in

theorem BigInt.value_eq_sum {B : ℕ} (x : BigInt m (F p)) :
    BigInt.value B x = ∑ k : Fin m, (x[k]).val * 2 ^ (B * k.val) := by
  rw [BigInt.value, fromLimbs_eq_sum]
  have hlen : (x.toList.map ZMod.val).length = m := by
    simp [List.length_map, Vector.length_toList]
  -- transport the sum over `Fin (length)` to `Fin m`
  rw [← Fin.sum_congr' (fun k : Fin m => (x[k]).val * 2 ^ (B * k.val)) hlen]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Fin.val_cast]
  congr 1
  rw [Fin.getElem_fin, List.getElem_map]
  rfl

theorem sum_lt_pow {B n : ℕ} (f : Fin n → ℕ) (hf : ∀ i, f i < 2 ^ B) :
    ∑ i : Fin n, f i * 2 ^ (B * i.val) < 2 ^ (B * n) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Fin.sum_univ_castSucc]
    have ihk : ∑ i : Fin k, f (Fin.castSucc i) * 2 ^ (B * i.val) < 2 ^ (B * k) :=
      ih (fun i => f (Fin.castSucc i)) (fun i => hf _)
    have hlast : f (Fin.last k) < 2 ^ B := hf _
    have hterm : f (Fin.last k) * 2 ^ (B * k) ≤ (2 ^ B - 1) * 2 ^ (B * k) := by
      apply Nat.mul_le_mul_right
      omega
    have hpow : (2 ^ B - 1) * 2 ^ (B * k) + 2 ^ (B * k) = 2 ^ (B * (k + 1)) := by
      have h1 : 0 < 2 ^ B := Nat.two_pow_pos B
      rw [Nat.mul_add, Nat.mul_one, pow_add, Nat.sub_mul, Nat.one_mul,
        Nat.mul_comm (2 ^ B) (2 ^ (B * k))]
      have hle : 2 ^ (B * k) ≤ 2 ^ (B * k) * 2 ^ B := Nat.le_mul_of_pos_right _ h1
      omega
    have hcs : ∀ i : Fin k, ((Fin.castSucc i : Fin (k+1)) : ℕ) = (i : ℕ) := fun i => rfl
    simp only [Fin.val_last, hcs] at *
    omega

omit [Fact (Nat.Prime p)] in

theorem BigInt.value_lt {B : ℕ} {x : BigInt m (F p)} (h : x.Normalized B) :
    BigInt.value B x < 2 ^ (B * m) := by
  rw [BigInt.value_eq_sum]
  exact sum_lt_pow (fun k => (x[k]).val) h

theorem limb_decomp_mod (B : ℕ) : ∀ (m N : ℕ),
    (∑ i ∈ Finset.range m, (N / 2 ^ (B * i) % 2 ^ B) * 2 ^ (B * i)) = N % 2 ^ (B * m) := by
  intro m
  induction m with
  | zero => intro N; simp [Nat.mod_one]
  | succ n ih =>
    intro N
    rw [Finset.sum_range_succ']
    simp only [Nat.mul_zero, pow_zero, Nat.mul_one, Nat.div_one]
    have htail : (∑ i ∈ Finset.range n, (N / 2 ^ (B * (i + 1)) % 2 ^ B) * 2 ^ (B * (i + 1)))
        = 2 ^ B * ((N / 2 ^ B) % 2 ^ (B * n)) := by
      rw [← ih (N / 2 ^ B), Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      have h1 : N / 2 ^ (B * (i + 1)) = (N / 2 ^ B) / 2 ^ (B * i) := by
        rw [Nat.div_div_eq_div_mul, ← pow_add]; congr 1; ring
      have h2 : (2 : ℕ) ^ (B * (i + 1)) = 2 ^ B * 2 ^ (B * i) := by rw [← pow_add]; congr 1; ring
      rw [h1, h2]; ring
    rw [htail]
    have hsplit : N % 2 ^ (B * (n + 1)) = N % 2 ^ B + 2 ^ B * ((N / 2 ^ B) % 2 ^ (B * n)) := by
      conv_lhs => rw [show B * (n + 1) = B + B * n by ring, pow_add, Nat.mod_mul]
    rw [hsplit]; ring

theorem BigInt.value_mapRange {B : ℕ} (off N : ℕ) (env : Environment (F p))
    (hB : 2 ^ B < p) (hN : N < 2 ^ (B * m))
    (hwit : ∀ i : Fin m, env.get (off + i.val) = ((N / 2 ^ (B * i.val) % 2 ^ B : ℕ) : F p)) :
    BigInt.value B (Vector.map (Expression.eval env)
      (Vector.mapRange m fun i => var (F := F p) { index := off + i })) = N := by
  rw [BigInt.value_eq_sum]
  have hstep : (∑ k : Fin m, ((Vector.map (Expression.eval env)
        (Vector.mapRange m fun i => var (F := F p) { index := off + i }))[k]).val * 2 ^ (B * k.val))
      = ∑ k ∈ Finset.range m, (N / 2 ^ (B * k) % 2 ^ B) * 2 ^ (B * k) := by
    rw [← Fin.sum_univ_eq_sum_range (fun k => (N / 2 ^ (B * k) % 2 ^ B) * 2 ^ (B * k))]
    apply Finset.sum_congr rfl
    intro i _
    have hget : (Vector.map (Expression.eval env)
        (Vector.mapRange m fun j => var (F := F p) { index := off + j }))[i.val] = env.get (off + i.val) := by
      simp [circuit_norm]
    rw [Fin.getElem_fin, hget, hwit i]
    congr 1
    rw [ZMod.val_natCast_of_lt]
    exact lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos B)) (le_of_lt hB)
  rw [hstep, limb_decomp_mod, Nat.mod_eq_of_lt hN]

end

section
variable {p : ℕ} [Fact p.Prime]
variable {m : ℕ} [NeZero m]

def bigIntMulNoReduce (a b : Var (BigInt m) (F p)) :
    Vector (Expression (F p)) (2 * m - 1) :=
  Vector.mapFinRange (2 * m - 1) fun k =>
    -- P_k = Σ_{i : Fin m, i ≤ k, k - i < m} a[i] * b[k - i]
    (Vector.finRange m).foldl
      (fun acc i =>
        if h : i.val ≤ k.val ∧ k.val - i.val < m then
          acc + a[i.val] * b[k.val - i.val]'(h.2)
        else acc)
      (0 : Expression (F p))

def polyValue (B : ℕ) {k : ℕ} (coeffs : Vector (F p) k) : ℕ :=
  ∑ i : Fin k, (coeffs[i.val]).val * 2 ^ (B * i.val)

lemma vector_foldl_finRange {α : Type*} (n : ℕ) (f : α → Fin n → α) (init : α) :
    Vector.foldl f init (Vector.finRange n) = Fin.foldl n f init := by
  induction n generalizing init with
  | zero => simp [Fin.foldl_zero]
  | succ k ih =>
    rw [Fin.foldl_succ_last, Vector.finRange_succ_last, Vector.foldl_append]
    simp only [Vector.foldl_map]
    rw [ih]
    simp [Vector.foldl]

lemma foldl_dif_add_eq_sum {M : Type*} [AddCommMonoid M] (n : ℕ)
    (P : Fin n → Prop) [DecidablePred P] (g : (i : Fin n) → P i → M) :
    Fin.foldl n (fun acc i => if h : P i then acc + g i h else acc) 0
      = ∑ i : Fin n, if h : P i then g i h else 0 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Fin.foldl_succ_last, Fin.sum_univ_castSucc]
    rw [ih (fun i => P i.castSucc) (fun i h => g i.castSucc h)]
    split <;> simp

def bigIntMulVars (pp : Vector (Expression (F p)) (m * m)) :
    Vector (Expression (F p)) (2 * m - 1) :=
  Vector.mapFinRange (2 * m - 1) fun k =>
    (Vector.finRange m).foldl
      (fun acc i =>
        if h : i.val ≤ k.val ∧ k.val - i.val < m then
          acc + pp[i.val * m + (k.val - i.val)]'(by
            have : i.val * m + (k.val - i.val) < m * m := by
              have hi := i.isLt; have := h.2; calc
                i.val * m + (k.val - i.val) < i.val * m + m := by omega
                _ = (i.val + 1) * m := by ring
                _ ≤ m * m := by apply Nat.mul_le_mul_right; omega
            simpa [Nat.mul_comm] using this)
        else acc)
      (0 : Expression (F p))

omit [NeZero m] in

lemma eval_bigIntMulNoReduce_coeff (env : Environment (F p))
    (a b : Var (BigInt m) (F p)) (k : Fin (2 * m - 1)) :
    Expression.eval env ((bigIntMulNoReduce a b)[k.val])
      = ∑ i : Fin m, if h : i.val ≤ k.val ∧ k.val - i.val < m then
          (Expression.eval env a[i.val]) * (Expression.eval env (b[k.val - i.val]'h.2)) else 0 := by
  simp only [bigIntMulNoReduce, Vector.getElem_mapFinRange]
  rw [vector_foldl_finRange]
  rw [eval_foldl env m
    (fun acc i => if h : i.val ≤ k.val ∧ k.val - i.val < m then
        acc + a[i.val] * b[k.val - i.val]'h.2 else acc) 0
    (by intro e i; by_cases h : i.val ≤ k.val ∧ k.val - i.val < m <;> simp [h, circuit_norm])]
  simp only [apply_dite (Expression.eval env), Expression.eval]
  rw [foldl_dif_add_eq_sum m (fun i : Fin m => i.val ≤ k.val ∧ k.val - i.val < m)
    (fun i h => (Expression.eval env a[i.val]) * (Expression.eval env (b[k.val - i.val]'h.2)))]

omit [NeZero m] in

lemma eval_bigIntMulVars_coeff (env : Environment (F p))
    (pp : Vector (Expression (F p)) (m * m)) (k : Fin (2 * m - 1)) :
    Expression.eval env ((bigIntMulVars pp)[k.val])
      = ∑ i : Fin m, if h : i.val ≤ k.val ∧ k.val - i.val < m then
          (Expression.eval env (pp[i.val * m + (k.val - i.val)]'(by
            have := i.isLt; have := h.2; calc
              i.val * m + (k.val - i.val) < i.val * m + m := by omega
              _ = (i.val + 1) * m := by ring
              _ ≤ m * m := by apply Nat.mul_le_mul_right; omega))) else 0 := by
  simp only [bigIntMulVars, Vector.getElem_mapFinRange]
  rw [vector_foldl_finRange]
  rw [eval_foldl env m
    (fun acc i => if h : i.val ≤ k.val ∧ k.val - i.val < m then
        acc + pp[i.val * m + (k.val - i.val)]'(by
          have hi := i.isLt; have := h.2; calc
            i.val * m + (k.val - i.val) < i.val * m + m := by omega
            _ = (i.val + 1) * m := by ring
            _ ≤ m * m := by apply Nat.mul_le_mul_right; omega) else acc) 0
    (by intro e i; by_cases h : i.val ≤ k.val ∧ k.val - i.val < m <;> simp [h, circuit_norm])]
  simp only [apply_dite (Expression.eval env), Expression.eval]
  rw [foldl_dif_add_eq_sum m (fun i : Fin m => i.val ≤ k.val ∧ k.val - i.val < m)
    (fun i h => Expression.eval env (pp[i.val * m + (k.val - i.val)]'(by
      have hi := i.isLt; have := h.2; calc
        i.val * m + (k.val - i.val) < i.val * m + m := by omega
        _ = (i.val + 1) * m := by ring
        _ ≤ m * m := by apply Nat.mul_le_mul_right; omega)))]

omit [NeZero m] in

lemma map_eval_bigIntMulVars_eq (env : Environment (F p))
    (a b : Var (BigInt m) (F p)) (pp : Vector (Expression (F p)) (m * m))
    (hpp : ∀ (i j : Fin m),
      Expression.eval env (pp[i.val * m + j.val]'(by
        have := i.isLt; have := j.isLt
        calc i.val * m + j.val < i.val * m + m := by omega
          _ = (i.val + 1) * m := by ring
          _ ≤ m * m := by apply Nat.mul_le_mul_right; omega))
        = Expression.eval env a[i.val] * Expression.eval env b[j.val]) :
    Vector.map (Expression.eval env) (bigIntMulVars pp)
      = Vector.map (Expression.eval env) (bigIntMulNoReduce a b) := by
  apply Vector.ext
  intro k hk
  rw [Vector.getElem_map, Vector.getElem_map,
    eval_bigIntMulVars_coeff env pp ⟨k, hk⟩, eval_bigIntMulNoReduce_coeff env a b ⟨k, hk⟩]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : i.val ≤ k ∧ k - i.val < m
  · simp only [dif_pos h]
    have hj : k - i.val < m := h.2
    have := hpp i ⟨k - i.val, hj⟩
    simpa using this
  · simp only [dif_neg h]

lemma val_bigIntMulNoReduce_coeff {B : ℕ} (env : Environment (F p))
    (a b : Var (BigInt m) (F p)) (k : Fin (2 * m - 1))
    (ha : ∀ i : Fin m, (Expression.eval env a[i.val]).val < 2 ^ B)
    (hb : ∀ i : Fin m, (Expression.eval env b[i.val]).val < 2 ^ B)
    (hbound : m * (2 ^ B * 2 ^ B) < p) :
    (Expression.eval env ((bigIntMulNoReduce a b)[k.val])).val
      = ∑ i : Fin m, if h : i.val ≤ k.val ∧ k.val - i.val < m then
          (Expression.eval env a[i.val]).val
            * (Expression.eval env (b[k.val - i.val]'h.2)).val else 0 := by
  set natConv := ∑ i : Fin m, if h : i.val ≤ k.val ∧ k.val - i.val < m then
      (Expression.eval env a[i.val]).val
        * (Expression.eval env (b[k.val - i.val]'h.2)).val else 0 with hnat
  -- the natural-number convolution is `< p`
  have hlt : natConv < p := by
    have hterm : ∀ i : Fin m, (if h : i.val ≤ k.val ∧ k.val - i.val < m then
        (Expression.eval env a[i.val]).val
          * (Expression.eval env (b[k.val - i.val]'h.2)).val else 0)
        ≤ 2 ^ B * 2 ^ B - 1 := by
      intro i
      by_cases h : i.val ≤ k.val ∧ k.val - i.val < m
      · rw [dif_pos h]
        have h1 := ha i
        have h2 := hb ⟨k.val - i.val, h.2⟩
        have : (Expression.eval env a[i.val]).val
            * (Expression.eval env (b[k.val - i.val]'h.2)).val < 2 ^ B * 2 ^ B :=
          Nat.mul_lt_mul'' h1 h2
        omega
      · rw [dif_neg h]; positivity
    have hcard : natConv ≤ m * (2 ^ B * 2 ^ B - 1) := by
      rw [hnat]
      calc ∑ i : Fin m, _ ≤ ∑ _i : Fin m, (2 ^ B * 2 ^ B - 1) :=
            Finset.sum_le_sum (fun i _ => hterm i)
        _ = m * (2 ^ B * 2 ^ B - 1) := by rw [Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, smul_eq_mul]
    have hpos : 0 < 2 ^ B * 2 ^ B := by positivity
    have hm : 0 < m := Nat.pos_of_neZero m
    have : m * (2 ^ B * 2 ^ B - 1) < m * (2 ^ B * 2 ^ B) :=
      (Nat.mul_lt_mul_left hm).mpr (by omega)
    omega
  -- the field coefficient is the cast of `natConv`
  have hcast : Expression.eval env ((bigIntMulNoReduce a b)[k.val]) = (natConv : F p) := by
    rw [eval_bigIntMulNoReduce_coeff, hnat, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : i.val ≤ k.val ∧ k.val - i.val < m
    · simp only [dif_pos h]
      rw [Nat.cast_mul, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    · simp only [dif_neg h, Nat.cast_zero]
  rw [hcast, ZMod.val_natCast_of_lt hlt]

lemma val_bigIntMulNoReduce_coeff_lt {B : ℕ} (env : Environment (F p))
    (a b : Var (BigInt m) (F p)) (k : Fin (2 * m - 1))
    (ha : ∀ i : Fin m, (Expression.eval env a[i.val]).val < 2 ^ B)
    (hb : ∀ i : Fin m, (Expression.eval env b[i.val]).val < 2 ^ B)
    (hbound : m * (2 ^ B * 2 ^ B) < p) :
    (Expression.eval env ((bigIntMulNoReduce a b)[k.val])).val < m * 2 ^ (2 * B) := by
  rw [val_bigIntMulNoReduce_coeff env a b k ha hb hbound]
  have hterm : ∀ i : Fin m, (if h : i.val ≤ k.val ∧ k.val - i.val < m then
      (Expression.eval env a[i.val]).val
        * (Expression.eval env (b[k.val - i.val]'h.2)).val else 0)
      ≤ 2 ^ B * 2 ^ B - 1 := by
    intro i
    by_cases h : i.val ≤ k.val ∧ k.val - i.val < m
    · rw [dif_pos h]
      have h1 := ha i
      have h2 := hb ⟨k.val - i.val, h.2⟩
      have : (Expression.eval env a[i.val]).val
          * (Expression.eval env (b[k.val - i.val]'h.2)).val < 2 ^ B * 2 ^ B :=
        Nat.mul_lt_mul'' h1 h2
      omega
    · rw [dif_neg h]; positivity
  have hcard : (∑ i : Fin m, if h : i.val ≤ k.val ∧ k.val - i.val < m then
      (Expression.eval env a[i.val]).val
        * (Expression.eval env (b[k.val - i.val]'h.2)).val else 0)
      ≤ m * (2 ^ B * 2 ^ B - 1) := by
    calc ∑ i : Fin m, _ ≤ ∑ _i : Fin m, (2 ^ B * 2 ^ B - 1) :=
          Finset.sum_le_sum (fun i _ => hterm i)
      _ = m * (2 ^ B * 2 ^ B - 1) := by rw [Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, smul_eq_mul]
  have hpos : 0 < 2 ^ B * 2 ^ B := by positivity
  have hm : 0 < m := Nat.pos_of_neZero m
  have h2B : (2 : ℕ) ^ B * 2 ^ B = 2 ^ (2 * B) := by rw [two_mul, pow_add]
  have hlt2 : m * (2 ^ B * 2 ^ B - 1) < m * (2 ^ B * 2 ^ B) :=
    (Nat.mul_lt_mul_left hm).mpr (by omega)
  rw [h2B] at hcard hlt2
  omega

lemma cauchy_inner_reindex (B m : ℕ) (f g : ℕ → ℕ) (i : ℕ) (hi : i < m) :
    (∑ k ∈ Finset.range (2 * m - 1),
        if i ≤ k ∧ k - i < m then f i * g (k - i) * 2 ^ (B * k) else 0)
      = ∑ j ∈ Finset.range m, f i * g j * 2 ^ (B * (i + j)) := by
  rw [← Finset.sum_filter]
  apply Finset.sum_nbij' (i := fun k => k - i) (j := fun j => i + j)
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
    omega
  · intro j hj
    simp only [Finset.mem_range, Finset.mem_filter] at hj ⊢
    omega
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    omega
  · intro j hj
    simp only [Finset.mem_range] at hj
    omega
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    rw [show i + (k - i) = k by omega]

lemma cauchy_base_pow (B m : ℕ) (f g : ℕ → ℕ) :
    (∑ i ∈ Finset.range m, f i * 2 ^ (B * i))
        * (∑ j ∈ Finset.range m, g j * 2 ^ (B * j))
      = ∑ k ∈ Finset.range (2 * m - 1),
          (∑ i ∈ Finset.range m, if i ≤ k ∧ k - i < m then f i * g (k - i) else 0)
            * 2 ^ (B * k) := by
  rw [Finset.sum_mul_sum]
  -- transform RHS into the same double sum `∑ i ∑ j, f i * g j * 2^(B*(i+j))`
  have hrhs : (∑ k ∈ Finset.range (2 * m - 1),
        (∑ i ∈ Finset.range m, if i ≤ k ∧ k - i < m then f i * g (k - i) else 0)
          * 2 ^ (B * k))
      = ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m, f i * g j * 2 ^ (B * (i + j)) := by
    have hstep : (∑ k ∈ Finset.range (2 * m - 1),
          (∑ i ∈ Finset.range m, if i ≤ k ∧ k - i < m then f i * g (k - i) else 0)
            * 2 ^ (B * k))
        = ∑ k ∈ Finset.range (2 * m - 1), ∑ i ∈ Finset.range m,
            if i ≤ k ∧ k - i < m then f i * g (k - i) * 2 ^ (B * k) else 0 := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [ite_mul, zero_mul]
    rw [hstep, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    rw [cauchy_inner_reindex B m f g i hi]
  rw [hrhs]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [show B * (i + j) = B * i + B * j by ring, pow_add]
  ring

lemma polyValue_bigIntMulNoReduce {B : ℕ} (env : Environment (F p))
    (a b : Var (BigInt m) (F p))
    (ha : ∀ i : Fin m, (Expression.eval env a[i.val]).val < 2 ^ B)
    (hb : ∀ i : Fin m, (Expression.eval env b[i.val]).val < 2 ^ B)
    (hbound : m * (2 ^ B * 2 ^ B) < p) :
    polyValue B (Vector.map (Expression.eval env) (bigIntMulNoReduce a b))
      = (∑ i : Fin m, (Expression.eval env a[i.val]).val * 2 ^ (B * i.val))
        * (∑ j : Fin m, (Expression.eval env b[j.val]).val * 2 ^ (B * j.val)) := by
  -- natural-number digit functions extended by 0 outside `range m`
  set av : ℕ → ℕ := fun i => if h : i < m then (Expression.eval env a[i]).val else 0 with hav
  set bv : ℕ → ℕ := fun j => if h : j < m then (Expression.eval env b[j]).val else 0 with hbv
  -- the two operand sums in `range m` / `av`,`bv` form
  have hAsum : (∑ i : Fin m, (Expression.eval env a[i.val]).val * 2 ^ (B * i.val))
      = ∑ i ∈ Finset.range m, av i * 2 ^ (B * i) := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => av i * 2 ^ (B * i))]
    apply Finset.sum_congr rfl
    intro i _; simp only [hav, dif_pos i.isLt]
  have hBsum : (∑ j : Fin m, (Expression.eval env b[j.val]).val * 2 ^ (B * j.val))
      = ∑ j ∈ Finset.range m, bv j * 2 ^ (B * j) := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => bv j * 2 ^ (B * j))]
    apply Finset.sum_congr rfl
    intro j _; simp only [hbv, dif_pos j.isLt]
  rw [hAsum, hBsum, cauchy_base_pow B m av bv]
  -- LHS: unfold `polyValue` over the mapped coefficient vector
  rw [polyValue]
  rw [← Fin.sum_univ_eq_sum_range
    (fun k => (∑ i ∈ Finset.range m, if i ≤ k ∧ k - i < m then av i * bv (k - i) else 0)
      * 2 ^ (B * k))]
  apply Finset.sum_congr rfl
  intro k _
  rw [Vector.getElem_map, val_bigIntMulNoReduce_coeff env a b k ha hb hbound]
  congr 1
  -- match the two convolution coefficients (`Fin m` dif vs. `range m` ite)
  rw [← Fin.sum_univ_eq_sum_range
    (fun i => if i ≤ k.val ∧ k.val - i < m then av i * bv (k.val - i) else 0)]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : i.val ≤ k.val ∧ k.val - i.val < m
  · rw [dif_pos h, if_pos h]
    simp only [hav, hbv, dif_pos i.isLt, dif_pos h.2]
  · rw [dif_neg h, if_neg h]

def evalPartial (B : ℕ) {n : ℕ} (env : ProverEnvironment (F p))
    (x : Var (fields n) (F p)) (k : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (k + 1),
    (if h : j < n then (Expression.eval env.toEnvironment x[j]).val else 0) * 2 ^ (B * j)

lemma partial_div_bound (B m : ℕ) (hB1 : 1 ≤ B) (f : ℕ → ℕ)
    (hf : ∀ j, f j < (m + 1) * 2 ^ (2 * B)) (k : ℕ) :
    (∑ j ∈ Finset.range (k + 1), f j * 2 ^ (B * j)) / 2 ^ (B * (k + 1))
      ≤ (m + 1) * 2 ^ (B + 1) := by
  -- partial sum < (m+1)*2^(2B) * 2^(B*k) * 2  (geometric, using B ≥ 1)
  have hgeo : (∑ j ∈ Finset.range (k + 1), 2 ^ (B * j)) ≤ 2 ^ (B * k + 1) := by
    induction k with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have h1 : (2 : ℕ) ^ (B * n + 1) + 2 ^ (B * (n + 1)) ≤ 2 ^ (B * (n + 1) + 1) := by
        have he : B * n + 1 ≤ B * (n + 1) := by nlinarith
        have h2 : (2 : ℕ) ^ (B * n + 1) ≤ 2 ^ (B * (n + 1)) := Nat.pow_le_pow_right (by norm_num) he
        have : (2 : ℕ) ^ (B * (n + 1)) + 2 ^ (B * (n + 1)) = 2 ^ (B * (n + 1) + 1) := by
          rw [pow_succ]; ring
        omega
      omega
  have hsum_lt : (∑ j ∈ Finset.range (k + 1), f j * 2 ^ (B * j))
      ≤ (m + 1) * 2 ^ (B + 1) * 2 ^ (B * (k + 1)) := by
    calc (∑ j ∈ Finset.range (k + 1), f j * 2 ^ (B * j))
        ≤ ∑ j ∈ Finset.range (k + 1), (m + 1) * 2 ^ (2 * B) * 2 ^ (B * j) := by
          apply Finset.sum_le_sum
          intro j _
          apply Nat.mul_le_mul_right
          have := hf j; omega
      _ = (m + 1) * 2 ^ (2 * B) * ∑ j ∈ Finset.range (k + 1), 2 ^ (B * j) := by
          rw [Finset.mul_sum]
      _ ≤ (m + 1) * 2 ^ (2 * B) * 2 ^ (B * k + 1) := Nat.mul_le_mul_left _ hgeo
      _ = (m + 1) * 2 ^ (B + 1) * 2 ^ (B * (k + 1)) := by
          rw [Nat.mul_assoc, Nat.mul_assoc, ← pow_add, ← pow_add]; congr 2; ring
  -- divide
  exact Nat.div_le_of_le_mul (by rw [Nat.mul_comm]; exact hsum_lt)

lemma geom_sum_mul_base (B : ℕ) : ∀ n : ℕ,
    (2 ^ B - 1) * (∑ j ∈ Finset.range n, 2 ^ (B * j)) = 2 ^ (B * n) - 1
  | 0 => by simp
  | n + 1 => by
    rw [Finset.sum_range_succ, Nat.mul_add, geom_sum_mul_base B n, Nat.sub_mul]
    have h1 : (2 : ℕ) ^ B * 2 ^ (B * n) = 2 ^ (B * (n + 1)) := by
      rw [← pow_add]; congr 1; ring
    have h2 : 1 ≤ (2 : ℕ) ^ (B * n) := Nat.one_le_two_pow
    have h3 : (2 : ℕ) ^ (B * n) ≤ 2 ^ B * 2 ^ (B * n) :=
      Nat.le_mul_of_pos_left _ (Nat.two_pow_pos B)
    omega

lemma partial_div_boundC (B : ℕ) (f : ℕ → ℕ) (C OFF : ℕ)
    (hf : ∀ j, f j < C) (hCO : C ≤ OFF * (2 ^ B - 1)) (k : ℕ) :
    (∑ j ∈ Finset.range (k + 1), f j * 2 ^ (B * j)) / 2 ^ (B * (k + 1)) ≤ OFF := by
  have hsum : (∑ j ∈ Finset.range (k + 1), f j * 2 ^ (B * j))
      ≤ OFF * (2 ^ (B * (k + 1)) - 1) := by
    calc (∑ j ∈ Finset.range (k + 1), f j * 2 ^ (B * j))
        ≤ ∑ j ∈ Finset.range (k + 1), (C - 1) * 2 ^ (B * j) := by
          apply Finset.sum_le_sum
          intro j _
          exact Nat.mul_le_mul_right _ (by have := hf j; omega)
      _ = (C - 1) * ∑ j ∈ Finset.range (k + 1), 2 ^ (B * j) := by
          rw [Finset.mul_sum]
      _ ≤ OFF * (2 ^ B - 1) * ∑ j ∈ Finset.range (k + 1), 2 ^ (B * j) := by
          apply Nat.mul_le_mul_right
          omega
      _ = OFF * ((2 ^ B - 1) * ∑ j ∈ Finset.range (k + 1), 2 ^ (B * j)) := by
          rw [Nat.mul_assoc]
      _ = OFF * (2 ^ (B * (k + 1)) - 1) := by
          rw [geom_sum_mul_base B (k + 1)]
  have hle : OFF * (2 ^ (B * (k + 1)) - 1) ≤ 2 ^ (B * (k + 1)) * OFF := by
    have h2 : (2 : ℕ) ^ (B * (k + 1)) - 1 ≤ 2 ^ (B * (k + 1)) := Nat.sub_le _ _
    calc OFF * (2 ^ (B * (k + 1)) - 1) ≤ OFF * 2 ^ (B * (k + 1)) :=
          Nat.mul_le_mul_left _ h2
      _ = 2 ^ (B * (k + 1)) * OFF := Nat.mul_comm _ _
  exact Nat.div_le_of_le_mul (le_trans hsum hle)

lemma partial_mod_stable (B : ℕ) (h : ℕ → ℕ) :
    ∀ N k, k < N →
      (∑ j ∈ Finset.range N, h j * 2 ^ (B * j)) % 2 ^ (B * (k + 1))
        = (∑ j ∈ Finset.range (k + 1), h j * 2 ^ (B * j)) % 2 ^ (B * (k + 1)) := by
  intro N
  induction N with
  | zero => intro k hk; omega
  | succ n ih =>
    intro k hk
    rw [Finset.sum_range_succ]
    rcases Nat.lt_or_ge k n with hlt | hge
    · -- n ≥ k+1, so the added limb h n * 2^(B*n) is a multiple of 2^(B*(k+1))
      have hfac : (2 : ℕ) ^ (B * n) = 2 ^ (B * (k + 1)) * 2 ^ (B * (n - k - 1)) := by
        rw [← pow_add]; congr 1
        have : B * (k + 1) + B * (n - k - 1) = B * (k + 1 + (n - k - 1)) := by ring
        rw [this]; congr 1; omega
      rw [hfac, show h n * (2 ^ (B * (k + 1)) * 2 ^ (B * (n - k - 1)))
          = (h n * 2 ^ (B * (n - k - 1))) * 2 ^ (B * (k + 1)) by ring,
        Nat.add_mul_mod_self_right]
      exact ih k hlt
    · -- k = n, range (n+1) = range (k+1)
      have : k = n := by omega
      subst this; rw [Finset.sum_range_succ]

lemma quot_step (B : ℕ) (f : ℕ → ℕ) (k : ℕ) :
    (∑ j ∈ Finset.range (k + 1), f j * 2 ^ (B * j)) / 2 ^ (B * k)
      = f k + (if k = 0 then 0
          else (∑ j ∈ Finset.range k, f j * 2 ^ (B * j)) / 2 ^ (B * k)) := by
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · subst hk0; simp
  · rw [if_neg (by omega : ¬ k = 0)]
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    rw [Finset.sum_range_succ, show n.succ = n + 1 from rfl,
      Nat.add_mul_div_right _ _ (Nat.two_pow_pos (B * (n + 1)))]
    ring

lemma carry_telescope (B : ℕ) (C : ℕ → ℕ) :
    ∀ n : ℕ,
      (∑ k ∈ Finset.range n, (if k = 0 then 0 else C (k - 1)) * 2 ^ (B * k))
        + (if n = 0 then 0 else C (n - 1) * 2 ^ (B * n))
      = ∑ k ∈ Finset.range n, C k * 2 ^ (B * (k + 1)) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    · rw [if_neg (by omega : n + 1 ≠ 0)] at *
      rw [if_neg (by omega : n ≠ 0)] at ih ⊢
      simp only [Nat.add_sub_cancel] at *
      omega

lemma geom_shift (B : ℕ) :
    ∀ n : ℕ,
      2 ^ B * (∑ k ∈ Finset.range n, 2 ^ (B * k))
        = (∑ k ∈ Finset.range n, 2 ^ (B * k)) + 2 ^ (B * n) - 1 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Nat.mul_add, ih]
    have h1 : (2 : ℕ) ^ B * 2 ^ (B * n) = 2 ^ (B * (n + 1)) := by
      rw [← pow_add]; congr 1; ring
    have hge : 1 ≤ 2 ^ (B * n) := Nat.one_le_two_pow
    have hge2 : 1 ≤ ∑ k ∈ Finset.range n, 2 ^ (B * k) + 2 ^ (B * n) := by omega
    rw [h1]; omega

def carryOffset (B : ℕ) : ℕ := (m + 1) * 2 ^ (B + 1)

structure BigIntParams (p m : ℕ) where
  
  B : ℕ
  
  W : ℕ
  
  hB : 2 ^ B < p
  
  hW : 2 ^ W < p
  
  hB1 : 1 ≤ B
  
  hWB : carryOffset (m := m) B * 2 < 2 ^ W
  
  hWp : (m + 1) * 2 ^ (2 * B) * 3 + 2 ^ W * 2 ^ B + 2 ^ W < p
  
  hp : 2 ^ (2 * B) * (m + 1) * 4 < p

lemma per_index_lift {B : ℕ} (a cinF b c off : F p) (cinN offN : ℕ)
    (hpB : 2 ^ B < p) (hcin : cinF.val = cinN) (hoff : off.val = offN)
    (hlhs : a.val + cinN + offN * 2 ^ B < p)
    (hrhs : b.val + c.val * 2 ^ B + offN < p)
    (heq : a + cinF + off * (2 ^ B : F p) = b + c * (2 ^ B : F p) + off) :
    a.val + cinN + offN * 2 ^ B = b.val + c.val * 2 ^ B + offN := by
  have hpow_val_cast : ((2 ^ B : ℕ) : F p) = (2 ^ B : F p) := by push_cast; ring
  have hpow_val : (2 ^ B : F p).val = 2 ^ B := by
    rw [← hpow_val_cast, ZMod.val_natCast_of_lt hpB]
  have hoffcast : ((offN : ℕ) : F p) = off := by rw [← hoff, ZMod.natCast_zmod_val]
  have hcincast : ((cinN : ℕ) : F p) = cinF := by rw [← hcin, ZMod.natCast_zmod_val]
  have hacast : ((a.val : ℕ) : F p) = a := ZMod.natCast_zmod_val a
  have hbcast : ((b.val : ℕ) : F p) = b := ZMod.natCast_zmod_val b
  have hccast : ((c.val : ℕ) : F p) = c := ZMod.natCast_zmod_val c
  -- LHS val
  have hlhs_cast : a + cinF + off * (2 ^ B : F p)
      = ((a.val + cinN + offN * 2 ^ B : ℕ) : F p) := by
    push_cast [hacast, hcincast, hoffcast, hpow_val_cast]; ring
  have hlhs_val : (a + cinF + off * (2 ^ B : F p)).val = a.val + cinN + offN * 2 ^ B := by
    rw [hlhs_cast, ZMod.val_natCast_of_lt hlhs]
  -- RHS val
  have hrhs_cast : b + c * (2 ^ B : F p) + off
      = ((b.val + c.val * 2 ^ B + offN : ℕ) : F p) := by
    push_cast [hbcast, hccast, hoffcast, hpow_val_cast]; ring
  have hrhs_val : (b + c * (2 ^ B : F p) + off).val = b.val + c.val * 2 ^ B + offN := by
    rw [hrhs_cast, ZMod.val_natCast_of_lt hrhs]
  have := congrArg ZMod.val heq
  rw [hlhs_val, hrhs_val] at this
  exact this

end

section
variable {p : ℕ} [Fact p.Prime]
variable {m : ℕ} [NeZero m]

lemma ripple_carry (B : ℕ) (g : ℕ → ℕ) (hg : ∀ j, g j ≤ 2 * (2 ^ B - 1)) :
    ∀ k : ℕ,
      let P : ℕ → ℕ := fun k => 1 + ∑ j ∈ Finset.range (k + 1), g j * 2 ^ (B * j)
      (P k / 2 ^ (B * k)) ≤ 2 ^ (B + 1) - 1 ∧
      P k / 2 ^ (B * (k + 1)) ≤ 1 := by
  have hBpos : 0 < 2 ^ B := Nat.two_pow_pos B
  have hcarry_bit : (2 ^ (B + 1) - 1) / 2 ^ B ≤ 1 := by
    rw [Nat.div_le_iff_le_mul_add_pred hBpos]
    rw [pow_succ]; omega
  intro k P
  induction k with
  | zero =>
    refine ⟨?_, ?_⟩
    · show P 0 / 2 ^ (B * 0) ≤ _
      have hP0 : P 0 = 1 + g 0 := by
        simp only [P, Finset.sum_range_succ, Finset.sum_range_zero, Nat.mul_zero, pow_zero]; ring
      rw [hP0, Nat.mul_zero, pow_zero, Nat.div_one]
      have := hg 0
      have : 2 * (2 ^ B - 1) + 1 ≤ 2 ^ (B + 1) - 1 := by rw [pow_succ]; omega
      omega
    · show P 0 / 2 ^ (B * (0 + 1)) ≤ 1
      have hP0 : P 0 = 1 + g 0 := by
        simp only [P, Finset.sum_range_succ, Finset.sum_range_zero, Nat.mul_zero, pow_zero]; ring
      rw [hP0, Nat.zero_add, Nat.mul_one]
      have hg0 := hg 0
      have hub : 1 + g 0 ≤ 2 ^ (B + 1) - 1 := by rw [pow_succ]; omega
      calc (1 + g 0) / 2 ^ B ≤ (2 ^ (B + 1) - 1) / 2 ^ B := Nat.div_le_div_right hub
        _ ≤ 1 := hcarry_bit
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih
    -- P (n+1) = P n + g (n+1) * 2^(B*(n+1))
    have hPsucc : P (n + 1) = P n + g (n + 1) * 2 ^ (B * (n + 1)) := by
      simp only [P, Finset.sum_range_succ]; ring
    -- P n / 2^(B*(n+1)) = c n = ih2 (≤ 1)
    -- P (n+1) / 2^(B*(n+1)) = P n / 2^(B*(n+1)) + g (n+1)
    have hdiv1 : P (n + 1) / 2 ^ (B * (n + 1)) = P n / 2 ^ (B * (n + 1)) + g (n + 1) := by
      rw [hPsucc, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _)]
    refine ⟨?_, ?_⟩
    · -- carry-in bound for next: P(n+1)/2^(B*(n+1)) ≤ 2^(B+1)-1
      rw [hdiv1]
      have := hg (n + 1)
      have hub : 2 * (2 ^ B - 1) + 1 ≤ 2 ^ (B + 1) - 1 := by rw [pow_succ]; omega
      omega
    · -- next carry is a bit
      have hdiv2 : P (n + 1) / 2 ^ (B * (n + 1 + 1))
          = (P n / 2 ^ (B * (n + 1)) + g (n + 1)) / 2 ^ B := by
        rw [show B * (n + 1 + 1) = B * (n + 1) + B by ring, pow_add,
          ← Nat.div_div_eq_div_mul, hdiv1]
      rw [hdiv2]
      have := hg (n + 1)
      have hsum : P n / 2 ^ (B * (n + 1)) + g (n + 1) ≤ 2 ^ (B + 1) - 1 := by
        rw [pow_succ]; omega
      calc (P n / 2 ^ (B * (n + 1)) + g (n + 1)) / 2 ^ B
          ≤ (2 ^ (B + 1) - 1) / 2 ^ B := Nat.div_le_div_right hsum
        _ ≤ 1 := hcarry_bit

lemma digit_extract (B : ℕ) (f : ℕ → ℕ) (hf : ∀ j, f j < 2 ^ B) :
    ∀ (m k : ℕ), k < m →
      (∑ j ∈ Finset.range m, f j * 2 ^ (B * j)) / 2 ^ (B * k) % 2 ^ B = f k := by
  intro m
  induction m with
  | zero => intro k hk; omega
  | succ n ih =>
    intro k hk
    rw [Finset.sum_range_succ]
    rcases Nat.lt_or_ge k n with hlt | hge
    · -- k < n: the top term f n * 2^(B*n) is a multiple of 2^(B*k)*2^B, doesn't affect digit k
      have hfac : (2 : ℕ) ^ (B * n) = 2 ^ (B * k) * 2 ^ B * 2 ^ (B * (n - k - 1)) := by
        rw [← pow_add, ← pow_add]; congr 1
        have hn : B * k + B + B * (n - k - 1) = B * (k + 1 + (n - k - 1)) := by ring
        rw [hn]; congr 1; omega
      rw [hfac, show f n * (2 ^ (B * k) * 2 ^ B * 2 ^ (B * (n - k - 1)))
          = (f n * 2 ^ (B * (n - k - 1)) * 2 ^ B) * 2 ^ (B * k) by ring,
        Nat.add_mul_div_right _ _ (Nat.two_pow_pos (B * k)), Nat.add_mul_mod_self_right]
      exact ih k hlt
    · -- k = n: lower sum < 2^(B*n), so it doesn't reach digit n
      have hkn : k = n := by omega
      subst hkn
      have hlow : (∑ j ∈ Finset.range k, f j * 2 ^ (B * j)) < 2 ^ (B * k) := by
        rw [← Fin.sum_univ_eq_sum_range (fun j => f j * 2 ^ (B * j)) k]
        exact sum_lt_pow (fun j : Fin k => f j) (fun j => hf _)
      rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos (B * k)),
        Nat.div_eq_of_lt hlow, Nat.zero_add, Nat.mod_eq_of_lt (hf k)]

lemma limb_stable (B : ℕ) (g : ℕ → ℕ) :
    let P : ℕ → ℕ := fun k => 1 + ∑ j ∈ Finset.range (k + 1), g j * 2 ^ (B * j)
    ∀ k k', k ≤ k' → P k' / 2 ^ (B * k) % 2 ^ B = P k / 2 ^ (B * k) % 2 ^ B := by
  intro P k k' hk
  induction k' with
  | zero => simp only [Nat.le_zero] at hk; subst hk; rfl
  | succ n ih =>
    rcases Nat.lt_or_ge k (n + 1) with hlt | hge
    · -- k ≤ n, use ih then add limb (n+1)
      have hkn : k ≤ n := by omega
      rw [← ih hkn]
      -- P (n+1) = P n + g (n+1) * 2^(B*(n+1)); the added term is a multiple of 2^(B*k)*2^B
      have hPsucc : P (n + 1) = P n + g (n + 1) * 2 ^ (B * (n + 1)) := by
        simp only [P, Finset.sum_range_succ]; ring
      rw [hPsucc]
      have hfac : (2 : ℕ) ^ (B * (n + 1)) = 2 ^ (B * k) * 2 ^ B * 2 ^ (B * (n - k)) := by
        rw [← pow_add, ← pow_add]; congr 1
        have hn : B * k + B + B * (n - k) = B * (k + 1 + (n - k)) := by ring
        rw [hn]; congr 1; omega
      rw [hfac]
      rw [show g (n + 1) * (2 ^ (B * k) * 2 ^ B * 2 ^ (B * (n - k)))
          = (g (n + 1) * 2 ^ (B * (n - k)) * 2 ^ B) * 2 ^ (B * k) by ring]
      rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos (B * k))]
      rw [Nat.add_mul_mod_self_right]
    · -- k = n+1
      have : k = n + 1 := by omega
      subst this; rfl

lemma ripple_eq (B : ℕ) (g : ℕ → ℕ) (k : ℕ) :
    let P : ℕ → ℕ := fun k => 1 + ∑ j ∈ Finset.range (k + 1), g j * 2 ^ (B * j)
    g k + (if k = 0 then 1 else P (k - 1) / 2 ^ (B * k))
      = (P k / 2 ^ (B * k)) % 2 ^ B + (P k / 2 ^ (B * (k + 1))) * 2 ^ B := by
  intro P
  have hkey : P k / 2 ^ (B * k) = g k + (if k = 0 then 1 else P (k - 1) / 2 ^ (B * k)) := by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      simp only [Nat.mul_zero, pow_zero, Nat.div_one, if_pos]
      show P 0 = g 0 + 1
      simp only [P, Finset.sum_range_succ, Finset.sum_range_zero, Nat.mul_zero, pow_zero]; ring
    · rw [if_neg (by omega : ¬ k = 0)]
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      have hPsucc : P (n + 1) = P n + g (n + 1) * 2 ^ (B * (n + 1)) := by
        simp only [P, Finset.sum_range_succ]; ring
      rw [hPsucc, Nat.succ_sub_one,
        Nat.add_mul_div_right _ _ (Nat.two_pow_pos (B * (n + 1)))]
      ring
  -- x = x % 2^B + (x / 2^B) * 2^B, with x = P k / 2^(B*k)
  have hdiv : P k / 2 ^ (B * (k + 1)) = (P k / 2 ^ (B * k)) / 2 ^ B := by
    rw [show B * (k + 1) = B * k + B by ring, pow_add, Nat.div_div_eq_div_mul]
  rw [hdiv, hkey]
  exact (Nat.mod_add_div' _ _).symm

lemma per_limb_lift {B : ℕ} (a d cin one b c : F p)
    (hpB : 2 ^ B < p)
    (hsum_lt : a.val + d.val + cin.val + one.val < p)
    (hrhs_lt : b.val + c.val * 2 ^ B < p)
    (heq : a + d + cin + one - b - c * (2 ^ B : F p) = 0) :
    a.val + d.val + cin.val + one.val = b.val + c.val * 2 ^ B := by
  have hpow_val_cast : ((2 ^ B : ℕ) : F p) = (2 ^ B : F p) := by push_cast; ring
  have hpow_val : (2 ^ B : F p).val = 2 ^ B := by
    rw [← hpow_val_cast, ZMod.val_natCast_of_lt hpB]
  have heq' : a + d + cin + one = b + c * (2 ^ B : F p) := by
    rw [← sub_eq_zero]; rw [← heq]; ring
  have hlhs : (a + d + cin + one).val = a.val + d.val + cin.val + one.val := by
    have hcast : a + d + cin + one
        = ((a.val + d.val + cin.val + one.val : ℕ) : F p) := by
      push_cast
      rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val,
        ZMod.natCast_zmod_val]
    rw [hcast, ZMod.val_natCast_of_lt hsum_lt]
  have hmul : (c * (2 ^ B : F p)).val = c.val * 2 ^ B := by
    rw [ZMod.val_mul, hpow_val, Nat.mod_eq_of_lt]
    omega
  have hrhs : (b + c * (2 ^ B : F p)).val = b.val + c.val * 2 ^ B := by
    have hcast : b + c * (2 ^ B : F p) = ((b.val + c.val * 2 ^ B : ℕ) : F p) := by
      push_cast
      rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    rw [hcast, ZMod.val_natCast_of_lt hrhs_lt]
  have := congrArg ZMod.val heq'
  rw [hlhs, hrhs] at this
  exact this

end

end Solution.Secp256k1ScalarMul
