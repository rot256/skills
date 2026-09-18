import Solution.Secp256k1ScalarMul.EqViaCarries
import Solution.Secp256k1ScalarMul.RangeCheck



namespace Solution.Secp256k1ScalarMul

section
variable {p : ℕ} [Fact p.Prime]
variable {m : ℕ} [NeZero m]

namespace MulMod


def polyEvalExpr {n : ℕ} (coeffs : Vector (Expression (F p)) n) (x : F p) : Expression (F p) :=
  Fin.foldl n (fun acc (i : Fin n) => acc + coeffs[i.val] * (x ^ i.val : F p)) 0


lemma polyEvalExpr_eval {n : ℕ} (env : Environment (F p))
    (coeffs : Vector (Expression (F p)) n) (x : F p) :
    Expression.eval env (polyEvalExpr coeffs x)
      = ∑ i : Fin n, (Expression.eval env coeffs[i.val]) * x ^ i.val := by
  simp only [polyEvalExpr]
  induction n with
  | zero => simp only [Fin.foldl_zero, Expression.eval, Finset.univ_eq_empty, Finset.sum_empty]
  | succ k ih =>
    obtain ih := ih coeffs.pop
    simp only [Vector.getElem_pop'] at ih
    rw [Fin.foldl_succ_last, Fin.sum_univ_castSucc]
    simp only [Expression.eval, Fin.val_last, Fin.val_castSucc]
    rw [← ih]

end MulMod


def carryOffsetG (B : ℕ) : ℕ := (m + 1) * (2 ^ B + 2)


lemma partial_div_boundG (B m : ℕ) (hB1 : 1 ≤ B) (f : ℕ → ℕ)
    (hf : ∀ j, f j < (m + 1) * 2 ^ (2 * B)) (k : ℕ) :
    (∑ j ∈ Finset.range (k + 1), f j * 2 ^ (B * j)) / 2 ^ (B * (k + 1))
      ≤ (m + 1) * (2 ^ B + 2) := by
  have hZ2 : 2 ≤ (2 : ℕ) ^ B := by
    calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ B := Nat.pow_le_pow_right (by norm_num) hB1
  have hgeo : (∑ j ∈ Finset.range (k + 1), 2 ^ (B * j)) * (2 ^ B - 1)
      = 2 ^ (B * (k + 1)) - 1 := by
    induction k with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, Nat.add_mul, ih]
      have hpow : (2 : ℕ) ^ (B * (n + 1)) * 2 ^ B = 2 ^ (B * (n + 1 + 1)) := by
        rw [← pow_add]; congr 1
      have h1 : 1 ≤ (2 : ℕ) ^ (B * (n + 1)) := Nat.one_le_two_pow
      obtain ⟨b, hb⟩ := Nat.exists_eq_add_of_le hZ2
      rw [hb] at hpow ⊢
      have e3 : 2 + b - 1 = 1 + b := by omega
      rw [e3, show (2 : ℕ) ^ (B * (n + 1)) * (1 + b)
            = 2 ^ (B * (n + 1)) + 2 ^ (B * (n + 1)) * b from by rw [Nat.mul_add, Nat.mul_one]]
      rw [show (2 : ℕ) ^ (B * (n + 1)) * (2 + b)
            = 2 ^ (B * (n + 1)) * 2 + 2 ^ (B * (n + 1)) * b from by rw [Nat.mul_add]] at hpow
      omega
  have hsum_le : (∑ j ∈ Finset.range (k + 1), f j * 2 ^ (B * j))
      ≤ (m + 1) * 2 ^ (2 * B) * ∑ j ∈ Finset.range (k + 1), 2 ^ (B * j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    apply Nat.mul_le_mul_right
    have := hf j; omega
  refine Nat.div_le_of_le_mul (le_trans hsum_le ?_)
  refine Nat.le_of_mul_le_mul_right ?_ (show 0 < (2 : ℕ) ^ B - 1 by omega)
  rw [Nat.mul_assoc ((m + 1) * 2 ^ (2 * B)), hgeo]
  have hX : (2 : ℕ) ^ (2 * B) = 2 ^ B * 2 ^ B := by rw [← pow_add]; congr 1; ring
  have hY1 : 1 ≤ (2 : ℕ) ^ (B * (k + 1)) := Nat.one_le_two_pow
  rw [hX]
  obtain ⟨y, hy⟩ := Nat.exists_eq_add_of_le hY1
  obtain ⟨z, hz⟩ := Nat.exists_eq_add_of_le hZ2
  rw [hy, hz]
  have e1 : 1 + y - 1 = y := by omega
  have e2 : 2 + z - 1 = 1 + z := by omega
  rw [e1, e2]
  calc (m + 1) * ((2 + z) * (2 + z)) * y
      ≤ (m + 1) * ((2 + z + 2) * (1 + z)) * (1 + y) := by
        have hzz : (2 + z) * (2 + z) ≤ (2 + z + 2) * (1 + z) := by nlinarith [Nat.zero_le z]
        exact Nat.mul_le_mul (Nat.mul_le_mul_left _ hzz) (Nat.le_add_left y 1)
    _ = (1 + y) * ((m + 1) * (2 + z + 2)) * (1 + z) := by ring

namespace GroupedEq




def numGroups (m g : ℕ) : ℕ := (2 * m - 1 + (g - 1)) / g

private lemma ceil_mul_ge (a g : ℕ) (hg : 1 ≤ g) : a ≤ g * ((a + (g - 1)) / g) := by
  have hdm := Nat.div_add_mod (a + (g - 1)) g
  have hr : (a + (g - 1)) % g < g := Nat.mod_lt _ (by omega)
  generalize hX : g * ((a + (g - 1)) / g) = X at hdm ⊢
  omega

private lemma ceil_pred_mul_lt (a g : ℕ) (hg : 1 ≤ g) (ha : 0 < a) :
    g * ((a + (g - 1)) / g - 1) < a := by
  have hdm := Nat.div_add_mod (a + (g - 1)) g
  have hr : (a + (g - 1)) % g < g := Nat.mod_lt _ (by omega)
  rcases Nat.eq_zero_or_pos ((a + (g - 1)) / g) with h0 | hpos
  · rw [h0]
    simpa using ha
  · obtain ⟨t, ht⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : (a + (g - 1)) / g ≠ 0)
    rw [ht, Nat.succ_sub_one]
    have h2 : g * (t + 1) = g * t + g := by ring
    rw [ht, h2] at hdm
    generalize hX : g * t = X at hdm ⊢
    omega


lemma numGroups_mul_ge (m g : ℕ) (hg : 1 ≤ g) : 2 * m - 1 ≤ g * numGroups m g :=
  ceil_mul_ge (2 * m - 1) g hg


lemma numGroups_pred_mul_lt (m g : ℕ) [NeZero m] (hg : 1 ≤ g) :
    g * (numGroups m g - 1) < 2 * m - 1 :=
  ceil_pred_mul_lt (2 * m - 1) g hg (by have := Nat.pos_of_neZero m; omega)


lemma numGroups_pos (m g : ℕ) [NeZero m] (hg : 1 ≤ g) : 0 < numGroups m g := by
  have hm : 0 < 2 * m - 1 := by have := Nat.pos_of_neZero m; omega
  have h := numGroups_mul_ge m g hg
  rcases Nat.eq_zero_or_pos (numGroups m g) with h0 | hpos
  · rw [h0, Nat.mul_zero] at h; omega
  · exact hpos




lemma group_flatten (B g : ℕ) (f : ℕ → ℕ) :
    ∀ G : ℕ, (∑ j ∈ Finset.range G,
        (∑ i ∈ Finset.range g, f (g * j + i) * 2 ^ (B * i)) * 2 ^ (B * g * j))
      = ∑ t ∈ Finset.range (g * G), f t * 2 ^ (B * t) := by
  intro G
  induction G with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Nat.mul_succ, Finset.sum_range_add]
    congr 1
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [show B * (g * n + i) = B * i + B * g * n from by ring, pow_add]
    ring


lemma sum_extend_zero (B N M : ℕ) (f : ℕ → ℕ) (hNM : N ≤ M)
    (hf : ∀ t, N ≤ t → f t = 0) :
    (∑ t ∈ Finset.range N, f t * 2 ^ (B * t)) = ∑ t ∈ Finset.range M, f t * 2 ^ (B * t) := by
  apply Finset.sum_subset
    (fun x hx => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hNM))
  intro x _ hx
  simp only [Finset.mem_range, not_lt] at hx
  rw [hf x hx, Nat.zero_mul]


lemma geom_sum_le (B : ℕ) (hB : 1 ≤ B) :
    ∀ g : ℕ, 1 ≤ g → (∑ i ∈ Finset.range g, 2 ^ (B * i)) ≤ 2 ^ (B * (g - 1)) * 2 := by
  intro g
  induction g with
  | zero => omega
  | succ t ih =>
    intro _
    rcases Nat.eq_zero_or_pos t with h0 | hpos
    · subst h0
      norm_num
    · rw [Finset.sum_range_succ, Nat.succ_sub_one]
      have h1 := ih hpos
      have h2 : 2 ^ (B * (t - 1)) * 2 ≤ 2 ^ (B * t) := by
        have hle : B * (t - 1) + 1 ≤ B * t := by
          have hstep : B * (t - 1) + B = B * t := by
            rw [← Nat.mul_succ]
            congr 1
            omega
          omega
        calc 2 ^ (B * (t - 1)) * 2 = 2 ^ (B * (t - 1) + 1) := by rw [pow_succ]
          _ ≤ 2 ^ (B * t) := Nat.pow_le_pow_right (by norm_num) hle
      calc (∑ i ∈ Finset.range t, 2 ^ (B * i)) + 2 ^ (B * t)
          ≤ 2 ^ (B * (t - 1)) * 2 + 2 ^ (B * t) := by omega
        _ ≤ 2 ^ (B * t) + 2 ^ (B * t) := by omega
        _ = 2 ^ (B * t) * 2 := by ring




def groupExpr (B g : ℕ) (x : Var (EqViaCarries.Coeffs m) (F p)) (k : ℕ) :
    Expression (F p) :=
  MulMod.polyEvalExpr
    (Vector.ofFn fun i : Fin g =>
      if h : g * k + i.val < 2 * m - 1 then x[g * k + i.val]'h else 0)
    ((2 : F p) ^ B)


lemma groupExpr_eval (env : Environment (F p)) (B g : ℕ)
    (x : Var (EqViaCarries.Coeffs m) (F p)) (k : ℕ) :
    Expression.eval env (groupExpr B g x k)
      = ∑ i ∈ Finset.range g,
          (if h : g * k + i < 2 * m - 1 then Expression.eval env (x[g * k + i]'h) else 0)
            * ((2 : F p) ^ B) ^ i := by
  rw [groupExpr, MulMod.polyEvalExpr_eval,
    ← Fin.sum_univ_eq_sum_range (fun i =>
      (if h : g * k + i < 2 * m - 1 then Expression.eval env (x[g * k + i]'h) else 0)
        * ((2 : F p) ^ B) ^ i)]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [Vector.getElem_ofFn]
  by_cases h : g * k + i.val < 2 * m - 1
  · rw [dif_pos h, dif_pos h]
  · rw [dif_neg h, dif_neg h]
    rfl


def carryExpr (B g OFF : ℕ) (lhs rhs : Var (EqViaCarries.Coeffs m) (F p)) :
    ℕ → Expression (F p)
  | 0 =>
      (groupExpr B g lhs 0 - groupExpr B g rhs 0) / ((2 : F p) ^ (B * g))
        + (OFF : F p)
  | k + 1 =>
      (groupExpr B g lhs (k + 1) + (carryExpr B g OFF lhs rhs k - (OFF : F p))
          - groupExpr B g rhs (k + 1)) / ((2 : F p) ^ (B * g))
        + (OFF : F p)


def carryInExpr (B g OFF : ℕ) (lhs rhs : Var (EqViaCarries.Coeffs m) (F p))
    (k : ℕ) : Expression (F p) :=
  if h : k = 0 then 0 else carryExpr B g OFF lhs rhs (k - 1) - (OFF : F p)




def GHyps (p m B W g : ℕ) : Prop :=
  1 ≤ g ∧ 2 ^ (B * g) < p ∧
    (m + 1) * 2 ^ (2 * B) * 2 ^ (B * (g - 1)) * 2
      + 2 ^ W * 2 ^ (B * g) + (m + 1) * (2 ^ B + 2) * 2 ^ (B * g) + 2 ^ W < p




def main (P : BigIntParams p m) (g : ℕ) [Fact (p > 2)]
    (input : Var (EqViaCarries.Inputs m) (F p)) :
    Circuit (F p) Unit := do
  let Pc := input.lhs
  let Sc := input.rhs

  -- 1. range-check each affine carry to `W` bits (implicit top bit).
  have hWpos : 1 ≤ P.W := by
    obtain ⟨B, W, hB, hW, hB1, hWB, hWp, hp⟩ := P
    replace hWB : carryOffsetG (m := m) B * 2 < 2 ^ W := by
      have hb : (2 : ℕ) ≤ 2 ^ B := by
        calc (2 : ℕ) = 2 ^ 1 := rfl
          _ ≤ 2 ^ B := Nat.pow_le_pow_right (by norm_num) hB1
      have hle : carryOffsetG (m := m) B ≤ carryOffset (m := m) B := by
        unfold carryOffsetG carryOffset
        have h2 : 2 ^ B + 2 ≤ 2 ^ (B + 1) := by rw [pow_succ]; omega
        exact Nat.mul_le_mul_left _ h2
      omega
    by_contra h
    have hW0 : W = 0 := Nat.lt_one_iff.mp (Nat.lt_of_not_ge h)
    have hlt : carryOffsetG (m := m) B * 2 < 1 := by
      simpa [hW0] using hWB
    have hpos : 0 < carryOffsetG (m := m) B * 2 := by
      unfold carryOffsetG
      positivity
    omega
  let carryChecks : Vector (Expression (F p)) (numGroups m g - 1) :=
    Vector.mapFinRange (numGroups m g - 1) fun k =>
      carryExpr P.B g (carryOffsetG (m := m) P.B) Pc Sc k.val
  Circuit.forEach carryChecks (fun c => RangeCheck.circuit P.W P.hW hWpos c)

  -- 2. final group equation: top signed carry-out is zero.
  let last := numGroups m g - 1
  assertZero
    (groupExpr P.B g Pc last
      + carryInExpr P.B g (carryOffsetG (m := m) P.B) Pc Sc last
      - groupExpr P.B g Sc last)

instance elaborated (P : BigIntParams p m) (g : ℕ) [Fact (p > 2)] :
    ElaboratedCircuit (F p) (EqViaCarries.Inputs m) unit (main P g) where
  localLength _ := (numGroups m g - 1) * (P.W - 1)
  localLength_eq := by
    intro input offset
    simp only [main, circuit_norm, RangeCheck.circuit]
  subcircuitsConsistent := by
    intro input offset
    simp +arith only [main, circuit_norm, RangeCheck.circuit]
  channelsLawful := by
    intro offset
    simp only [main, circuit_norm, RangeCheck.circuit]




def circuit (P : BigIntParams p m) (g : ℕ) (hgp : GHyps p m P.B P.W g)
    [Fact (p > 2)] : FormalAssertion (F p) (EqViaCarries.Inputs m) where
    main := main P g
    Assumptions := EqViaCarries.Assumptions P.B
    Spec := EqViaCarries.Spec P.B
    soundness := by
      obtain ⟨B, W, hB, hW, hB1, hWB, hWp, hp⟩ := P
      obtain ⟨hg1, hpBg, hGWp⟩ := hgp
      circuit_proof_start
      replace hWB : carryOffsetG (m := m) B * 2 < 2 ^ W := by
        have hb : (2 : ℕ) ≤ 2 ^ B := by
          calc (2 : ℕ) = 2 ^ 1 := rfl
            _ ≤ 2 ^ B := Nat.pow_le_pow_right (by norm_num) hB1
        have hle : carryOffsetG (m := m) B ≤ carryOffset (m := m) B := by
          unfold carryOffsetG carryOffset
          have h2 : 2 ^ B + 2 ≤ 2 ^ (B + 1) := by rw [pow_succ]; omega
          exact Nat.mul_le_mul_left _ h2
        omega
      simp only [circuit_norm, RangeCheck.circuit] at h_holds ⊢
      obtain ⟨h_range, h_lin⟩ := h_holds
      have hM : 0 < 2 * m - 1 := by have := Nat.pos_of_neZero m; omega
      have hG1 : 0 < numGroups m g := numGroups_pos m g hg1
      have hCov : 2 * m - 1 ≤ g * numGroups m g := numGroups_mul_ge m g hg1
      set G := numGroups m g with hGdef
      set OFFn := carryOffsetG (m := m) B with hOFFn
      have hOFF_eq : OFFn = (m + 1) * (2 ^ B + 2) := rfl
      -- coefficient-level digit functions (vanish beyond 2m−1)
      set Pn : ℕ → ℕ := fun k => if h : k < 2 * m - 1 then (input.lhs[k]'h).val else 0 with hPn
      set Sn : ℕ → ℕ := fun k => if h : k < 2 * m - 1 then (input.rhs[k]'h).val else 0 with hSn
      -- group digit functions
      set QP : ℕ → ℕ := fun j => ∑ i ∈ Finset.range g, Pn (g * j + i) * 2 ^ (B * i) with hQP
      set QS : ℕ → ℕ := fun j => ∑ i ∈ Finset.range g, Sn (g * j + i) * 2 ^ (B * i) with hQS
      have hQP_app : ∀ j, QP j = ∑ i ∈ Finset.range g, Pn (g * j + i) * 2 ^ (B * i) :=
        fun _ => rfl
      have hQS_app : ∀ j, QS j = ∑ i ∈ Finset.range g, Sn (g * j + i) * 2 ^ (B * i) :=
        fun _ => rfl
      -- carries (top group's effective offset carry-out is OFFn by construction)
      set Cn : ℕ → ℕ := fun k => if k = G - 1 then OFFn
        else (Expression.eval env (carryExpr B g OFFn input_var.lhs input_var.rhs k)).val with hCn
      have hOFF_pos : 0 < OFFn := by rw [hOFF_eq]; positivity
      -- bounds
      have hCn_lt : ∀ k, k < G → Cn k < 2 ^ W := by
        intro k hk
        by_cases hktop : k = G - 1
        · simp only [hCn, if_pos hktop]
          omega
        · simp only [hCn, if_neg hktop]
          simpa [RangeCheck.Spec] using h_range ⟨k, by omega⟩ trivial
      have hPn_lt : ∀ k, Pn k < (m + 1) * 2 ^ (2 * B) := by
        intro k; simp only [hPn]; split
        · rename_i h; exact h_assumptions.1 ⟨k, h⟩
        · positivity
      have hSn_lt : ∀ k, Sn k < (m + 1) * 2 ^ (2 * B) := by
        intro k; simp only [hSn]; split
        · rename_i h; exact h_assumptions.2 ⟨k, h⟩
        · positivity
      -- group digit bound X₂
      set X2 : ℕ := (m + 1) * 2 ^ (2 * B) * 2 ^ (B * (g - 1)) * 2 with hX2
      have hgeo := geom_sum_le B hB1 g hg1
      have hQ_lt : ∀ (Q : ℕ → ℕ), (∀ k, Q k = ∑ i ∈ Finset.range g, (fun t =>
          if h : t < 2 * m - 1 then 0 else 0) 0 * 0) → True := fun _ _ => trivial
      have hQP_lt : ∀ j, QP j < X2 := by
        intro j
        have hle : QP j ≤ ((m + 1) * 2 ^ (2 * B) - 1) * ∑ i ∈ Finset.range g, 2 ^ (B * i) := by
          rw [hQP_app, Finset.mul_sum]
          apply Finset.sum_le_sum
          intro i _
          have := hPn_lt (g * j + i)
          exact Nat.mul_le_mul_right _ (by omega)
        have hb_pos : 0 < (m + 1) * 2 ^ (2 * B) := by positivity
        calc QP j ≤ ((m + 1) * 2 ^ (2 * B) - 1) * ∑ i ∈ Finset.range g, 2 ^ (B * i) := hle
          _ ≤ ((m + 1) * 2 ^ (2 * B) - 1) * (2 ^ (B * (g - 1)) * 2) :=
              Nat.mul_le_mul_left _ hgeo
          _ < (m + 1) * 2 ^ (2 * B) * (2 ^ (B * (g - 1)) * 2) := by
              refine (Nat.mul_lt_mul_right (by positivity)).mpr ?_
              have hb0 : 0 < (m + 1) * 2 ^ (2 * B) := by positivity
              omega
          _ = X2 := by rw [hX2]; ring
      have hQS_lt : ∀ j, QS j < X2 := by
        intro j
        have hle : QS j ≤ ((m + 1) * 2 ^ (2 * B) - 1) * ∑ i ∈ Finset.range g, 2 ^ (B * i) := by
          rw [hQS_app, Finset.mul_sum]
          apply Finset.sum_le_sum
          intro i _
          have := hSn_lt (g * j + i)
          exact Nat.mul_le_mul_right _ (by omega)
        calc QS j ≤ ((m + 1) * 2 ^ (2 * B) - 1) * ∑ i ∈ Finset.range g, 2 ^ (B * i) := hle
          _ ≤ ((m + 1) * 2 ^ (2 * B) - 1) * (2 ^ (B * (g - 1)) * 2) :=
              Nat.mul_le_mul_left _ hgeo
          _ < (m + 1) * 2 ^ (2 * B) * (2 ^ (B * (g - 1)) * 2) := by
              refine (Nat.mul_lt_mul_right (by positivity)).mpr ?_
              have hb0 : 0 < (m + 1) * 2 ^ (2 * B) := by positivity
              omega
          _ = X2 := by rw [hX2]; ring
      have hX2_lt_p : X2 < p := by rw [hX2]; omega
      have hBg_pos : (1 : ℕ) ≤ 2 ^ (B * g) := Nat.one_le_two_pow
      have hOFFn_lt : OFFn < p := by
        have h1 : OFFn ≤ OFFn * 2 ^ (B * g) := Nat.le_mul_of_pos_right _ (by omega)
        rw [hOFF_eq] at h1 ⊢
        omega
      have hOFFn_cast : (OFFn : F p).val = OFFn := ZMod.val_natCast_of_lt hOFFn_lt
      have hOFFn_le_W : OFFn ≤ 2 ^ W := by
        have : OFFn ≤ OFFn * 2 := Nat.le_mul_of_pos_right _ (by norm_num)
        omega
      -- eval bridges: the group-sum expressions evaluate to the ℕ group digits
      have ha_e : ∀ (j : ℕ) (hj : j < 2 * m - 1),
          Expression.eval env (input_var.lhs[j]'hj) = input.lhs[j]'hj := by
        intro j hj
        rw [← h_input]
        simp [Vector.getElem_map]
      have hb_e : ∀ (j : ℕ) (hj : j < 2 * m - 1),
          Expression.eval env (input_var.rhs[j]'hj) = input.rhs[j]'hj := by
        intro j hj
        rw [← h_input]
        simp [Vector.getElem_map]
      have hGP_e : ∀ j : ℕ, Expression.eval env (groupExpr B g input_var.lhs j)
          = ((QP j : ℕ) : F p) := by
        intro j
        rw [groupExpr_eval, hQP_app, Nat.cast_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [Nat.cast_mul]
        congr 1
        · by_cases h : g * j + i < 2 * m - 1
          · rw [dif_pos h, ha_e _ h]
            simp only [hPn, dif_pos h]
            rw [ZMod.natCast_zmod_val]
          · rw [dif_neg h]
            simp only [hPn, dif_neg h]
            simp
        · push_cast
          rw [pow_mul]
      have hGS_e : ∀ j : ℕ, Expression.eval env (groupExpr B g input_var.rhs j)
          = ((QS j : ℕ) : F p) := by
        intro j
        rw [groupExpr_eval, hQS_app, Nat.cast_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [Nat.cast_mul]
        congr 1
        · by_cases h : g * j + i < 2 * m - 1
          · rw [dif_pos h, hb_e _ h]
            simp only [hSn, dif_pos h]
            rw [ZMod.natCast_zmod_val]
          · rw [dif_neg h]
            simp only [hSn, dif_neg h]
            simp
        · push_cast
          rw [pow_mul]
      have hbase_ne : ((2 : F p) ^ (B * g) ≠ 0) := by
        have hnat : (((2 ^ (B * g) : ℕ) : F p) ≠ 0) := by
          intro hzero
          have hval : (((2 ^ (B * g) : ℕ) : F p).val) = 2 ^ (B * g) :=
            ZMod.val_natCast_of_lt hpBg
          rw [hzero, ZMod.val_zero] at hval
          have hpos : 0 < 2 ^ (B * g) := Nat.two_pow_pos _
          omega
        simpa [Nat.cast_pow] using hnat
      have hCn_cast : ∀ k, k < G → ((Cn k : ℕ) : F p)
          = if k = G - 1 then (OFFn : F p)
            else Expression.eval env (carryExpr B g OFFn input_var.lhs input_var.rhs k) := by
        intro k hk
        by_cases hktop : k = G - 1
        · subst k
          simp [hCn]
        · simp only [hCn, if_neg hktop]
          rw [ZMod.natCast_zmod_val]
      have hcarry_eval : ∀ k, k < G - 1 →
          Expression.eval env (carryExpr B g OFFn input_var.lhs input_var.rhs k)
            = ((Cn k : ℕ) : F p) := by
        intro k hk
        have h := hCn_cast k (by omega)
        rw [if_neg (by omega : ¬ k = G - 1)] at h
        exact h.symm
      -- top group's carry is OFFn by construction
      have hCtop : Cn (G - 1) = OFFn := by simp only [hCn, if_pos rfl]
      -- per-group ℕ equation
      have h_idx : ∀ k, (hk : k < G) →
          QP k + (if k = 0 then OFFn else Cn (k - 1)) + OFFn * 2 ^ (B * g)
            = QS k + Cn k * 2 ^ (B * g) + OFFn := by
        intro k hk
        have hCk_val : (((Cn k : ℕ) : F p)).val = Cn k :=
          ZMod.val_natCast_of_lt (lt_trans (hCn_lt k hk) hW)
        have hfield : ((QP k : ℕ) : F p)
            + (if k = 0 then (OFFn : F p) else ((Cn (k - 1) : ℕ) : F p))
            + (OFFn : F p) * (2 ^ (B * g) : F p)
            = ((QS k : ℕ) : F p) + ((Cn k : ℕ) : F p) * (2 ^ (B * g) : F p)
              + (OFFn : F p) := by
          by_cases hktop : k = G - 1
          · have hlin0 := h_lin
            rw [← hktop] at hlin0
            have hcin_eval : Expression.eval env
                (carryInExpr B g OFFn input_var.lhs input_var.rhs k)
                  = if k = 0 then (0 : F p)
                    else ((Cn (k - 1) : ℕ) : F p) - (OFFn : F p) := by
              by_cases hk0 : k = 0
              · simp [carryInExpr, hk0, Expression.eval]
              · have hprev := hcarry_eval (k - 1) (by omega)
                simp [carryInExpr, hk0, Expression.eval, hprev, sub_eq_add_neg]
            have hlinF : ((QP k : ℕ) : F p)
                  + (if k = 0 then (0 : F p)
                    else ((Cn (k - 1) : ℕ) : F p) - (OFFn : F p))
                  + -((QS k : ℕ) : F p) = 0 := by
              simpa [hGP_e, hGS_e, hcin_eval] using hlin0
            have hCktop : Cn k = OFFn := by simp [hCn, hktop]
            rw [hCktop]
            rcases Nat.eq_zero_or_pos k with hk0 | hkpos
            · subst hk0
              simp only [↓reduceIte, add_zero] at hlinF ⊢
              linear_combination hlinF
            · simp only [if_neg (by omega : ¬ k = 0)] at hlinF ⊢
              linear_combination hlinF
          · rcases Nat.eq_zero_or_pos k with hk0 | hkpos
            · subst hk0
              have hcarry := hcarry_eval 0 (by omega)
              simp only [↓reduceIte]
              rw [← hcarry]
              simp [carryExpr, Expression.eval, hGP_e, hGS_e]
              field_simp [hbase_ne]
              ring_nf
            · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
              have hcarry := hcarry_eval (j + 1) (by omega)
              have hprev := hcarry_eval j (by omega)
              simp only [if_neg (by omega : ¬ j + 1 = 0)]
              rw [← hcarry]
              simp [carryExpr, Expression.eval, hGP_e, hGS_e, hprev]
              field_simp [hbase_ne]
              ring_nf
        -- lift to ℕ
        have hcin_val : (if k = 0 then (OFFn : F p) else ((Cn (k - 1) : ℕ) : F p)).val
            = if k = 0 then OFFn else Cn (k - 1) := by
          split
          · exact hOFFn_cast
          · exact ZMod.val_natCast_of_lt (lt_trans (hCn_lt (k - 1) (by omega)) hW)
        have hcin_le : (if k = 0 then OFFn else Cn (k - 1)) ≤ 2 ^ W := by
          split
          · exact hOFFn_le_W
          · have := hCn_lt (k - 1) (by omega); omega
        have hQPk_val : (((QP k : ℕ) : F p)).val = QP k :=
          ZMod.val_natCast_of_lt (lt_trans (hQP_lt k) hX2_lt_p)
        have hQSk_val : (((QS k : ℕ) : F p)).val = QS k :=
          ZMod.val_natCast_of_lt (lt_trans (hQS_lt k) hX2_lt_p)
        have hGWp' : X2 + 2 ^ W * 2 ^ (B * g) + OFFn * 2 ^ (B * g) + 2 ^ W < p := by
          rw [hX2, hOFF_eq]
          exact hGWp
        have hlhs : (((QP k : ℕ) : F p)).val + (if k = 0 then OFFn else Cn (k - 1))
            + OFFn * 2 ^ (B * g) < p := by
          rw [hQPk_val]
          have h1 := hQP_lt k
          omega
        have hrhs : (((QS k : ℕ) : F p)).val + (((Cn k : ℕ) : F p)).val * 2 ^ (B * g) + OFFn < p := by
          rw [hQSk_val, hCk_val]
          have h1 := hQS_lt k
          have hc : Cn k < 2 ^ W := hCn_lt k hk
          have hcB : Cn k * 2 ^ (B * g) ≤ 2 ^ W * 2 ^ (B * g) :=
            Nat.mul_le_mul_right _ (by omega)
          omega
        have hlift := per_index_lift (B := B * g) ((QP k : ℕ) : F p)
          (if k = 0 then (OFFn : F p) else ((Cn (k - 1) : ℕ) : F p))
          ((QS k : ℕ) : F p) ((Cn k : ℕ) : F p) (OFFn : F p)
          (if k = 0 then OFFn else Cn (k - 1)) OFFn hpBg hcin_val hOFFn_cast hlhs hrhs hfield
        rw [hCk_val, hQPk_val, hQSk_val] at hlift
        exact hlift
      -- express polyValue via the group digits
      have hpv_lhs : polyValue B input.lhs = ∑ k ∈ Finset.range G, QP k * 2 ^ (B * g * k) := by
        have h1 : polyValue B input.lhs = ∑ k ∈ Finset.range (2 * m - 1), Pn k * 2 ^ (B * k) := by
          rw [polyValue, ← Fin.sum_univ_eq_sum_range (fun k => Pn k * 2 ^ (B * k))]
          apply Finset.sum_congr rfl
          intro i _; simp only [hPn, dif_pos i.isLt]
        rw [h1, sum_extend_zero B (2 * m - 1) (g * G) Pn hCov
          (fun t ht => by simp only [hPn, dif_neg (by omega : ¬ t < 2 * m - 1)]),
          ← group_flatten B g Pn G]
      have hpv_rhs : polyValue B input.rhs = ∑ k ∈ Finset.range G, QS k * 2 ^ (B * g * k) := by
        have h1 : polyValue B input.rhs = ∑ k ∈ Finset.range (2 * m - 1), Sn k * 2 ^ (B * k) := by
          rw [polyValue, ← Fin.sum_univ_eq_sum_range (fun k => Sn k * 2 ^ (B * k))]
          apply Finset.sum_congr rfl
          intro i _; simp only [hSn, dif_pos i.isLt]
        rw [h1, sum_extend_zero B (2 * m - 1) (g * G) Sn hCov
          (fun t ht => by simp only [hSn, dif_neg (by omega : ¬ t < 2 * m - 1)]),
          ← group_flatten B g Sn G]
      rw [EqViaCarries.Spec, hpv_lhs, hpv_rhs]
      -- sum the per-group equations weighted by 2^(B·g·k) and telescope
      have hsum : (∑ k ∈ Finset.range G,
            ((QP k + (if k = 0 then OFFn else Cn (k - 1))) + OFFn * 2 ^ (B * g)) * 2 ^ (B * g * k))
          = ∑ k ∈ Finset.range G, (QS k + Cn k * 2 ^ (B * g) + OFFn) * 2 ^ (B * g * k) := by
        apply Finset.sum_congr rfl
        intro k hk; rw [Finset.mem_range] at hk; rw [h_idx k hk]
      set SP := ∑ k ∈ Finset.range G, QP k * 2 ^ (B * g * k) with hSP
      set SS := ∑ k ∈ Finset.range G, QS k * 2 ^ (B * g * k) with hSS
      set SC := ∑ k ∈ Finset.range G, Cn k * 2 ^ (B * g * (k + 1)) with hSC
      set SCin' := ∑ k ∈ Finset.range G,
        (if k = 0 then OFFn else Cn (k - 1)) * 2 ^ (B * g * k) with hSCin'
      set SCin := ∑ k ∈ Finset.range G,
        (if k = 0 then 0 else Cn (k - 1)) * 2 ^ (B * g * k) with hSCin
      set Gg := ∑ k ∈ Finset.range G, 2 ^ (B * g * k) with hGg
      have hSCin_rel : SCin' = SCin + OFFn := by
        rw [hSCin', hSCin, show G = (G - 1) + 1 from by omega]
        rw [Finset.sum_range_succ' _ (G - 1), Finset.sum_range_succ' _ (G - 1)]
        simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte,
          Nat.mul_zero, pow_zero, Nat.mul_one]
        ring
      have hLHS : (∑ k ∈ Finset.range G,
            ((QP k + (if k = 0 then OFFn else Cn (k - 1))) + OFFn * 2 ^ (B * g)) * 2 ^ (B * g * k))
          = SP + SCin' + OFFn * 2 ^ (B * g) * Gg := by
        rw [hSP, hSCin', hGg, Finset.mul_sum,
          ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _; ring
      have hRHS : (∑ k ∈ Finset.range G, (QS k + Cn k * 2 ^ (B * g) + OFFn) * 2 ^ (B * g * k))
          = SS + SC + OFFn * Gg := by
        rw [hSS, hSC, hGg, Finset.mul_sum,
          ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _
        rw [Nat.mul_add, Nat.mul_one, pow_add]; ring
      rw [hLHS, hRHS] at hsum
      have htel := carry_telescope (B * g) Cn G
      rw [if_neg (by omega : ¬ (G = 0)), hCtop] at htel
      rw [← hSCin, ← hSC] at htel
      have hgeo2 := geom_shift (B * g) G
      rw [← hGg] at hgeo2
      set Gtop := 2 ^ (B * g * G) with hGtop
      have hGtop_pos : 1 ≤ Gtop := Nat.one_le_two_pow
      have hGg_pos : 1 ≤ Gg := by
        rw [hGg]
        calc 1 = 2 ^ (B * g * 0) := by simp
          _ ≤ _ := Finset.single_le_sum (f := fun k => 2 ^ (B * g * k))
              (by intro i _; positivity) (Finset.mem_range.mpr hG1)
      have hgeo' : 2 ^ (B * g) * Gg + 1 = Gg + Gtop := by omega
      have hoff_geo : OFFn * (2 ^ (B * g) * Gg) + OFFn = OFFn * Gg + OFFn * Gtop := by
        have hc := congrArg (OFFn * ·) hgeo'
        simp only [Nat.mul_add, Nat.mul_one] at hc
        omega
      have hsum' : SP + SCin' + OFFn * (2 ^ (B * g) * Gg) = SS + SC + OFFn * Gg := by
        rw [← Nat.mul_assoc]; exact hsum
      omega
    completeness := by
      obtain ⟨B, W, hB, hW, hB1, hWB, hWp, hp⟩ := P
      obtain ⟨hg1, hpBg, hGWp⟩ := hgp
      circuit_proof_start
      replace hWB : carryOffsetG (m := m) B * 2 < 2 ^ W := by
        have hb : (2 : ℕ) ≤ 2 ^ B := by
          calc (2 : ℕ) = 2 ^ 1 := rfl
            _ ≤ 2 ^ B := Nat.pow_le_pow_right (by norm_num) hB1
        have hle : carryOffsetG (m := m) B ≤ carryOffset (m := m) B := by
          unfold carryOffsetG carryOffset
          have h2 : 2 ^ B + 2 ≤ 2 ^ (B + 1) := by rw [pow_succ]; omega
          exact Nat.mul_le_mul_left _ h2
        omega
      simp only [circuit_norm, RangeCheck.circuit] at h_env ⊢
      have hM : 0 < 2 * m - 1 := by have := Nat.pos_of_neZero m; omega
      have hG1 : 0 < numGroups m g := numGroups_pos m g hg1
      have hCov : 2 * m - 1 ≤ g * numGroups m g := numGroups_mul_ge m g hg1
      set G := numGroups m g with hGdef
      set OFFn := carryOffsetG (m := m) B with hOFFn
      have hOFF_eq : OFFn = (m + 1) * (2 ^ B + 2) := rfl
      -- coefficient digit functions
      set Pn : ℕ → ℕ := fun k => if h : k < 2 * m - 1 then (input.lhs[k]'h).val else 0 with hPn
      set Sn : ℕ → ℕ := fun k => if h : k < 2 * m - 1 then (input.rhs[k]'h).val else 0 with hSn
      have hPn_lt : ∀ k, Pn k < (m + 1) * 2 ^ (2 * B) := by
        intro k; simp only [hPn]; split
        · rename_i h; exact h_assumptions.1 ⟨k, h⟩
        · positivity
      have hSn_lt : ∀ k, Sn k < (m + 1) * 2 ^ (2 * B) := by
        intro k; simp only [hSn]; split
        · rename_i h; exact h_assumptions.2 ⟨k, h⟩
        · positivity
      -- group digits
      set QP : ℕ → ℕ := fun j => ∑ i ∈ Finset.range g, Pn (g * j + i) * 2 ^ (B * i) with hQP
      set QS : ℕ → ℕ := fun j => ∑ i ∈ Finset.range g, Sn (g * j + i) * 2 ^ (B * i) with hQS
      have hQP_app : ∀ j, QP j = ∑ i ∈ Finset.range g, Pn (g * j + i) * 2 ^ (B * i) :=
        fun _ => rfl
      have hQS_app : ∀ j, QS j = ∑ i ∈ Finset.range g, Sn (g * j + i) * 2 ^ (B * i) :=
        fun _ => rfl
      -- group-level partial sums and carries
      set PFn : ℕ → ℕ := fun k => ∑ j ∈ Finset.range (k + 1), QP j * 2 ^ (B * g * j) with hPFn
      set PSn : ℕ → ℕ := fun k => ∑ j ∈ Finset.range (k + 1), QS j * 2 ^ (B * g * j) with hPSn
      set Dk : ℕ → ℕ := fun k => 2 ^ (B * g * (k + 1)) with hDk
      set Cn : ℕ → ℕ := fun k => OFFn + PFn k / Dk k - PSn k / Dk k with hCn
      have hDk_app : ∀ k, Dk k = 2 ^ (B * g * (k + 1)) := fun _ => rfl
      have hPFn_app : ∀ k, PFn k = ∑ j ∈ Finset.range (k + 1), QP j * 2 ^ (B * g * j) :=
        fun _ => rfl
      have hPSn_app : ∀ k, PSn k = ∑ j ∈ Finset.range (k + 1), QS j * 2 ^ (B * g * j) :=
        fun _ => rfl
      have hCn_app : ∀ k, Cn k = OFFn + PFn k / Dk k - PSn k / Dk k := fun _ => rfl
      -- bridge: evalPartial through a group boundary equals the group-level partial sum
      have ha_e : ∀ (j : ℕ) (hj : j < 2 * m - 1),
          Expression.eval env.toEnvironment (input_var.lhs[j]'hj) = input.lhs[j]'hj := by
        intro j hj
        rw [← h_input]
        simp [Vector.getElem_map]
      have hb_e : ∀ (j : ℕ) (hj : j < 2 * m - 1),
          Expression.eval env.toEnvironment (input_var.rhs[j]'hj) = input.rhs[j]'hj := by
        intro j hj
        rw [← h_input]
        simp [Vector.getElem_map]
      have hgk_pos : ∀ k : ℕ, 1 ≤ g * (k + 1) := by
        intro k
        have := Nat.mul_le_mul hg1 (Nat.succ_le_succ (Nat.zero_le k))
        simpa using this
      have hPFn_eq : ∀ k, evalPartial B env input_var.lhs (g * (k + 1) - 1) = PFn k := by
        intro k
        rw [evalPartial, hPFn_app, group_flatten B g Pn (k + 1),
          show g * (k + 1) - 1 + 1 = g * (k + 1) from by have := hgk_pos k; omega]
        apply Finset.sum_congr rfl
        intro j _
        congr 1
        simp only [hPn]
        split
        · rename_i h; rw [ha_e j h]
        · rfl
      have hPSn_eq : ∀ k, evalPartial B env input_var.rhs (g * (k + 1) - 1) = PSn k := by
        intro k
        rw [evalPartial, hPSn_app, group_flatten B g Sn (k + 1),
          show g * (k + 1) - 1 + 1 = g * (k + 1) from by have := hgk_pos k; omega]
        apply Finset.sum_congr rfl
        intro j _
        congr 1
        simp only [hSn]
        split
        · rename_i h; rw [hb_e j h]
        · rfl
        -- carry magnitude bound via the coefficient-level partial_div_bound
      have hPFdiv : ∀ k, PFn k / Dk k ≤ OFFn := by
        intro k
        rw [hOFF_eq, hPFn_app, hDk_app, group_flatten B g Pn (k + 1)]
        have h1 := partial_div_boundG B m hB1 Pn hPn_lt (g * (k + 1) - 1)
        rw [show g * (k + 1) - 1 + 1 = g * (k + 1) from by have := hgk_pos k; omega] at h1
        rw [show B * g * (k + 1) = B * (g * (k + 1)) from by ring]
        exact h1
      have hPSdiv : ∀ k, PSn k / Dk k ≤ OFFn := by
        intro k
        rw [hOFF_eq, hPSn_app, hDk_app, group_flatten B g Sn (k + 1)]
        have h1 := partial_div_boundG B m hB1 Sn hSn_lt (g * (k + 1) - 1)
        rw [show g * (k + 1) - 1 + 1 = g * (k + 1) from by have := hgk_pos k; omega] at h1
        rw [show B * g * (k + 1) = B * (g * (k + 1)) from by ring]
        exact h1
      have hrange : ∀ k, Cn k < 2 ^ W := by
        intro k
        have h1 := hPFdiv k
        rw [hCn_app]
        calc OFFn + PFn k / Dk k - PSn k / Dk k ≤ OFFn + PFn k / Dk k := Nat.sub_le _ _
          _ ≤ OFFn + OFFn := by omega
          _ < 2 ^ W := by have := hWB; omega
      have hBg_pos : (1 : ℕ) ≤ 2 ^ (B * g) := Nat.one_le_two_pow
      have hOFFn_lt : OFFn < p := by
        have h1 : OFFn ≤ OFFn * 2 ^ (B * g) := Nat.le_mul_of_pos_right _ (by omega)
        rw [hOFF_eq] at h1 ⊢
        omega
      have hOFFn_cast : (OFFn : F p).val = OFFn := ZMod.val_natCast_of_lt hOFFn_lt
      -- top values agree
      have hPFn_top : PFn (G - 1) = polyValue B input.lhs := by
        rw [hPFn_app, show G - 1 + 1 = G from by omega]
        have h1 : polyValue B input.lhs = ∑ k ∈ Finset.range (2 * m - 1), Pn k * 2 ^ (B * k) := by
          rw [polyValue, ← Fin.sum_univ_eq_sum_range (fun k => Pn k * 2 ^ (B * k))]
          apply Finset.sum_congr rfl
          intro i _; simp only [hPn, dif_pos i.isLt]
        rw [h1, sum_extend_zero B (2 * m - 1) (g * G) Pn hCov
          (fun t ht => by simp only [hPn, dif_neg (by omega : ¬ t < 2 * m - 1)]),
          ← group_flatten B g Pn G]
      have hPSn_top : PSn (G - 1) = polyValue B input.rhs := by
        rw [hPSn_app, show G - 1 + 1 = G from by omega]
        have h1 : polyValue B input.rhs = ∑ k ∈ Finset.range (2 * m - 1), Sn k * 2 ^ (B * k) := by
          rw [polyValue, ← Fin.sum_univ_eq_sum_range (fun k => Sn k * 2 ^ (B * k))]
          apply Finset.sum_congr rfl
          intro i _; simp only [hSn, dif_pos i.isLt]
        rw [h1, sum_extend_zero B (2 * m - 1) (g * G) Sn hCov
          (fun t ht => by simp only [hSn, dif_neg (by omega : ¬ t < 2 * m - 1)]),
          ← group_flatten B g Sn G]
      have hPtop_eq : PFn (G - 1) = PSn (G - 1) := by
        rw [hPFn_top, hPSn_top]; exact h_spec
      have hmod : ∀ k, k < G → PFn k % Dk k = PSn k % Dk k := by
        intro k hk
        have e1 : PFn (G - 1) % Dk k = PFn k % Dk k := by
          rw [hPFn_app, hPFn_app, hDk_app, show G - 1 + 1 = G from by omega]
          exact partial_mod_stable (B * g) QP G k hk
        have e2 : PSn (G - 1) % Dk k = PSn k % Dk k := by
          rw [hPSn_app, hPSn_app, hDk_app, show G - 1 + 1 = G from by omega]
          exact partial_mod_stable (B * g) QS G k hk
        rw [← e1, ← e2, hPtop_eq]
      have hCtop : Cn (G - 1) = OFFn := by
        rw [hCn_app, hPtop_eq]; omega
      have hidx : ∀ k, k < G →
          QP k + (if k = 0 then OFFn else Cn (k - 1)) + OFFn * 2 ^ (B * g)
            = QS k + Cn k * 2 ^ (B * g) + OFFn := by
        intro k hk
        set qP := PFn k / 2 ^ (B * g * k) with hqP_def
        set qS := PSn k / 2 ^ (B * g * k) with hqS_def
        set rP := PFn k / Dk k with hrP_def
        set rS := PSn k / Dk k with hrS_def
        have hrP_quot : rP = qP / 2 ^ (B * g) := by
          rw [hrP_def, hqP_def, hDk_app, show B * g * (k + 1) = B * g * k + B * g from by ring,
            pow_add, Nat.div_div_eq_div_mul]
        have hrS_quot : rS = qS / 2 ^ (B * g) := by
          rw [hrS_def, hqS_def, hDk_app, show B * g * (k + 1) = B * g * k + B * g from by ring,
            pow_add, Nat.div_div_eq_div_mul]
        have hsplitP : qP = rP * 2 ^ (B * g) + qP % 2 ^ (B * g) := by
          rw [hrP_quot]; exact (Nat.div_add_mod' qP (2 ^ (B * g))).symm
        have hsplitS : qS = rS * 2 ^ (B * g) + qS % 2 ^ (B * g) := by
          rw [hrS_quot]; exact (Nat.div_add_mod' qS (2 ^ (B * g))).symm
        have hdig : qP % 2 ^ (B * g) = qS % 2 ^ (B * g) := by
          have hP : qP % 2 ^ (B * g) = PFn k % Dk k / 2 ^ (B * g * k) := by
            rw [hqP_def, hDk_app, show B * g * (k + 1) = B * g * k + B * g from by ring,
              pow_add, Nat.mod_mul_right_div_self]
          have hS : qS % 2 ^ (B * g) = PSn k % Dk k / 2 ^ (B * g * k) := by
            rw [hqS_def, hDk_app, show B * g * (k + 1) = B * g * k + B * g from by ring,
              pow_add, Nat.mod_mul_right_div_self]
          rw [hP, hS, hmod k hk]
        have hstepP : qP = QP k + (if k = 0 then 0
            else (∑ j ∈ Finset.range k, QP j * 2 ^ (B * g * j)) / 2 ^ (B * g * k)) := by
          rw [hqP_def, hPFn_app]; exact quot_step (B * g) QP k
        have hstepS : qS = QS k + (if k = 0 then 0
            else (∑ j ∈ Finset.range k, QS j * 2 ^ (B * g * j)) / 2 ^ (B * g * k)) := by
          rw [hqS_def, hPSn_app]; exact quot_step (B * g) QS k
        have hCnk : Cn k = OFFn + rP - rS := by rw [hCn_app, ← hrP_def, ← hrS_def]
        have hrS_le : rS ≤ OFFn := by rw [hrS_def]; exact hPSdiv k
        rw [hdig] at hsplitP
        clear_value qP qS rP rS
        have hmulCnk : Cn k * 2 ^ (B * g) = OFFn * 2 ^ (B * g) + rP * 2 ^ (B * g)
            - rS * 2 ^ (B * g) := by
          rw [hCnk, Nat.sub_mul, Nat.add_mul]
        rcases Nat.eq_zero_or_pos k with hk0 | hk0
        · subst hk0
          rw [hmulCnk]
          simp only [↓reduceIte] at hstepP hstepS ⊢
          rw [Nat.add_zero] at hstepP hstepS
          have hrPmul : rS * 2 ^ (B * g) ≤ rP * 2 ^ (B * g) + OFFn * 2 ^ (B * g) := by
            have hle : rS ≤ rP + OFFn := by omega
            calc rS * 2 ^ (B * g) ≤ (rP + OFFn) * 2 ^ (B * g) := Nat.mul_le_mul_right _ hle
              _ = rP * 2 ^ (B * g) + OFFn * 2 ^ (B * g) := by rw [Nat.add_mul]
          omega
        · rw [if_neg (by omega : ¬ k = 0), hmulCnk]
          have hPFnprev : (∑ j ∈ Finset.range k, QP j * 2 ^ (B * g * j)) = PFn (k - 1) := by
            rw [hPFn_app, show k - 1 + 1 = k from by omega]
          have hPSnprev : (∑ j ∈ Finset.range k, QS j * 2 ^ (B * g * j)) = PSn (k - 1) := by
            rw [hPSn_app, show k - 1 + 1 = k from by omega]
          rw [if_neg (by omega : ¬ k = 0), hPFnprev] at hstepP
          rw [if_neg (by omega : ¬ k = 0), hPSnprev] at hstepS
          set rP' := PFn (k - 1) / Dk (k - 1) with hrP'_def
          set rS' := PSn (k - 1) / Dk (k - 1) with hrS'_def
          have hprevP : PFn (k - 1) / 2 ^ (B * g * k) = rP' := by
            rw [hrP'_def, hDk_app, show k - 1 + 1 = k from by omega]
          have hprevS : PSn (k - 1) / 2 ^ (B * g * k) = rS' := by
            rw [hrS'_def, hDk_app, show k - 1 + 1 = k from by omega]
          rw [hprevP] at hstepP
          rw [hprevS] at hstepS
          have hCnprev : Cn (k - 1) = OFFn + rP' - rS' := hCn_app (k - 1)
          have hrSprev_le : rS' ≤ OFFn := hPSdiv (k - 1)
          rw [hCnprev]
          clear_value rP' rS'
          have hrPmul : rS * 2 ^ (B * g) ≤ rP * 2 ^ (B * g) + OFFn * 2 ^ (B * g) := by
            have hle : rS ≤ rP + OFFn := by omega
            calc rS * 2 ^ (B * g) ≤ (rP + OFFn) * 2 ^ (B * g) := Nat.mul_le_mul_right _ hle
              _ = rP * 2 ^ (B * g) + OFFn * 2 ^ (B * g) := by rw [Nat.add_mul]
          omega
        -- group value bounds for the field casts
      set X2 : ℕ := (m + 1) * 2 ^ (2 * B) * 2 ^ (B * (g - 1)) * 2 with hX2
      have hgeo := geom_sum_le B hB1 g hg1
      have hQP_lt : ∀ j, QP j < X2 := by
        intro j
        have hle : QP j ≤ ((m + 1) * 2 ^ (2 * B) - 1) * ∑ i ∈ Finset.range g, 2 ^ (B * i) := by
          rw [hQP_app, Finset.mul_sum]
          apply Finset.sum_le_sum
          intro i _
          have := hPn_lt (g * j + i)
          exact Nat.mul_le_mul_right _ (by omega)
        calc QP j ≤ ((m + 1) * 2 ^ (2 * B) - 1) * ∑ i ∈ Finset.range g, 2 ^ (B * i) := hle
          _ ≤ ((m + 1) * 2 ^ (2 * B) - 1) * (2 ^ (B * (g - 1)) * 2) :=
              Nat.mul_le_mul_left _ hgeo
          _ < (m + 1) * 2 ^ (2 * B) * (2 ^ (B * (g - 1)) * 2) := by
              refine (Nat.mul_lt_mul_right (by positivity)).mpr ?_
              have hb0 : 0 < (m + 1) * 2 ^ (2 * B) := by positivity
              omega
          _ = X2 := by rw [hX2]; ring
      have hQS_lt : ∀ j, QS j < X2 := by
        intro j
        have hle : QS j ≤ ((m + 1) * 2 ^ (2 * B) - 1) * ∑ i ∈ Finset.range g, 2 ^ (B * i) := by
          rw [hQS_app, Finset.mul_sum]
          apply Finset.sum_le_sum
          intro i _
          have := hSn_lt (g * j + i)
          exact Nat.mul_le_mul_right _ (by omega)
        calc QS j ≤ ((m + 1) * 2 ^ (2 * B) - 1) * ∑ i ∈ Finset.range g, 2 ^ (B * i) := hle
          _ ≤ ((m + 1) * 2 ^ (2 * B) - 1) * (2 ^ (B * (g - 1)) * 2) :=
              Nat.mul_le_mul_left _ hgeo
          _ < (m + 1) * 2 ^ (2 * B) * (2 ^ (B * (g - 1)) * 2) := by
              refine (Nat.mul_lt_mul_right (by positivity)).mpr ?_
              have hb0 : 0 < (m + 1) * 2 ^ (2 * B) := by positivity
              omega
          _ = X2 := by rw [hX2]; ring
      have hX2_lt_p : X2 < p := by rw [hX2]; omega
      -- eval bridges for the goal
      have hGP_e : ∀ j : ℕ, Expression.eval env.toEnvironment (groupExpr B g input_var.lhs j)
          = ((QP j : ℕ) : F p) := by
        intro j
        rw [groupExpr_eval, hQP_app, Nat.cast_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [Nat.cast_mul]
        congr 1
        · by_cases h : g * j + i < 2 * m - 1
          · rw [dif_pos h, ha_e _ h]
            simp only [hPn, dif_pos h]
            rw [ZMod.natCast_zmod_val]
          · rw [dif_neg h]
            simp only [hPn, dif_neg h]
            simp
        · push_cast
          rw [pow_mul]
      have hGS_e : ∀ j : ℕ, Expression.eval env.toEnvironment (groupExpr B g input_var.rhs j)
          = ((QS j : ℕ) : F p) := by
        intro j
        rw [groupExpr_eval, hQS_app, Nat.cast_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [Nat.cast_mul]
        congr 1
        · by_cases h : g * j + i < 2 * m - 1
          · rw [dif_pos h, hb_e _ h]
            simp only [hSn, dif_pos h]
            rw [ZMod.natCast_zmod_val]
          · rw [dif_neg h]
            simp only [hSn, dif_neg h]
            simp
        · push_cast
          rw [pow_mul]
      have hbase_ne : ((2 : F p) ^ (B * g) ≠ 0) := by
        have hnat : (((2 ^ (B * g) : ℕ) : F p) ≠ 0) := by
          intro hzero
          have hval : (((2 ^ (B * g) : ℕ) : F p).val) = 2 ^ (B * g) :=
            ZMod.val_natCast_of_lt hpBg
          rw [hzero, ZMod.val_zero] at hval
          have hpos : 0 < 2 ^ (B * g) := Nat.two_pow_pos _
          omega
        simpa [Nat.cast_pow] using hnat
      have hpow_cast : ((2 ^ (B * g) : ℕ) : F p) = (2 ^ (B * g) : F p) := by
        push_cast
        ring
      have hcarry_eval : ∀ k, k < G - 1 →
          Expression.eval env.toEnvironment (carryExpr B g OFFn input_var.lhs input_var.rhs k)
            = ((Cn k : ℕ) : F p) := by
        intro k hk
        induction k with
        | zero =>
            have hnatk := hidx 0 (by omega)
            have hcast := congrArg (Nat.cast : ℕ → F p) hnatk
            push_cast [hpow_cast] at hcast
            simp [carryExpr, Expression.eval, hGP_e, hGS_e]
            field_simp [hbase_ne]
            linear_combination hcast
        | succ j ih =>
            have hprev := ih (by omega)
            have hnatk := hidx (j + 1) (by omega)
            have hcast := congrArg (Nat.cast : ℕ → F p) hnatk
            push_cast [hpow_cast] at hcast
            simp [carryExpr, Expression.eval, hGP_e, hGS_e, hprev]
            field_simp [hbase_ne]
            linear_combination hcast
      refine ⟨?_, ?_⟩
      · -- range checks
        intro i
        exact ⟨trivial, by
          change (Expression.eval env.toEnvironment
            (carryExpr B g OFFn input_var.lhs input_var.rhs i.val)).val < 2 ^ W
          rw [hcarry_eval i.val i.isLt,
            ZMod.val_natCast_of_lt (lt_trans (hrange i.val) hW)]
          exact hrange i.val⟩
      · -- final group field equation
        have hnatk := hidx (G - 1) (by omega)
        have hcast := congrArg (Nat.cast : ℕ → F p) hnatk
        push_cast [hpow_cast] at hcast
        rw [hCtop] at hcast
        rw [hGP_e, hGS_e]
        by_cases hlast0 : G - 1 = 0
        · simp [carryInExpr, hlast0, Expression.eval] at hcast ⊢
          linear_combination hcast
        · have hprev := hcarry_eval (G - 1 - 1) (by omega)
          have hcin_eval : Expression.eval env.toEnvironment
              (carryInExpr B g OFFn input_var.lhs input_var.rhs (G - 1))
                = ((Cn (G - 1 - 1) : ℕ) : F p) - (OFFn : F p) := by
            simp [carryInExpr, hlast0, Expression.eval, hprev, sub_eq_add_neg]
          rw [hcin_eval]
          simp only [if_neg hlast0] at hcast
          linear_combination hcast

end GroupedEq

end

end Solution.Secp256k1ScalarMul
