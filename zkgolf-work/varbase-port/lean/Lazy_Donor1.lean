import Solution.Secp256k1ScalarMul.Lazy_Donor0


-- Adapted donor module: GroupedFlex
section DonorFile1_0

namespace Solution.Secp256k1ScalarMulFixedBase

section
variable {p : ℕ} [Fact p.Prime]
variable {L : ℕ} [NeZero L]

namespace GroupedFlex

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

lemma sum_extend_zero (B N M : ℕ) (f : ℕ → ℕ) (hNM : N ≤ M)
    (hf : ∀ t, N ≤ t → f t = 0) :
    (∑ t ∈ Finset.range N, f t * 2 ^ (B * t)) = ∑ t ∈ Finset.range M, f t * 2 ^ (B * t) := by
  apply Finset.sum_subset
    (fun x hx => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hNM))
  intro x _ hx
  simp only [Finset.mem_range, not_lt] at hx
  rw [hf x hx, Nat.zero_mul]

structure VParams where
  Nf : ℕ → ℕ
  OFFf : ℕ → ℕ
  Wf : ℕ → ℕ

def groupExprW (B L : ℕ) (gf posOf : ℕ → ℕ) (x : Var (EqViaCarriesFlex.Coeffs L) (F p)) (k : ℕ) :
    Expression (F p) :=
  polyEvalExpr
    (Vector.ofFn fun i : Fin (gf k) =>
      if h : posOf k + i.val < L then x[posOf k + i.val]'h else 0)
    ((2 : F p) ^ B)

lemma groupExprW_eval (env : Environment (F p)) (B L : ℕ) (gf posOf : ℕ → ℕ)
    (x : Var (EqViaCarriesFlex.Coeffs L) (F p)) (k : ℕ) :
    Expression.eval env (groupExprW B L gf posOf x k)
      = ∑ i ∈ Finset.range (gf k),
          (if h : posOf k + i < L then Expression.eval env (x[posOf k + i]'h) else 0)
            * ((2 : F p) ^ B) ^ i := by
  rw [groupExprW, polyEvalExpr_eval,
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

lemma group_flatten_sched (B : ℕ) (gf posOf : ℕ → ℕ) (f : ℕ → ℕ)
    (hpos0 : posOf 0 = 0) (hposS : ∀ k, posOf (k + 1) = posOf k + gf k) :
    ∀ G : ℕ, (∑ j ∈ Finset.range G,
        (∑ i ∈ Finset.range (gf j), f (posOf j + i) * 2 ^ (B * i)) * 2 ^ (B * posOf j))
      = ∑ t ∈ Finset.range (posOf G), f t * 2 ^ (B * t) := by
  intro G
  induction G with
  | zero => rw [hpos0]; simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, hposS n, Finset.sum_range_add]
    congr 1
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [show B * (posOf n + i) = B * i + B * posOf n from by ring, pow_add]
    ring

lemma partial_mod_stable_e (e : ℕ → ℕ) (hmono : ∀ k, e k ≤ e (k + 1)) (h : ℕ → ℕ) :
    ∀ N k, k < N →
      (∑ j ∈ Finset.range N, h j * 2 ^ (e j)) % 2 ^ (e (k + 1))
        = (∑ j ∈ Finset.range (k + 1), h j * 2 ^ (e j)) % 2 ^ (e (k + 1)) := by
  have hle : ∀ a b, a ≤ b → e a ≤ e b :=
    fun a b hab => monotone_nat_of_le_succ hmono hab
  intro N
  induction N with
  | zero => intro k hk; omega
  | succ n ih =>
    intro k hk
    rw [Finset.sum_range_succ]
    rcases Nat.lt_or_ge k n with hlt | hge
    · have hfac : (2 : ℕ) ^ (e n) = 2 ^ (e (k + 1)) * 2 ^ (e n - e (k + 1)) := by
        rw [← pow_add]; congr 1
        have : e (k + 1) ≤ e n := hle (k + 1) n (by omega)
        omega
      rw [hfac, show h n * (2 ^ (e (k + 1)) * 2 ^ (e n - e (k + 1)))
          = (h n * 2 ^ (e n - e (k + 1))) * 2 ^ (e (k + 1)) by ring,
        Nat.add_mul_mod_self_right]
      exact ih k hlt
    · have : k = n := by omega
      subst this; rw [Finset.sum_range_succ]

lemma quot_step_e (e : ℕ → ℕ) (f : ℕ → ℕ) (k : ℕ) :
    (∑ j ∈ Finset.range (k + 1), f j * 2 ^ (e j)) / 2 ^ (e k)
      = f k + (if k = 0 then 0
          else (∑ j ∈ Finset.range k, f j * 2 ^ (e j)) / 2 ^ (e k)) := by
  rw [Finset.sum_range_succ, Nat.add_mul_div_right _ _ (Nat.two_pow_pos (e k))]
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · subst hk0; simp
  · rw [if_neg (by omega : ¬ k = 0)]; ring

lemma carry_telescope_e (e : ℕ → ℕ) (C : ℕ → ℕ) :
    ∀ n : ℕ,
      (∑ k ∈ Finset.range n, (if k = 0 then 0 else C (k - 1)) * 2 ^ (e k))
        + (if n = 0 then 0 else C (n - 1) * 2 ^ (e n))
      = ∑ k ∈ Finset.range n, C k * 2 ^ (e (k + 1)) := by
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

def GVXHyps (p L : ℕ) (B : ℕ) (gf posOf : ℕ → ℕ) (G : ℕ)
    (V VR : VParams) : Prop :=
  posOf 0 = 0 ∧
  (∀ k, posOf (k + 1) = posOf k + gf k) ∧
  (∀ k, 1 ≤ gf k) ∧
  (∀ k, 1 ≤ V.Wf k ∧ 2 ^ V.Wf k < p) ∧
  (∀ j, 1 ≤ V.Nf j ∧ 1 ≤ VR.Nf j) ∧
  (∀ k, k < G - 1 →
    VR.OFFf k + V.OFFf k < 2 ^ V.Wf k ∧
    (((if k = 0 then 0 else V.OFFf (k - 1)) + 1
        + (∑ i ∈ Finset.range (gf k), (V.Nf (posOf k + i) - 1) * 2 ^ (B * i))
      ≤ (V.OFFf k + 1) * 2 ^ (B * gf k)) ∧
     ((if k = 0 then 0 else VR.OFFf (k - 1)) + 1
        + (∑ i ∈ Finset.range (gf k), (VR.Nf (posOf k + i) - 1) * 2 ^ (B * i))
      ≤ (VR.OFFf k + 1) * 2 ^ (B * gf k))) ∧
    ((∑ i ∈ Finset.range (gf k), (V.Nf (posOf k + i) - 1) * 2 ^ (B * i))
        + (∑ i ∈ Finset.range (gf k), (VR.Nf (posOf k + i) - 1) * 2 ^ (B * i))
        + 2 ^ V.Wf k * 2 ^ (B * gf k) + VR.OFFf k * 2 ^ (B * gf k)
        + 2 ^ V.Wf (k - 1) < p)) ∧
  3 ≤ G ∧
  posOf (G - 1) < L ∧
  L ≤ posOf G ∧
  2 ^ V.Wf (G - 3)
      + (∑ t ∈ Finset.range (L - posOf (G - 2)),
          V.Nf (posOf (G - 2) + t) * 2 ^ (B * t))
      + (∑ t ∈ Finset.range (L - posOf (G - 2)),
          VR.Nf (posOf (G - 2) + t) * 2 ^ (B * t)) < p

def carryExpr (B : ℕ) (gf posOf OFFf : ℕ → ℕ) (lhs rhs : Var (EqViaCarriesFlex.Coeffs L) (F p)) :
    ℕ → Expression (F p)
  | 0 =>
      (groupExprW B L gf posOf lhs 0 - groupExprW B L gf posOf rhs 0)
          / ((2 : F p) ^ (B * gf 0))
        + ((OFFf 0 : ℕ) : F p)
  | k + 1 =>
      (groupExprW B L gf posOf lhs (k + 1)
          + (carryExpr B gf posOf OFFf lhs rhs k - ((OFFf k : ℕ) : F p))
          - groupExprW B L gf posOf rhs (k + 1)) / ((2 : F p) ^ (B * gf (k + 1)))
        + ((OFFf (k + 1) : ℕ) : F p)

def widthAllocFrom (Wf : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | c + 1, k₀ => (Wf k₀ - 1) + widthAllocFrom Wf c (k₀ + 1)

def widthConsFrom (Wf : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | c + 1, k₀ => Wf k₀ + widthConsFrom Wf c (k₀ + 1)

def carryLoop (B : ℕ) (gf posOf OFFf Wf : ℕ → ℕ) (hWok : ∀ k, 1 ≤ Wf k ∧ 2 ^ Wf k < p)
    [Fact (p > 2)]
    (lhs rhs : Var (EqViaCarriesFlex.Coeffs L) (F p)) :
    ℕ → ℕ → Circuit (F p) Unit
  | 0, _ => pure ()
  | c + 1, k₀ => do
      assertion (RangeCheck.circuit (Wf k₀) (hWok k₀).2 (hWok k₀).1)
        (carryExpr B gf posOf OFFf lhs rhs k₀)
      carryLoop B gf posOf OFFf Wf hWok lhs rhs c (k₀ + 1)

def main (B : ℕ) (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : VParams)
    (hgv : GVXHyps p L B gf posOf G V VR) [Fact (p > 2)]
    (input : Var (EqViaCarriesFlex.Inputs L) (F p)) :
    Circuit (F p) Unit := do
  let Pc := input.lhs
  let Sc := input.rhs
  carryLoop B gf posOf VR.OFFf V.Wf hgv.2.2.2.1 Pc Sc (G - 2) 0
  assertZero
    (polyEvalExpr
      (Vector.ofFn fun j : Fin L => Pc[j.val]'j.isLt - Sc[j.val]'j.isLt)
      ((2 : F p) ^ B))

lemma carryLoop_localLength (B : ℕ) (gf posOf OFFf Wf : ℕ → ℕ)
    (hWok : ∀ k, 1 ≤ Wf k ∧ 2 ^ Wf k < p) [Fact (p > 2)]
    (lhs rhs : Var (EqViaCarriesFlex.Coeffs L) (F p)) :
    ∀ (c k₀ offset : ℕ),
      (carryLoop B gf posOf OFFf Wf hWok lhs rhs c k₀).localLength offset
        = widthAllocFrom Wf c k₀ := by
  intro c
  induction c with
  | zero => intro k₀ offset; simp [carryLoop, widthAllocFrom, circuit_norm]
  | succ n ih =>
    intro k₀ offset
    simp only [carryLoop, widthAllocFrom, circuit_norm, RangeCheck.circuit,
      RangeCheck.elaborated, ih]

lemma carryLoop_subcircuitsConsistent (B : ℕ) (gf posOf OFFf Wf : ℕ → ℕ)
    (hWok : ∀ k, 1 ≤ Wf k ∧ 2 ^ Wf k < p) [Fact (p > 2)]
    (lhs rhs : Var (EqViaCarriesFlex.Coeffs L) (F p)) :
    ∀ (c k₀ offset : ℕ),
      ((carryLoop B gf posOf OFFf Wf hWok lhs rhs c k₀).operations offset).SubcircuitsConsistent offset := by
  intro c
  induction c with
  | zero => intro k₀ offset; simp [carryLoop, circuit_norm]
  | succ n ih =>
    intro k₀ offset
    have key : ∀ k off, Operations.forAll off { subcircuit := fun off {n} _ => n = off }
        ((carryLoop B gf posOf OFFf Wf hWok lhs rhs n k).operations off) :=
      fun k off => ih k off
    simp only [carryLoop, circuit_norm, RangeCheck.circuit, RangeCheck.elaborated]
    ring_nf
    apply key

lemma carryLoop_channelsLawful (B : ℕ) (gf posOf OFFf Wf : ℕ → ℕ)
    (hWok : ∀ k, 1 ≤ Wf k ∧ 2 ^ Wf k < p) [Fact (p > 2)]
    (lhs rhs : Var (EqViaCarriesFlex.Coeffs L) (F p)) :
    ∀ (c k₀ offset : ℕ),
      ((carryLoop B gf posOf OFFf Wf hWok lhs rhs c k₀).operations offset).ChannelsLawful [] [] := by
  intro c
  induction c with
  | zero =>
    intro k₀ offset
    simp only [carryLoop, Circuit.pure_operations_eq]
    exact Operations.channelsLawful_nil
  | succ n ih =>
    intro k₀ offset
    show ((do
        assertion (RangeCheck.circuit (Wf k₀) (hWok k₀).2 (hWok k₀).1)
          (carryExpr B gf posOf OFFf lhs rhs k₀)
        carryLoop B gf posOf OFFf Wf hWok lhs rhs n (k₀ + 1)).operations offset).ChannelsLawful [] []
    rw [Circuit.bind_operations_eq]
    have hhead : ((assertion (RangeCheck.circuit (Wf k₀) (hWok k₀).2 (hWok k₀).1)
        (carryExpr B gf posOf OFFf lhs rhs k₀)).operations offset).ChannelsLawful [] [] := by
      simp only [circuit_norm, RangeCheck.circuit, RangeCheck.elaborated]
    exact Operations.channelsLawful_append_of_channelsLawful hhead (ih _ _)

lemma carryLoop_soundness (B : ℕ) (gf posOf OFFf Wf : ℕ → ℕ)
    (hWok : ∀ k, 1 ≤ Wf k ∧ 2 ^ Wf k < p) [Fact (p > 2)]
    (env : Environment (F p))
    (lhs rhs : Var (EqViaCarriesFlex.Coeffs L) (F p)) :
    ∀ (c k₀ offset : ℕ),
      Operations.forAllNoOffset
        { assert := fun e ↦ Expression.eval env e = 0, lookup := fun l ↦ l.Soundness env,
          interact := fun i ↦ i.Guarantees env,
          subcircuit := fun {_m} s ↦ s.Assumptions env → s.Spec env }
        ((carryLoop B gf posOf OFFf Wf hWok lhs rhs c k₀).operations offset) →
      ∀ i, i < c →
        (Expression.eval env (carryExpr B gf posOf OFFf lhs rhs (k₀ + i))).val < 2 ^ Wf (k₀ + i) := by
  intro c
  induction c with
  | zero => intro k₀ offset _ i hi; omega
  | succ n ih =>
    intro k₀ offset h_holds i hi
    rw [show carryLoop B gf posOf OFFf Wf hWok lhs rhs (n + 1) k₀
        = (do
            assertion (RangeCheck.circuit (Wf k₀) (hWok k₀).2 (hWok k₀).1)
              (carryExpr B gf posOf OFFf lhs rhs k₀)
            carryLoop B gf posOf OFFf Wf hWok lhs rhs n (k₀ + 1)) from rfl] at h_holds
    rw [Circuit.bind_operations_eq, Operations.forAllNoOffset_append] at h_holds
    obtain ⟨h_head, h_rest⟩ := h_holds
    rcases Nat.eq_zero_or_pos i with hi0 | hipos
    · subst hi0
      simp only [circuit_norm, RangeCheck.circuit] at h_head
      have := h_head trivial
      simpa [RangeCheck.Spec, Nat.add_zero] using this
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
      have := ih (k₀ + 1) _ h_rest j (by omega)
      rwa [show k₀ + 1 + j = k₀ + (j + 1) from by ring] at this

lemma carryLoop_completeness (B : ℕ) (gf posOf OFFf Wf : ℕ → ℕ)
    (hWok : ∀ k, 1 ≤ Wf k ∧ 2 ^ Wf k < p) [Fact (p > 2)]
    (env : ProverEnvironment (F p))
    (lhs rhs : Var (EqViaCarriesFlex.Coeffs L) (F p)) :
    ∀ (c k₀ offset : ℕ),
      (∀ i, i < c →
        (Expression.eval env.toEnvironment (carryExpr B gf posOf OFFf lhs rhs (k₀ + i))).val
          < 2 ^ Wf (k₀ + i)) →
      Operations.forAllNoOffset
        { assert := fun e ↦ Expression.eval env.toEnvironment e = 0,
          lookup := fun l ↦ l.Completeness env.toEnvironment,
          interact := fun i ↦ i.Guarantees env.toEnvironment,
          subcircuit := fun {_m} s ↦ s.ProverAssumptions env }
        ((carryLoop B gf posOf OFFf Wf hWok lhs rhs c k₀).operations offset) := by
  intro c
  induction c with
  | zero =>
    intro k₀ offset _
    simp only [carryLoop, Circuit.pure_operations_eq, Operations.forAllNoOffset_empty]
  | succ n ih =>
    intro k₀ offset h_small
    rw [show carryLoop B gf posOf OFFf Wf hWok lhs rhs (n + 1) k₀
        = (do
            assertion (RangeCheck.circuit (Wf k₀) (hWok k₀).2 (hWok k₀).1)
              (carryExpr B gf posOf OFFf lhs rhs k₀)
            carryLoop B gf posOf OFFf Wf hWok lhs rhs n (k₀ + 1)) from rfl]
    rw [Circuit.bind_operations_eq, Operations.forAllNoOffset_append]
    constructor
    · simp only [circuit_norm, RangeCheck.circuit]
      exact ⟨trivial, by simpa [RangeCheck.Spec, Nat.add_zero] using h_small 0 (by omega)⟩
    · refine ih (k₀ + 1) _ fun i hi => ?_
      have := h_small (i + 1) (by omega)
      rwa [show k₀ + (i + 1) = k₀ + 1 + i from by ring] at this

lemma carryLoop_requirements (B : ℕ) (gf posOf OFFf Wf : ℕ → ℕ)
    (hWok : ∀ k, 1 ≤ Wf k ∧ 2 ^ Wf k < p) [Fact (p > 2)]
    (env : Environment (F p))
    (lhs rhs : Var (EqViaCarriesFlex.Coeffs L) (F p)) :
    ∀ (c k₀ offset : ℕ),
      Operations.forAllNoOffset
        { interact := fun i ↦ i.Requirements env,
          subcircuit := fun {_m} s ↦ s.channelsWithRequirements = [] ∨ s.Assumptions env }
        ((carryLoop B gf posOf OFFf Wf hWok lhs rhs c k₀).operations offset) := by
  intro c
  induction c with
  | zero =>
    intro k₀ offset
    simp only [carryLoop, Circuit.pure_operations_eq, Operations.forAllNoOffset_empty]
  | succ n ih =>
    intro k₀ offset
    show Operations.forAllNoOffset _ ((do
        assertion (RangeCheck.circuit (Wf k₀) (hWok k₀).2 (hWok k₀).1)
          (carryExpr B gf posOf OFFf lhs rhs k₀)
        carryLoop B gf posOf OFFf Wf hWok lhs rhs n (k₀ + 1)).operations offset)
    rw [Circuit.bind_operations_eq, Operations.forAllNoOffset_append]
    refine ⟨?_, ih _ _⟩
    simp only [circuit_norm, RangeCheck.circuit, RangeCheck.elaborated]

instance elaborated (B : ℕ) (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : VParams)
    (hgv : GVXHyps p L B gf posOf G V VR) [Fact (p > 2)] :
    ElaboratedCircuit (F p) (EqViaCarriesFlex.Inputs L) unit (main B gf posOf G V VR hgv) where
  localLength _ := widthAllocFrom V.Wf (G - 2) 0
  localLength_eq := by
    intro input offset
    simp only [main, circuit_norm,
      carryLoop_localLength B gf posOf VR.OFFf V.Wf hgv.2.2.2.1 input.lhs input.rhs]
  subcircuitsConsistent := by
    intro input offset
    have key : ∀ off, Operations.forAll off { subcircuit := fun off {n} _ => n = off }
        ((carryLoop B gf posOf VR.OFFf V.Wf hgv.2.2.2.1 input.lhs input.rhs
          (G - 2) 0).operations off) :=
      fun off => carryLoop_subcircuitsConsistent B gf posOf VR.OFFf V.Wf hgv.2.2.2.1 _ _ _ _ off
    simp only [main, circuit_norm]
    ring_nf
    apply key
  channelsLawful := by
    intro input offset
    simp only [main, Circuit.bind_operations_eq]
    refine Operations.channelsLawful_append_of_channelsLawful
      (carryLoop_channelsLawful B gf posOf VR.OFFf V.Wf hgv.2.2.2.1 _ _ _ _ _) ?_
    simp only [circuit_norm]

def Assumptions (NfL NfR : ℕ → ℕ) (input : EqViaCarriesFlex.Inputs L (F p)) : Prop :=
  (∀ k : Fin (L), (input.lhs[k.val]).val < NfL k.val) ∧
  (∀ k : Fin (L), (input.rhs[k.val]).val < NfR k.val)

lemma per_index_lift2 {B : ℕ} (a cinF b c offL offR : F p) (cinN offLN offRN : ℕ)
    (hpB : 2 ^ B < p) (hcin : cinF.val = cinN) (hoffL : offL.val = offLN)
    (hoffR : offR.val = offRN)
    (hlhs : a.val + cinN + offLN * 2 ^ B < p)
    (hrhs : b.val + c.val * 2 ^ B + offRN < p)
    (heq : a + cinF + offL * (2 ^ B : F p) = b + c * (2 ^ B : F p) + offR) :
    a.val + cinN + offLN * 2 ^ B = b.val + c.val * 2 ^ B + offRN := by
  have hpow_val_cast : ((2 ^ B : ℕ) : F p) = (2 ^ B : F p) := by push_cast; ring
  have hoffLcast : ((offLN : ℕ) : F p) = offL := by rw [← hoffL, ZMod.natCast_zmod_val]
  have hoffRcast : ((offRN : ℕ) : F p) = offR := by rw [← hoffR, ZMod.natCast_zmod_val]
  have hcincast : ((cinN : ℕ) : F p) = cinF := by rw [← hcin, ZMod.natCast_zmod_val]
  have hacast : ((a.val : ℕ) : F p) = a := ZMod.natCast_zmod_val a
  have hbcast : ((b.val : ℕ) : F p) = b := ZMod.natCast_zmod_val b
  have hccast : ((c.val : ℕ) : F p) = c := ZMod.natCast_zmod_val c
  have hlhs_cast : a + cinF + offL * (2 ^ B : F p)
      = ((a.val + cinN + offLN * 2 ^ B : ℕ) : F p) := by
    push_cast [hacast, hcincast, hoffLcast, hpow_val_cast]; ring
  have hlhs_val : (a + cinF + offL * (2 ^ B : F p)).val = a.val + cinN + offLN * 2 ^ B := by
    rw [hlhs_cast, ZMod.val_natCast_of_lt hlhs]
  have hrhs_cast : b + c * (2 ^ B : F p) + offR
      = ((b.val + c.val * 2 ^ B + offRN : ℕ) : F p) := by
    push_cast [hbcast, hccast, hoffRcast, hpow_val_cast]; ring
  have hrhs_val : (b + c * (2 ^ B : F p) + offR).val = b.val + c.val * 2 ^ B + offRN := by
    rw [hrhs_cast, ZMod.val_natCast_of_lt hrhs]
  have := congrArg ZMod.val heq
  rw [hlhs_val, hrhs_val] at this
  exact this

lemma prefix_div_le_sched (B : ℕ) (gf posOf OFFf Nf : ℕ → ℕ) (G : ℕ)
    (he : ∀ k, B * posOf (k + 1) = B * posOf k + B * gf k)
    (hOFFrec : ∀ k, k < G →
      (if k = 0 then 0 else OFFf (k - 1)) + 1
          + (∑ i ∈ Finset.range (gf k), (Nf (posOf k + i) - 1) * 2 ^ (B * i))
        ≤ (OFFf k + 1) * 2 ^ (B * gf k))
    (f : ℕ → ℕ) (hf : ∀ t, f t < Nf t) :
    ∀ k, k < G →
      (∑ j ∈ Finset.range (k + 1),
          (∑ i ∈ Finset.range (gf j), f (posOf j + i) * 2 ^ (B * i)) * 2 ^ (B * posOf j))
        < (OFFf k + 1) * 2 ^ (B * posOf (k + 1)) := by
  have hQle : ∀ j, (∑ i ∈ Finset.range (gf j), f (posOf j + i) * 2 ^ (B * i))
      ≤ ∑ i ∈ Finset.range (gf j), (Nf (posOf j + i) - 1) * 2 ^ (B * i) := by
    intro j
    apply Finset.sum_le_sum
    intro i _
    have := hf (posOf j + i)
    exact Nat.mul_le_mul_right _ (by omega)
  intro k
  induction k with
  | zero =>
    intro hk
    have h0 := hOFFrec 0 hk
    simp only [reduceIte] at h0
    have hQ := hQle 0
    rw [Finset.sum_range_one, he 0]
    have hpow : (2 : ℕ) ^ (B * posOf 0 + B * gf 0) = 2 ^ (B * posOf 0) * 2 ^ (B * gf 0) := by
      rw [pow_add]
    rw [hpow]
    have hinner : (∑ i ∈ Finset.range (gf 0), (Nf (posOf 0 + i) - 1) * 2 ^ (B * i))
        < (OFFf 0 + 1) * 2 ^ (B * gf 0) := by omega
    calc (∑ i ∈ Finset.range (gf 0), f (posOf 0 + i) * 2 ^ (B * i)) * 2 ^ (B * posOf 0)
        ≤ (∑ i ∈ Finset.range (gf 0), (Nf (posOf 0 + i) - 1) * 2 ^ (B * i)) * 2 ^ (B * posOf 0) :=
          Nat.mul_le_mul_right _ hQ
      _ < (OFFf 0 + 1) * 2 ^ (B * gf 0) * 2 ^ (B * posOf 0) :=
          mul_lt_mul_of_pos_right hinner (Nat.two_pow_pos _)
      _ = (OFFf 0 + 1) * (2 ^ (B * posOf 0) * 2 ^ (B * gf 0)) := by ring
  | succ n ih =>
    intro hk
    have hprev := ih (by omega)
    have hrec := hOFFrec (n + 1) hk
    rw [if_neg (by omega : ¬ n + 1 = 0), Nat.add_sub_cancel] at hrec
    have hQ := hQle (n + 1)
    rw [Finset.sum_range_succ]
    have hstep : (∑ i ∈ Finset.range (gf (n + 1)), f (posOf (n + 1) + i) * 2 ^ (B * i))
          * 2 ^ (B * posOf (n + 1))
        ≤ (∑ i ∈ Finset.range (gf (n + 1)), (Nf (posOf (n + 1) + i) - 1) * 2 ^ (B * i))
            * 2 ^ (B * posOf (n + 1)) :=
      Nat.mul_le_mul_right _ hQ
    have hpow : (2 : ℕ) ^ (B * posOf (n + 1 + 1))
        = 2 ^ (B * posOf (n + 1)) * 2 ^ (B * gf (n + 1)) := by
      rw [he (n + 1), pow_add]
    calc (∑ j ∈ Finset.range (n + 1),
            (∑ i ∈ Finset.range (gf j), f (posOf j + i) * 2 ^ (B * i)) * 2 ^ (B * posOf j))
          + (∑ i ∈ Finset.range (gf (n + 1)), f (posOf (n + 1) + i) * 2 ^ (B * i))
              * 2 ^ (B * posOf (n + 1))
        < (OFFf n + 1) * 2 ^ (B * posOf (n + 1))
          + (∑ i ∈ Finset.range (gf (n + 1)), (Nf (posOf (n + 1) + i) - 1) * 2 ^ (B * i))
              * 2 ^ (B * posOf (n + 1)) := by
          have := hstep; omega
      _ = (OFFf n + 1
            + (∑ i ∈ Finset.range (gf (n + 1)), (Nf (posOf (n + 1) + i) - 1) * 2 ^ (B * i)))
              * 2 ^ (B * posOf (n + 1)) := by ring
      _ ≤ ((OFFf (n + 1) + 1) * 2 ^ (B * gf (n + 1))) * 2 ^ (B * posOf (n + 1)) := by
          apply Nat.mul_le_mul_right; omega
      _ = (OFFf (n + 1) + 1) * 2 ^ (B * posOf (n + 1 + 1)) := by rw [hpow]; ring

lemma polyEvalExpr_diff_eval (B : ℕ) (env : Environment (F p))
    (lhs rhs : Var (EqViaCarriesFlex.Coeffs L) (F p)) :
    Expression.eval env
        (polyEvalExpr
          (Vector.ofFn fun j : Fin L => lhs[j.val]'j.isLt - rhs[j.val]'j.isLt) ((2 : F p) ^ B))
      = (∑ i : Fin L, Expression.eval env (lhs[i.val]'i.isLt) * ((2 : F p) ^ B) ^ i.val)
        - (∑ i : Fin L, Expression.eval env (rhs[i.val]'i.isLt) * ((2 : F p) ^ B) ^ i.val) := by
  rw [polyEvalExpr_eval, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [Vector.getElem_ofFn]
  simp only [Expression.eval]
  ring

lemma polyValue_eval_cast (B : ℕ) (env : Environment (F p)) (x : Var (EqViaCarriesFlex.Coeffs L) (F p))
    (xv : Vector (F p) L)
    (hbridge : ∀ (j : ℕ) (hj : j < L), Expression.eval env (x[j]'hj) = xv[j]'hj) :
    ((polyValue B xv : ℕ) : F p)
      = ∑ i : Fin L, Expression.eval env (x[i.val]'i.isLt) * ((2 : F p) ^ B) ^ i.val := by
  rw [polyValue, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Nat.cast_mul, ZMod.natCast_zmod_val, ← hbridge i.val i.isLt]
  congr 1
  push_cast
  rw [pow_mul]

private lemma sum5_lt {a b c d e q : ℕ} (h : a + b + c + d + e < q) :
    a < q ∧ b < q ∧ c < q ∧ d < q ∧ e < q := by omega

def circuit (B : ℕ) (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : VParams)
    (hgv : GVXHyps p L B gf posOf G V VR) (hB1 : 1 ≤ B)
    [Fact (p > 2)] : FormalAssertion (F p) (EqViaCarriesFlex.Inputs L) where
    main := main B gf posOf G V VR hgv
    Assumptions := Assumptions V.Nf VR.Nf
    Spec := EqViaCarriesFlex.Spec B
    soundness := by
      obtain ⟨hpos0, hposS, hgf1, hWok, hNf1, hper, hG3, hlast, hCov, htrunc⟩ := hgv
      circuit_proof_start
      obtain ⟨h_loop, h_lin⟩ := h_holds
      have hM : 0 < L := Nat.pos_of_neZero L
      have hG1 : 0 < G := by omega
      have hposMono : ∀ a b, a ≤ b → posOf a ≤ posOf b :=
        fun a b hab => monotone_nat_of_le_succ (fun k => by rw [hposS k]; omega) hab
      have he : ∀ k, B * posOf (k + 1) = B * posOf k + B * gf k :=
        fun k => by rw [hposS k, Nat.mul_add]
      have hemono : ∀ k, B * posOf k ≤ B * posOf (k + 1) := fun k => by rw [he k]; omega
      have h_range := carryLoop_soundness B gf posOf VR.OFFf V.Wf hWok env
        input_var.lhs input_var.rhs (G - 2) 0 i₀ h_loop

      set Pn : ℕ → ℕ := fun k => if h : k < L then (input.lhs[k]'h).val else 0 with hPn
      set Sn : ℕ → ℕ := fun k => if h : k < L then (input.rhs[k]'h).val else 0 with hSn

      set QP : ℕ → ℕ := fun j => ∑ i ∈ Finset.range (gf j), Pn (posOf j + i) * 2 ^ (B * i) with hQP
      set QS : ℕ → ℕ := fun j => ∑ i ∈ Finset.range (gf j), Sn (posOf j + i) * 2 ^ (B * i) with hQS
      have hQP_app : ∀ j, QP j = ∑ i ∈ Finset.range (gf j), Pn (posOf j + i) * 2 ^ (B * i) :=
        fun _ => rfl
      have hQS_app : ∀ j, QS j = ∑ i ∈ Finset.range (gf j), Sn (posOf j + i) * 2 ^ (B * i) :=
        fun _ => rfl

      set OFFe : ℕ → ℕ := fun k => if k = G - 1 then 0 else VR.OFFf k with hOFFe
      set Cn : ℕ → ℕ := fun k => if k = G - 1 then 0
        else (Expression.eval env (carryExpr B gf posOf VR.OFFf input_var.lhs input_var.rhs k)).val
        with hCn
      have hCn_lt : ∀ k, k < G - 2 → Cn k < 2 ^ V.Wf k := by
        intro k hk
        simp only [hCn, if_neg (by omega : ¬ k = G - 1)]
        simpa using h_range k hk
      have hPn_lt : ∀ k, Pn k < V.Nf k := by
        intro k; simp only [hPn]; split
        · rename_i h; exact h_assumptions.1 ⟨k, h⟩
        · exact (hNf1 k).1
      have hSn_lt : ∀ k, Sn k < VR.Nf k := by
        intro k; simp only [hSn]; split
        · rename_i h; exact h_assumptions.2 ⟨k, h⟩
        · exact (hNf1 k).2
      have hSfP : ∀ k, QP k ≤ ∑ i ∈ Finset.range (gf k), (V.Nf (posOf k + i) - 1) * 2 ^ (B * i) := by
        intro k
        rw [hQP_app]
        exact Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_right _ (by have := hPn_lt (posOf k + i); omega))
      have hSfS : ∀ k, QS k ≤ ∑ i ∈ Finset.range (gf k), (VR.Nf (posOf k + i) - 1) * 2 ^ (B * i) := by
        intro k
        rw [hQS_app]
        exact Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_right _ (by have := hSn_lt (posOf k + i); omega))
      have hpBg : ∀ k, k < G - 1 → 2 ^ (B * gf k) < p := fun k hk =>
        lt_of_le_of_lt (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _))
          (sum5_lt (hper k hk).2.2).2.2.1
      have hbase_ne : ∀ k, k < G - 1 → ((2 : F p) ^ (B * gf k) ≠ 0) := by
        intro k hk
        have hnat : (((2 ^ (B * gf k) : ℕ) : F p) ≠ 0) := by
          intro hzero
          have hval : (((2 ^ (B * gf k) : ℕ) : F p).val) = 2 ^ (B * gf k) :=
            ZMod.val_natCast_of_lt (hpBg k hk)
          rw [hzero, ZMod.val_zero] at hval
          have : 0 < 2 ^ (B * gf k) := Nat.two_pow_pos _
          omega
        simpa [Nat.cast_pow] using hnat
      have hOFFe_cast : ∀ k, k < G - 1 → ((OFFe k : ℕ) : F p).val = OFFe k := by
        intro k hk
        apply ZMod.val_natCast_of_lt
        have hOFFk : OFFe k = VR.OFFf k := by simp only [hOFFe, if_neg (by omega : ¬ k = G - 1)]
        rw [hOFFk]
        have h1 := (hper k hk).1
        have h2 := (hWok k).2
        omega

      have ha_e : ∀ (j : ℕ) (hj : j < L),
          Expression.eval env (input_var.lhs[j]'hj) = input.lhs[j]'hj := by
        intro j hj
        rw [← h_input]
        simp [Vector.getElem_map]
      have hb_e : ∀ (j : ℕ) (hj : j < L),
          Expression.eval env (input_var.rhs[j]'hj) = input.rhs[j]'hj := by
        intro j hj
        rw [← h_input]
        simp [Vector.getElem_map]
      have hGP_e : ∀ j : ℕ, Expression.eval env (groupExprW B L gf posOf input_var.lhs j)
          = ((QP j : ℕ) : F p) := by
        intro j
        rw [groupExprW_eval, hQP_app, Nat.cast_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [Nat.cast_mul]
        congr 1
        · by_cases h : posOf j + i < L
          · rw [dif_pos h, ha_e _ h]
            simp only [hPn, dif_pos h]
            rw [ZMod.natCast_zmod_val]
          · rw [dif_neg h]
            simp only [hPn, dif_neg h]
            simp
        · push_cast
          rw [pow_mul]
      have hGS_e : ∀ j : ℕ, Expression.eval env (groupExprW B L gf posOf input_var.rhs j)
          = ((QS j : ℕ) : F p) := by
        intro j
        rw [groupExprW_eval, hQS_app, Nat.cast_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [Nat.cast_mul]
        congr 1
        · by_cases h : posOf j + i < L
          · rw [dif_pos h, hb_e _ h]
            simp only [hSn, dif_pos h]
            rw [ZMod.natCast_zmod_val]
          · rw [dif_neg h]
            simp only [hSn, dif_neg h]
            simp
        · push_cast
          rw [pow_mul]
      have hcarry_eval : ∀ k, k < G - 1 →
          Expression.eval env (carryExpr B gf posOf VR.OFFf input_var.lhs input_var.rhs k)
            = ((Cn k : ℕ) : F p) := by
        intro k hk
        simp only [hCn, if_neg (by omega : ¬ k = G - 1)]
        rw [ZMod.natCast_zmod_val]

      have h_idx : ∀ k, (hk : k < G - 2) →
          QP k + (if k = 0 then 0 else Cn (k - 1)) + OFFe k * 2 ^ (B * gf k)
            = QS k + Cn k * 2 ^ (B * gf k) + (if k = 0 then 0 else OFFe (k - 1)) := by
        intro k hk
        have hktop : ¬ k = G - 1 := by omega
        have hOFFk : OFFe k = VR.OFFf k := by simp only [hOFFe, if_neg hktop]
        have hCk_lt_p : Cn k < p := by
          have := hCn_lt k hk; have := (hWok k).2; omega
        have hCk_val : (((Cn k : ℕ) : F p)).val = Cn k := ZMod.val_natCast_of_lt hCk_lt_p
        have hCprev_lt_p : ∀ j, j < G - 2 → Cn j < p := by
          intro j hj
          have := hCn_lt j hj; have := (hWok j).2; omega
        have hfield : ((QP k : ℕ) : F p)
            + (if k = 0 then (0 : F p) else ((Cn (k - 1) : ℕ) : F p))
            + ((OFFe k : ℕ) : F p) * (2 ^ (B * gf k) : F p)
            = ((QS k : ℕ) : F p) + ((Cn k : ℕ) : F p) * (2 ^ (B * gf k) : F p)
              + (if k = 0 then (0 : F p) else ((OFFe (k - 1) : ℕ) : F p)) := by
          rw [hOFFk]
          rcases Nat.eq_zero_or_pos k with hk0 | hkpos
          · subst hk0
            have hcarry := hcarry_eval 0 (by omega)
            simp only [↓reduceIte]
            rw [← hcarry]
            simp [carryExpr, Expression.eval, hGP_e, hGS_e]
            field_simp [hbase_ne 0 (by omega)]
            ring_nf
          · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
            have hcarry := hcarry_eval (j + 1) (by omega)
            have hprev := hcarry_eval j (by omega)
            have hOFFj : OFFe j = VR.OFFf j := by
              simp only [hOFFe, if_neg (by omega : ¬ j = G - 1)]
            simp only [if_neg (by omega : ¬ j + 1 = 0), Nat.succ_sub_one,
              hOFFj]
            rw [← hcarry]
            simp [carryExpr, Expression.eval, hGP_e, hGS_e, hprev]
            field_simp [hbase_ne (j + 1) (by omega)]
            ring_nf
            try rw [hOFFj]
            try ring
        have hcin_val : (if k = 0 then (0 : F p) else ((Cn (k - 1) : ℕ) : F p)).val
            = if k = 0 then 0 else Cn (k - 1) := by
          split
          · exact ZMod.val_zero
          · exact ZMod.val_natCast_of_lt (hCprev_lt_p (k - 1) (by omega))
        have hoffR_val : (if k = 0 then (0 : F p) else ((OFFe (k - 1) : ℕ) : F p)).val
            = if k = 0 then 0 else OFFe (k - 1) := by
          split
          · exact ZMod.val_zero
          · exact hOFFe_cast (k - 1) (by omega)
        have hQPk_val : (((QP k : ℕ) : F p)).val = QP k :=
          ZMod.val_natCast_of_lt (lt_of_le_of_lt (hSfP k)
            (sum5_lt (hper k (by omega)).2.2).1)
        have hQSk_val : (((QS k : ℕ) : F p)).val = QS k :=
          ZMod.val_natCast_of_lt (lt_of_le_of_lt (hSfS k)
            (sum5_lt (hper k (by omega)).2.2).2.1)
        have hlhs : (((QP k : ℕ) : F p)).val + (if k = 0 then 0 else Cn (k - 1))
            + OFFe k * 2 ^ (B * gf k) < p := by
          rw [hQPk_val, hOFFk]
          have hnw := (hper k (by omega)).2.2
          have hSf := hSfP k
          have hcin : (if k = 0 then 0 else Cn (k - 1)) ≤ 2 ^ V.Wf (k - 1) := by
            split
            · positivity
            · have := hCn_lt (k - 1) (by omega); omega
          omega
        have hrhs : (((QS k : ℕ) : F p)).val + (((Cn k : ℕ) : F p)).val * 2 ^ (B * gf k)
            + (if k = 0 then 0 else OFFe (k - 1)) < p := by
          rw [hQSk_val, hCk_val]
          have hnw := (hper k (by omega)).2.2
          have hSf := hSfS k
          have hCkmul : Cn k * 2 ^ (B * gf k) ≤ 2 ^ V.Wf k * 2 ^ (B * gf k) :=
            Nat.mul_le_mul_right _ (by have := hCn_lt k hk; omega)
          have hoff : (if k = 0 then 0 else OFFe (k - 1)) ≤ 2 ^ V.Wf (k - 1) := by
            split
            · positivity
            · have hoe : OFFe (k - 1) = VR.OFFf (k - 1) := by
                simp only [hOFFe, if_neg (by omega : ¬ k - 1 = G - 1)]
              rw [hoe]; have := (hper (k - 1) (by omega)).1; omega
          omega
        have hlift := per_index_lift2 (B := B * gf k) ((QP k : ℕ) : F p)
          (if k = 0 then (0 : F p) else ((Cn (k - 1) : ℕ) : F p))
          ((QS k : ℕ) : F p) ((Cn k : ℕ) : F p)
          ((OFFe k : ℕ) : F p)
          (if k = 0 then (0 : F p) else ((OFFe (k - 1) : ℕ) : F p))
          (if k = 0 then 0 else Cn (k - 1)) (OFFe k) (if k = 0 then 0 else OFFe (k - 1))
          (hpBg k (by omega)) hcin_val (hOFFe_cast k (by omega)) hoffR_val hlhs hrhs hfield
        rw [hCk_val, hQPk_val, hQSk_val] at hlift
        exact hlift

      have hApos : polyValue B input.lhs = ∑ t ∈ Finset.range L, Pn t * 2 ^ (B * t) := by
        rw [polyValue, ← Fin.sum_univ_eq_sum_range (fun k => Pn k * 2 ^ (B * k))]
        apply Finset.sum_congr rfl
        intro i _; simp only [hPn, dif_pos i.isLt]
      have hBpos : polyValue B input.rhs = ∑ t ∈ Finset.range L, Sn t * 2 ^ (B * t) := by
        rw [polyValue, ← Fin.sum_univ_eq_sum_range (fun k => Sn k * 2 ^ (B * k))]
        apply Finset.sum_congr rfl
        intro i _; simp only [hSn, dif_pos i.isLt]
      have hMODP : ((polyValue B input.lhs : ℕ) : F p) = ((polyValue B input.rhs : ℕ) : F p) := by
        have hcl := polyValue_eval_cast B env input_var.lhs input.lhs (fun j hj => ha_e j hj)
        have hcr := polyValue_eval_cast B env input_var.rhs input.rhs (fun j hj => hb_e j hj)
        have hd := polyEvalExpr_diff_eval B env input_var.lhs input_var.rhs
        rw [← hcl, ← hcr] at hd
        rw [h_lin] at hd
        exact sub_eq_zero.mp hd.symm
      set n0 := G - 2 with hn0
      have hn0_pos : 1 ≤ n0 := by omega
      have hposn0_lt : posOf n0 < L := lt_of_le_of_lt (hposMono n0 (G - 1) (by omega)) hlast
      rw [show G - 3 = n0 - 1 from by omega] at htrunc
      set W := 2 ^ (B * posOf n0) with hW
      set SPlow := ∑ k ∈ Finset.range n0, QP k * 2 ^ (B * posOf k) with hSPlow
      set SSlow := ∑ k ∈ Finset.range n0, QS k * 2 ^ (B * posOf k) with hSSlow
      set TP := ∑ t ∈ Finset.range (L - posOf n0), Pn (posOf n0 + t) * 2 ^ (B * t) with hTP
      set TS := ∑ t ∈ Finset.range (L - posOf n0), Sn (posOf n0 + t) * 2 ^ (B * t) with hTS
      have hsplit : ∀ f : ℕ → ℕ, (∑ t ∈ Finset.range L, f t)
          = (∑ t ∈ Finset.range (posOf n0), f t)
            + ∑ i ∈ Finset.range (L - posOf n0), f (posOf n0 + i) := by
        intro f
        conv_lhs => rw [show L = posOf n0 + (L - posOf n0) from by omega]
        rw [Finset.sum_range_add]
      have hF1 : polyValue B input.lhs = SPlow + W * TP := by
        rw [hApos, hsplit (fun t => Pn t * 2 ^ (B * t))]
        congr 1
        · rw [hSPlow, ← group_flatten_sched B gf posOf Pn hpos0 hposS n0]
        · rw [hTP, hW, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          rw [show B * (posOf n0 + i) = B * posOf n0 + B * i from by ring, pow_add]
          ring
      have hF2 : polyValue B input.rhs = SSlow + W * TS := by
        rw [hBpos, hsplit (fun t => Sn t * 2 ^ (B * t))]
        congr 1
        · rw [hSSlow, ← group_flatten_sched B gf posOf Sn hpos0 hposS n0]
        · rw [hTS, hW, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          rw [show B * (posOf n0 + i) = B * posOf n0 + B * i from by ring, pow_add]
          ring
      have hsumlow : (∑ k ∈ Finset.range n0,
            ((QP k + (if k = 0 then 0 else Cn (k - 1))) + OFFe k * 2 ^ (B * gf k)) * 2 ^ (B * posOf k))
          = ∑ k ∈ Finset.range n0,
              (QS k + Cn k * 2 ^ (B * gf k) + (if k = 0 then 0 else OFFe (k - 1))) * 2 ^ (B * posOf k) := by
        apply Finset.sum_congr rfl
        intro k hk; rw [Finset.mem_range] at hk
        rw [h_idx k hk]
      have hLHSlow : (∑ k ∈ Finset.range n0,
            ((QP k + (if k = 0 then 0 else Cn (k - 1))) + OFFe k * 2 ^ (B * gf k)) * 2 ^ (B * posOf k))
          = SPlow + (∑ k ∈ Finset.range n0, (if k = 0 then 0 else Cn (k - 1)) * 2 ^ (B * posOf k))
            + (∑ k ∈ Finset.range n0, OFFe k * 2 ^ (B * posOf (k + 1))) := by
        rw [hSPlow, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _
        rw [he k, pow_add]; ring
      have hRHSlow : (∑ k ∈ Finset.range n0,
            (QS k + Cn k * 2 ^ (B * gf k) + (if k = 0 then 0 else OFFe (k - 1))) * 2 ^ (B * posOf k))
          = SSlow + (∑ k ∈ Finset.range n0, Cn k * 2 ^ (B * posOf (k + 1)))
            + (∑ k ∈ Finset.range n0, (if k = 0 then 0 else OFFe (k - 1)) * 2 ^ (B * posOf k)) := by
        rw [hSSlow, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _
        rw [he k, pow_add]; ring
      have htelC := carry_telescope_e (fun k => B * posOf k) Cn n0
      simp only [] at htelC
      rw [if_neg (by omega : ¬ (n0 = 0)), ← hW] at htelC
      have htelO := carry_telescope_e (fun k => B * posOf k) OFFe n0
      simp only [] at htelO
      rw [if_neg (by omega : ¬ (n0 = 0)), ← hW] at htelO
      have hdagger : SPlow + OFFe (n0 - 1) * W = SSlow + Cn (n0 - 1) * W := by
        have key := hsumlow
        rw [hLHSlow, hRHSlow] at key
        omega
      have hcombo : polyValue B input.lhs + W * (OFFe (n0 - 1) + TS)
          = polyValue B input.rhs + W * (Cn (n0 - 1) + TP) := by
        have hd2 : SPlow + W * OFFe (n0 - 1) = SSlow + W * Cn (n0 - 1) := by
          rw [Nat.mul_comm W (OFFe (n0 - 1)), Nat.mul_comm W (Cn (n0 - 1))]; exact hdagger
        rw [hF1, hF2, Nat.mul_add, Nat.mul_add]
        omega
      have hWF_ne : (W : F p) ≠ 0 := by
        have hp2 : (2 : ℕ) < p := Fact.out
        have h2ne : ((2 : ℕ) : F p) ≠ 0 := by
          intro h0
          have hv := ZMod.val_natCast_of_lt hp2
          rw [h0, ZMod.val_zero] at hv; omega
        rw [hW, Nat.cast_pow]
        exact pow_ne_zero _ h2ne
      have hcast : ((polyValue B input.lhs : ℕ) : F p)
            + (W : F p) * (((OFFe (n0 - 1) + TS : ℕ)) : F p)
          = ((polyValue B input.rhs : ℕ) : F p)
            + (W : F p) * (((Cn (n0 - 1) + TP : ℕ)) : F p) := by
        have h := congrArg (fun n : ℕ => (n : F p)) hcombo
        simpa only [Nat.cast_add, Nat.cast_mul] using h
      have hfield_eq : (((OFFe (n0 - 1) + TS : ℕ)) : F p) = (((Cn (n0 - 1) + TP : ℕ)) : F p) := by
        rw [hMODP] at hcast
        exact mul_left_cancel₀ hWF_ne (add_left_cancel hcast)
      have hOFFn0 : OFFe (n0 - 1) = VR.OFFf (n0 - 1) := by
        simp only [hOFFe, if_neg (by omega : ¬ n0 - 1 = G - 1)]
      have hOFF_lt : OFFe (n0 - 1) < 2 ^ V.Wf (n0 - 1) := by
        rw [hOFFn0]
        have := (hper (n0 - 1) (by omega)).1
        omega
      have hCn_lt_b : Cn (n0 - 1) < 2 ^ V.Wf (n0 - 1) := hCn_lt (n0 - 1) (by omega)
      have hTP_lt : TP < ∑ t ∈ Finset.range (L - posOf n0), V.Nf (posOf n0 + t) * 2 ^ (B * t) := by
        rw [hTP]
        apply Finset.sum_lt_sum_of_nonempty
        · rw [Finset.nonempty_range_iff]; omega
        · intro t _; exact mul_lt_mul_of_pos_right (hPn_lt (posOf n0 + t)) (by positivity)
      have hTS_lt : TS < ∑ t ∈ Finset.range (L - posOf n0), VR.Nf (posOf n0 + t) * 2 ^ (B * t) := by
        rw [hTS]
        apply Finset.sum_lt_sum_of_nonempty
        · rw [Finset.nonempty_range_iff]; omega
        · intro t _; exact mul_lt_mul_of_pos_right (hSn_lt (posOf n0 + t)) (by positivity)
      have hlt1 : OFFe (n0 - 1) + TS < p := by omega
      have hlt2 : Cn (n0 - 1) + TP < p := by omega
      have hnat_eq : OFFe (n0 - 1) + TS = Cn (n0 - 1) + TP := by
        have hv := congrArg ZMod.val hfield_eq
        rwa [ZMod.val_natCast_of_lt hlt1, ZMod.val_natCast_of_lt hlt2] at hv
      have hSpec : polyValue B input.lhs = polyValue B input.rhs := by
        rw [hnat_eq] at hcombo
        exact Nat.add_right_cancel hcombo
      rw [EqViaCarriesFlex.Spec]
      exact ⟨hSpec, carryLoop_requirements B gf posOf VR.OFFf V.Wf hWok env
        input_var.lhs input_var.rhs _ _ _⟩
    completeness := by
      obtain ⟨hpos0, hposS, hgf1, hWok, hNf1, hper, hG3, hlast, hCov, _⟩ := hgv
      circuit_proof_start
      have hM : 0 < L := Nat.pos_of_neZero L
      have hG1 : 0 < G := by omega
      have hposMono : ∀ a b, a ≤ b → posOf a ≤ posOf b :=
        fun a b hab => monotone_nat_of_le_succ (fun k => by rw [hposS k]; omega) hab
      have he : ∀ k, B * posOf (k + 1) = B * posOf k + B * gf k :=
        fun k => by rw [hposS k, Nat.mul_add]
      have hemono : ∀ k, B * posOf k ≤ B * posOf (k + 1) := fun k => by rw [he k]; omega
      have hpBg : ∀ k, k < G - 1 → 2 ^ (B * gf k) < p := fun k hk =>
        lt_of_le_of_lt (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _))
          (sum5_lt (hper k hk).2.2).2.2.1

      set Pn : ℕ → ℕ := fun k => if h : k < L then (input.lhs[k]'h).val else 0 with hPn
      set Sn : ℕ → ℕ := fun k => if h : k < L then (input.rhs[k]'h).val else 0 with hSn
      have hPn_lt : ∀ k, Pn k < V.Nf k := by
        intro k; simp only [hPn]; split
        · rename_i h; exact h_assumptions.1 ⟨k, h⟩
        · exact (hNf1 k).1
      have hSn_lt : ∀ k, Sn k < VR.Nf k := by
        intro k; simp only [hSn]; split
        · rename_i h; exact h_assumptions.2 ⟨k, h⟩
        · exact (hNf1 k).2

      set QP : ℕ → ℕ := fun j => ∑ i ∈ Finset.range (gf j), Pn (posOf j + i) * 2 ^ (B * i) with hQP
      set QS : ℕ → ℕ := fun j => ∑ i ∈ Finset.range (gf j), Sn (posOf j + i) * 2 ^ (B * i) with hQS
      have hQP_app : ∀ j, QP j = ∑ i ∈ Finset.range (gf j), Pn (posOf j + i) * 2 ^ (B * i) :=
        fun _ => rfl
      have hQS_app : ∀ j, QS j = ∑ i ∈ Finset.range (gf j), Sn (posOf j + i) * 2 ^ (B * i) :=
        fun _ => rfl

      set PFn : ℕ → ℕ := fun k => ∑ j ∈ Finset.range (k + 1), QP j * 2 ^ (B * posOf j) with hPFn
      set PSn : ℕ → ℕ := fun k => ∑ j ∈ Finset.range (k + 1), QS j * 2 ^ (B * posOf j) with hPSn
      set Dk : ℕ → ℕ := fun k => 2 ^ (B * posOf (k + 1)) with hDk
      set Cn : ℕ → ℕ := fun k => VR.OFFf k + PFn k / Dk k - PSn k / Dk k with hCn
      have hDk_app : ∀ k, Dk k = 2 ^ (B * posOf (k + 1)) := fun _ => rfl
      have hPFn_app : ∀ k, PFn k = ∑ j ∈ Finset.range (k + 1), QP j * 2 ^ (B * posOf j) :=
        fun _ => rfl
      have hPSn_app : ∀ k, PSn k = ∑ j ∈ Finset.range (k + 1), QS j * 2 ^ (B * posOf j) :=
        fun _ => rfl
      have hCn_app : ∀ k, Cn k = VR.OFFf k + PFn k / Dk k - PSn k / Dk k := fun _ => rfl

      have ha_e : ∀ (j : ℕ) (hj : j < L),
          Expression.eval env.toEnvironment (input_var.lhs[j]'hj) = input.lhs[j]'hj := by
        intro j hj
        rw [← h_input]
        simp [Vector.getElem_map]
      have hb_e : ∀ (j : ℕ) (hj : j < L),
          Expression.eval env.toEnvironment (input_var.rhs[j]'hj) = input.rhs[j]'hj := by
        intro j hj
        rw [← h_input]
        simp [Vector.getElem_map]

      have hOFFrec : ∀ k, k < G - 1 →
          (if k = 0 then 0 else V.OFFf (k - 1)) + 1
              + (∑ i ∈ Finset.range (gf k), (V.Nf (posOf k + i) - 1) * 2 ^ (B * i))
            ≤ (V.OFFf k + 1) * 2 ^ (B * gf k) :=
        fun k hk => (hper k hk).2.1.1
      have hOFFrecR : ∀ k, k < G - 1 →
          (if k = 0 then 0 else VR.OFFf (k - 1)) + 1
              + (∑ i ∈ Finset.range (gf k), (VR.Nf (posOf k + i) - 1) * 2 ^ (B * i))
            ≤ (VR.OFFf k + 1) * 2 ^ (B * gf k) :=
        fun k hk => (hper k hk).2.1.2
      have hPFdiv : ∀ k, k < G - 1 → PFn k / Dk k ≤ V.OFFf k := by
        intro k hk
        have h1 := prefix_div_le_sched B gf posOf V.OFFf V.Nf (G - 1) he hOFFrec Pn hPn_lt k hk
        rw [hPFn_app, hDk_app]
        exact Nat.lt_succ_iff.mp (Nat.div_lt_of_lt_mul (by
          calc (∑ j ∈ Finset.range (k + 1), QP j * 2 ^ (B * posOf j))
              < (V.OFFf k + 1) * 2 ^ (B * posOf (k + 1)) := h1
            _ = 2 ^ (B * posOf (k + 1)) * (V.OFFf k + 1) := by ring))
      have hPSdiv : ∀ k, k < G - 1 → PSn k / Dk k ≤ VR.OFFf k := by
        intro k hk
        have h1 := prefix_div_le_sched B gf posOf VR.OFFf VR.Nf (G - 1) he hOFFrecR Sn hSn_lt k hk
        rw [hPSn_app, hDk_app]
        exact Nat.lt_succ_iff.mp (Nat.div_lt_of_lt_mul (by
          calc (∑ j ∈ Finset.range (k + 1), QS j * 2 ^ (B * posOf j))
              < (VR.OFFf k + 1) * 2 ^ (B * posOf (k + 1)) := h1
            _ = 2 ^ (B * posOf (k + 1)) * (VR.OFFf k + 1) := by ring))
      have hrange : ∀ k, k < G - 1 → Cn k < 2 ^ V.Wf k := by
        intro k hk
        have h1 := hPFdiv k hk
        have h2 := (hper k hk).1
        rw [hCn_app]
        calc VR.OFFf k + PFn k / Dk k - PSn k / Dk k
            ≤ VR.OFFf k + PFn k / Dk k := Nat.sub_le _ _
          _ ≤ VR.OFFf k + V.OFFf k := by omega
          _ < 2 ^ V.Wf k := by omega

      have hPFn_top : PFn (G - 1) = polyValue B input.lhs := by
        rw [hPFn_app, show G - 1 + 1 = G from by omega]
        have h1 : polyValue B input.lhs = ∑ k ∈ Finset.range (L), Pn k * 2 ^ (B * k) := by
          rw [polyValue, ← Fin.sum_univ_eq_sum_range (fun k => Pn k * 2 ^ (B * k))]
          apply Finset.sum_congr rfl
          intro i _; simp only [hPn, dif_pos i.isLt]
        rw [h1, sum_extend_zero B (L) (posOf G) Pn hCov
          (fun t ht => by simp only [hPn, dif_neg (by omega : ¬ t < L)]),
          ← group_flatten_sched B gf posOf Pn hpos0 hposS G]
      have hPSn_top : PSn (G - 1) = polyValue B input.rhs := by
        rw [hPSn_app, show G - 1 + 1 = G from by omega]
        have h1 : polyValue B input.rhs = ∑ k ∈ Finset.range (L), Sn k * 2 ^ (B * k) := by
          rw [polyValue, ← Fin.sum_univ_eq_sum_range (fun k => Sn k * 2 ^ (B * k))]
          apply Finset.sum_congr rfl
          intro i _; simp only [hSn, dif_pos i.isLt]
        rw [h1, sum_extend_zero B (L) (posOf G) Sn hCov
          (fun t ht => by simp only [hSn, dif_neg (by omega : ¬ t < L)]),
          ← group_flatten_sched B gf posOf Sn hpos0 hposS G]
      have hPtop_eq : PFn (G - 1) = PSn (G - 1) := by
        rw [hPFn_top, hPSn_top]; exact h_spec
      have hmod : ∀ k, k < G → PFn k % Dk k = PSn k % Dk k := by
        intro k hk
        have e1 : PFn (G - 1) % Dk k = PFn k % Dk k := by
          rw [hPFn_app, hPFn_app, hDk_app, show G - 1 + 1 = G from by omega]
          have := partial_mod_stable_e (fun j => B * posOf j) hemono QP G k hk
          simpa only [] using this
        have e2 : PSn (G - 1) % Dk k = PSn k % Dk k := by
          rw [hPSn_app, hPSn_app, hDk_app, show G - 1 + 1 = G from by omega]
          have := partial_mod_stable_e (fun j => B * posOf j) hemono QS G k hk
          simpa only [] using this
        rw [← e1, ← e2, hPtop_eq]

      have hidx : ∀ k, k < G →
          QP k + (if k = 0 then 0 else Cn (k - 1)) + VR.OFFf k * 2 ^ (B * gf k)
            = QS k + Cn k * 2 ^ (B * gf k) + (if k = 0 then 0 else VR.OFFf (k - 1)) := by
        intro k hk
        set qP := PFn k / 2 ^ (B * posOf k) with hqP_def
        set qS := PSn k / 2 ^ (B * posOf k) with hqS_def
        set rP := PFn k / Dk k with hrP_def
        set rS := PSn k / Dk k with hrS_def
        have hrP_quot : rP = qP / 2 ^ (B * gf k) := by
          rw [hrP_def, hqP_def, hDk_app, he k, pow_add, Nat.div_div_eq_div_mul]
        have hrS_quot : rS = qS / 2 ^ (B * gf k) := by
          rw [hrS_def, hqS_def, hDk_app, he k, pow_add, Nat.div_div_eq_div_mul]
        have hsplitP : qP = rP * 2 ^ (B * gf k) + qP % 2 ^ (B * gf k) := by
          rw [hrP_quot]; exact (Nat.div_add_mod' qP (2 ^ (B * gf k))).symm
        have hsplitS : qS = rS * 2 ^ (B * gf k) + qS % 2 ^ (B * gf k) := by
          rw [hrS_quot]; exact (Nat.div_add_mod' qS (2 ^ (B * gf k))).symm
        have hdig : qP % 2 ^ (B * gf k) = qS % 2 ^ (B * gf k) := by
          have hP : qP % 2 ^ (B * gf k) = PFn k % Dk k / 2 ^ (B * posOf k) := by
            rw [hqP_def, hDk_app, he k, pow_add, Nat.mod_mul_right_div_self]
          have hS : qS % 2 ^ (B * gf k) = PSn k % Dk k / 2 ^ (B * posOf k) := by
            rw [hqS_def, hDk_app, he k, pow_add, Nat.mod_mul_right_div_self]
          rw [hP, hS, hmod k hk]
        have hstepP : qP = QP k + (if k = 0 then 0
            else (∑ j ∈ Finset.range k, QP j * 2 ^ (B * posOf j)) / 2 ^ (B * posOf k)) := by
          rw [hqP_def, hPFn_app]
          have := quot_step_e (fun j => B * posOf j) QP k
          simpa only [] using this
        have hstepS : qS = QS k + (if k = 0 then 0
            else (∑ j ∈ Finset.range k, QS j * 2 ^ (B * posOf j)) / 2 ^ (B * posOf k)) := by
          rw [hqS_def, hPSn_app]
          have := quot_step_e (fun j => B * posOf j) QS k
          simpa only [] using this
        have hCnk : Cn k = VR.OFFf k + rP - rS := by rw [hCn_app, ← hrP_def, ← hrS_def]
        have hrS_le : rS ≤ VR.OFFf k + rP := by
          have hEq := hmod k hk
          rcases Nat.le_total (PSn k) (PFn k) with hle | hle
          · have : rS ≤ rP := by
              rw [hrS_def, hrP_def]; exact Nat.div_le_div_right hle
            omega
          · have hdvd : Dk k ∣ (PSn k - PFn k) := (Nat.modEq_iff_dvd' hle).mp hEq
            obtain ⟨t, ht⟩ := hdvd
            have hD_pos : 0 < Dk k := Nat.two_pow_pos _
            have hquot : rS = rP + t := by
              rw [hrS_def, hrP_def]
              have : PSn k = PFn k + Dk k * t := by omega
              rw [this, Nat.add_mul_div_left _ _ hD_pos]
            by_cases hkG : k < G - 1
            · have h2 := hPSdiv k hkG
              rw [← hrS_def] at h2
              exact le_trans h2 (Nat.le_add_right _ _)
            · have hkeq : k = G - 1 := by omega
              rw [hkeq] at ht
              rw [hPtop_eq] at ht
              have hD_pos' : 0 < Dk (G - 1) := Nat.two_pow_pos _
              have ht0 : Dk (G - 1) * t = 0 := by omega
              have ht' : t = 0 :=
                (Nat.mul_eq_zero.mp ht0).resolve_left (Nat.pos_iff_ne_zero.mp hD_pos')
              rw [hquot, ht', Nat.add_zero]
              exact Nat.le_add_left _ _
        rw [hdig] at hsplitP
        clear_value qP qS rP rS
        have hmulCnk : Cn k * 2 ^ (B * gf k) = VR.OFFf k * 2 ^ (B * gf k) + rP * 2 ^ (B * gf k)
            - rS * 2 ^ (B * gf k) := by
          rw [hCnk, Nat.sub_mul, Nat.add_mul]
        rcases Nat.eq_zero_or_pos k with hk0 | hk0
        · subst hk0
          rw [hmulCnk]
          simp only [↓reduceIte] at hstepP hstepS ⊢
          rw [Nat.add_zero] at hstepP hstepS
          have hrPmul : rS * 2 ^ (B * gf 0) ≤ rP * 2 ^ (B * gf 0) + VR.OFFf 0 * 2 ^ (B * gf 0) := by
            have hle : rS ≤ rP + VR.OFFf 0 := by omega
            calc rS * 2 ^ (B * gf 0) ≤ (rP + VR.OFFf 0) * 2 ^ (B * gf 0) := Nat.mul_le_mul_right _ hle
              _ = rP * 2 ^ (B * gf 0) + VR.OFFf 0 * 2 ^ (B * gf 0) := by rw [Nat.add_mul]
          omega
        · rw [if_neg (by omega : ¬ k = 0), if_neg (by omega : ¬ k = 0), hmulCnk]
          have hPFnprev : (∑ j ∈ Finset.range k, QP j * 2 ^ (B * posOf j)) = PFn (k - 1) := by
            rw [hPFn_app, show k - 1 + 1 = k from by omega]
          have hPSnprev : (∑ j ∈ Finset.range k, QS j * 2 ^ (B * posOf j)) = PSn (k - 1) := by
            rw [hPSn_app, show k - 1 + 1 = k from by omega]
          rw [if_neg (by omega : ¬ k = 0), hPFnprev] at hstepP
          rw [if_neg (by omega : ¬ k = 0), hPSnprev] at hstepS
          set rP' := PFn (k - 1) / Dk (k - 1) with hrP'_def
          set rS' := PSn (k - 1) / Dk (k - 1) with hrS'_def
          have hprevP : PFn (k - 1) / 2 ^ (B * posOf k) = rP' := by
            rw [hrP'_def, hDk_app, show k - 1 + 1 = k from by omega]
          have hprevS : PSn (k - 1) / 2 ^ (B * posOf k) = rS' := by
            rw [hrS'_def, hDk_app, show k - 1 + 1 = k from by omega]
          rw [hprevP] at hstepP
          rw [hprevS] at hstepS
          have hCnprev : Cn (k - 1) = VR.OFFf (k - 1) + rP' - rS' := hCn_app (k - 1)
          have hrSprev_le : rS' ≤ VR.OFFf (k - 1) + rP' := by
            have hEq := hmod (k - 1) (by omega)
            rcases Nat.le_total (PSn (k - 1)) (PFn (k - 1)) with hle | hle
            · have : rS' ≤ rP' := by
                rw [hrS'_def, hrP'_def]; exact Nat.div_le_div_right hle
              omega
            · have hdvd : Dk (k - 1) ∣ (PSn (k - 1) - PFn (k - 1)) :=
                (Nat.modEq_iff_dvd' hle).mp hEq
              obtain ⟨t, ht⟩ := hdvd
              have hD_pos : 0 < Dk (k - 1) := Nat.two_pow_pos _
              have hquot : rS' = rP' + t := by
                rw [hrS'_def, hrP'_def]
                have : PSn (k - 1) = PFn (k - 1) + Dk (k - 1) * t := by omega
                rw [this, Nat.add_mul_div_left _ _ hD_pos]
              by_cases hkG : k - 1 < G - 1
              · have h2 := hPSdiv (k - 1) hkG
                rw [← hrS'_def] at h2
                exact le_trans h2 (Nat.le_add_right _ _)
              · have hkeq : k - 1 = G - 1 := by omega
                rw [hkeq] at ht
                rw [hPtop_eq] at ht
                have hD_pos' : 0 < Dk (G - 1) := Nat.two_pow_pos _
                have ht0 : Dk (G - 1) * t = 0 := by omega
                have ht' : t = 0 :=
                  (Nat.mul_eq_zero.mp ht0).resolve_left (Nat.pos_iff_ne_zero.mp hD_pos')
                rw [hquot, ht', Nat.add_zero]
                exact Nat.le_add_left _ _
          rw [hCnprev]
          clear_value rP' rS'
          have hrPmul : rS * 2 ^ (B * gf k) ≤ rP * 2 ^ (B * gf k) + VR.OFFf k * 2 ^ (B * gf k) := by
            have hle : rS ≤ rP + VR.OFFf k := by omega
            calc rS * 2 ^ (B * gf k) ≤ (rP + VR.OFFf k) * 2 ^ (B * gf k) := Nat.mul_le_mul_right _ hle
              _ = rP * 2 ^ (B * gf k) + VR.OFFf k * 2 ^ (B * gf k) := by rw [Nat.add_mul]
          omega

      have hGP_e : ∀ j : ℕ, Expression.eval env.toEnvironment (groupExprW B L gf posOf input_var.lhs j)
          = ((QP j : ℕ) : F p) := by
        intro j
        rw [groupExprW_eval, hQP_app, Nat.cast_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [Nat.cast_mul]
        congr 1
        · by_cases h : posOf j + i < L
          · rw [dif_pos h, ha_e _ h]
            simp only [hPn, dif_pos h]
            rw [ZMod.natCast_zmod_val]
          · rw [dif_neg h]
            simp only [hPn, dif_neg h]
            simp
        · push_cast
          rw [pow_mul]
      have hGS_e : ∀ j : ℕ, Expression.eval env.toEnvironment (groupExprW B L gf posOf input_var.rhs j)
          = ((QS j : ℕ) : F p) := by
        intro j
        rw [groupExprW_eval, hQS_app, Nat.cast_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [Nat.cast_mul]
        congr 1
        · by_cases h : posOf j + i < L
          · rw [dif_pos h, hb_e _ h]
            simp only [hSn, dif_pos h]
            rw [ZMod.natCast_zmod_val]
          · rw [dif_neg h]
            simp only [hSn, dif_neg h]
            simp
        · push_cast
          rw [pow_mul]
      have hbase_ne : ∀ k, k < G - 1 → ((2 : F p) ^ (B * gf k) ≠ 0) := by
        intro k hk
        have hnat : (((2 ^ (B * gf k) : ℕ) : F p) ≠ 0) := by
          intro hzero
          have hval : (((2 ^ (B * gf k) : ℕ) : F p).val) = 2 ^ (B * gf k) :=
            ZMod.val_natCast_of_lt (hpBg k hk)
          rw [hzero, ZMod.val_zero] at hval
          have : 0 < 2 ^ (B * gf k) := Nat.two_pow_pos _
          omega
        simpa [Nat.cast_pow] using hnat
      have hpow_cast : ∀ k, ((2 ^ (B * gf k) : ℕ) : F p) = (2 ^ (B * gf k) : F p) := by
        intro k; push_cast; ring
      have hcarry_eval : ∀ k, k < G - 1 →
          Expression.eval env.toEnvironment (carryExpr B gf posOf VR.OFFf input_var.lhs input_var.rhs k)
            = ((Cn k : ℕ) : F p) := by
        intro k hk
        induction k with
        | zero =>
            have hnatk := hidx 0 (by omega)
            simp only [↓reduceIte] at hnatk
            have hcast := congrArg (Nat.cast : ℕ → F p) hnatk
            push_cast [hpow_cast 0] at hcast
            simp [carryExpr, Expression.eval, hGP_e, hGS_e]
            field_simp [hbase_ne 0 (by omega)]
            linear_combination hcast
        | succ j ih =>
            have hprev := ih (by omega)
            have hnatk := hidx (j + 1) (by omega)
            simp only [if_neg (by omega : ¬ j + 1 = 0), Nat.add_sub_cancel] at hnatk
            have hcast := congrArg (Nat.cast : ℕ → F p) hnatk
            push_cast [hpow_cast (j + 1)] at hcast
            simp [carryExpr, Expression.eval, hGP_e, hGS_e, hprev]
            field_simp [hbase_ne (j + 1) (by omega)]
            linear_combination hcast
      refine ⟨?_, ?_⟩
      ·
        refine carryLoop_completeness B gf posOf VR.OFFf V.Wf hWok env
          input_var.lhs input_var.rhs (G - 2) 0 i₀ fun i hi => ?_
        rw [Nat.zero_add, hcarry_eval i (by omega),
          ZMod.val_natCast_of_lt (lt_trans (hrange i (by omega)) (hWok i).2)]
        exact hrange i (by omega)
      ·
        have hspec' : polyValue B input.lhs = polyValue B input.rhs := h_spec
        have hcl := polyValue_eval_cast B env.toEnvironment input_var.lhs input.lhs
          (fun j hj => ha_e j hj)
        have hcr := polyValue_eval_cast B env.toEnvironment input_var.rhs input.rhs
          (fun j hj => hb_e j hj)
        have hd := polyEvalExpr_diff_eval B env.toEnvironment input_var.lhs input_var.rhs
        rw [← hcl, ← hcr, hspec', sub_self] at hd
        try simp only [circuit_norm]
        exact hd

lemma carryExpr_eval_stable (B : ℕ) (gf posOf OFFf : ℕ → ℕ)
    (lhs rhs : Var (EqViaCarriesFlex.Coeffs L) (F p)) (env env' : Environment (F p))
    (hl : ∀ j (hj : j < L),
      Expression.eval env (lhs[j]'hj) = Expression.eval env' (lhs[j]'hj))
    (hr : ∀ j (hj : j < L),
      Expression.eval env (rhs[j]'hj) = Expression.eval env' (rhs[j]'hj)) :
    ∀ k, Expression.eval env (carryExpr B gf posOf OFFf lhs rhs k)
      = Expression.eval env' (carryExpr B gf posOf OFFf lhs rhs k) := by
  have hg : ∀ (x : Var (EqViaCarriesFlex.Coeffs L) (F p)),
      (∀ j (hj : j < L),
        Expression.eval env (x[j]'hj) = Expression.eval env' (x[j]'hj)) →
      ∀ k, Expression.eval env (groupExprW B L gf posOf x k)
        = Expression.eval env' (groupExprW B L gf posOf x k) := by
    intro x hx k
    rw [groupExprW_eval, groupExprW_eval]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    by_cases h : posOf k + i < L
    · simp only [dif_pos h]
      exact hx _ h
    · simp only [dif_neg h]
  intro k
  induction k with
  | zero =>
    simp only [carryExpr, Expression.eval, hg lhs hl 0, hg rhs hr 0]
  | succ k ih =>
    simp only [carryExpr, Expression.eval, hg lhs hl (k+1), hg rhs hr (k+1), ih]

lemma carryLoop_structuralComputableWitnesses (B : ℕ) (gf posOf OFFf Wf : ℕ → ℕ)
    (hWok : ∀ k, 1 ≤ Wf k ∧ 2 ^ Wf k < p) [Fact (p > 2)]
    (input : Var (EqViaCarriesFlex.Inputs L) (F p))
    (lhs rhs : Var (EqViaCarriesFlex.Coeffs L) (F p))
    (hstab : ∀ (e1 e2 : ProverEnvironment (F p)), eval e1 input = eval e2 input →
      ∀ k, Expression.eval e1.toEnvironment (carryExpr B gf posOf OFFf lhs rhs k)
        = Expression.eval e2.toEnvironment (carryExpr B gf posOf OFFf lhs rhs k))
    (env env' : ProverEnvironment (F p)) :
    ∀ (c k₀ offset : ℕ),
      Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.StructuralComputableWitnesses
        input env env' offset
        ((carryLoop B gf posOf OFFf Wf hWok lhs rhs c k₀).operations offset) := by
  intro c
  induction c with
  | zero =>
    intro k₀ offset
    simp [carryLoop, Circuit.pure_operations_eq,
      Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.StructuralComputableWitnesses]
  | succ n ih =>
    intro k₀ offset
    rw [show carryLoop B gf posOf OFFf Wf hWok lhs rhs (n + 1) k₀
        = (do
            assertion (RangeCheck.circuit (Wf k₀) (hWok k₀).2 (hWok k₀).1)
              (carryExpr B gf posOf OFFf lhs rhs k₀)
            carryLoop B gf posOf OFFf Wf hWok lhs rhs n (k₀ + 1)) from rfl]
    rw [Circuit.bind_operations_eq,
      Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.structuralComputableWitnesses_append]
    constructor
    · simp only [
        Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_structuralComputableWitnesses_iff]
      exact Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
        (RangeCheck.circuit (Wf k₀) (hWok k₀).2 (hWok k₀).1) input
        (carryExpr B gf posOf OFFf lhs rhs k₀) offset
        (by
          intro k e1 e2 hk h_agree h_parent
          rw [CircuitType.eval_var_field_prover, CircuitType.eval_var_field_prover]
          exact hstab e1 e2 h_parent k₀)
        (RangeCheck.computableWitnesses (Wf k₀) (hWok k₀).2 (hWok k₀).1) env env'
    · simpa [Nat.add_comm, Circuit.localLength] using ih (k₀ + 1) _

theorem computableWitnesses (B : ℕ) (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : VParams)
    (hgv : GVXHyps p L B gf posOf G V VR) (hB1 : 1 ≤ B) [Fact (p > 2)] :
    (circuit B gf posOf G V VR hgv hB1).ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition input env env')
    ((main B gf posOf G V VR hgv input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.assertZero_structuralComputableWitnesses_iff,
    and_true]
  exact carryLoop_structuralComputableWitnesses B gf posOf VR.OFFf V.Wf hgv.2.2.2.1 input
    input.lhs input.rhs
    (by
      intro e1 e2 h_parent k
      have hparts :
          (∀ a ∈ input.lhs, Expression.eval e1.toEnvironment a =
              Expression.eval e2.toEnvironment a) ∧
            ∀ a ∈ input.rhs, Expression.eval e1.toEnvironment a =
              Expression.eval e2.toEnvironment a := by
        simpa [circuit_norm, CircuitType.eval_expression_prover_to_verifier,
          CircuitType.eval_expression, ProvableType.eval, explicit_provable_type] using h_parent
      exact carryExpr_eval_stable B gf posOf VR.OFFf input.lhs input.rhs
        e1.toEnvironment e2.toEnvironment
        (fun j hj => hparts.1 _ (by
          simp only [Vector.mem_iff_getElem]
          exact ⟨j, hj, rfl⟩))
        (fun j hj => hparts.2 _ (by
          simp only [Vector.mem_iff_getElem]
          exact ⟨j, hj, rfl⟩)) k)
    env env' (G - 2) 0 offset

end GroupedFlex

end

namespace Cost

open Challenge.CostR1CS
open GroupedFlex (VParams)

theorem costIs_implicitRangeCheck (n : ℕ) (hpos : 1 ≤ n) (x : Expression (F circomPrime)) :
    CostIs (RangeCheck.main n x) ⟨n - 1, n⟩ := by
  unfold RangeCheck.main
  rw [show (⟨n - 1, n⟩ : Count)
        = ⟨n - 1, 0⟩ + (⟨(n - 1) * 0, (n - 1) * 1⟩ + (⟨0, 1⟩ + Count.zero)) from by
      simp only [Count.zero]; congr 1 <;> simp only [Count.add_constraints] <;> omega]
  refine CostIs.bind (CostIs.witnessVector (F := F circomPrime) (n - 1) _) fun bits => ?_
  refine CostIs.bind (CostIs.forEach fun a m => CostIs.assertZero _ m) fun _ => ?_
  exact CostIs.bind (CostIs.assertZero _) fun _ => CostIs.pure _

theorem isR1CS_implicitRangeCheck (n : ℕ) (x : Expression (F circomPrime)) (hx : Affine x) :
    IsR1CSCirc (RangeCheck.main n x) := by
  unfold RangeCheck.main
  refine IsR1CSCirc.bind_out (IsR1CSCirc.witnessVector (n - 1) _) fun w => ?_
  refine IsR1CSCirc.bind ?_ fun _ => ?_
  · refine IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) fun i k => ?_
    refine IsR1CSCirc.assertZero ?_ k
    exact isR1CSRow_mul (affineW_witnessVector_output _ _ _ i.val i.isLt)
      (Affine.sub (affineW_witnessVector_output _ _ _ i.val i.isLt) (Affine.const 1))
  · refine IsR1CSCirc.bind (IsR1CSCirc.assertZero ?_) fun _ => IsR1CSCirc.pure _
    let bits : Var (fields (n - 1)) (F circomPrime) :=
      (Circuit.witnessVector (n - 1) fun env => Utils.Bits.fieldToBits (n - 1) (x.eval env)).output w
    have hbits : Affine (Utils.Bits.fieldFromBitsExpr bits) := by
      change Affine (Utils.Bits.fieldFromBitsExpr
        (Vector.mapRange (n - 1) fun i => Expression.var { index := w + i }))
      exact affine_fieldFromBitsExpr _ (affineW_mapRange_var _)
    let c : F circomPrime := (((2 ^ (n - 1) : ℕ) : F circomPrime)⁻¹ : F circomPrime)
    have htop : Affine (c * (x - Utils.Bits.fieldFromBitsExpr bits)) := by
      exact Affine.fconst_mul c (Affine.sub hx hbits)
    exact isR1CSRow_mul htop (Affine.sub htop (Affine.const 1))

theorem costIs_assertion_implicitRangeCheck (n : ℕ) (hn : (2 : ℕ) ^ n < circomPrime)
    (hpos : 1 ≤ n) (x : Expression (F circomPrime)) :
    CostIs (assertion (RangeCheck.circuit n hn hpos) x) ⟨n - 1, n⟩ :=
  CostIs.assertion (fun m => costIs_implicitRangeCheck n hpos x m)

theorem isR1CS_assertion_implicitRangeCheck (n : ℕ) (hn : (2 : ℕ) ^ n < circomPrime)
    (hpos : 1 ≤ n) (x : Expression (F circomPrime)) (hx : Affine x) :
    IsR1CSCirc (assertion (RangeCheck.circuit n hn hpos) x) :=
  IsR1CSCirc.assertion (fun m => isR1CS_implicitRangeCheck n x hx m)

theorem affine_polyEvalExpr {n : ℕ} (coeffs : Vector (Expression (F circomPrime)) n)
    (x : F circomPrime)
    (h : ∀ i (hi : i < n), Affine coeffs[i]) :
    Affine (GroupedFlex.polyEvalExpr coeffs x) := by
  simp only [GroupedFlex.polyEvalExpr]
  refine affine_finFoldl' _ _ Affine.zero fun acc i hacc => ?_
  exact Affine.add hacc (Affine.mul_fconst _ (h i.val i.isLt))

theorem affine_groupExprW (B L : ℕ) (gf posOf : ℕ → ℕ)
    (x : Var (EqViaCarriesFlex.Coeffs L) (F circomPrime))
    (hx : AffineW x) (k : ℕ) :
    Affine (GroupedFlex.groupExprW B L gf posOf x k) := by
  unfold GroupedFlex.groupExprW
  refine affine_polyEvalExpr _ _ fun i hi => ?_
  rw [Vector.getElem_ofFn]
  split
  · rename_i h
    exact hx _ h
  · exact Affine.zero

section GroupedXV
variable {L : ℕ}

theorem costIs_carryLoopXV (B : ℕ) (gf posOf OFFf Wf : ℕ → ℕ)
    (hWok : ∀ k, 1 ≤ Wf k ∧ 2 ^ Wf k < circomPrime)
    [NeZero L]
    (lhs rhs : Var (EqViaCarriesFlex.Coeffs L) (F circomPrime)) :
    ∀ (c k₀ : ℕ),
      CostIs (GroupedFlex.carryLoop B gf posOf OFFf Wf hWok lhs rhs c k₀)
        ⟨GroupedFlex.widthAllocFrom Wf c k₀, GroupedFlex.widthConsFrom Wf c k₀⟩ := by
  intro c
  induction c with
  | zero =>
    intro k₀
    exact CostIs.pure _
  | succ n ih =>
    intro k₀
    rw [show (⟨GroupedFlex.widthAllocFrom Wf (n + 1) k₀,
          GroupedFlex.widthConsFrom Wf (n + 1) k₀⟩ : Count)
        = (⟨Wf k₀ - 1, Wf k₀⟩
            + ⟨GroupedFlex.widthAllocFrom Wf n (k₀ + 1),
               GroupedFlex.widthConsFrom Wf n (k₀ + 1)⟩ : Count) from by
      congr 1 <;>
        simp only [Count.add_allocations, Count.add_constraints,
          GroupedFlex.widthAllocFrom, GroupedFlex.widthConsFrom]]
    exact CostIs.bind
      (costIs_assertion_implicitRangeCheck (Wf k₀) (hWok k₀).2 (hWok k₀).1 _)
      fun _ => ih (k₀ + 1)

theorem costIs_groupedEqXV (B : ℕ) (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedFlex.VParams)
    (hgv : GroupedFlex.GVXHyps circomPrime L B gf posOf G V VR) (hB1 : 1 ≤ B)
    [NeZero L]
    (input : Var (EqViaCarriesFlex.Inputs L) (F circomPrime)) :
    CostIs (GroupedFlex.main B gf posOf G V VR hgv input)
      ⟨GroupedFlex.widthAllocFrom V.Wf (G - 2) 0,
       GroupedFlex.widthConsFrom V.Wf (G - 2) 0 + 1⟩ := by
  rw [show (⟨GroupedFlex.widthAllocFrom V.Wf (G - 2) 0,
        GroupedFlex.widthConsFrom V.Wf (G - 2) 0 + 1⟩ : Count)
      = (⟨GroupedFlex.widthAllocFrom V.Wf (G - 2) 0,
          GroupedFlex.widthConsFrom V.Wf (G - 2) 0⟩ + ⟨0, 1⟩ : Count) from by
    congr 1 <;> simp only [Count.add_allocations, Count.add_constraints]]
  unfold GroupedFlex.main
  refine CostIs.bind (costIs_carryLoopXV B gf posOf VR.OFFf V.Wf hgv.2.2.2.1 _ _ _ _) fun _ => ?_
  exact CostIs.assertZero _

theorem costIs_assertion_groupedEqXV (B : ℕ) (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedFlex.VParams)
    (hgv : GroupedFlex.GVXHyps circomPrime L B gf posOf G V VR) (hB1 : 1 ≤ B)
    [NeZero L]
    (input : Var (EqViaCarriesFlex.Inputs L) (F circomPrime)) :
    CostIs (assertion (GroupedFlex.circuit B gf posOf G V VR hgv hB1) input)
      ⟨GroupedFlex.widthAllocFrom V.Wf (G - 2) 0,
       GroupedFlex.widthConsFrom V.Wf (G - 2) 0 + 1⟩ :=
  CostIs.assertion (fun n => costIs_groupedEqXV B gf posOf G V VR hgv hB1 input n)

theorem affine_carryExprXV [NeZero L] (B : ℕ) (gf posOf OFFf : ℕ → ℕ)
    (lhs rhs : Var (EqViaCarriesFlex.Coeffs L) (F circomPrime))
    (hl : AffineW lhs) (hr : AffineW rhs) :
    ∀ k, Affine (GroupedFlex.carryExpr B gf posOf OFFf lhs rhs k)
  | 0 => by
      unfold GroupedFlex.carryExpr
      exact Affine.add
        (Affine.fconst_mul _
          (Affine.sub (affine_groupExprW B L gf posOf lhs hl 0) (affine_groupExprW B L gf posOf rhs hr 0)))
        (Affine.const _)
  | k + 1 => by
      unfold GroupedFlex.carryExpr
      exact Affine.add
        (Affine.fconst_mul _
          (Affine.sub
            (Affine.add (affine_groupExprW B L gf posOf lhs hl (k + 1))
              (Affine.sub (affine_carryExprXV B gf posOf OFFf lhs rhs hl hr k) (Affine.const _)))
            (affine_groupExprW B L gf posOf rhs hr (k + 1))))
        (Affine.const _)

theorem isR1CS_carryLoopXV (B : ℕ) (gf posOf OFFf Wf : ℕ → ℕ)
    (hWok : ∀ k, 1 ≤ Wf k ∧ 2 ^ Wf k < circomPrime)
    [NeZero L]
    (lhs rhs : Var (EqViaCarriesFlex.Coeffs L) (F circomPrime))
    (hl : AffineW lhs) (hr : AffineW rhs) :
    ∀ (c k₀ : ℕ),
      IsR1CSCirc (GroupedFlex.carryLoop B gf posOf OFFf Wf hWok lhs rhs c k₀) := by
  intro c
  induction c with
  | zero =>
    intro k₀
    exact IsR1CSCirc.pure _
  | succ n ih =>
    intro k₀
    refine IsR1CSCirc.bind
      (isR1CS_assertion_implicitRangeCheck (Wf k₀) (hWok k₀).2 (hWok k₀).1 _
        (affine_carryExprXV B gf posOf OFFf lhs rhs hl hr k₀))
      fun _ => ih (k₀ + 1)

theorem isR1CS_groupedEqXV (B : ℕ) (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedFlex.VParams)
    (hgv : GroupedFlex.GVXHyps circomPrime L B gf posOf G V VR) (hB1 : 1 ≤ B)
    [NeZero L]
    (input : Var (EqViaCarriesFlex.Inputs L) (F circomPrime))
    (hl : AffineW input.lhs) (hr : AffineW input.rhs) :
    IsR1CSCirc (GroupedFlex.main B gf posOf G V VR hgv input) := by
  unfold GroupedFlex.main
  refine IsR1CSCirc.bind (isR1CS_carryLoopXV B gf posOf VR.OFFf V.Wf hgv.2.2.2.1 _ _ hl hr _ _) fun _ => ?_
  refine IsR1CSCirc.assertZero ?_
  refine isR1CSRow_of_affine ?_
  refine affine_polyEvalExpr _ _ fun i hi => ?_
  rw [Vector.getElem_ofFn]
  exact Affine.sub (hl i hi) (hr i hi)

theorem isR1CS_assertion_groupedEqXV (B : ℕ) (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedFlex.VParams)
    (hgv : GroupedFlex.GVXHyps circomPrime L B gf posOf G V VR) (hB1 : 1 ≤ B)
    [NeZero L]
    (input : Var (EqViaCarriesFlex.Inputs L) (F circomPrime))
    (hl : AffineW input.lhs) (hr : AffineW input.rhs) :
    IsR1CSCirc (assertion (GroupedFlex.circuit B gf posOf G V VR hgv hB1) input) :=
  IsR1CSCirc.assertion (fun n => isR1CS_groupedEqXV B gf posOf G V VR hgv hB1 input hl hr n)

end GroupedXV

end Cost

end Solution.Secp256k1ScalarMulFixedBase

end DonorFile1_0

-- Adapted donor module: InterpMul
section DonorFile1_1

namespace Solution.Secp256k1ScalarMulFixedBase

section
variable {p : ℕ} [Fact p.Prime]
variable {m : ℕ} [NeZero m]

namespace MulMod

open GroupedFlex (polyEvalExpr polyEvalExpr_eval)

def interpolatedMul (a b : Var (BigInt m) (F p)) :
    Circuit (F p) (Vector (Expression (F p)) (2 * m - 1)) := do

  let z ← ProvableType.witness (α := fields (2 * m - 1)) fun env =>
    Vector.ofFn fun k : Fin (2 * m - 1) =>
      Expression.eval env.toEnvironment ((bigIntMulNoReduce a b)[k.val])

  let constraints : Vector (Expression (F p)) (2 * m - 1) :=
    Vector.mapFinRange (2 * m - 1) fun cIdx =>
      let c : F p := ((cIdx.val + 1 : ℕ) : F p)
      polyEvalExpr a c * polyEvalExpr b c - polyEvalExpr z c
  Circuit.forEach constraints assertZero
  return z

lemma interpolatedMul_output (off : ℕ) (a b : Var (BigInt m) (F p)) :
    (interpolatedMul a b off).1
      = (Vector.mapRange (2 * m - 1) fun i => var (F := F p) { index := off + i }) := by
  simp only [interpolatedMul, circuit_norm]

lemma interpolatedMul_localLength (off : ℕ) (a b : Var (BigInt m) (F p)) :
    Operations.localLength (interpolatedMul a b off).2 = 2 * m - 1 := by
  simp only [interpolatedMul, circuit_norm, Nat.mul_zero, Nat.add_zero]

def zVec (m off : ℕ) : Vector (Expression (F p)) (2 * m - 1) :=
  Vector.mapRange (2 * m - 1) fun i => var (F := F p) { index := off + i }

lemma interp_points_injective (hpm : 2 * m - 1 < p) :
    Function.Injective (fun cIdx : Fin (2 * m - 1) => (((cIdx.val + 1 : ℕ)) : F p)) := by
  intro i j hij
  simp only at hij
  have hi : i.val + 1 < p := by have := i.isLt; omega
  have hj : j.val + 1 < p := by have := j.isLt; omega
  have := (ZMod.natCast_eq_natCast_iff' _ _ _).mp hij
  rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at this
  exact Fin.ext (by omega)

lemma interpolatedMul_map_eval (env : Environment (F p)) (off : ℕ)
    (a b : Var (BigInt m) (F p)) (hpm : 2 * m - 1 < p)
    (hpts : ∀ cIdx : Fin (2 * m - 1),
      Expression.eval env (polyEvalExpr a ((cIdx.val + 1 : ℕ) : F p))
          * Expression.eval env (polyEvalExpr b ((cIdx.val + 1 : ℕ) : F p))
        = Expression.eval env (polyEvalExpr (zVec m off) ((cIdx.val + 1 : ℕ) : F p))) :
    Vector.map (Expression.eval env) (zVec m off)
      = Vector.map (Expression.eval env) (bigIntMulNoReduce a b) := by
  have hm : 0 < m := Nat.pos_of_neZero m

  set u : Fin (2 * m - 1) → F p := fun k => Expression.eval env (zVec m off)[k.val] with hu
  set v : Fin (2 * m - 1) → F p := fun k => Expression.eval env (bigIntMulNoReduce a b)[k.val] with hv

  have hagree : ∀ cIdx : Fin (2 * m - 1),
      (∑ k : Fin (2 * m - 1), u k * (((cIdx.val + 1 : ℕ)) : F p) ^ k.val)
        = ∑ k : Fin (2 * m - 1), v k * (((cIdx.val + 1 : ℕ)) : F p) ^ k.val := by
    intro cIdx
    set c : F p := (((cIdx.val + 1 : ℕ)) : F p) with hcdef

    have hz : Expression.eval env (polyEvalExpr (zVec m off) c)
        = ∑ k : Fin (2 * m - 1), u k * c ^ k.val := by
      rw [polyEvalExpr_eval]

    have hab : Expression.eval env (polyEvalExpr a c) * Expression.eval env (polyEvalExpr b c)
        = (∑ i : Fin m, Expression.eval env a[i.val] * c ^ i.val)
          * (∑ i : Fin m, Expression.eval env b[i.val] * c ^ i.val) := by
      rw [polyEvalExpr_eval, polyEvalExpr_eval]

    have hcauchy := cauchy_diag hm
      (fun i : Fin m => Expression.eval env a[i.val])
      (fun i : Fin m => Expression.eval env b[i.val]) c
    have hconv : ∀ k : Fin (2 * m - 1),
        (∑ i : Fin m, if hh : i.val ≤ k.val ∧ k.val - i.val < m then
          (fun i : Fin m => Expression.eval env a[i.val]) i
            * (fun i : Fin m => Expression.eval env b[i.val]) ⟨k.val - i.val, hh.2⟩ else 0)
        = v k := by
      intro k
      show _ = Expression.eval env (bigIntMulNoReduce a b)[k.val]
      rw [eval_bigIntMulNoReduce_coeff env a b k]

    have hsound := hpts cIdx
    rw [hz] at hsound
    rw [hab] at hsound
    rw [hcauchy] at hsound

    rw [← hsound]
    apply Finset.sum_congr rfl; intro k _
    rw [hconv k]

  have huniq := interp_uniqueness u v
    (fun cIdx : Fin (2 * m - 1) => (((cIdx.val + 1 : ℕ)) : F p))
    (interp_points_injective hpm) hagree
  apply Vector.ext
  intro k hk
  rw [Vector.getElem_map, Vector.getElem_map]
  exact huniq ⟨k, hk⟩

lemma interpolatedMul_eval_bridge (env : Environment (F p)) (off : ℕ) (a b : Var (BigInt m) (F p))
    (hpm : 2 * m - 1 < p)
    (hpts : ∀ cIdx : Fin (2 * m - 1),
      Expression.eval env (polyEvalExpr a ((cIdx.val + 1 : ℕ) : F p))
          * Expression.eval env (polyEvalExpr b ((cIdx.val + 1 : ℕ) : F p))
        = Expression.eval env (polyEvalExpr (zVec m off) ((cIdx.val + 1 : ℕ) : F p))) :
    ∀ k : Fin (2 * m - 1),
      Expression.eval env (interpolatedMul a b off).1[k.val]
        = Expression.eval env (bigIntMulNoReduce a b)[k.val] := by
  intro k
  rw [interpolatedMul_output off a b]
  have hvec := interpolatedMul_map_eval env off a b hpm hpts
  have := congrArg (fun w => w[k.val]) hvec
  simpa only [zVec, Vector.getElem_map] using this

lemma interpolatedMul_eval_bridge_uses (env : Environment (F p)) (off : ℕ) (a b : Var (BigInt m) (F p))
    (h : ∀ k : Fin (2 * m - 1), env.get (off + k.val)
        = Expression.eval env ((bigIntMulNoReduce a b)[k.val])) :
    ∀ k : Fin (2 * m - 1),
      Expression.eval env (interpolatedMul a b off).1[k.val]
        = Expression.eval env (bigIntMulNoReduce a b)[k.val] := by
  intro k
  rw [interpolatedMul_output off a b]
  rw [Vector.getElem_mapRange]
  show env.get (off + k.val) = _
  exact h k

lemma interpolatedMul_points_of_pins (env : Environment (F p)) (off : ℕ)
    (a b : Var (BigInt m) (F p))
    (h : ∀ k : Fin (2 * m - 1), env.get (off + k.val)
        = Expression.eval env ((bigIntMulNoReduce a b)[k.val])) :
    ∀ cIdx : Fin (2 * m - 1),
      Expression.eval env (polyEvalExpr a ((cIdx.val + 1 : ℕ) : F p))
          * Expression.eval env (polyEvalExpr b ((cIdx.val + 1 : ℕ) : F p))
        = Expression.eval env (polyEvalExpr (zVec m off) ((cIdx.val + 1 : ℕ) : F p)) := by
  intro cIdx
  have hm : 0 < m := Nat.pos_of_neZero m
  set c : F p := ((cIdx.val + 1 : ℕ) : F p) with hcdef
  rw [show Expression.eval env (polyEvalExpr a c)
        = ∑ i : Fin m, Expression.eval env a[i.val] * c ^ i.val from polyEvalExpr_eval _ _ _,
    show Expression.eval env (polyEvalExpr b c)
        = ∑ i : Fin m, Expression.eval env b[i.val] * c ^ i.val from polyEvalExpr_eval _ _ _,
    show Expression.eval env (polyEvalExpr (zVec m off) c)
        = ∑ k : Fin (2 * m - 1), Expression.eval env (zVec m off)[k.val] * c ^ k.val
      from polyEvalExpr_eval _ _ _]
  rw [cauchy_diag hm (fun i : Fin m => Expression.eval env a[i.val])
    (fun i : Fin m => Expression.eval env b[i.val]) c]
  apply Finset.sum_congr rfl; intro k _
  congr 1
  rw [show (∑ i : Fin m, if hh : i.val ≤ k.val ∧ k.val - i.val < m then
        (fun i : Fin m => Expression.eval env a[i.val]) i
          * (fun i : Fin m => Expression.eval env b[i.val]) ⟨k.val - i.val, hh.2⟩ else 0)
      = Expression.eval env (bigIntMulNoReduce a b)[k.val] from by
    rw [eval_bigIntMulNoReduce_coeff env a b k]]
  rw [← h k]
  simp only [zVec, Vector.getElem_mapRange, Expression.eval]

end MulMod

namespace Cost
open Challenge.CostR1CS

theorem affineW_interpolatedMul_output [NeZero m] (a b : Var (BigInt m) (F circomPrime)) (off : ℕ) :
    AffineW ((MulMod.interpolatedMul a b).output off) := by
  rw [show (MulMod.interpolatedMul a b).output off
        = (Vector.mapRange (2 * m - 1) fun i => var (F := F circomPrime) { index := off + i })
      from MulMod.interpolatedMul_output off a b]
  intro k hk
  rw [Vector.getElem_mapRange]; exact Affine.var _

theorem costIs_interpolatedMul [NeZero m] (a b : Var (BigInt m) (F circomPrime)) :
    CostIs (MulMod.interpolatedMul a b) ⟨2 * m - 1, 2 * m - 1⟩ := by
  rw [show (⟨2 * m - 1, 2 * m - 1⟩ : Count)
        = ⟨2 * m - 1, 0⟩ + (⟨(2 * m - 1) * 0, (2 * m - 1) * 1⟩ + Count.zero) from by
      simp only [Count.zero]; congr 1
      simp only [Count.add_constraints]; ring]
  unfold MulMod.interpolatedMul
  refine CostIs.bind (CostIs.provableWitness _) fun z => ?_
  refine CostIs.bind (CostIs.forEach fun a k => CostIs.assertZero _ k) fun _ => ?_
  exact CostIs.pure _

theorem isR1CS_interpolatedMul [NeZero m] (a b : Var (BigInt m) (F circomPrime))
    (ha : AffineW a) (hb : AffineW b) :
    IsR1CSCirc (MulMod.interpolatedMul a b) := by
  unfold MulMod.interpolatedMul
  refine IsR1CSCirc.bind_out (IsR1CSCirc.provableWitness _) fun nz => ?_
  refine IsR1CSCirc.bind ?_ fun _ => ?_
  · refine IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) fun t k => ?_
    refine IsR1CSCirc.assertZero ?_ k
    rw [Vector.getElem_mapFinRange]
    exact isR1CSRow_mul_sub (affine_polyEvalExpr _ _ (fun i hi => ha i hi))
      (affine_polyEvalExpr _ _ (fun i hi => hb i hi))
      (affine_polyEvalExpr _ _ (fun i hi =>
        affineW_provableWitness_bigInt (k := 2 * m - 1) _ nz i hi))
  exact IsR1CSCirc.pure _

end Cost

end

end Solution.Secp256k1ScalarMulFixedBase

end DonorFile1_1

-- Adapted donor module: Select
section DonorFile1_2

namespace Solution.Secp256k1ScalarMulFixedBase
namespace Select


structure AffPoint (F : Type) where
  x : Emu F
  y : Emu F
deriving ProvableStruct


def blockExpr (x y wb : Expression (F circomPrime)) (v : ℕ) :
    Expression (F circomPrime) :=
  if v = 0 then ((1 : F circomPrime) : Expression (F circomPrime)) - x - y + wb
  else if v = 1 then x - wb
  else if v = 2 then y - wb
  else wb


def weightedSum {m : ℕ} (e : Var (fields m) (F circomPrime))
    (coeff : Fin m → F circomPrime) (base : F circomPrime) : Expression (F circomPrime) :=
  (Vector.ofFn fun j : Fin m => e[j.val]'j.isLt * coeff j).foldl (· + ·) 0 + base


end Select
end Solution.Secp256k1ScalarMulFixedBase

end DonorFile1_2

-- Adapted donor module: FlexInstances
section DonorFile1_3

namespace Solution.Secp256k1ScalarMulFixedBase

def linFlex : EqViaCarriesFlex.FlexParams circomPrime 5 where
  B := 64
  W := 5
  M := #v[2^67, 2^67, 2^67, 2^67, 2^4]
  hB := by decide
  hW := by decide
  hB1 := by decide
  hW1 := by decide
  hcarry := by decide
  hlift := by decide

def quadFlex : EqViaCarriesFlex.FlexParams circomPrime 9 where
  B := 64
  W := 69
  M := #v[5*2^128, 5*2^128, 5*2^128, 5*2^128, 5*2^128, 5*2^128, 5*2^128,
          5*2^128, 5*2^128]
  hB := by decide
  hW := by decide
  hB1 := by decide
  hW1 := by decide
  hcarry := by decide
  hlift := by decide

def wideFlex : EqViaCarriesFlex.FlexParams circomPrime 10 where
  B := 64
  W := 69
  M := #v[13*2^128, 13*2^128, 13*2^128, 13*2^128, 13*2^128, 13*2^128, 13*2^128,
          13*2^128, 13*2^128, 13*2^128]
  hB := by decide
  hW := by decide
  hB1 := by decide
  hW1 := by decide
  hcarry := by decide
  hlift := by decide

end Solution.Secp256k1ScalarMulFixedBase

end DonorFile1_3

-- Adapted donor module: EqViaCarriesFlexT
section DonorFile1_4

namespace Solution.Secp256k1ScalarMulFixedBase
open Solution.Secp256k1ScalarMulFixedBase.Limbs
open EqViaCarriesFlex (boundAt Inputs Coeffs)

section
variable {p : ℕ} [Fact p.Prime]
variable {n : ℕ} [NeZero n]

namespace EqViaCarriesFlexT

def Wat (s W1 W2 k : ℕ) : ℕ := if k < s then W1 else W2

def OFFat (s W1 W2 k : ℕ) : ℕ := 2 ^ (Wat s W1 W2 k - 1)

structure FlexParamsT (p n : ℕ) where

  B : ℕ

  s : ℕ

  W1 : ℕ

  W2 : ℕ

  M : Vector ℕ n

  hs1 : 1 ≤ s

  hsn : s < n

  hB : 2 ^ B < p

  hW1p : 2 ^ W1 < p

  hW2p : 2 ^ W2 < p

  hB1 : 1 ≤ B

  hW11 : 1 ≤ W1

  hW21 : 1 ≤ W2

  hcarry : ∀ k : Fin n,
    (∑ j ∈ Finset.range (k.val + 1), boundAt M j * 2 ^ (B * j))
      ≤ 2 ^ (Wat s W1 W2 k.val - 1) * 2 ^ (B * (k.val + 1))

  hlift : ∀ k : Fin n,
    boundAt M k.val + 2 ^ max W1 W2 + 2 ^ max W1 W2 * 2 ^ B < p

def main (P : FlexParamsT p n) [Fact (p > 2)] (input : Var (Inputs n) (F p)) :
    Circuit (F p) Unit := do
  let Pc := input.lhs
  let Sc := input.rhs

  let carry1 ← witnessVector P.s fun env =>
    Vector.ofFn fun k : Fin P.s =>
      ((2 ^ (P.W1 - 1) + evalPartial P.B env Pc k.val / 2 ^ (P.B * (k.val + 1))
          - evalPartial P.B env Sc k.val / 2 ^ (P.B * (k.val + 1)) : ℕ) : F p)
  let carry2 ← witnessVector (n - P.s) fun env =>
    Vector.ofFn fun k : Fin (n - P.s) =>
      ((2 ^ (P.W2 - 1)
          + evalPartial P.B env Pc (P.s + k.val) / 2 ^ (P.B * (P.s + k.val + 1))
          - evalPartial P.B env Sc (P.s + k.val) / 2 ^ (P.B * (P.s + k.val + 1)) : ℕ)
        : F p)

  Circuit.forEach carry1 (fun c => Gadgets.ToBits.rangeCheck P.W1 P.hW1p c)
  Circuit.forEach carry2 (fun c => Gadgets.ToBits.rangeCheck P.W2 P.hW2p c)

  let constraints : Vector (Expression (F p)) n :=
    Vector.mapFinRange n fun k =>
      let cOut : Expression (F p) :=
        if h : k.val < P.s then carry1[k.val]
        else carry2[k.val - P.s]'(by have := k.isLt; omega)
      let carryIn : Expression (F p) :=
        if h : k.val = 0 then 0
        else (if h2 : k.val - 1 < P.s then carry1[k.val - 1]
              else carry2[k.val - 1 - P.s]'(by have := k.isLt; omega))
          - ((OFFat P.s P.W1 P.W2 (k.val - 1) : ℕ) : F p)
      Pc[k.val] + carryIn - Sc[k.val]
        - (cOut - ((OFFat P.s P.W1 P.W2 k.val : ℕ) : F p)) * (2 ^ P.B : F p)
  Circuit.forEach constraints assertZero

  assertZero ((carry2[n - 1 - P.s]'(by have := P.hsn; omega))
    - ((2 ^ (P.W2 - 1) : ℕ) : F p))

instance elaborated (P : FlexParamsT p n) [Fact (p > 2)] :
    ElaboratedCircuit (F p) (Inputs n) unit (main P) where
  localLength _ := n + P.s * P.W1 + (n - P.s) * P.W2
  localLength_eq := by
    intro input offset
    have hs := P.hsn
    simp only [main, circuit_norm, Gadgets.ToBits.rangeCheck]
    simp +arith [circuit_norm]
    omega
  subcircuitsConsistent := by
    intro input offset
    simp +arith only [main, circuit_norm, Gadgets.ToBits.rangeCheck]
  channelsLawful := by
    intro offset
    simp only [main, circuit_norm, Gadgets.ToBits.rangeCheck]

def Assumptions (P : FlexParamsT p n) (input : Inputs n (F p)) : Prop :=
  (∀ k : Fin n, (input.lhs[k.val]).val < boundAt P.M k.val) ∧
  (∀ k : Fin n, (input.rhs[k.val]).val < boundAt P.M k.val)

private lemma flex_div_bound (B : ℕ) (Mf f : ℕ → ℕ) (k : ℕ)
    (hf : ∀ j, j ≤ k → f j < Mf j) (OFF : ℕ) (hOFF : 1 ≤ OFF)
    (hsum : (∑ j ∈ Finset.range (k + 1), Mf j * 2 ^ (B * j))
      ≤ OFF * 2 ^ (B * (k + 1))) :
    (∑ j ∈ Finset.range (k + 1), f j * 2 ^ (B * j)) / 2 ^ (B * (k + 1))
      ≤ OFF - 1 := by
  have hlt : (∑ j ∈ Finset.range (k + 1), f j * 2 ^ (B * j))
      < ∑ j ∈ Finset.range (k + 1), Mf j * 2 ^ (B * j) := by
    apply Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.mpr (by omega))
    intro j hj
    rw [Finset.mem_range] at hj
    exact (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).mpr (hf j (by omega))
  have hdiv : (∑ j ∈ Finset.range (k + 1), f j * 2 ^ (B * j)) / 2 ^ (B * (k + 1))
      < OFF := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
    calc (∑ j ∈ Finset.range (k + 1), f j * 2 ^ (B * j))
        < ∑ j ∈ Finset.range (k + 1), Mf j * 2 ^ (B * j) := hlt
      _ ≤ OFF * 2 ^ (B * (k + 1)) := hsum
  omega

lemma per_index_lift2 {B : ℕ} (a cinF b c offI offO : F p) (cinN offIN offON : ℕ)
    (hcin : cinF.val = cinN) (hoffI : offI.val = offIN)
    (hoffO : offO.val = offON)
    (hlhs : a.val + cinN + offON * 2 ^ B < p)
    (hrhs : b.val + c.val * 2 ^ B + offIN < p)
    (heq : a + cinF + offO * (2 ^ B : F p) = b + c * (2 ^ B : F p) + offI) :
    a.val + cinN + offON * 2 ^ B = b.val + c.val * 2 ^ B + offIN := by
  have hpow_val_cast : ((2 ^ B : ℕ) : F p) = (2 ^ B : F p) := by push_cast; ring
  have hoffIcast : ((offIN : ℕ) : F p) = offI := by rw [← hoffI, ZMod.natCast_zmod_val]
  have hoffOcast : ((offON : ℕ) : F p) = offO := by rw [← hoffO, ZMod.natCast_zmod_val]
  have hcincast : ((cinN : ℕ) : F p) = cinF := by rw [← hcin, ZMod.natCast_zmod_val]
  have hacast : ((a.val : ℕ) : F p) = a := ZMod.natCast_zmod_val a
  have hbcast : ((b.val : ℕ) : F p) = b := ZMod.natCast_zmod_val b
  have hccast : ((c.val : ℕ) : F p) = c := ZMod.natCast_zmod_val c
  have hlhs_cast : a + cinF + offO * (2 ^ B : F p)
      = ((a.val + cinN + offON * 2 ^ B : ℕ) : F p) := by
    push_cast [hacast, hcincast, hoffOcast, hpow_val_cast]; ring
  have hlhs_val : (a + cinF + offO * (2 ^ B : F p)).val
      = a.val + cinN + offON * 2 ^ B := by
    rw [hlhs_cast, ZMod.val_natCast_of_lt hlhs]
  have hrhs_cast : b + c * (2 ^ B : F p) + offI
      = ((b.val + c.val * 2 ^ B + offIN : ℕ) : F p) := by
    push_cast [hbcast, hccast, hoffIcast, hpow_val_cast]; ring
  have hrhs_val : (b + c * (2 ^ B : F p) + offI).val
      = b.val + c.val * 2 ^ B + offIN := by
    rw [hrhs_cast, ZMod.val_natCast_of_lt hrhs]
  have := congrArg ZMod.val heq
  rw [hlhs_val, hrhs_val] at this
  exact this

def circuit (P : FlexParamsT p n) [Fact (p > 2)] : FormalAssertion (F p) (Inputs n) where
    main := main P
    Assumptions := Assumptions P
    Spec := EqViaCarriesFlex.Spec P.B
    soundness := by
      obtain ⟨B, s, W1, W2, M, hs1, hsn, hB, hW1p, hW2p, hB1, hW11, hW21,
        hcarry, hlift⟩ := P
      circuit_proof_start
      simp only [circuit_norm, Gadgets.ToBits.rangeCheck] at h_holds ⊢
      obtain ⟨h_range1, h_range2, h_lin, h_top⟩ := h_holds
      have hM : 0 < n := Nat.pos_of_neZero n

      set Wf : ℕ → ℕ := fun k => Wat s W1 W2 k with hWf
      set OFFf : ℕ → ℕ := fun k => OFFat s W1 W2 k with hOFFf
      have hWf1 : ∀ k, 1 ≤ Wf k := by
        intro k; simp only [hWf, Wat]; split <;> omega
      have hOFF_pow : ∀ k, OFFf k = 2 ^ (Wf k - 1) := fun k => rfl
      have hOFF_x2 : ∀ k, OFFf k * 2 = 2 ^ Wf k := by
        intro k
        rw [hOFF_pow, ← pow_succ]
        congr 1; have := hWf1 k; omega
      have hWf_le_max : ∀ k, Wf k ≤ max W1 W2 := by
        intro k; simp only [hWf, Wat]; split
        · exact le_max_left _ _
        · exact le_max_right _ _
      have hOFF_le_max : ∀ k, OFFf k ≤ 2 ^ max W1 W2 := by
        intro k
        calc OFFf k = 2 ^ (Wf k - 1) := hOFF_pow k
          _ ≤ 2 ^ Wf k := Nat.pow_le_pow_right (by norm_num) (by omega)
          _ ≤ 2 ^ max W1 W2 := Nat.pow_le_pow_right (by norm_num) (hWf_le_max k)
      have h2Wf_le_max : ∀ k, 2 ^ Wf k ≤ 2 ^ max W1 W2 :=
        fun k => Nat.pow_le_pow_right (by norm_num) (hWf_le_max k)
      have h2Wf_lt_p : ∀ k, 2 ^ Wf k < p := by
        intro k; simp only [hWf, Wat]; split
        · exact hW1p
        · exact hW2p
      have hOFF_lt_p : ∀ k, OFFf k < p := by
        intro k
        have h1 := hOFF_x2 k; have h2 := h2Wf_lt_p k; omega
      have hOFF_pos : ∀ k, 1 ≤ OFFf k := by
        intro k; rw [hOFF_pow]; exact Nat.one_le_two_pow
      have hOFF_cast : ∀ k, ((OFFf k : ℕ) : F p).val = OFFf k :=
        fun k => ZMod.val_natCast_of_lt (hOFF_lt_p k)
      have hpB : 2 ^ B < p := hB

      set Pn : ℕ → ℕ := fun k => if h : k < n then (input.lhs[k]'h).val else 0 with hPn
      set Sn : ℕ → ℕ := fun k => if h : k < n then (input.rhs[k]'h).val else 0 with hSn
      set Cn : ℕ → ℕ := fun k => (env.get (i₀ + k)).val with hCn

      have hCn_lt : ∀ k, k < n → Cn k < 2 ^ Wf k := by
        intro k hk
        simp only [hCn, hWf, Wat]
        split
        · rename_i hks; exact h_range1 ⟨k, hks⟩
        · rename_i hks
          have hcell : i₀ + s + (k - s) = i₀ + k := by omega
          have := h_range2 ⟨k - s, by omega⟩
          simpa [hcell] using this
      have hPn_lt : ∀ k, (hk : k < n) → Pn k < boundAt M k := by
        intro k hk; simp only [hPn, dif_pos hk]; exact h_assumptions.1 ⟨k, hk⟩
      have hSn_lt : ∀ k, (hk : k < n) → Sn k < boundAt M k := by
        intro k hk; simp only [hSn, dif_pos hk]; exact h_assumptions.2 ⟨k, hk⟩

      have hCtop : Cn (n - 1) = OFFf (n - 1) := by
        have hcell : i₀ + s + (n - 1 - s) = i₀ + (n - 1) := by omega
        have htv : env.get (i₀ + (n - 1)) = ((2 ^ (W2 - 1) : ℕ) : F p) := by
          rw [← hcell, ← sub_eq_zero]
          rw [show env.get (i₀ + s + (n - 1 - s)) - ((2 ^ (W2 - 1) : ℕ) : F p)
            = env.get (i₀ + s + (n - 1 - s)) + -((2 ^ (W2 - 1) : ℕ) : F p) by ring]
          exact h_top
        have hOFFtop : OFFf (n - 1) = 2 ^ (W2 - 1) := by
          simp only [hOFFf, OFFat, Wat, if_neg (by omega : ¬ (n - 1 < s))]
        simp only [hCn, htv, hOFFtop]
        have hlt : (2 : ℕ) ^ (W2 - 1) < p := by
          have := hOFF_lt_p (n - 1); rwa [hOFFtop] at this
        exact ZMod.val_natCast_of_lt hlt

      have hcell_e : ∀ j, j < n →
          Expression.eval env
            (if h : j < s then (var { index := i₀ + j } : Expression (F p))
             else var { index := i₀ + s + (j - s) })
            = env.get (i₀ + j) := by
        intro j hj
        split
        · simp [circuit_norm]
        · rename_i hjs
          have hcell : i₀ + s + (j - s) = i₀ + j := by omega
          simp [circuit_norm, hcell]

      have h_idx : ∀ k, (hk : k < n) →
          Pn k + (if k = 0 then OFFf 0 else Cn (k - 1)) + OFFf k * 2 ^ B
            = Sn k + Cn k * 2 ^ B + (if k = 0 then OFFf 0 else OFFf (k - 1)) := by
        intro k hk
        have hlin := h_lin ⟨k, hk⟩
        have ha_e : Expression.eval env input_var.lhs[(⟨k, hk⟩ : Fin n).val] = input.lhs[k]'hk := by
          rw [← h_input]; simp [Vector.getElem_map]
        have hb_e : Expression.eval env input_var.rhs[(⟨k, hk⟩ : Fin n).val] = input.rhs[k]'hk := by
          rw [← h_input]; simp [Vector.getElem_map]
        have hcin_e : Expression.eval env
            (if h : (⟨k, hk⟩ : Fin n).val = 0 then 0
              else (if h2 : (⟨k, hk⟩ : Fin n).val - 1 < s
                    then (var { index := i₀ + ((⟨k, hk⟩ : Fin n).val - 1) } : Expression (F p))
                    else var { index := i₀ + s + ((⟨k, hk⟩ : Fin n).val - 1 - s) })
                - Expression.const ((OFFat s W1 W2 ((⟨k, hk⟩ : Fin n).val - 1) : ℕ) : F p))
            = if k = 0 then 0
              else env.get (i₀ + (k - 1)) - ((OFFf (k - 1) : ℕ) : F p) := by
          simp only []
          split
          · simp [circuit_norm]
          · rename_i hk0
            have := hcell_e (k - 1) (by omega)
            simp only [circuit_norm, sub_eq_add_neg, hOFFf]
            rw [show Expression.eval env
                (if h2 : k - 1 < s then (var { index := i₀ + (k - 1) } : Expression (F p))
                 else var { index := i₀ + s + (k - 1 - s) }) = env.get (i₀ + (k - 1)) from this]
        have hcout_e : Expression.eval env
            (if h : (⟨k, hk⟩ : Fin n).val < s
             then (var { index := i₀ + (⟨k, hk⟩ : Fin n).val } : Expression (F p))
             else var { index := i₀ + s + ((⟨k, hk⟩ : Fin n).val - s) })
            = env.get (i₀ + k) := hcell_e k hk
        simp only [ha_e, hb_e, hcin_e, hcout_e] at hlin

        have hfield : (input.lhs[k]'hk)
              + (if k = 0 then ((OFFf 0 : ℕ) : F p) else env.get (i₀ + (k - 1)))
              + ((OFFf k : ℕ) : F p) * (2 ^ B : F p)
            = (input.rhs[k]'hk) + env.get (i₀ + k) * (2 ^ B : F p)
              + (if k = 0 then ((OFFf 0 : ℕ) : F p) else ((OFFf (k - 1) : ℕ) : F p)) := by
          rcases Nat.eq_zero_or_pos k with hk0 | hk0
          · subst hk0
            simp only [↓reduceIte] at hlin ⊢
            rw [← sub_eq_zero]
            rw [← hlin]; simp only [hOFFf]; ring
          · simp only [if_neg (show ¬ k = 0 from by omega)] at hlin ⊢
            rw [← sub_eq_zero]
            rw [← hlin]; simp only [hOFFf]; ring

        have hcin_val : (if k = 0 then ((OFFf 0 : ℕ) : F p) else env.get (i₀ + (k - 1))).val
            = if k = 0 then OFFf 0 else Cn (k - 1) := by
          split
          · exact hOFF_cast 0
          · simp [hCn]
        have hoffI_val : (if k = 0 then ((OFFf 0 : ℕ) : F p) else ((OFFf (k - 1) : ℕ) : F p)).val
            = if k = 0 then OFFf 0 else OFFf (k - 1) := by
          split
          · exact hOFF_cast 0
          · exact hOFF_cast (k - 1)
        have hcin_le : (if k = 0 then OFFf 0 else Cn (k - 1)) ≤ 2 ^ max W1 W2 := by
          split
          · exact hOFF_le_max 0
          · rename_i hkne
            have h1 := hCn_lt (k - 1) (by omega)
            have h2 := h2Wf_le_max (k - 1)
            omega
        have hoffI_le : (if k = 0 then OFFf 0 else OFFf (k - 1)) ≤ 2 ^ max W1 W2 := by
          split
          · exact hOFF_le_max 0
          · exact hOFF_le_max (k - 1)
        have hliftk : boundAt M k + 2 ^ max W1 W2 + 2 ^ max W1 W2 * 2 ^ B < p := hlift ⟨k, hk⟩
        have hlhs : (input.lhs[k]'hk).val + (if k = 0 then OFFf 0 else Cn (k - 1))
            + OFFf k * 2 ^ B < p := by
          have hp1 := hPn_lt k hk
          simp only [hPn, dif_pos hk] at hp1
          have hOB : OFFf k * 2 ^ B ≤ 2 ^ max W1 W2 * 2 ^ B :=
            Nat.mul_le_mul_right _ (hOFF_le_max k)
          generalize hX : OFFf k * 2 ^ B = X at hOB ⊢
          generalize hY : 2 ^ max W1 W2 * 2 ^ B = Y at hOB hliftk
          omega
        have hrhs : (input.rhs[k]'hk).val + (env.get (i₀ + k)).val * 2 ^ B
            + (if k = 0 then OFFf 0 else OFFf (k - 1)) < p := by
          have hp2 := hSn_lt k hk
          simp only [hSn, dif_pos hk] at hp2
          have hc : (env.get (i₀ + k)).val < 2 ^ Wf k := hCn_lt k hk
          have hcB : (env.get (i₀ + k)).val * 2 ^ B ≤ 2 ^ max W1 W2 * 2 ^ B := by
            apply Nat.mul_le_mul_right
            have := h2Wf_le_max k; omega
          generalize hZ : (env.get (i₀ + k)).val * 2 ^ B = Z at hcB ⊢
          generalize hY : 2 ^ max W1 W2 * 2 ^ B = Y at hcB hliftk
          omega
        have hlift' := per_index_lift2 (B := B) (input.lhs[k]'hk)
          (if k = 0 then ((OFFf 0 : ℕ) : F p) else env.get (i₀ + (k - 1)))
          (input.rhs[k]'hk) (env.get (i₀ + k))
          (if k = 0 then ((OFFf 0 : ℕ) : F p) else ((OFFf (k - 1) : ℕ) : F p))
          ((OFFf k : ℕ) : F p)
          (if k = 0 then OFFf 0 else Cn (k - 1))
          (if k = 0 then OFFf 0 else OFFf (k - 1)) (OFFf k)
          hcin_val hoffI_val (hOFF_cast k) hlhs hrhs hfield
        simp only [hPn, hSn, hCn, dif_pos hk] at hlift' ⊢
        convert hlift' using 2

      have hpv1 : polyValue B input.lhs = ∑ k ∈ Finset.range n, Pn k * 2 ^ (B * k) := by
        rw [polyValue, ← Fin.sum_univ_eq_sum_range (fun k => Pn k * 2 ^ (B * k))]
        apply Finset.sum_congr rfl
        intro i _; simp only [hPn, dif_pos i.isLt]
      have hpv2 : polyValue B input.rhs = ∑ k ∈ Finset.range n, Sn k * 2 ^ (B * k) := by
        rw [polyValue, ← Fin.sum_univ_eq_sum_range (fun k => Sn k * 2 ^ (B * k))]
        apply Finset.sum_congr rfl
        intro i _; simp only [hSn, dif_pos i.isLt]
      show polyValue B input.lhs = polyValue B input.rhs
      rw [hpv1, hpv2]

      have hsum : (∑ k ∈ Finset.range n,
            ((Pn k + (if k = 0 then OFFf 0 else Cn (k - 1))) + OFFf k * 2 ^ B) * 2 ^ (B * k))
          = ∑ k ∈ Finset.range n,
            (Sn k + Cn k * 2 ^ B + (if k = 0 then OFFf 0 else OFFf (k - 1))) * 2 ^ (B * k) := by
        apply Finset.sum_congr rfl
        intro k hk; rw [Finset.mem_range] at hk
        rw [show Pn k + (if k = 0 then OFFf 0 else Cn (k - 1)) + OFFf k * 2 ^ B
              = Pn k + (if k = 0 then OFFf 0 else Cn (k - 1)) + OFFf k * 2 ^ B from rfl,
          h_idx k hk]

      set SP := ∑ k ∈ Finset.range n, Pn k * 2 ^ (B * k) with hSP
      set SS := ∑ k ∈ Finset.range n, Sn k * 2 ^ (B * k) with hSS
      set SC := ∑ k ∈ Finset.range n, Cn k * 2 ^ (B * (k + 1)) with hSC
      set SO := ∑ k ∈ Finset.range n, OFFf k * 2 ^ (B * (k + 1)) with hSO
      set SCin := ∑ k ∈ Finset.range n,
        (if k = 0 then 0 else Cn (k - 1)) * 2 ^ (B * k) with hSCin
      set SOin := ∑ k ∈ Finset.range n,
        (if k = 0 then 0 else OFFf (k - 1)) * 2 ^ (B * k) with hSOin

      have hSCin_rel : (∑ k ∈ Finset.range n,
            (if k = 0 then OFFf 0 else Cn (k - 1)) * 2 ^ (B * k)) = SCin + OFFf 0 := by
        rw [hSCin, show n = (n - 1) + 1 from by omega]
        rw [Finset.sum_range_succ' _ (n - 1), Finset.sum_range_succ' _ (n - 1)]
        simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte,
          Nat.mul_zero, pow_zero, Nat.mul_one]
        ring
      have hSOin_rel : (∑ k ∈ Finset.range n,
            (if k = 0 then OFFf 0 else OFFf (k - 1)) * 2 ^ (B * k)) = SOin + OFFf 0 := by
        rw [hSOin, show n = (n - 1) + 1 from by omega]
        rw [Finset.sum_range_succ' _ (n - 1), Finset.sum_range_succ' _ (n - 1)]
        simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte,
          Nat.mul_zero, pow_zero, Nat.mul_one]
        ring

      have hLHS : (∑ k ∈ Finset.range n,
            ((Pn k + (if k = 0 then OFFf 0 else Cn (k - 1))) + OFFf k * 2 ^ B) * 2 ^ (B * k))
          = SP + (SCin + OFFf 0) + SO := by
        rw [← hSCin_rel, hSP, hSO, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _
        rw [Nat.mul_add B k 1, Nat.mul_one, pow_add]; ring

      have hRHS : (∑ k ∈ Finset.range n,
            (Sn k + Cn k * 2 ^ B + (if k = 0 then OFFf 0 else OFFf (k - 1))) * 2 ^ (B * k))
          = SS + SC + (SOin + OFFf 0) := by
        rw [← hSOin_rel, hSS, hSC, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _
        rw [Nat.mul_add B k 1, Nat.mul_one, pow_add]; ring
      rw [hLHS, hRHS] at hsum

      have htelC := carry_telescope B Cn n
      rw [if_neg (by omega : ¬ (n = 0)), ← hSCin, ← hSC] at htelC
      have htelO := carry_telescope B OFFf n
      rw [if_neg (by omega : ¬ (n = 0)), ← hSOin, ← hSO] at htelO

      have htop_eq : Cn (n - 1) * 2 ^ (B * n) = OFFf (n - 1) * 2 ^ (B * n) := by
        rw [hCtop]
      omega
    completeness := by
      obtain ⟨B, s, W1, W2, M, hs1, hsn, hB, hW1p, hW2p, hB1, hW11, hW21,
        hcarry, hlift⟩ := P
      circuit_proof_start
      simp only [circuit_norm, Gadgets.ToBits.rangeCheck] at h_env ⊢
      obtain ⟨h_wit1, h_wit2, _, _⟩ := h_env
      have hM : 0 < n := Nat.pos_of_neZero n

      set Wf : ℕ → ℕ := fun k => Wat s W1 W2 k with hWf
      set OFFf : ℕ → ℕ := fun k => OFFat s W1 W2 k with hOFFf
      have hWf1 : ∀ k, 1 ≤ Wf k := by
        intro k; simp only [hWf, Wat]; split <;> omega
      have hOFF_pow : ∀ k, OFFf k = 2 ^ (Wf k - 1) := fun k => rfl
      have hOFF_x2 : ∀ k, OFFf k * 2 = 2 ^ Wf k := by
        intro k
        rw [hOFF_pow, ← pow_succ]
        congr 1; have := hWf1 k; omega
      have h2Wf_lt_p : ∀ k, 2 ^ Wf k < p := by
        intro k; simp only [hWf, Wat]; split
        · exact hW1p
        · exact hW2p
      have hOFF_lt_p : ∀ k, OFFf k < p := by
        intro k
        have h1 := hOFF_x2 k; have h2 := h2Wf_lt_p k; omega
      have hOFF_pos : ∀ k, 1 ≤ OFFf k := by
        intro k; rw [hOFF_pow]; exact Nat.one_le_two_pow

      set Pn : ℕ → ℕ := fun k => if h : k < n then (input.lhs[k]'h).val else 0 with hPn
      set Sn : ℕ → ℕ := fun k => if h : k < n then (input.rhs[k]'h).val else 0 with hSn
      have hPn_lt : ∀ k, k < n → Pn k < boundAt M k := by
        intro k hk; simp only [hPn, dif_pos hk]; exact h_assumptions.1 ⟨k, hk⟩
      have hSn_lt : ∀ k, k < n → Sn k < boundAt M k := by
        intro k hk; simp only [hSn, dif_pos hk]; exact h_assumptions.2 ⟨k, hk⟩

      set PFn : ℕ → ℕ := fun k => ∑ j ∈ Finset.range (k + 1), Pn j * 2 ^ (B * j) with hPFn
      set PSn : ℕ → ℕ := fun k => ∑ j ∈ Finset.range (k + 1), Sn j * 2 ^ (B * j) with hPSn
      have hPFn_eq : ∀ k, evalPartial B env input_var.lhs k = PFn k := by
        intro k; simp only [evalPartial, hPFn]
        apply Finset.sum_congr rfl
        intro j _; congr 1
        simp only [hPn]; split
        · rename_i h; rw [← h_input]; simp [Vector.getElem_map]
        · rfl
      have hPSn_eq : ∀ k, evalPartial B env input_var.rhs k = PSn k := by
        intro k; simp only [evalPartial, hPSn]
        apply Finset.sum_congr rfl
        intro j _; congr 1
        simp only [hSn]; split
        · rename_i h; rw [← h_input]; simp [Vector.getElem_map]
        · rfl

      set Dk : ℕ → ℕ := fun k => 2 ^ (B * (k + 1)) with hDk
      set Cn : ℕ → ℕ := fun k => OFFf k + PFn k / Dk k - PSn k / Dk k with hCn
      have hDk_app : ∀ k, Dk k = 2 ^ (B * (k + 1)) := fun k => rfl
      have hPFn_app : ∀ k, PFn k = ∑ j ∈ Finset.range (k + 1), Pn j * 2 ^ (B * j) := fun k => rfl
      have hPSn_app : ∀ k, PSn k = ∑ j ∈ Finset.range (k + 1), Sn j * 2 ^ (B * j) := fun k => rfl
      have hCn_app : ∀ k, Cn k = OFFf k + PFn k / Dk k - PSn k / Dk k := fun k => rfl

      have hOFF_tier1 : ∀ k, k < s → OFFf k = 2 ^ (W1 - 1) := by
        intro k hk; simp only [hOFFf, OFFat, Wat, if_pos hk]
      have hOFF_tier2 : ∀ k, ¬ (k < s) → OFFf k = 2 ^ (W2 - 1) := by
        intro k hk; simp only [hOFFf, OFFat, Wat, if_neg hk]
      have hwit_eq : ∀ k, k < n → env.get (i₀ + k) = (Cn k : F p) := by
        intro k hk
        by_cases hks : k < s
        · rw [h_wit1 ⟨k, hks⟩]
          simp only [Vector.getElem_ofFn, hCn_app, hDk_app, hPFn_eq, hPSn_eq,
            hOFF_tier1 k hks]
        · have hcell : i₀ + s + (k - s) = i₀ + k := by omega
          have hpin := h_wit2 ⟨k - s, by omega⟩
          rw [hcell] at hpin
          rw [hpin]
          have hks' : s + (k - s) = k := by omega
          simp only [Vector.getElem_ofFn, hCn_app, hDk_app, hPFn_eq, hPSn_eq,
            hOFF_tier2 k hks, hks']

      have hMbound : ∀ k, (hk : k < n) →
          (∑ j ∈ Finset.range (k + 1), boundAt M j * 2 ^ (B * j))
            ≤ OFFf k * 2 ^ (B * (k + 1)) := by
        intro k hk; exact hcarry ⟨k, hk⟩
      have hPFdiv : ∀ k, (hk : k < n) → PFn k / Dk k ≤ OFFf k - 1 := by
        intro k hk
        rw [hPFn_app, hDk_app]
        exact flex_div_bound B (boundAt M) Pn k
          (fun j hj => hPn_lt j (by omega)) (OFFf k) (hOFF_pos k) (hMbound k hk)
      have hPSdiv : ∀ k, (hk : k < n) → PSn k / Dk k ≤ OFFf k - 1 := by
        intro k hk
        rw [hPSn_app, hDk_app]
        exact flex_div_bound B (boundAt M) Sn k
          (fun j hj => hSn_lt j (by omega)) (OFFf k) (hOFF_pos k) (hMbound k hk)

      have hrange : ∀ k, (hk : k < n) → Cn k < 2 ^ Wf k := by
        intro k hk
        have h1 := hPFdiv k hk
        have h2 := hOFF_x2 k
        have h3 := hOFF_pos k
        have hCk : Cn k = OFFf k + PFn k / Dk k - PSn k / Dk k := hCn_app k
        generalize hgq : PFn k / Dk k = q at h1 hCk
        generalize hgo : PSn k / Dk k = o at hCk
        generalize hgX : OFFf k = X at h1 h2 h3 hCk
        generalize hgY : (2 : ℕ) ^ Wf k = Y at h2 ⊢
        omega
      have hpB : 2 ^ B < p := hB
      have hOFF_cast : ∀ k, ((OFFf k : ℕ) : F p).val = OFFf k :=
        fun k => ZMod.val_natCast_of_lt (hOFF_lt_p k)

      have hPFn_top : PFn (n - 1) = polyValue B input.lhs := by
        rw [hPFn_app, polyValue, ← Fin.sum_univ_eq_sum_range (fun j => Pn j * 2 ^ (B * j)),
          show n - 1 + 1 = n from by omega]
        apply Finset.sum_congr rfl (fun i _ => ?_)
        simp only [hPn, dif_pos i.isLt]
      have hPSn_top : PSn (n - 1) = polyValue B input.rhs := by
        rw [hPSn_app, polyValue, ← Fin.sum_univ_eq_sum_range (fun j => Sn j * 2 ^ (B * j)),
          show n - 1 + 1 = n from by omega]
        apply Finset.sum_congr rfl (fun i _ => ?_)
        simp only [hSn, dif_pos i.isLt]
      have hPtop_eq : PFn (n - 1) = PSn (n - 1) := by
        rw [hPFn_top, hPSn_top]; exact h_spec
      have hmod : ∀ k, k < n → PFn k % Dk k = PSn k % Dk k := by
        intro k hk
        have e1 : PFn (n - 1) % Dk k = PFn k % Dk k := by
          rw [hPFn_app, hPFn_app, hDk_app, show n - 1 + 1 = n from by omega]
          exact partial_mod_stable B Pn n k hk
        have e2 : PSn (n - 1) % Dk k = PSn k % Dk k := by
          rw [hPSn_app, hPSn_app, hDk_app, show n - 1 + 1 = n from by omega]
          exact partial_mod_stable B Sn n k hk
        rw [← e1, ← e2, hPtop_eq]

      have hCtop : Cn (n - 1) = OFFf (n - 1) := by
        rw [hCn_app, hPtop_eq]; omega

      have hidx : ∀ k, k < n →
          Pn k + (if k = 0 then OFFf 0 else Cn (k - 1)) + OFFf k * 2 ^ B
            = Sn k + Cn k * 2 ^ B + (if k = 0 then OFFf 0 else OFFf (k - 1)) := by
        intro k hk
        set qP := PFn k / 2 ^ (B * k) with hqP_def
        set qS := PSn k / 2 ^ (B * k) with hqS_def
        set rP := PFn k / Dk k with hrP_def
        set rS := PSn k / Dk k with hrS_def
        have hrP_quot : rP = qP / 2 ^ B := by
          rw [hrP_def, hqP_def, hDk_app, show B * (k + 1) = B * k + B by ring, pow_add,
            Nat.div_div_eq_div_mul]
        have hrS_quot : rS = qS / 2 ^ B := by
          rw [hrS_def, hqS_def, hDk_app, show B * (k + 1) = B * k + B by ring, pow_add,
            Nat.div_div_eq_div_mul]
        have hsplitP : qP = rP * 2 ^ B + qP % 2 ^ B := by
          rw [hrP_quot]; exact (Nat.div_add_mod' qP (2 ^ B)).symm
        have hsplitS : qS = rS * 2 ^ B + qS % 2 ^ B := by
          rw [hrS_quot]; exact (Nat.div_add_mod' qS (2 ^ B)).symm
        have hdig : qP % 2 ^ B = qS % 2 ^ B := by
          have hP : qP % 2 ^ B = PFn k % Dk k / 2 ^ (B * k) := by
            rw [hqP_def, hDk_app, show B * (k + 1) = B * k + B by ring, pow_add,
              Nat.mod_mul_right_div_self]
          have hS : qS % 2 ^ B = PSn k % Dk k / 2 ^ (B * k) := by
            rw [hqS_def, hDk_app, show B * (k + 1) = B * k + B by ring, pow_add,
              Nat.mod_mul_right_div_self]
          rw [hP, hS, hmod k hk]
        have hstepP : qP = Pn k + (if k = 0 then 0
            else (∑ j ∈ Finset.range k, Pn j * 2 ^ (B * j)) / 2 ^ (B * k)) := by
          rw [hqP_def, hPFn_app]; exact quot_step B Pn k
        have hstepS : qS = Sn k + (if k = 0 then 0
            else (∑ j ∈ Finset.range k, Sn j * 2 ^ (B * j)) / 2 ^ (B * k)) := by
          rw [hqS_def, hPSn_app]; exact quot_step B Sn k
        have hCnk : Cn k = OFFf k + rP - rS := by rw [hCn_app, ← hrP_def, ← hrS_def]
        have hrS_le : rS ≤ OFFf k := by
          rw [hrS_def]; have := hPSdiv k hk; have := hOFF_pos k; omega
        rw [hdig] at hsplitP
        clear_value qP qS rP rS
        have hmulCnk : Cn k * 2 ^ B = OFFf k * 2 ^ B + rP * 2 ^ B - rS * 2 ^ B := by
          rw [hCnk, Nat.sub_mul, Nat.add_mul]
        rcases Nat.eq_zero_or_pos k with hk0 | hk0
        · subst hk0
          rw [hmulCnk]
          simp only [↓reduceIte] at hstepP hstepS ⊢
          rw [Nat.add_zero] at hstepP hstepS
          have hrPmul : rS * 2 ^ B ≤ rP * 2 ^ B + OFFf 0 * 2 ^ B := by
            have : rS ≤ rP + OFFf 0 := by omega
            calc rS * 2 ^ B ≤ (rP + OFFf 0) * 2 ^ B := Nat.mul_le_mul_right _ this
              _ = rP * 2 ^ B + OFFf 0 * 2 ^ B := by rw [Nat.add_mul]
          omega
        · simp only [if_neg (show ¬ k = 0 from by omega)] at hstepP hstepS ⊢
          rw [hmulCnk]
          have hPFnprev : (∑ j ∈ Finset.range k, Pn j * 2 ^ (B * j)) = PFn (k - 1) := by
            rw [hPFn_app, show k - 1 + 1 = k from by omega]
          have hPSnprev : (∑ j ∈ Finset.range k, Sn j * 2 ^ (B * j)) = PSn (k - 1) := by
            rw [hPSn_app, show k - 1 + 1 = k from by omega]
          rw [hPFnprev] at hstepP
          rw [hPSnprev] at hstepS
          set rP' := PFn (k - 1) / Dk (k - 1) with hrP'_def
          set rS' := PSn (k - 1) / Dk (k - 1) with hrS'_def
          have hprevP : PFn (k - 1) / 2 ^ (B * k) = rP' := by
            rw [hrP'_def, hDk_app, show k - 1 + 1 = k from by omega]
          have hprevS : PSn (k - 1) / 2 ^ (B * k) = rS' := by
            rw [hrS'_def, hDk_app, show k - 1 + 1 = k from by omega]
          rw [hprevP] at hstepP
          rw [hprevS] at hstepS
          have hCnprev : Cn (k - 1) = OFFf (k - 1) + rP' - rS' := hCn_app (k - 1)
          have hrSprev_le : rS' ≤ OFFf (k - 1) := by
            rw [hrS'_def]
            have := hPSdiv (k - 1) (by omega); have := hOFF_pos (k - 1); omega
          rw [hCnprev]
          clear_value rP' rS'
          have hrPmul : rS * 2 ^ B ≤ rP * 2 ^ B + OFFf k * 2 ^ B := by
            have : rS ≤ rP + OFFf k := by omega
            calc rS * 2 ^ B ≤ (rP + OFFf k) * 2 ^ B := Nat.mul_le_mul_right _ this
              _ = rP * 2 ^ B + OFFf k * 2 ^ B := by rw [Nat.add_mul]
          omega

      have hCn_val : ∀ k, (hk : k < n) → (env.get (i₀ + k)).val = Cn k := by
        intro k hk
        rw [hwit_eq k hk,
          ZMod.val_natCast_of_lt (lt_of_lt_of_le (hrange k hk) (le_of_lt (h2Wf_lt_p k)))]

      have hcell_e : ∀ j, j < n →
          Expression.eval env.toEnvironment
            (if h : j < s then (var { index := i₀ + j } : Expression (F p))
             else var { index := i₀ + s + (j - s) })
            = env.get (i₀ + j) := by
        intro j hj
        split
        · simp [circuit_norm]
        · rename_i hjs
          have hcell : i₀ + s + (j - s) = i₀ + j := by omega
          simp [circuit_norm, hcell]
      refine ⟨?_, ?_, ?_, ?_⟩
      ·
        intro i
        have hin : i.val < n := by have := i.isLt; omega
        rw [hCn_val i.val hin]
        have := hrange i.val hin
        have hWfi : Wf i.val = W1 := by
          simp only [hWf, Wat, if_pos i.isLt]
        rwa [hWfi] at this
      ·
        intro i
        have hin : s + i.val < n := by have := i.isLt; omega
        have hcell : i₀ + s + i.val = i₀ + (s + i.val) := by omega
        rw [hcell, hCn_val (s + i.val) hin]
        have := hrange (s + i.val) hin
        have hWfi : Wf (s + i.val) = W2 := by
          simp only [hWf, Wat, if_neg (show ¬ (s + i.val < s) from by omega)]
        rwa [hWfi] at this
      ·
        intro i
        have hk := i.isLt
        have hnatk := hidx i.val hk
        have ha_e : Expression.eval env.toEnvironment input_var.lhs[i.val] = input.lhs[i.val]'hk := by
          rw [← h_input]; simp [Vector.getElem_map]
        have hb_e : Expression.eval env.toEnvironment input_var.rhs[i.val] = input.rhs[i.val]'hk := by
          rw [← h_input]; simp [Vector.getElem_map]
        have hcin_e : Expression.eval env.toEnvironment
            (if h : i.val = 0 then 0
              else (if h2 : i.val - 1 < s
                    then (var { index := i₀ + (i.val - 1) } : Expression (F p))
                    else var { index := i₀ + s + (i.val - 1 - s) })
                - Expression.const ((OFFat s W1 W2 (i.val - 1) : ℕ) : F p))
            = if i.val = 0 then 0
              else env.get (i₀ + (i.val - 1)) - ((OFFf (i.val - 1) : ℕ) : F p) := by
          split
          · simp [circuit_norm]
          · rename_i hk0
            have := hcell_e (i.val - 1) (by omega)
            simp only [circuit_norm, sub_eq_add_neg, hOFFf]
            rw [show Expression.eval env.toEnvironment
                (if h2 : i.val - 1 < s then (var { index := i₀ + (i.val - 1) } : Expression (F p))
                 else var { index := i₀ + s + (i.val - 1 - s) }) = env.get (i₀ + (i.val - 1)) from this]
        have hcout_e : Expression.eval env.toEnvironment
            (if h : i.val < s
             then (var { index := i₀ + i.val } : Expression (F p))
             else var { index := i₀ + s + (i.val - s) })
            = env.get (i₀ + i.val) := hcell_e i.val hk
        rw [ha_e, hb_e, hcin_e, hcout_e]
        have hAk : ((Pn i.val : ℕ) : F p) = (input.lhs[i.val]'hk) := by
          simp only [hPn, dif_pos hk]; rw [ZMod.natCast_zmod_val]
        have hBk : ((Sn i.val : ℕ) : F p) = (input.rhs[i.val]'hk) := by
          simp only [hSn, dif_pos hk]; rw [ZMod.natCast_zmod_val]
        have hCk : ((Cn i.val : ℕ) : F p) = env.get (i₀ + i.val) := by
          rw [hwit_eq i.val hk]
        have hpow_cast : ((2 ^ B : ℕ) : F p) = (2 ^ B : F p) := by push_cast; ring
        have hcast := congrArg (Nat.cast : ℕ → F p) hnatk
        push_cast [hpow_cast] at hcast
        rw [hAk, hBk, hCk] at hcast
        rcases Nat.eq_zero_or_pos i.val with hi0 | hi0
        · simp only [hi0, ↓reduceIte, add_zero] at hcast ⊢
          rw [← sub_eq_zero] at hcast
          rw [← hcast]; simp only [hOFFf]; ring
        · simp only [if_neg (show ¬ i.val = 0 from by omega)] at hcast ⊢
          have hCkprev : ((Cn (i.val - 1) : ℕ) : F p) = env.get (i₀ + (i.val - 1)) := by
            rw [hwit_eq (i.val - 1) (by omega)]
          rw [hCkprev, ← sub_eq_zero] at hcast
          rw [← hcast]; simp only [hOFFf]; ring
      ·
        have hcell : i₀ + s + (n - 1 - s) = i₀ + (n - 1) := by omega
        have htop : env.get (i₀ + (n - 1)) = ((2 ^ (W2 - 1) : ℕ) : F p) := by
          rw [hwit_eq (n - 1) (by omega), hCtop,
            hOFF_tier2 (n - 1) (show ¬ (n - 1 < s) from by omega)]
        rw [hcell, htop]; ring

end EqViaCarriesFlexT

end

namespace Cost

open Challenge.CostR1CS
open EqViaCarriesFlexT (FlexParamsT)

variable {n : ℕ}

theorem isR1CS_eqViaCarriesFlexT (P : FlexParamsT circomPrime n) [NeZero n]
    (input : Var (EqViaCarriesFlex.Inputs n) (F circomPrime))
    (hl : AffineW input.lhs) (hr : AffineW input.rhs) :
    IsR1CSCirc (EqViaCarriesFlexT.main P input) := by
  have hsn := P.hsn
  unfold EqViaCarriesFlexT.main
  refine IsR1CSCirc.bind_out (isR1CS_witnessVec P.s _) fun c1 => ?_
  refine IsR1CSCirc.bind_out (isR1CS_witnessVec (n - P.s) _) fun c2 => ?_
  refine IsR1CSCirc.bind ?_ fun _ => ?_
  · refine IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) fun i k => ?_
    exact isR1CS_assertion_rangeCheck P.W1 P.hW1p _
      (affineW_witnessVector_output _ _ _ i.val i.isLt) k
  refine IsR1CSCirc.bind ?_ fun _ => ?_
  · refine IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) fun i k => ?_
    exact isR1CS_assertion_rangeCheck P.W2 P.hW2p _
      (affineW_witnessVector_output _ _ _ i.val i.isLt) k
  refine IsR1CSCirc.bind ?_ fun _ => ?_
  · refine IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) fun i k => ?_
    refine IsR1CSCirc.assertZero ?_ k
    rw [Vector.getElem_mapFinRange]
    refine isR1CSRow_of_affine ?_
    refine Affine.sub (Affine.sub (Affine.add (hl i.val i.isLt) ?_) (hr i.val i.isLt))
      (Affine.mul_fconst _ (Affine.sub ?_ (Affine.const _)))
    · split
      · exact Affine.zero
      · refine Affine.sub ?_ (Affine.const _)
        split
        · exact affineW_witnessVector_output _ _ _ _ (by omega)
        · exact affineW_witnessVector_output _ _ _ _ (by omega)
    · split
      · exact affineW_witnessVector_output _ _ _ _ (by omega)
      · exact affineW_witnessVector_output _ _ _ _ (by omega)
  exact IsR1CSCirc.bind (IsR1CSCirc.assertZero
    (isR1CSRow_of_affine (Affine.sub
      (affineW_witnessVector_output _ _ _ (n - 1 - P.s) (by omega)) (Affine.const _))))
    fun _ => IsR1CSCirc.pure _

theorem isR1CS_assertion_eqViaCarriesFlexT (P : FlexParamsT circomPrime n)
    [NeZero n] (input : Var (EqViaCarriesFlex.Inputs n) (F circomPrime))
    (hl : AffineW input.lhs) (hr : AffineW input.rhs) :
    IsR1CSCirc (assertion (EqViaCarriesFlexT.circuit P) input) :=
  IsR1CSCirc.assertion (fun m => isR1CS_eqViaCarriesFlexT P input hl hr m)

end Cost

namespace EqViaCarriesFlexT

def linFlexT : FlexParamsT circomPrime 5 where
  B := 64
  s := 4
  W1 := 5
  W2 := 1
  M := #v[2^67, 2^67, 2^67, 2^67, 2^4]
  hs1 := by decide
  hsn := by decide
  hB := by decide
  hW1p := by decide
  hW2p := by decide
  hB1 := by decide
  hW11 := by decide
  hW21 := by decide
  hcarry := by decide
  hlift := by decide

def quadFlexT : FlexParamsT circomPrime 9 where
  B := 64
  s := 7
  W1 := 68
  W2 := 5
  M := #v[5*2^128, 5*2^128, 5*2^128, 5*2^128, 5*2^128, 5*2^128, 5*2^128,
          2^67, 2^67]
  hs1 := by decide
  hsn := by decide
  hB := by decide
  hW1p := by decide
  hW2p := by decide
  hB1 := by decide
  hW11 := by decide
  hW21 := by decide
  hcarry := by decide
  hlift := by decide

def wideFlexT : FlexParamsT circomPrime 10 where
  B := 64
  s := 7
  W1 := 69
  W2 := 6
  M := #v[13*2^128, 13*2^128, 13*2^128, 13*2^128, 13*2^128, 13*2^128,
          13*2^128, 2^67, 2^67, 2^67]
  hs1 := by decide
  hsn := by decide
  hB := by decide
  hW1p := by decide
  hW2p := by decide
  hB1 := by decide
  hW11 := by decide
  hW21 := by decide
  hcarry := by decide
  hlift := by decide

example : (5 + 4 * linFlexT.W1 + 1 * linFlexT.W2)
    + (4 * (linFlexT.W1 + 1) + 1 * (linFlexT.W2 + 1) + 5 + 1) = 58 := rfl
example : (9 + 7 * quadFlexT.W1 + 2 * quadFlexT.W2)
    + (7 * (quadFlexT.W1 + 1) + 2 * (quadFlexT.W2 + 1) + 9 + 1) = 1000 := rfl
example : (10 + 7 * wideFlexT.W1 + 3 * wideFlexT.W2)
    + (7 * (wideFlexT.W1 + 1) + 3 * (wideFlexT.W2 + 1) + 10 + 1) = 1033 := rfl

end EqViaCarriesFlexT

end Solution.Secp256k1ScalarMulFixedBase

namespace Solution.Secp256k1ScalarMulFixedBase
namespace EqViaCarriesFlexT

section ComputableWitness
variable {p : ℕ} [Fact p.Prime] {n : ℕ} [NeZero n]
open Challenge.Utils.ComputableWitnessLemmas
open EqViaCarriesFlex (evalPartial_stable inputs_field_eq Inputs)

theorem computableWitnesses (P : FlexParamsT p n) [Fact (p > 2)] :
    (circuit P).ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (FormalCircuitBase.computableWitnessCondition input env env')
    ((main P input).operations offset)
  apply FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main
  simp only [
    Circuit.bind_structuralComputableWitnesses_iff,
    Circuit.witnessVector_structuralComputableWitnesses_iff,
    Circuit.forEach_structuralComputableWitnesses_iff,
    FormalAssertion.assertion_structuralComputableWitnesses_iff,
    Circuit.assertZero_structuralComputableWitnesses_iff]
  and_intros
  · intro _ h_input
    obtain ⟨hlhs, hrhs⟩ := inputs_field_eq h_input
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_ofFn]
    rw [evalPartial_stable (input := input) input.lhs P.B i hlhs,
      evalPartial_stable (input := input) input.rhs P.B i hrhs]
  · intro _ h_input
    obtain ⟨hlhs, hrhs⟩ := inputs_field_eq h_input
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_ofFn]
    rw [evalPartial_stable (input := input) input.lhs P.B (P.s + i) hlhs,
      evalPartial_stable (input := input) input.rhs P.B (P.s + i) hrhs]
  · intro i
    apply FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
    · intro k env env' hk h_agree _
      rw [CircuitType.eval_expression_prover_to_verifier (M := field),
        CircuitType.eval_expression_prover_to_verifier (M := field)]
      rw [show eval env.toEnvironment
              ((witnessVector P.s fun env =>
                Vector.ofFn fun k : Fin P.s =>
                  ((2 ^ (P.W1 - 1) + evalPartial P.B env input.lhs k.val / 2 ^ (P.B * (k.val + 1))
                      - evalPartial P.B env input.rhs k.val / 2 ^ (P.B * (k.val + 1)) : ℕ) :
                    F p)).output offset)[i.val] =
            env.get (offset + i.val) by
          rw [CircuitType.eval_expression (M := field)]
          simp [Circuit.witnessVector, Circuit.output, ProvableType.eval,
            explicit_provable_type, size, Vector.getElem_mapRange, Expression.eval],
        show eval env'.toEnvironment
              ((witnessVector P.s fun env =>
                Vector.ofFn fun k : Fin P.s =>
                  ((2 ^ (P.W1 - 1) + evalPartial P.B env input.lhs k.val / 2 ^ (P.B * (k.val + 1))
                      - evalPartial P.B env input.rhs k.val / 2 ^ (P.B * (k.val + 1)) : ℕ) :
                    F p)).output offset)[i.val] =
            env'.get (offset + i.val) by
          rw [CircuitType.eval_expression (M := field)]
          simp [Circuit.witnessVector, Circuit.output, ProvableType.eval,
            explicit_provable_type, size, Vector.getElem_mapRange, Expression.eval]]
      exact h_agree (offset + i.val) (by
        have hbase : offset + P.s + (n - P.s) + i.val * P.W1 ≤ k := by
          simpa [circuit_norm, Circuit.localLength, Gadgets.ToBits.rangeCheck] using hk
        have := i.isLt
        omega)
    · exact rangeCheckComputableWitnesses P.W1 P.hW1p
  · intro i
    apply FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
    · intro k env env' hk h_agree _
      rw [CircuitType.eval_expression_prover_to_verifier (M := field),
        CircuitType.eval_expression_prover_to_verifier (M := field)]
      have hL : ∀ (m : ℕ) (c : ProverEnvironment (F p) → Vector (F p) m) (o : ℕ),
          (witnessVector m c).localLength o = m := fun _ _ _ => rfl
      rw [hL] at *
      rw [show eval env.toEnvironment
              ((witnessVector (n - P.s) fun env =>
                Vector.ofFn fun k : Fin (n - P.s) =>
                  ((2 ^ (P.W2 - 1)
                      + evalPartial P.B env input.lhs (P.s + k.val) / 2 ^ (P.B * (P.s + k.val + 1))
                      - evalPartial P.B env input.rhs (P.s + k.val) / 2 ^ (P.B * (P.s + k.val + 1)) : ℕ) :
                    F p)).output (offset + P.s))[i.val] =
            env.get (offset + P.s + i.val) by
          rw [CircuitType.eval_expression (M := field)]
          simp [Circuit.witnessVector, Circuit.output, ProvableType.eval,
            explicit_provable_type, size, Vector.getElem_mapRange, Expression.eval],
        show eval env'.toEnvironment
              ((witnessVector (n - P.s) fun env =>
                Vector.ofFn fun k : Fin (n - P.s) =>
                  ((2 ^ (P.W2 - 1)
                      + evalPartial P.B env input.lhs (P.s + k.val) / 2 ^ (P.B * (P.s + k.val + 1))
                      - evalPartial P.B env input.rhs (P.s + k.val) / 2 ^ (P.B * (P.s + k.val + 1)) : ℕ) :
                    F p)).output (offset + P.s))[i.val] =
            env'.get (offset + P.s + i.val) by
          rw [CircuitType.eval_expression (M := field)]
          simp [Circuit.witnessVector, Circuit.output, ProvableType.eval,
            explicit_provable_type, size, Vector.getElem_mapRange, Expression.eval]]
      exact h_agree (offset + P.s + i.val) (by
        have hbase : offset + P.s + (n - P.s) + P.s * P.W1 + i.val * P.W2 ≤ k := by
          simp only [circuit_norm, Circuit.localLength, Gadgets.ToBits.rangeCheck,
            Circuit.forEach] at hk
          omega
        have := i.isLt
        omega)
    · exact rangeCheckComputableWitnesses P.W2 P.hW2p
  · intro _
    trivial
  · trivial

end ComputableWitness

end EqViaCarriesFlexT

end Solution.Secp256k1ScalarMulFixedBase

end DonorFile1_4

-- Adapted donor module: GroupedFlexInstances
section DonorFile1_5

namespace Solution.Secp256k1ScalarMulFixedBase

open GroupedFlex (VParams GVXHyps widthAllocFrom widthConsFrom)

def gfLin (k : ℕ) : ℕ := if k = 0 then 1 else 2

def posOfLin (k : ℕ) : ℕ := if k = 0 then 0 else if k = 1 then 1 else 2 * k - 1

def mLin : Vector ℕ 5 := #v[2 ^ 67, 2 ^ 67, 2 ^ 67, 2 ^ 67, 2 ^ 4]

def nfLin (j : ℕ) : ℕ := if h : j < 5 then mLin[j]'h else 1

def offLin (k : ℕ) : ℕ := if k = 0 then 7 else 8

def wfLin (k : ℕ) : ℕ := if k = 0 then 4 else 5

def vLin : VParams := { Nf := nfLin, OFFf := offLin, Wf := wfLin }

theorem mLin_pos : ∀ i (hi : i < 5), 1 ≤ mLin[i]'hi := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem hgvLin :
    GVXHyps circomPrime 5 64 gfLin posOfLin 3 vLin vLin := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, by norm_num, by decide, by decide, by decide⟩
  · intro k; simp only [posOfLin, gfLin]; split_ifs <;> omega
  · intro k; simp only [gfLin]; split_ifs <;> omega
  · intro k; simp only [vLin, wfLin]; split_ifs <;> exact ⟨by decide, by decide⟩
  · intro j
    simp only [vLin, nfLin]
    split
    · rename_i hj; exact ⟨mLin_pos j hj, mLin_pos j hj⟩
    · exact ⟨le_refl 1, le_refl 1⟩
  · intro k hk
    have hcase : k = 0 ∨ k = 1 := by omega
    rcases hcase with rfl | rfl <;>
      exact ⟨by decide, ⟨by decide, by decide⟩, by decide⟩

example : widthAllocFrom vLin.Wf (3 - 2) 0 + (widthConsFrom vLin.Wf (3 - 2) 0 + 1) = 8 := rfl

/-- Tight coefficient bounds for canonicalization's relation `r + b*p = x`.
The low limb uses the actual sparse low limb of secp256k1's prime; the other
three limbs use the exact sum bound. -/
def nfCanonicalL (j : ℕ) : ℕ := if j < 4 then 2 ^ 65 else 1

def nfCanonicalR (j : ℕ) : ℕ := if j < 4 then 2 ^ 64 else 1

/-- Group `0` of the canonicalization schedule spans position `0` alone
(`gfLin 0 = 1`), where the honest carry is a single bit: the left coefficient is
`r₀ + b·p₀ < 2^65` and the right one is `x₀ < 2^64`. Sizing the offsets and the
carry width per group rather than uniformly makes that carry a `1`-bit check. -/
def vCanonicalL : VParams :=
  { Nf := nfCanonicalL,
    OFFf := fun k => if k = 0 then 1 else 3,
    Wf := fun k => if k = 0 then 1 else 3 }

def vCanonicalR : VParams :=
  { Nf := nfCanonicalR,
    OFFf := fun k => if k = 0 then 0 else 4,
    Wf := fun k => if k = 0 then 1 else 3 }

set_option maxHeartbeats 4000000 in
theorem hgvCanonical :
    GVXHyps circomPrime 5 64 gfLin posOfLin 3 vCanonicalL vCanonicalR := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, by norm_num, by decide, by decide, by decide⟩
  · intro k; simp only [posOfLin, gfLin]; split_ifs <;> omega
  · intro k; simp only [gfLin]; split_ifs <;> omega
  · intro k
    simp only [vCanonicalL]
    split_ifs <;> exact ⟨by decide, by decide⟩
  · intro j
    simp only [vCanonicalL, vCanonicalR, nfCanonicalL, nfCanonicalR]
    split_ifs <;> omega
  · intro k hk
    have hcase : k = 0 ∨ k = 1 := by omega
    rcases hcase with rfl | rfl <;>
      norm_num [vCanonicalL, vCanonicalR, nfCanonicalL, nfCanonicalR, gfLin, posOfLin] <;>
      decide

example : widthAllocFrom vCanonicalL.Wf (3 - 2) 0 +
    (widthConsFrom vCanonicalL.Wf (3 - 2) 0 + 1) = 2 := rfl

def gfQuad (k : ℕ) : ℕ := if k = 3 then 1 else 2

def posOfQuad (k : ℕ) : ℕ :=
  if k = 0 then 0 else if k = 1 then 2 else if k = 2 then 4 else if k = 3 then 6 else 2 * k - 1

def mQuad : Vector ℕ 9 :=
  #v[5 * 2 ^ 128, 5 * 2 ^ 128, 5 * 2 ^ 128, 5 * 2 ^ 128, 5 * 2 ^ 128, 5 * 2 ^ 128, 5 * 2 ^ 128,
     2 ^ 67, 2 ^ 67]

def nfQuad (j : ℕ) : ℕ := if h : j < 9 then mQuad[j]'h else 1

def offQuad (k : ℕ) : ℕ := if k = 0 then 92233720368547758084 else 92233720368547758085

def wfQuad (_ : ℕ) : ℕ := 68

def vQuad : VParams := { Nf := nfQuad, OFFf := offQuad, Wf := wfQuad }

theorem mQuad_pos : ∀ i (hi : i < 9), 1 ≤ mQuad[i]'hi := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem hgvQuad :
    GVXHyps circomPrime 9 64 gfQuad posOfQuad 5 vQuad vQuad := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, by norm_num, by decide, by decide, by decide⟩
  · intro k; simp only [posOfQuad, gfQuad]; split_ifs <;> omega
  · intro k; simp only [gfQuad]; split_ifs <;> omega
  · intro k; simp only [vQuad, wfQuad]; exact ⟨by decide, by decide⟩
  · intro j
    simp only [vQuad, nfQuad]
    split
    · rename_i hj; exact ⟨mQuad_pos j hj, mQuad_pos j hj⟩
    · exact ⟨le_refl 1, le_refl 1⟩
  · intro k hk
    have hcase : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hcase with rfl | rfl | rfl | rfl <;>
      exact ⟨by decide, ⟨by decide, by decide⟩, by decide⟩

example :
    widthAllocFrom vQuad.Wf (5 - 2) 0 + (widthConsFrom vQuad.Wf (5 - 2) 0 + 1) = 406 := rfl

def gfWide (k : ℕ) : ℕ := if k ≤ 3 then 2 else 1

def posOfWide (k : ℕ) : ℕ :=
  if k = 0 then 0 else if k = 1 then 2 else if k = 2 then 4 else if k = 3 then 6 else k + 4

def mWide : Vector ℕ 10 :=
  #v[13 * 2 ^ 128, 13 * 2 ^ 128, 13 * 2 ^ 128, 13 * 2 ^ 128, 13 * 2 ^ 128, 13 * 2 ^ 128,
     13 * 2 ^ 128, 2 ^ 67, 2 ^ 67, 2 ^ 67]

def nfWide (j : ℕ) : ℕ := if h : j < 10 then mWide[j]'h else 1

def offWide (k : ℕ) : ℕ :=
  if k = 0 then 239807672958224171020
  else if k = 1 then 239807672958224171021
  else if k = 2 then 239807672958224171021
  else if k = 3 then 21
  else 8

def wfWide (k : ℕ) : ℕ :=
  if k = 0 then 69 else if k = 1 then 69 else if k = 2 then 69 else if k = 3 then 6 else 5

def vWide : VParams := { Nf := nfWide, OFFf := offWide, Wf := wfWide }

theorem mWide_pos : ∀ i (hi : i < 10), 1 ≤ mWide[i]'hi := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem hgvWide :
    GVXHyps circomPrime 10 64 gfWide posOfWide 6 vWide vWide := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, by norm_num, by decide, by decide, by decide⟩
  · intro k; simp only [posOfWide, gfWide]; split_ifs <;> omega
  · intro k; simp only [gfWide]; split_ifs <;> omega
  · intro k; simp only [vWide, wfWide]; split_ifs <;> exact ⟨by decide, by decide⟩
  · intro j
    simp only [vWide, nfWide]
    split
    · rename_i hj; exact ⟨mWide_pos j hj, mWide_pos j hj⟩
    · exact ⟨le_refl 1, le_refl 1⟩
  · intro k hk
    have hcase : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨by decide, ⟨by decide, by decide⟩, by decide⟩

example :
    widthAllocFrom vWide.Wf (6 - 2) 0 + (widthConsFrom vWide.Wf (6 - 2) 0 + 1) = 423 := rfl

/-! ### Fattened quad instance (§BORROW-PILOT)

Same shape as `gfQuad`/`posOfQuad`/`vQuad` (`G = 5`, partition `[2,2,2,1,2]`),
but the 7 convolution-position bounds are widened `5·2^128 → 12·2^128` to
accommodate a fat-limb multiplicand (`< 3·2^64` per limb, vs `< 2^64`
canonical). `grouped_tent_fat.py` (extending the leader's `grouped_tent.py`)
confirms the DP-optimal partition is unchanged and the cost moves
`406 → 412` (`Wf` widens `68 → 69` uniformly at all 3 paid boundaries),
capacity holding with wide margin (checked up to `32·2^128`). -/

def gfQuadFat (k : ℕ) : ℕ := if k = 3 then 1 else 2

def posOfQuadFat (k : ℕ) : ℕ :=
  if k = 0 then 0 else if k = 1 then 2 else if k = 2 then 4 else if k = 3 then 6 else 2 * k - 1

def mQuadFat : Vector ℕ 9 :=
  #v[12 * 2 ^ 128, 12 * 2 ^ 128, 12 * 2 ^ 128, 12 * 2 ^ 128, 12 * 2 ^ 128, 12 * 2 ^ 128,
     12 * 2 ^ 128, 2 ^ 67, 2 ^ 67]

def nfQuadFat (j : ℕ) : ℕ := if h : j < 9 then mQuadFat[j]'h else 1

def offQuadFat (k : ℕ) : ℕ :=
  if k = 0 then 221360928884514619403 else 221360928884514619404

def wfQuadFat (_ : ℕ) : ℕ := 69

def vQuadFat : VParams := { Nf := nfQuadFat, OFFf := offQuadFat, Wf := wfQuadFat }

theorem mQuadFat_pos : ∀ i (hi : i < 9), 1 ≤ mQuadFat[i]'hi := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem hgvQuadFat :
    GVXHyps circomPrime 9 64 gfQuadFat posOfQuadFat 5 vQuadFat vQuadFat := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, by norm_num, by decide, by decide, by decide⟩
  · intro k; simp only [posOfQuadFat, gfQuadFat]; split_ifs <;> omega
  · intro k; simp only [gfQuadFat]; split_ifs <;> omega
  · intro k; simp only [vQuadFat, wfQuadFat]; exact ⟨by decide, by decide⟩
  · intro j
    simp only [vQuadFat, nfQuadFat]
    split
    · rename_i hj; exact ⟨mQuadFat_pos j hj, mQuadFat_pos j hj⟩
    · exact ⟨le_refl 1, le_refl 1⟩
  · intro k hk
    have hcase : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hcase with rfl | rfl | rfl | rfl <;>
      exact ⟨by decide, ⟨by decide, by decide⟩, by decide⟩

example :
    widthAllocFrom vQuadFat.Wf (5 - 2) 0 + (widthConsFrom vQuadFat.Wf (5 - 2) 0 + 1) = 412 := rfl

/-! ### Fattened wide instance (§BORROW-ROLLOUT, d2 site)

Same shape as `gfWide`/`posOfWide`/`vWide` (`G = 6`, partition `[2,2,2,2,1,1]`),
but the 7 convolution-position bounds are widened `13·2^128 → 21·2^128`:
after converting stageC1's `d2` to the wire-only fat `dtilOf xT2 x1`, the
LHS coefficient is `convLD2fat (< 12·2^128) + convLX1 (< 8·2^128) + cExp
(< 2^64) < 21·2^128`. The tent DP (grouped_tent script) confirms the
partition is unchanged and the cost moves `423 → 429` (`Wf` widens
`69 → 70` at the 3 wide boundaries; the 4th boundary stays at 6). -/

def gfWideFat (k : ℕ) : ℕ := if k ≤ 3 then 2 else 1

def posOfWideFat (k : ℕ) : ℕ :=
  if k = 0 then 0 else if k = 1 then 2 else if k = 2 then 4 else if k = 3 then 6 else k + 4

def mWideFat : Vector ℕ 10 :=
  #v[21 * 2 ^ 128, 21 * 2 ^ 128, 21 * 2 ^ 128, 21 * 2 ^ 128, 21 * 2 ^ 128, 21 * 2 ^ 128,
     21 * 2 ^ 128, 2 ^ 67, 2 ^ 67, 2 ^ 67]

def nfWideFat (j : ℕ) : ℕ := if h : j < 10 then mWideFat[j]'h else 1

def offWideFat (k : ℕ) : ℕ :=
  if k = 0 then 387381625547900583956
  else if k = 1 then 387381625547900583957
  else if k = 2 then 387381625547900583957
  else if k = 3 then 29
  else 8

def wfWideFat (k : ℕ) : ℕ :=
  if k = 0 then 70 else if k = 1 then 70 else if k = 2 then 70 else if k = 3 then 6 else 5

def vWideFat : VParams := { Nf := nfWideFat, OFFf := offWideFat, Wf := wfWideFat }

theorem mWideFat_pos : ∀ i (hi : i < 10), 1 ≤ mWideFat[i]'hi := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem hgvWideFat :
    GVXHyps circomPrime 10 64 gfWideFat posOfWideFat 6 vWideFat vWideFat := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, by norm_num, by decide, by decide, by decide⟩
  · intro k; simp only [posOfWideFat, gfWideFat]; split_ifs <;> omega
  · intro k; simp only [gfWideFat]; split_ifs <;> omega
  · intro k; simp only [vWideFat, wfWideFat]; split_ifs <;> exact ⟨by decide, by decide⟩
  · intro j
    simp only [vWideFat, nfWideFat]
    split
    · rename_i hj; exact ⟨mWideFat_pos j hj, mWideFat_pos j hj⟩
    · exact ⟨le_refl 1, le_refl 1⟩
  · intro k hk
    have hcase : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨by decide, ⟨by decide, by decide⟩, by decide⟩

example :
    widthAllocFrom vWideFat.Wf (6 - 2) 0 + (widthConsFrom vWideFat.Wf (6 - 2) 0 + 1) = 429 := rfl

/-! ### Recode instance (§SKEPTIC-ROUND item 2, w9-mixed retune)

`B = 9`, `L = 30`, uniform per-position bound `1024` (recode digit rows are
10-bit affine combinations; the 4-bit top window and the tail ride the same
loose bound). Partition at max group size 2: `[1] ++ [2]×14 ++ [1]`,
`G = 16`, 14 paid interior boundaries plus the singleton tail. Same
structural regime as the shipped `L = 33` w8 instance. -/

theorem vLin_Nf_eq_boundAt (j : Fin 5) :
    vLin.Nf j.val = EqViaCarriesFlex.boundAt EqViaCarriesFlexT.linFlexT.M j.val := by
  fin_cases j <;> decide

theorem vQuad_Nf_eq_boundAt (j : Fin 9) :
    vQuad.Nf j.val = EqViaCarriesFlex.boundAt EqViaCarriesFlexT.quadFlexT.M j.val := by
  fin_cases j <;> decide

theorem vWide_Nf_eq_boundAt (j : Fin 10) :
    vWide.Nf j.val = EqViaCarriesFlex.boundAt EqViaCarriesFlexT.wideFlexT.M j.val := by
  fin_cases j <;> decide

/-- §BORROW-PILOT: direct bound facts for the fattened quad tent (no
`EqViaCarriesFlexT` table needed — `GroupedFlex.Assumptions` is parametrized
directly by `NfL NfR : ℕ → ℕ`, so `vQuadFat.Nf` itself is the bound). -/
theorem vQuadFat_Nf_lo (k : Fin 9) (hk : k.val < 7) : vQuadFat.Nf k.val = 12 * 2 ^ 128 := by
  fin_cases k <;> revert hk <;> decide

theorem vQuadFat_Nf_hi (k : Fin 9) (hk : 7 ≤ k.val) : vQuadFat.Nf k.val = 2 ^ 67 := by
  fin_cases k <;> revert hk <;> decide

theorem vWideFat_Nf_lo (k : Fin 10) (hk : k.val < 7) : vWideFat.Nf k.val = 21 * 2 ^ 128 := by
  fin_cases k <;> revert hk <;> decide

theorem vWideFat_Nf_hi (k : Fin 10) (hk : 7 ≤ k.val) : vWideFat.Nf k.val = 2 ^ 67 := by
  fin_cases k <;> revert hk <;> decide

/-! ### Folded (pseudo-Mersenne) layout: `L = 4` positions, a single carry

After folding convolution positions `4,5,6` onto `0,1,2` with the constant
`cF = 2 ^ 256 - P256`, both sides of the modular identity live on four
positions only, the quotient is a single wire below `2 ^ 68`, and one grouped
carry (positions `{0,1}`) plus the native-field row suffice. -/

def gfFold (k : ℕ) : ℕ := if k = 0 then 2 else 1

def posOfFold (k : ℕ) : ℕ := if k = 0 then 0 else k + 1

def nfFoldL (j : ℕ) : ℕ :=
  if j = 0 then 2 ^ 162 + 2 ^ 140
  else if j = 1 then 2 ^ 161 + 2 ^ 141
  else if j = 2 then 2 ^ 160 + 2 ^ 140
  else if j = 3 then 2 ^ 131 else 1

def nfFoldR (j : ℕ) : ℕ := if j < 4 then 2 ^ 133 else 1

def offFoldL (k : ℕ) : ℕ := if k = 0 then 2 ^ 97 + 2 ^ 78 else 2 ^ 96 + 2 ^ 77

def offFoldR (k : ℕ) : ℕ := if k = 0 then 2 ^ 69 + 2 ^ 5 else 2 ^ 69 + 2 ^ 6

def wfFold (_ : ℕ) : ℕ := 98

def vFoldL : VParams := { Nf := nfFoldL, OFFf := offFoldL, Wf := wfFold }

def vFoldR : VParams := { Nf := nfFoldR, OFFf := offFoldR, Wf := wfFold }

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem hgvFold :
    GVXHyps circomPrime 4 64 gfFold posOfFold 3 vFoldL vFoldR := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, by norm_num, by decide, by decide, by decide⟩
  · intro k; simp only [posOfFold, gfFold]; split_ifs <;> omega
  · intro k; simp only [gfFold]; split_ifs <;> omega
  · intro k; simp only [vFoldL, wfFold]; exact ⟨by decide, by decide⟩
  · intro j
    refine ⟨?_, ?_⟩
    · show 1 ≤ nfFoldL j
      unfold nfFoldL
      split_ifs <;> first | exact Nat.one_le_two_pow | omega
    · show 1 ≤ nfFoldR j
      unfold nfFoldR
      split_ifs <;> first | exact Nat.one_le_two_pow | omega
  · intro k hk
    have hcase : k = 0 ∨ k = 1 := by omega
    rcases hcase with rfl | rfl <;>
      exact ⟨by decide, ⟨by decide, by decide⟩, by decide⟩

example :
    widthAllocFrom vFoldL.Wf (3 - 2) 0 + (widthConsFrom vFoldL.Wf (3 - 2) 0 + 1) = 196 := rfl

/-! ### Folded layout for the wide (two-convolution) slope identity -/

/-- Position-aware coefficient caps for the wide fold.  The summed convolution
at position `k` has only `convTerms k` products, so positions `1` and `2`
(which fold in positions `5` and `6`) are strictly smaller than position `0`. -/
def nfFoldWL (j : ℕ) : ℕ :=
  if j = 0 then 2 ^ 164
  else if j = 1 then 2 ^ 163 + 2 ^ 162
  else if j = 2 then 2 ^ 163
  else if j = 3 then 2 ^ 134
  else 1

def nfFoldWR (j : ℕ) : ℕ := if j < 4 then 2 ^ 135 else 1

def offFoldWL (k : ℕ) : ℕ :=
  if k = 0 then 2 ^ 99 + 2 ^ 98 + 2 ^ 36 else 2 ^ 99 + 2 ^ 36

def offFoldWR (k : ℕ) : ℕ := if k = 0 then 2 ^ 71 + 2 ^ 7 else 2 ^ 71 + 2 ^ 8

def wfFoldW (_ : ℕ) : ℕ := 100

def vFoldWL : VParams := { Nf := nfFoldWL, OFFf := offFoldWL, Wf := wfFoldW }

def vFoldWR : VParams := { Nf := nfFoldWR, OFFf := offFoldWR, Wf := wfFoldW }

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem hgvFoldW :
    GVXHyps circomPrime 4 64 gfFold posOfFold 3 vFoldWL vFoldWR := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, by norm_num, by decide, by decide, by decide⟩
  · intro k; simp only [posOfFold, gfFold]; split_ifs <;> omega
  · intro k; simp only [gfFold]; split_ifs <;> omega
  · intro k; simp only [vFoldWL, wfFoldW]; exact ⟨by decide, by decide⟩
  · intro j
    refine ⟨?_, ?_⟩
    · show 1 ≤ nfFoldWL j
      unfold nfFoldWL
      split_ifs <;> first | exact Nat.one_le_two_pow | omega
    · show 1 ≤ nfFoldWR j
      unfold nfFoldWR
      split_ifs <;> first | exact Nat.one_le_two_pow | omega
  · intro k hk
    have hcase : k = 0 ∨ k = 1 := by omega
    rcases hcase with rfl | rfl <;>
      exact ⟨by decide, ⟨by decide, by decide⟩, by decide⟩

example :
    widthAllocFrom vFoldWL.Wf (3 - 2) 0 + (widthConsFrom vFoldWL.Wf (3 - 2) 0 + 1) = 200 := rfl

end Solution.Secp256k1ScalarMulFixedBase

end DonorFile1_5

-- Adapted donor module: NormalizeImplicit
section DonorFile1_6

namespace Solution.Secp256k1ScalarMulFixedBase
open Solution.Secp256k1ScalarMulFixedBase.Limbs

namespace NormalizeImplicit

variable {m : ℕ}

def main (P : BigIntParams circomPrime m) (x : Var (BigInt m) (F circomPrime)) :
    Circuit (F circomPrime) Unit :=
  Circuit.forEach x (fun xi => RangeCheck.circuit P.B P.hB P.hB1 xi)

instance elaborated (P : BigIntParams circomPrime m) :
    ElaboratedCircuit (F circomPrime) (BigInt m) unit (main P) where
  localLength _ := m * (P.B - 1)
  localLength_eq := by
    intro input offset
    simp only [main, circuit_norm, RangeCheck.circuit, RangeCheck.elaborated]
  subcircuitsConsistent := by
    intro input offset
    simp +arith only [main, circuit_norm, RangeCheck.circuit, RangeCheck.elaborated]
  channelsLawful := by
    simp only [main, circuit_norm, RangeCheck.circuit, RangeCheck.elaborated]

def Assumptions (_ : BigInt m (F circomPrime)) : Prop := True

def Spec (B : ℕ) (x : BigInt m (F circomPrime)) : Prop := BigInt.Normalized B x

def circuit (P : BigIntParams circomPrime m) : FormalAssertion (F circomPrime) (BigInt m) where
  main := main P
  Assumptions := Assumptions
  Spec := Spec P.B
  soundness := by
    circuit_proof_start
    simp_all only [circuit_norm, RangeCheck.circuit, RangeCheck.elaborated,
      RangeCheck.Assumptions, RangeCheck.Spec, BigInt.Normalized]
    intro i
    rw [← h_input, Vector.getElem_map]
    exact h_holds i
  completeness := by
    circuit_proof_start
    simp_all only [circuit_norm, RangeCheck.circuit, RangeCheck.elaborated,
      RangeCheck.Assumptions, RangeCheck.Spec, BigInt.Normalized]
    intro i
    have := h_spec i
    rwa [← h_input, Vector.getElem_map] at this

theorem computableWitnesses (P : BigIntParams circomPrime m) :
    (circuit P).ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition input env env')
    ((main P input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.forEach_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_structuralComputableWitnesses_iff]
  intro i
  apply Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_flatStructuralComputableWitnesses
  · intro env₁ env₂ h_input
    have h : (eval env₁ input)[i.val] = (eval env₂ input)[i.val] := by
      simpa only [Fin.getElem_fin] using congrArg (fun x : BigInt m (F circomPrime) => x[i]) h_input
    rw [← ProvableType.getElem_eval_fields_prover (env := env₁) input i.val i.isLt,
      ← ProvableType.getElem_eval_fields_prover (env := env₂) input i.val i.isLt] at h
    simpa [CircuitType.eval_expression_prover_to_verifier (M := field),
      CircuitType.eval_expression (M := field), ProvableType.eval, explicit_provable_type] using h
  · exact RangeCheck.computableWitnesses P.B P.hB P.hB1

theorem computableWitness (P : BigIntParams circomPrime m) : ∀ n input,
    ProverEnvironment.OnlyAccessedBelow n
      (fun env : ProverEnvironment (F circomPrime) => eval env input) →
    Circuit.ComputableWitnesses (main P input) n := by
  exact Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnesses_implies
    (computableWitnesses P)

namespace Cost
open Challenge.CostR1CS
open Solution.Secp256k1ScalarMulFixedBase.Cost

theorem costIs_main (P : BigIntParams circomPrime m)
    (x : Var (BigInt m) (F circomPrime)) :
    CostIs (main P x) ⟨m * (P.B - 1), m * P.B⟩ := by
  unfold main
  exact CostIs.forEach (fun a n => costIs_assertion_implicitRangeCheck P.B P.hB P.hB1 a n)

theorem isR1CS_main (P : BigIntParams circomPrime m)
    (x : Var (BigInt m) (F circomPrime)) (hx : AffineW x) :
    IsR1CSCirc (main P x) := by
  unfold main
  exact IsR1CSCirc.forEach_mem (α := Expression (F circomPrime))
    fun i n => isR1CS_assertion_implicitRangeCheck P.B P.hB P.hB1 x[i.val] (hx i.val i.isLt) n

theorem costIs_assertion_main (P : BigIntParams circomPrime m)
    (x : Var (BigInt m) (F circomPrime)) :
    CostIs (assertion (circuit P) x) ⟨m * (P.B - 1), m * P.B⟩ :=
  CostIs.assertion (fun n => costIs_main P x n)

theorem isR1CS_assertion_main (P : BigIntParams circomPrime m)
    (x : Var (BigInt m) (F circomPrime)) (hx : AffineW x) :
    IsR1CSCirc (assertion (circuit P) x) :=
  IsR1CSCirc.assertion (fun n => isR1CS_main P x hx n)

end Cost

end NormalizeImplicit

end Solution.Secp256k1ScalarMulFixedBase

end DonorFile1_6

-- Adapted donor module: CompactAdd
section DonorFile1_7

namespace Solution.Secp256k1ScalarMulFixedBase
namespace CompactAdd

open Specs.Secp256k1 (Fp)

def c976 : ℕ := 2 ^ 32 + 976

def cK : ℕ := P256 - c976

def cExp (v k : ℕ) : Expression (F circomPrime) :=
  (((limbOfNat v k : ℕ) : F circomPrime) : Expression (F circomPrime))

def qpCoeff (q : Var Emu (F circomPrime)) (qt : Expression (F circomPrime))
    (k : ℕ) : Expression (F circomPrime) :=
  (if h : k < 4 then q[k] * cExp P256 0 else 0)
    + (if h : 1 ≤ k ∧ k - 1 < 4 then q[k - 1]'h.2 * cExp P256 1 else 0)
    + (if h : 2 ≤ k ∧ k - 2 < 4 then q[k - 2]'h.2 * cExp P256 2 else 0)
    + (if h : 3 ≤ k ∧ k - 3 < 4 then q[k - 3]'h.2 * cExp P256 3 else 0)
    + (if k = 4 then qt * cExp P256 0 else 0)
    + (if k = 5 then qt * cExp P256 1 else 0)
    + (if k = 6 then qt * cExp P256 2 else 0)
    + (if k = 7 then qt * cExp P256 3 else 0)

def dFullVal (env : ProverEnvironment (F circomPrime))
    (xT xA : Var Emu (F circomPrime)) : ℕ :=
  2 * P256 + evalEmu env xT - evalEmu env xA

def chVal (env : ProverEnvironment (F circomPrime))
    (yT yA : Var Emu (F circomPrime)) : ℕ :=
  2 * P256 + evalEmu env yT - evalEmu env yA

def invModP (a : ℕ) : ℕ := (((a : ℕ) : Fp)⁻¹).val

def tsq2Val (xAv : ℕ) : ℕ := ((xAv * xAv % P256) * ((P256 + 1) / 2)) % P256

def lamVal (e n : Bool) (tsq2v yAv dfv chv : ℕ) : ℕ :=
  if e then
    if n then 3 * tsq2v % P256
    else 3 * tsq2v % P256 * invModP yAv % P256
  else chv * invModP dfv % P256

def lamValEnv (env : ProverEnvironment (F circomPrime))
    (xT xA yT yA : Var Emu (F circomPrime)) : ℕ :=
  lamVal (dFullVal env xT xA % P256 == 0)
    ((evalEmu env yA + evalEmu env yT) % P256 == 0)
    (tsq2Val (evalEmu env xA)) (evalEmu env yA)
    (dFullVal env xT xA) (chVal env yT yA)

def slopeQuot (env : ProverEnvironment (F circomPrime))
    (xT xA yT yA : Var Emu (F circomPrime)) : ℕ :=
  let df := dFullVal env xT xA
  let ef := df % P256 == 0
  let nf := (evalEmu env yA + evalEmu env yT) % P256 == 0
  let t2 := tsq2Val (evalEmu env xA)
  let lv := lamValEnv env xT xA yT yA
  let denv := if ef && nf then 1 else if ef then evalEmu env yA else df
  let nump := if ef then 3 * t2 else chVal env yT yA
  (lv * denv + 8 * P256 - nump) / P256

def x3Val (env : ProverEnvironment (F circomPrime))
    (xT xA yT yA : Var Emu (F circomPrime)) : ℕ :=
  let lv := lamValEnv env xT xA yT yA
  (lv * lv + 4 * P256 - evalEmu env xA - evalEmu env xT) % P256

def x3Quot (env : ProverEnvironment (F circomPrime))
    (xT xA yT yA : Var Emu (F circomPrime)) : ℕ :=
  let lv := lamValEnv env xT xA yT yA
  (lv * lv + 4 * P256 - evalEmu env xA - evalEmu env xT) / P256

def y3Val (env : ProverEnvironment (F circomPrime))
    (xT xA yT yA : Var Emu (F circomPrime)) : ℕ :=
  let lv := lamValEnv env xT xA yT yA
  let xd0v := evalEmu env xA + (2 ^ 256 - 1) - x3Val env xT xA yT yA
  (lv * xd0v + 2 ^ 35 * P256 - evalEmu env yA - c976 * lv) % P256

def y3Quot (env : ProverEnvironment (F circomPrime))
    (xT xA yT yA : Var Emu (F circomPrime)) : ℕ :=
  let lv := lamValEnv env xT xA yT yA
  let xd0v := evalEmu env xA + (2 ^ 256 - 1) - x3Val env xT xA yT yA
  (lv * xd0v + 2 ^ 35 * P256 - evalEmu env yA - c976 * lv) / P256

structure Inputs (F : Type) where
  A : FlaggedPoint F
  T : Select.AffPoint F
deriving ProvableStruct

def NormPoint (P : FlaggedPoint (F circomPrime)) : Prop :=
  IsBool P.isInf ∧ P.x.Normalized limbBits ∧ P.y.Normalized limbBits ∧
  (P.isInf = 0 →
    Specs.ShortWeierstrass.OnCurve Specs.Secp256k1.curve
      { x := decodeFe P.x, y := decodeFe P.y }) ∧
  (P.isInf = 1 → P.x.value limbBits = 0 ∧ P.y.value limbBits = 0)

def TValid (T : Select.AffPoint (F circomPrime)) : Prop :=
  Fe.Valid T.x ∧ Fe.Valid T.y ∧
  Specs.ShortWeierstrass.OnCurve Specs.Secp256k1.curve
    { x := decodeFe T.x, y := decodeFe T.y }

def Assumptions (input : Inputs (F circomPrime)) : Prop :=
  NormPoint input.A ∧ TValid input.T

def Spec (input : Inputs (F circomPrime)) (out : FlaggedPoint (F circomPrime)) : Prop :=
  NormPoint out ∧
    decodePoint out =
      Specs.ShortWeierstrass.add Specs.Secp256k1.curve
        (decodePoint input.A)
        (.affine { x := decodeFe input.T.x, y := decodeFe input.T.y })

end CompactAdd
end Solution.Secp256k1ScalarMulFixedBase

end DonorFile1_7

-- Adapted donor module: CompactAddR1CS
section DonorFile1_8

namespace Solution.Secp256k1ScalarMulFixedBase
namespace CompactAdd

open Challenge.CostR1CS
open Cost

attribute [local irreducible] isR1CSRow r1csProducts operationsIsR1CS flatOperationsIsR1CS

theorem degree_cExp (v k : ℕ) : degree (cExp v k) = 0 := degree_const _

theorem affine_cExp (v k : ℕ) : Affine (cExp v k) := Affine.const _

theorem affine_qpCoeff {q : Var Emu (F circomPrime)} {qt : Expression (F circomPrime)}
    (hq : AffineW q) (hqt : Affine qt) (k : ℕ) :
    Affine (qpCoeff q qt k) := by
  unfold qpCoeff
  refine Affine.add (Affine.add (Affine.add (Affine.add (Affine.add (Affine.add
    (Affine.add ?_ ?_) ?_) ?_) ?_) ?_) ?_) ?_
  · split
    · rename_i h; exact Affine.mul_deg0 (hq _ h) (degree_cExp _ _)
    · exact Affine.zero
  · split
    · rename_i h; exact Affine.mul_deg0 (hq _ h.2) (degree_cExp _ _)
    · exact Affine.zero
  · split
    · rename_i h; exact Affine.mul_deg0 (hq _ h.2) (degree_cExp _ _)
    · exact Affine.zero
  · split
    · rename_i h; exact Affine.mul_deg0 (hq _ h.2) (degree_cExp _ _)
    · exact Affine.zero
  all_goals
    split
    · exact Affine.mul_deg0 hqt (degree_cExp _ _)
    · exact Affine.zero

end CompactAdd
end Solution.Secp256k1ScalarMulFixedBase

end DonorFile1_8

-- Adapted donor module: IncompleteAdd
section DonorFile1_9

namespace Solution.Secp256k1ScalarMulFixedBase
namespace IncompleteAdd

def NormAff (P : Select.AffPoint (F circomPrime)) : Prop :=
  P.x.Normalized limbBits ∧ P.y.Normalized limbBits ∧
  Specs.ShortWeierstrass.OnCurve Specs.Secp256k1.curve
    { x := decodeFe P.x, y := decodeFe P.y }

end IncompleteAdd
end Solution.Secp256k1ScalarMulFixedBase

end DonorFile1_9

-- Adapted donor module: BorrowFree
section DonorFile1_10

/-! # Borrow-free fat-limb digit vector for `2·P256`

Pilot library for the chord-denominator de-re-limbing lever (see
`COST_NOTES.md` §BORROW-PILOT). Ported from the leader's `Params.lean`
(`twoPBorrowDigit`) and `CompleteAddTheorems.lean` (the `limb_borrow_*`/
`value_borrow` family) — verbatim in shape, since both trees target the same
`P256 = Specs.Secp256k1.p`. Proof-side only: this file adds zero circuit
cells, it only supplies the value/bound bridging lemmas needed to consume a
wire-only combination `xT[k] + twoPBorrowDigit k − xA[k]` directly (no fresh
witness, no `NormalizeImplicit`, no separate top digit) in place of a
freshly-witnessed canonical `d`.
-/

namespace Solution.Secp256k1ScalarMulFixedBase

/-- Borrow-free digit `k` of `2·P256` over `numLimbs = 4` positions: every
digit lies in `[2^64, 2^65)`, so a limb-wise `X[k] + (D_k − Y[k])` never
wraps below zero (for canonical `X, Y < 2^64`) and stays under `3·2^64`,
while the weighted digit sum is exactly `2·P256`. -/
def twoPBorrowDigit (k : ℕ) : ℕ :=
  if k = 0 then 2 ^ 65 - 2 ^ 33 - 1954 else 2 ^ 65 - 2

lemma twoPBorrowDigit_ge (k : ℕ) : 2 ^ limbBits ≤ twoPBorrowDigit k := by
  unfold twoPBorrowDigit; split <;> decide

lemma twoPBorrowDigit_lt (k : ℕ) : twoPBorrowDigit k < 2 ^ 65 := by
  unfold twoPBorrowDigit; split <;> decide

lemma twoPBorrowDigit_sum :
    (∑ k ∈ Finset.range numLimbs, twoPBorrowDigit k * 2 ^ (limbBits * k)) = 2 * P256 := by
  simp only [numLimbs, Finset.sum_range_succ, Finset.sum_range_zero, twoPBorrowDigit]
  decide

end Solution.Secp256k1ScalarMulFixedBase

end DonorFile1_10

-- Adapted donor module: PairAdd
section DonorFile1_11

namespace Solution.Secp256k1ScalarMulFixedBase
namespace PairAdd

open CompactAdd (cExp qpCoeff dFullVal chVal lamVal invModP lamValEnv slopeQuot
  x3Val x3Quot y3Val y3Quot cK c976)

/-- §BORROW-PILOT: `dtil = xT + twoPBorrowDigit − xA` is a wire-only
combination (zero fresh witnesses, zero constraints) representing the exact
same integer value as the old canonicalized `d` (`dFullVal = xT − xA + 2p`),
but with fat limbs (`< 3·2^64` each, vs `< 2^64` canonical). Feeding it
directly into `interpolatedMul` skips `NormalizeImplicit(d)` + the `gfLin`
carry identity + the `d4` top digit + the `lp = lam*d4` cross term entirely
(see `COST_NOTES.md` §BORROW-PILOT for the per-site arithmetic). -/
def dtilOf (xT xA : Var Emu (F circomPrime)) : Var Emu (F circomPrime) :=
  Vector.ofFn fun i : Fin 4 =>
    xT[i.val]'i.isLt
      + (((twoPBorrowDigit i.val : ℕ) : F circomPrime) : Expression (F circomPrime))
      - xA[i.val]'i.isLt

def stageA (xA yA xT yT : Var Emu (F circomPrime)) :
    Circuit (F circomPrime) (Var Emu (F circomPrime)) := do

  let lam ← ProvableType.witness (α := Emu) fun env =>
    emuOfNat (lamValEnv env xT xA yT yA)
  NormalizeImplicit.circuit secpParams lam
  let qs ← ProvableType.witness (α := Emu) fun env =>
    emuOfNat (slopeQuot env xT xA yT yA % 2 ^ 256)
  let qst ← ProvableType.witness (α := field) fun env =>
    ((slopeQuot env xT xA yT yA / 2 ^ 256 : ℕ) : F circomPrime)
  NormalizeImplicit.circuit secpParams qs
  assertion (RangeCheck.circuit 2 (by decide) (by decide)) qst
  let convLD ← MulMod.interpolatedMul lam (dtilOf xT xA)
  GroupedFlex.circuit 64 gfQuadFat posOfQuadFat 5 vQuadFat vQuadFat hgvQuadFat (by norm_num) {
    lhs := Vector.mapFinRange 9 fun k =>
      (if h : k.val < 7 then convLD[k.val] else 0)
        + (if k.val < 5 then cExp (8 * P256) k.val else 0)
    rhs := Vector.mapFinRange 9 fun k =>
      qpCoeff qs qst k.val
        + (if h : k.val < 4 then
            yT[k.val]'h - yA[k.val]'h
              + (((2 ^ 64 - 1 + limbOfNat cK k.val : ℕ) : F circomPrime) :
                  Expression (F circomPrime))
           else 0) }
  return lam

syntax "stageA_simp" : tactic
macro_rules
  | `(tactic| stageA_simp) =>
    `(tactic| simp +arith (maxSteps := 4000000) only
        [stageA, dtilOf, MulMod.witnessedMul, MulMod.interpolatedMul, circuit_norm,
         NormalizeImplicit.circuit, NormalizeImplicit.elaborated,
         EqViaCarriesFlex.circuit, EqViaCarriesFlex.elaborated,
         GroupedFlex.circuit, GroupedFlex.elaborated, GroupedFlex.main,
         gfQuadFat, posOfQuadFat, vQuadFat, wfQuadFat, hgvQuadFat,
         GroupedFlex.widthAllocFrom, GroupedFlex.widthConsFrom,
         secpParams, RangeCheck.circuit, RangeCheck.elaborated, numLimbs, limbBits])

lemma stageA_localLength (xA yA xT yT : Var Emu (F circomPrime)) (n : ℕ) :
    Operations.localLength (stageA xA yA xT yT n).2 = 725 := by
  stageA_simp

lemma stageA_output (xA yA xT yT : Var Emu (F circomPrime)) (n : ℕ) :
    (stageA xA yA xT yT n).1 = varFromOffset Emu n := by
  stageA_simp

lemma stageA_subcircuitsConsistent (xA yA xT yT : Var Emu (F circomPrime)) (n : ℕ) :
    Operations.forAll n { subcircuit := fun offset {m} _ => m = offset }
      (stageA xA yA xT yT n).2 := by stageA_simp

lemma stageA_chanG (xA yA xT yT : Var Emu (F circomPrime)) (n : ℕ) :
    Operations.subcircuitChannelsWithGuarantees (stageA xA yA xT yT n).2 = [] := by
  stageA_simp

lemma stageA_chanR (xA yA xT yT : Var Emu (F circomPrime)) (n : ℕ) :
    Operations.subcircuitChannelsWithRequirements (stageA xA yA xT yT n).2 = [] := by
  stageA_simp

lemma stageA_shallow (xA yA xT yT : Var Emu (F circomPrime)) (n : ℕ) :
    Operations.shallowChannels (stageA xA yA xT yT n).2 = [] := by
  stageA_simp

lemma stageA_guar (xA yA xT yT : Var Emu (F circomPrime)) (n : ℕ)
    (env : Environment (F circomPrime)) :
    Operations.forAllNoOffset { interact := fun i => i.Guarantees env }
      (stageA xA yA xT yT n).2 := by stageA_simp

lemma stageA_req (xA yA xT yT : Var Emu (F circomPrime)) (n : ℕ)
    (env : Environment (F circomPrime)) :
    Operations.forAllNoOffset { interact := fun i => i.Requirements env }
      (stageA xA yA xT yT n).2 := by stageA_simp

lemma stageA_subLawful (xA yA xT yT : Var Emu (F circomPrime)) (n : ℕ) :
    Operations.forAllNoOffset { subcircuit := fun {m} s => s.ChannelsLawful }
      (stageA xA yA xT yT n).2 := by stageA_simp

structure Inputs (F : Type) where
  A : Select.AffPoint F
  T1 : Select.AffPoint F
  T2 : Select.AffPoint F
deriving ProvableStruct

def y1W (env : ProverEnvironment (F circomPrime))
    (xA yA x1 lam1 : Var Emu (F circomPrime)) : ℕ :=
  (evalEmu env lam1 * (evalEmu env xA + (2 ^ 256 - 1) - evalEmu env x1)
    + 2 ^ 35 * P256 - evalEmu env yA - c976 * evalEmu env lam1) % P256

def lam2W (env : ProverEnvironment (F circomPrime))
    (xA yA x1 lam1 xT2 yT2 : Var Emu (F circomPrime)) : ℕ :=
  (2 * P256 + evalEmu env yT2 - y1W env xA yA x1 lam1)
    * invModP (dFullVal env xT2 x1) % P256

def slope2Quot (env : ProverEnvironment (F circomPrime))
    (xA yA x1 lam1 xT2 yT2 : Var Emu (F circomPrime)) : ℕ :=
  (lam2W env xA yA x1 lam1 xT2 yT2 * dFullVal env xT2 x1
    + evalEmu env lam1 * (evalEmu env xA + (2 ^ 256 - 1) - evalEmu env x1)
    + 2 ^ 34 * P256 - evalEmu env yT2 - evalEmu env yA
    - c976 * evalEmu env lam1) / P256

def x2W (env : ProverEnvironment (F circomPrime))
    (x1 xT2 lam2 : Var Emu (F circomPrime)) : ℕ :=
  (evalEmu env lam2 * evalEmu env lam2 + 4 * P256
    - evalEmu env x1 - evalEmu env xT2) % P256

def x2Quot (env : ProverEnvironment (F circomPrime))
    (x1 xT2 lam2 : Var Emu (F circomPrime)) : ℕ :=
  (evalEmu env lam2 * evalEmu env lam2 + 4 * P256
    - evalEmu env x1 - evalEmu env xT2) / P256

def y32W (env : ProverEnvironment (F circomPrime))
    (xT2 yT2 lam2 x2 : Var Emu (F circomPrime)) : ℕ :=
  (evalEmu env lam2 * (evalEmu env xT2 + (2 ^ 256 - 1) - evalEmu env x2)
    + 2 ^ 35 * P256 - evalEmu env yT2 - c976 * evalEmu env lam2) % P256

def y32Quot (env : ProverEnvironment (F circomPrime))
    (xT2 yT2 lam2 x2 : Var Emu (F circomPrime)) : ℕ :=
  (evalEmu env lam2 * (evalEmu env xT2 + (2 ^ 256 - 1) - evalEmu env x2)
    + 2 ^ 35 * P256 - evalEmu env yT2 - c976 * evalEmu env lam2) / P256

def stageO2 (xA yA xT1 yT1 lam1 : Var Emu (F circomPrime)) :
    Circuit (F circomPrime) (Var Emu (F circomPrime)) := do
  let x1 ← ProvableType.witness (α := Emu) fun env =>
    emuOfNat (x3Val env xT1 xA yT1 yA)
  NormalizeImplicit.circuit secpParams x1
  let q6 ← ProvableType.witness (α := Emu) fun env =>
    emuOfNat (x3Quot env xT1 xA yT1 yA % 2 ^ 256)
  let q6t ← ProvableType.witness (α := field) fun env =>
    ((x3Quot env xT1 xA yT1 yA / 2 ^ 256 : ℕ) : F circomPrime)
  NormalizeImplicit.circuit secpParams q6
  assertion (RangeCheck.circuit 1 (by decide) (by decide)) q6t
  let convLL ← MulMod.interpolatedMul lam1 lam1
  GroupedFlex.circuit 64 gfQuad posOfQuad 5 vQuad vQuad hgvQuad (by norm_num) {
    lhs := Vector.mapFinRange 9 fun k =>
      (if h : k.val < 7 then convLL[k.val] else 0)
        + (if k.val < 5 then cExp (4 * P256) k.val else 0)
    rhs := Vector.mapFinRange 9 fun k =>
      qpCoeff q6 q6t k.val
        + (if h : k.val < 4 then x1[k.val] + xA[k.val] + xT1[k.val] else 0) }
  return x1

/-- §BORROW-ROLLOUT (d2 site): the chord denominator `d2 = xT2 − x1 + 2p` is
now the wire-only fat combination `dtilOf xT2 x1` fed directly into
`interpolatedMul`, exactly like stageA's `d` — no `d2`/`d24` witnesses, no
`NormalizeImplicit`/`RangeCheck`/`gfLin` re-limbing, no `lp2` cross term.
The wide identity's tent fattens `gfWide (423) → gfWideFat (429)`. -/
def stageC1 (xA yA x1 lam1 xT2 yT2 : Var Emu (F circomPrime)) :
    Circuit (F circomPrime) (Var Emu (F circomPrime)) := do

  let lam2 ← ProvableType.witness (α := Emu) fun env =>
    emuOfNat (lam2W env xA yA x1 lam1 xT2 yT2)
  NormalizeImplicit.circuit secpParams lam2
  let q3 ← ProvableType.witness (α := Emu) fun env =>
    emuOfNat (slope2Quot env xA yA x1 lam1 xT2 yT2 % 2 ^ 256)
  let q3t ← ProvableType.witness (α := field) fun env =>
    ((slope2Quot env xA yA x1 lam1 xT2 yT2 / 2 ^ 256 : ℕ) : F circomPrime)
  NormalizeImplicit.circuit secpParams q3
  assertion (RangeCheck.circuit 3 (by decide) (by decide)) q3t

  let xd1 : Var Emu (F circomPrime) :=
    Vector.ofFn fun i : Fin 4 =>
      xA[i.val]'i.isLt
        + (((2 ^ 64 - 1 : ℕ) : F circomPrime) : Expression (F circomPrime))
        - x1[i.val]'i.isLt
  let convLX1 ← MulMod.interpolatedMul lam1 xd1
  let convLD2 ← MulMod.interpolatedMul lam2 (dtilOf xT2 x1)
  GroupedFlex.circuit 64 gfWideFat posOfWideFat 6 vWideFat vWideFat hgvWideFat (by norm_num) {
    lhs := Vector.mapFinRange 10 fun k =>
      (if h : k.val < 7 then convLD2[k.val] + convLX1[k.val] else 0)
        + (if k.val < 5 then cExp (2 ^ 34 * P256) k.val else 0)
    rhs := Vector.mapFinRange 10 fun k =>
      qpCoeff q3 q3t k.val
        + (if h : k.val < 4 then
            yT2[k.val] + yA[k.val]
              + ((c976 : ℕ) : F circomPrime) * (lam1[k.val]'h) else 0) }
  return lam2

def stageC2 (x1 xT2 yT2 lam2 : Var Emu (F circomPrime)) :
    Circuit (F circomPrime)
      (Var Emu (F circomPrime) × Var Emu (F circomPrime)) := do

  let x2 ← ProvableType.witness (α := Emu) fun env =>
    emuOfNat (x2W env x1 xT2 lam2)
  NormalizeImplicit.circuit secpParams x2
  let q6 ← ProvableType.witness (α := Emu) fun env =>
    emuOfNat (x2Quot env x1 xT2 lam2 % 2 ^ 256)
  let q6t ← ProvableType.witness (α := field) fun env =>
    ((x2Quot env x1 xT2 lam2 / 2 ^ 256 : ℕ) : F circomPrime)
  NormalizeImplicit.circuit secpParams q6
  assertion (RangeCheck.circuit 1 (by decide) (by decide)) q6t
  let convLL ← MulMod.interpolatedMul lam2 lam2
  GroupedFlex.circuit 64 gfQuad posOfQuad 5 vQuad vQuad hgvQuad (by norm_num) {
    lhs := Vector.mapFinRange 9 fun k =>
      (if h : k.val < 7 then convLL[k.val] else 0)
        + (if k.val < 5 then cExp (4 * P256) k.val else 0)
    rhs := Vector.mapFinRange 9 fun k =>
      qpCoeff q6 q6t k.val
        + (if h : k.val < 4 then x2[k.val] + x1[k.val] + xT2[k.val] else 0) }

  let xd2 : Var Emu (F circomPrime) :=
    Vector.ofFn fun i : Fin 4 =>
      xT2[i.val]'i.isLt
        + (((2 ^ 64 - 1 : ℕ) : F circomPrime) : Expression (F circomPrime))
        - x2[i.val]'i.isLt
  let y3 ← ProvableType.witness (α := Emu) fun env =>
    emuOfNat (y32W env xT2 yT2 lam2 x2)
  NormalizeImplicit.circuit secpParams y3
  let q7 ← ProvableType.witness (α := Emu) fun env =>
    emuOfNat (y32Quot env xT2 yT2 lam2 x2 % 2 ^ 256)
  let q7t ← ProvableType.witness (α := field) fun env =>
    ((y32Quot env xT2 yT2 lam2 x2 / 2 ^ 256 : ℕ) : F circomPrime)
  NormalizeImplicit.circuit secpParams q7
  assertion (RangeCheck.circuit 3 (by decide) (by decide)) q7t
  let convLX2 ← MulMod.interpolatedMul lam2 xd2
  GroupedFlex.circuit 64 gfWide posOfWide 6 vWide vWide hgvWide (by norm_num) {
    lhs := Vector.mapFinRange 10 fun k =>
      (if h : k.val < 7 then convLX2[k.val] else 0)
        + (if k.val < 5 then cExp (2 ^ 35 * P256) k.val else 0)
    rhs := Vector.mapFinRange 10 fun k =>
      qpCoeff q7 q7t k.val
        + (if h : k.val < 4 then
            y3[k.val] + yT2[k.val]
              + ((c976 : ℕ) : F circomPrime) * (lam2[k.val]'h) else 0) }
  return (x2, y3)

syntax "pair_add_simp" : tactic
macro_rules
  | `(tactic| pair_add_simp) =>
    `(tactic| simp +arith (maxSteps := 4000000) only
        [stageO2, stageC1, stageC2, dtilOf, MulMod.witnessedMul, MulMod.interpolatedMul, circuit_norm,
         NormalizeImplicit.circuit, NormalizeImplicit.elaborated,
         EqViaCarriesFlex.circuit, EqViaCarriesFlex.elaborated,
         GroupedFlex.circuit, GroupedFlex.elaborated, GroupedFlex.main,
         gfLin, posOfLin, vLin, wfLin, hgvLin,
         gfQuad, posOfQuad, vQuad, wfQuad, hgvQuad,
         gfWide, posOfWide, vWide, wfWide, hgvWide,
         gfWideFat, posOfWideFat, vWideFat, wfWideFat, hgvWideFat,
         GroupedFlex.widthAllocFrom, GroupedFlex.widthConsFrom,
         secpParams, RangeCheck.circuit, RangeCheck.elaborated, numLimbs, limbBits])

lemma stageO2_localLength (xA yA xT1 yT1 lam1 : Var Emu (F circomPrime)) (n : ℕ) :
    Operations.localLength (stageO2 xA yA xT1 yT1 lam1 n).2 = 721 := by
  pair_add_simp

lemma stageO2_output (xA yA xT1 yT1 lam1 : Var Emu (F circomPrime)) (n : ℕ) :
    (stageO2 xA yA xT1 yT1 lam1 n).1 = varFromOffset Emu n := by pair_add_simp

lemma stageO2_subcircuitsConsistent (xA yA xT1 yT1 lam1 : Var Emu (F circomPrime)) (n : ℕ) :
    Operations.forAll n { subcircuit := fun offset {m} _ => m = offset }
      (stageO2 xA yA xT1 yT1 lam1 n).2 := by pair_add_simp

lemma stageO2_chanG (xA yA xT1 yT1 lam1 : Var Emu (F circomPrime)) (n : ℕ) :
    Operations.subcircuitChannelsWithGuarantees (stageO2 xA yA xT1 yT1 lam1 n).2 = [] := by
  pair_add_simp

lemma stageO2_chanR (xA yA xT1 yT1 lam1 : Var Emu (F circomPrime)) (n : ℕ) :
    Operations.subcircuitChannelsWithRequirements (stageO2 xA yA xT1 yT1 lam1 n).2 = [] := by
  pair_add_simp

lemma stageO2_shallow (xA yA xT1 yT1 lam1 : Var Emu (F circomPrime)) (n : ℕ) :
    Operations.shallowChannels (stageO2 xA yA xT1 yT1 lam1 n).2 = [] := by
  pair_add_simp

lemma stageO2_guar (xA yA xT1 yT1 lam1 : Var Emu (F circomPrime)) (n : ℕ)
    (env : Environment (F circomPrime)) :
    Operations.forAllNoOffset { interact := fun i => i.Guarantees env }
      (stageO2 xA yA xT1 yT1 lam1 n).2 := by pair_add_simp

lemma stageO2_req (xA yA xT1 yT1 lam1 : Var Emu (F circomPrime)) (n : ℕ)
    (env : Environment (F circomPrime)) :
    Operations.forAllNoOffset { interact := fun i => i.Requirements env }
      (stageO2 xA yA xT1 yT1 lam1 n).2 := by pair_add_simp

lemma stageO2_subLawful (xA yA xT1 yT1 lam1 : Var Emu (F circomPrime)) (n : ℕ) :
    Operations.forAllNoOffset { subcircuit := fun {m} s => s.ChannelsLawful }
      (stageO2 xA yA xT1 yT1 lam1 n).2 := by pair_add_simp

lemma stageC1_localLength (xA yA x1 lam1 xT2 yT2 : Var Emu (F circomPrime)) (n : ℕ) :
    Operations.localLength (stageC1 xA yA x1 lam1 xT2 yT2 n).2 = 741 := by
  pair_add_simp

lemma stageC1_output (xA yA x1 lam1 xT2 yT2 : Var Emu (F circomPrime)) (n : ℕ) :
    (stageC1 xA yA x1 lam1 xT2 yT2 n).1 = varFromOffset Emu n := by
  pair_add_simp

lemma stageC1_subcircuitsConsistent (xA yA x1 lam1 xT2 yT2 : Var Emu (F circomPrime)) (n : ℕ) :
    Operations.forAll n { subcircuit := fun offset {m} _ => m = offset }
      (stageC1 xA yA x1 lam1 xT2 yT2 n).2 := by pair_add_simp

lemma stageC1_chanG (xA yA x1 lam1 xT2 yT2 : Var Emu (F circomPrime)) (n : ℕ) :
    Operations.subcircuitChannelsWithGuarantees (stageC1 xA yA x1 lam1 xT2 yT2 n).2 = [] := by
  pair_add_simp

lemma stageC1_chanR (xA yA x1 lam1 xT2 yT2 : Var Emu (F circomPrime)) (n : ℕ) :
    Operations.subcircuitChannelsWithRequirements (stageC1 xA yA x1 lam1 xT2 yT2 n).2 = [] := by
  pair_add_simp

lemma stageC1_shallow (xA yA x1 lam1 xT2 yT2 : Var Emu (F circomPrime)) (n : ℕ) :
    Operations.shallowChannels (stageC1 xA yA x1 lam1 xT2 yT2 n).2 = [] := by
  pair_add_simp

lemma stageC1_guar (xA yA x1 lam1 xT2 yT2 : Var Emu (F circomPrime)) (n : ℕ)
    (env : Environment (F circomPrime)) :
    Operations.forAllNoOffset { interact := fun i => i.Guarantees env }
      (stageC1 xA yA x1 lam1 xT2 yT2 n).2 := by pair_add_simp

lemma stageC1_req (xA yA x1 lam1 xT2 yT2 : Var Emu (F circomPrime)) (n : ℕ)
    (env : Environment (F circomPrime)) :
    Operations.forAllNoOffset { interact := fun i => i.Requirements env }
      (stageC1 xA yA x1 lam1 xT2 yT2 n).2 := by pair_add_simp

lemma stageC1_subLawful (xA yA x1 lam1 xT2 yT2 : Var Emu (F circomPrime)) (n : ℕ) :
    Operations.forAllNoOffset { subcircuit := fun {m} s => s.ChannelsLawful }
      (stageC1 xA yA x1 lam1 xT2 yT2 n).2 := by pair_add_simp

lemma stageC2_localLength (x1 xT2 yT2 lam2 : Var Emu (F circomPrime)) (n : ℕ) :
    Operations.localLength (stageC2 x1 xT2 yT2 lam2 n).2 = 1452 := by
  pair_add_simp

lemma stageC2_output (x1 xT2 yT2 lam2 : Var Emu (F circomPrime)) (n : ℕ) :
    (stageC2 x1 xT2 yT2 lam2 n).1
      = (varFromOffset Emu n, varFromOffset Emu (n + 721)) := by pair_add_simp

lemma stageC2_subcircuitsConsistent (x1 xT2 yT2 lam2 : Var Emu (F circomPrime)) (n : ℕ) :
    Operations.forAll n { subcircuit := fun offset {m} _ => m = offset }
      (stageC2 x1 xT2 yT2 lam2 n).2 := by pair_add_simp

lemma stageC2_chanG (x1 xT2 yT2 lam2 : Var Emu (F circomPrime)) (n : ℕ) :
    Operations.subcircuitChannelsWithGuarantees (stageC2 x1 xT2 yT2 lam2 n).2 = [] := by
  pair_add_simp

lemma stageC2_chanR (x1 xT2 yT2 lam2 : Var Emu (F circomPrime)) (n : ℕ) :
    Operations.subcircuitChannelsWithRequirements (stageC2 x1 xT2 yT2 lam2 n).2 = [] := by
  pair_add_simp

lemma stageC2_shallow (x1 xT2 yT2 lam2 : Var Emu (F circomPrime)) (n : ℕ) :
    Operations.shallowChannels (stageC2 x1 xT2 yT2 lam2 n).2 = [] := by
  pair_add_simp

lemma stageC2_guar (x1 xT2 yT2 lam2 : Var Emu (F circomPrime)) (n : ℕ)
    (env : Environment (F circomPrime)) :
    Operations.forAllNoOffset { interact := fun i => i.Guarantees env }
      (stageC2 x1 xT2 yT2 lam2 n).2 := by pair_add_simp

lemma stageC2_req (x1 xT2 yT2 lam2 : Var Emu (F circomPrime)) (n : ℕ)
    (env : Environment (F circomPrime)) :
    Operations.forAllNoOffset { interact := fun i => i.Requirements env }
      (stageC2 x1 xT2 yT2 lam2 n).2 := by pair_add_simp

lemma stageC2_subLawful (x1 xT2 yT2 lam2 : Var Emu (F circomPrime)) (n : ℕ) :
    Operations.forAllNoOffset { subcircuit := fun {m} s => s.ChannelsLawful }
      (stageC2 x1 xT2 yT2 lam2 n).2 := by pair_add_simp

def main (input : Var Inputs (F circomPrime)) :
    Circuit (F circomPrime) (Var Select.AffPoint (F circomPrime)) := do
  let { A, T1, T2 } := input
  let lam1 ← stageA A.x A.y T1.x T1.y
  let x1 ← stageO2 A.x A.y T1.x T1.y lam1
  let lam2 ← stageC1 A.x A.y x1 lam1 T2.x T2.y
  let (x2, y3) ← stageC2 x1 T2.x T2.y lam2
  return { x := x2, y := y3 }

set_option maxHeartbeats 8000000 in
instance elaborated : ElaboratedCircuit (F circomPrime) Inputs Select.AffPoint main where
  localLength _ := 3639
  output _ i0 :=
    { x := varFromOffset Emu (i0 + 2187), y := varFromOffset Emu (i0 + 2908) }
  localLength_eq := by
    intro input offset
    simp +arith only [main, circuit_norm,
      stageA_localLength, stageA_output,
      stageO2_localLength, stageO2_output, stageC1_localLength, stageC1_output,
      stageC2_localLength, stageC2_output]
  output_eq := by
    intro input offset
    simp +arith only [main, circuit_norm,
      stageA_localLength, stageA_output,
      stageO2_localLength, stageO2_output, stageC1_localLength, stageC1_output,
      stageC2_output]
  subcircuitsConsistent := by
    intro input offset
    simp +arith only [main, circuit_norm, Operations.forAll_append,
      stageA_localLength, stageA_output,
      stageO2_localLength, stageO2_output, stageC1_localLength, stageC1_output,
      stageC2_output,
      stageA_subcircuitsConsistent, stageO2_subcircuitsConsistent,
      stageC1_subcircuitsConsistent, stageC2_subcircuitsConsistent]
  channelsLawful := by
    intro input offset
    simp +arith only [main, circuit_norm,
      stageA_localLength, stageA_output,
      stageO2_localLength, stageO2_output, stageC1_localLength, stageC1_output,
      stageC2_output,
      stageA_chanG, stageO2_chanG, stageC1_chanG, stageC2_chanG,
      stageA_chanR, stageO2_chanR, stageC1_chanR, stageC2_chanR,
      stageA_shallow, stageO2_shallow, stageC1_shallow, stageC2_shallow,
      stageA_guar, stageO2_guar, stageC1_guar, stageC2_guar,
      stageA_req, stageO2_req, stageC1_req, stageC2_req,
      stageA_subLawful, stageO2_subLawful, stageC1_subLawful,
      stageC2_subLawful, List.nil_subset, List.not_mem_nil, List.append_nil,
      List.nil_append]

open IncompleteAdd (NormAff)

def Assumptions (input : Inputs (F circomPrime)) : Prop :=
  NormAff input.A ∧ CompactAdd.TValid input.T1 ∧ CompactAdd.TValid input.T2 ∧
  decodeFe input.A.x ≠ decodeFe input.T1.x ∧
  (Specs.ShortWeierstrass.chord
      { x := decodeFe input.A.x, y := decodeFe input.A.y }
      { x := decodeFe input.T1.x, y := decodeFe input.T1.y }).x
    ≠ decodeFe input.T2.x

def Spec (input : Inputs (F circomPrime)) (out : Select.AffPoint (F circomPrime)) : Prop :=
  NormAff out ∧
    Specs.ShortWeierstrass.GroupPoint.affine
        ({ x := decodeFe out.x, y := decodeFe out.y } :
          Specs.ShortWeierstrass.Point Specs.Secp256k1.Fp)
      = Specs.ShortWeierstrass.add Specs.Secp256k1.curve
          (Specs.ShortWeierstrass.add Specs.Secp256k1.curve
            (.affine { x := decodeFe input.A.x, y := decodeFe input.A.y })
            (.affine { x := decodeFe input.T1.x, y := decodeFe input.T1.y }))
          (.affine { x := decodeFe input.T2.x, y := decodeFe input.T2.y })

end PairAdd
end Solution.Secp256k1ScalarMulFixedBase

end DonorFile1_11

-- Adapted donor module: GroupedFlexNoTop
section DonorFile1_12

/-!
# `GroupedFlex` without the final native row

`GroupedFlex.main` emits a grouped carry loop followed by ONE extra row,

  `assertZero (∑ₖ (lhsₖ - rhsₖ) · (2^B)^k)`,

which pins the identity in the native field.  At every call site where the
folded quotient has already been *inverted* — i.e. written as an affine
expression over already-allocated wires rather than witnessed — that row is
identically zero as a polynomial in the wires, so it carries no information.

`mainNoTop` drops it.  The information it used to supply is instead demanded
as an extra *assumption* (`LinIdent`) on the evaluated inputs, which the caller
discharges by `ring` from the definition of the inverted quotient.
-/

namespace Solution.Secp256k1ScalarMulFixedBase

section
variable {p : ℕ} [Fact p.Prime]
variable {L : ℕ} [NeZero L]

namespace GroupedFlex

/-- The linear identity that the deleted final row of `main` used to assert. -/
def LinIdent (B : ℕ) (input : EqViaCarriesFlex.Inputs L (F p)) : Prop :=
  (∑ i : Fin L, input.lhs[i.val] * ((2 : F p) ^ B) ^ i.val)
    = ∑ i : Fin L, input.rhs[i.val] * ((2 : F p) ^ B) ^ i.val

/-- Assumptions of the top-row-free variant: the usual per-position bounds,
plus the native-field identity that the deleted row used to enforce. -/
def AssumptionsNoTop (B : ℕ) (NfL NfR : ℕ → ℕ) (input : EqViaCarriesFlex.Inputs L (F p)) :
    Prop :=
  Assumptions NfL NfR input ∧ LinIdent B input

/-- `GroupedFlex.main` with the final native row removed. -/
def mainNoTop (B : ℕ) (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : VParams)
    (hgv : GVXHyps p L B gf posOf G V VR) [Fact (p > 2)]
    (input : Var (EqViaCarriesFlex.Inputs L) (F p)) :
    Circuit (F p) Unit :=
  carryLoop B gf posOf VR.OFFf V.Wf hgv.2.2.2.1 input.lhs input.rhs (G - 2) 0

omit [NeZero L] in
lemma main_eq_bind_noTop (B : ℕ) (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : VParams)
    (hgv : GVXHyps p L B gf posOf G V VR) [Fact (p > 2)]
    (input : Var (EqViaCarriesFlex.Inputs L) (F p)) :
    main B gf posOf G V VR hgv input
      = (mainNoTop B gf posOf G V VR hgv input >>= fun _ =>
          assertZero
            (polyEvalExpr
              (Vector.ofFn fun j : Fin L =>
                input.lhs[j.val]'j.isLt - input.rhs[j.val]'j.isLt)
              ((2 : F p) ^ B))) := rfl

instance elaboratedNoTop (B : ℕ) (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : VParams)
    (hgv : GVXHyps p L B gf posOf G V VR) [Fact (p > 2)] :
    ElaboratedCircuit (F p) (EqViaCarriesFlex.Inputs L) unit
      (mainNoTop B gf posOf G V VR hgv) where
  localLength _ := widthAllocFrom V.Wf (G - 2) 0
  localLength_eq := by
    intro input offset
    simp only [mainNoTop,
      carryLoop_localLength B gf posOf VR.OFFf V.Wf hgv.2.2.2.1 input.lhs input.rhs]
  subcircuitsConsistent := by
    intro input offset
    exact carryLoop_subcircuitsConsistent B gf posOf VR.OFFf V.Wf hgv.2.2.2.1 _ _ _ _ offset
  channelsLawful := by
    intro input offset
    exact carryLoop_channelsLawful B gf posOf VR.OFFf V.Wf hgv.2.2.2.1 _ _ _ _ _

def circuitNoTop (B : ℕ) (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : VParams)
    (hgv : GVXHyps p L B gf posOf G V VR) (hB1 : 1 ≤ B)
    [Fact (p > 2)] : FormalAssertion (F p) (EqViaCarriesFlex.Inputs L) where
    main := mainNoTop B gf posOf G V VR hgv
    Assumptions := AssumptionsNoTop B V.Nf VR.Nf
    Spec := EqViaCarriesFlex.Spec B
    soundness := by
      intro i₀ env input_var input h_input h_assumptions h_holds
      have ha_e : ∀ (j : ℕ) (hj : j < L),
          Expression.eval env (input_var.lhs[j]'hj) = input.lhs[j]'hj := by
        intro j hj
        simpa [circuit_norm, CircuitType.eval_expression, ProvableType.eval,
          explicit_provable_type, Vector.getElem_map] using
            congrArg (fun x : EqViaCarriesFlex.Inputs L (F p) => x.lhs[j]'hj) h_input
      have hb_e : ∀ (j : ℕ) (hj : j < L),
          Expression.eval env (input_var.rhs[j]'hj) = input.rhs[j]'hj := by
        intro j hj
        simpa [circuit_norm, CircuitType.eval_expression, ProvableType.eval,
          explicit_provable_type, Vector.getElem_map] using
            congrArg (fun x : EqViaCarriesFlex.Inputs L (F p) => x.rhs[j]'hj) h_input
      have hrow : Expression.eval env
          (polyEvalExpr
            (Vector.ofFn fun j : Fin L =>
              input_var.lhs[j.val]'j.isLt - input_var.rhs[j.val]'j.isLt)
            ((2 : F p) ^ B)) = 0 := by
        rw [polyEvalExpr_diff_eval]
        have hl : (∑ i : Fin L, Expression.eval env (input_var.lhs[i.val]'i.isLt)
              * ((2 : F p) ^ B) ^ i.val)
            = ∑ i : Fin L, input.lhs[i.val]'i.isLt * ((2 : F p) ^ B) ^ i.val :=
          Finset.sum_congr rfl (fun i _ => by rw [ha_e i.val i.isLt])
        have hr : (∑ i : Fin L, Expression.eval env (input_var.rhs[i.val]'i.isLt)
              * ((2 : F p) ^ B) ^ i.val)
            = ∑ i : Fin L, input.rhs[i.val]'i.isLt * ((2 : F p) ^ B) ^ i.val :=
          Finset.sum_congr rfl (fun i _ => by rw [hb_e i.val i.isLt])
        rw [hl, hr, h_assumptions.2, sub_self]
      have hfull : ConstraintsHold.Soundness env
          ((main B gf posOf G V VR hgv input_var).operations i₀) := by
        rw [main_eq_bind_noTop, Circuit.bind_operations_eq]
        rw [ConstraintsHold.Soundness, Operations.forAllNoOffset_append]
        refine ⟨h_holds, ?_⟩
        simpa [circuit_norm] using hrow
      obtain ⟨hspec, _⟩ :=
        (circuit B gf posOf G V VR hgv hB1).soundness i₀ env input_var input h_input
          h_assumptions.1 hfull
      refine ⟨hspec, ?_⟩
      exact carryLoop_requirements B gf posOf VR.OFFf V.Wf hgv.2.2.2.1 env
        input_var.lhs input_var.rhs _ _ _
    completeness := by
      intro i₀ env input_var h_uses input h_input h_assumptions h_spec
      have h_uses_full : env.UsesLocalWitnessesCompleteness i₀
          ((main B gf posOf G V VR hgv input_var).operations i₀) := by
        rw [main_eq_bind_noTop]
        simp only [circuit_norm]
        exact h_uses
      have hfull : ConstraintsHold.Completeness env
          ((main B gf posOf G V VR hgv input_var).operations i₀) :=
        (circuit B gf posOf G V VR hgv hB1).completeness i₀ env input_var
          h_uses_full input h_input h_assumptions.1 h_spec
      rw [main_eq_bind_noTop, Circuit.bind_operations_eq, ConstraintsHold.Completeness,
        Operations.forAllNoOffset_append] at hfull
      exact hfull.1

theorem computableWitnessesNoTop (B : ℕ) (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : VParams)
    (hgv : GVXHyps p L B gf posOf G V VR) (hB1 : 1 ≤ B) [Fact (p > 2)] :
    (circuitNoTop B gf posOf G V VR hgv hB1).ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition
      input env env')
    ((mainNoTop B gf posOf G V VR hgv input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold mainNoTop
  exact carryLoop_structuralComputableWitnesses B gf posOf VR.OFFf V.Wf hgv.2.2.2.1 input
    input.lhs input.rhs
    (by
      intro e1 e2 h_parent k
      have hparts :
          (∀ a ∈ input.lhs, Expression.eval e1.toEnvironment a =
              Expression.eval e2.toEnvironment a) ∧
            ∀ a ∈ input.rhs, Expression.eval e1.toEnvironment a =
              Expression.eval e2.toEnvironment a := by
        simpa [circuit_norm, CircuitType.eval_expression_prover_to_verifier,
          CircuitType.eval_expression, ProvableType.eval, explicit_provable_type] using h_parent
      exact carryExpr_eval_stable B gf posOf VR.OFFf input.lhs input.rhs
        e1.toEnvironment e2.toEnvironment
        (fun j hj => hparts.1 _ (by
          simp only [Vector.mem_iff_getElem]
          exact ⟨j, hj, rfl⟩))
        (fun j hj => hparts.2 _ (by
          simp only [Vector.mem_iff_getElem]
          exact ⟨j, hj, rfl⟩)) k)
    env env' (G - 2) 0 offset

end GroupedFlex

end

namespace Cost

open Challenge.CostR1CS

section GroupedXVNoTop
variable {L : ℕ}

theorem costIs_groupedNoTop (B : ℕ) (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedFlex.VParams)
    (hgv : GroupedFlex.GVXHyps circomPrime L B gf posOf G V VR)
    [NeZero L]
    (input : Var (EqViaCarriesFlex.Inputs L) (F circomPrime)) :
    CostIs (GroupedFlex.mainNoTop B gf posOf G V VR hgv input)
      ⟨GroupedFlex.widthAllocFrom V.Wf (G - 2) 0,
       GroupedFlex.widthConsFrom V.Wf (G - 2) 0⟩ := by
  unfold GroupedFlex.mainNoTop
  exact costIs_carryLoopXV B gf posOf VR.OFFf V.Wf hgv.2.2.2.1 _ _ _ _

theorem costIs_assertion_groupedNoTop (B : ℕ) (gf posOf : ℕ → ℕ) (G : ℕ)
    (V VR : GroupedFlex.VParams)
    (hgv : GroupedFlex.GVXHyps circomPrime L B gf posOf G V VR) (hB1 : 1 ≤ B)
    [NeZero L]
    (input : Var (EqViaCarriesFlex.Inputs L) (F circomPrime)) :
    CostIs (assertion (GroupedFlex.circuitNoTop B gf posOf G V VR hgv hB1) input)
      ⟨GroupedFlex.widthAllocFrom V.Wf (G - 2) 0,
       GroupedFlex.widthConsFrom V.Wf (G - 2) 0⟩ :=
  CostIs.assertion (fun n => costIs_groupedNoTop B gf posOf G V VR hgv input n)

theorem isR1CS_groupedNoTop (B : ℕ) (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedFlex.VParams)
    (hgv : GroupedFlex.GVXHyps circomPrime L B gf posOf G V VR)
    [NeZero L]
    (input : Var (EqViaCarriesFlex.Inputs L) (F circomPrime))
    (hl : AffineW input.lhs) (hr : AffineW input.rhs) :
    IsR1CSCirc (GroupedFlex.mainNoTop B gf posOf G V VR hgv input) := by
  unfold GroupedFlex.mainNoTop
  exact isR1CS_carryLoopXV B gf posOf VR.OFFf V.Wf hgv.2.2.2.1 _ _ hl hr _ _

theorem isR1CS_assertion_groupedNoTop (B : ℕ) (gf posOf : ℕ → ℕ) (G : ℕ)
    (V VR : GroupedFlex.VParams)
    (hgv : GroupedFlex.GVXHyps circomPrime L B gf posOf G V VR) (hB1 : 1 ≤ B)
    [NeZero L]
    (input : Var (EqViaCarriesFlex.Inputs L) (F circomPrime))
    (hl : AffineW input.lhs) (hr : AffineW input.rhs) :
    IsR1CSCirc (assertion (GroupedFlex.circuitNoTop B gf posOf G V VR hgv hB1) input) :=
  IsR1CSCirc.assertion (fun n => isR1CS_groupedNoTop B gf posOf G V VR hgv input hl hr n)

end GroupedXVNoTop

end Cost

end Solution.Secp256k1ScalarMulFixedBase

end DonorFile1_12

-- Adapted donor module: SparseCanonical
section DonorFile1_13

/-!
### Sparse-prime canonicity check for secp256k1

Exploits the limb structure of `p = P256 = 2^256 − 2^32 − 977`:
its 64-bit limbs are `p₀ = 0xfffffffefffffc2f`, `p₁ = p₂ = p₃ = 2^64 − 1`.
For a normalized 4-limb `r`,
  `r.value < p ⟺ (r₁,r₂,r₃ not all 2^64−1) ∨ r₀ < p₀`.
-/

namespace Solution.Secp256k1ScalarMulFixedBase
namespace SparseCanonical

open Solution.Secp256k1ScalarMulFixedBase.Limbs

/-- `2^64 − 1`, the maxed value of the top three limbs of `p`. -/
def maxN : ℕ := 2 ^ limbBits - 1

/-- `p₀ = 0xfffffffefffffc2f`, the low limb of `P256`. -/
def p0N : ℕ := limbOfNat P256 0

/-- `3·(2^64−1)`, the summed max of the top three limbs. -/
def sumMaxN : ℕ := 3 * maxN

lemma maxN_eq : maxN = 18446744073709551615 := by decide
lemma p0N_eq : p0N = 18446744069414583343 := by decide
lemma sumMaxN_eq : sumMaxN = 55340232221128654845 := by decide
lemma p0N_lt_prime : p0N < circomPrime := by decide
lemma sumMaxN_lt_prime : sumMaxN < circomPrime := by decide

def main (r : Var Emu (F circomPrime)) : Circuit (F circomPrime) Unit := do
  -- One quotient witness encodes the conditional low-limb check.  Writing
  -- `S = 3·maxN - (r₁+r₂+r₃)` and `L = r₀+d₀+1-p₀`, the row `S·q=L`
  -- forces `L=0` exactly in the only case where the low limb matters (`S=0`).
  let q ← witnessField fun env =>
    let S := (sumMaxN : F circomPrime) - Expression.eval env.toEnvironment r[1]
      - Expression.eval env.toEnvironment r[2] - Expression.eval env.toEnvironment r[3]
    let d := ((p0N - 1 - (Expression.eval env.toEnvironment r[0]).val : ℕ) : F circomPrime)
    let L := Expression.eval env.toEnvironment r[0] + d + 1 - (p0N : F circomPrime)
    if S = 0 then 0 else L / S
  let d0 ← witnessField fun env =>
    ((p0N - 1 - (Expression.eval env.toEnvironment r[0]).val : ℕ) : F circomPrime)
  RangeCheck.circuit limbBits two_pow_limb_lt (by decide) d0
  let S := Expression.const (sumMaxN : F circomPrime) - r[1] - r[2] - r[3]
  let L := r[0] + d0 + 1 - Expression.const (p0N : F circomPrime)
  assertZero (S * q - L)

instance elaborated : ElaboratedCircuit (F circomPrime) Emu unit main := by
  elaborate_circuit

def Assumptions (r : Emu (F circomPrime)) : Prop :=
  r.Normalized limbBits

def Spec (r : Emu (F circomPrime)) : Prop :=
  BigInt.value limbBits r < P256

theorem soundness :
    FormalAssertion.Soundness (Input := Emu) (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [main, RangeCheck.circuit, RangeCheck.elaborated, RangeCheck.main,
    RangeCheck.Assumptions, RangeCheck.Spec]
  obtain ⟨hd0lt, hfin⟩ := h_holds
  set qv := env.get i₀ with hqvdef
  set dd := env.get (i₀ + 1) with hdddef
  have e0 : Expression.eval env input_var[0] = input[0] := by rw [← h_input, Vector.getElem_map]
  have e1 : Expression.eval env input_var[1] = input[1] := by rw [← h_input, Vector.getElem_map]
  have e2 : Expression.eval env input_var[2] = input[2] := by rw [← h_input, Vector.getElem_map]
  have e3 : Expression.eval env input_var[3] = input[3] := by rw [← h_input, Vector.getElem_map]
  rw [e1, e2, e3] at hfin; rw [e0] at hfin
  -- per-limb bounds
  have hb0v : input[0].val < 2 ^ limbBits := by have := h_assumptions (0 : Fin numLimbs); rwa [Fin.getElem_fin] at this
  have hb1v : input[1].val < 2 ^ limbBits := by have := h_assumptions (1 : Fin numLimbs); rwa [Fin.getElem_fin] at this
  have hb2v : input[2].val < 2 ^ limbBits := by have := h_assumptions (2 : Fin numLimbs); rwa [Fin.getElem_fin] at this
  have hb3v : input[3].val < 2 ^ limbBits := by have := h_assumptions (3 : Fin numLimbs); rwa [Fin.getElem_fin] at this
  -- value expansion
  have hval : BigInt.value limbBits input
      = input[0].val + input[1].val * 2 ^ 64 + input[2].val * 2 ^ 128 + input[3].val * 2 ^ 192 := by
    rw [BigInt.value_eq_sum, Fin.sum_univ_four]
    norm_num [Fin.getElem_fin, limbBits]
  -- numerals
  have hmaxN : maxN = 18446744073709551615 := maxN_eq
  have hp0N : p0N = 18446744069414583343 := p0N_eq
  have hsumM : sumMaxN = 55340232221128654845 := sumMaxN_eq
  have hpow : (2 : ℕ) ^ limbBits = 18446744073709551616 := by norm_num [limbBits]
  -- the affine sum, as a field element
  set SF : F circomPrime := (sumMaxN : F circomPrime) - input[1] - input[2] - input[3] with hSFdef
  rw [hval, show (2 : ℕ) ^ 64 = 18446744073709551616 from by norm_num,
    show (2 : ℕ) ^ 128 = 340282366920938463463374607431768211456 from by norm_num,
    show (2 : ℕ) ^ 192 = 6277101735386680763835789423207666416102355444464034512896 from by norm_num,
    show P256 = 115792089237316195423570985008687907853269984665640564039457584007908834671663 from by decide]
  by_cases hS : SF = 0
  · -- all three top limbs are maxed
    have hsumF : (input[1] + input[2] + input[3] : F circomPrime) = (sumMaxN : F circomPrime) := by
      rw [hSFdef] at hS; linear_combination -hS
    have hsum_val : input[1].val + input[2].val + input[3].val = sumMaxN := by
      have hcast : ((input[1].val + input[2].val + input[3].val : ℕ) : F circomPrime)
          = ((sumMaxN : ℕ) : F circomPrime) := by
        push_cast
        rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
        linear_combination hsumF
      have hlt : input[1].val + input[2].val + input[3].val < circomPrime := by
        rw [hpow] at hb1v hb2v hb3v; have := sumMaxN_lt_prime; omega
      have hc := congrArg ZMod.val hcast
      rwa [ZMod.val_natCast_of_lt hlt, ZMod.val_natCast_of_lt sumMaxN_lt_prime] at hc
    -- final constraint with allMax = 1 forces r₀ < p₀
    rw [hSFdef] at hS
    simp only [sub_eq_add_neg] at hS hfin
    rw [hS, zero_mul] at hfin
    norm_num at hfin
    have hsum : input[0] + dd + 1 = (↑p0N : F circomPrime) := by
      linear_combination -hfin
    have hcast : ((input[0].val + dd.val + 1 : ℕ) : F circomPrime) = ((p0N : ℕ) : F circomPrime) := by
      push_cast
      rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
      linear_combination hsum
    have hlt_sum : input[0].val + dd.val + 1 < circomPrime := by
      have := limb_add_lt; omega
    have heq : input[0].val + dd.val + 1 = p0N := by
      have hc := congrArg ZMod.val hcast
      rwa [ZMod.val_natCast_of_lt hlt_sum, ZMod.val_natCast_of_lt p0N_lt_prime] at hc
    rw [hpow] at hb1v hb2v hb3v
    omega
  · -- not all maxed: the top-limb sum is strictly below 3·maxN
    have hne : (input[1] + input[2] + input[3] : F circomPrime) ≠ (sumMaxN : F circomPrime) := by
      intro h; apply hS; rw [hSFdef]; linear_combination -h
    have hsum_ne : input[1].val + input[2].val + input[3].val ≠ sumMaxN := by
      intro h; apply hne
      have : ((input[1].val + input[2].val + input[3].val : ℕ) : F circomPrime)
          = ((sumMaxN : ℕ) : F circomPrime) := by rw [h]
      rwa [Nat.cast_add, Nat.cast_add, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val,
        ZMod.natCast_zmod_val] at this
    rw [hpow] at hb0v hb1v hb2v hb3v
    omega

theorem completeness :
    FormalAssertion.Completeness (Input := Emu) (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [main, RangeCheck.circuit, RangeCheck.elaborated, RangeCheck.main,
    RangeCheck.Assumptions, RangeCheck.Spec]
  obtain ⟨hv_q, hv_d0⟩ := h_env
  have e0 : Expression.eval env.toEnvironment input_var[0] = input[0] := by
    rw [← h_input, Vector.getElem_map]
  have e1 : Expression.eval env.toEnvironment input_var[1] = input[1] := by
    rw [← h_input, Vector.getElem_map]
  have e2 : Expression.eval env.toEnvironment input_var[2] = input[2] := by
    rw [← h_input, Vector.getElem_map]
  have e3 : Expression.eval env.toEnvironment input_var[3] = input[3] := by
    rw [← h_input, Vector.getElem_map]
  simp only [e0, e1, e2, e3] at hv_q hv_d0 ⊢
  have hb0v : input[0].val < 2 ^ limbBits := by
    have := h_assumptions (0 : Fin numLimbs); rwa [Fin.getElem_fin] at this
  have hb1v : input[1].val < 2 ^ limbBits := by
    have := h_assumptions (1 : Fin numLimbs); rwa [Fin.getElem_fin] at this
  have hb2v : input[2].val < 2 ^ limbBits := by
    have := h_assumptions (2 : Fin numLimbs); rwa [Fin.getElem_fin] at this
  have hb3v : input[3].val < 2 ^ limbBits := by
    have := h_assumptions (3 : Fin numLimbs); rwa [Fin.getElem_fin] at this
  have hmaxN : maxN = 18446744073709551615 := maxN_eq
  have hp0N : p0N = 18446744069414583343 := p0N_eq
  have hsumM : sumMaxN = 55340232221128654845 := sumMaxN_eq
  have hpow : (2 : ℕ) ^ limbBits = 18446744073709551616 := by norm_num [limbBits]
  refine ⟨?_, ?_⟩
  · -- range check on d0
    rw [hv_d0, ZMod.val_natCast_of_lt (lt_of_le_of_lt (by omega) p0N_lt_prime)]
    rw [hpow]; omega
  · -- quotient row
    rw [hv_q]
    by_cases hu : (sumMaxN : F circomPrime) - input[1] - input[2] - input[3] = 0
    · -- all three top limbs maxed ⇒ r₀ < p₀ so the low-limb constraint is honest
      have hsumF : (input[1] + input[2] + input[3] : F circomPrime) = (sumMaxN : F circomPrime) := by
        linear_combination -hu
      have hsum_val : input[1].val + input[2].val + input[3].val = sumMaxN := by
        have hcast : ((input[1].val + input[2].val + input[3].val : ℕ) : F circomPrime)
            = ((sumMaxN : ℕ) : F circomPrime) := by
          push_cast
          rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
          linear_combination hsumF
        have hlt : input[1].val + input[2].val + input[3].val < circomPrime := by
          rw [hpow] at hb1v hb2v hb3v; have := sumMaxN_lt_prime; omega
        have hc := congrArg ZMod.val hcast
        rwa [ZMod.val_natCast_of_lt hlt, ZMod.val_natCast_of_lt sumMaxN_lt_prime] at hc
      have hval : BigInt.value limbBits input
          = input[0].val + input[1].val * 2 ^ 64 + input[2].val * 2 ^ 128 + input[3].val * 2 ^ 192 := by
        rw [BigInt.value_eq_sum, Fin.sum_univ_four]
        norm_num [Fin.getElem_fin, limbBits]
      have ha0lt : input[0].val < p0N := by
        have hs := h_spec
        rw [hpow] at hb1v hb2v hb3v
        have ht1 : input[1].val = maxN := by omega
        have ht2 : input[2].val = maxN := by omega
        have ht3 : input[3].val = maxN := by omega
        rw [hval, ht1, ht2, ht3,
          show (2 : ℕ) ^ 64 = 18446744073709551616 from by norm_num,
          show (2 : ℕ) ^ 128 = 340282366920938463463374607431768211456 from by norm_num,
          show (2 : ℕ) ^ 192 = 6277101735386680763835789423207666416102355444464034512896 from by norm_num,
          show P256 = 115792089237316195423570985008687907853269984665640564039457584007908834671663 from by decide,
          hmaxN] at hs
        rw [hp0N]; omega
      have hX : input[0] + ((p0N - 1 - input[0].val : ℕ) : F circomPrime) + 1 + -(↑p0N : F circomPrime) = 0 := by
        have hcast : ((p0N - 1 - input[0].val : ℕ) : F circomPrime)
            = (↑p0N : F circomPrime) - 1 - input[0] := by
          rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_one, ZMod.natCast_zmod_val]
        rw [hcast]; ring
      rw [if_pos hu, hv_d0]
      linear_combination -hX
    · rw [if_neg hu, hv_d0]
      field_simp [hu]
      ring

def circuit : FormalAssertion (F circomPrime) Emu where
  main := main
  Assumptions := Assumptions
  Spec := Spec
  soundness := soundness
  completeness := completeness

set_option maxHeartbeats 3200000 in
open Challenge.Utils.ComputableWitnessLemmas in
theorem computableWitnesses : circuit.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations offset)
  apply FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  have key : Vector.map (Expression.eval env.toEnvironment) input
        = Vector.map (Expression.eval env'.toEnvironment) input →
      ∀ (i : ℕ) (hi : i < 4),
        Expression.eval env.toEnvironment input[i] = Expression.eval env'.toEnvironment input[i] := by
    intro h_in i hi
    have h := congrArg (fun v : Vector (F circomPrime) 4 => v[i]'hi) h_in
    simpa only [Vector.getElem_map] using h
  unfold main
  simp only [Circuit.bind_structuralComputableWitnesses_iff,
    Circuit.witnessField_structuralComputableWitnesses_iff,
    Circuit.assertZero_structuralComputableWitnesses_iff,
    FormalAssertion.assertion_structuralComputableWitnesses_iff, and_true]
  simp only [circuit_norm]
  refine ⟨?_, ?_, ?_⟩
  · intro _ h_in
    rw [key h_in 0 (by omega), key h_in 1 (by omega), key h_in 2 (by omega),
      key h_in 3 (by omega)]
  · intro _ h_in; rw [key h_in 0 (by omega)]
  · apply FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
    · intro k e1 e2 hle h_agree _
      rw [CircuitType.eval_var_field_prover, CircuitType.eval_var_field_prover]
      simp only [Expression.eval]
      exact h_agree _ (by omega)
    · exact RangeCheck.computableWitnesses limbBits two_pow_limb_lt (by decide)

theorem computableWitness : ∀ n input,
    ProverEnvironment.OnlyAccessedBelow n
      (fun env : ProverEnvironment (F circomPrime) => eval env input) →
    Circuit.ComputableWitnesses (main input) n :=
  Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnesses_implies
    computableWitnesses

end SparseCanonical
end Solution.Secp256k1ScalarMulFixedBase

end DonorFile1_13

-- Adapted donor module: ValidPTheorems
section DonorFile1_14

namespace Solution.Secp256k1ScalarMulFixedBase
namespace ValidP

open Utils.Bits

/-- Sum `1 - bit` over a slice. On boolean bits this is zero exactly when the
whole slice consists of ones. -/
def deficitSlice {n : ℕ} (bits : Vector (Expression (F circomPrime)) n)
    (start len : ℕ) (h : start + len ≤ n) : Expression (F circomPrime) :=
  Fin.foldl len (fun acc i => acc + (1 - bits[start + i.val]'(by omega))) 0

def dc (x start len : ℕ) : ℕ :=
  ∑ i : Fin len, if x.testBit (start + i.val) then 0 else 1

theorem dc_zero_iff (x start len : ℕ) :
    dc x start len = 0 ↔ ∀ i : Fin len, x.testBit (start + i.val) = true := by
  simp [dc]

theorem dc_ne_iff (x start len : ℕ) :
    dc x start len ≠ 0 ↔ ∃ i : Fin len, x.testBit (start + i.val) = false := by
  simp [dc]

theorem dc_le (x start len : ℕ) : dc x start len ≤ len := by
  unfold dc
  calc
    (∑ i : Fin len, if x.testBit (start + i.val) then 0 else 1)
        ≤ ∑ _i : Fin len, 1 := by
          apply Finset.sum_le_sum
          intro i _
          split <;> omega
    _ = len := by simp

theorem cast_zero_iff {n : ℕ} (hn : n < circomPrime) :
    ((n : ℕ) : F circomPrime) = 0 ↔ n = 0 := by
  rw [ZMod.natCast_eq_zero_iff]
  constructor
  · intro hd
    rcases hd with ⟨k, hk⟩
    by_cases hk0 : k = 0
    · simp [hk0] at hk
      exact hk
    · have : circomPrime ≤ n := by
        rw [hk]
        exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hk0)
      omega
  · rintro rfl
    exact dvd_zero _

lemma eval_fold {n : ℕ} (env : Environment (F Solution.Secp256k1ScalarMulFixedBase.circomPrime))
    (g : Fin n → Expression (F Solution.Secp256k1ScalarMulFixedBase.circomPrime)) :
    Expression.eval env (Fin.foldl n (fun acc i => acc + g i) 0)
      = ∑ i : Fin n, Expression.eval env (g i) := by
  induction n with
  | zero => simp [Expression.eval]
  | succ k ih =>
    simp [Fin.foldl_succ_last, Fin.sum_univ_castSucc, Expression.eval, ih]

lemma eval_ds {n start len : ℕ} (h : start + len ≤ n)
    (env : Environment (F Solution.Secp256k1ScalarMulFixedBase.circomPrime))
    (bits : Vector (Expression (F Solution.Secp256k1ScalarMulFixedBase.circomPrime)) n)
    (x : F Solution.Secp256k1ScalarMulFixedBase.circomPrime)
    (hb : Vector.map (Expression.eval env) bits = fieldToBits n x) :
    Expression.eval env (ValidP.deficitSlice bits start len h)
      = ((dc x.val start len : ℕ) : F Solution.Secp256k1ScalarMulFixedBase.circomPrime) := by
  rw [ValidP.deficitSlice, eval_fold, dc, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hi : start + i.val < n := by omega
  have he := congrArg (fun v : Vector (F Solution.Secp256k1ScalarMulFixedBase.circomPrime) n =>
    v[start + i.val]'hi) hb
  simp only [Vector.getElem_map] at he
  simp only [fieldToBits, Vector.getElem_map, toBits, Vector.getElem_mapRange] at he
  rw [show Expression.eval env (1 - bits[start + i.val]'hi)
      = 1 - Expression.eval env (bits[start + i.val]'hi) by
        simp only [Expression.eval]; ring, he]
  split <;> simp

theorem mapRange_eval_bit (env : Environment (F circomPrime)) (offset i : ℕ)
    (hi : i < limbBits) (x : F circomPrime)
    (hb : Vector.map (Expression.eval env)
      (Vector.mapRange limbBits fun j => var { index := offset + j }) =
        fieldToBits limbBits x) :
    env.get (offset + i) = if x.val.testBit i then 1 else 0 := by
  have h := congrArg (fun v : Vector (F circomPrime) limbBits => v[i]'hi) hb
  simp only [Vector.getElem_map] at h
  simp only [fieldToBits, Vector.getElem_map, toBits, Vector.getElem_mapRange] at h
  simp only [Expression.eval] at h
  split <;> simp_all

/-- Read the `i`-th bit off an arbitrary decomposition vector, given its value
equals `fieldToBits`.  Shape-agnostic: works for the affine-top vector where the
last entry is not a bare witness variable. -/
theorem vec_eval_bit (env : Environment (F circomPrime)) {n : ℕ}
    (b : Vector (Expression (F circomPrime)) n) (x : F circomPrime)
    (hb : Vector.map (Expression.eval env) b = fieldToBits n x)
    (i : ℕ) (hi : i < n) :
    Expression.eval env b[i] = if x.val.testBit i then 1 else 0 := by
  have h := congrArg (fun v : Vector (F circomPrime) n => v[i]'hi) hb
  simp only [Vector.getElem_map] at h
  simp only [fieldToBits, Vector.getElem_map, toBits, Vector.getElem_mapRange] at h
  split <;> simp_all

/-- For an affine-top vector `(mapRange w var).push top`, the low `w` cells are
plain witnesses, so their environment value is the corresponding bit. -/
theorem push_eval_bit (env : Environment (F circomPrime)) {w : ℕ} (base : ℕ)
    (top : Expression (F circomPrime)) (x : F circomPrime)
    (hb : Vector.map (Expression.eval env)
      ((Vector.mapRange w fun j => var { index := base + j }).push top) =
        fieldToBits (w + 1) x)
    (i : ℕ) (hi : i < w) :
    env.get (base + i) = if x.val.testBit i then 1 else 0 := by
  have h := vec_eval_bit env _ x hb i (by omega)
  rwa [Vector.getElem_push_lt hi, Vector.getElem_mapRange, Expression.eval] at h

theorem value_testBit (x : Emu (F circomPrime)) (hn : BigInt.Normalized limbBits x)
    (k : Fin 4) (j : Fin 64) :
    (BigInt.value limbBits x).testBit (64 * k.val + j.val) = x[k.val].val.testBit j.val := by
  fin_cases k
  · simp only [Fin.isValue, Nat.mul_zero, Nat.zero_add]
    have hn0 : x[0].val < 2^64 := by simpa [limbBits] using hn 0
    rw [show BigInt.value limbBits x =
        2^64 * (x[1].val + 2^64 * (x[2].val + 2^64 * x[3].val)) + x[0].val by
      rw [BigInt.value_eq_sum]; norm_num [Fin.sum_univ_succ]; ring_nf]
    rw [Nat.testBit_two_pow_mul_add _ hn0 j.val, if_pos j.isLt]
  · simp only [Fin.isValue, Nat.mul_one]
    have hn0 : x[0].val < 2^64 := by simpa [limbBits] using hn 0
    have hn1 : x[1].val < 2^64 := by simpa [limbBits] using hn 1
    rw [show BigInt.value limbBits x =
        2^64 * (x[1].val + 2^64 * (x[2].val + 2^64 * x[3].val)) + x[0].val by
      rw [BigInt.value_eq_sum]; norm_num [Fin.sum_univ_succ]; ring_nf]
    rw [Nat.testBit_two_pow_mul_add _ hn0 (64 + j.val), if_neg (by omega)]
    simp only [Nat.add_sub_cancel_left]
    rw [show x[1].val + 2^64 * (x[2].val + 2^64 * x[3].val)
        = 2^64 * (x[2].val + 2^64 * x[3].val) + x[1].val by ring]
    rw [Nat.testBit_two_pow_mul_add _ hn1 j.val, if_pos j.isLt]
  · simp only [Fin.isValue, Nat.reduceMul]
    have hn2 : x[2].val < 2^64 := by simpa [limbBits] using hn 2
    rw [show BigInt.value limbBits x =
        2^128 * (x[2].val + 2^64 * x[3].val) + (x[0].val + 2^64 * x[1].val) by
      rw [BigInt.value_eq_sum]; norm_num [Fin.sum_univ_succ]; ring_nf]
    have hlo : x[0].val + 2^64 * x[1].val < 2^128 := by
      have h0 := hn 0; have h1 := hn 1
      norm_num [limbBits] at h0 h1 ⊢
      nlinarith
    rw [Nat.testBit_two_pow_mul_add _ hlo (128 + j.val), if_neg (by omega)]
    simp only [Nat.add_sub_cancel_left]
    rw [show x[2].val + 2^64 * x[3].val = 2^64 * x[3].val + x[2].val by ring]
    rw [Nat.testBit_two_pow_mul_add _ hn2 j.val, if_pos j.isLt]
  · simp only [Fin.isValue, Nat.reduceMul]
    rw [show BigInt.value limbBits x =
        2^192 * x[3].val + (x[0].val + 2^64 * x[1].val + 2^128 * x[2].val) by
      rw [BigInt.value_eq_sum]; norm_num [Fin.sum_univ_succ]; ring_nf]
    have hlo : x[0].val + 2^64 * x[1].val + 2^128 * x[2].val < 2^192 := by
      have h0 := hn 0; have h1 := hn 1; have h2 := hn 2
      norm_num [limbBits] at h0 h1 h2 ⊢
      nlinarith
    rw [Nat.testBit_two_pow_mul_add _ hlo (192 + j.val), if_neg (by omega)]
    simp only [Nat.add_sub_cancel_left]

theorem value_testBit_global (x : Emu (F circomPrime)) (hn : BigInt.Normalized limbBits x)
    (i : ℕ) (hi : i < 256) :
    (BigInt.value limbBits x).testBit i =
      (x[i / 64]'(by norm_num [numLimbs]; omega)).val.testBit (i % 64) := by
  let k : Fin 4 := ⟨i / 64, by omega⟩
  let j : Fin 64 := ⟨i % 64, Nat.mod_lt _ (by norm_num)⟩
  have h := value_testBit x hn k j
  simpa [k, j, Nat.mul_comm, Nat.div_add_mod] using h

def topDC (x : Emu (F circomPrime)) : ℕ :=
  dc x[0].val 33 31 + dc x[1].val 0 64 + dc x[2].val 0 64 + dc x[3].val 0 64

def midDC (x : Emu (F circomPrime)) : ℕ := dc x[0].val 10 22

def lowDC (x : Emu (F circomPrime)) : ℕ := dc x[0].val 0 4

theorem cast_add4_zero_iff (a b c d : ℕ) (h : a + b + c + d < circomPrime) :
    ((a : F circomPrime) + (b : F circomPrime) + (c : F circomPrime) +
      (d : F circomPrime) = 0) ↔ a + b + c + d = 0 := by
  rw [← Nat.cast_add, ← Nat.cast_add, ← Nat.cast_add]
  exact cast_zero_iff h

theorem top_count_cast_zero_iff (a b c d : ℕ) :
    ((dc a 33 31 : F circomPrime) + (dc b 0 64 : F circomPrime) +
      (dc c 0 64 : F circomPrime) + (dc d 0 64 : F circomPrime) = 0) ↔
      dc a 33 31 + dc b 0 64 + dc c 0 64 + dc d 0 64 = 0 := by
  apply cast_add4_zero_iff
  have h0 := dc_le a 33 31
  have h1 := dc_le b 0 64
  have h2 := dc_le c 0 64
  have h3 := dc_le d 0 64
  exact lt_of_le_of_lt (by omega) (by decide +kernel : 223 < circomPrime)

theorem mid_cast_zero_iff (x : Emu (F circomPrime)) :
    ((dc x[0].val 10 22 : F circomPrime) = 0) ↔ midDC x = 0 := by
  apply cast_zero_iff
  exact lt_of_le_of_lt (dc_le x[0].val 10 22)
    (by decide +kernel : 22 < circomPrime)

theorem low_cast_zero_iff (x : Emu (F circomPrime)) :
    ((dc x[0].val 0 4 : F circomPrime) = 0) ↔ lowDC x = 0 := by
  apply cast_zero_iff
  exact lt_of_le_of_lt (dc_le x[0].val 0 4)
    (by decide +kernel : 4 < circomPrime)

set_option maxRecDepth 5000 in
theorem topDC_zero_high_bits (x : Emu (F circomPrime)) (hn : BigInt.Normalized limbBits x)
    (ht : topDC x = 0) (i : ℕ) (hi0 : 33 ≤ i) (hi1 : i < 256) :
    (BigInt.value limbBits x).testBit i = true := by
  have hd0 : dc x[0].val 33 31 = 0 := by unfold topDC at ht; omega
  have hd1 : dc x[1].val 0 64 = 0 := by unfold topDC at ht; omega
  have hd2 : dc x[2].val 0 64 = 0 := by unfold topDC at ht; omega
  have hd3 : dc x[3].val 0 64 = 0 := by unfold topDC at ht; omega
  by_cases h64 : i < 64
  · have hv := value_testBit x hn 0 ⟨i, h64⟩
    have hidx : i - 33 < 31 := by omega
    have h := (dc_zero_iff x[0].val 33 31).mp hd0 ⟨i - 33, hidx⟩
    calc
      (BigInt.value limbBits x).testBit i = x[0].val.testBit i := by simpa using hv
      _ = true := by simpa [Nat.add_sub_of_le hi0] using h
  · by_cases h128 : i < 128
    · have hv := value_testBit x hn 1 ⟨i - 64, by omega⟩
      have hidx : i - 64 < 64 := by omega
      have h := (dc_zero_iff x[1].val 0 64).mp hd1 ⟨i - 64, hidx⟩
      calc
        (BigInt.value limbBits x).testBit i = x[1].val.testBit (i - 64) := by
          simpa [Nat.add_sub_of_le (by omega : 64 ≤ i)] using hv
        _ = true := by simpa using h
    · by_cases h192 : i < 192
      · have hv := value_testBit x hn 2 ⟨i - 128, by omega⟩
        have hidx : i - 128 < 64 := by omega
        have h := (dc_zero_iff x[2].val 0 64).mp hd2 ⟨i - 128, hidx⟩
        calc
          (BigInt.value limbBits x).testBit i = x[2].val.testBit (i - 128) := by
            simpa [Nat.add_sub_of_le (by omega : 128 ≤ i)] using hv
          _ = true := by simpa using h
      · have hv := value_testBit x hn 3 ⟨i - 192, by omega⟩
        have hidx : i - 192 < 64 := by omega
        have h := (dc_zero_iff x[3].val 0 64).mp hd3 ⟨i - 192, hidx⟩
        calc
          (BigInt.value limbBits x).testBit i = x[3].val.testBit (i - 192) := by
            simpa [Nat.add_sub_of_le (by omega : 192 ≤ i)] using hv
          _ = true := by simpa using h

theorem topDC_ne_high_zero (x : Emu (F circomPrime)) (hn : BigInt.Normalized limbBits x)
    (ht : topDC x ≠ 0) :
    ∃ i, 33 ≤ i ∧ i < 256 ∧ (BigInt.value limbBits x).testBit i = false := by
  have hor : dc x[0].val 33 31 ≠ 0 ∨ dc x[1].val 0 64 ≠ 0 ∨
      dc x[2].val 0 64 ≠ 0 ∨ dc x[3].val 0 64 ≠ 0 := by
    unfold topDC at ht
    omega
  rcases hor with h0 | h1 | h2 | h3
  · rcases (dc_ne_iff x[0].val 33 31).mp h0 with ⟨j, hj⟩
    refine ⟨33 + j.val, by omega, by omega, ?_⟩
    calc
      (BigInt.value limbBits x).testBit (33 + j.val) =
          x[0].val.testBit (33 + j.val) := by
        simpa using value_testBit x hn 0 ⟨33 + j.val, by omega⟩
      _ = false := hj
  · rcases (dc_ne_iff x[1].val 0 64).mp h1 with ⟨j, hj⟩
    refine ⟨64 + j.val, by omega, by omega, ?_⟩
    calc
      (BigInt.value limbBits x).testBit (64 + j.val) = x[1].val.testBit j.val := by
        simpa using value_testBit x hn 1 j
      _ = false := by simpa using hj
  · rcases (dc_ne_iff x[2].val 0 64).mp h2 with ⟨j, hj⟩
    refine ⟨128 + j.val, by omega, by omega, ?_⟩
    calc
      (BigInt.value limbBits x).testBit (128 + j.val) = x[2].val.testBit j.val := by
        simpa using value_testBit x hn 2 j
      _ = false := by simpa using hj
  · rcases (dc_ne_iff x[3].val 0 64).mp h3 with ⟨j, hj⟩
    refine ⟨192 + j.val, by omega, by omega, ?_⟩
    calc
      (BigInt.value limbBits x).testBit (192 + j.val) = x[3].val.testBit j.val := by
        simpa using value_testBit x hn 3 j
      _ = false := by simpa using hj

set_option maxHeartbeats 1000000 in
theorem p_high_bit (i : ℕ) (hlo : 33 ≤ i) (hhi : i < 256) :
    P256.testBit i = true := by
  interval_cases i <;> decide +kernel

theorem lt_of_zero_in_one_run (N M lo hi : ℕ)
    (hz : ∃ i, lo ≤ i ∧ i < hi ∧ N.testBit i = false)
    (hm : ∀ i, lo ≤ i → i < hi → M.testBit i = true)
    (habove : ∀ j, hi ≤ j → N.testBit j = M.testBit j) : N < M := by
  let s := (Finset.range hi).filter fun i => lo ≤ i ∧ N.testBit i = false
  have hs : s.Nonempty := by
    rcases hz with ⟨i, hi0, hi1, hi2⟩
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi1, hi0, hi2⟩⟩
  let i := s.max' hs
  have himem : i ∈ s := Finset.max'_mem s hs
  have hip := Finset.mem_filter.mp himem
  have hiHi : i < hi := Finset.mem_range.mp hip.1
  have hiLo : lo ≤ i := hip.2.1
  have hiN : N.testBit i = false := hip.2.2
  refine Nat.lt_of_testBit i hiN (hm i hiLo hiHi) ?_
  intro j hij
  by_cases hj : j < hi
  · have hjlo : lo ≤ j := by omega
    have hmj := hm j hjlo hj
    have hNj : N.testBit j = true := by
      cases hbit : N.testBit j
      · have hjmem : j ∈ s := Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr hj, hjlo, hbit⟩
        have := Finset.le_max' s j hjmem
        omega
      · rfl
    rw [hNj, hmj]
  · exact habove j (by omega)

theorem lt_p_of_high_zero (N : ℕ) (hN : N < 2^256)
    (hz : ∃ i, 33 ≤ i ∧ i < 256 ∧ N.testBit i = false) : N < P256 := by
  refine lt_of_zero_in_one_run N P256 33 256 hz p_high_bit ?_
  intro j h256j
  have hpPow : 2^256 ≤ 2^j := Nat.pow_le_pow_right (by norm_num) h256j
  have hNb : N < 2^j := lt_of_lt_of_le hN hpPow
  have hPb : P256 < 2^j := lt_of_lt_of_le (by decide : P256 < 2^256) hpPow
  rw [Nat.testBit_eq_false_of_lt hNb, Nat.testBit_eq_false_of_lt hPb]

set_option maxHeartbeats 1000000 in
theorem p_mid_bit (i : ℕ) (hlo : 10 ≤ i) (hhi : i < 32) :
    P256.testBit i = true := by
  interval_cases i <;> decide +kernel

theorem value_testBit_limb0 (x : Emu (F circomPrime)) (hn : BigInt.Normalized limbBits x)
    (i : ℕ) (hi : i < 64) :
    (BigInt.value limbBits x).testBit i = x[0].val.testBit i := by
  simpa using value_testBit x hn 0 ⟨i, hi⟩

theorem equal_above32 (x : Emu (F circomPrime)) (hn : BigInt.Normalized limbBits x)
    (ht : topDC x = 0) (hb32 : x[0].val.testBit 32 = false) :
    ∀ j, 32 ≤ j → (BigInt.value limbBits x).testBit j = P256.testBit j := by
  intro j hj
  by_cases hj256 : j < 256
  · rcases eq_or_lt_of_le hj with rfl | hjgt
    · rw [value_testBit_limb0 x hn 32 (by omega), hb32]
      decide +kernel
    · rw [topDC_zero_high_bits x hn ht j (by omega) hj256,
        p_high_bit j (by omega) hj256]
  · have h256j : 256 ≤ j := by omega
    have hN := BigInt.value_lt hn
    norm_num [limbBits, numLimbs] at hN
    have hpPow : 2^256 ≤ 2^j := Nat.pow_le_pow_right (by norm_num) h256j
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hN hpPow),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by decide : P256 < 2^256) hpPow)]

theorem midDC_zero_mid_bits (x : Emu (F circomPrime)) (hn : BigInt.Normalized limbBits x)
    (hm : midDC x = 0) (i : ℕ) (hi0 : 10 ≤ i) (hi1 : i < 32) :
    (BigInt.value limbBits x).testBit i = true := by
  have hd : dc x[0].val 10 22 = 0 := hm
  have hidx : i - 10 < 22 := by omega
  have h := (dc_zero_iff x[0].val 10 22).mp hd ⟨i - 10, hidx⟩
  rw [value_testBit_limb0 x hn i (by omega)]
  simpa [Nat.add_sub_of_le hi0] using h

theorem midDC_ne_mid_zero (x : Emu (F circomPrime)) (hn : BigInt.Normalized limbBits x)
    (hm : midDC x ≠ 0) :
    ∃ i, 10 ≤ i ∧ i < 32 ∧ (BigInt.value limbBits x).testBit i = false := by
  rcases (dc_ne_iff x[0].val 10 22).mp hm with ⟨j, hj⟩
  refine ⟨10 + j.val, by omega, by omega, ?_⟩
  rw [value_testBit_limb0 x hn (10 + j.val) (by omega)]
  simpa using hj

theorem equal_above10 (x : Emu (F circomPrime)) (hn : BigInt.Normalized limbBits x)
    (ht : topDC x = 0) (hb32 : x[0].val.testBit 32 = false) (hm : midDC x = 0) :
    ∀ j, 10 ≤ j → (BigInt.value limbBits x).testBit j = P256.testBit j := by
  intro j hj
  by_cases hj32 : j < 32
  · rw [midDC_zero_mid_bits x hn hm j hj hj32, p_mid_bit j hj hj32]
  · exact equal_above32 x hn ht hb32 j (by omega)

set_option maxHeartbeats 1000000 in
theorem p_zero_6_10 (i : ℕ) (hlo : 6 ≤ i) (hhi : i < 10) :
    P256.testBit i = false := by
  interval_cases i <;> decide +kernel

set_option maxHeartbeats 1000000 in
theorem p_low_bit (i : ℕ) (hhi : i < 4) : P256.testBit i = true := by
  interval_cases i <;> decide +kernel

def zeroRun (x : Emu (F circomPrime)) : Prop :=
  ∀ i, 6 ≤ i → i < 10 → x[0].val.testBit i = false

def Pattern (x : Emu (F circomPrime)) : Prop :=
  topDC x ≠ 0 ∨
    (x[0].val.testBit 32 = false ∧
      (midDC x ≠ 0 ∨
        (zeroRun x ∧
          (x[0].val.testBit 5 = false ∨
            (x[0].val.testBit 4 = false ∧ lowDC x ≠ 0)))))

def bitNat (b : Bool) : ℕ := if b then 1 else 0

def bitField (b : Bool) : F circomPrime := if b then 1 else 0

theorem bitField_eq_natCast (b : Bool) : bitField b = (bitNat b : F circomPrime) := by
  cases b <;> rfl

theorem bitNat_le_one (b : Bool) : bitNat b ≤ 1 := by
  cases b <;> simp [bitNat]

theorem bitNat_zero_iff (b : Bool) : bitNat b = 0 ↔ b = false := by
  cases b <;> simp [bitNat]

theorem bitField_zero_iff (b : Bool) : bitField b = 0 ↔ b = false := by
  rw [bitField_eq_natCast, cast_zero_iff
    (lt_of_le_of_lt (bitNat_le_one b) (by decide +kernel : 1 < circomPrime)),
    bitNat_zero_iff]

theorem bitNat_sum4_lt_prime (a b c d : Bool) :
    bitNat a + bitNat b + bitNat c + bitNat d < circomPrime := by
  have ha := bitNat_le_one a
  have hb := bitNat_le_one b
  have hc := bitNat_le_one c
  have hd := bitNat_le_one d
  exact lt_of_le_of_lt (by omega) (by decide +kernel : 4 < circomPrime)

theorem pattern_of_constraints (x : Emu (F circomPrime))
    {topEq midEq throughMid through5 lowEq : F circomPrime}
    (htopEq : topEq = if topDC x = 0 then 1 else 0)
    (hbit32 : topEq * bitField (x[0].val.testBit 32) = 0)
    (hmidEq : midEq = if midDC x = 0 then 1 else 0)
    (hthroughMid : throughMid = topEq * midEq)
    (hzeroRun : throughMid *
      (bitField (x[0].val.testBit 9) + bitField (x[0].val.testBit 8) +
       bitField (x[0].val.testBit 7) + bitField (x[0].val.testBit 6)) = 0)
    (hthrough5 : through5 = throughMid * bitField (x[0].val.testBit 5))
    (hbit4 : through5 * bitField (x[0].val.testBit 4) = 0)
    (hlowEq : lowEq = if lowDC x = 0 then 1 else 0)
    (hstrict : through5 * lowEq = 0) : Pattern x := by
  by_cases ht : topDC x ≠ 0
  · exact Or.inl ht
  · have ht0 : topDC x = 0 := not_ne_iff.mp ht
    right
    have hb32 : x[0].val.testBit 32 = false := by
      apply (bitField_zero_iff _).mp
      rw [htopEq, if_pos ht0] at hbit32
      simpa only [one_mul] using hbit32
    refine ⟨hb32, ?_⟩
    by_cases hm : midDC x ≠ 0
    · exact Or.inl hm
    · have hm0 : midDC x = 0 := not_ne_iff.mp hm
      right
      have hsum := hzeroRun
      rw [hthroughMid, htopEq, if_pos ht0, hmidEq, if_pos hm0] at hsum
      simp only [one_mul] at hsum
      simp only [bitField_eq_natCast] at hsum
      have hsumNat := (cast_add4_zero_iff _ _ _ _
        (bitNat_sum4_lt_prime _ _ _ _)).mp hsum
      have hzeros : x[0].val.testBit 9 = false ∧
          x[0].val.testBit 8 = false ∧ x[0].val.testBit 7 = false ∧
          x[0].val.testBit 6 = false := by
        exact ⟨(bitNat_zero_iff _).mp (by omega),
          (bitNat_zero_iff _).mp (by omega),
          (bitNat_zero_iff _).mp (by omega),
          (bitNat_zero_iff _).mp (by omega)⟩
      have hz : zeroRun x := by
        intro i hi0 hi1
        interval_cases i <;> simp_all
      refine ⟨hz, ?_⟩
      by_cases hb5 : x[0].val.testBit 5 = false
      · exact Or.inl hb5
      · have hb5t : x[0].val.testBit 5 = true := by simpa using hb5
        right
        have hb4 : x[0].val.testBit 4 = false := by
          apply (bitField_zero_iff _).mp
          rw [hthrough5, hthroughMid, htopEq, if_pos ht0, hmidEq, if_pos hm0] at hbit4
          simpa only [bitField, hb5t, if_true, one_mul] using hbit4
        refine ⟨hb4, ?_⟩
        intro hl0
        rw [hthrough5, hthroughMid, htopEq, if_pos ht0, hmidEq, if_pos hm0,
          hlowEq, if_pos hl0] at hstrict
        simp [bitField, hb5t] at hstrict

theorem constraints_of_pattern (x : Emu (F circomPrime))
    {topEq midEq throughMid through5 lowEq : F circomPrime}
    (htopEq : topEq = if topDC x = 0 then 1 else 0)
    (hmidEq : midEq = if midDC x = 0 then 1 else 0)
    (hthroughMid : throughMid = topEq * midEq)
    (hthrough5 : through5 = throughMid * bitField (x[0].val.testBit 5))
    (hlowEq : lowEq = if lowDC x = 0 then 1 else 0)
    (hpatt : Pattern x) :
    topEq * bitField (x[0].val.testBit 32) = 0 ∧
      throughMid *
        (bitField (x[0].val.testBit 9) + bitField (x[0].val.testBit 8) +
         bitField (x[0].val.testBit 7) + bitField (x[0].val.testBit 6)) = 0 ∧
      through5 * bitField (x[0].val.testBit 4) = 0 ∧
      through5 * lowEq = 0 := by
  by_cases ht : topDC x ≠ 0
  · simp [htopEq, ht, hthroughMid, hthrough5]
  · have ht0 : topDC x = 0 := not_ne_iff.mp ht
    rcases hpatt with htop | ⟨hb32, hrest⟩
    · exact (ht htop).elim
    by_cases hm : midDC x ≠ 0
    · simp [htopEq, ht0, hmidEq, hm, hthroughMid, hthrough5, bitField, hb32]
    · have hm0 : midDC x = 0 := not_ne_iff.mp hm
      rcases hrest with hmid | ⟨hz, hlow⟩
      · exact (hm hmid).elim
      have h9 := hz 9 (by omega) (by omega)
      have h8 := hz 8 (by omega) (by omega)
      have h7 := hz 7 (by omega) (by omega)
      have h6 := hz 6 (by omega) (by omega)
      by_cases hb5 : x[0].val.testBit 5 = false
      · simp [htopEq, ht0, hmidEq, hm0, hthroughMid, hthrough5, bitField,
          hb32, h9, h8, h7, h6, hb5]
      · have hb5t : x[0].val.testBit 5 = true := by simpa using hb5
        rcases hlow with hb5f | ⟨hb4, hl⟩
        · exact (hb5 hb5f).elim
        simp [htopEq, ht0, hmidEq, hm0, hthroughMid, hthrough5, hlowEq,
          bitField, hb32, h9, h8, h7, h6, hb5t, hb4, hl]

theorem equal_above33 (x : Emu (F circomPrime)) (hn : BigInt.Normalized limbBits x)
    (ht : topDC x = 0) :
    ∀ j, 33 ≤ j → (BigInt.value limbBits x).testBit j = P256.testBit j := by
  intro j hj
  by_cases hj256 : j < 256
  · rw [topDC_zero_high_bits x hn ht j hj hj256, p_high_bit j hj hj256]
  · have h256j : 256 ≤ j := by omega
    have hN := BigInt.value_lt hn
    norm_num [limbBits, numLimbs] at hN
    have hpPow : 2^256 ≤ 2^j := Nat.pow_le_pow_right (by norm_num) h256j
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hN hpPow),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by decide : P256 < 2^256) hpPow)]

theorem equal_above5 (x : Emu (F circomPrime)) (hn : BigInt.Normalized limbBits x)
    (ht : topDC x = 0) (hb32 : x[0].val.testBit 32 = false) (hm : midDC x = 0)
    (hz : zeroRun x) :
    ∀ j, 5 < j → (BigInt.value limbBits x).testBit j = P256.testBit j := by
  intro j hj
  by_cases hj10 : j < 10
  · rw [value_testBit_limb0 x hn j (by omega), hz j (by omega) hj10,
      p_zero_6_10 j (by omega) hj10]
  · exact equal_above10 x hn ht hb32 hm j (by omega)

theorem equal_above4 (x : Emu (F circomPrime)) (hn : BigInt.Normalized limbBits x)
    (ht : topDC x = 0) (hb32 : x[0].val.testBit 32 = false) (hm : midDC x = 0)
    (hz : zeroRun x) (hb5 : x[0].val.testBit 5 = true) :
    ∀ j, 4 < j → (BigInt.value limbBits x).testBit j = P256.testBit j := by
  intro j hj
  rcases eq_or_lt_of_le (by omega : 5 ≤ j) with rfl | hj5
  · rw [value_testBit_limb0 x hn 5 (by omega), hb5]
    decide +kernel
  · exact equal_above5 x hn ht hb32 hm hz j hj5

theorem lowDC_ne_low_zero (x : Emu (F circomPrime)) (hn : BigInt.Normalized limbBits x)
    (hl : lowDC x ≠ 0) :
    ∃ i, i < 4 ∧ (BigInt.value limbBits x).testBit i = false := by
  rcases (dc_ne_iff x[0].val 0 4).mp hl with ⟨j, hj⟩
  refine ⟨j.val, j.isLt, ?_⟩
  rw [value_testBit_limb0 x hn j.val (by omega)]
  simpa using hj

theorem lt_of_one_in_zero_run (N M lo hi : ℕ)
    (hz : ∃ i, lo ≤ i ∧ i < hi ∧ N.testBit i = true)
    (hm : ∀ i, lo ≤ i → i < hi → M.testBit i = false)
    (habove : ∀ j, hi ≤ j → N.testBit j = M.testBit j) : M < N := by
  let s := (Finset.range hi).filter fun i => lo ≤ i ∧ N.testBit i = true
  have hs : s.Nonempty := by
    rcases hz with ⟨i, hi0, hi1, hi2⟩
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi1, hi0, hi2⟩⟩
  let i := s.max' hs
  have himem : i ∈ s := Finset.max'_mem s hs
  have hip := Finset.mem_filter.mp himem
  have hiHi : i < hi := Finset.mem_range.mp hip.1
  have hiLo : lo ≤ i := hip.2.1
  have hiN : N.testBit i = true := hip.2.2
  refine Nat.lt_of_testBit i (hm i hiLo hiHi) hiN ?_
  intro j hij
  by_cases hj : j < hi
  · have hjlo : lo ≤ j := by omega
    have hmj := hm j hjlo hj
    have hNj : N.testBit j = false := by
      cases hbit : N.testBit j
      · rfl
      · have hjmem : j ∈ s := Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr hj, hjlo, hbit⟩
        have := Finset.le_max' s j hjmem
        omega
    rw [hNj, hmj]
  · exact (habove j (by omega)).symm

set_option maxRecDepth 5000 in
theorem pattern_iff_lt (x : Emu (F circomPrime)) (hn : BigInt.Normalized limbBits x) :
    Pattern x ↔ BigInt.value limbBits x < P256 := by
  let N := BigInt.value limbBits x
  have hN : N < 2^256 := by
    have := BigInt.value_lt hn
    simpa [N, limbBits, numLimbs] using this
  constructor
  · intro hpatt
    by_cases ht : topDC x ≠ 0
    · exact lt_p_of_high_zero N hN (topDC_ne_high_zero x hn ht)
    · have ht0 : topDC x = 0 := not_ne_iff.mp ht
      rcases hpatt with htop | ⟨hb32, hrest⟩
      · exact (ht htop).elim
      by_cases hm : midDC x ≠ 0
      · exact lt_of_zero_in_one_run N P256 10 32 (midDC_ne_mid_zero x hn hm)
          p_mid_bit (equal_above32 x hn ht0 hb32)
      · have hm0 : midDC x = 0 := not_ne_iff.mp hm
        rcases hrest with hmid | ⟨hz, hlow⟩
        · exact (hm hmid).elim
        by_cases hb5 : x[0].val.testBit 5 = false
        · refine Nat.lt_of_testBit 5 ?_ (by decide +kernel) ?_
          · rw [value_testBit_limb0 x hn 5 (by omega), hb5]
          · exact equal_above5 x hn ht0 hb32 hm0 hz
        · have hb5t : x[0].val.testBit 5 = true := by simpa using hb5
          rcases hlow with hb5f | ⟨hb4, hl⟩
          · exact (hb5 hb5f).elim
          exact lt_of_zero_in_one_run N P256 0 4
            (by simpa [N] using lowDC_ne_low_zero x hn hl)
            (fun i _ hi => p_low_bit i hi)
            (fun j hj => by
              rcases eq_or_lt_of_le hj with rfl | hj4
              · rw [value_testBit_limb0 x hn 4 (by omega), hb4]
                decide +kernel
              · exact equal_above4 x hn ht0 hb32 hm0 hz hb5t j hj4)
  · intro hlt
    by_cases ht : topDC x ≠ 0
    · exact Or.inl ht
    · right
      have ht0 : topDC x = 0 := not_ne_iff.mp ht
      have hb32 : x[0].val.testBit 32 = false := by
        cases hb : x[0].val.testBit 32
        · rfl
        · exfalso
          have hPN : P256 < N := Nat.lt_of_testBit 32 (by decide +kernel)
            (by rw [value_testBit_limb0 x hn 32 (by omega), hb])
            (fun j hj => (equal_above33 x hn ht0 j (by omega)).symm)
          omega
      refine ⟨hb32, ?_⟩
      by_cases hm : midDC x ≠ 0
      · exact Or.inl hm
      · right
        have hm0 : midDC x = 0 := not_ne_iff.mp hm
        have hz : zeroRun x := by
          intro i hi0 hi1
          cases hb : x[0].val.testBit i
          · rfl
          · exfalso
            have hNi : N.testBit i = true := by
              rw [value_testBit_limb0 x hn i (by omega), hb]
            have hPN : P256 < N := lt_of_one_in_zero_run N P256 6 10
              ⟨i, hi0, hi1, hNi⟩ p_zero_6_10
              (fun j hj => equal_above10 x hn ht0 hb32 hm0 j hj)
            omega
        refine ⟨hz, ?_⟩
        cases hb5 : x[0].val.testBit 5
        · exact Or.inl (by simpa using hb5)
        · right
          have hb4 : x[0].val.testBit 4 = false := by
            cases h4 : x[0].val.testBit 4
            · rfl
            · exfalso
              have hPN : P256 < N := Nat.lt_of_testBit 4 (by decide +kernel)
                (by rw [value_testBit_limb0 x hn 4 (by omega), h4])
                (fun j hj => (equal_above4 x hn ht0 hb32 hm0 hz hb5 j hj).symm)
              omega
          refine ⟨hb4, ?_⟩
          intro hl0
          have hEq : N = P256 := Nat.eq_of_testBit_eq fun i => by
            by_cases hi4 : i < 4
            · have hli : x[0].val.testBit i = true := by
                simpa using (dc_zero_iff x[0].val 0 4).mp hl0 ⟨i, hi4⟩
              rw [value_testBit_limb0 x hn i (by omega)]
              rw [hli, p_low_bit i hi4]
            · rcases eq_or_lt_of_le (by omega : 4 ≤ i) with rfl | hi
              · rw [value_testBit_limb0 x hn 4 (by omega), hb4]
                decide +kernel
              · exact equal_above4 x hn ht0 hb32 hm0 hz hb5 i hi
          omega

end ValidP
end Solution.Secp256k1ScalarMulFixedBase

end DonorFile1_14

-- Adapted donor module: ValidPWeak
section DonorFile1_15

/-!
# Inverse-witness ("weak") form of the sparse `x < p` comparison

The sparse comparison against `p = 2^256 - 2^32 - 977` only ever needs
implications of the shape

  "the prefix deficit is zero  ⟹  this target is zero",

never the converse.  A single row `target - deficit * u = 0` with a freshly
witnessed `u` delivers exactly that implication, and consecutive prefix stages
can be pinned by *sums* of deficit counters instead of by explicit equality
flags multiplied together.

That replaces the three `IsZeroField` gadgets and the two product witnesses of
the flag-based tail (8 allocations, 12 rows) by four bare witnesses and four
rows.
-/

namespace Solution.Secp256k1ScalarMulFixedBase
namespace ValidP

open Utils.Bits

set_option maxHeartbeats 2000000

/-! Pure arithmetic helpers.  These are stated over abstract naturals so that
`omega` never has to look at the (very large) `ZMod` atoms. -/

theorem dc_sum_le_aux {a b c d : ℕ} (ha : a ≤ 31) (hb : b ≤ 64) (hc : c ≤ 64)
    (hd : d ≤ 64) : a + b + c + d ≤ 223 := by omega

theorem sum2_le_aux {a b : ℕ} (ha : a ≤ 223) (hb : b ≤ 22) : a + b ≤ 250 := by omega

theorem sum2_zero_aux {a b : ℕ} (h : a + b = 0) : a = 0 ∧ b = 0 := by omega

theorem sum3_le_aux {a b e : ℕ} (ha : a ≤ 223) (hb : b ≤ 22) : a + b + (1 - e) ≤ 250 := by
  omega

theorem sum4_le_aux {a b e c : ℕ} (ha : a ≤ 223) (hb : b ≤ 22) (hc : c ≤ 4) :
    a + b + (1 - e) + c ≤ 250 := by omega

theorem sum3_zero_aux {a b e : ℕ} (he : e ≤ 1) (h : a + b + (1 - e) = 0) :
    a = 0 ∧ b = 0 ∧ e = 1 := by omega

theorem sum4_zero_aux {a b e c : ℕ} (he : e ≤ 1) (h : a + b + (1 - e) + c = 0) :
    a = 0 ∧ b = 0 ∧ e = 1 ∧ c = 0 := by omega

theorem topDC_le (x : Emu (F circomPrime)) : topDC x ≤ 223 :=
  dc_sum_le_aux (dc_le _ 33 31) (dc_le _ 0 64) (dc_le _ 0 64) (dc_le _ 0 64)

theorem midDC_le (x : Emu (F circomPrime)) : midDC x ≤ 22 := dc_le _ 10 22

theorem lowDC_le (x : Emu (F circomPrime)) : lowDC x ≤ 4 := dc_le _ 0 4

/-- The sum of all deficit counters plus the `p[5]` slack bit. -/
def uNat (x : Emu (F circomPrime)) : ℕ :=
  topDC x + midDC x + (1 - bitNat (x[0].val.testBit 5)) + lowDC x

theorem small_cast_zero_iff {n : ℕ} (h : n ≤ 250) :
    ((n : ℕ) : F circomPrime) = 0 ↔ n = 0 :=
  cast_zero_iff (lt_of_le_of_lt h (by decide +kernel : 250 < circomPrime))

theorem topF_zero_iff (x : Emu (F circomPrime)) :
    ((topDC x : ℕ) : F circomPrime) = 0 ↔ topDC x = 0 :=
  small_cast_zero_iff (le_trans (topDC_le x) (by omega))

theorem sumF_eq (x : Emu (F circomPrime)) :
    ((topDC x : ℕ) : F circomPrime) + ((midDC x : ℕ) : F circomPrime)
      = ((topDC x + midDC x : ℕ) : F circomPrime) := by
  push_cast
  ring

theorem sumF_zero_iff (x : Emu (F circomPrime)) :
    ((topDC x : ℕ) : F circomPrime) + ((midDC x : ℕ) : F circomPrime) = 0 ↔
      topDC x = 0 ∧ midDC x = 0 := by
  rw [sumF_eq, small_cast_zero_iff (sum2_le_aux (topDC_le x) (midDC_le x))]
  exact ⟨sum2_zero_aux, fun h => by rw [h.1, h.2]⟩

/-- The stage-3 deficit expression, as a cast of a small natural number. -/
theorem tF_eq (x : Emu (F circomPrime)) :
    ((topDC x : ℕ) : F circomPrime) + ((midDC x : ℕ) : F circomPrime)
        + (1 - bitField (x[0].val.testBit 5))
      = ((topDC x + midDC x + (1 - bitNat (x[0].val.testBit 5)) : ℕ) : F circomPrime) := by
  cases h : x[0].val.testBit 5 <;>
    simp only [h, bitField, bitNat, if_true, if_false] <;> push_cast <;> ring

theorem uF_eq (x : Emu (F circomPrime)) :
    ((topDC x : ℕ) : F circomPrime) + ((midDC x : ℕ) : F circomPrime)
        + (1 - bitField (x[0].val.testBit 5)) + ((lowDC x : ℕ) : F circomPrime)
      = ((uNat x : ℕ) : F circomPrime) := by
  rw [tF_eq]
  unfold uNat
  push_cast
  ring

theorem uNat_le (x : Emu (F circomPrime)) : uNat x ≤ 250 :=
  sum4_le_aux (topDC_le x) (midDC_le x) (lowDC_le x)

theorem bit5_true_of_bitNat {x : Emu (F circomPrime)}
    (h : bitNat (x[0].val.testBit 5) = 1) : x[0].val.testBit 5 = true := by
  cases hh : x[0].val.testBit 5 with
  | false => rw [hh] at h; simp [bitNat] at h
  | true => rfl

/-- One witnessed-inverse row certifies exactly the implication `d = 0 → num = 0`. -/
theorem inv_row_of_imp {d num : F circomPrime} (h : d = 0 → num = 0) :
    num - d * (if d = 0 then 0 else num * d⁻¹) = 0 := by
  by_cases hd : d = 0
  · rw [if_pos hd, hd, h hd]; ring
  · rw [if_neg hd]
    field_simp
    ring

theorem inv_row_of_ne {d : F circomPrime} (h : d ≠ 0) :
    d * (if d = 0 then 0 else d⁻¹) - 1 = 0 := by
  rw [if_neg h, mul_inv_cancel₀ h, sub_self]

theorem pattern_of_weak (x : Emu (F circomPrime)) {u1 u2 u3 u4 : F circomPrime}
    (h1 : bitField (x[0].val.testBit 32) - ((topDC x : ℕ) : F circomPrime) * u1 = 0)
    (h2 : (bitField (x[0].val.testBit 9) + bitField (x[0].val.testBit 8) +
            bitField (x[0].val.testBit 7) + bitField (x[0].val.testBit 6))
          - (((topDC x : ℕ) : F circomPrime) + ((midDC x : ℕ) : F circomPrime)) * u2 = 0)
    (h3 : bitField (x[0].val.testBit 4)
          - (((topDC x : ℕ) : F circomPrime) + ((midDC x : ℕ) : F circomPrime)
              + (1 - bitField (x[0].val.testBit 5))) * u3 = 0)
    (h4 : (((topDC x : ℕ) : F circomPrime) + ((midDC x : ℕ) : F circomPrime)
              + (1 - bitField (x[0].val.testBit 5)) + ((lowDC x : ℕ) : F circomPrime)) * u4
          - 1 = 0) :
    Pattern x := by
  by_cases ht : topDC x ≠ 0
  · exact Or.inl ht
  · have ht0 : topDC x = 0 := not_ne_iff.mp ht
    have htF : ((topDC x : ℕ) : F circomPrime) = 0 := by rw [ht0]; simp
    right
    have hb32 : x[0].val.testBit 32 = false := by
      apply (bitField_zero_iff _).mp
      rw [htF, zero_mul, sub_zero] at h1
      exact h1
    refine ⟨hb32, ?_⟩
    by_cases hm : midDC x ≠ 0
    · exact Or.inl hm
    · have hm0 : midDC x = 0 := not_ne_iff.mp hm
      have hmF : ((midDC x : ℕ) : F circomPrime) = 0 := by rw [hm0]; simp
      right
      have hsum : bitField (x[0].val.testBit 9) + bitField (x[0].val.testBit 8) +
          bitField (x[0].val.testBit 7) + bitField (x[0].val.testBit 6) = 0 := by
        rw [htF, hmF, add_zero, zero_mul, sub_zero] at h2
        exact h2
      simp only [bitField_eq_natCast] at hsum
      have hsumNat := (cast_add4_zero_iff _ _ _ _
        (bitNat_sum4_lt_prime _ _ _ _)).mp hsum
      have hzeros : x[0].val.testBit 9 = false ∧
          x[0].val.testBit 8 = false ∧ x[0].val.testBit 7 = false ∧
          x[0].val.testBit 6 = false :=
        ⟨(bitNat_zero_iff _).mp (by omega), (bitNat_zero_iff _).mp (by omega),
          (bitNat_zero_iff _).mp (by omega), (bitNat_zero_iff _).mp (by omega)⟩
      have hz : zeroRun x := by
        intro i hi0 hi1
        interval_cases i <;> simp_all
      refine ⟨hz, ?_⟩
      by_cases hb5 : x[0].val.testBit 5 = false
      · exact Or.inl hb5
      · have hb5t : x[0].val.testBit 5 = true := by simpa using hb5
        right
        have hTF : ((topDC x : ℕ) : F circomPrime) + ((midDC x : ℕ) : F circomPrime)
            + (1 - bitField (x[0].val.testBit 5)) = 0 := by
          rw [htF, hmF, hb5t]
          simp [bitField]
        have hb4 : x[0].val.testBit 4 = false := by
          apply (bitField_zero_iff _).mp
          rw [hTF, zero_mul, sub_zero] at h3
          exact h3
        refine ⟨hb4, ?_⟩
        intro hl0
        have hlF : ((lowDC x : ℕ) : F circomPrime) = 0 := by rw [hl0]; simp
        rw [hTF, hlF, add_zero, zero_mul] at h4
        simp at h4

/-- Completeness side: from the pattern, each stage's implication holds and the
final combined deficit is nonzero. -/
theorem weak_of_pattern (x : Emu (F circomPrime)) (hpatt : Pattern x) :
    (((topDC x : ℕ) : F circomPrime) = 0 → bitField (x[0].val.testBit 32) = 0) ∧
    ((((topDC x : ℕ) : F circomPrime) + ((midDC x : ℕ) : F circomPrime) = 0) →
      bitField (x[0].val.testBit 9) + bitField (x[0].val.testBit 8) +
        bitField (x[0].val.testBit 7) + bitField (x[0].val.testBit 6) = 0) ∧
    ((((topDC x : ℕ) : F circomPrime) + ((midDC x : ℕ) : F circomPrime)
        + (1 - bitField (x[0].val.testBit 5)) = 0) →
      bitField (x[0].val.testBit 4) = 0) ∧
    (((topDC x : ℕ) : F circomPrime) + ((midDC x : ℕ) : F circomPrime)
        + (1 - bitField (x[0].val.testBit 5)) + ((lowDC x : ℕ) : F circomPrime) ≠ 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    have ht0 : topDC x = 0 := (topF_zero_iff x).mp h
    rcases hpatt with htop | ⟨hb32, -⟩
    · exact absurd ht0 htop
    · rw [bitField, hb32]; rfl
  · intro h
    obtain ⟨ht0, hm0⟩ := (sumF_zero_iff x).mp h
    rcases hpatt with htop | ⟨-, hrest⟩
    · exact absurd ht0 htop
    rcases hrest with hmid | ⟨hz, -⟩
    · exact absurd hm0 hmid
    rw [bitField, bitField, bitField, bitField,
      hz 9 (by omega) (by omega), hz 8 (by omega) (by omega),
      hz 7 (by omega) (by omega), hz 6 (by omega) (by omega)]
    norm_num
  · intro h
    rw [tF_eq] at h
    obtain ⟨ht0, hm0, he1⟩ := sum3_zero_aux (bitNat_le_one _)
      ((small_cast_zero_iff (sum3_le_aux (topDC_le x) (midDC_le x))).mp h)
    have hb5 : x[0].val.testBit 5 = true := bit5_true_of_bitNat he1
    rcases hpatt with htop | ⟨-, hrest⟩
    · exact absurd ht0 htop
    rcases hrest with hmid | ⟨-, hlow⟩
    · exact absurd hm0 hmid
    rcases hlow with hb5f | ⟨hb4, -⟩
    · rw [hb5] at hb5f; exact absurd hb5f (by simp)
    · rw [bitField, hb4]; rfl
  · intro h
    rw [uF_eq] at h
    have hnat := (small_cast_zero_iff (uNat_le x)).mp h
    rw [uNat] at hnat
    obtain ⟨ht0, hm0, he1, hl0⟩ := sum4_zero_aux (bitNat_le_one _) hnat
    have hb5 : x[0].val.testBit 5 = true := bit5_true_of_bitNat he1
    rcases hpatt with htop | ⟨-, hrest⟩
    · exact absurd ht0 htop
    rcases hrest with hmid | ⟨-, hlow⟩
    · exact absurd hm0 hmid
    rcases hlow with hb5f | ⟨-, hlne⟩
    · rw [hb5] at hb5f; exact absurd hb5f (by simp)
    · exact absurd hl0 hlne

end ValidP
end Solution.Secp256k1ScalarMulFixedBase

end DonorFile1_15

-- Adapted donor module: ToBitsAffine
section DonorFile1_16

namespace Solution.Secp256k1ScalarMulFixedBase
namespace ToBitsAffine

open Utils.Bits

variable {p : ℕ} [Fact p.Prime] [Fact (p > 2)]

def main (w : ℕ) (x : Expression (F p)) : Circuit (F p) (Var (fields (w + 1)) (F p)) := do
  let low ← witnessVector w fun env => fieldToBits w (x.eval env)
  Circuit.forEach low assertBool
  let top := (((2 ^ w : ℕ) : F p)⁻¹ : F p) * (x - fieldFromBitsExpr low)
  assertZero (top * (top - 1))
  return low.push top

instance elaborated (w : ℕ) : ElaboratedCircuit (F p) field (fields (w + 1)) (main w) := by
  elaborate_circuit

private theorem pow_lt {w : ℕ} (hn : 2 ^ (w + 1) < p) : 2 ^ w < p :=
  lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ w)) hn

private theorem pow_ne_zero' {w : ℕ} (hn : 2 ^ (w + 1) < p) :
    (((2 ^ w : ℕ) : F p) ≠ 0) := by
  intro h
  have hval : (((2 ^ w : ℕ) : F p).val) = 2 ^ w :=
    ZMod.val_natCast_of_lt (pow_lt hn)
  rw [h, ZMod.val_zero] at hval
  have hpos : 0 < 2 ^ w := Nat.two_pow_pos _
  omega

theorem fieldFromBits_push {w : ℕ} (low : Vector (F p) w) (top : F p) :
    fieldFromBits (low.push top) = fieldFromBits low + top * ((2 ^ w : ℕ) : F p) := by
  rw [fieldFromBits_succ w (low.push top)]
  have hpop : (low.push top).pop = low := by
    apply Vector.ext; intro i hi
    simp [Vector.getElem_pop', Vector.getElem_push_lt hi]
  rw [hpop, Vector.getElem_push_eq, Nat.cast_pow, Nat.cast_ofNat]

def toBitsAffine (w : ℕ) (hn : 2 ^ (w + 1) < p) : GeneralFormalCircuit (F p) field (fields (w + 1)) where
  main := main w

  ProverAssumptions (x : F p) _ _ := x.val < 2 ^ (w + 1)

  Spec (x : F p) (bits : Vector (F p) (w + 1)) _ :=
    x.val < 2 ^ (w + 1) ∧ bits = fieldToBits (w + 1) x

  soundness := by
    circuit_proof_start
    obtain ⟨h_bool, h_eq⟩ := h_holds
    set low_vars : Vector (Expression (F p)) w := Vector.mapRange w (fun i => var ⟨i₀ + i⟩) with hlv
    set low : Vector (F p) w := low_vars.map env with hlow
    set t : F p := (((2 ^ w : ℕ) : F p)⁻¹ : F p) * (input + -Expression.eval env (fieldFromBitsExpr low_vars)) with ht
    change t * (t + -1) = 0 at h_eq
    have hbase := pow_ne_zero' (w := w) hn
    have hE : Expression.eval env (fieldFromBitsExpr low_vars) = fieldFromBits low :=
      fieldFromBits_eval low_vars
    have h_low_bool : ∀ (i : ℕ) (hi : i < w), low[i] = 0 ∨ low[i] = 1 := by
      intro i hi
      have := h_bool ⟨i, hi⟩
      simp only [IsBool, hlow, hlv, Vector.getElem_map, Vector.getElem_mapRange, Expression.eval] at this ⊢
      exact this
    have h_top_bool : t = 0 ∨ t = 1 := by
      rcases mul_eq_zero.mp h_eq with h | h
      · exact Or.inl h
      · exact Or.inr (by linear_combination h)
    set bits : Vector (F p) (w + 1) := low.push t with hbits
    have h_bits : ∀ (i : ℕ) (hi : i < w + 1), bits[i] = 0 ∨ bits[i] = 1 := by
      intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
      · rw [hbits, Vector.getElem_push_lt hlt]; exact h_low_bool i hlt
      · rw [hbits, Vector.getElem_push_eq]; exact h_top_bool
    have hrecomp : fieldFromBits bits = input := by
      rw [hbits, fieldFromBits_push, ← hE, ht]
      field_simp
      ring
    have hval : input.val < 2 ^ (w + 1) := by
      rw [← hrecomp]; exact fieldFromBits_lt bits h_bits
    have htoBits : fieldToBits (w + 1) input = bits := by
      rw [← hrecomp]; exact fieldToBits_fieldFromBits hn bits h_bits
    refine ⟨hval, ?_⟩
    rw [htoBits, hbits, hlow]
    simp only [circuit_norm, Vector.map_push, hlv, ht, h_input]

  completeness := by
    circuit_proof_start
    set low_vars : Vector (Expression (F p)) w := Vector.mapRange w (fun i => var ⟨i₀ + i⟩) with hlv
    have hbase := pow_ne_zero' (w := w) hn
    refine ⟨?_, ?_⟩
    ·
      intro i
      rw [h_env i]
      rcases fieldToBits_bits (n := w) (x := input) i.val i.isLt with h | h <;>
        rw [h] <;> simp [IsBool]
    ·
      set base : ℕ := 2 ^ w with hbaseNat
      have hmap : low_vars.map env.toEnvironment = fieldToBits w input := by
        apply Vector.ext; intro i hi
        rw [hlv, Vector.getElem_map, Vector.getElem_mapRange]
        simpa using h_env ⟨i, hi⟩
      set v : ℕ := input.val with hv
      have hE0 : Expression.eval env.toEnvironment (fieldFromBitsExpr low_vars)
          = fieldFromBits (low_vars.map env.toEnvironment) := fieldFromBits_eval low_vars
      have hE : Expression.eval env.toEnvironment (fieldFromBitsExpr low_vars)
          = ((v % base : ℕ) : F p) := by
        rw [hE0, hmap, fieldFromBits_fieldToBits_mod, hbaseNat, hv]
      have htop_val : (((2 ^ w : ℕ) : F p)⁻¹ : F p) *
            (input + -Expression.eval env.toEnvironment (fieldFromBitsExpr low_vars))
          = ((v / base : ℕ) : F p) := by
        rw [hE]
        have hbaseF : ((base : F p) ≠ 0) := by rw [hbaseNat]; exact hbase
        have hinput : input = ((base * (v / base) + v % base : ℕ) : F p) := by
          rw [show base * (v / base) + v % base = v from Nat.div_add_mod v base, hv,
            ZMod.natCast_zmod_val]
        change ((base : F p)⁻¹ : F p) * (input + -((v % base : ℕ) : F p))
          = ((v / base : ℕ) : F p)
        rw [hinput]
        push_cast
        field_simp [hbaseF]
        ring
      rw [htop_val]
      have hq_lt : v / base < 2 := by
        apply Nat.div_lt_of_lt_mul
        rw [hbaseNat, ← pow_succ]
        exact h_assumptions
      set q : ℕ := v / base with hq_def
      clear_value q
      rcases (by omega : q = 0 ∨ q = 1) with h | h <;>
        rw [h] <;> norm_num

@[simp] theorem main_localLength (w : ℕ) (x : Expression (F p)) (n : ℕ) :
    (main w x).localLength n = w := by
  simp [main, circuit_norm]

theorem computableWitnesses (w : ℕ) (hn : 2 ^ (w + 1) < p) :
    (toBitsAffine (p := p) w hn).base.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition input env env')
    (((toBitsAffine (p := p) w hn).main input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold toBitsAffine main
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.witnessVector_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.forEach_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.assertZero_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.pure_structuralComputableWitnesses_iff,
    and_true]
  and_intros
  · intro _ h_input
    rw [CircuitType.eval_expression_prover_to_verifier (M := field),
      CircuitType.eval_expression_prover_to_verifier (M := field)] at h_input
    have h_input_expr :
        Expression.eval env.toEnvironment input = Expression.eval env'.toEnvironment input := by
      simpa only [CircuitType.eval_var_field] using h_input
    exact congrArg (Utils.Bits.fieldToBits w) h_input_expr
  · intro i
    apply Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
    · intro k env env' hk h_agree _
      rw [CircuitType.eval_expression_prover_to_verifier (M := field),
        CircuitType.eval_expression_prover_to_verifier (M := field)]
      rw [show eval env.toEnvironment
            ((witnessVector w fun env =>
                Utils.Bits.fieldToBits w (Expression.eval env.toEnvironment input)).output
          offset)[i.val] =
            env.get (offset + i.val) by
          rw [CircuitType.eval_expression (M := field)]
          simp [Circuit.witnessVector, Circuit.output,
            ProvableType.eval, explicit_provable_type, size, Vector.getElem_mapRange,
            Expression.eval],
        show eval env'.toEnvironment
            ((witnessVector w fun env =>
                Utils.Bits.fieldToBits w (Expression.eval env.toEnvironment input)).output
              offset)[i.val] =
            env'.get (offset + i.val) by
          rw [CircuitType.eval_expression (M := field)]
          simp [Circuit.witnessVector, Circuit.output,
            ProvableType.eval, explicit_provable_type, size, Vector.getElem_mapRange,
            Expression.eval]]
      exact h_agree (offset + i.val) (by
        have hi : i.val < w := i.isLt
        have hbase : offset + w ≤ k := by
          simpa [Circuit.localLength] using hk
        omega)
    · exact assertBoolComputableWitnesses

end ToBitsAffine
end Solution.Secp256k1ScalarMulFixedBase

end DonorFile1_16

-- Adapted donor module: ValidP
section DonorFile1_17

/-!
# secp256k1-specific canonical field validation

Every field-result gadget used to run `Normalize` and then the generic
`LessThan` gadget against `p`.  That decomposes 256 result bits once and then
allocates another 256-bit difference.  Here the four limb decompositions are
kept in scope and compared with the constant

`p = 2^256 - 2^32 - 977`.

The binary representation of `p` has only six zero positions:
`32, 9, 8, 7, 6, 4`.  Three zero tests summarize the long all-one runs and two
product witnesses carry the equal-prefix state.  The resulting assertion has
264 witnesses and 272 rows, versus 520 witnesses and 529 rows for
`Normalize + LessThan`.
-/

namespace Solution.Secp256k1ScalarMulFixedBase
namespace ValidP

open Utils.Bits

/-- Sparse comparison against the secp256k1 prime after the four limbs have
already been decomposed into bits.

Only four implications are needed, and each is delivered by a single row
`target - deficit * u = 0` with a witnessed `u`: whenever the (nonnegative,
small) deficit vanishes, the target must vanish too.  Consecutive prefix stages
are combined by *adding* deficit counters instead of multiplying equality
flags, so no `IsZeroField` gadget and no product witness is needed. -/
def tail (b0 b1 b2 b3 : Var (fields limbBits) (F circomPrime)) :
    Circuit (F circomPrime) Unit := do
  -- p has ones at every position 255..33.  A zero in this run makes x < p.
  let topDef := deficitSlice b0 33 31 (by decide)
    + deficitSlice b1 0 64 (by decide)
    + deficitSlice b2 0 64 (by decide)
    + deficitSlice b3 0 64 (by decide)
  -- If the top prefix equals p, bit 32 (a zero of p) must be zero.
  let u1 ← witnessField fun env =>
    if Expression.eval env.toEnvironment topDef = 0 then 0
    else Expression.eval env.toEnvironment b0[32]
      * (Expression.eval env.toEnvironment topDef)⁻¹
  assertZero (b0[32] - topDef * u1)

  -- Positions 31..10 are another all-one run of p.  Equality of the whole
  -- prefix down to bit 10 is `topDef + midDef = 0`.
  let sDef := topDef + deficitSlice b0 10 22 (by decide)
  let zRun := b0[9] + b0[8] + b0[7] + b0[6]
  let u2 ← witnessField fun env =>
    if Expression.eval env.toEnvironment sDef = 0 then 0
    else Expression.eval env.toEnvironment zRun
      * (Expression.eval env.toEnvironment sDef)⁻¹
  assertZero (zRun - sDef * u2)

  -- p[9..6] = 0 is now forced.  p[5] = 1, so the prefix stays equal exactly
  -- when `sDef + (1 - b0[5]) = 0`; then p[4] = 0 forces bit 4 to vanish.
  let tDef := sDef + ((1 : Expression (F circomPrime)) - b0[5])
  let u3 ← witnessField fun env =>
    if Expression.eval env.toEnvironment tDef = 0 then 0
    else Expression.eval env.toEnvironment b0[4]
      * (Expression.eval env.toEnvironment tDef)⁻¹
  assertZero (b0[4] - tDef * u3)

  -- p[3..0] = 1.  Equality all the way through is forbidden because the
  -- validator proves a strict inequality: the total deficit must be nonzero.
  let uDef := tDef + deficitSlice b0 0 4 (by decide)
  let u4 ← witnessField fun env =>
    if Expression.eval env.toEnvironment uDef = 0 then 0
    else (Expression.eval env.toEnvironment uDef)⁻¹
  assertZero (uDef * u4 - 1)

/-- Normalize four 64-bit limbs and prove their 256-bit value is below the
secp256k1 base-field prime using its sparse complement. -/
def main (x : Var Emu (F circomPrime)) : Circuit (F circomPrime) Unit := do
  let b0 ← ToBitsAffine.toBitsAffine 63 secpParams.hB x[0]
  let b1 ← ToBitsAffine.toBitsAffine 63 secpParams.hB x[1]
  let b2 ← ToBitsAffine.toBitsAffine 63 secpParams.hB x[2]
  let b3 ← ToBitsAffine.toBitsAffine 63 secpParams.hB x[3]
  tail b0 b1 b2 b3

instance elaborated : ElaboratedCircuit (F circomPrime) Emu unit main := by
  elaborate_circuit

def Assumptions (_x : Emu (F circomPrime)) : Prop := True

def Spec (x : Emu (F circomPrime)) : Prop := Fe.Valid x

set_option maxHeartbeats 4000000 in
theorem soundness :
    FormalAssertion.Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [tail, ToBitsAffine.toBitsAffine, ToBitsAffine.main]
  obtain ⟨⟨hn0, hb0⟩, ⟨hn1, hb1⟩, ⟨hn2, hb2⟩, ⟨hn3, hb3⟩, h1, h2, h3, h4⟩ := h_holds
  have hx : ∀ (i : ℕ) (hi : i < 4), Expression.eval env input_var[i] = input[i] := by
    intro i hi
    rw [← h_input, Vector.getElem_map]
  rw [hx 0 (by omega)] at hn0 hb0
  rw [hx 1 (by omega)] at hn1 hb1
  rw [hx 2 (by omega)] at hn2 hb2
  rw [hx 3 (by omega)] at hn3 hb3
  have hn : BigInt.Normalized limbBits input := by
    intro i
    fin_cases i <;> assumption
  simp only [eval_ds (start := 33) (len := 31) (by decide) env _ input[0] hb0,
    eval_ds (start := 0) (len := 64) (by decide) env _ input[1] hb1,
    eval_ds (start := 0) (len := 64) (by decide) env _ input[2] hb2,
    eval_ds (start := 0) (len := 64) (by decide) env _ input[3] hb3,
    eval_ds (start := 10) (len := 22) (by decide) env _ input[0] hb0,
    eval_ds (start := 0) (len := 4) (by decide) env _ input[0] hb0,
    Nat.reduceLT, dite_true, Expression.eval] at h1 h2 h3 h4
  have hb0val : ∀ (i : ℕ) (hi : i < 63),
      env.get (i₀ + i) = if input[0].val.testBit i then 1 else 0 :=
    fun i hi => push_eval_bit env i₀ _ input[0] hb0 i hi
  have H1 : bitField (input[0].val.testBit 32)
      - ((topDC input : ℕ) : F circomPrime) * env.get (i₀ + 63 + 63 + 63 + 63) = 0 := by
    rw [bitField, ← hb0val 32 (by omega)]
    simp only [topDC]
    push_cast
    linear_combination h1
  have H2 : (bitField (input[0].val.testBit 9) + bitField (input[0].val.testBit 8)
        + bitField (input[0].val.testBit 7) + bitField (input[0].val.testBit 6))
      - (((topDC input : ℕ) : F circomPrime) + ((midDC input : ℕ) : F circomPrime))
        * env.get (i₀ + 63 + 63 + 63 + 63 + 1) = 0 := by
    rw [bitField, ← hb0val 9 (by omega), bitField, ← hb0val 8 (by omega),
      bitField, ← hb0val 7 (by omega), bitField, ← hb0val 6 (by omega)]
    simp only [topDC, midDC]
    push_cast
    linear_combination h2
  have H3 : bitField (input[0].val.testBit 4)
      - (((topDC input : ℕ) : F circomPrime) + ((midDC input : ℕ) : F circomPrime)
          + (1 - bitField (input[0].val.testBit 5)))
        * env.get (i₀ + 63 + 63 + 63 + 63 + 1 + 1) = 0 := by
    rw [bitField, ← hb0val 4 (by omega), bitField, ← hb0val 5 (by omega)]
    simp only [topDC, midDC]
    push_cast
    linear_combination h3
  have H4 : (((topDC input : ℕ) : F circomPrime) + ((midDC input : ℕ) : F circomPrime)
        + (1 - bitField (input[0].val.testBit 5)) + ((lowDC input : ℕ) : F circomPrime))
      * env.get (i₀ + 63 + 63 + 63 + 63 + 1 + 1 + 1) - 1 = 0 := by
    rw [bitField, ← hb0val 5 (by omega)]
    simp only [topDC, midDC, lowDC]
    push_cast
    linear_combination h4
  exact ⟨hn, (pattern_iff_lt input hn).mp (pattern_of_weak input H1 H2 H3 H4)⟩

set_option maxHeartbeats 0 in
theorem completeness :
    FormalAssertion.Completeness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [tail, ToBitsAffine.toBitsAffine, ToBitsAffine.main]
  obtain ⟨hb0gen, hb1gen, hb2gen, hb3gen, hv1, hv2, hv3, hv4⟩ := h_env
  have hx : ∀ (i : ℕ) (hi : i < 4),
      Expression.eval env.toEnvironment input_var[i] = input[i] := by
    intro i hi
    rw [← h_input, Vector.getElem_map]
  have hn := h_spec.1
  have hn0 : (Expression.eval env.toEnvironment input_var[0]).val < 2 ^ limbBits := by
    rw [hx 0 (by omega)]; exact hn 0
  have hn1 : (Expression.eval env.toEnvironment input_var[1]).val < 2 ^ limbBits := by
    rw [hx 1 (by omega)]; exact hn 1
  have hn2 : (Expression.eval env.toEnvironment input_var[2]).val < 2 ^ limbBits := by
    rw [hx 2 (by omega)]; exact hn 2
  have hn3 : (Expression.eval env.toEnvironment input_var[3]).val < 2 ^ limbBits := by
    rw [hx 3 (by omega)]; exact hn 3
  obtain ⟨-, hb0⟩ := hb0gen hn0
  obtain ⟨-, hb1⟩ := hb1gen hn1
  obtain ⟨-, hb2⟩ := hb2gen hn2
  obtain ⟨-, hb3⟩ := hb3gen hn3
  rw [hx 0 (by omega)] at hb0
  rw [hx 1 (by omega)] at hb1
  rw [hx 2 (by omega)] at hb2
  rw [hx 3 (by omega)] at hb3
  simp only [eval_ds (start := 33) (len := 31) (by decide) env.toEnvironment _ input[0] hb0,
    eval_ds (start := 0) (len := 64) (by decide) env.toEnvironment _ input[1] hb1,
    eval_ds (start := 0) (len := 64) (by decide) env.toEnvironment _ input[2] hb2,
    eval_ds (start := 0) (len := 64) (by decide) env.toEnvironment _ input[3] hb3,
    eval_ds (start := 10) (len := 22) (by decide) env.toEnvironment _ input[0] hb0,
    eval_ds (start := 0) (len := 4) (by decide) env.toEnvironment _ input[0] hb0,
    Nat.reduceLT, dite_true, Expression.eval] at hv1 hv2 hv3 hv4 ⊢
  have hb0val : ∀ (i : ℕ) (hi : i < 63),
      env.get (i₀ + i) = if input[0].val.testBit i then 1 else 0 :=
    fun i hi => push_eval_bit env.toEnvironment i₀ _ input[0] hb0 i hi
  have hdt : ((dc input[0].val 33 31 : ℕ) : F circomPrime)
      + ((dc input[1].val 0 64 : ℕ) : F circomPrime)
      + ((dc input[2].val 0 64 : ℕ) : F circomPrime)
      + ((dc input[3].val 0 64 : ℕ) : F circomPrime)
      = ((topDC input : ℕ) : F circomPrime) := by
    simp only [topDC]; push_cast; ring
  have hdm : ((dc input[0].val 10 22 : ℕ) : F circomPrime)
      = ((midDC input : ℕ) : F circomPrime) := rfl
  have hdl : ((dc input[0].val 0 4 : ℕ) : F circomPrime)
      = ((lowDC input : ℕ) : F circomPrime) := rfl
  obtain ⟨w1, w2, w3, w4⟩ :=
    weak_of_pattern input ((pattern_iff_lt input hn).mpr h_spec.2)
  simp only [Nat.cast_one, bitField, sub_eq_add_neg] at w3 w4
  refine ⟨hn0, hn1, hn2, hn3, ?_, ?_, ?_, ?_⟩
  · rw [hv1, hdt, hb0val 32 (by omega)]
    linear_combination inv_row_of_imp
      (d := ((topDC input : ℕ) : F circomPrime))
      (num := (if input[0].val.testBit 32 then (1 : F circomPrime) else 0))
      (fun h => w1 h)
  · rw [hv2, hdt, hdm, hb0val 9 (by omega), hb0val 8 (by omega),
      hb0val 7 (by omega), hb0val 6 (by omega)]
    linear_combination inv_row_of_imp
      (d := ((topDC input : ℕ) : F circomPrime) + ((midDC input : ℕ) : F circomPrime))
      (num := (if input[0].val.testBit 9 then (1 : F circomPrime) else 0)
        + (if input[0].val.testBit 8 then (1 : F circomPrime) else 0)
        + (if input[0].val.testBit 7 then (1 : F circomPrime) else 0)
        + (if input[0].val.testBit 6 then (1 : F circomPrime) else 0))
      (fun h => w2 h)
  · rw [hv3, hdt, hdm, hb0val 4 (by omega), hb0val 5 (by omega)]
    linear_combination inv_row_of_imp
      (d := ((topDC input : ℕ) : F circomPrime) + ((midDC input : ℕ) : F circomPrime)
        + ((1 : F circomPrime) + -(if input[0].val.testBit 5 then (1 : F circomPrime) else 0)))
      (num := (if input[0].val.testBit 4 then (1 : F circomPrime) else 0))
      (fun h => w3 h)
  · rw [hv4, hdt, hdm, hdl, hb0val 5 (by omega)]
    linear_combination inv_row_of_ne
      (d := ((topDC input : ℕ) : F circomPrime) + ((midDC input : ℕ) : F circomPrime)
        + ((1 : F circomPrime) + -(if input[0].val.testBit 5 then (1 : F circomPrime) else 0))
        + ((lowDC input : ℕ) : F circomPrime))
      w4

def circuit : FormalAssertion (F circomPrime) Emu where
  main
  elaborated
  Assumptions
  Spec
  soundness
  completeness

/-! ## Computable witnesses -/

private lemma input_limb_stable {input : Var Emu (F circomPrime)} {i : ℕ} (hi : i < numLimbs)
    {env env' : ProverEnvironment (F circomPrime)}
    (h : eval env input = eval env' input) :
    eval env input[i] = eval env' input[i] := by
  have hmap := emu_map_eval_eq_of_eval_eq h
  have hget : (input.map (Expression.eval env.toEnvironment))[i] =
      (input.map (Expression.eval env'.toEnvironment))[i] := by rw [hmap]
  simp only [Vector.getElem_map] at hget
  rw [CircuitType.eval_var_field_prover, CircuitType.eval_var_field_prover]
  exact hget

private lemma input_limb_stable' {input : Var Emu (F circomPrime)} {i : ℕ} (hi : i < numLimbs)
    {env env' : ProverEnvironment (F circomPrime)}
    (h : eval env input = eval env' input) :
    Expression.eval env.toEnvironment input[i] = Expression.eval env'.toEnvironment input[i] := by
  have hstep := input_limb_stable hi h
  rwa [CircuitType.eval_var_field_prover, CircuitType.eval_var_field_prover] at hstep

private lemma deficitSlice_eval_stable {base k start len : ℕ}
    (h : start + len ≤ limbBits) {env env' : ProverEnvironment (F circomPrime)}
    (h_agree : env.AgreesBelow k env') (hk : base + limbBits ≤ k) :
    Expression.eval env.toEnvironment
        (deficitSlice (Vector.mapRange limbBits fun i => var { index := base + i }) start len h) =
      Expression.eval env'.toEnvironment
        (deficitSlice (Vector.mapRange limbBits fun i => var { index := base + i }) start len h) := by
  unfold deficitSlice
  rw [eval_fold, eval_fold]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Expression.eval, Vector.getElem_mapRange]
  rw [h_agree (base + (start + i.val)) (by omega)]

/-- The affine top expression of the limb `k` decomposition is stable under
environment agreement below `k`, given the limb input is stable. -/
private lemma top_eval_stable {base k : ℕ} {env env' : ProverEnvironment (F circomPrime)}
    (inp : Expression (F circomPrime))
    (h_agree : env.AgreesBelow k env') (hk : base + 63 ≤ k)
    (hinp : Expression.eval env.toEnvironment inp = Expression.eval env'.toEnvironment inp) :
    Expression.eval env.toEnvironment
        (Expression.const (((2 ^ 63 : ℕ) : F circomPrime)⁻¹) *
          (inp - fieldFromBitsExpr (Vector.mapRange 63 fun i => var { index := base + i }))) =
      Expression.eval env'.toEnvironment
        (Expression.const (((2 ^ 63 : ℕ) : F circomPrime)⁻¹) *
          (inp - fieldFromBitsExpr (Vector.mapRange 63 fun i => var { index := base + i }))) := by
  simp only [Expression.eval, hinp]
  have hmeq : (Vector.mapRange 63 fun i => var { index := base + i }).map env.toEnvironment
      = (Vector.mapRange 63 fun i => var { index := base + i }).map env'.toEnvironment := by
    apply Vector.ext; intro j hj
    simp only [Vector.getElem_map, Vector.getElem_mapRange, Expression.eval]
    exact h_agree (base + j) (by omega)
  have hE1 : Expression.eval env.toEnvironment
      (fieldFromBitsExpr (Vector.mapRange 63 fun i => var { index := base + i })) =
        fieldFromBits ((Vector.mapRange 63 fun i => var { index := base + i }).map env.toEnvironment) :=
    fieldFromBits_eval _
  have hE2 : Expression.eval env'.toEnvironment
      (fieldFromBitsExpr (Vector.mapRange 63 fun i => var { index := base + i })) =
        fieldFromBits ((Vector.mapRange 63 fun i => var { index := base + i }).map env'.toEnvironment) :=
    fieldFromBits_eval _
  rw [hE1, hE2, hmeq]

/-- Stability of a deficit slice over the affine-top vector.  Low cells are
plain witnesses; the top cell (index 63) is the affine residual, whose stability
is supplied by `htop`. -/
private lemma deficitSlice_push_eval_stable {base k start len : ℕ}
    (h : start + len ≤ limbBits) (top : Expression (F circomPrime))
    {env env' : ProverEnvironment (F circomPrime)}
    (h_agree : env.AgreesBelow k env') (hk : base + 63 ≤ k)
    (htop : Expression.eval env.toEnvironment top = Expression.eval env'.toEnvironment top) :
    Expression.eval env.toEnvironment
        (deficitSlice ((Vector.mapRange 63 fun i => var { index := base + i }).push top) start len h) =
      Expression.eval env'.toEnvironment
        (deficitSlice ((Vector.mapRange 63 fun i => var { index := base + i }).push top) start len h) := by
  have h64 : start + len ≤ 64 := h
  unfold deficitSlice
  rw [eval_fold, eval_fold]
  have hcells : ∀ (j : ℕ) (hj : j < 63 + 1),
      Expression.eval env.toEnvironment
        (((Vector.mapRange 63 fun m => var { index := base + m }).push top)[j]'hj) =
      Expression.eval env'.toEnvironment
        (((Vector.mapRange 63 fun m => var { index := base + m }).push top)[j]'hj) := by
    intro j hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
    · simp only [Vector.getElem_push_lt hlt, Vector.getElem_mapRange, Expression.eval]
      rw [h_agree (base + j) (by omega)]
    · simp only [Vector.getElem_push_eq]
      exact htop
  apply Finset.sum_congr rfl
  intro i _
  have hi := i.isLt
  simp only [Expression.eval]
  rw [hcells (start + i.val) (by omega)]

set_option maxHeartbeats 3200000 in
open Challenge.Utils.ComputableWitnessLemmas in
theorem computableWitnesses : circuit.base.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations offset)
  apply FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  have hT : ∀ (y : Expression (F circomPrime)) (o : ℕ),
      (subcircuitWithAssertion
        (ToBitsAffine.toBitsAffine 63 secpParams.hB) y).localLength o = 63 := by
    intro y o
    simp [subcircuitWithAssertion, ToBitsAffine.toBitsAffine, circuit_norm]
  unfold main tail
  simp only [
    Circuit.bind_structuralComputableWitnesses_iff,
    Circuit.witnessField_structuralComputableWitnesses_iff,
    Circuit.assertZero_structuralComputableWitnesses_iff,
    hT, and_true]
  and_intros
  all_goals try trivial
  · exact GeneralFormalCircuit.subcircuit_flatStructuralComputableWitnesses
      (ToBitsAffine.toBitsAffine 63 secpParams.hB) input input[0] offset
      (fun _ _ hinput => input_limb_stable (by decide) hinput)
      (ToBitsAffine.computableWitnesses 63 secpParams.hB) env env'
  · exact GeneralFormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (ToBitsAffine.toBitsAffine 63 secpParams.hB) input input[1] (offset + 63)
      (fun _ _ _ _ _ hinput => input_limb_stable (by decide) hinput)
      (ToBitsAffine.computableWitnesses 63 secpParams.hB) env env'
  · exact GeneralFormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (ToBitsAffine.toBitsAffine 63 secpParams.hB) input input[2] (offset + 63 + 63)
      (fun _ _ _ _ _ hinput => input_limb_stable (by decide) hinput)
      (ToBitsAffine.computableWitnesses 63 secpParams.hB) env env'
  · exact GeneralFormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (ToBitsAffine.toBitsAffine 63 secpParams.hB) input input[3] (offset + 63 + 63 + 63)
      (fun _ _ _ _ _ hinput => input_limb_stable (by decide) hinput)
      (ToBitsAffine.computableWitnesses 63 secpParams.hB) env env'
  · intro h_agree hcond
    have hi0 := input_limb_stable' (i := 0) (by decide) hcond
    have hi1 := input_limb_stable' (i := 1) (by decide) hcond
    have hi2 := input_limb_stable' (i := 2) (by decide) hcond
    have hi3 := input_limb_stable' (i := 3) (by decide) hcond
    simp only [circuit_norm, ToBitsAffine.toBitsAffine,
      Nat.reduceLT, dite_true]
    rw [deficitSlice_push_eval_stable (base := offset) (start := 33) (len := 31)
        (by decide) _ h_agree (by omega)
        (top_eval_stable (base := offset) input[0] h_agree (by omega) hi0),
      deficitSlice_push_eval_stable (base := offset + 63) (start := 0) (len := 64)
        (by decide) _ h_agree (by omega)
        (top_eval_stable (base := offset + 63) input[1] h_agree (by omega) hi1),
      deficitSlice_push_eval_stable (base := offset + 63 + 63) (start := 0) (len := 64)
        (by decide) _ h_agree (by omega)
        (top_eval_stable (base := offset + 63 + 63) input[2] h_agree (by omega) hi2),
      deficitSlice_push_eval_stable (base := offset + 63 + 63 + 63)
        (start := 0) (len := 64) (by decide) _ h_agree (by omega)
        (top_eval_stable (base := offset + 63 + 63 + 63) input[3] h_agree (by omega) hi3),
      h_agree (offset + 32) (by omega)]
  · intro h_agree hcond
    have hi0 := input_limb_stable' (i := 0) (by decide) hcond
    have hi1 := input_limb_stable' (i := 1) (by decide) hcond
    have hi2 := input_limb_stable' (i := 2) (by decide) hcond
    have hi3 := input_limb_stable' (i := 3) (by decide) hcond
    simp only [circuit_norm, ToBitsAffine.toBitsAffine,
      Nat.reduceLT, dite_true]
    rw [deficitSlice_push_eval_stable (base := offset) (start := 33) (len := 31)
        (by decide) _ h_agree (by omega)
        (top_eval_stable (base := offset) input[0] h_agree (by omega) hi0),
      deficitSlice_push_eval_stable (base := offset + 63) (start := 0) (len := 64)
        (by decide) _ h_agree (by omega)
        (top_eval_stable (base := offset + 63) input[1] h_agree (by omega) hi1),
      deficitSlice_push_eval_stable (base := offset + 63 + 63) (start := 0) (len := 64)
        (by decide) _ h_agree (by omega)
        (top_eval_stable (base := offset + 63 + 63) input[2] h_agree (by omega) hi2),
      deficitSlice_push_eval_stable (base := offset + 63 + 63 + 63)
        (start := 0) (len := 64) (by decide) _ h_agree (by omega)
        (top_eval_stable (base := offset + 63 + 63 + 63) input[3] h_agree (by omega) hi3),
      deficitSlice_push_eval_stable (base := offset) (start := 10) (len := 22)
        (by decide) _ h_agree (by omega)
        (top_eval_stable (base := offset) input[0] h_agree (by omega) hi0),
      h_agree (offset + 9) (by omega), h_agree (offset + 8) (by omega),
      h_agree (offset + 7) (by omega), h_agree (offset + 6) (by omega)]
  · intro h_agree hcond
    have hi0 := input_limb_stable' (i := 0) (by decide) hcond
    have hi1 := input_limb_stable' (i := 1) (by decide) hcond
    have hi2 := input_limb_stable' (i := 2) (by decide) hcond
    have hi3 := input_limb_stable' (i := 3) (by decide) hcond
    simp only [circuit_norm, ToBitsAffine.toBitsAffine,
      Nat.reduceLT, dite_true]
    rw [deficitSlice_push_eval_stable (base := offset) (start := 33) (len := 31)
        (by decide) _ h_agree (by omega)
        (top_eval_stable (base := offset) input[0] h_agree (by omega) hi0),
      deficitSlice_push_eval_stable (base := offset + 63) (start := 0) (len := 64)
        (by decide) _ h_agree (by omega)
        (top_eval_stable (base := offset + 63) input[1] h_agree (by omega) hi1),
      deficitSlice_push_eval_stable (base := offset + 63 + 63) (start := 0) (len := 64)
        (by decide) _ h_agree (by omega)
        (top_eval_stable (base := offset + 63 + 63) input[2] h_agree (by omega) hi2),
      deficitSlice_push_eval_stable (base := offset + 63 + 63 + 63)
        (start := 0) (len := 64) (by decide) _ h_agree (by omega)
        (top_eval_stable (base := offset + 63 + 63 + 63) input[3] h_agree (by omega) hi3),
      deficitSlice_push_eval_stable (base := offset) (start := 10) (len := 22)
        (by decide) _ h_agree (by omega)
        (top_eval_stable (base := offset) input[0] h_agree (by omega) hi0),
      h_agree (offset + 5) (by omega), h_agree (offset + 4) (by omega)]
  · intro h_agree hcond
    have hi0 := input_limb_stable' (i := 0) (by decide) hcond
    have hi1 := input_limb_stable' (i := 1) (by decide) hcond
    have hi2 := input_limb_stable' (i := 2) (by decide) hcond
    have hi3 := input_limb_stable' (i := 3) (by decide) hcond
    simp only [circuit_norm, ToBitsAffine.toBitsAffine,
      Nat.reduceLT, dite_true]
    rw [deficitSlice_push_eval_stable (base := offset) (start := 33) (len := 31)
        (by decide) _ h_agree (by omega)
        (top_eval_stable (base := offset) input[0] h_agree (by omega) hi0),
      deficitSlice_push_eval_stable (base := offset + 63) (start := 0) (len := 64)
        (by decide) _ h_agree (by omega)
        (top_eval_stable (base := offset + 63) input[1] h_agree (by omega) hi1),
      deficitSlice_push_eval_stable (base := offset + 63 + 63) (start := 0) (len := 64)
        (by decide) _ h_agree (by omega)
        (top_eval_stable (base := offset + 63 + 63) input[2] h_agree (by omega) hi2),
      deficitSlice_push_eval_stable (base := offset + 63 + 63 + 63)
        (start := 0) (len := 64) (by decide) _ h_agree (by omega)
        (top_eval_stable (base := offset + 63 + 63 + 63) input[3] h_agree (by omega) hi3),
      deficitSlice_push_eval_stable (base := offset) (start := 10) (len := 22)
        (by decide) _ h_agree (by omega)
        (top_eval_stable (base := offset) input[0] h_agree (by omega) hi0),
      deficitSlice_push_eval_stable (base := offset) (start := 0) (len := 4)
        (by decide) _ h_agree (by omega)
        (top_eval_stable (base := offset) input[0] h_agree (by omega) hi0),
      h_agree (offset + 5) (by omega)]

theorem computableWitness : ∀ n input,
    ProverEnvironment.OnlyAccessedBelow n
      (fun env : ProverEnvironment (F circomPrime) => eval env input) →
    Circuit.ComputableWitnesses (main input) n :=
  Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnesses_implies
    (circuit := circuit.base) computableWitnesses

end ValidP
end Solution.Secp256k1ScalarMulFixedBase

end DonorFile1_17

-- Adapted donor module: ValidPBytes
section DonorFile1_18

namespace Solution.Secp256k1ScalarMulFixedBase
namespace ValidPBytes

open Utils.Bits
open ValidP

/-- Pack one little-endian byte from the four limb bit vectors. -/
def byteFromBits (b0 b1 b2 b3 : Var (fields limbBits) (F circomPrime))
    (t : Fin coordBytes) : Expression (F circomPrime) :=
  Fin.foldl 8 (fun acc j =>
    let k := 8 * (t.val % bytesPerLimb) + j.val
    let bit := if t.val < 8 then b0[k]'(by
        have hm : t.val % 8 < 8 := Nat.mod_lt _ (by decide)
        change 8 * (t.val % 8) + j.val < 64
        omega)
      else if t.val < 16 then b1[k]'(by
        have hm : t.val % 8 < 8 := Nat.mod_lt _ (by decide)
        change 8 * (t.val % 8) + j.val < 64
        omega)
      else if t.val < 24 then b2[k]'(by
        have hm : t.val % 8 < 8 := Nat.mod_lt _ (by decide)
        change 8 * (t.val % 8) + j.val < 64
        omega)
      else b3[k]'(by
        have hm : t.val % 8 < 8 := Nat.mod_lt _ (by decide)
        change 8 * (t.val % 8) + j.val < 64
        omega)
    acc + bit * (((2 ^ j.val : ℕ) : F circomPrime) : Expression (F circomPrime))) 0

/-- `ValidP`, additionally exposing the already-proven coordinate bits as bytes.
The returned bytes are affine expressions, so this has exactly the same local
length and constraints as `ValidP.main`. -/
def main (x : Var Emu (F circomPrime)) :
    Circuit (F circomPrime) (Var (fields coordBytes) (F circomPrime)) := do
  let b0 ← ToBitsAffine.toBitsAffine 63 secpParams.hB x[0]
  let b1 ← ToBitsAffine.toBitsAffine 63 secpParams.hB x[1]
  let b2 ← ToBitsAffine.toBitsAffine 63 secpParams.hB x[2]
  let b3 ← ToBitsAffine.toBitsAffine 63 secpParams.hB x[3]
  ValidP.tail b0 b1 b2 b3
  return Vector.ofFn fun t => byteFromBits b0 b1 b2 b3 t

instance elaborated : ElaboratedCircuit (F circomPrime) Emu (fields coordBytes) main := by
  elaborate_circuit

def Assumptions (_x : Emu (F circomPrime)) (_data : ProverData (F circomPrime)) :
    Prop := True

def ProverAssumptions (x : Emu (F circomPrime))
    (_data : ProverData (F circomPrime)) (_hint : ProverHint (F circomPrime)) :
    Prop := Fe.Valid x

def Spec (x : Emu (F circomPrime)) (bytes : fields coordBytes (F circomPrime))
    (_data : ProverData (F circomPrime)) : Prop :=
  Fe.Valid x ∧ ToBytes.Spec x bytes

def ProverSpec (_x : Emu (F circomPrime))
    (_bytes : fields coordBytes (F circomPrime)) (_hint : ProverHint (F circomPrime)) :
    Prop := True

private def byteFromFieldBits
    (b0 b1 b2 b3 : Vector (F circomPrime) limbBits) (t : Fin coordBytes) :
    F circomPrime :=
  Fin.foldl 8 (fun acc j =>
    let k := 8 * (t.val % bytesPerLimb) + j.val
    let bit := if t.val < 8 then b0[k]'(by
        have hm : t.val % 8 < 8 := Nat.mod_lt _ (by decide)
        change 8 * (t.val % 8) + j.val < 64
        omega)
      else if t.val < 16 then b1[k]'(by
        have hm : t.val % 8 < 8 := Nat.mod_lt _ (by decide)
        change 8 * (t.val % 8) + j.val < 64
        omega)
      else if t.val < 24 then b2[k]'(by
        have hm : t.val % 8 < 8 := Nat.mod_lt _ (by decide)
        change 8 * (t.val % 8) + j.val < 64
        omega)
      else b3[k]'(by
        have hm : t.val % 8 < 8 := Nat.mod_lt _ (by decide)
        change 8 * (t.val % 8) + j.val < 64
        omega)
    acc + bit * ((2 ^ j.val : ℕ) : F circomPrime)) 0

private lemma eval_byteFromBits (env : Environment (F circomPrime))
    (b0 b1 b2 b3 : Var (fields limbBits) (F circomPrime))
    (t : Fin coordBytes) :
    Expression.eval env (byteFromBits b0 b1 b2 b3 t) =
      byteFromFieldBits (Vector.map (Expression.eval env) b0)
        (Vector.map (Expression.eval env) b1)
        (Vector.map (Expression.eval env) b2)
        (Vector.map (Expression.eval env) b3) t := by
  unfold byteFromBits byteFromFieldBits
  rw [ToBytes.eval_foldl_add]
  simp only [Fin.foldl_to_sum, Expression.eval, Vector.getElem_map]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> rfl

theorem byteFromBits_eval_stable
    (b0 b1 b2 b3 : Var (fields limbBits) (F circomPrime))
    {env env' : ProverEnvironment (F circomPrime)}
    (hb0 : ∀ (i : ℕ) (hi : i < limbBits),
      Expression.eval env.toEnvironment (b0[i]'hi) =
        Expression.eval env'.toEnvironment (b0[i]'hi))
    (hb1 : ∀ (i : ℕ) (hi : i < limbBits),
      Expression.eval env.toEnvironment (b1[i]'hi) =
        Expression.eval env'.toEnvironment (b1[i]'hi))
    (hb2 : ∀ (i : ℕ) (hi : i < limbBits),
      Expression.eval env.toEnvironment (b2[i]'hi) =
        Expression.eval env'.toEnvironment (b2[i]'hi))
    (hb3 : ∀ (i : ℕ) (hi : i < limbBits),
      Expression.eval env.toEnvironment (b3[i]'hi) =
        Expression.eval env'.toEnvironment (b3[i]'hi))
    (t : Fin coordBytes) :
    Expression.eval env.toEnvironment (byteFromBits b0 b1 b2 b3 t) =
      Expression.eval env'.toEnvironment (byteFromBits b0 b1 b2 b3 t) := by
  unfold byteFromBits
  rw [ToBytes.eval_foldl_add, ToBytes.eval_foldl_add]
  simp only [Fin.foldl_to_sum, Expression.eval]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs
  · rw [hb0]
  · rw [hb1]
  · rw [hb2]
  · rw [hb3]

theorem fieldFromBitsExpr_eval_stable {w : ℕ}
    (bits : Var (fields w) (F circomPrime))
    {env env' : ProverEnvironment (F circomPrime)}
    (hbits : ∀ (i : ℕ) (hi : i < w),
      Expression.eval env.toEnvironment (bits[i]'hi) =
        Expression.eval env'.toEnvironment (bits[i]'hi)) :
    Expression.eval env.toEnvironment (fieldFromBitsExpr bits) =
      Expression.eval env'.toEnvironment (fieldFromBitsExpr bits) := by
  change env.toEnvironment (fieldFromBitsExpr bits) =
    env'.toEnvironment (fieldFromBitsExpr bits)
  rw [fieldFromBits_eval (eval := env.toEnvironment) bits,
    fieldFromBits_eval (eval := env'.toEnvironment) bits]
  congr 1
  apply Vector.ext
  intro i hi
  simpa only [Vector.getElem_map] using hbits i hi

theorem toBitsAffine_output_eval_stable (w : ℕ) (x : Expression (F circomPrime))
    {offset k : ℕ} {env env' : ProverEnvironment (F circomPrime)}
    (hx : Expression.eval env.toEnvironment x =
      Expression.eval env'.toEnvironment x)
    (h_agree : env.AgreesBelow k env') (hk : offset + w ≤ k) :
    ∀ (i : ℕ) (hi : i < w + 1),
      Expression.eval env.toEnvironment (((ToBitsAffine.main w x).output offset)[i]'hi) =
        Expression.eval env'.toEnvironment (((ToBitsAffine.main w x).output offset)[i]'hi) := by
  intro i hi
  simp only [ToBitsAffine.main, circuit_norm]
  by_cases hlt : i < w
  · simp only [hlt, ↓reduceDIte, Vector.getElem_mapRange, Expression.eval]
    exact h_agree (offset + i) (by omega)
  · simp only [hlt, ↓reduceDIte, Expression.eval]
    rw [hx]
    rw [fieldFromBitsExpr_eval_stable (env := env) (env' := env')
      (Vector.mapRange w fun i => var { index := offset + i })
      (fun j hj => by
        rw [Vector.getElem_mapRange]
        simp only [Expression.eval]
        exact h_agree (offset + j) (by omega))]

theorem output_eval_stable (x : Var Emu (F circomPrime))
    {offset k : ℕ} {env env' : ProverEnvironment (F circomPrime)}
    (hx : eval env x = eval env' x)
    (h_agree : env.AgreesBelow k env') (hk : offset + 260 ≤ k) :
    Vector.map (Expression.eval env.toEnvironment) ((main x).output offset) =
      Vector.map (Expression.eval env'.toEnvironment) ((main x).output offset) := by
  simp only [main, circuit_norm, ToBitsAffine.toBitsAffine, ToBitsAffine.main_localLength]
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_map, Vector.getElem_ofFn]
  apply byteFromBits_eval_stable
  · exact toBitsAffine_output_eval_stable 63 x[0] (by
      have h0 := congrArg (fun y : Emu (F circomPrime) => y[0]) hx
      change (eval env x)[0] = (eval env' x)[0] at h0
      rw [← ProvableType.getElem_eval_fields_prover (env := env) x 0 (by decide),
        ← ProvableType.getElem_eval_fields_prover (env := env') x 0 (by decide)] at h0
      exact h0) h_agree (by omega)
  · exact toBitsAffine_output_eval_stable 63 x[1] (by
      have h1 := congrArg (fun y : Emu (F circomPrime) => y[1]) hx
      change (eval env x)[1] = (eval env' x)[1] at h1
      rw [← ProvableType.getElem_eval_fields_prover (env := env) x 1 (by decide),
        ← ProvableType.getElem_eval_fields_prover (env := env') x 1 (by decide)] at h1
      exact h1) h_agree (by omega)
  · exact toBitsAffine_output_eval_stable 63 x[2] (by
      have h2 := congrArg (fun y : Emu (F circomPrime) => y[2]) hx
      change (eval env x)[2] = (eval env' x)[2] at h2
      rw [← ProvableType.getElem_eval_fields_prover (env := env) x 2 (by decide),
        ← ProvableType.getElem_eval_fields_prover (env := env') x 2 (by decide)] at h2
      exact h2) h_agree (by omega)
  · exact toBitsAffine_output_eval_stable 63 x[3] (by
      have h3 := congrArg (fun y : Emu (F circomPrime) => y[3]) hx
      change (eval env x)[3] = (eval env' x)[3] at h3
      rw [← ProvableType.getElem_eval_fields_prover (env := env) x 3 (by decide),
        ← ProvableType.getElem_eval_fields_prover (env := env') x 3 (by decide)] at h3
      exact h3) h_agree (by omega)

private lemma fromBits_chunk (v : ℕ) (r : Fin 8) :
    fromBits (Vector.ofFn fun j : Fin 8 => (toBits 64 v)[8 * r.val + j.val]'(by
      have hr := r.isLt
      have hj := j.isLt
      omega)) = ToBytes.byteOfNat v r.val := by
  rw [show (Vector.ofFn fun j : Fin 8 => (toBits 64 v)[8 * r.val + j.val]'(by
        have hr := r.isLt
        have hj := j.isLt
        omega)) = toBits 8 (v / 2 ^ (8 * r.val)) by
      apply Vector.ext
      intro i hi
      simp only [Vector.getElem_ofFn, toBits, Vector.getElem_mapRange]
      rw [Nat.testBit_div_two_pow]
      rw [show 8 * r.val + i = i + 8 * r.val by omega]]
  rw [fromBits_toBits_mod]
  unfold ToBytes.byteOfNat
  norm_num

set_option maxHeartbeats 0 in
private lemma byteFromFieldBits_eq_byteOfNat (z : F circomPrime)
    (r : Fin bytesPerLimb) :
    byteFromFieldBits (fieldToBits 64 z) (fieldToBits 64 z)
      (fieldToBits 64 z) (fieldToBits 64 z) ⟨r.val, by
        have hr := r.isLt
        simp only [bytesPerLimb, coordBytes] at hr ⊢
        omega⟩ = ((ToBytes.byteOfNat z.val r.val : ℕ) : F circomPrime) := by
  rw [show byteFromFieldBits (fieldToBits 64 z) (fieldToBits 64 z)
      (fieldToBits 64 z) (fieldToBits 64 z) ⟨r.val, by
        have hr := r.isLt
        simp only [bytesPerLimb, coordBytes] at hr ⊢
        omega⟩ = fieldFromBits (Vector.ofFn fun j : Fin 8 =>
          (fieldToBits 64 z)[8 * r.val + j.val]'(by
            have hr := r.isLt
            have hj := j.isLt
            simp only [bytesPerLimb] at hr
            omega)) by
      rw [fieldFromBits_as_sum]
      unfold byteFromFieldBits
      simp only [Fin.foldl_to_sum, fieldToBits, Vector.getElem_map,
        Vector.getElem_ofFn]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [Finset.mem_univ, true_and] at hj
      rw [if_pos (by simpa only [bytesPerLimb] using r.isLt)]
      simp only [bytesPerLimb, Nat.mod_eq_of_lt r.isLt]
      push_cast
      rfl]
  unfold fieldFromBits fieldToBits
  simp only [Vector.getElem_map]
  rw [show Vector.map ZMod.val
      (Vector.ofFn fun j : Fin 8 =>
        ((toBits 64 z.val)[8 * r.val + j.val]'(by
          have hr := r.isLt
          have hj := j.isLt
          simp only [bytesPerLimb] at hr
          omega) : F circomPrime)) =
      Vector.ofFn (fun j : Fin 8 =>
        (toBits 64 z.val)[8 * r.val + j.val]'(by
          have hr := r.isLt
          have hj := j.isLt
          simp only [bytesPerLimb] at hr
          omega)) by
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_map, Vector.getElem_ofFn]
    have hidx : 8 * r.val + i < 64 := by
      have hr := r.isLt
      simp only [bytesPerLimb] at hr
      omega
    rcases (show (toBits 64 z.val)[8 * r.val + i]'hidx = 0 ∨
        (toBits 64 z.val)[8 * r.val + i]'hidx = 1 from by
      simp [toBits, Vector.getElem_mapRange]) with h | h <;> rw [h]
    · exact ZMod.val_zero
    · exact ZMod.val_natCast_of_lt (by decide : 1 < circomPrime)]
  change ((fromBits (Vector.ofFn fun j : Fin 8 =>
    (toBits 64 z.val)[8 * r.val + j.val]'(by
      have hr := r.isLt
      have hj := j.isLt
      simp only [bytesPerLimb] at hr
      omega)) : ℕ) : F circomPrime) = _
  rw [fromBits_chunk z.val ⟨r.val, by simpa only [bytesPerLimb] using r.isLt⟩]

private lemma byteFromFieldBits_selected
    (b0 b1 b2 b3 : F circomPrime) (t : Fin coordBytes) :
    byteFromFieldBits (fieldToBits 64 b0) (fieldToBits 64 b1)
      (fieldToBits 64 b2) (fieldToBits 64 b3) t =
      ((ToBytes.byteOfNat
        (if t.val < 8 then b0.val else if t.val < 16 then b1.val
          else if t.val < 24 then b2.val else b3.val)
        (t.val % 8) : ℕ) : F circomPrime) := by
  have hr : t.val % 8 < 8 := Nat.mod_lt _ (by decide)
  by_cases h0 : t.val < 8
  · simpa [byteFromFieldBits, h0, Nat.mod_eq_of_lt h0] using
      byteFromFieldBits_eq_byteOfNat b0 ⟨t.val, h0⟩
  · by_cases h1 : t.val < 16
    · simpa [byteFromFieldBits, h0, h1] using
        byteFromFieldBits_eq_byteOfNat b1 ⟨t.val % 8, hr⟩
    · by_cases h2 : t.val < 24
      · simpa [byteFromFieldBits, h0, h1, h2] using
          byteFromFieldBits_eq_byteOfNat b2 ⟨t.val % 8, hr⟩
      · simpa [byteFromFieldBits, h0, h1, h2] using
          byteFromFieldBits_eq_byteOfNat b3 ⟨t.val % 8, hr⟩

set_option maxHeartbeats 2000000 in
private lemma bytes_recompose (x : Emu (F circomPrime))
    (hn : BigInt.Normalized limbBits x)
    (bytes : Vector (F circomPrime) coordBytes)
    (hbyte : ∀ t : Fin coordBytes,
      bytes[t] = ((ToBytes.byteOfNat (x[t.val / 8]'(by
        have ht := t.isLt
        simp only [coordBytes, numLimbs] at ht ⊢
        omega)).val (t.val % 8) : ℕ) : F circomPrime)) :
    Limbs.fromLimbs 8 (List.map ZMod.val bytes.toList) =
      BigInt.value limbBits x := by
  rw [fromLimbs_eq_sum, BigInt.value_eq_sum]
  simp only [Fin.getElem_fin, List.getElem_map, Vector.getElem_toList]
  let bf : ℕ → ℕ := fun i =>
    if hi : i < coordBytes then (bytes[i]'hi).val else 0
  have hinner (k : ℕ) (hk4 : k < 4) :
      (∑ t ∈ Finset.range 8, bf (8 * k + t) * 2 ^ (8 * t)) =
        (x[k]'hk4).val := by
    calc
      (∑ t ∈ Finset.range 8, bf (8 * k + t) * 2 ^ (8 * t)) =
          ∑ t ∈ Finset.range 8,
            ToBytes.byteOfNat (x[k]'hk4).val t * 2 ^ (8 * t) := by
        apply Finset.sum_congr rfl
        intro t ht
        have ht8 : t < 8 := Finset.mem_range.mp ht
        have hi : 8 * k + t < coordBytes := by simp only [coordBytes]; omega
        have hbval := congrArg ZMod.val (hbyte ⟨8 * k + t, hi⟩)
        simp only [Fin.getElem_fin] at hbval
        rw [show bf (8 * k + t) = (bytes[8 * k + t]'hi).val by simp [bf, hi],
          hbval, ZMod.val_natCast_of_lt]
        · unfold ToBytes.byteOfNat
          have hdiv : (8 * k + t) / 8 = k := by omega
          have hmod : (8 * k + t) % 8 = t := by omega
          simp only [hdiv, hmod]
        · unfold ToBytes.byteOfNat
          exact lt_trans (Nat.mod_lt _ (by norm_num : 0 < 256))
            (by decide : 256 < circomPrime)
      _ = (x[k]'hk4).val := by
        unfold ToBytes.byteOfNat
        have hlimb : (x[k]'hk4).val < 2 ^ 64 := by
          simpa only [limbBits] using hn ⟨k, hk4⟩
        have hlimbNum : (x[k]'hk4).val < 18446744073709551616 := by
          norm_num at hlimb ⊢
          exact hlimb
        have hsum := ToBytes.byteSum_eq_limb (x[k]'hk4).val 0
        norm_num at hsum
        rw [Nat.mod_eq_of_lt hlimbNum] at hsum
        exact hsum
  let envB : Environment (F circomPrime) :=
    { get := fun i => if hi : i < coordBytes then bytes[i]'hi else 0
      data := fun _ _ => #[] }
  have hbytes : ∀ i : Fin coordBytes, (envB.get i.val).val < 2 ^ 8 := by
    intro i
    rw [show envB.get i.val = bytes[i] by simp [envB]]
    rw [hbyte i, ZMod.val_natCast_of_lt]
    · unfold ToBytes.byteOfNat
      exact Nat.mod_lt _ (by norm_num)
    · unfold ToBytes.byteOfNat
      exact lt_trans (Nat.mod_lt _ (by norm_num : 0 < 256))
        (by decide : 256 < circomPrime)
  have hrows : ∀ k : Fin numLimbs,
      (∑ t : Fin bytesPerLimb,
          envB.get (bytesPerLimb * k.val + t.val) *
            ((2 ^ (8 * t.val) : ℕ) : F circomPrime)) =
        x[k.val]'k.isLt := by
    intro k
    have hnat := hinner k.val k.isLt
    have hcast := congrArg (fun z : ℕ => (z : F circomPrime)) hnat
    change ((∑ t ∈ Finset.range 8,
      bf (8 * k.val + t) * 2 ^ (8 * t) : ℕ) : F circomPrime) =
        ((x[k.val]'k.isLt).val : F circomPrime) at hcast
    rw [Nat.cast_sum] at hcast
    calc
      (∑ t : Fin bytesPerLimb,
          envB.get (bytesPerLimb * k.val + t.val) *
            ((2 ^ (8 * t.val) : ℕ) : F circomPrime)) =
          ∑ t ∈ Finset.range 8,
            ((bf (8 * k.val + t) * 2 ^ (8 * t) : ℕ) :
              F circomPrime) := by
        rw [show (∑ t : Fin bytesPerLimb,
            envB.get (bytesPerLimb * k.val + t.val) *
              ((2 ^ (8 * t.val) : ℕ) : F circomPrime)) =
            ∑ t ∈ Finset.range 8,
              envB.get (8 * k.val + t) *
                ((2 ^ (8 * t) : ℕ) : F circomPrime) by
          simpa only [bytesPerLimb] using
            Fin.sum_univ_eq_sum_range
              (fun t => envB.get (8 * k.val + t) *
                ((2 ^ (8 * t) : ℕ) : F circomPrime)) 8]
        apply Finset.sum_congr rfl
        intro t ht
        have ht8 : t < 8 := Finset.mem_range.mp ht
        have hk4 : k.val < 4 := by
          simpa only [numLimbs] using k.isLt
        have hi : 8 * k.val + t < coordBytes := by
          simp only [coordBytes]
          omega
        rw [show envB.get (8 * k.val + t) = bytes[8 * k.val + t]'hi by
          simp only [envB, hi, ↓reduceDIte]]
        rw [show bf (8 * k.val + t) = (bytes[8 * k.val + t]'hi).val by
          simp only [bf, hi, ↓reduceDIte]]
        rw [Nat.cast_mul, ZMod.natCast_zmod_val]
      _ = ((x[k.val]'k.isLt).val : F circomPrime) := hcast
      _ = x[k.val]'k.isLt := ZMod.natCast_zmod_val _
  have hcore := ToBytes.soundness_core envB 0 x
    (fun i => by simpa using hbytes i)
    (fun k => by simpa using hrows k)
  have hout :
      Vector.map (Expression.eval envB)
        (Vector.mapRange coordBytes fun i =>
          var (F := F circomPrime) { index := 0 + i }) = bytes := by
    apply Vector.ext
    intro i hi
    simp [envB, circuit_norm, hi]
  rw [hout] at hcore
  simpa only [fromLimbs_eq_sum, BigInt.value_eq_sum, Fin.getElem_fin,
    List.getElem_map, Vector.getElem_toList] using hcore

private lemma bytes_of_fieldToBits_spec (x : Emu (F circomPrime))
    (hn : BigInt.Normalized limbBits x) :
    ToBytes.Spec x (Vector.ofFn fun t => byteFromFieldBits
      (fieldToBits 64 x[0]) (fieldToBits 64 x[1])
      (fieldToBits 64 x[2]) (fieldToBits 64 x[3]) t) := by
  let bytes : Vector (F circomPrime) coordBytes := Vector.ofFn fun t =>
    byteFromFieldBits (fieldToBits 64 x[0]) (fieldToBits 64 x[1])
      (fieldToBits 64 x[2]) (fieldToBits 64 x[3]) t
  have hbyte : ∀ t : Fin coordBytes,
      bytes[t] = ((ToBytes.byteOfNat (x[t.val / 8]'(by
        have ht := t.isLt
        simp only [coordBytes, numLimbs] at ht ⊢
        omega)).val (t.val % 8) : ℕ) : F circomPrime) := by
    intro t
    rw [show bytes[t] = byteFromFieldBits
      (fieldToBits 64 x[0]) (fieldToBits 64 x[1])
      (fieldToBits 64 x[2]) (fieldToBits 64 x[3]) t by simp [bytes]]
    rw [byteFromFieldBits_selected]
    congr 2
    split_ifs with h0 h1 h2
    · have hd : t.val / 8 = 0 := Nat.div_eq_of_lt h0
      simpa [hd]
    · have hd : t.val / 8 = 1 := by omega
      simpa [hd]
    · have hd : t.val / 8 = 2 := by omega
      simpa [hd]
    · have ht := t.isLt
      simp only [coordBytes] at ht
      have hd : t.val / 8 = 3 := by omega
      simpa [hd]
  refine ⟨?_, ?_⟩
  · intro t
    change (bytes[t]).val < 256
    rw [hbyte t, ZMod.val_natCast_of_lt (by
      unfold ToBytes.byteOfNat
      exact lt_trans (Nat.mod_lt _ (by norm_num : 0 < 256)) (by decide : 256 < circomPrime))]
    unfold ToBytes.byteOfNat
    exact Nat.mod_lt _ (by norm_num)
  · exact bytes_recompose x hn bytes hbyte

set_option maxHeartbeats 4000000 in
theorem soundness :
    GeneralFormalCircuit.Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [ValidP.tail, ToBitsAffine.toBitsAffine, ToBitsAffine.main]
  obtain ⟨⟨hn0, hb0⟩, ⟨hn1, hb1⟩, ⟨hn2, hb2⟩, ⟨hn3, hb3⟩, h1, h2, h3, h4⟩ := h_holds
  have hx : ∀ (i : ℕ) (hi : i < 4), Expression.eval env input_var[i] = input[i] := by
    intro i hi
    rw [← h_input, Vector.getElem_map]
  rw [hx 0 (by omega)] at hn0 hb0
  rw [hx 1 (by omega)] at hn1 hb1
  rw [hx 2 (by omega)] at hn2 hb2
  rw [hx 3 (by omega)] at hn3 hb3
  have hn : BigInt.Normalized limbBits input := by
    intro i
    fin_cases i <;> assumption
  simp only [eval_ds (start := 33) (len := 31) (by decide) env _ input[0] hb0,
    eval_ds (start := 0) (len := 64) (by decide) env _ input[1] hb1,
    eval_ds (start := 0) (len := 64) (by decide) env _ input[2] hb2,
    eval_ds (start := 0) (len := 64) (by decide) env _ input[3] hb3,
    eval_ds (start := 10) (len := 22) (by decide) env _ input[0] hb0,
    eval_ds (start := 0) (len := 4) (by decide) env _ input[0] hb0,
    Nat.reduceLT, dite_true, Expression.eval] at h1 h2 h3 h4
  have hb0val : ∀ (i : ℕ) (hi : i < 63),
      env.get (i₀ + i) = if input[0].val.testBit i then 1 else 0 :=
    fun i hi => push_eval_bit env i₀ _ input[0] hb0 i hi
  have H1 : bitField (input[0].val.testBit 32)
      - ((topDC input : ℕ) : F circomPrime) * env.get (i₀ + 63 + 63 + 63 + 63) = 0 := by
    rw [bitField, ← hb0val 32 (by omega)]
    simp only [topDC]
    push_cast
    linear_combination h1
  have H2 : (bitField (input[0].val.testBit 9) + bitField (input[0].val.testBit 8)
        + bitField (input[0].val.testBit 7) + bitField (input[0].val.testBit 6))
      - (((topDC input : ℕ) : F circomPrime) + ((midDC input : ℕ) : F circomPrime))
        * env.get (i₀ + 63 + 63 + 63 + 63 + 1) = 0 := by
    rw [bitField, ← hb0val 9 (by omega), bitField, ← hb0val 8 (by omega),
      bitField, ← hb0val 7 (by omega), bitField, ← hb0val 6 (by omega)]
    simp only [topDC, midDC]
    push_cast
    linear_combination h2
  have H3 : bitField (input[0].val.testBit 4)
      - (((topDC input : ℕ) : F circomPrime) + ((midDC input : ℕ) : F circomPrime)
          + (1 - bitField (input[0].val.testBit 5)))
        * env.get (i₀ + 63 + 63 + 63 + 63 + 1 + 1) = 0 := by
    rw [bitField, ← hb0val 4 (by omega), bitField, ← hb0val 5 (by omega)]
    simp only [topDC, midDC]
    push_cast
    linear_combination h3
  have H4 : (((topDC input : ℕ) : F circomPrime) + ((midDC input : ℕ) : F circomPrime)
        + (1 - bitField (input[0].val.testBit 5)) + ((lowDC input : ℕ) : F circomPrime))
      * env.get (i₀ + 63 + 63 + 63 + 63 + 1 + 1 + 1) - 1 = 0 := by
    rw [bitField, ← hb0val 5 (by omega)]
    simp only [topDC, midDC, lowDC]
    push_cast
    linear_combination h4
  refine ⟨⟨hn, (pattern_iff_lt input hn).mp (pattern_of_weak input H1 H2 H3 H4)⟩, ?_⟩
  have hb0' :
      Vector.map (Expression.eval env)
          (ToBitsAffine.main 63 input_var[0] i₀).1 =
        fieldToBits 64 input[0] := by
    simpa only [ToBitsAffine.main, circuit_norm] using hb0
  have hb1' :
      Vector.map (Expression.eval env)
          (ToBitsAffine.main 63 input_var[1] (i₀ + 63)).1 =
        fieldToBits 64 input[1] := by
    simpa only [ToBitsAffine.main, circuit_norm] using hb1
  have hb2' :
      Vector.map (Expression.eval env)
          (ToBitsAffine.main 63 input_var[2] (i₀ + 63 + 63)).1 =
        fieldToBits 64 input[2] := by
    simpa only [ToBitsAffine.main, circuit_norm] using hb2
  have hb3' :
      Vector.map (Expression.eval env)
          (ToBitsAffine.main 63 input_var[3] (i₀ + 63 + 63 + 63)).1 =
        fieldToBits 64 input[3] := by
    simpa only [ToBitsAffine.main, circuit_norm] using hb3
  have hout :
      Vector.map (Expression.eval env)
        (Vector.ofFn fun t => byteFromBits
          (ToBitsAffine.main 63 input_var[0] i₀).1
          (ToBitsAffine.main 63 input_var[1] (i₀ + 63)).1
          (ToBitsAffine.main 63 input_var[2] (i₀ + 63 + 63)).1
          (ToBitsAffine.main 63 input_var[3] (i₀ + 63 + 63 + 63)).1 t) =
        Vector.ofFn fun t => byteFromFieldBits
          (fieldToBits 64 input[0]) (fieldToBits 64 input[1])
          (fieldToBits 64 input[2]) (fieldToBits 64 input[3]) t := by
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_map, Vector.getElem_ofFn]
    rw [eval_byteFromBits, hb0', hb1', hb2', hb3']
  change ToBytes.Spec input
    (Vector.map (Expression.eval env)
      (Vector.ofFn fun t => byteFromBits
        (ToBitsAffine.main 63 input_var[0] i₀).1
        (ToBitsAffine.main 63 input_var[1] (i₀ + 63)).1
        (ToBitsAffine.main 63 input_var[2] (i₀ + 63 + 63)).1
        (ToBitsAffine.main 63 input_var[3] (i₀ + 63 + 63 + 63)).1 t))
  rw [hout]
  exact bytes_of_fieldToBits_spec input hn

set_option maxHeartbeats 0 in
theorem completeness :
    GeneralFormalCircuit.Completeness (F circomPrime) main
      ProverAssumptions ProverSpec := by
  circuit_proof_start [ValidP.tail, ToBitsAffine.toBitsAffine, ToBitsAffine.main]
  obtain ⟨hb0gen, hb1gen, hb2gen, hb3gen, hv1, hv2, hv3, hv4⟩ := h_env
  have hx : ∀ (i : ℕ) (hi : i < 4),
      Expression.eval env.toEnvironment input_var[i] = input[i] := by
    intro i hi
    rw [← h_input, Vector.getElem_map]
  have hn := h_assumptions.1
  have hn0 : (Expression.eval env.toEnvironment input_var[0]).val < 2 ^ limbBits := by
    rw [hx 0 (by omega)]; exact hn 0
  have hn1 : (Expression.eval env.toEnvironment input_var[1]).val < 2 ^ limbBits := by
    rw [hx 1 (by omega)]; exact hn 1
  have hn2 : (Expression.eval env.toEnvironment input_var[2]).val < 2 ^ limbBits := by
    rw [hx 2 (by omega)]; exact hn 2
  have hn3 : (Expression.eval env.toEnvironment input_var[3]).val < 2 ^ limbBits := by
    rw [hx 3 (by omega)]; exact hn 3
  obtain ⟨-, hb0⟩ := hb0gen hn0
  obtain ⟨-, hb1⟩ := hb1gen hn1
  obtain ⟨-, hb2⟩ := hb2gen hn2
  obtain ⟨-, hb3⟩ := hb3gen hn3
  rw [hx 0 (by omega)] at hb0
  rw [hx 1 (by omega)] at hb1
  rw [hx 2 (by omega)] at hb2
  rw [hx 3 (by omega)] at hb3
  simp only [eval_ds (start := 33) (len := 31) (by decide) env.toEnvironment _ input[0] hb0,
    eval_ds (start := 0) (len := 64) (by decide) env.toEnvironment _ input[1] hb1,
    eval_ds (start := 0) (len := 64) (by decide) env.toEnvironment _ input[2] hb2,
    eval_ds (start := 0) (len := 64) (by decide) env.toEnvironment _ input[3] hb3,
    eval_ds (start := 10) (len := 22) (by decide) env.toEnvironment _ input[0] hb0,
    eval_ds (start := 0) (len := 4) (by decide) env.toEnvironment _ input[0] hb0,
    Nat.reduceLT, dite_true, Expression.eval] at hv1 hv2 hv3 hv4 ⊢
  have hb0val : ∀ (i : ℕ) (hi : i < 63),
      env.get (i₀ + i) = if input[0].val.testBit i then 1 else 0 :=
    fun i hi => push_eval_bit env.toEnvironment i₀ _ input[0] hb0 i hi
  have hdt : ((dc input[0].val 33 31 : ℕ) : F circomPrime)
      + ((dc input[1].val 0 64 : ℕ) : F circomPrime)
      + ((dc input[2].val 0 64 : ℕ) : F circomPrime)
      + ((dc input[3].val 0 64 : ℕ) : F circomPrime)
      = ((topDC input : ℕ) : F circomPrime) := by
    simp only [topDC]; push_cast; ring
  have hdm : ((dc input[0].val 10 22 : ℕ) : F circomPrime)
      = ((midDC input : ℕ) : F circomPrime) := rfl
  have hdl : ((dc input[0].val 0 4 : ℕ) : F circomPrime)
      = ((lowDC input : ℕ) : F circomPrime) := rfl
  obtain ⟨w1, w2, w3, w4⟩ :=
    weak_of_pattern input ((pattern_iff_lt input hn).mpr h_assumptions.2)
  simp only [Nat.cast_one, bitField, sub_eq_add_neg] at w3 w4
  refine ⟨hn0, hn1, hn2, hn3, ?_, ?_, ?_, ?_⟩
  · rw [hv1, hdt, hb0val 32 (by omega)]
    linear_combination inv_row_of_imp
      (d := ((topDC input : ℕ) : F circomPrime))
      (num := (if input[0].val.testBit 32 then (1 : F circomPrime) else 0))
      (fun h => w1 h)
  · rw [hv2, hdt, hdm, hb0val 9 (by omega), hb0val 8 (by omega),
      hb0val 7 (by omega), hb0val 6 (by omega)]
    linear_combination inv_row_of_imp
      (d := ((topDC input : ℕ) : F circomPrime) + ((midDC input : ℕ) : F circomPrime))
      (num := (if input[0].val.testBit 9 then (1 : F circomPrime) else 0)
        + (if input[0].val.testBit 8 then (1 : F circomPrime) else 0)
        + (if input[0].val.testBit 7 then (1 : F circomPrime) else 0)
        + (if input[0].val.testBit 6 then (1 : F circomPrime) else 0))
      (fun h => w2 h)
  · rw [hv3, hdt, hdm, hb0val 4 (by omega), hb0val 5 (by omega)]
    linear_combination inv_row_of_imp
      (d := ((topDC input : ℕ) : F circomPrime) + ((midDC input : ℕ) : F circomPrime)
        + ((1 : F circomPrime) + -(if input[0].val.testBit 5 then (1 : F circomPrime) else 0)))
      (num := (if input[0].val.testBit 4 then (1 : F circomPrime) else 0))
      (fun h => w3 h)
  · rw [hv4, hdt, hdm, hdl, hb0val 5 (by omega)]
    linear_combination inv_row_of_ne
      (d := ((topDC input : ℕ) : F circomPrime) + ((midDC input : ℕ) : F circomPrime)
        + ((1 : F circomPrime) + -(if input[0].val.testBit 5 then (1 : F circomPrime) else 0))
        + ((lowDC input : ℕ) : F circomPrime))
      w4

def circuit : GeneralFormalCircuit (F circomPrime) Emu (fields coordBytes) where
  main := main
  elaborated := elaborated
  Assumptions := Assumptions
  Spec := Spec
  ProverAssumptions := ProverAssumptions
  ProverSpec := ProverSpec
  soundness := soundness
  completeness := completeness

theorem computableWitnesses : circuit.base.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition
      input env env')
    ((main input).operations offset)
  simpa only [main, ValidP.main, Circuit.operations] using
    ValidP.computableWitnesses offset input env env'

theorem computableWitness : ∀ n input,
    ProverEnvironment.OnlyAccessedBelow n
      (fun env : ProverEnvironment (F circomPrime) => eval env input) →
    Circuit.ComputableWitnesses (main input) n :=
  Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnesses_implies
    (circuit := circuit.base) computableWitnesses

end ValidPBytes
end Solution.Secp256k1ScalarMulFixedBase

end DonorFile1_18

-- Adapted donor module: Canonicalize
section DonorFile1_19

/-! ### merged from NormalizeR.lean (submission file-count cap) -/
section

namespace Solution.Secp256k1ScalarMulFixedBase
open Solution.Secp256k1ScalarMulFixedBase.Limbs

section
variable {p : ℕ} [Fact p.Prime]
variable {m : ℕ}

/-! `Normalize` over the `n−1`-bit `RangeCheck` gadget (one row and one
allocation fewer per limb). Kept separate from `Normalize` so the widely
consumed original keeps its offsets. -/
namespace NormalizeR

def main (P : BigIntParams p m) (hB1 : 1 ≤ P.B) [Fact (p > 2)]
    (x : Var (BigInt m) (F p)) :
    Circuit (F p) Unit :=
  Circuit.forEach x (fun xi => RangeCheck.circuit P.B P.hB hB1 xi)

instance elaborated (P : BigIntParams p m) (hB1 : 1 ≤ P.B) [Fact (p > 2)] :
    ElaboratedCircuit (F p) (BigInt m) unit (main P hB1) where
  localLength _ := m * (P.B - 1)
  localLength_eq := by
    intro input offset
    simp only [main, circuit_norm, RangeCheck.circuit, RangeCheck.main]
  subcircuitsConsistent := by
    intro input offset
    simp +arith only [main, circuit_norm, RangeCheck.circuit, RangeCheck.main]
  channelsLawful := by
    simp only [main, circuit_norm, RangeCheck.circuit, RangeCheck.main]

def Assumptions (_ : BigInt m (F p)) : Prop := True

def Spec (B : ℕ) (x : BigInt m (F p)) : Prop := BigInt.Normalized B x

def circuit (P : BigIntParams p m) (hB1 : 1 ≤ P.B) [Fact (p > 2)] :
    FormalAssertion (F p) (BigInt m) where
  main := main P hB1
  Assumptions := Assumptions
  Spec := Spec P.B
  soundness := by
    circuit_proof_start
    simp_all only [circuit_norm, RangeCheck.circuit, RangeCheck.Spec,
      RangeCheck.Assumptions, BigInt.Normalized]
    intro i
    rw [← h_input, Vector.getElem_map]
    exact h_holds i
  completeness := by
    circuit_proof_start
    simp_all only [circuit_norm, RangeCheck.circuit, RangeCheck.Spec,
      RangeCheck.Assumptions, BigInt.Normalized]
    intro i
    have := h_spec i
    rwa [← h_input, Vector.getElem_map] at this

theorem computableWitnesses (P : BigIntParams p m) (hB1 : 1 ≤ P.B) [Fact (p > 2)] :
    (circuit P hB1).ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition input env env')
    ((main P hB1 input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.forEach_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_structuralComputableWitnesses_iff]
  intro i
  apply Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_flatStructuralComputableWitnesses
  · intro env₁ env₂ h_input
    have h : (eval env₁ input)[i.val] = (eval env₂ input)[i.val] := by
      simpa only [Fin.getElem_fin] using congrArg (fun x : BigInt m (F p) => x[i]) h_input
    rw [← ProvableType.getElem_eval_fields_prover (env := env₁) input i.val i.isLt,
      ← ProvableType.getElem_eval_fields_prover (env := env₂) input i.val i.isLt] at h
    simpa [CircuitType.eval_expression_prover_to_verifier (M := field),
      CircuitType.eval_expression (M := field), ProvableType.eval, explicit_provable_type] using h
  · exact RangeCheck.computableWitnesses P.B P.hB hB1

theorem computableWitness (P : BigIntParams p m) (hB1 : 1 ≤ P.B) [Fact (p > 2)] : ∀ n input,
    ProverEnvironment.OnlyAccessedBelow n
      (fun env : ProverEnvironment (F p) => eval env input) →
    Circuit.ComputableWitnesses (main P hB1 input) n := by
  exact Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnesses_implies
    (computableWitnesses P hB1)

end NormalizeR

end

end Solution.Secp256k1ScalarMulFixedBase

end

/-! ### merged from LessThanR.lean (submission file-count cap) -/
section

namespace Solution.Secp256k1ScalarMulFixedBase
open Solution.Secp256k1ScalarMulFixedBase.Limbs

section
variable {p : ℕ} [Fact p.Prime]
variable {m : ℕ} [NeZero m]

namespace LessThanR

structure Inputs (m : ℕ) (F : Type) where
  lhs : BigInt m F
  rhs : BigInt m F
deriving ProvableStruct

private def evalValue (B : ℕ) (env : ProverEnvironment (F p))
    (x : Var (BigInt m) (F p)) : ℕ :=
  Solution.Secp256k1ScalarMulFixedBase.Limbs.fromLimbs B ((x.map (Expression.eval env.toEnvironment)).toList.map ZMod.val)

def main (P : BigIntParams p m) [Fact (p > 2)] (input : Var (Inputs m) (F p)) :
    Circuit (F p) Unit := do
  let a := input.lhs
  let b := input.rhs

  let d ← ProvableType.witness (α := BigInt m) fun env =>
    let dval : ℕ := evalValue P.B env b - 1 - evalValue P.B env a
    Vector.ofFn fun k : Fin m => ((dval / 2 ^ (P.B * k.val) % 2 ^ P.B : ℕ) : F p)

  NormalizeR.circuit P P.hB1 d

  let carry ← witnessVector (m - 1) fun env =>
    let av : ℕ → ℕ := fun j => if h : j < m then (Expression.eval env.toEnvironment a[j]).val else 0
    let dv : ℕ → ℕ := fun j => if h : j < m then (Expression.eval env.toEnvironment d[j]).val else 0
    Vector.ofFn fun k : Fin (m - 1) =>
      (((1 + ∑ j ∈ Finset.range (k.val + 1), (av j + dv j) * 2 ^ (P.B * j))
          / 2 ^ (P.B * (k.val + 1)) : ℕ) : F p)

  Circuit.forEach carry (fun c => assertZero (c * (c - 1)))

  let constraints : Vector (Expression (F p)) m := Vector.mapFinRange m fun k =>
    let carryIn : Expression (F p) :=
      if h : k.val = 0 then 0 else carry[k.val - 1]'(by omega)
    let one : Expression (F p) := if k.val = 0 then 1 else 0
    let carryOut : Expression (F p) :=
      if h : k.val < m - 1 then carry[k.val]'h else 0
    a[k.val] + d[k.val] + carryIn + one - b[k.val] - carryOut * (2 ^ P.B : F p)
  Circuit.forEach constraints assertZero

instance elaborated (P : BigIntParams p m) [Fact (p > 2)] :
    ElaboratedCircuit (F p) (Inputs m) unit (main P) where

  localLength _ := m + m * (P.B - 1) + (m - 1)
  localLength_eq := by
    intro input offset
    simp only [main, circuit_norm, NormalizeR.circuit, NormalizeR.elaborated, NormalizeR.main,
      Gadgets.ToBits.rangeCheck]
    simp +arith [circuit_norm]
  subcircuitsConsistent := by
    intro input offset
    simp +arith only [main, circuit_norm, NormalizeR.circuit, NormalizeR.elaborated, NormalizeR.main,
      Gadgets.ToBits.rangeCheck]
  channelsLawful := by
    intro offset
    simp only [main, circuit_norm, NormalizeR.circuit, NormalizeR.elaborated, NormalizeR.main,
      Gadgets.ToBits.rangeCheck]

def Assumptions (B : ℕ) (input : Inputs m (F p)) : Prop :=
  input.lhs.Normalized B ∧ input.rhs.Normalized B

def Spec (B : ℕ) (input : Inputs m (F p)) : Prop :=
  input.lhs.value B < input.rhs.value B

def circuit (P : BigIntParams p m) [Fact (p > 2)] :
    FormalAssertion (F p) (Inputs m) where
    main := main P
    Assumptions := Assumptions P.B
    Spec := Spec P.B
    soundness := by
      obtain ⟨B, W, hB, hW, hB1, hWB, hWp, hp⟩ := P
      circuit_proof_start
      simp only [circuit_norm, NormalizeR.circuit, NormalizeR.elaborated, NormalizeR.main,
        Gadgets.ToBits.rangeCheck] at h_holds ⊢
      obtain ⟨h_dnorm, h_cbool, h_lin⟩ := h_holds
      obtain ⟨ha_norm, hb_norm⟩ := h_assumptions
      rcases Nat.eq_zero_or_pos m with hm | hm
      ·

        exact absurd hm (NeZero.ne m)

      set An : ℕ → ℕ := fun k => if h : k < m then (input.lhs[k]'h).val else 0 with hAn
      set Dn : ℕ → ℕ := fun k => (env.get (i₀ + k)).val with hDn
      set Bn : ℕ → ℕ := fun k => if h : k < m then (input.rhs[k]'h).val else 0 with hBn
      set Cn : ℕ → ℕ := fun k =>
        if k < m - 1 then (env.get (i₀ + m + m * (B - 1) + k)).val else 0 with hCn

      have hAn_lt : ∀ k, k < m → An k < 2 ^ B := by
        intro k hk; simp only [hAn, dif_pos hk]; exact ha_norm ⟨k, hk⟩
      have hBn_lt : ∀ k, k < m → Bn k < 2 ^ B := by
        intro k hk; simp only [hBn, dif_pos hk]; exact hb_norm ⟨k, hk⟩
      have hDn_lt : ∀ k, k < m → Dn k < 2 ^ B := by
        intro k hk
        have hspec := h_dnorm trivial ⟨k, hk⟩
        have heq : (Vector.map (Expression.eval env)
            (Vector.mapRange m fun i => var { index := i₀ + i }))[(⟨k, hk⟩ : Fin m)]
            = env.get (i₀ + k) := by simp [circuit_norm]
        rw [heq] at hspec
        simpa [hDn] using hspec

      have hCn_le : ∀ k, k < m → Cn k ≤ 1 := by
        intro k hk
        simp only [hCn]
        split
        · rename_i hk1
          have hb := h_cbool ⟨k, hk1⟩
          have : IsBool (env.get (i₀ + m + m * (B - 1) + k)) := by
            rw [IsBool.iff_mul_sub_one]; rw [show env.get (i₀ + m + m * (B - 1) + k) - 1
              = env.get (i₀ + m + m * (B - 1) + k) + -1 by ring]; exact hb
          have := IsBool.val_lt_two this
          omega
        · omega

      have hPB1 : 2 ^ (B + 1) < p := by
        have h1 : 2 ^ (B + 1) ≤ 2 ^ (2 * B + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
        have h2 : 2 ^ (2 * B + 2) = 2 ^ (2 * B) * 4 := by rw [pow_add]; ring
        have h3 : 2 ^ (2 * B) * 4 ≤ 2 ^ (2 * B) * (m + 1) * 4 := by
          have : 1 ≤ m + 1 := by omega
          nlinarith [Nat.two_pow_pos (2 * B)]
        omega

      have h_limb : ∀ k : ℕ, (hk : k < m) →
          An k + Dn k + (if k = 0 then 0 else Cn (k - 1)) + (if k = 0 then 1 else 0)
            = Bn k + Cn k * 2 ^ B := by
        intro k hk
        have hlin := h_lin ⟨k, hk⟩

        have ha_e : Expression.eval env input_var.lhs[(⟨k, hk⟩ : Fin m).val] = input.lhs[k]'hk := by
          rw [← h_input]; simp [Vector.getElem_map]
        have hb_e : Expression.eval env input_var.rhs[(⟨k, hk⟩ : Fin m).val] = input.rhs[k]'hk := by
          rw [← h_input]; simp [Vector.getElem_map]
        have hcin_e : Expression.eval env
            (if h : (⟨k, hk⟩ : Fin m).val = 0 then 0
              else var { index := i₀ + m + m * (B - 1) + ((⟨k, hk⟩ : Fin m).val - 1) })
            = if k = 0 then 0 else env.get (i₀ + m + m * (B - 1) + (k - 1)) := by
          simp only []
          split <;> simp [circuit_norm]
        have hone_e : Expression.eval env (if (⟨k, hk⟩ : Fin m).val = 0 then 1 else 0)
            = if k = 0 then (1 : F p) else 0 := by
          simp only []; split <;> simp [circuit_norm]
        have hcout_e : Expression.eval env
            (if h : (⟨k, hk⟩ : Fin m).val < m - 1
              then var { index := i₀ + m + m * (B - 1) + (⟨k, hk⟩ : Fin m).val } else 0)
            = if k < m - 1 then env.get (i₀ + m + m * (B - 1) + k) else 0 := by
          simp only []
          split <;> simp [circuit_norm]
        simp only [ha_e, hb_e, hcin_e, hone_e, hcout_e] at hlin

        have h3 : (if k = 0 then (0:F p) else env.get (i₀ + m + m * (B - 1) + (k - 1))).val ≤ 1 := by
          split
          · simp [ZMod.val_zero]
          · rename_i h
            have hkm : k - 1 < m := by omega
            have := hCn_le (k - 1) hkm
            simp only [hCn] at this
            rw [if_pos (by omega)] at this
            exact this
        have h4 : (if k = 0 then (1 : F p) else 0).val ≤ 1 := by
          split
          · simp [ZMod.val_one]
          · simp [ZMod.val_zero]
        have hpw : 2 ^ B + 2 ^ B = 2 ^ (B + 1) := by rw [pow_succ]; ring
        have hsum_lt : (input.lhs[k]'hk).val + (env.get (i₀ + k)).val
            + (if k = 0 then (0:F p) else env.get (i₀ + m + m * (B - 1) + (k - 1))).val
            + (if k = 0 then (1 : F p) else 0).val < p := by
          have h1 := hAn_lt k hk; have h2 := hDn_lt k hk
          simp only [hAn, hDn, dif_pos hk] at h1 h2
          omega
        have hcout_le : (if k < m - 1 then env.get (i₀ + m + m * (B - 1) + k) else (0:F p)).val ≤ 1 := by
          split
          · rename_i h1
            have := hCn_le k hk
            simp only [hCn, if_pos h1] at this
            exact this
          · simp
        have hrhs_lt : (input.rhs[k]'hk).val
            + (if k < m - 1 then env.get (i₀ + m + m * (B - 1) + k) else (0:F p)).val * 2 ^ B < p := by
          have h1 := hBn_lt k hk
          simp only [hBn, dif_pos hk] at h1
          nlinarith [Nat.two_pow_pos B, hcout_le]
        have hlin' : (input.lhs[k]'hk) + env.get (i₀ + k)
            + (if k = 0 then (0:F p) else env.get (i₀ + m + m * (B - 1) + (k - 1)))
            + (if k = 0 then (1 : F p) else 0) - (input.rhs[k]'hk)
            - (if k < m - 1 then env.get (i₀ + m + m * (B - 1) + k) else (0:F p)) * (2 ^ B : F p) = 0 := by
          rw [sub_eq_add_neg, sub_eq_add_neg]; exact hlin
        have hlift := per_limb_lift (B := B) (input.lhs[k]'hk) (env.get (i₀ + k))
          (if k = 0 then (0:F p) else env.get (i₀ + m + m * (B - 1) + (k - 1)))
          (if k = 0 then (1 : F p) else 0) (input.rhs[k]'hk)
          (if k < m - 1 then env.get (i₀ + m + m * (B - 1) + k) else (0:F p)) hB hsum_lt hrhs_lt hlin'

        have hcin_val : (if k = 0 then (0:F p) else env.get (i₀ + m + m * (B - 1) + (k - 1))).val
            = if k = 0 then 0 else Cn (k - 1) := by
          split
          · simp
          · rename_i hk0
            simp only [hCn]
            rw [if_pos (by omega)]
        have hone_val : (if k = 0 then (1 : F p) else 0).val = if k = 0 then 1 else 0 := by
          split
          · simp [ZMod.val_one]
          · simp [ZMod.val_zero]
        have hcout_val : (if k < m - 1 then env.get (i₀ + m + m * (B - 1) + k) else (0:F p)).val
            = Cn k := by
          simp only [hCn]
          split <;> simp
        rw [hcin_val, hone_val, hcout_val] at hlift
        simp only [hAn, hDn, hBn, dif_pos hk]
        omega

      have htop0 : Cn (m - 1) = 0 := by
        simp only [hCn]
        rw [if_neg (lt_irrefl _)]

      have hval_a : BigInt.value B input.lhs = ∑ k ∈ Finset.range m, An k * 2 ^ (B * k) := by
        rw [BigInt.value_eq_sum, ← Fin.sum_univ_eq_sum_range (fun k => An k * 2 ^ (B * k))]
        apply Finset.sum_congr rfl
        intro i _
        simp only [hAn, dif_pos i.isLt, Fin.getElem_fin]
      have hval_b : BigInt.value B input.rhs = ∑ k ∈ Finset.range m, Bn k * 2 ^ (B * k) := by
        rw [BigInt.value_eq_sum, ← Fin.sum_univ_eq_sum_range (fun k => Bn k * 2 ^ (B * k))]
        apply Finset.sum_congr rfl
        intro i _
        simp only [hBn, dif_pos i.isLt, Fin.getElem_fin]

      have hsum_eq : (∑ k ∈ Finset.range m,
            ((An k + Dn k + (if k = 0 then 0 else Cn (k - 1)) + (if k = 0 then 1 else 0)) * 2 ^ (B * k)))
          = ∑ k ∈ Finset.range m, ((Bn k + Cn k * 2 ^ B) * 2 ^ (B * k)) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.mem_range] at hk
        rw [h_limb k hk]

      have hLHS : (∑ k ∈ Finset.range m,
            (An k + Dn k + (if k = 0 then 0 else Cn (k - 1)) + (if k = 0 then 1 else 0)) * 2 ^ (B * k))
          = (∑ k ∈ Finset.range m, An k * 2 ^ (B * k))
            + (∑ k ∈ Finset.range m, Dn k * 2 ^ (B * k))
            + (∑ k ∈ Finset.range m, (if k = 0 then 0 else Cn (k - 1)) * 2 ^ (B * k))
            + (∑ k ∈ Finset.range m, (if k = 0 then 1 else 0) * 2 ^ (B * k)) := by
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _; ring
      have hRHS : (∑ k ∈ Finset.range m, (Bn k + Cn k * 2 ^ B) * 2 ^ (B * k))
          = (∑ k ∈ Finset.range m, Bn k * 2 ^ (B * k))
            + (∑ k ∈ Finset.range m, Cn k * 2 ^ (B * (k + 1))) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _
        rw [Nat.mul_add, Nat.mul_one, pow_add]; ring

      have hone_sum : (∑ k ∈ Finset.range m, (if k = 0 then 1 else 0) * 2 ^ (B * k)) = 1 := by
        rw [Finset.sum_eq_single 0]
        · simp
        · intro k _ hk0; simp [hk0]
        · intro h; exact absurd (Finset.mem_range.mpr hm) h

      have htel := carry_telescope B Cn m
      rw [if_neg (by omega : ¬ (m = 0)), htop0, Nat.zero_mul, Nat.add_zero] at htel

      rw [hLHS, hRHS, hone_sum, htel] at hsum_eq

      rw [hval_a, hval_b]

      have hd_nonneg : 0 ≤ ∑ k ∈ Finset.range m, Dn k * 2 ^ (B * k) := Nat.zero_le _
      omega
    completeness := by
      obtain ⟨B, W, hB, hW, hB1, hWB, hWp, hp⟩ := P
      circuit_proof_start
      simp only [circuit_norm, NormalizeR.circuit, NormalizeR.elaborated, NormalizeR.main,
        Gadgets.ToBits.rangeCheck] at h_env ⊢
      obtain ⟨h_dwit, h_cwit, -⟩ := h_env
      obtain ⟨ha_norm, hb_norm⟩ := h_assumptions

      set An : ℕ → ℕ := fun k => if h : k < m then (input.lhs[k]'h).val else 0 with hAn
      set Bn : ℕ → ℕ := fun k => if h : k < m then (input.rhs[k]'h).val else 0 with hBn

      have hd_val : ∀ i : Fin m, (env.get (i₀ + i.val)).val
          = (evalValue B env input_var.rhs - 1 - evalValue B env input_var.lhs)
              / 2 ^ (B * i.val) % 2 ^ B := by
        intro i
        rw [h_dwit i]
        simp only [Vector.getElem_ofFn]
        rw [ZMod.val_natCast_of_lt]
        exact lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos B)) (le_of_lt hB)

      have heva : evalValue B env input_var.lhs = BigInt.value B input.lhs := by
        rw [evalValue, BigInt.value, ← h_input]
      have hevb : evalValue B env input_var.rhs = BigInt.value B input.rhs := by
        rw [evalValue, BigInt.value, ← h_input]

      set va := BigInt.value B input.lhs with hva
      set vb := BigInt.value B input.rhs with hvb

      set dtot : ℕ := vb - 1 - va with hdtot

      have hva_lt : va < 2 ^ (B * m) := BigInt.value_lt ha_norm
      have hvb_lt : vb < 2 ^ (B * m) := BigInt.value_lt hb_norm

      have hd_val' : ∀ i : Fin m, (env.get (i₀ + i.val)).val = dtot / 2 ^ (B * i.val) % 2 ^ B := by
        intro i; rw [hd_val i, heva, hevb]

      set Dn : ℕ → ℕ := fun k => if h : k < m then (env.get (i₀ + k)).val else 0 with hDn
      have hDn_eq : ∀ k, k < m → Dn k = dtot / 2 ^ (B * k) % 2 ^ B := by
        intro k hk; simp only [hDn, dif_pos hk]; exact hd_val' ⟨k, hk⟩
      have hDn_lt : ∀ k, k < m → Dn k < 2 ^ B := by
        intro k hk; rw [hDn_eq k hk]; exact lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos B)) (le_refl _)
      have hAn_lt : ∀ k, k < m → An k < 2 ^ B := fun k hk => by
        simp only [hAn, dif_pos hk]; exact ha_norm ⟨k, hk⟩
      have hBn_lt : ∀ k, k < m → Bn k < 2 ^ B := fun k hk => by
        simp only [hBn, dif_pos hk]; exact hb_norm ⟨k, hk⟩

      set gfun : ℕ → ℕ := fun k => An k + Dn k with hgfun
      have hgfun_le : ∀ j, gfun j ≤ 2 * (2 ^ B - 1) := by
        intro j
        rcases Nat.lt_or_ge j m with hj | hj
        · have := hAn_lt j hj; have := hDn_lt j hj; simp only [hgfun]; omega
        · simp only [hgfun, hAn, hDn, dif_neg (by omega : ¬ j < m)]; omega
      set P : ℕ → ℕ := fun k => 1 + ∑ j ∈ Finset.range (k + 1), gfun j * 2 ^ (B * j) with hP

      have hdtot_lt : dtot < 2 ^ (B * m) := by rw [hdtot]; omega
      have hadd : va + dtot + 1 = vb := by rw [hdtot]; omega

      have hvd : BigInt.value B (Vector.map (Expression.eval env.toEnvironment)
          (Vector.mapRange m fun i => var { index := i₀ + i })) = dtot := by
        rw [BigInt.value_eq_sum]
        have hstep : (∑ k : Fin m, ((Vector.map (Expression.eval env.toEnvironment)
            (Vector.mapRange m fun i => var { index := i₀ + i }))[k]).val * 2 ^ (B * k.val))
            = ∑ k ∈ Finset.range m, (dtot / 2 ^ (B * k) % 2 ^ B) * 2 ^ (B * k) := by
          rw [← Fin.sum_univ_eq_sum_range (fun k => (dtot / 2 ^ (B * k) % 2 ^ B) * 2 ^ (B * k))]
          apply Finset.sum_congr rfl
          intro i _
          have : (Vector.map (Expression.eval env.toEnvironment)
              (Vector.mapRange m fun j => var { index := i₀ + j }))[i] = env.get (i₀ + i.val) := by
            simp [circuit_norm]
          rw [this, hd_val' i]
        rw [hstep, limb_decomp_mod, Nat.mod_eq_of_lt hdtot_lt]

      have hCn_eq : ∀ k : ℕ, k < m - 1 →
          (env.get (i₀ + m + m * (B - 1) + k)).val = P k / 2 ^ (B * (k + 1)) := by
        intro k hk

        have hraw : (1 + ∑ x ∈ Finset.range (k + 1),
            ((if h : x < m then (Expression.eval env.toEnvironment input_var.lhs[x]).val else 0) +
              (if h : x < m then (env.get (i₀ + x)).val else 0)) * 2 ^ (B * x)) / 2 ^ (B * (k + 1))
            = P k / 2 ^ (B * (k + 1)) := by
          congr 1
          simp only [hP]
          congr 1
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.mem_range] at hj
          have hjm : j < m := by omega
          congr 1
          simp only [hgfun, hAn, hDn, dif_pos hjm]
          congr 1
          rw [← h_input]; simp [Vector.getElem_map]
        rw [h_cwit ⟨k, hk⟩]
        simp only [Vector.getElem_ofFn]
        rw [ZMod.val_natCast_of_lt, hraw]
        rw [hraw]
        have hbit : P k / 2 ^ (B * (k + 1)) ≤ 1 := (ripple_carry B gfun hgfun_le k).2
        have := hB; have := Nat.two_pow_pos B; omega

      have hm : 0 < m := by
        by_contra h
        have hm0 : m = 0 := by omega
        have h1 : va < 2 ^ (B * m) := hva_lt
        have h2 : vb < 2 ^ (B * m) := hvb_lt
        rw [hm0, Nat.mul_zero, pow_zero] at h1 h2
        omega

      have hsum_an : (∑ j ∈ Finset.range m, An j * 2 ^ (B * j)) = va := by
        rw [hva, BigInt.value_eq_sum, ← Fin.sum_univ_eq_sum_range (fun j => An j * 2 ^ (B * j))]
        apply Finset.sum_congr rfl
        intro i _; simp only [hAn, dif_pos i.isLt, Fin.getElem_fin]
      have hsum_dn : (∑ j ∈ Finset.range m, Dn j * 2 ^ (B * j)) = dtot := by
        rw [← hvd, BigInt.value_eq_sum, ← Fin.sum_univ_eq_sum_range (fun j => Dn j * 2 ^ (B * j))]
        apply Finset.sum_congr rfl
        intro i _
        simp only [hDn, dif_pos i.isLt]
        congr 1
        have : (Vector.map (Expression.eval env.toEnvironment)
            (Vector.mapRange m fun j => var { index := i₀ + j }))[i] = env.get (i₀ + i.val) := by
          simp [circuit_norm]
        rw [this]

      have hPlast : P (m - 1) = vb := by
        simp only [hP]
        rw [show m - 1 + 1 = m by omega]
        simp only [hgfun]
        rw [show (∑ j ∈ Finset.range m, (An j + Dn j) * 2 ^ (B * j))
            = (∑ j ∈ Finset.range m, An j * 2 ^ (B * j))
              + (∑ j ∈ Finset.range m, Dn j * 2 ^ (B * j)) by
          rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro j _; ring]
        rw [hsum_an, hsum_dn]; omega

      have hBn_eq : ∀ k, k < m → Bn k = vb / 2 ^ (B * k) % 2 ^ B := by
        intro k hk
        have hvb_sum : vb = ∑ j ∈ Finset.range m, Bn j * 2 ^ (B * j) := by
          rw [hvb, BigInt.value_eq_sum, ← Fin.sum_univ_eq_sum_range (fun j => Bn j * 2 ^ (B * j))]
          apply Finset.sum_congr rfl
          intro i _; simp only [hBn, dif_pos i.isLt, Fin.getElem_fin]
        rw [hvb_sum]
        exact (digit_extract B Bn (fun j => by
          rcases Nat.lt_or_ge j m with hj | hj
          · exact hBn_lt j hj
          · simp only [hBn, dif_neg (by omega : ¬ j < m)]; exact Nat.two_pow_pos B) m k hk).symm

      have hCn_bit : ∀ k : ℕ, k < m - 1 → IsBool (env.get (i₀ + m + m * (B - 1) + k)) := by
        intro k hk
        have hle : (env.get (i₀ + m + m * (B - 1) + k)).val ≤ 1 := by
          rw [hCn_eq k hk]; exact (ripple_carry B gfun hgfun_le k).2
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h0 | h1
        · left; exact (ZMod.val_eq_zero _).mp h0
        · right
          have : env.get (i₀ + m + m * (B - 1) + k) = ((1 : ℕ) : F p) := by
            conv_rhs => rw [← h1]
            rw [ZMod.natCast_zmod_val]
          simpa using this
      refine ⟨?_, ?_, ?_⟩
      ·
        refine ⟨trivial, ?_⟩
        intro i
        have : (Vector.map (Expression.eval env.toEnvironment)
            (Vector.mapRange m fun j => var { index := i₀ + j }))[i] = env.get (i₀ + i.val) := by
          simp [circuit_norm]
        rw [this]
        have := hDn_lt i.val i.isLt
        simp only [hDn, dif_pos i.isLt] at this
        exact this
      ·
        intro i
        have hbit := hCn_bit i.val i.isLt
        rw [show env.get (i₀ + m + m * (B - 1) + i.val) + -1
          = env.get (i₀ + m + m * (B - 1) + i.val) - 1 by ring]
        exact (IsBool.iff_mul_sub_one).mp hbit
      ·
        set Cn : ℕ → ℕ := fun k =>
          if k < m - 1 then (env.get (i₀ + m + m * (B - 1) + k)).val else 0 with hCn
        have hCnP : ∀ k, k < m - 1 → Cn k = P k / 2 ^ (B * (k + 1)) := fun k hk => by
          simp only [hCn, if_pos hk]; exact hCn_eq k hk

        have hnat : ∀ k, k < m →
            An k + Dn k + (if k = 0 then 0 else Cn (k - 1)) + (if k = 0 then 1 else 0)
              = Bn k + Cn k * 2 ^ B := by
          intro k hk
          have hre : gfun k + (if k = 0 then 1 else P (k - 1) / 2 ^ (B * k))
              = (P k / 2 ^ (B * k)) % 2 ^ B + (P k / 2 ^ (B * (k + 1))) * 2 ^ B := ripple_eq B gfun k

          have hlimb : (P k / 2 ^ (B * k)) % 2 ^ B = Bn k := by
            have h1 : P (m - 1) / 2 ^ (B * k) % 2 ^ B = P k / 2 ^ (B * k) % 2 ^ B :=
              limb_stable B gfun k (m - 1) (by omega)
            rw [hBn_eq k hk, ← hPlast, ← h1]

          have hco : P k / 2 ^ (B * (k + 1)) = Cn k := by
            rcases Nat.lt_or_ge k (m - 1) with hk1 | hk1
            · exact (hCnP k hk1).symm
            · have hkm : k = m - 1 := by omega
              subst hkm
              simp only [hCn]
              rw [if_neg (lt_irrefl _), show m - 1 + 1 = m from by omega, hPlast]
              exact Nat.div_eq_of_lt hvb_lt
          rw [hlimb, hco] at hre
          simp only [hgfun] at hre

          rcases Nat.eq_zero_or_pos k with hk0 | hk0
          · subst hk0
            simp only [↓reduceIte] at hre ⊢
            omega
          · rw [if_neg (by omega : ¬ k = 0), if_neg (by omega : ¬ k = 0)]
            have hcin : P (k - 1) / 2 ^ (B * k) = Cn (k - 1) := by
              rw [hCnP (k - 1) (by omega), show k - 1 + 1 = k from by omega]
            rw [if_neg (by omega : ¬ k = 0), hcin] at hre
            omega

        intro i
        have hk := i.isLt
        have hnatk := hnat i.val hk

        have ha_e : Expression.eval env.toEnvironment input_var.lhs[i.val] = input.lhs[i.val]'hk := by
          rw [← h_input]; simp [Vector.getElem_map]
        have hb_e : Expression.eval env.toEnvironment input_var.rhs[i.val] = input.rhs[i.val]'hk := by
          rw [← h_input]; simp [Vector.getElem_map]
        have hcin_e : Expression.eval env.toEnvironment
            (if h : i.val = 0 then 0 else var { index := i₀ + m + m * (B - 1) + (i.val - 1) })
            = if i.val = 0 then 0 else env.get (i₀ + m + m * (B - 1) + (i.val - 1)) := by
          split <;> simp [circuit_norm]
        have hone_e : Expression.eval env.toEnvironment (if i.val = 0 then 1 else 0)
            = if i.val = 0 then (1 : F p) else 0 := by split <;> simp [circuit_norm]
        have hcout_e : Expression.eval env.toEnvironment
            (if h : i.val < m - 1 then var { index := i₀ + m + m * (B - 1) + i.val } else 0)
            = if i.val < m - 1 then env.get (i₀ + m + m * (B - 1) + i.val) else 0 := by
          split <;> simp [circuit_norm]
        rw [ha_e, hb_e, hcin_e, hone_e, hcout_e]

        have hAk : ((An i.val : ℕ) : F p) = (input.lhs[i.val]'hk) := by
          simp only [hAn, dif_pos hk]; rw [ZMod.natCast_zmod_val]
        have hDk : ((Dn i.val : ℕ) : F p) = env.get (i₀ + i.val) := by
          simp only [hDn, dif_pos hk]; rw [ZMod.natCast_zmod_val]
        have hBk : ((Bn i.val : ℕ) : F p) = (input.rhs[i.val]'hk) := by
          simp only [hBn, dif_pos hk]; rw [ZMod.natCast_zmod_val]
        have hCk : ((Cn i.val : ℕ) : F p)
            = (if i.val < m - 1 then env.get (i₀ + m + m * (B - 1) + i.val) else 0) := by
          simp only [hCn]
          split
          · rw [ZMod.natCast_zmod_val]
          · simp

        have hcast_eq : (input.lhs[i.val]'hk) + env.get (i₀ + i.val)
            + (if i.val = 0 then (0:F p) else env.get (i₀ + m + m * (B - 1) + (i.val - 1)))
            + (if i.val = 0 then (1 : F p) else 0)
            = (input.rhs[i.val]'hk)
              + (if i.val < m - 1 then env.get (i₀ + m + m * (B - 1) + i.val) else 0)
                * (2 ^ B : F p) := by
          have hcast := congrArg (Nat.cast : ℕ → F p) hnatk
          push_cast at hcast
          rw [hAk, hDk, hBk, hCk] at hcast

          rw [show ((if i.val = 0 then (0:F p) else env.get (i₀ + m + m * (B - 1) + (i.val - 1))))
                = ((if i.val = 0 then (0:ℕ) else Cn (i.val - 1) : ℕ) : F p) by
              split
              · simp
              · simp only [hCn]; rw [if_pos (by omega), ZMod.natCast_zmod_val],
            show ((if i.val = 0 then (1:F p) else 0))
                = ((if i.val = 0 then (1:ℕ) else 0 : ℕ) : F p) by split <;> simp]
          push_cast
          convert hcast using 2
        rw [hcast_eq]; ring

theorem computableWitnesses (P : BigIntParams p m) [Fact (p > 2)] :
    (circuit P).ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition input env env')
    ((main P input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.provableWitness_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.witnessVector_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.forEach_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.assertZero_structuralComputableWitnesses_iff]
  and_intros
  · intro _ h_input
    have hlhs : evalValue P.B env input.lhs = evalValue P.B env' input.lhs := by
      have h_lhs : eval env input.lhs = eval env' input.lhs := by
        simpa [circuit_norm] using congrArg (fun x : Inputs m (F p) => x.lhs) h_input
      have h_vec :
          input.lhs.map (Expression.eval env.toEnvironment) =
            input.lhs.map (Expression.eval env'.toEnvironment) := by
        simpa [CircuitType.eval_expression_prover_to_verifier, CircuitType.eval_expression,
          ProvableType.eval, explicit_provable_type] using h_lhs
      simp [evalValue, h_vec]
    have hrhs : evalValue P.B env input.rhs = evalValue P.B env' input.rhs := by
      have h_rhs : eval env input.rhs = eval env' input.rhs := by
        simpa [circuit_norm] using congrArg (fun x : Inputs m (F p) => x.rhs) h_input
      have h_vec :
          input.rhs.map (Expression.eval env.toEnvironment) =
            input.rhs.map (Expression.eval env'.toEnvironment) := by
        simpa [CircuitType.eval_expression_prover_to_verifier, CircuitType.eval_expression,
          ProvableType.eval, explicit_provable_type] using h_rhs
      simp [evalValue, h_vec]
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_ofFn, hlhs, hrhs]
  · apply Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
    · intro k env env' hk h_agree _
      apply Vector.ext
      intro i hi
      rw [← ProvableType.getElem_eval_fields_prover (env := env) _ i hi,
        ← ProvableType.getElem_eval_fields_prover (env := env') _ i hi]
      simp only [Circuit.output, ProvableType.witness, ProvableType.varFromOffset_fields,
        Vector.getElem_mapRange, Expression.eval]
      exact h_agree (offset + i) (by
        have hk' : offset + m ≤ k := by
          simpa [ProvableType.witness, Circuit.localLength, size] using hk
        omega)
    · exact NormalizeR.computableWitnesses P P.hB1
  · intro h_agree h_input
    ext i
    simp only [Vector.getElem_ofFn]
    apply congrArg (fun n : ℕ => (n : F p))
    apply congrArg (fun s => ((1 + s) / 2 ^ (P.B * (i + 1)) : ℕ))
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    have hjm : j < m := by omega
    simp only [dif_pos hjm]
    have hlhs :
        ZMod.val (Expression.eval env.toEnvironment input.lhs[j]) =
          ZMod.val (Expression.eval env'.toEnvironment input.lhs[j]) := by
      apply congrArg ZMod.val
      have h_lhs : eval env input.lhs = eval env' input.lhs := by
        simpa [circuit_norm] using congrArg (fun x : Inputs m (F p) => x.lhs) h_input
      have h : (eval env input.lhs)[j] = (eval env' input.lhs)[j] := by
        simpa only using congrArg (fun x : BigInt m (F p) => x[j]) h_lhs
      rw [← ProvableType.getElem_eval_fields_prover (env := env) input.lhs j hjm,
        ← ProvableType.getElem_eval_fields_prover (env := env') input.lhs j hjm] at h
      exact h
    have hd :
        ZMod.val
          (Expression.eval env.toEnvironment
            ((ProvableType.witness (α := BigInt m) fun env =>
                    Vector.ofFn fun k : Fin m =>
                      (((evalValue P.B env input.rhs - 1 - evalValue P.B env input.lhs) /
                        2 ^ (P.B * k.val) % 2 ^ P.B : ℕ) : F p)).output
                offset)[j]) =
        ZMod.val
          (Expression.eval env'.toEnvironment
            ((ProvableType.witness (α := BigInt m) fun env =>
                    Vector.ofFn fun k : Fin m =>
                      (((evalValue P.B env input.rhs - 1 - evalValue P.B env input.lhs) /
                        2 ^ (P.B * k.val) % 2 ^ P.B : ℕ) : F p)).output
                offset)[j]) := by
      apply congrArg ZMod.val
      rw [Circuit.output, ProvableType.witness]
      simp only [ProvableType.varFromOffset_fields, Vector.getElem_mapRange, Expression.eval]
      exact h_agree (offset + j) (by
        have hdlen :
            (ProvableType.witness (α := BigInt m) fun env =>
              (Vector.ofFn fun k : Fin m =>
                (((evalValue P.B env input.rhs - 1 - evalValue P.B env input.lhs) /
                  2 ^ (P.B * k.val) % 2 ^ P.B : ℕ) : F p))).localLength offset = m := by
          simp [ProvableType.witness, Circuit.localLength, Operations.localLength, size]
        omega)
    rw [hlhs, hd]
  · intro _
    trivial
  · intro _
    trivial

theorem computableWitness (P : BigIntParams p m) [Fact (p > 2)] : ∀ n input,
    ProverEnvironment.OnlyAccessedBelow n
      (fun env : ProverEnvironment (F p) => eval env input) →
    Circuit.ComputableWitnesses (main P input) n := by
  exact Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnesses_implies
    (computableWitnesses P)

end LessThanR

end

end Solution.Secp256k1ScalarMulFixedBase

end

namespace Solution.Secp256k1ScalarMulFixedBase
namespace Canonicalize

open CompactAdd (cExp)

/-- The weight `2 ^ (64 * k)` as a field constant. -/
def wP (k : ℕ) : F circomPrime := ((2 ^ (limbBits * k) : ℕ) : F circomPrime)

/-- `∑_{k<4} a k * 2 ^ (64 k)` as an expression. -/
def emuPoly (a : Var Emu (F circomPrime)) : Expression (F circomPrime) :=
  a[0] + wP 1 * a[1] + wP 2 * a[2] + wP 3 * a[3]

/-- The conditional-reduction bit of the canonicalisation, recovered as an
AFFINE expression over wires that are already allocated (the input limbs and
the witnessed remainder), instead of being witnessed.  `P256` is a
compile-time constant, so `(P256 : F)⁻¹` is a numeral and the expression stays
affine; the booleanity row that used to constrain the witness now constrains
this expression, which is still rank-1.  Saves one allocation per call. -/
def bExpr (x r : Var Emu (F circomPrime)) : Expression (F circomPrime) :=
  (((P256 : ℕ) : F circomPrime)⁻¹) * (emuPoly x - emuPoly r)

lemma bExpr_eval_stable {e e' : Environment (F circomPrime)}
    {x r : Var Emu (F circomPrime)}
    (hx : ∀ (j : ℕ) (hj : j < 4), Expression.eval e (x[j]'hj) = Expression.eval e' (x[j]'hj))
    (hr : ∀ (j : ℕ) (hj : j < 4), Expression.eval e (r[j]'hj) = Expression.eval e' (r[j]'hj)) :
    Expression.eval e (bExpr x r) = Expression.eval e' (bExpr x r) := by
  simp only [bExpr, emuPoly, Expression.eval,
    hx 0 (by decide), hx 1 (by decide), hx 2 (by decide), hx 3 (by decide),
    hr 0 (by decide), hr 1 (by decide), hr 2 (by decide), hr 3 (by decide)]

def main (x : Var Emu (F circomPrime)) :
    Circuit (F circomPrime) (Var (fields coordBytes) (F circomPrime)) := do

  let r ← ProvableType.witness (α := Emu) fun env =>
    emuOfNat (evalEmu env x % P256)

  assertZero (bExpr x r * (bExpr x r - 1))

  -- `ValidPBytes` returns the bytes as AFFINE EXPRESSIONS over the bits it has
  -- already allocated for the canonicality proof, so they are returned directly:
  -- re-witnessing them and linking would cost one allocation and one row per byte
  -- for nothing (the range check IS the output encoding).
  let validBytes ← ValidPBytes.circuit r

  -- The conditional-reduction bit is an INVERTED (affine) expression, so the
  -- native top row `∑ (lhsₖ - rhsₖ) 2^(64k) = 0` is identically zero in the
  -- wires and carries no information: use the top-row-free variant.
  GroupedFlex.circuitNoTop 64 gfLin posOfLin 3 vCanonicalL vCanonicalR hgvCanonical
      (by norm_num) {
    lhs := Vector.mapFinRange 5 fun k =>
      if h : k.val < 4 then r[k.val] + bExpr x r * cExp P256 k.val else 0
    rhs := Vector.mapFinRange 5 fun k =>
      if h : k.val < 4 then x[k.val] else 0 }

  return validBytes

instance elaborated : ElaboratedCircuit (F circomPrime) Emu (fields coordBytes) main := by
  elaborate_circuit

def Assumptions (x : Emu (F circomPrime)) : Prop :=
  x.Normalized limbBits

def Spec (x : Emu (F circomPrime)) (out : fields coordBytes (F circomPrime)) : Prop :=
  (∀ i : Fin coordBytes, (out[i]).val < 256) ∧
    Limbs.fromLimbs 8 (out.toList.map ZMod.val)
      = (decodeFe x).val

end Canonicalize
end Solution.Secp256k1ScalarMulFixedBase

namespace Solution.Secp256k1ScalarMulFixedBase
namespace Canonicalize
section ComputableWitness
open Challenge.Utils.ComputableWitnessLemmas
set_option maxHeartbeats 3200000 in
theorem structuralCW {Parent : TypeMap} [CircuitType Parent]
    (parentInput : Var Parent (F circomPrime))
    (x : Var Emu (F circomPrime)) (n : ℕ)
    (hx : ∀ (k : ℕ) (env env' : ProverEnvironment (F circomPrime)), n ≤ k →
      env.AgreesBelow k env' → eval env parentInput = eval env' parentInput →
      eval env x = eval env' x)
    (env env' : ProverEnvironment (F circomPrime)) :
    FormalCircuitBase.Operations.StructuralComputableWitnesses
      parentInput env env' n ((main x).operations n) := by
  unfold main
  simp only [
    Circuit.bind_structuralComputableWitnesses_iff,
    Circuit.provableWitness_structuralComputableWitnesses_iff,
    Circuit.assertZero_structuralComputableWitnesses_iff,
    Circuit.pure_structuralComputableWitnesses_iff,
    FormalAssertion.assertion_structuralComputableWitnesses_iff,
    and_true, true_and]
  simp only [circuit_norm, numLimbs, coordBytes]
  refine ⟨?_, ?_, ?_⟩
  · intro hagree hpin
    have hxx := evalEmu_eq_of_eval_eq (hx n env env' (by omega) hagree hpin)
    apply Vector.ext; intro i hi
    simp only [Vector.getElem_ofFn, hxx]
  · exact Challenge.Utils.ComputableWitnessLemmas.GeneralFormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Parent) ValidPBytes.circuit parentInput
      (Vector.mapRange 4 fun i => var { index := n + i }) _ (by
        intro k e1 e2 hle h_agree h_input
        rw [CircuitType.eval_var_fields_prover, CircuitType.eval_var_fields_prover]
        apply Vector.ext; intro i hi
        simp only [Vector.getElem_map, Vector.getElem_mapRange, Expression.eval]
        exact h_agree (n + i) (by
          have hii : i < 4 := by simpa only [numLimbs] using hi
          omega))
      ValidPBytes.computableWitnesses env env'
  · apply FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
    · intro k e1 e2 hle h_agree h_input
      simp only [circuit_norm] at hle
      simp only [circuit_norm]
      have hxmap := emu_map_eval_eq_of_eval_eq (hx k e1 e2 (by omega) h_agree h_input)
      have hxs : ∀ (j : ℕ) (hj : j < 4),
          Expression.eval e1.toEnvironment (x[j]'hj)
            = Expression.eval e2.toEnvironment (x[j]'hj) := by
        intro j hj
        have := congrArg (fun v => v[j]'(by simpa only [numLimbs] using hj)) hxmap
        simpa only [Vector.getElem_map] using this
      have hrs : ∀ (j : ℕ) (hj : j < 4),
          Expression.eval e1.toEnvironment
              ((Vector.mapRange 4 fun i => var (F := F circomPrime) { index := n + i })[j]'hj)
            = Expression.eval e2.toEnvironment
              ((Vector.mapRange 4 fun i => var (F := F circomPrime) { index := n + i })[j]'hj) := by
        intro j hj
        simp only [Vector.getElem_mapRange, Expression.eval]
        exact h_agree (n + j) (by omega)
      have hbs := bExpr_eval_stable (e := e1.toEnvironment) (e' := e2.toEnvironment) hxs hrs
      congr 1
      · apply Vector.ext; intro i hi
        simp only [Vector.getElem_map, Vector.getElem_mapFinRange]
        split
        · next hlt =>
          simp only [Expression.eval, CompactAdd.cExp, Vector.getElem_ofFn]
          rw [h_agree (n + i) (by omega), hbs]
        · rfl
      · apply Vector.ext; intro i hi
        simp only [Vector.getElem_map, Vector.getElem_mapFinRange]
        split
        · next h =>
          have hxmap := emu_map_eval_eq_of_eval_eq (hx k e1 e2 (by omega) h_agree h_input)
          exact eval_mem_of_map_eval_eq hxmap _ (Vector.getElem_mem h)
        · rfl
    · exact GroupedFlex.computableWitnessesNoTop 64 gfLin posOfLin 3
        vCanonicalL vCanonicalR hgvCanonical (by norm_num)
end ComputableWitness
end Canonicalize
end Solution.Secp256k1ScalarMulFixedBase

end DonorFile1_19
