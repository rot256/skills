import Solution.Secp256k1ScalarMul.GroupedEq



namespace Solution.Secp256k1ScalarMul

section
variable {p : ℕ} [Fact p.Prime]
variable {m : ℕ} [NeZero m]

namespace GroupedEqV

open GroupedEq (numGroups numGroups_pos numGroups_mul_ge numGroups_pred_mul_lt
  group_flatten sum_extend_zero geom_sum_le groupExpr groupExpr_eval)




structure VParams where
  
  Nf : ℕ → ℕ
  
  OFFf : ℕ → ℕ
  
  Wf : ℕ → ℕ
  
  Nmax : ℕ
  
  OFFmax : ℕ
  
  Wmax : ℕ


def GVHyps (p m : ℕ) (B g : ℕ) (V : VParams) : Prop :=
  1 ≤ g ∧ 2 ^ (B * g) < p ∧ 2 ^ V.Wmax < p ∧
  (∀ k, 1 ≤ V.Wf k ∧ 2 ^ V.Wf k < p) ∧
  (∀ j, 1 ≤ V.Nf j) ∧
  (∀ j, j < 2 * m - 1 → V.Nf j ≤ V.Nmax) ∧
  (∀ k, k < numGroups m g - 1 →
    V.Wf k ≤ V.Wmax ∧ V.OFFf k ≤ V.OFFmax ∧
    2 * V.OFFf k < 2 ^ V.Wf k ∧
    (if k = 0 then 0 else V.OFFf (k - 1)) + 1
        + (∑ i ∈ Finset.range g, (V.Nf (g * k + i) - 1) * 2 ^ (B * i))
      ≤ (V.OFFf k + 1) * 2 ^ (B * g)) ∧
  V.Nmax * 2 ^ (B * (g - 1)) * 2 + 2 ^ V.Wmax * 2 ^ (B * g)
    + V.OFFmax * 2 ^ (B * g) + 2 ^ V.Wmax < p




def carryExpr (B g : ℕ) (OFFf : ℕ → ℕ) (lhs rhs : Var (EqViaCarries.Coeffs m) (F p)) :
    ℕ → Expression (F p)
  | 0 =>
      (groupExpr B g lhs 0 - groupExpr B g rhs 0) / ((2 : F p) ^ (B * g))
        + ((OFFf 0 : ℕ) : F p)
  | k + 1 =>
      (groupExpr B g lhs (k + 1) + (carryExpr B g OFFf lhs rhs k - ((OFFf k : ℕ) : F p))
          - groupExpr B g rhs (k + 1)) / ((2 : F p) ^ (B * g))
        + ((OFFf (k + 1) : ℕ) : F p)


def carryInExpr (B g : ℕ) (OFFf : ℕ → ℕ) (lhs rhs : Var (EqViaCarries.Coeffs m) (F p))
    (k : ℕ) : Expression (F p) :=
  if k = 0 then 0 else carryExpr B g OFFf lhs rhs (k - 1) - ((OFFf (k - 1) : ℕ) : F p)




def widthAllocFrom (Wf : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | c + 1, k₀ => (Wf k₀ - 1) + widthAllocFrom Wf c (k₀ + 1)


def widthConsFrom (Wf : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | c + 1, k₀ => Wf k₀ + widthConsFrom Wf c (k₀ + 1)




def carryLoop (B g : ℕ) (OFFf Wf : ℕ → ℕ) (hWok : ∀ k, 1 ≤ Wf k ∧ 2 ^ Wf k < p)
    [Fact (p > 2)]
    (lhs rhs : Var (EqViaCarries.Coeffs m) (F p)) :
    ℕ → ℕ → Circuit (F p) Unit
  | 0, _ => pure ()
  | c + 1, k₀ => do
      assertion (RangeCheck.circuit (Wf k₀) (hWok k₀).2 (hWok k₀).1)
        (carryExpr B g OFFf lhs rhs k₀)
      carryLoop B g OFFf Wf hWok lhs rhs c (k₀ + 1)


def main (B g : ℕ) (V : VParams) (hgv : GVHyps p m B g V) [Fact (p > 2)]
    (input : Var (EqViaCarries.Inputs m) (F p)) :
    Circuit (F p) Unit := do
  let Pc := input.lhs
  let Sc := input.rhs
  carryLoop B g V.OFFf V.Wf hgv.2.2.2.1 Pc Sc (numGroups m g - 1) 0
  let last := numGroups m g - 1
  assertZero
    (groupExpr B g Pc last
      + carryInExpr B g V.OFFf Pc Sc last
      - groupExpr B g Sc last)



lemma carryLoop_localLength (B g : ℕ) (OFFf Wf : ℕ → ℕ)
    (hWok : ∀ k, 1 ≤ Wf k ∧ 2 ^ Wf k < p) [Fact (p > 2)]
    (lhs rhs : Var (EqViaCarries.Coeffs m) (F p)) :
    ∀ (c k₀ offset : ℕ),
      (carryLoop B g OFFf Wf hWok lhs rhs c k₀).localLength offset
        = widthAllocFrom Wf c k₀ := by
  intro c
  induction c with
  | zero => intro k₀ offset; simp [carryLoop, widthAllocFrom, circuit_norm]
  | succ n ih =>
    intro k₀ offset
    simp only [carryLoop, widthAllocFrom, circuit_norm, RangeCheck.circuit,
      RangeCheck.elaborated, ih]

lemma carryLoop_subcircuitsConsistent (B g : ℕ) (OFFf Wf : ℕ → ℕ)
    (hWok : ∀ k, 1 ≤ Wf k ∧ 2 ^ Wf k < p) [Fact (p > 2)]
    (lhs rhs : Var (EqViaCarries.Coeffs m) (F p)) :
    ∀ (c k₀ offset : ℕ),
      ((carryLoop B g OFFf Wf hWok lhs rhs c k₀).operations offset).SubcircuitsConsistent offset := by
  intro c
  induction c with
  | zero => intro k₀ offset; simp [carryLoop, circuit_norm]
  | succ n ih =>
    intro k₀ offset
    have key : ∀ k off, Operations.forAll off { subcircuit := fun off {n} _ => n = off }
        ((carryLoop B g OFFf Wf hWok lhs rhs n k).operations off) :=
      fun k off => ih k off
    simp only [carryLoop, circuit_norm, RangeCheck.circuit, RangeCheck.elaborated]
    ring_nf
    apply key

lemma carryLoop_channelsLawful (B g : ℕ) (OFFf Wf : ℕ → ℕ)
    (hWok : ∀ k, 1 ≤ Wf k ∧ 2 ^ Wf k < p) [Fact (p > 2)]
    (lhs rhs : Var (EqViaCarries.Coeffs m) (F p)) :
    ∀ (c k₀ offset : ℕ),
      ((carryLoop B g OFFf Wf hWok lhs rhs c k₀).operations offset).ChannelsLawful [] [] := by
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
          (carryExpr B g OFFf lhs rhs k₀)
        carryLoop B g OFFf Wf hWok lhs rhs n (k₀ + 1)).operations offset).ChannelsLawful [] []
    rw [Circuit.bind_operations_eq]
    have hhead : ((assertion (RangeCheck.circuit (Wf k₀) (hWok k₀).2 (hWok k₀).1)
        (carryExpr B g OFFf lhs rhs k₀)).operations offset).ChannelsLawful [] [] := by
      simp only [circuit_norm, RangeCheck.circuit, RangeCheck.elaborated]
    exact Operations.channelsLawful_append_of_channelsLawful hhead (ih _ _)


lemma carryLoop_soundness (B g : ℕ) (OFFf Wf : ℕ → ℕ)
    (hWok : ∀ k, 1 ≤ Wf k ∧ 2 ^ Wf k < p) [Fact (p > 2)]
    (env : Environment (F p))
    (lhs rhs : Var (EqViaCarries.Coeffs m) (F p)) :
    ∀ (c k₀ offset : ℕ),
      Operations.forAllNoOffset
        { assert := fun e ↦ Expression.eval env e = 0, lookup := fun l ↦ l.Soundness env,
          interact := fun i ↦ i.Guarantees env,
          subcircuit := fun {_m} s ↦ s.Assumptions env → s.Spec env }
        ((carryLoop B g OFFf Wf hWok lhs rhs c k₀).operations offset) →
      ∀ i, i < c →
        (Expression.eval env (carryExpr B g OFFf lhs rhs (k₀ + i))).val < 2 ^ Wf (k₀ + i) := by
  intro c
  induction c with
  | zero => intro k₀ offset _ i hi; omega
  | succ n ih =>
    intro k₀ offset h_holds i hi
    rw [show carryLoop B g OFFf Wf hWok lhs rhs (n + 1) k₀
        = (do
            assertion (RangeCheck.circuit (Wf k₀) (hWok k₀).2 (hWok k₀).1)
              (carryExpr B g OFFf lhs rhs k₀)
            carryLoop B g OFFf Wf hWok lhs rhs n (k₀ + 1)) from rfl] at h_holds
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


lemma carryLoop_completeness (B g : ℕ) (OFFf Wf : ℕ → ℕ)
    (hWok : ∀ k, 1 ≤ Wf k ∧ 2 ^ Wf k < p) [Fact (p > 2)]
    (env : ProverEnvironment (F p))
    (lhs rhs : Var (EqViaCarries.Coeffs m) (F p)) :
    ∀ (c k₀ offset : ℕ),
      (∀ i, i < c →
        (Expression.eval env.toEnvironment (carryExpr B g OFFf lhs rhs (k₀ + i))).val
          < 2 ^ Wf (k₀ + i)) →
      Operations.forAllNoOffset
        { assert := fun e ↦ Expression.eval env.toEnvironment e = 0,
          lookup := fun l ↦ l.Completeness env.toEnvironment,
          interact := fun i ↦ i.Guarantees env.toEnvironment,
          subcircuit := fun {_m} s ↦ s.ProverAssumptions env }
        ((carryLoop B g OFFf Wf hWok lhs rhs c k₀).operations offset) := by
  intro c
  induction c with
  | zero =>
    intro k₀ offset _
    simp only [carryLoop, Circuit.pure_operations_eq, Operations.forAllNoOffset_empty]
  | succ n ih =>
    intro k₀ offset h_small
    rw [show carryLoop B g OFFf Wf hWok lhs rhs (n + 1) k₀
        = (do
            assertion (RangeCheck.circuit (Wf k₀) (hWok k₀).2 (hWok k₀).1)
              (carryExpr B g OFFf lhs rhs k₀)
            carryLoop B g OFFf Wf hWok lhs rhs n (k₀ + 1)) from rfl]
    rw [Circuit.bind_operations_eq, Operations.forAllNoOffset_append]
    constructor
    · simp only [circuit_norm, RangeCheck.circuit]
      exact ⟨trivial, by simpa [RangeCheck.Spec, Nat.add_zero] using h_small 0 (by omega)⟩
    · refine ih (k₀ + 1) _ fun i hi => ?_
      have := h_small (i + 1) (by omega)
      rwa [show k₀ + (i + 1) = k₀ + 1 + i from by ring] at this


lemma carryLoop_requirements (B g : ℕ) (OFFf Wf : ℕ → ℕ)
    (hWok : ∀ k, 1 ≤ Wf k ∧ 2 ^ Wf k < p) [Fact (p > 2)]
    (env : Environment (F p))
    (lhs rhs : Var (EqViaCarries.Coeffs m) (F p)) :
    ∀ (c k₀ offset : ℕ),
      Operations.forAllNoOffset
        { interact := fun i ↦ i.Requirements env,
          subcircuit := fun {_m} s ↦ s.channelsWithRequirements = [] ∨ s.Assumptions env }
        ((carryLoop B g OFFf Wf hWok lhs rhs c k₀).operations offset) := by
  intro c
  induction c with
  | zero =>
    intro k₀ offset
    simp only [carryLoop, Circuit.pure_operations_eq, Operations.forAllNoOffset_empty]
  | succ n ih =>
    intro k₀ offset
    show Operations.forAllNoOffset _ ((do
        assertion (RangeCheck.circuit (Wf k₀) (hWok k₀).2 (hWok k₀).1)
          (carryExpr B g OFFf lhs rhs k₀)
        carryLoop B g OFFf Wf hWok lhs rhs n (k₀ + 1)).operations offset)
    rw [Circuit.bind_operations_eq, Operations.forAllNoOffset_append]
    refine ⟨?_, ih _ _⟩
    simp only [circuit_norm, RangeCheck.circuit, RangeCheck.elaborated]

instance elaborated (B g : ℕ) (V : VParams) (hgv : GVHyps p m B g V) [Fact (p > 2)] :
    ElaboratedCircuit (F p) (EqViaCarries.Inputs m) unit (main B g V hgv) where
  localLength _ := widthAllocFrom V.Wf (numGroups m g - 1) 0
  localLength_eq := by
    intro input offset
    simp only [main, circuit_norm,
      carryLoop_localLength B g V.OFFf V.Wf hgv.2.2.2.1 input.lhs input.rhs]
  subcircuitsConsistent := by
    intro input offset
    have key : ∀ off, Operations.forAll off { subcircuit := fun off {n} _ => n = off }
        ((carryLoop B g V.OFFf V.Wf hgv.2.2.2.1 input.lhs input.rhs
          (numGroups m g - 1) 0).operations off) :=
      fun off => carryLoop_subcircuitsConsistent B g V.OFFf V.Wf hgv.2.2.2.1 _ _ _ _ off
    simp only [main, circuit_norm]
    ring_nf
    apply key
  channelsLawful := by
    intro input offset
    simp only [main, Circuit.bind_operations_eq]
    refine Operations.channelsLawful_append_of_channelsLawful
      (carryLoop_channelsLawful B g V.OFFf V.Wf hgv.2.2.2.1 _ _ _ _ _) ?_
    simp only [circuit_norm]




def Assumptions (Nf : ℕ → ℕ) (input : EqViaCarries.Inputs m (F p)) : Prop :=
  (∀ k : Fin (2 * m - 1), (input.lhs[k.val]).val < Nf k.val) ∧
  (∀ k : Fin (2 * m - 1), (input.rhs[k.val]).val < Nf k.val)




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




lemma prefix_div_le (B g : ℕ) (V : VParams) (G : ℕ)
    (hOFFrec : ∀ k, k < G →
      (if k = 0 then 0 else V.OFFf (k - 1)) + 1
          + (∑ i ∈ Finset.range g, (V.Nf (g * k + i) - 1) * 2 ^ (B * i))
        ≤ (V.OFFf k + 1) * 2 ^ (B * g))
    (f : ℕ → ℕ) (hf : ∀ t, f t < V.Nf t) :
    ∀ k, k < G →
      (∑ j ∈ Finset.range (k + 1),
          (∑ i ∈ Finset.range g, f (g * j + i) * 2 ^ (B * i)) * 2 ^ (B * g * j))
        < (V.OFFf k + 1) * 2 ^ (B * g * (k + 1)) := by
  have hQle : ∀ j, (∑ i ∈ Finset.range g, f (g * j + i) * 2 ^ (B * i))
      ≤ ∑ i ∈ Finset.range g, (V.Nf (g * j + i) - 1) * 2 ^ (B * i) := by
    intro j
    apply Finset.sum_le_sum
    intro i _
    have := hf (g * j + i)
    exact Nat.mul_le_mul_right _ (by omega)
  intro k
  induction k with
  | zero =>
    intro hk
    have h0 := hOFFrec 0 hk
    simp only [reduceIte] at h0
    have hQ := hQle 0
    rw [Finset.sum_range_one]
    have e1 : B * g * 0 = 0 := by ring
    have e2 : B * g * (0 + 1) = B * g := by ring
    rw [e1, e2, pow_zero, Nat.mul_one]
    omega
  | succ n ih =>
    intro hk
    have hprev := ih (by omega)
    have hrec := hOFFrec (n + 1) hk
    rw [if_neg (by omega : ¬ n + 1 = 0), Nat.add_sub_cancel] at hrec
    have hQ := hQle (n + 1)
    rw [Finset.sum_range_succ]
    have hstep : (∑ i ∈ Finset.range g, f (g * (n + 1) + i) * 2 ^ (B * i)) * 2 ^ (B * g * (n + 1))
        ≤ (∑ i ∈ Finset.range g, (V.Nf (g * (n + 1) + i) - 1) * 2 ^ (B * i))
            * 2 ^ (B * g * (n + 1)) :=
      Nat.mul_le_mul_right _ hQ
    have hpow : (2 : ℕ) ^ (B * g * (n + 1 + 1)) = 2 ^ (B * g * (n + 1)) * 2 ^ (B * g) := by
      rw [← pow_add, show B * g * (n + 1) + B * g = B * g * (n + 1 + 1) from by ring]
    calc (∑ j ∈ Finset.range (n + 1),
            (∑ i ∈ Finset.range g, f (g * j + i) * 2 ^ (B * i)) * 2 ^ (B * g * j))
          + (∑ i ∈ Finset.range g, f (g * (n + 1) + i) * 2 ^ (B * i)) * 2 ^ (B * g * (n + 1))
        < (V.OFFf n + 1) * 2 ^ (B * g * (n + 1))
          + (∑ i ∈ Finset.range g, (V.Nf (g * (n + 1) + i) - 1) * 2 ^ (B * i))
              * 2 ^ (B * g * (n + 1)) := by
          have := hstep
          omega
      _ = (V.OFFf n + 1
            + (∑ i ∈ Finset.range g, (V.Nf (g * (n + 1) + i) - 1) * 2 ^ (B * i)))
              * 2 ^ (B * g * (n + 1)) := by ring
      _ ≤ ((V.OFFf (n + 1) + 1) * 2 ^ (B * g)) * 2 ^ (B * g * (n + 1)) := by
          apply Nat.mul_le_mul_right
          omega
      _ = (V.OFFf (n + 1) + 1) * 2 ^ (B * g * (n + 1 + 1)) := by
          rw [hpow]; ring




def circuit (B g : ℕ) (V : VParams) (hgv : GVHyps p m B g V) (hB1 : 1 ≤ B)
    [Fact (p > 2)] : FormalAssertion (F p) (EqViaCarries.Inputs m) where
    main := main B g V hgv
    Assumptions := Assumptions V.Nf
    Spec := EqViaCarries.Spec B
    soundness := by
      obtain ⟨hg1, hpBg, hWmp, hWok, hNf1, hNcap, hper, hnowrap⟩ := hgv
      circuit_proof_start
      obtain ⟨h_loop, h_lin⟩ := h_holds
      have h_range := carryLoop_soundness B g V.OFFf V.Wf hWok env
        input_var.lhs input_var.rhs (numGroups m g - 1) 0 i₀ h_loop
      try simp only [circuit_norm] at h_lin
      have hM : 0 < 2 * m - 1 := by have := Nat.pos_of_neZero m; omega
      have hG1 : 0 < numGroups m g := numGroups_pos m g hg1
      have hCov : 2 * m - 1 ≤ g * numGroups m g := numGroups_mul_ge m g hg1
      set G := numGroups m g with hGdef
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
      -- effective offsets (0 at the top) and carries (0 at the top)
      set OFFe : ℕ → ℕ := fun k => if k = G - 1 then 0 else V.OFFf k with hOFFe
      set Cn : ℕ → ℕ := fun k => if k = G - 1 then 0
        else (Expression.eval env (carryExpr B g V.OFFf input_var.lhs input_var.rhs k)).val
        with hCn
      -- bounds
      have hCn_lt : ∀ k, k < G - 1 → Cn k < 2 ^ V.Wf k := by
        intro k hk
        simp only [hCn, if_neg (by omega : ¬ k = G - 1)]
        simpa using h_range k hk
      have hCn_lt_max : ∀ k, k < G → Cn k ≤ 2 ^ V.Wmax := by
        intro k hk
        by_cases hktop : k = G - 1
        · simp only [hCn, if_pos hktop]; positivity
        · have h1 := hCn_lt k (by omega)
          have h2 := (hper k (by omega)).1
          have : (2 : ℕ) ^ V.Wf k ≤ 2 ^ V.Wmax := Nat.pow_le_pow_right (by norm_num) h2
          omega
      have hOFFe_le : ∀ k, k < G → OFFe k ≤ V.OFFmax := by
        intro k hk
        by_cases hktop : k = G - 1
        · simp only [hOFFe, if_pos hktop]; omega
        · simp only [hOFFe, if_neg hktop]
          exact (hper k (by omega)).2.1
      have hPn_lt : ∀ k, Pn k < V.Nf k := by
        intro k; simp only [hPn]; split
        · rename_i h; exact h_assumptions.1 ⟨k, h⟩
        · exact hNf1 k
      have hSn_lt : ∀ k, Sn k < V.Nf k := by
        intro k; simp only [hSn]; split
        · rename_i h; exact h_assumptions.2 ⟨k, h⟩
        · exact hNf1 k
      have hPn_lt_max : ∀ k, Pn k < V.Nmax := by
        intro k; simp only [hPn]; split
        · rename_i h
          exact lt_of_lt_of_le (h_assumptions.1 ⟨k, h⟩) (hNcap k h)
        · exact lt_of_lt_of_le (hNf1 0) (hNcap 0 (by omega))
      have hSn_lt_max : ∀ k, Sn k < V.Nmax := by
        intro k; simp only [hSn]; split
        · rename_i h
          exact lt_of_lt_of_le (h_assumptions.2 ⟨k, h⟩) (hNcap k h)
        · exact lt_of_lt_of_le (hNf1 0) (hNcap 0 (by omega))
      -- group digit bound X₂ (uniform cap)
      set X2 : ℕ := V.Nmax * 2 ^ (B * (g - 1)) * 2 with hX2
      have hgeo := geom_sum_le B hB1 g hg1
      have hQP_lt : ∀ j, QP j < X2 := by
        intro j
        have hle : QP j ≤ (V.Nmax - 1) * ∑ i ∈ Finset.range g, 2 ^ (B * i) := by
          rw [hQP_app, Finset.mul_sum]
          apply Finset.sum_le_sum
          intro i _
          have := hPn_lt_max (g * j + i)
          exact Nat.mul_le_mul_right _ (by omega)
        have hNmax_pos : 0 < V.Nmax := lt_of_le_of_lt (Nat.zero_le _) (hPn_lt_max 0)
        calc QP j ≤ (V.Nmax - 1) * ∑ i ∈ Finset.range g, 2 ^ (B * i) := hle
          _ ≤ (V.Nmax - 1) * (2 ^ (B * (g - 1)) * 2) := Nat.mul_le_mul_left _ hgeo
          _ < V.Nmax * (2 ^ (B * (g - 1)) * 2) := by
              refine (Nat.mul_lt_mul_right (by positivity)).mpr ?_
              omega
          _ = X2 := by rw [hX2]; ring
      have hQS_lt : ∀ j, QS j < X2 := by
        intro j
        have hle : QS j ≤ (V.Nmax - 1) * ∑ i ∈ Finset.range g, 2 ^ (B * i) := by
          rw [hQS_app, Finset.mul_sum]
          apply Finset.sum_le_sum
          intro i _
          have := hSn_lt_max (g * j + i)
          exact Nat.mul_le_mul_right _ (by omega)
        have hNmax_pos : 0 < V.Nmax := lt_of_le_of_lt (Nat.zero_le _) (hSn_lt_max 0)
        calc QS j ≤ (V.Nmax - 1) * ∑ i ∈ Finset.range g, 2 ^ (B * i) := hle
          _ ≤ (V.Nmax - 1) * (2 ^ (B * (g - 1)) * 2) := Nat.mul_le_mul_left _ hgeo
          _ < V.Nmax * (2 ^ (B * (g - 1)) * 2) := by
              refine (Nat.mul_lt_mul_right (by positivity)).mpr ?_
              omega
          _ = X2 := by rw [hX2]; ring
      have hX2_lt_p : X2 < p :=
        lt_of_le_of_lt (le_trans (Nat.le_add_right _ _)
          (le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))) hnowrap
      have hBg_pos : (1 : ℕ) ≤ 2 ^ (B * g) := Nat.one_le_two_pow
      have hnowrap' : X2 + 2 ^ V.Wmax * 2 ^ (B * g) + V.OFFmax * 2 ^ (B * g) < p :=
        lt_of_le_of_lt (Nat.le_add_right _ _) hnowrap
      have hWmax_le_mul : 2 ^ V.Wmax ≤ 2 ^ V.Wmax * 2 ^ (B * g) :=
        Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
      have hOFFmax_le_mul : V.OFFmax ≤ V.OFFmax * 2 ^ (B * g) :=
        Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
      have hOFFmax_lt_p : V.OFFmax * 2 ^ (B * g) < p := by
        refine lt_of_le_of_lt ?_ hnowrap'
        omega
      have hOFFe_lt : ∀ k, k < G → OFFe k < p := fun k hk =>
        lt_of_le_of_lt (le_trans (hOFFe_le k hk)
          (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _))) hOFFmax_lt_p
      have hOFFe_cast : ∀ k, k < G → ((OFFe k : ℕ) : F p).val = OFFe k :=
        fun k hk => ZMod.val_natCast_of_lt (hOFFe_lt k hk)
      -- eval bridges
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
      have hcarry_eval : ∀ k, k < G - 1 →
          Expression.eval env (carryExpr B g V.OFFf input_var.lhs input_var.rhs k)
            = ((Cn k : ℕ) : F p) := by
        intro k hk
        simp only [hCn, if_neg (by omega : ¬ k = G - 1)]
        rw [ZMod.natCast_zmod_val]
      -- per-group ℕ equation
      have h_idx : ∀ k, (hk : k < G) →
          QP k + (if k = 0 then 0 else Cn (k - 1)) + OFFe k * 2 ^ (B * g)
            = QS k + Cn k * 2 ^ (B * g) + (if k = 0 then 0 else OFFe (k - 1)) := by
        intro k hk
        have hCk_lt_p : Cn k < p := by
          have := hCn_lt_max k hk
          omega
        have hCk_val : (((Cn k : ℕ) : F p)).val = Cn k := ZMod.val_natCast_of_lt hCk_lt_p
        have hCprev_lt_p : ∀ j, j < G → Cn j < p := by
          intro j hj
          have := hCn_lt_max j hj
          omega
        -- the field-level per-group equation
        have hfield : ((QP k : ℕ) : F p)
            + (if k = 0 then (0 : F p) else ((Cn (k - 1) : ℕ) : F p))
            + ((OFFe k : ℕ) : F p) * (2 ^ (B * g) : F p)
            = ((QS k : ℕ) : F p) + ((Cn k : ℕ) : F p) * (2 ^ (B * g) : F p)
              + (if k = 0 then (0 : F p) else ((OFFe (k - 1) : ℕ) : F p)) := by
          by_cases hktop : k = G - 1
          · -- the asserted final row
            subst hktop
            have hCktop : Cn (G - 1) = 0 := by simp [hCn]
            have hOFFtop : OFFe (G - 1) = 0 := by simp [hOFFe]
            rw [hCktop, hOFFtop]
            have hcin_eval : Expression.eval env
                (carryInExpr B g V.OFFf input_var.lhs input_var.rhs (G - 1))
                  = if G - 1 = 0 then (0 : F p)
                    else ((Cn (G - 1 - 1) : ℕ) : F p) - ((V.OFFf (G - 1 - 1) : ℕ) : F p) := by
              by_cases hk0 : G - 1 = 0
              · simp [carryInExpr, hk0, Expression.eval]
              · have hprev := hcarry_eval (G - 1 - 1) (by omega)
                simp [carryInExpr, hk0, Expression.eval, hprev, sub_eq_add_neg]
            have hlinF : ((QP (G - 1) : ℕ) : F p)
                  + (if G - 1 = 0 then (0 : F p)
                    else ((Cn (G - 1 - 1) : ℕ) : F p) - ((V.OFFf (G - 1 - 1) : ℕ) : F p))
                  + -((QS (G - 1) : ℕ) : F p) = 0 := by
              simpa [hGP_e, hGS_e, hcin_eval] using h_lin
            by_cases hk0 : G - 1 = 0
            · simp only [if_pos hk0] at hlinF ⊢
              rw [hk0] at hlinF ⊢
              simp only [Nat.cast_zero, zero_mul, add_zero] at hlinF ⊢
              linear_combination hlinF
            · simp only [if_neg hk0] at hlinF ⊢
              have hOFFprev : OFFe (G - 1 - 1) = V.OFFf (G - 1 - 1) := by
                simp only [hOFFe, if_neg (by omega : ¬ G - 1 - 1 = G - 1)]
              rw [hOFFprev]
              simp only [Nat.cast_zero, zero_mul, add_zero]
              linear_combination hlinF
          · -- an interior boundary: the range-checked carry expression solves the row
            have hOFFk : OFFe k = V.OFFf k := by simp only [hOFFe, if_neg hktop]
            rw [hOFFk]
            rcases Nat.eq_zero_or_pos k with hk0 | hkpos
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
              have hOFFj : OFFe j = V.OFFf j := by
                simp only [hOFFe, if_neg (by omega : ¬ j = G - 1)]
              simp only [if_neg (by omega : ¬ j + 1 = 0), Nat.succ_sub_one,
                hOFFj]
              rw [← hcarry]
              simp [carryExpr, Expression.eval, hGP_e, hGS_e, hprev]
              field_simp [hbase_ne]
              ring_nf
              try rw [hOFFj]
              try ring
        -- lift to ℕ
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
          ZMod.val_natCast_of_lt (lt_trans (hQP_lt k) hX2_lt_p)
        have hQSk_val : (((QS k : ℕ) : F p)).val = QS k :=
          ZMod.val_natCast_of_lt (lt_trans (hQS_lt k) hX2_lt_p)
        have hlhs : (((QP k : ℕ) : F p)).val + (if k = 0 then 0 else Cn (k - 1))
            + OFFe k * 2 ^ (B * g) < p := by
          rw [hQPk_val]
          have h1 := hQP_lt k
          have h2 : (if k = 0 then 0 else Cn (k - 1)) ≤ 2 ^ V.Wmax := by
            split
            · positivity
            · exact hCn_lt_max (k - 1) (by omega)
          have h3 : OFFe k * 2 ^ (B * g) ≤ V.OFFmax * 2 ^ (B * g) :=
            Nat.mul_le_mul_right _ (hOFFe_le k hk)
          omega
        have hrhs : (((QS k : ℕ) : F p)).val + (((Cn k : ℕ) : F p)).val * 2 ^ (B * g)
            + (if k = 0 then 0 else OFFe (k - 1)) < p := by
          rw [hQSk_val, hCk_val]
          have h1 := hQS_lt k
          have h2 : Cn k * 2 ^ (B * g) ≤ 2 ^ V.Wmax * 2 ^ (B * g) :=
            Nat.mul_le_mul_right _ (hCn_lt_max k hk)
          have h3 : (if k = 0 then 0 else OFFe (k - 1)) ≤ V.OFFmax := by
            split
            · positivity
            · exact hOFFe_le (k - 1) (by omega)
          omega
        have hlift := per_index_lift2 (B := B * g) ((QP k : ℕ) : F p)
          (if k = 0 then (0 : F p) else ((Cn (k - 1) : ℕ) : F p))
          ((QS k : ℕ) : F p) ((Cn k : ℕ) : F p)
          ((OFFe k : ℕ) : F p)
          (if k = 0 then (0 : F p) else ((OFFe (k - 1) : ℕ) : F p))
          (if k = 0 then 0 else Cn (k - 1)) (OFFe k) (if k = 0 then 0 else OFFe (k - 1))
          hpBg hcin_val (hOFFe_cast k hk) hoffR_val hlhs hrhs hfield
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
            ((QP k + (if k = 0 then 0 else Cn (k - 1))) + OFFe k * 2 ^ (B * g)) * 2 ^ (B * g * k))
          = ∑ k ∈ Finset.range G,
              (QS k + Cn k * 2 ^ (B * g) + (if k = 0 then 0 else OFFe (k - 1))) * 2 ^ (B * g * k) := by
        apply Finset.sum_congr rfl
        intro k hk; rw [Finset.mem_range] at hk
        rw [h_idx k hk]
      set SP := ∑ k ∈ Finset.range G, QP k * 2 ^ (B * g * k) with hSP
      set SS := ∑ k ∈ Finset.range G, QS k * 2 ^ (B * g * k) with hSS
      -- telescope both the carries and the offsets (their tops vanish)
      have htelC := carry_telescope (B * g) Cn G
      rw [if_neg (by omega : ¬ (G = 0)), show Cn (G - 1) = 0 from by simp [hCn],
        Nat.zero_mul, Nat.add_zero] at htelC
      have htelO := carry_telescope (B * g) OFFe G
      rw [if_neg (by omega : ¬ (G = 0)), show OFFe (G - 1) = 0 from by simp [hOFFe],
        Nat.zero_mul, Nat.add_zero] at htelO
      have hLHS : (∑ k ∈ Finset.range G,
            ((QP k + (if k = 0 then 0 else Cn (k - 1))) + OFFe k * 2 ^ (B * g)) * 2 ^ (B * g * k))
          = SP + (∑ k ∈ Finset.range G, (if k = 0 then 0 else Cn (k - 1)) * 2 ^ (B * g * k))
            + (∑ k ∈ Finset.range G, OFFe k * 2 ^ (B * g * (k + 1))) := by
        rw [hSP, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _
        rw [Nat.mul_add, Nat.mul_one, pow_add]
        ring
      have hRHS : (∑ k ∈ Finset.range G,
            (QS k + Cn k * 2 ^ (B * g) + (if k = 0 then 0 else OFFe (k - 1))) * 2 ^ (B * g * k))
          = SS + (∑ k ∈ Finset.range G, Cn k * 2 ^ (B * g * (k + 1)))
            + (∑ k ∈ Finset.range G, (if k = 0 then 0 else OFFe (k - 1)) * 2 ^ (B * g * k)) := by
        rw [hSS, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _
        rw [Nat.mul_add, Nat.mul_one, pow_add]
        ring
      have h1 := hLHS
      have h2 := hRHS
      refine And.intro (by omega) ?_
      exact carryLoop_requirements B g V.OFFf V.Wf hWok env
        input_var.lhs input_var.rhs _ _ _
    completeness := by
      obtain ⟨hg1, hpBg, hWmp, hWok, hNf1, hNcap, hper, hnowrap⟩ := hgv
      circuit_proof_start
      have hM : 0 < 2 * m - 1 := by have := Nat.pos_of_neZero m; omega
      have hG1 : 0 < numGroups m g := numGroups_pos m g hg1
      have hCov : 2 * m - 1 ≤ g * numGroups m g := numGroups_mul_ge m g hg1
      set G := numGroups m g with hGdef
      -- coefficient digit functions
      set Pn : ℕ → ℕ := fun k => if h : k < 2 * m - 1 then (input.lhs[k]'h).val else 0 with hPn
      set Sn : ℕ → ℕ := fun k => if h : k < 2 * m - 1 then (input.rhs[k]'h).val else 0 with hSn
      have hPn_lt : ∀ k, Pn k < V.Nf k := by
        intro k; simp only [hPn]; split
        · rename_i h; exact h_assumptions.1 ⟨k, h⟩
        · exact hNf1 k
      have hSn_lt : ∀ k, Sn k < V.Nf k := by
        intro k; simp only [hSn]; split
        · rename_i h; exact h_assumptions.2 ⟨k, h⟩
        · exact hNf1 k
      -- group digits
      set QP : ℕ → ℕ := fun j => ∑ i ∈ Finset.range g, Pn (g * j + i) * 2 ^ (B * i) with hQP
      set QS : ℕ → ℕ := fun j => ∑ i ∈ Finset.range g, Sn (g * j + i) * 2 ^ (B * i) with hQS
      have hQP_app : ∀ j, QP j = ∑ i ∈ Finset.range g, Pn (g * j + i) * 2 ^ (B * i) :=
        fun _ => rfl
      have hQS_app : ∀ j, QS j = ∑ i ∈ Finset.range g, Sn (g * j + i) * 2 ^ (B * i) :=
        fun _ => rfl
      -- group-level partial sums and carries (with per-boundary offsets)
      set PFn : ℕ → ℕ := fun k => ∑ j ∈ Finset.range (k + 1), QP j * 2 ^ (B * g * j) with hPFn
      set PSn : ℕ → ℕ := fun k => ∑ j ∈ Finset.range (k + 1), QS j * 2 ^ (B * g * j) with hPSn
      set Dk : ℕ → ℕ := fun k => 2 ^ (B * g * (k + 1)) with hDk
      set Cn : ℕ → ℕ := fun k => V.OFFf k + PFn k / Dk k - PSn k / Dk k with hCn
      have hDk_app : ∀ k, Dk k = 2 ^ (B * g * (k + 1)) := fun _ => rfl
      have hPFn_app : ∀ k, PFn k = ∑ j ∈ Finset.range (k + 1), QP j * 2 ^ (B * g * j) :=
        fun _ => rfl
      have hPSn_app : ∀ k, PSn k = ∑ j ∈ Finset.range (k + 1), QS j * 2 ^ (B * g * j) :=
        fun _ => rfl
      have hCn_app : ∀ k, Cn k = V.OFFf k + PFn k / Dk k - PSn k / Dk k := fun _ => rfl
      -- eval bridges
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
      -- prefix-quotient bounds from the recursive offsets
      have hOFFrec : ∀ k, k < G - 1 →
          (if k = 0 then 0 else V.OFFf (k - 1)) + 1
              + (∑ i ∈ Finset.range g, (V.Nf (g * k + i) - 1) * 2 ^ (B * i))
            ≤ (V.OFFf k + 1) * 2 ^ (B * g) :=
        fun k hk => (hper k hk).2.2.2
      have hPFdiv : ∀ k, k < G - 1 → PFn k / Dk k ≤ V.OFFf k := by
        intro k hk
        have h1 := prefix_div_le B g V (G - 1) hOFFrec Pn hPn_lt k hk
        rw [hPFn_app, hDk_app]
        exact Nat.lt_succ_iff.mp (Nat.div_lt_of_lt_mul (by
          calc (∑ j ∈ Finset.range (k + 1), QP j * 2 ^ (B * g * j))
              < (V.OFFf k + 1) * 2 ^ (B * g * (k + 1)) := h1
            _ = 2 ^ (B * g * (k + 1)) * (V.OFFf k + 1) := by ring))
      have hPSdiv : ∀ k, k < G - 1 → PSn k / Dk k ≤ V.OFFf k := by
        intro k hk
        have h1 := prefix_div_le B g V (G - 1) hOFFrec Sn hSn_lt k hk
        rw [hPSn_app, hDk_app]
        exact Nat.lt_succ_iff.mp (Nat.div_lt_of_lt_mul (by
          calc (∑ j ∈ Finset.range (k + 1), QS j * 2 ^ (B * g * j))
              < (V.OFFf k + 1) * 2 ^ (B * g * (k + 1)) := h1
            _ = 2 ^ (B * g * (k + 1)) * (V.OFFf k + 1) := by ring))
      have hrange : ∀ k, k < G - 1 → Cn k < 2 ^ V.Wf k := by
        intro k hk
        have h1 := hPFdiv k hk
        have h2 := (hper k hk).2.2.1
        rw [hCn_app]
        calc V.OFFf k + PFn k / Dk k - PSn k / Dk k
            ≤ V.OFFf k + PFn k / Dk k := Nat.sub_le _ _
          _ ≤ V.OFFf k + V.OFFf k := by omega
          _ < 2 ^ V.Wf k := by omega
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
      -- per-group ℕ equation for the honest carries
      have hidx : ∀ k, k < G →
          QP k + (if k = 0 then 0 else Cn (k - 1)) + V.OFFf k * 2 ^ (B * g)
            = QS k + Cn k * 2 ^ (B * g) + (if k = 0 then 0 else V.OFFf (k - 1)) := by
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
        have hCnk : Cn k = V.OFFf k + rP - rS := by rw [hCn_app, ← hrP_def, ← hrS_def]
        -- `rS ≤ OFFf k + rP` via the shared residue and (interior) quotient bound
        have hrS_le : rS ≤ V.OFFf k + rP := by
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
        have hmulCnk : Cn k * 2 ^ (B * g) = V.OFFf k * 2 ^ (B * g) + rP * 2 ^ (B * g)
            - rS * 2 ^ (B * g) := by
          rw [hCnk, Nat.sub_mul, Nat.add_mul]
        rcases Nat.eq_zero_or_pos k with hk0 | hk0
        · subst hk0
          rw [hmulCnk]
          simp only [↓reduceIte] at hstepP hstepS ⊢
          rw [Nat.add_zero] at hstepP hstepS
          have hrPmul : rS * 2 ^ (B * g) ≤ rP * 2 ^ (B * g) + V.OFFf 0 * 2 ^ (B * g) := by
            have hle : rS ≤ rP + V.OFFf 0 := by omega
            calc rS * 2 ^ (B * g) ≤ (rP + V.OFFf 0) * 2 ^ (B * g) := Nat.mul_le_mul_right _ hle
              _ = rP * 2 ^ (B * g) + V.OFFf 0 * 2 ^ (B * g) := by rw [Nat.add_mul]
          omega
        · rw [if_neg (by omega : ¬ k = 0), if_neg (by omega : ¬ k = 0), hmulCnk]
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
          have hCnprev : Cn (k - 1) = V.OFFf (k - 1) + rP' - rS' := hCn_app (k - 1)
          -- `rS' ≤ OFFf (k−1) + rP'` (same argument at the previous boundary)
          have hrSprev_le : rS' ≤ V.OFFf (k - 1) + rP' := by
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
          have hrPmul : rS * 2 ^ (B * g) ≤ rP * 2 ^ (B * g) + V.OFFf k * 2 ^ (B * g) := by
            have hle : rS ≤ rP + V.OFFf k := by omega
            calc rS * 2 ^ (B * g) ≤ (rP + V.OFFf k) * 2 ^ (B * g) := Nat.mul_le_mul_right _ hle
              _ = rP * 2 ^ (B * g) + V.OFFf k * 2 ^ (B * g) := by rw [Nat.add_mul]
          omega
      -- group value bounds for the field casts
      have hNmax_pos : 0 < V.Nmax :=
        lt_of_lt_of_le (hNf1 0) (hNcap 0 (by omega))
      set X2 : ℕ := V.Nmax * 2 ^ (B * (g - 1)) * 2 with hX2
      have hgeo := geom_sum_le B hB1 g hg1
      have hPn_lt_max : ∀ k, Pn k < V.Nmax := by
        intro k; simp only [hPn]; split
        · rename_i h
          exact lt_of_lt_of_le (h_assumptions.1 ⟨k, h⟩) (hNcap k h)
        · exact hNmax_pos
      have hSn_lt_max : ∀ k, Sn k < V.Nmax := by
        intro k; simp only [hSn]; split
        · rename_i h
          exact lt_of_lt_of_le (h_assumptions.2 ⟨k, h⟩) (hNcap k h)
        · exact hNmax_pos
      have hQP_lt : ∀ j, QP j < X2 := by
        intro j
        have hle : QP j ≤ (V.Nmax - 1) * ∑ i ∈ Finset.range g, 2 ^ (B * i) := by
          rw [hQP_app, Finset.mul_sum]
          apply Finset.sum_le_sum
          intro i _
          have := hPn_lt_max (g * j + i)
          exact Nat.mul_le_mul_right _ (by omega)
        calc QP j ≤ (V.Nmax - 1) * ∑ i ∈ Finset.range g, 2 ^ (B * i) := hle
          _ ≤ (V.Nmax - 1) * (2 ^ (B * (g - 1)) * 2) := Nat.mul_le_mul_left _ hgeo
          _ < V.Nmax * (2 ^ (B * (g - 1)) * 2) := by
              refine (Nat.mul_lt_mul_right (by positivity)).mpr ?_
              omega
          _ = X2 := by rw [hX2]; ring
      have hQS_lt : ∀ j, QS j < X2 := by
        intro j
        have hle : QS j ≤ (V.Nmax - 1) * ∑ i ∈ Finset.range g, 2 ^ (B * i) := by
          rw [hQS_app, Finset.mul_sum]
          apply Finset.sum_le_sum
          intro i _
          have := hSn_lt_max (g * j + i)
          exact Nat.mul_le_mul_right _ (by omega)
        calc QS j ≤ (V.Nmax - 1) * ∑ i ∈ Finset.range g, 2 ^ (B * i) := hle
          _ ≤ (V.Nmax - 1) * (2 ^ (B * (g - 1)) * 2) := Nat.mul_le_mul_left _ hgeo
          _ < V.Nmax * (2 ^ (B * (g - 1)) * 2) := by
              refine (Nat.mul_lt_mul_right (by positivity)).mpr ?_
              omega
          _ = X2 := by rw [hX2]; ring
      have hX2_lt_p : X2 < p :=
        lt_of_le_of_lt (le_trans (Nat.le_add_right _ _)
          (le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))) hnowrap
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
          Expression.eval env.toEnvironment (carryExpr B g V.OFFf input_var.lhs input_var.rhs k)
            = ((Cn k : ℕ) : F p) := by
        intro k hk
        induction k with
        | zero =>
            have hnatk := hidx 0 (by omega)
            simp only [↓reduceIte] at hnatk
            have hcast := congrArg (Nat.cast : ℕ → F p) hnatk
            push_cast [hpow_cast] at hcast
            simp [carryExpr, Expression.eval, hGP_e, hGS_e]
            field_simp [hbase_ne]
            linear_combination hcast
        | succ j ih =>
            have hprev := ih (by omega)
            have hnatk := hidx (j + 1) (by omega)
            simp only [if_neg (by omega : ¬ j + 1 = 0), Nat.add_sub_cancel] at hnatk
            have hcast := congrArg (Nat.cast : ℕ → F p) hnatk
            push_cast [hpow_cast] at hcast
            simp [carryExpr, Expression.eval, hGP_e, hGS_e, hprev]
            field_simp [hbase_ne]
            linear_combination hcast
      refine ⟨?_, ?_⟩
      · -- the loop's range checks
        refine carryLoop_completeness B g V.OFFf V.Wf hWok env
          input_var.lhs input_var.rhs (G - 1) 0 i₀ fun i hi => ?_
        rw [Nat.zero_add, hcarry_eval i hi,
          ZMod.val_natCast_of_lt (lt_trans (hrange i hi)
            (lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) (hper i hi).1) hWmp))]
        exact hrange i hi
      · -- final group field equation
        try simp only [circuit_norm]
        rw [show numGroups m g = G from hGdef.symm]
        have hnatk := hidx (G - 1) (by omega)
        -- at the top, Cn (G−1) = OFFf (G−1) since the tops agree
        have hCtop : Cn (G - 1) = V.OFFf (G - 1) := by
          rw [hCn_app, hPtop_eq]; omega
        rw [hCtop] at hnatk
        have hcast := congrArg (Nat.cast : ℕ → F p) hnatk
        push_cast [hpow_cast] at hcast
        by_cases hlast0 : G - 1 = 0
        · simp only [hlast0, ↓reduceIte] at hcast
          simp [carryInExpr, hlast0, Expression.eval, hGP_e, hGS_e]
          linear_combination hcast
        · have hprev := hcarry_eval (G - 1 - 1) (by omega)
          have hcin_eval : Expression.eval env.toEnvironment
              (carryInExpr B g V.OFFf input_var.lhs input_var.rhs (G - 1))
                = ((Cn (G - 1 - 1) : ℕ) : F p) - ((V.OFFf (G - 1 - 1) : ℕ) : F p) := by
            simp [carryInExpr, hlast0, Expression.eval, hprev, sub_eq_add_neg]
          simp only [circuit_norm, hGP_e, hGS_e, hcin_eval]
          simp only [if_neg hlast0] at hcast
          linear_combination hcast


lemma circuit_assumptions_eq (B g : ℕ) (V : VParams) (hgv : GVHyps p m B g V) (hB1 : 1 ≤ B)
    [Fact (p > 2)] :
    (circuit (m := m) B g V hgv hB1).Assumptions = Assumptions V.Nf := rfl


lemma circuit_spec_eq (B g : ℕ) (V : VParams) (hgv : GVHyps p m B g V) (hB1 : 1 ≤ B)
    [Fact (p > 2)] :
    (circuit (m := m) B g V hgv hB1).Spec = EqViaCarries.Spec B := rfl


lemma circuit_channels_req_eq (B g : ℕ) (V : VParams) (hgv : GVHyps p m B g V) (hB1 : 1 ≤ B)
    [Fact (p > 2)] :
    (circuit (m := m) B g V hgv hB1).channelsWithRequirements = [] := rfl




lemma val_bigIntMulNoReduce_coeff_le_pos {B : ℕ} (env : Environment (F p))
    (a b : Var (BigInt m) (F p)) (k : Fin (2 * m - 1))
    (ha : ∀ i : Fin m, (Expression.eval env a[i.val]).val < 2 ^ B)
    (hb : ∀ i : Fin m, (Expression.eval env b[i.val]).val < 2 ^ B)
    (hbound : m * (2 ^ B * 2 ^ B) < p) :
    (Expression.eval env ((bigIntMulNoReduce a b)[k.val])).val
      ≤ min (k.val + 1) (2 * m - 1 - k.val) * ((2 ^ B - 1) * (2 ^ B - 1)) := by
  rw [val_bigIntMulNoReduce_coeff env a b k ha hb hbound]
  set C := (2 ^ B - 1) * (2 ^ B - 1) with hC
  set S : Finset (Fin m) :=
    Finset.univ.filter (fun i : Fin m => i.val ≤ k.val ∧ k.val - i.val < m) with hS
  -- termwise: each guarded product is at most the guarded constant `C`
  have hsum_le : (∑ i : Fin m, if h : i.val ≤ k.val ∧ k.val - i.val < m then
      (Expression.eval env a[i.val]).val
        * (Expression.eval env (b[k.val - i.val]'h.2)).val else 0)
      ≤ ∑ i : Fin m, (if i.val ≤ k.val ∧ k.val - i.val < m then C else 0) := by
    apply Finset.sum_le_sum
    intro i _
    by_cases h : i.val ≤ k.val ∧ k.val - i.val < m
    · rw [dif_pos h, if_pos h, hC]
      have h1 := ha i
      have h2 : (Expression.eval env (b[k.val - i.val]'h.2)).val < 2 ^ B :=
        hb ⟨k.val - i.val, h.2⟩
      exact Nat.mul_le_mul (by omega) (by omega)
    · rw [dif_neg h, if_neg h]
  -- the guarded-constant sum is `card · C`
  have hsum_filter : (∑ i : Fin m, (if i.val ≤ k.val ∧ k.val - i.val < m then C else 0))
      = S.card * C := by
    rw [hS, ← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
  -- window cardinality bounds
  have hmemS : ∀ i : Fin m, i ∈ S → i.val ≤ k.val ∧ k.val - i.val < m := by
    intro i hi
    rw [hS, Finset.mem_filter] at hi
    exact hi.2
  have hcard1 : S.card ≤ k.val + 1 := by
    have h := Finset.card_le_card_of_injOn (s := S) (t := Finset.range (k.val + 1))
      (fun i : Fin m => i.val)
      (fun i hi => Finset.mem_range.mpr (by
        have := (hmemS i hi).1
        show i.val < k.val + 1
        omega))
      (fun x hx y hy hxy => Fin.ext hxy)
    simpa using h
  have hcard2 : S.card ≤ 2 * m - 1 - k.val := by
    have hklt : k.val < 2 * m - 1 := k.isLt
    have h := Finset.card_le_card_of_injOn (s := S) (t := Finset.range (2 * m - 1 - k.val))
      (fun i : Fin m => i.val - (k.val + 1 - m))
      (fun i hi => Finset.mem_range.mpr (by
        have h2 := (hmemS i hi).2
        have h3 := i.isLt
        show i.val - (k.val + 1 - m) < 2 * m - 1 - k.val
        omega))
      (fun x hx y hy hxy => by
        have hxy' : x.val - (k.val + 1 - m) = y.val - (k.val + 1 - m) := hxy
        have hx2 := (hmemS x (Finset.mem_coe.mp hx)).2
        have hy2 := (hmemS y (Finset.mem_coe.mp hy)).2
        have hx3 := x.isLt
        have hy3 := y.isLt
        exact Fin.ext (by omega))
    simpa using h
  have hcard : S.card ≤ min (k.val + 1) (2 * m - 1 - k.val) :=
    le_min hcard1 hcard2
  calc (∑ i : Fin m, if h : i.val ≤ k.val ∧ k.val - i.val < m then
        (Expression.eval env a[i.val]).val
          * (Expression.eval env (b[k.val - i.val]'h.2)).val else 0)
      ≤ S.card * C := by rw [← hsum_filter]; exact hsum_le
    _ ≤ min (k.val + 1) (2 * m - 1 - k.val) * C := Nat.mul_le_mul_right _ hcard




lemma top_limb_lt_of_value_lt {B tb : ℕ} {x : BigInt m (F p)}
    (hv : BigInt.value B x < 2 ^ ((m - 1) * B + tb)) :
    (x[m - 1]'(by have := Nat.pos_of_neZero m; omega)).val < 2 ^ tb := by
  have hm := Nat.pos_of_neZero m
  have hi1m : m - 1 < m := by omega
  by_contra hcon
  push_neg at hcon
  have hterm : 2 ^ tb * 2 ^ (B * (m - 1)) ≤ BigInt.value B x := by
    rw [BigInt.value_eq_sum]
    calc 2 ^ tb * 2 ^ (B * (m - 1))
        ≤ (x[((⟨m - 1, hi1m⟩ : Fin m) : Fin m)]).val
            * 2 ^ (B * ((⟨m - 1, hi1m⟩ : Fin m) : Fin m).val) := by
          exact Nat.mul_le_mul_right _ hcon
      _ ≤ ∑ k : Fin m, (x[k]).val * 2 ^ (B * k.val) :=
          Finset.single_le_sum (f := fun k : Fin m => (x[k]).val * 2 ^ (B * k.val))
            (fun i _ => Nat.zero_le _) (Finset.mem_univ (⟨m - 1, hi1m⟩ : Fin m))
  rw [show (m - 1) * B + tb = tb + B * (m - 1) from by ring_nf, pow_add] at hv
  omega


lemma val_bigIntMulNoReduce_coeff_le_weighted2 {B : ℕ} (env : Environment (F p))
    (a b : Var (BigInt m) (F p)) (k : Fin (2 * m - 1)) (t s : ℕ → ℕ)
    (ha : ∀ i : Fin m, (Expression.eval env a[i.val]).val < 2 ^ B)
    (hb : ∀ i : Fin m, (Expression.eval env b[i.val]).val < 2 ^ B)
    (hat : ∀ i : Fin m, (Expression.eval env a[i.val]).val ≤ t i.val)
    (hbt : ∀ i : Fin m, (Expression.eval env b[i.val]).val ≤ s i.val)
    (hbound : m * (2 ^ B * 2 ^ B) < p) :
    (Expression.eval env ((bigIntMulNoReduce a b)[k.val])).val
      ≤ ∑ i : Fin m, if i.val ≤ k.val ∧ k.val - i.val < m then
          t i.val * s (k.val - i.val) else 0 := by
  rw [val_bigIntMulNoReduce_coeff env a b k ha hb hbound]
  apply Finset.sum_le_sum
  intro i _
  by_cases h : i.val ≤ k.val ∧ k.val - i.val < m
  · rw [dif_pos h, if_pos h]
    exact Nat.mul_le_mul (hat i) (hbt ⟨k.val - i.val, h.2⟩)
  · rw [dif_neg h, if_neg h]


lemma topwindow_sum_le (B ta tb' k : ℕ)
    (hta : 2 ^ ta - 1 ≤ 2 ^ B - 1) (htb : 2 ^ tb' - 1 ≤ 2 ^ B - 1)
    (hk1 : m - 1 ≤ k) (hk2 : k < 2 * m - 1) :
    (∑ i : Fin m, if i.val ≤ k ∧ k - i.val < m then
        (if i.val = m - 1 then 2 ^ ta - 1 else 2 ^ B - 1)
          * (if k - i.val = m - 1 then 2 ^ tb' - 1 else 2 ^ B - 1) else 0)
      ≤ (2 * m - 3 - k) * ((2 ^ B - 1) * (2 ^ B - 1))
        + (2 ^ ta - 1) * (2 ^ B - 1) + (2 ^ tb' - 1) * (2 ^ B - 1) := by
  classical
  have hm := Nat.pos_of_neZero m
  have hi1m : m - 1 < m := by omega
  set L := 2 ^ B - 1 with hL
  set Ta := 2 ^ ta - 1 with hTa
  set Tb := 2 ^ tb' - 1 with hTb
  set f : Fin m → ℕ := fun i => if i.val ≤ k ∧ k - i.val < m then
      (if i.val = m - 1 then Ta else L) * (if k - i.val = m - 1 then Tb else L) else 0
    with hf
  set i1 : Fin m := ⟨m - 1, hi1m⟩ with hi1def
  have hsplit1 : (∑ i : Fin m, f i)
      = f i1 + ∑ i ∈ Finset.univ.erase i1, f i :=
    (Finset.add_sum_erase _ f (Finset.mem_univ i1)).symm
  have hf1 : f i1 ≤ Ta * L := by
    have hfe : f i1 = (if m - 1 ≤ k ∧ k - (m - 1) < m then
        (if m - 1 = m - 1 then Ta else L)
          * (if k - (m - 1) = m - 1 then Tb else L) else 0) := rfl
    rw [hfe, if_pos (⟨hk1, by omega⟩ : m - 1 ≤ k ∧ k - (m - 1) < m), if_pos rfl]
    by_cases h2 : k - (m - 1) = m - 1
    · rw [if_pos h2]; exact Nat.mul_le_mul_left _ htb
    · rw [if_neg h2]
  by_cases hk3 : k = 2 * m - 2
  · -- single-element window: only `i = m−1` qualifies
    have hrest0 : (∑ i ∈ Finset.univ.erase i1, f i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hne : i ≠ i1 := (Finset.mem_erase.mp hi).1
      have hng : ¬(i.val ≤ k ∧ k - i.val < m) := by
        intro hcon
        exact hne (Fin.ext (by have := i.isLt; show i.val = i1.val; show i.val = m - 1; omega))
      have hfe : f i = (if i.val ≤ k ∧ k - i.val < m then
          (if i.val = m - 1 then Ta else L)
            * (if k - i.val = m - 1 then Tb else L) else 0) := rfl
      rw [hfe, if_neg hng]
    rw [hsplit1, hrest0, Nat.add_zero]
    exact le_trans hf1 (le_trans (Nat.le_add_left _ _) (Nat.le_add_right _ _))
  · have hkm : k ≤ 2 * m - 3 := by omega
    have hi2m : k - (m - 1) < m := by omega
    set i2 : Fin m := ⟨k - (m - 1), hi2m⟩ with hi2def
    have hne12 : i2 ≠ i1 := by
      intro hcon
      have h12 : k - (m - 1) = m - 1 := congrArg Fin.val hcon
      omega
    have hi2mem : i2 ∈ Finset.univ.erase i1 := Finset.mem_erase.mpr ⟨hne12, Finset.mem_univ _⟩
    have hsplit2 : (∑ i ∈ Finset.univ.erase i1, f i)
        = f i2 + ∑ i ∈ (Finset.univ.erase i1).erase i2, f i :=
      (Finset.add_sum_erase _ f hi2mem).symm
    have hf2 : f i2 ≤ Tb * L := by
      have hfe : f i2 = (if k - (m - 1) ≤ k ∧ k - (k - (m - 1)) < m then
          (if k - (m - 1) = m - 1 then Ta else L)
            * (if k - (k - (m - 1)) = m - 1 then Tb else L) else 0) := rfl
      rw [hfe, if_pos (⟨by omega, by omega⟩ : k - (m - 1) ≤ k ∧ k - (k - (m - 1)) < m),
        if_neg (show ¬(k - (m - 1) = m - 1) from by omega),
        if_pos (show k - (k - (m - 1)) = m - 1 from by omega)]
      exact le_of_eq (Nat.mul_comm L Tb)
    -- remaining terms: at most `2m−3−k` full-width products
    have hrest : (∑ i ∈ (Finset.univ.erase i1).erase i2, f i)
        ≤ (2 * m - 3 - k) * (L * L) := by
      have hterm : ∀ i ∈ (Finset.univ.erase i1).erase i2,
          f i ≤ (if i.val ≤ k ∧ k - i.val < m then L * L else 0) := by
        intro i hi
        obtain ⟨hne2, hi'⟩ := Finset.mem_erase.mp hi
        obtain ⟨hne1, -⟩ := Finset.mem_erase.mp hi'
        have hfe : f i = (if i.val ≤ k ∧ k - i.val < m then
            (if i.val = m - 1 then Ta else L)
              * (if k - i.val = m - 1 then Tb else L) else 0) := rfl
        rw [hfe]
        by_cases hg : i.val ≤ k ∧ k - i.val < m
        · rw [if_pos hg, if_pos hg]
          have hv1 : ¬(i.val = m - 1) := fun hcon => hne1 (Fin.ext hcon)
          have hv2 : ¬(k - i.val = m - 1) := by
            intro hcon
            exact hne2 (Fin.ext (show i.val = k - (m - 1) from by omega))
          rw [if_neg hv1, if_neg hv2]
        · rw [if_neg hg, if_neg hg]
      have hmono := Finset.sum_le_sum hterm
      have hcount : (∑ i ∈ (Finset.univ.erase i1).erase i2,
            (if i.val ≤ k ∧ k - i.val < m then L * L else 0))
          = (((Finset.univ.erase i1).erase i2).filter
              (fun i : Fin m => i.val ≤ k ∧ k - i.val < m)).card * (L * L) := by
        rw [Finset.sum_ite, Finset.sum_const_zero, Nat.add_zero, Finset.sum_const,
          smul_eq_mul]
      have hcard : (((Finset.univ.erase i1).erase i2).filter
            (fun i : Fin m => i.val ≤ k ∧ k - i.val < m)).card ≤ 2 * m - 3 - k := by
        have hinj := Finset.card_le_card_of_injOn
          (s := ((Finset.univ.erase i1).erase i2).filter
            (fun i : Fin m => i.val ≤ k ∧ k - i.val < m))
          (t := Finset.range (2 * m - 3 - k))
          (fun i : Fin m => i.val - (k - (m - 1) + 1))
          (fun i hi => by
            simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_erase,
              Finset.mem_univ, and_true] at hi
            obtain ⟨⟨hne2, hne1⟩, hg1, hg2⟩ := hi
            have hv1 : i.val ≠ m - 1 := fun hcon => hne1 (Fin.ext hcon)
            have hv2 : i.val ≠ k - (m - 1) := fun hcon => hne2 (Fin.ext hcon)
            have hilt := i.isLt
            refine Finset.mem_coe.mpr (Finset.mem_range.mpr ?_)
            show i.val - (k - (m - 1) + 1) < 2 * m - 3 - k
            omega)
          (fun x hx y hy hxy => by
            simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_erase,
              Finset.mem_univ, and_true] at hx hy
            obtain ⟨⟨hxne2, -⟩, hxg1, hxg2⟩ := hx
            obtain ⟨⟨hyne2, -⟩, hyg1, hyg2⟩ := hy
            have hxv2 : x.val ≠ k - (m - 1) := fun hcon => hxne2 (Fin.ext hcon)
            have hyv2 : y.val ≠ k - (m - 1) := fun hcon => hyne2 (Fin.ext hcon)
            have hxy' : x.val - (k - (m - 1) + 1) = y.val - (k - (m - 1) + 1) := hxy
            exact Fin.ext (by omega))
        simpa using hinj
      calc (∑ i ∈ (Finset.univ.erase i1).erase i2, f i)
          ≤ (((Finset.univ.erase i1).erase i2).filter
              (fun i : Fin m => i.val ≤ k ∧ k - i.val < m)).card * (L * L) := by
            rw [← hcount]; exact hmono
        _ ≤ (2 * m - 3 - k) * (L * L) := Nat.mul_le_mul_right _ hcard
    rw [hsplit1, hsplit2]
    exact le_trans (Nat.add_le_add hf1 (Nat.add_le_add hf2 hrest))
      (le_of_eq (by ring))


lemma val_bigIntMulNoReduce_coeff_le_top {B ta tb' : ℕ} (env : Environment (F p))
    (a b : Var (BigInt m) (F p)) (k : Fin (2 * m - 1))
    (ha : ∀ i : Fin m, (Expression.eval env a[i.val]).val < 2 ^ B)
    (hb : ∀ i : Fin m, (Expression.eval env b[i.val]).val < 2 ^ B)
    (hatop : (Expression.eval env (a[m - 1]'(by have := Nat.pos_of_neZero m; omega))).val < 2 ^ ta)
    (hbtop : (Expression.eval env (b[m - 1]'(by have := Nat.pos_of_neZero m; omega))).val < 2 ^ tb')
    (htaB : ta ≤ B) (htbB : tb' ≤ B) (hk : m - 1 ≤ k.val)
    (hbound : m * (2 ^ B * 2 ^ B) < p) :
    (Expression.eval env ((bigIntMulNoReduce a b)[k.val])).val
      ≤ (2 * m - 3 - k.val) * ((2 ^ B - 1) * (2 ^ B - 1))
        + (2 ^ ta - 1) * (2 ^ B - 1) + (2 ^ tb' - 1) * (2 ^ B - 1) := by
  have hm := Nat.pos_of_neZero m
  have hw2 := val_bigIntMulNoReduce_coeff_le_weighted2 env a b k
    (fun i => if i = m - 1 then 2 ^ ta - 1 else 2 ^ B - 1)
    (fun j => if j = m - 1 then 2 ^ tb' - 1 else 2 ^ B - 1)
    ha hb
    (fun i => by
      show (Expression.eval env a[i.val]).val
        ≤ if i.val = m - 1 then 2 ^ ta - 1 else 2 ^ B - 1
      by_cases hi : i.val = m - 1
      · rw [if_pos hi]
        have hieq : i = ⟨m - 1, by omega⟩ := Fin.ext hi
        rw [hieq]
        exact Nat.le_pred_of_lt hatop
      · rw [if_neg hi]
        exact Nat.le_pred_of_lt (ha i))
    (fun i => by
      show (Expression.eval env b[i.val]).val
        ≤ if i.val = m - 1 then 2 ^ tb' - 1 else 2 ^ B - 1
      by_cases hi : i.val = m - 1
      · rw [if_pos hi]
        have hieq : i = ⟨m - 1, by omega⟩ := Fin.ext hi
        rw [hieq]
        exact Nat.le_pred_of_lt hbtop
      · rw [if_neg hi]
        exact Nat.le_pred_of_lt (hb i))
    hbound
  refine le_trans hw2 (topwindow_sum_le B ta tb' k.val ?_ ?_ hk k.isLt)
  · exact Nat.sub_le_sub_right (Nat.pow_le_pow_right (by norm_num) htaB) 1
  · exact Nat.sub_le_sub_right (Nat.pow_le_pow_right (by norm_num) htbB) 1

end GroupedEqV

end

end Solution.Secp256k1ScalarMul
