import Solution.Secp256k1ScalarMul.GroupedEq
import Solution.Secp256k1ScalarMul.GroupedEqX
import Solution.Secp256k1ScalarMul.GroupedEqV
import Solution.Secp256k1ScalarMul.RangeCheck



namespace Solution.Secp256k1ScalarMul

section
variable {p : ℕ} [Fact p.Prime]
variable {L : ℕ} [NeZero L]

namespace GroupedEqXV

open GroupedEq (sum_extend_zero geom_sum_le)
open GroupedEqX (groupExprW groupExprW_eval InputsX CoeffsX)




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
    (V VR : GroupedEqV.VParams) : Prop :=
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




def carryExpr (B : ℕ) (gf posOf OFFf : ℕ → ℕ) (lhs rhs : Var (CoeffsX L) (F p)) :
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


def carryInExpr (B : ℕ) (gf posOf OFFf : ℕ → ℕ) (lhs rhs : Var (CoeffsX L) (F p))
    (k : ℕ) : Expression (F p) :=
  if k = 0 then 0 else carryExpr B gf posOf OFFf lhs rhs (k - 1) - ((OFFf (k - 1) : ℕ) : F p)




def widthAllocFrom (Wf : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | c + 1, k₀ => (Wf k₀ - 1) + widthAllocFrom Wf c (k₀ + 1)


def widthConsFrom (Wf : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | c + 1, k₀ => Wf k₀ + widthConsFrom Wf c (k₀ + 1)




def carryLoop (B : ℕ) (gf posOf OFFf Wf : ℕ → ℕ) (hWok : ∀ k, 1 ≤ Wf k ∧ 2 ^ Wf k < p)
    [Fact (p > 2)]
    (lhs rhs : Var (CoeffsX L) (F p)) :
    ℕ → ℕ → Circuit (F p) Unit
  | 0, _ => pure ()
  | c + 1, k₀ => do
      assertion (RangeCheck.circuit (Wf k₀) (hWok k₀).2 (hWok k₀).1)
        (carryExpr B gf posOf OFFf lhs rhs k₀)
      carryLoop B gf posOf OFFf Wf hWok lhs rhs c (k₀ + 1)


def main (B : ℕ) (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GVXHyps p L B gf posOf G V VR) [Fact (p > 2)]
    (input : Var (InputsX L) (F p)) :
    Circuit (F p) Unit := do
  let Pc := input.lhs
  let Sc := input.rhs
  carryLoop B gf posOf VR.OFFf V.Wf hgv.2.2.2.1 Pc Sc (G - 2) 0
  assertZero
    (MulMod.polyEvalExpr
      (Vector.ofFn fun j : Fin L => Pc[j.val]'j.isLt - Sc[j.val]'j.isLt)
      ((2 : F p) ^ B))



lemma carryLoop_localLength (B : ℕ) (gf posOf OFFf Wf : ℕ → ℕ)
    (hWok : ∀ k, 1 ≤ Wf k ∧ 2 ^ Wf k < p) [Fact (p > 2)]
    (lhs rhs : Var (CoeffsX L) (F p)) :
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
    (lhs rhs : Var (CoeffsX L) (F p)) :
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
    (lhs rhs : Var (CoeffsX L) (F p)) :
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
    (lhs rhs : Var (CoeffsX L) (F p)) :
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
    (lhs rhs : Var (CoeffsX L) (F p)) :
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
    (lhs rhs : Var (CoeffsX L) (F p)) :
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

instance elaborated (B : ℕ) (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GVXHyps p L B gf posOf G V VR) [Fact (p > 2)] :
    ElaboratedCircuit (F p) (InputsX L) unit (main B gf posOf G V VR hgv) where
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




def Assumptions (NfL NfR : ℕ → ℕ) (input : InputsX L (F p)) : Prop :=
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
    (lhs rhs : Var (CoeffsX L) (F p)) :
    Expression.eval env
        (MulMod.polyEvalExpr
          (Vector.ofFn fun j : Fin L => lhs[j.val]'j.isLt - rhs[j.val]'j.isLt) ((2 : F p) ^ B))
      = (∑ i : Fin L, Expression.eval env (lhs[i.val]'i.isLt) * ((2 : F p) ^ B) ^ i.val)
        - (∑ i : Fin L, Expression.eval env (rhs[i.val]'i.isLt) * ((2 : F p) ^ B) ^ i.val) := by
  rw [MulMod.polyEvalExpr_eval, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [Vector.getElem_ofFn]
  simp only [Expression.eval]
  ring


lemma polyValue_eval_cast (B : ℕ) (env : Environment (F p)) (x : Var (CoeffsX L) (F p))
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


private lemma sum4_lt {a b c d q : ℕ} (h : a + b + c + d < q) :
    a < q ∧ b < q ∧ c < q ∧ d < q := by omega


private lemma sum5_lt {a b c d e q : ℕ} (h : a + b + c + d + e < q) :
    a < q ∧ b < q ∧ c < q ∧ d < q ∧ e < q := by omega




def circuit (B : ℕ) (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GVXHyps p L B gf posOf G V VR) (hB1 : 1 ≤ B)
    [Fact (p > 2)] : FormalAssertion (F p) (InputsX L) where
    main := main B gf posOf G V VR hgv
    Assumptions := Assumptions V.Nf VR.Nf
    Spec := GroupedEqX.Spec B L
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
      -- coefficient-level digit functions (vanish beyond L)
      set Pn : ℕ → ℕ := fun k => if h : k < L then (input.lhs[k]'h).val else 0 with hPn
      set Sn : ℕ → ℕ := fun k => if h : k < L then (input.rhs[k]'h).val else 0 with hSn
      -- group digit functions (schedule windows)
      set QP : ℕ → ℕ := fun j => ∑ i ∈ Finset.range (gf j), Pn (posOf j + i) * 2 ^ (B * i) with hQP
      set QS : ℕ → ℕ := fun j => ∑ i ∈ Finset.range (gf j), Sn (posOf j + i) * 2 ^ (B * i) with hQS
      have hQP_app : ∀ j, QP j = ∑ i ∈ Finset.range (gf j), Pn (posOf j + i) * 2 ^ (B * i) :=
        fun _ => rfl
      have hQS_app : ∀ j, QS j = ∑ i ∈ Finset.range (gf j), Sn (posOf j + i) * 2 ^ (B * i) :=
        fun _ => rfl
      -- effective offsets (0 at the top) and carries (0 at the top)
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
      -- eval bridges
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
      -- per-group ℕ equation (interior boundaries only; the top is the mod-p rider)
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
      -- express polyValue in position form
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
      rw [GroupedEqX.Spec]
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
      -- coefficient digit functions
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
      -- group digits
      set QP : ℕ → ℕ := fun j => ∑ i ∈ Finset.range (gf j), Pn (posOf j + i) * 2 ^ (B * i) with hQP
      set QS : ℕ → ℕ := fun j => ∑ i ∈ Finset.range (gf j), Sn (posOf j + i) * 2 ^ (B * i) with hQS
      have hQP_app : ∀ j, QP j = ∑ i ∈ Finset.range (gf j), Pn (posOf j + i) * 2 ^ (B * i) :=
        fun _ => rfl
      have hQS_app : ∀ j, QS j = ∑ i ∈ Finset.range (gf j), Sn (posOf j + i) * 2 ^ (B * i) :=
        fun _ => rfl
      -- group-level partial sums and carries (with per-boundary offsets)
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
      -- eval bridges
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
      -- prefix-quotient bounds from the recursive offsets
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
      -- top values agree
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
      -- per-group ℕ equation for the honest carries
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
      -- eval bridges for the goal
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
      · -- the loop's range checks
        refine carryLoop_completeness B gf posOf VR.OFFf V.Wf hWok env
          input_var.lhs input_var.rhs (G - 2) 0 i₀ fun i hi => ?_
        rw [Nat.zero_add, hcarry_eval i (by omega),
          ZMod.val_natCast_of_lt (lt_trans (hrange i (by omega)) (hWok i).2)]
        exact hrange i (by omega)
      · -- final mod-p row: holds because the honest values satisfy the spec
        have hspec' : polyValue B input.lhs = polyValue B input.rhs := h_spec
        have hcl := polyValue_eval_cast B env.toEnvironment input_var.lhs input.lhs
          (fun j hj => ha_e j hj)
        have hcr := polyValue_eval_cast B env.toEnvironment input_var.rhs input.rhs
          (fun j hj => hb_e j hj)
        have hd := polyEvalExpr_diff_eval B env.toEnvironment input_var.lhs input_var.rhs
        rw [← hcl, ← hcr, hspec', sub_self] at hd
        try simp only [circuit_norm]
        exact hd


lemma circuit_assumptions_eq (B : ℕ) (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GVXHyps p L B gf posOf G V VR)
    (hB1 : 1 ≤ B) [Fact (p > 2)] :
    (circuit (L := L) B gf posOf G V VR hgv hB1).Assumptions = Assumptions V.Nf VR.Nf := rfl


lemma circuit_spec_eq (B : ℕ) (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GVXHyps p L B gf posOf G V VR)
    (hB1 : 1 ≤ B) [Fact (p > 2)] :
    (circuit (L := L) B gf posOf G V VR hgv hB1).Spec = GroupedEqX.Spec B L := rfl


lemma circuit_channels_req_eq (B : ℕ) (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GVXHyps p L B gf posOf G V VR)
    (hB1 : 1 ≤ B) [Fact (p > 2)] :
    (circuit (L := L) B gf posOf G V VR hgv hB1).channelsWithRequirements = [] := rfl




def lowVec (rhs : Var (CoeffsX L) (F p)) : Vector (Expression (F p)) (L - 1) :=
  Vector.mapFinRange (L - 1) fun k => rhs[k.val]'(by have := k.isLt; omega)


def topExprD (B : ℕ) (lhs rhs : Var (CoeffsX L) (F p)) : Expression (F p) :=
  (MulMod.polyEvalExpr lhs ((2 : F p) ^ B)
    - MulMod.polyEvalExpr (lowVec rhs) ((2 : F p) ^ B)) / ((2 : F p) ^ (B * (L - 1)))


def rhsD (B : ℕ) (lhs rhs : Var (CoeffsX L) (F p)) : Var (CoeffsX L) (F p) :=
  Vector.mapFinRange L fun k =>
    if _h : k.val < L - 1 then rhs[k.val] else topExprD B lhs rhs


def topValD (B : ℕ) (lhs rhs : CoeffsX L (F p)) : F p :=
  (((2 : F p) ^ (B * (L - 1)))⁻¹)
    * ((∑ i : Fin L, lhs[i.val] * ((2 : F p) ^ B) ^ i.val)
      - (∑ i : Fin (L - 1),
          (rhs[i.val]'(by have := i.isLt; omega)) * ((2 : F p) ^ B) ^ i.val))


def rhsValD (B : ℕ) (lhs rhs : CoeffsX L (F p)) : CoeffsX L (F p) :=
  Vector.mapFinRange L fun k =>
    if _h : k.val < L - 1 then rhs[k.val] else topValD B lhs rhs

lemma rhsD_getElem_low (B : ℕ) (lhs rhs : Var (CoeffsX L) (F p)) (k : ℕ) (hk : k < L - 1) :
    (rhsD B lhs rhs)[k]'(by omega) = rhs[k]'(by omega) := by
  unfold rhsD
  rw [Vector.getElem_mapFinRange]
  simp only [dif_pos hk]

lemma rhsD_getElem_top (B : ℕ) (lhs rhs : Var (CoeffsX L) (F p)) :
    (rhsD B lhs rhs)[L - 1]'(by have := Nat.pos_of_neZero L; omega) = topExprD B lhs rhs := by
  unfold rhsD
  rw [Vector.getElem_mapFinRange]
  simp only [dif_neg (lt_irrefl (L - 1))]

lemma rhsValD_getElem_low (B : ℕ) (lhs rhs : CoeffsX L (F p)) (k : ℕ) (hk : k < L - 1) :
    (rhsValD B lhs rhs)[k]'(by omega) = rhs[k]'(by omega) := by
  unfold rhsValD
  rw [Vector.getElem_mapFinRange]
  simp only [dif_pos hk]

lemma rhsValD_getElem_top (B : ℕ) (lhs rhs : CoeffsX L (F p)) :
    (rhsValD B lhs rhs)[L - 1]'(by have := Nat.pos_of_neZero L; omega) = topValD B lhs rhs := by
  unfold rhsValD
  rw [Vector.getElem_mapFinRange]
  simp only [dif_neg (lt_irrefl (L - 1))]


lemma two_pow_ne_zero' [Fact (p > 2)] (n : ℕ) : ((2 : F p) ^ n) ≠ 0 := by
  have hp2 : (2 : ℕ) < p := Fact.out
  have h2ne : ((2 : ℕ) : F p) ≠ 0 := by
    intro h0
    have hv := ZMod.val_natCast_of_lt hp2
    rw [h0, ZMod.val_zero] at hv; omega
  have : ((2 : ℕ) : F p) = (2 : F p) := by push_cast; ring
  rw [this] at h2ne
  exact pow_ne_zero _ h2ne


lemma topExprD_eval [Fact (p > 2)] (B : ℕ) (env : Environment (F p))
    (lhs rhs : Var (CoeffsX L) (F p)) :
    Expression.eval env (topExprD B lhs rhs)
      = (((2 : F p) ^ (B * (L - 1)))⁻¹)
        * ((∑ i : Fin L, Expression.eval env (lhs[i.val]'i.isLt) * ((2 : F p) ^ B) ^ i.val)
          - (∑ i : Fin (L - 1),
              Expression.eval env (rhs[i.val]'(by have := i.isLt; omega))
                * ((2 : F p) ^ B) ^ i.val)) := by
  simp only [topExprD, Expression.eval, MulMod.polyEvalExpr_eval]
  have hlow : (∑ i : Fin (L - 1),
        Expression.eval env ((lowVec rhs)[i.val]'i.isLt) * ((2 : F p) ^ B) ^ i.val)
      = ∑ i : Fin (L - 1),
          Expression.eval env (rhs[i.val]'(by have := i.isLt; omega)) * ((2 : F p) ^ B) ^ i.val := by
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    simp only [lowVec, Vector.getElem_mapFinRange]
  rw [hlow]
  ring


lemma polyEvalExpr_rhsD_eval [Fact (p > 2)] (B : ℕ) (env : Environment (F p))
    (lhs rhs : Var (CoeffsX L) (F p)) :
    Expression.eval env
        (MulMod.polyEvalExpr
          (Vector.ofFn fun j : Fin L =>
            lhs[j.val]'j.isLt - (rhsD B lhs rhs)[j.val]'j.isLt) ((2 : F p) ^ B)) = 0 := by
  have hL : 0 < L := Nat.pos_of_neZero L
  rw [polyEvalExpr_diff_eval, sub_eq_zero]
  -- total ℕ-indexed summands (mirrors the `Pn`/`Sn` pattern of the soundness proof)
  set gR : ℕ → F p := fun i =>
    if h : i < L then Expression.eval env ((rhsD B lhs rhs)[i]'h) * ((2 : F p) ^ B) ^ i
    else 0 with hgR
  set gS : ℕ → F p := fun i =>
    if h : i < L - 1 then Expression.eval env (rhs[i]'(by omega)) * ((2 : F p) ^ B) ^ i
    else 0 with hgS
  have hR : (∑ i : Fin L,
        Expression.eval env ((rhsD B lhs rhs)[i.val]'i.isLt) * ((2 : F p) ^ B) ^ i.val)
      = ∑ i ∈ Finset.range L, gR i := by
    rw [← Fin.sum_univ_eq_sum_range gR]
    apply Finset.sum_congr rfl
    intro i _
    simp only [hgR, dif_pos i.isLt]
  have hRlow : (∑ i : Fin (L - 1),
        Expression.eval env (rhs[i.val]'(by have := i.isLt; omega)) * ((2 : F p) ^ B) ^ i.val)
      = ∑ i ∈ Finset.range (L - 1), gS i := by
    rw [← Fin.sum_univ_eq_sum_range gS]
    apply Finset.sum_congr rfl
    intro i _
    simp only [hgS, dif_pos i.isLt]
  have hlowsame : ∀ i ∈ Finset.range (L - 1), gR i = gS i := by
    intro i hi
    rw [Finset.mem_range] at hi
    simp only [hgR, hgS, dif_pos (by omega : i < L), dif_pos hi]
    congr 1
    exact congrArg (Expression.eval env) (rhsD_getElem_low B lhs rhs i hi)
  have hRsplit : (∑ i ∈ Finset.range L, gR i)
      = (∑ i ∈ Finset.range (L - 1), gS i) + gR (L - 1) := by
    conv_lhs => rw [show L = (L - 1) + 1 from by omega]
    rw [Finset.sum_range_succ]
    congr 1
    exact Finset.sum_congr rfl hlowsame
  have htopval : gR (L - 1)
      = (∑ i : Fin L, Expression.eval env (lhs[i.val]'i.isLt) * ((2 : F p) ^ B) ^ i.val)
        - (∑ i ∈ Finset.range (L - 1), gS i) := by
    simp only [hgR, dif_pos (by omega : L - 1 < L)]
    rw [congrArg (Expression.eval env) (rhsD_getElem_top B lhs rhs), topExprD_eval, hRlow]
    have hxpow : ((2 : F p) ^ B) ^ (L - 1) = (2 : F p) ^ (B * (L - 1)) := by
      rw [← pow_mul]
    rw [hxpow]
    set Y : F p := (∑ i : Fin L, Expression.eval env (lhs[i.val]'i.isLt) * ((2 : F p) ^ B) ^ i.val)
      - (∑ i ∈ Finset.range (L - 1), gS i) with hY
    calc (((2 : F p) ^ (B * (L - 1)))⁻¹ * Y) * (2 : F p) ^ (B * (L - 1))
        = Y * ((((2 : F p) ^ (B * (L - 1)))⁻¹) * (2 : F p) ^ (B * (L - 1))) := by ring
      _ = Y := by rw [inv_mul_cancel₀ (two_pow_ne_zero' _), mul_one]
  rw [hR, hRsplit, htopval]
  ring


lemma topExprD_eval_of_sum_eq_zero [Fact (p > 2)] (B : ℕ) (env : Environment (F p))
    (lhs rhs : Var (CoeffsX L) (F p)) (zl zr : ℕ → ℤ)
    (hl : ∀ (k : ℕ) (hk : k < L), Expression.eval env (lhs[k]'hk) = ((zl k : ℤ) : F p))
    (hr : ∀ (k : ℕ) (hk : k < L - 1),
      Expression.eval env (rhs[k]'(by omega)) = ((zr k : ℤ) : F p))
    (hzero : (∑ k ∈ Finset.range L, (zl k - zr k) * 2 ^ (B * k)) = 0) :
    Expression.eval env (topExprD B lhs rhs) = ((zr (L - 1) : ℤ) : F p) := by
  have hL : 0 < L := Nat.pos_of_neZero L
  rw [topExprD_eval]
  set x : F p := (2 : F p) ^ B with hx
  have hlsum : (∑ i : Fin L, Expression.eval env (lhs[i.val]'i.isLt) * x ^ i.val)
      = ∑ i : Fin L, ((zl i.val : ℤ) : F p) * x ^ i.val :=
    Finset.sum_congr rfl fun i _ => by rw [hl i.val i.isLt]
  have hrsum : (∑ i : Fin (L - 1),
        Expression.eval env (rhs[i.val]'(by have := i.isLt; omega)) * x ^ i.val)
      = ∑ i : Fin (L - 1), ((zr i.val : ℤ) : F p) * x ^ i.val :=
    Finset.sum_congr rfl fun i _ => by rw [hr i.val (by have := i.isLt; omega)]
  rw [hlsum, hrsum]
  have hc : (∑ k ∈ Finset.range L, (((zl k : ℤ) : F p) - ((zr k : ℤ) : F p)) * x ^ k) = 0 := by
    have hc0 := congrArg (fun z : ℤ => ((z : ℤ) : F p)) hzero
    simp only [Int.cast_zero, Int.cast_sum] at hc0
    rw [← hc0]
    apply Finset.sum_congr rfl
    intro k _
    push_cast
    rw [hx, ← pow_mul]
  have hkey : (∑ i : Fin L, ((zl i.val : ℤ) : F p) * x ^ i.val)
      - (∑ i : Fin (L - 1), ((zr i.val : ℤ) : F p) * x ^ i.val)
      = ((zr (L - 1) : ℤ) : F p) * x ^ (L - 1) := by
    have h1 : (∑ i : Fin L, ((zl i.val : ℤ) : F p) * x ^ i.val)
        = ∑ k ∈ Finset.range L, ((zl k : ℤ) : F p) * x ^ k :=
      Fin.sum_univ_eq_sum_range (fun k => ((zl k : ℤ) : F p) * x ^ k) L
    have h2 : (∑ i : Fin (L - 1), ((zr i.val : ℤ) : F p) * x ^ i.val)
        = ∑ k ∈ Finset.range (L - 1), ((zr k : ℤ) : F p) * x ^ k :=
      Fin.sum_univ_eq_sum_range (fun k => ((zr k : ℤ) : F p) * x ^ k) (L - 1)
    have h4 : (∑ k ∈ Finset.range L, ((zl k : ℤ) : F p) * x ^ k)
          - (∑ k ∈ Finset.range L, ((zr k : ℤ) : F p) * x ^ k) = 0 := by
      rw [← Finset.sum_sub_distrib, ← hc]
      apply Finset.sum_congr rfl
      intro k _
      ring
    have h3 : (∑ k ∈ Finset.range L, ((zl k : ℤ) : F p) * x ^ k)
        = ∑ k ∈ Finset.range L, ((zr k : ℤ) : F p) * x ^ k := sub_eq_zero.mp h4
    have h5 : (∑ k ∈ Finset.range L, ((zr k : ℤ) : F p) * x ^ k)
        = (∑ k ∈ Finset.range (L - 1), ((zr k : ℤ) : F p) * x ^ k)
          + ((zr (L - 1) : ℤ) : F p) * x ^ (L - 1) := by
      conv_lhs => rw [show L = (L - 1) + 1 from by omega]
      rw [Finset.sum_range_succ]
    rw [h1, h2, h3, h5]
    ring
  rw [hkey]
  have hxpow : x ^ (L - 1) = (2 : F p) ^ (B * (L - 1)) := by rw [hx, ← pow_mul]
  rw [hxpow]
  calc ((2 : F p) ^ (B * (L - 1)))⁻¹ * (((zr (L - 1) : ℤ) : F p) * (2 : F p) ^ (B * (L - 1)))
      = ((zr (L - 1) : ℤ) : F p)
        * (((2 : F p) ^ (B * (L - 1)))⁻¹ * (2 : F p) ^ (B * (L - 1))) := by ring
    _ = ((zr (L - 1) : ℤ) : F p) := by rw [inv_mul_cancel₀ (two_pow_ne_zero' _), mul_one]


lemma rhsD_eval_bridge (B : ℕ) [Fact (p > 2)] (env : Environment (F p))
    (lhsv rhsv : Var (CoeffsX L) (F p)) (lhs rhs : CoeffsX L (F p))
    (hl_e : ∀ (j : ℕ) (hj : j < L), Expression.eval env (lhsv[j]'hj) = lhs[j]'hj)
    (hr_e : ∀ (j : ℕ) (hj : j < L), Expression.eval env (rhsv[j]'hj) = rhs[j]'hj) :
    ∀ (j : ℕ) (hj : j < L),
      Expression.eval env ((rhsD B lhsv rhsv)[j]'hj) = (rhsValD B lhs rhs)[j]'hj := by
  intro j hj
  by_cases h : j < L - 1
  · rw [rhsD_getElem_low B lhsv rhsv j h, rhsValD_getElem_low B lhs rhs j h]
    exact hr_e j (by omega)
  · have hj1 : j = L - 1 := by omega
    subst hj1
    rw [rhsD_getElem_top B lhsv rhsv, rhsValD_getElem_top B lhs rhs, topExprD_eval]
    unfold topValD
    congr 1
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      rw [hl_e i.val i.isLt]
    · apply Finset.sum_congr rfl
      intro i _
      rw [hr_e i.val (by have := i.isLt; omega)]


def mainD (B : ℕ) (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GVXHyps p L B gf posOf G V VR) [Fact (p > 2)]
    (input : Var (InputsX L) (F p)) : Circuit (F p) Unit :=
  carryLoop B gf posOf VR.OFFf V.Wf hgv.2.2.2.1 input.lhs (rhsD B input.lhs input.rhs) (G - 2) 0

instance elaboratedD (B : ℕ) (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GVXHyps p L B gf posOf G V VR) [Fact (p > 2)] :
    ElaboratedCircuit (F p) (InputsX L) unit (mainD B gf posOf G V VR hgv) where
  localLength _ := widthAllocFrom V.Wf (G - 2) 0
  localLength_eq := by
    intro input offset
    unfold mainD
    exact carryLoop_localLength B gf posOf VR.OFFf V.Wf hgv.2.2.2.1
      input.lhs (rhsD B input.lhs input.rhs) (G - 2) 0 offset
  subcircuitsConsistent := by
    intro input offset
    unfold mainD
    exact carryLoop_subcircuitsConsistent B gf posOf VR.OFFf V.Wf hgv.2.2.2.1 _ _ _ _ offset
  channelsLawful := by
    intro input offset
    unfold mainD
    exact carryLoop_channelsLawful B gf posOf VR.OFFf V.Wf hgv.2.2.2.1 _ _ _ _ offset


def AssumptionsD (B : ℕ) (NfL NfR : ℕ → ℕ) (input : InputsX L (F p)) : Prop :=
  (∀ k : Fin L, (input.lhs[k.val]).val < NfL k.val) ∧
  (∀ k : Fin L, ((rhsValD B input.lhs input.rhs)[k.val]).val < NfR k.val)


def SpecD (B : ℕ) (input : InputsX L (F p)) : Prop :=
  polyValue B input.lhs = polyValue B (rhsValD B input.lhs input.rhs)


def circuitD (B : ℕ) (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GVXHyps p L B gf posOf G V VR) (hB1 : 1 ≤ B)
    [Fact (p > 2)] : FormalAssertion (F p) (InputsX L) where
    main := mainD B gf posOf G V VR hgv
    Assumptions := AssumptionsD B V.Nf VR.Nf
    Spec := SpecD B
    soundness := by
      obtain ⟨hpos0, hposS, hgf1, hWok, hNf1, hper, hG3, hlast, hCov, htrunc⟩ := hgv
      circuit_proof_start
      unfold mainD at h_holds
      have h_loop := h_holds
      have h_lin := polyEvalExpr_rhsD_eval (L := L) B env input_var.lhs input_var.rhs
      have hM : 0 < L := Nat.pos_of_neZero L
      have hG1 : 0 < G := by omega
      have hposMono : ∀ a b, a ≤ b → posOf a ≤ posOf b :=
        fun a b hab => monotone_nat_of_le_succ (fun k => by rw [hposS k]; omega) hab
      have he : ∀ k, B * posOf (k + 1) = B * posOf k + B * gf k :=
        fun k => by rw [hposS k, Nat.mul_add]
      have hemono : ∀ k, B * posOf k ≤ B * posOf (k + 1) := fun k => by rw [he k]; omega
      have h_range := carryLoop_soundness B gf posOf VR.OFFf V.Wf hWok env
        input_var.lhs (rhsD B input_var.lhs input_var.rhs) (G - 2) 0 i₀ h_loop
      -- coefficient-level digit functions (vanish beyond L)
      set Pn : ℕ → ℕ := fun k => if h : k < L then (input.lhs[k]'h).val else 0 with hPn
      set Sn : ℕ → ℕ := fun k => if h : k < L then ((rhsValD B input.lhs input.rhs)[k]'h).val else 0 with hSn
      -- group digit functions (schedule windows)
      set QP : ℕ → ℕ := fun j => ∑ i ∈ Finset.range (gf j), Pn (posOf j + i) * 2 ^ (B * i) with hQP
      set QS : ℕ → ℕ := fun j => ∑ i ∈ Finset.range (gf j), Sn (posOf j + i) * 2 ^ (B * i) with hQS
      have hQP_app : ∀ j, QP j = ∑ i ∈ Finset.range (gf j), Pn (posOf j + i) * 2 ^ (B * i) :=
        fun _ => rfl
      have hQS_app : ∀ j, QS j = ∑ i ∈ Finset.range (gf j), Sn (posOf j + i) * 2 ^ (B * i) :=
        fun _ => rfl
      -- effective offsets (0 at the top) and carries (0 at the top)
      set OFFe : ℕ → ℕ := fun k => if k = G - 1 then 0 else VR.OFFf k with hOFFe
      set Cn : ℕ → ℕ := fun k => if k = G - 1 then 0
        else (Expression.eval env (carryExpr B gf posOf VR.OFFf input_var.lhs (rhsD B input_var.lhs input_var.rhs) k)).val
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
      -- eval bridges
      have ha_e : ∀ (j : ℕ) (hj : j < L),
          Expression.eval env (input_var.lhs[j]'hj) = input.lhs[j]'hj := by
        intro j hj
        rw [← h_input]
        simp [Vector.getElem_map]
      have hb_e : ∀ (j : ℕ) (hj : j < L),
          Expression.eval env ((rhsD B input_var.lhs input_var.rhs)[j]'hj) = (rhsValD B input.lhs input.rhs)[j]'hj := by
        exact rhsD_eval_bridge B env input_var.lhs input_var.rhs input.lhs input.rhs
          (fun j hj => by rw [← h_input]; simp [Vector.getElem_map])
          (fun j hj => by rw [← h_input]; simp [Vector.getElem_map])
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
      have hGS_e : ∀ j : ℕ, Expression.eval env (groupExprW B L gf posOf (rhsD B input_var.lhs input_var.rhs) j)
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
          Expression.eval env (carryExpr B gf posOf VR.OFFf input_var.lhs (rhsD B input_var.lhs input_var.rhs) k)
            = ((Cn k : ℕ) : F p) := by
        intro k hk
        simp only [hCn, if_neg (by omega : ¬ k = G - 1)]
        rw [ZMod.natCast_zmod_val]
      -- per-group ℕ equation (interior boundaries only; the top is the mod-p rider)
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
      -- express polyValue in position form
      have hApos : polyValue B input.lhs = ∑ t ∈ Finset.range L, Pn t * 2 ^ (B * t) := by
        rw [polyValue, ← Fin.sum_univ_eq_sum_range (fun k => Pn k * 2 ^ (B * k))]
        apply Finset.sum_congr rfl
        intro i _; simp only [hPn, dif_pos i.isLt]
      have hBpos : polyValue B (rhsValD B input.lhs input.rhs) = ∑ t ∈ Finset.range L, Sn t * 2 ^ (B * t) := by
        rw [polyValue, ← Fin.sum_univ_eq_sum_range (fun k => Sn k * 2 ^ (B * k))]
        apply Finset.sum_congr rfl
        intro i _; simp only [hSn, dif_pos i.isLt]
      have hMODP : ((polyValue B input.lhs : ℕ) : F p) = ((polyValue B (rhsValD B input.lhs input.rhs) : ℕ) : F p) := by
        have hcl := polyValue_eval_cast B env input_var.lhs input.lhs (fun j hj => ha_e j hj)
        have hcr := polyValue_eval_cast B env (rhsD B input_var.lhs input_var.rhs) (rhsValD B input.lhs input.rhs) (fun j hj => hb_e j hj)
        have hd := polyEvalExpr_diff_eval B env input_var.lhs (rhsD B input_var.lhs input_var.rhs)
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
      have hF2 : polyValue B (rhsValD B input.lhs input.rhs) = SSlow + W * TS := by
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
          = polyValue B (rhsValD B input.lhs input.rhs) + W * (Cn (n0 - 1) + TP) := by
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
          = ((polyValue B (rhsValD B input.lhs input.rhs) : ℕ) : F p)
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
      have hSpec : polyValue B input.lhs = polyValue B (rhsValD B input.lhs input.rhs) := by
        rw [hnat_eq] at hcombo
        exact Nat.add_right_cancel hcombo
      exact ⟨hSpec, carryLoop_requirements B gf posOf VR.OFFf V.Wf hWok env
        input_var.lhs (rhsD B input_var.lhs input_var.rhs) _ _ _⟩
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
      -- coefficient digit functions
      set Pn : ℕ → ℕ := fun k => if h : k < L then (input.lhs[k]'h).val else 0 with hPn
      set Sn : ℕ → ℕ := fun k => if h : k < L then ((rhsValD B input.lhs input.rhs)[k]'h).val else 0 with hSn
      have hPn_lt : ∀ k, Pn k < V.Nf k := by
        intro k; simp only [hPn]; split
        · rename_i h; exact h_assumptions.1 ⟨k, h⟩
        · exact (hNf1 k).1
      have hSn_lt : ∀ k, Sn k < VR.Nf k := by
        intro k; simp only [hSn]; split
        · rename_i h; exact h_assumptions.2 ⟨k, h⟩
        · exact (hNf1 k).2
      -- group digits
      set QP : ℕ → ℕ := fun j => ∑ i ∈ Finset.range (gf j), Pn (posOf j + i) * 2 ^ (B * i) with hQP
      set QS : ℕ → ℕ := fun j => ∑ i ∈ Finset.range (gf j), Sn (posOf j + i) * 2 ^ (B * i) with hQS
      have hQP_app : ∀ j, QP j = ∑ i ∈ Finset.range (gf j), Pn (posOf j + i) * 2 ^ (B * i) :=
        fun _ => rfl
      have hQS_app : ∀ j, QS j = ∑ i ∈ Finset.range (gf j), Sn (posOf j + i) * 2 ^ (B * i) :=
        fun _ => rfl
      -- group-level partial sums and carries (with per-boundary offsets)
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
      -- eval bridges
      have ha_e : ∀ (j : ℕ) (hj : j < L),
          Expression.eval env.toEnvironment (input_var.lhs[j]'hj) = input.lhs[j]'hj := by
        intro j hj
        rw [← h_input]
        simp [Vector.getElem_map]
      have hb_e : ∀ (j : ℕ) (hj : j < L),
          Expression.eval env.toEnvironment ((rhsD B input_var.lhs input_var.rhs)[j]'hj) = (rhsValD B input.lhs input.rhs)[j]'hj := by
        exact rhsD_eval_bridge B env.toEnvironment input_var.lhs input_var.rhs input.lhs input.rhs
          (fun j hj => by rw [← h_input]; simp [Vector.getElem_map])
          (fun j hj => by rw [← h_input]; simp [Vector.getElem_map])
      -- prefix-quotient bounds from the recursive offsets
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
      -- top values agree
      have hPFn_top : PFn (G - 1) = polyValue B input.lhs := by
        rw [hPFn_app, show G - 1 + 1 = G from by omega]
        have h1 : polyValue B input.lhs = ∑ k ∈ Finset.range (L), Pn k * 2 ^ (B * k) := by
          rw [polyValue, ← Fin.sum_univ_eq_sum_range (fun k => Pn k * 2 ^ (B * k))]
          apply Finset.sum_congr rfl
          intro i _; simp only [hPn, dif_pos i.isLt]
        rw [h1, sum_extend_zero B (L) (posOf G) Pn hCov
          (fun t ht => by simp only [hPn, dif_neg (by omega : ¬ t < L)]),
          ← group_flatten_sched B gf posOf Pn hpos0 hposS G]
      have hPSn_top : PSn (G - 1) = polyValue B (rhsValD B input.lhs input.rhs) := by
        rw [hPSn_app, show G - 1 + 1 = G from by omega]
        have h1 : polyValue B (rhsValD B input.lhs input.rhs) = ∑ k ∈ Finset.range (L), Sn k * 2 ^ (B * k) := by
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
      -- per-group ℕ equation for the honest carries
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
      -- eval bridges for the goal
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
      have hGS_e : ∀ j : ℕ, Expression.eval env.toEnvironment (groupExprW B L gf posOf (rhsD B input_var.lhs input_var.rhs) j)
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
          Expression.eval env.toEnvironment (carryExpr B gf posOf VR.OFFf input_var.lhs (rhsD B input_var.lhs input_var.rhs) k)
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
      unfold mainD
      refine carryLoop_completeness B gf posOf VR.OFFf V.Wf hWok env
        input_var.lhs (rhsD B input_var.lhs input_var.rhs) (G - 2) 0 i₀ fun i hi => ?_
      rw [Nat.zero_add, hcarry_eval i (by omega),
        ZMod.val_natCast_of_lt (lt_trans (hrange i (by omega)) (hWok i).2)]
      exact hrange i (by omega)




lemma groupExprW_eval_stable (B : ℕ) (gf posOf : ℕ → ℕ)
    (env env' : Environment (F p)) (x : Var (CoeffsX L) (F p))
    (hx : ∀ (j : ℕ) (hj : j < L),
      Expression.eval env (x[j]'hj) = Expression.eval env' (x[j]'hj)) (k : ℕ) :
    Expression.eval env (groupExprW B L gf posOf x k)
      = Expression.eval env' (groupExprW B L gf posOf x k) := by
  rw [groupExprW_eval, groupExprW_eval]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  by_cases h : posOf k + i < L
  · simp only [dif_pos h]
    exact hx _ h
  · simp only [dif_neg h]


lemma carryExpr_eval_stable (B : ℕ) (gf posOf OFFf : ℕ → ℕ)
    (env env' : Environment (F p)) (lhs rhs : Var (CoeffsX L) (F p))
    (hl : ∀ (j : ℕ) (hj : j < L),
      Expression.eval env (lhs[j]'hj) = Expression.eval env' (lhs[j]'hj))
    (hr : ∀ (j : ℕ) (hj : j < L),
      Expression.eval env (rhs[j]'hj) = Expression.eval env' (rhs[j]'hj)) :
    ∀ k, Expression.eval env (carryExpr B gf posOf OFFf lhs rhs k)
      = Expression.eval env' (carryExpr B gf posOf OFFf lhs rhs k) := by
  intro k
  induction k with
  | zero =>
    simp only [carryExpr, Expression.eval]
    rw [groupExprW_eval_stable B gf posOf env env' lhs hl 0,
      groupExprW_eval_stable B gf posOf env env' rhs hr 0]
  | succ k ih =>
    simp only [carryExpr, Expression.eval]
    rw [groupExprW_eval_stable B gf posOf env env' lhs hl (k + 1),
      groupExprW_eval_stable B gf posOf env env' rhs hr (k + 1), ih]


lemma carryLoop_structuralComputableWitnesses
    (B : ℕ) (gf posOf OFFf Wf : ℕ → ℕ)
    (hWok : ∀ k, 1 ≤ Wf k ∧ 2 ^ Wf k < p) [Fact (p > 2)]
    (input : Var (InputsX L) (F p)) (lhs rhs : Var (CoeffsX L) (F p))
    (env env' : ProverEnvironment (F p))
    (hstab : ∀ (e e' : ProverEnvironment (F p)),
      eval e input = eval e' input →
      ∀ k, Expression.eval e.toEnvironment (carryExpr B gf posOf OFFf lhs rhs k)
        = Expression.eval e'.toEnvironment (carryExpr B gf posOf OFFf lhs rhs k)) :
    ∀ (c k₀ offset : ℕ),
      Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.StructuralComputableWitnesses
        input env env' offset
        ((carryLoop B gf posOf OFFf Wf hWok lhs rhs c k₀).operations offset) := by
  intro c
  induction c with
  | zero =>
    intro k₀ offset
    simp only [carryLoop, Circuit.pure_operations_eq]
    trivial
  | succ n ih =>
    intro k₀ offset
    rw [show carryLoop B gf posOf OFFf Wf hWok lhs rhs (n + 1) k₀
        = (do
            assertion (RangeCheck.circuit (Wf k₀) (hWok k₀).2 (hWok k₀).1)
              (carryExpr B gf posOf OFFf lhs rhs k₀)
            carryLoop B gf posOf OFFf Wf hWok lhs rhs n (k₀ + 1)) from rfl]
    rw [Circuit.bind_operations_eq]
    rw [Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.structuralComputableWitnesses_append]
    constructor
    · exact Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_structuralComputableWitnesses_of_condition
        (RangeCheck.circuit (Wf k₀) (hWok k₀).2 (hWok k₀).1) input
        (carryExpr B gf posOf OFFf lhs rhs k₀) offset
        (by
          intro k e e' hk h_agree h_parent
          have h := hstab e e' h_parent k₀
          rw [CircuitType.eval_expression_prover_to_verifier (M := field),
            CircuitType.eval_expression_prover_to_verifier (M := field)]
          simpa only [CircuitType.eval_var_field] using h)
        (RangeCheck.computableWitnesses (Wf k₀) (hWok k₀).2 (hWok k₀).1) env env'
    · rw [show ((assertion (RangeCheck.circuit (Wf k₀) (hWok k₀).2 (hWok k₀).1)
            (carryExpr B gf posOf OFFf lhs rhs k₀)).operations offset).localLength + offset
          = offset + (assertion (RangeCheck.circuit (Wf k₀) (hWok k₀).2 (hWok k₀).1)
            (carryExpr B gf posOf OFFf lhs rhs k₀)).localLength offset from by
        rw [Nat.add_comm]]
      exact ih (k₀ + 1) _

theorem computableWitnesses (B : ℕ) (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
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
  apply carryLoop_structuralComputableWitnesses
  intro e e' h_parent k
  have hl : ∀ (j : ℕ) (hj : j < L),
      Expression.eval e.toEnvironment (input.lhs[j]'hj)
        = Expression.eval e'.toEnvironment (input.lhs[j]'hj) := by
    intro j hj
    simpa [circuit_norm, CircuitType.eval_expression_prover_to_verifier,
      CircuitType.eval_expression, ProvableType.eval, explicit_provable_type,
      Vector.getElem_map] using
        congrArg (fun x : InputsX L (F p) => x.lhs[j]'hj) h_parent
  have hr : ∀ (j : ℕ) (hj : j < L),
      Expression.eval e.toEnvironment (input.rhs[j]'hj)
        = Expression.eval e'.toEnvironment (input.rhs[j]'hj) := by
    intro j hj
    simpa [circuit_norm, CircuitType.eval_expression_prover_to_verifier,
      CircuitType.eval_expression, ProvableType.eval, explicit_provable_type,
      Vector.getElem_map] using
        congrArg (fun x : InputsX L (F p) => x.rhs[j]'hj) h_parent
  exact carryExpr_eval_stable B gf posOf VR.OFFf e.toEnvironment e'.toEnvironment
    input.lhs input.rhs hl hr k

end GroupedEqXV

end

-- (The RSA tree's `WeightedWindow` mixed-convolution bound section is not
-- ported: it serves that tree's interpolated-product caps, not the grouped
-- equality circuit.)

end Solution.Secp256k1ScalarMul
