/-
  Gadgets that SHARE input variables.

  `Solution/Research/DegreePack.lean` proves the two obligations for gadgets living on
  pairwise **disjoint** blocks of cube variables.  This file settles the shared-variable
  case: both obligations are **false** there, and the counterexamples are explicit.

  * `shared_degree_three_packs` : two gadgets, non-affine on the cube, reading two triples
    that share two variables, with multiplier `lam = 1`, whose packed target has
    multilinear degree `3` and *is* pinned uniquely by a single R1CS row.
  * `shared_three_degree_two_gadgets_pack` : three non-affine gadgets of multilinear
    degree `2`, on blocks that are not pairwise disjoint, with nonzero multipliers, whose
    packed target is pinned by a single row.
  * `pinned_target_of_degree_three` : the intermediate step "pinned implies multilinear
    degree at most 2", which the disjoint-blocks proof establishes, already fails without
    disjointness -- here a degree-3 function of a single triple pinned by one row.

  The mechanism is the same in each case: over the cube a row of the shape
  `L(x) * z = E(x)` with `L` affine and nowhere zero pins `z = E/L`, and `E/L` is *not*
  affine, indeed not even of degree `2`, as soon as `L` is not constant.  With disjoint
  blocks the cross-block coefficients force `L` to be constant (this is what
  `Packing.linear_normal_form` proves); with shared variables they do not.
-/
import Solution.Research.Examples

namespace Solution.Research

open Finset

/-! ## A nowhere-vanishing affine form makes `E / L` a degree-3 function

Over `ℚ` on the cube `{0,1}^{Fin 4}` put `L = 1 + x₁ + x₂` (values `1, 2, 3`, never zero)
and `E = x₀`.  The row `L * z = E` pins `z` uniquely, and the multilinear form of `E / L`
is `x₀ - x₀x₁/2 - x₀x₂/2 + x₀x₁x₂/3`, of degree 3. -/

/-- `1 + x₁ + x₂`, an affine form on `{0,1}^{Fin 4}` that never vanishes. -/
def sharedL : Aff (Fin 4) ℚ := ⟨1, fun i => if i = 1 then 1 else if i = 2 then 1 else 0⟩

/-- `x₀`, as an affine form on `{0,1}^{Fin 4}`. -/
def sharedE : Aff (Fin 4) ℚ := ⟨0, fun i => if i = 0 then 1 else 0⟩

/-- The multilinear degree-3 function `x₀ / (1 + x₁ + x₂)`. -/
def sharedTarget : Finset (Fin 4) → ℚ := fun x =>
  mono {0} x - (1 / 2) * mono {0, 1} x - (1 / 2) * mono {0, 2} x + (1 / 3) * mono {0, 1, 2} x

/-- The row `(1 + x₁ + x₂) * z = x₀`. -/
def sharedRow : Row (Fin 4) ℚ where
  Az := 0
  A0 := sharedL
  Bz := 1
  B0 := ⟨0, fun _ => 0⟩
  Cz := 0
  C0 := sharedE

theorem sharedL_ev (x : Finset (Fin 4)) :
    sharedL.ev x = 1 + (if (1 : Fin 4) ∈ x then 1 else 0) + (if (2 : Fin 4) ∈ x then 1 else 0) := by
  simp only [sharedL, Aff.ev]
  rw [show (fun i : Fin 4 => if i = 1 then (1 : ℚ) else if i = 2 then 1 else 0)
      = fun i => (if i = 1 then (1 : ℚ) else 0) + (if i = 2 then (1 : ℚ) else 0) by
    funext i; by_cases h1 : i = 1 <;> by_cases h2 : i = 2 <;> simp [h1, h2]]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' x (1 : Fin 4) (fun _ => (1 : ℚ)),
    Finset.sum_ite_eq' x (2 : Fin 4) (fun _ => (1 : ℚ))]
  ring

theorem sharedE_ev (x : Finset (Fin 4)) :
    sharedE.ev x = (if (0 : Fin 4) ∈ x then 1 else 0) := by
  simp only [sharedE, Aff.ev]
  rw [Finset.sum_ite_eq' x (0 : Fin 4) (fun _ => (1 : ℚ))]
  ring

theorem sharedL_ne_zero (x : Finset (Fin 4)) : sharedL.ev x ≠ 0 := by
  rw [sharedL_ev]
  by_cases h1 : (1 : Fin 4) ∈ x <;> by_cases h2 : (2 : Fin 4) ∈ x <;> norm_num [h1, h2]

/-- The defining identity: `L * (E / L) = E` on the cube. -/
theorem sharedL_mul_sharedTarget (x : Finset (Fin 4)) :
    sharedL.ev x * sharedTarget x = sharedE.ev x := by
  rw [sharedL_ev, sharedE_ev]
  simp only [sharedTarget, mono, Finset.insert_subset_iff, Finset.singleton_subset_iff]
  by_cases h0 : (0 : Fin 4) ∈ x <;> by_cases h1 : (1 : Fin 4) ∈ x <;>
    by_cases h2 : (2 : Fin 4) ∈ x <;> norm_num [h0, h1, h2]

/-- **The row `(1 + x₁ + x₂) * z = x₀` pins its target, uniquely (no decoy needed).** -/
theorem sharedRow_pins : sharedRow.Pins sharedTarget := by
  have hsat : ∀ (x : Finset (Fin 4)) (z : ℚ), sharedRow.Sat x z ↔ z = sharedTarget x := by
    intro x z
    have hL := sharedL_ne_zero x
    have hkey := sharedL_mul_sharedTarget x
    have hB : (⟨0, fun _ => 0⟩ : Aff (Fin 4) ℚ).ev x = 0 := by simp [Aff.ev]
    simp only [sharedRow, Row.Sat, hB, zero_mul, zero_add, one_mul, add_zero]
    constructor
    · intro h
      have : sharedL.ev x * z = sharedL.ev x * sharedTarget x := by
        rw [hkey]; linear_combination h
      exact mul_left_cancel₀ hL this
    · intro h; rw [h]; linear_combination hkey
  exact ⟨⟨0, fun _ => 0⟩, fun x => (hsat x _).2 rfl, fun x z hz => Or.inl ((hsat x z).1 hz)⟩

theorem coef_sharedTarget_top : coef sharedTarget ({0, 1, 2} : Finset (Fin 4)) = 1 / 3 := by
  unfold sharedTarget
  rw [coef_add, coef_sub, coef_sub, coef_const_mul, coef_const_mul, coef_const_mul,
    coef_mono, coef_mono, coef_mono, coef_mono, if_neg (by decide), if_neg (by decide),
    if_neg (by decide), if_pos rfl]
  norm_num

theorem card_sharedTop : ({0, 1, 2} : Finset (Fin 4)).card = 3 := by decide

/-- **The intermediate degree bound fails for shared variables.**  There is a single R1CS
row pinning (uniquely, without a decoy) a target of multilinear degree `3`.  This is the
step that the disjoint-blocks argument obtains from `Packing.linear_normal_form`; it is
simply false in general. -/
theorem pinned_target_of_degree_three :
    ∃ (t : Finset (Fin 4) → ℚ) (R : Row (Fin 4) ℚ) (S : Finset (Fin 4)),
      R.Pins t ∧ 3 ≤ S.card ∧ coef t S ≠ 0 :=
  ⟨sharedTarget, sharedRow, {0, 1, 2}, sharedRow_pins, by rw [card_sharedTop],
    by rw [coef_sharedTarget_top]; norm_num⟩

/-! ## Obligation 1 is false for gadgets that share variables -/

/-- First gadget: `x₀/(1 + x₁ + x₂) + x₁x₂`, a non-affine function of the triple
`{0, 1, 2}`. -/
def sharedF : Finset (Fin 4) → ℚ := fun x => sharedTarget x + mono {1, 2} x

/-- Second gadget: `-x₁x₂`, a non-affine function of the triple `{1, 2, 3}`. -/
def sharedG : Finset (Fin 4) → ℚ := fun x => -mono {1, 2} x

theorem dependsOn_sharedTarget : DependsOn sharedTarget ({0, 1, 2} : Finset (Fin 4)) := by
  refine ((((dependsOn_mono (by decide)).sub
    (DependsOn.const_mul (1 / 2) (dependsOn_mono (by decide)))).sub
    (DependsOn.const_mul (1 / 2) (dependsOn_mono (by decide)))).add
    (DependsOn.const_mul (1 / 3) (dependsOn_mono (by decide))))

theorem dependsOn_sharedF : DependsOn sharedF ({0, 1, 2} : Finset (Fin 4)) :=
  dependsOn_sharedTarget.add (dependsOn_mono (by decide))

theorem dependsOn_sharedG : DependsOn sharedG ({1, 2, 3} : Finset (Fin 4)) := by
  intro x y hxy
  show -mono {1, 2} x = -mono {1, 2} y
  rw [dependsOn_mono (F := ℚ) (by decide : ({1, 2} : Finset (Fin 4)) ⊆ {1, 2, 3}) x y hxy]

theorem coef_sharedF_top : coef sharedF ({0, 1, 2} : Finset (Fin 4)) = 1 / 3 := by
  unfold sharedF
  rw [coef_add, coef_sharedTarget_top, coef_mono, if_neg (by decide), add_zero]

theorem not_isAffineOn_sharedF : ¬ IsAffineOn sharedF :=
  not_isAffineOn_iff.mpr ⟨{0, 1, 2}, by rw [card_sharedTop]; omega,
    by rw [coef_sharedF_top]; norm_num⟩

theorem not_isAffineOn_sharedG : ¬ IsAffineOn sharedG := by
  refine not_isAffineOn_iff.mpr ⟨{1, 2}, by decide, ?_⟩
  show coef (fun x => -mono {1, 2} x) ({1, 2} : Finset (Fin 4)) ≠ 0
  rw [coef_neg, coef_mono, if_pos rfl]
  norm_num

theorem sharedF_add_sharedG : (fun x => sharedF x + 1 * sharedG x) = sharedTarget := by
  funext x
  simp only [sharedF, sharedG, one_mul]
  ring

/-- **Obligation 1 fails once the two input triples share variables.**

There are two functions `f`, `g` on the cube, non-affine, reading two triples of variables
that overlap (in two variables), and a nonzero multiplier `lam`, such that the packed
target `f + lam * g` has multilinear degree `3` and yet a single R1CS row determines
`z = f x + lam * g x` -- uniquely, not even using a decoy root.

So the disjointness hypothesis in `degree_three_never_packs` is not an artefact of the
proof: the statement is false without it.  (The mechanism does not even need cancellation
between the two gadgets to hide the cubic term: the packed target here really does have a
nonzero coefficient on the monomial `x₀x₁x₂`.) -/
theorem shared_degree_three_packs :
    ∃ (P Q : Finset (Fin 4)) (f g : Finset (Fin 4) → ℚ) (lam : ℚ) (R : Row (Fin 4) ℚ)
      (S : Finset (Fin 4)),
      ¬ Disjoint P Q ∧ P.card = 3 ∧ Q.card = 3 ∧ DependsOn f P ∧ DependsOn g Q ∧
        ¬ IsAffineOn f ∧ ¬ IsAffineOn g ∧ lam ≠ 0 ∧
        3 ≤ S.card ∧ coef (fun x => f x + lam * g x) S ≠ 0 ∧
        R.Pins (fun x => f x + lam * g x) := by
  refine ⟨{0, 1, 2}, {1, 2, 3}, sharedF, sharedG, 1, sharedRow, {0, 1, 2}, by decide, by decide,
    by decide, dependsOn_sharedF, dependsOn_sharedG, not_isAffineOn_sharedF,
    not_isAffineOn_sharedG, one_ne_zero, by rw [card_sharedTop], ?_, ?_⟩
  · rw [sharedF_add_sharedG, coef_sharedTarget_top]; norm_num
  · rw [sharedF_add_sharedG]; exact sharedRow_pins

/-! ## Obligation 2 is false for gadgets that share variables -/

theorem degLE_mono {ι : Type*} [DecidableEq ι] {F : Type*} [Field F] {T : Finset ι} {d : ℕ}
    (h : T.card ≤ d) : DegLE (mono T : Finset ι → F) d := by
  intro S hS
  rw [coef_mono, if_neg]
  intro hc
  rw [hc] at hS
  omega

/-- The row `x₂ * x₃ = z`. -/
def and2Row : Row (Fin 4) ℚ where
  Az := 0
  A0 := ⟨0, fun i => if i = 2 then 1 else 0⟩
  Bz := 0
  B0 := ⟨0, fun i => if i = 3 then 1 else 0⟩
  Cz := 1
  C0 := ⟨0, fun _ => 0⟩

theorem and2Row_pins : and2Row.Pins (mono {2, 3} : Finset (Fin 4) → ℚ) := by
  have hsat : ∀ (x : Finset (Fin 4)) (z : ℚ),
      and2Row.Sat x z ↔ z = (mono {2, 3} : Finset (Fin 4) → ℚ) x := by
    intro x z
    simp only [and2Row, Row.Sat, Aff.ev, zero_mul, zero_add, one_mul, Finset.sum_const_zero,
      add_zero]
    rw [Finset.sum_ite_eq' x (2 : Fin 4) (fun _ => (1 : ℚ)),
      Finset.sum_ite_eq' x (3 : Fin 4) (fun _ => (1 : ℚ))]
    simp only [mono, Finset.insert_subset_iff, Finset.singleton_subset_iff]
    by_cases h2 : (2 : Fin 4) ∈ x <;> by_cases h3 : (3 : Fin 4) ∈ x <;>
      simp [h2, h3, eq_comm]
  exact ⟨⟨0, fun _ => 0⟩, fun x => (hsat x _).2 rfl, fun x z hz => Or.inl ((hsat x z).1 hz)⟩

/-- **Obligation 2 fails once the blocks share variables.**  Three non-affine gadgets of
multilinear degree `2`, on blocks that are not pairwise disjoint, with nonzero multipliers,
whose packed target is pinned by a single R1CS row: here two of the three gadgets cancel,
which shared variables make possible and disjointness forbids. -/
theorem shared_three_degree_two_gadgets_pack :
    ∃ (P1 P2 P3 : Finset (Fin 4)) (f1 f2 f3 : Finset (Fin 4) → ℚ) (l1 l2 l3 : ℚ)
      (R : Row (Fin 4) ℚ),
      ¬ Disjoint P1 P2 ∧ DependsOn f1 P1 ∧ DependsOn f2 P2 ∧ DependsOn f3 P3 ∧
        DegLE f1 2 ∧ DegLE f2 2 ∧ DegLE f3 2 ∧
        ¬ IsAffineOn f1 ∧ ¬ IsAffineOn f2 ∧ ¬ IsAffineOn f3 ∧
        l1 ≠ 0 ∧ l2 ≠ 0 ∧ l3 ≠ 0 ∧
        R.Pins (fun x => l1 * f1 x + l2 * f2 x + l3 * f3 x) := by
  refine ⟨{0, 1}, {0, 1}, {2, 3}, mono {0, 1}, mono {0, 1}, mono {2, 3}, 1, -1, 1, and2Row,
    by decide, dependsOn_mono (Finset.Subset.refl _), dependsOn_mono (Finset.Subset.refl _),
    dependsOn_mono (Finset.Subset.refl _), degLE_mono (by decide), degLE_mono (by decide),
    degLE_mono (by decide), not_isAffineOn_mono (by decide), not_isAffineOn_mono (by decide),
    not_isAffineOn_mono (by decide), one_ne_zero, by norm_num, one_ne_zero, ?_⟩
  have : (fun x => 1 * (mono {0, 1} : Finset (Fin 4) → ℚ) x + (-1) * mono {0, 1} x
      + 1 * mono {2, 3} x) = (mono {2, 3} : Finset (Fin 4) → ℚ) := by
    funext x; ring
  rw [this]
  exact and2Row_pins

end Solution.Research
