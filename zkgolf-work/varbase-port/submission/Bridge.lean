import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Challenge.Specs.Secp256k1



namespace Solution.Secp256k1ScalarMul
namespace Bridge

open Specs.ShortWeierstrass Specs.Secp256k1


def W : WeierstrassCurve.Affine Fp where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := 0
  a₆ := 7



lemma W_Δ_eq : W.Δ = -21168 := by
  simp only [W, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring


lemma c21168_ne_zero : (21168 : Fp) ≠ 0 := by
  have h : ((21168 : ℕ) : Fp) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hdvd
    have hle : p ≤ 21168 := Nat.le_of_dvd (by norm_num) hdvd
    have hp : 21168 < p := by norm_num [p]
    omega
  simpa using h

lemma W_Δ_ne_zero : W.Δ ≠ 0 := by
  rw [W_Δ_eq]
  exact neg_ne_zero.mpr c21168_ne_zero


lemma equation_of_onCurve {P : Point Fp} (hP : OnCurve curve P) :
    W.Equation P.x P.y := by
  rw [WeierstrassCurve.Affine.equation_iff]
  rw [onCurve_iff] at hP
  simp only [W]
  linear_combination hP


lemma onCurve_of_equation {x y : Fp} (h : W.Equation x y) :
    OnCurve curve { x := x, y := y } := by
  rw [WeierstrassCurve.Affine.equation_iff] at h
  simp only [W] at h
  rw [onCurve_iff]
  linear_combination h




def toSpec : W.Point → GroupPoint Fp
  | .zero => .infinity
  | @WeierstrassCurve.Affine.Point.some _ _ _ x y _ => .affine { x := x, y := y }

@[simp] lemma toSpec_zero : toSpec 0 = .infinity := rfl

@[simp] lemma toSpec_some {x y : Fp} (h : W.Nonsingular x y) :
    toSpec (.some h) = .affine { x := x, y := y } := rfl


def mkPoint (P : Point Fp) (hP : OnCurve curve P) : W.Point :=
  .some ((WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero W_Δ_ne_zero).mp
    (equation_of_onCurve hP))

@[simp] lemma toSpec_mkPoint (P : Point Fp) (hP : OnCurve curve P) :
    toSpec (mkPoint P hP) = .affine P := by
  cases P
  rfl


def fromSpec : (G : GroupPoint Fp) → OnCurveOrInfinity curve G → W.Point
  | .infinity, _ => 0
  | .affine P, h => mkPoint P h

@[simp] lemma toSpec_fromSpec (G : GroupPoint Fp) (h : OnCurveOrInfinity curve G) :
    toSpec (fromSpec G h) = G := by
  cases G with
  | infinity => rfl
  | affine P => exact toSpec_mkPoint P h


lemma toSpec_onCurveOrInfinity (Q : W.Point) : OnCurveOrInfinity curve (toSpec Q) := by
  cases Q with
  | zero => trivial
  | some h =>
    rw [toSpec_some]
    exact onCurve_of_equation h.1

lemma toSpec_injective : Function.Injective toSpec := by
  intro a b hab
  cases a with
  | zero =>
    cases b with
    | zero => rfl
    | some h => simp [toSpec] at hab
  | some ha =>
    cases b with
    | zero => simp [toSpec] at hab
    | some hb =>
      simp only [toSpec_some, GroupPoint.affine.injEq, Point.mk.injEq] at hab
      obtain ⟨hx, hy⟩ := hab
      subst hx; subst hy; rfl




private lemma add_affine (px py qx qy : Fp) :
    add curve (.affine { x := px, y := py }) (.affine { x := qx, y := qy })
      = if px = qx then
          (if py = -qy then .infinity else .affine (tangent curve { x := px, y := py }))
        else .affine (chord { x := px, y := py } { x := qx, y := qy }) := rfl


theorem bridge_add (a b : W.Point) :
    toSpec (a + b) = add curve (toSpec a) (toSpec b) := by
  cases a with
  | zero => rfl
  | some h₁ =>
    cases b with
    | zero => rfl
    | some h₂ =>
      rename_i x₁ y₁ x₂ y₂
      rw [toSpec_some, toSpec_some, add_affine]
      have hneg : W.negY x₂ y₂ = -y₂ := by simp [WeierstrassCurve.Affine.negY, W]
      by_cases hx : x₁ = x₂
      · by_cases hyy : y₁ = W.negY x₂ y₂
        · -- opposite points: both sides are the identity
          rw [WeierstrassCurve.Affine.Point.add_of_Y_eq hx hyy, toSpec_zero,
            if_pos hx, if_pos (hneg ▸ hyy)]
        · -- doubling: the tangent rule
          rw [WeierstrassCurve.Affine.Point.add_of_Y_ne hyy, toSpec_some,
            if_pos hx, if_neg (fun h => hyy (hneg.symm ▸ h))]
          have hslope : W.slope x₁ x₂ y₁ y₂ = 3 * x₁ ^ 2 / (2 * y₁) := by
            simp only [WeierstrassCurve.Affine.slope]
            rw [if_pos hx, if_neg hyy]
            simp only [W, WeierstrassCurve.Affine.negY]
            rw [hx]
            congr 1 <;> ring
          rw [hslope, hx]
          simp only [GroupPoint.affine.injEq, WeierstrassCurve.Affine.addX,
            WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
            WeierstrassCurve.Affine.negY, W, tangent, curve, Point.mk.injEq]
          refine ⟨by ring, by ring⟩
      · -- distinct x: the chord rule
        rw [WeierstrassCurve.Affine.Point.add_of_X_ne hx, toSpec_some, if_neg hx]
        have hslope : W.slope x₁ x₂ y₁ y₂ = (y₂ - y₁) / (x₂ - x₁) := by
          simp only [WeierstrassCurve.Affine.slope]
          rw [if_neg hx, show y₁ - y₂ = -(y₂ - y₁) from by ring,
            show x₁ - x₂ = -(x₂ - x₁) from by ring, neg_div_neg_eq]
        rw [hslope]
        simp only [GroupPoint.affine.injEq, WeierstrassCurve.Affine.addX,
          WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
          WeierstrassCurve.Affine.negY, W, chord, Point.mk.injEq]
        refine ⟨by ring, by ring⟩




theorem add_eq {G H : GroupPoint Fp} (hG : OnCurveOrInfinity curve G)
    (hH : OnCurveOrInfinity curve H) :
    add curve G H = toSpec (fromSpec G hG + fromSpec H hH) := by
  rw [bridge_add, toSpec_fromSpec, toSpec_fromSpec]


theorem add_onCurveOrInfinity {G H : GroupPoint Fp} (hG : OnCurveOrInfinity curve G)
    (hH : OnCurveOrInfinity curve H) :
    OnCurveOrInfinity curve (add curve G H) := by
  rw [add_eq hG hH]
  exact toSpec_onCurveOrInfinity _



private lemma vector_foldl_toList {α β : Type} {m : ℕ} (v : Vector α m)
    (g : β → α → β) (init : β) : v.foldl g init = v.toList.foldl g init := by
  cases v
  simp [Vector.foldl, Array.foldl_toList]


private lemma step_smul (P : Point Fp) (hP : OnCurve curve P) (s : ℕ) (bit : ℕ)
    (hbit : bit < 2) :
    step curve P (toSpec (s • mkPoint P hP)) bit
      = toSpec ((2 * s + bit) • mkPoint P hP) := by
  have hdouble : add curve (toSpec (s • mkPoint P hP)) (toSpec (s • mkPoint P hP))
      = toSpec ((2 * s) • mkPoint P hP) := by
    rw [← bridge_add, ← add_nsmul, two_mul]
  simp only [step]
  by_cases hb1 : bit = 1
  · subst hb1
    rw [if_pos rfl, hdouble, ← toSpec_mkPoint P hP, ← bridge_add, succ_nsmul]
  · rw [if_neg hb1]
    have hb0 : bit = 0 := by omega
    subst hb0
    rw [hdouble, Nat.add_zero]


private lemma list_fold (P : Point Fp) (hP : OnCurve curve P) :
    ∀ (l : List ℕ), (∀ b ∈ l, b < 2) → ∀ (s₀ : ℕ),
      l.foldl (step curve P) (toSpec (s₀ • mkPoint P hP))
        = toSpec ((l.foldl (fun acc bit => 2 * acc + bit) s₀) • mkPoint P hP) := by
  intro l
  induction l with
  | nil => intro _ s₀; rfl
  | cons b t ih =>
    intro hl s₀
    simp only [List.foldl_cons]
    rw [step_smul P hP s₀ b (hl b (List.mem_cons_self ..))]
    exact ih (fun x hx => hl x (List.mem_cons_of_mem b hx)) (2 * s₀ + b)


theorem scalarMul_eq_smul {n : ℕ} (bits : Vector ℕ n) (hbits : IsBitArray bits)
    (P : Point Fp) (hP : OnCurve curve P) :
    scalarMul curve bits P = toSpec (scalarOfBits bits • mkPoint P hP) := by
  have hlist : ∀ b ∈ bits.toList, b < 2 := by
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    rw [Vector.length_toList] at hi
    rw [Vector.getElem_toList]
    exact hbits ⟨i, hi⟩
  have h0 : (GroupPoint.infinity : GroupPoint Fp) = toSpec ((0 : ℕ) • mkPoint P hP) := by
    rw [zero_nsmul, toSpec_zero]
  unfold scalarMul scalarOfBits
  rw [vector_foldl_toList, vector_foldl_toList, h0]
  exact list_fold P hP bits.toList hlist 0




lemma add_nsmul_point (a b : ℕ) (Q : W.Point) : (a + b) • Q = a • Q + b • Q :=
  add_nsmul Q a b


lemma mul_nsmul_point (a b : ℕ) (Q : W.Point) : (a * b) • Q = a • (b • Q) :=
  mul_nsmul' Q a b


lemma two_pow_mul_nsmul_point (k w : ℕ) (Q : W.Point) :
    (2 ^ k * w) • Q = (2 ^ k) • (w • Q) :=
  mul_nsmul' Q (2 ^ k) w


lemma succ_nsmul_point (n : ℕ) (Q : W.Point) : (n + 1) • Q = n • Q + Q :=
  succ_nsmul Q n

end Bridge
end Solution.Secp256k1ScalarMul
