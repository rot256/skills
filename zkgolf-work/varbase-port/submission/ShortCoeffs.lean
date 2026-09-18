import Solution.Secp256k1ScalarMul.Bridge
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Lemmas

namespace Solution.Secp256k1ScalarMul.ShortCoeffs

open Specs.Secp256k1

def lambdaZ : ℤ :=
  37718080363155996902926221483475020450927657555482586988616620542887997980018

def a₁ : ℤ := 64502973549206556628585045361533709077
def b₁ : ℤ := -303414439467246543595250775667605759171
def a₂ : ℤ := 367917413016453100223835821029139468248
def b₂ : ℤ := a₁

def q₁ : ℤ := -98834128363575826231712400374302886273
def q₂ : ℤ := 21011179226632705335158493575954588082

def coeffBound : ℕ := 2 ^ 64

lemma lattice_relation₁ : a₁ + lambdaZ * b₁ = q₁ * (order : ℤ) := by
  norm_num [a₁, b₁, lambdaZ, q₁, order]

lemma lattice_relation₂ : a₂ + lambdaZ * b₂ = q₂ * (order : ℤ) := by
  norm_num [a₂, b₂, a₁, lambdaZ, q₂, order]

lemma lattice_determinant : a₁ * b₂ - a₂ * b₁ = (order : ℤ) := by
  norm_num [a₁, b₁, a₂, b₂, order]

private lemma bounds_of_natAbs_lt {z : ℤ} (hz : z.natAbs < coeffBound) :
    -(coeffBound : ℤ) < z ∧ z < (coeffBound : ℤ) := by
  rw [← abs_lt]
  rw [← Int.natCast_natAbs]
  exact_mod_cast hz

private lemma first_combination_small {x y : ℤ}
    (hx : x.natAbs < coeffBound) (hy : y.natAbs < coeffBound) :
    |b₂ * x - a₂ * y| < (order : ℤ) := by
  obtain ⟨hxl, hxu⟩ := bounds_of_natAbs_lt hx
  obtain ⟨hyl, hyu⟩ := bounds_of_natAbs_lt hy
  rw [abs_lt]
  norm_num [b₂, a₁, a₂, coeffBound, order] at hxl hxu hyl hyu ⊢
  constructor <;> omega

private lemma second_combination_small {x y : ℤ}
    (hx : x.natAbs < coeffBound) (hy : y.natAbs < coeffBound) :
    |-b₁ * x + a₁ * y| < (order : ℤ) := by
  obtain ⟨hxl, hxu⟩ := bounds_of_natAbs_lt hx
  obtain ⟨hyl, hyu⟩ := bounds_of_natAbs_lt hy
  rw [abs_lt]
  norm_num [b₁, a₁, coeffBound, order] at hxl hxu hyl hyu ⊢
  constructor <;> omega


theorem short_kernel {x y : ℤ}
    (hx : x.natAbs < coeffBound) (hy : y.natAbs < coeffBound)
    (hxy : (x : ZMod order) + (lambdaZ : ZMod order) * (y : ZMod order) = 0) :
    x = 0 ∧ y = 0 := by
  have hcast : ((x + lambdaZ * y : ℤ) : ZMod order) = 0 := by
    simpa only [Int.cast_add, Int.cast_mul] using hxy
  have hd : (order : ℤ) ∣ x + lambdaZ * y :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hcast
  obtain ⟨t, ht⟩ := hd
  have hd₁ : (order : ℤ) ∣ b₂ * x - a₂ * y := by
    refine ⟨b₂ * t - q₂ * y, ?_⟩
    calc
      b₂ * x - a₂ * y =
          b₂ * (x + lambdaZ * y) - y * (a₂ + lambdaZ * b₂) := by ring
      _ = b₂ * ((order : ℤ) * t) - y * (q₂ * (order : ℤ)) := by
        rw [ht, lattice_relation₂]
      _ = (order : ℤ) * (b₂ * t - q₂ * y) := by ring
  have hd₂ : (order : ℤ) ∣ -b₁ * x + a₁ * y := by
    refine ⟨-b₁ * t + q₁ * y, ?_⟩
    calc
      -b₁ * x + a₁ * y =
          -b₁ * (x + lambdaZ * y) + y * (a₁ + lambdaZ * b₁) := by ring
      _ = -b₁ * ((order : ℤ) * t) + y * (q₁ * (order : ℤ)) := by
        rw [ht, lattice_relation₁]
      _ = (order : ℤ) * (-b₁ * t + q₁ * y) := by ring
  have he₁ : b₂ * x - a₂ * y = 0 :=
    Int.eq_zero_of_abs_lt_dvd hd₁ (first_combination_small hx hy)
  have he₂ : -b₁ * x + a₁ * y = 0 :=
    Int.eq_zero_of_abs_lt_dvd hd₂ (second_combination_small hx hy)
  have hnx : (order : ℤ) * x = 0 := by
    rw [← lattice_determinant]
    linear_combination a₁ * he₁ + a₂ * he₂
  have hx0 : x = 0 := (mul_eq_zero.mp hnx).resolve_left (by norm_num [order])
  subst x
  have hy0 : y = 0 := by
    dsimp [b₂, a₁, a₂] at he₁
    have hm : 367917413016453100223835821029139468248 * y = 0 := by
      linear_combination -he₁
    exact (mul_eq_zero.mp hm).resolve_left (by norm_num)
  exact ⟨rfl, hy0⟩

def pigeonBound : ℕ := 2 ^ 64

structure Quad where
  u₁ : Fin pigeonBound
  u₂ : Fin pigeonBound
  v₁ : Fin pigeonBound
  v₂ : Fin pigeonBound
deriving DecidableEq

def quadEquiv : Quad ≃
    Fin pigeonBound × Fin pigeonBound × Fin pigeonBound × Fin pigeonBound where
  toFun q := (q.u₁, q.u₂, q.v₁, q.v₂)
  invFun q := ⟨q.1, q.2.1, q.2.2.1, q.2.2.2⟩
  left_inv q := by cases q; rfl
  right_inv q := by rcases q with ⟨a, b, c, d⟩; rfl

instance : Fintype Quad := Fintype.ofEquiv
  (Fin pigeonBound × Fin pigeonBound × Fin pigeonBound × Fin pigeonBound) quadEquiv.symm

def residue (k : ZMod order) (c : Quad) : ZMod order :=
  c.u₁.val + (lambdaZ : ZMod order) * c.u₂.val +
    k * (c.v₁.val + (lambdaZ : ZMod order) * c.v₂.val)

private lemma residue_not_injective (k : ZMod order) :
    ¬ Function.Injective (residue k) := by
  letI : NeZero order := ⟨by norm_num [order]⟩
  intro hinj
  have hc := Fintype.card_le_of_injective (residue k) hinj
  have hquad : Fintype.card Quad = pigeonBound ^ 4 := by
    rw [Fintype.card_congr quadEquiv]
    simp [pow_succ, mul_assoc]
  rw [hquad, ZMod.card] at hc
  norm_num [pigeonBound, order] at hc

def diffU₁ (a b : Quad) : ℤ := (a.u₁.val : ℤ) - b.u₁.val
def diffU₂ (a b : Quad) : ℤ := (a.u₂.val : ℤ) - b.u₂.val
def diffV₁ (a b : Quad) : ℤ := (a.v₁.val : ℤ) - b.v₁.val
def diffV₂ (a b : Quad) : ℤ := (a.v₂.val : ℤ) - b.v₂.val

private lemma diff_bound (a b : Fin pigeonBound) :
    ((a.val : ℤ) - b.val).natAbs < coeffBound := by
  simpa only [coeffBound, pigeonBound] using
    Int.natAbs_coe_sub_coe_lt_of_lt a.isLt b.isLt

private lemma residue_collision_relation {k : ZMod order} {a b : Quad}
    (h : residue k a = residue k b) :
    (diffU₁ a b : ZMod order) + (lambdaZ : ZMod order) * diffU₂ a b +
      k * ((diffV₁ a b : ZMod order) + (lambdaZ : ZMod order) * diffV₂ a b) = 0 := by
  dsimp [residue, diffU₁, diffU₂, diffV₁, diffV₂] at h ⊢
  simp only [Int.cast_sub, Int.cast_natCast]
  linear_combination h

private lemma quad_eq_of_diffs_zero {a b : Quad}
    (hu₁ : diffU₁ a b = 0) (hu₂ : diffU₂ a b = 0)
    (hv₁ : diffV₁ a b = 0) (hv₂ : diffV₂ a b = 0) : a = b := by
  rcases a with ⟨au₁, au₂, av₁, av₂⟩
  rcases b with ⟨bu₁, bu₂, bv₁, bv₂⟩
  congr <;> apply Fin.ext
  all_goals dsimp [diffU₁, diffU₂, diffV₁, diffV₂] at * <;> omega

structure Decomposition (k : ZMod order) where
  u₁ : ℤ
  u₂ : ℤ
  v₁ : ℤ
  v₂ : ℤ
  u₁_bound : u₁.natAbs < coeffBound
  u₂_bound : u₂.natAbs < coeffBound
  v₁_bound : v₁.natAbs < coeffBound
  v₂_bound : v₂.natAbs < coeffBound
  relation : (u₁ : ZMod order) + (lambdaZ : ZMod order) * u₂ +
    k * ((v₁ : ZMod order) + (lambdaZ : ZMod order) * v₂) = 0
  v_nonzero : v₁ ≠ 0 ∨ v₂ ≠ 0
  /-- Negating all four coefficients negates the relation, which still holds,
  and negates the accumulated point, which is at infinity iff its negation is.
  So the first coefficient may always be taken non-negative. -/
  u₁_nonneg : 0 ≤ u₁


theorem exists_decomposition (k : ZMod order) : Nonempty (Decomposition k) := by
  obtain ⟨a, b, hab, hne⟩ := Function.not_injective_iff.mp (residue_not_injective k)
  let u₁ := diffU₁ a b
  let u₂ := diffU₂ a b
  let v₁ := diffV₁ a b
  let v₂ := diffV₂ a b
  have hu₁b : u₁.natAbs < coeffBound := diff_bound a.u₁ b.u₁
  have hu₂b : u₂.natAbs < coeffBound := diff_bound a.u₂ b.u₂
  have hv₁b : v₁.natAbs < coeffBound := diff_bound a.v₁ b.v₁
  have hv₂b : v₂.natAbs < coeffBound := diff_bound a.v₂ b.v₂
  have hrel := residue_collision_relation hab
  have hvne : v₁ ≠ 0 ∨ v₂ ≠ 0 := by
    by_contra hn
    push_neg at hn
    obtain ⟨hv₁, hv₂⟩ := hn
    have hurel : (u₁ : ZMod order) + (lambdaZ : ZMod order) * u₂ = 0 := by
      dsimp [u₁, u₂, v₁, v₂] at hv₁ hv₂ hrel ⊢
      rw [hv₁, hv₂] at hrel
      simpa using hrel
    obtain ⟨hu₁, hu₂⟩ := short_kernel hu₁b hu₂b hurel
    apply hne
    exact quad_eq_of_diffs_zero hu₁ hu₂ hv₁ hv₂
  by_cases hsign : 0 ≤ u₁
  · exact ⟨⟨u₁, u₂, v₁, v₂, hu₁b, hu₂b, hv₁b, hv₂b, hrel, hvne, hsign⟩⟩
  · refine ⟨⟨-u₁, -u₂, -v₁, -v₂, ?_, ?_, ?_, ?_, ?_, ?_, by omega⟩⟩
    · simpa using hu₁b
    · simpa using hu₂b
    · simpa using hv₁b
    · simpa using hv₂b
    · push_cast
      linear_combination -hrel
    · rcases hvne with h | h
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)

end Solution.Secp256k1ScalarMul.ShortCoeffs
