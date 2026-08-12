/-
  # The Strassen corollary

  `matmul2 F` is the multiplication of 2×2 matrices, flattened row-major, as a bilinear
  map `F^4 × F^4 → F^4`.  Strassen's identity is a rank-7 decomposition, so by the upper
  bound it is a **7-row** R1CS certificate, against the 8 rows of the schoolbook
  decomposition.  Since additions are free in this cost model, the crossover is already
  at n = 2: no auxiliary bookkeeping is charged for the extra additions.
-/
import Solution.Research.LowerBound

namespace Solution.Research

open Module

variable {F : Type*} [Field F]

/-- 2×2 matrix multiplication, flattened row-major: entries `0,1,2,3` are
`a₁₁, a₁₂, a₂₁, a₂₂`. -/
def mm2 (F : Type*) [Field F] (x y : Vec F 4) : Vec F 4 :=
  ![x 0 * y 0 + x 1 * y 2, x 0 * y 1 + x 1 * y 3,
    x 2 * y 0 + x 3 * y 2, x 2 * y 1 + x 3 * y 3]

lemma mm2_add_left (x₁ x₂ y : Vec F 4) : mm2 F (x₁ + x₂) y = mm2 F x₁ y + mm2 F x₂ y := by
  funext i; fin_cases i <;> simp [mm2] <;> ring

lemma mm2_smul_left (c : F) (x y : Vec F 4) : mm2 F (c • x) y = c • mm2 F x y := by
  funext i; fin_cases i <;> simp [mm2] <;> ring

lemma mm2_add_right (x y₁ y₂ : Vec F 4) : mm2 F x (y₁ + y₂) = mm2 F x y₁ + mm2 F x y₂ := by
  funext i; fin_cases i <;> simp [mm2] <;> ring

lemma mm2_smul_right (c : F) (x y : Vec F 4) : mm2 F x (c • y) = c • mm2 F x y := by
  funext i; fin_cases i <;> simp [mm2] <;> ring

/-- 2×2 matrix multiplication as a bilinear map. -/
def matmul2 (F : Type*) [Field F] : BilMap F 4 4 4 :=
  LinearMap.mk₂ F (mm2 F) mm2_add_left mm2_smul_left mm2_add_right mm2_smul_right

@[simp] lemma matmul2_apply (x y : Vec F 4) : matmul2 F x y = mm2 F x y := rfl

/-- Coordinate functional on `F⁴`. -/
abbrev pr (F : Type*) [Field F] (i : Fin 4) : Vec F 4 →ₗ[F] F := LinearMap.proj i

/-- **Schoolbook**: 2×2 matrix multiplication has an 8-product decomposition. -/
theorem matmul2_hasRankLE_eight : HasRankLE (fun x y => matmul2 F x y) 8 := by
  refine ⟨fun k => match k with
      | 0 => pr F 0 | 1 => pr F 1 | 2 => pr F 0 | 3 => pr F 1
      | 4 => pr F 2 | 5 => pr F 3 | 6 => pr F 2 | _ => pr F 3,
    fun k => match k with
      | 0 => pr F 0 | 1 => pr F 2 | 2 => pr F 1 | 3 => pr F 3
      | 4 => pr F 0 | 5 => pr F 2 | 6 => pr F 1 | _ => pr F 3,
    fun k => match k with
      | 0 => ![1, 0, 0, 0] | 1 => ![1, 0, 0, 0] | 2 => ![0, 1, 0, 0] | 3 => ![0, 1, 0, 0]
      | 4 => ![0, 0, 1, 0] | 5 => ![0, 0, 1, 0] | 6 => ![0, 0, 0, 1] | _ => ![0, 0, 0, 1],
    fun x y => ?_⟩
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  funext i
  fin_cases i <;> simp [mm2]

/-- **Strassen**: 2×2 matrix multiplication has a 7-product decomposition,

`M₁ = (x₀+x₃)(y₀+y₃)`, `M₂ = (x₂+x₃)y₀`, `M₃ = x₀(y₁-y₃)`, `M₄ = x₃(y₂-y₀)`,
`M₅ = (x₀+x₁)y₃`, `M₆ = (x₂-x₀)(y₀+y₁)`, `M₇ = (x₁-x₃)(y₂+y₃)`,

with `c₁₁ = M₁+M₄-M₅+M₇`, `c₁₂ = M₃+M₅`, `c₂₁ = M₂+M₄`, `c₂₂ = M₁-M₂+M₃+M₆`. -/
theorem matmul2_hasRankLE_seven : HasRankLE (fun x y => matmul2 F x y) 7 := by
  refine ⟨fun k => match k with
      | 0 => pr F 0 + pr F 3
      | 1 => pr F 2 + pr F 3
      | 2 => pr F 0
      | 3 => pr F 3
      | 4 => pr F 0 + pr F 1
      | 5 => pr F 2 - pr F 0
      | _ => pr F 1 - pr F 3,
    fun k => match k with
      | 0 => pr F 0 + pr F 3
      | 1 => pr F 0
      | 2 => pr F 1 - pr F 3
      | 3 => pr F 2 - pr F 0
      | 4 => pr F 3
      | 5 => pr F 0 + pr F 1
      | _ => pr F 2 + pr F 3,
    fun k => match k with
      | 0 => ![1, 0, 0, 1]
      | 1 => ![0, 0, 1, -1]
      | 2 => ![0, 1, 0, 1]
      | 3 => ![1, 0, 1, 0]
      | 4 => ![-1, 1, 0, 0]
      | 5 => ![0, 0, 0, 1]
      | _ => ![1, 0, 0, 0],
    fun x y => ?_⟩
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  funext i
  fin_cases i <;> simp [mm2] <;> ring

/-- The tensor rank of 2×2 matrix multiplication is at most 7. -/
theorem tensorRank_matmul2_le_seven : tensorRank (fun x y => matmul2 F x y) ≤ 7 :=
  tensorRank_le matmul2_hasRankLE_seven

/-- **Strassen as a row count.** 2×2 matrix multiplication is certified by 7 R1CS rows;
the schoolbook algorithm needs 8. Because affine combinations are free, the extra
additions of Strassen's scheme cost nothing, so the saving is unconditional already at
n = 2. -/
theorem minRows_matmul2_le_seven : minRows (fun x y => matmul2 F x y) ≤ 7 :=
  minRows_le (hasRowsLE_of_hasRankLE matmul2_hasRankLE_seven)

/-- The explicit 7-row R1CS system for 2×2 matrix multiplication. -/
theorem exists_seven_row_matmul2_system :
    ∃ S : R1CS F 4 4 4, S.rows = 7 ∧ S.Certifies (fun x y => matmul2 F x y) :=
  certifies_of_hasRankLE _ 7 matmul2_hasRankLE_seven

end Solution.Research
