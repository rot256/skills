import Solution.Secp256k1ScalarMul.GLVVerifierTheorems

/-!
# Group algebra of the lazy chain with all-odd digits

The lazy chain starts at the all-plus table entry `Σ_j B_j` and performs 64
steps `R ← 2R + E(pattern)`, where `E(b) = Σ_j (2 b_j − 1) B_j` is the
sign-pattern entry selected by the four magnitude bits at that position.  The
result is `Σ_j (2 c_j + 1) B_j`; asserting that it equals the all-plus entry
again forces `2 · Σ_j c_j B_j = 0`, hence `Σ_j c_j B_j = 0` (no 2-torsion).
-/

namespace Solution.Secp256k1ScalarMul.LazyChain

open Specs.ShortWeierstrass Specs.Secp256k1
open GLVMSMTheorems

/-- Signed pick: `+P` for a set bit, `−P` for a clear bit. -/
def pickS (b : Bool) (P : Bridge.W.Point) : Bridge.W.Point := if b then P else -P

/-- The sign-pattern entry `Σ_j ± B_j` of pattern `t` (bit `j` set means `+B_j`). -/
def patW (B : Fin 4 → Bridge.W.Point) (t : ℕ) : Bridge.W.Point :=
  (pickS (decide (t / 2 ^ 0 % 2 = 1)) (B 0) + pickS (decide (t / 2 ^ 1 % 2 = 1)) (B 1)) +
    (pickS (decide (t / 2 ^ 2 % 2 = 1)) (B 2) + pickS (decide (t / 2 ^ 3 % 2 = 1)) (B 3))

/-- `Σ_j (2 a_j + 1) B_j`. -/
def oddComb (B : Fin 4 → Bridge.W.Point) (a0 a1 a2 a3 : ℕ) : Bridge.W.Point :=
  ((2 * (a0 : ℤ) + 1) • B 0 + (2 * (a1 : ℤ) + 1) • B 1) +
    ((2 * (a2 : ℤ) + 1) • B 2 + (2 * (a3 : ℤ) + 1) • B 3)

lemma val_one : ((1 : F circomPrime).val) = 1 := by
  change (((1 : ℕ) : F circomPrime).val) = 1
  exact ZMod.val_natCast_of_lt (by decide)

lemma patW_nibble {b0 b1 b2 b3 : F circomPrime}
    (h0 : IsBool b0) (h1 : IsBool b1) (h2 : IsBool b2) (h3 : IsBool b3)
    (B : Fin 4 → Bridge.W.Point) :
    patW B (8 * b3.val + 4 * b2.val + 2 * b1.val + b0.val) =
      ((2 * (b0.val : ℤ) - 1) • B 0 + (2 * (b1.val : ℤ) - 1) • B 1) +
        ((2 * (b2.val : ℤ) - 1) • B 2 + (2 * (b3.val : ℤ) - 1) • B 3) := by
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;>
    rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;>
    subst_vars <;> simp [patW, pickS, val_one]

lemma patW_fifteen (B : Fin 4 → Bridge.W.Point) : patW B 15 = oddComb B 0 0 0 0 := by
  simp [patW, pickS, oddComb]

lemma oddComb_eq_two_linComb (B : Fin 4 → Bridge.W.Point) (a0 a1 a2 a3 : ℕ) :
    oddComb B a0 a1 a2 a3 = 2 • linComb B a0 a1 a2 a3 + patW B 15 := by
  simp only [oddComb, linComb, patW, pickS, decide_true, if_true, add_zsmul, one_zsmul,
    two_zsmul, mul_zsmul, natCast_zsmul, smul_add]
  simp
  abel

private lemma odd_step (s b : ℤ) (P : Bridge.W.Point) :
    (2 * (2 * s + b) + 1) • P = (2 * s + 1) • P + (2 * s + 1) • P + (2 * b - 1) • P := by
  rw [← add_zsmul, ← add_zsmul]
  congr 1
  ring

lemma oddComb_step (B : Fin 4 → Bridge.W.Point) (s0 s1 s2 s3 b0 b1 b2 b3 : ℕ) :
    oddComb B (2 * s0 + b0) (2 * s1 + b1) (2 * s2 + b2) (2 * s3 + b3) =
      oddComb B s0 s1 s2 s3 + oddComb B s0 s1 s2 s3 +
        (((2 * (b0 : ℤ) - 1) • B 0 + (2 * (b1 : ℤ) - 1) • B 1) +
          ((2 * (b2 : ℤ) - 1) • B 2 + (2 * (b3 : ℤ) - 1) • B 3)) := by
  unfold oddComb
  push_cast
  rw [odd_step, odd_step, odd_step, odd_step]
  abel

/-! ### The chain recursion on decoded points -/

/-- Sign-pattern table: entry `i` decodes to `Σ_j ± B_j` with the signs given by
the bits of `i`. -/
def PatTableFor (input : GLVMSM.Inputs (F circomPrime)) (B : Fin 4 → Bridge.W.Point) : Prop :=
  ∀ i : Fin 16,
    decodePoint (GLVMSM.tableEntry input i.val i.isLt) = Bridge.toSpec (patW B i.val)

/-- Accumulator after `k` steps: seed `E(1111)`, then `R ← 2R + E(nibble_k)`. -/
def chainAcc (input : GLVMSM.Inputs (F circomPrime)) : ℕ → GroupPoint Fp
  | 0 => decodePoint (GLVMSM.tableEntry input 15 (by norm_num))
  | k + 1 =>
      if hk : k < GLVMSM.coeffBits then
        add curve (add curve (chainAcc input k) (chainAcc input k))
          (GLVMSM.selectedAt input k hk)
      else chainAcc input k

lemma selectedAt_pat (input : GLVMSM.Inputs (F circomPrime))
    (B : Fin 4 → Bridge.W.Point)
    (hall : GLVMSM.Assumptions input) (htable : PatTableFor input B)
    (k : ℕ) (hk : k < GLVMSM.coeffBits) :
    GLVMSM.selectedAt input k hk =
      Bridge.toSpec
        (((2 * ((input.m0[GLVMSM.coeffBits - 1 - k]'(by
            simp only [GLVMSM.coeffBits] at hk ⊢; omega)).val : ℤ) - 1) • B 0 +
          (2 * ((input.m1[GLVMSM.coeffBits - 1 - k]'(by
            simp only [GLVMSM.coeffBits] at hk ⊢; omega)).val : ℤ) - 1) • B 1) +
         ((2 * ((input.m2[GLVMSM.coeffBits - 1 - k]'(by
            simp only [GLVMSM.coeffBits] at hk ⊢; omega)).val : ℤ) - 1) • B 2 +
          (2 * ((input.m3[GLVMSM.coeffBits - 1 - k]'(by
            simp only [GLVMSM.coeffBits] at hk ⊢; omega)).val : ℤ) - 1) • B 3)) := by
  obtain ⟨_, _, hm0, hm1, hm2, hm3⟩ := hall
  have h0 := hm0 ⟨GLVMSM.coeffBits - 1 - k, by simp only [GLVMSM.coeffBits] at hk ⊢; omega⟩
  have h1 := hm1 ⟨GLVMSM.coeffBits - 1 - k, by simp only [GLVMSM.coeffBits] at hk ⊢; omega⟩
  have h2 := hm2 ⟨GLVMSM.coeffBits - 1 - k, by simp only [GLVMSM.coeffBits] at hk ⊢; omega⟩
  have h3 := hm3 ⟨GLVMSM.coeffBits - 1 - k, by simp only [GLVMSM.coeffBits] at hk ⊢; omega⟩
  have hn : GLVMSM.nibbleAt input k hk < 16 := by
    unfold GLVMSM.nibbleAt
    rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;>
      rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;>
      simp_all [val_one]
  unfold GLVMSM.selectedAt
  rw [dif_pos hn, htable ⟨_, hn⟩]
  unfold GLVMSM.nibbleAt
  exact congrArg Bridge.toSpec (patW_nibble h0 h1 h2 h3 B)

theorem chainAcc_eq (input : GLVMSM.Inputs (F circomPrime))
    (B : Fin 4 → Bridge.W.Point)
    (hall : GLVMSM.Assumptions input) (htable : PatTableFor input B) :
    ∀ k, k ≤ GLVMSM.coeffBits →
      chainAcc input k =
        Bridge.toSpec
          (oddComb B (scanValue input.m0 k) (scanValue input.m1 k)
            (scanValue input.m2 k) (scanValue input.m3 k)) := by
  intro k
  induction k with
  | zero =>
      intro _
      simp only [chainAcc, scanValue, List.take_zero, List.foldl_nil]
      rw [htable ⟨15, by norm_num⟩, patW_fifteen]
  | succ k ih =>
      intro hle
      have hk : k < GLVMSM.coeffBits := by omega
      rw [chainAcc, dif_pos hk, ih (by omega), selectedAt_pat input B hall htable k hk]
      rw [← Bridge.bridge_add, ← Bridge.bridge_add]
      apply congrArg Bridge.toSpec
      rw [scanValue_succ input.m0 k hk, scanValue_succ input.m1 k hk,
        scanValue_succ input.m2 k hk, scanValue_succ input.m3 k hk]
      exact (oddComb_step B _ _ _ _ _ _ _ _).symm

theorem chainAcc_final (input : GLVMSM.Inputs (F circomPrime))
    (B : Fin 4 → Bridge.W.Point)
    (hall : GLVMSM.Assumptions input) (htable : PatTableFor input B) :
    chainAcc input GLVMSM.coeffBits =
      Bridge.toSpec
        (oddComb B
          (scalarOfBits ((input.m0.map ZMod.val).reverse))
          (scalarOfBits ((input.m1.map ZMod.val).reverse))
          (scalarOfBits ((input.m2.map ZMod.val).reverse))
          (scalarOfBits ((input.m3.map ZMod.val).reverse))) := by
  rw [chainAcc_eq input B hall htable GLVMSM.coeffBits (le_refl _)]
  simp only [scanValue_final]

/-! ### No 2-torsion -/

theorem eq_zero_of_two_smul (L : Bridge.W.Point) (h : L + L = 0) : L = 0 := by
  cases L with
  | zero => rfl
  | @some x y hxy =>
      exfalso
      have hspec := congrArg Bridge.toSpec h
      rw [Bridge.bridge_add, Bridge.toSpec_some, Bridge.toSpec_zero] at hspec
      have hon : OnCurve curve ({ x := x, y := y } : Point Fp) := Bridge.onCurve_of_equation hxy.1
      have h2 := FusedStepTheorems.two_y_ne_zero hon
      simp only [add, if_pos rfl] at hspec
      by_cases hy : y = -y
      · exact h2 (by linear_combination hy)
      · rw [if_neg hy] at hspec
        cases hspec

theorem linComb_eq_zero_of_chain (B : Fin 4 → Bridge.W.Point) (a0 a1 a2 a3 : ℕ)
    (h : oddComb B a0 a1 a2 a3 = patW B 15) : linComb B a0 a1 a2 a3 = 0 := by
  rw [oddComb_eq_two_linComb] at h
  have h2 : (2 : ℕ) • linComb B a0 a1 a2 a3 = 0 :=
    add_right_cancel (h.trans (zero_add (patW B 15)).symm)
  rw [two_smul] at h2
  exact eq_zero_of_two_smul _ h2

end Solution.Secp256k1ScalarMul.LazyChain

/-! ### Special scalars -/

namespace Solution.Secp256k1ScalarMul.LazyChain

open Specs.ShortWeierstrass Specs.Secp256k1

/-- A nonzero point has prime order, so a vanishing multiple has a vanishing scalar. -/
lemma cast_eq_zero_of_zsmul_eq_zero (a : ℤ) (P : Bridge.W.Point) (hP : P ≠ 0)
    (h : a • P = 0) : (a : ZMod order) = 0 := by
  have hord : addOrderOf P = order :=
    addOrderOf_eq_prime (GLVFinal.order_nsmul_all P) hP
  have hdvd : ((addOrderOf P : ℕ) : ℤ) ∣ a := addOrderOf_dvd_iff_zsmul_eq_zero.mpr h
  rw [hord] at hdvd
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd a order).mpr hdvd

/-- Sign value of a pattern bit. -/
def sgn (b : Bool) : ℤ := if b then 1 else -1

lemma pickS_eq_sgn (b : Bool) (P : Bridge.W.Point) : pickS b P = sgn b • P := by
  cases b <;> simp [pickS, sgn]

/-- Scalar of the pattern entry `E(t)` of the signed bases `σ_j B_j`,
`B = (P, φP, kP, φ(kP))`, as a multiple of `P`. -/
def patScalar (σ : Fin 4 → ℤ) (k : ℕ) (t : ℕ) : ℤ :=
  sgn (decide (t / 2 ^ 0 % 2 = 1)) * σ 0 +
    (GLVAlgebra.lambda : ℤ) * (sgn (decide (t / 2 ^ 1 % 2 = 1)) * σ 1) +
    (k : ℤ) * (sgn (decide (t / 2 ^ 2 % 2 = 1)) * σ 2 +
      (GLVAlgebra.lambda : ℤ) * (sgn (decide (t / 2 ^ 3 % 2 = 1)) * σ 3))

def glvBases (P : Bridge.W.Point) (k : ℕ) (σ : Fin 4 → ℤ) : Fin 4 → Bridge.W.Point
  | ⟨0, _⟩ => σ 0 • P
  | ⟨1, _⟩ => σ 1 • Phi.hom P
  | ⟨2, _⟩ => σ 2 • (k • P)
  | ⟨3, _⟩ => σ 3 • Phi.hom (k • P)

lemma patW_bases (P : Bridge.W.Point) (k : ℕ) (σ : Fin 4 → ℤ) (t : ℕ) :
    patW (glvBases P k σ) t = patScalar σ k t • P := by
  unfold patW patScalar
  simp only [pickS_eq_sgn, glvBases]
  rw [GLVFinal.hom_eq_lambda_nsmul, GLVFinal.hom_eq_lambda_nsmul,
    ← GLVAlgebra.natCast_zsmul_eq_nsmul, ← GLVAlgebra.natCast_zsmul_eq_nsmul,
    ← GLVAlgebra.natCast_zsmul_eq_nsmul]
  simp only [smul_smul]
  rw [← add_zsmul, ← add_zsmul, ← add_zsmul]
  congr 1
  ring

/-- A vanishing pattern entry forces the pattern scalar to vanish modulo the order. -/
lemma patScalar_cast_eq_zero (P : Bridge.W.Point) (hP : P ≠ 0) (k : ℕ) (σ : Fin 4 → ℤ)
    (t : ℕ) (h : patW (glvBases P k σ) t = 0) : (patScalar σ k t : ZMod order) = 0 := by
  rw [patW_bases] at h
  exact cast_eq_zero_of_zsmul_eq_zero _ P hP h

end Solution.Secp256k1ScalarMul.LazyChain
