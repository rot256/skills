/-
  Is the minimal R1CS row count of a bilinear map exactly its tensor rank?

  In this cost model a row is one product (A·w)(B·w) = (C·w) with A, B, C affine, and
  affine combinations are FREE. That is precisely the classical model of BILINEAR
  COMPLEXITY: linear operations free, count the multiplications.

  If the correspondence is exact, the entire bilinear-complexity literature -- Strassen,
  Winograd, Alder-Strassen, the matrix-multiplication tensor-rank tables -- becomes
  directly citable as row counts, and constructions there can be imported wholesale.
  If it is only an inequality, we need to know which direction and by how much.
-/
import Mathlib

namespace Solution.Research

variable {F : Type*} [Field F]

/-- **The question.** For a bilinear map `f : F^m → F^n → F^p`, is the minimum number of
    R1CS rows needed to certify `z = f x y` -- with `x`, `y`, `z` the witness and affine
    combinations free -- exactly the tensor rank of `f`?

    Prove both directions, or identify precisely where the correspondence fails.

    UPPER BOUND (rank ⟹ rows) should be the easy direction: a rank-r decomposition
    `f(x,y) = Σ_{k<r} c_k · (u_k ⬝ x) * (v_k ⬝ y)` gives r rows directly, since each
    `u_k ⬝ x` and `v_k ⬝ y` is affine and hence free, and the final recombination is
    affine.

    LOWER BOUND (rows ⟹ rank) is the real content, and the place to be careful:
    R1CS rows may use INTERMEDIATE WITNESSES and may be NONDETERMINISTIC, neither of
    which the classical bilinear model allows. A row's factors may reference witnesses
    pinned by earlier rows, so the products need not be `(affine in x) * (affine in y)`.
    Decide whether that extra power strictly helps. -/
theorem rows_eq_tensor_rank : True := by trivial

end Solution.Research
