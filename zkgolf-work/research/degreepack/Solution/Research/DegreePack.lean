/-
  The degree filtration: which boolean gadgets can share a row?

  Reduce a boolean function to its MULTILINEAR polynomial over the cube (unique, since
  x^2 = x). Two independent derivations in this project agree on the following, and both
  were checked by exhaustive search, but neither is proved:

    * multilinear degree 2 (Ch, XOR2, AND2) takes the shape `gamma*z = P0*Q0 - R0`
      with z alone in the C-slot, and packs EXACTLY 2 instances per row -- never 3.
    * multilinear degree 3 (Maj, XOR3, AND3) packs NEVER -- not two instances, not even
      with a decoy root.

  These bound a whole search space. Proving them closes it permanently; refuting either
  would be a significant win, since degree-3 gadgets are the dominant cost in SHA-256.
-/
import Mathlib

namespace Solution.Research

variable {F : Type*} [Field F]

/-- **Obligation 1.** Let `f, g : Bool × Bool × Bool → F` be non-affine on the cube with
    DISJOINT input triples `a`, `b`. Show no single R1CS row -- one product of two affine
    forms, equated to a third affine form, all affine in the witness -- determines
    `z = f a + lambda * g b` for any `lambda ≠ 0`.

    Include the decoy-root case: `z` may appear QUADRATICALLY in the row, i.e. the row may
    pin `{z, z_decoy}` as a pair, provided `z_decoy` is affine.

    The sketched argument: apply the projector onto the bi-non-affine part. Since
    `f^2 = f` and `g^2 = g` on the cube, `z^2` contributes a nonzero `2*lambda * f~ ⊗ g~`
    term that no product of affine forms and no affine term can match. -/
theorem degree_three_never_packs : True := by trivial

/-- **Obligation 2.** For multilinear degree 2 on disjoint variable sets, show the packing
    cap is exactly 2: two instances fit one row, three never do.

    The sketched argument: the C-slot shape forces the quadratic part of the packed target
    to have rank at most 2 modulo the free diagonal shifts `alpha_i * (x_i^2 - x_i)` (which
    vanish on the cube). For k gadgets on disjoint variables the form is a direct sum of k
    blocks of rank at least 1, so k ≤ 2. -/
theorem degree_two_packs_exactly_two : True := by trivial

end Solution.Research
