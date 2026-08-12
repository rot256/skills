/-
  # The cost model for range checks

  A *row* is one rank-1 constraint `(A ⬝ v) * (B ⬝ v) = (C ⬝ v)` where `A`, `B`, `C`
  are affine forms in the public input `x` and the witness vector `w : Fin m → F`.
  Affine combinations are free: they are not rows, they are just the forms `A`, `B`, `C`.

  The *score* of a system is `m + r` (allocations + constraints).

  A system *certifies the `n`-bit range* if, for every `x : F`, the system is
  satisfiable at `x` exactly when `x` is the image of a natural number `< 2 ^ n`.
  Note carefully what this quantifies over: the witnesses are arbitrary field
  elements, nothing forces them to be bits, and the rows are arbitrary rank-1
  constraints.  Nothing about the standard bit decomposition is baked in.
-/
import Mathlib

namespace Solution.Research

variable {F : Type*} [Field F] {m r : ℕ}

/-- An affine form in the public input `x` and the `m` witness variables:
    `cx * x + ∑ i, cw i * w i + c`. -/
structure Aff (F : Type*) (m : ℕ) where
  /-- coefficient of the public input -/
  cx : F
  /-- coefficients of the witness variables -/
  cw : Fin m → F
  /-- constant term -/
  c : F

/-- Value of an affine form at a public input and a witness vector. -/
def Aff.eval (L : Aff F m) (x : F) (w : Fin m → F) : F :=
  L.cx * x + (∑ i, L.cw i * w i) + L.c

/-- One R1CS row: `(A ⬝ v) * (B ⬝ v) = (C ⬝ v)`. -/
structure Row (F : Type*) (m : ℕ) where
  /-- left factor -/
  A : Aff F m
  /-- right factor -/
  B : Aff F m
  /-- right-hand side -/
  C : Aff F m

/-- The row is satisfied at `(x, w)`. -/
def Row.Holds (R : Row F m) (x : F) (w : Fin m → F) : Prop :=
  R.A.eval x w * R.B.eval x w = R.C.eval x w

/-- A system of `r` rows over `m` witness variables (plus the public input `x`). -/
structure System (F : Type*) (m r : ℕ) where
  /-- the rows -/
  row : Fin r → Row F m

/-- The system is satisfiable at the public input `x`. -/
def System.Sat (S : System F m r) (x : F) : Prop :=
  ∃ w : Fin m → F, ∀ j, (S.row j).Holds x w

/-- The set of `x : F` at which the system is satisfiable. -/
def System.solutions (S : System F m r) : Set F := {x | S.Sat x}

/-- Score of a system: allocations plus constraints. -/
def System.score (_S : System F m r) : ℕ := m + r

/-- The values a genuine `n`-bit range check must accept: images in `F` of the
    naturals `< 2 ^ n`. -/
def RangeSet (F : Type*) [Field F] (n : ℕ) : Set F := {x : F | ∃ k : ℕ, k < 2 ^ n ∧ x = (k : F)}

/-- **What it means to certify an `n`-bit range.**  The system, viewed as a predicate on
    the public input `x`, is satisfiable exactly on the `n`-bit values.  Soundness is the
    forward direction, completeness the backward one. -/
def System.Certifies (S : System F m r) (n : ℕ) : Prop :=
  ∀ x : F, S.Sat x ↔ x ∈ RangeSet F n

omit [Field F] in
@[simp] theorem System.score_eq (S : System F m r) : S.score = m + r := rfl

theorem Aff.eval_def (L : Aff F m) (x : F) (w : Fin m → F) :
    L.eval x w = L.cx * x + (∑ i, L.cw i * w i) + L.c := rfl

end Solution.Research
