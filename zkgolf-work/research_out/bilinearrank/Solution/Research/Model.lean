/-
  # The model: bilinear maps, tensor rank, and nondeterministic R1CS

  This file fixes the two notions that the question compares.

  * `HasRankLE f r` / `tensorRank f` — the classical *bilinear complexity* of a bilinear
    map `f : F^m × F^n → F^p`: the least `r` such that
    `f x y = ∑_{k<r} (φ k x * ψ k y) • w k` with `φ k`, `ψ k` linear forms.
    This is exactly the rank of the associated 3-tensor.

  * `R1CS F m n p` / `minRows f` — the R1CS cost model, formalised so that it is at
    least as strong as anything a real R1CS front-end can do:

    - the witness is `(x, y, u)`: the two inputs together with an arbitrary number
      `aux` of **intermediate witnesses** `u`;
    - each row is one product `(A·w + a) * (B·w + b) = C·w + c` where `A, B, C` are
      *arbitrary* linear forms on the **whole** witness (so a factor may mix `x`, `y`
      and any intermediate witness — nothing is restricted to bilinear shape);
    - the output is an arbitrary **affine** function `Z·w + z₀` of the whole witness,
      charged nothing: affine combinations are free;
    - the system is **nondeterministic**: `Complete` only asks that for every input
      *some* witness satisfies the rows, and `Sound` asks that *every* satisfying
      witness produces the right output. Nothing forces the witness to be computed
      by any circuit, or even to depend algebraically on the input.

    `minRows f` is the least number of rows of such a certificate.
-/
import Mathlib

namespace Solution.Research

open Module

variable {F : Type*} [Field F] {m n p : ℕ}

/-- Coordinate vectors. -/
abbrev Vec (F : Type*) (m : ℕ) := Fin m → F

/-- A bilinear map `F^m × F^n → F^p`. -/
abbrev BilMap (F : Type*) [Field F] (m n p : ℕ) := Vec F m →ₗ[F] Vec F n →ₗ[F] Vec F p

/-! ## Tensor rank -/

/-- `HasRankLE f r`: the map `f` admits a bilinear decomposition with `r` products,
`f x y = ∑_{k < r} (φ k x * ψ k y) • w k`, with all `φ k`, `ψ k` linear forms.  For a
bilinear `f` this says exactly that the associated 3-tensor has rank at most `r`.

The definition is stated for an arbitrary function `f` (bilinearity is not needed to
state it, and this makes intermediate steps easier); it is applied to bilinear maps. -/
def HasRankLE (f : Vec F m → Vec F n → Vec F p) (r : ℕ) : Prop :=
  ∃ (φ : ℕ → (Vec F m →ₗ[F] F)) (ψ : ℕ → (Vec F n →ₗ[F] F)) (w : ℕ → Vec F p),
    ∀ x y, f x y = ∑ k ∈ Finset.range r, (φ k x * ψ k y) • w k

/-- The tensor rank (= classical bilinear complexity) of `f`. -/
noncomputable def tensorRank (f : Vec F m → Vec F n → Vec F p) : ℕ :=
  sInf {r | HasRankLE f r}

/-! ## R1CS systems -/

/-- The full witness of an R1CS system: the two inputs and `s` intermediate witnesses. -/
abbrev Wit (F : Type*) (m n s : ℕ) := Vec F m × Vec F n × Vec F s

/-- An R1CS system with `rows` rows and `aux` intermediate witnesses, over inputs
`F^m × F^n`, producing an output in `F^p` as an affine function of the witness.

Row `k` is the rank-one constraint `(A k · w + a k) * (B k · w + b k) = C k · w + c k`;
the linear forms `A k, B k, C k` may use *any* witness coordinate, including the inputs
and any intermediate witness. -/
structure R1CS (F : Type*) [Field F] (m n p : ℕ) where
  /-- number of intermediate witnesses -/
  aux : ℕ
  /-- number of rows (= the cost) -/
  rows : ℕ
  /-- linear part of the left factor of each row -/
  A : Fin rows → (Wit F m n aux →ₗ[F] F)
  /-- linear part of the right factor of each row -/
  B : Fin rows → (Wit F m n aux →ₗ[F] F)
  /-- linear part of the right-hand side of each row -/
  C : Fin rows → (Wit F m n aux →ₗ[F] F)
  /-- constant part of the left factor of each row -/
  a : Fin rows → F
  /-- constant part of the right factor of each row -/
  b : Fin rows → F
  /-- constant part of the right-hand side of each row -/
  c : Fin rows → F
  /-- linear part of the (free) affine output map -/
  Z : Wit F m n aux →ₗ[F] Vec F p
  /-- constant part of the (free) affine output map -/
  z₀ : Vec F p

namespace R1CS

variable (S : R1CS F m n p)

/-- The witness `w` satisfies all rows. -/
def Sat (w : Wit F m n S.aux) : Prop :=
  ∀ k, (S.A k w + S.a k) * (S.B k w + S.b k) = S.C k w + S.c k

/-- The (free, affine) output of the system on a witness. -/
def out (w : Wit F m n S.aux) : Vec F p := S.Z w + S.z₀

/-- Soundness: *every* witness satisfying the rows yields the value `f x y`. -/
def Sound (f : Vec F m → Vec F n → Vec F p) : Prop :=
  ∀ x y u, S.Sat (x, y, u) → S.out (x, y, u) = f x y

/-- Completeness: for every input *some* witness satisfies the rows. -/
def Complete : Prop := ∀ x y, ∃ u, S.Sat (x, y, u)

/-- `S` certifies `f`: sound and complete. This is the honest notion of "these rows
compute `f`" for a nondeterministic constraint system. -/
def Certifies (f : Vec F m → Vec F n → Vec F p) : Prop := S.Sound f ∧ S.Complete

end R1CS

/-- `HasRowsLE f r`: `f` can be certified by an R1CS system with at most `r` rows. -/
def HasRowsLE (f : Vec F m → Vec F n → Vec F p) (r : ℕ) : Prop :=
  ∃ S : R1CS F m n p, S.rows ≤ r ∧ S.Certifies f

/-- The minimal R1CS row count of `f`. -/
noncomputable def minRows (f : Vec F m → Vec F n → Vec F p) : ℕ :=
  sInf {r | HasRowsLE f r}

/-- Projection of the witness onto its `k`-th intermediate coordinate. -/
def auxProj (F : Type*) [Field F] (m n s : ℕ) (k : Fin s) : Wit F m n s →ₗ[F] F :=
  (LinearMap.proj k) ∘ₗ (LinearMap.snd F (Vec F n) (Vec F s)) ∘ₗ (LinearMap.snd F (Vec F m) _)

/-- Projection of the witness onto its `x` part. -/
def xProj (F : Type*) [Field F] (m n s : ℕ) : Wit F m n s →ₗ[F] Vec F m :=
  LinearMap.fst F (Vec F m) _

/-- Projection of the witness onto its `y` part. -/
def yProj (F : Type*) [Field F] (m n s : ℕ) : Wit F m n s →ₗ[F] Vec F n :=
  (LinearMap.fst F (Vec F n) (Vec F s)) ∘ₗ (LinearMap.snd F (Vec F m) _)

end Solution.Research
