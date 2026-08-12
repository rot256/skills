/-
  # Upper bound: rank ⟹ rows

  A rank-`r` bilinear decomposition `f x y = ∑_{k<r} (φ k x * ψ k y) • w k` is turned
  into an R1CS certificate with exactly `r` rows: allocate one intermediate witness
  `u k` per product, constrain `(φ k · x) * (ψ k · y) = u k`, and read the output off
  as the free affine combination `∑ k, u k • w k`.

  Consequently `minRows f ≤ tensorRank f`: every construction from the bilinear
  complexity literature imports as a row count.
-/
import Solution.Research.RankCalculus

namespace Solution.Research

open Module

variable {F : Type*} [Field F] {m n p : ℕ}

/-- **Upper bound.** A rank-`r` decomposition gives an R1CS certificate with `r` rows. -/
theorem certifies_of_hasRankLE (f : Vec F m → Vec F n → Vec F p) (r : ℕ) (h : HasRankLE f r) :
    ∃ S : R1CS F m n p, S.rows = r ∧ S.Certifies f := by
  obtain ⟨φ, ψ, w, hf⟩ := h
  classical
  refine ⟨{ aux := r, rows := r
            A := fun k => φ k ∘ₗ xProj F m n r
            B := fun k => ψ k ∘ₗ yProj F m n r
            C := fun k => auxProj F m n r k
            a := 0, b := 0, c := 0
            Z := ∑ k : Fin r, LinearMap.smulRight (auxProj F m n r k) (w k)
            z₀ := 0 }, rfl, ?_, ?_⟩
  · intro x y u hs
    simp only [R1CS.Sat, auxProj, xProj, yProj, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.proj_apply, LinearMap.snd_apply, LinearMap.fst_apply, Pi.zero_apply,
      add_zero] at hs
    simp only [R1CS.out, LinearMap.sum_apply, LinearMap.smulRight_apply, auxProj,
      LinearMap.coe_comp, Function.comp_apply, LinearMap.proj_apply, LinearMap.snd_apply,
      add_zero]
    rw [hf x y, ← Fin.sum_univ_eq_sum_range (fun k => (φ k x * ψ k y) • w k) r]
    exact Finset.sum_congr rfl fun k _ => by rw [hs k]
  · refine fun x y => ⟨fun k => φ k x * ψ k y, fun k => ?_⟩
    simp [auxProj, xProj, yProj]

/-- Rows are bounded by rank. -/
theorem hasRowsLE_of_hasRankLE {f : Vec F m → Vec F n → Vec F p} {r : ℕ} (h : HasRankLE f r) :
    HasRowsLE f r := by
  obtain ⟨S, hrows, hcert⟩ := certifies_of_hasRankLE f r h
  exact ⟨S, hrows.le, hcert⟩

/-- Every bilinear map has a decomposition with `m * n` products (the trivial one). -/
theorem hasRankLE_mul (f : BilMap F m n p) : HasRankLE (fun x y => f x y) (m * n) := by
  have h := hasRankLE_of_kernel_factor f (LinearMap.id (R := F) (M := Vec F m))
    (LinearMap.id (R := F) (M := Vec F n))
    (fun x hx y => by simp [show x = 0 from hx])
    (fun y hy x => by simp [show y = 0 from hy])
  simpa using h

/-- The tensor rank is attained. -/
theorem hasRankLE_tensorRank (f : BilMap F m n p) :
    HasRankLE (fun x y => f x y) (tensorRank (fun x y => f x y)) := by
  have hne : {r | HasRankLE (fun x y => f x y) r}.Nonempty := ⟨m * n, hasRankLE_mul f⟩
  exact Nat.sInf_mem hne

/-- The minimal row count is attained. -/
theorem hasRowsLE_minRows (f : BilMap F m n p) :
    HasRowsLE (fun x y => f x y) (minRows (fun x y => f x y)) := by
  have hne : {r | HasRowsLE (fun x y => f x y) r}.Nonempty :=
    ⟨m * n, hasRowsLE_of_hasRankLE (hasRankLE_mul f)⟩
  exact Nat.sInf_mem hne

/-- **Rows ≤ rank.** The minimal R1CS row count of a bilinear map is at most its tensor
rank: every rank decomposition imports wholesale as a row count. -/
theorem minRows_le_tensorRank (f : BilMap F m n p) :
    minRows (fun x y => f x y) ≤ tensorRank (fun x y => f x y) :=
  Nat.sInf_le (hasRowsLE_of_hasRankLE (hasRankLE_tensorRank f))

/-- `tensorRank` is a lower bound characterisation: if `f` has a rank-`r` decomposition
then `tensorRank f ≤ r`. -/
theorem tensorRank_le {f : Vec F m → Vec F n → Vec F p} {r : ℕ} (h : HasRankLE f r) :
    tensorRank f ≤ r := Nat.sInf_le h

/-- If `f` is certified by a system with `r` rows then `minRows f ≤ r`. -/
theorem minRows_le {f : Vec F m → Vec F n → Vec F p} {r : ℕ} (h : HasRowsLE f r) :
    minRows f ≤ r := Nat.sInf_le h

end Solution.Research
