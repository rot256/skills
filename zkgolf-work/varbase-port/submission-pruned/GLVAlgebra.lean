import Solution.Secp256k1ScalarMul.Phi
import Solution.Secp256k1ScalarMul.ProofBlocker
import Mathlib.Tactic.Module

namespace Solution.Secp256k1ScalarMul.GLVAlgebra

open Specs.Secp256k1

lemma natCast_zsmul_eq_nsmul {A : Type*} [AddGroup A] (n : ℕ) (P : A) :
    (n : ℤ) • P = n • P := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.cast_succ, add_zsmul, one_zsmul, succ_nsmul, ih]

lemma neg_natCast_zsmul_eq_neg_nsmul {A : Type*} [AddGroup A] (n : ℕ) (P : A) :
    (-(n : ℤ)) • P = -(n • P) := by
  rw [neg_zsmul, natCast_zsmul_eq_nsmul]

theorem norm_zsmul_eq_zero {A : Type*} [AddCommGroup A]
    (f : A →+ A) (hquad : ∀ P, f (f P) + f P + P = 0)
    (G : A) (a b : ℤ) (hrel : a • G + b • f G = 0) :
    (a * a - a * b + b * b) • G = 0 := by
  have hphi : a • f G + b • f (f G) = 0 := by
    have h := congrArg f hrel
    simpa using h
  have hphi2 : f (f G) = -f G - G := by
    calc
      f (f G) = (f (f G) + f G + G) - f G - G := by abel
      _ = -f G - G := by rw [hquad, zero_sub]
  have hrel2 : (a - b) • f G - b • G = 0 := by
    calc
      (a - b) • f G - b • G = a • f G + b • f (f G) := by
        rw [hphi2]
        module
      _ = 0 := hphi
  calc
    (a * a - a * b + b * b) • G =
        (a - b) • (a • G + b • f G) -
          b • ((a - b) • f G - b • G) := by module
    _ = 0 := by rw [hrel, hrel2]; simp

def latticeA : ℕ := 0x3086d221a7d46bcde86c90e49284eb15

def latticeB : ℕ := 0xe4437ed6010e88286f547fa90abfe4c3

def lambda : ℕ :=
  0x5363ad4cc05c30e0a5261c028812645a122e22ea20816678df02967c1b23bd72

def latticeQuotient : ℕ := 98834128363575826231712400374302886273

lemma lattice_norm :
    (latticeA : ℤ) * latticeA - (latticeA : ℤ) * (-(latticeB : ℤ)) +
      (-(latticeB : ℤ)) * (-(latticeB : ℤ)) = (order : ℤ) := by
  norm_num [latticeA, latticeB, order]

lemma lattice_eigen_relation :
    latticeA + latticeQuotient * order = latticeB * lambda := by
  norm_num [latticeA, latticeB, latticeQuotient, lambda, order]

theorem order_nsmul_of_short_relation
    (G : Bridge.W.Point) (hshort : latticeA • G = latticeB • Phi.hom G) :
    order • G = 0 := by
  have hrel : (latticeA : ℤ) • G + (-(latticeB : ℤ)) • Phi.hom G = 0 := by
    rw [natCast_zsmul_eq_nsmul, neg_natCast_zsmul_eq_neg_nsmul]
    rw [hshort, add_neg_cancel]
  have hnorm := norm_zsmul_eq_zero Phi.hom Phi.hom_quadratic G
    (latticeA : ℤ) (-(latticeB : ℤ)) hrel
  rw [lattice_norm] at hnorm
  rw [natCast_zsmul_eq_nsmul] at hnorm
  exact hnorm

lemma latticeB_not_order_dvd : ¬ order ∣ latticeB := by
  intro hdvd
  have hle : order ≤ latticeB := Nat.le_of_dvd (by norm_num [latticeB]) hdvd
  have hlt : latticeB < order := by norm_num [latticeB, order]
  omega

theorem hom_G_eq_lambda_nsmul
    (G : Bridge.W.Point)
    (hshort : latticeA • G = latticeB • Phi.hom G)
    (horder : order • ProofBlocker.gPoint = 0)
    (hG : G = ProofBlocker.gPoint) :
    Phi.hom G = lambda • G := by
  subst G
  have hlat : latticeA • ProofBlocker.gPoint =
      latticeB • (lambda • ProofBlocker.gPoint) := by
    calc
      latticeA • ProofBlocker.gPoint =
          (latticeA + latticeQuotient * order) • ProofBlocker.gPoint := by
            rw [add_nsmul, mul_nsmul', horder, nsmul_zero, add_zero]
      _ = (latticeB * lambda) • ProofBlocker.gPoint := by
        rw [lattice_eigen_relation]
      _ = latticeB • (lambda • ProofBlocker.gPoint) := by
        rw [mul_nsmul']
  apply ProofBlocker.nsmul_right_injective_of_not_order_dvd
    horder latticeB_not_order_dvd
  exact hshort.symm.trans hlat

lemma zsmul_nsmul_comm (z : ℤ) (n : ℕ) (P : Bridge.W.Point) :
    z • (n • P) = n • (z • P) := by
  induction n with
  | zero => simp
  | succ n ih => simp only [succ_nsmul, zsmul_add, ih]

theorem hom_eq_lambda_nsmul_all
    (hshort : latticeA • ProofBlocker.gPoint = latticeB • Phi.hom ProofBlocker.gPoint)
    (Q : Bridge.W.Point) : Phi.hom Q = lambda • Q := by
  have horder : order • ProofBlocker.gPoint = 0 :=
    order_nsmul_of_short_relation ProofBlocker.gPoint hshort
  have hfixed : Phi.hom ProofBlocker.gPoint = lambda • ProofBlocker.gPoint :=
    hom_G_eq_lambda_nsmul ProofBlocker.gPoint hshort horder rfl
  obtain ⟨z, rfl⟩ := ProofBlocker.exists_zsmul_gPoint horder Q
  rw [AddMonoidHom.map_zsmul, hfixed,
    zsmul_nsmul_comm z lambda ProofBlocker.gPoint]

end Solution.Secp256k1ScalarMul.GLVAlgebra
