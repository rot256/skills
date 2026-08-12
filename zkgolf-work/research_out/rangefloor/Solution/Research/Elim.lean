/-
  # Elimination toolkit: "small or cofinite" sets of public inputs

  Every lower-bound argument in this development has the same shape: the set of accepted
  public inputs `x` is shown to be *either* contained in the roots of a nonzero polynomial
  of bounded degree (hence small) *or* to have finite complement.  Neither alternative can
  be the `n`-bit range once `2 ^ n` exceeds the degree bound, because the range is a set
  of `2 ^ n` elements whose complement is infinite in characteristic zero.

  This file sets up that predicate, its closure properties, and the two elimination
  engines used later: for a one-unknown polynomial family, the set of `x` admitting a
  root (resp. a *nonzero* root) is small or cofinite.
-/
import Solution.Research.Model

namespace Solution.Research

open Polynomial

variable {F : Type*} [Field F]

/-- Either `T` is contained in the root set of a nonzero polynomial of degree at most `d`
    (so `T` has at most `d` elements), or the complement of `T` is finite. -/
def SmallOrCofinite (T : Set F) (d : ℕ) : Prop :=
  (∃ p : F[X], p ≠ 0 ∧ p.natDegree ≤ d ∧ ∀ x ∈ T, p.eval x = 0) ∨ (Tᶜ).Finite

namespace SmallOrCofinite

theorem mono {T : Set F} {d d' : ℕ} (h : SmallOrCofinite T d) (hd : d ≤ d') :
    SmallOrCofinite T d' := by
  rcases h with ⟨p, hp, hdeg, hroot⟩ | h
  · exact Or.inl ⟨p, hp, hdeg.trans hd, hroot⟩
  · exact Or.inr h

theorem congr_set {T T' : Set F} {d : ℕ} (h : SmallOrCofinite T d) (e : T = T') :
    SmallOrCofinite T' d := e ▸ h

theorem of_subset_zeroSet {T : Set F} {p : F[X]} (hp : p ≠ 0)
    (h : ∀ x ∈ T, p.eval x = 0) : SmallOrCofinite T p.natDegree :=
  Or.inl ⟨p, hp, le_rfl, h⟩

theorem of_compl_finite {T : Set F} (h : (Tᶜ).Finite) (d : ℕ) : SmallOrCofinite T d := Or.inr h

theorem of_compl_subset_zeroSet {T : Set F} {p : F[X]} (hp : p ≠ 0)
    (h : ∀ x ∈ Tᶜ, p.eval x = 0) (d : ℕ) : SmallOrCofinite T d := by
  refine Or.inr (Set.Finite.subset (Polynomial.finite_setOf_isRoot hp) ?_)
  intro x hx
  exact h x hx

theorem univ (d : ℕ) : SmallOrCofinite (Set.univ : Set F) d := by
  refine Or.inr ?_
  simp

/-- The zero set of a polynomial is small (or, if the polynomial is zero, everything). -/
theorem zeroSet (p : F[X]) : SmallOrCofinite {x : F | p.eval x = 0} p.natDegree := by
  by_cases hp : p = 0
  · subst hp
    refine (univ (F := F) 0).congr_set ?_ |>.mono (Nat.zero_le _)
    ext x; simp
  · exact of_subset_zeroSet hp fun x hx => hx

theorem union {T₁ T₂ : Set F} {d₁ d₂ : ℕ} (h₁ : SmallOrCofinite T₁ d₁)
    (h₂ : SmallOrCofinite T₂ d₂) : SmallOrCofinite (T₁ ∪ T₂) (d₁ + d₂) := by
  rcases h₁ with ⟨p, hp, hpd, hpr⟩ | h₁
  · rcases h₂ with ⟨q, hq, hqd, hqr⟩ | h₂
    · refine Or.inl ⟨p * q, mul_ne_zero hp hq, ?_, ?_⟩
      · exact (natDegree_mul hp hq).le.trans (Nat.add_le_add hpd hqd)
      · rintro x (hx | hx)
        · simp [hpr x hx]
        · simp [hqr x hx]
    · exact Or.inr (h₂.subset (by intro x hx; exact fun hx2 => hx (Or.inr hx2)))
  · exact Or.inr (h₁.subset (by intro x hx; exact fun hx1 => hx (Or.inl hx1)))

/-- Intersecting with the complement of a zero set preserves "small or cofinite". -/
theorem inter_nonzero {T : Set F} {d : ℕ} (h : SmallOrCofinite T d) {p : F[X]} (hp : p ≠ 0) :
    SmallOrCofinite (T ∩ {x : F | p.eval x ≠ 0}) d := by
  rcases h with ⟨q, hq, hqd, hqr⟩ | h
  · exact Or.inl ⟨q, hq, hqd, fun x hx => hqr x hx.1⟩
  · refine Or.inr (Set.Finite.subset (h.union (Polynomial.finite_setOf_isRoot hp)) ?_)
    intro x hx
    by_cases hx1 : x ∈ T
    · right
      have hne : ¬ p.eval x ≠ 0 := fun hne => hx ⟨hx1, hne⟩
      simpa [Polynomial.IsRoot] using not_not.1 hne
    · exact Or.inl hx1

end SmallOrCofinite

/-! ## Turning "small or cofinite" into a non-certification statement -/

/-- In characteristic zero the complement of the `n`-bit range is infinite. -/
theorem rangeSet_compl_infinite [CharZero F] (n : ℕ) : ((RangeSet F n)ᶜ).Infinite := by
  have hinj : Function.Injective (fun k : ℕ => ((k + 2 ^ n : ℕ) : F)) := by
    intro a b hab
    have : (a + 2 ^ n : ℕ) = (b + 2 ^ n : ℕ) := Nat.cast_injective hab
    omega
  refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ => ((k + 2 ^ n : ℕ) : F)) hinj ?_
  intro k
  simp only [Set.mem_compl_iff, RangeSet, Set.mem_setOf_eq, not_exists]
  rintro j ⟨hj, hje⟩
  have : j = k + 2 ^ n := Nat.cast_injective hje.symm
  omega

/-- The `n`-bit range contains `2 ^ n` distinct elements. -/
theorem rangeFinset_card [CharZero F] (n : ℕ) :
    ∃ Z : Finset F, 2 ^ n ≤ Z.card ∧ ∀ x ∈ Z, x ∈ RangeSet F n := by
  classical
  refine ⟨(Finset.range (2 ^ n)).image (fun k : ℕ => (k : F)), ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]
  · intro x hx
    simp only [Finset.mem_image, Finset.mem_range] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    exact ⟨k, hk, rfl⟩

/-- A system whose accepted set is small-or-cofinite with degree bound `d < 2 ^ n` cannot
    certify the `n`-bit range. -/
theorem not_certifies_of_smallOrCofinite [CharZero F] {m r : ℕ} (S : System F m r) {d n : ℕ}
    (h : SmallOrCofinite S.solutions d) (hd : d < 2 ^ n) : ¬ S.Certifies n := by
  intro hc
  have hset : S.solutions = RangeSet F n := by ext x; exact hc x
  rw [hset] at h
  rcases h with ⟨p, hp0, hdeg, hroots⟩ | h
  · obtain ⟨Z, hZcard, hZmem⟩ := rangeFinset_card (F := F) n
    exact hp0 (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' p Z
      (fun x hx => hroots x (hZmem x hx)) (by omega))
  · exact (rangeSet_compl_infinite (F := F) n) h

/-! ## Root existence for a one-unknown polynomial -/

/-- Over an algebraically closed field a polynomial with two distinct nonzero coefficients
    has a nonzero root. -/
theorem exists_nonzero_root_of_two_coeffs [IsAlgClosed F] (p : F[X]) {i j : ℕ} (hij : i ≠ j)
    (hi : p.coeff i ≠ 0) (hj : p.coeff j ≠ 0) : ∃ u : F, u ≠ 0 ∧ p.eval u = 0 := by
  have hp0 : p ≠ 0 := fun h => hi (by simp [h])
  obtain ⟨q, hq, hnd⟩ := p.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hp0 0
  obtain ⟨k, hk⟩ : ∃ k, p.rootMultiplicity 0 = k := ⟨_, rfl⟩
  rw [hk, Polynomial.C_0, sub_zero] at hq
  rw [Polynomial.C_0, sub_zero] at hnd
  have hq0 : q.coeff 0 ≠ 0 := fun h => hnd (Polynomial.X_dvd_iff.2 h)
  have hqdeg : q.natDegree ≠ 0 := by
    intro h
    obtain ⟨c, rfl⟩ := Polynomial.natDegree_eq_zero.1 h
    have hcoeff : ∀ n : ℕ, n ≠ k → p.coeff n = 0 := by
      intro n hn
      rw [hq, mul_comm, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg hn, mul_zero]
    have hik : i = k := by by_contra h'; exact hi (hcoeff i h')
    have hjk : j = k := by by_contra h'; exact hj (hcoeff j h')
    exact hij (hik.trans hjk.symm)
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_root q
    (fun h => hqdeg (Polynomial.natDegree_eq_zero_iff_degree_le_zero.2 (le_of_eq h)))
  refine ⟨u, ?_, ?_⟩
  · intro h
    subst h
    rw [Polynomial.IsRoot, ← Polynomial.coeff_zero_eq_eval_zero] at hu
    exact hq0 hu
  · rw [hq]
    simp [Polynomial.IsRoot.def.1 hu]

/-! ## The elimination engines: a one-unknown polynomial family -/

/-- The value at `u` of the degree-`≤ 4` polynomial whose coefficients are the
    polynomials `c 0, …, c 4` evaluated at `x`. -/
def quintEval (c : Fin 5 → F[X]) (x u : F) : F := ∑ i : Fin 5, (c i).eval x * u ^ (i : ℕ)

/-- The set of `x` for which the one-unknown equation has a solution. -/
def quintSet (c : Fin 5 → F[X]) : Set F := {x : F | ∃ u : F, quintEval c x u = 0}

/-- The set of `x` for which the one-unknown equation has a *nonzero* solution. -/
def quintSetNz (c : Fin 5 → F[X]) : Set F := {x : F | ∃ u : F, u ≠ 0 ∧ quintEval c x u = 0}

theorem quintEval_explicit (c₀ c₁ c₂ c₃ c₄ : F[X]) (x u : F) :
    quintEval ![c₀, c₁, c₂, c₃, c₄] x u =
      c₄.eval x * u ^ 4 + c₃.eval x * u ^ 3 + c₂.eval x * u ^ 2 + c₁.eval x * u + c₀.eval x := by
  simp [quintEval, Fin.sum_univ_five]
  ring

/-- The specialisation of the family at `x`, as a genuine polynomial in the unknown. -/
noncomputable def quintPoly (c : Fin 5 → F[X]) (x : F) : F[X] :=
  ∑ i : Fin 5, Polynomial.C ((c i).eval x) * X ^ (i : ℕ)

theorem quintPoly_eval (c : Fin 5 → F[X]) (x u : F) :
    (quintPoly c x).eval u = quintEval c x u := by
  simp [quintPoly, quintEval, Polynomial.eval_finset_sum]

theorem quintPoly_coeff (c : Fin 5 → F[X]) (x : F) (j : Fin 5) :
    (quintPoly c x).coeff (j : ℕ) = (c j).eval x := by
  classical
  rw [quintPoly, Polynomial.finset_sum_coeff]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    have : (j : ℕ) ≠ (i : ℕ) := fun h => hij (Fin.ext h.symm)
    simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, this]
  · intro h; exact absurd (Finset.mem_univ j) h

theorem quintPoly_eq_zero (c : Fin 5 → F[X]) (x : F) (h : ∀ i : Fin 5, (c i).eval x = 0) :
    quintPoly c x = 0 := by
  simp [quintPoly, h]

theorem natDegree_ne_zero_of_coeff_ne_zero (p : F[X]) {i : ℕ} (hi : i ≠ 0) (h : p.coeff i ≠ 0) :
    p.natDegree ≠ 0 := by
  intro hd
  obtain ⟨a, rfl⟩ := Polynomial.natDegree_eq_zero.1 hd
  exact h (by simp [Polynomial.coeff_C, hi])

theorem exists_root_of_natDegree_ne_zero [IsAlgClosed F] (p : F[X]) (h : p.natDegree ≠ 0) :
    ∃ u : F, p.eval u = 0 := by
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_root p
    (fun hd => h (Polynomial.natDegree_eq_zero_iff_degree_le_zero.2 (le_of_eq hd)))
  exact ⟨u, hu⟩

/-- **Engine 1.**  The set of `x` at which a one-unknown polynomial family of degree `≤ 4`
    has a root is either the zero set of its constant coefficient (when all the higher
    coefficients vanish identically) or cofinite. -/
theorem quintSet_smallOrCofinite [IsAlgClosed F] (c : Fin 5 → F[X]) {d : ℕ}
    (h0 : (c 0).natDegree ≤ d) : SmallOrCofinite (quintSet c) d := by
  classical
  by_cases hhi : ∃ i : Fin 5, i ≠ 0 ∧ c i ≠ 0
  · obtain ⟨i, hi0, hi⟩ := hhi
    refine SmallOrCofinite.of_compl_subset_zeroSet hi ?_ d
    intro x hx
    by_contra hne
    refine hx ?_
    have hcoeff : (quintPoly c x).coeff (i : ℕ) ≠ 0 := by
      rw [quintPoly_coeff]; exact hne
    have hival : (i : ℕ) ≠ 0 := fun h => hi0 (Fin.ext (by simpa using h))
    obtain ⟨u, hu⟩ := exists_root_of_natDegree_ne_zero (quintPoly c x)
      (natDegree_ne_zero_of_coeff_ne_zero _ hival hcoeff)
    exact ⟨u, by rwa [quintPoly_eval] at hu⟩
  · push_neg at hhi
    have hset : quintSet c = {x : F | (c 0).eval x = 0} := by
      ext x
      constructor
      · rintro ⟨u, hu⟩
        have : quintEval c x u = (c 0).eval x := by
          rw [quintEval, Finset.sum_eq_single (0 : Fin 5)]
          · simp
          · intro i _ hi0
            rw [hhi i hi0]
            simp
          · intro h; exact absurd (Finset.mem_univ (0 : Fin 5)) h
        rw [this] at hu
        exact hu
      · intro hx
        refine ⟨0, ?_⟩
        rw [quintEval, Finset.sum_eq_single (0 : Fin 5)]
        · simpa using hx
        · intro i _ hi0
          rw [hhi i hi0]
          simp
        · intro h; exact absurd (Finset.mem_univ (0 : Fin 5)) h
    exact (SmallOrCofinite.zeroSet (c 0)).congr_set hset.symm |>.mono h0

/-- **Engine 2.**  The set of `x` at which a one-unknown polynomial family of degree `≤ 4`
    has a *nonzero* root is either the zero set of its unique nonvanishing coefficient or
    cofinite. -/
theorem quintSetNz_smallOrCofinite [IsAlgClosed F] (c : Fin 5 → F[X]) {d : ℕ}
    (hdeg : ∀ i, (c i).natDegree ≤ d) : SmallOrCofinite (quintSetNz c) d := by
  classical
  by_cases htwo : ∃ i j : Fin 5, i ≠ j ∧ c i ≠ 0 ∧ c j ≠ 0
  · obtain ⟨i, j, hij, hi, hj⟩ := htwo
    refine SmallOrCofinite.of_compl_subset_zeroSet (mul_ne_zero hi hj) ?_ d
    intro x hx
    by_contra hne
    rw [Polynomial.eval_mul, mul_eq_zero] at hne
    push_neg at hne
    obtain ⟨hnei, hnej⟩ := hne
    refine hx ?_
    have hci : (quintPoly c x).coeff (i : ℕ) ≠ 0 := by rw [quintPoly_coeff]; exact hnei
    have hcj : (quintPoly c x).coeff (j : ℕ) ≠ 0 := by rw [quintPoly_coeff]; exact hnej
    obtain ⟨u, hu0, hu⟩ := exists_nonzero_root_of_two_coeffs (quintPoly c x)
      (fun h => hij (Fin.ext h)) hci hcj
    exact ⟨u, hu0, by rwa [quintPoly_eval] at hu⟩
  · push_neg at htwo
    by_cases hall : ∀ i, c i = 0
    · refine SmallOrCofinite.of_compl_finite ?_ d
      have : (quintSetNz c) = Set.univ := by
        ext x
        simp only [Set.mem_univ, iff_true, quintSetNz, Set.mem_setOf_eq]
        exact ⟨1, one_ne_zero, by simp [quintEval, hall]⟩
      rw [this]
      simp
    · push_neg at hall
      obtain ⟨i, hi⟩ := hall
      have hother : ∀ j : Fin 5, j ≠ i → c j = 0 := fun j hj => htwo i j (Ne.symm hj) hi
      have hval : ∀ (x u : F), quintEval c x u = (c i).eval x * u ^ (i : ℕ) := by
        intro x u
        rw [quintEval, Finset.sum_eq_single i]
        · intro j _ hj
          rw [hother j hj]
          simp
        · intro h; exact absurd (Finset.mem_univ i) h
      have hset : quintSetNz c = {x : F | (c i).eval x = 0} := by
        ext x
        constructor
        · rintro ⟨u, hu0, hu⟩
          rw [hval x u, mul_eq_zero] at hu
          rcases hu with h | h
          · exact h
          · exact absurd (pow_eq_zero_iff' .. |>.1 h).1 hu0
        · intro hx
          exact ⟨1, one_ne_zero, by rw [hval x 1, hx]; simp⟩
      exact (SmallOrCofinite.zeroSet (c i)).congr_set hset.symm |>.mono (hdeg i)

end Solution.Research
