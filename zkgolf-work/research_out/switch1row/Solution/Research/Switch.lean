/-
  The one-row permutation switch.

  A 2x2 switch is normally encoded with a boolean selector `s`:
      out1 = a + s * (b - a),  out2 = a + b - out1,  s * (s - 1) = 0
  costing 2 rows and 2 witnesses. The claim is that witnessing ONLY `out1` and
  asserting a single quadratic row pins the pair as a MULTISET at 1 row + 1 witness.

  Composed with a Waksman network (n·log2 n - n + 1 switches, realising every
  permutation in S_n) this is a permutation / multiset-equality certificate that needs
  NO random challenge -- which matters because our soundness obligation is an
  unconditional `forall env` theorem and the usual grand-product argument is not
  available to us.
-/
import Mathlib

namespace Solution.Research

variable {F : Type*} [Field F]

/-! ## Soundness and completeness of the one-row switch -/

/-- **The obligation.** The single row `(o - a) * (o - b) = 0`, together with the free
    affine definition `o' = a + b - o`, forces the unordered pair `{o, o'}` to equal
    `{a, b}`.

    Prove it. Then state and prove the converse (completeness): for either choice of
    `o ∈ {a, b}` the row is satisfied and `o'` is the other element. -/
theorem switch_pins_multiset (a b o : F) (h : (o - a) * (o - b) = 0) :
    (o = a ∧ a + b - o = b) ∨ (o = b ∧ a + b - o = a) := by
  rcases mul_eq_zero.mp h with h | h
  · exact Or.inl ⟨by linear_combination h, by linear_combination -h⟩
  · exact Or.inr ⟨by linear_combination h, by linear_combination -h⟩

/-- **Completeness (converse).** For either choice of `o ∈ {a, b}` the row
    `(o - a) * (o - b) = 0` is satisfiable, and the free affine wire `a + b - o` carries
    the other element of the pair. -/
theorem switch_complete (a b o : F) (h : o = a ∨ o = b) :
    (o - a) * (o - b) = 0 ∧ ((o = a ∧ a + b - o = b) ∨ (o = b ∧ a + b - o = a)) := by
  rcases h with rfl | rfl
  · exact ⟨by ring, Or.inl ⟨rfl, by ring⟩⟩
  · exact ⟨by ring, Or.inr ⟨rfl, by ring⟩⟩

/-- Soundness, packaged as an equality of two-element multisets:
    the row forces `{o, a + b - o} = {a, b}`. -/
theorem switch_multiset_eq (a b o : F) (h : (o - a) * (o - b) = 0) :
    ({o, a + b - o} : Multiset F) = {a, b} := by
  rcases switch_pins_multiset a b o h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h2, h1]
  · rw [h2, h1]
    exact Multiset.pair_comm b a

/-- Completeness, packaged as an equality of two-element multisets. -/
theorem switch_multiset_eq_iff (a b o : F) :
    (o - a) * (o - b) = 0 ↔ ({o, a + b - o} : Multiset F) = {a, b} := by
  refine ⟨switch_multiset_eq a b o, fun h => ?_⟩
  have ho : o = a ∨ o = b := by
    have : o ∈ ({a, b} : Multiset F) := by
      rw [← h]; simp
    simpa using this
  exact (switch_complete a b o ho).1

/-! ## The n-element version: a network of one-row switches preserves the multiset -/

/-- The multiset of values carried by an `n`-wire bus. -/
def wireMultiset {n : ℕ} (v : Fin n → F) : Multiset F := Finset.univ.val.map v

omit [Field F] in
@[simp] theorem wireMultiset_comp_equiv {n : ℕ} (v : Fin n → F) (e : Fin n ≃ Fin n) :
    wireMultiset (v ∘ e) = wireMultiset v := by
  have h : Multiset.map e Finset.univ.val = (Finset.univ : Finset (Fin n)).val :=
    Multiset.map_univ_val_equiv e
  show Multiset.map (v ∘ e) Finset.univ.val = Multiset.map v Finset.univ.val
  calc Multiset.map (v ∘ e) Finset.univ.val
      = Multiset.map v (Multiset.map e Finset.univ.val) := (Multiset.map_map v e _).symm
    _ = Multiset.map v Finset.univ.val := by rw [h]

/-- One application of the one-row switch to wires `i` and `j` of a bus: the witnessed
    output `o` goes to wire `i`, and wire `j` gets the *free* affine combination
    `v i + v j - o`. -/
def applySwitch {n : ℕ} (v : Fin n → F) (i j : Fin n) (o : F) : Fin n → F :=
  Function.update (Function.update v i o) j (v i + v j - o)

/-- If the witnessed output equals the first input, the switch is the identity. -/
theorem applySwitch_of_eq_left {n : ℕ} (v : Fin n → F) (i j : Fin n) :
    applySwitch v i j (v i) = v := by
  unfold applySwitch
  rw [Function.update_eq_self]
  have : v i + v j - v i = v j := by ring
  rw [this, Function.update_eq_self]

/-- If the witnessed output equals the second input, the switch swaps the two wires. -/
theorem applySwitch_of_eq_right {n : ℕ} (v : Fin n → F) (i j : Fin n) (hij : i ≠ j) :
    applySwitch v i j (v j) = v ∘ Equiv.swap i j := by
  funext k
  unfold applySwitch
  by_cases hkj : k = j
  · subst hkj
    simp [Equiv.swap_apply_right]
  · by_cases hki : k = i
    · subst hki
      simp [hkj, Equiv.swap_apply_left]
    · simp [hkj, hki, Equiv.swap_apply_of_ne_of_ne hki hkj]

/-- **The switch step is multiset-preserving.** A single row `(o - v i) * (o - v j) = 0`
    is enough to force the bus after the switch to carry exactly the same multiset of
    values as before. -/
theorem wireMultiset_applySwitch {n : ℕ} (v : Fin n → F) (i j : Fin n) (o : F)
    (h : (o - v i) * (o - v j) = 0) :
    wireMultiset (applySwitch v i j o) = wireMultiset v := by
  rcases mul_eq_zero.mp h with h | h
  · have ho : o = v i := by linear_combination h
    rw [ho, applySwitch_of_eq_left]
  · have ho : o = v j := by linear_combination h
    by_cases hij : i = j
    · subst hij
      rw [ho, applySwitch_of_eq_left]
    · rw [ho, applySwitch_of_eq_right v i j hij, wireMultiset_comp_equiv]

/-- A switch network: a list of steps, each naming the two wires it acts on together
    with the single witnessed output value. -/
abbrev Network (n : ℕ) (F : Type*) := List (Fin n × Fin n × F)

/-- Run a switch network on a bus, feeding the outputs of one switch into the next. -/
def runNetwork {n : ℕ} : (Fin n → F) → Network n F → (Fin n → F)
  | v, [] => v
  | v, (i, j, o) :: rest => runNetwork (applySwitch v i j o) rest

@[simp] theorem runNetwork_nil {n : ℕ} (v : Fin n → F) : runNetwork v ([] : Network n F) = v :=
  rfl

@[simp] theorem runNetwork_cons {n : ℕ} (v : Fin n → F) (i j : Fin n) (o : F)
    (rest : Network n F) :
    runNetwork v ((i, j, o) :: rest) = runNetwork (applySwitch v i j o) rest := rfl

/-- The constraint system of a switch network: one quadratic row per switch, each row
    referring to the bus as it stands when that switch is reached. -/
def NetworkConstraints {n : ℕ} : (Fin n → F) → Network n F → Prop
  | _, [] => True
  | v, (i, j, o) :: rest =>
      (o - v i) * (o - v j) = 0 ∧ NetworkConstraints (applySwitch v i j o) rest

@[simp] theorem networkConstraints_nil {n : ℕ} (v : Fin n → F) :
    NetworkConstraints v ([] : Network n F) := trivial

@[simp] theorem networkConstraints_cons {n : ℕ} (v : Fin n → F) (i j : Fin n) (o : F)
    (rest : Network n F) :
    NetworkConstraints v ((i, j, o) :: rest) ↔
      ((o - v i) * (o - v j) = 0 ∧ NetworkConstraints (applySwitch v i j o) rest) := Iff.rfl

/-- **Soundness of a switch network (the n-element version).** If every row of the
    network holds, the output bus carries exactly the same multiset of values as the
    input bus. No random challenge is involved. -/
theorem wireMultiset_runNetwork {n : ℕ} (v : Fin n → F) (net : Network n F)
    (h : NetworkConstraints v net) :
    wireMultiset (runNetwork v net) = wireMultiset v := by
  induction net generalizing v with
  | nil => rfl
  | cons step rest ih =>
    obtain ⟨i, j, o⟩ := step
    obtain ⟨hrow, hrest⟩ := h
    rw [runNetwork_cons, ih _ hrest, wireMultiset_applySwitch v i j o hrow]

/-- **Completeness of a switch network, row by row.** If the witnessed output of every
    switch is one of the two values that switch receives, then every row of the network
    holds. -/
theorem networkConstraints_of_outputs_are_inputs {n : ℕ} (v : Fin n → F) (net : Network n F)
    (h : ∀ (k : ℕ) (hk : k < net.length),
        let w := runNetwork v (net.take k)
        let s := net[k]
        s.2.2 = w s.1 ∨ s.2.2 = w s.2.1) :
    NetworkConstraints v net := by
  induction net generalizing v with
  | nil => trivial
  | cons step rest ih =>
    obtain ⟨i, j, o⟩ := step
    have h0 := h 0 (by simp)
    simp only [List.take_zero, runNetwork_nil, List.getElem_cons_zero] at h0
    refine ⟨?_, ih _ (fun k hk => ?_)⟩
    · rcases h0 with h0 | h0 <;> rw [h0] <;> ring
    · have := h (k + 1) (by simpa using hk)
      simpa [List.take_succ_cons, runNetwork_cons] using this

/-- **Completeness of a switch network, in the form a circuit consumes it.** Every
    permutation `σ` of the wires is realised by some network all of whose rows hold: the
    switches are all satisfiable, so no permutation is excluded by the encoding. -/
theorem exists_network_of_perm {n : ℕ} (sigma : Equiv.Perm (Fin n)) (v : Fin n → F) :
    ∃ net : Network n F, NetworkConstraints v net ∧ runNetwork v net = v ∘ sigma := by
  induction sigma using Equiv.Perm.swap_induction_on generalizing v with
  | one => exact ⟨[], trivial, rfl⟩
  | swap_mul f x y hxy ih =>
    obtain ⟨net, hc, hr⟩ := ih (v ∘ Equiv.swap x y)
    have hs : applySwitch v x y (v y) = v ∘ Equiv.swap x y :=
      applySwitch_of_eq_right v x y hxy
    refine ⟨(x, y, v y) :: net, ⟨by ring, ?_⟩, ?_⟩
    · rw [hs]; exact hc
    · rw [runNetwork_cons, hs, hr]
      funext k
      rfl

omit [Field F] in
/-- The two-wire bus `![a, b]` carries the multiset `{a, b}`. -/
theorem wireMultiset_two (a b : F) : wireMultiset ![a, b] = {a, b} := rfl

end Solution.Research
