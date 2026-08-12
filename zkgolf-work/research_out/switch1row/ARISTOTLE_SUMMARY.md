# Summary of changes for run 31c3c839-0c3c-476e-90a0-8a7e80713da6
**Result: everything requested is proved, including the n-element multiset version. `lake build` compiles the whole project with zero errors, and `Solution/` contains no `sorry`.**

All work is in `Solution/Research/Switch.lean` (single file, `variable {F : Type*} [Field F]`).

**Two-element case**
- `switch_pins_multiset (a b o : F) (h : (o - a) * (o - b) = 0) : (o = a ∧ a + b - o = b) ∨ (o = b ∧ a + b - o = a)` — the given obligation, proved unchanged (via `mul_eq_zero`, i.e. no zero divisors).
- `switch_complete (a b o : F) (h : o = a ∨ o = b) : (o - a) * (o - b) = 0 ∧ ((o = a ∧ a + b - o = b) ∨ (o = b ∧ a + b - o = a))` — the converse/completeness: either choice of `o ∈ {a,b}` satisfies the row and makes `a + b - o` the other element.
- `switch_multiset_eq` and `switch_multiset_eq_iff (a b o : F) : (o - a) * (o - b) = 0 ↔ ({o, a + b - o} : Multiset F) = {a, b}` — both directions packaged as the multiset identity a circuit actually wants.

**n-element case (obtained)**
- `wireMultiset v = Finset.univ.val.map v` for a bus `v : Fin n → F`; `applySwitch v i j o = update (update v i o) j (v i + v j - o)` (only `o` is witnessed, wire `j` is the free affine wire).
- `applySwitch_of_eq_left` / `applySwitch_of_eq_right`: a satisfied row makes a switch either the identity or `v ∘ Equiv.swap i j`.
- `wireMultiset_applySwitch`: one satisfied row preserves the wire multiset (no `i ≠ j` hypothesis needed — the degenerate case is forced to the identity).
- `Network n F := List (Fin n × Fin n × F)`, `runNetwork` (outputs of one switch feed the next), `NetworkConstraints` (one quadratic row per switch, evaluated against the bus as it stands at that switch).
- **Soundness:** `wireMultiset_runNetwork (v) (net) (h : NetworkConstraints v net) : wireMultiset (runNetwork v net) = wireMultiset v` — unconditional, no random challenge.
- **Completeness:** `networkConstraints_of_outputs_are_inputs` (rows hold whenever each witnessed output is one of that switch's two inputs) and `exists_network_of_perm (sigma : Equiv.Perm (Fin n)) (v) : ∃ net, NetworkConstraints v net ∧ runNetwork v net = v ∘ sigma` — every permutation is realisable by a network all of whose rows hold, so the encoding excludes no permutation.
- `wireMultiset_two (a b : F) : wireMultiset ![a, b] = {a, b}` links the bus view to the two-element view.

**Axioms.** `#print axioms` on each of `switch_pins_multiset`, `switch_complete`, `switch_multiset_eq`, `switch_multiset_eq_iff`, `wireMultiset_comp_equiv`, `applySwitch_of_eq_left`, `applySwitch_of_eq_right`, `wireMultiset_applySwitch`, `wireMultiset_runNetwork`, `networkConstraints_of_outputs_are_inputs`, `exists_network_of_perm`, `wireMultiset_two` prints exactly:

`depends on axioms: [propext, Classical.choice, Quot.sound]`

No `sorryAx`, no new `axiom`, no `native_decide`/`bv_decide`.

**One environment note:** the vendored dependency directory `.lake/packages/clean` was absent, so `lake build` initially failed to resolve the package before compiling anything. I re-fetched it at the commit pinned in the lakefile (it is gitignored, so no repository content changed). After that, `lake build` completes successfully; the only warnings are the pre-existing `declaration uses 'sorry'` notices in the untouched `Challenge/Instances/...` template files.
