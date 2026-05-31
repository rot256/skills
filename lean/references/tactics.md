# Lean 4 / Mathlib tactic toolbox

Reference for the proving stage. Match the existing project's style and naming; read neighboring proofs before writing new ones.

## Finding the right Mathlib lemma

For standard mathematical facts, search Mathlib before proving them yourself — it likely has the lemma, and reproving it wastes effort. (Project-specific steps still want local `have`s / helper lemmas; don't search endlessly for something bespoke.) To locate a library lemma:

- **`exact?`** — searches for a lemma that closes the current goal exactly. First thing to try on a leaf goal.
- **`apply?`** — like `exact?` but for lemmas that apply with remaining subgoals.
- **`rw?`** — suggests rewrites applicable to the goal.
- **`simp?`** — runs `simp` and reports the lemma set it used (turn an opaque `simp` into an explicit `simp only [...]`).
- **`#leansearch "natural language query"`** — semantic search over Mathlib from inside the file.
- **`loogle`** (web / `#loogle`) — search by type/name pattern, e.g. `Loogle: List.map _ (_ ++ _)`.
- Mathlib naming convention is descriptive: `add_comm`, `mul_le_mul`, `Nat.succ_le_succ`. Guessing by convention often works; confirm with `#check`.

## Core tactics

- **`exact`, `apply`, `refine`** — close/reduce a goal by a term; `refine` leaves `?_` holes.
- **`rw [h, ← h2]`** — rewrite with equations (left-to-right, `←` for right-to-left); the everyday equational tool. `simp only` when `rw` loops or needs matching.
- **`simpa [...] using h`** — simp the goal and `h`, then close by `h`; very common for "this is `h` up to simp".
- **`intro`, `rintro`** — introduce hypotheses; `rintro ⟨a, b, c⟩` destructures.
- **`obtain ⟨...⟩ := h`** — destructure an existential/conjunction/structure.
- **`rcases` / `rcases h with ...`** — recursive case analysis. **`by_cases h : P`** — split on a decidable/classical proposition.
- **`cases` / `induction x with ...`** — case split / induction; `induction` is the workhorse for recursive proofs.
- **`constructor`, `refine ⟨_, _⟩`** — split a conjunction/structure goal into its fields. **`use w`** — provide a witness for `∃`. **`left` / `right`** — pick a disjunct.
- **`have h : P := by ...`** — forward step; the backbone of decomposed proofs. Prefer many small `have`s.
- **`specialize h a b`** — instantiate a universally-quantified hypothesis. **`subst h`** — substitute an equation `x = e` everywhere.
- **`show P` / `change P`** — restate the goal as a definitionally-equal form for clarity.
- **`calc`** — chained equational/inequational reasoning; mirrors a paper derivation step by step.

## Automation

- **`simp` / `simp only [lemmas]` / `simp_all`** — simplification by the simp set; `simp only` keeps it controlled and fast.
- **`omega`** — linear arithmetic over `Nat`/`Int`. Excellent for index/bound goals.
- **`linarith` / `nlinarith`** — linear / nonlinear arithmetic over ordered fields.
- **`ring` / `ring_nf`** — commutative-ring equalities.
- **`field_simp`** — clear denominators ahead of `ring`. Needs the denominators known nonzero: it discharges that from hypotheses/`simp`, else leaves `x ≠ 0` side goals — supply them via `field_simp [hx]` or close with `positivity`.
- **`decide`** — closes decidable propositions by computation (small/finite only).
- **`norm_num`** — numeric goals.
- **`positivity`** — proves `0 < e` / `0 ≤ e`.
- **`tauto`, `aesop`** — general-purpose closers; `aesop` is strong but can be slow.
- **`grind`** — SMT-solver-inspired closer (Lean ≥ 4.22): congruence closure + E-matching + linear integer arithmetic + commutative-ring solver, with case-splitting. Strong on goals mixing equalities, arithmetic, and known lemmas. Guide it with `grind [lemma, ...]` (extra E-matching facts) or `grind only [...]`. NOT for combinatorial blowups (large pigeonhole, graph-coloring, big SAT-style encodings) — its branching search drowns. Try after `simp`/`omega`/`linarith` when those alone don't close.

## Hygiene

- Use `sorry` to stub unproven steps so the file still elaborates — but track every one; none may survive to the end.
- Convert exploratory `simp` / `exact?` results into explicit `simp only [...]` / `exact <lemma>` for stable, fast, readable proofs.
- If a tactic is slow or times out, the proof is usually wrong or under-decomposed. Split it, don't just raise `maxHeartbeats`.
- Name hypotheses meaningfully; avoid relying on auto-generated names that shift when the goal changes.
- After finishing, reread the proof: every step should map back to a line of the human-readable argument.
