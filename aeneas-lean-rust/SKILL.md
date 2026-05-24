---
name: aeneas-lean-rust
description: End-to-end Rust verification and formalization in Lean 4 using Aeneas and Charon. Use when Codex needs to translate Rust crates or functions to Lean, work with Aeneas-generated Lean files, write weakest-precondition specs, prove Rust program properties with Aeneas tactics, model mutable borrows/back-functions, reason about Rust scalars/vectors/loops/traits, configure Lake for the Aeneas Lean backend, or debug Charon/Aeneas/LLBC translation and proof workflows.
---

# Aeneas Lean Rust

Use this skill for Rust-to-Lean verification with Aeneas. First inspect the local crate and Lean project shape, then choose the smallest workflow that gets to a checked Lean proof.

## Core Workflow

1. Inspect the Rust crate: `Cargo.toml`, `rust-toolchain`, target functions, feature flags, tests, and any Aeneas/Charon options already present.
2. Inspect the Lean side: `lakefile.lean`, `lean-toolchain`, generated `*.lean`, external templates, and existing specs/proofs.
3. If translation is required, run Charon to produce LLBC and Aeneas to produce Lean. Prefer the repo's existing scripts/options over inventing new commands.
4. Keep generated Lean separate from hand-written specs/proofs. Do not manually patch generated files unless the user explicitly wants a temporary experiment.
5. Develop specs against the generated definitions, prove them, and validate with `lake build` or the narrowest available Lean check.

For command details, proof idioms, and generated-code patterns, read [references/aeneas-workflow.md](references/aeneas-workflow.md).

## Current Lean Defaults

Use the modern Aeneas style unless the local project clearly uses an older version:

```lean
import Aeneas
open Aeneas Std Result

set_option maxHeartbeats 1000000

#setup_aeneas_simps
```

Prefer weakest-precondition theorem statements:

```lean
@[step]
theorem f_spec (x : U32) (h : x.val + 1 <= U32.max) :
  f x ⦃ y => y.val = x.val + 1 ⦄ := by
  unfold f
  step
  scalar_tac
```

For functions returning several logical values, use multi-argument postconditions:

```lean
theorem nth_mut_spec {T : Type} [Inhabited T] (l : CList T) (i : U32)
    (h : i.val < l.toList.length) :
  list_nth_mut1 l i ⦃ x back =>
    x = l.toList[i.val]! ∧
    ∀ x', (back x').toList = l.toList.set i.val x' ⦄ := by
  unfold list_nth_mut1 list_nth_mut1_loop
  step*
  simp_all
```

## Proof Strategy

- Start by unfolding the generated function or wrapper under proof.
- Use `step` for monadic binds and registered specs; use `step with some_spec as ⟨...⟩` when the intended spec is not chosen automatically.
- Use `step*` for routine generated code with binds and branches; use `step*?` if available to inspect the generated script.
- Use `split` or `cases h:` before stepping when a branch must remain explicit.
- Use `simp_all`, `simp_lists [*]`, `scalar_tac`, `scalar_tac +split`, `agrind`, `grind`, `ring_nf`, and `ring_eq_nf` as the default cleanup/arithmetic toolbox.
- Add `@[step]` to reusable function specs so later proofs can step through callers.
- For recursive spec proofs, add a concrete `termination_by` measure and usually close `decreasing_by` with `scalar_decr_tac`.

## Version Notes

Aeneas changes quickly. If the local project uses `import Base`, `progress`, or `@[pspec]`, follow that local style for existing proofs. For new projects, prefer `import Aeneas`, WP notation `f args ⦃ ... ⦄`, `@[step]`, `step`, and `step*`.

Primary sources for this skill:

- https://github.com/AeneasVerif/aeneas
- https://github.com/AeneasVerif/aeneas/tree/main/tests/lean/Tutorial
- https://github.com/AeneasVerif/icfp-tutorial
- https://lean-lang.org/use-cases/aeneas/
- https://aeneasverif.github.io/
