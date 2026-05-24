# Aeneas Workflow Reference

## Source Setup

Aeneas verifies safe Rust by translating Rust through Charon into LLBC, then translating LLBC to Lean. Before changing anything, inspect local project conventions:

- Rust: `Cargo.toml`, `rust-toolchain`, `.cargo/config*`, `aeneas-test-options`, CI scripts, Makefiles, and target source files.
- Lean: `lakefile.lean`, `lean-toolchain`, `lake-manifest.json`, generated Lean modules, and hand-written proof modules.
- Existing generation scripts: prefer them, because Aeneas flags vary by version and project.

Common Charon/Aeneas shape:

```bash
charon cargo --preset=aeneas --dest-file crate.llbc
aeneas -backend lean -split-files -dest Generated crate.llbc
```

Older tutorials may use:

```bash
cd source && ../charon/bin/charon --hide-marker-traits --dest ../
../aeneas/bin/aeneas -backend lean tutorial.llbc
```

If a repository has `aeneas-test-options`, mirror its flags. The current Aeneas tutorial uses options equivalent to a Lean destination plus loop-to-recursive translation.

## Lake Wiring

For a standalone Lean project, the Lake file typically depends on the Aeneas Lean backend. Pin the dependency when possible:

```lean
import Lake
open Lake DSL

require aeneas from git
  "https://github.com/AeneasVerif/aeneas.git" @ "<commit>" / "backends/lean"

package «my_project» {}
@[default_target] lean_lib MyProject
```

Match `lean-toolchain` to the Aeneas backend version. If builds fail after updating Aeneas, inspect the backend's own `lean-toolchain` and `lakefile`.

## Generated Lean Patterns

Modern generated files usually start like:

```lean
import Aeneas
open Aeneas Aeneas.Std Result ControlFlow Error
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
```

Recognize these translations:

- Rust `u32`, `u8`, `usize`, `i32` become `Std.U32`, `Std.U8`, `Std.Usize`, `Std.I32` or opened aliases `U32`, `U8`, `Usize`, `I32`.
- Rust functions returning normally use `Result T`.
- Panics and failed preconditions appear through `fail panic` or failing `Result` computations.
- Mutable borrows are encoded by returning an updated value, or a value plus a back-function.
- Loops are often generated as `@[rust_loop]` definitions with `partial_fixpoint`.
- Wrappers may be marked `@[reducible]`.
- Rust vectors use `alloc.vec.Vec T`, `alloc.vec.Vec.len`, `alloc.vec.Vec.index`, `alloc.vec.Vec.index_mut`, `alloc.vec.Vec.resize`, and `alloc.vec.Vec.push`.
- Trait declarations become Lean structures; implementations become concrete values under generated namespaces.

Example mutable-borrow back-function spec:

```lean
theorem list_nth_mut1_spec {T : Type} [Inhabited T] (l : CList T) (i : U32)
    (h : i.val < l.toList.length) :
  list_nth_mut1 l i ⦃ x back =>
    x = l.toList[i.val]! ∧
    ∀ x', (back x').toList = l.toList.set i.val x' ⦄ := by
  unfold list_nth_mut1 list_nth_mut1_loop
  step*
  simp_all
```

## Spec Patterns

Use weakest-precondition notation for generated `Result` programs:

```lean
f a b ⦃ r => postcondition_about r ⦄
```

For tuple-like logical returns, Aeneas postconditions can bind multiple names:

```lean
g x ⦃ c x' =>
  x'.length = x.length ∧
  c.val <= 1 ⦄
```

Register reusable specs:

```lean
@[step]
theorem helper_spec (...) : helper ... ⦃ r => ... ⦄ := by
  ...
```

Then callers can use:

```lean
unfold caller
step with helper_spec as ⟨ hret ⟩
```

Use mathematical model functions next to proofs, not in generated files. For vectors of limbs, define a list-level interpretation:

```lean
@[simp]
def toInt (l : List U32) : Int :=
  match l with
  | [] => 0
  | x :: l => x + 2 ^ 32 * toInt l
```

Useful vector/list forms in modern proofs:

- `x.length`
- `x.val`
- `x[j]!`
- `l[i]!`
- `l.set i v`
- `l.drop i`

## Tactic Playbook

Default sequence:

```lean
unfold target target_loop
simp
split
  -- branch proofs
```

For Aeneas computations:

- `step` advances one monadic bind or applies one registered spec.
- `step as ⟨ x, hx ⟩` names produced values and facts.
- `step with theorem_name as ⟨ x ⟩` forces a specific spec.
- `step*` repeatedly steps and handles routine branches.
- `step*?` can show an explicit script when automation is opaque.

For cleanup:

- `simp_all` simplifies goals and hypotheses using context.
- `simp_lists [*]` is useful for `List.getElem!`, `List.set`, list lengths, and generated list goals.
- `scalar_tac` closes linear scalar arithmetic and machine-integer bounds.
- `scalar_tac +split` is useful when arithmetic facts depend on `if`/overflow cases.
- `agrind` and `grind` close many algebraic/logical obligations after Aeneas simplification.
- `ring_nf`, `ring_nf at *`, and `ring_eq_nf` help with non-linear integer arithmetic over limb encodings.

For recursive proofs:

```lean
termination_by x.length - i.val
decreasing_by scalar_decr_tac
```

Older proofs sometimes need:

```lean
termination_by n.toNat
decreasing_by
  simp_wf
  scalar_tac
```

## Lists, Vectors, and Back-Functions

When proving mutable-list functions, introduce a pure view:

```lean
@[simp, grind, agrind]
def CList.toList {α : Type} (x : CList α) : List α :=
  match x with
  | CList.CNil => []
  | CList.CCons hd tl => hd :: tl.toList
```

Useful current list lemmas:

- `List.getElem!_cons_zero`
- `List.getElem!_cons_nzero`
- `List.set_cons_zero`
- `List.set_cons_nzero`

For vector update proofs, common helper lemmas model `drop` and `set`:

```lean
@[simp]
theorem toInt_drop (l : List U32) (i : Nat) (h : i < l.length) :
  toInt (l.drop i) = l[i]! + 2 ^ 32 * toInt (l.drop (i + 1)) := by
  ...

@[simp]
theorem toInt_update (l : List U32) (i : Nat) (x : U32) (h : i < l.length) :
  toInt (l.set i x) = toInt l + 2 ^ (32 * i) * (x - l[i]!) := by
  ...
```

## External Functions and Unsupported Surface

If Aeneas emits external-template files, provide Lean models/specs for the externals rather than editing generated code. Keep those models small and document the Rust assumptions they encode.

Default limitations to surface:

- Aeneas is designed for safe Rust; unsafe code needs separate justification or another workflow.
- Some Rust features may be unsupported or require rewriting the Rust into Aeneas-friendly code.
- Translation flags and generated Lean names are version-sensitive. Inspect the local generated files before writing proofs.

## Validation

After generation or proof edits:

```bash
lake build
```

For narrow checks, use the repo's existing Lean/Lake target when available. If a file imports generated modules, checking that proof module is usually enough to catch stale names, bad specs, and tactic regressions.
