# Lean + Mathlib setup and cache

## Toolchain

Lean/Lake are managed by `elan`. The active toolchain is pinned per-project by a `lean-toolchain` file (e.g. `leanprover/lean4:v4.30.0`). `elan` auto-installs and selects it on first `lake` invocation in that directory.

- `elan toolchain list` — installed toolchains.
- `elan show` — toolchain active in the current directory.
- Do NOT hand-edit `lean-toolchain` to a version that disagrees with the Mathlib commit; they move together.

## New Mathlib project

Scaffold so the project toolchain matches Mathlib's from the start (avoids an immediate mismatch → recompile):

```bash
lake +leanprover-community/mathlib4:lean-toolchain new my_proj math   # 'math' template adds Mathlib; toolchain taken from Mathlib's lean-toolchain
cd my_proj
lake exe cache get         # fetch prebuilt Mathlib oleans — do this BEFORE lake build
lake build
```

`lake new my_proj math` also works but uses the ambient Lean version, which may not match the Mathlib revision it pulls. Don't pin an arbitrary `leanprover/lean4:vX.Y.0` independently — the toolchain must track the Mathlib commit, not the other way round.

## The Mathlib cache, in detail

Mathlib is huge; a from-source build is hours. The Mathlib repo publishes compiled `.olean` files to a cloud cache, addressed by source hash.

- `lake exe cache get` — downloads the oleans matching the Mathlib commit currently pinned in `lake-manifest.json`. (It fetches build artifacts only; the toolchain itself is installed/selected by `elan` from `lean-toolchain` — that file must already match the Mathlib commit.) This is the normal command. Run it from the **project root** (the dir holding `lakefile.*` / `lean-toolchain`); from a subdirectory it fails to find the workspace.
- `lake exe cache get!` — force re-download even if local files look present (use when oleans are corrupted or partially downloaded).
- `lake exe cache pack` / `unpack` — rarely needed by consumers.

When the cache is valid, `lake build` should compile only *your* modules and report no `Mathlib.*` recompilation. If you see Lean compiling Mathlib files, the cache is missing/stale:

1. Stop the build.
2. `lake exe cache get` (or `get!`).
3. Retry `lake build`.

### Why a build starts compiling Mathlib

- Fresh clone without `cache get` yet.
- **New git worktree:** `.lake/` is gitignored and lives per-checkout, so a freshly added worktree has no Mathlib oleans even though the repo is "already cloned." Run `lake exe cache get` inside the worktree before `lake build`.
- `lake-manifest.json` changed (after `lake update`) so the pinned rev no longer matches local oleans → run `cache get` again.
- `lean-toolchain` and Mathlib rev disagree (manual edit, partial update). Realign them; the cache only exists for the official (toolchain, commit) pairs Mathlib CI built.
- Local edits to files *under* the Mathlib dependency — don't edit dependency sources.

## Updating dependencies

```bash
lake update          # bumps deps per lakefile constraints, rewrites lake-manifest.json
lake exe cache get   # re-fetch oleans after update (see note)
lake build
```

In a Mathlib-dependent project `lake update` runs a post-update hook that calls `lake exe cache get` for you; set `MATHLIB_NO_CACHE_ON_UPDATE=1` to suppress it. Run `cache get` manually if you skipped the hook or it failed. Bumping Mathlib usually drags the toolchain with it (Mathlib's own `lean-toolchain` propagates).

## Project layout

- `lakefile.toml` or `lakefile.lean` — build config, dependencies, lean_lib/lean_exe targets.
- `lake-manifest.json` — locked dependency revisions (commit the file).
- `lean-toolchain` — pinned Lean version.
- `.lake/` — build outputs and fetched deps (gitignore'd).

## Common failures

- **Build recompiling Mathlib:** cache not fetched / stale — see above.
- **`lake exe cache get` fails / network:** retry first — many failures are transient CDN/network blips and a second run succeeds. A corporate proxy may block the download host.
- **olean version mismatch / "incompatible" / hash mismatch:** toolchain vs cache mismatch. Copy Mathlib's `lean-toolchain` into your project (or align the pinned versions), then `lake exe cache get!`.
- **Corrupt / partial oleans:** clear the shared cache dir `~/.cache/mathlib` (safe to delete), optionally `lake clean`, then `lake exe cache get!`.
- **`tar`/`xz: Cannot exec`:** missing decompression utility — install `xz`/`tar` on the system.
- **Windows file locks** ("file is being used by another process", `.git/index.lock`): close the editor / kill stray git processes; antivirus can also break the HTTPS download — disable it for the fetch.
- **Out of disk:** Mathlib oleans are several GB. Check space before fetching.
