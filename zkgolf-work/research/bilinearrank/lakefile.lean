import Lake
open Lake DSL

package Circuits where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩]

@[default_target]
lean_lib Challenge where
  globs := #[.submodules `Challenge]


lean_lib Solution where
  globs := #[.submodules `Solution]

require clean from git "https://github.com/Verified-zkEVM/clean" @ "041c6e7ebc06f5cbfd534c2a19c4120f3de62435"
