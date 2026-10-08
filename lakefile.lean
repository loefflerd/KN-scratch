import Lake
open Lake DSL

package «KNIndependent» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩ ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "f6090c7095e1e56b3464c1daba5f24631f1290d2"

@[default_target]
lean_lib «Definitions» where
  globs := #[.submodules `Definitions]

@[default_target]
lean_lib «Theorems» where
  globs := #[.submodules `Theorems]

@[default_target]
lean_lib «Solutions» where
  globs := #[.submodules `Solutions]

@[default_target]
lean_lib «TauCeti» where
  globs := #[.submodules `TauCeti]
  leanOptions := #[⟨`autoImplicit, true⟩]
