import Lake
open Lake DSL

package «KNIndependent» where
  allowNonModules := true
  leanOptions := #[
    ⟨`autoImplicit, false⟩ ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @
  "074063781836922cb02701cd12943c9f51731afa"

require TauCeti from git
  "https://github.com/TauCetiProject/TauCeti.git" @
  "ead24a3b604c3df52bdc2b656f23d15d370ee0e8"

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
lean_lib «Challenge» where
  roots := #[`Challenge]

@[default_target]
lean_lib «Solution» where
  roots := #[`Solution]
