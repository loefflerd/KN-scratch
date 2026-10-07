import Lake
open Lake DSL

package «KNIndependent» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩ ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "f6090c7095e1e56b3464c1daba5f24631f1290d2"

lean_lib «Definitions» where
lean_lib «Theorems» where
lean_lib «Solutions» where
lean_lib «TauCeti» where
