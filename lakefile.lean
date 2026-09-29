import Lake
open Lake DSL

package «KNIndependent» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`warn.sorry, (get_config? warn.sorry).getD "true" != "false"⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "v4.34.1"

lean_lib «Definitions» where
lean_lib «Theorems» where
lean_lib «Solutions» where
