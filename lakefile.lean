import Lake
open Lake DSL

package «KNIndependent» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`warn.sorry, (get_config? warn.sorry).getD "true" != "false"⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "0df444a360eaa60ab8c11dca51a86af692955474"

lean_lib «Definitions» where
lean_lib «Theorems» where
lean_lib «Solutions» where
