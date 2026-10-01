import Mathlib.Basic.Complex.Basic

import Definitions.FLT.Def_Gamma0CoeffCohomology

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
theorem HeckeEis.finrank_coeffH1par_top_add_le {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (W : Representation ℂ (⊤ : Subgroup SL(2, ℤ)) V)
    (hneg : W ⟨-1, Subgroup.mem_top _⟩ = LinearMap.id)
    (hinv : ∀ v : V, (∀ g : (⊤ : Subgroup SL(2, ℤ)), W g v = v) → v = 0)
    (hcoinv : ∀ v : V, ∃ a b : V,
      v = (W ⟨ModularGroup.S, Subgroup.mem_top _⟩ a - a) + (W ⟨ModularGroup.S * ModularGroup.T, Subgroup.mem_top _⟩ b - b)) :
    Module.finrank ℂ (HeckeEis.coeffH1par W)
      + Module.finrank ℂ ↥(LinearMap.ker (W ⟨ModularGroup.S, Subgroup.mem_top _⟩ - 1))
      + Module.finrank ℂ ↥(LinearMap.ker (W ⟨ModularGroup.S * ModularGroup.T, Subgroup.mem_top _⟩ - 1))
      + Module.finrank ℂ ↥(LinearMap.ker (W ⟨ModularGroup.T, Subgroup.mem_top _⟩ - 1))
      ≤ Module.finrank ℂ V := by sorry
