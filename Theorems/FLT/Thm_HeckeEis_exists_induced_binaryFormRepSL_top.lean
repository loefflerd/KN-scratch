import Mathlib.Basic.Complex.Basic
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

import Definitions.FLT.Def_HeckeEis_BinaryFormRep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
theorem HeckeEis.exists_induced_binaryFormRepSL_top (N : ℕ) [NeZero N] (n : ℕ) (hn : Even n) (hn0 : n ≠ 0) :
    ∃ W : Representation ℂ (⊤ : Subgroup SL(2, ℤ)) (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm ℂ n)),
      (∀ (g : (⊤ : Subgroup SL(2, ℤ))) (f : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm ℂ n)) (x : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N),
        W g f x = HeckeEis.binaryFormRepSL ℂ n (g : SL(2, ℤ)) (f (((g : SL(2, ℤ))⁻¹) • x))) ∧
      W ⟨-1, Subgroup.mem_top _⟩ = LinearMap.id ∧
      (∀ f : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm ℂ n), (∀ g : (⊤ : Subgroup SL(2, ℤ)), W g f = f) → f = 0) ∧
      (∀ f : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm ℂ n), ∃ a b : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm ℂ n),
        f = (W ⟨ModularGroup.S, Subgroup.mem_top _⟩ a - a) + (W ⟨ModularGroup.S * ModularGroup.T, Subgroup.mem_top _⟩ b - b)) := by sorry
