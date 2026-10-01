import Mathlib.Basic.Complex.Basic

import Definitions.FLT.Def_Gamma0CoeffCohomology
import Definitions.FLT.Def_HeckeEis_BinaryFormRep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
theorem HeckeEis.finrank_coeffH1par_gamma0_le_finrank_coeffH1par_top_induced (N : ℕ) [NeZero N] (n : ℕ)
    (W : Representation ℂ (⊤ : Subgroup SL(2, ℤ)) (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm ℂ n)))
    (hW : ∀ (g : (⊤ : Subgroup SL(2, ℤ))) (f : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm ℂ n)) (x : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N),
      W g f x = HeckeEis.binaryFormRepSL ℂ n (g : SL(2, ℤ)) (f (((g : SL(2, ℤ))⁻¹) • x))) :
    Module.finrank ℂ (HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype))
      ≤ Module.finrank ℂ (HeckeEis.coeffH1par W) := by sorry
