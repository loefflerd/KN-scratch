import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

import Definitions.FLT.Def_ModularCurve_GenusNumerics

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups
theorem ModularCurve.natCard_fixedPoints_ST_cosets_Gamma0_eq_nuThree (N : ℕ) [NeZero N] :
    Nat.card {x : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N //
        (ModularGroup.S * ModularGroup.T) • x = x} =
      ModularCurve.nuThree N := by sorry
