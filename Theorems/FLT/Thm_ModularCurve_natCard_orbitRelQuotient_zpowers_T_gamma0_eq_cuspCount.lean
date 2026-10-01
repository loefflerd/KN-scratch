import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

import Definitions.FLT.Def_ModularCurve_GenusNumerics

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
theorem ModularCurve.natCard_orbitRelQuotient_zpowers_T_gamma0_eq_cuspCount (N : ℕ) [NeZero N] :
    Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers ModularGroup.T)
        (Matrix.SpecialLinearGroup (Fin 2) ℤ ⧸ CongruenceSubgroup.Gamma0 N))
      = ModularCurve.cuspCount N := by sorry
