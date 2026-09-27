import Mathlib
import Definitions.FLT.Def_ModularCurve_CuspSpace
import Definitions.FLT.Def_ModularCurve_GenusNumerics

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open OnePoint
theorem ModularCurve.CuspSpace.normalFormCriterion {N : ℕ} (hN : N ≠ 0) :
    ModularCurve.CuspSpace.NormalFormCriterion N := by sorry
