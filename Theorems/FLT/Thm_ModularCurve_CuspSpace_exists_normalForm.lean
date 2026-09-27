import Mathlib
import Definitions.FLT.Def_ModularCurve_CuspSpace
import Definitions.FLT.Def_ModularCurve_GenusNumerics

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open OnePoint
theorem ModularCurve.CuspSpace.exists_normalForm {N : ℕ} (hN : N ≠ 0) (x : ModularCurve.CuspSpace N) :
    ∃ a : ℤ, IsCoprime a (ModularCurve.CuspSpace.cuspDenom N x : ℤ) ∧
      x = ModularCurve.CuspSpace.mk N (ModularCurve.ratPoint a (ModularCurve.CuspSpace.cuspDenom N x)) := by sorry
